-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.finrank_add_finrank_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:41.802861+00:00
-- url     : https://prove2.me/submissions/ca756cbc-c957-4192-8195-f51bb7b8adb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply



set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.DoubledSpace
variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] {σ : E →+* E}
namespace GlobalTheory.DoubledSpace
theorem _root_.solution [FiniteDimensional E W] {h : W →ₗ[E] W →ₛₗ[σ] E}
    (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
    (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (S : Submodule E W) :
    finrank E S + finrank E (S.orthogonalBilin h) = finrank E W := by
  haveI : RingHomSurjective σ := ⟨hσ.surjective⟩
  have hrefl : ∀ x y, h x y = 0 → h y x = 0 := fun x y e => by rw [← hh, e, map_zero]
  have e1 : S.orthogonalBilin h = (S.map h.flip).dualCoannihilator := by
    ext m
    rw [Submodule.mem_dualCoannihilator, Submodule.mem_orthogonalBilin_iff]
    constructor
    · rintro H _ ⟨s, hs, rfl⟩
      exact hrefl _ _ (H s hs)
    · intro H s hs
      exact hrefl _ _ (H _ ⟨s, hs, rfl⟩)
  have hinj : Function.Injective h.flip := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hn x fun y => hrefl _ _ (LinearMap.congr_fun hx y)
  let j : S →+ S.map h.flip := (h.flip.submoduleMap S).toAddMonoidHom
  have hj : Function.Bijective j :=
    ⟨fun a b e => Subtype.ext (hinj (congrArg Subtype.val e)),
      fun ⟨_, s, hs, e⟩ => ⟨⟨s, hs⟩, Subtype.ext e⟩⟩
  have e2 : finrank E S = finrank E (S.map h.flip) := by
    have := lift_rank_eq_of_equiv_equiv σ (AddEquiv.ofBijective j hj) hσ.bijective
      (fun r m => Subtype.ext (h.flip.map_smulₛₗ r (m : W)))
    simpa [finrank] using congrArg Cardinal.toNat this
  rw [e1, e2, Subspace.finrank_add_finrank_dualCoannihilator_eq]
end GlobalTheory.DoubledSpace
