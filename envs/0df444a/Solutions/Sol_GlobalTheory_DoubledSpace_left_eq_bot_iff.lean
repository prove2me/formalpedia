-- Prove2me | solution 1 for GlobalTheory.DoubledSpace.left_eq_bot_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:51:36.089377+00:00
-- url     : https://prove2.me/submissions/c4b55405-dc18-4f7c-9230-be960386ab27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HermitianPairingAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledIsotropicStructureGeneral
import Theorems.Thm_GlobalTheory_DoubledSpace_finrank_left_eq_finrank_right
import Theorems.Thm_GlobalTheory_DoubledSpace_map_fst_eq
import Theorems.Thm_GlobalTheory_DoubledSpace_map_snd_eq
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
variable {h : W →ₗ[E] W →ₛₗ[σ] E} {I : Submodule E (W × W)}
variable [FiniteDimensional E W] (hσ : Function.Involutive σ) (hh : ∀ x y, σ (h x y) = h y x)
  (hn : ∀ x, (∀ y, h x y = 0) → x = 0) (hI : ∀ p ∈ I, ∀ q ∈ I, form h p q = 0)
  (hd : finrank E I = finrank E W)
include hσ hh hn hI hd
namespace GlobalTheory.DoubledSpace
theorem _root_.solution :
    left I = ⊥ ↔ ∃! γ : W ≃ₗ[E] W,
      (∀ x y, h (γ x) (γ y) = h x y) ∧ I = (γ : W →ₗ[E] W).graph := by
  constructor
  · intro hX
    have hX' : right I = ⊥ := by
      rw [← Submodule.finrank_eq_zero, ← finrank_left_eq_finrank_right hσ hh hn hI hd, hX,
        finrank_bot]
    have b1 : Function.Bijective (Prod.fst ∘ I.subtype) := by
      refine ⟨fun p q e => ?_, fun x => ?_⟩
      · have e1 : p.1.1 = q.1.1 := e
        have : p.1.2 - q.1.2 ∈ right I := by
          rw [mem_right]
          convert I.sub_mem p.2 q.2 using 1
          ext <;> simp [e1]
        rw [hX', Submodule.mem_bot, sub_eq_zero] at this
        exact Subtype.ext (Prod.ext e1 this)
      · have : x ∈ I.map (LinearMap.fst E W W) := by
          rw [map_fst_eq hσ hh hn hI hd, hX]
          intro n hn; simp [(Submodule.mem_bot E).1 hn]
        obtain ⟨p, hp, rfl⟩ := this
        exact ⟨⟨p, hp⟩, rfl⟩
    have b2 : Function.Bijective (Prod.snd ∘ I.subtype) := by
      refine ⟨fun p q e => ?_, fun x => ?_⟩
      · have e1 : p.1.2 = q.1.2 := e
        have : p.1.1 - q.1.1 ∈ left I := by
          rw [mem_left]
          convert I.sub_mem p.2 q.2 using 1
          ext <;> simp [e1]
        rw [hX, Submodule.mem_bot, sub_eq_zero] at this
        exact Subtype.ext (Prod.ext this e1)
      · have : x ∈ I.map (LinearMap.snd E W W) := by
          rw [map_snd_eq hσ hh hn hI hd, hX']
          intro n hn; simp [(Submodule.mem_bot E).1 hn]
        obtain ⟨p, hp, rfl⟩ := this
        exact ⟨⟨p, hp⟩, rfl⟩
    obtain ⟨γ, hγ⟩ := Submodule.exists_equiv_eq_graph b1 b2
    refine ⟨γ, ⟨fun x y => ?_, hγ⟩, ?_⟩
    · have := hI (x, γ x) (by rw [hγ]; rfl) (y, γ y) (by rw [hγ]; rfl)
      rw [form_apply, sub_eq_zero] at this
      exact this.symm
    · rintro γ' ⟨-, hγ'⟩
      ext x
      have : (x, γ' x) ∈ I := by rw [hγ']; rfl
      rw [hγ] at this
      exact this
  · rintro ⟨γ, ⟨-, rfl⟩, -⟩
    rw [eq_bot_iff]
    intro x hx
    have : (0 : W) = γ x := hx
    exact γ.map_eq_zero_iff.1 this.symm
end GlobalTheory.DoubledSpace
