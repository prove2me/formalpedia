-- Prove2me | solution 1 for GlobalTheory.exists_addHom_zmod_pow_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:37:57.817149+00:00
-- url     : https://prove2.me/submissions/e93c3665-e2b0-44e2-971a-9c8ed6d1ddb5

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__PoitouTateNineTermTransgressionZeroApply_433ca0b5d42a991a
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisCohomology__ContinuousCycMod_abd9886c27059cc0
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsZmodPowCoboundaryOfRationalCoboundary
import Theorems.Thm_Formalism_GaloisCohomology_scalRep_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisCohomology.scalRep_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (O : Type) [CommRing O] (l n : ℕ) [Fact l.Prime]
    (hinj : Function.Injective (fun o : O => (l : O) ^ n * o)) (β : O →+ ZMod (l ^ 1)) :
    ∃ A : O →+ ZMod (l ^ (n + 1)), ∀ o : O,
      A ((l : O) ^ n * o) = ((l ^ n * (β o).val : ℕ) : ZMod (l ^ (n + 1))) := by
  classical
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ (n + 1)) := ⟨pow_ne_zero _ hl0⟩
  have : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl0⟩

  have hcong : ∀ x : ℕ, ((l ^ n * (x % l ^ 1) : ℕ) : ZMod (l ^ (n + 1)))
      = ((l ^ n * x : ℕ) : ZMod (l ^ (n + 1))) := by
    intro x
    rw [ZMod.natCast_eq_natCast_iff, pow_one, pow_succ]
    exact Nat.ModEq.mul_left' _ (Nat.mod_modEq x l)
  let g : O →+ ZMod (l ^ (n + 1)) :=
    { toFun := fun o => ((l ^ n * (β o).val : ℕ) : ZMod (l ^ (n + 1)))
      map_zero' := by simp
      map_add' := by
        intro a b
        rw [map_add, ZMod.val_add, hcong, mul_add, Nat.cast_add] }

  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible UnitAddCircle).extension_property_addMonoidHom
    (AddMonoidHom.mulLeft ((l : O) ^ n)) hinj ((ZMod.toAddCircle).comp g)
  have hh' : ∀ o, h ((l : O) ^ n * o) = ZMod.toAddCircle (g o) := fun o =>
    DFunLike.congr_fun hh o

  have htors : ∀ o, (l ^ (n + 1)) • h o = 0 := by
    intro o
    have hlo : β ((l : O) * o) = 0 := by
      have hz : ((l : ℕ) : ZMod (l ^ 1)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (by rw [pow_one])
      rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, hz, zero_mul]
    rw [← map_nsmul, nsmul_eq_mul, Nat.cast_pow, pow_succ, mul_assoc, hh']
    simp [g, hlo]

  have hdesc : ∀ o, ∃ k : ZMod (l ^ (n + 1)), ZMod.toAddCircle k = h o := by
    intro o
    have ht := htors o
    obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (h o)
    rw [← hx] at ht ⊢
    rw [← QuotientAddGroup.mk_nsmul, AddCircle.coe_eq_zero_iff] at ht
    obtain ⟨m, hm⟩ := ht
    refine ⟨(m : ZMod (l ^ (n + 1))), ?_⟩
    rw [ZMod.toAddCircle_intCast]
    congr 1
    have hN : ((l ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero _ hl0
    rw [zsmul_eq_mul, mul_one, nsmul_eq_mul] at hm
    rw [hm, mul_div_cancel_left₀ _ hN]
  choose A hA using hdesc
  have hAadd : ∀ a b, A (a + b) = A a + A b := by
    intro a b
    apply ZMod.toAddCircle_injective (l ^ (n + 1))
    rw [map_add, hA, hA, hA, map_add]
  refine ⟨⟨⟨A, ?_⟩, hAadd⟩, ?_⟩
  · apply ZMod.toAddCircle_injective (l ^ (n + 1))
    rw [hA, map_zero, map_zero]
  · intro o
    apply ZMod.toAddCircle_injective (l ^ (n + 1))
    show ZMod.toAddCircle (A _) = _
    rw [hA, hh']
    rfl
end GlobalTheory
