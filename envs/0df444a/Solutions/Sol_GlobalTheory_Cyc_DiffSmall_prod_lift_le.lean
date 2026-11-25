-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.prod_lift_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:30.881934+00:00
-- url     : https://prove2.me/submissions/3bcf1599-5d11-4641-8fea-41c4658e82bb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_gal
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_sum_le_of_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_mem_intPoly
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_C_mem_intPoly
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_X_mem_intPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.DiffSmall
theorem _root_.solution (F E : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ F.fixingSubgroup)
    (hu : ∀ h ∈ F.fixingSubgroup, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ E.fixingSubgroup)
    {x : Om l} (hxE : x ∈ E) (hx : ‖x‖ ≤ 1) (τ : GQ l) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hτ : ∀ z ∈ F, ‖z‖ ≤ 1 → ‖τ z - z‖ ≤ ρ) : ∏ s ∈ S, ‖x - τ (s x)‖ ≤ ρ := by
  classical
  have hfix : ∀ s t : GQ l, s⁻¹ * t ∈ E.fixingSubgroup → t x = s x := by
    intro s t h
    have := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h x hxE
    have h2 := congrArg s this
    simpa using h2
  set f : (Om l)[X] := ∏ s ∈ S, (X - C (s x)) with hf
  have hfi : f ∈ intPoly l := prod_mem fun t _ =>
    sub_mem X_mem_intPoly (C_mem_intPoly (by rwa [norm_gal]))
  have hmap : ∀ g : GQ l, f.map (g : Om l →+* Om l) = ∏ s ∈ S, (X - C (g (s x))) := by
    intro g
    simp [hf, Polynomial.map_prod]
  have hinv : ∀ h ∈ F.fixingSubgroup, f.map (h : Om l →+* Om l) = f := by
    intro h hh
    rw [hmap, hf]
    have hex := fun s (hs : s ∈ S) => hu (h * s) (mul_mem hh (hS s hs))
    choose φ hφ hφu using hex
    refine Finset.prod_bij φ (fun s hs => (hφ s hs).1) ?_ ?_ ?_
    · intro s hs t ht hst
      have h1 : s⁻¹ * t ∈ E.fixingSubgroup := by
        have := mul_mem (inv_mem (hφ s hs).2) (hφ t ht).2
        rw [hst] at this
        simpa [mul_assoc] using this
      exact (hu t (hS t ht)).unique ⟨hs, h1⟩ ⟨ht, by simp⟩
    · intro t ht
      obtain ⟨s, ⟨hs, h1⟩, -⟩ := hu (h⁻¹ * t) (mul_mem (inv_mem hh) (hS t ht))
      refine ⟨s, hs, (hφu s hs t ⟨ht, ?_⟩).symm⟩
      simpa [mul_assoc] using inv_mem h1
    · intro s hs
      rw [← hfix _ _ (hφ s hs).2]
      rfl
  have hcoef : ∀ n, f.coeff n ∈ F := by
    intro n
    rw [← InfiniteGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
    intro h hh
    conv_rhs => rw [← hinv h hh, coeff_map]
    rfl
  have h0 : f.eval x = 0 := by
    obtain ⟨s, ⟨hs, h1⟩, -⟩ := hu 1 (one_mem _)
    rw [hf, eval_prod]
    refine Finset.prod_eq_zero hs ?_
    rw [← hfix _ _ h1]
    simp
  have h1 : ∏ s ∈ S, (x - τ (s x)) = (f.map (τ : Om l →+* Om l) - f).eval x := by
    rw [eval_sub, h0, sub_zero, hmap, eval_prod]
    simp
  rw [← norm_prod, h1, eval_eq_sum_range]
  refine norm_sum_le_of_le _ _ hρ fun n _ => ?_
  rw [norm_mul, norm_pow, coeff_sub, coeff_map]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hx)).trans
    (hτ _ (hcoef n) (mem_intPoly.1 hfi n))
end GlobalTheory.Cyc.DiffSmall
