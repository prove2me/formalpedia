-- Prove2me | solution 1 for GlobalTheory.LocalQuad.isotropic_ternary_of_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:21:54.600399+00:00
-- url     : https://prove2.me/submissions/5e4a7473-b194-491e-9488-124a458f913d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsQuaternaryOfCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitValuedTernaryLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRingHomAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroCoordNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_LocalQuad_exists_unit_valued_ternary_lt_one
import Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
namespace GlobalTheory.LocalQuad
theorem _root_.solution (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (a : Fin 3 → v.adicCompletion F) (ha : ∀ i, Valued.v (a i) = 1) :
    ∃ x : Fin 3 → v.adicCompletion F, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0 := by
  classical
  obtain ⟨x, -, ⟨k, hk⟩, hx⟩ := exists_unit_valued_ternary_lt_one F v (Matrix.diagonal a) (by
    intro i j
    by_cases h : i = j
    · subst h; simp [ha]
    · simp [Matrix.diagonal_apply_ne _ h])
  have e : ∑ i, ∑ j, Matrix.diagonal a i j * x i * x j = ∑ i, a i * x i ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Matrix.diagonal_apply_ne _ hj.symm]) (by simp)]
    simp [sq, mul_assoc]
  rw [e] at hx
  set q := ∑ i, a i * x i ^ 2 with hq
  have hu : Valued.v (a k * x k ^ 2) = 1 := by simp [ha, hk]
  have hu0 : a k * x k ^ 2 ≠ 0 := by
    intro h; rw [h] at hu; simp at hu
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, mul_one]
  have hlt : Valued.v (1 - q / (a k * x k ^ 2) - 1) < 1 := by
    rw [sub_sub_cancel_left, Valuation.map_neg, map_div₀, hu, div_one]; exact hx
  obtain ⟨s, hs⟩ := isSquare_of_valued_sub_one_lt F v (1 - q / (a k * x k ^ 2)) (by rwa [h4])
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [hs] at hlt
    simp at hlt
  have hxk : x k ≠ 0 := by
    intro h; rw [h] at hk; simp at hk
  refine ⟨Function.update x k (x k * s), fun hc => ?_, ?_⟩
  · have := congrFun hc k
    simp [hs0, hxk] at this
  · have h1 : a k * x k ^ 2 * (s * s) = a k * x k ^ 2 - q := by
      rw [← hs, mul_sub, mul_one, mul_div_cancel₀ _ hu0]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)] at hq ⊢
    rw [Finset.sum_congr rfl (g := fun i => a i * x i ^ 2)
      (fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]), Function.update_self]
    linear_combination h1 - hq
end GlobalTheory.LocalQuad
