-- Prove2me | solution 1 for GlobalTheory.PMonE.gl1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:08:34.010924+00:00
-- url     : https://prove2.me/submissions/e086e3e7-9ca9-4c50-95f5-a4a3a998f8a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangCountFrobeniusEqMulVecSolutionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaOrderOne
import Theorems.Thm_GlobalTheory_PMonE_integralNormVector_pow_sub_mulVec
import Theorems.Thm_GlobalTheory_PMonE_additiveSystemFrobeniusPowerSum_zero
import Theorems.Thm_GlobalTheory_T_additiveSystem_preparation_normalForm_one
import Theorems.Thm_GlobalTheory_T_existsUnique_integral_additiveSystemFrobeniusPowerSum_eq
import Theorems.Thm_GlobalTheory_T_exists_integral_solution_frobenius_sub_mulVec_eq
import Theorems.Thm_GlobalTheory_T_lang_count_frobenius_eq_mulVec_solutions


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE
theorem _root_.solution : GLOnto 1 ∧ GLCount 1 := by
  constructor
  · intro F _ _ _ _ p _ _ m _ _ e D he hD M hM b hb
    obtain ⟨A, U, hA, hU0, hUn, -, hfac⟩ := GlobalTheory.T.additiveSystem_preparation_normalForm_one F p m e D he hD M hM
    obtain ⟨y, ⟨hy, hyb⟩, -⟩ := GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq F p m e D he U hU0 hUn b hb
    obtain ⟨x, hx, hxy⟩ := GlobalTheory.T.exists_integral_solution_frobenius_sub_mulVec_eq F p m e he A hA y hy
    refine ⟨x, hx, ?_⟩
    rw [hfac]
    have : (fun i => x i ^ p ^ e - A.mulVec x i) = y := funext hxy
    rw [this, hyb]
  · intro F _ _ _ _ p _ _ m _ _ e D he hD M hM hdet
    obtain ⟨A, U, hA, hU0, hUn, hM0, hfac⟩ := GlobalTheory.T.additiveSystem_preparation_normalForm_one F p m e D he hD M hM
    have hAdet : A.det ≠ 0 := by
      intro h
      apply hdet
      rw [hM0, Matrix.det_neg, Matrix.det_mul, h, mul_zero, mul_zero]
    obtain ⟨hInt, hcard⟩ := GlobalTheory.T.lang_count_frobenius_eq_mulVec_solutions F p m e he A hA hAdet
    have hq : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
    obtain ⟨z, -, hz⟩ := GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq F p m e D he U hU0 hUn 0 (fun i => by simp)
    have key : ∀ x : m → F, Integral x →
        (gsum (p ^ e) D M x = 0 ↔ ∀ i, x i ^ p ^ e = A.mulVec x i) := by
      intro x hx
      rw [hfac]
      constructor
      · intro h0
        have h1 := hz _ ⟨integralNormVector_pow_sub_mulVec A hA (p ^ e) x hx, h0⟩
        have h2 := hz (fun _ => 0) ⟨fun i => by simp, additiveSystemFrobeniusPowerSum_zero _ D hq U⟩
        intro i
        have := congrFun (h1.trans h2.symm) i
        exact sub_eq_zero.mp this
      · intro h
        have : (fun i => x i ^ p ^ e - A.mulVec x i) = fun _ => 0 := funext fun i => by rw [h i, sub_self]
        rw [this]
        exact additiveSystemFrobeniusPowerSum_zero _ D hq U
    have eqv : {x : m → F // Integral x ∧ gsum (p ^ e) D M x = 0} ≃
        {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} :=
      { toFun := fun x => ⟨x.1, (key x.1 x.2.1).mp x.2.2⟩
        invFun := fun x => ⟨x.1, hInt x.1 x.2, (key x.1 (hInt x.1 x.2)).mpr x.2⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    rw [Nat.card_congr eqv, hcard, mul_one]
end GlobalTheory.PMonE
