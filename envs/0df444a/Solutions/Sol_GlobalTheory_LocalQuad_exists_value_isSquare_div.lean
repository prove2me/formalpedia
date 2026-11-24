-- Prove2me | solution 1 for GlobalTheory.LocalQuad.exists_value_isSquare_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:24:31.560175+00:00
-- url     : https://prove2.me/submissions/688ca503-8228-4627-aea6-f9f370aa5135

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
import Theorems.Thm_GlobalTheory_LocalQuad_denseRange_finite_real
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
theorem _root_.solution (F : Type) [Field F] [NumberField F] {a a' : F} (ha : a ≠ 0)
    (T : Finset (HeightOneSpectrum (𝓞 F))) (p q : (v : T) → v.1.adicCompletion F)
    (hpq : ∀ v, algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2 ≠ 0)
    (p' q' : (F →+* ℝ) → ℝ) (hpq' : ∀ σ, σ a * p' σ ^ 2 + σ a' * q' σ ^ 2 ≠ 0) :
    ∃ x y : F, a * x ^ 2 + a' * y ^ 2 ≠ 0 ∧
      (∀ v : T, IsSquare (algebraMap F (v.1.adicCompletion F) (a * x ^ 2 + a' * y ^ 2) /
        (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2))) ∧
      ∀ σ : F →+* ℝ, IsSquare (σ (a * x ^ 2 + a' * y ^ 2) / (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2)) := by
  have hd := (denseRange_finite_real F T).prodMap (denseRange_finite_real F T)
  have h4 : ∀ v : T, Valued.v (4 : v.1.adicCompletion F) ≠ 0 := by
    intro v
    haveI : CharZero (v.1.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.1.adicCompletion F)).injective
    simp
  have h41 : ∀ v : T, Valued.v (4 : v.1.adicCompletion F) ≤ 1 := by
    intro v
    have h2 : Valued.v (1 + 1 : v.1.adicCompletion F) ≤ 1 :=
      Valuation.map_add_le _ (by simp) (by simp)
    rw [show (4 : v.1.adicCompletion F) = (1 + 1) * (1 + 1) by norm_num, map_mul]
    exact mul_le_one' h2 h2
  let U : Set ((((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) ×
      (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ))) := (⋂ v : T, {z | Valued.v ((algebraMap F _ a * z.1.1 v ^ 2 +
      algebraMap F _ a' * z.2.1 v ^ 2) / (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1)
        < Valued.v (4 : v.1.adicCompletion F)}) ∩
    ⋂ σ : F →+* ℝ, {z | 0 < (σ a * z.1.2 σ ^ 2 + σ a' * z.2.2 σ ^ 2) /
      (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2)}
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun v => ?_) (isOpen_iInter_of_finite fun σ => ?_)
    · have ho : IsOpen {u : v.1.adicCompletion F | Valued.v u < Valued.v (4 : v.1.adicCompletion F)} := by
        have := Valued.isOpen_ball (v.1.adicCompletion F) (Valued.v.restrict (4 : v.1.adicCompletion F))
        simpa only [Valuation.restrict_lt_iff] using this
      exact ho.preimage (f := fun z : (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) ×
      (((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) => (algebraMap F _ a * z.1.1 v ^ 2 +
        algebraMap F _ a' * z.2.1 v ^ 2) /
          (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1) (by fun_prop)
    · exact isOpen_lt continuous_const (by fun_prop)
  obtain ⟨⟨x, y⟩, hT, hR⟩ := hd.exists_mem_open hU ⟨((p, p'), (q, q')), by
    refine ⟨Set.mem_iInter.2 fun v => ?_, Set.mem_iInter.2 fun σ => ?_⟩
    · simp only [Set.mem_setOf_eq]
      rw [div_self (hpq v), sub_self, map_zero]
      exact zero_lt_iff.2 (h4 v)
    · simp only [Set.mem_setOf_eq]
      rw [div_self (hpq' σ)]
      exact one_pos⟩
  replace hT : ∀ v : T, Valued.v (algebraMap F (v.1.adicCompletion F) (a * x ^ 2 + a' * y ^ 2) /
      (algebraMap F _ a * p v ^ 2 + algebraMap F _ a' * q v ^ 2) - 1) <
        Valued.v (4 : v.1.adicCompletion F) := by
    intro v
    simp only [map_add, map_mul, map_pow]
    exact Set.mem_iInter.1 hT v
  replace hR : ∀ σ : F →+* ℝ,
      0 < σ (a * x ^ 2 + a' * y ^ 2) / (σ a * p' σ ^ 2 + σ a' * q' σ ^ 2) := by
    intro σ
    simp only [map_add, map_mul, map_pow]
    exact Set.mem_iInter.1 hR σ
  by_cases h0 : a * x ^ 2 + a' * y ^ 2 = 0
  · refine ⟨1, 0, by simpa using ha, fun v => ?_, fun σ => ?_⟩
    · have := (hT v).trans_le (h41 v)
      simp [h0] at this
    · have := hR σ
      simp [h0] at this
  · exact ⟨x, y, h0, fun v => isSquare_of_valued_sub_one_lt F v _ (hT v),
      fun σ => Real.isSquare_iff.2 (hR σ).le⟩
end GlobalTheory.LocalQuad
