-- Prove2me | solution 1 for GlobalTheory.JR.LamBound.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:29.39003+00:00
-- url     : https://prove2.me/submissions/8da027db-bccf-4b1c-bc5a-ad5c5445891e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerBoundBigCell
import Theorems.Thm_GlobalTheory_JR_LamBound_norm_etaK
import Theorems.Thm_GlobalTheory_JR_LamBound_absK_nonneg
import Theorems.Thm_GlobalTheory_JR_LamBound_bdd_of_loc_const
import Theorems.Thm_GlobalTheory_T_etaleHermitianPair_structure_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LamBound
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JR.LamBound
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (Ψ : SpecialLinearGroup (Fin 2) A.K → ℂ), A.InI Ψ → ∃ C : ℝ, ∀ (z : A.K) (s : A.Kˣ) (α β : A.K), α ∈ A.OK → β ∈ A.OK → (s : A.K) ∈ A.OK → (s : A.K) * z ∈ A.OK → α * s + β * (s * z) = 1 → ‖Ψ (wS A.K * nS z)‖ ≤ C * A.absK s := by
  intro F E _ _ _ _ U A Ψ hΨ
  have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  let b := Module.finBasis F A.K
  have : T2Space A.K := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcpt, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨V, hV, hloc⟩ := hΨ.1
  obtain ⟨C, hC⟩ := bdd_of_loc_const A.K A.OK hcpt Ψ V hV hloc
  refine ⟨C, fun z s α β hα hβ hs hsz h => ?_⟩
  have hu : (s : A.K) * ((s⁻¹ : A.Kˣ) : A.K) = 1 := Units.mul_inv s
  let k : SpecialLinearGroup (Fin 2) A.K := ⟨!![-β, α; -(s : A.K), -((s : A.K) * z)], by
    simp [Matrix.det_fin_two]; linear_combination h⟩
  have hk : wS A.K * nS z = nS (-((s : A.K) * β)) * mS s * k := by
    apply Subtype.ext
    show !![(0 : A.K), 1; -1, 0] * !![1, z; 0, 1] =
      !![1, -((s : A.K) * β); 0, 1] * !![(s : A.K), 0; 0, ((s⁻¹ : A.Kˣ) : A.K)] * !![-β, α; -(s : A.K), -((s : A.K) * z)]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      linear_combination (-1 : A.K) * h - (β * (s : A.K) * z) * hu
  have hkO : ∀ i j, (k : Matrix (Fin 2) (Fin 2) A.K) i j ∈ A.OK := by
    rw [← hR]
    have hα' : α ∈ R := by rw [← SetLike.mem_coe, hR]; exact hα
    have hβ' : β ∈ R := by rw [← SetLike.mem_coe, hR]; exact hβ
    have hs' : (s : A.K) ∈ R := by rw [← SetLike.mem_coe, hR]; exact hs
    have hsz' : (s : A.K) * z ∈ R := by rw [← SetLike.mem_coe, hR]; exact hsz
    intro i j; fin_cases i <;> fin_cases j <;> simp [k, R.neg_mem, hα', hβ', hs', hsz']
  rw [hk, hΨ.2, norm_mul, norm_mul, norm_etaK, Complex.norm_real, Real.norm_of_nonneg (absK_nonneg A _), one_mul,
    mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC k hkO) (absK_nonneg A _)
end GlobalTheory.JR.LamBound
