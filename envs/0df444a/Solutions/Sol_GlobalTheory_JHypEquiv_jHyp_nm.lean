-- Prove2me | solution 1 for GlobalTheory.JHypEquiv.jHyp_nm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:13.471987+00:00
-- url     : https://prove2.me/submissions/d943e08e-b5f5-4b2a-b792-65dc4889bfac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnifConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JHypUnipotentTorusEquivariance
import Theorems.Thm_GlobalTheory_JHypEquiv_row_one
import Theorems.Thm_GlobalTheory_JHypEquiv_absK_unit
import Theorems.Thm_GlobalTheory_JHypEquiv_integral_inv_mul
import Theorems.Thm_GlobalTheory_JHypEquiv_etaK_mul
import Theorems.Thm_GlobalTheory_JR_EtMeas_absK_unit
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
open GlobalTheory GlobalTheory.JHypEquiv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.JHypEquiv
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (ψ : AddChar F ℂ)
    (φ' : A.K × A.K → ℂ) (z : A.K) (s : A.Kˣ) (g : SpecialLinearGroup (Fin 2) A.K),
    A.jHyp μK ψ φ' (nS z * mS s * g) = A.etaK s * (A.absK s : ℂ) * A.jHyp μK ψ φ' g := by
  intro F E _ _ _ _ _ A μK hμ ψ φ' z s g
  haveI := hμ
  unfold Et.jHyp
  simp only [row_one]
  set H : A.K → ℂ := fun u => A.tilde μK ψ φ' (u * g 1 0) (u * g 1 1) * A.etaK ((s : A.K) * u) with hH
  have h1 : (fun t => A.tilde μK ψ φ' (t * (((s⁻¹ : A.Kˣ) : A.K) * g 1 0)) (t * (((s⁻¹ : A.Kˣ) : A.K) * g 1 1)) *
      A.etaK t) = fun t => H (((s⁻¹ : A.Kˣ) : A.K) * t) := by
    funext t
    simp only [hH]
    rw [Units.mul_inv_cancel_left]
    congr 2 <;> ring
  rw [h1, integral_inv_mul A μK s H]
  have hnull : μK {t | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hμ
  have hae : ∀ᵐ u ∂μK, IsUnit u := ae_iff.mpr hnull
  have h2 : ∫ u, H u ∂μK = ∫ u, A.tilde μK ψ φ' (u * g 1 0) (u * g 1 1) * A.etaK u * A.etaK s ∂μK := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    simp only [hH]
    rw [etaK_mul A s u hu]
    ring
  rw [h2, integral_mul_const, absK_unit]
  ring
end GlobalTheory.JHypEquiv
