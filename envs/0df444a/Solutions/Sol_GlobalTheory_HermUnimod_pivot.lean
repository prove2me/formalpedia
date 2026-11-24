-- Prove2me | solution 1 for GlobalTheory.HermUnimod.pivot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:43:22.571743+00:00
-- url     : https://prove2.me/submissions/80f9b1ed-5407-4c17-a8ae-ce351c2e3702

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnimodularHermitianMatrixCongruentOne
import Theorems.Thm_GlobalTheory_HermUnimod_intg_one
import Theorems.Thm_GlobalTheory_HermUnimod_pivot_w
import Theorems.Thm_GlobalTheory_HermUnimod_fixed_mem
import Theorems.Thm_GlobalTheory_HermUnimod_quad_col
import Theorems.Thm_GlobalTheory_T_exists_mul_star_eq_of_norm_one_unramifiedQuadratic
import Theorems.Thm_GlobalTheory_T_unramifiedQuadratic_integral_traceForm_perfect


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
open GlobalTheory GlobalTheory.HermUnimod
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E]
include F
namespace GlobalTheory.HermUnimod
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (G : Matrix n n E) (hG : G.IsHermitian)
    (hGi : Intg G) (hGd : ‖G.det‖ = 1) :
    ∃ P : Matrix n n E, Intg P ∧ ‖P.det‖ = 1 ∧ ∃ k, (Pᴴ * G * P) k k = 1 := by
  haveI := Unram.ultraE (F := F) (E := E)
  have hs : ∀ y : E, ‖star y‖ = ‖y‖ := Unram.norm_star (F := F)
  obtain ⟨-, ⟨e0, he0, he0'⟩, -⟩ := GlobalTheory.T.unramifiedQuadratic_integral_traceForm_perfect F E
  obtain ⟨i, w, hw, hwi, hq⟩ := pivot_w hs e0 he0 he0' G hG hGi hGd
  have ha : star (star w ⬝ᵥ (G *ᵥ w)) = star w ⬝ᵥ (G *ᵥ w) := by
    calc star (star w ⬝ᵥ (G *ᵥ w)) = (star w ᵥ* Gᴴ) ⬝ᵥ w := by rw [star_dotProduct, star_mulVec, star_star]
      _ = star w ⬝ᵥ (G *ᵥ w) := by rw [← dotProduct_mulVec, hG.eq]
  obtain ⟨u, hu⟩ := fixed_mem (F := F) _ ha
  have hu1 : ‖u‖ = 1 := by rw [← norm_algebraMap' E u, hu]; exact hq
  obtain ⟨v0, hv0⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E u hu1
  rw [hu] at hv0
  have hv0n : ‖v0‖ = 1 := by
    have h := congrArg norm hv0
    rw [norm_mul, hs, hq] at h
    nlinarith [norm_nonneg v0]
  have hv0ne : v0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv0n
    exact zero_ne_one hv0n
  have hc : ‖(star v0)⁻¹‖ = 1 := by rw [norm_inv, hs, hv0n, inv_one]
  refine ⟨(1 : Matrix n n E).updateCol i ((star v0)⁻¹ • w), ?_, ?_, i, ?_⟩
  · intro p q
    rw [updateCol_apply]
    split_ifs
    · rw [Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]
      exact hw p
    · exact intg_one p q
  · rw [← cramer_apply, cramer_one]
    simp [hc, hwi]
  · rw [quad_col]
    have hcol : (fun a => (1 : Matrix n n E).updateCol i ((star v0)⁻¹ • w) a i) = (star v0)⁻¹ • w := by
      funext a
      simp
    have hst : star ((star v0)⁻¹ • w) = v0⁻¹ • star w := by
      funext p
      simp [star_mul', star_inv₀]
    rw [hcol, hst, smul_dotProduct, mulVec_smul, dotProduct_smul, ← hv0, smul_eq_mul, smul_eq_mul]
    have hsv : star v0 ≠ 0 := by rwa [star_ne_zero]
    field_simp
end GlobalTheory.HermUnimod
