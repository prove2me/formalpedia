-- Prove2me | solution 1 for GlobalTheory.EtaChar.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:19:14.685411+00:00
-- url     : https://prove2.me/submissions/a3c65282-a06b-4f56-8eb6-1103b5ecfbfe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm
import Theorems.Thm_GlobalTheory_EtaChar_eta_eq_one_iff
import Theorems.Thm_GlobalTheory_EtaChar_eta_mul
import Theorems.Thm_GlobalTheory_EtaChar_eta_of_norm_eq
import Theorems.Thm_GlobalTheory_T_exists_mul_star_eq_of_norm_one_unramifiedQuadratic


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.EtaChar
namespace GlobalTheory.EtaChar
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E], (∀ x y : F, x ≠ 0 → y ≠ 0 → eta (x * y) = eta x * eta y) ∧ (∀ x : F, ‖x‖ = 1 → eta x = 1) ∧ (∀ x : F, x ≠ 0 → (eta x = 1 ↔ ∃ v : E, v * star v = algebraMap F E x)) ∧ IsLocallyConstant (fun x : {x : F // x ≠ 0} => eta x.1) := by
  intro F E _ _ _ _ hU
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  refine ⟨fun x y hx hy => eta_mul F x y hx hy, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · exact (eta_eq_one_iff x).2 ⟨1, by rw [hx, norm_one, one_pow]⟩
  · rw [eta_eq_one_iff]
    constructor
    · rintro ⟨y, hy⟩
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hx (norm_eq_zero.1 (by simpa using hy))
      obtain ⟨v, hv⟩ := GlobalTheory.T.exists_mul_star_eq_of_norm_one_unramifiedQuadratic F E (x / y ^ 2) (by rw [norm_div, norm_pow, hy, div_self (by positivity)])
      refine ⟨v * algebraMap F E y, ?_⟩
      rw [star_mul', hU.star_fix y]
      calc v * algebraMap F E y * (star v * algebraMap F E y)
          = (v * star v) * algebraMap F E (y ^ 2) := by rw [map_pow]; ring
        _ = algebraMap F E x := by rw [hv, ← map_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hy0)]
    · rintro ⟨v, hv⟩
      obtain ⟨z, hz⟩ := hU.unram v
      refine ⟨z, ?_⟩
      have := congrArg norm hv
      rw [norm_algebraMap', norm_mul, hU.norm_star, hz] at this
      rw [← this, sq]
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hx : 0 < ‖x.1‖ := norm_pos_iff.2 x.2
    have hmem : {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} ∈ 𝓝 x := by
      have : IsOpen {y : {x : F // x ≠ 0} | ‖y.1 - x.1‖ < ‖x.1‖} :=
        isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const)) continuous_const
      exact this.mem_nhds (by simpa using hx)
    filter_upwards [hmem] with y hy
    apply eta_of_norm_eq
    have h2 : y.1 = x.1 + (y.1 - x.1) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hy), max_eq_left hy.le]
end GlobalTheory.EtaChar
