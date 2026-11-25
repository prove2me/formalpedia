-- Prove2me | solution 1 for GlobalTheory.HodgeCurvPoint.dual_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:10:46.316715+00:00
-- url     : https://prove2.me/submissions/3ee86d00-7fd5-4b67-883b-389bc5fc834f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeCurvatureDualMetricPointwiseBound
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_re_form_map
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_isHermitian_map
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_form_map_self
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_posSemidef_map
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_sum_norm_sq
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_gnorm_map_star
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_dotProduct_mulVec_eq_form
import Theorems.Thm_GlobalTheory_HodgeCurvPoint_dotProduct_finsetSum
import Theorems.Thm_GlobalTheory_HermFrame_gnorm_sq
import Theorems.Thm_GlobalTheory_HermFrame_norm_form_le
import Theorems.Thm_GlobalTheory_HermFrame_opNorm_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HermFrame.opNorm_zero



set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame
noncomputable section
open GlobalTheory GlobalTheory.HodgeCurvPoint
variable {g : ℕ}
namespace GlobalTheory.HodgeCurvPoint
theorem _root_.solution : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K : ℝ), 0 < c → 0 ≤ K →
    Y.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, (Bs i).PosSemidef) → (∀ i, 0 < t i) →
    (∀ i x, t i * (x ⬝ᵥ Bs i *ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ j k, ‖Dm j k‖ ≤ K) →
    (Y.map Complex.ofReal).PosDef ∧ ∀ v, ‖form (Y.map Complex.ofReal)⁻¹
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)‖ ≤
      (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map Complex.ofReal) v ^ 2 := by
  intro g a Y Bs Dm s t c K hc hK hY hcY hB ht hBt hD
  have hBs : ∀ i, (Bs i).IsSymm := fun i =>
    IsSymm.ext fun j k => by simpa using (hB i).isHermitian.apply j k
  have hYpos : ∀ v : Fin g → ℂ, c * ∑ j, ‖v j‖ ^ 2 ≤ (form (Y.map ofReal) v v).re := fun v => by
    rw [re_form_map, sum_norm_sq, mul_add]; exact add_le_add (hcY _) (hcY _)
  have hPD : (Y.map ofReal).PosDef := by
    refine posDef_iff.2 ⟨isHermitian_map hY, fun v hv => ?_⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    have hS : 0 < ∑ j, ‖v j‖ ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hj) 2⟩
    have h1 := hYpos v
    rw [form_map_self hY] at h1 ⊢
    rw [ofReal_re] at h1
    rw [Complex.zero_lt_real]
    linarith [mul_pos hc hS]
  have hYpsd := hPD.posSemidef
  have hBpsd : ∀ i, ((Bs i).map ofReal).PosSemidef := fun i =>
    posSemidef_map (hBs i) fun x => by simpa using (hB i).dotProduct_mulVec_nonneg x
  have hgB : ∀ i w, t i * gnorm ((Bs i).map ofReal) w ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 :=
    fun i w => by
      rw [gnorm_sq (hBpsd i), gnorm_sq hYpsd, re_form_map, re_form_map, mul_add]
      exact add_le_add (hBt i _) (hBt i _)
  have hgY : ∀ w : Fin g → ℂ, c * ∑ j, ‖w j‖ ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 := fun w => by
    rw [gnorm_sq hYpsd]; exact hYpos w
  have hgc : 0 ≤ (g : ℝ) / c := div_nonneg (Nat.cast_nonneg _) hc.le

  have hDb : ∀ u v : Fin g → ℂ, ‖u ⬝ᵥ Dm *ᵥ v‖ ≤
      g * K / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
    intro u v
    have h1 : ‖u ⬝ᵥ Dm *ᵥ v‖ ≤ K * ((∑ j, ‖u j‖) * ∑ k, ‖v k‖) := by
      simp only [dotProduct, mulVec]
      calc _ ≤ ∑ j, ‖u j * ∑ k, Dm j k * v k‖ := norm_sum_le _ _
        _ ≤ ∑ j, ‖u j‖ * ∑ k, K * ‖v k‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hD j k) (norm_nonneg _)
        _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
    have hs : ∀ w : Fin g → ℂ, (∑ j, ‖w j‖) ^ 2 ≤ g / c * gnorm (Y.map ofReal) w ^ 2 :=
      fun w => by
        refine sq_sum_le_card_mul_sum_sq.trans ?_
        rw [Finset.card_univ, Fintype.card_fin, div_mul_eq_mul_div, le_div_iff₀ hc]
        nlinarith [hgY w, (Nat.cast_nonneg g : (0 : ℝ) ≤ g)]
    have hab : (∑ j, ‖u j‖) * (∑ k, ‖v k‖) ≤
        g / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
      rw [← pow_le_pow_iff_left₀ (by positivity)
        (mul_nonneg (mul_nonneg hgc (gnorm_nonneg _ _)) (gnorm_nonneg _ _)) two_ne_zero]
      calc ((∑ j, ‖u j‖) * (∑ k, ‖v k‖)) ^ 2 = (∑ j, ‖u j‖) ^ 2 * (∑ k, ‖v k‖) ^ 2 := mul_pow _ _ _
        _ ≤ (g / c * gnorm (Y.map ofReal) u ^ 2) * (g / c * gnorm (Y.map ofReal) v ^ 2) :=
          mul_le_mul (hs u) (hs v) (sq_nonneg _) (mul_nonneg hgc (sq_nonneg _))
        _ = _ := by ring
    calc _ ≤ K * ((∑ j, ‖u j‖) * ∑ k, ‖v k‖) := h1
      _ ≤ K * (g / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v) :=
        mul_le_mul_of_nonneg_left hab hK
      _ = _ := by ring

  have hBb : ∀ i (u v : Fin g → ℂ), ‖u ⬝ᵥ (Bs i).map ofReal *ᵥ v‖ ≤
      gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v / t i := by
    intro i u v
    rw [dotProduct_mulVec_eq_form ((hBs i).map _)]
    refine (norm_form_le (hBpsd i) _ _).trans ?_
    rw [gnorm_map_star]
    rw [← pow_le_pow_iff_left₀ (mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _))
      (div_nonneg (mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _)) (ht i).le) two_ne_zero]
    have a1 : ∀ w, gnorm ((Bs i).map ofReal) w ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 / t i := fun w => by
      rw [le_div_iff₀ (ht i), mul_comm]; exact hgB i w
    calc (gnorm ((Bs i).map ofReal) v * gnorm ((Bs i).map ofReal) u) ^ 2 =
          gnorm ((Bs i).map ofReal) v ^ 2 * gnorm ((Bs i).map ofReal) u ^ 2 := mul_pow _ _ _
      _ ≤ (gnorm (Y.map ofReal) v ^ 2 / t i) * (gnorm (Y.map ofReal) u ^ 2 / t i) :=
          mul_le_mul (a1 v) (a1 u) (sq_nonneg _) (div_nonneg (sq_nonneg _) (ht i).le)
      _ = _ := by ring

  have hPb : ∀ u v : Fin g → ℂ, ‖u ⬝ᵥ (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v‖ ≤
      (g * K / c + ∑ i, ‖s i‖ / t i) * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
    intro u v
    rw [add_mulVec, sum_mulVec, dotProduct_add, dotProduct_finsetSum]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖∑ i, u ⬝ᵥ (s i • (Bs i).map ofReal) *ᵥ v‖ ≤
        ∑ i, ‖s i‖ / t i * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, norm_mul]
      calc _ ≤ ‖s i‖ * (gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v / t i) :=
            mul_le_mul_of_nonneg_left (hBb i u v) (norm_nonneg _)
        _ = _ := by ring
    calc _ ≤ g * K / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v +
          ∑ i, ‖s i‖ / t i * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v :=
          add_le_add (hDb u v) h2
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

  refine ⟨hPD, fun v => ?_⟩
  have hdet : IsUnit (Y.map ofReal).det := (isUnit_iff_isUnit_det _).1 hPD.isUnit
  set x := (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v with hx
  set q := (Y.map ofReal)⁻¹ *ᵥ star x with hq
  have hF : form (Y.map ofReal)⁻¹ x x = q ⬝ᵥ (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v := by
    rw [form]; exact dotProduct_comm _ _
  have hsq : star q = (Y.map ofReal)⁻¹ *ᵥ x := by
    rw [hq, star_mulVec, star_star, (isHermitian_map hY).inv.eq, ← mulVec_transpose,
      transpose_nonsing_inv, (hY.map _).eq]
  have hq2 : gnorm (Y.map ofReal) q ^ 2 = (form (Y.map ofReal)⁻¹ x x).re := by
    rw [gnorm_sq hYpsd]
    simp only [form]
    rw [hsq, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec, dotProduct_comm]
  have hb := hPb q v
  rw [← hF] at hb
  have hre : gnorm (Y.map ofReal) q ^ 2 ≤ ‖form (Y.map ofReal)⁻¹ x x‖ := hq2 ▸ re_le_norm _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rcases (norm_nonneg (form (Y.map ofReal)⁻¹ x x)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · refine le_of_mul_le_mul_right ?_ h0
    calc ‖form (Y.map ofReal)⁻¹ x x‖ * ‖form (Y.map ofReal)⁻¹ x x‖ =
          ‖form (Y.map ofReal)⁻¹ x x‖ ^ 2 := by ring
      _ ≤ _ := h2
      _ = (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map ofReal) v ^ 2 *
          gnorm (Y.map ofReal) q ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (by positivity)
end GlobalTheory.HodgeCurvPoint
