-- Prove2me | solution 1 for GlobalTheory.height_rpow_neg_distortion_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:00:17.636313+00:00
-- url     : https://prove2.me/submissions/3f69ab14-e776-4263-81e1-681e12cc70d3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatticeHeightUpdateFrameComponentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightRpowNegDistortionContraction
import Theorems.Thm_GlobalTheory_rpow_neg_le_of_le_mul
import Theorems.Thm_GlobalTheory_T_exists_pos_le_latticeHeight_at_frame
import Theorems.Thm_GlobalTheory_T_gramDet_inequalities_closed_forms
import Theorems.Thm_GlobalTheory_T_latticeHeight_update_frameComponent


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ (τ0 : X.Ψ) (S : Finset (Matrix (Fin r) (Fin r) ℂ)), (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) → (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → ∃ δ c Ω : ℝ, 0 < δ ∧ 0 ≤ c ∧ c < 1 ∧ 1 ≤ Ω ∧ ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ W, (∀ a ∈ S, d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W ^ (-δ) ≤ Ω * d x W ^ (-δ) ∧ d x W ^ (-δ) ≤ Ω * d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W ^ (-δ)) ∧ (W ≠ ⊥ → W ≠ ⊤ → ∑ a ∈ S, d (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) W ^ (-δ) ≤ S.card * (c * d x W ^ (-δ)))) := by
  intro r X d hd τ0 S hS hirr
  obtain ⟨δ, c, ω, hδ, hc0, hc1, hω, H⟩ := GlobalTheory.T.gramDet_inequalities_closed_forms.2.2.1 r S hS hirr
  refine ⟨δ, c, ω ^ δ, hδ, hc0, hc1, Real.one_le_rpow hω hδ.le, ?_⟩
  intro x hx W
  obtain ⟨m, hm, hmd⟩ := GlobalTheory.T.exists_pos_le_latticeHeight_at_frame r X d hd x hx
  have hD : 0 < d x W := lt_of_lt_of_le hm (hmd W)
  obtain ⟨M, hM, hstep⟩ := GlobalTheory.T.latticeHeight_update_frameComponent r X d hd x hx τ0 W
  obtain ⟨H1, H2⟩ := H _ M hM
  have hω0 : 0 < ω := by linarith
  have hpos : ∀ a ∈ S, 0 < ((a * M)ᴴ * (a * M)).det.re := by
    intro a ha
    have := lt_of_lt_of_le hM (H1 a ha).2
    exact (mul_pos_iff_of_pos_left hω0).mp this
  refine ⟨fun a ha => ?_, fun hb ht => ?_⟩
  · rw [hstep a (hS a ha).2.1]
    obtain ⟨h1, h2⟩ := H1 a ha
    have hp := hpos a ha
    generalize ((a * M)ᴴ * (a * M)).det.re = A at h1 h2 hp
    generalize (Mᴴ * M).det.re = B at h1 h2 hM
    have hq : 0 < d x W * (A / B) := mul_pos hD (div_pos hp hM)
    refine ⟨rpow_neg_le_of_le_mul hq hD hω0 hδ.le ?_, rpow_neg_le_of_le_mul hD hq hω0 hδ.le ?_⟩
    · have : 1 ≤ ω * (A / B) := by
        rw [← mul_div_assoc, le_div_iff₀ hM]; linarith
      nlinarith
    · have : A / B ≤ ω := by rw [div_le_iff₀ hM]; exact h1
      nlinarith
  · have h0 : 0 < Module.finrank E W := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      exact hb (Submodule.finrank_eq_zero.mp h)
    have hr : Module.finrank E W < r := by
      have := Submodule.finrank_lt ht
      simpa using this
    have H3 := H2 h0 hr
    have hDp : 0 < d x W ^ (-δ) := Real.rpow_pos_of_pos hD _
    calc _ = ∑ a ∈ S, d x W ^ (-δ) *
          (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) ^ (-δ) := by
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [hstep a (hS a ha).2.1, Real.mul_rpow hD.le (div_pos (hpos a ha) hM).le]
      _ = d x W ^ (-δ) * ∑ a ∈ S,
          (((a * M)ᴴ * (a * M)).det.re / (Mᴴ * M).det.re) ^ (-δ) := by rw [Finset.mul_sum]
      _ ≤ d x W ^ (-δ) * (S.card * c) := mul_le_mul_of_nonneg_left H3 hDp.le
      _ = _ := by ring
end GlobalTheory
