-- Prove2me | solution 1 for GlobalTheory.PeriodLift.period_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:39:56.223033+00:00
-- url     : https://prove2.me/submissions/92053db6-6612-4d2b-928b-b7d40360ca02

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_PeriodCoordinatesFramesLiftTendsto
import Theorems.Thm_GlobalTheory_PeriodLift_exists_matrix_lift
import Theorems.Thm_GlobalTheory_PeriodLift_tendsto_of_span
import Theorems.Thm_GlobalTheory_PeriodLift_hermC_emb_inv_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Topology Filter ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix
open GlobalTheory GlobalTheory.PeriodLift
namespace GlobalTheory.PeriodLift
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ι : Type) (𝓕 : Filter ι) (x₀ : Frame X.Ψ r) (x₁ : ι → Frame X.Ψ r), x₀ ∈ X.dom → (∀ᶠ n in 𝓕, x₁ n ∈ X.dom) → (∀ v ∈ X.Λ, ∀ (τ : X.Ψ) (a : Fin r), Tendsto (fun n => (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)) 𝓕 (𝓝 (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v) else ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a))) → ∀ V ∈ 𝓝 x₀, ∀ᶠ n in 𝓕, ∃ x ∈ V, ∀ (v : Fin r → E) (τ : X.Ψ) (a : Fin r), (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat x τ) a) (Data.emb τ.1 v) else ((mat x τ)⁻¹ *ᵥ Data.emb τ.1 v) a) = (if (a : ℕ) < X.p0 then hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v) else ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a) := by
  intro E _ _ _ r X ι 𝓕 x₀ x₁ h0 h1 h V hV
  have key : ∀ τ : X.Ψ, ∃ B : ι → Matrix (Fin r) (Fin r) ℂ, Tendsto B 𝓕 (𝓝 (mat x₀ τ)) ∧
      ∀ᶠ n in 𝓕, (∀ a : Fin r, (a : ℕ) < X.p0 → ∀ k, B n k a = mat (x₁ n) τ k a) ∧
        (∀ a : Fin r, ¬ (a : ℕ) < X.p0 → ∀ k, (B n)⁻¹ a k = (mat (x₁ n) τ)⁻¹ a k) := by
    intro τ
    refine exists_matrix_lift (fun a : Fin r => (a : ℕ) < X.p0) (mat x₀ τ)
      (fun n => mat (x₁ n) τ) (h0 τ).1 (h1.mono fun n hn => (hn τ).1) ?_ ?_
    · intro a ha k
      have := tendsto_of_span (𝓕 := 𝓕) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => (starRingEnd ℂ) (τ.1 c))
        (fun n v => hermC τ.1 X.Gm (col (mat (x₁ n) τ) a) (Data.emb τ.1 v))
        (fun v => hermC τ.1 X.Gm (col (mat x₀ τ) a) (Data.emb τ.1 v))
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [hermC, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [ha, if_true] using h v hv τ a)
        (fun b => cc (X.Gm⁻¹ b k))
      simpa only [hermC_emb_inv_col τ.1 X.Gm X.Gm_det, col] using this
    · intro a ha k
      have := tendsto_of_span (𝓕 := 𝓕) (X.Λ : Set (Fin r → E)) X.Λ_span
        (fun c => τ.1 c)
        (fun n v => ((mat (x₁ n) τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (fun v => ((mat x₀ τ)⁻¹ *ᵥ Data.emb τ.1 v) a)
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, mul_add, Finset.sum_add_distrib])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by intros; simp [Matrix.mulVec, dotProduct, Data.emb, Finset.mul_sum, mul_left_comm])
        (by simp)
        (fun v hv => by simpa only [ha, if_false] using h v hv τ a)
        (Pi.single k 1)
      simpa [Matrix.mulVec, dotProduct, Data.emb, Pi.single_apply, apply_ite τ.1] using this
  choose B hB hB' using key
  have hx : Tendsto (fun n => (fun τ => B τ n : Frame X.Ψ r)) 𝓕 (𝓝 x₀) :=
    tendsto_pi_nhds.2 fun τ => hB τ
  filter_upwards [hx.eventually_mem hV, eventually_all.2 hB'] with n hn hn'
  refine ⟨_, hn, fun v τ a => ?_⟩
  have hm : mat (fun τ => B τ n : Frame X.Ψ r) τ = B τ n := rfl
  rw [hm]
  by_cases ha : (a : ℕ) < X.p0
  · have : col (B τ n) a = col (mat (x₁ n) τ) a := funext fun k => (hn' τ).1 a ha k
    simp only [ha, if_true, this]
  · simp only [ha, if_false, Matrix.mulVec, dotProduct, (hn' τ).2 a ha]
end GlobalTheory.PeriodLift
