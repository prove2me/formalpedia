-- Prove2me | solution 1 for GraphonMF.Stability.theorem_2_1_c
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T02:26:45.588659+00:00
-- url     : https://prove2.me/submissions/5bfa66fa-3da1-456c-b991-947f8a1d51f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GraphonMF_Stability_Setting
import Theorems.Thm_GraphonMF_Stability_display_p3604
import Theorems.Thm_GraphonMF_Stability_remark_2_1
import Theorems.Thm_GraphonMF_Stability_measurable_W2T

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.Stability

theorem W2T_eq_W2t {T : ℝ≥0} {d : ℕ} (μ ν : Measure (Cd T d)) :
    W2T μ ν = W2t T μ ν := by
  have hsup : ∀ x : Cd T d, supUpTo T x = ‖x‖ := by
    intro x
    unfold supUpTo
    rw [ContinuousMap.norm_eq_iSup_norm]
    congr 1
    funext s
    rw [if_pos s.2.2]
  unfold W2T W2t WassersteinDRO.Duality.wassersteinDistance
  simp_rw [hsup]

end GraphonMF.Stability

open GraphonMF.Stability in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0)
    (hT : 0 < T) (P : Measure Ω) (μ0 : I → Measure (State d))
    (X0 : I → Ω → State d) (B : I → ℝ≥0 → Ω → State d)
    (noise : NoiseSetting P μ0 X0 B)
    (b : State d → State d → State d)
    (σ : State d → State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hc : Cond21 ε μ0 b σ)
    (G : I → I → ℝ) (Gs : ℕ → I → I → ℝ)
    (hG : IsGraphon G) (hGs : ∀ n, IsGraphon (Gs n))
    (X : I → Ω → Cd T d) (Xs : ℕ → I → Ω → Cd T d)
    (hX : IsGraphonSolution P μ0 X0 B noise G b σ X)
    (hXs : ∀ n, IsGraphonSolution P μ0 X0 B noise (Gs n) b σ (Xs n))
    (hcut : Tendsto (fun n => cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0)) :
    (∀ n, Measurable (fun u => W2T (law P (Xs n) u) (law P X u))) ∧
      Tendsto (fun n => ∫⁻ u, W2T (law P (Xs n) u) (law P X u) ^ (2 : ℝ))
        atTop (𝓝 0) := by
  refine ⟨fun n => ?_, ?_⟩
  · exact measurable_W2T _ _ (hXs n).1.1 hX.1.1 (hXs n).1.2.1 hX.1.2.1
  have hε : 0 < ε := hc.1
  obtain ⟨κ, hκ, hM⟩ := display_p3604 T hT P μ0 X0 B noise b σ ε hc G hG X hX
  have hop := remark_2_1 G Gs hG hGs hcut
  set a : ℕ → ℝ := fun n => opNorm (fun u v => Gs n u v - G u v) with ha
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  rcases eq_or_ne e ⊤ with rfl | hetop
  · exact Eventually.of_forall (fun _ => le_top)
  set r := e.toReal with hr
  have hr0 : 0 < r := ENNReal.toReal_pos he.ne' hetop
  -- choose M with κ * M^(-ε) < r/2
  have hlim : Tendsto (fun M : ℝ => κ * M ^ (-ε)) atTop (𝓝 (κ * 0)) :=
    (tendsto_rpow_neg_atTop hε).const_mul κ
  rw [mul_zero] at hlim
  obtain ⟨M, hM1, hM0⟩ :=
    ((hlim.eventually (gt_mem_nhds (half_pos hr0))).and (eventually_gt_atTop (0 : ℝ))).exists
  obtain ⟨κM, hκM, hbound⟩ := hM M hM0
  have hlim2 : Tendsto (fun n => κ * κM * a n) atTop (𝓝 (κ * κM * 0)) :=
    hop.const_mul (κ * κM)
  rw [mul_zero] at hlim2
  filter_upwards [hlim2.eventually (gt_mem_nhds (half_pos hr0))] with n hn
  have h1 := hbound (Gs n) (Xs n) (hGs n) (hXs n) T le_rfl
  have heq : (fun u => W2T (law P (Xs n) u) (law P X u) ^ (2 : ℝ)) =
      (fun u => W2t T (law P (Xs n) u) (law P X u) ^ (2 : ℝ)) := by
    funext u; rw [W2T_eq_W2t]
  rw [heq]
  refine h1.trans ?_
  rw [← ENNReal.ofReal_toReal hetop]
  apply ENNReal.ofReal_le_ofReal
  have : 1 / M ^ ε = M ^ (-ε) := by rw [Real.rpow_neg hM0.le, one_div]
  rw [this]
  have : κ * (M ^ (-ε) + κM * a n) = κ * M ^ (-ε) + κ * κM * a n := by ring
  rw [this, ← hr]
  linarith
