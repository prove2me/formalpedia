-- Prove2me | solution 1 for NonconvexSplitting.ProxGrad.eq47_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:23:28.436446+00:00
-- url     : https://prove2.me/submissions/3836cbb9-ad43-41b0-a39f-a54eed403cd8

import Mathlib.Tactic
import Definitions.Def_NonconvexSplitting_ProxGrad_StandingAssumptions
import Definitions.Def_NonconvexSplitting_ProxGrad_IsProxGradSeq
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
open Filter Topology NonconvexSplitting.ProxGrad NonconvexSplitting.Shared
open scoped RealInnerProductSpace
private theorem prox_finite {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EReal) (β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hp : IsProperFn P) (hx : IsProxGradSeq h P β x) (t : ℕ) : P (x (t+1)) ≠ ⊤ := by
  obtain ⟨z,hz⟩ := hp.2
  have hh := hx t z
  rw [← EReal.coe_toReal hz (hp.1 z)] at hh
  intro he
  simp [he,← EReal.coe_add] at hh


theorem solution {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (P : EuclideanSpace ℝ (Fin n) → EReal) (β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hSA : StandingAssumptions h P) (hβ : 0 < β) (hx : IsProxGradSeq h P β x) (t : ℕ) :
    ∃ w ∈ LimitingSubdiff P (x (t + 1)),
      gradient h (x t) + (1 / β) • (x (t + 1) - x t) + w = 0 := by
  let z := x (t+1)
  let g := gradient h (x t)
  let v := -g-(1/β) • (z-x t)
  have hfin : P z ≠ ⊤ := prox_finite h P β x hSA.P_proper hx t
  have hreg : IsRegularSubgrad P z v := by
    refine ⟨hfin,?_⟩
    intro ε he
    filter_upwards [Metric.ball_mem_nhds z (by positivity : 0 < 2*β*ε)] with w hw
    have hw' : ‖w-z‖ < 2*β*ε := by simpa [Metric.mem_ball,dist_eq_norm] using hw
    by_cases hwtop : P w=⊤
    · rw [hwtop]; exact le_top
    have hpr := hx t w
    rw [← EReal.coe_toReal hfin (hSA.P_proper.1 z),
      ← EReal.coe_toReal hwtop (hSA.P_proper.1 w)] at hpr ⊢
    simp only [← EReal.coe_add,EReal.coe_le_coe_iff] at hpr ⊢
    have hphi : ⟪g,w-x t⟫+1/(2*β)*‖w-x t‖^2-
        (⟪g,z-x t⟫+1/(2*β)*‖z-x t‖^2) = -⟪v,w-z⟫+1/(2*β)*‖w-z‖^2 := by
      have hh : w-x t = (w-z)+(z-x t) := by abel
      have hvinner : ⟪v,w-z⟫ = -⟪g,w-z⟫-(1/β)*⟪z-x t,w-z⟫ := by
        dsimp only [v]
        rw [inner_sub_left,inner_neg_left,real_inner_smul_left]
      rw [hvinner,real_inner_comm (w-z) (z-x t),hh,norm_add_sq_real,inner_add_right]
      field_simp
      ring
    have hrem : 1/(2*β)*‖w-z‖^2 ≤ ε*‖w-z‖ := by
      apply (mul_le_mul_iff_right₀ (show 0 < 2*β by positivity)).mp
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hw'.le (norm_nonneg (w-z))]
    change ⟪g,z-x t⟫+1/(2*β)*‖z-x t‖^2+(P z).toReal ≤
      ⟪g,w-x t⟫+1/(2*β)*‖w-x t‖^2+(P w).toReal at hpr
    linarith
  refine ⟨v,⟨hfin,fun _ => z,fun _ => v,tendsto_const_nhds,tendsto_const_nhds,tendsto_const_nhds,
    fun _ => hreg⟩,?_⟩
  dsimp [v,g,z]
  abel
