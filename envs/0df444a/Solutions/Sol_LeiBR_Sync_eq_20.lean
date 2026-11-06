-- Prove2me | solution 1 for LeiBR.Sync.eq_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T11:50:56.86299+00:00
-- url     : https://prove2.me/submissions/9087a532-6a80-453b-acb9-3ab71d76aed0

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame
import Definitions.Def_LeiBR_Sync_Algorithm1
import Theorems.Thm_LeiBR_Sync_eq_9
import Theorems.Thm_LeiBR_Sync_fixed_point

open MeasureTheory

namespace LeiBRSE20
open LeiBR.Sync

variable {N : ℕ} {n : Fin N → ℕ}

lemma amgm (z y : ℝ) (hz : 0 ≤ z) (hy : 0 < y) : Real.sqrt z ≤ (z / y + y) / 2 := by
  have hs := Real.sq_sqrt hz
  have h0 := Real.sqrt_nonneg z
  rw [div_add' _ _ _ hy.ne', div_div, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt z - y)]

/-- Jensen for the square: `E X ≤ √(E X²)` for a bounded nonnegative measurable `X`. -/
lemma int_le_sqrt {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable X) (CX : ℝ) (hXb : ∀ ω, X ω ≤ CX) :
    ∫ ω, X ω ∂P ≤ Real.sqrt (∫ ω, X ω ^ 2 ∂P) := by
  have hXi : Integrable X P := Integrable.of_bound hXm.aestronglyMeasurable CX
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]; exact hXb ω)
  have hX2i : Integrable (fun ω => X ω ^ 2) P := Integrable.of_bound
    (hXm.pow_const 2).aestronglyMeasurable
    (CX ^ 2) (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (hX0 ω) (hXb ω) 2)
  set S := ∫ ω, X ω ^ 2 ∂P with hS
  have hS0 : 0 ≤ S := integral_nonneg fun ω => sq_nonneg _
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set y := Real.sqrt S + δ with hy
  have hy0 : 0 < y := by positivity
  have hpt : ∀ ω, X ω ≤ (X ω ^ 2 / y + y) / 2 := by
    intro ω
    have := amgm (X ω ^ 2) y (sq_nonneg _) hy0
    rwa [Real.sqrt_sq (hX0 ω)] at this
  have h1 : ∫ ω, X ω ∂P ≤ ∫ ω, (X ω ^ 2 / y + y) / 2 ∂P :=
    integral_mono hXi (((hX2i.div_const y).add (integrable_const y)).div_const 2) hpt
  rw [integral_div, integral_add (hX2i.div_const y) (integrable_const y), integral_div] at h1
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
  have hSy : S / y ≤ Real.sqrt S := by
    rw [div_le_iff₀ hy0]
    have := Real.sq_sqrt hS0
    have := Real.sqrt_nonneg S
    nlinarith
  rw [← hS] at h1
  linarith

lemma blockDist_nonneg (x y : Profile n) : 0 ≤ blockDist x y := Real.sqrt_nonneg _

lemma blockDist_tri (x y z : Profile n) : blockDist x z ≤ blockDist x y + blockDist y z := by
  let ua : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i => ‖x i - y i‖)
  let ub : EuclideanSpace ℝ (Fin N) := WithLp.toLp 2 (fun i => ‖y i - z i‖)
  have hw : ∀ u v : Profile n, blockDist u v =
      ‖(WithLp.toLp 2 (fun i => ‖u i - v i‖) : EuclideanSpace ℝ (Fin N))‖ := by
    intro u v
    rw [EuclideanSpace.norm_eq]
    unfold blockDist
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Real.norm_eq_abs, sq_abs]
  have hle : blockDist x z ≤ ‖ua + ub‖ := by
    rw [EuclideanSpace.norm_eq]
    unfold blockDist
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    simp only [ua, ub, WithLp.ofLp_add, Pi.add_apply, Real.norm_eq_abs, sq_abs]
    have h := norm_sub_le_norm_sub_add_norm_sub (x i) (y i) (z i)
    have : ‖x i - z i‖ ^ 2 ≤ (‖x i - y i‖ + ‖y i - z i‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    simpa [abs_of_nonneg (add_nonneg (norm_nonneg (x i - y i)) (norm_nonneg (y i - z i)))]
      using this
  rw [hw x y, hw y z]
  exact hle.trans (norm_add_le ua ub)

lemma comp_le_blockDist (x y : Profile n) (i : Fin N) : ‖x i - y i‖ ≤ blockDist x y := by
  unfold blockDist
  rw [← Real.sqrt_sq (norm_nonneg (x i - y i))]
  refine Real.sqrt_le_sqrt ?_
  exact Finset.single_le_sum (f := fun i => ‖x i - y i‖ ^ 2) (fun j _ => sq_nonneg _)
    (Finset.mem_univ i)

lemma blockDist_le_sup (x y : Profile n) : blockDist x y ≤ Real.sqrt N * ‖x - y‖ := by
  unfold blockDist
  calc Real.sqrt (∑ i : Fin N, ‖x i - y i‖ ^ 2) ≤ Real.sqrt (∑ _i : Fin N, ‖x - y‖ ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (by
            have := norm_le_pi_norm (x - y) i
            simpa using this) 2)
    _ = Real.sqrt N * ‖x - y‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma meas_bd {Ω : Type*} [MeasurableSpace Ω] (u v : Ω → Profile n) (hu : Measurable u)
    (hv : Measurable v) : Measurable (fun ω => blockDist (u ω) (v ω)) := by
  unfold blockDist
  exact (Finset.measurable_sum _ fun i _ =>
    ((hu.eval (a := i)).sub (hv.eval (a := i))).norm.pow_const 2).sqrt

end LeiBRSE20

open LeiBR.Sync LeiBRSE20 in
theorem solution
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (hA2 : Assumption2 X (payoff P ξ ψ) μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (xs : Profile n) (hxs : IsNashEq X (payoff P ξ ψ) xs)
    (F : Filtration ℕ mΩ) (α : Fin N → ℕ → ℝ) (hα : ∀ i k, 0 ≤ α i k)
    (x0 : Profile n) (x : ℕ → Ω → Profile n) (hx : IsAlg1 P F X xhat α x0 x) :
    ∀ k : ℕ, ∫ ω, blockDist (x (k + 1) ω) xs ∂P ≤
      specNorm (Gamma X (payoff P ξ ψ) μ) * ∫ ω, blockDist (x k ω) xs ∂P +
        Real.sqrt N * ⨆ i : Fin N, α i k := by
  intro k
  set a := specNorm (Gamma X (payoff P ξ ψ) μ) with ha
  have ha0 : 0 ≤ a := norm_nonneg _
  set S := stratSet X with hSdef
  have hmem : ∀ k ω, x k ω ∈ S := hx.2.2.1
  have hmeas : ∀ k, Measurable (x k) := fun k => (hx.2.2.2.1 k).mono (F.le k) le_rfl
  have h9 := eq_9 P ξ X ψ gψ M hA1 μ hμ xhat hxhat hA2
  have hfix : xhat xs = xs := funext (fixed_point P ξ X ψ gψ M hA1 μ hμ xhat hxhat xs hxs)
  have hxsS : xs ∈ S := hxs.1
  -- continuity of xhat on S
  have hcont : ContinuousOn xhat S := by
    refine continuousOn_pi.2 fun i => ?_
    refine (LipschitzOnWith.of_dist_le_mul (K := Real.toNNReal (a * Real.sqrt N))
      fun y hy y' hy' => ?_).continuousOn
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    calc ‖xhat y i - xhat y' i‖ ≤ blockDist (xhat y) (xhat y') := comp_le_blockDist _ _ i
      _ ≤ a * blockDist y y' := h9 y' hy' y hy
      _ ≤ a * (Real.sqrt N * ‖y - y'‖) :=
          mul_le_mul_of_nonneg_left (blockDist_le_sup y y') ha0
      _ = a * Real.sqrt N * ‖y - y'‖ := by ring
  have hxhm : ∀ k, Measurable (fun ω => xhat (x k ω)) := by
    intro k
    have h1 : Measurable (fun ω => (⟨x k ω, hmem k ω⟩ : S)) := (hmeas k).subtype_mk
    have h2 : Continuous (S.restrict xhat) := hcont.restrict
    exact h2.measurable.comp h1
  -- boundedness
  have hB : ∀ i, ∃ B : ℝ, ∀ z ∈ X i, ‖z‖ ≤ B := fun i =>
    isBounded_iff_forall_norm_le.1 (hA1.1 i).2.1.isBounded
  choose B hB using hB
  have hxhS : ∀ y ∈ S, xhat y ∈ S := fun y hy =>
    Set.mem_univ_pi.2 fun i => (hxhat y hy i).1
  have hbd : ∀ u ∈ S, ∀ v ∈ S, blockDist u v ≤ Real.sqrt (∑ i, (2 * B i) ^ 2) := by
    intro u hu v hv
    unfold blockDist
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have hu' := hB i _ (Set.mem_univ_pi.1 hu i)
    have hv' := hB i _ (Set.mem_univ_pi.1 hv i)
    have : ‖u i - v i‖ ≤ 2 * B i := (norm_sub_le _ _).trans (by linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  set Bd := Real.sqrt (∑ i, (2 * B i) ^ 2) with hBd
  have hint : ∀ (u v : Ω → Profile n), Measurable u → Measurable v → (∀ ω, u ω ∈ S) →
      (∀ ω, v ω ∈ S) → Integrable (fun ω => blockDist (u ω) (v ω)) P := by
    intro u v hu hv huS hvS
    refine Integrable.of_bound (meas_bd u v hu hv).aestronglyMeasurable Bd
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (blockDist_nonneg _ _)]
    exact hbd _ (huS ω) _ (hvS ω)
  -- the error term W = ‖(‖x_{i,k+1} - x̂_i(x_k)‖)_i‖
  set W : Ω → ℝ := fun ω => blockDist (x (k + 1) ω) (xhat (x k ω)) with hW
  have hWm : Measurable W := meas_bd _ _ (hmeas (k + 1)) (hxhm k)
  have hWb : ∀ ω, W ω ≤ Bd := fun ω => hbd _ (hmem _ ω) _ (hxhS _ (hmem k ω))
  have hcomp_int : ∀ i, Integrable (fun ω => ‖x (k + 1) ω i - xhat (x k ω) i‖ ^ 2) P := by
    intro i
    have hm : Measurable (fun ω => ‖x (k + 1) ω i - xhat (x k ω) i‖ ^ 2) :=
      (((hmeas (k + 1)).eval (a := i)).sub ((hxhm k).eval (a := i))).norm.pow_const 2
    refine Integrable.of_bound hm.aestronglyMeasurable ((2 * B i) ^ 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hu' := hB i _ (Set.mem_univ_pi.1 (hmem (k + 1) ω) i)
    have hv' := hB i _ (Set.mem_univ_pi.1 (hxhS _ (hmem k ω)) i)
    exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith)) 2
  have hcomp : ∀ i, ∫ ω, ‖x (k + 1) ω i - xhat (x k ω) i‖ ^ 2 ∂P ≤ α i k ^ 2 := by
    intro i
    rw [← integral_condExp (F.le k)]
    have := hx.2.2.2.2 k i
    calc ∫ ω, (P[fun ω => ‖x (k + 1) ω i - xhat (x k ω) i‖ ^ 2 | F k]) ω ∂P
        ≤ ∫ _ω, α i k ^ 2 ∂P := integral_mono_ae integrable_condExp (integrable_const _) this
      _ = α i k ^ 2 := by simp
  have hW2 : ∫ ω, W ω ^ 2 ∂P ≤ ∑ i, α i k ^ 2 := by
    have e : ∀ ω, W ω ^ 2 = ∑ i, ‖x (k + 1) ω i - xhat (x k ω) i‖ ^ 2 := by
      intro ω
      simp only [hW, blockDist]
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp_rw [e]
    rw [integral_finset_sum _ fun i _ => hcomp_int i]
    exact Finset.sum_le_sum fun i _ => hcomp i
  set A := ⨆ i : Fin N, α i k with hA
  have hA0 : 0 ≤ A := Real.iSup_nonneg fun i => hα i k
  have hαA : ∀ i, α i k ≤ A := fun i => le_ciSup (f := fun i => α i k) (Finite.bddAbove_range _) i
  have hsumA : Real.sqrt (∑ i, α i k ^ 2) ≤ Real.sqrt N * A := by
    calc Real.sqrt (∑ i, α i k ^ 2) ≤ Real.sqrt (∑ _i : Fin N, A ^ 2) :=
          Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hα i k) (hαA i) 2)
      _ = Real.sqrt N * A := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hA0]
  have hEW : ∫ ω, W ω ∂P ≤ Real.sqrt N * A :=
    (int_le_sqrt P W (fun ω => blockDist_nonneg _ _) hWm Bd hWb).trans
      ((Real.sqrt_le_sqrt hW2).trans hsumA)
  -- pointwise (12)
  have hpt : ∀ ω, blockDist (x (k + 1) ω) xs ≤ W ω + a * blockDist (x k ω) xs := by
    intro ω
    have h1 := blockDist_tri (x (k + 1) ω) (xhat (x k ω)) xs
    have h2 := h9 xs hxsS (x k ω) (hmem k ω)
    rw [hfix] at h2
    simp only [hW]
    linarith
  have hI1 := hint (x (k + 1)) (fun _ => xs) (hmeas _) measurable_const (hmem _) (fun _ => hxsS)
  have hI2 := hint (x k) (fun _ => xs) (hmeas _) measurable_const (hmem _) (fun _ => hxsS)
  have hWi := hint (x (k + 1)) (fun ω => xhat (x k ω)) (hmeas _) (hxhm k) (hmem _)
    (fun ω => hxhS _ (hmem k ω))
  calc ∫ ω, blockDist (x (k + 1) ω) xs ∂P
      ≤ ∫ ω, (W ω + a * blockDist (x k ω) xs) ∂P := integral_mono hI1 (hWi.add (hI2.const_mul a)) hpt
    _ = ∫ ω, W ω ∂P + a * ∫ ω, blockDist (x k ω) xs ∂P := by
        rw [integral_add hWi (hI2.const_mul a), integral_const_mul]
    _ ≤ a * ∫ ω, blockDist (x k ω) xs ∂P + Real.sqrt N * A := by linarith
