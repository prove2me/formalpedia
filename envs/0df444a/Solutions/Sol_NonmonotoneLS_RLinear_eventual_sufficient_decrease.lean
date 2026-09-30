-- Prove2me | solution 1 for NonmonotoneLS.RLinear.eventual_sufficient_decrease
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:28:38.942864+00:00
-- url     : https://prove2.me/submissions/005b6b0b-532d-4f46-9de0-d607f0bf98b3

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants

open scoped InnerProductSpace NNReal
open Filter
open scoped Topology
noncomputable section

private lemma cost_memory {v η : ℕ → ℝ} {a θ : ℝ}
    (hv : ∀ k, 0 ≤ v k) (ha : 0 < a) (hθ : 0 ≤ θ) (hθα : θ < a)
    (hη : ∀ k, a ≤ η k ∧ η k ≤ 1) (j : ℕ) (hj : 0 < v j) (D : ℝ) :
    ∀ᶠ k in atTop, D * θ ^ k ≤ NonmonotoneLS.Shared.costC v id η k := by
  let Q := NonmonotoneLS.Shared.costQ η
  let C := NonmonotoneLS.Shared.costC v id η
  have hη0 (k : ℕ) : 0 ≤ η k := le_trans ha.le (hη k).1
  have hQ (k : ℕ) : 0 < Q k ∧ Q k ≤ (k : ℝ) + 1 := by
    induction k with
    | zero => norm_num [Q, NonmonotoneLS.Shared.costQ]
    | succ k ih =>
      dsimp [Q, NonmonotoneLS.Shared.costQ]
      have hmul := mul_le_mul_of_nonneg_right (hη k).2 ih.1.le
      constructor
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (hη0 k) ih.1.le) zero_lt_one
      · norm_num only [Nat.cast_add, Nat.cast_one]
        dsimp [Q] at ih
        nlinarith
  let P : ℕ → ℝ := fun k => Q k * C k
  have hrec (k : ℕ) : P (k + 1) = η k * P k + v (k + 1) := by
    dsimp [P, C, NonmonotoneLS.Shared.costC]
    rw [mul_div_cancel₀ _ (ne_of_gt (hQ (k + 1)).1)]
    dsimp [Q]
    ring
  have hP (k : ℕ) : 0 ≤ P k ∧ v k ≤ P k := by
    induction k with
    | zero => simpa [P, Q, C, NonmonotoneLS.Shared.costC,
        NonmonotoneLS.Shared.costQ] using hv 0
    | succ k ih =>
      rw [hrec]
      constructor
      · exact add_nonneg (mul_nonneg (hη0 k) ih.1) (hv (k + 1))
      · nlinarith [mul_nonneg (hη0 k) ih.1]
  let b := P j / a ^ j
  have hb : 0 < b := div_pos (lt_of_lt_of_le hj (hP j).2) (pow_pos ha _)
  have hlow (k : ℕ) (hk : j ≤ k) : b * a ^ k ≤ P k := by
    induction k, hk using Nat.le_induction with
    | base => dsimp [b]; rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos ha _))]
    | succ k hk ih =>
      rw [hrec, pow_succ]
      have h1 := mul_le_mul_of_nonneg_left ih ha.le
      have h2 := mul_le_mul_of_nonneg_right (hη k).1 (hP k).1
      nlinarith [hv (k + 1)]
  have hr0 : 0 ≤ θ / a := div_nonneg hθ ha.le
  have hr1 : θ / a < 1 := (div_lt_one ha).mpr hθα
  have hlim : Tendsto (fun k : ℕ => D * ((k : ℝ) + 1) * (θ / a) ^ k) atTop (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    convert (h1.add h2).const_mul D using 1
    · ext k; ring
    · simp
  have hev := hlim.eventually_lt_const hb
  filter_upwards [hev, eventually_ge_atTop j] with k hk hjk
  have hsmall : D * θ ^ k * ((k : ℝ) + 1) ≤ b * a ^ k := by
    calc
      D * θ ^ k * ((k : ℝ) + 1) =
          (D * ((k : ℝ) + 1) * (θ / a) ^ k) * a ^ k := by
            rw [div_pow]
            field_simp [ne_of_gt ha]
            <;> ring
      _ ≤ b * a ^ k := mul_le_mul_of_nonneg_right hk.le (pow_nonneg ha.le k)
  by_cases hD : 0 ≤ D
  · have hnonneg : 0 ≤ D * θ ^ k := mul_nonneg hD (pow_nonneg hθ k)
    have hprod := mul_le_mul_of_nonneg_left (hQ k).2 hnonneg
    have hp := hlow k hjk
    have : Q k * (D * θ ^ k) ≤ Q k * C k := by dsimp [P] at hp; nlinarith
    exact (mul_le_mul_iff_right₀ (hQ k).1).mp this
  · have : D * θ ^ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hD) (pow_nonneg hθ k)
    have hc : 0 ≤ C k := (mul_nonneg_iff_of_pos_left (hQ k).1).mp (hP k).1
    exact this.trans hc

private lemma global_min_gradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (u : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f u ≤ f y) : gradient f u = 0 := by
  have h : IsLocalMin f u := Filter.Eventually.of_forall hmin
  simp [gradient, h.fderiv_eq_zero]

private lemma gradient_decay {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (θ c : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hRlin : ∀ k, f (x k) - f xstar ≤ c * θ ^ k)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKc : IsClosed K) (hKb : Bornology.IsBounded K)
    (hxK : ∀ k, x k ∈ K) (γ : ℝ) (hγ : 0 < γ)
    (hscK : ∀ u ∈ K, ∀ v ∈ K,
      f v + ⟪gradient f v, u - v⟫_ℝ + 1 / (2 * γ) * ‖u - v‖ ^ 2 ≤ f u)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (gradient f) K) :
    ∀ k, ‖gradient f (x k)‖ ^ 2 ≤ 2 * γ * (L : ℝ) ^ 2 * c * θ ^ k := by
  have hcompact : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKc hKb
  obtain ⟨y, hyK, hym⟩ := hcompact.exists_isMinOn ⟨x 0, hxK 0⟩ hf.continuous.continuousOn
  have hlim : Tendsto (fun k : ℕ => c * θ ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).const_mul c
  have hyle : f y - f xstar ≤ 0 := ge_of_tendsto hlim <| .of_forall fun k =>
    (sub_le_sub_right (hym (hxK k)) _).trans (hRlin k)
  have hyf : f y = f xstar := by linarith [hmin y]
  have hgy : gradient f y = 0 := global_min_gradient f y (by simpa [hyf] using hmin)
  intro k
  have hsc := hscK (x k) (hxK k) y hyK
  simp only [hgy, inner_zero_left, add_zero, hyf] at hsc
  have hdiv : ‖x k - y‖ ^ 2 / (2 * γ) ≤ f (x k) - f xstar := by
    have hh : 1 / (2 * γ) * ‖x k - y‖ ^ 2 ≤ f (x k) - f xstar := by linarith
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hh
  have hdist : ‖x k - y‖ ^ 2 ≤ 2 * γ * c * θ ^ k := by
    have hh := (div_le_iff₀ (show 0 < 2 * γ by positivity)).mp hdiv
    have hh' := mul_le_mul_of_nonneg_left (hRlin k) (show 0 ≤ 2 * γ by positivity)
    nlinarith
  have hnorm := hLip.norm_sub_le (hxK k) hyK
  simp only [hgy, sub_zero] at hnorm
  have hsquare : ‖gradient f (x k)‖ ^ 2 ≤ (L : ℝ) ^ 2 * ‖x k - y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖gradient f (x k)‖ - (L : ℝ) * ‖x k - y‖), norm_nonneg (gradient f (x k)),
      mul_nonneg L.coe_nonneg (norm_nonneg (x k - y))]
  have := mul_le_mul_of_nonneg_left hdist (sq_nonneg (L : ℝ))
  nlinarith

namespace NonmonotoneLS.RLinear

/-- Theorem 3.2 (p. 1051): let `x*` minimize `f` and let `x_{k+1} = x_k + α_k d_k` be any sequence
with `f(x_k) - f(x*) ≤ cθ^k`, `θ ∈ (0, 1)`, lying in a closed, bounded, convex set `K` on which
(3.1) holds with constant `γ` and `∇f` is `L`-Lipschitz, whose directions satisfy (2.4)–(2.5) for
all sufficiently large `k`, and whose steps satisfy `0 < α_k ≤ μ`. If `C_k` is given by (1.6) with
`η_k ∈ [η_min, η_max] ⊆ [0, 1]` and `η_min > θ`, then for every `δ ∈ (0, 1)` the condition (1.4),
`f(x_k + α_k d_k) ≤ C_k + δ α_k ∇f(x_k) d_k`, holds for all sufficiently large `k`. -/
theorem _root_.solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hupd : ∀ k, x (k + 1) = x k + α k • d k)
    (θ c : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hRlin : ∀ k, f (x k) - f xstar ≤ c * θ ^ k)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hKc : IsClosed K) (hKb : Bornology.IsBounded K)
    (hKconv : Convex ℝ K) (hxK : ∀ k, x k ∈ K)
    (γ : ℝ) (hγ : 0 < γ)
    (hscK : ∀ u ∈ K, ∀ v ∈ K,
      f v + ⟪gradient f v, u - v⟫_ℝ + 1 / (2 * γ) * ‖u - v‖ ^ 2 ≤ f u)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (gradient f) K)
    (hdir : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ k in atTop,
      ⟪gradient f (x k), d k⟫_ℝ ≤ -c₁ * ‖gradient f (x k)‖ ^ 2 ∧
        ‖d k‖ ≤ c₂ * ‖gradient f (x k)‖)
    (μ : ℝ) (hα : ∀ k, 0 < α k ∧ α k ≤ μ)
    (ηmin ηmax : ℝ) (hηmin0 : 0 ≤ ηmin) (hηle : ηmin ≤ ηmax) (hηmax1 : ηmax ≤ 1)
    (hη : ∀ k, η k ∈ Set.Icc ηmin ηmax) (hθη : θ < ηmin)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∀ᶠ k in atTop,
      f (x k + α k • d k) ≤ Shared.costC f x η k + δ * α k * ⟪gradient f (x k), d k⟫_ℝ := by
  classical
  let v : ℕ → ℝ := fun k => f (x k) - f xstar
  have hv (k : ℕ) : 0 ≤ v k := sub_nonneg.mpr (hmin (x k))
  have ha : 0 < ηmin := lt_trans hθ0 hθη
  have hη0 (k : ℕ) : 0 ≤ η k := hηmin0.trans (hη k).1
  have hQpos (k : ℕ) : 0 < Shared.costQ η k := by
    induction k with
    | zero => norm_num [Shared.costQ]
    | succ k ih =>
      exact add_pos_of_nonneg_of_pos (mul_nonneg (hη0 k) ih.le) zero_lt_one
  have hcenter (k : ℕ) : Shared.costC f x η k - f xstar = Shared.costC v id η k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Shared.costC]
      rw [← ih]
      have hn : η k * Shared.costQ η k + 1 ≠ 0 := ne_of_gt (hQpos (k + 1))
      dsimp [v]
      simp only [Shared.costQ]
      field_simp
      <;> ring
  by_cases hz : ∀ k, v k = 0
  · have hc (k : ℕ) : Shared.costC v id η k = 0 := by
      induction k with
      | zero => simpa [Shared.costC] using hz 0
      | succ k ih => simp [Shared.costC, ih, hz]
    filter_upwards [] with k
    have hxval : f (x k) = f xstar := sub_eq_zero.mp (hz k)
    have hxval' : f (x (k + 1)) = f xstar := sub_eq_zero.mp (hz (k + 1))
    have hg : gradient f (x k) = 0 := global_min_gradient f (x k) (by simpa [hxval] using hmin)
    rw [← hupd k, hg]
    simp only [inner_zero_left, mul_zero, add_zero]
    linarith [hcenter k, hc k]
  · push_neg at hz
    obtain ⟨j, hj⟩ := hz
    have hjpos : 0 < v j := lt_of_le_of_ne (hv j) (Ne.symm hj)
    obtain ⟨c₁, c₂, hc₁, hc₂, hdir⟩ := hdir
    have hμ : 0 < μ := (hα 0).1.trans_le (hα 0).2
    have hc : 0 ≤ c := by simpa using (hv 0).trans (hRlin 0)
    let B : ℝ := 2 * γ * (L : ℝ) ^ 2 * c
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hgrad := gradient_decay f hf xstar hmin x θ c hθ0 hθ1 hRlin K hKc hKb hxK γ hγ hscK L hLip
    have hmem := cost_memory hv ha hθ0.le hθη
      (fun k => ⟨(hη k).1, (hη k).2.trans hηmax1⟩) j hjpos
      (c * θ + δ * μ * c₂ * B)
    filter_upwards [hdir, hmem] with k hdk hmemory
    have hnorm := mul_le_mul_of_nonneg_left hdk.2 (norm_nonneg (gradient f (x k)))
    have hinner := real_inner_le_norm (-gradient f (x k)) (d k)
    simp only [inner_neg_left, norm_neg] at hinner
    have hdot : -c₂ * ‖gradient f (x k)‖ ^ 2 ≤ ⟪gradient f (x k), d k⟫_ℝ := by
      nlinarith
    have hdprod := mul_le_mul_of_nonneg_left hdot (mul_pos hδ0 (hα k).1).le
    have halpha := mul_le_mul_of_nonneg_left (hα k).2
      (mul_nonneg (mul_nonneg hδ0.le hc₂.le) (sq_nonneg ‖gradient f (x k)‖))
    have hdecay := mul_le_mul_of_nonneg_left (hgrad k)
      (mul_nonneg (mul_nonneg hδ0.le hμ.le) hc₂.le)
    have hnext := hRlin (k + 1)
    rw [pow_succ] at hnext
    rw [← hcenter k] at hmemory
    rw [← hupd k]
    dsimp [B] at *
    nlinarith


end NonmonotoneLS.RLinear
