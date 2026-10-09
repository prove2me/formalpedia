-- Prove2me | solution 1 for GhadimiLan.RSG.weighting_identity
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-08T23:10:08.251032+00:00
-- url     : https://prove2.me/submissions/e45796cc-c0d5-4db2-80bc-8d5aad819972

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open GhadimiLan.RSG
set_option autoImplicit false

namespace GhadimiLan.RSG.Sol_weighting_identity

/-- The RSG iterate as a deterministic function of the noise path `s : ℕ → Ξ`:
`Φ 0 s = Φ 1 s = x1` and `Φ (k + 1) s = Φ k s − γ k • G (Φ k s) (s k)` for `k ≥ 1`. -/
noncomputable def Φ {n : ℕ} {Ξ : Type*} (G : E n → Ξ → E n) (γ : ℕ → ℝ) (x1 : E n) :
    ℕ → (ℕ → Ξ) → E n
  | 0 => fun _ => x1
  | 1 => fun _ => x1
  | k + 2 => fun s => Φ G γ x1 (k + 1) s - γ (k + 1) • G (Φ G γ x1 (k + 1) s) (s (k + 1))

/-- Along an RSG run, `x k ω = Φ k (ξ · ω)` for every `k ≥ 1`: the iterate is a function of the
noise path. -/
private lemma iterate_eq_Φ {n : ℕ} {Ω Ξ : Type*} (G : E n → Ξ → E n) (γ : ℕ → ℝ) (x1 : E n)
    (ξ : ℕ → Ω → Ξ) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x) (k : ℕ) (hk : 1 ≤ k) (ω : Ω) :
    x k ω = Φ G γ x1 k (fun j => ξ j ω) := by
  induction k, hk using Nat.le_induction with
  | base =>
    rw [hx.1 ω]
    rfl
  | succ k hk ih =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hx.2 (k' + 1) hk ω, ih]
    rfl

/-- `Φ k` is measurable for the product σ-algebra on noise paths. -/
private lemma measurable_Φ {n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n)
    (hG : Measurable (Function.uncurry G)) (γ : ℕ → ℝ) (x1 : E n) :
    ∀ k : ℕ, Measurable (Φ G γ x1 k)
  | 0 => measurable_const
  | 1 => measurable_const
  | k + 2 => by
    have ih : Measurable (Φ G γ x1 (k + 1)) := measurable_Φ G hG γ x1 (k + 1)
    have hGk : Measurable (fun s : ℕ → Ξ => G (Φ G γ x1 (k + 1) s) (s (k + 1))) :=
      hG.comp (ih.prodMk (measurable_pi_apply (k + 1)))
    show Measurable (fun s : ℕ → Ξ =>
      Φ G γ x1 (k + 1) s - γ (k + 1) • G (Φ G γ x1 (k + 1) s) (s (k + 1)))
    exact ih.sub (hGk.const_smul (γ (k + 1)))

/-- The gradient map of an `L`-smooth function is `L`-Lipschitz. -/
private lemma lipschitz_grad {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) : LipschitzWith ⟨L, hf.1⟩ g :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    exact hf.2.2 x y

/-- Positivity of the weights `2γ_k − Lγ_k²` when `0 < γ_k < 2/L`. -/
private lemma weight_pos (L : ℝ) (hL : 0 < L) (γ : ℕ → ℝ) (N : ℕ)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L) (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
    0 < 2 * γ k - L * γ k ^ 2 := by
  have h1 : γ k * L < 2 := (lt_div_iff₀ hL).1 (hγ k hk).2
  have h2 : 2 * γ k - L * γ k ^ 2 = γ k * (2 - L * γ k) := by ring
  rw [h2]
  exact mul_pos (hγ k hk).1 (by linarith)

/-- The mass function (2.3) is nonnegative on `{1, …, N}`. -/
private lemma rsgPMF_nonneg (L : ℝ) (hL : 0 < L) (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ)
    (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L) (k : ℕ) (hk : k ∈ Finset.Icc 1 N) :
    0 ≤ rsgPMF L γ N k := by
  unfold rsgPMF
  apply div_nonneg (weight_pos L hL γ N hγ k hk).le
  apply le_of_lt
  apply Finset.sum_pos (fun j hj => weight_pos L hL γ N hγ j hj)
  exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩⟩

end GhadimiLan.RSG.Sol_weighting_identity

open GhadimiLan.RSG.Sol_weighting_identity

/-- The weighting identity in the proof of Theorem 2.1 (Ghadimi & Lan, arXiv:1309.5549v1, p. 7,
display after "Dividing both sides"): if the output index `R` has the mass function (2.3) on
`{1, …, N}` and is independent of the noise sequence `(ξ_k)`, and each `‖∇f(x_k)‖²`
(`k = 1, …, N`) is integrable, then `‖∇f(x_R)‖²` is integrable and
`E‖∇f(x_R)‖² = Σ_{k=1}^N (2γ_k − Lγ_k²) E‖∇f(x_k)‖² / Σ_{k=1}^N (2γ_k − Lγ_k²)`.

Proof: write `‖∇f(x_R)‖² = Σ_k 1_{R = k} ‖∇f(x_k)‖²`. Each `x_k` is a measurable function
`Φ k` of the noise path `(ξ_j)_j`, so `1_{R = k}` (a function of `R`) and `‖∇f(x_k)‖²` (a
function of the path) are independent; hence `E[1_{R = k} ‖∇f(x_k)‖²] = P(R = k) E‖∇f(x_k)‖²`
with `P(R = k) = P_R(k)`. Summing over `k` and pulling out the common denominator gives the
claim. -/
theorem solution {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    {Ξ : Type*} [MeasurableSpace Ξ] (G : E n → Ξ → E n) (hG : Measurable (Function.uncurry G))
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : ℕ → Ω → Ξ) (hξ : ∀ k, Measurable (ξ k))
    (N : ℕ) (hN : 1 ≤ N) (γ : ℕ → ℝ) (hγ : ∀ k ∈ Finset.Icc 1 N, 0 < γ k ∧ γ k < 2 / L)
    (x1 : E n) (x : ℕ → Ω → E n) (hx : IsRSGRun G γ x1 ξ x)
    (R : Ω → ℕ) (hR : IsRandomOutputIndex μ R L γ N)
    (hRind : IndepFun R (fun ω k => ξ k ω) μ)
    (hint : ∀ k ∈ Finset.Icc 1 N, Integrable (fun ω => ‖g (x k ω)‖ ^ 2) μ) :
    Integrable (fun ω => ‖g (x (R ω) ω)‖ ^ 2) μ ∧
    ∫ ω, ‖g (x (R ω) ω)‖ ^ 2 ∂μ =
      (∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ) /
        ∑ k ∈ Finset.Icc 1 N, (2 * γ k - L * γ k ^ 2) := by
  -- `∇f` is Lipschitz, hence continuous, hence Borel.
  have hgm : Measurable g := (lipschitz_grad f g L hf).continuous.measurable
  -- The noise path `ω ↦ (ξ_j(ω))_j` is measurable for the product σ-algebra.
  have hpath : Measurable (fun ω k => ξ k ω) := measurable_pi_lambda _ hξ
  -- Pointwise decomposition `‖∇f(x_R)‖² = Σ_{k=1}^N 1_{R = k} ‖∇f(x_k)‖²`.
  have hpt : ∀ ω, ‖g (x (R ω) ω)‖ ^ 2 =
      ∑ k ∈ Finset.Icc 1 N, (if R ω = k then (1 : ℝ) else 0) * ‖g (x k ω)‖ ^ 2 := by
    intro ω
    simp only [boole_mul]
    rw [Finset.sum_ite_eq, if_pos (hR.2.1 ω)]
  have heq : (fun ω => ‖g (x (R ω) ω)‖ ^ 2) =
      fun ω => ∑ k ∈ Finset.Icc 1 N, (if R ω = k then (1 : ℝ) else 0) * ‖g (x k ω)‖ ^ 2 :=
    funext hpt
  -- Each summand is integrable, with integral `P_R(k) · E‖∇f(x_k)‖²` (independence).
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      Integrable (fun ω => (if R ω = k then (1 : ℝ) else 0) * ‖g (x k ω)‖ ^ 2) μ ∧
      ∫ ω, (if R ω = k then (1 : ℝ) else 0) * ‖g (x k ω)‖ ^ 2 ∂μ =
        rsgPMF L γ N k * ∫ ω, ‖g (x k ω)‖ ^ 2 ∂μ := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.1 hk).1
    -- The indicator factor, as a function of `R`.
    set φ : ℕ → ℝ := fun r => if r = k then 1 else 0 with hφ
    have hφm : Measurable φ := Measurable.of_discrete
    have hφb : ∀ ω, ‖(φ ∘ R) ω‖ ≤ 1 := by
      intro ω
      simp only [Function.comp, hφ]
      split_ifs <;> simp
    -- The gradient factor, as a function of the noise path.
    set ψ : (ℕ → Ξ) → ℝ := fun s => ‖g (Φ G γ x1 k s)‖ ^ 2 with hψ
    have hψm : Measurable ψ := ((hgm.comp (measurable_Φ G hG γ x1 k)).norm).pow_const 2
    have hψx : ∀ ω, ψ (fun j => ξ j ω) = ‖g (x k ω)‖ ^ 2 := by
      intro ω
      simp only [hψ, iterate_eq_Φ G γ x1 ξ x hx k hk1 ω]
    -- Independence of the two factors, inherited from `R ⟂ (ξ_j)_j`.
    have hind : IndepFun (φ ∘ R) (ψ ∘ fun ω k => ξ k ω) μ := hRind.comp hφm hψm
    constructor
    · exact (hint k hk).bdd_mul (hφm.comp hR.1).aestronglyMeasurable
        (Filter.Eventually.of_forall hφb)
    · have h1 : ∫ ω, φ (R ω) * ψ (fun j => ξ j ω) ∂μ =
          (∫ ω, φ (R ω) ∂μ) * ∫ ω, ψ (fun j => ξ j ω) ∂μ :=
        hind.integral_fun_mul_eq_mul_integral (hφm.comp hR.1).aestronglyMeasurable
          (hψm.comp hpath).aestronglyMeasurable
      -- `E[1_{R = k}] = P(R = k) = P_R(k)`.
      have hφint : ∫ ω, φ (R ω) ∂μ = rsgPMF L γ N k := by
        have hset : MeasurableSet {ω | R ω = k} := hR.1 (measurableSet_singleton k)
        have heqφ : (fun ω => φ (R ω)) = {ω | R ω = k}.indicator 1 := by
          funext ω
          by_cases h : R ω = k
          · simp [hφ, h]
          · simp [hφ, h]
        rw [heqφ, integral_indicator_one hset, measureReal_def, hR.2.2 k hk,
          ENNReal.toReal_ofReal (rsgPMF_nonneg L hL N hN γ hγ k hk)]
      simp only [hψx] at h1
      rw [hφint] at h1
      exact h1
  constructor
  · rw [heq]
    exact integrable_finsetSum _ (fun k hk => (hterm k hk).1)
  · rw [heq, integral_finsetSum _ (fun k hk => (hterm k hk).1), Finset.sum_div]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [(hterm k hk).2]
    unfold rsgPMF
    rw [div_mul_eq_mul_div]
