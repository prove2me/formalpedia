-- Prove2me | solution 3 for MasulloGRH.scalar_expansion_of_weak_expansion
-- status  : ACCEPTED   (prove)
-- author  : @ghseeli
-- created : 2026-11-21T00:41:12.772708+00:00
-- url     : https://prove2.me/submissions/150b63ae-5597-4b4b-b960-a4a7d10f4893

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Topology Filter
universe u

/- The null-weight, bounded-seminorm and completeness-series arguments below are
adapted from marozols' accepted public proof 9a239bb5-5719-4b20-a005-ebb00cb463bc.
This file isolates their weaker weak-expansion consequence, without nuclearity. -/
namespace WeakExpansionHelpers
noncomputable def sc {X : Type*} [AddCommGroup X] [Module ℂ X] (c : ℝ) (hc : 0 ≤ c)
    (p : Seminorm ℂ X) : Seminorm ℂ X :=
  let c' : NNReal := ⟨c, hc⟩
  c' • p

theorem sc_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (c : ℝ) (hc : 0 ≤ c)
    (p : Seminorm ℂ X) (x : X) : sc c hc p x = c * p x := rfl

theorem exists_seminorm_ball_subset {X : Type u} [AddCommGroup X] [Module ℂ X]
    [t : TopologicalSpace X] (h : IsLocallyConvexTopology X t) {U : Set X}
    (hU : U ∈ 𝓝 (0 : X)) :
    ∃ p : Seminorm ℂ X, Continuous p ∧ ∀ x, p x < 1 → x ∈ U := by
  obtain ⟨ι, _, P, hP⟩ := h
  have hadd : IsTopologicalAddGroup X := hP.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ X := hP.continuousSMul
  obtain ⟨⟨s, ρ⟩, hρ, hsub⟩ := hP.hasBasis_zero_ball.mem_iff.1 hU
  have hρ : 0 < ρ := hρ
  obtain ⟨p0, hp0⟩ : ∃ p : Seminorm ℂ X, p = s.sup P := ⟨_, rfl⟩
  have hsub : p0.ball 0 ρ ⊆ U := by rw [hp0]; exact hsub
  have hsc : Continuous p0 := by
    rw [hp0]
    exact Seminorm.continuous (r := ρ) (hP.hasBasis_zero_ball.mem_of_mem (i := (s, ρ)) hρ)
  refine ⟨sc ρ⁻¹ (inv_pos.2 hρ).le p0, ?_, ?_⟩
  · have : (fun x => sc ρ⁻¹ (inv_pos.2 hρ).le p0 x) = fun x => ρ⁻¹ * p0 x :=
      funext fun x => sc_apply _ _ _ _
    change Continuous (fun x => sc ρ⁻¹ (inv_pos.2 hρ).le p0 x)
    rw [this]
    exact continuous_const.mul hsc
  · intro x hx
    apply hsub
    rw [Seminorm.mem_ball_zero]
    rw [sc_apply, inv_mul_lt_iff₀ hρ] at hx
    simpa using hx

/-- A continuous seminorm is bounded on a von Neumann bounded set. -/
theorem seminorm_bdd_of_bounded {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    (q : Seminorm ℂ X) (hqc : Continuous q) (B : Set X) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ B, q x ≤ M := by
  have hq1 : {x : X | q x < 1} ∈ 𝓝 (0 : X) :=
    (isOpen_lt hqc continuous_const).mem_nhds (by simp)
  obtain ⟨ρ, hρ⟩ := absorbs_iff_norm.1 (hB hq1)
  refine ⟨max ρ 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x hx => ?_⟩
  have hnorm : ‖((max ρ 1 : ℝ) : ℂ)‖ = max ρ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_trans zero_le_one (le_max_right _ _))]
  obtain ⟨y, hy, rfl⟩ := hρ ((max ρ 1 : ℝ) : ℂ) (by rw [hnorm]; exact le_max_left _ _) hx
  have hy' : q y < 1 := hy
  change q (((max ρ 1 : ℝ) : ℂ) • y) ≤ max ρ 1
  rw [map_smul_eq_mul, hnorm]
  nlinarith [le_max_right ρ 1, apply_nonneg q y]

theorem exists_dual_ne_zero {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) {x : E} (hx : x ≠ 0) : ∃ f : StrongDual ℂ E, f x ≠ 0 := by
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := hE
  have : IsTopologicalAddGroup E := hp.topologicalAddGroup
  have : ContinuousSMul ℂ E := hp.continuousSMul
  have : PolynormableSpace ℂ E := hp.toPolynormableSpace
  let S : Submodule ℂ E := ℂ ∙ x
  obtain ⟨g, hg⟩ := Submodule.ClosedComplemented.of_finiteDimensional S
  have hxS : x ∈ S := Submodule.mem_span_singleton_self x
  have hne : (⟨x, hxS⟩ : S) ≠ 0 := by
    intro h
    apply hx
    simpa using congrArg Subtype.val h
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ S, φ ⟨x, hxS⟩ ≠ 0 := by
    by_contra! h
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 h)
  let φc : S →L[ℂ] ℂ := LinearMap.toContinuousLinearMap φ
  refine ⟨φc.comp g, ?_⟩
  have hgx : g x = ⟨x, hxS⟩ := hg ⟨x, hxS⟩
  simpa [φc, hgx] using hφ

theorem eq_of_forall_dual_eq {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (x y : E) (h : ∀ f : StrongDual ℂ E, f x = f y) : x = y := by
  by_contra hxy
  obtain ⟨f, hf⟩ := exists_dual_ne_zero hE (sub_ne_zero.2 hxy)
  apply hf
  rw [map_sub, h f, sub_self]

/-- For a nonnegative summable sequence `c` there are weights `ε n > 0`, `ε n → 0`, with
`∑ c n / ε n < ∞`. -/
theorem exists_null_weights (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcs : Summable c) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ Tendsto ε atTop (𝓝 0) ∧ Summable (fun n => c n / ε n) := by
  let r : ℕ → ℝ := fun n => ∑' k, c (k + n)
  have hsh : ∀ n, Summable fun k => c (k + n) := fun n => (summable_nat_add_iff n).2 hcs
  have hr0 : ∀ n, 0 ≤ r n := fun n => tsum_nonneg fun k => hc0 _
  have hrec : ∀ n, r n = c n + r (n + 1) := by
    intro n
    have h1 := (hsh n).tsum_eq_zero_add
    change r n = c n + r (n + 1)
    change (∑' k, c (k + n)) = c n + ∑' k, c (k + (n + 1))
    rw [h1, zero_add]
    congr 1
    exact tsum_congr fun k => by rw [add_assoc, add_comm 1 n]
  have hrt : Tendsto r atTop (𝓝 0) := tendsto_sum_nat_add c
  refine ⟨fun n => Real.sqrt (r n) + (1 / 2) ^ n, fun n => by positivity, ?_, ?_⟩
  · have h1 : Tendsto (fun n => Real.sqrt (r n)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hrt
      simpa [Function.comp_def] using h
    have h2 : Tendsto (fun n : ℕ => ((1 : ℝ) / 2) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using h1.add h2
  · have hterm : ∀ n, c n / (Real.sqrt (r n) + (1 / 2) ^ n) ≤
        2 * (Real.sqrt (r n) - Real.sqrt (r (n + 1))) := by
      intro n
      have hp : (0 : ℝ) < (1 / 2) ^ n := by positivity
      obtain ⟨A, hA⟩ : ∃ A, A = Real.sqrt (r n) := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B, B = Real.sqrt (r (n + 1)) := ⟨_, rfl⟩
      have hA0 : 0 ≤ A := hA ▸ Real.sqrt_nonneg _
      have hB0 : 0 ≤ B := hB ▸ Real.sqrt_nonneg _
      have e1 : A * A = r n := by rw [hA]; exact Real.mul_self_sqrt (hr0 n)
      have e2 : B * B = r (n + 1) := by rw [hB]; exact Real.mul_self_sqrt (hr0 (n + 1))
      have hle : B ≤ A := by
        rw [hA, hB]
        exact Real.sqrt_le_sqrt (by rw [hrec n]; linarith [hc0 n])
      have hc : c n = A * A - B * B := by rw [e1, e2, hrec n]; ring
      rw [← hA, ← hB, div_le_iff₀ (by positivity), hc]
      nlinarith [mul_nonneg (sub_nonneg.2 hle) (by linarith : (0 : ℝ) ≤ A - B + 2 * (1 / 2) ^ n)]
    refine summable_of_sum_range_le (c := 2 * Real.sqrt (r 0))
      (fun n => div_nonneg (hc0 n) (by positivity)) fun N => ?_
    have h1 : ∑ i ∈ Finset.range N, c i / (Real.sqrt (r i) + (1 / 2) ^ i) ≤
        2 * (Real.sqrt (r 0) - Real.sqrt (r N)) := by
      induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ]
        have := hterm N
        linarith
    linarith [Real.sqrt_nonneg (r N)]


end WeakExpansionHelpers

open WeakExpansionHelpers in
theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hC : IsCompleteTVS G) (hL : IsHLCS G)
    (B : Set G) (w : ℕ → G) (Y : ℕ → StrongDual ℂ G) (c : ℕ → ℝ)
    (hw : Bornology.IsVonNBounded ℂ (Set.range w)) (hc0 : ∀ n, 0 ≤ c n) (hc : Summable c)
    (hY : ∀ n, ∀ x ∈ B, ‖Y n x‖ ≤ 1)
    (hrep : ∀ (f : StrongDual ℂ G), ∀ x ∈ B,
      HasSum (fun n => (c n : ℂ) * Y n x * f (w n)) (f x)) :
    ∃ (y : ℕ → G) (c : ℕ → ℝ) (a : ℕ → (Submodule.span ℂ B) →ₗ[ℂ] ℂ),
      Filter.Tendsto y Filter.atTop (nhds (0 : G)) ∧
      (∀ n, 0 ≤ c n) ∧ Summable c ∧
      (∀ n (x : Submodule.span ℂ B), (x : G) ∈ B → ‖a n x‖ ≤ c n) ∧
      ∀ x : Submodule.span ℂ B, HasSum (fun n => a n x • y n) (x : G) := by
  classical
  obtain ⟨⟨ι, hι, Pf, hPf⟩, hT2⟩ := hL
  have hadd : IsTopologicalAddGroup G := hPf.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ G := hPf.continuousSMul
  -- completeness of `G` as a uniform space
  obtain ⟨-, hcomp⟩ := hC
  let _ : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace G := by
    refine ⟨fun {f} hf => hcomp f ⟨hf.1, fun U hU => ?_⟩⟩
    have hmem : {p : G × G | p.2 - p.1 ∈ U} ∈ uniformity G := by
      rw [uniformity_eq_comap_nhds_zero G]
      exact preimage_mem_comap hU
    obtain ⟨t, ht, hts⟩ := mem_prod_same_iff.1 (hf.2 hmem)
    exact ⟨t, ht, fun x hx y hy => hts (Set.mk_mem_prod hy hx)⟩
  have hexp : ∀ x ∈ B, HasSum (fun n => ((c n : ℂ) * Y n x) • w n) x := by
    intro x hx
    -- summability in the complete space `G`
    have hsummT : Summable fun n => ((c n : ℂ) * Y n x) • w n := by
      rw [summable_iff_vanishing]
      intro e he
      obtain ⟨p, hpc, hp⟩ := exists_seminorm_ball_subset ⟨ι, hι, Pf, hPf⟩ he
      obtain ⟨M, hM0, hM⟩ := seminorm_bdd_of_bounded p hpc (Set.range w) hw
      obtain ⟨s, hs⟩ := hc.vanishing (Metric.ball_mem_nhds (0 : ℝ) (inv_pos.2 hM0))
      refine ⟨s, fun t ht => hp _ ?_⟩
      have h1 := hs t ht
      rw [mem_ball_zero_iff, Real.norm_of_nonneg (Finset.sum_nonneg fun n _ => hc0 n)] at h1
      calc p (∑ n ∈ t, ((c n : ℂ) * Y n x) • w n)
          ≤ ∑ n ∈ t, p (((c n : ℂ) * Y n x) • w n) :=
            Finset.le_sum_of_subadditive p (map_zero p).le (map_add_le_add p) _ _
        _ ≤ ∑ n ∈ t, c n * M := by
            refine Finset.sum_le_sum fun n _ => ?_
            rw [map_smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hc0 n)]
            have h2 := hY n x hx
            have h3 := hM (w n) (Set.mem_range_self n)
            have h4 := apply_nonneg p (w n)
            calc c n * ‖Y n x‖ * p (w n) ≤ c n * 1 * M := by
                  apply mul_le_mul (mul_le_mul_of_nonneg_left h2 (hc0 n)) h3 h4
                  exact mul_nonneg (hc0 n) zero_le_one
              _ = c n * M := by ring
        _ = (∑ n ∈ t, c n) * M := by rw [Finset.sum_mul]
        _ < 1 := by
            rw [← lt_div_iff₀ hM0, one_div]
            exact h1
    have hval : ∑' n, ((c n : ℂ) * Y n x) • w n = x := by
      apply eq_of_forall_dual_eq ⟨⟨ι, hι, Pf, hPf⟩, hT2⟩
      intro f
      have h1 := f.hasSum hsummT.hasSum
      have h2 : HasSum (fun n => f (((c n : ℂ) * Y n x) • w n)) (f x) := by
        simpa only [map_smul, smul_eq_mul] using hrep f x hx
      exact h1.unique h2
    simpa only [hval] using hsummT.hasSum
  -- extension to the span of `B` by linearity
  have hspan : ∀ x : G, x ∈ Submodule.span ℂ B →
      HasSum (fun n => ((c n : ℂ) * Y n x) • w n) x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hexp x hx
    | zero => simpa using (hasSum_zero : HasSum (fun _ : ℕ => (0 : G)) 0)
    | add x y _ _ hx hy =>
      have h1 := hx.add hy
      have e : (fun n => ((c n : ℂ) * Y n (x + y)) • w n) =
          fun n => ((c n : ℂ) * Y n x) • w n + ((c n : ℂ) * Y n y) • w n := by
        funext n
        rw [map_add, mul_add, add_smul]
      rw [e]
      exact h1
    | smul k x _ hx =>
      have h1 := hx.const_smul k
      have e : (fun n => ((c n : ℂ) * Y n (k • x)) • w n) =
          fun n => k • ((c n : ℂ) * Y n x) • w n := by
        funext n
        rw [map_smul, smul_eq_mul, smul_smul]
        congr 1
        ring
      rw [e]
      exact h1
  -- rescaling to a null sequence
  obtain ⟨ε, hε0, hεt, hεs⟩ := exists_null_weights c hc0 hc
  refine ⟨fun n => (ε n : ℂ) • w n, fun n => c n / ε n,
    fun n => (((c n / ε n : ℝ) : ℂ)) • ((Y n : G →ₗ[ℂ] ℂ).comp (Submodule.span ℂ B).subtype),
    ?_, fun n => div_nonneg (hc0 n) (hε0 n).le, hεs, ?_, ?_⟩
  · have hεc : Tendsto (fun n => (ε n : ℂ)) atTop (𝓝 0) := by
      have := (Complex.continuous_ofReal.tendsto 0).comp hεt
      simpa [Function.comp_def] using this
    exact hw.smul_tendsto_zero (Filter.Eventually.of_forall (fun n => Set.mem_range_self n)) hεc
  · intro n x hx
    change ‖((c n / ε n : ℝ) : ℂ) * Y n (x : G)‖ ≤ c n / ε n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hc0 n) (hε0 n).le)]
    have := mul_le_mul_of_nonneg_left (hY n x hx) (div_nonneg (hc0 n) (hε0 n).le)
    rwa [mul_one] at this
  · intro x
    have h1 := hspan (x : G) x.2
    have e : (fun n => ((((c n / ε n : ℝ) : ℂ)) •
        ((Y n : G →ₗ[ℂ] ℂ).comp (Submodule.span ℂ B).subtype)) x • ((ε n : ℂ) • w n)) =
        fun n => ((c n : ℂ) * Y n (x : G)) • w n := by
      funext n
      change ((((c n / ε n : ℝ) : ℂ)) * Y n (x : G)) • ((ε n : ℂ) • w n) =
        ((c n : ℂ) * Y n (x : G)) • w n
      rw [smul_smul]
      congr 1
      have hne : (ε n : ℂ) ≠ 0 := by
        rw [Ne, Complex.ofReal_eq_zero]; exact (hε0 n).ne'
      push_cast
      field_simp
    rw [e]
    exact h1
