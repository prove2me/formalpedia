-- Prove2me | solution 1 for GlynnSTS.NoAttain.display_4_27
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:23:02.571311+00:00
-- url     : https://prove2.me/submissions/844a5a1b-d666-4f7f-96c7-3c2d2ad2d3f5

import Mathlib
import Definitions.Def_GlynnSTS_NoAttain_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnNAAux

/-- hat function centered at `k`. -/
noncomputable def hat (k : ℕ) (u : ℝ) : ℝ := max 0 (1 - |u - k|)

lemma hat_nonneg (k : ℕ) (u : ℝ) : 0 ≤ hat k u := le_max_left _ _

lemma hat_pos_imp (k : ℕ) (u : ℝ) (h : hat k u ≠ 0) : |u - k| < 1 := by
  unfold hat at h
  by_contra h'
  push_neg at h'
  apply h
  exact max_eq_left (by linarith)

lemma continuous_hat (k : ℕ) : Continuous (hat k) := by
  unfold hat; fun_prop

/-- the node index of `u ∈ [0,n]`. -/
noncomputable def jdx (n : ℕ) (u : ℝ) : ℕ := min ⌊u⌋₊ (n - 1)

lemma jdx_le (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu0 : 0 ≤ u) (hun : u ≤ n) :
    (jdx n u : ℝ) ≤ u ∧ u ≤ (jdx n u : ℝ) + 1 ∧ jdx n u + 1 ≤ n := by
  unfold jdx
  refine ⟨?_, ?_, ?_⟩
  · calc ((min ⌊u⌋₊ (n-1) : ℕ) : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      _ ≤ u := Nat.floor_le hu0
  · rcases le_total ⌊u⌋₊ (n-1) with h | h
    · rw [min_eq_left h]; exact (Nat.lt_floor_add_one u).le
    · rw [min_eq_right h]
      have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub hn]; simp
      rw [this]; linarith
  · omega

lemma hat_sum (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu0 : 0 ≤ u) (hun : u ≤ n) (F : ℕ → ℝ) :
    ∑ k ∈ Finset.range (n + 1), hat k u * F k =
      ((jdx n u : ℝ) + 1 - u) * F (jdx n u) + (u - jdx n u) * F (jdx n u + 1) := by
  obtain ⟨h1, h2, h3⟩ := jdx_le n hn u hu0 hun
  set j := jdx n u with hj
  rw [Finset.sum_eq_add_of_mem j (j+1) (by simp; omega) (by simp; omega) (by omega)]
  · congr 1
    · congr 1
      unfold hat
      rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
      ring
    · congr 1
      unfold hat
      push_cast
      rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
      ring
  · intro c _ hc
    have : hat c u = 0 := by
      unfold hat
      apply max_eq_left
      rcases lt_or_gt_of_ne hc.1 with h | h
      · have : (c : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (j : ℝ) + 2 ≤ c := by
          have : j + 2 ≤ c := by omega
          exact_mod_cast this
        rw [abs_of_nonpos (by linarith)]; linarith
    rw [this, zero_mul]

lemma hat_sum_one (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu0 : 0 ≤ u) (hun : u ≤ n) :
    ∑ k ∈ Finset.range (n + 1), hat k u = 1 := by
  have := hat_sum n hn u hu0 hun (fun _ => 1)
  simp only [mul_one] at this
  rw [this]; ring


section BM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

noncomputable def node (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / n

def toNN (s : unitInterval) : ℝ≥0 := ⟨s, s.2.1⟩

noncomputable def Rp (n : ℕ) (W : ℝ≥0 → Ω → ℝ) (s : unitInterval) (ω : Ω) : ℝ :=
  W (toNN s) ω - ∑ k ∈ Finset.range (n + 1), hat k (n * s) * W (node n k) ω

lemma Rp_two (n : ℕ) (hn : 1 ≤ n) (s : unitInterval) (ω : Ω) :
    Rp n W s ω = W (toNN s) ω -
      (((jdx n (n * s) : ℝ) + 1 - n * s) * W (node n (jdx n (n * s))) ω
        + (n * s - jdx n (n * s)) * W (node n (jdx n (n * s) + 1)) ω) := by
  unfold Rp
  rw [hat_sum n hn _ (by have := s.2.1; positivity)
    (by have := s.2.2; have : (0:ℝ) ≤ n := by positivity
        nlinarith)]

lemma isGaussian_joint (hW : IsBrownianReal W P) (n : ℕ) (hn : 1 ≤ n) :
    IsGaussianProcess (Sum.elim (fun k => W (node n k)) (fun s => Rp n W s)) P := by
  apply hW.isGaussianProcess.of_isGaussianProcess
  rintro (k | s)
  · exact ⟨{node n k},
      { toFun x := x ⟨node n k, by simp⟩
        map_add' x y := by simp
        map_smul' c x := by simp }, by simp⟩
  · refine ⟨{toNN s, node n (jdx n (n * s)), node n (jdx n (n * s) + 1)},
      { toFun x := x ⟨toNN s, by simp⟩ -
          (((jdx n (n * s) : ℝ) + 1 - n * s) * x ⟨node n (jdx n (n * s)), by simp⟩
            + (n * s - jdx n (n * s)) * x ⟨node n (jdx n (n * s) + 1), by simp⟩)
        map_add' x y := by simp; ring
        map_smul' c x := by simp; ring }, ?_⟩
    intro ω
    simp only [Sum.elim_inr]
    rw [Rp_two n hn]
    simp


lemma node_coe (n k : ℕ) : ((node n k : ℝ≥0) : ℝ) = (k : ℝ) / n := by
  simp [node]

lemma toNN_coe (s : unitInterval) : ((toNN s : ℝ≥0) : ℝ) = s := rfl

lemma cov_Rp (hW : IsBrownianReal W P) (n : ℕ) (hn : 1 ≤ n) (s : unitInterval) (m : ℕ) :
    cov[Rp n W s, W (node n m); P] = 0 := by
  have hP : IsProbabilityMeasure P := hW.isGaussianProcess.isProbabilityMeasure
  have hL : ∀ t, MemLp (W t) 2 P := fun t => (hW.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  set j := jdx n (n * s)
  set a : ℝ := (j : ℝ) + 1 - n * s
  set b : ℝ := n * s - j
  have hfun : Rp n W s = W (toNN s) - ((fun ω => a * W (node n j) ω) +
      (fun ω => b * W (node n (j+1)) ω)) := by
    funext ω; rw [Rp_two n hn]; rfl
  rw [hfun, covariance_sub_left (hL _) ((hL _).const_mul a |>.add ((hL _).const_mul b)) (hL _),
    covariance_add_left ((hL _).const_mul a) ((hL _).const_mul b) (hL _),
    covariance_const_mul_left, covariance_const_mul_left,
    hW.covariance_eval, hW.covariance_eval, hW.covariance_eval]
  simp only [NNReal.coe_min, node_coe, toNN_coe]
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  obtain ⟨h1, h2, h3⟩ := jdx_le n hn (n * s) (by positivity) (by nlinarith)
  have hjs : (j : ℝ) / n ≤ s := by rw [div_le_iff₀ hnpos]; linarith
  have hjs' : s ≤ ((j + 1 : ℕ) : ℝ) / n := by rw [le_div_iff₀ hnpos]; push_cast; linarith
  rcases le_or_gt m j with hm | hm
  · have hm' : (m : ℝ) / n ≤ (j : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le; exact_mod_cast hm
    have hm'' : (m : ℝ) / n ≤ ((j + 1 : ℕ) : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le; push_cast; exact_mod_cast (by omega : m ≤ j + 1)
    rw [min_eq_right (hm'.trans hjs), min_eq_right hm', min_eq_right hm'']
    simp only [a, b]; ring
  · have hm' : ((j + 1 : ℕ) : ℝ) / n ≤ (m : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le; exact_mod_cast hm
    have hm'' : (j : ℝ) / n ≤ (m : ℝ) / n := by
      apply div_le_div_of_nonneg_right _ hnpos.le; exact_mod_cast hm.le
    rw [min_eq_left (hjs'.trans hm'), min_eq_left hm'', min_eq_left hm']
    simp only [a, b]; push_cast; field_simp; ring

lemma indep_nodes_Rp (hW : IsBrownianReal W P) (n : ℕ) (hn : 1 ≤ n) :
    IndepFun (fun ω k => W (node n k) ω) (fun ω s => Rp n W s ω) P := by
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero (isGaussian_joint hW n hn)
  · intro k; exact hW.aemeasurable _
  · intro s
    rw [show Rp n W s = fun ω => W (toNN s) ω -
      ∑ k ∈ Finset.range (n + 1), hat k (n * s) * W (node n k) ω from rfl]
    refine (hW.aemeasurable _).sub ?_
    refine Finset.aemeasurable_fun_sum _ (fun k _ => ?_)
    exact (hW.aemeasurable _).const_mul _
  · intro k s
    rw [covariance_comm]; exact cov_Rp hW n hn s k


lemma node_mono (n : ℕ) : Monotone (node n) := by
  intro a b h; unfold node; gcongr

lemma incr_pos (hW : IsBrownianReal W P) (n : ℕ) (hn : 1 ≤ n) (i : ℕ) (c r : ℝ) (hr : 0 < r) :
    0 < P {ω | |W (node n (i+1)) ω - W (node n i) ω - c| < r} := by
  have hlaw := hW.hasLaw_sub (node n (i+1)) (node n i)
  have hmeas : MeasurableSet {x : ℝ | |x - c| < r} :=
    measurableSet_lt (by fun_prop) measurable_const
  have := hlaw.measure_eq (p := fun x => |x - c| < r) hmeas
  simp only [Pi.sub_apply] at this
  rw [this]
  have hv : nndist ((node n (i+1) : ℝ≥0) : ℝ) (node n i) ≠ 0 := by
    rw [ne_eq, nndist_eq_zero, node_coe, node_coe]
    have hnpos : (0:ℝ) < n := by exact_mod_cast hn
    intro h
    field_simp at h
    push_cast at h
    linarith
  apply pos_iff_ne_zero.mpr
  intro h0
  have h1 := gaussianReal_absolutelyContinuous' 0 hv h0
  have h2 : {x : ℝ | |x - c| < r} = Metric.ball c r := by
    ext x; simp [Real.dist_eq]
  rw [h2, Real.volume_ball] at h1
  have : (0:ℝ) < 2 * r := by linarith
  simp [ENNReal.ofReal_eq_zero] at h1
  linarith

lemma nodes_pos (hW : IsBrownianReal W P) (n : ℕ) (hn : 1 ≤ n) (y : ℕ → ℝ) (hy0 : y 0 = 0)
    (r : ℝ) (hr : 0 < r) :
    0 < P {ω | ∀ k ≤ n, |W (node n k) ω - y k| < r} := by
  have hP : IsProbabilityMeasure P := hW.isGaussianProcess.isProbabilityMeasure
  set ρ : ℝ := r / (2 * n)
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hρ : 0 < ρ := by positivity
  let Δ : ℕ → Ω → ℝ := fun i ω => W (node n (i+1)) ω - W (node n i) ω
  have hind : iIndepFun Δ P := hW.hasIndepIncrements.nat (node_mono n)
  let S : ℕ → Set ℝ := fun i => {x | |x - (y (i+1) - y i)| < ρ}
  have hS : ∀ i, MeasurableSet (S i) := fun i => measurableSet_lt (by fun_prop) measurable_const
  have hprod := hind.measure_inter_preimage_eq_mul (Finset.range n) (sets := S) (fun i _ => hS i)
  have hpos : 0 < P (⋂ i ∈ Finset.range n, Δ i ⁻¹' S i) := by
    rw [hprod]
    exact pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => (incr_pos hW n hn i _ ρ hρ).ne')
  have h0 : ∀ᵐ ω ∂P, W 0 ω = 0 := hW.eval_zero_ae_eq_zero
  have hsub : (⋂ i ∈ Finset.range n, Δ i ⁻¹' S i) ≤ᵐ[P]
      {ω | ∀ k ≤ n, |W (node n k) ω - y k| < r} := by
    filter_upwards [h0] with ω hω hmem
    have key : ∀ k ≤ n, |W (node n k) ω - y k| ≤ k * ρ := by
      intro k
      induction k with
      | zero =>
        intro _
        simp [node, hω, hy0]
      | succ k ih =>
        intro hk
        have h1 := ih (by omega)
        have h2 : |W (node n (k+1)) ω - W (node n k) ω - (y (k+1) - y k)| < ρ :=
          Set.mem_iInter₂.mp hmem k (Finset.mem_range.2 (by omega))
        have : W (node n (k+1)) ω - y (k+1) =
          (W (node n k) ω - y k) + (W (node n (k+1)) ω - W (node n k) ω - (y (k+1) - y k)) := by
          ring
        rw [this]
        calc _ ≤ |W (node n k) ω - y k| +
              |W (node n (k+1)) ω - W (node n k) ω - (y (k+1) - y k)| := abs_add_le _ _
          _ ≤ k * ρ + ρ := by linarith
          _ = ((k+1 : ℕ) : ℝ) * ρ := by push_cast; ring
    intro k hk
    have := key k hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    have : (k : ℝ) * ρ ≤ r / 2 := by
      calc (k : ℝ) * ρ ≤ n * ρ := by gcongr
        _ = r / 2 := by simp only [ρ]; field_simp
    show |W (node n k) ω - y k| < r
    linarith
  exact lt_of_lt_of_le hpos (measure_mono_ae hsub)

end BM


lemma hat_avg_bound (N : ℕ) (hN : 1 ≤ N) (s : unitInterval) (F : ℕ → ℝ) (G c : ℝ)
    (h : ∀ k ≤ N, hat k (N * s) ≠ 0 → |G - F k| ≤ c) :
    |G - ∑ k ∈ Finset.range (N + 1), hat k (N * s) * F k| ≤ c := by
  have hs0 := s.2.1
  have hs1 := s.2.2
  have hNpos : (0:ℝ) ≤ N := by positivity
  have h1 := hat_sum_one N hN (N * s) (by positivity) (by nlinarith)
  have : G - ∑ k ∈ Finset.range (N + 1), hat k (N * s) * F k =
      ∑ k ∈ Finset.range (N + 1), hat k (N * s) * (G - F k) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, h1, one_mul]
  rw [this]
  calc _ ≤ ∑ k ∈ Finset.range (N + 1), |hat k (N * s) * (G - F k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), hat k (N * s) * c := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul, abs_of_nonneg (hat_nonneg _ _)]
      by_cases h0 : hat k (N * s) = 0
      · rw [h0]; simp
      · exact mul_le_mul_of_nonneg_left (h k (by simp at hk; omega) h0) (hat_nonneg _ _)
    _ = c := by rw [← Finset.sum_mul, h1, one_mul]

lemma dist_of_hat (N : ℕ) (hN : 1 ≤ N) (s : unitInterval) (k : ℕ) (hk : k ≤ N)
    (h : hat k (N * s) ≠ 0) :
    dist s (Set.projIcc 0 1 zero_le_one ((k : ℝ) / N)) < 1 / N := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hmem : (k : ℝ) / N ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hNpos]; exact_mod_cast hk
  rw [Set.projIcc_of_mem _ hmem, Subtype.dist_eq, Real.dist_eq]
  have h1 := hat_pos_imp k _ h
  have : (s : ℝ) - k / N = (N * s - k) / N := by field_simp
  rw [this, abs_div, abs_of_pos hNpos]
  exact div_lt_div_of_pos_right h1 hNpos

lemma node_eq (N : ℕ) (hN : 1 ≤ N) (k : ℕ) (hk : k ≤ N) :
    toNN (Set.projIcc 0 1 zero_le_one ((k : ℝ) / N)) = node N k := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hmem : (k : ℝ) / N ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_one hNpos]; exact_mod_cast hk
  apply NNReal.eq
  rw [toNN_coe, node_coe, Set.projIcc_of_mem _ hmem]

end GlynnNAAux

open GlynnNAAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (σ : ℝ) (hσ : 0 < σ) :
    ∀ x ∈ GlynnSTS.NoAttain.C0, ∀ ε : ℝ, 0 < ε → 0 < P {ω | dist (σ • B ω) x < ε} := by
  intro x hx ε hε
  obtain ⟨_, W, hW, hBW⟩ := hB
  have hBW' : ∀ ω t, B ω t = W (toNN t) ω := hBW
  set y : C(unitInterval, ℝ) := σ⁻¹ • x with hy
  set c : ℝ := ε / σ / 4 with hc
  have hcpos : 0 < c := by positivity
  -- uniform continuity of y
  obtain ⟨δy, hδy, hyuc⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous y.continuous) c hcpos
  -- oscillation events
  let A : ℕ → Set Ω := fun n => {ω | ∀ s s' : unitInterval, dist s s' < 1 / ((n:ℝ) + 1) →
    |B ω s - B ω s'| ≤ c}
  have hAmono : Monotone A := by
    intro n m hnm ω hω s s' hd
    apply hω s s'
    calc dist s s' < 1 / ((m:ℝ) + 1) := hd
      _ ≤ 1 / ((n:ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (n:ℝ) ≤ m := by exact_mod_cast hnm
        linarith
  have hAun : (⋃ n, A n) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    obtain ⟨δ, hδ, hδc⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous (B ω).continuous) c hcpos
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine Set.mem_iUnion.2 ⟨n, fun s s' hd => ?_⟩
    have := hδc (hd.trans hn)
    rw [Real.dist_eq] at this
    exact this.le
  have hAt := tendsto_measure_iUnion_atTop (μ := P) hAmono
  rw [hAun, measure_univ] at hAt
  have hev1 : ∀ᶠ n in atTop, 0 < P (A n) :=
    hAt.eventually (eventually_gt_nhds (by norm_num : (0:ℝ≥0∞) < 1))
  have hev2 : ∀ᶠ n : ℕ in atTop, 1 / ((n:ℝ) + 1) ≤ δy := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδy
    refine eventually_atTop.2 ⟨n, fun m hm => ?_⟩
    refine le_trans ?_ hn.le
    apply one_div_le_one_div_of_le (by positivity)
    have : (n:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  set N : ℕ := n + 1 with hNdef
  have hN : 1 ≤ N := by omega
  have hNcast : (N : ℝ) = (n : ℝ) + 1 := by simp [hNdef]
  -- events
  let yv : ℕ → ℝ := fun k => y (Set.projIcc 0 1 zero_le_one ((k : ℝ) / N))
  have hyv0 : yv 0 = 0 := by
    simp only [yv, Nat.cast_zero, zero_div]
    rw [Set.projIcc_left]
    simp only [hy, ContinuousMap.smul_apply, smul_eq_mul]
    have : x 0 = 0 := hx
    change σ⁻¹ * x 0 = 0
    rw [this, mul_zero]
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense unitInterval
  let S1 : Set (ℕ → ℝ) := {v | ∀ k ≤ N, |v k - yv k| < c}
  let S2 : Set (unitInterval → ℝ) := ⋂ q ∈ D, {f | |f q| ≤ c}
  have hS1 : MeasurableSet S1 := by
    have : S1 = ⋂ k, ⋂ (_ : k ≤ N), {v : ℕ → ℝ | |v k - yv k| < c} := by
      ext v; simp [S1]
    rw [this]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt (by fun_prop) measurable_const
  have hS2 : MeasurableSet S2 :=
    MeasurableSet.biInter hDc fun q _ => measurableSet_le (by fun_prop) measurable_const
  have hind := indep_nodes_Rp hW N hN
  have hprod := hind.measure_inter_preimage_eq_mul S1 S2 hS1 hS2
  have hE1 : 0 < P ((fun ω k => W (node N k) ω) ⁻¹' S1) :=
    nodes_pos hW N hN yv hyv0 c hcpos
  -- A n ⊆ E2
  have hRbound : ∀ ω ∈ A n, ∀ s, |Rp N W s ω| ≤ c := by
    intro ω hω s
    unfold Rp
    apply hat_avg_bound N hN s
    intro k hk hh
    rw [← node_eq N hN k hk, ← hBW', ← hBW']
    apply hω
    have := dist_of_hat N hN s k hk hh
    exact lt_of_lt_of_le this (le_of_eq (by rw [hNcast]))
  have hE2 : 0 < P ((fun ω s => Rp N W s ω) ⁻¹' S2) := by
    refine lt_of_lt_of_le hn1 (measure_mono ?_)
    intro ω hω
    simp only [Set.mem_preimage, S2, Set.mem_iInter]
    intro q _
    exact hRbound ω hω q
  have hpos : 0 < P ((fun ω k => W (node N k) ω) ⁻¹' S1 ∩ (fun ω s => Rp N W s ω) ⁻¹' S2) := by
    rw [hprod]
    exact ENNReal.mul_pos hE1.ne' hE2.ne'
  refine lt_of_lt_of_le hpos (measure_mono ?_)
  rintro ω ⟨h1, h2⟩
  simp only [Set.mem_preimage, S1, Set.mem_setOf_eq] at h1
  simp only [Set.mem_preimage, S2, Set.mem_iInter] at h2
  -- extend from D to all s by continuity
  have hRcont : Continuous fun s : unitInterval => Rp N W s ω := by
    have : (fun s : unitInterval => Rp N W s ω) = fun s => B ω s -
        ∑ k ∈ Finset.range (N + 1), hat k (N * s) * W (node N k) ω := by
      funext s; unfold Rp; rw [hBW']
    rw [this]
    have := continuous_hat
    fun_prop
  have hRall : ∀ s, |Rp N W s ω| ≤ c := by
    have hcl : IsClosed {s : unitInterval | |Rp N W s ω| ≤ c} :=
      isClosed_le (continuous_abs.comp hRcont) continuous_const
    have : D ⊆ {s : unitInterval | |Rp N W s ω| ≤ c} := fun q hq => h2 q hq
    have := hcl.closure_subset_iff.2 this
    rw [hDd.closure_eq] at this
    exact fun s => this (Set.mem_univ s)
  have hpt : ∀ s, |B ω s - y s| ≤ 3 * c := by
    intro s
    have e1 := hRall s
    have e2 : |(∑ k ∈ Finset.range (N + 1), hat k (N * s) * W (node N k) ω) -
        ∑ k ∈ Finset.range (N + 1), hat k (N * s) * yv k| ≤ c := by
      rw [← Finset.sum_sub_distrib]
      simp_rw [← mul_sub]
      have := hat_avg_bound N hN s (fun k => W (node N k) ω - yv k) 0 c (by
        intro k hk _
        rw [zero_sub, abs_neg]
        exact (h1 k hk).le)
      rwa [zero_sub, abs_neg] at this
    have e3 : |y s - ∑ k ∈ Finset.range (N + 1), hat k (N * s) * yv k| ≤ c := by
      apply hat_avg_bound N hN s
      intro k hk hh
      have hd := dist_of_hat N hN s k hk hh
      have : dist s (Set.projIcc 0 1 zero_le_one ((k : ℝ) / N)) < δy := by
        exact lt_of_lt_of_le hd (by rw [hNcast]; exact hn2)
      have := hyuc this
      rw [Real.dist_eq] at this
      exact this.le
    unfold Rp at e1
    rw [← hBW'] at e1
    have : B ω s - y s = (B ω s - ∑ k ∈ Finset.range (N + 1), hat k (N * s) * W (node N k) ω)
      + ((∑ k ∈ Finset.range (N + 1), hat k (N * s) * W (node N k) ω) -
        ∑ k ∈ Finset.range (N + 1), hat k (N * s) * yv k)
      - (y s - ∑ k ∈ Finset.range (N + 1), hat k (N * s) * yv k) := by ring
    rw [this]
    calc _ ≤ |B ω s - ∑ k ∈ Finset.range (N + 1), hat k (N * s) * W (node N k) ω|
        + |(∑ k ∈ Finset.range (N + 1), hat k (N * s) * W (node N k) ω) -
          ∑ k ∈ Finset.range (N + 1), hat k (N * s) * yv k|
        + |y s - ∑ k ∈ Finset.range (N + 1), hat k (N * s) * yv k| := by
          refine (abs_sub _ _).trans ?_
          gcongr
          exact abs_add_le _ _
      _ ≤ 3 * c := by linarith
  show dist (σ • B ω) x < ε
  have hdl : dist (σ • B ω) x ≤ 3 * ε / 4 := by
    rw [ContinuousMap.dist_le (by positivity)]
    intro s
    rw [Real.dist_eq]
    have hxs : x s = σ * y s := by
      simp only [hy, ContinuousMap.smul_apply, smul_eq_mul]; field_simp
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [hxs, ← mul_sub, abs_mul, abs_of_pos hσ]
    have := hpt s
    calc σ * |B ω s - y s| ≤ σ * (3 * c) := by gcongr
      _ = 3 * ε / 4 := by simp only [hc]; field_simp
  linarith
