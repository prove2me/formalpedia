-- Prove2me | solution 1 for MasulloGRH.isCompactOperator_of_isNuclearMap
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:07:20.781656+00:00
-- url     : https://prove2.me/submissions/90d10a92-fb36-4916-9df9-8889d77439a2

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_MasulloGRH_NuclearMap

open Filter Topology
set_option autoImplicit false

namespace Sol_MasulloGRH_isCompactOperator_of_isNuclearMap

open scoped Pointwise

variable {F : Type*} [AddCommGroup F] [Module ℂ F]

/-- A complex-balanced set is real-balanced. -/
theorem balanced_real {B : Set F} (hBal : Balanced ℂ B) : Balanced ℝ B := by
  intro a ha x hx
  obtain ⟨b, hb, rfl⟩ := hx
  have : (a : ℂ) • b ∈ B := hBal.smul_mem (by simpa [Complex.norm_real] using ha) hb
  simpa [Complex.coe_smul] using this

/-- `a • b ∈ ‖a‖ • B` for `b ∈ B`, `B` balanced. -/
theorem smul_mem_norm_smul {B : Set F} (hBal : Balanced ℂ B) (a : ℂ) {b : F} (hb : b ∈ B) :
    a • b ∈ (‖a‖ : ℝ) • B := by
  have h1 : a • B ⊆ (‖a‖ : ℝ) • B := hBal.smul_mono (by simp)
  exact h1 (Set.smul_mem_smul_set hb)

/-- Finite sums `∑ aᵢ bᵢ` with `bᵢ ∈ B` lie in `(∑ ‖aᵢ‖) • B`. -/
theorem sum_smul_mem {ι : Type*} {B : Set F} (hBne : B.Nonempty) (hBal : Balanced ℂ B)
    (hconv : Convex ℝ B) (s : Finset ι) (a : ι → ℂ) (b : ι → F) (hb : ∀ i ∈ s, b i ∈ B) :
    ∑ i ∈ s, a i • b i ∈ (∑ i ∈ s, ‖a i‖) • B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [Set.zero_smul_set hBne]
    exact Set.zero_mem_zero
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      hconv.add_smul (norm_nonneg _) (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
    exact Set.add_mem_add (smul_mem_norm_smul hBal _ (hb k (Finset.mem_insert_self k s)))
      (ih (fun i hi => hb i (Finset.mem_insert_of_mem hi)))

/-- Every element of the span of a balanced convex non-empty set `B` is absorbed by `B`. -/
theorem exists_mem_smul_of_mem_span {B : Set F} (hBne : B.Nonempty) (hBal : Balanced ℂ B)
    (hconv : Convex ℝ B) {v : F} (hv : v ∈ Submodule.span ℂ B) :
    ∃ r : ℝ, 0 < r ∧ v ∈ r • B := by
  obtain ⟨f, t, ht, -, rfl⟩ := Submodule.mem_span_iff_exists_finset_subset.1 hv
  have h := sum_smul_mem hBne hBal hconv t f id (fun i hi => ht hi)
  refine ⟨∑ i ∈ t, ‖f i‖ + 1, by positivity, ?_⟩
  refine (balanced_real hBal).smul_mono ?_ h
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _)),
    Real.norm_of_nonneg (by positivity)]
  linarith

/-- A seminorm bounded by `C` on `B` is bounded by `r * C` on `r • B`. -/
theorem seminorm_le_of_mem_smul (q : Seminorm ℂ F) {B : Set F} {C : ℝ}
    (hC : ∀ x ∈ B, q x ≤ C) {r : ℝ} (hr : 0 ≤ r) {v : F} (hv : v ∈ r • B) : q v ≤ r * C := by
  obtain ⟨b, hb, rfl⟩ := hv
  show q (r • b) ≤ r * C
  rw [← Complex.coe_smul, map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left (hC b hb) hr

/-- On the span of `B`, a seminorm bounded by `C` on `B` is dominated by `gauge B * C`. -/
theorem seminorm_le_gauge_mul (q : Seminorm ℂ F) {B : Set F} (hBne : B.Nonempty)
    (hBal : Balanced ℂ B) (hconv : Convex ℝ B) {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ x ∈ B, q x ≤ C) {v : F} (hv : v ∈ Submodule.span ℂ B) :
    q v ≤ gauge B v * C := by
  have hne : {r : ℝ | 0 < r ∧ v ∈ r • B}.Nonempty := by
    obtain ⟨r, hr, hvr⟩ := exists_mem_smul_of_mem_span hBne hBal hconv hv
    exact ⟨r, hr, hvr⟩
  have key : q v / C ≤ gauge B v := by
    refine le_of_forall_gt_imp_ge_of_dense (fun a ha => ?_)
    obtain ⟨r, ⟨hr, hvr⟩, hra⟩ := exists_lt_of_csInf_lt hne ha
    rw [div_le_iff₀ hCpos]
    exact (seminorm_le_of_mem_smul q hC hr.le hvr).trans
      (mul_le_mul_of_nonneg_right hra.le hCpos.le)
  rwa [div_le_iff₀ hCpos] at key

end Sol_MasulloGRH_isCompactOperator_of_isNuclearMap

open MasulloGRH Sol_MasulloGRH_isCompactOperator_of_isNuclearMap

open scoped Pointwise in
theorem solution {E F : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hE : IsHLCS E) (hF : IsHLCS F) (T : E →L[ℂ] F) (hT : IsNuclearMap T) :
    IsCompactOperator T := by
  obtain ⟨c, φ, y, hc, hφ, ⟨B, hB, hyB⟩, hsum⟩ := hT
  obtain ⟨⟨ι, hι, p, hp⟩, hT2⟩ := hF
  obtain ⟨hBne, hBbdd, hBal, hBconv, -, hBcomplete⟩ := hB
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  -- seminorm bounds on `B`
  have hCB : ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ x ∈ B, p i x ≤ C := by
    intro i
    obtain ⟨r, hr, h⟩ := (hp.isVonNBounded_iff_seminorm_bounded).1 hBbdd i
    exact ⟨r, hr, fun x hx => (h x hx).le⟩
  choose C hCpos hC using hCB
  -- the neighbourhood `U = {x | ∀ n, ‖φ n x‖ ≤ 1}`
  have hU : {x : E | ∀ n, ‖φ n x‖ ≤ 1} ∈ 𝓝 (0 : E) := by
    have h0 := Metric.equicontinuousAt_iff_right.1 (hφ 0) 1 one_pos
    filter_upwards [h0] with x hx n
    have := hx n
    simp only [map_zero, dist_zero_left] at this
    exact this.le
  -- partial sums and the parameter space
  set s : ℕ → (ℕ → ℂ) → F := fun M t => ∑ n ∈ Finset.range M, (c n * t n) • y n with hs_def
  set P : Set (ℕ → ℂ) := Set.univ.pi (fun _ => Metric.closedBall (0 : ℂ) 1) with hP_def
  have hPc : IsCompact P := isCompact_univ_pi (fun _ => isCompact_closedBall 0 1)
  have hPmem : ∀ t ∈ P, ∀ n, ‖t n‖ ≤ 1 := by
    intro t ht n
    have := ht n (Set.mem_univ n)
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  -- tails of `∑ ‖c n‖`
  set S : ℕ → ℝ := fun M => ∑ n ∈ Finset.range M, ‖c n‖ with hS_def
  set σ : ℝ := ∑' n, ‖c n‖ with hσ_def
  have hStend : Tendsto S atTop (𝓝 σ) := hc.hasSum.tendsto_sum_nat
  have hSle : ∀ M, S M ≤ σ := fun M => hc.sum_le_tsum _ (fun i _ => norm_nonneg _)
  have hSIco : ∀ N M, N ≤ M → S M - S N = ∑ n ∈ Finset.Ico N M, ‖c n‖ :=
    fun N M h => (Finset.sum_Ico_eq_sub _ h).symm
  have hSmono : ∀ N M, N ≤ M → 0 ≤ S M - S N := by
    intro N M h
    rw [hSIco N M h]
    exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have htail : Tendsto (fun N => σ - S N) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := σ)).sub hStend
    simpa using this
  -- differences of partial sums
  have hdiff : ∀ t ∈ P, ∀ N M, N ≤ M → s M t - s N t ∈ (S M - S N) • B := by
    intro t ht N M hNM
    have h1 : s M t - s N t = ∑ n ∈ Finset.Ico N M, (c n * t n) • y n :=
      (Finset.sum_Ico_eq_sub _ hNM).symm
    rw [h1]
    have h3 := sum_smul_mem hBne hBal hBconv (Finset.Ico N M) (fun n => c n * t n) y
      (fun n _ => hyB n)
    refine (balanced_real hBal).smul_mono ?_ h3
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _)),
      Real.norm_of_nonneg (hSmono N M hNM), hSIco N M hNM]
    refine Finset.sum_le_sum (fun n _ => ?_)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (hPmem t ht n)
  have hspan : ∀ M t, s M t ∈ Submodule.span ℂ B := fun M t =>
    Submodule.sum_mem _ (fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span (hyB n)))
  have hgauge_diff : ∀ t ∈ P, ∀ N M, N ≤ M → gauge B (s M t - s N t) ≤ σ - S N := by
    intro t ht N M h
    calc gauge B (s M t - s N t) ≤ S M - S N := gauge_le_of_mem (hSmono N M h) (hdiff t ht N M h)
      _ ≤ σ - S N := by linarith [hSle M]
  have hneg : ∀ x ∈ B, -x ∈ B := fun x hx => hBal.neg_mem_iff.2 hx
  -- Cauchy property in `F_B`
  have hcauchy : ∀ t ∈ P, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      gauge B (s m t - s n t) < ε := by
    intro t ht ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (htail.eventually (gt_mem_nhds hε))
    refine ⟨N, fun m hm n hn => ?_⟩
    rcases le_total n m with h | h
    · exact (hgauge_diff t ht n m h).trans_lt (hN n hn)
    · rw [← neg_sub, gauge_neg hneg]
      exact (hgauge_diff t ht m n h).trans_lt (hN m hm)
  have hlim : ∀ t ∈ P, ∃ z ∈ Submodule.span ℂ B,
      Tendsto (fun M => gauge B (s M t - z)) atTop (𝓝 0) := fun t ht =>
    hBcomplete (fun M => s M t) (fun M => hspan M t) (hcauchy t ht)
  choose! Φ hΦspan hΦlim using hlim
  -- seminorm convergence of the partial sums to `Φ t`
  have hpconv : ∀ t ∈ P, ∀ i, Tendsto (fun M => p i (s M t - Φ t)) atTop (𝓝 0) := by
    intro t ht i
    have h1 : Tendsto (fun M => gauge B (s M t - Φ t) * C i) atTop (𝓝 0) := by
      simpa using (hΦlim t ht).mul_const (C i)
    refine squeeze_zero (fun M => apply_nonneg _ _) (fun M => ?_) h1
    exact seminorm_le_gauge_mul (p i) hBne hBal hBconv (hCpos i) (hC i)
      (Submodule.sub_mem _ (hspan M t) (hΦspan t ht))
  have hFtend : ∀ t ∈ P, Tendsto (fun M => s M t) atTop (𝓝 (Φ t)) := by
    intro t ht
    rw [hp.tendsto_nhds]
    intro i ε hε
    exact (hpconv t ht i).eventually (gt_mem_nhds hε)
  -- uniform estimate
  have hunif : ∀ t ∈ P, ∀ i N, p i (Φ t - s N t) ≤ (σ - S N) * C i := by
    intro t ht i N
    have hle : ∀ M, N ≤ M → p i (Φ t - s N t) ≤ p i (s M t - Φ t) + (σ - S N) * C i := by
      intro M hM
      have e : Φ t - s N t = (s M t - s N t) - (s M t - Φ t) := by abel
      rw [e]
      refine (map_sub_le_add _ _ _).trans ?_
      have h2 : p i (s M t - s N t) ≤ (S M - S N) * C i :=
        seminorm_le_of_mem_smul (p i) (hC i) (hSmono N M hM) (hdiff t ht N M hM)
      have h3 : (S M - S N) * C i ≤ (σ - S N) * C i :=
        mul_le_mul_of_nonneg_right (by linarith [hSle M]) (hCpos i).le
      linarith
    have hlimit : Tendsto (fun M => p i (s M t - Φ t) + (σ - S N) * C i) atTop
        (𝓝 (0 + (σ - S N) * C i)) := (hpconv t ht i).add_const _
    have := ge_of_tendsto hlimit (eventually_atTop.2 ⟨N, hle⟩)
    simpa using this
  -- continuity
  have hsc : ∀ N, Continuous (s N) := fun N =>
    continuous_finsetSum _ (fun n _ =>
      ((continuous_const.mul (continuous_apply n)).smul continuous_const))
  have hΦc : ContinuousOn Φ P := by
    intro t0 ht0
    rw [ContinuousWithinAt, hp.tendsto_nhds]
    intro i ε hε
    have h1 : Tendsto (fun N => (σ - S N) * C i) atTop (𝓝 0) := by
      simpa using htail.mul_const (C i)
    obtain ⟨N, hN⟩ := (h1.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3))).exists
    have hcont := (hp.tendsto_nhds (s N) (s N t0)).1 ((hsc N).tendsto t0) i (ε / 3)
      (by positivity)
    filter_upwards [nhdsWithin_le_nhds hcont, self_mem_nhdsWithin] with t ht htP
    have e : Φ t - Φ t0 = ((Φ t - s N t) + (s N t - s N t0)) - (Φ t0 - s N t0) := by abel
    rw [e]
    have h2 := hunif t htP i N
    have h3 := hunif t0 ht0 i N
    have h4 := map_sub_le_add (p i) ((Φ t - s N t) + (s N t - s N t0)) (Φ t0 - s N t0)
    have h5 := map_add_le_add (p i) (Φ t - s N t) (s N t - s N t0)
    linarith
  -- conclusion
  have := hT2
  refine ⟨Φ '' P, hPc.image_of_continuousOn hΦc, ?_⟩
  filter_upwards [hU] with x hx
  have htP : (fun n => φ n x) ∈ P := by
    intro n _
    simpa [Metric.mem_closedBall, dist_zero_right] using hx n
  exact ⟨_, htP, tendsto_nhds_unique (hFtend _ htP) (hsum x).tendsto_sum_nat⟩
