-- Prove2me | solution 1 for OAI.LipschitzCounterexample.LocalizedLinearization.shrinking_tests
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:06:55.77292+00:00
-- url     : https://prove2.me/submissions/d033908d-dbad-44cc-97d7-f01d211a15a0

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/Localization.lean:L359-L448
-- (upload_full_project.md Phase 4): solution for node OAI.LipschitzCounterexample.LocalizedLinearization.shrinking_tests. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Theorems.Thm_OAI_LipschitzCounterexample_LocalizedLinearization_disjointOperator_coord
import Theorems.Thm_OAI_LipschitzCounterexample_WeakSequences_schur

-- ---- from OAI.Analysis.LipschitzEquivalence.Schur ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF

noncomputable section
namespace LipschitzCounterexample

namespace WeakSequences
open Filter Topology
open scoped ENNReal NNReal
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem WeakNull.map {u : ℕ → E} (hu : WeakNull u) (T : E →L[ℝ] F) :
    WeakNull (fun n => T (u n)) := fun f => hu (f.comp T)

theorem WeakNull.subseq {u : ℕ → E} (hu : WeakNull u) {a : ℕ → ℕ} (ha : StrictMono a) :
    WeakNull (fun n => u (a n)) := fun f => (hu f).comp ha.tendsto_atTop

end WeakSequences

end LipschitzCounterexample
end

end OAI

-- ---- from OAI.Analysis.LipschitzEquivalence.Localization ----
namespace OAI

universe uM uV

noncomputable section
namespace LipschitzCounterexample

namespace LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

omit [Zero M] in
theorem lipschitz_const_sub {V : Type uV} [NormedAddCommGroup V] (f : M → V)
    {K : ℝ≥0} (hf : LipschitzWith K f) (c : V) :
    LipschitzWith K (fun x => c - f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_sub_left] using hf.dist_le_mul x y

theorem norm_test_apply_le (f : FreeSpace.LipZero M) (μ : FreeSpace.Space M) :
    ‖test f μ‖ ≤ ‖f‖ * ‖μ‖ := by
  change ‖μ.1 f‖ ≤ ‖f‖ * ‖μ.1‖
  simpa only [mul_comm] using μ.1.le_opNorm f

theorem norm_normalized_le (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) :
    ‖normalized f hf‖ ≤ C := FreeSpace.norm_le_of_lipschitz _ (by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [normalized, Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y)

omit [Zero M] in
theorem cutoff_one (z : M) {s : ℝ≥0} (hs : 0 < s) {x : M} (hx : dist x z ≤ s / 2) :
    cutoff z s x = 1 := by
  have hs' : 0 < (s : ℝ) := hs
  have hmul : (2 / (s : ℝ)) * dist x z ≤ 1 := by
    calc
      _ ≤ (2 / (s : ℝ)) * ((s : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ = 1 := by field_simp
  unfold cutoff
  rw [min_eq_left (by linarith)]
  norm_num

omit [Zero M] in
theorem annular_product_lipschitz (z : M) {s : ℝ≥0} (hs : 0 < s)
    (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) (hfz : f z = 0) :
    LipschitzWith (3 * C) (fun x => f x * (1 - cutoff z s x)) := by
  apply product_lipschitz z hs f _ hf hfz
  · exact lipschitz_const_sub _ (cutoff_lipschitz z s) 1
  · intro x
    rw [abs_of_nonneg (sub_nonneg.mpr (cutoff_le_one z s x))]
    linarith [cutoff_nonneg z s x]
  · intro x y h
    by_contra! hc
    exact h (by rw [cutoff_zero z hs hc.1, cutoff_zero z hs hc.2])

theorem disjoint_tests_vanish {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) :
    Tendsto (fun i => test (normalized (h i) (hh i)) (μ i)) atTop (𝓝 0) := by
  have hn := WeakSequences.schur (hw.map (disjointOperator hd))
  apply squeeze_zero_norm (fun i => ?_) (by simpa only [norm_zero] using hn.norm)
  rw [← disjointOperator_coord hd hh]
  exact lp.norm_apply_le_norm (by norm_num) _ _

omit [Zero M] in
theorem finite_avoid_radius (z : M) (A : Finset M) {r : ℝ} (hr : 0 < r) :
    ∃ s : ℝ, 0 < s ∧ s < r ∧ ∀ x ∈ A, x ≠ z → s ≤ dist x z := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨r / 2, half_pos hr, half_lt_self hr, by simp⟩
  | @insert x A hx ih =>
      obtain ⟨s, hs, hsr, hA⟩ := ih
      by_cases hxz : x = z
      · refine ⟨s, hs, hsr, ?_⟩
        intro y hy hyz
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact (hyz hxz).elim
        · exact hA y hy hyz
      · refine ⟨min s (dist x z), lt_min hs (dist_pos.mpr hxz),
          (min_le_left _ _).trans_lt hsr, ?_⟩
        intro y hy hyz
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hA y hy hyz)

theorem test_combination_zero (f : FreeSpace.LipZero M) (a : M →₀ ℝ)
    (hf : ∀ x ∈ a.support, f.1 x = 0) :
    test f (Finsupp.linearCombination ℝ FreeSpace.point a) = 0 := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, test_point]
  apply Finset.sum_eq_zero
  intro x hx
  rw [hf x hx, smul_zero]

theorem exists_small_cutoff (z : M) (μ : FreeSpace.Space M) (C : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) {r : ℝ≥0} (hr : 0 < r) :
    ∃ s : ℝ≥0, ∃ hs : 0 < s, s < r ∧ ∀ (f : M → ℝ) (hf : LipschitzWith C f)
      (hfz : f z = 0),
      |test (normalized (fun x => f x * cutoff z s x)
        (cutoff_product_lipschitz z hs f hf hfz)) μ| < ε := by
  classical
  have hden : 0 < 3 * (C : ℝ) + 1 := by positivity
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.1 FreeSpace.dense_combinations μ
    (ε / (3 * (C : ℝ) + 1)) (div_pos hε hden)
  obtain ⟨s, hs, hsr, hsA⟩ := finite_avoid_radius z (insert 0 a.support) (show 0 < (r : ℝ) from hr)
  let sn : ℝ≥0 := ⟨s, hs.le⟩
  refine ⟨sn, hs, hsr, ?_⟩
  intro f hf hfz
  let p : M → ℝ := fun x => f x * cutoff z sn x
  have hp : LipschitzWith (3 * C) p := cutoff_product_lipschitz z hs f hf hfz
  have hpzero (x : M) (hx : x ∈ insert 0 a.support) : p x = 0 := by
    by_cases hxz : x = z
    · simp [p, hxz, hfz]
    · change f x * cutoff z sn x = 0
      rw [cutoff_zero z hs (hsA x hx hxz), mul_zero]
  have hp0 := hpzero 0 (Finset.mem_insert_self _ _)
  have hν : test (normalized p hp) (Finsupp.linearCombination ℝ FreeSpace.point a) = 0 := by
    apply test_combination_zero
    intro x hx
    change p x - p 0 = 0
    rw [hpzero x (Finset.mem_insert_of_mem hx), hp0, sub_self]
  have heq : test (normalized p hp) μ =
      test (normalized p hp) (μ - Finsupp.linearCombination ℝ FreeSpace.point a) := by
    rw [map_sub, hν, sub_zero]
  change |test (normalized p hp) μ| < ε
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖normalized p hp‖ * ‖μ - Finsupp.linearCombination ℝ FreeSpace.point a‖ :=
      norm_test_apply_le _ _
    _ ≤ (3 * (C : ℝ) + 1) * ‖μ - Finsupp.linearCombination ℝ FreeSpace.point a‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have h := norm_normalized_le p hp
      simp only [NNReal.coe_mul, NNReal.coe_ofNat] at h
      linarith
    _ < (3 * (C : ℝ) + 1) * (ε / (3 * (C : ℝ) + 1)) := by
      apply mul_lt_mul_of_pos_left _ hden
      simpa only [dist_eq_norm] using ha
    _ = ε := mul_div_cancel₀ _ hden.ne'

theorem shrinking_tests (z : M) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (r : ℕ → ℝ≥0) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto (fun i => (r i : ℝ)) atTop (𝓝 0))
    (f : ℕ → M → ℝ) {C : ℝ≥0} (hf : ∀ i, LipschitzWith C (f i))
    (hfz : ∀ i, f i z = 0) (hfs : ∀ i x, (r i : ℝ) ≤ dist x z → f i x = 0) :
    Tendsto (fun i => test (normalized (f i) (hf i)) (μ i)) atTop (𝓝 0) := by
  classical
  by_contra hn
  rw [Metric.tendsto_atTop] at hn
  push Not at hn
  obtain ⟨ε, hε, hlarge⟩ := hn
  simp only [dist_zero_right, Real.norm_eq_abs] at hlarge
  have hsmall := fun i => exists_small_cutoff z (μ i) C (half_pos hε) (hr i)
  choose s hs hsr hsbound using hsmall
  have chooseStep (p : ℕ) : ∃ n : ℕ, p < n ∧
      ε ≤ |test (normalized (f n) (hf n)) (μ n)| ∧ (r n : ℝ) < s p / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hrlim ((s p : ℝ) / 2) (half_pos (hs p))
    obtain ⟨n, hnp, hnε⟩ := hlarge (max N (p + 1))
    refine ⟨n, ?_, hnε, ?_⟩
    · exact (Nat.lt_succ_self p).trans_le ((le_max_right _ _).trans hnp)
    · have ht := hN n ((le_max_left _ _).trans hnp)
      simpa only [dist_zero_right, Real.norm_of_nonneg (r n).coe_nonneg] using ht
  let next (p : ℕ) : ℕ := Classical.choose (chooseStep p)
  let seq : ℕ → ℕ := fun j => Nat.rec 0 (fun _ p => next p) j
  have hseq (j : ℕ) : seq j < seq (j+1) ∧
      ε ≤ |test (normalized (f (seq (j+1))) (hf _)) (μ (seq (j+1)))| ∧
      (r (seq (j+1)) : ℝ) < s (seq j) / 2 := Classical.choose_spec (chooseStep (seq j))
  have hseqmono : StrictMono seq := strictMono_nat_of_lt_succ (fun j => (hseq j).1)
  let a : ℕ → ℕ := fun j => seq (j+1)
  have ha : StrictMono a := fun _ _ h => hseqmono (Nat.add_lt_add_right h 1)
  have hrad (j : ℕ) : (r (a (j+1)) : ℝ) < s (a j) / 2 := (hseq (j+1)).2.2
  have hanti : StrictAnti (fun j => (r (a j) : ℝ)) := by
    apply strictAnti_nat_of_succ_lt
    intro j
    have ht : (s (a j) : ℝ) < r (a j) := hsr (a j)
    have hp : 0 < (s (a j) : ℝ) := hs (a j)
    linarith [hrad j]
  let h : ℕ → M → ℝ := fun j x => f (a j) x * (1 - cutoff z (s (a j)) x)
  have hh (j : ℕ) : LipschitzWith (3 * C) (h j) :=
    annular_product_lipschitz z (hs (a j)) (f (a j)) (hf _) (hfz _)
  have hsupport (j : ℕ) (x : M) (hx : h j x ≠ 0) :
      (s (a j) : ℝ) / 2 < dist x z ∧ dist x z < r (a j) := by
    constructor
    · by_contra hx'
      have ht := cutoff_one z (hs (a j)) (le_of_not_gt hx')
      exact hx (by simp only [h, ht, sub_self, mul_zero])
    · by_contra hx'
      have ht := hfs (a j) x (le_of_not_gt hx')
      exact hx (by simp only [h, ht, zero_mul])
  have hd : DisjointTests h := by
    intro x j k hj hk
    by_contra hjk
    have hs₁ := hsupport j x hj
    have hs₂ := hsupport k x hk
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · have ht := hanti.antitone (Nat.succ_le_of_lt hjk)
      change (r (a k) : ℝ) ≤ r (a (j+1)) at ht
      linarith [hrad j]
    · have ht := hanti.antitone (Nat.succ_le_of_lt hkj)
      change (r (a j) : ℝ) ≤ r (a (k+1)) at ht
      linarith [hrad k]
  have hpos (j : ℕ) : ε / 2 < |test (normalized (h j) (hh j)) (μ (a j))| := by
    let p : M → ℝ := fun x => f (a j) x * cutoff z (s (a j)) x
    have hp : LipschitzWith (3 * C) p :=
      cutoff_product_lipschitz z (hs (a j)) (f (a j)) (hf _) (hfz _)
    have hid : normalized (h j) (hh j) = normalized (f (a j)) (hf _) - normalized p hp := by
      apply Subtype.ext
      funext x
      change (f (a j) x * (1 - cutoff z (s (a j)) x)) -
        (f (a j) 0 * (1 - cutoff z (s (a j)) 0)) =
        (f (a j) x - f (a j) 0) -
          (f (a j) x * cutoff z (s (a j)) x - f (a j) 0 * cutoff z (s (a j)) 0)
      ring
    have hpairid : test (normalized (h j) (hh j)) (μ (a j)) =
        test (normalized (f (a j)) (hf _)) (μ (a j)) - test (normalized p hp) (μ (a j)) := by
      change (μ (a j)).1 (normalized (h j) (hh j)) = _
      rw [hid, map_sub]
      rfl
    have hremoved : |test (normalized p hp) (μ (a j))| < ε / 2 :=
      hsbound (a j) (f (a j)) (hf _) (hfz _)
    have hbig : ε ≤ |test (normalized (f (a j)) (hf _)) (μ (a j))| := (hseq j).2.1
    rw [hpairid]
    have ht := abs_sub_abs_le_abs_sub
      (test (normalized (f (a j)) (hf _)) (μ (a j))) (test (normalized p hp) (μ (a j)))
    linarith
  have hlim := disjoint_tests_vanish hd hh (hw.subseq ha)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (half_pos hε)
  have ht := hN N le_rfl
  rw [dist_zero_right, Real.norm_eq_abs] at ht
  exact (not_lt_of_ge (hpos N).le) ht

end LocalizedLinearization

end LipschitzCounterexample
end

end OAI

-- ---- platform node ----
open OAI OAI.LipschitzCounterexample OAI.LipschitzCounterexample.LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal


theorem solution.{uM} : type_of% @_root_.OAI.LipschitzCounterexample.LocalizedLinearization.shrinking_tests.{uM} := @_root_.OAI.LipschitzCounterexample.LocalizedLinearization.shrinking_tests.{uM}
