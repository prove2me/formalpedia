-- Prove2me | solution 1 for GeometryOfGraphs.Clique.volume_count
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:44:50.782761+00:00
-- url     : https://prove2.me/submissions/1cf3213b-e7b3-4e7d-8039-2246740c1853

import Mathlib
import Definitions.Def_GeometryOfGraphs_Clique_isoDim

set_option autoImplicit false
open GeometryOfGraphs.Clique MeasureTheory
open scoped Pointwise

/-- difference body inclusion, for a norm-like function on an arbitrary real module -/
theorem diff_body_gen {E : Type*} [AddCommGroup E] [Module ℝ E] (N : E → ℝ)
    (hhom : ∀ (a : ℝ) z, N (a • z) = |a| * N z) (htri : ∀ u v, N (u + v) ≤ N u + N v)
    {n : ℕ} (x : Fin n → E)
    (hx : ∀ i j, i ≠ j → N (x i - x j) = 1)
    (u v : E)
    (hu : u ∈ convexHull ℝ (Set.range x))
    (hv : v ∈ convexHull ℝ (Set.range x)) :
    N (u - v) ≤ 1 := by
  have hN0 : N 0 = 0 := by simpa using hhom 0 0
  have hneg : ∀ y, N (-y) = N y := fun y => by
    have := hhom (-1) y
    simpa using this
  have hball : ∀ c : E, Convex ℝ {y | N (y - c) ≤ 1} := by
    intro c y hy z hz a b ha hb hab
    simp only [Set.mem_setOf_eq] at *
    have e : a • y + b • z - c = a • (y - c) + b • (z - c) := by
      have hc : c = (a + b) • c := by rw [hab, one_smul]
      conv_lhs => rw [hc]
      simp only [smul_sub, add_smul]
      abel
    rw [e]
    calc N (a • (y - c) + b • (z - c)) ≤ N (a • (y - c)) + N (b • (z - c)) := htri _ _
      _ = a * N (y - c) + b * N (z - c) := by
          rw [hhom, hhom, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr
      _ = 1 := by rw [mul_one, mul_one, hab]
  have hxx : ∀ i j, N (x i - x j) ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [hN0]
    · exact (hx i j h).le
  have step1 : ∀ i, ∀ w ∈ convexHull ℝ (Set.range x), N (w - x i) ≤ 1 := by
    intro i w hw
    have : convexHull ℝ (Set.range x) ⊆ {y | N (y - x i) ≤ 1} :=
      convexHull_min (by rintro _ ⟨j, rfl⟩; exact hxx j i) (hball _)
    exact this hw
  have step2 : convexHull ℝ (Set.range x) ⊆ {y | N (y - v) ≤ 1} := by
    refine convexHull_min ?_ (hball v)
    rintro _ ⟨j, rfl⟩
    have := step1 j v hv
    have h2 : x j - v = -(v - x j) := by abel
    show N (x j - v) ≤ 1
    rw [h2, hneg]
    exact this
  exact step2 hu

/-- translates of the hull have disjoint interiors -/
theorem disj_gen {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] (N : E → ℝ)
    (hhom : ∀ (a : ℝ) z, N (a • z) = |a| * N z) (htri : ∀ u v, N (u + v) ≤ N u + N v)
    {n : ℕ} (x : Fin n → E)
    (hx : ∀ i j, i ≠ j → N (x i - x j) = 1)
    (i j : Fin n) (hij : i ≠ j) :
    interior (((fun y => y + x i) '' convexHull ℝ (Set.range x)) ∩
      ((fun y => y + x j) '' convexHull ℝ (Set.range x))) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨I, hI⟩ : ∃ I : Set _, I = ((fun y => y + x i) '' convexHull ℝ (Set.range x)) ∩
      ((fun y => y + x j) '' convexHull ℝ (Set.range x)) := ⟨_, rfl⟩
  rw [← hI] at hz
  set e : E := x i - x j with he
  have hg : Continuous (fun t : ℝ => z + t • e) := by fun_prop
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (isOpen_interior.preimage hg) 0 (by simpa using hz)
  have h1 : z + (ε / 2) • e ∈ interior I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith)
  have h2 : z + (-(ε / 2)) • e ∈ interior I := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]
    linarith)
  have h1m : z + (ε / 2) • e ∈ I := interior_subset h1
  have h2m : z + (-(ε / 2)) • e ∈ I := interior_subset h2
  rw [hI] at h1m h2m
  have h1' := h1m.2
  have h2' := h2m.1
  obtain ⟨v, hvD, hv⟩ := h1'
  obtain ⟨u, huD, hu⟩ := h2'
  have hv' : v + x j = z + (ε / 2) • e := hv
  have hu' : u + x i = z + (-(ε / 2)) • e := hu
  have hvu : v - u = (2 * (ε / 2) + 1) • e := by
    have : v - u = (v + x j) - (u + x i) + e := by rw [he]; abel
    rw [this, hv', hu']
    module
  have := diff_body_gen N hhom htri x hx v u hvD huD
  rw [hvu, hhom, he, hx i j hij, abs_of_pos (by positivity)] at this
  linarith

theorem vol_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (M : E → ℝ) (hhom : ∀ (a : ℝ) z, M (a • z) = |a| * M z)
    (htri : ∀ u v, M (u + v) ≤ M u + M v)
    {n : ℕ} (y : Fin n → E) (hy : ∀ i j, i ≠ j → M (y i - y j) = 1)
    (hint : (interior (convexHull ℝ (Set.range y))).Nonempty) :
    n ≤ 2 ^ Module.finrank ℝ E := by
  set D := convexHull ℝ (Set.range y) with hD
  have hDc : IsCompact D := (Set.finite_range y).isCompact_convexHull ℝ
  have hDconv : Convex ℝ D := convex_convexHull ℝ _
  have hDpos : 0 < μ D :=
    lt_of_lt_of_le (isOpen_interior.measure_pos μ hint) (measure_mono interior_subset)
  have hDfin : μ D < ⊤ := hDc.measure_lt_top
  let T : Fin n → Set E := fun i => (fun z => z + y i) '' D
  have hTc : ∀ i, IsCompact (T i) := fun i => hDc.image (continuous_id.add continuous_const)
  have hTm : ∀ i, MeasurableSet (T i) := fun i => (hTc i).isClosed.measurableSet
  have hTconv : ∀ i, Convex ℝ (T i) := fun i => by
    have : T i = D + {y i} := by rw [Set.add_singleton]
    rw [this]
    exact hDconv.add (convex_singleton _)
  have hTμ : ∀ i, μ (T i) = μ D := by
    intro i
    show μ ((fun z => z + y i) '' D) = μ D
    rw [Set.image_add_right]
    exact measure_preimage_add_right μ (-y i) D
  have hae : Pairwise (Function.onFun (AEDisjoint μ) T) := by
    intro i j hij
    have hI : Convex ℝ (T i ∩ T j) := (hTconv i).inter (hTconv j)
    have hint0 : interior (T i ∩ T j) = ∅ := disj_gen M hhom htri y hy i j hij
    have hfr : μ (frontier (T i ∩ T j)) = 0 := hI.addHaar_frontier μ
    have hsub : T i ∩ T j ⊆ frontier (T i ∩ T j) := by
      rw [frontier, hint0, Set.diff_empty]
      exact subset_closure
    exact measure_mono_null hsub hfr
  have hunion : μ (⋃ i, T i) = n * μ D := by
    rw [measure_iUnion₀ hae (fun i => (hTm i).nullMeasurableSet), tsum_fintype]
    simp [hTμ]
  have hsub : (⋃ i, T i) ⊆ (2 : ℝ) • D := by
    have h2 : (2 : ℝ) • D = D + D := by
      have := hDconv.add_smul (zero_le_one' ℝ) (zero_le_one' ℝ)
      simp only [one_smul] at this
      rw [← this]
      norm_num
    rw [h2]
    intro z hz
    obtain ⟨i, w, hw, rfl⟩ := Set.mem_iUnion.mp hz |>.imp fun i h => h
    exact Set.add_mem_add hw (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hle : (n : ENNReal) * μ D ≤ ENNReal.ofReal (|(2 : ℝ) ^ Module.finrank ℝ E|) * μ D := by
    rw [← hunion, ← Measure.addHaar_smul μ (2 : ℝ) D]
    exact measure_mono hsub
  rw [ENNReal.mul_le_mul_iff_left hDpos.ne' hDfin.ne] at hle
  have h2 : ENNReal.ofReal (|(2 : ℝ) ^ Module.finrank ℝ E|) = ((2 ^ Module.finrank ℝ E : ℕ) : ENNReal) := by
    rw [abs_of_nonneg (by positivity), ← ENNReal.ofReal_natCast]
    push_cast
    rfl
  rw [h2] at hle
  exact_mod_cast hle

theorem solution {n d : ℕ} (hn : 0 < n) (N : (Fin d → ℝ) → ℝ)
    (hN : IsNormFun N) (x : Fin n → (Fin d → ℝ))
    (hx : ∀ i j, i ≠ j → N (x i - x j) = 1) :
    n ≤ 2 ^ d := by
  obtain ⟨_, _, hhom, htri⟩ := hN
  let i0 : Fin n := ⟨0, hn⟩
  let W : Submodule ℝ (Fin d → ℝ) := Submodule.span ℝ (Set.range fun i => x i - x i0)
  let y : Fin n → W := fun i => ⟨x i - x i0, Submodule.subset_span ⟨i, rfl⟩⟩
  let M : W → ℝ := fun w => N w.1
  have hMhom : ∀ (a : ℝ) z, M (a • z) = |a| * M z := fun a z => hhom a z.1
  have hMtri : ∀ u v, M (u + v) ≤ M u + M v := fun u v => htri u.1 v.1
  have hy : ∀ i j, i ≠ j → M (y i - y j) = 1 := by
    intro i j hij
    show N (x i - x i0 - (x j - x i0)) = 1
    rw [sub_sub_sub_cancel_right]
    exact hx i j hij
  have hint : (interior (convexHull ℝ (Set.range y))).Nonempty := by
    rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
    have hy0 : y i0 = 0 := by
      apply Subtype.ext
      show x i0 - x i0 = 0
      simp
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ W W (s := Set.range y) ⟨y i0, i0, rfl⟩]
    have hvs := vectorSpan_eq_span_vsub_set_right (k := ℝ) (s := Set.range y) (p := y i0) ⟨i0, rfl⟩
    rw [hvs]
    have claim : ∀ (w : Fin d → ℝ) (hw : w ∈ Submodule.span ℝ (Set.range fun i => x i - x i0)),
        (⟨w, hw⟩ : W) ∈ Submodule.span ℝ ((fun p => p -ᵥ y i0) '' Set.range y) := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨i, rfl⟩ := hv
        exact Submodule.subset_span ⟨y i, ⟨i, rfl⟩, by beta_reduce; rw [vsub_eq_sub, hy0, sub_zero]; try rfl⟩
      | zero => exact Submodule.zero_mem _
      | add a b ha hb iha ihb => exact Submodule.add_mem _ iha ihb
      | smul c v hv ih => exact Submodule.smul_mem _ c ih
    rw [eq_top_iff]
    rintro ⟨w, hw⟩ -
    exact claim w hw
  have := vol_aux (Measure.addHaar : Measure W) M hMhom hMtri y hy hint
  calc n ≤ 2 ^ Module.finrank ℝ W := this
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) (by simpa using Submodule.finrank_le W)
