-- Prove2me | solution 1 for GrothendieckLB.Supplement.exists_limitingScheme_cqCorr
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T16:27:40.551798+00:00
-- url     : https://prove2.me/submissions/8e362d90-80b8-435f-8949-9760989bc5f7

import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_LimitingScheme_corr

open Filter MeasureTheory GrothendieckLB GrothendieckLB.Supplement
open scoped Topology

private noncomputable def threshold (q : ℝ → ℝ) (z : Fin 2 → ℝ) : ℝ :=
  if 0 ≤ z 0 + q (z 1) then 1 else -1

private theorem threshold_properties (q : ℝ → ℝ) (hc : Continuous q)
    (ho : ∀ x, q (-x) = -q x) :
    Measurable (threshold q) ∧
      (∀ z, threshold q z = 1 ∨ threshold q z = -1) ∧
      (∀ᵐ z ∂(volume : Measure (Fin 2 → ℝ)), threshold q (-z) = -threshold q z) ∧
      volume {z | ¬ ContinuousAt (threshold q) z} = 0 := by
  let F (z : Fin 2 → ℝ) := z 0 + q (z 1)
  have hF : Continuous F := (continuous_apply 0).add (hc.comp (continuous_apply 1))
  let graph : Set (ℝ × ℝ) := {p | p.1 = -q p.2}
  have hm : MeasurableSet graph := (isClosed_eq continuous_fst (hc.comp continuous_snd).neg).measurableSet
  have hgraph : (volume : Measure (ℝ × ℝ)) graph = 0 := by
    change (volume.prod volume) graph = 0
    rw [Measure.prod_apply_symm hm]
    have hfiber (y : ℝ) : (fun x : ℝ => (x, y)) ⁻¹' graph = {-q y} := rfl
    simp [hfiber]
  have hnull : volume {z : Fin 2 → ℝ | z 0 = -q (z 1)} = 0 :=
    (volume_preserving_finTwoArrow ℝ).preimage_null hgraph
  have hzero : volume {z | F z = 0} = 0 := by
    refine measure_mono_null ?_ hnull
    intro z hz
    change z 0 + q (z 1) = 0 at hz
    change z 0 = -q (z 1)
    linarith
  have hae : ∀ᵐ z ∂(volume : Measure (Fin 2 → ℝ)), F z ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not] using hzero
  refine ⟨Measurable.ite (measurableSet_le measurable_const hF.measurable)
    measurable_const measurable_const, ?_, ?_, ?_⟩
  · intro z
    unfold threshold
    split <;> simp
  · filter_upwards [hae] with z hz
    have hneg : F (-z) = -F z := by
      change -z 0 + q (-(z 1)) = -(z 0 + q (z 1))
      rw [ho]
      ring
    change (if 0 ≤ F (-z) then (1 : ℝ) else -1) = -(if 0 ≤ F z then 1 else -1)
    rw [hneg]
    rcases lt_or_gt_of_ne hz with h | h
    · simp [not_le.mpr h, neg_nonneg.mpr h.le]
    · simp [h.le, not_le.mpr h]
  · refine measure_mono_null ?_ hzero
    intro z hz
    change F z = 0
    by_contra hn
    apply hz
    rcases lt_or_gt_of_ne hn with h | h
    · have hev : ∀ᶠ y in 𝓝 z, F y < 0 := hF.continuousAt.tendsto.eventually (eventually_lt_nhds h)
      have heq : threshold q =ᶠ[𝓝 z] fun _ => (-1 : ℝ) :=
        hev.mono fun y hy => if_neg (not_le.mpr hy)
      exact (continuousAt_congr heq).2 continuousAt_const
    · have hev : ∀ᶠ y in 𝓝 z, 0 < F y := hF.continuousAt.tendsto.eventually (eventually_gt_nhds h)
      have heq : threshold q =ᶠ[𝓝 z] fun _ => (1 : ℝ) :=
        hev.mono fun y hy => if_pos hy.le
      exact (continuousAt_congr heq).2 continuousAt_const

private theorem allowable_cq (s₃ s₅ : ℝ) :
    IsAllowableCorr (fun t => (cqRhoPoly s₃ s₅).eval t) := by
  classical
  let V := 1 + s₃ ^ 2 + s₅ ^ 2
  have hV : 0 < V := by dsimp [V]; positivity
  let c (n : ℕ) : ℝ := if n = 1 then 1 / V else if n = 3 then -(s₃ ^ 2 / V)
    else if n = 5 then s₅ ^ 2 / V else 0
  let I : Finset ℕ := {1, 3, 5}
  have hzero (n : ℕ) (hn : n ∉ I) : c n = 0 := by
    have h1 : n ≠ 1 := fun e => hn (by simp [I, e])
    have h3 : n ≠ 3 := fun e => hn (by simp [I, e])
    have h5 : n ≠ 5 := fun e => hn (by simp [I, e])
    simp [c, h1, h3, h5]
  have habs (n : ℕ) (hn : n ∉ I) : |c n| = 0 := by rw [hzero n hn, abs_zero]
  refine ⟨c, ?_, summable_of_ne_finset_zero habs, ?_, ?_⟩
  · rintro n ⟨j, hj⟩
    have h1 : n ≠ 1 := by omega
    have h3 : n ≠ 3 := by omega
    have h5 : n ≠ 5 := by omega
    simp [c, h1, h3, h5]
  · rw [tsum_eq_sum habs]
    have heval : (∑ n ∈ I, |c n|) = |1 / V| + (|-(s₃ ^ 2 / V)| + |s₅ ^ 2 / V|) := by
      norm_num [I, c, Finset.sum_insert]
    rw [heval, abs_neg, abs_of_nonneg (div_nonneg zero_le_one hV.le),
      abs_of_nonneg (div_nonneg (sq_nonneg s₃) hV.le),
      abs_of_nonneg (div_nonneg (sq_nonneg s₅) hV.le)]
    apply le_of_eq
    field_simp [hV.ne'] <;> dsimp [V] <;> ring
  · intro t _
    have hterm (n : ℕ) (hn : n ∉ I) : c n * t ^ n = 0 := by rw [hzero n hn, zero_mul]
    rw [tsum_eq_sum hterm]
    norm_num [I, c, V, cqRhoPoly, Finset.sum_insert] <;> ring

theorem solution (η s₃ s₅ : ℝ) : ∃ S : LimitingScheme 2, S.corr = cqCorr η s₃ s₅ := by
  let q (x : ℝ) := η / Real.sqrt (1 + s₃ ^ 2 + s₅ ^ 2) * he 3 x
  have hq : Continuous q := by
    change Continuous (fun x : ℝ => η / Real.sqrt (1 + s₃^2 + s₅^2) * ((x^3 - 3*x) / Real.sqrt 6))
    fun_prop
  have hodd (x : ℝ) : q (-x) = -q x := by
    change _ * (((-x)^3 - 3*(-x)) / Real.sqrt 6) = -(_ * ((x^3 - 3*x) / Real.sqrt 6))
    ring
  let f (z : Fin 2 → ℝ) := cqF η s₃ s₅ (z 0) (z 1)
  let g (z : Fin 2 → ℝ) := cqG η s₃ s₅ (z 0) (z 1)
  have hf : threshold q = f := rfl
  have hg : threshold (fun x => -q x) = g := by
    funext z
    simp only [threshold, g, cqG, q, sub_eq_add_neg]
  have fprops := threshold_properties q hq hodd
  rw [hf] at fprops
  obtain ⟨hfm, hfs, hfo, hfc⟩ := fprops
  have hodd' (x : ℝ) : -(q (-x)) = -(-q x) := by rw [hodd]
  have gprops := threshold_properties (fun x => -q x) hq.neg hodd'
  rw [hg] at gprops
  obtain ⟨hgm, hgs, hgo, hgc⟩ := gprops
  let ρ : Fin 2 → ℝ → ℝ := ![fun t => (cqRhoPoly s₃ s₅).eval t, fun t => t]
  have hr (i : Fin 2) : IsAllowableCorr (ρ i) := by
    fin_cases i
    · exact allowable_cq s₃ s₅
    · change IsAllowableCorr (fun t => t)
      simpa [cqRhoPoly] using allowable_cq 0 0
  let S : LimitingScheme 2 := {
    f := f, g := g, measurable_f := hfm, measurable_g := hgm,
    f_sign := hfs, g_sign := hgs, f_odd := hfo, g_odd := hgo,
    f_disc_null := hfc, g_disc_null := hgc, ρ := ρ, ρ_allowable := hr }
  refine ⟨S, ?_⟩
  funext t
  have hv : (fun i => ρ i t) = ![(cqRhoPoly s₃ s₅).eval t, t] := by
    funext i
    fin_cases i <;> rfl
  change multiCorr f g (fun i => ρ i t) = multiCorr f g ![(cqRhoPoly s₃ s₅).eval t, t]
  rw [hv]
