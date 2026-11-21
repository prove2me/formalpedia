-- Prove2me | solution 1 for MomentSearch.rakhmanov_triangle_contour_identity
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T00:03:28.283472+00:00
-- url     : https://prove2.me/submissions/5e7e6efc-814e-42a2-bc70-1cb5595f6bd8

import Mathlib
import Theorems.Thm_MomentSearch_rakhmanov_quantile_real_regularization
import Theorems.Thm_MomentSearch_rakhmanov_off_node_cauchy_formula

open Set Filter MeasureTheory
open scoped Topology

private theorem continuousAtCauchy {A Z : ℝ → ℂ} {x : ℝ} (hZ : Continuous Z)
    (hA : IntervalIntegrable A volume 0 2)
    (hne : ∀ t ∈ Icc (0:ℝ) 2, (x:ℂ) ≠ Z t) :
    ContinuousAt (fun u : ℝ => ∫ t in (0:ℝ)..2, A t / ((u:ℂ)-Z t)) x := by
  obtain ⟨p,hp,hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0:ℝ) 2).Nonempty from ⟨0,by norm_num⟩)
    (show Continuous (fun t => ‖(x:ℂ)-Z t‖) by fun_prop).continuousOn
  let m := ‖(x:ℂ)-Z p‖
  have hm : 0 < m := norm_pos_iff.mpr (sub_ne_zero.mpr (hne p hp))
  have far {u t : ℝ} (hu : dist u x < m/2) (ht : t ∈ Icc (0:ℝ) 2) :
      m/2 ≤ ‖(u:ℂ)-Z t‖ := by
    have hl : m ≤ ‖(x:ℂ)-Z t‖ := hmin ht
    have hh := norm_add_le ((x:ℂ)-u) ((u:ℂ)-Z t)
    rw [sub_add_sub_cancel] at hh
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at hh
    rw [Real.dist_eq] at hu
    linarith
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun t => ‖A t‖ * (m/2)⁻¹)
  · exact .of_forall fun u => (hA.def'.1.aemeasurable.div
      ((continuous_const.sub hZ).aemeasurable)).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x (show 0 < m / 2 by positivity)] with u hu
    apply Filter.Eventually.of_forall
    intro t ht
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 2)] at ht
    rw [norm_div, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) (far hu ⟨ht.1.le,ht.2⟩)
  · exact hA.norm.mul_const _
  · apply Filter.Eventually.of_forall
    intro t ht
    rw [uIoc_of_le (by norm_num : (0:ℝ) ≤ 2)] at ht
    exact continuousAt_const.div (Complex.continuous_ofReal.continuousAt.sub continuousAt_const)
      (sub_ne_zero.mpr (hne _ ⟨ht.1.le,ht.2⟩))

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun z => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - z ^ 2))
    let f : ℝ → ℝ := fun z => Real.cos (Real.pi * ∫ t in z..1, ρ t)
    let V : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, Real.log (1 / |z-t|) * ρ t
    let s : ℂ := ⟨1/2, -Real.sqrt 3 / 2⟩
    let Z : ℝ → ℂ := fun t => (r : ℂ) * (1 - s * t)
    let B : ℝ → ℂ := fun t => 2 * Complex.I * (N : ℂ) * r * s *
      ∫ v in (0 : ℝ)..t, Complex.arctan ((N : ℂ) / k *
        (((r : ℂ)^2 - (Z v)^2) ^ (1/2 : ℂ)))
    let η : ℝ → ℝ := fun x => (∫ t in (0 : ℝ)..2,
      Complex.log (1 + Complex.exp (-(B t))) * (-(r : ℂ) * s) / ((x : ℂ) - Z t)).im / Real.pi
    ∃ S : Polynomial ℝ, ∃ H : ℝ → ℝ, S.natDegree ≤ N-k ∧
      ContinuousOn H (Set.Icc (-1 : ℝ) 1) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, S.eval z = Real.exp (H z) * Real.exp (-V z) * f z) ∧
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, z ≠ r → z ≠ -r →
        H z = (if |z| < r then Real.log 2 else 0) + η z + η (-z) := by 
  intro r ρ f V s Z B η
  classical
  obtain ⟨hV,Y,hcard,hY,hzero,g,hgc,hg⟩ :=
    MomentSearch.rakhmanov_quantile_real_regularization N k hk hkN
  obtain ⟨hA,hoff⟩ := MomentSearch.rakhmanov_off_node_cauchy_formula N k hk hkN
  specialize hoff Y hcard hY hzero
  let S := Lagrange.nodal Y id
  let H := fun z => Real.log (g z) + V z
  have hmul (z : ℝ) (hz : z ∈ Icc (-1:ℝ) 1) : (∏ y ∈ Y, (z-y)) = g z * f z :=
    (hg z hz).2
  have hH : ContinuousOn H (Icc (-1:ℝ) 1) :=
    (hgc.log (fun z hz => (hg z hz).1.ne')).add hV
  have heval (z : ℝ) : S.eval z = ∏ y ∈ Y, (z-y) := Lagrange.eval_nodal
  refine ⟨S, H, ?_, hH, ?_, ?_⟩
  · dsimp [S]; rw [Lagrange.natDegree_nodal,hcard]
  · intro z hz
    rw [heval,hmul _ hz]
    dsimp [H]
    rw [Real.exp_add,Real.exp_log (hg _ hz).1,mul_assoc (g z),← Real.exp_add]
    simp
  · have agree (z : ℝ) (hz : z ∈ Icc (-1:ℝ) 1) (hn : z ∉ Y) (hr : z ≠ r) (hl : z ≠ -r) :
        H z = (if |z| < r then Real.log 2 else 0) + η z + η (-z) := by
      rw [← hoff z hz hn hr hl]
      have hf : f z ≠ 0 := fun e => hn ((hzero z hz).mpr e)
      have hlog := congrArg (fun q : ℝ => Real.log |q|) (hmul _ hz)
      simp only [Finset.abs_prod, Real.log_prod (fun y hy => abs_ne_zero.mpr (sub_ne_zero.mpr
        (show z ≠ y from fun e => hn (e ▸ hy)))), abs_mul,abs_of_pos (hg _ hz).1,
        Real.log_mul (hg _ hz).1.ne' (abs_ne_zero.mpr hf)] at hlog
      dsimp [H]
      linarith
    intro x hx hxr hxl
    by_cases hxy : x ∈ Y
    · have hi : x ∈ Ioo (-r) r := hY x hxy
      have hr : 0 < r := by linarith [hi.1,hi.2]
      have hr1 : r ≤ 1 := by
        dsimp [r]; rw [Real.sqrt_le_iff]
        exact ⟨by norm_num, by nlinarith [div_nonneg (sq_nonneg (k:ℝ)) (sq_nonneg (N:ℝ))]⟩
      have sub : Ioo (-r) r ⊆ Icc (-1:ℝ) 1 := fun z hz => ⟨by linarith [hz.1],by linarith [hz.2]⟩
      have contη (u : ℝ) (hu : u ≠ r) : ContinuousAt η u := by
        have ne (t : ℝ) (ht : t ∈ Icc (0:ℝ) 2) : (u:ℂ) ≠ Z t := by
          intro h
          have him := congrArg Complex.im h
          simp [Z,s,Complex.mul_im,Complex.mul_re] at him
          have ht0 : t = 0 := by
            by_contra ht'
            have htpos := lt_of_le_of_ne ht.1 (Ne.symm ht')
            have hsq : 0 < Real.sqrt 3 := by positivity
            rcases him with h | h <;> simp_all
          subst t
          exact hu (by simpa [Z] using h)
        have h := continuousAtCauchy (Z := Z) (by dsimp [Z]; fun_prop) hA ne
        exact (Complex.continuous_im.continuousAt.comp h).div_const _
      let good := Ioo (-r) r ∩ (↑Y : Set ℝ)ᶜ
      have dense : Ioo (-r) r ⊆ closure good := (Y.finite_toSet.countable.dense_compl ℝ).open_subset_closure_inter isOpen_Ioo
      have same : EqOn H (fun z => Real.log 2 + η z + η (-z)) good := by
        intro z hz
        have hh := hz.1
        have h := agree z (sub hh) hz.2 (ne_of_lt hh.2) (ne_of_gt hh.1)
        simpa only [if_pos (abs_lt.mpr hh)] using h
      have cr : ContinuousOn (fun z => Real.log 2 + η z + η (-z)) (Ioo (-r) r) := by
        intro z hz
        exact ((continuousAt_const.add (contη z hz.2.ne)).add
          ((contη (-z) (by linarith [hz.1])).comp continuous_neg.continuousAt)).continuousWithinAt
      rw [if_pos (abs_lt.mpr hi)]
      exact same.of_subset_closure (hH.mono sub) cr inter_subset_left dense hi
    · exact agree x hx hxy hxr hxl
