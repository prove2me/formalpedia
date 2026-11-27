-- Prove2me | solution 1 for LogBarrierIPM.Iterations.Supplement.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:03:40.254806+00:00
-- url     : https://prove2.me/submissions/153b59af-8c85-4e46-8267-404c34631437

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_PuiseuxGeometry

open Filter Matrix

open LogBarrierIPM
open LogBarrierIPM.Iterations
open LogBarrierIPM.Iterations.Supplement

open LogBarrierIPM.Curvature

theorem solution {p d q r : ℕ} (hd : 1 ≤ d)
    (A : Matrix (Fin p) (Fin d) Puiseux) (b : Fin p → Puiseux)
    (u : Fin q → Fin d → Puiseux) (v : Fin r → Fin d → Puiseux)
    (hgen : kPolyhedron A b = kGenerated u v) :
    ∀ᶠ t in atTop, realPolyhedron A b t =
      realGenerated (fun i => evalFun (u i) t) (fun j => evalFun (v j) t) := by
        classical
        set_option maxHeartbeats 0 in
          set_option backward.isDefEq.respectTransparency false in
            first
            | have hconst : ∀ c : ℝ, ∃ f : Puiseux, ∀ t : ℝ, f.eval t = c := by
                intro c
                let f : Puiseux := {
                  coeff := fun a => if a = 0 then c else 0
                  support_finite_above := by
                    intro a
                    apply Set.Finite.subset (Set.finite_singleton 0)
                    intro x hx
                    by_contra h
                    simp only [Set.mem_singleton_iff] at h
                    simp [h] at hx
                  abs_summable := by
                    refine ⟨1, zero_lt_one, ?_⟩
                    intro t ht
                    apply summable_of_ne_finset_zero (s := {0})
                    intro a ha
                    simp only [Finset.mem_singleton] at ha
                    simp [ha] }
                refine ⟨f, ?_⟩
                intro t
                simp [Puiseux.eval, f]
              choose C hC using hconst
              have hU : ∀ i : Fin q, u i ∈ kGenerated u v := by
                intro i
                refine ⟨(fun j => C (if j = i then 1 else 0)), (fun _ => C 0), ?_⟩
                apply Filter.Eventually.of_forall
                intro t
                simp only [hC]
                refine ⟨?_, by simp, ?_, ?_⟩
                · intro j
                  split_ifs <;> norm_num
                · simp
                · intro k
                  simp
              have hUevent : ∀ᶠ t : ℝ in atTop, ∀ i : Fin q,
                  evalFun (u i) t ∈ realPolyhedron A b t := by
                apply (Filter.eventually_all).mpr
                intro i
                have hi : u i ∈ kPolyhedron A b := by rw [hgen]; exact hU i
                exact hi
              have hpointwise : ∀ x : Fin d → Puiseux,
                  (∀ᶠ t in atTop, evalFun x t ∈ realPolyhedron A b t) ↔
                  ∃ α : Fin q → Puiseux, ∃ β : Fin r → Puiseux,
                    ∀ᶠ t in atTop, (∀ i, 0 ≤ (α i).eval t) ∧ (∀ j, 0 ≤ (β j).eval t) ∧
                      (∑ i, (α i).eval t) = 1 ∧
                      ∀ k, (x k).eval t = (∑ i, (α i).eval t * (u i k).eval t) +
                        ∑ j, (β j).eval t * (v j k).eval t := by
                intro x
                change x ∈ kPolyhedron A b ↔ x ∈ kGenerated u v
                rw [hgen]
              have hleading : ∀ (f : Puiseux) (m : ℝ),
                  (∀ a, f.coeff a ≠ 0 → a ≤ m) →
                  Tendsto (fun t : ℝ => f.eval t / t ^ m) atTop (nhds (f.coeff m)) := by
                intro f m hm
                obtain ⟨ρ, hρ, hs⟩ := f.abs_summable
                let R := max ρ 1 + 1
                have hR : 0 < R := by dsimp [R]; positivity
                have hρR : ρ < R := by dsimp [R]; linarith [le_max_left ρ 1]
                let F : ℝ → ℝ → ℝ := fun t a => f.coeff a * t ^ (a - m)
                let B : ℝ → ℝ := fun a => |f.coeff a| * R ^ (a - m)
                have hsum : Summable B := by
                  have hh := (hs R hρR).div_const (R ^ m)
                  have heq : B = (fun a => |f.coeff a| * R ^ a / R ^ m) := by
                    funext a
                    dsimp [B]
                    rw [Real.rpow_sub hR]
                    ring
                  rw [heq]
                  exact hh
                have hlim : ∀ a : ℝ, Tendsto (fun t : ℝ => F t a) atTop
                    (nhds (if a = m then f.coeff m else 0)) := by
                  intro a
                  by_cases ham : a = m
                  · subst a
                    simpa [F] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => f.coeff m) atTop (nhds (f.coeff m)))
                  · by_cases ha : f.coeff a = 0
                    · simpa [F, ha, ham] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))
                    · have hal : a < m := lt_of_le_of_ne (hm a ha) ham
                      have hh := (tendsto_rpow_neg_atTop (sub_pos.mpr hal)).const_mul (f.coeff a)
                      simpa [F, ham, neg_sub] using hh
                have hbound : ∀ᶠ t : ℝ in atTop, ∀ a : ℝ, ‖F t a‖ ≤ B a := by
                  filter_upwards [eventually_ge_atTop R] with t ht a
                  have htpos : 0 < t := hR.trans_le ht
                  dsimp [F, B]
                  rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
                  by_cases ha : f.coeff a = 0
                  · simp [ha]
                  · exact mul_le_mul_of_nonneg_left
                      (Real.rpow_le_rpow_of_nonpos hR ht (sub_nonpos.mpr (hm a ha))) (abs_nonneg _)
                have hlimsum := tendsto_tsum_of_dominated_convergence hsum hlim hbound
                simp only [tsum_ite_eq] at hlimsum
                apply hlimsum.congr'
                filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
                dsimp [F, Puiseux.eval]
                simp_rw [Real.rpow_sub ht, ← mul_div_assoc]
                rw [tsum_div_const]
              have hmax : ∀ f : Puiseux, (∃ a, f.coeff a ≠ 0) →
                  ∃ m, f.coeff m ≠ 0 ∧ ∀ a, f.coeff a ≠ 0 → a ≤ m := by
                intro f ⟨a, ha⟩
                obtain ⟨m, hm, hmax⟩ := Set.exists_max_image
                  {x : ℝ | a ≤ x ∧ f.coeff x ≠ 0} id (f.support_finite_above a) ⟨a, le_rfl, ha⟩
                refine ⟨m, hm.2, ?_⟩
                intro x hx
                by_cases hax : a ≤ x
                · exact hmax x ⟨hax, hx⟩
                · exact (le_of_not_ge hax).trans hm.1
              have hsign : ∀ f : Puiseux,
                  (∀ᶠ t in atTop, f.eval t = 0) ∨
                  (∀ᶠ t in atTop, 0 < f.eval t) ∨ (∀ᶠ t in atTop, f.eval t < 0) := by
                intro f
                by_cases hz : ∃ a, f.coeff a ≠ 0
                · obtain ⟨m, hm, htop⟩ := hmax f hz
                  have hl := hleading f m htop
                  rcases lt_or_gt_of_ne hm with hneg | hpos
                  · right; right
                    filter_upwards [hl.eventually (gt_mem_nhds hneg), eventually_gt_atTop (0 : ℝ)] with t ht htpos
                    have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos htpos m)).mp ht
                    simpa using hh
                  · right; left
                    filter_upwards [hl.eventually (lt_mem_nhds hpos), eventually_gt_atTop (0 : ℝ)] with t ht htpos
                    have hh := (lt_div_iff₀ (Real.rpow_pos_of_pos htpos m)).mp ht
                    simpa using hh
                · left
                  push_neg at hz
                  exact Filter.Eventually.of_forall (fun t => by simp [Puiseux.eval, hz])
              have hfamily_full : ∀ (ι : Type) (c e : ι → ℝ),
                  (∀ a : ℝ, {i : ι | a ≤ e i ∧ c i ≠ 0}.Finite) →
                  (∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, ρ < t → Summable (fun i => |c i| * t ^ e i)) →
                  ∃ f : Puiseux, (∀ x, f.coeff x = ∑' i : e ⁻¹' {x}, c i) ∧
                    ∀ᶠ t in atTop, f.eval t = ∑' i, c i * t ^ e i := by
                intro ι c e hfin habs
                obtain ⟨ρ, hρ, hs⟩ := habs
                let a : ℝ → ℝ := fun x => ∑' i : e ⁻¹' {x}, c i
                have hgroup : ∀ t : ℝ, ∀ x : ℝ,
                    a x * t ^ x = ∑' i : e ⁻¹' {x}, c i * t ^ e i := by
                  intro t x
                  rw [← tsum_mul_right]
                  apply tsum_congr
                  intro i
                  have hi : e i = x := i.property
                  rw [hi]
                have hfam : ∀ t : ℝ, ρ < t → Summable (fun x => |a x| * t ^ x) := by
                  intro t ht
                  have htpos := hρ.trans ht
                  have hnonneg : ∀ i, 0 ≤ |c i| * t ^ e i := fun i => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htpos.le _)
                  have hh := ((hs t ht).hasSum.tsum_fiberwise e).summable
                  apply hh.of_norm_bounded
                  intro x
                  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.rpow_pos_of_pos htpos x)]
                  calc
                    |a x| * t ^ x = |∑' i : e ⁻¹' {x}, c i * t ^ e i| := by
                      rw [← hgroup, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos x)]
                    _ ≤ ∑' i : e ⁻¹' {x}, |c i * t ^ e i| := by
                      have hnorm : Summable (fun i : e ⁻¹' {x} => ‖c i * t ^ e i‖) := by
                        simpa only [Function.comp_def, Real.norm_eq_abs, abs_mul,
                            abs_of_pos (Real.rpow_pos_of_pos htpos _)]
                          using! (hs t ht).subtype (e ⁻¹' {x})
                      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hnorm
                    _ = ∑' i : e ⁻¹' {x}, |c i| * t ^ e i := by
                      apply tsum_congr
                      intro i
                      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
                let f : Puiseux := {
                  coeff := a
                  support_finite_above := by
                    intro x
                    apply ((hfin x).image e).subset
                    intro y hy
                    have hn : ∃ i : e ⁻¹' {y}, c i ≠ 0 := by
                      by_contra hn
                      push Not at hn
                      have hz : a y = 0 := by simp [a, hn]
                      exact hy.2 hz
                    obtain ⟨i, hi⟩ := hn
                    have hieq : e (i : ι) = y := i.property
                    exact ⟨i, ⟨by rw [hieq]; exact hy.1, hi⟩, hieq⟩
                  abs_summable := ⟨ρ, hρ, hfam⟩ }
                refine ⟨f, (fun x => rfl), ?_⟩
                filter_upwards [eventually_gt_atTop ρ] with t ht
                have htpos := hρ.trans ht
                have hsum : Summable (fun i => c i * t ^ e i) := by
                  apply (hs t ht).of_norm_bounded
                  intro i
                  simp [abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
                have hh := (hsum.hasSum.tsum_fiberwise e).tsum_eq
                simpa only [Puiseux.eval, f, ← hgroup] using hh
              have hfamily : ∀ (ι : Type) (c e : ι → ℝ),
                  (∀ a : ℝ, {i : ι | a ≤ e i ∧ c i ≠ 0}.Finite) →
                  (∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, ρ < t → Summable (fun i => |c i| * t ^ e i)) →
                  ∃ f : Puiseux, ∀ᶠ t in atTop, f.eval t = ∑' i, c i * t ^ e i := by
                intro ι c e hfin habs
                obtain ⟨f, hf, he⟩ := hfamily_full ι c e hfin habs
                exact ⟨f, he⟩
              have hupper : ∀ f : Puiseux, ∃ m : ℝ, ∀ a, f.coeff a ≠ 0 → a ≤ m := by
                intro f
                by_cases h : ∃ a, f.coeff a ≠ 0
                · obtain ⟨m, hm, h⟩ := hmax f h
                  exact ⟨m, h⟩
                · push Not at h
                  exact ⟨0, fun a ha => (ha (h a)).elim⟩
              have hsum_eval : ∀ f : Puiseux, ∀ᶠ t in atTop,
                  Summable (fun a => f.coeff a * t ^ a) := by
                intro f
                obtain ⟨ρ, hρ, hs⟩ := f.abs_summable
                filter_upwards [eventually_gt_atTop ρ] with t ht
                apply (hs t ht).of_norm_bounded
                intro a
                simp [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hρ.trans ht) _)]
              have hadd : ∀ f g : Puiseux, ∃ h : Puiseux,
                  ∀ᶠ t in atTop, h.eval t = f.eval t + g.eval t := by
                intro f g
                obtain ⟨ρf, hρf, hsf⟩ := f.abs_summable
                obtain ⟨ρg, hρg, hsg⟩ := g.abs_summable
                let h : Puiseux := {
                  coeff := fun a => f.coeff a + g.coeff a
                  support_finite_above := by
                    intro a
                    apply ((f.support_finite_above a).union (g.support_finite_above a)).subset
                    intro x hx
                    by_cases hf : f.coeff x = 0
                    · right
                      exact ⟨hx.1, by simpa [hf] using hx.2⟩
                    · exact Or.inl ⟨hx.1, hf⟩
                  abs_summable := by
                    refine ⟨max ρf ρg, lt_max_of_lt_left hρf, ?_⟩
                    intro t ht
                    have htpos : 0 < t := hρf.trans (lt_of_le_of_lt (le_max_left _ _) ht)
                    apply ((hsf t (lt_of_le_of_lt (le_max_left _ _) ht)).add
                      (hsg t (lt_of_le_of_lt (le_max_right _ _) ht))).of_norm_bounded
                    intro a
                    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
                    calc
                      _ ≤ (|f.coeff a| + |g.coeff a|) * t ^ a := by
                        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (Real.rpow_nonneg htpos.le _)
                      _ = _ := by ring }
                refine ⟨h, ?_⟩
                filter_upwards [hsum_eval f, hsum_eval g] with t hf hg
                simpa only [Puiseux.eval, h, add_mul] using hf.tsum_add hg
              have hmul : ∀ f g : Puiseux, ∃ h : Puiseux,
                  ∀ᶠ t in atTop, h.eval t = f.eval t * g.eval t := by
                intro f g
                obtain ⟨m, hm⟩ := hupper f
                obtain ⟨n, hn⟩ := hupper g
                obtain ⟨ρf, hρf, hsf⟩ := f.abs_summable
                obtain ⟨ρg, hρg, hsg⟩ := g.abs_summable
                obtain ⟨h, hh⟩ := hfamily (ℝ × ℝ)
                  (fun z => f.coeff z.1 * g.coeff z.2) (fun z => z.1 + z.2) (by
                    intro a
                    apply ((f.support_finite_above (a - n)).prod (g.support_finite_above (a - m))).subset
                    intro z hz
                    have hf : f.coeff z.1 ≠ 0 := left_ne_zero_of_mul hz.2
                    have hg : g.coeff z.2 ≠ 0 := right_ne_zero_of_mul hz.2
                    exact ⟨⟨by linarith [hn z.2 hg, hz.1], hf⟩, ⟨by linarith [hm z.1 hf, hz.1], hg⟩⟩) (by
                    refine ⟨max ρf ρg, lt_max_of_lt_left hρf, ?_⟩
                    intro t ht
                    have htpos : 0 < t := hρf.trans (lt_of_le_of_lt (le_max_left _ _) ht)
                    have hh := (hsf t (lt_of_le_of_lt (le_max_left _ _) ht)).mul_of_nonneg
                      (hsg t (lt_of_le_of_lt (le_max_right _ _) ht))
                      (fun a => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htpos.le _))
                      (fun a => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg htpos.le _))
                    apply hh.congr
                    intro z
                    rw [abs_mul, Real.rpow_add htpos]
                    ring)
                refine ⟨h, ?_⟩
                filter_upwards [hh, hsum_eval f, hsum_eval g, eventually_gt_atTop (0 : ℝ)] with t hh hf hg ht
                rw [hh, Puiseux.eval, Puiseux.eval, tsum_mul_tsum_of_summable_norm hf.norm hg.norm]
                apply tsum_congr
                intro z
                rw [Real.rpow_add ht]
                ring
              have htuple : ∀ (a : ℝ → ℝ), Summable a → ∀ n : ℕ,
                  HasSum (fun x : Fin n → ℝ => ∏ i, a (x i)) ((∑' x, a x) ^ n) := by
                intro a ha n
                induction n with
                | zero =>
                  simpa using (hasSum_fintype (fun x : Fin 0 → ℝ => ∏ i, a (x i)))
                | succ n ih =>
                  have hpairSum : Summable (fun z : ℝ × (Fin n → ℝ) => a z.1 * ∏ i, a (z.2 i)) :=
                    summable_mul_of_summable_norm (R := ℝ) (f := a)
                      (g := fun x : Fin n → ℝ => ∏ i, a (x i)) ha.norm ih.summable.norm
                  have hp : HasSum (fun z : ℝ × (Fin n → ℝ) => a z.1 * ∏ i, a (z.2 i))
                      ((∑' x, a x) * (∑' x, a x) ^ n) :=
                    by simpa only using! (ha.hasSum.mul ih hpairSum)
                  apply (Fin.consEquiv (fun _ : Fin (n + 1) => ℝ)).hasSum_iff.mp
                  simpa [Function.comp_def, Fin.prod_univ_succ, pow_succ, mul_comm] using hp
              have hdecay : ∀ f : Puiseux, (∀ a, f.coeff a ≠ 0 → a < 0) →
                  Tendsto (fun t : ℝ => f.eval t) atTop (nhds 0) := by
                intro f hf
                by_cases hz : ∃ a, f.coeff a ≠ 0
                · obtain ⟨m, hm, htop⟩ := hmax f hz
                  have hmneg := hf m hm
                  have hl := (hleading f m htop).mul (tendsto_rpow_neg_atTop (neg_pos.mpr hmneg))
                  simp only [neg_neg, mul_zero] at hl
                  apply hl.congr'
                  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
                  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos ht m).ne'
                · push Not at hz
                  simpa [Puiseux.eval, hz] using
                    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0))
              have hwords : ∀ (a : ℝ → ℝ), Summable a → (∑' x, |a x|) < 1 →
                  Summable (fun z : Σ n : ℕ, Fin n → ℝ => |∏ i, a (z.2 i)|) ∧
                  (∑' z : Σ n : ℕ, Fin n → ℝ, ∏ i, a (z.2 i)) = (1 - ∑' x, a x)⁻¹ := by
                intro a ha hsmall
                have habs : Summable (fun x => |a x|) := by simpa only [Real.norm_eq_abs] using ha.norm
                have hnonneg : 0 ≤ ∑' x, |a x| := tsum_nonneg (fun x => abs_nonneg _)
                have hga := summable_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hnonneg])
                have hSigma : Summable (fun z : Σ n : ℕ, Fin n → ℝ => ∏ i, |a (z.2 i)|) := by
                  apply (summable_sigma_of_nonneg (fun z => Finset.prod_nonneg (fun i hi => abs_nonneg _))).mpr
                  refine ⟨fun n => (htuple _ habs n).summable, ?_⟩
                  have heq : (fun n => ∑' x : Fin n → ℝ, ∏ i, |a (x i)|) =
                      (fun n => (∑' x, |a x|) ^ n) := by
                    funext n
                    exact (htuple _ habs n).tsum_eq
                  rw [heq]
                  exact hga
                have hSigmaAbs : Summable (fun z : Σ n : ℕ, Fin n → ℝ => |∏ i, a (z.2 i)|) := by
                  simpa only [Finset.abs_prod] using hSigma
                refine ⟨hSigmaAbs, ?_⟩
                have hSigmaSigned : Summable (fun z : Σ n : ℕ, Fin n → ℝ => ∏ i, a (z.2 i)) := by
                  apply hSigmaAbs.of_norm_bounded
                  intro z
                  rw [Real.norm_eq_abs]
                rw [hSigmaSigned.tsum_sigma]
                have heq : (fun n => ∑' x : Fin n → ℝ, ∏ i, a (x i)) =
                    (fun n => (∑' x, a x) ^ n) := by
                  funext n
                  exact (htuple _ ha n).tsum_eq
                rw [heq]
                apply tsum_geometric_of_abs_lt_one
                have hnorm := norm_tsum_le_tsum_norm ha.norm
                simp only [Real.norm_eq_abs] at hnorm
                exact hnorm.trans_lt hsmall
              have hgeom : ∀ f : Puiseux, (∀ a, f.coeff a ≠ 0 → a < 0) →
                  ∃ g : Puiseux, ∀ᶠ t in atTop, g.eval t = (1 - f.eval t)⁻¹ := by
                intro f hf
                by_cases hz : ∃ a, f.coeff a ≠ 0
                · obtain ⟨m, hm, htop⟩ := hmax f hz
                  have hmneg := hf m hm
                  let af : Puiseux := {
                    coeff := fun a => |f.coeff a|
                    support_finite_above := by
                      intro a
                      simpa only [abs_ne_zero] using f.support_finite_above a
                    abs_summable := by simpa only [abs_abs] using f.abs_summable }
                  have haf : ∀ a, af.coeff a ≠ 0 → a < 0 := by
                    intro a ha
                    apply hf a
                    simpa only [af, abs_ne_zero] using ha
                  obtain ⟨ρ, hρ, hs⟩ := f.abs_summable
                  obtain ⟨R, hR, hsmallR⟩ := ((eventually_gt_atTop (max ρ 1)).and
                    ((hdecay af haf).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))).exists
                  have hρR : ρ < R := (le_max_left _ _).trans_lt hR
                  have hRpos : 0 < R := hρ.trans hρR
                  change (∑' a, |f.coeff a| * R ^ a) < 1 at hsmallR
                  have hsmall : ∀ t : ℝ, R < t → (∑' a, |f.coeff a| * t ^ a) < 1 := by
                    intro t ht
                    apply lt_of_le_of_lt _ hsmallR
                    apply (hs t (hρR.trans ht)).tsum_le_tsum _ (hs R hρR)
                    intro a
                    by_cases ha : f.coeff a = 0
                    · simp [ha]
                    · exact mul_le_mul_of_nonneg_left
                        (Real.rpow_le_rpow_of_nonpos hRpos ht.le (hf a ha).le) (abs_nonneg _)
                  let c : (Σ n : ℕ, Fin n → ℝ) → ℝ := fun z => ∏ i, f.coeff (z.2 i)
                  let e : (Σ n : ℕ, Fin n → ℝ) → ℝ := fun z => ∑ i, z.2 i
                  have hfinite : ∀ a : ℝ, {z | a ≤ e z ∧ c z ≠ 0}.Finite := by
                    intro a
                    obtain ⟨N, hN⟩ := exists_nat_gt (a / m)
                    have htuples (n : Fin N) : {x : Fin n.val → ℝ | ∀ i,
                        a ≤ x i ∧ f.coeff (x i) ≠ 0}.Finite :=
                      Set.Finite.pi' (fun i => f.support_finite_above a)
                    have hfin := Set.finite_iUnion (fun n : Fin N => (htuples n).image (fun x : Fin n.val → ℝ => (⟨n.val, x⟩ : Σ n : ℕ, Fin n → ℝ)))
                    apply hfin.subset
                    intro z hz
                    have hcoef : ∀ i : Fin z.1, f.coeff (z.2 i) ≠ 0 := by
                      intro i
                      exact Finset.prod_ne_zero_iff.mp hz.2 i (Finset.mem_univ i)
                    have hbound : e z ≤ (z.1 : ℝ) * m := by
                      calc
                        e z ≤ ∑ i : Fin z.1, m := Finset.sum_le_sum (fun i hi => htop _ (hcoef i))
                        _ = _ := by simp
                    have hn : z.1 < N := by
                      have hh : (z.1 : ℝ) ≤ a / m := (le_div_iff_of_neg hmneg).mpr (hz.1.trans hbound)
                      exact_mod_cast hh.trans_lt hN
                    apply Set.mem_iUnion.mpr
                    refine ⟨⟨z.1, hn⟩, ?_⟩
                    refine ⟨z.2, ?_, rfl⟩
                    intro i
                    refine ⟨?_, hcoef i⟩
                    have hsnonpos : ∑ k ∈ Finset.univ.erase i, z.2 k ≤ 0 := by
                      apply Finset.sum_nonpos
                      intro k hk
                      exact (hf _ (hcoef k)).le
                    have heq := Finset.sum_erase_add Finset.univ (fun k => z.2 k) (Finset.mem_univ i)
                    have haz : a ≤ ∑ k, z.2 k := hz.1
                    linarith
                  have habs : ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, ρ < t →
                      Summable (fun z => |c z| * t ^ e z) := by
                    refine ⟨R, hRpos, ?_⟩
                    intro t ht
                    have htpos := hRpos.trans ht
                    have hnorm : Summable (fun a => ‖f.coeff a * t ^ a‖) := by
                      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
                        using! hs t (hρR.trans ht)
                    have hh := (hwords (fun a => f.coeff a * t ^ a) hnorm.of_norm (by
                      simpa only [abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)] using hsmall t ht)).1
                    apply hh.congr
                    intro z
                    simp only [c, e, Finset.abs_prod, Finset.prod_mul_distrib,
                      Real.rpow_sum_of_pos htpos, abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
                  obtain ⟨g, hg⟩ := hfamily _ c e hfinite habs
                  refine ⟨g, ?_⟩
                  filter_upwards [hg, eventually_gt_atTop R, hsum_eval f] with t hgt ht hst
                  have htpos := hRpos.trans ht
                  rw [hgt]
                  have hh := (hwords (fun a => f.coeff a * t ^ a) hst (by
                    simpa only [abs_mul, abs_of_pos (Real.rpow_pos_of_pos htpos _)] using hsmall t ht)).2
                  change (∑' i, c i * t ^ e i) = (1 - ∑' a, f.coeff a * t ^ a)⁻¹
                  rw [← hh]
                  apply tsum_congr
                  intro z
                  simp only [c, e, Finset.prod_mul_distrib, Real.rpow_sum_of_pos htpos]
                · push Not at hz
                  refine ⟨C 1, Filter.Eventually.of_forall (fun t => ?_)⟩
                  rw [hC]
                  simp [Puiseux.eval, hz]
              have htail : ∀ (f : Puiseux) (m : ℝ), f.coeff m ≠ 0 →
                  (∀ a, f.coeff a ≠ 0 → a ≤ m) →
                  ∃ g : Puiseux, (∀ a, g.coeff a ≠ 0 → a < 0) ∧
                    ∀ᶠ t in atTop, g.eval t = 1 - f.eval t / (f.coeff m * t ^ m) := by
                intro f m hm htop
                let c : ℝ → ℝ := fun a => if a = m then 0 else -f.coeff a / f.coeff m
                let e : ℝ → ℝ := fun a => a - m
                obtain ⟨ρ, hρ, hs⟩ := f.abs_summable
                have hcfin : ∀ a : ℝ, {i | a ≤ e i ∧ c i ≠ 0}.Finite := by
                  intro a
                  apply (f.support_finite_above (a + m)).subset
                  intro x hx
                  refine ⟨by dsimp [e] at hx; linarith [hx.1], ?_⟩
                  by_contra hzero
                  simp [c, hzero] at hx
                have hcsum : ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, ρ < t →
                    Summable (fun a => |c a| * t ^ e a) := by
                  refine ⟨ρ, hρ, ?_⟩
                  intro t ht
                  have htpos := hρ.trans ht
                  have hh := (hs t ht).mul_right (|f.coeff m|⁻¹ / t ^ m)
                  apply hh.of_norm_bounded
                  intro a
                  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos (Real.rpow_pos_of_pos htpos _)]
                  dsimp [c, e]
                  by_cases ham : a = m
                  · simp only [ham, ite_true, abs_zero, zero_mul]
                    positivity
                  · rw [if_neg ham, abs_div, abs_neg, Real.rpow_sub htpos]
                    exact le_of_eq (by ring)
                obtain ⟨g, hgc, hge⟩ := hfamily_full ℝ c e hcfin hcsum
                refine ⟨g, ?_, ?_⟩
                · intro a ha
                  by_contra haneg
                  have hapos : 0 ≤ a := le_of_not_gt haneg
                  have hzero : ∀ i : e ⁻¹' {a}, c i = 0 := by
                    intro i
                    by_cases him : (i : ℝ) = m
                    · simp [c, him]
                    · have hieq : (i : ℝ) - m = a := i.property
                      have hfzero : f.coeff i = 0 := by
                        by_contra hfne
                        have hile := htop i hfne
                        have hilt : (i : ℝ) < m := lt_of_le_of_ne hile him
                        linarith
                      simp [c, hfzero]
                  have hz : g.coeff a = 0 := by simp only [hgc, hzero, tsum_zero]
                  exact ha hz
                · filter_upwards [hge, hsum_eval f, eventually_gt_atTop (0 : ℝ)] with t hget hst ht
                  let F : ℝ → ℝ := fun a => -f.coeff a / f.coeff m * t ^ (a - m)
                  have hFsum : Summable F := by
                    have hh := hst.mul_left (-(f.coeff m)⁻¹ / t ^ m)
                    apply hh.congr
                    intro a
                    dsimp [F]
                    rw [Real.rpow_sub ht]
                    ring
                  have hwhole : (∑' a, F a) = -f.eval t / (f.coeff m * t ^ m) := by
                    calc
                      (∑' a, F a) = ∑' a, -(f.coeff a * t ^ a) / (f.coeff m * t ^ m) := by
                        apply tsum_congr
                        intro a
                        dsimp [F]
                        rw [Real.rpow_sub ht]
                        ring
                      _ = _ := by rw [tsum_div_const, tsum_neg]; rfl
                  have hsplit : (∑' a, F a) = -1 + ∑' a, if a = m then 0 else F a := by
                    simpa only [F, sub_self, Real.rpow_zero, mul_one, neg_div, div_self hm]
                      using hFsum.tsum_eq_add_tsum_ite m
                  have heq : (∑' a, c a * t ^ e a) = ∑' a, if a = m then 0 else F a := by
                    apply tsum_congr
                    intro a
                    by_cases ham : a = m <;> simp [c, e, F, ham]
                  rw [hget, heq]
                  rw [neg_div] at hwhole
                  linarith only [hwhole, hsplit]
              have hmono : ∀ a : ℝ, ∃ f : Puiseux, ∀ t : ℝ, f.eval t = t ^ a := by
                intro a
                let f : Puiseux := {
                  coeff := fun x => if x = a then 1 else 0
                  support_finite_above := by
                    intro c
                    apply (Set.finite_singleton a).subset
                    intro x hx
                    by_contra h
                    have hxne : x ≠ a := h
                    simp [hxne] at hx
                  abs_summable := by
                    refine ⟨1, zero_lt_one, ?_⟩
                    intro t ht
                    apply summable_of_ne_finset_zero (s := {a})
                    intro x hx
                    simp only [Finset.mem_singleton] at hx
                    simp [hx] }
                refine ⟨f, ?_⟩
                intro t
                simp [Puiseux.eval, f]
              choose M hM using hmono
              have hneg : ∀ f : Puiseux, ∃ h : Puiseux,
                  ∀ᶠ t in atTop, h.eval t = -f.eval t := by
                intro f
                obtain ⟨h, hh⟩ := hmul (C (-1)) f
                exact ⟨h, hh.mono (fun t ht => by simpa [hC] using ht)⟩
              have hinv : ∀ f : Puiseux, ∃ g : Puiseux,
                  ∀ᶠ t in atTop, g.eval t = (f.eval t)⁻¹ := by
                intro f
                by_cases hz : ∃ a, f.coeff a ≠ 0
                · obtain ⟨m, hm, htop⟩ := hmax f hz
                  obtain ⟨g, hgneg, hge⟩ := htail f m hm htop
                  obtain ⟨k, hk⟩ := hgeom g hgneg
                  obtain ⟨z, hz⟩ := hmul (C (f.coeff m)⁻¹) (M (-m))
                  obtain ⟨w, hw⟩ := hmul z k
                  refine ⟨w, ?_⟩
                  filter_upwards [hge, hk, hz, hw, eventually_gt_atTop (0 : ℝ)] with t hgt hkt hzt hwt ht
                  rw [hwt, hzt, hC, hM, hkt, hgt]
                  rw [show 1 - (1 - f.eval t / (f.coeff m * t ^ m)) =
                    f.eval t / (f.coeff m * t ^ m) by ring]
                  rw [inv_div, Real.rpow_neg ht.le]
                  have htp : t ^ m ≠ 0 := (Real.rpow_pos_of_pos ht m).ne'
                  simp only [div_eq_mul_inv]
                  rw [show (f.coeff m)⁻¹ * (t ^ m)⁻¹ *
                    (f.coeff m * t ^ m * (f.eval t)⁻¹) =
                    ((f.coeff m)⁻¹ * f.coeff m) * ((t ^ m)⁻¹ * t ^ m) * (f.eval t)⁻¹ by ring]
                  simp [hm, htp]
                · push Not at hz
                  exact ⟨C 0, Filter.Eventually.of_forall (fun t => by rw [hC]; simp [Puiseux.eval, hz])⟩
              have hfinSum : ∀ {ι : Type} [Fintype ι] (f : ι → Puiseux),
                  ∃ h : Puiseux, ∀ᶠ t in atTop, h.eval t = ∑ i, (f i).eval t := by
                intro ι inst f
                have hh : ∀ s : Finset ι, ∃ h : Puiseux,
                    ∀ᶠ t in atTop, h.eval t = ∑ i ∈ s, (f i).eval t := by
                  intro s
                  induction s using Finset.induction_on with
                  | empty => exact ⟨C 0, Filter.Eventually.of_forall (fun t => by simp [hC])⟩
                  | @insert i s hi ih =>
                    obtain ⟨g, hg⟩ := ih
                    obtain ⟨h, hh⟩ := hadd (f i) g
                    refine ⟨h, ?_⟩
                    filter_upwards [hg, hh] with t ht hht
                    simpa [Finset.sum_insert hi, ht] using hht
                simpa using hh Finset.univ
              have hdot : ∀ {ι : Type} [Fintype ι] (f g : ι → Puiseux),
                  ∃ h : Puiseux, ∀ᶠ t in atTop, h.eval t = ∑ i, (f i).eval t * (g i).eval t := by
                intro ι inst f g
                choose k hk using (fun i => hmul (f i) (g i))
                obtain ⟨h, hh⟩ := hfinSum k
                refine ⟨h, ?_⟩
                filter_upwards [hh, Filter.eventually_all.mpr hk] with t ht hkt
                simp only [hkt] at ht
                exact ht
              have hdom : ∀ f g : Puiseux,
                  (∀ a : ℝ, ∀ᶠ t in atTop, t ^ a * f.eval t ≤ g.eval t) →
                  ∀ᶠ t in atTop, f.eval t ≤ 0 := by
                intro f g h
                by_cases hz : ∃ a, f.coeff a ≠ 0
                · obtain ⟨m, hm, htop⟩ := hmax f hz
                  obtain ⟨n, hn⟩ := hupper g
                  have hl := hleading f m htop
                  have hr := (hleading g n hn).mul (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 by norm_num))
                  simp only [mul_zero] at hr
                  have hevent : ∀ᶠ t in atTop,
                      f.eval t / t ^ m ≤ (g.eval t / t ^ n) * t ^ (-1 : ℝ) := by
                    filter_upwards [h (n - m + 1), eventually_gt_atTop (0 : ℝ)] with t ht htpos
                    have hp : 0 < t ^ (n + 1) := Real.rpow_pos_of_pos htpos _
                    have hh := (div_le_div_iff_of_pos_right hp).mpr ht
                    have heq : t ^ (n - m + 1) / t ^ (n + 1) = (t ^ m)⁻¹ := by
                      rw [← Real.rpow_sub htpos]
                      convert Real.rpow_neg htpos.le m using 1 <;> congr 1 <;> ring
                    have heq' : (t ^ (n + 1))⁻¹ = (t ^ n)⁻¹ * t ^ (-1 : ℝ) := by
                      rw [Real.rpow_add htpos, Real.rpow_one, Real.rpow_neg_one]
                      simp [mul_comm]
                    calc
                      f.eval t / t ^ m = f.eval t * (t ^ (n - m + 1) / t ^ (n + 1)) := by
                        rw [heq]; rfl
                      _ = t ^ (n - m + 1) * f.eval t / t ^ (n + 1) := by ring
                      _ ≤ g.eval t / t ^ (n + 1) := hh
                      _ = (g.eval t / t ^ n) * t ^ (-1 : ℝ) := by
                        simp only [div_eq_mul_inv, heq']
                        ring
                  have hc : f.coeff m ≤ 0 := le_of_tendsto_of_tendsto hl hr hevent
                  have hcneg : f.coeff m < 0 := lt_of_le_of_ne hc hm
                  filter_upwards [hl.eventually (gt_mem_nhds hcneg), eventually_gt_atTop (0 : ℝ)] with t ht htpos
                  have hh := (div_lt_iff₀ (Real.rpow_pos_of_pos htpos m)).mp ht
                  simpa using hh.le
                · push Not at hz
                  exact Filter.Eventually.of_forall (fun t => by simp [Puiseux.eval, hz])
              have hVevent : q ≠ 0 → ∀ᶠ t in atTop, ∀ j : Fin r, ∀ i : Fin p,
                  ∑ k, (A i k).eval t * (v j k).eval t ≤ 0 := by
                intro hq
                let i₀ : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
                apply Filter.eventually_all.mpr
                intro j
                apply Filter.eventually_all.mpr
                intro i
                obtain ⟨f, hf⟩ := hdot (A i) (v j)
                obtain ⟨g, hg⟩ := hdot (A i) (u i₀)
                obtain ⟨ng, hng⟩ := hneg g
                obtain ⟨s, hs⟩ := hadd (b i) ng
                have hscaled : ∀ a : ℝ, ∀ᶠ t in atTop, t ^ a * f.eval t ≤ s.eval t := by
                  intro a
                  choose z hz using (fun k => hmul (M a) (v j k))
                  choose x hx using (fun k => hadd (u i₀ k) (z k))
                  have hxeval : ∀ᶠ t in atTop, ∀ k,
                      (x k).eval t = (u i₀ k).eval t + t ^ a * (v j k).eval t := by
                    filter_upwards [Filter.eventually_all.mpr hz, Filter.eventually_all.mpr hx] with t hzt hxt k
                    rw [hxt, hzt, hM]
                  have hxgen : x ∈ kGenerated u v := by
                    refine ⟨(fun l => C (if l = i₀ then 1 else 0)),
                      (fun l => if l = j then M a else C 0), ?_⟩
                    filter_upwards [hxeval, eventually_gt_atTop (0 : ℝ)] with t hxt ht
                    refine ⟨?_, ?_, ?_, ?_⟩
                    · intro l
                      simp only [hC]
                      split_ifs <;> norm_num
                    · intro l
                      by_cases hl : l = j
                      · simp [hl, hM, Real.rpow_nonneg ht.le]
                      · simp [hl, hC]
                    · simp [hC]
                    · intro k
                      rw [hxt]
                      have hβ : ∀ l : Fin r, (if l = j then M a else C 0).eval t =
                          if l = j then t ^ a else 0 := by
                        intro l
                        split_ifs <;> simp [hM, hC]
                      simp_rw [hβ]
                      simp [hC, ite_mul]
                  have hxpoly : x ∈ kPolyhedron A b := by rw [hgen]; exact hxgen
                  filter_upwards [hxpoly, hxeval, hf, hg, hng, hs] with t hpt hxt hft hgt hngt hst
                  have heq : (∑ k, (A i k).eval t * (x k).eval t) = g.eval t + t ^ a * f.eval t := by
                    rw [hft, hgt]
                    simp_rw [hxt, mul_add, Finset.sum_add_distrib]
                    congr 1
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k hk
                    ring
                  have hineq := hpt i
                  change (∑ k, (A i k).eval t * (x k).eval t) ≤ (b i).eval t at hineq
                  rw [heq] at hineq
                  linarith
                filter_upwards [hdom f s hscaled, hf] with t ht hft
                simpa only [hft] using ht
              have hinclusion : ∀ᶠ t in atTop,
                  realGenerated (fun i => evalFun (u i) t) (fun j => evalFun (v j) t) ⊆
                    realPolyhedron A b t := by
                by_cases hq : q = 0
                · subst q
                  apply Filter.Eventually.of_forall
                  intro t x hx
                  obtain ⟨α, β, ha, hb, hs, he⟩ := hx
                  simp at hs
                · filter_upwards [hUevent, hVevent hq] with t hut hvt
                  intro x hx
                  obtain ⟨α, β, ha, hb, hs, he⟩ := hx
                  intro i
                  have hu : ∀ j : Fin q, ∑ k, (A i k).eval t * (u j k).eval t ≤ (b i).eval t := by
                    intro j
                    exact hut j i
                  have hv := fun j => hvt j i
                  change (∑ k, (A i k).eval t * x k) ≤ (b i).eval t
                  calc
                    (∑ k, (A i k).eval t * x k) =
                        (∑ j, α j * ∑ k, (A i k).eval t * (u j k).eval t) +
                        ∑ j, β j * ∑ k, (A i k).eval t * (v j k).eval t := by
                      simp_rw [he, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
                      congr 1
                      · rw [Finset.sum_comm]
                        apply Finset.sum_congr rfl
                        intro j hj
                        apply Finset.sum_congr rfl
                        intro k hk
                        dsimp [evalFun]
                        ring
                      · rw [Finset.sum_comm]
                        apply Finset.sum_congr rfl
                        intro j hj
                        apply Finset.sum_congr rfl
                        intro k hk
                        dsimp [evalFun]
                        ring
                    _ ≤ (∑ j, α j * (b i).eval t) + ∑ j, β j * 0 := by
                      apply add_le_add
                      · apply Finset.sum_le_sum
                        intro j hj
                        exact mul_le_mul_of_nonneg_left (hu j) (ha j)
                      · apply Finset.sum_le_sum
                        intro j hj
                        exact mul_le_mul_of_nonneg_left (hv j) (hb j)
                    _ = (b i).eval t := by simp [← Finset.sum_mul, hs]
              let LA (κ : Type) [Fintype κ] (f : ℝ → (κ → ℝ) → ℝ) : Prop :=
                ∃ a : κ → Puiseux, ∃ b : Puiseux, ∀ᶠ t in atTop, ∀ x,
                  f t x = (∑ k, (a k).eval t * x k) + b.eval t
              let LD (κ : Type) [Fintype κ] (P : ℝ → (κ → ℝ) → Prop) : Prop :=
                ∃ ι : Type, ∃ inst : Fintype ι, ∃ f : ι → ℝ → (κ → ℝ) → ℝ,
                  (∀ i, LA κ (f i)) ∧ ∃ Φ : (ι → Prop) → Prop, ∀ᶠ t in atTop, ∀ x,
                    P t x ↔ Φ (fun i => f i t x ≤ 0)
              have hLA_congr : ∀ {κ : Type} [Fintype κ] {f g : ℝ → (κ → ℝ) → ℝ},
                  LA κ f → (∀ᶠ t in atTop, ∀ x, g t x = f t x) → LA κ g := by
                intro κ inst f g ⟨a, b, hf⟩ he
                refine ⟨a, b, ?_⟩
                filter_upwards [hf, he] with t hft het x
                rw [het, hft]
              have hLA_const : ∀ {κ : Type} [Fintype κ] (b : Puiseux), LA κ (fun t _ => b.eval t) := by
                intro κ inst b
                exact ⟨(fun _ => C 0), b, Filter.Eventually.of_forall (fun t x => by simp [hC])⟩
              have hLA_coord : ∀ {κ : Type} [Fintype κ] (k : κ), LA κ (fun _ x => x k) := by
                intro κ inst k
                refine ⟨(fun j => C (if j = k then 1 else 0)), C 0, ?_⟩
                exact Filter.Eventually.of_forall (fun t x => by simp [hC, ite_mul])
              have hLA_add : ∀ {κ : Type} [Fintype κ] {f g : ℝ → (κ → ℝ) → ℝ},
                  LA κ f → LA κ g → LA κ (fun t x => f t x + g t x) := by
                intro κ inst f g ⟨a, b, hf⟩ ⟨c, e, hg⟩
                choose z hz using (fun k => hadd (a k) (c k))
                obtain ⟨w, hw⟩ := hadd b e
                refine ⟨z, w, ?_⟩
                filter_upwards [hf, hg, Filter.eventually_all.mpr hz, hw] with t hft hgt hzt hwt x
                rw [hft, hgt, hwt]
                simp_rw [hzt, add_mul, Finset.sum_add_distrib]
                ring
              have hLA_mul : ∀ {κ : Type} [Fintype κ] (a : Puiseux) {f : ℝ → (κ → ℝ) → ℝ},
                  LA κ f → LA κ (fun t x => a.eval t * f t x) := by
                intro κ inst a f ⟨b, c, hf⟩
                choose z hz using (fun k => hmul a (b k))
                obtain ⟨w, hw⟩ := hmul a c
                refine ⟨z, w, ?_⟩
                filter_upwards [hf, Filter.eventually_all.mpr hz, hw] with t hft hzt hwt x
                rw [hft, hwt]
                simp_rw [hzt, mul_add, Finset.mul_sum]
                apply congrArg (fun z => z + a.eval t * c.eval t)
                apply Finset.sum_congr rfl
                intro k hk
                ring
              have hLA_neg : ∀ {κ : Type} [Fintype κ] {f : ℝ → (κ → ℝ) → ℝ},
                  LA κ f → LA κ (fun t x => -f t x) := by
                intro κ inst f hf
                apply hLA_congr (hLA_mul (C (-1)) hf)
                exact Filter.Eventually.of_forall (fun t x => by simp [hC])
              have hLA_sum : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
                  (f : ι → ℝ → (κ → ℝ) → ℝ), (∀ i, LA κ (f i)) →
                  LA κ (fun t x => ∑ i, f i t x) := by
                intro κ ι instκ instι f hf
                have hh : ∀ s : Finset ι, LA κ (fun t x => ∑ i ∈ s, f i t x) := by
                  intro s
                  induction s using Finset.induction_on with
                  | empty =>
                    apply hLA_congr (hLA_const (κ := κ) (C 0))
                    exact Filter.Eventually.of_forall (fun t x => by simp [hC])
                  | @insert i s hi ih =>
                    apply hLA_congr (hLA_add (hf i) ih)
                    exact Filter.Eventually.of_forall (fun t x => by simp [Finset.sum_insert hi])
                simpa using hh Finset.univ
              have hLA_comp : ∀ {κ τ : Type} [Fintype κ] [Fintype τ]
                  {f : ℝ → (τ → ℝ) → ℝ} (y : τ → ℝ → (κ → ℝ) → ℝ),
                  LA τ f → (∀ i, LA κ (y i)) →
                  LA κ (fun t x => f t (fun i => y i t x)) := by
                intro κ τ instκ instτ f y ⟨a, b, hf⟩ hy
                apply hLA_congr (hLA_add
                  (hLA_sum (fun i t x => (a i).eval t * y i t x) (fun i => hLA_mul (a i) (hy i)))
                  (hLA_const b))
                exact hf.mono (fun t ht x => ht (fun i => y i t x))
              have hLD_congr : ∀ {κ : Type} [Fintype κ] {P Q : ℝ → (κ → ℝ) → Prop},
                  LD κ P → (∀ᶠ t in atTop, ∀ x, Q t x ↔ P t x) → LD κ Q := by
                intro κ inst P Q ⟨ι, instι, f, hf, Φ, hΦ⟩ he
                refine ⟨ι, instι, f, hf, Φ, ?_⟩
                filter_upwards [hΦ, he] with t hΦt het x
                exact (het x).trans (hΦt x)
              have hLD_atom : ∀ {κ : Type} [Fintype κ] {f : ℝ → (κ → ℝ) → ℝ},
                  LA κ f → LD κ (fun t x => f t x ≤ 0) := by
                intro κ inst f hf
                exact ⟨Unit, inferInstance, (fun _ => f), (fun _ => hf),
                  (fun P => P ()), Filter.Eventually.of_forall (fun t x => Iff.rfl)⟩
              have hLD_true : ∀ {κ : Type} [Fintype κ], LD κ (fun _ _ => True) := by
                intro κ inst
                exact ⟨Empty, inferInstance, (fun i => Empty.elim i), (fun i => Empty.elim i),
                  (fun _ => True), Filter.Eventually.of_forall (fun t x => Iff.rfl)⟩
              have hLD_not : ∀ {κ : Type} [Fintype κ] {P : ℝ → (κ → ℝ) → Prop},
                  LD κ P → LD κ (fun t x => ¬ P t x) := by
                intro κ inst P ⟨ι, instι, f, hf, Φ, hΦ⟩
                exact ⟨ι, instι, f, hf, (fun Z => ¬ Φ Z), hΦ.mono (fun t ht x => not_congr (ht x))⟩
              have hLD_and : ∀ {κ : Type} [Fintype κ] {P Q : ℝ → (κ → ℝ) → Prop},
                  LD κ P → LD κ Q → LD κ (fun t x => P t x ∧ Q t x) := by
                intro κ inst P Q ⟨ι, instι, f, hf, Φ, hΦ⟩ ⟨τ, instτ, g, hg, Ψ, hΨ⟩
                letI : Fintype ι := instι
                letI : Fintype τ := instτ
                refine ⟨ι ⊕ τ, inferInstance, Sum.elim f g, ?_,
                  (fun Z => Φ (fun i => Z (.inl i)) ∧ Ψ (fun i => Z (.inr i))), ?_⟩
                · intro i
                  cases i with
                  | inl i => exact hf i
                  | inr i => exact hg i
                · filter_upwards [hΦ, hΨ] with t hΦt hΨt x
                  exact and_congr (hΦt x) (hΨt x)
              have hLD_all : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
                  (P : ι → ℝ → (κ → ℝ) → Prop), (∀ i, LD κ (P i)) →
                  LD κ (fun t x => ∀ i, P i t x) := by
                intro κ ι instκ instι P hP
                have hh : ∀ s : Finset ι, LD κ (fun t x => ∀ i ∈ s, P i t x) := by
                  intro s
                  induction s using Finset.induction_on with
                  | empty =>
                    apply hLD_congr (hLD_true (κ := κ))
                    exact Filter.Eventually.of_forall (fun t x => by simp)
                  | @insert i s hi ih =>
                    apply hLD_congr (hLD_and (hP i) ih)
                    exact Filter.Eventually.of_forall (fun t x => by simp)
                simpa using hh Finset.univ
              have hLD_any : ∀ {κ ι : Type} [Fintype κ] [Fintype ι]
                  (P : ι → ℝ → (κ → ℝ) → Prop), (∀ i, LD κ (P i)) →
                  LD κ (fun t x => ∃ i, P i t x) := by
                intro κ ι instκ instι P hP
                apply hLD_congr (hLD_not (hLD_all (fun i t x => ¬ P i t x) (fun i => hLD_not (hP i))))
                exact Filter.Eventually.of_forall (fun t x => by simp)
              have hLD_comp : ∀ {κ τ : Type} [Fintype κ] [Fintype τ]
                  {P : ℝ → (τ → ℝ) → Prop} (y : τ → ℝ → (κ → ℝ) → ℝ),
                  LD τ P → (∀ i, LA κ (y i)) →
                  LD κ (fun t x => P t (fun i => y i t x)) := by
                intro κ τ instκ instτ P y ⟨ι, instι, f, hf, Φ, hΦ⟩ hy
                exact ⟨ι, instι, (fun i t x => f i t (fun j => y j t x)),
                  (fun i => hLA_comp y (hf i) hy), Φ,
                  hΦ.mono (fun t ht x => ht (fun i => y i t x))⟩
              have hsample_order : ∀ {ι : Type} [Fintype ι] (r : ι → ℝ) (y : ℝ),
                  ∃ z : ℝ, (z = 0 ∨ ∃ i, z = r i ∨ z = r i - 1 ∨ z = r i + 1 ∨
                    ∃ j, z = (r i + r j) / 2) ∧
                  ∀ i, (r i ≤ z ↔ r i ≤ y) ∧ (z ≤ r i ↔ y ≤ r i) := by
                intro ι inst r y
                by_cases heq : ∃ i, y = r i
                · obtain ⟨i, hi⟩ := heq
                  exact ⟨y, Or.inr ⟨i, Or.inl hi⟩, fun i => ⟨Iff.rfl, Iff.rfl⟩⟩
                · push Not at heq
                  by_cases hl : ∃ i, r i < y
                  · obtain ⟨i, hi, hmax⟩ := Set.exists_max_image {i | r i < y} r (Set.toFinite _) hl
                    change r i < y at hi
                    by_cases hu : ∃ j, y < r j
                    · obtain ⟨j, hj, hmin⟩ := Set.exists_min_image {j | y < r j} r (Set.toFinite _) hu
                      change y < r j at hj
                      refine ⟨(r i + r j) / 2, Or.inr ⟨i, Or.inr (Or.inr (Or.inr ⟨j, rfl⟩))⟩, ?_⟩
                      intro k
                      by_cases hk : r k < y
                      · have hkmax := hmax k hk
                        have hkz : r k < (r i + r j) / 2 := by linarith
                        exact ⟨iff_of_true hkz.le hk.le, iff_of_false (not_le_of_gt hkz) (not_le_of_gt hk)⟩
                      · have hky : y < r k := lt_of_le_of_ne (le_of_not_gt hk) (heq k)
                        have hkmin := hmin k hky
                        have hzk : (r i + r j) / 2 < r k := by linarith
                        exact ⟨iff_of_false (not_le_of_gt hzk) (not_le_of_gt hky), iff_of_true hzk.le hky.le⟩
                    · push Not at hu
                      refine ⟨r i + 1, Or.inr ⟨i, Or.inr (Or.inr (Or.inl rfl))⟩, ?_⟩
                      intro k
                      have hky : r k < y := lt_of_le_of_ne (hu k) (Ne.symm (heq k))
                      have hkmax := hmax k hky
                      have hkz : r k < r i + 1 := by linarith
                      exact ⟨iff_of_true hkz.le hky.le, iff_of_false (not_le_of_gt hkz) (not_le_of_gt hky)⟩
                  · push Not at hl
                    by_cases hu : ∃ j, y < r j
                    · obtain ⟨j, hj, hmin⟩ := Set.exists_min_image {j | y < r j} r (Set.toFinite _) hu
                      change y < r j at hj
                      refine ⟨r j - 1, Or.inr ⟨j, Or.inr (Or.inl rfl)⟩, ?_⟩
                      intro k
                      have hky : y < r k := lt_of_le_of_ne (hl k) (heq k)
                      have hkmin := hmin k hky
                      have hzk : r j - 1 < r k := by linarith
                      exact ⟨iff_of_false (not_le_of_gt hzk) (not_le_of_gt hky), iff_of_true hzk.le hky.le⟩
                    · push Not at hu
                      refine ⟨0, Or.inl rfl, ?_⟩
                      intro i
                      exact (heq i (le_antisymm (hl i) (hu i))).elim
              have hsample_sign : ∀ {ι : Type} [Fintype ι] (a b : ι → ℝ) (y : ℝ),
                  ∃ z : ℝ, (z = 0 ∨ ∃ i, z = -b i / a i ∨ z = -b i / a i - 1 ∨
                    z = -b i / a i + 1 ∨ ∃ j, z = ((-b i / a i) + (-b j / a j)) / 2) ∧
                  ∀ i, (a i * z + b i ≤ 0 ↔ a i * y + b i ≤ 0) := by
                intro ι inst a b y
                obtain ⟨z, hz, he⟩ := hsample_order (fun i => -b i / a i) y
                refine ⟨z, hz, ?_⟩
                intro i
                by_cases ha : a i = 0
                · simp [ha]
                · have hr : a i * (-b i / a i) + b i = 0 := by field_simp; ring
                  rcases lt_or_gt_of_ne ha with haneg | hapos
                  · have hlin (x : ℝ) : a i * x + b i ≤ 0 ↔ -b i / a i ≤ x := by
                      constructor
                      · intro hx
                        apply (mul_le_mul_left_of_neg haneg).mp
                        linarith
                      · intro hx
                        have hh := (mul_le_mul_left_of_neg haneg).mpr hx
                        linarith
                    rw [hlin, hlin]
                    exact (he i).1
                  · have hlin (x : ℝ) : a i * x + b i ≤ 0 ↔ x ≤ -b i / a i := by
                      constructor
                      · intro hx
                        apply (mul_le_mul_iff_right₀ hapos).mp
                        linarith
                      · intro hx
                        have hh := (mul_le_mul_iff_right₀ hapos).mpr hx
                        linarith
                    rw [hlin, hlin]
                    exact (he i).2
              have hLD_proj : ∀ {κ : Type} [Fintype κ] {P : ℝ → (Option κ → ℝ) → Prop},
                  LD (Option κ) P → ∃ ι : Type, ∃ inst : Fintype ι,
                  ∃ s : ι → ℝ → (κ → ℝ) → ℝ, (∀ i, LA κ (s i)) ∧
                  (∀ᶠ t in atTop, ∀ x,
                    (∃ y : ℝ, P t (Option.elim' y x)) ↔ ∃ i, P t (Option.elim' (s i t x) x)) ∧
                  LD κ (fun t x => ∃ y : ℝ, P t (Option.elim' y x)) := by
                intro κ inst P ⟨ι, instι, f, hf, Φ, hΦ⟩
                letI : Fintype ι := instι
                have hf_saved := hf
                choose a b he using hf
                choose c hc using (fun i => hinv (a i none))
                let B : ι → ℝ → (κ → ℝ) → ℝ := fun i t x =>
                  (∑ k, (a i (some k)).eval t * x k) + (b i).eval t
                have hB : ∀ i, LA κ (B i) := by
                  intro i
                  exact ⟨(fun k => a i (some k)), b i, Filter.Eventually.of_forall (fun t x => rfl)⟩
                let root : ι → ℝ → (κ → ℝ) → ℝ := fun i t x => -(c i).eval t * B i t x
                have hroot : ∀ i, LA κ (root i) := by
                  intro i
                  apply hLA_congr (hLA_neg (hLA_mul (c i) (hB i)))
                  exact Filter.Eventually.of_forall (fun t x => by dsimp [root]; ring)
                let J := Unit ⊕ (ι ⊕ ((ι × Bool) ⊕ (ι × ι)))
                let s : J → ℝ → (κ → ℝ) → ℝ := Sum.elim (fun _ _ _ => 0)
                  (Sum.elim root (Sum.elim
                    (fun z t x => root z.1 t x + if z.2 then -1 else 1)
                    (fun z t x => (root z.1 t x + root z.2 t x) / 2)))
                have hs : ∀ j, LA κ (s j) := by
                  intro j
                  rcases j with j | j
                  · apply hLA_congr (hLA_const (κ := κ) (C 0))
                    exact Filter.Eventually.of_forall (fun t x => by simp [s, hC])
                  · rcases j with i | j
                    · exact hroot i
                    · rcases j with z | z
                      · apply hLA_congr (hLA_add (hroot z.1) (hLA_const (C (if z.2 then -1 else 1))))
                        exact Filter.Eventually.of_forall (fun t x => by simp [s, hC])
                      · apply hLA_congr (hLA_mul (C (1 / 2)) (hLA_add (hroot z.1) (hroot z.2)))
                        exact Filter.Eventually.of_forall (fun t x => by dsimp [s]; rw [hC]; ring)
                have hcover : ∀ᶠ t in atTop, ∀ x,
                    (∃ y : ℝ, P t (Option.elim' y x)) ↔ ∃ j : J, P t (Option.elim' (s j t x) x) := by
                  filter_upwards [hΦ, Filter.eventually_all.mpr he, Filter.eventually_all.mpr hc] with t hΦt het hct x
                  have hval : ∀ i y, f i t (Option.elim' y x) = (a i none).eval t * y + B i t x := by
                    intro i y
                    rw [het i]
                    simp only [Fintype.sum_option, Option.elim', B]
                    ring
                  have hrval : ∀ i, root i t x = - B i t x / (a i none).eval t := by
                    intro i
                    dsimp [root]
                    rw [hct]
                    ring
                  constructor
                  · rintro ⟨y, hy⟩
                    obtain ⟨z, hz, hsign⟩ := hsample_sign (fun i => (a i none).eval t) (fun i => B i t x) y
                    have hj : ∃ j : J, s j t x = z := by
                      rcases hz with hz | ⟨i, hi | hi | hi | ⟨j, hij⟩⟩
                      · exact ⟨.inl (), hz.symm⟩
                      · exact ⟨.inr (.inl i), by simpa [s, hrval] using hi.symm⟩
                      · exact ⟨.inr (.inr (.inl (i, true))), by dsimp [s]; rw [hrval]; linarith⟩
                      · exact ⟨.inr (.inr (.inl (i, false))), by dsimp [s]; rw [hrval]; linarith⟩
                      · exact ⟨.inr (.inr (.inr (i, j))), by simpa [s, hrval] using hij.symm⟩
                    obtain ⟨j, hj⟩ := hj
                    refine ⟨j, (hΦt _).mpr ?_⟩
                    have hp := (hΦt _).mp hy
                    have hequal : (fun i => f i t (Option.elim' (s j t x) x) ≤ 0) =
                        (fun i => f i t (Option.elim' y x) ≤ 0) := by
                      funext i
                      apply propext
                      rw [hval, hval, hj]
                      exact hsign i
                    rw [hequal]
                    exact hp
                  · rintro ⟨j, hj⟩
                    exact ⟨s j t x, hj⟩
                refine ⟨J, inferInstance, s, hs, hcover, ?_⟩
                apply hLD_congr (hLD_any
                  (fun j t x => P t (Option.elim' (s j t x) x)) (fun j =>
                    hLD_comp (fun i t x => Option.elim' (s j t x) x i) ⟨ι, instι, f, hf_saved, Φ, hΦ⟩ (by
                      intro i
                      cases i with
                      | none => exact hs j
                      | some k => exact hLA_coord k)))
                exact hcover
              have hLA_eval : ∀ {κ : Type} [Fintype κ] {f : ℝ → (κ → ℝ) → ℝ},
                  LA κ f → ∀ x : κ → Puiseux, ∃ g : Puiseux,
                  ∀ᶠ t in atTop, g.eval t = f t (fun k => (x k).eval t) := by
                intro κ inst f ⟨a, b, hf⟩ x
                obtain ⟨z, hz⟩ := hdot a x
                obtain ⟨w, hw⟩ := hadd z b
                refine ⟨w, ?_⟩
                filter_upwards [hf, hz, hw] with t hft hzt hwt
                rw [hwt, hzt, hft]
              have hLD_truth : ∀ {κ : Type} [Fintype κ] {P : ℝ → (κ → ℝ) → Prop},
                  LD κ P → ∀ x : κ → Puiseux,
                  (∀ᶠ t in atTop, P t (fun k => (x k).eval t)) ∨
                  (∀ᶠ t in atTop, ¬ P t (fun k => (x k).eval t)) := by
                intro κ inst P ⟨ι, instι, f, hf, Φ, hΦ⟩ x
                letI : Fintype ι := instι
                choose g hg using (fun i => hLA_eval (hf i) x)
                let Z : ι → Prop := fun i => ∀ᶠ t in atTop, (g i).eval t ≤ 0
                have hstable : ∀ i, ∀ᶠ t in atTop, ((g i).eval t ≤ 0 ↔ Z i) := by
                  intro i
                  rcases hsign (g i) with hz | hp | hn
                  · have hZ : Z i := hz.mono (fun t ht => ht.le)
                    exact hz.mono (fun t ht => iff_of_true ht.le hZ)
                  · have hZ : ¬ Z i := by
                      intro hZ
                      obtain ⟨t, hpt, hzt⟩ := (hp.and hZ).exists
                      exact (not_lt_of_ge hzt) hpt
                    exact hp.mono (fun t ht => iff_of_false (not_le_of_gt ht) hZ)
                  · have hZ : Z i := hn.mono (fun t ht => ht.le)
                    exact hn.mono (fun t ht => iff_of_true ht.le hZ)
                have he : ∀ᶠ t in atTop, P t (fun k => (x k).eval t) ↔ Φ Z := by
                  filter_upwards [hΦ, Filter.eventually_all.mpr hg, Filter.eventually_all.mpr hstable] with t hΦt hgt hst
                  rw [hΦt]
                  have heq : (fun i => f i t (fun k => (x k).eval t) ≤ 0) = Z := by
                    funext i
                    apply propext
                    rw [← hgt i]
                    exact hst i
                  rw [heq]
                by_cases hZ : Φ Z
                · exact Or.inl (he.mono (fun t ht => ht.mpr hZ))
                · exact Or.inr (he.mono (fun t ht hp => hZ (ht.mp hp)))
              have hfinite_choose : ∀ {ι : Type} [Fintype ι] (P : ι → ℝ → Prop),
                  (∀ i, (∀ᶠ t in atTop, P i t) ∨ (∀ᶠ t in atTop, ¬ P i t)) →
                  (∀ᶠ t in atTop, ∃ i, P i t) → ∃ i, ∀ᶠ t in atTop, P i t := by
                intro ι inst P hs he
                by_contra hn
                have hn' : ∀ i, ¬ ∀ᶠ t in atTop, P i t := fun i hi => hn ⟨i, hi⟩
                have hall : ∀ i, ∀ᶠ t in atTop, ¬ P i t := fun i => (hs i).resolve_left (hn' i)
                obtain ⟨t, ⟨i, hi⟩, ht⟩ := (he.and (Filter.eventually_all.mpr hall)).exists
                exact ht i hi
              have hopt : ∀ {κ : Type} (y : Puiseux) (z : κ → Puiseux) (t : ℝ),
                  (fun i => (Option.elim' y z i).eval t) = Option.elim' (y.eval t) (fun k => (z k).eval t) := by
                intro κ y z t
                funext i
                cases i <;> rfl
              have hselect : ∀ (κ : Type) [Fintype κ] (P : ℝ → (κ → ℝ) → Prop),
                  LD κ P → (∀ᶠ t in atTop, ∃ x, P t x) →
                  ∃ z : κ → Puiseux, ∀ᶠ t in atTop, P t (fun k => (z k).eval t) := by
                apply Fintype.induction_empty_option
                · intro α β instβ e ih
                  letI : Fintype α := Fintype.ofEquiv β e.symm
                  intro P hP hev
                  have hP' := hLD_comp (fun i _ x => x (e.symm i)) hP (fun i => hLA_coord (e.symm i))
                  have hev' : ∀ᶠ t in atTop, ∃ x : α → ℝ, P t (fun i => x (e.symm i)) := by
                    apply hev.mono
                    rintro t ⟨x, hx⟩
                    refine ⟨(fun i => x (e i)), ?_⟩
                    simpa only [e.apply_symm_apply] using hx
                  obtain ⟨z, hz⟩ := ih _ hP' hev'
                  exact ⟨(fun i => z (e.symm i)), hz⟩
                · intro P hP hev
                  refine ⟨(fun i => PEmpty.elim i), ?_⟩
                  apply hev.mono
                  rintro t ⟨x, hx⟩
                  have heq : (fun k : PEmpty => (PEmpty.elim k : Puiseux).eval t) = x := by
                    funext k
                    exact PEmpty.elim k
                  rwa [heq]
                · intro κ instκ ih P hP hev
                  obtain ⟨ι, instι, s, hs, hcover, hP'⟩ := hLD_proj hP
                  letI : Fintype ι := instι
                  have hev' : ∀ᶠ t in atTop, ∃ x : κ → ℝ, ∃ y : ℝ, P t (Option.elim' y x) := by
                    apply hev.mono
                    rintro t ⟨x, hx⟩
                    refine ⟨(fun k => x (some k)), x none, ?_⟩
                    have heq : Option.elim' (x none) (fun k => x (some k)) = x := by
                      funext i
                      cases i <;> rfl
                    rwa [heq]
                  obtain ⟨z, hz⟩ := ih _ hP' hev'
                  choose y hy using (fun i => hLA_eval (hs i) z)
                  have hbranch : ∀ i, (∀ᶠ t in atTop, P t (Option.elim' ((y i).eval t) (fun k => (z k).eval t))) ∨
                      (∀ᶠ t in atTop, ¬ P t (Option.elim' ((y i).eval t) (fun k => (z k).eval t))) := by
                    intro i
                    simpa only [hopt] using hLD_truth hP (Option.elim' (y i) z)
                  have hevJ : ∀ᶠ t in atTop, ∃ i, P t (Option.elim' ((y i).eval t) (fun k => (z k).eval t)) := by
                    filter_upwards [hz, hcover, Filter.eventually_all.mpr hy] with t hzt hct hyt
                    obtain ⟨i, hi⟩ := (hct _).mp hzt
                    refine ⟨i, ?_⟩
                    rwa [hyt]
                  obtain ⟨i, hi⟩ := hfinite_choose _ hbranch hevJ
                  refine ⟨Option.elim' (y i) z, ?_⟩
                  simpa only [hopt] using hi
              have hLD_exists : ∀ (β : Type) [Fintype β] {κ : Type} [Fintype κ]
                  {P : ℝ → (β ⊕ κ → ℝ) → Prop}, LD (β ⊕ κ) P →
                  LD κ (fun t x => ∃ y : β → ℝ, P t (Sum.elim y x)) := by
                apply Fintype.induction_empty_option
                · intro α β instβ e ih
                  letI : Fintype α := Fintype.ofEquiv β e.symm
                  intro κ instκ P hP
                  have hP' := hLD_comp
                    (fun i _ x => x (Sum.map e.symm id i)) hP (fun i => hLA_coord (Sum.map e.symm id i))
                  apply hLD_congr (ih hP')
                  apply Filter.Eventually.of_forall
                  intro t x
                  constructor
                  · rintro ⟨y, hy⟩
                    refine ⟨(fun i => y (e i)), ?_⟩
                    have heq : (fun i => Sum.elim (fun i => y (e i)) x (Sum.map e.symm id i)) = Sum.elim y x := by
                      funext i
                      cases i <;> simp
                    rwa [heq]
                  · rintro ⟨y, hy⟩
                    refine ⟨(fun i => y (e.symm i)), ?_⟩
                    have heq : (fun i => Sum.elim y x (Sum.map e.symm id i)) =
                        Sum.elim (fun i => y (e.symm i)) x := by
                      funext i
                      cases i <;> rfl
                    rwa [← heq]
                · intro κ instκ P hP
                  have hP' := hLD_comp
                    (fun i _ x => Sum.elim (fun i : PEmpty => PEmpty.elim i) x i) hP (by
                      intro i
                      cases i with
                      | inl i => exact PEmpty.elim i
                      | inr i => exact hLA_coord i)
                  apply hLD_congr hP'
                  apply Filter.Eventually.of_forall
                  intro t x
                  constructor
                  · rintro ⟨y, hy⟩
                    have heq : y = (fun i : PEmpty => PEmpty.elim i) := by
                      funext i
                      exact PEmpty.elim i
                    simpa only [heq] using hy
                  · intro hx
                    exact ⟨(fun i => PEmpty.elim i), hx⟩
                · intro β instβ ih κ instκ P hP
                  let embed : Option β ⊕ κ → Option (β ⊕ κ) :=
                    Sum.elim (Option.elim' none (fun i => some (.inl i))) (fun i => some (.inr i))
                  let Q : ℝ → (Option (β ⊕ κ) → ℝ) → Prop := fun t z => P t (fun i => z (embed i))
                  have hQ : LD (Option (β ⊕ κ)) Q :=
                    hLD_comp (fun i _ z => z (embed i)) hP (fun i => hLA_coord (embed i))
                  obtain ⟨ι, instι, s, hs, hcov, hQ'⟩ := hLD_proj hQ
                  have hres := ih hQ'
                  apply hLD_congr hres
                  apply Filter.Eventually.of_forall
                  intro t x
                  constructor
                  · rintro ⟨y, hy⟩
                    refine ⟨(fun i => y (some i)), y none, ?_⟩
                    change P t (fun i => Option.elim' (y none) (Sum.elim (fun i => y (some i)) x) (embed i))
                    have heq : (fun i => Option.elim' (y none) (Sum.elim (fun i => y (some i)) x) (embed i)) =
                        Sum.elim y x := by
                      funext i
                      cases i with
                      | inl i => cases i <;> rfl
                      | inr i => rfl
                    rwa [heq]
                  · rintro ⟨y, y₀, hy⟩
                    refine ⟨Option.elim' y₀ y, ?_⟩
                    change P t (fun i => Option.elim' y₀ (Sum.elim y x) (embed i)) at hy
                    have heq : (fun i => Option.elim' y₀ (Sum.elim y x) (embed i)) =
                        Sum.elim (Option.elim' y₀ y) x := by
                      funext i
                      cases i with
                      | inl i => cases i <;> rfl
                      | inr i => rfl
                    rwa [heq] at hy
              have hLA_real : ∀ {κ : Type} [Fintype κ] (c : ℝ), LA κ (fun _ _ => c) := by
                intro κ inst c
                apply hLA_congr (hLA_const (κ := κ) (C c))
                exact Filter.Eventually.of_forall (fun t x => (hC c t).symm)
              have hLD_le : ∀ {κ : Type} [Fintype κ] {f g : ℝ → (κ → ℝ) → ℝ},
                  LA κ f → LA κ g → LD κ (fun t x => f t x ≤ g t x) := by
                intro κ inst f g hf hg
                apply hLD_congr (hLD_atom (hLA_add hf (hLA_neg hg)))
                exact Filter.Eventually.of_forall (fun t x => by constructor <;> intro h <;> linarith)
              have hLD_eq : ∀ {κ : Type} [Fintype κ] {f g : ℝ → (κ → ℝ) → ℝ},
                  LA κ f → LA κ g → LD κ (fun t x => f t x = g t x) := by
                intro κ inst f g hf hg
                apply hLD_congr (hLD_and (hLD_le hf hg) (hLD_le hg hf))
                exact Filter.Eventually.of_forall (fun t x => le_antisymm_iff)
              have hLD_poly : LD (Fin d) (fun t x => x ∈ realPolyhedron A b t) := by
                apply hLD_all (fun i t x => (∑ k, (A i k).eval t * x k) ≤ (b i).eval t)
                intro i
                exact hLD_le (hLA_sum (fun k t x => (A i k).eval t * x k)
                  (fun k => hLA_mul (A i k) (hLA_coord k))) (hLA_const (b i))
              let K := (Fin q ⊕ Fin r) ⊕ Fin d
              let R : ℝ → (K → ℝ) → Prop := fun t z =>
                (∀ i : Fin q, 0 ≤ z (.inl (.inl i))) ∧
                (∀ j : Fin r, 0 ≤ z (.inl (.inr j))) ∧
                (∑ i : Fin q, z (.inl (.inl i))) = 1 ∧
                ∀ k : Fin d, z (.inr k) =
                  (∑ i : Fin q, (u i k).eval t * z (.inl (.inl i))) +
                  ∑ j : Fin r, (v j k).eval t * z (.inl (.inr j))
              have hR : LD K R := by
                apply hLD_and
                · exact hLD_all (κ := K) (ι := Fin q) (fun i _ z => 0 ≤ z (.inl (.inl i)))
                    (fun i => hLD_le (hLA_real 0) (hLA_coord (κ := K) (.inl (.inl i))))
                · apply hLD_and
                  · exact hLD_all (κ := K) (ι := Fin r) (fun j _ z => 0 ≤ z (.inl (.inr j)))
                      (fun j => hLD_le (hLA_real 0) (hLA_coord (κ := K) (.inl (.inr j))))
                  · apply hLD_and
                    · exact hLD_eq (hLA_sum (κ := K) (fun i _ z => z (.inl (.inl i)))
                        (fun i => hLA_coord (κ := K) (.inl (.inl i)))) (hLA_real 1)
                    · apply hLD_all
                      intro k
                      exact hLD_eq (hLA_coord (κ := K) (.inr k))
                        (hLA_add
                          (hLA_sum (κ := K) (fun i t z => (u i k).eval t * z (.inl (.inl i)))
                            (fun i => hLA_mul (u i k) (hLA_coord (κ := K) (.inl (.inl i)))))
                          (hLA_sum (κ := K) (fun j t z => (v j k).eval t * z (.inl (.inr j)))
                            (fun j => hLA_mul (v j k) (hLA_coord (κ := K) (.inl (.inr j))))))
              have hLD_gen : LD (Fin d) (fun t x =>
                  x ∈ realGenerated (fun i => evalFun (u i) t) (fun j => evalFun (v j) t)) := by
                apply hLD_congr (hLD_exists (Fin q ⊕ Fin r) hR)
                apply Filter.Eventually.of_forall
                intro t x
                constructor
                · rintro ⟨α, β, ha, hb, hs, he⟩
                  refine ⟨Sum.elim α β, ha, hb, hs, ?_⟩
                  intro k
                  simpa only [Sum.elim_inl, Sum.elim_inr, evalFun, mul_comm] using he k
                · rintro ⟨γ, ha, hb, hs, he⟩
                  refine ⟨(fun i => γ (.inl i)), (fun j => γ (.inr j)), ha, hb, hs, ?_⟩
                  intro k
                  simpa only [Sum.elim_inl, Sum.elim_inr, evalFun, mul_comm] using he k
              have hstableExists : ∀ {κ : Type} [Fintype κ] {P : ℝ → (κ → ℝ) → Prop},
                  LD κ P → (∀ᶠ t in atTop, ∃ x, P t x) ∨ (∀ᶠ t in atTop, ¬ ∃ x, P t x) := by
                intro κ inst P hP
                have hP' := hLD_comp (fun k _ z => z (Sum.inl k : κ ⊕ PEmpty)) hP
                  (fun k => hLA_coord (Sum.inl k))
                have hE := hLD_exists κ hP'
                simpa only [Sum.elim_inl] using
                  hLD_truth hE (fun i : PEmpty => PEmpty.elim i)
              have hreverse : ∀ᶠ t in atTop,
                  realPolyhedron A b t ⊆
                    realGenerated (fun i => evalFun (u i) t) (fun j => evalFun (v j) t) := by
                by_contra hn
                have hbad := hLD_and hLD_poly (hLD_not hLD_gen)
                rcases hstableExists hbad with hb | hb
                · obtain ⟨z, hz⟩ := hselect (Fin d) _ hbad hb
                  have hzP : z ∈ kPolyhedron A b := hz.mono (fun t ht => ht.1)
                  have hzG : z ∈ kGenerated u v := by rw [← hgen]; exact hzP
                  obtain ⟨α, β, hαβ⟩ := hzG
                  have hrealG : ∀ᶠ t in atTop,
                      evalFun z t ∈ realGenerated (fun i => evalFun (u i) t) (fun j => evalFun (v j) t) := by
                    apply hαβ.mono
                    intro t ht
                    exact ⟨(fun i => (α i).eval t), (fun j => (β j).eval t), ht⟩
                  obtain ⟨t, hzt, hgt⟩ := (hz.and hrealG).exists
                  exact hzt.2 hgt
                · apply hn
                  apply hb.mono
                  intro t ht x hx
                  by_contra hxg
                  exact ht ⟨x, hx, hxg⟩
              filter_upwards [hinclusion, hreverse] with t ht ht'
              exact Set.Subset.antisymm ht' ht
