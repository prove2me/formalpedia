-- Prove2me | solution 1 for LiqProvision.Oligopoly.lemma_C_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T22:33:02.867667+00:00
-- url     : https://prove2.me/submissions/eb9d0dd6-76a6-4b5a-bae2-1b9b30efdcf6

import Mathlib

open Set

namespace LiqC3Aux

/-- Part 1 (⇐): nonnegative derivative with nowhere dense zero set gives strict monotonicity. -/
theorem strictMono_of (I : Set ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f I) (h0 : ∀ x ∈ I, 0 ≤ deriv f x)
    (hnd : IsNowhereDense {x | x ∈ I ∧ deriv f x = 0}) : StrictMonoOn f I := by
  have hdiff : DifferentiableOn ℝ f I := hf.differentiableOn (by norm_num)
  have hconv : Convex ℝ I := hIc.convex
  have hmono : MonotoneOn f I :=
    monotoneOn_of_deriv_nonneg hconv hdiff.continuousOn (by rwa [hIo.interior_eq])
      (by rwa [hIo.interior_eq])
  intro x hx y hy hxy
  rcases (hmono hx hy hxy.le).lt_or_eq with h | h
  · exact h
  exfalso
  -- f is constant on [x, y]
  have hIcc : Icc x y ⊆ I := hIc.out hx hy
  have hconst : ∀ z ∈ Icc x y, f z = f x := by
    intro z hz
    exact le_antisymm (h ▸ hmono (hIcc hz) hy hz.2) (hmono hx (hIcc hz) hz.1)
  have hsub : Ioo x y ⊆ {x | x ∈ I ∧ deriv f x = 0} := by
    intro z hz
    refine ⟨hIcc (Ioo_subset_Icc_self hz), ?_⟩
    have hev : f =ᶠ[nhds z] fun _ => f x := by
      filter_upwards [Ioo_mem_nhds hz.1 hz.2] with w hw
      exact hconst w (Ioo_subset_Icc_self hw)
    rw [hev.deriv_eq]; simp
  have : Ioo x y ⊆ interior (closure {x | x ∈ I ∧ deriv f x = 0}) :=
    interior_maximal (hsub.trans subset_closure) isOpen_Ioo
  rw [hnd] at this
  obtain ⟨z, hz⟩ := nonempty_Ioo.2 hxy
  exact this hz

end LiqC3Aux

open LiqC3Aux in
theorem solution (I : Set ℝ) (hIo : IsOpen I) (hIc : I.OrdConnected) (hIne : I.Nonempty)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 1 f I) :
    (StrictMonoOn f I ↔
      (∀ x ∈ I, 0 ≤ deriv f x) ∧ IsNowhereDense {x | x ∈ I ∧ deriv f x = 0}) ∧
    (StrictMonoOn f I → ∀ Kc : Set ℝ, IsCompact Kc → Kc ⊆ {x | x ∈ I ∧ 0 < deriv f x} →
      ∀ g : ℝ → ℝ, ContDiffOn ℝ 1 g I → (∀ x ∈ I, x ∉ Kc → g x = 0) →
        ∃ ε' > 0, ∀ ε ∈ Set.Icc (-ε') ε', StrictMonoOn (fun x => f x + ε * g x) I) := by
  have hdiff : DifferentiableOn ℝ f I := hf.differentiableOn (by norm_num)
  have hdc : ContinuousOn (deriv f) I := hf.continuousOn_deriv_of_isOpen hIo le_rfl
  have part1 : StrictMonoOn f I ↔
      (∀ x ∈ I, 0 ≤ deriv f x) ∧ IsNowhereDense {x | x ∈ I ∧ deriv f x = 0} := by
    refine ⟨fun hsm => ⟨?_, ?_⟩, fun h => strictMono_of I hIo hIc f hf h.1 h.2⟩
    · intro x hx
      have := (hsm.monotoneOn).derivWithin_nonneg (x := x)
      rwa [derivWithin_of_isOpen hIo hx] at this
    · -- nowhere dense
      rw [IsNowhereDense, Set.eq_empty_iff_forall_notMem]
      intro z hz
      set U := interior (closure {x | x ∈ I ∧ deriv f x = 0})
      have hzc : z ∈ closure I :=
        closure_mono (fun x hx => hx.1) (interior_subset hz)
      obtain ⟨w, hwU, hwI⟩ := mem_closure_iff.1 hzc U isOpen_interior hz
      have hV : U ∩ I ∈ nhds w := (isOpen_interior.inter hIo).mem_nhds ⟨hwU, hwI⟩
      obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hV
      -- on (w - δ, w + δ) the derivative vanishes
      have hzero : ∀ v ∈ Metric.ball w δ, deriv f v = 0 := by
        intro v hv
        have hvI : v ∈ I := (hball hv).2
        have hvcl : v ∈ closure {x | x ∈ I ∧ deriv f x = 0} := interior_subset (hball hv).1
        have hcont : ContinuousWithinAt (deriv f) {x | x ∈ I ∧ deriv f x = 0} v :=
          ((hdc v hvI).continuousAt (hIo.mem_nhds hvI)).continuousWithinAt
        have := hcont.mem_closure_image hvcl
        have himg : deriv f '' {x | x ∈ I ∧ deriv f x = 0} ⊆ {0} := by
          rintro _ ⟨u, hu, rfl⟩; exact hu.2
        have := closure_mono himg this
        simpa using this
      have hb : w + δ / 2 ∈ Metric.ball w δ := by
        rw [Metric.mem_ball, Real.dist_eq]; rw [abs_of_pos (by linarith)]; linarith
      have hw : w ∈ Metric.ball w δ := Metric.mem_ball_self hδ
      have hIcc : Icc w (w + δ / 2) ⊆ Metric.ball w δ := by
        intro v hv
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hv.1, hv.2]
      obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope f (by linarith : w < w + δ / 2)
        (hdiff.continuousOn.mono (fun v hv => (hball (hIcc hv)).2))
        (hdiff.mono (fun v hv => (hball (hIcc (Ioo_subset_Icc_self hv))).2))
      rw [hzero c (hIcc (Ioo_subset_Icc_self hc))] at hcd
      have hlt := hsm hwI (hball hb).2 (by linarith : w < w + δ / 2)
      have hne : (w + δ / 2 - w) ≠ 0 := by linarith
      have : f (w + δ / 2) - f w = 0 := by
        rw [eq_comm, div_eq_zero_iff] at hcd
        exact hcd.resolve_right hne
      linarith
  refine ⟨part1, ?_⟩
  intro hsm Kc hK hKsub g hg hg0
  obtain ⟨hnn, hnd⟩ := part1.1 hsm
  have hgdiff : DifferentiableOn ℝ g I := hg.differentiableOn (by norm_num)
  have hgdc : ContinuousOn (deriv g) I := hg.continuousOn_deriv_of_isOpen hIo le_rfl
  have hKI : Kc ⊆ I := fun x hx => (hKsub hx).1
  -- lower bound δ for deriv f on Kc
  obtain ⟨δ, hδ, hδK⟩ : ∃ δ > 0, ∀ x ∈ Kc, δ ≤ deriv f x := by
    rcases Kc.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x0, hx0, hmin⟩ := hK.exists_isMinOn hne (hdc.mono hKI)
      exact ⟨deriv f x0, (hKsub hx0).2, fun x hx => hmin hx⟩
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hgdc.mono hKI)
  have hB0 : 0 ≤ |B| := abs_nonneg B
  refine ⟨δ / (2 * (|B| + 1)), by positivity, ?_⟩
  intro ε hε
  have hεabs : |ε| ≤ δ / (2 * (|B| + 1)) := abs_le.2 hε
  -- derivative of g outside Kc vanishes
  have hgout : ∀ x ∈ I, x ∉ Kc → deriv g x = 0 := by
    intro x hx hxK
    have hopen : IsOpen (I \ Kc) := hIo.sdiff hK.isClosed
    have hev : g =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds ⟨hx, hxK⟩] with y hy
      exact hg0 y hy.1 hy.2
    rw [hev.deriv_eq]; simp
  have hderiv : ∀ x ∈ I, deriv (fun x => f x + ε * g x) x = deriv f x + ε * deriv g x := by
    intro x hx
    have h1 := (hdiff x hx).differentiableAt (hIo.mem_nhds hx)
    have h2 := (hgdiff x hx).differentiableAt (hIo.mem_nhds hx)
    exact ((h1.hasDerivAt).add (h2.hasDerivAt.const_mul ε)).deriv
  have hpos : ∀ x ∈ Kc, 0 < deriv f x + ε * deriv g x := by
    intro x hx
    have hb := hB x hx
    rw [Real.norm_eq_abs] at hb
    have : |ε * deriv g x| ≤ δ / (2 * (|B| + 1)) * |B| := by
      rw [abs_mul]
      exact mul_le_mul hεabs (hb.trans (le_abs_self B)) (abs_nonneg _) (by positivity)
    have hlt : δ / (2 * (|B| + 1)) * |B| < δ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have := neg_abs_le (ε * deriv g x)
    linarith [hδK x hx]
  apply strictMono_of I hIo hIc _ (hf.add (contDiffOn_const.mul hg))
  · intro x hx
    rw [hderiv x hx]
    by_cases hxK : x ∈ Kc
    · exact (hpos x hxK).le
    · rw [hgout x hx hxK]; simpa using hnn x hx
  · apply hnd.mono
    rintro x ⟨hx, hx0⟩
    refine ⟨hx, ?_⟩
    rw [hderiv x hx] at hx0
    by_cases hxK : x ∈ Kc
    · exact absurd hx0 (hpos x hxK).ne'
    · rw [hgout x hx hxK] at hx0; simpa using hx0
