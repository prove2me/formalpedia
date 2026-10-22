-- Prove2me | solution 1 for Gerver.sofa_cap_niche
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T05:00:40.759201+00:00
-- url     : https://prove2.me/submissions/925d2be9-788b-4f2b-8764-b564513ccc36

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

set_option linter.all false

namespace Gerver

open Real

/-- Algebraic core for the right contact point. In the orthonormal frame `(u_t, v_t)`,
`(c, s) = (cos (ω - t), sin (ω - t))` are the coordinates of `u_ω`. -/
lemma capniche_sideA (c s D1 D2 : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hD1 : 1 < D1) (hcon : c * D1 + s * D2 ≤ 1) : -s * D1 + c * D2 < 0 := by
  rcases hs.lt_or_eq with hs' | hs'
  · have h1 : s * (s * D2) ≤ s * (1 - c * D1) := mul_le_mul_of_nonneg_left (by linarith) hs
    have h2 : c * (s * D2) ≤ c * (1 - c * D1) := mul_le_mul_of_nonneg_left (by linarith) hc
    have hc1 : c ≤ 1 := by nlinarith
    have : s * (-s * D1 + c * D2) < 0 := by nlinarith
    by_contra hcon'
    push Not at hcon'
    have := mul_nonneg hs hcon'
    linarith
  · subst hs'
    have hc1 : c = 1 := by nlinarith
    subst hc1
    linarith

/-- Algebraic core for the left contact point. -/
lemma capniche_sideC (c s D1 D2 ct st sw : ℝ) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hst : 0 ≤ st) (hct : 0 ≤ ct) (hpt : ct ^ 2 + st ^ 2 = 1) (hsw : sw = c * st + s * ct)
    (hsle : s ≤ sw) (hsw0 : 0 < sw) (hD2 : 1 < D2) (hcon : st * D1 + ct * D2 ≤ 1) :
    0 < -s * D1 + c * D2 := by
  rcases hst.lt_or_eq with hst' | hst'
  · -- st * f = -s * (st * D1) + c * st * D2 ≥ -s * (1 - ct * D2) + c * st * D2 = D2 * sw - s
    have h1 : s * (st * D1) ≤ s * (1 - ct * D2) := mul_le_mul_of_nonneg_left (by linarith) hs
    have h2 : sw < D2 * sw := by nlinarith
    have : 0 < st * (-s * D1 + c * D2) := by
      have : st * (-s * D1 + c * D2) = -(s * (st * D1)) + D2 * (c * st) := by ring
      rw [this]
      have : D2 * (c * st) = D2 * sw - D2 * (s * ct) := by rw [hsw]; ring
      rw [this]
      nlinarith
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonneg_of_nonpos hst hneg
    linarith
  · subst hst'
    have hct1 : ct = 1 := by nlinarith
    subst hct1
    linarith

lemma capniche_trig {ω t : ℝ} (hω : 0 < ω) (hω' : ω ≤ π / 2) (ht0 : 0 ≤ t) (ht1 : t ≤ ω) :
    0 ≤ cos t ∧ 0 ≤ sin t ∧ 0 ≤ cos ω ∧ 0 < sin ω ∧
      0 ≤ cos ω * cos t + sin ω * sin t ∧ 0 ≤ sin ω * cos t - cos ω * sin t ∧
      sin ω * cos t - cos ω * sin t ≤ sin ω := by
  have hpi := pi_pos
  refine ⟨cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩,
    sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith),
    cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩,
    sin_pos_of_pos_of_lt_pi hω (by linarith), ?_, ?_, ?_⟩
  · rw [← cos_sub]; exact cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  · rw [← sin_sub]; exact sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  · rw [← sin_sub]
    exact sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

lemma capniche_eq (x : ℝ → ℝ × ℝ) (ω : ℝ) :
    sofaOfPath x ω = capOf x ω \ nicheOf x ω := by
  ext p
  simp only [sofaOfPath, capOf, nicheOf, Set.mem_inter_iff, Set.mem_iInter, Set.mem_diff,
    Set.mem_iUnion, not_and, not_exists]
  constructor
  · rintro ⟨hP, hQ⟩
    exact ⟨⟨hP, fun t ht => (hQ t ht).1⟩, fun _ t ht => (hQ t ht).2⟩
  · rintro ⟨⟨hP, hQ⟩, hN⟩
    have hF : p ∈ fan ω := ⟨hP.1.1, hP.2.1⟩
    exact ⟨hP, fun t ht => ⟨hQ t ht, hN hF t ht⟩⟩

lemma capniche_sub (x : ℝ → ℝ × ℝ) {ω : ℝ} (hω : 0 < ω) (hω' : ω ≤ π / 2)
    (hsup : IsSupportingPathOf x ω) (hconn : IsPreconnected (sofaOfPath x ω)) :
    nicheOf x ω ⊆ capOf x ω := by
  intro p hp
  by_contra hpK
  obtain ⟨hpF, hpN⟩ := hp
  simp only [Set.mem_iUnion] at hpN
  obtain ⟨t, ht, hpQ⟩ := hpN
  obtain ⟨⟨A, hA, hAu⟩, ⟨C, hC, hCv⟩⟩ := hsup.2 t ht
  obtain ⟨hct, hst, hcw, hsw, hc, hs, hsle⟩ := capniche_trig hω hω' ht.1 ht.2
  have hpt : cos t ^ 2 + sin t ^ 2 = 1 := cos_sq_add_sin_sq t
  have hpw : cos ω ^ 2 + sin ω ^ 2 = 1 := cos_sq_add_sin_sq ω
  set c := cos ω * cos t + sin ω * sin t with hcdef
  set s := sin ω * cos t - cos ω * sin t with hsdef
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    simp only [hcdef, hsdef]
    linear_combination (cos t ^ 2 + sin t ^ 2) * hpw + hpt
  -- membership data
  have hS : ∀ q ∈ sofaOfPath x ω, q ∈ para ω ∧ ∀ r ∈ Set.Icc 0 ω, q ∈ Qplus x r ∧ q ∉ Qminus x r := by
    intro q hq
    simp only [sofaOfPath, Set.mem_inter_iff, Set.mem_iInter, Set.mem_diff] at hq
    exact hq
  have hpy0 : 0 ≤ p.2 := hpF.1
  have hpw0 : 0 ≤ dot p (u ω) := hpF.2
  simp only [dot, u, v] at hpw0
  have hpQ1 : (p.1 - (x t).1) * cos t + (p.2 - (x t).2) * sin t < 0 := by
    have := hpQ.1; simpa [dot, u, Prod.fst_sub, Prod.snd_sub] using this
  have hpQ2 : (p.1 - (x t).1) * (-sin t) + (p.2 - (x t).2) * cos t < 0 := by
    have := hpQ.2; simpa [dot, v, Prod.fst_sub, Prod.snd_sub] using this
  let f : ℝ × ℝ → ℝ := fun q => -(q.1 - p.1) * sin ω + (q.2 - p.2) * cos ω
  have hfc : Continuous f := by fun_prop
  -- right contact point
  have hfA : f A < 0 := by
    obtain ⟨hAP, -⟩ := hS A hA
    have hAw : A.1 * cos ω + A.2 * sin ω ≤ 1 := by simpa [dot, u] using hAP.2.2
    have hAu' : (A.1 - (x t).1) * cos t + (A.2 - (x t).2) * sin t = 1 := by
      simpa [dot, u, Prod.fst_sub, Prod.snd_sub] using hAu
    have key := capniche_sideA c s ((A.1 - p.1) * cos t + (A.2 - p.2) * sin t)
      ((A.1 - p.1) * (-sin t) + (A.2 - p.2) * cos t) hcs hc hs (by linarith) (by
        have : c * ((A.1 - p.1) * cos t + (A.2 - p.2) * sin t) +
            s * ((A.1 - p.1) * (-sin t) + (A.2 - p.2) * cos t) =
            (A.1 - p.1) * cos ω + (A.2 - p.2) * sin ω := by
          simp only [hcdef, hsdef]
          linear_combination ((A.1 - p.1) * cos ω + (A.2 - p.2) * sin ω) * hpt
        rw [this]; linarith)
    have : -s * ((A.1 - p.1) * cos t + (A.2 - p.2) * sin t) +
        c * ((A.1 - p.1) * (-sin t) + (A.2 - p.2) * cos t) = f A := by
      simp only [hcdef, hsdef, f]
      linear_combination (-(A.1 - p.1) * sin ω + (A.2 - p.2) * cos ω) * hpt
    linarith
  -- left contact point
  have hfC : 0 < f C := by
    obtain ⟨hCP, -⟩ := hS C hC
    have hCy : C.2 ≤ 1 := hCP.1.2
    have hCv' : (C.1 - (x t).1) * (-sin t) + (C.2 - (x t).2) * cos t = 1 := by
      simpa [dot, v, Prod.fst_sub, Prod.snd_sub] using hCv
    have key := capniche_sideC c s ((C.1 - p.1) * cos t + (C.2 - p.2) * sin t)
      ((C.1 - p.1) * (-sin t) + (C.2 - p.2) * cos t) (cos t) (sin t) (sin ω) hc hs hst hct hpt
      (by simp only [hcdef, hsdef]; linear_combination (-sin ω) * hpt) hsle hsw (by linarith) (by
        have : sin t * ((C.1 - p.1) * cos t + (C.2 - p.2) * sin t) +
            cos t * ((C.1 - p.1) * (-sin t) + (C.2 - p.2) * cos t) = C.2 - p.2 := by
          linear_combination (C.2 - p.2) * hpt
        rw [this]; linarith)
    have : -s * ((C.1 - p.1) * cos t + (C.2 - p.2) * sin t) +
        c * ((C.1 - p.1) * (-sin t) + (C.2 - p.2) * cos t) = f C := by
      simp only [hcdef, hsdef, f]
      linear_combination (-(C.1 - p.1) * sin ω + (C.2 - p.2) * cos ω) * hpt
    linarith
  -- the line through `p` in direction `u ω` misses the sofa
  have hsplit : sofaOfPath x ω ⊆ {q | f q < 0} ∪ {q | 0 < f q} := by
    intro q hq
    rcases lt_trichotomy (f q) 0 with h | h | h
    · exact Or.inl h
    · exfalso
      obtain ⟨hqP, hqQ⟩ := hS q hq
      set l := (q.1 - p.1) * cos ω + (q.2 - p.2) * sin ω with hl
      have hq1 : q.1 = p.1 + l * cos ω := by
        simp only [f] at h
        linear_combination (-sin ω) * h - (q.1 - p.1) * hpw
      have hq2 : q.2 = p.2 + l * sin ω := by
        simp only [f] at h
        linear_combination (cos ω) * h - (q.2 - p.2) * hpw
      have hshift : ∀ w n : ℝ × ℝ, dot (q - w) n = dot (p - w) n + l * dot (u ω) n := by
        intro w n
        simp only [dot, u, Prod.fst_sub, Prod.snd_sub]
        rw [hq1, hq2]; ring
      have hut : dot (u ω) (u t) = c := by simp only [dot, u, hcdef]
      have hvt : dot (u ω) (v t) = s := by simp only [dot, u, v, hsdef]; ring
      rcases le_or_gt l 0 with hl0 | hl0
      · apply (hqQ t ht).2
        have m1 : l * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hl0 hc
        have m2 : l * s ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hl0 hs
        refine ⟨?_, ?_⟩
        · show dot (q - x t) (u t) < 0
          rw [hshift, hut]; linarith [hpQ.1]
        · show dot (q - x t) (v t) < 0
          rw [hshift, hvt]; linarith [hpQ.2]
      · apply hpK
        simp only [capOf, Set.mem_inter_iff, Set.mem_iInter]
        have hqy : q.2 ≤ 1 := hqP.1.2
        have hqw : dot q (u ω) ≤ 1 := hqP.2.2
        refine ⟨⟨⟨hpy0, ?_⟩, ⟨hpF.2, ?_⟩⟩, fun r hr => ?_⟩
        · show p.2 ≤ 1
          have : 0 ≤ l * sin ω := mul_nonneg hl0.le hsw.le
          rw [hq2] at hqy; linarith
        · show dot p (u ω) ≤ 1
          have e : dot q (u ω) = dot p (u ω) + l := by
            simp only [dot, u]; rw [hq1, hq2]; linear_combination l * hpw
          linarith
        · obtain ⟨-, -, -, -, hcr, hsr, -⟩ := capniche_trig hω hω' hr.1 hr.2
          obtain ⟨h1, h2⟩ := (hqQ r hr).1
          have m1 : 0 ≤ l * (cos ω * cos r + sin ω * sin r) := mul_nonneg hl0.le hcr
          have m2 : 0 ≤ l * (sin ω * cos r - cos ω * sin r) := mul_nonneg hl0.le hsr
          have e1 : dot (u ω) (u r) = cos ω * cos r + sin ω * sin r := by simp only [dot, u]
          have e2 : dot (u ω) (v r) = sin ω * cos r - cos ω * sin r := by simp only [dot, u, v]; ring
          rw [hshift, e1] at h1
          rw [hshift, e2] at h2
          exact ⟨by linarith, by linarith⟩
    · exact Or.inr h
  obtain ⟨z, -, hz1, hz2⟩ := hconn {q | f q < 0} {q | 0 < f q}
    (isOpen_lt hfc continuous_const) (isOpen_lt continuous_const hfc) hsplit ⟨A, hA, hfA⟩ ⟨C, hC, hfC⟩
  exact lt_asymm (show f z < 0 from hz1) (show 0 < f z from hz2)

theorem capniche_main (x : ℝ → ℝ × ℝ) {ω : ℝ} (hω : 0 < ω) (hω' : ω ≤ Real.pi / 2)
    (hsup : IsSupportingPathOf x ω) (hm : IsMovingSofa (sofaOfPath x ω)) :
    sofaOfPath x ω = capOf x ω \ nicheOf x ω ∧ nicheOf x ω ⊆ capOf x ω :=
  ⟨capniche_eq x ω, capniche_sub x hω hω' hsup hm.2.2.1.isPreconnected⟩

end Gerver

theorem solution (x : ℝ → ℝ × ℝ) {ω : ℝ} (hω : 0 < ω) (hω' : ω ≤ Real.pi / 2)
    (hsup : Gerver.IsSupportingPathOf x ω) (hm : Gerver.IsMovingSofa (Gerver.sofaOfPath x ω)) :
    Gerver.sofaOfPath x ω = Gerver.capOf x ω \ Gerver.nicheOf x ω ∧
      Gerver.nicheOf x ω ⊆ Gerver.capOf x ω :=
  Gerver.capniche_main x hω hω' hsup hm
