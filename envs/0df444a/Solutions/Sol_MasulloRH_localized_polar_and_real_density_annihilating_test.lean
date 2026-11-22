-- Prove2me | solution 1 for MasulloRH.localized_polar_and_real_density_annihilating_test
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-21T12:41:39.318332+00:00
-- url     : https://prove2.me/submissions/2d4ba3e4-2606-4c49-ab8f-f8ae92a73124

import Mathlib
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

theorem solution (c r : ℝ) (hr : 0 < r) (hc : r < c) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ tsupport f ⊆ closedBall c r ∧ f c ≠ 0 ∧
      (∀ a ∈ ([1/2, -1/2, 1, -1] : List ℝ), (∫ x : ℝ, Real.exp (a*x) * f x) = 0) ∧
      (∀ a ∈ ([-1/2, -3/2, 1, -1] : List ℝ),
        (∫ x : ℝ, Real.exp (a*x) * f x / (1 - Real.exp (-2*x))) = 0) := by
  let M := fun (a : ℝ) (h : ℝ → ℝ) => ∫ x : ℝ, Real.exp (a*x) * h x
  have hI (a : ℝ) (h : ℝ → ℝ) (hd : Continuous h) (hk : HasCompactSupport h) :
      Integrable (fun x => Real.exp (a*x) * h x) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hd).integrable_of_hasCompactSupport
      (hk.mul_left (f := fun x => Real.exp (a*x)))
  have step (a b : ℝ) (h : ℝ → ℝ) (hd : ContDiff ℝ ∞ h) (hk : HasCompactSupport h) :
      M a (fun x => deriv h x + b*h x) = (b-a)*M a h := by
    let E := fun x : ℝ => Real.exp (a*x)
    have dE (x : ℝ) : HasDerivAt E (a*E x) x := by
      simpa [E,mul_comm] using ((hasDerivAt_id x).const_mul a).exp
    have dh := (contDiff_infty_iff_deriv.mp hd)
    have hi := hI a h hd.continuous hk
    have hj := hI a (deriv h) dh.2.continuous hk.deriv
    have byp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := E) (u' := fun x => a*E x) (v := h) (v' := deriv h)
      (fun x _ => dE x) (fun x _ => (dh.1 x).hasDerivAt) hj
      (show Integrable (fun x => (a*E x)*h x) by simpa only [mul_assoc] using hi.const_mul a) hi
    simp only [mul_assoc,integral_const_mul] at byp
    change (∫ x, E x*(deriv h x + b*h x)) = (b-a)*(∫ x, E x*h x)
    have he (x : ℝ) : E x*(deriv h x + b*h x) = E x*deriv h x + b*(E x*h x) := by ring
    simp_rw [he]
    rw [integral_add hj (hi.const_mul b), byp, integral_const_mul]
    ring
  have build (ls : List ℝ) (hl : ∀ b ∈ ls, b ≠ 0) :
      ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ tsupport h ⊆ closedBall c r ∧
        (∃ v : ℝ, v ≠ 0 ∧ h =ᶠ[𝓝 c] (fun _ => v)) ∧ ∀ a ∈ ls, M a h = 0 := by
    induction ls with
    | nil =>
      let g : ContDiffBump c := ⟨r/2, r, by positivity, by linarith⟩
      refine ⟨g, g.contDiff, ?_, ⟨1, one_ne_zero, ?_⟩, by simp⟩
      · rw [g.tsupport_eq]
      · exact g.eventuallyEq_one_of_mem_ball (mem_ball_self g.rIn_pos)
    | cons b ls ih =>
      obtain ⟨h,hd,hs,⟨v,hv,he⟩,hm⟩ := ih (fun a ha => hl a (List.mem_cons_of_mem _ ha))
      have hk : HasCompactSupport h := (isCompact_closedBall c r).of_isClosed_subset isClosed_closure hs
      let k := fun x : ℝ => deriv h x + b*h x
      refine ⟨k, (contDiff_infty_iff_deriv.mp hd).2.add (contDiff_const.mul hd), ?_, ?_, ?_⟩
      · apply closure_minimal _ isClosed_closedBall
        intro x hx
        by_contra hx'
        have hx0 : x ∉ tsupport h := fun hy => hx' (hs hy)
        have hx1 : h x = 0 := by
          by_contra hz
          exact hx0 (subset_closure (show x ∈ Function.support h from hz))
        exact hx (by simp [k,deriv_of_notMem_tsupport hx0,hx1])
      · refine ⟨b*v, mul_ne_zero (hl b (by simp)) hv, ?_⟩
        filter_upwards [he,he.deriv] with x hx hx'
        change deriv h x = deriv (fun _ : ℝ => v) x at hx'
        simp [k,hx,hx']
      · intro a ha
        rw [show M a k = _ from step a b h hd hk]
        rcases List.mem_cons.mp ha with hab|has
        · simp [hab]
        · simp [hm a has]
  let ls : List ℝ := [1/2, -1/2, -3/2, -5/2, 1, -1, -3]
  obtain ⟨h,hd,hs,⟨v,hv,he⟩,hm⟩ := build ls (by norm_num [ls])
  have hk : HasCompactSupport h := (isCompact_closedBall c r).of_isClosed_subset isClosed_closure hs
  let f := fun x : ℝ => (1-Real.exp (-2*x))*h x
  have fsm : ContDiff ℝ ∞ f := by dsimp [f]; fun_prop
  have hf (a : ℝ) : M a f = M a h - M (a-2) h := by
    have ee (x : ℝ) : Real.exp ((a-2)*x) = Real.exp (a*x)*Real.exp (-2*x) := by
      rw [← Real.exp_add]; congr 1; ring
    dsimp [M,f]
    rw [← integral_sub (hI a h hd.continuous hk) (hI (a-2) h hd.continuous hk)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [ee]; ring
  have h0 : h 0 = 0 := by
    by_contra hx
    have hh := hs (subset_closure (show (0:ℝ) ∈ Function.support h from hx))
    rw [mem_closedBall,Real.dist_eq,zero_sub,abs_neg,abs_of_pos (by linarith : 0<c)] at hh
    linarith
  have divId (a : ℝ) (x : ℝ) :
      Real.exp (a*x)*f x / (1-Real.exp (-2*x)) = Real.exp (a*x)*h x := by
    by_cases hx : x = 0
    · simp [hx,h0,f]
    have hh : 1-Real.exp (-2*x) ≠ 0 := by
      intro hh
      have hx' : Real.exp (-2*x) = 1 := by linarith
      rw [← Real.exp_zero] at hx'
      exact hx (by have := Real.exp_injective hx'; linarith)
    apply (div_eq_iff hh).2
    dsimp [f]; ring
  refine ⟨f,fsm, (tsupport_mul_subset_right.trans hs), ?_, ?_, ?_⟩
  · apply mul_ne_zero _ (he.self_of_nhds ▸ hv)
    have := Real.exp_lt_one_iff.mpr (show -2*c < 0 by linarith)
    linarith
  · intro a ha
    change M a f = 0
    rw [hf,hm a (by simp [ls] at *; tauto),hm (a-2) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
      rcases ha with rfl|rfl|rfl|rfl <;> norm_num [ls])]
    ring
  · intro a ha
    simp_rw [divId]
    exact hm a (by simp [ls] at *; tauto)
