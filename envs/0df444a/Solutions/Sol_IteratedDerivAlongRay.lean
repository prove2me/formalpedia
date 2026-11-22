-- Prove2me | solution 1 for IteratedDerivAlongRay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:09:50.097741+00:00
-- url     : https://prove2.me/submissions/1d532a65-48fb-458c-9438-94e7ce2da699

import Definitions.Def_PHigherOrder_Plane
import Definitions.Def_PHigherOrder_IteratedDerivAlongRay

set_option autoImplicit false

theorem _root_.solution (U : Set Plane) (hU : IsOpen U) (u : Plane → ℝ) (j : ℕ)
    (hu : ContDiffOn ℝ (j : ℕ∞) u U) (x₀ e : Plane) (t : ℝ) (ht : x₀ + t • e ∈ U) :
    iteratedDeriv j (fun s : ℝ => u (x₀ + s • e)) t
      = iteratedFDeriv ℝ j u (x₀ + t • e) (fun _ => e) := by
  have hpathcont : Continuous (fun r : ℝ => x₀ + r • e) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hIopen : IsOpen ((fun r : ℝ => x₀ + r • e) ⁻¹' U) := hU.preimage hpathcont
  -- The induction is run with `U`, `u`, `x₀`, `e` fixed but the parameter quantified:
  -- the inductive step needs the order-`m` identity at every nearby parameter, not just at `t`.
  have key : ∀ m : ℕ, ContDiffOn ℝ (m : ℕ∞) u U → ∀ s : ℝ, x₀ + s • e ∈ U →
      iteratedDeriv m (fun r : ℝ => u (x₀ + r • e)) s
        = iteratedFDeriv ℝ m u (x₀ + s • e) (fun _ => e) := by
    intro m
    induction m with
    | zero =>
      intro _ s _
      simp
    | succ m ih =>
      intro hum s hs
      have hum' : ContDiffOn ℝ (m : ℕ∞) u U := hum.of_le (by exact_mod_cast Nat.le_succ m)
      -- `x ↦ D^m u x` is differentiable at the point, the set being open.
      have hdw : DifferentiableOn ℝ (iteratedFDerivWithin ℝ m u U) U :=
        hum.differentiableOn_iteratedFDerivWithin
          (by exact_mod_cast Nat.lt_succ_self m) hU.uniqueDiffOn
      have hev : iteratedFDeriv ℝ m u
          =ᶠ[nhds (x₀ + s • e)] iteratedFDerivWithin ℝ m u U :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hs)
          fun y hy => (iteratedFDerivWithin_of_isOpen m hU hy).symm
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m u) (x₀ + s • e) :=
        ((hdw _ hs).differentiableAt (hU.mem_nhds hs)).congr_of_eventuallyEq hev
      -- Diagonal evaluation against the fixed family `fun _ => e` is a continuous linear
      -- functional, so `F x = D^m u x [e, ..., e]` is differentiable with the flipped derivative.
      have hF : HasFDerivAt (fun y : Plane => iteratedFDeriv ℝ m u y (fun _ => e))
          ((fderiv ℝ (iteratedFDeriv ℝ m u) (x₀ + s • e)).flipMultilinear fun _ => e)
          (x₀ + s • e) :=
        hdiff.hasFDerivAt.continuousMultilinear_apply_const _
      have hpath : HasDerivAt (fun r : ℝ => x₀ + r • e) e s := by
        have h1 : HasDerivAt (fun r : ℝ => r • e) e s := by
          simpa using (hasDerivAt_id s).smul_const e
        simpa using h1.const_add x₀
      have hcomp := hF.comp_hasDerivAt s hpath
      -- The order-`m` identity holds on the open parameter set, hence near `s`.
      have hEq : iteratedDeriv m (fun r : ℝ => u (x₀ + r • e))
          =ᶠ[nhds s]
            (fun y : Plane => iteratedFDeriv ℝ m u y (fun _ => e)) ∘ fun r : ℝ => x₀ + r • e :=
        Filter.eventuallyEq_of_mem (hIopen.mem_nhds hs) fun r hr => ih hum' r hr
      rw [iteratedDeriv_succ, hEq.deriv_eq, hcomp.deriv, iteratedFDeriv_succ_apply_left]
      rfl
  exact key j hu t ht
