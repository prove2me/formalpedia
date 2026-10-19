-- Prove2me | solution 1 for OAI.Problem356.ae_branchCoupling
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:14:09.065273+00:00
-- url     : https://prove2.me/submissions/3d0de82a-8749-497f-b3f1-54fd903cb9f4

import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling

open OAI OAI.Problem356
open MeasureTheory
open scoped ENNReal
theorem pb_map_zero {nu : Measure E3} {g : E3 → Triple} (hg : Measurable g)
    {P : Triple → Prop} (hP : MeasurableSet {t | P t}) (h : ∀ᵐ x ∂nu, P (g x)) :
    Measure.map g nu {t | ¬ P t} = 0 := by
  rw [show {t | ¬ P t} = {t | P t}ᶜ from rfl, Measure.map_apply hg hP.compl]
  exact ae_iff.mp h

theorem solution (nu : Measure E3) {H1 H2 H3 H4 : E3 → E3}
    (h1 : Measurable H1) (h2 : Measurable H2) (h3 : Measurable H3)
    (h4 : Measurable H4) {P : Triple → Prop} (hP : MeasurableSet {t | P t})
    (hcycle : ∀ x y z, P (x, (y, z)) → P (y, (z, x)))
    (h12 : ∀ᵐ x ∂nu, P (x, (H1 x, H2 x)))
    (h34 : ∀ᵐ x ∂nu, P (x, (H3 x, H4 x))) :
    ∀ᵐ t ∂branchCoupling nu H1 H2 H3 H4, P t := by
  have hg : ∀ f g h : E3 → E3, Measurable f → Measurable g → Measurable h →
      Measurable (branchGraph f g h) := fun f g h hf hg hh => hf.prodMk (hg.prodMk hh)
  rw [ae_iff]
  simp only [branchCoupling, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  rw [pb_map_zero (hg _ _ _ measurable_id h1 h2) hP h12,
    pb_map_zero (hg _ _ _ h1 h2 measurable_id) hP (h12.mono fun x hx => hcycle _ _ _ hx),
    pb_map_zero (hg _ _ _ h2 measurable_id h1) hP
      (h12.mono fun x hx => hcycle _ _ _ (hcycle _ _ _ hx)),
    pb_map_zero (hg _ _ _ measurable_id h3 h4) hP h34,
    pb_map_zero (hg _ _ _ h3 h4 measurable_id) hP (h34.mono fun x hx => hcycle _ _ _ hx),
    pb_map_zero (hg _ _ _ h4 measurable_id h3) hP
      (h34.mono fun x hx => hcycle _ _ _ (hcycle _ _ _ hx))]
  simp

