-- Prove2me | solution 1 for MaxwellWiki.integral_div_eq_boxFlux
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T06:28:35.176204+00:00
-- url     : https://prove2.me/submissions/24348dfc-9c95-4878-9e1d-4f770563156e

import Mathlib
import Definitions.Def_MaxwellWiki_Defs

open MaxwellWiki

lemma MaxwellWiki_66ce_div_eq (F : Vec3 → Vec3) (hF : ContDiff ℝ 1 F) (x : Vec3) :
    div F x = ∑ i : Fin 3, fderiv ℝ F x (Pi.single i 1) i := by
  unfold div partialDeriv
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : HasFDerivAt F (fderiv ℝ F x) x :=
    (hF.differentiable one_ne_zero x).hasFDerivAt
  have := (hasFDerivAt_pi'.1 hd) i
  rw [this.fderiv]
  rfl

open MaxwellWiki in
theorem solution (F : Vec3 → Vec3) (hF : ContDiff ℝ 1 F) (a b : Vec3)
    (hab : a ≤ b) :
    ∫ x in Set.Icc a b, div F x = boxFlux F a b := by
  have hcont : Continuous (fun x => ∑ i : Fin 3, fderiv ℝ F x (Pi.single i 1) i) := by
    have hc := hF.continuous_fderiv one_ne_zero
    fun_prop
  simp_rw [MaxwellWiki_66ce_div_eq F hF]
  unfold boxFlux
  exact MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable a b hab F
    (fun x => fderiv ℝ F x) ∅ Set.countable_empty hF.continuous.continuousOn
    (fun x _ => (hF.differentiable one_ne_zero x).hasFDerivAt)
    (hcont.continuousOn.integrableOn_compact isCompact_Icc)
