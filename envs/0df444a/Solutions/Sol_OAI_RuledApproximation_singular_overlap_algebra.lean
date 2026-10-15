-- Prove2me | solution 1 for OAI.RuledApproximation.singular_overlap_algebra
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:37:31.899671+00:00
-- url     : https://prove2.me/submissions/248bb13c-b998-4dbb-b09d-23b9ede325da

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularOverlap.lean:L102-L200
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singular_overlap_algebra. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField

-- ---- from OAI.Geometry.RuledCovering.SingularOverlap ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma ceiling_P_identity (p x y : ℝ) :
    ceilingPolynomial p x + ceilingPolynomial p y -
      x^2*(p/4+(2-p)*y^2)-y^2*(p/4+(2-p)*x^2) = (2-p)*(x^2-y^2)^2 := by
  unfold ceilingPolynomial
  ring

lemma abs_unit_mul_le {x A B : ℝ} (hx : |x| ≤ 1) (hA : |A| ≤ B) :
    |x*A| ≤ B := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right hx (abs_nonneg A)).trans (by simpa using hA)

lemma singular_overlap_algebra {p K c x y bm bp rm rp Pm Pp Qm Qp : ℝ}
    (hp2 : p ≤ 2) (hK : 1 ≤ K) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcK : c*K ≤ 1/2) (hcsmall : 16*K^2*c^3 ≤ 2*c^(5/2:ℝ))
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hrm : 1/2 ≤ rm) (hrp : 1/2 ≤ rp)
    (hPm : |Pm| ≤ K) (hPp : |Pp| ≤ K)
    (hQm : |Qm-bm| ≤ K*(rm-1/2)) (hQp : |Qp-bp| ≤ K*(rp-1/2))
    (hPmy : |Pm-(p/4+(2-p)*y^2)| ≤ K*(|bm-y|+(rm-1/2)))
    (hPpx : |Pp-(p/4+(2-p)*x^2)| ≤ K*(|bp-x|+(rp-1/2)))
    (hdm : |ceilingPolynomial p bm-ceilingPolynomial p y| ≤ K*|bm-y|)
    (hdp : |ceilingPolynomial p bp-ceilingPolynomial p x| ≤ K*|bp-x|)
    (hbm : bm=y-c*x*Pm) (hbp : bp=x+c*y*Pp)
    (hsum : rm+rp=1+c*(y*Qp-x*Qm)) :
    rm ≤ 1/2+c^2*ceilingPolynomial p bm+c^(5/2:ℝ) ∨
    rp ≤ 1/2+c^2*ceilingPolynomial p bp+c^(5/2:ℝ) := by
  have hKn : 0 ≤ K := by linarith
  have hxs : |x^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg x)]; nlinarith only [(abs_le.mp hx).1,(abs_le.mp hx).2]
  have hys : |y^2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg y)]; nlinarith only [(abs_le.mp hy).1,(abs_le.mp hy).2]
  have hbm' : |bm-y| ≤ c*K := by
    rw [hbm,sub_sub_cancel_left,abs_neg,abs_mul,abs_mul,abs_of_nonneg hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_unit_mul_le hx hPm) hc
  have hbp' : |bp-x| ≤ c*K := by
    rw [hbp,add_sub_cancel_left,abs_mul,abs_mul,abs_of_nonneg hc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (by simpa only [abs_mul] using abs_unit_mul_le hy hPp) hc
  let D := rm+rp-1
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hEd : |y*(Qp-bp)-x*(Qm-bm)| ≤ K*D := by
    calc
      _ ≤ |y*(Qp-bp)|+|x*(Qm-bm)| := abs_sub _ _
      _ ≤ K*(rp-1/2)+K*(rm-1/2) := add_le_add (abs_unit_mul_le hy hQp) (abs_unit_mul_le hx hQm)
      _ = _ := by dsimp [D]; ring
  have hPe : |y^2*Pp+x^2*Pm| ≤ 2*K := by
    calc
      _ ≤ |y^2*Pp|+|x^2*Pm| := abs_add_le _ _
      _ ≤ K+K := add_le_add (abs_unit_mul_le hys hPp) (abs_unit_mul_le hxs hPm)
      _ = _ := by ring
  have hDeq : D=c^2*(y^2*Pp+x^2*Pm)+c*(y*(Qp-bp)-x*(Qm-bm)) := by
    dsimp [D]
    rw [hsum,hbm,hbp]
    ring
  have hDb : D ≤ 4*K*c^2 := by
    have hu : D ≤ c^2*(2*K)+c*(K*D) := by
      calc
        D = c^2*(y^2*Pp+x^2*Pm)+c*(y*(Qp-bp)-x*(Qm-bm)) := hDeq
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hPe) (sq_nonneg c))
          (mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hEd) hc)
    have hmul := mul_le_mul_of_nonneg_right hcK hD
    nlinarith only [hmul,hu]
  have hrmb : rm-1/2 ≤ 4*K*c^2 := by dsimp [D] at hDb; linarith
  have hrpb : rp-1/2 ≤ 4*K*c^2 := by dsimp [D] at hDb; linarith
  have hc2 : c^2 ≤ c := by nlinarith only [hc,hc1]
  have hPmy' : |Pm-(p/4+(2-p)*y^2)| ≤ 5*K^2*c := by
    apply hPmy.trans
    calc
      _ ≤ K*(c*K+4*K*c^2) := mul_le_mul_of_nonneg_left (add_le_add hbm' hrmb) hKn
      _ ≤ K*(c*K+4*K*c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4*K))) hKn
      _ = _ := by ring
  have hPpx' : |Pp-(p/4+(2-p)*x^2)| ≤ 5*K^2*c := by
    apply hPpx.trans
    calc
      _ ≤ K*(c*K+4*K*c^2) := mul_le_mul_of_nonneg_left (add_le_add hbp' hrpb) hKn
      _ ≤ K*(c*K+4*K*c) := mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc2 (by positivity : 0 ≤ 4*K))) hKn
      _ = _ := by ring
  let A := x^2*(p/4+(2-p)*y^2)+y^2*(p/4+(2-p)*x^2)
  have hAe : |y^2*Pp+x^2*Pm-A| ≤ 10*K^2*c := by
    calc
      _ = |y^2*(Pp-(p/4+(2-p)*x^2))+x^2*(Pm-(p/4+(2-p)*y^2))| := by dsimp [A]; congr 1; ring
      _ ≤ |y^2*(Pp-(p/4+(2-p)*x^2))|+|x^2*(Pm-(p/4+(2-p)*y^2))| := abs_add_le _ _
      _ ≤ 5*K^2*c+5*K^2*c := add_le_add (abs_unit_mul_le hys hPpx') (abs_unit_mul_le hxs hPmy')
      _ = _ := by ring
  have hDelta : D ≤ c^2*A+14*K^2*c^3 := by
    have hh : D-c^2*A ≤ c^2*(10*K^2*c)+c*(K*(4*K*c^2)) := by
      calc
        _ = c^2*(y^2*Pp+x^2*Pm-A)+c*(y*(Qp-bp)-x*(Qm-bm)) := by rw [hDeq]; ring
        _ ≤ c^2*(10*K^2*c)+c*(K*D) := add_le_add
          (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hAe) (sq_nonneg c))
          (mul_le_mul_of_nonneg_left ((le_abs_self _).trans hEd) hc)
        _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDb hKn) hc)
    nlinarith only [hh]
  have hdm' : ceilingPolynomial p y-K^2*c ≤ ceilingPolynomial p bm := by
    have hh := hdm.trans (mul_le_mul_of_nonneg_left hbm' hKn)
    have hh' := (abs_le.mp hh).1
    nlinarith only [hh']
  have hdp' : ceilingPolynomial p x-K^2*c ≤ ceilingPolynomial p bp := by
    have hh := hdp.trans (mul_le_mul_of_nonneg_left hbp' hKn)
    have hh' := (abs_le.mp hh).1
    nlinarith only [hh']
  have hAid : A ≤ ceilingPolynomial p y+ceilingPolynomial p x := by
    have hh := ceiling_P_identity p x y
    have hz : 0 ≤ (2-p)*(x^2-y^2)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    dsimp [A]
    linarith
  by_contra h
  push Not at h
  have hfail : c^2*(ceilingPolynomial p bm+ceilingPolynomial p bp)+2*c^(5/2:ℝ) < D := by
    dsimp [D]
    linarith [h.1,h.2]
  have hdlow : A-2*K^2*c ≤ ceilingPolynomial p bm+ceilingPolynomial p bp := by linarith
  have hh := mul_le_mul_of_nonneg_left hdlow (sq_nonneg c)
  nlinarith only [hh,hfail,hDelta,hcsmall]

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singular_overlap_algebra := @_root_.OAI.RuledApproximation.singular_overlap_algebra
