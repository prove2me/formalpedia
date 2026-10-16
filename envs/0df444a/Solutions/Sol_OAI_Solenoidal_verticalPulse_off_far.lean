-- Prove2me | solution 1 for OAI.Solenoidal.verticalPulse_off_far
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:18:49.343374+00:00
-- url     : https://prove2.me/submissions/ff59dc98-7c78-4033-b526-f50486f9f075

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Localization.lean:L233-L249
-- (upload_full_project.md Phase 4): solution for node OAI.Solenoidal.verticalPulse_off_far. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Clocks
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Differential
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ScheduledForce
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_ClassicalRegularity
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_EnergyIdentities
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_RectangleGeometry
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Trajectories
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Pulses
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Localization

-- ---- from OAI.MathematicalPhysics.SheetFlows.Profiles ----
namespace OAI

/-! SheetFlows profiles. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

open Filter
open scoped Topology

theorem Cprofile_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10) :
    Cprofile h d c s = plateau h d (s - c) :=
  periodize_on_chart (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => plateau_zero hd) hl hu) hs

theorem Cprofile_zero_on_chart {h d c s : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) (hs : s ∈ Set.Icc 0 10)
    (hsc : h + d ≤ |s - c|) : Cprofile h d c s = 0 := by
  rw [Cprofile_on_chart hd hl hu hs]
  exact plateau_zero hd hsc

end Solenoidal
end
end

end OAI

-- ---- from OAI.MathematicalPhysics.SheetFlows.Localization ----
namespace OAI

/-! SheetFlows localization. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

theorem Rectangle.point_bounds (R : Rectangle) (hR : R.inCodingSquare)
    {y : Plane} (hy : y ∈ R.carrier) (j : Fin 2) : 2 ≤ y j ∧ y j ≤ 3 := by
  have hl : (2:ℝ) ≤ R.lower j := by exact_mod_cast (hR j).1
  have hu : (R.upper j:ℝ) ≤ 3 := by exact_mod_cast (hR j).2
  exact ⟨hl.trans (hy j).1, (hy j).2.trans hu⟩

variable (d : Collar)

theorem verticalPulse_field (R : Rectangle) (hR : R.inCodingSquare) (s : ℝ) (x : Space) :
    (verticalPulse d R hR s).field x =
      (Cprofile (R.halfWidth 0) d.size (R.center 0+s) (x 0) *
        (Cprofile (R.halfWidth 1) d.size (R.center 1) (x 1) -
          Cprofile (R.halfWidth 1) d.size (R.center 1+4) (x 1))) • basis 2 := by
  simp [verticalPulse, StationaryPulse.tensor, tensorVelocity, tensorScalar, Fin.prod_univ_succ]

theorem rect_support_chart (R : Rectangle) (hR : R.inCodingSquare) (j : Fin 2)
    {s : ℝ} (hs : s ∈ Set.Icc 0 4) :
    R.halfWidth j + d.size ≤ R.center j + s ∧
      R.center j + s + (R.halfWidth j + d.size) ≤ 10 := by
  have hw := R.halfWidth_le_half hR j
  have hc := R.center_bounds hR j
  constructor <;> linarith [d.small, hs.1, hs.2]

theorem verticalPulse_off_far (P Q : Rectangle) (hP : P.inCodingSquare)
    (hQ : Q.inCodingSquare) {s t : ℝ} (hs : s ∈ Set.Icc 0 4)
    (ht : t ∈ Set.Icc 0 4) (hst : 4 ≤ |t-s|) {y : Plane} (hy : y ∈ Q.carrier) (z : ℝ) :
    (verticalPulse d P hP s).field (lifted t z y) = 0 := by
  have hc := rect_support_chart d P hP 0 hs
  have hz : Cprofile (P.halfWidth 0) d.size (P.center 0+s) (y 0+t) = 0 := by
    apply Cprofile_zero_on_chart d.positive hc.1 hc.2
    · have hb := Q.point_bounds hQ hy 0
      constructor <;> linarith [ht.1, ht.2, hb.1, hb.2]
    · rcases le_abs.mp hst with hf | hf
      · apply le_abs.mpr (Or.inl ?_)
        linarith [(Q.point_bounds hQ hy 0).1, (P.center_bounds hP 0).2,
          P.halfWidth_le_half hP 0, d.small]
      · apply le_abs.mpr (Or.inr ?_)
        linarith [(Q.point_bounds hQ hy 0).2, (P.center_bounds hP 0).1,
          P.halfWidth_le_half hP 0, d.small]
  simp [verticalPulse_field, lifted, hz]

end Solenoidal
end
end

end OAI

-- ---- platform node ----
open OAI OAI.Solenoidal
open Set MeasureTheory
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Solenoidal.verticalPulse_off_far := @_root_.OAI.Solenoidal.verticalPulse_off_far
