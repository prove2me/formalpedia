-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:03:52.929469+00:00
-- url     : https://prove2.me/submissions/f9cef3fc-0a36-4d4b-b881-18c577774d83

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/BinaryPacket.lean:L103-L117
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_abs_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket

-- ---- from OAI.Analysis.Littlewood.BinaryPacket ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uX

namespace AsymptoticallyMinimalLittlewood
namespace Auxiliary
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI
lemma cosine_abs_le (x : UnitAddCircle) : |cosine x| ≤ 1 := by
  simpa only [cosine, fourier_apply, Circle.norm_coe] using Complex.abs_re_le_norm (fourier 1 x)

lemma binary_abs_le (n : ℕ) (x : Fin n → UnitAddCircle) : |binary n x| ≤ 1 := by
  induction n with
  | zero => simp [binary]
  | succ n ih =>
      have hz := ih (Fin.tail x)
      have hc := cosine_abs_le (x 0)
      have hsq : binary n (Fin.tail x)^2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr hz
      have hcoeff : 0 ≤ (1-binary n (Fin.tail x)^2)/2 := by linarith
      have hstep : (1-binary n (Fin.tail x)^2)/2 ≤ 1-|binary n (Fin.tail x)| := by
        nlinarith [sq_abs (binary n (Fin.tail x)), sq_nonneg (1-|binary n (Fin.tail x)|)]
      calc
        |binary (n+1) x| ≤ |binary n (Fin.tail x)| + |(1-binary n (Fin.tail x)^2)/2*cosine (x 0)| := abs_add_le _ _
        _ = |binary n (Fin.tail x)| + (1-binary n (Fin.tail x)^2)/2*|cosine (x 0)| := by rw [abs_mul, abs_of_nonneg hcoeff]
        _ ≤ |binary n (Fin.tail x)| + (1-binary n (Fin.tail x)^2)/2 := by nlinarith
        _ ≤ 1 := by linarith

open UnitAddTorus

end
end Auxiliary
end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Auxiliary
open MeasureTheory Filter Topology Complex
open scoped BigOperators ComplexConjugate ENNReal
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instMeasureSpaceUnitAddCircle_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsAddHaarMeasureUnitAddCircleVolume_oAI
attribute [local instance] OAI.AsymptoticallyMinimalLittlewood.Auxiliary.instIsProbabilityMeasureUnitAddCircleVolume_oAI


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_abs_le := @_root_.OAI.AsymptoticallyMinimalLittlewood.Auxiliary.binary_abs_le
