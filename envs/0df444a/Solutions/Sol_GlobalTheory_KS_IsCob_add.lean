-- Prove2me | solution 1 for GlobalTheory.KS.IsCob.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:09:28.951323+00:00
-- url     : https://prove2.me/submissions/df779a90-5f84-4bcd-9f0a-9aad953cf2fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Theorems.Thm_GlobalTheory_KS_rsT_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
variable {K : Type} [Field K] {Y : Scheme.{0}} {I : Type} {U : I → Y.Opens}
namespace GlobalTheory.KS
namespace IsCob
theorem _root_.solution {c c' : C1 U} (h : IsCob U c) (h' : IsCob U c') : IsCob U (c + c') := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨b', hb'⟩ := h'
  refine ⟨fun i => b i + b' i, fun i j => ?_⟩
  simp only [Pi.add_apply, rsT_add, hb, hb']
  ring
end IsCob
end GlobalTheory.KS
