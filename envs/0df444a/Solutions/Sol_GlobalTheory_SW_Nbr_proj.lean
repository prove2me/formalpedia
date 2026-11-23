-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:52.129918+00:00
-- url     : https://prove2.me/submissions/c09cae8c-0af7-40f5-b47c-885fc71826d1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {Λ : Lt E n} (h : Λ.FG) : Module.Projective (𝓞 E) Λ := by
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr h
  have : Module.Flat (𝓞 E) Λ := inferInstance
  have : Module.FinitePresentation (𝓞 E) Λ := Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation
end GlobalTheory.SW.Nbr
