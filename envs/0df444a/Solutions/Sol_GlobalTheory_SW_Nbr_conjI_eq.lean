-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.conjI_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:10.551878+00:00
-- url     : https://prove2.me/submissions/210ada60-53bd-4d53-a5bc-1e7bc06ca231

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
namespace GlobalTheory.SW.Nbr
theorem _root_.solution (P : Ideal (𝓞 E)) : conjI P = P.map (co (E := E)) := by
  unfold conjI Ideal.map
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, (RingOfIntegers.ext h).symm⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩
end GlobalTheory.SW.Nbr
