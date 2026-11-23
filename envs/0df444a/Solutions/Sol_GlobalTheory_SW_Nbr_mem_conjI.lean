-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.mem_conjI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:20.196205+00:00
-- url     : https://prove2.me/submissions/69970764-78f6-4d73-92a9-b2d71965957a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Theorems.Thm_GlobalTheory_SW_Nbr_co_co
import Theorems.Thm_GlobalTheory_SW_Nbr_conjI_eq

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
theorem _root_.solution {P : Ideal (𝓞 E)} {a : 𝓞 E} : a ∈ conjI P ↔ co a ∈ P := by
  rw [conjI_eq, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rwa [co_co]
  · exact fun h => ⟨_, h, co_co a⟩
end GlobalTheory.SW.Nbr
