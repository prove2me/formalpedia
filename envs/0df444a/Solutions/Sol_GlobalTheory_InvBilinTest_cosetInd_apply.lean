-- Prove2me | solution 1 for GlobalTheory.InvBilinTest.cosetInd_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:43:10.759685+00:00
-- url     : https://prove2.me/submissions/6b30a229-9b27-466d-8af0-7a83e889aac9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantCosetInd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace
noncomputable section
open GlobalTheory GlobalTheory.InvBilinTest
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
open Classical
namespace GlobalTheory.InvBilinTest
theorem _root_.solution (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (g x : G) : (cosetInd K ho hK g).1 x = if x * g⁻¹ ∈ K then 1 else 0 := rfl
end GlobalTheory.InvBilinTest
