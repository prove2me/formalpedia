-- Prove2me | solution 1 for GlobalTheory.CMLattice.embAll_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:27:22.339139+00:00
-- url     : https://prove2.me/submissions/4978a615-c9f5-4754-a911-dfb54631ede4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.CMLattice
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMLattice
theorem _root_.solution (Ψ : Finset (E →+* ℂ)) (r : ℕ) (v : Fin r → E) (τ : Ψ) (a : Fin r) :
    embAll Ψ r v τ a = τ.1 (v a) := rfl
end GlobalTheory.CMLattice
