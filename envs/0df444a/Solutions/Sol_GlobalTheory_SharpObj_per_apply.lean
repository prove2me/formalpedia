-- Prove2me | solution 1 for GlobalTheory.SharpObj.per_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:46:56.534369+00:00
-- url     : https://prove2.me/submissions/4bbe0427-d322-4f6c-a794-4f6816a2ad67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SharpObj
variable {h : ℕ}
namespace GlobalTheory.SharpObj
theorem _root_.solution (τ : Matrix (Fin h) (Fin h) ℂ) (x : Fin h ⊕ Fin h → ℤ) (i : Fin h) :
    per τ x i = τ.mulVec (fun i' => (x (.inl i') : ℂ)) i + (x (.inr i) : ℂ) := rfl
end GlobalTheory.SharpObj
