-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.hasInv_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:25.159527+00:00
-- url     : https://prove2.me/submissions/2fbed8e4-5ece-4ba8-9fb4-06d285084711

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.HermInv
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
variable {r : ℕ}
namespace GlobalTheory.JR.HermInv
theorem _root_.solution (X : Hn r F E) (a : Inv r F) : HasInv X a ↔
    (∀ i : Fin r, X.1.1.charpoly.coeff i = algebraMap F E (a.1 i)) ∧
    (∀ i : Fin r, mom X.toGl i = algebraMap F E (a.2.1 i)) ∧ X.2.2 = a.2.2 := by
  simp only [HasInv, GlobalTheory.JR.inv, Inv.map, Prod.mk.injEq, funext_iff]
  exact and_congr Iff.rfl (and_congr Iff.rfl (algebraMap F E).injective.eq_iff)
end GlobalTheory.JR.HermInv
