-- Prove2me | solution 1 for GlobalTheory.JR.HermInv.pow_r_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:59:50.660928+00:00
-- url     : https://prove2.me/submissions/291705af-b4cb-4577-bb89-144618e00ae8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitive
import Theorems.Thm_GlobalTheory_JR_HermInv_pow_r_mulVec
import Theorems.Thm_GlobalTheory_JR_HermInv_hasInv_iff

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
theorem _root_.solution (X : Hn r F E) (a : Inv r F) (h : HasInv X a) :
    X.1.1 ^ r *ᵥ X.2.1 = -(Bm X.toGl *ᵥ fun i => algebraMap F E (a.1 i)) := by
  obtain ⟨h1, -, -⟩ := (hasInv_iff X a).1 h
  have := pow_r_mulVec X.toGl
  rwa [show (fun i : Fin r => X.toGl.1.charpoly.coeff i) = fun i => algebraMap F E (a.1 i) from funext h1] at this
end GlobalTheory.JR.HermInv
