-- Prove2me | solution 1 for GlobalTheory.T.wedge_of_symmetric_tensor_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:25:48.07627+00:00
-- url     : https://prove2.me/submissions/bf8b8c26-341d-433a-a467-0338107d877d

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZeroStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_eq_zero_of_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Projective R V] (t : V ⊗[R] V), t - TensorProduct.comm R V V t = 0 → wedgeT (R := R) V t = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm | exact GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm | (intros; apply GlobalTheory.CompanionTheory.WedgeOf.wedgeT_eq_zero_of_symm <;> assumption)
end _root_.GlobalTheory.T
