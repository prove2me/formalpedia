-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.isCompact_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:37:13.343823+00:00
-- url     : https://prove2.me/submissions/247b19cc-1710-4226-b4b6-44ae37022a59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryActionHermitianInvariantsTransitiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousCongruenceNearSymmetricMatrixStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CompanionMatrixOfCoeffsCharpolyCoeffEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedMatrixInvariantSpaceExistsCompactOpenSubStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnitaryOrbitProperOfInvertibleKrylovColumnsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOnHermitianBlockMatrixOfInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_InvariantImageOpenClosedLocalSections
import Theorems.Thm_GlobalTheory_T_unitaryOrbit_proper_of_invertible_krylovColumns


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ImgSec
namespace GlobalTheory.JR.ImgSec
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := GlobalTheory.T.unitaryOrbit_proper_of_invertible_krylovColumns
end GlobalTheory.JR.ImgSec
