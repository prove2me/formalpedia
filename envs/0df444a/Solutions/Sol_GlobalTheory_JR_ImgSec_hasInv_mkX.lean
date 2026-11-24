-- Prove2me | solution 1 for GlobalTheory.JR.ImgSec.hasInv_mkX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:31:16.566398+00:00
-- url     : https://prove2.me/submissions/4fd37bac-1cb9-4b2f-b599-d368b7fbdf6c

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
import Theorems.Thm_GlobalTheory_JR_ImgSec_charpoly_companion_coeff
import Theorems.Thm_GlobalTheory_JR_ImgSec_mkX_fst
import Theorems.Thm_GlobalTheory_JR_ImgSec_mom_mkX
import Theorems.Thm_GlobalTheory_JR_NormalFormL_charpoly_companion_coeff


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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}
namespace GlobalTheory.JR.ImgSec
theorem _root_.solution {a : Inv r F} {h : Matrix (Fin r) (Fin r) E} (hh : hᴴ * h = (hankel a).map (algebraMap F E))
    (hd : IsUnit h.det) : HasInv (mkX a h) a := by
  unfold HasInv inv
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    show ((mkX a h).1.1).charpoly.coeff i = algebraMap F E (a.1 i)
    rw [mkX_fst hh hd]
    let u : (Matrix (Fin r) (Fin r) E)ˣ := Matrix.nonsingInvUnit h hd
    have e : h * (companion a.1).map (algebraMap F E) * h⁻¹ =
        (u : Matrix (Fin r) (Fin r) E) * (companion a.1).map (algebraMap F E) *
          (u : Matrix (Fin r) (Fin r) E)⁻¹ := rfl
    rw [e, Matrix.charpoly_units_conj, Matrix.charpoly_map, Polynomial.coeff_map, charpoly_companion_coeff]
  · funext i; exact mom_mkX hh hd i
  · rfl
end GlobalTheory.JR.ImgSec
