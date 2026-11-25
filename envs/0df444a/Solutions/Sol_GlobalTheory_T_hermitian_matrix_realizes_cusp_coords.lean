-- Prove2me | solution 1 for GlobalTheory.T.hermitian_matrix_realizes_cusp_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:21:31.101315+00:00
-- url     : https://prove2.me/submissions/4b26cb85-02b5-48e0-962f-2416ac34e75e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HermitianMatrixRealizesCuspCoords
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HermitianMatrixRealizesCuspCoordsStatement
import Theorems.Thm_GlobalTheory_exists_isHermE_phZ_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ m : Fin (nZ X ρ) → ℤ, ∃ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ ∧ ∀ k, phZ X cu χ k = m k := by
  first | exact @GlobalTheory.exists_isHermE_phZ_eq | exact GlobalTheory.exists_isHermE_phZ_eq | (intros; apply GlobalTheory.exists_isHermE_phZ_eq <;> assumption)
end _root_.GlobalTheory.T
