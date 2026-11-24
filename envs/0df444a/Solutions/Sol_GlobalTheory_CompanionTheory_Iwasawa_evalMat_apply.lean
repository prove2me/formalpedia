-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwasawa.evalMat_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:44.358229+00:00
-- url     : https://prove2.me/submissions/2f31445e-393a-4fd6-8a3a-5bd4c58637da

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUpperMulUnitaryComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwasawa
namespace GlobalTheory.CompanionTheory.Iwasawa
theorem _root_.solution {ι : Type} {n : ℕ} (w : ι) (X : Matrix (Fin n) (Fin n) (ι → ℂ))
    (i j : Fin n) : evalMat w X i j = X i j w := rfl
end GlobalTheory.CompanionTheory.Iwasawa
