-- Prove2me | solution 1 for GlobalTheory.Chevalley.isArtinian_quotient_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:25:46.330134+00:00
-- url     : https://prove2.me/submissions/ca673c23-ed8c-4b68-8504-f21cacbfda04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FiniteCocycles
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MatMapTmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLeMaximalIdealPowSmulOfDirected
import Theorems.Thm_GlobalTheory_Chevalley_isArtinianRing_quotient_maximalIdeal_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Polynomial IsLocalRing GlobalTheory.Pat
open GlobalTheory GlobalTheory.Chevalley
namespace GlobalTheory.Chevalley
theorem _root_.solution (B M : Type) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [AddCommGroup M] [Module B M] [Module.Finite B M] (k : ℕ) :
    IsArtinian B (M ⧸ (maximalIdeal B ^ k • (⊤ : Submodule B M))) := by
  haveI := isArtinianRing_quotient_maximalIdeal_pow B k
  haveI : Module.Finite (B ⧸ maximalIdeal B ^ k) (M ⧸ (maximalIdeal B ^ k • (⊤ : Submodule B M))) :=
    Module.Finite.of_restrictScalars_finite B (B ⧸ maximalIdeal B ^ k) _
  exact isArtinian_of_surjective_algebraMap (R := B ⧸ maximalIdeal B ^ k) Ideal.Quotient.mk_surjective
end GlobalTheory.Chevalley
