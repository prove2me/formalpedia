-- Prove2me | solution 1 for GlobalTheory.UnRep.NormOne.exists_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:18:17.086101+00:00
-- url     : https://prove2.me/submissions/4f7e195f-f2f2-47c8-899d-2bf0ec43a563

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ValuationEqOneOfNormOneOfNotMoved
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsDenominatorPrimesPrescribed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_NormOneApproximationAtLevelPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.NormOne
variable {E : Type} [Field E] [NumberField E]
variable {F : Type} [Field F] [Algebra F E]
omit [NumberField E]
namespace GlobalTheory.UnRep.NormOne
theorem _root_.solution (c : E ≃ₐ[F] E) (x : 𝓞 E) : ∃ y : 𝓞 E, (y : E) = c x :=
  ⟨⟨c x, (RingOfIntegers.isIntegral_coe x).map (c : E →+* E).toIntAlgHom⟩, rfl⟩
end GlobalTheory.UnRep.NormOne
