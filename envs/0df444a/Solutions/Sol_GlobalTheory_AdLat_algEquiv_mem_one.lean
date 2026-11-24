-- Prove2me | solution 1 for GlobalTheory.AdLat.algEquiv_mem_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:54:16.442822+00:00
-- url     : https://prove2.me/submissions/2ba581a6-4977-4b9e-9c82-198b104dd61f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace GlobalTheory.AdLat
theorem _root_.solution (c : E ≃ₐ[F] E) (x : E) (hx : x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E)) :
    c x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
  rw [FractionalIdeal.mem_one_iff] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  exact ⟨⟨c y, (RingOfIntegers.isIntegral_coe y).map c.toRingEquiv.toRingHom.toIntAlgHom⟩, rfl⟩
end GlobalTheory.AdLat
