-- Prove2me | solution 1 for GlobalTheory.T.isOpen_nsmul_adelicCompletionOfVectorSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:16:03.846631+00:00
-- url     : https://prove2.me/submissions/5c865a1e-8b9f-4bfd-9de9-8de48ca42f4d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSet
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenNsmulAdelicCompletionOfVectorSetStatement
import Theorems.Thm_GlobalTheory_AdLat_OpenLat_isOpen_nsmul_hat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Topology Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), Submodule.span E (L : Set (Fin n → E)) = ⊤ → letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) := moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E); (∀ N : ℕ, 0 < N → IsOpen {z : Fin n → RA F E | ∃ y ∈ hat F (L : Set (Fin n → E)), z = N • y}) ∧ ∀ W ∈ 𝓝 (0 : RA F E), ∃ N : ℕ, 0 < N ∧ ∀ y ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), N • y ∈ W := by
  first | exact @GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat | exact GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat | (intros; apply GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat <;> assumption)
end _root_.GlobalTheory.T
