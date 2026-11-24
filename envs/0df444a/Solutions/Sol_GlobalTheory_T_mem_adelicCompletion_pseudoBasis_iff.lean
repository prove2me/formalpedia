-- Prove2me | solution 1 for GlobalTheory.T.mem_adelicCompletion_pseudoBasis_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:18:23.994674+00:00
-- url     : https://prove2.me/submissions/d04c2e29-cda8-476f-98e5-f775b0406497

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIffStatement
import Theorems.Thm_GlobalTheory_AdLat_mem_hat_pseudoBasis_iff


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (e : Module.Basis (Fin n) E (Fin n → E)) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E), (∀ v, v ∈ L ↔ ∀ a, e.repr v a ∈ cI a) → ∀ z : Fin n → RA F E, (∑ a, z a • fv F (e a)) ∈ (hat F (L : Set (Fin n → E))) ↔ ∀ a, z a ∈ hat1 F (cI a : Set E) := by
  first | exact @GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | exact GlobalTheory.AdLat.mem_hat_pseudoBasis_iff | (intros; apply GlobalTheory.AdLat.mem_hat_pseudoBasis_iff <;> assumption)
end _root_.GlobalTheory.T
