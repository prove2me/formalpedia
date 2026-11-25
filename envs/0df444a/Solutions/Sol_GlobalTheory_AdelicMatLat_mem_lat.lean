-- Prove2me | solution 1 for GlobalTheory.AdelicMatLat.mem_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:25:23.04523+00:00
-- url     : https://prove2.me/submissions/73a2f838-3bf7-4c03-a1e1-8e53b5d8cd9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsLatticeAdelicMatrixIntegralTranslate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.AdelicMatLat
variable (E : Type) [Field E] [NumberField E]
variable {E} {n : ℕ}
namespace GlobalTheory.AdelicMatLat
theorem _root_.solution {β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)} {x : Fin n → E} :
    x ∈ lat β ↔
      ∀ j, ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β k j ∈ intAdeles E := Iff.rfl
end GlobalTheory.AdelicMatLat
