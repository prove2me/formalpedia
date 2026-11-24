-- Prove2me | solution 1 for GlobalTheory.PadicEmb.exists_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:18:40.640848+00:00
-- url     : https://prove2.me/submissions/68dbd961-4405-4fa5-9c0d-b5695e987503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOneOfFinitePadicIntDomain
import Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_exists_injective_norm_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.PadicEmb
namespace GlobalTheory.PadicEmb
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [IsDomain D]
    [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D], (p : D) ≠ 0 →
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d, ‖φ d‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one
  | exact _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one
  | (apply _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one ..)
end GlobalTheory.PadicEmb
