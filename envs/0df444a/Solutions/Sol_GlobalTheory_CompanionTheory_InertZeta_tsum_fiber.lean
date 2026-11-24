-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.InertZeta.tsum_fiber
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:41:44.451931+00:00
-- url     : https://prove2.me/submissions/6598ce63-6e01-445c-9660-b22025857d27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DoubleCosetSwap
import Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_dosetOf_eq_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.CompanionTheory.InertZeta
theorem _root_.solution {M : Type} [AddCommMonoid M] [TopologicalSpace M] (hK : IsCommensurated K) (x : G ⧸ K)
    (h : G ⧸ K → M) : ∑' c : {y : G ⧸ K // dosetOf y = dosetOf x}, h c = ∑ y ∈ cosetsIn hK x.out, h y := by
  rw [← Finset.tsum_subtype (cosetsIn hK x.out) h]
  exact (Equiv.subtypeEquivRight
    (fun y => (dosetOf_eq_iff (hK := hK) (x := x) (y := y)))).tsum_eq (fun c => h c.1)
end GlobalTheory.CompanionTheory.InertZeta
