-- Prove2me | solution 1 for GlobalTheory.exists_minimal_local_generators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:49.726917+00:00
-- url     : https://prove2.me/submissions/87d4140f-0392-421b-a6f7-3d027ea826b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMulMemOfForall
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMinimalLocalGenerators
import Theorems.Thm_GlobalTheory_MultipleMembershipForAll_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (Q : Ideal S) [Q.IsPrime],
      ∃ (h : ℕ) (f : Fin h → S) (g : S), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧
        (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧
        h = (maximalIdeal (Localization.AtPrime Q)).spanFinrank ∧
        ∀ (a : Fin h → S) (u : S), u ∉ Q → u * ∑ j, a j * f j ∈ Q ^ 2 → ∀ j, a j ∈ Q := by
  first
  | exact @_root_.GlobalTheory.MultipleMembershipForAll.main
  | exact _root_.GlobalTheory.MultipleMembershipForAll.main
  | (apply _root_.GlobalTheory.MultipleMembershipForAll.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.MultipleMembershipForAll.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MultipleMembershipForAll.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MultipleMembershipForAll.main ..)
end GlobalTheory
