-- Prove2me | solution 1 for GlobalTheory.IsAdicFamily.of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:31:57.005889+00:00
-- url     : https://prove2.me/submissions/12fe7360-9ef0-4420-ae9d-4790d4e333c7

import Theorems.Thm_GlobalTheory_adicLevelMap_comp
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_adicLevelMap_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GlobalTheory.adicLevelMap_comp
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {I}
namespace GlobalTheory
namespace IsAdicFamily
theorem _root_.solution {X : Scheme.{u}} {f : ∀ n : ℕ, Spec (.of (R ⧸ I ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily I f) {m n : ℕ} (h : m ≤ n) :
    adicLevelMap I (Nat.succ_le_succ h) ≫ f n = f m := by
  induction n, h using Nat.le_induction with
  | base => rw [adicLevelMap_self, Category.id_comp]
  | succ n h ih => rw [← ih, ← hf n, _root_.GlobalTheory.adicLevelMap_comp_assoc]
end IsAdicFamily
end GlobalTheory
