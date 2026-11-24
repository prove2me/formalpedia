-- Prove2me | solution 1 for GlobalTheory.ProjModFinIso.finrank_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:38:49.56202+00:00
-- url     : https://prove2.me/submissions/a35bd18e-e9cc-4432-9524-f0a4ea49810c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.ProjModFinIso
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.ProjModFinIso
theorem _root_.solution (I : Ideal R) (h : I ≠ ⊥) : Module.finrank R I = 1 := by
  have h1 : Module.finrank R I ≤ 1 := by simpa using Submodule.finrank_le I
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr h
  have h2 := Module.finrank_pos (R := R) (M := I)
  omega
end GlobalTheory.ProjModFinIso
