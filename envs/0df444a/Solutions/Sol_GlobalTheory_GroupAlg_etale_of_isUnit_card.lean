-- Prove2me | solution 1 for GlobalTheory.GroupAlg.etale_of_isUnit_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:29:23.642798+00:00
-- url     : https://prove2.me/submissions/ae2456cc-2d25-4904-8b4d-b030aad86322

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Theorems.Thm_GlobalTheory_GroupAlg_formallyUnramified_of_isUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
open GlobalTheory GlobalTheory.GroupAlg
variable (R : Type*) [CommRing R] {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X)
namespace GlobalTheory.GroupAlg
theorem _root_.solution [Finite X] (hn : IsUnit (Nat.card X : R)) : Algebra.Etale R R[X] := by
  have := formallyUnramified_of_isUnit R (X := X) _ hn fun x => card_nsmul_eq_zero'
  have : Module.FinitePresentation R R[X] := Module.finitePresentation_of_projective _ _
  exact Algebra.Etale.of_formallyUnramified_of_flat
end GlobalTheory.GroupAlg
