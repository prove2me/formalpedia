-- Prove2me | solution 1 for MechanismDesign.SocialChoice.monotone_respectsUnanimity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:24:11.860927+00:00
-- url     : https://prove2.me/submissions/ea418432-eba9-4189-8613-00980e5700a8

import Mathlib
import Definitions.Def_MechanismDesign_SocialChoice_Model

set_option autoImplicit false
open MechanismDesign.SocialChoice

theorem solution {ι A : Type*} [Fintype ι] [Fintype A]
    (f : DirectMechanism ι A) (hf : IsMonotone f) (hrange : Function.Surjective f) :
    RespectsUnanimity f := by
  intro R a hR
  obtain ⟨R0, hR0⟩ := hrange a
  exact hf R0 R a hR0 (fun i b _ => hR i b)
