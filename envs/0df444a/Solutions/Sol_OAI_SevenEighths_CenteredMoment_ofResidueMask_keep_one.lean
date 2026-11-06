-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMoment.ofResidueMask_keep_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:34:48.384609+00:00
-- url     : https://prove2.me/submissions/7cded139-c2b1-4629-81bc-a3a8246615ac

import Mathlib.NumberTheory.MulChar.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Group.Commute.Units
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Basic

set_option autoImplicit false
open OAI
open scoped BigOperators NNReal
open OAI.SevenEighths OAI.SevenEighths.CenteredMoment
noncomputable section
variable {M R : Type*} [CommMonoid M] [CommRing R]
namespace OAI.SevenEighths.CenteredMoment
theorem _root_.solution {S : Type*} [CommRing S]
    (ρ : M →* R) (χ : MulChar R ℂ) (puncture : M →* S) :
    (ofResidueMask ρ χ puncture).keep 1 := by
  change IsUnit (puncture 1)
  simp only [map_one, isUnit_one]
end OAI.SevenEighths.CenteredMoment
