-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.frobEig_lpSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:40:20.309969+00:00
-- url     : https://prove2.me/submissions/369ffd10-e2a2-46c8-aa83-3c00983292e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_lpSum_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.lpSum_mk



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne.WD
open Unram
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (a b : WD h) : frobEig (lpSum a b) = frobEig a + frobEig b := by
  induction a using ind with
  | hP n a =>
  induction b using ind with
  | hP m b =>
    rw [lpSum_mk, frobEig_mk, frobEig_mk, frobEig_mk, WDRep.sum_ρ, LinearMap.charpoly_prodMap,
      roots_mul (mul_ne_zero (LinearMap.charpoly_monic _).ne_zero
        (LinearMap.charpoly_monic _).ne_zero)]
end GlobalTheory.WeilDeligne.WD
