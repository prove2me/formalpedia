-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.unr_mono0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:40:25.301293+00:00
-- url     : https://prove2.me/submissions/d4d9a45b-e43a-4591-a5c3-8f14519ba6ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsEquivOfMapEq
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_ind
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_unr_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.WD.unr_mk



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
open GlobalTheory.WeilDeligne.WD
open Unram
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (a : WD h) (ha : unr a) : mono0 a := by
  induction a using ind with
  | hP n a => exact (monodromyZero_ofWeilDeligneRepClass_iff a).mpr ((unr_mk a).mp ha).1
end GlobalTheory.WeilDeligne.WD
