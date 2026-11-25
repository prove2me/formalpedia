-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.WD.lpSum_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:55:46.657618+00:00
-- url     : https://prove2.me/submissions/35fe76d0-ae47-44d7-8ead-a065beac278a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]
open GlobalTheory.WeilDeligne.WD
variable {h : IsPlaceOver A w}
variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
namespace GlobalTheory.WeilDeligne.WD
theorem _root_.solution (a : WDRep h V) (b : WDRep h V') :
    lpSum (mk a) (mk b) = mk (a.sum b) :=
  sound ((iso_std a).sum (iso_std b)).symm
end GlobalTheory.WeilDeligne.WD
