-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.continuous_ineConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:09:41.050986+00:00
-- url     : https://prove2.me/submissions/d54195c5-8176-4f05-87b9-66a51d1756e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ToZModPowKummerEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {l : ℕ} [Fact l.Prime]
omit [IsAlgClosure E Ω]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution {h : IsPlaceOver A w} (g : Weil h) : Continuous (ineConj g) :=
  Continuous.subtype_mk (by fun_prop) _
end GlobalTheory.WeilDeligne
