-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.Weil_le_Dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:51.108115+00:00
-- url     : https://prove2.me/submissions/d1e57db4-6588-4c04-a6ff-063266cdeafc

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable (h : IsPlaceOver A w)
namespace GlobalTheory.WeilDeligne
theorem _root_.solution : Weil h ≤ Dec (F := E) A := fun _ ⟨_, _, hσ⟩ => hσ.1
end GlobalTheory.WeilDeligne
