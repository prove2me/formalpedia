-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.mem_Weil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:12:03.874882+00:00
-- url     : https://prove2.me/submissions/3fab5f99-d45b-4a48-b93b-e39b42048c34

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
theorem _root_.solution {σ : G E Ω} : σ ∈ Weil h ↔ ∃ a b, ActsAs A (normV w) σ a b := Iff.rfl
end GlobalTheory.WeilDeligne
