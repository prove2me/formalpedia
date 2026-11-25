-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.compactSpace_Ine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:11:35.470056+00:00
-- url     : https://prove2.me/submissions/58b106ae-fbbf-4dfb-96b5-aa636d313076

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Theorems.Thm_ReciprocityTheory_Gal_isClosed_Ine


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
variable {h}
variable [IsAlgClosure E Ω]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution (A : ValuationSubring Ω) : CompactSpace (Ine (F := E) A) := by
  have : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  exact isCompact_iff_compactSpace.mp (isClosed_Ine A).isCompact
end GlobalTheory.WeilDeligne
