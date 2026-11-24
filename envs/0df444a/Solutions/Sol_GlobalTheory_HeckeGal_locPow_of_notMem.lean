-- Prove2me | solution 1 for GlobalTheory.HeckeGal.locPow_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:35:08.233818+00:00
-- url     : https://prove2.me/submissions/6db44a61-3757-4fbb-9ffe-383222400532

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_isEmpty_contEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory GlobalTheory.HeckeGal
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.HeckeGal
theorem _root_.solution (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ) {v : HeightOneSpectrum (𝓞 E)}
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal) (y : v.adicCompletion E) : locPow ι n v y = 1 := by
  have := isEmpty_contEmb (l := l) hv
  exact finprod_of_isEmpty _
end GlobalTheory.HeckeGal
