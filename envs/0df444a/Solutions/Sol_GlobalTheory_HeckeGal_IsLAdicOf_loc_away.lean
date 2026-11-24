-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.loc_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:51:58.764896+00:00
-- url     : https://prove2.me/submissions/a6775333-6aae-42f3-ad6b-61c25962b5bc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_locPow_of_notMem
import Theorems.Thm_GlobalTheory_HeckeGal_locPow_zero

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
variable {art : Ideles E →* Gab E Ω} {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ}
  {r : G E Ω →* (Qbar l)ˣ} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
namespace GlobalTheory.HeckeGal
namespace IsLAdicOf
theorem _root_.solution (h : IsLAdicOf art ι χ n r) (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0)
    (x : (v.adicCompletion E)ˣ) (σ : G E Ω) (hx : art (localIdele E v x) = toAb E Ω σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = ι.symm ((χ.loc v x : ℂˣ) : ℂ) := by
  rw [h.loc x σ hx]
  rcases hv with hv | rfl
  · rw [locPow_of_notMem ι n hv, mul_one]
  · rw [locPow_zero, mul_one]
end IsLAdicOf
end GlobalTheory.HeckeGal
