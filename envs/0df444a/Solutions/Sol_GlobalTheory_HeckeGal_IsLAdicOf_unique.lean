-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:18.794738+00:00
-- url     : https://prove2.me/submissions/df89a435-7a3c-434a-af6a-aca022b2740f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04

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
theorem _root_.solution (hs : Function.Surjective art) {r' : G E Ω →* (Qbar l)ˣ}
    (h : IsLAdicOf art ι χ n r) (h' : IsLAdicOf art ι χ n r') : r = r' := by
  ext σ
  obtain ⟨x, hx⟩ := hs (toAb E Ω σ)
  rw [h x σ hx, h' x σ hx]
end IsLAdicOf
end GlobalTheory.HeckeGal
