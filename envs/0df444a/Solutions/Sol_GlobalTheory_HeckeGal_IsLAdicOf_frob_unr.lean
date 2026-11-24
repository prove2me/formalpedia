-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.frob_unr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:53.1818+00:00
-- url     : https://prove2.me/submissions/5ac6ef5f-ad2d-4eae-8674-275de3d754c3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_frob
import Theorems.Thm_Formalism_L2_Host_HChar_val_eq


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
theorem _root_.solution (ha : IsGlobalArtin art) (h : IsLAdicOf art ι χ n r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hu : χ.UnrAt v) (hA : IsPlaceOver A v) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) :
    ((r σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val v : ℂˣ) : ℂ))⁻¹ := by
  obtain ⟨x, hx, e⟩ := h.frob ha hv hA hσ
  rw [e, χ.val_eq hu x hx]
end IsLAdicOf
end GlobalTheory.HeckeGal
