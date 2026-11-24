-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.ine_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:05:53.62457+00:00
-- url     : https://prove2.me/submissions/a80e6cbb-4dae-4346-a29c-f1b4a341ce31

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_loc_away

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
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) (z : Qbar l) :
    (∃ σ ∈ Ine (F := E) A, ((r σ : (Qbar l)ˣ) : Qbar l) = z) ↔
      ∃ x, IsUnitAt v x ∧ ι.symm ((χ.loc v x : ℂˣ) : ℂ) = z := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨x, hx, e⟩ := (ha.ine v A hA _).mpr ⟨σ, hσ, rfl⟩
    exact ⟨x, hx, (h.loc_away hv x σ e).symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨σ, hσ, e⟩ := (ha.ine v A hA _).mp ⟨x, hx, rfl⟩
    exact ⟨σ, hσ, h.loc_away hv x σ e.symm⟩
end IsLAdicOf
end GlobalTheory.HeckeGal
