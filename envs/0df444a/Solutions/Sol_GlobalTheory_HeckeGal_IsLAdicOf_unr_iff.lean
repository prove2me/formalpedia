-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.unr_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:24:51.625923+00:00
-- url     : https://prove2.me/submissions/9c684948-2f15-4ca9-8126-5b7bc59ba975

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_ine_image

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
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) :
    (∀ σ ∈ Ine (F := E) A, r σ = 1) ↔ χ.UnrAt v := by
  constructor
  · intro H x hx
    obtain ⟨σ, hσ, e⟩ := (h.ine_image ha hv hA _).mpr ⟨x, hx, rfl⟩
    rw [H σ hσ, Units.val_one, eq_comm, map_eq_one_iff _ ι.symm.injective] at e
    exact Units.ext e
  · intro H σ hσ
    obtain ⟨x, hx, e⟩ := (h.ine_image ha hv hA _).mp ⟨σ, hσ, rfl⟩
    rw [H x hx, Units.val_one, map_one] at e
    exact Units.ext e.symm
end IsLAdicOf
end GlobalTheory.HeckeGal
