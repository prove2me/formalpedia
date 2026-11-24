-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:05:58.589246+00:00
-- url     : https://prove2.me/submissions/d0bc93c8-8df5-46e6-85db-8668b49f35b5

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
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) {σ : G E Ω}
    (hσ : IsFrob (F := E) A (normV v) σ) :
    ∃ x, IsUnifAt v x ∧ ((r σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.loc v x : ℂˣ) : ℂ))⁻¹ := by
  obtain ⟨x, hx, e⟩ := (ha.frob v A hA _).mpr ⟨σ, hσ, rfl⟩
  refine ⟨x, hx, ?_⟩
  rw [← h.loc_away hv x _ e, map_inv, Units.val_inv_eq_inv_val, inv_inv]
end IsLAdicOf
end GlobalTheory.HeckeGal
