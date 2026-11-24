-- Prove2me | solution 1 for GlobalTheory.HeckeGal.IsLAdicOf.dec_triv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:05:49.861793+00:00
-- url     : https://prove2.me/submissions/cd914f70-2a17-4f12-903a-b26fea5b5393

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_toAb_surjective
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_loc_away
import Theorems.Thm_GlobalTheory_HeckeGal_liftAb_toAb
import Theorems.Thm_GlobalTheory_HeckeGal_continuous_liftAb

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
namespace IsLAdicOf
theorem _root_.solution {art : Ideles E →* Gab E Ω} {ι : Qbar l ≃+* ℂ} {χ : HChar E} {n : (E →+* ℂ) → ℤ}
    {r : G E Ω →* (Qbar l)ˣ} {v : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (ha : IsGlobalArtin art) (h : IsLAdicOf art ι χ n r) (hr : Continuous r)
    (hv : ((l : ℕ) : 𝓞 E) ∉ v.asIdeal ∨ n = 0) (hA : IsPlaceOver A v) :
    (∀ σ ∈ Dec (F := E) A, r σ = 1) ↔ χ.loc v = 1 := by
  constructor
  · intro H
    ext x
    have hm : art (localIdele E v x) ∈ (Dec (F := E) A).map (toAb E Ω) := by
      rw [← ha.dec v A hA]
      exact Subgroup.le_topologicalClosure _ ⟨x, rfl⟩
    obtain ⟨σ, hσ, e⟩ := hm
    have e2 := h.loc_away hv x σ e.symm
    rw [H σ hσ, Units.val_one, eq_comm, map_eq_one_iff _ ι.symm.injective] at e2
    exact e2
  · intro H σ hσ
    have hm : toAb E Ω σ ∈ (art.comp (localIdele E v)).range.topologicalClosure := by
      rw [ha.dec v A hA]
      exact ⟨σ, hσ, rfl⟩
    have hle : (art.comp (localIdele E v)).range ≤ (liftAb r hr).ker := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨τ, hτ⟩ := toAb_surjective (art (localIdele E v x))
      have e2 := h.loc_away hv x τ hτ.symm
      rw [H, MonoidHom.one_apply, Units.val_one, map_one] at e2
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← hτ, liftAb_toAb]
      exact Units.ext e2
    exact Subgroup.topologicalClosure_minimal _ hle
      (isClosed_singleton.preimage (continuous_liftAb r hr)) hm
end IsLAdicOf
end GlobalTheory.HeckeGal
