-- Prove2me | solution 1 for GlobalTheory.Published.HeckeLAdicCharacter.full
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:41:28.6358+00:00
-- url     : https://prove2.me/submissions/9fba0fdc-ce92-4052-a716-28693e163efa

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Theorems.Thm_GlobalTheory_HeckeGal_isAlgPos_of_isAlg
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_unique
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_ine_image
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_unr_iff
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_frob_unr
import Theorems.Thm_GlobalTheory_HeckeGal_exists_unique_hchar_of_finite_order
import Theorems.Thm_GlobalTheory_HeckeGal_isAlgPos_zero_of_orderDvd
import Theorems.Thm_GlobalTheory_HeckeGal_IsLAdicOf_pow_eq_one

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
open GlobalTheory GlobalTheory.Published
open GlobalTheory.HeckeGal
namespace GlobalTheory.Published
namespace HeckeLAdicCharacter
theorem _root_.solution (H : HeckeLAdicCharacter) (E Ω : Type) [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] :
    ∃ art : Ideles E →* Gab E Ω, IsGlobalArtin art ∧ ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ),
      (∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), χ.IsAlg n →
        ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r ∧
          (∀ r', IsLAdicOf art ι χ n r' → r' = r) ∧
          ∀ v : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∉ v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
            (∀ z : Qbar l, (∃ σ ∈ Ine (F := E) A, ((r σ : (Qbar l)ˣ) : Qbar l) = z) ↔
              ∃ x, IsUnitAt v x ∧ ι.symm ((χ.loc v x : ℂˣ) : ℂ) = z) ∧
            ((∀ σ ∈ Ine (F := E) A, r σ = 1) ↔ χ.UnrAt v) ∧
            (χ.UnrAt v → ∀ σ : G E Ω, IsFrob (F := E) A (normV v) σ →
              ((r σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val v : ℂˣ) : ℂ))⁻¹)) ∧
      (∀ m : ℕ, 0 < m → ∀ χ : HChar E, χ.OrderDvd m →
        ∃! r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ r ^ m = 1 ∧ IsLAdicOf art ι χ 0 r) ∧
      (∀ m : ℕ, 0 < m → ∀ r : G E Ω →* (Qbar l)ˣ, Continuous r → r ^ m = 1 →
        ∃! χ : HChar E, χ.OrderDvd m ∧ IsLAdicOf art ι χ 0 r) := by
  obtain ⟨art, ha, h⟩ := H E Ω
  refine ⟨art, ha, fun l _ ι => ⟨fun χ n hn => ?_, fun m hm χ hχ => ?_,
    fun m hm r hr hrm => exists_unique_hchar_of_finite_order ha ι r hr hm hrm⟩⟩
  · obtain ⟨r, ⟨hr, hf⟩, -⟩ := h l ι χ n (isAlgPos_of_isAlg hn)
    exact ⟨r, hr, hf, fun r' h' => h'.unique ha.quot.surjective hf, fun v hv A hA =>
      ⟨hf.ine_image ha (Or.inl hv) hA, hf.unr_iff ha (Or.inl hv) hA,
        fun hu σ hσ => hf.frob_unr ha (Or.inl hv) hu hA hσ⟩⟩
  · obtain ⟨r, ⟨hr, hf⟩, -⟩ := h l ι χ 0 (isAlgPos_zero_of_orderDvd hm hχ)
    exact ⟨r, ⟨hr, hf.pow_eq_one ha.quot.surjective hχ, hf⟩,
      fun r' h' => h'.2.2.unique ha.quot.surjective hf⟩
end HeckeLAdicCharacter
end GlobalTheory.Published
