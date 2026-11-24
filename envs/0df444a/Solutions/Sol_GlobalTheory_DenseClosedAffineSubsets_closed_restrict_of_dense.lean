-- Prove2me | solution 1 for GlobalTheory.DenseClosedAffineSubsets.closed_restrict_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:28:56.682998+00:00
-- url     : https://prove2.me/submissions/ee773bab-d03b-4ff0-9884-a4951aea0060

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
import Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_closed_of_dense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets
namespace GlobalTheory.DenseClosedAffineSubsets
theorem _root_.solution {V X T P Y : Scheme.{0}} (p : T ⟶ P) [IsSeparated p] (ι : X ⟶ T)
    [IsClosedImmersion ι] (j : V ⟶ X) [IsSchemeTheoreticallyDominant j] [QuasiCompact j]
    (D : P.Opens) (y : Y ⟶ D) [IsClosedImmersion y] (e : Y ⟶ T) (he : e ≫ p = y ≫ D.ι)
    (hv : ∀ (Z : Scheme.{0}) (a : Z ⟶ V) (b : Z ⟶ D), a ≫ j ≫ ι ≫ p = b ≫ D.ι →
      ∃ v : Z ⟶ Y, v ≫ e = a ≫ j ≫ ι) :
    IsClosedImmersion ((ι ≫ p) ∣_ D) := by
  have hr : Set.range e ⊆ Set.range (p ⁻¹ᵁ D).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change p (e z) ∈ D
    rw [← Scheme.Hom.comp_apply, he, Scheme.Hom.comp_apply]
    exact (y z).2
  let e' : Y ⟶ (p ⁻¹ᵁ D).toScheme := IsOpenImmersion.lift (p ⁻¹ᵁ D).ι e hr
  have he' : e' ≫ (p ⁻¹ᵁ D).ι = e := IsOpenImmersion.lift_fac _ _ _
  have hy : e' ≫ p ∣_ D = y := by
    rw [← cancel_mono D.ι, Category.assoc, morphismRestrict_ι, reassoc_of% he', he]
  have : IsClosedImmersion (e' ≫ p ∣_ D) := by rw [hy]; infer_instance
  obtain ⟨v, hv⟩ := hv _ (j ⁻¹ᵁ ι ⁻¹ᵁ p ⁻¹ᵁ D).ι
    (j ∣_ (ι ⁻¹ᵁ p ⁻¹ᵁ D) ≫ ι ∣_ (p ⁻¹ᵁ D) ≫ p ∣_ D) (by simp)
  have := closed_of_dense (p ∣_ D) (ι ∣_ (p ⁻¹ᵁ D)) (j ∣_ (ι ⁻¹ᵁ p ⁻¹ᵁ D)) e' v (by
    rw [← cancel_mono (p ⁻¹ᵁ D).ι]
    simp [he', hv])
  rw [morphismRestrict_comp]
  exact this
end GlobalTheory.DenseClosedAffineSubsets
