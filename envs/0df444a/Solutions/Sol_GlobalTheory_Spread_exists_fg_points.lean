-- Prove2me | solution 1 for GlobalTheory.Spread.exists_fg_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:09:07.556799+00:00
-- url     : https://prove2.me/submissions/a55e7ba4-b4de-47b8-8889-b5a6dfe57893

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_exists_fg_forall_comp_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
variable (A : Type) [CommRing A] [Algebra k A]
variable {A} (pZ : Z ⟶ Sp k)
namespace GlobalTheory.Spread
theorem _root_.solution [LocallyOfFinitePresentation pZ] {ι : Type*} [Finite ι]
    (x : ι → (Sp A ⟶ Z)) (hx : ∀ i, x i ≫ pZ = spMap (algebraMap k A))
    (R₀ : Subalgebra k A) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k A) (y : ι → (Sp R ⟶ Z)), R.FG ∧ R₀ ≤ R ∧
      ∀ i, y i ≫ pZ = spMap (algebraMap k R) ∧ spMap R.val.toRingHom ≫ y i = x i := by
  obtain ⟨R, ψ, hR, hle, h⟩ := exists_fg_forall_comp_eq (𝟙 (Sp k)) pZ
    (fun i ↦ pullback.snd _ _ ≫ x i)
    (fun i ↦ by rw [Category.assoc, hx, pullback.condition]) R₀ hR₀
  refine ⟨R, fun i ↦ inv (pullback.snd (𝟙 (Sp k)) (spMap (algebraMap k R))) ≫ ψ i, hR, hle,
    fun i ↦ ⟨?_, ?_⟩⟩
  · rw [Category.assoc, (h i).1, pullback.condition, IsIso.inv_hom_id_assoc]
  · rw [← cancel_epi (pullback.snd (𝟙 (Sp k)) (spMap (algebraMap k A))), ← bcMap_snd_assoc,
      IsIso.hom_inv_id_assoc, (h i).2]
end GlobalTheory.Spread
