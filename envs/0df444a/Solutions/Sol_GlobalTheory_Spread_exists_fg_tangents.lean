-- Prove2me | solution 1 for GlobalTheory.Spread.exists_fg_tangents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:15:02.734003+00:00
-- url     : https://prove2.me/submissions/4053b3d0-23c3-497f-afb4-d070ed4dae7c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Theorems.Thm_GlobalTheory_Spread_exists_fg_points
import Theorems.Thm_GlobalTheory_Spread_dualMapR_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


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
open Chart
namespace GlobalTheory.Spread
theorem _root_.solution [LocallyOfFinitePresentation pZ] {ι : Type*} [Finite ι]
    (v : ι → (Sp (DualNumber A) ⟶ Z))
    (hv : ∀ i, v i ≫ pZ = spMap (algebraMap k (DualNumber A)))
    (R₀ : Subalgebra k A) (hR₀ : R₀.FG) :
    ∃ (R : Subalgebra k A) (w : ι → (Sp (DualNumber R) ⟶ Z)), R.FG ∧ R₀ ≤ R ∧
      ∀ i, w i ≫ pZ = spMap (algebraMap k (DualNumber R)) ∧
        spMap (dualMapR R.val.toRingHom) ≫ w i = v i := by
  classical
  obtain ⟨T, y, ⟨s, rfl⟩, -, h⟩ := exists_fg_points pZ v hv ⊥ Subalgebra.fg_bot
  let R : Subalgebra k A := R₀ ⊔ Algebra.adjoin k
    ((s.image TrivSqZeroExt.fst ∪ s.image TrivSqZeroExt.snd : Finset A) : Set A)
  let g : DualNumber R →ₐ[k] DualNumber A :=
    { dualMapR R.val.toRingHom with
      commutes' := fun c ↦ by
        ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl'] }
  have hg : Function.Injective g := dualMapR_injective Subtype.val_injective
  have hle : Algebra.adjoin k (s : Set (DualNumber A)) ≤ g.range := by
    refine Algebra.adjoin_le fun a ha ↦ ?_
    have h₁ : a.fst ∈ R := (le_sup_right : _ ≤ R) (Algebra.subset_adjoin (by
      simp only [Finset.coe_union, Finset.coe_image]
      exact Or.inl ⟨a, ha, rfl⟩))
    have h₂ : a.snd ∈ R := (le_sup_right : _ ≤ R) (Algebra.subset_adjoin (by
      simp only [Finset.coe_union, Finset.coe_image]
      exact Or.inr ⟨a, ha, rfl⟩))
    refine ⟨TrivSqZeroExt.inl ⟨_, h₁⟩ + TrivSqZeroExt.inr ⟨_, h₂⟩, ?_⟩
    ext <;> simp [g, dualMapR]
  let e : Algebra.adjoin k (s : Set (DualNumber A)) →ₐ[k] DualNumber R :=
    (AlgEquiv.ofInjective g hg).symm.toAlgHom.comp (Subalgebra.inclusion hle)
  have he (a) : g (e a) = a := by
    have := (AlgEquiv.ofInjective g hg).apply_symm_apply (Subalgebra.inclusion hle a)
    exact congrArg Subtype.val this
  refine ⟨R, fun i ↦ spMap e.toRingHom ≫ y i, hR₀.sup (Subalgebra.fg_adjoin_finset _),
    le_sup_left, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [Category.assoc, (h i).1, spMap_algHom_comp]
  · rw [← (h i).2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext he
end GlobalTheory.Spread
