-- Prove2me | solution 1 for GlobalTheory.splitFibres_descend_of_tame_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:09.402628+00:00
-- url     : https://prove2.me/submissions/0aec580c-3904-4b29-a813-95ccf483d889

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FiniteSeparableOfSumMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ResidueFieldMapFiniteSeparableOfTame
import Theorems.Thm_GlobalTheory_residueFieldMap_finite_separable_of_tame
import Theorems.Thm_GlobalTheory_quotient_isIntegral_surjective_orbits
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_grpPullback_iso
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGt_of_iso


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G.left ⟶ G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).hom = x} : k) ≠ 0) → IsGrpPullback G G' π φ → (∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)) → (∀ x : X', ∃ (k : Type) (_ : Field k) (_ : Algebra (X'.residueField x) k), FiniteDimensional (X'.residueField x) k ∧ Algebra.IsSeparable (X'.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) k)) ≫ X'.fromSpecResidueField x)).obj G')) := by
  intro Γ _ _ X X' ρ π G _ G' _ φ hq ht hφ hS x'
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hq
  obtain ⟨_, hπ, hV⟩ := hq
  obtain ⟨x, rfl⟩ := π.surjective x'
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨h₁, h₂⟩ := residueFieldMap_finite_separable_of_tame ρ π hπ
    (fun W _ s hs ↦ (hV W).2 s fun g _ ↦ (hs g).2) ht x
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS x
  let : Algebra (X'.residueField (π x)) k :=
    ((algebraMap (X.residueField x) k).comp (π.residueFieldMap x).hom).toAlgebra
  have : IsScalarTower (X'.residueField (π x)) (X.residueField x) k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨k, inferInstance, inferInstance, Module.Finite.trans (X.residueField x) k,
    Algebra.IsSeparable.trans _ (X.residueField x) k, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField (π x)) k)) ≫ X'.fromSpecResidueField (π x) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
    rfl
  rw [← key]
  generalize Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x = t at hGt
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G' π)
  have : IsMonHom ((Over.pullback t).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₃ := isGt_of_iso ((Over.pullback t).mapIso e) hGt
  have : IsMonHom (pullCompIso t π G').symm.hom := inferInstanceAs (IsMonHom (pullCompIso t π G').inv)
  exact isGt_of_iso (pullCompIso t π G').symm h₃
end GlobalTheory
