-- Prove2me | solution 1 for GlobalTheory.splitTorus_properties
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:49:59.824211+00:00
-- url     : https://prove2.me/submissions/16afbe0a-48af-4fb0-a03f-d23813b0e5ec

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_Torus2GammaBijective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinitePresentationOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Theorems.Thm_GlobalTheory_Diag_diagMap_chi
import Theorems.Thm_GlobalTheory_Diag_torsionIso_hom_diagMap
import Theorems.Thm_GlobalTheory_Diag_isClosedImmersion_diagMap
import Theorems.Thm_GlobalTheory_Diag_flat_diagMap
import Theorems.Thm_GlobalTheory_Diag_surjective_diagMap
import Theorems.Thm_GlobalTheory_Diag_isFinite_diagMap
import Theorems.Thm_GlobalTheory_Diag_locallyOfFinitePresentation_diagMap
import Theorems.Thm_GlobalTheory_Diag_finrank_diagMap
import Theorems.Thm_GlobalTheory_Diag_finrank_hom
import Theorems.Thm_GlobalTheory_Diag_etale_hom
import Theorems.Thm_GlobalTheory_Diag_isFinite_mulN
import Theorems.Thm_GlobalTheory_Diag_flat_mulN
import Theorems.Thm_GlobalTheory_Diag_surjective_mulN
import Theorems.Thm_GlobalTheory_Diag_locallyOfFinitePresentation_mulN
import Theorems.Thm_GlobalTheory_Diag_finrank_mulN
import Theorems.Thm_GlobalTheory_Diag_baseChangeIso_naturality
import Theorems.Thm_GlobalTheory_Diag_id_ne_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open GlobalTheory
open Diag
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) :
    (∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
      IsAffineHom (splitTorus S X).hom ∧ LocallyOfFinitePresentation (splitTorus S X).hom ∧
      QuasiCompact (splitTorus S X).hom ∧ QuasiSeparated (splitTorus S X).hom ∧
      SmoothOfRelativeDimension (Module.finrank ℤ X) (splitTorus S X).hom ∧
      Surjective (splitTorus S X).hom ∧ GeometricallyIntegral (splitTorus S X).hom ∧
      GeometricallyConnected (splitTorus S X).hom ∧ IsSemiAbelian (splitTorus S X) ∧
      (Nonempty S → Nontrivial X → 𝟙 (splitTorus S X) ≠ 1) ∧
      ∀ n : ℕ, 1 ≤ n → IsFinite (mulN (splitTorus S X) n).left ∧
        Flat (mulN (splitTorus S X) n).left ∧ Surjective (mulN (splitTorus S X) n).left ∧
        LocallyOfFinitePresentation (mulN (splitTorus S X) n).left ∧
        ∀ y, (mulN (splitTorus S X) n).left.finrank y = n ^ Module.finrank ℤ X) ∧
    (∀ (S' : Scheme.{0}) (f : S' ⟶ S) (X : Type) [AddCommGroup X],
      IsMonHom (baseChangeIso f X : (Over.pullback f).obj (splitTorus S X) ≅ splitTorus S' X).hom ∧
      ∀ (Y : Type) [AddCommGroup Y] (u : Y →+ X),
        (Over.pullback f).map (diagMap S u) ≫ (baseChangeIso f Y).hom =
          (baseChangeIso f X).hom ≫ diagMap S' u) ∧
    (∀ (X : Type) [AddCommGroup X] [Finite X],
      IsFinite (splitTorus S X).hom ∧ Flat (splitTorus S X).hom ∧
      LocallyOfFinitePresentation (splitTorus S X).hom ∧
      (∀ s, (splitTorus S X).hom.finrank s = Nat.card X) ∧
      (IsUnit (Nat.card X : Γ(S, ⊤)) → Etale (splitTorus S X).hom)) ∧
    (∀ (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (u : Y →+ X),
      IsMonHom (diagMap S u : splitTorus S X ⟶ splitTorus S Y) ∧
      (∀ y, (diagMap S u).left.appTop.hom (chi Y y) = chi X (u y)) ∧
      (∀ v : Y →+ X, diagMap S (u + v) = diagMap S u * diagMap S v) ∧
      (∀ (Z : Type) [AddCommGroup Z] (v : Z →+ Y), diagMap S (u.comp v) = diagMap S u ≫ diagMap S v) ∧
      IsPullback (diagMap S (QuotientAddGroup.mk' u.range)) (toUnit _) (diagMap S u)
        (η : 𝟙_ (Over S) ⟶ splitTorus S Y) ∧
      (Function.Surjective u → IsClosedImmersion (diagMap S u).left) ∧
      (Function.Injective u → Flat (diagMap S u).left ∧ Surjective (diagMap S u).left) ∧
      (u.range.FiniteIndex → IsFinite (diagMap S u).left) ∧
      (Function.Injective u → u.range.FiniteIndex →
        LocallyOfFinitePresentation (diagMap S u).left ∧
          ∀ y, (diagMap S u).left.finrank y = u.range.index)) ∧
    (∀ (X : Type) [AddCommGroup X] (n : ℕ),
      diagMap S (AddMonoidHom.id X) = 𝟙 (splitTorus S X) ∧
      mulN (splitTorus S X) n = diagMap S (nsmulAddMonoidHom n) ∧
      ∃ e : torsion (splitTorus S X) n ≅ splitTorus S (X ⧸ (nsmulAddMonoidHom n : X →+ X).range),
        e.hom ≫ diagMap S (QuotientAddGroup.mk' _) = torsion.ι (splitTorus S X) n) :=
  ⟨fun X _ _ _ => ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, fun _ _ => id_ne_one S,
      fun _ hn => have hn := Nat.one_le_iff_ne_zero.1 hn
        ⟨isFinite_mulN S X hn, flat_mulN S X hn, surjective_mulN S X hn,
          locallyOfFinitePresentation_mulN S X hn, finrank_mulN S X hn⟩⟩,
    fun _ f _ _ => ⟨inferInstance, fun _ _ u => baseChangeIso_naturality f u⟩,
    fun X _ _ => ⟨inferInstance, inferInstance, inferInstance, finrank_hom S X, etale_hom S X⟩,
    fun _ _ _ _ u => ⟨inferInstance, diagMap_chi S u, diagMap_add S u, fun _ _ v => diagMap_comp S u v,
      isPullback_ker S u, isClosedImmersion_diagMap S, fun h => ⟨flat_diagMap S h, surjective_diagMap S h⟩,
      fun _ => isFinite_diagMap S u,
      fun h _ => ⟨locallyOfFinitePresentation_diagMap S h, finrank_diagMap S h⟩⟩,
    fun X _ n => ⟨diagMap_id S, mulN_eq_diagMap S n, torsionIso S X n, torsionIso_hom_diagMap S n⟩⟩
end GlobalTheory
