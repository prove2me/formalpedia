-- Prove2me | solution 1 for GlobalTheory.TorusImage.exists_factor_goodOpen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:24.836472+00:00
-- url     : https://prove2.me/submissions/d823f397-1004-40cc-9516-03cbec028ccb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsRatioOfWeightSumsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorusStableGoodOpenOfWeightUnitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusImageFactorQuotientGoodOpen
import Theorems.Thm_GlobalTheory_TorusImage_wt_desc
import Theorems.Thm_GlobalTheory_TorusImage_eq_one_of_open
import Theorems.Thm_GlobalTheory_TorusImage_exists_open
import Theorems.Thm_GlobalTheory_Diag_diagMap_chi
import Theorems.Thm_GlobalTheory_Diag_flat_diagMap
import Theorems.Thm_GlobalTheory_Diag_surjective_diagMap
import Theorems.Thm_GlobalTheory_FlatQuotient_exists_desc
import Theorems.Thm_GlobalTheory_T_exists_torusStableGoodOpen_of_weightUnits
import Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.TorusImage
namespace GlobalTheory.TorusImage
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp k) X ⟶ G), IsMonHom i → ∃ (X' : Type) (_ : AddCommGroup X') (_ : Module.Free ℤ X') (_ : Module.Finite ℤ X') (i' : splitTorus (Sp k) X' ⟶ G) (ρ : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X'), IsMonHom i' ∧ IsMonHom ρ ∧ Surjective ρ.left ∧ ρ ≫ i' = i ∧ (∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen i' V) := by
  intro k _ _ G _ hG X _ _ _ i hi
  have := hG.2.1
  have := hG.2.2.2.2
  have : GeometricallyIntegral G.hom :=
    GlobalTheory.geometricallyIntegral_of_smooth G.hom
  have : IrreducibleSpace G.left := GeometricallyIrreducible.irreducibleSpace_of_subsingleton G.hom
  obtain ⟨U, ⟨y, hy⟩, hU⟩ := exists_open k G hG X i hi
  let φ : weights i →+ X := (weights i).subtype
  have hφ : Function.Injective φ := Subtype.val_injective
  have hfree : Module.Free ℤ (weights i) := inferInstanceAs (Module.Free ℤ (weights i).toIntSubmodule)
  have hfin : Module.Finite ℤ (weights i) := inferInstanceAs (Module.Finite ℤ (weights i).toIntSubmodule)
  let ρ := Diag.diagMap (Sp k) φ
  have : Flat ρ.left := Diag.flat_diagMap _ hφ
  have hsurj : Surjective ρ.left := Diag.surjective_diagMap _ hφ
  have : QuasiCompact (ρ.left ≫ (splitTorus (Sp k) (weights i)).hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact ρ.left := .of_comp _ (splitTorus (Sp k) (weights i)).hom
  have hker : IsPullback (pullback.fst ρ η[splitTorus (Sp k) (weights i)]) (toUnit _) ρ η := by
    rw [← toUnit_unique (pullback.snd ρ η[splitTorus (Sp k) (weights i)]) (toUnit _)]
    exact IsPullback.of_hasPullback _ _
  have hkill : pullback.fst ρ η[splitTorus (Sp k) (weights i)] ≫ i = toUnit _ ≫ η[G] := by
    rw [← Hom.one_def]
    refine eq_one_of_open U (fun s => ⟨y, hy, Subsingleton.elim _ _⟩) _ fun Y π g h₁ h₂ => ?_
    rw [← Category.assoc] at h₁ ⊢
    refine hU Y _ g (fun χ hχ => ?_) h₁ h₂
    have e : (π ≫ pullback.fst ρ η[splitTorus (Sp k) (weights i)]) ≫ ρ = 1 := by
      rw [Category.assoc, hker.w, ← Hom.one_def, MonObj.comp_one]
    have e' := SplitTorus.val_one (T := Y) (⟨χ, hχ⟩ : weights i)
    rw [← e, SplitTorus.val_comp, SplitTorus.val_eq ρ, Diag.diagMap_chi, ← SplitTorus.val_eq] at e'
    exact e'
  obtain ⟨i', hi', e⟩ := FlatQuotient.exists_desc ρ _ i hker hkill
  refine ⟨weights i, inferInstance, hfree, hfin, i', ρ, hi', inferInstance, hsurj, e,
    GlobalTheory.T.exists_torusStableGoodOpen_of_weightUnits k G hG (weights i) i' hi' fun χ => ?_⟩
  obtain ⟨V, u, hV, hu, h⟩ := χ.2
  exact ⟨V, u, hV, hu, wt_desc φ hφ i' e h⟩
end GlobalTheory.TorusImage
