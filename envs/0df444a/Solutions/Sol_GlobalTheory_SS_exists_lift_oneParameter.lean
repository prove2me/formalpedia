-- Prove2me | solution 1 for GlobalTheory.SS.exists_lift_oneParameter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:10:22.441142+00:00
-- url     : https://prove2.me/submissions/a43db2f1-6777-4b0c-860c-6415163ba5fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_UniqueFactorizationMonoidAddMonoidAlgebraOfFree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLiftOneParameterQuotientTorus
import Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_pullback_grp
import Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_ker_pullback
import Theorems.Thm_GlobalTheory_SS_LiftTorus_exists_section
import Theorems.Thm_GlobalTheory_SS_LiftTorus_subsingleton_pic_torus
import Theorems.Thm_P2M_GlobalTheory_pic_groupAlgebra_of_isIntegrallyClosed__4f9bdb8fe068
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_splitTorus_rigidity


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
open GlobalTheory GlobalTheory.SS
open LiftTorus
namespace GlobalTheory.SS
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], SmConn G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q → ∀ f : Gm (Sp k) ⟶ B, IsMonHom f → ∃ j : Gm (Sp k) ⟶ G, IsMonHom j ∧ j ≫ q = f := by
  intro k _ _ G _ _ X _ _ _ B _ i q ⟨_, _, hfl, hsu, haf, hi, _⟩ f _
  obtain ⟨E, _, p, r, _, _, hE⟩ := exists_pullback_grp q f
  obtain ⟨i', _, hi'⟩ := exists_ker_pullback hi hE
  have hE' : IsPullback p.left r.left q.left f.left := hE.map (Over.forget _)
  haveI : Flat r.left := MorphismProperty.of_isPullback hE' hfl
  haveI : Surjective r.left := MorphismProperty.of_isPullback hE' hsu
  haveI : IsAffineHom r.left := MorphismProperty.of_isPullback hE' haf
  haveI : IsAffine (Gm (Sp k)).left := .of_isIso (Rosenlicht.torusIso k (ULift.{0} ℤ)).inv
  haveI := subsingleton_pic_torus k (ULift.{0} ℤ)
  obtain ⟨s, hs⟩ := exists_section hi'
  have hs₀ : (s ≫ p) ≫ q = f := by rw [Category.assoc, hE.w, ← Category.assoc, hs, Category.id_comp]
  have hone : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ Gm (Sp k)) ≫ f = 1 := fun {Z} => MonObj.one_comp f
  let j : Gm (Sp k) ⟶ G := (s ≫ p) * ((1 : Gm (Sp k) ⟶ Gm (Sp k)) ≫ s ≫ p)⁻¹
  have hj : j ≫ q = f := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc 1, hs₀, hone, inv_one, _root_.mul_one]
  have hj1 : ∀ {Z : Over (Sp k)}, (1 : Z ⟶ Gm (Sp k)) ≫ j = 1 := fun {Z} => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc 1 1, MonObj.comp_one, mul_inv_cancel]
  clear_value j
  let c : Gm (Sp k) ⊗ Gm (Sp k) ⟶ G :=
    ((fst _ _ * snd _ _) ≫ j) * ((fst _ _ ≫ j) * (snd _ _ ≫ j))⁻¹
  have hc : c ≫ q = toUnit _ ≫ η[B] := by
    rw [MonObj.mul_comp _ _ q, GrpObj.inv_comp, MonObj.mul_comp _ _ q, Category.assoc, Category.assoc,
      Category.assoc, hj, MonObj.mul_comp _ _ f, mul_inv_cancel, Hom.one_def]
  have hcomp : ∀ a b : Gm (Sp k) ⟶ Gm (Sp k),
      lift a b ≫ c = ((a * b) ≫ j) * ((a ≫ j) * (b ≫ j))⁻¹ := fun a b => by
    rw [MonObj.comp_mul, GrpObj.comp_inv, MonObj.comp_mul, ← Category.assoc, MonObj.comp_mul,
      lift_fst_assoc, lift_snd_assoc, lift_fst, lift_snd]
  have hax : ∀ z : Gm (Sp k) ⟶ Gm (Sp k) ⊗ Gm (Sp k), z ≫ c = 1 →
      z ≫ hi.lift c _ hc = toUnit _ ≫ η := fun z hz => by
    refine hi.hom_ext ?_ (toUnit_unique _ _)
    rw [Category.assoc, hi.lift_fst, hz, Category.assoc, IsMonHom.one_hom, Hom.one_def]
  haveI : TwoUniqueSums (ULift.{0} ℤ) :=
    (TwoUniqueSums.of_injective_addHom (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).toAddHom
      (AddEquiv.ulift : ULift.{0} ℤ ≃+ ℤ).injective inferInstance)
  have h0 := splitTorus_rigidity k (ULift.{0} ℤ) X (hi.lift c _ hc)
    (hax _ (by rw [← Hom.one_def, hcomp, hj1, _root_.mul_one, _root_.mul_one, mul_inv_cancel]))
    (hax _ (by rw [← Hom.one_def, hcomp, hj1, _root_.one_mul, _root_.one_mul, mul_inv_cancel]))
  have h1 : c = 1 := by
    rw [← hi.lift_fst c _ hc, h0, Category.assoc, IsMonHom.one_hom, Hom.one_def]
  have h2 := mul_inv_eq_one.1 h1
  refine ⟨j, ⟨?_, ?_⟩, hj⟩
  · have := hj1 (Z := 𝟙_ _)
    simpa [Hom.one_def] using this
  · rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] at h2
    exact h2
end GlobalTheory.SS
