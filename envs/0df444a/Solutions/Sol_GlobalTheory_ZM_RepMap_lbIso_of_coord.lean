-- Prove2me | solution 1 for GlobalTheory.ZM.RepMap.lbIso_of_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:44:54.336969+00:00
-- url     : https://prove2.me/submissions/063e998e-9dcd-4cad-bf5f-83d79fd082fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordBcScaleUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SectionCoordinateVectorExistsLocallyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsSectionCoordinateVectorOfLocallyOnRingStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSchemeMapOfProjectiveCoordinates
import Theorems.Thm_GlobalTheory_ZM_RepMap_lbIso_of_germs
import Theorems.Thm_GlobalTheory_ZM_RepMap_coord_germ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gs_stalkMap


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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepMap
variable {X : Scheme.{0}} {σ : Type}
namespace GlobalTheory.ZM.RepMap
theorem _root_.solution (A B : LB X) (a : σ → A.Sec) (b : σ → B.Sec)
    (H : ∀ y : X, ∃ (R : Type) (_ : CommRing R) (x : Sp R ⟶ X) (v : σ → R), IsOpenImmersion x ∧ y ∈ Set.range x ∧
      Ideal.span (Set.range v) = ⊤ ∧ SecCoord A a x v ∧ SecCoord B b x v) : LBIso A B := by
  refine lbIso_of_germs A B a b fun y j k hj hk => ?_
  obtain ⟨R, _, x, v, _, ⟨p, rfl⟩, hv, hA, hB⟩ := H y
  obtain ⟨t, ht⟩ := coord_germ hA p k hk
  obtain ⟨t', ht'⟩ := coord_germ hB p j hj
  let e := (asIso (x.stalkMap p)).commRingCatIsoToRingEquiv
  have he : ∀ (U : X.Opens) (_ : x p ∈ U) f, gs x p U f = e (gs (𝟙 X) (x p) U f) := fun U h f => gs_stalkMap x p U h f
  let ψ : R →+* (Sp R).presheaf.stalk p :=
    ((Sp R).presheaf.germ ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  constructor
  · have : ∃ i, IsUnit (ψ (v i)) := by
      by_contra hn
      push_neg at hn
      have : Ideal.span (Set.range v) ≤ (IsLocalRing.maximalIdeal _).comap ψ := by
        rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact hn i
      rw [hv, top_le_iff, Ideal.comap_eq_top_iff] at this
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top this
    obtain ⟨i, hi⟩ := this
    refine ⟨i, ?_⟩
    rw [← MulEquiv.isUnit_map e, ← he _ hk, ht]
    exact hi.mul t.isUnit
  · refine ⟨Units.map e.symm.toMonoidHom (t' * t⁻¹), fun i => e.injective ?_⟩
    rw [map_mul, ← he _ hk, ← he _ hj, ht, ht']
    have : e (Units.map e.symm.toMonoidHom (t' * t⁻¹)).val = (t' * t⁻¹).val := e.apply_symm_apply _
    rw [this, Units.val_mul]
    linear_combination (-(ψ (v i)) * t'.val) * t.inv_mul
end GlobalTheory.ZM.RepMap
