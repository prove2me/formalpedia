-- Prove2me | solution 1 for GlobalTheory.ThetaSpecialise.fn_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:35:39.052421+00:00
-- url     : https://prove2.me/submissions/30fda8bd-cbd4-481d-acf9-2d3c4ebbda07

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExpansionBijectiveOverFields
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExpandsAtTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMoveMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SquareUnits_UnitAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaSpecialise
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {S F : Type} [CommRing S] [CommRing F] {fS : S →+* F} {X Y Y' : Scheme.{0}}
  {π : Y ⟶ Spec (CommRingCat.of S)} {π' : Y' ⟶ Spec (CommRingCat.of F)} {p : Y' ⟶ Y}
  (H : IsPullback p π' π (Spec.map (CommRingCat.ofHom fS))) [Flat π]
namespace GlobalTheory.ThetaSpecialise
theorem _root_.solution {U : Y.Opens} (hU : IsAffineOpen U) {n : ℕ} (c : Fin n → F)
    (hc : ∀ a : Fin n → S, ∑ i, fS (a i) * c i = 0 → ∀ i, a i = 0) (a : Fin n → FnOver π U)
    (h : ∑ i, c i • pullFn H.w (le_refl (p ⁻¹ᵁ U)) (a i) = 0) (i : Fin n) : a i = 0 := by
  let : Algebra S F := fS.toAlgebra
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := p ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (CommRingCat.ofHom (constHom π U)) (CommRingCat.ofHom fS) (p.app U)
      (CommRingCat.ofHom (constHom π' (p ⁻¹ᵁ U))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of S)) (Iso.refl _) (Scheme.ΓSpecIso (.of F)) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · ext x; simp [constHom, Scheme.Hom.appLE]; rfl
  let : Algebra (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) := (p.app U).hom.toAlgebra
  let : Algebra S (FnOver π' (p ⁻¹ᵁ U)) := ((constHom π' (p ⁻¹ᵁ U)).comp fS).toAlgebra
  have : IsScalarTower S F (FnOver π' (p ⁻¹ᵁ U)) := .of_algebraMap_eq fun r ↦ rfl
  have : IsScalarTower S (FnOver π U) (FnOver π' (p ⁻¹ᵁ U)) :=
    .of_algebraMap_eq fun r ↦ (congrArg (fun q => q.hom r) po'.w).symm
  have hpo : Algebra.IsPushout S (FnOver π U) F (FnOver π' (p ⁻¹ᵁ U)) :=
    CommRingCat.isPushout_iff_isPushout.mp po'
  have fl : Module.Flat S (FnOver π U) := by
    have f₁ : RingHom.Flat (π.appLE ⊤ U le_top).hom :=
      HasRingHomProperty.appLE (P := @Flat) π inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
    have f₂ : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom :=
      RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
    exact f₂.comp f₁
  have li : LinearIndependent S c := Fintype.linearIndependent_iff.2 fun g hg => hc g hg
  have li' := Fintype.linearIndependent_iff.1 (Module.Flat.linearIndependent_one_tmul (S := FnOver π U) li)
  refine li' a (hpo.out.equiv.injective ?_) i
  rw [map_zero, ← h, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hpo.out.equiv_tmul, one_smul, Algebra.smul_def, Algebra.smul_def, mul_comm]
  congr 1
  show _ = (Y'.presheaf.map (𝟙 _)).hom _
  rw [CategoryTheory.Functor.map_id]; rfl
end GlobalTheory.ThetaSpecialise
