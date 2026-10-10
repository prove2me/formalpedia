-- Prove2me | solution 1 for MazurTransfer.order13_actual_arithmetic_picard_group_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T00:39:34.372807+00:00
-- url     : https://prove2.me/submissions/be770143-64ca-4c5b-860f-b4e641c6d42d

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Original complete frame proof: official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the unchanged full actual arithmetic Picard group
correspondence, consuming the accepted signed closed-point comparison.
Named downstream consumer: actual finite-field Picard point counts and
compatible rational torsion reduction. No supplied class dictionary,
cardinality, genus or rank hypothesis is introduced.
-/
import Theorems.Thm_MazurTransfer_represented_picard_field_points_classify_line_bundles
import Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field
import Theorems.Thm_MazurTransfer_numerical_line_bundle_triviality_over_field
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
import Theorems.Thm_MazurTransfer_divisor_presentation_riemann_roch_over_perfect_field
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Theorems.Thm_MazurTransfer_order13_actual_function_field_invariants
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometric_integrality
import Theorems.Thm_MazurTransfer_tensor_presentation_principal_over_perfect_field
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_MazurTransfer_closed_point_kernel_invertible_over_field
import Theorems.Thm_MazurTransfer_order13_actual_picard_abel_jacobi_good_characteristic
import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Theorems.Thm_MazurTransfer_order13_actual_good_characteristic_geometry_and_finite_field_points
import Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Theorems.Thm_MazurTransfer_closed_point_kernel_presentations_signed_divisor_classes
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete frame nonvanishing proof from official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a frame over a nontrivial section ring is nonzero.
Named downstream consumer: independence of the actual order-13 point's
arithmetic divisor class from its chosen rational-section presentation.
-/
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
namespace MazurTransfer.PublicFrameNonzeroHelper
variable {X : Scheme.{u}}
theorem frame_ne_zero_of_nontrivial {M : X.Modules} {U : X.Opens} [Nontrivial Γ(X, U)] {s : Γ(M, U)}
    (hs : IsFrameOn s U) : s ≠ 0 := by
  intro h
  have h1 : (1 : Γ(X, U)) • M.presheaf.map (homOfLE (le_refl U)).op s = 0 := by
    rw [h, map_zero, smul_zero]
  have := (hs.smul_eq_zero_iff le_rfl le_rfl (1 : Γ(X, U))).mp h1
  exact one_ne_zero this

end MazurTransfer.PublicFrameNonzeroHelper
#print axioms MazurTransfer.PublicFrameNonzeroHelper.frame_ne_zero_of_nontrivial

end

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Actual curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Remaining complete original helpers: official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the unchanged actual arithmetic Picard group equivalence,
consuming accepted classification, geometry, arbitrary closed-point,
presentation-independence and numerical-triviality interfaces.
Named downstream consumer: finite-field Picard counts and rational torsion.
-/


section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: consume the accepted public classification of actual Poincare
line bundles, with no implementation helpers from its proof. Named downstream
consumer: the actual order-13 arithmetic Picard group correspondence.
Public theorem assembled from the MazurTheorem WIP and official Anthropic FLT
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/

universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

namespace MazurTransfer.LineBundleFieldComparison

noncomputable def curveEulerChar {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) : ℤ :=
  (Module.finrank k (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank k (𝒱.sectionsOf x M).H1

noncomputable def pointLineBundle {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) : X.Modules :=
  (Scheme.Modules.pullback (toProdSpec x)).obj (h.poincare.pullbackAlong a).L

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIntegral x]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) x)
    (D : RelativePic0Designation k x)
    (h : RepresentsRelSubPic x ε (algEquivZeroCut x ε) D)

theorem pointLineBundle_isInvertible
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) :
    Scheme.Modules.IsInvertible (pointLineBundle x ε D h a) :=
  (MazurTransfer.represented_picard_field_points_classify_line_bundles x ε D h).1 a |>.1

theorem pointLineBundle_curveEulerChar_eq
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase)
    (𝒱 : X.TwoAffineOpenCover) :
    curveEulerChar x 𝒱 (pointLineBundle x ε D h a) = curveEulerChar x 𝒱 (𝟙_ X.Modules) :=
  (MazurTransfer.represented_picard_field_points_classify_line_bundles x ε D h).1 a |>.2 𝒱

theorem pointLineBundle_iso_iff
    (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase) :
    Nonempty (pointLineBundle x ε D h a ≅ pointLineBundle x ε D h b) ↔ a = b :=
  (MazurTransfer.represented_picard_field_points_classify_line_bundles x ε D h).2.1 a b

theorem existsUnique_pointLineBundle_iso_of_curveEulerChar_eq
    (N : X.Modules) (hN : Scheme.Modules.IsInvertible N) (𝒱 : X.TwoAffineOpenCover)
    (hχ : curveEulerChar x 𝒱 N = curveEulerChar x 𝒱 (𝟙_ X.Modules)) :
    ∃! a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D.toBase,
      Nonempty (pointLineBundle x ε D h a ≅ N) :=
  (MazurTransfer.represented_picard_field_points_classify_line_bundles x ε D h).2.2 𝒱 N hN hχ

#print axioms pointLineBundle_isInvertible
#print axioms pointLineBundle_curveEulerChar_eq
#print axioms pointLineBundle_iso_iff
#print axioms existsUnique_pointLineBundle_iso_of_curveEulerChar_eq

end MazurTransfer.LineBundleFieldComparison

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Exact consumer of our accepted public perfect-field presentation comparison.
Design boundary: actual presentation independence without implementation
helper imports. Named downstream consumer: tensor/divisor compatibility
for the unchanged order-13 arithmetic Picard group correspondence.
Official Anthropic FLT pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
universe u
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

theorem MazurTransfer.FieldDivisorComparison.presentationRatioPrincipal_of_constantsAreBase
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (M : X.Modules)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ φ' : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ' V (M.presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (hsec : ∃ (U : X.Opens) (m : Γ(M, U)), m ≠ 0) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ g : X.functionField, g ≠ 0 ∧
      (∀ (U : X.Opens) [Nonempty U] (m : Γ(M, U)), φ' U m = g * φ U m) ∧
      (∀ v : AlgebraicCurve.Place K X.functionField, D v = D' v + v.ord g) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D - D') := by
  exact MazurTransfer.presentation_ratio_principal_over_perfect_field x hC M D D' φ φ'
    hnat hnat' hsmul hsmul' hinj hinj' hrange hrange' hsec

#print axioms MazurTransfer.FieldDivisorComparison.presentationRatioPrincipal_of_constantsAreBase

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Exact consumer of our accepted public numerical line-bundle triviality.
Official Anthropic FLT pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: the actual base-field Euler characteristic and a nonzero
section, with no private triviality implementation helpers. Named downstream
consumer: the principal-presentation kernel of the unchanged order-13
arithmetic Picard correspondence.
-/

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace MazurTransfer.LineBundleFieldComparison


theorem nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero
    {k : Type u} [Field k] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of k))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIrreducible x]
    (𝒱 : X.TwoAffineOpenCover) {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hχ : curveEulerChar x 𝒱 M = curveEulerChar x 𝒱 (𝟙_ X.Modules))
    (s : 𝟙_ X.Modules ⟶ M) (hs : s ≠ 0) :
    Nonempty (M ≅ 𝟙_ X.Modules) := by
  exact MazurTransfer.numerical_line_bundle_triviality_over_field x 𝒱 hM hχ s hs

#print axioms nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero
end MazurTransfer.LineBundleFieldComparison

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Selected complete global-section and divisor-quotient declarations from
 official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0, with source attribution retained.
Design boundary: a nontrivial actual Cech H0 yields a nonzero sheaf morphism
from the unit, and actual divisor-class equality is principal difference.
Named downstream consumer: the principal-presentation kernel and the unchanged
actual arithmetic Picard group correspondence. These interfaces use public
cohomology and quotient definitions without original implementation imports.
-/

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve

namespace MazurTransfer.PublicPicardPointKernelHelpers

/-- The canonical unit-section conversion is definitionally the identity. -/
def toUnitSection {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) :
    Γ((𝟙_ X.Modules : X.Modules), U) := r

noncomputable def sectionsOfGlobal {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) : SheafOfModules.sections L :=
  PresheafOfModules.sectionsMk (M := L.val)
    (fun U => (L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op m : Γ(L, U.unop)))
    (by
      intro U V f
      change (L.presheaf.map f) ((L.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) m) =
        (L.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op) m
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrArg (fun g => (L.presheaf.map g) m) (Quiver.Hom.unop_inj (Subsingleton.elim _ _)))

theorem sectionsOfGlobal_top {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) :
    (sectionsOfGlobal L m).1 (Opposite.op ⊤) = m := by
  change (L.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op) m = m
  have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this, CategoryTheory.Functor.map_id]
  rfl


noncomputable def homOfGlobal {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) : 𝟙_ X.Modules ⟶ L :=
  (SheafOfModules.unitHomEquiv L).symm (sectionsOfGlobal L m)

theorem app_homOfGlobal_one {X : Scheme.{u}} (L : X.Modules) (m : Γ(L, ⊤)) :
    (Scheme.Modules.Hom.app (homOfGlobal L m) ⊤) (toUnitSection ⊤ 1) = m := by
  have h1 := SheafOfModules.unitHomEquiv_apply_coe L (homOfGlobal L m) (Opposite.op ⊤)
  rw [homOfGlobal, Equiv.apply_symm_apply, sectionsOfGlobal_top] at h1
  exact h1.symm

theorem homOfGlobal_ne_zero {X : Scheme.{u}} (L : X.Modules) {m : Γ(L, ⊤)} (hm : m ≠ 0) :
    homOfGlobal L m ≠ 0 := by
  intro h0
  apply hm
  have h1 := app_homOfGlobal_one L m
  rw [h0, Scheme.Modules.Hom.zero_app] at h1
  exact h1.symm.trans (AddCommGrpCat.zero_apply _ _ _)


theorem exists_hom_ne_zero_of_nontrivial_H0 {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (𝒱 : X.TwoAffineOpenCover) (L : X.Modules) (hL : Nontrivial (𝒱.sectionsOf x L).H0) :
    ∃ s : 𝟙_ X.Modules ⟶ L, s ≠ 0 := by
  obtain ⟨e, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 x L
  haveI : Nontrivial Γ(L, ⊤) := e.toEquiv.nontrivial
  obtain ⟨m, hm⟩ := exists_ne (0 : Γ(L, ⊤))
  exact ⟨homOfGlobal L m, homOfGlobal_ne_zero L hm⟩



section Quotients
variable {K F : Type u} [Field K] [Field F] [Algebra K F]
theorem pic_mk_eq_iff (D E : Divisor K F) :
    (QuotientAddGroup.mk D : Pic K F) = QuotientAddGroup.mk E ↔ Divisor.IsPrincipal (D - E) := by
  rw [QuotientAddGroup.eq_iff_sub_mem, Divisor.mem_principal]

theorem pic0_mk_eq_iff (D E : Divisor.degZero (K := K) (F := F)) :
    Pic0.mk D = Pic0.mk E ↔ (QuotientAddGroup.mk (D : Divisor K F) : Pic K F) = QuotientAddGroup.mk (E : Divisor K F) := by
  rw [pic_mk_eq_iff, Pic0.mk, Pic0.mk, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_sub, Divisor.mem_principal]


end Quotients

end MazurTransfer.PublicPicardPointKernelHelpers

#print axioms MazurTransfer.PublicPicardPointKernelHelpers.sectionsOfGlobal_top

#print axioms MazurTransfer.PublicPicardPointKernelHelpers.app_homOfGlobal_one

#print axioms MazurTransfer.PublicPicardPointKernelHelpers.homOfGlobal_ne_zero

#print axioms MazurTransfer.PublicPicardPointKernelHelpers.exists_hom_ne_zero_of_nontrivial_H0

#print axioms MazurTransfer.PublicPicardPointKernelHelpers.pic_mk_eq_iff

#print axioms MazurTransfer.PublicPicardPointKernelHelpers.pic0_mk_eq_iff

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Selected complete presentation and transport declarations from official
Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a divisor presentation records restriction naturality,
scalar compatibility, injectivity and the complete local Riemann--Roch range.
Existence consumes the public arbitrary-field invertible-sheaf and unit-sheaf
presentation theorems. No algebraic-closure comparison is included.
Named downstream consumer: the unchanged actual arithmetic Picard group
correspondence and divisor-class realization with arbitrary closed points.
-/

universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve

namespace MazurTransfer.PublicDivisorPresentationInterface

theorem isInvertible_of_iso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L')
    (h : Scheme.Modules.IsInvertible L) : Scheme.Modules.IsInvertible L' := by
  refine ⟨fun y => ?_⟩
  obtain ⟨U, hy, ⟨t⟩⟩ := h.1 y
  exact ⟨U, hy, ⟨(Scheme.Modules.pullback U.ι).mapIso e.symm ≪≫ t⟩⟩

section Presentation

variable {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X]

structure IsPresentation (L : X.Modules)
    (D : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u)) : Prop where
  nat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
    ∀ m : Γ(L, U), φ V (L.presheaf.map (homOfLE h).op m) = φ U m
  smul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
    φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m
  inj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U)
  range : letI := (baseToFunctionField x).toAlgebra
    ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
      Set.range (φ U) = (lSpaceOn (placesOf x U) D : Set X.functionField)

variable {x}

omit [IsIntegral X] in

theorem app_map_of_hom {L L' : X.Modules} (f : L ⟶ L') {U V : X.Opens} (i : V ≤ U) (m : Γ(L, U)) :
    (Scheme.Modules.Hom.app f V) (L.presheaf.map (homOfLE i).op m) =
      L'.presheaf.map (homOfLE i).op ((Scheme.Modules.Hom.app f U) m) := by
  have hn := (Scheme.Modules.Hom.mapPresheaf f).naturality (homOfLE i).op
  have hm := ConcreteCategory.congr_hom hn m
  simpa only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] using hm


theorem IsPresentation.of_iso {L L' : X.Modules} (e : L ≅ L')
    {D : letI := (baseToFunctionField x).toAlgebra
      Divisor K X.functionField}
    {φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u)} (h : IsPresentation x L' D φ') :
    IsPresentation x L D (fun U => (φ' U).comp (Scheme.Modules.Hom.app e.hom U).hom) := by
  refine ⟨fun U V hVU hV m => ?_, fun U _ a m => ?_, fun U hU => ?_, fun U hU hne => ?_⟩
  · show φ' V ((Scheme.Modules.Hom.app e.hom V) (L.presheaf.map (homOfLE hVU).op m)) =
      φ' U ((Scheme.Modules.Hom.app e.hom U) m)
    rw [app_map_of_hom e.hom hVU m]
    exact h.nat U V hVU hV _
  · show φ' U ((Scheme.Modules.Hom.app e.hom U) (a • m)) =
      algebraMap Γ(X, U) X.functionField a * φ' U ((Scheme.Modules.Hom.app e.hom U) m)
    rw [Scheme.Modules.Hom.app_smul]
    exact h.smul U a _
  · exact (h.inj U hU).comp (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).1
  · letI := (baseToFunctionField x).toAlgebra
    have hs : Function.Surjective (Scheme.Modules.Hom.app e.hom U) :=
      (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).2
    show Set.range (φ' U ∘ (Scheme.Modules.Hom.app e.hom U)) = _
    rw [hs.range_comp]
    exact h.range U hU hne

variable (x)


theorem exists_isPresentation [IsSeparated x] [QuasiCompact x] [SmoothOfRelativeDimension 1 x]
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    letI := (baseToFunctionField x).toAlgebra
    ∃ (D : Divisor K X.functionField) (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u)),
      IsPresentation x L D φ := by
  obtain ⟨D, φ, hnat, hsmul, hinj, hrange, -⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn x L hL
  exact ⟨D, φ, ⟨hnat, hsmul, hinj, hrange⟩⟩


theorem exists_isPresentation_unit [SmoothOfRelativeDimension 1 x] :
    letI := (baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((𝟙_ X.Modules : X.Modules), U) →+ (X.functionField : Type u),
      IsPresentation x (𝟙_ X.Modules) 0 φ := by
  obtain ⟨φ, -, hnat, hsmul, hinj, hrange⟩ := Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero x
  exact ⟨φ, ⟨hnat, hsmul, hinj, hrange⟩⟩


end Presentation

section Degree
variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
theorem degree_eq_zero_of_isPrincipal [HasPrincipalDivisors K F] {P : Divisor K F}
    (hP : Divisor.IsPrincipal P) : Divisor.degree P = 0 := by
  obtain ⟨f, hf, hPf⟩ := hP
  obtain ⟨D₀, hD₀, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
  have : P = D₀ := Finsupp.ext fun w => (hPf w).trans (hD₀ w).symm
  rw [this, hdeg]

end Degree

end MazurTransfer.PublicDivisorPresentationInterface

#print axioms MazurTransfer.PublicDivisorPresentationInterface.isInvertible_of_iso

#print axioms MazurTransfer.PublicDivisorPresentationInterface.app_map_of_hom

#print axioms MazurTransfer.PublicDivisorPresentationInterface.IsPresentation.of_iso

#print axioms MazurTransfer.PublicDivisorPresentationInterface.exists_isPresentation

#print axioms MazurTransfer.PublicDivisorPresentationInterface.exists_isPresentation_unit

#print axioms MazurTransfer.PublicDivisorPresentationInterface.degree_eq_zero_of_isPrincipal

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The affine-cover, section comparison and Cartier-divisor arguments reuse official
Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a principal function-field presentation gives a nonzero global
section, and numerical degree zero then gives a trivial line bundle over the
actual base field. Named downstream consumer: the kernel of the order-13
arithmetic Picard-point map. Numerical triviality now uses our accepted
public theorem. No algebraic-closure hypothesis is imposed.
-/

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve TopologicalSpace
open MazurTransfer.PublicDivisorPresentationInterface
open MazurTransfer.PublicPicardPointKernelHelpers
open MazurTransfer.LineBundleFieldComparison
namespace MazurTransfer.FieldDivisorComparison

private theorem affineOpen_ne_top {X : Scheme.{u}} (hX : ¬ IsAffine X) {U : X.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hX
  have hT : IsAffineOpen (⊤ : X.Opens) := h ▸ hU
  haveI : IsAffine (⊤ : X.Opens) := hT
  exact IsAffine.of_isIso X.topIso.inv

theorem nonempty_iso_tensorUnit_of_principal_presentation
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (x : X ⟶ Spec (CommRingCat.of K))
    [IsProper x] [SmoothOfRelativeDimension 1 x] [GeometricallyIrreducible x]
    (𝒱 : X.TwoAffineOpenCover) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hχ : curveEulerChar x 𝒱 M = curveEulerChar x 𝒱 (𝟙_ X.Modules))
    (E : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hp : IsPresentation x M E φ)
    (hE : letI := (baseToFunctionField x).toAlgebra; Divisor.IsPrincipal E) :
    Nonempty (M ≅ 𝟙_ X.Modules) := by
  letI := (baseToFunctionField x).toAlgebra
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one x
  have hne0 : 𝒱.U0 ≠ ⊤ := affineOpen_ne_top hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := affineOpen_ne_top hNA 𝒱.isAffineOpen_U1
  have h0 : Nonempty 𝒱.U0 := by
    by_contra hc
    apply hne1
    have hb : 𝒱.U0 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, bot_sup_eq] at this
  have h1 : Nonempty 𝒱.U1 := by
    by_contra hc
    apply hne0
    have hb : 𝒱.U1 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, sup_bot_eq] at this
  obtain ⟨hcov, hS0, hS1⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top x 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1
  obtain ⟨⟨e0⟩, -⟩ :=
    nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf_of_range_eq_lSpaceOn
      𝒱 x h0 h1 M E φ hp.nat (fun U _ a m => hp.smul U a m) hp.inj hp.range
  obtain ⟨f, hf, hEf⟩ := hE
  have hfL : f⁻¹ ∈ LSpace E := by
    apply mem_lSpace_iff_ord.mpr
    right
    intro v
    rw [v.ord_inv, hEf v]
  haveI : Nontrivial (LSpace E) :=
    ⟨⟨⟨f⁻¹, hfL⟩, 0, fun h => inv_ne_zero hf (congrArg Subtype.val h)⟩⟩
  haveI : Nontrivial (𝒱.sectionsOf x M).H0 :=
    (e0.trans (cechH0Equiv hcov E)).toEquiv.nontrivial
  obtain ⟨s, hs⟩ := exists_hom_ne_zero_of_nontrivial_H0 x 𝒱 M inferInstance
  exact nonempty_iso_tensorUnit_of_curveEulerChar_eq_of_ne_zero x 𝒱 hM hχ s hs

#print axioms nonempty_iso_tensorUnit_of_principal_presentation
end MazurTransfer.FieldDivisorComparison

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Exact consumer of our accepted public perfect-field Riemann–Roch comparison.
Official Anthropic FLT pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: actual cohomology finiteness, dimensions and numerical degree.
Named downstream consumer: the unchanged actual order-13 arithmetic
Picard group correspondence.
-/
open CategoryTheory AlgebraicGeometry AlgebraicCurve TopologicalSpace

theorem MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase.{u}
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (x : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (M : X.Modules)
    (D : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (lSpaceOn (placesOf x U) D : Set X.functionField)) :
    letI := (baseToFunctionField x).toAlgebra
    Module.Finite K (𝒱.sectionsOf x M).H0 ∧ Module.Finite K (𝒱.sectionsOf x M).H1 ∧
      Module.finrank K (𝒱.sectionsOf x M).H0 = ell D ∧
      Module.finrank K (𝒱.sectionsOf x M).H1 = indexOfSpecialty D ∧
      (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1
        = Divisor.degree D + 1 - genusFF K X.functionField := by exact MazurTransfer.divisor_presentation_riemann_roch_over_perfect_field 𝒱 x hC M D φ hnat hsmul hinj hrange

#print axioms MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase

end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: expose the literal curve's structural algebra and geometry
through public theorem statements. Named downstream consumer: the unchanged
actual arithmetic Picard group equivalence. Actual curve: MazurTheorem WIP
at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Generic interfaces: official
Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
No chart, cohomology, genus, or constant-field implementation is imported.
-/

universe u
open AlgebraicGeometry AlgebraicCurve CategoryTheory
open _root_.MazurTorsion.XOneThirteenProjectiveCurve

namespace MazurTransfer.ArithmeticBridgePublicReuseGeometry
namespace MazurTransfer.Order13GoodCharacteristicCurveModel

variable (K : Type u) [Field K] [Fact ((104 : K) ≠ 0)]

instance actualCurve_isIntegral : IsIntegral (curveScheme K) :=
  (_root_.MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K Fact.out).1

instance actualCurve_smoothRelativeDimensionOne : SmoothOfRelativeDimension 1 (curveToBase K) :=
  (_root_.MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K Fact.out).2.1

instance actualCurve_isProper : IsProper (curveToBase K) :=
  (_root_.MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K Fact.out).2.2.1

instance actualCurve_isNoetherian : IsNoetherian (curveScheme K) :=
  (_root_.MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K Fact.out).2.2.2

instance actualCurve_isSmooth : Smooth (curveToBase K) :=
  SmoothOfRelativeDimension.smooth 1 _

abbrev actualCurveFunctionField : Type u := (curveScheme K).functionField

noncomputable instance actualCurveFunctionFieldAlgebra : Algebra K (actualCurveFunctionField K) :=
  (baseToFunctionField (curveToBase K)).toAlgebra

variable [PerfectField K]

instance actualCurve_geometricallyIntegral : GeometricallyIntegral (curveToBase K) :=
  _root_.MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out

instance actualFunctionFieldIsCurveOver : IsCurveOver K (actualCurveFunctionField K) :=
  (_root_.MazurTransfer.order13_actual_function_field_invariants K Fact.out).1

instance actualFunctionFieldEssFiniteType : Algebra.EssFiniteType K (actualCurveFunctionField K) :=
  (_root_.MazurTransfer.order13_actual_function_field_invariants K Fact.out).2.1

theorem actual_constantsAreBase_good_characteristic : ConstantsAreBase K (actualCurveFunctionField K) :=
  (_root_.MazurTransfer.order13_actual_function_field_invariants K Fact.out).2.2.1

theorem actual_genusFF_eq_two_good_characteristic : genusFF K (actualCurveFunctionField K) = 2 :=
  (_root_.MazurTransfer.order13_actual_function_field_invariants K Fact.out).2.2.2.1

#print axioms actualFunctionFieldIsCurveOver
#print axioms actual_constantsAreBase_good_characteristic
#print axioms actual_genusFF_eq_two_good_characteristic

end MazurTransfer.Order13GoodCharacteristicCurveModel

namespace MazurTorsion.XOneThirteenProjectiveCurve

noncomputable def actualTwoAffineOpenCover
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)] :
    (curveScheme K).TwoAffineOpenCover :=
  (_root_.MazurTransfer.order13_actual_function_field_invariants K Fact.out).2.2.2.2.some

#print axioms actualTwoAffineOpenCover

end MazurTorsion.XOneThirteenProjectiveCurve
end MazurTransfer.ArithmeticBridgePublicReuseGeometry

end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: every actual invertible sheaf on the literal order-13 curve
has a function-field divisor presentation whose cohomology satisfies the
genus-two Riemann-Roch formula over the perfect base field. Named downstream
consumer: the degree-zero arithmetic divisor class attached to an actual
Picard point over F₃ and F₅. Curve, rational place and genus: MazurTheorem WIP
at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Presentation and cohomology
arguments: official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0. ConstantsAreBase and genus two are proved actual-curve inputs.
-/

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.ArithmeticBridgePublicReuseGeometry.MazurTransfer.Order13GoodCharacteristicCurveModel

theorem MazurTransfer.order13_actual_line_bundle_divisor_riemann_roch
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (M : (curveScheme K).Modules) (hM : Scheme.Modules.IsInvertible M) :
    ∃ (D : Divisor K (actualCurveFunctionField K))
      (φ : ∀ U : (curveScheme K).Opens, Γ(M, U) →+ (actualCurveFunctionField K)),
      (∀ (U V : (curveScheme K).Opens) (h : V ≤ U), Nonempty V →
        ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : (curveScheme K).Opens) [Nonempty U]
        (a : Γ(curveScheme K, U)) (m : Γ(M, U)),
        φ U (a • m) = algebraMap Γ(curveScheme K, U) (actualCurveFunctionField K) a * φ U m) ∧
      (∀ U : (curveScheme K).Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : (curveScheme K).Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (lSpaceOn (placesOf (curveToBase K) U) D : Set (actualCurveFunctionField K))) ∧
      Module.Finite K (𝒱.sectionsOf (curveToBase K) M).H0 ∧
      Module.Finite K (𝒱.sectionsOf (curveToBase K) M).H1 ∧
      Module.finrank K (𝒱.sectionsOf (curveToBase K) M).H0 = ell D ∧
      (Module.finrank K (𝒱.sectionsOf (curveToBase K) M).H0 : ℤ) -
        Module.finrank K (𝒱.sectionsOf (curveToBase K) M).H1 = Divisor.degree D - 1 := by
  obtain ⟨D, φ, hnat, hsmul, hinj, hrange, _⟩ :=
    Scheme.Modules.IsInvertible.exists_divisor_range_eq_lSpaceOn (curveToBase K) M hM
  obtain ⟨h0, h1, hdim, _, hχ⟩ :=
    MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase 𝒱 (curveToBase K)
      (actual_constantsAreBase_good_characteristic K) M D φ hnat hsmul hinj hrange
  refine ⟨D, φ, hnat, hsmul, hinj, hrange, h0, h1, hdim, ?_⟩
  have hgenus := actual_genusFF_eq_two_good_characteristic K
  rw [hgenus] at hχ
  omega

#print axioms MazurTransfer.order13_actual_line_bundle_divisor_riemann_roch

end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: every base-field point of the actual order-13 represented
Picard scheme has a genuine degree-zero arithmetic divisor presentation.
Named downstream consumer: the map to the computed function-field Pic0 over
F₃ and F₅, followed by its still-required injectivity and surjectivity proofs.
Curve source: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Presentation, sheaf and Picard interfaces: official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.ArithmeticBridgePublicReuseGeometry.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.PublicDivisorPresentationInterface
open MazurTransfer.LineBundleFieldComparison

theorem MazurTransfer.order13_actual_tensorUnit_curveEulerChar
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover) :
    curveEulerChar (curveToBase K) 𝒱 (𝟙_ (curveScheme K).Modules) = -1 := by
  obtain ⟨φ, _, hnat, hsmul, hinj, hrange⟩ :=
    Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero (curveToBase K)
  obtain ⟨_, _, _, _, hχ⟩ :=
    MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase 𝒱 (curveToBase K)
      (actual_constantsAreBase_good_characteristic K) (𝟙_ (curveScheme K).Modules) 0
      φ hnat hsmul hinj hrange
  rw [actual_genusFF_eq_two_good_characteristic K] at hχ
  change curveEulerChar (curveToBase K) 𝒱 (𝟙_ (curveScheme K).Modules) = _ at hχ
  simpa using hχ

theorem MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    ∃ (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
      (φ : ∀ U : (curveScheme K).Opens,
        Γ(pointLineBundle (curveToBase K) ε D h a, U) →+ (actualCurveFunctionField K)),
      IsPresentation (curveToBase K) (pointLineBundle (curveToBase K) ε D h a) E.1 φ := by
  let N := pointLineBundle (curveToBase K) ε D h a
  have hN := pointLineBundle_isInvertible (curveToBase K) ε D h a
  obtain ⟨E, φ, hnat, hsmul, hinj, hrange, _, _, _, hχ⟩ :=
    MazurTransfer.order13_actual_line_bundle_divisor_riemann_roch K 𝒱 N hN
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out
  have hnχ := pointLineBundle_curveEulerChar_eq (curveToBase K) ε D h a 𝒱
  have hunit := MazurTransfer.order13_actual_tensorUnit_curveEulerChar K 𝒱
  have hdegree : Divisor.degree E = 0 := by
    change curveEulerChar (curveToBase K) 𝒱 N = Divisor.degree E - 1 at hχ
    change curveEulerChar (curveToBase K) 𝒱 N = _ at hnχ
    omega
  exact ⟨⟨E, Divisor.mem_degZero.mpr hdegree⟩, φ, ⟨hnat, hsmul, hinj, hrange⟩⟩

#print axioms MazurTransfer.order13_actual_tensorUnit_curveEulerChar
#print axioms MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Exact consumer of our accepted public tensor/divisor compatibility proof.
Official Anthropic FLT pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: tensor products map to addition of actual divisor classes.
Named downstream consumer: the unchanged actual order-13 arithmetic
Picard group correspondence.
-/
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve WithZero

theorem MazurTransfer.FieldDivisorComparison.presentationTensorPrincipal_of_constantsAreBase.{u}
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x] (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (L L' : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (hL' : Scheme.Modules.IsInvertible L')
    (D D' D'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V ((L).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ(L', U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L', U), φ' V ((L').presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L', U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField))
    (φ'' : ∀ U : X.Opens, Γ(L ⊗ L', U) →+ (X.functionField : Type u))
    (hnat'' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L ⊗ L', U), φ'' V ((L ⊗ L').presheaf.map (homOfLE h).op m) = φ'' U m)
    (hsmul'' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L ⊗ L', U)),
      φ'' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ'' U m)
    (hinj'' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ'' U))
    (hrange'' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ'' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D'' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D'' - D - D') := by exact MazurTransfer.tensor_presentation_principal_over_perfect_field x hC L L' hL hL' D D' D'' φ hnat hsmul hinj hrange φ' hnat' hsmul' hinj' hrange' φ'' hnat'' hsmul'' hinj'' hrange''

#print axioms MazurTransfer.FieldDivisorComparison.presentationTensorPrincipal_of_constantsAreBase

end

section
/-
Copyright (c) 2026 Vas and contributors. All rights reserved.
Released under Apache-2.0 license as described in the file LICENSE.

Design boundary: attach a degree-zero function-field divisor class to each
actual base-field Picard point, and prove independence from the chosen divisor
presentation. Named downstream consumer: the finite-field divisor-class/
Jacobian bijection over F₃ and F₅. Injectivity, surjectivity, group-law
compatibility and comparison with the computed function-field model are not
asserted by this interface. Curve source: MazurTheorem at
54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Generic presentation inputs:
official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2,
Apache-2.0, with the perfect-field constant-property argument explicit.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.ArithmeticBridgePublicReuseGeometry.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.PublicDivisorPresentationInterface
open MazurTransfer.PublicPicardPointKernelHelpers
open MazurTransfer.LineBundleFieldComparison

namespace MazurTransfer.Order13ArithmeticPicardPointMap

variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
variable (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase)

noncomputable def pointDivisor : Divisor.degZero (K := K) (F := actualCurveFunctionField K) :=
  (MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h a).choose

private noncomputable def pointPresentation :
    ∀ U : (curveScheme K).Opens,
      Γ(pointLineBundle (curveToBase K) ε D h a, U) →+ (actualCurveFunctionField K) :=
  (MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h a).choose_spec.choose

private theorem pointPresentation_spec :
    IsPresentation (curveToBase K) (pointLineBundle (curveToBase K) ε D h a)
      (pointDivisor K 𝒱 ε D h a).1 (pointPresentation K 𝒱 ε D h a) :=
  (MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h a).choose_spec.choose_spec

noncomputable def arithmeticClass : Pic0 K (actualCurveFunctionField K) :=
  Pic0.mk (pointDivisor K 𝒱 ε D h a)

/-- Any genuine degree-zero divisor presentation of the point's line bundle
gives the same arithmetic class, independently of every choice of section map. -/
theorem arithmeticClass_eq_of_presentation
    (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
    (φ : ∀ U : (curveScheme K).Opens,
      Γ(pointLineBundle (curveToBase K) ε D h a, U) →+ (actualCurveFunctionField K))
    (hE : IsPresentation (curveToBase K) (pointLineBundle (curveToBase K) ε D h a) E.1 φ) :
    Pic0.mk E = arithmeticClass K 𝒱 ε D h a := by
  let N := pointLineBundle (curveToBase K) ε D h a
  have hp := pointPresentation_spec K 𝒱 ε D h a
  have hsec : ∃ (U : (curveScheme K).Opens) (m : Γ(N, U)), m ≠ 0 := by
    obtain ⟨U, s, hη, hs⟩ :=
      (pointLineBundle_isInvertible (curveToBase K) ε D h a).exists_isFrameOn
        (genericPoint (curveScheme K))
    letI : Nonempty U := ⟨⟨_, hη⟩⟩
    exact ⟨U, s,
      MazurTransfer.PublicFrameNonzeroHelper.frame_ne_zero_of_nontrivial hs⟩
  obtain ⟨_, _, _, _, hP⟩ :=
    MazurTransfer.FieldDivisorComparison.presentationRatioPrincipal_of_constantsAreBase
      (curveToBase K) (actual_constantsAreBase_good_characteristic K) N E.1
      (pointDivisor K 𝒱 ε D h a).1 φ (pointPresentation K 𝒱 ε D h a)
      hE.nat hp.nat hE.smul hp.smul hE.inj hp.inj hE.range hp.range hsec
  exact (pic0_mk_eq_iff E (pointDivisor K 𝒱 ε D h a)).mpr
    ((pic_mk_eq_iff _ _).mpr hP)

#print axioms arithmeticClass_eq_of_presentation

end MazurTransfer.Order13ArithmeticPicardPointMap

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Curve source: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Generic presentation and Picard interfaces: official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: a point maps to zero in the actual arithmetic divisor-class
group exactly when its actual line bundle is trivial. Named downstream
consumer: injectivity and group compatibility of the order-13 arithmetic
Picard-point map over F₃ and F₅. Those conclusions are not asserted here.
-/

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.ArithmeticBridgePublicReuseGeometry.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.PublicDivisorPresentationInterface
open MazurTransfer.PublicPicardPointKernelHelpers
open MazurTransfer.LineBundleFieldComparison

namespace MazurTransfer.Order13ArithmeticPicardPointMap

theorem arithmeticClass_eq_zero_iff_pointLineBundle_iso_unit
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    arithmeticClass K 𝒱 ε D h a = 0 ↔
      Nonempty (pointLineBundle (curveToBase K) ε D h a ≅ 𝟙_ (curveScheme K).Modules) := by
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out
  constructor
  · intro ha
    obtain ⟨E, φ, hp⟩ :=
      MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h a
    have hmk : Pic0.mk E = Pic0.mk 0 := by
      rw [Pic0.mk_zero, arithmeticClass_eq_of_presentation K 𝒱 ε D h a E φ hp, ha]
    have hP : Divisor.IsPrincipal E.1 := by
      have hp0 := (pic_mk_eq_iff E.1 0).mp ((pic0_mk_eq_iff E 0).mp hmk)
      simpa only [sub_zero] using hp0
    exact MazurTransfer.FieldDivisorComparison.nonempty_iso_tensorUnit_of_principal_presentation
      (curveToBase K) 𝒱 (pointLineBundle (curveToBase K) ε D h a)
      (pointLineBundle_isInvertible (curveToBase K) ε D h a)
      (pointLineBundle_curveEulerChar_eq (curveToBase K) ε D h a 𝒱) E.1 φ hp hP
  · rintro ⟨e⟩
    obtain ⟨φ, hp⟩ := exists_isPresentation_unit (curveToBase K)
    have hpN := hp.of_iso e
    have hz := arithmeticClass_eq_of_presentation K 𝒱 ε D h a 0
      (fun U => (φ U).comp (Scheme.Modules.Hom.app e.hom U).hom) hpN
    exact hz.symm.trans Pic0.mk_zero

#print axioms arithmeticClass_eq_zero_iff_pointLineBundle_iso_unit
end MazurTransfer.Order13ArithmeticPicardPointMap

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Curve source: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Generic Picard and divisor interfaces: official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the actual arithmetic Picard-point map preserves tensor
multiplication and has trivial kernel, hence is injective over every perfect
field with 104 nonzero. Named downstream consumer: the actual finite-field
Picard/divisor-class bijection over F₃ and F₅. Surjectivity and identification
with the computed function-field model remain separate obligations.
-/

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.ArithmeticBridgePublicReuseGeometry.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.PublicDivisorPresentationInterface
open MazurTransfer.PublicPicardPointKernelHelpers
open MazurTransfer.LineBundleFieldComparison
open scoped CategoryTheory.MonObj

namespace MazurTransfer.Order13ArithmeticPicardPointMap

variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

noncomputable def pointOfOverHom (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase :=
  ⟨a.left, by simpa only [Over.mk_left, Over.mk_hom] using Over.w a⟩

noncomputable def overHomOfPoint (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase :=
  Over.homMk a.1 a.2

noncomputable def arithmeticClassOver
    (a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) :
    Pic0 K (actualCurveFunctionField K) :=
  arithmeticClass K 𝒱 ε D h (pointOfOverHom K D a)

theorem pointLineBundle_over_one_iso_unit :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    Nonempty (pointLineBundle (curveToBase K) ε D h (pointOfOverHom K D 1) ≅
      𝟙_ (curveScheme K).Modules) := by
  let hG : RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D := h
  letI := hG.grpObj
  obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_one_iso hG
    (Over.mk (𝟙 (Spec (CommRingCat.of K))))
  exact ⟨(Scheme.Modules.pullback (toProdSpec (curveToBase K))).mapIso i ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso (toProdSpec (curveToBase K))⟩

theorem arithmeticClassOver_one :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    arithmeticClassOver K 𝒱 ε D h 1 = 0 := by
  letI := (show RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
  exact (arithmeticClass_eq_zero_iff_pointLineBundle_iso_unit K 𝒱 ε D h _).mpr
    (pointLineBundle_over_one_iso_unit K ε D h)

theorem arithmeticClassOver_mul :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    ∀ a b : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase,
      arithmeticClassOver K 𝒱 ε D h (a * b) =
        arithmeticClassOver K 𝒱 ε D h a + arithmeticClassOver K 𝒱 ε D h b := by
  let hG : RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D := h
  letI := hG.grpObj
  intro a b
  let pa := pointOfOverHom K D a
  let pb := pointOfOverHom K D b
  let pab := pointOfOverHom K D (a * b)
  obtain ⟨Ea, φa, ha⟩ :=
    MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h pa
  obtain ⟨Eb, φb, hb⟩ :=
    MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h pb
  obtain ⟨Eab, φab, hab⟩ :=
    MazurTransfer.order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h pab
  obtain ⟨i⟩ := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso hG a b
  let i' : pointLineBundle (curveToBase K) ε D h pab ≅
      pointLineBundle (curveToBase K) ε D h pa ⊗ pointLineBundle (curveToBase K) ε D h pb :=
    (Scheme.Modules.pullback (toProdSpec (curveToBase K))).mapIso i ≪≫
      Scheme.Modules.pullbackTensorObjIso (toProdSpec (curveToBase K)) _ _
  have hp := hab.of_iso i'.symm
  have hP := MazurTransfer.FieldDivisorComparison.presentationTensorPrincipal_of_constantsAreBase
    (curveToBase K) (actual_constantsAreBase_good_characteristic K)
    (pointLineBundle (curveToBase K) ε D h pa) (pointLineBundle (curveToBase K) ε D h pb)
    (pointLineBundle_isInvertible (curveToBase K) ε D h pa)
    (pointLineBundle_isInvertible (curveToBase K) ε D h pb)
    Ea.1 Eb.1 Eab.1 φa ha.nat ha.smul ha.inj ha.range φb hb.nat hb.smul hb.inj hb.range
    (fun U => (φab U).comp (Scheme.Modules.Hom.app i'.symm.hom U).hom)
    hp.nat hp.smul hp.inj hp.range
  have hcl : Pic0.mk Eab = Pic0.mk (Ea + Eb) :=
    (pic0_mk_eq_iff Eab (Ea + Eb)).mpr ((pic_mk_eq_iff _ _).mpr (by
      simpa only [AddSubgroup.coe_add, sub_add_eq_sub_sub] using hP))
  rw [Pic0.mk_add,
    arithmeticClass_eq_of_presentation K 𝒱 ε D h pab Eab φab hab,
    arithmeticClass_eq_of_presentation K 𝒱 ε D h pa Ea φa ha,
    arithmeticClass_eq_of_presentation K 𝒱 ε D h pb Eb φb hb] at hcl
  exact hcl

theorem arithmeticClassOver_eq_zero_iff_eq_one :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase,
      arithmeticClassOver K 𝒱 ε D h a = 0 ↔ a = 1 := by
  letI := (show RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
  intro a
  constructor
  · intro ha
    obtain ⟨ia⟩ := (arithmeticClass_eq_zero_iff_pointLineBundle_iso_unit K 𝒱 ε D h _).mp ha
    obtain ⟨i1⟩ := pointLineBundle_over_one_iso_unit K ε D h
    have hp := (pointLineBundle_iso_iff (curveToBase K) ε D h
      (pointOfOverHom K D a) (pointOfOverHom K D 1)).mp ⟨ia ≪≫ i1.symm⟩
    exact Over.OverMorphism.ext (congrArg Subtype.val hp)
  · rintro rfl
    exact arithmeticClassOver_one K 𝒱 ε D h

theorem arithmeticClassOver_injective : Function.Injective (arithmeticClassOver K 𝒱 ε D h) := by
  letI := (show RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
  intro a b hab
  have h4 : arithmeticClassOver K 𝒱 ε D h (b * b⁻¹) = 0 := by
    rw [mul_inv_cancel, arithmeticClassOver_one K 𝒱 ε D h]
  have h3 : arithmeticClassOver K 𝒱 ε D h (a * b⁻¹) = 0 := by
    rw [arithmeticClassOver_mul K 𝒱 ε D h] at h4 ⊢
    rw [hab]
    exact h4
  have h1 := (arithmeticClassOver_eq_zero_iff_eq_one K 𝒱 ε D h _).mp h3
  exact mul_inv_eq_one.mp h1

/-- The choice-independent arithmetic class map on actual base-field points is injective. -/
theorem arithmeticClass_injective : Function.Injective (arithmeticClass K 𝒱 ε D h) := by
  intro a b hab
  have hp : overHomOfPoint K D a = overHomOfPoint K D b :=
    arithmeticClassOver_injective K 𝒱 ε D h hab
  exact Subtype.ext (congrArg (fun f => f.left) hp)

#print axioms arithmeticClassOver_mul
#print axioms arithmeticClassOver_injective
#print axioms arithmeticClass_injective
end MazurTransfer.Order13ArithmeticPicardPointMap

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Generic ideal, valuation, presentation and tensor proofs reuse official Anthropic
FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: every function-field divisor on an actual smooth proper
integral curve over a perfect field is realized, up to a principal divisor,
by an actual invertible sheaf. Nonrational closed points are included.
Named downstream consumer: surjectivity of the actual order-13 arithmetic
Picard-point map over F₃ and F₅. The constant-field property is explicit.
-/

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open MazurTransfer.PublicDivisorPresentationInterface

namespace MazurTransfer.PublicFieldDivisorRealization
open MazurTransfer.FieldDivisorComparison

variable {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
variable [IsIntegral X] [IsLocallyNoetherian X]
variable (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [SmoothOfRelativeDimension 1 x]

/-- Actual sheaf realization of a divisor class, using a genuine section presentation. -/
def DivisorClassRealized
    (E : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField) : Prop :=
  letI := (baseToFunctionField x).toAlgebra
  ∃ (M : X.Modules), Scheme.Modules.IsInvertible M ∧
    ∃ (G : Divisor K X.functionField)
      (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u)),
      IsPresentation x M G φ ∧ Divisor.IsPrincipal (G - E)

variable (hC : letI := (baseToFunctionField x).toAlgebra; ConstantsAreBase K X.functionField)

theorem divisorClassRealized_zero : DivisorClassRealized x 0 := by
  letI := (baseToFunctionField x).toAlgebra
  obtain ⟨φ, hp⟩ := exists_isPresentation_unit x
  exact ⟨𝟙_ X.Modules, Scheme.Modules.isInvertible_unit X, 0, φ, hp,
    by rw [sub_zero]; exact Divisor.mem_principal.mp (Divisor.principal (K := K) (F := X.functionField)).zero_mem⟩

include hC

theorem divisorClassRealized_signed_single
    (v : letI := (baseToFunctionField x).toAlgebra; Place K X.functionField) (n : ℕ) :
    letI := (baseToFunctionField x).toAlgebra
    DivisorClassRealized x (n • Finsupp.single v 1) ∧
      DivisorClassRealized x (-(n • Finsupp.single v 1)) := by
  letI := (baseToFunctionField x).toAlgebra
  obtain ⟨y, hy, hv⟩ := exists_closedPoint_range_stalk_eq x v
  let P : Spec (CommRingCat.of (X.residueField y)) ⟶ X := X.fromSpecResidueField y
  letI : IsClosedImmersion P := isClosed_singleton_iff_isClosedImmersion.mp hy
  have hI : (P.ker ^ n).IsInvertible :=
    (MazurTransfer.closed_point_kernel_invertible_over_field x P).pow n
  obtain ⟨G, φ, hp⟩ := exists_isPresentation x hI.isInvertible_invModule
  obtain ⟨G', φ', hp'⟩ := exists_isPresentation x hI.isInvertible_module
  have hv' :
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint (X.residueField y))))
        X.functionField).range = v.toValuationSubring.toSubring := by
    have he : P.base (IsLocalRing.closedPoint (X.residueField y)) = y :=
      X.fromSpecResidueField_apply y _
    rw [he]
    exact hv
  have hpr := MazurTransfer.closed_point_kernel_presentations_signed_divisor_classes
    x hC P n v hv' G G' φ hp.nat hp.smul hp.inj hp.range
    φ' hp'.nat hp'.smul hp'.inj hp'.range
  exact ⟨⟨(P.ker ^ n).invModule, hI.isInvertible_invModule, G, φ, hp, hpr.1⟩,
    ⟨(P.ker ^ n).module, hI.isInvertible_module, G', φ', hp',
      by simpa only [sub_neg_eq_add] using hpr.2⟩⟩

theorem divisorClassRealized_add
    (E E' : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField)
    (hE : DivisorClassRealized x E) (hE' : DivisorClassRealized x E') :
    DivisorClassRealized x (E + E') := by
  letI := (baseToFunctionField x).toAlgebra
  obtain ⟨M, hM, G, φ, hp, hG⟩ := hE
  obtain ⟨N, hN, G', ψ, hp', hG'⟩ := hE'
  obtain ⟨H, χ, hpH⟩ := exists_isPresentation x (hM.tensor hN)
  have hP := presentationTensorPrincipal_of_constantsAreBase x hC M N hM hN G G' H
    φ hp.nat hp.smul hp.inj hp.range ψ hp'.nat hp'.smul hp'.inj hp'.range
    χ hpH.nat hpH.smul hpH.inj hpH.range
  have htotal : Divisor.IsPrincipal ((H - G - G') + (G - E) + (G' - E')) :=
    (Divisor.principal (K := K) (F := X.functionField)).add_mem
      ((Divisor.principal (K := K) (F := X.functionField)).add_mem hP hG) hG'
  have heq : (H - G - G') + (G - E) + (G' - E') = H - (E + E') := by abel
  rw [heq] at htotal
  exact ⟨M ⊗ N, hM.tensor hN, H, χ, hpH, htotal⟩

/-- Full divisor-class realization, with arbitrary integer coefficients and closed points. -/
theorem divisorClassRealized_all
    (E : letI := (baseToFunctionField x).toAlgebra; Divisor K X.functionField) :
    DivisorClassRealized x E := by
  letI := (baseToFunctionField x).toAlgebra
  have hsingle : ∀ (v : Place K X.functionField) (n : ℤ),
      DivisorClassRealized x (Finsupp.single v n) := by
    intro v n
    cases n with
    | ofNat n =>
      simpa [Finsupp.smul_single, nsmul_eq_mul] using
        (divisorClassRealized_signed_single x hC v n).1
    | negSucc n =>
      simpa [Finsupp.smul_single, nsmul_eq_mul, Int.negSucc_eq] using (divisorClassRealized_signed_single x hC v (n + 1)).2
  induction E using Finsupp.induction with
  | zero => exact divisorClassRealized_zero x
  | single_add v n E _ _ ih =>
    exact divisorClassRealized_add x hC _ _ (hsingle v n) ih

#print axioms divisorClassRealized_all
end MazurTransfer.PublicFieldDivisorRealization

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Generic presentations and Picard arguments reuse official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: all actual arithmetic degree-zero divisor classes come from
base-field points of the represented Picard scheme, over every perfect field
of characteristic not dividing 104. Nonrational closed points are included.
Named downstream consumer: the actual order-13 arithmetic Picard-point
bijection, then comparison with finite-field divisor-class computations.
-/

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.ArithmeticBridgePublicReuseGeometry.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.PublicDivisorPresentationInterface
open MazurTransfer.PublicPicardPointKernelHelpers
open MazurTransfer.LineBundleFieldComparison

namespace MazurTransfer.PublicArithmeticPicardSurjectivity
open MazurTransfer.Order13ArithmeticPicardPointMap

variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

theorem arithmeticClass_surjective : Function.Surjective (arithmeticClass K 𝒱 ε D h) := by
  letI : GeometricallyIntegral (curveToBase K) :=
    MazurTransfer.order13_actual_good_characteristic_geometric_integrality K Fact.out
  intro c
  obtain ⟨E, rfl⟩ := Pic0.mk_surjective c
  obtain ⟨M, hM, G, φ, hp, hP⟩ :=
    MazurTransfer.PublicFieldDivisorRealization.divisorClassRealized_all
      (curveToBase K) (actual_constantsAreBase_good_characteristic K) E.1
  have hdegree : Divisor.degree G = 0 := by
    have hz := degree_eq_zero_of_isPrincipal hP
    rw [map_sub] at hz
    have he := Divisor.mem_degZero.mp E.2
    omega
  obtain ⟨_, _, _, _, hχ⟩ :=
    MazurTransfer.FieldDivisorComparison.riemannRoch_of_constantsAreBase 𝒱 (curveToBase K)
      (actual_constantsAreBase_good_characteristic K) M G φ hp.nat hp.smul hp.inj hp.range
  rw [actual_genusFF_eq_two_good_characteristic K, hdegree] at hχ
  have hχM : curveEulerChar (curveToBase K) 𝒱 M =
      curveEulerChar (curveToBase K) 𝒱 (𝟙_ (curveScheme K).Modules) := by
    rw [MazurTransfer.order13_actual_tensorUnit_curveEulerChar K 𝒱]
    change curveEulerChar (curveToBase K) 𝒱 M = _ at hχ
    omega
  obtain ⟨a, ⟨e⟩, _⟩ := existsUnique_pointLineBundle_iso_of_curveEulerChar_eq
    (curveToBase K) ε D h M hM 𝒱 hχM
  let G0 : Divisor.degZero (K := K) (F := actualCurveFunctionField K) :=
    ⟨G, Divisor.mem_degZero.mpr hdegree⟩
  have ha := arithmeticClass_eq_of_presentation K 𝒱 ε D h a G0
    (fun U => (φ U).comp (Scheme.Modules.Hom.app e.hom U).hom) (hp.of_iso e)
  have hm : Pic0.mk G0 = Pic0.mk E :=
    (pic0_mk_eq_iff G0 E).mpr ((pic_mk_eq_iff G E.1).mpr hP)
  exact ⟨a, ha.symm.trans hm⟩

theorem arithmeticClass_bijective : Function.Bijective (arithmeticClass K 𝒱 ε D h) :=
  ⟨arithmeticClass_injective K 𝒱 ε D h, arithmeticClass_surjective K 𝒱 ε D h⟩

/-- Genuine points of the actual represented Picard scheme classify actual
arithmetic divisor classes over the base field. -/
noncomputable def arithmeticClassEquiv :
    SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase ≃
      Pic0 K (actualCurveFunctionField K) :=
  Equiv.ofBijective (arithmeticClass K 𝒱 ε D h) (arithmeticClass_bijective K 𝒱 ε D h)

#print axioms arithmeticClass_surjective
#print axioms arithmeticClass_bijective
#print axioms arithmeticClassEquiv
end MazurTransfer.PublicArithmeticPicardSurjectivity

end

section
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Curve: MazurTheorem at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c.
Generic Picard and presentation arguments reuse official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the genuine group of points of the actual represented
Picard scheme is isomorphic to actual degree-zero arithmetic divisor classes.
Named downstream consumer: finite-field Jacobian cardinality and reduction.
-/

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.ArithmeticBridgePublicReuseGeometry.MazurTransfer.Order13GoodCharacteristicCurveModel
open scoped CategoryTheory.MonObj
namespace MazurTransfer.PublicArithmeticPicardGroupEquiv
open MazurTransfer.Order13ArithmeticPicardPointMap
open MazurTransfer.PublicArithmeticPicardSurjectivity
variable (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
variable (𝒱 : (curveScheme K).TwoAffineOpenCover)
variable (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
variable (D : RelativePic0Designation K (curveToBase K))
variable (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)

theorem arithmeticClassOver_surjective : Function.Surjective (arithmeticClassOver K 𝒱 ε D h) := by
  intro c
  obtain ⟨a, ha⟩ := MazurTransfer.PublicArithmeticPicardSurjectivity.arithmeticClass_surjective K 𝒱 ε D h c
  exact ⟨overHomOfPoint K D a, ha⟩

noncomputable def arithmeticClassGroupEquiv :
    letI := (show RepresentsRelSubPic (curveToBase K) ε
      (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
    (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) ≃*
      Multiplicative (Pic0 K (actualCurveFunctionField K)) := by
  letI := (show RepresentsRelSubPic (curveToBase K) ε
    (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
  let f : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) →*
      Multiplicative (Pic0 K (actualCurveFunctionField K)) :=
    { toFun := fun a => Multiplicative.ofAdd (arithmeticClassOver K 𝒱 ε D h a)
      map_one' := arithmeticClassOver_one K 𝒱 ε D h
      map_mul' := arithmeticClassOver_mul K 𝒱 ε D h }
  exact MulEquiv.ofBijective f
    ⟨arithmeticClassOver_injective K 𝒱 ε D h, arithmeticClassOver_surjective K 𝒱 ε D h⟩

end MazurTransfer.PublicArithmeticPicardGroupEquiv
open MazurTransfer.PublicArithmeticPicardGroupEquiv

/-- The representing scheme and the genuine group equivalence are constructed
for the literal order-13 curve, rather than assumed as extra hypotheses. -/
theorem MazurTransfer.order13_actual_picard_arithmetic_group_equiv_from_public_closed_points
    (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0)
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K)) :
    letI : Fact ((104 : K) ≠ 0) := ⟨h104⟩
    ∃ (D : RelativePic0Designation K (curveToBase K))
      (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D),
      letI := (show RepresentsRelSubPic (curveToBase K) ε
        (algEquivZeroGroupCut (curveToBase K) ε).toSubPicCondition D from h).grpObj
      Nonempty ((Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) ≃*
        Multiplicative (Pic0 K (actualCurveFunctionField K))) := by
  letI : Fact ((104 : K) ≠ 0) := ⟨h104⟩
  obtain ⟨D, h, _, _, _, _, _, _, _, _, _⟩ :=
    (MazurTransfer.order13_actual_picard_abel_jacobi_good_characteristic K h104).2 ε
  exact ⟨D, h, ⟨arithmeticClassGroupEquiv K 𝒱 ε D h⟩⟩

#print axioms MazurTransfer.PublicArithmeticPicardGroupEquiv.arithmeticClassGroupEquiv
#print axioms MazurTransfer.order13_actual_picard_arithmetic_group_equiv_from_public_closed_points

end

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem solution.{u}
    (K : Type u) [Field K] [PerfectField K] (h104 : (104 : K) ≠ 0)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K)))
      (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)) :
    letI : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K) :=
      (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104).1
    letI : Algebra K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField :=
      (baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)).toAlgebra
    ∃ (D : RelativePic0Designation K (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K))
      (h : RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
        (algEquivZeroCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε) D),
      letI := (show RepresentsRelSubPic (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε
        (algEquivZeroGroupCut (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K) ε).toSubPicCondition D from h).grpObj
      Nonempty ((Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk D.toBase) ≃*
        Multiplicative (Pic0 K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField)) := by
  letI : Fact ((104 : K) ≠ 0) := ⟨h104⟩
  letI : IsIntegral (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K) :=
    (MazurTransfer.order13_actual_good_characteristic_geometry_and_finite_field_points.1 K h104).1
  letI : Algebra K (MazurTorsion.XOneThirteenProjectiveCurve.curveScheme K).functionField :=
    (baseToFunctionField (MazurTorsion.XOneThirteenProjectiveCurve.curveToBase K)).toAlgebra
  obtain ⟨D, h, _, _, _, _, _, _, _, _, _⟩ :=
    (MazurTransfer.order13_actual_picard_abel_jacobi_good_characteristic K h104).2 ε
  exact ⟨D, h, ⟨MazurTransfer.PublicArithmeticPicardGroupEquiv.arithmeticClassGroupEquiv K
    (MazurTransfer.ArithmeticBridgePublicReuseGeometry.MazurTorsion.XOneThirteenProjectiveCurve.actualTwoAffineOpenCover K)
    ε D h⟩⟩


#print axioms solution
