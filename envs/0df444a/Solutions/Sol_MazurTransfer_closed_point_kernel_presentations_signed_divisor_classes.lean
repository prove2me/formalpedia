-- Prove2me | solution 1 for MazurTransfer.closed_point_kernel_presentations_signed_divisor_classes
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T00:33:01.507873+00:00
-- url     : https://prove2.me/submissions/84e3bc7b-f41d-4ac1-9112-0a3262a84f6f

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete official Anthropic FLT kernel-presentation proof
at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: both signed divisor classes of arbitrary closed points,
with full compatible injective section presentations and explicit full
constant field. Named downstream consumer: realization of every divisor
class and the unchanged actual order-13 arithmetic Picard correspondence.
The residue field need not equal the base field.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_MazurTransfer_closed_point_kernel_invertible_over_field
import Theorems.Thm_MazurTransfer_closed_point_kernel_power_generator_orders
import Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective

open CategoryTheory AlgebraicGeometry AlgebraicCurve Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules CategoryTheory.MonoidalCategory

universe u
theorem solution
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsLocallyNoetherian X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra; ConstantsAreBase K X.functionField)
    {L : Type u} [Field L] (P : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion P] (n : ℕ)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint L))) X.functionField).range =
        v.toValuationSubring.toSubring)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ((P.ker ^ n).invModule, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).invModule, U), φ V (((P.ker ^ n).invModule).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).invModule, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ((P.ker ^ n).module, U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).module, U), φ' V (((P.ker ^ n).module).presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).module, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D - n • Finsupp.single v 1) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D' + n • Finsupp.single v 1) := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  set pt : X := P.base (IsLocalRing.closedPoint L) with hpt
  have hI : (P.ker ^ n).IsInvertible := (MazurTransfer.closed_point_kernel_invertible_over_field x P).pow n

  have hplace : ∀ (y : X) (w : Place K X.functionField),
      (algebraMap (X.presheaf.stalk y) X.functionField).range = w.toValuationSubring.toSubring →
      ((pt = y → w = v) ∧ (pt ≠ y → w ≠ v)) := by
    intro y w hw
    constructor
    · rintro rfl
      apply Place.ext
      apply ValuationSubring.toSubring_injective
      exact hw.symm.trans hv
    · intro hne heq
      apply hne
      subst heq
      exact (eq_of_range_stalk_eq x pt y (hv.trans hw.symm))

  have hcoef : ∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} : Set X) →
      (P.ker ^ n).ideal ⟨U, hU⟩ = Ideal.span {g} →
      ∀ w : Place K X.functionField,
        (algebraMap (X.presheaf.stalk y) X.functionField).range = w.toValuationSubring.toSubring →
        haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
        ((n • Finsupp.single v (1 : ℤ) : Divisor K X.functionField) w : ℤ) =
          w.ord (algebraMap Γ(X, U) X.functionField g) := by
    intro U hU g y hyU hy hg w hw
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    have hord := MazurTransfer.closed_point_kernel_power_generator_orders x P n U hU g hg y hyU hy w hw
    obtain ⟨h1, h2⟩ := hplace y w hw
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, nsmul_eq_mul]
    by_cases hyp : pt = y
    · rw [hord.1 hyp, if_pos (h1 hyp).symm, mul_one]
    · rw [hord.2 hyp, if_neg (fun h => h2 hyp h.symm), mul_zero]
  constructor
  ·
    obtain ⟨D₀, φ₀, ⟨h1, h2, h3, h4, h5⟩, hf, hpin⟩ :=
      Scheme.IdealSheafData.IsInvertible.exists_divisor_range_invModule_eq_lSpaceOn x hI
    have hsec : ∃ (U : X.Opens) (m : Γ((P.ker ^ n).invModule, U)), m ≠ 0 :=
      ⟨⊤, (P.ker ^ n).invModuleSection.app ⊤ (toUnitSection ⊤ 1), fun h => hf (by rw [h, map_zero])⟩
    obtain ⟨g₁, hg₁, -, hDw, -⟩ := MazurTransfer.presentation_ratio_principal_over_perfect_field x hC _ D D₀ φ φ₀
      hnat h1 hsmul h2 hinj h3 hrange h4 hsec
    refine ⟨g₁ * (φ₀ ⊤ ((P.ker ^ n).invModuleSection.app ⊤ (toUnitSection ⊤ 1)))⁻¹,
      mul_ne_zero hg₁ (inv_ne_zero hf), fun w => ?_⟩
    obtain ⟨y, hy, hw⟩ := exists_closedPoint_range_stalk_eq x w
    obtain ⟨U, r, hyr, g, -, hIg⟩ := hI y
    have hc := hcoef (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    have hp := hpin (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    simp only [Finsupp.coe_sub, Pi.sub_apply]
    rw [hc, hDw w, Place.ord_mul _ hg₁ (inv_ne_zero hf), Place.ord_inv]
    haveI : Nonempty (X.affineBasicOpen r : X.Opens) := ⟨⟨y, hyr⟩⟩
    have hp' : D₀ w + w.ord (φ₀ ⊤ ((P.ker ^ n).invModuleSection.app ⊤ (toUnitSection ⊤ 1))) =
        w.ord (algebraMap Γ(X, X.affineBasicOpen r) X.functionField g) := hp
    change D₀ w + w.ord g₁ - _ = _
    omega
  ·
    obtain ⟨D₀, φ₀, ⟨h1, h2, h3, h4, h5⟩, c, hc0, hcφ, hpin⟩ :=
      Scheme.IdealSheafData.IsInvertible.exists_divisor_range_module_eq_lSpaceOn x hI

    have hsec : ∃ (U : X.Opens) (m : Γ((P.ker ^ n).module, U)), m ≠ 0 := by
      obtain ⟨U, r, hηr, g, hgnz, hIg⟩ := hI (genericPoint X)
      haveI : Nonempty (X.affineBasicOpen r : X.Opens) := ⟨⟨genericPoint X, hηr⟩⟩
      have hrg := (Scheme.IdealSheafData.range_moduleIota_app_and_injective (P.ker ^ n) (X.affineBasicOpen r)).1
      have hgmem : (toUnitSection (X.affineBasicOpen r) g) ∈ Set.range ((P.ker ^ n).moduleι.app (X.affineBasicOpen r)) := by
        rw [hrg, hIg]
        exact Ideal.mem_span_singleton_self g
      obtain ⟨m, hm⟩ := hgmem
      refine ⟨X.affineBasicOpen r, m, fun h0 => ?_⟩
      rw [h0, map_zero] at hm
      have : g = 0 := (ofUnitSection_injective _ hm).symm
      exact nonZeroDivisors.ne_zero hgnz this
    obtain ⟨g₂, hg₂, -, hDw, -⟩ := MazurTransfer.presentation_ratio_principal_over_perfect_field x hC _ D' D₀ φ' φ₀
      hnat' h1 hsmul' h2 hinj' h3 hrange' h4 hsec
    refine ⟨g₂ * c⁻¹, mul_ne_zero hg₂ (inv_ne_zero hc0), fun w => ?_⟩
    obtain ⟨y, hy, hw⟩ := exists_closedPoint_range_stalk_eq x w
    obtain ⟨U, r, hyr, g, -, hIg⟩ := hI y
    have hc := hcoef (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    have hp := hpin (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [hc, hDw w, Place.ord_mul _ hg₂ (inv_ne_zero hc0), Place.ord_inv]
    haveI : Nonempty (X.affineBasicOpen r : X.Opens) := ⟨⟨y, hyr⟩⟩
    change D₀ w + w.ord g₂ + _ = _
    have hp' : D₀ w + w.ord c + w.ord (algebraMap Γ(X, X.affineBasicOpen r) X.functionField g) = 0 := hp
    omega


#print axioms solution
