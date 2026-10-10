-- Prove2me | solution 1 for MazurTransfer.all_divisor_classes_realized_over_perfect_field
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-10T00:39:35.56612+00:00
-- url     : https://prove2.me/submissions/32d29e44-00df-4396-8210-e6903facea43

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Complete presentation interfaces reuse official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
The finite-support induction and perfect-field closed-point adaptation are
separately checked MazurTheorem bridges by Vas and contributors.
Design boundary: every actual function-field divisor class is represented
by an invertible sheaf with a complete rational-section presentation.
Named downstream consumer: surjectivity of the unchanged actual order-13
arithmetic Picard-point map. Nonrational closed points and arbitrary integer
coefficients are included; no sheaf realization is assumed.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_divisor_range_eq_lSpaceOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
import Theorems.Thm_MazurTransfer_closed_point_kernel_invertible_over_field
import Theorems.Thm_MazurTransfer_closed_point_kernel_presentations_signed_divisor_classes
import Theorems.Thm_MazurTransfer_tensor_presentation_principal_over_perfect_field
import Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Mathlib.Tactic.Abel

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

namespace MazurTransfer.PublicDivisorClassRealizationPresentation

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

end MazurTransfer.PublicDivisorClassRealizationPresentation

#print axioms MazurTransfer.PublicDivisorClassRealizationPresentation.isInvertible_of_iso

#print axioms MazurTransfer.PublicDivisorClassRealizationPresentation.app_map_of_hom

#print axioms MazurTransfer.PublicDivisorClassRealizationPresentation.IsPresentation.of_iso

#print axioms MazurTransfer.PublicDivisorClassRealizationPresentation.exists_isPresentation

#print axioms MazurTransfer.PublicDivisorClassRealizationPresentation.exists_isPresentation_unit

#print axioms MazurTransfer.PublicDivisorClassRealizationPresentation.degree_eq_zero_of_isPrincipal

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
open MazurTransfer.PublicDivisorClassRealizationPresentation

namespace MazurTransfer.PublicAllDivisorClassRealizationHelpers


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
  have hP := MazurTransfer.tensor_presentation_principal_over_perfect_field x hC M N hM hN G G' H
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
end MazurTransfer.PublicAllDivisorClassRealizationHelpers

end

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicCurve

universe u
theorem solution
    {K : Type u} [Field K] [PerfectField K] {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X]
    (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x] [SmoothOfRelativeDimension 1 x]
    (hC : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.ConstantsAreBase K X.functionField)
    (E : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ (M : X.Modules), Scheme.Modules.IsInvertible M ∧
      ∃ (G : AlgebraicCurve.Divisor K X.functionField)
        (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u)),
        (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
        (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
        (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
        (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) G : Set X.functionField)) ∧
        AlgebraicCurve.Divisor.IsPrincipal (G - E) := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  obtain ⟨M, hM, G, φ, hp, hprincipal⟩ :=
    MazurTransfer.PublicAllDivisorClassRealizationHelpers.divisorClassRealized_all x hC E
  exact ⟨M, hM, G, φ, hp.nat, hp.smul, hp.inj, hp.range, hprincipal⟩

#print axioms solution
