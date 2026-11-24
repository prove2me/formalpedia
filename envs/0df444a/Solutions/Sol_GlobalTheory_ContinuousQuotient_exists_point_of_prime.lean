-- Prove2me | solution 1 for GlobalTheory.ContinuousQuotient.exists_point_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:04:53.761006+00:00
-- url     : https://prove2.me/submissions/e539ee04-e2c5-4fbd-be8e-ad6ddd9650ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EqZeroOfForallAlgHomComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsEqMulOfContinuousOnQuotient
import Theorems.Thm_GlobalTheory_existsUnique_point_of_ringHom


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
open scoped CategoryTheory.Obj TensorProduct Topology
open GlobalTheory GlobalTheory.ContinuousQuotient
namespace GlobalTheory.ContinuousQuotient
theorem _root_.solution (X : Over (Sp ℂ)) [LocallyOfFiniteType X.hom] {U : X.left.Opens}
    (hU : IsAffineOpen U) (p : Ideal Γ(X.left, U)) [p.IsPrime] {s : Γ(X.left, U)} (hs : s ∉ p) :
    ∃ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U ∧ valAt' x.left U s ≠ 0 ∧
      ∀ r ∈ p, valAt' x.left U r = 0 := by
  classical
  have hle : U ≤ X.hom ⁻¹ᵁ ⊤ := by simp
  let φ : ℂ →+* Γ(X.left, U) :=
    (X.hom.appLE ⊤ U hle).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  have hft : φ.FiniteType := by
    refine RingHom.FiniteType.comp (X.hom.finiteType_appLE (isAffineOpen_top _) hU hle) ?_
    exact RingHom.FiniteType.of_surjective _
      (fun x => ⟨(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom x, by simp⟩)
  letI : Algebra ℂ Γ(X.left, U) := φ.toAlgebra
  have : Algebra.FiniteType ℂ Γ(X.left, U) := hft
  have : IsJacobsonRing Γ(X.left, U) := isJacobsonRing_of_finiteType (A := ℂ)

  have hjac : p.jacobson = p := isJacobsonRing_iff_prime_eq.1 this p inferInstance
  obtain ⟨m, ⟨hpm, hm⟩, hsm⟩ : ∃ m : Ideal Γ(X.left, U), (p ≤ m ∧ m.IsMaximal) ∧ s ∉ m := by
    by_contra hno
    push Not at hno
    apply hs
    rw [← hjac, Ideal.jacobson, Ideal.mem_sInf]
    exact fun J hJ => hno J hJ
  letI : Field (Γ(X.left, U) ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType ℂ (Γ(X.left, U) ⧸ m) :=
    Algebra.FiniteType.trans (S := Γ(X.left, U)) inferInstance inferInstance
  have : Module.Finite ℂ (Γ(X.left, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ _
  let E : ℂ ≃+* (Γ(X.left, U) ⧸ m) :=
    RingEquiv.ofBijective (algebraMap ℂ _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : Γ(X.left, U) →+* ℂ := E.symm.toRingHom.comp (Ideal.Quotient.mk m)
  have he : ∀ a, e (constFn X.hom U a) = a := fun a => by
    change E.symm (Ideal.Quotient.mk m (φ a)) = a
    rw [RingEquiv.symm_apply_eq]
    rfl
  obtain ⟨x, ⟨hx, hxv⟩, -⟩ := existsUnique_point_of_ringHom X U hU e he
  refine ⟨x, hx, ?_, fun r hr => ?_⟩
  · rw [hxv]
    intro h0
    apply hsm
    have : Ideal.Quotient.mk m s = 0 := by
      have := congrArg E h0
      simpa [e] using this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  · rw [hxv]
    simp [e, Ideal.Quotient.eq_zero_iff_mem.2 (hpm hr)]
end GlobalTheory.ContinuousQuotient
