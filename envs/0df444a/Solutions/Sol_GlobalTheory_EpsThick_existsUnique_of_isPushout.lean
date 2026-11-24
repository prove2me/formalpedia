-- Prove2me | solution 1 for GlobalTheory.EpsThick.existsUnique_of_isPushout
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:41:02.290186+00:00
-- url     : https://prove2.me/submissions/f95d9867-7c94-44be-aa54-8c486c1c312d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure

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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.EpsThick
namespace GlobalTheory.EpsThick
theorem _root_.solution {R : Type} [CommRing R] {A A' : CommRingCat.{0}} (s : R →+* A) (p : A ⟶ A')
    (s' : DualNumber R →+* A')
    (H : IsPushout (CommRingCat.ofHom s) (CommRingCat.ofHom (algebraMap R (DualNumber R))) p
      (CommRingCat.ofHom s')) :
    Function.Bijective fun ab : A × A => p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 := by
  let _ : Algebra R A := s.toAlgebra
  let _ : Algebra A A' := p.hom.toAlgebra
  let _ : Algebra (DualNumber R) A' := s'.toAlgebra
  let _ : Algebra R A' := (s'.comp (algebraMap R (DualNumber R))).toAlgebra
  have : IsScalarTower R (DualNumber R) A' := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R A A' := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) H.w).symm
  have h : Algebra.IsPushout R (DualNumber R) A A' := (CommRingCat.isPushout_iff_isPushout.mp H).symm
  let e : DualNumber R ⊗[R] A ≃+ A' := h.out.equiv.toAddEquiv
  have he : ∀ c v, e (c ⊗ₜ v) = s' c * p.hom v :=
    fun c v => (h.out.equiv_tmul c v).trans (Algebra.smul_def _ _)
  have key : ∀ ab : A × A, p.hom ab.1 + s' DualNumber.eps * p.hom ab.2 =
      e ((1 : DualNumber R) ⊗ₜ ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ ab.2) := fun ab => by
    rw [map_add, he, he, map_one, _root_.one_mul]
  simp only [key]
  refine e.bijective.comp (f := fun ab : A × A =>
    ((1 : DualNumber R) ⊗ₜ[R] ab.1 + (DualNumber.eps : DualNumber R) ⊗ₜ[R] ab.2)) ⟨fun x y hxy => ?_, fun t => ?_⟩
  · have h1 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      ((TrivSqZeroExt.fstHom R R R).toLinearMap).rTensor A) hxy
    have h2 := congrArg ((TensorProduct.lid R A).toLinearMap ∘ₗ
      (TrivSqZeroExt.sndHom R R).rTensor A) hxy
    ext
    · simpa using h1
    · simpa using h2
  · induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul c v =>
      refine ⟨(c.fst • v, c.snd • v), ?_⟩
      dsimp only
      rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
      congr 1
      ext <;> simp
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      refine ⟨a + b, ?_⟩
      simp only [Prod.fst_add, Prod.snd_add, TensorProduct.tmul_add]
      abel
end GlobalTheory.EpsThick
