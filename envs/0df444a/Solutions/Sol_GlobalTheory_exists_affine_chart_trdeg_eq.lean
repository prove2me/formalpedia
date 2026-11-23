-- Prove2me | solution 1 for GlobalTheory.exists_affine_chart_trdeg_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:36.124471+00:00
-- url     : https://prove2.me/submissions/47f4d2e1-18a7-4ce6-8201-48207228155a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing
open GlobalTheory
universe u
open AlgebraicGeometry CategoryTheory Topology
variable {O : Type u} [CommRing O] [IsDomain O]
  {Y : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Spec (.of O)) [LocallyOfFiniteType f] [Flat f]
namespace GlobalTheory
theorem _root_.solution (x : Y) :
    letI := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
    ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : Algebra O A)
      (_ : Algebra.FiniteType O A) (_ : FaithfulSMul O A) (j : Spec (.of A) ⟶ Y)
      (_ : IsOpenImmersion j), x ∈ Set.range j ∧
      j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O A)) ∧
      Algebra.trdeg O A = Algebra.trdeg O Y.functionField := by
  let := (Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f)).hom.toAlgebra
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let φ := Spec.preimage (hU.fromSpec ≫ f)
  have hφ : Spec.map φ = hU.fromSpec ≫ f := Spec.map_preimage _
  let : Algebra O Γ(Y, U) := φ.hom.toAlgebra
  have hft : Algebra.FiniteType O Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  have hfl : Module.Flat O Γ(Y, U) :=
    (HasRingHomProperty.Spec_iff (P := @Flat) (φ := φ)).mp (hφ ▸ inferInstance)
  have hη : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hcomp : φ ≫ Y.presheaf.germ U _ hη = Spec.preimage (Y.fromSpecStalk (genericPoint Y) ≫ f) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, Spec.map_preimage, ← hU.fromSpecStalk_eq_fromSpecStalk hη,
      IsAffineOpen.fromSpecStalk, Category.assoc]
  have : IsScalarTower O Γ(Y, U) Y.functionField :=
    IsScalarTower.of_algebraMap_eq fun a ↦ congr($(hcomp).hom a).symm
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  have : Algebra.IsAlgebraic Γ(Y, U) Y.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors _)
  refine ⟨Γ(Y, U), inferInstance, inferInstance, inferInstance, hft, inferInstance, hU.fromSpec,
    inferInstance, ?_, hφ.symm, (trdeg_eq_of_isAlgebraic_top O Γ(Y, U) Y.functionField).symm⟩
  rw [hU.range_fromSpec]
  exact hxU
end GlobalTheory
