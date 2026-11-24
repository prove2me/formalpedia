-- Prove2me | solution 1 for GlobalTheory.SS.DefectZero.isSmoothAt_of_torsion_free
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:50:17.673158+00:00
-- url     : https://prove2.me/submissions/0b473b85-e01e-4ee1-9340-e40f5133bccc

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
import Theorems.Thm_GlobalTheory_SS_DefectZero_isSmoothAt_iff_injective
import Theorems.Thm_GlobalTheory_SS_DefectZero_isSmoothAt_of_ker
import Theorems.Thm_GlobalTheory_SS_DefectZero_mem_span_of_map_eq_zero
import Theorems.Thm_GlobalTheory_SS_DefectZero_mem_span_of_residue
import Theorems.Thm_GlobalTheory_SS_DefectZero_mem_span_of_tower
import Theorems.Thm_GlobalTheory_SS_DefectZero_exists_mul_mem_span
import Theorems.Thm_GlobalTheory_SS_DefectZero_injective_of_linearIndependent

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
open TensorProduct KaehlerDifferential
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.DefectZero
namespace GlobalTheory.SS.DefectZero
theorem _root_.solution (R A B D : Type) [CommRing R] [IsRegularRing R] [CommRing A]
    [CommRing B] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] [Algebra B D] [Algebra.FiniteType R A]
    [Algebra.FormallySmooth R A] [Module.Free A Ω[A⁄R]]
    (hs : Function.Surjective (algebraMap A B)) (q x : Ideal B) [q.IsPrime] [x.IsPrime]
    (hq : q = RingHom.ker (algebraMap B D))
    (hx : x = (IsLocalRing.maximalIdeal D).comap (algebraMap B D)) [Algebra.IsSmoothAt R q]
    (ht : ∀ w ∈ Submodule.torsion D (D ⊗[B] Ω[B⁄R]), w = 0) : Algebra.IsSmoothAt R x := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  let : Algebra A D := ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B D := .of_algebraMap_eq' rfl
  let k := IsLocalRing.ResidueField D
  let K := FractionRing D
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible D
  let g : RingHom.ker (algebraMap A B) → Ω[A⁄R] := fun h => KaehlerDifferential.D R A h.1
  obtain ⟨I, a, -, hsp, hl⟩ := exists_linearIndependent' k fun h => (1 : k) ⊗ₜ[A] g h
  obtain ⟨ψ, hψ⟩ := mem_span_of_map_eq_zero R A B D hs
  have hD := mem_span_of_residue (k := k) π (hπ.maximalIdeal_eq.ge (Ideal.mem_span_singleton_self π))
    IsLocalRing.residue_surjective
    (fun d hd => Ideal.mem_span_singleton.mp
      (hπ.maximalIdeal_eq.le ((IsLocalRing.residue_eq_zero_iff d).mp hd))) g a
    (fun v hv => hψ.le (ht _ ⟨⟨π, mem_nonZeroDivisors_of_ne_zero hπ.ne_zero⟩,
      (ψ.map_smul π v).symm.trans (hψ.ge hv)⟩))
    (fun i => hsp.ge (Submodule.subset_span ⟨i, rfl⟩))
  have hqK : q = RingHom.ker (algebraMap B K) := by
    rw [hq, IsScalarTower.algebraMap_eq B D K, RingHom.ker_comp_of_injective _
      (IsFractionRing.injective D K)]
  have hi := (isSmoothAt_iff_injective R A B K hs q hqK).mp ‹_›
  have hu := exists_mul_mem_span R A B K I hi a fun h =>
    mem_span_of_tower (D := D) (fun j => g (a j)) (g h) (hD h)
  let J : Ideal A := Ideal.span (Set.range fun j => (a j).1)
  have hJ : ∀ y ∈ J, algebraMap A B y = 0 := fun y hy =>
    (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact (a j).2) :
      J ≤ RingHom.ker (algebraMap A B)) hy
  let φ : (A ⧸ J) →ₐ[R] B := Ideal.Quotient.liftₐ J (IsScalarTower.toAlgHom R A B) hJ
  have hφ : Function.Surjective φ := fun b => by
    obtain ⟨y, rfl⟩ := hs b
    exact ⟨Ideal.Quotient.mk J y, rfl⟩
  let : Algebra (A ⧸ J) k := ((algebraMap B k).comp φ.toRingHom).toAlgebra
  have : IsScalarTower A (A ⧸ J) k := .of_algebraMap_eq' rfl
  have hxk : x.comap φ.toRingHom = RingHom.ker (algebraMap (A ⧸ J) k) := by
    ext y
    rw [hx]
    exact (IsLocalRing.residue_eq_zero_iff _).symm
  have : Algebra.IsSmoothAt R (x.comap φ.toRingHom) :=
    (isSmoothAt_iff_injective R A (A ⧸ J) k Ideal.Quotient.mk_surjective _ hxk).mpr
      (injective_of_linearIndependent R A (A ⧸ J) k I (fun j => (a j).1) Ideal.mk_ker hl)
  have : Algebra.FinitePresentation R (A ⧸ J) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine isSmoothAt_of_ker R (A ⧸ J) B φ hφ x _ rfl (q.comap φ.toRingHom) (Ideal.comap_mono ?_) ?_
  · rw [hq, hx]
    exact Ideal.ker_le_comap _
  · intro c hc
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨u, hu0, hu⟩ := hu ⟨c, hc⟩
    refine ⟨Ideal.Quotient.mk J u, fun h => hu0 ?_, ?_⟩
    · rw [IsScalarTower.algebraMap_apply A B K]
      exact hqK.le h
    · rw [← map_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hu
end GlobalTheory.SS.DefectZero
