-- Prove2me | solution 1 for GlobalTheory.SS.DefectZero.exists_mul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:15.777913+00:00
-- url     : https://prove2.me/submissions/4ba58ad0-fc3b-4511-ac7d-15924f8fd9f5

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_MaximalIdealSquares_RingKrullDimQuotientSpanSingletonAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSmoothOfDefectZero
import Theorems.Thm_GlobalTheory_SS_DefectZero_exists_smul_eq_zero

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
theorem _root_.solution (R A B K I : Type) [CommRing R] [CommRing A] [CommRing B] [Field K]
    [Algebra R A] [Algebra A B] [Algebra B K] [Algebra A K] [IsScalarTower A B K]
    [IsNoetherianRing A] (hi : Function.Injective (cotangentComplexBaseChange R B A K))
    (f : I → RingHom.ker (algebraMap A B))
    (hf : ∀ h : RingHom.ker (algebraMap A B), (1 : K) ⊗ₜ[A] KaehlerDifferential.D R A h.1 ∈
      Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[A] KaehlerDifferential.D R A (f j).1))
    (h : RingHom.ker (algebraMap A B)) :
    ∃ u : A, algebraMap A K u ≠ 0 ∧ u * h.1 ∈ Ideal.span (Set.range fun j => (f j).1) := by
  let N := Submodule.span A (Set.range f)
  have h1 : ∀ h : RingHom.ker (algebraMap A B),
      (1 : K) ⊗ₜ[A] h ∈ Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[A] f j) := by
    intro h
    rw [← Submodule.apply_mem_span_image_iff_mem_span hi, ← Set.range_comp]
    simpa [Function.comp_def, cotangentComplexBaseChange_tmul] using hf h
  have h2 : ∀ h, (1 : K) ⊗ₜ[A] N.mkQ h = 0 := by
    intro h
    have h3 : Submodule.span K (Set.range fun j => (1 : K) ⊗ₜ[A] f j) ≤
        LinearMap.ker (N.mkQ.baseChange K) := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have : N.mkQ (f j) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr (Submodule.subset_span ⟨j, rfl⟩)
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.baseChange_tmul, this, tmul_zero]
    exact h3 (h1 h)
  have : Subsingleton (K ⊗[A] (RingHom.ker (algebraMap A B) ⧸ N)) := by
    refine subsingleton_of_forall_eq 0 fun v => ?_
    induction v with
    | zero => rfl
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul d m =>
      obtain ⟨m, rfl⟩ := N.mkQ_surjective m
      rw [← mul_one d, ← smul_eq_mul, ← smul_tmul', h2, smul_zero]
  obtain ⟨u, hu, hm⟩ := exists_smul_eq_zero A K _ (N.mkQ h)
  refine ⟨u, hu, ?_⟩
  rw [← map_smul] at hm
  have h4 := Submodule.mem_map_of_mem (f := (RingHom.ker (algebraMap A B)).subtype)
    ((Submodule.Quotient.mk_eq_zero N).mp hm)
  rw [Submodule.map_span, ← Set.range_comp] at h4
  exact h4
end GlobalTheory.SS.DefectZero
