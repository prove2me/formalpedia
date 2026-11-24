-- Prove2me | solution 1 for GlobalTheory.SmallPoint.exists_extend_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:05:29.021811+00:00
-- url     : https://prove2.me/submissions/199deddb-0c09-4cca-ab1d-1e25e9265d9c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit
import Theorems.Thm_GlobalTheory_SmallPoint_exists_extend_of_ker_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open GlobalTheory
open GlobalTheory.SmallPoint
namespace GlobalTheory.SmallPoint
theorem _root_.solution {R B Ω : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Algebra.IsIntegral R B] [FaithfulSMul R B]
    [Field Ω] [IsAlgClosed Ω] (ψ : R →+* Ω) (u : B) (t : Ω)
    (ht : (minpoly R u).eval₂ ψ t = 0) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap R B) = ψ ∧ φ u = t := by
  letI : Algebra R[X] B := (aeval u : R[X] →ₐ[R] B).toRingHom.toAlgebra
  haveI : IsScalarTower R R[X] B :=
    IsScalarTower.of_algebraMap_eq fun x => ((aeval u : R[X] →ₐ[R] B).commutes x).symm
  haveI : Algebra.IsIntegral R[X] B := Algebra.IsIntegral.tower_top (R := R)
  obtain ⟨φ, hφ⟩ := exists_extend_of_ker_le (B := B) (eval₂RingHom ψ t) (fun f hf => by
    obtain ⟨g, rfl⟩ := minpoly.isIntegrallyClosed_dvd
      (Algebra.IsIntegral.isIntegral (R := R) u) (p := f) hf
    rw [RingHom.mem_ker, map_mul, coe_eval₂RingHom, ht, zero_mul])
  have h : ∀ f : R[X], φ (aeval u f) = f.eval₂ ψ t := fun f => DFunLike.congr_fun hφ f
  refine ⟨φ, RingHom.ext fun r => ?_, ?_⟩
  · simpa using h (C r)
  · simpa using h X
end GlobalTheory.SmallPoint
