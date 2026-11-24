-- Prove2me | solution 1 for GlobalTheory.SmallPoint.exists_extend_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:21.88629+00:00
-- url     : https://prove2.me/submissions/00d4c30d-8497-4feb-b920-cf7b9dbade76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit

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
theorem _root_.solution {R B Ω : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.IsIntegral R B] [Field Ω] [IsAlgClosed Ω]
    (φ : R →+* Ω) (h : RingHom.ker (algebraMap R B) ≤ RingHom.ker φ) :
    ∃ ψ : B →+* Ω, ψ.comp (algebraMap R B) = φ := by
  haveI := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
    (RingHom.ker φ) ⊥ h
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (R ⧸ RingHom.ker φ) Ω := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (R ⧸ RingHom.ker φ) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.kerLift_injective φ)
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) Ω := FaithfulSMul.to_isTorsionFree _ _
  haveI : Module.IsTorsionFree (R ⧸ RingHom.ker φ) (B ⧸ Q) := FaithfulSMul.to_isTorsionFree _ _
  haveI : Algebra.IsIntegral (R ⧸ RingHom.ker φ) (B ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := R)
  haveI : Algebra.IsAlgebraic (R ⧸ RingHom.ker φ) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let σ : (B ⧸ Q) →ₐ[R ⧸ RingHom.ker φ] Ω := IsAlgClosed.lift
  refine ⟨σ.toRingHom.comp (Ideal.Quotient.mk Q), RingHom.ext fun r => ?_⟩
  exact (σ.commutes (Ideal.Quotient.mk _ r)).trans (RingHom.kerLift_mk φ r)
end GlobalTheory.SmallPoint
