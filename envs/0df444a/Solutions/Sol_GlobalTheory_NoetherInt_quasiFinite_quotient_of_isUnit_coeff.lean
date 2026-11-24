-- Prove2me | solution 1 for GlobalTheory.NoetherInt.quasiFinite_quotient_of_isUnit_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:13:27.75586+00:00
-- url     : https://prove2.me/submissions/9d0f7470-61e7-4a9b-ad13-39a0f2e86f11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open Polynomial
namespace GlobalTheory.NoetherInt
theorem _root_.solution {R : Type*} [CommRing R] (G : R[X]) (k : ℕ)
    (hc : IsUnit (G.coeff k)) : Algebra.QuasiFinite R (R[X] ⧸ Ideal.span {G}) := by
  refine ⟨fun P _ => ?_⟩
  let f : R[X] →ₐ[R] (R[X] ⧸ Ideal.span {G}) := Ideal.Quotient.mkₐ R _
  have hf : Function.Surjective f := Ideal.Quotient.mkₐ_surjective R _
  let e := Polynomial.fiberEquivQuotient f hf P
  let I : Ideal (P.ResidueField[X]) :=
    (RingHom.ker (f : R[X] →+* (R[X] ⧸ Ideal.span {G}))).map (mapRingHom (algebraMap R P.ResidueField))
  let Gb : P.ResidueField[X] := G.map (algebraMap R P.ResidueField)
  have hG : Gb ≠ 0 := by
    intro h
    have h2 : (Gb).coeff k = 0 := by rw [h]; simp
    rw [coeff_map] at h2
    exact (hc.map (algebraMap R P.ResidueField)).ne_zero h2
  have hmem : Gb ∈ I := by
    refine Ideal.mem_map_of_mem (mapRingHom (algebraMap R P.ResidueField)) (x := G) ?_
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self G)
  have hM : (Gb * C Gb.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hG
  have hMI : Gb * C Gb.leadingCoeff⁻¹ ∈ I := I.mul_mem_right _ hmem
  have h1 : Module.Finite P.ResidueField
      (P.ResidueField[X] ⧸ Ideal.span {Gb * C Gb.leadingCoeff⁻¹}) := hM.finite_quotient
  have hle : Ideal.span {Gb * C Gb.leadingCoeff⁻¹} ≤ I := by
    rw [Ideal.span_singleton_le_iff_mem]; exact hMI
  have h2 : Module.Finite P.ResidueField (P.ResidueField[X] ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ P.ResidueField hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
end GlobalTheory.NoetherInt
