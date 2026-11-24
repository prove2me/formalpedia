-- Prove2me | solution 1 for GlobalTheory.FibreMinimalPrime.trdeg_residueField_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:48.173518+00:00
-- url     : https://prove2.me/submissions/5eff3aa8-9a51-482b-9bd1-9195bf47fe50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TrdegResidueFieldEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.FibreMinimalPrime
namespace GlobalTheory.FibreMinimalPrime
theorem _root_.solution {R : Type} [CommRing R] (r : ℕ) (Q : Ideal (MvPolynomial (Fin r) R)) [Q.IsPrime]
    (hmin : ∀ Q' : Ideal (MvPolynomial (Fin r) R), Q'.IsPrime → Q' ≤ Q →
      Q'.comap (MvPolynomial.C : R →+* _) = Q.comap MvPolynomial.C → Q' = Q) :
    @Algebra.trdeg (Q.comap (MvPolynomial.C : R →+* _)).ResidueField Q.ResidueField _ _
      (Ideal.ResidueField.map (Q.comap MvPolynomial.C) Q MvPolynomial.C rfl).toAlgebra = r := by
  classical
  set q : Ideal R := Q.comap (MvPolynomial.C : R →+* _) with hq_def
  let f : MvPolynomial (Fin r) R →+* MvPolynomial (Fin r) (R ⧸ q) := MvPolynomial.map (Ideal.Quotient.mk q)
  have hfs : Function.Surjective f := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective

  have hker_prime : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hker_le : RingHom.ker f ≤ Q := by
    show RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk q)) ≤ Q
    rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_le_iff_le_comap]
  have hker_comap : (RingHom.ker f).comap (MvPolynomial.C : R →+* _) = q := by
    ext a
    simp only [Ideal.mem_comap, RingHom.mem_ker, f, MvPolynomial.map_C, MvPolynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem]

  have hQ : Q = RingHom.ker f := (hmin _ hker_prime hker_le hker_comap).symm

  letI algKL : Algebra q.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.map q Q MvPolynomial.C rfl).toAlgebra
  letI algkL : Algebra (R ⧸ q) Q.ResidueField :=
    ((algebraMap q.ResidueField Q.ResidueField).comp (algebraMap (R ⧸ q) q.ResidueField)).toAlgebra
  haveI : IsScalarTower (R ⧸ q) q.ResidueField Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI algkB : Algebra (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) :=
    (Ideal.quotientMap Q (MvPolynomial.C : R →+* _) le_rfl).toAlgebra
  haveI : IsScalarTower (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    show Ideal.ResidueField.map q Q MvPolynomial.C rfl
        (algebraMap (R ⧸ q) q.ResidueField (Ideal.Quotient.mk q a)) =
      algebraMap (MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField
        (Ideal.quotientMap Q (MvPolynomial.C : R →+* _) le_rfl (Ideal.Quotient.mk q a))
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.ResidueField.map_algebraMap,
      Ideal.quotientMap_mk, Ideal.algebraMap_quotient_residueField_mk]
  haveI : FaithfulSMul (R ⧸ q) q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  haveI : FaithfulSMul q.ResidueField Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap q.ResidueField Q.ResidueField).injective
  haveI : FaithfulSMul (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Ideal.quotientMap_injective
  haveI : FaithfulSMul (MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)

  let e0 : (MvPolynomial (Fin r) R ⧸ Q) ≃+* MvPolynomial (Fin r) (R ⧸ q) :=
    (Ideal.quotEquivOfEq hQ).trans (RingHom.quotientKerEquivOfSurjective hfs)
  let e : (MvPolynomial (Fin r) R ⧸ Q) ≃ₐ[R ⧸ q] MvPolynomial (Fin r) (R ⧸ q) :=
    AlgEquiv.ofRingEquiv (f := e0) (fun x => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      show e0 (Ideal.quotientMap Q (MvPolynomial.C : R →+* _) le_rfl (Ideal.Quotient.mk q a)) =
        MvPolynomial.C (Ideal.Quotient.mk q a)
      rw [Ideal.quotientMap_mk]
      simp only [e0, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
        RingHom.quotientKerEquivOfSurjective_apply_mk, f, MvPolynomial.map_C])
  have hB : Algebra.trdeg (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) = r := by
    rw [e.trdeg_eq, MvPolynomial.trdeg_of_isDomain]
    simp
  have h0K : Algebra.trdeg (R ⧸ q) q.ResidueField = 0 := by
    haveI := IsLocalization.isAlgebraic (R := R ⧸ q) q.ResidueField (nonZeroDivisors (R ⧸ q))
    exact trdeg_eq_zero
  have h0L : Algebra.trdeg (MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField = 0 := by
    haveI := IsLocalization.isAlgebraic (R := MvPolynomial (Fin r) R ⧸ Q) Q.ResidueField
      (nonZeroDivisors _)
    exact trdeg_eq_zero
  have h1 := trdeg_add_eq (R ⧸ q) q.ResidueField (A := Q.ResidueField)
  have h2 := trdeg_add_eq (R ⧸ q) (MvPolynomial (Fin r) R ⧸ Q) (A := Q.ResidueField)
  rw [h0K, zero_add] at h1
  rw [hB, h0L, add_zero] at h2
  exact h1.trans h2.symm
end GlobalTheory.FibreMinimalPrime
