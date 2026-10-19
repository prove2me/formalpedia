-- Prove2me | solution 1 for OAI.CirculantHadamard.LocalComparison.comparison_induction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:12:27.786439+00:00
-- url     : https://prove2.me/submissions/48970c30-172c-4fc5-85f8-23bed3907440

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal

open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalComparison
universe uA uS
open CyclicRing
variable {A : Type uA} {S : Type uS} [CommRing A] [IsDomain A]
  [CommRing S] [domainS : IsDomain S] [IsLocalRing S]
theorem cb_aux {A S : Type*} [CommRing A] [CommRing S] [IsLocalRing S] (n : ℕ) (φ : A →+* S)
    (v : Elem A n →+* S)
    (vres : ∀ F : Elem A n,
      IsLocalRing.residue S (v F) =
        IsLocalRing.residue S (φ (augmentation n F)))
    (F K : Elem A n) (hprod : v F * v K = φ (augmentation n F) * φ (augmentation n K))
    (hunit : IsUnit (augmentation n F)) :
    ResidueOneAssociated (IsLocalRing.residue S) (v F) (φ (augmentation n F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v K) (φ (augmentation n K)) := by
  obtain ⟨w, hw⟩ := hunit.map φ
  have hres_w : IsLocalRing.residue S (w : S) ≠ 0 := by
    rw [hw]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (hunit.map φ)
  have hvF : IsUnit (v F) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, vres, ← hw]; exact hres_w
  obtain ⟨z, hz⟩ := hvF
  have hres : IsLocalRing.residue S (z : S) = IsLocalRing.residue S (w : S) := by
    rw [hz, hw, vres]
  have hwne : IsLocalRing.residue S (w : S) * IsLocalRing.residue S ((w⁻¹ : Sˣ) : S) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hzne : IsLocalRing.residue S (z : S) * IsLocalRing.residue S ((z⁻¹ : Sˣ) : S) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine ⟨⟨z * w⁻¹, ?_, ?_⟩, ⟨w * z⁻¹, ?_, ?_⟩⟩
  · rw [← hz, ← hw, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  · rw [Units.val_mul, map_mul, hres, hwne]
  · have : (v K) = ((z⁻¹ : Sˣ) : S) * (v F * v K) := by
      rw [← hz, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this, hprod, ← hw, Units.val_mul]; ring
  · rw [Units.val_mul, map_mul, ← hres, hzne]

theorem aux_base {A S : Type*} [CommRing A] [IsDomain A] [CommRing S] [IsLocalRing S]
    (n p : ℕ) (φ : A →+* S) (hp : Prime (p : A))
    (hpS : φ (p : A) ≠ 0)
    (v : Elem A n →+* S)
    (vscalar : ∀ a : A, v (scalar n a) = φ a)
    (vres : ∀ F : Elem A n,
      IsLocalRing.residue S (v F) =
        IsLocalRing.residue S (φ (augmentation n F)))
    (b : Aˣ) (F K : Elem A n)
    (hFK : F * K = scalar n ((p : A) * (b : A))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v F) (φ (augmentation n F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v K) (φ (augmentation n K)) := by
  have hprod : v F * v K = φ (augmentation n F) * φ (augmentation n K) := by
    rw [← map_mul, ← map_mul, ← map_mul, hFK, vscalar, augmentation_scalar]
  have hprodA : augmentation n F * augmentation n K = (p : A) * (b : A) := by
    rw [← map_mul, hFK, augmentation_scalar]
  rcases (show IsUnit (augmentation n F) ∨ IsUnit (augmentation n K) from by
      have hd : (p : A) ∣ augmentation n F * augmentation n K := ⟨b, hprodA⟩
      rcases hp.dvd_or_dvd hd with ⟨x', hx'⟩ | ⟨y', hy'⟩
      · right
        have : (p : A) * (x' * augmentation n K) = (p : A) * b := by rw [← hprodA, hx']; ring
        have h2 := mul_left_cancel₀ hp.ne_zero this
        exact IsUnit.of_mul_eq_one (x' * ↑b⁻¹) (by rw [← mul_assoc, mul_comm _ x', h2, Units.mul_inv])
      · left
        have : (p : A) * (augmentation n F * y') = (p : A) * b := by rw [← hprodA, hy']; ring
        have h2 := mul_left_cancel₀ hp.ne_zero this
        exact IsUnit.of_mul_eq_one (y' * ↑b⁻¹) (by rw [← mul_assoc, h2, Units.mul_inv])) with h | h
  · exact cb_aux n φ v vres F K hprod h
  · have := cb_aux n φ v vres K F (by rw [mul_comm, hprod, mul_comm]) h
    exact ⟨this.2, this.1⟩

theorem aux_step {A S : Type*} [CommRing A] [IsDomain A] [CommRing S] [IsLocalRing S]
    (p e : ℕ) (φ : A →+* S)
    (hp : (p : A) ≠ 0)
    (v : Elem A (p ^ (e + 1)) →+* S)
    (v' : Elem A (p ^ (e + 2)) →+* S)
    (vscalar : ∀ a : A, v (scalar (p ^ (e + 1)) a) = φ a)
    (vq : ∀ F : Elem A (p ^ (e + 2)),
      v (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v' F)
    (b : Aˣ) (F K : Elem A (p ^ (e + 2)))
    (hFK : F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)))
    (F' : Elem A (p ^ (e + 1)))
    (hF : cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
      scalar (p ^ (e + 1)) (p : A) * F')
    (ih : ∀ U V : Elem A (p ^ (e + 1)),
      U * V = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
        ResidueOneAssociated (IsLocalRing.residue S) (v U)
          (φ (augmentation (p ^ (e + 1)) U)) ∧
        ResidueOneAssociated (IsLocalRing.residue S) (v V)
          (φ (augmentation (p ^ (e + 1)) V))) :
    ResidueOneAssociated (IsLocalRing.residue S) (v' F)
      (φ (augmentation (p ^ (e + 2)) F)) ∧
    ResidueOneAssociated (IsLocalRing.residue S) (v' K)
      (φ (augmentation (p ^ (e + 2)) K)) := by
  set π := cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1)))
  have hcancel : ∀ X Y : Elem A (p ^ (e + 1)),
      scalar (p ^ (e + 1)) (p : A) * X = scalar (p ^ (e + 1)) (p : A) * Y → X = Y := by
    intro X Y h
    apply AddMonoidAlgebra.coeff_injective
    ext a
    have := congrArg (fun Z => AddMonoidAlgebra.coeff Z a) h
    simp only [scalar, AddMonoidAlgebra.coeff_single_zero_mul] at this
    exact mul_left_cancel₀ hp this
  have hGH : π F * π K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 2) * (b : A)) := by
    rw [← map_mul, hFK, cyclicProjection_scalar]
  have hF'H : F' * π K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) := by
    apply hcancel
    rw [← mul_assoc, ← hF, hGH]
    simp only [scalar, AddMonoidAlgebra.single_mul_single, add_zero]
    congr 1; ring
  obtain ⟨⟨u, hu1, hu2⟩, hK⟩ := ih F' (π K) hF'H
  refine ⟨⟨u, ?_, hu2⟩, ?_⟩
  · rw [← vq, hF, map_mul, vscalar, hu1, ← augmentation_cyclicProjection
      (pow_dvd_pow p (Nat.le_succ (e + 1))) F, hF, map_mul, augmentation_scalar, map_mul]
    ring
  · rw [← vq, ← augmentation_cyclicProjection (pow_dvd_pow p (Nat.le_succ (e + 1))) K]
    exact hK


theorem solution (p : ℕ) (φ : A →+* S)
    (hp : Prime (p : A)) (hpS : φ (p : A) ≠ 0)
    (v : (e : ℕ) → Elem A (p ^ (e + 1)) →+* S)
    (vscalar : ∀ e a, v e (scalar (p ^ (e + 1)) a) = φ a)
    (vres : ∀ F : Elem A (p ^ 1),
      IsLocalRing.residue S (v 0 F) =
        IsLocalRing.residue S (φ (augmentation (p ^ 1) F)))
    (vq : ∀ e F,
      v e (cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F) = v (e + 1) F)
    (hdivide : ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 2))),
      F * K = scalar (p ^ (e + 2)) ((p : A) ^ (e + 2) * (b : A)) →
      (∃ F', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) F =
        scalar (p ^ (e + 1)) (p : A) * F') ∨
      (∃ K', cyclicProjection A (pow_dvd_pow p (Nat.le_succ (e + 1))) K =
        scalar (p ^ (e + 1)) (p : A) * K')) :
    ∀ e (b : Aˣ) (F K : Elem A (p ^ (e + 1))),
      F * K = scalar (p ^ (e + 1)) ((p : A) ^ (e + 1) * (b : A)) →
      ResidueOneAssociated (IsLocalRing.residue S) (v e F)
        (φ (augmentation (p ^ (e + 1)) F)) ∧
      ResidueOneAssociated (IsLocalRing.residue S) (v e K)
        (φ (augmentation (p ^ (e + 1)) K)) := by
  intro e
  induction e with
  | zero =>
    intro b F K hFK
    have hFK' : F * K = scalar (p ^ 1) ((p : A) * (b : A)) := by rw [hFK]; simp
    exact aux_base (p ^ 1) p φ hp hpS (v 0) (vscalar 0) vres b F K hFK'
  | succ e ih =>
    intro b F K hFK
    rcases hdivide e b F K hFK with ⟨F', hF'⟩ | ⟨K', hK'⟩
    · exact aux_step p e φ hp.ne_zero (v e) (v (e + 1)) (vscalar e) (vq e) b F K hFK F' hF' (ih b)
    · have := aux_step p e φ hp.ne_zero (v e) (v (e + 1)) (vscalar e) (vq e) b K F
        (by rw [mul_comm]; exact hFK) K' hK' (ih b)
      exact ⟨this.2, this.1⟩
