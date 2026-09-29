-- Prove2me | solution 1 for ModularCurve.PhiGen.PhiGenDescends.intCoeffs
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/b5b2f85b-7e0c-5ab0-abce-6c675d90775d

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs

noncomputable section

open Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd jNum jNumQ jq ofPowerSeries_coeff_of_neg jq_pow qTwist qTwist_coeff PhiGen.PhiGenDescends coeffEmb coeffEmb_coeff"
p2m_open "ModularCurve"

namespace PhiGen
p2m_export "ModularCurve.PhiGen" "conj conj_zero conj_succ phiProd IntCoeffs PhiGenDescends"
p2m_open "ModularCurve.PhiGen"

section JqIntegrality

private theorem intCoeffs_jq_pow (n : ℕ) : IntCoeffs (jq ^ n) := by
  intro m
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  by_cases hneg : (m - -(n : ℤ)) < 0
  · exact ⟨0, by rw [ofPowerSeries_coeff_of_neg _ hneg, Int.cast_zero]⟩
  · refine ⟨(PowerSeries.coeff (m - -(n : ℤ)).toNat (jNum ^ n) : ℤ), ?_⟩
    have hcast : (m - -(n : ℤ)) = (((m - -(n : ℤ)).toNat : ℕ) : ℤ) :=
      (Int.toNat_of_nonneg (not_lt.mp hneg)).symm
    rw [hcast, HahnSeries.ofPowerSeries_apply_coeff]
    show PowerSeries.coeff _ (jNumQ ^ n) = _
    rw [jNumQ, ← map_pow, PowerSeries.coeff_map]
    rfl

private theorem intCoeffs_jq : IntCoeffs jq := by
  have h := intCoeffs_jq_pow 1
  rwa [pow_one] at h

end JqIntegrality

section IntegralCoeffs

variable {K : Type*} [Field K]

private def CoeffsIntegral (f : LaurentSeries K) : Prop :=
  ∀ m : ℤ, f.coeff m ∈ integralClosure ℤ K

private theorem coeffsIntegral_zero : CoeffsIntegral (0 : LaurentSeries K) := fun _ =>
  Subalgebra.zero_mem _

private theorem coeffsIntegral_one : CoeffsIntegral (1 : LaurentSeries K) := by
  intro m
  rw [HahnSeries.coeff_one]
  split
  · exact Subalgebra.one_mem _
  · exact Subalgebra.zero_mem _

private theorem CoeffsIntegral.neg {f : LaurentSeries K} (hf : CoeffsIntegral f) :
    CoeffsIntegral (-f) := by
  intro m
  rw [HahnSeries.coeff_neg]
  exact Subalgebra.neg_mem _ (hf m)

private theorem CoeffsIntegral.mul {f g : LaurentSeries K} (hf : CoeffsIntegral f)
    (hg : CoeffsIntegral g) : CoeffsIntegral (f * g) := by
  intro m
  rw [HahnSeries.coeff_mul]
  exact Subalgebra.sum_mem _ fun ij _ => Subalgebra.mul_mem _ (hf ij.1) (hg ij.2)

private theorem CoeffsIntegral.qExpand {f : LaurentSeries K} (hf : CoeffsIntegral f)
    (N : ℕ) [NeZero N] : CoeffsIntegral (ModularCurve.qExpand K N f) := by
  intro m
  by_cases hdvd : (N : ℤ) ∣ m
  · obtain ⟨c, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    exact hf c
  · rw [qExpand_coeff_of_not_dvd N f hdvd]
    exact Subalgebra.zero_mem _

private theorem CoeffsIntegral.qTwist {f : LaurentSeries K} (hf : CoeffsIntegral f)
    (u : Kˣ) (hu : ∀ m : ℤ, ((u ^ m : Kˣ) : K) ∈ integralClosure ℤ K) :
    CoeffsIntegral (ModularCurve.qTwist u f) := by
  intro m
  rw [qTwist_coeff]
  exact Subalgebra.mul_mem _ (hu m) (hf m)

private theorem intCast_mem_integralClosure (z : ℤ) : (z : K) ∈ integralClosure ℤ K := by
  rw [mem_integralClosure_iff]
  refine ⟨Polynomial.X - Polynomial.C z, Polynomial.monic_X_sub_C z, ?_⟩
  simp

private theorem val_mem_integralClosure_of_pow_eq_one {u : Kˣ} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) : (u : K) ∈ integralClosure ℤ K := by
  rw [mem_integralClosure_iff]
  refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, ?_⟩
  have hval : (u : K) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  simp [hval]

private theorem zpow_val_mem_integralClosure_of_pow_eq_one {u : Kˣ} {n : ℕ} (hn : n ≠ 0)
    (hu : u ^ n = 1) (m : ℤ) : ((u ^ m : Kˣ) : K) ∈ integralClosure ℤ K := by

  have hrw : u ^ m = u ^ (m % (n : ℤ)).toNat := by
    have h1 : u ^ m = u ^ (m % (n : ℤ)) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv m (n : ℤ)]
      rw [zpow_add, zpow_mul, zpow_natCast, hu, one_zpow, mul_one]
    rw [h1, ← zpow_natCast,
      Int.toNat_of_nonneg (Int.emod_nonneg m (by exact_mod_cast hn))]
  rw [hrw, Units.val_pow_eq_pow_val]
  exact Subalgebra.pow_mem _ (val_mem_integralClosure_of_pow_eq_one hn hu) _

private theorem coeffsIntegral_coeff_X_sub_C {a : LaurentSeries K}
    (ha : CoeffsIntegral a) (k : ℕ) :
    CoeffsIntegral ((Polynomial.X - Polynomial.C a).coeff k) := by
  match k with
  | 0 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
      zero_sub]
    exact CoeffsIntegral.neg ha
  | 1 =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C,
      if_neg (one_ne_zero), sub_zero]
    exact coeffsIntegral_one
  | (k + 2) =>
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    rw [if_neg (by omega), if_neg (by omega), sub_zero]
    exact coeffsIntegral_zero

private theorem coeffsIntegral_coeff_mul {p q : Polynomial (LaurentSeries K)}
    (hp : ∀ k, CoeffsIntegral (p.coeff k)) (hq : ∀ k, CoeffsIntegral (q.coeff k))
    (k : ℕ) : CoeffsIntegral ((p * q).coeff k) := by
  rw [Polynomial.coeff_mul]
  intro a
  rw [HahnSeries.coeff_sum]
  exact Subalgebra.sum_mem _ fun ij _ => CoeffsIntegral.mul (hp ij.1) (hq ij.2) a

private theorem coeffsIntegral_coeff_prod {ι : Type*} (s : Finset ι)
    (p : ι → Polynomial (LaurentSeries K))
    (hp : ∀ i ∈ s, ∀ k, CoeffsIntegral ((p i).coeff k)) :
    ∀ k, CoeffsIntegral ((∏ i ∈ s, p i).coeff k) := by
  induction s using Finset.cons_induction with
  | empty =>
    intro k
    simp only [Finset.prod_empty]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using coeffsIntegral_one
    · rw [Polynomial.coeff_one, if_neg (by omega)]
      exact coeffsIntegral_zero
  | cons a s _ha ih =>
    intro k
    rw [Finset.prod_cons]
    exact coeffsIntegral_coeff_mul (hp a (Finset.mem_cons_self a s))
      (ih fun i hi k => hp i (Finset.mem_cons_of_mem hi) k) k

end IntegralCoeffs

section ConjIntegral

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem coeffsIntegral_jqK : CoeffsIntegral (coeffEmb K jq) := by
  intro m
  obtain ⟨z, hz⟩ := intCoeffs_jq m
  rw [coeffEmb_coeff, hz, map_intCast]
  exact intCast_mem_integralClosure z

variable (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ)

private theorem coeffsIntegral_conj (hζ1 : ζ ^ ℓ = 1) (i : Fin (ℓ + 1)) :
    CoeffsIntegral (conj ℓ ζ i) := by
  induction i using Fin.cases with
  | zero =>
    rw [conj_zero]
    exact CoeffsIntegral.qExpand coeffsIntegral_jqK (ℓ * ℓ)
  | succ b =>
    rw [conj_succ]
    refine CoeffsIntegral.qTwist coeffsIntegral_jqK _ fun m => ?_
    refine zpow_val_mem_integralClosure_of_pow_eq_one hℓ.out.ne_zero ?_ m
    rw [← pow_mul, mul_comm (b : ℕ) ℓ, pow_mul, hζ1, one_pow]

variable {ℓ ζ}

private theorem coeffsIntegral_phiProd_coeff (hζ1 : ζ ^ ℓ = 1) (k : ℕ) :
    CoeffsIntegral ((phiProd ℓ (conj ℓ ζ)).coeff k) := by
  rw [phiProd]
  exact coeffsIntegral_coeff_prod Finset.univ _
    (fun i _ k => coeffsIntegral_coeff_X_sub_C (coeffsIntegral_conj ℓ ζ hζ1 i) k) k

end ConjIntegral

section IntegralityDescent

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem exists_intCast_eq_of_mem {q : ℚ}
    (h : algebraMap ℚ K q ∈ integralClosure ℤ K) : ∃ z : ℤ, q = (z : ℚ) := by
  rw [mem_integralClosure_iff] at h
  obtain ⟨P, hPmonic, hPeval⟩ := h

  have hcomp : algebraMap ℤ K = (algebraMap ℚ K).comp (Int.castRingHom ℚ) :=
    Subsingleton.elim _ _
  rw [hcomp, ← Polynomial.hom_eval₂] at hPeval

  have h0 : Polynomial.eval₂ (Int.castRingHom ℚ) q P = 0 :=
    FaithfulSMul.algebraMap_injective ℚ K (by rw [hPeval, map_zero])

  have hint : IsIntegral ℤ q :=
    ⟨P, hPmonic, by
      rwa [show algebraMap ℤ ℚ = Int.castRingHom ℚ from Subsingleton.elim _ _]⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨z, by rw [← hz]; simp⟩

variable {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}

private theorem PhiGenDescends.intCoeffs (hc : PhiGenDescends ℓ ζ c) (hζ1 : ζ ^ ℓ = 1) (k : ℕ) :
    IntCoeffs (c k) := by
  intro m

  have h1 : algebraMap ℚ K ((c k).coeff m)
      = ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m) := by
    rw [hc k, coeffEmb_coeff, qExpand_coeff_mul]
  have h2 := coeffsIntegral_phiProd_coeff hζ1 k ((ℓ : ℤ) * m)
  rw [← h1] at h2
  exact exists_intCast_eq_of_mem h2

end IntegralityDescent

end PhiGen

end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.ModularCurve _root_.ModularCurve.PhiGen _root_.P2MW.S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.ModularCurve.PhiGen in

theorem solution {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (hζ1 : ζ ^ ℓ = 1) (k : ℕ) : IntCoeffs (c k) :=
  ModularCurve.PhiGen.PhiGenDescends.intCoeffs hc hζ1 k

#print axioms solution

end S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs
end P2MW
export P2MW.S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs (solution)
