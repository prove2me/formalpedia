-- Prove2me | solution 1 for ModularCurve.transcendental_lambdaModC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/ee85b6d6-f9c9-5670-873b-e78bb87679d9

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_transcendental_lambdaModC

set_option autoImplicit false

p2m_open "HahnSeries Polynomial ModularCurve P2MW.S_ModularCurve_transcendental_lambdaModC.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "lambdaInt lambdaModC qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd etaProd constantCoeff_etaProd dedekindEtaUnitInv laurentMap laurentMap_coeff laurentMap_single"
namespace TrLambda
p2m_open "ModularCurve"

def IsOneUnit {R : Type*} [CommRing R] (x : LaurentSeries R) : Prop := x.coeff 0 = 1 ∧ ∀ n < 0, x.coeff n = 0

namespace IsOneUnit

variable {R : Type*} [CommRing R]

theorem ofPowerSeries (P : PowerSeries R) (hP : PowerSeries.constantCoeff P = 1) :
    IsOneUnit (HahnSeries.ofPowerSeries ℤ R P) := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [PowerSeries.coeff_coe, if_neg (by omega)]; simpa using hP
  · rw [PowerSeries.coeff_coe, if_pos hn]

theorem mul {x y : LaurentSeries R} (hx : IsOneUnit x) (hy : IsOneUnit y) : IsOneUnit (x * y) := by
  refine ⟨?_, fun n hn => ?_⟩
  · rw [HahnSeries.coeff_mul, Finset.sum_eq_single ((0, 0) : ℤ × ℤ)]
    · rw [hx.1, hy.1, mul_one]
    · intro ij hij hne
      rw [Finset.mem_antidiagonal] at hij
      obtain ⟨h1, h2, h3⟩ := hij
      have hi : 0 ≤ ij.1 := by
        by_contra h; rw [not_le] at h; exact (HahnSeries.mem_support _ _).mp h1 (hx.2 _ h)
      have hj : 0 ≤ ij.2 := by
        by_contra h; rw [not_le] at h; exact (HahnSeries.mem_support _ _).mp h2 (hy.2 _ h)
      exfalso; apply hne
      exact Prod.ext (by omega) (by omega)
    · intro h
      rw [Finset.mem_antidiagonal, not_and_or, not_and_or] at h
      rcases h with h | h | h
      · rw [HahnSeries.mem_support, not_not] at h; rw [h, zero_mul]
      · rw [HahnSeries.mem_support, not_not] at h; rw [h, mul_zero]
      · exact absurd (by simp) h
  · rw [HahnSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ij hij
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    exfalso
    by_cases hi : ij.1 < 0
    · exact (HahnSeries.mem_support _ _).mp h1 (hx.2 _ hi)
    · exact (HahnSeries.mem_support _ _).mp h2 (hy.2 _ (by omega))

theorem pow {x : LaurentSeries R} (hx : IsOneUnit x) (n : ℕ) : IsOneUnit (x ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact ⟨by simp, fun n hn => by rw [HahnSeries.coeff_one, if_neg hn.ne]⟩
  | succ n ih => rw [pow_succ]; exact ih.mul hx

theorem qExpand {x : LaurentSeries R} (hx : IsOneUnit x) (N : ℕ) [NeZero N] : IsOneUnit (ModularCurve.qExpand R N x) := by
  refine ⟨?_, fun n hn => ?_⟩
  · have h := qExpand_coeff_mul (R := R) N x 0
    rw [mul_zero] at h
    rw [h, hx.1]
  · by_cases hd : (N : ℤ) ∣ n
    · obtain ⟨c, rfl⟩ := hd
      rw [qExpand_coeff_mul]
      have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      exact hx.2 c (by nlinarith)
    · exact qExpand_coeff_of_not_dvd N x hd

end IsOneUnit

theorem lambdaInt_eq : lambdaInt = HahnSeries.single (1 : ℤ) (1 : ℤ) *
    (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) := by
  rw [lambdaInt]; ring

theorem isOneUnit_lambdaInt_tail : IsOneUnit
    (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 * ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)) := by
  have hE : IsOneUnit (HahnSeries.ofPowerSeries ℤ ℤ etaProd) := IsOneUnit.ofPowerSeries _ constantCoeff_etaProd
  have hD : IsOneUnit (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) := by
    refine IsOneUnit.ofPowerSeries _ ?_
    rw [dedekindEtaUnitInv, PowerSeries.constantCoeff_invOfUnit, inv_one, Units.val_one]
  exact ((hE.pow 8).mul ((hE.pow 16).qExpand 4)).mul (hD.qExpand 2)

theorem IsOneUnit.laurentMap' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {x : LaurentSeries R} (hx : IsOneUnit x) :
    IsOneUnit (laurentMap φ x) :=
  ⟨by rw [laurentMap_coeff, hx.1, map_one], fun n hn => by rw [laurentMap_coeff, hx.2 n hn, map_zero]⟩

variable (K : Type*) [CommRing K]

theorem single_pow (n : ℕ) : (single (1 : ℤ) (1 : K)) ^ n = single (n : ℤ) 1 := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero]; rfl
  | succ n ih => rw [pow_succ, ih, HahnSeries.single_mul_single, mul_one, Nat.cast_succ]

theorem lambdaModC_eq : ∃ U : LaurentSeries K, IsOneUnit U ∧ lambdaModC K = single (1 : ℤ) (1 : K) * U := by
  refine ⟨laurentMap (Int.castRingHom K) (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 *
      ModularCurve.qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
      ModularCurve.qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)),
    isOneUnit_lambdaInt_tail.laurentMap' _, ?_⟩
  rw [lambdaModC, lambdaInt_eq, map_mul, laurentMap_single, map_one]

theorem coeff_lambdaModC_pow (i : ℕ) :
    ((lambdaModC K) ^ i).coeff (i : ℤ) = 1 ∧ ∀ n : ℤ, n < i → ((lambdaModC K) ^ i).coeff n = 0 := by
  obtain ⟨U, hU, hμ⟩ := lambdaModC_eq K
  have hUi := hU.pow i
  rw [hμ, mul_pow, single_pow]
  refine ⟨?_, fun n hn => ?_⟩
  · have h := HahnSeries.coeff_single_mul_add (r := (1 : K)) (x := U ^ i) (a := 0) (b := (i : ℤ))
    rw [zero_add, one_mul] at h
    rw [h, hUi.1]
  · have h := HahnSeries.coeff_single_mul_add (r := (1 : K)) (x := U ^ i) (a := n - i) (b := (i : ℤ))
    rw [sub_add_cancel, one_mul] at h
    rw [h, hUi.2 _ (by omega)]

theorem main : Transcendental K (lambdaModC K) := by
  rintro ⟨P, hP0, hP⟩
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact hP0 (Subsingleton.elim _ _)
  set d := P.natTrailingDegree with hd
  have hcd : P.coeff d ≠ 0 := by rw [hd]; exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hP0
  have h := congrArg (fun x : LaurentSeries K => x.coeff (d : ℤ)) hP
  simp only [HahnSeries.coeff_zero] at h
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum] at h
  have halg : ∀ c : K, algebraMap K (LaurentSeries K) c = HahnSeries.C c := fun c => by
    first
      | rfl
      | (rw [HahnSeries.algebraMap_apply', show algebraMap K (PowerSeries K) c = PowerSeries.C c from by simp,
          HahnSeries.ofPowerSeries_C])
      | (ext m; simp [HahnSeries.coeff_single])
  have hterm : ∀ i : ℕ, ((algebraMap K (LaurentSeries K)) (P.coeff i) * lambdaModC K ^ i).coeff (d : ℤ)
      = P.coeff i * ((lambdaModC K) ^ i).coeff (d : ℤ) := by
    intro i
    rw [halg, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
  simp only [hterm] at h
  rw [Finset.sum_eq_single d] at h
  · rw [(coeff_lambdaModC_pow K d).1, mul_one] at h
    exact hcd h
  · intro i _ hid
    rcases lt_or_gt_of_ne hid with hlt | hgt
    · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (hd ▸ hlt), zero_mul]
    · rw [(coeff_lambdaModC_pow K i).2 d (by exact_mod_cast hgt), mul_zero]
  · intro h'
    exfalso; apply h'
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (hd ▸ Polynomial.natTrailingDegree_le_natDegree P)

end ModularCurve.TrLambda

theorem solution (K : Type*) [CommRing K] : Transcendental K (ModularCurve.lambdaModC K) :=
  ModularCurve.TrLambda.main K

end S_ModularCurve_transcendental_lambdaModC
end P2MW
export P2MW.S_ModularCurve_transcendental_lambdaModC (solution)
