-- Prove2me | solution 1 for ModularCurve.map_eq_phiProd_lambda_of_eval_qExpand_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/35899790-6532-5c0c-8d4f-47eb96ab8826

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_map_eq_phiProd_lambda_of_eval_qExpand_eq_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 8000000

noncomputable section

open ModularCurve ModularCurve.PhiGen Polynomial

namespace LambdaSplitSol

section Supp

variable {R : Type*} [CommRing R]

def SuppGE (n : ℤ) (x : LaurentSeries R) : Prop := ∀ k < n, x.coeff k = 0

namespace SuppGE

variable {n a b : ℤ} {x y : LaurentSeries R}

theorem mono {m : ℤ} (h : m ≤ n) (hx : SuppGE n x) : SuppGE m x := fun k hk => hx k (lt_of_lt_of_le hk h)

theorem add (hx : SuppGE n x) (hy : SuppGE n y) : SuppGE n (x + y) :=
  fun k hk => by rw [HahnSeries.coeff_add, hx k hk, hy k hk, add_zero]

theorem neg (hx : SuppGE n x) : SuppGE n (-x) :=
  fun k hk => by rw [HahnSeries.coeff_neg, hx k hk, neg_zero]

theorem sub (hx : SuppGE n x) (hy : SuppGE n y) : SuppGE n (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem single' (m : ℤ) (r : R) : SuppGE m (HahnSeries.single m r) :=
  fun k hk => HahnSeries.coeff_single_of_ne (ne_of_lt hk)

theorem C' (r : R) : SuppGE 0 (HahnSeries.C r : LaurentSeries R) := single' 0 r

theorem one' : SuppGE 0 (1 : LaurentSeries R) := by
  have h := C' (1 : R)
  rwa [map_one] at h

theorem ofNat' (m : ℕ) [m.AtLeastTwo] : SuppGE 0 (OfNat.ofNat m : LaurentSeries R) := by
  have h := C' (R := R) (OfNat.ofNat m)
  rwa [map_ofNat] at h

theorem mul (hx : SuppGE a x) (hy : SuppGE b y) : SuppGE (a + b) (x * y) := by
  intro k hk
  rw [HahnSeries.coeff_mul]
  refine Finset.sum_eq_zero (fun ij hij => ?_)
  rw [Finset.mem_antidiagonal] at hij
  obtain ⟨h1, h2, h3⟩ := hij
  rw [HahnSeries.mem_support] at h1 h2
  have ha : a ≤ ij.1 := not_lt.mp (fun hlt => h1 (hx _ hlt))
  have hb : b ≤ ij.2 := not_lt.mp (fun hlt => h2 (hy _ hlt))
  omega

theorem pow (hx : SuppGE a x) : ∀ m : ℕ, SuppGE (m * a) (x ^ m)
  | 0 => by rw [pow_zero, Nat.cast_zero, zero_mul]; exact one'
  | m + 1 => by rw [pow_succ, Nat.cast_succ, add_mul, one_mul]; exact (pow hx m).mul hx

theorem pow0 (hx : SuppGE 0 x) (m : ℕ) : SuppGE 0 (x ^ m) := by simpa using hx.pow m

theorem qExpand' (hx : SuppGE a x) (N : ℕ) [NeZero N] : SuppGE (N * a) (ModularCurve.qExpand R N x) := by
  intro k hk
  by_cases hd : (N : ℤ) ∣ k
  · obtain ⟨k', rfl⟩ := hd
    rw [qExpand_coeff_mul]
    refine hx k' ?_
    have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    exact lt_of_mul_lt_mul_left hk hN.le
  · exact qExpand_coeff_of_not_dvd N x hd

theorem laurentMap' (hx : SuppGE a x) {S : Type*} [CommRing S] (f : R →+* S) :
    SuppGE a (ModularCurve.laurentMap f x) :=
  fun k hk => by rw [laurentMap_coeff, hx k hk, map_zero]

theorem ofPowerSeries' (p : PowerSeries R) : SuppGE 0 (HahnSeries.ofPowerSeries ℤ R p) :=
  fun k hk => ofPowerSeries_coeff_of_neg p hk

end SuppGE

theorem coeff_mul_of_suppGE {a b : ℤ} {x y : LaurentSeries R} (hx : SuppGE a x) (hy : SuppGE b y) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
  rw [HahnSeries.coeff_mul, Finset.sum_eq_single (a, b)]
  · intro ij hij hne
    rw [Finset.mem_antidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    rw [HahnSeries.mem_support] at h1 h2
    have ha : a ≤ ij.1 := not_lt.mp (fun hlt => h1 (hx _ hlt))
    have hb : b ≤ ij.2 := not_lt.mp (fun hlt => h2 (hy _ hlt))
    exfalso
    apply hne
    refine Prod.ext ?_ ?_
    · show ij.1 = a
      omega
    · show ij.2 = b
      omega
  · intro hn
    rw [Finset.mem_antidiagonal, not_and, not_and] at hn
    by_cases hxa : x.coeff a = 0
    · rw [hxa, zero_mul]
    by_cases hyb : y.coeff b = 0
    · rw [hyb, mul_zero]
    exact absurd rfl (hn (by rw [HahnSeries.mem_support]; exact hxa) (by rw [HahnSeries.mem_support]; exact hyb))

theorem coeff_pow_of_suppGE_zero {x : LaurentSeries R} (hx : SuppGE 0 x) :
    ∀ m : ℕ, (x ^ m).coeff 0 = (x.coeff 0) ^ m
  | 0 => by
      rw [pow_zero, pow_zero]
      have h : (HahnSeries.C (1 : R) : LaurentSeries R).coeff 0 = 1 := by
        rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]
      rwa [map_one] at h
  | m + 1 => by
      rw [pow_succ, pow_succ, ← coeff_pow_of_suppGE_zero hx m]
      have h := coeff_mul_of_suppGE (hx.pow0 m) hx
      rwa [add_zero] at h

theorem coeff_C_zero (r : R) : (HahnSeries.C r : LaurentSeries R).coeff 0 = r := by
  rw [HahnSeries.C_apply, HahnSeries.coeff_single_same]

theorem coeff_one_zero : (1 : LaurentSeries R).coeff 0 = 1 := by
  have h := coeff_C_zero (1 : R); rwa [map_one] at h

theorem coeff_ofNat_zero (m : ℕ) [m.AtLeastTwo] : (OfNat.ofNat m : LaurentSeries R).coeff 0 = (OfNat.ofNat m : R) := by
  have h := coeff_C_zero (R := R) (OfNat.ofNat m); rwa [map_ofNat] at h

theorem coeff_zero_of_suppGE_one {x : LaurentSeries R} (hx : SuppGE 1 x) : x.coeff 0 = 0 := hx 0 zero_lt_one

end Supp

theorem suppGE_lambdaInt_and_coeff : SuppGE 1 lambdaInt ∧ lambdaInt.coeff 1 = 1 := by

  set A : LaurentSeries ℤ := HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 with hA
  set X : LaurentSeries ℤ := qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) with hX
  set Y : LaurentSeries ℤ := qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) with hY
  have hdef : lambdaInt = HahnSeries.single 1 1 * (A * (X * Y)) := by
    rw [lambdaInt]; simp only [mul_assoc, hA, hX, hY]
  have hE : SuppGE 0 (HahnSeries.ofPowerSeries ℤ ℤ etaProd) := SuppGE.ofPowerSeries' _
  have hE0 : (HahnSeries.ofPowerSeries ℤ ℤ etaProd).coeff 0 = 1 := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_etaProd]
  have hAs : SuppGE 0 A := hE.pow0 8
  have hA0 : A.coeff 0 = 1 := by rw [hA, coeff_pow_of_suppGE_zero hE, hE0, one_pow]
  have hXs : SuppGE 0 X := by rw [hX]; simpa using (hE.pow0 16).qExpand' 4
  have hX0 : X.coeff 0 = 1 := by
    have h := qExpand_coeff_mul 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) 0
    rw [mul_zero] at h
    rw [hX, h, coeff_pow_of_suppGE_zero hE, hE0, one_pow]
  have hD : SuppGE 0 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) := SuppGE.ofPowerSeries' _
  have hYs : SuppGE 0 Y := by rw [hY]; simpa using hD.qExpand' 2
  have hY0 : Y.coeff 0 = 1 := by
    have h := qExpand_coeff_mul 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv) 0
    rw [mul_zero] at h
    rw [hY, h, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dedekindEtaUnitInv]
  have hZs : SuppGE 0 (A * (X * Y)) := by simpa using hAs.mul (hXs.mul hYs)
  have hZ0 : (A * (X * Y)).coeff 0 = 1 := by
    have h1 := coeff_mul_of_suppGE hXs hYs
    rw [add_zero] at h1
    have h2 := coeff_mul_of_suppGE hAs (hXs.mul hYs)
    simp only [add_zero] at h2
    rw [h2, h1, hA0, hX0, hY0]; ring
  refine ⟨?_, ?_⟩
  · rw [hdef]
    have h := (SuppGE.single' (R := ℤ) 1 1).mul hZs
    rwa [add_zero] at h
  · rw [hdef]
    have h := coeff_mul_of_suppGE (SuppGE.single' (R := ℤ) 1 1) hZs
    rw [add_zero] at h
    rw [h, HahnSeries.coeff_single_same, hZ0, one_mul]

section Main

variable {K : Type*} [Field K]

theorem coeff_lambdaModC_one : (lambdaModC K).coeff 1 = 1 := by
  show (laurentMap (Int.castRingHom K) lambdaInt).coeff 1 = 1
  rw [laurentMap_coeff, suppGE_lambdaInt_and_coeff.2, map_one]

theorem eval_map_comp_apply {A B C : Type*} [CommSemiring A] [CommSemiring B] [CommSemiring C]
    (P : Polynomial A) (g : A →+* B) (f : B →+* C) (x : B) :
    (P.map (f.comp g)).eval (f x) = f ((P.map g).eval x) := by
  rw [← Polynomial.map_map, eval_map, eval₂_at_apply]

variable (q : ℕ) [hq : Fact q.Prime] (ζ : Kˣ)

def lconj : Fin (q + 1) → LaurentSeries K :=
  Fin.cons (qExpand K (q * q) (lambdaModC K)) (fun b : Fin q => qTwist (ζ ^ (b : ℕ)) (lambdaModC K))

theorem lconj_zero : lconj q ζ 0 = qExpand K (q * q) (lambdaModC K) := by
  simp [lconj]

theorem lconj_succ (b : Fin q) : lconj q ζ b.succ = qTwist (ζ ^ (b : ℕ)) (lambdaModC K) := by
  simp [lconj]

theorem not_sq_dvd_one : ¬ ((q * q : ℕ) : ℤ) ∣ 1 := by
  intro h
  have h' : q * q ∣ 1 := by exact_mod_cast h
  exact hq.out.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right (Nat.dvd_one.mp h'))

theorem coeff_lconj_zero_one : (lconj q ζ 0).coeff 1 = 0 := by
  rw [lconj_zero]
  exact qExpand_coeff_of_not_dvd (q * q) _ (not_sq_dvd_one q)

theorem coeff_lconj_succ_one (b : Fin q) : (lconj q ζ b.succ).coeff 1 = (ζ : K) ^ (b : ℕ) := by
  rw [lconj_succ, qTwist_coeff, zpow_one, coeff_lambdaModC_one, mul_one, Units.val_pow_eq_pow_val]

theorem lconj_injective (hζ : IsPrimitiveRoot (ζ : K) q) : Function.Injective (lconj q ζ) := by
  have hz : ∀ b : Fin q, lconj q ζ 0 ≠ lconj q ζ b.succ := fun b h => by
    have hc := congrArg (fun f : LaurentSeries K => f.coeff 1) h
    simp only [coeff_lconj_zero_one, coeff_lconj_succ_one] at hc
    exact pow_ne_zero _ (Units.ne_zero ζ) hc.symm
  intro i j hij
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨a, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨b, rfl⟩
    · rfl
    · exact absurd hij (hz b)
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨b, rfl⟩
    · exact absurd hij.symm (hz a)
    · have hc := congrArg (fun f : LaurentSeries K => f.coeff 1) hij
      simp only [coeff_lconj_succ_one] at hc
      have hab : (a : ℕ) = b := hζ.pow_inj a.isLt b.isLt hc
      rw [Fin.ext hab]

variable [Algebra ℚ K]

theorem coeffEmb_qExpand' (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb K (qExpand ℚ n x) = qExpand K n (coeffEmb K x) := by
  ext k
  rw [coeffEmb_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffEmb_coeff]
  · rw [qExpand_coeff_of_not_dvd n x hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem coeffEmb_lambdaModC : coeffEmb K (lambdaModC ℚ) = lambdaModC K := by
  ext k
  simp only [coeffEmb, coeffMap_coeff, lambdaModC, laurentMap_coeff]
  simp

theorem twist_comp_emb_comp_qExpand (hζ : IsPrimitiveRoot (ζ : K) q) (b : ℕ) :
    ((qTwist (ζ ^ b)).comp (coeffEmb K)).comp (qExpand ℚ q) = (coeffEmb K).comp (qExpand ℚ q) := by
  refine RingHom.ext (fun x => ?_)
  simp only [RingHom.comp_apply]
  rw [coeffEmb_qExpand', qTwist_qExpand]
  have hq1 : ζ ^ q = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)
  have h1 : (ζ ^ b) ^ (q : ℤ) = 1 := by
    rw [zpow_natCast, ← pow_mul, mul_comm, pow_mul, hq1, one_pow]
  rw [h1, qTwist_one_apply]

variable (P : Polynomial (LaurentSeries ℚ))

theorem isRoot_lconj_zero (h0 : P.eval (lambdaNModC ℚ q) = 0) :
    (P.map ((coeffEmb K).comp (qExpand ℚ q))).IsRoot (lconj q ζ 0) := by
  have hE : lconj q ζ 0 = ((coeffEmb K).comp (qExpand ℚ q)) (lambdaNModC ℚ q) := by
    rw [lconj_zero, RingHom.comp_apply, lambdaNModC, qExpand_qExpand, coeffEmb_qExpand', coeffEmb_lambdaModC]
  rw [IsRoot, hE, eval_map, eval₂_at_apply, h0, map_zero]

theorem isRoot_lconj_succ (hζ : IsPrimitiveRoot (ζ : K) q) (h1 : (P.map (qExpand ℚ q)).eval (lambdaModC ℚ) = 0)
    (b : Fin q) : (P.map ((coeffEmb K).comp (qExpand ℚ q))).IsRoot (lconj q ζ b.succ) := by
  have hT : lconj q ζ b.succ = ((qTwist (ζ ^ (b : ℕ))).comp (coeffEmb K)) (lambdaModC ℚ) := by
    rw [lconj_succ, RingHom.comp_apply, coeffEmb_lambdaModC]
  rw [IsRoot, hT, ← twist_comp_emb_comp_qExpand q ζ hζ (b : ℕ), eval_map_comp_apply, h1, map_zero]

theorem main (hζ : IsPrimitiveRoot (ζ : K) q) (hP : P.Monic) (hdeg : P.natDegree = q + 1)
    (h0 : P.eval (lambdaNModC ℚ q) = 0) (h1 : (P.map (qExpand ℚ q)).eval (lambdaModC ℚ) = 0) :
    P.map ((coeffEmb K).comp (qExpand ℚ q)) = phiProd q (lconj q ζ) := by
  have hmK : (P.map ((coeffEmb K).comp (qExpand ℚ q))).Monic := hP.map _
  have hdK : (P.map ((coeffEmb K).comp (qExpand ℚ q))).natDegree = q + 1 := by rw [hP.natDegree_map, hdeg]
  have hroot : ∀ i, (P.map ((coeffEmb K).comp (qExpand ℚ q))).IsRoot (lconj q ζ i) := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨b, rfl⟩
    · exact isRoot_lconj_zero q ζ P h0
    · exact isRoot_lconj_succ q ζ P hζ h1 b

  have hdvd : phiProd q (lconj q ζ) ∣ P.map ((coeffEmb K).comp (qExpand ℚ q)) := by
    rw [phiProd]
    refine Finset.prod_dvd_of_coprime ?_ (fun i _ => dvd_iff_isRoot.mpr (hroot i))
    exact (pairwise_coprime_X_sub_C (lconj_injective q ζ hζ)).set_pairwise _

  exact eq_of_monic_of_dvd_of_natDegree_le (phiProd_monic q _) hmK hdvd (by rw [hdK, phiProd_natDegree])

end Main

end LambdaSplitSol

end

open ModularCurve ModularCurve.PhiGen in
theorem solution {K : Type*} [Field K] [Algebra ℚ K] (q : ℕ) [Fact q.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) q)
    (P : Polynomial (LaurentSeries ℚ)) (hP : P.Monic) (hdeg : P.natDegree = q + 1)
    (h0 : P.eval (lambdaNModC ℚ q) = 0)
    (h1 : (P.map (qExpand ℚ q)).eval (lambdaModC ℚ) = 0) :
    P.map ((coeffEmb K).comp (qExpand ℚ q)) =
      phiProd q (Fin.cons (qExpand K (q * q) (lambdaModC K))
        (fun b : Fin q => qTwist (ζ ^ (b : ℕ)) (lambdaModC K)) : Fin (q + 1) → LaurentSeries K) :=
  LambdaSplitSol.main q ζ P hζ hP hdeg h0 h1

end S_ModularCurve_map_eq_phiProd_lambda_of_eval_qExpand_eq_zero
end P2MW
export P2MW.S_ModularCurve_map_eq_phiProd_lambda_of_eval_qExpand_eq_zero (solution)
