-- Prove2me | solution 1 for HodgeComputer.Fermat.certificate
-- status  : ACCEPTED   (prove)
-- author  : @benediamond
-- created : 2026-11-05T22:24:23.470665+00:00
-- url     : https://prove2.me/submissions/3d62b3c7-f5f7-4319-97ba-1cab6f7016ed

import Definitions.Def_HodgeComputerFermat
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
namespace HodgeComputer
open MvPolynomial
open scoped BigOperators

theorem Homogeneous.of_isHomogeneous {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℕ}
    (h : P.IsHomogeneous k) : Homogeneous P (k : ℤ) := by
  intro m hm
  exact_mod_cast (show m.degree = k by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h hm)

theorem Homogeneous.isHomogeneous {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (hk : 0 ≤ k) : P.IsHomogeneous k.toNat := by
  intro m hm
  have hd := h hm
  have he : m.degree = k.toNat := by omega
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using he

theorem Homogeneous.eq_zero_of_neg {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (hk : k < 0) : P = 0 := by
  ext m
  rw [coeff_zero]
  by_contra hm
  have hd := h hm
  omega

theorem homogeneous_zero {σ : Type*} (k : ℤ) : Homogeneous (0 : MvPolynomial σ ℂ) k := by
  intro m hm
  exact False.elim (hm (coeff_zero m))

theorem Homogeneous.add {σ : Type*} {P Q : MvPolynomial σ ℂ} {k : ℤ}
    (hP : Homogeneous P k) (hQ : Homogeneous Q k) : Homogeneous (P + Q) k := by
  by_cases hk : 0 ≤ k
  · have h := Homogeneous.of_isHomogeneous ((hP.isHomogeneous hk).add (hQ.isHomogeneous hk))
    simpa only [Int.toNat_of_nonneg hk] using h
  · rw [hP.eq_zero_of_neg (by omega), hQ.eq_zero_of_neg (by omega), zero_add]
    exact homogeneous_zero k

theorem Homogeneous.mul {σ : Type*} {P Q : MvPolynomial σ ℂ} {k l : ℤ}
    (hP : Homogeneous P k) (hQ : Homogeneous Q l) : Homogeneous (P * Q) (k + l) := by
  by_cases hk : 0 ≤ k
  · by_cases hl : 0 ≤ l
    · have h := Homogeneous.of_isHomogeneous ((hP.isHomogeneous hk).mul (hQ.isHomogeneous hl))
      simpa only [Nat.cast_add, Int.toNat_of_nonneg hk, Int.toNat_of_nonneg hl] using h
    · rw [hQ.eq_zero_of_neg (by omega), mul_zero]
      exact homogeneous_zero _
  · rw [hP.eq_zero_of_neg (by omega), zero_mul]
    exact homogeneous_zero _

theorem Homogeneous.C_mul {σ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (c : ℂ) : Homogeneous (C c * P) k := by
  simpa using (Homogeneous.of_isHomogeneous (isHomogeneous_C (σ := σ) c)).mul h

theorem Homogeneous.rename {σ τ : Type*} {P : MvPolynomial σ ℂ} {k : ℤ}
    (h : Homogeneous P k) (f : σ → τ) : Homogeneous (MvPolynomial.rename f P) k := by
  by_cases hk : 0 ≤ k
  · simpa only [Int.toNat_of_nonneg hk] using
      Homogeneous.of_isHomogeneous ((h.isHomogeneous hk).rename_isHomogeneous (f := f))
  · rw [h.eq_zero_of_neg (by omega), map_zero]
    exact homogeneous_zero _

theorem directional_mul {n : ℕ} (P H : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    directional P (fun i => H * N i) = H * directional P N := by
  unfold directional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem directional_product {n : ℕ} (P H : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    directional (H * P) N = P * directional H N + H * directional P N := by
  unfold directional
  simp only [pderiv_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem divergence_mul {n : ℕ} (H : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    divergence (fun i => H * N i) = directional H N + H * divergence N := by
  unfold divergence directional
  simp only [pderiv_mul, Finset.sum_add_distrib, Finset.mul_sum]

/-- Multiplying both `D` and `N` by `H` multiplies the divergence numerator by `H²`.
The derivatives of `H` cancel exactly. No regularity or nonzero assumption is needed. -/
theorem divergenceNumerator_mul {n : ℕ} (H D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) :
    divergenceNumerator (H * D) (fun i => H * N i) =
      H ^ 2 * divergenceNumerator D N := by
  unfold divergenceNumerator
  rw [divergence_mul, directional_mul, directional_product]
  ring

theorem directional_add {n : ℕ} (P : AmbientPoly n) (N M : Fin (n + 1) → AmbientPoly n) :
    directional P (fun i => N i + M i) = directional P N + directional P M := by
  simp [directional, mul_add, Finset.sum_add_distrib]

theorem divergence_add {n : ℕ} (N M : Fin (n + 1) → AmbientPoly n) :
    divergence (fun i => N i + M i) = divergence N + divergence M := by
  simp [divergence, map_add, Finset.sum_add_distrib]

theorem divergenceNumerator_add {n : ℕ} (D : AmbientPoly n) (N M : Fin (n + 1) → AmbientPoly n) :
    divergenceNumerator D (fun i => N i + M i) =
      divergenceNumerator D N + divergenceNumerator D M := by
  simp only [divergenceNumerator, divergence_add, directional_add]
  ring

theorem defect_add_same_denominator {n : ℕ} (F A B D : AmbientPoly n) (q : ℕ)
    (N M : Fin (n + 1) → AmbientPoly n) :
    defect F (A+B) D q (fun i => N i + M i) =
      defect F A D q N + defect F B D q M := by
  simp only [defect, directional_add, divergenceNumerator_add]
  ring

theorem defect_scale_denominator {n : ℕ} (F A D H : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) :
    defect F A (H*D) q (fun i => H*N i) = H^2 * defect F A D q N := by
  simp only [defect, directional_mul,
    divergenceNumerator_mul]
  ring

theorem defect_add {n : ℕ} (F A B D E : AmbientPoly n) (q : ℕ) (N M : Fin (n + 1) → AmbientPoly n) :
    defect F (A+B) (D*E) q (fun i => E*N i + D*M i) =
      E^2 * defect F A D q N + D^2 * defect F B E q M := by
  rw [defect_add_same_denominator]
  conv_lhs => lhs; rw [mul_comm D E]
  rw [defect_scale_denominator, defect_scale_denominator]

theorem Verify.add {n : ℕ} {F A B D E Q R : AmbientPoly n} {d q : ℕ}
    {N M : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (k : Verify F B d q E M R) :
    Verify F (A+B) d q (D*E) (fun i => E*N i + D*M i)
      (E^2*Q+D^2*R) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous.add k.source_homogeneous
  denominator_ne_zero := mul_ne_zero h.denominator_ne_zero k.denominator_ne_zero
  denominator_homogeneous := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain h.denominator_ne_zero k.denominator_ne_zero]
    exact h.denominator_homogeneous.mul k.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    have hn := (Homogeneous.of_isHomogeneous k.denominator_homogeneous).mul (h.numerator_homogeneous i)
    have hm := (Homogeneous.of_isHomogeneous h.denominator_homogeneous).mul (k.numerator_homogeneous i)
    rw [MvPolynomial.totalDegree_mul_of_isDomain h.denominator_ne_zero k.denominator_ne_zero, Nat.cast_add]
    convert hn.add (by convert hm using 1 <;> ring) using 1 <;> ring
  denominator_legal := h.denominator_legal.mul_right k.denominator_legal
  identity := by
    rw [defect_add, h.identity, k.identity]
    ring

theorem HasCertificate.add {n : ℕ} {F A B : AmbientPoly n} {d q : ℕ}
    (h : HasCertificate F A d q) (k : HasCertificate F B d q) :
    HasCertificate F (A+B) d q := by
  obtain ⟨D, N, Q, h⟩ := h
  obtain ⟨E, M, R, k⟩ := k
  exact ⟨D*E, (fun i => E*N i+D*M i), E^2*Q+D^2*R, Verify.add h k⟩

/-- The zero source has a certificate with constant denominator. -/
theorem HasCertificate.zero {n : ℕ} (F : AmbientPoly n) (d q : ℕ)
    (hF : F ≠ 0) (hd : F.IsHomogeneous d) : HasCertificate F 0 d q := by
  refine ⟨1, (fun _ => 0), 0, ?_⟩
  exact {
    hypersurface_ne_zero := hF
    hypersurface_homogeneous := hd
    source_homogeneous := homogeneous_zero _
    denominator_ne_zero := one_ne_zero
    denominator_homogeneous := by simpa using isHomogeneous_one (Fin (n+1)) ℂ
    numerator_homogeneous := fun _ => homogeneous_zero _
    denominator_legal := isRelPrime_one_right
    identity := by simp [defect, directional, divergenceNumerator, divergence]
  }

end HodgeComputer

set_option maxHeartbeats 0
set_option maxRecDepth 100000
open scoped BigOperators

def EulerCondition (a : Fin 6 → ℕ) : Prop :=
  a 3 + a 4 + a 5 ≡ 1 [MOD 2] →
  ∃ I ∈ (Finset.univ : Finset (Fin 6)).powerset, ∑ i ∈ I, (a i + 1) = 6

theorem euler_q1 : ∀ a ∈ Finset.Nat.antidiagonalTuple 6 6, EulerCondition a := by unfold EulerCondition; decide +kernel
theorem euler_q2 : ∀ a ∈ Finset.Nat.antidiagonalTuple 6 12, EulerCondition a := by unfold EulerCondition; decide +kernel

theorem subset_euler (a : Fin 6 → ℕ) (q : ℕ) (hq : q = 1 ∨ q = 2)
    (ha : ∑ i, a i = 6*q) (ho : Odd (a 3 + a 4 + a 5)) :
    ∃ I : Finset (Fin 6), ∑ i ∈ I, (a i + 1) = 6 := by
  have hodd : a 3 + a 4 + a 5 ≡ 1 [MOD 2] := by
    obtain ⟨k,hk⟩ := ho
    unfold Nat.ModEq
    omega
  have hw : EulerCondition a := by
    rcases hq with rfl | rfl
    · exact euler_q1 a (Finset.Nat.mem_antidiagonalTuple.mpr (by simpa using ha))
    · exact euler_q2 a (Finset.Nat.mem_antidiagonalTuple.mpr (by simpa using ha))
  obtain ⟨I,_,hI⟩ := hw hodd
  exact ⟨I,hI⟩



set_option maxHeartbeats 1000000
noncomputable section
namespace HodgeComputer.Fermat
open MvPolynomial
open scoped BigOperators

abbrev R := AmbientPoly 5

def partialF (I : Finset (Fin 6)) : R := ∑ i ∈ I, X i ^ 6

lemma partialF_homogeneous (I : Finset (Fin 6)) : (partialF I).IsHomogeneous 6 := by
  apply IsHomogeneous.sum
  intro i hi
  simpa using (isHomogeneous_X ℂ i).pow 6

lemma partialF_ne_zero (I : Finset (Fin 6)) (hI : I.Nonempty) : partialF I ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval (fun _ : Fin 6 => (1 : ℂ))) h
  simp [partialF] at he
  exact hI.ne_empty he

lemma F_ne_zero : F ≠ 0 := by
  exact partialF_ne_zero Finset.univ ⟨0, Finset.mem_univ _⟩

lemma F_homogeneous : F.IsHomogeneous 6 := partialF_homogeneous Finset.univ

lemma monic_relPrime_constant {S : Type*} [CommRing S] [IsDomain S]
    {f : Polynomial S} (hf : f.Monic) {c : S} (hc : c ≠ 0) :
    IsRelPrime f (Polynomial.C c) := by
  intro p hpf hpc
  by_contra hunit
  have hpos := Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hf hunit hpf
  have hle := Polynomial.natDegree_le_of_dvd hpc (Polynomial.C_ne_zero.mpr hc)
  simp only [Polynomial.natDegree_C] at hle
  omega

def toUni (j : Fin 6) : R →+* Polynomial R :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => if i = j then Polynomial.X else Polynomial.C (X i))

def fromUni (j : Fin 6) : Polynomial R →+* R :=
  Polynomial.eval₂RingHom (RingHom.id R) (X j)

lemma retract (j : Fin 6) : (fromUni j).comp (toUni j) = RingHom.id R := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [toUni, fromUni]
  · intro i
    by_cases hi : i = j <;> simp [toUni, fromUni, hi]

lemma toUni_partialF (I : Finset (Fin 6)) (j : Fin 6) (hj : j ∉ I) :
    toUni j (partialF I) = Polynomial.C (partialF I) := by
  simp only [partialF, map_sum, map_pow]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  simp [toUni, hij]

lemma toUni_F (j : Fin 6) :
    toUni j F = Polynomial.X ^ 6 + Polynomial.C (partialF (Finset.univ.erase j)) := by
  change toUni j (partialF Finset.univ) = _
  have hsplit : partialF Finset.univ = partialF (Finset.univ.erase j) + (X j : R) ^ 6 := by
    exact (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
  rw [hsplit, map_add, toUni_partialF _ _ (Finset.notMem_erase j _)]
  simp [toUni, add_comm]

lemma partialF_legal (I : Finset (Fin 6)) (hI : I.Nonempty) (j : Fin 6) (hj : j ∉ I) :
    IsRelPrime F (partialF I) := by
  have h : IsRelPrime (toUni j F) (toUni j (partialF I)) := by
    rw [toUni_F, toUni_partialF I j hj]
    apply monic_relPrime_constant
    · change (Polynomial.X ^ 6 + Polynomial.C (partialF (Finset.univ.erase j))).leadingCoeff = 1
      exact Polynomial.leadingCoeff_X_pow_add_C (by decide)
    · exact partialF_ne_zero I hI
  intro p hpF hpI
  have hu := (h (map_dvd (toUni j) hpF) (map_dvd (toUni j) hpI)).map (fromUni j)
  have hr : fromUni j (toUni j p) = p := RingHom.congr_fun (retract j) p
  rwa [hr] at hu


def eulerNumerator (I : Finset (Fin 6)) (A : R) (i : Fin 6) : R :=
  if i ∈ I then A * X i else 0

lemma pderiv_partialF (I : Finset (Fin 6)) (i : Fin 6) :
    pderiv i (partialF I) = if i ∈ I then 6 * X i ^ 5 else 0 := by
  simp [partialF, pderiv_pow, pderiv_X, Pi.single_apply, Finset.sum_ite_eq']

lemma pderiv_F (i : Fin 6) : pderiv i F = 6 * X i ^ 5 := by
  change pderiv i (partialF Finset.univ) = _
  simp [pderiv_partialF]

lemma directional_F_euler (I : Finset (Fin 6)) (A : R) :
    directional (n := 5) F (eulerNumerator I A) = 6 * A * partialF I := by
  change (∑ i : Fin 6, (pderiv i (F : R)) * eulerNumerator I A i) = _
  simp only [pderiv_F, eulerNumerator, mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [partialF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma directional_partialF_euler (I : Finset (Fin 6)) (A : R) :
    directional (partialF I) (eulerNumerator I A) = 6 * A * partialF I := by
  change (∑ i : Fin 6, pderiv i (partialF I) * eulerNumerator I A i) = _
  simp only [pderiv_partialF, eulerNumerator, ite_mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  simp only [partialF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma divergence_euler (I : Finset (Fin 6)) (A : R) :
    divergence (eulerNumerator I A) = ∑ i ∈ I, (X i * pderiv i A + A) := by
  unfold divergence
  simp only [eulerNumerator, apply_ite, map_zero, Finset.sum_ite_mem, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pderiv_mul, pderiv_X, mul_comm]
  ring


lemma monomial_euler_weight (I : Finset (Fin 6)) (a : Fin 6 →₀ ℕ) (c : ℂ)
    (hI : ∑ i ∈ I, (a i + 1) = 6) :
    ∑ i ∈ I, (X i * pderiv i (monomial a c) + monomial a c) =
      6 * (monomial a c : R) := by
  have he (i : Fin 6) : X i * pderiv i (monomial a c) + monomial a c =
      ((a i + 1 : ℕ) : R) * monomial a c := by
    rw [X_mul_pderiv_monomial]
    simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [he]
  rw [← Finset.sum_mul, ← Nat.cast_sum, hI]
  norm_num

lemma monomial_hasCertificate (q : ℕ) (hq : q ≠ 0) (a : Fin 6 →₀ ℕ) (c : ℂ)
    (ha : a.degree = 6*q) (I : Finset (Fin 6))
    (hI : ∑ i ∈ I, (a i + 1) = 6) (hIp : ∃ j, j ∉ I) :
    HasCertificate (n := 5) F (monomial a c) 6 q := by
  have hIn : I.Nonempty := by
    by_contra h
    have he : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hI
  obtain ⟨j,hj⟩ := hIp
  let D : R := (6*q) * partialF I
  let N : Fin 6 → R := eulerNumerator I (monomial a c)
  have hqR : (q : R) ≠ 0 := by exact_mod_cast hq
  have hscalar : (6 : R) * q ≠ 0 := mul_ne_zero (by norm_num) hqR
  have hD0 : D ≠ 0 := mul_ne_zero hscalar (partialF_ne_zero I hIn)
  have hDhom : D.IsHomogeneous 6 := by
    simpa only [map_mul, map_ofNat, map_natCast, zero_add] using
      (isHomogeneous_C (σ := Fin 6) (6*(q:ℂ))).mul (partialF_homogeneous I)
  have hdegree : D.totalDegree = 6 := hDhom.totalDegree hD0
  have hAhom : (monomial a c : R).IsHomogeneous (6*q) := by
    exact isHomogeneous_monomial c ha
  refine ⟨D,N,0,?_⟩
  refine {
    hypersurface_ne_zero := F_ne_zero
    hypersurface_homogeneous := F_homogeneous
    source_homogeneous := ?_
    denominator_ne_zero := hD0
    denominator_homogeneous := by simpa only [hdegree] using hDhom
    numerator_homogeneous := ?_
    denominator_legal := ?_
    identity := ?_
  }
  · convert Homogeneous.of_isHomogeneous hAhom using 1 <;> push_cast <;> ring
  · intro i
    change Homogeneous (eulerNumerator I (monomial a c) i) _
    unfold eulerNumerator
    split_ifs with hi
    · convert Homogeneous.of_isHomogeneous (hAhom.mul (isHomogeneous_X ℂ i)) using 1 <;>
        simp only [hdegree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] <;> ring
    · exact homogeneous_zero _
  · apply IsRelPrime.mul_right
    · apply IsUnit.isRelPrime_right
      simpa only [map_mul, map_ofNat, map_natCast] using (isUnit_iff_ne_zero.mpr (show (6 : ℂ)*(q:ℂ) ≠ 0 from
        mul_ne_zero (by norm_num) (by exact_mod_cast hq))).map (MvPolynomial.C : ℂ →+* R)
    · exact partialF_legal I hIn j hj
  · have hdir : directional (n := 5) F N = 6 * monomial a c * partialF I :=
      directional_F_euler I (monomial a c)
    have hdiv : divergence N = 6 * monomial a c := by
      rw [show N = eulerNumerator I (monomial a c) from rfl, divergence_euler]
      exact monomial_euler_weight I a c hI
    have hDdir : directional D N = 6 * monomial a c * D := by
      have hc : directional (6*(q:R)) N = 0 := by
        have hh : directional (n := 5) (C (6*(q:ℂ))) N = 0 := by
          simp only [directional, pderiv_C, zero_mul, Finset.sum_const_zero]
        simpa only [map_mul, map_ofNat, map_natCast] using hh
      change directional ((6*(q:R)) * partialF I) N = _
      rw [directional_product, hc, mul_zero, zero_add]
      change (6*(q:R)) * directional (partialF I) (eulerNumerator I (monomial a c)) = _
      rw [directional_partialF_euler]
      dsimp [D]
      ring
    let f : R := F
    change monomial a c * D^2 - (q:R)*D*directional (n := 5) f N +
      f*(D*divergence N-directional D N) = f^(q+1)*(0:R)
    rw [hdir, hdiv, hDdir]
    simp only [mul_zero]
    dsimp [D]
    ring

end HodgeComputer.Fermat


set_option autoImplicit false
noncomputable section
namespace HodgeComputer.Fermat
open MvPolynomial
open scoped BigOperators

/-- Every homogeneous odd source on the Fermat sextic has a certificate
at pole parameter one or two, by the subset Euler construction. -/
theorem certificate
    (q : ℕ) (hq : q = 1 ∨ q = 2)
    (A : HodgeComputer.AmbientPoly HodgeComputer.Fermat.n)
    (hA : A.IsHomogeneous (HodgeComputer.Fermat.d * q))
    (hodd : HodgeComputer.Fermat.OddSource A) :
    HodgeComputer.HasCertificate HodgeComputer.Fermat.F A HodgeComputer.Fermat.d q := by
  classical
  let A0 : R := A
  have hA0 : A0.IsHomogeneous (6*q) := hA
  have hodd0 : ∀ ⦃a : Fin 6 →₀ ℕ⦄, coeff a A0 ≠ 0 → Odd (a 3+a 4+a 5) := hodd
  change HasCertificate (n := 5) F A0 6 q
  have hmono (a : Fin 6 →₀ ℕ) (ha : a ∈ A0.support) :
      HasCertificate (n := 5) F (monomial a (coeff a A0)) 6 q := by
    have hc : coeff a A0 ≠ 0 := mem_support_iff.mp ha
    have hdegree : a.degree = 6*q := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hA0 hc
    obtain ⟨I,hI⟩ := subset_euler a q hq
      (by simpa only [← Finsupp.degree_eq_sum] using hdegree) (hodd0 hc)
    have hproper : ∃ j : Fin 6, j ∉ I := by
      by_contra h
      have hfull : I = Finset.univ := Finset.eq_univ_of_forall (by
        intro j
        by_contra hj
        exact h ⟨j,hj⟩)
      have hsum : (∑ i : Fin 6, (a i+1)) = 6*q+6 := by
        rw [Finset.sum_add_distrib, ← Finsupp.degree_eq_sum, hdegree]
        simp
      rw [hfull, hsum] at hI
      rcases hq with rfl | rfl <;> omega
    exact monomial_hasCertificate q (by omega) a (coeff a A0) hdegree I hI hproper
  have hsum (s : Finset (Fin 6 →₀ ℕ)) :
      (∀ a ∈ s, HasCertificate (n := 5) F (monomial a (coeff a A0)) 6 q) →
      HasCertificate (n := 5) F (∑ a ∈ s, monomial a (coeff a A0)) 6 q := by
    induction s using Finset.induction_on with
    | empty =>
      intro _
      simpa only [Finset.sum_empty] using HasCertificate.zero (n := 5) F 6 q F_ne_zero F_homogeneous
    | @insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      exact (hs a (Finset.mem_insert_self a s)).add
        (ih (fun b hb => hs b (Finset.mem_insert_of_mem hb)))
  simpa only [support_sum_monomial_coeff] using hsum A0.support hmono

end HodgeComputer.Fermat


open HodgeComputer.Fermat in
theorem solution
    (q : ℕ) (hq : q = 1 ∨ q = 2)
    (A : HodgeComputer.AmbientPoly HodgeComputer.Fermat.n)
    (hA : A.IsHomogeneous (HodgeComputer.Fermat.d * q))
    (hodd : HodgeComputer.Fermat.OddSource A) :
    HodgeComputer.HasCertificate
      HodgeComputer.Fermat.F
      A
      HodgeComputer.Fermat.d
      q :=
  HodgeComputer.Fermat.certificate q hq A hA hodd
