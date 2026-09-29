-- Prove2me | solution 1 for HeckeEis.mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1c345bc7-a72a-509d-9946-00aa98c1e46b

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binaryFormRepSL binaryFormRepSL_apply_coe"
p2m_open "HeckeEis"

open MvPolynomial Polynomial
open scoped MatrixGroups

namespace UnipotentFixedAux

variable {R : Type*} [CommRing R] {n : ℕ}

private theorem _root_.HeckeEis.UnipotentFixedAux.monomial_eq (n j : ℕ) :
    (MvPolynomial.monomial (Finsupp.single 0 (n - j) + Finsupp.single 1 j) (1 : R))
      = MvPolynomial.X 0 ^ (n - j) * MvPolynomial.X 1 ^ j := by
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]

p2m_export "HeckeEis.UnipotentFixedAux" "monomial_eq"
variable (n) in

noncomputable def expo (j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 (n - j) + Finsupp.single 1 j

theorem expo_injOn : Set.InjOn (expo n) (Finset.range (n + 1) : Set ℕ) := by
  intro i _ j _ h
  have := congrArg (fun d : Fin 2 →₀ ℕ => d 1) h
  simpa [expo, Finsupp.single_apply] using this

theorem degree_eq_iff (d : Fin 2 →₀ ℕ) : d.degree = n ↔ ∃ j ∈ Finset.range (n + 1), expo n j = d := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  constructor
  · intro h
    refine ⟨d 1, Finset.mem_range.mpr (by omega), ?_⟩
    ext i
    fin_cases i <;> simp [expo, Finsupp.single_apply] <;> omega
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_range] at hj
    simp [expo, Finsupp.single_apply]
    omega

theorem eq_sum_range {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) :
    P = ∑ j ∈ Finset.range (n + 1), MvPolynomial.monomial (expo n j) (MvPolynomial.coeff (expo n j) P) := by
  classical
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  by_cases hd : d.degree = n
  · obtain ⟨j, hj, rfl⟩ := (degree_eq_iff d).mp hd
    rw [Finset.sum_eq_single j (fun i hi hne => if_neg fun h => hne (expo_injOn hi hj h)) (fun h => (h hj).elim),
      if_pos rfl]
  · rw [Finset.sum_eq_zero fun i hi => if_neg fun h => hd ((degree_eq_iff d).mpr ⟨i, hi, h⟩)]
    exact ((MvPolynomial.mem_homogeneousSubmodule n P).mp hP).coeff_eq_zero hd

noncomputable def dehom : MvPolynomial (Fin 2) R →ₐ[R] R[X] := MvPolynomial.aeval ![1, Polynomial.X]

theorem dehom_monomial (j : ℕ) (c : R) :
    dehom (MvPolynomial.monomial (expo n j) c) = Polynomial.C c * Polynomial.X ^ j := by
  rw [expo, MvPolynomial.monomial_eq, Finsupp.prod_add_index' (by simp) (by simp [pow_add]),
    Finsupp.prod_single_index (by simp), Finsupp.prod_single_index (by simp)]
  simp [dehom, Polynomial.C_mul']

theorem dehom_eq_sum {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) :
    dehom P = ∑ j ∈ Finset.range (n + 1), Polynomial.C (MvPolynomial.coeff (expo n j) P) * Polynomial.X ^ j := by
  conv_lhs => rw [eq_sum_range hP, map_sum]
  exact Finset.sum_congr rfl fun j _ => dehom_monomial j _

theorem coeff_dehom {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) (j : ℕ) :
    (dehom P).coeff j = if j ∈ Finset.range (n + 1) then MvPolynomial.coeff (expo n j) P else 0 := by
  rw [dehom_eq_sum hP, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single j (fun i _ hne => if_neg hne.symm) (fun h' => (h' h).elim), if_pos rfl]
  · exact Finset.sum_eq_zero fun i hi => if_neg fun h' => h (by rw [h']; exact hi)

theorem natDegree_dehom_le {P : MvPolynomial (Fin 2) R} (hP : P ∈ BinaryForm R n) : (dehom P).natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro j hj
  rw [coeff_dehom hP, if_neg]
  rw [Finset.mem_range]; omega

theorem dehom_binarySubst_T_zpow (h : ℤ) (P : MvPolynomial (Fin 2) R) :
    dehom (binarySubst R ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) P)
      = (dehom P).comp (Polynomial.X + Polynomial.C (h : R)) := by

  revert P
  refine fun P => ?_
  have key : (dehom : MvPolynomial (Fin 2) R →ₐ[R] R[X]).comp (binarySubst R ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))
      = (Polynomial.aeval (Polynomial.X + Polynomial.C (h : R)) : R[X] →ₐ[R] R[X]).comp dehom := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, binarySubst_X, ModularGroup.coe_T_zpow]
    fin_cases i <;> simp [dehom, Fin.sum_univ_two, add_comm]
  have := congrArg (fun φ => φ P) key
  simpa [Polynomial.aeval_X, Polynomial.comp_eq_aeval] using this

theorem eq_C_of_comp_X_add_C_eq [IsDomain R] {q : R[X]} (hq : q.natDegree ≤ n) {h : R} (hh : h ≠ 0)
    (hn : ∀ j : ℕ, 1 ≤ j → j ≤ n → (j : R) ≠ 0) (hinv : q.comp (Polynomial.X + Polynomial.C h) = q) :
    q = Polynomial.C (q.eval 0) := by
  classical

  have hper : ∀ k : ℕ, q.eval ((k : R) * h) = q.eval 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := congrArg (fun r => Polynomial.eval ((k : R) * h) r) hinv
      simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at this
      rw [← ih, ← this]
      congr 1; push_cast; ring

  set q' : R[X] := q - Polynomial.C (q.eval 0) with hq'
  have hdeg : q'.natDegree ≤ n := (Polynomial.natDegree_sub_le _ _).trans (by simpa using hq)
  have hroots : ∀ k ∈ Finset.range (n + 1), q'.eval ((k : R) * h) = 0 := fun k _ => by
    simp [hq', hper k]
  have hinj : Set.InjOn (fun k : ℕ => (k : R) * h) (Finset.range (n + 1) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have : ((i : R) - (j : R)) * h = 0 := by rw [sub_mul]; exact sub_eq_zero.mpr hij
    rcases mul_eq_zero.mp this with h0 | h0
    ·
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := hn (j - i) (by omega) (by omega)
        apply this; rw [Nat.cast_sub hlt.le]; linear_combination -h0
      · have := hn (i - j) (by omega) (by omega)
        apply this; rw [Nat.cast_sub hlt.le]; linear_combination h0
    · exact (hh h0).elim
  have hzero : q' = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q' ((Finset.range (n + 1)).image fun k : ℕ => (k : R) * h)
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
      exact hroots k hk
    · rw [Finset.card_image_of_injOn hinj, Finset.card_range]; omega
  rw [hq', sub_eq_zero] at hzero
  exact hzero

end UnipotentFixedAux

end HeckeEis

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binaryFormRepSL binaryFormRepSL_apply_coe"
p2m_open "HeckeEis"

open Polynomial

namespace SaturationAux

noncomputable def delta (h : ℤ) (q : ℤ[X]) : ℤ[X] := q.comp (X + C h) - q

theorem delta_add (h : ℤ) (a b : ℤ[X]) : delta h (a + b) = delta h a + delta h b := by
  simp only [delta, add_comp]; ring

theorem delta_sub (h : ℤ) (a b : ℤ[X]) : delta h (a - b) = delta h a - delta h b := by
  simp only [delta, sub_comp]; ring

theorem delta_C_mul (h c : ℤ) (a : ℤ[X]) : delta h (C c * a) = C c * delta h a := by
  simp only [delta, mul_comp, C_comp]; ring

theorem delta_sum (h : ℤ) {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) : delta h (∑ i ∈ s, f i) = ∑ i ∈ s, delta h (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [delta]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, delta_add, ih]

theorem natDegree_comp_le (h : ℤ) (q : ℤ[X]) : (q.comp (X + C h)).natDegree ≤ q.natDegree := by
  rw [natDegree_comp, natDegree_X_add_C, mul_one]

theorem natDegree_delta_le (h : ℤ) (q : ℤ[X]) : (delta h q).natDegree ≤ q.natDegree :=
  (natDegree_sub_le _ _).trans (max_le (natDegree_comp_le h q) le_rfl)

theorem coeff_delta_eq_zero (h : ℤ) {n : ℕ} {q : ℤ[X]} (hq : q.natDegree ≤ n) : (delta h q).coeff n = 0 := by
  rw [delta, coeff_sub, sub_eq_zero]
  rcases hq.lt_or_eq with hlt | heq
  · rw [coeff_eq_zero_of_natDegree_lt ((natDegree_comp_le h q).trans_lt hlt), coeff_eq_zero_of_natDegree_lt hlt]
  · have h1 : (q.comp (X + C h)).leadingCoeff = q.leadingCoeff := by
      rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C, one_pow, mul_one]
    have h2 : (q.comp (X + C h)).natDegree = q.natDegree := by
      rw [natDegree_comp, natDegree_X_add_C, mul_one]
    subst heq
    rw [Polynomial.leadingCoeff, Polynomial.leadingCoeff, h2] at h1
    exact h1

theorem delta_X_pow_succ (h : ℤ) (j : ℕ) :
    delta h (X ^ (j + 1)) = ∑ i ∈ Finset.range (j + 1), C (h ^ (j + 1 - i) * ((j + 1).choose i : ℤ)) * X ^ i := by
  rw [delta, X_pow_comp, add_pow, Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero]
  simp only [Nat.cast_one, mul_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C_mul, C_pow, ← C_eq_natCast]
  ring

theorem exists_delta_eq_C_mul_X_pow (h : ℤ) :
    ∀ j : ℕ, ∃ u : ℤ[X], u.natDegree ≤ j + 1 ∧ delta h u = C (((j + 1).factorial : ℤ) * h ^ (j + 1)) * X ^ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hlow : ∀ i < j, ∃ u : ℤ[X], u.natDegree ≤ j ∧ delta h u = C ((j.factorial : ℤ) * h ^ j) * X ^ i := by
      intro i hi
      obtain ⟨u, hu, hdu⟩ := ih i hi
      obtain ⟨c, hc⟩ : ((i + 1).factorial : ℤ) * h ^ (i + 1) ∣ (j.factorial : ℤ) * h ^ j :=
        mul_dvd_mul (Int.natCast_dvd_natCast.mpr (Nat.factorial_dvd_factorial hi)) (pow_dvd_pow h hi)
      refine ⟨C c * u, (natDegree_C_mul_le _ _).trans (hu.trans hi), ?_⟩
      rw [delta_C_mul, hdu, hc, ← mul_assoc, ← C_mul, mul_comm c]
    choose! u hu hdu using hlow
    refine ⟨C ((j.factorial : ℤ) * h ^ j) * X ^ (j + 1)
        - ∑ i ∈ Finset.range j, C (h ^ (j + 1 - i) * ((j + 1).choose i : ℤ)) * u i, ?_, ?_⟩
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le _)
      · refine (natDegree_sum_le_of_forall_le _ _ fun i hi => ?_)
        exact (natDegree_C_mul_le _ _).trans ((hu i (Finset.mem_range.mp hi)).trans (Nat.le_succ j))
    · rw [delta_sub, delta_sum, delta_C_mul, delta_X_pow_succ, Finset.sum_range_succ, Nat.choose_succ_self_right,
        Nat.add_sub_cancel_left, pow_one, mul_add, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun i hi => show delta h (C (h ^ (j + 1 - i) * ((j + 1).choose i : ℤ)) * u i)
          = C ((j.factorial : ℤ) * h ^ j) * (C (h ^ (j + 1 - i) * ((j + 1).choose i : ℤ)) * X ^ i) by
            rw [delta_C_mul, hdu i (Finset.mem_range.mp hi)]; ring]
      rw [add_sub_cancel_left, ← mul_assoc, ← C_mul]
      congr 2
      push_cast [Nat.factorial_succ]
      ring

theorem exists_delta_eq_C_mul (h : ℤ) (n : ℕ) (w : ℤ[X]) (hw : w.natDegree < n) :
    ∃ u : ℤ[X], u.natDegree ≤ n ∧ delta h u = C ((n.factorial : ℤ) * h ^ n) * w := by
  classical
  have hw' : w = ∑ j ∈ Finset.range n, C (w.coeff j) * X ^ j := w.as_sum_range_C_mul_X_pow' hw
  choose u hu hdu using exists_delta_eq_C_mul_X_pow h
  refine ⟨∑ j ∈ Finset.range n, C (w.coeff j * ((n.factorial / (j + 1).factorial : ℕ) : ℤ) * h ^ (n - (j + 1))) * u j, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    exact (natDegree_C_mul_le _ _).trans ((hu j).trans (by have := Finset.mem_range.mp hj; omega))
  · rw [delta_sum]
    conv_rhs => rw [hw', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j + 1 ≤ n := Finset.mem_range.mp hj
    rw [delta_C_mul, hdu j, ← mul_assoc, ← C_mul, ← mul_assoc (C _) (C _) (X ^ j), ← C_mul]
    congr 2
    have hfac : ((n.factorial / (j + 1).factorial : ℕ) : ℤ) * ((j + 1).factorial : ℤ) = (n.factorial : ℤ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.factorial_dvd_factorial hjn)]
    have hpow : (h : ℤ) ^ (n - (j + 1)) * h ^ (j + 1) = h ^ n := by rw [← pow_add, Nat.sub_add_cancel hjn]
    linear_combination (w.coeff j * h ^ (n - (j + 1)) * h ^ (j + 1)) * hfac + (w.coeff j * (n.factorial : ℤ)) * hpow

theorem exists_delta_eq_of_prime_mul (h : ℤ) (n : ℕ) {p : ℕ} (hp : p.Prime) (hn : n < p) (hph : ¬ (p : ℤ) ∣ h)
    (v u : ℤ[X]) (hv : v.natDegree ≤ n) (hu : u.natDegree ≤ n) (he : delta h u = C (p : ℤ) * v) :
    ∃ u' : ℤ[X], u'.natDegree ≤ n ∧ delta h u' = v := by

  have hvn : v.coeff n = 0 := by
    have := coeff_delta_eq_zero h hu
    rw [he, coeff_C_mul, mul_eq_zero] at this
    exact this.resolve_left (by exact_mod_cast hp.ne_zero)
  rcases eq_or_ne v 0 with rfl | hv0
  · exact ⟨0, by simp, by simp [delta]⟩
  have hvlt : v.natDegree < n := by
    refine lt_of_le_of_ne hv fun heq => ?_
    exact (leadingCoeff_ne_zero.mpr hv0) (by rw [Polynomial.leadingCoeff, heq, hvn])
  obtain ⟨u₂, hu₂, he₂⟩ := exists_delta_eq_C_mul h n v hvlt

  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hcop1 : IsCoprime (p : ℤ) (n.factorial : ℤ) :=
    (Prime.coprime_iff_not_dvd hpZ).mpr (by rw [Int.natCast_dvd_natCast]; exact mt hp.dvd_factorial.mp (by omega))
  have hcop : IsCoprime (p : ℤ) ((n.factorial : ℤ) * h ^ n) :=
    hcop1.mul_right (IsCoprime.pow_right ((Prime.coprime_iff_not_dvd hpZ).mpr hph))
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨C a * u + C b * u₂, ?_, ?_⟩
  · exact (natDegree_add_le _ _).trans (max_le ((natDegree_C_mul_le _ _).trans hu) ((natDegree_C_mul_le _ _).trans hu₂))
  · rw [delta_add, delta_C_mul, delta_C_mul, he, he₂, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul, ← add_mul, ← C_add, hab, C_1, one_mul]

end SaturationAux

end HeckeEis

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binarySubst binarySubst_X binaryFormRepSL binaryFormRepSL_apply_coe"
p2m_open "HeckeEis"

open MvPolynomial Polynomial UnipotentFixedAux SaturationAux
open scoped MatrixGroups

namespace SaturationAux

variable {n : ℕ}

noncomputable def rehom (n : ℕ) (U : ℤ[X]) : MvPolynomial (Fin 2) ℤ :=
  ∑ j ∈ Finset.range (n + 1), MvPolynomial.monomial (expo n j) (U.coeff j)

theorem rehom_mem (n : ℕ) (U : ℤ[X]) : rehom n U ∈ BinaryForm ℤ n := by
  refine Submodule.sum_mem _ fun j hj => (MvPolynomial.mem_homogeneousSubmodule n _).mpr ?_
  exact MvPolynomial.isHomogeneous_monomial _ ((degree_eq_iff _).mpr ⟨j, hj, rfl⟩)

theorem dehom_rehom (n : ℕ) {U : ℤ[X]} (hU : U.natDegree ≤ n) : dehom (rehom n U) = U := by
  rw [rehom, map_sum]
  conv_rhs => rw [U.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hU)]
  exact Finset.sum_congr rfl fun j _ => dehom_monomial j _

theorem dehom_injOn {P Q : MvPolynomial (Fin 2) ℤ} (hP : P ∈ BinaryForm ℤ n) (hQ : Q ∈ BinaryForm ℤ n)
    (h : dehom P = dehom Q) : P = Q := by
  rw [eq_sum_range hP, eq_sum_range hQ]
  refine Finset.sum_congr rfl fun j hj => ?_
  have := congrArg (fun r : ℤ[X] => r.coeff j) h
  simp only [coeff_dehom hP, coeff_dehom hQ, if_pos hj] at this
  rw [this]

theorem dehom_sub_eq_delta (h : ℤ) (u : ↥(BinaryForm ℤ n)) :
    dehom (((binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1) u : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ)
      = delta h (dehom (u : MvPolynomial (Fin 2) ℤ)) := by
  rw [LinearMap.sub_apply, Module.End.one_apply, Submodule.coe_sub, map_sub, binaryFormRepSL_apply_coe,
    dehom_binarySubst_T_zpow, delta, Int.cast_id]

end SaturationAux

theorem SolMain.G2 (n : ℕ) {p : ℕ} (hp : p.Prime) (hn : n < p)
    {h : ℤ} (hph : ¬ (p : ℤ) ∣ h) (v : ↥(BinaryForm ℤ n))
    (hv : (p : ℤ) • v ∈ LinearMap.range (binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1)) :
    v ∈ LinearMap.range (binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1) := by
  obtain ⟨u, hu⟩ := hv

  have hcoe : (((p : ℤ) • v : ↥(BinaryForm ℤ n)) : MvPolynomial (Fin 2) ℤ) = MvPolynomial.C (p : ℤ) * (v : MvPolynomial (Fin 2) ℤ) := by
    first
      | rw [Submodule.coe_smul, MvPolynomial.smul_eq_C_mul]
      | rw [Submodule.coe_smul_of_tower, MvPolynomial.smul_eq_C_mul]
      | (simp only [SetLike.val_smul, Submodule.coe_smul, zsmul_eq_mul, MvPolynomial.smul_eq_C_mul]; simp)
      | simp [MvPolynomial.smul_eq_C_mul, zsmul_eq_mul]
  have hdC : dehom (MvPolynomial.C (p : ℤ) : MvPolynomial (Fin 2) ℤ) = Polynomial.C (p : ℤ) := by
    simp [dehom]
  have he : delta h (dehom (u : MvPolynomial (Fin 2) ℤ)) = Polynomial.C (p : ℤ) * dehom (v : MvPolynomial (Fin 2) ℤ) := by
    rw [← dehom_sub_eq_delta, hu, hcoe, map_mul, hdC]
  obtain ⟨U, hU, hdU⟩ := exists_delta_eq_of_prime_mul h n hp hn hph _ _ (natDegree_dehom_le v.2) (natDegree_dehom_le u.2) he
  refine ⟨⟨rehom n U, rehom_mem n U⟩, Subtype.ext (dehom_injOn (Submodule.coe_mem _) v.2 ?_)⟩
  rw [dehom_sub_eq_delta]
  change delta h (dehom (rehom n U)) = _
  rw [dehom_rehom n hU, hdU]

end HeckeEis

open scoped MatrixGroups in
theorem solution (n : ℕ) {p : ℕ} (hp : p.Prime) (hn : n < p)
    {h : ℤ} (hph : ¬ (p : ℤ) ∣ h) (v : ↥(HeckeEis.BinaryForm ℤ n))
    (hv : (p : ℤ) • v ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1)) :
    v ∈ LinearMap.range (HeckeEis.binaryFormRepSL ℤ n (ModularGroup.T ^ h) - 1) :=
  HeckeEis.SolMain.G2 n hp hn hph v hv

#print axioms solution

end S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem
end P2MW
export P2MW.S_HeckeEis_mem_range_binaryFormRepSL_T_zpow_sub_one_of_prime_smul_mem (solution)
