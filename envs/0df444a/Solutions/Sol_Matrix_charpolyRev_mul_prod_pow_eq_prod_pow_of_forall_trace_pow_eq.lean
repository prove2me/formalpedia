-- Prove2me | solution 1 for Matrix.charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/ac479518-402a-51d0-890c-a7b1239b04b9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq
set_option autoImplicit false

namespace ArtinNewtonProof

open Polynomial Module
p2m_open "PowerSeries~C~X"

section algClosed

variable {E : Type*} [Field E] {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]

theorem trace_pow_restrict_maxGenEigenspace (S : Module.End E W) (μ : E) (n : ℕ) :
    LinearMap.trace E _ ((S ^ n).restrict
      (S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right n) μ)) =
      μ ^ n * (finrank E (S.maxGenEigenspace μ) : E) := by
  have hS : Set.MapsTo S ↑(S.maxGenEigenspace μ) ↑(S.maxGenEigenspace μ) :=
    S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S) μ
  set Sμ : Module.End E (S.maxGenEigenspace μ) := S.restrict hS with hSμ
  have hnil := S.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap μ
  have hpow : ∀ k : ℕ, (S ^ k).restrict
      (S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right k) μ) = Sμ ^ k := by
    intro k
    rw [hSμ, Module.End.pow_restrict k]
  rw [hpow n]
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, one_mul, LinearMap.trace_one]
  | succ k ih =>
    have hcomm : Commute (Sμ ^ k) Sμ := (Commute.refl Sμ).pow_left k
    have hk : Sμ ^ (k + 1) = (Sμ ^ k) ∘ₗ Sμ := by rw [pow_succ]; rfl
    rw [hk, LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent μ hcomm hnil, ih, ← mul_assoc,
      ← pow_succ']

theorem sum_roots_pow_eq_trace_pow [IsAlgClosed E] (S : Module.End E W) (n : ℕ) :
    ((S.charpoly).roots.map (fun z => z ^ n)).sum = LinearMap.trace E W (S ^ n) := by
  classical
  have hind := S.independent_maxGenEigenspace
  have htop := S.iSup_maxGenEigenspace_eq_top
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have h_fin : {μ : E | S.maxGenEigenspace μ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  have hf : ∀ μ : E, Set.MapsTo (S ^ n) ↑(S.maxGenEigenspace μ) ↑(S.maxGenEigenspace μ) :=
    fun μ => S.mapsTo_maxGenEigenspace_of_comm (Commute.refl S |>.pow_right n) μ
  rw [LinearMap.trace_eq_sum_trace_restrict' hds h_fin hf]
  simp_rw [trace_pow_restrict_maxGenEigenspace]
  rw [Finset.sum_multiset_map_count]
  have hset : S.charpoly.roots.toFinset = h_fin.toFinset := by
    ext μ
    rw [Multiset.mem_toFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      mem_roots (S.charpoly_monic).ne_zero, ne_eq, ← Submodule.finrank_eq_zero,
      LinearMap.finrank_maxGenEigenspace_eq, ← ne_eq, ← Nat.pos_iff_ne_zero, rootMultiplicity_pos']
    exact ⟨fun h => ⟨(S.charpoly_monic).ne_zero, h⟩, fun h => h.2⟩
  rw [hset]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [count_roots, ← LinearMap.finrank_maxGenEigenspace_eq, nsmul_eq_mul, mul_comm]

theorem sum_roots_pow_eq_trace_pow_matrix [IsAlgClosed E] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n E) (k : ℕ) :
    ((M.charpoly).roots.map (fun z => z ^ k)).sum = (M ^ k).trace := by
  have h := sum_roots_pow_eq_trace_pow (Matrix.toLin' M) k
  rw [Matrix.charpoly_toLin', ← Matrix.toLin'_pow,
    LinearMap.trace_eq_matrix_trace E (Pi.basisFun E n), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin'] at h
  exact h

end algClosed

section logderiv

variable {E : Type*} [Field E]

theorem mul_add_of_mul {F G S T : E⟦X⟧}
    (hF : F * S = -(d⁄dX E F)) (hG : G * T = -(d⁄dX E G)) :
    (F * G) * (S + T) = -(d⁄dX E (F * G)) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  linear_combination G * hF + F * hG

theorem linear_factor (r : E) :
    (((1 - C r * X : E[X]) : E⟦X⟧)) * PowerSeries.mk (fun k => r ^ (k + 1)) =
      -(d⁄dX E ((1 - C r * X : E[X]) : E⟦X⟧)) := by
  rw [derivative_coe]
  have hd : derivative (1 - C r * X : E[X]) = -C r := by
    simp
  rw [hd]
  have hc : (((1 - C r * X : E[X]) : E⟦X⟧)) = 1 - PowerSeries.C r * PowerSeries.X := by
    simp [Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_X]
  rw [hc]
  ext k
  rw [show ((↑(-C r : E[X])) : E⟦X⟧) = -PowerSeries.C r by simp, neg_neg]
  rw [sub_mul, one_mul, map_sub, coeff_mk, mul_assoc, PowerSeries.coeff_C_mul]
  cases k with
  | zero => simp
  | succ k =>
    rw [PowerSeries.coeff_succ_X_mul, coeff_mk, PowerSeries.coeff_C]
    simp [pow_succ]; ring

theorem multiset_prod (R : Multiset E) :
    (((R.map fun r => (1 - C r * X : E[X])).prod : E[X]) : E⟦X⟧) *
        PowerSeries.mk (fun k => (R.map fun r => r ^ (k + 1)).sum) =
      -(d⁄dX E (((R.map fun r => (1 - C r * X : E[X])).prod : E[X]) : E⟦X⟧)) := by
  induction R using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero, Polynomial.coe_one, one_mul]
    ext k; simp
  | cons r R ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.coe_mul]
    have hmk : PowerSeries.mk (fun k => ((r ::ₘ R).map fun r => r ^ (k + 1)).sum) =
        PowerSeries.mk (fun k => r ^ (k + 1)) + PowerSeries.mk (fun k => (R.map fun r => r ^ (k + 1)).sum) := by
      ext k; simp [Multiset.map_cons, Multiset.sum_cons]
    rw [hmk]
    exact mul_add_of_mul (linear_factor r) ih

theorem reverse_X_sub_C (r : E) : (X - C r : E[X]).reverse = 1 - C r * X := by
  have h1 : (X : E[X]).reverse = 1 := by
    have := reverse_mul_X (1 : E[X])
    rw [one_mul] at this
    rw [this]
    simpa using reverse_C (1 : E)
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, h1, natDegree_X, pow_one, C_neg]
  ring

theorem reverse_multiset_prod (R : Multiset E) :
    ((R.map fun r => (X - C r : E[X])).prod).reverse = (R.map fun r => (1 - C r * X : E[X])).prod := by
  induction R using Multiset.induction_on with
  | empty => simpa using reverse_C (1 : E)
  | cons r R ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      reverse_mul_of_domain, ih, reverse_X_sub_C]

theorem main_algClosed [IsAlgClosed E] {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n E) :
    ((M.charpolyRev : E[X]) : E⟦X⟧) * PowerSeries.mk (fun k => (M ^ (k + 1)).trace) =
      -((Polynomial.derivative M.charpolyRev : E[X]) : E⟦X⟧) := by
  have hsplit : M.charpoly = ((M.charpoly.roots).map fun r => (X - C r : E[X])).prod := by
    have h := (IsAlgClosed.splits M.charpoly).eq_prod_roots
    rwa [M.charpoly_monic.leadingCoeff, C_1, one_mul] at h
  have hrev : M.charpolyRev = ((M.charpoly.roots).map fun r => (1 - C r * X : E[X])).prod := by
    rw [← Matrix.reverse_charpoly, hsplit, reverse_multiset_prod]
    rw [← hsplit]
  have hmk : PowerSeries.mk (fun k => (M ^ (k + 1)).trace) =
      PowerSeries.mk (fun k => ((M.charpoly.roots).map fun r => r ^ (k + 1)).sum) := by
    ext k; rw [coeff_mk, coeff_mk, sum_roots_pow_eq_trace_pow_matrix]
  rw [hmk, hrev, ← derivative_coe]
  exact multiset_prod _

end logderiv

section descent

variable {K : Type*} [Field K]

theorem charpolyRev_map {E : Type*} [Field E] (f : K →+* E) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n K) : (M.map f).charpolyRev = M.charpolyRev.map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, map_sub, Polynomial.coe_mapRingHom]
  split_ifs <;> simp

private theorem _root_.ArtinNewtonProof.main {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n K) :
    ((M.charpolyRev : K[X]) : K⟦X⟧) * PowerSeries.mk (fun k => (M ^ (k + 1)).trace) =
      -((Polynomial.derivative M.charpolyRev : K[X]) : K⟦X⟧) := by
  let E := AlgebraicClosure K
  let f : K →+* E := algebraMap K E
  apply PowerSeries.map_injective f f.injective
  have h := main_algClosed (M.map f)
  rw [charpolyRev_map, Polynomial.derivative_map, Polynomial.polynomial_map_coe,
    Polynomial.polynomial_map_coe] at h
  have hmk : PowerSeries.mk (fun k => ((M.map f) ^ (k + 1)).trace) =
      PowerSeries.map f (PowerSeries.mk (fun k => (M ^ (k + 1)).trace)) := by
    ext k
    rw [coeff_mk, PowerSeries.coeff_map, coeff_mk, ← Matrix.map_pow, ← AddMonoidHom.map_trace]
  rw [hmk, ← map_mul, ← map_neg] at h
  exact h

p2m_export "ArtinNewtonProof" "main"
end descent

end ArtinNewtonProof

namespace ArtinVirtProof

open Polynomial PowerSeries

variable {K : Type*} [Field K]

theorem eq_of_mul_eq_neg_derivative [CharZero K] {F G S : K⟦X⟧}
    (hF : F * S = -(d⁄dX K F)) (hG : G * S = -(d⁄dX K G))
    (h0 : constantCoeff F = constantCoeff G) : F = G := by

  set R := F - G with hR
  have hRS : R * S = -(d⁄dX K R) := by
    simp only [hR, sub_mul, hF, hG, map_sub, neg_sub_neg]; ring
  have hR0 : constantCoeff R = 0 := by simp [hR, h0]
  by_contra hne
  have hRne : R ≠ 0 := sub_ne_zero.mpr hne

  obtain ⟨d, hd, hmin⟩ : ∃ d : ℕ, coeff d R ≠ 0 ∧ ∀ u < d, coeff u R = 0 := by
    classical
    have hex : ∃ d : ℕ, coeff d R ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hRne (PowerSeries.ext fun n => by simpa using hall n)
    refine ⟨Nat.find hex, Nat.find_spec hex, fun u hu => ?_⟩
    have := Nat.find_min hex hu
    simpa using this
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; exact absurd (by simpa using hR0) hd
    · exact h
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩

  have h1 : coeff e (R * S) = 0 := by
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun uv huv => ?_
    have hu : uv.1 ≤ e := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp huv; omega
    rw [hmin uv.1 (by omega), zero_mul]
  have h2 : coeff e (-(d⁄dX K R)) = -(coeff (e + 1) R * (e + 1)) := by
    rw [map_neg, PowerSeries.coeff_derivative]
  rw [hRS] at h1
  rw [h1] at h2
  have h3 : coeff (e + 1) R * (e + 1 : K) = 0 := by
    have := h2.symm; rwa [neg_eq_zero] at this
  rcases mul_eq_zero.mp h3 with h | h
  · exact hd h
  · exact absurd h (by exact_mod_cast Nat.succ_ne_zero e)

theorem mul_add_of_mul {F G S T : K⟦X⟧}
    (hF : F * S = -(d⁄dX K F)) (hG : G * T = -(d⁄dX K G)) :
    (F * G) * (S + T) = -(d⁄dX K (F * G)) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  linear_combination G * hF + F * hG

theorem pow_nsmul_of_mul {F S : K⟦X⟧} (hF : F * S = -(d⁄dX K F)) (n : ℕ) :
    F ^ n * ((n : K⟦X⟧) * S) = -(d⁄dX K (F ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := mul_add_of_mul ih hF
    rw [← pow_succ] at this
    rw [← this]; push_cast; ring

theorem prod_pow_sum_of_mul {α : Type*} (s : Finset α) (F : α → K⟦X⟧) (S : α → K⟦X⟧) (a : α → ℕ)
    (hF : ∀ i ∈ s, F i * S i = -(d⁄dX K (F i))) :
    (∏ i ∈ s, F i ^ a i) * (∑ i ∈ s, (a i : K⟦X⟧) * S i) = -(d⁄dX K (∏ i ∈ s, F i ^ a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact mul_add_of_mul (pow_nsmul_of_mul (hF j (Finset.mem_insert_self j s)) (a j))
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

private theorem _root_.ArtinVirtProof.main [CharZero K] {α β : Type*} [Fintype α] [Fintype β]
    (P : α → K[X]) (a : α → ℕ) (s : α → ℕ → K)
    (Q : β → K[X]) (b : β → ℕ) (t : β → ℕ → K)
    (hP₀ : ∀ i, (P i).coeff 0 = 1) (hQ₀ : ∀ j, (Q j).coeff 0 = 1)
    (hP : ∀ i, ((P i : K[X]) : PowerSeries K) * PowerSeries.mk (s i) =
      -((derivative (P i) : K[X]) : PowerSeries K))
    (hQ : ∀ j, ((Q j : K[X]) : PowerSeries K) * PowerSeries.mk (t j) =
      -((derivative (Q j) : K[X]) : PowerSeries K))
    (h : ∀ k : ℕ, ∑ i, (a i : K) * s i k = ∑ j, (b j : K) * t j k) :
    ∏ i, P i ^ a i = ∏ j, Q j ^ b j := by
  have hPc : ∀ i, ((P i : K[X]) : K⟦X⟧) * PowerSeries.mk (s i) = -(d⁄dX K (P i : K⟦X⟧)) := fun i => by
    rw [derivative_coe]; exact hP i
  have hQc : ∀ j, ((Q j : K[X]) : K⟦X⟧) * PowerSeries.mk (t j) = -(d⁄dX K (Q j : K⟦X⟧)) := fun j => by
    rw [derivative_coe]; exact hQ j
  have h1 := prod_pow_sum_of_mul Finset.univ (fun i => (P i : K⟦X⟧)) (fun i => PowerSeries.mk (s i)) a
    (fun i _ => hPc i)
  have h2 := prod_pow_sum_of_mul Finset.univ (fun j => (Q j : K⟦X⟧)) (fun j => PowerSeries.mk (t j)) b
    (fun j _ => hQc j)
  have hST : (∑ i, (a i : K⟦X⟧) * PowerSeries.mk (s i)) = ∑ j, (b j : K⟦X⟧) * PowerSeries.mk (t j) := by
    ext k
    simp only [map_sum]
    have e1 : ∀ (n : ℕ) (f : ℕ → K), coeff k ((n : K⟦X⟧) * PowerSeries.mk f) = (n : K) * f k := by
      intro n f
      rw [show (n : K⟦X⟧) = PowerSeries.C (n : K) by simp, PowerSeries.coeff_C_mul, coeff_mk]
    simp only [e1]
    exact h k
  rw [hST] at h1
  have hc : constantCoeff (∏ i, (P i : K⟦X⟧) ^ a i) = constantCoeff (∏ j, (Q j : K⟦X⟧) ^ b j) := by
    simp only [map_prod, map_pow]
    have eP : ∀ i, constantCoeff ((P i : K[X]) : K⟦X⟧) = 1 := fun i => by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP₀]
    have eQ : ∀ j, constantCoeff ((Q j : K[X]) : K⟦X⟧) = 1 := fun j => by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hQ₀]
    simp [eP, eQ]
  have heq := eq_of_mul_eq_neg_derivative h1 h2 hc
  apply Polynomial.coe_injective
  simp only [Polynomial.coeToPowerSeries.ringHom_apply.symm, map_prod, map_pow] at heq ⊢
  simpa using heq

p2m_export "ArtinVirtProof" "main"
end ArtinVirtProof

theorem solution
    {K : Type*} [Field K] [CharZero K] {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m K) {k : ℕ} (E : Fin k → Polynomial K) (hE : ∀ i, (E i).coeff 0 = 1)
    (a : Fin k → ℤ)
    (h : ∀ j : ℕ, 0 < j → (M ^ j).trace =
      ∑ i, (a i : K) * PowerSeries.coeff j
        (((-(Polynomial.X * Polynomial.derivative (E i)) : Polynomial K) : PowerSeries K) *
          ((E i : Polynomial K) : PowerSeries K)⁻¹)) :
    M.charpolyRev * ∏ i, E i ^ (-a i).toNat = ∏ i, E i ^ (a i).toNat := by
  classical

  have hM0 : M.charpolyRev.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

  have hEunit : ∀ i, PowerSeries.constantCoeff ((E i : Polynomial K) : PowerSeries K) ≠ 0 := fun i => by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hE i]
    exact one_ne_zero
  let t : Fin k → ℕ → K := fun i j =>
    PowerSeries.coeff j (-(((Polynomial.derivative (E i) : Polynomial K) : PowerSeries K)) *
      ((E i : Polynomial K) : PowerSeries K)⁻¹)
  have hmk : ∀ i, PowerSeries.mk (t i) =
      -(((Polynomial.derivative (E i) : Polynomial K) : PowerSeries K)) * ((E i : Polynomial K) : PowerSeries K)⁻¹ :=
    fun i => PowerSeries.ext fun j => by rw [PowerSeries.coeff_mk]
  have hQ : ∀ i, ((E i : Polynomial K) : PowerSeries K) * PowerSeries.mk (t i) =
      -((Polynomial.derivative (E i) : Polynomial K) : PowerSeries K) := fun i => by
    rw [hmk, neg_mul, mul_neg, mul_left_comm, PowerSeries.mul_inv_cancel _ (hEunit i), mul_one]

  have hshift : ∀ i (j : ℕ), PowerSeries.coeff (j + 1)
      ((((-(Polynomial.X * Polynomial.derivative (E i)) : Polynomial K) : PowerSeries K)) *
        ((E i : Polynomial K) : PowerSeries K)⁻¹) = t i j := fun i j => by
    have e : (((-(Polynomial.X * Polynomial.derivative (E i)) : Polynomial K) : PowerSeries K)) *
        ((E i : Polynomial K) : PowerSeries K)⁻¹ =
        PowerSeries.X * (-(((Polynomial.derivative (E i) : Polynomial K) : PowerSeries K)) *
          ((E i : Polynomial K) : PowerSeries K)⁻¹) := by
      rw [Polynomial.coe_neg, Polynomial.coe_mul, Polynomial.coe_X]
      ring
    rw [e, PowerSeries.coeff_succ_X_mul]
  have h' : ∀ j : ℕ, (M ^ (j + 1)).trace = ∑ i, (a i : K) * t i j := fun j => by
    rw [h (j + 1) (Nat.succ_pos j)]
    exact Finset.sum_congr rfl fun i _ => by rw [hshift]

  have hint : ∀ i, ((a i : ℤ).toNat : K) = (a i : K) + ((-a i).toNat : K) := fun i => by
    have e : ((a i).toNat : ℤ) = a i + ((-a i).toNat : ℤ) := by omega
    exact_mod_cast e
  have key := ArtinVirtProof.main (K := K) (α := Option (Fin k)) (β := Fin k)
    (fun o => o.elim M.charpolyRev fun i => E i) (fun o => o.elim 1 fun i => (-a i).toNat)
    (fun o => o.elim (fun j => (M ^ (j + 1)).trace) fun i => t i)
    E (fun i => (a i).toNat) t
    (fun o => by cases o with | none => exact hM0 | some i => exact hE i) hE
    (fun o => by cases o with | none => exact ArtinNewtonProof.main M | some i => exact hQ i) hQ
    (fun j => by
      rw [Fintype.sum_option]
      simp only [Option.elim, Nat.cast_one, one_mul, h' j, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hint]; ring)
  rw [Fintype.prod_option] at key
  simpa using key

end S_Matrix_charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq
end P2MW
export P2MW.S_Matrix_charpolyRev_mul_prod_pow_eq_prod_pow_of_forall_trace_pow_eq (solution)
