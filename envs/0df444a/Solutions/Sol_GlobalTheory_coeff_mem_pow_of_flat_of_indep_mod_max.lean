-- Prove2me | solution 1 for GlobalTheory.coeff_mem_pow_of_flat_of_indep_mod_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:31:58.405215+00:00
-- url     : https://prove2.me/submissions/9f9d6b13-ed70-4569-80aa-2362e6c33860

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolynomialApproxUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open IsLocalRing TensorProduct
namespace GlobalTheory
open IsLocalRing TensorProduct in
private lemma mem_ideal_of_sum_mul_mem_of_independent_mod_max {A : Type} [CommRing A] [IsLocalRing A] {κ : Type} [Fintype κ] :
    ∀ (d : ℕ) (C : Fin d → κ → A),
      (∀ c : Fin d → A, (∀ l, ∑ i, c i * C i l ∈ maximalIdeal A) → ∀ i, c i ∈ maximalIdeal A) →
      ∀ (I : Ideal A) (b : Fin d → A), (∀ l, ∑ i, b i * C i l ∈ I) → ∀ i, b i ∈ I := by
  intro d
  induction d with
  | zero => intro C _ I b _ i; exact i.elim0
  | succ d ih =>
    intro C hC I b hb
    have h0 : ∃ l0, C 0 l0 ∉ maximalIdeal A := by
      by_contra h
      push_neg at h
      have := hC (Pi.single 0 1) (fun l => by
        simpa [Fin.sum_univ_succ, Pi.single_apply] using h l) 0
      simp at this
    obtain ⟨l0, hl0⟩ := h0
    set u := C 0 l0 with hu
    have hunit : IsUnit u := (IsLocalRing.mem_maximalIdeal _).not.mp hl0 |> not_not.mp
    let C' : Fin d → κ → A := fun i l => u * C i.succ l - C i.succ l0 * C 0 l
    have hC' : ∀ c : Fin d → A, (∀ l, ∑ i, c i * C' i l ∈ maximalIdeal A) → ∀ i, c i ∈ maximalIdeal A := by
      intro c hc i
      have key := hC (Fin.cons (-(∑ j, c j * C j.succ l0)) (fun j => u * c j)) (fun l => by
        convert hc l using 1
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, C']
        rw [show ∑ i, c i * (u * C i.succ l - C i.succ l0 * C 0 l)
            = ∑ i, u * c i * C i.succ l - (∑ i, c i * C i.succ l0) * C 0 l by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)]
        ring) i.succ
      simp only [Fin.cons_succ] at key
      exact ((Ideal.IsPrime.mem_or_mem inferInstance key).resolve_left hl0)
    have hb' := ih C' hC' I (fun i => b i.succ) (fun l => by
      have e : ∑ i, b i.succ * C' i l = u * (∑ i, b i * C i l) - (∑ i, b i * C i l0) * C 0 l := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
        simp only [C']
        rw [show ∑ i : Fin d, b i.succ * (u * C i.succ l - C i.succ l0 * C 0 l)
            = u * ∑ i : Fin d, b i.succ * C i.succ l - (∑ i : Fin d, b i.succ * C i.succ l0) * C 0 l by
          rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)]
        ring
      rw [e]
      exact I.sub_mem (I.mul_mem_left _ (hb l)) (I.mul_mem_right _ (hb l0)))
    intro i
    refine Fin.cases ?_ (fun j => hb' j) i
    have h1 : b 0 * u ∈ I := by
      have := hb l0
      rw [Fin.sum_univ_succ] at this
      have h2 : ∑ i : Fin d, b i.succ * C i.succ l0 ∈ I :=
        I.sum_mem (fun j _ => I.mul_mem_right _ (hb' j))
      simpa [hu] using I.sub_mem this h2
    obtain ⟨v, hv⟩ := hunit
    have := I.mul_mem_right (↑v⁻¹ : A) h1
    rwa [← hv, mul_assoc, Units.mul_inv, mul_one] at this
end GlobalTheory
end

set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory
open IsLocalRing TensorProduct
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] (φ : A →+* R), φ.Flat → (maximalIdeal A).map φ = maximalIdeal R → ∀ (θ : R) (q : Polynomial A), q.Monic → (q.map φ).eval θ = 0 → (∀ (n : ℕ) (r : R), ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R ^ n) → (∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A) → ∀ (n : ℕ) (P : Polynomial A), P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R ^ n → ∀ i, P.coeff i ∈ maximalIdeal A ^ n := by
  intro A R _ _ _ _ φ hflat hmax θ q _ _ _ hind n P hdeg hP i
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hflat
  have hsm : ∀ (a : A) (r : R), a • r = φ a * r := fun a r => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  have hφm : ∀ a ∈ maximalIdeal A, φ a ∈ maximalIdeal R := fun a ha => hmax ▸ Ideal.mem_map_of_mem φ ha
  by_cases hi : i < q.natDegree
  swap
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (not_lt.mp hi))]
    exact Ideal.zero_mem _
  set d := q.natDegree with hd
  rw [← hmax, ← Ideal.map_pow] at hP
  obtain ⟨K, y, g, hg⟩ := Submodule.mem_span_set'.mp hP
  have hb : ∀ k, ∃ b ∈ maximalIdeal A ^ n, φ b = g k := fun k => (g k).2
  choose b hbI hbg using hb
  have hev : (P.map φ).eval θ = ∑ j : Fin d, φ (P.coeff j) * θ ^ (j : ℕ) := by
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (Polynomial.natDegree_map_le) hdeg),
      Finset.sum_range]
    simp [Polynomial.coeff_map]
  have hsum : ∑ k, φ (b k) * y k = (P.map φ).eval θ := by
    rw [← hg]
    exact Finset.sum_congr rfl (fun k _ => by rw [hbg, smul_eq_mul, mul_comm])
  let v : Fin d ⊕ Fin K → R := Sum.elim (fun j => θ ^ (j : ℕ)) y
  let f : Fin d ⊕ Fin K → A := Sum.elim (fun j => P.coeff j) (fun k => - b k)
  have hx : Fintype.linearCombination A v f = 0 := by
    rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
    simp only [v, f, Sum.elim_inl, Sum.elim_inr, hsm, map_neg, neg_mul, Finset.sum_neg_distrib]
    rw [hsum, hev]
    ring
  obtain ⟨k, a, z, hxz, haf⟩ := Module.Flat.exists_factorization_of_apply_eq_zero_of_free hx
  let e : Fin d ⊕ Fin K → Fin d ⊕ Fin K → A := fun x x' => if x = x' then 1 else 0
  let C : Fin d → Fin k → A := fun j l => a (e (Sum.inl j)) l
  let w : Fin k → R := fun l => z (Finsupp.single l 1)
  have hz : ∀ x : Fin k →₀ A, z x = ∑ l, φ (x l) * w l := by
    intro x
    conv_lhs => rw [← Finsupp.univ_sum_single x]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun l _ => by rw [← Finsupp.smul_single_one, map_smul, hsm])
  have hθ : ∀ j : Fin d, θ ^ (j : ℕ) = ∑ l, φ (C j l) * w l := by
    intro j
    have h1 : θ ^ (j : ℕ) = Fintype.linearCombination A v (e (Sum.inl j)) := by
      rw [Fintype.linearCombination_apply]
      simp [e, v]
    rw [h1, hxz, LinearMap.comp_apply, hz]
  have haf' : ∀ l, ∑ j : Fin d, P.coeff (j : ℕ) * C j l = ∑ k', b k' * a (e (Sum.inr k')) l := by
    intro l
    have h2 := DFunLike.congr_fun haf l
    rw [LinearMap.pi_apply_eq_sum_univ a f, Finsupp.finset_sum_apply, Fintype.sum_sum_type] at h2
    simp only [f, e, C, Sum.elim_inl, Sum.elim_inr, Finsupp.smul_apply, smul_eq_mul, neg_mul,
      Finset.sum_neg_distrib, Finsupp.coe_zero, Pi.zero_apply] at h2
    linear_combination h2
  have hCm : ∀ c : Fin d → A, (∀ l, ∑ j, c j * C j l ∈ maximalIdeal A) → ∀ j, c j ∈ maximalIdeal A := by
    intro c hc j
    let Q : Polynomial A := ∑ j' : Fin d, Polynomial.C (c j') * Polynomial.X ^ (j' : ℕ)
    have hQdeg : Q.natDegree < d := by
      by_cases hQ : Q = 0
      · rw [hQ, Polynomial.natDegree_zero]; exact lt_of_le_of_lt (Nat.zero_le _) j.2
      · exact (Polynomial.natDegree_lt_iff_degree_lt hQ).mpr (Polynomial.degree_sum_fin_lt c)
    have hQc : Q.coeff j = c j := by
      simp [Q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Fin.val_inj]
    have hQe : (Q.map φ).eval θ = ∑ l, φ (∑ j', c j' * C j' l) * w l := by
      simp only [Q, Polynomial.map_sum, Polynomial.eval_finset_sum, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_X, hθ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j' _ => by rw [map_mul]; ring)
    rw [← hQc]
    refine hind Q hQdeg ?_ j
    rw [hQe]
    exact Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_right _ _ (hφm _ (hc l)))
  exact mem_ideal_of_sum_mul_mem_of_independent_mod_max d C hCm (maximalIdeal A ^ n) (fun j => P.coeff j)
    (fun l => by
      rw [haf' l]
      exact Ideal.sum_mem _ (fun k' _ => Ideal.mul_mem_right _ _ (hbI k'))) ⟨i, hi⟩
end _root_.GlobalTheory
end GlobalTheory
