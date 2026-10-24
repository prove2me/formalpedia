-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.finite_of_integral_coordinates_over_repair6
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T16:51:52.547772+00:00
-- url     : https://prove2.me/submissions/0d497c63-621e-4762-9cb0-2aa4ec8dc82f

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

section

open MvPolynomial

namespace PiL6

theorem fin_int {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hcoords : ∀ i : Fin d,
      IsIntegral A (MvPolynomial.X i : MvPolynomial (Fin d) Complex)) :
    Module.Finite A (MvPolynomial (Fin d) Complex) := by
  have htop : Algebra.adjoin A (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ)) = ⊤ := by
    rw [eq_top_iff]
    intro p _
    have hp : p ∈ Algebra.adjoin ℂ (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ)) := by
      rw [MvPolynomial.adjoin_range_X]; trivial
    have hle : Algebra.adjoin ℂ (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ)) ≤
        (Algebra.adjoin A (Set.range (X : Fin d → MvPolynomial (Fin d) ℂ))).restrictScalars ℂ :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle hp
  have hfg := fg_adjoin_of_finite (Set.finite_range (X : Fin d → MvPolynomial (Fin d) ℂ))
    (R := A) (by rintro _ ⟨i, rfl⟩; exact hcoords i)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

theorem coord_dep {d : Nat} (I : Ideal (MvPolynomial (Fin d) ℂ))
    [Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ I)] (i : Fin d) :
    ∃ K : Nat, ∃ c : Fin (K + 1) → ℂ,
      (∃ n : Fin (K + 1), c n ≠ 0) ∧
      (∑ n : Fin (K + 1), MvPolynomial.C (c n) *
        (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ (n : Nat)) ∈ I := by
  set K := Module.finrank ℂ (MvPolynomial (Fin d) ℂ ⧸ I)
  let v : Fin (K + 1) → MvPolynomial (Fin d) ℂ ⧸ I := fun n => Ideal.Quotient.mkₐ ℂ I (X i ^ (n : ℕ))
  have hnli : ¬ LinearIndependent ℂ v := by
    intro h
    have := h.fintype_card_le_finrank
    simp [K] at this
  obtain ⟨g, hg, n, hn⟩ := Fintype.not_linearIndependent_iff.1 hnli
  refine ⟨K, g, ⟨n, hn⟩, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : Ideal.Quotient.mk I (∑ n : Fin (K + 1), C (g n) * X i ^ (n : ℕ)) = ∑ n, g n • v n := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.C_mul', ← Ideal.Quotient.mkₐ_eq_mk ℂ, map_smul]
  rw [this, hg]

theorem mono_quot (d : Nat) (N : Fin d → Nat) (hN : ∀ i, 0 < N i) : Module.Finite ℂ (MvPolynomial (Fin d) ℂ ⧸ Ideal.span (Set.range (fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N i))) := by
  set J := Ideal.span (Set.range (fun i : Fin d => (MvPolynomial.X i : MvPolynomial (Fin d) ℂ) ^ N i))
  let f := Ideal.Quotient.mkₐ ℂ J
  have htop : Algebra.adjoin ℂ (f '' Set.range (X : Fin d → MvPolynomial (Fin d) ℂ)) = ⊤ := by
    rw [Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top f).2 (Ideal.Quotient.mkₐ_surjective ℂ J)
  have hfg := fg_adjoin_of_finite ((Set.finite_range (X : Fin d → MvPolynomial (Fin d) ℂ)).image f)
    (R := ℂ) (by
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      refine IsIntegral.of_pow (hN i) ?_
      have : f (X i) ^ N i = 0 := by
        rw [← map_pow, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span ⟨i, rfl⟩
      rw [this]; exact isIntegral_zero)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

theorem const_zero {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (i : Fin d) (q : Polynomial ℂ)
    (hqI : Polynomial.aeval (MvPolynomial.X i) q ∈ Ideal.span (Set.range p)) :
    q.coeff 0 = 0 := by
  have hle : Ideal.span (Set.range p) ≤ RingHom.ker (MvPolynomial.constantCoeff (R := ℂ) (σ := Fin d)) := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.constantCoeff_eq]
    by_contra h
    have := hp j h
    simp at this
    exact absurd this (by exact_mod_cast hD.ne)
  have := hle hqI
  rw [RingHom.mem_ker, Polynomial.aeval_def, Polynomial.hom_eval₂] at this
  rw [Polynomial.coeff_zero_eq_eval_zero]
  convert this using 1
  simp [Polynomial.eval₂_eq_eval_map]

end PiL6

end

section

open MvPolynomial

namespace PiL7

theorem int_scale {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ)) (D m : Nat) : ∃ S : Nat, 0 < S ∧ ∃ W : Fin d → Nat, (∀ i, 0 < W i) ∧ (∀ i, (S : ℚ) * w i = (W i : ℚ)) ∧ ∀ (i : Fin d) (n : Nat) (q : Fin m → MvPolynomial (Fin d) ℂ), (∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) ((n : ℚ) * w i - (D : ℚ))) → ∀ (j : Fin m) (a : Fin d →₀ Nat), a ∈ (q j).support → (∑ k : Fin d, (a k : ℤ) * (W k : ℤ)) = (n : ℤ) * (W i : ℤ) - ((S * D : Nat) : ℤ) := by
  have hw' : ∀ i, 0 < w i := fun i => by exact_mod_cast hw i
  set S := ∏ i, (w i).den with hSdef
  have hS : 0 < S := Finset.prod_pos fun i _ => (w i).den_pos
  have hW : ∀ i, ∃ W : ℕ, 0 < W ∧ (S : ℚ) * w i = W := by
    intro i
    obtain ⟨k, hk⟩ : (w i).den ∣ S := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hnum : 0 < (w i).num := Rat.num_pos.2 (hw' i)
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    refine ⟨k * (w i).num.toNat, Nat.mul_pos hk0 (by omega), ?_⟩
    rw [hk]
    push_cast
    have e : (((w i).num.toNat : ℕ) : ℚ) = ((w i).num : ℚ) := by
      have := Int.toNat_of_nonneg hnum.le
      exact_mod_cast this
    rw [e]
    have := Rat.mul_den_eq_num (w i)
    calc ((w i).den : ℚ) * k * w i = k * (w i * (w i).den) := by ring
      _ = _ := by rw [this]
  choose W hWpos hWeq using hW
  refine ⟨S, hS, W, hWpos, hWeq, fun i n q hq j a ha => ?_⟩
  have h := hq j (MvPolynomial.mem_support_iff.1 ha)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [nsmul_eq_mul] at h
  have : (∑ k, (a k : ℚ) * (W k : ℚ)) = n * W i - S * D := by
    simp_rw [← hWeq]
    calc ∑ k, (a k : ℚ) * ((S : ℚ) * w k) = S * ∑ k, (a k : ℚ) * w k := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = _ := by rw [h]; ring
  exact_mod_cast this

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem hom_coeffs {d : Nat} (w : Fin d → ℚ) (hw : ∀ i, 0 < (w i : ℝ))
    (D : Nat) (hD : 0 < D)
    (m : Nat) (p : Fin m → MvPolynomial (Fin d) ℂ)
    (hp : ∀ j, MvPolynomial.IsWeightedHomogeneous w (p j) (D : ℚ))
    (f : MvPolynomial (Fin d) ℂ) (E : ℚ)
    (hf : MvPolynomial.IsWeightedHomogeneous w f E)
    (hmem : f ∈ Ideal.span (Set.range p)) :
    ∃ q : Fin m → MvPolynomial (Fin d) ℂ,
      (∀ j, MvPolynomial.IsWeightedHomogeneous w (q j) (E - (D : ℚ))) ∧
      f = ∑ j, q j * p j := by
  classical
  obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.1 hmem
  refine ⟨fun j => weightedHomogeneousComponent w (E - D) (g j),
    fun j => weightedHomogeneousComponent_isWeightedHomogeneous _ _, ?_⟩
  have hdec : ∀ (x : MvPolynomial (Fin d) ℂ) (n : ℚ),
      ((DirectSum.decompose (weightedHomogeneousSubmodule ℂ w) x n : _) : MvPolynomial (Fin d) ℂ) =
        weightedHomogeneousComponent w n x := fun x n => weightedDecomposition.decompose'_apply ℂ w x n
  have key : ∀ j, weightedHomogeneousComponent w E (g j * p j) =
      weightedHomogeneousComponent w (E - D) (g j) * p j := by
    intro j
    have := DirectSum.coe_decompose_mul_add_of_right_mem (weightedHomogeneousSubmodule ℂ w)
      (i := E - D) (a := g j) ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (hp j))
    rw [sub_add_cancel, hdec, hdec] at this
    exact this
  calc f = weightedHomogeneousComponent w E f := hf.weightedHomogeneousComponent_same.symm
    _ = ∑ j, weightedHomogeneousComponent w E (g j * p j) := by rw [← hg, map_sum]
    _ = _ := by simp_rw [key]

theorem coord_pow {d k : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (D : Real) (hD : 0 < D) (g : Fin k → MvPolynomial (Fin d) Complex)
    (hhom : ∀ j, (g j).IsWeightedHomogeneous (fun i => (w i : Real)) D)
    (J : Ideal (MvPolynomial (Fin d) Complex))
    (hspan : Ideal.span (Set.range g) = J)
    (hfinite : Module.Finite Complex ((MvPolynomial (Fin d) Complex) ⧸ J)) :
    ∀ i, ∃ n : Nat, 0 < n ∧ (MvPolynomial.X i : MvPolynomial (Fin d) Complex) ^ n ∈ J := by
  classical
  intro i
  set w' : Fin d → ℝ := fun i => (w i : ℝ) with hw'
  have hJ : J.IsHomogeneous (weightedHomogeneousSubmodule ℂ w') := by
    rw [← hspan]
    apply Ideal.homogeneous_span
    rintro _ ⟨j, rfl⟩
    exact ⟨D, (mem_weightedHomogeneousSubmodule _ _ _ _).2 (hhom j)⟩
  obtain ⟨K, c, ⟨n0, hn0⟩, hmem⟩ := PiL6.coord_dep J i
  have hcomp := weightedHomogeneousComponent_mem_of_mem ℂ w' hJ hmem (((n0 : ℕ) : ℝ) * w' i)
  have hterm : ∀ n : Fin (K + 1), weightedHomogeneousComponent w' (((n0 : ℕ) : ℝ) * w' i)
      (C (c n) * X i ^ (n : ℕ)) = if n0 = n then C (c n) * X i ^ (n : ℕ) else 0 := by
    intro n
    have hh : IsWeightedHomogeneous w' (C (c n) * X i ^ (n : ℕ)) (((n : ℕ) : ℝ) * w' i) := by
      have := (isWeightedHomogeneous_C w' (c n)).mul ((isWeightedHomogeneous_X ℂ w' i).pow (n : ℕ))
      simpa [nsmul_eq_mul] using this
    split_ifs with h
    · subst h; exact hh.weightedHomogeneousComponent_same
    · apply hh.weightedHomogeneousComponent_ne
      intro heq
      apply h
      have hwi : 0 < w' i := hw i
      have : ((n0 : ℕ) : ℝ) = ((n : ℕ) : ℝ) := mul_right_cancel₀ hwi.ne' heq
      exact Fin.ext (by exact_mod_cast this)
  rw [map_sum] at hcomp
  simp_rw [hterm] at hcomp
  rw [Finset.sum_ite_eq] at hcomp
  simp only [Finset.mem_univ, if_true] at hcomp
  have hX : X i ^ (n0 : ℕ) ∈ J := by
    have := J.mul_mem_left (C (c n0)⁻¹) hcomp
    rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hn0, C_1, one_mul] at this
  by_cases hpos : 0 < (n0 : ℕ)
  · exact ⟨n0, hpos, hX⟩
  · refine ⟨1, one_pos, ?_⟩
    have : (n0 : ℕ) = 0 := by omega
    rw [this, pow_zero] at hX
    simpa using J.mul_mem_left (X i) hX

end PiL7

end


open OAI.PiExponent.FormalInterpolation

theorem solution
    {d : Nat} (A : Subalgebra Complex (MvPolynomial (Fin d) Complex))
    (hcoords : ∀ i : Fin d,
      IsIntegral A (MvPolynomial.X i : MvPolynomial (Fin d) Complex)) :
    Module.Finite A (MvPolynomial (Fin d) Complex) := by
  apply PiL6.fin_int <;> assumption
