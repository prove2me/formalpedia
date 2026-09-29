-- Prove2me | solution 1 for MvPolynomial.exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e217fdc1-3087-5eb8-8b43-b08293b1c4e1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent

set_option autoImplicit false

open MvPowerSeries

universe u

namespace AutFrob

section ModP

variable (p : ℕ) [Fact p.Prime] {d : ℕ} (Cb : Matrix (Fin d) (Fin d) (ZMod p))

private noncomputable def T :
    (Fin d → MvPolynomial (Fin d) (ZMod p)) →+ (Fin d → MvPolynomial (Fin d) (ZMod p)) where
  toFun v i := ∑ j, MvPolynomial.C (Cb i j) * frobenius (MvPolynomial (Fin d) (ZMod p)) p (v j)
  map_zero' := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private theorem T_apply (v : Fin d → MvPolynomial (Fin d) (ZMod p)) (i : Fin d) :
    T p Cb v i = ∑ j, MvPolynomial.C (Cb i j) * v j ^ p := by
  simp [T, frobenius_def]

private theorem iterate_T_apply (r : ℕ) (v : Fin d → MvPolynomial (Fin d) (ZMod p)) (i : Fin d) :
    (T p Cb)^[r] v i = ∑ j, MvPolynomial.C ((Cb ^ r) i j) * v j ^ (p ^ r) := by
  induction r generalizing i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, Matrix.one_apply, pow_one]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (Ne.symm hj), map_zero, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), if_pos rfl, map_one, one_mul]
  | succ r ih =>
    rw [Function.iterate_succ_apply', T_apply]
    have hfrob : ∀ j : Fin d, ((T p Cb)^[r] v j) ^ p =
        ∑ l, MvPolynomial.C ((Cb ^ r) j l) * v l ^ p ^ (r + 1) := by
      intro j
      rw [ih, ← frobenius_def, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, frobenius_def, frobenius_def, ← map_pow, ZMod.pow_card, ← pow_mul, ← pow_succ]
    simp_rw [hfrob, Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum, ← Matrix.mul_apply, ← pow_succ']

private theorem iterate_T_eq_zero {N : ℕ} (hN : Cb ^ N = 0) (v : Fin d → MvPolynomial (Fin d) (ZMod p)) :
    (T p Cb)^[N] v = 0 := by
  funext i
  rw [iterate_T_apply, hN]
  simp

private theorem algHom_T (ψ : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin d) (ZMod p))
    (v : Fin d → MvPolynomial (Fin d) (ZMod p)) (i : Fin d) :
    ψ (T p Cb v i) = T p Cb (fun j => ψ (v j)) i := by
  simp [T_apply, map_sum, map_mul, map_pow, MvPolynomial.algHom_C]

private theorem algHom_iterate_T (ψ : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin d) (ZMod p))
    (r : ℕ) (v : Fin d → MvPolynomial (Fin d) (ZMod p)) (i : Fin d) :
    ψ ((T p Cb)^[r] v i) = (T p Cb)^[r] (fun j => ψ (v j)) i := by
  induction r generalizing v i with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih,
      show (fun j => ψ (T p Cb v j)) = T p Cb (fun j => ψ (v j)) from funext fun j => algHom_T p Cb ψ v j]

private theorem constantCoeff_iterate_T_X (r : ℕ) (i : Fin d) :
    MvPolynomial.constantCoeff ((T p Cb)^[r] (fun j => MvPolynomial.X j) i) = 0 := by
  rw [iterate_T_apply, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_mul, map_pow, MvPolynomial.constantCoeff_X, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    mul_zero]

private theorem iterate_neg_T (r : ℕ) (v : Fin d → MvPolynomial (Fin d) (ZMod p)) :
    (⇑(-T p Cb))^[r] v = if Even r then (T p Cb)^[r] v else -((T p Cb)^[r] v) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    by_cases hr : Even r
    · rw [if_pos hr, if_neg (Nat.even_add_one.not.2 (not_not.2 hr)), AddMonoidHom.neg_apply]
    · rw [if_neg hr, if_pos (Nat.even_add_one.2 hr), AddMonoidHom.neg_apply, map_neg, neg_neg]

private theorem iterate_neg_T_eq_zero {N : ℕ} (hN : Cb ^ N = 0) (v : Fin d → MvPolynomial (Fin d) (ZMod p)) :
    (⇑(-T p Cb))^[N] v = 0 := by
  rw [iterate_neg_T, iterate_T_eq_zero p Cb hN]
  simp

private theorem algHom_iterate_negT (ψ : MvPolynomial (Fin d) (ZMod p) →ₐ[ZMod p] MvPolynomial (Fin d) (ZMod p))
    (r : ℕ) (v : Fin d → MvPolynomial (Fin d) (ZMod p)) (i : Fin d) :
    ψ ((⇑(-T p Cb))^[r] v i) = (⇑(-T p Cb))^[r] (fun j => ψ (v j)) i := by
  induction r generalizing v i with
  | zero => rfl
  | succ r ih =>
    have hstep : (fun j => ψ ((-T p Cb) v j)) = (-T p Cb) (fun j => ψ (v j)) := by
      funext j
      rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, Pi.neg_apply, Pi.neg_apply, map_neg, algHom_T]
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hstep]

private noncomputable def chiBar (N : ℕ) : Fin d → MvPolynomial (Fin d) (ZMod p) :=
  ∑ r ∈ Finset.range N, (⇑(-T p Cb))^[r] (fun j => MvPolynomial.X j)

private theorem negT_chiBar (N : ℕ) :
    (-T p Cb) (chiBar p Cb N) = ∑ r ∈ Finset.range N, (⇑(-T p Cb))^[r + 1] (fun j => MvPolynomial.X j) := by
  rw [chiBar, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Function.iterate_succ_apply']

private theorem chiBar_sub_negT_chiBar (N : ℕ) :
    chiBar p Cb N - (-T p Cb) (chiBar p Cb N) =
      (fun j => MvPolynomial.X j) - (⇑(-T p Cb))^[N] (fun j => MvPolynomial.X j) := by
  set U := -T p Cb with hU
  induction N with
  | zero => simp [chiBar]
  | succ N ih =>
    have h1 : chiBar p Cb (N + 1) = chiBar p Cb N + (⇑U)^[N] (fun j => MvPolynomial.X j) := by
      rw [chiBar, Finset.sum_range_succ, chiBar, hU]
    rw [h1, map_add, ← Function.iterate_succ_apply' (⇑U)]
    calc chiBar p Cb N + (⇑U)^[N] (fun j => MvPolynomial.X j) -
          (U (chiBar p Cb N) + (⇑U)^[N + 1] (fun j => MvPolynomial.X j))
        = (chiBar p Cb N - U (chiBar p Cb N)) + (⇑U)^[N] (fun j => MvPolynomial.X j) -
            (⇑U)^[N + 1] (fun j => MvPolynomial.X j) := by abel
      _ = (fun j => MvPolynomial.X j) - (⇑U)^[N + 1] (fun j => MvPolynomial.X j) := by rw [ih]; abel

private theorem chiBar_add_T_chiBar {N : ℕ} (hN : Cb ^ N = 0) :
    chiBar p Cb N + T p Cb (chiBar p Cb N) = fun j => MvPolynomial.X j := by
  have h := chiBar_sub_negT_chiBar p Cb N
  rwa [iterate_neg_T_eq_zero p Cb hN, sub_zero, AddMonoidHom.neg_apply, sub_neg_eq_add] at h

variable {Cb}

private theorem bind₁_chiBar_phi {N : ℕ} (hN : Cb ^ N = 0) (i : Fin d) :
    MvPolynomial.bind₁ (chiBar p Cb N)
        (MvPolynomial.X i + ∑ j, MvPolynomial.C (Cb i j) * MvPolynomial.X j ^ p) =
      MvPolynomial.X i := by
  have h := congrFun (chiBar_add_T_chiBar p Cb hN) i
  rw [Pi.add_apply, T_apply] at h
  rw [map_add, MvPolynomial.bind₁_X_right, map_sum]
  simp_rw [map_mul, map_pow, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]
  exact h

private theorem bind₁_phi_chiBar {N : ℕ} (hN : Cb ^ N = 0) (i : Fin d) :
    MvPolynomial.bind₁ (fun j => MvPolynomial.X j + ∑ l, MvPolynomial.C (Cb j l) * MvPolynomial.X l ^ p)
        (chiBar p Cb N i) =
      MvPolynomial.X i := by
  set ψ := MvPolynomial.bind₁ (R := ZMod p)
    (fun j : Fin d => MvPolynomial.X j + ∑ l, MvPolynomial.C (Cb j l) * MvPolynomial.X l ^ p) with hψ

  have hψX : (fun j => ψ (MvPolynomial.X j)) =
      (fun j => MvPolynomial.X j) + -((-T p Cb) (fun j => MvPolynomial.X j)) := by
    funext j
    rw [hψ, MvPolynomial.bind₁_X_right, AddMonoidHom.neg_apply, neg_neg, Pi.add_apply, T_apply]
  have hsum : chiBar p Cb N i = ∑ r ∈ Finset.range N, (⇑(-T p Cb))^[r] (fun j => MvPolynomial.X j) i := by
    rw [chiBar, Finset.sum_apply]
  rw [hsum, map_sum]
  simp_rw [algHom_iterate_negT, hψX, iterate_map_add, iterate_map_neg, Pi.add_apply, Pi.neg_apply,
    ← Function.iterate_succ_apply, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have h := congrFun (chiBar_sub_negT_chiBar p Cb N) i
  rw [iterate_neg_T_eq_zero p Cb hN, sub_zero, negT_chiBar, Pi.sub_apply, chiBar, Finset.sum_apply,
    Finset.sum_apply, sub_eq_add_neg] at h
  exact h

private theorem constantCoeff_chiBar (N : ℕ) (i : Fin d) :
    MvPolynomial.constantCoeff (chiBar p Cb N i) = 0 := by
  rw [chiBar, Finset.sum_apply, map_sum]
  refine Finset.sum_eq_zero fun r _ => ?_
  rw [iterate_neg_T]
  split_ifs
  · exact constantCoeff_iterate_T_X p Cb r i
  · rw [Pi.neg_apply, map_neg, constantCoeff_iterate_T_X, neg_zero]

end ModP

section Lift

variable {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] [Algebra 𝓞 (ZMod p)] {d : ℕ}
  (C : Matrix (Fin d) (Fin d) 𝓞)

private theorem map_phi (j : Fin d) :
    MvPolynomial.map (algebraMap 𝓞 (ZMod p))
        (MvPolynomial.X j + ∑ l, MvPolynomial.C (C j l) * MvPolynomial.X l ^ p) =
      MvPolynomial.X j + ∑ l, MvPolynomial.C ((C.map (algebraMap 𝓞 (ZMod p))) j l) * MvPolynomial.X l ^ p := by
  simp [map_sum, MvPolynomial.map_X, MvPolynomial.map_C, Matrix.map_apply]

private theorem exists_chi (hC : IsNilpotent (C.map (algebraMap 𝓞 (ZMod p)))) :
    ∃ χ : Fin d → MvPolynomial (Fin d) 𝓞, (∀ i, MvPolynomial.constantCoeff (χ i) = 0) ∧
      (∀ i, MvPolynomial.map (algebraMap 𝓞 (ZMod p))
          (MvPolynomial.bind₁ χ (MvPolynomial.X i + ∑ j, MvPolynomial.C (C i j) * MvPolynomial.X j ^ p)) =
        MvPolynomial.X i) ∧
      (∀ i, MvPolynomial.map (algebraMap 𝓞 (ZMod p))
          (MvPolynomial.bind₁ (fun j => MvPolynomial.X j + ∑ l, MvPolynomial.C (C j l) * MvPolynomial.X l ^ p)
            (χ i)) =
        MvPolynomial.X i) := by
  obtain ⟨N, hN⟩ := hC
  have hπs : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _

  choose χ₀ hχ₀ using fun i =>
    MvPolynomial.map_surjective (algebraMap 𝓞 (ZMod p)) hπs (chiBar p (C.map (algebraMap 𝓞 (ZMod p))) N i)
  have hχ : ∀ i, MvPolynomial.map (algebraMap 𝓞 (ZMod p))
      (χ₀ i - MvPolynomial.C (MvPolynomial.constantCoeff (χ₀ i))) = chiBar p (C.map (algebraMap 𝓞 (ZMod p))) N i := by
    intro i
    rw [map_sub, hχ₀, MvPolynomial.map_C, ← MvPolynomial.constantCoeff_map, hχ₀, constantCoeff_chiBar, map_zero,
      sub_zero]
  refine ⟨fun i => χ₀ i - MvPolynomial.C (MvPolynomial.constantCoeff (χ₀ i)), fun i => ?_, fun i => ?_, fun i => ?_⟩
  · rw [map_sub, MvPolynomial.constantCoeff_C, sub_self]
  · rw [MvPolynomial.map_bind₁, map_phi, funext hχ]
    exact bind₁_chiBar_phi p hN i
  · rw [MvPolynomial.map_bind₁, hχ]
    simp_rw [map_phi]
    exact bind₁_phi_chiBar p hN i

private theorem coeff_sub_coeff_mem (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {P Q : MvPolynomial (Fin d) 𝓞}
    (h : MvPolynomial.map (algebraMap 𝓞 (ZMod p)) P = MvPolynomial.map (algebraMap 𝓞 (ZMod p)) Q)
    (m : Fin d →₀ ℕ) : P.coeff m - Q.coeff m ∈ Ideal.span {(p : 𝓞)} := by
  rw [← MvPolynomial.coeff_sub, ← hker, RingHom.mem_ker, ← MvPolynomial.coeff_map, map_sub, h, sub_self,
    MvPolynomial.coeff_zero]

private theorem aeval_coe (χ : Fin d → MvPolynomial (Fin d) 𝓞) (P : MvPolynomial (Fin d) 𝓞) :
    MvPolynomial.aeval (fun j => (χ j : MvPowerSeries (Fin d) 𝓞)) P =
      ((MvPolynomial.aeval χ P : MvPolynomial (Fin d) 𝓞) : MvPowerSeries (Fin d) 𝓞) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply,
      MvPolynomial.algebraMap_eq, MvPolynomial.coe_C]
  | add f g hf hg => rw [map_add, map_add, hf, hg, MvPolynomial.coe_add]
  | mul_X f j hf => rw [map_mul, map_mul, hf, MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.coe_mul]

omit [Fact p.Prime] [Algebra 𝓞 (ZMod p)] in

private theorem coe_phi (i : Fin d) :
    ((MvPolynomial.X i + ∑ j, MvPolynomial.C (C i j) * MvPolynomial.X j ^ p : MvPolynomial (Fin d) 𝓞) :
        MvPowerSeries (Fin d) 𝓞) =
      (MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞) +
        ∑ j, MvPowerSeries.C (C i j) * (MvPowerSeries.X j : MvPowerSeries (Fin d) 𝓞) ^ p := by
  rw [MvPolynomial.coe_add, MvPolynomial.coe_X, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_sum]
  simp only [map_mul, map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_C,
    MvPolynomial.coe_X]

end Lift

end AutFrob

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (C : Matrix (Fin d) (Fin d) 𝓞) (hC : IsNilpotent (C.map (algebraMap 𝓞 (ZMod p)))) :
    ∃ χ : Fin d → MvPolynomial (Fin d) 𝓞, (∀ i, MvPolynomial.constantCoeff (χ i) = 0) ∧
      (∀ (i : Fin d) (m : Fin d →₀ ℕ),
        (subst (fun j => (χ j : MvPowerSeries (Fin d) 𝓞))
            ((MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞) +
              ∑ j, MvPowerSeries.C (C i j) * (MvPowerSeries.X j : MvPowerSeries (Fin d) 𝓞) ^ p)).coeff m -
          (MvPowerSeries.X i : MvPowerSeries (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)}) ∧
      (∀ (i : Fin d) (m : Fin d →₀ ℕ),
        (MvPolynomial.aeval (fun j => (MvPolynomial.X j : MvPolynomial (Fin d) 𝓞) +
            ∑ l, MvPolynomial.C (C j l) * MvPolynomial.X l ^ p) (χ i)).coeff m -
          (MvPolynomial.X i : MvPolynomial (Fin d) 𝓞).coeff m ∈ Ideal.span {(p : 𝓞)}) := by
  obtain ⟨χ, hχ0, hA, hB⟩ := AutFrob.exists_chi p C hC
  refine ⟨χ, hχ0, fun i m => ?_, fun i m => ?_⟩
  · rw [← AutFrob.coe_phi p C i, MvPowerSeries.subst_coe, AutFrob.aeval_coe, MvPolynomial.coeff_coe,
      ← MvPolynomial.coe_X, MvPolynomial.coeff_coe]
    refine AutFrob.coeff_sub_coeff_mem p hker ?_ m
    rw [MvPolynomial.aeval_eq_bind₁, hA i, MvPolynomial.map_X]
  · refine AutFrob.coeff_sub_coeff_mem p hker ?_ m
    rw [MvPolynomial.aeval_eq_bind₁, hB i, MvPolynomial.map_X]

end S_MvPolynomial_exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent
end P2MW
export P2MW.S_MvPolynomial_exists_subst_X_add_sum_mul_X_pow_sub_X_coeff_mem_span_of_isNilpotent (solution)
