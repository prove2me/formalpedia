-- Prove2me | solution 1 for OAI.PiExponent.logJetSurjective_truncatedLogMatrix
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T06:36:44.255393+00:00
-- url     : https://prove2.me/submissions/086934fa-17eb-4322-8b50-1a516d37e557

import Definitions.Def_PiExponent_FiniteMinorComparison
import Mathlib

open scoped BigOperators
open OAI.PiExponent

namespace PXJet

noncomputable def Φ (m : ℕ) : MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C Polynomial.X) (fun i => MvPolynomial.X i))

lemma ev_zero {m : ℕ} (s : ℕ) (b : Fin m → ℕ) :
    InterpolationMatrix.exponentVector (Fin.cases s b : Fin (m + 1) → ℕ) 0 = s := rfl

lemma ev_succ {m : ℕ} (s : ℕ) (b : Fin m → ℕ) (i : Fin m) :
    InterpolationMatrix.exponentVector (Fin.cases s b : Fin (m + 1) → ℕ) i.succ = b i := rfl

lemma Φ_monomial {m : ℕ} (e : Fin (m + 1) →₀ ℕ) (c : ℂ) :
    Φ m (MvPolynomial.monomial e c) =
      MvPolynomial.monomial (InterpolationMatrix.exponentVector (fun i => e i.succ))
        (Polynomial.monomial (e 0) c) := by
  rw [Φ, MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [← MvPolynomial.C_pow, InterpolationMatrix.exponentVector,
    Finsupp.coe_equivFunOnFinite_symm, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_eq]
  rw [← mul_assoc, ← MvPolynomial.C_mul, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_Φ {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℂ) (s : ℕ) (b : Fin m → ℕ) :
    MvPolynomial.coeff (InterpolationMatrix.exponentVector (Fin.cases s b)) P =
      ((Φ m P).coeff (InterpolationMatrix.exponentVector b)).coeff s := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [Φ_monomial, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
    by_cases he : e = InterpolationMatrix.exponentVector (Fin.cases s b)
    · subst he
      rw [if_pos rfl, if_pos, Polynomial.coeff_monomial, if_pos (ev_zero s b)]
      ext i; rfl
    · rw [if_neg he]
      by_cases ht : InterpolationMatrix.exponentVector (fun i => e i.succ) = InterpolationMatrix.exponentVector b
      · rw [if_pos ht, Polynomial.coeff_monomial, if_neg]
        intro h0
        apply he
        ext i
        refine Fin.cases ?_ (fun i => ?_) i
        · exact h0
        · have := congrArg (fun f => f i) ht
          simpa [InterpolationMatrix.exponentVector] using this
      · rw [if_neg ht]; rfl
  | add p q hp hq =>
    rw [MvPolynomial.coeff_add, hp, hq, map_add, MvPolynomial.coeff_add, Polynomial.coeff_add]

lemma Φ_aeval_X0 {m : ℕ} (G : Polynomial ℂ) :
    Φ m (Polynomial.aeval (MvPolynomial.X 0) G) = MvPolynomial.C G := by
  rw [← Polynomial.aeval_algHom_apply, Φ, MvPolynomial.aeval_X, Fin.cases_zero]
  rw [show (MvPolynomial.C Polynomial.X : MvPolynomial (Fin m) (Polynomial ℂ))
      = algebraMap (Polynomial ℂ) (MvPolynomial (Fin m) (Polynomial ℂ)) Polynomial.X from rfl,
    Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rfl

theorem jet_general (m : Nat) (c : Fin m → Complex) (G : Fin m → Polynomial Complex)
    (h : Nat) (a : Fin m → Nat) (s : Nat) (b : Fin m → Nat) :
    (MvPolynomial.aeval
      (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C (c i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (G i)))
      (MvPolynomial.monomial
        (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
    ((MvPolynomial.C ((1 + Polynomial.X) ^ h) *
      ∏ i, (MvPolynomial.C (Polynomial.C (c i) + G i) + MvPolynomial.X i) ^ a i).coeff
      (InterpolationMatrix.exponentVector b)).coeff s := by
  rw [coeff_Φ]
  congr 2
  rw [MvPolynomial.aeval_monomial, map_one, one_mul,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod, Fin.prod_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, ev_zero, ev_succ, map_pow, map_add, map_one,
    Φ_aeval_X0]
  have h0 : Φ m (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
    rw [Φ, MvPolynomial.aeval_X, Fin.cases_zero]
  have hs : ∀ i : Fin m, Φ m (MvPolynomial.X i.succ) = MvPolynomial.X i := by
    intro i; rw [Φ, MvPolynomial.aeval_X, Fin.cases_succ]
  have hc : ∀ z : ℂ, Φ m (MvPolynomial.C z) = MvPolynomial.C (Polynomial.C z) := by
    intro z; rw [MvPolynomial.algHom_C]; rfl
  simp only [h0, hs, hc]
  rw [← MvPolynomial.C_1, ← map_add, ← map_pow]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  ring

end PXJet

open OAI.PiExponent

lemma LJT_log (T : ℕ) {m : ℕ} :
    Polynomial.aeval (MvPolynomial.X (0 : Fin (m + 1)) : MvPolynomial (Fin (m + 1)) ℂ)
      (InterpolationMatrix.truncatedLog T) =
    ∑ k ∈ Finset.range T, if k = 0 then 0 else
      MvPolynomial.C (((-1 : ℂ) ^ (k + 1)) / (k : ℂ)) * (MvPolynomial.X 0) ^ k := by
  rw [InterpolationMatrix.truncatedLog, PowerSeries.trunc_apply, ← Finset.range_eq_Ico, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.aeval_monomial, PowerSeries.coeff_log]
  split_ifs with hk
  · simp
  · rw [MvPolynomial.algebraMap_eq]
    congr 2
    push_cast
    rfl

theorem solution
    (m K : ℕ) (w0 v0 theta : ℚ) (w : Fin m → ℕ)
    (r : Fin m → ℂ) (H : ℕ)
    (hw0 : 0 < w0) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hw : ∀ i, 0 < w i)
    (hjet : OAI.PiExponent.logJetSurjective m K w0 v0 theta w
      (fun j i => (j.val : ℂ) * r i) H) :
    Function.Surjective
      (OAI.PiExponent.InterpolationMatrix.truncatedLogMatrix K
        (w0 : ℝ) (v0 : ℝ) (theta : ℝ) (fun i => (w i : ℝ)) (H : ℝ) r
        (fun _ => Nat.ceil ((H : ℝ) / (v0 : ℝ)))).mulVecLin := by
  classical
  intro y
  set T := Nat.ceil ((H : ℝ) / (v0 : ℝ)) with hT
  unfold OAI.PiExponent.logJetSurjective at hjet
  let J : Fin K → (Fin (m + 1) →₀ ℕ) → ℂ := fun j d =>
    if hd : (fun i => d i) ∈ strictWeightedSimplex
        (InterpolationMatrix.rowWeights (v0 : ℝ) (theta : ℝ) (fun i => (w i : ℝ))) (H : ℝ)
    then y (j, ⟨_, hd⟩) else 0
  obtain ⟨P, hPsupp, hPcoeff⟩ := hjet J
  have hcs : ∀ f : Fin (m + 1) → ℕ, (Fin.cases (f 0) (fun i => f i.succ) : Fin (m + 1) → ℕ) = f :=
    fun f => funext fun i => by refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
  have hev : ∀ f : Fin (m + 1) → ℕ, (fun i => InterpolationMatrix.exponentVector f i) = f :=
    fun f => rfl
  have hw0' : (0 : ℝ) < (w0 : ℝ) := by exact_mod_cast hw0
  -- support of P lies in the column simplex
  have hcol : ∀ d ∈ P.support, (fun i => d i) ∈ realWeightedSimplex
      (InterpolationMatrix.columnWeights (w0 : ℝ) (fun i => (w i : ℝ))) (H : ℝ) := by
    intro d hd
    have hb := hPsupp d hd
    have hsum : ∑ i, InterpolationMatrix.columnWeights (w0 : ℝ) (fun i => (w i : ℝ)) i * (d i : ℝ)
        ≤ (H : ℝ) := by
      rw [Fin.sum_univ_succ]; simpa [InterpolationMatrix.columnWeights] using hb
    have hpos : ∀ i, 0 < InterpolationMatrix.columnWeights (w0 : ℝ) (fun i => (w i : ℝ)) i := by
      intro i; refine Fin.cases ?_ (fun i => ?_) i
      · simpa [InterpolationMatrix.columnWeights] using hw0'
      · simp [InterpolationMatrix.columnWeights, hw i]
    simp only [realWeightedSimplex, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun i => Nat.lt_succ_of_le (Nat.le_floor ?_), hsum⟩
    rw [le_div_iff₀ (hpos i), mul_comm]
    refine le_trans ?_ hsum
    exact Finset.single_le_sum (f := fun i =>
      InterpolationMatrix.columnWeights (w0 : ℝ) (fun i => (w i : ℝ)) i * (d i : ℝ))
      (fun i _ => mul_nonneg (hpos i).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  -- P as a sum over columns
  have hPeq : P = ∑ c : InterpolationMatrix.Column (w0 : ℝ) (fun i => (w i : ℝ)) (H : ℝ),
      MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1)
        (P.coeff (InterpolationMatrix.exponentVector c.1)) := by
    ext d
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    by_cases hd : d ∈ P.support
    · rw [Finset.sum_eq_single ⟨_, hcol d hd⟩]
      · have e : InterpolationMatrix.exponentVector (fun i => d i) = d :=
          Finsupp.equivFunOnFinite_symm_coe d
        show _ = if InterpolationMatrix.exponentVector (fun i => d i) = d then
          P.coeff (InterpolationMatrix.exponentVector (fun i => d i)) else 0
        rw [e, if_pos rfl]
      · intro c _ hc
        rw [if_neg]
        intro h
        apply hc
        apply Subtype.ext
        show c.1 = fun i => d i
        subst h; rfl
      · simp
    · rw [MvPolynomial.notMem_support_iff.mp hd]
      refine (Finset.sum_eq_zero fun c _ => ?_).symm
      split_ifs with h
      · rw [h]; exact MvPolynomial.notMem_support_iff.mp hd
      · rfl
  refine ⟨fun c => P.coeff (InterpolationMatrix.exponentVector c.1), ?_⟩
  refine funext fun ρ => ?_
  obtain ⟨j, a, ha⟩ := ρ
  have hrow : (v0 : ℝ) * ((InterpolationMatrix.exponentVector a) 0 : ℝ) +
      (∑ i : Fin m, ((w i : ℝ) / (theta : ℝ)) * ((InterpolationMatrix.exponentVector a) i.succ : ℝ))
        < (H : ℝ) := by
    have := (Finset.mem_filter.mp ha).2
    rw [Fin.sum_univ_succ] at this
    simp only [InterpolationMatrix.rowWeights, Fin.cases_zero, Fin.cases_succ] at this
    exact this
  have key := hPcoeff j (InterpolationMatrix.exponentVector a) hrow
  have hJ : J j (InterpolationMatrix.exponentVector a) = y (j, ⟨a, ha⟩) := by
    exact dif_pos ha
  have main : (InterpolationMatrix.truncatedLogMatrix K (w0 : ℝ) (v0 : ℝ) (theta : ℝ)
      (fun i => (w i : ℝ)) (H : ℝ) r (fun _ => T)).mulVecLin
      (fun c => P.coeff (InterpolationMatrix.exponentVector c.1)) (j, ⟨a, ha⟩) =
      (MvPolynomial.aeval (Fin.cases (1 + MvPolynomial.X 0)
        (fun i => MvPolynomial.C ((j.val : ℂ) * r i) + MvPolynomial.X i.succ +
          Polynomial.aeval (MvPolynomial.X 0) (InterpolationMatrix.truncatedLog T))) P).coeff
        (InterpolationMatrix.exponentVector a) := by
      rw [Matrix.mulVecLin_apply]
      simp only [Matrix.mulVec, dotProduct, InterpolationMatrix.truncatedLogMatrix,
        InterpolationMatrix.matrix]
      conv_rhs => rw [hPeq]
      rw [map_sum, MvPolynomial.coeff_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hj := PXJet.jet_general m (fun i => (j.val : ℂ) * r i)
        (fun i => InterpolationMatrix.truncatedLog T) (c.1 0) (fun i => c.1 i.succ) (a 0)
        (fun i => a i.succ)
      rw [hcs, hcs] at hj
      rw [InterpolationMatrix.entry, InterpolationMatrix.monomialImage, ← hj,
        show MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1)
          (P.coeff (InterpolationMatrix.exponentVector c.1)) =
          P.coeff (InterpolationMatrix.exponentVector c.1) •
            MvPolynomial.monomial (InterpolationMatrix.exponentVector c.1) (1 : ℂ) by
          rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one],
        map_smul, MvPolynomial.coeff_smul, smul_eq_mul]
      simp only [MvPolynomial.aeval_monomial, map_one, one_mul]
      exact mul_comm _ _

  rw [main, LJT_log, ← hJ]
  exact key

