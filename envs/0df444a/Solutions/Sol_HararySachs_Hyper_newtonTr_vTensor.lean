-- Prove2me | solution 1 for HararySachs.Hyper.newtonTr_vTensor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-13T04:34:40.303203+00:00
-- url     : https://prove2.me/submissions/05bd8082-cc63-4063-bf0b-56e1e2132cf6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators
import Definitions.Def_HararySachs_Hyper_TensorPhi
import Theorems.Thm_HararySachs_Hyper_phiPoly_vTensor_factor
import Theorems.Thm_HararySachs_Hyper_newtonTr_charpolyRev
import Theorems.Thm_HararySachs_Hyper_newtonTr_prod
import Theorems.Thm_HararySachs_Hyper_newtonTr_comp_X_pow
import Theorems.Thm_HararySachs_Hyper_tapplyAll_coeff_zero_congr

open HararySachs.Hyper Finset

namespace VTensorAux

/-! ### Naturality -/

lemma newtonTr_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (Φ : Polynomial R)
    (d : ℕ) : newtonTr (Φ.map f) d = f (newtonTr Φ d) := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    cases d with
    | zero => simp [newtonTr]
    | succ d =>
      rw [newtonTr, newtonTr, map_sub, map_neg, map_mul, map_sum, map_natCast,
        Polynomial.coeff_map]
      congr 1
      refine sum_congr rfl fun j _ => ?_
      rw [map_mul, ih j (by omega), Polynomial.coeff_map]

lemma charpolyRev_map {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (N : Matrix (Fin n) (Fin n) R) : N.charpolyRev.map f = (N.map f).charpolyRev := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

lemma coeff_zero_charpolyRev {n : ℕ} {R : Type*} [CommRing R] (N : Matrix (Fin n) (Fin n) R) :
    N.charpolyRev.coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

/-! ### Scaling the rows by roots of unity -/

/-- the weight `ξ^{Σ_v Ω(v.1) μ(v)}` of a monomial under the row scaling `V_{ij} ↦ ξ^{Ω i} V_{ij}` -/
noncomputable def wt {n : ℕ} (ξ : ℂ) (Ω : Fin n → ℕ) (μ : Fin n × Fin n →₀ ℕ) : ℂ :=
  ξ ^ (μ.sum fun v e => Ω v.1 * e)

/-- the row scaling `V_{ij} ↦ ξ^{Ω i} V_{ij}`, written monomial by monomial -/
noncomputable def sc {n : ℕ} (ξ : ℂ) (Ω : Fin n → ℕ) (q : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ μ ∈ q.support, MvPolynomial.monomial μ (wt ξ Ω μ * MvPolynomial.coeff μ q)

lemma coeff_sc {n : ℕ} (ξ : ℂ) (Ω : Fin n → ℕ) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (ν : Fin n × Fin n →₀ ℕ) :
    MvPolynomial.coeff ν (sc ξ Ω q) = wt ξ Ω ν * MvPolynomial.coeff ν q := by
  classical
  unfold sc
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [MvPolynomial.mem_support_iff, not_not] at h
    rw [h, mul_zero]

lemma eval_sc {n : ℕ} (ξ : ℂ) (Ω : Fin n → ℕ) (q : MvPolynomial (Fin n × Fin n) ℂ)
    (x : Fin n × Fin n → ℂ) :
    MvPolynomial.eval x (sc ξ Ω q) = MvPolynomial.eval (fun v => ξ ^ Ω v.1 * x v) q := by
  conv_rhs => rw [MvPolynomial.eval_eq]
  unfold sc
  rw [map_sum]
  refine sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.eval_monomial]
  unfold wt Finsupp.prod Finsupp.sum
  rw [← prod_pow_eq_pow_sum]
  simp_rw [mul_pow, prod_mul_distrib, ← pow_mul]
  ring

lemma wt_eq_one {n r : ℕ} (ξ : ℂ) (hξ : ξ ^ r = 1) (Ω : Fin n → ℕ) (μ : Fin n × Fin n →₀ ℕ)
    (hμ : ∀ i, r ∣ ∑ j, μ (i, j)) : wt ξ Ω μ = 1 := by
  unfold wt
  have hs : (μ.sum fun v e => Ω v.1 * e) = ∑ i, Ω i * ∑ j, μ (i, j) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
    simp_rw [mul_sum]
  obtain ⟨m, hm⟩ : r ∣ ∑ i, Ω i * ∑ j, μ (i, j) :=
    dvd_sum fun i _ => Dvd.dvd.mul_left (hμ i) _
  rw [hs, hm, pow_mul, hξ, one_pow]

/-! ### Evaluating `tr(V^L)` -/

lemma eval_trPow {n : ℕ} (x : Fin n × Fin n → ℂ) (L : ℕ) :
    MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) (trPow n L)) =
      ((Matrix.of fun i j => x (i, j)) ^ L).trace := by
  set f : AuxPoly n →+* ℂ := (MvPolynomial.eval x).comp (MvPolynomial.map (algebraMap ℚ ℂ))
    with hf
  have hW : f.mapMatrix (Matrix.of fun i j : Fin n => (MvPolynomial.X (i, j) : AuxPoly n)) =
      Matrix.of fun i j => x (i, j) := by
    ext i j; simp [hf]
  set W : Matrix (Fin n) (Fin n) (AuxPoly n) := Matrix.of fun i j => MvPolynomial.X (i, j)
    with hWdef
  have hp : f.mapMatrix (W ^ L) = (f.mapMatrix W) ^ L := map_pow _ _ _
  change f (Matrix.trace (W ^ L)) = _
  rw [← hW, ← hp, Matrix.trace, Matrix.trace, map_sum]
  rfl

end VTensorAux

open VTensorAux in
theorem solution (n k : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ)
    (hres : IsResultant n (fun _ => k - 1) res)
    (A : Fin n → (Fin (k - 1) → Fin n) → ℚ) (d : ℕ) (hd : 1 ≤ d)
    (a : Fin n → Fin (d + 1)) (ha : (∑ i, (a i).val) = d) :
    MvPolynomial.coeff 0
        (tapplyAll (k := k) A a (newtonTr (phiPoly (k := k) (vTensor n k) res) d)) =
      ((k - 1 : ℕ) : ℚ) ^ (n - 1) *
        MvPolynomial.coeff 0 (tapplyAll (k := k) A a (trPow n (d * (k - 1)))) := by
  classical
  have hr1 : 1 ≤ k - 1 := by omega
  -- the primitive root of unity
  have hprim := Complex.isPrimitiveRoot_exp (k - 1) (by omega)
  have hξ : Complex.exp (2 * Real.pi * Complex.I / ((k - 1 : ℕ) : ℂ)) ^ (k - 1) = 1 :=
    hprim.pow_eq_one
  -- abbreviations
  have hΦdef : ∃ Φ, Φ = phiPoly (k := k) (vTensor n k) res := ⟨_, rfl⟩
  obtain ⟨Φ, hΦ⟩ := hΦdef
  rw [← hΦ]
  have hfac := phiPoly_vTensor_factor n k hk hn res hres
  rw [← hΦ] at hfac
  -- Step 1: pointwise, `r · τ_d(Φ_M) = Σ_Ω tr((Ω M)^{rd})`
  have step1 : ∀ x : Fin n × Fin n → ℂ,
      ((k - 1 : ℕ) : ℂ) *
          MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) (newtonTr Φ d)) =
        ∑ Ω : Fin n → Fin (k - 1),
          ((Matrix.diagonal (fun i =>
              Complex.exp (2 * Real.pi * Complex.I / ((k - 1 : ℕ) : ℂ)) ^ (Ω i : ℕ)) *
            Matrix.of fun i j => x (i, j)) ^ ((k - 1) * d)).trace := by
    intro x
    set ψ : AuxPoly n →+* ℂ :=
      (MvPolynomial.eval x).comp (MvPolynomial.map (algebraMap ℚ ℂ)) with hψ
    have hcomp : (Φ.map ψ).comp (Polynomial.X ^ (k - 1)) =
        ∏ Ω : Fin n → Fin (k - 1),
          (Matrix.diagonal (fun i =>
              Complex.exp (2 * Real.pi * Complex.I / ((k - 1 : ℕ) : ℂ)) ^ (Ω i : ℕ)) *
            Matrix.of fun i j => x (i, j)).charpolyRev := by
      have h := congrArg (Polynomial.map (MvPolynomial.eval x)) hfac
      rw [Polynomial.map_comp, Polynomial.map_map, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_prod] at h
      rw [hψ, h]
      refine prod_congr rfl fun Ω _ => ?_
      rw [charpolyRev_map, Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
      congr 2
      · ext i; simp
      · ext i j; simp
    have h0 : (Φ.map ψ).coeff 0 = 1 := by
      have h := congrArg (Polynomial.eval 0) hcomp
      rw [Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
        zero_pow (by omega), Polynomial.eval_prod] at h
      rw [Polynomial.coeff_zero_eq_eval_zero, h]
      exact prod_eq_one fun Ω _ => Matrix.eval_charpolyRev
    have hτ : MvPolynomial.eval x (MvPolynomial.map (algebraMap ℚ ℂ) (newtonTr Φ d)) =
        newtonTr (Φ.map ψ) d := by
      rw [newtonTr_map]; rfl
    rw [hτ, ← newtonTr_comp_X_pow (Φ.map ψ) h0 (k - 1) hr1 d, hcomp,
      newtonTr_prod _ _ (fun Ω _ => coeff_zero_charpolyRev _)]
    refine sum_congr rfl fun Ω _ => ?_
    exact newtonTr_charpolyRev _ _ (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega)))
  -- Step 2: as polynomials over `ℂ`
  set ξ := Complex.exp (2 * Real.pi * Complex.I / ((k - 1 : ℕ) : ℂ)) with hξdef
  have step2 : MvPolynomial.C ((k - 1 : ℕ) : ℂ) *
        MvPolynomial.map (algebraMap ℚ ℂ) (newtonTr Φ d) =
      ∑ Ω : Fin n → Fin (k - 1), sc ξ (fun i => (Ω i : ℕ))
        (MvPolynomial.map (algebraMap ℚ ℂ) (trPow n (d * (k - 1)))) := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, MvPolynomial.eval_C, step1 x, map_sum]
    refine sum_congr rfl fun Ω _ => ?_
    rw [eval_sc, eval_trPow, mul_comm d]
    congr 2
    ext i j
    simp [Matrix.diagonal_mul]
  -- Step 3: coefficients with all row degrees divisible by `r`
  have key : ∀ μ : Fin n × Fin n →₀ ℕ, (∀ i, (k - 1) ∣ ∑ j, μ (i, j)) →
      MvPolynomial.coeff μ (newtonTr Φ d) =
        ((k - 1 : ℕ) : ℚ) ^ (n - 1) * MvPolynomial.coeff μ (trPow n (d * (k - 1))) := by
    intro μ hμ
    have h := congrArg (MvPolynomial.coeff μ) step2
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_sum] at h
    simp_rw [coeff_sc, wt_eq_one ξ hξ _ μ hμ, one_mul] at h
    rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
      nsmul_eq_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_map] at h
    have hr0 : ((k - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show k - 1 ≠ 0 by omega)
    have h' : ((k - 1 : ℕ) : ℚ) * MvPolynomial.coeff μ (newtonTr Φ d) =
        ((k - 1 : ℕ) : ℚ) ^ n * MvPolynomial.coeff μ (trPow n (d * (k - 1))) := by
      apply (algebraMap ℚ ℂ).injective
      rw [map_mul, map_mul, map_pow, map_natCast, h]
      push_cast; ring
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ, mul_comm (((k - 1 : ℕ) : ℚ) ^ m), mul_assoc] at h'
    rw [Nat.add_sub_cancel]
    exact mul_left_cancel₀ hr0 h'
  -- Step 4: only row degrees `r a_i` matter
  refine tapplyAll_coeff_zero_congr A a _ _ _ fun μ hμ => key μ fun i => ?_
  rw [hμ i]
  exact dvd_mul_right _ _
