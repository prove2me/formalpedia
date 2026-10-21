-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.ordinaryTaylor_coefficient_functionals_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T18:56:35.070832+00:00
-- url     : https://prove2.me/submissions/7c34d876-8489-41d6-832a-db013a3258e3

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open OAI.PiExponent.AdmissibleFormalInterpolation

/-!
# Independence of ordinary multivariate Taylor coefficient functionals

The coefficient functional attached to a centre `c` and an exponent `e` is
`P ↦ [X^e] P(X + c)`.  We show that finitely many such functionals are linearly
independent as soon as the centre–exponent pairs are pairwise distinct.

The proof translates the statement to a polynomial computation.  If a linear
relation held, take a non-zero coefficient at a point `x₀` whose exponent is
maximal (componentwise) among the support, and test the relation on
`P = ∏_i (X_i - c₀_i)^{e₀_i} · ∏_y (X_{i(y)} - c_y(i(y)))^{e_y(i(y))+1}`.
The first factor becomes the monomial `X^{e₀}` after translation by `c₀`, and
every other functional either dies on a high power of a single variable or
misses the support of `X^{e₀}`.  Consequently only the `x₀`-term survives,
contradicting maximality.
-/

noncomputable section

namespace TaylorScratch

abbrev K (m : ℕ) := MvPolynomial (Fin (m + 1)) ℂ

/-- Translation `P ↦ P(X + c)` on multivariate polynomials, as an algebra endomorphism. -/
def shift {m : ℕ} (c : Fin (m + 1) → ℂ) : K m →ₐ[ℂ] K m :=
  MvPolynomial.aeval (fun i => MvPolynomial.C (c i) + MvPolynomial.X i)

@[simp]
lemma shift_X {m : ℕ} (c : Fin (m + 1) → ℂ) (i : Fin (m + 1)) :
    shift c (MvPolynomial.X i) = MvPolynomial.C (c i) + MvPolynomial.X i := by
  simp [shift]

lemma shift_sub_C {m : ℕ} (c : Fin (m + 1) → ℂ) (i : Fin (m + 1)) :
    shift c (MvPolynomial.X i - MvPolynomial.C (c i)) = MvPolynomial.X i := by
  simp [shift]

lemma aeval_shift {m : ℕ} (c d : Fin (m + 1) → ℂ) (Q : K m) :
    MvPolynomial.aeval d (shift c Q) = MvPolynomial.aeval (fun i => d i + c i) Q := by
  have h : (MvPolynomial.aeval d).comp (shift c) = MvPolynomial.aeval (fun i => d i + c i) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [shift, add_comm]
  exact AlgHom.congr_fun h Q

lemma coeff_zero_shift {m : ℕ} (c : Fin (m + 1) → ℂ) (Q : K m) :
    MvPolynomial.coeff 0 (shift c Q) = MvPolynomial.aeval c Q := by
  have h := aeval_shift c (fun _ : Fin (m + 1) => (0 : ℂ)) Q
  simpa [MvPolynomial.constantCoeff_eq] using h

/-- The canonical algebra embedding of polynomials into formal power series (self-scalars). -/
def coeAlg (m : ℕ) : K m →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ where
  toFun := fun P => ↑P
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp
  commutes' := by intro r; simp [MvPowerSeries.algebraMap_apply]

@[simp]
lemma coeAlg_apply {m : ℕ} (P : K m) : coeAlg m P = (P : MvPowerSeries (Fin (m + 1)) ℂ) := rfl

/-- The same translation on multivariate formal power series. -/
def psShift {m : ℕ} (c : Fin (m + 1) → ℂ) :
    K m →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i)

lemma psShift_eq {m : ℕ} (c : Fin (m + 1) → ℂ) :
    psShift c = (coeAlg m).comp (shift c) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [psShift, shift]

lemma coeff_psShift {m : ℕ} (c : Fin (m + 1) → ℂ) (e : Fin (m + 1) →₀ ℕ) (P : K m) :
    MvPowerSeries.coeff e (psShift c P) = MvPolynomial.coeff e (shift c P) := by
  rw [psShift_eq c, AlgHom.comp_apply, coeAlg_apply]
  exact MvPolynomial.coeff_coe (shift c P) e

lemma coeff_X_pow_mul_eq_zero {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (i : σ) (k : ℕ) (Q : MvPolynomial σ R) (e : σ →₀ ℕ) (h : e i < k) :
    MvPolynomial.coeff e (MvPolynomial.X i ^ k * Q) = 0 := by
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul']
  rw [if_neg]
  intro hle
  rw [Finsupp.single_le_iff] at hle
  omega

lemma coeff_eq_zero_of_X_pow_dvd {σ R : Type*} [CommSemiring R] [DecidableEq σ]
    (i : σ) (k : ℕ) {Q : MvPolynomial σ R} (h : MvPolynomial.X i ^ k ∣ Q)
    (e : σ →₀ ℕ) (he : e i < k) : MvPolynomial.coeff e Q = 0 := by
  obtain ⟨Q', rfl⟩ := h
  exact coeff_X_pow_mul_eq_zero i k Q' e he

lemma dvd_shift_prod_of_factor {ι : Type*} [DecidableEq ι] {m : ℕ}
    (T : Finset ι) (f : ι → K m) {y : ι} (hy : y ∈ T)
    (c : Fin (m + 1) → ℂ) (i : Fin (m + 1)) (k : ℕ)
    (hf : shift c (f y) = MvPolynomial.X i ^ k) :
    MvPolynomial.X i ^ k ∣ shift c (∏ z ∈ T, f z) := by
  rw [map_prod (shift c), ← Finset.mul_prod_erase T (fun z => shift c (f z)) hy, hf]
  exact dvd_mul_right _ _

namespace Main


variable {m : ℕ}

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (center : ι → Fin (m + 1) → ℂ) (exponent : ι → (Fin (m + 1) →₀ ℕ))

/-- The polynomial coefficient functional `P ↦ [X^(exponent x)] P(X + center x)`. -/
def polyFn (x : ι) : K m →ₗ[ℂ] ℂ :=
  (MvPolynomial.lcoeff (R := ℂ) (exponent x)).comp (shift (center x)).toLinearMap

omit [Fintype ι] [DecidableEq ι] in
lemma polyFn_apply (x : ι) (P : K m) :
    polyFn center exponent x P = MvPolynomial.coeff (exponent x) (shift (center x) P) := by
  simp [polyFn]

lemma poly_linearIndependent
    (hindex : Function.Injective (fun x => (center x, exponent x))) :
    LinearIndependent ℂ (fun x => polyFn center exponent x) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro l hl x
  by_contra hx
  -- the support of the coefficient family
  set S : Finset ι := Finset.univ.filter (fun y => l y ≠ 0) with hS
  have hxS : x ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ x, hx⟩
  -- a point whose exponent is maximal (w.r.t. the componentwise order) among the support
  have hne : (S.image exponent).Nonempty :=
    ⟨exponent x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩⟩
  obtain ⟨e0, he0mem, he0max⟩ := Finset.exists_maximal (s := S.image exponent) hne
  obtain ⟨x0, hx0S, hx0e⟩ := Finset.mem_image.mp he0mem
  subst hx0e
  have hex0max : ∀ y ∈ S, exponent x0 ≤ exponent y → exponent y = exponent x0 := by
    intro y hy hle
    exact le_antisymm (he0max (Finset.mem_image.mpr ⟨y, hy, rfl⟩) hle) hle
  -- the finitely many indices where we must kill the translate of the other functionals
  set T : Finset ι := (S.erase x0).filter (fun y => center y ≠ center x0) with hT
  have hcoord : ∀ y, center y ≠ center x0 → ∃ i : Fin (m + 1), center x0 i ≠ center y i := by
    intro y hy
    exact Function.ne_iff.mp (fun hh => hy hh.symm)
  let idx : ι → Fin (m + 1) :=
    fun y => if h : center y ≠ center x0 then Classical.choose (hcoord y h) else 0
  have hidx : ∀ y ∈ T, center x0 (idx y) ≠ center y (idx y) := by
    intro y hy
    have hyne : center y ≠ center x0 := (Finset.mem_filter.mp hy).2
    have hidxy : idx y = Classical.choose (hcoord y hyne) := by
      dsimp only [idx]
      exact dif_pos hyne
    rw [hidxy]
    exact Classical.choose_spec (hcoord y hyne)
  -- the test polynomial
  let bfac : ι → K m := fun z =>
    (MvPolynomial.X (idx z) - MvPolynomial.C (center z (idx z))) ^ (exponent z (idx z) + 1)
  set B : K m := ∏ z ∈ T, bfac z with hB_def
  set A : K m :=
    (exponent x0).prod (fun i n => (MvPolynomial.X i - MvPolynomial.C (center x0 i)) ^ n) with hA_def
  set P : K m := A * B with hP_def
  -- the translated leading factor is the monomial of the maximal exponent
  have hAprod : shift (center x0) A =
      (exponent x0).prod (fun i n => (MvPolynomial.X i) ^ n) := by
    rw [hA_def, map_finsuppProd]
    apply Finsupp.prod_congr
    intro i hi
    rw [map_pow, shift_sub_C]
  have hA : shift (center x0) A = MvPolynomial.monomial (exponent x0) 1 := by
    rw [hAprod, MvPolynomial.monomial_eq]
    simp
  have hshiftP : shift (center x0) P =
      MvPolynomial.monomial (exponent x0) 1 * shift (center x0) B := by
    rw [hP_def, map_mul, hA]
  -- B does not vanish at the center x0
  have hBne : MvPolynomial.aeval (center x0) B ≠ 0 := by
    rw [hB_def, map_prod]
    rw [Finset.prod_ne_zero_iff]
    intro y hy
    rw [map_pow]
    have hbase : MvPolynomial.aeval (center x0)
        (MvPolynomial.X (idx y) - MvPolynomial.C (center y (idx y))) =
        center x0 (idx y) - center y (idx y) := by simp
    rw [hbase]
    exact pow_ne_zero _ (sub_ne_zero.mpr (hidx y hy))
  -- hence the x0-functional does not vanish at P
  have hcoeffTop : MvPolynomial.coeff (exponent x0) (shift (center x0) P) =
      MvPolynomial.aeval (center x0) B := by
    rw [hshiftP, MvPolynomial.coeff_monomial_mul']
    rw [if_pos le_rfl, tsub_self, one_mul]
    exact coeff_zero_shift (center x0) B
  have hx0val : polyFn center exponent x0 P ≠ 0 := by
    rw [polyFn_apply, hcoeffTop]
    exact hBne
  -- the translated B is divisible by a large power of one variable
  have hBdvd : ∀ y ∈ T,
      MvPolynomial.X (idx y) ^ (exponent y (idx y) + 1) ∣ shift (center y) B := by
    intro y hy
    rw [hB_def]
    refine dvd_shift_prod_of_factor (y := y) T bfac hy (center y) (idx y)
      (exponent y (idx y) + 1) ?_
    dsimp only [bfac]
    rw [map_pow, shift_sub_C]
  -- functionals with a different center vanish
  have hzero_ne : ∀ y ∈ S, y ≠ x0 → center y ≠ center x0 →
      polyFn center exponent y P = 0 := by
    intro y hyS hyne hcne
    have hyT : y ∈ T := by
      rw [hT, Finset.mem_filter, Finset.mem_erase]
      exact ⟨⟨hyne, hyS⟩, hcne⟩
    rw [polyFn_apply]
    have hPshift : shift (center y) P = shift (center y) A * shift (center y) B := by
      rw [hP_def, map_mul]
    have hdvd : MvPolynomial.X (idx y) ^ (exponent y (idx y) + 1) ∣
        shift (center y) P := by
      rw [hPshift]
      exact dvd_mul_of_dvd_right (hBdvd y hyT) _
    exact coeff_eq_zero_of_X_pow_dvd (idx y) (exponent y (idx y) + 1) hdvd
      (exponent y) (Nat.lt_succ_self _)
  -- functionals with the same center vanish by maximality of the exponent
  have hzero_eq : ∀ y ∈ S.erase x0, center y = center x0 →
      polyFn center exponent y P = 0 := by
    intro y hy hyc
    obtain ⟨hyne, hyS⟩ := Finset.mem_erase.mp hy
    have hval : polyFn center exponent y P =
        MvPolynomial.coeff (exponent y) (shift (center x0) P) := by
      rw [polyFn_apply, hyc]
    rw [hval, hshiftP, MvPolynomial.coeff_monomial_mul']
    rw [if_neg]
    intro hle
    have heq : exponent y = exponent x0 := hex0max y hyS hle
    have hpair : (center x0, exponent x0) = (center y, exponent y) := by
      rw [hyc, heq]
    exact hyne (hindex hpair).symm
  have hkey : ∀ y ∈ S, y ≠ x0 → polyFn center exponent y P = 0 := by
    intro y hyS hyne
    by_cases hc : center y = center x0
    · exact hzero_eq y (Finset.mem_erase.mpr ⟨hyne, hyS⟩) hc
    · exact hzero_ne y hyS hyne hc
  -- evaluate the linear relation at P
  have hrel : ∑ y : ι, l y * polyFn center exponent y P = 0 := by
    have h := LinearMap.congr_fun hl P
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] using h
  have hPzero : ∑ y ∈ S, l y * polyFn center exponent y P = 0 := by
    rw [← hrel, hS, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y hy
    split_ifs with h
    · rfl
    · simp only [not_not] at h
      rw [h, zero_mul]
  have hsum_single : ∑ y ∈ S, l y * polyFn center exponent y P =
      l x0 * polyFn center exponent x0 P := by
    rw [← Finset.sum_erase_add S (fun y => l y * polyFn center exponent y P) hx0S]
    have hzero : ∑ y ∈ S.erase x0, l y * polyFn center exponent y P = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      obtain ⟨hyne, hyS⟩ := Finset.mem_erase.mp hy
      rw [hkey y hyS hyne, mul_zero]
    rw [hzero, zero_add]
  have hmul : l x0 * polyFn center exponent x0 P = 0 := by
    rw [← hsum_single]
    exact hPzero
  have hlx0 : l x0 = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exact absurd h hx0val
  have hx0S' : x0 ∈ Finset.univ.filter (fun y => l y ≠ 0) := by
    rw [← hS]
    exact hx0S
  have hlx0ne : l x0 ≠ 0 := (Finset.mem_filter.mp hx0S').2
  exact hlx0ne hlx0

end Main

end TaylorScratch

open TaylorScratch
open TaylorScratch.Main

theorem solution {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (center : ι → Fin (m + 1) → ℂ) (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (center x, exponent x))) :
    LinearIndependent ℂ
      (fun x => (MvPowerSeries.coeff (exponent x)).comp
        (MvPolynomial.aeval (fun i =>
          MvPowerSeries.C (center x i) + MvPowerSeries.X i)).toLinearMap) := by
  have hli := poly_linearIndependent (m := m) center exponent hindex
  have hfam : (fun x => (MvPowerSeries.coeff (exponent x)).comp
        (MvPolynomial.aeval (fun i =>
          MvPowerSeries.C (center x i) + MvPowerSeries.X i)).toLinearMap)
      = (fun x => polyFn center exponent x) := by
    funext x
    apply LinearMap.ext
    intro Q
    rw [LinearMap.comp_apply]
    change MvPowerSeries.coeff (exponent x)
        ((MvPolynomial.aeval (fun i =>
          MvPowerSeries.C (center x i) + MvPowerSeries.X i)) Q) = (polyFn center exponent x) Q
    rw [show (MvPolynomial.aeval (fun i =>
          MvPowerSeries.C (center x i) + MvPowerSeries.X i)) Q = psShift (center x) Q from rfl,
      coeff_psShift (center x) (exponent x) Q]
    exact (polyFn_apply center exponent x Q).symm
  rw [hfam]
  exact hli
