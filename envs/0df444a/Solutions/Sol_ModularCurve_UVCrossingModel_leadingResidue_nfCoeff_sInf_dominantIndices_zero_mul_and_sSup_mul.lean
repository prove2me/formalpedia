-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1777a66a-d6db-5654-9a42-465e2ff622b7

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Definitions.Def_ModularCurve_UVCrossingInitialForm
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul

set_option autoImplicit false

universe u

set_option autoImplicit false

open Finset BigOperators

namespace AnnulusNF

variable {W : Type*} [CommRing W] (I : Ideal W)

def psum (c : ℕ → W) (π : W) (k N : ℕ) : W := ∑ m ∈ range N, c (k + m) * π ^ m

theorem psum_succ (c : ℕ → W) (π : W) (k N : ℕ) :
    psum c π k (N + 1) = c k + π * psum c π (k + 1) N := by
  unfold psum
  rw [Finset.sum_range_succ', pow_zero, mul_one, add_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pow_succ, show k + (m + 1) = k + 1 + m by omega]
  ring

theorem psum_sub_psum_mem (c : ℕ → W) (π : W) (hπ : π ∈ I) (k : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    psum c π k N - psum c π k M ∈ I ^ M := by
  unfold psum
  rw [← Finset.sum_range_add_sum_Ico _ hMN, add_sub_cancel_left]
  refine Ideal.sum_mem _ fun m hm => ?_
  rw [Finset.mem_Ico] at hm
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hm.1 (Ideal.pow_mem_pow hπ m))

theorem exists_diag_sum [IsAdicComplete I W] (c : ℕ → W) (π : W) (hπ : π ∈ I) :
    ∃ h : ℕ → W, ∀ k, h k = c k + π * h (k + 1) := by

  have hlim : ∀ k, ∃ L : W, ∀ N, psum c π k N ≡ L [SMOD (I ^ N • ⊤ : Submodule W W)] := by
    intro k
    refine IsPrecomplete.prec' (fun N => psum c π k N) ?_
    intro M N hMN
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have := psum_sub_psum_mem I c π hπ k hMN
    rw [← Ideal.neg_mem_iff, neg_sub]
    exact this
  choose h hh using hlim
  refine ⟨h, fun k => ?_⟩

  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I) (h k - (c k + π * h (k + 1)))
  intro N
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  have h1 : psum c π k (N + 1) - h k ∈ I ^ (N + 1) := by
    have := hh k (N + 1); rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  have h2 : psum c π (k + 1) N - h (k + 1) ∈ I ^ N := by
    have := hh (k + 1) N; rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  have h1' : psum c π k (N + 1) - h k ∈ I ^ N := Ideal.pow_le_pow_right (Nat.le_succ N) h1
  have key : h k - (c k + π * h (k + 1)) =
      π * (psum c π (k + 1) N - h (k + 1)) - (psum c π k (N + 1) - h k) := by
    rw [psum_succ]; ring
  rw [key]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ h2) h1'

theorem eq_zero_of_diag_rec [IsAdicComplete I W] (x : ℕ → W) (π : W) (hπ : π ∈ I)
    (hx : ∀ k, x k = π * x (k + 1)) (k : ℕ) : x k = 0 := by
  have hpow : ∀ n, x k = π ^ n * x (k + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, hx (k + n), pow_succ, mul_assoc, show k + n + 1 = k + (n + 1) by omega]
  apply IsHausdorff.haus' (I := I) (x k)
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top, hpow n]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ n)

end AnnulusNF

namespace AnnulusNF

open ModularCurve ModularCurve.UVCrossingModel

variable {W : Type*} [CommRing W]

noncomputable abbrev ij (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

theorem ij_apply_zero (i j : ℕ) : ij i j 0 = i := by simp [ij]
theorem ij_apply_one (i j : ℕ) : ij i j 1 = j := by simp [ij]

theorem eq_ij (d : Fin 2 →₀ ℕ) : d = ij (d 0) (d 1) := by
  ext k
  fin_cases k <;> simp [ij]

theorem exists_coherent {I : Ideal W} [IsAdicComplete I W] (c : ℕ → ℕ → W) (π : W) (hπ : π ∈ I) :
    ∃ H : ℕ → ℕ → W, ∀ i j, H i j = c i j + π * H (i + 1) (j + 1) := by
  have hex : ∀ i j : ℕ, ∃ h : ℕ → W, ∀ k, h k = c (i + k) (j + k) + π * h (k + 1) :=
    fun i j => exists_diag_sum I (fun k => c (i + k) (j + k)) π hπ
  choose h hh using hex
  refine ⟨fun i j => h (i - min i j) (j - min i j) (min i j), fun i j => ?_⟩
  have hmin : min (i + 1) (j + 1) = min i j + 1 := Nat.add_min_add_right i j 1
  simp only [hmin, Nat.add_sub_add_right]
  have h1 := hh (i - min i j) (j - min i j) (min i j)
  rw [Nat.sub_add_cancel (Nat.min_le_left i j), Nat.sub_add_cancel (Nat.min_le_right i j)] at h1
  exact h1

theorem coeff_X_mul_X_mul (G : MvPowerSeries (Fin 2) W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 * G) =
      if 1 ≤ d 0 ∧ 1 ≤ d 1 then MvPowerSeries.coeff (ij (d 0 - 1) (d 1 - 1)) G else 0 := by
  have hXX : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 =
      MvPowerSeries.monomial (ij 1 1) 1 := by
    rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, one_mul]
  rw [hXX, MvPowerSeries.coeff_monomial_mul]
  have hle : ij 1 1 ≤ d ↔ 1 ≤ d 0 ∧ 1 ≤ d 1 := by
    constructor
    · intro h; exact ⟨by simpa [ij] using h 0, by simpa [ij] using h 1⟩
    · rintro ⟨h0, h1⟩ k; fin_cases k <;> simp [ij, h0, h1]
  by_cases h : 1 ≤ d 0 ∧ 1 ≤ d 1
  · rw [if_pos (hle.2 h), if_pos h, one_mul]
    congr 1
    rw [eq_ij (d - ij 1 1)]
    simp [ij]
  · rw [if_neg (fun h' => h (hle.1 h')), if_neg h]

theorem exists_normalForm (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W] (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) :
    ∃ ab : PowerSeries W × PowerSeries W,
      PowerSeries.constantCoeff ab.2 = 0 ∧ mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x := by
  classical
  obtain ⟨F, rfl⟩ := mk_surjective (ϖ ^ e) x
  set π : W := ϖ ^ e with hπdef
  have hπ : π ∈ Ideal.span {ϖ} := by
    rw [hπdef, ← Nat.sub_add_cancel he, pow_succ]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  let c : ℕ → ℕ → W := fun i j => MvPowerSeries.coeff (ij i j) F
  obtain ⟨H, hH⟩ := exists_coherent c π hπ
  let a : PowerSeries W := PowerSeries.mk fun i => H i 0
  let b : PowerSeries W := PowerSeries.mk fun j => if j = 0 then 0 else H 0 j
  let G : MvPowerSeries (Fin 2) W := fun d => H (d 0 + 1) (d 1 + 1)
  refine ⟨(a, b), by simp [b], ?_⟩

  symm
  change Ideal.Quotient.mk _ F = Ideal.Quotient.mk _ (inU a + inV b)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  refine ⟨G, ?_⟩
  rw [mul_comm]
  ext d
  rw [map_sub, sub_mul, map_sub, coeff_X_mul_X_mul, MvPowerSeries.coeff_C_mul, map_add, coeff_inU, coeff_inV]
  have hc : MvPowerSeries.coeff d F = c (d 0) (d 1) := by
    show _ = MvPowerSeries.coeff (ij (d 0) (d 1)) F
    rw [← eq_ij d]
  rw [hc]
  simp only [a, b, PowerSeries.coeff_mk]
  have hG : ∀ i j, MvPowerSeries.coeff (ij i j) G = H (i + 1) (j + 1) := by
    intro i j
    show G (ij i j) = _
    simp only [G, ij_apply_zero, ij_apply_one]
  have hGd : MvPowerSeries.coeff d G = H (d 0 + 1) (d 1 + 1) := rfl
  rw [hGd]
  have hrec := hH (d 0) (d 1)
  by_cases h0 : d 0 = 0 <;> by_cases h1 : d 1 = 0
  ·
    rw [if_neg (by omega), if_pos h1, if_pos h0, if_pos h1, h0, h1]
    rw [h0, h1] at hrec
    rw [hrec]; ring
  ·
    rw [if_neg (by omega), if_neg h1, if_pos h0, if_neg h1, h0]
    rw [h0] at hrec
    rw [hrec]; ring
  ·
    rw [if_neg (by omega), if_pos h1, if_neg h0, h1]
    rw [h1] at hrec
    rw [hrec]; ring
  ·
    rw [if_pos ⟨by omega, by omega⟩, if_neg h1, if_neg h0, hG, Nat.sub_add_cancel (by omega),
      Nat.sub_add_cancel (by omega), hrec]
    ring

theorem inU_sub (a a' : PowerSeries W) : inU (a - a') = inU a - inU a' := by
  ext d; simp only [coeff_inU, map_sub]; split_ifs <;> simp

theorem inV_sub (b b' : PowerSeries W) : inV (b - b') = inV b - inV b' := by
  ext d; simp only [coeff_inV, map_sub]; split_ifs <;> simp

theorem normalForm_unique (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W] (e : ℕ) (he : 1 ≤ e)
    (a b a' b' : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) (hb' : PowerSeries.constantCoeff b' = 0)
    (h : mk (ϖ ^ e) (inU a + inV b) = mk (ϖ ^ e) (inU a' + inV b')) : a = a' ∧ b = b' := by
  classical
  set π : W := ϖ ^ e with hπdef
  have hπ : π ∈ Ideal.span {ϖ} := by
    rw [hπdef, ← Nat.sub_add_cancel he, pow_succ]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _ at h
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h
  obtain ⟨G, hG⟩ := h
  rw [mul_comm] at hG

  have hoff : ∀ i j, MvPowerSeries.coeff (ij i j) G = π * MvPowerSeries.coeff (ij (i + 1) (j + 1)) G := by
    intro i j
    have hc := congrArg (MvPowerSeries.coeff (ij (i + 1) (j + 1))) hG
    rw [sub_mul, map_sub, coeff_X_mul_X_mul, MvPowerSeries.coeff_C_mul, ij_apply_zero, ij_apply_one,
      if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel, Nat.add_sub_cancel] at hc
    have hz : MvPowerSeries.coeff (ij (i + 1) (j + 1)) (inU a + inV b - (inU a' + inV b')) = 0 := by
      simp [coeff_inU, coeff_inV, ij_apply_zero, ij_apply_one]
    rw [hz] at hc
    exact sub_eq_zero.mp hc

  have hG0 : ∀ i j, MvPowerSeries.coeff (ij i j) G = 0 := by
    intro i j
    have := eq_zero_of_diag_rec (Ideal.span {ϖ}) (fun k => MvPowerSeries.coeff (ij (i + k) (j + k)) G) π hπ
      (fun k => by
        have := hoff (i + k) (j + k)
        simpa [Nat.add_assoc] using this) 0
    simpa using this
  have hGzero : G = 0 := by
    ext d; rw [eq_ij d, hG0, map_zero]
  rw [hGzero, mul_zero] at hG

  have hz : ∀ d, MvPowerSeries.coeff d (inU a + inV b - (inU a' + inV b')) = 0 := by
    intro d; rw [← hG, map_zero]
  constructor
  · ext i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h00 := hz (ij 0 0)
      simp only [map_sub, map_add, coeff_inU, coeff_inV, ij_apply_zero, ij_apply_one, if_true] at h00
      have hb0 : PowerSeries.coeff 0 b = 0 := by simpa using hb
      have hb0' : PowerSeries.coeff 0 b' = 0 := by simpa using hb'
      rw [hb0, hb0'] at h00
      exact sub_eq_zero.mp (by simpa using h00)
    · have h := hz (ij i 0)
      simp only [map_sub, map_add, coeff_inU, coeff_inV, ij_apply_zero, ij_apply_one, if_true,
        if_neg (Nat.pos_iff_ne_zero.mp hi), add_zero] at h
      exact sub_eq_zero.mp h
  · ext j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · have hb0 : PowerSeries.coeff 0 b = 0 := by simpa using hb
      have hb0' : PowerSeries.coeff 0 b' = 0 := by simpa using hb'
      rw [hb0, hb0']
    · have h := hz (ij 0 j)
      simp only [map_sub, map_add, coeff_inU, coeff_inV, ij_apply_zero, ij_apply_one, if_true,
        if_neg (Nat.pos_iff_ne_zero.mp hj), zero_add] at h
      exact sub_eq_zero.mp h

theorem existsUnique_normalForm (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W] (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) :
    ∃! ab : PowerSeries W × PowerSeries W,
      PowerSeries.constantCoeff ab.2 = 0 ∧ mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x := by
  obtain ⟨ab, hb, hx⟩ := exists_normalForm ϖ e he x
  refine ⟨ab, ⟨hb, hx⟩, ?_⟩
  rintro ⟨a', b'⟩ ⟨hb', hx'⟩
  obtain ⟨ha, hbb⟩ := normalForm_unique ϖ e he a' b' ab.1 ab.2 hb' hb (hx'.trans hx.symm)
  exact Prod.ext ha hbb

end AnnulusNF

namespace AnnulusG1

open ModularCurve ModularCurve.UVCrossingModel Finset

variable {W : Type*} [CommRing W]

theorem le_map_sum_add (v : AddValuation W ℕ∞) {ι : Type*} (s : Finset ι) (a : ι → W) (n w : ℕ∞)
    (h : ∀ k ∈ s, n ≤ v (a k) + w) : n ≤ v (∑ k ∈ s, a k) + w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
      rw [Finset.sum_insert hx]
      have h1 : n ≤ v (a x) + w := h x (Finset.mem_insert_self x s)
      have h2 : n ≤ v (∑ k ∈ s, a k) + w := ih fun k hk => h k (Finset.mem_insert_of_mem hk)
      calc n ≤ min (v (a x)) (v (∑ k ∈ s, a k)) + w := by
            rw [← min_add_add_right]; exact le_min h1 h2
        _ ≤ v (a x + ∑ k ∈ s, a k) + w := add_le_add (v.map_add _ _) le_rfl

theorem annulusWeight_add (e t : ℕ) (p q : Fin 2 →₀ ℕ) :
    annulusWeight e t (p + q) = annulusWeight e t p + annulusWeight e t q := by
  simp only [annulusWeight, Finsupp.add_apply]
  ring

end AnnulusG1

namespace AnnulusNF

open ModularCurve ModularCurve.UVCrossingModel Finset

variable {W : Type*} [CommRing W]

theorem exists_normalForm_rec (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W] (e : ℕ) (he : 1 ≤ e)
    (F : MvPowerSeries (Fin 2) W) :
    ∃ H : ℕ → ℕ → W, (∀ i j, H i j = MvPowerSeries.coeff (ij i j) F + ϖ ^ e * H (i + 1) (j + 1)) ∧
      mk (ϖ ^ e) (inU (PowerSeries.mk fun i => H i 0) + inV (PowerSeries.mk fun j => if j = 0 then 0 else H 0 j)) =
        mk (ϖ ^ e) F := by
  classical
  set π : W := ϖ ^ e with hπdef
  have hπ : π ∈ Ideal.span {ϖ} := by
    rw [hπdef, ← Nat.sub_add_cancel he, pow_succ]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  let c : ℕ → ℕ → W := fun i j => MvPowerSeries.coeff (ij i j) F
  obtain ⟨H, hH⟩ := exists_coherent c π hπ
  refine ⟨H, hH, ?_⟩
  let a : PowerSeries W := PowerSeries.mk fun i => H i 0
  let b : PowerSeries W := PowerSeries.mk fun j => if j = 0 then 0 else H 0 j
  let G : MvPowerSeries (Fin 2) W := fun d => H (d 0 + 1) (d 1 + 1)
  symm
  change Ideal.Quotient.mk _ F = Ideal.Quotient.mk _ (inU a + inV b)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  refine ⟨G, ?_⟩
  rw [mul_comm]
  ext d
  rw [map_sub, sub_mul, map_sub, coeff_X_mul_X_mul, MvPowerSeries.coeff_C_mul, map_add, coeff_inU, coeff_inV]
  have hc : MvPowerSeries.coeff d F = c (d 0) (d 1) := by
    show _ = MvPowerSeries.coeff (ij (d 0) (d 1)) F
    rw [← eq_ij d]
  rw [hc]
  simp only [a, b, PowerSeries.coeff_mk]
  have hG : ∀ i j, MvPowerSeries.coeff (ij i j) G = H (i + 1) (j + 1) := by
    intro i j
    show G (ij i j) = _
    simp only [G, ij_apply_zero, ij_apply_one]
  have hGd : MvPowerSeries.coeff d G = H (d 0 + 1) (d 1 + 1) := rfl
  rw [hGd]
  have hrec := hH (d 0) (d 1)
  by_cases h0 : d 0 = 0 <;> by_cases h1 : d 1 = 0
  · rw [if_neg (by omega), if_pos h1, if_pos h0, if_pos h1, h0, h1]
    rw [h0, h1] at hrec
    rw [hrec]; ring
  · rw [if_neg (by omega), if_neg h1, if_pos h0, if_neg h1, h0]
    rw [h0] at hrec
    rw [hrec]; ring
  · rw [if_neg (by omega), if_pos h1, if_neg h0, h1]
    rw [h1] at hrec
    rw [hrec]; ring
  · rw [if_pos ⟨by omega, by omega⟩, if_neg h1, if_neg h0, hG, Nat.sub_add_cancel (by omega),
      Nat.sub_add_cancel (by omega), hrec]
    ring

theorem rec_iterate {H c : ℕ → ℕ → W} {π : W} (hH : ∀ i j, H i j = c i j + π * H (i + 1) (j + 1))
    (i j N : ℕ) :
    H i j = (∑ k ∈ range N, c (i + k) (j + k) * π ^ k) + π ^ N * H (i + N) (j + N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ih, Finset.sum_range_succ, hH (i + N) (j + N), pow_succ]
      simp only [Nat.add_assoc]
      ring

end AnnulusNF

namespace AnnulusStepA

open ModularCurve ModularCurve.UVCrossingModel Finset AnnulusNF AnnulusG1

variable {W : Type*} [CommRing W]

end AnnulusStepA

namespace AnnulusStepA

open ModularCurve ModularCurve.UVCrossingModel Finset AnnulusNF AnnulusG1

variable {W : Type*} [CommRing W]

end AnnulusStepA

namespace AnnulusG1eq

open ModularCurve ModularCurve.UVCrossingModel Finset AnnulusNF AnnulusG1 AnnulusStepA

variable {W : Type*} [CommRing W]

def lam (d : Fin 2 →₀ ℕ) : ℤ := (d 0 : ℤ) - (d 1 : ℤ)

theorem lam_add (d d' : Fin 2 →₀ ℕ) : lam (d + d') = lam d + lam d' := by
  simp only [lam, Finsupp.add_apply, Nat.cast_add]; ring

theorem lam_ij (i j : ℕ) : lam (ij i j) = (i : ℤ) - (j : ℤ) := by
  simp only [lam, ij_apply_zero, ij_apply_one]

theorem eq_of_axis_of_lam_eq {d d' : Fin 2 →₀ ℕ} (hd : d 0 = 0 ∨ d 1 = 0) (hd' : d' 0 = 0 ∨ d' 1 = 0)
    (h : lam d = lam d') : d = d' := by
  simp only [lam] at h
  have h0 : d 0 = d' 0 := by omega
  have h1 : d 1 = d' 1 := by omega
  rw [eq_ij d, eq_ij d', h0, h1]

theorem annulusWeight_ij_add_diag (e t : ℕ) (ht : t ≤ e) (i j k : ℕ) :
    annulusWeight e t (ij (i + k) (j + k)) = annulusWeight e t (ij i j) + k * e := by
  simp only [annulusWeight, ij_apply_zero, ij_apply_one]
  have hk : k * t + k * (e - t) = k * e := by rw [← mul_add, Nat.add_sub_cancel' ht]
  calc (i + k) * t + (j + k) * (e - t) = i * t + j * (e - t) + (k * t + k * (e - t)) := by ring
    _ = i * t + j * (e - t) + k * e := by rw [hk]

theorem coeff_normalForm_axis (H : ℕ → ℕ → W) (i j : ℕ) (h : i = 0 ∨ j = 0) :
    MvPowerSeries.coeff (ij i j) (inU (PowerSeries.mk fun i => H i 0) +
      inV (PowerSeries.mk fun j => if j = 0 then 0 else H 0 j)) = H i j := by
  rw [map_add, coeff_inU, coeff_inV]
  simp only [ij_apply_zero, ij_apply_one, PowerSeries.coeff_mk]
  rcases h with rfl | rfl
  · by_cases hj : j = 0
    · subst hj; simp
    · simp [hj]
  · simp

theorem coeff_nf_off_axis (a b : PowerSeries W) (d : Fin 2 →₀ ℕ) (h0 : d 0 ≠ 0) (h1 : d 1 ≠ 0) :
    MvPowerSeries.coeff d (inU a + inV b) = 0 := by
  rw [map_add, coeff_inU, coeff_inV, if_neg h1, if_neg h0, add_zero]

theorem isolate (v : AddValuation W ℕ∞) {T R : W} {μ w : ℕ∞} (hμ : μ ≠ ⊤) (hT : v T + w = μ)
    (hR : μ + 1 ≤ v R + w) : v (T + R) + w ≤ μ := by
  by_contra h
  push Not at h
  have h1 : μ + 1 ≤ v (T + R) + w := Order.add_one_le_of_lt h
  have h2 : μ + 1 ≤ v T + w := by
    have hT' : T = (T + R) - R := by ring
    rw [hT']
    calc μ + 1 ≤ min (v (T + R)) (v R) + w := by
          rw [← min_add_add_right]; exact le_min h1 hR
      _ ≤ v (T + R - R) + w := add_le_add (v.map_sub _ _) le_rfl
  rw [hT] at h2
  exact absurd ((ENat.lt_add_one_iff hμ).mpr le_rfl) (not_lt.mpr h2)

theorem term_order (v : AddValuation W ℕ∞) (π : W) (e t : ℕ) (ht : t ≤ e) (hπ : v π = (e : ℕ∞))
    (Fx Fy : MvPowerSeries (Fin 2) W) (i j k : ℕ) (d₁ d₂ : Fin 2 →₀ ℕ)
    (h : d₁ + d₂ = ij (i + k) (j + k)) :
    v (MvPowerSeries.coeff d₁ Fx * MvPowerSeries.coeff d₂ Fy * π ^ k) +
        (annulusWeight e t (ij i j) : ℕ∞) =
      (v (MvPowerSeries.coeff d₁ Fx) + (annulusWeight e t d₁ : ℕ∞)) +
        (v (MvPowerSeries.coeff d₂ Fy) + (annulusWeight e t d₂ : ℕ∞)) := by
  have hw : annulusWeight e t d₁ + annulusWeight e t d₂ = annulusWeight e t (ij i j) + k * e := by
    rw [← annulusWeight_add, h, annulusWeight_ij_add_diag e t ht]
  have hw' : ((annulusWeight e t d₁ : ℕ) : ℕ∞) + ((annulusWeight e t d₂ : ℕ) : ℕ∞) =
      ((annulusWeight e t (ij i j) : ℕ) : ℕ∞) + (k : ℕ∞) * (e : ℕ∞) := by
    exact_mod_cast hw
  rw [v.map_mul, v.map_mul, v.map_pow, hπ, nsmul_eq_mul]
  generalize v (MvPowerSeries.coeff d₁ Fx) = A
  generalize v (MvPowerSeries.coeff d₂ Fy) = B
  calc A + B + (k : ℕ∞) * (e : ℕ∞) + ((annulusWeight e t (ij i j) : ℕ) : ℕ∞)
      = A + B + (((annulusWeight e t (ij i j) : ℕ) : ℕ∞) + (k : ℕ∞) * (e : ℕ∞)) := by ring
    _ = A + B + (((annulusWeight e t d₁ : ℕ) : ℕ∞) + ((annulusWeight e t d₂ : ℕ) : ℕ∞)) := by rw [hw']
    _ = _ := by ring

theorem exists_extreme_dominant (v : AddValuation W ℕ∞) (e t : ℕ) (hte : t < e)
    (F : MvPowerSeries (Fin 2) W)
    (hF : ∀ d : Fin 2 →₀ ℕ, d 0 ≠ 0 → d 1 ≠ 0 → MvPowerSeries.coeff d F = 0) (m : ℕ)
    (hm : (m : ℕ∞) = repGaussOrder v e t F) :
    ∃ dx : Fin 2 →₀ ℕ, (dx 0 = 0 ∨ dx 1 = 0) ∧
      v (MvPowerSeries.coeff dx F) + (annulusWeight e t dx : ℕ∞) = m ∧
      ∀ d, v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) = m →
        (d 0 = 0 ∨ d 1 = 0) ∧ lam dx ≤ lam d := by
  classical
  set o : (Fin 2 →₀ ℕ) → ℕ∞ := fun d => v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞)
    with ho
  have hm' : (m : ℕ∞) = ⨅ d, o d := hm

  obtain ⟨d₀, hd₀⟩ : ∃ d, o d = m := by
    obtain ⟨d, hd⟩ := ENat.exists_eq_iInf o
    exact ⟨d, hd.trans hm'.symm⟩

  have haxis : ∀ d, o d = m → d 0 = 0 ∨ d 1 = 0 := by
    intro d hd
    by_contra h
    push Not at h
    have : o d = ⊤ := by simp only [ho, hF d h.1 h.2, AddValuation.map_zero, top_add]
    rw [this] at hd
    exact ENat.top_ne_coe m hd

  have hbdd : ∀ d, o d = m → -(m : ℤ) ≤ lam d := by
    intro d hd
    rcases haxis d hd with h0 | h1
    · have hw : ((annulusWeight e t d : ℕ) : ℕ∞) ≤ m := by rw [← hd]; exact le_add_self
      have hw' : annulusWeight e t d ≤ m := by exact_mod_cast hw
      simp only [annulusWeight, h0, zero_mul, zero_add] at hw'
      have h2 : d 1 ≤ d 1 * (e - t) := Nat.le_mul_of_pos_right _ (by omega)
      simp only [lam, h0]; omega
    · simp only [lam, h1]; omega
  set S : Set ℤ := lam '' {d | o d = m} with hS
  have hSne : S.Nonempty := ⟨lam d₀, d₀, hd₀, rfl⟩
  have hSbdd : BddBelow S := ⟨-(m : ℤ), by rintro _ ⟨d, hd, rfl⟩; exact hbdd d hd⟩
  obtain ⟨dx, hdx, hdxS⟩ : ∃ d, o d = m ∧ lam d = sInf S := by
    obtain ⟨d, hd, hd'⟩ := Int.csInf_mem hSne hSbdd
    exact ⟨d, hd, hd'⟩
  refine ⟨dx, haxis dx hdx, hdx, fun d hd => ⟨haxis d hd, ?_⟩⟩
  rw [hdxS]
  exact csInf_le hSbdd ⟨d, hd, rfl⟩

end AnnulusG1eq

namespace AnnulusEndCoeff

open ModularCurve ModularCurve.UVCrossingModel Finset AnnulusNF AnnulusG1 AnnulusStepA AnnulusG1eq IsLocalRing

section General

variable {W : Type*} [CommRing W]

theorem exists_extreme_dominant_min (v : AddValuation W ℕ∞) (e t : ℕ) (hte : t < e)
    (F : MvPowerSeries (Fin 2) W)
    (hF : ∀ d : Fin 2 →₀ ℕ, d 0 ≠ 0 → d 1 ≠ 0 → MvPowerSeries.coeff d F = 0) (m : ℕ)
    (hm : (m : ℕ∞) = repGaussOrder v e t F) :
    ∃ dx : Fin 2 →₀ ℕ, (dx 0 = 0 ∨ dx 1 = 0) ∧
      v (MvPowerSeries.coeff dx F) + (annulusWeight e t dx : ℕ∞) = m ∧
      lam dx = sInf (lam '' {d | v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) = m}) ∧
      ∀ d, v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) = m →
        (d 0 = 0 ∨ d 1 = 0) ∧ lam dx ≤ lam d := by
  obtain ⟨dx, hax, hdx, hmin⟩ := exists_extreme_dominant v e t hte F hF m hm
  refine ⟨dx, hax, hdx, ?_, hmin⟩
  have hbdd : BddBelow (lam '' {d | v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) = m}) :=
    ⟨lam dx, by rintro _ ⟨d, hd, rfl⟩; exact (hmin d hd).2⟩
  refine le_antisymm (le_csInf ⟨lam dx, dx, hdx, rfl⟩ ?_) (csInf_le hbdd ⟨dx, hdx, rfl⟩)
  rintro _ ⟨d, hd, rfl⟩
  exact (hmin d hd).2

theorem exists_extreme_dominant_max (v : AddValuation W ℕ∞) (e t : ℕ) (ht0 : 0 < t)
    (F : MvPowerSeries (Fin 2) W)
    (hF : ∀ d : Fin 2 →₀ ℕ, d 0 ≠ 0 → d 1 ≠ 0 → MvPowerSeries.coeff d F = 0) (m : ℕ)
    (hm : (m : ℕ∞) = repGaussOrder v e t F) :
    ∃ dx : Fin 2 →₀ ℕ, (dx 0 = 0 ∨ dx 1 = 0) ∧
      v (MvPowerSeries.coeff dx F) + (annulusWeight e t dx : ℕ∞) = m ∧
      lam dx = sSup (lam '' {d | v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) = m}) ∧
      ∀ d, v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞) = m →
        (d 0 = 0 ∨ d 1 = 0) ∧ lam d ≤ lam dx := by
  classical
  set o : (Fin 2 →₀ ℕ) → ℕ∞ := fun d => v (MvPowerSeries.coeff d F) + (annulusWeight e t d : ℕ∞)
    with ho
  have hm' : (m : ℕ∞) = ⨅ d, o d := hm
  obtain ⟨d₀, hd₀⟩ : ∃ d, o d = m := by
    obtain ⟨d, hd⟩ := ENat.exists_eq_iInf o
    exact ⟨d, hd.trans hm'.symm⟩
  have haxis : ∀ d, o d = m → d 0 = 0 ∨ d 1 = 0 := by
    intro d hd
    by_contra h
    push Not at h
    have : o d = ⊤ := by simp only [ho, hF d h.1 h.2, AddValuation.map_zero, top_add]
    rw [this] at hd
    exact ENat.top_ne_coe m hd

  have hbdd : ∀ d, o d = m → lam d ≤ (m : ℤ) := by
    intro d hd
    rcases haxis d hd with h0 | h1
    · simp only [lam, h0]; omega
    · have hw : ((annulusWeight e t d : ℕ) : ℕ∞) ≤ m := by rw [← hd]; exact le_add_self
      have hw' : annulusWeight e t d ≤ m := by exact_mod_cast hw
      simp only [annulusWeight, h1, zero_mul, add_zero] at hw'
      have h2 : d 0 ≤ d 0 * t := Nat.le_mul_of_pos_right _ ht0
      simp only [lam, h1]; omega
  set S : Set ℤ := lam '' {d | o d = m} with hS
  have hSne : S.Nonempty := ⟨lam d₀, d₀, hd₀, rfl⟩
  have hSbdd : BddAbove S := ⟨(m : ℤ), by rintro _ ⟨d, hd, rfl⟩; exact hbdd d hd⟩
  obtain ⟨dx, hdx, hdxS⟩ : ∃ d, o d = m ∧ lam d = sSup S := by
    obtain ⟨d, hd, hd'⟩ := Int.csSup_mem hSne hSbdd
    exact ⟨d, hd, hd'⟩
  refine ⟨dx, haxis dx hdx, hdx, hdxS, fun d hd => ⟨haxis d hd, ?_⟩⟩
  rw [hdxS]
  exact le_csSup hSbdd ⟨d, hd, rfl⟩

theorem extreme_coeff_decomp (v : AddValuation W ℕ∞) (π : W) (e t : ℕ) (he : 1 ≤ e) (ht : t ≤ e)
    (hπ : v π = (e : ℕ∞)) (Fx Fy : MvPowerSeries (Fin 2) W)
    {H : ℕ → ℕ → W}
    (hH : ∀ i j, H i j = MvPowerSeries.coeff (ij i j) (Fx * Fy) + π * H (i + 1) (j + 1))
    (m n : ℕ) (hm : (m : ℕ∞) = repGaussOrder v e t Fx) (hn : (n : ℕ∞) = repGaussOrder v e t Fy)
    (dx dy : Fin 2 →₀ ℕ)
    (hdx : v (MvPowerSeries.coeff dx Fx) + (annulusWeight e t dx : ℕ∞) = m)
    (hdy : v (MvPowerSeries.coeff dy Fy) + (annulusWeight e t dy : ℕ∞) = n)
    (huniq : ∀ d₁ d₂, v (MvPowerSeries.coeff d₁ Fx) + (annulusWeight e t d₁ : ℕ∞) = m →
      v (MvPowerSeries.coeff d₂ Fy) + (annulusWeight e t d₂ : ℕ∞) = n →
      lam d₁ + lam d₂ = lam dx + lam dy → d₁ = dx ∧ d₂ = dy) :
    ∃ i₀ j₀ μ : ℕ, (i₀ = 0 ∨ j₀ = 0) ∧ dx + dy = ij (i₀ + μ) (j₀ + μ) ∧
      ∃ R : W, H i₀ j₀ = MvPowerSeries.coeff dx Fx * MvPowerSeries.coeff dy Fy * π ^ μ + R ∧
        v (MvPowerSeries.coeff dx Fx * MvPowerSeries.coeff dy Fy * π ^ μ) +
            (annulusWeight e t (ij i₀ j₀) : ℕ∞) = m + n ∧
        (m : ℕ∞) + n + 1 ≤ v R + (annulusWeight e t (ij i₀ j₀) : ℕ∞) := by
  classical
  set ox : (Fin 2 →₀ ℕ) → ℕ∞ := fun d => v (MvPowerSeries.coeff d Fx) + (annulusWeight e t d : ℕ∞)
    with hox
  set oy : (Fin 2 →₀ ℕ) → ℕ∞ := fun d => v (MvPowerSeries.coeff d Fy) + (annulusWeight e t d : ℕ∞)
    with hoy
  have hox_ge : ∀ d, (m : ℕ∞) ≤ ox d := fun d => by rw [hm]; exact repGaussOrder_le v e t Fx d
  have hoy_ge : ∀ d, (n : ℕ∞) ≤ oy d := fun d => by rw [hn]; exact repGaussOrder_le v e t Fy d

  set μ : ℕ := min ((dx + dy) 0) ((dx + dy) 1) with hμ
  set i₀ : ℕ := (dx + dy) 0 - μ with hi₀
  set j₀ : ℕ := (dx + dy) 1 - μ with hj₀
  have hij₀ : i₀ = 0 ∨ j₀ = 0 := by simp only [hi₀, hj₀, hμ]; omega
  have hs_eq : dx + dy = ij (i₀ + μ) (j₀ + μ) := by
    have h0 : i₀ + μ = (dx + dy) 0 := by simp only [hi₀, hμ]; omega
    have h1 : j₀ + μ = (dx + dy) 1 := by simp only [hj₀, hμ]; omega
    rw [h0, h1]; exact eq_ij _
  refine ⟨i₀, j₀, μ, hij₀, hs_eq, ?_⟩
  set w₀ : ℕ∞ := (annulusWeight e t (ij i₀ j₀) : ℕ∞) with hw₀

  set N : ℕ := μ + 1 + (m + n) with hN
  have hexpand := rec_iterate hH i₀ j₀ N
  set σ : Finset (Σ _ : ℕ, (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) :=
    (range N).sigma (fun k => antidiagonal (ij (i₀ + k) (j₀ + k))) with hσ
  set f : (Σ _ : ℕ, (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) → W :=
    fun z => MvPowerSeries.coeff z.2.1 Fx * MvPowerSeries.coeff z.2.2 Fy * π ^ z.1 with hf
  have hexp : (∑ k ∈ range N, MvPowerSeries.coeff (ij (i₀ + k) (j₀ + k)) (Fx * Fy) * π ^ k) =
      ∑ z ∈ σ, f z := by
    rw [hσ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  rw [hexp] at hexpand

  set z₀ : (Σ _ : ℕ, (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) := ⟨μ, (dx, dy)⟩ with hz₀def
  have hz₀ : z₀ ∈ σ := by
    rw [hσ, Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨(by omega : μ < N), hs_eq⟩

  have hterm : ∀ z ∈ σ, v (f z) + w₀ = ox z.2.1 + oy z.2.2 := by
    rintro ⟨k, d₁, d₂⟩ hz
    rw [hσ, Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hz
    exact term_order v π e t ht hπ Fx Fy i₀ j₀ k d₁ d₂ hz.2
  have hspecial : v (f z₀) + w₀ = (m : ℕ∞) + n := by
    rw [hterm z₀ hz₀]; exact congrArg₂ (· + ·) hdx hdy

  have hothers : ∀ z ∈ σ.erase z₀, (m : ℕ∞) + n + 1 ≤ v (f z) + w₀ := by
    intro z hz
    obtain ⟨hne, hzσ⟩ := Finset.mem_erase.mp hz
    rw [hterm z hzσ]
    obtain ⟨k, d₁, d₂⟩ := z
    rw [hσ, Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hzσ
    have h1 : (m : ℕ∞) ≤ ox d₁ := hox_ge d₁
    have h2 : (n : ℕ∞) ≤ oy d₂ := hoy_ge d₂
    by_cases hboth : ox d₁ = m ∧ oy d₂ = n
    · exfalso
      apply hne
      have hsum : lam d₁ + lam d₂ = lam dx + lam dy := by
        rw [← lam_add, ← lam_add, hzσ.2, hs_eq, lam_ij, lam_ij]; push_cast; ring
      obtain ⟨e1, e2⟩ := huniq d₁ d₂ hboth.1 hboth.2 hsum
      subst e1 e2
      have hk : k = μ := by
        have h3 : ij (i₀ + k) (j₀ + k) = ij (i₀ + μ) (j₀ + μ) := hzσ.2.symm.trans hs_eq
        have h4 := congrArg (fun d : Fin 2 →₀ ℕ => d 0) h3
        simp only [ij_apply_zero] at h4
        omega
      subst hk
      rfl
    · rw [not_and_or] at hboth
      rcases hboth with h | h
      · have h1' : (m : ℕ∞) + 1 ≤ ox d₁ := Order.add_one_le_of_lt (lt_of_le_of_ne h1 (Ne.symm h))
        calc (m : ℕ∞) + n + 1 = (m + 1) + n := by ring
          _ ≤ ox d₁ + oy d₂ := add_le_add h1' h2
      · have h2' : (n : ℕ∞) + 1 ≤ oy d₂ := Order.add_one_le_of_lt (lt_of_le_of_ne h2 (Ne.symm h))
        calc (m : ℕ∞) + n + 1 = m + (n + 1) := by ring
          _ ≤ ox d₁ + oy d₂ := add_le_add h1 h2'

  have htail : (m : ℕ∞) + n + 1 ≤ v (π ^ N * H (i₀ + N) (j₀ + N)) + w₀ := by
    rw [v.map_mul, v.map_pow, hπ, nsmul_eq_mul]
    have hNe : m + n + 1 ≤ N * e :=
      le_trans (by omega) (Nat.le_mul_of_pos_right N (by omega))
    have hNe' : ((m : ℕ) : ℕ∞) + n + 1 ≤ (N : ℕ∞) * (e : ℕ∞) := by exact_mod_cast hNe
    calc (m : ℕ∞) + n + 1 ≤ (N : ℕ∞) * (e : ℕ∞) := hNe'
      _ ≤ (N : ℕ∞) * (e : ℕ∞) + v (H (i₀ + N) (j₀ + N)) := le_self_add
      _ ≤ (N : ℕ∞) * (e : ℕ∞) + v (H (i₀ + N) (j₀ + N)) + w₀ := le_self_add
  have hrest : (m : ℕ∞) + n + 1 ≤
      v ((∑ z ∈ σ.erase z₀, f z) + π ^ N * H (i₀ + N) (j₀ + N)) + w₀ := by
    calc (m : ℕ∞) + n + 1
        ≤ min (v (∑ z ∈ σ.erase z₀, f z)) (v (π ^ N * H (i₀ + N) (j₀ + N))) + w₀ := by
          rw [← min_add_add_right]
          exact le_min (le_map_sum_add v _ f _ _ hothers) htail
      _ ≤ _ := add_le_add (v.map_add _ _) le_rfl
  refine ⟨(∑ z ∈ σ.erase z₀, f z) + π ^ N * H (i₀ + N) (j₀ + N), ?_, hspecial, hrest⟩
  rw [hexpand, ← Finset.add_sum_erase σ f hz₀, add_assoc]

theorem nfExponent_axis (n : ℤ) : (nfExponent n) 0 = 0 ∨ (nfExponent n) 1 = 0 := by
  cases n <;> simp [nfExponent]

theorem lam_nfExponent (n : ℤ) : lam (nfExponent n) = n := by
  cases n with
  | ofNat i => simp [lam, nfExponent]
  | negSucc j => simp [lam, nfExponent, Int.negSucc_eq]

theorem nfExponent_lam {d : Fin 2 →₀ ℕ} (hd : d 0 = 0 ∨ d 1 = 0) : nfExponent (lam d) = d :=
  eq_of_axis_of_lam_eq (nfExponent_axis _) hd (lam_nfExponent _)

theorem coeff_nfExponent (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    MvPowerSeries.coeff (nfExponent n) (inU ab.1 + inV ab.2) = nfCoeff ab n := by
  cases n with
  | ofNat i =>
    rw [map_add, coeff_inU, coeff_inV]
    simp only [nfExponent, nfCoeff, Finsupp.single_apply]
    simp only [Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, if_false, if_true]
    by_cases hi : i = 0
    · subst hi; simp [hb]
    · simp [hi]
  | negSucc j =>
    rw [map_add, coeff_inU, coeff_inV]
    simp [nfExponent, nfCoeff]

theorem termOrder_eq (v : W → ℕ∞) (e t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    termOrder v e t ab n =
      v (MvPowerSeries.coeff (nfExponent n) (inU ab.1 + inV ab.2)) + (annulusWeight e t (nfExponent n) : ℕ∞) := by
  rw [termOrder, coeff_nfExponent ab hb]

theorem nfCoeff_lam (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    {d : Fin 2 →₀ ℕ} (hd : d 0 = 0 ∨ d 1 = 0) :
    nfCoeff ab (lam d) = MvPowerSeries.coeff d (inU ab.1 + inV ab.2) := by
  rw [← coeff_nfExponent ab hb, nfExponent_lam hd]

theorem dominantIndices_eq_image_lam (v : AddValuation W ℕ∞) (e t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (m : ℕ)
    (hm : (m : ℕ∞) = repGaussOrder v e t (inU ab.1 + inV ab.2)) :
    dominantIndices v e t ab =
      lam '' {d | v (MvPowerSeries.coeff d (inU ab.1 + inV ab.2)) + (annulusWeight e t d : ℕ∞) = m} := by
  ext n
  simp only [dominantIndices, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro h
    refine ⟨nfExponent n, ?_, lam_nfExponent n⟩
    rw [hm, ← termOrder_eq v e t ab hb n]
    exact h
  · rintro ⟨d, hd, rfl⟩
    have hax : d 0 = 0 ∨ d 1 = 0 := by
      by_contra h
      push Not at h
      rw [coeff_nf_off_axis ab.1 ab.2 d h.1 h.2, AddValuation.map_zero, top_add] at hd
      exact ENat.top_ne_coe m hd
    rw [termOrder_eq v e t ab hb, nfExponent_lam hax, hd, hm]

theorem repGaussOrder_ne_top (v : AddValuation W ℕ∞) (hv : ∀ c : W, v c = ⊤ → c = 0) (π : W) (e t : ℕ)
    (ab : PowerSeries W × PowerSeries W) {x : UVCrossingModel W π} (hx : x ≠ 0)
    (habx : mk π (inU ab.1 + inV ab.2) = x) :
    repGaussOrder v e t (inU ab.1 + inV ab.2) ≠ ⊤ := by
  intro htop
  apply hx
  rw [← habx]
  have : inU ab.1 + inV ab.2 = 0 := by
    ext d
    have h := repGaussOrder_le v e t (inU ab.1 + inV ab.2) d
    rw [htop, top_le_iff] at h
    have h' : v (MvPowerSeries.coeff d (inU ab.1 + inV ab.2)) = ⊤ := by
      by_contra hne
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
      rw [← hk, ← ENat.coe_add] at h
      exact ENat.coe_ne_top _ h
    rw [hv _ h', map_zero]
  rw [this, map_zero]

end General

section DVR

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem isUnit_unitPart {ϖ c : W} (hϖ : Irreducible ϖ) (hc : c ≠ 0) : IsUnit (unitPart ϖ c) := by
  by_contra hu
  have hfin : FiniteMultiplicity ϖ c :=
    FiniteMultiplicity.of_prime_left (UniqueFactorizationMonoid.irreducible_iff_prime.mp hϖ) hc
  have hmem : unitPart ϖ c ∈ maximalIdeal W := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.mem_span_singleton] at hmem
  obtain ⟨r, hr⟩ := hmem
  apply hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_add_one (multiplicity ϖ c))
  refine ⟨r, ?_⟩
  conv_lhs => rw [← pow_multiplicity_mul_unitPart ϖ c, hr]
  ring

theorem leadingResidue_unit_mul_pow {ϖ : W} (hϖ : Irreducible ϖ) (u : Wˣ) (n : ℕ) {c : W}
    (h : c = (u : W) * ϖ ^ n) : leadingResidue ϖ c = residue W u := by
  have hc : c ≠ 0 := by rw [h]; exact mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ.ne_zero)
  rw [leadingResidue, if_neg hc]
  set w := (isUnit_unitPart hϖ hc).unit with hwdef
  have hw : (w : W) = unitPart ϖ c := IsUnit.unit_spec _
  have key : (w : W) * ϖ ^ multiplicity ϖ c = u * ϖ ^ n := by
    rw [hw, mul_comm, pow_multiplicity_mul_unitPart, h]
  rw [← hw, IsDiscreteValuationRing.unit_mul_pow_congr_unit hϖ w u _ _ key]

theorem ϖ_mem_maximalIdeal {ϖ : W} (hϖ : Irreducible ϖ) : ϖ ∈ maximalIdeal W := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  exact Ideal.mem_span_singleton_self ϖ

theorem leadingResidue_unit_mul_pow_add {ϖ : W} (hϖ : Irreducible ϖ) (u : Wˣ) (s : ℕ) (R : W)
    (hR : ((s + 1 : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal W R) :
    leadingResidue ϖ ((u : W) * ϖ ^ s + R) = residue W u := by

  have hdvd : ϖ ^ (s + 1) ∣ R := by
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_eq_mul, mul_one]
    exact hR
  obtain ⟨r, hr⟩ := hdvd

  have hunit : IsUnit ((u : W) + ϖ * r) := by
    by_contra hnu
    have hmem : (u : W) + ϖ * r ∈ maximalIdeal W := (mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have hmem' : (u : W) ∈ maximalIdeal W := by
      have := (maximalIdeal W).sub_mem hmem ((maximalIdeal W).mul_mem_right r (ϖ_mem_maximalIdeal hϖ))
      rwa [add_sub_cancel_right] at this
    exact (mem_maximalIdeal _).mp hmem' u.isUnit
  have hpres : (u : W) * ϖ ^ s + R = (hunit.unit : W) * ϖ ^ s := by
    rw [IsUnit.unit_spec, hr]; ring
  rw [leadingResidue_unit_mul_pow hϖ hunit.unit s hpres, IsUnit.unit_spec, map_add, map_mul,
    (residue_eq_zero_iff ϖ).mpr (ϖ_mem_maximalIdeal hϖ), zero_mul, add_zero]

end DVR

section Assembly

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem end_core (ϖ : W) (hϖ : Irreducible ϖ) [IsAdicComplete (Ideal.span {ϖ}) W] (e t : ℕ) (he : 1 ≤ e)
    (ht : t ≤ e)
    {x y : UVCrossingModel W (ϖ ^ e)}
    (ab ab' ab'' : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (hb'' : PowerSeries.constantCoeff ab''.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (haby : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y)
    (habxy : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) = x * y)
    (m n : ℕ) (hm : (m : ℕ∞) = repGaussOrder (IsDiscreteValuationRing.addVal W) e t (inU ab.1 + inV ab.2))
    (hn : (n : ℕ∞) = repGaussOrder (IsDiscreteValuationRing.addVal W) e t (inU ab'.1 + inV ab'.2))
    (dx dy : Fin 2 →₀ ℕ) (hdx0 : dx 0 = 0 ∨ dx 1 = 0) (hdy0 : dy 0 = 0 ∨ dy 1 = 0)
    (hdx : IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff dx (inU ab.1 + inV ab.2)) +
      (annulusWeight e t dx : ℕ∞) = m)
    (hdy : IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff dy (inU ab'.1 + inV ab'.2)) +
      (annulusWeight e t dy : ℕ∞) = n)
    (huniq : ∀ d₁ d₂,
      IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff d₁ (inU ab.1 + inV ab.2)) +
          (annulusWeight e t d₁ : ℕ∞) = m →
      IsDiscreteValuationRing.addVal W (MvPowerSeries.coeff d₂ (inU ab'.1 + inV ab'.2)) +
          (annulusWeight e t d₂ : ℕ∞) = n →
      lam d₁ + lam d₂ = lam dx + lam dy → d₁ = dx ∧ d₂ = dy)
    (N'' : ℤ) (hN'' : N'' = lam dx + lam dy) :
    leadingResidue ϖ (nfCoeff ab'' N'') =
      leadingResidue ϖ (nfCoeff ab (lam dx)) * leadingResidue ϖ (nfCoeff ab' (lam dy)) := by
  classical
  set v := IsDiscreteValuationRing.addVal W with hvdef
  set Fx := inU ab.1 + inV ab.2 with hFx
  set Fy := inU ab'.1 + inV ab'.2 with hFy
  have hπ : v (ϖ ^ e) = (e : ℕ∞) := by
    rw [hvdef, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_eq_mul,
      mul_one]

  obtain ⟨H, hH, hmk⟩ := exists_normalForm_rec ϖ e he (Fx * Fy)
  have hmk' : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) =
      mk (ϖ ^ e) (inU (PowerSeries.mk fun i => H i 0) + inV (PowerSeries.mk fun j => if j = 0 then 0 else H 0 j)) := by
    rw [habxy, hmk, map_mul, hFx, hFy, habx, haby]
  obtain ⟨h1'', h2''⟩ := normalForm_unique ϖ e he ab''.1 ab''.2 (PowerSeries.mk fun i => H i 0)
    (PowerSeries.mk fun j => if j = 0 then 0 else H 0 j) hb'' (by simp) hmk'

  obtain ⟨i₀, j₀, μ, hij₀, hs_eq, R, hHR, hT, hRest⟩ :=
    extreme_coeff_decomp v (ϖ ^ e) e t he ht hπ Fx Fy hH m n hm hn dx dy hdx hdy huniq

  have hN : N'' = lam (ij i₀ j₀) := by
    rw [hN'', ← lam_add, hs_eq, lam_ij, lam_ij]; push_cast; ring
  have hcoeff'' : nfCoeff ab'' N'' = H i₀ j₀ := by
    rw [hN, nfCoeff_lam ab'' hb'' (by rcases hij₀ with h | h <;> simp [ij_apply_zero, ij_apply_one, h]),
      show inU ab''.1 + inV ab''.2 = _ from by rw [h1'', h2''], coeff_normalForm_axis H i₀ j₀ hij₀]
  rw [hcoeff'', nfCoeff_lam ab hb hdx0, nfCoeff_lam ab' hb' hdy0, hHR]

  have hcx : MvPowerSeries.coeff dx Fx ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero, top_add] at hdx
    exact ENat.top_ne_coe m hdx
  have hcy : MvPowerSeries.coeff dy Fy ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero, top_add] at hdy
    exact ENat.top_ne_coe n hdy
  obtain ⟨p, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hcx hϖ
  obtain ⟨q, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hcy hϖ
  set s : ℕ := p + q + e * μ with hs
  have hTpres : MvPowerSeries.coeff dx Fx * MvPowerSeries.coeff dy Fy * (ϖ ^ e) ^ μ = ((u * w : Wˣ) : W) * ϖ ^ s := by
    rw [hu, hw, Units.val_mul, hs]; ring

  have hvT : v (MvPowerSeries.coeff dx Fx * MvPowerSeries.coeff dy Fy * (ϖ ^ e) ^ μ) = s := by
    rw [hTpres, hvdef, IsDiscreteValuationRing.addVal_def' _ hϖ]
  have hRv : ((s + 1 : ℕ) : ℕ∞) ≤ v R := by
    have hw₀ : ((annulusWeight e t (ij i₀ j₀) : ℕ) : ℕ∞) ≠ ⊤ := ENat.coe_ne_top _
    rw [← hT, hvT] at hRest
    have : ((s : ℕ∞) + 1) + (annulusWeight e t (ij i₀ j₀) : ℕ∞) ≤ v R + (annulusWeight e t (ij i₀ j₀) : ℕ∞) := by
      calc ((s : ℕ∞) + 1) + (annulusWeight e t (ij i₀ j₀) : ℕ∞)
          = (s : ℕ∞) + (annulusWeight e t (ij i₀ j₀) : ℕ∞) + 1 := by ring
        _ ≤ _ := hRest
    have h' := (WithTop.add_le_add_iff_right hw₀).mp this
    exact_mod_cast h'
  rw [hTpres, leadingResidue_unit_mul_pow_add hϖ (u * w) s R hRv, leadingResidue_unit_mul_pow hϖ u p hu,
    leadingResidue_unit_mul_pow hϖ w q hw, Units.val_mul, map_mul]

theorem leadingResidue_end_mul
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (y : UVCrossingModel W (ϖ ^ e)) (hy : y ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (haby : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y)
    (ab'' : PowerSeries W × PowerSeries W) (hb'' : PowerSeries.constantCoeff ab''.2 = 0)
    (habxy : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) = x * y) :
    leadingResidue ϖ (nfCoeff ab'' (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab''))) =
        leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) *
          leadingResidue ϖ (nfCoeff ab' (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab'))) ∧
      leadingResidue ϖ (nfCoeff ab'' (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab''))) =
        leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) *
          leadingResidue ϖ (nfCoeff ab' (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab'))) := by
  classical
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  set v := IsDiscreteValuationRing.addVal W with hvdef
  have hv0 : ∀ c : W, v c = ⊤ → c = 0 := fun c hc => IsDiscreteValuationRing.addVal_eq_top_iff.mp hc

  obtain ⟨hidx0, hidxe⟩ := ModularCurve.UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul
    ϖ hϖ e he x hx ab hb habx y hy ab' hb' haby ab'' hb'' habxy
  have hFx : ∀ d : Fin 2 →₀ ℕ, d 0 ≠ 0 → d 1 ≠ 0 → MvPowerSeries.coeff d (inU ab.1 + inV ab.2) = 0 :=
    coeff_nf_off_axis ab.1 ab.2
  have hFy : ∀ d : Fin 2 →₀ ℕ, d 0 ≠ 0 → d 1 ≠ 0 → MvPowerSeries.coeff d (inU ab'.1 + inV ab'.2) = 0 :=
    coeff_nf_off_axis ab'.1 ab'.2
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (repGaussOrder_ne_top v hv0 (ϖ ^ e) e 0 ab hx habx)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (repGaussOrder_ne_top v hv0 (ϖ ^ e) e 0 ab' hy haby)
    obtain ⟨dx, hdx0, hdx, hdxS, hdxmin⟩ := exists_extreme_dominant_min v e 0 (by omega) _ hFx m hm
    obtain ⟨dy, hdy0, hdy, hdyS, hdymin⟩ := exists_extreme_dominant_min v e 0 (by omega) _ hFy n hn
    have hSx : sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) = lam dx := by
      rw [dominantIndices_eq_image_lam v e 0 ab hb m hm, ← hdxS]
    have hSy : sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab') = lam dy := by
      rw [dominantIndices_eq_image_lam v e 0 ab' hb' n hn, ← hdyS]
    rw [hSx, hSy]
    refine end_core ϖ hϖ e 0 he (Nat.zero_le _) ab ab' ab'' hb hb' hb'' habx haby habxy m n hm hn dx dy
      hdx0 hdy0 hdx hdy ?_ _ (by rw [hidx0, hSx, hSy])
    intro d₁ d₂ h₁ h₂ hsum
    obtain ⟨ha₁, hl₁⟩ := hdxmin d₁ h₁
    obtain ⟨ha₂, hl₂⟩ := hdymin d₂ h₂
    exact ⟨eq_of_axis_of_lam_eq ha₁ hdx0 (by omega), eq_of_axis_of_lam_eq ha₂ hdy0 (by omega)⟩
  ·
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (repGaussOrder_ne_top v hv0 (ϖ ^ e) e e ab hx habx)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (repGaussOrder_ne_top v hv0 (ϖ ^ e) e e ab' hy haby)
    obtain ⟨dx, hdx0, hdx, hdxS, hdxmax⟩ := exists_extreme_dominant_max v e e (by omega) _ hFx m hm
    obtain ⟨dy, hdy0, hdy, hdyS, hdymax⟩ := exists_extreme_dominant_max v e e (by omega) _ hFy n hn
    have hSx : sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) = lam dx := by
      rw [dominantIndices_eq_image_lam v e e ab hb m hm, ← hdxS]
    have hSy : sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab') = lam dy := by
      rw [dominantIndices_eq_image_lam v e e ab' hb' n hn, ← hdyS]
    rw [hSx, hSy]
    refine end_core ϖ hϖ e e he le_rfl ab ab' ab'' hb hb' hb'' habx haby habxy m n hm hn dx dy
      hdx0 hdy0 hdx hdy ?_ _ (by rw [hidxe, hSx, hSy])
    intro d₁ d₂ h₁ h₂ hsum
    obtain ⟨ha₁, hl₁⟩ := hdxmax d₁ h₁
    obtain ⟨ha₂, hl₂⟩ := hdymax d₂ h₂
    exact ⟨eq_of_axis_of_lam_eq ha₁ hdx0 (by omega), eq_of_axis_of_lam_eq ha₂ hdy0 (by omega)⟩

end Assembly

end AnnulusEndCoeff

open ModularCurve ModularCurve.UVCrossingModel IsLocalRing in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (y : UVCrossingModel W (ϖ ^ e)) (hy : y ≠ 0)
    (ab' : PowerSeries W × PowerSeries W) (hb' : PowerSeries.constantCoeff ab'.2 = 0)
    (haby : mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y)
    (ab'' : PowerSeries W × PowerSeries W) (hb'' : PowerSeries.constantCoeff ab''.2 = 0)
    (habxy : mk (ϖ ^ e) (inU ab''.1 + inV ab''.2) = x * y) :
    leadingResidue ϖ (nfCoeff ab'' (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab''))) =
        leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) *
          leadingResidue ϖ (nfCoeff ab' (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab'))) ∧
      leadingResidue ϖ (nfCoeff ab'' (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab''))) =
        leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) *
          leadingResidue ϖ (nfCoeff ab' (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab'))) :=
  AnnulusEndCoeff.leadingResidue_end_mul ϖ hϖ e he x hx ab hb habx y hy ab' hb' haby ab'' hb'' habxy

#print axioms solution

end S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sInf_dominantIndices_zero_mul_and_sSup_mul (solution)
