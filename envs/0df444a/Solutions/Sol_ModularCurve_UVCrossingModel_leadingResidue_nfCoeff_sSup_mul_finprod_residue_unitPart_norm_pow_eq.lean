-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1139a103-244b-529c-a7ac-86606aaae5bd

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingInitialForm
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_existsUnique_normalForm
import Theorems.Thm_ModularCurve_UVCrossingModel_finsum_rank_mul_length_eq_sInf_sub_sSup
import Theorems.Thm_ModularCurve_UVCrossingModel_setOf_horizontal_mem_finite
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem
import Theorems.Thm_ModularCurve_UVCrossingModel_U_mul_V
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_mul_and_sSup_dominantIndices_mul
import Theorems.Thm_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_prime_V_sub_const_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq

set_option autoImplicit false

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel IsLocalRing"

universe u
set_option autoImplicit false

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

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

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

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel Finset"

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

theorem repGaussOrder_add_le_mul (v : AddValuation W ℕ∞) (e t : ℕ) (F G : MvPowerSeries (Fin 2) W) :
    repGaussOrder v e t F + repGaussOrder v e t G ≤ repGaussOrder v e t (F * G) := by
  classical
  rw [le_repGaussOrder_iff]
  intro d
  rw [MvPowerSeries.coeff_mul]
  apply le_map_sum_add
  rintro ⟨p, q⟩ hpq
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
  have hF := repGaussOrder_le v e t F p
  have hG := repGaussOrder_le v e t G q
  calc repGaussOrder v e t F + repGaussOrder v e t G
      ≤ (v (MvPowerSeries.coeff p F) + (annulusWeight e t p : ℕ∞)) +
          (v (MvPowerSeries.coeff q G) + (annulusWeight e t q : ℕ∞)) := add_le_add hF hG
    _ = v (MvPowerSeries.coeff p F * MvPowerSeries.coeff q G) + (annulusWeight e t d : ℕ∞) := by
          rw [v.map_mul, ← hpq, annulusWeight_add, Nat.cast_add]
          simp only [add_assoc, add_left_comm, add_comm]

theorem gaussOrder_eq_iSup_subtype (v : W → ℕ∞) (π : W) (e t : ℕ) (x : UVCrossingModel W π) :
    gaussOrder v π e t x = ⨆ F : {F : MvPowerSeries (Fin 2) W // mk π F = x}, repGaussOrder v e t F.1 := by
  rw [gaussOrder]
  exact iSup_subtype'

theorem gaussOrder_add_le_gaussOrder_mul (v : AddValuation W ℕ∞) (π : W) (e t : ℕ)
    (x y : UVCrossingModel W π) :
    gaussOrder v π e t x + gaussOrder v π e t y ≤ gaussOrder v π e t (x * y) := by
  rw [gaussOrder_eq_iSup_subtype, gaussOrder_eq_iSup_subtype]
  haveI : Nonempty {F : MvPowerSeries (Fin 2) W // mk π F = x} :=
    let ⟨F, hF⟩ := mk_surjective π x; ⟨⟨F, hF⟩⟩
  haveI : Nonempty {F : MvPowerSeries (Fin 2) W // mk π F = y} :=
    let ⟨F, hF⟩ := mk_surjective π y; ⟨⟨F, hF⟩⟩
  refine ENat.iSup_add_iSup_le fun F G => ?_
  calc repGaussOrder v e t F.1 + repGaussOrder v e t G.1
      ≤ repGaussOrder v e t (F.1 * G.1) := repGaussOrder_add_le_mul v e t F.1 G.1
    _ ≤ gaussOrder v π e t (mk π (F.1 * G.1)) := repGaussOrder_le_gaussOrder v π e t _
    _ = gaussOrder v π e t (x * y) := by rw [map_mul, F.2, G.2]

end AnnulusG1

namespace AnnulusNF

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel Finset"

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

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel Finset P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.AnnulusNF P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.AnnulusG1"

variable {W : Type*} [CommRing W]

theorem annulusWeight_diag_U (e t : ℕ) (ht : t ≤ e) (i k : ℕ) :
    annulusWeight e t (ij (i + k) k) = i * t + k * e := by
  simp only [annulusWeight, ij_apply_zero, ij_apply_one]
  have : k * (e - t) + k * t = k * e := by rw [← mul_add, Nat.sub_add_cancel ht]
  nlinarith [this]

theorem annulusWeight_diag_V (e t : ℕ) (ht : t ≤ e) (j k : ℕ) :
    annulusWeight e t (ij k (j + k)) = j * (e - t) + k * e := by
  simp only [annulusWeight, ij_apply_zero, ij_apply_one]
  have : k * (e - t) + k * t = k * e := by rw [← mul_add, Nat.sub_add_cancel ht]
  nlinarith [this]

theorem min_le_v_H_U (v : AddValuation W ℕ∞) (π : W) (e t : ℕ) (ht : t ≤ e) (hπ : ((e : ℕ) : ℕ∞) ≤ v π)
    (F : MvPowerSeries (Fin 2) W) {H : ℕ → ℕ → W}
    (hH : ∀ i j, H i j = MvPowerSeries.coeff (ij i j) F + π * H (i + 1) (j + 1)) (N i : ℕ) :
    min (repGaussOrder v e t F) ((N * e : ℕ) : ℕ∞) ≤ v (H i 0) + ((i * t : ℕ) : ℕ∞) := by
  rw [rec_iterate hH i 0 N]
  simp only [Nat.zero_add]

  have hsum : repGaussOrder v e t F ≤
      v (∑ k ∈ range N, MvPowerSeries.coeff (ij (i + k) k) F * π ^ k) + ((i * t : ℕ) : ℕ∞) := by
    apply le_map_sum_add
    intro k _
    have h1 := repGaussOrder_le v e t F (ij (i + k) k)
    rw [annulusWeight_diag_U e t ht] at h1
    calc repGaussOrder v e t F ≤ v (MvPowerSeries.coeff (ij (i + k) k) F) + ((i * t + k * e : ℕ) : ℕ∞) := h1
      _ ≤ v (MvPowerSeries.coeff (ij (i + k) k) F * π ^ k) + ((i * t : ℕ) : ℕ∞) := by
          rw [v.map_mul, v.map_pow, Nat.cast_add, Nat.cast_mul]
          have hk : ((k : ℕ) : ℕ∞) * (e : ℕ∞) ≤ k • v π := by
            rw [nsmul_eq_mul]; exact mul_le_mul_right hπ _
          calc v (MvPowerSeries.coeff (ij (i + k) k) F) + (↑i * ↑t + ↑k * ↑e)
              = (v (MvPowerSeries.coeff (ij (i + k) k) F) + ↑k * ↑e) + ↑i * ↑t := by ring
            _ ≤ (v (MvPowerSeries.coeff (ij (i + k) k) F) + k • v π) + ↑i * ↑t :=
                add_le_add (add_le_add le_rfl hk) le_rfl

  have htail : ((N * e : ℕ) : ℕ∞) ≤ v (π ^ N * H (i + N) N) + ((i * t : ℕ) : ℕ∞) := by
    rw [v.map_mul, v.map_pow, Nat.cast_mul]
    have hN : ((N : ℕ) : ℕ∞) * (e : ℕ∞) ≤ N • v π := by
      rw [nsmul_eq_mul]; exact mul_le_mul_right hπ _
    calc (↑N * ↑e : ℕ∞) ≤ N • v π := hN
      _ ≤ N • v π + v (H (i + N) N) := le_self_add
      _ ≤ N • v π + v (H (i + N) N) + ↑(i * t) := le_self_add
  calc min (repGaussOrder v e t F) ((N * e : ℕ) : ℕ∞)
      ≤ min (v (∑ k ∈ range N, MvPowerSeries.coeff (ij (i + k) k) F * π ^ k) + ((i * t : ℕ) : ℕ∞))
          (v (π ^ N * H (i + N) N) + ((i * t : ℕ) : ℕ∞)) := min_le_min hsum htail
    _ = min (v (∑ k ∈ range N, MvPowerSeries.coeff (ij (i + k) k) F * π ^ k)) (v (π ^ N * H (i + N) N)) +
          ((i * t : ℕ) : ℕ∞) := (min_add_add_right _ _ _)
    _ ≤ _ := add_le_add (v.map_add _ _) le_rfl

theorem min_le_v_H_V (v : AddValuation W ℕ∞) (π : W) (e t : ℕ) (ht : t ≤ e) (hπ : ((e : ℕ) : ℕ∞) ≤ v π)
    (F : MvPowerSeries (Fin 2) W) {H : ℕ → ℕ → W}
    (hH : ∀ i j, H i j = MvPowerSeries.coeff (ij i j) F + π * H (i + 1) (j + 1)) (N j : ℕ) :
    min (repGaussOrder v e t F) ((N * e : ℕ) : ℕ∞) ≤ v (H 0 j) + ((j * (e - t) : ℕ) : ℕ∞) := by
  rw [rec_iterate hH 0 j N]
  simp only [Nat.zero_add]
  have hsum : repGaussOrder v e t F ≤
      v (∑ k ∈ range N, MvPowerSeries.coeff (ij k (j + k)) F * π ^ k) + ((j * (e - t) : ℕ) : ℕ∞) := by
    apply le_map_sum_add
    intro k _
    have h1 := repGaussOrder_le v e t F (ij k (j + k))
    rw [annulusWeight_diag_V e t ht] at h1
    calc repGaussOrder v e t F ≤ v (MvPowerSeries.coeff (ij k (j + k)) F) + ((j * (e - t) + k * e : ℕ) : ℕ∞) := h1
      _ ≤ v (MvPowerSeries.coeff (ij k (j + k)) F * π ^ k) + ((j * (e - t) : ℕ) : ℕ∞) := by
          rw [v.map_mul, v.map_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
          have hk : ((k : ℕ) : ℕ∞) * (e : ℕ∞) ≤ k • v π := by
            rw [nsmul_eq_mul]; exact mul_le_mul_right hπ _
          calc v (MvPowerSeries.coeff (ij k (j + k)) F) + (↑j * ↑(e - t) + ↑k * ↑e)
              = (v (MvPowerSeries.coeff (ij k (j + k)) F) + ↑k * ↑e) + ↑j * ↑(e - t) := by ring
            _ ≤ (v (MvPowerSeries.coeff (ij k (j + k)) F) + k • v π) + ↑j * ↑(e - t) :=
                add_le_add (add_le_add le_rfl hk) le_rfl
  have htail : ((N * e : ℕ) : ℕ∞) ≤ v (π ^ N * H N (j + N)) + ((j * (e - t) : ℕ) : ℕ∞) := by
    rw [v.map_mul, v.map_pow, Nat.cast_mul]
    have hN : ((N : ℕ) : ℕ∞) * (e : ℕ∞) ≤ N • v π := by
      rw [nsmul_eq_mul]; exact mul_le_mul_right hπ _
    calc (↑N * ↑e : ℕ∞) ≤ N • v π := hN
      _ ≤ N • v π + v (H N (j + N)) := le_self_add
      _ ≤ N • v π + v (H N (j + N)) + ↑(j * (e - t)) := le_self_add
  calc min (repGaussOrder v e t F) ((N * e : ℕ) : ℕ∞)
      ≤ min (v (∑ k ∈ range N, MvPowerSeries.coeff (ij k (j + k)) F * π ^ k) + ((j * (e - t) : ℕ) : ℕ∞))
          (v (π ^ N * H N (j + N)) + ((j * (e - t) : ℕ) : ℕ∞)) := min_le_min hsum htail
    _ = min (v (∑ k ∈ range N, MvPowerSeries.coeff (ij k (j + k)) F * π ^ k)) (v (π ^ N * H N (j + N))) +
          ((j * (e - t) : ℕ) : ℕ∞) := (min_add_add_right _ _ _)
    _ ≤ _ := add_le_add (v.map_add _ _) le_rfl

theorem le_of_forall_min_le {ρ X : ℕ∞} {e : ℕ} (he : 1 ≤ e)
    (h : ∀ N : ℕ, min ρ ((N * e : ℕ) : ℕ∞) ≤ X) : ρ ≤ X := by
  rw [← ENat.forall_natCast_le_iff_le]
  intro a ha
  have h1 : (a : ℕ∞) ≤ ((a * e : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_mul_of_pos_right a he
  exact le_trans (le_min ha h1) (h a)

theorem repGaussOrder_le_normalForm (v : AddValuation W ℕ∞) (π : W) (e t : ℕ) (he : 1 ≤ e) (ht : t ≤ e)
    (hπ : ((e : ℕ) : ℕ∞) ≤ v π) (F : MvPowerSeries (Fin 2) W) {H : ℕ → ℕ → W}
    (hH : ∀ i j, H i j = MvPowerSeries.coeff (ij i j) F + π * H (i + 1) (j + 1)) :
    repGaussOrder v e t F ≤
      repGaussOrder v e t (inU (PowerSeries.mk fun i => H i 0) + inV (PowerSeries.mk fun j => if j = 0 then 0 else H 0 j)) := by
  classical
  rw [le_repGaussOrder_iff]
  intro d
  rw [map_add, coeff_inU, coeff_inV]
  simp only [PowerSeries.coeff_mk]
  by_cases h0 : d 0 = 0 <;> by_cases h1 : d 1 = 0
  ·
    rw [if_pos h1, if_pos h0, if_pos h1, add_zero, h0]
    have := le_of_forall_min_le he fun N => min_le_v_H_U v π e t ht hπ F hH N 0
    simp only [Nat.zero_mul, Nat.cast_zero, add_zero] at this
    have hw : annulusWeight e t d = 0 := by simp [annulusWeight, h0, h1]
    rw [hw, Nat.cast_zero, add_zero]
    exact this
  ·
    rw [if_neg h1, if_pos h0, if_neg h1, zero_add]
    have hw : annulusWeight e t d = d 1 * (e - t) := by simp [annulusWeight, h0]
    rw [hw]
    exact le_of_forall_min_le he fun N => min_le_v_H_V v π e t ht hπ F hH N (d 1)
  ·
    rw [if_pos h1, if_neg h0, add_zero]
    have hw : annulusWeight e t d = d 0 * t := by simp [annulusWeight, h1]
    rw [hw]
    exact le_of_forall_min_le he fun N => min_le_v_H_U v π e t ht hπ F hH N (d 0)
  ·
    rw [if_neg h1, if_neg h0, add_zero, v.map_zero, top_add]
    exact le_top

end AnnulusStepA

set_option autoImplicit false

namespace AnnulusSlope

theorem iInf_midpoint_concave {ι : Type*} (F : ι → ℕ → ℕ∞) (t : ℕ)
    (hF : ∀ i, F i (t - 1) + F i (t + 1) = F i t + F i t) :
    (⨅ i, F i (t - 1)) + (⨅ i, F i (t + 1)) ≤ (⨅ i, F i t) + (⨅ i, F i t) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [iInf_of_empty]
    exact le_rfl
  ·
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, F i₀ t = ⨅ i, F i t := by
      have hmem := csInf_mem (Set.range_nonempty fun i => F i t)
      obtain ⟨i₀, hi₀⟩ := hmem
      exact ⟨i₀, hi₀⟩
    rw [← hi₀, ← hF i₀]
    exact add_le_add (iInf_le _ i₀) (iInf_le _ i₀)

noncomputable def gaussOrder (e : ℕ) (α β : ℕ → ℕ∞) (t : ℕ) : ℕ∞ :=
  (⨅ i : ℕ, α i + ((i * t : ℕ) : ℕ∞)) ⊓ (⨅ j : ℕ, β j + (((j + 1) * (e - t) : ℕ) : ℕ∞))

theorem gaussOrder_midpoint_concave (e : ℕ) (α β : ℕ → ℕ∞) (t : ℕ) (ht1 : 1 ≤ t) (hte : t + 1 ≤ e) :
    gaussOrder e α β (t - 1) + gaussOrder e α β (t + 1) ≤ gaussOrder e α β t + gaussOrder e α β t := by

  let F : ℕ ⊕ ℕ → ℕ → ℕ∞ := fun k s => match k with
    | Sum.inl i => α i + ((i * s : ℕ) : ℕ∞)
    | Sum.inr j => β j + (((j + 1) * (e - s) : ℕ) : ℕ∞)
  have hg : ∀ s, gaussOrder e α β s = ⨅ k, F k s := by
    intro s
    rw [gaussOrder, iInf_sum]
  rw [hg, hg, hg]
  apply iInf_midpoint_concave
  rintro (i | j)
  · show α i + ((i * (t - 1) : ℕ) : ℕ∞) + (α i + ((i * (t + 1) : ℕ) : ℕ∞)) =
      α i + ((i * t : ℕ) : ℕ∞) + (α i + ((i * t : ℕ) : ℕ∞))
    have h : i * (t - 1) + i * (t + 1) = i * t + i * t := by
      have : t - 1 + (t + 1) = t + t := by omega
      rw [← mul_add, ← mul_add, this]
    rw [add_add_add_comm, ← Nat.cast_add, h, Nat.cast_add, add_add_add_comm]
  · show β j + (((j + 1) * (e - (t - 1)) : ℕ) : ℕ∞) + (β j + (((j + 1) * (e - (t + 1)) : ℕ) : ℕ∞)) =
      β j + (((j + 1) * (e - t) : ℕ) : ℕ∞) + (β j + (((j + 1) * (e - t) : ℕ) : ℕ∞))
    have h : (j + 1) * (e - (t - 1)) + (j + 1) * (e - (t + 1)) = (j + 1) * (e - t) + (j + 1) * (e - t) := by
      have : e - (t - 1) + (e - (t + 1)) = (e - t) + (e - t) := by omega
      rw [← mul_add, ← mul_add, this]
    rw [add_add_add_comm, ← Nat.cast_add, h, Nat.cast_add, add_add_add_comm]

theorem gaussOrder_forward_diff_antitone (e : ℕ) (α β : ℕ → ℕ∞) (t : ℕ) (ht1 : 1 ≤ t) (hte : t + 1 ≤ e) :
    gaussOrder e α β (t + 1) + gaussOrder e α β (t - 1) ≤ gaussOrder e α β t + gaussOrder e α β t := by
  rw [add_comm]
  exact gaussOrder_midpoint_concave e α β t ht1 hte

end AnnulusSlope

namespace AnnulusStepA

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel Finset P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.AnnulusNF P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.AnnulusG1"

variable {W : Type*} [CommRing W]

theorem exists_normalForm_gaussOrder_eq (v : AddValuation W ℕ∞) (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W]
    (e : ℕ) (he : 1 ≤ e) (hπ : ((e : ℕ) : ℕ∞) ≤ v (ϖ ^ e)) (x : UVCrossingModel W (ϖ ^ e)) :
    ∃ ab : PowerSeries W × PowerSeries W,
      PowerSeries.constantCoeff ab.2 = 0 ∧ mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x ∧
      ∀ t, t ≤ e → gaussOrder v (ϖ ^ e) e t x = repGaussOrder v e t (inU ab.1 + inV ab.2) := by
  classical
  obtain ⟨F₀, rfl⟩ := mk_surjective (ϖ ^ e) x
  obtain ⟨H, hH, hmk⟩ := exists_normalForm_rec ϖ e he F₀
  set a : PowerSeries W := PowerSeries.mk fun i => H i 0 with ha
  set b : PowerSeries W := PowerSeries.mk fun j => if j = 0 then 0 else H 0 j with hb
  have hb0 : PowerSeries.constantCoeff b = 0 := by simp [hb]
  refine ⟨(a, b), hb0, hmk, fun t ht => le_antisymm ?_ ?_⟩
  · rw [gaussOrder_le_iff]
    intro F hF
    obtain ⟨H', hH', hmk'⟩ := exists_normalForm_rec ϖ e he F
    have huniq := normalForm_unique ϖ e he (PowerSeries.mk fun i => H' i 0)
      (PowerSeries.mk fun j => if j = 0 then 0 else H' 0 j) a b (by simp) hb0
      (by rw [hmk', hF, ← hmk])
    have hle := repGaussOrder_le_normalForm v (ϖ ^ e) e t he ht hπ F hH'
    rw [huniq.1, huniq.2] at hle
    exact hle
  · have := repGaussOrder_le_gaussOrder v (ϖ ^ e) e t (inU a + inV b)
    rwa [hmk] at this

theorem annulusWeight_midpoint (e t : ℕ) (ht1 : 1 ≤ t) (hte : t + 1 ≤ e) (d : Fin 2 →₀ ℕ) :
    annulusWeight e (t - 1) d + annulusWeight e (t + 1) d = annulusWeight e t d + annulusWeight e t d := by
  simp only [annulusWeight]
  have h1 : t - 1 + (t + 1) = t + t := by omega
  have h2 : e - (t - 1) + (e - (t + 1)) = (e - t) + (e - t) := by omega
  calc d 0 * (t - 1) + d 1 * (e - (t - 1)) + (d 0 * (t + 1) + d 1 * (e - (t + 1)))
      = d 0 * (t - 1 + (t + 1)) + d 1 * (e - (t - 1) + (e - (t + 1))) := by ring
    _ = d 0 * (t + t) + d 1 * ((e - t) + (e - t)) := by rw [h1, h2]
    _ = _ := by ring

theorem repGaussOrder_midpoint_concave (v : W → ℕ∞) (e t : ℕ) (ht1 : 1 ≤ t) (hte : t + 1 ≤ e)
    (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder v e (t - 1) F + repGaussOrder v e (t + 1) F ≤ repGaussOrder v e t F + repGaussOrder v e t F := by
  unfold repGaussOrder
  apply AnnulusSlope.iInf_midpoint_concave (fun d s => v (MvPowerSeries.coeff d F) + (annulusWeight e s d : ℕ∞)) t
  intro d
  rw [add_add_add_comm, ← Nat.cast_add, annulusWeight_midpoint e t ht1 hte d, Nat.cast_add, add_add_add_comm]

theorem gaussOrder_midpoint_concave' (v : AddValuation W ℕ∞) (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W]
    (e : ℕ) (he : 1 ≤ e) (hπ : ((e : ℕ) : ℕ∞) ≤ v (ϖ ^ e)) (t : ℕ) (ht1 : 1 ≤ t) (hte : t + 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) :
    gaussOrder v (ϖ ^ e) e (t - 1) x + gaussOrder v (ϖ ^ e) e (t + 1) x ≤
      gaussOrder v (ϖ ^ e) e t x + gaussOrder v (ϖ ^ e) e t x := by
  obtain ⟨ab, -, -, hg⟩ := exists_normalForm_gaussOrder_eq v ϖ e he hπ x
  rw [hg (t - 1) (by omega), hg (t + 1) hte, hg t (by omega)]
  exact repGaussOrder_midpoint_concave v e t ht1 hte _

theorem gaussOrder_midpoint_concave
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e t : ℕ) (ht1 : 1 ≤ t) (hte : t + 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e (t - 1) x +
        gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e (t + 1) x ≤
      gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t x +
        gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t x := by
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal W) W)
  have hπ : ((e : ℕ) : ℕ∞) ≤ IsDiscreteValuationRing.addVal W (ϖ ^ e) := by
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_eq_mul, mul_one]
  exact gaussOrder_midpoint_concave' _ ϖ e (by omega) hπ t ht1 hte x

end AnnulusStepA

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

open AnnulusNF AnnulusStepA

variable {W : Type u} [CommRing W]

@[scoped simp] theorem nfCoeff_negSucc (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    nfCoeff ab (Int.negSucc j) = PowerSeries.coeff (j + 1) ab.2 := rfl
@[scoped simp] theorem nfCoeff_natCast (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    nfCoeff ab (i : ℤ) = PowerSeries.coeff i ab.1 := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_negSucc (j : ℕ) : nfExponent (Int.negSucc j) = Finsupp.single 1 (j + 1) := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_natCast (i : ℕ) : nfExponent (i : ℤ) = Finsupp.single 0 i := rfl

theorem coeff_inU_add_inV (a b : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inU a + inV b) =
      (if d 1 = 0 then PowerSeries.coeff (d 0) a else 0) + (if d 0 = 0 then PowerSeries.coeff (d 1) b else 0) := by
  rw [map_add, coeff_inU, coeff_inV]

theorem coeff_nfExponent (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    MvPowerSeries.coeff (nfExponent n) (inU ab.1 + inV ab.2) = nfCoeff ab n := by
  cases n with
  | ofNat i =>
    rw [Int.ofNat_eq_natCast, nfExponent_natCast, nfCoeff_natCast, coeff_inU_add_inV]
    simp only [Finsupp.single_apply, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, if_true]
    by_cases hi : i = 0
    · subst hi; simp [hb]
    · simp [hi]
  | negSucc j =>
    rw [nfExponent_negSucc, nfCoeff_negSucc, coeff_inU_add_inV]
    simp [Finsupp.single_apply]

theorem termOrder_natCast (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    termOrder v E t ab (i : ℤ) = v (PowerSeries.coeff i ab.1) + ((i * t : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

theorem termOrder_negSucc (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    termOrder v E t ab (Int.negSucc j) = v (PowerSeries.coeff (j + 1) ab.2) + (((j + 1) * (E - t) : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

theorem repGaussOrder_normalForm_eq_iInf_termOrder
    (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    repGaussOrder v E t (inU ab.1 + inV ab.2) = ⨅ n : ℤ, termOrder v E t ab n := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    have := repGaussOrder_le v E t (inU ab.1 + inV ab.2) (nfExponent n)
    rwa [coeff_nfExponent ab hb n] at this
  · rw [le_repGaussOrder_iff]
    intro d
    by_cases h0 : d 0 = 0 <;> by_cases h1 : d 1 = 0
    · have hd : d = nfExponent ((0 : ℕ) : ℤ) := by
        rw [nfExponent_natCast]; ext k; fin_cases k <;> simp [h0, h1]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · obtain ⟨j, hj⟩ : ∃ j, d 1 = j + 1 := Nat.exists_eq_succ_of_ne_zero h1
      have hd : d = nfExponent (Int.negSucc j) := by
        rw [nfExponent_negSucc]; ext k; fin_cases k <;> simp [h0, hj]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · obtain ⟨i, hi⟩ : ∃ i, d 0 = i + 1 := Nat.exists_eq_succ_of_ne_zero h0
      have hd : d = nfExponent ((i + 1 : ℕ) : ℤ) := by
        rw [nfExponent_natCast]; ext k; fin_cases k <;> simp [h1, hi]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · rw [coeff_inU_add_inV, if_neg h1, if_neg h0, add_zero, hv0, top_add]
      exact le_top

theorem termOrder_succ_add (v : W → ℕ∞) (E t : ℕ) (hte : t + 1 ≤ E) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E (t + 1) ab n + ((-n).toNat : ℕ∞) = termOrder v E t ab n + (n.toNat : ℕ∞) := by
  cases n with
  | ofNat i =>
    simp only [Int.ofNat_eq_natCast, termOrder_natCast, Int.toNat_natCast]
    have : (-(i : ℤ)).toNat = 0 := by simp
    rw [this, Nat.cast_zero, add_zero, add_assoc, ← Nat.cast_add, Nat.mul_succ]
  | negSucc j =>
    have hn : (-(Int.negSucc j)).toNat = j + 1 := by simp
    rw [termOrder_negSucc, termOrder_negSucc, hn, Int.toNat_negSucc, Nat.cast_zero, add_zero,
      add_assoc, ← Nat.cast_add]
    have h1 : E - t = (E - (t + 1)) + 1 := by omega
    have h2 : (j + 1) * (E - (t + 1)) + (j + 1) = (j + 1) * (E - t) := by rw [h1]; ring
    rw [h2]

theorem mem_dominantIndices_iff (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices v E t ab ↔ termOrder v E t ab n = ⨅ m : ℤ, termOrder v E t ab m := by
  rw [dominantIndices, Set.mem_setOf_eq, repGaussOrder_normalForm_eq_iInf_termOrder v hv0 E t ab hb]

theorem dominantIndices_nonempty (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) : (dominantIndices v E t ab).Nonempty := by
  obtain ⟨n, hn⟩ := ciInf_mem (fun n : ℤ => termOrder v E t ab n)
  exact ⟨n, (mem_dominantIndices_iff v hv0 E t ab hb n).mpr hn⟩

theorem dominantIndices_bddBelow (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (hte : t < E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : (⨅ m : ℤ, termOrder v E t ab m) < ⊤) : BddBelow (dominantIndices v E t ab) := by
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  refine ⟨-(g : ℤ) - 1, fun n hn => ?_⟩
  rw [mem_dominantIndices_iff v hv0 E t ab hb] at hn
  by_contra hlt
  push Not at hlt
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = Int.negSucc j := Int.eq_negSucc_of_lt_zero (by omega)
  have hj : g + 1 ≤ j + 1 := by
    have : (Int.negSucc j : ℤ) = -(j : ℤ) - 1 := by rw [Int.negSucc_eq]; ring
    omega
  have h1 : (((j + 1) * (E - t) : ℕ) : ℕ∞) ≤ termOrder v E t ab (Int.negSucc j) := by
    rw [termOrder_negSucc]; exact le_add_self
  rw [hn, ← hg] at h1
  have : (j + 1) * (E - t) ≤ g := by exact_mod_cast h1
  have het : 1 ≤ E - t := by omega
  nlinarith

theorem dominantIndices_bddAbove (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht0 : 0 < t)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : (⨅ m : ℤ, termOrder v E t ab m) < ⊤) : BddAbove (dominantIndices v E t ab) := by
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  refine ⟨(g : ℤ), fun n hn => ?_⟩
  rw [mem_dominantIndices_iff v hv0 E t ab hb] at hn
  by_contra hlt
  push Not at hlt
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = (i : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hi : g + 1 ≤ i := by omega
  have h1 : ((i * t : ℕ) : ℕ∞) ≤ termOrder v E t ab i := by rw [termOrder_natCast]; exact le_add_self
  rw [hn, ← hg] at h1
  have : i * t ≤ g := by exact_mod_cast h1
  nlinarith

theorem iInf_termOrder_lt_top (v : W → ℕ∞) (hv : ∀ c, v c = ⊤ → c = 0) (π : W) (E t : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) : (⨅ n : ℤ, termOrder v E t ab n) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  apply hx
  have hall : ∀ n, termOrder v E t ab n = ⊤ := fun n => top_le_iff.mp (htop ▸ iInf_le _ n)
  have hcoef : ∀ n, nfCoeff ab n = 0 := fun n => by
    apply hv
    have := hall n
    rw [termOrder] at this
    exact (WithTop.add_eq_top.mp this).resolve_right (ENat.coe_ne_top _)
  have ha : ab.1 = 0 := by
    ext i; simpa using hcoef (i : ℤ)
  have hb' : ab.2 = 0 := by
    ext j
    cases j with
    | zero => simpa using hb
    | succ j => simpa using hcoef (Int.negSucc j)
  have h0 : inU ab.1 + inV ab.2 = 0 := by
    ext d; rw [coeff_inU_add_inV, ha, hb']; simp
  rw [h0, map_zero]

section Scaled
variable [IsDomain W] [IsDiscreteValuationRing W]

noncomputable abbrev vq (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (q : ℕ) : W → ℕ∞ :=
  fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w

theorem vq_zero (q : ℕ) (hq : 1 ≤ q) : vq W q 0 = ⊤ := by
  simp only [vq, AddValuation.map_zero]
  exact WithTop.mul_top (Nat.cast_ne_zero.mpr (by omega))

theorem vq_eq_top (q : ℕ) (c : W) (h : vq W q c = ⊤) : c = 0 := by
  simp only [vq] at h
  rcases WithTop.mul_eq_top_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact IsDiscreteValuationRing.addVal_eq_top_iff.mp h2
  · exact absurd h1 (ENat.coe_ne_top q)

noncomputable def vqAddVal (W : Type u) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (q : ℕ) (hq : 1 ≤ q) :
    AddValuation W ℕ∞ :=
  AddValuation.of (vq W q) (vq_zero q hq) (by simp [vq])
    (fun x y => by
      simp only [vq]
      rw [← mul_min]
      exact mul_le_mul_right (AddValuation.map_add _ x y) _)
    (fun x y => by simp only [vq, AddValuation.map_mul, mul_add])

theorem vqAddVal_apply (q : ℕ) (hq : 1 ≤ q) (w : W) : vqAddVal W q hq w = vq W q w := rfl

theorem coe_vqAddVal (q : ℕ) (hq : 1 ≤ q) : (vqAddVal W q hq : W → ℕ∞) = vq W q := rfl

theorem gaussOrder_scaled_eq_repGaussOrder_normalForm [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e))
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp : p ≤ q * e) :
    gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x =
      repGaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p (inU ab.1 + inV ab.2) := by
  classical
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal W) W)
  set v : AddValuation W ℕ∞ := vqAddVal W q hq with hvdef
  have hv : (v : W → ℕ∞) = fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w := rfl
  rw [← hv]
  have hqe : 1 ≤ q * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hπ : (((q * e : ℕ) : ℕ∞)) ≤ v (ϖ ^ e) := by
    change ((q * e : ℕ) : ℕ∞) ≤ (q : ℕ∞) * IsDiscreteValuationRing.addVal W (ϖ ^ e)
    rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_eq_mul, mul_one,
      Nat.cast_mul]
  subst habx
  refine le_antisymm ?_ (repGaussOrder_le_gaussOrder v (ϖ ^ e) (q * e) p _)
  rw [gaussOrder_le_iff]
  intro F hF
  obtain ⟨H', hH', hmk'⟩ := exists_normalForm_rec ϖ e he F
  have huniq := normalForm_unique ϖ e he (PowerSeries.mk fun i => H' i 0)
    (PowerSeries.mk fun j => if j = 0 then 0 else H' 0 j) ab.1 ab.2 (by simp) hb (by rw [hmk', hF])
  have hle := repGaussOrder_le_normalForm v (ϖ ^ e) (q * e) p hqe hp hπ F hH'
  rw [huniq.1, huniq.2] at hle
  exact hle

theorem gaussOrder_scaled_eq_iInf_termOrder [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e))
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp : p ≤ q * e) :
    gaussOrder (vq W q) (ϖ ^ e) (q * e) p x = ⨅ n : ℤ, termOrder (vq W q) (q * e) p ab n := by
  rw [show vq W q = fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w from rfl,
    gaussOrder_scaled_eq_repGaussOrder_normalForm ϖ hϖ e he q hq x ab hb habx p hp,
    repGaussOrder_normalForm_eq_iInf_termOrder _ (vq_zero q hq) _ p ab hb]

theorem dominantIndices_finite_nonempty [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp1 : 1 ≤ p) (hpe : p + 1 ≤ q * e) :
    (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab).Finite ∧
      (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab).Nonempty := by
  change (dominantIndices (vq W q) (q * e) p ab).Finite ∧ (dominantIndices (vq W q) (q * e) p ab).Nonempty
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := habx ▸ hx
  have hfin := iInf_termOrder_lt_top (vq W q) (vq_eq_top q) (ϖ ^ e) (q * e) p ab hb hx'
  obtain ⟨lb, hlb⟩ := dominantIndices_bddBelow (vq W q) (vq_zero q hq) (q * e) p (by omega) ab hb hfin
  obtain ⟨ub, hub⟩ := dominantIndices_bddAbove (vq W q) (vq_zero q hq) (q * e) p (by omega) ab hb hfin
  exact ⟨(Set.finite_Icc lb ub).subset fun n hn => ⟨hlb hn, hub hn⟩,
    dominantIndices_nonempty _ (vq_zero q hq) _ p ab hb⟩

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem toNat_sub_toNat_of_add_eq {A B : ℕ∞} (hA : A < ⊤) (hB : B < ⊤) {m n : ℕ}
    (h : A + (m : ℕ∞) = B + (n : ℕ∞)) : (A.toNat : ℤ) - B.toNat = n - m := by
  obtain ⟨a, rfl⟩ := ENat.ne_top_iff_exists.mp hA.ne
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hB.ne
  have : a + m = b + n := by exact_mod_cast h
  simp only [ENat.toNat_coe]
  omega

theorem gaussOrder_succ_sub_eq_sInf_dominantIndices [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hpe : p + 1 ≤ q * e)
    (hright : sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) ∈
      dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p + 1) ab) :
    ((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ) -
        (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat =
      sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) := by
  change ((gaussOrder (vq W q) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ) - (gaussOrder (vq W q) (ϖ ^ e) (q * e) p x).toNat
    = sInf (dominantIndices (vq W q) (q * e) p ab)
  change sInf (dominantIndices (vq W q) (q * e) p ab) ∈ dominantIndices (vq W q) (q * e) (p + 1) ab at hright
  set m := sInf (dominantIndices (vq W q) (q * e) p ab)
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := habx ▸ hx
  have h0 := vq_zero (W := W) q hq
  have hfin_t := iInf_termOrder_lt_top (vq W q) (vq_eq_top q) (ϖ ^ e) (q * e) p ab hb hx'
  have hfin_s := iInf_termOrder_lt_top (vq W q) (vq_eq_top q) (ϖ ^ e) (q * e) (p + 1) ab hb hx'
  have hm : m ∈ dominantIndices (vq W q) (q * e) p ab :=
    Int.csInf_mem (dominantIndices_nonempty _ h0 _ p ab hb) (dominantIndices_bddBelow _ h0 _ p (by omega) ab hb hfin_t)
  rw [mem_dominantIndices_iff _ h0 _ _ ab hb] at hm hright
  rw [gaussOrder_scaled_eq_iInf_termOrder ϖ hϖ e he q hq x ab hb habx (p + 1) hpe,
    gaussOrder_scaled_eq_iInf_termOrder ϖ hϖ e he q hq x ab hb habx p (by omega), ← hm, ← hright]
  have hslope := termOrder_succ_add (vq W q) (q * e) p hpe ab m
  have := toNat_sub_toNat_of_add_eq (hright ▸ hfin_s) (hm ▸ hfin_t) hslope
  rw [this]; omega

theorem gaussOrder_sub_pred_eq_sSup_dominantIndices [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp1 : 1 ≤ p) (hpe : p ≤ q * e)
    (hleft : sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) ∈
      dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p - 1) ab) :
    ((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ) -
        (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x).toNat =
      sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) := by
  change ((gaussOrder (vq W q) (ϖ ^ e) (q * e) p x).toNat : ℤ) - (gaussOrder (vq W q) (ϖ ^ e) (q * e) (p - 1) x).toNat
    = sSup (dominantIndices (vq W q) (q * e) p ab)
  change sSup (dominantIndices (vq W q) (q * e) p ab) ∈ dominantIndices (vq W q) (q * e) (p - 1) ab at hleft
  set M := sSup (dominantIndices (vq W q) (q * e) p ab)
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := habx ▸ hx
  have h0 := vq_zero (W := W) q hq
  have hfin_t := iInf_termOrder_lt_top (vq W q) (vq_eq_top q) (ϖ ^ e) (q * e) p ab hb hx'
  have hfin_p := iInf_termOrder_lt_top (vq W q) (vq_eq_top q) (ϖ ^ e) (q * e) (p - 1) ab hb hx'
  have hM : M ∈ dominantIndices (vq W q) (q * e) p ab :=
    Int.csSup_mem (dominantIndices_nonempty _ h0 _ p ab hb) (dominantIndices_bddAbove _ h0 _ p (by omega) ab hb hfin_t)
  rw [mem_dominantIndices_iff _ h0 _ _ ab hb] at hM hleft
  rw [gaussOrder_scaled_eq_iInf_termOrder ϖ hϖ e he q hq x ab hb habx p hpe,
    gaussOrder_scaled_eq_iInf_termOrder ϖ hϖ e he q hq x ab hb habx (p - 1) (by omega), ← hM, ← hleft]
  have hp' : p - 1 + 1 = p := by omega
  have hslope := termOrder_succ_add (vq W q) (q * e) (p - 1) (by omega) ab M
  rw [hp'] at hslope
  have := toNat_sub_toNat_of_add_eq (hM ▸ hfin_t) (hleft ▸ hfin_p) hslope
  rw [this]; omega

theorem gaussOrder_slopeDrop_eq_circleIndexDrop [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp1 : 1 ≤ p) (hpe : p + 1 ≤ q * e)
    (hright : sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) ∈
      dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p + 1) ab)
    (hleft : sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) ∈
      dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p - 1) ab) :
    (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat : ℤ) -
          (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x).toNat) -
        (((gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ) -
          (gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x).toNat) =
      circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab := by
  rw [gaussOrder_sub_pred_eq_sSup_dominantIndices ϖ hϖ e he q hq x hx ab hb habx p hp1 (by omega) hleft,
    gaussOrder_succ_sub_eq_sInf_dominantIndices ϖ hϖ e he q hq x hx ab hb habx p hpe hright, circleIndexDrop]
  obtain ⟨hfin, m, hm⟩ := dominantIndices_finite_nonempty ϖ hϖ e he q hq x hx ab hb habx p hp1 hpe
  have hle := le_trans (csInf_le hfin.bddBelow hm) (le_csSup hfin.bddAbove hm)
  omega

end Scaled

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

section ScaledCD
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem iInf_termOrder_succ_add_le (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E p : ℕ) (hpe : p + 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (m : ℤ) (hm : m ∈ dominantIndices v E p ab) :
    (⨅ n : ℤ, termOrder v E (p + 1) ab n) + ((-m).toNat : ℕ∞) ≤ (⨅ n : ℤ, termOrder v E p ab n) + (m.toNat : ℕ∞) := by
  rw [mem_dominantIndices_iff v hv0 E p ab hb] at hm
  rw [← hm, ← termOrder_succ_add v E p hpe ab m]
  exact add_le_add (iInf_le (fun n : ℤ => termOrder v E (p + 1) ab n) m) le_rfl

theorem iInf_termOrder_pred_add_le (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E p : ℕ) (hp1 : 1 ≤ p) (hpe : p ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (M : ℤ) (hM : M ∈ dominantIndices v E p ab) :
    (⨅ n : ℤ, termOrder v E (p - 1) ab n) + (M.toNat : ℕ∞) ≤ (⨅ n : ℤ, termOrder v E p ab n) + ((-M).toNat : ℕ∞) := by
  rw [mem_dominantIndices_iff v hv0 E p ab hb] at hM
  have h := termOrder_succ_add v E (p - 1) (by omega) ab M
  rw [show p - 1 + 1 = p by omega] at h
  rw [← hM, h]
  exact add_le_add (iInf_le (fun n : ℤ => termOrder v E (p - 1) ab n) M) le_rfl

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem enat_chord_arith {A B C : ℕ∞} (hB : B < ⊤) {mp mn Mp Mn : ℕ}
    (h1 : C + (mn : ℕ∞) ≤ B + (mp : ℕ∞)) (h2 : A + (Mp : ℕ∞) ≤ B + (Mn : ℕ∞)) (hmM : (mp : ℤ) - mn ≤ Mp - Mn) :
    A + C + (((Mp : ℤ) - Mn - (mp - mn)).toNat : ℕ∞) ≤ B + B := by
  obtain ⟨b, rfl⟩ := ENat.ne_top_iff_exists.mp hB.ne
  have hA : A < ⊤ := lt_of_le_of_lt le_self_add (lt_of_le_of_lt h2 (by simp [← Nat.cast_add]))
  have hC : C < ⊤ := lt_of_le_of_lt le_self_add (lt_of_le_of_lt h1 (by simp [← Nat.cast_add]))
  obtain ⟨a, rfl⟩ := ENat.ne_top_iff_exists.mp hA.ne
  obtain ⟨c, rfl⟩ := ENat.ne_top_iff_exists.mp hC.ne
  have e1 : c + mn ≤ b + mp := by exact_mod_cast h1
  have e2 : a + Mp ≤ b + Mn := by exact_mod_cast h2
  have : a + c + ((Mp : ℤ) - Mn - (mp - mn)).toNat ≤ b + b := by omega
  exact_mod_cast this

theorem gaussOrder_second_difference_le [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp1 : 1 ≤ p) (hpe : p + 1 ≤ q * e) :
    gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x +
        gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x +
        (circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab : ℕ∞) ≤
      gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x +
        gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x := by
  change gaussOrder (vq W q) (ϖ ^ e) (q * e) (p - 1) x + gaussOrder (vq W q) (ϖ ^ e) (q * e) (p + 1) x +
      (circleIndexDrop (vq W q) (q * e) p ab : ℕ∞) ≤ gaussOrder (vq W q) (ϖ ^ e) (q * e) p x + gaussOrder (vq W q) (ϖ ^ e) (q * e) p x
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := habx ▸ hx
  have h0 := vq_zero (W := W) q hq
  obtain ⟨hfin, hne⟩ := dominantIndices_finite_nonempty ϖ hϖ e he q hq x hx ab hb habx p hp1 hpe
  change (dominantIndices (vq W q) (q * e) p ab).Finite at hfin
  change (dominantIndices (vq W q) (q * e) p ab).Nonempty at hne
  set m := sInf (dominantIndices (vq W q) (q * e) p ab)
  set M := sSup (dominantIndices (vq W q) (q * e) p ab)
  have hm : m ∈ _ := Int.csInf_mem hne hfin.bddBelow
  have hM : M ∈ _ := Int.csSup_mem hne hfin.bddAbove
  obtain ⟨k, hk⟩ := hne
  have hmM : m ≤ M := le_trans (csInf_le hfin.bddBelow hk) (le_csSup hfin.bddAbove hk)
  rw [gaussOrder_scaled_eq_iInf_termOrder ϖ hϖ e he q hq x ab hb habx (p - 1) (by omega),
    gaussOrder_scaled_eq_iInf_termOrder ϖ hϖ e he q hq x ab hb habx (p + 1) hpe,
    gaussOrder_scaled_eq_iInf_termOrder ϖ hϖ e he q hq x ab hb habx p (by omega), circleIndexDrop]
  have h1 := iInf_termOrder_succ_add_le (vq W q) h0 (q * e) p hpe ab hb m hm
  have h2 := iInf_termOrder_pred_add_le (vq W q) h0 (q * e) p hp1 (by omega) ab hb M hM
  have hfin_t := iInf_termOrder_lt_top (vq W q) (vq_eq_top q) (ϖ ^ e) (q * e) p ab hb hx'
  have key := enat_chord_arith hfin_t h1 h2 (by omega)
  have hrw : ((M.toNat : ℤ) - (-M).toNat - ((m.toNat : ℤ) - (-m).toNat)).toNat = (M - m).toNat := by omega
  rw [hrw] at key
  exact key

theorem gaussOrder_second_difference_eq [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) (p : ℕ) (hp1 : 1 ≤ p) (hpe : p + 1 ≤ q * e)
    (hright : sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) ∈
      dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p + 1) ab)
    (hleft : sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) ∈
      dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (p - 1) ab) :
    gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p - 1) x +
        gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) (p + 1) x +
        (circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab : ℕ∞) =
      gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x +
        gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) p x := by
  have hf := gaussOrder_slopeDrop_eq_circleIndexDrop ϖ hϖ e he q hq x hx ab hb habx p hp1 hpe hright hleft
  change gaussOrder (vq W q) (ϖ ^ e) (q * e) (p - 1) x + gaussOrder (vq W q) (ϖ ^ e) (q * e) (p + 1) x +
      (circleIndexDrop (vq W q) (q * e) p ab : ℕ∞) = gaussOrder (vq W q) (ϖ ^ e) (q * e) p x + gaussOrder (vq W q) (ϖ ^ e) (q * e) p x
  change (((gaussOrder (vq W q) (ϖ ^ e) (q * e) p x).toNat : ℤ) - (gaussOrder (vq W q) (ϖ ^ e) (q * e) (p - 1) x).toNat)
    - (((gaussOrder (vq W q) (ϖ ^ e) (q * e) (p + 1) x).toNat : ℤ) - (gaussOrder (vq W q) (ϖ ^ e) (q * e) p x).toNat)
    = circleIndexDrop (vq W q) (q * e) p ab at hf
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := habx ▸ hx
  have fin : ∀ s, s ≤ q * e → gaussOrder (vq W q) (ϖ ^ e) (q * e) s x < ⊤ := fun s hs => by
    rw [gaussOrder_scaled_eq_iInf_termOrder ϖ hϖ e he q hq x ab hb habx s hs]
    exact iInf_termOrder_lt_top (vq W q) (vq_eq_top q) (ϖ ^ e) (q * e) s ab hb hx'
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (fin (p - 1) (by omega)).ne
  obtain ⟨b, hb2⟩ := ENat.ne_top_iff_exists.mp (fin p (by omega)).ne
  obtain ⟨c, hc⟩ := ENat.ne_top_iff_exists.mp (fin (p + 1) hpe).ne
  rw [← ha, ← hb2, ← hc] at hf ⊢
  simp only [ENat.toNat_coe] at hf
  have : a + c + circleIndexDrop (vq W q) (q * e) p ab = b + b := by omega
  exact_mod_cast this

end ScaledCD
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

namespace P1Arch

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

def IsPureSlope (r : ℕ) (n : W) (d : ℕ) (f : Polynomial W) : Prop :=
  f.Monic ∧ f.natDegree = d ∧
    (∀ i : ℕ, i ≤ d → ((d - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W n ≤
      (r : ℕ∞) * IsDiscreteValuationRing.addVal W (f.coeff i)) ∧
    ((d : ℕ∞) * IsDiscreteValuationRing.addVal W n = (r : ℕ∞) * IsDiscreteValuationRing.addVal W (f.coeff 0))

end P1Arch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

section UPoly

open Polynomial

variable {W : Type u} [CommRing W]

theorem inV_zero : inV (0 : PowerSeries W) = 0 := by
  ext d; rw [coeff_inV]; simp

theorem inU_coe_polynomial (p : W[X]) :
    inU (p : PowerSeries W) = aeval (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) p := by
  classical
  ext d
  rw [coeff_inU, Polynomial.coeff_coe, aeval_eq_sum_range, map_sum]
  simp only [map_smul, MvPowerSeries.coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h1 : d 1 = 0
  · rw [if_pos h1]
    have hd : ∀ i, (d = Finsupp.single 0 i ↔ d 0 = i) := by
      intro i
      constructor
      · rintro rfl; simp
      · intro h; ext k; fin_cases k <;> simp [h, h1]
    simp_rw [hd]
    rw [Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · rw [Finset.mem_range, not_lt] at hmem
      exact coeff_eq_zero_of_natDegree_lt (show p.natDegree < d 0 by omega)
  · rw [if_neg h1]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg]
    rintro rfl
    simp at h1

theorem mk_normalForm_polynomial (π : W) (p : W[X]) :
    mk π (inU (p : PowerSeries W) + inV (0 : PowerSeries W)) = aeval (U π) p := by
  rw [inV_zero, add_zero, inU_coe_polynomial]
  change Ideal.Quotient.mkₐ W _ (aeval (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) p) =
    aeval (Ideal.Quotient.mkₐ W _ (MvPowerSeries.X 0)) p
  rw [aeval_algHom_apply]

theorem constantCoeff_normalForm_polynomial_snd :
    PowerSeries.constantCoeff ((((0 : PowerSeries W)) : PowerSeries W)) = 0 := map_zero _

theorem termOrder_polynomial_natCast (v : W → ℕ∞) (E t : ℕ) (p : W[X]) (i : ℕ) :
    termOrder v E t ((p : PowerSeries W), 0) (i : ℤ) = v (p.coeff i) + ((i * t : ℕ) : ℕ∞) := by
  rw [termOrder_natCast, Polynomial.coeff_coe]

theorem termOrder_polynomial_negSucc (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (p : W[X]) (j : ℕ) :
    termOrder v E t ((p : PowerSeries W), 0) (Int.negSucc j) = ⊤ := by
  rw [termOrder_negSucc]
  simp [hv0]

theorem termOrder_polynomial_of_natDegree_lt (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (p : W[X]) (i : ℕ)
    (hi : p.natDegree < i) : termOrder v E t ((p : PowerSeries W), 0) (i : ℤ) = ⊤ := by
  rw [termOrder_polynomial_natCast, coeff_eq_zero_of_natDegree_lt hi, hv0, top_add]

theorem iInf_termOrder_polynomial (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (p : W[X]) :
    (⨅ n : ℤ, termOrder v E t ((p : PowerSeries W), 0) n) = ⨅ i : ℕ, (v (p.coeff i) + ((i * t : ℕ) : ℕ∞)) := by
  apply le_antisymm
  · exact le_iInf fun i => (iInf_le _ (i : ℤ)).trans_eq (termOrder_polynomial_natCast v E t p i)
  · refine le_iInf fun n => ?_
    cases n with
    | ofNat i => rw [Int.ofNat_eq_natCast, termOrder_polynomial_natCast]; exact iInf_le _ i
    | negSucc j => rw [termOrder_polynomial_negSucc v hv0]; exact le_top

variable [IsDomain W] [IsDiscreteValuationRing W]

theorem gaussOrder_scaled_aeval_U [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (q : ℕ) (hq : 1 ≤ q) (p : W[X]) (t : ℕ) (ht : t ≤ q * e) :
    gaussOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (ϖ ^ e) (q * e) t (aeval (U (ϖ ^ e)) p) =
      ⨅ i : ℕ, ((q : ℕ∞) * IsDiscreteValuationRing.addVal W (p.coeff i) + ((i * t : ℕ) : ℕ∞)) := by
  change gaussOrder (vq W q) (ϖ ^ e) (q * e) t (aeval (U (ϖ ^ e)) p) = ⨅ i : ℕ, (vq W q (p.coeff i) + ((i * t : ℕ) : ℕ∞))
  rw [gaussOrder_scaled_eq_iInf_termOrder ϖ hϖ e he q hq _ ((p : PowerSeries W), 0) (map_zero _)
    (mk_normalForm_polynomial _ p) t ht, iInf_termOrder_polynomial _ (vq_zero q hq)]

end UPoly
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section PureSlope

open Polynomial IsDiscreteValuationRing

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
variable {r : ℕ} {N : W} {d : ℕ} {p : W[X]}

theorem termOrder_vq_polynomial (q E t : ℕ) (p : W[X]) (i : ℕ) :
    termOrder (vq W q) E t ((p : PowerSeries W), 0) (i : ℤ) = (q : ℕ∞) * addVal W (p.coeff i) + ((i * t : ℕ) : ℕ∞) :=
  termOrder_polynomial_natCast _ E t p i

theorem termOrder_pure_natDegree (hp : P1Arch.IsPureSlope r N d p) (q E t : ℕ) :
    termOrder (vq W q) E t ((p : PowerSeries W), 0) (d : ℤ) = ((d * t : ℕ) : ℕ∞) := by
  rw [termOrder_vq_polynomial]
  have : p.coeff d = 1 := by rw [← hp.2.1]; exact hp.1
  rw [this, addVal_one, mul_zero, zero_add]

theorem termOrder_pure_cases (hp : P1Arch.IsPureSlope r N d p) {ν : ℕ} (hν : addVal W N = ν)
    (q : ℕ) (hq : 1 ≤ q) (E t i : ℕ) (hi : i ≤ d) :
    termOrder (vq W q) E t ((p : PowerSeries W), 0) (i : ℤ) = ⊤ ∨
      ∃ w : ℕ, termOrder (vq W q) E t ((p : PowerSeries W), 0) (i : ℤ) = ((q * w + i * t : ℕ) : ℕ∞) ∧
        (d - i) * ν ≤ r * w := by
  rw [termOrder_vq_polynomial]
  by_cases hc : p.coeff i = 0
  · left
    have hq0 : (q : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hqtop : (q : ℕ∞) * ⊤ = ⊤ := WithTop.mul_top hq0
    rw [hc, addVal_zero, hqtop, top_add]
  · right
    obtain ⟨w, hw⟩ := ENat.ne_top_iff_exists.mp (fun h => hc (addVal_eq_top_iff.mp h))
    refine ⟨w, by rw [← hw]; push_cast; ring, ?_⟩
    have := hp.2.2.1 i hi
    rw [hν, ← hw] at this
    exact_mod_cast this

theorem termOrder_pure_zero (hp : P1Arch.IsPureSlope r N d p) {ν : ℕ} (hν : addVal W N = ν) (hr : 1 ≤ r)
    (q E t : ℕ) :
    ∃ w₀ : ℕ, termOrder (vq W q) E t ((p : PowerSeries W), 0) ((0 : ℕ) : ℤ) = ((q * w₀ : ℕ) : ℕ∞) ∧ r * w₀ = d * ν := by
  rw [termOrder_vq_polynomial]
  have h0 := hp.2.2.2
  rw [hν] at h0
  have hfin : addVal W (p.coeff 0) ≠ ⊤ := by
    intro htop
    have hr0 : (r : ℕ∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hrtop : (r : ℕ∞) * ⊤ = ⊤ := WithTop.mul_top hr0
    rw [htop, hrtop] at h0
    exact WithTop.natCast_ne_top (d * ν) (by exact_mod_cast h0)
  obtain ⟨w₀, hw⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨w₀, by rw [← hw]; push_cast; ring, ?_⟩
  rw [← hw] at h0
  have : ((d * ν : ℕ) : ℕ∞) = ((r * w₀ : ℕ) : ℕ∞) := by push_cast; exact h0
  exact_mod_cast this.symm

theorem min_termOrder_le_of_pure (hp : P1Arch.IsPureSlope r N d p) (hN : N ≠ 0) (hr : 1 ≤ r)
    (q : ℕ) (hq : 1 ≤ q) (E t : ℕ) (n : ℤ) :
    min (termOrder (vq W q) E t ((p : PowerSeries W), 0) ((0 : ℕ) : ℤ))
        (termOrder (vq W q) E t ((p : PowerSeries W), 0) (d : ℤ)) ≤
      termOrder (vq W q) E t ((p : PowerSeries W), 0) n := by
  obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.mp (fun h => hN (addVal_eq_top_iff.mp h))
  have hν' : addVal W N = ν := hν.symm
  obtain ⟨w₀, h0, hw₀⟩ := termOrder_pure_zero hp hν' hr q E t
  have hd := termOrder_pure_natDegree hp q E t
  cases n with
  | negSucc j => rw [termOrder_polynomial_negSucc _ (vq_zero q hq)]; exact le_top
  | ofNat i =>
    rw [Int.ofNat_eq_natCast]
    by_cases hi : i ≤ d
    · rcases termOrder_pure_cases hp hν' q hq E t i hi with htop | ⟨w, hw, hpur⟩
      · rw [htop]; exact le_top
      · rw [h0, hd, hw]
        obtain ⟨k, rfl⟩ : ∃ k, d = i + k := ⟨d - i, by omega⟩
        rw [Nat.add_sub_cancel_left] at hpur
        by_cases hcase : q * ν ≤ r * t
        · apply min_le_of_left_le
          have h1 : q * (k * ν) ≤ q * (r * w) := Nat.mul_le_mul_left q hpur
          have h2 : i * (q * ν) ≤ i * (r * t) := Nat.mul_le_mul_left i hcase
          have : r * (q * w₀) ≤ r * (q * w + i * t) := by nlinarith
          exact_mod_cast Nat.le_of_mul_le_mul_left this (by omega)
        · apply min_le_of_right_le
          push Not at hcase
          have h1 : q * (k * ν) ≤ q * (r * w) := Nat.mul_le_mul_left q hpur
          have h2 : k * (r * t) ≤ k * (q * ν) := Nat.mul_le_mul_left k hcase.le
          have : r * ((i + k) * t) ≤ r * (q * w + i * t) := by nlinarith
          exact_mod_cast Nat.le_of_mul_le_mul_left this (by omega)
    · rw [termOrder_polynomial_of_natDegree_lt _ (vq_zero q hq) E t p i (by rw [hp.2.1]; omega)]
      exact le_top

theorem iInf_termOrder_pure (hp : P1Arch.IsPureSlope r N d p) (hN : N ≠ 0) (hr : 1 ≤ r)
    (q : ℕ) (hq : 1 ≤ q) (E t : ℕ) :
    (⨅ n : ℤ, termOrder (vq W q) E t ((p : PowerSeries W), 0) n) =
      min (termOrder (vq W q) E t ((p : PowerSeries W), 0) ((0 : ℕ) : ℤ))
        (termOrder (vq W q) E t ((p : PowerSeries W), 0) (d : ℤ)) :=
  le_antisymm (le_min (iInf_le _ _) (iInf_le _ _)) (le_iInf (min_termOrder_le_of_pure hp hN hr q hq E t))

theorem mem_dominantIndices_pure_iff (hp : P1Arch.IsPureSlope r N d p) (hN : N ≠ 0) (hr : 1 ≤ r)
    (q : ℕ) (hq : 1 ≤ q) (E t : ℕ) (n : ℤ) :
    n ∈ dominantIndices (vq W q) E t ((p : PowerSeries W), 0) ↔
      termOrder (vq W q) E t ((p : PowerSeries W), 0) n =
        min (termOrder (vq W q) E t ((p : PowerSeries W), 0) ((0 : ℕ) : ℤ))
          (termOrder (vq W q) E t ((p : PowerSeries W), 0) (d : ℤ)) := by
  rw [mem_dominantIndices_iff _ (vq_zero q hq) E t _ (map_zero _), iInf_termOrder_pure hp hN hr q hq E t]

theorem mem_Icc_of_mem_dominantIndices_pure (hp : P1Arch.IsPureSlope r N d p) (hN : N ≠ 0) (hr : 1 ≤ r)
    (q : ℕ) (hq : 1 ≤ q) (E t : ℕ) (n : ℤ) (hn : n ∈ dominantIndices (vq W q) E t ((p : PowerSeries W), 0)) :
    0 ≤ n ∧ n ≤ d := by
  rw [mem_dominantIndices_pure_iff hp hN hr q hq E t] at hn
  have hfin : termOrder (vq W q) E t ((p : PowerSeries W), 0) n < ⊤ := by
    rw [hn]
    exact lt_of_le_of_lt (min_le_right _ _) (by rw [termOrder_pure_natDegree hp]; exact WithTop.coe_lt_top _)
  cases n with
  | negSucc j => rw [termOrder_polynomial_negSucc _ (vq_zero q hq)] at hfin; exact absurd hfin (lt_irrefl _)
  | ofNat i =>
    rw [Int.ofNat_eq_natCast] at hfin ⊢
    refine ⟨by omega, ?_⟩
    by_contra h
    rw [termOrder_polynomial_of_natDegree_lt _ (vq_zero q hq) E t p i (by rw [hp.2.1]; omega)] at hfin
    exact lt_irrefl _ hfin

theorem dominantIndices_polynomial_pure (hp : P1Arch.IsPureSlope r N d p) (hN : N ≠ 0) (hr : 1 ≤ r)
    (q : ℕ) (hq : 1 ≤ q) (E t : ℕ) :
    ((((t * r : ℕ) : ℕ∞) = (q : ℕ∞) * addVal W N) →
        ((0 : ℕ) : ℤ) ∈ dominantIndices (vq W q) E t ((p : PowerSeries W), 0) ∧
          (d : ℤ) ∈ dominantIndices (vq W q) E t ((p : PowerSeries W), 0)) ∧
    ((((t * r : ℕ) : ℕ∞) < (q : ℕ∞) * addVal W N) →
        dominantIndices (vq W q) E t ((p : PowerSeries W), 0) = {(d : ℤ)}) ∧
    (((q : ℕ∞) * addVal W N < ((t * r : ℕ) : ℕ∞)) →
        dominantIndices (vq W q) E t ((p : PowerSeries W), 0) = {((0 : ℕ) : ℤ)}) := by
  obtain ⟨ν, hν⟩ := ENat.ne_top_iff_exists.mp (fun h => hN (addVal_eq_top_iff.mp h))
  have hν' : addVal W N = ν := hν.symm
  obtain ⟨w₀, h0, hw₀⟩ := termOrder_pure_zero hp hν' hr q E t
  have hd := termOrder_pure_natDegree hp q E t
  set D := dominantIndices (vq W q) E t ((p : PowerSeries W), 0) with hD
  have hmem := mem_dominantIndices_pure_iff hp hN hr q hq E t
  have hIcc := mem_Icc_of_mem_dominantIndices_pure hp hN hr q hq E t

  have hdom : ∀ n ∈ D, ∃ i : ℕ, n = (i : ℤ) ∧ i ≤ d ∧ ∃ w : ℕ, (d - i) * ν ≤ r * w ∧
      q * w + i * t ≤ q * w₀ ∧ q * w + i * t ≤ d * t := by
    intro n hn
    obtain ⟨h0n, hnd⟩ := hIcc n hn
    rw [hD, hmem] at hn
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = (i : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg h0n).symm⟩
    have hid : i ≤ d := by exact_mod_cast hnd
    refine ⟨i, rfl, hid, ?_⟩
    rcases termOrder_pure_cases hp hν' q hq E t i hid with htop | ⟨w, hw, hpur⟩
    · exfalso
      have : min (termOrder (vq W q) E t ((p : PowerSeries W), 0) ((0 : ℕ) : ℤ))
          (termOrder (vq W q) E t ((p : PowerSeries W), 0) (d : ℤ)) < ⊤ :=
        lt_of_le_of_lt (min_le_right _ _) (by rw [hd]; exact WithTop.coe_lt_top _)
      rw [← hn, htop] at this
      exact lt_irrefl _ this
    · refine ⟨w, hpur, ?_, ?_⟩
      · have := (hn.le.trans (min_le_left _ _))
        rw [hw, h0] at this
        exact_mod_cast this
      · have := (hn.le.trans (min_le_right _ _))
        rw [hw, hd] at this
        exact_mod_cast this
  refine ⟨fun heq => ?_, fun hlt => ?_, fun hgt => ?_⟩
  ·
    rw [hν', ← Nat.cast_mul, Nat.cast_inj] at heq
    have h0d : termOrder (vq W q) E t ((p : PowerSeries W), 0) ((0 : ℕ) : ℤ) =
        termOrder (vq W q) E t ((p : PowerSeries W), 0) (d : ℤ) := by
      rw [h0, hd, Nat.cast_inj]
      apply Nat.eq_of_mul_eq_mul_left (show 0 < r by omega)
      calc r * (q * w₀) = q * (r * w₀) := by ring
        _ = q * (d * ν) := by rw [hw₀]
        _ = d * (q * ν) := by ring
        _ = d * (t * r) := by rw [heq]
        _ = r * (d * t) := by ring
    exact ⟨by rw [hD, hmem, h0d, min_self], by rw [hD, hmem, h0d, min_self]⟩
  ·
    rw [hν', ← Nat.cast_mul, Nat.cast_lt] at hlt
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun n hn => ?_⟩
    · rw [hD, hmem, min_eq_right]
      rw [h0, hd, Nat.cast_le]
      refine Nat.le_of_mul_le_mul_left ?_ (show 0 < r by omega)
      calc r * (d * t) = d * (t * r) := by ring
        _ ≤ d * (q * ν) := Nat.mul_le_mul_left d hlt.le
        _ = q * (r * w₀) := by rw [hw₀]; ring
        _ = r * (q * w₀) := by ring
    · obtain ⟨i, rfl, hid, w, hpur, -, hle⟩ := hdom n hn
      rcases hid.eq_or_lt with rfl | hlt'
      · rfl
      · exfalso
        obtain ⟨k, rfl⟩ : ∃ k, d = i + k := ⟨d - i, by omega⟩
        rw [Nat.add_sub_cancel_left] at hpur
        have hk : 1 ≤ k := by omega
        have h1 : q * (k * ν) ≤ q * (r * w) := Nat.mul_le_mul_left q hpur
        have h2 : k * (t * r) < k * (q * ν) := (Nat.mul_lt_mul_left (by omega)).mpr hlt
        have h3 : r * (q * w + i * t) ≤ r * ((i + k) * t) := Nat.mul_le_mul_left r hle
        nlinarith
  ·
    rw [hν', ← Nat.cast_mul, Nat.cast_lt] at hgt
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, fun n hn => ?_⟩
    · rw [hD, hmem, min_eq_left]
      rw [h0, hd, Nat.cast_le]
      refine Nat.le_of_mul_le_mul_left ?_ (show 0 < r by omega)
      calc r * (q * w₀) = q * (r * w₀) := by ring
        _ = d * (q * ν) := by rw [hw₀]; ring
        _ ≤ d * (t * r) := Nat.mul_le_mul_left d hgt.le
        _ = r * (d * t) := by ring
    · obtain ⟨i, rfl, hid, w, hpur, hle, -⟩ := hdom n hn
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rfl
      · exfalso
        obtain ⟨k, rfl⟩ : ∃ k, d = i + k := ⟨d - i, by omega⟩
        rw [Nat.add_sub_cancel_left] at hpur
        have h1 : q * (k * ν) ≤ q * (r * w) := Nat.mul_le_mul_left q hpur
        have h2 : i * (q * ν) < i * (t * r) := (Nat.mul_lt_mul_left hpos).mpr hgt
        have h3 : r * (q * w + i * t) ≤ r * (q * w₀) := Nat.mul_le_mul_left r hle
        have h4 : r * (q * w₀) = q * ((i + k) * ν) := by
          calc r * (q * w₀) = q * (r * w₀) := by ring
            _ = q * ((i + k) * ν) := by rw [hw₀]
        nlinarith

theorem sInf_sSup_dominantIndices_polynomial_pure_at (hp : P1Arch.IsPureSlope r N d p) (hN : N ≠ 0) (hr : 1 ≤ r)
    (q : ℕ) (hq : 1 ≤ q) (E t : ℕ) (h : ((t * r : ℕ) : ℕ∞) = (q : ℕ∞) * IsDiscreteValuationRing.addVal W N) :
    sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) E t ((p : PowerSeries W), 0)) = 0 ∧
      sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) E t ((p : PowerSeries W), 0)) = d := by
  change sInf (dominantIndices (vq W q) E t ((p : PowerSeries W), 0)) = 0 ∧
    sSup (dominantIndices (vq W q) E t ((p : PowerSeries W), 0)) = d
  obtain ⟨hmem0, hmemd⟩ := (dominantIndices_polynomial_pure hp hN hr q hq E t).1 h
  have hIcc := mem_Icc_of_mem_dominantIndices_pure hp hN hr q hq E t
  exact ⟨le_antisymm (csInf_le ⟨0, fun n hn => (hIcc n hn).1⟩ hmem0) (le_csInf ⟨_, hmem0⟩ fun n hn => (hIcc n hn).1),
    le_antisymm (csSup_le ⟨_, hmemd⟩ fun n hn => (hIcc n hn).2) (le_csSup ⟨d, fun n hn => (hIcc n hn).2⟩ hmemd)⟩

theorem sInf_sSup_dominantIndices_polynomial_pure_below (hp : P1Arch.IsPureSlope r N d p) (hN : N ≠ 0) (hr : 1 ≤ r)
    (q : ℕ) (hq : 1 ≤ q) (E t : ℕ) (h : ((t * r : ℕ) : ℕ∞) < (q : ℕ∞) * IsDiscreteValuationRing.addVal W N) :
    sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) E t ((p : PowerSeries W), 0)) = d ∧
      sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) E t ((p : PowerSeries W), 0)) = d := by
  change sInf (dominantIndices (vq W q) E t ((p : PowerSeries W), 0)) = d ∧
    sSup (dominantIndices (vq W q) E t ((p : PowerSeries W), 0)) = d
  rw [(dominantIndices_polynomial_pure hp hN hr q hq E t).2.1 h, csInf_singleton, csSup_singleton]
  exact ⟨rfl, rfl⟩

theorem sInf_sSup_dominantIndices_polynomial_pure_above (hp : P1Arch.IsPureSlope r N d p) (hN : N ≠ 0) (hr : 1 ≤ r)
    (q : ℕ) (hq : 1 ≤ q) (E t : ℕ) (h : (q : ℕ∞) * IsDiscreteValuationRing.addVal W N < ((t * r : ℕ) : ℕ∞)) :
    sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) E t ((p : PowerSeries W), 0)) = 0 ∧
      sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) E t ((p : PowerSeries W), 0)) = 0 := by
  change sInf (dominantIndices (vq W q) E t ((p : PowerSeries W), 0)) = 0 ∧
    sSup (dominantIndices (vq W q) E t ((p : PowerSeries W), 0)) = 0
  rw [(dominantIndices_polynomial_pure hp hN hr q hq E t).2.2 h, csInf_singleton, csSup_singleton]
  exact ⟨rfl, rfl⟩

theorem circleIndexDrop_polynomial_pure (hp : P1Arch.IsPureSlope r N d p) (hN : N ≠ 0) (hr : 1 ≤ r)
    (q : ℕ) (hq : 1 ≤ q) (E t : ℕ) :
    circleIndexDrop (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) E t ((p : PowerSeries W), 0) =
      if ((t * r : ℕ) : ℕ∞) = (q : ℕ∞) * IsDiscreteValuationRing.addVal W N then d else 0 := by
  rw [circleIndexDrop]
  split_ifs with h
  · obtain ⟨h1, h2⟩ := sInf_sSup_dominantIndices_polynomial_pure_at hp hN hr q hq E t h
    rw [h1, h2]; simp
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · obtain ⟨h1, h2⟩ := sInf_sSup_dominantIndices_polynomial_pure_below hp hN hr q hq E t hlt
      rw [h1, h2]; simp
    · obtain ⟨h1, h2⟩ := sInf_sSup_dominantIndices_polynomial_pure_above hp hN hr q hq E t hgt
      rw [h1, h2]; simp

end PureSlope
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

section DominantIndicesScale
variable {W : Type u} [CommRing W]

theorem enat_map_iInf_eq_of_monotone {ι : Type*} [Nonempty ι] (g : ℕ∞ → ℕ∞) (hg : Monotone g) (f : ι → ℕ∞) :
    g (⨅ i, f i) = ⨅ i, g (f i) := by
  apply le_antisymm
  · exact le_iInf fun i => hg (iInf_le f i)
  · obtain ⟨i, hi⟩ := ciInf_mem f
    rw [← hi]
    exact iInf_le (fun i => g (f i)) i

theorem enat_natCast_mul_left_cancel (q : ℕ) (hq : 1 ≤ q) {a b : ℕ∞} (h : (q : ℕ∞) * a = (q : ℕ∞) * b) :
    a = b := by
  have hq0 : (q : ℕ∞) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => rfl
    | coe b =>
      exfalso
      rw [ENat.mul_top hq0, ← Nat.cast_mul] at h
      exact ENat.coe_ne_top _ h.symm
  | coe a =>
    induction b using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.mul_top hq0, ← Nat.cast_mul] at h
      exact ENat.coe_ne_top _ h
    | coe b =>
      rw [← Nat.cast_mul, ← Nat.cast_mul] at h
      have h' : q * a = q * b := by exact_mod_cast h
      exact_mod_cast Nat.eq_of_mul_eq_mul_left (by omega) h'

theorem annulusWeight_scale (q E t : ℕ) (d : Fin 2 →₀ ℕ) :
    annulusWeight (q * E) (q * t) d = q * annulusWeight E t d := by
  simp only [annulusWeight, ← mul_tsub]; ring

theorem repGaussOrder_scale (v : W → ℕ∞) (E t q : ℕ) (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder (fun w => (q : ℕ∞) * v w) (q * E) (q * t) F = (q : ℕ∞) * repGaussOrder v E t F := by
  simp only [repGaussOrder, annulusWeight_scale, Nat.cast_mul, ← mul_add]
  exact (enat_map_iInf_eq_of_monotone (fun x => (q : ℕ∞) * x) (fun a b h => mul_le_mul_right h _) _).symm

theorem termOrder_scale (v : W → ℕ∞) (E t q : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab n = (q : ℕ∞) * termOrder v E t ab n := by
  simp only [termOrder, annulusWeight_scale, Nat.cast_mul, mul_add]

theorem dominantIndices_scale (v : W → ℕ∞) (E t q : ℕ) (hq : 1 ≤ q) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => (q : ℕ∞) * v w) (q * E) (q * t) ab = dominantIndices v E t ab := by
  ext n
  simp only [dominantIndices, Set.mem_setOf_eq, termOrder_scale, repGaussOrder_scale]
  exact ⟨enat_natCast_mul_left_cancel q hq, fun h => by rw [h]⟩

end DominantIndicesScale
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

namespace P1Arch

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

local notation "addv" => (IsDiscreteValuationRing.addVal W : W → ℕ∞)

theorem dominantIndices_scaled_zero (q e : ℕ) (hq : 1 ≤ q) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab =
      dominantIndices addv e 0 ab := by
  simpa using dominantIndices_scale addv e 0 q hq ab

theorem dominantIndices_scaled_top (q e : ℕ) (hq : 1 ≤ q) (ab : PowerSeries W × PowerSeries W) :
    dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab =
      dominantIndices addv e e ab :=
  dominantIndices_scale addv e e q hq ab

end P1Arch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

section KinkGeneral
variable {W : Type u} [CommRing W]

theorem mem_dominantIndices_iff_forall_le (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices v E t ab ↔ ∀ m, termOrder v E t ab n ≤ termOrder v E t ab m := by
  rw [mem_dominantIndices_iff v hv0 E t ab hb]
  exact ⟨fun h m => h ▸ iInf_le _ m, fun h => le_antisymm (le_iInf h) (iInf_le _ n)⟩

theorem termOrder_add_add (v : W → ℕ∞) (E t k : ℕ) (htk : t + k ≤ E) (ab : PowerSeries W × PowerSeries W)
    (n : ℤ) :
    termOrder v E (t + k) ab n + ((k * (-n).toNat : ℕ) : ℕ∞) =
      termOrder v E t ab n + ((k * n.toNat : ℕ) : ℕ∞) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := termOrder_succ_add v E (t + k) (by omega) ab n
    have ih' := ih (by omega)
    rw [show t + (k + 1) = t + k + 1 from by omega]
    calc termOrder v E (t + k + 1) ab n + ((((k + 1) * (-n).toNat : ℕ)) : ℕ∞)
        = (termOrder v E (t + k + 1) ab n + (((-n).toNat : ℕ) : ℕ∞)) + ((k * (-n).toNat : ℕ) : ℕ∞) := by
          push_cast; ring
      _ = (termOrder v E (t + k) ab n + ((n.toNat : ℕ) : ℕ∞)) + ((k * (-n).toNat : ℕ) : ℕ∞) := by rw [h1]
      _ = (termOrder v E (t + k) ab n + ((k * (-n).toNat : ℕ) : ℕ∞)) + ((n.toNat : ℕ) : ℕ∞) := by ring
      _ = (termOrder v E t ab n + ((k * n.toNat : ℕ) : ℕ∞)) + ((n.toNat : ℕ) : ℕ∞) := by rw [ih']
      _ = termOrder v E t ab n + ((((k + 1) * n.toNat : ℕ)) : ℕ∞) := by push_cast; ring

theorem termOrder_add_ne_top (v : W → ℕ∞) (E t k : ℕ) (htk : t + k ≤ E) (ab : PowerSeries W × PowerSeries W)
    (n : ℤ) (h : termOrder v E t ab n ≠ ⊤) : termOrder v E (t + k) ab n ≠ ⊤ := by
  intro htop
  have hid := termOrder_add_add v E t k htk ab n
  rw [htop, top_add] at hid
  exact (WithTop.add_ne_top.mpr ⟨h, ENat.coe_ne_top _⟩) hid.symm

theorem termOrder_ne_top_of_add (v : W → ℕ∞) (E t k : ℕ) (htk : t + k ≤ E) (ab : PowerSeries W × PowerSeries W)
    (n : ℤ) (h : termOrder v E (t + k) ab n ≠ ⊤) : termOrder v E t ab n ≠ ⊤ := by
  intro htop
  have hid := termOrder_add_add v E t k htk ab n
  rw [htop, top_add] at hid
  exact (WithTop.add_ne_top.mpr ⟨h, ENat.coe_ne_top _⟩) hid

theorem termOrder_add_eq_of_eq_coe (v : W → ℕ∞) (E t k : ℕ) (htk : t + k ≤ E)
    (ab : PowerSeries W × PowerSeries W) (n : ℤ) (a : ℕ) (ha : termOrder v E t ab n = a) :
    ∃ b : ℕ, termOrder v E (t + k) ab n = b ∧ (b : ℤ) = a + k * n := by
  have hne : termOrder v E (t + k) ab n ≠ ⊤ :=
    termOrder_add_ne_top v E t k htk ab n (by rw [ha]; exact ENat.coe_ne_top _)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨b, hb.symm, ?_⟩
  have hid := termOrder_add_add v E t k htk ab n
  rw [ha, ← hb] at hid
  have hnat : b + k * (-n).toNat = a + k * n.toNat := by exact_mod_cast hid
  have hz : (b : ℤ) + k * ((-n).toNat : ℤ) = a + k * (n.toNat : ℤ) := by exact_mod_cast hnat
  have hnn : (n.toNat : ℤ) - ((-n).toNat : ℤ) = n := Int.toNat_sub_toNat_neg n
  linear_combination hz + (k : ℤ) * hnn

theorem eq_of_mem_dominantIndices_of_mem_of_mem (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E P k l : ℕ)
    (hk : 1 ≤ k) (hl : 1 ≤ l) (hPE : P + k + l ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : (⨅ n, termOrder v E P ab n) < ⊤) (m : ℤ)
    (hmP : m ∈ dominantIndices v E P ab) (hmQ : m ∈ dominantIndices v E (P + k + l) ab)
    (n : ℤ) (hn : n ∈ dominantIndices v E (P + k) ab) : n = m := by
  have hmeq : termOrder v E P ab m = ⨅ n, termOrder v E P ab n := (mem_dominantIndices_iff v hv0 E P ab hb m).mp hmP
  rw [mem_dominantIndices_iff_forall_le v hv0 _ _ ab hb] at hmP hmQ hn

  have hTm : termOrder v E P ab m < ⊤ := by rw [hmeq]; exact hfin
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hTm.ne
  have ha' : termOrder v E P ab m = a := ha.symm

  obtain ⟨c, hc, hcz⟩ := termOrder_add_eq_of_eq_coe v E P k (by omega) ab m a ha'
  obtain ⟨e', he', hez⟩ := termOrder_add_eq_of_eq_coe v E (P + k) l hPE ab m c hc

  have hbne : termOrder v E P ab n ≠ ⊤ := by
    apply termOrder_ne_top_of_add v E P k (by omega) ab n
    have := hn m
    rw [hc] at this
    exact ne_top_of_le_ne_top (ENat.coe_ne_top c) this
  obtain ⟨b, hbb⟩ := ENat.ne_top_iff_exists.mp hbne
  have hb' : termOrder v E P ab n = b := hbb.symm
  obtain ⟨d, hd, hdz⟩ := termOrder_add_eq_of_eq_coe v E P k (by omega) ab n b hb'
  obtain ⟨f, hf, hfz⟩ := termOrder_add_eq_of_eq_coe v E (P + k) l hPE ab n d hd

  have h1 : a ≤ b := by have := hmP n; rw [ha', hb'] at this; exact_mod_cast this
  have h2 : d ≤ c := by have := hn m; rw [hd, hc] at this; exact_mod_cast this
  have h3 : e' ≤ f := by have := hmQ n; rw [he', hf] at this; exact_mod_cast this
  have h1z : (a : ℤ) ≤ b := by exact_mod_cast h1
  have h2z : (d : ℤ) ≤ c := by exact_mod_cast h2
  have h3z : (e' : ℤ) ≤ f := by exact_mod_cast h3
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  have hlpos : (0 : ℤ) < l := by exact_mod_cast hl
  have hA : (k : ℤ) * n - k * m ≤ 0 := by linarith
  have hB : 0 ≤ (l : ℤ) * n - l * m := by linarith
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exfalso
    have := mul_lt_mul_of_pos_left hlt hlpos
    linarith
  · exact heq
  · exfalso
    have := mul_lt_mul_of_pos_left hgt hkpos
    linarith

theorem enat_le_of_mul_le_mul {r : ℕ} (hr : 1 ≤ r) {a b : ℕ∞} (h : (r : ℕ∞) * a ≤ (r : ℕ∞) * b) : a ≤ b := by
  induction b using ENat.recTopCoe with
  | top => exact le_top
  | coe b =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have hrt : (r : ℕ∞) * ⊤ = ⊤ := WithTop.mul_top (Nat.cast_ne_zero.mpr (show r ≠ 0 by omega))
      rw [hrt] at h
      have hfin : ((r : ℕ∞) * (b : ℕ∞)) ≠ ⊤ := by rw [← Nat.cast_mul]; exact ENat.coe_ne_top _
      exact hfin (top_le_iff.mp h)
    | coe a =>
      have : r * a ≤ r * b := by exact_mod_cast h
      exact_mod_cast Nat.le_of_mul_le_mul_left this (by omega)

end KinkGeneral
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section Monotone
variable {W : Type u} [CommRing W]

theorem le_of_mem_dominantIndices_succ (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht : t + 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : ∀ s, (⨅ n, termOrder v E s ab n) < ⊤)
    (m n : ℤ) (hm : m ∈ dominantIndices v E t ab) (hn : n ∈ dominantIndices v E (t + 1) ab) : n ≤ m := by
  have hmeq : termOrder v E t ab m = ⨅ k, termOrder v E t ab k := (mem_dominantIndices_iff v hv0 E t ab hb m).mp hm
  have hneq : termOrder v E (t + 1) ab n = ⨅ k, termOrder v E (t + 1) ab k :=
    (mem_dominantIndices_iff v hv0 E _ ab hb n).mp hn
  have hmle := (mem_dominantIndices_iff_forall_le v hv0 E _ ab hb m).mp hm
  have hnle := (mem_dominantIndices_iff_forall_le v hv0 E _ ab hb n).mp hn
  have hfa : termOrder v E t ab m < ⊤ := by rw [hmeq]; exact hfin _
  obtain ⟨a, ha0⟩ := ENat.ne_top_iff_exists.mp hfa.ne
  have ha : termOrder v E t ab m = a := ha0.symm
  obtain ⟨c, hc, hcz⟩ := termOrder_add_eq_of_eq_coe v E t 1 ht ab m a ha

  have hbne : termOrder v E t ab n ≠ ⊤ := by
    apply termOrder_ne_top_of_add v E t 1 ht ab n
    have := hnle m
    rw [hc] at this
    exact ne_top_of_le_ne_top (ENat.coe_ne_top c) this
  obtain ⟨b, hb0⟩ := ENat.ne_top_iff_exists.mp hbne
  have hb' : termOrder v E t ab n = b := hb0.symm
  obtain ⟨d, hd, hdz⟩ := termOrder_add_eq_of_eq_coe v E t 1 ht ab n b hb'
  have h1 : a ≤ b := by have := hmle n; rw [ha, hb'] at this; exact_mod_cast this
  have h2 : d ≤ c := by have := hnle m; rw [hd, hc] at this; exact_mod_cast this
  have h1z : (a : ℤ) ≤ b := by exact_mod_cast h1
  have h2z : (d : ℤ) ≤ c := by exact_mod_cast h2
  simp only [Nat.cast_one, one_mul] at hcz hdz
  linarith

theorem sSup_dominantIndices_le_sInf (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) (hE : 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : ∀ s, (⨅ n, termOrder v E s ab n) < ⊤) :
    sSup (dominantIndices v E E ab) ≤ sInf (dominantIndices v E 0 ab) := by
  have hbdd0 : BddBelow (dominantIndices v E 0 ab) := dominantIndices_bddBelow v hv0 E 0 (by omega) ab hb (hfin 0)
  have h0 : sInf (dominantIndices v E 0 ab) ∈ dominantIndices v E 0 ab :=
    Int.csInf_mem (dominantIndices_nonempty v hv0 E 0 ab hb) hbdd0

  have key : ∀ t, 1 ≤ t → t ≤ E → ∀ n ∈ dominantIndices v E t ab, n ≤ sInf (dominantIndices v E 0 ab) := by
    intro t
    induction t with
    | zero => intro h; omega
    | succ t ih =>
      intro _ htE n hn
      rcases Nat.eq_zero_or_pos t with ht0 | ht0
      · subst ht0
        exact le_of_mem_dominantIndices_succ v hv0 E 0 htE ab hb hfin _ n h0 hn
      · obtain ⟨m, hm⟩ := dominantIndices_nonempty v hv0 E t ab hb
        exact (le_of_mem_dominantIndices_succ v hv0 E t htE ab hb hfin m n hm hn).trans (ih ht0 (by omega) m hm)
  exact csSup_le (dominantIndices_nonempty v hv0 E E ab hb) (key E hE le_rfl)

end Monotone
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel IsLocalRing Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

section MonicBounds

open Polynomial

variable {W : Type u} [CommRing W]

theorem inU_zero : inU (0 : PowerSeries W) = 0 := by
  ext d; rw [coeff_inU]; simp

theorem mem_Icc_of_mem_dominantIndices_monic (v : W → ℕ∞) (hv0 : v 0 = ⊤) (hv1 : v 1 = 0) (E t : ℕ)
    (p : W[X]) (hp : p.Monic) (n : ℤ) (hn : n ∈ dominantIndices v E t ((p : PowerSeries W), 0)) :
    0 ≤ n ∧ n ≤ p.natDegree := by
  rw [mem_dominantIndices_iff v hv0 E t _ (map_zero _)] at hn
  have htop : termOrder v E t ((p : PowerSeries W), 0) (p.natDegree : ℤ) < ⊤ := by
    rw [termOrder_polynomial_natCast, hp.coeff_natDegree, hv1, zero_add]
    exact WithTop.coe_lt_top _
  have hfin : termOrder v E t ((p : PowerSeries W), 0) n < ⊤ := by
    rw [hn]; exact lt_of_le_of_lt (iInf_le _ _) htop
  cases n with
  | negSucc j => rw [termOrder_polynomial_negSucc v hv0] at hfin; exact absurd hfin (lt_irrefl _)
  | ofNat i =>
    rw [Int.ofNat_eq_natCast] at hfin ⊢
    refine ⟨by omega, ?_⟩
    by_contra h
    rw [termOrder_polynomial_of_natDegree_lt v hv0 E t p i (by omega)] at hfin
    exact lt_irrefl _ hfin

theorem sInf_le_natDegree_and_sSup_nonneg_of_monic (v : W → ℕ∞) (hv0 : v 0 = ⊤) (hv1 : v 1 = 0) (E t : ℕ)
    (p : W[X]) (hp : p.Monic) :
    sInf (dominantIndices v E t ((p : PowerSeries W), 0)) ≤ p.natDegree ∧
      0 ≤ sSup (dominantIndices v E t ((p : PowerSeries W), 0)) := by
  obtain ⟨m, hm⟩ := dominantIndices_nonempty v hv0 E t ((p : PowerSeries W), 0) (map_zero _)
  have hI := mem_Icc_of_mem_dominantIndices_monic v hv0 hv1 E t p hp
  exact ⟨(csInf_le ⟨0, fun n hn => (hI n hn).1⟩ hm).trans (hI m hm).2,
    (hI m hm).1.trans (le_csSup ⟨(p.natDegree : ℤ), fun n hn => (hI n hn).2⟩ hm)⟩

end MonicBounds
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section SingleSlope

variable {W : Type u} [CommRing W]

theorem sInf_sSup_dominantIndices_eq_of_sInf_le_sSup (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E : ℕ) (hE : 1 ≤ E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : ∀ s, (⨅ n, termOrder v E s ab n) < ⊤)
    (hle : sInf (dominantIndices v E 0 ab) ≤ sSup (dominantIndices v E E ab)) :
    (∀ t, t + 1 ≤ E → sInf (dominantIndices v E t ab) = sSup (dominantIndices v E E ab)) ∧
      (∀ t, 1 ≤ t → t ≤ E → sSup (dominantIndices v E t ab) = sSup (dominantIndices v E E ab)) := by
  set n₀ := sSup (dominantIndices v E E ab) with hn₀
  set I₀ := sInf (dominantIndices v E 0 ab) with hI₀
  have hge : n₀ ≤ I₀ := sSup_dominantIndices_le_sInf v hv0 E hE ab hb hfin
  have heq : I₀ = n₀ := le_antisymm hle hge
  have hne := fun t => dominantIndices_nonempty v hv0 E t ab hb
  have hbdd0 : BddBelow (dominantIndices v E 0 ab) := dominantIndices_bddBelow v hv0 E 0 (by omega) ab hb (hfin 0)
  have hbddE : BddAbove (dominantIndices v E E ab) := dominantIndices_bddAbove v hv0 E E (by omega) ab hb (hfin E)
  have h0mem : I₀ ∈ dominantIndices v E 0 ab := Int.csInf_mem (hne 0) hbdd0

  have up : ∀ t, 1 ≤ t → t ≤ E → ∀ n ∈ dominantIndices v E t ab, n ≤ I₀ := by
    intro t
    induction t with
    | zero => intro h; omega
    | succ t ih =>
      intro _ htE n hn
      rcases Nat.eq_zero_or_pos t with ht0 | ht0
      · subst ht0
        exact le_of_mem_dominantIndices_succ v hv0 E 0 htE ab hb hfin _ n h0mem hn
      · obtain ⟨m, hm⟩ := hne t
        exact (le_of_mem_dominantIndices_succ v hv0 E t htE ab hb hfin m n hm hn).trans (ih ht0 (by omega) m hm)

  have down : ∀ k t, t + k = E → 1 ≤ k → ∀ n ∈ dominantIndices v E t ab, n₀ ≤ n := by
    intro k
    induction k with
    | zero => intro t _ h; omega
    | succ k ih =>
      intro t htk _ n hn
      have hstep : ∀ m ∈ dominantIndices v E (t + 1) ab, m ≤ n := fun m hm =>
        le_of_mem_dominantIndices_succ v hv0 E t (by omega) ab hb hfin n m hn hm
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        have htE : t + 1 = E := by omega
        rw [htE] at hstep
        rw [hn₀]
        exact csSup_le (hne E) hstep
      · obtain ⟨m, hm⟩ := hne (t + 1)
        exact (ih (t + 1) (by omega) hk0 m hm).trans (hstep m hm)
  constructor
  · intro t ht
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · exact heq
    · have hlo : ∀ n ∈ dominantIndices v E t ab, n₀ ≤ n := down (E - t) t (by omega) (by omega)
      have hhi : ∀ n ∈ dominantIndices v E t ab, n ≤ n₀ := fun n hn => heq ▸ up t ht0 (by omega) n hn
      obtain ⟨m, hm⟩ := hne t
      exact le_antisymm ((csInf_le ⟨n₀, hlo⟩ hm).trans (hhi m hm)) (le_csInf (hne t) hlo)
  · intro t ht1 htE
    rcases htE.eq_or_lt with rfl | hlt
    · rfl
    · have hlo : ∀ n ∈ dominantIndices v E t ab, n₀ ≤ n := down (E - t) t (by omega) (by omega)
      have hhi : ∀ n ∈ dominantIndices v E t ab, n ≤ n₀ := fun n hn => heq ▸ up t ht1 htE n hn
      obtain ⟨m, hm⟩ := hne t
      exact le_antisymm (csSup_le (hne t) hhi) ((hlo m hm).trans (le_csSup ⟨n₀, hhi⟩ hm))

end SingleSlope
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section CayleyHamilton

open Polynomial AnnulusNF

theorem aeval_charpoly_mulLeft_mk_mem {A : Type*} [CommRing A] {S : Type*} [CommRing S] [Algebra A S]
    (I : Ideal S) (u : S) [Module.Free A (S ⧸ I)] [Module.Finite A (S ⧸ I)] :
    aeval u (LinearMap.mulLeft A (Ideal.Quotient.mk I u)).charpoly ∈ I := by
  set T := LinearMap.mulLeft A (Ideal.Quotient.mk I u) with hT
  set χ := T.charpoly with hχ
  have h := LinearMap.aeval_self_charpoly T
  rw [← hχ] at h
  have h1 : T = Algebra.lmul A (S ⧸ I) (Ideal.Quotient.mk I u) := LinearMap.ext fun _ => rfl
  rw [h1, aeval_algHom_apply] at h
  have h2 : aeval (Ideal.Quotient.mk I u) χ = 0 := by
    simpa [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using LinearMap.congr_fun h 1
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h3 : (Ideal.Quotient.mk I) (aeval u χ) = aeval (Ideal.Quotient.mk I u) χ := by
    change Ideal.Quotient.mkₐ A I (aeval u χ) = aeval (Ideal.Quotient.mkₐ A I u) χ
    rw [aeval_algHom_apply]
  rw [h3, h2]

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem aeval_U_ne_zero_of_monic [IsAdicComplete (maximalIdeal W) W] (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (p : W[X]) (hp : p.Monic) : aeval (U (ϖ ^ e)) p ≠ 0 := by
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  intro h0
  rw [← mk_normalForm_polynomial] at h0
  have h00 : mk (ϖ ^ e) (inU (0 : PowerSeries W) + inV 0) = 0 := by
    rw [inU_zero, inV_zero, add_zero, map_zero]
  have h1 := (normalForm_unique ϖ e he (p : PowerSeries W) 0 0 0 (map_zero _) (map_zero _) (h0.trans h00.symm)).1
  have h2 := congrArg (PowerSeries.coeff p.natDegree) h1
  rw [Polynomial.coeff_coe, hp.coeff_natDegree, map_zero] at h2
  exact one_ne_zero h2

end CayleyHamilton
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

section ShiftAlgebra

variable {W : Type u} [CommRing W]

private theorem finTwo_eq_zero_iff (d : Fin 2 →₀ ℕ) : d = 0 ↔ d 0 = 0 ∧ d 1 = 0 := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h0, h1⟩; ext i; fin_cases i <;> simp [h0, h1]

theorem inU_add (a a' : PowerSeries W) : inU (a + a') = inU a + inU a' := by
  ext d
  simp only [coeff_inU, map_add]
  split_ifs <;> simp

theorem inV_add (b b' : PowerSeries W) : inV (b + b') = inV b + inV b' := by
  ext d
  simp only [coeff_inV, map_add]
  split_ifs <;> simp

theorem inU_C_mul (w : W) (a : PowerSeries W) : inU (PowerSeries.C w * a) = MvPowerSeries.C w * inU a := by
  ext d
  rw [MvPowerSeries.coeff_C_mul, coeff_inU, coeff_inU]
  split_ifs
  · rw [PowerSeries.coeff_C_mul]
  · rw [mul_zero]

theorem inV_C_mul (w : W) (b : PowerSeries W) : inV (PowerSeries.C w * b) = MvPowerSeries.C w * inV b := by
  ext d
  rw [MvPowerSeries.coeff_C_mul, coeff_inV, coeff_inV]
  split_ifs
  · rw [PowerSeries.coeff_C_mul]
  · rw [mul_zero]

theorem inU_C (w : W) : inU (PowerSeries.C w) = (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) := by
  classical
  ext d
  rw [coeff_inU, MvPowerSeries.coeff_C, PowerSeries.coeff_C]
  by_cases h1 : d 1 = 0 <;> by_cases h0 : d 0 = 0 <;> simp [h0, h1, finTwo_eq_zero_iff]

theorem inV_C (w : W) : inV (PowerSeries.C w) = (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) := by
  classical
  ext d
  rw [coeff_inV, MvPowerSeries.coeff_C, PowerSeries.coeff_C]
  by_cases h1 : d 1 = 0 <;> by_cases h0 : d 0 = 0 <;> simp [h0, h1, finTwo_eq_zero_iff]

theorem X_zero_mul_inU (a : PowerSeries W) :
    (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * inU a = inU (PowerSeries.X * a) := by
  classical
  ext d
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, coeff_inU, coeff_inU]
  have h1 : (d - Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 1 = d 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (by decide), tsub_zero]
  have h0 : (d - Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) 0 = d 0 - 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl]
  by_cases hle : Finsupp.single (0 : Fin 2) 1 ≤ d
  · rw [if_pos hle, one_mul, h1, h0]
    have hd0 : 1 ≤ d 0 := Finsupp.single_le_iff.1 hle
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d 0 ≠ 0)
    rw [hn, Nat.succ_sub_one, PowerSeries.coeff_succ_X_mul]
  · rw [if_neg hle]
    have hd0 : d 0 = 0 := by rw [Finsupp.single_le_iff] at hle; omega
    rw [hd0, PowerSeries.coeff_zero_X_mul]
    split_ifs <;> rfl

theorem X_one_mul_inV (b : PowerSeries W) :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) * inV b = inV (PowerSeries.X * b) := by
  classical
  ext d
  rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, coeff_inV, coeff_inV]
  have h0 : (d - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 0 = d 0 := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (by decide), tsub_zero]
  have h1 : (d - Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) 1 = d 1 - 1 := by
    rw [Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl]
  by_cases hle : Finsupp.single (1 : Fin 2) 1 ≤ d
  · rw [if_pos hle, one_mul, h1, h0]
    have hd1 : 1 ≤ d 1 := Finsupp.single_le_iff.1 hle
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d 1 ≠ 0)
    rw [hn, Nat.succ_sub_one, PowerSeries.coeff_succ_X_mul]
  · rw [if_neg hle]
    have hd1 : d 1 = 0 := by rw [Finsupp.single_le_iff] at hle; omega
    rw [hd1, PowerSeries.coeff_zero_X_mul]
    split_ifs <;> rfl

private theorem mk_X_zero_mul_X_one (π : W) (y : MvPowerSeries (Fin 2) W) :
    mk π (MvPowerSeries.X 0 * MvPowerSeries.X 1 * y) = mk π (MvPowerSeries.C π * y) := by
  rw [mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← sub_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

theorem U_mul_mk_inU_add_inV (π : W) (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    U π * mk π (inU a + inV b) =
      mk π (inU (PowerSeries.X * a + PowerSeries.C (π * PowerSeries.coeff 1 b)) +
        inV (PowerSeries.C π * PowerSeries.X * PowerSeries.mk fun i => PowerSeries.coeff (i + 2) b)) := by
  have hb' : b = PowerSeries.X * PowerSeries.mk fun i => PowerSeries.coeff (i + 1) b := by
    have h := PowerSeries.eq_X_mul_shift_add_const b
    rw [hb, map_zero, add_zero] at h
    exact h
  have hbs : (PowerSeries.mk fun i => PowerSeries.coeff (i + 1) b) =
      PowerSeries.C (PowerSeries.coeff 1 b) + PowerSeries.X * PowerSeries.mk fun i => PowerSeries.coeff (i + 2) b := by
    ext n
    rcases n with _ | n
    · simp
    · simp [PowerSeries.coeff_succ_X_mul, add_assoc]
  show mk π (MvPowerSeries.X 0) * mk π (inU a + inV b) = _
  rw [← map_mul, mul_add, X_zero_mul_inU]
  conv_lhs => rw [hb', ← X_one_mul_inV, ← mul_assoc, map_add, mk_X_zero_mul_X_one, ← map_add]
  congr 1
  rw [← inV_C_mul, hbs, mul_add, inV_add, ← map_mul, inV_C, ← inU_C, ← mul_assoc, inU_add, add_assoc]

theorem V_mul_mk_inU_add_inV (π : W) (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    V π * mk π (inU a + inV b) =
      mk π (inU (PowerSeries.C π * PowerSeries.mk fun i => PowerSeries.coeff (i + 1) a) +
        inV (PowerSeries.X * (PowerSeries.C (PowerSeries.constantCoeff a) + b))) := by
  have ha' : a = PowerSeries.X * (PowerSeries.mk fun i => PowerSeries.coeff (i + 1) a) +
      PowerSeries.C (PowerSeries.constantCoeff a) := PowerSeries.eq_X_mul_shift_add_const a
  have hX1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) = inV PowerSeries.X := by
    have h := X_one_mul_inV (W := W) (PowerSeries.C 1)
    rwa [inV_C, map_one, map_one, mul_one, mul_one] at h
  show mk π (MvPowerSeries.X 1) * mk π (inU a + inV b) = _
  rw [← map_mul, mul_add, X_one_mul_inV]
  conv_lhs => rw [ha', inU_add, ← X_zero_mul_inU, mul_add, ← mul_assoc, mul_comm (MvPowerSeries.X 1) (MvPowerSeries.X 0),
    inU_C, mul_comm (MvPowerSeries.X 1) (MvPowerSeries.C _), map_add, map_add, mk_X_zero_mul_X_one, hX1, ← inV_C_mul,
    ← map_add, ← map_add, ← inU_C_mul]
  congr 1
  rw [mul_add, inV_add, mul_comm PowerSeries.X (PowerSeries.C _), add_assoc]

theorem const_mul_mk_inU_add_inV (π w : W) (a b : PowerSeries W) :
    const π w * mk π (inU a + inV b) = mk π (inU (PowerSeries.C w * a) + inV (PowerSeries.C w * b)) := by
  show mk π (MvPowerSeries.C w) * mk π (inU a + inV b) = _
  rw [← map_mul, mul_add, inU_C_mul, inV_C_mul]

end ShiftAlgebra
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

open IsLocalRing

section LeadingResidue

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ϖ : W) (hϖ : Irreducible ϖ)
include hϖ

theorem multiplicity_eq_and_unitPart_eq_of_eq_pow_mul {c u : W} {n : ℕ} (hu : IsUnit u) (h : c = ϖ ^ n * u) :
    multiplicity ϖ c = n ∧ unitPart ϖ c = u := by
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hmul : multiplicity ϖ c = n := by
    apply multiplicity_eq_of_dvd_of_not_dvd
    · exact ⟨u, h⟩
    · rintro ⟨t, ht⟩
      apply hϖ.not_isUnit
      apply isUnit_of_dvd_unit _ hu
      refine ⟨t, mul_left_cancel₀ (pow_ne_zero n hϖ0) ?_⟩
      rw [← h, ht, pow_succ, mul_assoc]
  refine ⟨hmul, ?_⟩
  have h2 := pow_multiplicity_mul_unitPart ϖ c
  rw [hmul] at h2
  exact mul_left_cancel₀ (pow_ne_zero n hϖ0) (h2.trans h)

theorem exists_eq_pow_mul_of_ne_zero {c : W} (hc : c ≠ 0) : ∃ (n : ℕ) (u : W), IsUnit u ∧ c = ϖ ^ n * u := by
  obtain ⟨n, u, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  exact ⟨n, u, u.isUnit, h.trans (mul_comm _ _)⟩

theorem isUnit_unitPart {c : W} (hc : c ≠ 0) : IsUnit (unitPart ϖ c) := by
  obtain ⟨n, u, hu, h⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  rw [(multiplicity_eq_and_unitPart_eq_of_eq_pow_mul ϖ hϖ hu h).2]
  exact hu

omit hϖ in
theorem leadingResidue_of_ne_zero {c : W} (hc : c ≠ 0) : leadingResidue ϖ c = residue W (unitPart ϖ c) := by
  rw [leadingResidue, if_neg hc]

theorem leadingResidue_eq_zero_iff (c : W) : leadingResidue ϖ c = 0 ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    rw [leadingResidue_of_ne_zero ϖ hc, residue_eq_zero_iff] at h
    exact h (isUnit_unitPart ϖ hϖ hc)
  · rintro rfl
    rw [leadingResidue, if_pos rfl]

theorem leadingResidue_pow_mul_of_isUnit {u : W} (hu : IsUnit u) (n : ℕ) :
    leadingResidue ϖ (ϖ ^ n * u) = residue W u := by
  have hne : ϖ ^ n * u ≠ 0 := mul_ne_zero (pow_ne_zero n hϖ.ne_zero) hu.ne_zero
  rw [leadingResidue_of_ne_zero ϖ hne, (multiplicity_eq_and_unitPart_eq_of_eq_pow_mul ϖ hϖ hu rfl).2]

theorem leadingResidue_of_isUnit {u : W} (hu : IsUnit u) : leadingResidue ϖ u = residue W u := by
  simpa using leadingResidue_pow_mul_of_isUnit ϖ hϖ hu 0

theorem leadingResidue_mul (c d : W) : leadingResidue ϖ (c * d) = leadingResidue ϖ c * leadingResidue ϖ d := by
  by_cases hc : c = 0
  · rw [hc, zero_mul, (leadingResidue_eq_zero_iff ϖ hϖ 0).2 rfl, zero_mul]
  by_cases hd : d = 0
  · rw [hd, mul_zero, (leadingResidue_eq_zero_iff ϖ hϖ 0).2 rfl, mul_zero]
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  obtain ⟨n, v, hv, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hd
  rw [show ϖ ^ m * u * (ϖ ^ n * v) = ϖ ^ (m + n) * (u * v) by ring, leadingResidue_pow_mul_of_isUnit ϖ hϖ (hu.mul hv),
    leadingResidue_pow_mul_of_isUnit ϖ hϖ hu, leadingResidue_pow_mul_of_isUnit ϖ hϖ hv, map_mul]

theorem leadingResidue_uniformizer_pow_mul (n : ℕ) (c : W) : leadingResidue ϖ (ϖ ^ n * c) = leadingResidue ϖ c := by
  by_cases hc : c = 0
  · rw [hc, mul_zero]
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  rw [show ϖ ^ n * (ϖ ^ m * u) = ϖ ^ (n + m) * u by ring, leadingResidue_pow_mul_of_isUnit ϖ hϖ hu,
    leadingResidue_pow_mul_of_isUnit ϖ hϖ hu]

theorem leadingResidue_neg (c : W) : leadingResidue ϖ (-c) = -leadingResidue ϖ c := by
  by_cases hc : c = 0
  · rw [hc, neg_zero, (leadingResidue_eq_zero_iff ϖ hϖ 0).2 rfl, neg_zero]
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  rw [← mul_neg, leadingResidue_pow_mul_of_isUnit ϖ hϖ hu.neg, leadingResidue_pow_mul_of_isUnit ϖ hϖ hu, map_neg]

theorem leadingResidue_add_of_addVal_lt {c d : W}
    (h : IsDiscreteValuationRing.addVal W c < IsDiscreteValuationRing.addVal W d) :
    leadingResidue ϖ (c + d) = leadingResidue ϖ c := by
  have hc : c ≠ 0 := by
    rintro rfl
    rw [IsDiscreteValuationRing.addVal_zero] at h
    exact not_top_lt h
  by_cases hd : d = 0
  · rw [hd, add_zero]
  obtain ⟨m, u, hu, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hc
  obtain ⟨n, v, hv, rfl⟩ := exists_eq_pow_mul_of_ne_zero ϖ hϖ hd
  have hm : IsDiscreteValuationRing.addVal W (ϖ ^ m * u) = m :=
    IsDiscreteValuationRing.addVal_def _ hu.unit hϖ m (by rw [IsUnit.unit_spec, mul_comm])
  have hn : IsDiscreteValuationRing.addVal W (ϖ ^ n * v) = n :=
    IsDiscreteValuationRing.addVal_def _ hv.unit hϖ n (by rw [IsUnit.unit_spec, mul_comm])
  rw [hm, hn] at h
  have hmn : m < n := by exact_mod_cast h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn

  have hsum : ϖ ^ m * u + ϖ ^ (m + k + 1) * v = ϖ ^ m * (u + ϖ ^ (k + 1) * v) := by ring
  have hmem : ϖ ^ (k + 1) * v ∈ maximalIdeal W := by
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).2 hϖ.not_isUnit))
  have hres : residue W (u + ϖ ^ (k + 1) * v) = residue W u := by
    rw [map_add, (residue_eq_zero_iff _).2 hmem, add_zero]
  have hu' : IsUnit (u + ϖ ^ (k + 1) * v) := by
    rw [← residue_ne_zero_iff_isUnit, hres]
    exact (residue_ne_zero_iff_isUnit u).2 hu
  rw [show m + k + 1 = m + (k + 1) by ring] at hsum ⊢
  rw [show ϖ ^ m * u + ϖ ^ (m + (k + 1)) * v = ϖ ^ m * (u + ϖ ^ (k + 1) * v) by ring,
    leadingResidue_pow_mul_of_isUnit ϖ hϖ hu', leadingResidue_pow_mul_of_isUnit ϖ hϖ hu, hres]

end LeadingResidue
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

open IsLocalRing

section ShiftDefs

variable {W : Type u} [CommRing W]

noncomputable def nfU (π : W) (ab : PowerSeries W × PowerSeries W) : PowerSeries W × PowerSeries W :=
  (PowerSeries.X * ab.1 + PowerSeries.C (π * PowerSeries.coeff 1 ab.2),
    PowerSeries.C π * PowerSeries.X * PowerSeries.mk fun i => PowerSeries.coeff (i + 2) ab.2)

noncomputable def nfV (π : W) (ab : PowerSeries W × PowerSeries W) : PowerSeries W × PowerSeries W :=
  (PowerSeries.C π * PowerSeries.mk fun i => PowerSeries.coeff (i + 1) ab.1,
    PowerSeries.X * (PowerSeries.C (PowerSeries.constantCoeff ab.1) + ab.2))

noncomputable def nfC (w : W) (ab : PowerSeries W × PowerSeries W) : PowerSeries W × PowerSeries W :=
  (PowerSeries.C w * ab.1, PowerSeries.C w * ab.2)

theorem constantCoeff_nfU_snd (π : W) (ab : PowerSeries W × PowerSeries W) :
    PowerSeries.constantCoeff (nfU π ab).2 = 0 := by
  simp [nfU]

theorem constantCoeff_nfV_snd (π : W) (ab : PowerSeries W × PowerSeries W) :
    PowerSeries.constantCoeff (nfV π ab).2 = 0 := by
  simp [nfV]

theorem constantCoeff_nfC_snd (w : W) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) : PowerSeries.constantCoeff (nfC w ab).2 = 0 := by
  simp [nfC, hb]

theorem mk_nfU (π : W) (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) :
    mk π (inU (nfU π ab).1 + inV (nfU π ab).2) = U π * mk π (inU ab.1 + inV ab.2) :=
  (U_mul_mk_inU_add_inV π ab.1 ab.2 hb).symm

theorem mk_nfV (π : W) (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) :
    mk π (inU (nfV π ab).1 + inV (nfV π ab).2) = V π * mk π (inU ab.1 + inV ab.2) :=
  (V_mul_mk_inU_add_inV π ab.1 ab.2 hb).symm

theorem mk_nfC (π w : W) (ab : PowerSeries W × PowerSeries W) :
    mk π (inU (nfC w ab).1 + inV (nfC w ab).2) = const π w * mk π (inU ab.1 + inV ab.2) :=
  (const_mul_mk_inU_add_inV π w ab.1 ab.2).symm

private theorem nfCoeff_natCast' (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    nfCoeff ab (i : ℤ) = PowerSeries.coeff i ab.1 := rfl

private theorem nfCoeff_negSucc' (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    nfCoeff ab (Int.negSucc j) = PowerSeries.coeff (j + 1) ab.2 := rfl

private theorem negSucc_sub_one' (j : ℕ) : Int.negSucc j - 1 = Int.negSucc (j + 1) := by
  simp only [Int.negSucc_eq]; push_cast; ring

private theorem negSucc_succ_add_one' (j : ℕ) : Int.negSucc (j + 1) + 1 = Int.negSucc j := by
  simp only [Int.negSucc_eq]; push_cast; ring

theorem nfCoeff_nfU (π : W) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    nfCoeff (nfU π ab) n = (if 1 ≤ n then 1 else π) * nfCoeff ab (n - 1) := by
  rcases n with (_ | i) | j
  ·
    rw [show (Int.ofNat 0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, nfCoeff_natCast', if_neg (by decide),
      show ((0 : ℕ) : ℤ) - 1 = Int.negSucc 0 from rfl, nfCoeff_negSucc']
    simp [nfU]
  ·
    rw [show (Int.ofNat (i + 1) : ℤ) = ((i + 1 : ℕ) : ℤ) from rfl, nfCoeff_natCast', if_pos (by push_cast; omega),
      show ((i + 1 : ℕ) : ℤ) - 1 = ((i : ℕ) : ℤ) by push_cast; ring, nfCoeff_natCast', one_mul]
    simp [nfU, PowerSeries.coeff_succ_X_mul]
  ·
    rw [nfCoeff_negSucc', if_neg (by simp [Int.negSucc_eq]; omega), negSucc_sub_one', nfCoeff_negSucc']
    simp only [nfU]
    rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]

theorem nfCoeff_nfV (π : W) (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    nfCoeff (nfV π ab) n = (if 0 ≤ n then π else 1) * nfCoeff ab (n + 1) := by
  rcases n with i | (_ | j)
  ·
    rw [show (Int.ofNat i : ℤ) = ((i : ℕ) : ℤ) from rfl, nfCoeff_natCast', if_pos (by positivity),
      show ((i : ℕ) : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by push_cast; ring, nfCoeff_natCast']
    simp only [nfV]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  ·
    rw [nfCoeff_negSucc', if_neg (by decide), show Int.negSucc 0 + 1 = ((0 : ℕ) : ℤ) from rfl, nfCoeff_natCast', one_mul]
    simp only [nfV]
    rw [zero_add, PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_zero_C, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      hb, add_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  ·
    rw [nfCoeff_negSucc', if_neg (by simp [Int.negSucc_eq]; omega), negSucc_succ_add_one', nfCoeff_negSucc', one_mul]
    simp only [nfV]
    rw [PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_C, if_neg (by omega), zero_add]

theorem nfCoeff_nfC (w : W) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    nfCoeff (nfC w ab) n = w * nfCoeff ab n := by
  rcases n with i | j
  · rw [show (Int.ofNat i : ℤ) = ((i : ℕ) : ℤ) from rfl, nfCoeff_natCast', nfCoeff_natCast']
    simp only [nfC]; rw [PowerSeries.coeff_C_mul]
  · rw [nfCoeff_negSucc', nfCoeff_negSucc']
    simp only [nfC]; rw [PowerSeries.coeff_C_mul]

end ShiftDefs
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section ShiftHelpers

private theorem annulusWeight_nfExponent_natCast' (e t : ℕ) (i : ℕ) :
    annulusWeight e t (nfExponent (i : ℤ)) = i * t := by
  show annulusWeight e t (Finsupp.single 0 i) = i * t
  simp [annulusWeight]

private theorem annulusWeight_nfExponent_negSucc' (e t : ℕ) (j : ℕ) :
    annulusWeight e t (nfExponent (Int.negSucc j)) = (j + 1) * (e - t) := by
  show annulusWeight e t (Finsupp.single 1 (j + 1)) = (j + 1) * (e - t)
  simp [annulusWeight]

private theorem iInf_comp_sub_one' (f : ℤ → ℕ∞) : ⨅ n : ℤ, f (n - 1) = ⨅ n : ℤ, f n :=
  Function.Surjective.iInf_comp (fun m => ⟨m + 1, by ring⟩) f

private theorem iInf_comp_add_one' (f : ℤ → ℕ∞) : ⨅ n : ℤ, f (n + 1) = ⨅ n : ℤ, f n :=
  Function.Surjective.iInf_comp (fun m => ⟨m - 1, by ring⟩) f

end ShiftHelpers
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section ShiftOrders

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ)
include hϖ

private theorem addVal_uniformizer_pow' (n : ℕ) : IsDiscreteValuationRing.addVal W (ϖ ^ n) = n := by
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]; simp

theorem termOrder_nfU (t : ℕ) (ht : t ≤ e) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder (IsDiscreteValuationRing.addVal W) e t (nfU (ϖ ^ e) ab) n =
      termOrder (IsDiscreteValuationRing.addVal W) e t ab (n - 1) + t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  simp only [termOrder]
  rw [nfCoeff_nfU, IsDiscreteValuationRing.addVal_mul]
  rcases n with (_ | i) | j
  · rw [if_neg (by decide), addVal_uniformizer_pow' ϖ hϖ, show (Int.ofNat 0 : ℤ) = ((0 : ℕ) : ℤ) from rfl,
      show ((0 : ℕ) : ℤ) - 1 = Int.negSucc 0 from rfl, annulusWeight_nfExponent_natCast',
      annulusWeight_nfExponent_negSucc', Nat.add_sub_cancel_left]
    push_cast
    ring
  · rw [if_pos (by show (1 : ℤ) ≤ ((i + 1 : ℕ) : ℤ); omega), IsDiscreteValuationRing.addVal_one, zero_add,
      show (Int.ofNat (i + 1) : ℤ) = ((i + 1 : ℕ) : ℤ) from rfl,
      show ((i + 1 : ℕ) : ℤ) - 1 = ((i : ℕ) : ℤ) by push_cast; ring, annulusWeight_nfExponent_natCast',
      annulusWeight_nfExponent_natCast']
    push_cast
    ring
  · rw [if_neg (by simp [Int.negSucc_eq]; omega), addVal_uniformizer_pow' ϖ hϖ, negSucc_sub_one',
      annulusWeight_nfExponent_negSucc', annulusWeight_nfExponent_negSucc', Nat.add_sub_cancel_left]
    push_cast
    ring

theorem termOrder_nfV (t : ℕ) (ht : t ≤ e) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    termOrder (IsDiscreteValuationRing.addVal W) e t (nfV (ϖ ^ e) ab) n =
      termOrder (IsDiscreteValuationRing.addVal W) e t ab (n + 1) + (e - t : ℕ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  simp only [termOrder]
  rw [nfCoeff_nfV _ _ hb, IsDiscreteValuationRing.addVal_mul, Nat.add_sub_cancel_left]
  rcases n with i | (_ | j)
  · rw [if_pos (by exact Int.natCast_nonneg i), addVal_uniformizer_pow' ϖ hϖ, show (Int.ofNat i : ℤ) = ((i : ℕ) : ℤ) from rfl,
      show ((i : ℕ) : ℤ) + 1 = ((i + 1 : ℕ) : ℤ) by push_cast; ring, annulusWeight_nfExponent_natCast',
      annulusWeight_nfExponent_natCast']
    push_cast
    ring
  · rw [if_neg (by decide), IsDiscreteValuationRing.addVal_one, zero_add,
      show Int.negSucc 0 + 1 = ((0 : ℕ) : ℤ) from rfl, annulusWeight_nfExponent_negSucc',
      annulusWeight_nfExponent_natCast', Nat.add_sub_cancel_left]
    push_cast
    ring
  · rw [if_neg (by simp [Int.negSucc_eq]; omega), IsDiscreteValuationRing.addVal_one, zero_add, negSucc_succ_add_one',
      annulusWeight_nfExponent_negSucc', annulusWeight_nfExponent_negSucc', Nat.add_sub_cancel_left]
    push_cast
    ring

omit hϖ in
theorem termOrder_nfC (t : ℕ) (w : W) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder (IsDiscreteValuationRing.addVal W) e t (nfC w ab) n =
      termOrder (IsDiscreteValuationRing.addVal W) e t ab n + IsDiscreteValuationRing.addVal W w := by
  simp only [termOrder]
  rw [nfCoeff_nfC, IsDiscreteValuationRing.addVal_mul]
  ring

theorem mem_dominantIndices_nfU_iff (t : ℕ) (ht : t ≤ e) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices (IsDiscreteValuationRing.addVal W) e t (nfU (ϖ ^ e) ab) ↔
      n - 1 ∈ dominantIndices (IsDiscreteValuationRing.addVal W) e t ab := by
  simp only [dominantIndices, Set.mem_setOf_eq]
  rw [show (nfU (ϖ ^ e) ab) = ((nfU (ϖ ^ e) ab).1, (nfU (ϖ ^ e) ab).2) from rfl,
    repGaussOrder_normalForm_eq_iInf_termOrder _ IsDiscreteValuationRing.addVal_zero e t _ (constantCoeff_nfU_snd _ _),
    show ab = (ab.1, ab.2) from rfl,
    repGaussOrder_normalForm_eq_iInf_termOrder _ IsDiscreteValuationRing.addVal_zero e t _ hb]
  simp only [Prod.mk.eta]
  simp_rw [termOrder_nfU ϖ hϖ e t ht]
  rw [← ENat.iInf_add, iInf_comp_sub_one', add_left_inj_of_ne_top (ENat.coe_ne_top t)]

theorem mem_dominantIndices_nfV_iff (t : ℕ) (ht : t ≤ e) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices (IsDiscreteValuationRing.addVal W) e t (nfV (ϖ ^ e) ab) ↔
      n + 1 ∈ dominantIndices (IsDiscreteValuationRing.addVal W) e t ab := by
  simp only [dominantIndices, Set.mem_setOf_eq]
  rw [show (nfV (ϖ ^ e) ab) = ((nfV (ϖ ^ e) ab).1, (nfV (ϖ ^ e) ab).2) from rfl,
    repGaussOrder_normalForm_eq_iInf_termOrder _ IsDiscreteValuationRing.addVal_zero e t _ (constantCoeff_nfV_snd _ _),
    show ab = (ab.1, ab.2) from rfl,
    repGaussOrder_normalForm_eq_iInf_termOrder _ IsDiscreteValuationRing.addVal_zero e t _ hb]
  simp only [Prod.mk.eta]
  simp_rw [termOrder_nfV ϖ hϖ e t ht ab hb]
  rw [← ENat.iInf_add, iInf_comp_add_one', add_left_inj_of_ne_top (ENat.coe_ne_top _)]

omit hϖ in
theorem dominantIndices_nfC (t : ℕ) (w : W) (hw : w ≠ 0) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    dominantIndices (IsDiscreteValuationRing.addVal W) e t (nfC w ab) =
      dominantIndices (IsDiscreteValuationRing.addVal W) e t ab := by
  ext n
  simp only [dominantIndices, Set.mem_setOf_eq]
  rw [show (nfC w ab) = ((nfC w ab).1, (nfC w ab).2) from rfl,
    repGaussOrder_normalForm_eq_iInf_termOrder _ IsDiscreteValuationRing.addVal_zero e t _ (constantCoeff_nfC_snd _ _ hb),
    show ab = (ab.1, ab.2) from rfl,
    repGaussOrder_normalForm_eq_iInf_termOrder _ IsDiscreteValuationRing.addVal_zero e t _ hb]
  simp only [Prod.mk.eta]
  simp_rw [termOrder_nfC e t w]
  have hne : IsDiscreteValuationRing.addVal W w ≠ ⊤ := fun h => hw (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  rw [← ENat.iInf_add, add_left_inj_of_ne_top hne]

theorem dominantIndices_nfU_eq_image (t : ℕ) (ht : t ≤ e) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    dominantIndices (IsDiscreteValuationRing.addVal W) e t (nfU (ϖ ^ e) ab) =
      (fun n => n + 1) '' dominantIndices (IsDiscreteValuationRing.addVal W) e t ab := by
  ext n
  rw [mem_dominantIndices_nfU_iff ϖ hϖ e t ht ab hb, Set.mem_image]
  constructor
  · intro h; exact ⟨n - 1, h, by ring⟩
  · rintro ⟨m, hm, rfl⟩; simpa using hm

theorem dominantIndices_nfV_eq_image (t : ℕ) (ht : t ≤ e) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    dominantIndices (IsDiscreteValuationRing.addVal W) e t (nfV (ϖ ^ e) ab) =
      (fun n => n - 1) '' dominantIndices (IsDiscreteValuationRing.addVal W) e t ab := by
  ext n
  rw [mem_dominantIndices_nfV_iff ϖ hϖ e t ht ab hb, Set.mem_image]
  constructor
  · intro h; exact ⟨n + 1, h, by ring⟩
  · rintro ⟨m, hm, rfl⟩; simpa using hm

omit hϖ in

theorem sInf_image_add_const (S : Set ℤ) (hS : S.Nonempty) (hbdd : BddBelow S) (c : ℤ) :
    sInf ((fun n => n + c) '' S) = sInf S + c := by
  rw [show ((fun n => n + c) : ℤ → ℤ) = ⇑(OrderIso.addRight c) from rfl, ← (OrderIso.addRight c).map_csInf' hS hbdd]
  rfl

omit hϖ in
theorem sSup_image_add_const (S : Set ℤ) (hS : S.Nonempty) (hbdd : BddAbove S) (c : ℤ) :
    sSup ((fun n => n + c) '' S) = sSup S + c := by
  rw [show ((fun n => n + c) : ℤ → ℤ) = ⇑(OrderIso.addRight c) from rfl, ← (OrderIso.addRight c).map_csSup' hS hbdd]
  rfl

theorem leadingResidue_nfCoeff_nfU (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    leadingResidue ϖ (nfCoeff (nfU (ϖ ^ e) ab) n) = leadingResidue ϖ (nfCoeff ab (n - 1)) := by
  rw [nfCoeff_nfU]
  split_ifs
  · rw [one_mul]
  · exact leadingResidue_uniformizer_pow_mul ϖ hϖ e _

theorem leadingResidue_nfCoeff_nfV (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    leadingResidue ϖ (nfCoeff (nfV (ϖ ^ e) ab) n) = leadingResidue ϖ (nfCoeff ab (n + 1)) := by
  rw [nfCoeff_nfV _ _ hb]
  split_ifs
  · exact leadingResidue_uniformizer_pow_mul ϖ hϖ e _
  · rw [one_mul]

theorem leadingResidue_nfCoeff_nfC (w : W) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    leadingResidue ϖ (nfCoeff (nfC w ab) n) = leadingResidue ϖ w * leadingResidue ϖ (nfCoeff ab n) := by
  rw [nfCoeff_nfC, leadingResidue_mul ϖ hϖ]

end ShiftOrders
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "unitPart pow_multiplicity_mul_unitPart leadingResidue mk U V const constHom constHom_apply mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete existsUnique_normalForm finsum_rank_mul_length_eq_sInf_sub_sSup setOf_horizontal_mem_finite exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem U_mul_V leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff exists_prime_V_sub_const_pow_mem"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_scaled_eq_repGaussOrder_normalForm~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_scaled_eq_repGaussOrder_normalForm~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

namespace BToolkit

variable {R : Type u} [CommRing R]

noncomputable def mulQuot (x y : R) : (R ⧸ Ideal.span {y}) →ₗ[R] (R ⧸ Ideal.span {x * y}) :=
  Submodule.mapQ (Ideal.span {y}) (Ideal.span {x * y}) (LinearMap.mulLeft R x) (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩)

theorem mulQuot_mk (x y r : R) :
    mulQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (x * r) := rfl

noncomputable def projQuot (x y : R) : (R ⧸ Ideal.span {x * y}) →ₗ[R] (R ⧸ Ideal.span {x}) :=
  Submodule.mapQ (Ideal.span {x * y}) (Ideal.span {x}) LinearMap.id (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.id_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c * y, by ring⟩)

theorem projQuot_mk (x y r : R) :
    projQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := rfl

theorem projQuot_surjective (x y : R) : Function.Surjective (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  exact ⟨Ideal.Quotient.mk _ r, rfl⟩

theorem mulQuot_injective [IsDomain R] (x y : R) (hx : x ≠ 0) : Function.Injective (mulQuot x y) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [LinearMap.mem_ker, mulQuot_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hm
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.mem_span_singleton'.mpr ⟨s, mul_left_cancel₀ hx ?_⟩
  rw [← hs]; ring

theorem exact_mulQuot_projQuot (x y : R) : Function.Exact (mulQuot x y) (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [projQuot_mk, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    exact ⟨Ideal.Quotient.mk _ c, by rw [mulQuot_mk, mul_comm x c]⟩
  · rintro ⟨m', hm'⟩
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
    rw [mulQuot_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hm'
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hm'
    refine Ideal.mem_span_singleton'.mpr ⟨r' - s * y, ?_⟩
    have : r = x * r' - s * (x * y) := by rw [hs]; ring
    rw [this]; ring

theorem length_localized_quotient_mul [IsDomain R] (S : Submonoid R) (x y : R) (hx : x ≠ 0) :
    Module.length (Localization S) (LocalizedModule S (R ⧸ Ideal.span {x * y})) =
      Module.length (Localization S) (LocalizedModule S (R ⧸ Ideal.span {y})) +
        Module.length (Localization S) (LocalizedModule S (R ⧸ Ideal.span {x})) := by
  refine Module.length_eq_add_of_exact (LocalizedModule.map S (mulQuot x y)) (LocalizedModule.map S (projQuot x y))
    (LocalizedModule.map_injective S _ (mulQuot_injective x y hx))
    (LocalizedModule.map_surjective S _ (projQuot_surjective x y)) ?_
  exact LocalizedModule.map_exact S (mulQuot x y) (projQuot x y) (exact_mulQuot_projQuot x y)

theorem subsingleton_localized_quotient (P : Ideal R) [P.IsPrime] (x : R) (hx : x ∉ P) :
    Subsingleton (LocalizedModule P.primeCompl (R ⧸ Ideal.span {x})) := by
  rw [LocalizedModule.subsingleton_iff]
  intro m
  refine ⟨x, hx, ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [← Ideal.Quotient.mkₐ_eq_mk R, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
  exact Ideal.mem_span_singleton'.mpr ⟨r, mul_comm r x⟩

theorem length_localized_quotient_eq_zero (P : Ideal R) [P.IsPrime] (x : R) (hx : x ∉ P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ Ideal.span {x})) = 0 :=
  Module.length_eq_zero_iff.mpr (subsingleton_localized_quotient P x hx)

end BToolkit
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section BRing

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

noncomputable def horizResProd (ϖ : W) (e : ℕ) (x : UVCrossingModel W (ϖ ^ e)) : ResidueField W :=
  ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
    (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal),
    residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
      (Module.length (Localization.AtPrime Q.asIdeal)
        (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat

noncomputable def horizResFactor (ϖ : W) (e : ℕ) (x : UVCrossingModel W (ϖ ^ e))
    (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) : ResidueField W :=
  residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
    (Module.length (Localization.AtPrime Q.asIdeal)
      (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat

theorem horizResFactor_eq_one_of_not_mem (ϖ : W) (e : ℕ) (x : UVCrossingModel W (ϖ ^ e))
    (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (hxQ : x ∉ Q.asIdeal) : horizResFactor ϖ e x Q = 1 := by
  haveI := Q.isPrime
  rw [horizResFactor, BToolkit.length_localized_quotient_eq_zero Q.asIdeal x hxQ, ENat.toNat_zero, pow_zero]

theorem horizResProd_eq_finprod_mem (ϖ : W) (e : ℕ) (x : UVCrossingModel W (ϖ ^ e)) :
    horizResProd ϖ e x = ∏ᶠ Q ∈ {Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) |
      Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal}, horizResFactor ϖ e x Q := by
  rw [horizResProd]
  change (∏ᶠ Q ∈ {Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) |
      Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal}, horizResFactor ϖ e x Q) = _
  apply finprod_mem_inter_mulSupport_eq
  ext Q
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_mulSupport]
  constructor
  · rintro ⟨⟨h1, h2, -⟩, h4⟩; exact ⟨⟨h1, h2⟩, h4⟩
  · rintro ⟨⟨h1, h2⟩, h4⟩
    refine ⟨⟨h1, h2, ?_⟩, h4⟩
    by_contra hxQ
    exact h4 (horizResFactor_eq_one_of_not_mem ϖ e x Q hxQ)

theorem horizResProd_eq_one_of_forall_not_mem (ϖ : W) (e : ℕ) (x : UVCrossingModel W (ϖ ^ e))
    (h : ∀ Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)), Q.asIdeal ≠ ⊥ → const (ϖ ^ e) ϖ ∉ Q.asIdeal →
      x ∉ Q.asIdeal) : horizResProd ϖ e x = 1 := by
  rw [horizResProd_eq_finprod_mem]
  exact finprod_mem_of_eqOn_one fun Q hQ => horizResFactor_eq_one_of_not_mem ϖ e x Q (h Q hQ.1 hQ.2)

theorem const_not_mem_of_horizontal (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ)
    (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (hQϖ : const (ϖ ^ e) ϖ ∉ Q.asIdeal)
    (c : W) (hc : c ≠ 0) : const (ϖ ^ e) c ∉ Q.asIdeal := by
  haveI := Q.isPrime
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  intro hmem
  rw [← constHom_apply, map_mul, map_pow, constHom_apply, constHom_apply] at hmem
  rcases Q.isPrime.mem_or_mem hmem with h | h
  · exact Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ((u.isUnit.map (constHom (ϖ ^ e)))))
  · exact hQϖ (Q.isPrime.mem_of_pow_mem n h)

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem U_not_mem_of_horizontal (ϖ : W) (e : ℕ)
    (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (hQϖ : const (ϖ ^ e) ϖ ∉ Q.asIdeal) :
    U (ϖ ^ e) ∉ Q.asIdeal := by
  haveI := Q.isPrime
  intro hU
  have h : const (ϖ ^ e) (ϖ ^ e) ∈ Q.asIdeal := by
    rw [← U_mul_V]; exact Ideal.mul_mem_right _ _ hU
  rw [← constHom_apply, map_pow, constHom_apply] at h
  exact hQϖ (Q.isPrime.mem_of_pow_mem e h)

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem V_not_mem_of_horizontal (ϖ : W) (e : ℕ)
    (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (hQϖ : const (ϖ ^ e) ϖ ∉ Q.asIdeal) :
    V (ϖ ^ e) ∉ Q.asIdeal := by
  haveI := Q.isPrime
  intro hV
  have h : const (ϖ ^ e) (ϖ ^ e) ∈ Q.asIdeal := by
    rw [← U_mul_V]; exact Ideal.mul_mem_left _ _ hV
  rw [← constHom_apply, map_pow, constHom_apply] at h
  exact hQϖ (Q.isPrime.mem_of_pow_mem e h)

theorem horizResProd_const (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (c : W) (hc : c ≠ 0) :
    horizResProd ϖ e (const (ϖ ^ e) c) = 1 :=
  horizResProd_eq_one_of_forall_not_mem ϖ e _ fun Q _ hQϖ => const_not_mem_of_horizontal ϖ hϖ e Q hQϖ c hc

theorem horizResProd_U (ϖ : W) (e : ℕ) : horizResProd ϖ e (U (ϖ ^ e)) = 1 :=
  horizResProd_eq_one_of_forall_not_mem ϖ e _ fun Q _ hQϖ => U_not_mem_of_horizontal ϖ e Q hQϖ

theorem horizResProd_V (ϖ : W) (e : ℕ) : horizResProd ϖ e (V (ϖ ^ e)) = 1 :=
  horizResProd_eq_one_of_forall_not_mem ϖ e _ fun Q _ hQϖ => V_not_mem_of_horizontal ϖ e Q hQϖ

variable [IsAdicComplete (maximalIdeal W) W]

theorem length_localized_quotient_ne_top (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) (hQ0 : Q.asIdeal ≠ ⊥) (hQϖ : const (ϖ ^ e) ϖ ∉ Q.asIdeal) :
    Module.length (Localization.AtPrime Q.asIdeal)
      (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) ≠ ⊤ := by
  classical
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal W) W)
  obtain ⟨ab, ⟨hb, habx⟩, -⟩ := existsUnique_normalForm ϖ e he x
  have htot := finsum_rank_mul_length_eq_sInf_sub_sSup ϖ hϖ e he 1 le_rfl x hx ab hb habx
  set S : Set (PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) := {P | P.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ P.asIdeal} with hS
  set g : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) → ℕ∞ := fun P =>
    (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ P.asIdeal) : ℕ∞) *
      Module.length (Localization.AtPrime P.asIdeal)
        (LocalizedModule P.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) with hg
  change ∑ᶠ P ∈ S, g P = _ at htot
  have hfin := setOf_horizontal_mem_finite ϖ hϖ e he x hx
  have hsupp : S ∩ Function.support g ⊆
      {P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) | P.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ P.asIdeal ∧ x ∈ P.asIdeal} := by
    rintro P ⟨⟨hP1, hP2⟩, hP3⟩
    refine ⟨hP1, hP2, ?_⟩
    by_contra hxP
    apply hP3
    haveI : P.asIdeal.IsPrime := P.isPrime
    show g P = 0
    rw [hg]
    simp only
    rw [BToolkit.length_localized_quotient_eq_zero P.asIdeal x hxP, mul_zero]
  have hfin' : (S ∩ Function.support g).Finite := hfin.subset hsupp
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin'] at htot
  intro htop
  by_cases hgQ : g Q = 0
  · rw [hg] at hgQ
    simp only [mul_eq_zero, Nat.cast_eq_zero] at hgQ
    rcases hgQ with h | h
    · have hrk := (exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem ϖ hϖ e he Q hQ0 hQϖ).1
      omega
    · rw [h] at htop; exact ENat.zero_ne_top htop
  · have hmem : Q ∈ hfin'.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨⟨hQ0, hQϖ⟩, hgQ⟩
    have hle := Finset.single_le_sum (f := g) (fun P _ => zero_le) hmem
    rw [htot] at hle
    have hgtop : g Q = ⊤ := by
      rw [hg]
      simp only
      rw [htop, ENat.mul_top]
      have hrk := (exists_mul_length_eq_mul_finrank_of_ne_bot_of_const_notMem ϖ hϖ e he Q hQ0 hQϖ).1
      exact_mod_cast (show Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Q.asIdeal) ≠ 0 by omega)
    rw [hgtop] at hle
    exact ENat.coe_ne_top _ (le_antisymm le_top hle)

theorem horizResProd_mul (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x z : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0) (hz : z ≠ 0) :
    horizResProd ϖ e (x * z) = horizResProd ϖ e x * horizResProd ϖ e z := by
  classical
  haveI : IsDomain (UVCrossingModel W (ϖ ^ e)) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ e he).1
  rw [horizResProd_eq_finprod_mem, horizResProd_eq_finprod_mem, horizResProd_eq_finprod_mem]
  set H : Set (PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) := {Q | Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal} with hH

  have hsuppfin : ∀ y : UVCrossingModel W (ϖ ^ e), y ≠ 0 → (H ∩ Function.mulSupport (horizResFactor ϖ e y)).Finite := by
    intro y hy
    refine (setOf_horizontal_mem_finite ϖ hϖ e he y hy).subset ?_
    rintro Q ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, ?_⟩
    by_contra hyQ
    exact h3 (horizResFactor_eq_one_of_not_mem ϖ e y Q hyQ)
  rw [← finprod_mem_mul_distrib' (hsuppfin x hx) (hsuppfin z hz)]
  refine finprod_mem_congr rfl fun Q hQ => ?_
  haveI : Q.asIdeal.IsPrime := Q.isPrime
  rw [horizResFactor, horizResFactor, horizResFactor, ← pow_add]
  congr 1
  rw [BToolkit.length_localized_quotient_mul Q.asIdeal.primeCompl x z hx, add_comm,
    ENat.toNat_add (length_localized_quotient_ne_top ϖ hϖ e he x hx Q hQ.1 hQ.2)
      (length_localized_quotient_ne_top ϖ hϖ e he z hz Q hQ.1 hQ.2)]

theorem horizResProd_V_sub_const_pow (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e) :
    horizResProd ϖ e (V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d)) = 1 := by
  classical
  obtain ⟨Qd, hQ0, hQϖ, hVQ, -, huniq, -, -, -, hnorm, hlen⟩ := exists_prime_V_sub_const_pow_mem ϖ hϖ e he d hd1 hde
  rw [horizResProd]
  have hset : {Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) | Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧
      V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ∈ Q.asIdeal} = {Qd} := by
    ext Q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨-, h2, h3⟩; exact huniq Q h2 h3
    · rintro rfl; exact ⟨hQ0, hQϖ, hVQ⟩
  change (∏ᶠ Q ∈ {Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)) | Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧
      V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ∈ Q.asIdeal}, horizResFactor ϖ e (V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d)) Q) = 1
  rw [hset, finprod_mem_singleton, horizResFactor, hnorm, hlen,
    (multiplicity_eq_and_unitPart_eq_of_eq_pow_mul ϖ hϖ isUnit_one (mul_one (ϖ ^ d)).symm).2, map_one, one_pow]

end BRing
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section BEnds

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

noncomputable def gNF (e t : ℕ) (ab : PowerSeries W × PowerSeries W) : ℕ∞ :=
  ⨅ n : ℤ, termOrder (IsDiscreteValuationRing.addVal W) e t ab n

theorem gNF_le (e t : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    gNF e t ab ≤ termOrder (IsDiscreteValuationRing.addVal W) e t ab n := iInf_le _ n

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem enat_iInf_add_const {ι : Type*} [Nonempty ι] (f : ι → ℕ∞) (c : ℕ∞) :
    (⨅ i, (f i + c)) = (⨅ i, f i) + c :=
  (enat_map_iInf_eq_of_monotone (fun x => x + c) (fun _ _ h => add_le_add h le_rfl) f).symm

theorem gNF_nfC (e t : ℕ) (w : W) (ab : PowerSeries W × PowerSeries W) :
    gNF e t (nfC w ab) = gNF e t ab + IsDiscreteValuationRing.addVal W w := by
  rw [gNF, gNF, ← enat_iInf_add_const]
  exact iInf_congr fun n => termOrder_nfC e t w ab n

theorem gNF_nfU (ϖ : W) (hϖ : Irreducible ϖ) (e t : ℕ) (ht : t ≤ e) (ab : PowerSeries W × PowerSeries W) :
    gNF e t (nfU (ϖ ^ e) ab) = gNF e t ab + t := by
  rw [gNF, gNF, ← enat_iInf_add_const]
  rw [show (⨅ n : ℤ, termOrder (IsDiscreteValuationRing.addVal W) e t (nfU (ϖ ^ e) ab) n) =
      ⨅ n : ℤ, (termOrder (IsDiscreteValuationRing.addVal W) e t ab (n - 1) + (t : ℕ∞)) from
    iInf_congr fun n => termOrder_nfU ϖ hϖ e t ht ab n]
  exact Function.Surjective.iInf_comp (f := fun n : ℤ => n - 1) (fun m : ℤ => ⟨m + 1, by ring⟩)
    (fun m : ℤ => termOrder (IsDiscreteValuationRing.addVal W) e t ab m + (t : ℕ∞))

theorem gNF_nfV (ϖ : W) (hϖ : Irreducible ϖ) (e t : ℕ) (ht : t ≤ e) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    gNF e t (nfV (ϖ ^ e) ab) = gNF e t ab + (e - t : ℕ) := by
  rw [gNF, gNF, ← enat_iInf_add_const]
  rw [show (⨅ n : ℤ, termOrder (IsDiscreteValuationRing.addVal W) e t (nfV (ϖ ^ e) ab) n) =
      ⨅ n : ℤ, (termOrder (IsDiscreteValuationRing.addVal W) e t ab (n + 1) + ((e - t : ℕ) : ℕ∞)) from
    iInf_congr fun n => termOrder_nfV ϖ hϖ e t ht ab hb n]
  exact Function.Surjective.iInf_comp (f := fun n : ℤ => n + 1) (fun m : ℤ => ⟨m - 1, by ring⟩)
    (fun m : ℤ => termOrder (IsDiscreteValuationRing.addVal W) e t ab m + ((e - t : ℕ) : ℕ∞))

theorem gNF_lt_top (e t : ℕ) (π : W) (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) : gNF e t ab < ⊤ :=
  iInf_termOrder_lt_top _ (fun _ h => IsDiscreteValuationRing.addVal_eq_top_iff.mp h) π e t ab hb hx

def EndRatioIdentity (ϖ : W) (e : ℕ) (x : UVCrossingModel W (ϖ ^ e)) (ab : PowerSeries W × PowerSeries W) : Prop :=
  leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) *
      horizResProd ϖ e x =
    (-1) ^ (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)).toNat *
      leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab)))

theorem leadingResidue_uniformizer (ϖ : W) (hϖ : Irreducible ϖ) : leadingResidue ϖ ϖ = 1 := by
  rw [leadingResidue_of_ne_zero ϖ hϖ.ne_zero,
    (multiplicity_eq_and_unitPart_eq_of_eq_pow_mul ϖ hϖ isUnit_one (show ϖ = ϖ ^ 1 * 1 by ring)).2, map_one]

variable [IsAdicComplete (maximalIdeal W) W]

theorem normalForm_eq_zero (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (h : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = 0) : ab = (0, 0) := by
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal W) W)
  have h0 : PowerSeries.constantCoeff ((0, 0) : PowerSeries W × PowerSeries W).2 = 0 ∧
      mk (ϖ ^ e) (inU ((0, 0) : PowerSeries W × PowerSeries W).1 + inV ((0, 0) : PowerSeries W × PowerSeries W).2) = 0 := by
    refine ⟨map_zero _, ?_⟩
    show mk (ϖ ^ e) (inU 0 + inV 0) = 0
    rw [inU_zero, inV_zero, add_zero, map_zero]
  exact (existsUnique_normalForm ϖ e he (0 : UVCrossingModel W (ϖ ^ e))).unique ⟨hb, h⟩ h0

theorem mk_ne_zero_of_ne (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (hab : ab ≠ (0, 0)) :
    mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 :=
  fun h => hab (normalForm_eq_zero ϖ hϖ e he ab hb h)

theorem const_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (c : W) (hc : c ≠ 0) :
    const (ϖ ^ e) c ≠ 0 := by
  have h := mk_ne_zero_of_ne ϖ hϖ e he (PowerSeries.C c, 0) (map_zero _)
    (fun h => hc (by simpa using congrArg (fun ab : PowerSeries W × PowerSeries W => PowerSeries.constantCoeff ab.1) h))
  rwa [inU_C, inV_zero, add_zero] at h

theorem U_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) : U (ϖ ^ e) ≠ 0 := by
  intro h
  apply const_ne_zero ϖ hϖ e he (ϖ ^ e) (pow_ne_zero e hϖ.ne_zero)
  rw [← U_mul_V, h, zero_mul]

theorem V_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) : V (ϖ ^ e) ≠ 0 := by
  intro h
  apply const_ne_zero ϖ hϖ e he (ϖ ^ e) (pow_ne_zero e hϖ.ne_zero)
  rw [← U_mul_V, h, mul_zero]

theorem endRatioIdentity_const_mul (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (z : UVCrossingModel W (ϖ ^ e)) (hz : z ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (h : EndRatioIdentity ϖ e z ab) : EndRatioIdentity ϖ e (const (ϖ ^ e) ϖ * z) (nfC ϖ ab) := by
  unfold EndRatioIdentity at h ⊢
  rw [dominantIndices_nfC e 0 ϖ hϖ.ne_zero ab hb, dominantIndices_nfC e e ϖ hϖ.ne_zero ab hb,
    leadingResidue_nfCoeff_nfC ϖ hϖ, leadingResidue_nfCoeff_nfC ϖ hϖ, leadingResidue_uniformizer ϖ hϖ, one_mul,
    one_mul, horizResProd_mul ϖ hϖ e he _ _ (const_ne_zero ϖ hϖ e he ϖ hϖ.ne_zero) hz,
    horizResProd_const ϖ hϖ e ϖ hϖ.ne_zero, one_mul]
  exact h

theorem endRatioIdentity_U_mul (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (z : UVCrossingModel W (ϖ ^ e)) (hz : z ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habz : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = z)
    (h : EndRatioIdentity ϖ e z ab) : EndRatioIdentity ϖ e (U (ϖ ^ e) * z) (nfU (ϖ ^ e) ab) := by
  have hv0 : IsDiscreteValuationRing.addVal W 0 = ⊤ := IsDiscreteValuationRing.addVal_zero
  have hne : (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab).Nonempty :=
    dominantIndices_nonempty _ hv0 e 0 ab hb
  have hne' : (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab).Nonempty :=
    dominantIndices_nonempty _ hv0 e e ab hb
  have hfin0 := gNF_lt_top e 0 (ϖ ^ e) ab hb (by rw [habz]; exact hz)
  have hfine := gNF_lt_top e e (ϖ ^ e) ab hb (by rw [habz]; exact hz)
  have hbb : BddBelow (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) :=
    dominantIndices_bddBelow _ hv0 e 0 (by omega) ab hb hfin0
  have hba : BddAbove (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) :=
    dominantIndices_bddAbove _ hv0 e e (by omega) ab hb hfine
  unfold EndRatioIdentity at h ⊢
  rw [dominantIndices_nfU_eq_image ϖ hϖ e 0 (by omega) ab hb, dominantIndices_nfU_eq_image ϖ hϖ e e le_rfl ab hb,
    sInf_image_add_const _ hne hbb 1, sSup_image_add_const _ hne' hba 1,
    leadingResidue_nfCoeff_nfU ϖ hϖ e, leadingResidue_nfCoeff_nfU ϖ hϖ e, add_sub_cancel_right, add_sub_cancel_right,
    add_sub_add_right_eq_sub,
    horizResProd_mul ϖ hϖ e he _ _ (U_ne_zero ϖ hϖ e he) hz, horizResProd_U ϖ e, one_mul]
  exact h

theorem endRatioIdentity_V_mul (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (z : UVCrossingModel W (ϖ ^ e)) (hz : z ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habz : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = z)
    (h : EndRatioIdentity ϖ e z ab) : EndRatioIdentity ϖ e (V (ϖ ^ e) * z) (nfV (ϖ ^ e) ab) := by
  have hv0 : IsDiscreteValuationRing.addVal W 0 = ⊤ := IsDiscreteValuationRing.addVal_zero
  have hne : (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab).Nonempty :=
    dominantIndices_nonempty _ hv0 e 0 ab hb
  have hne' : (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab).Nonempty :=
    dominantIndices_nonempty _ hv0 e e ab hb
  have hfin0 := gNF_lt_top e 0 (ϖ ^ e) ab hb (by rw [habz]; exact hz)
  have hfine := gNF_lt_top e e (ϖ ^ e) ab hb (by rw [habz]; exact hz)
  have hbb : BddBelow (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) :=
    dominantIndices_bddBelow _ hv0 e 0 (by omega) ab hb hfin0
  have hba : BddAbove (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) :=
    dominantIndices_bddAbove _ hv0 e e (by omega) ab hb hfine
  have himg : (fun n : ℤ => n - 1) = (fun n : ℤ => n + (-1)) := by funext n; ring
  unfold EndRatioIdentity at h ⊢
  rw [dominantIndices_nfV_eq_image ϖ hϖ e 0 (by omega) ab hb, dominantIndices_nfV_eq_image ϖ hϖ e e le_rfl ab hb, himg,
    sInf_image_add_const _ hne hbb (-1), sSup_image_add_const _ hne' hba (-1),
    leadingResidue_nfCoeff_nfV ϖ hϖ e ab hb, leadingResidue_nfCoeff_nfV ϖ hϖ e ab hb, neg_add_cancel_right,
    neg_add_cancel_right, add_sub_add_right_eq_sub,
    horizResProd_mul ϖ hϖ e he _ _ (V_ne_zero ϖ hϖ e he) hz, horizResProd_V ϖ e, one_mul]
  exact h

end BEnds
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section BAux

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

noncomputable def nfY (ϖ : W) (e d : ℕ) (ab : PowerSeries W × PowerSeries W) : PowerSeries W × PowerSeries W :=
  ((nfV (ϖ ^ e) ab).1 - (nfC (ϖ ^ d) ab).1, (nfV (ϖ ^ e) ab).2 - (nfC (ϖ ^ d) ab).2)

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem constantCoeff_nfY_snd (ϖ : W) (e d : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) : PowerSeries.constantCoeff (nfY ϖ e d ab).2 = 0 := by
  rw [nfY, map_sub, constantCoeff_nfV_snd, constantCoeff_nfC_snd _ _ hb, sub_zero]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem mk_nfY (ϖ : W) (e d : ℕ) (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) :
    mk (ϖ ^ e) (inU (nfY ϖ e d ab).1 + inV (nfY ϖ e d ab).2) =
      mk (ϖ ^ e) (inU ab.1 + inV ab.2) * (V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d)) := by
  rw [nfY, AnnulusNF.inU_sub, AnnulusNF.inV_sub, show ∀ a b c d : MvPowerSeries (Fin 2) W, a - b + (c - d) = (a + c) - (b + d) from
    fun a b c d => by ring, map_sub, mk_nfV _ _ hb, mk_nfC, mul_sub, mul_comm (V (ϖ ^ e)), mul_comm (const (ϖ ^ e) (ϖ ^ d))]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem nfCoeff_sub_sub (a a' b b' : PowerSeries W) (n : ℤ) :
    nfCoeff (a - a', b - b') n = nfCoeff (a, b) n - nfCoeff (a', b') n := by
  cases n with
  | ofNat i => simp only [Int.ofNat_eq_natCast, nfCoeff_natCast, map_sub]
  | negSucc j => simp only [nfCoeff_negSucc, map_sub]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem nfCoeff_nfY (ϖ : W) (e d : ℕ) (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (n : ℤ) : nfCoeff (nfY ϖ e d ab) n = nfCoeff (nfV (ϖ ^ e) ab) n - ϖ ^ d * nfCoeff ab n := by
  rw [nfY, nfCoeff_sub_sub, ← nfCoeff_nfC (ϖ ^ d) ab n]

theorem termOrder_eq_addVal_add (e t : ℕ) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder (IsDiscreteValuationRing.addVal W) e t ab n =
      IsDiscreteValuationRing.addVal W (nfCoeff ab n) + (annulusWeight e t (nfExponent n) : ℕ∞) := rfl

variable [IsAdicComplete (maximalIdeal W) W]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in
theorem inV_X : inV (PowerSeries.X : PowerSeries W) = (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) := by
  have h := X_one_mul_inV (PowerSeries.C (1 : W))
  rw [inV_C, map_one, mul_one, map_one, mul_one] at h
  exact h.symm

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in
theorem mk_V_sub_const_pow (ϖ : W) (e d : ℕ) :
    mk (ϖ ^ e) (inU (PowerSeries.C (-ϖ ^ d)) + inV PowerSeries.X) = V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) := by
  rw [inU_C, inV_X, map_add, ← constHom_apply, sub_eq_neg_add, ← map_neg, constHom_apply]
  rfl

theorem V_sub_const_pow_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (d : ℕ) :
    V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d) ≠ 0 := by
  rw [← mk_V_sub_const_pow]
  exact mk_ne_zero_of_ne ϖ hϖ e he (PowerSeries.C (-ϖ ^ d), PowerSeries.X) (by simp)
    (fun h => absurd (congrArg (fun ab : PowerSeries W × PowerSeries W => PowerSeries.coeff 1 ab.2) h) (by simp))

end BAux
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section BAuxEnds

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem BaddVal_uniformizer_pow (ϖ : W) (hϖ : Irreducible ϖ) (n : ℕ) :
    IsDiscreteValuationRing.addVal W (ϖ ^ n) = n := by
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]; simp

theorem min_le_termOrder_nfY (ϖ : W) (hϖ : Irreducible ϖ) (e t : ℕ) (ht : t ≤ e) (d : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    min (termOrder (IsDiscreteValuationRing.addVal W) e t ab (n + 1) + ((e - t : ℕ) : ℕ∞))
        (termOrder (IsDiscreteValuationRing.addVal W) e t ab n + d) ≤
      termOrder (IsDiscreteValuationRing.addVal W) e t (nfY ϖ e d ab) n := by
  have hd : IsDiscreteValuationRing.addVal W (ϖ ^ d * nfCoeff ab n) = IsDiscreteValuationRing.addVal W (nfCoeff ab n) + d := by
    rw [IsDiscreteValuationRing.addVal_mul, BaddVal_uniformizer_pow ϖ hϖ d, add_comm]
  rw [← termOrder_nfV ϖ hϖ e t ht ab hb n, termOrder_eq_addVal_add e t (nfY ϖ e d ab) n,
    termOrder_eq_addVal_add e t (nfV (ϖ ^ e) ab) n, termOrder_eq_addVal_add e t ab n, nfCoeff_nfY ϖ e d ab hb n,
    add_right_comm, ← hd, min_add_add_right]
  exact add_le_add (AddValuation.map_sub _ _ _) le_rfl

theorem termOrder_nfY_of_lt_left (ϖ : W) (hϖ : Irreducible ϖ) (e t : ℕ) (ht : t ≤ e) (d : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ)
    (hlt : termOrder (IsDiscreteValuationRing.addVal W) e t ab (n + 1) + ((e - t : ℕ) : ℕ∞) <
      termOrder (IsDiscreteValuationRing.addVal W) e t ab n + d) :
    termOrder (IsDiscreteValuationRing.addVal W) e t (nfY ϖ e d ab) n =
        termOrder (IsDiscreteValuationRing.addVal W) e t ab (n + 1) + ((e - t : ℕ) : ℕ∞) ∧
      leadingResidue ϖ (nfCoeff (nfY ϖ e d ab) n) = leadingResidue ϖ (nfCoeff ab (n + 1)) := by
  have hd : IsDiscreteValuationRing.addVal W (ϖ ^ d * nfCoeff ab n) = IsDiscreteValuationRing.addVal W (nfCoeff ab n) + d := by
    rw [IsDiscreteValuationRing.addVal_mul, BaddVal_uniformizer_pow ϖ hϖ d, add_comm]
  rw [← termOrder_nfV ϖ hϖ e t ht ab hb n, termOrder_eq_addVal_add e t (nfV (ϖ ^ e) ab) n,
    termOrder_eq_addVal_add e t ab n, add_right_comm, ← hd] at hlt
  have hlt' : IsDiscreteValuationRing.addVal W (nfCoeff (nfV (ϖ ^ e) ab) n) <
      IsDiscreteValuationRing.addVal W (ϖ ^ d * nfCoeff ab n) := lt_of_add_lt_add_right hlt
  have hlt'' : IsDiscreteValuationRing.addVal W (nfCoeff (nfV (ϖ ^ e) ab) n) <
      IsDiscreteValuationRing.addVal W (-(ϖ ^ d * nfCoeff ab n)) := by rwa [AddValuation.map_neg]
  refine ⟨?_, ?_⟩
  · rw [← termOrder_nfV ϖ hϖ e t ht ab hb n, termOrder_eq_addVal_add e t (nfY ϖ e d ab) n,
      termOrder_eq_addVal_add e t (nfV (ϖ ^ e) ab) n,
      nfCoeff_nfY ϖ e d ab hb n, sub_eq_add_neg, AddValuation.map_add_of_distinct_val _ hlt''.ne, min_eq_left hlt''.le]
  · rw [nfCoeff_nfY ϖ e d ab hb n, sub_eq_add_neg, leadingResidue_add_of_addVal_lt ϖ hϖ hlt'',
      leadingResidue_nfCoeff_nfV ϖ hϖ e ab hb n]

theorem termOrder_nfY_of_lt_right (ϖ : W) (hϖ : Irreducible ϖ) (e t : ℕ) (ht : t ≤ e) (d : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ)
    (hlt : termOrder (IsDiscreteValuationRing.addVal W) e t ab n + d <
      termOrder (IsDiscreteValuationRing.addVal W) e t ab (n + 1) + ((e - t : ℕ) : ℕ∞)) :
    termOrder (IsDiscreteValuationRing.addVal W) e t (nfY ϖ e d ab) n =
        termOrder (IsDiscreteValuationRing.addVal W) e t ab n + d ∧
      leadingResidue ϖ (nfCoeff (nfY ϖ e d ab) n) = -leadingResidue ϖ (nfCoeff ab n) := by
  have hd : IsDiscreteValuationRing.addVal W (ϖ ^ d * nfCoeff ab n) = IsDiscreteValuationRing.addVal W (nfCoeff ab n) + d := by
    rw [IsDiscreteValuationRing.addVal_mul, BaddVal_uniformizer_pow ϖ hϖ d, add_comm]
  rw [← termOrder_nfV ϖ hϖ e t ht ab hb n, termOrder_eq_addVal_add e t ab n,
    termOrder_eq_addVal_add e t (nfV (ϖ ^ e) ab) n, add_right_comm, ← hd] at hlt
  have hlt' : IsDiscreteValuationRing.addVal W (ϖ ^ d * nfCoeff ab n) <
      IsDiscreteValuationRing.addVal W (nfCoeff (nfV (ϖ ^ e) ab) n) := lt_of_add_lt_add_right hlt
  have hlt'' : IsDiscreteValuationRing.addVal W (-(ϖ ^ d * nfCoeff ab n)) <
      IsDiscreteValuationRing.addVal W (nfCoeff (nfV (ϖ ^ e) ab) n) := by rwa [AddValuation.map_neg]
  refine ⟨?_, ?_⟩
  · rw [termOrder_eq_addVal_add e t (nfY ϖ e d ab) n, termOrder_eq_addVal_add e t ab n, nfCoeff_nfY ϖ e d ab hb n,
      sub_eq_neg_add, AddValuation.map_add_of_distinct_val _ hlt''.ne, min_eq_left hlt''.le, AddValuation.map_neg, hd,
      add_right_comm]
  · rw [nfCoeff_nfY ϖ e d ab hb n, sub_eq_neg_add, leadingResidue_add_of_addVal_lt ϖ hϖ hlt'', leadingResidue_neg ϖ hϖ,
      leadingResidue_uniformizer_pow_mul ϖ hϖ]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem enat_add_natCast_lt_add_natCast_right {a : ℕ∞} (ha : a ≠ ⊤) {c d : ℕ} (hcd : c < d) :
    a + (c : ℕ∞) < a + (d : ℕ∞) := by
  lift a to ℕ using ha
  exact_mod_cast Nat.add_lt_add_left hcd a

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem enat_add_natCast_lt_add_natCast_left {a b : ℕ∞} (hab : a < b) (c : ℕ) :
    a + (c : ℕ∞) < b + (c : ℕ∞) := by
  have ha : a ≠ ⊤ := ne_top_of_lt hab
  lift a to ℕ using ha
  induction b using ENat.recTopCoe with
  | top => rw [top_add]; exact WithTop.coe_lt_top (a + c)
  | coe b => exact_mod_cast Nat.add_lt_add_right (by exact_mod_cast hab) c

theorem nfY_end_data (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0)
    (d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e) :
    sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 (nfY ϖ e d ab)) =
        sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) ∧
      sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e (nfY ϖ e d ab)) =
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) - 1 ∧
      leadingResidue ϖ (nfCoeff (nfY ϖ e d ab) (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) =
        -leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) ∧
      leadingResidue ϖ (nfCoeff (nfY ϖ e d ab) (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) - 1)) =
        leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) ∧
      gNF e 0 (nfY ϖ e d ab) = gNF e 0 ab + d ∧ gNF e e (nfY ϖ e d ab) = gNF e e ab := by
  have hv0 : IsDiscreteValuationRing.addVal W 0 = ⊤ := IsDiscreteValuationRing.addVal_zero
  have hbY := constantCoeff_nfY_snd ϖ e d ab hb

  set n₀ := sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) with hn₀
  set nₑ := sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) with hnₑ
  have hne0 : (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab).Nonempty := dominantIndices_nonempty _ hv0 e 0 ab hb
  have hnee : (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab).Nonempty := dominantIndices_nonempty _ hv0 e e ab hb
  have hfin0 : gNF e 0 ab < ⊤ := gNF_lt_top e 0 (ϖ ^ e) ab hb hx
  have hfine : gNF e e ab < ⊤ := gNF_lt_top e e (ϖ ^ e) ab hb hx
  have hbb : BddBelow (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) :=
    dominantIndices_bddBelow _ hv0 e 0 (by omega) ab hb hfin0
  have hba : BddAbove (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) :=
    dominantIndices_bddAbove _ hv0 e e (by omega) ab hb hfine
  have hn₀mem : n₀ ∈ dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab := Int.csInf_mem hne0 hbb
  have hnₑmem : nₑ ∈ dominantIndices (IsDiscreteValuationRing.addVal W) e e ab := Int.csSup_mem hnee hba
  rw [mem_dominantIndices_iff _ hv0 e _ ab hb] at hn₀mem hnₑmem
  change termOrder (IsDiscreteValuationRing.addVal W) e 0 ab n₀ = gNF e 0 ab at hn₀mem
  change termOrder (IsDiscreteValuationRing.addVal W) e e ab nₑ = gNF e e ab at hnₑmem
  have hg0top : gNF e 0 ab ≠ ⊤ := hfin0.ne
  have hgetop : gNF e e ab ≠ ⊤ := hfine.ne
  have hde' : d < e := by omega

  have hdom0 : termOrder (IsDiscreteValuationRing.addVal W) e 0 ab n₀ + d <
      termOrder (IsDiscreteValuationRing.addVal W) e 0 ab (n₀ + 1) + ((e - 0 : ℕ) : ℕ∞) := by
    rw [hn₀mem, Nat.sub_zero]
    calc gNF e 0 ab + (d : ℕ∞) < gNF e 0 ab + (e : ℕ∞) := enat_add_natCast_lt_add_natCast_right hg0top hde'
      _ ≤ _ := add_le_add (gNF_le e 0 ab _) le_rfl
  obtain ⟨hT0n₀, hLR0⟩ := termOrder_nfY_of_lt_right ϖ hϖ e 0 (by omega) d ab hb n₀ hdom0

  have hlow0 : ∀ n, gNF e 0 ab + d ≤ termOrder (IsDiscreteValuationRing.addVal W) e 0 (nfY ϖ e d ab) n := by
    intro n
    refine le_trans ?_ (min_le_termOrder_nfY ϖ hϖ e 0 (by omega) d ab hb n)
    rw [Nat.sub_zero]
    exact le_min ((add_le_add (gNF_le e 0 ab _) (by exact_mod_cast hde'.le))) (add_le_add (gNF_le e 0 ab _) le_rfl)
  have hg0Y : gNF e 0 (nfY ϖ e d ab) = gNF e 0 ab + d :=
    le_antisymm ((gNF_le e 0 _ n₀).trans_eq (by rw [hT0n₀, hn₀mem])) (le_iInf hlow0)

  have hnot0 : ∀ n, n < n₀ → gNF e 0 ab + d < termOrder (IsDiscreteValuationRing.addVal W) e 0 (nfY ϖ e d ab) n := by
    intro n hlt
    refine lt_of_lt_of_le ?_ (min_le_termOrder_nfY ϖ hϖ e 0 (by omega) d ab hb n)
    rw [Nat.sub_zero]
    refine lt_min ?_ ?_
    · calc gNF e 0 ab + (d : ℕ∞) < gNF e 0 ab + (e : ℕ∞) := enat_add_natCast_lt_add_natCast_right hg0top hde'
        _ ≤ _ := add_le_add (gNF_le e 0 ab _) le_rfl
    · have hnotmem : n ∉ dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab := notMem_of_lt_csInf hlt hbb
      rw [mem_dominantIndices_iff _ hv0 e 0 ab hb] at hnotmem
      have hgt : gNF e 0 ab < termOrder (IsDiscreteValuationRing.addVal W) e 0 ab n :=
        lt_of_le_of_ne (gNF_le e 0 ab n) (Ne.symm hnotmem)
      exact enat_add_natCast_lt_add_natCast_left hgt d
  have hsInf : sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 (nfY ϖ e d ab)) = n₀ := by
    refine IsLeast.csInf_eq ⟨?_, fun m hm => ?_⟩
    · rw [mem_dominantIndices_iff _ hv0 e 0 _ hbY]
      change _ = gNF e 0 (nfY ϖ e d ab)
      rw [hg0Y, hT0n₀, hn₀mem]
    · rw [mem_dominantIndices_iff _ hv0 e 0 _ hbY] at hm
      change _ = gNF e 0 (nfY ϖ e d ab) at hm
      by_contra hlt
      push Not at hlt
      have := hnot0 m hlt
      rw [hm, hg0Y] at this
      exact lt_irrefl _ this

  have hdome : termOrder (IsDiscreteValuationRing.addVal W) e e ab (nₑ - 1 + 1) + ((e - e : ℕ) : ℕ∞) <
      termOrder (IsDiscreteValuationRing.addVal W) e e ab (nₑ - 1) + d := by
    rw [sub_add_cancel, Nat.sub_self, Nat.cast_zero, add_zero, hnₑmem]
    calc gNF e e ab < gNF e e ab + (d : ℕ∞) := by
          have h' := enat_add_natCast_lt_add_natCast_right hgetop (show 0 < d by omega)
          rwa [Nat.cast_zero, add_zero] at h'
      _ ≤ _ := add_le_add (gNF_le e e ab _) le_rfl
  obtain ⟨hTenₑ, hLRe⟩ := termOrder_nfY_of_lt_left ϖ hϖ e e le_rfl d ab hb (nₑ - 1) hdome
  rw [sub_add_cancel] at hTenₑ hLRe
  rw [Nat.sub_self, Nat.cast_zero, add_zero] at hTenₑ
  have hlowe : ∀ n, gNF e e ab ≤ termOrder (IsDiscreteValuationRing.addVal W) e e (nfY ϖ e d ab) n := by
    intro n
    refine le_trans ?_ (min_le_termOrder_nfY ϖ hϖ e e le_rfl d ab hb n)
    rw [Nat.sub_self, Nat.cast_zero, add_zero]
    exact le_min (gNF_le e e ab _) ((gNF_le e e ab _).trans le_self_add)
  have hgeY : gNF e e (nfY ϖ e d ab) = gNF e e ab :=
    le_antisymm ((gNF_le e e _ (nₑ - 1)).trans_eq (by rw [hTenₑ, hnₑmem])) (le_iInf hlowe)
  have hnote : ∀ n, nₑ - 1 < n → gNF e e ab < termOrder (IsDiscreteValuationRing.addVal W) e e (nfY ϖ e d ab) n := by
    intro n hlt
    refine lt_of_lt_of_le ?_ (min_le_termOrder_nfY ϖ hϖ e e le_rfl d ab hb n)
    rw [Nat.sub_self, Nat.cast_zero, add_zero]
    refine lt_min ?_ ?_
    · have hnotmem : n + 1 ∉ dominantIndices (IsDiscreteValuationRing.addVal W) e e ab :=
        notMem_of_csSup_lt (by omega) hba
      rw [mem_dominantIndices_iff _ hv0 e e ab hb] at hnotmem
      exact lt_of_le_of_ne (gNF_le e e ab _) (Ne.symm hnotmem)
    · calc gNF e e ab < gNF e e ab + (d : ℕ∞) := by
            have h' := enat_add_natCast_lt_add_natCast_right hgetop (show 0 < d by omega)
            rwa [Nat.cast_zero, add_zero] at h'
        _ ≤ _ := add_le_add (gNF_le e e ab _) le_rfl
  have hsSup : sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e (nfY ϖ e d ab)) = nₑ - 1 := by
    refine IsGreatest.csSup_eq ⟨?_, fun m hm => ?_⟩
    · rw [mem_dominantIndices_iff _ hv0 e e _ hbY]
      change _ = gNF e e (nfY ϖ e d ab)
      rw [hgeY, hTenₑ, hnₑmem]
    · rw [mem_dominantIndices_iff _ hv0 e e _ hbY] at hm
      change _ = gNF e e (nfY ϖ e d ab) at hm
      by_contra hlt
      push Not at hlt
      have := hnote m hlt
      rw [hm, hgeY] at this
      exact lt_irrefl _ this
  exact ⟨hsInf, hsSup, hLR0, hLRe, hg0Y, hgeY⟩

end BAuxEnds
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

section BDescent

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

theorem endRatioIdentity_of_mul_V_sub_const_pow (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (d : ℕ) (hd1 : 1 ≤ d) (hde : d + 1 ≤ e)
    (h : EndRatioIdentity ϖ e (x * (V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d))) (nfY ϖ e d ab)) :
    EndRatioIdentity ϖ e x ab := by
  have hv0 : IsDiscreteValuationRing.addVal W 0 = ⊤ := IsDiscreteValuationRing.addVal_zero
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := by rwa [habx]
  obtain ⟨hsInf, hsSup, hLR0, hLRe, -, -⟩ := nfY_end_data ϖ hϖ e he ab hb hx' d hd1 hde
  have hle : sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) ≤
      sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) :=
    sSup_dominantIndices_le_sInf _ hv0 e he ab hb (fun s => gNF_lt_top e s (ϖ ^ e) ab hb hx')
  unfold EndRatioIdentity at h ⊢
  rw [hsInf, hsSup, hLR0, hLRe, horizResProd_mul ϖ hϖ e he x _ hx (V_sub_const_pow_ne_zero ϖ hϖ e he d),
    horizResProd_V_sub_const_pow ϖ hϖ e he d hd1 hde, mul_one,
    show sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
        (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab) - 1) =
      (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)) + ((1 : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_add_nat (by omega), pow_succ] at h
  rw [h]
  ring

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in

theorem exists_nfC_eq_of_forall_dvd (ϖ : W) (ab : PowerSeries W × PowerSeries W)
    (ha : ∀ i, ϖ ∣ PowerSeries.coeff i ab.1) (hb' : ∀ j, ϖ ∣ PowerSeries.coeff j ab.2) :
    ∃ ab' : PowerSeries W × PowerSeries W, nfC ϖ ab' = ab := by
  choose a' ha' using ha
  choose b' hb'' using hb'
  refine ⟨(PowerSeries.mk a', PowerSeries.mk b'), ?_⟩
  rw [nfC]
  ext i
  · simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]; exact (ha' i).symm
  · simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]; exact (hb'' i).symm

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in

theorem exists_nfU_eq_of_dvd (π : W) (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (ha0 : π ∣ PowerSeries.constantCoeff ab.1) (hbj : ∀ j, π ∣ PowerSeries.coeff (j + 1) ab.2) :
    ∃ ab' : PowerSeries W × PowerSeries W, PowerSeries.constantCoeff ab'.2 = 0 ∧ nfU π ab' = ab := by
  obtain ⟨c0, hc0⟩ := ha0
  choose b' hb'' using hbj
  refine ⟨(PowerSeries.mk fun i => PowerSeries.coeff (i + 1) ab.1,
    PowerSeries.mk fun j => Nat.casesOn j 0 (fun j => Nat.casesOn j c0 (fun j => b' j))), ?_, ?_⟩
  · simp
  · rw [nfU]
    ext i
    · cases i with
      | zero => simp [hc0]
      | succ i => simp
    · cases i with
      | zero => simp [hb]
      | succ j =>
        rw [show PowerSeries.C π * PowerSeries.X * (PowerSeries.mk fun i => PowerSeries.coeff (i + 2)
            (PowerSeries.mk fun j => Nat.casesOn j 0 (fun j => Nat.casesOn j c0 (fun j => b' j)))) =
          PowerSeries.C π * (PowerSeries.X * (PowerSeries.mk fun i => b' i)) by
            rw [mul_assoc]; congr 2; ext i; simp]
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
        exact (hb'' j).symm

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in

theorem exists_nfV_eq_of_dvd (π : W) (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hai : ∀ i, π ∣ PowerSeries.coeff i ab.1) :
    ∃ ab' : PowerSeries W × PowerSeries W, PowerSeries.constantCoeff ab'.2 = 0 ∧ nfV π ab' = ab := by
  choose a' ha' using hai
  refine ⟨(PowerSeries.mk fun i => Nat.casesOn i (PowerSeries.coeff 1 ab.2) (fun i => a' i),
    PowerSeries.mk fun j => Nat.casesOn j 0 (fun j => PowerSeries.coeff (j + 2) ab.2)), ?_, ?_⟩
  · simp
  · rw [nfV]
    ext i
    · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
      simp only [PowerSeries.coeff_mk]
      exact (ha' i).symm
    · cases i with
      | zero => simp [hb]
      | succ j =>
        rw [PowerSeries.coeff_succ_X_mul, map_add, PowerSeries.coeff_C, PowerSeries.coeff_mk]
        cases j with
        | zero => simp
        | succ j => simp

omit [IsAdicComplete (maximalIdeal W) W] in

theorem good_of_gNF_eq_zero (e : ℕ) (he : 1 ≤ e) (ab : PowerSeries W × PowerSeries W)
    (h0 : gNF e 0 ab = 0) (he0 : gNF e e ab = 0) :
    (∃ i, IsUnit (PowerSeries.coeff i ab.1)) ∧
      (IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2)) := by
  have hunit : ∀ c : W, IsDiscreteValuationRing.addVal W c = 0 → IsUnit c := fun c hc =>
    (IsDiscreteValuationRing.addVal_eq_zero_iff).mp hc
  constructor
  · obtain ⟨n, hn⟩ := ciInf_mem (fun n : ℤ => termOrder (IsDiscreteValuationRing.addVal W) e 0 ab n)
    change termOrder (IsDiscreteValuationRing.addVal W) e 0 ab n = gNF e 0 ab at hn
    rw [h0] at hn
    cases n with
    | ofNat i =>
      rw [Int.ofNat_eq_natCast, termOrder_natCast, mul_zero, Nat.cast_zero, add_zero] at hn
      exact ⟨i, hunit _ hn⟩
    | negSucc j =>
      exfalso
      rw [termOrder_negSucc, Nat.sub_zero, add_eq_zero] at hn
      have := hn.2
      have h1 : (j + 1) * e ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
      exact h1 (by exact_mod_cast this)
  · obtain ⟨n, hn⟩ := ciInf_mem (fun n : ℤ => termOrder (IsDiscreteValuationRing.addVal W) e e ab n)
    change termOrder (IsDiscreteValuationRing.addVal W) e e ab n = gNF e e ab at hn
    rw [he0] at hn
    cases n with
    | ofNat i =>
      rw [Int.ofNat_eq_natCast, termOrder_natCast, add_eq_zero] at hn
      cases i with
      | zero => left; rw [← PowerSeries.coeff_zero_eq_constantCoeff]; exact hunit _ hn.1
      | succ i =>
        exfalso
        have h1 : (i + 1) * e ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
        exact h1 (by exact_mod_cast hn.2)
    | negSucc j =>
      rw [termOrder_negSucc, Nat.sub_self, mul_zero, Nat.cast_zero, add_zero] at hn
      exact Or.inr ⟨j + 1, by omega, hunit _ hn⟩

omit [IsAdicComplete (maximalIdeal W) W] in

theorem dvd_coeff_of_le_gNF_zero (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (ab : PowerSeries W × PowerSeries W)
    (k : ℕ) (h : (k : ℕ∞) ≤ gNF e 0 ab) (i : ℕ) : ϖ ^ k ∣ PowerSeries.coeff i ab.1 := by
  have h1 := h.trans (gNF_le e 0 ab (i : ℤ))
  rw [termOrder_natCast, mul_zero, Nat.cast_zero, add_zero] at h1
  rwa [← IsDiscreteValuationRing.addVal_le_iff_dvd, BaddVal_uniformizer_pow ϖ hϖ k]

omit [IsAdicComplete (maximalIdeal W) W] in
theorem dvd_coeff_of_le_gNF_e (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (ab : PowerSeries W × PowerSeries W)
    (k : ℕ) (h : (k : ℕ∞) ≤ gNF e e ab) :
    ϖ ^ k ∣ PowerSeries.constantCoeff ab.1 ∧ ∀ j, ϖ ^ k ∣ PowerSeries.coeff (j + 1) ab.2 := by
  constructor
  · have h1 := h.trans (gNF_le e e ab ((0 : ℕ) : ℤ))
    rw [termOrder_natCast, zero_mul, Nat.cast_zero, add_zero, PowerSeries.coeff_zero_eq_constantCoeff] at h1
    rwa [← IsDiscreteValuationRing.addVal_le_iff_dvd, BaddVal_uniformizer_pow ϖ hϖ k]
  · intro j
    have h1 := h.trans (gNF_le e e ab (Int.negSucc j))
    rw [termOrder_negSucc, Nat.sub_self, mul_zero, Nat.cast_zero, add_zero] at h1
    rwa [← IsDiscreteValuationRing.addVal_le_iff_dvd, BaddVal_uniformizer_pow ϖ hϖ k]

theorem endRatioIdentity_of_dvd_sub (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (hgood : ∀ (x : UVCrossingModel W (ϖ ^ e)), x ≠ 0 → ∀ ab : PowerSeries W × PowerSeries W,
      PowerSeries.constantCoeff ab.2 = 0 → mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x →
      (∃ i, IsUnit (PowerSeries.coeff i ab.1)) →
      (IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2)) →
      EndRatioIdentity ϖ e x ab)
    (N : ℕ) :
    ∀ (x : UVCrossingModel W (ϖ ^ e)), x ≠ 0 → ∀ ab : PowerSeries W × PowerSeries W,
      PowerSeries.constantCoeff ab.2 = 0 → mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x →
      ∀ g0 ge : ℕ, gNF e 0 ab = g0 → gNF e e ab = ge → g0 + ge ≤ N → (e : ℤ) ∣ (g0 : ℤ) - ge →
      EndRatioIdentity ϖ e x ab := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro x hx ab hb habx g0 ge hg0 hge hN hdvd
  by_cases hzero : g0 = 0 ∧ ge = 0
  · obtain ⟨rfl, rfl⟩ := hzero
    obtain ⟨h1, h2⟩ := good_of_gNF_eq_zero e he ab (by rw [hg0]; rfl) (by rw [hge]; rfl)
    exact hgood x hx ab hb habx h1 h2
  by_cases hboth : 1 ≤ g0 ∧ 1 ≤ ge
  ·
    have ha : ∀ i, ϖ ∣ PowerSeries.coeff i ab.1 := fun i => by
      simpa using dvd_coeff_of_le_gNF_zero ϖ hϖ e ab 1 (by rw [hg0]; exact_mod_cast hboth.1) i
    have hbd : ∀ j, ϖ ∣ PowerSeries.coeff j ab.2 := by
      intro j
      cases j with
      | zero => rw [PowerSeries.coeff_zero_eq_constantCoeff, hb]; exact dvd_zero _
      | succ j => simpa using (dvd_coeff_of_le_gNF_e ϖ hϖ e ab 1 (by rw [hge]; exact_mod_cast hboth.2)).2 j
    obtain ⟨ab', hab'⟩ := exists_nfC_eq_of_forall_dvd ϖ ab ha hbd
    have hb' : PowerSeries.constantCoeff ab'.2 = 0 := by
      have := hb
      rw [← hab', nfC] at this
      simpa [hϖ.ne_zero] using this
    set z := mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) with hz
    have hxz : const (ϖ ^ e) ϖ * z = x := by rw [hz, ← mk_nfC, hab', habx]
    have hz0 : z ≠ 0 := right_ne_zero_of_mul (by rw [hxz]; exact hx)
    have hg0' : gNF e 0 ab' + 1 = g0 := by
      rw [← hg0, ← hab', gNF_nfC, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    have hge' : gNF e e ab' + 1 = ge := by
      rw [← hge, ← hab', gNF_nfC, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    have hfin0' : gNF e 0 ab' ≠ ⊤ := fun h => by rw [h, top_add] at hg0'; exact ENat.top_ne_coe _ hg0'
    have hfine' : gNF e e ab' ≠ ⊤ := fun h => by rw [h, top_add] at hge'; exact ENat.top_ne_coe _ hge'
    obtain ⟨g0', hg0''⟩ := ENat.ne_top_iff_exists.mp hfin0'
    obtain ⟨ge', hge''⟩ := ENat.ne_top_iff_exists.mp hfine'
    rw [← hg0''] at hg0'
    rw [← hge''] at hge'
    have h1 : g0' + 1 = g0 := by exact_mod_cast hg0'
    have h2 : ge' + 1 = ge := by exact_mod_cast hge'
    have hrec := ih (g0' + ge') (by omega) z hz0 ab' hb' rfl g0' ge' hg0''.symm hge''.symm le_rfl
      (by rw [show (g0' : ℤ) - ge' = g0 - ge by omega]; exact hdvd)
    rw [← hxz, ← hab']
    exact endRatioIdentity_const_mul ϖ hϖ e he z hz0 ab' hb' hrec

  push Not at hzero hboth
  by_cases hg0z : g0 = 0
  ·
    subst hg0z
    have hge0 : ge ≠ 0 := hzero rfl
    have hediv : e ∣ ge := by
      have : (e : ℤ) ∣ (ge : ℤ) := by
        have := hdvd; rw [Nat.cast_zero, zero_sub, dvd_neg] at this; exact this
      exact_mod_cast this
    have hege : e ≤ ge := Nat.le_of_dvd (by omega) hediv
    obtain ⟨ha0, hbj⟩ := dvd_coeff_of_le_gNF_e ϖ hϖ e ab e (by rw [hge]; exact_mod_cast hege)
    obtain ⟨ab', hb', hab'⟩ := exists_nfU_eq_of_dvd (ϖ ^ e) ab hb ha0 hbj
    set z := mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) with hz
    have hxz : U (ϖ ^ e) * z = x := by rw [hz, ← mk_nfU _ _ hb', hab', habx]
    have hz0 : z ≠ 0 := right_ne_zero_of_mul (by rw [hxz]; exact hx)
    have hg0' : gNF e 0 ab' = 0 := by
      have := gNF_nfU ϖ hϖ e 0 (by omega) ab'
      rw [hab', hg0, Nat.cast_zero, add_zero] at this
      exact_mod_cast this.symm
    have hge' : gNF e e ab' + e = ge := by rw [← hge, ← hab', gNF_nfU ϖ hϖ e e le_rfl]
    have hfine' : gNF e e ab' ≠ ⊤ := fun h => by rw [h, top_add] at hge'; exact ENat.top_ne_coe _ hge'
    obtain ⟨ge', hge''⟩ := ENat.ne_top_iff_exists.mp hfine'
    rw [← hge''] at hge'
    have h2 : ge' + e = ge := by exact_mod_cast hge'
    have hrec := ih (0 + ge') (by omega) z hz0 ab' hb' rfl 0 ge' (by rw [hg0']; rfl) hge''.symm le_rfl
      (by rw [show ((0 : ℕ) : ℤ) - ge' = (0 - ge) + e by push_cast; omega]; exact dvd_add hdvd (dvd_refl _))
    rw [← hxz, ← hab']
    exact endRatioIdentity_U_mul ϖ hϖ e he z hz0 ab' hb' rfl hrec
  ·
    have hgez : ge = 0 := by
      by_contra hge0
      exact absurd (hboth (by omega)) (by omega)
    subst hgez
    have hediv : e ∣ g0 := by
      have : (e : ℤ) ∣ (g0 : ℤ) := by
        have := hdvd; rw [Nat.cast_zero, sub_zero] at this; exact this
      exact_mod_cast this
    have heg0 : e ≤ g0 := Nat.le_of_dvd (by omega) hediv
    have hai : ∀ i, ϖ ^ e ∣ PowerSeries.coeff i ab.1 :=
      dvd_coeff_of_le_gNF_zero ϖ hϖ e ab e (by rw [hg0]; exact_mod_cast heg0)
    obtain ⟨ab', hb', hab'⟩ := exists_nfV_eq_of_dvd (ϖ ^ e) ab hb hai
    set z := mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) with hz
    have hxz : V (ϖ ^ e) * z = x := by rw [hz, ← mk_nfV _ _ hb', hab', habx]
    have hz0 : z ≠ 0 := right_ne_zero_of_mul (by rw [hxz]; exact hx)
    have hge' : gNF e e ab' = 0 := by
      have := gNF_nfV ϖ hϖ e e le_rfl ab' hb'
      rw [hab', hge, Nat.cast_zero, Nat.sub_self, Nat.cast_zero, add_zero] at this
      exact this.symm
    have hg0' : gNF e 0 ab' + e = g0 := by rw [← hg0, ← hab', gNF_nfV ϖ hϖ e 0 (by omega) ab' hb', Nat.sub_zero]
    have hfin0' : gNF e 0 ab' ≠ ⊤ := fun h => by rw [h, top_add] at hg0'; exact ENat.top_ne_coe _ hg0'
    obtain ⟨g0', hg0''⟩ := ENat.ne_top_iff_exists.mp hfin0'
    rw [← hg0''] at hg0'
    have h2 : g0' + e = g0 := by exact_mod_cast hg0'
    have hrec := ih (g0' + 0) (by omega) z hz0 ab' hb' rfl g0' 0 hg0''.symm (by rw [hge']; rfl) le_rfl
      (by rw [show (g0' : ℤ) - (0 : ℕ) = (g0 - 0) - e by push_cast; omega]; exact dvd_sub hdvd (dvd_refl _))
    rw [← hxz, ← hab']
    exact endRatioIdentity_V_mul ϖ hϖ e he z hz0 ab' hb' rfl hrec

end BDescent
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq.ModularCurve.UVCrossingModel"

theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x) :
    leadingResidue ϖ (nfCoeff ab (sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab))) *
        ∏ᶠ (Q : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
          (_ : Q.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ Q.asIdeal ∧ x ∈ Q.asIdeal),
          residue W (unitPart ϖ (Algebra.norm W (Ideal.Quotient.mk Q.asIdeal (V (ϖ ^ e))))) ^
            (Module.length (Localization.AtPrime Q.asIdeal)
              (LocalizedModule Q.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}))).toNat =
      (-1) ^ (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
          sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)).toNat *
        leadingResidue ϖ (nfCoeff ab (sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab))) := by
  show EndRatioIdentity ϖ e x ab
  have hgood : ∀ (y : UVCrossingModel W (ϖ ^ e)), y ≠ 0 → ∀ ab' : PowerSeries W × PowerSeries W,
      PowerSeries.constantCoeff ab'.2 = 0 → mk (ϖ ^ e) (inU ab'.1 + inV ab'.2) = y →
      (∃ i, IsUnit (PowerSeries.coeff i ab'.1)) →
      (IsUnit (PowerSeries.constantCoeff ab'.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab'.2)) →
      EndRatioIdentity ϖ e y ab' := fun y hy ab' hb' haby h0 hE =>
    leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq_of_isUnit_coeff ϖ hϖ e he y hy ab' hb' haby h0 hE
  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := by rwa [habx]

  obtain ⟨g0, hg0⟩ := ENat.ne_top_iff_exists.mp (gNF_lt_top e 0 (ϖ ^ e) ab hb hx').ne
  obtain ⟨ge, hge⟩ := ENat.ne_top_iff_exists.mp (gNF_lt_top e e (ϖ ^ e) ab hb hx').ne
  by_cases hdvd : (e : ℤ) ∣ (g0 : ℤ) - ge
  · exact endRatioIdentity_of_dvd_sub ϖ hϖ e he hgood (g0 + ge) x hx ab hb habx g0 ge hg0.symm hge.symm le_rfl hdvd

  set r : ℤ := ((ge : ℤ) - g0) % e with hr
  have he0 : (0 : ℤ) < e := by exact_mod_cast (show 0 < e by omega)
  have hr0 : 0 ≤ r := Int.emod_nonneg _ he0.ne'
  have hre : r < e := Int.emod_lt_of_pos _ he0
  have hrne : r ≠ 0 := by
    intro h0
    apply hdvd
    have h1 : (e : ℤ) ∣ (ge : ℤ) - g0 := Int.dvd_of_emod_eq_zero h0
    rw [← dvd_neg, neg_sub] at h1
    exact h1
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = r := ⟨r.toNat, Int.toNat_of_nonneg hr0⟩
  have hd1 : 1 ≤ d := by omega
  have hde : d + 1 ≤ e := by omega
  haveI : IsDomain (UVCrossingModel W (ϖ ^ e)) := (isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ e he).1
  set y := x * (V (ϖ ^ e) - const (ϖ ^ e) (ϖ ^ d)) with hy
  have hy0 : y ≠ 0 := mul_ne_zero hx (V_sub_const_pow_ne_zero ϖ hϖ e he d)
  have hby := constantCoeff_nfY_snd ϖ e d ab hb
  have haby : mk (ϖ ^ e) (inU (nfY ϖ e d ab).1 + inV (nfY ϖ e d ab).2) = y := by rw [mk_nfY _ _ _ _ hb, habx]
  obtain ⟨-, -, -, -, hg0y, hgey⟩ := nfY_end_data ϖ hϖ e he ab hb hx' d hd1 hde
  have hg0y' : gNF e 0 (nfY ϖ e d ab) = ((g0 + d : ℕ) : ℕ∞) := by rw [hg0y, ← hg0, Nat.cast_add]
  have hgey' : gNF e e (nfY ϖ e d ab) = (ge : ℕ∞) := by rw [hgey, ← hge]
  have hdvdy : (e : ℤ) ∣ ((g0 + d : ℕ) : ℤ) - ge := by
    have hdecomp := Int.mul_ediv_add_emod ((ge : ℤ) - g0) e
    rw [← hr] at hdecomp
    refine ⟨-(((ge : ℤ) - g0) / e), ?_⟩
    push_cast
    rw [hd]
    linarith
  have hyid := endRatioIdentity_of_dvd_sub ϖ hϖ e he hgood (g0 + d + ge) y hy0 (nfY ϖ e d ab) hby haby (g0 + d) ge
    hg0y' hgey' le_rfl hdvdy
  exact endRatioIdentity_of_mul_V_sub_const_pow ϖ hϖ e he x hx ab hb habx d hd1 hde hyid

end S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_leadingResidue_nfCoeff_sSup_mul_finprod_residue_unitPart_norm_pow_eq (solution)
