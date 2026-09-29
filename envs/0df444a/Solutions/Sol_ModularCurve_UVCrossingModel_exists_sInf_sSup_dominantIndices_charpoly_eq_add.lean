-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_sInf_sSup_dominantIndices_charpoly_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/94a71b8e-24d5-5d79-9666-2367d502d468

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_mul_and_sSup_dominantIndices_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add

set_option maxHeartbeats 800000
set_option autoImplicit false

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

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

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

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel Finset"

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

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel Finset"

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

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel Finset P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.AnnulusNF P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.AnnulusG1"

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

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel Finset P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.AnnulusNF P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.AnnulusG1"

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

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop sInf_dominantIndices_mul_and_sSup_dominantIndices_mul"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop sInf_dominantIndices_mul_and_sSup_dominantIndices_mul"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

namespace P1Arch

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

def IsPureSlope (r : ℕ) (n : W) (d : ℕ) (f : Polynomial W) : Prop :=
  f.Monic ∧ f.natDegree = d ∧
    (∀ i : ℕ, i ≤ d → ((d - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W n ≤
      (r : ℕ∞) * IsDiscreteValuationRing.addVal W (f.coeff i)) ∧
    ((d : ℕ∞) * IsDiscreteValuationRing.addVal W n = (r : ℕ∞) * IsDiscreteValuationRing.addVal W (f.coeff 0))

end P1Arch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop sInf_dominantIndices_mul_and_sSup_dominantIndices_mul"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop sInf_dominantIndices_mul_and_sSup_dominantIndices_mul"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

namespace P1Arch

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop sInf_dominantIndices_mul_and_sSup_dominantIndices_mul"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

p2m_open "ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel IsLocalRing Polynomial"

namespace ModularCurve
p2m_export "ModularCurve" "UVCrossingModel"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V mk_surjective S D inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices circleIndexDrop sInf_dominantIndices_mul_and_sSup_dominantIndices_mul"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder~gaussOrder_succ_sub_eq_sInf_dominantIndices~gaussOrder_sub_pred_eq_sSup_dominantIndices~dominantIndices_scale ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder~UVCrossingModel.gaussOrder_succ_sub_eq_sInf_dominantIndices~UVCrossingModel.gaussOrder_sub_pred_eq_sSup_dominantIndices~UVCrossingModel.dominantIndices_scale"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add.ModularCurve.UVCrossingModel"

open AnnulusNF in

theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    [Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    [Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})]
    (hΔ : (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) : ℤ) =
      sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)) :
    ∃ n₀ : ℤ, ∀ q : ℕ, 1 ≤ q →
      (∀ p : ℕ, p + 1 ≤ q * e →
        sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p
            (((LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e)))).charpoly : PowerSeries W), 0)) =
          sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) + n₀) ∧
      (∀ p : ℕ, 1 ≤ p → p ≤ q * e →
        sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p
            (((LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e)))).charpoly : PowerSeries W), 0)) =
          sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) p ab) + n₀) := by
  classical
  set χ := (LinearMap.mulLeft W (Ideal.Quotient.mk (Ideal.span {x}) (U (ϖ ^ e)))).charpoly with hχdef
  have hmon : χ.Monic := LinearMap.charpoly_monic _
  have hdeg : χ.natDegree = Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) :=
    LinearMap.charpoly_natDegree _

  obtain ⟨y, hy⟩ : ∃ y, aeval (U (ϖ ^ e)) χ = x * y := by
    have hmem := aeval_charpoly_mulLeft_mk_mem (A := W) (Ideal.span {x}) (U (ϖ ^ e))
    rw [Ideal.mem_span_singleton'] at hmem
    obtain ⟨y, hy⟩ := hmem
    exact ⟨y, by rw [← hy, mul_comm]⟩
  have hxy0 : x * y ≠ 0 := by rw [← hy]; exact aeval_U_ne_zero_of_monic ϖ hϖ e he χ hmon
  have hy0 : y ≠ 0 := by rintro rfl; exact hxy0 (mul_zero x)
  have habxy : mk (ϖ ^ e) (inU ((χ : PowerSeries W), (0 : PowerSeries W)).1 +
      inV ((χ : PowerSeries W), (0 : PowerSeries W)).2) = x * y := by
    rw [← hy]; exact mk_normalForm_polynomial _ χ
  have hb'' : PowerSeries.constantCoeff ((χ : PowerSeries W), (0 : PowerSeries W)).2 = 0 := map_zero _

  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  obtain ⟨aby, hby, haby⟩ := exists_normalForm ϖ e he y
  refine ⟨sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e aby), fun q hq => ?_⟩

  have hE : 1 ≤ q * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hv0 : (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) 0 = ⊤ := vq_zero q hq
  have hv1 : (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) 1 = 0 := by
    simp only [IsDiscreteValuationRing.addVal_one, mul_zero]
  have hA := fun p => sInf_dominantIndices_mul_and_sSup_dominantIndices_mul ϖ hϖ e he q hq x hx ab hb habx y hy0
    aby hby haby _ hb'' habxy p
  have hfin : ∀ s, (⨅ n, termOrder (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) s aby n) < ⊤ :=
    fun s => iInf_termOrder_lt_top (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (vq_eq_top q) (ϖ ^ e) (q * e) s aby hby (haby ▸ hy0)
  have hbd0 := sInf_le_natDegree_and_sSup_nonneg_of_monic (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) hv0 hv1 (q * e) 0 χ hmon
  have hbdE := sInf_le_natDegree_and_sSup_nonneg_of_monic (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) hv0 hv1 (q * e) (q * e) χ hmon
  have hΔq : (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) : ℤ) =
      sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 ab) - sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) ab) := by
    rw [P1Arch.dominantIndices_scaled_zero q e hq ab, P1Arch.dominantIndices_scaled_top q e hq ab]; exact hΔ
  have hA0 := (hA 0).1 (by omega)
  have hAE := (hA (q * e)).2 hE le_rfl

  have hle : sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) 0 aby) ≤ sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) aby) := by
    have h1 := hbd0.1
    have h2 := hbdE.2
    rw [hdeg] at h1
    linarith
  obtain ⟨hI, hS⟩ := sInf_sSup_dominantIndices_eq_of_sInf_le_sSup (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) hv0 (q * e) hE aby hby hfin hle
  have hn₀ : sSup (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * e) (q * e) aby) =
      sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e aby) := by
    rw [P1Arch.dominantIndices_scaled_top q e hq aby]
  refine ⟨fun p hpe => ?_, fun p hp1 hpe => ?_⟩
  · rw [(hA p).1 hpe, hI p hpe, hn₀]
  · rw [(hA p).2 hp1 hpe, hS p hp1 hpe, hn₀]

end S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_sInf_sSup_dominantIndices_charpoly_eq_add (solution)
