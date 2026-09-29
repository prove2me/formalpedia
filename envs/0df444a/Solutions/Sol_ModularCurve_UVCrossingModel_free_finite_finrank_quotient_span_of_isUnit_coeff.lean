-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.free_finite_finrank_quotient_span_of_isUnit_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fbbd17d2-ccfa-5fc6-bf5e-7740391980f1

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Definitions.Def_ModularCurve_UVCrossingChart
import Theorems.Thm_ModularCurve_UVCrossingModel_isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete
import Theorems.Thm_ModularCurve_UVCrossingModel_range_chartHom_eq_fixedSubring
import Theorems.Thm_ModularCurve_UVCrossingModel_exists_mem_fixedSubring_eq_add_mul_U
import Theorems.Thm_ModularCurve_UVCrossingModel_chartHom_C
import Theorems.Thm_ModularCurve_UVCrossingModel_isNoetherianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff

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

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"

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

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel Finset"

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

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel Finset"

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

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel Finset P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.AnnulusNF P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.AnnulusG1"

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

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel Finset P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.AnnulusNF P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.AnnulusG1"

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

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"
open scoped TensorProduct

namespace P1Arch

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"
open scoped TensorProduct

section Toolkit
variable {W : Type u} [CommRing W]
variable {R : Type u} [CommRing R] [Algebra W R]

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

theorem tensor_eq_zero_of_smul_eq_zero {K : Type*} [CommRing K] [Algebra W K] {M : Type*} [AddCommGroup M]
    [Module W M] (w : W) (hw : IsUnit (algebraMap W K w)) (hM : ∀ m : M, w • m = 0) (z : K ⊗[W] M) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul k m =>
    obtain ⟨u, hu⟩ := hw
    have hk : k = w • (k * ↑u⁻¹) := by
      rw [Algebra.smul_def, ← hu, ← mul_assoc, mul_comm (↑u) k, mul_assoc, Units.mul_inv, mul_one]
    rw [hk, TensorProduct.smul_tmul, hM, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

theorem subsingleton_tensor_of_smul_eq_zero {K : Type*} [CommRing K] [Algebra W K] {M : Type*} [AddCommGroup M]
    [Module W M] (w : W) (hw : IsUnit (algebraMap W K w)) (hM : ∀ m : M, w • m = 0) :
    Subsingleton (K ⊗[W] M) :=
  ⟨fun x y => by rw [tensor_eq_zero_of_smul_eq_zero w hw hM x, tensor_eq_zero_of_smul_eq_zero w hw hM y]⟩

theorem smul_quotient_eq_zero_of_algebraMap_mem (w : W) (J : Ideal R) (hJ : algebraMap W R w ∈ J)
    (m : R ⧸ J) : w • m = 0 := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [← Ideal.Quotient.mkₐ_eq_mk W, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
  convert J.mul_mem_right r hJ using 1
  exact Algebra.smul_def w r

theorem finite_tensor_quotient_mul_of_torsion [IsDomain W] (x y : R) (w : W)
    (hw : IsUnit (algebraMap W (FractionRing W) w)) (hy : algebraMap W R w ∈ Ideal.span {y})
    [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {x}))] :
    Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {x * y})) := by
  let f := ((mulQuot x y).restrictScalars W).baseChange (FractionRing W)
  let g := ((projQuot x y).restrictScalars W).baseChange (FractionRing W)
  have hgsurj : Function.Surjective g := by
    change Function.Surjective (((projQuot x y).restrictScalars W).baseChange (FractionRing W))
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (projQuot_surjective x y)
  have hexact : Function.Exact f g := by
    change Function.Exact (((mulQuot x y).restrictScalars W).baseChange (FractionRing W))
      (((projQuot x y).restrictScalars W).baseChange (FractionRing W))
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact (FractionRing W) (exact_mulQuot_projQuot x y) (projQuot_surjective x y)
  haveI : Subsingleton ((FractionRing W) ⊗[W] (R ⧸ Ideal.span {y})) :=
    subsingleton_tensor_of_smul_eq_zero w hw (smul_quotient_eq_zero_of_algebraMap_mem w _ hy)
  exact Module.Finite.of_exact hexact hgsurj

end Toolkit

section Wside
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

local notation "addv" => (IsDiscreteValuationRing.addVal W : W → ℕ∞)

theorem exists_eq_mul_C_pow_of_ne_zero (ϖ : W) (hϖ : Irreducible ϖ) (g : PowerSeries W) (hg : g ≠ 0) :
    ∃ (m : ℕ) (g' : PowerSeries W), (∃ k, IsUnit (PowerSeries.coeff k g')) ∧ g = g' * PowerSeries.C (ϖ ^ m) := by
  classical
  have hex : ∃ m : ℕ, ∃ k, addv (PowerSeries.coeff k g) = m := by
    obtain ⟨k, hk⟩ : ∃ k, PowerSeries.coeff k g ≠ 0 := by
      by_contra h
      push_neg at h
      exact hg (PowerSeries.ext fun k => by simpa using h k)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
      (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp hk)
    exact ⟨m, k, hm.symm⟩
  let m := Nat.find hex
  obtain ⟨k₀, hk₀⟩ : ∃ k, addv (PowerSeries.coeff k g) = m := Nat.find_spec hex
  have hmin : ∀ k, (m : ℕ∞) ≤ addv (PowerSeries.coeff k g) := by
    intro k
    by_cases h0 : PowerSeries.coeff k g = 0
    · rw [h0, (IsDiscreteValuationRing.addVal W).map_zero]; exact le_top
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (mt IsDiscreteValuationRing.addVal_eq_top_iff.mp h0)
      rw [← hn]
      exact_mod_cast Nat.find_min' hex ⟨k, hn.symm⟩
  have hdvd : ∀ k, ϖ ^ m ∣ PowerSeries.coeff k g := by
    intro k
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simpa using hmin k
  choose c hc using hdvd
  refine ⟨m, PowerSeries.mk c, ⟨k₀, ?_⟩, ?_⟩
  · rw [PowerSeries.coeff_mk, ← IsDiscreteValuationRing.addVal_eq_zero_iff]
    have h1 : addv (PowerSeries.coeff k₀ g) = (m : ℕ∞) + addv (c k₀) := by
      rw [hc k₀, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
        IsDiscreteValuationRing.addVal_uniformizer hϖ]
      simp
    rw [hk₀] at h1
    have h2 : (m : ℕ∞) + addv (c k₀) = (m : ℕ∞) + 0 := by rw [add_zero]; exact h1.symm
    exact (WithTop.add_left_inj (ENat.coe_ne_top m)).mp h2
  · ext k
    rw [PowerSeries.coeff_mul_C, PowerSeries.coeff_mk, mul_comm]
    exact hc k

variable [IsAdicComplete (maximalIdeal W) W]

theorem moduleFinite_quotient_of_isUnit_coeff (g : PowerSeries W) (hg : ∃ k, IsUnit (PowerSeries.coeff k g)) :
    Module.Finite W (PowerSeries W ⧸ Ideal.span {g}) := by
  classical
  have hres : PowerSeries.map (IsLocalRing.residue W) g ≠ 0 := by
    obtain ⟨k, hk⟩ := hg
    intro h
    have := congrArg (PowerSeries.coeff k) h
    rw [PowerSeries.coeff_map, map_zero] at this
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hk this
  set d : ℕ := (PowerSeries.map (IsLocalRing.residue W) g).order.toNat with hd

  let φ : Polynomial.degreeLT W d →ₗ[W] (PowerSeries W ⧸ Ideal.span {g}) :=
    ((Ideal.Quotient.mkₐ W (Ideal.span {g})).toLinearMap.comp
      (Polynomial.coeToPowerSeries.algHom W).toLinearMap).comp (Polynomial.degreeLT W d).subtype
  haveI : Module.Finite W (Polynomial.degreeLT W d) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv W d).symm
  refine Module.Finite.of_surjective φ ?_
  intro q
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨q', r, hdiv⟩ := PowerSeries.exists_isWeierstrassDivision f (g := g) hres
  refine ⟨⟨r, Polynomial.mem_degreeLT.mpr hdiv.degree_lt⟩, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {g}) ((r : PowerSeries W)) = Ideal.Quotient.mk _ f
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, hdiv.eq_mul_add]
  exact Ideal.mem_span_singleton'.mpr ⟨-q', by ring⟩

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in
theorem algebraMap_powerSeries_apply (w : W) : algebraMap W (PowerSeries W) w = PowerSeries.C w := by
  rw [PowerSeries.algebraMap_apply]
  rfl

theorem finite_tensor_powerSeries_quotient (ϖ : W) (hϖ : Irreducible ϖ) (g : PowerSeries W) (hg : g ≠ 0) :
    Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (PowerSeries W ⧸ Ideal.span {g})) := by
  obtain ⟨m, g', hunit, rfl⟩ := exists_eq_mul_C_pow_of_ne_zero ϖ hϖ g hg
  haveI := moduleFinite_quotient_of_isUnit_coeff g' hunit
  haveI : Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (PowerSeries W ⧸ Ideal.span {g'})) :=
    inferInstance
  refine finite_tensor_quotient_mul_of_torsion g' (PowerSeries.C (ϖ ^ m)) (ϖ ^ m) ?_ ?_
  · exact isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).mpr (pow_ne_zero m hϖ.ne_zero))
  · rw [algebraMap_powerSeries_apply]
    exact Ideal.subset_span rfl

end Wside

end P1Arch

namespace P1Arch

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"
open scoped TensorProduct

section Rside
variable {W : Type u} [CommRing W]

theorem algebraMap_eq_const (π w : W) : algebraMap W (UVCrossingModel W π) w = const π w := by
  change Ideal.Quotient.mk _ (algebraMap W (MvPowerSeries (Fin 2) W) w) = _
  rw [MvPowerSeries.algebraMap_apply]
  rfl

theorem isUnit_of_isUnit_const_self (π : W) (h : IsUnit (const π π)) : IsUnit π := by
  obtain ⟨y, hy⟩ := h.exists_right_inv
  obtain ⟨G, rfl⟩ := mk_surjective π y
  rw [const, ← map_mul, ← (mk π).map_one] at hy
  change Ideal.Quotient.mk (uvCrossingIdeal W π) _ = Ideal.Quotient.mk (uvCrossingIdeal W π) _ at hy
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hy
  obtain ⟨H, hH⟩ := Ideal.mem_span_singleton'.mp hy
  have h0 := congrArg MvPowerSeries.constantCoeff hH
  simp only [map_mul, map_sub, map_one, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C] at h0
  exact isUnit_iff_exists_inv.mpr ⟨MvPowerSeries.constantCoeff G + MvPowerSeries.constantCoeff H,
    by linear_combination (-1 : W) * h0⟩

theorem crossingSwap_crossingSwap (π : W) (x : UVCrossingModel W π) :
    crossingSwap π (crossingSwap π x) = x := by
  obtain ⟨F, rfl⟩ := mk_surjective π x
  rw [crossingSwap_mk, crossingSwap_mk]
  congr 1
  change (MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1))
      ((MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1)) F) = F
  conv_lhs => rw [← Equiv.symm_swap, ← MvPowerSeries.renameEquiv_symm]
  exact (MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1)).symm_apply_apply F

theorem isPrecomplete_span_pow (ϖ : W) (e : ℕ) (he : 1 ≤ e) [IsPrecomplete (Ideal.span {ϖ}) W] :
    IsPrecomplete (Ideal.span {ϖ ^ e}) W := by
  have key : ∀ k, (Ideal.span {ϖ ^ e}) ^ k = (Ideal.span {ϖ}) ^ (e * k) := by
    intro k
    rw [Ideal.span_singleton_pow, ← pow_mul, ← Ideal.span_singleton_pow]
  constructor
  intro f hf
  have hf' : ∀ {m n}, m ≤ n → f m ≡ f n [SMOD (Ideal.span {ϖ}) ^ m • (⊤ : Submodule W W)] := by
    intro m n hmn
    refine SModEq.mono ?_ (hf hmn)
    rw [key]
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by nlinarith))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' f hf'
  refine ⟨L, fun n => ?_⟩
  have h1 : f n ≡ f (e * n) [SMOD (Ideal.span {ϖ ^ e}) ^ n • (⊤ : Submodule W W)] := hf (by nlinarith)
  have h2 : f (e * n) ≡ L [SMOD (Ideal.span {ϖ ^ e}) ^ n • (⊤ : Submodule W W)] := by
    rw [key]; exact hL (e * n)
  exact h1.trans h2

end Rside

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

local notation "addv" => (IsDiscreteValuationRing.addVal W : W → ℕ∞)

variable [IsAdicComplete (maximalIdeal W) W]

theorem finite_tensor_quotient (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0) :
    Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) := by
  classical
  obtain ⟨hdom, hloc, -⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ e he
  haveI := hdom
  haveI := hloc
  haveI : IsNoetherianRing (UVCrossingModel W (ϖ ^ e)) := UVCrossingModel.isNoetherianRing (ϖ ^ e)
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  haveI : IsPrecomplete (Ideal.span {ϖ ^ e}) W := isPrecomplete_span_pow ϖ e he

  have hreg : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (ϖ ^ e)) ∈
      nonZeroDivisors (MvPowerSeries (Fin 2) W) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    have h0 := congrArg MvPowerSeries.constantCoeff h
    simp only [map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, map_zero,
      mul_zero, zero_sub, neg_eq_zero] at h0
    exact pow_ne_zero e hϖ.ne_zero h0
  have hsep : ∀ y : UVCrossingModel W (ϖ ^ e), (∀ B : ℕ, y ∈ Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ^ B) → y = 0 := by
    intro y hy
    have hne : Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ≠ ⊤ := by
      apply Ideal.span_singleton_ne_top
      intro hu
      exact hϖ.1 ((isUnit_pow_iff (by omega)).mp (isUnit_of_isUnit_const_self _ hu))
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
    have hmem : y ∈ (⨅ i : ℕ, Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ^ i) := Ideal.mem_iInf.mpr hy
    rw [hbot] at hmem
    exact Ideal.mem_bot.mp hmem
  have hrange := ModularCurve.UVCrossingModel.range_chartHom_eq_fixedSubring (π := ϖ ^ e) hreg hsep

  have hn_fixed : x * crossingSwap (ϖ ^ e) x ∈ fixedSubring (ϖ ^ e) := by
    rw [mem_fixedSubring_iff, map_mul, crossingSwap_crossingSwap, mul_comm]
  have hn_range : x * crossingSwap (ϖ ^ e) x ∈ (chartHom (ϖ ^ e)).range := hrange ▸ hn_fixed
  obtain ⟨n, hn⟩ := RingHom.mem_range.mp hn_range
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn
    exact mul_ne_zero hx ((RingEquiv.map_ne_zero_iff (crossingSwap (ϖ ^ e))).mpr hx) hn.symm
  haveI hfinQ := finite_tensor_powerSeries_quotient ϖ hϖ n hn0

  let χ : PowerSeries W →ₐ[W] UVCrossingModel W (ϖ ^ e) := AlgHom.mk (chartHom (ϖ ^ e)) (fun w => by
    change chartHom (ϖ ^ e) (algebraMap W (PowerSeries W) w) = algebraMap W _ w
    rw [algebraMap_powerSeries_apply, ModularCurve.UVCrossingModel.chartHom_C, algebraMap_eq_const])
  let ψ : UVCrossingModel W (ϖ ^ e) → (PowerSeries W →ₗ[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) :=
    fun r₀ => (Ideal.Quotient.mkₐ W (Ideal.span {x})).toLinearMap ∘ₗ (LinearMap.mulRight W r₀) ∘ₗ χ.toLinearMap
  have hψ : ∀ r₀ f, ψ r₀ f = Ideal.Quotient.mk (Ideal.span {x}) (chartHom (ϖ ^ e) f * r₀) := fun _ _ => rfl
  have hker : ∀ r₀, (Ideal.span {n}).restrictScalars W ≤ LinearMap.ker (ψ r₀) := by
    intro r₀ z hz
    rw [Submodule.restrictScalars_mem] at hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [LinearMap.mem_ker, hψ, (chartHom (ϖ ^ e)).map_mul, hn, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨chartHom (ϖ ^ e) c * crossingSwap (ϖ ^ e) x * r₀, by ring⟩
  let P : Submodule W (PowerSeries W) := (Ideal.span {n}).restrictScalars W
  let Φ : ((PowerSeries W ⧸ P) × (PowerSeries W ⧸ P)) →ₗ[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) :=
    (P.liftQ (ψ 1) (hker 1)).coprod (P.liftQ (ψ (U (ϖ ^ e))) (hker _))
  have hΦ : Function.Surjective Φ := by
    intro q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, ha, hb, rfl⟩ := ModularCurve.UVCrossingModel.exists_mem_fixedSubring_eq_add_mul_U (ϖ ^ e) r
    rw [← hrange] at ha hb
    obtain ⟨f, rfl⟩ := RingHom.mem_range.mp ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hb
    refine ⟨(Submodule.Quotient.mk f, Submodule.Quotient.mk g), ?_⟩
    rw [LinearMap.coprod_apply, Submodule.liftQ_apply, Submodule.liftQ_apply, hψ, hψ, ← map_add, mul_one]

  let eQ : (PowerSeries W ⧸ P) ≃ₗ[W] (PowerSeries W ⧸ Ideal.span {n}) :=
    Submodule.Quotient.restrictScalarsEquiv W (Ideal.span {n})
  haveI : Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (PowerSeries W ⧸ P)) :=
    Module.Finite.equiv (LinearEquiv.baseChange W (FractionRing W) _ _ eQ).symm
  haveI : Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] ((PowerSeries W ⧸ P) × (PowerSeries W ⧸ P))) :=
    Module.Finite.equiv (TensorProduct.prodRight W (FractionRing W) (FractionRing W) (PowerSeries W ⧸ P)
      (PowerSeries W ⧸ P)).symm
  refine Module.Finite.of_surjective (Φ.baseChange (FractionRing W)) ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective _ hΦ

end P1Arch

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete UVCrossingModel.range_chartHom_eq_fixedSubring UVCrossingModel.exists_mem_fixedSubring_eq_add_mul_U UVCrossingModel.chartHom_C UVCrossingModel.isNoetherianRing"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const constHom constHom_apply mk_surjective crossingSwap crossingSwap_mk S fixedSubring mem_fixedSubring_iff inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices chartHom isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete range_chartHom_eq_fixedSubring exists_mem_fixedSubring_eq_add_mul_U chartHom_C isNoetherianRing"
p2m_open "ModularCurve.UVCrossingModel~U_mul_V ModularCurve"

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

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"

namespace P1Branch

variable {W : Type u} [CommRing W]

noncomputable def keepVar (s : Fin 2) : Fin 2 → PowerSeries W :=
  fun i => if i = s then PowerSeries.X else 0

theorem hasSubst_keepVar (s : Fin 2) : MvPowerSeries.HasSubst (keepVar (W := W) s) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  by_cases h : i = s
  · simp only [keepVar, if_pos h]; exact PowerSeries.constantCoeff_X
  · simp [keepVar, h]

noncomputable def keepHom (s : Fin 2) : MvPowerSeries (Fin 2) W →ₐ[W] PowerSeries W :=
  MvPowerSeries.substAlgHom (hasSubst_keepVar s)

theorem keepHom_X_self (s : Fin 2) : keepHom (W := W) s (MvPowerSeries.X s) = PowerSeries.X := by
  unfold keepHom
  rw [MvPowerSeries.substAlgHom_X]
  simp [keepVar]

theorem keepHom_X_other (s s' : Fin 2) (h : s' ≠ s) : keepHom (W := W) s (MvPowerSeries.X s') = 0 := by
  unfold keepHom
  rw [MvPowerSeries.substAlgHom_X]
  simp [keepVar, h]

theorem keepHom_C (s : Fin 2) (w : W) : keepHom (W := W) s (MvPowerSeries.C w) = PowerSeries.C w := by
  unfold keepHom
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C]
  rfl

variable [IsLocalRing W]

noncomputable def branchRed₀ (s : Fin 2) : MvPowerSeries (Fin 2) W →+* PowerSeries (ResidueField W) :=
  (PowerSeries.map (residue W)).comp (keepHom s).toRingHom

theorem branchRed₀_X_self (s : Fin 2) : branchRed₀ (W := W) s (MvPowerSeries.X s) = PowerSeries.X := by
  simp [branchRed₀, keepHom_X_self]

theorem branchRed₀_X_other (s s' : Fin 2) (h : s' ≠ s) : branchRed₀ (W := W) s (MvPowerSeries.X s') = 0 := by
  simp [branchRed₀, keepHom_X_other s s' h]

theorem branchRed₀_C (s : Fin 2) (w : W) : branchRed₀ (W := W) s (MvPowerSeries.C w) = PowerSeries.C (residue W w) := by
  simp [branchRed₀, keepHom_C]

theorem branchRed₀_crossing (s : Fin 2) (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) :
    branchRed₀ (W := W) s ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (ϖ ^ e)) = 0 := by
  have hres : residue W (ϖ ^ e) = 0 := by
    rw [map_pow, (residue_eq_zero_iff _).mpr hϖ, zero_pow (by omega)]
  rw [map_sub, map_mul, branchRed₀_C, hres, map_zero, sub_zero]
  obtain rfl | rfl : s = 0 ∨ s = 1 := by fin_cases s <;> simp
  · rw [branchRed₀_X_other (W := W) 0 1 (by decide), mul_zero]
  · rw [branchRed₀_X_other (W := W) 1 0 (by decide), zero_mul]

noncomputable def branchRed (s : Fin 2) (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) :
    UVCrossingModel W (ϖ ^ e) →+* PowerSeries (ResidueField W) :=
  Ideal.Quotient.lift (uvCrossingIdeal W (ϖ ^ e)) (branchRed₀ s)
    (fun f hf => by
      rw [uvCrossingIdeal, Ideal.mem_span_singleton] at hf
      obtain ⟨g, rfl⟩ := hf
      rw [map_mul, branchRed₀_crossing s ϖ hϖ e he, zero_mul])

theorem branchRed_mk (s : Fin 2) (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) (F : MvPowerSeries (Fin 2) W) :
    branchRed s ϖ hϖ e he (mk (ϖ ^ e) F) = branchRed₀ s F := rfl

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"

namespace P1Branch

variable {W : Type u} [CommRing W]

theorem coeff_keepHom (s : Fin 2) (F : MvPowerSeries (Fin 2) W) (n : ℕ) :
    PowerSeries.coeff n (keepHom s F) = MvPowerSeries.coeff (Finsupp.single s n) F := by
  classical
  unfold keepHom
  rw [MvPowerSeries.substAlgHom_apply, PowerSeries.coeff, MvPowerSeries.coeff_subst (hasSubst_keepVar s)]
  rw [finsum_eq_single _ (Finsupp.single s n)]
  have hk : keepVar (W := W) s s = PowerSeries.X := by simp [keepVar]
  ·
    rw [Finsupp.prod_single_index (by simp), hk, smul_eq_mul]
    rw [show (MvPowerSeries.coeff (Finsupp.single () n)) ((PowerSeries.X : PowerSeries W) ^ n) =
      PowerSeries.coeff n ((PowerSeries.X : PowerSeries W) ^ n) from rfl, PowerSeries.coeff_X_pow_self, mul_one]
  · intro d hd

    by_cases hoff : d (if s = 0 then 1 else 0) = 0
    · have hds : d = Finsupp.single s (d s) := by
        ext i
        obtain rfl | rfl : s = 0 ∨ s = 1 := by fin_cases s <;> simp
        all_goals obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
        all_goals simp_all
      have hne : d s ≠ n := fun h => hd (by rw [hds, h])
      have hk : keepVar (W := W) s s = PowerSeries.X := by simp [keepVar]
      rw [hds, Finsupp.prod_single_index (by simp), hk, smul_eq_mul]
      rw [show (MvPowerSeries.coeff (Finsupp.single () n)) ((PowerSeries.X : PowerSeries W) ^ d s) =
        PowerSeries.coeff n ((PowerSeries.X : PowerSeries W) ^ d s) from rfl, PowerSeries.coeff_X_pow,
        if_neg (Ne.symm hne), mul_zero]
    ·
      set t : Fin 2 := if s = 0 then 1 else 0 with ht
      have hts : t ≠ s := by obtain rfl | rfl : s = 0 ∨ s = 1 := by fin_cases s <;> simp
                             all_goals simp [ht]
      have hmem : t ∈ d.support := Finsupp.mem_support_iff.mpr hoff
      have hzero : (d.prod fun i k => keepVar (W := W) s i ^ k) = 0 := by
        rw [Finsupp.prod, Finset.prod_eq_zero hmem]
        simp [keepVar, hts, zero_pow hoff]
      rw [hzero, map_zero, smul_zero]

theorem keepHom_zero_inU_add_inV (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    keepHom 0 (inU a + inV b) = a := by
  ext n
  rw [coeff_keepHom, map_add, coeff_inU, coeff_inV]
  simp only [Finsupp.single_apply]
  by_cases hn : n = 0
  · subst hn; simp [hb]
  · simp [hn]

theorem keepHom_one_inU_add_inV (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    keepHom 1 (inU a + inV b) = PowerSeries.C (PowerSeries.constantCoeff a) + b := by
  ext n
  rw [coeff_keepHom, map_add, coeff_inU, coeff_inV, map_add]
  simp only [Finsupp.single_apply]
  by_cases hn : n = 0
  · subst hn; simp [hb]
  · simp [hn, PowerSeries.coeff_C]

variable [IsLocalRing W]

theorem branchRed_zero_normalForm (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e)
    (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    branchRed 0 ϖ hϖ e he (mk (ϖ ^ e) (inU a + inV b)) = PowerSeries.map (residue W) a := by
  rw [branchRed_mk, branchRed₀, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    keepHom_zero_inU_add_inV a b hb]

theorem branchRed_one_normalForm (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e)
    (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    branchRed 1 ϖ hϖ e he (mk (ϖ ^ e) (inU a + inV b)) =
      PowerSeries.C (residue W (PowerSeries.constantCoeff a)) + PowerSeries.map (residue W) b := by
  rw [branchRed_mk, branchRed₀, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    keepHom_one_inU_add_inV a b hb, map_add, PowerSeries.map_C]

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"

namespace P1Branch

open AnnulusNF

variable {W : Type u} [CommRing W]

theorem inU_C_mul (w : W) (a : PowerSeries W) : inU (PowerSeries.C w * a) = MvPowerSeries.C w * inU a := by
  ext d; rw [coeff_inU, MvPowerSeries.coeff_C_mul, coeff_inU]; split_ifs <;> simp [PowerSeries.coeff_C_mul]

theorem inV_C_mul (w : W) (b : PowerSeries W) : inV (PowerSeries.C w * b) = MvPowerSeries.C w * inV b := by
  ext d; rw [coeff_inV, MvPowerSeries.coeff_C_mul, coeff_inV]; split_ifs <;> simp [PowerSeries.coeff_C_mul]

theorem mk_C_mul (π w : W) (F : MvPowerSeries (Fin 2) W) : mk π (MvPowerSeries.C w * F) = const π w * mk π F := by
  rw [map_mul]; rfl

theorem exists_eq_C_mul_of_forall_dvd (w : W) (a : PowerSeries W) (h : ∀ i, w ∣ PowerSeries.coeff i a) :
    ∃ a' : PowerSeries W, a = PowerSeries.C w * a' := by
  choose c hc using h
  refine ⟨PowerSeries.mk c, ?_⟩
  ext i
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc i]

variable [IsDomain W] [IsDiscreteValuationRing W]

theorem varpi_mem (ϖ : W) (hϖ : Irreducible ϖ) : ϖ ∈ maximalIdeal W :=
  (Irreducible.maximalIdeal_eq hϖ) ▸ Ideal.mem_span_singleton_self ϖ

theorem residue_eq_zero_iff_dvd (ϖ : W) (hϖ : Irreducible ϖ) (w : W) : residue W w = 0 ↔ ϖ ∣ w := by
  rw [residue_eq_zero_iff, Irreducible.maximalIdeal_eq hϖ, Ideal.mem_span_singleton]

theorem exists_eq_const_mul_of_branchRed_eq_zero [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (y : UVCrossingModel W (ϖ ^ e))
    (h0 : branchRed 0 ϖ (varpi_mem ϖ hϖ) e he y = 0)
    (h1 : branchRed 1 ϖ (varpi_mem ϖ hϖ) e he y = 0) :
    ∃ y' : UVCrossingModel W (ϖ ^ e), y = const (ϖ ^ e) ϖ * y' := by
  haveI : IsAdicComplete (Ideal.span {ϖ}) W :=
    (Irreducible.maximalIdeal_eq hϖ) ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  obtain ⟨⟨a, b⟩, hb, rfl⟩ := exists_normalForm ϖ e he y
  simp only at hb h0 h1 ⊢
  rw [branchRed_zero_normalForm _ _ _ _ a b hb] at h0
  rw [branchRed_one_normalForm _ _ _ _ a b hb] at h1
  have ha : ∀ i, ϖ ∣ PowerSeries.coeff i a := fun i => by
    rw [← residue_eq_zero_iff_dvd ϖ hϖ]
    have := congrArg (PowerSeries.coeff i) h0
    rwa [PowerSeries.coeff_map, map_zero] at this
  have hbd : ∀ j, ϖ ∣ PowerSeries.coeff j b := fun j => by
    by_cases hj : j = 0
    · subst hj; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hb; rw [hb]; exact dvd_zero _
    rw [← residue_eq_zero_iff_dvd ϖ hϖ]
    have := congrArg (PowerSeries.coeff j) h1
    rwa [map_add, PowerSeries.coeff_map, PowerSeries.coeff_C, if_neg hj, zero_add, map_zero] at this
  obtain ⟨a', rfl⟩ := exists_eq_C_mul_of_forall_dvd ϖ a ha
  obtain ⟨b', rfl⟩ := exists_eq_C_mul_of_forall_dvd ϖ b hbd
  refine ⟨mk (ϖ ^ e) (inU a' + inV b'), ?_⟩
  rw [inU_C_mul, inV_C_mul, ← mul_add, mk_C_mul]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem inU_zero : inU (0 : PowerSeries W) = 0 := by
  ext d; rw [coeff_inU]; split_ifs <;> simp

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem inV_zero : inV (0 : PowerSeries W) = 0 := by
  ext d; rw [coeff_inV]; split_ifs <;> simp

omit [IsDiscreteValuationRing W] in
theorem eq_zero_of_C_mul_eq_zero {w : W} (hw : w ≠ 0) {a : PowerSeries W} (h : PowerSeries.C w * a = 0) : a = 0 := by
  ext i
  have := congrArg (PowerSeries.coeff i) h
  rw [PowerSeries.coeff_C_mul, map_zero] at this
  simpa using (mul_eq_zero.mp this).resolve_left hw

theorem eq_zero_of_const_mul_eq_zero [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (w : UVCrossingModel W (ϖ ^ e))
    (h : const (ϖ ^ e) ϖ * w = 0) : w = 0 := by
  haveI : IsAdicComplete (Ideal.span {ϖ}) W :=
    (Irreducible.maximalIdeal_eq hϖ) ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  obtain ⟨⟨a, b⟩, hb, rfl⟩ := exists_normalForm ϖ e he w
  simp only at hb h ⊢
  rw [← mk_C_mul, mul_add, ← inU_C_mul, ← inV_C_mul] at h
  have h0 : mk (ϖ ^ e) (inU (PowerSeries.C ϖ * a) + inV (PowerSeries.C ϖ * b)) = mk (ϖ ^ e) (inU 0 + inV 0) := by
    rw [h, inU_zero, inV_zero, add_zero, map_zero]
  have hu := normalForm_unique ϖ e he (PowerSeries.C ϖ * a) (PowerSeries.C ϖ * b) 0 0 (by simp [hb]) (by simp) h0
  have ha : a = 0 := eq_zero_of_C_mul_eq_zero hϖ.ne_zero hu.1
  have hb0 : b = 0 := eq_zero_of_C_mul_eq_zero hϖ.ne_zero hu.2
  subst ha; subst hb0
  rw [inU_zero, inV_zero, add_zero, map_zero]

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"

namespace P1Branch

open AnnulusNF

variable {W : Type u} [CommRing W]

theorem algebraMap_eq_const (π w : W) : algebraMap W (UVCrossingModel W π) w = const π w := by
  rw [IsScalarTower.algebraMap_apply W (MvPowerSeries (Fin 2) W) (UVCrossingModel W π),
    MvPowerSeries.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  rfl

variable [IsDomain W] [IsDiscreteValuationRing W]

theorem branchRed_const (s : Fin 2) (ϖ : W) (hϖm : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) (w : W) :
    branchRed s ϖ hϖm e he (const (ϖ ^ e) w) = PowerSeries.C (residue W w) := by
  change branchRed s ϖ hϖm e he (mk (ϖ ^ e) (MvPowerSeries.C w)) = _
  rw [branchRed_mk, branchRed₀_C]

variable [IsAdicComplete (maximalIdeal W) W]

theorem isSMulRegular_quotient_of_good (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (hgood0 : ∃ i, IsUnit (PowerSeries.coeff i ab.1))
    (hgoodE : IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2)) :
    IsSMulRegular (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) ϖ := by
  classical
  have hmem := varpi_mem ϖ hϖ

  have hx0 : branchRed 0 ϖ hmem e he x ≠ 0 := by
    intro hzero
    rw [← habx, branchRed_zero_normalForm _ _ _ _ ab.1 ab.2 hb] at hzero
    obtain ⟨i, hi⟩ := hgood0
    have := congrArg (PowerSeries.coeff i) hzero
    rw [PowerSeries.coeff_map, map_zero, residue_eq_zero_iff] at this
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp this) hi
  have hx1 : branchRed 1 ϖ hmem e he x ≠ 0 := by
    intro hzero
    rw [← habx, branchRed_one_normalForm _ _ _ _ ab.1 ab.2 hb] at hzero
    rcases hgoodE with h0u | ⟨j, hj1, hju⟩
    · have := congrArg (PowerSeries.coeff 0) hzero
      rw [map_add, PowerSeries.coeff_map, PowerSeries.coeff_C, if_pos rfl, map_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hb, map_zero, add_zero, residue_eq_zero_iff] at this
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp this) h0u
    · have := congrArg (PowerSeries.coeff j) hzero
      rw [map_add, PowerSeries.coeff_map, PowerSeries.coeff_C, if_neg (by omega), zero_add, map_zero,
        residue_eq_zero_iff] at this
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp this) hju

  intro p₁ p₂ hpq
  simp only at hpq
  obtain ⟨y₁, rfl⟩ := Ideal.Quotient.mk_surjective p₁
  obtain ⟨y₂, rfl⟩ := Ideal.Quotient.mk_surjective p₂
  rw [Ideal.Quotient.eq]
  have h' : Ideal.Quotient.mk (Ideal.span {x}) (const (ϖ ^ e) ϖ * (y₁ - y₂)) = 0 := by
    rw [← algebraMap_eq_const, map_mul, Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def, map_sub, smul_sub]
    exact sub_eq_zero.mpr hpq
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h'
  obtain ⟨z, hz⟩ := h'
  have hres0 : PowerSeries.C (residue W ϖ) = (0 : PowerSeries (ResidueField W)) := by
    rw [(residue_eq_zero_iff_dvd ϖ hϖ ϖ).mpr (dvd_refl ϖ), map_zero]

  have hz0 : branchRed 0 ϖ hmem e he z = 0 := by
    have := congrArg (branchRed 0 ϖ hmem e he) hz
    rw [map_mul, map_mul, branchRed_const, hres0, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_right hx0
  have hz1 : branchRed 1 ϖ hmem e he z = 0 := by
    have := congrArg (branchRed 1 ϖ hmem e he) hz
    rw [map_mul, map_mul, branchRed_const, hres0, zero_mul] at this
    exact (mul_eq_zero.mp this).resolve_right hx1
  obtain ⟨z', rfl⟩ := exists_eq_const_mul_of_branchRed_eq_zero ϖ hϖ e he z hz0 hz1

  have hcancel : y₁ - y₂ = z' * x := by
    have h3 : const (ϖ ^ e) ϖ * (y₁ - y₂ - z' * x) = 0 := by
      rw [mul_sub, ← hz]; ring
    exact sub_eq_zero.mp (eq_zero_of_const_mul_eq_zero ϖ hϖ e he _ h3)
  rw [hcancel, Ideal.mem_span_singleton']
  exact ⟨z', rfl⟩

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete UVCrossingModel.range_chartHom_eq_fixedSubring UVCrossingModel.exists_mem_fixedSubring_eq_add_mul_U UVCrossingModel.chartHom_C UVCrossingModel.isNoetherianRing"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const constHom constHom_apply mk_surjective crossingSwap crossingSwap_mk S fixedSubring mem_fixedSubring_iff inU inV coeff_inU coeff_inV annulusWeight repGaussOrder gaussOrder repGaussOrder_le le_repGaussOrder_iff repGaussOrder_le_gaussOrder gaussOrder_le_iff nfCoeff nfExponent termOrder dominantIndices chartHom isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete range_chartHom_eq_fixedSubring exists_mem_fixedSubring_eq_add_mul_U chartHom_C isNoetherianRing"
p2m_open "ModularCurve.UVCrossingModel~U_mul_V ModularCurve"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"

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
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"

namespace P1Branch

open AnnulusNF

variable {W : Type u} [CommRing W]

theorem constantCoeff_keepHom_eq (F : MvPowerSeries (Fin 2) W) :
    PowerSeries.constantCoeff (keepHom 0 F) = PowerSeries.constantCoeff (keepHom 1 F) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_keepHom, coeff_keepHom, Finsupp.single_zero, Finsupp.single_zero]

variable [IsDomain W] [IsDiscreteValuationRing W]

theorem constantCoeff_branchRed_eq (ϖ : W) (hϖm : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e)
    (z : UVCrossingModel W (ϖ ^ e)) :
    PowerSeries.constantCoeff (branchRed 0 ϖ hϖm e he z) = PowerSeries.constantCoeff (branchRed 1 ϖ hϖm e he z) := by
  obtain ⟨F, rfl⟩ := mk_surjective (ϖ ^ e) z
  rw [branchRed_mk, branchRed_mk]
  simp only [branchRed₀, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_keepHom_eq]

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel"

namespace P1Branch

open AnnulusNF

variable {W : Type u} [CommRing W]

noncomputable def shift (p : PowerSeries W) : PowerSeries W := PowerSeries.mk fun i => PowerSeries.coeff (i + 1) p

@[scoped simp] theorem coeff_shift (p : PowerSeries W) (i : ℕ) : PowerSeries.coeff i (shift p) = PowerSeries.coeff (i + 1) p := by
  simp [shift]

theorem coeff_shift_iterate (p : PowerSeries W) (k i : ℕ) :
    PowerSeries.coeff i (shift^[k] p) = PowerSeries.coeff (i + k) p := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih (shift p), coeff_shift, Nat.add_assoc, Nat.add_comm k 1]

theorem constantCoeff_shift_iterate (p : PowerSeries W) (k : ℕ) :
    PowerSeries.constantCoeff (shift^[k] p) = PowerSeries.coeff k p := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_shift_iterate, Nat.zero_add]

theorem ij_eq_zero_iff (i j : ℕ) : ij i j = (0 : Fin 2 →₀ ℕ) ↔ i = 0 ∧ j = 0 := by
  constructor
  · intro h
    exact ⟨by simpa [ij_apply_zero] using congrArg (fun f : Fin 2 →₀ ℕ => f 0) h,
      by simpa [ij_apply_one] using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h⟩
  · rintro ⟨rfl, rfl⟩
    simp [ij]

theorem coeff_X_zero_mul (G : MvPowerSeries (Fin 2) W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * G) =
      if 1 ≤ d 0 then MvPowerSeries.coeff (ij (d 0 - 1) (d 1)) G else 0 := by
  have hX : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) = MvPowerSeries.monomial (ij 1 0) 1 := by
    rw [MvPowerSeries.X]; simp [ij]
  rw [hX, MvPowerSeries.coeff_monomial_mul]
  have hle : ij 1 0 ≤ d ↔ 1 ≤ d 0 := by
    constructor
    · intro h; simpa [ij] using h 0
    · intro h0 k; fin_cases k <;> simp [ij, h0]
  by_cases h : 1 ≤ d 0
  · rw [if_pos (hle.2 h), if_pos h, one_mul]
    congr 1
    rw [eq_ij (d - ij 1 0)]
    simp [ij]
  · rw [if_neg (fun h' => h (hle.1 h')), if_neg h]

theorem coeff_X_one_mul (G : MvPowerSeries (Fin 2) W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d ((MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) * G) =
      if 1 ≤ d 1 then MvPowerSeries.coeff (ij (d 0) (d 1 - 1)) G else 0 := by
  have hX : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) W) = MvPowerSeries.monomial (ij 0 1) 1 := by
    rw [MvPowerSeries.X]; simp [ij]
  rw [hX, MvPowerSeries.coeff_monomial_mul]
  have hle : ij 0 1 ≤ d ↔ 1 ≤ d 1 := by
    constructor
    · intro h; simpa [ij] using h 1
    · intro h1 k; fin_cases k <;> simp [ij, h1]
  by_cases h : 1 ≤ d 1
  · rw [if_pos (hle.2 h), if_pos h, one_mul]
    congr 1
    rw [eq_ij (d - ij 0 1)]
    simp [ij]
  · rw [if_neg (fun h' => h (hle.1 h')), if_neg h]

theorem inU_eq_C_add_X_mul (p : PowerSeries W) :
    inU p = MvPowerSeries.C (PowerSeries.constantCoeff p) + MvPowerSeries.X 0 * inU (shift p) := by
  classical
  ext d
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = ij i j := ⟨d 0, d 1, eq_ij d⟩
  rw [map_add, coeff_X_zero_mul, MvPowerSeries.coeff_C, coeff_inU]
  simp only [ij_apply_zero, ij_apply_one, ij_eq_zero_iff]
  rcases i with _ | i <;> rcases j with _ | j <;> simp [coeff_inU, ij_apply_zero, ij_apply_one]

theorem inV_eq_C_add_X_mul (q : PowerSeries W) :
    inV q = MvPowerSeries.C (PowerSeries.constantCoeff q) + MvPowerSeries.X 1 * inV (shift q) := by
  classical
  ext d
  obtain ⟨i, j, rfl⟩ : ∃ i j, d = ij i j := ⟨d 0, d 1, eq_ij d⟩
  rw [map_add, coeff_X_one_mul, MvPowerSeries.coeff_C, coeff_inV]
  simp only [ij_apply_zero, ij_apply_one, ij_eq_zero_iff]
  rcases i with _ | i <;> rcases j with _ | j <;> simp [coeff_inV, ij_apply_zero, ij_apply_one]

theorem inU_eq_sum_add_X_pow_mul (p : PowerSeries W) (m : ℕ) :
    inU p = (∑ i ∈ Finset.range m, MvPowerSeries.C (PowerSeries.coeff i p) * MvPowerSeries.X 0 ^ i) +
      MvPowerSeries.X 0 ^ m * inU (shift^[m] p) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply' shift m p, ← constantCoeff_shift_iterate p m]
    conv_lhs => rw [ih, inU_eq_C_add_X_mul (shift^[m] p)]
    ring

theorem inV_eq_sum_add_X_pow_mul (q : PowerSeries W) (n : ℕ) :
    inV q = (∑ j ∈ Finset.range n, MvPowerSeries.C (PowerSeries.coeff j q) * MvPowerSeries.X 1 ^ j) +
      MvPowerSeries.X 1 ^ n * inV (shift^[n] q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Function.iterate_succ_apply' shift n q, ← constantCoeff_shift_iterate q n]
    conv_lhs => rw [ih, inV_eq_C_add_X_mul (shift^[n] q)]
    ring

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

namespace P1Branch

open AnnulusNF

variable {W : Type u} [CommRing W]

theorem mk_C (π w : W) : mk π (MvPowerSeries.C w) = const π w := rfl

theorem mk_X_zero (π : W) : mk π (MvPowerSeries.X 0) = U π := rfl

theorem mk_X_one (π : W) : mk π (MvPowerSeries.X 1) = V π := rfl

theorem const_mul (π a b : W) : const π (a * b) = const π a * const π b := by
  rw [← constHom_apply, ← constHom_apply, ← constHom_apply, map_mul]

theorem U_mul_V (π : W) : U π * V π = const π π := by
  show mk π (MvPowerSeries.X 0) * mk π (MvPowerSeries.X 1) = mk π (MvPowerSeries.C π)
  rw [← map_mul]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq]
  exact Ideal.subset_span rfl

theorem coeff_zero_inU (q : PowerSeries W) :
    MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) (inU q) = PowerSeries.constantCoeff q := by
  rw [coeff_inU]; simp

theorem coeff_zero_inV (q : PowerSeries W) :
    MvPowerSeries.coeff (0 : Fin 2 →₀ ℕ) (inV q) = PowerSeries.constantCoeff q := by
  rw [coeff_inV]; simp

theorem isUnit_inU {q : PowerSeries W} (hq : IsUnit (PowerSeries.constantCoeff q)) : IsUnit (inU q) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_inU]
  exact hq

theorem isUnit_inV {q : PowerSeries W} (hq : IsUnit (PowerSeries.constantCoeff q)) : IsUnit (inV q) := by
  rw [MvPowerSeries.isUnit_iff_constantCoeff, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_zero_inV]
  exact hq

theorem exists_mk_inU_eq (π ϖ : W) (a : PowerSeries W) (m : ℕ) (ha : ∀ i < m, ϖ ∣ PowerSeries.coeff i a) :
    ∃ y, mk π (inU a) = const π ϖ * y + U π ^ m * mk π (inU (shift^[m] a)) := by
  have hc : ∀ i, ∃ c : W, i < m → PowerSeries.coeff i a = ϖ * c := by
    intro i
    by_cases hi : i < m
    · obtain ⟨c, hc⟩ := ha i hi
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose c hc using hc
  refine ⟨∑ i ∈ Finset.range m, const π (c i) * U π ^ i, ?_⟩
  rw [inU_eq_sum_add_X_pow_mul a m]
  simp only [map_add, map_sum, map_mul, map_pow, mk_C, mk_X_zero, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hc i (Finset.mem_range.1 hi), const_mul, mul_assoc]

theorem exists_mk_inV_eq (π ϖ : W) (b : PowerSeries W) (n : ℕ) (hb : ∀ j < n, ϖ ∣ PowerSeries.coeff j b) :
    ∃ y, mk π (inV b) = const π ϖ * y + V π ^ n * mk π (inV (shift^[n] b)) := by
  have hc : ∀ j, ∃ c : W, j < n → PowerSeries.coeff j b = ϖ * c := by
    intro j
    by_cases hj : j < n
    · obtain ⟨c, hc⟩ := hb j hj
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose c hc using hc
  refine ⟨∑ j ∈ Finset.range n, const π (c j) * V π ^ j, ?_⟩
  rw [inV_eq_sum_add_X_pow_mul b n]
  simp only [map_add, map_sum, map_mul, map_pow, mk_C, mk_X_one, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hc j (Finset.mem_range.1 hj), const_mul, mul_assoc]

variable [IsDomain W] [IsDiscreteValuationRing W]

theorem dvd_of_not_isUnit (ϖ : W) (hϖ : Irreducible ϖ) {w : W} (hw : ¬ IsUnit w) : ϖ ∣ w := by
  rw [← Ideal.mem_span_singleton, ← Irreducible.maximalIdeal_eq hϖ]
  exact (IsLocalRing.mem_maximalIdeal w).mpr hw

variable [IsAdicComplete (maximalIdeal W) W]

theorem relations_quotient_span_pair (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e))
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (m n : ℕ) (hm : IsUnit (PowerSeries.coeff m ab.1)) (hm' : ∀ i < m, ¬ IsUnit (PowerSeries.coeff i ab.1))
    (hn1 : 1 ≤ n) (hn : IsUnit (PowerSeries.coeff n ab.2)) (hn' : ∀ j < n, ¬ IsUnit (PowerSeries.coeff j ab.2))
    (h0 : ¬ IsUnit (PowerSeries.constantCoeff ab.1)) :
    let J : Ideal (UVCrossingModel W (ϖ ^ e)) := Ideal.span {x, const (ϖ ^ e) ϖ}
    U (ϖ ^ e) ^ (m + 1) ∈ J ∧ V (ϖ ^ e) ^ (n + 1) ∈ J ∧ U (ϖ ^ e) * V (ϖ ^ e) ∈ J ∧
      ∃ c : W, IsUnit c ∧ U (ϖ ^ e) ^ m - const (ϖ ^ e) c * V (ϖ ^ e) ^ n ∈ J := by
  intro J
  have hxJ : x ∈ J := Ideal.subset_span (by simp)
  have hϖJm : const (ϖ ^ e) ϖ ∈ J := Ideal.subset_span (by simp)
  clear_value J

  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m
    · exact absurd (by simpa using hm) h0
    · exact ⟨m, rfl⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩

  obtain ⟨π, hπ⟩ : ∃ π : UVCrossingModel W (ϖ ^ e) →+* UVCrossingModel W (ϖ ^ e) ⧸ J,
      π = Ideal.Quotient.mk J := ⟨_, rfl⟩
  have hmemJ : ∀ z, z ∈ J ↔ π z = 0 := fun z => by rw [hπ, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨κ, hκ⟩ : ∃ κ : W →+* UVCrossingModel W (ϖ ^ e) ⧸ J, ∀ w, κ w = π (const (ϖ ^ e) w) :=
    ⟨π.comp (constHom (ϖ ^ e)), fun w => rfl⟩
  clear hπ
  have hxJ' : π x = 0 := (hmemJ x).1 hxJ
  have hϖJ' : π (const (ϖ ^ e) ϖ) = 0 := (hmemJ _).1 hϖJm

  have huv : π (U (ϖ ^ e)) * π (V (ϖ ^ e)) = 0 := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have h : π (U (ϖ ^ (e' + 1))) * π (V (ϖ ^ (e' + 1))) =
        π (const (ϖ ^ (e' + 1)) ϖ) * π (const (ϖ ^ (e' + 1)) (ϖ ^ e')) := by
      rw [← map_mul, ← map_mul, U_mul_V, ← const_mul, ← pow_succ']
    linear_combination h + π (const (ϖ ^ (e' + 1)) (ϖ ^ e')) * hϖJ'

  have ha : ∀ i < m + 1, ϖ ∣ PowerSeries.coeff i ab.1 := fun i hi => dvd_of_not_isUnit ϖ hϖ (hm' i hi)
  have hb' : ∀ j < n + 1, ϖ ∣ PowerSeries.coeff j ab.2 := fun j hj => dvd_of_not_isUnit ϖ hϖ (hn' j hj)
  obtain ⟨y₁, hy₁⟩ := exists_mk_inU_eq (ϖ ^ e) ϖ ab.1 (m + 1) ha
  obtain ⟨y₂, hy₂⟩ := exists_mk_inV_eq (ϖ ^ e) ϖ ab.2 (n + 1) hb'
  have hAu : IsUnit (π (mk (ϖ ^ e) (inU (shift^[m + 1] ab.1)))) :=
    ((isUnit_inU (by rw [constantCoeff_shift_iterate]; exact hm)).map _).map _
  have hBu : IsUnit (π (mk (ϖ ^ e) (inV (shift^[n + 1] ab.2)))) :=
    ((isUnit_inV (by rw [constantCoeff_shift_iterate]; exact hn)).map _).map _

  have key : π (U (ϖ ^ e)) ^ (m + 1) * π (mk (ϖ ^ e) (inU (shift^[m + 1] ab.1))) +
      π (V (ϖ ^ e)) ^ (n + 1) * π (mk (ϖ ^ e) (inV (shift^[n + 1] ab.2))) = 0 := by
    have hxR : x = const (ϖ ^ e) ϖ * y₁ + U (ϖ ^ e) ^ (m + 1) * mk (ϖ ^ e) (inU (shift^[m + 1] ab.1)) +
        (const (ϖ ^ e) ϖ * y₂ + V (ϖ ^ e) ^ (n + 1) * mk (ϖ ^ e) (inV (shift^[n + 1] ab.2))) := by
      rw [← habx, map_add, hy₁, hy₂]
    have hx := congrArg π hxR
    rw [π.map_add, π.map_add, π.map_add, π.map_mul, π.map_mul, π.map_mul, π.map_mul,
      π.map_pow, π.map_pow] at hx
    linear_combination -hx + hxJ' - (π y₁ + π y₂) * hϖJ'

  have hA' : π (mk (ϖ ^ e) (inU (shift^[m + 1] ab.1))) = κ (PowerSeries.coeff (m + 1) ab.1) +
      π (U (ϖ ^ e)) * π (mk (ϖ ^ e) (inU (shift^[m + 1 + 1] ab.1))) := by
    rw [inU_eq_C_add_X_mul (shift^[m + 1] ab.1), constantCoeff_shift_iterate,
      ← Function.iterate_succ_apply' shift (m + 1), (mk (ϖ ^ e)).map_add, (mk (ϖ ^ e)).map_mul, mk_C, mk_X_zero,
      π.map_add, π.map_mul, hκ]
  have hB' : π (mk (ϖ ^ e) (inV (shift^[n + 1] ab.2))) = κ (PowerSeries.coeff (n + 1) ab.2) +
      π (V (ϖ ^ e)) * π (mk (ϖ ^ e) (inV (shift^[n + 1 + 1] ab.2))) := by
    rw [inV_eq_C_add_X_mul (shift^[n + 1] ab.2), constantCoeff_shift_iterate,
      ← Function.iterate_succ_apply' shift (n + 1), (mk (ϖ ^ e)).map_add, (mk (ϖ ^ e)).map_mul, mk_C, mk_X_one,
      π.map_add, π.map_mul, hκ]

  have H1 : π (U (ϖ ^ e)) ^ (m + 1 + 1) = 0 := by
    have h : π (U (ϖ ^ e)) ^ (m + 1 + 1) * π (mk (ϖ ^ e) (inU (shift^[m + 1] ab.1))) = 0 := by
      linear_combination π (U (ϖ ^ e)) * key -
        π (V (ϖ ^ e)) ^ n * π (mk (ϖ ^ e) (inV (shift^[n + 1] ab.2))) * huv
    obtain ⟨Ainv, hAinv⟩ := hAu.exists_left_inv
    linear_combination Ainv * h - π (U (ϖ ^ e)) ^ (m + 1 + 1) * hAinv
  have H2 : π (V (ϖ ^ e)) ^ (n + 1 + 1) = 0 := by
    have h : π (V (ϖ ^ e)) ^ (n + 1 + 1) * π (mk (ϖ ^ e) (inV (shift^[n + 1] ab.2))) = 0 := by
      linear_combination π (V (ϖ ^ e)) * key -
        π (U (ϖ ^ e)) ^ m * π (mk (ϖ ^ e) (inU (shift^[m + 1] ab.1))) * huv
    obtain ⟨Binv, hBinv⟩ := hBu.exists_left_inv
    linear_combination Binv * h - π (V (ϖ ^ e)) ^ (n + 1 + 1) * hBinv

  have E1 : κ (PowerSeries.coeff (m + 1) ab.1) * π (U (ϖ ^ e)) ^ (m + 1) +
      κ (PowerSeries.coeff (n + 1) ab.2) * π (V (ϖ ^ e)) ^ (n + 1) = 0 := by
    rw [hA', hB'] at key
    linear_combination key - π (mk (ϖ ^ e) (inU (shift^[m + 1 + 1] ab.1))) * H1 -
      π (mk (ϖ ^ e) (inV (shift^[n + 1 + 1] ab.2))) * H2
  obtain ⟨am, ham⟩ := hm
  have E2 : κ (↑am⁻¹ : W) * κ (PowerSeries.coeff (m + 1) ab.1) = 1 := by
    rw [← ham, ← map_mul, Units.inv_mul]
    exact map_one κ
  have hcu : IsUnit (-(↑am⁻¹ * PowerSeries.coeff (n + 1) ab.2)) := ((Units.isUnit am⁻¹).mul hn).neg
  have E3 : κ (-(↑am⁻¹ * PowerSeries.coeff (n + 1) ab.2)) = -(κ (↑am⁻¹ : W) * κ (PowerSeries.coeff (n + 1) ab.2)) := by
    rw [map_neg, map_mul]
  have H3 : π (U (ϖ ^ e)) ^ (m + 1) - κ (-(↑am⁻¹ * PowerSeries.coeff (n + 1) ab.2)) * π (V (ϖ ^ e)) ^ (n + 1) = 0 := by
    linear_combination κ (↑am⁻¹ : W) * E1 - π (U (ϖ ^ e)) ^ (m + 1) * E2 - π (V (ϖ ^ e)) ^ (n + 1) * E3

  refine ⟨(hmemJ _).2 (by rw [map_pow, H1]), (hmemJ _).2 (by rw [map_pow, H2]),
    (hmemJ _).2 (by rw [map_mul, huv]), _, hcu, (hmemJ _).2 ?_⟩
  rw [map_sub, map_mul, map_pow, map_pow, ← hκ, H3]

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

namespace P1Branch

open AnnulusNF

section coeffSums

variable {K : Type*} [CommSemiring K] {N : ℕ}

theorem coeff_sum_C_mul_X_pow (f : Fin N → K) (i : Fin N) :
    PowerSeries.coeff (i : ℕ) (∑ l : Fin N, PowerSeries.C (f l) * PowerSeries.X ^ (l : ℕ)) = f i := by
  rw [map_sum, Finset.sum_eq_single i]
  · rw [PowerSeries.coeff_C_mul_X_pow, if_pos rfl]
  · intro l _ hl
    rw [PowerSeries.coeff_C_mul_X_pow, if_neg (fun h => hl (Fin.ext h).symm)]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coeff_sum_C_mul_X_pow_succ (f : Fin N → K) (i : Fin N) :
    PowerSeries.coeff ((i : ℕ) + 1) (∑ l : Fin N, PowerSeries.C (f l) * PowerSeries.X ^ ((l : ℕ) + 1)) = f i := by
  rw [map_sum, Finset.sum_eq_single i]
  · rw [PowerSeries.coeff_C_mul_X_pow, if_pos rfl]
  · intro l _ hl
    rw [PowerSeries.coeff_C_mul_X_pow, if_neg (fun h => hl (Fin.ext (by omega)).symm)]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coeff_zero_sum_C_mul_X_pow_succ (f : Fin N → K) :
    PowerSeries.coeff 0 (∑ l : Fin N, PowerSeries.C (f l) * PowerSeries.X ^ ((l : ℕ) + 1)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun l _ => by rw [PowerSeries.coeff_C_mul_X_pow, if_neg (by omega)]

end coeffSums
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

variable {W : Type u} [CommRing W]

section red

variable [IsLocalRing W]

theorem branchRed_zero_U (ϖ : W) (hϖm : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) :
    branchRed 0 ϖ hϖm e he (U (ϖ ^ e)) = PowerSeries.X := by
  show branchRed 0 ϖ hϖm e he (mk (ϖ ^ e) (MvPowerSeries.X 0)) = _
  rw [branchRed_mk, branchRed₀_X_self]

theorem branchRed_zero_V (ϖ : W) (hϖm : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) :
    branchRed 0 ϖ hϖm e he (V (ϖ ^ e)) = 0 := by
  show branchRed 0 ϖ hϖm e he (mk (ϖ ^ e) (MvPowerSeries.X 1)) = _
  rw [branchRed_mk, branchRed₀_X_other 0 1 (by decide)]

theorem branchRed_one_U (ϖ : W) (hϖm : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) :
    branchRed 1 ϖ hϖm e he (U (ϖ ^ e)) = 0 := by
  show branchRed 1 ϖ hϖm e he (mk (ϖ ^ e) (MvPowerSeries.X 0)) = _
  rw [branchRed_mk, branchRed₀_X_other 1 0 (by decide)]

theorem branchRed_one_V (ϖ : W) (hϖm : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) :
    branchRed 1 ϖ hϖm e he (V (ϖ ^ e)) = PowerSeries.X := by
  show branchRed 1 ϖ hϖm e he (mk (ϖ ^ e) (MvPowerSeries.X 1)) = _
  rw [branchRed_mk, branchRed₀_X_self]

end red
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

variable [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

theorem coeffs_mem_of_combination_mem (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e))
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (m n : ℕ) (hm : IsUnit (PowerSeries.coeff m ab.1)) (hm' : ∀ i < m, ¬ IsUnit (PowerSeries.coeff i ab.1))
    (hn1 : 1 ≤ n) (hn : IsUnit (PowerSeries.coeff n ab.2)) (hn' : ∀ j < n, ¬ IsUnit (PowerSeries.coeff j ab.2))
    (h0 : ¬ IsUnit (PowerSeries.constantCoeff ab.1))
    (c : Fin (m + 1) → W) (d : Fin (n - 1) → W)
    (hmem : (∑ i, const (ϖ ^ e) (c i) * U (ϖ ^ e) ^ (i : ℕ)) + (∑ j, const (ϖ ^ e) (d j) * V (ϖ ^ e) ^ ((j : ℕ) + 1))
      ∈ Ideal.span {x, const (ϖ ^ e) ϖ}) :
    (∀ i, ϖ ∣ c i) ∧ (∀ j, ϖ ∣ d j) := by
  classical
  have hϖm := varpi_mem ϖ hϖ
  have hres0 : PowerSeries.C (residue W ϖ) = (0 : PowerSeries (ResidueField W)) := by
    rw [(residue_eq_zero_iff_dvd ϖ hϖ ϖ).mpr (dvd_refl ϖ), map_zero]
  obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 hmem

  have hx0 : branchRed 0 ϖ hϖm e he x = PowerSeries.map (residue W) ab.1 := by
    rw [← habx, branchRed_zero_normalForm _ _ _ _ ab.1 ab.2 hb]
  have hx1 : branchRed 1 ϖ hϖm e he x = PowerSeries.map (residue W) ab.2 := by
    rw [← habx, branchRed_one_normalForm _ _ _ _ ab.1 ab.2 hb,
      (residue_eq_zero_iff_dvd ϖ hϖ _).mpr (dvd_of_not_isUnit ϖ hϖ h0), map_zero, zero_add]
  have hadvd : PowerSeries.X ^ m ∣ PowerSeries.map (residue W) ab.1 :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi => by
      rw [PowerSeries.coeff_map, residue_eq_zero_iff_dvd ϖ hϖ]; exact dvd_of_not_isUnit ϖ hϖ (hm' i hi)
  have hbdvd : PowerSeries.X ^ n ∣ PowerSeries.map (residue W) ab.2 :=
    PowerSeries.X_pow_dvd_iff.mpr fun j hj => by
      rw [PowerSeries.coeff_map, residue_eq_zero_iff_dvd ϖ hϖ]; exact dvd_of_not_isUnit ϖ hϖ (hn' j hj)
  have hbne : PowerSeries.map (residue W) ab.2 ≠ 0 := by
    intro hzero
    have := congrArg (PowerSeries.coeff n) hzero
    rw [PowerSeries.coeff_map, map_zero, residue_eq_zero_iff] at this
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp this) hn

  have h0eq : (∑ i : Fin (m + 1), PowerSeries.C (residue W (c i)) * PowerSeries.X ^ (i : ℕ)) =
      branchRed 0 ϖ hϖm e he r * PowerSeries.map (residue W) ab.1 := by
    have h := congrArg (branchRed 0 ϖ hϖm e he) hrs
    simp only [map_add, map_mul, map_sum, map_pow, branchRed_const, branchRed_zero_U, branchRed_zero_V, hx0, hres0,
      mul_zero, add_zero, ne_eq, Nat.succ_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero] at h
    exact h.symm
  have h1eq : PowerSeries.C (residue W (c 0)) +
      (∑ j : Fin (n - 1), PowerSeries.C (residue W (d j)) * PowerSeries.X ^ ((j : ℕ) + 1)) =
      branchRed 1 ϖ hϖm e he r * PowerSeries.map (residue W) ab.2 := by
    have h := congrArg (branchRed 1 ϖ hϖm e he) hrs
    simp only [map_add, map_mul, map_sum, map_pow, branchRed_const, branchRed_one_U, branchRed_one_V, hx1, hres0,
      mul_zero, add_zero] at h
    rw [Fin.sum_univ_succ] at h
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, ne_eq, Nat.succ_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Finset.sum_const_zero, add_zero] at h
    exact h.symm

  have h1dvd : PowerSeries.X ^ n ∣ PowerSeries.C (residue W (c 0)) +
      (∑ j : Fin (n - 1), PowerSeries.C (residue W (d j)) * PowerSeries.X ^ ((j : ℕ) + 1)) := by
    rw [h1eq]; exact Dvd.dvd.mul_left hbdvd _
  have hd : ∀ j : Fin (n - 1), residue W (d j) = 0 := fun j => by
    have := (PowerSeries.X_pow_dvd_iff.mp h1dvd) ((j : ℕ) + 1) (by omega)
    rwa [map_add, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero _), zero_add, coeff_sum_C_mul_X_pow_succ] at this
  have hc0 : residue W (c 0) = 0 := by
    have := (PowerSeries.X_pow_dvd_iff.mp h1dvd) 0 (by omega)
    rwa [map_add, PowerSeries.coeff_C, if_pos rfl, coeff_zero_sum_C_mul_X_pow_succ, add_zero] at this

  have hr1 : branchRed 1 ϖ hϖm e he r = 0 := by
    have hz : branchRed 1 ϖ hϖm e he r * PowerSeries.map (residue W) ab.2 = 0 := by
      rw [← h1eq, hc0, map_zero, zero_add]
      exact Finset.sum_eq_zero fun j _ => by rw [hd j, map_zero, zero_mul]
    exact (mul_eq_zero.mp hz).resolve_right hbne
  have hr0 : PowerSeries.X ∣ branchRed 0 ϖ hϖm e he r := by
    rw [PowerSeries.X_dvd_iff, constantCoeff_branchRed_eq, hr1, map_zero]

  have h0dvd : PowerSeries.X ^ (m + 1) ∣
      ∑ i : Fin (m + 1), PowerSeries.C (residue W (c i)) * PowerSeries.X ^ (i : ℕ) := by
    rw [h0eq, pow_succ']; exact mul_dvd_mul hr0 hadvd
  have hc : ∀ i : Fin (m + 1), residue W (c i) = 0 := fun i => by
    have := (PowerSeries.X_pow_dvd_iff.mp h0dvd) (i : ℕ) i.2
    rwa [coeff_sum_C_mul_X_pow] at this
  exact ⟨fun i => (residue_eq_zero_iff_dvd ϖ hϖ _).mp (hc i), fun j => (residue_eq_zero_iff_dvd ϖ hϖ _).mp (hd j)⟩

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

namespace P1Branch

open AnnulusNF

variable {W : Type u} [CommRing W]

theorem quotient_mk_const_mul (π : W) (J : Ideal (UVCrossingModel W π)) (w : W) (z : UVCrossingModel W π) :
    Ideal.Quotient.mk J (const π w * z) = w • Ideal.Quotient.mk J z := by
  rw [← algebraMap_eq_const, ← Algebra.smul_def, ← Ideal.Quotient.mkₐ_eq_mk W, map_smul]

theorem const_one (π : W) : const π 1 = 1 := by
  rw [← constHom_apply, map_one]

variable [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

theorem span_monomials_eq_top (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e))
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (m n : ℕ) (hm : IsUnit (PowerSeries.coeff m ab.1)) (hm' : ∀ i < m, ¬ IsUnit (PowerSeries.coeff i ab.1))
    (hn1 : 1 ≤ n) (hn : IsUnit (PowerSeries.coeff n ab.2)) (hn' : ∀ j < n, ¬ IsUnit (PowerSeries.coeff j ab.2))
    (h0 : ¬ IsUnit (PowerSeries.constantCoeff ab.1)) :
    Submodule.span W
      (Set.range (fun i : Fin (m + 1) => Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (U (ϖ ^ e) ^ (i : ℕ))) ∪
       Set.range (fun j : Fin (n - 1) => Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (V (ϖ ^ e) ^ ((j : ℕ) + 1)))) = ⊤ := by
  classical
  haveI : IsAdicComplete (Ideal.span {ϖ}) W :=
    (Irreducible.maximalIdeal_eq hϖ) ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)

  obtain ⟨hUJ, hVJ, hUVJ, c, hc, hcJ⟩ :=
    relations_quotient_span_pair ϖ hϖ e he x ab hb habx m n hm hm' hn1 hn hn' h0
  obtain ⟨cu, rfl⟩ := hc

  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := by
    rcases m with _ | m
    · exact absurd (by simpa using hm) h0
    · exact ⟨m, rfl⟩
  rw [Submodule.eq_top_iff']
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨⟨a', b'⟩, hb', rfl⟩ := exists_normalForm ϖ e he z

  generalize hS : Submodule.span W
      (Set.range (fun i : Fin (m + 1 + 1) => Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (U (ϖ ^ e) ^ (i : ℕ))) ∪
       Set.range (fun j : Fin (n - 1) => Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (V (ϖ ^ e) ^ ((j : ℕ) + 1)))) = S
  have hUmem : ∀ i < m + 1 + 1, Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (U (ϖ ^ e) ^ i) ∈ S := by
    intro i hi; rw [← hS]; exact Submodule.subset_span (Or.inl ⟨⟨i, hi⟩, rfl⟩)
  have hVmem : ∀ j, 1 ≤ j → j < n → Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (V (ϖ ^ e) ^ j) ∈ S := by
    intro j hj1 hjn; rw [← hS]
    refine Submodule.subset_span (Or.inr ⟨⟨j - 1, by omega⟩, ?_⟩)
    simp only [Nat.sub_add_cancel hj1]
  have hsm : ∀ (w : W) (z : UVCrossingModel W (ϖ ^ e)), Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) z ∈ S →
      Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (const (ϖ ^ e) w * z) ∈ S := by
    intro w z hz; rw [quotient_mk_const_mul]; exact S.smul_mem w hz
  have hJmem : ∀ z ∈ Ideal.span {x, const (ϖ ^ e) ϖ}, Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) z ∈ S := by
    intro z hz; rw [Ideal.Quotient.eq_zero_iff_mem.2 hz]; exact S.zero_mem
  simp only
  rw [RingHom.map_add, RingHom.map_add]
  refine S.add_mem ?_ ?_
  ·
    have hU : mk (ϖ ^ e) (inU a') = (∑ i ∈ Finset.range (m + 1 + 1), const (ϖ ^ e) (PowerSeries.coeff i a') * U (ϖ ^ e) ^ i) +
        U (ϖ ^ e) ^ (m + 1 + 1) * mk (ϖ ^ e) (inU (shift^[m + 1 + 1] a')) := by
      rw [inU_eq_sum_add_X_pow_mul a' (m + 1 + 1)]
      simp only [map_add, map_sum, map_mul, map_pow, mk_C, mk_X_zero]
    have hqs := map_sum (Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}))
      (fun i => const (ϖ ^ e) (PowerSeries.coeff i a') * U (ϖ ^ e) ^ i) (Finset.range (m + 1 + 1))
    rw [hU, RingHom.map_add, hqs]
    refine S.add_mem (S.sum_mem fun i hi => hsm _ _ (hUmem i (Finset.mem_range.1 hi))) ?_
    exact hJmem _ (Ideal.mul_mem_right _ _ hUJ)
  ·
    have hV : mk (ϖ ^ e) (inV b') = (∑ j ∈ Finset.range n, const (ϖ ^ e) (PowerSeries.coeff j b') * V (ϖ ^ e) ^ j) +
        V (ϖ ^ e) ^ n * mk (ϖ ^ e) (inV (shift^[n] b')) := by
      rw [inV_eq_sum_add_X_pow_mul b' n]
      simp only [map_add, map_sum, map_mul, map_pow, mk_C, mk_X_one]
    have hqs := map_sum (Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}))
      (fun j => const (ϖ ^ e) (PowerSeries.coeff j b') * V (ϖ ^ e) ^ j) (Finset.range n)
    rw [hV, RingHom.map_add, hqs]
    refine S.add_mem (S.sum_mem fun j hj => hsm _ _ ?_) ?_
    · rcases Nat.eq_zero_or_pos j with hj0 | hj1
      · rw [hj0, pow_zero, ← pow_zero (U (ϖ ^ e))]; exact hUmem 0 (by omega)
      · exact hVmem j hj1 (Finset.mem_range.1 hj)
    ·
      have hβ : mk (ϖ ^ e) (inV (shift^[n] b')) =
          const (ϖ ^ e) (PowerSeries.coeff n b') + V (ϖ ^ e) * mk (ϖ ^ e) (inV (shift^[n + 1] b')) := by
        rw [inV_eq_C_add_X_mul (shift^[n] b'), constantCoeff_shift_iterate, ← Function.iterate_succ_apply' shift n,
          map_add, map_mul, mk_C, mk_X_one]
      have hcc : const (ϖ ^ e) (↑cu⁻¹ : W) * const (ϖ ^ e) (↑cu : W) = 1 := by
        rw [← const_mul, Units.inv_mul, const_one]
      have hdiff : V (ϖ ^ e) ^ n * mk (ϖ ^ e) (inV (shift^[n] b')) -
          const (ϖ ^ e) (↑cu⁻¹ * PowerSeries.coeff n b') * U (ϖ ^ e) ^ (m + 1) ∈ Ideal.span {x, const (ϖ ^ e) ϖ} := by
        have hrw : V (ϖ ^ e) ^ n * mk (ϖ ^ e) (inV (shift^[n] b')) -
            const (ϖ ^ e) (↑cu⁻¹ * PowerSeries.coeff n b') * U (ϖ ^ e) ^ (m + 1) =
            (-(const (ϖ ^ e) (↑cu⁻¹ : W) * mk (ϖ ^ e) (inV (shift^[n] b')))) *
                (U (ϖ ^ e) ^ (m + 1) - const (ϖ ^ e) ↑cu * V (ϖ ^ e) ^ n) +
              (const (ϖ ^ e) (↑cu⁻¹ : W) * U (ϖ ^ e) ^ m * mk (ϖ ^ e) (inV (shift^[n + 1] b'))) *
                (U (ϖ ^ e) * V (ϖ ^ e)) := by
          rw [const_mul]
          linear_combination (-(V (ϖ ^ e) ^ n * mk (ϖ ^ e) (inV (shift^[n] b')))) * hcc +
            const (ϖ ^ e) (↑cu⁻¹ : W) * U (ϖ ^ e) ^ (m + 1) * hβ
        rw [hrw]
        exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hcJ) (Ideal.mul_mem_left _ _ hUVJ)
      rw [Ideal.Quotient.eq.2 hdiff]
      exact hsm _ _ (hUmem (m + 1) (by omega))

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

namespace P1Branch
p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

local notation "addv" => (IsDiscreteValuationRing.addVal W : W → ℕ∞)

theorem addVal_ne_zero_of_not_isUnit {c : W} (h : ¬ IsUnit c) : 1 ≤ IsDiscreteValuationRing.addVal W c := by
  rw [ENat.one_le_iff_ne_zero]
  exact fun h0 => h (IsDiscreteValuationRing.addVal_eq_zero_iff.mp h0)

theorem sInf_dominantIndices_zero_eq_of_good (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (m : ℕ) (hm : IsUnit (PowerSeries.coeff m ab.1)) (hm' : ∀ i < m, ¬ IsUnit (PowerSeries.coeff i ab.1)) :
    sInf (dominantIndices addv e 0 ab) = m := by
  have hv0 : (addv) 0 = ⊤ := AddValuation.map_zero _

  have hm0 : termOrder addv e 0 ab (m : ℤ) = 0 := by
    rw [termOrder_natCast, mul_zero, Nat.cast_zero, add_zero]
    exact IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hm
  have hinf : (⨅ n : ℤ, termOrder addv e 0 ab n) = 0 :=
    le_antisymm (hm0 ▸ iInf_le _ (m : ℤ)) bot_le
  apply IsLeast.csInf_eq
  constructor
  · rw [mem_dominantIndices_iff _ hv0 _ _ ab hb, hinf, hm0]
  · intro n hn
    rw [mem_dominantIndices_iff _ hv0 _ _ ab hb, hinf] at hn
    cases n with
    | ofNat i =>
      rw [Int.ofNat_eq_natCast, termOrder_natCast, mul_zero, Nat.cast_zero, add_zero] at hn
      by_contra hlt
      push Not at hlt
      rw [Int.ofNat_eq_natCast] at hlt
      have hi : i < m := by exact_mod_cast hlt
      have := addVal_ne_zero_of_not_isUnit (hm' i hi)
      rw [hn] at this
      exact absurd this (by simp)
    | negSucc j =>
      exfalso
      rw [termOrder_negSucc, Nat.sub_zero] at hn
      have : (((j + 1) * e : ℕ) : ℕ∞) ≤ 0 := by rw [← hn]; exact le_add_self
      have h2 : (j + 1) * e = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp this
      have : 1 ≤ (j + 1) * e := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      omega

theorem sSup_dominantIndices_top_eq_of_good (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (n : ℕ) (hn : IsUnit (PowerSeries.coeff n ab.2) ∨ (n = 0 ∧ IsUnit (PowerSeries.constantCoeff ab.1)))
    (hn' : ∀ j < n, ¬ IsUnit (PowerSeries.coeff j ab.2)) (h0 : n ≠ 0 → ¬ IsUnit (PowerSeries.constantCoeff ab.1)) :
    sSup (dominantIndices addv e e ab) = -(n : ℤ) := by
  have hv0 : (addv) 0 = ⊤ := AddValuation.map_zero _

  have hwit : termOrder addv e e ab (-(n : ℤ)) = 0 := by
    rcases hn with hbn | ⟨rfl, ha0⟩
    · have hn0 : n ≠ 0 := by
        rintro rfl
        rw [PowerSeries.coeff_zero_eq_constantCoeff, hb] at hbn
        exact not_isUnit_zero hbn
      obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := Nat.exists_eq_succ_of_ne_zero hn0
      rw [show (-((j + 1 : ℕ) : ℤ)) = Int.negSucc j from rfl, termOrder_negSucc, Nat.sub_self, mul_zero, Nat.cast_zero,
        add_zero]
      exact IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hbn
    · rw [Nat.cast_zero, neg_zero, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, termOrder_natCast, zero_mul, Nat.cast_zero,
        add_zero, PowerSeries.coeff_zero_eq_constantCoeff]
      exact IsDiscreteValuationRing.addVal_eq_zero_iff.mpr ha0
  have hinf : (⨅ k : ℤ, termOrder addv e e ab k) = 0 :=
    le_antisymm (hwit ▸ iInf_le _ (-(n : ℤ))) bot_le
  apply IsGreatest.csSup_eq
  constructor
  · rw [mem_dominantIndices_iff _ hv0 _ _ ab hb, hinf, hwit]
  · intro k hk
    rw [mem_dominantIndices_iff _ hv0 _ _ ab hb, hinf] at hk
    cases k with
    | ofNat i =>
      rw [Int.ofNat_eq_natCast, termOrder_natCast] at hk

      have hie : ((i * e : ℕ) : ℕ∞) ≤ 0 := by rw [← hk]; exact le_add_self
      have hie0 : i * e = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hie
      have hi : i = 0 := by rcases Nat.mul_eq_zero.mp hie0 with h | h; exact h; omega
      subst hi
      rw [zero_mul, Nat.cast_zero, add_zero, PowerSeries.coeff_zero_eq_constantCoeff] at hk
      have ha0 : IsUnit (PowerSeries.constantCoeff ab.1) := IsDiscreteValuationRing.addVal_eq_zero_iff.mp hk
      have : n = 0 := by by_contra hne; exact h0 hne ha0
      subst this
      simp
    | negSucc j =>
      rw [termOrder_negSucc, Nat.sub_self, mul_zero, Nat.cast_zero, add_zero] at hk
      have hbj : IsUnit (PowerSeries.coeff (j + 1) ab.2) := IsDiscreteValuationRing.addVal_eq_zero_iff.mp hk
      have : ¬ (j + 1 < n) := fun hlt => hn' _ hlt hbj
      rw [Int.negSucc_eq]
      omega

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

namespace P1Branch

open AnnulusNF

section generic

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem length_quot_span_uniformizer (ϖ : W) (hϖ : Irreducible ϖ) :
    Module.length W (W ⧸ (Ideal.span {ϖ} : Ideal W)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]
  refine ⟨Ideal.span {ϖ}, ?_, ⟨LinearEquiv.refl W _⟩⟩
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  exact IsLocalRing.maximalIdeal.isMaximal W

theorem length_eq_card_of_span_eq_top (ϖ : W) (hϖ : Irreducible ϖ) {A : Type*} [AddCommGroup A] [Module W A]
    {ι : Type*} [Fintype ι] (g : ι → A) (hspan : Submodule.span W (Set.range g) = ⊤)
    (hindep : ∀ f : ι → W, ∑ k, f k • g k = 0 → ∀ k, ϖ ∣ f k) (htors : ∀ a : A, ϖ • a = 0) :
    Module.length W A = Fintype.card ι := by
  classical
  let φ : (ι → W) →ₗ[W] A := ∑ k : ι, (LinearMap.proj k).smulRight (g k)
  have hφ : ∀ f, φ f = ∑ k, f k • g k := fun f => by
    simp only [φ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨Pi.single k 1, ?_⟩
    rw [hφ, Finset.sum_eq_single k (fun k' _ hk' => by rw [Pi.single_eq_of_ne hk', zero_smul])
      (fun h => absurd (Finset.mem_univ k) h), Pi.single_eq_same, one_smul]
  have hker : LinearMap.ker φ = Submodule.pi Set.univ (fun _ : ι => (Ideal.span {ϖ} : Ideal W)) := by
    ext f
    rw [LinearMap.mem_ker, Submodule.mem_pi, hφ]
    constructor
    · intro h k _
      exact Ideal.mem_span_singleton.2 (hindep f h k)
    · intro h
      refine Finset.sum_eq_zero fun k _ => ?_
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (h k (Set.mem_univ k))
      rw [hc, mul_smul]
      exact htors _
  let E : A ≃ₗ[W] (ι → W ⧸ (Ideal.span {ϖ} : Ideal W)) :=
    (LinearMap.quotKerEquivOfSurjective φ hsurj).symm ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ hker ≪≫ₗ Submodule.quotientPi _)
  rw [E.length_eq, Module.length_pi]
  simp [length_quot_span_uniformizer ϖ hϖ]

end generic
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

variable {W : Type u} [CommRing W]

theorem isUnit_mk_normalForm_of_isUnit (π : W) (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0)
    (ha : IsUnit (PowerSeries.constantCoeff a)) : IsUnit (mk π (inU a + inV b)) := by
  refine IsUnit.map _ (MvPowerSeries.isUnit_iff_constantCoeff.mpr ?_)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_add, coeff_zero_inU, coeff_zero_inV, hb, add_zero]
  exact ha

variable [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

theorem length_quotient_span_pair_of_good (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (hgood0 : ∃ i, IsUnit (PowerSeries.coeff i ab.1))
    (hgoodE : IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2)) :
    Module.length W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x, const (ϖ ^ e) ϖ}) =
      ((sInf (dominantIndices (IsDiscreteValuationRing.addVal W : W → ℕ∞) e 0 ab) -
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W : W → ℕ∞) e e ab)).toNat : ℕ∞) := by
  classical

  have hm : IsUnit (PowerSeries.coeff (Nat.find hgood0) ab.1) := Nat.find_spec hgood0
  have hm' : ∀ i < Nat.find hgood0, ¬ IsUnit (PowerSeries.coeff i ab.1) := fun i hi => Nat.find_min hgood0 hi
  rw [sInf_dominantIndices_zero_eq_of_good ϖ hϖ e he ab hb (Nat.find hgood0) hm hm']
  by_cases h0 : IsUnit (PowerSeries.constantCoeff ab.1)
  ·
    have hm0 : Nat.find hgood0 = 0 :=
      (Nat.find_eq_zero hgood0).mpr (by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply])
    rw [sSup_dominantIndices_top_eq_of_good ϖ hϖ e he ab hb 0 (Or.inr ⟨rfl, h0⟩) (fun j hj => absurd hj (Nat.not_lt_zero j))
      (fun h => absurd rfl h), hm0]
    have hxu : IsUnit x := habx ▸ isUnit_mk_normalForm_of_isUnit (ϖ ^ e) ab.1 ab.2 hb h0
    have htop : Ideal.span {x, const (ϖ ^ e) ϖ} = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) hxu
    haveI : Subsingleton (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x, const (ϖ ^ e) ϖ}) :=
      Ideal.Quotient.subsingleton_iff.mpr htop
    rw [Module.length_eq_zero_iff.mpr ‹_›]
    simp
  ·
    obtain ⟨j, -, hju⟩ := hgoodE.resolve_left h0
    have hex : ∃ j, IsUnit (PowerSeries.coeff j ab.2) := ⟨j, hju⟩
    have hn : IsUnit (PowerSeries.coeff (Nat.find hex) ab.2) := Nat.find_spec hex
    have hn' : ∀ j < Nat.find hex, ¬ IsUnit (PowerSeries.coeff j ab.2) := fun j hj => Nat.find_min hex hj
    have hn1 : 1 ≤ Nat.find hex := by
      rw [Nat.one_le_iff_ne_zero, Ne, Nat.find_eq_zero hex, PowerSeries.coeff_zero_eq_constantCoeff_apply, hb]
      exact not_isUnit_zero
    rw [sSup_dominantIndices_top_eq_of_good ϖ hϖ e he ab hb (Nat.find hex) (Or.inl hn) hn' (fun _ => h0)]

    have hspan := span_monomials_eq_top ϖ hϖ e he x ab hb habx _ _ hm hm' hn1 hn hn' h0
    rw [← Set.Sum.elim_range] at hspan
    have hindep : ∀ f : Fin (Nat.find hgood0 + 1) ⊕ Fin (Nat.find hex - 1) → W,
        ∑ k, f k • Sum.elim
          (fun i : Fin (Nat.find hgood0 + 1) => Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (U (ϖ ^ e) ^ (i : ℕ)))
          (fun j : Fin (Nat.find hex - 1) => Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (V (ϖ ^ e) ^ ((j : ℕ) + 1)))
          k = 0 → ∀ k, ϖ ∣ f k := by
      intro f hf
      have hsum : ∑ k, f k • Sum.elim
          (fun i : Fin (Nat.find hgood0 + 1) => Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (U (ϖ ^ e) ^ (i : ℕ)))
          (fun j : Fin (Nat.find hex - 1) => Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ}) (V (ϖ ^ e) ^ ((j : ℕ) + 1)))
          k = Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ})
            ((∑ i, const (ϖ ^ e) (f (Sum.inl i)) * U (ϖ ^ e) ^ (i : ℕ)) +
              (∑ j, const (ϖ ^ e) (f (Sum.inr j)) * V (ϖ ^ e) ^ ((j : ℕ) + 1))) := by
        rw [Fintype.sum_sum_type, RingHom.map_add,
          map_sum (Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ})) _ Finset.univ,
          map_sum (Ideal.Quotient.mk (Ideal.span {x, const (ϖ ^ e) ϖ})) _ Finset.univ]
        simp only [Sum.elim_inl, Sum.elim_inr]
        congr 1 <;> refine Finset.sum_congr rfl fun k _ => ?_ <;> exact (quotient_mk_const_mul _ _ _ _).symm
      rw [hsum] at hf
      have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hf
      obtain ⟨hc, hd⟩ := coeffs_mem_of_combination_mem ϖ hϖ e he x ab hb habx _ _ hm hm' hn1 hn hn' h0
        (fun i => f (Sum.inl i)) (fun j => f (Sum.inr j)) hmem
      rintro (i | j)
      · exact hc i
      · exact hd j
    have htors : ∀ a : UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x, const (ϖ ^ e) ϖ}, ϖ • a = 0 := by
      intro a
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [← quotient_mk_const_mul]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
    rw [length_eq_card_of_span_eq_top ϖ hϖ _ hspan hindep htors, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    congr 1
    omega

end P1Branch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

namespace P1Arch

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"
open scoped TensorProduct

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

theorem noZeroSMulDivisors_of_isSMulRegular (ϖ : W) (hϖ : Irreducible ϖ)
    (M : Type u) [AddCommGroup M] [Module W M] (hreg : IsSMulRegular M ϖ) : NoZeroSMulDivisors W M := by
  refine ⟨fun {c m} h => ?_⟩
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have h1 : ϖ ^ n • m = 0 := by
    have := congrArg (fun z => (↑u⁻¹ : W) • z) h
    rw [smul_zero, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
    exact this
  have h2 : ϖ ^ n • m = ϖ ^ n • (0 : M) := by rw [h1, smul_zero]
  exact (hreg.pow n) h2

theorem length_quotient_uniformizer (ϖ : W) (hϖ : Irreducible ϖ) :
    Module.length W (W ⧸ (Ideal.span {ϖ} : Ideal W)) = 1 := by
  rw [Module.length_eq_one_iff, isSimpleModule_iff_quot_maximal]
  refine ⟨Ideal.span {ϖ}, ?_, ⟨LinearEquiv.refl W _⟩⟩
  rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
  exact IsLocalRing.maximalIdeal.isMaximal W

theorem free_and_finrank_of_finite_of_isSMulRegular (ϖ : W) (hϖ : Irreducible ϖ)
    (M : Type u) [AddCommGroup M] [Module W M] [Module.Finite W M] (hreg : IsSMulRegular M ϖ) :
    Module.Free W M ∧
      (Module.finrank W M : ℕ∞) = Module.length W (M ⧸ ((Ideal.span {ϖ} : Ideal W) • (⊤ : Submodule W M))) := by
  classical
  haveI := noZeroSMulDivisors_of_isSMulRegular ϖ hϖ M hreg
  haveI : Module.Free W M := Module.free_of_finite_type_torsion_free'
  refine ⟨inferInstance, ?_⟩
  set I : Ideal W := Ideal.span {ϖ} with hI
  set r := Module.finrank W M with hr

  let b := Module.finBasis W M
  let e1 : (M ⧸ (I • (⊤ : Submodule W M))) ≃ₗ[W] TensorProduct W (W ⧸ I) M :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm
  let e2 : TensorProduct W (W ⧸ I) M ≃ₗ[W] TensorProduct W (W ⧸ I) (Fin r → W) :=
    TensorProduct.congr (LinearEquiv.refl W _) b.equivFun
  let e3 : TensorProduct W (W ⧸ I) (Fin r → W) ≃ₗ[W] (Fin r → W ⧸ I) :=
    TensorProduct.piScalarRight W W (W ⧸ I) (Fin r)
  rw [(e1.trans (e2.trans e3)).length_eq, Module.length_pi, length_quotient_uniformizer ϖ hϖ, mul_one]
  simp [hr]

theorem finrank_eq_length_tensor_of_finite_of_isSMulRegular (ϖ : W) (hϖ : Irreducible ϖ)
    (M : Type u) [AddCommGroup M] [Module W M] [Module.Finite W M] (hreg : IsSMulRegular M ϖ) :
    (Module.finrank W M : ℕ∞) = Module.length W (TensorProduct W (W ⧸ (Ideal.span {ϖ} : Ideal W)) M) := by
  rw [(free_and_finrank_of_finite_of_isSMulRegular ϖ hϖ M hreg).2,
    (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {ϖ} : Ideal W)).length_eq]

omit [IsDomain W] [IsDiscreteValuationRing W] in

theorem length_tensor_quot_eq (B : Type u) [CommRing B] [Algebra W B] (I : Ideal W) :
    Module.length W (TensorProduct W (W ⧸ I) B) = Module.length W (B ⧸ I.map (algebraMap W B)) :=
  ((TensorProduct.comm W (W ⧸ I) B).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toLinearEquiv.restrictScalars W)).length_eq

omit [IsDomain W] [IsDiscreteValuationRing W] in

theorem length_quot_quot_eq (R : Type u) [CommRing R] [Algebra W R] (J : Ideal R) (I : Ideal W) :
    Module.length W ((R ⧸ J) ⧸ I.map (algebraMap W (R ⧸ J))) =
      Module.length W (R ⧸ (J ⊔ I.map (algebraMap W R))) := by
  have h1 : (I.map (algebraMap W R)).map (Ideal.Quotient.mkₐ W J) = (I.map (algebraMap W R)).map (Ideal.Quotient.mk J) := by
    simp only [Ideal.map, Ideal.Quotient.mkₐ_eq_mk]
  have hmap : I.map (algebraMap W (R ⧸ J)) = (I.map (algebraMap W R)).map (Ideal.Quotient.mkₐ W J) := by
    rw [h1, Ideal.map_map]
    congr 1
  exact ((Ideal.quotientEquivAlgOfEq W hmap).toLinearEquiv.trans
    (DoubleQuot.quotQuotEquivQuotSupₐ W J (I.map (algebraMap W R))).toLinearEquiv).length_eq

variable [IsAdicComplete (maximalIdeal W) W]

theorem moduleFinite_quotient_of_isSMulRegular (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (hϖreg : IsSMulRegular (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) ϖ) :
    Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) := by
  classical
  obtain ⟨hdom, hloc, -⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ e he
  haveI := hdom
  haveI := hloc
  haveI : IsNoetherianRing (UVCrossingModel W (ϖ ^ e)) := UVCrossingModel.isNoetherianRing (ϖ ^ e)
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  haveI : IsPrecomplete (Ideal.span {ϖ ^ e}) W := isPrecomplete_span_pow ϖ e he

  have hreg : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (ϖ ^ e)) ∈
      nonZeroDivisors (MvPowerSeries (Fin 2) W) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    have h0 := congrArg MvPowerSeries.constantCoeff h
    simp only [map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, map_zero,
      mul_zero, zero_sub, neg_eq_zero] at h0
    exact pow_ne_zero e hϖ.ne_zero h0
  have hsep : ∀ y : UVCrossingModel W (ϖ ^ e), (∀ B : ℕ, y ∈ Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ^ B) → y = 0 := by
    intro y hy
    have hne : Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ≠ ⊤ := by
      apply Ideal.span_singleton_ne_top
      intro hu
      exact hϖ.1 ((isUnit_pow_iff (by omega)).mp (isUnit_of_isUnit_const_self _ hu))
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
    have hmem : y ∈ (⨅ i : ℕ, Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ^ i) := Ideal.mem_iInf.mpr hy
    rw [hbot] at hmem
    exact Ideal.mem_bot.mp hmem
  have hrange := ModularCurve.UVCrossingModel.range_chartHom_eq_fixedSubring (π := ϖ ^ e) hreg hsep

  have hn_fixed : x * crossingSwap (ϖ ^ e) x ∈ fixedSubring (ϖ ^ e) := by
    rw [mem_fixedSubring_iff, map_mul, crossingSwap_crossingSwap, mul_comm]
  have hn_range : x * crossingSwap (ϖ ^ e) x ∈ (chartHom (ϖ ^ e)).range := hrange ▸ hn_fixed
  obtain ⟨n, hn⟩ := RingHom.mem_range.mp hn_range
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn
    exact mul_ne_zero hx ((RingEquiv.map_ne_zero_iff (crossingSwap (ϖ ^ e))).mpr hx) hn.symm

  obtain ⟨m, n', hn'u, hnn'⟩ := exists_eq_mul_C_pow_of_ne_zero ϖ hϖ n hn0
  haveI : Module.Finite W (PowerSeries W ⧸ Ideal.span {n'}) := moduleFinite_quotient_of_isUnit_coeff n' hn'u

  let χ : PowerSeries W →ₐ[W] UVCrossingModel W (ϖ ^ e) := AlgHom.mk (chartHom (ϖ ^ e)) (fun w => by
    change chartHom (ϖ ^ e) (algebraMap W (PowerSeries W) w) = algebraMap W _ w
    rw [algebraMap_powerSeries_apply, ModularCurve.UVCrossingModel.chartHom_C, algebraMap_eq_const])

  have hn'x : chartHom (ϖ ^ e) n' ∈ Ideal.span {x} := by
    have hsm : (ϖ ^ m) • chartHom (ϖ ^ e) n' = chartHom (ϖ ^ e) n := by
      change (ϖ ^ m) • χ n' = χ n
      rw [← map_smul, PowerSeries.smul_eq_C_mul, mul_comm, ← hnn']
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hpow : (ϖ ^ m) • Ideal.Quotient.mk (Ideal.span {x}) (chartHom (ϖ ^ e) n') =
        (ϖ ^ m) • (0 : UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) := by
      rw [smul_zero, ← Ideal.Quotient.mkₐ_eq_mk W, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
        hsm, hn]
      exact Ideal.mem_span_singleton'.mpr ⟨crossingSwap (ϖ ^ e) x, by ring⟩
    exact (hϖreg.pow m) hpow
  obtain ⟨cx, hcx⟩ := Ideal.mem_span_singleton'.mp hn'x
  let ψ : UVCrossingModel W (ϖ ^ e) → (PowerSeries W →ₗ[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) :=
    fun r₀ => (Ideal.Quotient.mkₐ W (Ideal.span {x})).toLinearMap ∘ₗ (LinearMap.mulRight W r₀) ∘ₗ χ.toLinearMap
  have hψ : ∀ r₀ f, ψ r₀ f = Ideal.Quotient.mk (Ideal.span {x}) (chartHom (ϖ ^ e) f * r₀) := fun _ _ => rfl
  have hker : ∀ r₀, (Ideal.span {n'}).restrictScalars W ≤ LinearMap.ker (ψ r₀) := by
    intro r₀ z hz
    rw [Submodule.restrictScalars_mem] at hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [LinearMap.mem_ker, hψ, (chartHom (ϖ ^ e)).map_mul, ← hcx, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.mpr ⟨chartHom (ϖ ^ e) c * cx * r₀, by ring⟩
  let P : Submodule W (PowerSeries W) := (Ideal.span {n'}).restrictScalars W
  let Φ : ((PowerSeries W ⧸ P) × (PowerSeries W ⧸ P)) →ₗ[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) :=
    (P.liftQ (ψ 1) (hker 1)).coprod (P.liftQ (ψ (U (ϖ ^ e))) (hker _))
  have hΦ : Function.Surjective Φ := by
    intro q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, ha, hb, rfl⟩ := ModularCurve.UVCrossingModel.exists_mem_fixedSubring_eq_add_mul_U (ϖ ^ e) r
    rw [← hrange] at ha hb
    obtain ⟨f, rfl⟩ := RingHom.mem_range.mp ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hb
    refine ⟨(Submodule.Quotient.mk f, Submodule.Quotient.mk g), ?_⟩
    rw [LinearMap.coprod_apply, Submodule.liftQ_apply, Submodule.liftQ_apply, hψ, hψ, ← map_add, mul_one]

  let eQ : (PowerSeries W ⧸ P) ≃ₗ[W] (PowerSeries W ⧸ Ideal.span {n'}) :=
    Submodule.Quotient.restrictScalarsEquiv W (Ideal.span {n'})
  haveI : Module.Finite W (PowerSeries W ⧸ P) := Module.Finite.equiv eQ.symm
  exact Module.Finite.of_surjective Φ hΦ

local notation "addv" => (IsDiscreteValuationRing.addVal W : W → ℕ∞)

private theorem _root_.P1Arch.length_quotient_span_pair_of_good (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (hgood0 : ∃ i, IsUnit (PowerSeries.coeff i ab.1))
    (hgoodE : IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2)) :
    Module.length W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x, const (ϖ ^ e) ϖ}) =
      ((sInf (dominantIndices addv e 0 ab) - sSup (dominantIndices addv e e ab)).toNat : ℕ∞) :=
  P1Branch.length_quotient_span_pair_of_good ϖ hϖ e he x hx ab hb habx hgood0 hgoodE

p2m_export "P1Arch" "length_quotient_span_pair_of_good"

theorem free_finite_finrank_quotient_of_good (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (hgood0 : ∃ i, IsUnit (PowerSeries.coeff i ab.1))
    (hgoodE : IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2)) :
    Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) ∧
    Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) ∧
    ((Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) : ℤ) =
      sInf (dominantIndices addv e 0 ab) - sSup (dominantIndices addv e e ab)) := by
  classical
  have hreg := P1Branch.isSMulRegular_quotient_of_good ϖ hϖ e he x hx ab hb habx hgood0 hgoodE
  haveI hfinM : Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) :=
    moduleFinite_quotient_of_isSMulRegular ϖ hϖ e he x hx hreg
  have hfree := (free_and_finrank_of_finite_of_isSMulRegular ϖ hϖ (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) hreg).1
  have hrankT := finrank_eq_length_tensor_of_finite_of_isSMulRegular ϖ hϖ (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) hreg
  refine ⟨hfree, hfinM, ?_⟩

  have G1 := length_tensor_quot_eq (W := W) (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) (Ideal.span {ϖ} : Ideal W)
  have G2 := length_quot_quot_eq (W := W) (UVCrossingModel W (ϖ ^ e)) (Ideal.span {x}) (Ideal.span {ϖ} : Ideal W)
  have hmap : (Ideal.span {ϖ} : Ideal W).map (algebraMap W (UVCrossingModel W (ϖ ^ e))) = Ideal.span {const (ϖ ^ e) ϖ} := by
    rw [Ideal.map_span, Set.image_singleton, algebraMap_eq_const]
  have hsup : Ideal.span {x} ⊔ Ideal.span {const (ϖ ^ e) ϖ} =
      (Ideal.span {x, const (ϖ ^ e) ϖ} : Ideal (UVCrossingModel W (ϖ ^ e))) := by
    rw [Ideal.span_insert]
  rw [hmap, hsup] at G2
  have hrank := hrankT.trans (G1.trans G2)
  rw [length_quotient_span_pair_of_good ϖ hϖ e he x hx ab hb habx hgood0 hgoodE] at hrank
  have hr : Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) =
      (sInf (dominantIndices addv e 0 ab) - sSup (dominantIndices addv e e ab)).toNat := by exact_mod_cast hrank

  have hx' : mk (ϖ ^ e) (inU ab.1 + inV ab.2) ≠ 0 := habx ▸ hx
  have hfin : ∀ s, (⨅ n, termOrder addv e s ab n) < ⊤ := fun s =>
    iInf_termOrder_lt_top addv (fun c hc => IsDiscreteValuationRing.addVal_eq_top_iff.mp hc) (ϖ ^ e) e s ab hb hx'
  have hnn := sSup_dominantIndices_le_sInf addv (AddValuation.map_zero _) e he ab hb hfin
  rw [hr, Int.toNat_of_nonneg (by omega)]

end P1Arch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

namespace P1Arch

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"
open scoped TensorProduct

variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

set_option synthInstance.maxHeartbeats 400000

theorem moduleFinite_quotient_of_mem_of_isSMulRegular (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0) (J : Ideal (UVCrossingModel W (ϖ ^ e))) (hxJ : x ∈ J)
    (hϖreg : IsSMulRegular (UVCrossingModel W (ϖ ^ e) ⧸ J) ϖ) :
    Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ J) := by
  classical
  obtain ⟨hdom, hloc, -⟩ :=
    ModularCurve.UVCrossingModel.isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete ϖ hϖ e he
  haveI := hdom
  haveI := hloc
  haveI : IsNoetherianRing (UVCrossingModel W (ϖ ^ e)) := UVCrossingModel.isNoetherianRing (ϖ ^ e)
  have hmax : maximalIdeal W = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W := hmax ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  haveI : IsPrecomplete (Ideal.span {ϖ ^ e}) W := isPrecomplete_span_pow ϖ e he

  have hreg : ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (ϖ ^ e)) ∈
      nonZeroDivisors (MvPowerSeries (Fin 2) W) := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    have h0 := congrArg MvPowerSeries.constantCoeff h
    simp only [map_sub, map_mul, MvPowerSeries.constantCoeff_X, MvPowerSeries.constantCoeff_C, map_zero,
      mul_zero, zero_sub, neg_eq_zero] at h0
    exact pow_ne_zero e hϖ.ne_zero h0
  have hsep : ∀ y : UVCrossingModel W (ϖ ^ e), (∀ B : ℕ, y ∈ Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ^ B) → y = 0 := by
    intro y hy
    have hne : Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ≠ ⊤ := by
      apply Ideal.span_singleton_ne_top
      intro hu
      exact hϖ.1 ((isUnit_pow_iff (by omega)).mp (isUnit_of_isUnit_const_self _ hu))
    have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing _ hne
    have hmem : y ∈ (⨅ i : ℕ, Ideal.span {const (ϖ ^ e) (ϖ ^ e)} ^ i) := Ideal.mem_iInf.mpr hy
    rw [hbot] at hmem
    exact Ideal.mem_bot.mp hmem
  have hrange := ModularCurve.UVCrossingModel.range_chartHom_eq_fixedSubring (π := ϖ ^ e) hreg hsep

  have hn_fixed : x * crossingSwap (ϖ ^ e) x ∈ fixedSubring (ϖ ^ e) := by
    rw [mem_fixedSubring_iff, map_mul, crossingSwap_crossingSwap, mul_comm]
  have hn_range : x * crossingSwap (ϖ ^ e) x ∈ (chartHom (ϖ ^ e)).range := hrange ▸ hn_fixed
  obtain ⟨n, hn⟩ := RingHom.mem_range.mp hn_range
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [map_zero] at hn
    exact mul_ne_zero hx ((RingEquiv.map_ne_zero_iff (crossingSwap (ϖ ^ e))).mpr hx) hn.symm

  obtain ⟨m, n', hn'u, hnn'⟩ := exists_eq_mul_C_pow_of_ne_zero ϖ hϖ n hn0
  haveI : Module.Finite W (PowerSeries W ⧸ Ideal.span {n'}) := moduleFinite_quotient_of_isUnit_coeff n' hn'u

  let χ : PowerSeries W →ₐ[W] UVCrossingModel W (ϖ ^ e) := AlgHom.mk (chartHom (ϖ ^ e)) (fun w => by
    change chartHom (ϖ ^ e) (algebraMap W (PowerSeries W) w) = algebraMap W _ w
    rw [algebraMap_powerSeries_apply, ModularCurve.UVCrossingModel.chartHom_C, algebraMap_eq_const])

  have hn'x : chartHom (ϖ ^ e) n' ∈ J := by
    have hsm : (ϖ ^ m) • chartHom (ϖ ^ e) n' = chartHom (ϖ ^ e) n := by
      change (ϖ ^ m) • χ n' = χ n
      rw [← map_smul, PowerSeries.smul_eq_C_mul, mul_comm, ← hnn']
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hpow : (ϖ ^ m) • Ideal.Quotient.mk J (chartHom (ϖ ^ e) n') =
        (ϖ ^ m) • (0 : UVCrossingModel W (ϖ ^ e) ⧸ J) := by
      rw [smul_zero, ← Ideal.Quotient.mkₐ_eq_mk W, ← map_smul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem,
        hsm, hn]
      exact J.mul_mem_right _ hxJ
    exact (hϖreg.pow m) hpow
  let ψ : UVCrossingModel W (ϖ ^ e) → (PowerSeries W →ₗ[W] (UVCrossingModel W (ϖ ^ e) ⧸ J)) :=
    fun r₀ => (Ideal.Quotient.mkₐ W (J)).toLinearMap ∘ₗ (LinearMap.mulRight W r₀) ∘ₗ χ.toLinearMap
  have hψ : ∀ r₀ f, ψ r₀ f = Ideal.Quotient.mk (J) (chartHom (ϖ ^ e) f * r₀) := fun _ _ => rfl
  have hker : ∀ r₀, (Ideal.span {n'}).restrictScalars W ≤ LinearMap.ker (ψ r₀) := by
    intro r₀ z hz
    rw [Submodule.restrictScalars_mem] at hz
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [LinearMap.mem_ker, hψ, (chartHom (ϖ ^ e)).map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact J.mul_mem_right _ (J.mul_mem_left _ hn'x)
  let P : Submodule W (PowerSeries W) := (Ideal.span {n'}).restrictScalars W
  let Φ : ((PowerSeries W ⧸ P) × (PowerSeries W ⧸ P)) →ₗ[W] (UVCrossingModel W (ϖ ^ e) ⧸ J) :=
    (P.liftQ (ψ 1) (hker 1)).coprod (P.liftQ (ψ (U (ϖ ^ e))) (hker _))
  have hΦ : Function.Surjective Φ := by
    intro q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, ha, hb, rfl⟩ := ModularCurve.UVCrossingModel.exists_mem_fixedSubring_eq_add_mul_U (ϖ ^ e) r
    rw [← hrange] at ha hb
    obtain ⟨f, rfl⟩ := RingHom.mem_range.mp ha
    obtain ⟨g, rfl⟩ := RingHom.mem_range.mp hb
    refine ⟨(Submodule.Quotient.mk f, Submodule.Quotient.mk g), ?_⟩
    rw [LinearMap.coprod_apply, Submodule.liftQ_apply, Submodule.liftQ_apply, hψ, hψ, ← map_add, mul_one]

  let eQ : (PowerSeries W ⧸ P) ≃ₗ[W] (PowerSeries W ⧸ Ideal.span {n'}) :=
    Submodule.Quotient.restrictScalarsEquiv W (Ideal.span {n'})
  haveI : Module.Finite W (PowerSeries W ⧸ P) := Module.Finite.equiv eQ.symm
  exact Module.Finite.of_surjective Φ hΦ

theorem moduleFinite_quotient_of_isSMulRegular' (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (hϖreg : IsSMulRegular (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) ϖ) :
    Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) :=
  moduleFinite_quotient_of_mem_of_isSMulRegular ϖ hϖ e he x hx _ (Ideal.subset_span rfl) hϖreg

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in

theorem isSMulRegular_quotient_of_const_not_mem (ϖ : W) (e : ℕ) (P : Ideal (UVCrossingModel W (ϖ ^ e))) [P.IsPrime]
    (hPϖ : const (ϖ ^ e) ϖ ∉ P) : IsSMulRegular (UVCrossingModel W (ϖ ^ e) ⧸ P) ϖ := by
  intro p₁ p₂ hpq
  simp only at hpq
  obtain ⟨y₁, rfl⟩ := Ideal.Quotient.mk_surjective p₁
  obtain ⟨y₂, rfl⟩ := Ideal.Quotient.mk_surjective p₂
  rw [Ideal.Quotient.eq]
  have h' : Ideal.Quotient.mk P (const (ϖ ^ e) ϖ * (y₁ - y₂)) = 0 := by
    rw [← algebraMap_eq_const, map_mul, Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def, map_sub, smul_sub]
    exact sub_eq_zero.mpr hpq
  rw [Ideal.Quotient.eq_zero_iff_mem] at h'
  exact ((Ideal.IsPrime.mem_or_mem ‹P.IsPrime› h').resolve_left hPϖ)

theorem free_finite_quotient_prime (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0) (P : Ideal (UVCrossingModel W (ϖ ^ e))) [P.IsPrime]
    (hxP : x ∈ P) (hPϖ : const (ϖ ^ e) ϖ ∉ P) :
    Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ P) ∧ Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ P) := by
  have hreg := isSMulRegular_quotient_of_const_not_mem ϖ e P hPϖ
  haveI := moduleFinite_quotient_of_mem_of_isSMulRegular ϖ hϖ e he x hx P hxP hreg
  haveI := noZeroSMulDivisors_of_isSMulRegular ϖ hϖ (UVCrossingModel W (ϖ ^ e) ⧸ P) hreg
  have hTF : Module.IsTorsionFree W (UVCrossingModel W (ϖ ^ e) ⧸ P) :=
    ⟨fun r hr => smul_right_injective (UVCrossingModel W (ϖ ^ e) ⧸ P) (IsRegular.ne_zero hr)⟩
  exact ⟨inferInstance, @Module.free_of_finite_type_torsion_free' W _ (UVCrossingModel W (ϖ ^ e) ⧸ P) _ _ _ _ _ hTF⟩

end P1Arch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

universe v w

namespace P1Arch

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"
open scoped TensorProduct

theorem finrank_residueField_localization_eq_finrank_quotient_aux
    (K : Type u) [Field K] (A : Type v) [CommRing A] [Algebra K A] (𝔪 : Ideal A) [𝔪.IsMaximal] :
    Module.finrank K (ResidueField (Localization.AtPrime 𝔪)) = Module.finrank K (A ⧸ 𝔪) := by
  let ρ : A →+* ResidueField (Localization.AtPrime 𝔪) :=
    (residue (Localization.AtPrime 𝔪)).comp (algebraMap A (Localization.AtPrime 𝔪))
  have hρ : ∀ a ∈ 𝔪, ρ a = 0 := by
    intro a ha
    change residue _ (algebraMap A (Localization.AtPrime 𝔪) a) = 0
    rw [residue_eq_zero_iff]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a).mpr ha
  let ψ₀ : (A ⧸ 𝔪) →+* ResidueField (Localization.AtPrime 𝔪) := Ideal.Quotient.lift 𝔪 ρ hρ
  have hψmk : ∀ a : A, ψ₀ (Ideal.Quotient.mk _ a) = residue _ (algebraMap A (Localization.AtPrime 𝔪) a) :=
    fun a => rfl
  have hKL : ∀ k : K, algebraMap K (ResidueField (Localization.AtPrime 𝔪)) k =
      residue _ (algebraMap A (Localization.AtPrime 𝔪) (algebraMap K A k)) := by
    intro k
    rw [← IsScalarTower.algebraMap_apply K A (Localization.AtPrime 𝔪) k,
      IsScalarTower.algebraMap_apply K (Localization.AtPrime 𝔪) (ResidueField (Localization.AtPrime 𝔪)) k,
      ResidueField.algebraMap_eq]
  let ψ : (A ⧸ 𝔪) →ₗ[K] ResidueField (Localization.AtPrime 𝔪) :=
    { toFun := ψ₀
      map_add' := ψ₀.map_add
      map_smul' := by
        intro k x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def, hKL, ← hψmk, ← map_mul, IsScalarTower.algebraMap_apply K A (A ⧸ 𝔪) k,
          Ideal.Quotient.algebraMap_eq, ← map_mul] }
  have hψapply : ∀ x, ψ x = ψ₀ x := fun x => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [hψapply, hψmk, residue_eq_zero_iff,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪 a] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hz
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl l
    have hs0 : (Ideal.Quotient.mk 𝔪 (s : A)) ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact s.2
    obtain ⟨t, ht⟩ := Ideal.Quotient.exists_inv hs0
    obtain ⟨t', rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨Ideal.Quotient.mk _ a * Ideal.Quotient.mk _ t', ?_⟩
    have hsunit : residue _ (algebraMap A (Localization.AtPrime 𝔪) s) ≠ 0 := by
      rw [Ne, residue_eq_zero_iff, IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔪) 𝔪]
      exact s.2
    apply mul_right_cancel₀ hsunit
    dsimp only
    rw [hψapply]
    change ψ₀ _ * _ = residue _ (IsLocalization.mk' (Localization.AtPrime 𝔪) a s) *
      residue _ (algebraMap A (Localization.AtPrime 𝔪) s)
    have hts : Ideal.Quotient.mk 𝔪 t' * Ideal.Quotient.mk 𝔪 (s : A) = 1 := by
      rw [mul_comm]; exact ht
    rw [← map_mul (residue _), IsLocalization.mk'_spec, ← hψmk a, ← hψmk (s : A), ← map_mul ψ₀, mul_assoc,
      hts, mul_one]
  exact ((LinearEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).finrank_eq).symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem finrank_quotient_tensor_eq_finrank_quotient
    (W : Type u) [CommRing W] [IsDomain W] (B : Type u) [CommRing B] [Algebra W B]
    (𝔪 : Ideal ((FractionRing W) ⊗[W] B)) [𝔪.IsMaximal]
    [Module.Free W (B ⧸ 𝔪.comap (algebraMap B ((FractionRing W) ⊗[W] B)))] :
    Module.finrank (FractionRing W) (((FractionRing W) ⊗[W] B) ⧸ 𝔪) =
      Module.finrank W (B ⧸ 𝔪.comap (algebraMap B ((FractionRing W) ⊗[W] B))) := by
  set Q : Ideal B := 𝔪.comap (algebraMap B (FractionRing W ⊗[W] B)) with hQ
  have halg : ∀ b : B, algebraMap B (FractionRing W ⊗[W] B) b = (1 : FractionRing W) ⊗ₜ[W] b := fun b => rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (FractionRing W ⊗[W] B) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  have h𝔪 : 𝔪 = Q.map (algebraMap B (FractionRing W ⊗[W] B)) :=
    (IsLocalization.map_comap (Algebra.algebraMapSubmonoid B (nonZeroDivisors W)) (FractionRing W ⊗[W] B) 𝔪).symm
  let Q' : Submodule W B := Q.restrictScalars W
  let f : (FractionRing W) ⊗[W] Q' →ₗ[FractionRing W] (FractionRing W ⊗[W] B) := (Q'.subtype).baseChange (FractionRing W)
  let g : (FractionRing W ⊗[W] B) →ₗ[FractionRing W] (FractionRing W) ⊗[W] (B ⧸ Q') := (Q'.mkQ).baseChange (FractionRing W)
  have hftmul : ∀ (k : FractionRing W) (q : Q'), f (k ⊗ₜ q) = k ⊗ₜ (q : B) := fun k q => by
    simp only [f, LinearMap.baseChange_tmul, Submodule.subtype_apply]
  have hgsurj : Function.Surjective g := by
    change Function.Surjective ((Q'.mkQ).baseChange (FractionRing W))
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective Q')
  have hexact : Function.Exact f g := by
    change Function.Exact ((Q'.subtype).baseChange (FractionRing W)) ((Q'.mkQ).baseChange (FractionRing W))
    rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact (FractionRing W) (LinearMap.exact_subtype_mkQ Q') (Submodule.mkQ_surjective Q')
  have hrange : LinearMap.range f = 𝔪.restrictScalars (FractionRing W) := by
    apply le_antisymm
    · rintro _ ⟨z, rfl⟩
      induction z using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | tmul k q =>
        rw [hftmul, Submodule.restrictScalars_mem]
        have : (k ⊗ₜ[W] (q : B) : FractionRing W ⊗[W] B) =
            (k ⊗ₜ[W] (1 : B)) * algebraMap B (FractionRing W ⊗[W] B) q := by
          rw [halg, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        rw [this]
        exact 𝔪.mul_mem_left _ (Ideal.mem_comap.mp q.2)
      | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro x hx
      rw [Submodule.restrictScalars_mem, h𝔪] at hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · rintro _ ⟨q, hq, rfl⟩
        exact ⟨1 ⊗ₜ ⟨q, hq⟩, by rw [hftmul, halg]⟩
      · exact Submodule.zero_mem _
      · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
      · intro a y hymem hy
        obtain ⟨z, rfl⟩ := hy
        clear hymem
        rw [smul_eq_mul]
        induction a using TensorProduct.induction_on with
        | zero => rw [zero_mul]; exact Submodule.zero_mem _
        | tmul k b =>
          induction z using TensorProduct.induction_on with
          | zero => rw [map_zero, mul_zero]; exact Submodule.zero_mem _
          | tmul k' q =>
            refine ⟨(k * k') ⊗ₜ ⟨b * q, Q.mul_mem_left b q.2⟩, ?_⟩
            rw [hftmul, hftmul, Algebra.TensorProduct.tmul_mul_tmul]
          | add z₁ z₂ h₁ h₂ => rw [map_add, mul_add]; exact Submodule.add_mem _ h₁ h₂
        | add a₁ a₂ h₁ h₂ => rw [add_mul]; exact Submodule.add_mem _ h₁ h₂
  let e₁ : ((FractionRing W ⊗[W] B) ⧸ 𝔪) ≃ₗ[FractionRing W] ((FractionRing W ⊗[W] B) ⧸ 𝔪.restrictScalars (FractionRing W)) :=
    (Submodule.Quotient.restrictScalarsEquiv (FractionRing W) 𝔪).symm
  let e₂ : ((FractionRing W ⊗[W] B) ⧸ 𝔪.restrictScalars (FractionRing W)) ≃ₗ[FractionRing W]
      ((FractionRing W ⊗[W] B) ⧸ LinearMap.ker g) :=
    Submodule.quotEquivOfEq _ _ (by rw [← hrange, hexact.linearMap_ker_eq])
  let e₃ : ((FractionRing W ⊗[W] B) ⧸ LinearMap.ker g) ≃ₗ[FractionRing W] (FractionRing W) ⊗[W] (B ⧸ Q') :=
    g.quotKerEquivOfSurjective hgsurj
  let e₄ : (B ⧸ Q') ≃ₗ[W] (B ⧸ Q) := Submodule.Quotient.restrictScalarsEquiv W Q
  haveI : Module.Free W (B ⧸ Q') := Module.Free.of_equiv e₄.symm
  rw [(e₁.trans (e₂.trans e₃)).finrank_eq, Module.finrank_baseChange, e₄.finrank_eq]

theorem finrank_residueField_localization_eq_finrank_quotient
    (W : Type u) [CommRing W] [IsDomain W] (B : Type u) [CommRing B] [Algebra W B]
    [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] B)]
    (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] B))
    [Module.Free W (B ⧸ 𝔪.asIdeal.comap (algebraMap B ((FractionRing W) ⊗[W] B)))]
    [Module.Finite W (B ⧸ 𝔪.asIdeal.comap (algebraMap B ((FractionRing W) ⊗[W] B)))] :
    Module.finrank (FractionRing W) (ResidueField (Localization.AtPrime 𝔪.asIdeal)) =
      Module.finrank W (B ⧸ 𝔪.asIdeal.comap (algebraMap B ((FractionRing W) ⊗[W] B))) := by
  haveI : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal
  rw [finrank_residueField_localization_eq_finrank_quotient_aux (FractionRing W) _ 𝔪.asIdeal]
  exact finrank_quotient_tensor_eq_finrank_quotient W B 𝔪.asIdeal

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Inputs

open IsLocalRing

theorem finrank_eq_finrank_residueField_mul_length
    (K : Type u) (L : Type v) (M : Type w) [Field K] [CommRing L] [IsLocalRing L] [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M] [Module.Finite K M] :
    (Module.finrank K M : ℕ∞) = (Module.finrank K (IsLocalRing.ResidueField L) : ℕ∞) * Module.length L M := by

  suffices h : ∀ n : ℕ, ∀ (M : Type w) [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M]
      [Module.Finite K M], Module.finrank K M = n →
      (Module.finrank K M : ℕ∞) = (Module.finrank K (IsLocalRing.ResidueField L) : ℕ∞) * Module.length L M from
    h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ _ _ _ hn
  by_cases hM : Subsingleton M
  · rw [Module.finrank_zero_of_subsingleton, Module.length_eq_zero_iff.mpr hM, Nat.cast_zero, mul_zero]
  · have hnt : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM

    haveI : IsArtinian L M := isArtinian_of_tower K inferInstance
    haveI : IsNoetherian L M := isNoetherian_of_tower K inferInstance
    obtain ⟨S, hS⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule L M)).resolve_left top_ne_bot
    obtain ⟨hSatom, -⟩ := hS
    haveI hSsimple : IsSimpleModule L S := isSimpleModule_iff_isAtom.mpr hSatom

    obtain ⟨I, hImax, ⟨eS⟩⟩ := isSimpleModule_iff_quot_maximal.mp hSsimple
    have hI : I = maximalIdeal L := IsLocalRing.eq_maximalIdeal hImax
    subst hI
    have hfinS : Module.finrank K S = Module.finrank K (IsLocalRing.ResidueField L) :=
      (eS.restrictScalars K).finrank_eq

    haveI : Module.Finite K (M ⧸ S) :=
      Module.Finite.of_surjective (S.mkQ.restrictScalars K) (Submodule.mkQ_surjective S)
    have hdim : Module.finrank K M = Module.finrank K S + Module.finrank K (M ⧸ S) := by
      rw [← (Submodule.Quotient.restrictScalarsEquiv K S).finrank_eq, add_comm]
      exact (Submodule.finrank_quotient_add_finrank (S.restrictScalars K)).symm
    have hκpos : 0 < Module.finrank K (IsLocalRing.ResidueField L) := by
      rw [← hfinS]
      haveI : Nontrivial S := IsSimpleModule.nontrivial L S
      haveI : Module.Finite K S := Module.Finite.of_injective (S.subtype.restrictScalars K) (Submodule.injective_subtype S)
      exact Module.finrank_pos
    have hlt : Module.finrank K (M ⧸ S) < n := by omega
    have ihq := ih _ hlt (M ⧸ S) rfl

    have hlen : Module.length L M = 1 + Module.length L (M ⧸ S) := by
      rw [Module.length_eq_add_of_exact S.subtype S.mkQ (Submodule.injective_subtype S) (Submodule.mkQ_surjective S)
        (LinearMap.exact_subtype_mkQ S), Module.length_eq_one_iff.mpr hSsimple]
    rw [hdim, hfinS, Nat.cast_add, ihq, hlen, mul_add, mul_one]

theorem moduleFinite_localization_atPrime_of_moduleFinite
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] (m : MaximalSpectrum A) :
    Module.Finite K (Localization.AtPrime m.asIdeal) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact Module.Finite.of_surjective
    (IsScalarTower.toAlgHom K A (Localization.AtPrime m.asIdeal)).toLinearMap
    (IsArtinianRing.localization_surjective m.asIdeal.primeCompl _)

theorem finrank_eq_sum_finrank_localization_atPrime
    (K : Type u) (A : Type v) [Field K] [CommRing A] [Algebra K A] [Module.Finite K A] [Fintype (MaximalSpectrum A)] :
    Module.finrank K A = ∑ m : MaximalSpectrum A, Module.finrank K (Localization.AtPrime m.asIdeal) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : ∀ m : MaximalSpectrum A, Module.Finite K (Localization.AtPrime m.asIdeal) :=
    fun m => moduleFinite_localization_atPrime_of_moduleFinite K A m
  let e : A ≃ₗ[K] MaximalSpectrum.PiLocalization A :=
    (MaximalSpectrum.toPiLocalizationEquiv A).toLinearEquiv.restrictScalars K
  rw [e.finrank_eq]
  exact Module.finrank_pi_fintype K

theorem length_eq_of_orderIso {R : Type*} {R' : Type*} [Ring R] [Ring R'] {M : Type*} {M' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R' M'] (e : Submodule R M ≃o Submodule R' M') :
    Module.length R M = Module.length R' M' := by
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso e

theorem length_self_eq_of_ringEquiv {R : Type*} {R' : Type*} [CommRing R] [CommRing R'] (e : R ≃+* R') :
    Module.length R R = Module.length R' R' :=
  (length_eq_of_orderIso (Ideal.relIsoOfBijective e e.bijective)).symm

noncomputable def restrictScalarsOrderIsoOfSurjective (S T : Type*) [CommRing S] [CommRing T] [Algebra S T]
    (N : Type*) [AddCommGroup N] [Module T N] [Module S N] [IsScalarTower S T N]
    (h : Function.Surjective (algebraMap S T)) : Submodule T N ≃o Submodule S N where
  toFun p := p.restrictScalars S
  invFun p :=
    { carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' := fun t n hn => by
        obtain ⟨s, rfl⟩ := h t
        rw [algebraMap_smul]
        exact p.smul_mem s hn }
  left_inv p := by ext; rfl
  right_inv p := by ext; rfl
  map_rel_iff' := Iff.rfl

theorem length_eq_of_surjective_algebraMap (S T : Type*) [CommRing S] [CommRing T] [Algebra S T]
    (N : Type*) [AddCommGroup N] [Module T N] [Module S N] [IsScalarTower S T N]
    (h : Function.Surjective (algebraMap S T)) : Module.length S N = Module.length T N :=
  (length_eq_of_orderIso (restrictScalarsOrderIsoOfSurjective S T N h)).symm

theorem length_localization_atPrime_eq_of_isLocalization
    (B : Type u) [CommRing B] (S : Submonoid B) (A : Type v) [CommRing A] [Algebra B A] [IsLocalization S A]
    (𝔪 : Ideal A) [𝔪.IsPrime] :
    Module.length (Localization.AtPrime 𝔪) (Localization.AtPrime 𝔪) =
      Module.length (Localization.AtPrime (𝔪.comap (algebraMap B A))) (Localization.AtPrime (𝔪.comap (algebraMap B A))) := by
  haveI : IsLocalization.AtPrime (Localization.AtPrime 𝔪) (𝔪.comap (algebraMap B A)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization S (Localization.AtPrime 𝔪) 𝔪
  exact length_self_eq_of_ringEquiv
    (IsLocalization.algEquiv (𝔪.comap (algebraMap B A)).primeCompl (Localization.AtPrime 𝔪)
      (Localization.AtPrime (𝔪.comap (algebraMap B A)))).toRingEquiv

theorem length_localizedModule_quotient_eq_length_localization
    (R : Type u) [CommRing R] (I : Ideal R) (Q : Ideal (R ⧸ I)) [Q.IsPrime] :
    Module.length (Localization.AtPrime (Q.comap (Ideal.Quotient.mk I)))
        (LocalizedModule (Q.comap (Ideal.Quotient.mk I)).primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) := by
  set P : Ideal R := Q.comap (Ideal.Quotient.mk I) with hP

  have hS : Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl = Q.primeCompl := by
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hz
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨s, hz, rfl⟩

  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl) (Localization.AtPrime Q) := by
    rw [hS]; infer_instance
  haveI hloc : IsLocalizedModule P.primeCompl
      (IsScalarTower.toAlgHom R (R ⧸ I) (Localization.AtPrime Q)).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  let e₀ : LocalizedModule P.primeCompl (R ⧸ I) ≃ₗ[R] Localization.AtPrime Q :=
    IsLocalizedModule.iso P.primeCompl (IsScalarTower.toAlgHom R (R ⧸ I) (Localization.AtPrime Q)).toLinearMap

  let φ : Localization.AtPrime P →+* Localization.AtPrime Q :=
    Localization.localRingHom P Q (Ideal.Quotient.mk I) hP
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) := φ.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime P) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [RingHom.algebraMap_toAlgebra]
      change algebraMap (R ⧸ I) (Localization.AtPrime Q) (Ideal.Quotient.mk I r) = φ (algebraMap R _ r)
      rw [Localization.localRingHom_to_map])
  have hφ : Function.Surjective (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) := by
    intro z
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl z
    obtain ⟨a', ha'⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : R ⧸ I)
    have hs'P : s' ∈ P.primeCompl := by
      change Ideal.Quotient.mk I s' ∉ Q
      rw [hs']; exact s.2
    refine ⟨IsLocalization.mk' _ a' ⟨s', hs'P⟩, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_mk']
    congr 1
    · exact Subtype.ext hs'
  let e : LocalizedModule P.primeCompl (R ⧸ I) ≃ₗ[Localization.AtPrime P] Localization.AtPrime Q :=
    LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P) e₀
  rw [e.length_eq]
  exact length_eq_of_surjective_algebraMap _ _ _ hφ

end Inputs
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

section GenericH1
variable {W : Type u} [CommRing W] [IsDomain W]
variable (R : Type u) [CommRing R] [Algebra W R] (I : Ideal R)

noncomputable def primeOfMax (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) : PrimeSpectrum R :=
  ⟨(𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I), by
    haveI := 𝔪.isMaximal.isPrime
    exact inferInstance⟩

theorem primeOfMax_asIdeal (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) :
    (primeOfMax R I 𝔪).asIdeal =
      (𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I) := rfl

theorem primeOfMax_injective : Function.Injective (primeOfMax (W := W) R I) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  intro 𝔪₁ 𝔪₂ h
  have h1 := congrArg (fun P : PrimeSpectrum R => (P.asIdeal.map (Ideal.Quotient.mk I)).map
    (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))) h
  simp only [primeOfMax_asIdeal, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
    IsLocalization.map_under (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W))] at h1
  cases 𝔪₁; cases 𝔪₂; simp only at h1; subst h1; rfl

theorem le_primeOfMax (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) : I ≤ (primeOfMax R I 𝔪).asIdeal := by
  intro y hy
  rw [primeOfMax_asIdeal, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hy]
  exact Ideal.zero_mem _

theorem disjoint_primeOfMax (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) :
    Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑(primeOfMax R I 𝔪).asIdeal := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  rw [Set.disjoint_left]
  intro r hr hrP
  obtain ⟨w, hw, rfl⟩ := Submonoid.mem_map.mp hr
  rw [SetLike.mem_coe, primeOfMax_asIdeal, Ideal.mem_comap, Ideal.mem_comap, Ideal.Quotient.mk_algebraMap] at hrP
  have hu : IsUnit (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)) (algebraMap W (R ⧸ I) w)) :=
    IsLocalization.map_units ((FractionRing W) ⊗[W] (R ⧸ I))
      ⟨algebraMap W (R ⧸ I) w, Algebra.mem_algebraMapSubmonoid_of_mem ⟨w, hw⟩⟩
  exact 𝔪.isMaximal.ne_top (Ideal.eq_top_of_isUnit_mem _ hrP hu)

theorem mem_range_primeOfMax [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I))]
    (P : PrimeSpectrum R) (hIP : I ≤ P.asIdeal)
    (hdisj : Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal) :
    P ∈ Set.range (primeOfMax (W := W) R I) := by
  classical
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  haveI : IsArtinianRing ((FractionRing W) ⊗[W] (R ⧸ I)) := IsArtinianRing.of_finite (FractionRing W) _
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ P.asIdeal := by rw [Ideal.mk_ker]; exact hIP
  haveI hPbar : (P.asIdeal.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hback : (P.asIdeal.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P.asIdeal := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hIP
  have hdisj' : Disjoint (↑(Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) : Set (R ⧸ I))
      ↑(P.asIdeal.map (Ideal.Quotient.mk I)) := by
    rw [Set.disjoint_left]
    intro b hb hbP
    obtain ⟨w, hw, rfl⟩ := Submonoid.mem_map.mp hb
    rw [SetLike.mem_coe, ← Ideal.Quotient.mk_algebraMap, ← Ideal.mem_comap, hback] at hbP
    exact Set.disjoint_left.mp hdisj (Algebra.mem_algebraMapSubmonoid_of_mem ⟨w, hw⟩) hbP
  set 𝔪 : Ideal ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    (P.asIdeal.map (Ideal.Quotient.mk I)).map (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I))) with h𝔪
  haveI h𝔪p : 𝔪.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hPbar hdisj'
  haveI h𝔪m : 𝔪.IsMaximal := IsArtinianRing.isMaximal_of_isPrime 𝔪
  refine ⟨⟨𝔪, h𝔪m⟩, ?_⟩
  ext1
  rw [primeOfMax_asIdeal]
  change (Ideal.comap (algebraMap (R ⧸ I) _) 𝔪).comap _ = _
  have hunder : Ideal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I))) 𝔪 = P.asIdeal.map (Ideal.Quotient.mk I) :=
    IsLocalization.under_map_of_isPrime_disjoint (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) _ hPbar hdisj'
  rw [hunder, hback]

noncomputable def quotQuotEquiv (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) :
    ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))) ≃ₗ[W]
      R ⧸ (primeOfMax R I 𝔪).asIdeal := by
  refine ((Ideal.quotientEquivAlgOfEq W ?_).trans (DoubleQuot.quotQuotEquivQuotOfLEₐ W (le_primeOfMax R I 𝔪))).toLinearEquiv

  rw [primeOfMax_asIdeal]
  have h1 : Ideal.map (Ideal.Quotient.mkₐ W I)
      ((𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I)) =
      Ideal.map (Ideal.Quotient.mk I)
      ((𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))).comap (Ideal.Quotient.mk I)) := by
    simp only [Ideal.map, Ideal.Quotient.mkₐ_eq_mk]
  rw [h1, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]

theorem finrank_localization_atPrime_eq [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I))]
    (𝔪 : MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I)))
    (hfin : Module.Finite W (R ⧸ (primeOfMax R I 𝔪).asIdeal)) (hfree : Module.Free W (R ⧸ (primeOfMax R I 𝔪).asIdeal)) :
    (Module.finrank (FractionRing W) (Localization.AtPrime 𝔪.asIdeal) : ℕ∞) =
      (Module.finrank W (R ⧸ (primeOfMax R I 𝔪).asIdeal) : ℕ∞) *
        Module.length (Localization.AtPrime (primeOfMax R I 𝔪).asIdeal)
          (LocalizedModule (primeOfMax R I 𝔪).asIdeal.primeCompl (R ⧸ I)) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W)) ((FractionRing W) ⊗[W] (R ⧸ I)) :=
    IsLocalization.tensorRight (FractionRing W) (nonZeroDivisors W)
  haveI := 𝔪.isMaximal.isPrime
  haveI : Module.Finite (FractionRing W) (Localization.AtPrime 𝔪.asIdeal) :=
    moduleFinite_localization_atPrime_of_moduleFinite (FractionRing W) _ 𝔪
  haveI : Module.Finite W ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))) :=
    Module.Finite.equiv (quotQuotEquiv R I 𝔪).symm
  haveI : Module.Free W ((R ⧸ I) ⧸ 𝔪.asIdeal.comap (algebraMap (R ⧸ I) ((FractionRing W) ⊗[W] (R ⧸ I)))) :=
    Module.Free.of_equiv (quotQuotEquiv R I 𝔪).symm
  rw [finrank_eq_finrank_residueField_mul_length (FractionRing W) (Localization.AtPrime 𝔪.asIdeal)
      (Localization.AtPrime 𝔪.asIdeal),
    finrank_residueField_localization_eq_finrank_quotient W (R ⧸ I) 𝔪,
    (quotQuotEquiv R I 𝔪).finrank_eq,
    length_localization_atPrime_eq_of_isLocalization (R ⧸ I) (Algebra.algebraMapSubmonoid (R ⧸ I) (nonZeroDivisors W))
      ((FractionRing W) ⊗[W] (R ⧸ I)) 𝔪.asIdeal]
  congr 1
  exact (length_localizedModule_quotient_eq_length_localization R I _).symm

theorem finrank_tensor_quotient_eq_finsum_generic [Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I))]
    (hff : ∀ P : PrimeSpectrum R, I ≤ P.asIdeal →
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal →
        Module.Finite W (R ⧸ P.asIdeal) ∧ Module.Free W (R ⧸ P.asIdeal)) :
    (Module.finrank (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I)) : ℕ∞) =
      ∑ᶠ (P : PrimeSpectrum R) (_ : P ∈ {P : PrimeSpectrum R | I ≤ P.asIdeal ∧
          Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal}),
        (Module.finrank W (R ⧸ P.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime P.asIdeal) (LocalizedModule P.asIdeal.primeCompl (R ⧸ I)) := by
  classical
  haveI : IsArtinianRing ((FractionRing W) ⊗[W] (R ⧸ I)) := IsArtinianRing.of_finite (FractionRing W) _
  haveI : Finite (MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) := IsArtinianRing.instFiniteMaximalSpectrum _
  letI : Fintype (MaximalSpectrum ((FractionRing W) ⊗[W] (R ⧸ I))) := Fintype.ofFinite _
  have hrange : Set.range (primeOfMax (W := W) R I) = {P : PrimeSpectrum R | I ≤ P.asIdeal ∧
      Disjoint (↑(Algebra.algebraMapSubmonoid R (nonZeroDivisors W)) : Set R) ↑P.asIdeal} := by
    ext P
    constructor
    · rintro ⟨𝔪, rfl⟩
      exact ⟨le_primeOfMax R I 𝔪, disjoint_primeOfMax R I 𝔪⟩
    · rintro ⟨h1, h2⟩
      exact mem_range_primeOfMax R I P h1 h2
  rw [← hrange, finsum_mem_range (primeOfMax_injective R I), finsum_eq_sum_of_fintype,
    finrank_eq_sum_finrank_localization_atPrime (FractionRing W) ((FractionRing W) ⊗[W] (R ⧸ I)), Nat.cast_sum]
  refine Finset.sum_congr rfl fun 𝔪 _ => ?_
  obtain ⟨hfin, hfree⟩ := hff (primeOfMax R I 𝔪) (le_primeOfMax R I 𝔪) (disjoint_primeOfMax R I 𝔪)
  exact finrank_localization_atPrime_eq R I 𝔪 hfin hfree

end GenericH1
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

section CrossingH1
variable {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]

theorem length_localized_quot_eq_zero {R : Type u} [CommRing R] (P : Ideal R) [P.IsPrime] (x : R) (hx : x ∉ P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ Ideal.span {x})) = 0 := by
  rw [Module.length_eq_zero_iff]
  have hz : ∀ z : LocalizedModule P.primeCompl (R ⧸ Ideal.span {x}), z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [← LocalizedModule.zero_mk s, LocalizedModule.mk_eq]
      refine ⟨⟨x, hx⟩, ?_⟩
      simp only [smul_zero]
      rw [Submonoid.smul_def, Submonoid.smul_def, Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        ← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton x))
  exact ⟨fun a b => by rw [hz a, hz b]⟩

theorem disjoint_iff_const_not_mem (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e))) :
    Disjoint (↑(Algebra.algebraMapSubmonoid (UVCrossingModel W (ϖ ^ e)) (nonZeroDivisors W)) :
      Set (UVCrossingModel W (ϖ ^ e))) ↑P.asIdeal ↔ const (ϖ ^ e) ϖ ∉ P.asIdeal := by
  constructor
  · intro h hmem
    refine Set.disjoint_left.mp h ?_ hmem
    rw [SetLike.mem_coe, ← algebraMap_eq_const]
    exact Algebra.mem_algebraMapSubmonoid_of_mem ⟨ϖ, mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero⟩
  · intro hPϖ
    rw [Set.disjoint_left]
    intro r hr hrP
    obtain ⟨w, hw, rfl⟩ := Submonoid.mem_map.mp hr
    rw [SetLike.mem_coe, algebraMap_eq_const] at hrP
    have hw0 : (w : W) ≠ 0 := nonZeroDivisors.ne_zero hw
    obtain ⟨n, u, hwu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hϖ
    have hmem' : const (ϖ ^ e) ϖ ^ n ∈ P.asIdeal := by
      have h1 : const (ϖ ^ e) w = const (ϖ ^ e) (u : W) * const (ϖ ^ e) ϖ ^ n := by
        rw [hwu, ← constHom_apply, ← constHom_apply, ← constHom_apply, map_mul, map_pow]
      rw [h1] at hrP
      have hu : IsUnit (const (ϖ ^ e) (u : W)) := by
        rw [← constHom_apply]; exact (Units.isUnit u).map _
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hrP
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, pow_zero] at hmem'
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hmem')
    · exact hPϖ (P.isPrime.mem_of_pow_mem n hmem')

theorem finrank_tensor_quotient_eq_finsum (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0) :
    (Module.finrank (FractionRing W) ((FractionRing W) ⊗[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) : ℕ∞) =
      ∑ᶠ (P : PrimeSpectrum (UVCrossingModel W (ϖ ^ e)))
        (_ : P.asIdeal ≠ ⊥ ∧ const (ϖ ^ e) ϖ ∉ P.asIdeal),
        (Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ P.asIdeal) : ℕ∞) *
          Module.length (Localization.AtPrime P.asIdeal)
            (LocalizedModule P.asIdeal.primeCompl (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) := by
  classical
  haveI : Module.Finite (FractionRing W) ((FractionRing W) ⊗[W] (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x})) :=
    finite_tensor_quotient ϖ hϖ e he x hx
  have hgen := finrank_tensor_quotient_eq_finsum_generic (W := W) (UVCrossingModel W (ϖ ^ e)) (Ideal.span {x})
    (fun P hIP hdisj => by
      haveI := P.isPrime
      have hPϖ := (disjoint_iff_const_not_mem ϖ hϖ e P).mp hdisj
      exact free_finite_quotient_prime ϖ hϖ e he x hx P.asIdeal ((Ideal.span_singleton_le_iff_mem _).mp hIP) hPϖ)
  rw [hgen]

  apply finsum_mem_inter_support_eq
  ext P
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Function.mem_support, ne_eq]
  constructor
  · rintro ⟨⟨hIP, hdisj⟩, hne⟩
    refine ⟨⟨?_, (disjoint_iff_const_not_mem ϖ hϖ e P).mp hdisj⟩, hne⟩
    intro hbot
    have : x ∈ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).mp hIP
    rw [hbot, Ideal.mem_bot] at this
    exact hx this
  · rintro ⟨⟨hP0, hPϖ⟩, hne⟩
    refine ⟨⟨?_, (disjoint_iff_const_not_mem ϖ hϖ e P).mpr hPϖ⟩, hne⟩

    rw [Ideal.span_singleton_le_iff_mem]
    by_contra hxP
    haveI := P.isPrime
    apply hne
    rw [length_localized_quot_eq_zero P.asIdeal x hxP, mul_zero]

end CrossingH1
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

end P1Arch
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.P1Branch"

#print axioms P1Arch.finrank_tensor_quotient_eq_finsum

#print axioms P1Arch.free_finite_finrank_quotient_of_good

p2m_open "ModularCurve P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve ModularCurve.UVCrossingModel~U_mul_V P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff.ModularCurve.UVCrossingModel IsLocalRing"

theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e)
    (x : UVCrossingModel W (ϖ ^ e)) (hx : x ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (ϖ ^ e) (inU ab.1 + inV ab.2) = x)
    (hgood0 : ∃ i, IsUnit (PowerSeries.coeff i ab.1))
    (hgoodE : IsUnit (PowerSeries.constantCoeff ab.1) ∨ ∃ j, 1 ≤ j ∧ IsUnit (PowerSeries.coeff j ab.2)) :
    Module.Free W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) ∧
    Module.Finite W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) ∧
    ((Module.finrank W (UVCrossingModel W (ϖ ^ e) ⧸ Ideal.span {x}) : ℤ) =
      sInf (dominantIndices (IsDiscreteValuationRing.addVal W) e 0 ab) -
        sSup (dominantIndices (IsDiscreteValuationRing.addVal W) e e ab)) := by
  exact P1Arch.free_finite_finrank_quotient_of_good ϖ hϖ e he x hx ab hb habx hgood0 hgoodE

end S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_free_finite_finrank_quotient_span_of_isUnit_coeff (solution)
