-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.gaussOrder_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/aa98d6b6-0353-5878-9295-fa60c4d7915a

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_gaussOrder_mul

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

namespace AnnulusStepA

open ModularCurve ModularCurve.UVCrossingModel Finset AnnulusNF AnnulusG1

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

theorem repGaussOrder_normalForm_mul_le (v : AddValuation W ℕ∞) (π : W) (e t : ℕ) (hte : t < e)
    (hπ : v π = (e : ℕ∞)) (Fx Fy : MvPowerSeries (Fin 2) W)
    (hx : ∀ d : Fin 2 →₀ ℕ, d 0 ≠ 0 → d 1 ≠ 0 → MvPowerSeries.coeff d Fx = 0)
    (hy : ∀ d : Fin 2 →₀ ℕ, d 0 ≠ 0 → d 1 ≠ 0 → MvPowerSeries.coeff d Fy = 0)
    {H : ℕ → ℕ → W}
    (hH : ∀ i j, H i j = MvPowerSeries.coeff (ij i j) (Fx * Fy) + π * H (i + 1) (j + 1)) :
    repGaussOrder v e t (inU (PowerSeries.mk fun i => H i 0) +
        inV (PowerSeries.mk fun j => if j = 0 then 0 else H 0 j)) ≤
      repGaussOrder v e t Fx + repGaussOrder v e t Fy := by
  classical
  have hte' : t ≤ e := hte.le

  rcases eq_or_ne (repGaussOrder v e t Fx) ⊤ with hmt | hmt
  · rw [hmt, top_add]; exact le_top
  rcases eq_or_ne (repGaussOrder v e t Fy) ⊤ with hnt | hnt
  · rw [hnt, add_top]; exact le_top
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hmt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnt
  rw [← hm, ← hn]

  set ox : (Fin 2 →₀ ℕ) → ℕ∞ := fun d => v (MvPowerSeries.coeff d Fx) + (annulusWeight e t d : ℕ∞)
    with hox
  set oy : (Fin 2 →₀ ℕ) → ℕ∞ := fun d => v (MvPowerSeries.coeff d Fy) + (annulusWeight e t d : ℕ∞)
    with hoy
  have hox_ge : ∀ d, (m : ℕ∞) ≤ ox d := fun d => by rw [hm]; exact repGaussOrder_le v e t Fx d
  have hoy_ge : ∀ d, (n : ℕ∞) ≤ oy d := fun d => by rw [hn]; exact repGaussOrder_le v e t Fy d

  obtain ⟨dx, hdx_axis, hdx, hdx_min⟩ := exists_extreme_dominant v e t hte Fx hx m hm
  obtain ⟨dy, hdy_axis, hdy, hdy_min⟩ := exists_extreme_dominant v e t hte Fy hy n hn

  set μ : ℕ := min ((dx + dy) 0) ((dx + dy) 1) with hμ
  set i₀ : ℕ := (dx + dy) 0 - μ with hi₀
  set j₀ : ℕ := (dx + dy) 1 - μ with hj₀
  have hij₀ : i₀ = 0 ∨ j₀ = 0 := by simp only [hi₀, hj₀, hμ]; omega
  have hs_eq : dx + dy = ij (i₀ + μ) (j₀ + μ) := by
    have h0 : i₀ + μ = (dx + dy) 0 := by simp only [hi₀, hμ]; omega
    have h1 : j₀ + μ = (dx + dy) 1 := by simp only [hj₀, hμ]; omega
    rw [h0, h1]; exact eq_ij _

  refine le_trans (repGaussOrder_le v e t _ (ij i₀ j₀)) ?_
  rw [coeff_normalForm_axis H i₀ j₀ hij₀]
  set w₀ : ℕ∞ := (annulusWeight e t (ij i₀ j₀) : ℕ∞) with hw₀

  set N : ℕ := μ + 1 + (m + n) with hN
  rw [rec_iterate hH i₀ j₀ N]
  set σ : Finset (Σ _ : ℕ, (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) :=
    (range N).sigma (fun k => antidiagonal (ij (i₀ + k) (j₀ + k))) with hσ
  set f : (Σ _ : ℕ, (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) → W :=
    fun z => MvPowerSeries.coeff z.2.1 Fx * MvPowerSeries.coeff z.2.2 Fy * π ^ z.1 with hf
  have hexp : (∑ k ∈ range N, MvPowerSeries.coeff (ij (i₀ + k) (j₀ + k)) (Fx * Fy) * π ^ k) =
      ∑ z ∈ σ, f z := by
    rw [hσ, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  rw [hexp]

  set z₀ : (Σ _ : ℕ, (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) := ⟨μ, (dx, dy)⟩ with hz₀def
  have hz₀ : z₀ ∈ σ := by
    rw [hσ, Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨(by omega : μ < N), hs_eq⟩

  have hterm : ∀ z ∈ σ, v (f z) + w₀ = ox z.2.1 + oy z.2.2 := by
    rintro ⟨k, d₁, d₂⟩ hz
    rw [hσ, Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hz
    exact term_order v π e t hte' hπ Fx Fy i₀ j₀ k d₁ d₂ hz.2
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
      obtain ⟨hd1_axis, hd1_min⟩ := hdx_min d₁ hboth.1
      obtain ⟨hd2_axis, hd2_min⟩ := hdy_min d₂ hboth.2
      have hsum : lam d₁ + lam d₂ = lam dx + lam dy := by
        rw [← lam_add, ← lam_add, hzσ.2, hs_eq, lam_ij, lam_ij]; push_cast; ring
      have e1 : d₁ = dx := eq_of_axis_of_lam_eq hd1_axis hdx_axis (by omega)
      have e2 : d₂ = dy := eq_of_axis_of_lam_eq hd2_axis hdy_axis (by omega)
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
  rw [← Finset.add_sum_erase σ f hz₀, add_assoc]
  have hfin : (m : ℕ∞) + n ≠ ⊤ := by rw [← Nat.cast_add]; exact ENat.coe_ne_top _
  exact isolate v hfin hspecial hrest

theorem gaussOrder_mul_le_of_lt (v : AddValuation W ℕ∞) (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W]
    (e t : ℕ) (hte : t < e) (hϖ : v ϖ = 1) (x y : UVCrossingModel W (ϖ ^ e)) :
    gaussOrder v (ϖ ^ e) e t (x * y) ≤ gaussOrder v (ϖ ^ e) e t x + gaussOrder v (ϖ ^ e) e t y := by
  classical
  have he : 1 ≤ e := by omega
  have hπ : v (ϖ ^ e) = (e : ℕ∞) := by rw [v.map_pow, hϖ, nsmul_eq_mul, mul_one]
  have hπ' : ((e : ℕ) : ℕ∞) ≤ v (ϖ ^ e) := hπ.ge
  obtain ⟨⟨a, b⟩, -, hxmk, hgx⟩ := exists_normalForm_gaussOrder_eq v ϖ e he hπ' x
  obtain ⟨⟨a', b'⟩, -, hymk, hgy⟩ := exists_normalForm_gaussOrder_eq v ϖ e he hπ' y
  obtain ⟨⟨A, B⟩, hB0, hxymk, hgxy⟩ := exists_normalForm_gaussOrder_eq v ϖ e he hπ' (x * y)
  simp only at hxmk hgx hymk hgy hB0 hxymk hgxy
  rw [hgx t hte.le, hgy t hte.le, hgxy t hte.le]
  obtain ⟨H, hH, hmkH⟩ := exists_normalForm_rec ϖ e he ((inU a + inV b) * (inU a' + inV b'))
  have huniq := normalForm_unique ϖ e he (PowerSeries.mk fun i => H i 0)
      (PowerSeries.mk fun j => if j = 0 then 0 else H 0 j) A B (by simp) hB0
      (by rw [hmkH, map_mul, hxmk, hymk, hxymk])
  rw [← huniq.1, ← huniq.2]
  exact repGaussOrder_normalForm_mul_le v (ϖ ^ e) e t hte hπ _ _
    (coeff_nf_off_axis a b) (coeff_nf_off_axis a' b') hH

theorem repGaussOrder_uvSwap (v : W → ℕ∞) (e t : ℕ) (ht : t ≤ e) (F : MvPowerSeries (Fin 2) W) :
    repGaussOrder v e t (uvSwapEquiv F) = repGaussOrder v e (e - t) F := by
  classical
  unfold repGaussOrder
  rw [← Equiv.iInf_comp (Finsupp.equivCongrLeft (Equiv.swap (0 : Fin 2) 1))]
  refine iInf_congr fun d => ?_
  have h1 : Finsupp.equivCongrLeft (Equiv.swap (0 : Fin 2) 1) d =
      Finsupp.embDomain (Equiv.swap (0 : Fin 2) 1).toEmbedding d := by
    rw [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain,
      Finsupp.embDomain_eq_mapDomain, Equiv.coe_toEmbedding]
  have hc : MvPowerSeries.coeff (Finsupp.equivCongrLeft (Equiv.swap (0 : Fin 2) 1) d) (uvSwapEquiv F) =
      MvPowerSeries.coeff d F := by
    rw [h1, uvSwapEquiv_apply]
    exact MvPowerSeries.coeff_embDomain_rename (Equiv.swap (0 : Fin 2) 1).toEmbedding F d
  have hw : annulusWeight e t (Finsupp.equivCongrLeft (Equiv.swap (0 : Fin 2) 1) d) =
      annulusWeight e (e - t) d := by
    simp only [annulusWeight, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply,
      Equiv.symm_swap, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [Nat.sub_sub_self ht]; ring
  rw [hc, hw]

theorem gaussOrder_crossingSwap (v : W → ℕ∞) (π : W) (e t : ℕ) (ht : t ≤ e) (x : UVCrossingModel W π) :
    gaussOrder v π e t (crossingSwap π x) = gaussOrder v π e (e - t) x := by
  apply le_antisymm
  · rw [gaussOrder_le_iff]
    intro G hG
    have hx : mk π (uvSwapEquiv.symm G) = x := by
      apply (crossingSwap π).injective
      rw [crossingSwap_mk, RingEquiv.apply_symm_apply, hG]
    calc repGaussOrder v e t G = repGaussOrder v e t (uvSwapEquiv (uvSwapEquiv.symm G)) := by
          rw [RingEquiv.apply_symm_apply]
      _ = repGaussOrder v e (e - t) (uvSwapEquiv.symm G) := repGaussOrder_uvSwap v e t ht _
      _ ≤ gaussOrder v π e (e - t) (mk π (uvSwapEquiv.symm G)) := repGaussOrder_le_gaussOrder v π e _ _
      _ = gaussOrder v π e (e - t) x := by rw [hx]
  · rw [gaussOrder_le_iff]
    intro F hF
    calc repGaussOrder v e (e - t) F = repGaussOrder v e t (uvSwapEquiv F) :=
          (repGaussOrder_uvSwap v e t ht F).symm
      _ ≤ gaussOrder v π e t (mk π (uvSwapEquiv F)) := repGaussOrder_le_gaussOrder v π e t _
      _ = gaussOrder v π e t (crossingSwap π x) := by rw [← crossingSwap_mk, hF]

theorem gaussOrder_mul_le (v : AddValuation W ℕ∞) (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W]
    (e t : ℕ) (he : 1 ≤ e) (ht : t ≤ e) (hϖ : v ϖ = 1) (x y : UVCrossingModel W (ϖ ^ e)) :
    gaussOrder v (ϖ ^ e) e t (x * y) ≤ gaussOrder v (ϖ ^ e) e t x + gaussOrder v (ϖ ^ e) e t y := by
  rcases lt_or_eq_of_le ht with hlt | rfl
  · exact gaussOrder_mul_le_of_lt v ϖ e t hlt hϖ x y
  ·
    have key := gaussOrder_mul_le_of_lt v ϖ t 0 (by omega) hϖ (crossingSwap _ x) (crossingSwap _ y)
    rw [← map_mul, gaussOrder_crossingSwap _ _ t 0 (Nat.zero_le _),
      gaussOrder_crossingSwap _ _ t 0 (Nat.zero_le _), gaussOrder_crossingSwap _ _ t 0 (Nat.zero_le _),
      Nat.sub_zero] at key
    exact key

theorem gaussOrder_mul' (v : AddValuation W ℕ∞) (ϖ : W) [IsAdicComplete (Ideal.span {ϖ}) W]
    (e t : ℕ) (he : 1 ≤ e) (ht : t ≤ e) (hϖ : v ϖ = 1) (x y : UVCrossingModel W (ϖ ^ e)) :
    gaussOrder v (ϖ ^ e) e t (x * y) = gaussOrder v (ϖ ^ e) e t x + gaussOrder v (ϖ ^ e) e t y :=
  le_antisymm (gaussOrder_mul_le v ϖ e t he ht hϖ x y) (gaussOrder_add_le_gaussOrder_mul v _ e t x y)

theorem gaussOrder_mul
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e t : ℕ) (he : 1 ≤ e) (ht : t ≤ e)
    (x y : UVCrossingModel W (ϖ ^ e)) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t (x * y) =
      gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t x +
        gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t y := by
  have hmax : IsLocalRing.maximalIdeal W = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) W :=
    hmax ▸ (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal W) W)
  exact gaussOrder_mul' _ ϖ e t he ht (IsDiscreteValuationRing.addVal_uniformizer hϖ) x y

end AnnulusG1eq

open ModularCurve ModularCurve.UVCrossingModel in
theorem solution
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e t : ℕ) (he : 1 ≤ e) (ht : t ≤ e)
    (x y : UVCrossingModel W (ϖ ^ e)) :
    gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t (x * y) =
      gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t x +
        gaussOrder (IsDiscreteValuationRing.addVal W) (ϖ ^ e) e t y :=
  AnnulusG1eq.gaussOrder_mul ϖ hϖ e t he ht x y

end S_ModularCurve_UVCrossingModel_gaussOrder_mul
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_gaussOrder_mul (solution)
