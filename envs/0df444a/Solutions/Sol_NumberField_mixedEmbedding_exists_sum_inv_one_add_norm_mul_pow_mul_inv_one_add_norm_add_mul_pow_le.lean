-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/a27d3c56-3c3a-58fd-948e-81f9102116fe

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le

set_option autoImplicit false

p2m_open_scoped "NumberField P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le.NumberField"
p2m_open "NumberField P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le.NumberField NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le.NumberField.mixedEmbedding Module Finset"

namespace NumberField
p2m_export "NumberField" "mixedEmbedding.norm_apply mixedEmbedding mixedEmbedding.mixedSpace InfinitePlace mixedEmbedding.norm mixedEmbedding.norm_nonneg"
namespace mixedEmbedding
p2m_export "NumberField.mixedEmbedding" "index normAtPlace norm_eq_norm normAtPlace_nonneg mixedSpace normAtPlace_apply_of_isReal norm_smul normAtPlace_apply_of_isComplex"
namespace ShearedLatticeSol
p2m_open "NumberField.mixedEmbedding NumberField"

variable {K : Type*} [Field K] [NumberField K]

open scoped Classical

theorem normAtPlace_le_norm (w : InfinitePlace K) (x : mixedSpace K) :
    normAtPlace w x ≤ ‖x‖ := by
  obtain hw | hw := isReal_or_isComplex w
  · rw [normAtPlace_apply_of_isReal hw]
    exact (norm_le_pi_norm x.1 ⟨w, hw⟩).trans (norm_fst_le x)
  · rw [normAtPlace_apply_of_isComplex hw]
    exact (norm_le_pi_norm x.2 ⟨w, hw⟩).trans (norm_snd_le x)

theorem norm_le_norm_pow (x : mixedSpace K) :
    mixedEmbedding.norm x ≤ ‖x‖ ^ finrank ℚ K := by
  rw [mixedEmbedding.norm_apply, ← sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _) fun w _ => ?_
  exact pow_le_pow_left₀ (normAtPlace_nonneg w x) (normAtPlace_le_norm w x) _

theorem one_le_norm_mixedEmbedding {c : 𝓞 K} (hc : c ≠ 0) :
    1 ≤ mixedEmbedding.norm (mixedEmbedding K (c : K)) := by
  rw [norm_eq_norm, ← Algebra.coe_norm_int, Rat.cast_abs, Rat.cast_intCast]
  have h : Algebra.norm ℤ c ≠ 0 := Algebra.norm_ne_zero_iff.mpr hc
  exact_mod_cast Int.one_le_abs h

variable (K) in

noncomputable def sig (s : 𝓞 K) : ℝ := mixedEmbedding.norm (mixedEmbedding K (s : K))

theorem one_le_sig {s : 𝓞 K} (hs : s ≠ 0) : 1 ≤ sig K s := one_le_norm_mixedEmbedding hs

theorem sig_pos {s : 𝓞 K} (hs : s ≠ 0) : 0 < sig K s := one_pos.trans_le (one_le_sig hs)

theorem inv_sig_le_norm {s : 𝓞 K} (hs : s ≠ 0) {ξ : K} (hξ : ξ ≠ 0)
    (hint : ∃ c : 𝓞 K, (c : K) = (s : K) * ξ) :
    (sig K s)⁻¹ ≤ mixedEmbedding.norm (mixedEmbedding K ξ) := by
  obtain ⟨c, hc⟩ := hint
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hc
    have : (s : K) * ξ = 0 := by rw [← hc]; rfl
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hs (by exact_mod_cast h1)
    · exact hξ h1
  have h1 : 1 ≤ mixedEmbedding.norm (mixedEmbedding K (c : K)) := one_le_norm_mixedEmbedding hc0
  rw [hc, map_mul, map_mul] at h1
  have hσ := sig_pos hs
  rw [inv_le_iff_one_le_mul₀ hσ]
  simpa only [sig, mul_comm] using h1

theorem norm_mul_inv_sig_le_pow {s : 𝓞 K} (hs : s ≠ 0) (a : mixedSpace K) {ξ : K} (hξ : ξ ≠ 0)
    (hint : ∃ c : 𝓞 K, (c : K) = (s : K) * ξ) :
    mixedEmbedding.norm a * (sig K s)⁻¹ ≤ ‖a * mixedEmbedding K ξ‖ ^ finrank ℚ K := by
  refine le_trans ?_ (norm_le_norm_pow _)
  rw [map_mul]
  exact mul_le_mul_of_nonneg_left (inv_sig_le_norm hs hξ hint) (mixedEmbedding.norm_nonneg _)

variable (K) in

abbrev CoordIdx : Type _ :=
  {w : InfinitePlace K // IsReal w} ⊕
    ({w : InfinitePlace K // IsComplex w} ⊕ {w : InfinitePlace K // IsComplex w})

noncomputable def rnd (x : mixedSpace K) : CoordIdx K → ℝ
  | Sum.inl w => ((⌊2 * x.1 w⌋ : ℤ) : ℝ)
  | Sum.inr (Sum.inl w) => ((⌊2 * (x.2 w).re⌋ : ℤ) : ℝ)
  | Sum.inr (Sum.inr w) => ((⌊2 * (x.2 w).im⌋ : ℤ) : ℝ)

theorem abs_floor_le (t : ℝ) : |((⌊t⌋ : ℤ) : ℝ)| ≤ |t| + 1 := by
  rw [abs_le]
  constructor
  · have h1 := Int.lt_floor_add_one t
    have h2 := neg_abs_le t
    linarith
  · have h1 := Int.floor_le t
    have h2 := le_abs_self t
    linarith

theorem norm_rnd_le (x : mixedSpace K) : ‖rnd x‖ ≤ 2 * ‖x‖ + 1 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  have h2 : ∀ t : ℝ, |t| ≤ ‖x‖ → ‖((⌊2 * t⌋ : ℤ) : ℝ)‖ ≤ 2 * ‖x‖ + 1 := by
    intro t ht
    rw [Real.norm_eq_abs]
    refine (abs_floor_le _).trans ?_
    rw [abs_mul, abs_two]
    linarith
  match i with
  | Sum.inl w =>
    simp only [rnd]
    refine h2 _ ?_
    rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm x.1 w).trans (norm_fst_le x)
  | Sum.inr (Sum.inl w) =>
    simp only [rnd]
    exact h2 _ ((Complex.abs_re_le_norm _).trans
      ((norm_le_pi_norm x.2 w).trans (norm_snd_le x)))
  | Sum.inr (Sum.inr w) =>
    simp only [rnd]
    exact h2 _ ((Complex.abs_im_le_norm _).trans
      ((norm_le_pi_norm x.2 w).trans (norm_snd_le x)))

theorem norm_sub_lt_one_of_rnd_eq {x y : mixedSpace K} (h : rnd x = rnd y) :
    ‖x - y‖ < 1 := by
  have hc : ∀ s t : ℝ, ((⌊2 * s⌋ : ℤ) : ℝ) = ((⌊2 * t⌋ : ℤ) : ℝ) → |s - t| < 1 / 2 := by
    intro s t hst
    have h1 := Int.abs_sub_lt_one_of_floor_eq_floor (Int.cast_injective hst)
    rw [← mul_sub, abs_mul, abs_two] at h1
    linarith
  rw [Prod.norm_def, max_lt_iff]
  constructor
  · rw [pi_norm_lt_iff zero_lt_one]
    intro w
    have h1 := hc _ _ (by simpa only [rnd] using congr_fun h (Sum.inl w))
    rw [Prod.fst_sub, Pi.sub_apply, Real.norm_eq_abs]
    linarith
  · rw [pi_norm_lt_iff zero_lt_one]
    intro w
    have hre := hc _ _ (by simpa only [rnd] using congr_fun h (Sum.inr (Sum.inl w)))
    have him := hc _ _ (by simpa only [rnd] using congr_fun h (Sum.inr (Sum.inr w)))
    rw [Prod.snd_sub, Pi.sub_apply]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    rw [Complex.sub_re, Complex.sub_im]
    linarith

variable (K) in

abbrev intLattice : Submodule ℤ (CoordIdx K → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (CoordIdx K)))

theorem rnd_mem (x : mixedSpace K) : rnd x ∈ intLattice K := by
  refine ((Pi.basisFun ℝ (CoordIdx K)).mem_span_iff_repr_mem ℤ (rnd x)).mpr fun i => ?_
  rw [Pi.basisFun_repr]
  match i with
  | Sum.inl w => exact ⟨⌊2 * x.1 w⌋, by simp [rnd]⟩
  | Sum.inr (Sum.inl w) => exact ⟨⌊2 * (x.2 w).re⌋, by simp [rnd]⟩
  | Sum.inr (Sum.inr w) => exact ⟨⌊2 * (x.2 w).im⌋, by simp [rnd]⟩

theorem card_coordIdx : Fintype.card (CoordIdx K) = finrank ℚ K := by
  rw [Fintype.card_sum, Fintype.card_sum, ← card_add_two_mul_card_eq_rank, two_mul]

variable (K) in

noncomputable def kk : ℕ := Fintype.card (CoordIdx K) + 1

variable (K) in

noncomputable def W (z : intLattice K) : ℝ := (1 + ‖(z : CoordIdx K → ℝ)‖)⁻¹ ^ kk K

theorem W_nonneg (z : intLattice K) : 0 ≤ W K z := by unfold W; positivity

theorem summable_W : Summable (W K) := by
  have hrank : finrank ℤ (intLattice K) < kk K := by
    rw [ZLattice.rank ℝ (intLattice K), finrank_fintype_fun_eq_card]
    exact Nat.lt_succ_self _
  have hg := ZLattice.summable_norm_pow_inv (intLattice K) (kk K) hrank
  refine (Finset.summable_compl_iff ({0} : Finset (intLattice K))).mp ?_
  refine Summable.of_nonneg_of_le (fun z => W_nonneg _) (fun z => ?_)
    (hg.comp_injective Subtype.val_injective)
  have hz : (z : intLattice K) ≠ 0 := by
    have := z.2
    simpa only [Finset.mem_singleton] using this
  simp only [Function.comp_apply, W]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [← Submodule.coe_norm]
  exact inv_anti₀ (norm_pos_iff.mpr hz) (by linarith [norm_nonneg (z : intLattice K)])

variable (K) in

noncomputable def ZZ : ℝ := ∑' z, W K z

theorem ZZ_nonneg : 0 ≤ ZZ K := tsum_nonneg W_nonneg

theorem packing {ι : Type*} (S : Finset ι) (u : ι → mixedSpace K) (t : mixedSpace K) {r : ℝ}
    (hr : 0 < r) (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r ≤ ‖u i - u j‖) :
    ∑ i ∈ S, (1 + ‖t + u i‖)⁻¹ ^ kk K ≤ 2 ^ kk K * (max 1 r⁻¹) ^ kk K * ZZ K := by
  set m : ℝ := max 1 r⁻¹ with hm_def
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm0 : 0 < m := one_pos.trans_le hm1
  have hmr : r⁻¹ ≤ m := le_max_right _ _

  let R : ι → intLattice K := fun i => ⟨rnd (r⁻¹ • (t + u i)), rnd_mem _⟩
  have hRinj : Set.InjOn R S := by
    intro i hi j hj hij
    by_contra hne
    have hlt := norm_sub_lt_one_of_rnd_eq (congrArg Subtype.val hij)
    rw [← smul_sub, add_sub_add_left_eq_sub, _root_.norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr)] at hlt
    have hge := hsep i hi j hj hne
    have : r⁻¹ * ‖u i - u j‖ ≥ 1 := by
      rw [ge_iff_le, ← div_le_iff₀' (inv_pos.mpr hr), one_div, inv_inv]
      exact hge
    linarith

  have hpt : ∀ i, (1 + ‖t + u i‖)⁻¹ ^ kk K ≤ (2 * m) ^ kk K * W K (R i) := by
    intro i
    set v : mixedSpace K := r⁻¹ • (t + u i) with hv_def
    have hv : ‖v‖ = r⁻¹ * ‖t + u i‖ := by
      rw [hv_def, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    have hR : ‖rnd v‖ ≤ 2 * ‖v‖ + 1 := norm_rnd_le v
    have h0 : 0 ≤ ‖t + u i‖ := norm_nonneg _
    have h4 : 1 + ‖rnd v‖ ≤ 2 * m * (1 + ‖t + u i‖) := by
      have h5 : r⁻¹ * ‖t + u i‖ ≤ m * ‖t + u i‖ := mul_le_mul_of_nonneg_right hmr h0
      nlinarith
    have h6 : (1 + ‖t + u i‖)⁻¹ ≤ 2 * m * (1 + ‖rnd v‖)⁻¹ := by
      rw [show (1 + ‖t + u i‖)⁻¹ = 2 * m * (2 * m * (1 + ‖t + u i‖))⁻¹ by
        field_simp]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h4) (by positivity)
    calc (1 + ‖t + u i‖)⁻¹ ^ kk K ≤ (2 * m * (1 + ‖rnd v‖)⁻¹) ^ kk K :=
          pow_le_pow_left₀ (by positivity) h6 _
      _ = (2 * m) ^ kk K * W K (R i) := by rw [mul_pow]; rfl
  calc ∑ i ∈ S, (1 + ‖t + u i‖)⁻¹ ^ kk K
      ≤ ∑ i ∈ S, (2 * m) ^ kk K * W K (R i) := Finset.sum_le_sum fun i _ => hpt i
    _ = (2 * m) ^ kk K * ∑ i ∈ S, W K (R i) := by rw [Finset.mul_sum]
    _ = (2 * m) ^ kk K * ∑ z ∈ S.image R, W K z := by rw [Finset.sum_image hRinj]
    _ ≤ (2 * m) ^ kk K * ZZ K := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact summable_W.sum_le_tsum _ (fun z _ => W_nonneg z)
    _ = 2 ^ kk K * (max 1 r⁻¹) ^ kk K * ZZ K := by rw [mul_pow]

def MemInv (s : 𝓞 K) (ξ : K) : Prop := ∃ c : 𝓞 K, (c : K) = (s : K) * ξ

omit [NumberField K] in
theorem memInv_sub {s : 𝓞 K} {ξ η : K} (hξ : MemInv s ξ) (hη : MemInv s η) : MemInv s (ξ - η) := by
  obtain ⟨c, hc⟩ := hξ
  obtain ⟨d, hd⟩ := hη
  refine ⟨c - d, ?_⟩
  push_cast
  linear_combination hc - hd

theorem exists_root {β : ℝ} (hβ : 0 < β) :
    ∃ r : ℝ, 0 < r ∧ r ^ finrank ℚ K = β ∧ (β ≤ 1 → β ≤ r) := by
  have hd : (finrank ℚ K : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  refine ⟨β ^ ((finrank ℚ K : ℝ)⁻¹), Real.rpow_pos_of_pos hβ _, ?_, fun h1 => ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hβ.le, inv_mul_cancel₀ hd, Real.rpow_one]
  · conv_lhs => rw [← Real.rpow_one β]
    refine Real.rpow_le_rpow_of_exponent_ge hβ h1 ?_
    rw [inv_le_one_iff₀]
    right
    exact_mod_cast Module.finrank_pos

variable (K) in

noncomputable def PP (s : 𝓞 K) : ℝ := 2 ^ kk K * ZZ K * (1 + sig K s ^ 2)

theorem PP_nonneg (s : 𝓞 K) : 0 ≤ PP K s := by
  unfold PP
  exact mul_nonneg (mul_nonneg (by positivity) ZZ_nonneg) (by positivity)

theorem transl_bound {s : 𝓞 K} (hs : s ≠ 0) (b t : mixedSpace K) (hb : 0 < mixedEmbedding.norm b)
    (S : Finset K) (hS : ∀ ξ ∈ S, MemInv s ξ) :
    ∑ ξ ∈ S, (1 + ‖t + b * mixedEmbedding K ξ‖)⁻¹ ^ kk K
      ≤ PP K s * (1 + (mixedEmbedding.norm b)⁻¹ ^ 2) := by
  set β : ℝ := mixedEmbedding.norm b * (sig K s)⁻¹ with hβ_def
  have hσ := sig_pos hs
  have hβ : 0 < β := mul_pos hb (inv_pos.mpr hσ)
  obtain ⟨r, hr, hrd, hrβ⟩ := exists_root (K := K) hβ

  have hsep : ∀ ξ ∈ S, ∀ η ∈ S, ξ ≠ η →
      r ≤ ‖b * mixedEmbedding K ξ - b * mixedEmbedding K η‖ := by
    intro ξ hξ η hη hne
    have hsub : ξ - η ≠ 0 := sub_ne_zero.mpr hne
    have h1 : β ≤ ‖b * mixedEmbedding K (ξ - η)‖ ^ finrank ℚ K :=
      norm_mul_inv_sig_le_pow hs b hsub (memInv_sub (hS ξ hξ) (hS η hη))
    rw [map_sub, mul_sub, ← hrd] at h1
    exact le_of_pow_le_pow_left₀ Module.finrank_pos.ne' (norm_nonneg _) h1
  have hpack := packing S (fun ξ => b * mixedEmbedding K ξ) t hr hsep

  have hmax : (max 1 r⁻¹) ^ kk K ≤ 1 + β⁻¹ ^ 2 := by
    rcases le_or_gt 1 β with h1 | h1
    ·
      have hr1 : 1 ≤ r := by
        by_contra h
        rw [not_le] at h
        have : r ^ finrank ℚ K < 1 := pow_lt_one₀ hr.le h Module.finrank_pos.ne'
        rw [hrd] at this
        linarith
      rw [max_eq_left (inv_le_one_of_one_le₀ hr1), one_pow]
      linarith [sq_nonneg β⁻¹]
    ·
      have hβr : β ≤ r := hrβ h1.le
      have hr1 : r ≤ 1 := by
        by_contra h
        rw [not_le] at h
        have : 1 < r ^ finrank ℚ K := one_lt_pow₀ h Module.finrank_pos.ne'
        rw [hrd] at this
        linarith
      rw [max_eq_right (one_le_inv_iff₀.mpr ⟨hr, hr1⟩)]
      have hk : kk K = finrank ℚ K + 1 := by rw [kk, card_coordIdx]
      rw [hk, pow_succ, inv_pow, hrd]
      have h2 : r⁻¹ ≤ β⁻¹ := (inv_le_inv₀ hr hβ).mpr hβr
      calc β⁻¹ * r⁻¹ ≤ β⁻¹ * β⁻¹ := mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hβ).le
        _ = β⁻¹ ^ 2 := by ring
        _ ≤ 1 + β⁻¹ ^ 2 := by linarith

  have hβinv : β⁻¹ ^ 2 = sig K s ^ 2 * (mixedEmbedding.norm b)⁻¹ ^ 2 := by
    rw [hβ_def, mul_inv, inv_inv, mul_pow]; ring
  have hZ := ZZ_nonneg (K := K)
  calc ∑ ξ ∈ S, (1 + ‖t + b * mixedEmbedding K ξ‖)⁻¹ ^ kk K
      ≤ 2 ^ kk K * (max 1 r⁻¹) ^ kk K * ZZ K := hpack
    _ ≤ 2 ^ kk K * (1 + β⁻¹ ^ 2) * ZZ K := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmax (by positivity)) hZ
    _ = 2 ^ kk K * ZZ K * (1 + sig K s ^ 2 * (mixedEmbedding.norm b)⁻¹ ^ 2) := by
        rw [hβinv]; ring
    _ ≤ PP K s * (1 + (mixedEmbedding.norm b)⁻¹ ^ 2) := by
        unfold PP
        have h3 : 1 + sig K s ^ 2 * (mixedEmbedding.norm b)⁻¹ ^ 2
            ≤ (1 + sig K s ^ 2) * (1 + (mixedEmbedding.norm b)⁻¹ ^ 2) := by
          nlinarith [sq_nonneg (sig K s), sq_nonneg (mixedEmbedding.norm b)⁻¹,
            mul_nonneg (sq_nonneg (sig K s)) (sq_nonneg (mixedEmbedding.norm b)⁻¹)]
        calc 2 ^ kk K * ZZ K * (1 + sig K s ^ 2 * (mixedEmbedding.norm b)⁻¹ ^ 2)
            ≤ 2 ^ kk K * ZZ K * ((1 + sig K s ^ 2) * (1 + (mixedEmbedding.norm b)⁻¹ ^ 2)) :=
              mul_le_mul_of_nonneg_left h3 (by positivity)
          _ = 2 ^ kk K * ZZ K * (1 + sig K s ^ 2) * (1 + (mixedEmbedding.norm b)⁻¹ ^ 2) := by ring

variable (K) in

noncomputable def QQ (s : 𝓞 K) (N : ℕ) : ℝ := max 1 (sig K s ^ N)

theorem one_le_QQ (s : 𝓞 K) (N : ℕ) : 1 ≤ QQ K s N := le_max_left _ _

theorem decay_factor {s : 𝓞 K} (hs : s ≠ 0) (N : ℕ) (a : mixedSpace K)
    (ha : 0 < mixedEmbedding.norm a) {ξ : K} (hξ : ξ ≠ 0) (hint : MemInv s ξ) :
    ((1 + ‖a * mixedEmbedding K ξ‖)⁻¹ ^ finrank ℚ K) ^ N
      ≤ QQ K s N * min 1 ((mixedEmbedding.norm a)⁻¹ ^ N) := by
  set α : ℝ := mixedEmbedding.norm a * (sig K s)⁻¹ with hα_def
  have hσ := sig_pos hs
  have hα : 0 < α := mul_pos ha (inv_pos.mpr hσ)
  set u := a * mixedEmbedding K ξ with hu_def
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  have hud : α ≤ ‖u‖ ^ finrank ℚ K := norm_mul_inv_sig_le_pow hs a hξ hint

  have h1 : (1 + ‖u‖)⁻¹ ^ finrank ℚ K ≤ 1 := pow_le_one₀ (by positivity)
    (inv_le_one_of_one_le₀ (by linarith))
  have h2 : (1 + ‖u‖)⁻¹ ^ finrank ℚ K ≤ α⁻¹ := by
    rw [inv_pow]
    refine (inv_le_inv₀ (by positivity) hα).mpr (hud.trans ?_)
    exact pow_le_pow_left₀ hu0 (by linarith) _
  have h3 : ((1 + ‖u‖)⁻¹ ^ finrank ℚ K) ^ N ≤ min 1 (α⁻¹ ^ N) := by
    refine le_min ?_ ?_
    · exact pow_le_one₀ (by positivity) h1
    · exact pow_le_pow_left₀ (by positivity) h2 N
  refine h3.trans ?_

  have hαinv : α⁻¹ ^ N = sig K s ^ N * (mixedEmbedding.norm a)⁻¹ ^ N := by
    rw [hα_def, mul_inv, inv_inv, mul_pow, mul_comm]
  have hQ := one_le_QQ (K := K) s N
  rw [mul_min_of_nonneg _ _ (zero_le_one.trans hQ), mul_one]
  refine le_min ((min_le_left _ _).trans hQ) ((min_le_right _ _).trans ?_)
  rw [hαinv]
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

theorem decay_bound {s : 𝓞 K} (hs : s ≠ 0) (N : ℕ) (a : mixedSpace K)
    (ha : 0 < mixedEmbedding.norm a) (S : Finset K) (hS : ∀ ξ ∈ S, ξ ≠ 0 ∧ MemInv s ξ) :
    ∑ ξ ∈ S, (1 + ‖a * mixedEmbedding K ξ‖)⁻¹ ^ (kk K + finrank ℚ K * N)
      ≤ PP K s * QQ K s N * (1 + (mixedEmbedding.norm a)⁻¹ ^ 2)
          * min 1 ((mixedEmbedding.norm a)⁻¹ ^ N) := by
  have hpt : ∀ ξ ∈ S, (1 + ‖a * mixedEmbedding K ξ‖)⁻¹ ^ (kk K + finrank ℚ K * N)
      ≤ (QQ K s N * min 1 ((mixedEmbedding.norm a)⁻¹ ^ N))
          * (1 + ‖0 + a * mixedEmbedding K ξ‖)⁻¹ ^ kk K := by
    intro ξ hξ
    rw [pow_add, pow_mul, zero_add, mul_comm]
    exact mul_le_mul_of_nonneg_right (decay_factor hs N a ha (hS ξ hξ).1 (hS ξ hξ).2)
      (by positivity)
  have htr := transl_bound hs a 0 ha S (fun ξ hξ => (hS ξ hξ).2)
  have hQmin : 0 ≤ QQ K s N * min 1 ((mixedEmbedding.norm a)⁻¹ ^ N) :=
    mul_nonneg (zero_le_one.trans (one_le_QQ s N)) (le_min zero_le_one (by positivity))
  calc ∑ ξ ∈ S, (1 + ‖a * mixedEmbedding K ξ‖)⁻¹ ^ (kk K + finrank ℚ K * N)
      ≤ ∑ ξ ∈ S, (QQ K s N * min 1 ((mixedEmbedding.norm a)⁻¹ ^ N))
          * (1 + ‖0 + a * mixedEmbedding K ξ‖)⁻¹ ^ kk K := Finset.sum_le_sum hpt
    _ = (QQ K s N * min 1 ((mixedEmbedding.norm a)⁻¹ ^ N))
          * ∑ ξ ∈ S, (1 + ‖0 + a * mixedEmbedding K ξ‖)⁻¹ ^ kk K := by rw [Finset.mul_sum]
    _ ≤ (QQ K s N * min 1 ((mixedEmbedding.norm a)⁻¹ ^ N))
          * (PP K s * (1 + (mixedEmbedding.norm a)⁻¹ ^ 2)) :=
        mul_le_mul_of_nonneg_left htr hQmin
    _ = PP K s * QQ K s N * (1 + (mixedEmbedding.norm a)⁻¹ ^ 2)
          * min 1 ((mixedEmbedding.norm a)⁻¹ ^ N) := by ring

theorem main {s : 𝓞 K} (hs : s ≠ 0) (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (a b : mixedSpace K),
        0 < mixedEmbedding.norm a → 0 < mixedEmbedding.norm b →
        ∀ (τ : K → mixedSpace K), τ 0 = 0 → ∀ (T : Finset (K × K)),
          (∀ p ∈ T, p ≠ 0 ∧ (∃ c : 𝓞 K, (c : K) = (s : K) * p.1) ∧
            (∃ c : 𝓞 K, (c : K) = (s : K) * p.2)) →
          ∑ p ∈ T, ((1 + ‖a * mixedEmbedding K p.1‖) ^ M)⁻¹ *
              ((1 + ‖τ p.1 + b * mixedEmbedding K p.2‖) ^ M)⁻¹
            ≤ C * (1 + (mixedEmbedding.norm a)⁻¹ ^ 2)
                * (1 + (mixedEmbedding.norm b)⁻¹ ^ 2)
                * (min 1 ((mixedEmbedding.norm a)⁻¹ ^ N)
                    + min 1 ((mixedEmbedding.norm b)⁻¹ ^ N)) := by
  have hP0 : 0 ≤ PP K s := PP_nonneg s
  have hQ1 : 1 ≤ QQ K s N := one_le_QQ s N
  refine ⟨kk K + finrank ℚ K * N, PP K s * QQ K s N + PP K s * PP K s * QQ K s N,
    add_nonneg (mul_nonneg hP0 (zero_le_one.trans hQ1))
      (mul_nonneg (mul_nonneg hP0 hP0) (zero_le_one.trans hQ1)),
    fun a b ha hb τ hτ T hT => ?_⟩

  have Hdec_a := decay_bound hs N a ha
  have Hdec_b := decay_bound hs N b hb
  have Htr : ∀ (t : mixedSpace K) (S : Finset K), (∀ ξ ∈ S, MemInv s ξ) →
      ∑ ξ ∈ S, (1 + ‖t + b * mixedEmbedding K ξ‖)⁻¹ ^ kk K
        ≤ PP K s * (1 + (mixedEmbedding.norm b)⁻¹ ^ 2) := fun t S hS => transl_bound hs b t hb S hS
  generalize hP : PP K s = P at hP0 Hdec_a Hdec_b Htr ⊢
  generalize hQ : QQ K s N = Q at hQ1 Hdec_a Hdec_b ⊢
  generalize hM : kk K + finrank ℚ K * N = M at Hdec_a Hdec_b ⊢
  have hMk : kk K ≤ M := by rw [← hM]; exact Nat.le_add_right _ _
  generalize hNa : mixedEmbedding.norm a = Na at ha Hdec_a ⊢
  generalize hNb : mixedEmbedding.norm b = Nb at hb Hdec_b Htr ⊢
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ1

  obtain ⟨A, hA⟩ : ∃ A : K → ℝ, A = fun ξ => (1 + ‖a * mixedEmbedding K ξ‖)⁻¹ ^ M := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : K × K → ℝ,
      B = fun p => (1 + ‖τ p.1 + b * mixedEmbedding K p.2‖)⁻¹ ^ M := ⟨_, rfl⟩
  have hA0 : ∀ ξ, 0 ≤ A ξ := fun ξ => by rw [hA]; positivity
  have hA1 : ∀ ξ, A ξ ≤ 1 := fun ξ => by
    rw [hA]
    exact pow_le_one₀ (by positivity)
      (inv_le_one_of_one_le₀ (by linarith [norm_nonneg (a * mixedEmbedding K ξ)]))
  have hBk : ∀ p, B p ≤ (1 + ‖τ p.1 + b * mixedEmbedding K p.2‖)⁻¹ ^ kk K := fun p => by
    rw [hB]
    exact pow_le_pow_of_le_one (by positivity)
      (inv_le_one_of_one_le₀ (by linarith [norm_nonneg (τ p.1 + b * mixedEmbedding K p.2)])) hMk
  have hsum_eq : ∑ p ∈ T, ((1 + ‖a * mixedEmbedding K p.1‖) ^ M)⁻¹ *
      ((1 + ‖τ p.1 + b * mixedEmbedding K p.2‖) ^ M)⁻¹ = ∑ p ∈ T, A p.1 * B p := by
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hA, hB, inv_pow]
  rw [hsum_eq]

  have hsplit : ∑ p ∈ T, A p.1 * B p
      = ∑ p ∈ T with p.1 = 0, A p.1 * B p + ∑ p ∈ T with ¬ p.1 = 0, A p.1 * B p :=
    (Finset.sum_filter_add_sum_filter_not T (fun p => p.1 = 0) _).symm

  have h0 : ∑ p ∈ T with p.1 = 0, A p.1 * B p ≤ P * Q * (1 + Nb⁻¹ ^ 2) * min 1 (Nb⁻¹ ^ N) := by
    have hle : ∀ p ∈ T.filter (fun p => p.1 = 0),
        A p.1 * B p ≤ (1 + ‖b * mixedEmbedding K p.2‖)⁻¹ ^ M := by
      intro p hp
      have hp1 : p.1 = 0 := (Finset.mem_filter.mp hp).2
      have : B p = (1 + ‖b * mixedEmbedding K p.2‖)⁻¹ ^ M := by
        rw [hB]
        simp only [hp1, hτ, zero_add]
      rw [this]
      exact mul_le_of_le_one_left (by positivity) (hA1 _)
    have hinj : Set.InjOn Prod.snd (T.filter (fun p => p.1 = 0) : Set (K × K)) := by
      intro p hp q hq hpq
      have hp1 : p.1 = 0 := (Finset.mem_filter.mp hp).2
      have hq1 : q.1 = 0 := (Finset.mem_filter.mp hq).2
      exact Prod.ext (hp1.trans hq1.symm) hpq
    have hS : ∀ ξ ∈ (T.filter (fun p => p.1 = 0)).image Prod.snd, ξ ≠ 0 ∧ MemInv s ξ := by
      intro ξ hξ
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hξ
      have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
      have hp1 : p.1 = 0 := (Finset.mem_filter.mp hp).2
      obtain ⟨hp0, -, h2⟩ := hT p hpT
      exact ⟨fun h => hp0 (Prod.ext hp1 h), h2⟩
    calc ∑ p ∈ T with p.1 = 0, A p.1 * B p
        ≤ ∑ p ∈ T with p.1 = 0, (1 + ‖b * mixedEmbedding K p.2‖)⁻¹ ^ M := Finset.sum_le_sum hle
      _ = ∑ ξ ∈ (T.filter (fun p => p.1 = 0)).image Prod.snd, (1 + ‖b * mixedEmbedding K ξ‖)⁻¹ ^ M :=
          (Finset.sum_image (f := fun ξ => (1 + ‖b * mixedEmbedding K ξ‖)⁻¹ ^ M) hinj).symm
      _ ≤ P * Q * (1 + Nb⁻¹ ^ 2) * min 1 (Nb⁻¹ ^ N) := Hdec_b _ hS

  have h1 : ∑ p ∈ T with ¬ p.1 = 0, A p.1 * B p
      ≤ P * (1 + Nb⁻¹ ^ 2) * (P * Q * (1 + Na⁻¹ ^ 2) * min 1 (Na⁻¹ ^ N)) := by
    have hmaps : ∀ p ∈ T.filter (fun p => ¬ p.1 = 0),
        p.1 ∈ (T.filter (fun p => ¬ p.1 = 0)).image Prod.fst := fun p hp =>
      Finset.mem_image_of_mem _ hp
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]

    have hinner : ∀ ξ₁ ∈ (T.filter (fun p => ¬ p.1 = 0)).image Prod.fst,
        ∑ p ∈ (T.filter (fun p => ¬ p.1 = 0)) with p.1 = ξ₁, A p.1 * B p
          ≤ A ξ₁ * (P * (1 + Nb⁻¹ ^ 2)) := by
      intro ξ₁ _
      have heq : ∑ p ∈ (T.filter (fun p => ¬ p.1 = 0)) with p.1 = ξ₁, A p.1 * B p
          = A ξ₁ * ∑ p ∈ (T.filter (fun p => ¬ p.1 = 0)) with p.1 = ξ₁, B p := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(Finset.mem_filter.mp hp).2]
      rw [heq]
      refine mul_le_mul_of_nonneg_left ?_ (hA0 _)
      have hinj : Set.InjOn Prod.snd
          (((T.filter (fun p => ¬ p.1 = 0)).filter fun p => p.1 = ξ₁ : Finset (K × K)) :
            Set (K × K)) := by
        intro p hp q hq hpq
        have hp1 : p.1 = ξ₁ := (Finset.mem_filter.mp hp).2
        have hq1 : q.1 = ξ₁ := (Finset.mem_filter.mp hq).2
        exact Prod.ext (hp1.trans hq1.symm) hpq
      have hS : ∀ ξ ∈ ((T.filter (fun p => ¬ p.1 = 0)).filter fun p => p.1 = ξ₁).image Prod.snd,
          MemInv s ξ := by
        intro ξ hξ
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hξ
        have hpT : p ∈ T := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1
        exact (hT p hpT).2.2
      calc ∑ p ∈ (T.filter (fun p => ¬ p.1 = 0)) with p.1 = ξ₁, B p
          ≤ ∑ p ∈ (T.filter (fun p => ¬ p.1 = 0)) with p.1 = ξ₁,
              (1 + ‖τ ξ₁ + b * mixedEmbedding K p.2‖)⁻¹ ^ kk K := by
            refine Finset.sum_le_sum fun p hp => ?_
            have hp1 : p.1 = ξ₁ := (Finset.mem_filter.mp hp).2
            rw [← hp1]
            exact hBk p
        _ = ∑ ξ ∈ ((T.filter (fun p => ¬ p.1 = 0)).filter fun p => p.1 = ξ₁).image Prod.snd,
              (1 + ‖τ ξ₁ + b * mixedEmbedding K ξ‖)⁻¹ ^ kk K :=
            (Finset.sum_image (f := fun ξ => (1 + ‖τ ξ₁ + b * mixedEmbedding K ξ‖)⁻¹ ^ kk K)
              hinj).symm
        _ ≤ P * (1 + Nb⁻¹ ^ 2) := Htr (τ ξ₁) _ hS

    have hS1 : ∀ ξ ∈ (T.filter (fun p => ¬ p.1 = 0)).image Prod.fst, ξ ≠ 0 ∧ MemInv s ξ := by
      intro ξ hξ
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hξ
      have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
      exact ⟨(Finset.mem_filter.mp hp).2, (hT p hpT).2.1⟩
    have hPY : 0 ≤ P * (1 + Nb⁻¹ ^ 2) := mul_nonneg hP0 (by positivity)
    have hdecA : ∑ ξ₁ ∈ (T.filter (fun p => ¬ p.1 = 0)).image Prod.fst, A ξ₁
        ≤ P * Q * (1 + Na⁻¹ ^ 2) * min 1 (Na⁻¹ ^ N) := by
      have := Hdec_a _ hS1
      simpa only [hA] using this
    calc ∑ ξ₁ ∈ (T.filter (fun p => ¬ p.1 = 0)).image Prod.fst,
          ∑ p ∈ (T.filter (fun p => ¬ p.1 = 0)) with p.1 = ξ₁, A p.1 * B p
        ≤ ∑ ξ₁ ∈ (T.filter (fun p => ¬ p.1 = 0)).image Prod.fst, A ξ₁ * (P * (1 + Nb⁻¹ ^ 2)) :=
          Finset.sum_le_sum hinner
      _ = (∑ ξ₁ ∈ (T.filter (fun p => ¬ p.1 = 0)).image Prod.fst, A ξ₁) * (P * (1 + Nb⁻¹ ^ 2)) := by
          rw [Finset.sum_mul]
      _ ≤ (P * Q * (1 + Na⁻¹ ^ 2) * min 1 (Na⁻¹ ^ N)) * (P * (1 + Nb⁻¹ ^ 2)) :=
          mul_le_mul_of_nonneg_right hdecA hPY
      _ = P * (1 + Nb⁻¹ ^ 2) * (P * Q * (1 + Na⁻¹ ^ 2) * min 1 (Na⁻¹ ^ N)) := by ring

  have hma : 0 ≤ min 1 (Na⁻¹ ^ N) := le_min zero_le_one (by positivity)
  have hmb : 0 ≤ min 1 (Nb⁻¹ ^ N) := le_min zero_le_one (by positivity)
  have hX : 1 ≤ 1 + Na⁻¹ ^ 2 := le_add_of_nonneg_right (by positivity)
  generalize hX_def : 1 + Na⁻¹ ^ 2 = X at h0 h1 hX ⊢
  generalize hY_def : 1 + Nb⁻¹ ^ 2 = Y at h0 h1 ⊢
  generalize hma_def : min 1 (Na⁻¹ ^ N) = ma at h0 h1 hma ⊢
  generalize hmb_def : min 1 (Nb⁻¹ ^ N) = mb at h0 h1 hmb ⊢
  have hY0 : 0 ≤ Y := by rw [← hY_def]; positivity
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have e1 : P * Q * Y * mb ≤ (P * Q + P * P * Q) * X * Y * mb := by
    have h1' : P * Q * Y * mb ≤ P * Q * Y * mb * X :=
      le_mul_of_one_le_right (mul_nonneg (mul_nonneg (mul_nonneg hP0 hQ0) hY0) hmb) hX
    have h2' : P * Q * Y * mb * X ≤ (P * Q + P * P * Q) * X * Y * mb := by
      have : P * Q ≤ P * Q + P * P * Q :=
        le_add_of_nonneg_right (mul_nonneg (mul_nonneg hP0 hP0) hQ0)
      calc P * Q * Y * mb * X = (P * Q) * (X * Y * mb) := by ring
        _ ≤ (P * Q + P * P * Q) * (X * Y * mb) :=
            mul_le_mul_of_nonneg_right this (mul_nonneg (mul_nonneg hX0 hY0) hmb)
        _ = (P * Q + P * P * Q) * X * Y * mb := by ring
    exact h1'.trans h2'
  have e2 : P * Y * (P * Q * X * ma) ≤ (P * Q + P * P * Q) * X * Y * ma := by
    have : P * P * Q ≤ P * Q + P * P * Q := le_add_of_nonneg_left (mul_nonneg hP0 hQ0)
    calc P * Y * (P * Q * X * ma) = (P * P * Q) * (X * Y * ma) := by ring
      _ ≤ (P * Q + P * P * Q) * (X * Y * ma) :=
          mul_le_mul_of_nonneg_right this (mul_nonneg (mul_nonneg hX0 hY0) hma)
      _ = (P * Q + P * P * Q) * X * Y * ma := by ring
  rw [hsplit]
  calc ∑ p ∈ T with p.1 = 0, A p.1 * B p + ∑ p ∈ T with ¬ p.1 = 0, A p.1 * B p
      ≤ P * Q * Y * mb + P * Y * (P * Q * X * ma) := add_le_add h0 h1
    _ ≤ (P * Q + P * P * Q) * X * Y * mb + (P * Q + P * P * Q) * X * Y * ma := add_le_add e1 e2
    _ = (P * Q + P * P * Q) * X * Y * (ma + mb) := by ring

end NumberField.mixedEmbedding.ShearedLatticeSol

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] {s : 𝓞 K} (hs : s ≠ 0) (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (a b : NumberField.mixedEmbedding.mixedSpace K),
        0 < NumberField.mixedEmbedding.norm a → 0 < NumberField.mixedEmbedding.norm b →
        ∀ (τ : K → NumberField.mixedEmbedding.mixedSpace K), τ 0 = 0 → ∀ (T : Finset (K × K)),
          (∀ p ∈ T, p ≠ 0 ∧ (∃ c : 𝓞 K, (c : K) = (s : K) * p.1) ∧
            (∃ c : 𝓞 K, (c : K) = (s : K) * p.2)) →
          ∑ p ∈ T, ((1 + ‖a * NumberField.mixedEmbedding K p.1‖) ^ M)⁻¹ *
              ((1 + ‖τ p.1 + b * NumberField.mixedEmbedding K p.2‖) ^ M)⁻¹
            ≤ C * (1 + (NumberField.mixedEmbedding.norm a)⁻¹ ^ 2)
                * (1 + (NumberField.mixedEmbedding.norm b)⁻¹ ^ 2)
                * (min 1 ((NumberField.mixedEmbedding.norm a)⁻¹ ^ N)
                    + min 1 ((NumberField.mixedEmbedding.norm b)⁻¹ ^ N)) :=
  NumberField.mixedEmbedding.ShearedLatticeSol.main hs N

end S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_mul_pow_mul_inv_one_add_norm_add_mul_pow_le (solution)
