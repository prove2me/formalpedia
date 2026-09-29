-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c6be5100-c7cd-5826-9a3d-18f28a096148

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers

set_option autoImplicit false

p2m_open_scoped "NumberField P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers.NumberField"
p2m_open "NumberField P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers.NumberField NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers.NumberField.mixedEmbedding Module"

namespace NumberField
p2m_export "NumberField" "mixedEmbedding.norm_apply RingOfIntegers mixedEmbedding mixedEmbedding.mixedSpace InfinitePlace RingOfIntegers.coe_eq_algebraMap mixedEmbedding.norm"
namespace mixedEmbedding
p2m_export "NumberField.mixedEmbedding" "index normAtPlace norm_eq_norm normAtPlace_nonneg mixedSpace normAtPlace_apply_of_isReal normAtPlace_apply_of_isComplex"
namespace LatticeDecaySol
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

theorem one_le_norm_mixedEmbedding {ξ : 𝓞 K} (hξ : ξ ≠ 0) :
    1 ≤ mixedEmbedding.norm (mixedEmbedding K (ξ : K)) := by
  rw [norm_eq_norm, ← Algebra.coe_norm_int, Rat.cast_abs, Rat.cast_intCast]
  have h : Algebra.norm ℤ ξ ≠ 0 := Algebra.norm_ne_zero_iff.mpr hξ
  exact_mod_cast Int.one_le_abs h

theorem norm_le_norm_mul_pow {a : mixedSpace K} (ha : 1 ≤ mixedEmbedding.norm a)
    {ξ : 𝓞 K} (hξ : ξ ≠ 0) :
    mixedEmbedding.norm a ≤ ‖a * mixedEmbedding K (ξ : K)‖ ^ finrank ℚ K := by
  refine le_trans ?_ (norm_le_norm_pow _)
  rw [map_mul]
  exact le_mul_of_one_le_right (zero_le_one.trans ha) (one_le_norm_mixedEmbedding hξ)

theorem one_le_norm_mul {a : mixedSpace K} (ha : 1 ≤ mixedEmbedding.norm a)
    {ξ : 𝓞 K} (hξ : ξ ≠ 0) : 1 ≤ ‖a * mixedEmbedding K (ξ : K)‖ := by
  by_contra h
  rw [not_le] at h
  have h1 : ‖a * mixedEmbedding K (ξ : K)‖ ^ finrank ℚ K < 1 :=
    pow_lt_one₀ (norm_nonneg _) h Module.finrank_pos.ne'
  exact absurd (ha.trans (norm_le_norm_mul_pow ha hξ)) (not_le.mpr h1)

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

theorem summable_weight (k : ℕ) (hk : Fintype.card (CoordIdx K) < k) :
    Summable fun z : intLattice K => (1 + ‖(z : CoordIdx K → ℝ)‖)⁻¹ ^ k := by
  have hrank : finrank ℤ (intLattice K) < k := by
    rw [ZLattice.rank ℝ (intLattice K), finrank_fintype_fun_eq_card]
    exact hk
  have hg := ZLattice.summable_norm_pow_inv (intLattice K) k hrank
  refine (Finset.summable_compl_iff ({0} : Finset (intLattice K))).mp ?_
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    (hg.comp_injective Subtype.val_injective)
  have hz : (z : intLattice K) ≠ 0 := by
    have := z.2
    simpa only [Finset.mem_singleton] using this
  simp only [Function.comp_apply]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  rw [← Submodule.coe_norm]
  exact inv_anti₀ (norm_pos_iff.mpr hz) (by linarith [norm_nonneg (z : intLattice K)])

theorem main (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (Φ : SchwartzMap (mixedSpace K) V) (a : mixedSpace K),
        1 ≤ mixedEmbedding.norm a →
          Summable (fun ξ : 𝓞 K => ‖Φ (a * mixedEmbedding K (ξ : K))‖) ∧
          ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖Φ (a * mixedEmbedding K ((ξ : 𝓞 K) : K))‖ ≤
            C * SchwartzMap.seminorm ℝ M 0 Φ * (mixedEmbedding.norm a)⁻¹ ^ N := by
  set n := finrank ℚ K with hn
  set k := Fintype.card (CoordIdx K) + 1 with hk
  set W : intLattice K → ℝ := fun z => (1 + ‖(z : CoordIdx K → ℝ)‖)⁻¹ ^ k with hW
  have hWs : Summable W := summable_weight k (Nat.lt_succ_self _)
  have hW0 : ∀ z, 0 ≤ W z := fun z => by positivity
  refine ⟨n * N + k, 4 ^ k * ∑' z, W z, mul_nonneg (by positivity) (tsum_nonneg hW0),
    fun Φ a ha => ?_⟩
  set S := SchwartzMap.seminorm ℝ (n * N + k) 0 Φ with hS_def
  have hS : 0 ≤ S := apply_nonneg _ _
  set A := mixedEmbedding.norm a with hA_def
  have hA : 0 < A := zero_lt_one.trans_le ha
  have hB : 0 ≤ 4 ^ k * S * A⁻¹ ^ N := mul_nonneg (mul_nonneg (by positivity) hS) (by positivity)

  let R : 𝓞 K → intLattice K := fun ξ => ⟨rnd (a * mixedEmbedding K (ξ : K)), rnd_mem _⟩
  have hRinj : Function.Injective R := by
    intro ξ η hξη
    by_contra hne
    have hlt := norm_sub_lt_one_of_rnd_eq (congrArg Subtype.val hξη)
    have hsub : (ξ - η : 𝓞 K) ≠ 0 := sub_ne_zero.mpr hne
    have hge := one_le_norm_mul ha hsub
    rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_sub, mul_sub,
      ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap] at hge
    linarith

  have hpt : ∀ ξ : 𝓞 K, ξ ≠ 0 →
      ‖Φ (a * mixedEmbedding K (ξ : K))‖ ≤ (4 ^ k * S * A⁻¹ ^ N) * W (R ξ) := by
    intro ξ hξ
    set v := a * mixedEmbedding K (ξ : K) with hv_def
    have hv1 : 1 ≤ ‖v‖ := one_le_norm_mul ha hξ
    have hv0 : 0 < ‖v‖ := one_pos.trans_le hv1
    have hvA : A ≤ ‖v‖ ^ n := norm_le_norm_mul_pow ha hξ

    have h1 : ‖Φ v‖ ≤ S * ‖v‖⁻¹ ^ (n * N + k) := by
      have := SchwartzMap.norm_pow_mul_le_seminorm ℝ Φ (n * N + k) v
      rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hv0 _), mul_comm]
      exact this

    have h2 : ‖v‖⁻¹ ^ (n * N) ≤ A⁻¹ ^ N := by
      have h : ‖v‖⁻¹ ^ n ≤ A⁻¹ := by
        rw [inv_pow]
        exact inv_anti₀ hA hvA
      rw [pow_mul]
      exact pow_le_pow_left₀ (by positivity) h N
    have h3 : ‖v‖⁻¹ ^ k ≤ 4 ^ k * W (R ξ) := by
      have hR : ‖rnd v‖ ≤ 2 * ‖v‖ + 1 := norm_rnd_le v
      have h4 : 1 + ‖rnd v‖ ≤ 4 * ‖v‖ := by linarith
      have h5 : ‖v‖⁻¹ ≤ 4 * (1 + ‖rnd v‖)⁻¹ := by
        rw [show ‖v‖⁻¹ = 4 * (4 * ‖v‖)⁻¹ by field_simp]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) h4) (by norm_num)
      calc ‖v‖⁻¹ ^ k ≤ (4 * (1 + ‖rnd v‖)⁻¹) ^ k := pow_le_pow_left₀ (by positivity) h5 k
        _ = 4 ^ k * W (R ξ) := by rw [mul_pow]
    calc ‖Φ v‖ ≤ S * ‖v‖⁻¹ ^ (n * N + k) := h1
      _ = S * (‖v‖⁻¹ ^ (n * N) * ‖v‖⁻¹ ^ k) := by rw [pow_add]
      _ ≤ S * (A⁻¹ ^ N * (4 ^ k * W (R ξ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h2 h3 (by positivity) (by positivity)) hS
      _ = (4 ^ k * S * A⁻¹ ^ N) * W (R ξ) := by ring

  have hG : Summable fun ξ : 𝓞 K => (4 ^ k * S * A⁻¹ ^ N) * W (R ξ) :=
    (hWs.comp_injective hRinj).mul_left _

  have hfull : Summable (fun ξ : 𝓞 K => ‖Φ (a * mixedEmbedding K (ξ : K))‖) := by
    have h0 : Summable fun ξ : 𝓞 K =>
        if ξ = 0 then ‖Φ (a * mixedEmbedding K ((0 : 𝓞 K) : K))‖ else 0 := by
      refine summable_of_ne_finset_zero (s := {0}) fun ξ hξ => ?_
      rw [Finset.mem_singleton] at hξ
      exact if_neg hξ
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_) (hG.add h0)
    by_cases hξ : ξ = 0
    · subst hξ
      rw [if_pos rfl]
      exact le_add_of_nonneg_left (mul_nonneg hB (hW0 _))
    · rw [if_neg hξ, add_zero]
      exact hpt ξ hξ
  refine ⟨hfull, ?_⟩
  calc ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖Φ (a * mixedEmbedding K ((ξ : 𝓞 K) : K))‖
      ≤ ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, (4 ^ k * S * A⁻¹ ^ N) * W (R ξ) :=
        Summable.tsum_le_tsum (fun ξ => hpt ξ.1 ξ.2)
          (hfull.comp_injective Subtype.val_injective)
          (hG.comp_injective Subtype.val_injective)
    _ = (4 ^ k * S * A⁻¹ ^ N) * ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, W (R ξ) := tsum_mul_left
    _ ≤ (4 ^ k * S * A⁻¹ ^ N) * ∑' z, W z :=
        mul_le_mul_of_nonneg_left
          (tsum_comp_le_tsum_of_inj hWs hW0 (hRinj.comp Subtype.val_injective)) hB
    _ = 4 ^ k * (∑' z, W z) * S * A⁻¹ ^ N := by ring

end NumberField.mixedEmbedding.LatticeDecaySol

open scoped Classical in
theorem solution
    (K : Type*) [Field K] [NumberField K]
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (Φ : SchwartzMap (NumberField.mixedEmbedding.mixedSpace K) V)
        (a : NumberField.mixedEmbedding.mixedSpace K),
        1 ≤ NumberField.mixedEmbedding.norm a →
          Summable (fun ξ : 𝓞 K => ‖Φ (a * NumberField.mixedEmbedding K (ξ : K))‖) ∧
          ∑' ξ : {ξ : 𝓞 K // ξ ≠ 0}, ‖Φ (a * NumberField.mixedEmbedding K ((ξ : 𝓞 K) : K))‖ ≤
            C * SchwartzMap.seminorm ℝ M 0 Φ * (NumberField.mixedEmbedding.norm a)⁻¹ ^ N :=
  NumberField.mixedEmbedding.LatticeDecaySol.main V N

end S_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_bound_tsum_norm_schwartzMap_mul_ringOfIntegers (solution)
