-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/8efc943d-6a78-52f4-bcc8-ed82e35e22a1

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat

open scoped NumberField Classical

noncomputable section

namespace LSQ

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

theorem isReal_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]; exact Rat.isReal_infinitePlace

def w₀ : {w : InfinitePlace ℚ // w.IsReal} := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

scoped instance : Unique {w : InfinitePlace ℚ // w.IsReal} where
  default := w₀
  uniq := fun w => Subtype.ext (Subsingleton.elim _ _)

scoped instance : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
  ⟨fun w => (not_isComplex_iff_isReal.2 (isReal_rat w.1)) w.2⟩

def E (x : mixedSpace ℚ) : ℝ := x.1 w₀

theorem E_add (x y : mixedSpace ℚ) : E (x + y) = E x + E y := rfl
theorem E_mul (x y : mixedSpace ℚ) : E (x * y) = E x * E y := rfl

theorem E_embedding (q : ℚ) : E (mixedEmbedding ℚ q) = (q : ℝ) := by
  show (mixedEmbedding ℚ q).1 w₀ = (q : ℝ)
  rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
  exact eq_ratCast _ q

theorem norm_eq_abs_E (x : mixedSpace ℚ) : ‖x‖ = |E x| := by
  rw [Prod.norm_def]
  have h2 : ‖x.2‖ = 0 := by
    rw [Pi.norm_def]; simp [Finset.univ_eq_empty]
  have h1 : ‖x.1‖ = |E x| := by
    rw [Pi.norm_def, Finset.univ_unique, Finset.sup_singleton]
    show ((‖x.1 default‖₊ : NNReal) : ℝ) = |x.1 w₀|
    rw [coe_nnnorm, Real.norm_eq_abs]; rfl
  rw [h1, h2, max_eq_left (abs_nonneg _)]

theorem mnorm_eq_abs_E (x : mixedSpace ℚ) : mixedEmbedding.norm x = |E x| := by
  rw [mixedEmbedding.norm_apply, Fintype.prod_subsingleton _ Rat.infinitePlace,
    normAtPlace_apply_of_isReal Rat.isReal_infinitePlace, Real.norm_eq_abs]
  have : Rat.infinitePlace.mult = 1 := by rw [mult, if_pos Rat.isReal_infinitePlace]
  rw [this, pow_one]; rfl

theorem one_le_abs_coe {s : 𝓞 ℚ} (hs : s ≠ 0) : 1 ≤ |((s : ℚ) : ℝ)| := by
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (s : ℚ) = n := ⟨Rat.ringOfIntegersEquiv s, by
    rw [Rat.ringOfIntegersEquiv_apply_coe]⟩
  have hn0 : n ≠ 0 := by
    intro h; apply hs
    have : (s : ℚ) = 0 := by rw [hn, h]; simp
    exact_mod_cast this
  rw [hn]; push_cast
  exact_mod_cast Int.one_le_abs hn0

theorem sep_of_memInv {s : 𝓞 ℚ} (hs : s ≠ 0) {ξ η : ℚ} (hξ : ∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * ξ)
    (hη : ∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * η) (hne : ξ ≠ η) :
    |((s : ℚ) : ℝ)|⁻¹ ≤ |((ξ : ℝ)) - (η : ℝ)| := by
  obtain ⟨c, hc⟩ := hξ
  obtain ⟨d, hd⟩ := hη
  have hcd : c - d ≠ 0 := by
    intro h
    have : (s : ℚ) * (ξ - η) = 0 := by
      have : ((c - d : 𝓞 ℚ) : ℚ) = 0 := by rw [h]; rfl
      push_cast at this; linear_combination this + 0 * hc - 0 * hd + (hd - hc)
    rcases mul_eq_zero.1 this with h1 | h1
    · exact hs (by exact_mod_cast h1)
    · exact hne (sub_eq_zero.1 h1)
  have h1 := one_le_abs_coe hcd
  have hs1 := one_le_abs_coe hs
  have h2 : (((c - d : 𝓞 ℚ) : ℚ) : ℝ) = ((s : ℚ) : ℝ) * ((ξ : ℝ) - (η : ℝ)) := by
    have : ((c - d : 𝓞 ℚ) : ℚ) = (s : ℚ) * (ξ - η) := by push_cast; linear_combination hc - hd
    rw [this]; push_cast; ring
  rw [h2, abs_mul] at h1
  rw [inv_le_iff_one_le_mul₀ (by linarith)]
  linarith [mul_comm (|((s:ℚ):ℝ)|) (|(ξ:ℝ) - (η:ℝ)|)]

def Z₂ : ℝ := ∑' z : ℤ, ((1 + |(z : ℝ)|) ^ 2)⁻¹

theorem summable_Z₂ : Summable (fun z : ℤ => ((1 + |(z : ℝ)|) ^ 2)⁻¹) := by
  have hnat : Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) := by
    have := (Real.summable_one_div_nat_pow (p := 2)).2 one_lt_two
    have h2 := (summable_nat_add_iff 1).2 this
    refine (h2.congr fun n => ?_)
    push_cast; rw [one_div, add_comm]
  refine summable_int_iff_summable_nat_and_neg.2 ⟨?_, ?_⟩
  · refine hnat.congr fun n => ?_; simp [Nat.abs_cast]
  · refine hnat.congr fun n => ?_; simp [abs_neg, Nat.abs_cast]

theorem Z₂_nonneg : 0 ≤ Z₂ := tsum_nonneg fun z => by positivity

theorem weight_cell (x : ℝ) : ((1 + |x|) ^ 2)⁻¹ ≤ 4 * ((1 + |((⌊x⌋ : ℤ) : ℝ)|) ^ 2)⁻¹ := by
  have h1 : |((⌊x⌋ : ℤ) : ℝ)| ≤ |x| + 1 := by
    rw [abs_le]; constructor
    · have := Int.lt_floor_add_one x; have := abs_nonneg x; have := neg_abs_le x; linarith [Int.floor_le x]
    · have := Int.floor_le x; have := le_abs_self x; linarith
  have h2 : 1 + |((⌊x⌋ : ℤ) : ℝ)| ≤ 2 * (1 + |x|) := by linarith [abs_nonneg x]
  have h3 : (1 + |((⌊x⌋ : ℤ) : ℝ)|) ^ 2 ≤ 4 * (1 + |x|) ^ 2 := by nlinarith [abs_nonneg x, abs_nonneg ((⌊x⌋ : ℤ) : ℝ)]
  rw [show 4 * ((1 + |((⌊x⌋ : ℤ) : ℝ)|) ^ 2)⁻¹ = (4⁻¹ * (1 + |((⌊x⌋ : ℤ) : ℝ)|) ^ 2)⁻¹ by rw [mul_inv, inv_inv]]
  exact inv_anti₀ (by positivity) (by linarith)

theorem card_cell_le {ι : Type*} (S : Finset ι) (u : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r ≤ |u i - u j|) (z : ℤ)
    (hz : ∀ i ∈ S, ⌊u i⌋ = z) : (S.card : ℝ) ≤ r⁻¹ + 2 := by

  have hinj : Set.InjOn (fun i => ⌊u i / r⌋) S := by
    intro i hi j hj hij
    by_contra hne
    have h := hsep i hi j hj hne
    have h1 : |u i / r - u j / r| < 1 := by
      have e1 := Int.floor_le (u i / r)
      have e2 := Int.lt_floor_add_one (u j / r)
      have e3 := Int.floor_le (u j / r)
      have e4 := Int.lt_floor_add_one (u i / r)
      have e5 : ((⌊u i / r⌋ : ℤ) : ℝ) = ⌊u j / r⌋ := by exact_mod_cast hij
      rw [abs_sub_lt_iff]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hr, div_lt_one hr] at h1
    linarith
  have hmaps : ∀ i ∈ S, ⌊u i / r⌋ ∈ Finset.Icc ⌊(z : ℝ) / r⌋ ⌊((z : ℝ) + 1) / r⌋ := by
    intro i hi
    rw [Finset.mem_Icc]
    have h1 : (z : ℝ) ≤ u i := by rw [← hz i hi]; exact Int.floor_le _
    have h2 : u i < (z : ℝ) + 1 := by rw [← hz i hi]; exact Int.lt_floor_add_one _
    exact ⟨Int.floor_le_floor (div_le_div_of_nonneg_right h1 hr.le),
      Int.floor_le_floor (div_le_div_of_nonneg_right h2.le hr.le)⟩
  have hcard := Finset.card_le_card_of_injOn (fun i => ⌊u i / r⌋) hmaps hinj
  rw [Int.card_Icc] at hcard
  have h3 : (S.card : ℝ) ≤ ((⌊((z : ℝ) + 1) / r⌋ + 1 - ⌊(z : ℝ) / r⌋).toNat : ℝ) := by exact_mod_cast hcard
  refine h3.trans ?_
  have h4 : ((⌊((z : ℝ) + 1) / r⌋ + 1 - ⌊(z : ℝ) / r⌋ : ℤ) : ℝ) ≤ r⁻¹ + 2 := by
    push_cast
    have := Int.floor_le (((z : ℝ) + 1) / r); have := Int.lt_floor_add_one ((z : ℝ) / r)
    have : ((z : ℝ) + 1) / r = (z : ℝ) / r + r⁻¹ := by rw [add_div, one_div]
    linarith
  rcases le_or_gt 0 (⌊((z : ℝ) + 1) / r⌋ + 1 - ⌊(z : ℝ) / r⌋) with h5 | h5
  · rw [show (((⌊((z : ℝ) + 1) / r⌋ + 1 - ⌊(z : ℝ) / r⌋).toNat : ℕ) : ℝ) = ((⌊((z : ℝ) + 1) / r⌋ + 1 - ⌊(z : ℝ) / r⌋ : ℤ) : ℝ) by
      rw [← Int.toNat_of_nonneg h5]; push_cast; rw [Int.toNat_of_nonneg h5]]
    exact h4
  · rw [Int.toNat_of_nonpos h5.le]; push_cast; positivity

theorem count_shift {ι : Type*} (S : Finset ι) (u : ι → ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r ≤ |u i - u j|) (t : ℝ) :
    ∑ i ∈ S, ((1 + |t + u i|) ^ 2)⁻¹ ≤ 8 * Z₂ * (1 + r⁻¹) := by

  set c : ι → ℤ := fun i => ⌊t + u i⌋ with hc
  have hsep' : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → r ≤ |(t + u i) - (t + u j)| := by
    intro i hi j hj hij; rw [add_sub_add_left_eq_sub]; exact hsep i hi j hj hij
  rw [← Finset.sum_fiberwise_of_maps_to (g := c) (fun i hi => Finset.mem_image_of_mem c hi)]
  have hfib : ∀ z ∈ S.image c, ∑ i ∈ S.filter (fun i => c i = z), ((1 + |t + u i|) ^ 2)⁻¹ ≤
      (r⁻¹ + 2) * (4 * ((1 + |(z : ℝ)|) ^ 2)⁻¹) := by
    intro z _
    calc ∑ i ∈ S.filter (fun i => c i = z), ((1 + |t + u i|) ^ 2)⁻¹
        ≤ ∑ i ∈ S.filter (fun i => c i = z), 4 * ((1 + |(z : ℝ)|) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_filter] at hi
          have := weight_cell (t + u i)
          rw [show ⌊t + u i⌋ = z from hi.2] at this
          exact this
      _ = ((S.filter (fun i => c i = z)).card : ℝ) * (4 * ((1 + |(z : ℝ)|) ^ 2)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (r⁻¹ + 2) * (4 * ((1 + |(z : ℝ)|) ^ 2)⁻¹) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          refine card_cell_le _ (fun i => t + u i) hr (fun i hi j hj hij => ?_) z (fun i hi => ?_)
          · exact hsep' i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij
          · exact (Finset.mem_filter.1 hi).2
  calc ∑ z ∈ S.image c, ∑ i ∈ S.filter (fun i => c i = z), ((1 + |t + u i|) ^ 2)⁻¹
      ≤ ∑ z ∈ S.image c, (r⁻¹ + 2) * (4 * ((1 + |(z : ℝ)|) ^ 2)⁻¹) := Finset.sum_le_sum hfib
    _ = 4 * (r⁻¹ + 2) * ∑ z ∈ S.image c, ((1 + |(z : ℝ)|) ^ 2)⁻¹ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun z _ => by ring
    _ ≤ 4 * (r⁻¹ + 2) * Z₂ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact summable_Z₂.sum_le_tsum _ (fun z _ => by positivity)
    _ ≤ 8 * Z₂ * (1 + r⁻¹) := by nlinarith [Z₂_nonneg, inv_pos.2 hr]

theorem transl_count {s : 𝓞 ℚ} (hs : s ≠ 0) {β : ℝ} (hβ : 0 < |β|) (t : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (S : Finset ℚ) (hS : ∀ ξ ∈ S, ∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * ξ) :
    ∑ ξ ∈ S, ((1 + |t + β * (ξ : ℝ)|) ^ M)⁻¹ ≤ 8 * Z₂ * |((s : ℚ) : ℝ)| * (1 + |β|⁻¹) := by
  have hs1 := one_le_abs_coe hs
  have hsep : ∀ ξ ∈ S, ∀ η ∈ S, ξ ≠ η → |β| * |((s : ℚ) : ℝ)|⁻¹ ≤ |β * (ξ : ℝ) - β * (η : ℝ)| := by
    intro ξ hξ η hη hne
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (sep_of_memInv hs (hS ξ hξ) (hS η hη) hne) (abs_nonneg _)
  have hr : 0 < |β| * |((s : ℚ) : ℝ)|⁻¹ := by positivity
  have h1 : ∀ ξ ∈ S, ((1 + |t + β * (ξ : ℝ)|) ^ M)⁻¹ ≤ ((1 + |t + β * (ξ : ℝ)|) ^ 2)⁻¹ := by
    intro ξ _
    refine inv_anti₀ (by positivity) ?_
    exact pow_le_pow_right₀ (by linarith [abs_nonneg (t + β * (ξ : ℝ))]) hM
  refine (Finset.sum_le_sum h1).trans ?_
  refine (count_shift S (fun ξ => β * (ξ : ℝ)) hr hsep t).trans ?_
  rw [mul_inv, inv_inv]
  have hZ := Z₂_nonneg
  have : 1 + |β|⁻¹ * |((s : ℚ) : ℝ)| ≤ |((s : ℚ) : ℝ)| * (1 + |β|⁻¹) := by nlinarith [inv_pos.2 hβ]
  calc 8 * Z₂ * (1 + |β|⁻¹ * |((s : ℚ) : ℝ)|) ≤ 8 * Z₂ * (|((s : ℚ) : ℝ)| * (1 + |β|⁻¹)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = 8 * Z₂ * |((s : ℚ) : ℝ)| * (1 + |β|⁻¹) := by ring

theorem decay_count {s : 𝓞 ℚ} (hs : s ≠ 0) {γ : ℝ} (hγ : 0 < |γ|) (N : ℕ)
    (S : Finset ℚ) (hS : ∀ ξ ∈ S, ξ ≠ 0 ∧ ∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * ξ) :
    ∑ ξ ∈ S, ((1 + |γ * (ξ : ℝ)|) ^ (N + 2))⁻¹ ≤
      8 * Z₂ * |((s : ℚ) : ℝ)| ^ (N + 1) * (1 + |γ|⁻¹) * min 1 (|γ|⁻¹ ^ N) := by
  set σ : ℝ := |((s : ℚ) : ℝ)| with hσ
  have hs1 : 1 ≤ σ := one_le_abs_coe hs

  have hlow : ∀ ξ ∈ S, |γ| * σ⁻¹ ≤ |γ * (ξ : ℝ)| := by
    intro ξ hξ
    obtain ⟨hξ0, hmem⟩ := hS ξ hξ
    have h := sep_of_memInv hs hmem ⟨0, by simp⟩ hξ0
    rw [Rat.cast_zero, sub_zero] at h
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

  have hdec : ((1 + |γ| * σ⁻¹) ^ N)⁻¹ ≤ σ ^ N * min 1 (|γ|⁻¹ ^ N) := by
    rw [mul_min_of_nonneg _ _ (by positivity), le_min_iff]; constructor
    · rw [mul_one]
      calc ((1 + |γ| * σ⁻¹) ^ N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [(by positivity : 0 ≤ |γ| * σ⁻¹)]))
        _ ≤ σ ^ N := one_le_pow₀ hs1
    · have h1 : |γ| * σ⁻¹ ≤ 1 + |γ| * σ⁻¹ := by linarith
      have h2 : (|γ| * σ⁻¹) ^ N ≤ (1 + |γ| * σ⁻¹) ^ N := pow_le_pow_left₀ (by positivity) h1 N
      calc ((1 + |γ| * σ⁻¹) ^ N)⁻¹ ≤ ((|γ| * σ⁻¹) ^ N)⁻¹ := inv_anti₀ (by positivity) h2
        _ = σ ^ N * |γ|⁻¹ ^ N := by rw [mul_pow, mul_inv, ← inv_pow, ← inv_pow, inv_inv, mul_comm]
  have h1 : ∀ ξ ∈ S, ((1 + |γ * (ξ : ℝ)|) ^ (N + 2))⁻¹ ≤
      ((1 + |γ| * σ⁻¹) ^ N)⁻¹ * ((1 + |0 + γ * (ξ : ℝ)|) ^ 2)⁻¹ := by
    intro ξ hξ
    rw [zero_add, pow_add, mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine inv_anti₀ (by positivity) ?_
    exact pow_le_pow_left₀ (by positivity) (by linarith [hlow ξ hξ]) N
  refine (Finset.sum_le_sum h1).trans ?_
  rw [← Finset.mul_sum]
  have hsep : ∀ ξ ∈ S, ∀ η ∈ S, ξ ≠ η → |γ| * σ⁻¹ ≤ |γ * (ξ : ℝ) - γ * (η : ℝ)| := by
    intro ξ hξ η hη hne
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (sep_of_memInv hs (hS ξ hξ).2 (hS η hη).2 hne) (abs_nonneg _)
  have hcount := count_shift S (fun ξ => γ * (ξ : ℝ)) (by positivity : 0 < |γ| * σ⁻¹) hsep 0
  have hZ := Z₂_nonneg
  calc ((1 + |γ| * σ⁻¹) ^ N)⁻¹ * ∑ ξ ∈ S, ((1 + |0 + γ * (ξ : ℝ)|) ^ 2)⁻¹
      ≤ (σ ^ N * min 1 (|γ|⁻¹ ^ N)) * (8 * Z₂ * (1 + (|γ| * σ⁻¹)⁻¹)) :=
        mul_le_mul hdec hcount (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
    _ ≤ (σ ^ N * min 1 (|γ|⁻¹ ^ N)) * (8 * Z₂ * (σ * (1 + |γ|⁻¹))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by positivity)) (by positivity)
        rw [mul_inv, inv_inv]; nlinarith [inv_pos.2 hγ]
    _ = 8 * Z₂ * σ ^ (N + 1) * (1 + |γ|⁻¹) * min 1 (|γ|⁻¹ ^ N) := by rw [pow_succ]; ring

end LSQ
p2m_reactivate "P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat.LSQ"

open LSQ NumberField NumberField.mixedEmbedding in
theorem solution
    {s : 𝓞 ℚ} (hs : s ≠ 0) (N : ℕ) :
    ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (a b : NumberField.mixedEmbedding.mixedSpace ℚ),
        0 < NumberField.mixedEmbedding.norm a → 0 < NumberField.mixedEmbedding.norm b →
        ∀ (τ : ℚ → NumberField.mixedEmbedding.mixedSpace ℚ), τ 0 = 0 →
        ∀ (T : Finset (ℚ × ℚ)),
          (∀ p ∈ T, p ≠ 0 ∧ (∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * p.1) ∧
            (∃ c : 𝓞 ℚ, (c : ℚ) = (s : ℚ) * p.2)) →
          ∑ p ∈ T, ((1 + ‖a * NumberField.mixedEmbedding ℚ p.1‖) ^ M)⁻¹ *
              ((1 + ‖τ p.1 + b * NumberField.mixedEmbedding ℚ p.2‖) ^ M)⁻¹
            ≤ C * (1 + (NumberField.mixedEmbedding.norm a)⁻¹)
                * (1 + (NumberField.mixedEmbedding.norm b)⁻¹)
                * (min 1 ((NumberField.mixedEmbedding.norm a)⁻¹ ^ N)
                    + min 1 ((NumberField.mixedEmbedding.norm b)⁻¹ ^ N)) := by
  set σ : ℝ := |((s : ℚ) : ℝ)| with hσ
  have hs1 : 1 ≤ σ := one_le_abs_coe hs
  set C₁ : ℝ := 8 * Z₂ * σ with hC₁
  set C₂ : ℝ := 8 * Z₂ * σ ^ (N + 1) with hC₂
  have hZ := Z₂_nonneg
  refine ⟨N + 2, C₂ + C₁ * C₂, by positivity, ?_⟩
  intro a b ha hb τ hτ T hT
  set α : ℝ := E a with hα
  set β : ℝ := E b with hβ
  rw [mnorm_eq_abs_E] at ha hb
  simp only [mnorm_eq_abs_E, norm_eq_abs_E, E_add, E_mul, E_embedding]

  rw [← Finset.sum_filter_add_sum_filter_not T (fun p => p.1 = 0)]

  have part0 : ∑ p ∈ T.filter (fun p => p.1 = 0),
      ((1 + |E a * ((p.1 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ * ((1 + |E (τ p.1) + E b * ((p.2 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ ≤
      C₂ * (1 + |E b|⁻¹) * min 1 (|E b|⁻¹ ^ N) := by
    have e1 : ∀ p ∈ T.filter (fun p => p.1 = 0),
        ((1 + |E a * ((p.1 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ * ((1 + |E (τ p.1) + E b * ((p.2 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ =
        ((1 + |E b * ((p.2 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [hp.2, hτ]
      simp [E]
    rw [Finset.sum_congr rfl e1]

    have hinj : Set.InjOn (fun p : ℚ × ℚ => p.2) (T.filter (fun p => p.1 = 0)) := by
      intro p hp q hq h
      rw [Finset.mem_coe, Finset.mem_filter] at hp hq
      exact Prod.ext (hp.2.trans hq.2.symm) h
    rw [← Finset.sum_image (f := fun ξ : ℚ => ((1 + |E b * ((ξ : ℚ) : ℝ)|) ^ (N + 2))⁻¹) hinj]
    refine decay_count hs hb N _ fun ξ hξ => ?_
    rw [Finset.mem_image] at hξ
    obtain ⟨p, hp, rfl⟩ := hξ
    rw [Finset.mem_filter] at hp
    obtain ⟨hp0, -, h2⟩ := hT p hp.1
    refine ⟨fun h => hp0 (Prod.ext hp.2 h), h2⟩

  have part1 : ∑ p ∈ T.filter (fun p => ¬ p.1 = 0),
      ((1 + |E a * ((p.1 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ * ((1 + |E (τ p.1) + E b * ((p.2 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ ≤
      C₁ * (1 + |E b|⁻¹) * (C₂ * (1 + |E a|⁻¹) * min 1 (|E a|⁻¹ ^ N)) := by
    set T₁ := T.filter (fun p => ¬ p.1 = 0) with hT₁
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℚ × ℚ => p.1) (fun p hp => Finset.mem_image_of_mem _ hp)]
    have hinner : ∀ x ∈ T₁.image (fun p : ℚ × ℚ => p.1),
        ∑ p ∈ T₁.filter (fun p => p.1 = x),
          ((1 + |E a * ((p.1 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ * ((1 + |E (τ p.1) + E b * ((p.2 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ ≤
        ((1 + |E a * ((x : ℚ) : ℝ)|) ^ (N + 2))⁻¹ * (C₁ * (1 + |E b|⁻¹)) := by
      intro x hx
      have e1 : ∀ p ∈ T₁.filter (fun p => p.1 = x),
          ((1 + |E a * ((p.1 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ * ((1 + |E (τ p.1) + E b * ((p.2 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ =
          ((1 + |E a * ((x : ℚ) : ℝ)|) ^ (N + 2))⁻¹ * ((1 + |E (τ x) + E b * ((p.2 : ℚ) : ℝ)|) ^ (N + 2))⁻¹ := by
        intro p hp; rw [Finset.mem_filter] at hp; rw [hp.2]
      rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hinj : Set.InjOn (fun p : ℚ × ℚ => p.2) (T₁.filter (fun p => p.1 = x)) := by
        intro p hp q hq h
        rw [Finset.mem_coe, Finset.mem_filter] at hp hq
        exact Prod.ext (hp.2.trans hq.2.symm) h
      rw [← Finset.sum_image (f := fun ξ : ℚ => ((1 + |E (τ x) + E b * ((ξ : ℚ) : ℝ)|) ^ (N + 2))⁻¹) hinj]
      refine transl_count hs hb (E (τ x)) (N + 2) (by omega) _ fun ξ hξ => ?_
      rw [Finset.mem_image] at hξ
      obtain ⟨p, hp, rfl⟩ := hξ
      rw [Finset.mem_filter] at hp
      exact (hT p (Finset.mem_filter.1 hp.1).1).2.2
    refine (Finset.sum_le_sum hinner).trans ?_
    rw [← Finset.sum_mul]
    rw [mul_comm (C₁ * (1 + |E b|⁻¹))]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine decay_count hs ha N _ fun ξ hξ => ?_
    rw [Finset.mem_image] at hξ
    obtain ⟨p, hp, rfl⟩ := hξ
    rw [hT₁, Finset.mem_filter] at hp
    exact ⟨hp.2, (hT p hp.1).2.1⟩
  refine (add_le_add part0 part1).trans ?_

  have ha1 : 1 ≤ 1 + |E a|⁻¹ := by have := inv_pos.2 ha; linarith
  have hb1 : 1 ≤ 1 + |E b|⁻¹ := by have := inv_pos.2 hb; linarith
  have hma : 0 ≤ min 1 (|E a|⁻¹ ^ N) := le_min zero_le_one (by positivity)
  have hmb : 0 ≤ min 1 (|E b|⁻¹ ^ N) := le_min zero_le_one (by positivity)
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hB0 : 0 ≤ 1 + |E b|⁻¹ := by positivity
  have hA0 : 0 ≤ 1 + |E a|⁻¹ := by positivity
  have key1 : C₂ * (1 + |E b|⁻¹) * min 1 (|E b|⁻¹ ^ N) * 1 ≤ C₂ * (1 + |E b|⁻¹) * min 1 (|E b|⁻¹ ^ N) * (1 + |E a|⁻¹) :=
    mul_le_mul_of_nonneg_left ha1 (by positivity)
  have P1 : 0 ≤ C₂ * (1 + |E a|⁻¹) * (1 + |E b|⁻¹) * min 1 (|E a|⁻¹ ^ N) := by positivity
  have P2 : 0 ≤ C₁ * C₂ * (1 + |E a|⁻¹) * (1 + |E b|⁻¹) * min 1 (|E b|⁻¹ ^ N) := by positivity
  linarith [key1, P1, P2]

end
p2m_reactivate "P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat.LSQ"

end S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_sum_inv_one_add_norm_pow_mul_inv_one_add_norm_add_mul_pow_le_mul_one_add_inv_rat (solution)
