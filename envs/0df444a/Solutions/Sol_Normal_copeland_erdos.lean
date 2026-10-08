-- Prove2me | solution 1 for Normal.copeland_erdos
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T15:29:50.5928+00:00
-- url     : https://prove2.me/submissions/7a433383-20d1-4e96-b2e3-ec12712e1a5e

import Init
import Mathlib
import Definitions.Def_Normal_Core

set_option autoImplicit false


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: Normal.Basic -/
section
set_option autoImplicit false


/-!
# Normal sequences and normal numbers: basic definitions

This file fixes the vocabulary shared by the formalizations of

* D. G. Champernowne, *The construction of decimals normal in the scale of ten*,
  J. London Math. Soc. 8 (1933), 254–260 (`papers/champernowne-1933.pdf`), and
* A. H. Copeland, P. Erdős, *Note on normal numbers*,
  Bull. Amer. Math. Soc. 52 (1946), 857–860 (`papers/copeland-erdos-1946.pdf`).

## Conventions

* A *digit sequence* is a function `s : ℕ → ℕ`; `s 0` is the first digit after the point.
* A *word* is a `List ℕ`; a word over base `b` has all entries `< b`.
* `count s w N` is the number of positions `i < N` at which the word `w` occurs in `s`
  (overlapping occurrences are counted). Champernowne's `G(x)` counts occurrences lying
  inside the first `x` digits; the two differ by at most `w.length`, so the limits agree.
* `IsNormalSeq b s` is Borel normality in base `b` exactly as defined on p. 254 of
  Champernowne and on p. 857 of Copeland–Erdős: every word of length `k` over base `b`
  occurs with limiting relative frequency `b⁻ᵏ`.
-/

open Filter Topology

namespace Normal

/-! ## Words and occurrences -/







/-! ## Base-`b` digits of real numbers -/







/-! ## Finite strings over base `b` -/



/-! ## Concatenating a sequence of words -/







end Normal

end

/- Original source header (imports hoisted):
import Normal.Basic
-/
/- Source module: Normal.Agafonov -/
section
set_option autoImplicit false


/-!
# Compatibility with the `agafonov` repository's definition of normality

The repository `xiangyazi24/agafonov` (branch `research-dot/agafonov-formalization-20261002`,
file `Agafonov/Target.lean`, commit `cb08d11`) defines normality of a sequence `x : ℕ → Fin b`
with integer arithmetic, in a form that avoids reals and truncated subtraction. That
repository is pinned to a different Lean toolchain (`v4.31.0-rc2`), so it is not a Lake
dependency here. Instead its three definitions are copied **verbatim** into the namespace
`Normal.Agafonov`, and we prove that they agree with `Normal.IsNormalSeq`:

* `count_eq_blockCount`: the two occurrence counters agree on corresponding words;
* `isNormalSeq_iff_isNormal`: `IsNormalSeq b (fun n => (x n : ℕ)) ↔ Agafonov.IsNormal x`.

Hence every normality theorem of this repository can be restated in the `agafonov` form.
-/

open Filter Topology

namespace Normal

namespace Agafonov

/-! ### Verbatim copies of the `agafonov` definitions -/







end Agafonov

/-! ### The occurrence counters agree -/





/-! ### Real-limit form versus integer `e`-form -/



/-! ### The two definitions of normality agree -/



end Normal

end

/- Original source header (imports hoisted):
import Normal.Basic
-/
/- Source module: Normal.Flatten -/
section
set_option autoImplicit false


/-!
# Basic facts about `Normal.flatten`

`flatten d L` is the infinite concatenation `L 0 ++ L 1 ++ ⋯`. When every `L i` is
nonempty its first `|L 0| + ⋯ + |L (J-1)|` entries are exactly
`(List.range J).flatMap L`, every entry lies in some `L i`, and flattening is associative.
-/

namespace Normal

variable {α : Type*}

/-! ### The finite concatenations `L 0 ++ ⋯ ++ L (J-1)` form a prefix chain -/



private theorem flatMap_range_prefix (L : ℕ → List α) {J J' : ℕ} (h : J ≤ J') :
    (List.range J).flatMap L <+: (List.range J').flatMap L := by
  induction J', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ J' _ ih =>
    rw [flatMap_range_succ]
    exact ih.trans (List.prefix_append _ _)



private theorem getD_of_prefix {l₁ l₂ : List α} (h : l₁ <+: l₂) {n : ℕ} (hn : n < l₁.length)
    (d : α) : l₂.getD n d = l₁.getD n d := by
  have hn' : n < l₂.length := lt_of_lt_of_le hn h.length_le
  rw [List.getD_eq_getElem _ _ hn, List.getD_eq_getElem _ _ hn', h.getElem hn]

/-- The entries of `flatten d L` below `|L 0 ++ ⋯ ++ L (J-1)|` are read off from that
finite concatenation. -/
theorem flatten_eq_getD {d : α} {L : ℕ → List α} (hne : ∀ i, L i ≠ []) (J n : ℕ)
    (hn : n < ((List.range J).flatMap L).length) :
    flatten d L n = ((List.range J).flatMap L).getD n d := by
  have h1 : n < ((List.range (n + 1)).flatMap L).length :=
    lt_of_lt_of_le (Nat.lt_succ_self n) (le_length_flatMap_range hne _)
  unfold flatten
  rcases le_total (n + 1) J with h | h
  · exact (getD_of_prefix (flatMap_range_prefix L h) h1 d).symm
  · exact getD_of_prefix (flatMap_range_prefix L h) hn d

/-- The first `|L 0 ++ ⋯ ++ L (J-1)|` entries of `flatten d L`, as a list. -/
theorem map_flatten_range {d : α} {L : ℕ → List α} (hne : ∀ i, L i ≠ []) (J : ℕ) :
    (List.range ((List.range J).flatMap L).length).map (flatten d L) =
      (List.range J).flatMap L := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [flatten_eq_getD hne J i h2, List.getD_eq_getElem _ _ h2]





end Normal

end

/- Original source header (imports hoisted):
import Normal.Basic
-/
/- Source module: Normal.Strs -/
section
set_option autoImplicit false


/-!
# The finite set `strs b n` of words of length `n` over base `b`
-/

namespace Normal

/-- `u ∈ strs b n` iff `u` has length `n` and all its entries are `< b`. -/
theorem mem_strs {b n : ℕ} {u : List ℕ} : u ∈ strs b n ↔ u.length = n ∧ ∀ d ∈ u, d < b := by
  induction n generalizing u with
  | zero => simp only [strs, Finset.mem_singleton, List.length_eq_zero_iff]; aesop
  | succ n ih =>
    cases u with
    | nil => simp [strs]
    | cons a t => simp [strs, ih, and_comm, and_left_comm]

/-- There are `bⁿ` words of length `n` over base `b`. -/
theorem card_strs (b n : ℕ) : (strs b n).card = b ^ n := by
  induction n with
  | zero => simp [strs]
  | succ n ih =>
    rw [strs, Finset.card_image_of_injective _ (fun p q h => by
      simpa [Prod.ext_iff] using h), Finset.card_product, ih, Finset.card_range, pow_succ,
      mul_comm]

end Normal

end

/- Original source header (imports hoisted):
import Normal.Flatten
import Normal.Strs
-/
/- Source module: Normal.LargeDeviation -/
section
set_option autoImplicit false


/-!
# The Copeland–Erdős counting lemma (large deviations for word counts)

Copeland–Erdős, p. 858, **Lemma**: *the number of integers up to `N` which are not
`(ε, k)` normal with respect to a given base `β` is less than `N^δ`, where
`δ = δ(ε, k, β) < 1`.*

We prove the form that is actually used (only the upper deviation is needed, see
`Normal.Blocks`): among the `bⁿ` words of length `n` over base `b`, those in which a fixed
word `w` occurs more than `(b^{-|w|} + ε) · n` times number at most `C · βⁿ` for some
`β < b`. Since a number below `bⁿ` is a word of length `n`, `C βⁿ = C N^{log_b β}`
recovers the lemma.

Proof (a Chernoff bound, replacing the paper's explicit binomial-tail estimate and its
Borel grouping step): split the occurrence positions by residue mod `k = |w|`; within one
residue class the windows are disjoint, so the exponential moment `∑ λ^{count}` over all
words factorises as `(bᵏ - 1 + λ)^m · b^{rest}`; Markov's inequality with a suitable
`λ > 1` gives the geometric saving.
-/

open Filter Topology

namespace Normal



theorem alc_zero (w v : List ℕ) : alc w 0 v = 0 := by simp [alc]

/-- Peeling off a first block `x` of length `|w|`. -/
theorem alc_succ_append {w x y : List ℕ} (hx : x.length = w.length) (m : ℕ) :
    alc w (m + 1) (x ++ y) = (if x = w then 1 else 0) + alc w m y := by
  unfold alc
  rw [Finset.sum_range_succ', add_comm]
  have hp : (w <+: x ++ y) ↔ x = w := by
    rw [List.prefix_iff_eq_take, ← hx, List.take_left]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  congr 1
  · simp only [mul_zero, List.drop_zero, hp]
  · apply Finset.sum_congr rfl
    intro j _
    have : List.drop (w.length * (j + 1)) (x ++ y) = List.drop (w.length * j) y := by
      rw [List.drop_append, List.drop_eq_nil_of_le (by rw [hx]; nlinarith)]
      simp only [List.nil_append, hx]
      congr 1
      rw [Nat.mul_succ]; omega
    rw [this]

/-- Words shorter than `w` have no aligned occurrences. -/
theorem alc_short {w v : List ℕ} (h : v.length < w.length) (m : ℕ) : alc w m v = 0 := by
  unfold alc
  apply Finset.sum_eq_zero
  intro j _
  rw [ite_eq_right_iff]
  intro hp
  exfalso
  have := hp.length_le
  simp at this
  omega

/-- Words of length `a + n` are exactly the concatenations of a word of length `a` and one
of length `n`. -/
theorem strs_add (b a n : ℕ) :
    strs b (a + n) = (strs b a ×ˢ strs b n).image (fun p => p.1 ++ p.2) := by
  ext u
  simp only [Finset.mem_image, Finset.mem_product, mem_strs, Prod.exists]
  constructor
  · rintro ⟨hl, hd⟩
    exact ⟨u.take a, u.drop a, ⟨⟨by simp; omega, fun d hd' => hd d (List.mem_of_mem_take hd')⟩,
      ⟨by simp; omega, fun d hd' => hd d (List.mem_of_mem_drop hd')⟩⟩, List.take_append_drop a u⟩
  · rintro ⟨x, y, ⟨⟨hx, hxd⟩, ⟨hy, hyd⟩⟩, rfl⟩
    refine ⟨by simp [hx, hy], fun d hd => ?_⟩
    rcases List.mem_append.1 hd with h | h
    exacts [hxd d h, hyd d h]

/-- A sum over words of length `a + n` splits as a double sum over the two blocks. -/
theorem sum_strs_add {M : Type*} [AddCommMonoid M] (b a n : ℕ) (g : List ℕ → M) :
    ∑ u ∈ strs b (a + n), g u = ∑ x ∈ strs b a, ∑ y ∈ strs b n, g (x ++ y) := by
  rw [strs_add, Finset.sum_image, Finset.sum_product]
  rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' h
  simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, mem_strs] at hxy hxy'
  have hl : x.length = x'.length := by rw [hxy.1.1, hxy'.1.1]
  obtain ⟨h1, h2⟩ := List.append_inj (by simpa using h) hl
  simp [h1, h2]

/-- `∑_{|x| = |w|} λ^{[x = w]} = b^{|w|} - 1 + λ`. -/
theorem sum_block {b : ℕ} {w : List ℕ} (hwb : w ∈ strs b w.length) (l : ℝ) :
    ∑ x ∈ strs b w.length, l ^ (if x = w then 1 else 0) = (b : ℝ) ^ w.length - 1 + l := by
  have : ∀ x : List ℕ, l ^ (if x = w then 1 else 0) = 1 + (if x = w then l - 1 else 0) := by
    intro x; split_ifs <;> simp
  simp only [this, Finset.sum_add_distrib, Finset.sum_const, card_strs, Finset.sum_ite_eq', hwb,
    ite_true, nsmul_eq_mul, mul_one]
  push_cast; ring

/-- Exponential moment of the aligned count: `∑_{|v| = n} λ^{alc} ≤ bⁿ ρ^{⌊n/|w|⌋}` whenever
`b^{|w|} - 1 + λ ≤ b^{|w|} ρ`. -/
theorem gen_bound {b : ℕ} {w : List ℕ} (hw : w ≠ []) (hwb : w ∈ strs b w.length) {l ρ : ℝ}
    (hl : 1 ≤ l) (hρ1 : 1 ≤ ρ) (hρ : (b : ℝ) ^ w.length - 1 + l ≤ (b : ℝ) ^ w.length * ρ) :
    ∀ m n : ℕ, ∑ v ∈ strs b n, l ^ (alc w m v) ≤ (b : ℝ) ^ n * ρ ^ (n / w.length) := by
  have hK : 0 < w.length := List.length_pos_iff.2 hw
  intro m
  induction m with
  | zero =>
    intro n
    simp only [alc_zero, pow_zero, Finset.sum_const, card_strs, nsmul_eq_mul, mul_one]
    push_cast
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hρ1)
  | succ m ih =>
    intro n
    rcases lt_or_ge n w.length with h | h
    · have : ∀ v ∈ strs b n, l ^ alc w (m + 1) v = 1 := fun v hv => by
        rw [alc_short (by rw [(mem_strs.1 hv).1]; exact h)]; simp
      rw [Finset.sum_congr rfl this]
      simp [card_strs, Nat.div_eq_of_lt h]
    · obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le h
      rw [sum_strs_add]
      have e : ∀ x ∈ strs b w.length, ∑ y ∈ strs b n', l ^ alc w (m + 1) (x ++ y)
          = l ^ (if x = w then 1 else 0) * ∑ y ∈ strs b n', l ^ alc w m y := by
        intro x hx
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [alc_succ_append (mem_strs.1 hx).1, pow_add]
      rw [Finset.sum_congr rfl e, ← Finset.sum_mul, sum_block hwb]
      have hB0 : (0 : ℝ) ≤ (b : ℝ) ^ w.length := by positivity
      calc _ ≤ ((b : ℝ) ^ w.length - 1 + l) * ((b : ℝ) ^ n' * ρ ^ (n' / w.length)) := by
              gcongr
              · linarith
              · exact ih n'
        _ ≤ ((b : ℝ) ^ w.length * ρ) * ((b : ℝ) ^ n' * ρ ^ (n' / w.length)) := by
              gcongr
        _ = _ := by
              rw [Nat.add_comm w.length n', Nat.add_div_right n' hK, pow_add, pow_succ]; ring

/-- Markov's inequality for the aligned count. -/
theorem markov {b : ℕ} {w : List ℕ} {l : ℝ} (hl : 1 ≤ l) (t : ℝ) (m n : ℕ) :
    (((strs b n).filter (fun v => t < alc w m v)).card : ℝ) * l ^ t
      ≤ ∑ v ∈ strs b n, l ^ (alc w m v) := by
  calc _ = ∑ v ∈ (strs b n).filter (fun v => t < alc w m v), l ^ t := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ v ∈ (strs b n).filter (fun v => t < alc w m v), l ^ (alc w m v) := by
          apply Finset.sum_le_sum
          intro v hv
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le hl (Finset.mem_filter.1 hv).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => pow_nonneg (by linarith) _)

theorem sum_range_mul_split (f : ℕ → ℕ) (K m : ℕ) :
    ∑ i ∈ Finset.range (K * m), f i
      = ∑ j ∈ Finset.range m, ∑ r ∈ Finset.range K, f (K * j + r) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Residue split: every occurrence position `i` is `r + |w| j` with `r < |w|`. -/
theorem occ_le_sum_alc {w : List ℕ} (hw : w ≠ []) (u : List ℕ) :
    occ w u ≤ ∑ r ∈ Finset.range w.length, alc w u.length (u.drop r) := by
  have hK : 0 < w.length := List.length_pos_iff.2 hw
  unfold occ alc
  calc _ ≤ ∑ i ∈ Finset.range (w.length * u.length), (if w <+: u.drop i then 1 else 0) :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.le_mul_of_pos_left _ hK))
    _ = _ := by
        rw [sum_range_mul_split, Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro j _
        rw [List.drop_drop, Nat.add_comm r]

/-- The numerical heart of the Chernoff bound: with `λ = 1 + εB/2`,
`1 + ε/2 < λ^{1/B + ε}`. -/
theorem real_key {B ε : ℝ} (hB : 0 < B) (hε : 0 < ε) :
    1 + ε / 2 < (1 + ε * B / 2) ^ (B⁻¹ + ε) := by
  set L := 1 + ε * B / 2 with hL
  have hεB := mul_pos hε hB
  have hL1 : 1 < L := by linarith
  have hL0 : 0 < L := by linarith
  have hq : 0 < B⁻¹ + ε := by positivity
  have h1 : 1 - L⁻¹ ≤ Real.log L := Real.one_sub_inv_le_log_of_pos hL0
  have h2 : Real.log L * (B⁻¹ + ε) + 1 ≤ L ^ (B⁻¹ + ε) := by
    rw [Real.rpow_def_of_pos hL0]; exact Real.add_one_le_exp _
  have h3 : (1 - L⁻¹) * (B⁻¹ + ε) ≤ Real.log L * (B⁻¹ + ε) :=
    mul_le_mul_of_nonneg_right h1 hq.le
  have h4 : ε / 2 < (1 - L⁻¹) * (B⁻¹ + ε) := by
    have e : (1 - L⁻¹) * (B⁻¹ + ε) = (ε / 2 + ε * ε * B / 2) / L := by
      rw [hL]; field_simp; ring
    rw [e, lt_div_iff₀ hL0, hL]
    nlinarith [mul_pos hεB hε]
  linarith

/-- Count of words with too many aligned occurrences in residue class `r`. -/
theorem card_residue_le {b : ℕ} {w : List ℕ} (hw : w ≠ []) (hwb : w ∈ strs b w.length)
    {l ρ : ℝ} (hl : 1 ≤ l) (hρ1 : 1 ≤ ρ)
    (hρ : (b : ℝ) ^ w.length - 1 + l ≤ (b : ℝ) ^ w.length * ρ) {t : ℝ} (ht : 0 ≤ t) (n r : ℕ) :
    (((strs b n).filter (fun u => t < alc w n (u.drop r))).card : ℝ)
      ≤ (b : ℝ) ^ n * ρ ^ ((n : ℝ) / w.length) / l ^ t := by
  have hl0 : 0 < l := by linarith
  have hlt : 0 < l ^ t := Real.rpow_pos_of_pos hl0 t
  rcases le_or_gt r n with hr | hr
  · set T := (strs b (n - r)).filter (fun v => t < alc w n v)
    have hsub : (strs b n).filter (fun u => t < alc w n (u.drop r))
        ⊆ (strs b r ×ˢ T).image (fun p => p.1 ++ p.2) := by
      intro u hu
      obtain ⟨hu, hut⟩ := Finset.mem_filter.1 hu
      obtain ⟨hl, hd⟩ := mem_strs.1 hu
      refine Finset.mem_image.2 ⟨(u.take r, u.drop r), Finset.mem_product.2 ⟨?_, ?_⟩,
        List.take_append_drop r u⟩
      · exact mem_strs.2 ⟨by simp; omega, fun d hd' => hd d (List.mem_of_mem_take hd')⟩
      · exact Finset.mem_filter.2 ⟨mem_strs.2 ⟨by simp; omega,
          fun d hd' => hd d (List.mem_of_mem_drop hd')⟩, hut⟩
    have h1 : (((strs b n).filter (fun u => t < alc w n (u.drop r))).card : ℝ)
        ≤ (b : ℝ) ^ r * T.card := by
      have := (Finset.card_le_card hsub).trans Finset.card_image_le
      rw [Finset.card_product, card_strs] at this
      exact_mod_cast this
    have h2 : (T.card : ℝ) * l ^ t ≤ (b : ℝ) ^ (n - r) * ρ ^ ((n : ℝ) / w.length) := by
      refine (markov hl t n (n - r)).trans ((gen_bound hw hwb hl hρ1 hρ n (n - r)).trans ?_)
      gcongr
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hρ1
      refine Nat.cast_div_le.trans ?_
      gcongr
      exact_mod_cast Nat.sub_le n r
    rw [le_div_iff₀ hlt]
    calc _ ≤ (b : ℝ) ^ r * T.card * l ^ t := by gcongr
      _ = (b : ℝ) ^ r * (T.card * l ^ t) := by ring
      _ ≤ (b : ℝ) ^ r * ((b : ℝ) ^ (n - r) * ρ ^ ((n : ℝ) / w.length)) := by gcongr
      _ = _ := by rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hr]
  · have : (strs b n).filter (fun u => t < alc w n (u.drop r)) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro u hu
      rw [List.drop_eq_nil_of_le (by rw [(mem_strs.1 hu).1]; omega),
        alc_short (by simpa using List.length_pos_iff.2 hw)]
      simpa using ht
    rw [this, Finset.card_empty, Nat.cast_zero]
    positivity

/-- **Copeland–Erdős Lemma** (upper-deviation form). For a nonempty word `w` over base
`b ≥ 2` and `ε > 0`, the number of words `u` of length `n` in which `w` occurs more than
`(b^{-|w|} + ε) · n` times is at most `C · βⁿ`, with constants `0 ≤ β < b` and `C`
independent of `n`. -/
theorem large_deviation {b : ℕ} (hb : 2 ≤ b) {w : List ℕ} (hw : w ≠ [])
    (hwd : ∀ d ∈ w, d < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ, 0 ≤ β ∧ β < b ∧ ∃ C : ℝ, ∀ n : ℕ,
      (((strs b n).filter
          (fun u => (((b : ℝ) ^ w.length)⁻¹ + ε) * u.length < occ w u)).card : ℝ)
        ≤ C * β ^ n := by
  classical
  have hK : 0 < w.length := List.length_pos_iff.2 hw
  have hKr : (0 : ℝ) < w.length := by exact_mod_cast hK
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hB : (0 : ℝ) < (b : ℝ) ^ w.length := by positivity
  set B : ℝ := (b : ℝ) ^ w.length with hBdef
  set q : ℝ := B⁻¹ + ε with hq
  set l : ℝ := 1 + ε * B / 2 with hldef
  set ρ : ℝ := 1 + ε / 2 with hρdef
  have hεB := mul_pos hε hB
  have hl : 1 ≤ l := by linarith
  have hl0 : 0 < l := by linarith
  have hρ1 : 1 ≤ ρ := by linarith
  have hρB : B - 1 + l ≤ B * ρ := by rw [hldef, hρdef]; nlinarith
  have hρl : ρ < l ^ q := real_key hB hε
  have hq0 : 0 < q := by positivity
  have hwb : w ∈ strs b w.length := mem_strs.2 ⟨rfl, hwd⟩
  set θ : ℝ := ρ ^ ((1 : ℝ) / w.length) / l ^ (q / w.length) with hθ
  have hlq : 0 < l ^ (q / w.length) := Real.rpow_pos_of_pos hl0 _
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hlq, show q / w.length = q * (1 / w.length) by ring,
      Real.rpow_mul hl0.le]
    exact Real.rpow_lt_rpow (by linarith) hρl (by positivity)
  refine ⟨b * θ, by positivity, mul_lt_of_lt_one_right hb0 hθ1, (w.length : ℝ), fun n => ?_⟩
  set t : ℝ := q * n / w.length with ht
  have ht0 : 0 ≤ t := by positivity
  have hθn : θ ^ n = ρ ^ ((n : ℝ) / w.length) / l ^ t := by
    rw [hθ, div_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (l ^ (q / w.length)),
      ← Real.rpow_mul (by linarith), ← Real.rpow_mul hl0.le]
    congr 2 <;> ring
  have hsub : (strs b n).filter (fun u => q * u.length < occ w u)
      ⊆ (Finset.range w.length).biUnion
          (fun r => (strs b n).filter (fun u => t < alc w n (u.drop r))) := by
    intro u hu
    obtain ⟨hu, hocc⟩ := Finset.mem_filter.1 hu
    have hlen := (mem_strs.1 hu).1
    rw [Finset.mem_biUnion]
    by_contra hne
    push Not at hne
    have hall : ∀ r ∈ Finset.range w.length, (alc w n (u.drop r) : ℝ) ≤ t := by
      intro r hr
      have := hne r hr
      rw [Finset.mem_filter, not_and, not_lt] at this
      exact this hu
    have h1 : (occ w u : ℝ) ≤ ∑ r ∈ Finset.range w.length, (alc w n (u.drop r) : ℝ) := by
      have := occ_le_sum_alc hw u
      rw [hlen] at this
      exact_mod_cast this
    have h2 := Finset.sum_le_sum hall
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    rw [hlen] at hocc
    have : (w.length : ℝ) * t = q * n := by rw [ht]; field_simp
    linarith
  calc (((strs b n).filter (fun u => q * u.length < occ w u)).card : ℝ)
      ≤ (((Finset.range w.length).biUnion
          (fun r => (strs b n).filter (fun u => t < alc w n (u.drop r)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ r ∈ Finset.range w.length,
          (((strs b n).filter (fun u => t < alc w n (u.drop r))).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ r ∈ Finset.range w.length, (b : ℝ) ^ n * ρ ^ ((n : ℝ) / w.length) / l ^ t :=
        Finset.sum_le_sum (fun r _ => card_residue_le hw hwb hl hρ1 hρB ht0 n r)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_pow, hθn]
        ring

end Normal

end

/- Original source header (imports hoisted):
import Normal.LargeDeviation
-/
/- Source module: Normal.Blocks -/
section
set_option autoImplicit false


/-!
# Normality of a concatenation of blocks

A general criterion, abstracted from the proof of the theorem of Copeland–Erdős
(pp. 858–860), for the sequence `B 0 ++ B 1 ++ B 2 ++ ⋯` of digit blocks to be normal:

1. the average block length tends to infinity (`J / T J → 0`, where `T J` is the total
   length of the first `J` blocks), so occurrences straddling block boundaries are
   negligible;
2. the current block is negligible against what came before (`|B J| / T J → 0`), so a
   prefix ending inside a block behaves like one ending at a block boundary;
3. every family of words that is *exponentially thin* (at most `C βⁿ` of length `n`, with
   `β < b`) carries an asymptotically negligible share of the total length.

Condition 3 is fed by `Normal.large_deviation`: the blocks in which a given word is
over-represented form an exponentially thin family, so they do not matter, and in all the
remaining blocks the word has frequency at most `b^{-k} + ε`. This gives the upper bound
`limsup count / N ≤ b^{-k}` for every word; since the counts of the `bᵏ` words of length
`k` add up to `N`, the matching lower bound follows (the paper's closing remark on p. 860).
-/

open Filter Topology

namespace Normal



/-- A word occurs at most `|u|` times in `u`. -/
theorem occ_le_length (w u : List ℕ) : occ w u ≤ u.length := by
  unfold occ
  calc (∑ i ∈ Finset.range u.length, if w <+: u.drop i then 1 else 0)
      ≤ ∑ i ∈ Finset.range u.length, 1 := Finset.sum_le_sum (fun i _ => by split_ifs <;> simp)
    _ = u.length := by simp

/-- Occurrences in a concatenation: those inside `u`, those inside `v`, and at most `|w| - 1`
straddling the boundary. -/
theorem occ_append_le {w : List ℕ} (u v : List ℕ) :
    occ w (u ++ v) ≤ occ w u + occ w v + (w.length - 1) := by
  unfold occ
  rw [List.length_append, Finset.sum_range_add]
  have h2 : (∑ x ∈ Finset.range v.length, if w <+: (u ++ v).drop (u.length + x) then 1 else 0)
      = ∑ i ∈ Finset.range v.length, if w <+: v.drop i then 1 else 0 := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← List.drop_drop, List.drop_left]
  have h1 : (∑ i ∈ Finset.range u.length, if w <+: (u ++ v).drop i then 1 else 0)
      ≤ (∑ i ∈ Finset.range u.length, if w <+: u.drop i then 1 else 0)
        + ∑ i ∈ Finset.range u.length, if u.length < i + w.length then 1 else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i hi => ?_)
    by_cases hl : u.length < i + w.length
    · simp only [hl, ite_true]; split_ifs <;> omega
    · have hle : w.length ≤ (u.drop i).length := by simp; omega
      have : w <+: (u ++ v).drop i ↔ w <+: u.drop i := by
        rw [List.drop_append_of_le_length (by simp at hi; omega), List.prefix_iff_eq_take,
          List.prefix_iff_eq_take, List.take_append_of_le_length hle]
      simp only [this, hl, ite_false]; omega
  have h3 : (∑ i ∈ Finset.range u.length, if u.length < i + w.length then 1 else 0)
      ≤ w.length - 1 := by
    rw [Finset.sum_boole]
    calc _ ≤ (Finset.Ico (u.length - (w.length - 1)) u.length).card := by
          apply Finset.card_le_card
          intro i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
      _ ≤ w.length - 1 := by simp; omega
  rw [h2]; omega

/-- Total length is the length of the concatenation. -/
theorem totalLen_eq_length (B : ℕ → List ℕ) (J : ℕ) :
    totalLen B J = ((List.range J).flatMap B).length := by
  induction J with
  | zero => simp [totalLen]
  | succ J ih => simp [totalLen, Finset.sum_range_succ, List.range_succ, List.flatMap_append] at ih ⊢; omega

/-- Occurrences in `B 0 ++ ⋯ ++ B (J-1)`: within blocks, plus at most `|w| - 1` per boundary. -/
theorem occ_flatMap_le (w : List ℕ) (B : ℕ → List ℕ) (J : ℕ) :
    occ w ((List.range J).flatMap B) ≤ ∑ i ∈ Finset.range J, occ w (B i) + J * (w.length - 1) := by
  induction J with
  | zero => simp [occ]
  | succ J ih =>
    rw [List.range_succ, List.flatMap_append, Finset.sum_range_succ]
    have := occ_append_le (w := w) ((List.range J).flatMap B) ([J].flatMap B)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at this ⊢
    rw [Nat.succ_mul]; omega

/-- A window of `s` starting at `i < N` and lying inside the first `L` entries is an
occurrence of `w` in the list of those entries. -/
theorem count_le_occ (s : ℕ → ℕ) {w : List ℕ} (hw : w ≠ []) {N L : ℕ}
    (hNL : N + w.length ≤ L + 1) : count s w N ≤ occ w ((List.range L).map s) := by
  have hK : 1 ≤ w.length := by
    cases w with
    | nil => exact absurd rfl hw
    | cons a t => simp
  unfold count occ
  rw [Finset.sum_boole, Nat.cast_id, List.length_map, List.length_range]
  apply Finset.card_le_card
  intro i
  simp only [Finset.mem_filter, Finset.mem_range]
  rintro ⟨hi, hP⟩
  refine ⟨by omega, ?_⟩
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    have := hP ⟨j, h1⟩
    simp only [List.get_eq_getElem] at this
    simp [this]

/-- The empty word occurs at every position. -/
theorem count_nil (s : ℕ → ℕ) (N : ℕ) : count s [] N = N := by
  simp [count]

/-- The windows of length `k` starting at the positions `i < N` are partitioned according to
which word of length `k` they spell. -/
theorem sum_count_strs {b : ℕ} {s : ℕ → ℕ} (hs : ∀ n, s n < b) (k N : ℕ) :
    ∑ w ∈ strs b k, count s w N = N := by
  classical
  have hmaps : Set.MapsTo (fun i => List.ofFn (fun j : Fin k => s (i + j)))
      (Finset.range N : Set ℕ) (strs b k : Set (List ℕ)) := by
    intro i _
    simp only [Finset.mem_coe, mem_strs, List.length_ofFn, List.mem_ofFn, true_and]
    rintro d ⟨j, rfl⟩; exact hs _
  conv_rhs => rw [← Finset.card_range N, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl (fun w hw => ?_)
  rw [mem_strs] at hw
  obtain ⟨rfl, -⟩ := hw
  unfold count
  congr 1
  apply Finset.filter_congr
  intro i _
  constructor
  · intro h
    apply List.ext_get (by simp)
    intro n h1 h2
    simpa using h ⟨n, h2⟩
  · intro h j
    have := congrArg (fun l => l[(j : ℕ)]?) h
    simp only [List.getElem?_ofFn] at this
    rw [List.get_eq_getElem]
    simp at this
    exact this

theorem totalLen_succ (B : ℕ → List ℕ) (J : ℕ) :
    totalLen B (J + 1) = totalLen B J + (B J).length := by
  simp [totalLen, Finset.sum_range_succ]

/-- With nonempty blocks, `m` further blocks add at least `m` to the total length. -/
theorem totalLen_add_le {B : ℕ → List ℕ} (hne : ∀ i, B i ≠ []) (J m : ℕ) :
    totalLen B J + m ≤ totalLen B (J + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := List.length_pos_iff.2 (hne (J + m))
    rw [show J + (m + 1) = J + m + 1 by omega, totalLen_succ]; omega

theorem totalLen_strictMono {B : ℕ → List ℕ} (hne : ∀ i, B i ≠ []) :
    StrictMono (totalLen B) :=
  strictMono_nat_of_lt_succ (fun J => by have := totalLen_add_le hne J 1; omega)

theorem le_totalLen {B : ℕ → List ℕ} (hne : ∀ i, B i ≠ []) (J : ℕ) : J ≤ totalLen B J := by
  simpa [totalLen] using totalLen_add_le hne 0 J

/-- Every position `N` lies in some block: `T J ≤ N < T (J + 1)`. -/
theorem exists_block {B : ℕ → List ℕ} (hne : ∀ i, B i ≠ []) (N : ℕ) :
    ∃ J, totalLen B J ≤ N ∧ N < totalLen B (J + 1) := by
  classical
  have hex : ∃ J, N < totalLen B (J + 1) := ⟨N, by have := le_totalLen hne (N + 1); omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | j
  · simp [totalLen]
  · have := Nat.find_min hex (show j < Nat.find hex by omega)
    omega

/-- Occurrences of `w` in the first `J` blocks: at most `c · T J` from the blocks where `w`
is not over-represented (`¬ P`), at most the full length from the others, plus the
boundary terms. -/
theorem occ_prefix_le {w : List ℕ} (hw : w ≠ []) (B : ℕ → List ℕ) (P : List ℕ → Prop) [DecidablePred P]
    {c : ℝ} (hc : 0 ≤ c) (hgood : ∀ u, ¬ P u → (occ w u : ℝ) ≤ c * u.length) (J : ℕ) :
    (occ w ((List.range J).flatMap B) : ℝ) ≤
      c * totalLen B J + (∑ i ∈ (Finset.range J).filter (fun i => P (B i)), ((B i).length : ℝ))
        + J * ((w.length : ℝ) - 1) := by
  have h1 := occ_flatMap_le w B J
  have h1' : (occ w ((List.range J).flatMap B) : ℝ) ≤
      ∑ i ∈ Finset.range J, (occ w (B i) : ℝ) + J * ((w.length : ℝ) - 1) := by
    have h0 : 1 ≤ w.length := List.length_pos_iff.2 hw
    have := (Nat.cast_le (α := ℝ)).2 h1
    push_cast [Nat.cast_sub h0] at this; linarith
  refine h1'.trans ?_
  gcongr
  rw [Finset.sum_filter, totalLen, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  by_cases hP : P (B i)
  · simp only [hP, ite_true]
    have := (Nat.cast_le (α := ℝ)).2 (occ_le_length w (B i))
    have : 0 ≤ c * ((B i).length : ℝ) := by positivity
    linarith
  · simp only [hP, ite_false, add_zero]; exact hgood _ hP

/-- A prefix of `flatten 0 B` ending inside block `J` is covered, together with all windows
starting in it, by the first `J + |w|` blocks. -/
theorem count_le_occ_prefix {B : ℕ → List ℕ} (hne : ∀ i, B i ≠ []) {w : List ℕ} (hw : w ≠ [])
    {N J : ℕ} (hN : N < totalLen B (J + 1)) :
    count (flatten 0 B) w N ≤ occ w ((List.range (J + w.length)).flatMap B) := by
  have hK : 1 ≤ w.length := List.length_pos_iff.2 hw
  rw [← map_flatten_range (d := 0) hne, ← totalLen_eq_length]
  apply count_le_occ _ hw
  have := totalLen_add_le hne (J + 1) (w.length - 1)
  rw [show J + 1 + (w.length - 1) = J + w.length by omega] at this
  omega

/-- If the current block is negligible against what came before (`|B J| / T J → 0`), then
`T (J + m) / T J → 1` for every fixed `m`. -/
theorem tendsto_totalLen_ratio {B : ℕ → List ℕ} (hne : ∀ i, B i ≠ [])
    (hlast : Tendsto (fun J : ℕ => ((B J).length : ℝ) / totalLen B J) atTop (𝓝 0)) (m : ℕ) :
    Tendsto (fun J : ℕ => (totalLen B (J + m) : ℝ) / totalLen B J) atTop (𝓝 1) := by
  have hpos : ∀ᶠ J : ℕ in atTop, (0 : ℝ) < totalLen B J := by
    filter_upwards [eventually_ge_atTop 1] with J hJ
    have := le_totalLen hne J
    exact_mod_cast (show 0 < totalLen B J by omega)
  induction m with
  | zero =>
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with J hJ
    simp [hJ.ne']
  | succ m ih =>
    have h1 : Tendsto (fun J : ℕ => (totalLen B (J + 1) : ℝ) / totalLen B J) atTop (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1 : ℝ))).add hlast
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [hpos] with J hJ
      rw [totalLen_succ]; push_cast; field_simp
    have h2 := (ih.comp (tendsto_add_atTop_nat 1)).mul h1
    rw [mul_one] at h2
    refine h2.congr' ?_
    filter_upwards [hpos, (tendsto_add_atTop_nat 1).eventually hpos] with J hJ hJ1
    simp only [Function.comp_apply] at hJ1 ⊢
    rw [show J + (m + 1) = J + 1 + m by omega]
    field_simp

variable {b : ℕ} {B : ℕ → List ℕ}

/-- **Upper bound.** Under the hypotheses of `isNormalSeq_flatten`, every nonempty word `w`
eventually has relative frequency at most `b^{-|w|} + ε` in `flatten 0 B`. -/
theorem eventually_count_div_le (hb : 2 ≤ b) (hne : ∀ i, B i ≠ [])
    (hcount : Tendsto (fun J : ℕ => (J : ℝ) / totalLen B J) atTop (𝓝 0))
    (hlast : Tendsto (fun J : ℕ => ((B J).length : ℝ) / totalLen B J) atTop (𝓝 0))
    (hbad : ∀ (P : List ℕ → Prop) [DecidablePred P] (β C : ℝ), β < b →
      (∀ n, (((strs b n).filter P).card : ℝ) ≤ C * β ^ n) →
      Tendsto (fun J : ℕ =>
          (∑ i ∈ (Finset.range J).filter (fun i => P (B i)), ((B i).length : ℝ)) /
            totalLen B J) atTop (𝓝 0))
    {w : List ℕ} (hw : w ≠ []) (hwd : ∀ d ∈ w, d < b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (count (flatten 0 B) w N : ℝ) / N ≤ ((b : ℝ) ^ w.length)⁻¹ + ε := by
  classical
  set p : ℝ := ((b : ℝ) ^ w.length)⁻¹ with hp
  set K := w.length with hKdef
  have hK : 1 ≤ K := List.length_pos_iff.2 hw
  have hp0 : 0 ≤ p := by positivity
  obtain ⟨β, -, hβb, C, hC⟩ := large_deviation hb hw hwd (half_pos hε)
  set P : List ℕ → Prop := fun u => (p + ε / 2) * u.length < occ w u with hP
  have hbadP := hbad P β C hβb hC
  set T : ℕ → ℝ := fun J => (totalLen B J : ℝ) with hT
  set bad : ℕ → ℝ := fun J =>
    ∑ i ∈ (Finset.range J).filter (fun i => P (B i)), ((B i).length : ℝ) with hbaddef
  set g : ℕ → ℝ := fun J =>
    ((p + ε / 2) * T (J + K) + bad (J + K) + ((J + K : ℕ) : ℝ) * ((K : ℝ) - 1)) / T J with hg
  have hpos : ∀ J, 1 ≤ J → (0 : ℝ) < T J := by
    intro J hJ
    have := le_totalLen hne J
    simp only [hT]; exact_mod_cast (show 0 < totalLen B J by omega)
  have hR := tendsto_totalLen_ratio hne hlast K
  have hlim : Tendsto g atTop (𝓝 (p + ε / 2)) := by
    have hb' := hbadP.comp (tendsto_add_atTop_nat K)
    have hc' := hcount.comp (tendsto_add_atTop_nat K)
    have := ((tendsto_const_nhds (x := p + ε / 2)).mul hR).add (hb'.mul hR) |>.add
      (((tendsto_const_nhds (x := (K : ℝ) - 1)).mul hc').mul hR)
    simp only [mul_one, mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with J hJ
    have h1 := hpos J hJ
    have h2 := hpos (J + K) (by omega)
    simp only [Function.comp_apply, hg, hT, hbaddef] at h1 h2 ⊢
    field_simp
  have hev : ∀ᶠ J in atTop, 1 ≤ J ∧ g J < p + ε :=
    (eventually_ge_atTop 1).and ((tendsto_order.1 hlim).2 _ (by linarith))
  obtain ⟨J0, hJ0⟩ := eventually_atTop.1 hev
  filter_upwards [eventually_ge_atTop (totalLen B J0)] with N hN
  obtain ⟨J, hJN, hNJ⟩ := exists_block hne N
  have hJJ : J0 ≤ J := by
    have := (totalLen_strictMono hne).lt_iff_lt.1 (lt_of_le_of_lt hN hNJ); omega
  obtain ⟨hJ1, hgJ⟩ := hJ0 J hJJ
  have hTJ := hpos J hJ1
  have hTN : T J ≤ N := by simp only [hT]; exact_mod_cast hJN
  have hc1 := (Nat.cast_le (α := ℝ)).2 (count_le_occ_prefix hne hw hNJ)
  have hc2 := occ_prefix_le hw B P (c := p + ε / 2) (by positivity)
    (fun u hu => le_of_not_gt hu) (J + K)
  have hX : (count (flatten 0 B) w N : ℝ) ≤ g J * T J := by
    simp only [hg]; rw [div_mul_cancel₀ _ hTJ.ne']
    refine hc1.trans (hc2.trans (le_of_eq ?_))
    simp only [hT, hbaddef]
    rfl
  calc (count (flatten 0 B) w N : ℝ) / N ≤ g J * T J / T J := by
        rw [div_le_div_iff₀ (by linarith) hTJ]
        have : 0 ≤ g J * T J := (Nat.cast_nonneg _).trans hX
        nlinarith
    _ = g J := by field_simp
    _ ≤ p + ε := hgJ.le

/-- **Lower bound.** If every word of length `k = |w|` eventually has relative frequency at
most `b^{-k} + δ` for every `δ > 0`, then, since these frequencies add up to `1`, the word
`w` eventually has relative frequency at least `b^{-k} - ε`. -/
theorem eventually_le_count_div {s : ℕ → ℕ} (hb : 2 ≤ b) (hs : ∀ n, s n < b)
    (hup : ∀ w : List ℕ, w ≠ [] → (∀ d ∈ w, d < b) → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, (count s w N : ℝ) / N ≤ ((b : ℝ) ^ w.length)⁻¹ + ε)
    {w : List ℕ} (hw : w ≠ []) (hwd : ∀ d ∈ w, d < b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ((b : ℝ) ^ w.length)⁻¹ - ε ≤ (count s w N : ℝ) / N := by
  classical
  set K := w.length with hKdef
  have hK : 1 ≤ K := List.length_pos_iff.2 hw
  set q : ℝ := (b : ℝ) ^ K with hq
  have hq1 : 1 ≤ q := one_le_pow₀ (by exact_mod_cast (show 1 ≤ b by omega))
  have hq0 : 0 < q := by linarith
  have hwS : w ∈ strs b K := mem_strs.2 ⟨rfl, hwd⟩
  have hothers : ∀ᶠ N : ℕ in atTop, ∀ w' ∈ (strs b K).erase w,
      (count s w' N : ℝ) / N ≤ q⁻¹ + ε / q := by
    rw [Filter.eventually_all_finset]
    intro w' hw'
    obtain ⟨hlen, hd⟩ := mem_strs.1 (Finset.mem_of_mem_erase hw')
    have hne' : w' ≠ [] := by intro h; subst h; simp at hlen; omega
    have := hup w' hne' hd (ε / q) (by positivity)
    rwa [hlen] at this
  filter_upwards [hothers, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsum := sum_count_strs hs K N
  rw [← Finset.add_sum_erase _ _ hwS] at hsum
  have hsumR : (count s w N : ℝ) / N = 1 - ∑ w' ∈ (strs b K).erase w, (count s w' N : ℝ) / N := by
    rw [← Finset.sum_div, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hNpos.ne']
    exact_mod_cast hsum
  have hcard : (((strs b K).erase w).card : ℝ) = q - 1 := by
    rw [Finset.card_erase_of_mem hwS, card_strs, Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
    simp [hq]
  have hle : ∑ w' ∈ (strs b K).erase w, (count s w' N : ℝ) / N ≤ (q - 1) * (q⁻¹ + ε / q) := by
    calc _ ≤ ∑ w' ∈ (strs b K).erase w, (q⁻¹ + ε / q) := Finset.sum_le_sum hN
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [hsumR]
  have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq0.ne'
  have : ε / q = ε * q⁻¹ := div_eq_mul_inv _ _
  rw [this] at hle
  have : 0 < ε * q⁻¹ := by positivity
  nlinarith

/-- **Block criterion for normality.** See the module docstring for the meaning of the
three hypotheses. -/
theorem isNormalSeq_flatten {b : ℕ} (hb : 2 ≤ b) (B : ℕ → List ℕ)
    (hne : ∀ i, B i ≠ []) (hdig : ∀ i, ∀ d ∈ B i, d < b)
    (hcount : Tendsto (fun J : ℕ => (J : ℝ) / totalLen B J) atTop (𝓝 0))
    (hlast : Tendsto (fun J : ℕ => ((B J).length : ℝ) / totalLen B J) atTop (𝓝 0))
    (hbad : ∀ (P : List ℕ → Prop) [DecidablePred P] (β C : ℝ), β < b →
      (∀ n, (((strs b n).filter P).card : ℝ) ≤ C * β ^ n) →
      Tendsto (fun J : ℕ =>
          (∑ i ∈ (Finset.range J).filter (fun i => P (B i)), ((B i).length : ℝ)) /
            totalLen B J) atTop (𝓝 0)) :
    IsNormalSeq b (flatten 0 B) := by
  have hs : ∀ n, flatten 0 B n < b := fun n => by
    obtain ⟨i, hi⟩ := flatten_mem (d := 0) hne n
    exact hdig i _ hi
  have hup := fun w (hw : w ≠ []) hwd ε (hε : (0 : ℝ) < ε) =>
    eventually_count_div_le hb hne hcount hlast hbad hw hwd hε
  intro w hwd
  by_cases hw : w = []
  · subst hw
    simp only [count_nil, List.length_nil, pow_zero, inv_one]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [div_self (by exact_mod_cast (show N ≠ 0 by omega))]
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · filter_upwards [eventually_le_count_div hb hs hup hw hwd (show 0 < (((b : ℝ) ^ w.length)⁻¹ - a) / 2 by linarith)] with N hN
    linarith
  · filter_upwards [hup w hw hwd ((a - ((b : ℝ) ^ w.length)⁻¹) / 2) (by linarith)] with N hN
    linarith

end Normal

end

/- Original source header (imports hoisted):
import Normal.Flatten
-/
/- Source module: Normal.Real -/
section
set_option autoImplicit false


/-!
# From normal digit sequences to normal real numbers

Champernowne and Copeland–Erdős speak of the *decimal* `0.a₁a₂a₃…`. We record the bridge
from a digit sequence `s` to the real number `ofDigits b s = ∑ sₙ b^{-(n+1)}`: when `s` is a
genuine base-`b` digit sequence that is not eventually `b - 1`, the base-`b` digits of
`ofDigits b s` are exactly `s`. A normal sequence is never eventually `b - 1` (the digit `0`
must have frequency `1/b`), so normality transfers to the real number.
-/

open Filter Topology

namespace Normal









end Normal

end

/- Original source header (imports hoisted):
import Normal.Blocks
-/
/- Source module: Normal.CopelandErdos -/
section
set_option autoImplicit false


/-!
# The theorem of Copeland and Erdős

A. H. Copeland, P. Erdős, *Note on normal numbers*, Bull. Amer. Math. Soc. 52 (1946),
857–860, p. 857:

> **THEOREM.** *If `a₁, a₂, ⋯` is an increasing sequence of integers such that for every
> `θ < 1` the number of `a`'s up to `N` exceeds `N^θ` provided `N` is sufficiently large,
> then the infinite decimal `0.a₁a₂a₃⋯` is normal with respect to the base `β` in which
> these integers are expressed.*

Formal reading: the sequence is `a : ℕ → ℕ`, strictly increasing ("increasing sequence of
integers", whose terms are written out in base `b`, hence positive); "the number of `a`'s
up to `N`" is `#{i | a i ≤ N}`, which we write as a filter over `range (N + 1)` (this loses
nothing: `a i ≥ i` for a strictly increasing sequence of naturals, so `a i ≤ N` forces
`i ≤ N`).

Corollaries on the same page: the conjecture of Champernowne that `0.235711131719⋯`
(the primes) is normal, and Champernowne's own Theorem III, `0.123456789101112⋯`.
-/

open Filter Topology

namespace Normal







/-- `digitsBE` has as many digits as `Nat.digits`. -/
theorem length_digitsBE (b m : ℕ) : (digitsBE b m).length = (Nat.digits b m).length := by
  simp [digitsBE]

/-- `m < b ^ |m|_b`. -/
theorem lt_pow_length_digitsBE {b : ℕ} (hb : 2 ≤ b) (m : ℕ) :
    m < b ^ (digitsBE b m).length := by
  rw [length_digitsBE]; exact Nat.lt_base_pow_length_digits (by omega)

/-- `b ^ (|m|_b - 1) ≤ m` for `m > 0`. -/
theorem pow_length_digitsBE_sub_one_le {b : ℕ} (hb : 2 ≤ b) {m : ℕ} (hm : 0 < m) :
    b ^ ((digitsBE b m).length - 1) ≤ m := by
  rw [length_digitsBE]
  have h1 := Nat.base_pow_length_digits_le b m (by omega) hm.ne'
  have h2 : 1 ≤ (Nat.digits b m).length := by
    rw [Nat.one_le_iff_ne_zero, Ne, List.length_eq_zero_iff, ← Ne, Nat.digits_ne_nil_iff_ne_zero]
    exact hm.ne'
  obtain ⟨k, hk⟩ : ∃ k, (Nat.digits b m).length = k + 1 := ⟨_, (Nat.sub_add_cancel h2).symm⟩
  rw [hk, pow_succ] at h1
  rw [hk, Nat.add_sub_cancel]
  have : 0 < b := by omega
  nlinarith

/-- A number `≥ b ^ L` has more than `L` digits. -/
theorem lt_length_digitsBE {b : ℕ} (hb : 2 ≤ b) {m L : ℕ} (h : b ^ L ≤ m) :
    L < (digitsBE b m).length := by
  by_contra hc
  have := lt_pow_length_digitsBE hb m
  have := Nat.pow_le_pow_right (by omega : 0 < b) (not_lt.1 hc)
  omega

/-- Distinct numbers have distinct base-`b` expansions. -/
theorem digitsBE_injective (b : ℕ) : Function.Injective (digitsBE b) := by
  intro m n h
  simpa [digitsBE, Nat.digits_inj_iff] using h

/-- Larger numbers have at least as many digits. -/
theorem length_digitsBE_mono (b : ℕ) : Monotone (fun m => (digitsBE b m).length) := by
  intro m n h
  simpa [length_digitsBE] using Nat.le_length_digits_le b m n h

section CopelandErdosProof

variable {b : ℕ} {a : ℕ → ℕ}

/-- For strictly increasing `a`, exactly `J + 1` terms are `≤ a J`. -/
theorem card_filter_le_apply (ha : StrictMono a) (J : ℕ) :
    ((Finset.range (a J + 1)).filter (fun i => a i ≤ a J)).card = J + 1 := by
  have : (Finset.range (a J + 1)).filter (fun i => a i ≤ a J) = Finset.range (J + 1) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, ha.le_iff_le]
    have := ha.id_le J
    simp only [id] at this
    omega
  rw [this, Finset.card_range]

/-- The density hypothesis, read at `N = a J`: `(a J)^θ < J + 1` eventually. -/
theorem eventually_rpow_apply_lt (ha : StrictMono a)
    (hdense : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ < (((Finset.range (N + 1)).filter (fun i => a i ≤ N)).card : ℝ))
    {θ : ℝ} (hθ : θ < 1) : ∀ᶠ J : ℕ in atTop, ((a J : ℕ) : ℝ) ^ θ < (J : ℝ) + 1 := by
  filter_upwards [ha.tendsto_atTop.eventually (hdense θ hθ)] with J hJ
  rw [card_filter_le_apply ha J] at hJ
  exact_mod_cast hJ

/-- For `1 ≤ c < b`, the number `ℓ J` of digits of `a J` satisfies `c ^ ℓ J < c (J + 1)`
eventually. -/
theorem eventually_pow_length_lt (hb : 2 ≤ b) (ha : StrictMono a) (ha0 : 0 < a 0)
    (hdense : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ < (((Finset.range (N + 1)).filter (fun i => a i ≤ N)).card : ℝ))
    {c : ℝ} (hc1 : 1 ≤ c) (hcb : c < b) :
    ∀ᶠ J : ℕ in atTop, c ^ (digitsBE b (a J)).length < c * ((J : ℝ) + 1) := by
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hc0 : 0 < c := by linarith
  set θ := Real.logb b c with hθdef
  have hθ1 : θ < 1 := by
    rw [hθdef, ← Real.logb_self_eq_one hb1, Real.logb_lt_logb_iff hb1 hc0 (by linarith)]
    exact hcb
  have hθ0 : 0 ≤ θ := Real.logb_nonneg hb1 hc1
  have hbθ : (b : ℝ) ^ θ = c := Real.rpow_logb (by linarith) hb1.ne' hc0
  filter_upwards [eventually_rpow_apply_lt ha hdense hθ1] with J hJ
  have hapos : 0 < a J := lt_of_lt_of_le ha0 (ha.monotone (Nat.zero_le J))
  set L := (digitsBE b (a J)).length
  have hL : 1 ≤ L := by
    have := lt_length_digitsBE (L := 0) hb (by simpa using Nat.one_le_iff_ne_zero.2 hapos.ne'); omega
  have h1 : ((b : ℝ) ^ (L - 1)) ≤ (a J : ℝ) := by
    exact_mod_cast pow_length_digitsBE_sub_one_le hb hapos
  have h2 : c ^ (L - 1) ≤ (a J : ℝ) ^ θ := by
    rw [← hbθ, Real.rpow_pow_comm (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h1 hθ0
  have h3 : c ^ L = c * c ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h3]
  exact mul_lt_mul_of_pos_left (lt_of_le_of_lt h2 hJ) hc0

/-- The number of digits of `a i` tends to infinity. -/
theorem tendsto_length_digitsBE (hb : 2 ≤ b) (ha : StrictMono a) :
    Tendsto (fun i => (digitsBE b (a i)).length) atTop atTop := by
  rw [tendsto_atTop]
  intro L
  filter_upwards [eventually_ge_atTop (b ^ L)] with i hi
  have := ha.id_le i
  exact (lt_length_digitsBE hb (hi.trans this)).le

/-- Every block is nonempty, so `J ≤ T J`. -/
theorem le_totalLen_digitsBE (ha : ∀ i, 0 < a i) (J : ℕ) :
    J ≤ totalLen (fun i => digitsBE b (a i)) J := by
  unfold totalLen
  calc J = ∑ _i ∈ Finset.range J, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => by
      have := digitsBE_ne_nil (b := b) (ha i)
      exact List.length_pos_iff.2 this

/-- Blocks beyond index `b ^ L` have more than `L` digits, so `(J - b^L)(L+1) ≤ T J`. -/
theorem sub_mul_le_totalLen (hb : 2 ≤ b) (ha : StrictMono a) (L J : ℕ) :
    (J - b ^ L) * (L + 1) ≤ totalLen (fun i => digitsBE b (a i)) J := by
  unfold totalLen
  rcases le_or_gt J (b ^ L) with h | h
  · simp [Nat.sub_eq_zero_of_le h]
  calc (J - b ^ L) * (L + 1) = ∑ _i ∈ Finset.Ico (b ^ L) J, (L + 1) := by simp
    _ ≤ ∑ i ∈ Finset.Ico (b ^ L) J, (digitsBE b (a i)).length :=
        Finset.sum_le_sum fun i hi => by
          have hi' := (Finset.mem_Ico.1 hi).1
          have := ha.id_le i
          exact lt_length_digitsBE hb (hi'.trans this)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi => by simp at hi ⊢; omega) (fun _ _ _ => Nat.zero_le _)

/-- Squeeze along the digit lengths: if `0 ≤ f J ≤ G (ℓ J)` eventually, `G → 0` and
`ℓ → ∞`, then `f → 0`. -/
theorem tendsto_zero_of_le_comp {f : ℕ → ℝ} {G : ℕ → ℝ} {ℓ : ℕ → ℕ}
    (hℓ : Tendsto ℓ atTop atTop) (hG : Tendsto G atTop (𝓝 0)) (h0 : ∀ J, 0 ≤ f J)
    (hle : ∀ᶠ J in atTop, f J ≤ G (ℓ J)) : Tendsto f atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hG.comp hℓ)
    (Eventually.of_forall h0) hle

/-- **Hypothesis 1 of the block criterion**: the average block length tends to infinity. -/
theorem tendsto_count_div_totalLen (hb : 2 ≤ b) (ha : StrictMono a) (ha0 : 0 < a 0) :
    Tendsto (fun J : ℕ => (J : ℝ) / totalLen (fun i => digitsBE b (a i)) J) atTop (𝓝 0) := by
  have hpos : ∀ i, 0 < a i := fun i => lt_of_lt_of_le ha0 (ha.monotone (Nat.zero_le i))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L, hL⟩ := exists_nat_gt (2 / ε)
  refine ⟨2 * b ^ L + 1, fun J hJ => ?_⟩
  have hT := sub_mul_le_totalLen hb ha L J
  have hTJ := le_totalLen_digitsBE (b := b) hpos J
  set T := totalLen (fun i => digitsBE b (a i)) J
  have hJ1 : 1 ≤ J := by omega
  have hkey : J * (L + 1) ≤ 2 * T := by
    have : J ≤ 2 * (J - b ^ L) := by omega
    nlinarith
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hTpos]
  have hkey' : (J : ℝ) * (L + 1) ≤ 2 * T := by exact_mod_cast hkey
  have hL' : 2 < ε * (L + 1) := by
    rw [div_lt_iff₀ hε] at hL; nlinarith
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ1
  nlinarith

/-- **Hypothesis 2 of the block criterion**: the current block is negligible. -/
theorem tendsto_length_div_totalLen (hb : 2 ≤ b) (ha : StrictMono a) (ha0 : 0 < a 0)
    (hdense : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ < (((Finset.range (N + 1)).filter (fun i => a i ≤ N)).card : ℝ)) :
    Tendsto (fun J : ℕ => ((digitsBE b (a J)).length : ℝ) /
      totalLen (fun i => digitsBE b (a i)) J) atTop (𝓝 0) := by
  have hpos : ∀ i, 0 < a i := fun i => lt_of_lt_of_le ha0 (ha.monotone (Nat.zero_le i))
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  set c : ℝ := (1 + b) / 2 with hc
  have hc1 : 1 < c := by rw [hc]; linarith
  have hcb : c < b := by rw [hc]; linarith
  have hr : |1 / c| < 1 := by
    rw [abs_of_pos (by positivity), div_lt_one (by linarith)]; exact hc1
  have hG : Tendsto (fun L : ℕ => 2 * c * ((L : ℝ) ^ 1 * (1 / c) ^ L)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr).const_mul (2 * c)
  refine tendsto_zero_of_le_comp (tendsto_length_digitsBE hb ha) hG (fun J => by positivity) ?_
  filter_upwards [eventually_pow_length_lt hb ha ha0 hdense hc1.le hcb,
    eventually_ge_atTop 1] with J hJ hJ1
  set L := (digitsBE b (a J)).length
  have hTJ : (J : ℝ) ≤ totalLen (fun i => digitsBE b (a i)) J := by
    exact_mod_cast le_totalLen_digitsBE (b := b) hpos J
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ1
  have hJ1' : (1 : ℝ) ≤ J := by exact_mod_cast hJ1
  have hcL : 0 < c ^ L := by positivity
  calc (L : ℝ) / totalLen (fun i => digitsBE b (a i)) J ≤ L / J :=
        div_le_div_of_nonneg_left (by positivity) hJpos hTJ
    _ ≤ 2 * c * ((L : ℝ) ^ 1 * (1 / c) ^ L) := by
        rw [div_pow, one_pow, pow_one, div_le_iff₀ hJpos]
        have : c ^ L ≤ 2 * c * J := by nlinarith
        have hL0 : (0 : ℝ) ≤ L := by positivity
        rw [show 2 * c * (↑L * (1 / c ^ L)) * ↑J = L * ((2 * c * J) / c ^ L) by
          field_simp]
        exact le_mul_of_one_le_right hL0 ((one_le_div hcL).2 this)

/-- An exponential bound `C βⁿ` with `β < b` can be normalised to `C' β'ⁿ` with `C' ≥ 0`
and `1 ≤ β' < b`. -/
theorem card_filter_le_normalise {P : List ℕ → Prop} [DecidablePred P] {β C : ℝ}
    (hP : ∀ n, (((strs b n).filter P).card : ℝ) ≤ C * β ^ n) (n : ℕ) :
    (((strs b n).filter P).card : ℝ) ≤ max C 0 * max β 1 ^ n := by
  by_cases hβ0 : 0 ≤ β
  · calc _ ≤ C * β ^ n := hP n
      _ ≤ max C 0 * β ^ n := mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hβ0 n)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ0 (le_max_left _ _) n)
          (le_max_right _ _)
  · push Not at hβ0
    have h0 := hP 0
    have h1 := hP 1
    simp only [pow_zero, mul_one, pow_one] at h0 h1
    have hc0 : (0 : ℝ) ≤ ((strs b 0).filter P).card := by positivity
    have hc1 : (0 : ℝ) ≤ ((strs b 1).filter P).card := by positivity
    have hC : C = 0 := by nlinarith
    calc _ ≤ C * β ^ n := hP n
      _ = 0 := by rw [hC, zero_mul]
      _ ≤ _ := by positivity

/-- The blocks `B 0, …, B J` satisfying an exponentially thin property `P` are few: they are
distinct words of length at most `ℓ J`. -/
theorem card_filter_bad_le (hb : 2 ≤ b) (ha : StrictMono a) {P : List ℕ → Prop}
    [DecidablePred P] {β C : ℝ} (hP : ∀ n, (((strs b n).filter P).card : ℝ) ≤ C * β ^ n)
    (J : ℕ) :
    ((((Finset.range (J + 1)).filter (fun i => P (digitsBE b (a i)))).card : ℕ) : ℝ) ≤
      ((digitsBE b (a J)).length + 1) * (max C 0 * max β 1 ^ (digitsBE b (a J)).length) := by
  set L := (digitsBE b (a J)).length
  have h1 : ((Finset.range (J + 1)).filter (fun i => P (digitsBE b (a i)))).card ≤
      ((Finset.range (L + 1)).biUnion (fun n => (strs b n).filter P)).card := by
    apply Finset.card_le_card_of_injOn (fun i => digitsBE b (a i))
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hi
      simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_Iio, Finset.coe_filter,
        Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      refine ⟨(digitsBE b (a i)).length, ?_, ?_, hi.2⟩
      · have := length_digitsBE_mono b (ha.monotone (Nat.lt_succ_iff.1 hi.1))
        simp only at this; omega
      · exact mem_strs.2 ⟨rfl, fun d hd => digitsBE_lt hb hd⟩
    · intro i _ j _ hij
      exact ha.injective (digitsBE_injective b hij)
  have h2 := (Finset.card_biUnion_le (s := Finset.range (L + 1))
    (t := fun n => (strs b n).filter P))
  have hβ1 : (1 : ℝ) ≤ max β 1 := le_max_right _ _
  calc ((((Finset.range (J + 1)).filter (fun i => P (digitsBE b (a i)))).card : ℕ) : ℝ)
      ≤ ((∑ n ∈ Finset.range (L + 1), ((strs b n).filter P).card : ℕ) : ℝ) := by
        exact_mod_cast h1.trans h2
    _ = ∑ n ∈ Finset.range (L + 1), ((((strs b n).filter P).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ _n ∈ Finset.range (L + 1), max C 0 * max β 1 ^ L :=
        Finset.sum_le_sum fun n hn => (card_filter_le_normalise hP n).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hβ1 (Nat.lt_succ_iff.1
            (Finset.mem_range.1 hn))) (le_max_right _ _))
    _ = _ := by simp

/-- Algebraic identity used in `tendsto_bad_div_totalLen`. -/
theorem bad_bound_identity {c : ℝ} (hc : c ≠ 0) (L C β : ℝ) (n : ℕ) :
    (L + 1) * (C * β ^ n) * L / (c ^ n / c) = C * c * (L ^ 2 * (β / c) ^ n + L ^ 1 * (β / c) ^ n) := by
  rw [div_pow]; field_simp

/-- **Hypothesis 3 of the block criterion**: exponentially thin families of blocks carry a
negligible share of the digits. -/
theorem tendsto_bad_div_totalLen (hb : 2 ≤ b) (ha : StrictMono a) (ha0 : 0 < a 0)
    (hdense : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ < (((Finset.range (N + 1)).filter (fun i => a i ≤ N)).card : ℝ))
    (P : List ℕ → Prop) [DecidablePred P] (β C : ℝ) (hβ : β < b)
    (hP : ∀ n, (((strs b n).filter P).card : ℝ) ≤ C * β ^ n) :
    Tendsto (fun J : ℕ =>
        (∑ i ∈ (Finset.range J).filter (fun i => P (digitsBE b (a i))),
          ((digitsBE b (a i)).length : ℝ)) / totalLen (fun i => digitsBE b (a i)) J)
      atTop (𝓝 0) := by
  have hpos : ∀ i, 0 < a i := fun i => lt_of_lt_of_le ha0 (ha.monotone (Nat.zero_le i))
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  rw [← tendsto_add_atTop_iff_nat 1]
  set β' := max β 1 with hβ'
  set C' := max C 0 with hC'
  have hβ'1 : 1 ≤ β' := le_max_right _ _
  have hβ'b : β' < b := max_lt hβ hb1
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set c : ℝ := (β' + b) / 2 with hc
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  have hcb : c < b := by rw [hc]; linarith
  have hc0 : 0 < c := by linarith
  set r := β' / c with hr
  have hr' : |r| < 1 := by
    rw [abs_of_pos (by positivity), hr, div_lt_one hc0, hc]; linarith
  have hG : Tendsto (fun L : ℕ => C' * c * ((L : ℝ) ^ 2 * r ^ L + (L : ℝ) ^ 1 * r ^ L))
      atTop (𝓝 0) := by
    simpa using ((tendsto_pow_const_mul_const_pow_of_abs_lt_one 2 hr').add
      (tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr')).const_mul (C' * c)
  refine tendsto_zero_of_le_comp (tendsto_length_digitsBE hb ha) hG
    (fun J => by positivity) ?_
  filter_upwards [eventually_pow_length_lt hb ha ha0 hdense hc1 hcb] with J hJ
  set L := (digitsBE b (a J)).length
  set S := (Finset.range (J + 1)).filter (fun i => P (digitsBE b (a i)))
  have hcard := card_filter_bad_le hb ha hP J
  have hsum : ∑ i ∈ S, ((digitsBE b (a i)).length : ℝ) ≤ (S.card : ℝ) * L := by
    rw [← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro i hi
    have := length_digitsBE_mono b (ha.monotone (Nat.lt_succ_iff.1
      (Finset.mem_range.1 (Finset.mem_filter.1 hi).1)))
    exact_mod_cast this
  have hTJ : ((J + 1 : ℕ) : ℝ) ≤ totalLen (fun i => digitsBE b (a i)) (J + 1) := by
    exact_mod_cast le_totalLen_digitsBE (b := b) hpos (J + 1)
  have hJpos : (0 : ℝ) < ((J + 1 : ℕ) : ℝ) := by positivity
  have hcL : 0 < c ^ L := by positivity
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hnum : ∑ i ∈ S, ((digitsBE b (a i)).length : ℝ) ≤ (L + 1) * (C' * β' ^ L) * L :=
    hsum.trans (mul_le_mul_of_nonneg_right hcard hL0)
  calc (∑ i ∈ S, ((digitsBE b (a i)).length : ℝ)) /
        totalLen (fun i => digitsBE b (a i)) (J + 1)
      ≤ (L + 1) * (C' * β' ^ L) * L / ((J + 1 : ℕ) : ℝ) :=
        div_le_div₀ (by positivity) hnum hJpos hTJ
    _ ≤ (L + 1) * (C' * β' ^ L) * L / (c ^ L / c) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        rw [div_le_iff₀ hc0]; push_cast; linarith
    _ = C' * c * ((L : ℝ) ^ 2 * r ^ L + (L : ℝ) ^ 1 * r ^ L) := by
        rw [hr]; exact bad_bound_identity hc0.ne' _ _ _ _





end CopelandErdosProof







end Normal

end

/- Original source header (imports hoisted):
import Normal.Blocks
-/
/- Source module: Normal.Champernowne -/
section
set_option autoImplicit false


/-!
# Champernowne's Theorems I, II and IV

D. G. Champernowne, *The construction of decimals normal in the scale of ten*,
J. London Math. Soc. 8 (1933), 254–260, p. 255. Let `s_r` denote the sequence
`00..0, 00..1, 00..2, ⋯, 99..9` of all `10^r` arrangements of `r` digits in ascending
order, and `_μs_r` the sequence `s_r` repeated `μ` times.

* **Theorem I.** `0.s₁s₂s₃⋯` is normal in the scale of ten.
* **Theorem II.** For every fixed positive integer `μ`, `0._μs₁ _μs₂ ⋯ _μs_r ⋯` is normal.
* **Theorem III.** `0.123456789101112⋯` is normal (see `Normal.champernowne_concat`).
* **Theorem IV.** `0.₁s₁ ₂s₂ ⋯ _rs_r ⋯` is normal.

We state and prove them in every base `b ≥ 2`; base ten is the specialisation in
`Normal.Main`. Champernowne's proofs count occurrences exactly; ours go through the block
criterion `Normal.isNormalSeq_flatten`, with the members of `s_r` as the blocks.
-/

open Filter Topology

namespace Normal












/-! ## The strings `padDigits b r m` -/











/-! ## Abstract block sequences `flatten [] M` -/

section Abstract

variable (M : ℕ → List (List ℕ))







variable {M}





















end Abstract




/-! ## Champernowne's block sequences -/






































end Normal

end

/- Original source header (imports hoisted):
import Normal.CopelandErdos
import Normal.Champernowne
import Normal.Real
import Normal.Agafonov
-/
/- Source module: Normal.Main -/
section
set_option autoImplicit false


/-!
# Headline theorems: the Champernowne and Copeland–Erdős constants are normal

Real-number forms, in base ten exactly as in the papers, and in every base `b ≥ 2`.
The `example`s at the end check, by evaluation, that the digit sequences are the intended
ones (`0.123456789101112…`, `0.0123456789000102…`).
-/

open Filter Topology

namespace Normal



















/-! ## The same results in the `agafonov` repository's form

Via `isNormalSeq_iff_isNormal`, the digit sequences, viewed as `ℕ → Fin b`, satisfy
`Agafonov.IsNormal` (the integer-arithmetic definition of `xiangyazi24/agafonov`). -/









/-! ## Sanity checks on the digit sequences -/





end Normal

end

/- Original source header (imports hoisted):
import Normal.Basic
import Normal.Agafonov
import Normal.Flatten
import Normal.Strs
import Normal.LargeDeviation
import Normal.Blocks
import Normal.Real
import Normal.CopelandErdos
import Normal.Champernowne
import Normal.Main
-/
/- Source module: Normal -/
section
set_option autoImplicit false


end


set_option autoImplicit false
open Filter Topology
open Normal

theorem solution {b : ℕ} (hb : 2 ≤ b) {a : ℕ → ℕ} (ha : StrictMono a) (ha0 : 0 < a 0)
    (hdense : ∀ θ : ℝ, θ < 1 → ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ θ < (((Finset.range (N + 1)).filter (fun i => a i ≤ N)).card : ℝ)) :
    IsNormalSeq b (concatDigits b a) := by
  have hpos : ∀ i, 0 < a i := fun i => lt_of_lt_of_le ha0 (ha.monotone (Nat.zero_le i))
  refine isNormalSeq_flatten hb (fun i => digitsBE b (a i)) (fun i => digitsBE_ne_nil (hpos i))
    (fun i d hd => digitsBE_lt hb hd) (tendsto_count_div_totalLen hb ha ha0)
    (tendsto_length_div_totalLen hb ha ha0 hdense) ?_
  intro P _ β C hβ hP
  exact tendsto_bad_div_totalLen hb ha ha0 hdense P β C hβ hP
