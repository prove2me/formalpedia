-- Prove2me | solution 1 for Normal.champGen_normal
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T15:29:36.038558+00:00
-- url     : https://prove2.me/submissions/884e9314-4b0b-4614-9a77-c04ab702e340

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



/-- Flattening is associative: flattening the concatenations `(M r).flatten` gives the
same sequence as flattening the sequence of all lists occurring in `M 0, M 1, …`. -/
theorem flatten_flatten {d : α} {M : ℕ → List (List α)} (hM : ∀ r, M r ≠ [])
    (hM' : ∀ r, ∀ l ∈ M r, l ≠ []) :
    flatten d (fun r => (M r).flatten) = flatten d (flatten [] M) := by
  -- the blocks `flatten [] M i` are nonempty lists
  have hG : ∀ i, flatten [] M i ≠ [] := fun i => by
    obtain ⟨r, hr⟩ := flatten_mem hM i
    exact hM' r _ hr
  have hMf : ∀ r, (M r).flatten ≠ [] := fun r => by
    obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ (hM r)
    intro h
    exact hM' r l hl (List.flatten_eq_nil_iff.mp h l hl)
  funext n
  set A := (List.range (n + 1)).flatMap M
  -- the first `|A|` blocks of `flatten [] M` concatenate to the first `n + 1` lists `(M r).flatten`
  have key : (List.range A.length).flatMap (flatten [] M) =
      (List.range (n + 1)).flatMap (fun r => (M r).flatten) := by
    rw [List.flatMap_def, map_flatten_range hM, List.flatMap_def, List.flatten_flatten,
      List.map_map]
    rfl
  have hn : n < ((List.range A.length).flatMap (flatten [] M)).length := by
    rw [key]
    exact lt_of_lt_of_le (Nat.lt_succ_self n) (le_length_flatMap_range hMf _)
  rw [flatten_eq_getD hG A.length n hn, key]
  rfl

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



















section CopelandErdosProof

variable {b : ℕ} {a : ℕ → ℕ}































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

theorem length_padDigits (b r m : ℕ) : (padDigits b r m).length = r := by
  simp [padDigits]

theorem lt_of_mem_padDigits {b r m d : ℕ} (hb : 0 < b) (hd : d ∈ padDigits b r m) : d < b := by
  simp only [padDigits, List.mem_ofFn] at hd
  obtain ⟨i, rfl⟩ := hd
  exact Nat.mod_lt _ hb

theorem padDigits_mem_strs {b r : ℕ} (hb : 0 < b) (m : ℕ) : padDigits b r m ∈ strs b r :=
  mem_strs.2 ⟨length_padDigits b r m, fun _ hd => lt_of_mem_padDigits hb hd⟩

/-- Peeling off the last (least significant) digit. -/
theorem padDigits_succ (b r m : ℕ) :
    padDigits b (r + 1) m = padDigits b r (m / b) ++ [m % b] := by
  rw [padDigits, List.ofFn_succ', List.concat_eq_append, padDigits]
  congr 1
  · congr 1
    funext i
    have hi := i.isLt
    simp only [Fin.val_castSucc]
    have h : r + 1 - 1 - (i : ℕ) = (r - 1 - i) + 1 := by omega
    rw [h, pow_succ, mul_comm, ← Nat.div_div_eq_div_mul]
  · simp

/-- `m ↦ padDigits b r m` is injective on `m < b ^ r`. -/
theorem padDigits_inj {b : ℕ} (hb : 0 < b) {r m m' : ℕ} (hm : m < b ^ r) (hm' : m' < b ^ r)
    (h : padDigits b r m = padDigits b r m') : m = m' := by
  induction r generalizing m m' with
  | zero => simp at hm hm'; omega
  | succ r ih =>
    rw [padDigits_succ, padDigits_succ] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp [length_padDigits])
    simp only [List.cons.injEq, and_true] at h2
    have hd : m / b < b ^ r := by rw [Nat.div_lt_iff_lt_mul hb]; rwa [← pow_succ]
    have hd' : m' / b < b ^ r := by rw [Nat.div_lt_iff_lt_mul hb]; rwa [← pow_succ]
    have := ih hd hd' h1
    rw [← Nat.div_add_mod m b, ← Nat.div_add_mod m' b, this, h2]

/-! ## Abstract block sequences `flatten [] M` -/

section Abstract

variable (M : ℕ → List (List ℕ))





theorem nBlk_mono : Monotone (nBlk M) :=
  monotone_nat_of_le_succ fun R => by rw [nBlk_succ]; omega

variable {M}



/-- A block with index in `[nBlk M R, nBlk M (R + k))` comes from a group `M r`,
`R ≤ r < R + k`. -/
theorem blk_mem (hM : ∀ r, M r ≠ []) {R k i : ℕ} (h1 : nBlk M R ≤ i) (h2 : i < nBlk M (R + k)) :
    ∃ r, R ≤ r ∧ r < R + k ∧ flatten [] M i ∈ M r := by
  have hsplit : (List.range (R + k)).flatMap M =
      (List.range R).flatMap M ++ (List.map (fun x => R + x) (List.range k)).flatMap M := by
    rw [List.range_add, List.flatMap_append]
  have h2' := h2
  rw [nBlk, hsplit, List.length_append] at h2'
  rw [flatten_eq_getD hM (R + k) i h2, hsplit, List.getD_append_right _ _ _ _ h1]
  have hlt : i - nBlk M R < ((List.map (fun x => R + x) (List.range k)).flatMap M).length := by
    unfold nBlk at h1 ⊢; omega
  change ∃ r, R ≤ r ∧ r < R + k ∧ _ ∈ M r
  rw [show (List.flatMap M (List.range R)).length = nBlk M R from rfl, List.getD_eq_getElem _ _ hlt]
  have hmem := List.getElem_mem hlt
  rw [List.mem_flatMap] at hmem
  obtain ⟨r, hr, hmem⟩ := hmem
  simp only [List.mem_map, List.mem_range] at hr
  obtain ⟨a, ha, rfl⟩ := hr
  exact ⟨R + a, by omega, by omega, hmem⟩

theorem sum_range_eq_list (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range n, g i = ((List.range n).map g).sum := by
  induction n with
  | zero => simp
  | succ n ih => simp [Finset.sum_range_succ, List.range_succ, ih]

theorem sum_flatMap_range (f : List ℕ → ℝ) (R : ℕ) :
    (((List.range R).flatMap M).map f).sum = ∑ r ∈ Finset.range R, ((M r).map f).sum := by
  induction R with
  | zero => simp
  | succ R ih => simp [Finset.sum_range_succ, List.range_succ, List.flatMap_append, ih]

/-- Summing a function over the first `nBlk M R` blocks is summing it over the groups
`M 0, …, M (R-1)`. -/
theorem sum_blk (hM : ∀ r, M r ≠ []) (f : List ℕ → ℝ) (R : ℕ) :
    ∑ i ∈ Finset.range (nBlk M R), f (flatten [] M i) =
      ∑ r ∈ Finset.range R, ((M r).map f).sum := by
  rw [sum_range_eq_list, show (fun i => f (flatten [] M i)) = f ∘ flatten [] M from rfl,
    ← List.map_map, nBlk, map_flatten_range hM R, sum_flatMap_range]





theorem lt_nBlk_lev (hM : ∀ r, M r ≠ []) (J : ℕ) : J < nBlk M (lev hM J + 1) :=
  Nat.find_spec (exists_lev hM J)

theorem nBlk_lev_le (hM : ∀ r, M r ≠ []) (J : ℕ) : nBlk M (lev hM J) ≤ J := by
  rcases h : lev hM J with _ | s
  · simp [nBlk]
  · have := Nat.find_min (exists_lev hM J) (m := s) (by unfold lev at h; omega)
    omega

theorem tendsto_lev (hM : ∀ r, M r ≠ []) : Tendsto (lev hM) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro K
  refine ⟨nBlk M K, fun J hJ => ?_⟩
  by_contra hlt
  have := nBlk_mono M (show lev hM J + 1 ≤ K by omega)
  have := lt_nBlk_lev hM J
  omega

end Abstract

/-- If block lengths are `≥ 1` and tend to infinity, then `J / T J → 0`. -/
theorem tendsto_div_totalLen (B : ℕ → List ℕ) (hlen : ∀ i, 1 ≤ (B i).length)
    (hgrow : ∀ L : ℕ, ∃ i0, ∀ i, i0 ≤ i → L ≤ (B i).length) :
    Tendsto (fun J : ℕ => (J : ℝ) / totalLen B J) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L, hL⟩ := exists_nat_gt (2 / ε)
  obtain ⟨i0, hi0⟩ := hgrow L
  obtain ⟨N0, hN0⟩ := exists_nat_gt (2 * i0 / ε)
  refine ⟨max (i0 + 1) N0, fun J hJ => ?_⟩
  have hJ1 : i0 + 1 ≤ J := le_of_max_le_left hJ
  have hJ2 : N0 ≤ J := le_of_max_le_right hJ
  have hT1 : (J : ℝ) ≤ totalLen B J := by
    have : J ≤ totalLen B J := calc
      J = ∑ i ∈ Finset.range J, 1 := by simp
      _ ≤ totalLen B J := Finset.sum_le_sum fun i _ => hlen i
    exact_mod_cast this
  have hT2 : ((J - i0 : ℕ) : ℝ) * L ≤ totalLen B J := by
    have : (J - i0) * L ≤ totalLen B J := calc
      (J - i0) * L = ∑ i ∈ Finset.Ico i0 J, L := by simp
      _ ≤ ∑ i ∈ Finset.Ico i0 J, (B i).length :=
          Finset.sum_le_sum fun i hi => hi0 i (Finset.mem_Ico.1 hi).1
      _ ≤ totalLen B J := Finset.sum_le_sum_of_subset (by
          intro i; simp only [Finset.mem_Ico, Finset.mem_range]; omega)
    exact_mod_cast this
  rw [Nat.cast_sub (by omega)] at hT2
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hTpos : (0 : ℝ) < totalLen B J := lt_of_lt_of_le hJpos hT1
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hTpos]
  have h1 : 2 < ε * L := by rw [div_lt_iff₀ hε, mul_comm] at hL; exact hL
  have h2 : 2 * (i0 : ℝ) < ε * J := by
    rw [div_lt_iff₀ hε] at hN0
    have : (N0 : ℝ) ≤ J := by exact_mod_cast hJ2
    nlinarith
  have hJi : (1 : ℝ) ≤ J - i0 := by
    have : ((i0 + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast hJ1
    push_cast at this; linarith
  have A := mul_le_mul_of_nonneg_left hT2 hε.le
  have Bq := mul_le_mul_of_nonneg_left hT1 hε.le
  have C := mul_lt_mul_of_pos_right h1 (show (0 : ℝ) < J - i0 by linarith)
  nlinarith


/-! ## Champernowne's block sequences -/







theorem mem_grp {b : ℕ} {mult : ℕ → ℕ} {r : ℕ} {l : List ℕ} (h : l ∈ grp b mult r) :
    ∃ m < b ^ (r + 1), padDigits b (r + 1) m = l := by
  simp only [grp, memb, List.mem_flatten, List.mem_replicate] at h
  obtain ⟨_, ⟨_, rfl⟩, h⟩ := h
  simpa using h

theorem grp_ne_nil {b : ℕ} (hb : 0 < b) {mult : ℕ → ℕ} (h1 : ∀ r, 1 ≤ mult r) (r : ℕ) :
    grp b mult r ≠ [] := by
  obtain ⟨k, hk⟩ : ∃ k, mult r = k + 1 := ⟨mult r - 1, by have := h1 r; omega⟩
  have : 0 < b ^ (r + 1) := pow_pos hb _
  obtain ⟨n, hn⟩ : ∃ n, b ^ (r + 1) = n + 1 := ⟨b ^ (r + 1) - 1, by omega⟩
  simp [grp, hk, List.replicate_succ, memb, hn, List.range_succ]

theorem ne_nil_of_mem_grp {b : ℕ} {mult : ℕ → ℕ} {r : ℕ} {l : List ℕ} (h : l ∈ grp b mult r) :
    l ≠ [] := by
  obtain ⟨m, -, rfl⟩ := mem_grp h
  rw [← List.length_pos_iff, length_padDigits]; omega

theorem length_of_mem_grp {b : ℕ} {mult : ℕ → ℕ} {r : ℕ} {l : List ℕ} (h : l ∈ grp b mult r) :
    l.length = r + 1 := by
  obtain ⟨m, -, rfl⟩ := mem_grp h
  exact length_padDigits _ _ _

/-- The digit sequence is the concatenation of the blocks `flatten [] (grp b mult)`. -/
theorem champGen_eq {b : ℕ} (hb : 0 < b) {mult : ℕ → ℕ} (h1 : ∀ r, 1 ≤ mult r) :
    champGen b mult = flatten 0 (flatten [] (grp b mult)) := by
  rw [champGen, ← flatten_flatten (grp_ne_nil hb h1) (fun r l hl => ne_nil_of_mem_grp hl)]
  congr 1
  funext r
  simp [grp, List.flatten_flatten, List.map_replicate, level, List.flatMap_def, memb]

theorem sum_grp (b : ℕ) (mult : ℕ → ℕ) (r : ℕ) (f : List ℕ → ℝ) :
    ((grp b mult r).map f).sum =
      mult r * ∑ m ∈ Finset.range (b ^ (r + 1)), f (padDigits b (r + 1) m) := by
  simp [grp, List.map_flatten, List.sum_flatten, List.map_replicate, List.sum_replicate, memb,
    List.map_map, sum_range_eq_list, Function.comp_def]




















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

theorem solution {b : ℕ} (hb : 2 ≤ b) {mult : ℕ → ℕ} (K : ℕ) (h1 : ∀ r, 1 ≤ mult r)
    (hK : ∀ r, mult r ≤ K * (r + 1)) : IsNormalSeq b (champGen b mult) := by
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hM := grp_ne_nil hb0 h1
  rw [champGen_eq hb0 h1]
  set B := flatten [] (grp b mult) with hBdef
  have hBmem : ∀ i, ∃ r, B i ∈ grp b mult r := fun i => flatten_mem (d := []) hM i
  have hne : ∀ i, B i ≠ [] := fun i => by
    obtain ⟨r, hr⟩ := hBmem i; exact ne_nil_of_mem_grp hr
  have hlenJ : ∀ J, (B J).length ≤ lev hM J + 1 := by
    intro J
    obtain ⟨r, -, hr, hmem⟩ := blk_mem hM (R := 0) (k := lev hM J + 1) (i := J)
      (by simp [nBlk]) (by simpa using lt_nBlk_lev hM J)
    rw [length_of_mem_grp hmem]; omega
  have hTcast : ∀ J, (totalLen B J : ℝ) = ∑ i ∈ Finset.range J, ((B i).length : ℝ) := by
    intro J; simp [totalLen]
  have hTlow : ∀ J, 1 ≤ lev hM J → (b : ℝ) ^ lev hM J ≤ totalLen B J := by
    intro J hJ
    obtain ⟨s, hs⟩ : ∃ s, lev hM J = s + 1 := ⟨lev hM J - 1, by omega⟩
    have hle := nBlk_lev_le hM J
    rw [hs] at hle
    have hmono : totalLen B (nBlk (grp b mult) (s + 1)) ≤ totalLen B J :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hle)
    have heq : (totalLen B (nBlk (grp b mult) (s + 1)) : ℝ) =
        ∑ r ∈ Finset.range (s + 1), (mult r : ℝ) * ((b : ℝ) ^ (r + 1) * (r + 1)) := by
      rw [hTcast, sum_blk hM (fun l => (l.length : ℝ))]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [sum_grp]
      simp only [length_padDigits, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast; ring
    have hterm : (b : ℝ) ^ (s + 1) ≤ (mult s : ℝ) * ((b : ℝ) ^ (s + 1) * (s + 1)) := by
      have hm1 : (1 : ℝ) ≤ mult s := by exact_mod_cast h1 s
      have hbp : 0 ≤ (b : ℝ) ^ (s + 1) := by positivity
      have hs0 : (0 : ℝ) ≤ s := by positivity
      have X : (1 : ℝ) ≤ mult s * (s + 1) := by nlinarith
      have Y := mul_le_mul_of_nonneg_right X hbp
      linarith
    rw [hs]
    calc (b : ℝ) ^ (s + 1) ≤ _ := hterm
      _ ≤ ∑ r ∈ Finset.range (s + 1), (mult r : ℝ) * ((b : ℝ) ^ (r + 1) * (r + 1)) :=
          Finset.single_le_sum (f := fun r => (mult r : ℝ) * ((b : ℝ) ^ (r + 1) * (r + 1)))
            (fun r _ => by positivity) (Finset.self_mem_range_succ s)
      _ = _ := heq.symm
      _ ≤ _ := by exact_mod_cast hmono
  have hev : ∀ᶠ J in atTop, 1 ≤ lev hM J := (tendsto_lev hM).eventually_ge_atTop 1
  have hS : Tendsto (fun J => lev hM J + 1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (tendsto_lev hM)
  have hdecay : ∀ (k : ℕ) (ρ A : ℝ), 0 ≤ ρ → ρ < 1 →
      Tendsto (fun J => A * (((lev hM J + 1 : ℕ) : ℝ) ^ k * ρ ^ (lev hM J + 1))) atTop (𝓝 0) := by
    intro k ρ A h0 h1'
    have := (tendsto_pow_const_mul_const_pow_of_abs_lt_one k (r := ρ)
      (by rw [abs_of_nonneg h0]; exact h1')).comp hS
    simpa using this.const_mul A
  apply isNormalSeq_flatten hb B hne
  · intro i d hd
    obtain ⟨r, hr⟩ := hBmem i
    obtain ⟨m, -, hm⟩ := mem_grp hr
    rw [← hm] at hd
    exact lt_of_mem_padDigits hb0 hd
  · apply tendsto_div_totalLen
    · intro i; have := List.length_pos_iff.2 (hne i); omega
    · intro L
      refine ⟨nBlk (grp b mult) L, fun i hi => ?_⟩
      obtain ⟨r, hr, -, hmem⟩ := blk_mem hM (R := L) (k := i + 1) hi
        (by have := le_nBlk hM (L + (i + 1)); omega)
      rw [length_of_mem_grp hmem]; omega
  · refine squeeze_zero' (Eventually.of_forall fun J => by positivity) ?_
      (hdecay 1 (1 / b) b (by positivity) (by rw [div_lt_one (by positivity)]; exact hbR))
    filter_upwards [hev] with J hJ
    have hT := hTlow J hJ
    have hTpos : 0 < (totalLen B J : ℝ) := lt_of_lt_of_le (by positivity) hT
    rw [div_le_iff₀ hTpos]
    have hl : ((B J).length : ℝ) ≤ lev hM J + 1 := by exact_mod_cast hlenJ J
    have key : (b : ℝ) * (((lev hM J + 1 : ℕ) : ℝ) ^ 1 * (1 / b) ^ (lev hM J + 1)) *
        (b : ℝ) ^ (lev hM J) = lev hM J + 1 := by
      rw [one_div, inv_pow, pow_succ]; push_cast; field_simp; ring
    calc ((B J).length : ℝ) ≤ _ := hl
      _ = _ := key.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
  · intro P _ β C hβ hP
    have hC : 0 ≤ C := by
      have := hP 0; rw [pow_zero, mul_one] at this; exact le_trans (Nat.cast_nonneg _) this
    set γ := max β 1 with hγdef
    have hγ1 : 1 ≤ γ := le_max_right _ _
    have hγb : γ < b := max_lt hβ hbR
    have hPγ : ∀ n, (((strs b n).filter P).card : ℝ) ≤ C * γ ^ n := by
      intro n
      by_cases h0 : 0 ≤ β
      · exact (hP n).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (le_max_left _ _) n) hC)
      · have hC0 : C = 0 := by
          have := hP 1; rw [pow_one] at this
          have := le_trans (Nat.cast_nonneg _) this
          nlinarith
        have := hP n; rw [hC0] at this ⊢; simpa using this
    have hcnt : ∀ r, ∑ m ∈ Finset.range (b ^ (r + 1)), (if P (padDigits b (r + 1) m) then
        ((padDigits b (r + 1) m).length : ℝ) else 0) ≤ ((r : ℝ) + 1) * (C * γ ^ (r + 1)) := by
      intro r
      rw [← Finset.sum_filter]
      simp only [length_padDigits]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hc : ((Finset.range (b ^ (r + 1))).filter (fun m => P (padDigits b (r + 1) m))).card ≤
          ((strs b (r + 1)).filter P).card := by
        apply Finset.card_le_card_of_injOn (padDigits b (r + 1))
        · intro m hm
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hm
          simp only [Finset.coe_filter, Set.mem_ofPred_eq]
          exact ⟨padDigits_mem_strs hb0 m, hm.2⟩
        · intro m hm m' hm' h
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq] at hm hm'
          exact padDigits_inj hb0 hm.1 hm'.1 h
      have h3 : (((Finset.range (b ^ (r + 1))).filter (fun m => P (padDigits b (r + 1) m))).card
          : ℝ) ≤ C * γ ^ (r + 1) := le_trans (by exact_mod_cast hc) (hPγ (r + 1))
      push_cast
      have : (0 : ℝ) ≤ r := by positivity
      nlinarith
    have hnum : ∀ J, (∑ i ∈ (Finset.range J).filter (fun i => P (B i)), ((B i).length : ℝ)) ≤
        K * C * (((lev hM J + 1 : ℕ) : ℝ) ^ 3 * γ ^ (lev hM J + 1)) := by
      intro J
      set S := lev hM J + 1 with hSdef
      have hJS : J ≤ nBlk (grp b mult) S := (lt_nBlk_lev hM J).le
      rw [Finset.sum_filter]
      calc _ ≤ ∑ i ∈ Finset.range (nBlk (grp b mult) S),
              (if P (B i) then ((B i).length : ℝ) else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hJS)
              (fun i _ _ => by split_ifs <;> positivity)
        _ = ∑ r ∈ Finset.range S, (mult r : ℝ) * ∑ m ∈ Finset.range (b ^ (r + 1)),
              (if P (padDigits b (r + 1) m) then ((padDigits b (r + 1) m).length : ℝ) else 0) := by
            rw [sum_blk hM (fun l => if P l then (l.length : ℝ) else 0)]
            exact Finset.sum_congr rfl fun r _ => sum_grp _ _ _ _
        _ ≤ ∑ r ∈ Finset.range S, ((K : ℝ) * S) * ((S : ℝ) * (C * γ ^ S)) := by
            apply Finset.sum_le_sum
            intro r hr
            rw [Finset.mem_range] at hr
            have hm : (mult r : ℝ) ≤ K * S := by
              have : mult r ≤ K * S := le_trans (hK r) (Nat.mul_le_mul_left K hr)
              exact_mod_cast this
            have hrS : (r : ℝ) + 1 ≤ S := by exact_mod_cast hr
            have hin2 : ((r : ℝ) + 1) * (C * γ ^ (r + 1)) ≤ S * (C * γ ^ S) :=
              mul_le_mul hrS (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hγ1 hr) hC)
                (by positivity) (by positivity)
            have hnn : (0 : ℝ) ≤ ∑ m ∈ Finset.range (b ^ (r + 1)),
                (if P (padDigits b (r + 1) m) then ((padDigits b (r + 1) m).length : ℝ) else 0) :=
              Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
            calc _ ≤ ((K : ℝ) * S) * _ := mul_le_mul_of_nonneg_right hm hnn
              _ ≤ _ := mul_le_mul_of_nonneg_left ((hcnt r).trans hin2) (by positivity)
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    refine squeeze_zero' (Eventually.of_forall fun J => by positivity) ?_
      (hdecay 3 (γ / b) (K * C * b) (by positivity) (by rw [div_lt_one (by positivity)]; exact hγb))
    filter_upwards [hev] with J hJ
    have hT := hTlow J hJ
    have hTpos : 0 < (totalLen B J : ℝ) := lt_of_lt_of_le (by positivity) hT
    rw [div_le_iff₀ hTpos]
    have key : (K : ℝ) * C * (((lev hM J + 1 : ℕ) : ℝ) ^ 3 * γ ^ (lev hM J + 1)) =
        K * C * b * (((lev hM J + 1 : ℕ) : ℝ) ^ 3 * (γ / b) ^ (lev hM J + 1)) *
          (b : ℝ) ^ (lev hM J) := by
      rw [div_pow, pow_succ (b : ℝ)]; field_simp
    calc _ ≤ _ := hnum J
      _ = _ := key
      _ ≤ _ := mul_le_mul_of_nonneg_left hT (by positivity)
