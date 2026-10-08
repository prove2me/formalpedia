-- Prove2me | solution 1 for Normal.large_deviation
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T15:30:10.671049+00:00
-- url     : https://prove2.me/submissions/5687d88b-c2a7-4107-a9f4-7dfc104bc276

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

































variable {b : ℕ} {B : ℕ → List ℕ}







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

theorem solution {b : ℕ} (hb : 2 ≤ b) {w : List ℕ} (hw : w ≠ [])
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
