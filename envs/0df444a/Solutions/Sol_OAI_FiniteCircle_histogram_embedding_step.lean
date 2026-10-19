-- Prove2me | solution 1 for OAI.FiniteCircle.histogram_embedding_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T17:01:26.957109+00:00
-- url     : https://prove2.me/submissions/a095889a-ab95-4742-9c4e-534a51a55d9c

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/HistogramEmbedding.lean:L12-L113
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.histogram_embedding_step. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedDescent
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Primes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Fourier
import Definitions.Def_OAI_Combinatorics_FiniteCircle_DyadicShifts
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TreeBranching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Translations
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Distortion
import Definitions.Def_OAI_Combinatorics_FiniteCircle_BlockMatching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_OffsetRecovery
import Definitions.Def_OAI_Combinatorics_FiniteCircle_RandomCodes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Codes
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Lower
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Windows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Partitions
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Histograms
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Separation
import Theorems.Thm_OAI_FiniteCircle_deficit_le_sum_blocks
import Theorems.Thm_OAI_FiniteCircle_exists_separating_scale
import Theorems.Thm_OAI_FiniteCircle_expect_histDist_ofFn_ge
import Theorems.Thm_OAI_FiniteCircle_finite_partition
import Theorems.Thm_OAI_FiniteCircle_histogram_forward_bound

-- ---- from OAI.Combinatorics.FiniteCircle.Edit ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace EditStep
variable {α β : Type*} {x y : List α}

end EditStep

namespace EditScript
variable {α β : Type*} {n m : ℕ} {x y z : List α}

end EditScript

theorem lcs_mono {α : Type*} {x y x' y' : List α} (hx : x <+ x') (hy : y <+ y') :
    lcs x y ≤ lcs x' y' := by
  obtain ⟨z, hz, hw, heq⟩ := lcs_exists x y
  rw [← heq]
  exact le_lcs (hz.trans hx) (hw.trans hy)

theorem lcs_reverse {α : Type*} (x y : List α) : lcs x.reverse y.reverse = lcs x y := by
  apply Nat.le_antisymm
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists x.reverse y.reverse
    have h := le_lcs hx.reverse hy.reverse
    simpa only [List.reverse_reverse, List.length_reverse, hz] using h
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
    have h := le_lcs hx.reverse hy.reverse
    simpa only [List.length_reverse, hz] using h

theorem lcs_append_common_left {α : Type*} (z x y : List α) :
    lcs (z ++ x) (z ++ y) = z.length + lcs x y := by
  induction z with
  | nil => simp
  | cons a z ih => simp only [List.cons_append, lcs_cons_cons, List.length_cons, ih]; omega

theorem lcs_append_common_right {α : Type*} (x y z : List α) :
    lcs (x ++ z) (y ++ z) = lcs x y + z.length := by
  rw [← lcs_reverse (x ++ z) (y ++ z)]
  simp only [List.reverse_append, lcs_append_common_left, lcs_reverse, List.length_reverse]
  omega

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Matching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem segment_sublist {α : Type*} (x : List α) (start size : ℕ) :
    segment x start size <+ x := (List.take_sublist _ _).trans (List.drop_sublist _ _)

namespace Slide
variable {α : Type*} {x y : List α}

theorem symm (h : Slide x y) : Slide y x := by
  cases h with
  | forward u v t a b => exact .backward u v t a b
  | backward u v t a b => exact .forward u v t a b

theorem append_left (h : Slide x y) (l : List α) : Slide (l ++ x) (l ++ y) := by
  cases h with
  | forward u v t a b => simpa only [List.append_assoc] using Slide.forward (l ++ u) v t a b
  | backward u v t a b => simpa only [List.append_assoc] using Slide.backward (l ++ u) v t a b

theorem append_right (h : Slide x y) (l : List α) : Slide (x ++ l) (y ++ l) := by
  cases h with
  | forward u v t a b =>
    simpa only [List.append_assoc, List.cons_append] using Slide.forward u v (t ++ l) a b
  | backward u v t a b =>
    simpa only [List.append_assoc, List.cons_append] using Slide.backward u v (t ++ l) a b

end Slide

namespace SlidePath
variable {α : Type*} {x y z : List α} {n m : ℕ}

theorem trans (h : SlidePath n x y) (g : SlidePath m y z) : SlidePath (n + m) x z := by
  induction h with
  | nil => simpa using g
  | cons h hs ih => simpa only [Nat.add_right_comm] using SlidePath.cons h (ih g)

theorem symm (h : SlidePath n x y) : SlidePath n y x := by
  induction h with
  | nil x => exact .nil x
  | cons h hs ih => exact ih.trans (.cons h.symm (.nil _))

theorem append_left (h : SlidePath n x y) (l : List α) : SlidePath n (l ++ x) (l ++ y) := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih => exact .cons (h.append_left l) ih

theorem append_right (h : SlidePath n x y) (l : List α) : SlidePath n (x ++ l) (y ++ l) := by
  induction h with
  | nil => exact .nil _
  | cons h hs ih => exact .cons (h.append_right l) ih

theorem to_padded_sublist (h : z <+ x) (a : α) :
    SlidePath (x.length - z.length) x (z ++ List.replicate (x.length - z.length) a) := by
  induction h with
  | slnil => simpa using SlidePath.nil ([] : List α)
  | @cons z x b h ih =>
    have hl := h.length_le
    have hfirst : Slide (b :: x) (x ++ [a]) := by
      simpa using Slide.forward ([] : List α) x [] b a
    have ht := SlidePath.cons hfirst (ih.append_right [a])
    simpa only [List.length_cons,
      show x.length + 1 - z.length = (x.length - z.length) + 1 by omega,
      List.append_assoc, List.replicate_succ', List.concat_eq_append] using ht
  | cons_cons b h ih =>
    simpa using ih.append_left [b]
end SlidePath

theorem exists_slidePath {α : Type*} (a : α) {x y : List α} (h : x.length = y.length) :
    SlidePath (2 * deficit x y) x y := by
  obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
  have h1 := SlidePath.to_padded_sublist hx a
  have h2 := SlidePath.to_padded_sublist hy a
  rw [← h] at h2
  have ht := h1.trans h2.symm
  simpa only [deficit, hz, two_mul] using ht

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

namespace WordMatching
variable {α : Type*} {x y : List α} {q : ℕ}

end WordMatching

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Fourier ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

open scoped BigOperators ComplexConjugate
open RCLike Module

open scoped BigOperators

namespace HasCutRepresentation
variable {X : Type*} [Fintype X]

theorem zero : HasCutRepresentation (fun _ _ : X => 0) := by
  classical
  exact ⟨fun _ => 0, fun _ => le_rfl, by simp⟩

theorem congr {ρ σ : X → X → ℝ} (h : HasCutRepresentation ρ)
    (he : ∀ x y, σ x y = ρ x y) : HasCutRepresentation σ := by
  obtain ⟨a, ha, hρ⟩ := h
  exact ⟨a, ha, fun x y => (he x y).trans (hρ x y)⟩

theorem add {ρ σ : X → X → ℝ} (hρ : HasCutRepresentation ρ)
    (hσ : HasCutRepresentation σ) : HasCutRepresentation (fun x y => ρ x y + σ x y) := by
  obtain ⟨a, ha, hρ⟩ := hρ
  obtain ⟨b, hb, hσ⟩ := hσ
  refine ⟨fun c => a c + b c, fun c => add_nonneg (ha c) (hb c), ?_⟩
  intro x y
  simp only [add_mul, Finset.sum_add_distrib, ← hρ, ← hσ]

theorem mul {ρ : X → X → ℝ} (h : HasCutRepresentation ρ) {r : ℝ} (hr : 0 ≤ r) :
    HasCutRepresentation (fun x y => r * ρ x y) := by
  obtain ⟨a, ha, hρ⟩ := h
  refine ⟨fun c => r * a c, fun c => mul_nonneg hr (ha c), ?_⟩
  intro x y
  simp only [mul_assoc, ← Finset.mul_sum, ← hρ]

theorem cut (c : X → Bool) : HasCutRepresentation (cutDistance c) := by
  classical
  refine ⟨fun d => if d = c then 1 else 0, ?_, ?_⟩
  · intro d; dsimp; split <;> norm_num
  · intro x y; simp

theorem sum {ι : Type*} (s : Finset ι) (ρ : ι → X → X → ℝ)
    (h : ∀ i ∈ s, HasCutRepresentation (ρ i)) :
    HasCutRepresentation (fun x y => ∑ i ∈ s, ρ i x y) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simpa using (zero (X := X))
  | cons i s hi ih =>
    have ht := (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))
    simpa only [Finset.sum_cons] using ht
end HasCutRepresentation

theorem finite_scalar_cuts {X : Type*} [Fintype X] (s : Finset ℝ) :
    ∀ f : X → ℝ, (∀ x, f x ∈ s) →
      HasCutRepresentation (fun x y => |f x - f y|) := by
  classical
  induction s using Finset.induction_on_max with
  | empty =>
    intro f hf
    exact HasCutRepresentation.zero.congr (fun x _ => (Finset.notMem_empty _ (hf x)).elim)
  | insert a s ha ih =>
    intro f hf
    by_cases hs : s.Nonempty
    · let b := s.max' hs
      have hb : b ∈ s := Finset.max'_mem s hs
      have hba : b < a := ha b hb
      let g : X → ℝ := fun x => if f x = a then b else f x
      have hg : ∀ x, g x ∈ s := by
        intro x
        dsimp [g]
        split_ifs with h
        · exact hb
        · exact (Finset.mem_insert.mp (hf x)).resolve_left h
      have hle : ∀ x, f x ≠ a → f x ≤ b := by
        intro x hx
        exact Finset.le_max' s _ ((Finset.mem_insert.mp (hf x)).resolve_left hx)
      let c : X → Bool := fun x => decide (f x = a)
      have he : ∀ x y, |f x - f y| = |g x - g y| + (a - b) * cutDistance c x y := by
        intro x y
        by_cases hx : f x = a <;> by_cases hy : f y = a
        · simp [g, c, cutDistance, hx, hy]
        · have hya := (hle y hy).trans hba.le
          simp [g, c, cutDistance, hx, hy, abs_of_nonneg (sub_nonneg.mpr hya),
            abs_of_nonneg (sub_nonneg.mpr (hle y hy))]
        · have hxa := (hle x hx).trans hba.le
          simp [g, c, cutDistance, hx, hy, abs_of_nonpos (sub_nonpos.mpr hxa),
            abs_of_nonpos (sub_nonpos.mpr (hle x hx))]
        · simp [g, c, cutDistance, hx, hy]
      exact ((ih g hg).add ((HasCutRepresentation.cut c).mul (sub_nonneg.mpr hba.le))).congr he
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have hfa : ∀ x, f x = a := by simpa [hs0] using hf
      exact HasCutRepresentation.zero.congr (by intro x y; simp [hfa])

theorem scalar_cuts {X : Type*} [Fintype X] (f : X → ℝ) :
    HasCutRepresentation (fun x y => |f x - f y|) := by
  classical
  exact finite_scalar_cuts (Finset.univ.image f) f (by intro x; simp)

theorem finite_l1_cuts {X ι : Type*} [Fintype X] [Fintype ι] (f : X → ι → ℝ) :
    HasCutRepresentation (fun x y => ∑ i, |f x i - f y i|) := by
  exact HasCutRepresentation.sum Finset.univ _ (fun i _ => scalar_cuts (fun x => f x i))

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Windows ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem segment_segment {α : Type*} (x : List α) (start size r len : ℕ)
    (h : r + len ≤ size) : segment (segment x start size) r len = segment x (start + r) len := by
  unfold segment
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

open scoped BigOperators List

open scoped BigOperators

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Partitions ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem expect_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ μ.expect f := Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω))

end FiniteLaw

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Histograms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem histDist_nonneg {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X) :
    0 ≤ histDist label xs ys := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem histDist_symm {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X) :
    histDist label xs ys = histDist label ys xs := by
  unfold histDist
  simp only [abs_sub_comm]

theorem histMap_distance {X Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) (xs ys : List X) :
    ∑ i, |histMap μ label xs i - histMap μ label ys i| =
      μ.expect (fun ω => histDist (label ω) xs ys) := by
  simp only [histMap, ← mul_sub, abs_mul, abs_of_nonneg (μ.nonneg _),
    Fintype.sum_prod_type, FiniteLaw.expect, histDist, Finset.mul_sum]

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Separation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem coordDist_triangle {X ι : Type*} [Fintype ι] (F : X → ι → ℝ) (x y z : X) :
    coordDist F x z ≤ coordDist F x y + coordDist F y z := by
  unfold coordDist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_sub_le _ _ _)

theorem normalizeWord_val {α : Type*} (a : α) {m : ℕ} {x : List α} (h : x.length ≤ m) :
    (normalizeWord a m x).val = x ++ List.replicate (m-x.length) a := by
  simp only [normalizeWord, List.take_of_length_le h]

theorem normalizeWord_deficit {α : Type*} (a : α) {m : ℕ} {x y : List α}
    (hx : x.length ≤ m) (hy : x.length = y.length) :
    deficit (normalizeWord a m x).val (normalizeWord a m y).val = deficit x y := by
  rw [normalizeWord_val a hx, normalizeWord_val a (by omega), ← hy]
  simp only [deficit, List.length_append, List.length_replicate, lcs_append_common_right]
  omega

theorem windowWords_ofFn {α : Type*} (a : α) (x : List α) (start m s : ℕ) :
    windowWords a x start m s =
      List.ofFn (fun r : Fin s => normalizeWord a m (segment x (start+r) (m-s+1))) := by
  simp [windowWords, windows, List.map_ofFn, Function.comp_def]

theorem windows_segment {α : Type*} (x : List α) {start m s : ℕ}
    (_hs : 1 ≤ s) (hsm : s ≤ m) :
    windows (segment x start m) 0 m s = windows x start m s := by
  unfold windows
  congr 1
  funext r
  simp only [Nat.zero_add]
  exact segment_segment x start m r (m-s+1) (by have := r.isLt; omega)

theorem windowWords_segment {α : Type*} (a : α) (x : List α) {start m s : ℕ}
    (hs : 1 ≤ s) (hsm : s ≤ m) :
    windowWords a (segment x start m) 0 m s = windowWords a x start m s := by
  simp only [windowWords, windows_segment x hs hsm]

theorem cross_window_deficit {α : Type*} (a : α) {x y : List α} {m s : ℕ}
    (hx : x.length = m) (hy : y.length = m) (hs : 1 ≤ s) (hsm : s ≤ m)
    (hq : 2*s ≤ deficit x y + 1) (i j : Fin s) :
    s ≤ deficit (normalizeWord a m (segment x i (m-s+1))).val
      (normalizeWord a m (segment y j (m-s+1))).val := by
  have hxi : (segment x i (m-s+1)).length = m-s+1 :=
    length_segment (by have := i.isLt; omega)
  have hyj : (segment y j (m-s+1)).length = m-s+1 :=
    length_segment (by have := j.isLt; omega)
  rw [normalizeWord_deficit a (by omega) (by omega)]
  have hmono := lcs_mono (segment_sublist x i (m-s+1)) (segment_sublist y j (m-s+1))
  have hb := lcs_le_length_left x y
  simp only [deficit, hxi] at *
  omega

theorem partitionRate_nonneg (s : ℕ) : 0 ≤ partitionRate s := by
  unfold partitionRate
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (Nat.cast_nonneg _)

theorem partition_collision_bound {s : ℕ} (hs : 1 ≤ s) {ρ : ℝ} (hρ : s ≤ ρ) :
    Real.exp (-partitionRate s * ρ) ≤ ((s : ℝ)+1)⁻¹ ^ 4 := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  calc
    _ ≤ Real.exp (-partitionRate s * s) := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonpos_left hρ (neg_nonpos.mpr (partitionRate_nonneg s)))
    _ = _ := by
      rw [show -partitionRate s * s = -(4 * Real.log ((s:ℝ)+1)) by
        unfold partitionRate; field_simp]
      rw [Real.exp_neg, show 4 * Real.log ((s:ℝ)+1) = (4:ℕ) * Real.log ((s:ℝ)+1) by norm_num,
        Real.exp_nat_mul, Real.exp_log (by positivity), inv_pow]

theorem scale_collision_union {s : ℕ} : (s : ℝ)^2 * (((s:ℝ)+1)⁻¹ ^ 4) ≤ 1/2 := by
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  rw [inv_pow, mul_inv_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg ((s:ℝ)^2), sq_nonneg ((s:ℝ)-1)]

theorem block_histogram_lower {α Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]
    (a : α) {m s : ℕ} (F : List.Vector α m → ι → ℝ)
    (hF : ∀ u v, (deficit u.val v.val : ℝ) ≤ coordDist F u v)
    (μ : FiniteLaw Ω) (label : Ω → List.Vector α m → Y)
    (he : ∀ u v, μ.event (fun ω => label ω u = label ω v) =
      Real.exp (-partitionRate s * coordDist F u v))
    {x y : List α} (hx : x.length = m) (hy : y.length = m)
    (hs : 1 ≤ s) (hsm : s ≤ m) (hq : 2*s ≤ deficit x y + 1) :
    (s:ℝ) ≤ μ.expect (fun ω => histDist (label ω) (windowWords a x 0 m s) (windowWords a y 0 m s)) := by
  rw [windowWords_ofFn, windowWords_ofFn]
  simp only [Nat.zero_add]
  apply expect_histDist_ofFn_ge μ label _ _ (((s:ℝ)+1)⁻¹^4) _ scale_collision_union
  intro i j
  rw [he]
  apply partition_collision_bound hs
  exact (Nat.cast_le.mpr (cross_window_deficit a hx hy hs hsm hq i j)).trans (hF _ _)

theorem histogram_slide_bound {α Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]
    (a : α) {m s : ℕ} (F : List.Vector α m → ι → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hF : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val)
    (μ : FiniteLaw Ω) (label : Ω → List.Vector α m → Y)
    (he : ∀ u v, μ.event (fun ω => label ω u = label ω v) =
      Real.exp (-partitionRate s * coordDist F u v))
    {x y : List α} (hxy : Slide x y) (b : ℕ) (hs : 1 ≤ s) (hsm : s ≤ m) :
    (∑ j : Fin b, μ.expect (fun ω => histDist (label ω)
      (windowWords a x (j*m) m s) (windowWords a y (j*m) m s))) ≤
      2*b + 32 * Real.log ((s:ℝ)+1) * Λ := by
  cases hxy with
  | forward u v t c d => exact histogram_forward_bound a F Λ hΛ hF μ label he u v t c d b hs hsm
  | backward u v t c d =>
    simp only [histDist_symm (label _)
      (windowWords a (u ++ v ++ d :: t) _ _ _)]
    exact histogram_forward_bound a F Λ hΛ hF μ label he u v t c d b hs hsm

theorem SlidePath.coordDist_le {α ι : Type*} [Fintype ι] {x y : List α} {n : ℕ}
    (h : SlidePath n x y) (F : List α → ι → ℝ) (K : ℝ)
    (hF : ∀ u v, Slide u v → coordDist F u v ≤ K) : coordDist F x y ≤ n*K := by
  induction h with
  | nil => simp [coordDist]
  | @cons n x y z h hs ih =>
    calc
      _ ≤ coordDist F x y + coordDist F y z := coordDist_triangle F x y z
      _ ≤ K + n*K := add_le_add (hF x y h) ih
      _ = _ := by push_cast; ring

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.HistogramEmbedding ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem histogram_embedding_step {α : Type*} [Fintype α] (a : α) {m M : ℕ}
    (hm : 0 < m) (b : ℕ) (F : List.Vector α m → Fin M → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hFlo : ∀ u v, (deficit u.val v.val : ℝ) ≤ coordDist F u v)
    (hFhi : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val) :
    ∃ M' : ℕ, ∃ F' : List.Vector α (b*m) → Fin M' → ℝ,
      ∀ x y, (deficit x.val y.val : ℝ) ≤ coordDist F' x y ∧
        coordDist F' x y ≤ (16 * (Nat.log 2 m + 1) *
          (b + 16 * Real.log ((m:ℝ)+1) * Λ)) * deficit x.val y.val := by
  classical
  let X := List.Vector α m
  let : DecidableEq X := Classical.decEq X
  let Ω := PartitionSpace X
  let K := Nat.log 2 m + 1
  have hav (k : Fin K) : 1 ≤ 2^k.val ∧ 2^k.val ≤ m := by
    refine ⟨?_, Nat.pow_le_of_le_log hm.ne' (by have := k.isLt; dsimp [K] at *; omega)⟩
    have hp : 0 < 2^k.val := pow_pos (by norm_num) _
    omega
  have hp (k : Fin K) := finite_partition (finite_l1_cuts F) (partitionRate (2^k.val))
    (partitionRate_nonneg (2^k.val))
  choose μ label he using hp
  let I := (Fin b × Fin K) × (Ω × Ω)
  let Φ : List α → I → ℝ := fun x i =>
    4 * histMap (μ i.1.2) (label i.1.2) (windowWords a x (i.1.1*m) m (2^i.1.2.val)) i.2
  have hΦ (x y : List α) : coordDist Φ x y =
      4 * ∑ j : Fin b, ∑ k : Fin K, (μ k).expect (fun ω => histDist (label k ω)
        (windowWords a x (j*m) m (2^k.val)) (windowWords a y (j*m) m (2^k.val))) := by
    unfold coordDist
    rw [Fintype.sum_prod_type]
    simp only [Φ, ← mul_sub, abs_mul, show |(4:ℝ)| = 4 by norm_num]
    simp_rw [← Finset.mul_sum, histMap_distance]
    rw [Fintype.sum_prod_type]
  have hnonneg (x y : List α) (j : Fin b) (k : Fin K) :
      0 ≤ (μ k).expect (fun ω => histDist (label k ω)
        (windowWords a x (j*m) m (2^k.val)) (windowWords a y (j*m) m (2^k.val))) :=
    (μ k).expect_nonneg (fun _ => histDist_nonneg _ _ _)
  have hlo (x y : List.Vector α (b*m)) : (deficit x.val y.val : ℝ) ≤ coordDist Φ x.val y.val := by
    have hx (j : Fin b) : (segment x.val (j*m) m).length = m := by
      apply length_segment
      rw [x.property]
      have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt j.isLt)
      simpa only [Nat.succ_mul] using h
    have hy (j : Fin b) : (segment y.val (j*m) m).length = m := by
      apply length_segment
      rw [y.property]
      have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt j.isLt)
      simpa only [Nat.succ_mul] using h
    have hblock (j : Fin b) : (deficit (segment x.val (j*m) m) (segment y.val (j*m) m) : ℝ) ≤
        4 * ∑ k : Fin K, (μ k).expect (fun ω => histDist (label k ω)
          (windowWords a x.val (j*m) m (2^k.val)) (windowWords a y.val (j*m) m (2^k.val))) := by
      let q := deficit (segment x.val (j*m) m) (segment y.val (j*m) m)
      by_cases hq : q = 0
      · change (q:ℝ) ≤ _
        rw [hq, Nat.cast_zero]
        exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun k _ => hnonneg x.val y.val j k))
      · have hqm : q ≤ m := by dsimp [q, deficit]; rw [hx]; omega
        obtain ⟨k, hs, hsm, hqs, hsq⟩ := exists_separating_scale (Nat.pos_of_ne_zero hq) hqm
        have hsep := block_histogram_lower a F hFlo (μ k) (label k) (he k)
          (hx j) (hy j) hs hsm hsq
        rw [windowWords_segment a x.val hs hsm, windowWords_segment a y.val hs hsm] at hsep
        calc
          _ = (q:ℝ) := rfl
          _ ≤ 4 * (2^k.val : ℕ) := by exact_mod_cast hqs
          _ ≤ 4 * (μ k).expect (fun ω => histDist (label k ω)
              (windowWords a x.val (j*m) m (2^k.val)) (windowWords a y.val (j*m) m (2^k.val))) := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (fun k _ => hnonneg x.val y.val j k) (Finset.mem_univ _)) (by norm_num)
    calc
      _ ≤ ∑ j : Fin b, (deficit (segment x.val (j*m) m) (segment y.val (j*m) m) : ℝ) := by
        exact_mod_cast deficit_le_sum_blocks x.property y.property
      _ ≤ ∑ j : Fin b, 4 * ∑ k : Fin K, (μ k).expect (fun ω => histDist (label k ω)
          (windowWords a x.val (j*m) m (2^k.val)) (windowWords a y.val (j*m) m (2^k.val))) :=
        Finset.sum_le_sum (fun j _ => hblock j)
      _ = _ := by rw [hΦ, Finset.mul_sum]
  have hmove (x y : List α) (hxy : Slide x y) : coordDist Φ x y ≤
      4*K * (2*b + 32 * Real.log ((m:ℝ)+1) * Λ) := by
    rw [hΦ, Finset.sum_comm]
    calc
      _ ≤ 4 * ∑ k : Fin K, (2*b + 32 * Real.log ((m:ℝ)+1) * Λ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro k _
        refine (histogram_slide_bound a F Λ hΛ hFhi (μ k) (label k) (he k) hxy b
          (hav k).1 (hav k).2).trans ?_
        have hlog : Real.log (((2^k.val : ℕ):ℝ)+1) ≤ Real.log ((m:ℝ)+1) :=
          Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right (hav k).2 1)
        gcongr
      _ = _ := by simp; ring
  let e := Fintype.equivFin I
  let F' : List.Vector α (b*m) → Fin (Fintype.card I) → ℝ := fun x i => Φ x.val (e.symm i)
  have hdist (x y : List.Vector α (b*m)) : coordDist F' x y = coordDist Φ x.val y.val :=
    e.symm.sum_comp (fun i => |Φ x.val i - Φ y.val i|)
  refine ⟨Fintype.card I, F', fun x y => ⟨?_, ?_⟩⟩
  · rw [hdist]
    exact hlo x y
  · rw [hdist]
    have hp := (exists_slidePath a (x.property.trans y.property.symm)).coordDist_le Φ
      (4*K * (2*b + 32 * Real.log ((m:ℝ)+1) * Λ)) hmove
    refine hp.trans_eq ?_
    push_cast
    dsimp [K]
    push_cast
    ring

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.histogram_embedding_step := @_root_.OAI.FiniteCircle.histogram_embedding_step
