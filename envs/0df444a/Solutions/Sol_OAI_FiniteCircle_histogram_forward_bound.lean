-- Prove2me | solution 1 for OAI.FiniteCircle.histogram_forward_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:59:31.248257+00:00
-- url     : https://prove2.me/submissions/6da10c44-5e11-4edb-8dd7-4e7e05a37419

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/Separation.lean:L200-L256
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.histogram_forward_bound. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_expect_histDist_ofFn_le

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

theorem lcs_symm {α : Type*} (x y : List α) : lcs x y = lcs y x := by
  apply Nat.le_antisymm
  · obtain ⟨z, hx, hy, hz⟩ := lcs_exists x y
    rw [← hz]
    exact le_lcs hy hx
  · obtain ⟨z, hy, hx, hz⟩ := lcs_exists y x
    rw [← hz]
    exact le_lcs hx hy

theorem sublist_common_large {α : Type*} {x y z : List α} (hx : x <+ z) (hy : y <+ z) :
    ∃ u : List α, u <+ x ∧ u <+ y ∧ x.length + y.length ≤ u.length + z.length := by
  induction z generalizing x y with
  | nil =>
    have : x = [] := List.sublist_nil.mp hx
    have : y = [] := List.sublist_nil.mp hy
    subst x; subst y
    exact ⟨[], .slnil, .slnil, le_rfl⟩
  | cons a z ih =>
    cases hx with
    | cons _ hx =>
      cases hy with
      | cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux, huy, by simp only [List.length_cons]; omega⟩
      | cons_cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux, huy.cons a, by simp only [List.length_cons]; omega⟩
    | cons_cons _ hx =>
      cases hy with
      | cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨u, hux.cons a, huy, by simp only [List.length_cons]; omega⟩
      | cons_cons _ hy =>
        obtain ⟨u, hux, huy, hlen⟩ := ih hx hy
        exact ⟨a :: u, hux.cons_cons a, huy.cons_cons a, by simp only [List.length_cons]; omega⟩

theorem lcs_triangle {α : Type*} (x y z : List α) : lcs x y + lcs y z ≤ y.length + lcs x z := by
  obtain ⟨a, hax, hay, ha⟩ := lcs_exists x y
  obtain ⟨b, hby, hbz, hb⟩ := lcs_exists y z
  obtain ⟨u, hua, hub, hlen⟩ := sublist_common_large hay hby
  have hle := le_lcs (hua.trans hax) (hub.trans hbz)
  omega

theorem unequalDeficit_triangle {α : Type*} (x y z : List α) :
    unequalDeficit x z ≤ unequalDeficit x y + unequalDeficit y z := by
  have hxy := lcs_le_length_left x y
  have hyx := lcs_le_length_right x y
  have hyz := lcs_le_length_left y z
  have hzy := lcs_le_length_right y z
  have hxz := lcs_le_length_left x z
  have hzx := lcs_le_length_right x z
  have ht := lcs_triangle x y z
  simp only [unequalDeficit]
  omega

theorem deficit_eq_unequalDeficit {α : Type*} {x y : List α} (h : x.length = y.length) :
    deficit x y = unequalDeficit x y := by simp [deficit, unequalDeficit, h]

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

theorem sublist_take_with_loss {α : Type*} {x y : List α} (h : x <+ y) (k : ℕ) :
    x.take (k - (y.length - x.length)) <+ y.take k := by
  induction h generalizing k with
  | slnil => simp
  | @cons x y a h ih =>
    have hl := h.length_le
    cases k with
    | zero => simp
    | succ k =>
      simpa only [List.length_cons, List.take_succ_cons,
        show k + 1 - (y.length + 1 - x.length) = k - (y.length - x.length) by omega]
        using (ih k).cons a
  | @cons_cons x y a h ih =>
    have hl := h.length_le
    cases k with
    | zero => simp
    | succ k =>
      by_cases hk : k + 1 ≤ y.length - x.length
      · have he : k + 1 - ((a :: y).length - (a :: x).length) = 0 := by
          simp only [List.length_cons]; omega
        rw [he]
        simp
      · have he : k + 1 - ((a :: y).length - (a :: x).length) =
            (k - (y.length - x.length)) + 1 := by simp only [List.length_cons]; omega
        simpa only [he, List.take_succ_cons] using (ih k).cons_cons a

theorem unequalDeficit_take_sublist_le {α : Type*} {x y : List α} (h : x <+ y) (k : ℕ) :
    unequalDeficit (x.take k) (y.take k) ≤ y.length - x.length := by
  have hs : x.take (k - (y.length - x.length)) <+ x.take k :=
    List.take_sublist_take_left (Nat.sub_le _ _)
  have hc := le_lcs hs (sublist_take_with_loss h k)
  have hl := h.length_le
  simp only [unequalDeficit, List.length_take] at *
  omega

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Matching ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

theorem unequalDeficit_segment_sublist_le {α : Type*} {x y : List α} (h : x <+ y)
    (start size : ℕ) :
    unequalDeficit (segment x start size) (segment y start size) ≤ y.length - x.length := by
  have hl := h.length_le
  exact (unequalDeficit_take_sublist_le (h.drop start) size).trans (by
    simp only [List.length_drop]
    omega)

theorem unequalDeficit_symm {α : Type*} (x y : List α) :
    unequalDeficit x y = unequalDeficit y x := by
  simp [unequalDeficit, lcs_symm x y, max_comm]

namespace Slide
variable {α : Type*} {x y : List α}

theorem length_eq (h : Slide x y) : x.length = y.length := by
  cases h <;> simp <;> omega

theorem common_delete (h : Slide x y) :
    ∃ z : List α, z <+ x ∧ z <+ y ∧ z.length + 1 = x.length ∧ z.length + 1 = y.length := by
  cases h with
  | forward u v t a b =>
    exact ⟨u ++ v ++ t,
      by simpa only [List.append_assoc] using ((List.Sublist.refl (v ++ t)).cons a).append_left u,
      ((List.Sublist.refl t).cons b).append_left (u ++ v), by simp; omega, by simp; omega⟩
  | backward u v t a b =>
    exact ⟨u ++ v ++ t,
      ((List.Sublist.refl t).cons b).append_left (u ++ v),
      by simpa only [List.append_assoc] using ((List.Sublist.refl (v ++ t)).cons a).append_left u,
      by simp; omega, by simp; omega⟩

theorem segment_deficit_le_two (h : Slide x y) (start size : ℕ) :
    unequalDeficit (segment x start size) (segment y start size) ≤ 2 := by
  obtain ⟨z, hx, hy, hzx, hzy⟩ := h.common_delete
  have hleft := unequalDeficit_segment_sublist_le hx start size
  have hright := unequalDeficit_segment_sublist_le hy start size
  rw [unequalDeficit_symm] at hleft
  exact (unequalDeficit_triangle _ (segment z start size) _).trans (by omega)
end Slide

namespace SlidePath
variable {α : Type*} {x y z : List α} {n m : ℕ}

end SlidePath

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

-- ---- from OAI.Combinatorics.FiniteCircle.Windows ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

theorem segment_append_left {α : Type*} (u v : List α) {start size : ℕ}
    (h : start + size ≤ u.length) : segment (u ++ v) start size = segment u start size := by
  unfold segment
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem segment_append_right {α : Type*} (u v : List α) {start size : ℕ}
    (h : u.length ≤ start) : segment (u ++ v) start size = segment v (start - u.length) size := by
  unfold segment
  rw [List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

theorem slide_segment_before {α : Type*} (u v t : List α) (a b : α) {start size : ℕ}
    (h : start + size ≤ u.length) :
    segment (u ++ a :: (v ++ t)) start size = segment (u ++ v ++ b :: t) start size := by
  rw [segment_append_left _ _ h, List.append_assoc, segment_append_left _ _ h]

theorem slide_segment_after {α : Type*} (u v t : List α) (a b : α) {start size : ℕ}
    (h : u.length + v.length + 1 ≤ start) :
    segment (u ++ a :: (v ++ t)) start size = segment (u ++ v ++ b :: t) start size := by
  have h₁ : (u ++ a :: v).length ≤ start := by simp; omega
  have h₂ : (u ++ v ++ [b]).length ≤ start := by simp; omega
  rw [show u ++ a :: (v ++ t) = (u ++ a :: v) ++ t by simp,
    show u ++ v ++ b :: t = (u ++ v ++ [b]) ++ t by simp,
    segment_append_right _ _ h₁, segment_append_right _ _ h₂]
  congr 2
  simp

theorem slide_segment_shift {α : Type*} (u v t : List α) (a b : α) {start size : ℕ}
    (h₁ : u.length + 1 ≤ start) (h₂ : start + size ≤ u.length + v.length + 1) :
    segment (u ++ a :: (v ++ t)) start size =
      segment (u ++ v ++ b :: t) (start - 1) size := by
  rw [show u ++ a :: (v ++ t) = (u ++ [a]) ++ (v ++ t) by simp,
    segment_append_right (u ++ [a]) _ (by simp; omega),
    show u ++ v ++ b :: t = u ++ (v ++ b :: t) by simp,
    segment_append_right u _ (by omega),
    segment_append_left v t (by simp; omega),
    segment_append_left v (b :: t) (by omega)]
  congr 1
  simp only [List.length_append, List.length_singleton]
  omega

theorem windows_before {α : Type*} (u v t : List α) (a b : α)
    {start m s : ℕ} (_hs : 1 ≤ s) (hsm : s ≤ m) (hbef : start + m ≤ u.length) :
    windows (u ++ a :: (v ++ t)) start m s = windows (u ++ v ++ b :: t) start m s := by
  unfold windows
  congr 1
  funext r
  exact slide_segment_before _ _ _ _ _ (by have := r.isLt; omega)

theorem windows_after {α : Type*} (u v t : List α) (a b : α)
    {start m s : ℕ} (haft : u.length + v.length + 1 ≤ start) :
    windows (u ++ a :: (v ++ t)) start m s = windows (u ++ v ++ b :: t) start m s := by
  unfold windows
  congr 1
  funext r
  exact slide_segment_after _ _ _ _ _ (by omega)

theorem windows_shift {α : Type*} (u v t : List α) (a b : α)
    {start m s : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (h₁ : u.length + 1 ≤ start) (h₂ : start + m ≤ u.length + v.length) :
    ∃ zs : List (List α), zs.length = s - 1 ∧
      zs <+ windows (u ++ a :: (v ++ t)) start m s ∧
      zs <+ windows (u ++ v ++ b :: t) start m s := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  let zs := List.ofFn (fun i : Fin r => segment (u ++ a :: (v ++ t)) (start + i.val + 1) (m - (r+1) + 1))
  refine ⟨zs, by simp [zs], ?_, ?_⟩
  · unfold windows
    rw [List.ofFn_succ]
    have he : zs = List.ofFn (fun i : Fin r => segment (u ++ a :: (v ++ t))
        (start + (i.succ : Fin (r+1))) (m - (r+1) + 1)) := by simp [zs, Nat.add_assoc]
    rw [he]
    exact List.Sublist.cons _ (List.Sublist.refl _)
  · unfold windows
    rw [List.ofFn_succ']
    have he : zs = List.ofFn (fun i : Fin r => segment (u ++ v ++ b :: t)
        (start + (i.castSucc : Fin (r+1))) (m - (r+1) + 1)) := by
      unfold zs
      congr 1
      funext i
      have hh := slide_segment_shift u v t a b (start := start + i.val + 1)
        (size := m - (r+1) + 1) (by omega) (by have := i.isLt; omega)
      simpa using hh
    rw [he]
    rw [List.concat_eq_append]
    exact List.sublist_append_left _ _

theorem block_location (p q m j : ℕ) (hm : 0 < m) (_hpq : p ≤ q)
    (hp : j ≠ p / m) (hq : j ≠ q / m) :
    (j * m + m ≤ p) ∨ (p + 1 ≤ j * m ∧ j * m + m ≤ q) ∨ (q + 1 ≤ j * m) := by
  by_cases hjp : j < p / m
  · left
    have h := (Nat.le_div_iff_mul_le hm).mp (by omega : j+1 ≤ p/m)
    nlinarith
  · have hstart : p + 1 ≤ j*m := by
      have h := (Nat.div_lt_iff_lt_mul hm).mp (by omega : p/m < j)
      omega
    by_cases hjq : j < q / m
    · right; left
      refine ⟨hstart, ?_⟩
      have h := (Nat.le_div_iff_mul_le hm).mp (by omega : j+1 ≤ q/m)
      nlinarith
    · right; right
      have h := (Nat.div_lt_iff_lt_mul hm).mp (by omega : q/m < j)
      omega

theorem windows_nonexceptional {α : Type*} (u v t : List α) (a b : α)
    {m s j : ℕ} (hs : 1 ≤ s) (hsm : s ≤ m)
    (hp : j ≠ u.length / m) (hq : j ≠ (u.length + v.length) / m) :
    ∃ zs : List (List α), s - 1 ≤ zs.length ∧
      zs <+ windows (u ++ a :: (v ++ t)) (j*m) m s ∧
      zs <+ windows (u ++ v ++ b :: t) (j*m) m s := by
  rcases block_location u.length (u.length+v.length) m j (by omega) (by omega) hp hq with h | h | h
  · have he := windows_before u v t a b hs hsm h
    exact ⟨_, by simp, .refl _, he ▸ List.Sublist.refl _⟩
  · obtain ⟨zs, hz, hx, hy⟩ := windows_shift u v t a b hs hsm h.1 h.2
    exact ⟨zs, hz.ge, hx, hy⟩
  · have he := windows_after u v t a b (m := m) (s := s) h
    exact ⟨_, by simp, .refl _, he ▸ List.Sublist.refl _⟩

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

theorem expect_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ ω, f ω ≤ g ω) :
    μ.expect f ≤ μ.expect g :=
  Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (h ω) (μ.nonneg ω))

theorem event_compl (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.event (fun ω => ¬P ω) = 1 - μ.event P := by
  classical
  rw [← μ.total]
  unfold event
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

end FiniteLaw

theorem partition_separation_le {X Ω Y : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (label : Ω → X → Y) (ρ : X → X → ℝ) (α : ℝ)
    (he : ∀ x y, μ.event (fun ω => label ω x = label ω y) = Real.exp (-α * ρ x y))
    (x y : X) : μ.event (fun ω => label ω x ≠ label ω y) ≤ α * ρ x y := by
  rw [μ.event_compl, he]
  have h := Real.add_one_le_exp (-α * ρ x y)
  linarith

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

theorem histDist_symm {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys : List X) :
    histDist label xs ys = histDist label ys xs := by
  unfold histDist
  simp only [abs_sub_comm]

theorem histDist_triangle {X Y : Type*} [Fintype Y] (label : X → Y) (xs ys zs : List X) :
    histDist label xs zs ≤ histDist label xs ys + histDist label ys zs := by
  unfold histDist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => abs_sub_le _ _ _)

theorem histogram_mono {X Y : Type*} (label : X → Y) {xs ys : List X} (h : xs <+ ys) (y : Y) :
    histogram label xs y ≤ histogram label ys y := by
  classical
  induction h with
  | slnil => exact le_rfl
  | cons a h ih =>
    rw [histogram_cons]
    split <;> linarith
  | cons_cons a h ih =>
    rw [histogram_cons, histogram_cons]
    by_cases ha : label a = y <;> simp only [ha, ite_true, ite_false] <;> linarith

theorem histDist_sublist {X Y : Type*} [Fintype Y] (label : X → Y)
    {xs ys : List X} (h : xs <+ ys) : histDist label xs ys = ys.length - xs.length := by
  unfold histDist
  simp only [abs_of_nonpos (sub_nonpos.mpr (histogram_mono label h _))]
  simp only [neg_sub, Finset.sum_sub_distrib, histogram_mass]

theorem histDist_common_sublist_le {X Y : Type*} [Fintype Y] (label : X → Y)
    {xs ys zs : List X} (hx : zs <+ xs) (hy : zs <+ ys) :
    histDist label xs ys ≤ xs.length + ys.length - 2 * zs.length := by
  calc
    _ ≤ histDist label xs zs + histDist label zs ys := histDist_triangle _ _ _ _
    _ = _ := by rw [histDist_symm label xs, histDist_sublist label hx, histDist_sublist label hy]; ring

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Separation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical

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

theorem partitionRate_nonneg (s : ℕ) : 0 ≤ partitionRate s := by
  unfold partitionRate
  exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) (Nat.cast_nonneg _)

theorem normalized_slide_segment {α : Type*} (a : α) {x y : List α} (h : Slide x y)
    {m len start : ℕ} (hlen : len ≤ m) :
    deficit (normalizeWord a m (segment x start len)).val
      (normalizeWord a m (segment y start len)).val ≤ 2 := by
  have hx : (segment x start len).length ≤ m := by
    simp only [segment, List.length_take, List.length_drop]
    exact (min_le_left _ _).trans hlen
  have hy : (segment x start len).length = (segment y start len).length := by
    simp only [segment, List.length_take, List.length_drop, h.length_eq]
  rw [normalizeWord_deficit a hx hy, deficit_eq_unequalDeficit hy]
  exact h.segment_deficit_le_two _ _

theorem block_histogram_pairing {α Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]
    (a : α) {m s : ℕ} (F : List.Vector α m → ι → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hF : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val)
    (μ : FiniteLaw Ω) (label : Ω → List.Vector α m → Y)
    (he : ∀ u v, μ.event (fun ω => label ω u = label ω v) =
      Real.exp (-partitionRate s * coordDist F u v))
    {x y : List α} (hxy : Slide x y) (start : ℕ) (hs : 1 ≤ s) (hsm : s ≤ m) :
    μ.expect (fun ω => histDist (label ω) (windowWords a x start m s) (windowWords a y start m s)) ≤
      16 * Real.log ((s:ℝ)+1) * Λ := by
  rw [windowWords_ofFn, windowWords_ofFn]
  calc
    _ ≤ 2 * s * (2 * partitionRate s * Λ) := by
      apply expect_histDist_ofFn_le
      intro i
      have hr := partition_separation_le μ label (coordDist F) (partitionRate s) he
        (normalizeWord a m (segment x (start+i) (m-s+1)))
        (normalizeWord a m (segment y (start+i) (m-s+1)))
      refine hr.trans ?_
      calc
        _ ≤ partitionRate s * (Λ * 2) := by
          apply mul_le_mul_of_nonneg_left _ (partitionRate_nonneg s)
          refine (hF _ _).trans ?_
          apply mul_le_mul_of_nonneg_left _ hΛ
          exact_mod_cast normalized_slide_segment a hxy (by omega : m-s+1 ≤ m)
        _ = _ := by ring
    _ = _ := by
      have hs0 : (s:ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
      unfold partitionRate
      field_simp
      ring

theorem fin_index_indicator_sum (b p : ℕ) :
    (∑ j : Fin b, if j.val = p then (1:ℝ) else 0) ≤ 1 := by
  classical
  by_cases hp : p < b
  · have he (j : Fin b) : j.val = p ↔ j = ⟨p,hp⟩ := by simp only [Fin.ext_iff]
    simp only [he]
    simp
  · have hn (j : Fin b) : j.val ≠ p := by have := j.isLt; omega
    simp [hn]

theorem histogram_forward_bound {α Ω Y ι : Type*} [Fintype Ω] [Fintype Y] [Fintype ι]
    (a : α) {m s : ℕ} (F : List.Vector α m → ι → ℝ) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hF : ∀ u v, coordDist F u v ≤ Λ * deficit u.val v.val)
    (μ : FiniteLaw Ω) (label : Ω → List.Vector α m → Y)
    (he : ∀ u v, μ.event (fun ω => label ω u = label ω v) =
      Real.exp (-partitionRate s * coordDist F u v))
    (u v t : List α) (c d : α) (b : ℕ) (hs : 1 ≤ s) (hsm : s ≤ m) :
    (∑ j : Fin b, μ.expect (fun ω => histDist (label ω)
      (windowWords a (u ++ c :: (v ++ t)) (j*m) m s)
      (windowWords a (u ++ v ++ d :: t) (j*m) m s))) ≤
      2*b + 32 * Real.log ((s:ℝ)+1) * Λ := by
  classical
  let B := 16 * Real.log ((s:ℝ)+1) * Λ
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) s; linarith))) hΛ
  let p := u.length / m
  let q := (u.length + v.length) / m
  have hb (j : Fin b) : μ.expect (fun ω => histDist (label ω)
      (windowWords a (u ++ c :: (v ++ t)) (j*m) m s)
      (windowWords a (u ++ v ++ d :: t) (j*m) m s)) ≤
      2 + B * ((if j.val = p then 1 else 0) + (if j.val = q then 1 else 0)) := by
    have hexc : μ.expect (fun ω => histDist (label ω)
        (windowWords a (u ++ c :: (v ++ t)) (j*m) m s)
        (windowWords a (u ++ v ++ d :: t) (j*m) m s)) ≤ B :=
      block_histogram_pairing a F Λ hΛ hF μ label he (.forward u v t c d) (j*m) hs hsm
    by_cases hp : j.val = p
    · refine hexc.trans ?_
      rw [ite_eq_left hp]
      split_ifs <;> linarith
    · by_cases hq : j.val = q
      · refine hexc.trans ?_
        rw [ite_eq_right hp, ite_eq_left hq]
        linarith
      · rw [ite_eq_right hp, ite_eq_right hq]
        simp only [add_zero, mul_zero]
        obtain ⟨zs, hz, hx, hy⟩ := windows_nonexceptional u v t c d hs hsm hp hq
        have hbω (ω : Ω) : histDist (label ω)
            (windowWords a (u ++ c :: (v ++ t)) (j*m) m s)
            (windowWords a (u ++ v ++ d :: t) (j*m) m s) ≤ 2 := by
          have h := histDist_common_sublist_le (label ω) (hx.map (normalizeWord a m))
            (hy.map (normalizeWord a m))
          simp only [List.length_map, length_windows] at h
          have hr : (2:ℝ) * s ≤ 2 * zs.length + 2 := by
            exact_mod_cast (by omega : 2*s ≤ 2*zs.length+2)
          exact h.trans (by linarith)
        simpa using μ.expect_mono hbω
  calc
    _ ≤ ∑ j : Fin b, (2 + B * ((if j.val = p then 1 else 0) + (if j.val = q then 1 else 0))) :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = 2*b + B * ((∑ j : Fin b, if j.val=p then (1:ℝ) else 0) +
        (∑ j : Fin b, if j.val=q then (1:ℝ) else 0)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ 2*b + B * (1+1) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add (fin_index_indicator_sum b p) (fin_index_indicator_sum b q)) hB)
    _ = _ := by dsimp [B]; ring

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module
open Classical


theorem solution : type_of% @_root_.OAI.FiniteCircle.histogram_forward_bound := @_root_.OAI.FiniteCircle.histogram_forward_bound
