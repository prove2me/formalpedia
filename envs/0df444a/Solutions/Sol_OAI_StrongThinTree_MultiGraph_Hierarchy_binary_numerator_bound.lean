-- Prove2me | solution 1 for OAI.StrongThinTree.MultiGraph.Hierarchy.binary_numerator_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T17:07:50.520981+00:00
-- url     : https://prove2.me/submissions/a39083d0-4f7c-4bbf-a775-37a52a3b988a

import Mathlib
import Definitions.Def_StrongThinTree
import Definitions.Def_OAIQWSTT000

section
-- module Solutions.OAIQW_StrongThinTree.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434
end

section
-- module Solutions.OAIQW_StrongThinTree.Coarea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uE uV2 uE2 uV3 uE3 uI uI2 uI3

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

lemma integrable_interval_indicator (a b c : ℝ) :
    Integrable ((Set.Ioc a b).indicator (fun _ : ℝ => c)) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp [Real.volume_Ioc]))

lemma integral_interval_indicator (a b c : ℝ) (hab : a ≤ b) :
    (∫ t : ℝ, (Set.Ioc a b).indicator (fun _ => c) t) = (b-a)*c := by
  rw [integral_indicator_const c measurableSet_Ioc, Real.volume_real_Ioc,
    max_eq_left (sub_nonneg.mpr hab), smul_eq_mul]

lemma threshold_interval {x y t : ℝ} :
    ((x < t ∧ ¬ y < t) ∨ (y < t ∧ ¬ x < t)) ↔ t ∈ Set.Ioc (min x y) (max x y) := by
  simp only [Set.mem_Ioc, min_lt_iff, le_max_iff, not_lt]
  constructor
  · rintro (h | h)
    · exact ⟨Or.inl h.1, Or.inr h.2⟩
    · exact ⟨Or.inr h.1, Or.inl h.2⟩
  · rintro ⟨h | h, h' | h'⟩ <;> first | (exfalso; linarith) | exact Or.inl ⟨h, h'⟩ | exact Or.inr ⟨h, h'⟩

lemma finite_coarea {V : Type uV} {E : Type uE} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) :
    (∫ t : ℝ, (((univ.filter (fun e =>
      (f (u e)<t ∧ ¬f (v e)<t) ∨ (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) =
      ∑e, |f (u e)-f (v e)| := by
  have heq (t : ℝ) :
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ)) =
      ∑e, (Set.Ioc (min (f (u e)) (f (v e)))
        (max (f (u e)) (f (v e)))).indicator (fun _ : ℝ => (1:ℝ)) t := by
    simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    apply sum_congr rfl
    intro e he
    rw [Set.indicator_apply]
    simp only [threshold_interval]
    split_ifs <;> norm_num
  simp_rw [heq]
  rw [integral_finsetSum _ (fun e _ => integrable_interval_indicator _ _ _)]
  apply sum_congr rfl
  intro e he
  rw [integral_interval_indicator _ _ _ min_le_max, mul_one]
  simpa only [abs_sub_comm] using (max_sub_min_eq_abs (f (u e)) (f (v e)))

lemma integrable_cut_card {V : Type uV2} {E : Type uE2} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) :
    Integrable (fun t : ℝ =>
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) := by
  have hi := integrable_finsetSum univ
    (fun e _ => integrable_interval_indicator (min (f (u e)) (f (v e)))
      (max (f (u e)) (f (v e))) 1)
  apply hi.congr
  filter_upwards with t
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro e he
  rw [Set.indicator_apply]
  simp only [threshold_interval]
  split_ifs <;> norm_num

lemma cut_range_bound {V : Type uV3} {E : Type uE3} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) {a b k : ℝ} (hab : a ≤ b)
    (hcut : ∀t ∈ Set.Ioc a b, k ≤
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) :
    k*(b-a) ≤ ∑e, |f (u e)-f (v e)| := by
  have hh := integral_mono (integrable_interval_indicator a b k)
    (integrable_cut_card u v f) (show (Set.Ioc a b).indicator (fun _ : ℝ => k) ≤
      (fun t : ℝ => (((univ.filter (fun e =>
        (f (u e)<t ∧ ¬f (v e)<t) ∨ (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) by
        intro t
        by_cases ht : t ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem ht]
          exact hcut t ht
        · rw [Set.indicator_of_notMem ht]
          positivity)
  rw [integral_interval_indicator a b k hab, finite_coarea] at hh
  simpa only [mul_comm] using hh

lemma clamp_eq_left {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) : clamp a b x = a := by
  simp [clamp, max_eq_left hx, min_eq_right hab]

lemma clamp_eq_right {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) : clamp a b x = b := by
  simp [clamp, max_eq_right (hab.trans hx), min_eq_left hx]

lemma clamp_bounds {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    a ≤ clamp a b x ∧ clamp a b x ≤ b := by
  exact ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩

lemma clamp_lt_iff {a b x t : ℝ} (ht : t ∈ Set.Ioc a b) :
    clamp a b x < t ↔ x < t := by
  simp only [clamp, min_lt_iff, max_lt_iff]
  constructor
  · rintro (h | h)
    · linarith [ht.2]
    · exact h.2
  · intro h
    exact Or.inr ⟨ht.1, h⟩

end
end StrongThinTree.Geometry

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m : ℕ} (G : MultiGraph n m)

lemma clamped_variation_lower {k : ℕ} (hk : G.EdgeConnected k)
    (f : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hu : ∃u, f u ≤ a) (hv : ∃v, b ≤ f v) :
    (k : ℝ)*(b-a) ≤ ∑e : Fin m,
      |clamp a b (f (G.left e))-clamp a b (f (G.right e))| := by
  classical
  apply cut_range_bound G.left G.right (fun v => clamp a b (f v)) hab
  intro t ht
  let S := univ.filter (fun v => f v < t)
  have hne : S.Nonempty := by
    obtain ⟨u, hu⟩ := hu
    exact ⟨u, mem_filter.mpr ⟨mem_univ _, lt_of_le_of_lt hu ht.1⟩⟩
  have hproper : S ≠ univ := by
    obtain ⟨v, hv⟩ := hv
    intro heq
    have hh : v ∈ S := heq.symm ▸ mem_univ v
    have := (mem_filter.mp hh).2
    linarith [ht.2]
  have hc := hk S hne hproper
  have hset : (univ.filter (fun e =>
      (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
      (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))) = G.cut univ S := by
    ext e
    simp only [S, cut, mem_filter, mem_univ, true_and, clamp_lt_iff ht]
  rw [hset]
  exact_mod_cast hc

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

lemma clamp_mono {a b x y : ℝ} (hxy : x ≤ y) : clamp a b x ≤ clamp a b y :=
  min_le_min_left _ (max_le_max_left _ hxy)

lemma clipped_affine_interval_increasing {a b x y : ℝ} (hab : a ≤ b) (hxy : x < y) :
    ∃ l r : ℝ, 0 ≤ l ∧ l ≤ r ∧ r ≤ 1 ∧
      |clamp a b x-clamp a b y| = |y-x| *(r-l) ∧
      ∀t ∈ Set.Ioo l r, a < x+t*(y-x) ∧ x+t*(y-x) < b := by
  by_cases heq : clamp a b x = clamp a b y
  · exact ⟨0,0,by norm_num,by norm_num,by norm_num,by simp [heq],by simp⟩
  have hAB := lt_of_le_of_ne (clamp_mono hxy.le) heq
  have hAx := clamp_bounds hab x
  have hBy := clamp_bounds hab y
  have hx : x < b := by
    by_contra h
    have hh := clamp_eq_right hab (not_lt.mp h)
    linarith
  have hy : a < y := by
    by_contra h
    have hh := clamp_eq_left hab (not_lt.mp h)
    linarith
  have hxA : x ≤ clamp a b x := by
    rw [clamp, min_eq_right (max_le hab hx.le)]
    exact le_max_right _ _
  have hBy' : clamp a b y ≤ y := by
    rw [clamp, max_eq_right hy.le]
    exact min_le_right _ _
  let s := y-x
  have hs : 0 < s := sub_pos.mpr hxy
  let l := (clamp a b x-x)/s
  let r := (clamp a b y-x)/s
  have hl : 0 ≤ l := div_nonneg (sub_nonneg.mpr hxA) hs.le
  have hr : r ≤ 1 := (div_le_one hs).mpr (by dsimp [s]; linarith)
  have hlr : l ≤ r := (div_le_div_iff_of_pos_right hs).mpr (by linarith)
  have hlmul : l*s = clamp a b x-x := div_mul_cancel₀ _ hs.ne'
  have hrmul : r*s = clamp a b y-x := div_mul_cancel₀ _ hs.ne'
  refine ⟨l,r,hl,hlr,hr,?_,?_⟩
  · rw [abs_of_nonpos (by linarith : clamp a b x-clamp a b y ≤ 0),
      abs_of_pos (sub_pos.mpr hxy)]
    dsimp [s] at hlmul hrmul
    linarith
  · intro t ht
    have hlt := mul_lt_mul_of_pos_right ht.1 hs
    have htr := mul_lt_mul_of_pos_right ht.2 hs
    dsimp [s] at hlt htr hlmul hrmul
    constructor <;> linarith

lemma clipped_affine_interval {a b x y : ℝ} (hab : a ≤ b) :
    ∃ l r : ℝ, 0 ≤ l ∧ l ≤ r ∧ r ≤ 1 ∧
      |clamp a b x-clamp a b y| = |y-x| *(r-l) ∧
      ∀t ∈ Set.Ioo l r, a < x+t*(y-x) ∧ x+t*(y-x) < b := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact clipped_affine_interval_increasing hab hxy
  · subst y
    exact ⟨0,0,by norm_num,by norm_num,by norm_num,by simp,by simp⟩
  · obtain ⟨l,r,hl,hlr,hr,heq,h⟩ := clipped_affine_interval_increasing hab hxy
    refine ⟨1-r,1-l,by linarith,by linarith,by linarith,?_,?_⟩
    · rw [abs_sub_comm, heq, abs_sub_comm x y]
      congr 1
      ring
    · intro t ht
      have hh := h (1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
      constructor <;> linarith [hh.1,hh.2]

lemma clamped_affine_disjoint_sum {I : Type uI} [Fintype I]
    (a b x y : I → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hab : ∀i, a i ≤ b i) (hslope : ∀i, |y i-x i| ≤ L)
    (hdis : ∀ i j, i ≠ j → ∀t ∈ Set.Ioo (0:ℝ) 1,
      ¬(a i < x i+t*(y i-x i) ∧ x i+t*(y i-x i)<b i ∧
        a j < x j+t*(y j-x j) ∧ x j+t*(y j-x j)<b j)) :
    ∑i, |clamp (a i) (b i) (x i)-clamp (a i) (b i) (y i)| ≤ L := by
  classical
  choose l r hl hlr hr heq hactive using fun i =>
    clipped_affine_interval (x:=x i) (y:=y i) (hab i)
  have hsub : (⋃i, Set.Ioo (l i) (r i)) ⊆ Set.Ioo (0:ℝ) 1 := by
    rintro t ⟨_,⟨i,rfl⟩,ht⟩
    exact ⟨lt_of_le_of_lt (hl i) ht.1,lt_of_lt_of_le ht.2 (hr i)⟩
  have hd : Pairwise (fun i j => Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t hti htj
    exact hdis i j hij t ⟨lt_of_le_of_lt (hl i) hti.1,
      lt_of_lt_of_le hti.2 (hr i)⟩ ⟨(hactive i t hti).1,(hactive i t hti).2,
        (hactive j t htj).1,(hactive j t htj).2⟩
  have hv := measureReal_mono (μ:=volume) hsub (by simp [Real.volume_Ioo])
  rw [measureReal_iUnion_fintype hd (fun _ => measurableSet_Ioo)
      (fun _ => by simp [Real.volume_Ioo]), Real.volume_real_Ioo] at hv
  simp only [Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr (hlr _))] at hv
  have hsum : ∑i, (r i-l i) ≤ 1 := by simpa using hv
  calc
    _ = ∑i, |y i-x i| *(r i-l i) := sum_congr rfl (fun i _ => heq i)
    _ ≤ ∑i, L*(r i-l i) := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hslope i) (sub_nonneg.mpr (hlr i)))
    _ = L*∑i, (r i-l i) := (mul_sum _ _ _).symm
    _ ≤ L*1 := mul_le_mul_of_nonneg_left hsum hL
    _ = L := mul_one L

end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry
noncomputable section
open Finset

lemma binary_cube {h : ℕ} {x : Fin h → ℝ} (hx : binary x) : cube x := by
  intro j
  rcases hx j with h | h <;> simp [h]

lemma l1dist_nonneg {h : ℕ} (x y : Fin h → ℝ) : 0 ≤ l1dist x y :=
  sum_nonneg (fun _ _ => abs_nonneg _)

lemma l1dist_reverse {h : ℕ} (x y z : Fin h → ℝ) :
    |l1dist x z-l1dist y z| ≤ l1dist x y := by
  rw [l1dist, l1dist, ← sum_sub_distrib]
  calc
    _ ≤ ∑j, abs (abs (x j-z j) - abs (y j-z j)) := abs_sum_le_sum_abs _ _
    _ ≤ ∑j, |x j-y j| := by
      apply sum_le_sum
      intro j _
      simpa only [sub_sub_sub_cancel_right] using abs_abs_sub_abs_le_abs_sub (x j-z j) (y j-z j)
    _ = _ := rfl

lemma cube_segment {h : ℕ} {x y : Fin h → ℝ} (hx : cube x) (hy : cube y)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : cube (fun j => x j+t*(y j-x j)) := by
  intro j
  have h1 : 0 ≤ (1-t)*x j+t*y j := add_nonneg
    (mul_nonneg (by linarith [ht.2]) (hx j).1) (mul_nonneg ht.1 (hy j).1)
  have h2 : (1-t)*x j+t*y j ≤ (1-t)*1+t*1 := add_le_add
    (mul_le_mul_of_nonneg_left (hx j).2 (by linarith [ht.2]))
    (mul_le_mul_of_nonneg_left (hy j).2 ht.1)
  constructor <;> linarith

lemma binary_radial_affine {h : ℕ} {x y z : Fin h → ℝ}
    (hx : cube x) (hy : cube y) (hz : binary z)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    l1dist (fun j => x j+t*(y j-x j)) z =
      l1dist x z+t*(l1dist y z-l1dist x z) := by
  have hc := cube_segment hx hy ht
  unfold l1dist
  rw [← sum_sub_distrib, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  rcases hz j with hzj | hzj
  · simp only [hzj, sub_zero, abs_of_nonneg (hx j).1, abs_of_nonneg (hy j).1,
      abs_of_nonneg (hc j).1]
  · rw [hzj, abs_of_nonpos (sub_nonpos.mpr (hc j).2),
      abs_of_nonpos (sub_nonpos.mpr (hx j).2), abs_of_nonpos (sub_nonpos.mpr (hy j).2)]
    ring

lemma binary_shell_edge_bound {h : ℕ} {I : Type uI2} [Fintype I]
    {x y : Fin h → ℝ} (hx : cube x) (hy : cube y)
    (z : I → Fin h → ℝ) (hz : ∀i, binary (z i)) (a b : I → ℝ)
    (hab : ∀i, a i ≤ b i)
    (hdis : ∀i j, i ≠ j → ∀w, cube w →
      ¬(a i < l1dist w (z i) ∧ l1dist w (z i)<b i ∧
        a j < l1dist w (z j) ∧ l1dist w (z j)<b j)) :
    ∑i, |clamp (a i) (b i) (l1dist x (z i))-
      clamp (a i) (b i) (l1dist y (z i))| ≤ l1dist x y := by
  apply clamped_affine_disjoint_sum a b _ _ (l1dist_nonneg x y) hab
  · intro i
    simpa only [l1dist_comm y x] using l1dist_reverse y x (z i)
  · intro i j hij t ht hbad
    have htc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    apply hdis i j hij (fun j => x j+t*(y j-x j)) (cube_segment hx hy htc)
    simpa only [binary_radial_affine hx hy (hz i) htc,
      binary_radial_affine hx hy (hz j) htc] using hbad

end
end StrongThinTree.Geometry

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry

lemma binary_shell_length_bound {n m h : ℕ} (G : MultiGraph n m) {k : ℕ}
    (hk : G.EdgeConnected k) (X : Fin n → Fin h → ℝ) (hX : ∀v, cube (X v))
    {I : Type uI3} [Fintype I] (z : I → Fin h → ℝ) (hz : ∀i, binary (z i))
    (a b : I → ℝ) (hab : ∀i, a i ≤ b i)
    (hu : ∀i, ∃u, l1dist (X u) (z i) ≤ a i)
    (hv : ∀i, ∃v, b i ≤ l1dist (X v) (z i))
    (hdis : ∀i j, i ≠ j → ∀w, cube w →
      ¬(a i < l1dist w (z i) ∧ l1dist w (z i)<b i ∧
        a j < l1dist w (z j) ∧ l1dist w (z j)<b j)) :
    (k:ℝ)*(∑i, (b i-a i)) ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  classical
  calc
    _ = ∑i, (k:ℝ)*(b i-a i) := mul_sum _ _ _
    _ ≤ ∑i, ∑e : Fin m, |clamp (a i) (b i) (l1dist (X (G.left e)) (z i))-
      clamp (a i) (b i) (l1dist (X (G.right e)) (z i))| := by
      apply sum_le_sum
      intro i _
      exact G.clamped_variation_lower hk _ (hab i) (hu i) (hv i)
    _ = ∑e : Fin m, ∑i, |clamp (a i) (b i) (l1dist (X (G.left e)) (z i))-
      clamp (a i) (b i) (l1dist (X (G.right e)) (z i))| := sum_comm
    _ ≤ _ := sum_le_sum (fun e _ => binary_shell_edge_bound (hX _) (hX _) z hz a b hab hdis)

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Shells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uV2 uV3 uV4 uV5 uV6

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset

lemma l1dist_self {h : ℕ} (x : Fin h → ℝ) : l1dist x x = 0 := by simp [l1dist]

lemma l1dist_triangle {h : ℕ} (x y z : Fin h → ℝ) :
    l1dist x z ≤ l1dist x y+l1dist y z := by
  rw [l1dist, l1dist, l1dist, ← sum_add_distrib]
  exact sum_le_sum (fun j _ => abs_sub_le (x j) (y j) (z j))

namespace RadialShell
variable {V : Type uV2} {h : ℕ}

lemma valid_width_pos {X : V → Fin h → ℝ} {H : RadialShell V} (hH : H.Valid X) :
    0 < H.width := sub_pos.mpr hH.2.1

lemma support_ball (X : V → Fin h → ℝ) (v : V) (r : ℝ) :
    (ball v r).support X = {w | cube w ∧ l1dist w (X v)<r} := by
  ext w
  simp [support,ball]

lemma support_hollow (X : V → Fin h → ℝ) (v : V) (a b : ℝ) :
    (hollow v a b).support X = {w | cube w ∧ a<l1dist w (X v) ∧ l1dist w (X v)<b} := by
  ext w
  simp only [support,hollow,Set.mem_ofPred_eq,Bool.false_eq_true,false_or]
  tauto

lemma valid_support_nonempty {X : V → Fin h → ℝ} (hX : ∀v, binary (X v))
    {H : RadialShell V} (hH : H.Valid X) : (H.support X).Nonempty := by
  obtain ⟨v,hv⟩ := hH.2.2.2.2
  let R := l1dist (X v) (X H.center)
  let q := (H.inner+H.outer)/2
  have hq : H.inner<q ∧ q<H.outer := by dsimp [q]; constructor <;> linarith [hH.2.1]
  have hR : 0 < R := lt_of_lt_of_le (lt_of_le_of_lt hH.1 hH.2.1) hv
  let t := q/R
  have ht : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg (le_trans hH.1 hq.1.le) hR.le,
      (div_le_one hR).mpr (le_trans hq.2.le hv)⟩
  let w := fun j => X H.center j+t*(X v j-X H.center j)
  have hw : l1dist w (X H.center) = q := by
    rw [binary_radial_affine (binary_cube (hX _)) (binary_cube (hX _)) (hX _) ht,
      l1dist_self, sub_zero, zero_add]
    exact div_mul_cancel₀ _ hR.ne'
  exact ⟨w,cube_segment (binary_cube (hX _)) (binary_cube (hX _)) ht,
    hw ▸ hq.2,Or.inr (hw ▸ hq.1)⟩

lemma restriction_valid {X : V → Fin h → ℝ} {H : RadialShell V}
    (hH : H.Valid X) {a b : ℝ} (ha : H.inner ≤ a) (hb : b ≤ H.outer) (hab : a < b) :
    (hollow H.center a b).Valid X := by
  refine ⟨hH.1.trans ha,hab,by simp [hollow],?_,?_⟩
  · obtain ⟨u,hu⟩ := hH.2.2.2.1
    exact ⟨u,hu.trans ha⟩
  · obtain ⟨v,hv⟩ := hH.2.2.2.2
    exact ⟨v,hb.trans hv⟩

lemma restriction_subset (X : V → Fin h → ℝ) (H : RadialShell V)
    {a b : ℝ} (ha : H.inner ≤ a) (hb : b ≤ H.outer) :
    (hollow H.center a b).support X ⊆ H.support X := by
  intro w hw
  rw [support_hollow] at hw
  exact ⟨hw.1,lt_of_lt_of_le hw.2.2 hb,Or.inr (lt_of_le_of_lt ha hw.2.1)⟩

lemma ball_subset_of_radial_margin (X : V → Fin h → ℝ) (H : RadialShell V)
    (z : V) {δ : ℝ} (hlo : H.inner+δ ≤ l1dist (X z) (X H.center))
    (hhi : l1dist (X z) (X H.center) ≤ H.outer-δ) :
    (ball z δ).support X ⊆ H.support X := by
  intro w hw
  rw [support_ball] at hw
  have htri := l1dist_triangle w (X z) (X H.center)
  have htri' := l1dist_triangle (X z) w (X H.center)
  rw [l1dist_comm (X z) w] at htri'
  exact ⟨hw.1,by linarith [hw.2],Or.inr (by linarith [hw.2])⟩

lemma ball_disjoint_hollow_lower (X : V → Fin h → ℝ) (x z : V) {δ q a : ℝ}
    (hq : q+δ ≤ l1dist (X z) (X x)) :
    Disjoint ((ball z δ).support X) ((hollow x a q).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_ball] at hw
  rw [support_hollow] at hz
  have ht := l1dist_triangle (X z) w (X x)
  rw [l1dist_comm (X z) w] at ht
  linarith [hw.2,hz.2.2]

lemma ball_disjoint_hollow_upper (X : V → Fin h → ℝ) (x z : V) {δ q b : ℝ}
    (hq : l1dist (X z) (X x)+δ ≤ q) :
    Disjoint ((ball z δ).support X) ((hollow x q b).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_ball] at hw
  rw [support_hollow] at hz
  have ht := l1dist_triangle w (X z) (X x)
  linarith [hw.2,hz.2.1]

lemma concentric_disjoint (X : V → Fin h → ℝ) (x : V) {a b c d : ℝ} (hbc : b ≤ c) :
    Disjoint ((hollow x a b).support X) ((hollow x c d).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_hollow] at hw hz
  linarith [hw.2.2,hz.2.1]

lemma disjoint_balls_distance {X : V → Fin h → ℝ} (hX : ∀v, binary (X v))
    (u v : V) {δ : ℝ} (hd : Disjoint ((ball u δ).support X) ((ball v δ).support X)) :
    2*δ ≤ l1dist (X u) (X v) := by
  by_contra hh
  have hh := not_le.mp hh
  let w := fun j => X u j+(1/2:ℝ)*(X v j-X u j)
  have hw := cube_segment (binary_cube (hX u)) (binary_cube (hX v))
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  have hu := binary_radial_affine (binary_cube (hX u)) (binary_cube (hX v)) (hX u)
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  have hv := binary_radial_affine (binary_cube (hX u)) (binary_cube (hX v)) (hX v)
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  simp only [l1dist_self,l1dist_comm (X v) (X u)] at hu hv
  have hwu : w ∈ (ball u δ).support X := by
    rw [support_ball]; exact ⟨hw,by dsimp [w]; linarith⟩
  have hwv : w ∈ (ball v δ).support X := by
    rw [support_ball]; exact ⟨hw,by dsimp [w]; linarith⟩
  exact Set.disjoint_left.mp hd hwu hwv

end RadialShell
end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry.RadialShell
noncomputable section
open Finset
variable {V : Type uV3} [DecidableEq V] {h : ℕ} {X : V → Fin h → ℝ}

omit [DecidableEq V] in
lemma arrangement_empty : Arrangement X ∅ := by simp [Arrangement]

omit [DecidableEq V] in
lemma arrangement_subset {O P : Finset (RadialShell V)} (hO : Arrangement X O) (hPO : P ⊆ O) :
    Arrangement X P := ⟨fun H hH => hO.1 H (hPO hH),hO.2.mono hPO⟩

omit [DecidableEq V] in
lemma arrangement_disjoint_finsets (hX : ∀v, binary (X v))
    {O P : Finset (RadialShell V)} (hO : Arrangement X O)
    (hd : ∀H ∈ O, ∀K ∈ P, Disjoint (H.support X) (K.support X)) : Disjoint O P := by
  rw [Finset.disjoint_left]
  intro H hHO hHP
  obtain ⟨w,hw⟩ := valid_support_nonempty hX (hO.1 H hHO)
  exact Set.disjoint_left.mp (hd H hHO H hHP) hw hw

lemma arrangement_union {O P : Finset (RadialShell V)}
    (hO : Arrangement X O) (hP : Arrangement X P)
    (hd : ∀H ∈ O, ∀K ∈ P, Disjoint (H.support X) (K.support X)) : Arrangement X (O ∪ P) := by
  constructor
  · intro H hH
    rcases mem_union.mp hH with hH | hH
    · exact hO.1 H hH
    · exact hP.1 H hH
  · intro H hH K hK hne
    rcases mem_union.mp hH with hH | hH <;> rcases mem_union.mp hK with hK | hK
    · exact hO.2 hH hK hne
    · exact hd H hH K hK
    · exact (hd K hK H hH).symm
    · exact hP.2 hH hK hne

lemma image_restriction_injective (hX : ∀v, binary (X v))
    {O : Finset (RadialShell V)} (hO : Arrangement X O)
    (f : RadialShell V → RadialShell V)
    (hf : ∀H ∈ O, (f H).Valid X ∧ (f H).support X ⊆ H.support X) :
    Set.InjOn f (O : Set (RadialShell V)) := by
  intro H hH K hK heq
  by_contra hne
  obtain ⟨w,hw⟩ := valid_support_nonempty hX (hf H hH).1
  exact Set.disjoint_left.mp (hO.2 hH hK hne) ((hf H hH).2 hw)
    ((hf K hK).2 (heq ▸ hw))

lemma arrangement_image_restriction {O : Finset (RadialShell V)} (hO : Arrangement X O)
    (f : RadialShell V → RadialShell V)
    (hf : ∀H ∈ O, (f H).Valid X ∧ (f H).support X ⊆ H.support X) :
    Arrangement X (O.image f) := by
  constructor
  · intro H hH
    obtain ⟨K,hK,rfl⟩ := mem_image.mp hH
    exact (hf K hK).1
  · intro H hH K hK hne
    obtain ⟨H',hH',rfl⟩ := mem_image.mp hH
    obtain ⟨K',hK',rfl⟩ := mem_image.mp hK
    exact (hO.2 hH' hK' (by intro heq; exact hne (congrArg f heq))).mono
      (hf H' hH').2 (hf K' hK').2

omit [DecidableEq V] in
lemma capacity_nonneg (Δ : ℝ) (H : RadialShell V) : 0 ≤ capacity Δ H := le_max_right _ _
omit [DecidableEq V] in
lemma capacity_ge_formal (Δ : ℝ) (H : RadialShell V) : H.width-6*Δ ≤ capacity Δ H := le_max_left _ _

lemma potential_union {O P : Finset (RadialShell V)} (hOP : Disjoint O P) (Δ : ℝ) :
    potential Δ (O ∪ P) = potential Δ O+potential Δ P := sum_union hOP

lemma potential_erase {O : Finset (RadialShell V)} {H : RadialShell V}
    (hH : H ∈ O) (Δ : ℝ) : potential Δ (O.erase H)+capacity Δ H = potential Δ O :=
  sum_erase_add _ _ hH

lemma potential_image_restriction (hX : ∀v, binary (X v))
    {O : Finset (RadialShell V)} (hO : Arrangement X O)
    (f : RadialShell V → RadialShell V)
    (hf : ∀H ∈ O, (f H).Valid X ∧ (f H).support X ⊆ H.support X) (Δ : ℝ) :
    potential Δ (O.image f) = ∑H ∈ O, capacity Δ (f H) := by
  exact sum_image (fun H hH K hK heq => image_restriction_injective hX hO f hf hH hK heq)

omit [DecidableEq V] in
lemma capacity_ball {δ Δ : ℝ} (h : 6*Δ ≤ δ) (v : V) :
    capacity Δ (ball v δ) = δ-6*Δ := by
  simp only [capacity,width,ball,sub_zero]
  exact max_eq_left (sub_nonneg.mpr h)

omit [DecidableEq V] in
lemma ball_injective (δ : ℝ) : Function.Injective (fun v : V => ball v δ) := by
  intro u v heq
  exact congrArg RadialShell.center heq

lemma potential_balls {δ Δ : ℝ} (h : 6*Δ ≤ δ) (C : Finset V) :
    potential Δ (C.image (fun v => ball v δ)) = (C.card : ℝ)*(δ-6*Δ) := by
  rw [potential,sum_image (fun _ _ _ _ heq => ball_injective δ heq)]
  simp only [capacity_ball h,sum_const,nsmul_eq_mul]

end
end StrongThinTree.Geometry.RadialShell

namespace StrongThinTree.Geometry.RadialShell
noncomputable section
open Finset
variable {V : Type uV4} [DecidableEq V] {h : ℕ} {X : V → Fin h → ℝ}

omit [DecidableEq V] in
lemma potential_filter_width (O : Finset (RadialShell V)) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    potential Δ (O.filter (fun H => 0 < H.width)) = potential Δ O := by
  apply sum_subset (filter_subset _ _)
  intro H hH hn
  have hw : H.width ≤ 0 := le_of_not_gt (fun hh => hn (mem_filter.mpr ⟨hH,hh⟩))
  exact max_eq_right (by linarith)

lemma arrangement_balls {U : Finset V} {δ : ℝ}
    (hv : ∀u ∈ U, (ball u δ).Valid X)
    (hd : (U : Set V).Pairwise (fun u v => Disjoint ((ball u δ).support X) ((ball v δ).support X))) :
    Arrangement X (U.image (fun v => ball v δ)) := by
  constructor
  · intro H hH
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hH
    exact hv u hu
  · intro H hH K hK hne
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hH
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hK
    exact hd hu hv (by intro heq; exact hne (congrArg (fun z => ball z δ) heq))

lemma split_shells (_hX : ∀v, binary (X v))
    {H : RadialShell V} (hH : H.Valid X) {L R δ Δ Δ' n : ℝ}
    (hδ : 0 < δ) (hΔ : 2*δ ≤ Δ) (_hΔ' : 0 ≤ Δ') (hnext : 6*Δ' ≤ δ/2)
    (hL : H.inner+δ ≤ L) (hR : R ≤ H.outer-δ) (hLR : L ≤ R)
    (hspan : R-L ≤ Δ) (hn : 36*Δ ≤ n*δ) :
    ∃P : Finset (RadialShell V), Arrangement X P ∧
      (∀K ∈ P, K.support X ⊆ H.support X) ∧
      (∀z, L ≤ l1dist (X z) (X H.center) → l1dist (X z) (X H.center) ≤ R →
        ∀K ∈ P, Disjoint ((ball z δ).support X) (K.support X)) ∧
      capacity Δ H+n*δ/4 ≤ potential Δ P+n*(δ-6*Δ') := by
  let A := hollow H.center H.inner (L-δ)
  let B := hollow H.center (R+δ) H.outer
  let P := ({A,B} : Finset (RadialShell V)).filter (fun K => 0 < K.width)
  have hΔ0 : 0 ≤ Δ := by linarith
  have hA : H.inner ≤ L-δ := by linarith
  have hB : R+δ ≤ H.outer := by linarith
  have hAB : A ≠ B := by
    intro heq
    have := congrArg RadialShell.inner heq
    change H.inner = R+δ at this
    linarith
  have hpA : L-δ ≤ H.outer := by linarith
  have hpB : H.inner ≤ R+δ := by linarith
  have hdAB : Disjoint (A.support X) (B.support X) := concentric_disjoint X H.center (by linarith)
  have hv : ∀K ∈ P, K.Valid X := by
    intro K hK
    obtain ⟨hK,hw⟩ := mem_filter.mp hK
    rcases mem_insert.mp hK with rfl | hK
    · exact restriction_valid hH le_rfl hpA (by exact sub_pos.mp hw)
    · have heq := mem_singleton.mp hK
      subst K
      exact restriction_valid hH hpB le_rfl (by exact sub_pos.mp hw)
  have hsub : ∀K ∈ P, K.support X ⊆ H.support X := by
    intro K hK
    have hK := (mem_filter.mp hK).1
    rcases mem_insert.mp hK with rfl | hK
    · exact restriction_subset X H le_rfl hpA
    · have heq := mem_singleton.mp hK
      subst K
      exact restriction_subset X H hpB le_rfl
  have harr : Arrangement X P := by
    refine ⟨hv,?_⟩
    intro J hJ K hK hne
    have hJ := (mem_filter.mp hJ).1
    have hK := (mem_filter.mp hK).1
    simp only [mem_insert,mem_singleton] at hJ hK
    rcases hJ with rfl | rfl <;> rcases hK with rfl | rfl
    · exact (hne rfl).elim
    · exact hdAB
    · exact hdAB.symm
    · exact (hne rfl).elim
  refine ⟨P,harr,hsub,?_,?_⟩
  · intro z hzL hzR K hK
    have hK := (mem_filter.mp hK).1
    rcases mem_insert.mp hK with rfl | hK
    · exact ball_disjoint_hollow_lower X H.center z (by linarith)
    · have heq := mem_singleton.mp hK
      subst K
      exact ball_disjoint_hollow_upper X H.center z (by linarith)
  · have hp : potential Δ P = capacity Δ A+capacity Δ B := by
      rw [show P = ({A,B} : Finset (RadialShell V)).filter (fun K => 0 < K.width) from rfl,
        potential_filter_width _ hΔ0]
      simp [potential,hAB]
    rw [hp]
    have hn0 : 0 ≤ n := by nlinarith
    have hnew : n*δ/2 ≤ n*(δ-6*Δ') := by nlinarith
    have hcapA := capacity_ge_formal Δ A
    have hcapB := capacity_ge_formal Δ B
    have hcapA0 := capacity_nonneg Δ A
    have hcapB0 := capacity_nonneg Δ B
    change L-δ-H.inner-6*Δ ≤ capacity Δ A at hcapA
    change H.outer-(R+δ)-6*Δ ≤ capacity Δ B at hcapB
    by_cases ht : H.width-6*Δ ≤ 0
    · rw [capacity,max_eq_right ht]
      linarith
    · rw [capacity,max_eq_left (le_of_not_ge ht)]
      dsimp [width]
      linarith

lemma shrink_shells (hX : ∀v, binary (X v))
    {O : Finset (RadialShell V)} (hO : Arrangement X O)
    {δ Δ Δ' : ℝ} (hδ : 0 < δ) (hΔ : 2*δ ≤ Δ) (_hΔ' : 0 ≤ Δ') (hnext : 6*Δ' ≤ δ/2) :
    ∃P : Finset (RadialShell V), Arrangement X P ∧
      (∀K ∈ P, ∃H ∈ O, K.support X ⊆ H.support X) ∧
      (∀z, (∀H ∈ O, ¬(H.inner+δ+Δ ≤ l1dist (X z) (X H.center) ∧
        l1dist (X z) (X H.center) ≤ H.outer-δ-Δ)) →
        ∀K ∈ P, Disjoint ((ball z δ).support X) (K.support X)) ∧
      potential Δ O ≤ potential Δ' P := by
  let s := 2*δ+Δ
  let f := fun H : RadialShell V => hollow H.center (H.inner+s) (H.outer-s)
  let Q := O.filter (fun H => 2*s < H.width)
  have hs : 0 ≤ s := by dsimp [s]; linarith
  have hres : 2*s+6*Δ' ≤ 6*Δ := by dsimp [s]; linarith
  have hQ : Arrangement X Q := arrangement_subset hO (filter_subset _ _)
  have hf : ∀H ∈ Q, (f H).Valid X ∧ (f H).support X ⊆ H.support X := by
    intro H hH
    obtain ⟨hH,hw⟩ := mem_filter.mp hH
    exact ⟨restriction_valid (hO.1 H hH) (by linarith) (by linarith)
      (by dsimp [width] at hw; linarith),restriction_subset X H (by linarith) (by linarith)⟩
  refine ⟨Q.image f,arrangement_image_restriction hQ f hf,?_,?_,?_⟩
  · intro K hK
    obtain ⟨H,hH,rfl⟩ := mem_image.mp hK
    exact ⟨H,(mem_filter.mp hH).1,(hf H hH).2⟩
  · intro z hz K hK
    obtain ⟨H,hH,rfl⟩ := mem_image.mp hK
    have hz := hz H (mem_filter.mp hH).1
    by_cases hlo : H.inner+δ+Δ ≤ l1dist (X z) (X H.center)
    · have hhi : H.outer-δ-Δ < l1dist (X z) (X H.center) :=
        lt_of_not_ge (fun hh => hz ⟨hlo,hh⟩)
      exact ball_disjoint_hollow_lower X H.center z (by dsimp [s]; linarith)
    · have hlo := lt_of_not_ge hlo
      exact ball_disjoint_hollow_upper X H.center z (by dsimp [s]; linarith)
  · rw [potential_image_restriction hX hQ f hf]
    have heq : potential Δ O = potential Δ Q := by
      symm
      apply sum_subset (filter_subset _ _)
      intro H hH hn
      have hw : H.width ≤ 2*s := le_of_not_gt (fun hh => hn (mem_filter.mpr ⟨hH,hh⟩))
      exact max_eq_right (by linarith)
    rw [heq]
    apply sum_le_sum
    intro H hH
    apply max_le_max_right
    dsimp [f,width,hollow]
    linarith

end
end StrongThinTree.Geometry.RadialShell

namespace StrongThinTree.Geometry.RadialShell
noncomputable section
open Finset
variable {V : Type uV5} [DecidableEq V] {h : ℕ} {X : V → Fin h → ℝ}

omit [DecidableEq V] in
lemma radial_span {D : Finset V} (hD : D.Nonempty) {Δ δ : ℝ}
    (hdiam : ∀u ∈ D, ∀v ∈ D, l1dist (X u) (X v) ≤ Δ)
    {H : RadialShell V} {z : V} (hz : z ∈ D)
    (hint : H.inner+δ+Δ ≤ l1dist (X z) (X H.center) ∧
      l1dist (X z) (X H.center) ≤ H.outer-δ-Δ) :
    ∃L R : ℝ, H.inner+δ ≤ L ∧ R ≤ H.outer-δ ∧ L ≤ R ∧ R-L ≤ Δ ∧
      (∀u ∈ D, L ≤ l1dist (X u) (X H.center) ∧ l1dist (X u) (X H.center) ≤ R) := by
  obtain ⟨u,hu,humin⟩ := D.exists_min_image (fun v => l1dist (X v) (X H.center)) hD
  obtain ⟨v,hv,hvmax⟩ := D.exists_max_image (fun v => l1dist (X v) (X H.center)) hD
  refine ⟨l1dist (X u) (X H.center),l1dist (X v) (X H.center),?_,?_,?_,?_,?_⟩
  · have ht := l1dist_triangle (X z) (X u) (X H.center)
    have hd := hdiam z hz u hu
    linarith [hint.1]
  · have ht := l1dist_triangle (X v) (X z) (X H.center)
    have hd := hdiam v hv z hz
    linarith [hint.2]
  · exact humin v hv
  · have ht := l1dist_triangle (X v) (X u) (X H.center)
    linarith [hdiam v hv u hu]
  · exact fun w hw => ⟨humin w hw,hvmax w hw⟩

lemma compact_phase (hX : ∀v, binary (X v))
    {δ Δ Δ' : ℝ} (hδ : 0 < δ) (hΔ : 2*δ ≤ Δ) (hΔ' : 0 ≤ Δ') (hnext : 6*Δ' ≤ δ/2)
    (U : Finset V) (hUv : ∀u ∈ U, (ball u δ).Valid X)
    (hUd : (U : Set V).Pairwise (fun u v => Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (F : Finset (Finset V))
    (hFd : (F : Set (Finset V)).Pairwise Disjoint)
    (hF : ∀D ∈ F, D ⊆ U ∧ D.Nonempty ∧
      (∀u ∈ D, ∀v ∈ D, l1dist (X u) (X v) ≤ Δ) ∧ 36*Δ ≤ (D.card : ℝ)*δ)
    (O : Finset (RadialShell V)) (hO : Arrangement X O)
    (C : Finset V) (hCU : C ⊆ U) (hCF : ∀D ∈ F, Disjoint C D)
    (hOC : ∀H ∈ O, ∀z ∈ C, Disjoint (H.support X) ((ball z δ).support X)) :
    ∃Z : Finset (RadialShell V), Arrangement X Z ∧
      potential Δ O+(C.card : ℝ)*(δ-6*Δ')+δ/4*∑D ∈ F, (D.card : ℝ) ≤ potential Δ' Z := by
  induction F using Finset.strongInductionOn generalizing O C with
  | _ F ih =>
    by_cases hinter : ∃D ∈ F, ∃z ∈ D, ∃H ∈ O,
      H.inner+δ+Δ ≤ l1dist (X z) (X H.center) ∧
        l1dist (X z) (X H.center) ≤ H.outer-δ-Δ
    · obtain ⟨D,hDF,z,hz,H,hHO,hint⟩ := hinter
      obtain ⟨L,R,hL,hR,hLR,hspan,hbounds⟩ :=
        radial_span (hF D hDF).2.1 (hF D hDF).2.2.1 hz hint
      obtain ⟨P,hP,hPH,hPD,hpot⟩ := split_shells hX (hO.1 H hHO) hδ hΔ hΔ' hnext
        hL hR hLR hspan (hF D hDF).2.2.2
      have hballH : ∀u ∈ D, (ball u δ).support X ⊆ H.support X := by
        intro u hu
        exact ball_subset_of_radial_margin X H u (hL.trans (hbounds u hu).1)
          ((hbounds u hu).2.trans hR)
      have hcross : ∀K ∈ O.erase H, ∀J ∈ P, Disjoint (K.support X) (J.support X) := by
        intro K hK J hJ
        exact (hO.2 (mem_of_mem_erase hK) hHO (ne_of_mem_erase hK)).mono_right (hPH J hJ)
      have hOE := arrangement_subset hO (erase_subset H O)
      have hOP := arrangement_union hOE hP hcross
      have hCUD : C ∪ D ⊆ U := union_subset hCU (hF D hDF).1
      have hCDE : ∀E ∈ F.erase D, Disjoint (C ∪ D) E := by
        intro E hE
        exact disjoint_union_left.mpr ⟨hCF E (mem_of_mem_erase hE),
          hFd hDF (mem_of_mem_erase hE) (ne_of_mem_erase hE).symm⟩
      have hnewOC : ∀K ∈ O.erase H ∪ P, ∀u ∈ C ∪ D,
          Disjoint (K.support X) ((ball u δ).support X) := by
        intro K hK u hu
        rcases mem_union.mp hK with hK | hK <;> rcases mem_union.mp hu with hu | hu
        · exact hOC K (mem_of_mem_erase hK) u hu
        · exact (hO.2 (mem_of_mem_erase hK) hHO (ne_of_mem_erase hK)).mono_right (hballH u hu)
        · exact (hOC H hHO u hu).mono_left (hPH K hK)
        · exact (hPD u (hbounds u hu).1 (hbounds u hu).2 K hK).symm
      obtain ⟨Z,hZ,hZpot⟩ := ih (F.erase D) (erase_ssubset hDF)
        (hFd.mono (erase_subset _ _)) (fun E hE => hF E (mem_of_mem_erase hE))
        (O.erase H ∪ P) hOP (C ∪ D) hCUD hCDE hnewOC
      refine ⟨Z,hZ,?_⟩
      have hp := potential_union (arrangement_disjoint_finsets hX hOE hcross) Δ
      have he := potential_erase hHO Δ
      have hc := card_union_of_disjoint (hCF D hDF)
      have hs := sum_erase_add F (fun E : Finset V => (E.card : ℝ)) hDF
      have hc' : ((C ∪ D).card : ℝ) = (C.card : ℝ)+(D.card : ℝ) := by exact_mod_cast hc
      rw [hp,hc'] at hZpot
      nlinarith
    · obtain ⟨P,hP,hPO,hPF,hpot⟩ := shrink_shells hX hO hδ hΔ hΔ' hnext
      let W := C ∪ F.biUnion id
      have hWU : W ⊆ U := by
        intro u hu
        rcases mem_union.mp hu with hu | hu
        · exact hCU hu
        · obtain ⟨D,hD,hu⟩ := mem_biUnion.mp hu
          exact (hF D hD).1 hu
      have hB : Arrangement X (W.image (fun u => ball u δ)) :=
        arrangement_balls (fun u hu => hUv u (hWU hu)) (hUd.mono hWU)
      have hcross : ∀H ∈ P, ∀K ∈ W.image (fun u => ball u δ),
          Disjoint (H.support X) (K.support X) := by
        intro H hH K hK
        obtain ⟨u,hu,rfl⟩ := mem_image.mp hK
        rcases mem_union.mp hu with hu | hu
        · obtain ⟨J,hJ,hsub⟩ := hPO H hH
          exact (hOC J hJ u hu).mono_left hsub
        · obtain ⟨D,hD,hu⟩ := mem_biUnion.mp hu
          exact (hPF u (fun J hJ hh => hinter ⟨D,hD,u,hu,J,hJ,hh⟩) H hH).symm
      refine ⟨P ∪ W.image (fun u => ball u δ),arrangement_union hP hB hcross,?_⟩
      rw [potential_union (arrangement_disjoint_finsets hX hP hcross),
        potential_balls (show 6*Δ' ≤ δ by linarith)]
      have hCW : Disjoint C (F.biUnion id) := by
        rw [Finset.disjoint_left]
        intro u hu hv
        obtain ⟨D,hD,hv⟩ := mem_biUnion.mp hv
        exact Finset.disjoint_left.mp (hCF D hD) hu hv
      have hflat : (F.biUnion id).card = ∑D ∈ F, D.card := card_biUnion hFd
      have hwcard : (W.card : ℝ) = (C.card : ℝ)+∑D ∈ F, (D.card : ℝ) := by
        dsimp [W]
        rw [card_union_of_disjoint hCW,hflat,Nat.cast_add,Nat.cast_sum]
      rw [hwcard]
      have hsum : 0 ≤ ∑D ∈ F, (D.card : ℝ) := sum_nonneg (fun D _ => Nat.cast_nonneg _)
      have hmass : δ/4*(∑D ∈ F, (D.card : ℝ)) ≤
          (∑D ∈ F, (D.card : ℝ))*(δ-6*Δ') := by nlinarith
      linarith

end
end StrongThinTree.Geometry.RadialShell

namespace StrongThinTree.Geometry.RadialShell
noncomputable section
open Finset
variable {V : Type uV6} [DecidableEq V] {h : ℕ} {X : V → Fin h → ℝ}

lemma compact_arrangement (hX : ∀v, binary (X v))
    (q : ℕ) (δ Δ : ℕ → ℝ) (U : ℕ → Finset V) (F : ℕ → Finset (Finset V))
    (hδ : ∀i < q, 0 < δ i) (hΔ : ∀i < q, 2*δ i ≤ Δ i)
    (hΔ0 : ∀i ≤ q, 0 ≤ Δ i) (hnext : ∀i < q, 6*Δ (i+1) ≤ δ i/2)
    (hUv : ∀i < q, ∀u ∈ U i, (ball u (δ i)).Valid X)
    (hUd : ∀i < q, (U i : Set V).Pairwise
      (fun u v => Disjoint ((ball u (δ i)).support X) ((ball v (δ i)).support X)))
    (hFd : ∀i < q, (F i : Set (Finset V)).Pairwise Disjoint)
    (hF : ∀i < q, ∀D ∈ F i, D ⊆ U i ∧ D.Nonempty ∧
      (∀u ∈ D, ∀v ∈ D, l1dist (X u) (X v) ≤ Δ i) ∧ 36*Δ i ≤ (D.card : ℝ)*δ i) :
    ∃Z : Finset (RadialShell V), Arrangement X Z ∧
      (∑i ∈ range q, δ i*(∑D ∈ F i, (D.card : ℝ)))/4 ≤ potential (Δ q) Z := by
  have hex : ∀j ≤ q, ∃Z : Finset (RadialShell V), Arrangement X Z ∧
      (∑i ∈ range j, δ i*(∑D ∈ F i, (D.card : ℝ)))/4 ≤ potential (Δ j) Z := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨∅,arrangement_empty,by simp [potential]⟩
    | succ j ih =>
      intro hj
      have hjq : j < q := by omega
      obtain ⟨O,hO,hpot⟩ := ih (by omega)
      obtain ⟨Z,hZ,hZp⟩ := compact_phase hX (hδ j hjq) (hΔ j hjq)
        (hΔ0 (j+1) hj) (hnext j hjq) (U j) (hUv j hjq) (hUd j hjq)
        (F j) (hFd j hjq) (hF j hjq) O hO ∅ (empty_subset _) (by simp) (by simp)
      refine ⟨Z,hZ,?_⟩
      simp only [card_empty,Nat.cast_zero,zero_mul,add_zero] at hZp
      rw [sum_range_succ]
      linarith
  exact hex q le_rfl

lemma CompactFamily.ball_valid (hX : ∀v, binary (X v)) {δ Δ : ℝ}
    (F : CompactFamily X δ Δ) {u : V} (hu : u ∈ F.bags.biUnion id) :
    (ball u δ).Valid X := by
  obtain ⟨D,hD,huD⟩ := mem_biUnion.mp hu
  have hcard := F.cardinal D hD
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne (by omega : 1 < D.card) u
  have hvU : v ∈ F.bags.biUnion id := mem_biUnion.mpr ⟨D,hD,hv⟩
  have hdist := disjoint_balls_distance hX u v (F.balls_disjoint hu hvU hvu.symm)
  refine ⟨le_rfl,F.radius_pos,fun _ => rfl,⟨u,by simp [ball,l1dist_self]⟩,v,?_⟩
  change δ ≤ l1dist (X v) (X u)
  rw [l1dist_comm]
  linarith [F.radius_pos]

lemma CompactFamily.scale (hX : ∀v, binary (X v)) {δ Δ : ℝ}
    (F : CompactFamily X δ Δ) : 2*δ ≤ Δ := by
  obtain ⟨D,hD⟩ := F.nonempty
  have hcard := F.cardinal D hD
  obtain ⟨u,hu⟩ := card_pos.mp (by omega : 0 < D.card)
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne (by omega : 1 < D.card) u
  have huU : u ∈ F.bags.biUnion id := mem_biUnion.mpr ⟨D,hD,hu⟩
  have hvU : v ∈ F.bags.biUnion id := mem_biUnion.mpr ⟨D,hD,hv⟩
  exact (disjoint_balls_distance hX u v (F.balls_disjoint huU hvU hvu.symm)).trans
    (F.diameter D hD u hu v hv)

end
end StrongThinTree.Geometry.RadialShell

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell

lemma arrangement_length_bound {n m h : ℕ} (G : MultiGraph n m) {k : ℕ}
    (hk : G.EdgeConnected k) (X : Fin n → Fin h → ℝ) (hX : ∀v, binary (X v))
    {O : Finset (RadialShell (Fin n))} (hO : Arrangement X O) :
    (k:ℝ)*potential 0 O ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  have hb := G.binary_shell_length_bound hk X (fun v => binary_cube (hX v))
    (fun H : O => X H.val.center) (fun H => hX H.val.center)
    (fun H : O => H.val.inner) (fun H : O => H.val.outer)
    (fun H => (hO.1 H.val H.property).2.1.le)
    (fun H => (hO.1 H.val H.property).2.2.2.1)
    (fun H => (hO.1 H.val H.property).2.2.2.2) ?_
  · convert hb using 2
    rw [potential,Finset.sum_coe_sort O (fun H : RadialShell (Fin n) => H.outer-H.inner)]
    apply sum_congr rfl
    intro H hH
    simp only [capacity,mul_zero,sub_zero]
    exact max_eq_left (valid_width_pos (hO.1 H hH)).le
  · intro H K hne w hw hbad
    exact Set.disjoint_left.mp (hO.2 H.property K.property (Subtype.val_injective.ne hne))
      ⟨hw,hbad.2.1,Or.inr hbad.1⟩ ⟨hw,hbad.2.2.2,Or.inr hbad.2.2.1⟩

lemma binary_compact_bound {n m h : ℕ} (G : MultiGraph n m) {k : ℕ}
    (hk : G.EdgeConnected k) (X : Fin n → Fin h → ℝ) (hX : ∀v, binary (X v))
    (q : ℕ) (δ Δ : ℕ → ℝ) (F : ∀i, CompactFamily X (δ i) (Δ i))
    (hnext : ∀i, i+1 < q → Δ (i+1) ≤ δ i/12) :
    (k:ℝ)/4*(∑i ∈ range q, δ i*(∑D ∈ (F i).bags, (D.card : ℝ))) ≤
      ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  let D := fun i => if i < q then Δ i else 0
  have hD0 : ∀i ≤ q, 0 ≤ D i := by
    intro i hi
    dsimp [D]
    split_ifs with hh
    · linarith [(F i).scale hX,(F i).radius_pos]
    · exact le_rfl
  obtain ⟨Z,hZ,hZp⟩ := compact_arrangement hX q δ D
    (fun i => (F i).bags.biUnion id) (fun i => (F i).bags)
    (fun i _ => (F i).radius_pos)
    (fun i hi => by simpa [D,hi] using (F i).scale hX) hD0
    (by
      intro i hi
      dsimp [D]
      split_ifs with hh
      · linarith [hnext i hh]
      · linarith [(F i).radius_pos])
    (fun i _ u hu => (F i).ball_valid hX hu)
    (fun i _ => (F i).balls_disjoint)
    (fun i _ => (F i).bags_disjoint)
    (by
      intro i hi S hS
      refine ⟨?_,?_,?_,?_⟩
      · intro u hu; exact mem_biUnion.mpr ⟨S,hS,hu⟩
      · exact card_pos.mp (by have := (F i).cardinal S hS; omega)
      · simpa [D,hi] using (F i).diameter S hS
      · simpa [D,hi] using (F i).compact S hS)
  simp only [D,lt_self_iff_false,ite_false] at hZp
  have hmul := mul_le_mul_of_nonneg_left hZp (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  have hlength := G.arrangement_length_bound hk X hX hZ
  linarith

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.SpectralPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι uι2 uV uι3 uV2 uV3 uV4 uV5 uV6 uι4 uη

section
open scoped Classical
open Matrix

namespace StrongThinTree.Spectral
noncomputable section
open Finset LinearMap
open scoped InnerProductSpace
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma frobSq_eq_sum {ι : Type uι} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq T = ∑i, ‖T (b i)‖ ^ 2 := by
  rw [frobSq, LinearMap.trace_eq_sum_inner _ b]
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]

lemma frobSq_nonneg (T : E →ₗ[ℝ] E) : 0 ≤ frobSq T := by
  rw [frobSq_eq_sum (stdOrthonormalBasis ℝ E)]
  positivity

lemma frobSq_adjoint (T : E →ₗ[ℝ] E) : frobSq T.adjoint = frobSq T := by
  rw [frobSq, adjoint_adjoint, LinearMap.trace_comp_comm', frobSq]

omit [FiniteDimensional ℝ E] in
lemma trace_bound (T : E →ₗ[ℝ] E) {ι : Type uι2} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    |LinearMap.trace ℝ E T| ≤ ∑i, ‖T (b i)‖ := by
  rw [LinearMap.trace_eq_sum_inner _ b]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro i hi
  calc
    |⟪b i, T (b i)⟫_ℝ| ≤ ‖b i‖ * ‖T (b i)‖ := abs_real_inner_le_norm _ _
    _ = ‖T (b i)‖ := by rw [b.orthonormal.norm_eq_one, one_mul]

lemma norm_eigenvector (T : E →ₗ[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    ‖T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)‖ = T.singularValues i := by
  let h := T.isSymmetric_adjoint_comp_self
  let b := h.eigenvectorBasis rfl
  have he := h.apply_eigenvectorBasis rfl i
  have he' := congrArg (fun x => ⟪b i, x⟫_ℝ) he
  change ⟪b i, T.adjoint (T (b i))⟫_ℝ = ⟪b i, h.eigenvalues rfl i • b i⟫_ℝ at he'
  rw [adjoint_inner_right, real_inner_self_eq_norm_sq, inner_smul_right,
    real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow, mul_one] at he'
  rw [T.singularValues_fin rfl i, ← he', Real.sqrt_sq (norm_nonneg _)]

lemma trace_le_singular_sum (T : E →ₗ[ℝ] E) :
    |LinearMap.trace ℝ E T| ≤ ∑i : Fin (Module.finrank ℝ E), T.singularValues i := by
  simpa only [norm_eigenvector] using trace_bound T (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)

lemma frobSq_eq_singular_sum (T : E →ₗ[ℝ] E) :
    frobSq T = ∑i : Fin (Module.finrank ℝ E), T.singularValues i ^ 2 := by
  rw [frobSq_eq_sum (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)]
  simp only [norm_eigenvector]

lemma projection_symmetric (K : Submodule ℝ E) : K.starProjection.toLinearMap.IsSymmetric := by
  intro u v
  exact K.inner_starProjection_left_eq_right u v

lemma projection_sq (K : Submodule ℝ E) :
    K.starProjection.toLinearMap ∘ₗ K.starProjection.toLinearMap = K.starProjection.toLinearMap := by
  ext v
  exact K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem v)

lemma projection_trace (K : Submodule ℝ E) :
    LinearMap.trace ℝ E K.starProjection.toLinearMap = (Module.finrank ℝ K : ℝ) := by
  exact (show LinearMap.IsProj K K.starProjection.toLinearMap from
    ⟨K.starProjection_apply_mem, fun v hv => K.starProjection_eq_self_iff.mpr hv⟩).trace

lemma projection_inner (K : Submodule ℝ E) (v : E) :
    ⟪v, K.starProjection v⟫_ℝ = ‖K.starProjection v‖ ^ 2 := by
  rw [real_inner_comm]
  exact K.re_inner_starProjection_eq_normSq v

lemma frobSq_projection_le (K : Submodule ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq (K.starProjection.toLinearMap ∘ₗ T) ≤ frobSq T := by
  rw [frobSq_eq_sum (stdOrthonormalBasis ℝ E), frobSq_eq_sum (stdOrthonormalBasis ℝ E)]
  apply sum_le_sum
  intro i hi
  exact pow_le_pow_left₀ (norm_nonneg _) (K.norm_starProjection_apply_le _) 2

lemma frobSq_projection (K : Submodule ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq (K.starProjection.toLinearMap ∘ₗ T) =
      LinearMap.trace ℝ E ((T ∘ₗ T.adjoint) ∘ₗ K.starProjection.toLinearMap) := by
  let P := K.starProjection.toLinearMap
  have hP : P.adjoint = P := (projection_symmetric K).adjoint_eq
  have hPP : P ∘ₗ P = P := projection_sq K
  change LinearMap.trace ℝ E ((P ∘ₗ T).adjoint ∘ₗ (P ∘ₗ T)) = _
  have heq : (P ∘ₗ T).adjoint ∘ₗ (P ∘ₗ T) = T.adjoint ∘ₗ (P ∘ₗ T) := by
    rw [adjoint_comp, hP]
    ext v
    change T.adjoint (P (P (T v))) = T.adjoint (P (T v))
    exact congrArg T.adjoint (congrArg (fun f : E →ₗ[ℝ] E => f (T v)) hPP)
  rw [heq, LinearMap.trace_comp_comm', comp_assoc, LinearMap.trace_comp_comm']

lemma weighted_tail_le {d k : ℕ} (hk : k ≤ d) (s w : Fin d → ℝ)
    (hs : Antitone s) (hn : ∀i, 0 ≤ s i)
    (hw : ∀i, 0 ≤ w i ∧ w i ≤ 1)
    (hsum : (d - k : ℕ) ≤ ∑i, w i) :
    (∑i with k ≤ i.val, s i) ≤ ∑i, s i * w i := by
  classical
  by_cases hkd : k = d
  · subst k
    have hz : univ.filter (fun i : Fin d => d ≤ i.val) = ∅ := by
      apply eq_empty_of_forall_notMem
      intro i hi
      exact (not_le_of_gt i.isLt) (mem_filter.mp hi).2
    rw [hz, sum_empty]
    exact sum_nonneg (fun i _ => mul_nonneg (hn i) (hw i).1)
  have hkd' : k < d := lt_of_le_of_ne hk hkd
  let c := s ⟨k, hkd'⟩
  let L := univ.filter (fun i : Fin d => i.val < k)
  let R := univ.filter (fun i : Fin d => k ≤ i.val)
  have hc : 0 ≤ c := hn _
  have hRcard : R.card = d - k := by
    suffices L.card = k by
      have hcard := card_filter_add_card_filter_not (s := (univ : Finset (Fin d))) (p := fun i => i.val < k)
      simp only [card_univ, Fintype.card_fin, not_lt] at hcard
      change L.card + R.card = d at hcard
      omega
    change (univ.filter (fun i : Fin d => i.val < k)).card = k
    calc
      _ = (univ : Finset (Fin k)).card := by
        apply card_bij (fun i hi => (⟨i.val, (mem_filter.mp hi).2⟩ : Fin k))
        · intro i hi; exact mem_univ _
        · intro i hi j hj he; exact Fin.ext (congrArg (fun x : Fin k => x.val) he)
        · intro j hj
          refine ⟨⟨j.val, j.isLt.trans_le hk⟩, mem_filter.mpr ⟨mem_univ _, j.isLt⟩, ?_⟩
          rfl
      _ = k := by simp
  have hsplit (f : Fin d → ℝ) : (∑i ∈ L, f i) + (∑i ∈ R, f i) = ∑i, f i := by
    simpa only [L, R, not_lt] using (sum_filter_add_sum_filter_not univ (fun i : Fin d => i.val < k) f)
  have hl : c * (∑i ∈ L, w i) ≤ ∑i ∈ L, s i * w i := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right (hs (by exact (mem_filter.mp hi).2.le)) (hw i).1
  have hr : (∑i ∈ R, s i) - ∑i ∈ R, s i * w i ≤ c * ((d - k : ℕ) - ∑i ∈ R, w i) := by
    have hcard : (R.card : ℝ) = ∑i ∈ R, (1 : ℝ) := by simp
    rw [← hRcard, hcard, ← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
    apply sum_le_sum
    intro i hi
    have hsic : s i ≤ c := hs (by exact (mem_filter.mp hi).2)
    have h := mul_le_mul_of_nonneg_right hsic (sub_nonneg.mpr (hw i).2)
    linarith
  have hwc : c * ((d - k : ℕ) - ∑i ∈ R, w i) ≤ c * ∑i ∈ L, w i := by
    apply mul_le_mul_of_nonneg_left _ hc
    have hspl := hsplit w
    linarith
  have hspl := hsplit (fun i => s i * w i)
  change (∑i ∈ R, s i) ≤ _
  linarith

lemma eigenvalue_eq_singular_sq (T : E →ₗ[ℝ] E) (i : Fin (Module.finrank ℝ E)) :
    T.isSymmetric_adjoint_comp_self.eigenvalues rfl i = T.singularValues i ^ 2 := by
  let h := T.isSymmetric_adjoint_comp_self
  let b := h.eigenvectorBasis rfl
  have he' := congrArg (fun x => ⟪b i, x⟫_ℝ) (h.apply_eigenvectorBasis rfl i)
  change ⟪b i, T.adjoint (T (b i))⟫_ℝ = ⟪b i, h.eigenvalues rfl i • b i⟫_ℝ at he'
  rw [adjoint_inner_right, real_inner_self_eq_norm_sq, inner_smul_right,
    real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one, one_pow, mul_one] at he'
  rw [← he']
  exact congrArg (fun x : ℝ => x ^ 2) (norm_eigenvector T i)

lemma trace_adjoint (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T.adjoint = LinearMap.trace ℝ E T := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E)]
  apply sum_congr rfl
  intro i hi
  rw [adjoint_inner_right, real_inner_comm]

lemma frobSq_projection_eigenbasis (K : Submodule ℝ E) (T : E →ₗ[ℝ] E) :
    frobSq (K.starProjection.toLinearMap ∘ₗ T) =
      ∑i : Fin (Module.finrank ℝ E), T.adjoint.singularValues i ^ 2 *
        ⟪T.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i,
          K.starProjection (T.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)⟫_ℝ := by
  let h := T.adjoint.isSymmetric_adjoint_comp_self
  let b := h.eigenvectorBasis rfl
  rw [frobSq_projection, LinearMap.trace_eq_sum_inner _ b]
  apply sum_congr rfl
  intro i hi
  have he : (T ∘ₗ T.adjoint) (b i) = h.eigenvalues rfl i • b i := by
    calc
      _ = (T.adjoint.adjoint ∘ₗ T.adjoint) (b i) := by rw [adjoint_adjoint]
      _ = _ := h.apply_eigenvectorBasis rfl i
  change ⟪b i, (T ∘ₗ T.adjoint) (K.starProjection (b i))⟫_ℝ = _
  rw [← T.isSymmetric_self_comp_adjoint, he, real_inner_smul_left,
    eigenvalue_eq_singular_sq]

lemma rank_approximation (T C : E →ₗ[ℝ] E) {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) (hC : Module.finrank ℝ (LinearMap.range C) ≤ k) :
    (∑i : Fin (Module.finrank ℝ E) with k ≤ i.val, T.adjoint.singularValues i ^ 2) ≤
      frobSq (T - C) := by
  let K := (LinearMap.range C)ᗮ
  let P := K.starProjection.toLinearMap
  let b := T.adjoint.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl
  let w := fun i => ⟪b i, K.starProjection (b i)⟫_ℝ
  have hw (i : Fin (Module.finrank ℝ E)) : 0 ≤ w i ∧ w i ≤ 1 := by
    change 0 ≤ ⟪b i, K.starProjection (b i)⟫_ℝ ∧ _
    rw [projection_inner]
    constructor
    · positivity
    · have hh := K.norm_starProjection_apply_le (b i)
      rw [b.orthonormal.norm_eq_one] at hh
      dsimp [w]
      rw [projection_inner]
      exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (one_pow _)
  have hsum : ((Module.finrank ℝ E - k : ℕ) : ℝ) ≤ ∑i, w i := by
    have hh := (LinearMap.range C).finrank_add_finrank_orthogonal
    have hd : Module.finrank ℝ E - k ≤ Module.finrank ℝ K := by dsimp [K]; omega
    calc
      _ ≤ (Module.finrank ℝ K : ℝ) := by exact_mod_cast hd
      _ = ∑i, w i := by rw [← projection_trace, LinearMap.trace_eq_sum_inner _ b]; rfl
  have hs : Antitone (fun i : Fin (Module.finrank ℝ E) => T.adjoint.singularValues i ^ 2) := by
    intro i j hij
    exact pow_le_pow_left₀ (T.adjoint.singularValues_nonneg _) (T.adjoint.singularValues_antitone hij) 2
  have hb := weighted_tail_le hk (fun i => T.adjoint.singularValues i ^ 2) w hs
    (fun _ => sq_nonneg _) hw hsum
  have hPC : P ∘ₗ C = 0 := by
    ext x
    change K.starProjection (C x) = 0
    apply K.starProjection_apply_eq_zero_iff.mpr
    change C x ∈ (LinearMap.range C)ᗮᗮ
    rw [Submodule.orthogonal_orthogonal]
    exact LinearMap.mem_range_self C x
  have heq : P ∘ₗ (T - C) = P ∘ₗ T := by rw [comp_sub, hPC, sub_zero]
  calc
    _ ≤ ∑i : Fin (Module.finrank ℝ E), T.adjoint.singularValues i ^ 2 * w i := hb
    _ = frobSq (P ∘ₗ T) := (frobSq_projection_eigenbasis K T).symm
    _ = frobSq (P ∘ₗ (T - C)) := congrArg frobSq heq.symm
    _ ≤ frobSq (T - C) := frobSq_projection_le K (T - C)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in

lemma separated_net {V : Type uV} [DecidableEq V] (F : Finset V) (hF : F.Nonempty)
    (Y : V → E) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ S : Finset V, S ⊆ F ∧ S.Nonempty ∧
      (∀u ∈ S, ∀v ∈ S, u ≠ v → δ < ‖Y u - Y v‖) ∧
      ∀u ∈ F, ∃v ∈ S, ‖Y u - Y v‖ ≤ δ := by
  classical
  let sep : Finset V → Prop := fun S => ∀u ∈ S, ∀v ∈ S, u ≠ v → δ < ‖Y u - Y v‖
  let : DecidablePred sep := fun _ => Classical.propDecidable _
  let good := F.powerset.filter sep
  have hgood : good.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), by simp [sep]⟩⟩
  obtain ⟨S, hS, hmax⟩ := exists_max_image good card hgood
  obtain ⟨hSF, hsep⟩ := mem_filter.mp hS
  have hcover : ∀u ∈ F, ∃v ∈ S, ‖Y u - Y v‖ ≤ δ := by
    intro u hu
    by_contra! hn
    have huS : u ∉ S := by
      intro huS
      have h := hn u huS
      simp only [sub_self, norm_zero] at h
      linarith
    have hnew : insert u S ∈ good := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hu (mem_powerset.mp hSF)), ?_⟩
      intro x hx y hy hxy
      rcases mem_insert.mp hx with hxU | hxS
      · subst x
        rcases mem_insert.mp hy with hyU | hyS
        · exact (hxy hyU.symm).elim
        · exact hn y hyS
      · rcases mem_insert.mp hy with hyU | hyS
        · subst y
          rw [norm_sub_rev]; exact hn x hxS
        · exact hsep x hxS y hyS hxy
    have hh := hmax _ hnew
    rw [card_insert_of_notMem huS] at hh
    omega
  refine ⟨S, mem_powerset.mp hSF, ?_, hsep, hcover⟩
  obtain ⟨u, hu⟩ := hF
  obtain ⟨v, hv, _⟩ := hcover u hu
  exact ⟨v, hv⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma norm_sub_sq_le_twice (x y : E) : ‖x-y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have hn := norm_sub_le x y
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hh : ‖x-y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  linarith [sq_nonneg (‖x‖ - ‖y‖)]

omit [FiniteDimensional ℝ E] in
lemma range_le_of_basis {ι : Type uι3} [Fintype ι] (b : Module.Basis ι ℝ E)
    (T : E →ₗ[ℝ] E) (K : Submodule ℝ E) (h : ∀i, T (b i) ∈ K) :
    LinearMap.range T ≤ K := by
  rintro _ ⟨x, rfl⟩
  rw [← b.sum_repr x, map_sum]
  apply K.sum_mem
  intro i hi
  rw [map_smul]
  exact K.smul_mem _ (h i)

omit [FiniteDimensional ℝ E] in

lemma difference_span_rank {V : Type uV2} [DecidableEq V] (S : Finset V)
    (Y : V → E) {v₀ : V} (hv₀ : v₀ ∈ S) :
    Module.finrank ℝ (Submodule.span ℝ
      ((fun v => Y v - Y v₀) '' (S : Set V))) ≤ S.card - 1 := by
  classical
  let A := (S.erase v₀).image (fun v => Y v - Y v₀)
  have heq : Submodule.span ℝ ((fun v => Y v - Y v₀) '' (S : Set V)) =
      Submodule.span ℝ (A : Set E) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨v, hv, rfl⟩
      by_cases heq : v = v₀
      · simp [heq]
      · exact Submodule.subset_span (mem_image.mpr ⟨v, mem_erase.mpr ⟨heq, hv⟩, rfl⟩)
    · apply Submodule.span_mono
      intro x hx
      obtain ⟨v, hv, rfl⟩ := mem_image.mp hx
      exact ⟨v, mem_of_mem_erase hv, rfl⟩
  rw [heq]
  exact (finrank_span_finset_le_card A).trans ((card_image_le).trans_eq (card_erase_of_mem hv₀))

lemma spectral_centers_at_radius {V : Type uV3} [DecidableEq V]
    (Y : V → E) (u v : Fin (Module.finrank ℝ E) → V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (T : E →ₗ[ℝ] E) (hT : ∀i, T (b i) = Y (u i) - Y (v i))
    {p : ℕ} (hp : 1 ≤ p) (hpd : p ≤ Module.finrank ℝ E)
    {r : ℝ} (hr : 0 < r)
    (hrT : 32 * (Module.finrank ℝ E : ℝ) * r =
      ∑i : Fin (Module.finrank ℝ E) with p - 1 ≤ i.val, T.adjoint.singularValues i ^ 2) :
    ∃ S : Finset V, S ⊆ (univ.image u ∪ univ.image v) ∧ p < S.card ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x - Y y‖) := by
  classical
  let F := univ.image u ∪ univ.image v
  have hd : 0 < Module.finrank ℝ E := lt_of_lt_of_le (by omega) hpd
  have hF : F.Nonempty := ⟨u ⟨0, hd⟩, mem_union_left _ (mem_image.mpr ⟨⟨0, hd⟩, mem_univ _, rfl⟩)⟩
  obtain ⟨S, hSF, hSne, hsep, hcover⟩ := separated_net F hF Y (show 0 ≤ 2 * Real.sqrt r by positivity)
  refine ⟨S, hSF, ?_, hsep⟩
  by_contra! hSp
  obtain ⟨v₀, hv₀⟩ := hSne
  let c : V → V := fun x => if hx : x ∈ F then Classical.choose (hcover x hx) else v₀
  have hcS (x : V) : c x ∈ S := by
    dsimp [c]
    split
    · exact (Classical.choose_spec (hcover _ ‹_›)).1
    · exact hv₀
  have hcclose (x : V) (hx : x ∈ F) : ‖Y x - Y (c x)‖ ^ 2 ≤ 4 * r := by
    have hh := (Classical.choose_spec (hcover x hx)).2
    have he : c x = Classical.choose (hcover x hx) := dite_eq_left hx
    rw [he]
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
    linarith [Real.sq_sqrt hr.le]
  have hu (i) : u i ∈ F := mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  have hv (i) : v i ∈ F := mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩)
  let C := b.toBasis.constr ℝ (fun i => Y (c (u i)) - Y (c (v i)))
  let K := Submodule.span ℝ ((fun x => Y x - Y v₀) '' (S : Set V))
  have hCK : LinearMap.range C ≤ K := by
    apply range_le_of_basis b.toBasis
    intro i
    change C (b.toBasis i) ∈ K
    rw [Module.Basis.constr_basis]
    have huK : Y (c (u i)) - Y v₀ ∈ K := Submodule.subset_span ⟨_, hcS _, rfl⟩
    have hvK : Y (c (v i)) - Y v₀ ∈ K := Submodule.subset_span ⟨_, hcS _, rfl⟩
    convert K.sub_mem huK hvK using 1 ; abel
  have hCrank : Module.finrank ℝ (LinearMap.range C) ≤ p - 1 :=
    (Submodule.finrank_mono hCK).trans ((difference_span_rank S Y hv₀).trans (Nat.sub_le_sub_right hSp 1))
  have hlow := rank_approximation T C ((Nat.sub_le p 1).trans hpd) hCrank
  rw [← hrT] at hlow
  have hupp : frobSq (T - C) ≤ 16 * (Module.finrank ℝ E : ℝ) * r := by
    have hpoint (i : Fin (Module.finrank ℝ E)) : ‖(T - C) (b i)‖ ^ 2 ≤ 16 * r := by
      rw [LinearMap.sub_apply, hT]
      change ‖(Y (u i) - Y (v i)) - C (b.toBasis i)‖ ^ 2 ≤ _
      rw [Module.Basis.constr_basis]
      have heq : (Y (u i) - Y (v i)) - (Y (c (u i)) - Y (c (v i))) =
          (Y (u i) - Y (c (u i))) - (Y (v i) - Y (c (v i))) := by abel
      rw [heq]
      have hh := norm_sub_sq_le_twice (Y (u i) - Y (c (u i))) (Y (v i) - Y (c (v i)))
      linarith [hcclose (u i) (hu i), hcclose (v i) (hv i)]
    rw [frobSq_eq_sum b]
    calc
      _ ≤ ∑i : Fin (Module.finrank ℝ E), (16 * r) := sum_le_sum (fun i _ => hpoint i)
      _ = _ := by simp; ring
  have hdr : (0 : ℝ) < Module.finrank ℝ E := by exact_mod_cast hd
  linarith [mul_pos hdr hr]

private lemma tail_split {d : ℕ} (s : Fin d → ℝ) (p : ℕ) :
    tail s p = block s p + tail s (2*p) := by
  classical
  have hh := sum_filter_add_sum_filter_not (univ.filter (fun i : Fin d => p ≤ i.val + 1))
    (fun i => i.val + 1 < 2*p) s
  have heq : (univ.filter (fun i : Fin d => p ≤ i.val+1)).filter (fun i => ¬i.val+1 < 2*p) =
      univ.filter (fun i : Fin d => 2*p ≤ i.val+1) := by
    ext i
    simp only [mem_filter, mem_univ, true_and]
    omega
  rw [heq] at hh
  simpa only [filter_filter, tail, block] using hh.symm

private lemma block_sq_le {d : ℕ} (s : Fin d → ℝ) (p : ℕ) :
    block s p ^ 2 ≤ (p : ℝ) * tail (fun i => s i ^ 2) p := by
  classical
  let B := univ.filter (fun i : Fin d => p ≤ i.val+1 ∧ i.val+1 < 2*p)
  have hcard : B.card ≤ p := by
    have hh : B.card ≤ (range p).card := by
      apply card_le_card_of_injOn (fun i : Fin d => i.val+1-p)
      · intro i hi
        have h := (mem_filter.mp hi).2
        exact mem_range.mpr (by dsimp; omega)
      · intro i hi j hj hij
        have hi' := (mem_filter.mp hi).2
        have hj' := (mem_filter.mp hj).2
        apply Fin.ext
        dsimp at hij
        omega
    simpa using hh
  have hsum : (∑i ∈ B, s i ^ 2) ≤ tail (fun i => s i ^ 2) p := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro i hi; exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2.1⟩
    · intro i hi hn; positivity
  have hcs := sum_mul_sq_le_sq_mul_sq B s (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  calc
    _ ≤ (∑i ∈ B, s i ^ 2) * (B.card : ℝ) := hcs
    _ ≤ tail (fun i => s i ^ 2) p * (p : ℝ) :=
      mul_le_mul hsum (by exact_mod_cast hcard) (by positivity)
        (sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := mul_comm _ _

lemma dyadic_tail_selection {d p₀ L : ℕ} (s : Fin d → ℝ)
    (hs : ∀i, 0 ≤ s i) (_hp₀ : 1 ≤ p₀) (hL : 0 < L)
    (hcover : d < 2^L*p₀) (hpositive : 0 < tail s p₀) :
    ∃ p : ℕ, p₀ ≤ p ∧ p ≤ d ∧
      tail s p₀ ^ 2 ≤ (L : ℝ)^2 * ((p : ℝ) * tail (fun i => s i ^ 2) p) := by
  classical
  let p : ℕ → ℕ := fun j => 2^j*p₀
  let M : ℕ → ℝ := fun j => (p j : ℝ) * tail (fun i => s i ^ 2) (p j)
  obtain ⟨j, hj, hmax⟩ := exists_max_image (range L) M (nonempty_range_iff.mpr (ne_of_gt hL))
  have hM : 0 ≤ M j := mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => sq_nonneg _))
  have hzero : tail s (p L) = 0 := by
    apply sum_eq_zero
    intro i hi
    have hh := (mem_filter.mp hi).2
    dsimp [p] at hh
    omega
  have hpnext (i : ℕ) : p (i+1) = 2*p i := by dsimp [p]; rw [pow_succ]; ring
  have hsplit (i : ℕ) : tail s (p i) - tail s (p (i+1)) = block s (p i) := by
    rw [hpnext, tail_split s (p i)]
    ring
  have hsum : (∑i ∈ range L, block s (p i)) = tail s p₀ := by
    conv_lhs => enter [2, i]; rw [← hsplit]
    rw [sum_range_sub', hzero]
    simp [p]
  have hbound (i : ℕ) (hi : i ∈ range L) : block s (p i) ≤ Real.sqrt (M j) := by
    have hh := (block_sq_le s (p i)).trans (hmax i hi)
    have hn : 0 ≤ block s (p i) := sum_nonneg (fun i _ => hs i)
    nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg (M j)]
  have htotal : tail s p₀ ≤ (L : ℝ) * Real.sqrt (M j) := by
    rw [← hsum]
    calc
      _ ≤ ∑i ∈ range L, Real.sqrt (M j) := sum_le_sum hbound
      _ = _ := by simp
  have hsq : tail s p₀ ^ 2 ≤ (L : ℝ)^2 * M j := by
    have hh := pow_le_pow_left₀ hpositive.le htotal 2
    rw [mul_pow, Real.sq_sqrt hM] at hh
    exact hh
  have hpd : p j ≤ d := by
    by_contra! hpd
    have hzero : tail (fun i => s i ^ 2) (p j) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hh := (mem_filter.mp hi).2
      omega
    dsimp [M] at hsq
    rw [hzero, mul_zero, mul_zero] at hsq
    nlinarith
  refine ⟨p j, ?_, hpd, hsq⟩
  have hpow : 1 ≤ 2^j := Nat.one_le_pow _ _ (by omega)
  simpa only [one_mul, p] using (Nat.mul_le_mul_right p₀ hpow)

lemma singular_tail_selection {d : ℕ} (hd : 0 < d) (s : Fin d → ℝ)
    (hs : ∀i, 0 ≤ s i) {a τ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 < τ)
    (htrace : τ ≤ ∑i, s i) (hfrob : a * d * (∑i, s i ^ 2) ≤ τ ^ 2) :
    ∃ p L : ℕ, a * d / 16 < p ∧ p ≤ d ∧ 0 < L ∧
      (L : ℝ) ≤ 5 + Real.logb 2 (1/a) ∧
      9 * τ ^ 2 ≤ 16 * (L : ℝ)^2 * ((p : ℝ) * tail (fun i => s i ^ 2) p) := by
  classical
  let f := ⌊a * d / 16⌋₊
  let p₀ := f+1
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have had : 0 ≤ a * d / 16 := by positivity
  have hf : (f : ℝ) ≤ a * d / 16 := Nat.floor_le had
  have hp₀ : a * d / 16 < (p₀ : ℝ) := by simpa only [p₀, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (a*d/16)
  have hp₀pos : 1 ≤ p₀ := by dsimp [p₀]; omega
  have hp₀d : p₀ ≤ d := by
    have hf' : (f : ℝ) < d := by nlinarith
    have hfn : f < d := by exact_mod_cast hf'
    dsimp [p₀]; omega
  let I := univ.filter (fun i : Fin d => i.val < f)
  have hcard : I.card ≤ f := by
    have hh : I.card ≤ (range f).card := by
      apply card_le_card_of_injOn (fun i : Fin d => i.val)
      · intro i hi; exact mem_range.mpr (mem_filter.mp hi).2
      · intro i hi j hj hij; exact Fin.ext hij
    simpa using hh
  have hhead : ∑i ∈ I, s i ≤ τ/4 := by
    have hcs := sum_mul_sq_le_sq_mul_sq I s (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
    have hsum : (∑i ∈ I, s i ^ 2) ≤ ∑i, s i ^ 2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i hi hn => sq_nonneg _)
    have hcard' : (I.card : ℝ) ≤ a*d/16 := (by exact_mod_cast hcard : (I.card : ℝ) ≤ f).trans hf
    have hupp := mul_le_mul hsum hcard' (Nat.cast_nonneg _) (sum_nonneg (fun _ _ => sq_nonneg _))
    have hheadn : 0 ≤ ∑i ∈ I, s i := sum_nonneg (fun i _ => hs i)
    nlinarith
  have hsplit : (∑i ∈ I, s i) + tail s p₀ = ∑i, s i := by
    have hh := sum_filter_add_sum_filter_not univ (fun i : Fin d => i.val < f) s
    have heq : univ.filter (fun i : Fin d => ¬i.val < f) =
        univ.filter (fun i : Fin d => p₀ ≤ i.val+1) := by
      ext i
      simp only [mem_filter, mem_univ, true_and]
      dsimp [p₀]
      omega
    rw [heq] at hh
    exact hh
  have htail : 3*τ/4 ≤ tail s p₀ := by linarith
  let q := d / p₀
  let L := q.log2 + 1
  have hq : q ≠ 0 := by
    have hqp : 0 < q := Nat.div_pos hp₀d (by omega)
    omega
  have hL : 0 < L := by dsimp [L]; omega
  have hcover : d < 2^L*p₀ := by
    have hh : q < 2^L := (Nat.log2_lt hq).mp (by dsimp [L]; omega)
    exact (Nat.div_lt_iff_lt_mul (by omega)).mp hh
  have hp₀r : (0 : ℝ) < p₀ := by exact_mod_cast (show 0 < p₀ by omega)
  have hqreal : (q : ℝ) ≤ 16/a := by
    have hh : (q : ℝ) * p₀ ≤ d := by exact_mod_cast (Nat.div_mul_le_self d p₀)
    have hqn : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    apply (le_div_iff₀ ha).mpr
    nlinarith
  have hlog : (L : ℝ) ≤ 5 + Real.logb 2 (1/a) := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero hq)
    have hmono := (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) hqpos (by positivity : (0 : ℝ) < 16/a)).mpr hqreal
    have hlogq := Real.log2_le_logb q
    have hlog16 : Real.logb 2 (16/a) = 4 + Real.logb 2 (1/a) := by
      rw [show (16 : ℝ)/a = 2^4*(1/a) by ring, Real.logb_mul (by norm_num) (ne_of_gt (by positivity : (0 : ℝ) < 1/a)), Real.logb_pow]
      norm_num
    rw [hlog16] at hmono
    dsimp [L]
    push_cast
    linarith
  obtain ⟨p, hpp, hpd, hpbig⟩ := dyadic_tail_selection s hs hp₀pos hL hcover (by linarith)
  refine ⟨p, L, hp₀.trans_le (by exact_mod_cast hpp), hpd, hL, hlog, ?_⟩
  have htailn : 0 ≤ tail s p₀ := by linarith
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 3*τ/4) htail 2
  linarith

lemma trace_sq_le_frobSq (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T ^ 2 ≤ (Module.finrank ℝ E : ℝ) * frobSq T := by
  let b := stdOrthonormalBasis ℝ E
  have hh := trace_bound T b
  have hn : 0 ≤ ∑i, ‖T (b i)‖ := sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) hh 2
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun i => ‖T (b i)‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hcs
  rw [← frobSq_eq_sum b] at hcs
  rw [sq_abs] at hsq
  exact hsq.trans (hcs.trans_eq (mul_comm _ _))

lemma spectral_packing_log {V : Type uV4} [DecidableEq V]
    (Y : V → E) (u v : Fin (Module.finrank ℝ E) → V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (T : E →ₗ[ℝ] E) (hT : ∀i, T (b i) = Y (u i) - Y (v i))
    {a : ℝ} (ha : 0 < a) (htrace : 0 < |LinearMap.trace ℝ E T|)
    (hassume : a * Module.finrank ℝ E * frobSq T ≤ LinearMap.trace ℝ E T ^ 2) :
    a ≤ 1 ∧ ∃ S : Finset V, ∃ r : ℝ, 0 < r ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      a * Module.finrank ℝ E / 16 ≤ S.card ∧
      9 * LinearMap.trace ℝ E T ^ 2 ≤
        512 * Module.finrank ℝ E * (5 + Real.logb 2 (1/a))^2 * (S.card * r) ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x - Y y‖) := by
  classical
  let d := Module.finrank ℝ E
  let τ := |LinearMap.trace ℝ E T|
  have htsq : τ ^ 2 = LinearMap.trace ℝ E T ^ 2 := sq_abs _
  have htpos : 0 < τ ^ 2 := sq_pos_of_pos htrace
  have htraceF := trace_sq_le_frobSq T
  have hdn : (0 : ℝ) < d := by
    have hf := frobSq_nonneg T
    dsimp [d]
    by_contra! hn
    have hz : (Module.finrank ℝ E : ℝ) = 0 := le_antisymm hn (Nat.cast_nonneg _)
    rw [hz, zero_mul] at htraceF
    linarith
  have hd : 0 < d := by exact_mod_cast hdn
  have hfpos : 0 < frobSq T := by nlinarith
  have ha1 : a ≤ 1 := by
    have hh : 0 < (d : ℝ) * frobSq T := mul_pos hdn hfpos
    have hh' : a * ((d : ℝ) * frobSq T) ≤ (d : ℝ) * frobSq T := by
      calc
        _ = a * d * frobSq T := by ring
        _ ≤ LinearMap.trace ℝ E T ^ 2 := hassume
        _ ≤ _ := htraceF
    exact (mul_le_mul_iff_left₀ hh).mp (by simpa only [mul_comm, one_mul] using hh')
  let s := fun i : Fin d => T.adjoint.singularValues i
  have hs (i : Fin d) : 0 ≤ s i := T.adjoint.singularValues_nonneg i
  have hsum : τ ≤ ∑i, s i := by
    simpa only [trace_adjoint] using trace_le_singular_sum T.adjoint
  have hsq : a * d * (∑i, s i ^ 2) ≤ τ ^ 2 := by
    rw [← frobSq_eq_singular_sum T.adjoint, frobSq_adjoint, htsq]
    exact hassume
  obtain ⟨p, L, hpmin, hpd, hL, hlog, hpbig⟩ := singular_tail_selection hd s hs ha ha1 htrace hsum hsq
  have hpp : 1 ≤ p := by
    have hpp' : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) hpmin
    have : 0 < p := by exact_mod_cast hpp'
    omega
  let tailVal := tail (fun i => s i ^ 2) p
  have htailpos : 0 < tailVal := by
    have hn : 0 ≤ tailVal := sum_nonneg (fun _ _ => sq_nonneg _)
    by_contra! hh
    have hz : tailVal = 0 := le_antisymm hh hn
    change 9*τ^2 ≤ 16*(L:ℝ)^2*((p:ℝ)*tailVal) at hpbig
    rw [hz, mul_zero, mul_zero] at hpbig
    linarith
  let r := tailVal / (32*d)
  have hr : 0 < r := div_pos htailpos (by positivity)
  have hrt : 32*(d:ℝ)*r = tailVal := by dsimp [r]; field_simp
  have heq : tailVal =
      ∑i : Fin d with p-1 ≤ i.val, T.adjoint.singularValues i ^ 2 := by
    unfold tailVal tail
    apply sum_congr
    · ext i
      simp only [mem_filter, mem_univ, true_and]
      omega
    · intro i hi; rfl
  obtain ⟨S, hSF, hpS, hsep⟩ := spectral_centers_at_radius Y u v b T hT hpp hpd hr (hrt.trans heq)
  have hpSr : (p : ℝ) ≤ S.card := by exact_mod_cast hpS.le
  have hSr : 0 ≤ (S.card : ℝ)*r := mul_nonneg (Nat.cast_nonneg _) hr.le
  have hpr : (p : ℝ)*r ≤ S.card*r := mul_le_mul_of_nonneg_right hpSr hr.le
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogn : 0 ≤ 5+Real.logb 2 (1/a) := hLr.le.trans hlog
  have hLsq := pow_le_pow_left₀ hLr.le hlog 2
  refine ⟨ha1, S, r, hr, hSF, by omega, hpmin.le.trans hpSr, ?_, hsep⟩
  have hpbig' : 9*τ^2 ≤ 512*(d:ℝ)*(L:ℝ)^2*((p:ℝ)*r) := by
    change 9*τ^2 ≤ 16*(L:ℝ)^2*((p:ℝ)*tailVal) at hpbig
    rw [← hrt] at hpbig
    convert hpbig using 1 ; ring
  rw [← htsq]
  calc
    _ ≤ 512*(d:ℝ)*(L:ℝ)^2*((p:ℝ)*r) := hpbig'
    _ ≤ 512*(d:ℝ)*(L:ℝ)^2*(S.card*r) :=
      mul_le_mul_of_nonneg_left hpr (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLsq (by positivity)) hSr

lemma logarithmic_power_bound {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hε : 0 < ε) (hε1 : ε < 1/3) :
    ε^2 * a^ε * (5 + Real.logb 2 (1/a))^2 ≤ 16 := by
  let t := Real.log (1/a)
  have ht : 0 ≤ t := Real.log_nonneg (by exact (one_le_div ha).mpr ha1)
  have htlog : t = - Real.log a := by dsimp [t]; rw [Real.log_div (by norm_num) ha.ne']; simp
  have hlog2 : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : 5+Real.logb 2 (1/a) ≤ 5+2*t := by
    dsimp [Real.logb]
    have hh : t / Real.log 2 ≤ 2*t := (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr (by nlinarith)
    linarith
  have hlogn : 0 ≤ 5+Real.logb 2 (1/a) := by
    have hh := Real.logb_nonneg (by norm_num : (1:ℝ)<2) ((one_le_div ha).mpr ha1)
    linarith
  let z := ε*t/2
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hexple : Real.exp (-z) ≤ 1 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by linarith)
  have he1 : Real.exp (-1) ≤ 1/2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (inv_anti₀ (by norm_num : (0:ℝ)<2) (by linarith [Real.add_one_le_exp 1] : (2:ℝ) ≤ Real.exp 1))
  have hzbound : z * Real.exp (-z) ≤ 1/2 := (Real.mul_exp_neg_le_exp_neg_one z).trans he1
  have hmain : ε*(5+Real.logb 2 (1/a))*Real.exp (-z) ≤ 4 := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hε.le) (Real.exp_pos (-z)).le
    have h5 := mul_le_mul_of_nonneg_left hexple (show 0 ≤ 5*ε by positivity)
    dsimp [z] at hzbound
    linarith
  have heq : Real.exp (-z)^2 = a^ε := by
    rw [← Real.exp_nat_mul, Real.rpow_def_of_pos ha]
    congr 1
    dsimp [z]
    rw [htlog]
    ring
  have hn : 0 ≤ ε*(5+Real.logb 2 (1/a))*Real.exp (-z) := by positivity
  have hh := pow_le_pow_left₀ hn hmain 2
  rw [mul_pow, mul_pow, heq] at hh
  linarith

lemma spectral_packing_power {V : Type uV5} [DecidableEq V]
    (Y : V → E) (u v : Fin (Module.finrank ℝ E) → V)
    (b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E)
    (T : E →ₗ[ℝ] E) (hT : ∀i, T (b i) = Y (u i) - Y (v i))
    {a ε : ℝ} (ha : 0 < a) (htrace : 0 < |LinearMap.trace ℝ E T|)
    (hassume : a * Module.finrank ℝ E * frobSq T ≤ LinearMap.trace ℝ E T ^ 2)
    (hε : 0 < ε) (hε1 : ε < 1/3) :
    a ≤ 1 ∧ ∃ S : Finset V, ∃ r : ℝ, 0 < r ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      ε^2 * a * Module.finrank ℝ E ≤ 1024 * S.card ∧
      ε^2 * a^ε * LinearMap.trace ℝ E T ^ 2 ≤
        1024 * Module.finrank ℝ E * (S.card * r) ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x - Y y‖) := by
  obtain ⟨ha1, S, r, hr, hSF, hS2, hcard, hlog, hsep⟩ :=
    spectral_packing_log Y u v b T hT ha htrace hassume
  have he2 : ε^2 ≤ 64 := by nlinarith
  have hd : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hSr : 0 ≤ (S.card : ℝ)*r := mul_nonneg (Nat.cast_nonneg _) hr.le
  have hpow : 0 ≤ ε^2 * a^ε := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ha.le _)
  have hh := mul_le_mul_of_nonneg_left hlog hpow
  have hb := mul_le_mul_of_nonneg_right (logarithmic_power_bound ha ha1 hε hε1)
    (show 0 ≤ 512*(Module.finrank ℝ E : ℝ)*(S.card*r) by positivity)
  refine ⟨ha1, S, r, hr, hSF, hS2, ?_, ?_, hsep⟩
  · have hc : a * Module.finrank ℝ E ≤ 16 * S.card := by linarith
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg ε)
    have hb := mul_le_mul_of_nonneg_right he2 (show 0 ≤ 16*(S.card:ℝ) by positivity)
    linarith
  · have h9 : 9 * (ε^2 * a^ε * LinearMap.trace ℝ E T ^ 2) ≤
        8192 * Module.finrank ℝ E * (S.card * r) := by
      calc
        _ ≤ ε^2 * a^ε *
          (512 * Module.finrank ℝ E * (5 + Real.logb 2 (1/a))^2 * (S.card*r)) := by
            linarith only [hh]
        _ = (ε^2 * a^ε * (5 + Real.logb 2 (1/a))^2) *
            (512 * Module.finrank ℝ E * (S.card*r)) := by ring
        _ ≤ _ := by linarith only [hb]
    have hn : 0 ≤ (Module.finrank ℝ E : ℝ) * (S.card*r) := mul_nonneg hd hSr
    linarith

theorem spectral_packing_coordinates {V : Type uV6} {ι : Type uι4} {η : Type uη} [DecidableEq V]
    [Fintype ι] [Fintype η] [DecidableEq ι] [DecidableEq η]
    (Y : V → EuclideanSpace ℝ η) (u v : ι → V)
    (j : ι → η) (hj : Function.Injective j) {a ε : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1/3)
    (hpos : 0 < (∑i, (Y (u i) - Y (v i)).ofLp (j i))^2)
    (hbound : a * Fintype.card ι * (∑i, ‖Y (u i)-Y (v i)‖^2) ≤
      (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2) :
    a ≤ 1 ∧ ∃ S : Finset V, ∃ r : ℝ, 0 < r ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      ε^2 * a * Fintype.card ι ≤ 1024 * S.card ∧
      ε^2 * a^ε * (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2 ≤
        1024 * Fintype.card ι * (S.card*r) ∧
      (∀x ∈ S, ∀y ∈ S, x ≠ y → 2 * Real.sqrt r < ‖Y x-Y y‖) := by
  classical
  let Y' : V → EuclideanSpace ℝ ι := fun x => WithLp.toLp 2 (fun i => (Y x).ofLp (j i))
  let b₀ := EuclideanSpace.basisFun ι ℝ
  let T := b₀.toBasis.constr ℝ (fun i => Y' (u i)-Y' (v i))
  have hT₀ (i : ι) : T (b₀ i) = Y' (u i)-Y' (v i) :=
    b₀.toBasis.constr_basis ℝ _ i
  have htr : LinearMap.trace ℝ (EuclideanSpace ℝ ι) T =
      ∑i, (Y (u i)-Y (v i)).ofLp (j i) := by
    rw [LinearMap.trace_eq_sum_inner _ b₀]
    apply sum_congr rfl
    intro i hi
    rw [hT₀, EuclideanSpace.basisFun_inner]
    rfl
  have hn (x y : V) : ‖Y' x-Y' y‖^2 ≤ ‖Y x-Y y‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq]
    change (∑i, ‖(Y x-Y y).ofLp (j i)‖^2) ≤ ∑i, ‖(Y x-Y y).ofLp i‖^2
    rw [← sum_image (f := fun i => ‖(Y x-Y y).ofLp i‖^2) hj.injOn]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; positivity)
  have hf : frobSq T ≤ ∑i, ‖Y (u i)-Y (v i)‖^2 := by
    rw [frobSq_eq_sum b₀]
    exact sum_le_sum (fun i _ => by rw [hT₀]; exact hn _ _)
  let e : Fin (Module.finrank ℝ (EuclideanSpace ℝ ι)) ≃ ι :=
    (finCongr finrank_euclideanSpace).trans (Fintype.equivFin ι).symm
  let b := b₀.reindex e.symm
  have hT : ∀i, T (b i) = Y' (u (e i))-Y' (v (e i)) := by
    intro i
    simpa only [b, OrthonormalBasis.reindex_apply, Equiv.symm_symm] using hT₀ (e i)
  have hassume : a * Module.finrank ℝ (EuclideanSpace ℝ ι) * frobSq T ≤
      LinearMap.trace ℝ (EuclideanSpace ℝ ι) T ^ 2 := by
    rw [htr, finrank_euclideanSpace]
    exact (mul_le_mul_of_nonneg_left hf (by positivity)).trans hbound
  have htrace : 0 < |LinearMap.trace ℝ (EuclideanSpace ℝ ι) T| := by
    rw [htr]
    exact abs_pos.mpr (sq_pos_iff.mp hpos)
  obtain ⟨ha1, S, r, hr, hSF, hS2, hcard, hmass, hsep⟩ :=
    spectral_packing_power Y' (u ∘ e) (v ∘ e) b T hT ha htrace hassume hε hε1
  rw [htr, finrank_euclideanSpace] at hmass
  rw [finrank_euclideanSpace] at hcard
  refine ⟨ha1, S, r, hr, ?_, hS2, hcard, hmass, ?_⟩
  · intro x hx
    rcases mem_union.mp (hSF hx) with hh | hh
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hh
      exact mem_union_left _ (mem_image.mpr ⟨e i, mem_univ _, rfl⟩)
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hh
      exact mem_union_right _ (mem_image.mpr ⟨e i, mem_univ _, rfl⟩)
  · intro x hx y hy hxy
    exact (hsep x hx y hy hxy).trans_le ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hn x y))

end
end StrongThinTree.Spectral

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.BagGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uI uV2 uV3 uI2 uJ

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset
open scoped Classical
variable {V : Type uV} {I : Type uI} [DecidableEq V] [DecidableEq I] {h : ℕ}

omit [DecidableEq V] in
lemma distance_balls_disjoint (X : V → Fin h → ℝ) (u v : V) {r : ℝ}
    (hsep : 2*r ≤ l1dist (X u) (X v)) :
    Disjoint ((RadialShell.ball u r).support X) ((RadialShell.ball v r).support X) := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hx := l1dist_triangle (X u) z (X v)
  rw [l1dist_comm (X u) z] at hx
  have hz₁ := hz.2.1
  have hz₂ := hz'.2.1
  change l1dist z (X u) < r at hz₁
  change l1dist z (X v) < r at hz₂
  linarith

lemma l1_separated_net (X : V → Fin h → ℝ) (F : Finset V) (hF : F.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃S : Finset V, S ⊆ F ∧ S.Nonempty ∧
      (∀u ∈ S, ∀v ∈ S, u ≠ v → r < l1dist (X u) (X v)) ∧
      ∀u ∈ F, ∃v ∈ S, l1dist (X u) (X v) ≤ r := by
  let sep : Finset V → Prop := fun S => ∀u ∈ S, ∀v ∈ S, u ≠ v → r < l1dist (X u) (X v)
  let good := F.powerset.filter sep
  have hgood : good.Nonempty := ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),by simp [sep]⟩⟩
  obtain ⟨S,hS,hmax⟩ := exists_max_image good card hgood
  obtain ⟨hSF,hsep⟩ := mem_filter.mp hS
  have hcover : ∀u ∈ F, ∃v ∈ S, l1dist (X u) (X v) ≤ r := by
    intro u hu
    by_contra! hn
    have huS : u ∉ S := by
      intro huS
      have hh := hn u huS
      rw [l1dist_self] at hh
      linarith
    have hnew : insert u S ∈ good := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset hu (mem_powerset.mp hSF)),?_⟩
      intro x hx y hy hxy
      rcases mem_insert.mp hx with rfl | hxS
      · rcases mem_insert.mp hy with rfl | hyS
        · exact (hxy rfl).elim
        · exact hn y hyS
      · rcases mem_insert.mp hy with rfl | hyS
        · rw [l1dist_comm]; exact hn x hxS
        · exact hsep x hxS y hyS hxy
    have hh := hmax _ hnew
    rw [card_insert_of_notMem huS] at hh
    omega
  refine ⟨S,mem_powerset.mp hSF,?_,hsep,hcover⟩
  obtain ⟨u,hu⟩ := hF
  obtain ⟨v,hv,_⟩ := hcover u hu
  exact ⟨v,hv⟩

omit [DecidableEq V] in

lemma retain_fibers (S : Finset V) (T : Finset I) (f : V → I)
    (hf : ∀u ∈ S, f u ∈ T) (w : I → ℝ) (hw : ∀i ∈ T, 0 < w i)
    {c : ℝ} (hc : 0 < c) :
    ∃J : Finset I, J ⊆ T ∧
      (∀i ∈ J, (S.filter (fun u => f u=i)).Nonempty ∧
        c*w i ≤ ((S.filter (fun u => f u=i)).card : ℝ)) ∧
      (S.card : ℝ)-c*(∑i ∈ T, w i) ≤ ∑i ∈ J, ((S.filter (fun u => f u=i)).card : ℝ) := by
  let J := T.filter (fun i => c*w i ≤ ((S.filter (fun u => f u=i)).card : ℝ))
  have hsum : (∑i ∈ T, ((S.filter (fun u => f u=i)).card : ℝ)) = S.card := by
    rw [←Nat.cast_sum]
    congr 1
    exact sum_card_fiberwise_eq_card_filter S T f |>.trans (by
      congr 1
      exact filter_eq_self.mpr hf)
  refine ⟨J,filter_subset _ _,?_,?_⟩
  · intro i hi
    obtain ⟨hi,hci⟩ := mem_filter.mp hi
    refine ⟨card_pos.mp ?_,hci⟩
    have hh := mul_pos hc (hw i hi)
    have : (0:ℝ) < (S.filter (fun u => f u=i)).card := hh.trans_le hci
    exact_mod_cast this
  · have hbound : ∑i ∈ T, ((S.filter (fun u => f u=i)).card : ℝ) ≤
        (∑i ∈ T, if i ∈ J then ((S.filter (fun u => f u=i)).card : ℝ) else 0)+c*(∑i ∈ T, w i) := by
      rw [mul_sum,←sum_add_distrib]
      apply sum_le_sum
      intro i hi
      by_cases hiJ : i ∈ J
      · rw [ite_eq_left hiJ]
        linarith [mul_pos hc (hw i hi)]
      · rw [ite_eq_right hiJ,zero_add]
        exact le_of_lt (lt_of_not_ge (fun hh => hiJ (mem_filter.mpr ⟨hi,hh⟩)))
    rw [hsum] at hbound
    have he : (∑i ∈ T, if i ∈ J then ((S.filter (fun u => f u=i)).card : ℝ) else 0) =
        ∑i ∈ J, ((S.filter (fun u => f u=i)).card : ℝ) := by
      rw [←sum_filter]
      congr 1
      exact filter_mem_eq_inter.trans (inter_eq_right.mpr (filter_subset _ _))
    rw [he] at hbound
    linarith

end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry
noncomputable section
open Finset RadialShell
open scoped Classical
variable {V : Type uV2} [DecidableEq V] {h : ℕ} {X : V → Fin h → ℝ}

lemma compact_from_net (S W : Finset V) (hS : S.Nonempty) (hW : W.Nonempty)
    {δ D : ℝ} (hδ : 0 < δ) (hD : δ ≤ D)
    (hsep : (S : Set V).Pairwise (fun u v =>
      Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (hcover : ∀u ∈ S, ∃v ∈ W, l1dist (X u) (X v) ≤ 3*D)
    (hsmall : 432*D*(W.card : ℝ) ≤ δ*(S.card : ℝ)) :
    ∃F : CompactFamily X δ (6*D),
      δ*(S.card : ℝ)/2 ≤ δ*(∑B ∈ F.bags, (B.card : ℝ)) := by
  have hD0 : 0 < D := hδ.trans_le hD
  obtain ⟨w0,hw0⟩ := hW
  have hex : ∀u : V, ∃v ∈ W, u ∈ S → l1dist (X u) (X v) ≤ 3*D := by
    intro u
    by_cases hu : u ∈ S
    · obtain ⟨v,hv,hvu⟩ := hcover u hu
      exact ⟨v,hv,fun _ => hvu⟩
    · exact ⟨w0,hw0,fun hh => (hu hh).elim⟩
  choose f hfW hfDist using hex
  let fiber := fun i => S.filter (fun u => f u=i)
  let c : ℝ := 216*D/δ
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨J,hJW,hJ,hgain⟩ := retain_fibers S W f (fun u _ => hfW u)
    (fun _ => (1:ℝ)) (fun _ _ => zero_lt_one) hc
  have hsumRet : (∑i ∈ J, ((fiber i).card : ℝ)) ≥ (S.card : ℝ)/2 := by
    have hcost : c*(W.card : ℝ) ≤ (S.card : ℝ)/2 := by
      dsimp [c]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hδ).mpr
      linarith
    simp only [sum_const, nsmul_eq_mul,mul_one] at hgain
    dsimp [fiber]
    linarith
  have hJne : J.Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty.mp hh,sum_empty] at hsumRet
    have hs0 : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
    linarith
  have hinj : Set.InjOn fiber J := by
    intro i hi j hj hij
    obtain ⟨u,hu⟩ := (hJ i hi).1
    have huj : u ∈ fiber j := hij ▸ hu
    exact (mem_filter.mp hu).2.symm.trans (mem_filter.mp huj).2
  have hfiber : ∀i ∈ J, fiber i ⊆ S := fun i _ => filter_subset _ _
  let F : CompactFamily X δ (6*D) := {
    bags := J.image fiber
    nonempty := hJne.image fiber
    radius_pos := hδ
    bags_disjoint := by
      intro A hA B hB hAB
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hB
      apply Finset.disjoint_left.mpr
      intro u hui huj
      have hij := (mem_filter.mp hui).2.symm.trans (mem_filter.mp huj).2
      exact hAB (congrArg fiber hij)
    balls_disjoint := by
      intro u hu v hv huv
      obtain ⟨A,hA,huA⟩ := mem_biUnion.mp hu
      obtain ⟨B,hB,hvB⟩ := mem_biUnion.mp hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hB
      exact hsep (hfiber i hi huA) (hfiber j hj hvB) huv
    cardinal := by
      intro A hA
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      have hh := (hJ i hi).2
      have h216 : (216:ℝ) ≤ c := (le_div_iff₀ hδ).mpr (by linarith)
      have : (2:ℝ) ≤ (fiber i).card := by dsimp [fiber]; linarith
      exact_mod_cast this
    diameter := by
      intro A hA u hu v hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      have hui := (mem_filter.mp hu).2
      have hvi := (mem_filter.mp hv).2
      have hu' := hfDist u (hfiber i hi hu)
      have hv' := hfDist v (hfiber i hi hv)
      rw [hui] at hu'
      rw [hvi,l1dist_comm (X v) (X i)] at hv'
      have htri := l1dist_triangle (X u) (X i) (X v)
      linarith
    compact := by
      intro A hA
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hA
      have hh := (hJ i hi).2
      rw [mul_one] at hh
      have hm := (div_le_iff₀ hδ).mp hh
      linarith }
  refine ⟨F,?_⟩
  have he : (∑B ∈ F.bags, (B.card : ℝ)) = ∑i ∈ J, ((fiber i).card : ℝ) :=
    sum_image hinj
  rw [he]
  linarith [mul_le_mul_of_nonneg_left hsumRet hδ.le]

end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry
noncomputable section
open Finset RadialShell
open scoped Classical
variable {V : Type uV3} {I : Type uI2} {J : Type uJ} [DecidableEq V] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] {h : ℕ}

lemma normalized_small_balls (X : V → Fin h → ℝ) (Y : V → EuclideanSpace ℝ J)
    (u v : I → V) (j : I → J) (hj : Function.Injective j)
    (hN : 0 < Fintype.card I) {a ε c₁ : ℝ}
    (ha : 0 < a) (hε : 0 < ε) (hε1 : ε < 1/3) (hc : 0 < c₁)
    (hdiag : ∀i, 0 ≤ (Y (u i)-Y (v i)).ofLp (j i) ∧
      c₁ ≤ ((Y (u i)-Y (v i)).ofLp (j i))^2)
    (hbound : a * Fintype.card I * (∑i, ‖Y (u i)-Y (v i)‖^2) ≤
      (∑i, (Y (u i)-Y (v i)).ofLp (j i))^2)
    (hcontract : ∀x y, ‖Y x-Y y‖^2 ≤ l1dist (X x) (X y)) :
    a ≤ 1 ∧ ∃S : Finset V, ∃δ : ℝ, 0 < δ ∧
      S ⊆ (univ.image u ∪ univ.image v) ∧ 2 ≤ S.card ∧
      ε^2*a*Fintype.card I ≤ 1024*S.card ∧
      (S.card : ℝ)*δ = a^ε*c₁*Fintype.card I/(1024/ε^2) ∧
      (S : Set V).Pairwise (fun x y =>
        Disjoint ((ball x δ).support X) ((ball y δ).support X)) := by
  let N : ℝ := Fintype.card I
  let A : ℝ := ∑i, (Y (u i)-Y (v i)).ofLp (j i)
  have hN0 : 0 < N := by dsimp [N]; exact_mod_cast hN
  have hsqrt : ∀i, Real.sqrt c₁ ≤ (Y (u i)-Y (v i)).ofLp (j i) := by
    intro i
    exact (Real.sqrt_le_iff).mpr ⟨(hdiag i).1,(hdiag i).2⟩
  have hsum : N*Real.sqrt c₁ ≤ A := by
    simpa only [sum_const,nsmul_eq_mul,card_univ,N,A] using sum_le_sum (fun i (_ : i ∈ univ) => hsqrt i)
  have hA0 : 0 < A := (mul_pos hN0 (Real.sqrt_pos.mpr hc)).trans_le hsum
  have hA2 : c₁*N^2 ≤ A^2 := by
    have hh := sq_le_sq₀ (by positivity : 0 ≤ N*Real.sqrt c₁) hA0.le |>.mpr hsum
    rw [mul_pow,Real.sq_sqrt hc.le] at hh
    linarith
  obtain ⟨ha1,S,r,hr,hSF,hS2,hcard,hmass,hsep⟩ :=
    StrongThinTree.Spectral.spectral_packing_coordinates Y u v j hj ha hε hε1
      (by change 0 < A^2; positivity) hbound
  have hS0 : (0:ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have he2 : 0 < ε^2 := sq_pos_of_pos hε
  have hpow : 0 < a^ε := Real.rpow_pos_of_pos ha _
  let C : ℝ := 1024/ε^2
  have hC : 0 < C := by dsimp [C]; positivity
  let w := a^ε*c₁*N/C
  let δ := w/S.card
  have hw : 0 < w := by dsimp [w]; positivity
  have hδ : 0 < δ := div_pos hw hS0
  have hwle : w ≤ (S.card : ℝ)*r := by
    have hh := mul_le_mul_of_nonneg_left hA2 (show 0 ≤ ε^2*a^ε by positivity)
    change ε^2*a^ε*A^2 ≤ 1024*N*(S.card*r) at hmass
    have hh' : ε^2*a^ε*c₁*N ≤ 1024*(S.card*r) := by
      apply (mul_le_mul_iff_right₀ hN0).mp
      linarith
    dsimp [w,C]
    exact (div_le_iff₀ (div_pos (by norm_num) he2)).mpr (by
      rw [←mul_div_assoc]
      apply (le_div_iff₀ he2).mpr
      linarith)
  have hδr : δ ≤ r := (div_le_iff₀ hS0).mpr (by linarith)
  refine ⟨ha1,S,δ,hδ,hSF,hS2,hcard,?_,?_⟩
  · dsimp [δ,w,C,N]
    field_simp
  · intro x hx y hy hxy
    apply distance_balls_disjoint
    have hh := hsep x hx y hy hxy
    have hh' := hcontract x y
    have hs : (Real.sqrt r)^2 = r := Real.sq_sqrt hr.le
    have hnorm := norm_nonneg (Y x-Y y)
    have hroot := Real.sqrt_nonneg r
    nlinarith

end
end StrongThinTree.Geometry

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Hierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma cut_internal_split {A S : Finset (Fin n)} (hS : S ⊆ A) :
    ((G.inducedEdges A).card : ℝ) = (G.inducedEdges S).card+
      (G.inducedEdges (A\S)).card+(G.cut (G.inducedEdges A) S).card := by
  have heq : G.inducedEdges A = G.inducedEdges S ∪ G.inducedEdges (A\S) ∪ G.cut (G.inducedEdges A) S := by
    ext e
    simp only [mem_union,mem_inducedEdges,cut,mem_filter]
    simp only [mem_sdiff]
    constructor
    · intro h
      by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> tauto
    · intro h
      rcases h with ((h | h) | h)
      · exact ⟨hS h.1,hS h.2⟩
      · exact ⟨h.1.1,h.2.1⟩
      · exact h.1
  have hd : Disjoint (G.inducedEdges S) (G.inducedEdges (A\S)) := by
    rw [Finset.disjoint_left]
    intro e he hf
    rw [mem_inducedEdges] at he hf
    exact (mem_sdiff.mp hf.1).2 he.1
  have hd' : Disjoint (G.inducedEdges S ∪ G.inducedEdges (A\S)) (G.cut (G.inducedEdges A) S) := by
    rw [Finset.disjoint_left]
    intro e he hf
    have hc := (mem_filter.mp hf).2
    rcases mem_union.mp he with he | he
    · rw [mem_inducedEdges] at he
      tauto
    · rw [mem_inducedEdges] at he
      have hl := (mem_sdiff.mp he.1).2
      have hr := (mem_sdiff.mp he.2).2
      tauto
  have hc : (G.inducedEdges A).card = (G.inducedEdges S).card+
      (G.inducedEdges (A\S)).card+(G.cut (G.inducedEdges A) S).card := by
    conv_lhs => rw [heq]
    rw [card_union_of_disjoint hd',card_union_of_disjoint hd]
  exact_mod_cast hc

lemma vertexPartition_singleton {A : Finset (Fin n)} (hA : A.Nonempty) :
    VertexPartition A {A} := by
  refine ⟨?_,?_,by simp⟩
  · intro B hB
    have heq := mem_singleton.mp hB
    subst B
    exact ⟨hA,Subset.rfl⟩
  · intro B hB C hC hne
    exact (hne ((mem_singleton.mp hB).trans (mem_singleton.mp hC).symm)).elim

lemma vertexPartition_union {A B : Finset (Fin n)} {P Q : Finset (Finset (Fin n))}
    (hP : VertexPartition A P) (hQ : VertexPartition B Q) (hAB : Disjoint A B) :
    VertexPartition (A∪B) (P∪Q) ∧ Disjoint P Q := by
  have hd : ∀S ∈ P, ∀T ∈ Q, Disjoint S T := by
    intro S hS T hT
    exact hAB.mono (hP.1 S hS).2 (hQ.1 T hT).2
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro S hS hT
    obtain ⟨u,hu⟩ := (hP.1 S hS).1
    exact Finset.disjoint_left.mp (hd S hS S hT) hu hu
  refine ⟨⟨?_,?_,?_⟩,hPQ⟩
  · intro S hS
    rcases mem_union.mp hS with hS | hS
    · exact ⟨(hP.1 S hS).1,((hP.1 S hS).2).trans (subset_union_left)⟩
    · exact ⟨(hQ.1 S hS).1,((hQ.1 S hS).2).trans (subset_union_right)⟩
  · intro S hS T hT hne
    rcases mem_union.mp hS with hS | hS <;> rcases mem_union.mp hT with hT | hT
    · exact hP.2.1 hS hT hne
    · exact hd S hS T hT
    · exact (hd T hT S hS).symm
    · exact hQ.2.1 hS hT hne
  · rw [union_biUnion,hP.2.2,hQ.2.2]

lemma connected_partition (A : Finset (Fin n)) (hA : A.Nonempty) {q : ℝ} (_hq : 0 ≤ q) :
    ∃P : Finset (Finset (Fin n)), VertexPartition A P ∧
      (∀B ∈ P, G.EdgeConnectedReal B q) ∧
      ((G.inducedEdges A).card : ℝ)-(∑B ∈ P, ((G.inducedEdges B).card : ℝ)) ≤ q*((P.card : ℝ)-1) := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hconn : G.EdgeConnectedReal A q
    · exact ⟨{A},vertexPartition_singleton hA,by simpa,by simp⟩
    · obtain ⟨S,hSne,hSA,hcut⟩ : ∃S, S.Nonempty ∧ S ⊂ A ∧
          ((G.cut (G.inducedEdges A) S).card : ℝ) < q := by
        simp only [EdgeConnectedReal,not_forall,not_le] at hconn
        obtain ⟨S,hSne,hSA,hcut⟩ := hconn
        exact ⟨S,hSne,hSA,hcut⟩
      have hRA : A\S ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨sdiff_subset,?_⟩
        intro heq
        obtain ⟨u,hu⟩ := hSne
        have : u ∈ A\S := heq.symm ▸ hSA.subset hu
        exact (mem_sdiff.mp this).2 hu
      have hRne : (A\S).Nonempty := by
        apply sdiff_nonempty.mpr
        intro hh
        exact (Finset.ssubset_iff_subset_ne.mp hSA).2 (Subset.antisymm hSA.subset hh)
      obtain ⟨P,hP,hPc,hPb⟩ := ih S hSA hSne
      obtain ⟨Q,hQ,hQc,hQb⟩ := ih (A\S) hRA hRne
      obtain ⟨hPQ,hdis⟩ := vertexPartition_union hP hQ (disjoint_sdiff_self_right)
      have hcover : S ∪ (A\S) = A := union_sdiff_of_subset hSA.subset
      rw [hcover] at hPQ
      refine ⟨P∪Q,hPQ,?_,?_⟩
      · intro B hB
        rcases mem_union.mp hB with hB | hB
        · exact hPc B hB
        · exact hQc B hB
      · rw [sum_union hdis,card_union_of_disjoint hdis,Nat.cast_add]
        have he := G.cut_internal_split hSA.subset
        linarith

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma partition_point_mass {A : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hP : VertexPartition A P) (v : Fin n) :
    (∑B ∈ P, if v ∈ B then (1:ℝ) else 0) = if v ∈ A then (1:ℝ) else 0 := by
  by_cases hv : v ∈ A
  · obtain ⟨B,hB,hvB⟩ := mem_biUnion.mp (hP.2.2.symm ▸ hv)
    rw [ite_eq_left hv,sum_eq_single B]
    · exact ite_eq_left hvB
    · intro C hC hCB
      have hvC : v ∉ C := fun hh => Finset.disjoint_left.mp (hP.2.1 hC hB hCB) hh hvB
      simp [hvC]
    · exact fun hh => (hh hB).elim
  · rw [ite_eq_right hv]
    apply sum_eq_zero
    intro B hB
    exact ite_eq_right (fun hh => hv ((hP.1 B hB).2 hh))

lemma volume_partition {A R : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hP : VertexPartition A P) : (∑B ∈ P, G.volume R B) = G.volume R A := by
  simp only [volume]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  simp only [endpointMass,sum_add_distrib]
  rw [partition_point_mass hP,partition_point_mass hP]

lemma volume_eq_boundary {A B : Finset (Fin n)} (hBA : B ⊆ A) :
    G.volume A B = ((G.cut (G.inducedEdges A) B).card : ℝ)+2*(G.inducedEdges B).card := by
  have hcard (E : Finset (Fin m)) : (E.card : ℝ) = ∑e : Fin m, if e ∈ E then (1:ℝ) else 0 := by simp
  rw [hcard,hcard,mul_sum,← sum_add_distrib]
  simp only [volume,inducedEdges,sum_filter]
  apply sum_congr rfl
  intro e he
  simp only [endpointMass,cut,mem_filter,mem_univ,true_and]
  have hl := hBA (x := G.left e)
  have hr := hBA (x := G.right e)
  by_cases hlA : G.left e ∈ A <;> by_cases hrA : G.right e ∈ A <;>
    by_cases hlB : G.left e ∈ B <;> by_cases hrB : G.right e ∈ B <;>
      norm_num [*] at *

lemma cut_complement_in {A B : Finset (Fin n)} (_hBA : B ⊆ A) :
    G.cut (G.inducedEdges A) (A\B) = G.cut (G.inducedEdges A) B := by
  ext e
  simp only [cut,mem_filter,mem_inducedEdges,mem_sdiff]
  tauto

lemma outside_connected_partition {A T : Finset (Fin n)} {k : ℝ}
    (hk : 0 < k) (hconn : G.EdgeConnectedReal A k) (hT : T.Nonempty) (hTA : T ⊂ A) :
    ∃P : Finset (Finset (Fin n)), VertexPartition (A\T) P ∧
      (∀B ∈ P, G.EdgeConnectedReal B (k/4)) ∧
      (P.card : ℝ)*k ≤ 2*(G.cut (G.inducedEdges A) T).card := by
  have hR : (A\T).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hh
    exact (Finset.ssubset_iff_subset_ne.mp hTA).2 (Subset.antisymm hTA.subset hh)
  obtain ⟨P,hP,hPc,hcost⟩ := G.connected_partition (A\T) hR (by positivity : 0 ≤ k/4)
  have hBA : ∀B ∈ P, B ⊆ A := fun B hB => ((hP.1 B hB).2).trans sdiff_subset
  have hcuts : (P.card : ℝ)*k ≤ ∑B ∈ P, ((G.cut (G.inducedEdges A) B).card : ℝ) := by
    calc
      _ = ∑B ∈ P, k := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro B hB
        apply hconn B (hP.1 B hB).1
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hBA B hB,?_⟩
        intro heq
        obtain ⟨v,hv⟩ := hT
        have hh := (hP.1 B hB).2 (heq.symm ▸ hTA.subset hv)
        exact (mem_sdiff.mp hh).2 hv
  have hvol : (∑B ∈ P, ((G.cut (G.inducedEdges A) B).card : ℝ))+
      2*(∑B ∈ P, ((G.inducedEdges B).card : ℝ)) =
      ((G.cut (G.inducedEdges A) T).card : ℝ)+2*(G.inducedEdges (A\T)).card := by
    calc
      _ = ∑B ∈ P, G.volume A B := by
        rw [mul_sum,← sum_add_distrib]
        exact sum_congr rfl (fun B hB => (G.volume_eq_boundary (hBA B hB)).symm)
      _ = G.volume A (A\T) := G.volume_partition hP
      _ = _ := by rw [G.volume_eq_boundary sdiff_subset,G.cut_complement_in hTA.subset]
  refine ⟨P,hP,hPc,?_⟩
  linarith

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (G : MultiGraph n m)

lemma routed_variation_lower {R L : Finset (Fin n)} {q a b : ℝ}
    (f : Fin n → ℝ) (hab : a ≤ b) (hconn : G.EdgeConnectedReal R q)
    (hu : ∃u ∈ R, u ∈ L ∧ f u ≤ a) (hv : ∃v ∈ R, b ≤ f v)
    (hprotect : ∀e ∈ G.inducedEdges R,
      ((G.left e ∈ L ∧ G.right e ∉ L) ∨ (G.right e ∈ L ∧ G.left e ∉ L)) →
      b ≤ f (G.left e) ∧ b ≤ f (G.right e)) :
    q*(b-a) ≤ ∑e ∈ G.inducedEdges L,
      |clamp a b (f (G.left e))-clamp a b (f (G.right e))| := by
  have hh := cut_range_bound (k := q) (fun e : G.inducedEdges L => G.left e)
    (fun e : G.inducedEdges L => G.right e) (fun v => clamp a b (f v)) hab
  rw [← Finset.sum_coe_sort]
  apply hh
  intro t ht
  let S := R.filter (fun v => v ∈ L ∧ f v < t)
  have hSR : S ⊆ R := filter_subset _ _
  have hSn : S.Nonempty := by
    obtain ⟨u,huR,huL,hu⟩ := hu
    exact ⟨u,mem_filter.mpr ⟨huR,huL,lt_of_le_of_lt hu ht.1⟩⟩
  have hSproper : S ⊂ R := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSR,?_⟩
    intro heq
    obtain ⟨v,hvR,hv⟩ := hv
    have hh := (mem_filter.mp (heq.symm ▸ hvR)).2.2
    linarith [ht.2]
  have hc := hconn S hSn hSproper
  have hedge : ∀e ∈ G.cut (G.inducedEdges R) S, e ∈ G.inducedEdges L ∧
      ((f (G.left e)<t ∧ ¬ f (G.right e)<t) ∨
       (f (G.right e)<t ∧ ¬f (G.left e)<t)) := by
    intro e he
    obtain ⟨heR,hcut⟩ := mem_filter.mp he
    obtain ⟨hlR,hrR⟩ := (G.mem_inducedEdges _ _).mp heR
    rcases hcut with hcut | hcut
    · have hl := (mem_filter.mp hcut.1).2
      have hrL : G.right e ∈ L := by
        by_contra hh
        have hp := (hprotect e heR (Or.inl ⟨hl.1,hh⟩)).1
        linarith [ht.2,hl.2]
      have hr : ¬f (G.right e)<t := fun hh => hcut.2 (mem_filter.mpr ⟨hrR,hrL,hh⟩)
      exact ⟨(G.mem_inducedEdges _ _).mpr ⟨hl.1,hrL⟩,Or.inl ⟨hl.2,hr⟩⟩
    · have hr := (mem_filter.mp hcut.1).2
      have hlL : G.left e ∈ L := by
        by_contra hh
        have hp := (hprotect e heR (Or.inr ⟨hr.1,hh⟩)).2
        linarith [ht.2,hr.2]
      have hl : ¬f (G.left e)<t := fun hh => hcut.2 (mem_filter.mpr ⟨hlR,hlL,hh⟩)
      exact ⟨(G.mem_inducedEdges _ _).mpr ⟨hlL,hr.1⟩,Or.inr ⟨hr.2,hl⟩⟩
  have hcard : (G.cut (G.inducedEdges R) S).card ≤
      (univ.filter (fun e : G.inducedEdges L =>
      (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
      (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))).card := by
    let F (e : G.cut (G.inducedEdges R) S) :
        (univ.filter (fun e : G.inducedEdges L =>
          (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
          (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))) :=
      ⟨⟨e.val,(hedge e.val e.property).1⟩,by
        simp only [mem_filter,mem_univ,true_and,clamp_lt_iff ht]
        exact (hedge e.val e.property).2⟩
    apply Finset.card_le_card_of_injective (f := F)
    intro e f hh
    apply Subtype.ext
    exact congrArg (fun x => x.val.val) hh
  exact hc.trans (by exact_mod_cast hcard)

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Records
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n h : ℕ} (H : Hierarchy n)

lemma mem_domain {A B : Finset (Fin n)} {P : Finset (Finset (Fin n))} :
    B ∈ H.domain A P ↔ B ∈ H.nodes ∧ B ⊆ A ∧ ∀S ∈ P, ¬B ⊆ S := by
  simp [domain]

lemma mem_leaves {A : Finset (Fin n)} {P : Finset (Finset (Fin n))} {v : Fin n} :
    v ∈ H.leaves A P ↔ v ∈ A ∧ ∀S ∈ P, v ∉ S := by
  simp [leaves]

lemma root_mem_domain {A : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hA : A ∈ H.nodes) (hP : ∀S ∈ P, S ⊂ A) : A ∈ H.domain A P := by
  apply H.mem_domain.mpr
  refine ⟨hA,Subset.refl _,?_⟩
  intro S hS hh
  have hs := hP S hS
  exact (Finset.ssubset_iff_subset_ne.mp hs).2 (Subset.antisymm hs.subset hh)

lemma singleton_domain_iff {A : Finset (Fin n)} {P : Finset (Finset (Fin n))} {v : Fin n} :
    {v} ∈ H.domain A P ↔ v ∈ H.leaves A P := by
  simp only [mem_domain,H.singletons,true_and,singleton_subset_iff,mem_leaves]

lemma domain_root_test {A B : Finset (Fin n)} {P Q : Finset (Finset (Fin n))}
    (hA : A ∈ H.nodes) (hB : B ∈ H.nodes)
    (hP : ∀S ∈ P, S ⊂ A) (hQ : ∀S ∈ Q, S ⊂ B) :
    (H.domain A P ∩ H.domain B Q).Nonempty ↔
      A ∈ H.domain B Q ∨ B ∈ H.domain A P := by
  constructor
  · rintro ⟨C,hC⟩
    obtain ⟨hCA,hCB⟩ := mem_inter.mp hC
    obtain ⟨hCnode,hCA,hCP⟩ := H.mem_domain.mp hCA
    obtain ⟨_,hCB,hCQ⟩ := H.mem_domain.mp hCB
    rcases H.laminar A hA B hB with hAB | hBA | hdis
    · left
      apply H.mem_domain.mpr
      exact ⟨hA,hAB,fun S hS hh => hCQ S hS (hCA.trans hh)⟩
    · right
      apply H.mem_domain.mpr
      exact ⟨hB,hBA,fun S hS hh => hCP S hS (hCB.trans hh)⟩
    · obtain ⟨v,hv⟩ := H.nonempty C hCnode
      exact (Finset.disjoint_left.mp hdis (hCA hv) (hCB hv)).elim
  · rintro (hAB | hBA)
    · exact ⟨A,mem_inter.mpr ⟨H.root_mem_domain hA hP,hAB⟩⟩
    · exact ⟨B,mem_inter.mpr ⟨hBA,H.root_mem_domain hB hQ⟩⟩

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry

namespace Record
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

lemma root_mem {B : Record n} (hB : B.Shape H) : B.owner ∈ B.conflict H :=
  H.root_mem_domain hB.1 (fun S hS => (hB.2 S hS).2)

lemma mem_leafSet {B : Record n} {v : Fin n} :
    v ∈ B.leafSet H ↔ v ∈ B.owner ∧ ∀S ∈ B.excluded, v ∉ S := H.mem_leaves

lemma mem_routing {B : Record n} {v : Fin n} :
    v ∈ B.routing ↔ v ∈ B.owner ∧ ∀S ∈ B.avoided.toFinset, v ∉ S := by
  cases heq : B.avoided <;> simp [routing,heq]

lemma protected_routing_edges {B : Record n} (hB : B.Protected G X)
    {R : Finset (Fin n)} (hR : R ⊆ B.routing) :
    ∀e ∈ G.inducedEdges R,
      ((G.left e ∈ B.leafSet H ∧ G.right e ∉ B.leafSet H) ∨
       (G.right e ∈ B.leafSet H ∧ G.left e ∉ B.leafSet H)) →
      B.shell.outer ≤ l1dist (X (G.left e)) (X B.shell.center) ∧
      B.shell.outer ≤ l1dist (X (G.right e)) (X B.shell.center) := by
  have hex {u v : Fin n} (hu : u ∈ B.leafSet H) (hv : v ∈ B.routing)
      (hn : v ∉ B.leafSet H) : ∃S ∈ B.predecessors, u ∉ S ∧ v ∈ S := by
    obtain ⟨hu,hup⟩ := (mem_leafSet H).mp hu
    obtain ⟨hv,hva⟩ := mem_routing.mp hv
    have : ∃S ∈ B.excluded, v ∈ S := by
      by_contra hh
      push Not at hh
      exact hn ((mem_leafSet H).mpr ⟨hv,hh⟩)
    obtain ⟨S,hS,hvS⟩ := this
    have hSp : S ∈ B.predecessors := by
      rcases mem_union.mp hS with hh | hh
      · exact hh
      · exact (hva S hh hvS).elim
    exact ⟨S,hSp,hup S hS,hvS⟩
  intro e he hcross
  obtain ⟨hlR,hrR⟩ := (G.mem_inducedEdges _ _).mp he
  rcases hcross with hcross | hcross
  · obtain ⟨S,hS,hl,hr⟩ := hex hcross.1 (hR hrR) hcross.2
    exact hB S hS e (mem_filter.mpr ⟨mem_univ _,Or.inr ⟨hr,hl⟩⟩)
  · obtain ⟨S,hS,hr,hl⟩ := hex hcross.1 (hR hlR) hcross.2
    exact hB S hS e (mem_filter.mpr ⟨mem_univ _,Or.inl ⟨hl,hr⟩⟩)

lemma variation_lower {q : ℝ} {B : Record n} (hB : B.Valid H G X q) :
    q*B.shell.width ≤ ∑e ∈ G.inducedEdges (B.leafSet H),
      |clamp B.shell.inner B.shell.outer (l1dist (X (G.left e)) (X B.shell.center))-
       clamp B.shell.inner B.shell.outer (l1dist (X (G.right e)) (X B.shell.center))| := by
  obtain ⟨R,hR,hconn,hu,hv⟩ := hB.2.2.2
  exact G.routed_variation_lower _ hB.2.2.1.2.1.le hconn hu hv
    (protected_routing_edges H G X hB.2.1 hR)

lemma restrict_valid {q a b : ℝ} {B : Record n} (hB : B.Valid H G X q)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) (hab : a < b) :
    ({B with shell := RadialShell.hollow B.shell.center a b}).Valid H G X q := by
  refine ⟨hB.1,?_,?_,?_⟩
  · intro S hS e he
    exact ⟨hb.trans (hB.2.1 S hS e he).1,hb.trans (hB.2.1 S hS e he).2⟩
  · obtain ⟨u,hu⟩ := hB.2.2.1.2.2.2.1
    obtain ⟨v,hv⟩ := hB.2.2.1.2.2.2.2
    exact ⟨hB.2.2.1.1.trans ha,hab,by simp [RadialShell.hollow],⟨u,hu.trans ha⟩,⟨v,hb.trans hv⟩⟩
  · obtain ⟨R,hR,hconn,⟨u,huR,huL,hu⟩,⟨v,hvR,hv⟩⟩ := hB.2.2.2
    exact ⟨R,hR,hconn,⟨u,huR,huL,hu.trans ha⟩,⟨v,hvR,hb.trans hv⟩⟩

end Record
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

lemma labeled_energy {q : ℝ} (hX : ∀v, binary (X v)) {Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) :
    q*(∑B ∈ Z, B.shell.width) ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  let f (B : Record n) (e : Fin m) :=
    |clamp B.shell.inner B.shell.outer (l1dist (X (G.left e)) (X B.shell.center))-
     clamp B.shell.inner B.shell.outer (l1dist (X (G.right e)) (X B.shell.center))|
  calc
    _ = ∑B ∈ Z, q*B.shell.width := mul_sum _ _ _
    _ ≤ ∑B ∈ Z, ∑e ∈ G.inducedEdges (B.leafSet H), f B e :=
      sum_le_sum (fun B hB => B.variation_lower H G X (hZ.1 B hB))
    _ = ∑e : Fin m, ∑B ∈ Z.filter (fun B => e ∈ G.inducedEdges (B.leafSet H)), f B e := by
      simp only [inducedEdges,sum_filter,mem_filter,mem_univ,true_and]
      rw [sum_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro e he
      let W := Z.filter (fun B => e ∈ G.inducedEdges (B.leafSet H))
      rw [← Finset.sum_coe_sort]
      apply binary_shell_edge_bound (binary_cube (hX _)) (binary_cube (hX _))
        (fun B : W => X B.val.shell.center) (fun B => hX _) _ _
      · intro B
        exact (hZ.1 B.val (mem_filter.mp B.property).1).2.2.1.2.1.le
      · intro B D hBD w hw hbad
        have hB : B.val ∈ Z := (mem_filter.mp B.property).1
        have hD : D.val ∈ Z := (mem_filter.mp D.property).1
        have hinter : ¬Disjoint (B.val.shell.support X) (D.val.shell.support X) := by
          intro hh
          exact Set.disjoint_left.mp hh ⟨hw,hbad.2.1,Or.inr hbad.1⟩
            ⟨hw,hbad.2.2.2,Or.inr hbad.2.2.1⟩
        have hdis := hZ.2 hB hD (fun hh => hBD (Subtype.ext hh)) hinter
        have hlB := ((G.mem_inducedEdges _ _).mp (mem_filter.mp B.property).2).1
        have hlD := ((G.mem_inducedEdges _ _).mp (mem_filter.mp D.property).2).1
        have hmB : {G.left e} ∈ B.val.conflict H := H.singleton_domain_iff.mpr hlB
        have hmD : {G.left e} ∈ D.val.conflict H := H.singleton_domain_iff.mpr hlD
        exact Finset.disjoint_left.mp hdis hmB hmD

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

lemma parent_boundary_lower {q : ℝ} (hconn : H.LocallyConnectedReal G q)
    {A : Finset (Fin n)} (hA : A ∈ H.nodes) (hne : A ≠ univ) :
    q ≤ (H.parentBoundary G A).card :=
  hconn (H.parent A) (H.parent_mem A hA hne) A (H.nonempty A hA)
    (H.parent_strict A hA hne)

namespace AssignedBag
variable {H G X} {δ η : ℝ} (A : H.AssignedBag G X δ η)

lemma input_leaf {P : Finset (Finset (Fin n))} (hP : ∀S ∈ P, S ⊂ A.owner)
    {u : Fin n} (hu : u ∈ A.centers) (hins : (A.input P u).Protected G X) :
    u ∈ (A.input P u).leafSet H := by
  apply (Record.mem_leafSet H).mpr
  refine ⟨(A.endpoint u hu).1,?_⟩
  intro S hS huS
  have hSP : S ∈ P := by simpa [Record.excluded,input] using hS
  obtain ⟨e,he,heu,hlen⟩ := (A.endpoint u hu).2
  have he' := (mem_filter.mp he).2
  have hcut : e ∈ G.cut univ S := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases he' with hh | hh
    · have hright : G.right e ∉ S := fun hs => hh.2 ((hP S hSP).subset hs)
      rcases heu with heu | heu
      · exact Or.inl ⟨heu.symm ▸ huS,hright⟩
      · exact (hright (heu.symm ▸ huS)).elim
    · have hleft : G.left e ∉ S := fun hs => hh.2 ((hP S hSP).subset hs)
      rcases heu with heu | heu
      · exact (hleft (heu.symm ▸ huS)).elim
      · exact Or.inr ⟨heu.symm ▸ huS,hleft⟩
  have hp := hins S hSP e hcut
  rcases heu with heu | heu
  · have hp := hp.1
    change δ ≤ l1dist (X (G.left e)) (X u) at hp
    rw [heu,l1dist_self] at hp
    linarith [A.radius_pos]
  · have hp := hp.2
    change δ ≤ l1dist (X (G.right e)) (X u) at hp
    rw [heu,l1dist_self] at hp
    linarith [A.radius_pos]

lemma input_valid (hX : ∀v, binary (X v)) {q : ℝ} (_hq : 0 ≤ q)
    (hconn : H.LocallyConnectedReal G q) (hsize : 1 < A.centers.card)
    {P : Finset (Finset (Fin n))} (hP : ∀S ∈ P, S ∈ H.nodes ∧ S ⊂ A.owner)
    {u : Fin n} (hu : u ∈ A.centers) (hins : (A.input P u).Protected G X) :
    (A.input P u).Valid H G X (q/4) := by
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne hsize u
  have hdist := RadialShell.disjoint_balls_distance hX u v (A.disjoint hu hv hvu.symm)
  have houter : δ ≤ l1dist (X v) (X u) := by
    rw [l1dist_comm]
    linarith [A.radius_pos]
  refine ⟨?_,hins,?_,?_⟩
  · refine ⟨A.owner_mem,?_⟩
    intro S hS
    exact hP S (by simpa [input,Record.excluded] using hS)
  · exact ⟨le_refl 0,A.radius_pos,by simp [input,RadialShell.ball],
      ⟨u,by simp [input,RadialShell.ball,l1dist_self]⟩,⟨v,houter⟩⟩
  · refine ⟨A.owner,?_,?_,⟨u,(A.endpoint u hu).1,A.input_leaf (fun S hS => (hP S hS).2) hu hins,?_⟩,
      ⟨v,(A.endpoint v hv).1,houter⟩⟩
    · simp [input,Record.routing]
    · intro S hS hSA
      have hh := hconn A.owner A.owner_mem S hS hSA
      linarith
    · simp [input,RadialShell.ball,l1dist_self]

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Partitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n)

lemma predecessor_dichotomy {A t : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (ht : t ∈ H.domain A P) (hP : ∀S ∈ P, S ∈ H.nodes)
    {S : Finset (Fin n)} (hS : S ∈ P) : S ⊂ t ∨ Disjoint S t := by
  obtain ⟨htn,hta,htP⟩ := H.mem_domain.mp ht
  rcases H.laminar S (hP S hS) t htn with hSt | htS | hdis
  · left
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSt,?_⟩
    intro heq
    exact htP S hS (heq ▸ Subset.refl _)
  · exact (htP S hS htS).elim
  · exact Or.inr hdis

lemma domain_descendant_partition {A t : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (ht : t ∈ H.domain A P) (hP : ∀S ∈ P, S ∈ H.nodes) :
    H.domain t (P.filter (fun S => S ⊂ t)) =
      (H.domain A P).filter (fun C => C ⊆ t) := by
  obtain ⟨htn,htA,htP⟩ := H.mem_domain.mp ht
  ext C
  simp only [mem_filter,mem_domain]
  constructor
  · rintro ⟨hCn,hCt,hCP⟩
    refine ⟨⟨hCn,hCt.trans htA,?_⟩,hCt⟩
    intro S hS hCS
    rcases H.predecessor_dichotomy ht hP hS with hSt | hdis
    · exact hCP S ⟨hS,hSt⟩ hCS
    · obtain ⟨v,hv⟩ := H.nonempty C hCn
      exact Finset.disjoint_left.mp hdis (hCS hv) (hCt hv)
  · rintro ⟨⟨hCn,hCA,hCP⟩,hCt⟩
    exact ⟨hCn,hCt,fun S hS => hCP S hS.1⟩

lemma domain_avoid_partition (A t : Finset (Fin n)) (P : Finset (Finset (Fin n))) :
    H.domain A (insert t P) = (H.domain A P).filter (fun C => ¬C ⊆ t) := by
  ext C
  simp only [mem_domain,mem_filter,mem_insert]
  constructor
  · rintro ⟨hCn,hCA,hCP⟩
    exact ⟨⟨hCn,hCA,fun S hS => hCP S (Or.inr hS)⟩,hCP t (Or.inl rfl)⟩
  · rintro ⟨⟨hCn,hCA,hCP⟩,hCt⟩
    exact ⟨hCn,hCA,fun S hS => by rcases hS with rfl | hS; exact hCt; exact hCP S hS⟩

namespace Record
variable (G : MultiGraph n m) (X : Fin n → Fin h → ℝ)

lemma central_conflict {B : Record n} (hshape : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) (a b c d : ℝ) :
    (B.innerRecord t a b).conflict H = (B.conflict H).filter (fun C => C ⊆ t) ∧
    (B.outsideRecord t c d).conflict H = (B.conflict H).filter (fun C => ¬C ⊆ t) := by
  have heq : B.excluded = B.predecessors := by simp [excluded,hno]
  have hP : ∀S ∈ B.predecessors, S ∈ H.nodes := fun S hS => (hshape.2 S (heq.symm ▸ hS)).1
  have ht' : t ∈ H.domain B.owner B.predecessors := by simpa only [conflict,heq] using ht
  constructor
  · simpa only [conflict,innerRecord,excluded,Option.toFinset_none,union_empty,hno] using
      H.domain_descendant_partition ht' hP
  · simpa only [conflict,outsideRecord,excluded,Option.toFinset_some,union_singleton,hno,Option.toFinset_none,union_empty] using
      H.domain_avoid_partition B.owner t B.predecessors

lemma central_domain_disjoint {B : Record n} (hshape : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) (a b c d : ℝ) :
    Disjoint ((B.innerRecord t a b).conflict H) ((B.outsideRecord t c d).conflict H) := by
  obtain ⟨h1,h2⟩ := central_conflict H hshape hno ht a b c d
  rw [h1,h2,Finset.disjoint_left]
  intro C hC hD
  exact (mem_filter.mp hD).2 (mem_filter.mp hC).2

lemma protected_same_side {B : Record n} (hB : B.Protected G X)
    {u v : Fin n} {e : Fin m}
    (he : (G.left e = u ∧ G.right e = v) ∨ (G.left e = v ∧ G.right e = u))
    (hu : l1dist (X u) (X B.shell.center) < B.shell.outer) :
    ∀S ∈ B.predecessors, u ∈ S ↔ v ∈ S := by
  intro S hS
  have hn : e ∉ G.cut univ S := by
    intro hc
    have hh := hB S hS e hc
    rcases he with he | he
    · rw [he.1] at hh
      linarith [hh.1]
    · rw [he.2] at hh
      linarith [hh.2]
  simp only [cut,mem_filter,mem_univ,true_and] at hn
  rcases he with he | he <;> simp only [he.1,he.2] at hn <;> tauto

lemma central_valid {q a b δ : ℝ} {B : Record n}
    (hB : B.Valid H G X (q/4)) (hno : B.avoided = none)
    (hq : 0 ≤ q) (hconn : H.LocallyConnectedReal G q)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) (htstrict : t ⊂ B.owner)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hδ : 0 < δ) (hab : a+δ < b-δ)
    {R : Finset (Fin n)} (hR : R ⊆ H.parent t \ t)
    (hRc : G.EdgeConnectedReal R (q/4))
    {u₁ u₂ v₁ v₂ : Fin n} (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t)
    (hv₁ : v₁ ∈ R) (hv₂ : v₂ ∈ R)
    (hu₁rad : l1dist (X u₁) (X B.shell.center) ≤ a+δ)
    (hu₂rad : b-δ ≤ l1dist (X u₂) (X B.shell.center))
    (hv₁rad : l1dist (X v₁) (X B.shell.center) ≤ a)
    (hv₂rad : b ≤ l1dist (X v₂) (X B.shell.center))
    {e : Fin m} (he : (G.left e = u₁ ∧ G.right e = v₁) ∨
      (G.left e = v₁ ∧ G.right e = u₁)) :
    (B.innerRecord t (a+δ) (b-δ)).Valid H G X (q/4) ∧
    (B.outsideRecord t a b).Valid H G X (q/4) := by
  have htn := (H.mem_domain.mp ht).1
  have htne : t ≠ univ := by
    intro hh
    have := htstrict.not_subset (by simp [hh])
    exact this
  have hparent : H.parent t ⊆ B.owner :=
    H.parent_minimal t htn htne B.owner hB.1.1 htstrict
  have hp : ∀S ∈ B.predecessors, S ∈ H.nodes ∧ S ⊂ B.owner :=
    fun S hS => hB.1.2 S (mem_union_left _ hS)
  have htex : t ∈ H.domain B.owner B.predecessors := by
    simpa only [conflict,excluded,hno,Option.toFinset_none,union_empty] using ht
  have hv₁out : v₁ ∉ t := (mem_sdiff.mp (hR hv₁)).2
  have hsame : ∀S ∈ B.predecessors, u₁ ∈ S ↔ v₁ ∈ S :=
    protected_same_side G X hB.2.1 he (by linarith)
  have huvavoid : ∀S ∈ B.predecessors, u₁ ∉ S ∧ v₁ ∉ S := by
    intro S hS
    rcases H.predecessor_dichotomy htex (fun S hS => (hp S hS).1) hS with hSt | hdis
    · have hvS : v₁ ∉ S := fun hh => hv₁out (hSt.subset hh)
      exact ⟨fun hh => hvS ((hsame S hS).mp hh),hvS⟩
    · have huS : u₁ ∉ S := fun hh => Finset.disjoint_left.mp hdis hh hu₁
      exact ⟨huS,fun hh => huS ((hsame S hS).mpr hh)⟩
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · refine ⟨htn,?_⟩
      intro S hS
      have hS' : S ∈ B.predecessors ∧ S ⊂ t := by
        simpa [excluded,innerRecord] using hS
      exact ⟨(hp S hS'.1).1,hS'.2⟩
    · intro S hS e he
      have hS' : S ∈ B.predecessors := (mem_filter.mp hS).1
      have hh := hB.2.1 S hS' e he
      exact ⟨(by dsimp [innerRecord,RadialShell.hollow]; linarith [hh.1]),
        (by dsimp [innerRecord,RadialShell.hollow]; linarith [hh.2])⟩
    · refine ⟨?_,hab,by simp [innerRecord,RadialShell.hollow],⟨u₁,hu₁rad⟩,⟨u₂,hu₂rad⟩⟩
      dsimp [innerRecord,RadialShell.hollow]
      linarith [hB.2.2.1.1]
    · refine ⟨t,?_,?_,⟨u₁,hu₁,?_,hu₁rad⟩,⟨u₂,hu₂,hu₂rad⟩⟩
      · simp [routing,innerRecord]
      · intro S hSn hSt
        exact (by linarith : q/4 ≤ q).trans (hconn t htn S hSn hSt)
      · apply (mem_leafSet H).mpr
        refine ⟨hu₁,?_⟩
        intro S hS
        have hS' : S ∈ B.predecessors ∧ S ⊂ t := by
          simpa [excluded,innerRecord] using hS
        exact (huvavoid S hS'.1).1
  · refine ⟨?_,?_,?_,?_⟩
    · refine ⟨hB.1.1,?_⟩
      intro S hS
      have hS' : S ∈ B.predecessors ∨ S = t := by
        simpa [excluded,outsideRecord,or_comm] using hS
      rcases hS' with hS | rfl
      · exact hp S hS
      · exact ⟨htn,htstrict⟩
    · intro S hS e he
      have hh := hB.2.1 S hS e he
      exact ⟨hb.trans hh.1,hb.trans hh.2⟩
    · refine ⟨?_,?_,by simp [outsideRecord,RadialShell.hollow],⟨v₁,hv₁rad⟩,⟨v₂,hv₂rad⟩⟩
      · exact hB.2.2.1.1.trans ha
      · dsimp [outsideRecord,RadialShell.hollow]
        linarith
    · refine ⟨R,?_,hRc,⟨v₁,hv₁,?_,hv₁rad⟩,⟨v₂,hv₂,hv₂rad⟩⟩
      · intro v hv
        obtain ⟨hvA,hvt⟩ := mem_sdiff.mp (hR hv)
        exact mem_sdiff.mpr ⟨hparent hvA,hvt⟩
      · apply (mem_leafSet H).mpr
        refine ⟨hparent (mem_sdiff.mp (hR hv₁)).1,?_⟩
        intro S hS
        have hS' : S ∈ B.predecessors ∨ S = t := by
          simpa [excluded,outsideRecord,or_comm] using hS
        rcases hS' with hS | rfl
        · exact (huvavoid S hS).2
        · exact hv₁out

end Record
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

lemma compatible_symm {B D : Record n} (h : B.Compatible H X D) : D.Compatible H X B :=
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

lemma compatible_self_iff (B : Record n) (hX : ∀v, binary (X v))
    (hshape : B.Shape H) (hvalid : B.shell.Valid X) : ¬B.Compatible H X B := by
  intro hh
  rcases hh with hh | hh
  · obtain ⟨w,hw⟩ := RadialShell.valid_support_nonempty hX hvalid
    exact Set.disjoint_left.mp hh hw hw
  · exact Finset.disjoint_left.mp hh (B.root_mem H hshape) (B.root_mem H hshape)

lemma compatible_heredity {B D C : Record n} (hBD : B.Compatible H X D)
    (hCB : C.shell.support X ⊆ B.shell.support X) (hCC : C.conflict H ⊆ B.conflict H) :
    C.Compatible H X D := by
  rcases hBD with hBD | hBD
  · exact Or.inl (hBD.mono_left hCB)
  · exact Or.inr (hBD.mono_left hCC)

lemma candidate_ancestor {A B : Record n} (hA : A.Shape H) (hB : B.Shape H)
    (horder : B.owner ⊂ A.owner → B.owner ∈ A.excluded)
    (hinter : (A.conflict H ∩ B.conflict H).Nonempty) : A.owner ∈ B.conflict H := by
  have hroots := (H.domain_root_test hA.1 hB.1
    (fun S hS => (hA.2 S hS).2) (fun S hS => (hB.2 S hS).2)).mp hinter
  rcases hroots with hh | hh
  · exact hh
  · have hba := (H.mem_domain.mp hh).2.1
    by_cases heq : B.owner = A.owner
    · exact heq ▸ B.root_mem H hB
    · have hs := horder (Finset.ssubset_iff_subset_ne.mpr ⟨hba,heq⟩)
      exact ((H.mem_domain.mp hh).2.2 B.owner hs (Subset.refl _)).elim

lemma insert_compatible {q : ℝ} {Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) {A B D : Record n}
    (hA : A.Shape H) (hB : B ∈ Z) (hD : D ∈ Z) (hne : B ≠ D)
    (hBA : A.owner ∈ B.conflict H)
    (horder : ∀F ∈ Z, F.owner ⊂ A.owner → F.owner ∈ A.excluded)
    (hAB : A.shell.support X ⊆ B.shell.support X) : A.Compatible H X D := by
  by_cases hgeo : Disjoint (A.shell.support X) (D.shell.support X)
  · exact Or.inl hgeo
  right
  by_contra hh
  have hinter : (A.conflict H ∩ D.conflict H).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hh (Finset.disjoint_iff_inter_eq_empty.mpr hempty)
  have hDA := candidate_ancestor H hA (hZ.1 D hD).1 (horder D hD) hinter
  have hBD : ¬Disjoint (B.shell.support X) (D.shell.support X) :=
    fun hd => hgeo (hd.mono_left hAB)
  exact Finset.disjoint_left.mp (hZ.2 hB hD hne hBD) hBA hDA

lemma interior_restriction {C δ : ℝ} {A B D : Record n}
    (hcenter : D.shell.center = B.shell.center)
    (ha : B.shell.inner ≤ D.shell.inner) (hb : D.shell.outer ≤ B.shell.outer)
    (hdom : D.conflict H ⊆ B.conflict H) (hh : A.Interior H X C δ D) :
    A.Interior H X C δ B := by
  obtain ⟨⟨S,hS⟩,hl,hr⟩ := hh
  rw [hcenter] at hl hr
  exact ⟨⟨S,mem_inter.mpr ⟨(mem_inter.mp hS).1,hdom (mem_inter.mp hS).2⟩⟩,
    by linarith,by linarith⟩

lemma not_interior_ball {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 ≤ δ)
    (A B : Record n) (hw : B.shell.width ≤ δ) : ¬A.Interior H X C δ B := by
  rintro ⟨_,hl,hr⟩
  unfold RadialShell.width at hw
  have := mul_le_mul_of_nonneg_right hC hδ
  linarith

end Record

lemma labeled_empty (q : ℝ) : H.LabeledArrangement G X q ∅ := by simp [LabeledArrangement]

lemma labeled_subset {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) (hW : W ⊆ Z) :
    H.LabeledArrangement G X q W :=
  ⟨fun B hB => hZ.1 B (hW hB),fun _ hB _ hD hne => hZ.2 (hW hB) (hW hD) hne⟩

lemma labeled_pair {q : ℝ} {Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) {B D : Record n}
    (hB : B ∈ Z) (hD : D ∈ Z) (hne : B ≠ D) : B.Compatible H X D := by
  by_cases hh : Disjoint (B.shell.support X) (D.shell.support X)
  · exact Or.inl hh
  · exact Or.inr (hZ.2 hB hD hne hh)

lemma labeled_union {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) (hW : H.LabeledArrangement G X q W)
    (hZW : ∀B ∈ Z, ∀D ∈ W, B.Compatible H X D) :
    H.LabeledArrangement G X q (Z∪W) := by
  constructor
  · intro B hB
    exact (mem_union.mp hB).elim (hZ.1 B) (hW.1 B)
  · intro B hB D hD hne hgeo
    rcases mem_union.mp hB with hB | hB <;> rcases mem_union.mp hD with hD | hD
    · exact hZ.2 hB hD hne hgeo
    · exact (hZW B hB D hD).resolve_left hgeo
    · exact (Record.compatible_symm H X (hZW D hD B hB)).resolve_left hgeo
    · exact hW.2 hB hD hne hgeo

lemma labeled_sets_disjoint (hX : ∀v, binary (X v)) {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z)
    (hZW : ∀B ∈ Z, ∀D ∈ W, B.Compatible H X D) : Disjoint Z W := by
  rw [Finset.disjoint_left]
  intro B hB hBW
  exact B.compatible_self_iff H X hX (hZ.1 B hB).1 (hZ.1 B hB).2.2.1 (hZW B hB B hBW)

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

lemma restriction_refines (B : Record n) {a b : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) :
    (B.restriction a b).Refines H X B :=
  ⟨RadialShell.restriction_subset X B.shell ha hb,Subset.refl _⟩

lemma compatible_refinements {A B C D : Record n}
    (hBD : B.Compatible H X D) (hAB : A.Refines H X B) (hCD : C.Refines H X D) :
    A.Compatible H X C := by
  have hh := compatible_heredity H X hBD hAB.1 hAB.2
  have hh' := compatible_heredity H X (compatible_symm H X hh) hCD.1 hCD.2
  exact compatible_symm H X hh'

end Record

lemma labeled_replace {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) (hW : H.LabeledArrangement G X q W)
    (B : Record n) (hcompat : ∀D ∈ Z.erase B, ∀A ∈ W, D.Compatible H X A) :
    H.LabeledArrangement G X q (Z.erase B∪W) :=
  H.labeled_union G X (H.labeled_subset G X hZ (erase_subset _ _)) hW hcompat

lemma replacement_credit (hX : ∀v, binary (X v)) {q : ℝ} {Z W : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) {B : Record n} (hB : B ∈ Z)
    (hcompat : ∀D ∈ Z.erase B, ∀A ∈ W, D.Compatible H X A)
    (p : Record n → ℝ) {c : ℝ} (hcredit : p B+c ≤ ∑A ∈ W, p A) :
    (∑D ∈ Z, p D)+c ≤ ∑D ∈ Z.erase B∪W, p D := by
  have hdis := H.labeled_sets_disjoint G X hX
    (H.labeled_subset G X hZ (erase_subset B Z)) hcompat
  rw [sum_union hdis]
  have hh := sum_erase_add Z p hB
  linarith

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Selection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uU uI

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset
variable {h : ℕ}

lemma binary_antipode {x : Fin h → ℝ} (hx : binary x) : binary (antipode x) := by
  intro j
  rcases hx j with hh | hh <;> simp [antipode,hh]

lemma radial_complement {x z : Fin h → ℝ} (hx : binary x) (hz : cube z) :
    l1dist z x+l1dist z (antipode x) = h := by
  rw [l1dist,l1dist,← sum_add_distrib]
  calc
    _ = ∑j : Fin h, (1:ℝ) := by
      apply sum_congr rfl
      intro j hj
      rcases hx j with hh | hh
      · simp only [hh,antipode,sub_zero,abs_of_nonneg (hz j).1,
          abs_of_nonpos (by linarith [(hz j).2] : z j-1 ≤ 0)]
        ring
      · simp only [hh,antipode,sub_self,sub_zero,abs_of_nonneg (hz j).1,
          abs_of_nonpos (by linarith [(hz j).2] : z j-1 ≤ 0)]
        ring
    _ = h := by simp

lemma radial_max {x z : Fin h → ℝ} (hx : binary x) (hz : cube z) :
    l1dist z x ≤ h := by
  have hh := radial_complement hx hz
  linarith [l1dist_nonneg z (antipode x)]

lemma binary_radial_move {x z : Fin h → ℝ} (hx : binary x) (hz : binary z)
    {r : ℝ} (hr : 0 ≤ r) (hrmax : r ≤ h) :
    ∃w : Fin h → ℝ, cube w ∧ l1dist w x = r ∧ l1dist w z = |r-l1dist z x| := by
  let R := l1dist z x
  by_cases heq : r = R
  · exact ⟨z,binary_cube hz,heq.symm,by rw [heq]; simp [R,l1dist_self]⟩
  rcases lt_or_gt_of_ne heq with hlo | hhi
  · have hR : 0 < R := lt_of_le_of_lt hr hlo
    let t := (R-r)/R
    have ht : t ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (by linarith) hR.le,(div_le_one hR).mpr (by linarith)⟩
    have hmul : t*R = R-r := div_mul_cancel₀ _ hR.ne'
    let w := fun j => z j+t*(x j-z j)
    refine ⟨w,cube_segment (binary_cube hz) (binary_cube hx) ht,?_,?_⟩
    · have hh := binary_radial_affine (binary_cube hz) (binary_cube hx) hx ht
      rw [l1dist_self] at hh
      dsimp [w]
      rw [hh]
      dsimp [R] at hmul
      linarith
    · have hh := binary_radial_affine (binary_cube hz) (binary_cube hx) hz ht
      rw [l1dist_self,l1dist_comm x z] at hh
      dsimp [w]
      rw [hh,abs_of_neg (by linarith : r-l1dist z x < 0)]
      dsimp [R] at hmul
      linarith
  · let y := antipode x
    have hy := binary_antipode hx
    have hcomp : R+l1dist y z = h := by
      simpa only [R,l1dist_comm y z] using radial_complement hx (binary_cube hz)
    have hyx : l1dist y x = h := by
      have hh := radial_complement hx (binary_cube hy)
      simpa only [y,l1dist_self,add_zero] using hh
    let D := l1dist y z
    have hD : 0 < D := by dsimp [D]; linarith
    let t := (r-R)/D
    have ht : t ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg (by linarith) hD.le,(div_le_one hD).mpr (by dsimp [D]; linarith)⟩
    have hmul : t*D = r-R := div_mul_cancel₀ _ hD.ne'
    let w := fun j => z j+t*(y j-z j)
    refine ⟨w,cube_segment (binary_cube hz) (binary_cube hy) ht,?_,?_⟩
    · have hh := binary_radial_affine (binary_cube hz) (binary_cube hy) hx ht
      rw [hyx] at hh
      dsimp [w]
      rw [hh]
      dsimp [R,D] at hmul hcomp
      nlinarith
    · have hh := binary_radial_affine (binary_cube hz) (binary_cube hy) hz ht
      rw [l1dist_self] at hh
      dsimp [w]
      rw [hh,abs_of_pos (by exact sub_pos.mpr hhi)]
      dsimp [R,D] at hmul
      linarith

namespace RadialShell
variable {V : Type uV} {X : V → Fin h → ℝ}

lemma ball_meets_radial {B : RadialShell V} (hX : ∀v, binary (X v))
    (hB : B.Valid X) (z : V) {δ : ℝ} (hδ : 0 < δ)
    (hlo : B.inner-δ < l1dist (X z) (X B.center))
    (hhi : l1dist (X z) (X B.center) < B.outer+δ) :
    ¬Disjoint ((ball z δ).support X) (B.support X) := by
  have hinterval : max B.inner (l1dist (X z) (X B.center)-δ) <
      min B.outer (l1dist (X z) (X B.center)+δ) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    exact ⟨⟨hB.2.1,by linarith⟩,⟨by linarith,by linarith⟩⟩
  obtain ⟨r,hl,hr⟩ := exists_between hinterval
  have hlo' : B.inner < r := (le_max_left _ _).trans_lt hl
  have hhi' : r < B.outer := hr.trans_le (min_le_left _ _)
  have hradlo : l1dist (X z) (X B.center)-δ < r := (le_max_right _ _).trans_lt hl
  have hradhi : r < l1dist (X z) (X B.center)+δ := hr.trans_le (min_le_right _ _)
  obtain ⟨v,hv⟩ := hB.2.2.2.2
  have hmax : B.outer ≤ h := hv.trans (radial_max (hX _) (binary_cube (hX v)))
  obtain ⟨w,hw,hwr,hwz⟩ := binary_radial_move (hX B.center) (hX z)
    (hB.1.trans hlo'.le) (hhi'.le.trans hmax)
  have hwA : w ∈ (ball z δ).support X := by
    rw [support_ball]
    refine ⟨hw,?_⟩
    rw [hwz,abs_lt]
    constructor <;> linarith
  have hwB : w ∈ B.support X := ⟨hw,hwr ▸ hhi',Or.inr (hwr ▸ hlo')⟩
  exact fun hdis => Set.disjoint_left.mp hdis hwA hwB

end RadialShell
end
end StrongThinTree.Geometry

namespace StrongThinTree.AssignedAccounting
noncomputable section

lemma base_le_width (a : Bool) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) :
    base a R δ ≤ R := by
  have hh : max (R-3*δ) 0 ≤ R := max_le (by linarith) hR
  cases a <;> simp only [base,Bool.false_eq_true,↓reduceIte,div_one] <;> linarith

lemma base_discard (a : Bool) {R δ : ℝ} (hR : R ≤ 0) (hδ : 0 ≤ δ) :
    base a R δ = 0 := by
  have : max (R-3*δ) 0 = 0 := max_eq_right (by linarith)
  simp [base,this]

lemma fresh_lower {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536) :
    (5/6:ℝ)*δ ≤ fresh δ ε := by dsimp [fresh]; linarith

lemma avoiding_carve {δ ε R R₁ R₂ : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536)
    (hR : 512*δ ≤ R) (hsum : R₁+R₂ = R-2*δ) :
    base true R δ + theta*δ ≤ base true R₁ δ+base true R₂ δ+fresh δ ε := by
  have h1 := le_max_left (R₁-3*δ) 0
  have h2 := le_max_left (R₂-3*δ) 0
  have hf := fresh_lower hδ hε
  have hr : max (R-3*δ) 0 = R-3*δ := max_eq_left (by linarith)
  simp only [base,↓reduceIte,hr,theta]
  linarith

lemma dense_carve {δ ε R R₁ R₂ L M : ℝ}
    (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536) (hM : 0 ≤ M)
    (hR : 512*δ ≤ R) (hsum : R₁+R₂ = R-L-4*δ)
    (hdense : 3*L ≤ M*δ) (hcount : 765*δ ≤ M*δ) :
    base false R δ+theta*M*δ ≤
      base false R₁ δ+base false R₂ δ+M*fresh δ ε := by
  have h1 := le_max_left (R₁-3*δ) 0
  have h2 := le_max_left (R₂-3*δ) 0
  have hf := mul_le_mul_of_nonneg_left (fresh_lower hδ hε) hM
  have hr : max (R-3*δ) 0 = R-3*δ := max_eq_left (by linarith)
  simp only [base,Bool.false_eq_true,↓reduceIte,div_one,hr,theta]
  linarith

lemma sparse_carve {δ R R₁ R₂ L M : ℝ}
    (hδ : 0 ≤ δ) (hR : 512*δ ≤ R) (hsum : R₁+R₂ = R-L)
    (hwidth : 255*δ ≤ L) (hsparse : M*δ ≤ 3*L) :
    base false R δ+theta*M*δ ≤
      base false R₁ δ+base false R₂ δ+base false (L-2*δ) δ+base true L δ := by
  have h1 := le_max_left (R₁-3*δ) 0
  have h2 := le_max_left (R₂-3*δ) 0
  have h3 := le_max_left (L-2*δ-3*δ) 0
  have h4 := le_max_left (L-3*δ) 0
  have hr : max (R-3*δ) 0 = R-3*δ := max_eq_left (by linarith)
  simp only [base,Bool.false_eq_true,↓reduceIte,div_one,hr,theta]
  linarith

lemma shrink_cost (a : Bool) {R δ ε : ℝ} (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536) :
    0 ≤ base a R δ-base a (R-514*δ) ε ∧
    base a R δ-base a (R-514*δ) ε ≤
      256*(base a R ε-base a R δ) := by
  have hthreshold : R-514*δ-3*ε ≤ R-3*δ := by linarith
  have hmono := max_le_max_right (0:ℝ) hthreshold
  have hr : max (R-3*δ) 0-max (R-514*δ-3*ε) 0 ≤
      256*(max (R-3*ε) 0-max (R-3*δ) 0) := by
    by_cases hh : R ≤ 3*δ
    · rw [max_eq_right (by linarith : R-3*δ ≤ 0)]
      have h0 := le_max_right (R-514*δ-3*ε) 0
      have h1 := le_max_right (R-3*ε) 0
      linarith
    · have hd : 3*δ ≤ R := (not_le.mp hh).le
      rw [max_eq_left (by linarith : 0 ≤ R-3*δ),
        max_eq_left (by linarith : 0 ≤ R-3*ε)]
      have hlo := le_max_left (R-514*δ-3*ε) 0
      linarith
  cases a <;> simp only [base,Bool.false_eq_true,↓reduceIte,div_one] <;>
    constructor <;> linarith

lemma border_payment {δ ε B D : ℝ}
    (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536) (hB : 0 ≤ B)
    (hD : D ≤ B*δ/2) : theta*B*δ+D ≤ B*fresh δ ε := by
  have hh := mul_le_mul_of_nonneg_left (fresh_lower hδ hε) hB
  have hnon : 0 ≤ B*δ := mul_nonneg hB hδ
  dsimp [theta]
  linarith

end
end StrongThinTree.AssignedAccounting

namespace StrongThinTree.AssignedSelection
noncomputable section
open Finset

lemma large_neighbor_class {U : Type uU} {I : Type uI} [DecidableEq U] [DecidableEq I]
    (A : Finset U) (P : Finset I) (R : U → I → Prop) [DecidableRel R]
    (hP : P.Nonempty) (hcover : ∀u ∈ A, ∃i ∈ P, R u i)
    {q O : ℝ} (hq : 0 < q) (hO : 0 < O)
    (hparts : q*(P.card : ℝ) ≤ 2*O) (hmany : 1536*O ≤ q*(A.card : ℝ)) :
    ∃i ∈ P, 768 ≤ (A.filter (fun u => R u i)).card := by
  obtain ⟨i,hi,hmax⟩ := P.exists_max_image (fun i => (A.filter (fun u => R u i)).card) hP
  have hcover' : A = P.biUnion (fun i => A.filter (fun u => R u i)) := by
    ext u
    simp only [mem_biUnion,mem_filter]
    constructor
    · intro hu
      obtain ⟨j,hj,hr⟩ := hcover u hu
      exact ⟨j,hj,hu,hr⟩
    · rintro ⟨j,hj,hu,hr⟩
      exact hu
  have hc : A.card ≤ P.card*(A.filter (fun u => R u i)).card := by
    calc
      A.card = (P.biUnion (fun i => A.filter (fun u => R u i))).card := congrArg card hcover'
      _ ≤ ∑j ∈ P, (A.filter (fun u => R u j)).card := card_biUnion_le
      _ ≤ ∑j ∈ P, (A.filter (fun u => R u i)).card := sum_le_sum (fun j hj => hmax j hj)
      _ = _ := by simp
  have hc' : (A.card : ℝ) ≤ (P.card : ℝ)*(A.filter (fun u => R u i)).card := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hc' hq.le
  have hp := mul_le_mul_of_nonneg_right hparts
    (Nat.cast_nonneg (A.filter (fun u => R u i)).card : (0:ℝ) ≤ _)
  have hn : (768:ℝ) ≤ (A.filter (fun u => R u i)).card := by nlinarith
  exact ⟨i,hi,by exact_mod_cast hn⟩

lemma radial_range {r₁ r₂ p q s₀ u₀ s u δ : ℝ}
    (hδ : 0 < δ) (hp0 : p ≤ s₀) (hq0 : s₀ ≤ q)
    (hu₀lo : r₁+256*δ < u₀) (hu₀hi : u₀ < r₂-256*δ)
    (hnear0 : |u₀-s₀| < δ) (hp : p ≤ s) (hq : s ≤ q)
    (hnear : |u-s| < δ)
    (hout : ¬(max r₁ p-δ < u ∧ u < min r₂ q+δ)) :
    255*δ ≤ min r₂ q-max r₁ p := by
  obtain ⟨hn0a,hn0b⟩ := abs_lt.mp hnear0
  obtain ⟨hna,hnb⟩ := abs_lt.mp hnear
  have hslo : r₁+255*δ < s₀ := by linarith
  have hshi : s₀ < r₂-255*δ := by linarith
  have ha : max r₁ p ≤ s₀ := max_le (by linarith) hp0
  have hb : s₀ ≤ min r₂ q := le_min (by linarith) hq0
  by_cases hul : max r₁ p-δ < u
  · have huh : min r₂ q+δ ≤ u := le_of_not_gt (fun hh => hout ⟨hul,hh⟩)
    have hclip : r₂ ≤ q := by
      by_contra hh
      rw [min_eq_right (not_le.mp hh).le] at huh
      linarith
    rw [min_eq_left hclip]
    linarith
  · have hul : u ≤ max r₁ p-δ := not_lt.mp hul
    have hclip : p ≤ r₁ := by
      by_contra hh
      rw [max_eq_right (not_le.mp hh).le] at hul
      linarith
    rw [max_eq_left hclip]
    linarith

lemma interior_neighbor_in_range {r₁ r₂ p q s u δ : ℝ}
    (hδ : 0 < δ) (hp : p ≤ s) (hq : s ≤ q)
    (hulo : r₁+256*δ < u) (huhi : u < r₂-256*δ)
    (hnear : |u-s| < δ) :
    max r₁ p ≤ min r₂ q ∧ max r₁ p-δ < u ∧ u < min r₂ q+δ := by
  obtain ⟨hna,hnb⟩ := abs_lt.mp hnear
  have ha : max r₁ p ≤ s := max_le (by linarith) hp
  have hb : s ≤ min r₂ q := le_min (by linarith) hq
  exact ⟨ha.trans hb,by linarith,by linarith⟩

lemma dense_count {δ L M N : ℝ} (hδ : 0 ≤ δ) (hN : 768 ≤ N)
    (hdich : N ≤ M ∨ 255*δ ≤ L) (hdense : 3*L ≤ M*δ) : 765*δ ≤ M*δ := by
  rcases hdich with hh | hh
  · have := mul_le_mul_of_nonneg_right hh hδ
    nlinarith
  · linarith

lemma sparse_width {δ L M N : ℝ} (hδ : 0 ≤ δ) (hN : 768 ≤ N)
    (hdich : N ≤ M ∨ 255*δ ≤ L) (hsparse : M*δ ≤ 3*L) : 255*δ ≤ L := by
  rcases hdich with hh | hh
  · have := mul_le_mul_of_nonneg_right hh hδ
    nlinarith
  · exact hh

end
end StrongThinTree.AssignedSelection

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Assignment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

lemma compatible_ne (hX : ∀v, binary (X v)) {B D : Record n}
    (hB : B.Shape H) (hval : B.shell.Valid X) (hBD : B.Compatible H X D) : B ≠ D := by
  rintro rfl
  exact B.compatible_self_iff H X hX hB hval hBD

lemma restriction_not_fresh {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true) (B : Record n) (a b : ℝ) :
    B.restriction a b ∉ F := by
  intro hh
  have hh' := hF _ hh
  simp [restriction,RadialShell.hollow] at hh'

lemma restriction_token {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true) (B : Record n) (a b δ ε : ℝ) :
    phaseToken F δ ε (B.restriction a b) =
      AssignedAccounting.base B.avoided.isSome (b-a) δ := by
  rw [phaseToken,ite_eq_right (restriction_not_fresh hF B a b)]
  rfl

lemma interior_width {δ : ℝ} {A B : Record n} (hh : A.Interior H X 256 δ B) :
    512*δ < B.shell.width := by
  dsimp [RadialShell.width]
  linarith [hh.2.1,hh.2.2]

lemma interior_ball_subset {δ : ℝ} {A B : Record n} (hδ : 0 ≤ δ)
    (hA : A.shell = RadialShell.ball A.shell.center δ)
    (hh : A.Interior H X 256 δ B) : A.shell.support X ⊆ B.shell.support X := by
  rw [hA]
  apply RadialShell.ball_subset_of_radial_margin
  · linarith [hh.2.1]
  · linarith [hh.2.2]

end Record

lemma labeled_singleton {q : ℝ} {B : Record n} (hB : B.Valid H G X q) :
    H.LabeledArrangement G X q {B} := by
  constructor
  · intro A hA
    simpa only [mem_singleton.mp hA] using hB
  · intro A hA D hD hne
    exact (hne ((mem_singleton.mp hA).trans (mem_singleton.mp hD).symm)).elim

lemma labeled_insert {q : ℝ} {Z : Finset (Record n)} {B : Record n}
    (hZ : H.LabeledArrangement G X q Z) (hB : B.Valid H G X q)
    (hcompat : ∀D ∈ Z, B.Compatible H X D) :
    H.LabeledArrangement G X q (insert B Z) := by
  rw [← singleton_union]
  apply H.labeled_union G X (H.labeled_singleton G X hB) hZ
  intro A hA D hD
  simpa only [mem_singleton.mp hA] using hcompat D hD

lemma avoiding_operation (hX : ∀v, binary (X v))
    {q δ ε : ℝ} (hδ : 0 < δ) (hε : ε ≤ δ/1536)
    {F Z : Finset (Record n)} (hF : ∀D ∈ F,
      D.shell.ordinary = true ∧ D.avoided = none)
    (hZ : H.LabeledArrangement G X q Z) {A B : Record n}
    (hA : A.Valid H G X q) (hAF : A ∈ F)
    (hAball : A.shell = RadialShell.ball A.shell.center δ)
    (hB : B ∈ Z) (havoid : B.avoided.isSome = true)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ A.excluded)
    (hinter : A.Interior H X 256 δ B) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X q Z' ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+AssignedAccounting.theta*δ ≤
        ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      ∀D ∈ Z', D ∈ Z ∨ D = A ∨ ∃a b, D = B.restriction a b ∧
        B.shell.inner ≤ a ∧ b ≤ B.shell.outer ∧ a < b := by
  let r := l1dist (X A.shell.center) (X B.shell.center)
  let B₁ := B.restriction B.shell.inner (r-δ)
  let B₂ := B.restriction (r+δ) B.shell.outer
  have hbvalid := hZ.1 B hB
  have h1a : B.shell.inner < r-δ := by dsimp [r]; linarith [hinter.2.1]
  have h1b : r-δ ≤ B.shell.outer := by dsimp [r]; linarith [hinter.2.2]
  have h2a : B.shell.inner ≤ r+δ := by dsimp [r]; linarith [hinter.2.1]
  have h2b : r+δ < B.shell.outer := by dsimp [r]; linarith [hinter.2.2]
  have hB₁ : B₁.Valid H G X q := Record.restrict_valid H G X hbvalid (le_refl _) h1b h1a
  have hB₂ : B₂.Valid H G X q := Record.restrict_valid H G X hbvalid h2a (le_refl _) h2b
  have h12 : B₁.Compatible H X B₂ := Or.inl
    (RadialShell.concentric_disjoint X B.shell.center (by linarith : r-δ ≤ r+δ))
  have hA1 : A.Compatible H X B₁ := by
    left
    change Disjoint (A.shell.support X) ((RadialShell.hollow B.shell.center B.shell.inner (r-δ)).support X)
    rw [hAball]
    exact RadialShell.ball_disjoint_hollow_lower X _ _ (by dsimp [r]; linarith)
  have hA2 : A.Compatible H X B₂ := by
    left
    change Disjoint (A.shell.support X) ((RadialShell.hollow B.shell.center (r+δ) B.shell.outer).support X)
    rw [hAball]
    exact RadialShell.ball_disjoint_hollow_upper X _ _ (le_refl _)
  let W : Finset (Record n) := {A,B₁,B₂}
  have hW : H.LabeledArrangement G X q W := by
    apply H.labeled_insert G X
    · apply H.labeled_insert G X (H.labeled_singleton G X hB₂) hB₁
      intro D hD
      simpa only [mem_singleton.mp hD] using h12
    · exact hA
    · intro D hD
      rcases mem_insert.mp hD with rfl | hD
      · exact hA1
      · simpa only [mem_singleton.mp hD] using hA2
  have hancestor : A.owner ∈ B.conflict H :=
    Record.candidate_ancestor H hA.1 hbvalid.1 (horder B hB) hinter.1
  have hcompat : ∀D ∈ Z.erase B, ∀C ∈ W, D.Compatible H X C := by
    intro D hD C hC
    obtain ⟨hDB,hDZ⟩ := mem_erase.mp hD
    have hBC : B.Compatible H X D := H.labeled_pair G X hZ hB hDZ hDB.symm
    apply Record.compatible_symm H X
    rcases mem_insert.mp hC with rfl | hC
    · exact Record.insert_compatible H G X hZ hA.1 hB hDZ hDB.symm hancestor horder
        (Record.interior_ball_subset H X hδ.le hAball hinter)
    rcases mem_insert.mp hC with rfl | hC
    · exact Record.compatible_heredity H X hBC
        (B.restriction_refines H X (le_refl _) h1b).1 (Subset.refl _)
    · have heq := mem_singleton.mp hC
      subst C
      exact Record.compatible_heredity H X hBC
        (B.restriction_refines H X h2a (le_refl _)).1 (Subset.refl _)
  have hBF : B ∉ F := by
    intro hh
    rw [(hF B hh).2] at havoid
    simp at havoid
  have hcredit : Record.phaseToken F δ ε B+AssignedAccounting.theta*δ ≤
      ∑D ∈ W, Record.phaseToken F δ ε D := by
    have hne12 := Record.compatible_ne H X hX hB₁.1 hB₁.2.2.1 h12
    have hneA1 := Record.compatible_ne H X hX hA.1 hA.2.2.1 hA1
    have hneA2 := Record.compatible_ne H X hX hA.1 hA.2.2.1 hA2
    have hAnot : A ∉ ({B₁,B₂} : Finset (Record n)) := by simp [hneA1,hneA2]
    have h1not : B₁ ∉ ({B₂} : Finset (Record n)) := by simpa using hne12
    dsimp [W]
    rw [sum_insert hAnot,sum_insert h1not,sum_singleton]
    rw [Record.phaseToken,ite_eq_right hBF,havoid]
    rw [show Record.phaseToken F δ ε A = AssignedAccounting.fresh δ ε by simp [Record.phaseToken,hAF]]
    rw [Record.restriction_token (fun D hD => (hF D hD).1) B,
      Record.restriction_token (fun D hD => (hF D hD).1) B,havoid]
    have hh := AssignedAccounting.avoiding_carve hδ.le hε
      (Record.interior_width H X hinter).le
      (show (r-δ-B.shell.inner)+(B.shell.outer-(r+δ))=B.shell.width-2*δ by
        dsimp [RadialShell.width]; ring)
    linarith
  refine ⟨Z.erase B∪W,H.labeled_replace G X hZ hW B hcompat,
    H.replacement_credit G X hX hZ hB hcompat _ hcredit,?_⟩
  intro D hD
  rcases mem_union.mp hD with hD | hD
  · exact Or.inl (mem_of_mem_erase hD)
  right
  rcases mem_insert.mp hD with rfl | hD
  · exact Or.inl rfl
  right
  rcases mem_insert.mp hD with rfl | hD
  · exact ⟨B.shell.inner,r-δ,rfl,le_refl _,h1b,h1a⟩
  · have heq := mem_singleton.mp hD
    exact ⟨r+δ,B.shell.outer,heq,h2a,le_refl _,h2b⟩

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

lemma mem_restrictionSet {B D : Record n} {a b : ℝ} :
    D ∈ B.restrictionSet a b ↔ a < b ∧ D = B.restriction a b := by
  by_cases hh : a < b <;> simp [restrictionSet,hh]

lemma restrictionSet_valid {q a b : ℝ} {B : Record n} (hB : B.Valid H G X q)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) :
    H.LabeledArrangement G X q (B.restrictionSet a b) := by
  by_cases hab : a < b
  · rw [restrictionSet,ite_eq_left hab]
    exact H.labeled_singleton G X (restrict_valid H G X hB ha hb hab)
  · rw [restrictionSet,ite_eq_right hab]
    exact H.labeled_empty G X q

lemma restrictionSet_refines {B D : Record n} {a b : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hD : D ∈ B.restrictionSet a b) : D.Refines H X B := by
  obtain ⟨hab,rfl⟩ := mem_restrictionSet.mp hD
  exact B.restriction_refines H X ha hb

lemma restrictionSet_token {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true) (B : Record n) (a b : ℝ)
    {δ ε : ℝ} (hδ : 0 ≤ δ) :
    (∑D ∈ B.restrictionSet a b, phaseToken F δ ε D) =
      AssignedAccounting.base B.avoided.isSome (b-a) δ := by
  by_cases hab : a < b
  · rw [restrictionSet,ite_eq_left hab,sum_singleton,restriction_token hF]
  · rw [restrictionSet,ite_eq_right hab,sum_empty,AssignedAccounting.base_discard _ (by linarith) hδ]

lemma restrictions_compatible (B : Record n) {a b c d : ℝ} (hbc : b ≤ c)
    {D E : Record n} (hD : D ∈ B.restrictionSet a b) (hE : E ∈ B.restrictionSet c d) :
    D.Compatible H X E := by
  obtain ⟨_,rfl⟩ := mem_restrictionSet.mp hD
  obtain ⟨_,rfl⟩ := mem_restrictionSet.mp hE
  exact Or.inl (RadialShell.concentric_disjoint X B.shell.center hbc)

end Record

lemma dense_operation (hX : ∀v, binary (X v))
    {q δ ε a b : ℝ} (hδ : 0 < δ) (hε : ε ≤ δ/1536)
    {F Z M : Finset (Record n)} (hF : ∀D ∈ F,
      D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hZ : H.LabeledArrangement G X q Z) {B : Record n} (hB : B ∈ Z)
    (hMZ : H.LabeledArrangement G X q M) (hMF : M ⊆ F)
    (hMball : ∀A ∈ M, A.shell = RadialShell.ball A.shell.center δ)
    (hno : B.avoided = none) (hwidth : 512*δ < B.shell.width)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) (hab : a ≤ b)
    (hrange : ∀A ∈ M, a-δ < l1dist (X A.shell.center) (X B.shell.center) ∧
      l1dist (X A.shell.center) (X B.shell.center) < b+δ)
    (hinter : ∀A ∈ M, A.Interior H X 256 δ B)
    (horder : ∀A ∈ M, ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ A.excluded)
    (hcount : 765*δ ≤ (M.card : ℝ)*δ) (hdense : 3*(b-a) ≤ (M.card : ℝ)*δ) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X q Z' ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+AssignedAccounting.theta*(M.card : ℝ)*δ ≤
        ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      ∀D ∈ Z', D ∈ Z ∨ D ∈ M ∨ ∃c d, D = B.restriction c d ∧
        B.shell.inner ≤ c ∧ d ≤ B.shell.outer ∧ c < d := by
  let W₁ := B.restrictionSet B.shell.inner (a-2*δ)
  let W₂ := B.restrictionSet (b+2*δ) B.shell.outer
  let W := W₁∪W₂∪M
  have hbvalid := hZ.1 B hB
  have h1b : a-2*δ ≤ B.shell.outer := by linarith
  have h2a : B.shell.inner ≤ b+2*δ := by linarith
  have hW₁ : H.LabeledArrangement G X q W₁ :=
    B.restrictionSet_valid H G X hbvalid (le_refl _) h1b
  have hW₂ : H.LabeledArrangement G X q W₂ :=
    B.restrictionSet_valid H G X hbvalid h2a (le_refl _)
  have h12 : ∀D ∈ W₁, ∀E ∈ W₂, D.Compatible H X E := by
    intro D hD E hE
    exact B.restrictions_compatible H X (by linarith : a-2*δ ≤ b+2*δ) hD hE
  have hWM : ∀D ∈ W₁∪W₂, ∀A ∈ M, D.Compatible H X A := by
    intro D hD A hAM
    apply Record.compatible_symm H X
    left
    rw [hMball A hAM]
    rcases mem_union.mp hD with hD | hD
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hD
      exact RadialShell.ball_disjoint_hollow_lower X _ _ (by linarith [(hrange A hAM).1])
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hD
      exact RadialShell.ball_disjoint_hollow_upper X _ _ (by linarith [(hrange A hAM).2])
  have hW12 := H.labeled_union G X hW₁ hW₂ h12
  have hW : H.LabeledArrangement G X q W := H.labeled_union G X hW12 hMZ hWM
  have hcompat : ∀D ∈ Z.erase B, ∀C ∈ W, D.Compatible H X C := by
    intro D hD C hC
    obtain ⟨hDB,hDZ⟩ := mem_erase.mp hD
    have hBD := H.labeled_pair G X hZ hB hDZ hDB.symm
    apply Record.compatible_symm H X
    rcases mem_union.mp hC with hC | hC
    · rcases mem_union.mp hC with hC | hC
      · have hh := B.restrictionSet_refines H X (le_refl _) h1b hC
        exact Record.compatible_heredity H X hBD hh.1 hh.2
      · have hh := B.restrictionSet_refines H X h2a (le_refl _) hC
        exact Record.compatible_heredity H X hBD hh.1 hh.2
    · have hancestor := Record.candidate_ancestor H (hMZ.1 C hC).1 hbvalid.1
        (horder C hC B hB) (hinter C hC).1
      exact Record.insert_compatible H G X hZ (hMZ.1 C hC).1 hB hDZ hDB.symm hancestor
        (horder C hC) (Record.interior_ball_subset H X hδ.le (hMball C hC) (hinter C hC))
  have hBF : B ∉ F := by
    intro hh
    rw [(hF B hh).2.1] at hwidth
    linarith
  have hcredit : Record.phaseToken F δ ε B+AssignedAccounting.theta*(M.card : ℝ)*δ ≤
      ∑D ∈ W, Record.phaseToken F δ ε D := by
    have hd12 := H.labeled_sets_disjoint G X hX hW₁ h12
    have hdM := H.labeled_sets_disjoint G X hX hW12 hWM
    dsimp only [W]
    rw [sum_union hdM,sum_union hd12,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le]
    have hsumM : (∑D ∈ M, Record.phaseToken F δ ε D) =
        (M.card : ℝ)*AssignedAccounting.fresh δ ε := by
      calc
        _ = ∑D ∈ M, AssignedAccounting.fresh δ ε := sum_congr rfl (fun D hD => by
          simp only [Record.phaseToken,ite_eq_left (hMF hD)])
        _ = _ := by simp
    rw [hsumM,Record.phaseToken,ite_eq_right hBF,hno,Option.isSome_none]
    exact AssignedAccounting.dense_carve hδ.le hε (Nat.cast_nonneg _) hwidth.le
      (by dsimp [RadialShell.width]; ring) hdense hcount
  refine ⟨Z.erase B∪W,H.labeled_replace G X hZ hW B hcompat,
    H.replacement_credit G X hX hZ hB hcompat _ hcredit,?_⟩
  intro D hD
  rcases mem_union.mp hD with hD | hD
  · exact Or.inl (mem_of_mem_erase hD)
  right
  rcases mem_union.mp hD with hD | hD
  · right
    rcases mem_union.mp hD with hD | hD
    · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hD
      exact ⟨B.shell.inner,a-2*δ,heq,le_refl _,h1b,hpos⟩
    · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hD
      exact ⟨b+2*δ,B.shell.outer,heq,h2a,le_refl _,hpos⟩
  · exact Or.inl hD

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Fin h → ℝ)

namespace Record

lemma central_refines {B : Record n} (hshape : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) {a b c d : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hc : B.shell.inner ≤ c) (hd : d ≤ B.shell.outer) :
    (B.innerRecord t a b).Refines H X B ∧ (B.outsideRecord t c d).Refines H X B := by
  obtain ⟨h1,h2⟩ := central_conflict H hshape hno ht a b c d
  exact ⟨⟨RadialShell.restriction_subset X B.shell ha hb,h1 ▸ filter_subset _ _⟩,
    ⟨RadialShell.restriction_subset X B.shell hc hd,h2 ▸ filter_subset _ _⟩⟩

lemma hollow_token {F : Finset (Record n)} (hF : ∀D ∈ F, D.shell.ordinary = true)
    {B : Record n} (hB : B.shell.ordinary = false) (δ ε : ℝ) :
    phaseToken F δ ε B = AssignedAccounting.base B.avoided.isSome B.shell.width δ := by
  rw [phaseToken,ite_eq_right]
  intro hh
  have := hF B hh
  simp [hB] at this

end Record

lemma sparse_operation (hX : ∀v, binary (X v))
    {q δ ε a b M : ℝ} (hδ : 0 < δ)
    {F Z : Finset (Record n)} (hF : ∀D ∈ F,
      D.shell.ordinary = true ∧ D.shell.width = δ)
    (hZ : H.LabeledArrangement G X q Z) {B : Record n} (hB : B ∈ Z)
    (hno : B.avoided = none) (hwidth : 512*δ < B.shell.width)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hwide : 255*δ ≤ b-a) (hsparse : M*δ ≤ 3*(b-a))
    (hinner : (B.innerRecord t (a+δ) (b-δ)).Valid H G X q)
    (houter : (B.outsideRecord t a b).Valid H G X q) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X q Z' ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+AssignedAccounting.theta*M*δ ≤
        ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      ∀D ∈ Z', D ∈ Z ∨ D = B.innerRecord t (a+δ) (b-δ) ∨
        D = B.outsideRecord t a b ∨ ∃c d, D = B.restriction c d ∧
          B.shell.inner ≤ c ∧ d ≤ B.shell.outer ∧ c < d := by
  let C := B.innerRecord t (a+δ) (b-δ)
  let D := B.outsideRecord t a b
  let W₁ := B.restrictionSet B.shell.inner a
  let W₂ := B.restrictionSet b B.shell.outer
  let W₀ := W₁∪W₂
  let W₃ := insert C W₀
  let W := insert D W₃
  have hab : a ≤ b := by linarith
  have hv := hZ.1 B hB
  have hW₁ : H.LabeledArrangement G X q W₁ :=
    Record.restrictionSet_valid H G X hv (le_refl _) (hab.trans hb)
  have hW₂ : H.LabeledArrangement G X q W₂ :=
    Record.restrictionSet_valid H G X hv (ha.trans hab) (le_refl _)
  have h12 : ∀E ∈ W₁, ∀J ∈ W₂, E.Compatible H X J := by
    intro E hE J hJ
    exact Record.restrictions_compatible H X B hab hE hJ
  have hW₀ : H.LabeledArrangement G X q W₀ := H.labeled_union G X hW₁ hW₂ h12
  have hC0 : ∀E ∈ W₀, C.Compatible H X E := by
    intro E hE
    rcases mem_union.mp hE with hE | hE
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl ((RadialShell.concentric_disjoint X B.shell.center (by linarith : a ≤ a+δ)).symm)
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl (RadialShell.concentric_disjoint X B.shell.center (by linarith : b-δ ≤ b))
  have hW₃ : H.LabeledArrangement G X q W₃ := H.labeled_insert G X hW₀ hinner hC0
  have hD3 : ∀E ∈ W₃, D.Compatible H X E := by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact Or.inr (Record.central_domain_disjoint H hv.1 hno ht (a+δ) (b-δ) a b).symm
    rcases mem_union.mp hE with hE | hE
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl ((RadialShell.concentric_disjoint X B.shell.center (le_refl a)).symm)
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl (RadialShell.concentric_disjoint X B.shell.center (le_refl b))
  have hW : H.LabeledArrangement G X q W := H.labeled_insert G X hW₃ houter hD3
  have hCD := Record.central_refines H X hv.1 hno ht
    (show B.shell.inner ≤ a+δ by linarith) (show b-δ ≤ B.shell.outer by linarith) ha hb
  have hWB : ∀E ∈ W, E.Refines H X B := by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact hCD.2
    rcases mem_insert.mp hE with rfl | hE
    · exact hCD.1
    rcases mem_union.mp hE with hE | hE
    · exact Record.restrictionSet_refines H X (le_refl _) (hab.trans hb) hE
    · exact Record.restrictionSet_refines H X (ha.trans hab) (le_refl _) hE
  have hcompat : ∀J ∈ Z.erase B, ∀E ∈ W, J.Compatible H X E := by
    intro J hJ E hE
    obtain ⟨hne,hJ⟩ := mem_erase.mp hJ
    exact Record.compatible_symm H X (Record.compatible_heredity H X
      (H.labeled_pair G X hZ hB hJ hne.symm) (hWB E hE).1 (hWB E hE).2)
  have hBF : B ∉ F := by
    intro hh
    rw [(hF B hh).2] at hwidth
    linarith
  have hDC : D ∉ W₃ := by
    intro hh
    exact Record.compatible_self_iff H X D hX houter.1 houter.2.2.1 (hD3 D hh)
  have hCW : C ∉ W₀ := by
    intro hh
    exact Record.compatible_self_iff H X C hX hinner.1 hinner.2.2.1 (hC0 C hh)
  have hcredit : Record.phaseToken F δ ε B+AssignedAccounting.theta*M*δ ≤
      ∑E ∈ W, Record.phaseToken F δ ε E := by
    have hdis := H.labeled_sets_disjoint G X hX hW₁ h12
    change _ ≤ ∑E ∈ insert D W₃, _
    rw [sum_insert hDC]
    change _ ≤ _+(∑E ∈ insert C W₀, _)
    rw [sum_insert hCW]
    change _ ≤ _+(_+(∑E ∈ W₁∪W₂, _))
    rw [sum_union hdis,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le,
      Record.hollow_token (fun D hD => (hF D hD).1) (show D.shell.ordinary = false from rfl),
      Record.hollow_token (fun D hD => (hF D hD).1) (show C.shell.ordinary = false from rfl),
      Record.phaseToken,ite_eq_right hBF]
    simp only [D,C,Record.innerRecord,Record.outsideRecord,RadialShell.hollow,
      hno,Option.isSome_none,Option.isSome_some,RadialShell.width]
    have hh := AssignedAccounting.sparse_carve hδ.le hwidth.le
      (R₁ := a-B.shell.inner) (R₂ := B.shell.outer-b) (L := b-a)
      (by dsimp [RadialShell.width]; ring) hwide hsparse
    rw [show b-δ-(a+δ) = b-a-2*δ by ring]
    dsimp only [RadialShell.width] at hh
    linarith
  refine ⟨Z.erase B∪W,H.labeled_replace G X hZ hW B hcompat,
    H.replacement_credit G X hX hZ hB hcompat _ hcredit,?_⟩
  intro E hE
  rcases mem_union.mp hE with hE | hE
  · exact Or.inl (mem_of_mem_erase hE)
  right
  rcases mem_insert.mp hE with heq | hE
  · exact Or.inr (Or.inl heq)
  rcases mem_insert.mp hE with heq | hE
  · exact Or.inl heq
  right; right
  rcases mem_union.mp hE with hE | hE
  · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hE
    exact ⟨B.shell.inner,a,heq,le_refl _,hab.trans hb,hpos⟩
  · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hE
    exact ⟨b,B.shell.outer,heq,ha.trans hab,le_refl _,hpos⟩

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.BagBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}

namespace AssignedBag

lemma neighbor_spec (A : H.AssignedBag G X δ η) {u : Fin n} (hu : u ∈ A.centers) :
    A.neighbor u ∈ H.parent A.owner\A.owner ∧
      l1dist (X u) (X (A.neighbor u)) < δ ∧
      ∃e : Fin m, (G.left e = u ∧ G.right e = A.neighbor u) ∨
        (G.left e = A.neighbor u ∧ G.right e = u) := by
  simpa only [neighbor,dite_eq_left hu] using (A.neighbor_exists hu).choose_spec

lemma input_injective (A : H.AssignedBag G X δ η) (P : Finset (Finset (Fin n))) :
    Function.Injective (A.input P) := by
  intro u v hh
  exact congrArg (fun B : Record n => B.shell.center) hh

lemma input_arrangement (A : H.AssignedBag G X δ η) {q : ℝ}
    {P : Finset (Finset (Fin n))} {U : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hvalid : ∀u ∈ U, (A.input P u).Valid H G X q) :
    H.LabeledArrangement G X q (U.image (A.input P)) := by
  constructor
  · intro B hB
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hB
    exact hvalid u hu
  · intro B hB D hD hne hgeo
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hB
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hD
    exact (hgeo (A.disjoint (hU hu) (hU hv) (fun hh => hne (congrArg (A.input P) hh)))).elim

end AssignedBag

namespace Record

lemma unique_interior (_hX : ∀v, binary (X v)) {q : ℝ}
    {Z : Finset (Record n)} (hZ : H.LabeledArrangement G X q Z)
    {A B D : Record n} (hA : A.Shape H) (hB : B ∈ Z) (hD : D ∈ Z)
    (horder : ∀E ∈ Z, E.owner ⊂ A.owner → E.owner ∈ A.excluded)
    (hAB : (A.conflict H ∩ B.conflict H).Nonempty)
    (hAD : (A.conflict H ∩ D.conflict H).Nonempty)
    (hsub : A.shell.support X ⊆ D.shell.support X)
    (hmeet : ¬Disjoint (A.shell.support X) (B.shell.support X)) : B = D := by
  by_contra hne
  have hba := candidate_ancestor H hA (hZ.1 B hB).1 (horder B hB) hAB
  have hda := candidate_ancestor H hA (hZ.1 D hD).1 (horder D hD) hAD
  rcases H.labeled_pair G X hZ hB hD hne with hh | hh
  · exact hmeet ((hh.symm).mono_left hsub)
  · exact Finset.disjoint_left.mp hh hba hda

lemma strict_owner_of_interior (hX : ∀v, binary (X v))
    {A B : Record n} (hA : A.Shape H) (hB : B.Shape H)
    (hAv : A.shell.Valid X) (hδ : 0 ≤ δ)
    (hball : A.shell = RadialShell.ball A.shell.center δ)
    (horder : B.owner ⊂ A.owner → B.owner ∈ A.excluded)
    (hsep : B.owner = A.owner → Disjoint (A.shell.support X) (B.shell.support X))
    (hinter : A.Interior H X 256 δ B) : A.owner ⊂ B.owner := by
  have hanc := candidate_ancestor H hA hB horder hinter.1
  have hsub := (H.mem_domain.mp hanc).2.1
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro hh
  obtain ⟨z,hz⟩ := RadialShell.valid_support_nonempty hX hAv
  exact Set.disjoint_left.mp (hsep hh.symm) hz
    (interior_ball_subset H X hδ hball hinter hz)

end Record
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma large_component (A : H.AssignedBag G X δ η) {q : ℝ}
    (hq : 0 < q) (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    {U : Finset (Fin n)} (hU : U ⊆ A.centers) (hhalf : A.centers.card ≤ 2*U.card) :
    ∃R : Finset (Fin n), R ⊆ H.parent A.owner\A.owner ∧
      G.EdgeConnectedReal R (q/4) ∧ 768 ≤ (U.filter (fun u => A.neighbor u ∈ R)).card := by
  obtain ⟨J,hJ,hJc,hcount⟩ := G.outside_connected_partition hq
    (hconn (H.parent A.owner) (H.parent_mem A.owner A.owner_mem A.nonroot))
    (H.nonempty A.owner A.owner_mem) (H.parent_strict A.owner A.owner_mem A.nonroot)
  have hJn : J.Nonempty := by
    have hout : (H.parent A.owner\A.owner).Nonempty :=
      sdiff_nonempty.mpr (H.parent_strict A.owner A.owner_mem A.nonroot).not_subset
    rw [← hJ.2.2] at hout
    obtain ⟨R,hR,_⟩ := biUnion_nonempty.mp hout
    exact ⟨R,hR⟩
  have hcover : ∀u ∈ U, ∃R ∈ J, A.neighbor u ∈ R := by
    intro u hu
    have hh := (A.neighbor_spec (hU hu)).1
    rw [← hJ.2.2] at hh
    simpa only [mem_biUnion,id_eq] using hh
  have hb := H.parent_boundary_lower G hconn A.owner_mem A.nonroot
  have hηq : 3072 ≤ η*q := (div_le_iff₀ hq).mp hη
  have hsum := mul_le_mul_of_nonneg_right A.assignment hq.le
  have hmass := mul_le_mul_of_nonneg_right hηq
    (Nat.cast_nonneg (H.parentBoundary G A.owner).card : (0:ℝ) ≤ _)
  have hhalf' : (A.centers.card : ℝ) ≤ 2*(U.card : ℝ) := by exact_mod_cast hhalf
  have hmul := mul_le_mul_of_nonneg_left hhalf' hq.le
  obtain ⟨R,hR,hlarge⟩ := AssignedSelection.large_neighbor_class U J
    (fun u R => A.neighbor u ∈ R) hJn hcover hq (lt_of_lt_of_le hq hb)
    (by simpa [mul_comm,Hierarchy.parentBoundary] using hcount)
    (by linarith)
  exact ⟨R,(hJ.1 R hR).2,hJc R hR,hlarge⟩

lemma selected_interior (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q : ℝ} {P : Finset (Finset (Fin n))} {U : Finset (Fin n)}
    {Z : Finset (Record n)} (hZ : H.LabeledArrangement G X q Z)
    (hshape : ∀u ∈ U, (A.input P u).Shape H)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hinter : ∀u ∈ U, ∃D ∈ Z, (A.input P u).Interior H X 256 δ D)
    {B : Record n} (hB : B ∈ Z) {u₀ : Fin n}
    (hint₀ : (A.input P u₀).Interior H X 256 δ B)
    {a b : ℝ} (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    {u : Fin n} (hu : u ∈ U)
    (hr : a-δ < l1dist (X u) (X B.shell.center) ∧
      l1dist (X u) (X B.shell.center) < b+δ) :
    (A.input P u).Interior H X 256 δ B := by
  obtain ⟨D,hD,hintD⟩ := hinter u hu
  have hconf : ((A.input P u).conflict H ∩ B.conflict H).Nonempty := hint₀.1
  have hmeet : ¬Disjoint ((A.input P u).shell.support X) (B.shell.support X) :=
    RadialShell.ball_meets_radial hX (hZ.1 B hB).2.2.1 u A.radius_pos
      (by linarith [hr.1]) (by linarith [hr.2])
  have heq : B = D := Record.unique_interior hX hZ (hshape u hu) hB hD
    (fun E hE hsub => by simpa [input,Record.excluded] using horder E hE hsub)
    hconf hintD.1 (Record.interior_ball_subset H X A.radius_pos.le rfl hintD) hmeet
  exact heq.symm ▸ hintD

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma radial_group (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q : ℝ} {P : Finset (Finset (Fin n))} {U : Finset (Fin n)}
    (hU : U ⊆ A.centers) {Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z)
    (hshape : ∀u ∈ U, (A.input P u).Shape H)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hinter : ∀u ∈ U, ∃D ∈ Z, (A.input P u).Interior H X 256 δ D)
    (hno : ∀u ∈ U, ∀D ∈ Z, (A.input P u).Interior H X 256 δ D → D.avoided = none)
    {R : Finset (Fin n)} (hlarge : 768 ≤ (U.filter (fun u => A.neighbor u ∈ R)).card) :
    ∃(B : Record n) (a b : ℝ) (M : Finset (Fin n)) (u₁ u₂ : Fin n),
      B ∈ Z ∧ B.avoided = none ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer ∧ a ≤ b ∧
      M.Nonempty ∧ M = U.filter (fun u => a-δ < l1dist (X u) (X B.shell.center) ∧
        l1dist (X u) (X B.shell.center) < b+δ) ∧
      (∀u ∈ M, (A.input P u).Interior H X 256 δ B) ∧
      (768 ≤ M.card ∨ 255*δ ≤ b-a) ∧
      u₁ ∈ U ∧ u₂ ∈ U ∧ A.neighbor u₁ ∈ R ∧ A.neighbor u₂ ∈ R ∧
      l1dist (X (A.neighbor u₁)) (X B.shell.center) ≤ a ∧
      b ≤ l1dist (X (A.neighbor u₂)) (X B.shell.center) ∧
      l1dist (X u₁) (X B.shell.center) ≤ a+δ ∧
      b-δ ≤ l1dist (X u₂) (X B.shell.center) := by
  let K := U.filter (fun u => A.neighbor u ∈ R)
  have hKn : K.Nonempty := card_pos.mp (lt_of_lt_of_le (by norm_num : 0<768) hlarge)
  obtain ⟨u₀,hu₀⟩ := hKn
  obtain ⟨B,hB,hint₀⟩ := hinter u₀ (mem_filter.mp hu₀).1
  let ρ := fun u => l1dist (X u) (X B.shell.center)
  obtain ⟨u₁,hu₁,hmin⟩ := K.exists_min_image (fun u => ρ (A.neighbor u)) ⟨u₀,hu₀⟩
  obtain ⟨u₂,hu₂,hmax⟩ := K.exists_max_image (fun u => ρ (A.neighbor u)) ⟨u₀,hu₀⟩
  let a := max B.shell.inner (ρ (A.neighbor u₁))
  let b := min B.shell.outer (ρ (A.neighbor u₂))
  let M := U.filter (fun u => a-δ < ρ u ∧ ρ u < b+δ)
  have hnear (u : Fin n) (hu : u ∈ U) : |ρ u - ρ (A.neighbor u)| < δ :=
    (l1dist_reverse _ _ _).trans_lt (A.neighbor_spec (hU hu)).2.1
  have hr₀ := AssignedSelection.interior_neighbor_in_range A.radius_pos (hmin u₀ hu₀) (hmax u₀ hu₀)
    hint₀.2.1 hint₀.2.2 (hnear u₀ (mem_filter.mp hu₀).1)
  have hMn : M.Nonempty := ⟨u₀,mem_filter.mpr ⟨(mem_filter.mp hu₀).1,hr₀.2⟩⟩
  have hMinter : ∀u ∈ M, (A.input P u).Interior H X 256 δ B := by
    intro u hu
    obtain ⟨hu,hr⟩ := mem_filter.mp hu
    exact A.selected_interior hX hZ hshape horder hinter hB hint₀
      (le_max_left _ _) (min_le_left _ _) hu hr
  have hdich : 768 ≤ M.card ∨ 255*δ ≤ b-a := by
    by_cases hs : K ⊆ M
    · exact Or.inl (hlarge.trans (card_le_card hs))
    · obtain ⟨u,hu,huM⟩ := Finset.not_subset.mp hs
      have hr : ¬(a-δ < ρ u ∧ ρ u < b+δ) :=
        fun hh => huM (mem_filter.mpr ⟨(mem_filter.mp hu).1,hh⟩)
      exact Or.inr (AssignedSelection.radial_range A.radius_pos (hmin u₀ hu₀) (hmax u₀ hu₀)
        hint₀.2.1 hint₀.2.2 (hnear u₀ (mem_filter.mp hu₀).1)
        (hmin u hu) (hmax u hu) (hnear u (mem_filter.mp hu).1) hr)
  have hnear₁ := (abs_lt.mp (hnear u₁ (mem_filter.mp hu₁).1)).2
  have hnear₂ := (abs_lt.mp (hnear u₂ (mem_filter.mp hu₂).1)).1
  refine ⟨B,a,b,M,u₁,u₂,hB,hno u₀ (mem_filter.mp hu₀).1 B hB hint₀,
    le_max_left _ _,min_le_left _ _,hr₀.1,hMn,rfl,hMinter,hdich,
    (mem_filter.mp hu₁).1,(mem_filter.mp hu₂).1,(mem_filter.mp hu₁).2,(mem_filter.mp hu₂).2,
    le_max_right _ _,min_le_right _ _,?_,?_⟩
  · change ρ u₁ ≤ a+δ
    have hh : ρ (A.neighbor u₁) ≤ a := le_max_right _ _
    linarith
  · change b-δ ≤ ρ u₂
    have hh : b ≤ ρ (A.neighbor u₂) := min_le_right _ _
    linarith

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

namespace Record

lemma radialRefines_refl (B : Record n) : B.RadialRefines (H := H) B :=
  ⟨rfl,le_refl _,le_refl _,Subset.refl _⟩

lemma restriction_radialRefines (B : Record n) {a b : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) :
    (B.restriction a b).RadialRefines (H := H) B := ⟨rfl,ha,hb,Subset.refl _⟩

lemma central_radialRefines {B : Record n} (hB : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) {a b c d : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hc : B.shell.inner ≤ c) (hd : d ≤ B.shell.outer) :
    (B.innerRecord t a b).RadialRefines (H := H) B ∧
      (B.outsideRecord t c d).RadialRefines (H := H) B := by
  obtain ⟨h1,h2⟩ := central_conflict H hB hno ht a b c d
  refine ⟨⟨rfl,ha,hb,?_⟩,⟨rfl,hc,hd,?_⟩⟩
  · rw [h1]; exact filter_subset _ _
  · rw [h2]; exact filter_subset _ _

end Record

lemma evolution_interior {δ : ℝ} (hδ : 0 ≤ δ)
    {F Z Z' : Finset (Record n)} (hF : ∀D ∈ F, D.shell.width = δ)
    (hevol : Evolution (H := H) F Z Z') {A : Record n}
    (hh : A.InteriorTo (H := H) (X := X) δ Z') : A.InteriorTo (H := H) (X := X) δ Z := by
  obtain ⟨D,hD,hint⟩ := hh
  rcases hevol D hD with hD | ⟨B,hB,href⟩
  · exact (Record.not_interior_ball H X (by norm_num : (1:ℝ) ≤ 256) hδ A D
      (hF D hD).le hint).elim
  · exact ⟨B,hB,Record.interior_restriction H X href.1 href.2.1 href.2.2.1 href.2.2.2 hint⟩

lemma ownerEvolution_order {t : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    {Z Z' : Finset (Record n)} (hold : ∀B ∈ Z, B.owner ⊂ t → B.owner ∈ P)
    (hevol : OwnerEvolution t Z Z') : ∀B ∈ Z', B.owner ⊂ t → B.owner ∈ P := by
  intro B hB hs
  rcases hevol B hB with hh | ⟨D,hD,hh⟩
  · exact (hs.ne hh).elim
  · rw [hh] at hs ⊢
    exact hold D hD hs

namespace AssignedBag
variable {δ η : ℝ} (A : H.AssignedBag G X δ η)

lemma metadata_evolution {F Z Z' Q : Finset (Record n)}
    (hQ : ∀D ∈ Q, D ∈ F ∨ ∃B ∈ Z, D.RadialRefines (H := H) B)
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    Evolution (H := H) F Z Z' := by
  intro D hD
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,ha,hb⟩
  · exact Or.inr ⟨D,hD,D.radialRefines_refl⟩
  · exact hQ D hD
  · exact Or.inr ⟨B,hB,B.restriction_radialRefines ha hb⟩

lemma metadata_owners {Z Z' Q : Finset (Record n)}
    (hQ : ∀D ∈ Q, D.owner = A.owner ∨ ∃B ∈ Z, D.owner = B.owner)
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    OwnerEvolution A.owner Z Z' := by
  intro D hD
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,_⟩
  · exact Or.inr ⟨D,hD,rfl⟩
  · exact hQ D hD
  · exact Or.inr ⟨B,hB,rfl⟩

lemma metadata_separation {P : Finset (Finset (Fin n))} {U V : Finset (Fin n)}
    (hVU : V ⊆ U) {Z Z' Q F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.width = δ) (hevol : Evolution (H := H) F Z Z')
    (hsep : A.SameOwnerSeparated P U Z)
    (hQ : ∀D ∈ Q, D.owner = A.owner → ∀u ∈ V,
      (A.input P u).InteriorTo (H := H) (X := X) δ Z →
      Disjoint ((RadialShell.ball u δ).support X) (D.shell.support X))
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    A.SameOwnerSeparated P V Z' := by
  intro u hu hint D hD hown
  have hintold := evolution_interior A.radius_pos.le hF hevol hint
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,ha,hb⟩
  · exact hsep u (hVU hu) hintold D hD hown
  · exact hQ D hD hown u hu hintold
  · exact (hsep u (hVU hu) hintold B hB hown).mono_right
      (RadialShell.restriction_subset X B.shell ha hb)

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma metadata_fresh (A : H.AssignedBag G X δ η) {P : Finset (Finset (Fin n))}
    {F Z Z' Q : Finset (Record n)} {M : Finset (Fin n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true)
    (hQ : ∀D ∈ Q, D ∈ F → ∃u ∈ M, D = A.input P u)
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    ∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃u ∈ M, D = A.input P u := by
  intro D hD hDF
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,_⟩
  · exact Or.inl hD
  · exact Or.inr (hQ D hD hDF)
  · exact (Record.restriction_not_fresh hF B a b hDF).elim

lemma avoiding_move (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε : ℝ} (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    {u : Fin n} (hu : u ∈ U) {B : Record n} (hB : B ∈ Z)
    (havoid : B.avoided.isSome = true) (hinter : (A.input P u).Interior H X 256 δ B) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  obtain ⟨Z',hZ',hcredit,hmeta₀⟩ := H.avoiding_operation G X hX A.radius_pos hε
    (fun D hD => ⟨(hF D hD).1,(hF D hD).2.2⟩) hZ (hvalid u (hU hu))
    (hAF u (hU hu)) rfl hB havoid
    (fun D hD hs => by simpa [input,Record.excluded] using horder D hD hs) hinter
  let Q : Finset (Record n) := {A.input P u}
  have hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃E ∈ Z, ∃a b,
      D = E.restriction a b ∧ E.shell.inner ≤ a ∧ b ≤ E.shell.outer := by
    intro D hD
    rcases hmeta₀ D hD with hD | rfl | ⟨a,b,heq,ha,hb,_⟩
    · exact Or.inl hD
    · exact Or.inr (Or.inl (mem_singleton_self _))
    · exact Or.inr (Or.inr ⟨B,hB,a,b,heq,ha,hb⟩)
  have hevol : Evolution (H := H) F Z Z' := metadata_evolution
    (fun D hD => Or.inl ((mem_singleton.mp hD).symm ▸ hAF u (hU hu))) hmeta
  have howner : OwnerEvolution A.owner Z Z' := A.metadata_owners
    (fun D hD => Or.inl (by rw [mem_singleton.mp hD]; rfl)) hmeta
  have hfresh := A.metadata_fresh (fun D hD => (hF D hD).1)
    (M := {u}) (by
      intro D hD _
      exact ⟨u,mem_singleton_self _,mem_singleton.mp hD⟩) hmeta
  have hsep' : A.SameOwnerSeparated P (U\{u}) Z' := by
    apply A.metadata_separation sdiff_subset (fun D hD => (hF D hD).2.1) hevol hsep _ hmeta
    intro D hD _ v hv _
    rw [mem_singleton.mp hD]
    obtain ⟨hv,hvu⟩ := mem_sdiff.mp hv
    exact A.disjoint (hU hv) (hU hu) (by simpa only [mem_singleton] using hvu)
  refine ⟨⟨{u},Z',singleton_nonempty _,?_,hZ',?_,hevol,howner,hfresh,hsep'⟩⟩
  · intro v hv
    rw [mem_singleton.mp hv]
    exact ⟨hu,⟨B,hB,hinter⟩⟩
  · simpa only [card_singleton,Nat.cast_one,mul_one] using hcredit

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.BagConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma dense_move (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε a b : ℝ} (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U M : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    {B : Record n} (hB : B ∈ Z) (hno : B.avoided = none)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) (hab : a ≤ b)
    (hMn : M.Nonempty) (hMU : M ⊆ U)
    (hinter : ∀u ∈ M, (A.input P u).Interior H X 256 δ B)
    (hrange : ∀u ∈ M, a-δ < l1dist (X u) (X B.shell.center) ∧
      l1dist (X u) (X B.shell.center) < b+δ)
    (hcount : 765*δ ≤ (M.card : ℝ)*δ) (hdense : 3*(b-a) ≤ (M.card : ℝ)*δ) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  let Q := M.image (A.input P)
  have hQcard : Q.card = M.card := card_image_of_injective _ (A.input_injective P)
  obtain ⟨u₀,hu₀⟩ := hMn
  have hwidth := Record.interior_width H X (hinter u₀ hu₀)
  obtain ⟨Z',hZ',hcredit,hmeta₀⟩ := H.dense_operation G X hX A.radius_pos hε hF hZ hB
    (A.input_arrangement (hMU.trans hU) (fun u hu => hvalid u (hU (hMU hu))))
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; exact hAF u (hU (hMU hu)))
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; rfl) hno hwidth ha hb hab
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; exact hrange u hu)
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; exact hinter u hu)
    (by intro D hD E hE hs; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
        simpa [input,Record.excluded] using horder E hE hs)
    (by rwa [hQcard]) (by rwa [hQcard])
  have hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃E ∈ Z, ∃a b,
      D = E.restriction a b ∧ E.shell.inner ≤ a ∧ b ≤ E.shell.outer := by
    intro D hD
    rcases hmeta₀ D hD with hD | hD | ⟨a,b,heq,ha,hb,_⟩
    · exact Or.inl hD
    · exact Or.inr (Or.inl hD)
    · exact Or.inr (Or.inr ⟨B,hB,a,b,heq,ha,hb⟩)
  have hevol : Evolution (H := H) F Z Z' := metadata_evolution (by
    intro D hD
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    exact Or.inl (hAF u (hU (hMU hu)))) hmeta
  have howner : OwnerEvolution A.owner Z Z' := A.metadata_owners (by
    intro D hD
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    exact Or.inl rfl) hmeta
  have hfresh := A.metadata_fresh (fun D hD => (hF D hD).1)
    (M := M) (by
      intro D hD _
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
      exact ⟨u,hu,rfl⟩) hmeta
  have hsep' : A.SameOwnerSeparated P (U\M) Z' := by
    apply A.metadata_separation sdiff_subset (fun D hD => (hF D hD).2.1) hevol hsep _ hmeta
    intro D hD _ v hv _
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    obtain ⟨hv,hvM⟩ := mem_sdiff.mp hv
    exact A.disjoint (hU hv) (hU (hMU hu)) (fun hh => hvM (hh ▸ hu))
  refine ⟨⟨M,Z',⟨u₀,hu₀⟩,fun u hu => ⟨hMU hu,⟨B,hB,hinter u hu⟩⟩,
    hZ',?_,hevol,howner,hfresh,hsep'⟩⟩
  rwa [hQcard] at hcredit

lemma sparse_move (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε a b : ℝ} {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U M : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    {B : Record n} (hB : B ∈ Z) (hno : B.avoided = none)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hMn : M.Nonempty) (hMU : M ⊆ U)
    (hinter : ∀u ∈ M, (A.input P u).Interior H X 256 δ B)
    (hexact : ∀u ∈ U, (A.input P u).InteriorTo (H := H) (X := X) δ Z →
      a-δ < l1dist (X u) (X B.shell.center) →
      l1dist (X u) (X B.shell.center) < b+δ → u ∈ M)
    (hwide : 255*δ ≤ b-a) (hsparse : (M.card : ℝ)*δ ≤ 3*(b-a))
    (hinner : (B.innerRecord A.owner (a+δ) (b-δ)).Valid H G X (q/4))
    (houter : (B.outsideRecord A.owner a b).Valid H G X (q/4)) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  obtain ⟨u₀,hu₀⟩ := hMn
  have hint := hinter u₀ hu₀
  have hov := hvalid u₀ (hU (hMU hu₀))
  have ht := Record.candidate_ancestor H hov.1 (hZ.1 B hB).1
    (fun hs => by simpa [input,Record.excluded] using horder B hB hs) hint.1
  have hstrict : A.owner ⊂ B.owner := Record.strict_owner_of_interior hX
    hov.1 (hZ.1 B hB).1 hov.2.2.1 A.radius_pos.le rfl
    (fun hs => by simpa [input,Record.excluded] using horder B hB hs) (hsep u₀ (hMU hu₀) ⟨B,hB,hint⟩ B hB) hint
  obtain ⟨Z',hZ',hcredit,hmeta₀⟩ := H.sparse_operation G X hX A.radius_pos
    (fun D hD => ⟨(hF D hD).1,(hF D hD).2.1⟩) hZ hB hno
    (Record.interior_width H X hint) ht ha hb hwide hsparse hinner houter
  let C := B.innerRecord A.owner (a+δ) (b-δ)
  let D := B.outsideRecord A.owner a b
  let Q : Finset (Record n) := {C,D}
  have hmeta : ∀E ∈ Z', E ∈ Z ∨ E ∈ Q ∨ ∃K ∈ Z, ∃c d,
      E = K.restriction c d ∧ K.shell.inner ≤ c ∧ d ≤ K.shell.outer := by
    intro E hE
    rcases hmeta₀ E hE with hE | rfl | rfl | ⟨c,d,heq,hc,hd,_⟩
    · exact Or.inl hE
    · exact Or.inr (Or.inl (mem_insert_self _ _))
    · exact Or.inr (Or.inl (mem_insert_of_mem (mem_singleton_self _)))
    · exact Or.inr (Or.inr ⟨B,hB,c,d,heq,hc,hd⟩)
  have href := Record.central_radialRefines (hZ.1 B hB).1 hno ht
    (by linarith [A.radius_pos] : B.shell.inner ≤ a+δ)
    (by linarith [A.radius_pos] : b-δ ≤ B.shell.outer) ha hb
  have hevol : Evolution (H := H) F Z Z' := metadata_evolution (by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact Or.inr ⟨B,hB,href.1⟩
    · rw [mem_singleton.mp hE]
      exact Or.inr ⟨B,hB,href.2⟩) hmeta
  have howner : OwnerEvolution A.owner Z Z' := A.metadata_owners (by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact Or.inl rfl
    · rw [mem_singleton.mp hE]
      exact Or.inr ⟨B,hB,rfl⟩) hmeta
  have hfresh := A.metadata_fresh (fun D hD => (hF D hD).1)
    (P := P) (M := M) (by
      intro E hE hEF
      have hh := (hF E hEF).1
      rcases mem_insert.mp hE with rfl | hE
      · simp [C,Record.innerRecord,RadialShell.hollow] at hh
      · rw [mem_singleton.mp hE] at hh
        simp [D,Record.outsideRecord,RadialShell.hollow] at hh) hmeta
  have hsep' : A.SameOwnerSeparated P (U\M) Z' := by
    apply A.metadata_separation sdiff_subset (fun D hD => (hF D hD).2.1) hevol hsep _ hmeta
    intro E hE hown u hu hintold
    rcases mem_insert.mp hE with rfl | hE
    · obtain ⟨hu,huM⟩ := mem_sdiff.mp hu
      by_cases hlo : a-δ < l1dist (X u) (X B.shell.center)
      · have hhi : b+δ ≤ l1dist (X u) (X B.shell.center) :=
          le_of_not_gt (fun hh => huM (hexact u hu hintold hlo hh))
        exact RadialShell.ball_disjoint_hollow_lower X _ _ (by linarith [A.radius_pos])
      · exact RadialShell.ball_disjoint_hollow_upper X _ _ (by
          have := not_lt.mp hlo
          linarith [A.radius_pos])
    · rw [mem_singleton.mp hE] at hown
      exact (hstrict.ne hown.symm).elim
  exact ⟨⟨M,Z',⟨u₀,hu₀⟩,fun u hu => ⟨hMU hu,⟨B,hB,hinter u hu⟩⟩,
    hZ',hcredit,hevol,howner,hfresh,hsep'⟩⟩

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma interior_move (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε : ℝ} (hq : 0 < q) (hconn : H.LocallyConnectedReal G q)
    (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    (hhalf : A.centers.card ≤ 2*(U.filter (fun u =>
      (A.input P u).InteriorTo (H := H) (X := X) δ Z)).card) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  by_cases hav : ∃u ∈ U, ∃B ∈ Z, B.avoided.isSome = true ∧
      (A.input P u).Interior H X 256 δ B
  · obtain ⟨u,hu,B,hB,hav,hint⟩ := hav
    exact A.avoiding_move hX hε hU hF hAF hvalid hZ horder hsep hu hB hav hint
  let I := U.filter (fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z)
  have hIU : I ⊆ U := by
    intro u hu
    exact (mem_filter.mp hu).1
  have hI : ∀u ∈ I, (A.input P u).InteriorTo (H := H) (X := X) δ Z :=
    fun u hu => (mem_filter.mp hu).2
  obtain ⟨R,hR,hRc,hlarge⟩ := A.large_component hq hconn hη (hIU.trans hU) hhalf
  have hno : ∀u ∈ I, ∀D ∈ Z, (A.input P u).Interior H X 256 δ D → D.avoided = none := by
    intro u hu D hD hint
    cases hh : D.avoided with
    | none => rfl
    | some t => exact (hav ⟨u,hIU hu,D,hD,by simp [hh],hint⟩).elim
  obtain ⟨B,a,b,M,u₁,u₂,hB,hBno,ha,hb,hab,hMn,hMeq,hinter,hdich,
    hu₁,hu₂,hv₁,hv₂,hv₁r,hv₂r,hu₁r,hu₂r⟩ := A.radial_group hX (hIU.trans hU) hZ
      (fun u hu => (hvalid u (hU (hIU hu))).1) horder hI hno hlarge
  have hMI : M ⊆ I := by rw [hMeq]; exact filter_subset _ _
  have hMU : M ⊆ U := hMI.trans hIU
  have hrange : ∀u ∈ M, a-δ < l1dist (X u) (X B.shell.center) ∧
      l1dist (X u) (X B.shell.center) < b+δ := by
    intro u hu
    rw [hMeq] at hu
    exact (mem_filter.mp hu).2
  have hdich' : (768:ℝ) ≤ M.card ∨ 255*δ ≤ b-a := by exact_mod_cast hdich
  by_cases hdense : 3*(b-a) ≤ (M.card : ℝ)*δ
  · have hcount := AssignedSelection.dense_count A.radius_pos.le (by norm_num : (768:ℝ) ≤ 768)
      hdich' hdense
    exact A.dense_move hX hε hU hF hAF hvalid hZ horder hsep hB hBno ha hb hab
      hMn hMU hinter hrange hcount hdense
  · have hsparse : (M.card : ℝ)*δ ≤ 3*(b-a) := (not_le.mp hdense).le
    have hwide := AssignedSelection.sparse_width A.radius_pos.le (by norm_num : (768:ℝ) ≤ 768)
      hdich' hsparse
    obtain ⟨u₀,hu₀⟩ := hMn
    have hint := hinter u₀ hu₀
    have hov := hvalid u₀ (hU (hMU hu₀))
    have ht := Record.candidate_ancestor H hov.1 (hZ.1 B hB).1 (fun hs => by simpa [input,Record.excluded] using horder B hB hs) hint.1
    have hstrict : A.owner ⊂ B.owner := Record.strict_owner_of_interior hX
      hov.1 (hZ.1 B hB).1 hov.2.2.1 A.radius_pos.le rfl
      (fun hs => by simpa [input,Record.excluded] using horder B hB hs) (hsep u₀ (hMU hu₀) ⟨B,hB,hint⟩ B hB) hint
    obtain ⟨e,he⟩ := (A.neighbor_spec (hU (hIU hu₁))).2.2
    obtain ⟨hin,hout⟩ := Record.central_valid H G X (hZ.1 B hB) hBno hq.le hconn ht hstrict
      ha hb A.radius_pos (by linarith [A.radius_pos]) hR hRc
      (A.endpoint u₁ (hU (hIU hu₁))).1 (A.endpoint u₂ (hU (hIU hu₂))).1
      hv₁ hv₂ hu₁r hu₂r hv₁r hv₂r he
    apply A.sparse_move hX hU hF hvalid hZ horder hsep hB hBno ha hb ⟨u₀,hu₀⟩ hMU
      hinter _ hwide hsparse hin hout
    intro u hu hint hlo hhi
    rw [hMeq]
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hu,hint⟩,hlo,hhi⟩

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}

lemma ownerEvolution_refl (t : Finset (Fin n)) (Z : Finset (Record n)) : OwnerEvolution t Z Z := by
  intro D hD
  exact Or.inr ⟨D,hD,rfl⟩

lemma ownerEvolution_trans {t : Finset (Fin n)} {Z W V : Finset (Record n)}
    (h1 : OwnerEvolution t Z W) (h2 : OwnerEvolution t W V) : OwnerEvolution t Z V := by
  intro D hD
  rcases h2 D hD with hh | ⟨E,hE,hh⟩
  · exact Or.inl hh
  · rcases h1 E hE with he | ⟨B,hB,he⟩
    · exact Or.inl (hh.trans he)
    · exact Or.inr ⟨B,hB,hh.trans he⟩

namespace AssignedBag

lemma interior_loop (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε : ℝ} (hq : 0 < q) (hconn : H.LocallyConnectedReal G q)
    (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (U : Finset (Fin n)) (hU : U ⊆ A.centers) (Z : Finset (Record n))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z) :
    ∃(V : Finset (Fin n)) (Z' : Finset (Record n)), V ⊆ U ∧
      H.LabeledArrangement G X (q/4) Z' ∧
      2*(V.filter (fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z')).card <
        A.centers.card ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+
        AssignedAccounting.theta*((U.card : ℝ)-(V.card : ℝ))*δ ≤
          ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      (∀B : Record n, B.InteriorTo (H := H) (X := X) δ Z' →
        B.InteriorTo (H := H) (X := X) δ Z) ∧
      OwnerEvolution A.owner Z Z' ∧
      (∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃u ∈ U\V, D = A.input P u) ∧
      A.SameOwnerSeparated P V Z' := by
  induction U using Finset.strongInduction generalizing Z with
  | H U ih =>
    by_cases hstop : 2*(U.filter (fun u =>
        (A.input P u).InteriorTo (H := H) (X := X) δ Z)).card < A.centers.card
    · refine ⟨U,Z,Subset.refl _,hZ,hstop,?_,fun _ h => h,ownerEvolution_refl _ _,
        fun _ h _ => Or.inl h,hsep⟩
      simp
    · obtain ⟨W⟩ := A.interior_move hX hq hconn hη hε hU hF hAF hvalid hZ horder hsep
        (not_lt.mp hstop)
      have hMU : W.treated ⊆ U := fun u hu => (W.treated_interior u hu).1
      have hss : U\W.treated ⊂ U := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨sdiff_subset,?_⟩
        intro hh
        obtain ⟨u,hu⟩ := W.nonempty
        have hm : u ∈ U\W.treated := hh.symm ▸ hMU hu
        exact (mem_sdiff.mp hm).2 hu
      obtain ⟨V,Z',hVU,hZ',hstop',hcredit',hinter',howners',hfresh',hsep'⟩ := ih (U\W.treated) hss
        (sdiff_subset.trans hU) W.next W.valid (ownerEvolution_order horder W.owners) W.separation
      have hcards : ((U\W.treated).card : ℝ)+(W.treated.card : ℝ) = (U.card : ℝ) := by
        exact_mod_cast card_sdiff_add_card_eq_card hMU
      refine ⟨V,Z',hVU.trans sdiff_subset,hZ',hstop',?_,?_,
        ownerEvolution_trans W.owners howners',?_,hsep'⟩
      · calc
          (∑D ∈ Z, Record.phaseToken F δ ε D)+
              AssignedAccounting.theta*((U.card : ℝ)-(V.card : ℝ))*δ =
            ((∑D ∈ Z, Record.phaseToken F δ ε D)+
              AssignedAccounting.theta*(W.treated.card : ℝ)*δ)+
              AssignedAccounting.theta*(((U\W.treated).card : ℝ)-(V.card : ℝ))*δ := by
                rw [←hcards]
                ring
          _ ≤ (∑D ∈ W.next, Record.phaseToken F δ ε D)+
              AssignedAccounting.theta*(((U\W.treated).card : ℝ)-(V.card : ℝ))*δ :=
            add_le_add W.credit (le_refl _)
          _ ≤ _ := hcredit'
      · intro B hB
        exact evolution_interior A.radius_pos.le (fun D hD => (hF D hD).2.1)
          W.evolution (hinter' B hB)
      · intro D hD hDF
        rcases hfresh' D hD hDF with hD | ⟨u,hu,heq⟩
        · rcases W.fresh D hD hDF with hD | ⟨u,hu,heq⟩
          · exact Or.inl hD
          · exact Or.inr ⟨u,mem_sdiff.mpr ⟨hMU hu,
              fun hv => (mem_sdiff.mp (hVU hv)).2 hu⟩,heq⟩
        · exact Or.inr ⟨u,mem_sdiff.mpr ⟨sdiff_subset (mem_sdiff.mp hu).1,
            (mem_sdiff.mp hu).2⟩,heq⟩

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}
namespace Record

lemma fresh_base {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536)
    {B : Record n} (hwidth : B.shell.width = δ) (hno : B.avoided = none) :
    B.baseToken ε = AssignedAccounting.fresh δ ε := by
  simp only [baseToken,hwidth,hno,Option.isSome_none,AssignedAccounting.base,
    Bool.false_eq_true,↓reduceIte,AssignedAccounting.fresh,div_one]
  exact max_eq_left (by linarith)

lemma shrink_refines {δ : ℝ} (hδ : 0 ≤ δ) (F : Finset (Record n)) (B : Record n) :
    (B.shrinkRecord F δ).Refines H X B := by
  by_cases hB : B ∈ F
  · simp only [shrinkRecord,ite_eq_left hB]
    exact ⟨Set.Subset.refl _,Subset.refl _⟩
  · simp only [shrinkRecord,ite_eq_right hB]
    exact B.restriction_refines H X (by linarith) (by linarith)

lemma shrink_valid {δ q : ℝ} (hδ : 0 ≤ δ) {F : Finset (Record n)} {B : Record n}
    (hB : B.Valid H G X q) (hw : 0 < (B.shrinkRecord F δ).shell.width) :
    (B.shrinkRecord F δ).Valid H G X q := by
  by_cases hf : B ∈ F
  · simpa only [shrinkRecord,ite_eq_left hf] using hB
  · simp only [shrinkRecord,ite_eq_right hf] at hw ⊢
    exact Record.restrict_valid H G X hB (by linarith) (by linarith)
      (by simpa only [restriction,RadialShell.hollow,RadialShell.width,sub_pos] using hw)

lemma shrink_base {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536)
    {F : Finset (Record n)} (hF : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none)
    (B : Record n) : (B.shrinkRecord F δ).baseToken ε = B.shrinkValue F δ ε := by
  by_cases hf : B ∈ F
  · simp only [shrinkRecord,shrinkValue,ite_eq_left hf]
    exact fresh_base hδ hε (hF B hf).1 (hF B hf).2
  · simp only [shrinkRecord,shrinkValue,ite_eq_right hf,baseToken,restriction,RadialShell.hollow,
      RadialShell.width]
    congr 1
    ring

lemma shrink_cost {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536)
    {F : Finset (Record n)} (hF : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none)
    (B : Record n) :
    0 ≤ B.phaseToken F δ ε-B.shrinkValue F δ ε ∧
      B.phaseToken F δ ε-B.shrinkValue F δ ε ≤
        256*(B.baseToken ε-B.phaseToken F δ ε) := by
  by_cases hf : B ∈ F
  · rw [phaseToken,shrinkValue,ite_eq_left hf,ite_eq_left hf,
      fresh_base hδ hscale (hF B hf).1 (hF B hf).2]
    simp
  · simp only [phaseToken,shrinkValue,ite_eq_right hf,baseToken]
    exact AssignedAccounting.shrink_cost _ hδ hε hscale

lemma shrink_discard {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    {F : Finset (Record n)} (hF : ∀B ∈ F, B.shell.width = δ)
    (B : Record n) (hw : ¬0 < (B.shrinkRecord F δ).shell.width) :
    B.shrinkValue F δ ε = 0 := by
  by_cases hf : B ∈ F
  · rw [shrinkRecord,ite_eq_left hf,hF B hf] at hw
    exact (hw hδ).elim
  · rw [shrinkValue,ite_eq_right hf]
    apply AssignedAccounting.base_discard _ _ hε
    rw [shrinkRecord,ite_eq_right hf] at hw
    dsimp [restriction,RadialShell.hollow,RadialShell.width] at hw ⊢
    linarith [not_lt.mp hw]

lemma border_shrink_compatible {δ : ℝ} (_hδ : 0 ≤ δ) {F : Finset (Record n)}
    (hF : ∀A ∈ F, ∀B ∈ F, A ≠ B → Disjoint (A.shell.support X) (B.shell.support X))
    {A B : Record n} (hA : A ∈ F) (hne : A ≠ B)
    (hball : A.shell = RadialShell.ball A.shell.center δ)
    (hbor : ¬A.Interior H X 256 δ B) :
    A.Compatible H X (B.shrinkRecord F δ) := by
  by_cases hf : B ∈ F
  · simp only [shrinkRecord,ite_eq_left hf]
    exact Or.inl (hF A hA B hf hne)
  · simp only [shrinkRecord,ite_eq_right hf]
    by_cases hdis : Disjoint (A.conflict H) (B.conflict H)
    · exact Or.inr hdis
    · have hmeet : (A.conflict H ∩ B.conflict H).Nonempty := by
        apply nonempty_iff_ne_empty.mpr
        exact fun hh => hdis (Finset.disjoint_iff_inter_eq_empty.mpr hh)
      left
      rw [hball]
      by_cases hlo : B.shell.inner+256*δ < l1dist (X A.shell.center) (X B.shell.center)
      · have hhi : B.shell.outer-256*δ ≤ l1dist (X A.shell.center) (X B.shell.center) :=
          le_of_not_gt (fun hh => hbor ⟨hmeet,hlo,hh⟩)
        exact RadialShell.ball_disjoint_hollow_lower X _ _ (by linarith)
      · exact RadialShell.ball_disjoint_hollow_upper X _ _ (by linarith [not_lt.mp hlo])

end Record

lemma shrinkFamily_valid {q δ : ℝ} (hδ : 0 ≤ δ) {F Z : Finset (Record n)}
    (hZ : H.LabeledArrangement G X q Z) : H.LabeledArrangement G X q (shrinkFamily F Z δ) := by
  constructor
  · intro D hD
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
    exact Record.shrink_valid hδ (hZ.1 B (mem_filter.mp hB).1) (mem_filter.mp hB).2
  · intro D hD E hE hne hgeo
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hE
    have hh := Record.compatible_refinements H X
      (H.labeled_pair G X hZ (mem_filter.mp hB).1 (mem_filter.mp hC).1
        (fun hh => hne (congrArg (Record.shrinkRecord F δ) hh)))
      (Record.shrink_refines hδ F B) (Record.shrink_refines hδ F C)
    exact hh.resolve_left hgeo

lemma shrinkFamily_sum (hX : ∀v, binary (X v)) {q δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536) {F Z : Finset (Record n)}
    (hF : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none)
    (hZ : H.LabeledArrangement G X q Z) :
    ∑D ∈ shrinkFamily F Z δ, D.baseToken ε = ∑B ∈ Z, B.shrinkValue F δ ε := by
  have hinj : ∀B ∈ Z.filter (fun B => 0 < (B.shrinkRecord F δ).shell.width),
      ∀C ∈ Z.filter (fun B => 0 < (B.shrinkRecord F δ).shell.width),
      B.shrinkRecord F δ = C.shrinkRecord F δ → B = C := by
    intro B hB C hC heq
    by_contra hh
    have hv := Record.shrink_valid hδ.le (hZ.1 B (mem_filter.mp hB).1) (mem_filter.mp hB).2
    have hc := Record.compatible_refinements H X
      (H.labeled_pair G X hZ (mem_filter.mp hB).1 (mem_filter.mp hC).1 hh)
      (Record.shrink_refines hδ.le F B) (Record.shrink_refines hδ.le F C)
    rw [←heq] at hc
    exact (B.shrinkRecord F δ).compatible_self_iff H X hX hv.1 hv.2.2.1 hc
  rw [shrinkFamily,sum_image hinj,sum_filter]
  apply sum_congr rfl
  intro B hB
  by_cases hw : 0 < (B.shrinkRecord F δ).shell.width
  · rw [ite_eq_left hw,Record.shrink_base hδ.le hscale hF]
  · rw [ite_eq_right hw,Record.shrink_discard hδ hε (fun D hD => (hF D hD).1) B hw]

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Phases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uι2

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma border_transition (hX : ∀v, binary (X v)) {q δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536)
    {F Z K : Finset (Record n)}
    (hF : ∀B ∈ F, B.shell.ordinary = true ∧ B.shell.width = δ ∧ B.avoided = none)
    (hFball : ∀B ∈ F, B.shell = RadialShell.ball B.shell.center δ)
    (hFgeo : ∀A ∈ F, ∀B ∈ F, A ≠ B → Disjoint (A.shell.support X) (B.shell.support X))
    (hFvalid : H.LabeledArrangement G X q F)
    (hZ : H.LabeledArrangement G X q Z) (hKF : K ⊆ F) (hKZ : Disjoint K Z)
    (hbor : ∀A ∈ K, ¬A.InteriorTo (H := H) (X := X) δ Z) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X q Z' ∧
      (∑B ∈ Z, B.phaseToken F δ ε)+AssignedAccounting.theta*(K.card : ℝ)*δ ≤
        ∑B ∈ Z', B.baseToken ε ∧
      (∀D ∈ Z', D ∈ K ∨ ∃B ∈ Z, D.owner = B.owner) := by
  let p := ∑B ∈ Z, B.phaseToken F δ ε
  let q' := ∑B ∈ Z, B.baseToken ε
  have hw : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none :=
    fun B hB => (hF B hB).2
  by_cases hex : AssignedAccounting.theta*(K.card : ℝ)*δ ≤ q'-p
  · exact ⟨Z,hZ,by dsimp [p,q'] at *; linarith,fun D hD => Or.inr ⟨D,hD,rfl⟩⟩
  let W := shrinkFamily F Z δ
  have hW : H.LabeledArrangement G X q W := shrinkFamily_valid hδ.le hZ
  have hK := H.labeled_subset G X hFvalid hKF
  have hKW : ∀A ∈ K, ∀B ∈ W, A.Compatible H X B := by
    intro A hA D hD
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
    have hBZ : B ∈ Z := (mem_filter.mp hB).1
    exact Record.border_shrink_compatible hδ.le hFgeo (hKF hA)
      (fun heq => Finset.disjoint_left.mp hKZ hA (heq.symm ▸ hBZ))
      (hFball A (hKF hA)) (fun hh => hbor A hA ⟨B,hBZ,hh⟩)
  have hdis : Disjoint K W := H.labeled_sets_disjoint G X hX hK hKW
  have hsum : ∑B ∈ W, B.baseToken ε = ∑B ∈ Z, B.shrinkValue F δ ε :=
    shrinkFamily_sum hX hδ hε hscale hw hZ
  have hkSum : ∑B ∈ K, B.baseToken ε = (K.card : ℝ)*AssignedAccounting.fresh δ ε := by
    calc
      ∑B ∈ K, B.baseToken ε = ∑B ∈ K, AssignedAccounting.fresh δ ε :=
        sum_congr rfl (fun B hB => Record.fresh_base hδ.le hscale (hw B (hKF hB)).1 (hw B (hKF hB)).2)
      _ = _ := by simp
  have hcost : p-(∑B ∈ W, B.baseToken ε) ≤ 256*(q'-p) := by
    rw [hsum]
    dsimp [p,q']
    rw [←sum_sub_distrib,←sum_sub_distrib,Finset.mul_sum]
    exact sum_le_sum (fun B hB => (Record.shrink_cost hδ.le hε hscale hw B).2)
  have hdef : p-(∑B ∈ W, B.baseToken ε) ≤ (K.card : ℝ)*δ/2 := by
    have hh := not_le.mp hex
    dsimp [AssignedAccounting.theta] at hh
    linarith
  have hpay := AssignedAccounting.border_payment hδ.le hscale
    (Nat.cast_nonneg K.card : (0:ℝ) ≤ _) hdef
  refine ⟨K∪W,H.labeled_union G X hK hW hKW,?_,?_⟩
  · rw [sum_union hdis,hkSum]
    dsimp [p] at hpay
    linarith
  · intro D hD
    rcases mem_union.mp hD with hD | hD
    · exact Or.inl hD
    · obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
      refine Or.inr ⟨B,(mem_filter.mp hB).1,?_⟩
      dsimp [Record.shrinkRecord]
      split_ifs <;> rfl

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma loop_with_border_debt (A : H.AssignedBag G X δ η) (hX : ∀v, binary (X v))
    {q ε : ℝ} (hq : 0 < q) (hconn : H.LocallyConnectedReal G q)
    (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (howner : ∀D ∈ Z, D.owner ≠ A.owner) :
    ∃(Z' K : Finset (Record n)), H.LabeledArrangement G X (q/4) Z' ∧
      K ⊆ A.centers.image (A.input P) ∧ Disjoint K Z' ∧
      (∀B ∈ K, ¬B.InteriorTo (H := H) (X := X) δ Z') ∧
      (∑D ∈ Z, D.phaseToken F δ ε)+
        (AssignedAccounting.theta/2)*(A.centers.card : ℝ)*δ ≤
          (∑D ∈ Z', D.phaseToken F δ ε)+AssignedAccounting.theta*(K.card : ℝ)*δ ∧
      (∀B : Record n, B.InteriorTo (H := H) (X := X) δ Z' →
        B.InteriorTo (H := H) (X := X) δ Z) ∧
      OwnerEvolution A.owner Z Z' ∧
      (∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃u ∈ A.centers, D = A.input P u) := by
  obtain ⟨V,Z',hVA,hZ',hstop,hcredit,hinter,howners,hfresh,_⟩ :=
    A.interior_loop hX hq hconn hη hε hF hAF hvalid A.centers (Subset.refl _) Z hZ horder
      (fun u hu hint B hB hh => (howner B hB hh).elim)
  let I := V.filter (fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z')
  let B := V.filter (fun u => ¬(A.input P u).InteriorTo (H := H) (X := X) δ Z')
  let K := B.image (A.input P)
  have hKV : ∀D ∈ K, ∃u ∈ V, D = A.input P u ∧
      ¬D.InteriorTo (H := H) (X := X) δ Z' := by
    intro D hD
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    exact ⟨u,(mem_filter.mp hu).1,rfl,(mem_filter.mp hu).2⟩
  have hKcard : K.card = B.card := card_image_of_injective _ (A.input_injective P)
  have hcards : (I.card : ℝ)+(K.card : ℝ) = (V.card : ℝ) := by
    rw [hKcard]
    exact_mod_cast card_filter_add_card_filter_not (s := V)
      (p := fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z')
  have hI : 2*(I.card : ℝ) < A.centers.card := by exact_mod_cast hstop
  have hcount : (A.centers.card : ℝ)/2 ≤ (A.centers.card : ℝ)-(V.card : ℝ)+(K.card : ℝ) := by
    linarith
  have hnum := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcount (by norm_num [AssignedAccounting.theta] :
      (0:ℝ) ≤ AssignedAccounting.theta)) A.radius_pos.le
  refine ⟨Z',K,hZ',?_,?_,fun D hD => (hKV D hD).choose_spec.2.2,?_,hinter,howners,?_⟩
  · intro D hD
    obtain ⟨u,hu,rfl,_⟩ := hKV D hD
    exact mem_image.mpr ⟨u,hVA hu,rfl⟩
  · rw [Finset.disjoint_left]
    intro D hD hDZ
    obtain ⟨u,hu,rfl,_⟩ := hKV D hD
    rcases hfresh _ hDZ (hAF u (hVA hu)) with hh | ⟨v,hv,heq⟩
    · exact howner _ hh rfl
    · have he : u = v := A.input_injective P heq
      exact (mem_sdiff.mp hv).2 (he ▸ hu)
  · dsimp [AssignedAccounting.theta] at hnum hcredit ⊢
    linarith
  · intro D hD hDF
    rcases hfresh D hD hDF with hh | ⟨u,hu,heq⟩
    · exact Or.inl hh
    · exact Or.inr ⟨u,(mem_sdiff.mp hu).1,heq⟩

end AssignedBag
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}

lemma phase_loops {ι : Type uι} [DecidableEq ι]
    (A : ι → H.AssignedBag G X δ η) (P : ι → Finset (Finset (Fin n)))
    (hX : ∀v, binary (X v)) {q ε : ℝ} (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536)
    {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (J : Finset ι) (hAi : Set.InjOn (fun i => (A i).owner) J)
    (hAF : ∀i ∈ J, ∀u ∈ (A i).centers, (A i).input (P i) u ∈ F)
    (hvalid : ∀i ∈ J, ∀u ∈ (A i).centers, ((A i).input (P i) u).Valid H G X (q/4))
    (Z : Finset (Record n)) (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀i ∈ J, ∀D ∈ Z, D.owner ⊂ (A i).owner → D.owner ∈ P i)
    (howner : ∀i ∈ J, ∀D ∈ Z, D.owner ≠ (A i).owner) :
    ∃(Z' K : Finset (Record n)), H.LabeledArrangement G X (q/4) Z' ∧ K ⊆ F ∧
      (∀D ∈ K, ∃i ∈ J, D.owner = (A i).owner) ∧ Disjoint K Z' ∧
      (∀B ∈ K, ¬B.InteriorTo (H := H) (X := X) δ Z') ∧
      (∑D ∈ Z, D.phaseToken F δ ε)+
        (AssignedAccounting.theta/2)*(∑i ∈ J, ((A i).centers.card : ℝ))*δ ≤
          (∑D ∈ Z', D.phaseToken F δ ε)+AssignedAccounting.theta*(K.card : ℝ)*δ ∧
      (∀B : Record n, B.InteriorTo (H := H) (X := X) δ Z' →
        B.InteriorTo (H := H) (X := X) δ Z) ∧
      (∀D ∈ Z', (∃i ∈ J, D.owner = (A i).owner) ∨ ∃B ∈ Z, D.owner = B.owner) ∧
      (∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃i ∈ J, ∃u ∈ (A i).centers, D = (A i).input (P i) u) := by
  induction J using Finset.strongInduction generalizing Z with
  | H J ih =>
    by_cases hn : J.Nonempty
    · obtain ⟨j,hj,hmax⟩ := J.exists_max_image (fun i => (A i).owner.card) hn
      obtain ⟨Z₁,K₁,hZ₁,hKA,hKZ₁,hbor₁,hcredit₁,hint₁,hown₁,hfresh₁⟩ :=
        (A j).loop_with_border_debt hX hq hconn hη hε hF (hAF j hj) (hvalid j hj)
          hZ (horder j hj) (howner j hj)
      have hKi : ∀D ∈ K₁, ∃u ∈ (A j).centers, D = (A j).input (P j) u := by
        intro D hD
        obtain ⟨u,hu,heq⟩ := mem_image.mp (hKA hD)
        exact ⟨u,hu,heq.symm⟩
      have hKown : ∀D ∈ K₁, D.owner = (A j).owner := by
        intro D hD
        obtain ⟨u,hu,rfl⟩ := hKi D hD
        rfl
      have hKAf : K₁ ⊆ F := by
        intro D hD
        obtain ⟨u,hu,rfl⟩ := hKi D hD
        exact hAF j hj u hu
      have hInj : Set.InjOn (fun i => (A i).owner) (J.erase j) := hAi.mono (erase_subset _ _)
      have horder₁ : ∀i ∈ J.erase j, ∀D ∈ Z₁, D.owner ⊂ (A i).owner → D.owner ∈ P i := by
        intro i hi D hD hs
        rcases hown₁ D hD with hh | ⟨B,hB,hh⟩
        · rw [hh] at hs
          have hcard := card_lt_card hs
          have hmax := hmax i (mem_of_mem_erase hi)
          omega
        · rw [hh] at hs ⊢
          exact horder i (mem_of_mem_erase hi) B hB hs
      have howner₁ : ∀i ∈ J.erase j, ∀D ∈ Z₁, D.owner ≠ (A i).owner := by
        intro i hi D hD heq
        rcases hown₁ D hD with hh | ⟨B,hB,hh⟩
        · exact (mem_erase.mp hi).1 (hAi (mem_of_mem_erase hi) hj (heq.symm.trans hh))
        · exact howner i (mem_of_mem_erase hi) B hB (hh.symm.trans heq)
      obtain ⟨Z₂,K₂,hZ₂,hKF₂,hKown₂,hKZ₂,hbor₂,hcredit₂,hint₂,hown₂,hfresh₂⟩ :=
        ih (J.erase j) (erase_ssubset hj) hInj
          (fun i hi => hAF i (mem_of_mem_erase hi))
          (fun i hi => hvalid i (mem_of_mem_erase hi)) Z₁ hZ₁ horder₁ howner₁
      have hdis : Disjoint K₁ K₂ := by
        rw [Finset.disjoint_left]
        intro D hD hD₂
        obtain ⟨i,hi,heq⟩ := hKown₂ D hD₂
        exact (mem_erase.mp hi).1 (hAi (mem_of_mem_erase hi) hj (heq.symm.trans (hKown D hD)))
      have hKZ : Disjoint K₁ Z₂ := by
        rw [Finset.disjoint_left]
        intro D hD hDZ
        rcases hfresh₂ D hDZ (hKAf hD) with hD₁ | ⟨i,hi,u,hu,heq⟩
        · exact Finset.disjoint_left.mp hKZ₁ hD hD₁
        · have hoi : D.owner = (A i).owner := congrArg Record.owner heq
          exact (mem_erase.mp hi).1 (hAi (mem_of_mem_erase hi) hj (hoi.symm.trans (hKown D hD)))
      refine ⟨Z₂,K₁∪K₂,hZ₂,union_subset hKAf hKF₂,?_,disjoint_union_left.mpr ⟨hKZ,hKZ₂⟩,
        ?_,?_,fun B hh => hint₁ B (hint₂ B hh),?_,?_⟩
      · intro D hD
        rcases mem_union.mp hD with hD | hD
        · exact ⟨j,hj,hKown D hD⟩
        · obtain ⟨i,hi,hh⟩ := hKown₂ D hD
          exact ⟨i,mem_of_mem_erase hi,hh⟩
      · intro D hD hint
        rcases mem_union.mp hD with hD | hD
        · exact hbor₁ D hD (hint₂ D hint)
        · exact hbor₂ D hD hint
      · have hsum := sum_erase_add J (fun i => ((A i).centers.card : ℝ)) hj
        have hcard : ((K₁∪K₂).card : ℝ) = (K₁.card : ℝ)+(K₂.card : ℝ) := by
          exact_mod_cast card_union_of_disjoint hdis
        rw [hcard,←hsum]
        dsimp [AssignedAccounting.theta] at hcredit₁ hcredit₂ ⊢
        linarith
      · intro D hD
        rcases hown₂ D hD with ⟨i,hi,hh⟩ | ⟨B,hB,hh⟩
        · exact Or.inl ⟨i,mem_of_mem_erase hi,hh⟩
        · rcases hown₁ B hB with heq | ⟨C,hC,heq⟩
          · exact Or.inl ⟨j,hj,hh.trans heq⟩
          · exact Or.inr ⟨C,hC,hh.trans heq⟩
      · intro D hD hDF
        rcases hfresh₂ D hD hDF with hD | ⟨i,hi,u,hu,heq⟩
        · rcases hfresh₁ D hD hDF with hD | ⟨u,hu,heq⟩
          · exact Or.inl hD
          · exact Or.inr ⟨j,hj,u,hu,heq⟩
        · exact Or.inr ⟨i,mem_of_mem_erase hi,u,hu,heq⟩
    · have he : J = ∅ := not_nonempty_iff_eq_empty.mp hn
      subst J
      refine ⟨Z,∅,hZ,empty_subset _,?_,disjoint_empty_left _,?_,?_,fun _ hh => hh,?_,?_⟩
      · simp
      · simp
      · simp
      · intro D hD
        exact Or.inr ⟨D,hD,rfl⟩
      · intro D hD _
        exact Or.inl hD

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {δ η : ℝ}

lemma assigned_phase {ι : Type uι2} [DecidableEq ι]
    (A : ι → H.AssignedBag G X δ η) (P : ι → Finset (Finset (Fin n)))
    (hX : ∀v, binary (X v)) {q ε : ℝ} (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536)
    (J : Finset ι) (hAi : Set.InjOn (fun i => (A i).owner) J)
    (hvalid : ∀i ∈ J, ∀u ∈ (A i).centers, ((A i).input (P i) u).Valid H G X (q/4))
    (hgeo : ∀i ∈ J, ∀u ∈ (A i).centers, ∀j ∈ J, ∀v ∈ (A j).centers,
      ((A i).input (P i) u) ≠ ((A j).input (P j) v) →
      Disjoint ((RadialShell.ball u δ).support X) ((RadialShell.ball v δ).support X))
    (Z : Finset (Record n)) (hZ : H.LabeledArrangement G X (q/4) Z)
    (horder : ∀i ∈ J, ∀D ∈ Z, D.owner ⊂ (A i).owner → D.owner ∈ P i)
    (howner : ∀i ∈ J, ∀D ∈ Z, D.owner ≠ (A i).owner) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X (q/4) Z' ∧
      (∑D ∈ Z, D.baseToken δ)+(AssignedAccounting.theta/2)*
        (∑i ∈ J, ((A i).centers.card : ℝ))*δ ≤ ∑D ∈ Z', D.baseToken ε ∧
      (∀D ∈ Z', (∃i ∈ J, D.owner = (A i).owner) ∨ ∃B ∈ Z, D.owner = B.owner) := by
  let F := J.biUnion (fun i => ((A i).centers.image ((A i).input (P i))))
  have hFmem : ∀D : Record n, D ∈ F ↔ ∃i ∈ J, ∃u ∈ (A i).centers, D = (A i).input (P i) u := by
    intro D
    simp only [F,mem_biUnion,mem_image]
    constructor
    · rintro ⟨i,hi,u,hu,heq⟩
      exact ⟨i,hi,u,hu,heq.symm⟩
    · rintro ⟨i,hi,u,hu,heq⟩
      exact ⟨i,hi,u,hu,heq.symm⟩
  have hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none := by
    intro D hD
    obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem D).mp hD
    simp [AssignedBag.input,RadialShell.ball,RadialShell.width]
  have hFball : ∀B ∈ F, B.shell = RadialShell.ball B.shell.center δ := by
    intro D hD
    obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem D).mp hD
    rfl
  have hFg : ∀B ∈ F, ∀D ∈ F, B ≠ D → Disjoint (B.shell.support X) (D.shell.support X) := by
    intro B hB D hD hne
    obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem B).mp hB
    obtain ⟨j,hj,v,hv,rfl⟩ := (hFmem D).mp hD
    exact hgeo i hi u hu j hj v hv hne
  have hFv : H.LabeledArrangement G X (q/4) F := by
    refine ⟨?_,?_⟩
    · intro D hD
      obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem D).mp hD
      exact hvalid i hi u hu
    · intro B hB D hD hne hh
      exact (hh (hFg B hB D hD hne)).elim
  have hAF : ∀i ∈ J, ∀u ∈ (A i).centers, (A i).input (P i) u ∈ F :=
    fun i hi u hu => (hFmem _).mpr ⟨i,hi,u,hu,rfl⟩
  obtain ⟨Z₁,K,hZ₁,hKF,hKo,hKZ,hbor,hcredit,hint,hown,hfresh⟩ :=
    phase_loops A P hX hq hconn hη hscale hF J hAi hAF hvalid Z hZ horder howner
  obtain ⟨Z₂,hZ₂,hcredit₂,hown₂⟩ :=
    border_transition hX hδ hε hscale hF hFball hFg hFv hZ₁ hKF hKZ hbor
  have hsum : ∑D ∈ Z, D.phaseToken F δ ε = ∑D ∈ Z, D.baseToken δ := by
    apply sum_congr rfl
    intro D hD
    have hn : D ∉ F := by
      intro hf
      obtain ⟨i,hi,u,hu,heq⟩ := (hFmem D).mp hf
      exact howner i hi D hD (congrArg Record.owner heq)
    simp only [Record.phaseToken,ite_eq_right hn,Record.baseToken]
  refine ⟨Z₂,hZ₂,?_,?_⟩
  · rw [hsum] at hcredit
    linarith
  · intro D hD
    rcases hown₂ D hD with hDK | ⟨B,hB,heq⟩
    · exact Or.inl (hKo D hDK)
    · rcases hown B hB with ⟨i,hi,hoi⟩ | ⟨C,hC,hoi⟩
      · exact Or.inl ⟨i,hi,heq.trans hoi⟩
      · exact Or.inr ⟨C,hC,heq.trans hoi⟩

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.AssignedFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {η : ℝ}

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

lemma owner_mem (i : Fin F.count) : (F.bag i).owner ∈ F.owners := mem_image.mpr ⟨i,mem_univ _,rfl⟩
lemma owners_nodes : F.owners ⊆ H.nodes := by
  intro S hS
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
  exact (F.bag i).owner_mem

lemma input_valid {q : ℝ} (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    {E : Finset (Finset (Fin n))} (hE : E ⊆ H.nodes) (hprot : F.ProtectedFrom E)
    (i : Fin F.count) {u : Fin n} (hu : u ∈ (F.bag i).centers) :
    ((F.bag i).input (F.predecessors E i) u).Valid H G X (q/4) := by
  have hbound := H.parent_boundary_lower G hconn (F.bag i).owner_mem (F.bag i).nonroot
  have hassign := (F.bag i).assignment
  have hc : (3072:ℝ) ≤ ((F.bag i).centers.card : ℝ) := by
    have ha := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg (H.parentBoundary G (F.bag i).owner).card)
    have hb := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (3072:ℝ)/q by positivity)
    have heq : (3072:ℝ)/q*q = 3072 := by field_simp
    rw [heq] at hb
    linarith
  apply (F.bag i).input_valid hX hq.le hconn
    (by exact_mod_cast (show (1:ℝ) < ((F.bag i).centers.card : ℝ) by linarith))
    (fun S hS => ⟨hE (mem_filter.mp hS).1,(mem_filter.mp hS).2⟩) hu (hprot i u hu)

lemma phase {q ε : ℝ} (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    (hε : 0 ≤ ε) (hscale : ε ≤ F.radius/1536)
    {E : Finset (Finset (Fin n))} (hE : E ⊆ H.nodes) (hprot : F.ProtectedFrom E)
    (hdis : Disjoint E F.owners)
    (Z : Finset (Record n)) (hZ : H.LabeledArrangement G X (q/4) Z)
    (hown : ∀D ∈ Z, D.owner ∈ E) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X (q/4) Z' ∧
      (∑D ∈ Z, D.baseToken F.radius)+(AssignedAccounting.theta/2)*F.mass ≤
        ∑D ∈ Z', D.baseToken ε ∧ (∀D ∈ Z', D.owner ∈ E∪F.owners) := by
  obtain ⟨Z',hZ',hc,ho⟩ := assigned_phase F.bag (F.predecessors E) hX hq hconn hη
    F.positive hε hscale univ F.owner_injective.injOn
    (fun i _ u hu => F.input_valid hX hq hconn hη hE hprot i hu)
    (by
      intro i hi u hu j hj v hv hne
      apply F.separated i u hu j v hv
      by_cases hh : i = j
      · right
        intro he
        subst j; subst v
        exact hne rfl
      · exact Or.inl hh)
    Z hZ
    (fun i _ D hD hs => mem_filter.mpr ⟨hown D hD,hs⟩)
    (fun i _ D hD heq => Finset.disjoint_left.mp hdis (hown D hD) (heq ▸ F.owner_mem i))
  refine ⟨Z',hZ',?_,?_⟩
  · simpa only [mass,mul_assoc] using hc
  · intro D hD
    rcases ho D hD with ⟨i,hi,heq⟩ | ⟨B,hB,heq⟩
    · exact mem_union_right _ (heq ▸ F.owner_mem i)
    · exact mem_union_left _ (heq ▸ hown B hB)

end AssignedFamily

namespace AssignedSequence

lemma radius_nonneg (L : List (Family (H := H) (G := G) (X := X) (η := η))) :
    0 ≤ initialRadius L := by
  cases L with
  | nil => exact le_refl _
  | cons F L => exact F.positive.le

lemma construct {q : ℝ} (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    (L : List (Family (H := H) (G := G) (X := X) (η := η)))
    (hgeo : Geometric L) (E : Finset (Finset (Fin n))) (hE : E ⊆ H.nodes)
    (hready : Ready E L) (Z : Finset (Record n)) (hZ : H.LabeledArrangement G X (q/4) Z)
    (hown : ∀D ∈ Z, D.owner ∈ E) {credit : ℝ}
    (hcredit : credit ≤ ∑D ∈ Z, D.baseToken (initialRadius L)) :
    ∃Z' : Finset (Record n), H.LabeledArrangement G X (q/4) Z' ∧
      credit+(AssignedAccounting.theta/2)*mass L ≤ ∑D ∈ Z', D.shell.width := by
  induction L generalizing E Z credit with
  | nil =>
    refine ⟨Z,hZ,?_⟩
    simp only [mass,mul_zero,add_zero] at *
    apply hcredit.trans
    exact sum_le_sum (fun D hD => AssignedAccounting.base_le_width D.avoided.isSome
      (by have hh := (hZ.1 D hD).2.2.1.2.1; dsimp [RadialShell.width]; linarith) (le_refl _))
  | cons F L ih =>
    obtain ⟨Z₁,hZ₁,hstep,hown₁⟩ := F.phase hX hq hconn hη (radius_nonneg L)
      hgeo.1 hE hready.2.1 hready.1 Z hZ hown
    have hc : credit+(AssignedAccounting.theta/2)*F.mass ≤
        ∑D ∈ Z₁, D.baseToken (initialRadius L) := by
      change credit ≤ ∑D ∈ Z, D.baseToken F.radius at hcredit
      linarith
    obtain ⟨Z₂,hZ₂,hc₂⟩ := ih hgeo.2 (E∪F.owners) (union_subset hE F.owners_nodes)
      hready.2.2 Z₁ hZ₁ hown₁ hc
    refine ⟨Z₂,hZ₂,?_⟩
    dsimp [mass]
    linarith

lemma insertable_bound {q : ℝ} (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hη : 3072/q ≤ η)
    (L : List (Family (H := H) (G := G) (X := X) (η := η)))
    (hgeo : Geometric L) (hready : Ready ∅ L) :
    (q/4096)*mass L ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  have hempty : H.LabeledArrangement G X (q/4) ∅ := by constructor <;> simp
  obtain ⟨Z,hZ,hwidth⟩ := construct hX hq hconn hη L hgeo ∅ (empty_subset _) hready
    ∅ hempty (by simp) (credit := 0) (by simp)
  have he := H.labeled_energy G X hX hZ
  have hh := mul_le_mul_of_nonneg_left hwidth (show 0 ≤ q/4 by positivity)
  dsimp [AssignedAccounting.theta] at hh
  linarith

end AssignedSequence
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ} {η : ℝ}

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

lemma bad_witness {E : Finset (Finset (Fin n))} (i : Fin F.count) {u : Fin n}
    (hu : u ∈ F.badCenters E i) :
    ∃S ∈ E, ∃e ∈ G.cut univ S, ∃v : Fin n,
      (v = G.left e ∨ v = G.right e) ∧ l1dist (X v) (X u) < F.radius := by
  have hn : ¬((F.bag i).input (F.predecessors E i) u).Protected G X := by
    intro hh
    exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,hh⟩)
  simp only [Record.Protected,not_forall] at hn
  obtain ⟨S,hS,e,he,hn⟩ := hn
  have hSE : S ∈ E := (mem_filter.mp hS).1
  change ¬(F.radius ≤ l1dist (X (G.left e)) (X u) ∧
    F.radius ≤ l1dist (X (G.right e)) (X u)) at hn
  by_cases hl : l1dist (X (G.left e)) (X u) < F.radius
  · exact ⟨S,hSE,e,he,G.left e,Or.inl rfl,hl⟩
  · exact ⟨S,hSE,e,he,G.right e,Or.inr rfl,lt_of_not_ge (fun hr => hn ⟨le_of_not_gt hl,hr⟩)⟩

lemma badCount_le (hX : ∀v, binary (X v)) (E : Finset (Finset (Fin n))) :
    F.badCount E ≤ 2*boundaryCount G E := by
  let B := univ.sigma (F.badCenters E)
  let W := E.biUnion (fun S => (G.cut univ S).biUnion (fun e => {G.left e,G.right e}))
  have hBW : ∀p ∈ B, ∃v ∈ W, l1dist (X v) (X p.2) < F.radius := by
    intro p hp
    obtain ⟨S,hS,e,he,v,hv,hd⟩ := F.bad_witness p.1 (mem_sigma.mp hp).2
    refine ⟨v,mem_biUnion.mpr ⟨S,hS,mem_biUnion.mpr ⟨e,he,?_⟩⟩,hd⟩
    simp only [mem_insert,mem_singleton]
    exact hv
  choose f hfW hfd using hBW
  have hinj : ∀p hp q hq, f p hp = f q hq → p = q := by
    intro p hp r hr heq
    by_contra hh
    have hne : p.1 ≠ r.1 ∨ p.2 ≠ r.2 := by
      by_contra hn
      push Not at hn
      exact hh (Sigma.ext hn.1 (heq_of_eq hn.2))
    have hd := F.separated p.1 p.2 (mem_sdiff.mp (mem_sigma.mp hp).2).1
      r.1 r.2 (mem_sdiff.mp (mem_sigma.mp hr).2).1 hne
    have ha : X (f p hp) ∈ (RadialShell.ball p.2 F.radius).support X := by
      rw [RadialShell.support_ball]
      exact ⟨binary_cube (hX _),hfd p hp⟩
    have hb : X (f p hp) ∈ (RadialShell.ball r.2 F.radius).support X := by
      rw [RadialShell.support_ball,heq]
      exact ⟨binary_cube (hX _),hfd r hr⟩
    exact Set.disjoint_left.mp hd ha hb
  have hcard : B.card ≤ W.card := by
    apply Finset.card_le_card_of_injective (f := fun p : B => (⟨f p.val p.property,hfW p.val p.property⟩ : W))
    intro p r heq
    exact Subtype.ext (hinj p.val p.property r.val r.property (congrArg Subtype.val heq))
  have hW : W.card ≤ 2*boundaryCount G E := by
    calc
      W.card ≤ ∑S ∈ E, ((G.cut univ S).biUnion (fun e => {G.left e,G.right e})).card := card_biUnion_le
      _ ≤ ∑S ∈ E, ∑e ∈ G.cut univ S, ({G.left e,G.right e} : Finset (Fin n)).card :=
        sum_le_sum (fun S hS => card_biUnion_le)
      _ ≤ ∑S ∈ E, ∑_e ∈ G.cut univ S, 2 :=
        sum_le_sum (fun S hS => sum_le_sum (fun e he => card_le_two))
      _ = _ := by simp [boundaryCount,mul_sum,Nat.mul_comm]
  have heq : B.card = F.badCount E := by simp [B,badCount,Finset.card_sigma]
  rw [heq] at hcard
  exact hcard.trans hW

lemma prune (E : Finset (Finset (Fin n))) {η' : ℝ} (hη : 2*η' ≤ η) :
    ∃F' : AssignedFamily H G X η', F'.radius = F.radius ∧ F'.owners ⊆ F.owners ∧
      (∀E' ⊆ E, F'.ProtectedFrom E') ∧
      F.mass-2*(F.badCount E : ℝ)*F.radius ≤ F'.mass := by
  let J := univ.filter (fun i : Fin F.count => (F.bag i).centers.card ≤ 2*(F.goodCenters E i).card)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hnon : ∀i ∈ J, (F.goodCenters E i).Nonempty := by
    intro i hi
    apply card_pos.mp
    have hn := card_pos.mpr (F.bag i).nonempty
    have hc := (mem_filter.mp hi).2
    omega
  let a (i : J) : H.AssignedBag G X F.radius η' := {
    owner := (F.bag i.val).owner
    owner_mem := (F.bag i.val).owner_mem
    nonroot := (F.bag i.val).nonroot
    centers := F.goodCenters E i.val
    nonempty := hnon i.val i.property
    radius_pos := F.positive
    disjoint := (F.bag i.val).disjoint.mono (filter_subset _ _)
    assignment := by
      have hc : ((F.bag i.val).centers.card : ℝ) ≤ 2*((F.goodCenters E i.val).card : ℝ) := by
        exact_mod_cast (mem_filter.mp i.property).2
      have hh := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg (H.parentBoundary G (F.bag i.val).owner).card)
      have ha := (F.bag i.val).assignment
      linarith
    endpoint := fun u hu => (F.bag i.val).endpoint u (mem_filter.mp hu).1 }
  let F' : AssignedFamily H G X η' := {
    radius := F.radius
    positive := F.positive
    count := Fintype.card J
    bag := fun i => a (e i)
    owner_injective := by
      intro i j hij
      apply e.injective
      apply Subtype.ext
      exact F.owner_injective hij
    separated := by
      intro i u hu j v hv hne
      apply F.separated (e i).val u (mem_filter.mp hu).1 (e j).val v (mem_filter.mp hv).1
      rcases hne with hne | hne
      · left
        intro hh
        exact hne (e.injective (Subtype.ext hh))
      · exact Or.inr hne }
  have hsum : ∑i : Fin F'.count, ((F'.bag i).centers.card : ℝ) =
      ∑i ∈ J, ((F.goodCenters E i).card : ℝ) := by
    change (∑i : Fin (Fintype.card J), ((F.goodCenters E (e i).val).card : ℝ)) = _
    rw [e.sum_comp (fun i : J => ((F.goodCenters E i.val).card : ℝ))]
    exact Finset.sum_coe_sort J (fun i : Fin F.count => ((F.goodCenters E i).card : ℝ))
  have hgood : ∀i, ((F.bag i).centers.card : ℝ) ≤
      (if i ∈ J then ((F.goodCenters E i).card : ℝ) else 0)+2*((F.badCenters E i).card : ℝ) := by
    intro i
    have hc : ((F.badCenters E i).card : ℝ)+((F.goodCenters E i).card : ℝ) =
        ((F.bag i).centers.card : ℝ) := by
      exact_mod_cast card_sdiff_add_card_eq_card (filter_subset (fun u =>
        ((F.bag i).input (F.predecessors E i) u).Protected G X) (F.bag i).centers)
    by_cases hi : i ∈ J
    · rw [ite_eq_left hi]
      linarith [show (0:ℝ) ≤ (F.badCenters E i).card from Nat.cast_nonneg _]
    · rw [ite_eq_right hi]
      have hh : 2*(F.goodCenters E i).card < (F.bag i).centers.card := by
        simpa only [J,mem_filter,mem_univ,true_and,not_le] using hi
      have hh' : 2*((F.goodCenters E i).card : ℝ) < ((F.bag i).centers.card : ℝ) := by exact_mod_cast hh
      linarith
  have hcount := Finset.sum_le_sum (s := univ) (fun i _ => hgood i)
  have hcounts : (∑i, ((F.bag i).centers.card : ℝ))-2*(F.badCount E : ℝ) ≤
      ∑i ∈ J, ((F.goodCenters E i).card : ℝ) := by
    rw [sum_add_distrib,←mul_sum] at hcount
    have heq : (∑i, if i ∈ J then ((F.goodCenters E i).card : ℝ) else 0) =
        ∑i ∈ J, ((F.goodCenters E i).card : ℝ) := by simp
    rw [heq] at hcount
    apply sub_le_iff_le_add.mpr
    simpa only [badCount,Nat.cast_sum] using hcount
  refine ⟨F',rfl,?_,?_,?_⟩
  · intro S hS
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
    exact F.owner_mem (e i).val
  · intro E' hE' i u hu S hS edge hedge
    have hp := (mem_filter.mp hu).2
    exact hp S (mem_filter.mpr ⟨hE' (mem_filter.mp hS).1,(mem_filter.mp hS).2⟩) edge hedge
  · dsimp [mass]
    rw [hsum]
    linarith [mul_le_mul_of_nonneg_right hcounts F.positive.le]

end AssignedFamily
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Capture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

namespace AssignedFamily
variable {q : ℝ} (F : AssignedFamily H G X (6144/q))

lemma boundary_mass {ρ : ℝ} (hq : 0 < q) (hR : F.BoundaryRatio ρ) :
    6144*ρ*(boundaryCount G F.owners : ℝ)*F.radius ≤ F.mass := by
  have he : (boundaryCount G F.owners : ℝ) =
      ∑i, ((G.cut univ (F.bag i).owner).card : ℝ) := by
    simp only [boundaryCount,owners,Nat.cast_sum]
    exact sum_image F.owner_injective.injOn
  have hi : ∀i, (6144*ρ)*((G.cut univ (F.bag i).owner).card : ℝ) ≤ ((F.bag i).centers.card : ℝ) := by
    intro i
    have hh := mul_le_mul_of_nonneg_left (hR i) (show 0 ≤ (6144:ℝ)/q by positivity)
    have hx : (6144:ℝ)/q*((q*ρ)*((G.cut univ (F.bag i).owner).card : ℝ)) =
        (6144*ρ)*((G.cut univ (F.bag i).owner).card : ℝ)  := by field_simp
    rw [hx] at hh
    exact hh.trans (F.bag i).assignment
  rw [he]
  dsimp [mass]
  apply mul_le_mul_of_nonneg_right _ F.positive.le
  rw [mul_sum]
  exact sum_le_sum (fun i _ => hi i)
end AssignedFamily

namespace AssignedSequence
open AssignedFamily
variable {q : ℝ}

lemma geometric_of {η ρ : ℝ} (hρ : ρ ≤ 1/1536)
    (L : List (AssignedFamily H G X η)) (hL : GeometricAt ρ L) : Geometric L := by
  induction L with
  | nil => trivial
  | cons F L ih =>
    refine ⟨?_,ih hL.2⟩
    have hh := mul_le_mul_of_nonneg_right hρ F.positive.le
    linarith [hL.1]

lemma prune_sequence (hX : ∀v, binary (X v)) (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (L : List (AssignedFamily H G X (6144/q)))
    (hgeo : GeometricAt ρ L) (hR : Ratios ρ L)
    (E E' : Finset (Finset (Fin n))) (hE : E ⊆ H.nodes) (hE' : E' ⊆ E)
    (hfresh : Fresh E L) :
    ∃L' : List (AssignedFamily H G X (3072/q)), initialRadius L' = initialRadius L ∧
      GeometricAt ρ L' ∧ Ready E' L' ∧
      mass L/2-8*(initialRadius L)*(boundaryCount G E : ℝ) ≤ mass L' := by
  induction L generalizing E E' with
  | nil => exact ⟨[],rfl,True.intro,True.intro,by simp [mass,initialRadius]⟩
  | cons F L ih =>
    obtain ⟨F',hrad,howners,hprot,hgain⟩ := F.prune E (η' := 3072/q) (by field_simp; ring_nf; rfl)
    have hE₁ : E∪F.owners ⊆ H.nodes := union_subset hE F.owners_nodes
    obtain ⟨L',headEq,hgeo',hready',hgain'⟩ := ih hgeo.2 hR.2
      (E∪F.owners) (E'∪F'.owners) hE₁ (union_subset_union hE' howners) hfresh.2
    have hdis : Disjoint E' F'.owners := hfresh.1.mono hE' howners
    have hBC : (boundaryCount G (E∪F.owners) : ℝ) =
        (boundaryCount G E : ℝ)+(boundaryCount G F.owners : ℝ) := by
      simp only [boundaryCount,sum_union hfresh.1,Nat.cast_add]
    have hb := F.badCount_le hX E
    have hb' : (F.badCount E : ℝ) ≤ 2*(boundaryCount G E : ℝ) := by exact_mod_cast hb
    have hpf : F.mass-4*F.radius*(boundaryCount G E : ℝ) ≤ F'.mass := by
      have hh := mul_le_mul_of_nonneg_right hb' F.positive.le
      linarith
    have hr := F.boundary_mass hq hR.1
    have heps := radius_nonneg L
    have hsc := hgeo.1
    have hsmall := mul_le_mul_of_nonneg_right hρsmall F.positive.le
    have hcoal : 4*F.radius+8*initialRadius L ≤ 8*F.radius := by linarith
    have hB0 : (0:ℝ) ≤ boundaryCount G E := Nat.cast_nonneg _
    have hBF0 : (0:ℝ) ≤ boundaryCount G F.owners := Nat.cast_nonneg _
    have hc := mul_le_mul_of_nonneg_right hsc hBF0
    have hcost : 8*initialRadius L*(boundaryCount G F.owners : ℝ) ≤ F.mass/2 := by
      have hpos : 0 ≤ ρ*F.radius*(boundaryCount G F.owners : ℝ) :=
        mul_nonneg (mul_nonneg hρ.le F.positive.le) hBF0
      linarith
    have hprev := mul_le_mul_of_nonneg_right hcoal hB0
    refine ⟨F'::L',hrad,⟨?_,hgeo'⟩,⟨hdis,hprot E' hE',hready'⟩,?_⟩
    · simpa only [headEq,hrad] using hsc
    · rw [hBC] at hgain'
      dsimp [mass,initialRadius]
      linarith

lemma assigned_bound (hX : ∀v, binary (X v)) {q : ℝ} (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q)
    {ρ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (L : List (AssignedFamily H G X (6144/q)))
    (hgeo : GeometricAt ρ L) (hR : Ratios ρ L) (hfresh : Fresh ∅ L) :
    (q/8192)*mass L ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  obtain ⟨L',hrad,hgeo',hready',hmass⟩ := prune_sequence hX hq hρ hρsmall L hgeo hR ∅ ∅
    (empty_subset _) (Subset.refl _) hfresh
  have hcharge := insertable_bound hX hq hconn (le_refl (3072/q)) L' (geometric_of hρsmall L' hgeo') hready'
  have hmass' : mass L/2 ≤ mass L' := by simpa [boundaryCount] using hmass
  have hh := mul_le_mul_of_nonneg_left hmass' (show 0 ≤ q/4096 by positivity)
  linarith

end AssignedSequence
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma assigned_from_net (T : Finset (Finset (Fin n))) (W : Finset (Fin n))
    (hW : W.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hboundary : ∀t ∈ T, 0 < (H.parentBoundary G t).card)
    {D η : ℝ} (hD : 0 < D)
    (hsep : (W : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u D).support X) ((ball v D).support X)))
    (hcenter : ∀u ∈ W, ∃t ∈ T, u ∈ t ∧ ∃e ∈ H.parentBoundary G t,
      (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) < D)
    (hη : η ≤ (W.card : ℝ)/(2*(∑t ∈ T, ((H.parentBoundary G t).card : ℝ)))) :
    ∃F : AssignedFamily H G X η, F.radius = D ∧ F.owners ⊆ T ∧
      D*(W.card : ℝ)/2 ≤ F.mass := by
  obtain ⟨u0,hu0⟩ := hW
  obtain ⟨t0,ht0,ht0c⟩ := hcenter u0 hu0
  have hex : ∀u : Fin n, ∃t ∈ T, u ∈ W → u ∈ t ∧ ∃e ∈ H.parentBoundary G t,
      (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) < D := by
    intro u
    by_cases hu : u ∈ W
    · obtain ⟨t,ht,hc⟩ := hcenter u hu
      exact ⟨t,ht,fun _ => hc⟩
    · exact ⟨t0,ht0,fun hh => (hu hh).elim⟩
  choose f hfT hf using hex
  let N : ℝ := ∑t ∈ T, ((H.parentBoundary G t).card : ℝ)
  have hN : 0 < N := sum_pos (fun t ht => by exact_mod_cast hboundary t ht) ⟨t0,ht0⟩
  have hW0 : (0:ℝ) < W.card := by exact_mod_cast card_pos.mpr ⟨u0,hu0⟩
  let c : ℝ := W.card/(2*N)
  have hc : 0 < c := div_pos hW0 (mul_pos (by norm_num) hN)
  obtain ⟨J,hJT,hJ,hgain⟩ := retain_fibers W T f (fun u _ => hfT u)
    (fun t => ((H.parentBoundary G t).card : ℝ))
    (fun t ht => by exact_mod_cast hboundary t ht) hc
  let fiber := fun t => W.filter (fun u => f u=t)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a (t : J) : H.AssignedBag G X D η := {
    owner := t.val
    owner_mem := hT (hJT t.property)
    nonroot := hroot t.val (hJT t.property)
    centers := fiber t.val
    nonempty := (hJ t.val t.property).1
    radius_pos := hD
    disjoint := hsep.mono (filter_subset _ _)
    assignment := (mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg _)).trans (hJ t.val t.property).2
    endpoint := by
      intro u hu
      obtain ⟨hu,hfu⟩ := mem_filter.mp hu
      simpa only [hfu] using hf u hu }
  let F : AssignedFamily H G X η := {
    radius := D
    positive := hD
    count := Fintype.card J
    bag := fun i => a (e i)
    owner_injective := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    separated := by
      intro i u hu j v hv hne
      apply hsep (mem_filter.mp hu).1 (mem_filter.mp hv).1
      intro huv
      subst v
      have hh : (e i).val = (e j).val :=
        (mem_filter.mp hu).2.symm.trans (mem_filter.mp hv).2
      rcases hne with hne | hne
      · exact hne (e.injective (Subtype.ext hh))
      · exact hne rfl }
  have hsum : (∑i : Fin F.count, ((F.bag i).centers.card : ℝ)) =
      ∑t ∈ J, ((fiber t).card : ℝ) := by
    change (∑i : Fin (Fintype.card J), ((fiber (e i).val).card : ℝ)) = _
    rw [e.sum_comp (fun t : J => ((fiber t.val).card : ℝ))]
    exact sum_coe_sort J (fun t => ((fiber t).card : ℝ))
  refine ⟨F,rfl,?_,?_⟩
  · intro t ht
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ht
    exact hJT (e i).property
  · have heq : c*N = (W.card : ℝ)/2 := by dsimp [c]; field_simp
    change (W.card : ℝ)-c*N ≤ _ at hgain
    rw [heq] at hgain
    change D*(W.card : ℝ)/2 ≤ (∑i : Fin F.count, ((F.bag i).centers.card : ℝ))*D
    rw [hsum]
    have hh := mul_le_mul_of_nonneg_left hgain hD.le
    linarith

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
open scoped Classical
variable {n m : ℕ} (H : Hierarchy n) (G : MultiGraph n m)

lemma boundary_owner_unique {A B : Finset (Fin n)} {u v : Fin n}
    (hA : A ∈ H.nodes) (hB : B ∈ H.nodes) (hAr : A ≠ univ) (hBr : B ≠ univ)
    (huA : u ∈ A) (huB : u ∈ B) (hvA : v ∉ A) (hvB : v ∉ B)
    (hvPA : v ∈ H.parent A) (hvPB : v ∈ H.parent B) : A = B := by
  rcases H.laminar A hA B hB with hAB | hBA | hdis
  · by_contra hne
    have hp := H.parent_minimal A hA hAr B hB (Finset.ssubset_iff_subset_ne.mpr ⟨hAB,hne⟩)
    exact hvB (hp hvPA)
  · by_contra hne
    have hp := H.parent_minimal B hB hBr A hA (Finset.ssubset_iff_subset_ne.mpr ⟨hBA,Ne.symm hne⟩)
    exact hvA (hp hvPB)
  · exact (Finset.disjoint_left.mp hdis huA huB).elim

lemma parentBoundary_multiplicity (T : Finset (Finset (Fin n)))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ) (e : Fin m) :
    (T.filter (fun t => e ∈ H.parentBoundary G t)).card ≤ 2 := by
  let S := T.filter (fun t => e ∈ H.parentBoundary G t)
  let L := S.filter (fun t => G.left e ∈ t)
  let R := S.filter (fun t => G.right e ∈ t)
  have hL : L.card ≤ 1 := by
    apply card_le_one.mpr
    intro A hA B hB
    obtain ⟨hA,hlA⟩ := mem_filter.mp hA
    obtain ⟨hB,hlB⟩ := mem_filter.mp hB
    obtain ⟨hAT,heA⟩ := mem_filter.mp hA
    obtain ⟨hBT,heB⟩ := mem_filter.mp hB
    obtain ⟨hePA,hcutA⟩ := mem_filter.mp heA
    obtain ⟨hePB,hcutB⟩ := mem_filter.mp heB
    have hrA : G.right e ∉ A := by rcases hcutA with hh | hh; exact hh.2; exact (hh.2 hlA).elim
    have hrB : G.right e ∉ B := by rcases hcutB with hh | hh; exact hh.2; exact (hh.2 hlB).elim
    exact H.boundary_owner_unique (hT hAT) (hT hBT) (hroot A hAT) (hroot B hBT)
      hlA hlB hrA hrB ((G.mem_inducedEdges _ _).mp hePA).2 ((G.mem_inducedEdges _ _).mp hePB).2
  have hR : R.card ≤ 1 := by
    apply card_le_one.mpr
    intro A hA B hB
    obtain ⟨hA,hrA⟩ := mem_filter.mp hA
    obtain ⟨hB,hrB⟩ := mem_filter.mp hB
    obtain ⟨hAT,heA⟩ := mem_filter.mp hA
    obtain ⟨hBT,heB⟩ := mem_filter.mp hB
    obtain ⟨hePA,hcutA⟩ := mem_filter.mp heA
    obtain ⟨hePB,hcutB⟩ := mem_filter.mp heB
    have hlA : G.left e ∉ A := by rcases hcutA with hh | hh; exact (hh.2 hrA).elim; exact hh.2
    have hlB : G.left e ∉ B := by rcases hcutB with hh | hh; exact (hh.2 hrB).elim; exact hh.2
    exact H.boundary_owner_unique (hT hAT) (hT hBT) (hroot A hAT) (hroot B hBT)
      hrA hrB hlA hlB ((G.mem_inducedEdges _ _).mp hePA).1 ((G.mem_inducedEdges _ _).mp hePB).1
  have hsub : S ⊆ L∪R := by
    intro A hA
    have hc := (mem_filter.mp (mem_filter.mp hA).2).2
    rcases hc with hh | hh
    · exact mem_union_left _ (mem_filter.mpr ⟨hA,hh.1⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hA,hh.1⟩)
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))

lemma subset_boundary_multiplicity (T : Finset (Finset (Fin n)))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (F : Finset (Fin n) → Finset (Fin m)) (hF : ∀t ∈ T, F t ⊆ H.parentBoundary G t) :
    (∑t ∈ T, (F t).card) ≤ 2*(T.biUnion F).card := by
  have hdouble : (∑t ∈ T, (F t).card) =
      ∑e ∈ T.biUnion F, (T.filter (fun t => e ∈ F t)).card := by
    simp only [card_eq_sum_ones,sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro t ht
    simp only [←sum_filter]
    congr 1
    ext e
    simp only [mem_filter,mem_biUnion]
    exact ⟨fun hh => ⟨⟨t,ht,hh⟩,hh⟩,fun hh => hh.2⟩
  rw [hdouble]
  have heq : 2*(T.biUnion F).card = ∑_e ∈ T.biUnion F, 2 := by simp [mul_comm]
  rw [heq]
  apply sum_le_sum
  intro e he
  apply le_trans (card_le_card (show T.filter (fun t => e ∈ F t) ⊆
      T.filter (fun t => e ∈ H.parentBoundary G t) from by
    intro t ht
    obtain ⟨ht,he⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨ht,hF t ht he⟩))
  exact H.parentBoundary_multiplicity G T hT hroot e

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma capture_small_balls (T : Finset (Finset (Fin n))) (S P : Finset (Fin n))
    (hS : S.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hboundary : ∀t ∈ T, 0 < (H.parentBoundary G t).card)
    {δ c₂ η : ℝ} (hδ : 0 < δ) (hc : 0 < c₂) (_hη : 0 ≤ η)
    (hsep : (S : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u δ).support X) ((ball v δ).support X)))
    (hcover : ∀u ∈ S, ∃v ∈ P, l1dist (X u) (X v) ≤ c₂)
    (hP : ∀u ∈ P, ∃t ∈ T, u ∈ t ∧ ∃e ∈ H.parentBoundary G t,
      (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hηδ : 864*η*(∑t ∈ T, ((H.parentBoundary G t).card : ℝ)) ≤ S.card)
    (hηc : 1728*η*c₂*(∑t ∈ T, ((H.parentBoundary G t).card : ℝ)) ≤ δ*S.card) :
    (∃F : CompactFamily X δ (6*max δ (2*c₂)),
      δ*(S.card : ℝ)/864 ≤ δ*(∑B ∈ F.bags, (B.card : ℝ))) ∨
    (∃F : AssignedFamily H G X η, F.radius = max δ (2*c₂) ∧ F.owners ⊆ T ∧
      δ*(S.card : ℝ)/864 ≤ F.mass) := by
  let D := max δ (2*c₂)
  have hD : 0 < D := hδ.trans_le (le_max_left _ _)
  have hcD : c₂ < D := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨u0,hu0⟩ := hS
  obtain ⟨v0,hv0,hv0d⟩ := hcover u0 hu0
  have hPne : P.Nonempty := ⟨v0,hv0⟩
  obtain ⟨W,hWP,hW,hWsep,hWcover⟩ := l1_separated_net X P hPne (show 0 ≤ 2*D by positivity)
  have hballs : (W : Set (Fin n)).Pairwise (fun u v =>
      Disjoint ((ball u D).support X) ((ball v D).support X)) := by
    intro u hu v hv huv
    exact distance_balls_disjoint X u v (hWsep u hu v hv huv).le
  have hcover' : ∀u ∈ S, ∃v ∈ W, l1dist (X u) (X v) ≤ 3*D := by
    intro u hu
    obtain ⟨p,hp,hup⟩ := hcover u hu
    obtain ⟨v,hv,hpv⟩ := hWcover p hp
    exact ⟨v,hv,(l1dist_triangle (X u) (X p) (X v)).trans (by linarith)⟩
  by_cases hsmall : 432*D*(W.card : ℝ) ≤ δ*(S.card : ℝ)
  · obtain ⟨F,hF⟩ := compact_from_net S W ⟨u0,hu0⟩ hW hδ (le_max_left _ _) hsep hcover' hsmall
    exact Or.inl ⟨F,(by nlinarith [show (0:ℝ) ≤ S.card from Nat.cast_nonneg _] : δ*(S.card : ℝ)/864 ≤ δ*(S.card : ℝ)/2).trans hF⟩
  · have hlarge : δ*(S.card : ℝ) < 432*D*(W.card : ℝ) := lt_of_not_ge hsmall
    have hcenter : ∀u ∈ W, ∃t ∈ T, u ∈ t ∧ ∃e ∈ H.parentBoundary G t,
        (G.left e = u ∨ G.right e = u) ∧ l1dist (X (G.left e)) (X (G.right e)) < D := by
      intro u hu
      obtain ⟨t,ht,hut,e,he,heu,hlen⟩ := hP u (hWP hu)
      exact ⟨t,ht,hut,e,he,heu,hlen.trans_lt hcD⟩
    let N : ℝ := ∑t ∈ T, ((H.parentBoundary G t).card : ℝ)
    obtain ⟨t0,ht0,ht0c⟩ := hP v0 hv0
    have hN : 0 < N := sum_pos (fun t ht => by exact_mod_cast hboundary t ht) ⟨t0,ht0⟩
    have hnumer : 864*η*N*D ≤ δ*(S.card : ℝ) := by
      rcases le_total δ (2*c₂) with hh | hh
      · dsimp [D]
        rw [max_eq_right hh]
        change 1728*η*c₂*N ≤ δ*(S.card : ℝ) at hηc
        linarith
      · dsimp [D]
        rw [max_eq_left hh]
        change 864*η*N ≤ (S.card : ℝ) at hηδ
        simpa [mul_comm δ] using mul_le_mul_of_nonneg_right hηδ hδ.le
    have hassign : η ≤ (W.card : ℝ)/(2*N) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) hN)).mpr
      nlinarith
    obtain ⟨F,hFD,hFT,hgain⟩ := assigned_from_net T W hW hT hroot hboundary hD hballs hcenter hassign
    exact Or.inr ⟨F,hFD,hFT,(by linarith : δ*(S.card : ℝ)/864 ≤ D*(W.card : ℝ)/2).trans hgain⟩

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uT uE uI uI2 uA uB

section
open scoped Classical
open Matrix

namespace StrongThinTree.BagDensity
noncomputable section
open Finset
open scoped Classical
variable {T : Type uT} {E : Type uE} [DecidableEq E]

omit [DecidableEq E] in
lemma sum_square_bound (F : Finset E) (a : E → ℝ) {c : ℝ}
    (hc : ∀e ∈ F, (a e)^2 ≤ c) : (∑e ∈ F, a e)^2 ≤ c*(F.card : ℝ)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F (fun _ => (1:ℝ)) a
  have hs : (∑e ∈ F, (a e)^2) ≤ (F.card : ℝ)*c := by simpa using sum_le_sum hc
  simp only [one_pow,sum_const,nsmul_eq_mul,mul_one,one_mul] at hcs
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg F.card : (0:ℝ) ≤ _)
  linarith

omit [DecidableEq E] in
lemma local_density (O F : Finset E) (a d : E → ℝ) {α γ c₁ c₂ : ℝ}
    (hF : F ⊆ O) (hFn : F.Nonempty) (hα : 0 < α) (hγ : 0 < γ)
    (hd : ∀e ∈ O, 0 ≤ d e) (hmax : ∀e ∈ F, (a e)^2 ≤ 4*c₁)
    (hmin : ∀e ∈ F, c₂/4 ≤ d e)
    (hbad : α*(O.card : ℝ)*(∑e ∈ O, d e) ≤ (∑e ∈ O, a e)^2)
    (hdom : γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ F, a e)^2) :
    α*γ*(O.card : ℝ)*c₂ ≤ 16*c₁*F.card := by
  have hFc : (0:ℝ) < F.card := by exact_mod_cast card_pos.mpr hFn
  have hOc : (0:ℝ) ≤ O.card := Nat.cast_nonneg _
  have hsum : (F.card : ℝ)*(c₂/4) ≤ ∑e ∈ O, d e := by
    calc
      _ = ∑_e ∈ F, c₂/4 := by simp
      _ ≤ ∑e ∈ F, d e := sum_le_sum hmin
      _ ≤ ∑e ∈ O, d e := sum_le_sum_of_subset_of_nonneg hF (fun e he _ => hd e he)
  have hh1 := mul_le_mul_of_nonneg_left hsum (show 0 ≤ γ*α*(O.card : ℝ) by positivity)
  have hh2 := mul_le_mul_of_nonneg_left hbad hγ.le
  have hu := sum_square_bound F a hmax
  apply (mul_le_mul_iff_right₀ hFc).mp
  linarith

lemma family_density (Ts : Finset T) (O F : T → Finset E) (a d : E → ℝ)
    {α γ c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (hc : 0 ≤ c₁)
    (hF : ∀t ∈ Ts, F t ⊆ O t) (hFn : ∀t ∈ Ts, (F t).Nonempty)
    (hd : ∀t ∈ Ts, ∀e ∈ O t, 0 ≤ d e)
    (hmax : ∀t ∈ Ts, ∀e ∈ F t, (a e)^2 ≤ 4*c₁)
    (hmin : ∀t ∈ Ts, ∀e ∈ F t, c₂/4 ≤ d e)
    (hbad : ∀t ∈ Ts, α*((O t).card : ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2)
    (hdom : ∀t ∈ Ts, γ*(∑e ∈ O t, a e)^2 ≤ (∑e ∈ F t, a e)^2)
    (hmult : (∑t ∈ Ts, (F t).card) ≤ 2*(Ts.biUnion F).card) :
    (α*γ/32)*(∑t ∈ Ts, ((O t).card : ℝ))*c₂ ≤ c₁*(Ts.biUnion F).card ∧
    (∑t ∈ Ts, (∑e ∈ F t, a e)^2/((O t).card : ℝ)) ≤ 8*c₁*(Ts.biUnion F).card := by
  have hcast : (∑t ∈ Ts, ((F t).card : ℝ)) ≤ 2*(Ts.biUnion F).card := by exact_mod_cast hmult
  constructor
  · have hh := sum_le_sum (fun t ht => local_density (O t) (F t) a d
      (hF t ht) (hFn t ht) hα hγ (hd t ht) (hmax t ht) (hmin t ht) (hbad t ht) (hdom t ht))
    simp only [←mul_sum,←sum_mul] at hh
    have hm := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 16*c₁ by positivity)
    linarith
  · have hu : ∀t ∈ Ts, (∑e ∈ F t, a e)^2/((O t).card : ℝ) ≤ 4*c₁*(F t).card := by
      intro t ht
      have hm : (0:ℝ) < (O t).card := by exact_mod_cast card_pos.mpr ((hFn t ht).mono (hF t ht))
      have hfm : ((F t).card : ℝ) ≤ (O t).card := by exact_mod_cast card_le_card (hF t ht)
      have hs := sum_square_bound (F t) a (hmax t ht)
      apply (div_le_iff₀ hm).mpr
      have hh := mul_le_mul_of_nonneg_left hfm (show 0 ≤ 4*c₁*(F t).card by positivity)
      linarith
    have hs := sum_le_sum hu
    rw [←mul_sum] at hs
    have hh := mul_le_mul_of_nonneg_left hcast (show 0 ≤ 4*c₁ by positivity)
    linarith

end
end StrongThinTree.BagDensity

namespace StrongThinTree.CaptureNumeric
noncomputable section

lemma thresholds {s a ε C N N' c₁ c₂ b δ R : ℝ}
    (hs : 0 < s) (ha : s ≤ a) (ha1 : a ≤ 1)
    (he : 0 < ε) (he1 : ε ≤ 1/2) (hC : 0 < C)
    (hN : 0 < N) (hN' : 0 < N') (hNle : N' ≤ N)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (_hb : 0 < b) (hδ : 0 < δ)
    (hscale : a*N' = s*N) (hdensity : s*N*c₂ ≤ c₁*N')
    (hcard : a*N'/C ≤ b) (hcard₂ : b ≤ 2*N')
    (hmass : b*δ = a^ε*c₁*N'/C)
    (hsmall : s^ε ≤ 1/(1728*C)) (hR : R ≤ 8*c₁*N') :
    864*s^(1+2*ε)*N ≤ b ∧
    1728*s^(1+2*ε)*c₂*N ≤ δ*b ∧
    s*c₁ ≤ δ ∧ max δ (2*c₂) ≤ 2*c₁/s ∧
    s^ε*R/(6912*C) ≤ δ*b/864 := by
  have ha0 : 0 < a := hs.trans_le ha
  have hs1 : s ≤ 1 := ha.trans ha1
  have hsε : 0 < s^ε := Real.rpow_pos_of_pos hs _
  have haε : 0 < a^ε := Real.rpow_pos_of_pos ha0 _
  have hsε1 : s^ε ≤ 1 := Real.rpow_le_one hs.le hs1 he.le
  have haε1 : a^ε ≤ 1 := Real.rpow_le_one ha0.le ha1 he.le
  have hsale : s^ε ≤ a^ε := Real.rpow_le_rpow hs.le ha he.le
  have hsmall' := (le_div_iff₀ (show 0 < 1728*C by positivity)).mp hsmall
  have hη : s^(1+2*ε) = s*(s^ε)^2 := by
    rw [Real.rpow_add hs,Real.rpow_one]
    congr 1
    rw [mul_comm (2:ℝ) ε,Real.rpow_mul hs.le,Real.rpow_two]
  have hfirst : 864*s^(1+2*ε)*N ≤ b := by
    have hc := (div_le_iff₀ hC).mp hcard
    rw [hscale] at hc
    rw [hη]
    have hh : 864*(s^ε)^2*C ≤ 1 := by linarith only [hsmall',mul_nonneg (sub_nonneg.mpr hsε1) (by positivity : 0 ≤ 1728*C*s^ε)]
    have hmul := mul_le_mul_of_nonneg_right hh (show 0 ≤ s*N by positivity)
    apply (mul_le_mul_iff_right₀ hC).mp
    linarith only [hmul,hc]
  have hsecond : 1728*s^(1+2*ε)*c₂*N ≤ δ*b := by
    have hh := mul_le_mul_of_nonneg_right hdensity (show 0 ≤ 1728*(s^ε)^2*C by positivity)
    have hh' : 1728*(s^ε)^2*C ≤ a^ε := by
      have hh := mul_le_mul_of_nonneg_right hsmall' hsε.le
      linarith only [hh,hsale]
    have hh'' := mul_le_mul_of_nonneg_right hh' (show 0 ≤ c₁*N' by positivity)
    have hm := (eq_div_iff hC.ne').mp hmass
    rw [hη]
    apply (mul_le_mul_iff_right₀ hC).mp
    linarith only [hh,hh'',hm]
  have hlower : s*c₁ ≤ δ := by
    have hpow := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show ε ≤ 1-ε by linarith)
    have hex : s = s^ε*s^(1-ε) := by
      rw [←Real.rpow_add hs]
      have heq : ε+(1-ε) = 1 := by ring
      rw [heq,Real.rpow_one]
    have hh : 2*C*s ≤ s^ε := by
      have hc : 2*C*s^(1-ε) ≤ 1 := by linarith only [hsmall',mul_le_mul_of_nonneg_left hpow hC.le]
      have hm := mul_le_mul_of_nonneg_left hc hsε.le
      linarith only [hm,congrArg (fun x : ℝ => 2*C*x) hex]
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ c₁*N' by positivity)
    have hh'' := mul_le_mul_of_nonneg_right hsale (show 0 ≤ c₁*N' by positivity)
    have hm := (eq_div_iff hC.ne').mp hmass
    have hbc := mul_le_mul_of_nonneg_right hcard₂ hδ.le
    have hbcC := mul_le_mul_of_nonneg_right hbc hC.le
    apply (mul_le_mul_iff_right₀ (show 0 < 2*C*N' by positivity)).mp
    linarith only [hh',hh'',hm,hbcC]
  have hupperδ : δ ≤ c₁/s := by
    have hh := mul_le_mul_of_nonneg_right hcard hδ.le
    have hm := (eq_div_iff hC.ne').mp hmass
    have hc := (div_le_iff₀ hC).mp hcard
    have hhC := mul_le_mul_of_nonneg_right hh hC.le
    have hhA := mul_le_mul_of_nonneg_right haε1 (show 0 ≤ c₁*N' by positivity)
    have hhS := mul_le_mul_of_nonneg_right ha (show 0 ≤ N'*δ by positivity)
    apply (le_div_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hN').mp
    have hcan : (a*N'/C)*δ*C = a*N'*δ := by field_simp
    rw [hcan] at hhC
    linarith only [hhC,hm,hhA,hhS]
  have hupperc : c₂ ≤ c₁/s := by
    have hh := mul_le_mul_of_nonneg_left hNle (show 0 ≤ s*c₂ by positivity)
    apply (le_div_iff₀ hs).mpr
    apply (mul_le_mul_iff_right₀ hN').mp
    linarith only [hh,hdensity]
  refine ⟨hfirst,hsecond,hlower,max_le ?_ ?_,?_⟩
  · have hh : 0 ≤ c₁/s := by positivity
    rw [mul_div_assoc]
    linarith only [hh,hupperδ]
  · have hh := mul_le_mul_of_nonneg_left hupperc (show (0:ℝ) ≤ 2 by norm_num)
    simpa only [mul_div_assoc] using hh
  · have hh := mul_le_mul_of_nonneg_left hR hsε.le
    have hh' := mul_le_mul_of_nonneg_right hsale (show 0 ≤ 8*c₁*N' by positivity)
    have hm := (eq_div_iff hC.ne').mp hmass
    apply (div_le_iff₀ (show 0 < 6912*C by positivity)).mpr
    linarith only [hh,hh',hm]

end
end StrongThinTree.CaptureNumeric

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma density_spectral_input {I : Type uI} [Fintype I]
    (a d : I → ℝ) {c₁ c₂ α : ℝ}
    (hc₁ : 0 ≤ c₁) (hα : 0 ≤ α) (ha : ∀i, 0 ≤ a i)
    (hmin : ∀i, c₁ ≤ (a i)^2) (hd : ∀i, d i ≤ c₂)
    (hscale : α*c₂ ≤ c₁) :
    α*(Fintype.card I : ℝ)*(∑i, d i) ≤ (∑i, a i)^2 := by
  have hN : (0:ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  have hsum : (Fintype.card I : ℝ)*Real.sqrt c₁ ≤ ∑i, a i := by
    simpa only [sum_const,nsmul_eq_mul,card_univ] using
      sum_le_sum (fun i (_ : i ∈ univ) => Real.sqrt_le_iff.mpr ⟨ha i,hmin i⟩)
  have hsum0 : 0 ≤ ∑i, a i := sum_nonneg (fun i _ => ha i)
  have hsum2 : c₁*(Fintype.card I : ℝ)^2 ≤ (∑i, a i)^2 := by
    have hh := (sq_le_sq₀ (mul_nonneg hN (Real.sqrt_nonneg _)) hsum0).mpr hsum
    rw [mul_pow,Real.sq_sqrt hc₁] at hh
    linarith only [hh]
  have hdsum : (∑i, d i) ≤ (Fintype.card I : ℝ)*c₂ := by
    simpa only [sum_const,nsmul_eq_mul,card_univ] using sum_le_sum (fun i (_ : i ∈ univ) => hd i)
  have h1 := mul_le_mul_of_nonneg_left hdsum (mul_nonneg hα hN)
  have h2 := mul_le_mul_of_nonneg_right hscale (sq_nonneg (Fintype.card I : ℝ))
  linarith only [h1,h2,hsum2]

lemma homogeneous_family (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ H.parentBoundary G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
    (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ l1dist (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, l1dist (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hbad : ∀t ∈ T, α*((H.parentBoundary G t).card : ℝ)*
      (∑e ∈ H.parentBoundary G t, l1dist (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2))) :
    let s := α*γ/32
    let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((H.parentBoundary G t).card : ℝ)
    (∃δ Δ : ℝ, ∃B : CompactFamily X δ Δ,
      s*c₁ ≤ δ ∧ Δ ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ δ*(∑D ∈ B.bags, (D.card : ℝ))) ∨
    (∃B : AssignedFamily H G X (s^(1+2*ε)), B.owners ⊆ T ∧
      s*c₁ ≤ B.radius ∧ B.radius ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass) := by
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => l1dist (X (G.left e)) (X (G.right e))
  let E := T.biUnion F
  let N : ℝ := ∑t ∈ T, ((H.parentBoundary G t).card : ℝ)
  let N' : ℝ := E.card
  let s := α*γ/32
  let C : ℝ := 1024/ε^2
  let R := ∑t ∈ T, (∑e ∈ F t, a e)^2/((H.parentBoundary G t).card : ℝ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hEn : E.Nonempty := by
    obtain ⟨t,ht⟩ := hTne
    obtain ⟨e,he⟩ := hFn t ht
    exact ⟨e,mem_biUnion.mpr ⟨t,ht,he⟩⟩
  have hN' : 0 < N' := by dsimp [N']; exact_mod_cast card_pos.mpr hEn
  have hboundary : ∀t ∈ T, 0 < (H.parentBoundary G t).card :=
    fun t ht => card_pos.mpr ((hFn t ht).mono (hF t ht))
  have hN : 0 < N := by
    apply sum_pos (fun t ht => ?_) hTne
    exact_mod_cast hboundary t ht
  have hNle : N' ≤ N := by
    have h1 : E.card ≤ ∑t ∈ T, (F t).card := card_biUnion_le
    have h2 : (∑t ∈ T, (F t).card) ≤ ∑t ∈ T, (H.parentBoundary G t).card :=
      sum_le_sum (fun t ht => card_le_card (hF t ht))
    dsimp [N',N]
    exact_mod_cast h1.trans h2
  have hd0 : ∀e, 0 ≤ d e := fun e => l1dist_nonneg _ _
  obtain ⟨hdensity,hR⟩ := StrongThinTree.BagDensity.family_density T (H.parentBoundary G) F a d
    hα hγ hc₁.le hF hFn (fun t ht e he => hd0 e) hmax hdmin hbad hdom
    (H.subset_boundary_multiplicity G T hT hroot F hF)
  change s*N*c₂ ≤ c₁*N' at hdensity
  change R ≤ 8*c₁*N' at hR
  let specα := s*N/N'
  have ha0 : 0 < specα := div_pos (mul_pos hs hN) hN'
  have hscale : specα*N' = s*N := div_mul_cancel₀ _ hN'.ne'
  have has : s ≤ specα := by
    apply (le_div_iff₀ hN').mpr
    exact mul_le_mul_of_nonneg_left hNle hs.le
  have had : specα*c₂ ≤ c₁ := by
    change (s*N/N')*c₂ ≤ c₁
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hN').mpr hdensity
  have hminE : ∀e ∈ E, c₁ ≤ (a e)^2 := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hmin t ht e he
  have hmaxE : ∀e ∈ E, d e ≤ c₂ := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hdmax t ht e he
  let u : E → Fin n := fun e => G.left e.val
  let v : E → Fin n := fun e => G.right e.val
  have hIE : Fintype.card E = E.card := Fintype.card_coe E
  have hI : 0 < Fintype.card E := by rw [hIE]; exact card_pos.mpr hEn
  have hbnd : specα*(Fintype.card E : ℝ)*(∑e : E, ‖Y (u e)-Y (v e)‖^2) ≤
      (∑e : E, (Y (u e)-Y (v e)).ofLp e.val)^2 :=
    density_spectral_input (fun e : E => a e.val) (fun e : E => ‖Y (u e)-Y (v e)‖^2)
      hc₁.le ha0.le (fun e => hpositive e.val) (fun e => hminE e.val e.property)
      (fun e => (hcontract (u e) (v e)).trans (hmaxE e.val e.property)) had
  obtain ⟨ha1,S,δ,hδ,hSE,hS2,hSc,hmass,hsep⟩ := normalized_small_balls X Y u v
    (fun e : E => e.val) Subtype.val_injective hI ha0 he he1 hc₁
    (fun e => ⟨hpositive e.val,hminE e.val e.property⟩) hbnd hcontract
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hSc0 : (0:ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have hcard : specα*N'/C ≤ (S.card : ℝ) := by
    apply (div_le_iff₀ hC).mpr
    dsimp [C]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos he)).mpr
    rw [hIE] at hSc
    change ε^2*specα*N' ≤ _ at hSc
    linarith only [hSc]
  have hcard₂ : (S.card : ℝ) ≤ 2*N' := by
    have hh := card_le_card hSE
    have h1 := card_union_le (univ.image u) (univ.image v)
    have h2 := card_image_le (f := u) (s := univ)
    have h3 := card_image_le (f := v) (s := univ)
    simp only [card_univ,hIE] at h2 h3
    have hSc : S.card ≤ 2*E.card := by omega
    dsimp [N']; exact_mod_cast hSc
  rw [hIE] at hmass
  change (S.card : ℝ)*δ = specα^ε*c₁*N'/C at hmass
  obtain ⟨hηδ,hηc,hlower,hupper,hgain⟩ := StrongThinTree.CaptureNumeric.thresholds
    hs has ha1 he (by linarith : ε ≤ 1/2) hC hN hN' hNle hc₁ hc₂ hSc0 hδ
    hscale hdensity hcard hcard₂ hmass hsmall hR
  let P := T.biUnion (fun t => t.filter (fun w => ∃e ∈ F t, G.left e=w ∨ G.right e=w))
  have hP : ∀w ∈ P, ∃t ∈ T, w ∈ t ∧ ∃e ∈ H.parentBoundary G t,
      (G.left e=w ∨ G.right e=w) ∧ l1dist (X (G.left e)) (X (G.right e)) ≤ c₂ := by
    intro w hw
    obtain ⟨t,ht,hw⟩ := mem_biUnion.mp hw
    obtain ⟨hwt,e,he,hew⟩ := mem_filter.mp hw
    exact ⟨t,ht,hwt,e,hF t ht he,hew,hdmax t ht e he⟩
  have hEnd : ∀e ∈ E, ∃w ∈ P, (G.left e=w ∨ G.right e=w) := by
    intro e he
    obtain ⟨t,ht,het⟩ := mem_biUnion.mp he
    have hc := (mem_filter.mp (hF t ht het)).2
    rcases hc with hc | hc
    · exact ⟨G.left e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inl rfl⟩⟩,Or.inl rfl⟩
    · exact ⟨G.right e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inr rfl⟩⟩,Or.inr rfl⟩
  have hcover : ∀w ∈ S, ∃p ∈ P, l1dist (X w) (X p) ≤ c₂ := by
    intro w hw
    rcases mem_union.mp (hSE hw) with hw | hw
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [u,hp',l1dist_self] using hc₂.le
      · simpa [u,d,hp'] using hmaxE e.val e.property
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [v,d,hp',l1dist_comm] using hmaxE e.val e.property
      · simpa [v,hp',l1dist_self] using hc₂.le
  have hNcast : ∑t ∈ T, ((H.parentBoundary G t).card : ℝ) = N := rfl
  have hη : 0 ≤ s^(1+2*ε) := (Real.rpow_pos_of_pos hs _).le
  obtain hcomp | hass := capture_small_balls T S P hS hT hroot hboundary hδ hc₂ hη
    hsep hcover hP hηδ hηc
  · obtain ⟨B,hB⟩ := hcomp
    refine Or.inl ⟨δ,6*max δ (2*c₂),B,hlower,?_,hgain.trans hB⟩
    change 6*max δ (2*c₂) ≤ 12*c₁/s
    calc
      _ ≤ 6*(2*c₁/s) := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = 12*c₁/s := by ring
  · obtain ⟨B,hBD,hBT,hB⟩ := hass
    refine Or.inr ⟨B,hBT,?_,?_,hgain.trans hB⟩
    · rw [hBD]
      exact hlower.trans (le_max_left _ _)
    · rw [hBD]
      have hh : 0 ≤ c₁/s := by positivity
      calc
        max δ (2*c₂) ≤ 2*c₁/s := hupper
        _ ≤ 12*c₁/s := by rw [mul_div_assoc,mul_div_assoc]; linarith only [hh]

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.ScaleSelection
noncomputable section
open Finset
open scoped Classical

lemma integer_dyadic {x : ℝ} (hx : 0 < x) :
    2^(⌊Real.logb 2 x⌋ : ℝ) ≤ x ∧ x < 2*2^(⌊Real.logb 2 x⌋ : ℝ) := by
  have h1 := (Real.le_logb_iff_rpow_le (by norm_num) hx).mp (Int.floor_le (Real.logb 2 x))
  have h2 := (Real.logb_lt_iff_lt_rpow (by norm_num) hx).mp (Int.lt_floor_add_one (Real.logb 2 x))
  rw [Real.rpow_add (by norm_num),Real.rpow_one] at h2
  constructor
  · exact h1
  · linarith only [h2]

lemma integer_dyadic_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ⌊Real.logb 2 x⌋ ≤ ⌊Real.logb 2 y⌋ :=
  Int.floor_mono (Real.logb_le_logb_of_le (by norm_num) hx hxy)

lemma integer_scale_offset {x y K : ℝ} {L : ℕ}
    (hx : 0 < x) (hxy : x ≤ y) (hK : y ≤ K*x)
    (hL : Real.logb 2 K+1 < L) :
    0 ≤ ⌊Real.logb 2 y⌋-⌊Real.logb 2 x⌋ ∧
      ⌊Real.logb 2 y⌋-⌊Real.logb 2 x⌋ < L := by
  have hy : 0 < y := hx.trans_le hxy
  have hK0 : 0 < K := by nlinarith only [hK,hy,hx]
  have hlogs : Real.logb 2 y ≤ Real.logb 2 K+Real.logb 2 x := by
    rw [←Real.logb_mul hK0.ne' hx.ne']
    exact Real.logb_le_logb_of_le (by norm_num) hy hK
  constructor
  · exact sub_nonneg.mpr (integer_dyadic_mono hx hxy)
  · have h1 := Int.floor_le (Real.logb 2 y)
    have h2 := Int.lt_floor_add_one (Real.logb 2 x)
    have hh : ((⌊Real.logb 2 y⌋-⌊Real.logb 2 x⌋ : ℤ) : ℝ) < L := by
      push_cast
      linarith only [h1,h2,hlogs,hL]
    exact_mod_cast hh

lemma select_fibers {I : Type uI2} {A : Type uA} {B : Type uB} [DecidableEq I] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Nonempty B]
    (T : Finset I) (a : I → A) (b : I → B) (w : I → ℝ) :
    ∃choice : A → B,
      (∑i ∈ T, w i)/(Fintype.card B : ℝ) ≤
        ∑i ∈ T.filter (fun i => b i = choice (a i)), w i := by
  have hB : (0:ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos (α := B)
  have hex : ∀x : A, ∃y : B,
      (∑i ∈ T.filter (fun i => a i=x), w i)/(Fintype.card B : ℝ) ≤
        ∑i ∈ (T.filter (fun i => a i=x)).filter (fun i => b i=y), w i := by
    intro x
    obtain ⟨y,hy,hgain⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
      (s := T.filter (fun i => a i=x)) (t := univ) (f := b) (w := w)
      (fun _ _ => mem_univ _) univ_nonempty
      (b := (∑i ∈ T.filter (fun i => a i=x), w i)/(Fintype.card B : ℝ)) (by
        simp only [card_univ,nsmul_eq_mul]
        exact (mul_div_cancel₀ _ hB.ne').le)
    exact ⟨y,hgain⟩
  choose choice hchoice using hex
  refine ⟨choice,?_⟩
  have hs := sum_le_sum (s := T.image a) (fun x hx => hchoice x)
  rw [←sum_div] at hs
  have hleft : (∑x ∈ T.image a, ∑i ∈ T.filter (fun i => a i=x), w i) = ∑i ∈ T, w i := by
    exact sum_fiberwise_of_maps_to (fun i hi => mem_image_of_mem a hi) w
  rw [hleft] at hs
  have hright : (∑x ∈ T.image a, ∑i ∈ (T.filter (fun i => a i=x)).filter
      (fun i => b i=choice x), w i) = ∑i ∈ T.filter (fun i => b i=choice (a i)), w i := by
    simp only [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    rw [sum_eq_single (a i)]
    · simp
    · intro x hx hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (mem_image_of_mem a hi)).elim
  rw [hright] at hs
  exact hs

lemma residue_spacing {H : ℕ} (_hH : 0 < H) {n n' : ℤ}
    (hlt : n' < n) (hmod : n'%H = n%H) : n' ≤ n-H := by
  have hd : (H:ℤ) ∣ n-n' := Int.ModEq.dvd hmod
  have hh := Int.le_of_dvd (sub_pos.mpr hlt) hd
  omega

lemma separated_scales {s ρ : ℝ} {H : ℕ} {n n' : ℤ}
    (hs : 0 < s) (hρ : 0 < ρ)
    (hH : Real.logb 2 (24/(ρ*s^2)) < H)
    (hgap : n' ≤ n-H) : 24*2^(n':ℝ)/s < ρ*s*2^(n:ℝ) := by
  have hpow : 24/(ρ*s^2) < (2:ℝ)^(H:ℝ) :=
    (Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity)).mp hH
  have hgapR : (n':ℝ)+(H:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : n'+H ≤ n)
  have hle : (2:ℝ)^(n':ℝ)*(2:ℝ)^(H:ℝ) ≤ (2:ℝ)^(n:ℝ) := by
    rw [←Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hgapR
  have hp := Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (n':ℝ)
  have hh := (div_lt_iff₀ (show 0 < ρ*s^2 by positivity)).mp hpow
  have hm := mul_lt_mul_of_pos_left hh hp
  have hm' := mul_le_mul_of_nonneg_right hle (show 0 ≤ ρ*s^2 by positivity)
  apply (div_lt_iff₀ hs).mpr
  linarith only [hm,hm']

end
end StrongThinTree.ScaleSelection

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.CompactPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uJ uJ2 uJ3

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset _root_.OAI.StrongThinTree.Geometry Geometry.RadialShell
open scoped Classical

namespace CompactPackage
variable {n m h : ℕ} {G : MultiGraph n m} {X : Fin n → Fin h → ℝ}

lemma finite_bound {k : ℕ} (hk : G.EdgeConnected k) (hX : ∀v, binary (X v))
    {q : ℕ} (F : Fin q → CompactPackage X)
    (hnext : ∀i j : Fin q, i.val+1=j.val → (F j).diameter ≤ (F i).radius/12) :
    (k:ℝ)/4*(∑i, (F i).mass) ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  by_cases hq : q=0
  · subst q
    simp only [Finset.univ_eq_empty,Finset.sum_empty,mul_zero]
    exact sum_nonneg (fun e _ => l1dist_nonneg _ _)
  · have hq' : 0 < q := Nat.pos_of_ne_zero hq
    let ind : ℕ → Fin q := fun i => ⟨i%q,Nat.mod_lt _ hq'⟩
    have hh := binary_compact_bound G hk X hX q
      (fun i => (F (ind i)).radius) (fun i => (F (ind i)).diameter)
      (fun i => (F (ind i)).family) (by
        intro i hi
        apply hnext
        simp only [ind,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt (show i<q by omega)])
    have he : (∑i : Fin q, (F i).mass) = ∑i ∈ range q, (F (ind i)).mass := by
      rw [←Fin.sum_univ_eq_sum_range]
      apply sum_congr rfl
      intro i hi
      have hind : ind i.val=i := by apply Fin.ext; exact Nat.mod_eq_of_lt i.isLt
      rw [hind]
    rw [he]
    exact hh

lemma ordered_bound {J : Type uJ} [LinearOrder J] {k : ℕ} (hk : G.EdgeConnected k) (hX : ∀v, binary (X v))
    (S : Finset J) (F : S → CompactPackage X)
    (hgeo : ∀i j : S, j.val < i.val → (F j).diameter ≤ (F i).radius/12) :
    (k:ℝ)/4*(∑i, (F i).mass) ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  let e := S.orderIsoOfFin rfl
  let f : Fin S.card ≃ S := Fin.revPerm.trans e.toEquiv
  have hh := finite_bound hk hX (fun i => F (f i)) (by
    intro i j hij
    apply hgeo
    change (e j.rev).val < (e i.rev).val
    exact e.strictMono (Fin.rev_lt_rev.mpr (show i<j by omega)))
  rw [f.sum_comp (fun i => (F i).mass)] at hh
  exact hh
end CompactPackage

namespace Hierarchy
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Fin h → ℝ}

namespace AssignedSequence
variable {η q ρ : ℝ}

lemma mass_eq (L : List (AssignedFamily H G X η)) : mass L = (L.map AssignedFamily.mass).sum := by
  induction L with
  | nil => rfl
  | cons F L ih => simpa only [mass,List.map_cons,List.sum_cons] using congrArg (F.mass+·) ih

lemma geometric_of_pairwise (hρ : 0 ≤ ρ) (L : List (AssignedFamily H G X η))
    (hL : L.Pairwise (fun F F' => F'.radius ≤ ρ*F.radius)) : GeometricAt ρ L := by
  induction L with
  | nil => trivial
  | cons F L ih =>
    refine ⟨?_,ih (List.pairwise_cons.mp hL).2⟩
    cases L with
    | nil => exact mul_nonneg hρ F.positive.le
    | cons F' L => exact (List.pairwise_cons.mp hL).1 F' (by simp)

lemma ratios_of_mem (L : List (AssignedFamily H G X (6144/q)))
    (hL : ∀F ∈ L, F.BoundaryRatio ρ) : Ratios ρ L := by
  induction L with
  | nil => trivial
  | cons F L ih => exact ⟨hL F (by simp),ih (fun F' hF' => hL F' (by simp [hF']))⟩

lemma fresh_of_pairwise (L : List (AssignedFamily H G X (6144/q)))
    (hL : L.Pairwise (fun F F' => Disjoint F.owners F'.owners))
    (E : Finset (Finset (Fin n))) (hE : ∀F ∈ L, Disjoint E F.owners) : Fresh E L := by
  induction L generalizing E with
  | nil => trivial
  | cons F L ih =>
    refine ⟨hE F (by simp),ih (List.pairwise_cons.mp hL).2 _ ?_⟩
    intro F' hF'
    exact disjoint_union_left.mpr ⟨hE F' (by simp [hF']), (List.pairwise_cons.mp hL).1 F' hF'⟩

lemma finite_bound (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    {r : ℕ} (F : Fin r → AssignedFamily H G X (6144/q))
    (hgeo : ∀i j, i<j → (F j).radius ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).BoundaryRatio ρ)
    (hdis : ∀i j, i<j → Disjoint (F i).owners (F j).owners) :
    (q/8192)*(∑i, (F i).mass) ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  have hh := assigned_bound hX hq hconn hρ hρsmall (List.ofFn F)
    (geometric_of_pairwise hρ.le _ (List.pairwise_ofFn.mpr hgeo))
    (ratios_of_mem _ (by
      intro A hA
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hA
      exact hR i))
    (fresh_of_pairwise _ (List.pairwise_ofFn.mpr hdis) ∅ (by simp))
  rw [mass_eq,List.map_ofFn,List.sum_ofFn] at hh
  exact hh

lemma ordered_bound {J : Type uJ2} [LinearOrder J] (hX : ∀v, binary (X v)) (hq : 0 < q)
    (hconn : H.LocallyConnectedReal G q) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (S : Finset J) (F : S → AssignedFamily H G X (6144/q))
    (hgeo : ∀i j : S, j.val < i.val → (F j).radius ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).BoundaryRatio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    (q/8192)*(∑i, (F i).mass) ≤ ∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  let e := S.orderIsoOfFin rfl
  let f : Fin S.card ≃ S := Fin.revPerm.trans e.toEquiv
  have hh := finite_bound hX hq hconn hρ hρsmall (fun i => F (f i)) (by
    intro i j hij
    apply hgeo
    change (e j.rev).val < (e i.rev).val
    exact e.strictMono (Fin.rev_lt_rev.mpr hij))
    (fun i => hR (f i)) (fun i j hij => hdis _ _ (f.injective.ne hij.ne))
  rw [f.sum_comp (fun i => (F i).mass)] at hh
  exact hh
end AssignedSequence
end Hierarchy
end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset _root_.OAI.StrongThinTree.Geometry Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Fin h → ℝ}

namespace CapturedFamily
variable {η : ℝ}

lemma mass_nonneg (F : CapturedFamily H G X η) : 0 ≤ F.mass := by
  cases F with
  | inl F => exact mul_nonneg F.family.radius_pos.le (sum_nonneg (fun D _ => Nat.cast_nonneg _))
  | inr F => exact mul_nonneg (sum_nonneg (fun i _ => Nat.cast_nonneg _)) F.positive.le

lemma mixed_bound {J : Type uJ3} [LinearOrder J] {q : ℕ}
    (hq : 0 < q) (hk : G.EdgeConnected q) (hX : ∀v, binary (X v))
    (hconn : H.LocallyConnectedReal G q) {ρ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (S : Finset J) (F : S → CapturedFamily H G X (6144/q))
    (hgeo : ∀i j : S, j.val < i.val → (F j).upper ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).Ratio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    ((q:ℝ)/8192)*(∑i, (F i).mass) ≤ 2*∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
  let C : Finset S := univ.filter (fun i => ∃P, F i=Sum.inl P)
  let A : Finset S := univ\C
  have hexC : ∀i : C, ∃P, F i.val=Sum.inl P := fun i => (mem_filter.mp i.property).2
  have hexA : ∀i : A, ∃P, F i.val=Sum.inr P := by
    intro i
    cases hh : F i.val with
    | inl P =>
      have hi : i.val ∉ C := (mem_sdiff.mp i.property).2
      exact (hi (mem_filter.mpr ⟨mem_univ _,⟨P,hh⟩⟩)).elim
    | inr P => exact ⟨P,rfl⟩
  let FC : C → CompactPackage X := fun i => Classical.choose (hexC i)
  let FA : A → AssignedFamily H G X (6144/q) := fun i => Classical.choose (hexA i)
  have hFC : ∀i : C, F i.val=Sum.inl (FC i) := fun i => Classical.choose_spec (hexC i)
  have hFA : ∀i : A, F i.val=Sum.inr (FA i) := fun i => Classical.choose_spec (hexA i)
  have hC := CompactPackage.ordered_bound hk hX C FC (by
    intro i j hij
    have hh := hgeo i.val j.val hij
    rw [hFC i,hFC j] at hh
    change (FC j).diameter ≤ ρ*(FC i).radius at hh
    have hr : ρ ≤ 1/12 := hρsmall.trans (by norm_num)
    have hm := mul_le_mul_of_nonneg_right hr (FC i).family.radius_pos.le
    exact hh.trans (by linarith only [hm]))
  have hA := AssignedSequence.ordered_bound hX (show (0:ℝ)<q by exact_mod_cast hq)
    hconn hρ hρsmall A FA (by
      intro i j hij
      have hh := hgeo i.val j.val hij
      rw [hFA i,hFA j] at hh
      exact hh)
    (by intro i; have hh := hR i.val; rw [hFA i] at hh; exact hh)
    (by
      intro i j hij
      have hh := hdis i.val j.val (Subtype.val_injective.ne hij)
      rw [hFA i,hFA j] at hh
      exact hh)
  have hsumC : (∑i : C, (FC i).mass) = ∑i ∈ C, (F i).mass := by
    rw [←sum_coe_sort C (fun i => (F i).mass)]
    apply sum_congr rfl
    intro i hi
    rw [hFC i]
    rfl
  have hsumA : (∑i : A, (FA i).mass) = ∑i ∈ A, (F i).mass := by
    rw [←sum_coe_sort A (fun i => (F i).mass)]
    apply sum_congr rfl
    intro i hi
    rw [hFA i]
    rfl
  rw [hsumC] at hC
  rw [hsumA] at hA
  have hCn : 0 ≤ ∑i ∈ C, (F i).mass := sum_nonneg (fun i _ => mass_nonneg (F i))
  have hcoef : (q:ℝ)/8192 ≤ (q:ℝ)/4 := by
    have hh : (0:ℝ) ≤ q := Nat.cast_nonneg _
    linarith
  have hC' := (mul_le_mul_of_nonneg_right hcoef hCn).trans hC
  have he : (∑i ∈ A, (F i).mass)+(∑i ∈ C, (F i).mass) = ∑i : S, (F i).mass :=
    sum_sdiff (subset_univ C)
  rw [←he,mul_add]
  linarith only [hA,hC']
end CapturedFamily
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}
namespace CapturedFamily
lemma scale_bound {q : ℕ} (hq : 0 < q) (hk : G.EdgeConnected q)
    (hX : ∀v, binary (X v)) (hconn : H.LocallyConnectedReal G q)
    {ρ s : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536) (hs : 0 < s)
    {R : ℕ} (hR : 0 < R) (hlog : Real.logb 2 (24/(ρ*s^2)) < R)
    (S : Finset ℤ) (F : S → CapturedFamily H G X (6144/q))
    (hlow : ∀i : S, s*2^(i.val:ℝ) ≤ (F i).radius)
    (hupp : ∀i : S, (F i).upper ≤ 24*2^(i.val:ℝ)/s)
    (hratio : ∀i, (F i).Ratio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    ((q:ℝ)/8192)*(∑i, (F i).mass) ≤
      2*R*(∑e : Fin m, l1dist (X (G.left e)) (X (G.right e))) := by
  let residue : ℤ → Fin R := fun i => ⟨(i%R).toNat, by
    have hn := Int.emod_nonneg i (show (R:ℤ)≠0 by omega)
    have hh := Int.emod_lt_of_pos i (show (0:ℤ)<R by omega)
    omega⟩
  let C : Fin R → Finset S := fun r => univ.filter (fun i => residue i.val=r)
  have hbound : ∀r : Fin R, ((q:ℝ)/8192)*(∑i ∈ C r, (F i).mass) ≤
      2*∑e : Fin m, l1dist (X (G.left e)) (X (G.right e)) := by
    intro r
    have hh := mixed_bound hq hk hX hconn hρ hρsmall (C r) (fun i => F i.val) (by
      intro i j hij
      have hi := (mem_filter.mp i.property).2
      have hj := (mem_filter.mp j.property).2
      have hmod : j.val.val%R=i.val.val%R := by
        have he := congrArg Fin.val (hj.trans hi.symm)
        dsimp [residue] at he
        have hn1 := Int.emod_nonneg i.val.val (show (R:ℤ)≠0 by omega)
        have hn2 := Int.emod_nonneg j.val.val (show (R:ℤ)≠0 by omega)
        omega
      have hsep := ScaleSelection.separated_scales hs hρ hlog
        (ScaleSelection.residue_spacing hR hij hmod)
      exact (hupp j.val).trans (hsep.le.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hlow i.val) hρ.le)))
      (fun i => hratio i.val)
      (fun i j hij => hdis i.val j.val (Subtype.val_injective.ne hij))
    rw [←sum_coe_sort (C r) (fun i => (F i).mass)]
    exact hh
  have hh := sum_le_sum (s := univ) (fun r (_ : r ∈ univ) => hbound r)
  rw [←mul_sum] at hh
  have he : (∑r : Fin R, ∑i ∈ C r, (F i).mass) = ∑i : S, (F i).mass := by
    exact sum_fiberwise_of_maps_to (fun _ _ => mem_univ _) (fun i => (F i).mass)
  rw [he] at hh
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc,mul_left_comm] using hh
end CapturedFamily
end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma capturePackage (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ H.parentBoundary G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
    (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ l1dist (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, l1dist (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hbad : ∀t ∈ T, α*((H.parentBoundary G t).card : ℝ)*
      (∑e ∈ H.parentBoundary G t, l1dist (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2)))
    {q : ℕ} {ρ : ℝ}
    (hassign : (6144:ℝ)/q ≤ (α*γ/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card) :
    let s := α*γ/32
    let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((H.parentBoundary G t).card : ℝ)
    ∃B : CapturedFamily H G X (6144/q), B.owners ⊆ T ∧ B.Ratio ρ ∧
      s*c₁ ≤ B.radius ∧ B.upper ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass := by
  obtain hC | hA := homogeneous_family T F Y hTne hT hroot hF hFn hα hγ he he1 hc₁ hc₂
    hcontract hpositive hmin hmax hdmin hdmax hbad hdom hsmall
  · obtain ⟨δ,Δ,B,hl,hu,hg⟩ := hC
    exact ⟨.inl ⟨δ,Δ,B⟩,empty_subset _,trivial,hl,hu,hg⟩
  · obtain ⟨B,hBT,hl,hu,hg⟩ := hA
    refine ⟨.inr (B.weaken hassign),hBT,?_,hl,hu,hg⟩
    intro i
    apply hratio
    apply hBT
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩

end
end StrongThinTree.MultiGraph.Hierarchy

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma homogeneous_scale_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, binary (X v))
    (hconn : H.LocallyConnectedReal G q)
    (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (idx : Finset (Fin n) → ℤ) (off : Finset (Fin n) → Fin L)
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ H.parentBoundary G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε ρ : ℝ} (hα : 0 < α) (hγ : 0 < γ) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, 2^(idx t:ℝ) ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*2^(idx t:ℝ))
    (hdmin : ∀t ∈ T, ∀e ∈ F t, 2^((idx t:ℝ)+(off t).val) ≤ l1dist (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, l1dist (X (G.left e)) (X (G.right e)) ≤ 4*2^((idx t:ℝ)+(off t).val))
    (hbad : ∀t ∈ T, α*((H.parentBoundary G t).card : ℝ)*
      (∑e ∈ H.parentBoundary G t, l1dist (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*γ/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlog : Real.logb 2 (24/(ρ*(α*γ/32)^2)) < R) :
    let s := α*γ/32
    let W := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((H.parentBoundary G t).card : ℝ)
    ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*(W/(L:ℝ)) ≤
      2*R*(∑e : Fin m, l1dist (X (G.left e)) (X (G.right e))) := by
  let : NeZero L := ⟨Nat.ne_of_gt hL⟩
  let s := α*γ/32
  let w : Finset (Fin n) → ℝ := fun t =>
    (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/((H.parentBoundary G t).card : ℝ)
  let c := s^ε/(6912*(1024/ε^2))
  have hs : 0 < s := by dsimp [s]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  obtain ⟨choice,hchoice⟩ := ScaleSelection.select_fibers T idx off w
  simp only [Fintype.card_fin] at hchoice
  let U := T.filter (fun t => off t=choice (idx t))
  let S := U.image idx
  let B : S → Finset (Finset (Fin n)) := fun i => U.filter (fun t => idx t=i.val)
  have hBT : ∀i : S, B i ⊆ T := fun i => (filter_subset _ _).trans (filter_subset _ _)
  have hBn : ∀i : S, (B i).Nonempty := by
    intro i
    obtain ⟨t,ht,heq⟩ := mem_image.mp i.property
    exact ⟨t,mem_filter.mpr ⟨ht,heq⟩⟩
  have hi : ∀i : S, ∀t ∈ B i, idx t=i.val := fun i t ht => (mem_filter.mp ht).2
  have hoff : ∀i : S, ∀t ∈ B i, off t=choice i.val := by
    intro i t ht
    have hh := (mem_filter.mp (mem_filter.mp ht).1).2
    change off t=choice (idx t) at hh
    rw [hi i t ht] at hh
    exact hh
  have hex : ∀i : S, ∃P : CapturedFamily H G X (6144/q),
      P.owners ⊆ B i ∧ P.Ratio ρ ∧ s*2^(i.val:ℝ) ≤ P.radius ∧
      P.upper ≤ 12*2^(i.val:ℝ)/s ∧ c*(∑t ∈ B i, w t) ≤ P.mass := by
    intro i
    have hp1 : (0:ℝ) < 2^(i.val:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have hp2 : (0:ℝ) < 4*2^((i.val:ℝ)+(choice i.val).val) := by positivity
    obtain ⟨P,hP⟩ := capturePackage (B i) F Y (hBn i) ((hBT i).trans hT)
      (fun t ht => hroot t (hBT i ht)) (fun t ht => hF t (hBT i ht))
      (fun t ht => hFn t (hBT i ht)) hα hγ he he1 hp1 hp2 hcontract hpositive
      (by intro t ht e he; simpa only [hi i t ht] using hmin t (hBT i ht) e he)
      (by intro t ht e he; simpa only [hi i t ht] using hmax t (hBT i ht) e he)
      (by
        intro t ht e he
        have hh := hdmin t (hBT i ht) e he
        rw [hi i t ht,hoff i t ht] at hh
        simpa only [mul_div_cancel_left₀ _ (by norm_num : (4:ℝ)≠0)] using hh)
      (by intro t ht e he; simpa only [hi i t ht,hoff i t ht] using hdmax t (hBT i ht) e he)
      (fun t ht => hbad t (hBT i ht)) (fun t ht => hdom t (hBT i ht)) hsmall hassign
      (fun t ht => hratio t (hBT i ht))
    refine ⟨P,hP.1,hP.2.1,hP.2.2.1,hP.2.2.2.1,?_⟩
    simpa only [c,w,div_mul_eq_mul_div] using hP.2.2.2.2
  let P : S → CapturedFamily H G X (6144/q) := fun i => Classical.choose (hex i)
  have hP := fun i => Classical.choose_spec (hex i)
  have hbound := CapturedFamily.scale_bound hq hk hX hconn hρ hρsmall hs hR hlog S P
    (fun i => (hP i).2.2.1)
    (by
      intro i
      apply (hP i).2.2.2.1.trans
      apply div_le_div_of_nonneg_right _ hs.le
      exact mul_le_mul_of_nonneg_right (by norm_num : (12:ℝ)≤24) (Real.rpow_nonneg (by norm_num) _))
    (fun i => (hP i).2.1)
    (by
      intro i j hij
      apply Finset.disjoint_left.mpr
      intro t hti htj
      have he := (hi i t ((hP i).1 hti)).symm.trans (hi j t ((hP j).1 htj))
      exact hij (Subtype.ext he))
  have hfiber : (∑i : S, ∑t ∈ B i, w t) = ∑t ∈ U, w t := by
    rw [sum_coe_sort S (fun i => ∑t ∈ U.filter (fun t => idx t=i), w t)]
    exact sum_fiberwise_of_maps_to (fun t ht => mem_image_of_mem idx ht) w
  have hsum : c*(∑t ∈ U, w t) ≤ ∑i : S, (P i).mass := by
    have hh := sum_le_sum (s := univ) (fun i (_ : i ∈ univ) => (hP i).2.2.2.2)
    rw [←mul_sum,hfiber] at hh
    exact hh
  have hgain := (mul_le_mul_of_nonneg_left hchoice hc).trans hsum
  have hq0 : 0 ≤ (q:ℝ)/8192 := by positivity
  have hh := (mul_le_mul_of_nonneg_left hgain hq0).trans hbound
  simpa only [mul_assoc] using hh
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Truncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uE2 uE3 uE4

section
open scoped Classical
open Matrix

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE} [DecidableEq E]

omit [DecidableEq E] in

lemma sum_sq_le_card_mul_sum_sq (S : Finset E) (a : E → ℝ) :
    (∑e ∈ S, a e)^2 ≤ (S.card : ℝ)*(∑e ∈ S, (a e)^2) := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) a

lemma two_truncations (S : Finset E) (a d : E → ℝ) {α : ℝ}
    (hα : 0 < α) (_hα1 : α ≤ 1) (hS : S.Nonempty)
    (ha : ∀e ∈ S, 0 ≤ a e) (hsq : ∀e ∈ S, (a e)^2 ≤ d e)
    (hpos : 0 < ∑e ∈ S, a e)
    (hbad : α*(S.card : ℝ)*(∑e ∈ S, d e) ≤ (∑e ∈ S, a e)^2) :
    let μ := (∑e ∈ S, a e)/(S.card : ℝ)
    ∃R : Finset E, R ⊆ S ∧
      (∑e ∈ S, a e)/2 ≤ ∑e ∈ R, a e ∧
      ∀e ∈ R, μ^2/16 ≤ (a e)^2 ∧ (a e)^2 ≤ d e ∧ d e ≤ 16*μ^2/α^2 := by
  let M : ℝ := S.card
  let A : ℝ := ∑e ∈ S, a e
  let μ := A/M
  have hM : 0 < M := by dsimp [M]; exact_mod_cast card_pos.mpr hS
  have hA : 0 < A := hpos
  have hμ : 0 < μ := div_pos hA hM
  have hμM : μ*M = A := div_mul_cancel₀ _ hM.ne'
  have hbad' : α*(∑e ∈ S, d e) ≤ M*μ^2 := by
    apply (mul_le_mul_iff_right₀ hM).mp
    change α*M*(∑e ∈ S, d e) ≤ A^2 at hbad
    nlinarith [sq_nonneg (μ*M-A)]
  let L := S.filter (fun e => a e < μ/4)
  let H := S.filter (fun e => 16*μ^2/α^2 < d e)
  let R := S\(L∪H)
  have hd : ∀e ∈ S, 0 ≤ d e := fun e he => (sq_nonneg _).trans (hsq e he)
  have hLsum : (∑e ∈ L, a e) ≤ A/4 := by
    calc
      _ ≤ ∑_e ∈ L, μ/4 := sum_le_sum (fun e he => (mem_filter.mp he).2.le)
      _ = (L.card : ℝ)*μ/4 := by simp; ring
      _ ≤ M*μ/4 := by
        have hh : (L.card : ℝ) ≤ M := by
          change (L.card : ℝ) ≤ (S.card : ℝ)
          exact_mod_cast card_le_card (show L ⊆ S from filter_subset _ _)
        nlinarith
      _ = A/4 := by rw [mul_comm M,hμM]
  have hHmass : (H.card : ℝ)*(16*μ^2/α^2) ≤ ∑e ∈ S, d e := by
    calc
      _ = ∑_e ∈ H, 16*μ^2/α^2 := by simp
      _ ≤ ∑e ∈ H, d e := sum_le_sum (fun e he => (mem_filter.mp he).2.le)
      _ ≤ ∑e ∈ S, d e := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hd e he)
  have hHcard : (H.card : ℝ) ≤ α*M/16 := by
    have hc := mul_le_mul_of_nonneg_left hHmass hα.le
    have hμ2 : 0 < μ^2 := sq_pos_of_pos hμ
    have heq : α*(H.card : ℝ)*(16*μ^2/α^2) = (H.card : ℝ)*16*μ^2/α := by field_simp
    have hh : (H.card : ℝ)*16*μ^2/α ≤ M*μ^2 := by
      calc
        _ = α*((H.card : ℝ)*(16*μ^2/α^2)) := by rw [←mul_assoc,heq]
        _ ≤ α*(∑e ∈ S, d e) := hc
        _ ≤ M*μ^2 := hbad'
    have hh' := (div_le_iff₀ hα).mp hh
    nlinarith
  have hHsq : (∑e ∈ H, a e)^2 ≤ (A/4)^2 := by
    have hcs := sum_sq_le_card_mul_sum_sq H a
    have hs : ∑e ∈ H, (a e)^2 ≤ ∑e ∈ S, d e :=
      (sum_le_sum (fun e he => hsq e (mem_filter.mp he).1)).trans
        (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun e he _ => hd e he))
    have hD0 : 0 ≤ ∑e ∈ S, d e := sum_nonneg hd
    have hh := mul_le_mul_of_nonneg_right hHcard hD0
    have hh' := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg H.card : (0:ℝ) ≤ _)
    have hb := mul_le_mul_of_nonneg_left hbad' hM.le
    linarith [sq_nonneg (μ*M-A)]
  have hHsum : (∑e ∈ H, a e) ≤ A/4 := by nlinarith [sum_nonneg (s := H) (fun e he => ha e (mem_filter.mp he).1)]
  have hU : L∪H ⊆ S := union_subset (filter_subset _ _) (filter_subset _ _)
  have hsum : ∑e ∈ S, a e = (∑e ∈ R, a e)+(∑e ∈ L∪H, a e) := (sum_sdiff hU).symm
  have hUH : ∑e ∈ L∪H, a e ≤ (∑e ∈ L, a e)+(∑e ∈ H, a e) := by
    have he := sum_union_inter (s₁ := L) (s₂ := H) (f := a)
    have hi : 0 ≤ ∑e ∈ L∩H, a e := sum_nonneg (fun e he => ha e (hU (mem_union_left _ (mem_inter.mp he).1)))
    linarith
  refine ⟨R,sdiff_subset,?_,?_⟩
  · change A/2 ≤ _
    change A = _ at hsum
    linarith
  · intro e he
    obtain ⟨heS,heU⟩ := mem_sdiff.mp he
    have hle : μ/4 ≤ a e := le_of_not_gt (fun hh => heU (mem_union_left _ (mem_filter.mpr ⟨heS,hh⟩)))
    have hde : d e ≤ 16*μ^2/α^2 := le_of_not_gt (fun hh => heU (mem_union_right _ (mem_filter.mpr ⟨heS,hh⟩)))
    exact ⟨by change μ^2/16 ≤ _; nlinarith [ha e heS],hsq e heS,hde⟩

end
end StrongThinTree.Truncation

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE2} [DecidableEq E]

lemma dyadic_interval {L x : ℝ} (hL : 0 < L) (hx : L ≤ x) :
    (2:ℝ)^(dyadicIndex L x : ℝ)*L ≤ x ∧
      x < 2*((2:ℝ)^(dyadicIndex L x : ℝ)*L) := by
  have hratio : 1 ≤ x/L := (le_div_iff₀ hL).mpr (by simpa)
  have hp : 0 < x/L := lt_of_lt_of_le zero_lt_one hratio
  have hg : 0 ≤ Real.logb 2 (x/L) := Real.logb_nonneg (by norm_num) hratio
  constructor
  · exact (le_div_iff₀ hL).mp ((Real.le_logb_iff_rpow_le (by norm_num) hp).mp (Nat.floor_le hg))
  · have hh := (Real.logb_lt_iff_lt_rpow (by norm_num) hp).mp (Nat.lt_floor_add_one (Real.logb 2 (x/L)))
    rw [Real.rpow_add (by norm_num),Real.rpow_one] at hh
    have hh' := (div_lt_iff₀ hL).mp hh
    dsimp [dyadicIndex]
    linarith

lemma dyadicIndex_lt {L U x : ℝ} {J : ℕ} (hL : 0 < L) (hx : L ≤ x) (hU : x ≤ U)
    (hJ : Real.logb 2 (U/L) < J) : dyadicIndex L x < J := by
  have hr : 1 ≤ x/L := (le_div_iff₀ hL).mpr (by simpa)
  apply (Nat.floor_lt (Real.logb_nonneg (by norm_num) hr)).mpr
  exact (Real.logb_le_logb_of_le (by norm_num) (lt_of_lt_of_le zero_lt_one hr)
    ((div_le_div_iff_of_pos_right hL).mpr hU)).trans_lt hJ

lemma same_dyadic_ratio {L x y : ℝ} (hL : 0 < L) (hx : L ≤ x) (hy : L ≤ y)
    (heq : dyadicIndex L x = dyadicIndex L y) : x < 2*y := by
  have hh := (dyadic_interval hL hx).2
  rw [heq] at hh
  exact hh.trans_le (mul_le_mul_of_nonneg_left (dyadic_interval hL hy).1 (by norm_num))

omit [DecidableEq E] in

lemma dyadic_pair (R : Finset E) (a b w : E → ℝ) {L U : ℝ} {J : ℕ}
    (hL : 0 < L) (hJ : 0 < J) (hj : Real.logb 2 (U/L) < J)
    (ha : ∀e ∈ R, L ≤ a e ∧ a e ≤ U) (hb : ∀e ∈ R, L ≤ b e ∧ b e ≤ U)
    (hpos : 0 < ∑e ∈ R, w e) :
    ∃B : Finset E, B.Nonempty ∧ B ⊆ R ∧
      (∑e ∈ R, w e)/(J:ℝ)^2 ≤ ∑e ∈ B, w e ∧
      ∀e ∈ B, ∀f ∈ B, a e < 2*a f ∧ b e < 2*b f := by
  let f := fun e => (dyadicIndex L (a e),dyadicIndex L (b e))
  let T := (range J)×ˢ(range J)
  have hT : T.Nonempty := ⟨(0,0),mem_product.mpr ⟨mem_range.mpr hJ,mem_range.mpr hJ⟩⟩
  have hf : ∀e ∈ R, f e ∈ T := by
    intro e he
    exact mem_product.mpr ⟨mem_range.mpr (dyadicIndex_lt hL (ha e he).1 (ha e he).2 hj),
      mem_range.mpr (dyadicIndex_lt hL (hb e he).1 (hb e he).2 hj)⟩
  have hJ0 : (0:ℝ) < J := by exact_mod_cast hJ
  obtain ⟨i,hi,hgain⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (w := w) hf hT
    (b := (∑e ∈ R, w e)/(J:ℝ)^2) (by
      have hh : (T.card : ℝ) = (J:ℝ)^2 := by simp [T,pow_two]
      rw [nsmul_eq_mul,hh,mul_div_cancel₀ _ (ne_of_gt (sq_pos_of_pos hJ0))])
  refine ⟨R.filter (fun e => f e=i),?_,filter_subset _ _,hgain,?_⟩
  · apply card_pos.mp
    by_contra hh
    have he : (R.filter (fun e => f e=i)) = ∅ := card_eq_zero.mp (by omega)
    rw [he,sum_empty] at hgain
    exact (not_le_of_gt (div_pos hpos (sq_pos_of_pos hJ0))) hgain
  · intro e he g hg
    obtain ⟨he,hfe⟩ := mem_filter.mp he
    obtain ⟨hg,hfg⟩ := mem_filter.mp hg
    have heq := hfe.trans hfg.symm
    exact ⟨same_dyadic_ratio hL (ha e he).1 (ha g hg).1 (congrArg Prod.fst heq),
      same_dyadic_ratio hL (hb e he).1 (hb g hg).1 (congrArg Prod.snd heq)⟩

end
end StrongThinTree.Truncation

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE3} [DecidableEq E]

lemma homogeneous_subset (S : Finset E) (a d : E → ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hS : S.Nonempty)
    (ha : ∀e ∈ S, 0 ≤ a e) (hsq : ∀e ∈ S, (a e)^2 ≤ d e)
    (hpos : 0 < ∑e ∈ S, a e)
    (hbad : α*(S.card : ℝ)*(∑e ∈ S, d e) ≤ (∑e ∈ S, a e)^2) :
    let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
    ∃B : Finset E, B.Nonempty ∧ B ⊆ S ∧
      (∑e ∈ S, a e)^2/(4*(J:ℝ)^4) ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 0 < (a e)^2) ∧
      ∀e ∈ B, ∀f ∈ B, (a e)^2 < 2*(a f)^2 ∧ d e < 2*d f := by
  let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
  let A := ∑e ∈ S, a e
  let μ := A/(S.card : ℝ)
  have hM : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  have hμ : 0 < μ := div_pos hpos hM
  obtain ⟨R,hRS,hRsum,hR⟩ := two_truncations S a d hα hα1 hS ha hsq hpos hbad
  have hRpos : 0 < ∑e ∈ R, a e := by linarith
  have hJ : 0 < J := by dsimp [J]; omega
  have hJr : (0:ℝ) < J := by exact_mod_cast hJ
  have hj : Real.logb 2 ((16*μ^2/α^2)/(μ^2/16)) < J := by
    have he : (16*μ^2/α^2)/(μ^2/16) = 256/α^2 := by field_simp; ring
    rw [he]
    have hh := Nat.le_ceil (Real.logb 2 (256/α^2))
    dsimp [J]
    push_cast
    linarith
  obtain ⟨B,hB,hBR,hgain,hratio⟩ := dyadic_pair R (fun e => (a e)^2) d a
    (show 0 < μ^2/16 by positivity) hJ hj
    (fun e he => ⟨(hR e he).1,(hR e he).2.1.trans (hR e he).2.2⟩)
    (fun e he => ⟨(hR e he).1.trans (hR e he).2.1,(hR e he).2.2⟩) hRpos
  refine ⟨B,hB,hBR.trans hRS,?_,?_,hratio⟩
  · change A^2/(4*(J:ℝ)^4) ≤ _
    have hbound : A/(2*(J:ℝ)^2) ≤ ∑e ∈ B, a e := by
      have hh := div_le_div_of_nonneg_right hRsum (sq_nonneg (J:ℝ))
      have he : (A/2)/(J:ℝ)^2 = A/(2*(J:ℝ)^2) := by ring
      change (A/2)/(J:ℝ)^2 ≤ _ at hh
      rw [he] at hh
      exact hh.trans hgain
    have hA : 0 < A := hpos
    have hnonneg : 0 ≤ A/(2*(J:ℝ)^2) := by positivity
    have hh := pow_le_pow_left₀ hnonneg hbound 2
    have he : (A/(2*(J:ℝ)^2))^2 = A^2/(4*(J:ℝ)^4) := by ring
    rw [he] at hh
    exact hh
  · intro e he
    exact lt_of_lt_of_le (by positivity : 0 < μ^2/16) (hR e (hBR he)).1

end
end StrongThinTree.Truncation

namespace StrongThinTree.Truncation
noncomputable section
open Finset
open scoped Classical
variable {E : Type uE4} [DecidableEq E]

lemma scaled_subset (O : Finset E) (a d : E → ℝ) {α : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hO : O.Nonempty)
    (ha : ∀e ∈ O, 0 ≤ a e) (hsq : ∀e ∈ O, (a e)^2 ≤ d e)
    (hpos : 0 < ∑e ∈ O, a e)
    (hbad : α*(O.card : ℝ)*(∑e ∈ O, d e) ≤ (∑e ∈ O, a e)^2)
    {L : ℕ} (hL : Real.logb 2 (16/(α*(1/(4*((1+⌈Real.logb 2 (256/α^2)⌉₊:ℕ):ℝ)^4))))+1 < L) :
    let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
    let γ := 1/(4*(J:ℝ)^4)
    ∃B : Finset E, ∃idx : ℤ, ∃off : Fin L,
      B.Nonempty ∧ B ⊆ O ∧ γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 2^(idx:ℝ) ≤ (a e)^2) ∧
      (∀e ∈ B, (a e)^2 ≤ 4*2^(idx:ℝ)) ∧
      (∀e ∈ B, 2^((idx:ℝ)+off.val) ≤ d e) ∧
      (∀e ∈ B, d e ≤ 4*2^((idx:ℝ)+off.val)) := by
  let J := 1+⌈Real.logb 2 (256/α^2)⌉₊
  let γ := 1/(4*(J:ℝ)^4)
  have hJ : (0:ℝ) < J := by dsimp [J]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  obtain ⟨B,hBn,hBO,hgain,hapos,hratio⟩ := homogeneous_subset O a d hα hα1 hO ha hsq hpos hbad
  obtain ⟨e₀,he₀,hmin₁⟩ := exists_min_image B (fun e => (a e)^2) hBn
  obtain ⟨f₀,hf₀,hmin₂⟩ := exists_min_image B d hBn
  let c₁ := (a e₀)^2
  let c₂ := d f₀
  have hc₁ : 0 < c₁ := hapos e₀ he₀
  have hc₁₂ : c₁ ≤ c₂ := (hmin₁ f₀ hf₀).trans (hsq f₀ (hBO hf₀))
  have hc₂ : 0 < c₂ := hc₁.trans_le hc₁₂
  have hdom : γ*(∑e ∈ O, a e)^2 ≤ (∑e ∈ B, a e)^2 := by
    simpa only [γ,one_div,inv_mul_eq_div] using hgain
  have hmax₁ : ∀e ∈ B, (a e)^2 ≤ 4*c₁ := by
    intro e he
    have hh := (hratio e he e₀ he₀).1.le
    dsimp [c₁]
    linarith only [hh,sq_nonneg (a e₀)]
  have hmin₂' : ∀e ∈ B, c₂/4 ≤ d e := by
    intro e he
    have hh : c₂ ≤ d e := hmin₂ e he
    linarith only [hh,hc₂]
  have hden := BagDensity.local_density O B a d hBO hBn hα hγ
    (fun e he => (sq_nonneg (a e)).trans (hsq e he)) hmax₁ hmin₂' hbad hdom
  have hcard : (B.card:ℝ) ≤ O.card := by exact_mod_cast card_le_card hBO
  have hOpos : (0:ℝ) < O.card := by exact_mod_cast card_pos.mpr hO
  have hscale : c₂ ≤ (16/(α*γ))*c₁ := by
    have hm := mul_le_mul_of_nonneg_left hcard (show 0 ≤ 16*c₁ by positivity)
    have hh : α*γ*c₂ ≤ 16*c₁ := by
      apply (mul_le_mul_iff_right₀ hOpos).mp
      linarith only [hden,hm]
    calc
      c₂ ≤ 16*c₁/(α*γ) := (le_div_iff₀ (mul_pos hα hγ)).mpr (by linarith only [hh])
      _ = (16/(α*γ))*c₁ := by ring
  let i := ⌊Real.logb 2 c₁⌋
  let j := ⌊Real.logb 2 c₂⌋
  have hoff := ScaleSelection.integer_scale_offset hc₁ hc₁₂ hscale hL
  let o : Fin L := ⟨(j-i).toNat, by dsimp [i,j] at *; omega⟩
  have hj : ((j:ℤ):ℝ)=(i:ℝ)+(o.val:ℝ) := by
    have hh : (o.val:ℤ)=j-i := Int.toNat_of_nonneg hoff.1
    have hh' := congrArg (fun x : ℤ => (x:ℝ)) hh
    push_cast at hh'
    linarith only [hh']
  have hi := ScaleSelection.integer_dyadic hc₁
  have hj' := ScaleSelection.integer_dyadic hc₂
  refine ⟨B,i,o,hBn,hBO,hdom,?_,?_,?_,?_⟩
  · intro e he
    exact hi.1.trans (hmin₁ e he)
  · intro e he
    have hh := (hratio e he e₀ he₀).1
    have hh' : (a e)^2 < 2*c₁ := hh
    have hhi : c₁ < 2*2^(i:ℝ) := hi.2
    linarith only [hh',hhi]
  · intro e he
    rw [←hj]
    exact hj'.1.trans (hmin₂ e he)
  · intro e he
    rw [←hj]
    have hh := (hratio e he f₀ hf₀).2
    have hh' : d e < 2*c₂ := hh
    have hjj : c₂ < 2*2^(j:ℝ) := hj'.2
    linarith only [hh',hjj]
end
end StrongThinTree.Truncation

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell
open scoped Classical
variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma truncationGain_pos (α : ℝ) : 0 < truncationGain α := by
  dsimp [truncationGain,truncationBins]
  positivity

lemma diagonal_sq_le (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v)) (e : Fin m) :
    ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ l1dist (X (G.left e)) (X (G.right e)) := by
  have hh := pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (Y (G.left e)-Y (G.right e)) e) 2
  have he : ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ ‖Y (G.left e)-Y (G.right e)‖^2 := by
    simpa only [Real.norm_eq_abs,sq_abs] using hh
  exact he.trans (hcontract _ _)

lemma positive_bad_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, binary (X v))
    (hconn : H.LocallyConnectedReal G q)
    (T : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hpos : ∀t ∈ T, 0 < ∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)
    (hbad : ∀t ∈ T, α*((H.parentBoundary G t).card : ℝ)*
      (∑e ∈ H.parentBoundary G t, l1dist (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ T, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    let γ := truncationGain α
    let s := α*γ/32
    let N := ∑t ∈ T, (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((H.parentBoundary G t).card : ℝ)
    ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*(γ*N/(L:ℝ)) ≤
      2*R*(∑e : Fin m, l1dist (X (G.left e)) (X (G.right e))) := by
  let γ := truncationGain α
  let s := α*γ/32
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => l1dist (X (G.left e)) (X (G.right e))
  let O := H.parentBoundary G
  have hγ : 0 < γ := truncationGain_pos α
  have hs : 0 < s := by dsimp [s]; positivity
  have hex : ∀t : Finset (Fin n), ∃B : Finset (Fin m), ∃i : ℤ, ∃o : Fin L,
      t ∈ T → B.Nonempty ∧ B ⊆ O t ∧ γ*(∑e ∈ O t, a e)^2 ≤ (∑e ∈ B, a e)^2 ∧
      (∀e ∈ B, 2^(i:ℝ) ≤ (a e)^2) ∧
      (∀e ∈ B, (a e)^2 ≤ 4*2^(i:ℝ)) ∧
      (∀e ∈ B, 2^((i:ℝ)+o.val) ≤ d e) ∧
      (∀e ∈ B, d e ≤ 4*2^((i:ℝ)+o.val)) := by
    intro t
    by_cases ht : t ∈ T
    · have hOn : (O t).Nonempty := by
        by_contra hh
        have heq : O t=∅ := not_nonempty_iff_eq_empty.mp hh
        have hp := hpos t ht
        change 0 < ∑e ∈ O t, a e at hp
        simp only [heq,sum_empty,lt_self_iff_false] at hp
      obtain ⟨B,i,o,hB⟩ := Truncation.scaled_subset (O t) a d hα hα1 hOn
        (fun e _ => hpositive e) (fun e _ => diagonal_sq_le Y hcontract e) (hpos t ht) (hbad t ht) hlogL
      exact ⟨B,i,o,fun _ => hB⟩
    · exact ⟨∅,0,⟨0,hL⟩,fun hh => (ht hh).elim⟩
  choose F idx off hf using hex
  have hh := homogeneous_scale_bound hq hL hR hk hX hconn T F idx off Y hT hroot
    (fun t ht => (hf t ht).2.1) (fun t ht => (hf t ht).1) hα hγ he he1 hρ hρsmall
    hcontract hpositive (fun t ht => (hf t ht).2.2.2.1)
    (fun t ht => (hf t ht).2.2.2.2.1) (fun t ht => (hf t ht).2.2.2.2.2.1)
    (fun t ht => (hf t ht).2.2.2.2.2.2) hbad (fun t ht => (hf t ht).2.2.1)
    hsmall hassign hratio hlogR
  have hsum : γ*(∑t ∈ T, (∑e ∈ O t, a e)^2/((O t).card:ℝ)) ≤
      ∑t ∈ T, (∑e ∈ F t, a e)^2/((O t).card:ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro t ht
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_right (hf t ht).2.2.1 (Nat.cast_nonneg _)
  have hgain := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg L : (0:ℝ)≤L)
  have hc : 0 ≤ ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2))) := by positivity
  exact (mul_le_mul_of_nonneg_left hgain hc).trans hh
lemma weighted_boundary_sum (M : Finset (Finset (Fin n)))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    (d : Fin m → ℝ) (hd : ∀e, 0 ≤ d e) :
    (∑t ∈ M, ∑e ∈ H.parentBoundary G t, d e) ≤ 2*∑e, d e := by
  have heq : (∑t ∈ M, ∑e ∈ H.parentBoundary G t, d e) =
      ∑e, ((M.filter (fun t => e ∈ H.parentBoundary G t)).card : ℝ)*d e := by
    calc
      _ = ∑t ∈ M, ∑e : Fin m, if e ∈ H.parentBoundary G t then d e else 0 := by
        apply sum_congr rfl
        intro t ht
        rw [←sum_filter]
        simp
      _ = ∑e : Fin m, ∑t ∈ M, if e ∈ H.parentBoundary G t then d e else 0 := sum_comm
      _ = _ := by
        apply sum_congr rfl
        intro e he
        rw [←sum_filter, sum_const,nsmul_eq_mul]
  rw [heq,mul_sum]
  apply sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_right _ (hd e)
  exact_mod_cast H.parentBoundary_multiplicity G M hM hroot e

lemma hierarchy_numerator_bound {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hX : ∀v, binary (X v))
    (hconn : H.LocallyConnectedReal G q)
    (M : Finset (Finset (Fin n))) (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R) :
    let γ := truncationGain α
    let s := α*γ/32
    (∑t ∈ M, (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((H.parentBoundary G t).card : ℝ)) ≤
      (2*α+2*(R:ℝ)*(L:ℝ)/(((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*γ))*
        (∑e : Fin m, l1dist (X (G.left e)) (X (G.right e))) := by
  let O := H.parentBoundary G
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => l1dist (X (G.left e)) (X (G.right e))
  let N : Finset (Fin n) → ℝ := fun t => (∑e ∈ O t, a e)^2/((O t).card:ℝ)
  let T := M.filter (fun t => 0 < ∑e ∈ O t, a e ∧
    α*((O t).card:ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2)
  have hTM : T ⊆ M := filter_subset _ _
  have hgood : ∀t ∈ M\T, N t ≤ α*∑e ∈ O t, d e := by
    intro t ht
    have htM := (mem_sdiff.mp ht).1
    have htT := (mem_sdiff.mp ht).2
    have hd : 0 ≤ α*∑e ∈ O t, d e := mul_nonneg hα.le (sum_nonneg (fun e _ => l1dist_nonneg _ _))
    by_cases hp : 0 < ∑e ∈ O t, a e
    · have hn : ¬α*((O t).card:ℝ)*(∑e ∈ O t, d e) ≤ (∑e ∈ O t, a e)^2 := by
        intro hh; exact htT (mem_filter.mpr ⟨htM,hp,hh⟩)
      have hc : 0 < ((O t).card:ℝ) := by
        by_contra h
        have hz : (O t).card=0 := by exact_mod_cast le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
        have hz' : O t=∅ := card_eq_zero.mp hz
        simp [hz'] at hp
      apply (div_le_iff₀ hc).mpr
      linarith only [lt_of_not_ge hn]
    · have hz : ∑e ∈ O t, a e=0 := le_antisymm (le_of_not_gt hp) (sum_nonneg (fun e _ => hpositive e))
      simpa [N,hz] using hd
  have hg : (∑t ∈ M\T, N t) ≤ 2*α*∑e, d e := by
    calc
      (∑t ∈ M\T, N t) ≤ ∑t ∈ M\T, α*∑e ∈ O t, d e := sum_le_sum hgood
      _ = α*∑t ∈ M\T, ∑e ∈ O t, d e := (mul_sum _ _ _).symm
      _ ≤ α*(2*∑e, d e) := mul_le_mul_of_nonneg_left
        (weighted_boundary_sum (M\T) (fun _ ht => hM (mem_sdiff.mp ht).1)
          (fun t ht => hroot t (mem_sdiff.mp ht).1) d (fun _ => l1dist_nonneg _ _)) hα.le
      _ = 2*α*∑e, d e := by ring
  have hb := positive_bad_bound hq hL hR hk hX hconn T Y (hTM.trans hM)
    (fun t ht => hroot t (hTM ht)) hα hα1 he he1 hρ hρsmall hcontract hpositive
    (fun t ht => (mem_filter.mp ht).2.1) (fun t ht => (mem_filter.mp ht).2.2)
    hsmall hassign (fun t ht => hratio t (hTM ht)) hlogL hlogR
  let γ := truncationGain α
  let s := α*γ/32
  let c := ((q:ℝ)/8192)*(s^ε/(6912*(1024/ε^2)))*γ
  have hγ : 0 < γ := truncationGain_pos α
  have hs : 0 < s := by dsimp [s]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hL' : 0 < (L:ℝ) := Nat.cast_pos.mpr hL
  have hb' : (∑t ∈ T, N t) ≤ (2*(R:ℝ)*(L:ℝ)/c)*(∑e, d e) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    have hh := (div_le_iff₀ hL').mp (show c*(∑t ∈ T, N t)/L ≤ 2*(R:ℝ)*∑e, d e by
      convert hb using 1 ; dsimp [c,N,γ,s,O,a,d] ; ring)
    linarith only [hh]
  change (∑t ∈ M, N t) ≤ (2*α+2*(R:ℝ)*(L:ℝ)/c)*(∑e, d e)
  rw [←sum_sdiff hTM]
  linarith only [hg,hb']
end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Duality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV uI2 uI3 uV2 uW uJ2 uV3 uE2 uT uJ3 uH uI4

section

namespace StrongThinTree.Polar
noncomputable section
open Matrix Finset
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV2} {W : Type uW} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [DecidableEq W] in
lemma norm_sq_mulVec_le {U : Matrix W V ℝ} (hU : Uᵀ*U ≤ 1) (x : V → ℝ) :
    (U *ᵥ x) ⬝ᵥ (U *ᵥ x) ≤ x ⬝ᵥ x := by
  have hp := (Matrix.le_iff.mp hU).dotProduct_mulVec_nonneg x
  simp only [star_trivial,sub_mulVec,one_mulVec,dotProduct_sub] at hp
  have heq : x ⬝ᵥ ((Uᵀ*U) *ᵥ x)=(U *ᵥ x) ⬝ᵥ (U *ᵥ x) := by
    rw [←mulVec_mulVec,dotProduct_mulVec,vecMul_transpose]
  rw [heq] at hp
  linarith only [hp]

end
end StrongThinTree.Polar

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ShortcutDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

lemma eval_incidence (x : Fin n → ℝ) (e : Fin m) :
    (∑v, x v*G.incidence e v)=x (G.left e)-x (G.right e) := by
  simp [incidence,point,Pi.sub_apply,mul_sub,sum_sub_distrib,Pi.single_apply,mul_ite]

lemma binary_matrix_energy (X : Matrix (Fin h) (Fin n) ℝ)
    (hX : ∀i v, X i v=0 ∨ X i v=1) :
    (∑e, ∑i, (X*Matrix.of (fun v e => G.incidence e v)) i e ^2)=
      ∑e, l1dist (fun i => X i (G.left e)) (fun i => X i (G.right e)) := by
  apply sum_congr rfl
  intro e _
  unfold l1dist
  apply sum_congr rfl
  intro i _
  change (∑v, X i v*G.incidence e v)^2 = |X i (G.left e)-X i (G.right e)|
  rw [G.eval_incidence]
  rcases hX i (G.left e) with hl | hl <;> rcases hX i (G.right e) with hr | hr <;>
    simp [hl,hr]

lemma contraction_embedding (X : Matrix (Fin h) (Fin n) ℝ)
    (hX : ∀i v, X i v=0 ∨ X i v=1) (U : Matrix (Fin m) (Fin h) ℝ)
    (hU : Uᵀ*U ≤ 1) :
    let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
    ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (fun i => X i u) (fun i => X i v) := by
  dsimp
  intro u v
  have hh := Polar.norm_sq_mulVec_le hU (fun i => X i u-X i v)
  have heq : (WithLp.toLp 2 (U *ᵥ (fun i => X i u)) : EuclideanSpace ℝ (Fin m)) -
      WithLp.toLp 2 (U *ᵥ (fun i => X i v)) =
      WithLp.toLp 2 (U *ᵥ (fun i => X i u-X i v)) := by
    rw [show (fun i => X i u-X i v)=(fun i => X i u)-(fun i => X i v) from rfl,mulVec_sub]
    rfl
  rw [heq,EuclideanSpace.norm_sq_eq]
  have hdist : (fun i => X i u-X i v) ⬝ᵥ (fun i => X i u-X i v)=
      l1dist (fun i => X i u) (fun i => X i v) := by
    unfold dotProduct l1dist
    apply sum_congr rfl
    intro i _
    rcases hX i u with hu | hu <;> rcases hX i v with hv | hv <;> simp [hu,hv]
  rw [←hdist]
  simpa only [dotProduct,PiLp.toLp_apply,Real.norm_eq_abs,←pow_two,sq_abs] using hh

lemma contraction_edge_diag (X : Matrix (Fin h) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin h) ℝ) (e : Fin m) :
    let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
    (Y (G.left e)-Y (G.right e)).ofLp e =
      (U*(X*Matrix.of (fun v e => G.incidence e v))) e e := by
  change (∑i, U e i*X i (G.left e))-(∑i, U e i*X i (G.right e)) = _
  change (∑i, U e i*X i (G.left e))-(∑i, U e i*X i (G.right e)) =
    ∑i, U e i*(∑v, X i v*G.incidence e v)
  simp_rw [G.eval_incidence,mul_sub]
  rw [sum_sub_distrib]

namespace Hierarchy
variable {G : MultiGraph n m} {H : Hierarchy n}

lemma binary_numerator_bound_oai {q L R : ℕ} (hq : 0 < q) (hL : 0 < L) (hR : 0 < R)
    (hk : G.EdgeConnected q) (hconn : H.LocallyConnectedReal G q)
    (M : Finset (Finset (Fin n))) (hM : M ⊆ H.nodes) (hroot : ∀t ∈ M, t ≠ univ)
    {α ε ρ : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (he : 0 < ε) (he1 : ε < 1/3)
    (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (hsmall : (α*truncationGain α/32)^ε ≤ 1/(1728*(1024/ε^2)))
    (hassign : (6144:ℝ)/q ≤ (α*truncationGain α/32)^(1+2*ε))
    (hratio : ∀t ∈ M, (q:ℝ)*ρ*((G.cut univ t).card : ℝ) ≤ (H.parentBoundary G t).card)
    (hlogL : Real.logb 2 (16/(α*truncationGain α))+1 < L)
    (hlogR : Real.logb 2 (24/(ρ*(α*truncationGain α/32)^2)) < R)
    (X : Matrix (Fin h) (Fin n) ℝ) (hX : ∀i v, X i v=0 ∨ X i v=1)
    (U : Matrix (Fin m) (Fin h) ℝ) (hU : Uᵀ*U ≤ 1)
    (hpositive : ∀e, 0 ≤ (U*(X*Matrix.of (fun v e => G.incidence e v))) e e) :
    (∑t : M, (∑e ∈ H.parentBoundary G t, (U*(X*Matrix.of (fun v e => G.incidence e v))) e e)^2/
      ((H.parentBoundary G t).card : ℝ)) ≤
      shortcutCoefficient q L R α ε*(∑e, ∑i, (X*Matrix.of (fun v e => G.incidence e v)) i e ^2) := by
  let Y : Fin n → EuclideanSpace ℝ (Fin m) := fun v => WithLp.toLp 2 (U *ᵥ (fun i => X i v))
  have hh := hierarchy_numerator_bound hq hL hR hk (fun v i => hX i v) hconn M Y hM hroot
    hα hα1 he he1 hρ hρsmall (contraction_embedding X hX U hU)
    (fun e => by simpa only [Y,G.contraction_edge_diag] using hpositive e)
    hsmall hassign hratio hlogL hlogR
  rw [sum_coe_sort M (fun t => (∑e ∈ H.parentBoundary G t,
    (U*(X*Matrix.of (fun v e => G.incidence e v))) e e)^2/((H.parentBoundary G t).card:ℝ)),
    G.binary_matrix_energy X hX]
  simpa only [Y,G.contraction_edge_diag,shortcutCoefficient] using hh

end Hierarchy
end
end StrongThinTree.MultiGraph

end

end OAI
end

theorem solution : type_of% @OAI.StrongThinTree.MultiGraph.Hierarchy.binary_numerator_bound_oai := @OAI.StrongThinTree.MultiGraph.Hierarchy.binary_numerator_bound_oai
