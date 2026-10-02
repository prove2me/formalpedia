-- Prove2me | solution 1 for MooreFoelner.isMarginal_not_extended_Rf
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T07:01:16.176245+00:00
-- url     : https://prove2.me/submissions/4b33d3ed-8ab6-4c95-87ee-f2a722124a4f

import Theorems.Thm_MooreFoelner_bijOn_Lf_Rf_and_diagramMul
import Definitions.Def_CannonFloydParry
import Definitions.Def_MooreFoelner
import Definitions.Def_MooreTrees
import Definitions.Def_ThompsonAmenability
import Mathlib

section
namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

section
/-!
# Moore 2013, group GenTrees: #7, #17, #18, #27
-/

namespace MooreFoelner.Dev.GenTrees

open Classical MooreFoelner CannonFloydParry
open scoped symmDiff

section Folner

variable {G : Type*} [Group G]

end Folner

section Seqs

/-- The infinite sequence `s⁀y`. -/
def appS (s : Seq) (y : ℕ → Bool) : ℕ → Bool :=
  fun n => if h : n < s.length then s.get ⟨n, h⟩ else y (n - s.length)

/-- `x` with its first `k` digits removed. -/
def shift (x : ℕ → Bool) (k : ℕ) : ℕ → Bool := fun n => x (n + k)

lemma isInitialPart_appS (s : Seq) (y : ℕ → Bool) : IsInitialPart s (appS s y) := by
  intro i h; simp [appS, h]

lemma appS_shift {s : Seq} {x : ℕ → Bool} (h : IsInitialPart s x) :
    appS s (shift x s.length) = x := by
  funext n; unfold appS shift
  split_ifs with hn
  · exact h n hn
  · congr 1; omega

lemma shift_appS (s : Seq) (y : ℕ → Bool) : shift (appS s y) s.length = y := by
  funext n; simp [appS, shift]

lemma appS_append (r w : Seq) (y : ℕ → Bool) : appS (r ++ w) y = appS r (appS w y) := by
  funext n; unfold appS
  by_cases h1 : n < r.length
  · have h2 : n < (r ++ w).length := by simp; omega
    simp only [h1, h2, dif_pos, List.get_eq_getElem, List.getElem_append_left h1]
  · by_cases h2 : n < (r ++ w).length
    · have h3 : n - r.length < w.length := by simp at h2; omega
      simp only [h1, h2, h3, dif_pos, dif_neg, not_false_eq_true, List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
    · have h3 : ¬ n - r.length < w.length := by simp at h2; omega
      simp only [h1, h2, h3, dif_neg, not_false_eq_true]
      congr 1; simp; omega

@[simp] lemma appS_nil (y : ℕ → Bool) : appS [] y = y := by funext n; simp [appS]

@[simp] lemma shift_zero (x : ℕ → Bool) : shift x 0 = x := by funext n; simp [shift]

lemma isInitialPart_of_prefix {a b : Seq} {x : ℕ → Bool} (hab : a <+: b)
    (hb : IsInitialPart b x) : IsInitialPart a x := by
  intro i hi
  obtain ⟨c, rfl⟩ := hab
  have := hb i (by simp; omega)
  simpa [List.getElem_append_left hi] using this

lemma isInitialPart_comparable {a b : Seq} {x : ℕ → Bool} (ha : IsInitialPart a x)
    (hb : IsInitialPart b x) : a <+: b ∨ b <+: a := by
  have key : ∀ a b : Seq, IsInitialPart a x → IsInitialPart b x → a.length ≤ b.length →
      a <+: b := by
    intro a b ha hb hle
    rw [List.prefix_iff_eq_take]
    apply List.ext_getElem (by simp; omega)
    intro n h1 h2
    have := ha n h1
    have := hb n (by omega)
    simp_all
  rcases le_total a.length b.length with h | h
  · exact Or.inl (key a b ha hb h)
  · exact Or.inr (key b a hb ha h)

end Seqs

section Trees

lemma tree_prefix_eq {T : Finset Seq} (hT : IsTree T) {a b : Seq} (ha : a ∈ T) (hb : b ∈ T)
    (hab : a <+: b) : a = b := by
  obtain ⟨t, _, huniq⟩ := hT (appS b fun _ => false)
  have hb' := huniq b ⟨hb, isInitialPart_appS _ _⟩
  have ha' := huniq a ⟨ha, isInitialPart_of_prefix hab (isInitialPart_appS _ _)⟩
  rw [ha', hb']

lemma tree_comparable_eq {T : Finset Seq} (hT : IsTree T) {a b : Seq} (ha : a ∈ T) (hb : b ∈ T)
    (hab : a <+: b ∨ b <+: a) : a = b := by
  rcases hab with h | h
  · exact tree_prefix_eq hT ha hb h
  · exact (tree_prefix_eq hT hb ha h).symm

lemma tree_exists_initialPart {T : Finset Seq} (hT : IsTree T) (x : ℕ → Bool) :
    ∃ t ∈ T, IsInitialPart t x := by
  obtain ⟨t, ⟨ht, hx⟩, _⟩ := hT x
  exact ⟨t, ht, hx⟩

lemma tree_exists_comparable {T : Finset Seq} (hT : IsTree T) (u : Seq) :
    ∃ t ∈ T, t <+: u ∨ u <+: t := by
  obtain ⟨t, ht, hx⟩ := tree_exists_initialPart hT (appS u fun _ => false)
  exact ⟨t, ht, isInitialPart_comparable hx (isInitialPart_appS _ _)⟩

end Trees

section Sorted

lemma mem_sorted {T : Finset Seq} {a : Seq} : a ∈ sorted T ↔ a ∈ T := by
  unfold sorted; simp [List.mem_mergeSort]

lemma length_sorted (T : Finset Seq) : (sorted T).length = T.card := by
  unfold sorted; simp

lemma nodup_sorted (T : Finset Seq) : (sorted T).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList T)

lemma get_mem_sorted (T : Finset Seq) (i : Fin (sorted T).length) : (sorted T).get i ∈ T :=
  mem_sorted.mp (List.get_mem _ _)

lemma exists_index_of_mem {T : Finset Seq} {a : Seq} (ha : a ∈ T) :
    ∃ i : Fin (sorted T).length, (sorted T).get i = a :=
  List.get_of_mem (mem_sorted.mpr ha)

lemma sorted_index_unique {T : Finset Seq} {i j : Fin (sorted T).length}
    (h : (sorted T).get i = (sorted T).get j) : i = j :=
  (nodup_sorted T).get_inj_iff.mp h

end Sorted

section DiagramMap

lemma find_finRange_eq {n : ℕ} (p : Fin n → Bool) (i : Fin n) (hi : p i = true)
    (huniq : ∀ j, p j = true → j = i) : (List.finRange n).find? p = some i := by
  cases h : (List.finRange n).find? p with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd hi (by simpa using h i (List.mem_finRange i))
  | some j =>
    have := List.find?_some h
    rw [huniq j this]

lemma diagramMap_eq {L R : Finset Seq} (hL : IsTree L)
    (x : ℕ → Bool) (i : ℕ) (hiL : i < (sorted L).length) (hiR : i < (sorted R).length)
    (hx : IsInitialPart ((sorted L).get ⟨i, hiL⟩) x) :
    diagramMap L R x = appS ((sorted R).get ⟨i, hiR⟩) (shift x ((sorted L).get ⟨i, hiL⟩).length) := by
  unfold diagramMap
  simp only
  rw [find_finRange_eq _ ⟨i, hiL⟩ (by simpa using hx)]
  · simp only [List.getElem?_eq_getElem hiR]
    funext n
    simp [appS, shift]
  · intro j hj
    have hj' : IsInitialPart ((sorted L).get j) x := by simpa using hj
    exact sorted_index_unique (tree_comparable_eq hL (get_mem_sorted L _) (get_mem_sorted L _)
      (isInitialPart_comparable hj' hx))

lemma exists_index_initialPart {L : Finset Seq} (hL : IsTree L) (x : ℕ → Bool) :
    ∃ i : Fin (sorted L).length, IsInitialPart ((sorted L).get i) x := by
  obtain ⟨t, ht, hx⟩ := tree_exists_initialPart hL x
  obtain ⟨i, rfl⟩ := exists_index_of_mem ht
  exact ⟨i, hx⟩

end DiagramMap

section DiagramAct

end DiagramAct

section Five

/-- The reduced diagram of `f`. -/
noncomputable def DD (f : MooreF) : Finset Seq × Finset Seq := (Lf (toMap f), Rf (toMap f))

lemma reduced_DD (f : MooreF) : IsReducedDiagram (Lf (toMap f)) (Rf (toMap f)) :=
  (bijOn_Lf_Rf_and_diagramMul).2.2.2.2.2.1.mapsTo (Set.mem_univ f)

lemma isTree_Lf (f : MooreF) : IsTree (Lf (toMap f)) := (reduced_DD f).1.1
lemma isTree_Rf (f : MooreF) : IsTree (Rf (toMap f)) := (reduced_DD f).1.2.1
lemma card_Lf_Rf (f : MooreF) : (Lf (toMap f)).card = (Rf (toMap f)).card := (reduced_DD f).1.2.2

lemma describes_DD (f : MooreF) : Describes (Lf (toMap f)) (Rf (toMap f)) (toMap f) :=
  (bijOn_Lf_Rf_and_diagramMul).2.2.2.2.2.2.1 f

lemma DD_mul (f g : MooreF) : DD (f * g) = diagramMul (DD f) (DD g) :=
  (bijOn_Lf_Rf_and_diagramMul).2.2.2.2.2.2.2 f g

lemma reduced_DD' (f : MooreF) : IsReducedDiagram (DD f).1 (DD f).2 := reduced_DD f

lemma DD_one : DD 1 = (trivialTree, trivialTree) := by
  obtain ⟨_, hassoc, htriv, hid, hinv, _⟩ := bijOn_Lf_Rf_and_diagramMul
  set E := DD 1
  have hE : IsReducedDiagram E.1 E.2 := reduced_DD' 1
  have h1 : diagramMul E E = E := by rw [← DD_mul, mul_one]
  have hEi := hinv E hE
  have h2 : diagramMul (diagramMul E E) (E.2, E.1) = diagramMul E (diagramMul E (E.2, E.1)) :=
    hassoc E E (E.2, E.1) hE hE hEi.1
  rw [h1, hEi.2.1, (hid E hE).2] at h2
  exact h2.symm

lemma Lf_one : Lf (toMap 1) = trivialTree := congrArg Prod.fst DD_one
lemma Rf_one : Rf (toMap 1) = trivialTree := congrArg Prod.snd DD_one

/-- The map of `f` on infinite sequences. -/
noncomputable def phi (f : MooreF) (x : ℕ → Bool) : ℕ → Bool :=
  diagramMap (Lf (toMap f)) (Rf (toMap f)) x

lemma phi_mul (f g : MooreF) (x : ℕ → Bool) : phi (f * g) x = phi g (phi f x) := by
  have h := ((bijOn_Lf_Rf_and_diagramMul).1 (DD f) (DD g) (reduced_DD' f) (reduced_DD' g)).2 x
  rw [← DD_mul] at h
  exact h

lemma sorted_trivialTree : sorted trivialTree = [[]] := by
  unfold sorted trivialTree
  rw [Finset.toList_singleton, List.mergeSort_singleton]

lemma phi_one (x : ℕ → Bool) : phi 1 x = x := by
  unfold phi
  rw [Lf_one, Rf_one]
  have hT : IsTree trivialTree := by
    intro y
    refine ⟨[], ⟨by simp [trivialTree], fun i h => by simp at h⟩, ?_⟩
    rintro t ⟨ht, _⟩
    simpa [trivialTree] using ht
  have h0 : 0 < (sorted trivialTree).length := by rw [sorted_trivialTree]; simp
  rw [diagramMap_eq hT x 0 h0 h0 (by intro i h; simp [sorted_trivialTree] at h)]
  simp [sorted_trivialTree]

lemma phi_inv_phi (f : MooreF) (x : ℕ → Bool) : phi f⁻¹ (phi f x) = x := by
  rw [← phi_mul, mul_inv_cancel, phi_one]

lemma phi_injective (f : MooreF) : Function.Injective (phi f) := fun x y h => by
  rw [← phi_inv_phi f x, h, phi_inv_phi]

end Five

section PartialAction

end PartialAction

section StrictSort

variable {α : Type*}

end StrictSort

section SortedOrder

end SortedOrder

section Val

/-- The `n`th term of the binary expansion. -/
noncomputable def term (x : ℕ → Bool) (n : ℕ) : ℝ := if x n then (1/2 : ℝ) ^ (n + 1) else 0

lemma term_nonneg (x : ℕ → Bool) (n : ℕ) : 0 ≤ term x n := by
  unfold term; split_ifs <;> positivity

lemma term_le (x : ℕ → Bool) (n : ℕ) : term x n ≤ (1/2 : ℝ) ^ (n + 1) := by
  unfold term; split_ifs <;> [exact le_rfl; positivity]

lemma summable_geom : Summable (fun n : ℕ => (1/2 : ℝ) ^ (n + 1)) := by
  simp_rw [pow_succ]
  exact (summable_geometric_two).mul_right _

lemma tsum_geom : ∑' n : ℕ, (1/2 : ℝ) ^ (n + 1) = 1 := by
  simp_rw [pow_succ]
  rw [tsum_mul_right, tsum_geometric_two]; norm_num

lemma summable_term (x : ℕ → Bool) : Summable (term x) :=
  Summable.of_nonneg_of_le (term_nonneg x) (term_le x) summable_geom

/-- The real number `0.x₀x₁x₂…`. -/
noncomputable def val (x : ℕ → Bool) : ℝ := ∑' n, term x n

lemma val_nonneg (x : ℕ → Bool) : 0 ≤ val x := tsum_nonneg (term_nonneg x)

lemma val_le_one (x : ℕ → Bool) : val x ≤ 1 := by
  rw [← tsum_geom]
  exact Summable.tsum_le_tsum (term_le x) (summable_term x) summable_geom

lemma term_shift (x : ℕ → Bool) (k n : ℕ) :
    term x (n + k) = (1/2 : ℝ) ^ k * term (shift x k) n := by
  unfold term shift
  split_ifs <;> [ring; ring]

lemma val_split (x : ℕ → Bool) (k : ℕ) :
    val x = ∑ n ∈ Finset.range k, term x n + (1/2 : ℝ) ^ k * val (shift x k) := by
  unfold val
  rw [← (summable_term x).sum_add_tsum_nat_add k]
  congr 1
  simp_rw [term_shift x k]
  rw [tsum_mul_left]

lemma sum_term_appS (s : Seq) (y : ℕ → Bool) :
    ∑ n ∈ Finset.range s.length, term (appS s y) n = seqVal s := by
  unfold seqVal
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp [term, appS, i.2]

lemma val_appS (s : Seq) (y : ℕ → Bool) :
    val (appS s y) = seqVal s + (1/2 : ℝ) ^ s.length * val y := by
  rw [val_split _ s.length, sum_term_appS, shift_appS]

lemma val_of_initialPart {s : Seq} {x : ℕ → Bool} (h : IsInitialPart s x) :
    val x = seqVal s + (1/2 : ℝ) ^ s.length * val (shift x s.length) := by
  conv_lhs => rw [← appS_shift h]
  exact val_appS _ _

lemma val_eq_one {y : ℕ → Bool} (h : val y = 1) (n : ℕ) : y n = true := by
  by_contra hn
  simp only [Bool.not_eq_true] at hn
  have hs : Summable (fun m => (1/2 : ℝ) ^ (m + 1) - term y m) := summable_geom.sub (summable_term y)
  have h1 : ∑' m, ((1/2 : ℝ) ^ (m + 1) - term y m) = 0 := by
    rw [summable_geom.tsum_sub (summable_term y), tsum_geom]; unfold val at h; linarith
  have h2 : (1/2 : ℝ) ^ (n + 1) - term y n ≤ ∑' m, ((1/2 : ℝ) ^ (m + 1) - term y m) :=
    hs.le_tsum n (fun j _ => by linarith [term_le y j])
  have h3 : term y n = 0 := by simp [term, hn]
  rw [h3, h1] at h2
  have : (0 : ℝ) < (1/2) ^ (n + 1) := by positivity
  linarith

lemma val_eq_zero {y : ℕ → Bool} (h : val y = 0) (n : ℕ) : y n = false := by
  by_contra hn
  simp only [Bool.not_eq_false] at hn
  have h2 : term y n ≤ val y := (summable_term y).le_tsum n (fun j _ => term_nonneg y j)
  have h3 : term y n = (1/2 : ℝ) ^ (n + 1) := by simp [term, hn]
  have : (0 : ℝ) < (1/2) ^ (n + 1) := by positivity
  linarith

lemma eq_of_val_eq {a b : ℕ → Bool} (hv : val a = val b) (hne : a ≠ b) :
    ∃ p c, (∀ n, p < n → a n = c) ∧ (∀ n, p < n → b n = !c) := by
  have hex : ∃ n, a n ≠ b n := by
    by_contra h; push Not at h; exact hne (funext h)
  set p := Nat.find hex with hpdef
  have hp : a p ≠ b p := Nat.find_spec hex
  have hlt : ∀ n < p, a n = b n := fun n hn => not_not.mp (Nat.find_min hex hn)
  have hS : ∑ n ∈ Finset.range p, term a n = ∑ n ∈ Finset.range p, term b n :=
    Finset.sum_congr rfl (fun n hn => by unfold term; rw [hlt n (Finset.mem_range.mp hn)])
  have ha := val_split a (p + 1)
  have hb := val_split b (p + 1)
  rw [Finset.sum_range_succ] at ha hb
  have hpos : (0 : ℝ) < (1/2) ^ (p + 1) := by positivity
  have va0 := val_nonneg (shift a (p + 1))
  have va1 := val_le_one (shift a (p + 1))
  have vb0 := val_nonneg (shift b (p + 1))
  have vb1 := val_le_one (shift b (p + 1))
  have hsh : ∀ (x : ℕ → Bool) (n : ℕ), p < n → x n = shift x (p + 1) (n - (p + 1)) := by
    intro x n hn; unfold shift; congr 1; omega
  rcases hap : a p <;> rcases hbp : b p
  · exact absurd (hap.trans hbp.symm) hp
  · -- a p = false, b p = true
    have hta : term a p = 0 := by simp [term, hap]
    have htb : term b p = (1/2) ^ (p + 1) := by simp [term, hbp]
    rw [hta] at ha; rw [htb] at hb
    have e1 : val (shift a (p + 1)) = 1 := by nlinarith
    have e2 : val (shift b (p + 1)) = 0 := by nlinarith
    exact ⟨p, true, fun n hn => by rw [hsh a n hn]; exact val_eq_one e1 _,
      fun n hn => by rw [hsh b n hn]; exact val_eq_zero e2 _⟩
  · have hta : term a p = (1/2) ^ (p + 1) := by simp [term, hap]
    have htb : term b p = 0 := by simp [term, hbp]
    rw [hta] at ha; rw [htb] at hb
    have e1 : val (shift a (p + 1)) = 0 := by nlinarith
    have e2 : val (shift b (p + 1)) = 1 := by nlinarith
    exact ⟨p, false, fun n hn => by rw [hsh a n hn]; exact val_eq_zero e1 _,
      fun n hn => by rw [hsh b n hn]; exact val_eq_one e2 _⟩
  · exact absurd (hap.trans hbp.symm) hp

/-- `0.x₀x₁…` as a point of `[0,1]`. -/
noncomputable def valUI (x : ℕ → Bool) : UI := ⟨val x, val_nonneg x, val_le_one x⟩

lemma describes_val {L R : Finset Seq} {h : UI ≃o UI} (hD : Describes L R h) (x : ℕ → Bool) :
    (h (valUI x) : ℝ) = val (diagramMap L R x) := by
  obtain ⟨⟨i, hiL⟩, hx⟩ := exists_index_initialPart hD.1.1 x
  have hiR : i < (sorted R).length := by
    rw [length_sorted, ← hD.1.2.2, ← length_sorted]; exact hiL
  rw [diagramMap_eq hD.1.1 x i hiL hiR hx, val_appS]
  have hv := val_of_initialPart hx
  set s := (sorted L).get ⟨i, hiL⟩
  set t := (sorted R).get ⟨i, hiR⟩
  have v0 := val_nonneg (shift x s.length)
  have v1 := val_le_one (shift x s.length)
  have hp : (0 : ℝ) < (1/2) ^ s.length := by positivity
  have h1 : seqVal s ≤ (valUI x : ℝ) := by
    show seqVal s ≤ val x
    rw [hv]; nlinarith
  have h2 : (valUI x : ℝ) ≤ seqVal s + (1/2 : ℝ) ^ s.length := by
    show val x ≤ _
    rw [hv]; nlinarith
  rw [hD.2 i hiL hiR (valUI x) h1 h2]
  have e : (valUI x : ℝ) - seqVal s = (1/2 : ℝ) ^ s.length * val (shift x s.length) := by
    show val x - _ = _
    rw [hv]; ring
  rw [e, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]
  congr 1
  rw [one_div_pow, one_div_pow]
  field_simp
  ring

end Val

section Concrete

@[simp] lemma seqVal_nil : seqVal [] = 0 := by simp [seqVal]

@[simp] lemma seqVal_cons (b : Bool) (s : Seq) :
    seqVal (b :: s) = (if b then 1/2 else 0) + (1/2) * seqVal s := by
  unfold seqVal
  change (∑ i : Fin (s.length + 1), _) = _
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i _
    simp only [List.length_cons, Fin.val_succ, List.get_eq_getElem, List.getElem_cons_succ]
    split_ifs <;> ring

end Concrete

section GMap

/-! ### The element `g_u`: `x₀` acting inside the dyadic interval of `u` -/

noncomputable def g4 (a l : ℝ) : ℝ → ℝ := fun y => if y ≤ a + l then (y + a + l) / 2 else y
noncomputable def g3 (a l : ℝ) : ℝ → ℝ := fun y => if y ≤ a + l / 2 then y + l / 4 else g4 a l y
noncomputable def g2 (a l : ℝ) : ℝ → ℝ := fun y => if y ≤ a + l / 4 then 2 * y - a else g3 a l y
noncomputable def gFun (a l : ℝ) : ℝ → ℝ := fun y => if y ≤ a then y else g2 a l y

lemma strictMono_gFun {a l : ℝ} (hl : 0 < l) : StrictMono (gFun a l) := by
  have h4 : StrictMono (g4 a l) :=
    strictMono_glue (c := a + l) (fun x _ y _ h => by linarith) (fun x _ y _ h => h)
      (by ring)
  have h3 : StrictMono (g3 a l) :=
    strictMono_glue (c := a + l / 2) (fun x _ y _ h => by linarith) (fun x _ y _ h => h4 h)
      (by unfold g4; rw [if_pos (by linarith)]; ring)
  have h2 : StrictMono (g2 a l) :=
    strictMono_glue (c := a + l / 4) (fun x _ y _ h => by linarith) (fun x _ y _ h => h3 h)
      (by unfold g3; rw [if_pos (by linarith)]; ring)
  exact strictMono_glue (c := a) (fun x _ y _ h => h) (fun x _ y _ h => h2 h)
    (by unfold g2; rw [if_pos (by linarith)]; ring)

noncomputable def gInv (a l : ℝ) : ℝ → ℝ := fun z =>
  if z ≤ a then z
  else if z ≤ a + l / 2 then (z + a) / 2
  else if z ≤ a + 3 * l / 4 then z - l / 4
  else if z ≤ a + l then 2 * z - a - l
  else z

lemma gFun_gInv {a l : ℝ} (hl : 0 < l) (z : ℝ) : gFun a l (gInv a l z) = z := by
  unfold gFun g2 g3 g4 gInv
  split_ifs <;> linarith

lemma gFun_of_le {a l y : ℝ} (_hl : 0 < l) (h : y ≤ a) : gFun a l y = y := by
  unfold gFun; rw [if_pos h]

lemma gFun_of_mem1 {a l y : ℝ} (_hl : 0 < l) (h0 : a ≤ y) (h1 : y ≤ a + l / 4) :
    gFun a l y = 2 * y - a := by
  unfold gFun g2 g3 g4; split_ifs <;> linarith

lemma gFun_of_mem2 {a l y : ℝ} (hl : 0 < l) (h0 : a + l / 4 ≤ y) (h1 : y ≤ a + l / 2) :
    gFun a l y = y + l / 4 := by
  unfold gFun g2 g3 g4; split_ifs <;> linarith

lemma gFun_of_mem3 {a l y : ℝ} (hl : 0 < l) (h0 : a + l / 2 ≤ y) (h1 : y ≤ a + l) :
    gFun a l y = (y + a + l) / 2 := by
  unfold gFun g2 g3 g4; split_ifs <;> linarith

lemma gFun_of_ge {a l y : ℝ} (hl : 0 < l) (h : a + l ≤ y) : gFun a l y = y := by
  unfold gFun g2 g3 g4; split_ifs <;> linarith

noncomputable def lineG (a l : ℝ) (hl : 0 < l) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (gFun a l) (strictMono_gFun hl) (fun z => ⟨gInv a l z, gFun_gInv hl z⟩)

/-- `g` as an order isomorphism of `[0,1]`. -/
noncomputable def gUI (a l : ℝ) (hl : 0 < l) (ha : 0 ≤ a) (hal : a + l ≤ 1) : UI ≃o UI :=
  CannonFloydParry.restrict (lineG a l hl) (fun x hx => gFun_of_le hl (by linarith))
    (fun x hx => gFun_of_ge hl (by linarith))

lemma gUI_apply {a l : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hal : a + l ≤ 1) (z : UI) :
    (gUI a l hl ha hal z : ℝ) = gFun a l z := rfl

lemma isDyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x + y) := by
  obtain ⟨m, k, rfl⟩ := hx
  obtain ⟨m', k', rfl⟩ := hy
  refine ⟨m * 2 ^ k' + m' * 2 ^ k, k + k', ?_⟩
  push_cast
  field_simp
  ring

lemma isDyadic_half_pow (n : ℕ) : IsDyadic ((1/2 : ℝ) ^ n) :=
  ⟨1, n, by rw [one_div_pow]; push_cast; ring⟩

lemma isDyadic_seqVal (u : Seq) : IsDyadic (seqVal u) := by
  induction u with
  | nil => exact ⟨0, 0, by simp⟩
  | cons b s ih =>
    rw [seqVal_cons]
    obtain ⟨m, k, hm⟩ := ih
    refine isDyadic_add ?_ ⟨m, k + 1, by rw [hm, pow_succ]; field_simp⟩
    split_ifs
    · exact ⟨1, 1, by norm_num⟩
    · exact ⟨0, 0, by norm_num⟩

lemma isThompson_gUI {a l : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hal : a + l ≤ 1)
    (hda : IsDyadic a) (hdl : ∀ n : ℕ, IsDyadic (l / 2 ^ n)) : IsThompson (gUI a l hl ha hal) := by
  refine ⟨{a, a + l / 4, a + l / 2, a + l}, ?_, ?_⟩
  · intro b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact hda
    · exact isDyadic_add hda (by have := hdl 2; norm_num at this; exact this)
    · exact isDyadic_add hda (by have := hdl 1; norm_num at this; exact this)
    · exact isDyadic_add hda (by have := hdl 0; norm_num at this; exact this)
  · intro x y hxy hB
    have hnot : ∀ b ∈ ({a, a + l / 4, a + l / 2, a + l} : Finset ℝ), b ≤ (x : ℝ) ∨ (y : ℝ) ≤ b := by
      intro b hb
      by_contra h
      push Not at h
      have : b ∈ Set.Ioo (x : ℝ) (y : ℝ) ∩ (({a, a + l / 4, a + l / 2, a + l} : Finset ℝ) : Set ℝ) :=
        ⟨⟨h.1, h.2⟩, hb⟩
      rw [hB] at this; exact this
    have b1 := hnot a (by simp)
    have b2 := hnot (a + l / 4) (by simp)
    have b3 := hnot (a + l / 2) (by simp)
    have b4 := hnot (a + l) (by simp)
    simp only [gUI_apply]
    rcases b1 with b1 | b1
    · rcases b2 with b2 | b2
      · rcases b3 with b3 | b3
        · rcases b4 with b4 | b4
          · exact ⟨0, 0, fun z hz => by rw [gFun_of_ge hl (by linarith [hz.1])]; simp⟩
          · exact ⟨-1, (a + l) / 2, fun z hz => by
              rw [gFun_of_mem3 hl (by linarith [hz.1]) (by linarith [hz.2])]
              rw [zpow_neg, zpow_one]; ring⟩
        · exact ⟨0, l / 4, fun z hz => by
            rw [gFun_of_mem2 hl (by linarith [hz.1]) (by linarith [hz.2])]; simp⟩
      · exact ⟨1, -a, fun z hz => by
          rw [gFun_of_mem1 hl (by linarith [hz.1]) (by linarith [hz.2])]; simp; ring⟩
    · exact ⟨0, 0, fun z hz => by rw [gFun_of_le hl (by linarith [hz.2])]; simp⟩

lemma seqVal_add_le_one (u : Seq) : seqVal u + (1/2 : ℝ) ^ u.length ≤ 1 := by
  have h := val_appS u (fun _ => true)
  have h1 : val (fun _ => true) = 1 := by unfold val term; simp only [if_true]; exact tsum_geom
  rw [h1, mul_one] at h
  rw [← h]; exact val_le_one _

lemma seqVal_nonneg (u : Seq) : 0 ≤ seqVal u := by
  have h := val_appS u (fun _ => false)
  have h1 : val (fun _ => false) = 0 := by unfold val term; simp
  rw [h1, mul_zero, add_zero] at h
  rw [← h]; exact val_nonneg _

/-- `g_u`: the identity off the dyadic interval of `u`, and a copy of `x₀` on it. -/
noncomputable def gU (u : Seq) : MooreF :=
  MulOpposite.op ⟨gUI (seqVal u) ((1/2 : ℝ) ^ u.length) (by positivity) (seqVal_nonneg u)
    (seqVal_add_le_one u),
    mem_F_of_isThompson (isThompson_gUI _ _ _ (isDyadic_seqVal u) (fun n => by
      have : (1/2 : ℝ) ^ u.length / 2 ^ n = (1/2) ^ (u.length + n) := by
        rw [pow_add, one_div_pow (2:ℝ) n, mul_one_div]
      rw [this]; exact isDyadic_half_pow _))⟩

lemma toMap_gU_apply (u : Seq) (z : UI) :
    (toMap (gU u) z : ℝ) = gFun (seqVal u) ((1/2 : ℝ) ^ u.length) z := rfl

end GMap

section Concrete2

end Concrete2

section WordLength

end WordLength

section LocalX0

/-- `0^∞`. -/
def zero : ℕ → Bool := fun _ => false

lemma val_zero : val zero = 0 := by unfold val term zero; simp

lemma val_appS_zero (s : Seq) : val (appS s zero) = seqVal s := by
  rw [val_appS, val_zero]; ring

lemma seqVal_append (s t : Seq) : seqVal (s ++ t) = seqVal s + (1/2 : ℝ) ^ s.length * seqVal t := by
  rw [← val_appS_zero, appS_append, val_appS, val_appS_zero]

lemma seqVal_zs (j : ℕ) : seqVal (List.replicate j false ++ [true]) = (1/2 : ℝ) ^ (j + 1) := by
  induction j with
  | zero => simp
  | succ j ih => rw [List.replicate_succ, List.cons_append, seqVal_cons, ih]; simp; ring

lemma seqVal_os (j : ℕ) : seqVal (List.replicate j true) = 1 - (1/2 : ℝ) ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [List.replicate_succ, seqVal_cons, ih]; simp; ring

/-- An infinite sequence is eventually `0`. -/
def EvZero (x : ℕ → Bool) : Prop := ∃ N, ∀ n, N ≤ n → x n = false

lemma evZero_appS_zero (s : Seq) : EvZero (appS s zero) :=
  ⟨s.length, fun n hn => by simp [appS, zero, show ¬ n < s.length by omega]⟩

lemma evZero_phi (f : MooreF) {x : ℕ → Bool} (hx : EvZero x) : EvZero (phi f x) := by
  obtain ⟨N, hN⟩ := hx
  obtain ⟨⟨i, hiL⟩, hxi⟩ := exists_index_initialPart (isTree_Lf f) x
  have hiR : i < (sorted (Rf (toMap f))).length := by
    rw [length_sorted, ← card_Lf_Rf, ← length_sorted]; exact hiL
  unfold phi
  rw [diagramMap_eq (isTree_Lf f) x i hiL hiR hxi]
  refine ⟨N + ((sorted (Rf (toMap f))).get ⟨i, hiR⟩).length, fun n hn => ?_⟩
  simp only [appS, shift]
  rw [dif_neg (by omega)]
  exact hN _ (by omega)

lemma phi_eq_of_val {f : MooreF} {x y : ℕ → Bool} (hx : EvZero x) (hy : EvZero y)
    (h : (toMap f (valUI x) : ℝ) = val y) : phi f x = y := by
  by_contra hne
  have hv : val (phi f x) = val y := by rw [← h]; exact (describes_val (describes_DD f) x).symm
  obtain ⟨p, c, h1, h2⟩ := eq_of_val_eq hv hne
  obtain ⟨N, hN⟩ := evZero_phi f hx
  obtain ⟨M, hM⟩ := hy
  have e1 := h1 (p + N + M + 1) (by omega)
  have e2 := h2 (p + N + M + 1) (by omega)
  rw [hN _ (by omega)] at e1
  rw [hM _ (by omega)] at e2
  subst e1; simp at e2

/-- `u⁀0^j⁀1⁀0^∞`. -/
def zs (u : Seq) (j : ℕ) : ℕ → Bool := appS (u ++ (List.replicate j false ++ [true])) zero
/-- `u⁀1^j⁀0^∞`. -/
def os (u : Seq) (j : ℕ) : ℕ → Bool := appS (u ++ List.replicate j true) zero

lemma phi_gU_zs (u : Seq) (j : ℕ) (hj : 1 ≤ j) : phi (gU u) (zs u (j + 1)) = zs u j := by
  apply phi_eq_of_val (evZero_appS_zero _) (evZero_appS_zero _)
  rw [toMap_gU_apply]
  show gFun _ _ (val (zs u (j + 1))) = _
  unfold zs
  rw [val_appS_zero, val_appS_zero, seqVal_append u, seqVal_append u, seqVal_zs, seqVal_zs]
  have hp : (0 : ℝ) < (1/2) ^ u.length := by positivity
  have hq : (1/2 : ℝ) ^ (j + 1 + 1) ≤ 1/4 := by
    calc (1/2 : ℝ) ^ (j + 1 + 1) ≤ (1/2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1/4 := by norm_num
  have hq0 : (0 : ℝ) ≤ (1/2) ^ (j + 1 + 1) := by positivity
  rw [gFun_of_mem1 hp (by nlinarith) (by nlinarith)]
  rw [pow_succ (1/2 : ℝ) (j + 1)]; ring

lemma phi_gU_os (u : Seq) (j : ℕ) (hj : 1 ≤ j) : phi (gU u) (os u j) = os u (j + 1) := by
  apply phi_eq_of_val (evZero_appS_zero _) (evZero_appS_zero _)
  rw [toMap_gU_apply]
  show gFun _ _ (val (os u j)) = _
  unfold os
  rw [val_appS_zero, val_appS_zero, seqVal_append u, seqVal_append u, seqVal_os, seqVal_os]
  have hp : (0 : ℝ) < (1/2) ^ u.length := by positivity
  have hq : (1/2 : ℝ) ^ j ≤ 1/2 := by
    calc (1/2 : ℝ) ^ j ≤ (1/2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
      _ = 1/2 := by norm_num
  have hq0 : (0 : ℝ) ≤ (1/2) ^ j := by positivity
  rw [gFun_of_mem3 hp (by nlinarith) (by nlinarith)]
  rw [pow_succ (1/2 : ℝ) j]; ring

lemma phi_gU_pow_zs (u : Seq) (k m : ℕ) (hm : 1 ≤ m) :
    phi (gU u ^ k) (zs u (m + k)) = zs u m := by
  induction k generalizing m with
  | zero => simp [phi_one]
  | succ k ih =>
    rw [pow_succ, phi_mul, show m + (k + 1) = (m + 1) + k by omega, ih (m + 1) (by omega),
      phi_gU_zs u m hm]

lemma phi_gU_pow_os (u : Seq) (k m : ℕ) (hm : 1 ≤ m) :
    phi (gU u ^ k) (os u m) = os u (m + k) := by
  induction k with
  | zero => simp [phi_one]
  | succ k ih =>
    rw [pow_succ, phi_mul, ih, phi_gU_os u (m + k) (by omega)]; rfl

lemma exists_phi_appS {f : MooreF} {u : Seq} (h : ∃ r ∈ Rf (toMap f), r <+: u) :
    ∃ c, ∀ y, phi f (appS c y) = appS u y := by
  obtain ⟨r, hr, w, rfl⟩ := h
  obtain ⟨⟨i, hiR⟩, rfl⟩ := exists_index_of_mem hr
  have hiL : i < (sorted (Lf (toMap f))).length := by
    rw [length_sorted, card_Lf_Rf, ← length_sorted]; exact hiR
  refine ⟨(sorted (Lf (toMap f))).get ⟨i, hiL⟩ ++ w, fun y => ?_⟩
  unfold phi
  rw [diagramMap_eq (isTree_Lf f) _ i hiL hiR
    (isInitialPart_of_prefix (List.prefix_append _ _) (isInitialPart_appS _ _)),
    appS_append, shift_appS, appS_append]

lemma length_eq_of_appS_zero_eq {v₁ v₂ : Seq} (h : appS v₁ zero = appS v₂ zero)
    (h₁ : v₁.getLast? = some true) (h₂ : v₂.getLast? = some true) : v₁.length = v₂.length := by
  have key : ∀ v : Seq, v.getLast? = some true →
      0 < v.length ∧ appS v zero (v.length - 1) = true ∧
        ∀ n, v.length - 1 < n → appS v zero n = false := by
    intro v hv
    have hpos : 0 < v.length := by
      rcases v with _ | ⟨b, v⟩
      · simp at hv
      · simp
    refine ⟨hpos, ?_, fun n hn => ?_⟩
    · simp only [appS, show v.length - 1 < v.length by omega, dif_pos, List.get_eq_getElem]
      rw [List.getLast?_eq_getElem?] at hv
      rw [List.getElem?_eq_getElem (by omega)] at hv
      exact Option.some.inj hv
    · simp [appS, zero, show ¬ n < v.length by omega]
  obtain ⟨p1, t1, f1⟩ := key v₁ h₁
  obtain ⟨p2, t2, f2⟩ := key v₂ h₂
  rw [h] at t1 f1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := f1 (v₂.length - 1) (by omega); rw [t2] at this; simp at this
  · have := f2 (v₁.length - 1) (by omega); rw [t1] at this; simp at this

lemma exists_prefix_of_notMem {R : Finset Seq} (hR : IsTree R) {u : Seq}
    (h : ¬ ∃ r ∈ R, u <+: r) : ∃ r ∈ R, r <+: u := by
  obtain ⟨t, ht, h1 | h1⟩ := tree_exists_comparable hR u
  · exact ⟨t, ht, h1⟩
  · exact absurd ⟨t, ht, h1⟩ h

lemma not_mem_E_of_mem_E (u : Seq) (f : MooreF) (k : ℕ) (hk : 0 < k)
    (hf : ∃ r ∈ Rf (toMap f), r <+: u) (hfk : ∃ r ∈ Rf (toMap (f * gU u ^ k)), r <+: u) : False := by
  obtain ⟨c, hc⟩ := exists_phi_appS hf
  obtain ⟨c', hc'⟩ := exists_phi_appS hfk
  have inj := phi_injective (f * gU u ^ k)
  -- the zeros family
  have e1 : appS c (appS (List.replicate (1 + k) false ++ [true]) zero) =
      appS c' (appS (List.replicate 1 false ++ [true]) zero) := by
    apply inj
    rw [hc', phi_mul, hc]
    have := phi_gU_pow_zs u k 1 le_rfl
    unfold zs at this; rw [appS_append u, appS_append u] at this
    rw [this]
  -- the ones family
  have e2 : appS c (appS (List.replicate 1 true) zero) =
      appS c' (appS (List.replicate (1 + k) true) zero) := by
    apply inj
    rw [hc', phi_mul, hc]
    have := phi_gU_pow_os u k 1 le_rfl
    unfold os at this; rw [appS_append u, appS_append u] at this
    rw [this]
  rw [← appS_append, ← appS_append] at e1 e2
  have l1 := length_eq_of_appS_zero_eq e1 (by simp) (by simp)
  have l2 := length_eq_of_appS_zero_eq e2 (by simp [List.getLast?_append, List.replicate_succ])
    (by rw [List.getLast?_append]; simp [List.getLast?_replicate])
  simp at l1 l2
  omega

end LocalX0

section Lemma41

lemma isMarginal_of_marginalizes {G S : Type*} [Group G] (act : S → G → Option S) (E : Set S)
    (g : G) (h : Marginalizes act g E ∅) : IsMarginal act E := by
  refine ⟨1, ?_⟩
  have := IsKMarginal.succ (l := 1) (fun _ => E) (fun _ => ∅) (fun _ => g)
    (fun _ => IsKMarginal.zero) (fun _ => h)
  rwa [Set.iUnion_const] at this

theorem isMarginal_not_extended_Rf' (u : Seq) :
    IsMarginal (rightMul : MooreF → MooreF → Option MooreF)
      {f | ¬ ∃ r ∈ Rf (toMap f), u <+: r} := by
  apply isMarginal_of_marginalizes _ _ (gU u)
  intro f hf k hk ⟨y, hy, hfy⟩
  exfalso
  simp only [actPow, rightMul, Option.some.injEq] at hfy
  subst hfy
  exact not_mem_E_of_mem_E u f k hk (exists_prefix_of_notMem (isTree_Rf f) hf)
    (exists_prefix_of_notMem (isTree_Rf _) hy)

end Lemma41

section Lemma42


end Lemma42

end MooreFoelner.Dev.GenTrees

namespace MooreFoelner

open Classical CannonFloydParry

end MooreFoelner
end

open MooreFoelner in
open Classical MooreFoelner CannonFloydParry in
open scoped symmDiff in
open Classical CannonFloydParry in
theorem solution (u : Seq) :
    IsMarginal (rightMul : MooreF → MooreF → Option MooreF)
      {f | ¬ ∃ r ∈ Rf (toMap f), u <+: r} :=
  Dev.GenTrees.isMarginal_not_extended_Rf' u
