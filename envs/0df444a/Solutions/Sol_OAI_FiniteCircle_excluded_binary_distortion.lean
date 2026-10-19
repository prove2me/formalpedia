-- Prove2me | solution 1 for OAI.FiniteCircle.excluded_binary_distortion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T16:08:26.628961+00:00
-- url     : https://prove2.me/submissions/1a05c5b7-7dae-4261-b9c6-a4e436dabef6

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/BinaryDistortion.lean:L144-L183
-- (upload_full_project.md Phase 4): solution for node OAI.FiniteCircle.excluded_binary_distortion. The node keeps its source
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
import Theorems.Thm_OAI_FiniteCircle_coded_range_lower
import Theorems.Thm_OAI_FiniteCircle_editDistance_ofFn_le_hamming
import Theorems.Thm_OAI_FiniteCircle_excluded_character_branching
import Theorems.Thm_OAI_FiniteCircle_excluded_long_deficit
import Theorems.Thm_OAI_FiniteCircle_halfHamming_eq
import Theorems.Thm_OAI_FiniteCircle_halfHamming_fin
import Theorems.Thm_OAI_FiniteCircle_residue_representative
import Theorems.Thm_OAI_FiniteCircle_tree_cheap_ed

-- ---- from OAI.Combinatorics.FiniteCircle.Edit ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace EditStep
variable {α β : Type*} {x y : List α}

theorem append_left (h : EditStep x y) (u : List α) : EditStep (u ++ x) (u ++ y) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc] using EditStep.insert (u ++ p) q a
  | delete p q a => simpa only [List.append_assoc] using EditStep.delete (u ++ p) q a
  | substitute p q a b =>
    simpa only [List.append_assoc] using EditStep.substitute (u ++ p) q a b

theorem append_right (h : EditStep x y) (v : List α) : EditStep (x ++ v) (y ++ v) := by
  cases h with
  | insert p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.insert p (q ++ v) a
  | delete p q a => simpa only [List.append_assoc, List.cons_append] using EditStep.delete p (q ++ v) a
  | substitute p q a b =>
    simpa only [List.append_assoc, List.cons_append] using EditStep.substitute p (q ++ v) a b

theorem map (h : EditStep x y) (f : α → β) : EditStep (x.map f) (y.map f) := by
  cases h with
  | insert u v a => simpa using EditStep.insert (u.map f) (v.map f) (f a)
  | delete u v a => simpa using EditStep.delete (u.map f) (v.map f) (f a)
  | substitute u v a b => simpa using EditStep.substitute (u.map f) (v.map f) (f a) (f b)
end EditStep

namespace EditScript
variable {α β : Type*} {n m : ℕ} {x y z : List α}

theorem append_left (h : EditScript n x y) (u : List α) : EditScript n (u ++ x) (u ++ y) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_left u) ih

theorem append_right (h : EditScript n x y) (v : List α) : EditScript n (x ++ v) (y ++ v) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.append_right v) ih

theorem map (h : EditScript n x y) (f : α → β) : EditScript n (x.map f) (y.map f) := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.map f) ih

end EditScript

theorem editDistance_map_le {α β : Type*} (f : α → β) (x y : List α) :
    editDistance (x.map f) (y.map f) ≤ editDistance x y :=
  editDistance_le_of_script ((editDistance_spec x y).map f)

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.ExcludedSeparation ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

 theorem excludedPhaseHom_natCast (m : ℕ) (p : ℕ → ℕ → ℕ) (M l a : ℕ)
    (hd : ∀ k : Fin m, p l k ∣ M) (hn : ∀ k : Fin m, 0 < p l k) :
    excludedPhaseHom m p M l hd (fun k => (a : ZMod (p l k))) =
      excludedTranslation m p M l a := by
  ext i
  change (∑ j ∈ Finset.univ.erase i, subcircle (hd j) (a : ZMod (p l j))) = _
  unfold excludedTranslation
  apply Finset.sum_congr rfl
  intro j _
  let : NeZero (p l j) := ⟨(hn j).ne'⟩
  rw [subcircle_val, ZMod.val_natCast]

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Primes ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List

namespace StandingPrimes
variable {h : ℕ} {p : ℕ → ℕ → ℕ} (hp : StandingPrimes h p)
include hp

 theorem atLevel (l : ℕ) (hl : 1 ≤ l) (hlh : l ≤ h) (k : Fin h) :
    Nat.Prime (p l k) ∧ h^3 < p l k ∧ p l k ≤ 2*h^3 := by
  have ht := hp.inside ⟨l-1,by omega⟩ k
  simpa only [show l-1+1=l by omega] using ht

 theorem positive (l : ℕ) (k : Fin h) : 0 < p l k := by
  by_cases hl : 1 ≤ l ∧ l ≤ h
  · exact (hp.atLevel l hl.1 hl.2 k).1.pos
  · rw [hp.outside l k (by omega)]
    norm_num

 theorem level_injective (l : ℕ) (hl : 1 ≤ l) (hlh : l ≤ h) :
    Function.Injective (fun k : Fin h => p l k) := by
  intro i j he
  have hi := hp.inj (a₁ := (⟨l-1,by omega⟩,i)) (a₂ := (⟨l-1,by omega⟩,j))
    (by simpa only [show l-1+1=l by omega] using he)
  exact congrArg Prod.snd hi

 theorem coprime (l : ℕ) : Pairwise (fun i j : Fin h => Nat.Coprime (p l i) (p l j)) := by
  intro i j hij
  by_cases hl : 1 ≤ l ∧ l ≤ h
  · exact ((hp.atLevel l hl.1 hl.2 i).1.coprime_iff_not_dvd).mpr (by
      intro hd
      have he := ((hp.atLevel l hl.1 hl.2 j).1.dvd_iff_eq (hp.atLevel l hl.1 hl.2 i).1.ne_one).mp hd
      exact hij (hp.level_injective l hl.1 hl.2 he.symm))
  · rw [hp.outside l i (by omega), hp.outside l j (by omega)]
    exact Nat.coprime_one_left _

 theorem period_pos (l : ℕ) : 0 < period h p l :=
  Finset.prod_pos (fun k _ => hp.positive l k)

 theorem circle_pos : 0 < circleSize h p := by
  apply Nat.mul_pos (by norm_num)
  exact Finset.prod_pos (fun l _ => hp.period_pos (l.val+1))

 omit hp in
 theorem circle_even : circleSize h p = 2*(circleSize h p/2) := by
  unfold circleSize
  omega

 theorem divides_circle (l : ℕ) (k : Fin h) : p l k ∣ circleSize h p := by
  by_cases hl : 1 ≤ l ∧ l ≤ h
  · have hk : p l k ∣ period h p l := Finset.dvd_prod_of_mem _ (Finset.mem_univ k)
    have hd : period h p l ∣ ∏ r : Fin h, period h p (r.val+1) := by
      have hh := Finset.dvd_prod_of_mem (fun r : Fin h => period h p (r.val+1))
        (Finset.mem_univ (⟨l-1,by omega⟩ : Fin h))
      simpa only [show l-1+1=l by omega] using hh
    exact hk.trans (hd.trans (dvd_mul_left _ _))
  · rw [hp.outside l k (by omega)]
    exact one_dvd _

end StandingPrimes

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.TreeBranching ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem flatExcludedState_shift (m M l : ℕ)
    (v : TreeLeaf (fun _ => Fin m) l → ZMod M) (θ : ZMod M) :
    flatExcludedState m M l (fun i => v i+θ) = shiftExcludedState m M l (flatExcludedState m M l v) θ := by
  induction l with
  | zero => rfl
  | succ l ih =>
    funext j
    exact ih (fun i => v (j,i))

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Translations ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem editDistance_append_le {α : Type*} (x y x' y' : List α) :
    editDistance (x++y) (x'++y') ≤ editDistance x x' + editDistance y y' := by
  apply editDistance_le_of_script
  exact ((editDistance_spec x x').append_right y).trans ((editDistance_spec y y').append_left x')

 theorem editDistance_flatMap_le {α β : Type*} (xs : List α) (f g : α → List β) :
    editDistance (xs.flatMap f) (xs.flatMap g) ≤ (xs.map (fun a => editDistance (f a) (g a))).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simpa only [List.flatMap_cons, List.map_cons, List.sum_cons] using
      (editDistance_append_le (f a) (xs.flatMap f) (g a) (xs.flatMap g)).trans (Nat.add_le_add_left ih _)

 theorem editDistance_flatMap_uniform {α β : Type*} (xs : List α) (f g : α → List β)
    (k : ℕ) (hk : ∀ a ∈ xs, editDistance (f a) (g a) ≤ k) :
    editDistance (xs.flatMap f) (xs.flatMap g) ≤ xs.length*k := by
  apply (editDistance_flatMap_le xs f g).trans
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have ha := hk a (by simp)
    have hs := ih (fun a ha => hk a (by simp [ha]))
    nlinarith

 theorem ed_tagged_halfBit_le {M : ℕ} [NeZero M] (he : M = 2*(M/2)) (v w : ZMod M) :
    editDistance (List.ofFn (fun b : Fin M => (b,halfBit v b.val)))
      (List.ofFn (fun b : Fin M => (b,halfBit w b.val))) ≤ 2*(w-v).valMinAbs.natAbs := by
  apply (editDistance_ofFn_le_hamming _ _).trans
  have heq : (Finset.univ.filter fun i : Fin M => (i,halfBit v i.val) ≠ (i,halfBit w i.val)) =
      (Finset.univ.filter fun i : Fin M => halfBit v i.val ≠ halfBit w i.val) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply not_congr
    constructor
    · exact congrArg Prod.snd
    · intro hh
      rw [hh]
  rw [heq]
  exact le_of_eq ((halfHamming_fin v w).trans (halfHamming_eq he v w))

 theorem tree_coordinate_ed (J A : ℕ → Type) [∀ l, Fintype (J l)]
    {M R : ℕ} (P : ℕ → ℕ) (tags : ∀ l, List (J (l+1)))
    (hsum : ∀ l (f : J (l+1) → ℕ), ((tags l).map f).sum = ∑ j, f j)
    (tag : ∀ l, J (l+1) → A l → A (l+1))
    (γ : ∀ l, ℕ → J (l+1) → ZMod M)
    (W : ∀ l, (TreeLeaf J l → ZMod M) → List (A l))
    (hbase : ∀ v w, editDistance (W 0 v) (W 0 w) ≤ 2*(w PUnit.unit-v PUnit.unit).valMinAbs.natAbs)
    (hrec : ∀ l v, W (l+1) v = (List.range (R*P (l+1))).flatMap
      (fun a => (tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j))))
    (l : ℕ) (v w : TreeLeaf J l → ZMod M) :
    editDistance (W l v) (W l w) ≤ 2*treeCopies R P l * ∑ i, (w i-v i).valMinAbs.natAbs := by
  classical
  induction l with
  | zero => simpa only [treeCopies, mul_one, Fintype.sum_unique] using hbase v w
  | succ l ih =>
    rw [hrec, hrec]
    have hr : ∀ a, editDistance
        ((tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j)))
        ((tags l).flatMap (fun j => (W l (fun i => w (j,i)+γ l a j)).map (tag l j))) ≤
        2*treeCopies R P l * ∑ i, (w i-v i).valMinAbs.natAbs := by
      intro a
      apply (editDistance_flatMap_le _ _ _).trans
      rw [hsum]
      change (∑ j, editDistance _ _) ≤ 2*treeCopies R P l *
        ∑ i : J (l+1) × TreeLeaf J l, (w i-v i).valMinAbs.natAbs
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      apply (editDistance_map_le _ _ _).trans
      have hh := ih (fun i => v (j,i)+γ l a j) (fun i => w (j,i)+γ l a j)
      simpa only [add_sub_add_right_eq_sub] using hh
    have hh := editDistance_flatMap_uniform (List.range (R*P (l+1))) _ _
      (2*treeCopies R P l * ∑ i, (w i-v i).valMinAbs.natAbs) (fun a _ => hr a)
    simpa only [List.length_range, treeCopies, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hh

 theorem tree_single_ed (J A : ℕ → Type) [∀ l, Fintype (J l)]
    {M R : ℕ} [NeZero M] (P : ℕ → ℕ) (tags : ∀ l, List (J (l+1)))
    (hsum : ∀ l (f : J (l+1) → ℕ), ((tags l).map f).sum = ∑ j, f j)
    (tag : ∀ l, J (l+1) → A l → A (l+1))
    (γ : ∀ l, ℕ → J (l+1) → ZMod M)
    (W : ∀ l, (TreeLeaf J l → ZMod M) → List (A l))
    (hbase : ∀ v w, editDistance (W 0 v) (W 0 w) ≤ 2*(w PUnit.unit-v PUnit.unit).valMinAbs.natAbs)
    (hrec : ∀ l v, W (l+1) v = (List.range (R*P (l+1))).flatMap
      (fun a => (tags l).flatMap (fun j => (W l (fun i => v (j,i)+γ l a j)).map (tag l j))))
    (l : ℕ) (v : TreeLeaf J l → ZMod M) (i : TreeLeaf J l) (q : ℕ) :
    editDistance (W l v) (W l (v+Pi.single i (q : ZMod M))) ≤ 2*treeCopies R P l*q := by
  classical
  have hh := tree_coordinate_ed J A P tags hsum tag γ W hbase hrec l v (v+Pi.single i (q : ZMod M))
  have hs : (∑ k, ((v+Pi.single i (q : ZMod M) : TreeLeaf J l → ZMod M) k-v k).valMinAbs.natAbs) = (q : ZMod M).valMinAbs.natAbs := by
    simp only [Pi.add_apply, add_sub_cancel_left, Pi.single_apply]
    simp only [apply_ite, ZMod.valMinAbs_zero, Int.natAbs_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hs] at hh
  apply hh.trans
  apply Nat.mul_le_mul_left
  rw [ZMod.valMinAbs_natAbs_eq_min]
  exact (min_le_left _ _).trans ((ZMod.val_natCast M q).trans_le (Nat.mod_le _ _))

 theorem tree_length_eq (J : ℕ → Type) [∀ l, Fintype (J l)] (M R : ℕ) (P L : ℕ → ℕ)
    (h0 : L 0=M) (hL : ∀ l, L (l+1)=(R*P (l+1))*(Fintype.card (J (l+1))*L l)) (l : ℕ) :
    L l = M*Fintype.card (TreeLeaf J l)*treeCopies R P l := by
  induction l with
  | zero => simp only [TreeLeaf, Fintype.card_punit, treeCopies, mul_one, h0]
  | succ l ih =>
    change L (l+1) = M*Fintype.card (J (l+1) × TreeLeaf J l)*treeCopies R P (l+1)
    rw [hL, ih, Fintype.card_prod, treeCopies]
    ring

 theorem excluded_CRT_shift {h M : ℕ} {p : ℕ → ℕ → ℕ}
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l, Pairwise (fun i j : Fin h => Nat.Coprime (p l i) (p l j)))
    (l : ℕ) (z : MaskResidues h p (l+1)) :
    ∃ q, q < period h p (l+1) ∧ ∀ a j,
      excludedTranslation h p M (l+1) (q+a) j =
        excludedPhaseHom h p M (l+1) (hd (l+1)) z j + excludedTranslation h p M (l+1) a j := by
  obtain ⟨q,hq,hz⟩ := residue_representative (fun k : Fin h => p (l+1) k) (hn _) (hp _) z
  refine ⟨q,hq,?_⟩
  intro a j
  rw [← excludedPhaseHom_natCast h p M (l+1) (q+a) (hd _) (hn _),
    ← excludedPhaseHom_natCast h p M (l+1) a (hd _) (hn _)]
  have he : (fun k : Fin h => ((q+a : ℕ) : ZMod (p (l+1) k))) = z+(fun k : Fin h => (a : ZMod (p (l+1) k))) := by
    funext k
    simp only [Nat.cast_add, hz, Pi.add_apply]
  rw [he, map_add, Pi.add_apply]

 theorem flatExcludedWord_succ (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : TreeLeaf (fun _ => Fin h) (l+1) → ZMod M) :
    flatExcludedWord h p R M (l+1) v = (List.range (R*period h p (l+1))).flatMap
      (fun a => (excludedTags h (l+1)).flatMap (fun j =>
        (flatExcludedWord h p R M l (fun i => v (j,i)+excludedTranslation h p M (l+1) a j)).map (Prod.mk j))) := by
  unfold flatExcludedWord
  rw [excludedWord_succ]
  apply List.flatMap_congr
  intro a _
  unfold taggedRow
  apply List.flatMap_congr
  intro j _
  congr 2
  change excludedWord h p R M l (shiftExcludedState h M l (flatExcludedState h M l (fun i => v (j,i))) _) = _
  rw [flatExcludedState_shift]

 theorem excluded_cheap_ed {h M R : ℕ} {p : ℕ → ℕ → ℕ} (hR : 0 < R)
    (hd : ∀ l (k : Fin h), p l k ∣ M) (hn : ∀ l (k : Fin h), 0 < p l k)
    (hp : ∀ l, Pairwise (fun i j : Fin h => Nat.Coprime (p l i) (p l j)))
    (l : ℕ) (v c : TreeLeaf (fun _ => Fin h) l → ZMod M)
    (hc : c ∈ treeCheap (fun _ => Fin h) (MaskResidues h p) (fun l => excludedPhaseHom h p M l (hd l)) l) :
    R*editDistance (flatExcludedWord h p R M l v) (flatExcludedWord h p R M l (v+c)) ≤ 2*l*excludedLength h p R M l := by
  apply tree_cheap_ed (fun _ => Fin h) (MaskResidues h p) (ExcludedAlphabet h M) hR
    (period h p) (excludedLength h p R M) (fun l => excludedTags h (l+1)) (fun _ => Prod.mk)
    (fun l => excludedPhaseHom h p M l (hd l)) (fun l => excludedTranslation h p M (l+1))
    (flatExcludedWord h p R M) (fun l v => length_excludedWord h p R M l (flatExcludedState h M l v))
    (fun _ => rfl) (flatExcludedWord_succ h p R M) (excluded_CRT_shift hd hn hp) l v c hc

 theorem sum_map_excludedTags (h l : ℕ) (f : Fin h → ℕ) :
    ((excludedTags h l).map f).sum = ∑ j, f j := by
  simp only [excludedTags, List.map_ofFn, Function.comp_id, List.sum_ofFn]

 theorem flatExcludedWord_base (h : ℕ) (p : ℕ → ℕ → ℕ) (R M : ℕ)
    (v : TreeLeaf (fun _ => Fin h) 0 → ZMod M) :
    flatExcludedWord h p R M 0 v = List.ofFn (fun b : Fin M => (b,halfBit (v PUnit.unit) b.val)) := by
  rfl

 theorem excluded_single_ed {h M R : ℕ} {p : ℕ → ℕ → ℕ} [NeZero M] (he : M=2*(M/2))
    (l : ℕ) (v : TreeLeaf (fun _ => Fin h) l → ZMod M) (i : TreeLeaf (fun _ => Fin h) l) (q : ℕ) :
    editDistance (flatExcludedWord h p R M l v) (flatExcludedWord h p R M l (v+Pi.single i (q : ZMod M))) ≤
      2*treeCopies R (period h p) l*q := by
  apply tree_single_ed (fun _ => Fin h) (ExcludedAlphabet h M) (period h p) (fun l => excludedTags h (l+1))
    (fun l => sum_map_excludedTags h (l+1)) (fun _ => Prod.mk) (fun l => excludedTranslation h p M (l+1))
    (flatExcludedWord h p R M) _ (flatExcludedWord_succ h p R M) l v i q
  intro v w
  rw [flatExcludedWord_base, flatExcludedWord_base]
  exact ed_tagged_halfBit_le he _ _

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.Parameters ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

theorem StandingPrimes.small_prime {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) (k : Fin h) :
    p l k ≤ h^4 := by
  apply (hp.atLevel l hl hlh k).2.2.trans
  calc
    2*h^3 ≤ h*h^3 := Nat.mul_le_mul_right _ hh
    _ = h^4 := by ring

 theorem StandingPrimes.period_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) (l : ℕ) (hl : 1≤l) (hlh : l≤h) :
    period h p l ≤ h^(4*h) := by
  calc
    _ ≤ ∏ _k : Fin h, h^4 := Finset.prod_le_prod' (fun k _ => hp.small_prime hh l hl hlh k)
    _ = _ := by simp [← pow_mul]

 theorem StandingPrimes.circle_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) : circleSize h p ≤ h^(5*h^2) := by
  calc
    _ ≤ h*(∏ _l : Fin h, h^(4*h)) := Nat.mul_le_mul hh
      (Finset.prod_le_prod' (fun l _ => hp.period_bound hh (l.val+1) (by omega) (by omega)))
    _ = h^(4*h^2+1) := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

 theorem StandingPrimes.log_circle_bound {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 2 ≤ h) : Nat.log 2 (circleSize h p)+1 ≤ 6*h^3 := by
  have ht : h ≤ 2^h := (Nat.lt_two_pow_self (n:=h)).le
  have hm : circleSize h p ≤ 2^(5*h^3) := by
    calc
      _ ≤ h^(5*h^2) := hp.circle_bound hh
      _ ≤ (2^h)^(5*h^2) := Nat.pow_le_pow_left ht _
      _ = _ := by rw [← pow_mul]; congr 1; ring
  have hn := Nat.log_mono_right hm (b:=2)
  rw [Nat.log_pow (by norm_num : 1<2)] at hn
  have hp3 : 0<h^3 := pow_pos (by omega) _
  nlinarith

 theorem StandingPrimes.excluded_length_pos {h : ℕ} {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes h p) (hh : 1≤h) {R : ℕ} (hR : 0<R) (l : ℕ) :
    0<excludedLength h p R (circleSize h p) l := by
  induction l with
  | zero => exact hp.circle_pos
  | succ l ih =>
    simp only [excludedLength,length_excludedTags]
    exact Nat.mul_pos (Nat.mul_pos hR (hp.period_pos _)) (Nat.mul_pos (by omega) ih)

 theorem StandingPrimes.log_circle_fourth {n : ℕ} (hn : 1000000≤n) {p : ℕ → ℕ → ℕ}
    (hp : StandingPrimes (n^4) p) : Nat.log 2 (circleSize (n^4) p)+1≤n^13 := by
  have nh : 2≤n^4 := (show 2≤n by omega).trans (le_self_pow₀ (by omega) (by norm_num))
  calc
    _ ≤ 6*(n^4)^3 := hp.log_circle_bound nh
    _ ≤ n*(n^4)^3 := Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

end FiniteCircle

end OAI

-- ---- from OAI.Combinatorics.FiniteCircle.BinaryDistortion ----
namespace OAI

namespace FiniteCircle

open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module

 theorem flatExcludedState_surjective (h M l : ℕ) :
    Function.Surjective (flatExcludedState h M l) := by
  classical
  induction l with
  | zero => intro v; exact ⟨fun _ => v,rfl⟩
  | succ l ih =>
    intro v
    choose f hf using fun j => ih (v j)
    refine ⟨fun i => f i.1 i.2, ?_⟩
    funext j
    exact hf j

 theorem range_comp_surjective {X Y Z : Type*} (f : X → Y) (g : Y → Z) (hf : Function.Surjective f) :
    Set.range (fun x => g (f x)) = Set.range g := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩; exact ⟨f x,rfl⟩
  · rintro ⟨y,rfl⟩; obtain ⟨x,rfl⟩ := hf y; exact ⟨x,rfl⟩

 theorem excluded_length_factor (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ) :
    excludedLength h p R M l = M*Fintype.card (TreeLeaf (fun _ => Fin h) l)*treeCopies R (period h p) l := by
  apply tree_length_eq (fun _ => Fin h) M R (period h p) (excludedLength h p R M) rfl
  intro l
  simp only [excludedLength,length_excludedTags,Fintype.card_fin]

 theorem excluded_binary_distortion {n k : ℕ} (hn : 1000000≤n) (hk : n^4=4*k)
    {p : ℕ → ℕ → ℕ} (hp : StandingPrimes (n^4) p) {w : ℕ}
    (c : ExcludedAlphabet (n^4) (circleSize (n^4) p) (n^4) → Fin w → Bool)
    (hc : SubstitutionBounds (1/268435456) 67108928 c) :
    (n:ℝ)^k ≤ setDistortion (Set.range fun v : ExcludedState (n^4) (circleSize (n^4) p) (n^4) =>
      encode c (excludedWord (n^4) p ((n^4)^(2*n^4)) (circleSize (n^4) p) (n^4) v)) := by
  classical
  let h := n^4
  let M := circleSize h p
  let R := h^(2*h)
  let : NeZero M := ⟨hp.circle_pos.ne'⟩
  have hh : 2≤h := (show 2≤n by omega).trans (le_self_pow₀ (by omega) (by norm_num))
  have hR : 0<R := pow_pos (by omega) _
  let H := excludedCheap h p M hp.divides_circle h
  let : Fintype H := Fintype.ofFinite H
  have hhb (χ : AddChar (TreeLeaf (fun _ => Fin h) h → ZMod M) ℂ)
      (ha : χ.compAddMonoidHom H.subtype=0) (hw : χ (fun _ => ((M/2:ℕ):ZMod M))≠1) :
      ((h:ℝ)/2)^h ≤ ∑ i, ((coordinateFrequency χ i).valMinAbs.natAbs:ℝ) := by
    apply excluded_character_branching hh hp.divides_circle hp.positive
      (fun l k hl hlh => (hp.atLevel l hl hlh k).1)
      hp.level_injective (fun l k hl hlh => (hp.atLevel l hl hlh k).2.1.le) χ ha _ hw
  have hlong (v : TreeLeaf (fun _ => Fin h) h → ZMod M) :
      (excludedLength h p R M h:ℝ)/(n:ℝ)^(3*n^4) ≤
        (deficit (flatExcludedWord h p R M h v) (flatExcludedWord h p R M h (v+(fun _ => ((M/2:ℕ):ZMod M)))):ℝ) := by
    have he : n^4=2*(n^4/2) := by omega
    have ht := excluded_long_deficit hn he hp hR (flatExcludedState h M h v)
    have hf := flatExcludedState_shift h M h v ((M/2:ℕ):ZMod M)
    change flatExcludedState h M h (v+(fun _ => ((M/2:ℕ):ZMod M))) = _ at hf
    simpa only [flatExcludedWord,hf] using ht
  have ht := coded_range_lower hn hk (hp.log_circle_fourth hn) H (fun _ => ((M/2:ℕ):ZMod M)) hhb
    (flatExcludedWord h p R M h) (excludedLength h p R M h) (treeCopies R (period h p) h)
    (hp.excluded_length_pos (by omega) hR h) (excluded_length_factor h p R M h)
    (fun v => length_excludedWord h p R M h (flatExcludedState h M h v))
    (fun v z => excluded_cheap_ed hR hp.divides_circle hp.positive hp.coprime h v z z.property)
    (fun v i j => excluded_single_ed (StandingPrimes.circle_even (h:=h) (p:=p)) h v i (2^j.val)) hlong c hc
  have he := range_comp_surjective (flatExcludedState h M h)
    (fun v => encode c (excludedWord h p R M h v)) (flatExcludedState_surjective h M h)
  unfold flatExcludedWord at ht
  rw [he] at ht
  exact ht

end FiniteCircle

end OAI

-- ---- platform node ----
open OAI OAI.FiniteCircle
open scoped BigOperators List
open scoped ComplexConjugate
open RCLike Module


theorem solution : type_of% @_root_.OAI.FiniteCircle.excluded_binary_distortion := @_root_.OAI.FiniteCircle.excluded_binary_distortion
