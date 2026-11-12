-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:39:34.768093+00:00
-- url     : https://prove2.me/submissions/fb8b5e37-3242-44ad-8cb9-1104ba52ff0f

import Mathlib
import Definitions.Def_Q238L026
import Theorems.Thm_OAI_MetricKMedianRecovery_RationalLeaves_prefix_leaf_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
namespace Entry
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {i : X}
lemma mem (h : Entry loc F B Q v z lam eta i) : i ∈ F ∪ B := by
  rcases h.2 with h|h
  · exact Finset.mem_union_right _ h
  · exact Finset.mem_union_left _ h.1
end Entry

namespace Prefix
variable {loc : D → X} {F B Q Q' : Finset X} {v z lam eta : ℝ} {H G : List X}

lemma opened_subset (h : Prefix loc F B v z lam eta Q H) : H.toFinset ⊆ F ∪ B := by
  intro i hi
  induction h with
  | nil => simp at hi
  | cons ha ht ih =>
    simp only [List.toFinset_cons,Finset.mem_insert] at hi
    rcases hi with rfl|hi
    · exact ha.mem
    · exact ih hi

end Prefix

end PhaseSequence
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PhasesBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LeafMetric
variable {V C : Type*} [PseudoMetricSpace V]

lemma copy_distance (root : C → V) (u : C → ℝ) (x : V) (c : C) :
    leafDist root u (.inl x) (.inr c) = dist x (root c)+u c := by
  simp [leafDist,height,parent]

end MetricKMedianRecovery.LeafMetric

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.levelWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.parentWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

lemma leaf_dist (i j : V) (key : ℕ) (s : ℚ) :
    dist (original i) (leaf key j s)=dist i j+(max s 0:ℚ) :=
  LeafMetric.copy_distance root height i (key,j,s)

variable [DecidableEq V]

omit [PseudoMetricSpace V] in
lemma fresh (F : Finset V) (B : Finset (Label V)) (key : ℕ) (hB : Before key B)
    (i : V) (s : ℚ) : leaf key i s ∉ F.image original ∪ B := by
  intro h
  rcases Finset.mem_union.mp h with h|h
  · obtain ⟨x,_,hx⟩ := Finset.mem_image.mp h
    cases hx
  · exact (lt_irrefl key) (hB (key,i,s) h)

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma Before.mono {B : Finset (Label V)} {a b : ℕ} (h : Before a B) (hab : a≤b) : Before b B :=
  fun c hc=>(h c hc).trans_le hab

omit [PseudoMetricSpace V] in
lemma singleton_before (key : ℕ) (i : V) (s : ℚ) (B : Finset (Label V)) (hB : Before key B) :
    Before (key+1) (insert (leaf key i s) B) := by
  intro c hc
  rcases Finset.mem_insert.mp hc with he|hc
  · have hh : c=(key,i,s) := Sum.inr.inj he
    subst c
    omega
  · exact (hB c hc).trans (by omega)

omit [PseudoMetricSpace V] in
lemma shorten_injective (key : ℕ) (i : V) (l u : ℚ) : Function.Injective (shorten key i l u) :=
  (Equiv.swap _ _).injective

omit [PseudoMetricSpace V] in
lemma shorten_original (key : ℕ) (i j : V) (l u : ℚ) : shorten key i l u (original j)=original j :=
  Equiv.swap_apply_of_ne_of_ne (by simp [original,leaf]) (by simp [original,leaf])

omit [PseudoMetricSpace V] in
lemma shorten_old (key : ℕ) (i : V) (l u : ℚ) (B : Finset (Label V)) (hB : Before key B)
    (x : Label V) (hx : x∈B) : shorten key i l u x=x := by
  apply Equiv.swap_apply_of_ne_of_ne
  · intro he; subst x; exact (lt_irrefl key) (hB (key,i,u) hx)
  · intro he; subst x; exact (lt_irrefl key) (hB (key,i,l) hx)

lemma shorten_dist (key : ℕ) (i : V) (l u : ℚ) (hl : 0≤l) (hlu : l≤u)
    (F : Finset V) (B : Finset (Label V)) (hB : Before key B) (j : V)
    (x : Label V) (hx : x∈F.image original ∪ insert (leaf key i u) B) :
    dist (original j) (shorten key i l u x) ≤ dist (original j) x ∧
      dist (original j) x ≤ dist (original j) (shorten key i l u x)+(u-l:ℚ) := by
  have heps : (0:ℝ)≤(u-l:ℚ) := by exact_mod_cast sub_nonneg.mpr hlu
  rcases Finset.mem_union.mp hx with hx|hx
  · obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hx
    rw [shorten_original]
    exact ⟨le_rfl,le_add_of_nonneg_right heps⟩
  · rcases Finset.mem_insert.mp hx with rfl|hx
    · rw [shorten,Equiv.swap_apply_left,leaf_dist,leaf_dist,max_eq_left hl,max_eq_left (hl.trans hlu)]
      constructor
      · have hh : (l:ℝ)≤(u:ℝ) := by exact_mod_cast hlu
        linarith
      · push_cast <;> linarith
    · rw [shorten_old key i l u B hB x hx]
      exact ⟨le_rfl,le_add_of_nonneg_right heps⟩

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_PrefixData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeInvariant
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
universe uD uX uY
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [Fintype D] [PseudoMetricSpace X] in
lemma after_append (Q : Finset X) (P T : List (List X)) :
    after Q (P++T) = after (after Q P) T := by
  induction P generalizing Q with
  | nil => rfl
  | cons H P ih => exact ih _

end MetricKMedianRecovery.PhaseMergeInvariant

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledLeaf
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.levelWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.parentWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open PhaseSequence PhaseHistoryTransfer PhaseMergeInvariant PhaseMergeRefinement
variable {V : Type*} [DecidableEq V] {d : ℕ}

lemma shorten_allowed (F : Finset V) (B : Finset (Label V)) (key : ℕ) (hB : Before key B)
    (i : V) (l u : ℚ) (x : Label V) (hx : x∈F.image original∪B) : shorten key i l u x=x := by
  rcases Finset.mem_union.mp hx with hx|hx
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    exact shorten_original key i j l u
  · exact shorten_old key i l u B hB x hx

lemma shorten_image (B : Finset (Label V)) (key : ℕ) (hB : Before key B) (i : V) (l u : ℚ) :
    (B.image (shorten key i l u))=B := by
  calc
    _=B.image id := Finset.image_congr (shorten_old key i l u B hB)
    _=B := Finset.image_id

lemma shorten_insert (B : Finset (Label V)) (key : ℕ) (hB : Before key B) (i : V) (l u : ℚ) :
    (insert (leaf key i u) B).image (shorten key i l u)=insert (leaf key i l) B := by
  rw [Finset.image_insert,shorten_image B key hB i l u,shorten,Equiv.swap_apply_left]

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma history_allowed {loc : Fin d → V} {F : Finset V} {B Q : Finset (Label V)}
    {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
    (h : History (fun j=>original (loc j)) (F.image original) B v lam eta q Q P) :
    ∀ H∈P,H.toFinset⊆F.image original∪B := by
  induction h with
  | nil => simp
  | @cons q Q H T hH hT ih =>
    intro G hG
    rcases List.mem_cons.mp hG with rfl|hG
    · exact hH.1.opened_subset
    · exact ih G hG

lemma history_shorten {loc : Fin d → V} {F : Finset V} {B Q : Finset (Label V)}
    {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
    (h : History (fun j=>original (loc j)) (F.image original) B v lam eta q Q P)
    (key : ℕ) (hB : Before key B) (i : V) (l u : ℚ) :
    P.map (List.map (shorten key i l u))=P := by
  calc
    _=P.map id := List.map_congr_left (by
      intro H hH
      change H.map (shorten key i l u)=H
      calc
        _=H.map id := List.map_congr_left (fun x hx=>shorten_allowed F B key hB i l u x
          (history_allowed h H hH (List.mem_toFinset.mpr hx)))
        _=H := List.map_id H)
    _=P := List.map_id P

lemma prefix_shorten {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v lam eta : ℝ} {q : ℕ} {P : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (key : ℕ) (hB : Before key B) (i : V) (l u : ℚ) (H : List (Label V))
    (hH : H.toFinset⊆F.image original∪B) :
    (P++[H++[leaf key i u]]).map (List.map (shorten key i l u))=P++[H++[leaf key i l]] := by
  have hm : H.map (shorten key i l u)=H := by
    calc
      _=H.map id := List.map_congr_left (fun x hx=>shorten_allowed F B key hB i l u x (hH (List.mem_toFinset.mpr hx)))
      _=H := List.map_id H
  simp only [List.map_append,List.map_cons,List.map_nil,history_shorten hp.history key hB i l u,hm]
  rw [shorten,Equiv.swap_apply_left]

end MetricKMedianRecovery.RationalLeaves

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

lemma leaf_certified_s238r_oai {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v eta lo hi : ℝ} {lam : ℚ} {q n k : ℕ} {P : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (key : ℕ) (hB : Before key B) (hkey : key<3*(q+1))
    (i : V) (H : List (Label V)) (l u : ℚ) (T U : List (List (Label V)))
    (hv : 0<v) (hv1 : v<1/6) (hlam : (0:ℝ)<lam) (hd : Disjoint (F.image original) B)
    (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hH : Good (fun j=>original (loc j)) (F.image original) B (after ∅ P) v ((1+v^2)^q) lam eta H)
    (hl0 : 0≤l) (hlu : l≤u) (hw : (u:ℝ)-(l:ℝ)≤eta)
    (hT : Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i l) B)
      (insert (leaf key i l) (after ∅ P∪H.toFinset)) v lam (q+1) n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) (insert (leaf key i u) B)
      (insert (leaf key i u) (after ∅ P∪H.toFinset)) v lam (q+1) n U)
    (hs : Sandwich k ((after (insert (leaf key i l) (after ∅ P∪H.toFinset)) T)∩F.image original).card
      ((after (insert (leaf key i u) (after ∅ P∪H.toFinset)) U)∩F.image original).card) :
    Certified loc F v eta lo hi (q+1) n k (leafState B P lam key i H l u T U) := by
  have him := shorten_insert B key hB i l u
  have hpm := prefix_shorten hp key hB i l u H hH.1.1.opened_subset
  have heps : (0:ℝ)≤(u-l:ℚ) := by exact_mod_cast sub_nonneg.mpr hlu
  have heq : ∀ s:ℚ,after ∅ (P++[H++[leaf key i s]])=insert (leaf key i s) (after ∅ P∪H.toFinset) := by
    intro s
    simp only [after_append,after,List.toFinset_append,List.toFinset_cons,List.toFinset_nil,
      Finset.union_empty,Finset.union_insert]
  refine {
    before := (singleton_before key i u B hB).mono (by omega)
    before_map := ?_
    disjoint := ?_
    low := hl
    high := hu
    price := le_rfl
    eps_nonneg := heps
    error := ?_
    inj := shorten_injective key i l u
    fixed := ?_
    shrink := ?_
    loss := ?_
    old_prefix := prefix_leaf_s238r hp key hB i u hv hv1 hlam H hH
    new_prefix := ?_
    sandwich := ?_
    new_tail := ?_
    old_tail := ?_ }
  · change Before (3*(q+1)) ((insert (leaf key i u) B).image (shorten key i l u))
    rw [him]
    exact (singleton_before key i l B hB).mono (by omega)
  · change Disjoint (F.image original) (insert (leaf key i u) B)
    rw [Finset.disjoint_insert_right]
    exact ⟨fun he=>fresh F B key hB i u (Finset.mem_union_left _ he),hd⟩
  · change (lam:ℝ)-lam+(d:ℝ)*((1-3*v)*(u-l:ℚ))≤(d:ℝ)*eta
    simp only [sub_self,zero_add]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
    have hh : (0:ℝ)≤(u:ℝ)-(l:ℝ) := by exact_mod_cast sub_nonneg.mpr hlu
    push_cast
    nlinarith only [hv,hh,hw]
  · intro x hx
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
    exact shorten_original key i j l u
  · intro j x hx
    exact (shorten_dist key i l u hl0 hlu F B hB (loc j) x hx).1
  · intro j x hx
    exact (shorten_dist key i l u hl0 hlu F B hB (loc j) x hx).2
  · change PrefixData _ _ ((insert (leaf key i u) B).image (shorten key i l u)) _ _ _ _
      ((P++[H++[leaf key i u]]).map (List.map (shorten key i l u)))
    rw [him,hpm]
    exact prefix_leaf_s238r hp key hB i l hv hv1 hlam H hH
  · change Sandwich k ((after (after ∅ ((P++[H++[leaf key i u]]).map (List.map (shorten key i l u)))) T)∩F.image original).card
      ((after (after ∅ (P++[H++[leaf key i u]])) U)∩F.image original).card
    simpa only [hpm,heq] using hs
  · change Runs _ _ ((insert (leaf key i u) B).image (shorten key i l u))
      (after ∅ ((P++[H++[leaf key i u]]).map (List.map (shorten key i l u)))) _ _ _ _ T
    simpa only [him,hpm,heq,leafState] using hT
  · change Runs _ _ _ (after ∅ (P++[H++[leaf key i u]])) _ _ _ _ U
    simpa only [heq,leafState] using hU

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.leaf_certified_s238r_oai.{u_1}
