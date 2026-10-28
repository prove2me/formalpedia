-- Prove2me | solution 1 for OAI.MatchingFPRAS.FiniteTrial.ScaleState.sampleLaw_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:20:57.778473+00:00
-- url     : https://prove2.me/submissions/03b62c5f-da15-4bd2-b52d-440795efff24

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ColoredEdge
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.Transport.Sparse.decideOverlay _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V L : Type*}

variable {E : Type*} [DecidableEq V] [DecidableEq E] (inc : E → V → Prop)

lemma union_eq_of_multiset_union_eq {M N A B : Finset E}
    (h : M.val + N.val = A.val + B.val) : M ∪ N = A ∪ B := by
  ext e
  have he := congrArg (fun s : Multiset E => e ∈ s) h
  simpa only [Multiset.mem_add, Finset.mem_val, Finset.mem_union] using (iff_of_eq he)

omit [DecidableEq V] in
lemma layer_agreement_adj {M N A B : Finset E} {U : Finset V}
    (hM : MatchingOn inc M U) (hN : MatchingOn inc N U)
    (hA : MatchingOn inc A U) (hB : MatchingOn inc B U)
    (hu : M ∪ N = A ∪ B) {e f : E}
    (hadj : (overlayLineGraph inc (M ∪ N)).Adj e f)
    (he : e ∈ M ↔ e ∈ A) : f ∈ M ↔ f ∈ A := by
  obtain ⟨hne, heu, hfu, v, hev, hfv⟩ := hadj
  by_cases heM : e ∈ M
  · have heA := he.mp heM
    have hfM : f ∉ M := fun hf =>
      hne (hM.unique (hM.1 e heM v hev) heM hev hf hfv)
    have hfA : f ∉ A := fun hf =>
      hne (hA.unique (hA.1 e heA v hev) heA hev hf hfv)
    exact iff_of_false hfM hfA
  · have heA : e ∉ A := fun h => heM (he.mpr h)
    have heN : e ∈ N := (Finset.mem_union.mp heu).resolve_left heM
    have heB : e ∈ B := (Finset.mem_union.mp (hu ▸ heu)).resolve_left heA
    have hfN : f ∉ N := fun hf =>
      hne (hN.unique (hN.1 e heN v hev) heN hev hf hfv)
    have hfB : f ∉ B := fun hf =>
      hne (hB.unique (hB.1 e heB v hev) heB hev hf hfv)
    exact iff_of_true ((Finset.mem_union.mp hfu).resolve_right hfN)
      ((Finset.mem_union.mp (hu ▸ hfu)).resolve_right hfB)

omit [DecidableEq V] in
lemma layer_agreement_reachable {M N A B : Finset E} {U : Finset V}
    (hM : MatchingOn inc M U) (hN : MatchingOn inc N U)
    (hA : MatchingOn inc A U) (hB : MatchingOn inc B U)
    (hu : M ∪ N = A ∪ B) {e f : E}
    (hr : (overlayLineGraph inc (M ∪ N)).Reachable e f)
    (he : e ∈ M ↔ e ∈ A) : f ∈ M ↔ f ∈ A := by
  have hrel := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hr
  clear hr
  induction hrel with
  | refl => exact he
  | tail hpath hadj ih => exact layer_agreement_adj inc hM hN hA hB hu hadj ih

omit [DecidableEq V] in
lemma pair_reconstruction {M N A B : Finset E} {U : Finset V}
    (hM : MatchingOn inc M U) (hN : MatchingOn inc N U)
    (hA : MatchingOn inc A U) (hB : MatchingOn inc B U)
    (hu : M.val + N.val = A.val + B.val) (anchor : E)
    (hbit : anchor ∈ M ↔ anchor ∈ A)
    (hout : ∀ e ∈ M ∪ N, ¬ (overlayLineGraph inc (M ∪ N)).Reachable anchor e →
      (e ∈ M ↔ e ∈ A)) : M = A ∧ N = B := by
  have hset := union_eq_of_multiset_union_eq hu
  have hMA : M = A := by
    ext e
    by_cases hr : (overlayLineGraph inc (M ∪ N)).Reachable anchor e
    · exact layer_agreement_reachable inc hM hN hA hB hset hr hbit
    · by_cases he : e ∈ M ∪ N
      · exact hout e he hr
      · have heM : e ∉ M := fun hm => he (Finset.mem_union_left _ hm)
        have heA : e ∉ A := fun ha => he (hset.symm ▸ Finset.mem_union_left B ha)
        exact iff_of_false heM heA
  refine ⟨hMA, Finset.val_injective ?_⟩
  rw [hMA] at hu
  exact add_left_cancel hu

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SumLiftMate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

 theorem paired_prefix_weight (a : Bool) (xs ys : List ℝ) :
    wordWeight a (duplicate xs ++ ys) = xs.prod * wordWeight a ys := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih, mul_assoc]

theorem profile_weight (a : Bool) (left right : List ℝ) (lam : ℝ) :
    wordWeight a (duplicate left ++ [lam] ++ duplicate right) =
      left.prod * right.prod * (if a then lam else 1) := by
  rw [List.append_assoc, paired_prefix_weight]
  simp only [List.singleton_append, wordWeight]
  have h := paired_prefix_weight (!a) right []
  simp only [List.append_nil, wordWeight_nil, mul_one] at h
  rw [h]
  ring

theorem wordWeight_ofFn (n : ℕ) (w : Fin n → ℝ) (a : Bool) :
    wordWeight a (List.ofFn w) = ∏ i, (if alternating a i.val then w i else 1) := by
  induction n generalizing a with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ, Fin.prod_univ_succ]
    simp only [wordWeight, Fin.val_zero, alternating_zero]
    rw [ih]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    simp

 theorem intact_weight {m : ℕ} (w : Fin (m+1) → ℝ) (b : Selection m)
    (h : Valid ∅ b) : selectedWeight w b = wordWeight (b 0) (List.ofFn w) := by
  rw [wordWeight_ofFn]
  unfold selectedWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [(intact_iff b).mp h]

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Profile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Subdivision

open Finset

 theorem profileActivity_ofFn (p : ℕ) (B Hu Hv lam : ℝ) :
    List.ofFn (profileActivity p B Hu Hv lam) = profile p B Hu Hv lam := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, profileActivity, List.get_eq_getElem, Fin.val_cast]

section Deletion

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
 theorem deletion_weight [Fintype V] [Fintype E] {m : ℕ} (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base b : E → Selection m)
    (hb0 : FamilyHoles u v m R₀ U base) (hb : FamilyHoles u v m R₀ U b)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e)) :
    (∏ e, selectedWeight (w e) (b e)) =
      deletionConstant U base w (fun e => (left e).prod * (right e).prod) *
        ∏ e, if extract U b e then lam e else 1 := by
  classical
  unfold deletionConstant
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : (U e).Nonempty
  · have heq := broken_unique he (hb0.1 e) (hb.1 e)
    simp [extract,he,heq]
  · have he' : U e = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    simp only [extract,he,↓reduceIte]
    rw [intact_weight _ _ (by simpa [he'] using hb.1 e),hw e,profile_weight]

theorem deletion_partition_identity {m : ℕ} (hm : Even m) (u v : E → V) (R₀ : Finset V)
    (U : E → Finset (Fin m)) (base : E → Selection m)
    (hb : FamilyHoles u v m R₀ U base)
    (w : E → Fin (m+1) → ℝ) (left right : E → List ℝ) (lam : E → ℝ)
    (hw : ∀ e, List.ofFn (w e) = duplicate (left e) ++ [lam e] ++ duplicate (right e)) :
    realHolePartition u v m R₀ U w =
      deletionConstant U base w (fun e => (left e).prod * (right e).prod) *
        logicalHolePartition u v (residualHoles u v R₀ U base) (broken U) lam := by
  classical
  let := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R₀ U b}
  let := Fintype.ofFinite {s : E → Bool //
    LogicalHoles u v (residualHoles u v R₀ U base) (broken U) s}
  unfold realHolePartition logicalHolePartition
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (deletionEquiv hm u v R₀ U base hb)
  intro b
  exact deletion_weight u v R₀ U base b.val hb b.property w left right lam hw

end Deletion

end MatchingFPRAS.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Height
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (inc : E → V → Prop)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma partitionWeight_mono (r w : E → ℝ) (hr : ∀ e,0 ≤ r e) (hrw : ∀ e,r e≤w e)
    (U : Finset V) : partitionWeight inc r U≤partitionWeight inc w U :=
  Finset.sum_le_sum (fun _ _ => Finset.prod_le_prod (fun e _ => hr e) (fun e _ => hrw e))

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Incident
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Representation

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.Enlargement
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (R : Finset V) (s : LogicalEdge V → Bool)
    (hs : LogicalHoles source target R ∅ s)

variable {R s hs}

lemma selection_weight (w : V → V → ℝ) (m : Mate V) :
    (∏ e : LogicalEdge V, if select m e then logicalActivity w e else 1)=weight w m := by
  classical
  unfold weight
  rw [← Finset.prod_filter,← Finset.prod_filter]
  apply Finset.prod_bij (fun e _ => source e)
  · intro e he
    have hh := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hh]
    exact e.property
  · intro e he f hf h
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    have hf' := (select_eq_true m f).mp (Finset.mem_filter.mp hf).2
    exact Subtype.ext (Prod.ext h (he'.symm.trans ((congrArg m.val h).trans hf')))
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    refine ⟨⟨(x,m.val x),hx'⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [select,source,target]⟩
  · intro e he
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [logicalActivity,edgeActivity,show source e < target e from e.property,ite_true,he']

lemma asMate_weight (w : V → V → ℝ) :
    (∏ e : LogicalEdge V, if s e then logicalActivity w e else 1)=weight w (asMate R s hs) := by
  rw [← selection_weight,select_asMate]

theorem logical_partition_eq (w : V → V → ℝ) (R : Finset V) :
    logicalHolePartition source target R ∅ (logicalActivity w)=partition w R := by
  classical
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s}
  let := Fintype.ofFinite {m : Mate V // HasHoles m R}
  unfold logicalHolePartition partition
  rw [Finset.sum_subtype (matchings R) (fun m => mem_matchings m R)]
  apply Fintype.sum_equiv (matchingEquiv R)
  intro s
  exact asMate_weight w

end MatchingFPRAS.Representation

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Representation
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma pathConstant_pos (p : ℕ) (B Hu Hv : ℝ) (hB : 0 < B) :
    0 < pathConstant p B Hu Hv := by
  apply mul_pos <;> apply Finset.prod_pos <;> intro i hi <;> exact hB.trans_le (le_max_left _ _)

theorem intact_partition_identity (w : V → V → ℝ) (hz : 0 < partition w ∅)
    (p : ℕ) (B Hu Hv : LogicalEdge V → ℝ) :
    realHolePartition source target (4*p) ∅ (fun _ => ∅)
      (pathActivity p B Hu Hv (logicalActivity w)) =
      (∏ e, pathConstant p (B e) (Hu e) (Hv e)) * partition w ∅ := by
  classical
  have hn : (matchings (∅ : Finset V)).Nonempty := by
    by_contra hn
    have hz0 : partition w ∅=0 := by
      simp [partition,Finset.not_nonempty_iff_eq_empty.mp hn]
    linarith
  obtain ⟨m,hm⟩ := hn
  let b := fun (e : LogicalEdge V) (i : Fin (4*p+1)) => alternating (select m e) i.val
  have hb := intact_family p m ((mem_matchings m ∅).mp hm)
  have hid := deletion_partition_identity (show Even (4*p) from ⟨2*p,by omega⟩)
    source target ∅ (fun _ => ∅) b hb (pathActivity p B Hu Hv (logicalActivity w))
    (fun e => List.ofFn fun r : Fin p => max (B e) (Hu e/2^r.val))
    (fun e => (List.ofFn fun r : Fin p => max (B e) (Hv e/2^r.val)).reverse) _
    (fun e => profileActivity_ofFn p (B e) (Hu e) (Hv e) (logicalActivity w e))
  simpa [residualHoles,broken,deletionConstant,List.prod_ofFn,pathConstant,
    logical_partition_eq] using hid

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_EdgeLow
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RealGeometry

open Finset MatchingFPRAS.Subdivision MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (m : ℕ)

omit [DecidableEq E] in
lemma selectedSet_weight (w : E → Fin (m+1) → ℝ) (b : E → Selection m) :
    (∏ q ∈ selectedSet m b,w q.1 q.2)=∏ e,selectedWeight (w e) (b e) := by
  classical
  simp only [selectedSet,Finset.prod_filter,selectedWeight,Fintype.prod_prod_type]

omit [DecidableEq V] in
theorem realMatching_partition (huv : ∀ e,u e≠v e) (R : Finset V) (U : E → Finset (Fin m))
    (w : E → Fin (m+1) → ℝ) :
    partitionWeight (fun (q : E × Fin (m+1)) x => x∈edge u v m q.1 q.2) (fun q => w q.1 q.2) (survivors m R U)=
      realHolePartition u v m R U w := by
  classical
  let := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R U b}
  unfold partitionWeight realHolePartition
  rw [←(realMatchingEquiv u v m huv R U).sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  exact selectedSet_weight m w b.val

end MatchingFPRAS.RealGeometry

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_IndexedCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*}

variable (inc : E → V → Prop)

namespace IndexedCycle

variable {inc} (c : IndexedCycle inc)

lemma vertexAt_mod (i : ℕ) : c.vertexAt (i % c.size) = c.vertexAt i := by
  exact congrArg c.vertex (Fin.ext (Nat.mod_mod i c.size))

end IndexedCycle

end

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Sets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Cells
open SimpleGraph

variable {L : Type*} {G : SimpleGraph L}
namespace CycleData

variable [DecidableEq L] {m : ℕ} (C : CycleData G m)

namespace Subdivision

variable {C} {x y : ℕ}

lemma cells_length (Q : Subdivision C x y) : 2 * Q.cells + 1 + x = y := by
  induction Q with
  | edge h => simp only [cells]; omega
  | node cell Q₁ Q₂ Q₃ h₁ h₂ h₃ => simp only [cells]; omega

end Subdivision

end CycleData

end MatchingFPRAS.Cells

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_LabelCycle
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
variable {V E L : Type*}
namespace IndexedCycle

variable {bags : V → Finset L}

variable (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable [DecidableEq L]

lemma chord_short (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) (h : y = x+1) :
    c.chord hbags x y hxy hy ha = c.edgeAt x := by
  simp only [chord, dite_eq_left h]

lemma chord_wrap (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) (h : x = 0 ∧ y+1 = c.size) :
    c.chord hbags x y hxy hy ha = c.edgeAt y := by
  have hn : y ≠ x+1 := by have := c.four_le; omega
  simp only [chord, dite_eq_right hn, dite_eq_left h]

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_PM
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.LongComponent.instFintype _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.Transport.Sparse.decideOverlay _root_.OAI.MatchingFPRAS.Transport.instFintypePM _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [Fintype V] [DecidableEq E]

variable (inc : E → V → Prop)

omit [DecidableEq E] in
lemma padOccurrences_recovers {m n : Multiset E} (hm : m.card ≤ 4) (hn : n.card ≤ 4)
    (h : padOccurrences m = padOccurrences n) : m = n := by
  have hl : m.toList = n.toList := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < 4
    · exact congrFun h ⟨i, hi⟩
    · have hm' : m.toList.length ≤ i := by rw [Multiset.length_toList]; omega
      have hn' : n.toList.length ≤ i := by rw [Multiset.length_toList]; omega
      rw [List.getElem?_eq_none hm', List.getElem?_eq_none hn']
  simpa only [Multiset.coe_toList] using congrArg (fun l : List E => (l : Multiset E)) hl

omit [DecidableEq E] in
lemma tag_card [Fintype E] : Fintype.card (DemandTag (V := V) (E := E)) =
    Fintype.card E * Fintype.card V ^ 4 * 128 * (Fintype.card E + 1) ^ 8 := by
  simp only [DemandTag, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_option]
  ring

omit [DecidableEq E] in
lemma tag_card_bound [Fintype E] (N : ℕ) (hN : 2 ≤ N) (hV : Fintype.card V ≤ N)
    (hE : Fintype.card E ≤ 2 * N^2) :
    Fintype.card (DemandTag (V := V) (E := E)) ≤ (10*N)^30 := by
  rw [tag_card]
  have hp : 1 ≤ N^2 := Nat.one_le_pow 2 N (by omega)
  have he : Fintype.card E + 1 ≤ 3 * N^2 := by omega
  calc
    _ ≤ (2*N^2) * N^4 * 128 * (3*N^2)^8 := by gcongr
    _ = (2*128*3^8) * N^22 := by ring
    _ ≤ 10^30 * N^30 := by
      exact Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right (by omega) (by omega))
    _ = _ := by ring

namespace DemandEncoding

variable {inc}

theorem code_recovers {d e : RawDemand inc} (a : DemandEncoding inc d)
    (b : DemandEncoding inc e) (h : a.code = b.code) : d = e := by
  simp only [code, Prod.mk.injEq] at h
  obtain ⟨hf,hs,ha,hc,hfl,hbit,had,hdr⟩ := h
  have hu : d.first.val.val + d.second.val.val = e.first.val.val + e.second.val.val := by
    have hh := a.conservation
    rw [hf, hs, hdr, ← b.conservation, ← had] at hh
    exact add_right_cancel hh
  have hunion := union_eq_of_multiset_union_eq hu
  have hb : d.anchor ∈ d.first.val ↔ d.anchor ∈ e.first.val := by
    rw [← ha] at hbit
    exact decide_eq_decide.mp hbit
  have hp := pair_reconstruction inc d.first.property d.second.property
    e.first.property e.second.property hu d.anchor hb (fun f hfu hnr => by
      have hm := a.outside f hfu hnr
      have hn := b.outside f (hunion ▸ hfu) (by simpa only [← ha, ← hunion] using hnr)
      rw [hf] at hm
      exact hm.trans hn.symm)
  exact RawDemand.ext (Subtype.ext hp.1) (Subtype.ext hp.2) ha hc hfl

theorem finiteCode_recovers {d e : RawDemand inc} (a : DemandEncoding inc d)
    (b : DemandEncoding inc e) (h : a.finiteCode = b.finiteCode) : d = e := by
  simp only [finiteCode, tag, Prod.mk.injEq] at h
  obtain ⟨hf,hs,ha,hc,hfl,hbit,had,hdr⟩ := h
  apply code_recovers a b
  simp only [code, Prod.mk.injEq]
  exact ⟨hf,hs,ha,hc,hfl,hbit,
    padOccurrences_recovers a.added_card b.added_card had,
    padOccurrences_recovers a.dropped_card b.dropped_card hdr⟩

end DemandEncoding

end

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_IntervalPattern
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open scoped symmDiff

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}

lemma exchange_composition (M N S T : Finset E) :
    exchange (exchange M N S) (exchange N M S) T = exchange M N (S ∆ T) := by
  ext e
  simp only [mem_exchange, Finset.mem_symmDiff]
  tauto

lemma exchange_multiset (M N S : Finset E) :
    (exchange M N S).val + (exchange N M S).val = M.val + N.val := by
  apply Multiset.ext.mpr
  intro e
  have hc (s : Finset E) : Multiset.count e s.val = if e ∈ s then 1 else 0 :=
    Multiset.count_eq_of_nodup s.nodup
  simp only [Multiset.count_add, hc]
  by_cases hs : e ∈ S <;> by_cases hm : e ∈ M <;> by_cases hn : e ∈ N <;>
    simp [mem_exchange, hs, hm, hn]

lemma exchange_weight {R : Type*} [CommMonoid R] (w : E → R) (M N S : Finset E) :
    (∏ e ∈ exchange M N S, w e) * (∏ e ∈ exchange N M S, w e) =
      (∏ e ∈ M, w e) * (∏ e ∈ N, w e) := by
  have h := congrArg (fun U : Multiset E => (U.map w).prod) (exchange_multiset M N S)
  simpa only [Multiset.map_add, Multiset.prod_add, Finset.prod_eq_multiset_prod] using h

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Components
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.Transport.Sparse.decideOverlay _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq E] in
lemma componentEdges_subset (U : Finset E) (a : E) : componentEdges (inc := inc) U a ⊆ U := by
  intro e he
  exact ((mem_componentEdges U a e).mp he).1

omit [DecidableEq E] in
lemma componentEdges_eq {U : Finset E} {a b : E}
    (hab : (overlayLineGraph inc U).Reachable a b) :
    componentEdges (inc := inc) U a = componentEdges (inc := inc) U b := by
  ext e
  simp only [mem_componentEdges]
  exact and_congr_right (fun _ => ⟨fun h => hab.symm.trans h, fun h => hab.trans h⟩)

lemma component_subset {U S : Finset E} (hS : S ∈ components (inc := inc) U) : S ⊆ U := by
  obtain ⟨a,ha,rfl⟩ := mem_components.mp hS
  exact componentEdges_subset U a

lemma component_eq_of_shares {U S T : Finset E}
    (hS : S ∈ components (inc := inc) U) (hT : T ∈ components (inc := inc) U)
    {e f : E} (he : e ∈ S) (hf : f ∈ T) {v : V} (hev : inc e v) (hfv : inc f v) : S=T := by
  obtain ⟨a,ha,rfl⟩ := mem_components.mp hS
  obtain ⟨b,hb,rfl⟩ := mem_components.mp hT
  obtain ⟨heu,hra⟩ := (mem_componentEdges U a e).mp he
  obtain ⟨hfu,hrb⟩ := (mem_componentEdges U b f).mp hf
  exact componentEdges_eq ((hra.trans (shares_reachable heu hfu hev hfv)).trans hrb.symm)

lemma components_pairwise_disjoint (U : Finset E) :
    (components (inc := inc) U : Set (Finset E)).PairwiseDisjoint id := by
  intro S hS T hT hne
  apply Finset.disjoint_left.mpr
  intro e he hf
  apply hne
  obtain ⟨a,ha,rfl⟩ := mem_components.mp hS
  obtain ⟨b,hb,rfl⟩ := mem_components.mp hT
  obtain ⟨_,hra⟩ := (mem_componentEdges U a e).mp he
  obtain ⟨_,hrb⟩ := (mem_componentEdges U b e).mp hf
  exact componentEdges_eq (hra.trans hrb.symm)

lemma components_cover (U : Finset E) : (components (inc := inc) U).biUnion id = U := by
  classical
  ext e
  simp only [Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨S,hS,he⟩
    exact component_subset hS he
  · intro he
    exact ⟨componentEdges (inc := inc) U e, mem_components.mpr ⟨e,he,rfl⟩,
      componentEdges_self he⟩

lemma componentVertex_injective (hinc : ∀ e, ∃ v, inc e v) (U : Finset E) :
    Function.Injective (componentVertex hinc (U := U)) := by
  intro S T h
  obtain ⟨e,he,hev⟩ := (component_exists_vertex hinc S.property).choose_spec
  obtain ⟨f,hf,hfv⟩ := (component_exists_vertex hinc T.property).choose_spec
  apply Subtype.ext
  apply component_eq_of_shares S.property T.property he hf hev
  change inc f (componentVertex hinc T) at hfv
  change inc f (componentVertex hinc S)
  rwa [h]

lemma components_card_le [Fintype V] (hinc : ∀ e, ∃ v, inc e v) (U : Finset E) :
    (components (inc := inc) U).card ≤ Fintype.card V := by
  simpa only [Fintype.card_coe] using
    Fintype.card_le_of_injective (componentVertex hinc (U := U)) (componentVertex_injective hinc U)



namespace IndexedCycle

variable (c : IndexedCycle inc)

lemma edgeAt_mem_edgeSet (i : ℕ) : c.edgeAt i ∈ c.edgeSet := by
  apply (c.mem_edgeSet _).mpr
  exact ⟨i % c.size,Nat.mod_lt _ (by have := c.four_le; omega), c.edgeAt_mod i⟩

omit [DecidableEq E] in
lemma previous_indices (i : ℕ) (hi : i < c.size) :
    let j := (i+c.size-1) % c.size
    c.index (j+1) = c.index i := by
  dsimp only
  apply Fin.ext
  dsimp only [index]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have he : i + c.size - 1 + 1 = i + c.size := by have := c.four_le; omega
  rw [he, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod]

variable [Fintype V]

lemma edge_incident_cycle_mem {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) {e : E} (he : e ∈ M ∪ N)
    (i : ℕ) (hi : i < c.size) (hev : inc e (c.vertexAt i)) : e ∈ c.edgeSet := by
  let j := (i+c.size-1) % c.size
  have hj : j < c.size := Nat.mod_lt _ (by have := c.four_le; omega)
  have heq : c.edgeAt (j+1) = c.edgeAt i := congrArg c.edge (c.previous_indices i hi)
  have hvq : c.vertexAt (j+1) = c.vertexAt i := congrArg c.vertex (c.previous_indices i hi)
  have hji : c.edgeAt j ≠ c.edgeAt i := by rw [← heq]; exact c.consecutive_ne j hj
  have hiinc := (c.edgeAt_incidence i (c.vertexAt i)).mpr (Or.inl rfl)
  have hjinc : inc (c.edgeAt j) (c.vertexAt i) :=
    (c.edgeAt_incidence j _).mpr (Or.inr hvq.symm)
  have hcomp : c.edgeAt i ∈ M ↔ c.edgeAt j ∉ M := by
    rw [← heq]; exact c.adjacent_mem_complement hM hN hU j hj
  by_cases hjM : c.edgeAt j ∈ M
  · have hiN : c.edgeAt i ∈ N :=
      (Finset.mem_union.mp (hU i)).resolve_left (fun hiM => (hcomp.mp hiM) hjM)
    rcases Finset.mem_union.mp he with heM | heN
    · rw [hM.unique (Finset.mem_univ _) heM hev hjM hjinc]
      exact c.edgeAt_mem_edgeSet j
    · rw [hN.unique (Finset.mem_univ _) heN hev hiN hiinc]
      exact c.edgeAt_mem_edgeSet i
  · have hjN := (Finset.mem_union.mp (hU j)).resolve_left hjM
    have hiM := hcomp.mpr hjM
    rcases Finset.mem_union.mp he with heM | heN
    · rw [hM.unique (Finset.mem_univ _) heM hev hiM hiinc]
      exact c.edgeAt_mem_edgeSet i
    · rw [hN.unique (Finset.mem_univ _) heN hev hjN hjinc]
      exact c.edgeAt_mem_edgeSet j

lemma edgeSet_closed {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) {e f : E} (he : e ∈ c.edgeSet)
    (hef : (overlayLineGraph inc (M ∪ N)).Adj e f) : f ∈ c.edgeSet := by
  obtain ⟨i,hi,rfl⟩ := (c.mem_edgeSet e).mp he
  obtain ⟨_,_,hf,v,hev,hfv⟩ := hef
  rcases (c.edgeAt_incidence i v).mp hev with rfl | rfl
  · exact c.edge_incident_cycle_mem hM hN hU hf i hi hfv
  · have hi' : (i+1) % c.size < c.size := Nat.mod_lt _ (by have := c.four_le; omega)
    apply c.edge_incident_cycle_mem hM hN hU hf ((i+1)%c.size) hi'
    simpa only [c.vertexAt_mod] using hfv

lemma edgeSet_eq_component {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) :
    c.edgeSet = componentEdges (inc := inc) (M ∪ N) (c.edgeAt 0) := by
  ext e
  constructor
  · intro he
    obtain ⟨i,hi,rfl⟩ := (c.mem_edgeSet e).mp he
    exact (mem_componentEdges _ _ _).mpr ⟨hU i,c.edges_reachable _ hU i⟩
  · intro he
    obtain ⟨heu,hr⟩ := (mem_componentEdges _ _ _).mp he
    have hrel := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hr
    clear he heu hr
    induction hrel with
    | refl => exact c.edgeAt_mem_edgeSet 0
    | tail hpath hadj ih => exact c.edgeSet_closed hM hN hU ih hadj

lemma edgeSet_mem_components {M N : Finset E}
    (hM : MatchingOn inc M Finset.univ) (hN : MatchingOn inc N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) : c.edgeSet ∈ components (inc := inc) (M ∪ N) := by
  rw [c.edgeSet_eq_component hM hN hU]
  exact mem_components.mpr ⟨c.edgeAt 0,hU 0,rfl⟩

end IndexedCycle

end

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

namespace CellPaths

variable (c : CellPaths inc)

lemma mem_assemble_iff (M : Fin 4 → Finset E) (e : E) :
    e ∈ assemble M ↔ ∃ i, e ∈ M i := by
  simp only [assemble, Finset.mem_union]
  constructor
  · rintro ((h | h) | (h | h))
    · exact ⟨0,h⟩
    · exact ⟨2,h⟩
    · exact ⟨1,h⟩
    · exact ⟨3,h⟩
  · rintro ⟨i,hi⟩
    fin_cases i <;> tauto

lemma assemble_update (M : Fin 4 → Finset E)
    (hd : Pairwise fun i j => Disjoint (M i) (M j)) (i : Fin 4) (Q : Finset E) :
    assemble (Function.update M i Q) = (assemble M \ M i) ∪ Q := by
  ext e
  simp only [mem_assemble_iff, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro ⟨j,hj⟩
    by_cases hji : j = i
    · subst j
      exact Or.inr (by simpa using hj)
    · have hj' : e ∈ M j := by simpa [Function.update_of_ne hji] using hj
      exact Or.inl ⟨⟨j,hj'⟩, fun hi => Finset.disjoint_left.mp (hd hji) hj' hi⟩
  · rintro (⟨⟨j,hj⟩,hi⟩ | hq)
    · have hji : j ≠ i := by rintro rfl; exact hi hj
      exact ⟨j, by simpa [Function.update_of_ne hji] using hj⟩
    · exact ⟨i, by simpa using hq⟩

lemma conversion_pieces_matching (b : Bool) (S : Finset (Fin 4))
    (hS : ∀ i ∈ S, sideBit i = b) (i : Fin 4) :
    MatchingOn inc (c.conversionPieces b S i) (c.blocks b i) := by
  by_cases hi : i ∈ S
  · simp only [conversionPieces, ite_eq_left hi, blocks, ite_eq_left (hS i hi)]
    exact (c.side i).closed_matching _ (c.chord_incidence i)
  · simp only [conversionPieces, ite_eq_right hi]
    exact c.orientation_pieces_matching b i

lemma converted_empty (b : Bool) : c.converted b ∅ = c.orientation b := by
  unfold converted orientation
  congr 1

lemma conversion_pieces_insert (b : Bool) (S : Finset (Fin 4)) (i : Fin 4) :
    c.conversionPieces b (insert i S) =
      Function.update (c.conversionPieces b S) i ((c.side i).closed (c.chord i)) := by
  funext j
  by_cases hji : j = i
  · subst j; simp [conversionPieces]
  · simp [conversionPieces, hji]

lemma converted_insert (b : Bool) (S : Finset (Fin 4))
    (hS : ∀ j ∈ S, sideBit j = b) (i : Fin 4) (hi : sideBit i = b)
    (hni : i ∉ S) (hinc : ∀ e, ∃ v, inc e v) :
    c.converted b (insert i S) =
      (c.converted b S \ (c.side i).through) ∪ (c.side i).closed (c.chord i) := by
  rw [converted, c.conversion_pieces_insert]
  rw [assemble_update]
  · simp only [conversionPieces, ite_eq_right hni, orientationPieces, pieces, ite_eq_left hi, converted]
  · intro j k hjk
    exact (c.conversion_pieces_matching b S hS j).disjoint_edges
      (c.conversion_pieces_matching b S hS k) hinc (c.blocks_disjoint b hjk)

lemma converted_singleton (b : Bool) (i : Fin 4) (hi : sideBit i = b)
    (hinc : ∀ e, ∃ v, inc e v) :
    c.converted b {i} = c.contextOne b i := by
  have h := c.converted_insert b ∅ (by simp) i hi (by simp) hinc
  simpa only [converted_empty, Finset.insert_empty, contextOne] using h

lemma converted_pair (b : Bool) (X Y : Fin 4)
    (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y) :
    c.converted b {X,Y} = c.switched b := by
  unfold converted switched
  congr 1
  funext i
  have hh : i ∈ ({X,Y} : Finset (Fin 4)) ↔ sideBit i = b := by
    fin_cases X <;> fin_cases Y <;> fin_cases i <;> cases b <;>
      simp_all [sideBit]
  simp only [conversionPieces, hh, switchPieces, pieces, orientationPieces]
  split_ifs <;> rfl

lemma double_conversion (b : Bool) (X Y : Fin 4)
    (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.contextOne b Y \ (c.side X).through) ∪ (c.side X).closed (c.chord X) =
      c.switched b := by
  rw [← c.converted_singleton b Y hY hinc, ← c.converted_insert b {Y}
    (by intro i hi; have hi := Finset.mem_singleton.mp hi; subst i; exact hY) X hX
    (by simpa only [Finset.mem_singleton] using hne) hinc]
  exact c.converted_pair b X Y hX hY hne

lemma opposite_pair_identity (R : Finset E) (f : Finset E → ℝ) (b : Bool)
    (X Y : Fin 4) (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v) :
    f (R ∪ c.orientation b) - f (R ∪ c.switched b) =
      c.canonicalGain R f b Y + c.canonicalGain R f b X + c.contextError R f b X Y := by
  rw [contextError, c.double_conversion b X Y hX hY hne hinc]
  unfold canonicalGain
  ring

theorem single_cell_identity (R : Finset E) (f : Finset E → ℝ)
    (hinc : ∀ e, ∃ v, inc e v) :
    f (R ∪ c.orientation true) - f (R ∪ c.orientation false) =
      (f (R ∪ c.switched true) - f (R ∪ c.switched false)) +
      (c.canonicalGain R f true 0 + c.canonicalGain R f true 2) -
      (c.canonicalGain R f false 1 + c.canonicalGain R f false 3) +
      c.contextError R f true 2 0 - c.contextError R f false 3 1 := by
  have h₀ := c.opposite_pair_identity R f true 2 0 (by decide) (by decide) (by decide) hinc
  have h₁ := c.opposite_pair_identity R f false 3 1 (by decide) (by decide) (by decide) hinc
  linarith

end CellPaths

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Sewn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section
variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable {inc : E → V → Prop}

namespace CellPaths

variable (c : CellPaths inc)

lemma through_subset_contextOne (b : Bool) (X Y : Fin 4)
    (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v) :
    (c.side X).through ⊆ c.contextOne b Y := by
  have hd := (c.side X).through_matching.disjoint_edges (c.side Y).through_matching hinc
    (c.same_bit_spans X Y hne (hX.trans hY.symm))
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
    ⟨c.through_subset_orientation b X hX he,fun hy => Finset.disjoint_left.mp hd he hy⟩)

lemma contextOne_self (b : Bool) (i : Fin 4) (hi : sideBit i = b)
    (he : (c.side i).closed (c.chord i) = (c.side i).through) :
    c.contextOne b i = c.orientation b := by
  rw [contextOne,he,Finset.sdiff_union_of_subset (c.through_subset_orientation b i hi)]

lemma contextError_short_left (R : Finset E) (f : Finset E → ℝ) (b : Bool)
    (X Y : Fin 4) (hX : sideBit X = b) (hY : sideBit Y = b) (hne : X ≠ Y)
    (hinc : ∀ e, ∃ v, inc e v)
    (he : (c.side X).closed (c.chord X) = (c.side X).through) :
    c.contextError R f b X Y = 0 := by
  rw [contextError,he,Finset.sdiff_union_of_subset
    (c.through_subset_contextOne b X Y hX hY hne hinc),c.contextOne_self b X hX he]
  ring

lemma contextError_short_right (R : Finset E) (f : Finset E → ℝ) (b : Bool)
    (X Y : Fin 4) (hY : sideBit Y = b)
    (he : (c.side Y).closed (c.chord Y) = (c.side Y).through) :
    c.contextError R f b X Y = 0 := by
  rw [contextError,c.contextOne_self b Y hY he]
  simp only [contextOne,sub_self]

lemma contextError_derivative (R : Finset E) (f : Finset E → ℝ) (b : Bool)
    (X Y : Fin 4) (hdis : Disjoint R (c.side X).through) :
    c.contextError R f b X Y =
    (f (R ∪ c.contextOne b Y) -
      f (((R ∪ c.contextOne b Y) \ (c.side X).through) ∪ (c.side X).closed (c.chord X))) -
    (f (R ∪ c.orientation b) -
      f (((R ∪ c.orientation b) \ (c.side X).through) ∪ (c.side X).closed (c.chord X))) := by
  have h (S : Finset E) :
      ((R ∪ S) \ (c.side X).through) ∪ (c.side X).closed (c.chord X) =
        R ∪ ((S \ (c.side X).through) ∪ (c.side X).closed (c.chord X)) := by
    have hr : R \ (c.side X).through = R := by
      ext e
      simp only [Finset.mem_sdiff]
      exact ⟨And.left,fun he => ⟨he,fun hn => Finset.disjoint_left.mp hdis he hn⟩⟩
    rw [Finset.union_sdiff_distrib,hr,Finset.union_assoc]
  rw [h,h]
  rfl

end CellPaths

end

section

variable {V E : Type*}

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

lemma edgeAt_injective_range {i j : ℕ} (hi : i < c.size) (hj : j < c.size)
    (he : c.edgeAt i = c.edgeAt j) : i = j := by
  have hf := c.four_le
  have h₀ := (c.edgeAt_incidence j (c.vertexAt i)).mp
    (he ▸ (c.edgeAt_incidence i _).mpr (Or.inl rfl))
  have h₁ := (c.edgeAt_incidence j (c.vertexAt (i+1))).mp
    (he ▸ (c.edgeAt_incidence i _).mpr (Or.inr rfl))
  have hv : ∀ a b, c.vertexAt a = c.vertexAt b → a % c.size = b % c.size := by
    intro a b h
    exact congrArg Fin.val (c.simple h)
  rcases h₀ with h₀ | h₀
  · have hh := hv _ _ h₀
    simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hh
  · have hh₀ := hv _ _ h₀
    rcases h₁ with h₁ | h₁ <;> have hh₁ := hv _ _ h₁ <;>
      rw [Nat.mod_eq_of_lt hi, mod_of_lt_twice (by omega)] at hh₀ <;>
      rw [mod_of_lt_twice (by omega)] at hh₁
    · rw [Nat.mod_eq_of_lt hj] at hh₁
      split_ifs at hh₀ hh₁ <;> omega
    · rw [mod_of_lt_twice (by omega)] at hh₁
      split_ifs at hh₀ hh₁ <;> omega

lemma edgeAt_eq_iff {a x y : ℕ} (ha : a < c.size)
    (hx : a ≤ x ∧ x < a+c.size) (hy : a ≤ y ∧ y < a+c.size) :
    c.edgeAt x = c.edgeAt y ↔ x = y := by
  constructor
  · intro he
    have hh := c.edgeAt_injective_range
      (Nat.mod_lt x (by have := c.four_le; omega))
      (Nat.mod_lt y (by have := c.four_le; omega))
      (by simpa only [c.edgeAt_mod] using he)
    rw [mod_of_lt_twice (by omega), mod_of_lt_twice (by omega)] at hh
    split_ifs at hh <;> omega
  · exact congrArg c.edgeAt

variable [DecidableEq E]

lemma intervalPattern_disjoint {x y z : ℕ} (hx : x < c.size)
    (hxy : x ≤ y) (hyz : y ≤ z) (hz : z ≤ x+c.size) (a b : ℕ) :
    Disjoint (c.intervalPattern x y a) (c.intervalPattern y z b) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,hi,hj,_,he⟩ := (c.mem_intervalPattern e _ _ _).mp he
  obtain ⟨j,hk,hl,_,hf⟩ := (c.mem_intervalPattern e _ _ _).mp hf
  have hh := (c.edgeAt_eq_iff hx ⟨hi,by omega⟩ ⟨by omega,by omega⟩).mp (he.trans hf.symm)
  omega

lemma parity_sdiff_interval {x y : ℕ} (hx : x < c.size)
    (hxy : x ≤ y) (hy : y ≤ x+c.size) (a : ℕ) :
    c.parityPattern a \ c.intervalPattern x y a = c.intervalPattern y (x+c.size) a := by
  have hu := c.intervalPattern_union hxy hy a
  rw [c.rotatedPattern (by omega) a] at hu
  rw [← hu]
  have hd := c.intervalPattern_disjoint hx hxy hy (by omega) a a
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_union]
  have hh : ¬ (e ∈ c.intervalPattern x y a ∧ e ∈ c.intervalPattern y (x+c.size) a) := by
    rintro ⟨h,h'⟩
    exact Finset.disjoint_left.mp hd h h'
  tauto

lemma forward_conversion {x y : ℕ} (hx : x < c.size) (hxy : x < y)
    (hy : y < c.size) (ho : (y-x)%2=1) (e : E) :
    (c.parityPattern (x%2) \ (c.arc x (y-x) hx (by omega) (by omega) ho).through) ∪
      (c.arc x (y-x) hx (by omega) (by omega) ho).closed e = c.sewn x y e := by
  rw [OddPath.closed, c.arc_through, c.arc_interior]
  have he : x+(y-x)=y := by omega
  rw [he, c.parity_sdiff_interval hx (by omega) (by omega)]
  unfold sewn
  ext z
  simp only [Finset.mem_union]
  tauto

lemma complementary_conversion {x y : ℕ} (_hx : x < c.size) (hxy : x < y)
    (hy : y < c.size) (ho : (y-x)%2=1) (e : E) :
    (c.parityPattern (y%2) \
      (c.arc y (c.size+x-y) hy (by omega) (by omega) (by have := c.even; omega)).through) ∪
      (c.arc y (c.size+x-y) hy (by omega) (by omega) (by have := c.even; omega)).closed e =
      c.sewn x y e := by
  have hev := c.even
  have hp : y%2=1-x%2 := by omega
  have hp' : 1-y%2=x%2 := by omega
  have he : y+(c.size+x-y)=x+c.size := by omega
  rw [OddPath.closed, c.arc_through, c.arc_interior, he,
    c.parity_sdiff_interval hy (by omega) (by omega)]
  have hshift : c.intervalPattern (x+c.size) (y+c.size) (y%2) =
      c.intervalPattern x y (y%2) := c.intervalPattern_periodic _
  rw [hshift, hp', hp]
  unfold sewn
  ext z
  simp only [Finset.mem_union]
  tauto

lemma edgeAt_mem_parity (i : ℕ) : c.edgeAt i ∈ c.parityPattern (i%2) := by
  rw [parityPattern, c.mem_intervalPattern]
  have hdiv : 2 ∣ c.size := Nat.dvd_of_mod_eq_zero c.even
  exact ⟨i%c.size,by omega,Nat.mod_lt _ (by have := c.four_le; omega),
    Nat.mod_mod_of_dvd i hdiv,c.edgeAt_mod i⟩

lemma short_through (x : ℕ) (hx : x < c.size) :
    (c.arc x 1 hx (by omega) (by have := c.four_le; omega) (by omega)).through =
      {c.edgeAt x} := by
  norm_num [OddPath.through, pathPattern, arc]
  rw [show ({i ∈ ({0} : Finset ℕ) | i % 2 = 0}) = {0} by decide]
  simp

lemma short_closed (x : ℕ) (hx : x < c.size) :
    (c.arc x 1 hx (by omega) (by have := c.four_le; omega) (by omega)).closed (c.edgeAt x) =
      {c.edgeAt x} := by
  simp [OddPath.closed, OddPath.interior, pathPattern, arc]

lemma sewn_short (x : ℕ) (hx : x+1 < c.size) :
    c.sewn x (x+1) (c.edgeAt x) = c.parityPattern (x%2) := by
  have hh := c.forward_conversion (x := x) (y := x+1) (by omega) (by omega) hx (by omega) (c.edgeAt x)
  have ord : x+1-x=1 := by omega
  simp only [ord] at hh
  rw [c.short_through, c.short_closed] at hh
  rw [← hh]
  have hm : {c.edgeAt x} ⊆ c.parityPattern (x%2) := by
    simpa only [Finset.singleton_subset_iff] using c.edgeAt_mem_parity x
  exact Finset.sdiff_union_of_subset hm

lemma sewn_root : c.sewn 0 (c.size-1) (c.edgeAt (c.size-1)) = c.parityPattern 1 := by
  have hf := c.four_le
  have hev := c.even
  have hh := c.complementary_conversion (x := 0) (y := c.size-1) (by omega) (by omega)
    (by omega) (by omega) (c.edgeAt (c.size-1))
  have he : c.size+0-(c.size-1)=1 := by omega
  have hp : (c.size-1)%2=1 := by omega
  simp only [he, hp] at hh
  rw [c.short_through, c.short_closed] at hh
  rw [← hh]
  have hm : {c.edgeAt (c.size-1)} ⊆ c.parityPattern 1 := by
    simpa only [Finset.singleton_subset_iff, hp] using c.edgeAt_mem_parity (c.size-1)
  exact Finset.sdiff_union_of_subset hm

end IndexedCycle

end

variable {V E : Type*} [DecidableEq E]

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

lemma signedGain_short (R : Finset E) (f : Finset E → ℝ) (x : ℕ) (hx : x+1 < c.size) :
    c.signedGain R f x (x+1) (c.edgeAt x) = 0 := by
  unfold signedGain
  rw [c.sewn_short x hx]
  split_ifs with h
  · simp [h]
  · have hh : x%2=1 := by omega
    simp [hh]

lemma signedGain_root (R : Finset E) (f : Finset E → ℝ) :
    c.signedGain R f 0 (c.size-1) (c.edgeAt (c.size-1)) =
      f (R ∪ c.parityPattern 0) - f (R ∪ c.parityPattern 1) := by
  simp [signedGain, c.sewn_root]

namespace Corners

variable {c} (k : c.Corners)

variable [DecidableEq V]

lemma context_eq_sewn (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (i : Fin 4) :
    (k.cellPaths chord hc).contextOne (CellPaths.sideBit i) i = k.cornerSewn chord i := by
  have eh := k.cell_orientation_parity chord hc (CellPaths.sideBit i)
  rw [← k.parity_start i] at eh
  change ((k.cellPaths chord hc).orientation (CellPaths.sideBit i) \ (k.side i).through) ∪
    (k.side i).closed (chord i) = _
  rw [eh]
  have h₀ := k.lt₀
  have h₁ := k.lt₁
  have h₂ := k.lt₂
  have h₃ := k.lt₃
  fin_cases i
  · exact c.forward_conversion (by omega) h₀ (by omega) k.odd₀ _
  · exact c.forward_conversion (by omega) h₁ (by omega) k.odd₁ _
  · exact c.forward_conversion (by omega) h₂ h₃ k.odd₂ _
  · exact c.complementary_conversion (by omega) (by omega) h₃
      (by have := k.odd₀; have := k.odd₁; have := k.odd₂; omega) _

theorem signed_cell_recurrence (chord : Fin 4 → E)
    (hc : ∀ i v, inc (chord i) v ↔
      v = (k.side i).vertex 0 ∨ v = (k.side i).vertex (k.side i).length)
    (R : Finset E) (f : Finset E → ℝ) (hinc : ∀ e, ∃ v, inc e v) :
    c.signedGain R f k.a₀ k.a₃ (chord 3) =
      k.signedLocalTerm chord hc R f +
      c.signedGain R f k.a₀ k.a₁ (chord 0) +
      c.signedGain R f k.a₁ k.a₂ (chord 1) +
      c.signedGain R f k.a₂ k.a₃ (chord 2) := by
  have hh := (k.cellPaths chord hc).single_cell_identity R f hinc
  have hc₀ := k.context_eq_sewn chord hc 0
  have hc₁ := k.context_eq_sewn chord hc 1
  have hc₂ := k.context_eq_sewn chord hc 2
  have hc₃ := k.context_eq_sewn chord hc 3
  norm_num [CellPaths.sideBit, Fin.isValue, cornerSewn, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons, Matrix.tail_cons] at hc₀ hc₁ hc₂ hc₃
  change (k.cellPaths chord hc).contextOne true 2 = c.sewn k.a₂ k.a₃ (chord 2) at hc₂
  change (k.cellPaths chord hc).contextOne false 3 = c.sewn k.a₀ k.a₃ (chord 3) at hc₃
  unfold CellPaths.canonicalGain at hh
  rw [hc₀, hc₁, hc₂, hc₃, k.cell_orientation_parity chord hc true,
    k.cell_orientation_parity chord hc false] at hh
  simp only [ite_true, Bool.false_eq_true, ite_false] at hh
  have ho₀ := k.odd₀
  have ho₁ := k.odd₁
  have hl₀ := k.lt₀
  have hl₁ := k.lt₁
  by_cases h : k.a₀%2=0
  · have h₁ : k.a₁%2=1 := by omega
    have h₂ : k.a₂%2=0 := by omega
    simp only [signedGain, signedLocalTerm, h, h₁, h₂,
      Nat.one_ne_zero, Nat.sub_zero, ite_true, ite_false] at hh ⊢
    linarith
  · have h₀ : k.a₀%2=1 := by omega
    have h₁ : k.a₁%2=0 := by omega
    have h₂ : k.a₂%2=1 := by omega
    simp only [signedGain, signedLocalTerm, h₀, h₁, h₂,
      Nat.one_ne_zero, Nat.sub_self, ite_true, ite_false] at hh ⊢
    linarith

end Corners

end IndexedCycle

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Cells.CycleData.Subdivision

variable {L : Type*} [DecidableEq L] {G : SimpleGraph L} {m : ℕ} {C : CycleData G m} {x y : ℕ}

lemma signed_cancellation_bounded (Q : Subdivision C x y)
    (gain : ℕ → ℕ → ℝ) (localTerm : ℕ → ℕ → ℕ → ℕ → ℝ)
    (hshort : ∀ x, x + 1 < m → gain x (x+1)=0)
    (hcell : ∀ x p q y, C.Cell x p q y → y < m →
      gain x y = localTerm x p q y + gain x p + gain p q + gain q y)
    (hy : y < m) : gain x y = Q.sumCells localTerm := by
  induction Q with
  | edge h => simpa only [h, sumCells] using hshort _ (by omega)
  | node cell Q₁ Q₂ Q₃ h₁ h₂ h₃ =>
    have hpq := cell.middle_pos
    have hqy := cell.third_pos
    simpa only [sumCells, h₁ (by omega), h₂ (by omega), h₃ hy]
      using hcell _ _ _ _ cell hy

end MatchingFPRAS.Cells.CycleData.Subdivision

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_ChosenChord
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.Transport.instFintypePM _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] [Fintype L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

omit [Fintype V] [DecidableEq V] [Fintype L] in
lemma chosenChord_eq (x y : ℕ) (hxy : x < y) (hy : y < c.size)
    (ha : (c.labelCycle hbags).Admissible x y) :
    c.chosenChord hbags x y = c.chord hbags x y hxy hy ha := by
  unfold chosenChord
  rw [dite_eq_left (show x < y ∧ y < c.size ∧ (c.labelCycle hbags).Admissible x y from ⟨hxy,hy,ha⟩)]

omit [Fintype V] [Fintype L] in
lemma diagramGain_short (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x : ℕ) (hx : x + 1 < c.size) : c.diagramGain hbags R f x (x+1)=0 := by
  have ha : (c.labelCycle hbags).Admissible x (x+1) := by
    refine ⟨(c.edgeAt x).color, (c.edge_color_fixed hbags x).1, ?_⟩
    simpa only [Nat.cast_add, Nat.cast_one] using (c.edge_color_fixed hbags x).2
  unfold diagramGain
  rw [c.chosenChord_eq hbags x (x+1) (by omega) hx ha,
    c.chord_short hbags _ _ _ _ _ rfl]
  exact c.signedGain_short R f x hx

omit [Fintype V] [Fintype L] in
lemma diagramGain_root (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ) :
    c.diagramGain hbags R f 0 (c.size-1) =
      f (R ∪ c.parityPattern 0) - f (R ∪ c.parityPattern 1) := by
  have hm := c.four_le
  have ha : (c.labelCycle hbags).Admissible 0 (c.size-1) := by
    refine ⟨(c.edgeAt (c.size-1)).color, ?_, (c.edge_color_fixed hbags (c.size-1)).1⟩
    have hh := (c.edge_color_fixed hbags (c.size-1)).2
    have he : ((c.size-1 : ℕ) : ℤ)+1 = (0 : ℤ)+c.size := by omega
    rw [he, c.labelSets_periodic hbags] at hh
    simpa only [Nat.cast_zero] using hh
  unfold diagramGain
  rw [c.chosenChord_eq hbags 0 (c.size-1) (by omega) (by omega) ha,
    c.chord_wrap hbags _ _ _ _ _ ⟨rfl,by omega⟩]
  exact c.signedGain_root R f

omit [Fintype V] [Fintype L] in
lemma diagram_cell_recurrence (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (x p q y : ℕ) (hc : (c.labelCycle hbags).Cell x p q y) (hy : y < c.size) :
    c.diagramGain hbags R f x y = c.diagramTerm hbags R f x p q y +
      c.diagramGain hbags R f x p + c.diagramGain hbags R f p q +
      c.diagramGain hbags R f q y := by
  have hxp := hc.first_pos
  have hpq := hc.middle_pos
  have hqy := hc.third_pos
  have he : (c.labelCycle hbags).Admissible x y := by
    obtain ⟨l,hl₁,hl₂⟩ := hc.exterior
    exact ⟨l,hl₂,hl₁⟩
  unfold diagramGain diagramTerm
  rw [dite_eq_left ⟨hc,hy⟩,
    c.chosenChord_eq hbags x y (by omega) hy he,
    c.chosenChord_eq hbags x p hxp (by omega) hc.first,
    c.chosenChord_eq hbags p q hpq (by omega) hc.middle,
    c.chosenChord_eq hbags q y hqy hy hc.third]
  exact (c.cellCorners hbags hc hy).signed_cell_recurrence
    (c.cellChords hbags hc hy) (c.cellChords_incidence hbags hc hy) R f
    BagEdge.exists_incident

omit [Fintype V] [Fintype L] in
theorem sum_cells_identity (R : Finset (BagEdge bags)) (f : Finset (BagEdge bags) → ℝ)
    (Q : MatchingFPRAS.Cells.CycleData.Subdivision (c.labelCycle hbags) 0 (c.size-1)) :
    f (R ∪ c.parityPattern 0) - f (R ∪ c.parityPattern 1) =
      Q.sumCells (c.diagramTerm hbags R f) := by
  rw [← c.diagramGain_root hbags R f]
  exact Q.signed_cancellation_bounded (c.diagramGain hbags R f) (c.diagramTerm hbags R f)
    (c.diagramGain_short hbags R f) (c.diagram_cell_recurrence hbags R f)
    (by have := c.four_le; omega)

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Cells.CycleData

variable {L : Type*} [DecidableEq L] {G : SimpleGraph L} {m : ℕ} {C : CycleData G m}

namespace Subdivision

variable {x y : ℕ}

lemma cellList_length (Q : Subdivision C x y) : Q.cellList.length = Q.cells := by
  induction Q with
  | edge h => rfl
  | node h _ _ _ ih₁ ih₂ ih₃ => simp only [cellList, List.length_cons,
      List.length_append, cells, ih₁, ih₂, ih₃]; omega

lemma cellList_separated {x₁ y₁ x₂ y₂ : ℕ} (Q₁ : Subdivision C x₁ y₁)
    (Q₂ : Subdivision C x₂ y₂) (h : y₁ ≤ x₂) :
    ∀ a ∈ Q₁.cellList, ∀ b ∈ Q₂.cellList, a ≠ b := by
  intro a ha b hb hab
  subst b
  obtain ⟨_,hy,hc⟩ := mem_cellList ha
  obtain ⟨hx,_,_⟩ := mem_cellList hb
  have := hc.first_pos
  have := hc.middle_pos
  have := hc.third_pos
  omega

lemma cellList_nodup (Q : Subdivision C x y) : Q.cellList.Nodup := by
  induction Q with
  | edge h => simp [cellList]
  | @node x p q y h Q₁ Q₂ Q₃ ih₁ ih₂ ih₃ =>
    rw [cellList, List.nodup_cons]
    refine ⟨?_, List.nodup_append.mpr ⟨List.nodup_append.mpr ⟨ih₁, ih₂,
      cellList_separated Q₁ Q₂ le_rfl⟩, ih₃, ?_⟩⟩
    · intro ha
      simp only [List.mem_append] at ha
      rcases ha with (ha | ha) | ha
      · have hh := (mem_cellList ha).2.1
        have := h.middle_pos
        have := h.third_pos
        simp only at hh
        omega
      · have hh := (mem_cellList ha).1
        have := h.first_pos
        simp only at hh
        omega
      · have hh := (mem_cellList ha).1
        have := h.first_pos
        have := h.middle_pos
        simp only at hh
        omega
    · intro a ha b hb
      rcases List.mem_append.mp ha with ha | ha
      · exact cellList_separated Q₁ Q₃ (le_of_lt h.middle_pos) a ha b hb
      · exact cellList_separated Q₂ Q₃ le_rfl a ha b hb

lemma cellSet_card (Q : Subdivision C x y) : Q.cellSet.card = Q.cells := by
  rw [cellSet, List.toFinset_card_of_nodup Q.cellList_nodup, Q.cellList_length]

lemma sumCells_eq_sum (Q : Subdivision C x y) (f : ℕ → ℕ → ℕ → ℕ → ℝ) :
    Q.sumCells f = ∑ a ∈ Q.cellSet, f a.x a.p a.q a.y := by
  rw [cellSet, List.sum_toFinset _ Q.cellList_nodup]
  induction Q with
  | edge h => rfl
  | node h _ _ _ ih₁ ih₂ ih₃ =>
    simp only [sumCells, cellList, List.map_cons, List.map_append, List.sum_cons,
      List.sum_append, ih₁, ih₂, ih₃]
    ring

end Subdivision

end MatchingFPRAS.Cells.CycleData

namespace MatchingFPRAS.Transport.IndexedCycle

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] [Fintype L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

omit [Fintype V] [Fintype L] in
lemma diagramEnergy_nonneg (R : Finset (BagEdge bags))
    (f : Finset (BagEdge bags) → ℝ) (x p q y : ℕ) :
    0 ≤ c.diagramEnergy hbags R f x p q y := by
  unfold diagramEnergy
  split_ifs <;> positivity

omit [Fintype V] [Fintype L] in
lemma diagramTerm_sq_le (R : Finset (BagEdge bags))
    (f : Finset (BagEdge bags) → ℝ) (x p q y : ℕ) :
    (c.diagramTerm hbags R f x p q y)^2 ≤ 3 * c.diagramEnergy hbags R f x p q y := by
  classical
  by_cases h : (c.labelCycle hbags).Cell x p q y ∧ y < c.size
  · simp only [diagramTerm, diagramEnergy, dite_eq_left h]
    let P := c.pathsOfCell hbags h.1 h.2
    let a := f (R ∪ P.switched true) - f (R ∪ P.switched false)
    let b := P.contextError R f true 2 0
    let d := P.contextError R f false 3 1
    change (if x%2=0 then a+b-d else -(a+b-d))^2 ≤ 3*(a^2+b^2+d^2)
    split_ifs <;> nlinarith [sq_nonneg (a-b), sq_nonneg (a+d), sq_nonneg (b+d)]
  · simp only [diagramTerm, diagramEnergy, dite_eq_right h, zero_pow (by decide : 2≠0), mul_zero,
      le_refl]

omit [Fintype L] in
theorem cycle_cell_square_bound (R : Finset (BagEdge bags))
    (f : Finset (BagEdge bags) → ℝ)
    (Q : MatchingFPRAS.Cells.CycleData.Subdivision (c.labelCycle hbags) 0 (c.size-1)) :
    (f (R ∪ c.parityPattern 0) - f (R ∪ c.parityPattern 1))^2 ≤
      3 * (Fintype.card V : ℝ) *
        ∑ a ∈ Q.cellSet, c.diagramEnergy hbags R f a.x a.p a.q a.y := by
  classical
  let t := fun a : MatchingFPRAS.Cells.CycleData.CellIndex =>
    c.diagramTerm hbags R f a.x a.p a.q a.y
  let e := fun a : MatchingFPRAS.Cells.CycleData.CellIndex =>
    c.diagramEnergy hbags R f a.x a.p a.q a.y
  have hsum : 0 ≤ ∑ a ∈ Q.cellSet, e a :=
    Finset.sum_nonneg (fun a _ => c.diagramEnergy_nonneg hbags R f a.x a.p a.q a.y)
  have hsize : c.size ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective c.vertex c.simple
  have hcells : (Q.cellSet.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    apply Nat.cast_le.mpr
    rw [Q.cellSet_card]
    have := Q.cells_length
    omega
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Q.cellSet t (fun _ => (1:ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have he : ∑ a ∈ Q.cellSet, (t a)^2 ≤ 3 * ∑ a ∈ Q.cellSet, e a := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun a _ => c.diagramTerm_sq_le hbags R f a.x a.p a.q a.y)
  rw [c.sum_cells_identity hbags R f Q, Q.sumCells_eq_sum]
  change (∑ a ∈ Q.cellSet, t a)^2 ≤ 3 * (Fintype.card V : ℝ) * ∑ a ∈ Q.cellSet, e a
  calc
    _ ≤ (∑ a ∈ Q.cellSet, t a^2) * (Q.cellSet.card : ℝ) := hcs
    _ ≤ (3 * ∑ a ∈ Q.cellSet, e a) * (Q.cellSet.card : ℝ) :=
      mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)
    _ ≤ (3 * ∑ a ∈ Q.cellSet, e a) * (Fintype.card V : ℝ) :=
      mul_le_mul_of_nonneg_left hcells (mul_nonneg (by norm_num) hsum)
    _ = _ := by ring

end

variable {V L : Type*} [Fintype V] [DecidableEq V] [DecidableEq L] [Fintype L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

omit [Fintype L] in
theorem exchange_cell_square_bound {M N : Finset (BagEdge bags)}
    (hM : MatchingOn BagEdge.Incident M Finset.univ)
    (hN : MatchingOn BagEdge.Incident N Finset.univ)
    (hU : ∀ i, c.edgeAt i ∈ M ∪ N) (hG : G.IsAcyclic)
    (f : Finset (BagEdge bags) → ℝ) :
    (f M - f (exchange M N c.edgeSet))^2 ≤
      3 * (Fintype.card V : ℝ) *
        ∑ a ∈ (c.subdivision hbags hG).cellSet,
          c.diagramEnergy hbags (M \ c.edgeSet) f a.x a.p a.q a.y := by
  classical
  have hU' : ∀ i, c.edgeAt i ∈ N ∪ M := by simpa only [Finset.union_comm] using hU
  have hpat := c.inter_edgeSet_parity hM hN hU
  have hpat' := c.inter_edgeSet_parity hN hM hU'
  have hcomp := c.cycle_edge_mem_complement hM hN hU 0
  have hMsplit : M = (M \ c.edgeSet) ∪ M ∩ c.edgeSet := by
    ext e
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  have hX : exchange M N c.edgeSet = (M \ c.edgeSet) ∪ N ∩ c.edgeSet := rfl
  rw [hpat] at hMsplit
  rw [hpat'] at hX
  have hb := c.cycle_cell_square_bound hbags (M \ c.edgeSet) f (c.subdivision hbags hG)
  by_cases he : c.edgeAt 0 ∈ M
  · have hn : c.edgeAt 0 ∉ N := fun hn => (hcomp.mp hn) he
    simp only [ite_eq_left he,ite_eq_right hn] at hMsplit hX
    calc
      _ = (f ((M \ c.edgeSet) ∪ c.parityPattern 0) -
          f ((M \ c.edgeSet) ∪ c.parityPattern 1))^2 := by rw [← hMsplit,← hX]
      _ ≤ _ := hb
  · have hn : c.edgeAt 0 ∈ N := by tauto
    simp only [ite_eq_right he,ite_eq_left hn] at hMsplit hX
    calc
      _ = (f ((M \ c.edgeSet) ∪ c.parityPattern 1) -
          f ((M \ c.edgeSet) ∪ c.parityPattern 0))^2 := by rw [← hMsplit,← hX]
      _ = (f ((M \ c.edgeSet) ∪ c.parityPattern 0) -
          f ((M \ c.edgeSet) ∪ c.parityPattern 1))^2 := by ring
      _ ≤ _ := hb

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

namespace LongComponent

variable {p : PM inc × PM inc} (S : LongComponent p)

omit [DecidableEq V] [Fintype E] in
lemma cycle_set : S.cycle.edgeSet = S.val := S.property.choose_spec.1

omit [DecidableEq V] [Fintype E] in
lemma anchor_recovers {T : LongComponent p} (h : S.cycle.edgeAt 0 = T.cycle.edgeAt 0) : S = T := by
  apply Subtype.ext
  rw [← S.cycle_set,← T.cycle_set,S.cycle.edgeSet_eq_component p.1.property p.2.property S.cycle_union,
    T.cycle.edgeSet_eq_component p.1.property p.2.property T.cycle_union,h]

end LongComponent

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Cycle
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.Transport.instFintypePM _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.CellDemands
variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]
variable {bags : V → Finset L}
variable {G : SimpleGraph L}
variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
variable (hG : G.IsAcyclic)
namespace Demand

variable {hbags hG} (d : Demand hbags hG)

omit [Fintype L] in
theorem raw_injective (flags : Fin 64) : Function.Injective (fun d : Demand hbags hG => d.raw flags) := by
  intro d e h
  obtain ⟨p,S,a⟩ := d
  obtain ⟨q,T,b⟩ := e
  have heq : p = q := by
    apply Prod.ext
    · exact congrArg RawDemand.first h
    · exact congrArg RawDemand.second h
  subst q
  have hanc : S.cycle.edgeAt 0 = T.cycle.edgeAt 0 := congrArg RawDemand.anchor h
  have hST : S = T := S.anchor_recovers hanc
  subst T
  have hcorn := congrArg RawDemand.corners h
  have ha := ((S.cycle.subdivision hbags hG).mem_cellList (List.mem_toFinset.mp a.property))
  have hb := ((S.cycle.subdivision hbags hG).mem_cellList (List.mem_toFinset.mp b.property))
  have hsize := S.cycle.four_le
  have hax := ha.2.2.first_pos
  have hap := ha.2.2.middle_pos
  have haq := ha.2.2.third_pos
  have hbx := hb.2.2.first_pos
  have hbp := hb.2.2.middle_pos
  have hbq := hb.2.2.third_pos
  have hidx (i : Fin 4) := congrFun hcorn i
  have hpos : 0 < S.cycle.size := by omega
  have hinj {i j : ℕ} (hi : i < S.cycle.size) (hj : j < S.cycle.size)
      (hh : S.cycle.vertexAt i = S.cycle.vertexAt j) : i = j :=
    (S.cycle.vertexAt_eq_iff hpos ⟨by omega,by omega⟩ ⟨by omega,by omega⟩).mp hh
  have hab : a = b := by
    apply Subtype.ext
    apply MatchingFPRAS.Cells.CycleData.CellIndex.ext
    · apply hinj (by omega) (by omega)
      exact hidx 0
    · apply hinj (by omega) (by omega)
      exact hidx 1
    · apply hinj (by omega) (by omega)
      exact hidx 2
    · apply hinj (by omega) (by omega)
      exact hidx 3
  subst b
  rfl

end Demand

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

omit [Fintype V] [DecidableEq V] in
lemma OddPath.closed_eq_through_of_short (p : OddPath inc) (chord : E)
    (hl : p.length = 1) (he : chord = p.edge 0) : p.closed chord = p.through := by
  simp [OddPath.closed,OddPath.through,OddPath.interior,pathPattern,hl,he,Finset.filter_singleton]

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} (c : IndexedCycle (BagEdge.Incident (bags := bags)))

variable {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

omit [Fintype V] [Fintype L] in
lemma cellShort_chord {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) (hl : ((c.pathsOfCell hbags hc hy).side i).length = 1) :
    (c.pathsOfCell hbags hc hy).chord i = ((c.pathsOfCell hbags hc hy).side i).edge 0 := by
  have hxp := hc.first_pos
  have hpq := hc.middle_pos
  have hqy := hc.third_pos
  change (c.cellChords hbags hc hy) i = ((c.cellCorners hbags hc hy).side i).edge 0
  change (c.cellCorners hbags hc hy).length i = 1 at hl
  fin_cases i
  · simp only [Corners.length,Corners.start,Corners.stop,cellCorners] at hl
    have h : p = x+1 := by simp at hl; omega
    simpa [cellChords,Corners.side,arc,Corners.start,cellCorners] using c.chord_short hbags x p _ _ hc.first h
  · simp only [Corners.length,Corners.start,Corners.stop,cellCorners] at hl
    have h : q = p+1 := by simp at hl; omega
    simpa [cellChords,Corners.side,arc,Corners.start,cellCorners] using c.chord_short hbags p q _ _ hc.middle h
  · simp only [Corners.length,Corners.start,Corners.stop,cellCorners] at hl
    have h : y = q+1 := by simp at hl; omega
    simpa [cellChords,Corners.side,arc,Corners.start,cellCorners] using c.chord_short hbags q y _ _ hc.third h
  · simp only [Corners.length,Corners.start,Corners.stop,cellCorners] at hl
    have h : x = 0 ∧ y+1=c.size := by simp at hl; omega
    simpa [cellChords,Corners.side,arc,Corners.start,cellCorners] using c.chord_wrap hbags x y _ _ _ h

omit [Fintype V] [Fintype L] in
lemma cellShort_pattern {x p q y : ℕ} (hc : (c.labelCycle hbags).Cell x p q y)
    (hy : y < c.size) (i : Fin 4) (hl : ((c.pathsOfCell hbags hc hy).side i).length = 1) :
    ((c.pathsOfCell hbags hc hy).side i).closed ((c.pathsOfCell hbags hc hy).chord i) =
      ((c.pathsOfCell hbags hc hy).side i).through :=
  OddPath.closed_eq_through_of_short _ _ hl (c.cellShort_chord hbags hc hy i hl)

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace ErrorDemand

variable (e : ErrorDemand hbags hG)

omit [Fintype L] in
lemma raw_injective : Function.Injective (raw (hbags := hbags) (hG := hG)) := by
  intro e f h
  have hf : e.flags = f.flags := congrArg RawDemand.flags h
  have hb : e.bit = f.bit := by
    cases he : e.bit <;> cases hh : f.bit <;> simp_all [flags]
  have hd : e.demand = f.demand := by
    apply Demand.raw_injective e.flags
    simpa only [raw,hf] using h
  apply Subtype.ext
  exact Prod.ext hb hd

end ErrorDemand

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

namespace Demand

variable (d : Demand hbags hG)

attribute [local instance] OAI.MatchingFPRAS.Transport.CellDemands.instFintypeBagEdge_1
lemma switchChoice_spec :
    (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).first.val =
      d.outside ∪ d.paths.switched true ∧
    gibbs (fun e => max lo (min hi (w e))) d.1.1 * gibbs (fun e => max lo (min hi (w e))) d.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e)))
        (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).first *
        gibbs (fun e => max lo (min hi (w e)))
        (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).second :=
  (d.exists_switch height hheight hstep D hD w hw lo hi hlo hlohi).choose_spec

lemma switchChoice_injective : Function.Injective (fun d : Demand hbags hG =>
    (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).finiteCode) := by
  intro d e h
  exact Demand.raw_injective 0 (DemandEncoding.finiteCode_recovers _ _ h)

end Demand

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

namespace IndexedCycle

variable (c : IndexedCycle inc)

omit [Fintype V] [DecidableEq V] in
lemma edgeSet_eq_parity_union : c.edgeSet = c.parityPattern 0 ∪ c.parityPattern 1 := by
  ext e
  simp only [mem_edgeSet,parityPattern,mem_intervalPattern,Finset.mem_union]
  constructor
  · rintro ⟨i,hi,he⟩
    have hp : i % 2 = 0 ∨ i % 2 = 1 := by omega
    rcases hp with hp | hp
    · exact Or.inl ⟨i,by omega,hi,hp,he⟩
    · exact Or.inr ⟨i,by omega,hi,hp,he⟩
  · rintro (⟨i,_,hi,_,he⟩ | ⟨i,_,hi,_,he⟩) <;> exact ⟨i,hi,he⟩

omit [Fintype V] [DecidableEq V] in
lemma zero_mem_parity : c.edgeAt 0 ∈ c.parityPattern 0 := by
  apply (c.mem_intervalPattern _ _ _ _).mpr
  exact ⟨0,le_rfl,by have := c.four_le; omega,rfl,rfl⟩

end IndexedCycle

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Through
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]
variable {inc : E → V → Prop}
namespace PatternCode

variable (x : PatternCode inc)

omit [DecidableEq V] in
lemma activated {A B : Finset E}
    (hA : MatchingOn inc A Finset.univ) (hB : MatchingOn inc B Finset.univ)
    (hT : x.through ⊆ A) (hC : x.closed ⊆ B) :
    x.total ∈ components (inc := inc) (A ∪ B) ∧
      A ∩ x.total = x.through ∧ B ∩ x.total = x.closed := by
  obtain ⟨c,ht,hc⟩ := x.property
  have heq : c.edgeSet = x.total := by
    rw [c.edgeSet_eq_parity_union,ht,hc]
    rfl
  have hU : ∀ i, c.edgeAt i ∈ A ∪ B := by
    intro i
    have he := c.edgeAt_mem_edgeSet i
    rw [heq] at he
    rcases Finset.mem_union.mp he with he | he
    · exact Finset.mem_union_left _ (hT he)
    · exact Finset.mem_union_right _ (hC he)
  have hz : c.edgeAt 0 ∈ A := hT (by change c.edgeAt 0 ∈ x.val.1; rw [← ht]; exact c.zero_mem_parity)
  have hzn : c.edgeAt 0 ∉ B := fun hb => ((c.cycle_edge_mem_complement hA hB hU 0).mp hb) hz
  have hUr : ∀ i, c.edgeAt i ∈ B ∪ A := by simpa only [Finset.union_comm] using hU
  refine ⟨heq ▸ c.edgeSet_mem_components hA hB hU,?_,?_⟩
  · have h := c.inter_edgeSet_parity hA hB hU
    simpa only [ite_eq_left hz,heq,ht,through] using h
  · have h := c.inter_edgeSet_parity hB hA hUr
    simpa only [ite_eq_right hzn,heq,hc,closed] using h

omit [DecidableEq V] in
lemma activated_injective {A B : Finset E}
    (hA : MatchingOn inc A Finset.univ) (hB : MatchingOn inc B Finset.univ) :
    Set.InjOn (fun x : PatternCode inc => x.total)
      {x | x.through ⊆ A ∧ x.closed ⊆ B} := by
  intro x hx y hy he
  change x.total = y.total at he
  have hxx := x.activated hA hB hx.1 hx.2
  have hyy := y.activated hA hB hy.1 hy.2
  apply Subtype.ext
  apply Prod.ext
  · change x.through = y.through
    rw [← hxx.2.1,← hyy.2.1,he]
  · change x.closed = y.closed
    rw [← hxx.2.2,← hyy.2.2,he]

omit [DecidableEq V] in
lemma activated_derivative {A B : Finset E}
    (hA : MatchingOn inc A Finset.univ) (hB : MatchingOn inc B Finset.univ)
    (hT : x.through ⊆ A) (hC : x.closed ⊆ B)
    (f g : Finset E → ℝ) :
    (f ((A \ x.through) ∪ x.through) - f ((A \ x.through) ∪ x.closed)) -
      (g ((B \ x.closed) ∪ x.through) - g ((B \ x.closed) ∪ x.closed)) =
    (f A + g B) - (f (exchange A B x.total) + g (exchange B A x.total)) := by
  have hx := x.activated hA hB hT hC
  have hAT : A \ x.through = A \ x.total := by rw [← hx.2.1]; ext e; simp
  have hBC : B \ x.closed = B \ x.total := by rw [← hx.2.2]; ext e; simp
  rw [Finset.sdiff_union_of_subset hT,Finset.sdiff_union_of_subset hC,hAT,hBC]
  simp only [exchange,hx.2.1,hx.2.2]
  ring

variable [Fintype E]

omit [DecidableEq V] in
theorem activated_sum_le {A B : Finset E}
    (hA : MatchingOn inc A Finset.univ) (hB : MatchingOn inc B Finset.univ)
    (f g : Finset E → ℝ) :
    (∑ x : PatternCode inc, if x.through ⊆ A ∧ x.closed ⊆ B then
      ((f ((A \ x.through) ∪ x.through) - f ((A \ x.through) ∪ x.closed)) -
       (g ((B \ x.closed) ∪ x.through) - g ((B \ x.closed) ∪ x.closed)))^2 else 0)
    ≤ ∑ S ∈ components (inc := inc) (A ∪ B),
      ((f A + g B) - (f (exchange A B S) + g (exchange B A S)))^2 := by
  classical
  rw [← Finset.sum_filter]
  let active : Finset (PatternCode inc) := Finset.univ.filter (fun x => x.through ⊆ A ∧ x.closed ⊆ B)
  let cost : Finset E → ℝ := fun S =>
    ((f A + g B) - (f (exchange A B S) + g (exchange B A S)))^2
  change (∑ x ∈ active, _) ≤ ∑ S ∈ components (inc := inc) (A ∪ B), cost S
  have hinj : Set.InjOn (fun x : PatternCode inc => x.total) (active : Set (PatternCode inc)) := by
    intro x hx y hy h
    exact activated_injective hA hB (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 h
  calc
    _ = ∑ x ∈ active, cost x.total := by
      apply Finset.sum_congr rfl
      intro x hx
      have hh := (Finset.mem_filter.mp hx).2
      rw [x.activated_derivative hA hB hh.1 hh.2 f g]
    _ = ∑ S ∈ active.image (fun x => x.total), cost S := (Finset.sum_image hinj).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (by
      intro S hS
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hS
      have hh := (Finset.mem_filter.mp hx).2
      exact (x.activated hA hB hh.1 hh.2).1) (fun S _ _ => sq_nonneg _)

end PatternCode

end MatchingFPRAS.Transport

namespace MatchingFPRAS.PairEnergy

open scoped BigOperators

variable {ι Ω Δ : Type*} [Fintype ι] [Fintype Ω] [Fintype Δ]

omit [Fintype Ω] in
lemma weighted_jensen (s : Finset Ω) (w b : Ω → ℝ) (a : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i) * (a - (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i)) ^ 2 ≤
      ∑ i ∈ s, w i * (a - b i) ^ 2 := by
  have hm : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  obtain hm0 | hmpos := hm.eq_or_lt
  · rw [← hm0, zero_mul]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  · have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (r := fun i => w i * (a - b i))
        (f := w) (g := fun i => w i * (a - b i) ^ 2)
        hw (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
        (fun i hi => by nlinarith [sq_nonneg (w i * (a - b i))])
    have heq : (∑ i ∈ s, w i * (a - b i)) =
        (∑ i ∈ s, w i) *
          (a - (∑ i ∈ s, w i * b i) / (∑ i ∈ s, w i)) := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [mul_div_cancel₀ _ (ne_of_gt hmpos)]
    rw [heq, mul_pow] at hc
    apply (mul_le_mul_iff_right₀ hmpos).mp
    nlinarith [hc]

omit [Fintype Ω] in
lemma sum_contextMass (ρ : Δ → ℝ) (arc : Δ → ι) (context : Δ → Ω)
    (through : ι → Finset Ω) (hcontext : ∀ d, context d ∈ through (arc d))
    (h : ι → Ω → ℝ) :
    (∑ d, ρ d * h (arc d) (context d)) =
      ∑ X, ∑ A ∈ through X, contextMass ρ arc context X A * h X A := by
  classical
  symm
  simp only [contextMass, Finset.sum_mul]
  calc
    _ = ∑ X, ∑ A ∈ through X,
        ∑ d with arc d = X ∧ context d = A, ρ d * h (arc d) (context d) := by
      apply Finset.sum_congr rfl
      intro X _
      apply Finset.sum_congr rfl
      intro A _
      apply Finset.sum_congr rfl
      intro d hd
      obtain ⟨hX, hA⟩ := (Finset.mem_filter.mp hd).2
      rw [hX, hA]
    _ = ∑ X, ∑ d with arc d = X, ρ d * h (arc d) (context d) := by
      apply Finset.sum_congr rfl
      intro X _
      have ht : ∀ d ∈ Finset.univ.filter (fun d => arc d = X), context d ∈ through X := by
        intro d hd
        simpa only [(Finset.mem_filter.mp hd).2] using hcontext d
      simpa only [Finset.filter_filter] using
        Finset.sum_fiberwise_of_maps_to ht (fun d => ρ d * h (arc d) (context d))
    _ = ∑ d, ρ d * h (arc d) (context d) := Finset.sum_fiberwise _ arc _

omit [Fintype ι] in
lemma tagged_context_bound {Tag : Type*} [Fintype Tag]
    (π : Law Ω) (closed : ι → Finset Ω) (ρ : Δ → ℝ)
    (arc : Δ → ι) (context guide : Δ → Ω) (tag : Δ → Tag) (C : ℝ)
    (hC : 0 ≤ C)
    (hguide : ∀ d, guide d ∈ closed (arc d))
    (hinj : Function.Injective fun d => (context d, guide d, tag d))
    (hweight : ∀ d, ρ d ≤ C * π.weight (context d) * π.weight (guide d))
    (X : ι) (A : Ω) :
    contextMass ρ arc context X A ≤
      (C * Fintype.card Tag) * π.weight A * guideMass π closed X := by
  classical
  let s : Finset Δ := Finset.univ.filter (fun d => arc d = X ∧ context d = A)
  have hmaps : ∀ d ∈ s, guide d ∈ closed X := by
    intro d hd
    have hX := (Finset.mem_filter.mp hd).2.1
    simpa only [hX] using hguide d
  have hfiber (B : Ω) : (s.filter (fun d => guide d = B)).card ≤ Fintype.card Tag := by
    apply Finset.card_le_card_of_injOn tag (t := Finset.univ)
    · intro d hd
      exact Finset.mem_univ _
    · intro d hd e he heq
      apply hinj
      have hd' := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
      have he' := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
      have hdB := (Finset.mem_filter.mp hd).2
      have heB := (Finset.mem_filter.mp he).2
      exact Prod.ext (hd'.2.trans he'.2.symm) (Prod.ext (hdB.trans heB.symm) heq)
  change (∑ d ∈ s, ρ d) ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps ρ]
  calc
    _ ≤ ∑ B ∈ closed X, (Fintype.card Tag : ℝ) * (C * π.weight A * π.weight B) := by
      apply Finset.sum_le_sum
      intro B hB
      calc
        _ ≤ ∑ d ∈ s with guide d = B, C * π.weight A * π.weight B := by
          apply Finset.sum_le_sum
          intro d hd
          have hdA := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2.2
          have hdB := (Finset.mem_filter.mp hd).2
          simpa only [hdA, hdB] using hweight d
        _ = ((s.filter (fun d => guide d = B)).card : ℝ) *
            (C * π.weight A * π.weight B) := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber B)
          (mul_nonneg (mul_nonneg hC (π.nonneg A)) (π.nonneg B))
    _ = _ := by
      simp only [guideMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      ring

theorem error_demand_load
    (π : Law Ω) (through closed : ι → Finset Ω) (d₁ d₂ : ι → Ω → ℝ)
    (ρ : Δ → ℝ) (arc : Δ → ι) (c₀ c₁ : Δ → Ω) (C : ℝ)
    (hρ : ∀ d, 0 ≤ ρ d) (hC : 0 ≤ C)
    (hc₀ : ∀ d, c₀ d ∈ through (arc d))
    (hc₁ : ∀ d, c₁ d ∈ through (arc d))
    (hm₀ : ∀ X A, contextMass ρ arc c₀ X A ≤ C * π.weight A * guideMass π closed X)
    (hm₁ : ∀ X A, contextMass ρ arc c₁ X A ≤ C * π.weight A * guideMass π closed X) :
    (∑ d, ρ d * (d₁ (arc d) (c₁ d) - d₁ (arc d) (c₀ d)) ^ 2) ≤
      4 * C * swapSum π through closed d₁ d₂ := by
  classical
  let μ := guideMean π closed d₂
  have hcontext (c : Δ → Ω) (hc : ∀ d, c d ∈ through (arc d))
      (hm : ∀ X A, contextMass ρ arc c X A ≤ C * π.weight A * guideMass π closed X) :
      (∑ d, ρ d * (d₁ (arc d) (c d) - μ (arc d)) ^ 2) ≤
        C * swapSum π through closed d₁ d₂ := by
    rw [sum_contextMass ρ arc c through hc (fun X A => (d₁ X A - μ X) ^ 2)]
    calc
      _ ≤ ∑ X, ∑ A ∈ through X,
          C * π.weight A * guideMass π closed X * (d₁ X A - μ X) ^ 2 := by
        apply Finset.sum_le_sum
        intro X _
        exact Finset.sum_le_sum fun A _ =>
          mul_le_mul_of_nonneg_right (hm X A) (sq_nonneg _)
      _ ≤ ∑ X, ∑ A ∈ through X, C * π.weight A *
          (∑ B ∈ closed X, π.weight B * (d₁ X A - d₂ X B) ^ 2) := by
        apply Finset.sum_le_sum
        intro X _
        apply Finset.sum_le_sum
        intro A _
        have hj := weighted_jensen (closed X) π.weight (d₂ X) (d₁ X A)
          (fun B _ => π.nonneg B)
        change guideMass π closed X * (d₁ X A - μ X) ^ 2 ≤ _ at hj
        convert mul_le_mul_of_nonneg_left hj (mul_nonneg hC (π.nonneg A)) using 1
        all_goals try with_reducible_and_instances rfl
        ring
      _ = C * swapSum π through closed d₁ d₂ := by
        simp only [swapSum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro X _
        apply Finset.sum_congr rfl
        intro A _
        apply Finset.sum_congr rfl
        intro B _
        ring
  have h₀ := hcontext c₀ hc₀ hm₀
  have h₁ := hcontext c₁ hc₁ hm₁
  calc
    _ ≤ ∑ d, (2 * (ρ d * (d₁ (arc d) (c₁ d) - μ (arc d)) ^ 2) +
          2 * (ρ d * (d₁ (arc d) (c₀ d) - μ (arc d)) ^ 2)) := by
      apply Finset.sum_le_sum
      intro d _
      nlinarith [mul_nonneg (hρ d)
        (sq_nonneg (d₁ (arc d) (c₁ d) + d₁ (arc d) (c₀ d) - 2 * μ (arc d)))]
    _ = 2 * (∑ d, ρ d * (d₁ (arc d) (c₁ d) - μ (arc d)) ^ 2) +
          2 * (∑ d, ρ d * (d₁ (arc d) (c₀ d) - μ (arc d)) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 4 * C * swapSum π through closed d₁ d₂ := by linarith

end MatchingFPRAS.PairEnergy

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

namespace PatternCode

omit [DecidableEq V] in
lemma mem_throughStates (x : PatternCode inc) (A : PM inc) :
    A ∈ x.throughStates ↔ x.through ⊆ A.val := by
  classical
  simp [throughStates]

omit [DecidableEq V] in
lemma mem_closedStates (x : PatternCode inc) (A : PM inc) :
    A ∈ x.closedStates ↔ x.closed ⊆ A.val := by
  classical
  simp [closedStates]

end PatternCode

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace ErrorDemand

variable (e : ErrorDemand hbags hG)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

attribute [local instance] OAI.MatchingFPRAS.Transport.CellDemands.instFintypeBagEdge_2
lemma choice_spec (j : Bool) :
    let enc := e.choice height hheight hstep D hD w hw lo hi hlo hlohi j
    enc.first.val = e.demand.outside ∪
      (if j then e.demand.paths.contextOne e.bit e.Y else e.demand.paths.orientation e.bit) ∧
    e.pattern.closed ⊆ enc.second.val ∧
    gibbs (fun e => max lo (min hi (w e))) e.demand.1.1 *
      gibbs (fun e => max lo (min hi (w e))) e.demand.1.2 ≤
      (1000*D)^4 * gibbs (fun e => max lo (min hi (w e))) enc.first *
        gibbs (fun e => max lo (min hi (w e))) enc.second := by
  have h := (e.exists_errors height hheight hstep D hD w hw lo hi hlo hlohi).choose_spec.choose_spec
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at h
  cases j
  · exact ⟨h.1,h.2.2.1,h.2.2.2.2.1⟩
  · exact ⟨h.2.1,h.2.2.2.1,h.2.2.2.2.2⟩

lemma choice_injective (j : Bool) : Function.Injective (fun e : ErrorDemand hbags hG =>
    (e.choice height hheight hstep D hD w hw lo hi hlo hlohi j).finiteCode) := by
  intro e f h
  exact raw_injective (DemandEncoding.finiteCode_recovers _ _ h)

lemma choice_through (j : Bool) :
    (e.choice height hheight hstep D hD w hw lo hi hlo hlohi j).first ∈ e.pattern.throughStates := by
  apply (e.pattern.mem_throughStates _).mpr
  rw [(e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi j).1]
  change (e.demand.paths.side e.X).through ⊆ _
  apply Finset.Subset.trans _ (Finset.subset_union_right)
  cases j
  · exact e.demand.paths.through_subset_orientation e.bit e.X e.X_bit
  · exact e.demand.paths.through_subset_contextOne e.bit e.X e.Y e.X_bit e.Y_bit e.X_ne_Y
      BagEdge.exists_incident

theorem context_load (M : PM (BagEdge.Incident (bags := bags))) (j : Bool)
    (X : PatternCode (BagEdge.Incident (bags := bags))) (A : PM BagEdge.Incident) :
    let wt := fun e => max lo (min hi (w e))
    let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
    let ρ := fun e : ErrorDemand hbags hG => gibbs wt e.demand.1.1 * gibbs wt e.demand.1.2
    let enc := fun e : ErrorDemand hbags hG => e.choice height hheight hstep D hD w hw lo hi hlo hlohi j
    MatchingFPRAS.PairEnergy.contextMass ρ pattern (fun e => (enc e).first) X A ≤
      ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))) *
        π.weight A * MatchingFPRAS.PairEnergy.guideMass π PatternCode.closedStates X := by
  dsimp only
  apply MatchingFPRAS.PairEnergy.tagged_context_bound
    (guide := fun e => (e.choice height hheight hstep D hD w hw lo hi hlo hlohi j).second)
    (tag := fun e => (e.choice height hheight hstep D hD w hw lo hi hlo hlohi j).tag)
  · positivity
  · intro e
    exact (e.pattern.mem_closedStates _).mpr
      (e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi j).2.1
  · exact choice_injective height hheight hstep D hD w hw lo hi hlo hlohi j
  · intro e
    exact (e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi j).2.2

end ErrorDemand

end MatchingFPRAS.Transport.CellDemands

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_SafeSwitch
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.IndexedCycle

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

omit [Fintype V] [DecidableEq V] in
lemma parityPattern_subset_edgeSet (c : IndexedCycle inc) (a : ℕ) : c.parityPattern a ⊆ c.edgeSet := by
  intro e he
  obtain ⟨i,_,hi,_,rfl⟩ := (c.mem_intervalPattern e 0 c.size a).mp he
  exact c.edgeAt_mem_edgeSet i

end MatchingFPRAS.Transport.IndexedCycle

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace Demand

variable (d : Demand hbags hG)

omit [Fintype L] in
lemma outside_disjoint_through (i : Fin 4) : Disjoint d.outside (d.paths.side i).through := by
  have hp := d.corners.cell_orientation_parity d.paths.chord d.paths.chord_incidence (CellPaths.sideBit i)
  have hsub : (d.paths.side i).through ⊆ d.cycle.edgeSet := by
    apply Finset.Subset.trans (d.paths.through_subset_orientation (CellPaths.sideBit i) i rfl)
    exact hp ▸ d.cycle.parityPattern_subset_edgeSet _
  exact Finset.disjoint_left.mpr fun _ he hi => (Finset.mem_sdiff.mp he).2 (hsub hi)

omit [Fintype L] in
lemma short_error_zero (f : Finset (BagEdge bags) → ℝ) (b : Bool)
    (hh : ¬ ∀ i : Fin 4, CellPaths.sideBit i = b → (d.paths.side i).length ≠ 1) :
    d.paths.contextError d.outside f b (if b then 2 else 3) (if b then 0 else 1) = 0 := by
  classical
  push Not at hh
  obtain ⟨i,hib,hil⟩ := hh
  have he := d.cycle.cellShort_pattern hbags d.cell d.last_lt i hil
  cases b <;> fin_cases i <;> simp_all [CellPaths.sideBit]
  · exact d.paths.contextError_short_right d.outside f false 3 1 (by decide) he
  · exact d.paths.contextError_short_left d.outside f false 3 1 (by decide) (by decide)
      (by decide) BagEdge.exists_incident he
  · exact d.paths.contextError_short_right d.outside f true 2 0 (by decide) he
  · exact d.paths.contextError_short_left d.outside f true 2 0 (by decide) (by decide)
      (by decide) BagEdge.exists_incident he

end Demand

namespace ErrorDemand

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

variable (f g : Finset (BagEdge bags) → ℝ)

variable (e : ErrorDemand hbags hG)

attribute [local instance] OAI.MatchingFPRAS.Transport.CellDemands.instFintypeBagEdge_3
lemma literal_error :
    e.demand.paths.contextError e.demand.outside f e.bit e.X e.Y =
      PatternCode.firstDerivative f e.pattern
        (e.choice height hheight hstep D hD w hw lo hi hlo hlohi true).first -
      PatternCode.firstDerivative f e.pattern
        (e.choice height hheight hstep D hD w hw lo hi hlo hlohi false).first := by
  simp only [PatternCode.firstDerivative,
    (e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi true).1,
    (e.choice_spec height hheight hstep D hD w hw lo hi hlo hlohi false).1,
    Bool.false_eq_true,ite_false,ite_true]
  exact e.demand.paths.contextError_derivative e.demand.outside f e.bit e.X e.Y
    (e.demand.outside_disjoint_through e.X)

include hheight hstep hD hw hlohi

theorem error_load_bound (M : PM (BagEdge.Incident (bags := bags))) :
    let wt := fun e => max lo (min hi (w e))
    let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
    (∑ e : ErrorDemand hbags hG, π.weight e.demand.1.1 * π.weight e.demand.1.2 *
      (e.demand.paths.contextError e.demand.outside f e.bit e.X e.Y)^2) ≤
    4 * ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))) *
      MatchingFPRAS.PairEnergy.swapSum π PatternCode.throughStates PatternCode.closedStates
        (PatternCode.firstDerivative f) (PatternCode.secondDerivative g) := by
  classical
  dsimp only
  let wt := fun e => max lo (min hi (w e))
  let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
  let ρ := fun e : ErrorDemand hbags hG => π.weight e.demand.1.1 * π.weight e.demand.1.2
  let enc := fun j (e : ErrorDemand hbags hG) => e.choice height hheight hstep D hD w hw lo hi hlo hlohi j
  have h := MatchingFPRAS.PairEnergy.error_demand_load π PatternCode.throughStates
    PatternCode.closedStates (PatternCode.firstDerivative f) (PatternCode.secondDerivative g)
    ρ pattern (fun e => (enc false e).first) (fun e => (enc true e).first)
    ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags)))
    (fun e => mul_nonneg (π.nonneg _) (π.nonneg _)) (by positivity)
    (fun e => e.choice_through height hheight hstep D hD w hw lo hi hlo hlohi false)
    (fun e => e.choice_through height hheight hstep D hD w hw lo hi hlo hlohi true)
    (context_load height hheight hstep D hD w hw lo hi hlo hlohi M false)
    (context_load height hheight hstep D hD w hw lo hi hlo hlohi M true)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro e _
  rw [e.literal_error height hheight hstep D hD w hw lo hi hlo hlohi f]

end ErrorDemand

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport.PatternCode

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

variable (π : MatchingFPRAS.PairEnergy.Law (PM inc)) (f g : Finset E → ℝ)

omit [DecidableEq V] in
lemma statewise_swap_bound (A B : PM inc) :
    (∑ x : PatternCode inc, if x.through ⊆ A.val ∧ x.closed ⊆ B.val then
      (firstDerivative f x A - secondDerivative g x B)^2 else 0) ≤
    ∑ S ∈ components (inc := inc) (A.val ∪ B.val),
      ((f A.val + g B.val) - (f (exchange A.val B.val S) + g (exchange B.val A.val S)))^2 := by
  have h := activated_sum_le A.property B.property f g
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · rw [Finset.sdiff_union_of_subset hx.1,Finset.sdiff_union_of_subset hx.2]
    rfl
  · rfl

omit [DecidableEq V] in
theorem weighted_swap_bound :
    MatchingFPRAS.PairEnergy.swapSum π throughStates closedStates
      (firstDerivative f) (secondDerivative g) ≤
    ∑ A : PM inc, ∑ B : PM inc, π.weight A * π.weight B *
      ∑ S ∈ components (inc := inc) (A.val ∪ B.val),
        ((f A.val + g B.val) - (f (exchange A.val B.val S) + g (exchange B.val A.val S)))^2 := by
  classical
  let cost := fun (x : PatternCode inc) (A B : PM inc) =>
    if x.through ⊆ A.val ∧ x.closed ⊆ B.val then
      (firstDerivative f x A - secondDerivative g x B)^2 else 0
  have hsum : MatchingFPRAS.PairEnergy.swapSum π throughStates closedStates
      (firstDerivative f) (secondDerivative g) =
      ∑ A : PM inc, ∑ B : PM inc, π.weight A * π.weight B * ∑ x : PatternCode inc, cost x A B := by
    unfold MatchingFPRAS.PairEnergy.swapSum
    calc
      _ = ∑ x : PatternCode inc, ∑ A : PM inc, ∑ B : PM inc,
          π.weight A * π.weight B * cost x A B := by
        apply Finset.sum_congr rfl
        intro x _
        simp only [throughStates,closedStates,Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro A _
        by_cases ht : x.through ⊆ A.val
        · simp only [ht,ite_true]
          apply Finset.sum_congr rfl
          intro B _
          by_cases hc : x.closed ⊆ B.val <;> simp [cost,ht,hc]
        · simp [cost,ht]
      _ = ∑ A : PM inc, ∑ B : PM inc, ∑ x : PatternCode inc,
          π.weight A * π.weight B * cost x A B := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro A _
        rw [Finset.sum_comm]
      _ = _ := by simp only [Finset.mul_sum]
  rw [hsum]
  apply Finset.sum_le_sum
  intro A _
  apply Finset.sum_le_sum
  intro B _
  exact mul_le_mul_of_nonneg_left (statewise_swap_bound f g A B)
    (mul_nonneg (π.nonneg A) (π.nonneg B))

end MatchingFPRAS.Transport.PatternCode

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

namespace CellPaths

variable (c : CellPaths inc)

omit [Fintype V] [Fintype E] in
lemma switched_true_common : c.switched true = c.commonInterior ∪ {c.chord 0,c.chord 2} := by
  ext e
  simp [switched,switchPieces,pieces,assemble,sideBit,OddPath.closed,commonInterior]
  tauto

omit [Fintype V] [Fintype E] in
lemma switched_false_common : c.switched false = c.commonInterior ∪ {c.chord 1,c.chord 3} := by
  ext e
  simp [switched,switchPieces,pieces,assemble,sideBit,OddPath.closed,commonInterior]
  tauto

omit [Fintype E] in
lemma safe_switch (w : E → ℝ) (K : ℝ) (hw : ∀ i j, w (c.chord i) ≤ K*w (c.chord j))
    (R : Finset E) (A B : PM inc)
    (hA : A.val = R ∪ c.switched true) (hB : B.val = R ∪ c.switched false) :
    SafeSwitch w K A B := by
  refine ⟨fun i => (c.side i).vertex 0,c.chord,R ∪ c.commonInterior,
    c.corners_injective,?_,?_,?_,hw⟩
  · intro i x
    rw [c.chord_incidence,c.joins]
  · rw [hA,c.switched_true_common,Finset.union_assoc]
  · rw [hB,c.switched_false_common,Finset.union_assoc]

end CellPaths

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

namespace Demand

variable (d : Demand hbags hG)

omit [Fintype L] in
lemma switchState_val (b : Bool) : (d.switchState b).val = d.outside ∪ d.paths.switched b := by
  exact congrArg (fun R => R ∪ d.paths.switched b)
    (d.corners.embeddedPair_outside d.1.1 d.1.2 d.2.1.cycle_union
      d.paths.chord d.paths.chord_incidence 0)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

include hheight hstep hD hw hlo in
omit [Fintype L] in
lemma switchState_safe : SafeSwitch (fun e => max lo (min hi (w e))) (1000*D)
    (d.switchState true) (d.switchState false) := by
  apply d.paths.safe_switch _ _ _ d.outside _ _ (d.switchState_val true) (d.switchState_val false)
  intro i j
  exact d.cycle.cell_clamp_comparability hbags height hheight hstep d.cell d.last_lt D hD w hw
    lo hi (le_of_lt hlo) ⟨i,Or.inl rfl⟩ ⟨j,Or.inl rfl⟩

attribute [local instance] OAI.MatchingFPRAS.Transport.CellDemands.instFintypeBagEdge_4
lemma switchChoice_first :
    (d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi).first = d.switchState true := by
  apply Subtype.ext
  exact (d.switchChoice_spec height hheight hstep D hD w hw lo hi hlo hlohi).1.trans
    (d.switchState_val true).symm

include hheight hstep hD hw hlohi

theorem switch_load_bound (M : PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) :
    let wt := fun e => max lo (min hi (w e))
    let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
    (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 *
      (f (d.outside ∪ d.paths.switched true) - f (d.outside ∪ d.paths.switched false))^2) ≤
    ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))) *
      ∑ A : PM BagEdge.Incident, π.weight A *
        ∑ B ∈ safeDestinations wt (1000*D) A, (f A.val-f B.val)^2 := by
  classical
  dsimp only
  let wt := fun e => max lo (min hi (w e))
  let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
  let ρ := fun d : Demand hbags hG => π.weight d.1.1 * π.weight d.1.2
  let enc := fun d : Demand hbags hG => d.switchChoice height hheight hstep D hD w hw lo hi hlo hlohi
  let C := (1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))
  let cost := fun A : PM BagEdge.Incident =>
    ∑ B ∈ safeDestinations wt (1000*D) A, (f A.val-f B.val)^2
  have hc (A) : 0 ≤ cost A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hload (A : PM BagEdge.Incident) :
      MatchingFPRAS.PairEnergy.contextMass ρ (fun _ => ()) (fun d => (enc d).first) () A ≤ C*π.weight A := by
    have h := MatchingFPRAS.PairEnergy.tagged_context_bound π (fun _ : Unit => Finset.univ) ρ
      (fun _ => ()) (fun d => (enc d).first) (fun d => (enc d).second) (fun d => (enc d).tag)
      ((1000*D)^4) (by positivity) (fun _ => Finset.mem_univ _)
      (switchChoice_injective height hheight hstep D hD w hw lo hi hlo hlohi)
      (fun d => (d.switchChoice_spec height hheight hstep D hD w hw lo hi hlo hlohi).2) () A
    simpa only [MatchingFPRAS.PairEnergy.guideMass,π.total,mul_one] using h
  have hd (d : Demand hbags hG) :
      (f (d.outside ∪ d.paths.switched true)-f (d.outside ∪ d.paths.switched false))^2 ≤
      cost (enc d).first := by
    have he := d.switchChoice_first height hheight hstep D hD w hw lo hi hlo hlohi
    change _ ≤ cost _
    rw [he,← d.switchState_val true,← d.switchState_val false]
    exact Finset.single_le_sum (fun (B : PM (BagEdge.Incident (bags := bags))) _ =>
      sq_nonneg (f (d.switchState true).val-f B.val)) (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,d.switchState_safe height hheight hstep D hD w hw lo hi hlo⟩)
  calc
    _ ≤ ∑ d : Demand hbags hG, ρ d * cost (enc d).first :=
      Finset.sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (hd d)
        (mul_nonneg (π.nonneg _) (π.nonneg _))
    _ = ∑ A : PM BagEdge.Incident,
        MatchingFPRAS.PairEnergy.contextMass ρ (fun _ => ()) (fun d => (enc d).first) () A * cost A := by
      simpa using MatchingFPRAS.PairEnergy.sum_contextMass ρ (fun _ => ()) (fun d => (enc d).first)
        (fun _ : Unit => Finset.univ) (fun _ => Finset.mem_univ _) (fun _ => cost)
    _ ≤ ∑ A : PM BagEdge.Incident, C*π.weight A*cost A :=
      Finset.sum_le_sum fun A _ => mul_le_mul_of_nonneg_right (hload A) (hc A)
    _ = _ := by simp only [C,cost,π,wt,Finset.mul_sum,mul_assoc]

end Demand

end

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

lemma sum_errorDemands (ρ : Demand hbags hG → ℝ) (f : Finset (BagEdge bags) → ℝ) :
    (∑ e : ErrorDemand hbags hG, ρ e.demand * (e.demand.cellError f e.bit)^2) =
    ∑ d : Demand hbags hG, ρ d * ((d.cellError f true)^2+(d.cellError f false)^2) := by
  classical
  let p := fun e : Bool × Demand hbags hG =>
    ∀ i : Fin 4, CellPaths.sideBit i = e.1 → (e.2.paths.side i).length ≠ 1
  let H := fun e : Bool × Demand hbags hG => ρ e.2 * (e.2.cellError f e.1)^2
  have hzero (e : Bool × Demand hbags hG) (he : ¬ p e) : H e = 0 := by
    have h := e.2.short_error_zero f e.1 he
    simp only [H,Demand.cellError,h,zero_pow (by decide : 2≠0),mul_zero]
  calc
    _ = ∑ e ∈ Finset.univ.filter p, H e := (Finset.sum_subtype (p := p) _
      (fun _ => by simp only [Finset.mem_filter,Finset.mem_univ,true_and]) H).symm
    _ = ∑ e : Bool × Demand hbags hG, H e :=
      Finset.sum_subset (Finset.filter_subset _ _) (by
        intro e _ he
        exact hzero e (fun hp => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [H,Fintype.sum_bool,← Finset.sum_add_distrib,mul_add]

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

include hheight hstep hD hw hlohi

attribute [local instance] OAI.MatchingFPRAS.Transport.CellDemands.instFintypeBagEdge_5
theorem total_cell_demand_load (M : PM (BagEdge.Incident (bags := bags)))
    (f g : Finset (BagEdge bags) → ℝ) :
    let wt := fun e => max lo (min hi (w e))
    let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
    (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * d.cellCost f) ≤
    ((1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))) *
      ((∑ A : PM BagEdge.Incident, π.weight A *
          ∑ B ∈ safeDestinations wt (1000*D) A, (f A.val-f B.val)^2) +
       4 * ∑ A : PM BagEdge.Incident, ∑ B : PM BagEdge.Incident, π.weight A * π.weight B *
          ∑ S ∈ components (inc := BagEdge.Incident) (A.val ∪ B.val),
            ((f A.val+g B.val)-(f (exchange A.val B.val S)+g (exchange B.val A.val S)))^2) := by
  classical
  dsimp only
  let wt := fun e => max lo (min hi (w e))
  let π := gibbsLaw wt (fun _ => lt_of_lt_of_le hlo (le_max_left _ _)) M
  let C := (1000*D)^4 * Fintype.card (DemandTag (V := V) (E := BagEdge bags))
  have hC : 0 ≤ C := by positivity
  have hs := Demand.switch_load_bound (hbags := hbags) (hG := hG) height hheight hstep D hD w hw lo hi hlo hlohi M f
  have he := ErrorDemand.error_load_bound (hbags := hbags) (hG := hG) height hheight hstep D hD w hw lo hi hlo hlohi f g M
  have hsw := PatternCode.weighted_swap_bound π f g
  have herr := mul_le_mul_of_nonneg_left hsw (mul_nonneg (by norm_num : (0:ℝ)≤4) hC)
  have hsum := sum_errorDemands (hbags := hbags) (hG := hG)
    (fun d => π.weight d.1.1 * π.weight d.1.2) f
  change (∑ e : ErrorDemand hbags hG, π.weight e.demand.1.1 * π.weight e.demand.1.2 *
    (e.demand.cellError f e.bit)^2) ≤ _ at he
  rw [hsum] at he
  have hsplit : (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * d.cellCost f) =
      (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * (d.cellSwitch f)^2) +
      (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 *
        ((d.cellError f true)^2+(d.cellError f false)^2)) := by
    simp only [Demand.cellCost,mul_add,Finset.sum_add_distrib]
    ring
  change (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * d.cellCost f) ≤ _
  rw [hsplit]
  change (∑ d : Demand hbags hG, π.weight d.1.1 * π.weight d.1.2 * (d.cellSwitch f)^2) ≤ _ at hs
  have h := add_le_add hs (he.trans herr)
  calc
    _ ≤ _ := h
    _ = _ := by dsimp only [C,π,wt]; ring

end MatchingFPRAS.Transport.CellDemands

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Underlying
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.Transport.Sparse.decideOverlay _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

namespace Overlay

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)

open scoped symmDiff

lemma discrepancy_cycles (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ) :
    (discrepancy ends hloop M N).IsCycles := by
  have h := (underlying_perfect ends hloop M hM).symmDiff_isCycles
    (underlying_perfect ends hloop N hN)
  exact h

lemma discrepancy_component_cycle (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    (c : (discrepancy ends hloop M N).ConnectedComponent) (v : V)
    (hv : v ∈ c.supp) (hn : ((discrepancy ends hloop M N).neighborSet v).Nonempty) :
    ∃ p : (discrepancy ends hloop M N).Walk v v,
      p.IsCycle ∧ p.toSubgraph.verts = c.supp :=
  (discrepancy_cycles ends hloop M N hM hN).exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv hn

lemma discrepancy_component_even_cycle (M N : Finset E)
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)
    (c : (discrepancy ends hloop M N).ConnectedComponent) (v : V)
    (hv : v ∈ c.supp) (hn : ((discrepancy ends hloop M N).neighborSet v).Nonempty) :
    ∃ p : (discrepancy ends hloop M N).Walk v v,
      p.IsCycle ∧ p.toSubgraph.verts = c.supp ∧ p.length % 2 = 0 ∧ 4 ≤ p.length := by
  obtain ⟨p, hp, hc⟩ := discrepancy_component_cycle ends hloop M N hM hN c v hv hn
  have he := alternating_cycle_parity p hp (discrepancy_alternating ends hloop M N hM hN)
  exact ⟨p, hp, hc, he, by have := hp.three_le_length; omega⟩

end Overlay

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.Overlay

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)

variable (M N : Finset E)

variable (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)

variable (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)

lemma indexedCycle_edge_mem {v : V}
    (p : (discrepancy ends hloop M N).Walk v v) (hp : p.IsCycle)
    (i : Fin p.length) : (indexedCycle ends hloop M N hM hN p hp).edge i ∈ M ∪ N :=
  (cyclicEdge_spec ends hloop M N hM hN p hp i.val).1

end

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)

variable {M N : Finset E}

variable (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)

variable (hN : MatchingOn (fun e v => v ∈ ends e) N Finset.univ)

include hM hN

omit [DecidableEq V] in
lemma parallel_component [DecidableEq V] {e f : E} (he : e ∈ M) (hf : f ∈ N)
    (hef : ends e = ends f) :
    componentEdges (inc := fun e v => v ∈ ends e) (M ∪ N) e = {e,f} := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, v ∈ ends e := by
    induction ends e using Sym2.inductionOn with | hf a b => exact ⟨a,by simp⟩
  have hfv : v ∈ ends f := hef ▸ hv
  have closed : ∀ {a b}, a ∈ ({e,f} : Finset E) →
      (overlayLineGraph (fun e v => v ∈ ends e) (M ∪ N)).Adj a b → b ∈ ({e,f} : Finset E) := by
    intro a b ha hab
    obtain ⟨_,_,hb,w,haw,hbw⟩ := hab
    have hew : w ∈ ends e := by
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact haw
      · have haf := Finset.mem_singleton.mp ha
        simpa only [haf,← hef] using haw
    have hfw : w ∈ ends f := hef ▸ hew
    rcases Finset.mem_union.mp hb with hb | hb
    · have hbe := hM.unique (Finset.mem_univ w) hb hbw he hew
      simp [hbe]
    · have hbf := hN.unique (Finset.mem_univ w) hb hbw hf hfw
      simp [hbf]
  ext a
  constructor
  · intro ha
    obtain ⟨hau,hr⟩ := (mem_componentEdges _ _ _).mp ha
    have hrel := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hr
    clear ha hau hr
    induction hrel with
    | refl => simp
    | tail hpath hadj ih => exact closed ih hadj
  · intro ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact componentEdges_self (Finset.mem_union_left N he)
    · have haf := Finset.mem_singleton.mp ha
      subst a
      exact (mem_componentEdges _ _ _).mpr ⟨Finset.mem_union_right M hf,
        shares_reachable (Finset.mem_union_left N he) (Finset.mem_union_right M hf) hv hfv⟩

include hloop

theorem component_classification {S : Finset E}
    (hS : S ∈ components (inc := fun e v => v ∈ ends e) (M ∪ N)) :
    (∃ e ∈ M, ∃ f ∈ N, ends e = ends f ∧ S = {e,f}) ∨
    (∃ c : IndexedCycle (fun e v => v ∈ ends e),
      (∀ i, c.edgeAt i ∈ M ∪ N) ∧ S = c.edgeSet) := by
  classical
  obtain ⟨a,ha,haS⟩ := mem_components.mp hS
  obtain ⟨v,hav⟩ : ∃ v, v ∈ ends a := by
    induction ends a using Sym2.inductionOn with | hf x y => exact ⟨x,by simp⟩
  obtain ⟨e,⟨he,hev⟩,_⟩ := hM.2 v (Finset.mem_univ v)
  obtain ⟨f,⟨hf,hfv⟩,_⟩ := hN.2 v (Finset.mem_univ v)
  have heU : e ∈ M ∪ N := Finset.mem_union_left N he
  have heS : e ∈ S := by
    rw [← haS]
    exact (mem_componentEdges _ _ _).mpr ⟨heU, shares_reachable ha heU hav hev⟩
  by_cases hef : ends e = ends f
  · left
    refine ⟨e,he,f,hf,hef,?_⟩
    rw [← haS, componentEdges_eq (shares_reachable ha heU hav hev)]
    exact parallel_component ends hM hN he hf hef
  · right
    obtain ⟨w,hw⟩ := exists_partner ends hev
    have hadj : (discrepancy ends hloop M N).Adj v w := by
      apply (discrepancy_adj_iff ends hloop M N v w).mpr
      refine Or.inl ⟨⟨e,he,hw⟩,?_⟩
      rintro ⟨g,hg,hgw⟩
      have hgv : v ∈ ends g := by rw [hgw]; simp
      have hgf := hN.unique (Finset.mem_univ v) hg hgv hf hfv
      apply hef
      rw [hw,← hgf,hgw]
    let H := discrepancy ends hloop M N
    obtain ⟨p,hp,_,_,_⟩ := discrepancy_component_even_cycle ends hloop M N hM hN
      (H.connectedComponentMk v) v rfl ⟨w,hadj⟩
    let c := indexedCycle ends hloop M N hM hN p hp
    have hU : ∀ i, c.edgeAt i ∈ M ∪ N := by
      intro i
      exact indexedCycle_edge_mem ends hloop M N hM hN p hp (c.index i)
    have hv0 : c.vertexAt 0 = v := by
      simp [c,IndexedCycle.vertexAt,IndexedCycle.index,indexedCycle,cyclicVertex]
    have hec : e ∈ c.edgeSet :=
      c.edge_incident_cycle_mem hM hN hU heU 0 (by have := c.four_le; omega) (hv0.symm ▸ hev)
    refine ⟨c,hU,?_⟩
    exact component_eq_of_shares hS (c.edgeSet_mem_components hM hN hU) heS hec hev hev

end MatchingFPRAS.Transport.Overlay

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_ComponentOrder
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

variable {inc : E → V → Prop}

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_zero (U : Finset E) : componentPrefix (inc := inc) U 0 = ∅ := by
  ext e
  simp [mem_componentPrefix]

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_succ (U : Finset E) (i : ℕ) (hi : i < (components (inc := inc) U).card) :
    componentPrefix (inc := inc) U (i+1) =
      componentPrefix (inc := inc) U i ∪ (componentOrder (inc := inc) U ⟨i,hi⟩).val := by
  ext e
  simp only [mem_componentPrefix, Finset.mem_union]
  constructor
  · rintro ⟨j,hj,he⟩
    by_cases hji : j.val < i
    · exact Or.inl ⟨j,hji,he⟩
    · have hje : j = ⟨i,hi⟩ := Fin.ext (by change j.val = i; omega)
      exact Or.inr (hje ▸ he)
  · rintro (⟨j,hj,he⟩ | he)
    · exact ⟨j,by omega,he⟩
    · exact ⟨⟨i,hi⟩,by change i < i+1; omega,he⟩

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_full (U : Finset E) :
    componentPrefix (inc := inc) U (components (inc := inc) U).card = U := by
  rw [← components_cover (inc := inc) U]
  conv_lhs => rw [components_cover]
  ext e
  simp only [mem_componentPrefix, Finset.mem_biUnion, id_eq]
  constructor
  · rintro ⟨j,_,he⟩
    exact ⟨(componentOrder U j).val, (componentOrder U j).property, he⟩
  · rintro ⟨S,hS,he⟩
    obtain ⟨j,hj⟩ := (componentOrder (inc := inc) U).surjective ⟨S,hS⟩
    exact ⟨j,j.isLt,by simpa only [hj] using he⟩

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_disjoint (U : Finset E) (i : ℕ)
    (hi : i < (components (inc := inc) U).card) :
    Disjoint (componentPrefix (inc := inc) U i) (componentOrder (inc := inc) U ⟨i,hi⟩).val := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨j,hj,he⟩ := (mem_componentPrefix U i e).mp he
  have hne : (componentOrder (inc := inc) U j).val ≠
      (componentOrder (inc := inc) U ⟨i,hi⟩).val := by
    intro heq
    have hh := (componentOrder (inc := inc) U).injective (Subtype.ext heq)
    have hv : j.val = i := congrArg Fin.val hh
    omega
  exact Finset.disjoint_left.mp
    (components_pairwise_disjoint U (componentOrder U j).property
      (componentOrder U ⟨i,hi⟩).property hne) he hf

lemma exchange_empty (M N : Finset E) : exchange M N ∅ = M := by
  simp [exchange]

lemma exchange_all (M N : Finset E) : exchange M N (M ∪ N) = N := by
  ext e
  simp only [mem_exchange, Finset.mem_union]
  tauto

lemma exchange_disjoint_composition (M N S T : Finset E) (h : Disjoint S T) :
    exchange (exchange M N S) (exchange N M S) T = exchange M N (S ∪ T) := by
  rw [exchange_composition]
  congr 1
  ext e
  have hh : e ∈ S → e ∉ T := fun he => Finset.disjoint_left.mp h he
  simp only [Finset.mem_symmDiff, Finset.mem_union]
  tauto

omit [Fintype V] [DecidableEq V] in
lemma componentPrefix_step (M N : Finset E) (i : ℕ)
    (hi : i < (components (inc := inc) (M ∪ N)).card) :
    exchange M N (componentPrefix (inc := inc) (M ∪ N) (i+1)) =
      exchange (exchange M N (componentPrefix (inc := inc) (M ∪ N) i))
        (exchange N M (componentPrefix (inc := inc) (M ∪ N) i))
        (componentOrder (inc := inc) (M ∪ N) ⟨i,hi⟩).val := by
  rw [componentPrefix_succ _ _ hi,
    exchange_disjoint_composition M N _ _ (componentPrefix_disjoint _ _ hi)]

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_union (p : PM inc × PM inc) (i : ℕ) :
    (prefixPair p i).1.val ∪ (prefixPair p i).2.val = p.1.val ∪ p.2.val :=
  exchange_union _ _ _

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_involutive (i : ℕ) : Function.Involutive (fun p : PM inc × PM inc => prefixPair p i) := by
  intro p
  have hu := prefixPair_union p i
  apply Prod.ext <;> apply Subtype.ext
  · change exchange (prefixPair p i).1.val (prefixPair p i).2.val
      (componentPrefix (inc := inc) ((prefixPair p i).1.val ∪ (prefixPair p i).2.val) i) = _
    rw [hu]
    exact exchange_involution _ _ _
  · change exchange (prefixPair p i).2.val (prefixPair p i).1.val
      (componentPrefix (inc := inc) ((prefixPair p i).1.val ∪ (prefixPair p i).2.val) i) = _
    rw [hu]
    exact exchange_involution _ _ _

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_zero (p : PM inc × PM inc) : prefixPair p 0 = p := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [prefixPair, componentPrefix_zero, exchange_empty]

omit [Fintype V] [DecidableEq V] [Fintype E] in
lemma componentPrefix_eq_full (U : Finset E) (i : ℕ)
    (hi : (components (inc := inc) U).card ≤ i) : componentPrefix (inc := inc) U i = U := by
  calc
    _ = componentPrefix (inc := inc) U (components (inc := inc) U).card := by
      apply Finset.ext
      intro e
      simp only [mem_componentPrefix]
      constructor
      · rintro ⟨j,_,he⟩
        exact ⟨j,j.isLt,he⟩
      · rintro ⟨j,_,he⟩
        exact ⟨j,Nat.lt_of_lt_of_le j.isLt hi,he⟩
    _ = U := componentPrefix_full U

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_full (p : PM inc × PM inc) (i : ℕ)
    (hi : (components (inc := inc) (p.1.val ∪ p.2.val)).card ≤ i) :
    prefixPair p i = (p.2,p.1) := by
  apply Prod.ext <;> apply Subtype.ext
  · dsimp only [prefixPair]
    rw [componentPrefix_eq_full _ _ hi, exchange_all]
  · dsimp only [prefixPair]
    rw [componentPrefix_eq_full _ _ hi, Finset.union_comm p.1.val p.2.val, exchange_all]

omit [DecidableEq V] [Fintype E] in
lemma prefixPair_step (p : PM inc × PM inc) (i : ℕ) :
    prefixPair p (i+1) = componentPair (prefixPair p i) i := by
  classical
  by_cases h : i < (components (inc := inc) (p.1.val ∪ p.2.val)).card
  · apply Prod.ext <;> apply Subtype.ext
    · change exchange p.1.val p.2.val (componentPrefix (inc := inc) (p.1.val ∪ p.2.val) (i+1)) =
        exchange (prefixPair p i).1.val (prefixPair p i).2.val
          (componentAt (inc := inc) ((prefixPair p i).1.val ∪ (prefixPair p i).2.val) i)
      rw [prefixPair_union, componentAt, dite_eq_left h]
      exact componentPrefix_step _ _ _ h
    · change exchange p.2.val p.1.val (componentPrefix (inc := inc) (p.1.val ∪ p.2.val) (i+1)) =
        exchange (prefixPair p i).2.val (prefixPair p i).1.val
          (componentAt (inc := inc) ((prefixPair p i).1.val ∪ (prefixPair p i).2.val) i)
      rw [prefixPair_union, componentAt, dite_eq_left h, componentPrefix_succ _ _ h]
      exact (exchange_disjoint_composition _ _ _ _ (componentPrefix_disjoint _ _ h)).symm
  · have hle := Nat.le_of_not_gt h
    rw [prefixPair_full p (i+1) (by omega), prefixPair_full p i hle]
    apply Prod.ext <;> apply Subtype.ext <;>
      simp only [componentPair, componentAt, Finset.union_comm p.2.val p.1.val, dite_eq_right h,
        exchange_empty]

omit [DecidableEq V] in
lemma prefixPair_gibbs (w : E → ℝ) (p : PM inc × PM inc) (i : ℕ) :
    gibbs w (prefixPair p i).1 * gibbs w (prefixPair p i).2 = gibbs w p.1 * gibbs w p.2 := by
  simp only [gibbs, div_mul_div_comm]
  congr 1
  exact exchange_weight w _ _ _

omit [DecidableEq V] [Fintype E] in
lemma prefix_difference_sum (f : PM inc → ℝ) (p : PM inc × PM inc) (n : ℕ) :
    (∑ i ∈ Finset.range n, componentDifference f (prefixPair p i) i) =
      f p.1 - f (prefixPair p n).1 := by
  induction n with
  | zero => simp [prefixPair_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [componentDifference, ← prefixPair_step]
    ring

omit [DecidableEq V] [Fintype E] in
lemma canonical_path_square (hinc : ∀ e, ∃ v, inc e v)
    (f : PM inc → ℝ) (p : PM inc × PM inc) :
    (f p.1 - f p.2)^2 ≤ (Fintype.card V : ℝ) *
      ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f (prefixPair p i) i)^2 := by
  classical
  have hfull := prefixPair_full p (Fintype.card V) (components_card_le hinc _)
  have hs := prefix_difference_sum f p (Fintype.card V)
  rw [hfull] at hs
  rw [← hs]
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (Fintype.card V))
    (fun i => componentDifference f (prefixPair p i) i) (fun _ => (1:ℝ))
  simpa only [mul_one, one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm] using hh

omit [DecidableEq V] in
lemma sum_prefixPair (w : E → ℝ) (g : PM inc × PM inc → ℝ) (i : ℕ) :
    letI : Fintype (PM inc) := Fintype.ofFinite _
    (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 * g (prefixPair p i)) =
      ∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 * g p := by
  classical
  let : Fintype (PM inc) := Fintype.ofFinite _
  let e := (prefixPair_involutive i).toPerm (fun p : PM inc × PM inc => prefixPair p i)
  have hh := Equiv.sum_comp e (fun p => gibbs w p.1 * gibbs w p.2 * g p)
  change (∑ p : PM inc × PM inc, gibbs w (prefixPair p i).1 * gibbs w (prefixPair p i).2 *
    g (prefixPair p i)) = _ at hh
  simpa only [prefixPair_gibbs] using hh

omit [DecidableEq V] in
theorem cycle_demand_variance (hinc : ∀ e, ∃ v, inc e v)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (f : PM inc → ℝ) :
    letI : Fintype (PM inc) := Fintype.ofFinite _
    (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 * (f p.1 - f p.2)^2) / 2 ≤
      (Fintype.card V : ℝ) * ∑ p : PM inc × PM inc,
        gibbs w p.1 * gibbs w p.2 *
          ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f p i)^2 := by
  classical
  let : Fintype (PM inc) := Fintype.ofFinite _
  have he : (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 *
        ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f (prefixPair p i) i)^2) =
      ∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 *
        ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f p i)^2 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.range _)]
    apply Finset.sum_congr rfl
    intro i _
    exact sum_prefixPair w (fun p => (componentDifference f p i)^2) i
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (PM inc × PM inc)))
    (fun p _ => mul_le_mul_of_nonneg_left (canonical_path_square hinc f p)
      (mul_nonneg (le_of_lt (gibbs_pos w hw p.1)) (le_of_lt (gibbs_pos w hw p.2))))
  have hr : 0 ≤ (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 * (f p.1 - f p.2)^2) :=
    Finset.sum_nonneg (fun p _ => mul_nonneg
      (mul_nonneg (le_of_lt (gibbs_pos w hw p.1)) (le_of_lt (gibbs_pos w hw p.2))) (sq_nonneg _))
  have hrew : (∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 *
        ((Fintype.card V : ℝ) * ∑ i ∈ Finset.range (Fintype.card V),
          (componentDifference f (prefixPair p i) i)^2)) =
      (Fintype.card V : ℝ) * ∑ p : PM inc × PM inc, gibbs w p.1 * gibbs w p.2 *
        ∑ i ∈ Finset.range (Fintype.card V), (componentDifference f p i)^2 := by
    rw [← he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hrew] at hb
  linarith

end

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

omit [DecidableEq V] [Fintype E] in
lemma matching_inter_parallel {M : Finset E}
    (hM : MatchingOn (fun e v => v ∈ ends e) M Finset.univ)
    {e f : E} (he : e ∈ M) (hef : ends e = ends f) : M ∩ {e,f} = {e} := by
  classical
  obtain ⟨v,hv⟩ : ∃ v, v ∈ ends e := by
    induction ends e using Sym2.inductionOn with | hf a b => exact ⟨a,by simp⟩
  ext a
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨ha, rfl | haf⟩
    · rfl
    · subst a
      exact hM.unique (Finset.mem_univ v) ha (hef ▸ hv) he hv
  · rintro rfl
    exact ⟨he,Or.inl rfl⟩

omit [DecidableEq V] [Fintype E] in
lemma parallel_exchange_color (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e))
    {S : Finset E} (hS : S ∈ components (inc := fun e v => v ∈ ends e) (p.1.val ∪ p.2.val))
    {e f : E} (he : e ∈ p.1.val) (hf : f ∈ p.2.val) (hef : ends e = ends f) (hset : S = {e,f}) :
    ColorChange ends p.1
      ⟨exchange p.1.val p.2.val S,exchange_matching p.1.property p.2.property (component_exchange_compatible hS)⟩ := by
  classical
  refine ⟨e,f,p.1.val \ S,hef,?_,?_⟩
  · have h := matching_inter_parallel ends p.1.property he hef
    rw [← hset] at h
    rw [← h]
    ext a
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_inter]
    tauto
  · change exchange p.1.val p.2.val S = _
    have h := matching_inter_parallel ends p.2.property hf hef.symm
    rw [Finset.pair_comm,← hset] at h
    exact congrArg ((p.1.val \ S) ∪ ·) h

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

omit [Fintype L] in
lemma Demand.cellCost_nonneg (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) :
    0 ≤ d.cellCost f := by unfold Demand.cellCost; positivity

omit [Fintype L] in
lemma Demand.cellCost_eq (d : Demand hbags hG) (f : Finset (BagEdge bags) → ℝ) :
    d.cellCost f = d.cycle.diagramEnergy hbags d.outside f
      d.2.2.val.x d.2.2.val.p d.2.2.val.q d.2.2.val.y := by
  classical
  rw [IndexedCycle.diagramEnergy, dite_eq_left ⟨d.cell,d.last_lt⟩]
  rfl

attribute [local instance] OAI.MatchingFPRAS.Transport.CellDemands.instFintypeBagEdge_6
lemma longCellCost_nonneg (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) : 0 ≤ longCellCost (hbags := hbags) (hG := hG) p f :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Demand.cellCost_nonneg _ _))

lemma colorCost_nonneg (A : PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) : 0 ≤ colorCost A f :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem component_cell_bound
    (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) {S : Finset (BagEdge bags)}
    (hS : S ∈ components (inc := BagEdge.Incident) (p.1.val ∪ p.2.val)) :
    (f p.1.val - f (exchange p.1.val p.2.val S))^2 ≤
      3 * (Fintype.card V : ℝ) * longCellCost (hbags := hbags) (hG := hG) p f + colorCost p.1 f := by
  classical
  rcases Overlay.component_classification (fun e : BagEdge bags => e.val.val.1)
    (fun e => e.val.property) p.1.property p.2.property hS with h | ⟨c,hc,rfl⟩
  · obtain ⟨e,he,d,hd,hed,hset⟩ := h
    have hcol := parallel_exchange_color (fun e : BagEdge bags => e.val.val.1) p hS he hd hed hset
    have hle : (f p.1.val-f (exchange p.1.val p.2.val S))^2 ≤ colorCost p.1 f := by
      exact Finset.single_le_sum (s := colorDestinations (fun e : BagEdge bags => e.val.val.1) p.1)
        (a := ⟨exchange p.1.val p.2.val S,exchange_matching p.1.property p.2.property (component_exchange_compatible hS)⟩)
        (f := fun B : PM BagEdge.Incident => (f p.1.val-f B.val)^2)
        (fun _ _ => sq_nonneg _) (by
          change _ ∈ Finset.univ.filter (ColorChange (fun e : BagEdge bags => e.val.val.1) p.1)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcol⟩)
    exact hle.trans (le_add_of_nonneg_left (mul_nonneg (by positivity) (longCellCost_nonneg p f)))
  · let T : LongComponent p := ⟨c.edgeSet,c,rfl,hc⟩
    have hcell := T.cycle.exchange_cell_square_bound hbags p.1.property p.2.property T.cycle_union hG f
    have hcost : (∑ a ∈ (T.cycle.subdivision hbags hG).cellSet,
        T.cycle.diagramEnergy hbags (p.1.val \ T.cycle.edgeSet) f a.x a.p a.q a.y) =
        ∑ a : ↥(T.cycle.subdivision hbags hG).cellSet,
          (show Demand hbags hG from ⟨p,T,a⟩).cellCost f := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro a _
      exact (Demand.cellCost_eq ⟨p,T,a⟩ f).symm
    rw [hcost,T.cycle_set] at hcell
    have hle : (∑ a : ↥(T.cycle.subdivision hbags hG).cellSet,
          (show Demand hbags hG from ⟨p,T,a⟩).cellCost f) ≤
        longCellCost (hbags := hbags) (hG := hG) p f :=
      Finset.single_le_sum (f := fun S : LongComponent p => ∑ a : ↥(S.cycle.subdivision hbags hG).cellSet,
        (show Demand hbags hG from ⟨p,S,a⟩).cellCost f)
        (fun S _ => Finset.sum_nonneg (fun a _ => Demand.cellCost_nonneg ⟨p,S,a⟩ f)) (Finset.mem_univ T)
    exact (hcell.trans (mul_le_mul_of_nonneg_left hle (by positivity))).trans
      (le_add_of_nonneg_right (colorCost_nonneg p.1 f))

end MatchingFPRAS.Transport.CellDemands

lemma arbitrary_sigma_sum {α : Type*} {β : α → Type*} [Fintype α] [∀ a, Fintype (β a)]
    [i : Fintype (Sigma β)] (f : Sigma β → ℝ) :
    (∑ d : Sigma β, f d) = ∑ a : α, ∑ b : β a, f ⟨a,b⟩ := by
  have hi : i = Sigma.instFintype := Subsingleton.elim _ _
  subst hi
  exact Fintype.sum_sigma f

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_EndpointPair
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

lemma componentDifference_cell_bound
    (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) (i : ℕ) :
    (componentDifference (fun A => f A.val) p i)^2 ≤
      3 * (Fintype.card V : ℝ) * longCellCost (hbags := hbags) (hG := hG) p f + colorCost p.1 f := by
  classical
  change (f p.1.val - f (exchange p.1.val p.2.val
    (componentAt (inc := BagEdge.Incident) (p.1.val ∪ p.2.val) i)))^2 ≤ _
  unfold componentAt
  split_ifs with h
  · exact component_cell_bound p f (componentOrder (p.1.val ∪ p.2.val) ⟨i,h⟩).property
  · rw [exchange_empty, sub_self, zero_pow (by decide : 2≠0)]
    exact add_nonneg (mul_nonneg (by positivity) (longCellCost_nonneg p f)) (colorCost_nonneg p.1 f)

lemma sum_componentDifference_bound
    (p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))
    (f : Finset (BagEdge bags) → ℝ) :
    (∑ i ∈ Finset.range (Fintype.card V), (componentDifference (fun A => f A.val) p i)^2) ≤
      (Fintype.card V : ℝ) *
        (3 * (Fintype.card V : ℝ) * longCellCost (hbags := hbags) (hG := hG) p f + colorCost p.1 f) := by
  have h := Finset.sum_le_sum (s := Finset.range (Fintype.card V))
    (fun i _ => componentDifference_cell_bound (hbags := hbags) (hG := hG) p f i)
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using h

attribute [local instance] OAI.MatchingFPRAS.Transport.CellDemands.instFintypeBagEdge_7
lemma sum_demand_eq (ρ : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)) → ℝ)
    (f : Finset (BagEdge bags) → ℝ) :
    (∑ d : Demand hbags hG, ρ d.1 * d.cellCost f) =
      ∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
        ρ p * longCellCost (hbags := hbags) (hG := hG) p f := by
  classical
  rw [arbitrary_sigma_sum]
  simp_rw [arbitrary_sigma_sum]
  simp only [longCellCost,Finset.mul_sum]

theorem variance_cell_demand_bound (w : BagEdge bags → ℝ) (hw : ∀ e, 0 < w e)
    (M : PM (BagEdge.Incident (bags := bags))) (f : Finset (BagEdge bags) → ℝ) :
    (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
        gibbs w p.1 * gibbs w p.2 * (f p.1.val-f p.2.val)^2) / 2 ≤
      3 * (Fintype.card V : ℝ)^3 *
        (∑ d : Demand hbags hG, gibbs w d.1.1 * gibbs w d.1.2 * d.cellCost f) +
      (Fintype.card V : ℝ)^2 * ∑ A : PM (BagEdge.Incident (bags := bags)), gibbs w A * colorCost A f := by
  classical
  have hv := cycle_demand_variance BagEdge.exists_incident w hw (fun A => f A.val)
  have hs := Finset.sum_le_sum
    (s := (Finset.univ : Finset (PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)))))
    (fun p _ => mul_le_mul_of_nonneg_left (sum_componentDifference_bound (hbags := hbags) (hG := hG) p f)
      (mul_nonneg (le_of_lt (gibbs_pos w hw p.1)) (le_of_lt (gibbs_pos w hw p.2))))
  have h := hv.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (Fintype.card V)))
  rw [sum_demand_eq (fun p => gibbs w p.1 * gibbs w p.2) f]
  have hc : (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
      gibbs w p.1 * gibbs w p.2 * colorCost p.1 f) =
        ∑ A : PM (BagEdge.Incident (bags := bags)), gibbs w A * colorCost A f := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro A _
    calc
      _ = (gibbs w A * colorCost A f) * ∑ B : PM (BagEdge.Incident (bags := bags)), gibbs w B := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro B _
        ring
      _ = _ := by rw [gibbs_sum w hw M,mul_one]
  have halgebra : (Fintype.card V : ℝ) *
      (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
        gibbs w p.1 * gibbs w p.2 * ((Fintype.card V : ℝ) *
          (3 * (Fintype.card V : ℝ) * longCellCost (hbags := hbags) (hG := hG) p f + colorCost p.1 f))) =
      3 * (Fintype.card V : ℝ)^3 *
        (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
          gibbs w p.1 * gibbs w p.2 * longCellCost (hbags := hbags) (hG := hG) p f) +
      (Fintype.card V : ℝ)^2 *
        (∑ p : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags)),
          gibbs w p.1 * gibbs w p.2 * colorCost p.1 f) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [halgebra,hc] at h
  exact h

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (hG : G.IsAcyclic)

namespace BagEdge

omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
lemma verticesColor_injective : Function.Injective (verticesColor (bags := bags)) := by
  intro e f h
  have h₁ : e.endpointPair.1 = f.endpointPair.1 := congrArg Sigma.fst h
  have h₂ : e.endpointPair.2 = f.endpointPair.2 := congrArg (fun p => p.2.1) h
  have h₃ : e.color = f.color := congrArg (fun p => p.2.2.val) h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rw [e.endpointPair_eq,f.endpointPair_eq,h₁,h₂]
  · exact h₃

end BagEdge

attribute [local instance] OAI.MatchingFPRAS.Transport.endpointPairBagEdgeFintype
include hbags hG in
omit [DecidableEq V] [DecidableEq L] in
lemma bag_edges_card_le : Fintype.card (BagEdge bags) ≤ 2 * Fintype.card V ^ 2 := by
  classical
  calc
    _ ≤ Fintype.card (Σ v : V, V × ↥(bags v)) := Fintype.card_le_of_injective BagEdge.verticesColor BagEdge.verticesColor_injective
    _ = ∑ v : V, Fintype.card V * (bags v).card := by simp only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_coe]
    _ ≤ ∑ _v : V, Fintype.card V * 2 :=
      Finset.sum_le_sum (fun v _ => Nat.mul_le_mul_left _ (label_memberships_le_two hbags hG v))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul]; ring

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] in
lemma SafeSwitch.weight_ratio {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ}
    {A B : PM inc} (h : SafeSwitch w K A B) : matchingWeight w A ≤ K^2 * matchingWeight w B := by
  classical
  obtain ⟨v,e,R,hv,he,hA,hB,hcomp⟩ := h
  have hne (i j : Fin 4) (hij : i ≠ j) (hij' : i ≠ j+1) : e i ≠ e j := by
    intro h
    have hi := (he i (v i)).mpr (Or.inl rfl)
    rw [h] at hi
    rcases (he j (v i)).mp hi with h | h
    · exact hij (hv h)
    · exact hij' (hv h)
  have h01 : e 0 ≠ e 1 := hne 0 1 (by decide) (by decide)
  have h23 : e 2 ≠ e 3 := hne 2 3 (by decide) (by decide)
  have h02 : e 0 ≠ e 2 := hne 0 2 (by decide) (by decide)
  have h13 : e 1 ≠ e 3 := hne 1 3 (by decide) (by decide)
  have hRA : R ⊆ A.val := by rw [hA]; exact Finset.subset_union_left
  have hRB : R ⊆ B.val := by rw [hB]; exact Finset.subset_union_left
  have ha0 : e 0 ∈ A.val := by rw [hA]; simp
  have ha2 : e 2 ∈ A.val := by rw [hA]; simp
  have hb1 : e 1 ∈ B.val := by rw [hB]; simp
  have hb3 : e 3 ∈ B.val := by rw [hB]; simp
  have hr0 : e 0 ∉ R := by
    intro hr
    exact h01 (B.property.unique (Finset.mem_univ (v 1)) (hRB hr)
      ((he 0 (v 1)).mpr (Or.inr rfl)) hb1 ((he 1 (v 1)).mpr (Or.inl rfl)))
  have hr1 : e 1 ∉ R := by
    intro hr
    exact h01 (A.property.unique (Finset.mem_univ (v 1)) ha0
      ((he 0 (v 1)).mpr (Or.inr rfl)) (hRA hr) ((he 1 (v 1)).mpr (Or.inl rfl)))
  have hr2 : e 2 ∉ R := by
    intro hr
    exact h23 (B.property.unique (Finset.mem_univ (v 3)) (hRB hr)
      ((he 2 (v 3)).mpr (Or.inr rfl)) hb3 ((he 3 (v 3)).mpr (Or.inl rfl)))
  have hr3 : e 3 ∉ R := by
    intro hr
    exact h23 (A.property.unique (Finset.mem_univ (v 3)) ha2
      ((he 2 (v 3)).mpr (Or.inr rfl)) (hRA hr) ((he 3 (v 3)).mpr (Or.inl rfl)))
  have hdA : Disjoint R {e 0,e 2} := by
    simp only [Finset.disjoint_insert_right,Finset.disjoint_singleton_right]
    exact ⟨hr0,hr2⟩
  have hdB : Disjoint R {e 1,e 3} := by
    simp only [Finset.disjoint_insert_right,Finset.disjoint_singleton_right]
    exact ⟨hr1,hr3⟩
  have hp := mul_le_mul (hcomp 0 1) (hcomp 2 3) (le_of_lt (hw (e 2)))
    (le_trans (le_of_lt (hw (e 0))) (hcomp 0 1))
  have hr : 0 ≤ ∏ a ∈ R, w a := Finset.prod_nonneg (fun a _ => le_of_lt (hw a))
  have h := mul_le_mul_of_nonneg_left hp hr
  simp only [matchingWeight,hA,hB,Finset.prod_union hdA,Finset.prod_union hdB,
    Finset.prod_pair h02,Finset.prod_pair h13]
  nlinarith only [h]

omit [DecidableEq V] in
lemma SafeSwitch.gibbs_ratio {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ}
    {A B : PM inc} (h : SafeSwitch w K A B) : gibbs w A ≤ K^2 * gibbs w B := by
  dsimp only [gibbs]
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (h.weight_ratio hw) (le_of_lt (partition_pos w hw A))

omit [DecidableEq V] in
lemma SafeSwitch.min_capacity {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ} (hK : 1 ≤ K)
    {A B : PM inc} (h : SafeSwitch w K A B) : gibbs w A ≤ K^2 * min (gibbs w A) (gibbs w B) := by
  rw [mul_min_of_nonneg _ _ (sq_nonneg K)]
  apply le_min
  · have hp := le_of_lt (gibbs_pos w hw A)
    have hsq : 1 ≤ K^2 := by nlinarith
    nlinarith
  · exact h.gibbs_ratio hw

end

section

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

omit [DecidableEq V] [Fintype E] in
lemma ColorChange.weight_ratio {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ} (hK : 1 ≤ K)
    (hcomp : ∀ e f, ends e = ends f → w e ≤ K*w f)
    {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    matchingWeight w A ≤ K * matchingWeight w B := by
  classical
  obtain ⟨e,f,R,hef,hA,hB⟩ := h
  by_cases heq : e = f
  · have hAB : A = B := Subtype.ext (by rw [hA,hB,heq])
    subst B
    have hp := le_of_lt (matchingWeight_pos w hw A)
    nlinarith
  · obtain ⟨v,hv⟩ : ∃ v, v ∈ ends e := by
      induction ends e using Sym2.inductionOn with | hf a b => exact ⟨a,by simp⟩
    have hRA : R ⊆ A.val := by rw [hA]; exact Finset.subset_union_left
    have hRB : R ⊆ B.val := by rw [hB]; exact Finset.subset_union_left
    have hae : e ∈ A.val := by rw [hA]; simp
    have hbf : f ∈ B.val := by rw [hB]; simp
    have hre : e ∉ R := by
      intro hr
      exact heq (B.property.unique (Finset.mem_univ v) (hRB hr) hv hbf (hef ▸ hv))
    have hrf : f ∉ R := by
      intro hr
      exact heq (A.property.unique (Finset.mem_univ v) hae hv (hRA hr) (hef ▸ hv))
    have hdA : Disjoint R {e} := Finset.disjoint_singleton_right.mpr hre
    have hdB : Disjoint R {f} := Finset.disjoint_singleton_right.mpr hrf
    have hr : 0 ≤ ∏ a ∈ R, w a := Finset.prod_nonneg (fun a _ => le_of_lt (hw a))
    have h := mul_le_mul_of_nonneg_left (hcomp e f hef) hr
    simp only [matchingWeight,hA,hB,Finset.prod_union hdA,Finset.prod_union hdB,Finset.prod_singleton]
    nlinarith only [h]

omit [DecidableEq V] in
lemma ColorChange.min_capacity {w : E → ℝ} (hw : ∀ e, 0 < w e) {K : ℝ} (hK : 1 ≤ K)
    (hcomp : ∀ e f, ends e = ends f → w e ≤ K*w f)
    {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    gibbs w A ≤ K * min (gibbs w A) (gibbs w B) := by
  rw [mul_min_of_nonneg _ _ (by linarith : 0 ≤ K)]
  apply le_min
  · have hp := le_of_lt (gibbs_pos w hw A)
    nlinarith
  · dsimp only [gibbs]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (h.weight_ratio ends hw hK hcomp)
      (le_of_lt (partition_pos w hw A))

end

section

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo)

include hbags hheight hstep hD hw hlo in
omit [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L] in
lemma color_clamp_comparability (e f : BagEdge bags) (hef : e.val.val.1 = f.val.val.1) :
    max lo (min hi (w e)) ≤ (1000*D) * max lo (min hi (w f)) := by
  obtain ⟨v,hev⟩ := BagEdge.exists_incident e
  have hfv : f.Incident v := by
    change v ∈ f.val.val.1
    rw [← hef]
    exact hev
  have hc := hbags v _ (BagEdge.color_mem e hev) _ (BagEdge.color_mem f hfv)
  have hh : height e.color ≤ 2 * height f.color := by
    rcases hc with h | h
    · rw [h]; nlinarith [hheight f.color]
    · exact hstep _ _ h
  have hDpos : 0 < D := by linarith
  have hfpos : 0 < w f := lt_of_lt_of_le (div_pos (hheight f.color) hDpos) (hw f).1
  have hlow : height f.color ≤ w f * D := (div_le_iff₀ hDpos).mp (hw f).1
  apply IndexedCycle.common_clamp_ratio (le_of_lt hlo) (by linarith)
  nlinarith [(hw e).2,mul_pos hDpos hfpos]

end

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] in
lemma SafeSwitch.legal {w : E → ℝ} {K : ℝ} {A B : PM inc} (h : SafeSwitch w K A B) :
    TwoEdgeSwitch A B := by
  obtain ⟨v,e,R,hv,he,hA,hB,_⟩ := h
  exact ⟨v,e,R,hv,he,hA,hB⟩

omit [DecidableEq V] [Fintype E] in
lemma TwoEdgeSwitch.two_le {A B : PM inc} (h : TwoEdgeSwitch A B) : 2 ≤ A.val.card := by
  classical
  obtain ⟨v,e,R,hv,he,hA,hB⟩ := h
  have h02 : e 0 ≠ e 2 := by
    intro h
    have h0 := (he 0 (v 0)).mpr (Or.inl rfl)
    rw [h] at h0
    rcases (he 2 (v 0)).mp h0 with h | h
    · have := hv h; exact (by decide : (0:Fin 4) ≠ 2) this
    · have := hv h; exact (by decide : (0:Fin 4) ≠ 2+1) this
  have hs : {e 0,e 2} ⊆ A.val := by rw [hA]; exact Finset.subset_union_right
  simpa only [Finset.card_pair h02] using Finset.card_le_card hs

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma PM.card_le_vertices (hinc : ∀ e, ∃ v, inc e v) (A : PM inc) : A.val.card ≤ Fintype.card V := by
  classical
  let vertex : ↥A.val → V := fun e => Classical.choose (hinc e.val)
  have hv (e : ↥A.val) : inc e.val (vertex e) := Classical.choose_spec (hinc e.val)
  have hinj : Function.Injective vertex := by
    intro e f h
    apply Subtype.ext
    exact A.property.unique (Finset.mem_univ (vertex e)) e.property (hv e) f.property (h ▸ hv f)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective vertex hinj

variable (ends : E → Sym2 V)

lemma scale_div_lower {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 < a) (hab : a ≤ b) :
    x ≤ b * (x/a) := by
  calc
    x = a * (x/a) := by field_simp [ne_of_gt ha]
    _ ≤ b * (x/a) := mul_le_mul_of_nonneg_right hab (div_nonneg hx (le_of_lt ha))

omit [DecidableEq V] in
lemma switchDirichlet_nonneg (w : E → ℝ) (hw : ∀ e, 0 < w e) (f : Finset E → ℝ) :
    0 ≤ switchDirichlet (inc := inc) w f := by
  apply Finset.sum_nonneg
  intro A _
  apply Finset.sum_nonneg
  intro B _
  exact div_nonneg (mul_nonneg (le_min (le_of_lt (gibbs_pos w hw A))
    (le_of_lt (gibbs_pos w hw B))) (sq_nonneg _)) (by positivity)

omit [DecidableEq V] in
lemma colorDirichlet_nonneg (w : E → ℝ) (hw : ∀ e, 0 < w e) (f : Finset E → ℝ) :
    0 ≤ colorDirichlet ends w f := by
  apply Finset.sum_nonneg
  intro A _
  apply Finset.sum_nonneg
  intro B _
  exact div_nonneg (mul_nonneg (le_min (le_of_lt (gibbs_pos w hw A))
    (le_of_lt (gibbs_pos w hw B))) (sq_nonneg _)) (by positivity)

omit [DecidableEq V] in
lemma cycleDirichlet_nonneg (w : E → ℝ) (hw : ∀ e, 0 < w e) (f g : Finset E → ℝ) :
    0 ≤ cycleDirichlet (inc := inc) w f g := by
  apply Finset.sum_nonneg
  intro A _
  apply Finset.sum_nonneg
  intro B _
  apply mul_nonneg (mul_nonneg (le_of_lt (gibbs_pos w hw A)) (le_of_lt (gibbs_pos w hw B)))
  exact Finset.sum_nonneg (fun S _ => div_nonneg (sq_nonneg _) (by positivity))

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Variance
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma switch_denominator_bound (hinc : ∀ e, ∃ v, inc e v) (A : PM inc) :
    48 * (A.val.card.choose 2 : ℝ) ≤ 60 * (Fintype.card V : ℝ)^2 := by
  have hm := A.card_le_vertices hinc
  have hc : A.val.card.choose 2 ≤ (Fintype.card V)^2 :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hm 2)
  have hc' : (A.val.card.choose 2 : ℝ) ≤ (Fintype.card V : ℝ)^2 := by exact_mod_cast hc
  nlinarith [sq_nonneg (Fintype.card V : ℝ)]

omit [DecidableEq V] in
lemma safe_switch_elementary (hinc : ∀ e, ∃ v, inc e v)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (K : ℝ) (hK : 1 ≤ K) (f : Finset E → ℝ) :
    (∑ A : PM inc, gibbs w A * ∑ B ∈ safeDestinations w K A, (f A.val-f B.val)^2) ≤
      60 * (Fintype.card V : ℝ)^2 * K^2 * switchDirichlet (inc := inc) w f := by
  classical
  simp only [switchDirichlet,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  let term (B : PM inc) := 60*(Fintype.card V : ℝ)^2*K^2 *
    (min (gibbs w A) (gibbs w B)*(f A.val-f B.val)^2 / (48*(A.val.card.choose 2 : ℝ)))
  change (∑ B ∈ safeDestinations w K A, gibbs w A*(f A.val-f B.val)^2) ≤
    ∑ B ∈ switchDestinations A, term B
  calc
    _ ≤ ∑ B ∈ safeDestinations w K A, term B := by
      apply Finset.sum_le_sum
      intro B hB
      have h : SafeSwitch w K A B := (Finset.mem_filter.mp hB).2
      have hd : 0 < 48 * (A.val.card.choose 2 : ℝ) := by
        have hc : 0 < A.val.card.choose 2 := Nat.choose_pos h.legal.two_le
        positivity
      have hn : 0 ≤ min (gibbs w A) (gibbs w B) * (f A.val-f B.val)^2 :=
        mul_nonneg (le_min (le_of_lt (gibbs_pos w hw A)) (le_of_lt (gibbs_pos w hw B))) (sq_nonneg _)
      have h₁ := mul_le_mul_of_nonneg_right (h.min_capacity hw hK) (sq_nonneg (f A.val-f B.val))
      have h₂ := mul_le_mul_of_nonneg_left (scale_div_lower hn hd (switch_denominator_bound hinc A)) (sq_nonneg K)
      dsimp only [term]
      nlinarith only [h₁,h₂]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro B hB
        have h : SafeSwitch w K A B := (Finset.mem_filter.mp hB).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.legal⟩
      · intro B _ _
        have ha := le_of_lt (gibbs_pos w hw A)
        have hb := le_of_lt (gibbs_pos w hw B)
        dsimp only [term]
        positivity

variable (ends : E → Sym2 V)

omit [DecidableEq V] [Fintype E] in
lemma ColorChange.card_pos {A B : PM (fun e v => v ∈ ends e)} (h : ColorChange ends A B) :
    0 < A.val.card := by
  obtain ⟨e,f,R,hef,hA,hB⟩ := h
  exact Finset.card_pos.mpr ⟨e,by rw [hA]; simp⟩

omit [DecidableEq V] in
lemma color_elementary (w : E → ℝ) (hw : ∀ e, 0 < w e) (K : ℝ) (hK : 1 ≤ K)
    (hcomp : ∀ e f, ends e = ends f → w e ≤ K*w f) (f : Finset E → ℝ) :
    (∑ A : PM (fun e v => v ∈ ends e), gibbs w A *
      ∑ B ∈ colorDestinations ends A, (f A.val-f B.val)^2) ≤
      12 * (Fintype.card V : ℝ) * K * colorDirichlet ends w f := by
  classical
  have hinc (e : E) : ∃ v, v ∈ ends e := by
    induction ends e using Sym2.inductionOn with | hf a b => exact ⟨a,by simp⟩
  simp only [colorDirichlet,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  apply Finset.sum_le_sum
  intro B hB
  have h : ColorChange ends A B := (Finset.mem_filter.mp hB).2
  have hd : 0 < 12 * (A.val.card : ℝ) := by have := h.card_pos ends; positivity
  have hb : 12 * (A.val.card : ℝ) ≤ 12 * (Fintype.card V : ℝ) := by
    exact_mod_cast (Nat.mul_le_mul_left 12 (A.card_le_vertices hinc))
  have hn : 0 ≤ min (gibbs w A) (gibbs w B) * (f A.val-f B.val)^2 :=
    mul_nonneg (le_min (le_of_lt (gibbs_pos w hw A)) (le_of_lt (gibbs_pos w hw B))) (sq_nonneg _)
  have h₁ := mul_le_mul_of_nonneg_right (h.min_capacity ends hw hK hcomp) (sq_nonneg (f A.val-f B.val))
  have h₂ := mul_le_mul_of_nonneg_left (scale_div_lower hn hd hb) (by linarith : 0 ≤ K)
  nlinarith only [h₁,h₂]

omit [Fintype E] in
lemma cycleSquare_common (f g : Finset E → ℝ) (A B S : Finset E) (hS : S ⊆ A ∩ B) :
    cycleSquare f g A B S = 0 := by
  have hSA : S ⊆ A := fun e he => (Finset.mem_inter.mp (hS he)).1
  have hSB : S ⊆ B := fun e he => (Finset.mem_inter.mp (hS he)).2
  simp only [cycleSquare,exchange,Finset.inter_eq_right.mpr hSA,Finset.inter_eq_right.mpr hSB,
    Finset.sdiff_union_of_subset hSA,Finset.sdiff_union_of_subset hSB,sub_self,zero_pow (by decide : 2 ≠ 0)]

omit [DecidableEq V] [Fintype E] in
lemma all_cycleSquare_sum (f g : Finset E → ℝ) (A B : PM inc) :
    (∑ S ∈ components (inc := inc) (A.val ∪ B.val), cycleSquare f g A.val B.val S) =
      ∑ S ∈ discrepancyComponents A B, cycleSquare f g A.val B.val S := by
  classical
  apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro S hS hnot
  have hcommon : S ⊆ A.val ∩ B.val := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hS,h⟩)
  exact cycleSquare_common f g _ _ _ hcommon

omit [DecidableEq V] in
lemma cycle_elementary (hinc : ∀ e, ∃ v, inc e v)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (f g : Finset E → ℝ) :
    (∑ A : PM inc, ∑ B : PM inc, gibbs w A * gibbs w B *
      ∑ S ∈ components (inc := inc) (A.val ∪ B.val), cycleSquare f g A.val B.val S) ≤
      6 * (Fintype.card V : ℝ) * cycleDirichlet (inc := inc) w f g := by
  classical
  simp only [cycleDirichlet,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  apply Finset.sum_le_sum
  intro B _
  rw [← Finset.mul_sum,all_cycleSquare_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hcard : 0 < (discrepancyComponents A B).card := Finset.card_pos.mpr ⟨S,hS⟩
  have hd : (discrepancyComponents A B).card ≤ Fintype.card V :=
    (Finset.card_filter_le _ _).trans (components_card_le hinc _)
  have hb : 6 * ((discrepancyComponents A B).card : ℝ) ≤ 6 * (Fintype.card V : ℝ) := by exact_mod_cast Nat.mul_le_mul_left 6 hd
  have hscale := scale_div_lower (sq_nonneg ((f A.val+g B.val)-(f (exchange A.val B.val S)+g (exchange B.val A.val S))))
    (by positivity : 0 < 6 * ((discrepancyComponents A B).card : ℝ)) hb
  have h := mul_le_mul_of_nonneg_left hscale
    (mul_nonneg (le_of_lt (gibbs_pos w hw A)) (le_of_lt (gibbs_pos w hw B)))
  dsimp only [cycleSquare] at *
  nlinarith only [h]

end MatchingFPRAS.Transport

namespace MatchingFPRAS.FiniteVariance

variable {Ω : Type*} [Fintype Ω]

lemma variance_eq_pair (π f : Ω → ℝ) (hπ : ∑ x, π x = 1) :
    variance π f = (∑ p : Ω × Ω, π p.1 * π p.2 * (f p.1-f p.2)^2) / 2 := by
  let m := ∑ y, π y * f y
  let s := ∑ y, π y * f y ^ 2
  have hl : variance π f = s-m^2 := by
    unfold variance
    change (∑ x, π x * (f x-m)^2) = s-m^2
    calc
      _ = ∑ x, (π x * f x^2 - 2*m*(π x*f x) + m^2*π x) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = s-m^2 := by
        rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hπ]
        change s-2*m*m+m^2*1 = s-m^2
        ring
  have hr : (∑ p : Ω × Ω, π p.1 * π p.2 * (f p.1-f p.2)^2) = 2*(s-m^2) := by
    rw [Fintype.sum_prod_type]
    have hin (x : Ω) : (∑ y, π x*π y*(f x-f y)^2) = π x*f x^2-2*m*(π x*f x)+s*π x := by
      calc
        _ = ∑ y, ((π x*f x^2)*π y - (2*π x*f x)*(π y*f y) + π x*(π y*f y^2)) := by
          apply Finset.sum_congr rfl
          intro y _
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hπ]
          change (π x*f x^2)*1-(2*π x*f x)*m+π x*s = _
          ring
    simp_rw [hin]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hπ]
    change s-2*m*m+s*1 = 2*(s-m^2)
    ring
  rw [hl,hr]
  ring

end MatchingFPRAS.FiniteVariance

namespace MatchingFPRAS

lemma energy_coefficient_bound {N D T : ℝ} (hN1 : 1 ≤ N) (hD : 1 ≤ D)
    (hT0 : 0 ≤ T) (htag : T ≤ (10*N)^30) :
    180*N^5*(1000*D)^6*T+72*N^4*(1000*D)^4*T+12*N^3*(1000*D) ≤
      ((10^4 : ℝ)*N*D)^100 := by
  let K := 1000*D
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hN0 : 0 ≤ N := by linarith
  have hDN : N ≤ N*D := by nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hD)]
  have hDD : D ≤ N*D := by nlinarith [mul_nonneg (sub_nonneg.mpr hN1) (le_trans (by norm_num : (0:ℝ) ≤ 1) hD)]
  let B := (10^4 : ℝ)*N*D
  have hB : 3 ≤ B := by dsimp [B]; nlinarith
  have hNB : N ≤ B := by dsimp [B]; nlinarith
  have hKB : K ≤ B := by dsimp [B,K]; nlinarith
  have h10NB : 10*N ≤ B := by dsimp [B]; nlinarith
  have hTB : T ≤ B^30 := htag.trans (by gcongr)
  have h180 : (180:ℝ) ≤ B := by dsimp [B]; nlinarith
  have h72 : (72:ℝ) ≤ B := by linarith
  have h12 : (12:ℝ) ≤ B := by linarith
  have hb0 : 0 ≤ B := by linarith
  have hterm1 : 180*N^5*K^6*T ≤ B^42 := by
    calc
      _ ≤ B*B^5*B^6*B^30 := by gcongr
      _ = _ := by ring
  have hterm2 : 72*N^4*K^4*T ≤ B^39 := by
    calc
      _ ≤ B*B^4*B^4*B^30 := by gcongr
      _ = _ := by ring
  have hterm3 : 12*N^3*K ≤ B^5 := by
    calc
      _ ≤ B*B^3*B := by gcongr
      _ = _ := by ring
  have hp39 : B^39 ≤ B^42 := pow_le_pow_right₀ (by linarith : 1 ≤ B) (by omega)
  have hp5 : B^5 ≤ B^42 := pow_le_pow_right₀ (by linarith : 1 ≤ B) (by omega)
  have hcoef : 180*N^5*K^6*T+72*N^4*K^4*T+12*N^3*K ≤ B^100 := by
    calc
      _ ≤ 3*B^42 := by linarith
      _ ≤ B*B^42 := mul_le_mul_of_nonneg_right hB (pow_nonneg hb0 _)
      _ = B^43 := by ring
      _ ≤ B^100 := pow_le_pow_right₀ (by linarith : 1 ≤ B) (by omega)
  exact hcoef

end MatchingFPRAS

namespace MatchingFPRAS.Transport.CellDemands

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

variable (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)

include hheight hstep hD hw hlo hlohi hbags hG

attribute [local instance] OAI.MatchingFPRAS.Transport.CellDemands.instFintypeBagEdge_8
theorem pair_energy_inequality (hN : 2 ≤ Fintype.card V)
    (M : PM (BagEdge.Incident (bags := bags))) (f g : Finset (BagEdge bags) → ℝ) :
    let wt := fun e => max lo (min hi (w e))
    MatchingFPRAS.FiniteVariance.variance (gibbs (inc := BagEdge.Incident) wt) (fun A => f A.val) ≤
      ((10^4 : ℝ) * Fintype.card V * D)^100 *
        pairDirichlet (fun e : BagEdge bags => e.val.val.1) wt f g := by
  classical
  let wt := fun e => max lo (min hi (w e))
  have hwt (e : BagEdge bags) : 0 < wt e := lt_of_lt_of_le hlo (le_max_left _ _)
  let N : ℝ := Fintype.card V
  let K : ℝ := 1000*D
  let T : ℝ := Fintype.card (DemandTag (V := V) (E := BagEdge bags))
  let E := pairDirichlet (fun e : BagEdge bags => e.val.val.1) wt f g
  have hK : 1 ≤ K := by dsimp [K]; linarith
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  have hE : 0 ≤ E := by
    exact add_nonneg (add_nonneg (switchDirichlet_nonneg wt hwt f)
      (colorDirichlet_nonneg _ wt hwt f)) (cycleDirichlet_nonneg wt hwt f g)
  have hsE : switchDirichlet (inc := BagEdge.Incident) wt f ≤ E :=
    (le_add_of_nonneg_right (colorDirichlet_nonneg (fun e : BagEdge bags => e.val.val.1) wt hwt f)).trans
      (le_add_of_nonneg_right (cycleDirichlet_nonneg wt hwt f g))
  have hcE : colorDirichlet (fun e : BagEdge bags => e.val.val.1) wt f ≤ E :=
    (le_add_of_nonneg_left (switchDirichlet_nonneg (inc := BagEdge.Incident) wt hwt f)).trans
      (le_add_of_nonneg_right (cycleDirichlet_nonneg wt hwt f g))
  have hyE : cycleDirichlet (inc := BagEdge.Incident) wt f g ≤ E :=
    le_add_of_nonneg_left (add_nonneg (switchDirichlet_nonneg wt hwt f)
      (colorDirichlet_nonneg (fun e : BagEdge bags => e.val.val.1) wt hwt f))
  have hs := (safe_switch_elementary BagEdge.exists_incident wt hwt K hK f).trans
    (mul_le_mul_of_nonneg_left hsE (by positivity : 0 ≤ 60*N^2*K^2))
  have hc := (color_elementary (fun e : BagEdge bags => e.val.val.1) wt hwt K hK
    (color_clamp_comparability hbags height hheight hstep D hD w hw lo hi hlo) f).trans
    (mul_le_mul_of_nonneg_left hcE (by positivity : 0 ≤ 12*N*K))
  have hy := (cycle_elementary BagEdge.exists_incident wt hwt f g).trans
    (mul_le_mul_of_nonneg_left hyE (by positivity : 0 ≤ 6*N))
  have hl := total_cell_demand_load (hbags := hbags) (hG := hG) height hheight hstep D hD w hw lo hi hlo hlohi M f g
  change (∑ d : Demand hbags hG, gibbs wt d.1.1 * gibbs wt d.1.2 * d.cellCost f) ≤
    K^4*T*((∑ A : PM BagEdge.Incident, gibbs wt A *
      ∑ B ∈ safeDestinations wt K A, (f A.val-f B.val)^2) + 4*
      ∑ A : PM BagEdge.Incident, ∑ B : PM BagEdge.Incident, gibbs wt A*gibbs wt B*
      ∑ S ∈ components (inc := BagEdge.Incident) (A.val∪B.val), cycleSquare f g A.val B.val S) at hl
  have hload := hl.trans (mul_le_mul_of_nonneg_left (add_le_add hs (mul_le_mul_of_nonneg_left hy (by norm_num)))
    (by dsimp [T]; positivity : 0 ≤ K^4*T))
  have hv := variance_cell_demand_bound (hbags := hbags) (hG := hG) wt hwt M f
  have hvar := hv.trans (add_le_add (mul_le_mul_of_nonneg_left hload (by positivity : 0 ≤ 3*N^3))
    (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ N^2)))
  have hraw : MatchingFPRAS.FiniteVariance.variance (gibbs (inc := BagEdge.Incident) wt) (fun A => f A.val) ≤
      (180*N^5*K^6*T+72*N^4*K^4*T+12*N^3*K)*E := by
    rw [MatchingFPRAS.FiniteVariance.variance_eq_pair _ _ (gibbs_sum wt hwt M)]
    calc
      _ ≤ _ := hvar
      _ = _ := by ring
  have htag : T ≤ (10*N)^30 := by
    have h := tag_card_bound (V := V) (E := BagEdge bags) (Fintype.card V) hN le_rfl (bag_edges_card_le hbags hG)
    dsimp only [T,N]
    exact_mod_cast h
  have hT0 : 0 ≤ T := Nat.cast_nonneg _
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ Fintype.card V by omega)
  have hcoef := MatchingFPRAS.energy_coefficient_bound hN1 hD hT0 htag
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoef hE)

end MatchingFPRAS.Transport.CellDemands

namespace MatchingFPRAS.Transport

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬(ends e).IsDiag)

include hloop

omit [Fintype E] [DecidableEq E] in
lemma PM.card_eq (A B : PM (fun e v => v ∈ ends e)) : A.val.card = B.val.card := by
  have ha := A.twice_card ends hloop
  have hb := B.twice_card ends hloop
  omega

omit hloop

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma matchingWeight_compare {w z : E → ℝ} (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (_hc : 0 ≤ c) (h : ∀ e, w e ≤ c*z e)
    (A : PM (fun e v => v ∈ ends e)) :
    matchingWeight w A ≤ c^A.val.card*matchingWeight z A := by
  calc
    _ ≤ ∏ e ∈ A.val, c*z e := Finset.prod_le_prod (fun edge _ => hw edge) (fun edge _ => h edge)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const]; rfl

include hloop

omit [DecidableEq E] in
lemma partition_compare {w z : E → ℝ} (hw : ∀ e, 0 ≤ w e)
    (c : ℝ) (hc : 0 ≤ c) (h : ∀ e, w e ≤ c*z e)
    (A : PM (fun e v => v ∈ ends e)) :
    partition (inc := fun e v => v ∈ ends e) w ≤
      c^A.val.card*partition (inc := fun e v => v ∈ ends e) z := by
  classical
  unfold partition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro B _
  have hh := matchingWeight_compare ends hw c hc h B
  rwa [PM.card_eq ends hloop B A] at hh

omit [DecidableEq E] in
lemma gibbs_compare {w z : E → ℝ} (hw : ∀ e, 0 < w e) (hz : ∀ e, 0 < z e)
    (c : ℝ) (hc : 0 ≤ c) (hwz : ∀ e, w e ≤ c*z e) (hzw : ∀ e, z e ≤ c*w e)
    (A : PM (fun e v => v ∈ ends e)) :
    gibbs w A ≤ c^(Fintype.card V)*gibbs z A := by
  have hwa := matchingWeight_compare ends (fun e => (hw e).le) c hc hwz A
  have hpz := partition_compare ends hloop (fun e => (hz e).le) c hc hzw A
  have hprod := mul_le_mul hwa hpz (le_of_lt (partition_pos z hz A))
    (mul_nonneg (pow_nonneg hc _) (matchingWeight_pos z hz A).le)
  have he : c^A.val.card*c^A.val.card = c^(Fintype.card V) := by
    rw [← pow_add,← A.twice_card ends hloop]
    congr 1; omega
  have hh : matchingWeight w A*partition (inc := fun e v => v ∈ ends e) z ≤
      c^(Fintype.card V)*matchingWeight z A*partition (inc := fun e v => v ∈ ends e) w := by
    calc
      _ ≤ (c^A.val.card*matchingWeight z A)*(c^A.val.card*partition (inc := fun e v => v ∈ ends e) w) := hprod
      _ = _ := by rw [← he]; ring
  unfold gibbs
  rw [← mul_div_assoc,div_le_div_iff₀ (partition_pos w hw A) (partition_pos z hz A)]
  exact hh

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_MatchingMap
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

variable [DecidableEq V] [DecidableEq E] [DecidableEq F]

variable (inc : E → V → Prop) (inc' : F → V → Prop) (f : E ↪ F)

variable (hinc : ∀ e x,inc' (f e) x ↔ inc e x)

lemma matchingMap_injective (U : Finset V) : Function.Injective (matchingMap inc inc' f hinc U) := by
  intro a b h
  apply Subtype.ext
  exact Finset.map_injective f (congrArg Subtype.val h)

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_on [Fintype F] [DecidableEq E] (w : E → ℝ) (e : E) : edgeExtension f w (f e)=w e := by
  classical
  unfold edgeExtension
  rw [dite_eq_left ⟨e,rfl⟩]
  exact congrArg w (f.injective (Exists.choose_spec (show ∃ e',f e'=f e from ⟨e,rfl⟩)))

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_off [Fintype F] [DecidableEq E] (w : E → ℝ) (q : F) (hq : ¬∃ e,f e=q) : edgeExtension f w q=0 := by
  classical
  simp [edgeExtension,hq]

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_nonneg [Fintype F] [DecidableEq E] (w : E → ℝ) (hw : ∀ e,0≤w e) (q : F) : 0≤edgeExtension f w q := by
  classical
  unfold edgeExtension
  split_ifs <;> first | exact hw _ | norm_num

lemma matchingMap_weight (w : E → ℝ) (U : Finset V) (M : Matchings inc U) :
    (∏ q∈(matchingMap inc inc' f hinc U M).val,edgeExtension f w q)=∏ e∈M.val,w e := by
  dsimp [matchingMap]
  rw [Finset.prod_map]
  simp_rw [edgeExtension_on]

include hinc in

theorem partition_embedding (w : E → ℝ) (U : Finset V) :
    partitionWeight inc' (edgeExtension f w) U=partitionWeight inc w U := by
  classical
  unfold partitionWeight
  symm
  apply Finset.sum_bij_ne_zero (fun M _ _ => matchingMap inc inc' f hinc U M)
  · intros; exact Finset.mem_univ _
  · intro a _ _ b _ _ h
    exact matchingMap_injective inc inc' f hinc U h
  · intro N _ hN
    have hr : ∀ q∈N.val,∃ e,f e=q := by
      intro q hq
      by_contra hn
      apply hN
      exact Finset.prod_eq_zero hq (edgeExtension_off f w q hn)
    let S := univ.filter fun e : E => f e∈N.val
    have hS : S.map f=N.val := by
      ext q
      constructor
      · intro hq
        obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hq
        exact (Finset.mem_filter.mp he).2
      · intro hq
        obtain ⟨e,rfl⟩ := hr q hq
        exact Finset.mem_map.mpr ⟨e,by simp [S,hq],rfl⟩
    let M : Matchings inc U := ⟨S,(matching_map_iff inc inc' f hinc S U).mp (hS.symm ▸ N.property)⟩
    have hM : matchingMap inc inc' f hinc U M=N := Subtype.ext hS
    refine ⟨M,Finset.mem_univ _,?_,hM⟩
    rw [←matchingMap_weight inc inc' f hinc w U M,hM]
    exact hN
  · intro M _ _
    exact (matchingMap_weight inc inc' f hinc w U M).symm

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags
lemma sourceRealPortion_partition (w : V → V → ℝ) (K : ℕ)
    (R : Finset V) (U : LogicalEdge V → Finset (Fin (4*(2*K+2)))) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) (survivors (4*(2*K+2)) R U)=
    realHolePartition source target (4*(2*K+2)) R U
      (pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
        (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w)) := by
  classical
  rw [show sourceRealPortion w K=edgeExtension (sourceRealEmbedding w K) (sourceRealActivity w K) from rfl]
  rw [partition_embedding (fun (q : SourceRealEdge V K) x => x∈edge source target (4*(2*K+2)) q.1 q.2)
    BagEdge.Incident (sourceRealEmbedding w K) (fun _ _ => Iff.rfl)]
  exact realMatching_partition source target (4*(2*K+2)) source_ne_target R U _

lemma sourceRealActivity_pos (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : SourceRealEdge V K) : 0 < sourceRealActivity w K e := by
  have hl : 0<logicalActivity w e.1 := by
    unfold logicalActivity edgeActivity
    split_ifs <;> exact hw _ _
  exact hl.trans_le (profile_lower _ _ _ _ _
    (edgeActivity_le_bottleneck w _ _ (source_ne_target e.1)) e.2)

lemma sourceRealPortion_nonneg (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : BagEdge (sourceBags w K)) : 0 ≤ sourceRealPortion w K e := by
  classical
  exact edgeExtension_nonneg _ _ (fun q => (sourceRealActivity_pos w hw K q).le) e

lemma sourceRealPortion_full (w : V → V → ℝ) (hz : 0<partition w ∅) (K : ℕ) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) univ =
      (∏ e, pathConstant (2*K+2) (bottleneck w (source e) (target e))
        (sourceHeight w (source e)) (sourceHeight w (target e))) * partition w ∅ := by
  rw [←survivors_empty (V := V) K,sourceRealPortion_partition]
  exact intact_partition_identity w hz _ _ _ _

lemma sourceRealPortion_full_pos (w : V → V → ℝ) (hz : 0<partition w ∅) (K : ℕ) :
    0<partitionWeight BagEdge.Incident (sourceRealPortion w K) univ := by
  rw [sourceRealPortion_full w hz K]
  apply mul_pos _ hz
  exact Finset.prod_pos fun e _ => pathConstant_pos _ _ _ _
    (zero_lt_one.trans_le (one_le_bottleneck w _ _))



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance instDecidableEqSourceLabel_1_r3ec436_1 (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
lemma bagHeight_one (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : 1 ≤ bagHeight w K l := by
  exact one_le_pow₀ (by norm_num)

lemma bagHeight_pos (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : 0 < bagHeight w K l :=
  zero_lt_one.trans_le (bagHeight_one w K l)

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable (p : I → Ω → ℝ)

lemma dot_comm (f g : (I → Ω) → ℝ) : dot p f g = dot p g f := by
  unfold dot; apply Finset.sum_congr rfl; intro s _; ring

lemma dot_zero_left (f : (I → Ω) → ℝ) : dot p 0 f = 0 := by simp [dot]

lemma dot_const_left (c : ℝ) (g : (I → Ω) → ℝ) :
    dot p (fun _ => c) g = c * dot p (fun _ => 1) g := by
  simp only [dot, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _; ring

lemma dot_nonneg (hp : ∀ i a, 0 ≤ p i a) (f : (I → Ω) → ℝ) : 0 ≤ dot p f f := by
  apply Finset.sum_nonneg
  intro s _
  have hh : 0 ≤ density p s := Finset.prod_nonneg (fun i _ => hp i (s i))
  nlinarith [mul_nonneg hh (sq_nonneg (f s))]

namespace Projection

variable {p}

lemma dot_image (P : Projection p) (f : (I → Ω) → ℝ) :
    dot p f (P.op f) = dot p (P.op f) (P.op f) := by
  rw [P.adj, P.idem]

end Projection

omit [Fintype I] in
lemma average_list_mem (hp : ∀ i, ∑ a, p i a = 1) (l : List I) (i : I) (hi : i ∈ l)
    (f : (I → Ω) → ℝ) : average p i (avgList p l f) = avgList p l f := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · simpa only [avgList_cons] using average_idem p hp i (avgList p l f)
    · rw [avgList_cons, average_comm, ih hi]

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω]

variable (p : I → Ω → ℝ)

lemma residual_apply (x y : I) (f : (I → Ω) → ℝ) :
    residual p x y f =
      pairCondition p x y f - average p y (pairCondition p x y f) -
        average p x (pairCondition p x y f - average p y (pairCondition p x y f)) := rfl

lemma residual_formula (x y : I) (f : (I → Ω) → ℝ) :
    residual p x y f = pairCondition p x y f -
      average p x (pairCondition p x y f) - average p y (pairCondition p x y f) +
      average p x (average p y (pairCondition p x y f)) := by
  rw [residual_apply, map_sub]; abel

lemma average_condition_comm (i x y : I) (f : (I → Ω) → ℝ) :
    average p i (pairCondition p x y f) = pairCondition p x y (average p i f) :=
  average_comm_list p i (outside x y) f

lemma residual_center_x (hp : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    average p x (residual p x y f) = 0 := by
  rw [residual_apply, map_sub, average_idem p hp, sub_self]

lemma residual_center_y (hp : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    average p y (residual p x y f) = 0 := by
  simp only [residual_apply, map_sub]
  rw [average_idem p hp, average_comm p y x, average_comm p y x,
    average_idem p hp]
  simp

lemma condition_invariant (hp : ∀ i, ∑ a, p i a = 1) (i x y : I)
    (hix : x < i) (hiy : i ≠ y) (f : (I → Ω) → ℝ) :
    average p i (pairCondition p x y f) = pairCondition p x y f := by
  apply average_list_mem p hp
  simp [outside, hix, hiy]

lemma residual_invariant (hp : ∀ i, ∑ a, p i a = 1) (i x y : I)
    (hix : x < i) (hiy : i ≠ y) (f : (I → Ω) → ℝ) :
    average p i (residual p x y f) = residual p x y f := by
  simp only [residual_apply, map_sub]
  simp_rw [average_comm p i x, average_comm p i y,
    condition_invariant p hp i x y hix hiy]

lemma residual_projection (hp : ∀ i, ∑ a, p i a = 1) (x y : I) :
    ∃ P : Projection p, P.op = residual p x y := by
  let X := (avgProjection p hp x).complement
  let Y := (avgProjection p hp y).complement
  let C := listProjection p hp (outside x y)
  have hyc : ∀ f, Y.op (C.op f) = C.op (Y.op f) := by
    intro f
    change pairCondition p x y f-average p y (pairCondition p x y f) =
      pairCondition p x y (f-average p y f)
    rw [map_sub, average_condition_comm]
  have hxc : ∀ f, X.op ((Y.comp C hyc).op f) = (Y.comp C hyc).op (X.op f) := by
    intro f
    change (pairCondition p x y f-average p y (pairCondition p x y f)) -
      average p x (pairCondition p x y f-average p y (pairCondition p x y f)) =
      pairCondition p x y (f-average p x f) -
        average p y (pairCondition p x y (f-average p x f))
    simp only [map_sub]
    rw [← average_condition_comm, average_comm p x y]
    abel
  exact ⟨X.comp (Y.comp C hyc) hxc, rfl⟩

lemma residual_dot (hp : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    dot p f (residual p x y f) = dot p (residual p x y f) (residual p x y f) := by
  obtain ⟨P,hP⟩ := residual_projection p hp x y
  rw [← hP]
  exact P.dot_image f

omit [LinearOrder I] in
lemma centered_invariant_orthogonal (i : I) (f g : (I → Ω) → ℝ)
    (hf : average p i f = 0) (hg : average p i g = g) : dot p f g = 0 := by
  rw [← hg, ← average_adjoint, hf, dot_zero_left]

lemma residual_orthogonal (hp : ∀ i, ∑ a, p i a = 1) (x y u v : I)
    (hxy : x < y) (huv : u < v) (hd : (x,y) ≠ (u,v)) (f : (I → Ω) → ℝ) :
    dot p (residual p x y f) (residual p u v f) = 0 := by
  rcases lt_trichotomy y v with hyv | rfl | hvy
  · rw [dot_comm]
    exact centered_invariant_orthogonal p v _ _ (residual_center_y p hp u v f)
      (residual_invariant p hp v x y (lt_trans hxy hyv) (ne_of_gt hyv) f)
  · rcases lt_trichotomy x u with hxu | rfl | hux
    · rw [dot_comm]
      exact centered_invariant_orthogonal p u _ _ (residual_center_x p hp u y f)
        (residual_invariant p hp u x y hxu (ne_of_lt huv) f)
    · exact (hd rfl).elim
    · exact centered_invariant_orthogonal p x _ _ (residual_center_x p hp x y f)
        (residual_invariant p hp x u y hux (ne_of_lt hxy) f)
  · exact centered_invariant_orthogonal p y _ _ (residual_center_y p hp x y f)
      (residual_invariant p hp y u v (lt_trans huv hvy) (ne_of_gt hvy) f)

omit [Fintype I] [LinearOrder I] in
lemma average_one (hp : ∀ i, ∑ a, p i a = 1) (i : I) :
    average p i (fun _ => 1) = (fun _ => 1) := by
  funext s; simpa [average_apply] using hp i

lemma residual_mean_zero (hp : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    dot p (fun _ => 1) (residual p x y f) = 0 := by
  rw [dot_comm]
  exact centered_invariant_orthogonal p x _ _ (residual_center_x p hp x y f)
    (average_one p hp x)

end

section

open Finset

variable {I Ω J : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable (p : I → Ω → ℝ)

lemma dot_sum_right (S : Finset J) (f : (I → Ω) → ℝ) (r : J → (I → Ω) → ℝ) :
    dot p f (∑ j ∈ S, r j) = ∑ j ∈ S, dot p f (r j) := by
  unfold dot
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma dot_sum_left (S : Finset J) (r : J → (I → Ω) → ℝ) (f : (I → Ω) → ℝ) :
    dot p (∑ j ∈ S, r j) f = ∑ j ∈ S, dot p (r j) f := by
  rw [dot_comm, dot_sum_right]
  exact Finset.sum_congr rfl (fun j _ => dot_comm p f (r j))

end

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω]

theorem residual_sum (p : I → Ω → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hs : ∀ i, ∑ a, p i a = 1) (pairs : Finset (I × I))
    (hpair : ∀ z ∈ pairs, z.1 < z.2) (f : (I → Ω) → ℝ) :
    (∑ z ∈ pairs, dot p (residual p z.1 z.2 f) (residual p z.1 z.2 f)) ≤
      ∑ s, density p s * (f s - ∑ t, density p t * f t)^2 := by
  classical
  let r : (I × I) → (I → Ω) → ℝ := fun z => residual p z.1 z.2 f
  let R := ∑ z ∈ pairs, r z
  let m := ∑ t, density p t * f t
  let F := f - (fun _ => m)
  have hd (z) : dot p F (r z) = dot p (r z) (r z) := by
    change dot p (f-(fun _ => m)) (residual p z.1 z.2 f) = _
    rw [dot_sub_left, dot_const_left, residual_mean_zero p hs, mul_zero, sub_zero]
    exact residual_dot p hs z.1 z.2 f
  have hFR : dot p F R = ∑ z ∈ pairs, dot p (r z) (r z) := by
    rw [dot_sum_right]
    exact Finset.sum_congr rfl (fun z _ => hd z)
  have hRR : dot p R R = ∑ z ∈ pairs, dot p (r z) (r z) := by
    rw [dot_sum_left]
    apply Finset.sum_congr rfl
    intro z hz
    rw [dot_sum_right]
    apply Finset.sum_eq_single z
    · intro w hw hwz
      apply residual_orthogonal p hs z.1 z.2 w.1 w.2 (hpair z hz) (hpair w hw)
      simpa only [Prod.mk.eta] using Ne.symm hwz
    · exact fun hn => (hn hz).elim
  have hn := dot_nonneg p hp (F-R)
  rw [dot_sub_left p F R (F-R), dot_sub_right p F F R,
    dot_sub_right p R F R, dot_comm p R F, hFR, hRR] at hn
  have hff : dot p F F = ∑ s, density p s * (f s-∑ t, density p t*f t)^2 := by
    unfold dot
    apply Finset.sum_congr rfl
    intro s _
    change density p s * (f s-m) * (f s-m) = density p s * (f s-m)^2
    ring
  rw [← hff]
  change (∑ z ∈ pairs, dot p (r z) (r z)) ≤ dot p F F
  linarith

end MatchingFPRAS.Replica

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Mean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable (p : I → Ω → ℝ)

lemma mean_dot (f : (I → Ω) → ℝ) : mean p f = dot p (fun _ => 1) f := by simp [mean,dot]

lemma density_sum (hs : ∀ i, ∑ a, p i a = 1) : ∑ s, density p s = 1 := by
  unfold density
  rw [← Fintype.prod_sum]
  simp_rw [hs]
  simp

lemma mean_average (hs : ∀ i, ∑ a, p i a = 1) (i : I) (f : (I → Ω) → ℝ) :
    mean p (average p i f) = mean p f := by
  rw [mean_dot, ← average_adjoint]
  have ho : average p i (fun _ => 1) = (fun _ => 1) := by
    funext s; simpa [average_apply] using hs i
  rw [ho, ← mean_dot]

lemma mean_avgList (hs : ∀ i, ∑ a, p i a = 1) (l : List I) (f : (I → Ω) → ℝ) :
    mean p (avgList p l f) = mean p f := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [avgList_cons,mean_average p hs,ih]

omit [Fintype I] in
lemma average_update (i : I) (a : Ω) (f : (I → Ω) → ℝ) (s : I → Ω) :
    average p i f (Function.update s i a) = average p i f s := by
  simp only [average_apply,Function.update_idem]

lemma invariant_constant (f : (I → Ω) → ℝ) (hf : ∀ i, average p i f = f)
    (s t : I → Ω) : f s = f t := by
  classical
  have hu (i : I) (a : Ω) (s : I → Ω) : f (Function.update s i a) = f s := by
    rw [← hf i]
    exact average_update p i a f s
  have hpatch (S : Finset I) : f (fun i => if i ∈ S then t i else s i) = f s := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      have he : (fun j => if j ∈ insert i S then t j else s j) =
          Function.update (fun j => if j ∈ S then t j else s j) i (t i) := by
        funext j
        by_cases hji : j = i
        · subst j; simp
        · simp [hji]
      rw [he,hu,ih]
  simpa using (hpatch Finset.univ).symm

lemma average_all (hs : ∀ i, ∑ a, p i a = 1) (l : List I) (hl : ∀ i, i ∈ l)
    (f : (I → Ω) → ℝ) : avgList p l f = (fun _ => mean p f) := by
  funext s
  have hc : ∀ t, avgList p l f t = avgList p l f s := fun t =>
    invariant_constant p (avgList p l f) (fun i => average_list_mem p hs l i (hl i) f) t s
  have hm := mean_avgList p hs l f
  unfold mean at hm
  simp_rw [hc] at hm
  rw [← Finset.sum_mul,density_sum p hs,one_mul] at hm
  exact hm

omit [Fintype I] in
lemma avgList_fixed (l : List I) (f : (I → Ω) → ℝ)
    (hf : ∀ i ∈ l, average p i f = f) : avgList p l f = f := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [avgList_cons,ih (fun j hj => hf j (List.mem_cons_of_mem i hj)),hf i (List.mem_cons_self)]

omit [Fintype I] in
lemma avgList_comm_list (l k : List I) (f : (I → Ω) → ℝ) :
    avgList p l (avgList p k f) = avgList p k (avgList p l f) := by
  induction l with
  | nil => rfl
  | cons i l ih => rw [avgList_cons,ih,average_comm_list,avgList_cons]

omit [Fintype I] in
lemma avgList_congr (hs : ∀ i, ∑ a, p i a = 1) (l k : List I)
    (hmem : ∀ i, i ∈ l ↔ i ∈ k) (f : (I → Ω) → ℝ) : avgList p l f = avgList p k f := by
  have h₁ : avgList p l (avgList p k f) = avgList p k f :=
    avgList_fixed p l _ (fun i hi => average_list_mem p hs k i ((hmem i).mp hi) f)
  have h₂ : avgList p k (avgList p l f) = avgList p l f :=
    avgList_fixed p k _ (fun i hi => average_list_mem p hs l i ((hmem i).mpr hi) f)
  rw [avgList_comm_list,h₂] at h₁
  exact h₁

lemma projection_pythagoras (P : Projection p) (f : (I → Ω) → ℝ) :
    dot p (f-P.op f) (f-P.op f) = dot p f f-dot p (P.op f) (P.op f) := by
  rw [dot_sub_left p f (P.op f) (f-P.op f),dot_sub_right p f f (P.op f),
    dot_sub_right p (P.op f) f (P.op f),dot_comm p (P.op f) f,P.dot_image]
  ring

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω]

variable (p : I → Ω → ℝ)

lemma martingale_partial (hs : ∀ i, ∑ a, p i a = 1) (S : Finset I) (f : (I → Ω) → ℝ) :
    (∑ x ∈ S, dot p (increment p S x f) (increment p S x f)) =
      dot p f f-dot p (avgList p S.toList f) (avgList p S.toList f) := by
  classical
  induction S using Finset.induction_on_min with
  | empty => simp [future,increment,avgList]
  | insert a S hmin ih =>
    have ha : a ∉ S := fun h => (lt_irrefl a) (hmin a h)
    have hfilter : (insert a S).filter (a < ·) = S := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hai⟩; rcases hi with rfl | hi
        · exact (lt_irrefl _ hai).elim
        · exact hi
      · intro hi; exact ⟨Or.inr hi,hmin i hi⟩
    have hother (x) (hx : x ∈ S) : (insert a S).filter (x < ·) = S.filter (x < ·) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hi,hxi⟩; rcases hi with rfl | hi
        · exact (not_lt_of_gt (hmin x hx) hxi).elim
        · exact ⟨hi,hxi⟩
      · rintro ⟨hi,hxi⟩; exact ⟨Or.inr hi,hxi⟩
    have hc : avgList p (insert a S).toList f = average p a (avgList p S.toList f) := by
      change avgList p (insert a S).toList f = avgList p (a::S.toList) f
      apply avgList_congr p hs
      intro i; simp
    rw [Finset.sum_insert ha,hc]
    have hsum : (∑ x ∈ S, dot p (increment p (insert a S) x f)
        (increment p (insert a S) x f)) = ∑ x ∈ S, dot p (increment p S x f) (increment p S x f) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [increment,future,hother x hx]
    rw [hsum,ih]
    have hp := projection_pythagoras p (avgProjection p hs a) (avgList p S.toList f)
    change dot p (increment p (insert a S) a f) (increment p (insert a S) a f) + _ = _
    unfold increment future
    rw [hfilter]
    change dot p (avgList p S.toList f-average p a (avgList p S.toList f))
      (avgList p S.toList f-average p a (avgList p S.toList f)) =
      dot p (avgList p S.toList f) (avgList p S.toList f)-
        dot p (average p a (avgList p S.toList f)) (average p a (avgList p S.toList f)) at hp
    linarith

lemma martingale_variance (hs : ∀ i, ∑ a, p i a = 1) (f : (I → Ω) → ℝ) :
    variance p f = ∑ x, dot p (increment p Finset.univ x f) (increment p Finset.univ x f) := by
  rw [martingale_partial p hs]
  have hp := projection_pythagoras p (listProjection p hs Finset.univ.toList) f
  change dot p (f-avgList p Finset.univ.toList f) (f-avgList p Finset.univ.toList f) =
    dot p f f-dot p (avgList p Finset.univ.toList f) (avgList p Finset.univ.toList f) at hp
  rw [average_all p hs Finset.univ.toList (by simp)] at hp ⊢
  exact hp

omit [Fintype I] in
lemma increment_center (hs : ∀ i, ∑ a, p i a = 1) (S : Finset I) (x : I) (f : (I → Ω) → ℝ) :
    average p x (increment p S x f) = 0 := by
  simp [increment,map_sub,average_idem p hs]

lemma average_pair_future (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (hxy : x < y)
    (f : (I → Ω) → ℝ) : average p y (pairCondition p x y f) = future p Finset.univ x f := by
  change avgList p (y::outside x y) f = avgList p ((Finset.univ.filter (x < ·)).toList) f
  apply avgList_congr p hs
  intro i
  simp only [List.mem_cons,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and,outside]
  constructor
  · rintro (rfl | ⟨hi,_⟩)
    · exact hxy
    · exact hi
  · intro hi
    by_cases hiy : i=y
    · exact Or.inl hiy
    · exact Or.inr ⟨hi,hiy⟩

lemma increment_pair_formula (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (hxy : x < y)
    (f : (I → Ω) → ℝ) : increment p Finset.univ x f =
      average p y (pairCondition p x y f)-average p x (average p y (pairCondition p x y f)) := by
  rw [average_pair_future p hs x y hxy]
  rfl

end

section

open Finset

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

lemma localEnergy_nonneg (q : Ω → Ω → ℝ) (hq : ∀ a b, 0 ≤ q a b) (f : Ω → ℝ) :
    0 ≤ localEnergy q f := by
  exact div_nonneg (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg
    (fun b _ => mul_nonneg (hq a b) (sq_nonneg _)))) (by norm_num)

lemma localEnergy_sub (q : Ω → Ω → ℝ) (hq : ∀ a b, 0 ≤ q a b) (f g : Ω → ℝ) :
    localEnergy q (f-g) ≤ 2*localEnergy q f+2*localEnergy q g := by
  unfold localEnergy
  have h : (∑ a, ∑ b, q a b*((f-g) a-(f-g) b)^2) ≤
      ∑ a, ∑ b, (2*(q a b*(f a-f b)^2)+2*(q a b*(g a-g b)^2)) := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    have hsq : ((f a-g a)-(f b-g b))^2 ≤ 2*(f a-f b)^2+2*(g a-g b)^2 := by
      nlinarith [sq_nonneg ((f a-f b)+(g a-g b))]
    change q a b*((f a-g a)-(f b-g b))^2 ≤ _
    calc
      _ ≤ q a b*(2*(f a-f b)^2+2*(g a-g b)^2) := mul_le_mul_of_nonneg_left hsq (hq a b)
      _ = _ := by ring
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at h
  linarith

lemma localEnergy_shift (q : Ω → Ω → ℝ) (f : Ω → ℝ) (c : ℝ) :
    localEnergy q (fun a => f a-c) = localEnergy q f := by
  unfold localEnergy
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  congr 2; ring

lemma square_average (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (f : A → ℝ) :
    (∑ a, w a*f a)^2 ≤ ∑ a, w a*(f a)^2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun a => w a*f a) (f := w) (g := fun a => w a*(f a)^2)
    (fun a _ => hw a) (fun a _ => mul_nonneg (hw a) (sq_nonneg _))
    (fun a _ => by nlinarith [sq_nonneg (w a*f a)])
  simpa only [hs,one_mul] using h

lemma localEnergy_average (q : Ω → Ω → ℝ) (hq : ∀ a b, 0 ≤ q a b)
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : ∑ a, w a = 1) (f : A → Ω → ℝ) :
    localEnergy q (fun a => ∑ i, w i*f i a) ≤ ∑ i, w i*localEnergy q (f i) := by
  have h : (∑ a, ∑ b, q a b*((∑ i, w i*f i a)-(∑ i, w i*f i b))^2) ≤
      ∑ a, ∑ b, q a b*(∑ i, w i*(f i a-f i b)^2) := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    apply mul_le_mul_of_nonneg_left _ (hq a b)
    simpa only [mul_sub,Finset.sum_sub_distrib] using square_average w hw hs (fun i => f i a-f i b)
  have he : (∑ a, ∑ b, q a b*(∑ i, w i*(f i a-f i b)^2)) =
      ∑ i, w i*(∑ a, ∑ b, q a b*(f i a-f i b)^2) := by
    simp only [Finset.mul_sum]
    have hin (a : Ω) : (∑ b, ∑ i, q a b*(w i*(f i a-f i b)^2)) =
        ∑ i, ∑ b, q a b*(w i*(f i a-f i b)^2) := Finset.sum_comm
    simp_rw [hin]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  unfold localEnergy
  rw [he] at h
  have := div_le_div_of_nonneg_right h (by norm_num : (0:ℝ) ≤ 2)
  simpa only [Finset.sum_div,mul_div_assoc] using this

lemma localEnergy_bound (π : Ω → ℝ) (q : Ω → Ω → ℝ) (hq : ∀ a b, 0 ≤ q a b)
    (hr : ∀ a, ∑ b, q a b = π a) (hc : ∀ b, ∑ a, q a b = π b) (f : Ω → ℝ) :
    localEnergy q f ≤ 2*∑ a, π a*(f a)^2 := by
  have hh : (∑ a, ∑ b, q a b*(f a-f b)^2) ≤
      ∑ a, ∑ b, (2*(q a b*(f a)^2)+2*(q a b*(f b)^2)) := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    have hs : (f a-f b)^2 ≤ 2*(f a)^2+2*(f b)^2 := by nlinarith [sq_nonneg (f a+f b)]
    calc
      _ ≤ q a b * (2 * (f a)^2 + 2 * (f b)^2) :=
        mul_le_mul_of_nonneg_left hs (hq a b)
      _ = _ := by ring
  have hleft : (∑ a, ∑ b, q a b*(f a)^2) = ∑ a, π a*(f a)^2 := by
    simp only [← Finset.sum_mul,hr]
  have hright : (∑ a, ∑ b, q a b*(f b)^2) = ∑ b, π b*(f b)^2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,hc]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,hleft,hright] at hh
  unfold localEnergy; linarith

end

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]

variable (p : I → Ω → ℝ)

omit [DecidableEq I] [Fintype Ω] in
lemma density_nonneg (hp : ∀ i a, 0 ≤ p i a) (s : I → Ω) : 0 ≤ density p s :=
  Finset.prod_nonneg (fun i _ => hp i (s i))

lemma mean_mono (hp : ∀ i a, 0 ≤ p i a) {f g : (I → Ω) → ℝ}
    (h : ∀ s, f s ≤ g s) : mean p f ≤ mean p g :=
  Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (h s) (density_nonneg p hp s))

lemma mean_nonneg (hp : ∀ i a, 0 ≤ p i a) {f : (I → Ω) → ℝ} (h : ∀ s, 0 ≤ f s) :
    0 ≤ mean p f := Finset.sum_nonneg (fun s _ => mul_nonneg (density_nonneg p hp s) (h s))

lemma mean_add (f g : (I → Ω) → ℝ) : mean p (f+g) = mean p f+mean p g := by
  simp [mean,mul_add,Finset.sum_add_distrib]

lemma mean_mul (c : ℝ) (f : (I → Ω) → ℝ) : mean p (fun s => c*f s) = c*mean p f := by
  simp only [mean,Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring

lemma mean_square (f : (I → Ω) → ℝ) : mean p (fun s => (f s)^2) = dot p f f := by
  simp only [mean,dot]; apply Finset.sum_congr rfl; intro s _; ring

lemma pairEnergy_nonneg (hp : ∀ i a, 0 ≤ p i a) (x y : I) (Q : PairCapacity p x y)
    (f : (I → Ω) → ℝ) : 0 ≤ pairEnergy p x y Q f :=
  mean_nonneg p hp (fun _ => localEnergy_nonneg Q.q Q.nonneg _)

lemma pairEnergy_sub (hp : ∀ i a, 0 ≤ p i a) (x y : I) (Q : PairCapacity p x y)
    (f g : (I → Ω) → ℝ) : pairEnergy p x y Q (f-g) ≤
      2*pairEnergy p x y Q f+2*pairEnergy p x y Q g := by
  have hh := mean_mono p hp (fun s => localEnergy_sub Q.q Q.nonneg (slice x y f s) (slice x y g s))
  change mean p (fun s => localEnergy Q.q (slice x y (f-g) s)) ≤
    mean p ((fun s => 2*localEnergy Q.q (slice x y f s))+(fun s => 2*localEnergy Q.q (slice x y g s))) at hh
  rw [mean_add,mean_mul,mean_mul] at hh
  exact hh

lemma slice_square_mean (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    mean p (fun s => ∑ a : Ω × Ω, (p x a.1*p y a.2)*(slice x y f s a)^2) = dot p f f := by
  have he (s : I → Ω) : (∑ a : Ω × Ω, (p x a.1*p y a.2)*(slice x y f s a)^2) =
      average p x (average p y (fun s => (f s)^2)) s := by
    rw [Fintype.sum_prod_type]
    simp only [average_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    unfold slice replacePair; ring
  simp_rw [he]
  rw [mean_average p hs,mean_average p hs,mean_square]

lemma pairEnergy_bound (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (x y : I) (Q : PairCapacity p x y) (f : (I → Ω) → ℝ) :
    pairEnergy p x y Q f ≤ 2*dot p f f := by
  have hh := mean_mono p hp (fun s => localEnergy_bound (fun a => p x a.1*p y a.2)
    Q.q Q.nonneg Q.row Q.col (slice x y f s))
  rw [mean_mul,slice_square_mean p hs] at hh
  exact hh

omit [Fintype I] [Fintype Ω] in
lemma replacePair_update (i x y : I) (hix : i ≠ x) (hiy : i ≠ y)
    (s : I → Ω) (a : Ω × Ω) (b : Ω) :
    replacePair x y (Function.update s i b) a = Function.update (replacePair x y s a) i b := by
  unfold replacePair
  rw [Function.update_comm hix,Function.update_comm hiy]

omit [Fintype I] in
lemma slice_average (i x y : I) (hix : i ≠ x) (hiy : i ≠ y)
    (f : (I → Ω) → ℝ) (s : I → Ω) :
    slice x y (average p i f) s = (fun a => ∑ b, p i b*slice x y f (Function.update s i b) a) := by
  funext a
  simp only [slice,average_apply,replacePair_update i x y hix hiy]

lemma pairEnergy_average (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (i x y : I) (hix : i ≠ x) (hiy : i ≠ y) (Q : PairCapacity p x y) (f : (I → Ω) → ℝ) :
    pairEnergy p x y Q (average p i f) ≤ pairEnergy p x y Q f := by
  have hh (s : I → Ω) : localEnergy Q.q (slice x y (average p i f) s) ≤
      average p i (fun s => localEnergy Q.q (slice x y f s)) s := by
    rw [slice_average p i x y hix hiy]
    exact localEnergy_average Q.q Q.nonneg (p i) (hp i) (hs i) (fun b => slice x y f (Function.update s i b))
  have hh := mean_mono p hp hh
  rw [mean_average p hs] at hh
  exact hh

lemma pairEnergy_avgList (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (l : List I) (x y : I) (hl : ∀ i ∈ l, i ≠ x ∧ i ≠ y) (Q : PairCapacity p x y)
    (f : (I → Ω) → ℝ) : pairEnergy p x y Q (avgList p l f) ≤ pairEnergy p x y Q f := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih =>
    rw [avgList_cons]
    exact (pairEnergy_average p hp hs i x y (hl i (by simp)).1 (hl i (by simp)).2 Q _).trans
      (ih (fun j hj => hl j (List.mem_cons_of_mem i hj)))

end MatchingFPRAS.Replica

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TierClamp
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

lemma clamp_comparison {c lo hi lo' hi' w : ℝ} (hc : 0 ≤ c)
    (hlo : lo' ≤ c*lo) (hhi : hi' ≤ c*hi) (hw : w ≤ c*w) :
    max lo' (min hi' w) ≤ c*max lo (min hi w) := by
  rw [mul_max_of_nonneg _ _ hc,mul_min_of_nonneg _ _ hc]
  exact max_le_max hlo (min_le_min hhi hw)

lemma tierClamp_adjacent {c : ℝ} (hc : 1 ≤ c) (t : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    tierClamp c (t+1) w ≤ c*tierClamp c t w ∧
      tierClamp c t w ≤ c*tierClamp c (t+1) w := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have ht : 0 < c^t := pow_pos hc0 t
  have ht1 : 0 < c^(t+1) := pow_pos hc0 _
  have hpow : c^t ≤ c^(t+1) := pow_le_pow_right₀ hc (by omega)
  have hi : (c^(t+1))⁻¹ ≤ (c^t)⁻¹ := inv_anti₀ ht hpow
  have hwc : w ≤ c*w := by nlinarith
  constructor
  · apply clamp_comparison hc0.le _ _ hwc
    · exact hi.trans (by nlinarith [inv_pos.mpr ht])
    · rw [pow_succ]; nlinarith
  · apply clamp_comparison hc0.le _ _ hwc
    · have he : (c^t)⁻¹ = c*(c^(t+1))⁻¹ := by
        rw [pow_succ,mul_inv_rev]; field_simp
      exact he.le
    · exact hpow.trans (by nlinarith)

lemma ladder_base_pow_bound (N : ℕ) (hN : 2 ≤ N) :
    (1+((N:ℝ)^2)⁻¹)^N ≤ 2 := by
  have hn2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hn : (0:ℝ) < N := by positivity
  have hx : 0 ≤ ((N:ℝ)^2)⁻¹ := by positivity
  have hbase : 0 ≤ 1+((N:ℝ)^2)⁻¹ := by positivity
  have hb : 1+((N:ℝ)^2)⁻¹ ≤ Real.exp (((N:ℝ)^2)⁻¹) := by simpa [add_comm] using Real.add_one_le_exp (((N:ℝ)^2)⁻¹)
  have hp := pow_le_pow_left₀ hbase hb N
  have he : (Real.exp (((N:ℝ)^2)⁻¹))^N = Real.exp ((N:ℝ)⁻¹) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [he] at hp
  have hinv : (N:ℝ)⁻¹ ≤ 1/2 := (inv_le_comm₀ hn (by norm_num)).mpr (by nlinarith)
  have hexp : Real.exp (1/2:ℝ) < 2 := by
    have hs : (Real.exp (1/2:ℝ))^2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h := Real.exp_one_lt_three
    have hpos := Real.exp_pos (1/2:ℝ)
    nlinarith
  exact hp.trans ((Real.exp_le_exp.mpr hinv).trans hexp.le)

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V) (hloop : ∀ e, ¬(ends e).IsDiag)

include hloop

omit [DecidableEq E] in
theorem adjacent_gibbs (hN : 2 ≤ Fintype.card V) (w : E → ℝ) (hw : ∀ e, 0 < w e)
    (t : ℕ) (A : PM (fun e v => v ∈ ends e)) :
    let c : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹
    let πt := gibbs (fun e => tierClamp c t (w e)) A
    let πnext := gibbs (fun e => tierClamp c (t+1) (w e)) A
    πnext/2 ≤ πt ∧ πt ≤ 2*πnext := by
  let c : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹
  have hc : 1 ≤ c := by
    dsimp [c]
    have : 0 ≤ ((Fintype.card V:ℝ)^2)⁻¹ := by positivity
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  let z := fun e => tierClamp c t (w e)
  let z' := fun e => tierClamp c (t+1) (w e)
  have hz : ∀ e, 0 < z e := fun e => tierClamp_pos hc0 t (w e)
  have hz' : ∀ e, 0 < z' e := fun e => tierClamp_pos hc0 (t+1) (w e)
  have hh := fun e => tierClamp_adjacent hc t (hw e).le
  have h1 := gibbs_compare ends hloop hz hz' c hc0.le (fun e => (hh e).2) (fun e => (hh e).1) A
  have h2 := gibbs_compare ends hloop hz' hz c hc0.le (fun e => (hh e).1) (fun e => (hh e).2) A
  have hb : c^(Fintype.card V) ≤ 2 := ladder_base_pow_bound _ hN
  have hp := gibbs_pos z hz A
  have hp' := gibbs_pos z' hz' A
  change gibbs z' A/2 ≤ gibbs z A ∧ gibbs z A ≤ 2*gibbs z' A
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hb) hp.le,
    mul_nonneg (sub_nonneg.mpr hb) hp'.le]

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] in
lemma cycleMove_gibbs (w : E → ℝ) (p : PM inc × PM inc) (S : Finset E) :
    gibbs w (cycleMove p S).1*gibbs w (cycleMove p S).2 = gibbs w p.1*gibbs w p.2 := by
  classical
  by_cases h : S ∈ components (inc := inc) (p.1.val ∪ p.2.val)
  · unfold gibbs matchingWeight
    rw [(cycleMove_val _ _ h).1,(cycleMove_val _ _ h).2,div_mul_div_comm,exchange_weight]
    rw [div_mul_div_comm]
  · simp only [cycleMove,dite_eq_right h]

omit [DecidableEq V] in
lemma cycleProposal_gibbs (w : E → ℝ) (p q : PM inc × PM inc) :
    gibbs w p.1*gibbs w p.2*cycleProposal p q =
      gibbs w q.1*gibbs w q.2*cycleProposal q p := by
  classical
  rw [cycleProposal_symmetric q p]
  by_cases h : (discrepancyComponents p.1 p.2).Nonempty
  · simp only [cycleProposal,ite_eq_left h,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    unfold cycleTerm
    split_ifs with he
    · rw [← he.2,cycleMove_gibbs]
    · simp
  · by_cases he : p = q
    · subst q; rfl
    · simp [cycleProposal,h,he]

omit [DecidableEq V] in
lemma cycleProposal_expectation (p : PM inc × PM inc) (F : PM inc × PM inc → ℝ) :
    (∑ q, cycleProposal p q * F q) =
      if (discrepancyComponents p.1 p.2).Nonempty then
        (∑ S ∈ discrepancyComponents p.1 p.2, F (cycleMove p S)) /
          (discrepancyComponents p.1 p.2).card else F p := by
  classical
  by_cases h : (discrepancyComponents p.1 p.2).Nonempty
  · simp only [cycleProposal,ite_eq_left h,Finset.sum_mul]
    rw [Finset.sum_comm]
    have hs (S : Finset E) : (∑ q, cycleTerm p q S*F q) =
        if S ∈ discrepancyComponents p.1 p.2 then
          F (cycleMove p S) / (discrepancyComponents p.1 p.2).card else 0 := by
      by_cases hm : S ∈ discrepancyComponents p.1 p.2
      · simp only [cycleTerm,hm,true_and,ite_eq_left,ite_mul,zero_mul]
        simp [div_eq_mul_inv,mul_comm]
      · simp [cycleTerm,hm]
    simp_rw [hs]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_div]
  · simp [cycleProposal,h]




omit [DecidableEq V] in
theorem cycleProposal_dirichlet (w : E → ℝ) (f g : Finset E → ℝ) :
    (∑ A : PM inc, ∑ B : PM inc, gibbs w A*gibbs w B *
      (∑ q : PM inc × PM inc, cycleProposal (A,B) q *
        ((f A.val+g B.val)-(f q.1.val+g q.2.val))^2)) / 6 =
      cycleDirichlet (inc := inc) w f g := by
  classical
  unfold cycleDirichlet
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro A _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro B _
  rw [mul_div_assoc]
  congr 1
  rw [cycleProposal_expectation]
  by_cases h : (discrepancyComponents A B).Nonempty
  · rw [ite_eq_left h,div_div]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro S hS
    have hc : S ∈ components (inc := inc) (A.val ∪ B.val) := (Finset.mem_filter.mp hS).1
    rw [(cycleMove_val (A,B) S hc).1,(cycleMove_val (A,B) S hc).2]
    dsimp only [cycleSquare]
    rw [mul_comm ((discrepancyComponents A B).card:ℝ)]
  · have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he]

end

open Finset

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_RelationDestinations
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

attribute [local instance] Classical.propDecidable

lemma colorProposal_off (hloop : ∀ e, ¬(ends e).IsDiag)
    (A B : PM (fun e v => v ∈ ends e)) (h : A ≠ B) :
    colorProposal ends A B = if ColorChange ends A B then (2*(A.val.card:ℝ))⁻¹ else 0 := by
  classical
  have hn : (Fintype.card V:ℝ) = 2*(A.val.card:ℝ) := by exact_mod_cast (A.twice_card ends hloop).symm
  simp [colorProposal,relationProposal,relationOff,relationDestinations,h,hn]

theorem colorProposal_dirichlet (hloop : ∀ e, ¬(ends e).IsDiag)
    (w : E → ℝ) (f : Finset E → ℝ) :
    (∑ A : PM (fun e v => v ∈ ends e), ∑ B : PM (fun e v => v ∈ ends e),
      min (gibbs w A) (gibbs w B)*colorProposal ends A B*(f A.val-f B.val)^2) / 6 =
      colorDirichlet ends w f := by
  classical
  unfold colorDirichlet
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro A _
  rw [Finset.sum_div]
  unfold colorDestinations
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro B _
  by_cases h : A = B
  · subst B; simp
  · rw [colorProposal_off ends hloop A B h]
    by_cases hc : ColorChange ends A B
    · rw [ite_eq_left hc,ite_eq_left hc]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · simp [hc]

end

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

attribute [local instance] Classical.propDecidable

lemma switchProposal_off (hloop : ∀ e, ¬(ends e).IsDiag)
    (A B : PM (fun e v => v ∈ ends e)) (h : A ≠ B) :
    switchProposal ends A B = if TwoEdgeSwitch A B then (8*(A.val.card.choose 2:ℝ))⁻¹ else 0 := by
  have hn : Fintype.card V/2 = A.val.card := by have := A.twice_card ends hloop; omega
  simp [switchProposal,relationProposal,relationOff,relationDestinations,h,hn]

theorem switchProposal_dirichlet (hloop : ∀ e, ¬(ends e).IsDiag)
    (w : E → ℝ) (f : Finset E → ℝ) :
    (∑ A : PM (fun e v => v ∈ ends e), ∑ B : PM (fun e v => v ∈ ends e),
      min (gibbs w A) (gibbs w B)*switchProposal ends A B*(f A.val-f B.val)^2) / 6 =
      switchDirichlet (inc := fun e v => v ∈ ends e) w f := by
  classical
  unfold switchDirichlet
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl; intro A _
  rw [Finset.sum_div]
  unfold switchDestinations
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro B _
  by_cases h : A = B
  · subst B; simp
  · rw [switchProposal_off ends hloop A B h]
    by_cases hc : TwoEdgeSwitch A B
    · rw [ite_eq_left hc,ite_eq_left hc]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    · simp [hc]

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_LocalVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

omit [Fintype I] [DecidableEq Ω] in
lemma invariant_update (i : I) (f : (I → Ω) → ℝ) (hi : average p i f = f)
    (s : I → Ω) (a : Ω) : f (Function.update s i a) = f s := by
  rw [← hi]
  exact average_update p i a f s

omit [DecidableEq Ω] in
lemma pairEnergy_shift_invariant (x y : I) (Q : PairCapacity p x y)
    (f d : (I → Ω) → ℝ) (hx : average p x d = d) (hy : average p y d = d) :
    pairEnergy p x y Q (f-d) = pairEnergy p x y Q f := by
  have he (s : I → Ω) : slice x y (f-d) s = (fun a => slice x y f s a-d s) := by
    funext a
    change f (replacePair x y s a)-d (Function.update (Function.update s x a.1) y a.2) = _
    rw [invariant_update p y d hy,invariant_update p x d hx]
    rfl
  unfold pairEnergy
  simp_rw [he,localEnergy_shift]

omit [DecidableEq Ω] in
lemma pair_poincare_global (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (x y : I) (hxy : x ≠ y) (Q : PairCapacity p x y) (C : ℝ) (hQ : PairPoincare p x y Q C)
    (h k : (I → Ω) → ℝ) (hh : average p x h = 0) (hhy : average p y h = h)
    (hkx : average p x k = k) : dot p h h ≤ C*pairEnergy p x y Q (h+k) := by
  have hc (s : I → Ω) : (∑ a, p x a*h (Function.update s x a)) = 0 := by
    change average p x h s = 0
    rw [hh]; rfl
  have he (s : I → Ω) : (fun a : Ω × Ω =>
      h (Function.update s x a.1)+k (Function.update s y a.2)) = slice x y (h+k) s := by
    funext a
    change _ = h (Function.update (Function.update s x a.1) y a.2)+
      k (Function.update (Function.update s x a.1) y a.2)
    rw [invariant_update p y h hhy,Function.update_comm hxy,invariant_update p x k hkx]
  have hi (s : I → Ω) : average p x (fun s => (h s)^2) s ≤
      C*localEnergy Q.q (slice x y (h+k) s) := by
    have hi := hQ (fun a => h (Function.update s x a)) (fun b => k (Function.update s y b))
    unfold localVariance at hi
    rw [hc,he] at hi
    simpa only [sub_zero,average_apply] using hi
  have hi := mean_mono p hp hi
  rw [mean_average p hs,mean_square,mean_mul] at hi
  exact hi

omit [DecidableEq Ω] in
lemma projection_contraction (hp : ∀ i a, 0 ≤ p i a) (P : Projection p) (f : (I → Ω) → ℝ) :
    dot p (P.op f) (P.op f) ≤ dot p f f := by
  have hh := dot_nonneg p hp (f-P.op f)
  rw [projection_pythagoras] at hh
  linarith

omit [DecidableEq Ω] in
lemma baseEnergy_nonneg (hp : ∀ i a, 0 ≤ p i a) (i : I) (f : (I → Ω) → ℝ) :
    0 ≤ baseEnergy p i f := dot_nonneg p hp _

variable [LinearOrder I]

omit [DecidableEq Ω] in
lemma increment_base_bound (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (i : I) (f : (I → Ω) → ℝ) :
    dot p (increment p Finset.univ i f) (increment p Finset.univ i f) ≤ baseEnergy p i f := by
  let P := listProjection p hs ((Finset.univ.filter (i < ·)).toList)
  have he : increment p Finset.univ i f = P.op (f-average p i f) := by
    change avgList p _ f-average p i (avgList p _ f) = avgList p _ (f-average p i f)
    rw [map_sub,average_comm_list]
  rw [he]
  exact projection_contraction p hp P (f-average p i f)

omit [DecidableEq Ω] in
lemma one_pair (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (x y : I) (hxy : x < y) (Q : PairCapacity p x y) (L : ℝ) (hL : 0 ≤ L)
    (hQ : PairPoincare p x y Q (2*L)) (f : (I → Ω) → ℝ) :
    dot p (increment p Finset.univ x f) (increment p Finset.univ x f) ≤
      4*L*pairEnergy p x y Q f+8*L*dot p (residual p x y f) (residual p x y f) := by
  let c := pairCondition p x y f
  let h := increment p Finset.univ x f
  let k := average p x c-average p x (average p y c)
  let d := average p x (average p y c)
  have hh : h = average p y c-d := increment_pair_formula p hs x y hxy f
  have hhy : average p y h = h := by
    rw [hh,map_sub]
    change average p y (average p y c)-average p y (average p x (average p y c)) =
      average p y c-average p x (average p y c)
    rw [average_comm p y x,average_idem p hs]
  have hkx : average p x k = k := by
    change average p x (average p x c-average p x (average p y c)) = _
    rw [map_sub,average_idem p hs,average_idem p hs]
  have hdx : average p x d = d := average_idem p hs x _
  have hdy : average p y d = d := by
    change average p y (average p x (average p y c)) = average p x (average p y c)
    rw [average_comm,average_idem p hs]
  have hhk : h+k = c-residual p x y f-d := by
    rw [hh,residual_formula]
    change (average p y c-d)+(average p x c-d) =
      c-(c-average p x c-average p y c+average p x (average p y c))-d
    dsimp [d]; abel
  have hpq := pair_poincare_global p hp hs x y (ne_of_lt hxy) Q (2*L) hQ h k
    (increment_center p hs Finset.univ x f) hhy hkx
  rw [hhk,pairEnergy_shift_invariant p x y Q _ d hdx hdy] at hpq
  have hc : pairEnergy p x y Q c ≤ pairEnergy p x y Q f := by
    apply pairEnergy_avgList p hp hs (outside x y) x y _ Q f
    intro i hi
    have hi : x < i ∧ i ≠ y := by simpa [outside] using hi
    exact ⟨ne_of_gt hi.1,hi.2⟩
  have he := pairEnergy_sub p hp x y Q c (residual p x y f)
  have hr := pairEnergy_bound p hp hs x y Q (residual p x y f)
  nlinarith [mul_nonneg hL (sub_nonneg.mpr hc),mul_nonneg hL (sub_nonneg.mpr hr),
    mul_nonneg hL (sub_nonneg.mpr he)]

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [LinearOrder I]
  [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

omit [LinearOrder I] in
lemma sum_allowed (guides : I → Finset I) (f : I × I → ℝ) :
    (∑ z ∈ allowed guides, f z) = ∑ x, ∑ y ∈ guides x, f (x,y) := by
  classical
  simp only [allowed,Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro x _
  simpa only [Finset.filter_univ_mem] using
    (Finset.sum_filter (s := Finset.univ) (fun y => y ∈ guides x) (fun y => f (x,y))).symm

omit [DecidableEq Ω] in
theorem replica_gap (hp : ∀ i a, 0 ≤ p i a) (hs : ∀ i, ∑ a, p i a = 1)
    (guides : I → Finset I) (base : Finset I) (hbase : base.Nonempty)
    (q : ℕ) (L : ℝ) (hL : 0 < L) (hq : (q:ℝ) = 32*L)
    (hn : ∀ x ∉ base, (guides x).card = q) (hb : ∀ x ∈ base, guides x = ∅)
    (horder : ∀ x y, y ∈ guides x → x < y)
    (Q : ∀ x y, PairCapacity p x y)
    (hQ : ∀ x y, y ∈ guides x → PairPoincare p x y (Q x y) (2*L))
    (f : (I → Ω) → ℝ) :
    variance p f ≤ (8*((∑ x, (guides x).card)+base.card : ℕ)/3:ℝ)*
      scanEnergy p guides base Q f := by
  classical
  let H : I → ℝ := fun x => dot p (increment p Finset.univ x f) (increment p Finset.univ x f)
  let B := ∑ x ∈ base, H x
  let A := ∑ x ∈ baseᶜ, H x
  let E := pairTotal p guides Q f
  let F := baseTotal p base f
  have hvar : variance p f = A+B := by
    have h := Finset.sum_add_sum_compl base H
    rw [martingale_variance]
    change (∑ x, H x) = A+B
    dsimp [A,B]; linarith
    exact hs
  have hbaseBound : B ≤ F := Finset.sum_le_sum (fun x _ => increment_base_bound p hp hs x f)
  have hE : 0 ≤ E := Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
    (fun y _ => pairEnergy_nonneg p hp x y (Q x y) f))
  have hF : 0 ≤ F := Finset.sum_nonneg (fun x _ => baseEnergy_nonneg p hp x f)
  have hlhs : (∑ x, ∑ y ∈ guides x, H x) = (q:ℝ)*A := by
    calc
      _ = ∑ x, if x ∈ baseᶜ then (q:ℝ)*H x else 0 := by
        apply Finset.sum_congr rfl; intro x _
        by_cases hx : x ∈ base
        · simp [hb x hx,hx]
        · simp [hx,hn x hx]
      _ = ∑ x ∈ baseᶜ, (q:ℝ)*H x := by
        simpa only [Finset.filter_univ_mem] using
          (Finset.sum_filter (s := Finset.univ) (fun x => x ∈ baseᶜ) (fun x => (q:ℝ)*H x)).symm
      _ = _ := by rw [Finset.mul_sum]
  have hr : (∑ x, ∑ y ∈ guides x, dot p (residual p x y f) (residual p x y f)) ≤ variance p f := by
    have hh := residual_sum p hp hs (allowed guides)
      (fun z hz => horder z.1 z.2 (by simpa [allowed] using hz)) f
    rw [sum_allowed] at hh
    have hv : variance p f = ∑ s, density p s*(f s-∑ t, density p t*f t)^2 := by
      unfold variance dot mean
      apply Finset.sum_congr rfl; intro s _
      change density p s*(f s-∑ t, density p t*f t)*(f s-∑ t, density p t*f t) = _
      ring
    rw [hv]
    exact hh
  have hpair := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset I)) =>
    Finset.sum_le_sum (fun y hy => one_pair p hp hs x y (horder x y hy) (Q x y) L
      (le_of_lt hL) (hQ x y hy) f))
  change (∑ x, ∑ y ∈ guides x, H x) ≤ _ at hpair
  rw [hlhs,hq] at hpair
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hpair
  change 32*L*A ≤ 4*L*E+8*L*(∑ x, ∑ y ∈ guides x,
      dot p (residual p x y f) (residual p x y f)) at hpair
  have hstrong : variance p f ≤ E/6+(4/3:ℝ)*F := by
    apply (mul_le_mul_iff_left₀ hL).mp
    nlinarith [mul_nonneg (le_of_lt hL) (sub_nonneg.mpr hr),
      mul_nonneg (le_of_lt hL) (sub_nonneg.mpr hbaseBound)]
  let M : ℝ := ((∑ x, (guides x).card)+base.card : ℕ)
  have hM : 0 < M := by
    have hnM : 0 < ((∑ x, (guides x).card)+base.card : ℕ) :=
      lt_of_lt_of_le (Finset.card_pos.mpr hbase) (Nat.le_add_left _ _)
    dsimp [M]
    exact_mod_cast hnM
  change variance p f ≤ (8*M/3)*((E+F)/(2*M))
  have he : (8*M/3)*((E+F)/(2*M)) = (4/3:ℝ)*(E+F) := by
    field_simp [ne_of_gt hM]
    ring
  rw [he]
  linarith

end

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma metropolis_row (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 < π a) (a : Ω) : (∑ b, metropolis P π a b) = 1 := by
  simp only [metropolis,← Finset.sum_div,metropolisCapacity_row]
  exact div_self (ne_of_gt (hπ a))

lemma metropolis_acceptance (P : SymmetricProposal Ω) (π : Ω → ℝ)
    (hπ : ∀ a, 0 < π a) (a b : Ω) (hab : a ≠ b) :
    metropolis P π a b = P.q a b*min 1 (π b/π a) := by
  unfold metropolis metropolisCapacity
  rw [ite_eq_right hab]
  unfold offCapacity
  rw [mul_div_right_comm,← min_div_div_right (hπ a).le,div_self (ne_of_gt (hπ a)),mul_comm]

lemma metropolis_energy (P : SymmetricProposal Ω) (π : Ω → ℝ) (f : Ω → ℝ) :
    localEnergy (metropolisCapacity P π) f = localEnergy (offCapacity P π) f := by
  unfold localEnergy
  congr 1
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  by_cases h : a = b
  · subst b; simp
  · simp only [metropolisCapacity,ite_eq_right h]

theorem metropolis_energy_domination (P : SymmetricProposal Ω) (π μ : Ω → ℝ)
    (r : ℝ) (hr : 0 ≤ r) (h : ∀ a, r*π a ≤ μ a) (f : Ω → ℝ) :
    r*localEnergy (metropolisCapacity P π) f ≤ localEnergy (metropolisCapacity P μ) f := by
  rw [metropolis_energy,metropolis_energy]
  unfold localEnergy
  rw [← mul_div_assoc,Finset.mul_sum]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Finset.sum_le_sum; intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro b _
  have hh : r*min (π a) (π b) ≤ min (μ a) (μ b) := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hr).trans (h a)
    · exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hr).trans (h b)
  calc
    _ = (r*min (π a) (π b))*P.q a b*(f a-f b)^2 := by unfold offCapacity; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hh (P.nonneg a b)) (sq_nonneg _)

end MatchingFPRAS.Replica

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma firstLift_energy (π : Ω → ℝ) (hπ : ∀ a, 0 ≤ π a) (hs : ∑ a, π a = 1)
    (q : Ω → Ω → ℝ) (f g : Ω → ℝ) :
    (∑ a : Ω × Ω, ∑ b : Ω × Ω, min (π a.1*π a.2) (π b.1*π b.2)*
      firstLift q a b*((f a.1+g a.2)-(f b.1+g b.2))^2) =
      ∑ a, ∑ b, min (π a) (π b)*q a b*(f a-f b)^2 := by
  classical
  simp only [Fintype.sum_prod_type,firstLift,mul_ite,ite_mul,zero_mul,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have h (a b c : Ω) :
      min (π a*π b) (π c*π b)*q a c*((f a+g b)-(f c+g b))^2 =
      π b*(min (π a) (π c)*q a c*(f a-f c)^2) := by
    rw [← min_mul_of_nonneg _ _ (hπ b)]
    ring
  simp_rw [h,← Finset.mul_sum]
  simp only [← Finset.sum_mul,hs,one_mul]

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_PushedFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

section

open Finset

variable {R A S : Type*} [Fintype R] [Fintype A] [Fintype S] [DecidableEq S]

omit [Fintype S] in
lemma pushedFlow_nonneg (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (hρ : ∀ r, 0 ≤ ρ r) (hq : ∀ a b, 0 ≤ q a b) (s t : S) :
    0 ≤ pushedFlow ρ F q s t := by
  apply Finset.sum_nonneg; intro z _
  split_ifs <;> [exact mul_nonneg (hρ _) (hq _ _); exact le_refl _]

lemma pushedFlow_test (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (g : S → S → ℝ) :
    (∑ s, ∑ t, pushedFlow ρ F q s t*g s t) =
    ∑ r, ρ r*∑ a, ∑ b, q a b*g (F r a) (F r b) := by
  classical
  calc
    _ = ∑ st : S × S, (∑ z : R × (A × A),
        if (F z.1 z.2.1,F z.1 z.2.2) = st then ρ z.1*q z.2.1 z.2.2 else 0)*g st.1 st.2 := by
      rw [Fintype.sum_prod_type]; rfl
    _ = ∑ z : R × (A × A), ρ z.1*q z.2.1 z.2.2*g (F z.1 z.2.1) (F z.1 z.2.2) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro z _
      simp only [ite_mul,zero_mul]
      simp
    _ = _ := by
      simp only [Fintype.sum_prod_type,Finset.mul_sum]
      apply Finset.sum_congr rfl; intro r _
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      ring

lemma pushedFlow_row_test (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (μ : A → ℝ) (hrow : ∀ a, ∑ b, q a b = μ a) (g : S → ℝ) :
    (∑ s, ∑ t, pushedFlow ρ F q s t*g s) = ∑ r, ρ r*∑ a, μ a*g (F r a) := by
  rw [pushedFlow_test]
  apply Finset.sum_congr rfl; intro r _
  congr 1
  apply Finset.sum_congr rfl; intro a _
  rw [← Finset.sum_mul,hrow]

lemma pushedFlow_col_test (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (μ : A → ℝ) (hcol : ∀ b, ∑ a, q a b = μ b) (g : S → ℝ) :
    (∑ s, ∑ t, pushedFlow ρ F q s t*g t) = ∑ r, ρ r*∑ b, μ b*g (F r b) := by
  rw [pushedFlow_test]
  apply Finset.sum_congr rfl; intro r _
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [← Finset.sum_mul,hcol]

lemma pushedFlow_energy (ρ : R → ℝ) (F : R → A → S) (q : A → A → ℝ)
    (f : S → ℝ) : localEnergy (pushedFlow ρ F q) f =
    ∑ r, ρ r*localEnergy q (fun a => f (F r a)) := by
  unfold localEnergy
  rw [pushedFlow_test]
  simp only [mul_div_assoc,Finset.sum_div]

end

section

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

omit [DecidableEq Ω] in
lemma slice_mean (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (f : (I → Ω) → ℝ) :
    mean p (fun s => ∑ a : Ω × Ω, p x a.1*p y a.2*f (replacePair x y s a)) = mean p f := by
  have he (s : I → Ω) : (∑ a : Ω × Ω, p x a.1*p y a.2*f (replacePair x y s a)) =
      average p x (average p y f) s := by
    rw [Fintype.sum_prod_type]
    simp only [average_apply,Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    unfold replacePair; ring
  simp_rw [he]
  rw [mean_average p hs,mean_average p hs]

lemma pairFlow_row (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (Q : PairCapacity p x y) (s : I → Ω) :
    (∑ t, pairFlow p x y Q s t) = density p s := by
  have h := pushedFlow_row_test (density p) (replacePair x y) Q.q
    (fun a => p x a.1*p y a.2) Q.row (fun t => if t=s then 1 else 0)
  change (∑ r, ∑ t, pairFlow p x y Q r t*(if r=s then 1 else 0)) =
    mean p (fun r => ∑ a : Ω × Ω, p x a.1*p y a.2*(if replacePair x y r a=s then 1 else 0)) at h
  rw [slice_mean p hs x y (fun t => if t=s then 1 else 0)] at h
  simpa [mean,mul_ite,Finset.sum_ite_irrel] using h

lemma pairFlow_col (hs : ∀ i, ∑ a, p i a = 1) (x y : I) (Q : PairCapacity p x y) (t : I → Ω) :
    (∑ s, pairFlow p x y Q s t) = density p t := by
  have h := pushedFlow_col_test (density p) (replacePair x y) Q.q
    (fun a => p x a.1*p y a.2) Q.col (fun s => if s=t then 1 else 0)
  change (∑ r, ∑ s, pairFlow p x y Q r s*(if s=t then 1 else 0)) =
    mean p (fun r => ∑ a : Ω × Ω, p x a.1*p y a.2*(if replacePair x y r a=t then 1 else 0)) at h
  rw [slice_mean p hs x y (fun s => if s=t then 1 else 0)] at h
  simpa [mean,mul_ite] using h

lemma pairFlow_nonneg (hp : ∀ i a, 0 ≤ p i a) (x y : I) (Q : PairCapacity p x y) (s t : I → Ω) :
    0 ≤ pairFlow p x y Q s t := pushedFlow_nonneg _ _ _ (density_nonneg p hp) Q.nonneg s t

lemma pairFlow_energy (x y : I) (Q : PairCapacity p x y) (f : (I → Ω) → ℝ) :
    localEnergy (pairFlow p x y Q) f = pairEnergy p x y Q f :=
  pushedFlow_energy _ _ _ f

lemma baseFlow_nonneg (hp : ∀ i a, 0 ≤ p i a) (i : I) (s t : I → Ω) :
    0 ≤ baseFlow p i s t := pushedFlow_nonneg _ _ _ (density_nonneg p hp)
      (fun a b => mul_nonneg (hp i a) (hp i b)) s t

lemma baseFlow_row (hs : ∀ i, ∑ a, p i a = 1) (i : I) (s : I → Ω) :
    (∑ t, baseFlow p i s t) = density p s := by
  have h := pushedFlow_row_test (density p) (fun r a => Function.update r i a)
    (fun a b => p i a*p i b) (p i) (fun a => by rw [← Finset.mul_sum,hs, mul_one])
    (fun t => if t=s then 1 else 0)
  change (∑ r, ∑ t, baseFlow p i r t*(if r=s then 1 else 0)) =
    mean p (average p i (fun t => if t=s then 1 else 0)) at h
  rw [mean_average p hs] at h
  simpa [mean,mul_ite,Finset.sum_ite_irrel] using h

lemma baseFlow_col (hs : ∀ i, ∑ a, p i a = 1) (i : I) (t : I → Ω) :
    (∑ s, baseFlow p i s t) = density p t := by
  have h := pushedFlow_col_test (density p) (fun r a => Function.update r i a)
    (fun a b => p i a*p i b) (p i) (fun b => by rw [← Finset.sum_mul,hs, one_mul])
    (fun s => if s=t then 1 else 0)
  change (∑ r, ∑ s, baseFlow p i r s*(if s=t then 1 else 0)) =
    mean p (average p i (fun s => if s=t then 1 else 0)) at h
  rw [mean_average p hs] at h
  simpa [mean,mul_ite] using h

lemma baseFlow_energy (hs : ∀ i, ∑ a, p i a = 1) (i : I) (f : (I → Ω) → ℝ) :
    localEnergy (baseFlow p i) f = baseEnergy p i f := by
  rw [baseFlow,pushedFlow_energy]
  have he (s : I → Ω) : localEnergy (fun a b => p i a*p i b) (fun a => f (Function.update s i a)) =
      average p i (fun r => (f r-average p i f r)^2) s := by
    have h := FiniteVariance.variance_eq_pair (p i) (fun a => f (Function.update s i a)) (hs i)
    rw [Fintype.sum_prod_type] at h
    unfold localEnergy
    rw [← h]
    simp only [FiniteVariance.variance,average_apply,Function.update_idem]
  simp_rw [he]
  change mean p (average p i (fun r => (f r-average p i f r)^2)) = _
  rw [mean_average p hs]
  exact mean_square p (f-average p i f)




end

section

open Finset

variable {Ω J : Type*} [Fintype Ω]

lemma localEnergy_add (q r : Ω → Ω → ℝ) (f : Ω → ℝ) :
    localEnergy (fun a b => q a b+r a b) f = localEnergy q f+localEnergy r f := by
  simp only [localEnergy,add_mul,Finset.sum_add_distrib,add_div]

lemma localEnergy_div (q : Ω → Ω → ℝ) (c : ℝ) (f : Ω → ℝ) :
    localEnergy (fun a b => q a b/c) f = localEnergy q f/c := by
  simp only [localEnergy,div_mul_eq_mul_div,← Finset.sum_div]
  ring

lemma localEnergy_sum (s : Finset J) (q : J → Ω → Ω → ℝ) (f : Ω → ℝ) :
    localEnergy (fun a b => ∑ i ∈ s, q i a b) f = ∑ i ∈ s, localEnergy (q i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [localEnergy]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [localEnergy_add,ih]

lemma localEnergy_diag [DecidableEq Ω] (π : Ω → ℝ) (f : Ω → ℝ) :
    localEnergy (fun a b => if a=b then π a else 0) f = 0 := by
  unfold localEnergy
  have h (a b : Ω) : (if a=b then π a else 0)*(f a-f b)^2 = 0 := by
    by_cases hh : a=b <;> simp [hh]
  simp_rw [h]; simp

end

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

omit [DecidableEq I] in
lemma updateCount_pos (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty) :
    0 < updateCount guides base := Nat.add_pos_right _ (Finset.card_pos.mpr hb)

lemma scanFlow_nonneg (hp : ∀ i a, 0 ≤ p i a) (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (s t : I → Ω) : 0 ≤ scanFlow p guides base Q s t := by
  unfold scanFlow
  apply add_nonneg
  · apply div_nonneg _ (by norm_num)
    split_ifs <;> [exact density_nonneg p hp s; exact le_refl _]
  · apply div_nonneg _ (by positivity)
    exact add_nonneg (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
      (fun y _ => pairFlow_nonneg p hp x y (Q x y) s t)))
      (Finset.sum_nonneg (fun i _ => baseFlow_nonneg p hp i s t))

lemma scanFlow_lazy (hp : ∀ i a, 0 ≤ p i a) (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (s : I → Ω) : density p s/2 ≤ scanFlow p guides base Q s s := by
  unfold scanFlow
  simp only [ite_true,le_add_iff_nonneg_right]
  apply div_nonneg _ (by positivity)
  exact add_nonneg (Finset.sum_nonneg (fun x _ => Finset.sum_nonneg
      (fun y _ => pairFlow_nonneg p hp x y (Q x y) s s)))
    (Finset.sum_nonneg (fun i _ => baseFlow_nonneg p hp i s s))

lemma scanFlow_row (hs : ∀ i, ∑ a, p i a = 1) (guides : I → Finset I) (base : Finset I)
    (hb : base.Nonempty) (Q : ∀ x y, PairCapacity p x y) (s : I → Ω) :
    (∑ t, scanFlow p guides base Q s t) = density p s := by
  have hm : (updateCount guides base:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (updateCount_pos guides base hb))
  unfold scanFlow
  rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := guides _)]
  simp_rw [pairFlow_row p hs]
  rw [Finset.sum_comm]
  simp only [baseFlow_row p hs,Finset.sum_const,nsmul_eq_mul]
  simp only [← Finset.sum_mul]
  have hc : (∑ x, ((guides x).card:ℝ))+(base.card:ℝ) = (updateCount guides base:ℝ) := by
    simp [updateCount,Nat.cast_sum]
  rw [← add_mul,hc]
  field_simp
  ring

lemma scanFlow_col (hs : ∀ i, ∑ a, p i a = 1) (guides : I → Finset I) (base : Finset I)
    (hb : base.Nonempty) (Q : ∀ x y, PairCapacity p x y) (t : I → Ω) :
    (∑ s, scanFlow p guides base Q s t) = density p t := by
  have hm : (updateCount guides base:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (updateCount_pos guides base hb))
  unfold scanFlow
  rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_div]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.sum_add_distrib,Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := Finset.univ) (t := guides _)]
  simp_rw [pairFlow_col p hs]
  rw [Finset.sum_comm]
  simp only [baseFlow_col p hs,Finset.sum_const,nsmul_eq_mul]
  simp only [← Finset.sum_mul]
  have hc : (∑ x, ((guides x).card:ℝ))+(base.card:ℝ) = (updateCount guides base:ℝ) := by
    simp [updateCount,Nat.cast_sum]
  rw [← add_mul,hc]
  field_simp
  ring

lemma scanFlow_energy (hs : ∀ i, ∑ a, p i a = 1) (guides : I → Finset I) (base : Finset I)
    (Q : ∀ x y, PairCapacity p x y) (f : (I → Ω) → ℝ) :
    localEnergy (scanFlow p guides base Q) f = scanEnergy p guides base Q f := by
  unfold scanFlow
  rw [localEnergy_add,localEnergy_div,localEnergy_diag,zero_div,zero_add,
    localEnergy_div,localEnergy_add]
  simp_rw [localEnergy_sum,pairFlow_energy,baseFlow_energy p hs]
  rfl

end MatchingFPRAS.Replica

namespace MatchingFPRAS.FiniteChain

open Finset MatchingFPRAS.Replica

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
lemma stepDensity_mean (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hrow : ∀ a, ∑ b, C a b = π a) (f : Ω → ℝ) :
    massMean π (stepDensity π C f) = massMean π f := by
  unfold massMean stepDensity
  simp only [mul_div_cancel₀ _ (ne_of_gt (hp _))]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hrow]

omit [DecidableEq Ω] in
lemma stepDensity_one (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hcol : ∀ b, ∑ a, C a b = π b) : stepDensity π C (fun _ => 1) = (fun _ => 1) := by
  funext b; simp only [stepDensity,mul_one,hcol,div_self (ne_of_gt (hp b))]

omit [DecidableEq Ω] in
lemma stepDensity_linear (π : Ω → ℝ) (C : Ω → Ω → ℝ) (f g : Ω → ℝ) (c d : ℝ) :
    stepDensity π C (fun a => c*f a+d*g a) =
      fun b => c*stepDensity π C f b+d*stepDensity π C g b := by
  funext b
  have hc (a : Ω) : C a b*(c*f a) = c*(C a b*f a) := by ring
  have hd (a : Ω) : C a b*(d*g a) = d*(C a b*g a) := by ring
  simp only [stepDensity,mul_add,Finset.sum_add_distrib,hc,hd,← Finset.mul_sum,
    add_div,mul_div_assoc]

omit [DecidableEq Ω] in
lemma stepDensity_jensen (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (hrow : ∀ a, ∑ b, C a b = π a)
    (hcol : ∀ b, ∑ a, C a b = π b) (f : Ω → ℝ) :
    sqNorm π (stepDensity π C f) ≤ sqNorm π f := by
  have h (b : Ω) : π b*(stepDensity π C f b)^2 ≤ ∑ a, C a b*(f a)^2 := by
    have hh := square_average (fun a => C a b/π b) (fun a => div_nonneg (hC a b) (hp b).le)
      (by rw [← Finset.sum_div,hcol,div_self (ne_of_gt (hp b))]) f
    have he : (∑ a, (C a b/π b)*f a) = stepDensity π C f b := by
      simp only [stepDensity,div_mul_eq_mul_div,Finset.sum_div]
    rw [he] at hh
    have hh := mul_le_mul_of_nonneg_left hh (hp b).le
    simp only [div_mul_eq_mul_div,← Finset.sum_div,mul_div_cancel₀ _ (ne_of_gt (hp b))] at hh
    exact hh
  have hh := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => h b)
  rw [Finset.sum_comm] at hh
  simp_rw [← Finset.sum_mul,hrow] at hh
  exact hh

omit [DecidableEq Ω] in
lemma energy_norm_cross (π : Ω → ℝ) (C : Ω → Ω → ℝ)
    (hrow : ∀ a, ∑ b, C a b = π a) (hcol : ∀ b, ∑ a, C a b = π b)
    (f : Ω → ℝ) : localEnergy C f = sqNorm π f-(∑ a, ∑ b, C a b*f a*f b) := by
  have he (a b : Ω) : C a b*(f a-f b)^2 = C a b*(f a)^2+C a b*(f b)^2-2*(C a b*f a*f b) := by ring
  unfold localEnergy
  simp_rw [he,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hl : (∑ a, ∑ b, C a b*(f a)^2) = sqNorm π f := by
    simp_rw [← Finset.sum_mul,hrow]; rfl
  have hr : (∑ a, ∑ b, C a b*(f b)^2) = sqNorm π f := by
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul,hcol]; rfl
  simp_rw [← Finset.mul_sum]
  rw [hl,hr]; ring

omit [Fintype Ω] in
lemma unlazyFlow_nonneg (π : Ω → ℝ) (C : Ω → Ω → ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (hlazy : ∀ a, π a/2 ≤ C a a) :
    ∀ a b, 0 ≤ unlazyFlow π C a b := by
  intro a b; unfold unlazyFlow
  by_cases h : a=b
  · subst b; simp only [ite_true]; linarith [hlazy a]
  · simp only [ite_eq_right h,sub_zero]; exact mul_nonneg (by norm_num) (hC a b)

lemma unlazyFlow_row (π : Ω → ℝ) (C : Ω → Ω → ℝ) (hrow : ∀ a, ∑ b, C a b = π a) (a : Ω) :
    (∑ b, unlazyFlow π C a b) = π a := by
  simp only [unlazyFlow,Finset.sum_sub_distrib,← Finset.mul_sum,hrow,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  ring

lemma unlazyFlow_col (π : Ω → ℝ) (C : Ω → Ω → ℝ) (hcol : ∀ b, ∑ a, C a b = π b) (b : Ω) :
    (∑ a, unlazyFlow π C a b) = π b := by
  simp only [unlazyFlow,Finset.sum_sub_distrib,← Finset.mul_sum,hcol,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  ring

lemma unlazyFlow_step (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ) (f : Ω → ℝ) :
    stepDensity π (unlazyFlow π C) f = fun b => 2*stepDensity π C f b-f b := by
  funext b
  simp only [stepDensity,unlazyFlow,sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true,sub_div,
    mul_div_cancel_left₀ (f b) (ne_of_gt (hp b))]
  simp_rw [mul_assoc,← Finset.mul_sum]
  ring

lemma lazy_l2 (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (hrow : ∀ a, ∑ b, C a b = π a)
    (hcol : ∀ b, ∑ a, C a b = π b) (hlazy : ∀ a, π a/2 ≤ C a a)
    (f : Ω → ℝ) : sqNorm π (stepDensity π C f) ≤ sqNorm π f-localEnergy C f := by
  have hj := stepDensity_jensen π hp (unlazyFlow π C) (unlazyFlow_nonneg π C hC hlazy)
    (unlazyFlow_row π C hrow) (unlazyFlow_col π C hcol) f
  rw [unlazyFlow_step π hp] at hj
  have he : sqNorm π (fun b => 2*stepDensity π C f b-f b) =
      4*sqNorm π (stepDensity π C f)-4*(∑ a, ∑ b, C a b*f a*f b)+sqNorm π f := by
    have ht (b : Ω) : π b*(2*stepDensity π C f b-f b)^2 =
        4*(π b*(stepDensity π C f b)^2)-4*(π b*stepDensity π C f b*f b)+π b*(f b)^2 := by ring
    unfold sqNorm
    simp_rw [ht,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    congr 2
    simp only [stepDensity,mul_div_cancel₀ _ (ne_of_gt (hp _)),Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he] at hj
  rw [energy_norm_cross π C hrow hcol]
  linarith

end MatchingFPRAS.FiniteChain

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePairProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

omit [DecidableEq V] in
lemma cycleProposal_min (w : E → ℝ)
    (a b : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    min (pairLaw ends w w a) (pairLaw ends w w b)*cycleProposal a b =
      pairLaw ends w w a*cycleProposal a b := by
  rw [min_mul_of_nonneg _ _ (cycleProposal_nonneg a b)]
  have h := cycleProposal_gibbs w a b
  rw [cycleProposal_symmetric b a] at h
  change pairLaw ends w w a*cycleProposal a b = pairLaw ends w w b*cycleProposal a b at h
  rw [h,min_self]




theorem pairKernel_energy (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (Finset.univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (w : E → ℝ) (hw : ∀ e, 0 < w e) (M : PM (fun e v => v ∈ ends e))
    (f g : Finset E → ℝ) :
    localEnergy (metropolisCapacity (pairProposal ends hloop hpar) (pairLaw ends w w))
      (fun a => f a.1.val+g a.2.val) = pairDirichlet ends w f g := by
  classical
  rw [metropolis_energy]
  let F := fun a : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e) =>
    f a.1.val+g a.2.val
  let π := pairLaw ends w w
  let S := ∑ a, ∑ b, min (π a) (π b)*firstLift (switchProposal ends) a b*(F a-F b)^2
  let C := ∑ a, ∑ b, min (π a) (π b)*firstLift (colorProposal ends) a b*(F a-F b)^2
  let Y := ∑ a, ∑ b, min (π a) (π b)*cycleProposal a b*(F a-F b)^2
  have he : localEnergy (offCapacity (pairProposal ends hloop hpar) π) F = (S+C+Y)/6 := by
    unfold localEnergy offCapacity
    change (∑ a, ∑ b, min (π a) (π b)*
      ((firstLift (switchProposal ends) a b+firstLift (colorProposal ends) a b+cycleProposal a b)/3)*
      (F a-F b)^2)/2 = _
    dsimp only [S,C,Y]
    simp only [add_div,Finset.sum_div,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    ring
  have hs : S/6 = switchDirichlet (inc := fun e v => v ∈ ends e) w f := by
    dsimp only [S,π,pairLaw,F]
    rw [firstLift_energy _ (fun A => (gibbs_pos w hw A).le) (gibbs_sum w hw M) _ (fun A => f A.val) (fun A => g A.val)]
    exact switchProposal_dirichlet ends hloop w f
  have hc : C/6 = colorDirichlet ends w f := by
    dsimp only [C,π,pairLaw,F]
    rw [firstLift_energy _ (fun A => (gibbs_pos w hw A).le) (gibbs_sum w hw M) _ (fun A => f A.val) (fun A => g A.val)]
    exact colorProposal_dirichlet ends hloop w f
  have hy : Y/6 = cycleDirichlet (inc := fun e v => v ∈ ends e) w f g := by
    dsimp only [Y,π]
    simp_rw [cycleProposal_min]
    simp only [Fintype.sum_prod_type,pairLaw,F]
    simpa only [Fintype.sum_prod_type,Finset.mul_sum,mul_assoc] using
      cycleProposal_dirichlet (inc := fun e v => v ∈ ends e) w f g
  change localEnergy (offCapacity (pairProposal ends hloop hpar) π) F = _
  rw [he,add_div,add_div,hs,hc,hy]
  rfl

end

section

open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG

attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_1
theorem tree_pair_poincare (hN : 2 ≤ Fintype.card V)
    (M : PM (BagEdge.Incident (bags := bags)))
    (lo hi : ℝ) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (a b : PM (BagEdge.Incident (bags := bags)) → ℝ) :
    let wt := fun e => max lo (min hi (w e))
    localVariance (gibbs wt) a ≤ ((10^4:ℝ)*Fintype.card V*D)^100 *
      treePairEnergy hbags hG wt wt (fun z => a z.1+b z.2) := by
  classical
  let wt := fun e => max lo (min hi (w e))
  have hwt : ∀ e, 0 < wt e := fun e => lt_of_lt_of_le hlo (le_max_left _ _)
  let af : Finset (BagEdge bags) → ℝ := fun S => if h : MatchingOn BagEdge.Incident S Finset.univ then a ⟨S,h⟩ else 0
  let bf : Finset (BagEdge bags) → ℝ := fun S => if h : MatchingOn BagEdge.Incident S Finset.univ then b ⟨S,h⟩ else 0
  have ha (A : PM (BagEdge.Incident (bags := bags))) : af A.val = a A := by simp [af,A.property]
  have hb (A : PM (BagEdge.Incident (bags := bags))) : bf A.val = b A := by simp [bf,A.property]
  have ht := CellDemands.pair_energy_inequality (hbags := hbags) (hG := hG)
    height hheight hstep D hD w hw lo hi hlo hlohi hN M af bf
  have he := pairKernel_energy (fun e : BagEdge bags => e.val.val.1) (fun e => e.val.property)
    (fun e => BagEdge.parallels_card_le (label_memberships_le_two hbags hG) e) wt hwt M af bf
  have he' : treePairEnergy hbags hG wt wt (fun z => af z.1.val+bf z.2.val) =
      pairDirichlet (fun e : BagEdge bags => e.val.val.1) wt af bf := by
    unfold treePairEnergy treePairProposal treePairLaw
    unfold pairLaw at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    congr 4 <;> first | rfl | exact Subsingleton.elim _ _
  change localVariance (gibbs wt) a ≤ _
  change localVariance (gibbs wt) (fun A => af A.val) ≤ _ at ht
  simp_rw [ha,hb] at he' ht
  exact ht.trans_eq (congrArg (fun z => ((10^4:ℝ)*Fintype.card V*D)^100*z) he'.symm)

end

open Finset MatchingFPRAS.Replica

variable {V L : Type*} [Fintype V] [DecidableEq V] [Fintype L] [DecidableEq L]

variable {bags : V → Finset L} {G : SimpleGraph L}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : L → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℝ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG

attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_2
theorem adjacent_tree_pair_poincare (hN : 2 ≤ Fintype.card V)
    (M : PM (BagEdge.Incident (bags := bags))) (t : ℕ)
    (a b : PM (BagEdge.Incident (bags := bags)) → ℝ) :
    let c : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹
    let upper := fun e => tierClamp c (t+1) (w e)
    let lower := fun e => tierClamp c t (w e)
    localVariance (gibbs upper) a ≤ (2*((10^4:ℝ)*Fintype.card V*D)^100) *
      treePairEnergy hbags hG upper lower (fun z => a z.1+b z.2) := by
  classical
  let c : ℝ := 1+((Fintype.card V:ℝ)^2)⁻¹
  have hc : 1 ≤ c := by
    dsimp [c]; have : 0 ≤ ((Fintype.card V:ℝ)^2)⁻¹ := by positivity
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hp1 : 1 ≤ c^(t+1) := one_le_pow₀ hc
  have hp0 : 0 < c^(t+1) := pow_pos hc0 _
  have hilo : (c^(t+1))⁻¹ ≤ c^(t+1) := (inv_le_one₀ hp0).mpr hp1 |>.trans hp1
  let upper := fun e => tierClamp c (t+1) (w e)
  let lower := fun e => tierClamp c t (w e)
  have hupper : ∀ e, 0 < upper e := fun e => tierClamp_pos hc0 _ _
  have hwpos : ∀ e, 0 < w e := fun e =>
    lt_of_lt_of_le (div_pos (hheight e.color) (lt_of_lt_of_le (by norm_num) hD)) (hw e).1
  have hv := tree_pair_poincare (hbags := hbags) (hG := hG)
    height hheight hstep D hD w hw hN M (c^(t+1))⁻¹ (c^(t+1)) (inv_pos.mpr hp0) hilo a b
  change localVariance (gibbs upper) a ≤ ((10^4:ℝ)*Fintype.card V*D)^100 *
    treePairEnergy hbags hG upper upper (fun z => a z.1+b z.2) at hv
  have hd (z : PM (BagEdge.Incident (bags := bags)) × PM (BagEdge.Incident (bags := bags))) :
      (1/2:ℝ)*treePairLaw upper upper z ≤ treePairLaw upper lower z := by
    have h := (adjacent_gibbs (fun e : BagEdge bags => e.val.val.1) (fun e => e.val.property)
      hN w hwpos t z.2).1
    change gibbs upper z.2/2 ≤ gibbs lower z.2 at h
    have h := mul_le_mul_of_nonneg_left h (gibbs_pos upper hupper z.1).le
    dsimp only [treePairLaw]
    nlinarith only [h]
  have he := metropolis_energy_domination (treePairProposal hbags hG)
    (treePairLaw upper upper) (treePairLaw upper lower) (1/2) (by norm_num) hd
    (fun z => a z.1+b z.2)
  change (1/2:ℝ)*treePairEnergy hbags hG upper upper (fun z => a z.1+b z.2) ≤
    treePairEnergy hbags hG upper lower (fun z => a z.1+b z.2) at he
  have hL : 0 ≤ ((10^4:ℝ)*Fintype.card V*D)^100 := by positivity
  have hh := mul_le_mul_of_nonneg_left he hL
  change localVariance (gibbs upper) a ≤ _
  nlinarith only [hv,hh]

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Replica.Ladder

open Finset

lemma rank_le {T q : ℕ} (x : Slot T q) : rank x ≤ T := by
  have h := (ofLex x).1.isLt
  dsimp [rank]; omega

lemma mem_base {T q : ℕ} (x : Slot T q) : x ∈ base T q ↔ rank x = T := by
  constructor
  · rintro hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hx
    rw [← hj]; rfl
  · intro hx
    apply Finset.mem_image.mpr
    refine ⟨(ofLex x).2,Finset.mem_univ _,?_⟩
    apply ofLex.injective
    apply Prod.ext
    · apply Fin.ext; exact hx.symm
    · rfl

lemma guides_base {T q : ℕ} (x : Slot T q) (hx : x ∈ base T q) : guides x = ∅ := by
  simp [guides,(mem_base x).mp hx]

lemma guides_card {T q : ℕ} (x : Slot T q) (hx : x ∉ base T q) : (guides x).card = q := by
  have h : rank x < T := lt_of_le_of_ne (rank_le x) (fun he => hx ((mem_base x).mpr he))
  rw [guides,dite_eq_left h,Finset.card_image_of_injective]
  · simp
  · intro j k h
    exact congrArg (fun x : Slot T q => (ofLex x).2) h

lemma guides_order {T q : ℕ} (x y : Slot T q) (hy : y ∈ guides x) : x < y := by
  unfold guides at hy
  split_ifs at hy with h
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    exact Prod.Lex.left (ofLex x).2 j (show (ofLex x).1 < ⟨rank x+1,by omega⟩ from by
      change rank x < rank x+1; omega)
  · simp at hy

lemma guides_tier {T q : ℕ} (x y : Slot T q) (hy : y ∈ guides x) : tier x = tier y+1 := by
  unfold guides at hy
  split_ifs at hy with h
  · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
    simp only [tier,rank]
    change T-rank x = T-(rank x+1)+1
    omega
  · simp at hy

lemma slots_card (T q : ℕ) : Fintype.card (Slot T q) = (T+1)*q := by
  rw [Fintype.card_congr (ofLex : Slot T q ≃ Fin (T+1) × Fin q)]
  simp

lemma updates_count (T q : ℕ) : (∑ x : Slot T q, (guides x).card)+(base T q).card = T*q^2+q := by
  classical
  have hc : ((base T q)ᶜ).card = T*q := by
    rw [Finset.card_compl,slots_card,base_card,Nat.add_mul,one_mul,Nat.add_sub_cancel]
  have hs : ∑ x : Slot T q, (guides x).card = T*q*q := by
    rw [← Finset.sum_add_sum_compl (base T q)]
    have hb : (∑ x ∈ base T q, (guides x).card) = 0 := by
      apply Finset.sum_eq_zero; intro x hx; rw [guides_base x hx]; rfl
    have hg : (∑ x ∈ (base T q)ᶜ, (guides x).card) = ∑ x ∈ (base T q)ᶜ, q := by
      apply Finset.sum_congr rfl; intro x hx
      exact guides_card x (Finset.mem_compl.mp hx)
    rw [hb,hg,Finset.sum_const,smul_eq_mul,hc,zero_add]
  rw [hs,base_card]; ring

end MatchingFPRAS.Replica.Ladder

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_3
omit [DecidableEq V] [DecidableEq J] in
lemma slotLaw_sum {T q : ℕ} (w : BagEdge bags → ℝ) (x : Slot T q)
    (M : PM (BagEdge.Incident (bags := bags))) : (∑ A, slotLaw w x A) = 1 :=
  gibbs_sum _ (slotWeight_pos w x) M

end

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : J → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℕ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG

attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_4
theorem concrete_ladder_poincare (hN : 2 ≤ Fintype.card V)
    (M₀ : PM (BagEdge.Incident (bags := bags))) (T : ℕ)
    (f : (Slot T (32*(10^4*Fintype.card V*D)^100) → PM (BagEdge.Incident (bags := bags))) → ℝ) :
    let q := 32*(10^4*Fintype.card V*D)^100
    MatchingFPRAS.Replica.variance (slotLaw w) f ≤ ((8*(T*q^2+q):ℕ):ℝ)/3 *
      scanEnergy (slotLaw w) guides (base T q) (treeLadderCapacity hbags hG w) f := by
  classical
  let q : ℕ := 32*(10^4*Fintype.card V*D)^100
  let L : ℝ := ((10^4:ℝ)*Fintype.card V*D)^100
  have hDc : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hNp : 0 < (Fintype.card V:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hN)
  have hDp : 0 < (D:ℝ) := lt_of_lt_of_le (by norm_num) hDc
  have hL : 0 < L := by dsimp [L]; positivity
  have hq : (q:ℝ) = 32*L := by norm_num [q,L,Nat.cast_mul,Nat.cast_pow]
  have hqn : 0 < q := by
    have : (0:ℝ) < (q:ℝ) := by rw [hq]; positivity
    exact_mod_cast this
  have hQ : ∀ x y : Slot T q, y ∈ guides x →
      PairPoincare (slotLaw w) x y (treeLadderCapacity hbags hG w x y) (2*L) := by
    intro x y hy a b
    have ht := adjacent_tree_pair_poincare (hbags := hbags) (hG := hG)
      height hheight hstep (D:ℝ) hDc w hw hN M₀ (tier y) a b
    change localVariance (gibbs (slotWeight w x)) a ≤ (2*L)*
      treePairEnergy hbags hG (slotWeight w x) (slotWeight w y) (fun z => a z.1+b z.2)
    unfold slotWeight
    rw [guides_tier x y hy]
    exact ht
  have hh := replica_gap (slotLaw w) (fun x A => (slotLaw_pos w x A).le)
    (fun x => slotLaw_sum w x M₀) guides (base T q) (base_nonempty T q hqn)
    q L hL hq (fun x hx => guides_card x hx) (fun x hx => guides_base x hx)
    (fun x y hy => guides_order x y hy) (treeLadderCapacity hbags hG w) hQ f
  rw [updates_count] at hh
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Evolve
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteChain

open Finset MatchingFPRAS.Replica

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
lemma evolve_mean (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hrow : ∀ a, ∑ b, C a b = π a) (n : ℕ) (f : Ω → ℝ) :
    massMean π (evolve π C n f) = massMean π f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [evolve,stepDensity_mean π hp C hrow,ih]

omit [DecidableEq Ω] in
lemma evolve_center (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hcol : ∀ b, ∑ a, C a b = π b) (n : ℕ) (f : Ω → ℝ) :
    evolve π C n (fun a => f a-1) = fun a => evolve π C n f a-1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evolve,ih]
    have he : (fun a => evolve π C n f a-1) = fun a => 1*evolve π C n f a+(-1)*(1:ℝ) := by funext a; ring
    rw [he,stepDensity_linear,stepDensity_one π hp C hcol]
    funext a; ring

lemma lazy_decay (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ)
    (hC : ∀ a b, 0 ≤ C a b) (hrow : ∀ a, ∑ b, C a b = π a)
    (hcol : ∀ b, ∑ a, C a b = π b) (hlazy : ∀ a, π a/2 ≤ C a a)
    (γ : ℝ) (hγ : γ ≤ 1)
    (hgap : ∀ f, massMean π f = 0 → γ*sqNorm π f ≤ localEnergy C f)
    (f : Ω → ℝ) (hf : massMean π f = 0) (n : ℕ) :
    sqNorm π (evolve π C n f) ≤ (1-γ)^n*sqNorm π f := by
  induction n with
  | zero => simp [evolve]
  | succ n ih =>
    have hm : massMean π (evolve π C n f) = 0 := (evolve_mean π hp C hrow n f).trans hf
    have hl := lazy_l2 π hp C hC hrow hcol hlazy (evolve π C n f)
    have hg := hgap (evolve π C n f) hm
    have hh := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hγ)
    rw [evolve,pow_succ]
    nlinarith

lemma deltaDensity_mean (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (z : Ω) :
    massMean π (deltaDensity π z) = 1 := by
  simp [massMean,deltaDensity,mul_ite,ne_of_gt (hp z)]

omit [DecidableEq Ω] in
lemma sqNorm_center (π f : Ω → ℝ) (hs : ∑ a, π a = 1) :
    sqNorm π (fun a => f a-1) = sqNorm π f-2*massMean π f+1 := by
  have he (a : Ω) : π a*(f a-1)^2 = π a*(f a)^2-2*(π a*f a)+π a := by ring
  simp only [sqNorm,massMean,he,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,hs]

lemma deltaDensity_sqNorm (π : Ω → ℝ) (_hp : ∀ a, 0 < π a) (z : Ω) :
    sqNorm π (deltaDensity π z) = (π z)⁻¹ := by
  simp only [sqNorm,deltaDensity,ite_pow,zero_pow (by decide : (2:ℕ) ≠ 0),mul_ite,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  field_simp

lemma deltaDensity_center_norm (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (hs : ∑ a, π a = 1) (z : Ω) :
    sqNorm π (fun a => deltaDensity π z a-1) = (π z)⁻¹-1 := by
  rw [sqNorm_center π _ hs,deltaDensity_sqNorm π hp,deltaDensity_mean π hp]
  ring

omit [DecidableEq Ω] in
lemma abs_sum_sq_le (π f : Ω → ℝ) (hp : ∀ a, 0 ≤ π a) (hs : ∑ a, π a = 1) :
    (∑ a, |π a*f a|)^2 ≤ sqNorm π f := by
  have hh := square_average π hp hs (fun a => |f a|)
  simpa only [abs_mul,abs_of_nonneg (hp _),sq_abs,sqNorm] using hh

lemma walk_density (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (C : Ω → Ω → ℝ) (z : Ω) (n : ℕ) (a : Ω) :
    walk π C z n a = π a*evolve π C n (deltaDensity π z) a := by
  induction n generalizing a with
  | zero =>
    by_cases h : a=z
    · subst a; simp [walk,evolve,deltaDensity,ne_of_gt (hp z)]
    · simp [walk,evolve,deltaDensity,h]
  | succ n ih =>
    simp only [walk,ih,kernel,evolve,stepDensity,mul_div_cancel₀ _ (ne_of_gt (hp a))]
    apply Finset.sum_congr rfl
    intro b _
    field_simp [ne_of_gt (hp b)]

lemma meeting_bound (π : Ω → ℝ) (hp : ∀ a, 0 < π a) (hs : ∑ a, π a = 1)
    (C : Ω → Ω → ℝ) (hC : ∀ a b, 0 ≤ C a b)
    (hrow : ∀ a, ∑ b, C a b = π a) (hcol : ∀ b, ∑ a, C a b = π b)
    (hlazy : ∀ a, π a/2 ≤ C a a) (γ : ℝ) (hγ : γ ≤ 1)
    (hgap : ∀ f, massMean π f = 0 → γ*sqNorm π f ≤ localEnergy C f)
    (z : Ω) (n : ℕ) :
    (∑ a, |walk π C z n a-π a|)^2 ≤ (1-γ)^n*((π z)⁻¹-1) := by
  let f : Ω → ℝ := fun a => deltaDensity π z a-1
  have hf : massMean π f = 0 := by
    simp only [f,massMean,mul_sub,mul_one,Finset.sum_sub_distrib,hs]
    change massMean π (deltaDensity π z)-1=0
    rw [deltaDensity_mean π hp]; ring
  have hb := lazy_decay π hp C hC hrow hcol hlazy γ hγ hgap f hf n
  have ha := abs_sum_sq_le π (evolve π C n f) (fun a => (hp a).le) hs
  have he : (fun a => π a*evolve π C n f a) = fun a => walk π C z n a-π a := by
    funext a
    dsimp only [f]
    rw [evolve_center π hp C hcol,walk_density π hp C z n]
    ring
  have hh : (∑ a, |π a*evolve π C n f a|) = ∑ a, |walk π C z n a-π a| := by
    exact congrArg (fun g : Ω → ℝ => ∑ a, |g a|) he
  rw [hh] at ha
  have hn : sqNorm π f = (π z)⁻¹-1 := deltaDensity_center_norm π hp hs z
  rw [hn] at hb
  exact ha.trans hb

end MatchingFPRAS.FiniteChain

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

attribute [local instance] OAI.MatchingFPRAS.Transport.instDecidableEqPMBagEdgeIncident
attribute [local instance] OAI.MatchingFPRAS.Transport.instDecidableEqPMBagEdgeIncident_1
variable {hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b}

variable {hG : G.IsAcyclic}

variable (height : J → ℝ) (hheight : ∀ l, 0 < height l)

variable (hstep : ∀ a b, G.Adj a b → height a ≤ 2 * height b)

variable (D : ℕ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)

variable (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3 * height e.color)

include hheight hstep hD hw hbags hG

attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_5
attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_6
theorem concrete_ladder_mixing (hN : 2 ≤ Fintype.card V)
    (M₀ : PM (BagEdge.Incident (bags := bags))) (T : ℕ)
    (z : Slot T (32*(10^4*Fintype.card V*D)^100) → PM (BagEdge.Incident (bags := bags)))
    (n : ℕ) :
    let q := 32*(10^4*Fintype.card V*D)^100
    let ν := ladderLaw w T q
    let C := ladderFlow hbags hG w T q
    (∑ s, |MatchingFPRAS.FiniteChain.walk ν C z n s-ν s|)^2 ≤
      (1-3/((8*(T*q^2+q):ℕ):ℝ))^n*((ν z)⁻¹-1) := by
  classical
  dsimp only
  let q : ℕ := 32*(10^4*Fintype.card V*D)^100
  let ν := ladderLaw w T q
  let C := ladderFlow hbags hG w T q
  have hq : 0 < q := by
    have hV : 0 < Fintype.card V := lt_of_lt_of_le (by norm_num) hN
    have hd : 0 < D := lt_of_lt_of_le (by norm_num) hD
    dsimp [q]; positivity
  have hM : 0 < ((8*(T*q^2+q):ℕ):ℝ) := by exact_mod_cast (by omega : 0 < 8*(T*q^2+q))
  have hp (s) : 0 < ν s := by
    apply Finset.prod_pos; intro i _; exact slotLaw_pos w i (s i)
  have hs : (∑ s, ν s) = 1 := density_sum (slotLaw w) (fun i => slotLaw_sum w i M₀)
  have hbase : (base T q).Nonempty := Finset.card_pos.mp (by rw [base_card]; exact hq)
  have hC (s t) : 0 ≤ C s t := scanFlow_nonneg (slotLaw w) (fun i a => (slotLaw_pos w i a).le)
    guides (base T q) (treeLadderCapacity hbags hG w) s t
  have hrow (s) : (∑ t, C s t) = ν s := scanFlow_row (slotLaw w) (fun i => slotLaw_sum w i M₀)
    guides (base T q) hbase (treeLadderCapacity hbags hG w) s
  have hcol (t) : (∑ s, C s t) = ν t := scanFlow_col (slotLaw w) (fun i => slotLaw_sum w i M₀)
    guides (base T q) hbase (treeLadderCapacity hbags hG w) t
  have hlazy (s) : ν s/2 ≤ C s s := scanFlow_lazy (slotLaw w) (fun i a => (slotLaw_pos w i a).le)
    guides (base T q) (treeLadderCapacity hbags hG w) s
  have hγ : 3/((8*(T*q^2+q):ℕ):ℝ) ≤ 1 := by
    apply (div_le_one hM).mpr
    exact_mod_cast (by omega : 3 ≤ 8*(T*q^2+q))
  have hgap (f) (hf : MatchingFPRAS.FiniteChain.massMean ν f = 0) :
      (3/((8*(T*q^2+q):ℕ):ℝ))*MatchingFPRAS.FiniteChain.sqNorm ν f ≤ localEnergy C f := by
    have hh := concrete_ladder_poincare (hbags := hbags) (hG := hG) height hheight hstep D hD w hw hN M₀ T f
    dsimp only at hh
    have hv : MatchingFPRAS.Replica.variance (slotLaw w) f = MatchingFPRAS.FiniteChain.sqNorm ν f := by
      have hm : MatchingFPRAS.Replica.mean (slotLaw w) f = 0 := hf
      unfold MatchingFPRAS.Replica.variance MatchingFPRAS.Replica.dot
      simp only [hm,Pi.sub_apply,sub_zero]
      unfold MatchingFPRAS.FiniteChain.sqNorm
      apply Finset.sum_congr rfl
      intro s _; change ν s*f s*f s=ν s*(f s)^2; ring
    rw [hv] at hh
    have he : localEnergy C f = scanEnergy (slotLaw w) guides (base T q) (treeLadderCapacity hbags hG w) f :=
      scanFlow_energy (slotLaw w) (fun i => slotLaw_sum w i M₀) guides (base T q) (treeLadderCapacity hbags hG w) f
    rw [← he] at hh
    change MatchingFPRAS.FiniteChain.sqNorm ν f ≤ ((8*(T*q^2+q):ℕ):ℝ)/3*localEnergy C f at hh
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hM).mpr
    linarith

  exact MatchingFPRAS.FiniteChain.meeting_bound ν hp hs C hC hrow hcol hlazy
    (3/((8*(T*q^2+q):ℕ):ℝ)) hγ hgap z n

end

section

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma chosenEdge_mem (A : PM inc) (v : V) : chosenEdge A v ∈ A.val :=
  (Classical.choose_spec (A.property.2 v (mem_univ v))).1.1

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma chosenEdge_incident (A : PM inc) (v : V) : inc (chosenEdge A v) v :=
  (Classical.choose_spec (A.property.2 v (mem_univ v))).1.2

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma chosenEdge_injective (hinc : ∀ e, ∃ v, inc e v) :
    Function.Injective (chosenEdge (inc := inc)) := by
  intro A B h
  apply Subtype.ext; ext e
  have hh (A B : PM inc) (h : chosenEdge A = chosenEdge B) : e ∈ A.val → e ∈ B.val := by
    intro he
    obtain ⟨v,hv⟩ := hinc e
    have heq : e = chosenEdge A v := A.property.unique (mem_univ v) he hv
      (chosenEdge_mem A v) (chosenEdge_incident A v)
    rw [heq,congrFun h v]
    exact chosenEdge_mem B v
  exact ⟨hh A B h,hh B A h.symm⟩

omit [DecidableEq E] in
lemma pm_card_le (hinc : ∀ e, ∃ v, inc e v) :
    Fintype.card (PM inc) ≤ Fintype.card E ^ Fintype.card V := by
  classical
  simpa only [Fintype.card_fun] using Fintype.card_le_of_injective chosenEdge (chosenEdge_injective hinc)

omit [DecidableEq V] [DecidableEq E] in
lemma gibbs_mass_lower (hinc : ∀ e, ∃ v, inc e v) (w : E → ℝ)
    (D B : ℝ) (hD : 1 ≤ D) (hB : 1 ≤ B)
    (hw : ∀ e, D⁻¹ ≤ w e ∧ w e ≤ B) (A : PM inc) :
    (Fintype.card (PM inc)*(D*B)^Fintype.card V)⁻¹ ≤ gibbs w A := by
  classical
  have hD0 : 0 < D := by linarith
  have hB0 : 0 < B := by linarith
  have hw0 : ∀ e, 0 < w e := fun e => (inv_pos.mpr hD0).trans_le (hw e).1
  have lower (M : PM inc) : (D^Fintype.card V)⁻¹ ≤ matchingWeight w M := by
    have hh : (D⁻¹)^M.val.card ≤ matchingWeight w M := by
      simpa only [matchingWeight,Finset.prod_const] using Finset.prod_le_prod
        (fun e (_ : e ∈ M.val) => (inv_pos.mpr hD0).le) (fun e _ => (hw e).1)
    rw [inv_pow] at hh
    exact (inv_anti₀ (pow_pos hD0 _) (pow_le_pow_right₀ hD (PM.card_le_vertices hinc M))).trans hh
  have upper (M : PM inc) : matchingWeight w M ≤ B^Fintype.card V := by
    have hh : matchingWeight w M ≤ B^M.val.card := by
      simpa only [matchingWeight,Finset.prod_const] using Finset.prod_le_prod
        (fun e (_ : e ∈ M.val) => (hw0 e).le) (fun e _ => (hw e).2)
    exact hh.trans (pow_le_pow_right₀ hB (PM.card_le_vertices hinc M))
  have hc : 0 < (Fintype.card (PM inc):ℝ) := by
    have : Nonempty (PM inc) := ⟨A⟩
    exact_mod_cast Fintype.card_pos
  have hz : partition (inc := inc) w ≤ Fintype.card (PM inc)*B^Fintype.card V := by
    have he : partition (inc := inc) w = ∑ M : PM inc, matchingWeight w M := by
      unfold partition
      congr
      all_goals (try exact Subsingleton.elim _ _)
    rw [he]
    calc
      _ ≤ ∑ _M : PM inc, B^Fintype.card V := Finset.sum_le_sum (fun M _ => upper M)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hp := partition_pos w hw0 A
  have hden : 0 < (Fintype.card (PM inc):ℝ)*B^Fintype.card V := mul_pos hc (pow_pos hB0 _)
  calc
    _ = (D^Fintype.card V)⁻¹/(Fintype.card (PM inc)*B^Fintype.card V) := by
      rw [mul_pow]; field_simp
    _ ≤ matchingWeight w A/partition (inc := inc) w :=
      div_le_div₀ (matchingWeight_pos w hw0 A).le (lower A) hp hz
    _ = _ := rfl

end

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

lemma tierClamp_range {c lo hi w : ℝ} (hc : 1 ≤ c) (hlo : lo ≤ 1) (hhi : 1 ≤ hi)
    (hw : lo ≤ w ∧ w ≤ hi) (t : ℕ) : lo ≤ tierClamp c t w ∧ tierClamp c t w ≤ hi := by
  have hp : 1 ≤ c^t := one_le_pow₀ hc
  have hip : (c^t)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
  constructor
  · exact le_trans (le_min (hlo.trans hp) hw.1) (le_max_right _ _)
  · exact max_le (hip.trans hhi) ((min_le_right _ _).trans hw.2)

omit [DecidableEq V] [Fintype J] [DecidableEq J] in
lemma slotWeight_range (D K : ℕ) (hD : 1 ≤ D) (w : BagEdge bags → ℝ)
    (hw : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K) {T q : ℕ} (x : Slot T q) (e : BagEdge bags) :
    (D:ℝ)⁻¹ ≤ slotWeight w x e ∧ slotWeight w x e ≤ 3*4^K := by
  apply tierClamp_range
  · unfold tierBase; exact le_add_of_nonneg_right (by positivity)
  · apply inv_le_one_of_one_le₀; exact_mod_cast hD
  · have h : (1:ℝ) ≤ 4^K := one_le_pow₀ (by norm_num)
    linarith
  · exact hw e

attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_7
omit [DecidableEq J] in
lemma bag_pm_card_le
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) :
    Fintype.card (PM (BagEdge.Incident (bags := bags))) ≤ (2*Fintype.card V^2)^Fintype.card V := by
  apply (pm_card_le BagEdge.exists_incident).trans
  exact Nat.pow_le_pow_left (bag_edges_card_le hbags hG) _

lemma denominator_power_bound (N D K : ℕ) (hN : 2 ≤ N) (hD : 1 ≤ D) :
    ((2*(N:ℝ)^2)^N)*((D:ℝ)*(3*4^K))^N ≤
      (2:ℝ)^(10*N*(K+Nat.clog 2 (N*D+2)+1)) := by
  let a := Nat.clog 2 (N*D+2)
  have hp : (N*D+2:ℝ) ≤ (2:ℝ)^a := by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (N*D+2)
  have hn : (N:ℝ) ≤ 2^a := by
    have hd : (1:ℝ) ≤ D := by exact_mod_cast hD
    have hn0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
    have hnd : (N:ℝ) ≤ N*D := by nlinarith
    exact hnd.trans (le_trans (by linarith) hp)
  have hd : (D:ℝ) ≤ 2^a := by
    have hn2 : (2:ℝ) ≤ N := by exact_mod_cast hN
    have hd0 : (0:ℝ) ≤ D := Nat.cast_nonneg D
    have hnd : (D:ℝ) ≤ N*D := by nlinarith
    exact hnd.trans (le_trans (by linarith) hp)
  have hfour : (4:ℝ)^K = 2^(2*K) := by rw [pow_mul]; norm_num
  have hb : 2*(N:ℝ)^2*((D:ℝ)*(3*4^K)) ≤ 2^(3+3*a+2*K) := by
    calc
      _ ≤ 2*(2^a)^2*((2^a)*(3*4^K)) := mul_le_mul
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg N) hn 2) (by norm_num))
        (mul_le_mul_of_nonneg_right hd (by positivity)) (by positivity) (by positivity)
      _ ≤ 2*(2^a)^2*((2^a)*(4*4^K)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (by norm_num : (3:ℝ) ≤ 4) (by positivity)
      _ = _ := by
        rw [hfour]
        calc
          _ = (2:ℝ)^3*2^(a*2)*2^a*2^(2*K) := by rw [pow_mul]; norm_num; ring
          _ = _ := by simp only [← pow_add]; congr 1; omega
  calc
    _ = (2*(N:ℝ)^2*((D:ℝ)*(3*4^K)))^N := (mul_pow _ _ _).symm
    _ ≤ (2^(3+3*a+2*K))^N := pow_le_pow_left₀ (by positivity) hb N
    _ = (2:ℝ)^((3+3*a+2*K)*N) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by dsimp only [a]; nlinarith)

end

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_8
omit [DecidableEq J] in
lemma slotLaw_minimum_mass
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (D K : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ Fintype.card V)
    (w : BagEdge bags → ℝ) (hw : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K)
    {T q : ℕ} (x : Slot T q) (A : PM (BagEdge.Incident (bags := bags))) :
    ((2:ℝ)^(10*Fintype.card V*(K+Nat.clog 2 (Fintype.card V*D+2)+1)))⁻¹ ≤ slotLaw w x A := by
  have hl := gibbs_mass_lower BagEdge.exists_incident (slotWeight w x) D (3*4^K)
    (by exact_mod_cast hD) (by
      have hh : (1:ℝ) ≤ 4^K := one_le_pow₀ (by norm_num)
      linarith)
    (slotWeight_range D K hD w hw x) A
  have hc : (Fintype.card (PM (BagEdge.Incident (bags := bags))):ℝ) ≤
      (2*Fintype.card V^2:ℝ)^Fintype.card V := by exact_mod_cast bag_pm_card_le hbags hG
  have hd := (mul_le_mul_of_nonneg_right hc (by positivity : (0:ℝ) ≤ ((D:ℝ)*(3*4^K))^Fintype.card V)).trans
    (denominator_power_bound (Fintype.card V) D K hN hD)
  have hp : 0 < (Fintype.card (PM (BagEdge.Incident (bags := bags))):ℝ)*
      ((D:ℝ)*(3*4^K))^Fintype.card V := by
    have : Nonempty (PM (BagEdge.Incident (bags := bags))) := ⟨A⟩
    have hc0 : (0:ℝ) < Fintype.card (PM (BagEdge.Incident (bags := bags))) := by exact_mod_cast Fintype.card_pos
    have hd0 : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    positivity
  exact (inv_anti₀ hp hd).trans hl

omit [DecidableEq J] in
lemma ladderLaw_power_lower
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (D K : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ Fintype.card V)
    (w : BagEdge bags → ℝ) (hw : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K) (T q : ℕ)
    (z : Slot T q → PM (BagEdge.Incident (bags := bags))) :
    ((2:ℝ)^(10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1)))⁻¹ ≤ ladderLaw w T q z := by
  have hh := Finset.prod_le_prod (s := Finset.univ)
    (fun (x : Slot T q) _ => (by positivity : (0:ℝ) ≤ ((2:ℝ)^(10*Fintype.card V*(K+Nat.clog 2 (Fintype.card V*D+2)+1)))⁻¹))
    (fun x _ => slotLaw_minimum_mass hbags hG D K hD hN w hw x (z x))
  simp only [prod_const,card_univ,slots_card,← inv_pow,← pow_mul] at hh
  have he : 10*Fintype.card V*(K+Nat.clog 2 (Fintype.card V*D+2)+1)*((T+1)*q) =
      10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1) := by ring
  rw [he] at hh
  simpa only [inv_pow,ladderLaw,density] using hh

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_LadderL
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

omit [DecidableEq J] in
theorem ladder_minimum_mass
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (D K : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ Fintype.card V)
    (w : BagEdge bags → ℝ)
    (hw : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K) (T q : ℕ)
    (z : Slot T q → PM (BagEdge.Incident (bags := bags))) :
    Real.log ((ladderLaw w T q z)⁻¹) ≤
      (10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1):ℕ) := by
  have hl := ladderLaw_power_lower hbags hG D K hD hN w hw T q z
  have hp : 0 < ladderLaw w T q z := by
    apply Finset.prod_pos; intro x _; exact slotLaw_pos w x (z x)
  have hu := inv_anti₀ (by positivity : (0:ℝ) < ((2:ℝ)^(10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1)))⁻¹) hl
  rw [inv_inv] at hu
  have hh := Real.log_le_log (inv_pos.mpr hp) hu
  rw [Real.log_pow] at hh
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hΛ : (0:ℝ) ≤ (10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1):ℕ) := Nat.cast_nonneg _
  exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hΛ)

end

end MatchingFPRAS.Transport

namespace MatchingFPRAS.FiniteChain

lemma log_inv_le_ceil_logb {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    -Real.log ξ ≤ (⌈Real.logb 2 ξ⁻¹⌉₊:ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog21 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hxi : 1 ≤ ξ⁻¹ := (one_le_inv₀ hξ).mpr hξ1.le
  have hlogxi : 0 ≤ Real.log ξ⁻¹ := Real.log_nonneg hxi
  have hb : 0 ≤ Real.logb 2 ξ⁻¹ := div_nonneg hlogxi hlog2.le
  have he : Real.logb 2 ξ⁻¹*Real.log 2 = -Real.log ξ := by
    rw [Real.logb,div_mul_cancel₀ _ hlog2.ne',Real.log_inv]
  exact (by nlinarith : -Real.log ξ ≤ Real.logb 2 ξ⁻¹).trans (Nat.le_ceil _)

lemma mixing_at_steps {a u γ Λ ξ : ℝ} {n b : ℕ}
    (ha : 0 ≤ a) (hu : 0 < u) (hγ : γ ≤ 1) (hΛ : 0 ≤ Λ)
    (hξ : 0 < ξ) (hb : -Real.log ξ ≤ (b:ℝ))
    (hmass : Real.log u⁻¹ ≤ Λ)
    (hsteps : 2*(Λ+(b:ℝ)+1) ≤ γ*n)
    (hmix : a^2 ≤ (1-γ)^n*(u⁻¹-1)) : a/2 ≤ ξ := by
  have hmass' : u⁻¹ ≤ Real.exp Λ := (Real.log_le_iff_le_exp (inv_pos.mpr hu)).mp hmass
  have hp : 0 ≤ 1-γ := by linarith
  have he : (1-γ)^n ≤ Real.exp (-γ*(n:ℝ)) := by
    calc
      _ ≤ (Real.exp (-γ))^n := pow_le_pow_left₀ hp (Real.one_sub_le_exp_neg γ) n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsq : a^2 ≤ ξ^2 := by
    calc
      _ ≤ (1-γ)^n*(u⁻¹-1) := hmix
      _ ≤ (1-γ)^n*Real.exp Λ := mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hp _)
      _ ≤ Real.exp (-γ*(n:ℝ))*Real.exp Λ := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = Real.exp (-γ*(n:ℝ)+Λ) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (2*Real.log ξ) := Real.exp_le_exp.mpr (by linarith)
      _ = ξ^2 := by rw [show (2:ℝ)=(2:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hξ]
  nlinarith

end MatchingFPRAS.FiniteChain

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_10
attribute [local instance] OAI.MatchingFPRAS.Transport.instDecidableEqPMBagEdgeIncident_2
theorem ideal_ladder_sampling
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (height : J → ℝ) (hheight : ∀ l, 0 < height l)
    (hstep : ∀ a b, G.Adj a b → height a ≤ 2*height b)
    (D K : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ Fintype.card V) (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3*height e.color)
    (hglobal : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K)
    (M₀ : PM (BagEdge.Incident (bags := bags))) (T : ℕ)
    (z : Slot T (ladderQ (Fintype.card V) D) → PM (BagEdge.Incident (bags := bags)))
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    let ν := ladderLaw w T (ladderQ (Fintype.card V) D)
    let C := ladderFlow hbags hG w T (ladderQ (Fintype.card V) D)
    (∑ s, |MatchingFPRAS.FiniteChain.walk ν C z (ladderSteps (Fintype.card V) D K T ξ) s-ν s|)/2 ≤ ξ := by
  classical
  dsimp only
  let N := Fintype.card V
  let L := ladderL N D
  let q := ladderQ N D
  let M := ladderM N D T
  let Λ := ladderLambda N D K T
  let b := ⌈Real.logb 2 ξ⁻¹⌉₊
  let ν := ladderLaw w T q
  let C := ladderFlow hbags hG w T q
  let n := ladderSteps N D K T ξ
  let γ : ℝ := 3/(8*(M:ℝ))
  have hL0 : 0 < L := by
    have hn : 0 < N := by dsimp [N]; omega
    have hd : 0 < D := by omega
    dsimp [L,ladderL]; positivity
  have hq0 : 0 < q := by dsimp [q,ladderQ]; exact Nat.mul_pos (by decide) hL0
  have hM0 : 0 < M := by dsimp [M,ladderM]; omega
  have hMr : (0:ℝ) < M := by exact_mod_cast hM0
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast hL0
  have hΛr : (0:ℝ) ≤ Λ := Nat.cast_nonneg _
  have hγ : γ ≤ 1 := by
    dsimp [γ]
    apply (div_le_one (by positivity : (0:ℝ)<8*M)).mpr
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hM0
    linarith
  have hsteps : 2*((Λ:ℝ)+(b:ℝ)+1) ≤ γ*(n:ℝ) := by
    have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg _
    have hfac : (0:ℝ) ≤ (Λ:ℝ)+(b:ℝ)+1 := by positivity
    calc
      _ ≤ ((15:ℝ)/2)*(L:ℝ)*((Λ:ℝ)+(b:ℝ)+1) :=
        mul_le_mul_of_nonneg_right (by linarith) hfac
      _ = _ := by
        dsimp [γ,n,ladderSteps,L,M,Λ,b]
        push_cast
        have hm0 : (ladderM N D T:ℝ) ≠ 0 := hMr.ne'
        field_simp [hm0]
        ring
  have hp : 0 < ν z := by
    apply Finset.prod_pos; intro i _; exact slotLaw_pos w i (z i)
  have hmass : Real.log ((ν z)⁻¹) ≤ (Λ:ℝ) :=
    ladder_minimum_mass hbags hG D K hD hN w hglobal T q z
  have hmix := concrete_ladder_mixing (hbags := hbags) (hG := hG)
    height hheight hstep D hD w hw hN M₀ T z n
  dsimp only at hmix
  have hmix' : (∑ s, |MatchingFPRAS.FiniteChain.walk ν C z n s-ν s|)^2 ≤
      (1-γ)^n*((ν z)⁻¹-1) := by
    simp only [γ,ν,C,q,M,ladderM,ladderQ,ladderL,N,Nat.cast_mul,Nat.cast_ofNat] at hmix ⊢
    convert hmix using 1
    all_goals try with_reducible_and_instances rfl
    congr 4
  exact MatchingFPRAS.FiniteChain.mixing_at_steps
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hp hγ hΛr hξ
    (MatchingFPRAS.FiniteChain.log_inv_le_ceil_logb hξ hξ1) hmass hsteps hmix'

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Marked
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Marking

open Finset MatchingFPRAS.Transport

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I]

variable [DecidableEq V] [DecidableEq E] [DecidableEq I]

variable (inc : E → V → Prop)

omit [Fintype E] [DecidableEq V] [DecidableEq I] in
lemma sum_marks (part : E → I → ℝ) (M : Matchings inc univ) :
    (∑ m : (↥M.val → I),mass inc part ⟨M,m⟩)=∏ e ∈ M.val,collapse part e := by
  classical
  rw [Finset.prod_subtype M.val (fun _ => Iff.rfl)]
  exact (Fintype.prod_sum (fun e : M.val => part e.val)).symm

omit [DecidableEq V] [DecidableEq I] in
theorem total_mass (part : E → I → ℝ) :
    (∑ a : Marked (I:=I) inc,mass inc part a)=partitionWeight inc (collapse part) univ := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun M _ => sum_marks inc part M

omit [Fintype E] [Fintype I] [DecidableEq V] [DecidableEq E] [DecidableEq I] in
lemma mass_nonneg (part : E → I → ℝ) (hp : ∀ e i,0 ≤ part e i) (a : Marked (I:=I) inc) :
    0 ≤ mass inc part a := Finset.prod_nonneg fun _ _ => hp _ _

omit [DecidableEq V] [DecidableEq I] in
lemma law_sum (part : E → I → ℝ) (hz : partitionWeight inc (collapse part) univ ≠ 0) :
    ∑ a : Marked (I:=I) inc,law inc part a=1 := by
  simp only [law,←Finset.sum_div,total_mass,div_self hz]

omit [DecidableEq V] [DecidableEq E] [DecidableEq I] in
lemma law_from_reveal (part : E → I → ℝ) (hc : ∀ e,collapse part e≠0)
    (a : Marked (I:=I) inc) :
    ((∏ e ∈ a.1.val,collapse part e)/partitionWeight inc (collapse part) univ) *
      conditional inc part a.1 a.2 = law inc part a := by
  classical
  rw [conditional,Finset.prod_div_distrib,←Finset.prod_subtype a.1.val (fun _ => Iff.rfl)]
  have hn : (∏ e ∈ a.1.val,collapse part e)≠0 := Finset.prod_ne_zero_iff.mpr (fun e _ => hc e)
  unfold law mass
  field_simp

end MatchingFPRAS.Marking

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Representation Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_3
lemma sourcePortions_collapse (w : V → V → ℝ) (K D : ℕ) :
    Marking.collapse (sourcePortions w K D)=sourceBagWeight w K D := by
  funext e
  simp [Marking.collapse,sourcePortions,Fin.sum_univ_succ,sourceBagWeight]

lemma sourcePortions_nonneg (w : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K D : ℕ)
    (e : BagEdge (sourceBags w K)) (i : Fin 3) : 0 ≤ sourcePortions w K D e i := by
  classical
  fin_cases i
  · exact sourceRealPortion_nonneg w hw K e
  · change 0 ≤ bagHeight w K e.val.val.2/D-probePortion w K D e
    apply sub_nonneg.mpr
    unfold probePortion
    split_ifs
    · exact div_le_div_of_nonneg_right (bagHeight_one w K _) (Nat.cast_nonneg D)
    · exact div_nonneg (bagHeight_pos w K _).le (Nat.cast_nonneg D)
  · change 0 ≤ probePortion w K D e
    unfold probePortion
    split_ifs <;> positivity

open scoped Classical

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_4
lemma sourceLaw_sum (w : V → V → ℝ) (K D : ℕ) (hz : sourceBagZ w K D≠0) :
    ∑ a : SourceMarked w K,sourceLaw w K D a=1 := by
  apply Marking.law_sum
  simpa only [sourcePortions_collapse,sourceBagZ] using hz

lemma sourceLaw_nonneg (w : V → V → ℝ) (hw : ∀ x y,0 < w x y) (K D : ℕ)
    (hz : 0 ≤ sourceBagZ w K D) (a : SourceMarked w K) : 0 ≤ sourceLaw w K D a := by
  unfold sourceLaw Marking.law
  rw [sourcePortions_collapse]
  exact div_nonneg (Marking.mass_nonneg _ _ (sourcePortions_nonneg w hw K D) a) hz

lemma observableA_range (w : V → V → ℝ) (K : ℕ) (a : SourceMarked w K) :
    0 ≤ observableA w K a ∧ observableA w K a ≤ 1 := by
  classical
  unfold observableA
  split_ifs <;> norm_num

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Tv
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

lemma tv_triangle (p q r : Ω → ℝ) : tv p r ≤ tv p q+tv q r := by
  unfold tv
  rw [←add_div,←sum_add_distrib]
  exact div_le_div_of_nonneg_right (sum_le_sum (fun s _ => abs_sub_le _ _ _)) (by norm_num)

theorem event_sub_le (p q : Ω → ℝ) (hs : ∑ x,p x=∑ x,q x) (P : Ω → Prop) :
    |event p P-event q P| ≤ tv p q := by
  let A : Finset Ω := univ.filter P
  have hz : ∑ x,(p x-q x)=0 := by rw [sum_sub_distrib,hs,sub_self]
  have he : event p P-event q P=∑ x ∈ A,(p x-q x) := by
    simp only [event,←sum_sub_distrib,A,sum_filter]
    apply sum_congr rfl
    intro x _
    split_ifs <;> simp
  have hc : ∑ x ∈ Aᶜ,(p x-q x)= -(∑ x ∈ A,(p x-q x)) := by
    have h := Finset.sum_add_sum_compl A (fun x => p x-q x)
    rw [hz] at h
    linarith
  have ha := abs_sum_le_sum_abs (fun x => p x-q x) A
  have hb := abs_sum_le_sum_abs (fun x => p x-q x) Aᶜ
  rw [hc,abs_neg] at hb
  have hab := Finset.sum_add_sum_compl A (fun x => |p x-q x|)
  rw [he]
  unfold tv
  linarith

lemma bind_contraction (p q : Ω → ℝ) (k : Ω → Ψ → ℝ)
    (hk : ∀ x y,0 ≤ k x y) (hs : ∀ x,∑ y,k x y=1) :
    tv (bind p k) (bind q k) ≤ tv p q := by
  unfold tv bind
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ = ∑ y,|∑ x,(p x-q x)*k x y| := by simp only [sub_mul,sum_sub_distrib]
    _ ≤ ∑ y,∑ x,|(p x-q x)*k x y| := sum_le_sum (fun y _ => abs_sum_le_sum_abs _ _)
    _ = _ := by
      rw [sum_comm]
      simp_rw [abs_mul,abs_of_nonneg (hk _ _),←mul_sum,hs,mul_one]

lemma bind_perturbation (p : Ω → ℝ) (k l : Ω → Ψ → ℝ)
    (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1) (ε : ℝ) (he : ∀ x,tv (k x) (l x) ≤ ε) :
    tv (bind p k) (bind p l) ≤ ε := by
  unfold tv bind
  have h : ∑ y,|∑ x,p x*k x y-∑ x,p x*l x y| ≤ 2*ε := by
    calc
      _ = ∑ y,|∑ x,p x*(k x y-l x y)| := by simp only [mul_sub,sum_sub_distrib]
      _ ≤ ∑ y,∑ x,|p x*(k x y-l x y)| := sum_le_sum (fun y _ => abs_sum_le_sum_abs _ _)
      _ = ∑ x,p x*(∑ y,|k x y-l x y|) := by
        rw [sum_comm]; simp_rw [abs_mul,abs_of_nonneg (hp _),←mul_sum]
      _ ≤ ∑ x,p x*(2*ε) := by
        apply sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_left _ (hp x)
        have hh := he x
        unfold tv at hh
        linarith
      _ = _ := by rw [←sum_mul,hs,one_mul]
  linarith

lemma push_contraction (p q : Ω → ℝ) (f : Ω → Ψ) : tv (push p f) (push q f) ≤ tv p q := by
  have he (r : Ω → ℝ) : push r f=bind r (fun x y => if f x=y then 1 else 0) := by
    funext y
    simp only [push,bind,mul_ite,mul_one,mul_zero]
  rw [he p,he q]
  exact
    bind_contraction p q (fun x y => if f x=y then 1 else 0)
      (fun x y => by split_ifs <;> norm_num) (fun x => by simp)

lemma tensor_tv (p q : Ω → ℝ) (r s : Ψ → ℝ)
    (hp : ∀ x,0 ≤ p x) (hps : ∑ x,p x=1) (hs : ∀ y,0 ≤ s y) (hss : ∑ y,s y=1) :
    tv (tensor p r) (tensor q s) ≤ tv p q+tv r s := by
  have hv (x : Ω) (y : Ψ) : |p x*r y-q x*s y| ≤ p x*|r y-s y|+|p x-q x| *s y := by
    have he : p x*r y-q x*s y=p x*(r y-s y)+(p x-q x)*s y := by ring
    rw [he]
    simpa only [abs_mul,abs_of_nonneg (hp x),abs_of_nonneg (hs y)] using abs_add_le (p x*(r y-s y)) ((p x-q x)*s y)
  unfold tv tensor
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ x,∑ y,(p x*|r y-s y|+|p x-q x| *s y) := sum_le_sum (fun x _ => sum_le_sum (fun y _ => hv x y))
    _ = _ := by simp_rw [sum_add_distrib,←mul_sum,hss,mul_one,←sum_mul,hps,one_mul]; ring

lemma tv_equiv (e : Ω ≃ Ψ) (p q : Ψ → ℝ) : tv (p ∘ e) (q ∘ e)=tv p q := by
  unfold tv
  rw [←e.sum_comp (fun y => |p y-q y|)]
  rfl

theorem iid_tv (p q : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (hps : ∑ x,p x=1)
    (hq : ∀ x,0 ≤ q x) (hqs : ∑ x,q x=1) (n : ℕ) :
    tv (iid p n) (iid q n) ≤ n*tv p q := by
  induction n with
  | zero => simp [tv,iid]
  | succ n ih =>
    let e : (Ω×(Fin n → Ω)) ≃ (Fin (n+1) → Ω) := Fin.consEquiv (fun _ : Fin (n+1) => Ω)
    have hpE : iid p (n+1) ∘ e=tensor p (iid p n) := by
      funext x
      simp [iid,tensor,e,Fin.prod_univ_succ]
    have hqE : iid q (n+1) ∘ e=tensor q (iid q n) := by
      funext x
      simp [iid,tensor,e,Fin.prod_univ_succ]
    rw [←tv_equiv e,hpE,hqE]
    have ht := tensor_tv p q (iid p n) (iid q n) hp hps (iid_nonneg q hq n) (iid_sum q hqs n)
    push_cast
    nlinarith

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]

lemma product_marginal (p : I → Ω → ℝ) (hs : ∀ i,∑ a,p i a=1) (j : I) :
    push (product p) (fun x => x j)=p j := by
  classical
  funext y
  let q : I → Ω → ℝ := fun i a => if i=j then (if a=y then p i a else 0) else p i a
  have he (x : I → Ω) : (if x j=y then product p x else 0)=∏ i,q i (x i) := by
    by_cases h : x j=y
    · simp only [ite_eq_left h,product]
      apply prod_congr rfl
      intro i _
      by_cases hi : i=j
      · subst i; simp [q,h]
      · simp [q,hi]
    · simp only [ite_eq_right h]
      symm
      apply prod_eq_zero (mem_univ j)
      simp [q,h]
  have hq (i : I) : ∑ a,q i a=if i=j then p j y else 1 := by
    by_cases h : i=j
    · subst i; simp [q]
    · simp [q,h,hs i]
  unfold push
  simp_rw [he]
  rw [←Fintype.prod_sum]
  simp_rw [hq]
  simp

end Product


end MatchingFPRAS.Variation

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J}

noncomputable local instance instDecidableEqPMBagEdgeIncident_3_r3ec436_1 : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _
lemma topSlot_tier (T q : ℕ) (hq : 0<q) : tier (topSlot T q hq)=T := by simp [tier,rank,topSlot]

attribute [local instance] OAI.MatchingFPRAS.Transport.instFintypeBagEdge_11
omit [DecidableEq V] [DecidableEq J] in
lemma ladder_top_marginal (w : BagEdge bags → ℝ) (T q : ℕ) (hq : 0<q)
    (M : PM (BagEdge.Incident (bags := bags))) :
    Variation.push (ladderLaw w T q) (fun x => x (topSlot T q hq))=slotLaw w (topSlot T q hq) := by
  exact Variation.product_marginal (slotLaw w) (fun i => slotLaw_sum w i M) _

omit [DecidableEq V] [Fintype J] [DecidableEq J] in
lemma slotWeight_top (w : BagEdge bags → ℝ) (D K T q : ℕ) (hD : 0<D) (hq : 0<q)
    (hw : ∀ e,(D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K)
    (hT : max (D:ℝ) (3*4^K) ≤ (tierBase V)^T) :
    slotWeight w (topSlot T q hq)=w := by
  funext e
  have hlo : ((tierBase V)^T)⁻¹ ≤ w e :=
    (inv_anti₀ (by exact_mod_cast hD) ((le_max_left _ _).trans hT)).trans (hw e).1
  have hhi : w e ≤ (tierBase V)^T := (hw e).2.trans ((le_max_right _ _).trans hT)
  simp only [slotWeight,topSlot_tier,tierClamp,min_eq_right hhi,max_eq_right hlo]

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Cumulative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteChoice

open Finset

lemma cumulative_mono {r : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j) : Monotone (cumulative p) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro j _
  by_cases ha : j.val<a
  · simp only [ite_eq_left ha,ite_eq_left (lt_of_lt_of_le ha hab),le_refl]
  · simp only [ite_eq_right ha]
    split_ifs <;> [exact hp j; exact le_refl _]

lemma gridInterval_eq (K : ℕ) (hK : 0 < K) (a b : ℚ) (hb : b ≤ 1) :
    gridInterval K a b = Finset.Ico ⌈(K:ℚ)*a⌉₊ ⌈(K:ℚ)*b⌉₊ := by
  have hKr : (0:ℚ)<K := by exact_mod_cast hK
  have hlast : ⌈(K:ℚ)*b⌉₊ ≤ K := Nat.ceil_le.mpr (by nlinarith)
  ext j
  simp only [gridInterval,Finset.mem_filter,Finset.mem_range,Finset.mem_Ico,
    Nat.ceil_le,Nat.lt_ceil]
  constructor
  · rintro ⟨_,ha,hb⟩
    constructor
    · have := (le_div_iff₀ hKr).mp ha; nlinarith
    · have := (div_lt_iff₀ hKr).mp hb; nlinarith
  · rintro ⟨ha,hb⟩
    constructor
    · exact lt_of_lt_of_le (Nat.lt_ceil.mpr hb) hlast
    · constructor
      · apply (le_div_iff₀ hKr).mpr; nlinarith
      · apply (div_lt_iff₀ hKr).mpr; nlinarith

lemma gridInterval_card (K : ℕ) (hK : 0 < K) (a b : ℚ) (hab : a ≤ b) (hb : b ≤ 1) :
    ((gridInterval K a b).card:ℚ) = (⌈(K:ℚ)*b⌉₊:ℚ)-(⌈(K:ℚ)*a⌉₊:ℚ) := by
  rw [gridInterval_eq K hK a b hb,Nat.card_Ico,Nat.cast_sub]
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left hab (by positivity))

lemma gridInterval_error (K : ℕ) (hK : 0 < K) (a b : ℚ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    |((gridInterval K a b).card:ℚ)/K-(b-a)| ≤ 2/(K:ℚ) := by
  have hKr : (0:ℚ)<K := by exact_mod_cast hK
  rw [gridInterval_card K hK a b hab hb]
  have ha₀ := Nat.le_ceil ((K:ℚ)*a)
  have hb₀ := Nat.le_ceil ((K:ℚ)*b)
  have ha₁ := Nat.ceil_lt_add_one (mul_nonneg hKr.le ha)
  have hb₁ := Nat.ceil_lt_add_one (mul_nonneg hKr.le (ha.trans hab))
  rw [abs_sub_le_iff]
  constructor
  · apply (le_div_iff₀ hKr).mpr
    simp only [sub_mul,div_mul_cancel₀ _ (ne_of_gt hKr)]
    nlinarith
  · apply (le_div_iff₀ hKr).mpr
    simp only [sub_mul,div_mul_cancel₀ _ (ne_of_gt hKr)]
    nlinarith




lemma cumulative_nonneg {r : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j) (i : ℕ) :
    0 ≤ cumulative p i := by
  apply Finset.sum_nonneg; intro j _; split_ifs <;> [exact hp j; exact le_rfl]

lemma cumulative_le_one {r : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (i : ℕ) (hi : i ≤ r) : cumulative p i ≤ 1 := by
  rw [← cumulative_total p hs]; exact cumulative_mono p hp hi

lemma choose_eq_iff {r K : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (hK : 0 < K) (J : Fin K) (i : Fin r) :
    choose p hs hK J=i ↔ cumulative p i.val ≤ (J.val:ℚ)/K ∧
      (J.val:ℚ)/K < cumulative p (i.val+1) := by
  constructor
  · intro he
    have hl := choose_lower p hs hK J
    have hu := choose_upper p hs hK J
    rw [he] at hl hu
    exact ⟨hl,hu⟩
  · rintro ⟨hl,hu⟩
    apply le_antisymm (choose_le p hs hK J i hu)
    by_contra h
    have hlt : (choose p hs hK J).val+1 ≤ i.val := by
      have hh : choose p hs hK J < i := lt_of_not_ge h
      exact hh
    have hm := cumulative_mono p hp hlt
    have hh := choose_upper p hs hK J
    linarith

lemma outputLaw_grid {r K : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (hK : 0 < K) (i : Fin r) :
    outputLaw p hs hK i = ((gridInterval K (cumulative p i.val) (cumulative p (i.val+1))).card:ℚ)/K := by
  unfold outputLaw
  congr 2
  apply Finset.card_bij (fun J _ => J.val)
  · intro J hJ
    have he := (Finset.mem_filter.mp hJ).2
    have hc := (choose_eq_iff p hp hs hK J i).mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr J.isLt,hc⟩
  · intro J _ J' _ h; exact Fin.ext h
  · intro j hj
    have hh := Finset.mem_filter.mp hj
    let J : Fin K := ⟨j,Finset.mem_range.mp hh.1⟩
    refine ⟨J,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    exact (choose_eq_iff p hp hs hK J i).mpr hh.2

lemma outputLaw_error {r K : ℕ} (p : Fin r → ℚ) (hp : ∀ j, 0 ≤ p j)
    (hs : ∑ j, p j = 1) (hK : 0 < K) (i : Fin r) :
    |outputLaw p hs hK i-p i| ≤ 2/(K:ℚ) := by
  rw [outputLaw_grid p hp hs hK i,← cumulative_step p i]
  exact gridInterval_error K hK _ _ (cumulative_nonneg p hp i.val)
    (cumulative_mono p hp (by omega)) (cumulative_le_one p hp hs _ (by have := i.isLt; omega))




theorem fixed_bit_choice {r : ℕ} (p : Fin r → ℚ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (k : ℕ) :
    (∑ i, |outputLaw p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) i-p i|)/2 ≤
      2*r/(2:ℚ)^k := by
  have hK : 0 < (2:ℕ)^k := pow_pos (by norm_num) k
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => outputLaw_error p hp hs hK i)
  simp only [Finset.sum_const,Finset.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
  have hr : (0:ℚ) ≤ r := Nat.cast_nonneg r
  have hpow : (0:ℚ) < 2^k := pow_pos (by norm_num) k
  have hz : 0 ≤ r/(2:ℚ)^k := div_nonneg hr hpow.le
  calc
    (∑ i, |outputLaw p hs hK i-p i|)/2 ≤ ((r:ℚ)*(2/(2:ℚ)^k))/2 :=
      div_le_div_of_nonneg_right hh (by norm_num)
    _ = (r:ℚ)/(2:ℚ)^k := by ring
    _ ≤ 2*r/(2:ℚ)^k := div_le_div_of_nonneg_right (by linarith) hpow.le




end MatchingFPRAS.FiniteChoice

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_RunBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteChoice

open Finset

lemma tapeLaw_eq {r : ℕ} (p : Fin r → ℚ) (hs : ∑ i, p i = 1) (k : ℕ) :
    tapeLaw p hs k = outputLaw p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) := by
  funext i
  have hcard : (univ.filter (fun bits : Fin k → Bool => chooseBits p hs k bits=i)).card =
      (univ.filter (fun J : Fin (2^k) => choose p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) J=i)).card := by
    calc
      _ = ∑ bits : Fin k → Bool, if chooseBits p hs k bits=i then (1:ℕ) else 0 := by simp
      _ = ∑ J : Fin (2^k), if choose p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) J=i then (1:ℕ) else 0 :=
        by
          simp only [chooseBits]
          convert (tapeIndex k).sum_comp
            (fun J : Fin (2^k) => if choose p hs (pow_pos (by norm_num : 0 < (2:ℕ)) k) J=i then (1:ℕ) else 0) using 1
          all_goals try with_reducible_and_instances rfl
          congr 3
      _ = _ := by simp
  simp only [tapeLaw,outputLaw,hcard,Nat.cast_pow,Nat.cast_ofNat]

end MatchingFPRAS.FiniteChoice

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Component
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport.Sparse

open Finset

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable (ends : E → Sym2 V)

lemma discrepancies_eq (A B : PM (fun e v => v ∈ ends e)) :
    discrepancies ends A B = discrepancyComponents A B := by
  rw [discrepancies,allComponents_eq]
  rfl

lemma cycle_eq (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) (S : Finset E) :
    cycle ends p S = cycleMove p S := by
  unfold cycle cycleMove
  simp only [allComponents_eq]

lemma discrepancies_card (A B : PM (fun e v => v ∈ ends e)) :
    (discrepancies ends A B).card ≤ A.val.card+B.val.card := by
  calc
    _ ≤ (allComponents ends (A.val ∪ B.val)).card := card_filter_le _ _
    _ ≤ (A.val ∪ B.val).card := card_image_le
    _ ≤ _ := card_union_le _ _

end MatchingFPRAS.Transport.Sparse

namespace MatchingFPRAS

namespace WeightedOptions

open Finset

variable {Ω Ψ : Type*}

variable [DecidableEq Ω]

lemma law_nonneg (c : WeightedOptions Ω) (b : Ω) : 0 ≤ c.law b := by
  apply sum_nonneg
  intro i _
  split_ifs <;> [exact c.nonneg i; exact le_rfl]

lemma law_sum [Fintype Ω] (c : WeightedOptions Ω) : ∑ b, c.law b=1 := by
  unfold law
  rw [sum_comm]
  simpa using c.total

lemma mix_law (p : ℚ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (a b : WeightedOptions Ω) (x : Ω) :
    (mix p hp hp1 a b).law x=p*a.law x+(1-p)*b.law x := by
  change (∑ i : Fin (a.size+b.size), if Fin.addCases a.out b.out i=x then
    Fin.addCases (fun i=>p*a.mass i) (fun i=>(1-p)*b.mass i) i else (0:ℚ))=_
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,law,mul_sum]
  congr 1 <;> apply sum_congr rfl <;> intro i _ <;> split_ifs <;> simp

lemma sum_law_mul [Fintype Ω] (c : WeightedOptions Ω) (f : Ω → ℚ) :
    ∑ b, c.law b*f b = ∑ i, c.mass i*f (c.out i) := by
  simp only [law,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp only [ite_mul,zero_mul]
  simp

lemma map_law [Fintype Ω] [DecidableEq Ψ] (f : Ω → Ψ) (c : WeightedOptions Ω) (b : Ψ) :
    (c.map f).law b = ∑ a, if f a=b then c.law a else 0 := by
  change (∑ i : Fin c.size, if f (c.out i)=b then c.mass i else (0:ℚ))=_
  calc
    _ = ∑ i, c.mass i*(if f (c.out i)=b then 1 else 0) := by
      simp only [mul_ite,mul_one,mul_zero]
    _ = ∑ a, c.law a*(if f a=b then 1 else 0) :=
      (c.sum_law_mul (fun a => if f a=b then (1:ℚ) else 0)).symm
    _ = _ := by simp

lemma map_first_law [DecidableEq Ψ] (c : WeightedOptions Ω) (a : Ψ) (b : Ω × Ψ) :
    (c.map (fun x => (x,a))).law b = if a=b.2 then c.law b.1 else 0 := by
  change (∑ i : Fin c.size, if (c.out i,a)=b then c.mass i else (0:ℚ))=_
  rcases b with ⟨b,d⟩
  by_cases h : a=d
  · subst d
    simp [law]
  · simp [h]

lemma accept_law (c : WeightedOptions Ω) (hold : Ω) (p : Ω → ℚ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∀ a, p a ≤ 1) (b : Ω) :
    (c.accept hold p hp hp1).law b = c.law b*p b +
      if hold=b then ∑ i, c.mass i*(1-p (c.out i)) else 0 := by
  change (∑ i : Fin (c.size+c.size), if Fin.addCases c.out (fun _=>hold) i=b then
    Fin.addCases (fun i=>c.mass i*p (c.out i)) (fun i=>c.mass i*(1-p (c.out i))) i
    else (0:ℚ))=_
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right]
  congr 1
  · rw [law,sum_mul]
    apply sum_congr rfl
    intro i _
    split_ifs with h
    · rw [h]
    · simp
  · split_ifs <;> simp_all

variable [LinearOrder Ω]

lemma uniform_law (s : Finset Ω) (hs : s.Nonempty) (b : Ω) :
    (uniform s hs).law b=if b ∈ s then (s.card:ℚ)⁻¹ else 0 := by
  unfold law uniform
  change (∑ i, if (numbering s i).val=b then (s.card:ℚ)⁻¹ else 0)=_
  rw [(numbering s).sum_comp (fun i : ↥s => if i.val=b then (s.card:ℚ)⁻¹ else 0)]
  rw [Finset.sum_coe_sort s (fun x : Ω => if x=b then (s.card:ℚ)⁻¹ else 0)]
  simp

lemma neighbors_law (a : Ω) (s : Finset Ω) (d : ℕ) (hd : s.card ≤ d) (b : Ω) :
    (neighbors a s d hd).law b=(if b ∈ s then (d:ℚ)⁻¹ else 0)+
      (if a=b then 1-(s.card:ℚ)/d else 0) := by
  unfold law neighbors
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc,Fin.lastCases_last]
  congr 1
  rw [(numbering s).sum_comp (fun i : ↥s => if i.val=b then (d:ℚ)⁻¹ else 0)]
  rw [Finset.sum_coe_sort s (fun x : Ω => if x=b then (d:ℚ)⁻¹ else 0)]
  simp

end WeightedOptions

end MatchingFPRAS

namespace MatchingFPRAS.Transport.Sparse

open Finset WeightedOptions

variable {Ω : Type*} [Fintype Ω] [LinearOrder Ω] [DecidableEq Ω]

omit [LinearOrder Ω] in
lemma erased_eq (R : Ω → Ω → Prop) (s : Finset Ω) (a : Ω)
    (hs : ∀ b, b ∈ s ↔ R a b) : s.erase a = relationDestinations R a := by
  classical
  ext b
  simp only [mem_erase,relationDestinations,mem_filter,mem_univ,true_and,hs,ne_comm]

lemma neighbors_real (R : Ω → Ω → Prop) (s : Finset Ω) (d : ℕ) (a b : Ω)
    (hs : s=relationDestinations R a) (hd : s.card ≤ d) :
    ((WeightedOptions.neighbors a s d hd).law b : ℝ) = relationProposal R d a b := by
  classical
  rw [WeightedOptions.neighbors_law]
  push_cast
  subst s
  rw [relationProposal,relationOff_sum]
  by_cases hab : a=b
  · subst b
    simp [relationDestinations]
  · simp only [hab,ite_false,relationOff]
    split_ifs <;> push_cast <;> simp

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

variable (ends : E → Sym2 V)

attribute [local instance] OAI.MatchingFPRAS.Transport.Sparse.pmOrder
lemma colorTable_law (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A B : PM (fun e v => v ∈ ends e)) :
    ((colorTable ends hloop hpar A).law B : ℝ)=colorProposal ends A B := by
  exact neighbors_real (ColorChange ends) ((colors ends A).erase A) (Fintype.card V) A B
    (erased_eq _ _ _ (mem_colors ends A)) (color_degree ends hloop hpar A)

lemma switchTable_law (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (A B : PM (fun e v => v ∈ ends e)) :
    ((switchTable ends hloop hpar A).law B : ℝ)=switchProposal ends A B := by
  exact neighbors_real (fun A B => TwoEdgeSwitch A B) ((switches ends A).erase A)
    (8*(Fintype.card V/2).choose 2) A B
    (erased_eq _ _ _ (mem_switches ends A)) (switch_degree ends hloop hpar A)

attribute [local instance] OAI.MatchingFPRAS.Transport.Sparse.finsetOrder
lemma cycleTable_law (p q : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    ((cycleTable ends p).law q : ℝ)=cycleProposal p q := by
  classical
  by_cases h : (discrepancies ends p.1 p.2).Nonempty
  · have h' : (discrepancyComponents p.1 p.2).Nonempty := by rwa [←discrepancies_eq]
    rw [cycleTable,dite_eq_left h,cycleProposal,ite_eq_left h',WeightedOptions.map_law]
    push_cast
    apply sum_congr rfl
    intro S _
    rw [WeightedOptions.uniform_law,cycle_eq,discrepancies_eq]
    unfold cycleTerm
    split_ifs <;> simp_all
  · have h' : ¬(discrepancyComponents p.1 p.2).Nonempty := by rwa [←discrepancies_eq]
    rw [cycleTable,dite_eq_right h,cycleProposal,ite_eq_right h',WeightedOptions.pure_law]
    split_ifs <;> norm_num

lemma pairTable_law (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (p q : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    ((pairTable ends hloop hpar p).law q : ℝ)=pairProposalRaw ends p q := by
  unfold pairTable
  rw [WeightedOptions.mix_law,WeightedOptions.mix_law,
    WeightedOptions.map_first_law,WeightedOptions.map_first_law]
  push_cast
  unfold pairProposalRaw firstLift
  by_cases h : p.2=q.2
  · simp only [ite_eq_left h]
    rw [switchTable_law,colorTable_law,cycleTable_law]
    ring
  · simp only [ite_eq_right h]
    push_cast
    rw [cycleTable_law]
    ring

lemma pairTable_size (hloop : ∀ e, ¬(ends e).IsDiag)
    (hpar : ∀ e, (univ.filter (fun f => ends f = ends e)).card ≤ 2)
    (p : PM (fun e v => v ∈ ends e) × PM (fun e v => v ∈ ends e)) :
    (pairTable ends hloop hpar p).size ≤
      8*p.1.val.card.choose 2 + 2*p.1.val.card + (p.1.val.card+p.2.val.card)+3 := by
  have hs : ((switches ends p.1).erase p.1).card ≤ 8*p.1.val.card.choose 2 := card_erase_le.trans (switches_card ends hpar p.1)
  have hc : ((colors ends p.1).erase p.1).card ≤ 2*p.1.val.card := card_erase_le.trans (colors_card ends hpar p.1)
  have hy := discrepancies_card ends p.1 p.2
  simp only [pairTable,WeightedOptions.mix,WeightedOptions.map,switchTable,colorTable,
    WeightedOptions.neighbors]
  have hz : (cycleTable ends p).size ≤ p.1.val.card+p.2.val.card+1 := by
    unfold cycleTable
    split_ifs <;> simp only [WeightedOptions.map,WeightedOptions.uniform,WeightedOptions.pure]
    · omega
    · omega
  omega

end MatchingFPRAS.Transport.Sparse

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MetropolisChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.WeightedOptions

open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma real_law_sum (c : WeightedOptions Ω) : ∑ b, (c.law b : ℝ)=1 := by
  exact_mod_cast c.law_sum

lemma row_eq_of_off (f g : Ω → ℝ) (hf : ∑ x, f x=1) (hg : ∑ x, g x=1)
    (a : Ω) (h : ∀ b, a≠b → f b=g b) : f=g := by
  funext b
  by_cases hab : a=b
  · subst b
    have he : ∑ b ∈ univ.erase a, f b = ∑ b ∈ univ.erase a, g b := by
      apply sum_congr rfl
      intro b hb
      exact h b (ne_of_mem_erase hb).symm
    rw [←sum_erase_add _ _ (mem_univ a)] at hf hg
    linarith
  · exact h b hab

lemma min_ratio (x y : ℝ) (hx : 0 < x) : min (1:ℝ) (y/x) = min x y / x := by
  by_cases h : x≤y
  · rw [min_eq_left ((le_div_iff₀ hx).mpr (by simpa using h)),min_eq_left h,div_self hx.ne']
  · rw [min_eq_right ((div_le_one hx).mpr (le_of_not_ge h)),min_eq_right (le_of_not_ge h)]

theorem metropolisChoice_law (P : Replica.SymmetricProposal Ω) (c : Ω → WeightedOptions Ω)
    (hc : ∀ a b, ((c a).law b : ℝ)=P.q a b)
    (w : Ω → ℚ) (hw : ∀ a, 0 < w a) (a b : Ω) :
    (((c a).metropolisChoice w hw a).law b : ℝ) =
      Replica.metropolis P (fun x => (w x:ℝ)) a b := by
  have hpos : ∀ x, (0:ℝ)<w x := fun x => by exact_mod_cast hw x
  have hsum := real_law_sum ((c a).metropolisChoice w hw a)
  have he := row_eq_of_off _ _ hsum (Replica.metropolis_row P _ hpos a) a (fun b hab => ?_)
  · exact congrFun he b
  rw [metropolisChoice,accept_law,ite_eq_right hab,add_zero]
  push_cast
  rw [hc,min_ratio _ _ (hpos a)]
  simp only [Replica.metropolis,Replica.metropolisCapacity,ite_eq_right hab,Replica.offCapacity]
  ring

omit [Fintype Ω] [DecidableEq Ω] in
lemma metropolisChoice_size (c : WeightedOptions Ω) (w : Ω → ℚ) (hw : ∀ a, 0 < w a) (a : Ω) :
    (c.metropolisChoice w hw a).size = 2*c.size := by
  simp only [metropolisChoice,accept]
  omega

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype B] in
lemma imageLaw_eq_count (f : A → B) (b : B) :
    imageLaw f b=((univ.filter (fun a=>f a=b)).card:ℝ)/Fintype.card A := by
  simp only [imageLaw,push,uniform]
  rw [show (∑ x,if f x=b then (1:ℝ)/Fintype.card A else 0)=
    (∑ x,if f x=b then (1:ℝ) else 0)/Fintype.card A by
      simp only [sum_div,ite_div,zero_div]]
  simp

lemma imageLaw_equiv (e : A ≃ B) : imageLaw e=uniform B := by
  funext b
  unfold imageLaw push uniform
  rw [e.sum_comp (fun x=>if x=b then (1:ℝ)/Fintype.card A else 0)]
  simp [Fintype.card_congr e]

omit [Fintype C] in
lemma imageLaw_comp_equiv (e : A ≃ B) (f : B → C) : imageLaw (f ∘ e)=imageLaw f := by
  funext c
  unfold imageLaw push uniform
  rw [Fintype.card_congr e,←e.sum_comp (fun b=>if f b=c then (1:ℝ)/Fintype.card B else 0)]
  rfl

omit [Fintype C] in
lemma push_comp (p : A → ℝ) (f : A → B) (g : B → C) :
    push (push p f) g=push p (g ∘ f) := by
  funext c
  unfold push
  have h (b : B) : (if g b=c then ∑ a,if f a=b then p a else 0 else 0)=
      ∑ a,if g b=c then (if f a=b then p a else 0) else 0 := by
    by_cases hh : g b=c <;> simp [hh]
  simp_rw [h]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [←ite_and]
  rw [show (fun b=>if g b=c ∧ f a=b then p a else 0)=
    (fun b=>if f a=b then (if g b=c then p a else 0) else 0) by
      funext b; split_ifs <;> simp_all]
  simp

omit [Fintype C] in
lemma imageLaw_comp (f : A → B) (g : B → C) : imageLaw (g ∘ f)=push (imageLaw f) g :=
  (push_comp _ _ _).symm

lemma uniform_prod (a : A×B) : uniform (A×B) a=uniform A a.1*uniform B a.2 := by
  simp [uniform,Fintype.card_prod,Nat.cast_mul,mul_comm]

variable {D : Type*} [Fintype D]

omit [Fintype C] in
lemma imageLaw_pair (f : A → B → C) :
    imageLaw (fun x : A×B=>f x.1 x.2)=bind (uniform A) (fun a=>imageLaw (f a)) := by
  funext c
  simp only [imageLaw,push,bind,Fintype.sum_prod_type,uniform_prod,mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro b _
  split_ifs <;> simp

omit [Fintype C] in
lemma bind_push (p : A → ℝ) (f : A → B) (k : B → C → ℝ) :
    bind (push p f) k=bind p (fun a=>k (f a)) := by
  funext c
  simp only [bind,push,sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp

omit [Fintype C] in
lemma imageLaw_adaptive_pair (d : A → D) (f : D → B → C) :
    imageLaw (fun x : A×B=>f (d x.1) x.2)=bind (imageLaw d) (fun a=>imageLaw (f a)) := by
  rw [imageLaw_pair (fun a b=>f (d a) b), imageLaw,bind_push]

theorem uniform_sigma [Nonempty A] {E : B → Type*} [∀ b,Fintype (E b)]
    (e : (Σ b,E b) ≃ A) (z : A) :
    push (sigmaLift (fun b=>(Fintype.card (E b):ℝ)/Fintype.card A)
      (fun b=>uniform (E b))) e z=uniform A z := by
  have h (s : Sigma E) : sigmaLift (fun b=>(Fintype.card (E b):ℝ)/Fintype.card A)
      (fun b=>uniform (E b)) s=uniform (Sigma E) s := by
    have hn : (Fintype.card (E s.1):ℝ)≠0 := by
      let : Nonempty (E s.1) := ⟨s.2⟩
      exact_mod_cast Fintype.card_ne_zero
    simp only [sigmaLift,uniform,Fintype.card_congr e]
    field_simp
  have hh := congrArg (fun p=>push p e z) (funext h)
  rw [hh]
  exact congrFun (imageLaw_equiv e) z

open Finset
open scoped Classical

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype C] in
lemma imageLaw_ignore [Nonempty A] (f : B → C) :
    imageLaw (fun x : A×B=>f x.2)=imageLaw f := by
  rw [imageLaw_pair (fun _ b=>f b)]
  funext c
  simp only [bind,←sum_mul,uniform_sum,one_mul]

omit [Fintype B] in
lemma push_sigmaLift {E : A → Type*} [∀ a,Fintype (E a)]
    (p : A → ℝ) (k : ∀ a,E a → ℝ) (f : (Σ a,E a) → B) :
    push (sigmaLift p k) f=bind p (fun a=>push (k a) (fun e=>f ⟨a,e⟩)) := by
  funext b
  simp only [push,sigmaLift,bind,Fintype.sum_sigma,mul_sum]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro e _
  split_ifs <;> simp

lemma imageLaw_subsingleton [Nonempty A] [Subsingleton B] (f : A → B) :
    imageLaw f=uniform B := by
  let : Nonempty B := ⟨f (Classical.choice (inferInstance : Nonempty A))⟩
  funext b
  simp only [imageLaw,push,Subsingleton.elim (f _) b,ite_true,uniform_sum]
  let : Unique B := ⟨⟨b⟩,fun x=>Subsingleton.elim x b⟩
  simp [uniform]

lemma tv_self (p : A → ℝ) : tv p p=0 := by simp [tv]

open scoped Classical

lemma imageLaw_fin_skip {B C D : Type*} [Fintype B] [Nonempty B] [Fintype C] [Fintype D]
    (n : ℕ) (g : (Fin (n+2) → B) → C) (d : B → D) (f : D → (Fin n → B) → C)
    (hg : ∀ bits,g bits=f (d (bits (Fin.last (n+1)))) (fun i=>bits i.castSucc.castSucc)) :
    imageLaw g=bind (imageLaw d) (fun c=>imageLaw (f c)) := by
  let e : (B×(B×(Fin n → B))) ≃ (Fin (n+2) → B) :=
    (Equiv.prodCongr (Equiv.refl B) (Fin.snocEquiv (fun _ : Fin (n+1)=>B))).trans
      (Fin.snocEquiv (fun _ : Fin (n+2)=>B))
  have hE : g ∘ e=(fun x : B×(B×(Fin n→B))=>f (d x.1) x.2.2) := by
    funext x
    rw [Function.comp_apply,hg]
    simp [e,Fin.snocEquiv]

  rw [←imageLaw_comp_equiv e,hE,imageLaw_adaptive_pair d (fun c (u : B×(Fin n→B))=>f c u.2)]
  simp_rw [imageLaw_ignore]

end MatchingFPRAS.Variation

namespace MatchingFPRAS.WeightedOptions

open Finset Variation FiniteChoice

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] [DecidableEq Ω] in
lemma chooseBits_imageLaw (c : WeightedOptions Ω) (k : ℕ) :
    imageLaw (chooseBits c.mass c.total k) = fun i => (tapeLaw c.mass c.total k i:ℝ) := by
  funext i
  rw [imageLaw_eq_count]
  simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,
    Nat.cast_ofNat,tapeLaw,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat]
  congr 2
  congr 1
  ext bits
  simp only [mem_filter,mem_univ,true_and]

omit [Fintype Ω] in
lemma realLaw_push (c : WeightedOptions Ω) :
    (fun b => (c.law b:ℝ))=push (fun i=>(c.mass i:ℝ)) c.out := by
  funext b
  unfold law push
  simp only [Rat.cast_sum,apply_ite,Rat.cast_zero]

theorem draw_tv (c : WeightedOptions Ω) (k : ℕ) :
    tv (imageLaw (c.draw k)) (fun b=>(c.law b:ℝ)) ≤ 2*c.size/(2:ℝ)^k := by
  have h := fixed_bit_choice c.mass c.nonneg c.total k
  rw [←tapeLaw_eq] at h
  have hr : tv (fun i=>(tapeLaw c.mass c.total k i:ℝ)) (fun i=>(c.mass i:ℝ))
      ≤ 2*c.size/(2:ℝ)^k := by
    change (∑ i : Fin c.size, |(tapeLaw c.mass c.total k i:ℝ)-(c.mass i:ℝ)|)/2 ≤ _
    have hh := (Rat.cast_le (K := ℝ)).mpr h
    simpa only [Rat.cast_div,Rat.cast_sum,Rat.cast_abs,Rat.cast_sub,Rat.cast_mul,
      Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_pow] using hh
  have hd : c.draw k = c.out ∘ chooseBits c.mass c.total k := rfl
  rw [hd,imageLaw_comp,realLaw_push,chooseBits_imageLaw]
  exact (push_contraction _ _ _).trans hr

end MatchingFPRAS.WeightedOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_PairStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Replica

open Finset

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable (p : I → Ω → ℝ)

omit [Fintype I] [Fintype Ω] [DecidableEq Ω] in
lemma replacePair_at (x y : I) (hxy : x≠y) (s : I → Ω) (a : Ω×Ω) :
    ((replacePair x y s a) x,(replacePair x y s a) y)=a := by
  simp [replacePair,hxy]

omit [Fintype I] [Fintype Ω] [DecidableEq Ω] in
lemma replacePair_idem (x y : I) (s : I → Ω) (a b : Ω×Ω) :
    replacePair x y (replacePair x y s a) b = replacePair x y s b := by
  funext i
  by_cases hy : i=y
  · subst i; simp [replacePair]
  · by_cases hx : i=x
    · subst i; simp [replacePair,hy]
    · simp [replacePair,hx,hy]

lemma local_pairFlow (hp : ∀ i a, 0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (x y : I) (hxy : x≠y) (Q : PairCapacity p x y) (s t : I → Ω) :
    pairFlow p x y Q s t = density p s*pairStep p x y Q s t := by
  let f : (I → Ω) → ℝ := fun r => if r=s then pairStep p x y Q r t else 0
  have hf := slice_mean p hs x y f
  have hmean : mean p f=density p s*pairStep p x y Q s t := by
    simp only [mean,f,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true]
  rw [hmean] at hf
  rw [←hf]
  unfold pairFlow pushedFlow mean
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro r _
  rw [Fintype.sum_prod_type,mul_sum]
  apply sum_congr rfl
  intro a _
  have hpa : ((replacePair x y r a) x,(replacePair x y r a) y)=a := replacePair_at x y hxy r a
  rcases a with ⟨ax,ay⟩
  have hx : (replacePair x y r (ax,ay)) x=ax := congrArg Prod.fst hpa
  have hy : (replacePair x y r (ax,ay)) y=ay := congrArg Prod.snd hpa
  by_cases ha : replacePair x y r (ax,ay)=s
  · simp only [f,ha,ite_true]
    rw [←ha]
    simp only [pairStep,hx,hy,replacePair_idem,mul_sum]
    apply sum_congr rfl
    intro b _
    by_cases hb : replacePair x y r b=t
    · simp only [ha,hb,ite_true]
      field_simp [ne_of_gt (hp x ax),ne_of_gt (hp y ay)]
    · simp only [Prod.mk.injEq,ha,hb,true_and,ite_false,mul_zero]
  · simp only [f,ite_eq_right ha,mul_zero]
    apply sum_eq_zero
    intro b _
    simp only [Prod.mk.injEq,ha,false_and,ite_false]

lemma local_baseFlow (_hp : ∀ i a,0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (i : I) (s t : I → Ω) : baseFlow p i s t=density p s*baseStep p i s t := by
  let f : (I → Ω) → ℝ := fun r => if r=s then baseStep p i r t else 0
  have hf := mean_average p hs i f
  have hmean : mean p f=density p s*baseStep p i s t := by
    simp only [mean,f,mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true]
  rw [hmean] at hf
  rw [←hf]
  unfold baseFlow pushedFlow mean
  rw [Fintype.sum_prod_type]
  simp only [average_apply]
  apply sum_congr rfl
  intro r _
  rw [Fintype.sum_prod_type,mul_sum]
  apply sum_congr rfl
  intro a _
  by_cases ha : Function.update r i a=s
  · simp only [f,ite_eq_left ha]
    rw [←ha]
    simp only [baseStep,Function.update_idem,mul_sum]
    apply sum_congr rfl
    intro b _
    by_cases hb : Function.update r i b=t
    · simp only [ha,hb,ite_true]
    · simp only [Prod.mk.injEq,ha,hb,true_and,ite_false,mul_zero]
  · simp only [f,ite_eq_right ha,mul_zero]
    apply sum_eq_zero
    intro b _
    simp only [Prod.mk.injEq,ha,false_and,ite_false]

theorem localScan_kernel (hp : ∀ i a,0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (guides : I → Finset I) (hself : ∀ x y,y∈guides x → x≠y) (base : Finset I)
    (Q : ∀ x y,PairCapacity p x y) (s t : I → Ω) :
    localScan p guides base Q s t=FiniteChain.kernel (density p) (scanFlow p guides base Q) s t := by
  have hpos : 0<density p s := prod_pos fun i _=>hp i (s i)
  have hpair : (∑ x,∑ y ∈ guides x,pairFlow p x y (Q x y) s t)=
      density p s*(∑ x,∑ y ∈ guides x,pairStep p x y (Q x y) s t) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro y hy
    exact local_pairFlow p hp hs x y (hself x y hy) (Q x y) s t
  have hbase : (∑ i ∈ base,baseFlow p i s t)=density p s*(∑ i ∈ base,baseStep p i s t) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro i hi
    exact local_baseFlow p hp hs i s t
  unfold FiniteChain.kernel scanFlow localScan
  rw [hpair,hbase]
  have hn := ne_of_gt hpos
  by_cases hst : s=t
  · subst t
    simp only [ite_true]
    field_simp [hn]
  · simp only [ite_eq_right hst,zero_div]
    field_simp [hn]
    ring

end MatchingFPRAS.Replica

namespace MatchingFPRAS.WeightedOptions

open Finset Variation

variable {J Ω B : Type*} [Fintype J] [DecidableEq J] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B]

omit [DecidableEq J] [Fintype Ω] [DecidableEq Ω] [Nonempty B] in
lemma drawThen_law [DecidableEq J] [Fintype Ω] [DecidableEq Ω] [Nonempty B]
    (c : WeightedOptions J) (g : J → B → Ω) (k : ℕ) :
    imageLaw (c.drawThen g k)=bind (imageLaw (c.draw k)) (fun j=>imageLaw (g j)) :=
  imageLaw_adaptive_pair (c.draw k) g

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Replica

open Finset Variation

variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

lemma updates_card (guides : I → Finset I) (base : Finset I) :
    (updates guides base).card=updateCount guides base := by
  simp only [updates,card_disjSum,updateCount]
  congr 1
  rw [card_eq_sum_ones,sum_filter,Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x _
  simp

variable (p : I → Ω → ℝ)

variable [LinearOrder (Update I)]

lemma scanChoice_size (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty) :
    (scanChoice guides base hb).size=1+updateCount guides base := by
  simp only [scanChoice,WeightedOptions.mix,WeightedOptions.map,WeightedOptions.pure,
    WeightedOptions.uniform,updates_card]

lemma scanChoice_law (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty)
    (Q : ∀ x y,PairCapacity p x y) (s t : I → Ω) :
    bind (fun u=>((scanChoice guides base hb).law u:ℝ)) (updateKernel p Q s) t=
      localScan p guides base Q s t := by
  unfold Variation.bind
  rw [Fintype.sum_option]
  simp only [scanChoice,WeightedOptions.mix_law,WeightedOptions.pure_law,
    WeightedOptions.map_law]
  simp only [Option.some.injEq,reduceCtorEq,ite_false,sum_const_zero,mul_zero,zero_add]
  simp only [sum_ite_eq',mem_univ,ite_true,WeightedOptions.uniform_law]
  push_cast
  rw [updates_card]
  simp only [updateKernel,Fintype.sum_sum_type,Fintype.sum_prod_type,updates,
    inl_mem_disjSum,inr_mem_disjSum,
    mem_filter,mem_univ,true_and]
  unfold localScan
  simp only [apply_ite,Rat.cast_inv,Rat.cast_natCast,Rat.cast_zero,
    ite_mul,zero_mul,mul_zero,sum_ite_mem,univ_inter]
  simp only [←mul_sum]
  by_cases h : s=t <;> simp only [h,ite_true,ite_false] <;> ring



open Finset Variation

end MatchingFPRAS.Replica

namespace MatchingFPRAS.Variation

open Finset

variable {Ω B : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype B] [Nonempty B]

omit [DecidableEq Ω] [Nonempty B] in
lemma runSample_law [DecidableEq Ω] [Nonempty B] (g : Ω → B → Ω) (z : Ω) (n : ℕ) :
    imageLaw (runSample g z (n+1))=bind (imageLaw (runSample g z n)) (fun s=>imageLaw (g s)) := by
  let e : ((Fin n → B) × B) ≃ (Fin (n+1) → B) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _=>B))
  have h : runSample g z (n+1) ∘ e=(fun u=>g (runSample g z n u.1) u.2) := by
    funext u
    change g (runSample g z n (Fin.init (Fin.snoc (α:=fun _ : Fin (n+1)=>B) u.1 u.2)))
      (Fin.snoc (α:=fun _ : Fin (n+1)=>B) u.1 u.2 (Fin.last n))=_
    simp only [Fin.init_snoc,Fin.snoc_last]
  rw [←imageLaw_comp_equiv e,h]
  exact imageLaw_adaptive_pair (runSample g z n) g

theorem runSample_walk_tv (π : Ω → ℝ) (C : Ω → Ω → ℝ)
    (hn : ∀ s t,0≤FiniteChain.kernel π C s t) (hs : ∀ s,∑ t,FiniteChain.kernel π C s t=1)
    (g : Ω → B → Ω) (d : ℝ)
    (hd : ∀ s,tv (imageLaw (g s)) (FiniteChain.kernel π C s)≤d) (z : Ω) (n : ℕ) :
    tv (imageLaw (runSample g z n)) (FiniteChain.walk π C z n)≤n*d := by
  induction n with
  | zero =>
    have h : imageLaw (runSample g z 0)=FiniteChain.walk π C z 0 := by
      funext b
      by_cases hb : b=z
      · subst b; simp [imageLaw,push,uniform,runSample,FiniteChain.walk]
      · simp [imageLaw,push,runSample,FiniteChain.walk,hb,Ne.symm hb]
    rw [h,tv_self]
    simp
  | succ n ih =>
    rw [runSample_law]
    change tv (bind _ _) (bind _ _)≤_
    calc
      _ ≤ tv (bind (imageLaw (runSample g z n)) (fun s=>imageLaw (g s)))
          (bind (imageLaw (runSample g z n)) (FiniteChain.kernel π C))+
          tv (bind (imageLaw (runSample g z n)) (FiniteChain.kernel π C))
            (bind (FiniteChain.walk π C z n) (FiniteChain.kernel π C)) := tv_triangle _ _ _
      _ ≤ d+n*d := add_le_add
        (bind_perturbation _ _ _ (imageLaw_nonneg _) (imageLaw_sum _) d hd)
        ((bind_contraction _ _ _ hn hs).trans ih)
      _ = _ := by push_cast; ring

end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Admissible
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset

variable {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]

lemma bind_perturbation_on (p : Ω → ℝ) (k l : Ω → Ψ → ℝ)
    (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1) (ε : ℝ)
    (he : ∀ x,p x≠0 → tv (k x) (l x) ≤ ε) :
    tv (bind p k) (bind p l) ≤ ε := by
  unfold tv bind
  have h : ∑ y,|∑ x,p x*k x y-∑ x,p x*l x y| ≤ 2*ε := by
    calc
      _ = ∑ y,|∑ x,p x*(k x y-l x y)| := by simp only [mul_sub,sum_sub_distrib]
      _ ≤ ∑ y,∑ x,|p x*(k x y-l x y)| := sum_le_sum (fun y _ => abs_sum_le_sum_abs _ _)
      _ = ∑ x,p x*(∑ y,|k x y-l x y|) := by
        rw [sum_comm]; simp_rw [abs_mul,abs_of_nonneg (hp _),←mul_sum]
      _ ≤ ∑ x,p x*(2*ε) := by
        apply sum_le_sum
        intro x _
        by_cases hx : p x=0
        · simp [hx]
        · apply mul_le_mul_of_nonneg_left _ (hp x)
          have hh:=he x hx
          unfold tv at hh
          linarith
      _ = _ := by rw [←sum_mul,hs,one_mul]
  linarith

end MatchingFPRAS.Variation

namespace MatchingFPRAS.WeightedOptions

open Finset Variation

variable {J Ω B : Type*} [Fintype J] [DecidableEq J] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B]

theorem drawThen_tv_on (c : WeightedOptions J) (g : J → B → Ω) (k : ℕ)
    (P : J → Ω → ℝ) (e : ℝ) (he : ∀ j,c.law j≠0 → tv (imageLaw (g j)) (P j)≤e) :
    tv (imageLaw (c.drawThen g k)) (bind (fun j=>(c.law j:ℝ)) P)≤
      2*c.size/(2:ℝ)^k+e := by
  rw [drawThen_law]
  calc
    _ ≤ tv (bind (imageLaw (c.draw k)) (fun j=>imageLaw (g j)))
        (bind (fun j=>(c.law j:ℝ)) (fun j=>imageLaw (g j)))+
        tv (bind (fun j=>(c.law j:ℝ)) (fun j=>imageLaw (g j)))
          (bind (fun j=>(c.law j:ℝ)) P) := tv_triangle _ _ _
    _ ≤ 2*c.size/(2:ℝ)^k+e := add_le_add
      ((bind_contraction _ _ _ (fun _=>imageLaw_nonneg _) (fun _=>imageLaw_sum _)).trans (c.draw_tv k))
      (bind_perturbation_on _ _ _ (fun j=>by exact_mod_cast c.law_nonneg j)
        (c.real_law_sum) e (fun j hj=>he j (by exact_mod_cast hj)))

end MatchingFPRAS.WeightedOptions

namespace MatchingFPRAS.Replica

open Finset Variation

variable {I Ω B : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

variable [Fintype B] [Nonempty B] [LinearOrder (Update I)]

lemma scanChoice_support (guides : I → Finset I) (base : Finset I) (hb : base.Nonempty)
    (u : Option (Update I)) (hu : (scanChoice guides base hb).law u≠0) :
    admissible guides base u := by
  cases u with
  | none => trivial
  | some u =>
    by_contra h
    apply hu
    simp only [scanChoice,WeightedOptions.mix_law,WeightedOptions.pure_law,
      WeightedOptions.map_law]
    simp only [reduceCtorEq,ite_false,Option.some.injEq,sum_ite_eq',mem_univ,ite_true]
    rw [WeightedOptions.uniform_law]
    have hn : u∉updates guides base := by
      cases u <;> simpa [updates,admissible] using h
    simp [hn]

omit [LinearOrder (Update I)] in
lemma localSampler_tv_on [LinearOrder (Update I)] (p : I → Ω → ℝ) (Q : ∀ x y,PairCapacity p x y)
    (guides : I → Finset I) (base : Finset I)
    (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω) (e : ℝ) (he : 0≤e)
    (hp : ∀ x y,y∈guides x → ∀ a,tv (imageLaw (pair x y a))
      (fun b=>(Q x y).q a b/(p x a.1*p y a.2))≤e)
    (hr : ∀ i,i∈base → tv (imageLaw (refresh i)) (p i)≤e)
    (s : I → Ω) (u : Option (Update I)) (hu : admissible guides base u) :
    tv (imageLaw (localSampler pair refresh s u)) (updateKernel p Q s u)≤e := by
  cases u with
  | none =>
    have h : imageLaw (localSampler pair refresh s none)=updateKernel p Q s none := by
      funext t
      simp only [imageLaw,push,localSampler,updateKernel]
      by_cases hst : s=t
      · subst t
        simpa using uniform_sum (A:=B)
      · simp [hst]
    rw [h,tv_self]
    exact he
  | some u => cases u with
    | inl ij =>
      have hk : updateKernel p Q s (some (.inl ij))=
          push (fun b=>(Q ij.1 ij.2).q (s ij.1,s ij.2) b/(p ij.1 (s ij.1)*p ij.2 (s ij.2)))
            (replacePair ij.1 ij.2 s) := by
        funext t
        simp only [updateKernel,pairStep,push]
      rw [hk]
      change tv (imageLaw ((replacePair ij.1 ij.2 s) ∘ pair ij.1 ij.2 (s ij.1,s ij.2)))
        (push (fun b=>(Q ij.1 ij.2).q (s ij.1,s ij.2) b/(p ij.1 (s ij.1)*p ij.2 (s ij.2)))
          (replacePair ij.1 ij.2 s))≤e
      rw [imageLaw_comp]
      exact (push_contraction _ _ _).trans (hp _ _ hu _)
    | inr i =>
      have hk : updateKernel p Q s (some (.inr i))=push (p i) (Function.update s i) := by
        funext t
        simp only [updateKernel,baseStep,push]
        apply sum_congr rfl
        intro a _
        congr 1
      rw [hk]
      change tv (imageLaw ((Function.update s i) ∘ refresh i)) (push (p i) (Function.update s i))≤e
      rw [imageLaw_comp]
      exact (push_contraction _ _ _).trans (hr i hu)

theorem sampleScan_tv_on (p : I → Ω → ℝ) (hp : ∀ i a,0<p i a) (hs : ∀ i,∑ a,p i a=1)
    (guides : I → Finset I) (hself : ∀ x y,y∈guides x → x≠y)
    (base : Finset I) (hb : base.Nonempty) (Q : ∀ x y,PairCapacity p x y)
    (pair : I → I → (Ω×Ω) → B → Ω×Ω) (refresh : I → B → Ω) (e : ℝ) (he : 0≤e)
    (hpr : ∀ x y,y∈guides x → ∀ a,tv (imageLaw (pair x y a))
      (fun b=>(Q x y).q a b/(p x a.1*p y a.2))≤e)
    (hr : ∀ i,i∈base → tv (imageLaw (refresh i)) (p i)≤e) (k : ℕ) (s : I → Ω) :
    tv (imageLaw (sampleScan guides base hb pair refresh k s))
      (FiniteChain.kernel (density p) (scanFlow p guides base Q) s)≤
      2*(1+updateCount guides base)/(2:ℝ)^k+e := by
  have ht := WeightedOptions.drawThen_tv_on (scanChoice guides base hb) (localSampler pair refresh s)
    k (updateKernel p Q s) e (fun u hu=>
      localSampler_tv_on p Q guides base pair refresh e he hpr hr s u (scanChoice_support guides base hb u hu))
  have hl : Variation.bind (fun u=>((scanChoice guides base hb).law u:ℝ)) (updateKernel p Q s)=
      FiniteChain.kernel (density p) (scanFlow p guides base Q) s := by
    funext t
    rw [scanChoice_law,localScan_kernel p hp hs guides hself base Q]
  rw [hl,scanChoice_size] at ht
  simpa only [Nat.cast_add,Nat.cast_one,sampleScan] using ht



open Finset

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma metropolis_normalize (P : SymmetricProposal Ω) (u : Ω → ℝ) (hu : ∀ a,0<u a)
    (c : ℝ) (hc : 0 < c) (a b : Ω) :
    metropolis P (fun x=>u x/c) a b=metropolis P u a b := by
  have huc : ∀ x,0<u x/c:=fun x=>div_pos (hu x) hc
  have hf := WeightedOptions.row_eq_of_off _ _ (metropolis_row P _ huc a)
    (metropolis_row P _ hu a) a (fun b hab=>?_)
  · exact congrFun hf b
  rw [metropolis_acceptance _ _ huc _ _ hab,metropolis_acceptance _ _ hu _ _ hab]
  congr 2
  field_simp

end MatchingFPRAS.Replica

namespace MatchingFPRAS.Transport.Sparse

open Finset Replica Variation

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [LinearOrder E]

variable (ends : E → Sym2 V)

attribute [local instance] finsetOrder pmOrder

omit [DecidableEq V] [Fintype E] [LinearOrder E] in
lemma rationalWeight_cast [DecidableEq V] [Fintype E] [LinearOrder E]
    (w : E → ℚ) (A : PM (fun e v=>v∈ends e)) :
    (rationalWeight ends w A:ℝ)=matchingWeight (fun e=>(w e:ℝ)) A := by
  simp [rationalWeight,matchingWeight]

theorem pairStepTable_law (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E → ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a b : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) :
    ((pairStepTable ends hloop hpar w z hw hz a).law b:ℝ)=
      metropolis (pairProposal ends hloop hpar) (pairLaw ends (fun e=>(w e:ℝ)) (fun e=>(z e:ℝ))) a b := by
  rw [pairStepTable,WeightedOptions.metropolisChoice_law (pairProposal ends hloop hpar)
    (pairTable ends hloop hpar) (pairTable_law ends hloop hpar)]
  have hw' : ∀ e,(0:ℝ)<w e:=fun e=>by exact_mod_cast hw e
  have hz' : ∀ e,(0:ℝ)<z e:=fun e=>by exact_mod_cast hz e
  let c:=partition (inc:=fun e v=>v∈ends e) (fun e=>(w e:ℝ))*
    partition (inc:=fun e v=>v∈ends e) (fun e=>(z e:ℝ))
  have hc : 0 < c:=mul_pos (partition_pos _ hw' a.1) (partition_pos _ hz' a.2)
  have he : pairLaw ends (fun e=>(w e:ℝ)) (fun e=>(z e:ℝ))=
      (fun x=>(rationalPairWeight ends w z x:ℝ)/c) := by
    funext x
    simp only [pairLaw,gibbs,rationalPairWeight,Rat.cast_mul,rationalWeight_cast,c]
    exact div_mul_div_comm _ _ _ _
  rw [he,metropolis_normalize _ _ (fun x=>by exact_mod_cast rationalPairWeight_pos ends w z hw hz x) c hc]

theorem pairStepTable_tv (hloop : ∀ e,¬(ends e).IsDiag)
    (hpar : ∀ e,(univ.filter (fun f=>ends f=ends e)).card≤2)
    (w z : E → ℚ) (hw : ∀ e,0<w e) (hz : ∀ e,0<z e)
    (a : PM (fun e v=>v∈ends e) × PM (fun e v=>v∈ends e)) (k : ℕ) :
    tv (imageLaw ((pairStepTable ends hloop hpar w z hw hz a).draw k))
      (metropolis (pairProposal ends hloop hpar) (pairLaw ends (fun e=>(w e:ℝ)) (fun e=>(z e:ℝ))) a) ≤
      4*(8*a.1.val.card.choose 2+2*a.1.val.card+(a.1.val.card+a.2.val.card)+3)/(2:ℝ)^k := by
  have ht := (pairStepTable ends hloop hpar w z hw hz a).draw_tv k
  have hl : (fun b=>((pairStepTable ends hloop hpar w z hw hz a).law b:ℝ))=
      metropolis (pairProposal ends hloop hpar) (pairLaw ends (fun e=>(w e:ℝ)) (fun e=>(z e:ℝ))) a :=
    funext (pairStepTable_law ends hloop hpar w z hw hz a)
  rw [hl] at ht
  apply ht.trans
  rw [pairStepTable,WeightedOptions.metropolisChoice_size]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hs := pairTable_size ends hloop hpar a
  have hs' : ((pairTable ends hloop hpar a).size:ℝ)≤
      8*a.1.val.card.choose 2+2*a.1.val.card+(a.1.val.card+a.2.val.card)+3 := by exact_mod_cast hs
  push_cast
  nlinarith

end MatchingFPRAS.Transport.Sparse

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Plan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]



open Finset MatchingFPRAS.FiniteChoice

variable {n m : ℕ}

lemma edgeProbability_nonneg (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) (i : Fin (n*m)) :
    0≤edgeProbability bags rank parent a i := by unfold edgeProbability; positivity

theorem drawEdge_tv (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin n) (hz : 0 < count bags parent (plan rank)) (k : ℕ) :
    let p := edgeProbability bags rank parent a
    let hs := edgeProbability_sum bags rank parent hb hne hp a hz
    (∑ i,|tapeLaw p hs k i-p i|)/2≤2*(n*m)/(2:ℚ)^k := by
  dsimp only
  rw [tapeLaw_eq]
  simpa only [Nat.cast_mul] using fixed_bit_choice _ (edgeProbability_nonneg bags rank parent a) _ k

end MatchingFPRAS.UnitRefresh.Materialized

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset MatchingFPRAS.FiniteChoice

variable {m : ℕ}



open Finset MatchingFPRAS.FiniteChoice MatchingFPRAS.Variation
open scoped Classical

variable {n m : ℕ}

lemma partnerIndex_injective (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) :
    Function.Injective (partnerIndex bags rank parent a) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  exact finProdFinEquiv.injective h

lemma drawEdge_index (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin n) (hz : 0 < count bags parent (plan rank)) (k : ℕ) (bits : Fin k → Bool) :
    partnerIndex bags rank parent a (drawEdge bags rank parent hb hne hp a hz k bits)=
      chooseBits (edgeProbability bags rank parent a) (edgeProbability_sum bags rank parent hb hne hp a hz) k bits := by
  exact finProdFinEquiv.apply_symm_apply _

lemma drawEdge_law (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin n) (hz : 0 < count bags parent (plan rank)) (k : ℕ)
    (c : PositivePartner bags rank parent a) :
    imageLaw (drawEdge bags rank parent hb hne hp a hz k) c=
      (tapeLaw (edgeProbability bags rank parent a) (edgeProbability_sum bags rank parent hb hne hp a hz) k
        (partnerIndex bags rank parent a c):ℝ) := by
  rw [imageLaw_eq_count]
  simp only [tapeLaw,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,
    Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat]
  congr 2
  apply congrArg Finset.card
  ext bits
  simp only [mem_filter,mem_univ,true_and]
  rw [←drawEdge_index]
  exact (partnerIndex_injective bags rank parent a).eq_iff.symm

theorem drawEdge_positive_tv (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin n) (hz : 0 < count bags parent (plan rank)) (k : ℕ) :
    tv (imageLaw (drawEdge bags rank parent hb hne hp a hz k))
      (fun c : PositivePartner bags rank parent a=>(branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank))
      ≤ 2*n*m/(2:ℝ)^k := by
  let idx := partnerIndex bags rank parent a
  let p := edgeProbability bags rank parent a
  let hs := edgeProbability_sum bags rank parent hb hne hp a hz
  have he (c : PositivePartner bags rank parent a) :
      (p (idx c):ℝ)=(branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank) := by
    have hv : validBranch bags a c.val.val := c.val.property
    simp [p,idx,partnerIndex,edgeProbability,edgeCount,hv]
  have hg : ∑ c : PositivePartner bags rank parent a,|(tapeLaw p hs k (idx c):ℝ)-(p (idx c):ℝ)| ≤
      ∑ i : Fin (n*m),|(tapeLaw p hs k i:ℝ)-(p i:ℝ)| := by
    change (∑ c,|(tapeLaw p hs k (partnerIndex bags rank parent a c):ℝ)-(p (partnerIndex bags rank parent a c):ℝ)|)≤_
    rw [←Finset.sum_image (s:=univ) (f:=fun i=>|(tapeLaw p hs k i:ℝ)-(p i:ℝ)|)
      (fun c _ d _ h=>(partnerIndex_injective bags rank parent a) h)]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _=>abs_nonneg _)
  have ht : (∑ i : Fin (n*m),|(tapeLaw p hs k i:ℝ)-(p i:ℝ)|)/2 ≤ 2*(n*m)/(2:ℝ)^k := by
    have hh := drawEdge_tv bags rank parent hb hne hp a hz k
    have hcast := (Rat.cast_le (K:=ℝ)).mpr hh
    push_cast at hcast
    simpa only [p,hs,Nat.cast_mul] using hcast
  unfold tv
  have hg' : (∑ c : PositivePartner bags rank parent a,
      |imageLaw (drawEdge bags rank parent hb hne hp a hz k) c-
        (branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank)|)≤
      ∑ i : Fin (n*m),|(tapeLaw p hs k i:ℝ)-(p i:ℝ)| := by
    simpa only [drawEdge_law,he] using hg
  exact (div_le_div_of_nonneg_right hg' (by norm_num)).trans (by simpa only [mul_assoc] using ht)

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RemainingBags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset MatchingFPRAS.FiniteChoice MatchingFPRAS.Variation
open scoped Classical

variable {n m : ℕ}

lemma sampleUnit_step (k : ℕ) (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (hz : 0 < count bags parent (plan rank)) (bits : Fin (n+2) → Fin k → Bool) :
    sampleUnit k (n+2) bags rank parent hb hne hp hz bits=
      residualSampler k bags rank parent hb hne hp (Fin.last (n+1))
        (drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k (bits (Fin.last (n+1))))
        (fun i=>bits i.castSucc.castSucc) := rfl

lemma renumberedSplitEquiv_apply (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin (n+2)) (s : Σ c : PositivePartner bags rank parent a,ColoredPairing (remainingBags bags a c.val)) :
    renumberedSplitEquiv bags rank parent hb hne hp a s=assembleEdge bags a s.1.val s.2 := rfl

lemma sampleUnit_step_law (k : ℕ) (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (hz : 0 < count bags parent (plan rank)) :
    imageLaw (sampleUnit k (n+2) bags rank parent hb hne hp hz)=
      bind (imageLaw (drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k))
        (fun c=>imageLaw (residualSampler k bags rank parent hb hne hp (Fin.last (n+1)) c)) := by
  exact imageLaw_fin_skip n _ _ _ (sampleUnit_step k bags rank parent hb hne hp hz)

lemma exact_unit_step (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin (n+2)) (hz : 0 < count bags parent (plan rank)) :
    bind (fun c : PositivePartner bags rank parent a=>
      (branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank))
      (fun c : PositivePartner bags rank parent a=>
        push (uniform (ColoredPairing (remainingBags bags a c.val))) (assembleEdge bags a c.val))=
      uniform (ColoredPairing bags) := by
  let : Nonempty (ColoredPairing bags) := Fintype.card_pos_iff.mp (by
    rwa [←computable_count_eq bags rank parent hb hne hp])
  have h := funext (uniform_sigma (renumberedSplitEquiv bags rank parent hb hne hp a))
  rw [push_sigmaLift] at h
  simpa only [remainingCard bags rank parent hb hne hp,←computable_count_eq bags rank parent hb hne hp,
    renumberedSplitEquiv_apply] using h

open Finset MatchingFPRAS.Variation
open scoped Classical

variable {m n : ℕ}

lemma residualSampler_law (k : ℕ) (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (a : Fin (n+2)) (c : PositivePartner bags rank parent a) :
    imageLaw (residualSampler k bags rank parent hb hne hp a c)=
      push (imageLaw (sampleUnit k n (remainingBags bags a c.val) rank parent
        (remainingRanked bags rank parent hb a c.val) (remainingNonempty bags hne a c.val) hp
        (remainingPositive bags rank parent hb hne hp a c))) (assembleEdge bags a c.val) := by
  exact imageLaw_comp _ _

theorem sampleUnit_tv (k n : ℕ) (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p < rank l)
    (hz : 0 < count bags parent (plan rank)) :
    tv (imageLaw (sampleUnit k n bags rank parent hb hne hp hz))
      (uniform (ColoredPairing bags)) ≤ 2*(n:ℝ)^2*m/(2:ℝ)^k := by
  induction n using Nat.twoStepInduction with
  | zero =>
    let : Subsingleton (ColoredPairing bags) := ⟨fun p q=>ColoredPairing.ext
      (Pairing.ext (fun x=>Fin.elim0 x)) (funext (fun x=>Fin.elim0 x))⟩
    rw [imageLaw_subsingleton,tv_self]
    simp
  | one =>
    rw [singleton_count_zero bags rank parent hb hne hp] at hz
    omega
  | more n ih _ =>
    let a : Fin (n+2) := Fin.last (n+1)
    let p := imageLaw (drawEdge bags rank parent hb hne hp a hz k)
    let q : PositivePartner bags rank parent a → ℝ := fun c=>
      (branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank)
    let u : PositivePartner bags rank parent a → ColoredPairing bags → ℝ := fun c=>
      imageLaw (residualSampler k bags rank parent hb hne hp a c)
    let v : PositivePartner bags rank parent a → ColoredPairing bags → ℝ := fun c=>
      push (uniform (ColoredPairing (remainingBags bags a c.val))) (assembleEdge bags a c.val)
    have hvn (c : PositivePartner bags rank parent a) (y : ColoredPairing bags) : 0 ≤ v c y :=
      push_nonneg _ uniform_nonneg _ _
    have hvs (c : PositivePartner bags rank parent a) : ∑ y,v c y=1 := by
      let : Nonempty (ColoredPairing (remainingBags bags a c.val)) :=
        Fintype.card_pos_iff.mp (by rw [remainingCard bags rank parent hb hne hp]; exact c.property)
      exact push_sum _ uniform_sum _
    have huv (c : PositivePartner bags rank parent a) : tv (u c) (v c) ≤ 2*(n:ℝ)^2*m/(2:ℝ)^k := by
      dsimp only [u,v]
      rw [residualSampler_law]
      exact (push_contraction _ _ _).trans (ih (remainingBags bags a c.val)
        (remainingRanked bags rank parent hb a c.val) (remainingNonempty bags hne a c.val)
        (remainingPositive bags rank parent hb hne hp a c))
    have hpv := bind_perturbation p u v (imageLaw_nonneg _) (imageLaw_sum _)
      (2*(n:ℝ)^2*m/(2:ℝ)^k) huv
    have hpq := bind_contraction p q v hvn hvs
    have hd := drawEdge_positive_tv bags rank parent hb hne hp a hz k
    rw [sampleUnit_step_law,←exact_unit_step bags rank parent hb hne hp a hz]
    change tv (bind p u) (bind q v)≤_
    calc
      _ ≤ tv (bind p u) (bind p v)+tv (bind p v) (bind q v) := tv_triangle _ _ _
      _ ≤ (2*(n:ℝ)^2*m/(2:ℝ)^k)+(2*((n:ℝ)+2)*m/(2:ℝ)^k) := by
        apply add_le_add hpv
        exact hpq.trans (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hd)
      _ ≤ _ := by
        rw [←add_div]
        push_cast
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [show (0:ℝ)≤n*m by positivity]

end MatchingFPRAS.UnitRefresh.Materialized

namespace MatchingFPRAS.UnitRefresh

open Finset MatchingFPRAS.Variation

variable {V L J : Type*} [Fintype V] [DecidableEq V] [Fintype L] [Fintype J] [DecidableEq L] [DecidableEq J]

open Finset MatchingFPRAS.Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

theorem sampleNumbered_tv (k : ℕ) (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l) (M : ColoredPairing bags) :
    tv (imageLaw (sampleNumbered k bags rank parent hb hne hp M))
      (uniform (ColoredPairing bags)) ≤ 2*(Fintype.card V:ℝ)^2*Fintype.card L/(2:ℝ)^k := by
  have ht:=Materialized.sampleUnit_tv k (Fintype.card V) (numberedBags bags)
    (numberedRank rank) (numberedParent parent) (numberedRanked bags rank parent hb)
    (numberedNonempty bags hne) (numberedDecreasing rank parent hp)
    (numbered_count_pos bags rank parent hb hne hp M)
  change tv (imageLaw (numberingEquiv bags ∘ _)) _ ≤ _
  rw [imageLaw_comp,←imageLaw_equiv (numberingEquiv bags)]
  exact (push_contraction _ _ _).trans ht

open MatchingFPRAS.Transport

theorem sampleMatching_tv (k : ℕ) (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p < rank l)
    (M : PM (BagEdge.Incident (bags:=bags))) :
    tv (imageLaw (sampleMatching k bags rank parent hb hne hp M))
      (uniform (PM (BagEdge.Incident (bags:=bags)))) ≤
      2*(Fintype.card V:ℝ)^2*Fintype.card L/(2:ℝ)^k := by
  have ht:=sampleNumbered_tv k bags rank parent hb hne hp (Computable.pairingEquiv M)
  change tv (imageLaw ((Computable.pairingEquiv (bags:=bags)).symm ∘ _)) _ ≤ _
  rw [imageLaw_comp,←imageLaw_equiv (Computable.pairingEquiv (bags:=bags)).symm]
  exact (push_contraction _ _ _).trans ht

end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Sym2Order
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

attribute [local instance] sym2Order

attribute [local instance] bagEdgeOrder

variable {bags : V → Finset L} {G : SimpleGraph L}

variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

attribute [local instance] UnitRefresh.Computable.allowedDec

attribute [local instance] bagEdgeFintype

noncomputable local instance instDecidableEqBagPM_r3ec436_1 : DecidableEq (BagPM bags) := Classical.decEq _
lemma pairProposal_instances {E : Type*} (F₁ F₂ : Fintype E) (D₁ D₂ : DecidableEq E)
    (ends : E → Sym2 V) (hloop : ∀ e,¬(ends e).IsDiag)
    (hp₁ : ∀ e,(@univ E F₁ |>.filter (fun f=>ends f=ends e)).card≤2)
    (hp₂ : ∀ e,(@univ E F₂ |>.filter (fun f=>ends f=ends e)).card≤2) :
    @pairProposal V E _ _ F₁ D₁ ends hloop hp₁ =
      @pairProposal V E _ _ F₂ D₂ ends hloop hp₂ := by
  cases Subsingleton.elim F₁ F₂
  cases Subsingleton.elim D₁ D₂
  rfl

omit [LinearOrder V] in
lemma pairLaw_instances [LinearOrder V] {E : Type*} (F₁ F₂ : Fintype E) (ends : E → Sym2 V)
    (w z : E → ℝ) : @pairLaw V E _ F₁ ends w z = @pairLaw V E _ F₂ ends w z := by
  cases Subsingleton.elim F₁ F₂
  rfl

lemma pairProposal_eq (F : Fintype (BagEdge bags)) (D : DecidableEq (BagEdge bags))
    (hpar : ∀ e : BagEdge bags,(@univ (BagEdge bags) F |>.filter
      (fun f=>f.val.val.1=e.val.val.1)).card≤2) :
    @pairProposal V (BagEdge bags) _ _ F D (fun e=>e.val.val.1) (fun e=>e.val.property)
      hpar = treePairProposal hbags hG := by
  unfold treePairProposal
  exact pairProposal_instances _ _ _ _ _ _ _ _

omit [LinearOrder L] in
lemma pairLaw_eq [LinearOrder L] (F : Fintype (BagEdge bags)) {T q : ℕ} (w : BagEdge bags → ℚ)
    (x y : Slot T q) :
    @pairLaw V (BagEdge bags) _ F (fun e=>e.val.val.1) (slotWeight (fun e=>(w e:ℝ)) x)
      (slotWeight (fun e=>(w e:ℝ)) y) =
    (fun a : BagPM bags × BagPM bags=>slotLaw (fun e=>(w e:ℝ)) x a.1*
      slotLaw (fun e=>(w e:ℝ)) y a.2) := by
  exact pairLaw_instances F (instFintypeBagEdge_5 (bags:=bags))
    (fun e : BagEdge bags=>e.val.val.1) (slotWeight (fun e=>(w e:ℝ)) x)
      (slotWeight (fun e=>(w e:ℝ)) y)

lemma metropolis_eq_capacity (D : DecidableEq (BagPM bags × BagPM bags))
    {T q : ℕ} (w : BagEdge bags → ℚ) (x y : Slot T q) (a : BagPM bags × BagPM bags) :
    (@metropolis _ _ D (treePairProposal hbags hG)
      (fun a=>slotLaw (fun e=>(w e:ℝ)) x a.1*slotLaw (fun e=>(w e:ℝ)) y a.2) a)=
      (fun b=>(treeLadderCapacity hbags hG (fun e=>(w e:ℝ)) x y).q a b /
        (slotLaw (fun e=>(w e:ℝ)) x a.1*slotLaw (fun e=>(w e:ℝ)) y a.2)) := by
  rw [Subsingleton.elim D (inferInstance : DecidableEq (BagPM bags × BagPM bags))]
  unfold metropolis treeLadderCapacity
  funext b
  congr 2

lemma sampleLadderPair_tv {T q : ℕ} (w : BagEdge bags → ℚ) (x y : Slot T q)
    (a : BagPM bags × BagPM bags) (k : ℕ) :
    tv (imageLaw (sampleLadderPair hbags hG w x y a k))
      (fun b=>(treeLadderCapacity hbags hG (fun e=>(w e:ℝ)) x y).q a b /
        (slotLaw (fun e=>(w e:ℝ)) x a.1*slotLaw (fun e=>(w e:ℝ)) y a.2)) ≤
      4*(8*(Fintype.card (BagEdge bags):ℝ)^2+4*Fintype.card (BagEdge bags)+3)/(2:ℝ)^k := by
  classical
  have ht := Sparse.pairStepTable_tv (fun e : BagEdge bags=>e.val.val.1)
    (fun e=>e.val.property)
    (parallels_bound hbags hG)
    (rationalSlotWeight w x) (rationalSlotWeight w y)
    (rationalSlotWeight_pos w x) (rationalSlotWeight_pos w y) a k
  simp_rw [rationalSlotWeight_cast] at ht
  change tv (imageLaw (sampleLadderPair hbags hG w x y a k)) _ ≤ _ at ht
  erw [pairProposal_eq hbags hG,pairLaw_eq,metropolis_eq_capacity] at ht
  apply ht.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have ha : (a.1.val.card:ℝ)≤Fintype.card (BagEdge bags) := by exact_mod_cast card_le_univ a.1.val
  have hb : (a.2.val.card:ℝ)≤Fintype.card (BagEdge bags) := by exact_mod_cast card_le_univ a.2.val
  have hc : (a.1.val.card.choose 2:ℝ)≤(a.1.val.card:ℝ)^2 := by exact_mod_cast Nat.choose_le_pow a.1.val.card 2
  have hd : (a.1.val.card:ℝ)^2≤(Fintype.card (BagEdge bags):ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) ha 2
  nlinarith

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Variation

open Finset

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype C] in
lemma imageLaw_ignoreRight [Fintype C] [Nonempty B] (f : A → C) :
    imageLaw (fun x : A×B=>f x.1)=imageLaw f := by
  change imageLaw ((fun x : B×A=>f x.2) ∘ Equiv.prodComm A B)=_
  rw [imageLaw_comp_equiv,imageLaw_ignore]

end MatchingFPRAS.Variation

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

noncomputable local instance instDecidableEqBagPM_1_r3ec436_1 : DecidableEq (BagPM bags) := Classical.decEq _
lemma base_slotLaw {T q : ℕ} (w : BagEdge bags → ℚ) (x : Slot T q) (hx : x∈base T q) :
    slotLaw (fun e=>(w e:ℝ)) x=uniform (BagPM bags) := by
  classical
  have he : slotWeight (fun e=>(w e:ℝ)) x=fun _ : BagEdge bags=>(1:ℝ) := by
    funext e
    have ht : tier x=0 := by simp only [tier,(mem_base x).mp hx,Nat.sub_self]
    simp only [slotWeight,tierClamp,ht,pow_zero,inv_one]
    exact max_eq_left (min_le_left _ _)
  unfold slotLaw
  rw [he]
  funext A
  simp only [gibbs,partition,matchingWeight,prod_const_one,sum_const,nsmul_eq_mul,
    card_univ,mul_one,uniform,Fintype.card_eq_nat_card]



open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

attribute [local instance] prodOrder sumOrder

attribute [local instance] OAI.MatchingFPRAS.Transport.instDecidableEqBagPM_2
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p < rank l)

lemma ladderScan_tv {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k : ℕ)
    (s : Slot T q → BagPM bags) :
    tv (imageLaw (ladderScan hbags hG rank parent hb hne hp hq w M k s))
      (FiniteChain.kernel (ladderLaw (fun e=>(w e:ℝ)) T q)
        (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s) ≤
      (scanErrorNumerator V L bags T q:ℝ)/(2:ℝ)^k := by
  classical
  let eP : ℝ := 4*(8*(Fintype.card (BagEdge bags):ℝ)^2+4*Fintype.card (BagEdge bags)+3)/(2:ℝ)^k
  let eU : ℝ := 2*(Fintype.card V:ℝ)^2*Fintype.card L/(2:ℝ)^k
  have hep : 0≤eP := by dsimp [eP]; positivity
  have heu : 0≤eU := by dsimp [eU]; positivity
  have hpr : ∀ x y : Slot T q,y∈guides x → ∀ a : BagPM bags × BagPM bags,
      tv (imageLaw (pairDraw hbags hG w k x y a))
        (fun b=>(treeLadderCapacity hbags hG (fun e=>(w e:ℝ)) x y).q a b /
          (slotLaw (fun e=>(w e:ℝ)) x a.1*slotLaw (fun e=>(w e:ℝ)) y a.2))≤eP+eU := by
    intro x y _ a
    unfold pairDraw
    rw [imageLaw_ignoreRight]
    exact (sampleLadderPair_tv hbags hG w x y a k).trans (le_add_of_nonneg_right heu)
  have hr : ∀ i : Slot T q,i∈base T q →
      tv (imageLaw (baseDraw rank parent hb hne hp M k)) (slotLaw (fun e=>(w e:ℝ)) i)≤eP+eU := by
    intro i hi
    rw [base_slotLaw w i hi]
    unfold baseDraw
    rw [imageLaw_ignore]
    exact (UnitRefresh.sampleMatching_tv k bags rank parent hb hne hp M).trans
      (le_add_of_nonneg_left hep)
  have ht:= sampleScan_tv_on (slotLaw (fun e=>(w e:ℝ))) (slotLaw_pos _)
    (fun x=>slotLaw_sum _ x M) guides (fun x y hy=>(guides_order x y hy).ne)
    (base T q) (base_nonempty T q hq) (treeLadderCapacity hbags hG (fun e=>(w e:ℝ)))
    (pairDraw hbags hG w k) (fun _=>baseDraw rank parent hb hne hp M k) (eP+eU)
    (add_nonneg hep heu) hpr hr k s
  change tv (imageLaw (ladderScan hbags hG rank parent hb hne hp hq w M k s))
    (FiniteChain.kernel (ladderLaw (fun e=>(w e:ℝ)) T q)
      (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s) ≤ _ at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  have hcount : updateCount (@guides T q) (base T q)=T*q^2+q := updates_count T q
  rw [hcount]
  simp only [scanErrorNumerator,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    Nat.cast_one,eP,eU,add_div]
  ring

lemma ladderKernel_nonneg {T q : ℕ} (w : BagEdge bags → ℚ) (s t : Slot T q → BagPM bags) :
    0≤FiniteChain.kernel (ladderLaw (fun e=>(w e:ℝ)) T q)
      (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s t := by
  apply div_nonneg
  · exact scanFlow_nonneg (slotLaw _) (fun i a=>(slotLaw_pos _ i a).le) _ _ _ s t
  · exact (Finset.prod_pos (fun i _=>slotLaw_pos _ i (s i))).le

lemma ladderKernel_sum {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags)
    (s : Slot T q → BagPM bags) :
    (∑ t,FiniteChain.kernel (ladderLaw (fun e=>(w e:ℝ)) T q)
      (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s t)=1 := by
  unfold FiniteChain.kernel
  rw [←sum_div]
  have hr:=scanFlow_row (slotLaw (fun e=>(w e:ℝ))) (fun i=>slotLaw_sum _ i M)
    guides (base T q) (base_nonempty T q hq) (treeLadderCapacity hbags hG (fun e=>(w e:ℝ))) s
  change (∑ t,ladderFlow hbags hG (fun e=>(w e:ℝ)) T q s t)=_ at hr
  rw [hr]
  exact div_self (Finset.prod_pos (fun i _=>slotLaw_pos _ i (s i))).ne'

lemma ladderRun_walk_tv {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k n : ℕ)
    (s : Slot T q → BagPM bags) :
    tv (imageLaw (ladderRun hbags hG rank parent hb hne hp hq w M k n s))
      (FiniteChain.walk (ladderLaw (fun e=>(w e:ℝ)) T q)
        (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s n) ≤
      n * (scanErrorNumerator V L bags T q:ℝ)/(2:ℝ)^k := by
  have ht:=runSample_walk_tv _ _ (ladderKernel_nonneg hbags hG w)
    (ladderKernel_sum hbags hG hq w M)
    (ladderScan hbags hG rank parent hb hne hp hq w M k) _
    (ladderScan_tv hbags hG rank parent hb hne hp hq w M k) s n
  change tv (imageLaw (ladderRun hbags hG rank parent hb hne hp hq w M k n s)) _ ≤ _ at ht
  simpa only [mul_div_assoc] using ht



open Finset Replica Replica.Ladder Variation

lemma bitPrecision_error (R : ℕ) (η : ℚ) (hη : 0<η) :
    (R:ℝ)/(2:ℝ)^bitPrecision R η ≤ (η:ℝ) := by
  have hp : (R:ℝ)*(⌈η⁻¹⌉₊:ℝ)≤(2:ℝ)^bitPrecision R η := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) (R*⌈η⁻¹⌉₊)
  have hh : (η:ℝ)⁻¹≤(⌈η⁻¹⌉₊:ℝ) := by
    exact_mod_cast Nat.le_ceil (η⁻¹)
  have he : (0:ℝ)<(η:ℝ) := by exact_mod_cast hη
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2^bitPrecision R η)).mpr
  calc
    (R:ℝ) = (η:ℝ)*((R:ℝ)*(η:ℝ)⁻¹) := by field_simp
    _ ≤ (η:ℝ)*((R:ℝ)*(⌈η⁻¹⌉₊:ℝ)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hp he.le

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

attribute [local instance] prodOrder sumOrder

attribute [local instance] OAI.MatchingFPRAS.Transport.instDecidableEqBagPM_3
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p < rank l)

lemma ladderBitRun_walk_tv {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags)
    (n : ℕ) (η : ℚ) (hη : 0<η) (s : Slot T q → BagPM bags) :
    let k:=bitPrecision (n*scanErrorNumerator V L bags T q) η
    tv (imageLaw (ladderBitRun hbags hG rank parent hb hne hp hq w M k n s))
      (FiniteChain.walk (ladderLaw (fun e=>(w e:ℝ)) T q)
        (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s n) ≤ (η:ℝ) := by
  dsimp only
  unfold ladderBitRun
  change tv (imageLaw (_ ∘ runBitsEquiv V _ n)) _ ≤ _
  rw [imageLaw_comp_equiv]
  exact (ladderRun_walk_tv hbags hG rank parent hb hne hp hq w M _ n s).trans
    (by simpa only [Nat.cast_mul] using bitPrecision_error (n*scanErrorNumerator V L bags T q) η hη)

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_DiscreteLadderSteps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

lemma discreteLadderSteps_eq (N D K T m : ℕ) :
    discreteLadderSteps N D K T m=ladderSteps N D K T ((m:ℝ)⁻¹) := by
  simp only [discreteLadderSteps,ladderSteps,inv_inv]
  rw [show (2:ℝ)=(2:ℕ) by norm_cast,Real.natCeil_logb_natCast]

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

attribute [local instance] prodOrder sumOrder

noncomputable local instance instDecidableEqBagPM_4_r3ec436_1 : DecidableEq (BagPM bags) := Classical.decEq _
variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p < rank l)

lemma finiteLadder_tv (height : L → ℝ) (hheight : ∀ l,0<height l)
    (hstep : ∀ a b,G.Adj a b → height a≤2*height b)
    (D K : ℕ) (hD : 1≤D) (hN : 2≤Fintype.card V) (w : BagEdge bags → ℚ)
    (hw : ∀ e,height e.color / D ≤ (w e:ℝ) ∧ (w e:ℝ)≤3*height e.color)
    (hglobal : ∀ e,(D:ℝ)⁻¹≤(w e:ℝ) ∧ (w e:ℝ)≤3*4^K)
    (M : BagPM bags) (T m : ℕ) (hm : 1 < m) (η : ℚ) (hη : 0<η)
    (hq : 0<ladderQ (Fintype.card V) D)
    (s : Slot T (ladderQ (Fintype.card V) D) → BagPM bags) :
    tv (imageLaw (finiteLadder hbags hG rank parent hb hne hp D K T m hq w M η s))
      (ladderLaw (fun e=>(w e:ℝ)) T (ladderQ (Fintype.card V) D)) ≤ (η:ℝ)+(m:ℝ)⁻¹ := by
  have hm' : (1:ℝ)<(m:ℝ) := by exact_mod_cast hm
  have hi:=ideal_ladder_sampling hbags hG height hheight hstep D K hD hN
    (fun e=>(w e:ℝ)) hw hglobal M T s ((m:ℝ)⁻¹) (by positivity) (by exact inv_lt_one_of_one_lt₀ hm')
  rw [←discreteLadderSteps_eq] at hi
  have hb:=ladderBitRun_walk_tv hbags hG rank parent hb hne hp hq w M
    (discreteLadderSteps (Fintype.card V) D K T m) η hη s
  exact (tv_triangle _ _ _).trans (add_le_add hb hi)

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Related2
attribute [-instance] _root_.OAI.MatchingFPRAS.NumberedHierarchy.treeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumberedHierarchy

open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ)

variable (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

lemma labelEquiv_level {H : ℕ} (l : Hierarchy.Label (fun x y=>(B x y:ℝ))
    (symmetric B hsym) (triangular B htri) H) :
    (labelEquiv B hsym htri H l).1=l.1 := rfl

end MatchingFPRAS.NumberedHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumberedHierarchy

open Finset MatchingFPRAS.UnitRefresh

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (B : V → V → ℚ) (hsym : ∀ x y,B x y=B y x)

variable (htri : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)

attribute [local instance] labelOrder

variable {E : Type*} [Fintype E] [DecidableEq E] (left right : E → V)

omit [Fintype E] [DecidableEq E] in
lemma height_step (H : ℕ) (a b : Label B H) (h : (tree B hsym htri H).Adj a b) :
    (2:ℝ)^a.1.val ≤ 2*(2:ℝ)^b.1.val := by
  rcases (tree_adj B hsym htri H a b).mp h with h|h
  · have hh:=((parent_iff B hsym htri b a).mp h).1
    rw [←hh,pow_succ]
    have hp : 0≤(2:ℝ)^a.1.val := by positivity
    nlinarith
  · have hh:=((parent_iff B hsym htri a b).mp h).1
    rw [←hh,pow_succ]
    ring_nf
    exact le_rfl

end MatchingFPRAS.NumberedHierarchy

namespace MatchingFPRAS.RationalSource

open Finset MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec

lemma realPortion_on (w : V → V → ℚ) (K : ℕ) (q : SourceRealEdge V K) :
    realPortion w K (coloredReal w K q)=pathActivity w K q.1 q.2 := by
  simp only [realPortion,(coloredReal_injective w K).eq_iff,sum_ite_eq',mem_univ,ite_true]

lemma realPortion_off (w : V → V → ℚ) (K : ℕ) (e : BagEdge (bags w K))
    (he : ¬∃ q,coloredReal w K q=e) : realPortion w K e=0 := by
  apply sum_eq_zero
  intro q _
  exact ite_eq_right (fun h=>he ⟨q,h⟩)

lemma pathActivity_le_realB (w : V → V → ℚ) (K : ℕ) (e : SourceRealEdge V K) :
    pathActivity w K e.1 e.2 ≤ realB w K (realLeft K e) (realRight K e) := by
  apply (Rat.cast_le (K:=ℝ)).mp
  rw [pathActivity_cast,realB_cast]
  exact edge_activity_le_realBottleneck source target source_ne_target (2*K+2) (by omega) _ _ _ _ e.1 e.2

lemma realPortion_le_height (w : V → V → ℚ) (K : ℕ)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (e : BagEdge (bags w K)) : realPortion w K e≤2*bagHeight w K e.color := by
  by_cases he : ∃ q,coloredReal w K q=e
  · obtain ⟨q,rfl⟩:=he
    rw [realPortion_on]
    apply (pathActivity_le_realB w K q).trans
    apply (Rat.cast_le (K:=ℝ)).mp
    have hu:=dyadic_upper_of_lt (levels w K) (realB w K (realLeft K q) (realRight K q):ℝ)
      (by exact_mod_cast realB_upper w K h q)
    rw [←NumberedHierarchy.level_cast,pow_succ] at hu
    change (realB w K (realLeft K q) (realRight K q):ℝ)≤((2*2^_ : ℚ):ℝ)
    push_cast
    simpa only [coloredReal,BagEdge.color,ColoredEdge.color,realLabel,NumberedHierarchy.edgeLabel,NumberedHierarchy.labelAt,mul_comm] using hu.le
  · rw [realPortion_off w K e he]
    dsimp [bagHeight]
    positivity

lemma bagWeight_range (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 1≤D)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (e : BagEdge (bags w K)) :
    (bagHeight w K e.color:ℝ)/D≤(bagWeight w K D e:ℝ) ∧
      (bagWeight w K D e:ℝ)≤3*(bagHeight w K e.color:ℝ) := by
  have he:=realPortion_nonneg w hw K e
  have hu:=realPortion_le_height w K h e
  have hd : (1:ℚ)≤D := by exact_mod_cast hD
  have hh : bagHeight w K e.color/(D:ℚ)≤bagHeight w K e.color :=
    div_le_self (by dsimp [bagHeight]; positivity) hd
  have hlo : bagHeight w K e.color / (D:ℚ)≤bagWeight w K D e := by unfold bagWeight; linarith
  have hhi : bagWeight w K D e≤3*bagHeight w K e.color := by unfold bagWeight; linarith
  constructor <;> exact_mod_cast (by assumption)

lemma bagHeight_le (w : V → V → ℚ) (K : ℕ) (l : Label w K) : bagHeight w K l≤(4:ℚ)^K := by
  have hl : l.1.val≤2*K := (Nat.le_of_lt_succ l.1.isLt).trans (by rw [levels_eq]; exact sourceLevels_le _ _)
  calc
    _ ≤ (2:ℚ)^(2*K) := pow_le_pow_right₀ (by norm_num) hl
    _ = _ := by rw [pow_mul]; norm_num

lemma bagHeight_step (w : V → V → ℚ) (K : ℕ) (a b : Label w K) (h : (tree w K).Adj a b) :
    (bagHeight w K a:ℝ)≤2*(bagHeight w K b:ℝ) := by
  simpa only [bagHeight,Rat.cast_pow,Rat.cast_ofNat] using
    NumberedHierarchy.height_step (realB w K) (realB_symm w K) (realB_tri w K) (levels w K) a b h

lemma bagWeight_global (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 1≤D)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (e : BagEdge (bags w K)) :
    (D:ℝ)⁻¹≤(bagWeight w K D e:ℝ) ∧ (bagWeight w K D e:ℝ)≤3*4^K := by
  have hr:=bagWeight_range w hw K D hD h e
  have h1 : (1:ℝ)≤(bagHeight w K e.color:ℝ) := by exact_mod_cast bagHeight_one w K e.color
  have h4 : (bagHeight w K e.color:ℝ)≤(4:ℝ)^K := by exact_mod_cast bagHeight_le w K e.color
  constructor
  · calc
      (D:ℝ)⁻¹ = 1/(D:ℝ) := (one_div _).symm
      _ ≤ (bagHeight w K e.color:ℝ)/(D:ℝ) := div_le_div_of_nonneg_right h1 (Nat.cast_nonneg D)
      _ ≤ _ := hr.1
  · exact hr.2.trans (mul_le_mul_of_nonneg_left h4 (by norm_num))

open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Variation

attribute [local instance] prodOrder sumOrder

noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_r3ec436_1 (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagPMSourceVertexLabelBags
theorem sampler_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D T m : ℕ) (hD : 1≤D)
    (hN : 2≤Fintype.card (SourceVertex V K)) (hm : 1 < m)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) (hη : 0<η)
    (s : Slot T (ladderQ (Fintype.card (SourceVertex V K)) D) → BagPM (bags w K)) :
    tv (imageLaw (sampler w K D T m h hq M η s))
      (ladderLaw (fun e=>(bagWeight w K D e:ℝ)) T (ladderQ (Fintype.card (SourceVertex V K)) D))≤
        (η:ℝ)+(m:ℝ)⁻¹ := by
  apply finiteLadder_tv (bags_adjacent w K h) (tree_acyclic w K) (fun l=>l.1.val) (parent w K)
    (bags_ranked w K h) (bags_nonempty w K) (parent_rank w K) (fun l=>(bagHeight w K l:ℝ))
    (fun l=>by have hh : (1:ℝ)≤(bagHeight w K l:ℝ) := by exact_mod_cast bagHeight_one w K l
               linarith)
    (bagHeight_step w K) D K hD hN (bagWeight w K D) (bagWeight_range w hw K D hD h)
    (bagWeight_global w hw K D hD h) M T m hm η hη hq s

end MatchingFPRAS.RationalSource

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J}

noncomputable local instance instDecidableEqPMBagEdgeIncident_5_r3ec436_1 : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _
omit [DecidableEq V] in
lemma gibbs_instances [DecidableEq V] {E : Type*} (F₁ F₂ : Fintype E) (inc : E → V → Prop)
    (w : E → ℝ) : @gibbs V E _ inc F₁ w = @gibbs V E _ inc F₂ w := by
  cases Subsingleton.elim F₁ F₂
  rfl

noncomputable local instance instFintypeBagEdge_13_r3ec436_1 : Fintype (BagEdge bags) := Fintype.ofFinite _
omit [DecidableEq J] in
lemma slotLaw_of_weight [DecidableEq J] {T q : ℕ} (F : Fintype (BagEdge bags))
    (w : BagEdge bags → ℝ) (i : Slot T q)
    (he : slotWeight w i=w) : slotLaw w i=@gibbs V (BagEdge bags) _ BagEdge.Incident F w := by
  change @gibbs V (BagEdge bags) _ BagEdge.Incident (instFintypeBagEdge_5 (bags:=bags))
    (slotWeight w i)=_
  rw [he]
  exact gibbs_instances _ _ _ _

lemma top_marginal_tv {A : Type*} [Fintype A] {T q : ℕ} (F : Fintype (BagEdge bags))
    (hq : 0<q) (w : BagEdge bags → ℝ) (M : PM (BagEdge.Incident (bags:=bags)))
    (f : A → Slot T q → PM (BagEdge.Incident (bags:=bags)))
    (he : slotWeight w (topSlot T q hq)=w) :
    Variation.tv (Variation.imageLaw (fun a=>f a (topSlot T q hq)))
      (@gibbs V (BagEdge bags) _ BagEdge.Incident F w)≤
      Variation.tv (Variation.imageLaw f) (ladderLaw w T q) := by
  have ht:=Variation.push_contraction (Variation.imageLaw f) (ladderLaw w T q)
    (fun x=>x (topSlot T q hq))
  rw [ladder_top_marginal w T q hq M,slotLaw_of_weight F _ _ he] at ht
  change Variation.tv (Variation.imageLaw ((fun x=>x (topSlot T q hq)) ∘ f)) _≤_
  rw [Variation.imageLaw_comp]
  exact ht



open Finset Replica Replica.Ladder Variation

lemma endpoint_reaches (N D K : ℕ) (hN : 0<N) :
    max (D:ℝ) (3*4^K)≤(1+((N:ℝ)^2)⁻¹)^(endpoint N D K hN) := by
  rw [endpoint_eq]; exact ladderTier_spec N D K hN

end MatchingFPRAS.Transport

namespace MatchingFPRAS.RationalSource

open Finset MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.Enlargement
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Variation

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_1_r3ec436_1 (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagPMSourceVertexLabelBags_1
theorem topSampler_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ) (hD : 1≤D)
    (hN : 2≤Fintype.card (SourceVertex V K)) (hm : 1 < m)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) (hη : 0<η) :
    tv (imageLaw (topSampler w K D m (by omega) h hq M η))
      (gibbs (fun e=>(bagWeight w K D e:ℝ)))≤(η:ℝ)+(m:ℝ)⁻¹ := by
  let T:=endpoint (Fintype.card (SourceVertex V K)) D K (by omega)
  have hs:=sampler_tv w hw K D T m hD hN hm h hq M η hη (fun _=>M)
  have he:=slotWeight_top (fun e=>(bagWeight w K D e:ℝ)) D K T _ (by omega) hq
    (bagWeight_global w hw K D hD h) (endpoint_reaches _ _ _ (by omega))
  exact (top_marginal_tv (bagEdgeFintype (bags:=bags w K)) hq (fun e=>(bagWeight w K D e:ℝ)) M
    (sampler w K D T m h hq M η (fun _=>M)) he).trans hs

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RelabelMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource

open MatchingFPRAS Switching Subdivision RealGeometry Hierarchy Enlargement Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype

attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

lemma labelCast_level {X : Type*} [Fintype X] {B B' : X → X → ℝ}
    (s : ∀ x y,B x y=B y x)
    (t : ∀ x y z,x≠y → x≠z → y≠z → min (B x z) (B z y)≤B x y)
    (s' : ∀ x y,B' x y=B' y x)
    (t' : ∀ x y z,x≠y → x≠z → y≠z → min (B' x z) (B' z y)≤B' x y)
    {H H' : ℕ} (hB : B=B') (hH : H=H') (l : Hierarchy.Label B s t H) :
    (labelCast s t s' t' hB hH l).1.val=l.1.val := by
  cases hB;cases hH;rfl

lemma labelsEquiv_level (w : V → V → ℚ) (K : ℕ)
    (l : SourceLabel (fun x y=>(w x y:ℝ)) K) :
    (labelsEquiv w K l).1.val=l.1.val := by
  unfold labelsEquiv
  simp only [Equiv.trans_apply,NumberedHierarchy.labelEquiv_level,labelCast_level]

end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RelabelWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement
open Transport

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] OAI.MatchingFPRAS.Enlargement.relabelWeightsSourceLabelDecidableEq
attribute [local instance] OAI.MatchingFPRAS.Enlargement.relabelWeightsSourceBagEdgeFintype
lemma realPortion_on (w : V → V → ℝ) (K : ℕ) (q : SourceRealEdge V K) :
    sourceRealPortion w K (sourceColoredReal w K q)=sourceRealActivity w K q := by
  classical
  exact edgeExtension_on (sourceRealEmbedding w K) (sourceRealActivity w K) q
lemma realPortion_off (w : V → V → ℝ) (K : ℕ) (e : BagEdge (sourceBags w K))
    (he : ¬∃ q,sourceColoredReal w K q=e) : sourceRealPortion w K e=0 := by
  classical
  exact edgeExtension_off (sourceRealEmbedding w K) (sourceRealActivity w K) e he
end MatchingFPRAS.Enlargement
namespace MatchingFPRAS.RationalSource
open MatchingFPRAS Transport Enlargement Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal
lemma sourceEdgeEquiv_color (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (sourceEdgeEquiv w K e).color=labelsEquiv w K e.color := rfl
lemma bagHeight_cast (w : V → V → ℚ) (K : ℕ) (l : SourceLabel (fun x y=>(w x y:ℝ)) K) :
    (bagHeight w K (labelsEquiv w K l):ℝ)=Enlargement.bagHeight (fun x y=>(w x y:ℝ)) K l := by
  simp only [bagHeight,Enlargement.bagHeight,labelsEquiv_level]
  norm_cast
lemma realPortion_cast (w : V → V → ℚ) (K : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (realPortion w K (sourceEdgeEquiv w K e):ℝ)=sourceRealPortion (fun x y=>(w x y:ℝ)) K e := by
  classical
  by_cases he : ∃ q,sourceColoredReal (fun x y=>(w x y:ℝ)) K q=e
  · obtain ⟨q,rfl⟩:=he
    rw [sourceEdgeEquiv_real,realPortion_on,Enlargement.realPortion_on]
    exact pathActivity_cast w K q.1 q.2
  · rw [realPortion_off w K _ ?_,Enlargement.realPortion_off _ _ _ he]
    norm_num
    rintro ⟨q,hq⟩
    apply he
    refine ⟨q,(sourceEdgeEquiv w K).injective ?_⟩
    rwa [sourceEdgeEquiv_real]
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RatWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

open scoped Classical

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_6
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_7
lemma sourceBagZ_pos (w : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hz : 0 < partition w ∅) (K D : ℕ) : 0 < sourceBagZ w K D := by
  apply (sourceRealPortion_full_pos w hz K).trans_le
  apply partitionWeight_mono BagEdge.Incident _ _ (sourceRealPortion_nonneg w hw K)
  intro e
  exact le_add_of_nonneg_right (div_nonneg (bagHeight_pos w K _).le (Nat.cast_nonneg D))

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_FinitePMF
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.allowedDec _root_.OAI.MatchingFPRAS.UnitRefresh.Computable.edgeDec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Concentration

open MeasureTheory ProbabilityTheory Finset

variable {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I]

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem hoeffding_mean (X : I → Ω → ℝ) (hi : iIndepFun X μ)
    (hm : ∀ i,AEMeasurable (X i) μ) (hb : ∀ i,∀ᵐ ω ∂μ,X i ω∈Set.Icc (0:ℝ) 1)
    (m : ℝ) (hmean : ∀ i,(∫ ω,X i ω ∂μ)=m)
    (hI : 0<Fintype.card I) (t : ℝ) (ht : 0≤t) :
    μ.real {ω | t < |(∑ i,X i ω)/(Fintype.card I : ℝ)-m|} ≤
      2*Real.exp (-2*(Fintype.card I : ℝ)*t^2) := by
  classical
  have hN : (0:ℝ)<Fintype.card I := Nat.cast_pos.mpr hI
  have hc (i : I) : HasSubgaussianMGF (fun ω => X i ω-m) (1/4) μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (hm i) (hb i)
    rw [hmean i] at h
    norm_num at h ⊢
    exact h
  have hind : iIndepFun (fun i ω => X i ω-m) μ := by
    exact hi.comp (fun _ x => x-m) (fun _ => by fun_prop)
  have hs : HasSubgaussianMGF (fun ω => ∑ i,(X i ω-m))
      ((Fintype.card I : NNReal)/4) μ := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one_div,Finset.card_univ] using HasSubgaussianMGF.sum_of_iIndepFun hind (s:=univ) (fun i _ => hc i)
  have hh := hs.measure_ge_le (mul_nonneg hN.le ht)
  have hl := hs.neg.measure_ge_le (mul_nonneg hN.le ht)
  have he : -((Fintype.card I : ℝ)*t)^2 /
      (2*((Fintype.card I : NNReal)/4 : NNReal)) = -2*(Fintype.card I : ℝ)*t^2 := by
    push_cast
    field_simp [ne_of_gt hN]
    ring
  rw [he] at hh hl
  calc
    _ ≤ μ.real ({ω | (Fintype.card I : ℝ)*t ≤ ∑ i,(X i ω-m)} ∪
        {ω | (Fintype.card I : ℝ)*t ≤ -(∑ i,(X i ω-m))}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro ω hω
      simp only [Set.mem_ofPred_eq,Set.mem_union] at hω ⊢
      by_cases h : (Fintype.card I : ℝ)*t ≤ ∑ i,(X i ω-m)
      · exact Or.inl h
      · right
        simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,Finset.card_univ] at h ⊢
        rcases lt_abs.mp hω with hv | hv
        · have hv' := (lt_div_iff₀ hN).mp (by linarith : m+t < (∑ i,X i ω)/(Fintype.card I : ℝ))
          nlinarith
        · have hv' := (div_lt_iff₀ hN).mp (by linarith : (∑ i,X i ω)/(Fintype.card I : ℝ) < m-t)
          nlinarith
    _ ≤ μ.real {ω | (Fintype.card I : ℝ)*t ≤ ∑ i,(X i ω-m)} +
        μ.real {ω | (Fintype.card I : ℝ)*t ≤ -(∑ i,(X i ω-m))} := measureReal_union_le _ _
    _ ≤ _ := by simpa only [Pi.neg_apply, two_mul] using add_le_add hh hl

theorem hoeffding_observables [Fintype J] (X : J → I → Ω → ℝ)
    (hi : ∀ j,iIndepFun (X j) μ) (hm : ∀ j i,AEMeasurable (X j i) μ)
    (hb : ∀ j i,∀ᵐ ω ∂μ,X j i ω∈Set.Icc (0:ℝ) 1)
    (m : J → ℝ) (hmean : ∀ j i,(∫ ω,X j i ω ∂μ)=m j)
    (hI : 0<Fintype.card I) (t : ℝ) (ht : 0≤t) :
    μ.real {ω | ∃ j,t < |(∑ i,X j i ω)/(Fintype.card I : ℝ)-m j|} ≤
      2*(Fintype.card J : ℝ)*Real.exp (-2*(Fintype.card I : ℝ)*t^2) := by
  classical
  have he : {ω | ∃ j,t < |(∑ i,X j i ω)/(Fintype.card I : ℝ)-m j|} =
      ⋃ j,{ω | t < |(∑ i,X j i ω)/(Fintype.card I : ℝ)-m j|} := by ext; simp
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _ : J,2*Real.exp (-2*(Fintype.card I : ℝ)*t^2) := by
      apply sum_le_sum
      intro j hj
      exact hoeffding_mean (X j) (hi j) (hm j) (hb j) (m j) (hmean j) hI t ht
    _ = _ := by simp; ring



open MeasureTheory ProbabilityTheory Finset
open scoped Classical

variable {Ω I J : Type*} [Fintype Ω] [Fintype I] [Fintype J]

lemma finitePMF_apply (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1) (x : Ω) :
    (finitePMF p hp hs x).toReal=p x := by simp [finitePMF,hp x]

theorem finite_hoeffding [DecidableEq I] (p : Ω → ℝ) (hp : ∀ x,0 ≤ p x) (hs : ∑ x,p x=1)
    (f : J → Ω → ℝ) (hf : ∀ j x,f j x∈Set.Icc (0:ℝ) 1)
    (hI : 0<Fintype.card I) (t : ℝ) (ht : 0≤t) :
    ∑ v : I → Ω,(if ∃ j,t < |(∑ i,f j (v i))/(Fintype.card I : ℝ)-∑ x,p x*f j x|
      then ∏ i,p (v i) else 0) ≤
      2*(Fintype.card J : ℝ)*Real.exp (-2*(Fintype.card I : ℝ)*t^2) := by
  classical
  let : MeasurableSpace Ω := ⊤
  let q := finitePMF p hp hs
  let μ : Measure (I → Ω) := Measure.pi (fun _ : I => q.toMeasure)
  have hi (j : J) : iIndepFun (fun i (v : I → Ω) => f j (v i)) μ := by
    exact iIndepFun_pi (fun _ : I => (measurable_of_finite (f j)).aemeasurable)
  have hm (j : J) (i : I) : AEMeasurable (fun v : I → Ω => f j (v i)) μ :=
    (measurable_of_finite _).aemeasurable
  have hb (j : J) (i : I) : ∀ᵐ v ∂μ,f j (v i)∈Set.Icc (0:ℝ) 1 :=
    Filter.Eventually.of_forall (fun v => hf j (v i))
  have he (j : J) (i : I) : (∫ v,f j (v i) ∂μ)=∑ x,p x*f j x := by
    have hev := (measurePreserving_eval (fun _ : I => q.toMeasure) i).map_eq
    have hmap := integral_map ((measurable_of_finite (Function.eval i)).aemeasurable (μ:=μ))
      ((measurable_of_finite (f j)).aestronglyMeasurable (μ:=Measure.map (Function.eval i) μ))
    rw [hev] at hmap
    rw [←hmap, PMF.integral_eq_sum]
    apply sum_congr rfl
    intro x hx
    simp [q,finitePMF_apply,smul_eq_mul]
  have h := hoeffding_observables (μ:=μ) (fun j i v => f j (v i)) hi hm hb
    (fun j => ∑ x,p x*f j x) he hI t ht
  have hsingle (v : I → Ω) : μ.real {v}=∏ i,p (v i) := by
    simp only [Measure.real,μ,Measure.pi_singleton,ENNReal.toReal_prod]
    apply prod_congr rfl
    intro i hi
    simp [q,finitePMF,hp (v i)]
  let B : Finset (I → Ω) := univ.filter (fun v => ∃ j,t < |(∑ i,f j (v i))/(Fintype.card I : ℝ)-∑ x,p x*f j x|)
  have hB : (B : Set (I → Ω))={v | ∃ j,t < |(∑ i,f j (v i))/(Fintype.card I : ℝ)-∑ x,p x*f j x|} := by
    ext v; simp [B]
  rw [←hB,←sum_measureReal_singleton] at h
  simpa only [hsingle, B, sum_filter] using h



lemma observables_exp_tail (n K : ℕ) (hK : 0<K) :
    2*((n:ℝ)^2+2)*Real.exp (-20*((n:ℝ)+K+1)) < 1/(100*K) := by
  have hK0 : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
  have h1 : (2:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hc : (200:ℝ)<Real.exp 8 := by
    calc
      (200:ℝ) < 2^8 := by norm_num
      _ ≤ (Real.exp 1)^8 := pow_le_pow_left₀ (by norm_num) h1 _
      _ = Real.exp 8 := by rw [← Real.exp_nat_mul]; norm_num
  have hn : (n:ℝ)^2+2≤Real.exp (2*((n:ℝ)+1)) := by
    have h := Real.add_one_le_exp ((n:ℝ)+1)
    have hh : 0≤(n:ℝ)+2 := by positivity
    calc
      _ ≤ ((n:ℝ)+2)^2 := by nlinarith
      _ ≤ (Real.exp ((n:ℝ)+1))^2 := pow_le_pow_left₀ hh (by linarith) _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hk : (K:ℝ)≤Real.exp (K:ℝ) := by linarith [Real.add_one_le_exp (K:ℝ)]
  have hprod : 200*(K:ℝ)*((n:ℝ)^2+2)<Real.exp (20*((n:ℝ)+K+1)) := by
    calc
      _ ≤ 200*Real.exp (K:ℝ)*Real.exp (2*((n:ℝ)+1)) := by gcongr
      _ < Real.exp 8*Real.exp (K:ℝ)*Real.exp (2*((n:ℝ)+1)) := by gcongr
      _ = Real.exp (8+(K:ℝ)+2*((n:ℝ)+1)) := by rw [Real.exp_add,Real.exp_add]
      _ < _ := Real.exp_lt_exp.mpr (by nlinarith)
  have he : 0<Real.exp (20*((n:ℝ)+K+1)) := Real.exp_pos _
  rw [show -20*((n:ℝ)+K+1)= -(20*((n:ℝ)+K+1)) by ring,Real.exp_neg]
  apply (lt_div_iff₀ (by positivity : (0:ℝ)<100*K)).mpr
  rw [← div_eq_mul_inv, (div_mul_eq_mul_div), div_lt_one he]
  nlinarith [hprod]

lemma stage_hoeffding_budget (n K S : ℕ) (hK : 0<K) (sigma : ℝ)
    (hS : 10*((n:ℝ)+K+1)≤(S:ℝ)*sigma^2) :
    2*((n:ℝ)^2+2)*Real.exp (-2*(S:ℝ)*sigma^2)<1/(100*K) := by
  apply lt_of_le_of_lt _ (observables_exp_tail n K hK)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

end MatchingFPRAS.Concentration

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_8
lemma observableProbe_range_off (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (e₀ : LogicalEdge V) (a : SourceMarked w K) :
    0 ≤ observableProbe w w₁ K e₀ a ∧ observableProbe w w₁ K e₀ a ≤ 1 := by
  unfold observableProbe
  split_ifs
  · exact ⟨Finset.prod_nonneg (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).1),
      Finset.prod_le_one (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).1)
        (fun e _ => (bagReweight_range_off w w₁ hw hw₁ hle K e).2)⟩
  · norm_num

lemma sourceObservable_range (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (j : ObservableIndex V) (a : SourceMarked w K) :
    sourceObservable w w₁ K j a∈Set.Icc (0:ℝ) 1 := by
  cases j with
  | inl i =>
    dsimp [sourceObservable]
    split_ifs
    · exact observableA_range w K a
    · exact observableD_range_off w w₁ hw hw₁ hle K a
  | inr e => exact observableProbe_range_off w w₁ hw hw₁ hle K e a

omit [Nontrivial V] in
lemma observableIndex_card : Fintype.card (ObservableIndex V) ≤ (Fintype.card V)^2+2 := by
  have h := Fintype.card_subtype_le (fun e : V×V => e.1<e.2)
  change Fintype.card (LogicalEdge V) ≤ Fintype.card (V×V) at h
  simp only [Fintype.card_prod] at h
  simpa only [ObservableIndex,Fintype.card_sum,Fintype.card_fin,pow_two,Nat.add_comm] using Nat.add_le_add_left h 2

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_9
theorem source_ideal_concentration (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (hz : 0 < partition w ∅) (K S : ℕ) (hS : 0<S) (σ : ℝ) (hσ : 0≤σ) :
    ∑ x : Fin S → SourceMarked w K,(if ¬StageGood w w₁ K σ x
      then ∏ i,sourceLaw w K (sourceD (V:=V) K) (x i) else 0) ≤
      2*((Fintype.card V:ℝ)^2+2)*Real.exp (-2*(S:ℝ)*σ^2) := by
  have hp := sourceBagZ_pos w hw hz K (sourceD (V:=V) K)
  have h := MatchingFPRAS.Concentration.finite_hoeffding (I:=Fin S)
    (sourceLaw w K (sourceD (V:=V) K)) (sourceLaw_nonneg w hw K _ hp.le)
    (sourceLaw_sum w K _ hp.ne') (sourceObservable w w₁ K) (sourceObservable_range w w₁ hw hw₁ hle K)
    (by simpa using hS) σ hσ
  have he : ∀ x : Fin S → SourceMarked w K,
      (¬StageGood w w₁ K σ x) ↔
      (∃ j,σ < |(∑ i,sourceObservable w w₁ K j (x i))/(Fintype.card (Fin S):ℝ)-
        ∑ a,sourceLaw w K (sourceD (V:=V) K) a*sourceObservable w w₁ K j a|) := by
    intro x
    simp only [StageGood,not_forall,not_le,sampleAverage,sourceMean,Fintype.card_fin]
  simp_rw [he] at ⊢
  apply h.trans
  have hc : (Fintype.card (ObservableIndex V):ℝ) ≤ (Fintype.card V:ℝ)^2+2 := by
    exact_mod_cast (observableIndex_card (V:=V))
  simpa only [Fintype.card_fin] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (Real.exp_pos _).le

variable {n K T S : ℕ} [Nontrivial (Fin n)]

lemma StageData.sigma_pos (c : StageData n K T) : 0 < RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold RealStage.sigma RealStage.alpha
  have hD : 0 < sourceD (V:=Fin n) K := sourceD_one K
  have ht : 0 < T := c.stages
  have he := c.epsilon_positive
  exact lt_min (by positivity) (by positivity)

lemma StageData.sampleCount_pos (c : StageData n K T) :
    0 < stageSampleCount n (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold stageSampleCount
  apply Nat.ceil_pos.mpr
  have hs := c.sigma_pos
  positivity

lemma StageData.sampleCount_bound (c : StageData n K T) :
    10*((n:ℝ)+T+1) ≤
      (stageSampleCount n (sourceD (V:=Fin n) K) T c.epsilon:ℝ)*
        (RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon)^2 := by
  have hs := c.sigma_pos
  have h := mul_le_mul_of_nonneg_right
    (Nat.le_ceil (10*((RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon)⁻¹)^2*((n:ℝ)+T+1)))
    (sq_nonneg (RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  all_goals first | rfl | field_simp [ne_of_gt hs]

theorem source_ideal_budget (w w₁ : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hw₁ : ∀ x y,0 ≤ w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (hz : 0 < partition w ∅) (K T S : ℕ) (hT : 0<T) (hS : 0<S)
    (σ : ℝ) (hσ : 0≤σ) (hsize : 10*((Fintype.card V:ℝ)+T+1) ≤ (S:ℝ)*σ^2) :
    ∑ x : Fin S → SourceMarked w K,(if ¬StageGood w w₁ K σ x
      then ∏ i,sourceLaw w K (sourceD (V:=V) K) (x i) else 0) < 1/(100*T) := by
  exact (source_ideal_concentration w w₁ hw hw₁ hle hz K S hS σ hσ).trans_lt
    (MatchingFPRAS.Concentration.stage_hoeffding_budget (Fintype.card V) T S hT σ hsize)



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_9
attribute [local instance] OAI.MatchingFPRAS.Enlargement.instFintypeBagEdgeSourceVertexSourceLabelSourceBags_10
theorem source_nearby_budget (w w₁ : V → V → ℝ) (hw : ∀ x y,0<w x y)
    (hw₁ : ∀ x y,0≤w₁ x y) (hle : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (hz : 0<Switching.partition w ∅) (K T S : ℕ) (hT : 0<T) (hS : 0<S)
    (σ : ℝ) (hσ : 0≤σ) (hsize : 10*((Fintype.card V:ℝ)+T+1) ≤ (S:ℝ)*σ^2)
    (p : SourceMarked w K → ℝ) (hp : ∀ a,0≤p a) (hpsum : ∑ a,p a=1)
    (htv : Variation.tv p (sourceLaw w K (sourceD (V:=V) K)) ≤ 3/(1000*T*S)) :
    Variation.event (Variation.iid p S) (fun x => ¬StageGood w w₁ K σ x) < 13/(1000*T) := by
  have hpos := sourceBagZ_pos w hw hz K (sourceD (V:=V) K)
  have hq := sourceLaw_nonneg w hw K _ hpos.le
  have hqs := sourceLaw_sum w K _ hpos.ne'
  have hiid := Variation.iid_tv p (sourceLaw w K (sourceD (V:=V) K)) hp hpsum hq hqs S
  have he := Variation.event_sub_le (Variation.iid p S)
    (Variation.iid (sourceLaw w K (sourceD (V:=V) K)) S)
    (by rw [Variation.iid_sum p hpsum,Variation.iid_sum _ hqs])
    (fun x => ¬StageGood w w₁ K σ x)
  have hv := (le_abs_self _).trans (he.trans hiid)
  have hh := source_ideal_budget w w₁ hw hw₁ hle hz K T S hT hS σ hσ hsize
  have ht := mul_le_mul_of_nonneg_left htv (Nat.cast_nonneg S : (0:ℝ)≤S)
  have hid : (1:ℝ)/(100*T)+(S:ℝ)*(3/(1000*T*S))=13/(1000*T) := by
    have ht0 : (T:ℝ)≠0 := by exact_mod_cast hT.ne'
    have hs0 : (S:ℝ)≠0 := by exact_mod_cast hS.ne'
    field_simp
    ring
  have hh' : Variation.event (Variation.iid (sourceLaw w K (sourceD (V:=V) K)) S)
      (fun x => ¬StageGood w w₁ K σ x) < 1/(100*T) := by
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    unfold Variation.event Variation.iid
    congr 1
    funext x
    split_ifs <;> rfl
  linarith

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_AdaptiveLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Adaptive
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_1_r3ec436_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
lemma Parameters.sigma_pos (p : Parameters G) : 0<p.sigma := p.initialData.sigma_pos

lemma Parameters.S_pos (p : Parameters G) : 0<p.S := p.initialData.sampleCount_pos

lemma Parameters.S_bound (p : Parameters G) : 10*((G.n:ℝ)+p.K+1) ≤ (p.S:ℝ)*p.sigma^2 :=
  p.initialData.sampleCount_bound

attribute [instance] Layer.finite

end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_ProductBits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation

open Finset
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

omit [Fintype Ω] in
lemma product_nonneg {I : Type*} [Fintype I] [DecidableEq I] (p : I → Ω → ℝ)
    (hp : ∀ i x,0≤p i x) (x : I → Ω) : 0≤product p x :=
  prod_nonneg (fun i _=>hp i (x i))

lemma product_sum {I : Type*} [Fintype I] [DecidableEq I] (p : I → Ω → ℝ)
    (hp : ∀ i,∑ x,p i x=1) : ∑ x,product p x=1 := by
  unfold product
  rw [←Fintype.prod_sum]
  simp [hp]

lemma product_fin_tv (n : ℕ) (p q : Fin n → Ω → ℝ)
    (hp : ∀ i x,0≤p i x) (hps : ∀ i,∑ x,p i x=1)
    (hq : ∀ i x,0≤q i x) (hqs : ∀ i,∑ x,q i x=1) :
    tv (product p) (product q)≤∑ i,tv (p i) (q i) := by
  induction n with
  | zero => simp [tv,product]
  | succ n ih =>
    let e : (Ω×(Fin n → Ω)) ≃ (Fin (n+1) → Ω) := Fin.consEquiv (fun _=>Ω)
    have hpE : product p ∘ e=tensor (p 0) (product (fun i : Fin n=>p i.succ)) := by
      funext x
      simp [product,tensor,e,Fin.prod_univ_succ]
    have hqE : product q ∘ e=tensor (q 0) (product (fun i : Fin n=>q i.succ)) := by
      funext x
      simp [product,tensor,e,Fin.prod_univ_succ]
    rw [←tv_equiv e,hpE,hqE]
    have ht := tensor_tv (p 0) (q 0) (product (fun i : Fin n=>p i.succ))
      (product (fun i : Fin n=>q i.succ)) (hp 0) (hps 0)
      (product_nonneg (fun i : Fin n=>q i.succ) (fun i=>hq i.succ))
      (product_sum (fun i : Fin n=>q i.succ) (fun i=>hqs i.succ))
    rw [Fin.sum_univ_succ]
    exact ht.trans (add_le_add_right (ih _ _ (fun i=>hp i.succ) (fun i=>hps i.succ)
      (fun i=>hq i.succ) (fun i=>hqs i.succ)) _)

lemma product_tv {I : Type*} [Fintype I] [DecidableEq I] (p q : I → Ω → ℝ)
    (hp : ∀ i x,0≤p i x) (hps : ∀ i,∑ x,p i x=1)
    (hq : ∀ i x,0≤q i x) (hqs : ∀ i,∑ x,q i x=1) :
    tv (product p) (product q)≤∑ i,tv (p i) (q i) := by
  let e:=Fintype.equivFin I
  let a : (I → Ω) ≃ (Fin (Fintype.card I) → Ω) := Equiv.arrowCongr e (Equiv.refl Ω)
  have he (p : I → Ω → ℝ) : product p ∘ a.symm=product (fun i=>p (e.symm i)) := by
    funext x
    change (∏ i,p i (x (e i)))=∏ j,p (e.symm j) (x j)
    exact Fintype.prod_equiv e _ _ (by simp)
  rw [←tv_equiv a.symm,he,he]
  have ht:=product_fin_tv _ (fun i=>p (e.symm i)) (fun i=>q (e.symm i))
    (fun i=>hp _) (fun i=>hps _) (fun i=>hq _) (fun i=>hqs _)
  rw [e.symm.sum_comp (fun i=>tv (p i) (q i))] at ht
  exact ht

lemma uniform_fun {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] (x : I → A) :
    uniform (I → A) x=∏ i,uniform A (x i) := by
  simp [uniform,Nat.cast_pow]

omit [Fintype Ω] in
lemma imageLaw_componentwise [Fintype Ω] {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (f : I → A → Ω) : imageLaw (fun x : I → A=>fun i=>f i (x i))=
      product (fun i=>imageLaw (f i)) := by
  funext y
  let : DecidableEq (I → Ω) := Classical.decEq _
  have he (x : I → A) : (if (fun i=>f i (x i))=y then uniform (I → A) x else 0)=
      ∏ i,if f i (x i)=y i then uniform A (x i) else 0 := by
    by_cases h : (fun i=>f i (x i))=y
    · rw [ite_eq_left h,uniform_fun]
      apply prod_congr rfl
      intro i _
      rw [ite_eq_left (congrFun h i)]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ : ∃ i,f i (x i)≠y i := by
        by_contra hn
        apply h
        funext i
        exact Classical.not_not.mp (fun hi=>hn ⟨i,hi⟩)
      symm
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  unfold imageLaw push product
  simp_rw [he]
  exact (Fintype.prod_sum (fun i a=>if f i a=y i then uniform A a else 0)).symm

lemma product_restrict {I : Type*} [Fintype I] [DecidableEq I] (S : Finset I)
    (p : I → Ω → ℝ) (hs : ∀ i,∑ a,p i a=1) :
    push (product p) (fun x=>fun i : S=>x i.val)=product (fun i : S=>p i.val) := by
  funext y
  let : DecidableEq (S → Ω) := Classical.decEq _
  let q : I → Ω → ℝ := fun i a=>if hi : i∈S then (if a=y ⟨i,hi⟩ then p i a else 0) else p i a
  have he (x : I → Ω) : (if (fun i : S=>x i.val)=y then product p x else 0)=∏ i,q i (x i) := by
    by_cases h : (fun i : S=>x i.val)=y
    · rw [ite_eq_left h]
      apply prod_congr rfl
      intro i _
      by_cases hi : i∈S
      · simp only [q,dite_eq_left hi,congrFun h ⟨i,hi⟩,ite_true]
      · simp only [q,dite_eq_right hi]
    · rw [ite_eq_right h]
      obtain ⟨i,hi⟩ : ∃ i : S,x i.val≠y i := by
        by_contra hn
        apply h
        funext i
        exact Classical.not_not.mp (fun hi=>hn ⟨i,hi⟩)
      symm
      apply prod_eq_zero (mem_univ i.val)
      simp only [q,dite_eq_left i.property,ite_eq_right hi]
  have hq (i : I) : ∑ a,q i a=if hi : i∈S then p i (y ⟨i,hi⟩) else 1 := by
    by_cases hi : i∈S
    · simp [q,hi]
    · simp [q,hi,hs i]
  unfold push
  simp_rw [he]
  rw [←Fintype.prod_sum]
  simp_rw [hq]
  change (∏ i,if hi : i∈S then p i (y ⟨i,hi⟩) else 1)=∏ i : S,p i.val (y i)
  let g : I → ℝ := fun i=>if hi : i∈S then p i (y ⟨i,hi⟩) else 1
  change (∏ i,g i)=_
  calc
    _ = ∏ i∈S,g i := (prod_subset (subset_univ S) (by intro i _ hi;simp [g,hi])).symm
    _ = ∏ i∈S.attach,g i.val := (Finset.prod_attach S g).symm
    _ = ∏ i : S,p i.val (y i) := by
      rw [Finset.univ_eq_attach]
      apply prod_congr rfl
      intro i _
      simp [g]

lemma imageLaw_tensor {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → C) (g : B → D) :
    imageLaw (fun x : A×B=>(f x.1,g x.2))=tensor (imageLaw f) (imageLaw g) := by
  funext y
  simp only [imageLaw,push,tensor,Fintype.sum_prod_type,uniform_prod,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro a _
  by_cases hf : f a=y.1 <;> by_cases hg : g b=y.2 <;> simp [hf,hg,Prod.ext_iff]

lemma push_tensor_sigma {A B : Type*} [Fintype A] [Fintype B] {C : A → Type*}
    [∀ a,Fintype (C a)] (p : A → ℝ) (r : B → ℝ) (f : ∀ a,B → C a) :
    push (tensor p r) (fun x : A×B=>Sigma.mk x.1 (f x.1 x.2))=
      sigmaLift p (fun a=>push r (f a)) := by
  funext x
  obtain ⟨a,c⟩:=x
  simp only [push,tensor,sigmaLift,Fintype.sum_prod_type]
  have he (x : A) : (∑ b,if (⟨x,f x b⟩ : Sigma C)=⟨a,c⟩ then p x*r b else 0)=
      if x=a then p a*(∑ b,if f a b=c then r b else 0) else 0 := by
    by_cases h : x=a
    · subst x
      simp [mul_sum,mul_ite]
    · simp only [ite_eq_right h]
      apply sum_eq_zero
      intro b _
      apply ite_eq_right
      intro he
      exact h (congrArg Sigma.fst he)
  simp_rw [he]
  simp

end MatchingFPRAS.Variation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TableMarking
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TableMarking

open Finset Transport Variation

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]

variable (inc : E → V → Prop)

variable {A : Type*} [Fintype A] [Nonempty A]

lemma reveal_law (p : PM inc → ℝ) (c : E → WeightedOptions I) :
    push (tensor p (product (portion c))) (fun x : PM inc×(E → I)=>reveal inc x.1 x.2)=
      sigmaLift p (fun M=>product (fun e : M.val=>portion c e.val)) := by
  calc
    _ = sigmaLift p (fun M=>push (product (portion c)) (fun m=>fun e : M.val=>m e.val)) := by
      exact push_tensor_sigma p (product (portion c)) (fun M m=>fun e : M.val=>m e.val)
    _ = _ := ?_
  congr 1
  funext M
  apply product_restrict
  intro e
  exact WeightedOptions.real_law_sum (c e)

lemma draw_tv (f : A → PM inc) (w : E → ℝ) (c : E → WeightedOptions I) (k : ℕ) :
    tv (imageLaw (draw inc f c k)) (law inc w c)≤
      tv (imageLaw f) (gibbs w)+(∑ e : E,(2:ℝ)*(c e).size)/(2:ℝ)^k := by
  let mark : (E → Fin k → Bool) → E → I := fun bits e=>(c e).draw k (bits e)
  have hs (e : E) : ∑ b,portion c e b=1 := WeightedOptions.real_law_sum _
  have hn (e : E) (b : I) : 0≤portion c e b := (Rat.cast_nonneg (K:=ℝ)).mpr ((c e).law_nonneg b)
  have hm : tv (imageLaw mark) (product (portion c))≤(∑ e : E,(2:ℝ)*(c e).size)/(2:ℝ)^k := by
    rw [show mark=(fun bits : E → Fin k → Bool=>fun e=>(c e).draw k (bits e)) from rfl,
      imageLaw_componentwise]
    have hh:=product_tv (fun e=>imageLaw ((c e).draw k)) (portion c)
      (fun e=>imageLaw_nonneg _) (fun e=>imageLaw_sum _) hn hs
    refine hh.trans ?_
    rw [sum_div]
    apply sum_le_sum
    intro e _
    exact (c e).draw_tv k
  have htv:=tensor_tv (imageLaw f) (gibbs w) (imageLaw mark) (product (portion c))
    (imageLaw_nonneg f) (imageLaw_sum f) (product_nonneg _ hn) (product_sum _ hs)
  have hc:=push_contraction (tensor (imageLaw f) (imageLaw mark))
    (tensor (gibbs w) (product (portion c))) (fun x : PM inc×(E → I)=>reveal inc x.1 x.2)
  rw [reveal_law inc _ c,←imageLaw_tensor f mark,←imageLaw_comp] at hc
  change tv (imageLaw (draw inc f c k)) (law inc w c)≤_ at hc
  rw [imageLaw_tensor f mark] at hc
  exact hc.trans (htv.trans (add_le_add_right hm _))

lemma draw_tv_size (f : A → PM inc) (w : E → ℝ) (c : E → WeightedOptions I) (k s : ℕ)
    (h : ∀ e,(c e).size=s) :
    tv (imageLaw (draw inc f c k)) (law inc w c)≤
      tv (imageLaw f) (gibbs w)+2*s*Fintype.card E/(2:ℝ)^k := by
  have hh:=draw_tv inc f w c k
  simpa [h,mul_comm,mul_left_comm,mul_assoc] using hh

end MatchingFPRAS.TableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_Marking
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation
lemma imageLaw_instances {A B : Type*} (F₁ F₂ : Fintype A) (f : A → B) :
    @imageLaw A B F₁ f=@imageLaw A B F₂ f := by
  cases Subsingleton.elim F₁ F₂
  rfl
lemma tv_instances {A : Type*} (F₁ F₂ : Fintype A) (p q : A → ℝ) :
    @tv A F₁ p q=@tv A F₂ p q := by
  cases Subsingleton.elim F₁ F₂
  rfl
end MatchingFPRAS.Variation
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_2_r3ec436_1 (w : V → V → ℚ) (K : ℕ) : DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma markingTable_law (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (e : BagEdge (bags w K)) (i : Fin 3) :
    (markingTable w hw K D hD e).law i=portions w K D e i/bagWeight w K D e := by
  change (∑ j : Fin 3,if j=i then portions w K D e j/bagWeight w K D e else 0)=_
  simp only [sum_ite_eq',mem_univ,ite_true]

attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagPMSourceVertexLabelBags_2
attribute [local instance] OAI.MatchingFPRAS.RationalSource.sourceMarkedFintype
attribute [local instance] OAI.MatchingFPRAS.RationalSource.sourceMarkingBitsFintype
lemma marking_tv {A : Type*} [Fintype A] [Nonempty A]
    (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (f : A → BagPM (bags w K)) (k : ℕ) :
    tv (imageLaw (TableMarking.draw BagEdge.Incident f (markingTable w hw K D hD) k))
      (markedLaw w K D)≤tv (imageLaw f) (gibbs (fun e=>(bagWeight w K D e:ℝ)))+
        6*Fintype.card (BagEdge (bags w K))/(2:ℝ)^k := by
  have he : TableMarking.law BagEdge.Incident (fun e=>(bagWeight w K D e:ℝ))
      (markingTable w hw K D hD)=markedLaw w K D := by
    unfold TableMarking.law TableMarking.portion markedLaw
    simp only [markingTable_law]
  have hh:=TableMarking.draw_tv_size BagEdge.Incident f
    (fun e=>(bagWeight w K D e:ℝ)) (markingTable w hw K D hD) k 3 (fun _=>rfl)
  rw [he] at hh
  norm_num only [Nat.cast_ofNat] at hh
  rw [imageLaw_instances _ (sourceMarkingBitsFintype w K k),
    tv_instances _ (sourceMarkedFintype w K)] at hh
  exact hh

theorem markedSampler_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ) (hD : 1≤D)
    (hN : 2≤Fintype.card (SourceVertex V K)) (hm : 1 < m)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) (hη : 0<η) :
    tv (markedSamplerLaw w hw K D m (lt_of_lt_of_le Nat.zero_lt_one hD) (lt_of_lt_of_le Nat.zero_lt_two hN) h hq M η)
      (markedLaw w K D)≤2*(η:ℝ)+(m:ℝ)⁻¹ := by
  have hh:=marking_tv w hw K D (lt_of_lt_of_le Nat.zero_lt_one hD)
    (topSampler w K D m (lt_of_lt_of_le Nat.zero_lt_two hN) h hq M η)
    (bitPrecision (6*Fintype.card (BagEdge (bags w K))) η)
  have hs:=topSampler_tv w hw K D m hD hN hm h hq M η hη
  have hb:=bitPrecision_error (6*Fintype.card (BagEdge (bags w K))) η hη
  push_cast at hb
  change tv (markedSamplerLaw w hw K D m (lt_of_lt_of_le Nat.zero_lt_one hD)
    (lt_of_lt_of_le Nat.zero_lt_two hN) h hq M η) _≤_ at hh
  linarith
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_RelabelMarking
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
omit [DecidableEq V] [Fintype E] [Fintype F] [Fintype I] in
lemma mass_markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (part : F → I → ℝ) (a : Marking.Marked (I:=I) inc) :
    Marking.mass j part (markedEquiv e he a)=Marking.mass inc (part ∘ e) a := by
  apply Fintype.prod_equiv (selectedEquiv e he a.1).symm
  intro x
  change part x.val ((markedEquiv e he a).2 x)=part (e ((selectedEquiv e he a.1).symm x).val) (a.2 ((selectedEquiv e he a.1).symm x))
  rw [←markedEquiv_mark e he a]
  simp only [Equiv.apply_symm_apply]
  congr 1
  exact (e.apply_symm_apply x.val).symm
lemma partitionWeight_pmEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (w : F → ℝ) : partitionWeight j w univ=partitionWeight inc (w ∘ e) univ := by
  classical
  unfold partitionWeight
  symm
  apply Fintype.sum_equiv (pmEquiv e he)
  intro M
  exact (matchingWeight_pmEquiv e he w M).symm
lemma law_markedEquiv (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (part : F → I → ℝ) (a : Marking.Marked (I:=I) inc) :
    Marking.law j part (markedEquiv e he a)=Marking.law inc (part ∘ e) a := by
  unfold Marking.law
  rw [mass_markedEquiv,partitionWeight_pmEquiv e he]
  rfl
end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MarkBridge
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_1
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_3_r3ec436_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma sourceEdgeEquiv_central (w : V → V → ℚ) (K : ℕ) (q : LogicalEdge V) :
    sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q)=centralEdge w K q :=
  sourceEdgeEquiv_real w K _
lemma probePortion_cast (w : V → V → ℚ) (K D : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) :
    (probePortion w K D (sourceEdgeEquiv w K e):ℝ)=Enlargement.probePortion (fun x y=>(w x y:ℝ)) K D e := by
  classical
  have he : (∃ q,centralEdge w K q=sourceEdgeEquiv w K e) ↔
      ∃ q,Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q=e := by
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q,(sourceEdgeEquiv w K).injective ((sourceEdgeEquiv_central w K q).trans hq)⟩
    · rintro ⟨q,rfl⟩
      exact ⟨q,(sourceEdgeEquiv_central w K q).symm⟩
  simp only [probePortion,Enlargement.probePortion,he]
  split_ifs <;> push_cast <;> rfl
lemma portions_cast (w : V → V → ℚ) (K D : ℕ)
    (e : BagEdge (sourceBags (fun x y=>(w x y:ℝ)) K)) (i : Fin 3) :
    (portions w K D (sourceEdgeEquiv w K e) i:ℝ)=sourcePortions (fun x y=>(w x y:ℝ)) K D e i := by
  fin_cases i
  · exact realPortion_cast w K e
  · change ((bagHeight w K (sourceEdgeEquiv w K e).color/D-probePortion w K D (sourceEdgeEquiv w K e):ℚ):ℝ)=_
    rw [Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,probePortion_cast,sourceEdgeEquiv_color,bagHeight_cast]
    rfl
  · exact probePortion_cast w K D e
lemma portions_collapse (w : V → V → ℚ) (K D : ℕ) :
    Marking.collapse (fun e i=>(portions w K D e i:ℝ))=fun e=>(bagWeight w K D e:ℝ) := by
  funext e
  change (∑ i : Fin 3,(portions w K D e i:ℝ))=(bagWeight w K D e:ℝ)
  exact_mod_cast portions_sum w K D e
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeBagEdgeSourceVertexSourceLabelCastRealSourceBags_1
lemma markedLaw_eq (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (a : Marked w K) :
    markedLaw w K D a=Marking.law BagEdge.Incident (fun e i=>(portions w K D e i:ℝ)) a := by
  have hc : ∀ e,Marking.collapse (fun e i=>(portions w K D e i:ℝ)) e≠0 := by
    intro e
    rw [portions_collapse]
    dsimp only
    exact_mod_cast (bagWeight_pos w hw K D hD e).ne'
  have h:=Marking.law_from_reveal BagEdge.Incident (fun e i=>(portions w K D e i:ℝ)) hc a
  rw [portions_collapse] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [markedLaw,Variation.sigmaLift,product,gibbs,matchingWeight,partition,Marking.conditional,
    portions_collapse,Rat.cast_div,partitionWeight]
  all_goals (try congr 3)
  all_goals (try ext)
  all_goals (try simp)
lemma markedLaw_equiv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    markedLaw w K D (sourceMarkedEquiv w K a)=sourceLaw (fun x y=>(w x y:ℝ)) K D a := by
  rw [markedLaw_eq w hw K D hD]
  change Marking.law BagEdge.Incident (fun e i=>(portions w K D e i:ℝ))
    (markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl) a)=_
  rw [law_markedEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (fun _ _=>Iff.rfl)]
  have hp : ((fun e i=>(portions w K D e i:ℝ)) ∘ sourceEdgeEquiv w K)=
        sourcePortions (fun x y=>(w x y:ℝ)) K D := by
    funext e i
    exact portions_cast w K D e i
  rw [hp]
  rfl
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_FiniteStage
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Variation
open Finset

lemma event_instances {A : Type*} (F₁ F₂ : Fintype A) (p : A → ℝ) (D : A → Prop) :
    @event A F₁ p D=@event A F₂ p D := by
  cases Subsingleton.elim F₁ F₂
  rfl
lemma sum_instances {A : Type*} (F₁ F₂ : Fintype A) (p : A → ℝ) :
    (letI:=F₁; ∑ a,p a)=(letI:=F₂; ∑ a,p a) := by
  cases Subsingleton.elim F₁ F₂
  rfl
end MatchingFPRAS.Variation
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance finiteStageSourceLabelDecidableEq_r3ec436_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_4_r3ec436_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeMarked_1
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instFintypeSourceMarkedCastReal_1
lemma source_transfer_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D : ℕ) (hD : 0<D)
    (p : Marked w K → ℝ) :
    tv (p ∘ sourceMarkedEquiv w K) (sourceLaw (fun x y=>(w x y:ℝ)) K D)=tv p (markedLaw w K D) := by
  have he : sourceLaw (fun x y=>(w x y:ℝ)) K D=markedLaw w K D ∘ sourceMarkedEquiv w K := by
    funext a
    exact (markedLaw_equiv w hw K D hD a).symm
  rw [he]
  exact tv_equiv (sourceMarkedEquiv w K) p (markedLaw w K D)

noncomputable local instance instFintypeProdForallFinBoolForallBagEdgeSourceVertexLabelBags_r3ec436_1 (w : V → V → ℚ) (K t k : ℕ) :
    Fintype ((Fin t → Bool) × (BagEdge (bags w K) → Fin k → Bool)) := Fintype.ofFinite _
theorem finiteSourceLaw_tv (w : V → V → ℚ) (hw : ∀ x y,0<w x y) (K D m : ℕ) (hD : 1≤D)
    (hN : 2≤Fintype.card (SourceVertex V K)) (hm : 1 < m)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<Transport.ladderQ (Fintype.card (SourceVertex V K)) D) (M : BagPM (bags w K)) (η : ℚ) (hη : 0<η) :
    tv (finiteSourceLaw w hw K D m (lt_of_lt_of_le Nat.zero_lt_one hD) (lt_of_lt_of_le Nat.zero_lt_two hN) h hq M η)
      (sourceLaw (fun x y=>(w x y:ℝ)) K D)≤2*(η:ℝ)+(m:ℝ)⁻¹ := by
  rw [finiteSourceLaw,source_transfer_tv w hw K D (by omega)]
  exact markedSampler_tv w hw K D m hD hN hm h hq M η hη

lemma sampling_denominator_gt (T S : ℕ) (hT : 0<T) (hS : 0<S) : 1<1000*T*S := by
  have ht : 1≤T := hT
  have hs : 1≤S := hS
  nlinarith
lemma sampling_budget (T S : ℕ) (_hT : 0<T) (_hS : 0<S) :
    2*((1/(1000*T*S):ℚ):ℝ)+((1000*T*S:ℕ):ℝ)⁻¹=3/(1000*T*S) := by
  push_cast
  ring

attribute [local instance] OAI.MatchingFPRAS.RationalSource.finiteStageSourceBagEdgeFintype
theorem finite_source_stage_budget (w : V → V → ℚ) (hw : ∀ x y,0<w x y)
    (w₁ : V → V → ℝ) (hw₁ : ∀ x y,0≤w₁ x y)
    (hle : ∀ x y,x≠y → w₁ x y ≤ (w x y:ℝ))
    (hz : 0<Switching.partition (fun x y=>(w x y:ℝ)) ∅)
    (K T S : ℕ) (hT : 0<T) (hS : 0<S) (σ : ℝ) (hσ : 0≤σ)
    (hsize : 10*((Fintype.card V:ℝ)+T+1) ≤ (S:ℝ)*σ^2)
    (h : ∀ x y,x≠y → BottleneckAlgorithm.edge w x y≤(4:ℚ)^K)
    (hq : 0<ladderQ (Fintype.card (SourceVertex V K)) (sourceD (V:=V) K))
    (M : BagPM (bags w K)) :
    let p := finiteSourceLaw w hw K (sourceD (V:=V) K) (1000*T*S)
      (sourceD_one K) Fintype.card_pos h hq M (1/(1000*T*S))
    Variation.event (Variation.iid p S)
      (fun x=>¬StageGood (fun x y=>(w x y:ℝ)) w₁ K σ x)<13/(1000*T) := by
  dsimp only
  have hN : 2≤Fintype.card (SourceVertex V K) :=
    (Fintype.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial V)).trans_le (sourceVertex_card_ge K)
  let p := finiteSourceLaw w hw K (sourceD (V:=V) K) (1000*T*S)
    (sourceD_one K) Fintype.card_pos h hq M (1/(1000*T*S))
  have hv := finiteSourceLaw_tv w hw K (sourceD (V:=V) K) (1000*T*S) (sourceD_one K)
    hN (sampling_denominator_gt T S hT hS) h hq M (1/(1000*T*S)) (by positivity)
  rw [sampling_budget T S hT hS] at hv
  have hh:=source_nearby_budget (fun x y=>(w x y:ℝ)) w₁
    (fun x y=>by exact_mod_cast hw x y) hw₁ hle hz K T S hT hS σ hσ hsize p
    (finiteSourceLaw_nonneg w hw K _ _ _ _ h hq M _) ?_ ?_
  · rw [event_instances _ (inferInstance : Fintype (Fin S → SourceMarked (fun x y=>(w x y:ℝ)) K))] at hh
    exact hh
  · rw [sum_instances _ (inferInstance : Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K))]
    exact finiteSourceLaw_sum w hw K _ _ _ _ h hq M _
  · rw [tv_instances _ (inferInstance : Fintype (SourceMarked (fun x y=>(w x y:ℝ)) K))]
    exact hv
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_FiniteTrialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Switching Transport Enlargement Adaptive
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder

noncomputable local instance finiteTrialLawSourceLabelDecidableEq_r3ec436_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
attribute [local instance] OAI.MatchingFPRAS.FiniteTrial.instFintypeSourceMarkedFinNCastReal
theorem ScaleState.sampleLaw_budget_oai (p : Trial.Parameters G) {j : ℕ} (hj : j≤p.K) (s : ScaleState G j) :
    (s.sampleLaw p hj).event
      (fun x=>¬StageGood (fun a b=>(s.activity a b:ℝ)) (fun a b=>(s.nextActivity a b:ℝ)) p.K p.sigma x)
      <13/(1000*p.K) := by
  have h:=RationalSource.finite_source_stage_budget s.activity s.activity_pos
    (fun a b=>(s.nextActivity a b:ℝ))
    (fun a b=>by exact_mod_cast (s.nextActivity_pos a b).le)
    (fun a b _=>by have h:=(s.toReal.cooling a b).2; rw [←s.activity_cast,←s.nextActivity_cast] at h; exact h)
    (by rw [s.activity_cast]; exact s.toReal.partition_pos p.even)
    p.K p.K p.S p.K_pos p.S_pos p.sigma p.sigma_pos.le (by simpa using p.S_bound)
    (s.cap hj) p.q_pos (RationalSource.startMatching s.activity p.K p.even)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold ScaleState.sampleLaw ScaleState.runLaw Law.event Law.iid Variation.event
  rfl
end MatchingFPRAS.FiniteTrial

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.FiniteTrial.ScaleState.sampleLaw_budget_oai := @OAI.MatchingFPRAS.FiniteTrial.ScaleState.sampleLaw_budget_oai
