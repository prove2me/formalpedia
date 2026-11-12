-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:40:35.955865+00:00
-- url     : https://prove2.me/submissions/dbf1e871-8a55-4bcc-a8ec-03d1c224a043

import Mathlib
import Definitions.Def_Q238L026
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_start_correct_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_start_small_certificate_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_HistoryCompatibleCertificate_compatible_certificate_s238r

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery

lemma nearestDistance_nonneg {X : Type*} [PseudoMetricSpace X]
    (x : X) (S : Finset X) : 0 ≤ nearestDistance x S := by
  classical
  unfold nearestDistance
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => dist_nonneg)
  · exact le_rfl

end MetricKMedianRecovery

end OAI
end

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ImagePhaseUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma History.after_subset {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {T : List (List X)} (h : History loc F B v lam eta q Q T)
    (hQ : Q ⊆ F ∪ B) : after Q T ⊆ F ∪ B := by
  induction h with
  | nil => exact hQ
  | cons hhead htail ih =>
    exact ih (Finset.union_subset hQ hhead.1.opened_subset)

end MetricKMedianRecovery.PhaseHistoryTransfer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_BudgetBound
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.UniformRowDisabling
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [DecidableEq X] in

lemma budget_bound (loc : D → X) (F Q : Finset X) (hF : F.Nonempty)
    (t z lam M : ℝ) (hrow : ∀ i ∈ F, bidRow loc t z Q i ≤ lam)
    (hM : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (j : D) :
    clippedAt loc t z Q j ≤ M+lam := by
  obtain ⟨i,hi⟩ := hF
  have hsum : max (clippedAt loc t z Q j-dist i (loc j)) 0 ≤ bidRow loc t z Q i :=
    Finset.single_le_sum (fun a _ => le_max_right (clippedAt loc t z Q a-dist i (loc a)) 0)
      (Finset.mem_univ j)
  have hh := (le_max_left (clippedAt loc t z Q j-dist i (loc j)) 0).trans (hsum.trans (hrow i hi))
  linarith only [hh,hM i hi j]

end MetricKMedianRecovery.UniformRowDisabling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Live
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.HistoryPhaseBound
open PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma limit_threshold (v Z : ℝ) (hv : 0 < v) (hZ : 0 < Z) :
    Z < (1+v^2)^(limit v Z) := by
  have hK : 1 < 1+v^2 := by nlinarith
  have hlog := Real.log_pos hK
  have hceil := Nat.le_ceil (Real.log Z / Real.log (1+v^2))
  have hq : Real.log Z / Real.log (1+v^2) < (limit v Z : ℝ) := by
    simp only [limit,Nat.cast_add,Nat.cast_one]
    linarith
  have hmul := (div_lt_iff₀ hlog).mp hq
  apply (Real.log_lt_log_iff hZ (pow_pos (by positivity : 0 < 1+v^2) _)).mp
  simpa only [Real.log_pow] using hmul

omit [Fintype D] [PseudoMetricSpace X] in

theorem free_count (F Q : Finset X) (T : List (List X)) (b : ℕ)
    (hb : ∀ H ∈ T, (H.toFinset \ F).card ≤ b) :
    (after Q T \ F).card ≤ (Q \ F).card+b*T.length := by
  induction T generalizing Q with
  | nil => simp [after]
  | cons H T ih =>
    have ht := ih (Q ∪ H.toFinset) (fun G hG => hb G (List.mem_cons_of_mem H hG))
    have hH := hb H (List.mem_cons_self)
    have hs : ((Q ∪ H.toFinset) \ F).card ≤ (Q \ F).card+(H.toFinset \ F).card := by
      rw [Finset.union_sdiff_distrib]
      exact Finset.card_union_le _ _
    simp only [after,List.length_cons]
    calc
      (after (Q ∪ H.toFinset) T \ F).card ≤ ((Q ∪ H.toFinset) \ F).card+b*T.length := ht
      _ ≤ (Q \ F).card+b+b*T.length := by omega
      _ = (Q \ F).card+b*(T.length+1) := by ring

end MetricKMedianRecovery.HistoryPhaseBound

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

lemma original_distance (root : C → V) (u : C → ℝ) (x y : V) :
    leafDist root u (.inl x) (.inl y) = dist x y := by
  by_cases h : x = y
  · subst y; simp [leafDist_self]
  · simp [leafDist,h,height,parent]
lemma copy_distance (root : C → V) (u : C → ℝ) (x : V) (c : C) :
    leafDist root u (.inl x) (.inr c) = dist x (root c)+u c := by
  simp [leafDist,height,parent]

end MetricKMedianRecovery.LeafMetric

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

lemma PrefixData.after_subset {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P) :
    after ∅ P ⊆ F ∪ B := h.history.after_subset (Finset.empty_subset _)

end MetricKMedianRecovery.PhaseMergeInvariant

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_TerminalPrefix
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseTerminalProducer
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant HistoryPhaseBound
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma terminal_prefix {loc : D → X} {F B : Finset X} {v lam eta M Z : ℝ}
    {P : List (List X)} (hF : F.Nonempty) (hv : 0 < v) (hvsmall : v < 1/6)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < Z) (hbound : M+lam ≤ Z)
    (hp : PrefixData loc F B v lam eta (limit v Z+1) P) :
    ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^(limit v Z)) (after ∅ P) j := by
  intro j ha
  have he := clippedAt_of_active loc (1-3*v) ((1+v^2)^(limit v Z)) (after ∅ P) j
    (by linarith only [hvsmall]) ha
  have hpow : (1+v^2)^(limit v Z) ≤ (1+v^2)^(limit v Z+1) :=
    pow_le_pow_right₀ (by nlinarith only [sq_nonneg v]) (Nat.le_succ _)
  have hm := clippedAt_mono_phase loc (1-3*v) (after ∅ P) j hpow
  have hb := UniformRowDisabling.budget_bound loc F (after ∅ P) hF (1-3*v)
    ((1+v^2)^(limit v Z+1)) lam M hp.row hdiam j
  dsimp only at hm
  rw [he] at hm
  exact (not_lt_of_ge ((hm.trans hb).trans hbound)) (limit_threshold v Z hv hZ)

lemma terminal_next {loc : D → X} {F B : Finset X} {v lam eta M Z : ℝ}
    {P : List (List X)} (hF : F.Nonempty) (hv : 0 < v) (hvsmall : v < 1/6)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < Z) (hbound : M+lam ≤ Z)
    (hp : PrefixData loc F B v lam eta (limit v Z+1) P) :
    ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^P.length) (after ∅ P) j := by
  intro j ha
  apply terminal_prefix hF hv hvsmall hdiam hZ hbound hp j
  intro f hf
  have hh := ha f hf
  rw [hp.length_eq] at hh
  exact lt_of_le_of_lt (pow_le_pow_right₀ (by nlinarith only [sq_nonneg v]) (Nat.le_succ _)) hh

lemma copies_bound {loc : D → X} {F B : Finset X} {v lam eta : ℝ} {q : ℕ}
    {P : List (List X)} (hp : PrefixData loc F B v lam eta q P) :
    (after ∅ P \ F).card ≤ 3*q := by
  have h := free_count F ∅ P 3 hp.free_bound
  simpa only [Finset.empty_sdiff,Finset.card_empty,zero_add,hp.length_eq] using h

end MetricKMedianRecovery.PhaseTerminalProducer

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Algorithms_FinalBudgetPos
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeCertificate
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant
  PhaseTerminalProducer HistoryPhaseBound
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma certify {loc : D → X} {F B : Finset X} {v lam eta M hi : ℝ}
    {P : List (List X)} (hF : F.Nonempty) (hdis : Disjoint F B)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j))
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < M+hi) (hu : lam ≤ hi)
    (hp : PrefixData loc F B v lam eta (limit v (M+hi)+1) P) :
    Budget loc F (after ∅ P) v lam eta := by
  exact HistoryCompatibleCertificate.compatible_certificate_s238r loc F B v lam eta P hdis
    (fun j i hi => hfar i hi j) hp.history
    (terminal_next hF hv hvsmall hdiam hZ (by linarith only [hu]) hp) hv hvsmall hlam

end MetricKMedianRecovery.PhaseMergeCertificate

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalLeaves
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [PseudoMetricSpace V]

attribute [local instance] metric

lemma original_dist (i j : V) :
    dist (original i) (original j)=dist i j := LeafMetric.original_distance root height i j

lemma leaf_dist (i j : V) (key : ℕ) (s : ℚ) :
    dist (original i) (leaf key j s)=dist i j+(max s 0:ℚ) :=
  LeafMetric.copy_distance root height i (key,j,s)

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FiniteCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalLengthView
open PhaseSequence PhaseMergeRefinement CanonicalMergeRefinement PhaseCountCrossing
variable {X : Type*} [DecidableEq X] {d : ℕ}

lemma view_sound (distance : X → Fin d → ℚ) (F : Finset X) (R H G : List X) (J : Plan X)
    (h : view distance F R H G=some J) : accepts distance F H G J :=
  of_decide_eq_true (List.find?_some (p := fun J=>decide (accepts distance F H G J)) h)

end MetricKMedianRecovery.CanonicalLengthView

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_MergeResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
open RationalHeight
variable {V : Type*} [DecidableEq V]

lemma parent_shorten (key : ℕ) (i : V) (l u : ℚ) (x : Label V) :
    parent (shorten key i l u x)=parent x := by
  simp only [shorten,Equiv.swap_apply_def]
  split_ifs with hu hl
  · subst x; rfl
  · subst x; rfl
  · rfl

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CanonicalParents
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.levelWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.parentWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalLeaves
variable {V : Type*} [DecidableEq V]
omit [DecidableEq V] in
lemma parent_original (i : V) : parent (original i)=i := rfl
omit [DecidableEq V] in
lemma parent_copy (key : ℕ) (x : Label V) : parent (copy key x)=parent x := by cases x <;> rfl
end MetricKMedianRecovery.RationalLeaves
namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}
omit [LinearOrder V] in
lemma rooted_empty (F : Finset V) : Rooted F ∅ := by intro x hx; simp at hx
lemma correction_parent (c : Correction V) (x : Label V) : parent (c.apply x)=parent x := by
  cases c with
  | identity => rfl
  | shorten key i l u => exact parent_shorten key i l u x
lemma rooted_mapFree (F : Finset V) (s : State V) (h : Rooted F s.B) : Rooted F s.mapFree := by
  intro x hx
  obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
  rw [correction_parent]
  exact h y hy
lemma rooted_pool (F : Finset V) (B : Finset (Label V)) (key : ℕ) (h : Rooted F B) :
    Rooted F (PhaseMergePath.pool (F.image original) B (copy key)) := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx|hx
  · exact h x hx
  · obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hy
    simpa only [parent_copy,parent_original] using hi
lemma rooted_banks (F : Finset V) (B : Finset (Label V)) (q : ℕ) (h : Rooted F B) :
    Rooted F (banks F B q) := rooted_pool F _ _ (rooted_pool F B _ h)
lemma rooted_insert (F : Finset V) (B : Finset (Label V)) (key : ℕ) (i : V) (s : ℚ)
    (h : Rooted F B) (hi : i∈F) : Rooted F (insert (leaf key i s) B) := by
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl|hx
  · exact hi
  · exact h x hx

lemma resolve_rooted (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k key : ℕ) (B : Finset (Label V)) (lam : ℚ)
    (P : List (List (Label V))) (R : CanonicalMergeCrossing.Result (Label V)) (h : Rooted F B) :
    (resolve loc distance F v M N precision q n k key B lam P R).Rooted F := by
  cases R with
  | success H T => exact h
  | common H T U => exact h
  | sensitive H G T U =>
    simp only [resolve]
    split
    next he => exact h
    next J he =>
      have hj:=view_sound (rows distance) (F.image original) ((F.sort (·≤·)).map original) H G J he
      have hr : J.root∈F.image original := by cases J <;> exact hj.1
      obtain ⟨i,hi,hiJ⟩:=Finset.mem_image.mp hr
      have hp : parent J.root∈F := by rw [←hiJ,parent_original]; exact hi
      split <;> exact rooted_insert F B key (parent J.root) _ h hp
lemma step_rooted (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision q n k : ℕ) (s : State V) (h : Rooted F s.B) :
    (step loc distance F v M N precision q n k s).Rooted F := by
  unfold step
  split
  next H T G U hT hU =>
    dsimp only
    split
    · exact rooted_mapFree F s h
    · split
      · exact resolve_rooted loc distance F v M N precision q n k _ _ _ _ _
          (rooted_banks F s.mapFree q (rooted_mapFree F s h))
      · exact h
  next => exact h
lemma run_rooted (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k q n : ℕ) (s : State V) (h : Rooted F s.B) :
    Rooted F (run loc distance F v M N precision k q n s).B := by
  induction n generalizing q s with
  | zero => exact h
  | succ n ih =>
    have hs:=step_rooted loc distance F v M N precision q n k s h
    rw [run]
    split
    next o he => rw [he] at hs; exact hs
    next t he => rw [he] at hs; exact ih (q+1) t hs

lemma start_rooted (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v lo M : ℚ) (N precision total k : ℕ) :
    (start loc distance F v lo M N precision total k).Rooted F := by
  simp only [start]
  split
  · exact rooted_empty F
  · split
    · exact rooted_empty F
    · split
      · exact rooted_empty F
      · exact run_rooted loc distance F v M N precision k 0 total _ (rooted_empty F)
end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.RationalLeaves
open PhaseSequence
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]
attribute [local instance] RationalLeaves.metric

omit [PseudoMetricSpace V] in
lemma project_nonempty {Q : Finset (Label V)} (hQ : Q.Nonempty) : (project Q).Nonempty := hQ.image parent
omit [PseudoMetricSpace V] in
lemma project_card (Q : Finset (Label V)) : (project Q).card≤Q.card := Finset.card_image_le
omit [DecidableEq V] in
lemma parent_distance (j : V) (x : Label V) : dist j (parent x)≤dist (original j) x := by
  cases x with
  | inl i => exact (original_dist j i).ge
  | inr c =>
    change dist j c.2.1≤dist (original j) (leaf c.1 c.2.1 c.2.2)
    rw [leaf_dist]
    have hh : (0:ℝ)≤(max c.2.2 0:ℚ) := by exact_mod_cast le_max_right c.2.2 0
    linarith
lemma project_distance (j : V) (Q : Finset (Label V)) :
    nearestDistance j (project Q)≤nearestDistance (original j) Q := by
  by_cases hQ : Q.Nonempty
  · obtain ⟨x,hx,he⟩:=nearestDistance_attained (original j) Q hQ
    exact (nearestDistance_le_mem j _ (parent x) (Finset.mem_image.mpr ⟨x,hx,rfl⟩)).trans
      ((parent_distance j x).trans_eq he.symm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hQ]
    simp [project, nearestDistance]
omit [PseudoMetricSpace V] in
lemma project_subset (F : Finset V) (B Q : Finset (Label V))
    (hb : CanonicalCoupledMerge.Rooted F B) (hQ : Q⊆F.image original∪B) : project Q⊆F := by
  intro i hi
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hi
  rcases Finset.mem_union.mp (hQ hx) with hx|hx
  · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hx
    exact hj
  · exact hb x hx
end MetricKMedianRecovery.RationalLeaves
namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves PhaseSequence PhaseHistoryTransfer PhaseMergeInvariant PhaseMergeCertificate HistoryPhaseBound
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

lemma Output.normal_certificate (loc : Fin d→V) (F : Finset V) (v eta lo hi M : ℝ)
    (k : ℕ) (o : Output V) (h : o.Correct loc F v eta lo hi (limit v (M+hi)+1) k)
    (hroot : Rooted F o.B) (hk : 0<k) (hF : F.Nonempty) (hv : 0<v) (hv1 : v<1/6)
    (hlo : 0<lo) (hZ : 0<M+hi)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M) :
    o.project⊆F ∧ o.project.Nonempty ∧ o.project.card≤k+3*(limit v (M+hi)+1) ∧
    ∃ (Q : ℝ) (alpha : Fin d→ℝ), 0≤Q ∧ (∑ j,nearestDistance (loc j) o.project)≤Q ∧
      PhaseOriginalLedger.Dual loc F v o.lam alpha ∧
      (1-3*v)*Q+(k:ℝ)*((o.lam:ℝ)-(d:ℝ)*eta)≤∑ j,alpha j := by
  obtain ⟨hdis,hl,hu,hp,hcount⟩:=h
  have hne : (after ∅ o.P).Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.empty_inter,Finset.card_empty] at hcount
    omega
  have hfar' : ∀ x∈F.image original,∀ j,1≤dist x (original (loc j)) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hfar i hi j
  have hdiam' : ∀ x∈F.image original,∀ j,dist x (original (loc j))≤M := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hdiam i hi j
  obtain ⟨alpha,hpos,hdual,hpay,hstrict⟩:=certify (hF.image original) hdis hv hv1 (hlo.trans_le hl)
    hfar' hdiam' hZ hu hp
  refine ⟨project_subset F o.B _ hroot hp.after_subset,project_nonempty hne,?_,
    ∑ j,nearestDistance (original (loc j)) (after ∅ o.P),alpha,?_,?_,?_,?_⟩
  · have hc:=PhaseTerminalProducer.copies_bound hp
    have he:=Finset.card_inter_add_card_sdiff (after ∅ o.P) (F.image original)
    exact (project_card _).trans (by omega)
  · exact Finset.sum_nonneg (fun j _=>nearestDistance_nonneg _ _)
  · exact Finset.sum_le_sum (fun j _=>project_distance (loc j) _)
  · refine ⟨hpos,?_,?_⟩
    · intro i hi
      simpa only [original_dist] using hdual (original i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · intro C hC i hi b hb hP hlp hsmall
      have hP' : 0<∑ j∈C,dist (original i) (original (loc j)) := by simpa only [original_dist] using hP
      have hlp' : (o.lam:ℝ)≤b*(∑ j∈C,dist (original i) (original (loc j))) := by
        simpa only [original_dist] using hlp
      simpa only [original_dist] using hstrict C hC (original i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩) b hb hP' hlp' hsmall
  · simpa only [hcount,Fintype.card_fin] using hpay
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialProject
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseOriginalLedger HistoryPhaseBound
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {d : ℕ}
lemma start_certificate_s238r_oai (loc : Fin d→V) (distance : V→Fin d→ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lo M : ℚ) (eta : ℝ) (N precision k : ℕ)
    (hd : 0<d) (hdN : d≤N) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hlohi : lo≤8*(d:ℚ)*M) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    let total := limit v ((M:ℝ)+8*(d:ℝ)*M)+1
    let S := (start loc distance F v lo M N precision total k).project
    LowCertificate loc F S v lo k ∨ NormalCertificate loc F S v lo (8*(d:ℝ)*M) eta total k := by
  dsimp only
  let total := limit v ((M:ℝ)+8*(d:ℝ)*M)+1
  cases he : start loc distance F v lo M N precision total k with
  | small o =>
    left
    exact start_small_certificate_s238r loc distance hmetric F v lo M N precision k o he hd hF hv hv1 hlo hM hlohi hfar hdiam
  | normal o =>
    right
    have hc := start_correct_s238r loc distance hmetric F v lo M eta N precision total k
      hd hdN hk hF hM hN hv hv1 hlo heta hlohi hprecision hfar hdiam
    have hr := start_rooted loc distance F v lo M N precision total k
    rw [he] at hc hr
    obtain ⟨hSF,hS,hcard,Q,alpha,hQ,hcost,hdual,hpay⟩ := o.normal_certificate loc F v eta lo (8*(d:ℝ)*M) M k hc hr
      (by omega) hF hv hv1 (by exact_mod_cast hlo) (by positivity) hfar hdiam
    exact ⟨hSF,hS,hcard,o.lam,Q,alpha,hc.2.1,hc.2.2.1,hQ,hcost,hdual,hpay⟩
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238r_oai.{u_1} := @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238r_oai.{u_1}
