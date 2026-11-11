-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:56:53.128659+00:00
-- url     : https://prove2.me/submissions/dd580054-70bc-48ad-b546-8418644c9377

import Mathlib
import Definitions.Def_Q238K031
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_initialHistory_spec_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_HistoryCompatibleCertificate_compatible_certificate_s238

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

omit [DecidableEq X] in
lemma exact_opening_eta {loc : D → X} {F W : Finset X} {v z lam eta : ℝ} {i : X}
    (h : etaOpenable loc F W (1-3*v) (1+v^2) v z lam 0 i) (heta : 0 ≤ eta) :
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i := by
  obtain ⟨tau,hb,hp,hd⟩ := h
  refine ⟨tau,hb,?_,hd⟩
  have hn : 0 ≤ (Fintype.card D:ℝ)*eta := mul_nonneg (Nat.cast_nonneg _) heta
  simp only [mul_zero,sub_zero] at hp
  exact (sub_le_self lam hn).trans hp

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

lemma advance_rows (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q : ℕ)
    (H : List X) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hhead : PhaseSequence.Valid loc F B Q v ((1+v^2)^q) lam eta H) :
    ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^(q+1)) (Q ∪ H.toFinset) i ≤ lam := by
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have hrow' : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) (Q ∪ H.toFinset) i ≤ lam := by
    intro i hi
    exact (bidRow_antitone_open loc (1-3*v) ((1+v^2)^q) Q (Q ∪ H.toFinset) i ht
      Finset.subset_union_left).trans (hrow i hi)
  have hz : 0 < (1+v^2)^q := by positivity
  simpa only [pow_succ,mul_comm] using
    phase_update_no_overbid loc F (Q ∪ H.toFinset) v ((1+v^2)^q) lam
      hv hvsmall hz hlam hrow' hhead.2

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_EntryFreeMono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeSurgery
open PhaseSequence
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma prefix_exact_eta {loc : D → X} {F B Q : Finset X} {v z lam eta : ℝ}
    {H : List X} (h : Prefix loc F B v z lam 0 Q H) (heta : 0 ≤ eta) :
    Prefix loc F B v z lam eta Q H := by
  induction h with
  | nil Q => exact Prefix.nil Q
  | cons hi ht ih =>
    refine Prefix.cons ⟨hi.1,?_⟩ ih
    rcases hi.2 with hi | ⟨hi,W,hW,hWF,hop⟩
    · exact Or.inl hi
    · exact Or.inr ⟨hi,W,hW,hWF,exact_opening_eta hop heta⟩

end MetricKMedianRecovery.PhaseMergeSurgery

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
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_PrefixFreeMono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CommonPrefixTransfer
open PhaseHistoryTransfer FreshCopyEndpoints
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma history_rows (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q : ℕ) (T : List (List X)) (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam)
    (hrow : ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^q) Q i ≤ lam)
    (hh : History loc F B v lam eta q Q T) :
    ∀ i ∈ F, bidRow loc (1-3*v) ((1+v^2)^(q+T.length)) (after Q T) i ≤ lam := by
  induction hh with
  | nil q Q => simpa only [List.length_nil,Nat.add_zero,after] using hrow
  | @cons q Q H T hhead htail ih =>
    have hr := ih (advance_rows loc F B Q v lam eta q H hv hvsmall hlam hrow hhead)
    simpa only [after,List.length_cons,Nat.add_right_comm,Nat.add_assoc] using hr

lemma history_append (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ)
    (q : ℕ) (P T : List (List X)) (hp : History loc F B v lam eta q Q P)
    (ht : History loc F B v lam eta (q+P.length) (after Q P) T) :
    History loc F B v lam eta q Q (P++T) := by
  induction hp with
  | nil q Q => simpa only [List.nil_append,List.length_nil,Nat.add_zero,after] using ht
  | @cons q Q H P hhead htail ih =>
    apply History.cons hhead
    apply ih
    simpa only [after,List.length_cons,Nat.add_right_comm,Nat.add_assoc] using ht

end MetricKMedianRecovery.CommonPrefixTransfer

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

lemma history_exact_eta {loc : D → X} {F B Q : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : History loc F B v lam 0 q Q P) (heta : 0 ≤ eta) :
    History loc F B v lam eta q Q P := by
  induction h with
  | nil => exact History.nil _ _
  | cons hhead htail ih =>
    exact History.cons ⟨PhaseMergeSurgery.prefix_exact_eta hhead.1 heta,hhead.2⟩ ih

lemma PrefixData.after_subset {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P) :
    after ∅ P ⊆ F ∪ B := h.history.after_subset (Finset.empty_subset _)

lemma PrefixData.append_exact {loc : D → X} {F B : Finset X} {v lam eta : ℝ}
    {q : ℕ} {P : List (List X)} (h : PrefixData loc F B v lam eta q P)
    (hv : 0 < v) (hvsmall : v < 1/6) (hlam : 0 < lam) (heta : 0 ≤ eta)
    (T : List (List X)) (hh : History loc F B v lam 0 q (after ∅ P) T)
    (hreg : Regular F T) : PrefixData loc F B v lam eta (q+T.length) (P++T) := by
  refine ⟨by simp only [List.length_append,h.length_eq],?_,?_,?_⟩
  · apply CommonPrefixTransfer.history_append loc F B ∅ v lam eta 0 P T h.history
    simpa only [Nat.zero_add,h.length_eq] using history_exact_eta hh heta
  · intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · exact h.free_bound H hH
    · have hs : H.toFinset ⊆ F := fun i hi => hreg H hH i (List.mem_toFinset.mp hi)
      simp only [Finset.sdiff_eq_empty_iff_subset.mpr hs,Finset.card_empty,Nat.zero_le]
  · rw [after_append]
    exact CommonPrefixTransfer.history_rows loc F B (after ∅ P) v lam 0 q T
      hv hvsmall hlam h.row hh

end MetricKMedianRecovery.PhaseMergeInvariant

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialRows
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseInitialBracket
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma empty_prefix (loc : D → X) (F B : Finset X) (v lam eta : ℝ) (hlam : 0 ≤ lam)
    (hfar : ∀ i ∈ F, ∀ j, 1 ≤ dist i (loc j)) :
    PrefixData loc F B v lam eta 0 [] := by
  refine ⟨rfl,History.nil _ _,by simp,?_⟩
  intro i hi
  have he : bidRow loc (1-3*v) ((1+v^2)^0) ∅ i = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    simp only [clippedAt,Finset.not_nonempty_empty,↓reduceIte,pow_zero]
    exact max_eq_right (by linarith only [hfar i hi j])
  simpa only [after,he] using hlam

end MetricKMedianRecovery.PhaseInitialBracket

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
  exact HistoryCompatibleCertificate.compatible_certificate_s238 loc F B v lam eta P hdis
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CanonicalParents
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.levelWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.parentWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}
omit [LinearOrder V] in
lemma rooted_empty (F : Finset V) : Rooted F ∅ := by intro x hx; simp at hx
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

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialAuto
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant PhaseMergeCertificate HistoryPhaseBound
variable {V : Type*} [LinearOrder V] {d : ℕ}
lemma start_small_eq (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v lo M : ℚ) (N precision total k : ℕ) (o : Output V)
    (he : start loc distance F v lo M N precision total k=.small o) :
    o=finish ∅ lo [] (initialHistory loc distance F v lo total) ∧
      initialCount loc distance F v lo total≤k := by
  simp only [start] at he
  split at he
  next hc => exact ⟨(StartOutput.small.inj he).symm,hc⟩
  next => split at he <;> first | contradiction | (split at he <;> contradiction)
variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric
lemma start_small_certificate_s238_oai (loc : Fin d→V) (distance : V→Fin d→ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lo M : ℚ) (N precision k : ℕ) (o : Output V)
    (he : start loc distance F v lo M N precision
      (limit v ((M:ℝ)+8*(d:ℝ)*(M:ℝ))+1) k=.small o)
    (hd : 0<d) (hF : F.Nonempty) (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6)
    (hlo : 0<lo) (hM : 0<M) (hlohi : lo≤8*(d:ℚ)*M)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    o.project⊆F ∧ o.project.Nonempty ∧ o.project.card≤k ∧
    ∃ (Q : ℝ) (alpha : Fin d→ℝ), 0≤Q ∧ (∑ j,nearestDistance (loc j) o.project)≤Q ∧
      PhaseOriginalLedger.Dual loc F v lo alpha ∧ (1-3*(v:ℝ))*Q≤∑ j,alpha j := by
  let total := limit v ((M:ℝ)+8*(d:ℝ)*(M:ℝ))+1
  obtain ⟨rfl,hcount⟩:=start_small_eq loc distance F v lo M N precision total k o he
  have hfar' : ∀ x∈F.image original,∀ j,1≤dist x (original (loc j)) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hfar i hi j
  have hdiam' : ∀ x∈F.image original,∀ j,dist x (original (loc j))≤(M:ℝ) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hdiam i hi j
  have hloR : (0:ℝ)<lo := by exact_mod_cast hlo
  have hhi : (lo:ℝ)≤8*(d:ℝ)*(M:ℝ) := by exact_mod_cast hlohi
  have hZ : 0<(M:ℝ)+8*(d:ℝ)*(M:ℝ) := by exact_mod_cast (show 0<M+8*(d:ℚ)*M by positivity)
  have ht:=initialHistory_spec_s238 loc distance hmetric F v lo total hv hv1
  have hp0:=PhaseInitialBracket.empty_prefix (fun j=>original (loc j)) (F.image original) ∅
    (v:ℝ) (lo:ℝ) 0 hloR.le hfar'
  have hp : PrefixData (fun j=>original (loc j)) (F.image original) ∅ v lo 0 total
      (initialHistory loc distance F v lo total) := by
    have hh:=hp0.append_exact hv hv1 hloR le_rfl _ ht.2.1 ht.2.2
    simpa only [ht.1,Nat.zero_add,List.nil_append] using hh
  have hterm:=PhaseTerminalProducer.terminal_prefix (hF.image original) hv hv1 hdiam' hZ (by linarith only [hhi]) hp
  have hQF : after ∅ (initialHistory loc distance F v lo total)⊆F.image original := by
    simpa only [Finset.union_empty] using hp.after_subset
  have hne : (after ∅ (initialHistory loc distance F v lo total)).Nonempty := by
    by_contra hn
    have hh:=hterm ⟨0,hd⟩
    apply hh
    intro f hf
    rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hf
    exact False.elim (Finset.notMem_empty f hf)
  obtain ⟨alpha,hpos,hdual,hpay,hstrict⟩:=certify (hF.image original) (Finset.disjoint_empty_right _) hv hv1 hloR
    hfar' hdiam' hZ hhi hp
  refine ⟨project_subset F ∅ _ (rooted_empty F) hp.after_subset,project_nonempty hne,?_,
    ∑ j,nearestDistance (original (loc j)) (after ∅ (initialHistory loc distance F v lo total)),alpha,
    Finset.sum_nonneg (fun j _=>nearestDistance_nonneg _ _),?_,?_,?_⟩
  · change (RationalLeaves.project (after ∅ ([]++initialHistory loc distance F v lo total))).card≤k
    rw [List.nil_append]
    exact (project_card _).trans (by simpa only [initialCount,Finset.inter_eq_left.mpr hQF] using hcount)
  · exact Finset.sum_le_sum (fun j _=>project_distance (loc j) _)
  · refine ⟨hpos,?_,?_⟩
    · intro i hi
      simpa only [original_dist] using hdual (original i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    · intro C hC i hi b hb hP hlp hsmall
      have hP' : 0<∑ j∈C,dist (original i) (original (loc j)) := by simpa only [original_dist] using hP
      have hlp' : (lo:ℝ)≤b*(∑ j∈C,dist (original i) (original (loc j))) := by
        simpa only [original_dist] using hlp
      simpa only [original_dist] using hstrict C hC (original i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩) b hb hP' hlp' hsmall
  · simp only [mul_zero,sub_zero] at hpay
    have hh : (0:ℝ)≤(((after ∅ (initialHistory loc distance F v lo total)∩F.image original).card):ℝ)*(lo:ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) hloR.le
    linarith only [hpay,hh]
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_small_certificate_s238_oai.{u_1}
