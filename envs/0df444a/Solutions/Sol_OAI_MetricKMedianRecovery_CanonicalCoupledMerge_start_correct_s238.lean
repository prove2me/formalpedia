-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_correct_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:54:06.135194+00:00
-- url     : https://prove2.me/submissions/a07538ef-6342-46fd-be9a-e61ffdee0fca

import Mathlib
import Definitions.Def_Q238K031
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_initialHistory_spec_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_step_correct_s238

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

omit [Fintype D] [PseudoMetricSpace X] in
lemma image_phase_union (Q : Finset X) (H : List X) (r : X → X) :
    Q.image r ∪ (H.map r).toFinset = (Q ∪ H.toFinset).image r := by
  ext x
  simp only [Finset.mem_union,Finset.mem_image,List.mem_toFinset,List.mem_map]
  aesop

omit [Fintype D] [PseudoMetricSpace X] in
lemma after_map (Q : Finset X) (T : List (List X)) (r : X → X) :
    after (Q.image r) (T.map (List.map r)) = (after Q T).image r := by
  induction T generalizing Q with
  | nil => rfl
  | cons H T ih =>
    simp only [List.map_cons,after,image_phase_union]
    exact ih _

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

omit [Fintype D] [PseudoMetricSpace X] in
lemma paid_image (F Q : Finset X) (r : X → X) (hinj : Function.Injective r)
    (hfix : ∀ i ∈ F, r i = i) :
    (Q.image r ∩ F).card = (Q ∩ F).card := by
  have heq : Q.image r ∩ F = (Q ∩ F).image r := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxQ,hxF⟩ := Finset.mem_inter.mp hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hxQ
      have haeq : r a = a := hinj (hfix (r a) hxF)
      exact Finset.mem_image.mpr ⟨a,Finset.mem_inter.mpr ⟨ha,haeq ▸ hxF⟩,rfl⟩
    · intro hx
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨a,(Finset.mem_inter.mp ha).1,rfl⟩,
        (hfix a (Finset.mem_inter.mp ha).2).symm ▸ (Finset.mem_inter.mp ha).2⟩
  rw [heq,Finset.card_image_of_injective _ hinj]

end MetricKMedianRecovery.PhaseHistoryTransfer

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

end MetricKMedianRecovery.LeafMetric

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

end MetricKMedianRecovery.RationalLeaves

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_MergeCross
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseMergeCompletion
open PhaseSequence PhaseMergeSurgery PhaseHistoryTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma attains_zero {loc : D → X} {F B Q : Finset X} {v lam : ℝ} {q c : ℕ}
    (h : Attains loc F B Q v lam q 0 c) : c = (Q ∩ F).card := by
  obtain ⟨T,hT,_,_,hc⟩ := h
  have he : T = [] := List.length_eq_zero_iff.mp hT
  simpa only [he,after] using hc.symm

end MetricKMedianRecovery.PhaseMergeCompletion

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Coupled
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseCountCrossing PhaseMergeInvariant
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma Coupled.zero_false {loc : D → X} {F : Finset X} {v eta lo hi : ℝ} {q k : ℕ}
    (h : Coupled loc F v eta lo hi q 0 k) : False := by
  have ha := attains_zero h.new_tail
  have hb := attains_zero h.old_tail
  have he := PhaseHistoryTransfer.after_map ∅ h.P h.r
  simp only [Finset.image_empty] at he
  rw [he,paid_image F (after ∅ h.P) h.r h.inj h.fixed] at ha
  have hab : h.a = h.b := ha.trans hb.symm
  have hs := h.sandwich
  unfold Sandwich at hs
  omega

end MetricKMedianRecovery.PhaseCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DisjointPool
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PriceBisection

lemma refine_bounds (count : ℚ → ℕ) (h : ℕ) (a b : ℚ) (hab : a ≤ b) :
    a ≤ (refine count h (a,b)).1 ∧
    (refine count h (a,b)).1 ≤ (refine count h (a,b)).2 ∧
    (refine count h (a,b)).2 ≤ b := by
  dsimp only [refine]
  split_ifs <;> dsimp
  · exact ⟨by linarith, by linarith, le_rfl⟩
  · exact ⟨le_rfl, by linarith, by linarith⟩

lemma refine_width (count : ℚ → ℕ) (h : ℕ) (a b : ℚ) :
    (refine count h (a,b)).2-(refine count h (a,b)).1 = (b-a)/2 := by
  dsimp only [refine]
  split_ifs <;> dsimp <;> ring

lemma refine_bracket (count : ℚ → ℕ) (h : ℕ) (a b : ℚ)
    (ha : h ≤ count a) (hb : count b ≤ h) :
    h ≤ count (refine count h (a,b)).1 ∧ count (refine count h (a,b)).2 ≤ h := by
  dsimp only [refine]
  split_ifs with hm
  · exact ⟨hm,hb⟩
  · exact ⟨ha,(Nat.lt_of_not_ge hm).le⟩

lemma search_spec (count : ℚ → ℕ) (h n : ℕ) (a b : ℚ) (hab : a ≤ b)
    (ha : h ≤ count a) (hb : count b ≤ h) :
    let I := search count h n (a,b)
    a ≤ I.1 ∧ I.1 ≤ I.2 ∧ I.2 ≤ b ∧
      h ≤ count I.1 ∧ count I.2 ≤ h ∧ I.2-I.1 = (b-a)/2^n := by
  induction n generalizing a b with
  | zero =>
    simp only [search,pow_zero,div_one]
    exact ⟨le_rfl,hab,le_rfl,ha,hb,True.intro⟩
  | succ n ih =>
    obtain ⟨hlo,hm,hhi⟩ := refine_bounds count h a b hab
    obtain ⟨hcl,hch⟩ := refine_bracket count h a b ha hb
    obtain ⟨hl',he',hh',hcl',hch',hw'⟩ := ih _ _ hm hcl hch
    refine ⟨hlo.trans hl',he',hh'.trans hhi,hcl',hch',?_⟩
    change (search count h n (refine count h (a,b))).2 -
      (search count h n (refine count h (a,b))).1 = _
    rw [hw',refine_width,pow_succ]
    ring

lemma iterations_precision (a b : ℚ) (N : ℕ) :
    (b-a) / (2:ℚ) ^ iterations a b N ≤ 1 / (2:ℚ)^N := by
  have hwidth : b-a ≤ (2:ℚ)^(Nat.clog 2 (Nat.ceil (b-a))) := by
    exact (Nat.le_ceil (b-a)).trans (by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (Nat.ceil (b-a)))
  unfold iterations
  rw [pow_add]
  apply (div_le_iff₀ (by positivity : (0:ℚ) < 2^N*2^(Nat.clog 2 (Nat.ceil (b-a))))).mpr
  simpa using hwidth

end MetricKMedianRecovery.PriceBisection

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LeafOrder
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [DecidableEq V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma Certified.zero_false {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {q k : ℕ} {s : State V} (h : Certified loc F v eta lo hi q 0 k s) : False :=
  h.coupled.zero_false

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledFinish
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

lemma finish_correct {loc : Fin d → V} {F : Finset V} {B : Finset (Label V)}
    {v eta lo hi : ℝ} {lam : ℚ} {q n k : ℕ} {P T : List (List (Label V))}
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (hv : 0<v) (hv1 : v<1/6) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hd : Disjoint (F.image original) B) (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hT : Runs (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam q n T)
    (hc : ((after (after ∅ P) T)∩F.image original).card=k) :
    (finish B lam P T).Correct loc F v eta lo hi (q+n) k := by
  refine ⟨hd,hl,hu,?_,?_⟩
  · simpa only [hT.1,finish] using hp.append_exact hv hv1 hlam heta T hT.2.1 hT.2.2
  · simpa only [finish,after_append] using hc

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_CoupledLoop
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma run_correct (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision k : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ))
    (q n : ℕ) (s : State V) (h : Certified loc F v eta lo hi q n k s) :
    (run loc distance F v M N precision k q n s).Correct loc F v eta lo hi (q+n) k := by
  induction n generalizing q s with
  | zero => exact h.zero_false.elim
  | succ n ih =>
    have hs:=step_correct_s238 loc distance hmetric F v M eta lo hi N precision q n k s h
      hF hM hN hv hv1 hlo heta hhi hprecision hdiam
    rw [run]
    cases he : step loc distance F v M N precision q n k s with
    | inl o =>
      rw [he] at hs
      exact hs
    | inr t =>
      rw [he] at hs
      have hh := ih (q+1) t hs
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_comm 1 n] using hh

end MetricKMedianRecovery.CanonicalCoupledMerge

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

namespace MetricKMedianRecovery.PhaseUpperBracket
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

omit [DecidableEq X] in
lemma payment_small (loc : D → X) (F W : Finset X) (v z M : ℝ)
    (hv : 0 ≤ v) (hvsmall : v < 1/6) (hM : 0 ≤ M) (hz : z ≤ M)
    (hW : W ⊆ F) (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (i : X) (tau : D → ℝ)
    (hadm : admissibleBids loc (1-3*v) (1+v^2) v z W i tau) :
    openingPayment loc (1-3*v) z W i tau ≤ (Fintype.card D:ℝ)*((1+v^2)*M) := by
  classical
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  have hK : 0 ≤ 1+v^2 := by positivity
  have hKM : M ≤ (1+v^2)*M := by nlinarith only [mul_nonneg (sq_nonneg v) hM]
  unfold openingPayment
  calc
    _ ≤ ∑ _ : D, (1+v^2)*M := by
      apply Finset.sum_le_sum
      intro j _
      apply max_le _ (by positivity)
      have hd := mul_nonneg ht (dist_nonneg : 0 ≤ dist i (loc j))
      split_ifs with ha
      · exact (sub_le_self _ hd).trans ((hadm j ha).2.1.trans (mul_le_mul_of_nonneg_left hz hK))
      · obtain ⟨f,hf⟩ := inactive_nonempty loc (1-3*v) z W j ha
        have hn : nearestDistance (loc j) W ≤ M :=
          (nearestDistance_le_mem (loc j) W f hf).trans (by rw [dist_comm]; exact hdiam f (hW hf) j)
        have hh := mul_le_mul_of_nonneg_right ht1 (nearestDistance_nonneg (loc j) W)
        linarith only [hn,hh,hd,hKM]
    _ = _ := by simp

omit [DecidableEq X] in
lemma small_impossible [Nonempty D] (loc : D → X) (F W : Finset X) (v z M : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hM : 0 < M) (hz : z ≤ M)
    (hW : W ⊆ F) (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (i : X) :
    ¬etaOpenable loc F W (1-3*v) (1+v^2) v z (8*(Fintype.card D:ℝ)*M) 0 i := by
  rintro ⟨tau,hb,hpay,_⟩
  have hp := payment_small loc F W v z M hv.le hvsmall hM.le hz hW hdiam i tau hb
  simp only [mul_zero,sub_zero] at hpay
  have hn : 0 < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  have hv2 : v^2 < 1/36 := by nlinarith
  have hg : (1+v^2)*M < 8*M := by nlinarith
  have hh := mul_lt_mul_of_pos_left hg hn
  nlinarith only [hp,hpay,hh]

omit [DecidableEq X] in
lemma inactive_impossible [Nonempty D] (loc : D → X) (F W : Finset X) (v z M : ℝ)
    (hv : 0 ≤ v) (hvsmall : v < 1/6) (hM : 0 < M) (hz : M ≤ z)
    (hne : W.Nonempty) (hW : W ⊆ F)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (i : X) :
    ¬etaOpenable loc F W (1-3*v) (1+v^2) v z (8*(Fintype.card D:ℝ)*M) 0 i := by
  classical
  rintro ⟨tau,_,hpay,_⟩
  have ht : 0 ≤ 1-3*v := by linarith only [hvsmall]
  have ht1 : 1-3*v ≤ 1 := by linarith only [hv]
  have hnear : ∀ j, nearestDistance (loc j) W ≤ M := by
    intro j
    obtain ⟨f,hf⟩ := hne
    exact (nearestDistance_le_mem (loc j) W f hf).trans (by rw [dist_comm]; exact hdiam f (hW hf) j)
  have hact : ∀ j, ¬activeAt loc (1-3*v) z W j := by
    intro j ha
    have hh := ((activeAt_iff loc (1-3*v) z W j ht hne).mp ha)
    have hh' := mul_le_mul_of_nonneg_right ht1 (nearestDistance_nonneg (loc j) W)
    linarith only [hz,hh,hh',hnear j]
  have hp : openingPayment loc (1-3*v) z W i tau ≤ (Fintype.card D:ℝ)*M := by
    unfold openingPayment
    calc
      _ ≤ ∑ _ : D, M := by
        apply Finset.sum_le_sum
        intro j _
        rw [ite_eq_right (hact j)]
        apply max_le _ hM.le
        have hh := mul_le_mul_of_nonneg_right ht1 (nearestDistance_nonneg (loc j) W)
        have hd := mul_nonneg ht (dist_nonneg : 0 ≤ dist i (loc j))
        linarith only [hh,hd,hnear j]
      _ = _ := by simp
  have hn : 0 < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  simp only [mul_zero,sub_zero] at hpay
  nlinarith only [hpay,hp,mul_pos hn hM]

lemma prefix_invariant [Nonempty D] (loc : D → X) (F Q : Finset X) (v z M : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hM : 0 < M)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (hQ : Q ⊆ F) (hc : Q.card ≤ 1) (hz : Q.Nonempty → M ≤ z)
    (H : List X) (h : Prefix loc F ∅ v z (8*(Fintype.card D:ℝ)*M) 0 Q H) :
    (Q ∪ H.toFinset) ⊆ F ∧ (Q ∪ H.toFinset).card ≤ 1 ∧
      ((Q ∪ H.toFinset).Nonempty → M ≤ z) := by
  induction h with
  | nil => simpa using And.intro hQ (And.intro hc hz)
  | @cons Q i H hi htail ih =>
    have hentry : i ∈ F ∧ ∃ W : Finset X, Q ⊆ W ∧ W ⊆ F ∧
        etaOpenable loc F W (1-3*v) (1+v^2) v z (8*(Fintype.card D:ℝ)*M) 0 i := by
      simpa only [Finset.notMem_empty,Finset.union_empty,false_or] using hi.2
    obtain ⟨hiF,W,hQW,hWF,hop⟩ := hentry
    have hz' : M < z := lt_of_not_ge (fun hz' => small_impossible loc F W v z M hv hvsmall hM hz' hWF hdiam i hop)
    have he : Q = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact inactive_impossible loc F W v z M hv.le hvsmall hM (hz ⟨x,hx⟩)
        ⟨x,hQW hx⟩ hWF hdiam i hop
    have hh := ih (Finset.insert_subset hiF hQ) (by simp [he]) (fun _ => hz'.le)
    simpa only [List.toFinset_cons,Finset.union_insert,Finset.insert_union] using hh

lemma history_invariant [Nonempty D] (loc : D → X) (F : Finset X) (v M : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hM : 0 < M)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M)
    (q : ℕ) (Q : Finset X) (hQ : Q ⊆ F) (hc : Q.card ≤ 1)
    (hz : Q.Nonempty → M ≤ (1+v^2)^q) (T : List (List X))
    (h : History loc F ∅ v (8*(Fintype.card D:ℝ)*M) 0 q Q T) :
    (after Q T) ⊆ F ∧ (after Q T).card ≤ 1 := by
  induction h with
  | nil => exact ⟨hQ,hc⟩
  | @cons q Q H T hhead htail ih =>
    obtain ⟨hsub,hcard,hphase⟩ := prefix_invariant loc F Q v _ M hv hvsmall hM hdiam hQ hc hz H hhead.1
    apply ih hsub hcard
    intro hne
    exact (hphase hne).trans (pow_le_pow_right₀ (by nlinarith only [sq_nonneg v]) (by omega))

theorem attains_high [Nonempty D] (loc : D → X) (F : Finset X) (v M : ℝ)
    (hv : 0 < v) (hvsmall : v < 1/6) (hM : 0 < M)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) {n c : ℕ}
    (h : Attains loc F ∅ ∅ v (8*(Fintype.card D:ℝ)*M) 0 n c) : c ≤ 1 := by
  obtain ⟨T,_,hh,_,hc⟩ := h
  have hs := history_invariant loc F v M hv hvsmall hM hdiam 0 ∅ (Finset.empty_subset _)
    (by simp) (by simp) T hh
  rw [← hc,Finset.inter_eq_left.mpr hs.1]
  exact hs.2

end MetricKMedianRecovery.PhaseUpperBracket

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoupledInitial
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.levelWords_encode _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.parentWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma initial_certified {loc : Fin d → V} {F : Finset V} {v eta lo hi : ℝ}
    {l u : ℚ} {n k : ℕ} {T U : List (List (Label V))}
    (hl : lo≤(l:ℝ)) (hu : (u:ℝ)≤hi) (hlu : l≤u) (hl0 : (0:ℝ)≤l)
    (hwidth : (u:ℝ)-l≤(d:ℝ)*eta)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j))
    (hT : Runs (fun j=>original (loc j)) (F.image original) ∅ ∅ v u 0 n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) ∅ ∅ v l 0 n U)
    (hs : Sandwich k ((after ∅ T)∩F.image original).card ((after ∅ U)∩F.image original).card) :
    Certified loc F v eta lo hi 0 n k (initial l u T U) := by
  have hf : ∀ x∈F.image original,∀ j,1≤dist x (original (loc j)) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hfar i hi j
  have hp := PhaseInitialBracket.empty_prefix (fun j=>original (loc j)) (F.image original) ∅
    v (l:ℝ) eta hl0 hf
  have hp' := PhaseInitialBracket.empty_prefix (fun j=>original (loc j)) (F.image original) ∅
    v (u:ℝ) eta (hl0.trans (by exact_mod_cast hlu)) hf
  refine {
    before := by simp [initial,Before]
    before_map := by simp [initial,State.mapFree,Before]
    disjoint := Finset.disjoint_empty_right _
    low := hl
    high := hu
    price := by exact_mod_cast hlu
    eps_nonneg := by norm_num [initial,Correction.error]
    error := ?_
    inj := Function.injective_id
    fixed := fun _ _=>rfl
    shrink := fun _ _ _=>le_rfl
    loss := fun _ _ _=>by simp only [initial,Correction.apply,Correction.error,id_eq,Rat.cast_zero,add_zero,le_refl]
    old_prefix := hp
    new_prefix := ?_
    sandwich := hs
    new_tail := ?_
    old_tail := hU }
  · simpa only [initial,Correction.error,Rat.cast_zero,mul_zero,add_zero] using hwidth
  · simpa only [initial,State.mapFree,State.mapPrefix,Finset.image_empty,List.map_nil] using hp'
  · simpa only [initial,State.mapFree,State.mapPrefix,Finset.image_empty,List.map_nil,after] using hT

end MetricKMedianRecovery.CanonicalCoupledMerge

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma start_correct_s238_oai (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lo M : ℚ) (eta : ℝ) (N precision total k : ℕ)
    (hd : 0<d) (hdN : d≤N) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hlohi : lo≤8*(d:ℚ)*M) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    (start loc distance F v lo M N precision total k).Correct loc F v eta lo M total k := by
  let count := fun lam=>initialCount loc distance F v lam total
  let high : ℚ := 8*(d:ℚ)*M
  have hloR : (0:ℝ)<lo := by exact_mod_cast hlo
  have hhighR : (high:ℝ)=8*(d:ℝ)*(M:ℝ) := by simp only [high,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
  have hhN : 8*(d:ℝ)*(M:ℝ)≤8*N*(M:ℝ) := by
    gcongr
  have hfar' : ∀ x∈F.image original,∀ j,1≤dist x (original (loc j)) := by
    intro x hx j
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
    rw [original_dist]
    exact hfar i hi j
  have hs (lam : ℚ) := initialHistory_spec_s238 loc distance hmetric F v lam total hv hv1
  have hp (lam : ℚ) (hlam : (0:ℝ)≤lam) :=
    PhaseInitialBracket.empty_prefix (fun j=>original (loc j)) (F.image original) ∅ v lam eta hlam hfar'
  dsimp only [start]
  change StartOutput.Correct loc F v eta lo M total k (if count lo≤k then _ else _)
  split
  next hc =>
    refine ⟨rfl,rfl,?_,hc⟩
    have ht := hs lo
    have hh := (hp lo hloR.le).append_exact hv hv1 hloR heta _ ht.2.1 ht.2.2
    simpa only [ht.1,Nat.zero_add,finish,List.nil_append] using hh
  next hc =>
    have hhigh : count high≤k := by
      let : NeZero d := ⟨by omega⟩
      apply (PhaseUpperBracket.attains_high (fun j=>original (loc j)) (F.image original)
        (v:ℝ) (M:ℝ) hv hv1 (by exact_mod_cast hM) (fun x hx j=>by
          obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
          rw [original_dist]
          exact hdiam i hi j) (n:=total) (c:=count high) ?_).trans (by omega : 1≤k)
      have hh := (hs high).attains
      simpa only [Fintype.card_fin,hhighR,count,initialCount] using hh
    let I := PriceBisection.search count k (PriceBisection.iterations lo high precision) (lo,high)
    obtain ⟨hl,hlu,hu,hcl,hcu,hw⟩:=PriceBisection.search_spec count k
      (PriceBisection.iterations lo high precision) lo high hlohi (by omega) hhigh
    change k ≤ count I.1 at hcl
    change count I.2≤k at hcu
    have hlR : (lo:ℝ)≤(I.1:ℝ) := by exact_mod_cast hl
    have hluR : (I.1:ℝ)≤(I.2:ℝ) := by exact_mod_cast hlu
    have huR : (I.2:ℝ)≤8*(d:ℝ)*(M:ℝ) := by rw [←hhighR]; exact_mod_cast hu
    have hlp : (0:ℝ)<(I.1:ℝ) := hloR.trans_le hlR
    have hup : (0:ℝ)<(I.2:ℝ) := hlp.trans_le hluR
    have hw' : I.2-I.1 ≤1/(2:ℚ)^precision := hw ▸ PriceBisection.iterations_precision lo high precision
    change StartOutput.Correct loc F v eta lo M total k (if count I.1=k then _ else if count I.2=k then _ else _)
    split
    next he =>
      have hh := finish_correct (hp I.1 hlp.le) hv hv1 hlp heta (Finset.disjoint_empty_right _)
        hlR (hluR.trans huR) (hs I.1) he
      simpa only [StartOutput.Correct,Nat.zero_add] using hh
    next he =>
      split
      next he' =>
        have hh := finish_correct (hp I.2 hup.le) hv hv1 hup heta (Finset.disjoint_empty_right _)
          (hlR.trans hluR) huR (hs I.2) he'
        simpa only [StartOutput.Correct,Nat.zero_add] using hh
      next he' =>
        have hwR : (I.2:ℝ)-I.1≤(d:ℝ)*eta := by
          have hh : (I.2:ℝ)-I.1≤eta := by
            have hwr : ((I.2-I.1:ℚ):ℝ)≤((1/(2:ℚ)^precision:ℚ):ℝ) := by exact_mod_cast hw'
            simpa only [Rat.cast_sub] using hwr.trans hprecision
          have hdR : (1:ℝ)≤d := by exact_mod_cast hd
          exact hh.trans (by nlinarith)
        have hsand : Sandwich k (count I.2) (count I.1) := Or.inl ⟨by omega,by omega⟩
        have hi := initial_certified hlR huR hlu hlp.le hwR hfar (hs I.2) (hs I.1) hsand
        have hh := run_correct loc distance hmetric F v M eta lo (8*(d:ℝ)*(M:ℝ)) N precision k
          hF hM hN hv hv1 hloR heta hhN hprecision hdiam 0 total _ hi
        simpa only [StartOutput.Correct,Nat.zero_add] using hh

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end

theorem solution.{u_1} : type_of% @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_correct_s238_oai.{u_1} := @OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_correct_s238_oai.{u_1}
