-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:16:44.988886+00:00
-- url     : https://prove2.me/submissions/70c0c469-94d7-4a74-84d1-8476086b568a

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L049
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_run_initial_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitial_counts_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitial_finishes_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitial_loopInput_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialQuery_count_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialQuery_history_pack_s238r
import Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_initialHistory_spec_s238r

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

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialPack
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outputBits outcomeBits)
attribute [local irreducible] BinaryInitialQuery.count BinaryInitialQuery.history BinaryCoupledLoop.run BinaryBisection.run
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v lo M : ℚ) (N precision total k : ℕ)
local notation "xx" => pack distance loc F v lo M N precision total k
local notation "bb" => BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v 0 0
local notation "qq" => BinaryInitialQuery.ctx bb total
lemma ctx_pack : ctx xx=qq := by
  simp only [ctx,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,BinaryInitialQuery.ctx]
lemma loInput_pack : loInput xx=pairBits (qq,BinaryRational.encode lo) := by
  unfold loInput
  rw [ctx_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
lemma loCount_pack : loCount xx=(initialCount loc distance F v lo total).bits := by
  unfold loCount
  rw [loInput_pack,BinaryInitialQuery.count_pack_s238r]
lemma loHistory_pack : loHistory xx=historyBits (initialHistory loc distance F v lo total) := by
  unfold loHistory
  rw [loInput_pack,BinaryInitialQuery.history_pack_s238r]
lemma loFinish_pack : loFinish xx=outputBits (finish ∅ lo [] (initialHistory loc distance F v lo total)) := by
  unfold loFinish
  rw [loHistory_pack]
  simp only [pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  simp only [outputBits,finish,List.nil_append,setBits,BinaryLabel.orderedSort,Finset.sort_empty,labels,List.map_nil,encode]
end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_InitialCorrect
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitial
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing PhaseMergeInvariant PhaseCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryCoupled (outputBits)
variable {m d : ℕ} [PseudoMetricSpace (Fin m)]
attribute [local instance] RationalLeaves.metric
lemma run_pack_s238r_oai (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset (Fin m))
    (v lo M : ℚ) (eta : ℝ) (N precision total k : ℕ)
    (hd : 0<d) (hdN : d≤N) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hlohi : lo≤8*(d:ℚ)*M) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    run (pack distance loc F v lo M N precision total k)=
      output (start loc distance F v lo M N precision total k) := by
  let xx := pack distance loc F v lo M N precision total k
  let count := fun lam=>initialCount loc distance F v lam total
  let high : ℚ := 8*(d:ℚ)*M
  let I := PriceBisection.search count k (PriceBisection.iterations lo high precision) (lo,high)
  have hkbits : field 4 xx=k.bits := by
    simp only [xx,pack,field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
  have hloC : loCount xx=(count lo).bits := loCount_pack distance loc F v lo M N precision total k
  have hloF : loFinish xx=outputBits (finish ∅ lo [] (initialHistory loc distance F v lo total)) :=
    loFinish_pack distance loc F v lo M N precision total k
  change run xx=output (start loc distance F v lo M N precision total k)
  unfold run start
  rw [hkbits,hloC,value_bits,value_bits]
  change (if count lo≤k then _ else _)=output (if count lo≤k then _ else _)
  by_cases hc : count lo≤k
  · simp only [hc,ite_eq_left,output,hloF]
  · rw [ite_eq_right hc,ite_eq_right hc]
    have hloR : (0:ℝ)<lo := by exact_mod_cast hlo
    have hhighR : (high:ℝ)=8*(d:ℝ)*(M:ℝ) := by simp only [high,Rat.cast_mul,Rat.cast_natCast,Rat.cast_ofNat]
    have hhN : 8*(d:ℝ)*(M:ℝ)≤8*N*(M:ℝ) := by gcongr
    have hs (lam : ℚ) := initialHistory_spec_s238r loc distance hmetric F v lam total hv hv1
    have hhigh : count high≤k := by
      let : NeZero d := ⟨by omega⟩
      apply (PhaseUpperBracket.attains_high (fun j=>original (loc j)) (F.image original)
        (v:ℝ) (M:ℝ) hv hv1 (by exact_mod_cast hM) (fun x hx j=>by
          obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hx
          rw [original_dist]
          exact hdiam i hi j) (n:=total) (c:=count high) ?_).trans (by omega : 1≤k)
      have hh := (hs high).attains
      simpa only [Fintype.card_fin,hhighR,count,initialCount] using hh
    obtain ⟨hl,hlu,hu,hcl,hcu,hw⟩:=PriceBisection.search_spec count k
      (PriceBisection.iterations lo high precision) lo high hlohi (by omega) hhigh
    change k ≤ count I.1 at hcl
    change count I.2≤k at hcu
    obtain ⟨hlC,huC⟩:=counts_pack_s238r distance loc F v lo M N precision total k
    obtain ⟨hlF,huF⟩:=finishes_pack_s238r distance loc F v lo M N precision total k
    change lowerCount xx=(count I.1).bits at hlC
    change upperCount xx=(count I.2).bits at huC
    change lowerFinish xx=outputBits (finish ∅ I.1 [] (initialHistory loc distance F v I.1 total)) at hlF
    change upperFinish xx=outputBits (finish ∅ I.2 [] (initialHistory loc distance F v I.2 total)) at huF
    unfold normal
    rw [hlC,huC,hkbits,value_bits,value_bits,value_bits]
    change pairBits ([true], if count I.1=k then _ else if count I.2=k then _ else _)=
      output (if count I.1=k then _ else if count I.2=k then _ else _)
    by_cases he : count I.1=k
    · rw [ite_eq_left he,ite_eq_left he]
      simp only [output,hlF]
      rfl
    · rw [ite_eq_right he,ite_eq_right he]
      by_cases he' : count I.2=k
      · rw [ite_eq_left he',ite_eq_left he']
        simp only [output,huF]
        rfl
      · rw [ite_eq_right he',ite_eq_right he']
        simp only [output]
        have hlR : (lo:ℝ)≤(I.1:ℝ) := by exact_mod_cast hl
        have hluR : (I.1:ℝ)≤(I.2:ℝ) := by exact_mod_cast hlu
        have huR : (I.2:ℝ)≤8*(d:ℝ)*(M:ℝ) := by rw [←hhighR]; exact_mod_cast hu
        have hlp : (0:ℝ)<(I.1:ℝ) := hloR.trans_le hlR
        have hw' : I.2-I.1 ≤1/(2:ℚ)^precision := hw ▸ PriceBisection.iterations_precision lo high precision
        have hwR : (I.2:ℝ)-I.1≤(d:ℝ)*eta := by
          have hh : (I.2:ℝ)-I.1≤eta := by
            have hwr : ((I.2-I.1:ℚ):ℝ)≤((1/(2:ℚ)^precision:ℚ):ℝ) := by exact_mod_cast hw'
            simpa only [Rat.cast_sub] using hwr.trans hprecision
          have hdR : (1:ℝ)≤d := by exact_mod_cast hd
          exact hh.trans (by nlinarith)
        have hsand : Sandwich k (count I.2) (count I.1) := Or.inl ⟨by omega,by omega⟩
        have hi := initial_certified hlR huR hlu hlp.le hwR hfar (hs I.2) (hs I.1) hsand
        rw [loopInput_pack_s238r]
        rw [BinaryCoupledLoop.run_initial_s238r distance loc hmetric F v M I.1 I.2 eta lo (8*(d:ℝ)*(M:ℝ)) N precision total k
          hF hM hN hv hv1 hloR heta hhN hprecision hdiam _ _ hi]
end MetricKMedianRecovery.BitMachine.BinaryInitial

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238r_oai
