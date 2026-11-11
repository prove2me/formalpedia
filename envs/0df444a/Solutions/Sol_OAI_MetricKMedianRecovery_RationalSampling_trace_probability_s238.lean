-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:33:08.078005+00:00
-- url     : https://prove2.me/submissions/c2f175b8-3947-4d36-bec2-83ef268ad197

import Mathlib
import Definitions.Def_Q238K021
import Definitions.Def_Q238K022

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Basic
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace RationalMin
open WordList
lemma fold_le_init (qs : List ℚ) (a : ℚ) : qs.foldl min a≤a := by
  induction qs generalizing a with
  | nil=>exact le_rfl
  | cons q qs ih=>exact (ih (min a q)).trans (min_le_left a q)
lemma fold_le_mem (qs : List ℚ) (a q : ℚ) (hq : q∈qs) : qs.foldl min a≤q := by
  induction qs generalizing a with
  | nil=>simp only [List.not_mem_nil] at hq
  | cons r rs ih=>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hq with rfl|hq
    · exact (fold_le_init rs (min a q)).trans (min_le_right a q)
    · exact ih (min a r) hq
lemma minimum_le_mem (qs : List ℚ) (q : ℚ) (hq : q∈qs) : minimum qs≤q := fold_le_mem qs _ q hq
end RationalMin
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_PopulationBridge
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.RationalMin
lemma fold_lower_real (qs : List ℚ) (a : ℚ) (u : ℝ) (ha : u≤(a:ℝ)) (hq : ∀ q∈qs,u≤(q:ℝ)) :
    u≤((qs.foldl min a : ℚ):ℝ) := by
  induction qs generalizing a with
  | nil=>exact ha
  | cons q qs ih=>
    rw [List.foldl_cons]
    apply ih
    · rw [Rat.cast_min]
      exact le_min ha (hq q (by simp))
    · intro r hr
      exact hq r (by simp [hr])
lemma minimum_lower_real (qs : List ℚ) (u : ℝ) (hne : qs≠[]) (hu : ∀ q∈qs,u≤(q:ℝ)) :
    u≤(minimum qs:ℝ) := by
  cases qs with
  | nil=>exact (hne rfl).elim
  | cons q qs=>
    apply fold_lower_real
    · exact hu q (by simp)
    · exact hu
end MetricKMedianRecovery.BitMachine.RationalMin
namespace MetricKMedianRecovery.BitMachine.BinaryPopulation
variable {n : ℕ} [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma filter_count_cast (D : Finset (Fin n)) (w p : Fin n) :
    ((distanceList δ D w).filter (fun q=>decide (q≤δ w p))).length=(Population.ball D w (dist w p)).card := by
  rw [distanceList,List.filter_map,List.length_map]
  simp only [Function.comp_def]
  rw [←List.toFinset_card_of_nodup ((D.sort_nodup (·≤·)).filter (fun v=>decide (δ w v≤δ w p)))]
  congr 1
  ext i
  simp only [List.toFinset_filter,Finset.sort_toFinset,Finset.mem_filter,decide_eq_true_eq,Population.ball]
  rw [←hδ w i,←hδ w p,Rat.cast_le]
lemma candidate_cast (D : Finset (Fin n)) (P : ℚ) (m : ℕ) (w p : Fin n) :
    (candidateQ P m (distanceList δ D w) (δ w p):ℝ)=Population.candidate D (P:ℝ) m w p := by
  simp only [candidateQ,Rat.cast_max,Rat.cast_div,Rat.cast_mul,Rat.cast_natCast,hδ,
    filter_count_cast δ hδ,Population.candidate]
omit hδ [PseudoMetricSpace (Fin n)] in
lemma distanceList_nonempty (D : Finset (Fin n)) (hD : D.Nonempty) (w : Fin n) : distanceList δ D w≠[] := by
  intro hh
  obtain ⟨p,hp⟩:=hD
  have hm : δ w p∈distanceList δ D w := List.mem_map.mpr ⟨p,(Finset.mem_sort (·≤·)).mpr hp,rfl⟩
  rw [hh] at hm
  exact List.not_mem_nil hm
lemma radiusQ_cast (D : Finset (Fin n)) (hD : D.Nonempty) (P : ℚ) (m : ℕ) (w : Fin n) :
    (radiusQ P m (distanceList δ D w):ℝ)=Population.radius D hD (P:ℝ) m w := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro p hp
    rw [←candidate_cast δ hδ D P m w p]
    exact_mod_cast RationalMin.minimum_le_mem ((distanceList δ D w).map (candidateQ P m (distanceList δ D w))) (candidateQ P m (distanceList δ D w) (δ w p))
      (List.mem_map.mpr ⟨δ w p,List.mem_map.mpr ⟨p,(Finset.mem_sort (·≤·)).mpr hp,rfl⟩,rfl⟩)
  · apply RationalMin.minimum_lower_real
    · exact fun h=>distanceList_nonempty δ D hD w (List.map_eq_nil_iff.mp h)
    · intro q hq
      obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hq
      obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hd
      rw [candidate_cast δ hδ]
      exact Finset.inf'_le _ ((Finset.mem_sort (·≤·)).mp hp)
end MetricKMedianRecovery.BitMachine.BinaryPopulation

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

lemma chosen_mem (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    chosen S Δ s x ∈ tags S s :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).1

lemma chosen_key_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) :
    toLex (tagDistance Δ s x (chosen S Δ s x),chosen S Δ s x) ≤
      toLex (tagDistance Δ s x t,t) :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).2 t ht

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_Kernel
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided

variable {S A : Type*} [Fintype A]

lemma sum_fin_succ (n : ℕ) (X : (Fin (n+1) → A) → ℝ) :
    (∑ seed, X seed) = ∑ a : A, ∑ seed : Fin n → A, X (Fin.cons a seed) := by
  calc
    _ = ∑ y : A × (Fin n → A), X (Fin.cons y.1 y.2) := by
      apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => A)).symm
      intro x
      exact congrArg X (Fin.cons_self_tail x).symm
    _ = _ := Fintype.sum_prod_type _

end MetricKMedianRecovery.Guided

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RationalSampling
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling
variable {n : ℕ}
lemma tagId_le_iff (t u : Tag (Fin n)) : tagId t≤tagId u ↔ t≤u := by
  cases t using Sum.rec with
  | inl a =>
    cases u using Sum.rec with
    | inl b =>
      change a.val≤b.val ↔ toLex (Sum.inl a:Fin n⊕ℕ)≤toLex (Sum.inl b)
      exact (@Sum.Lex.inl_le_inl_iff (Fin n) ℕ _ _ a b).symm
    | inr b =>
      change a.val≤n+b ↔ toLex (Sum.inl a:Fin n⊕ℕ)≤toLex (Sum.inr b)
      exact iff_of_true (by omega) (Sum.Lex.inl_le_inr a b)
  | inr a =>
    cases u using Sum.rec with
    | inl b =>
      change n+a≤b.val ↔ toLex (Sum.inr a:Fin n⊕ℕ)≤toLex (Sum.inl b)
      exact iff_of_false (by omega) Sum.Lex.not_inr_le_inl
    | inr b =>
      change n+a≤n+b ↔ toLex (Sum.inr a:Fin n⊕ℕ)≤toLex (Sum.inr b)
      rw [Sum.Lex.inr_le_inr_iff]
      omega
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ in
lemma tagDistance_cast (Δ : ℚ) (s : State n) (w : Fin n) (t : Tag (Fin n)) :
    (tagDistance δ Δ s w t:ℝ)=Sampling.tagDistance (Δ:ℝ) s.real w t := by
  cases ht : ofLex t with
  | inl v=>simp only [tagDistance,Sampling.tagDistance,ht,hδ]
  | inr j=>
    cases j with
    | zero=>simp only [tagDistance,Sampling.tagDistance,ht]
    | succ j=>
      simp only [tagDistance,Sampling.tagDistance,ht,State.real,List.getElem?_map]
      cases hz : s.leaves[j]? <;> simp only [Option.map_none,Option.map_some,Rat.cast_add,hδ]
include hδ in
lemma key_le_iff (Δ : ℚ) (s : State n) (w : Fin n) (t u : Tag (Fin n)) :
    key δ Δ s w t≤ key δ Δ s w u ↔
      toLex (Sampling.tagDistance (Δ:ℝ) s.real w t,t)≤toLex (Sampling.tagDistance (Δ:ℝ) s.real w u,u) := by
  rw [←tagDistance_cast δ hδ Δ s w t,←tagDistance_cast δ hδ Δ s w u]
  simp only [key,Prod.Lex.le_iff,ofLex_toLex,Rat.cast_lt,Rat.cast_inj,tagId_le_iff]
include hδ in
lemma minimum_key (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (keys δ S Δ s w).min' (keys_nonempty δ S Δ s w)=key δ Δ s w (Sampling.chosen S (Δ:ℝ) s.real w) := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨_,Sampling.chosen_mem S (Δ:ℝ) s.real w,rfl⟩)
  · apply Finset.le_min'
    intro x hx
    obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp hx
    exact (key_le_iff δ hδ Δ s w _ t).mpr (Sampling.chosen_key_le S (Δ:ℝ) s.real w ht)
include hδ in
lemma minimum_reference (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    ((ofLex ((keys δ S Δ s w).min' (keys_nonempty δ S Δ s w))).1:ℝ)=Sampling.reference S (Δ:ℝ) s.real w := by
  rw [minimum_key δ hδ]
  exact tagDistance_cast δ hδ Δ s w _
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalMenus
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
lemma menuWeight_cast (M E J : ℕ) (e : Sampling.Entry M E J) :
    (menuWeight M E J e:ℝ)=RadiusMenus.menuWeight M E J e := by
  rcases e with i | (i | i) <;>
    simp only [menuWeight,RadiusMenus.menuWeight,RadiusMenus.thirdNormalizer_eq,Rat.cast_div,Rat.cast_mul,
      Rat.cast_one,Rat.cast_ofNat,Rat.cast_natCast,Rat.cast_add,Rat.cast_pow,Rat.cast_sub]
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
omit hδ [PseudoMetricSpace (Fin n)] in
lemma leafValues_nonempty (s : State n) (w : Fin n) (h : s.leaves≠[]) : leafValues δ s w≠[] := by
  exact fun hh=>h (List.map_eq_nil_iff.mp hh)
lemma nearestLeaf_cast (s : State n) (w : Fin n) :
    (nearestLeaf δ s w).map (fun q : ℚ=>(q:ℝ))=Sampling.nearestLeaf s.real w := by
  by_cases he : s.leaves=[]
  · simp [nearestLeaf,he,Sampling.nearestLeaf,Sampling.leafDistances,State.real]
  · have hn : (Sampling.leafDistances s.real w).Nonempty := by
      obtain ⟨z,hz⟩:=List.exists_mem_of_ne_nil s.leaves he
      exact ⟨dist w z.1+(z.2:ℝ),Finset.mem_image.mpr ⟨(z.1,(z.2:ℝ)),List.mem_toFinset.mpr
        (List.mem_map.mpr ⟨z,hz,rfl⟩),rfl⟩⟩
    simp only [nearestLeaf,ite_eq_right he,Option.map_some,Sampling.nearestLeaf,dite_eq_left hn,Option.some.injEq]
    apply le_antisymm
    · apply Finset.le_inf'
      intro x hx
      obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hx
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp hz)
      dsimp only [id]
      rw [←hδ w t.1,←Rat.cast_add]
      exact_mod_cast RationalMin.minimum_le_mem (leafValues δ s w) (δ w t.1+t.2) (List.mem_map.mpr ⟨t,ht,rfl⟩)
    · apply RationalMin.minimum_lower_real
      · exact leafValues_nonempty δ s w he
      · intro q hq
        obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hq
        rw [Rat.cast_add,hδ]
        exact Finset.inf'_le _ (Finset.mem_image.mpr ⟨(z.1,(z.2:ℝ)),List.mem_toFinset.mpr (List.mem_map.mpr ⟨z,hz,rfl⟩),rfl⟩)
lemma menuRadius_cast (D : Finset (Fin n)) (hD : D.Nonempty) (P κ : ℚ) (m M E J : ℕ) (s : State n) (w : Fin n)
    (e : Sampling.Entry M E J) :
    (menuRadius δ D P κ m M E J s w e).map (fun q : ℚ=>(q:ℝ))=
      Sampling.menuRadius D hD (P:ℝ) (κ:ℝ) m M E J s.real w e := by
  rcases e with i | (i | i)
  · simp only [menuRadius,Sampling.menuRadius,Option.map_some,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
      Rat.cast_one,BinaryPopulation.radiusQ_cast δ hδ D hD]
  · simp only [menuRadius,Sampling.menuRadius,←nearestLeaf_cast δ hδ,Option.map_map,Function.comp_def,
      Rat.cast_div,Rat.cast_pow,Rat.cast_add,Rat.cast_one]
  · simp only [menuRadius,Sampling.menuRadius,Option.map_some,Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,
      Rat.cast_one,BinaryPopulation.radiusQ_cast δ hδ D hD]
end Metric
end MetricKMedianRecovery.RationalSampling

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
lemma remove_real (s : State n) (v : Fin n) : (s.remove v).real=s.real.remove v := by
  simp only [State.remove,State.real,Sampling.State.remove]
  congr 1
  ext x
  simp only [Finset.mem_insert]
lemma add_real (s : State n) (w : Fin n) (R : ℚ) : (s.add w R).real=s.real.add w (R:ℝ) := by
  simp only [State.add,State.real,Sampling.State.add,List.map_append,List.map_cons,List.map_nil]
lemma retain_real (m : ℕ) (s : State n) : (retain m s).map State.real=Sampling.retain m s.real := by
  simp only [retain,Sampling.retain,State.real,List.length_map]
  split_ifs <;> rfl
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma reference_cast (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (reference δ S Δ s w:ℝ)=Sampling.reference S (Δ:ℝ) s.real w := minimum_reference δ hδ S Δ s w
lemma chosenId_eq (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    chosenId δ S Δ s w=tagId (Sampling.chosen S (Δ:ℝ) s.real w) := by
  simp only [chosenId,chosenKey,minimum_key δ hδ,key,ofLex_toLex]
lemma clientWeight_cast (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (clientWeight δ S Δ s w:ℝ)=Sampling.clientWeight S (Δ:ℝ) s.real w := by
  simp only [clientWeight,Rat.cast_max,Rat.cast_zero,reference_cast δ hδ,Sampling.clientWeight]
lemma totalWeight_cast (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) :
    (totalWeight δ D S Δ s:ℝ)=Sampling.totalWeight D S (Δ:ℝ) s.real := by
  simp only [totalWeight,Rat.cast_sum,clientWeight_cast δ hδ,Sampling.totalWeight]
lemma transitionWeight_cast (D S : Finset (Fin n)) (Δ : ℚ) (M E J : ℕ) (s : Option (State n))
    (a : Sampling.Action D M E J) :
    (transitionWeight δ D S Δ M E J s a:ℝ)=Sampling.transitionWeight D S (Δ:ℝ) M E J (s.map State.real) a := by
  cases s with
  | none=>simp only [transitionWeight,Sampling.transitionWeight,Option.map_none];split_ifs <;> norm_num
  | some s=>
    simp only [transitionWeight,Sampling.transitionWeight,Option.map_some,←totalWeight_cast δ hδ]
    have hh : (0:ℝ)<(totalWeight δ D S Δ s:ℝ) ↔ 0<totalWeight δ D S Δ s := Rat.cast_pos
    simp only [hh]
    split_ifs
    · rcases a with u | (w | ⟨w,e⟩) <;>
        simp only [Rat.cast_zero,Rat.cast_div,Rat.cast_mul,Rat.cast_ofNat,clientWeight_cast δ hδ,menuWeight_cast]
    all_goals norm_num
lemma update_real (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (State n)) (a : Sampling.Action D M E J) :
    (update δ D F S Δ P κ m M E J s a).map State.real=
      Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J (s.map State.real) a := by
  cases s with
  | none=>rfl
  | some s=>
    simp only [update,Sampling.update,Option.map_some,←totalWeight_cast δ hδ]
    have hh : (0:ℝ)<(totalWeight δ D S Δ s:ℝ) ↔ 0<totalWeight δ D S Δ s := Rat.cast_pos
    simp only [hh]
    split_ifs with ht
    · rcases a with u | (w | ⟨w,e⟩)
      · rfl
      · dsimp only
        rw [chosenId_eq δ hδ]
        cases hz : ofLex (Sampling.chosen S (Δ:ℝ) s.real w) with
        | inl v=>
          simp only [tagId,hz,dite_eq_left v.isLt,retain_real,remove_real]
        | inr j=>simp [tagId,hz,show ¬n+j<n by omega]
      · dsimp only
        have hr:=menuRadius_cast δ hδ D hD P κ m M E J s w e
        cases he : menuRadius δ D P κ m M E J s w e with
        | none=>simp only [Option.map_none,he] at hr;rw [←hr];rfl
        | some R=>
          simp only [he,Option.map_some] at hr
          rw [←hr]
          have hb : F.filter (fun v=>δ w.val v≤R)=F.filter (fun v=>dist w.val v≤(R:ℝ)) := by
            ext i
            simp only [Finset.mem_filter,←hδ w.val i,Rat.cast_le]
          dsimp only
          rw [hb]
          split_ifs <;> simp only [retain_real,add_real,Option.map_none]
    · rfl
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Average
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery
namespace FiniteSampling

open scoped BigOperators

section Average
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

lemma average_prod (X : Ω × Ξ → ℝ) :
    average X = average (fun ω => average (fun ξ => X (ω,ξ))) := by
  simpa only [average, Finset.univ_product_univ] using
    Finset.expect_product (Finset.univ : Finset Ω) (Finset.univ : Finset Ξ) X

lemma average_equiv (e : Ω ≃ Ξ) (X : Ω → ℝ) (Y : Ξ → ℝ)
    (h : ∀ ω, X ω = Y (e ω)) : average X = average Y :=
  Fintype.expect_equiv e X Y h

end Average

lemma average_fin_succ {Ω : Type*} [Fintype Ω] (n : ℕ)
    (X : (Fin (n+1) → Ω) → ℝ) :
    average X = average (fun ω => average (fun s : Fin n → Ω => X (Fin.cons ω s))) := by
  calc
    average X = average (fun p : Ω × (Fin n → Ω) => X (Fin.cons p.1 p.2)) := by
      apply average_equiv (Fin.consEquiv (fun _ : Fin (n+1) => Ω)).symm
      intro s
      exact congrArg X (Fin.cons_self_tail s).symm
    _ = _ := average_prod _

end FiniteSampling
end MetricKMedianRecovery

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_RawCount
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Dyadic
variable {A : Type*} [Fintype A] [DecidableEq A]

lemma draw_average (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ht : ∑ a, p a = 1) (b : ℕ) (default : A) (f : A → ℝ) :
    (∑ bits : Fin b → Bool, f (draw p hp ht b default bits)) / 2^b =
      ∑ a, weight p b default a * f a := by
  have h := Fintype.sum_equiv (allocation p hp ht b default)
    (fun bits => f (draw p hp ht b default bits)) (fun x => f x.1) (fun _ => rfl)
  rw [h,Fintype.sum_sigma,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,weight]
  ring

end MetricKMedianRecovery.Dyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided.FixedDyadic
open FiniteSampling
variable {S A : Type*} [Fintype A] [DecidableEq A]

lemma draw_average (p : Kernel S A) (b : ℕ) (default : A) (s : S) (g : A → ℝ) :
    average (fun bits => g (draw p b default s bits)) =
      ∑ a, (kernel p b default).weight s a * g a := by
  rw [average,Fintype.expect_eq_sum_div_card]
  simpa only [draw,kernel,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
    using Dyadic.draw_average (p.weight s) (p.nonneg s) (p.total s) b default g

theorem actions_average (f : S → A → S) (p : Kernel S A) (b : ℕ) (default : A)
    (n : ℕ) (s : S) (g : (Fin n → A) → ℝ) :
    average (fun bits => g (actions f p b default n s bits)) =
      ∑ a : Fin n → A, pathWeight f (kernel p b default).weight n s a * g a := by
  classical
  induction n generalizing s with
  | zero =>
    simp only [actions,average_const,pathWeight,one_mul]
    simp only [Fintype.sum_unique]
    congr 1
  | succ n ih =>
    rw [average_fin_succ,sum_fin_succ]
    simp only [actions,Fin.cons_zero,Fin.tail_cons,pathWeight]
    conv_lhs =>
      arg 1; ext bits
      rw [ih (f s (draw p b default s bits)) (fun seed => g (Fin.cons (draw p b default s bits) seed))]
    rw [draw_average p b default s
      (fun a => ∑ seed : Fin n → A,
        pathWeight f (kernel p b default).weight n (f s a) seed * g (Fin.cons a seed))]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro seed _
    ring

end MetricKMedianRecovery.Guided.FixedDyadic

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RealizedKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Guided.Realized
open FiniteSampling
variable {S A Ω : Type*} [Fintype A] [Fintype Ω]

theorem actions_average (f : S→A→S) (p : Kernel S A) (r : Draw (Ω:=Ω) p)
    (n : ℕ) (s : S) (g : (Fin n→A)→ℝ) :
    average (fun bits=>g (actions f p r n s bits))=
      ∑ a : Fin n→A,pathWeight f p.weight n s a*g a := by
  classical
  induction n generalizing s with
  | zero=>
    simp only [actions,average_const,pathWeight,one_mul,Fintype.sum_unique]
    congr 1
  | succ n ih=>
    rw [average_fin_succ,sum_fin_succ]
    simp only [actions,Fin.cons_zero,Fin.tail_cons,pathWeight]
    conv_lhs=>
      arg 1; ext bits
      rw [ih (f s (r.run s bits)) (fun seed=>g (Fin.cons (r.run s bits) seed))]
    rw [r.law s (fun a=>∑ seed : Fin n→A,pathWeight f p.weight n (f s a) seed*g (Fin.cons a seed))]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro seed _
    ring
lemma canonical_law [DecidableEq A] (f : S→A→S) (p : Kernel S A) (b : ℕ) (d : A)
    (as : List A) (h : as.Perm Finset.univ.toList) (n : ℕ) (s : S) (g : (Fin n→A)→ℝ) :
    average (fun bits=>g (actions f (FixedDyadic.kernel p b d) (canonical p b d as h) n s bits))=
      average (fun bits=>g (FixedDyadic.actions f p b d n s bits)) := by
  rw [actions_average,FixedDyadic.actions_average]
end MetricKMedianRecovery.Guided.Realized

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
lemma mem_entries (M E J : ℕ) (e : Entry M E J) : e∈entries M E J := by
  rcases e with i | (i | i) <;> simp only [entries,List.mem_append,List.mem_ofFn]
  · exact Or.inl (Or.inl ⟨i,rfl⟩)
  · exact Or.inl (Or.inr ⟨i,rfl⟩)
  · exact Or.inr ⟨i,rfl⟩
lemma entries_nodup (M E J : ℕ) : (entries M E J).Nodup := by
  simp only [entries,List.nodup_append,List.nodup_ofFn]
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · exact fun a b h=>Sum.inl.inj h
  · exact fun a b h=>Sum.inl.inj (Sum.inr.inj h)
  · simp only [List.mem_ofFn]; rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ h; cases h
  · exact fun a b h=>Sum.inr.inj (Sum.inr.inj h)
  · simp only [List.mem_append,List.mem_ofFn]
    rintro _ (⟨a,rfl⟩|⟨a,rfl⟩) _ ⟨b,rfl⟩ h <;> cases h

lemma clients_nodup (D : Finset (Fin n)) : (clients D).Nodup := Finset.sort_nodup _ _
lemma mem_clients (D : Finset (Fin n)) (w : D) : w∈clients D := by simp [clients]
lemma actions_nodup (D : Finset (Fin n)) (M E J : ℕ) : (actions D M E J).Nodup := by
  simp only [actions,List.nodup_cons,List.mem_append,List.mem_map,List.nodup_append]
  refine ⟨?_,?_,?_,?_⟩
  · simp
  · exact (clients_nodup D).map (fun a b h=>Sum.inl.inj (Sum.inr.inj h))
  · exact ((clients_nodup D).product (entries_nodup M E J)).map (fun a b h=>Sum.inr.inj (Sum.inr.inj h))
  · rintro _ ⟨w,hw,rfl⟩ _ ⟨z,hz,rfl⟩ h
    cases h
lemma mem_actions (D : Finset (Fin n)) (M E J : ℕ) (a : Action D M E J) : a∈actions D M E J := by
  rcases a with u | (w | ⟨w,e⟩)
  · cases u; simp [actions]
  · simp only [actions,List.mem_cons,List.mem_append,List.mem_map]
    exact Or.inr (Or.inl ⟨w,mem_clients D w,rfl⟩)
  · simp only [actions,List.mem_cons,List.mem_append,List.mem_map]
    exact Or.inr (Or.inr ⟨(w,e),List.mem_product.mpr ⟨mem_clients D w,mem_entries M E J e⟩,rfl⟩)
lemma actions_perm (D : Finset (Fin n)) (M E J : ℕ) : (actions D M E J).Perm Finset.univ.toList := by
  apply (List.perm_ext_iff_of_nodup (actions_nodup D M E J) (Finset.nodup_toList _)).mpr
  simp only [mem_actions,Finset.mem_toList,Finset.mem_univ,implies_true]
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine Guided FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma next_real (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b : ℕ)
    (s : Option (State n)) (seed : Fin b→Bool) :
    (next δ D F S Δ P κ m M E J b s seed).map State.real=
      Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J (s.map State.real)
        (Dyadic.Canonical.draw (Sampling.transitionWeight D S (Δ:ℝ) M E J (s.map State.real)) b (Sum.inl ()) (actions D M E J) seed) := by
  rw [next,update_real δ hδ D F S hD]
  congr 1
  congr 1
  funext a
  exact transitionWeight_cast δ hδ D S Δ M E J s a
end MetricKMedianRecovery.RationalSampling

namespace MetricKMedianRecovery.Guided
variable {S T A : Type*}
lemma states_map (h : S→T) (f : S→A→S) (g : T→A→T)
    (hf : ∀ s a,h (f s a)=g (h s) a) (n : ℕ) (s : S) (seed : Fin n→A) (i : Fin (n+1)) :
    h (states f n s seed i)=states g n (h s) seed i := by
  induction n generalizing s with
  | zero=>rfl
  | succ n ih=>
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · simpa only [states,Fin.cases_succ,hf] using ih (f s (seed 0)) (Fin.tail seed) j
lemma states_list (f : S→A→S) (n : ℕ) (s : S) (seed : Fin n→A) (i : Fin (n+1)) :
    states f n s seed i=((List.ofFn seed).take i.val).foldl f s := by
  induction n generalizing s with
  | zero=>simp only [List.ofFn_zero,List.take_nil,List.foldl_nil];rfl
  | succ n ih=>
    refine Fin.cases ?_ (fun j=>?_) i
    · simp only [states,Fin.cases_zero,Fin.val_zero,List.take_zero,List.foldl_nil]
    · simpa only [states,Fin.cases_succ,List.ofFn_succ,Fin.val_succ,List.take_succ_cons,List.foldl_cons,Fin.tail_def]
        using ih (f s (seed 0)) (Fin.tail seed) j
end MetricKMedianRecovery.Guided
namespace MetricKMedianRecovery.Guided.Realized
variable {S A Ω : Type*} [Fintype A] [Fintype Ω]
lemma states_actions (f : S→A→S) (p : Kernel S A) (r : Draw (Ω:=Ω) p)
    (n : ℕ) (s : S) (bits : Fin n→Ω) (i : Fin (n+1)) :
    states f n s (actions f p r n s bits) i=
      states (fun s bit=>f s (r.run s bit)) n s bits i := by
  induction n generalizing s with
  | zero=>rfl
  | succ n ih=>
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · simpa only [actions,states,Fin.cases_succ,Fin.cons_zero,Fin.tail_cons]
        using ih (f s (r.run s (bits 0))) (Fin.tail bits) j
end MetricKMedianRecovery.Guided.Realized
namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine Guided FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma trace_average (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b t : ℕ)
    (hM : 0<M) (hJ : 0<J) (s : Option (State n)) (G : (Fin (t+1)→Option (Sampling.State (Fin n)))→ℝ) :
    average (fun seed : Fin t→Fin b→Bool=>G (fun i=>(((List.ofFn seed).take i.val).foldl
      (next δ D F S Δ P κ m M E J b) s).map State.real))=
      average (fun seed=>G (states (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J) t (s.map State.real)
        (FixedDyadic.actions (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J)
          (actualKernel D S (Δ:ℝ) M E J hM hJ) b (Sum.inl ()) t (s.map State.real) seed))) := by
  let f:=Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J
  let p:=actualKernel D S (Δ:ℝ) M E J hM hJ
  let r:=Realized.canonical p b (Sum.inl ()) (actions D M E J) (actions_perm D M E J)
  have he (seed : Fin t→Fin b→Bool) :
      (fun i:Fin (t+1)=>(((List.ofFn seed).take i.val).foldl (next δ D F S Δ P κ m M E J b) s).map State.real)=
        states f t (s.map State.real) (Realized.actions f (FixedDyadic.kernel p b (Sum.inl ())) r t (s.map State.real) seed) := by
    funext i
    rw [←states_list,Realized.states_actions]
    exact states_map (Option.map State.real) _ _ (next_real δ hδ D F S hD Δ P κ m M E J b) t s seed i
  simp only [he]
  exact Realized.canonical_law f p b (Sum.inl ()) (actions D M E J) (actions_perm D M E J) t (s.map State.real)
    (fun as=>G (states f t (s.map State.real) as))
lemma trace_probability_s238_oai (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b t : ℕ)
    (hM : 0<M) (hJ : 0<J) (s : Option (State n)) (G : (Fin (t+1)→Option (Sampling.State (Fin n)))→Prop) :
    probability (fun seed : Fin t→Fin b→Bool=>G (fun i=>(((List.ofFn seed).take i.val).foldl
      (next δ D F S Δ P κ m M E J b) s).map State.real))=
      probability (fun seed=>G (states (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J) t (s.map State.real)
        (FixedDyadic.actions (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J)
          (actualKernel D S (Δ:ℝ) M E J hM hJ) b (Sum.inl ()) t (s.map State.real) seed))) := by
  classical
  exact trace_average δ hδ D F S hD Δ P κ m M E J b t hM hJ s (fun z=>if G z then 1 else 0)
end MetricKMedianRecovery.RationalSampling

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238_oai := @OAI.MetricKMedianRecovery.RationalSampling.trace_probability_s238_oai
