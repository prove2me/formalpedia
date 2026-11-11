-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:32.875339+00:00
-- url     : https://prove2.me/submissions/cea2d48f-c2fe-4b61-b2c7-fd3428339915

import Mathlib
import Definitions.Def_Q238K022
import Definitions.Def_Q238K037
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLocalAnchor_run_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMetricAnchor_anchorInput_pack_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryProjection_run_setBits_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_IntegralAssembly_gamma_pos_s238
import Theorems.Thm_OAI_MetricKMedianRecovery_LocalSearch_local_five_approx_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_ClassSlotsMem
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [PseudoMetricSpace V]

variable [DecidableEq V]

omit [PseudoMetricSpace V] in
lemma exchange_diff_bounds (S R A : Finset V) :
    S \ ((S \ R) ∪ A) ⊆ R ∧ ((S \ R) ∪ A) \ S ⊆ A := by
  constructor
  · intro x hx
    by_contra hn
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,hn⟩))
  · intro x hx
    rcases Finset.mem_sdiff.mp hx with ⟨hxu,hxs⟩
    rcases Finset.mem_union.mp hxu with hx | hx
    · exact (hxs (Finset.mem_sdiff.mp hx).1).elim
    · exact hx

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SmallSubsets
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

lemma mem_smallSubsets (S R : Finset V) (w : ℕ) :
    R ∈ smallSubsets S w ↔ R ⊆ S ∧ R.card ≤ w := by
  simp only [smallSubsets,Finset.mem_biUnion,Finset.mem_range,Finset.mem_powersetCard]
  constructor
  · rintro ⟨r,hr,hRS,hR⟩
    exact ⟨hRS,by omega⟩
  · rintro ⟨hRS,hR⟩
    exact ⟨R.card,by omega,hRS,rfl⟩

lemma candidate_mem_self (F S : Finset V) (w : ℕ) : S ∈ exchangeCandidates F S w := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(∅,∅),?_,by simp⟩,rfl⟩
  apply Finset.mem_product.mpr
  constructor <;> apply (mem_smallSubsets _ _ w).mpr <;> simp

lemma candidate_properties (F S T : Finset V) (w : ℕ) (hSF : S ⊆ F)
    (hT : T ∈ exchangeCandidates F S w) :
    T ⊆ F ∧ T.card = S.card ∧ (S \ T).card ≤ w ∧ (T \ S).card ≤ w := by
  rcases Finset.mem_filter.mp hT with ⟨hm,hcard⟩
  rcases Finset.mem_image.mp hm with ⟨⟨R,A⟩,hra,rfl⟩
  rcases Finset.mem_product.mp hra with ⟨hr,ha⟩
  rcases (mem_smallSubsets _ _ _).mp hr with ⟨hRS,hrc⟩
  rcases (mem_smallSubsets _ _ _).mp ha with ⟨hAF,hac⟩
  have hdiff := exchange_diff_bounds S R A
  exact ⟨Finset.union_subset (Finset.sdiff_subset.trans hSF) hAF,hcard,
    (Finset.card_le_card hdiff.1).trans hrc,(Finset.card_le_card hdiff.2).trans hac⟩

lemma candidate_of_exchange (F S T : Finset V) (w : ℕ) (hTF : T ⊆ F)
    (hcard : T.card = S.card) (hR : (S \ T).card ≤ w) (hA : (T \ S).card ≤ w) :
    T ∈ exchangeCandidates F S w := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(S \ T,T \ S),?_,?_⟩,hcard⟩
  · exact Finset.mem_product.mpr ⟨(mem_smallSubsets _ _ _).mpr ⟨Finset.sdiff_subset,hR⟩,
      (mem_smallSubsets _ _ _).mpr ⟨Finset.sdiff_subset.trans hTF,hA⟩⟩
  · ext x
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_NatConnection
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

variable [PseudoMetricSpace V]

omit [DecidableEq V] in
lemma natConnection_cast (δ : V → V → ℕ) (F S : Finset V) (p : V)
    (hSF : S ⊆ F) (hδ : ∀ i ∈ F, (δ p i : ℝ) = dist p i) :
    (natConnection δ S p : ℝ) = connection S p := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi,heq⟩ := Finset.exists_mem_eq_inf' hS (δ p)
    have hmin : ∀ j ∈ S, δ p i ≤ δ p j := by
      intro j hj
      rw [←heq]
      exact Finset.inf'_le _ hj
    simp only [natConnection,connection,dite_eq_left hS]
    rw [heq,hδ i (hSF hi)]
    apply le_antisymm
    · apply Finset.le_inf' hS _
      intro j hj
      have hh : (δ p i : ℝ) ≤ (δ p j : ℝ) := by exact_mod_cast hmin j hj
      simpa only [hδ i (hSF hi),hδ j (hSF hj)] using hh
    · exact Finset.inf'_le _ hi
  · simp only [natConnection,connection,dite_eq_right hS,Nat.cast_zero]

omit [DecidableEq V] in
lemma natCost_cast (δ : V → V → ℕ) (F D S : Finset V) (hSF : S ⊆ F)
    (hδ : ∀ p ∈ D, ∀ i ∈ F, (δ p i : ℝ) = dist p i) :
    (natCost δ D S : ℝ) = cost D S := by
  unfold natCost cost
  push_cast
  exact Finset.sum_congr rfl (fun p hp => natConnection_cast δ F S p hSF (hδ p hp))

omit [PseudoMetricSpace V] [DecidableEq V] in
lemma natCost_le (δ : V → V → ℕ) (F D S : Finset V) (hSF : S ⊆ F)
    (M : ℕ) (hM : ∀ p ∈ D, ∀ i ∈ F, δ p i ≤ M) : natCost δ D S ≤ D.card*M := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨i,hi⟩ := hS
    have hS : S.Nonempty := ⟨i,hi⟩
    calc
      _ ≤ ∑ _p ∈ D, M := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [natConnection,dite_eq_left hS]
        exact (Finset.inf'_le _ hi).trans (hM p hp i (hSF hi))
      _ = _ := by simp
  · simp [natCost,natConnection,hS]

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [DecidableEq V]

lemma mem_widthLists (fs : List V) (w : ℕ) (R : Finset V) :
    R ∈ widthLists fs w ↔ R ⊆ fs.toFinset ∧ R.card ≤ w := by
  induction w generalizing R with
  | zero =>
    constructor
    · intro h
      have he : R = ∅ := by simpa only [widthLists,List.mem_singleton] using h
      subst R
      simp
    · rintro ⟨_,hc⟩
      have he : R = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hc)
      simp only [widthLists,List.mem_singleton,he]
  | succ w ih =>
    simp only [widthLists,List.mem_append,List.mem_flatMap,List.mem_map]
    constructor
    · rintro (h | ⟨i,hi,T,hT,rfl⟩)
      · exact ⟨(ih R).mp h |>.1, Nat.le_succ_of_le ((ih R).mp h |>.2)⟩
      · rcases (ih T).mp hT with ⟨hTF,hTw⟩
        exact ⟨Finset.insert_subset (List.mem_toFinset.mpr hi) hTF,
          (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hTw 1)⟩
    · rintro ⟨hRF,hRw⟩
      by_cases hc : R.card ≤ w
      · exact Or.inl ((ih R).mpr ⟨hRF,hc⟩)
      · have hR : R.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨i,hi⟩ := hR
        refine Or.inr ⟨i,List.mem_toFinset.mp (hRF hi),R.erase i,?_,Finset.insert_erase hi⟩
        apply (ih (R.erase i)).mpr
        exact ⟨Finset.erase_subset _ _ |>.trans hRF,by rw [Finset.card_erase_of_mem hi]; omega⟩

omit [DecidableEq V] in
lemma listBest_mem (rank : V → ℕ) (seed : V) (xs : List V) :
    listBest rank seed xs = seed ∨ listBest rank seed xs ∈ xs := by
  induction xs generalizing seed with
  | nil => exact Or.inl rfl
  | cons a xs ih =>
    unfold listBest
    rcases ih (if rank a < rank seed then a else seed) with h | h
    · rw [h]
      split_ifs
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)

omit [DecidableEq V] in
lemma listBest_le (rank : V → ℕ) (seed : V) (xs : List V) :
    rank (listBest rank seed xs) ≤ rank seed ∧ ∀ a ∈ xs, rank (listBest rank seed xs) ≤ rank a := by
  induction xs generalizing seed with
  | nil => simp [listBest]
  | cons a xs ih =>
    have hh := ih (if rank a < rank seed then a else seed)
    have hs : rank (if rank a < rank seed then a else seed) ≤ rank seed := by
      split_ifs with h
      · exact h.le
      · exact le_rfl
    have ha : rank (if rank a < rank seed then a else seed) ≤ rank a := by
      split_ifs with h
      · exact le_rfl
      · exact le_of_not_gt h
    refine ⟨hh.1.trans hs,?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hh.1.trans ha
    · exact hh.2 b hb

omit [DecidableEq V] in
lemma listBest_fixed (rank : V → ℕ) (seed : V) (xs : List V)
    (h : ∀ a ∈ xs, rank seed ≤ rank a) : listBest rank seed xs = seed := by
  induction xs generalizing seed with
  | nil => rfl
  | cons a xs ih =>
    have ha : ¬rank a < rank seed := not_lt.mpr (h a (List.mem_cons_self ..))
    simp only [listBest,ite_eq_right ha]
    exact ih seed (fun b hb => h b (List.mem_cons_of_mem _ hb))

lemma mem_exchangeList (fs : List V) (S T : Finset V) (w : ℕ) (hSF : S ⊆ fs.toFinset) :
    T ∈ exchangeList fs S w ↔ T ∈ exchangeCandidates fs.toFinset S w := by
  simp only [exchangeList,List.mem_filter,List.mem_flatMap,List.mem_map,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨R,hR,A,hA,rfl⟩,hcard⟩
    rcases (mem_widthLists fs w R).mp hR with ⟨_,hRw⟩
    rcases (mem_widthLists fs w A).mp hA with ⟨hAF,hAw⟩
    have hd := exchange_diff_bounds S R A
    exact candidate_of_exchange _ _ _ _
      (Finset.union_subset (Finset.sdiff_subset.trans hSF) hAF) hcard
      ((Finset.card_le_card hd.1).trans hRw) ((Finset.card_le_card hd.2).trans hAw)
  · intro h
    have hp := candidate_properties _ _ _ _ hSF h
    refine ⟨⟨S \ T,(mem_widthLists fs w _).mpr ⟨Finset.sdiff_subset.trans hSF,hp.2.2.1⟩,
      T \ S,(mem_widthLists fs w _).mpr ⟨Finset.sdiff_subset.trans hp.1,hp.2.2.2⟩,?_⟩,hp.2.1⟩
    ext i
    simp only [Finset.mem_union,Finset.mem_sdiff]
    tauto

lemma executableStep_mem (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V)
    (hSF : S ⊆ fs.toFinset) : executableStep fs rank w S ∈ exchangeCandidates fs.toFinset S w := by
  rcases listBest_mem rank S (exchangeList fs S w) with h | h
  · change listBest rank S (exchangeList fs S w) ∈ _
    rw [h]
    exact candidate_mem_self fs.toFinset S w
  · exact (mem_exchangeList fs S _ w hSF).mp h

lemma executableStep_min (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S T : Finset V)
    (hSF : S ⊆ fs.toFinset) (hT : T ∈ exchangeCandidates fs.toFinset S w) :
    rank (executableStep fs rank w S) ≤ rank T :=
  (listBest_le rank S (exchangeList fs S w)).2 T ((mem_exchangeList fs S T w hSF).mpr hT)

lemma executableStep_mono (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V) :
    rank (executableStep fs rank w S) ≤ rank S := (listBest_le ..).1

lemma executableStep_fixed (fs : List V) (rank : Finset V → ℕ) (w : ℕ) (S : Finset V)
    (hSF : S ⊆ fs.toFinset)
    (h : ∀ T ∈ exchangeCandidates fs.toFinset S w, rank S ≤ rank T) :
    executableStep fs rank w S = S := by
  apply listBest_fixed
  intro T hT
  exact h T ((mem_exchangeList fs S T w hSF).mp hT)

lemma executableDescent_properties (fs : List V) (rank : Finset V → ℕ) (w n : ℕ)
    (S : Finset V) (hSF : S ⊆ fs.toFinset) :
    executableDescent fs rank w n S ⊆ fs.toFinset ∧
      (executableDescent fs rank w n S).card = S.card ∧
      rank (executableDescent fs rank w n S) ≤ rank S := by
  induction n generalizing S with
  | zero => exact ⟨hSF,rfl,le_rfl⟩
  | succ n ih =>
    have hp := candidate_properties _ _ _ _ hSF (executableStep_mem fs rank w S hSF)
    have hh := ih (executableStep fs rank w S) hp.1
    exact ⟨hh.1,hh.2.1.trans hp.2.1,hh.2.2.trans (executableStep_mono ..)⟩

lemma executableDescent_fixed (fs : List V) (rank : Finset V → ℕ) (w n : ℕ) (S : Finset V)
    (h : executableStep fs rank w S = S) : executableDescent fs rank w n S = S := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [executableDescent,h] using ih

theorem executableDescent_min (fs : List V) (rank : Finset V → ℕ) (w n : ℕ)
    (S : Finset V) (hSF : S ⊆ fs.toFinset) (hn : rank S ≤ n) :
    ∀ T ∈ exchangeCandidates fs.toFinset (executableDescent fs rank w n S) w,
      rank (executableDescent fs rank w n S) ≤ rank T := by
  induction n generalizing S with
  | zero =>
    intro T _
    change rank S ≤ rank T
    omega
  | succ n ih =>
    by_cases hlocal : ∀ T ∈ exchangeCandidates fs.toFinset S w, rank S ≤ rank T
    · rw [executableDescent_fixed fs rank w (n+1) S (executableStep_fixed fs rank w S hSF hlocal)]
      exact hlocal
    · push Not at hlocal
      obtain ⟨T,hT,ht⟩ := hlocal
      have hs := (executableStep_min fs rank w S T hSF hT).trans_lt ht
      have hp := candidate_properties _ _ _ _ hSF (executableStep_mem fs rank w S hSF)
      exact ih _ hp.1 (by omega)

end MetricKMedianRecovery.LocalSearch

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

omit [MetricSpace V] in
lemma seed_card (fs : List V) (r : ℕ) (hfs : fs.Nodup) (hr : r ≤ fs.length) :
    (fs.take r).toFinset.card = r := by
  rw [List.toFinset_card_of_nodup (hfs.take),List.length_take,Nat.min_eq_left hr]

omit [MetricSpace V] in
lemma seed_subset (fs : List V) (r : ℕ) : (fs.take r).toFinset ⊆ fs.toFinset := by
  intro i hi
  exact List.mem_toFinset.mpr (List.mem_of_mem_take (List.mem_toFinset.mp hi))

end MetricKMedianRecovery.LocalSearch

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_PolynomialProduct
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.GlobalAssembly

open LocalSearch Sampling FiniteSampling IntegralAssembly IndexedCopies

lemma cap_polynomial (n N : ℕ) (h : n ≤ N) :
    Rounding.cap n (gamma/16) ≤ (⌈20/(gamma/16)⌉₊+2)*(N+2)^2 := by
  have he : 0 < gamma/16 := div_pos gamma_pos_s238 (by norm_num)
  have hn : (n:ℝ)^2 ≤ ((N:ℝ)+2)^2 := by
    have h' : (n:ℝ) ≤ N := by exact_mod_cast h
    nlinarith [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) N]
  have hc : ⌈20*(n:ℝ)^2/(gamma/16)⌉₊ ≤ ⌈20/(gamma/16)⌉₊*(N+2)^2 := by
    apply Nat.ceil_le.mpr
    push_cast
    calc
      _ = (20/(gamma/16))*(n:ℝ)^2 := by ring
      _ ≤ (20/(gamma/16))*((N:ℝ)+2)^2 := mul_le_mul_of_nonneg_left hn (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (sq_nonneg _)
  have hb : 1 ≤ (N+2)^2 := one_le_pow₀ (by omega)
  unfold Rounding.cap
  nlinarith

end MetricKMedianRecovery.GlobalAssembly

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_LocalFuel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open WordOperations WordList BinaryArithmetic RationalLeaves Polynomial
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] Take.run BinaryLabel.sort
lemma fuel_bound {m d : ℕ} (distance : Fin m→Fin d→ℚ) (fs : List (Fin m)) (r : ℕ) :
    d*Rounding.cap d (IntegralAssembly.gamma/16) ≤ (fuelPoly.eval (pack distance fs r).length) := by
  let L := (pack distance fs r).length
  have hd : d≤L := by
    simp only [L,pack,length_encode,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil,List.length_replicate]
    omega
  have hc := GlobalAssembly.cap_polynomial d L hd
  have hdl : d≤L+2 := by omega
  change d*Rounding.cap d (IntegralAssembly.gamma/16)≤fuelPoly.eval L
  calc
    _ ≤ (L+2)*((⌈20/(IntegralAssembly.gamma/16)⌉₊+2)*(L+2)^2) := Nat.mul_le_mul hdl hc
    _ = _ := by simp only [fuelPoly,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_ofNat] <;> ring
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

namespace MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]
lemma executableAnchorFuel_spec (δ : V→V→ℕ) (fs : List V) (D : Finset V) (r n M : ℕ)
    (hfs : fs.Nodup) (hr : 0 < r) (hrF : r≤fs.length)
    (hδ : ∀ p∈D,∀ i∈fs.toFinset,(δ p i:ℝ)=dist p i)
    (hM : ∀ p∈D,∀ i∈fs.toFinset,δ p i≤M) (hn : D.card*M≤n) :
    let S := executableDescent fs (natCost δ D) 5 n (fs.take r).toFinset
    S⊆fs.toFinset ∧ S.Nonempty ∧ S.card=r ∧ WidthLocalMin fs.toFinset D S 5 ∧
      ∀ O : Finset V,O.Nonempty→O⊆fs.toFinset→O.card ≤ r→cost D S≤5*cost D O := by
  dsimp only
  let S := executableDescent fs (natCost δ D) 5 n (fs.take r).toFinset
  have hp := executableDescent_properties fs (natCost δ D) 5 n (fs.take r).toFinset (seed_subset fs r)
  have hc : S.card=r:=hp.2.1.trans (seed_card fs r hfs hrF)
  have hs : S.Nonempty:=Finset.card_pos.mp (by rw [hc]; exact hr)
  have hm := executableDescent_min fs (natCost δ D) 5 n (fs.take r).toFinset (seed_subset fs r)
    ((natCost_le δ fs.toFinset D _ (seed_subset fs r) M hM).trans hn)
  have hlocal : WidthLocalMin fs.toFinset D S 5 := by
    intro U hUF hcard hrem hadd
    rw [←natCost_cast δ fs.toFinset D S hp.1 hδ,←natCost_cast δ fs.toFinset D U hUF hδ]
    exact_mod_cast hm U (candidate_of_exchange _ _ _ _ hUF hcard hrem hadd)
  refine ⟨hp.1,hs,hc,hlocal,?_⟩
  intro O hO hOF hOr
  exact local_five_approx_s238 _ _ _ O hs hO hp.1 hlocal hOF (by rw [hc]; exact hOr)
end MetricKMedianRecovery.LocalSearch

namespace MetricKMedianRecovery.BitMachine.BinaryLocalAnchor
open RationalLeaves LocalSearch
lemma integral_spec {m d : ℕ} [MetricSpace (Fin m)] (δ : Fin m→Fin m→ℕ) (loc : Fin d→Fin m)
    (hloc : Function.Injective loc) (fs : List (Fin m)) (r : ℕ)
    (hfs : fs.Nodup) (hr : 0 < r) (hrF : r≤fs.length)
    (hδ : ∀ j,∀ i∈fs.toFinset,(δ (loc j) i:ℝ)=dist (loc j) i)
    (hM : ∀ j,∀ i∈fs.toFinset,δ (loc j) i≤Rounding.cap d (IntegralAssembly.gamma/16)) :
    ∃ S : Finset (Fin m),
      run (pack (fun i j=>(δ (loc j) i:ℚ)) fs r)=BinaryFiniteContext.setBits (S.image original) ∧
      S⊆fs.toFinset ∧ S.Nonempty ∧ S.card=r ∧ WidthLocalMin fs.toFinset (Finset.univ.image loc) S 5 ∧
      ∀ O : Finset (Fin m),O.Nonempty→O⊆fs.toFinset→O.card ≤ r→
        cost (Finset.univ.image loc) S≤5*cost (Finset.univ.image loc) O := by
  refine ⟨_,run_pack_s238 δ loc hloc fs r,?_⟩
  apply executableAnchorFuel_spec δ fs (Finset.univ.image loc) r _
    (Rounding.cap d (IntegralAssembly.gamma/16)) hfs hr hrF
  · intro p hp i hi
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hp
    exact hδ j i hi
  · intro p hp i hi
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hp
    exact hM j i hi
  · rw [Finset.card_image_of_injective _ hloc,Finset.card_univ,Fintype.card_fin]
    exact fuel_bound _ fs r
end MetricKMedianRecovery.BitMachine.BinaryLocalAnchor

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_SortedDual
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.SortedIndex
variable {V : Type*} [LinearOrder V]
lemma equiv_dual_val (D : Finset V) (i : Fin D.card) : (equiv_dual D i).val=enum D i := rfl
lemma enum_symm (D : Finset V) (j : D) : enum D ((equiv_dual D).symm j)=j.val := by
  rw [←equiv_dual_val,Equiv.apply_symm_apply]
lemma image_enum (D : Finset V) : Finset.univ.image (enum D)=D := by
  ext j
  constructor
  · intro hj
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hj
    exact enum_mem D i
  · intro hj
    exact Finset.mem_image.mpr ⟨(equiv_dual D).symm ⟨j,hj⟩,Finset.mem_univ _,enum_symm D ⟨j,hj⟩⟩
end MetricKMedianRecovery.SortedIndex

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_MetricAnchor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMetricAnchor
open WordOperations WordList RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryLocalAnchor.run BinaryProjection.run BinaryMetricArrays.run
variable {n : ℕ}
attribute [local irreducible] WordList.map
attribute [local semireducible] WordList.map
lemma produce_s238_oai [MetricSpace (Fin n)] (δ : Fin n→Fin n→ℕ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F : Finset (Fin n)) (r : ℕ) (hr : 0 < r) (hrF : r≤F.card)
    (hcap : ∀ p∈D,∀ i∈F,δ p i≤Rounding.cap D.card (IntegralAssembly.gamma/16)) :
    ∃ S : Finset (Fin n),run (pack (fun i j=>(δ i j:ℚ)) D F r)=BinaryFinSet.encode S ∧
      S⊆F ∧ S.Nonempty ∧ S.card=r ∧ LocalSearch.WidthLocalMin F D S 5 ∧
      ∀ O : Finset (Fin n),O.Nonempty→O⊆F→O.card ≤ r→LocalSearch.cost D S≤5*LocalSearch.cost D O := by
  have hsymm (i j : Fin n) : δ i j=δ j i := by
    exact_mod_cast ((hδ i j).trans ((dist_comm i j).trans (hδ j i).symm))
  obtain ⟨S,he,hSF,hS,hcard,hlocal,hcost⟩:=BinaryLocalAnchor.integral_spec (fun i j=>δ j i) (SortedIndex.enum D)
    (SortedIndex.enum_injective D) (F.sort (·≤·)) r (Finset.sort_nodup _ _) hr
    (by simpa only [Finset.length_sort] using hrF)
    (fun j i _=>(hδ i (SortedIndex.enum D j)).trans (dist_comm _ _))
    (fun j i hi=>by rw [hsymm i (SortedIndex.enum D j)]; exact hcap _ (SortedIndex.enum_mem D j) i (by simpa only [Finset.sort_toFinset] using hi))
  rw [SortedIndex.image_enum] at hlocal hcost
  refine ⟨S,?_,by simpa only [Finset.sort_toFinset] using hSF,hS,hcard,
    by simpa only [Finset.sort_toFinset] using hlocal,?_⟩
  · rw [run,Function.comp_apply,Function.comp_apply,anchorInput_pack_s238,he,BinaryProjection.run_setBits_s238]
    congr 1
    simp only [project,Finset.image_image]
    change S.image id=S
    exact Finset.image_id
  · intro O hO hOF hOr
    exact hcost O hO (by simpa only [Finset.sort_toFinset] using hOF) hOr
end MetricKMedianRecovery.BitMachine.BinaryMetricAnchor

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryMetricAnchor.produce_s238_oai
