-- Prove2me | solution 1 for OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:18:50.261018+00:00
-- url     : https://prove2.me/submissions/aafe2233-ee31-4651-b31e-33c3fc42ea36

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_ScoreGeometry_eventually_four_high_training_score

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Best
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {V I : Type*} [DecidableEq V] [LinearOrder I]

variable (F : Finset I) (hF : F.Nonempty) (shape : I → Finset V) (X : Finset V)

lemma remaining_succ_subset (k : ℕ) :
    remaining F hF shape X (k+1) ⊆ remaining F hF shape X k := Finset.sdiff_subset

lemma remaining_antitone : Antitone (remaining F hF shape X) :=
  antitone_nat_of_succ_le (remaining_succ_subset F hF shape X)

lemma remaining_subset (k : ℕ) : remaining F hF shape X k ⊆ X :=
  remaining_antitone F hF shape X (Nat.zero_le k)

lemma cell_subset (k : ℕ) : cell F hF shape X k ⊆ remaining F hF shape X k :=
  Finset.inter_subset_left

lemma cell_disjoint_of_lt {i j : ℕ} (hij : i < j) :
    Disjoint (cell F hF shape X i) (cell F hF shape X j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hx : x ∈ remaining F hF shape X (i+1) :=
    remaining_antitone F hF shape X hij (cell_subset F hF shape X j hxj)
  have hxnot := (Finset.mem_sdiff.mp hx).2
  exact hxnot (Finset.mem_inter.mp hxi).2

lemma before_stop (threshold : ℕ) (hthreshold : 0 < threshold) {j : ℕ}
    (hj : j < stopIndex F hF shape X threshold hthreshold) :
    (cell F hF shape X j).card ≥ threshold ∧
      2*(X.card-(remaining F hF shape X j).card) < X.card := by
  have h := Nat.find_min (Exists.imp (fun _ hk => hk.2)
    (exists_stop F hF shape X threshold hthreshold)) hj
  simpa only [Stop, not_or, not_le, not_lt, and_comm] using h

lemma list_length_bound (threshold : ℕ) (hthreshold : 0 < threshold) :
    stopIndex F hF shape X threshold hthreshold * threshold ≤ X.card := by
  let J := stopIndex F hF shape X threshold hthreshold
  change J*threshold ≤ X.card
  have hs := Finset.sum_le_sum (s := Finset.range J) (fun j hj =>
    (before_stop F hF shape X threshold hthreshold (Finset.mem_range.mp hj)).1)
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  have hc := sum_card_add_remaining F hF shape X J
  omega

lemma retained_subset (threshold : ℕ) (hthreshold : 0 < threshold) :
    retained F hF shape X threshold hthreshold ⊆ X := by
  unfold retained
  split
  · exact Finset.sdiff_subset
  · exact remaining_subset F hF shape X _

lemma retained_half (threshold : ℕ) (hthreshold : 0 < threshold) :
    X.card ≤ 2*(retained F hF shape X threshold hthreshold).card := by
  have hsub := Finset.card_le_card (remaining_subset F hF shape X
    (stopIndex F hF shape X threshold hthreshold))
  unfold retained
  split
  · rename_i h
    rw [Finset.card_sdiff_of_subset (remaining_subset F hF shape X _)]
    exact h
  · rename_i h
    omega

lemma remaining_eq_sdiff_union (k : ℕ) :
    remaining F hF shape X k = X \ (Finset.range k).biUnion (fun j => shape (chosen F hF shape X j)) := by
  induction k with
  | zero => simp [remaining]
  | succ k ih =>
    change remaining F hF shape X k \ shape (chosen F hF shape X k) = _
    rw [ih]
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range]
    change (x ∈ X ∧ ¬∃ j < k, x ∈ shape (chosen F hF shape X j)) ∧
        x ∉ shape (chosen F hF shape X k) ↔
      x ∈ X ∧ ¬∃ j < k+1, x ∈ shape (chosen F hF shape X j)
    constructor
    · rintro ⟨⟨hx,hn⟩,hk⟩
      refine ⟨hx,?_⟩
      rintro ⟨j,hj,hxj⟩
      rcases (Nat.lt_succ_iff_lt_or_eq.mp hj) with hj | rfl
      · exact hn ⟨j,hj,hxj⟩
      · exact hk hxj
    · rintro ⟨hx,hn⟩
      refine ⟨⟨hx,?_⟩,?_⟩
      · rintro ⟨j,hj,hxj⟩
        exact hn ⟨j,Nat.lt_succ_of_lt hj,hxj⟩
      · intro hxk
        exact hn ⟨k,Nat.lt_succ_self k,hxk⟩

lemma cell_earliest (j : ℕ) (x : V) :
    x ∈ cell F hF shape X j ↔
      x ∈ X ∧ x ∈ shape (chosen F hF shape X j) ∧ ∀ i < j, x ∉ shape (chosen F hF shape X i) := by
  unfold cell
  rw [Finset.mem_inter, remaining_eq_sdiff_union]
  simp only [Finset.mem_sdiff, Finset.mem_biUnion, Finset.mem_range, not_exists, not_and]
  tauto

lemma firstAt_mem (J : ℕ) (x : V) (h : firstAt F hF shape X J x < J) :
    x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) := by
  have hs := Nat.find_spec (show ∃ j, J ≤ j ∨ x ∈ shape (chosen F hF shape X j) from ⟨J,Or.inl le_rfl⟩)
  change J ≤ firstAt F hF shape X J x ∨ x ∈ shape (chosen F hF shape X (firstAt F hF shape X J x)) at hs
  exact hs.resolve_left (not_le_of_gt h)

lemma firstAt_eq (J j : ℕ) (x : V) (hj : j < J)
    (hxj : x ∈ shape (chosen F hF shape X j))
    (hearlier : ∀ i < j, x ∉ shape (chosen F hF shape X i)) :
    firstAt F hF shape X J x = j := by
  apply le_antisymm
  · exact Nat.find_min' _ (Or.inr hxj)
  · by_contra hn
    have hlt : firstAt F hF shape X J x < j := by omega
    exact hearlier _ hlt (firstAt_mem F hF shape X J x (hlt.trans hj))

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Beta
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics
open scoped Topology

lemma beta_pos {η : ℝ} (h : 0 < η) : 0 < beta η := by unfold beta; positivity

lemma finite_bounds {η σ D R : ℝ} (hη : 0 < η) (_hη' : η < 1/10)
    (hσ : 1 ≤ σ) (h : Range η σ D R) :
    0 < D ∧ 0 < R ∧ 1 ≤ σ ^ beta η ∧
    σ ^ (9 * beta η) ≤ L η σ D ∧ L η σ D ≤ σ ∧
    σ ^ (10 * beta η) ≤ P η σ D R ∧
    P η σ D R ≤ 4 * σ ^ (1 - η/2 + 9 * beta η) := by
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hb : 0 < beta η := beta_pos hη
  have hx : 1 ≤ σ ^ beta η := Real.one_le_rpow hσ hb.le
  have hd : 0 < D := (Real.rpow_pos_of_pos hs _).trans_le h.dlo
  have hr : 0 < R := (Real.rpow_pos_of_pos hs _).trans_le h.rlo
  have hlo : σ ^ (9 * beta η) ≤ L η σ D := by
    dsimp [L]
    calc
      _ = σ ^ beta η * σ ^ (8 * beta η) := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h.dlo (Real.rpow_nonneg hs.le _)
  have hhi : L η σ D ≤ σ := by
    dsimp [L]
    calc
      _ ≤ σ ^ (1-η/2) * σ ^ (8*beta η) := mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)
      _ = σ ^ (1-η/2+8*beta η) := (Real.rpow_add hs _ _).symm
      _ ≤ σ ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hσ (by dsimp [beta]; linarith)
      _ = σ := Real.rpow_one _
  refine ⟨hd,hr,hx,hlo,hhi,?_,?_⟩
  · calc
      _ = σ ^ (9*beta η) * σ ^ beta η := by rw [← Real.rpow_add hs]; congr 1; ring
      _ ≤ L η σ D * R := mul_le_mul hlo h.rlo (Real.rpow_nonneg hs.le _) (by dsimp [L]; positivity)
  · have hR : R ≤ 4 * σ ^ beta η := h.rhi.trans (by linarith)
    calc
      _ ≤ (σ ^ (1-η/2) * σ ^ (8*beta η)) * (4*σ ^ beta η) := by
        dsimp [P,L]
        exact mul_le_mul (mul_le_mul_of_nonneg_right h.dhi (Real.rpow_nonneg hs.le _)) hR hr.le (by positivity)
      _ = 4 * σ ^ (1-η/2+9*beta η) := by
        rw [show σ ^ (1-η/2) * σ ^ (8*beta η) * (4*σ ^ beta η) =
          4 * ((σ ^ (1-η/2) * σ ^ (8*beta η)) * σ ^ beta η) by ring,
          ← Real.rpow_add hs, ← Real.rpow_add hs]
        congr 2
        ring

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_Training
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

lemma peel_subset (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelSet e F hF shape X k hk ⊆ X := by
  unfold peelSet
  split_ifs
  · exact retained_subset F hF shape X k hk
  · exact Finset.Subset.refl _

lemma peel_half (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    X.card≤2*(peelSet e F hF shape X k hk).card := by
  unfold peelSet
  split_ifs
  · exact retained_half F hF shape X k hk
  · omega

lemma peel_length_bound (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (k : ℕ) (hk : 0<k) :
    peelLength e F hF shape X k hk*k≤X.card := by
  unfold peelLength
  split_ifs
  · exact list_length_bound F hF shape X k hk
  · simp

lemma peel_length_real (e : Prop) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (t : ℝ) (ht : 0<t) :
    (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht):ℝ)*t≤X.card := by
  have hi := peel_length_bound e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  calc
    _ ≤ (peelLength e F hF shape X ⌈t⌉₊ (Nat.ceil_pos.mpr ht):ℝ)*⌈t⌉₊ :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil t) (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast hi

lemma clippedPart_subset (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (i : Option (Fin J)) :
    clippedPart S F hF shape X J i⊆S := by
  cases i
  · exact Finset.empty_subset _
  · exact Finset.inter_subset_left

lemma clippedPart_disjoint (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) :
    Pairwise (fun i j => Disjoint (clippedPart S F hF shape X J i) (clippedPart S F hF shape X J j)) := by
  intro i j hij
  cases i with
  | none => simp [clippedPart]
  | some i =>
    cases j with
    | none => simp [clippedPart]
    | some j =>
      have hneq : i≠j := by simpa only [ne_eq,Option.some.injEq] using hij
      have hv : i.val≠j.val := fun hh => hneq (Fin.ext hh)
      rcases lt_or_gt_of_ne hv with h|h
      · exact (cell_disjoint_of_lt F hF shape X h).mono Finset.inter_subset_right Finset.inter_subset_right
      · exact (cell_disjoint_of_lt F hF shape X h).symm.mono Finset.inter_subset_right Finset.inter_subset_right

lemma clippedPart_query (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (x : A) :
    clippedPart S F hF shape X J (queryPart F hF shape X J x)=S∩ownCell F hF shape X J x := by
  unfold queryPart ownCell
  split_ifs with h
  · rfl
  · simp [clippedPart]

end SharpRamseyFive.GreedyTraining

namespace SharpRamseyFive.TrainingCells
open scoped BigOperators Classical
variable {A H P : Type*} [DecidableEq A] [Fintype H] [Fintype P]

lemma sum_card_le (S : Finset A) {J : Type*} [Fintype J] (C : J→Finset A)
    (hsub : ∀j,C j⊆S) (hdis : Pairwise (fun i j => Disjoint (C i) (C j))) :
    (∑j,(C j).card)≤S.card := by
  have hpair : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint C :=
    fun i _ j _ hij => hdis hij
  rw [←Finset.card_biUnion hpair]
  exact Finset.card_le_card (Finset.biUnion_subset.mpr fun j _ => hsub j)

omit [Fintype H] [Fintype P] in
lemma inter_disjoint (C : H→Finset A) (D : P→Finset A)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j))) (hD : Pairwise (fun i j => Disjoint (D i) (D j))) :
    Pairwise (fun ij kl : H×P => Disjoint (C ij.1∩D ij.2) (C kl.1∩D kl.2)) := by
  intro ij kl hne
  by_cases hi : ij.1=kl.1
  · have hj : ij.2≠kl.2 := fun hh => hne (Prod.ext hi hh)
    exact (hD hj).mono Finset.inter_subset_right Finset.inter_subset_right
  · exact (hC hi).mono Finset.inter_subset_left Finset.inter_subset_left

lemma family_mass (S : Finset A) (C : H→Finset A) (D : P→Finset A)
    (hC : ∀i,C i⊆S) (hD : ∀j,D j⊆S)
    (hdC : Pairwise (fun i j => Disjoint (C i) (C j))) (hdD : Pairwise (fun i j => Disjoint (D i) (D j))) :
    (∑i,(family C D i).card)≤3*S.card := by
  have h₁ := sum_card_le S C hC hdC
  have h₂ := sum_card_le S D hD hdD
  have h₃ := sum_card_le S (fun ij : H×P => C ij.1∩D ij.2)
    (fun ij => Finset.inter_subset_left.trans (hC ij.1)) (inter_disjoint C D hdC hdD)
  simp only [Fintype.sum_sum_type,family]
  omega

omit [Fintype H] [Fintype P] in
lemma family_subsets (S : Finset A) (C : H→Finset A) (D : P→Finset A)
    (hC : ∀i,C i⊆S) (hD : ∀j,D j⊆S) (i : H⊕P⊕(H×P)) : family C D i⊆S := by
  rcases i with i | j | ij
  · exact hC i
  · exact hD j
  · exact Finset.inter_subset_left.trans (hC ij.1)

end SharpRamseyFive.TrainingCells

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MeasurePublicTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.MeasurePublicTable
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical
variable {α : Type*}

lemma firstIndex_none_iff (E : Set α) {N : ℕ} (t : Fin N→α) :
    firstIndex E t=none ↔ ∀i,t i∉E := by
  unfold firstIndex
  split_ifs with h
  · simp only [false_iff]
    simpa only [Finset.nonempty_def,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_not] using h
  · simp only [true_iff]
    simpa only [Finset.not_nonempty_iff_eq_empty,Finset.filter_eq_empty_iff,Finset.mem_univ,true_implies] using h

lemma firstIndex_some_mem (E : Set α) {N : ℕ} (t : Fin N→α) {i : Fin N}
    (hi : firstIndex E t=some i) : t i∈E := by
  unfold firstIndex at hi
  split_ifs at hi with h
  · have he := Option.some.inj hi
    have hm := Finset.min'_mem (Finset.univ.filter (fun i=>t i∈E)) h
    rw [he] at hm
    exact (Finset.mem_filter.mp hm).2

lemma firstIndex_minimal (E : Set α) {N : ℕ} (t : Fin N→α) {i : Fin N}
    (hi : firstIndex E t=some i) : ∀ j, j < i → t j∉E := by
  unfold firstIndex at hi
  split_ifs at hi with h
  · have he := Option.some.inj hi
    intro j hj hE
    have hh := Finset.min'_le (Finset.univ.filter (fun i=>t i∈E)) j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hE⟩)
    rw [he] at hh
    exact (not_le_of_gt hj) hh

variable [MeasurableSpace α]

lemma firstIndex_failure_mass (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N : ℕ) :
    (Measure.pi (fun _ : Fin N=>μ)).real {t | firstIndex E t=none}=(1-μ.real E)^N := by
  have he : {t : Fin N→α | firstIndex E t=none}=Set.univ.pi (fun _=>Eᶜ) := by
    ext t
    simp only [Set.mem_ofPred_eq,firstIndex_none_iff,Set.mem_univ_pi,Set.mem_compl_iff]
  rw [he,measureReal_def,Measure.pi_pi,ENNReal.toReal_prod]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [←measureReal_def,measureReal_compl hE]
  simp

lemma firstIndex_failure_le (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) (N : ℕ) {p : ℝ} (hp : p≤μ.real E) :
    (Measure.pi (fun _ : Fin N=>μ)).real {t | firstIndex E t=none}≤Real.exp (-p*N) := by
  rw [firstIndex_failure_mass μ E hE N]
  have hbase : 1-μ.real E≤Real.exp (-p) := by
    have hh := Real.add_one_le_exp (-p)
    linarith
  calc
    _ ≤ (Real.exp (-p))^N := pow_le_pow_left₀ (sub_nonneg.mpr (measureReal_le_one)) hbase N
    _ = _ := by rw [←Real.exp_nat_mul];congr 1;ring

theorem finite_cutoff_failure (μ : Measure α) [IsProbabilityMeasure μ]
    (E : Set α) (hE : MeasurableSet E) {A q : ℝ} (_hq : 0≤q) (N : ℕ)
    (hp : Real.exp (-A)≤μ.real E) (hN : q*Real.exp A≤N) :
    (Measure.pi (fun _ : Fin N=>μ)).real {t | firstIndex E t=none}≤Real.exp (-q) := by
  apply (firstIndex_failure_le μ E hE N hp).trans
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (-A))
  have he : Real.exp (-A)*(q*Real.exp A)=q := by
    rw [mul_left_comm,←Real.exp_add]
    simp
  rw [he] at hh
  linarith

end SharpRamseyFive.MeasurePublicTable

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_PublicTraining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.GreedyTraining

section
open MeasurePublicTable
open scoped BigOperators Classical
variable {A I : Type*} [DecidableEq A] [LinearOrder I]

lemma firstIndex_greedyList (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (J : ℕ) (x : A) :
    firstIndex {B | x∈B} (greedyList F hF shape X J)=queryPart F hF shape X J x := by
  cases he : firstIndex {B | x∈B} (greedyList F hF shape X J) with
  | none =>
    have hh := (firstIndex_none_iff _ _).mp he
    unfold queryPart
    have hn : ¬firstAt F hF shape X J x<J := by
      intro h
      exact hh ⟨_,h⟩ (firstAt_mem F hF shape X J x h)
    rw [dite_eq_right hn]
  | some i =>
    have hm := firstIndex_some_mem _ _ he
    have hmin := firstIndex_minimal _ _ he
    have hf : firstAt F hF shape X J x=i.val := by
      apply firstAt_eq F hF shape X J i.val x i.prop hm
      intro j hj
      exact hmin ⟨j,hj.trans i.prop⟩ hj
    unfold queryPart
    simp only [hf,dite_eq_left i.prop]

lemma region_cell (F : Finset I) (hF : F.Nonempty) (shape : I→Finset A)
    (X : Finset A) (J : ℕ) (i : Fin J) :
    X∩publicRegion (greedyList F hF shape X J) i=cell F hF shape X i := by
  ext x
  rw [cell_earliest]
  rw [Finset.mem_inter]
  change (x∈X ∧ x∈(shape (chosen F hF shape X i)).filter (fun x => ∀ j : Fin J, j < i → x∉shape (chosen F hF shape X j))) ↔ _
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hx,hm,he⟩
    refine ⟨hx,hm,fun j hj=>he ⟨j,hj.trans i.prop⟩ hj⟩
  · rintro ⟨hx,hm,he⟩
    exact ⟨hx,hm,fun j hj=>he j.val hj⟩

lemma clipped_publicOwn (S : Finset A) (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (hSX : S⊆X) (J : ℕ) (x : A) :
    S∩publicOwn (greedyList F hF shape X J) x=
      clippedPart S F hF shape X J (queryPart F hF shape X J x) := by
  unfold publicOwn
  rw [firstIndex_greedyList]
  cases he : queryPart F hF shape X J x with
  | none => simp [clippedPart]
  | some i =>
    change S∩publicRegion (greedyList F hF shape X J) i=S∩cell F hF shape X i
    rw [←region_cell F hF shape X J i,←Finset.inter_assoc,Finset.inter_eq_left.mpr hSX]

lemma ownCell_subset_publicOwn (F : Finset I) (hF : F.Nonempty)
    (shape : I→Finset A) (X : Finset A) (J : ℕ) (x : A) :
    ownCell F hF shape X J x⊆publicOwn (greedyList F hF shape X J) x := by
  have hh := clipped_publicOwn X F hF shape X (Finset.Subset.refl _) J x
  rw [clippedPart_query] at hh
  have hc : ownCell F hF shape X J x⊆X := by
    unfold ownCell
    split_ifs
    · exact (cell_subset F hF shape X _).trans (remaining_subset F hF shape X _)
    · exact Finset.empty_subset _
  rw [Finset.inter_eq_right.mpr hc] at hh
  exact hh▸Finset.inter_subset_right

end

open TrainingCells
open scoped Classical BigOperators
variable {A I J : Type*} [DecidableEq A] [LinearOrder I] [LinearOrder J]

theorem literal_cell_data (S X Y : Finset A) (hSX : S⊆X) (hSY : S⊆Y)
    (H : Finset I) (hH : H.Nonempty) (hyper : I→Finset A) (h : ℕ)
    (P : Finset J) (hP : P.Nonempty) (plane : J→Finset A) (p : ℕ) :
    let CH := clippedPart S H hH hyper X h
    let CP := clippedPart S P hP plane Y p
    let C := family CH CP
    let ih := fun x => queryPart H hH hyper X h x
    let ip := fun x => queryPart P hP plane Y p x
    let raw := twoPublicOwn (greedyList H hH hyper X h) (greedyList P hP plane Y p)
    (∀i,C i⊆S) ∧ (∑i,(C i).card)≤3*S.card ∧
    (∀x,S∩raw x=C (.inl (ih x))∪C (.inr (.inl (ip x)))) ∧
    (∀x,C (.inr (.inr (ih x,ip x)))=C (.inl (ih x))∩C (.inr (.inl (ip x)))) ∧
    (∀x,ownCell H hH hyper X h x⊆raw x) ∧
    (∀x,ownCell P hP plane Y p x⊆raw x) := by
  dsimp only
  refine ⟨family_subsets S _ _ (clippedPart_subset S H hH hyper X h)
    (clippedPart_subset S P hP plane Y p),
    family_mass S _ _ (clippedPart_subset S H hH hyper X h)
      (clippedPart_subset S P hP plane Y p) (clippedPart_disjoint S H hH hyper X h)
      (clippedPart_disjoint S P hP plane Y p),?_,?_,?_,?_⟩
  · intro x
    change S∩(publicOwn (greedyList H hH hyper X h) x∪publicOwn (greedyList P hP plane Y p) x)=_
    rw [Finset.inter_union_distrib_left,clipped_publicOwn S H hH hyper X hSX,
      clipped_publicOwn S P hP plane Y hSY]
    rfl
  · intro x; rfl
  · intro x
    exact (ownCell_subset_publicOwn H hH hyper X h x).trans Finset.subset_union_left
  · intro x
    exact (ownCell_subset_publicOwn P hP plane Y p x).trans Finset.subset_union_right

end SharpRamseyFive.GreedyTraining

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_MetadataScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata
open Filter
open scoped Topology

lemma list_length_bounds (σ g h p : ℝ) (_hh : 0≤h) (hp : 0≤p)
    (hg : 0≤g) (hghi : g≤σ+Real.log 4)
    (hlen : h*Real.exp (2*σ)≤Real.exp (3*σ/2+g))
    (plen : p*Real.exp (σ+17*g/15)≤Real.exp (3*σ/2+g)) :
    h≤4*Real.exp (σ/2) ∧ p≤Real.exp (σ/2) ∧ h*p≤4*Real.exp (13*σ/15) := by
  have hb : h≤Real.exp (g-σ/2) := by
    have hb := (le_div_iff₀ (Real.exp_pos (2*σ))).mpr hlen
    rw [←Real.exp_sub] at hb
    convert hb using 1; congr 1; ring
  have pb : p≤Real.exp (σ/2-2*g/15) := by
    have pb := (le_div_iff₀ (Real.exp_pos (σ+17*g/15))).mpr plen
    rw [←Real.exp_sub] at pb
    convert pb using 1; congr 1; ring
  refine ⟨?_,pb.trans (Real.exp_le_exp.mpr (by linarith)),?_⟩
  · calc
      h≤Real.exp (σ/2+Real.log 4) := hb.trans (Real.exp_le_exp.mpr (by linarith))
      _=4*Real.exp (σ/2) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)];ring
  · calc
      _≤Real.exp (g-σ/2)*Real.exp (σ/2-2*g/15) := mul_le_mul hb pb hp (Real.exp_nonneg _)
      _=Real.exp (13*g/15) := by rw [←Real.exp_add];congr 1;ring
      _≤Real.exp (13*σ/15+Real.log 4) := Real.exp_le_exp.mpr (by have := Real.log_nonneg (by norm_num : (1:ℝ)≤4);linarith)
      _=4*Real.exp (13*σ/15) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)];ring

lemma sigma_exp_absorb (C σ : ℝ) (hC : 0≤C) (hσ : 225*C≤σ) (hσ0 : 0≤σ) :
    C*σ*Real.exp (13*σ/15)≤Real.exp σ := by
  have hp := Real.pow_div_factorial_le_exp (2*σ/15) (by positivity : (0:ℝ)≤2*σ/15) 2
  norm_num only [Nat.factorial,Finset.prod_range_succ,Nat.cast_ofNat] at hp
  have hc : C*σ≤Real.exp (2*σ/15) := by nlinarith
  calc
    _≤Real.exp (2*σ/15)*Real.exp (13*σ/15) := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _=Real.exp σ := by rw [←Real.exp_add];congr 1;ring

lemma metadata_budget (σ H J B V : ℝ) (hσ : 100000≤σ)
    (hH : 0≤H) (hJ : 0≤J) (_hB : 0<B) (_hV : 0<V)
    (hHhi : H≤5*Real.exp (σ/2)) (hJhi : J≤5*Real.exp (13*σ/15))
    (hHlog : Real.log (H+1)≤σ) (hBlog : Real.log B≤6*σ) (hVlog : Real.log V≤5*σ) :
    2*Real.log (H+1)+(10*H)*Real.log V+(1+2*H+J)*Real.log B≤Real.exp σ := by
  have hσ0 : 0≤σ := by linarith
  have he : Real.exp (σ/2)≤Real.exp (13*σ/15) := Real.exp_le_exp.mpr (by linarith)
  have he1 : 1≤Real.exp (13*σ/15) := Real.one_le_exp_iff.mpr (by positivity)
  have hh : H≤5*Real.exp (13*σ/15) := hHhi.trans (mul_le_mul_of_nonneg_left he (by norm_num))
  have h₁ := mul_le_mul_of_nonneg_left hVlog (by positivity : (0:ℝ)≤10*H)
  have h₂ := mul_le_mul_of_nonneg_left hBlog (by positivity : (0:ℝ)≤1+2*H+J)
  have h₃ := mul_le_mul_of_nonneg_left hh hσ0
  have h₄ := mul_le_mul_of_nonneg_left hJhi hσ0
  have h₅ := mul_le_mul_of_nonneg_left he1 hσ0
  apply le_trans _ (sigma_exp_absorb 400 σ (by norm_num) (by linarith) hσ0)
  nlinarith only [hHlog,h₁,h₂,h₃,h₄,h₅,mul_nonneg hσ0 (Real.exp_nonneg (13*σ/15))]

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MetadataAlphabet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata
open scoped BigOperators Classical

lemma card_TwoListCode {V : Type*} [Fintype V] (h p B : ℕ) :
    Nat.card (TwoListCode V h p B)=Nat.card V^(5*(h+p))*(B+1)^(1+h+p+h*p) := by
  simp only [TwoListCode,Nat.card_prod,Nat.card_fun,Nat.card_fin]
  simp only [pow_mul,pow_add,pow_one]
  ring

lemma card_profile (H J : ℕ) : Nat.card (ListProfile H J)≤(H+1)^2 := by
  have h := Nat.card_le_card_of_injective (fun z : ListProfile H J=>z.val) Subtype.val_injective
  simpa only [ListProfile,Nat.card_prod,Nat.card_fin,pow_two] using h

theorem card_TrainingCode {V : Type*} [Fintype V] [Nonempty V] (H J B : ℕ) :
    Nat.card (TrainingCode V H J B)≤
      (H+1)^2*Nat.card V^(10*H)*(B+1)^(1+2*H+J) := by
  change Nat.card ((r : ListProfile H J) × TwoListCode V r.val.1.val r.val.2.val B)≤_
  rw [Nat.card_sigma]
  have hV : 1≤Nat.card V := Nat.card_pos
  calc
    _ ≤ ∑ _r : ListProfile H J,Nat.card V^(10*H)*(B+1)^(1+2*H+J) := by
      apply Finset.sum_le_sum
      intro r _
      rw [card_TwoListCode]
      have hh : r.val.1.val≤H := Nat.le_of_lt_succ r.val.1.isLt
      have hp : r.val.2.val≤H := Nat.le_of_lt_succ r.val.2.isLt
      exact Nat.mul_le_mul (Nat.pow_le_pow_right hV (by omega))
        (Nat.pow_le_pow_right (by omega : 1≤B+1) (by have := r.prop;omega))
    _ = Nat.card (ListProfile H J)*(Nat.card V^(10*H)*(B+1)^(1+2*H+J)) := by simp [Nat.card_eq_fintype_card]
    _ ≤ _ := by
      rw [mul_assoc]
      exact Nat.mul_le_mul_right _ (card_profile H J)

theorem log_card_TrainingCode {V : Type*} [Fintype V] [Nonempty V] (H J B : ℕ) :
    Real.log (Nat.card (TrainingCode V H J B))≤
      2*Real.log (H+1)+(10*(H:ℝ))*Real.log (Nat.card V)+
        (1+2*(H:ℝ)+J)*Real.log (B+1) := by
  have hV : (0:ℝ)<Nat.card V := by exact_mod_cast Nat.card_pos (α:=V)
  have hh : (0:ℝ)<H+1 := by positivity
  have hb : (0:ℝ)<B+1 := by positivity
  have hc := Real.log_le_log (show (0:ℝ)<Nat.card (TrainingCode V H J B) by exact_mod_cast Nat.card_pos (α:=TrainingCode V H J B))
    (show (Nat.card (TrainingCode V H J B):ℝ)≤(H+1)^2*(Nat.card V:ℝ)^(10*H)*(B+1)^(1+2*H+J) by
      exact_mod_cast card_TrainingCode (V:=V) H J B)
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow,Real.log_pow] at hc
  push_cast at hc
  exact hc

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MetadataBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata
open scoped Classical

lemma ceil_five_exp (x : ℝ) (hx : 0≤x) : (⌈4*Real.exp x⌉₊:ℝ)≤5*Real.exp x := by
  have hh := Nat.ceil_lt_add_one (by positivity : (0:ℝ)≤4*Real.exp x)
  have he := Real.one_le_exp_iff.mpr hx
  linarith

theorem log_card_training_le {V : Type*} [Fintype V] [Nonempty V]
    (σ : ℝ) (hσ : 100000≤σ) (hV : (Nat.card V:ℝ)≤Real.exp (5*σ)) :
    Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)))≤Real.exp σ := by
  have hσ0 : 0≤σ := by linarith
  have hH := ceil_five_exp (σ/2) (by positivity)
  have hJ := ceil_five_exp (13*σ/15) (by positivity)
  have hv : (0:ℝ)<Nat.card V := by exact_mod_cast Nat.card_pos (α:=V)
  have he : 6≤Real.exp (σ/2) := by linarith only [Real.add_one_le_exp (σ/2),hσ]
  have hx : 2≤Real.exp σ := by linarith only [Real.add_one_le_exp σ,hσ]
  have he5 : 1≤Real.exp (5*σ) := Real.one_le_exp_iff.mpr (by positivity)
  have hh : (listCap σ:ℝ)+1≤Real.exp σ := by
    have hpow : Real.exp (σ/2)*Real.exp (σ/2)=Real.exp σ := by rw [←Real.exp_add];congr 1;ring
    dsimp only [listCap]
    nlinarith
  have hb : (Nat.card V:ℝ)+1≤Real.exp (6*σ) := by
    have hm : Real.exp σ*Real.exp (5*σ)=Real.exp (6*σ) := by rw [←Real.exp_add];congr 1;ring
    nlinarith
  have hhlog : Real.log ((listCap σ:ℝ)+1)≤σ := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<(listCap σ:ℝ)+1) hh
    rwa [Real.log_exp] at h
  have hblog : Real.log ((Nat.card V:ℝ)+1)≤6*σ := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<(Nat.card V:ℝ)+1) hb
    rwa [Real.log_exp] at h
  have hvlog : Real.log (Nat.card V)≤5*σ := by
    have h := Real.log_le_log hv hV
    rwa [Real.log_exp] at h
  exact (log_card_TrainingCode (V:=V) (listCap σ) (productCap σ) (Nat.card V)).trans
    (metadata_budget σ (listCap σ) (productCap σ) (Nat.card V+1) (Nat.card V)
      hσ (by positivity) (by positivity) (by positivity) hv hH hJ hhlog hblog hvlog)

lemma profile_of_lengths (σ g : ℝ) (h p : ℕ) (hg : 0≤g) (hghi : g≤σ+Real.log 4)
    (hlen : (h:ℝ)*Real.exp (2*σ)≤Real.exp (3*σ/2+g))
    (plen : (p:ℝ)*Real.exp (σ+17*g/15)≤Real.exp (3*σ/2+g)) :
    h≤listCap σ ∧ p≤listCap σ ∧ h*p≤productCap σ := by
  obtain ⟨hh,hp,hj⟩ := list_length_bounds σ g h p (by positivity) (by positivity) hg hghi hlen plen
  refine ⟨?_,?_,?_⟩
  · exact_mod_cast hh.trans (Nat.le_ceil _)
  · exact_mod_cast (hp.trans (by linarith only [Real.exp_pos (σ/2)] : Real.exp (σ/2)≤4*Real.exp (σ/2))).trans (Nat.le_ceil _)
  · exact_mod_cast hj.trans (Nat.le_ceil _)

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_FlatAtlas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FlatAtlas

open Module
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

lemma decode_flatCode (n : ℕ) (hn : finrank K V≤n) (A : Submodule K V) :
    Submodule.span K (Set.range (flatCode n hn A))=A :=
  (exists_spanning_code A n hn).choose_spec

end SharpRamseyFive.FlatAtlas

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_MetadataCodec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Metadata

section
open Module GreedyTraining MeasurePublicTable ProjectiveTraining
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (ℙ K V)]

omit [Fintype (ℙ K V)]

lemma decodeH_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) :
    decodeH (encodeLists hd H P S hB)=fun i=>flatPoints (H i) := by
  funext i
  exact congrArg flatPoints (FlatAtlas.decode_flatCode 5 hd (H i))
lemma decodeP_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) :
    decodeP (encodeLists hd H P S hB)=fun i=>flatPoints (P i) := by
  funext i
  exact congrArg flatPoints (FlatAtlas.decode_flatCode 5 hd (P i))

lemma decodeOwn_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) (x : ℙ K V) :
    decodeOwn (encodeLists hd H P S hB) x=
      twoPublicOwn (fun i=>flatPoints (H i)) (fun i=>flatPoints (P i)) x := by
  simp only [decodeOwn,decodeH_encode,decodeP_encode]

theorem decodeOwnCount_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) (x : ℙ K V) :
    decodeOwnCount (encodeLists hd H P S hB) x=
      (S∩twoPublicOwn (fun i=>flatPoints (H i)) (fun i=>flatPoints (P i)) x).card := by
  simp only [decodeOwnCount,decodeH_encode,decodeP_encode,twoPublicOwn,publicOwn,
    Finset.inter_union_distrib_left]
  cases hh : firstIndex {F | x∈F} (fun i=>flatPoints (H i)) <;>
    cases hp : firstIndex {F | x∈F} (fun i=>flatPoints (P i)) <;>
    simp [encodeLists,Finset.card_union]

lemma decodeBaseScore_encode {h p B : ℕ} (hd : finrank K V≤5)
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V)
    (S : Finset (ℙ K V)) (hB : S.card≤B) (L : ℝ) (x : ℙ K V) :
    decodeBaseScore (encodeLists hd H P S hB) L x=
      Real.exp (-L*(1-((S∩twoPublicOwn (fun i=>flatPoints (H i))
        (fun i=>flatPoints (P i)) x).card:ℝ)/S.card)) := by
  simp only [decodeBaseScore,decodeOwnCount_encode]
  rfl

end

open Module GreedyTraining ProjectiveTraining
open scoped Classical LinearAlgebra.Projectivization
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype V] [Fintype (ℙ K V)]

theorem training_message {h p : ℕ} (σ g : ℝ) (hd : finrank K V≤5)
    (hσ : 100000≤σ) (hq : Real.exp σ=Nat.card K)
    (hg : 0≤g) (hghi : g≤σ+Real.log 4)
    (hlen : (h:ℝ)*Real.exp (2*σ)≤Real.exp (3*σ/2+g))
    (plen : (p:ℝ)*Real.exp (σ+17*g/15)≤Real.exp (3*σ/2+g))
    (H : Fin h→Submodule K V) (P : Fin p→Submodule K V) (S : Finset (ℙ K V)) :
    Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)))≤Nat.card K ∧
    ∃c : TrainingCode V (listCap σ) (productCap σ) (Nat.card V),
      (∀x,messageOwn c x=twoPublicOwn (fun i=>flatPoints (H i)) (fun i=>flatPoints (P i)) x) ∧
      (∀L x,messageBase c L x=Real.exp (-L*(1-((S∩twoPublicOwn (fun i=>flatPoints (H i))
        (fun i=>flatPoints (P i)) x).card:ℝ)/S.card))) := by
  obtain ⟨hh,hp,hj⟩ := profile_of_lengths σ g h p hg hghi hlen plen
  refine ⟨?_,encodeTraining σ hd hh hp hj H P S,?_,?_⟩
  · rw [←hq]
    exact log_card_training_le σ hσ (vector_card_le_exp σ hq hd)
  · intro x
    exact decodeOwn_encode hd H P S (projective_card_le_vectors S) x
  · intro L x
    exact decodeBaseScore_encode hd H P S (projective_card_le_vectors S) L x

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.SharpRamsey_Entropy_ForcedHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*}

omit [DecidableEq ι] in
lemma measurePreserving_uncurry_schedule (rate : ι → ℝ≥0) (R : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin R) ι ℕ).symm
      (scheduleMeasure rate R) (batchMeasure (fun p : Fin R × ι => rate p.2)) := by
  refine ⟨(MeasurableEquiv.curry (Fin R) ι ℕ).symm.measurable, ?_⟩
  simpa only [Measure.infinitePi_eq_pi, scheduleMeasure, batchMeasure] using
    Measure.infinitePi_map_curry_symm (fun (_ : Fin R) i => poissonMeasure (rate i))

end SharpRamseyFive.PoissonScore
end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PeelingGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreScalars

lemma plane_threshold_exp {σ g n q : ℝ} (hn : n=Real.exp (3*σ/2+g))
    (hq : q=Real.exp σ) :
    n^(4/3:ℝ)/q*Real.exp (-g/5)=Real.exp (σ+17*g/15) := by
  rw [hn,hq,←Real.exp_mul,←Real.exp_sub,←Real.exp_add]
  congr 1
  ring

end SharpRamseyFive.ScoreScalars

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Decoding_TwoPeelMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.Metadata
open Module GreedyTraining ProjectiveTraining MeasurePublicTable
open scoped Classical LinearAlgebra.Projectivization
variable {K V J : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype V] [Fintype (ℙ K V)] [LinearOrder J]

theorem two_peel_message (σ g P : ℝ) (hd : finrank K V≤5)
    (hσ : 100000≤σ) (hq : Real.exp σ=Nat.card K) (hg : 0≤g) (hghi : g≤σ/2+Real.log 4)
    (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K V)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K V)
    (X : Finset (ℙ K V)) (hX : (X.card:ℝ)=Real.exp (2*σ+g)) :
    let XH := peelSet (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let h := peelLength (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
    let ht : 0<t := by positivity
    let S := peelSet (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let raw := twoPublicOwn (greedyList H hH (fun j=>flatPoints (Hyper j)) X h)
      (greedyList F hF (fun j=>flatPoints (Flat j)) XH p)
    Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)))≤Nat.card K ∧
    ∃c : TrainingCode V (listCap σ) (productCap σ) (Nat.card V),
      (∀x,messageOwn c x=raw x) ∧
      (∀L x,messageBase c L x=Real.exp (-L*(1-((S∩raw x).card:ℝ)/S.card))) := by
  dsimp only
  let XH := peelSet (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let h := peelLength (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let p := peelLength (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  have hc : 3*σ/2+(g+σ/2)=2*σ+g := by ring
  have hlen : (h:ℝ)*Real.exp (2*σ)≤Real.exp (3*σ/2+(g+σ/2)) := by
    have hh := peel_length_bound (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    have he : (Nat.card K:ℝ)^2=Real.exp (2*σ) := by rw [←hq,←Real.exp_nat_mul];norm_num
    rw [hc,←hX,←he]
    exact_mod_cast hh
  have plen : (p:ℝ)*Real.exp (σ+17*(g+σ/2)/15)≤Real.exp (3*σ/2+(g+σ/2)) := by
    have he : t=Real.exp (σ+17*(g+σ/2)/15) := by
      dsimp only [t]
      rw [←hc]
      exact ScoreScalars.plane_threshold_exp rfl rfl
    have hl := peel_length_real (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH t ht
    have hphase : (p:ℝ)*Real.exp (σ+17*(g+σ/2)/15)≤XH.card := by
      calc
        _ = (p:ℝ)*t := congrArg (fun z=>(p:ℝ)*z) he.symm
        _ ≤ _ := hl
    rw [hc,←hX]
    exact hphase.trans (by exact_mod_cast Finset.card_le_card (peel_subset _ _ _ _ _ _ _))
  let Hs : Fin h→Submodule K V := fun i=>Hyper (chosen H hH (fun j=>flatPoints (Hyper j)) X i)
  let Ps : Fin p→Submodule K V := fun i=>Flat (chosen F hF (fun j=>flatPoints (Flat j)) XH i)
  obtain ⟨hcost,c,hOwn,hBase⟩ := training_message σ (g+σ/2) hd hσ hq
    (by linarith) (by linarith) hlen plen Hs Ps S
  exact ⟨hcost,c,hOwn,hBase⟩

end SharpRamseyFive.Metadata

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_SequentialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy

open MeasureTheory
open scoped Classical BigOperators
variable {Ω α : Type*} [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω]
  [Fintype α]

lemma finiteImageLaw_positive (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→α)
    (a : α) (ha : 0<finiteImageLaw μ f a) : ∃ω,f ω=a := by
  have hh : μ.real {ω | f ω=a}≠0 := ne_of_gt ha
  exact nonempty_of_measureReal_ne_zero hh

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma chooseMessage_none (P : Ω→α→Prop) (ω : Ω) :
    chooseMessage P ω=none ↔ ¬∃a,P ω a := by
  unfold chooseMessage
  split <;> simp_all

omit [MeasurableSpace Ω] [Countable Ω] [MeasurableSingletonClass Ω] in
lemma chooseMessage_sound (P : Ω→α→Prop) (ω : Ω) (a : α)
    (h : chooseMessage P ω=some a) : P ω a := by
  unfold chooseMessage at h
  split at h
  next hh => exact (Option.some.inj h) ▸ hh.choose_spec
  next hh => contradiction

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_Aggregate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

lemma poisson_zero : poissonMeasure 0 = Measure.dirac (0 : ℕ) := by
  apply Measure.ext_of_singleton
  intro n
  rw [poissonMeasure_singleton]
  cases n <;> simp

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma hasLaw_coordinate (rate : ι→ℝ≥0) (i : ι) :
    HasLaw (fun ω : ι→ℕ => ω i) (poissonMeasure (rate i)) (batchMeasure rate) :=
  (measurePreserving_eval (fun i => poissonMeasure (rate i)) i).hasLaw

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_MeasurePreservingSplitSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma measurePreserving_split_schedule (rate : ι→ℝ≥0) (p : ι→Prop) [DecidablePred p]
    (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ =>
      ((fun r (i : {i // p i}) => ω r i),(fun r (i : {i // ¬p i}) => ω r i)))
      (scheduleMeasure rate R)
      ((scheduleMeasure (fun i : {i // p i} => rate i) R).prod
        (scheduleMeasure (fun i : {i // ¬p i} => rate i) R)) := by
  have h1 := measurePreserving_pi (fun _ : Fin R => batchMeasure rate)
    (fun _ : Fin R => (batchMeasure (fun i : {i // p i} => rate i)).prod
      (batchMeasure (fun i : {i // ¬p i} => rate i)))
    (fun _ => measurePreserving_piEquivPiSubtypeProd (fun i => poissonMeasure (rate i)) p)
  exact (measurePreserving_arrowProdEquivProdArrow ({i // p i}→ℕ) ({i // ¬p i}→ℕ)
    (Fin R) (fun _ => batchMeasure (fun i : {i // p i} => rate i))
      (fun _ => batchMeasure (fun i : {i // ¬p i} => rate i))).comp h1

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_SampledPoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma not_mem_sampledPoints (S : Finset (ℙ K V)) {R : ℕ} (ω : Fin R→S→ℕ) (x : ℙ K V) :
    x∉sampledPoints S ω ↔ Unsampled x S ω := by
  simp only [sampledPoints,Finset.mem_filter,not_and,not_not]
  refine ⟨fun h r y hy => ?_,fun h _ => h⟩
  apply h (hy ▸ y.property) r y hy

end

open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PoissonLikelihood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma batch_real_singleton (rate : ι→ℝ≥0) (ω : ι→ℕ) :
    (batchMeasure rate).real {ω}=
      Real.exp (-(∑i,(rate i:ℝ)))*(∏i,(rate i:ℝ)^(ω i))/(∏i,(ω i).factorial:ℝ) := by
  simp only [measureReal_def,batchMeasure,Measure.pi_singleton,ENNReal.toReal_prod]
  simp_rw [←measureReal_def,poissonMeasure_real_singleton]
  rw [Finset.prod_div_distrib,Finset.prod_mul_distrib,←Real.exp_sum,Finset.sum_neg_distrib]

omit [DecidableEq ι] in
lemma batch_singleton_likelihood (proposal trueRate : ι→ℝ≥0)
    (htotal : (∑i,(proposal i:ℝ))=∑i,(trueRate i:ℝ))
    {D : ℝ} (hD : ∀i,Real.exp (-D)*(trueRate i:ℝ)≤proposal i) (ω : ι→ℕ) :
    Real.exp (-D*(∑i,ω i))*(batchMeasure trueRate).real {ω}≤
      (batchMeasure proposal).real {ω} := by
  rw [batch_real_singleton,batch_real_singleton,htotal]
  have hp : Real.exp (-D*(∑i,ω i))*(∏i,(trueRate i:ℝ)^(ω i))≤
      ∏i,(proposal i:ℝ)^(ω i) := by
    calc
      _ = ∏i,(Real.exp (-D)*(trueRate i:ℝ))^(ω i) := by
        simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
        rw [←Real.exp_nat_mul]
        congr 2
        push_cast
        ring
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => pow_nonneg (by positivity) _)
        (fun i _ => pow_le_pow_left₀ (by positivity) (hD i) _)
  have hn : (0:ℝ)<∏i,((ω i).factorial:ℝ) := Finset.prod_pos fun _ _ => Nat.cast_pos.mpr (Nat.factorial_pos _)
  calc
    _ = (Real.exp (-(∑i,(trueRate i:ℝ)))*
        (Real.exp (-D*(∑i,ω i))*(∏i,(trueRate i:ℝ)^(ω i))))/(∏i,(ω i).factorial:ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)) hn.le

lemma real_event_domination {α : Type*} [MeasurableSpace α] [Countable α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set α) (hE : MeasurableSet E) {a : ℝ} (ha : 0≤a)
    (h : ∀x∈E,a*μ.real {x}≤ν.real {x}) : a*μ.real E≤ν.real E := by
  have hh (x : α) : ENNReal.ofReal a*E.indicator (fun y => μ {y}) x≤
      E.indicator (fun y => ν {y}) x := by
    by_cases hx : x∈E
    · simp only [Set.indicator_of_mem hx]
      have he := ENNReal.ofReal_le_ofReal (h x hx)
      simpa only [ENNReal.ofReal_mul ha,ofReal_measureReal (measure_ne_top μ {x}),ofReal_measureReal (measure_ne_top ν {x})] using he
    · simp [Set.indicator_of_notMem hx]
  have ht := ENNReal.tsum_le_tsum hh
  rw [ENNReal.tsum_mul_left,Measure.tsum_indicator_apply_singleton μ E hE,
    Measure.tsum_indicator_apply_singleton ν E hE] at ht
  have hr := ENNReal.toReal_mono (measure_ne_top ν E) ht
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal ha,measureReal_def] using hr

omit [DecidableEq ι] in
theorem batch_event_likelihood (proposal trueRate : ι→ℝ≥0)
    (htotal : (∑i,(proposal i:ℝ))=∑i,(trueRate i:ℝ))
    {D K : ℝ} (hD : 0≤D) (hrate : ∀i,Real.exp (-D)*(trueRate i:ℝ)≤proposal i)
    (E : Set (ι→ℕ)) (hsize : ∀ω∈E,(∑i,ω i:ℕ)≤K) :
    Real.exp (-D*K)*(batchMeasure trueRate).real E≤(batchMeasure proposal).real E := by
  apply real_event_domination _ _ E (by exact Set.to_countable E |>.measurableSet) (Real.exp_nonneg _)
  intro ω hω
  apply le_trans _ (batch_singleton_likelihood proposal trueRate htotal hrate ω)
  apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
  exact Real.exp_le_exp.mpr (by nlinarith only [hsize ω hω,hD])

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Probability_PoissonProposal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.PoissonScore

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma schedule_event_likelihood (proposal trueRate : ι→ℝ≥0)
    (htotal : (∑i,(proposal i:ℝ))=∑i,(trueRate i:ℝ))
    {D K : ℝ} (hD : 0≤D) (hrate : ∀i,Real.exp (-D)*(trueRate i:ℝ)≤proposal i)
    (R : ℕ) (E : Set (Fin R→ι→ℕ)) (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K) :
    Real.exp (-D*K)*(scheduleMeasure trueRate R).real E≤(scheduleMeasure proposal R).real E := by
  have hh := batch_event_likelihood (fun p : Fin R×ι=>proposal p.2) (fun p : Fin R×ι=>trueRate p.2)
    (by simp only [Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];rw [htotal])
    hD (fun p=>hrate p.2) {ω | Function.curry ω∈E} (by
      intro ω hω
      simpa only [sampleCount,Fintype.sum_prod_type,Function.curry] using hsize (Function.curry ω) hω)
  have ht := (measurePreserving_uncurry_schedule trueRate R).hasLaw.measureReal_eq
    (p:=fun ω=>Function.curry ω∈E) (Set.to_countable _ |>.measurableSet)
  have hp := (measurePreserving_uncurry_schedule proposal R).hasLaw.measureReal_eq
    (p:=fun ω=>Function.curry ω∈E) (Set.to_countable _ |>.measurableSet)
  simpa only [Function.curry_uncurry] using (ht▸hp▸hh)

lemma measurePreserving_restrict_schedule (H : Finset ι) (rho : ℝ≥0) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R→ι→ℕ=>fun r (i : H)=>ω r i)
      (scheduleMeasure (fun i=>if i∈H then rho else 0) R)
      (scheduleMeasure (fun _ : H=>rho) R) := by
  have h := measurePreserving_fst.comp
    (measurePreserving_split_schedule (fun i=>if i∈H then rho else 0) (fun i=>i∈H) R)
  convert h using 1 <;> try rfl
  congr 1
  · exact Subsingleton.elim _ _
  · funext i
    exact (ite_eq_left i.prop).symm

lemma ae_zero_outside_schedule (H : Finset ι) (rho : ℝ≥0) (R : ℕ) :
    ∀ᵐω∂scheduleMeasure (fun i=>if i∈H then rho else 0) R,∀r i,i∉H → ω r i=0 := by
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro i
  by_cases hi : i∈H
  · exact Filter.Eventually.of_forall fun _ h=>False.elim (h hi)
  · have h := (hasLaw_coordinate (fun i=>if i∈H then rho else 0) i).comp
      (measurePreserving_eval (fun _ : Fin R=>batchMeasure (fun i=>if i∈H then rho else 0)) r).hasLaw
    simp only [ite_eq_right hi,poisson_zero] at h
    filter_upwards [h.ae_eq_of_dirac] with ω hω
    exact fun _=>hω

lemma ambientSuccess_true_mass (H : Finset ι) (rho : ℝ≥0) (R : ℕ)
    (E : Set (Fin R→H→ℕ)) :
    (scheduleMeasure (fun i=>if i∈H then rho else 0) R).real (ambientSuccess H E)=
      (scheduleMeasure (fun _ : H=>rho) R).real E := by
  have h := (measurePreserving_restrict_schedule H rho R).hasLaw.measureReal_eq
    (p:=fun ω=>ω∈E) (Set.to_countable _ |>.measurableSet)
  apply Eq.trans _ h
  apply measureReal_congr
  filter_upwards [ae_zero_outside_schedule H rho R] with ω hω
  change (((∀r i,i∉H → ω r i=0) ∧ (fun r (i : H)=>ω r i)∈E) = ((fun r (i : H)=>ω r i)∈E))
  exact propext ⟨And.right,fun hh=>⟨hω,hh⟩⟩

omit [DecidableEq ι] in
lemma sampleCount_restrict (H : Finset ι) {R : ℕ} (ω : Fin R→ι→ℕ)
    (hω : ∀r i,i∉H → ω r i=0) : sampleCount ω=sampleCount (fun r (i : H)=>ω r i) := by
  unfold sampleCount
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_coe_sort]
  apply (Finset.sum_subset (Finset.subset_univ H) (fun i _ hi=>hω r i hi)).symm

end

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_set_rate (H : Finset ι) (hH : H.Nonempty) (rho : ℝ≥0) :
    (∑i,((if i∈H then rho/(H.card:ℝ≥0) else 0):ℝ≥0):ℝ)=rho := by
  have hH0 : (0:ℝ)<H.card := Nat.cast_pos.mpr hH.card_pos
  simp only [apply_ite,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_zero]
  simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul]
  field_simp

theorem enclosure_hidden_event_likelihood (S U : Finset ι) (hS : S.Nonempty)
    (hSU : S⊆U) (rho : ℝ≥0) (R : ℕ) (K : ℝ) (E : Set (Fin R→S→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K) :
    Real.exp (-Real.log ((U.card:ℝ)/S.card)*K)*
      (scheduleMeasure (fun _ : S=>rho/(S.card:ℝ≥0)) R).real E≤
      (scheduleMeasure (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0) R).real (ambientSuccess S E) := by
  have hU : U.Nonempty := hS.mono hSU
  have hS0 : (0:ℝ)<S.card := Nat.cast_pos.mpr hS.card_pos
  have hU0 : (0:ℝ)<U.card := Nat.cast_pos.mpr hU.card_pos
  have hSUc : (S.card:ℝ)≤U.card := Nat.cast_le.mpr (Finset.card_le_card hSU)
  have hr (i : ι) : Real.exp (-Real.log ((U.card:ℝ)/S.card))*
      ((if i∈S then rho/(S.card:ℝ≥0) else 0):ℝ≥0)≤
      ((if i∈U then rho/(U.card:ℝ≥0) else 0):ℝ≥0) := by
    by_cases hi : i∈S
    · simp only [ite_eq_left hi,ite_eq_left (hSU hi),NNReal.coe_div,NNReal.coe_natCast]
      rw [Real.exp_neg,Real.exp_log (div_pos hU0 hS0)]
      field_simp
      rfl
    · simp only [ite_eq_right hi,NNReal.coe_zero,mul_zero]
      positivity
  have hh := schedule_event_likelihood
    (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0)
    (fun i=>if i∈S then rho/(S.card:ℝ≥0) else 0)
    (by rw [sum_set_rate U hU rho,sum_set_rate S hS rho])
    (Real.log_nonneg ((one_le_div hS0).mpr hSUc)) hr R (ambientSuccess S E) (K:=K) (by
      intro ω hω
      rw [sampleCount_restrict S ω hω.1]
      exact hsize _ hω.2)
  rwa [ambientSuccess_true_mass] at hh

end SharpRamseyFive.PoissonScore

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_PublicDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma publicScore_restrict (S O rawO : Finset (ℙ K V))
    (hO : S∩rawO=O) (F : Finset (ℙ K (Dual K V))) {R : ℕ}
    (b : ℝ) (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0) :
    publicScore rawO F b ω=pointScore S O F b (fun r y=>ω r y) := by
  unfold publicScore pointScore
  apply Finset.sum_congr rfl
  intro H _
  apply Finset.prod_congr rfl
  intro r _
  have ho (y : S) : y.val∈rawO ↔ y.val∈O := by
    rw [←hO,Finset.mem_inter]
    exact ⟨fun h=>⟨y.prop,h⟩,And.right⟩
  have ha : (∀y,y∈rawO → Incident y H.val → ω r y=0) ↔
      (∀y:S,y.val∈O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI;exact h y ((ho y).mpr hy) hI
    · intro h y hy hI
      by_cases hs : y∈S
      · exact h ⟨y,hs⟩ ((ho ⟨y,hs⟩).mp hy) hI
      · exact hω r y hs
  have hb : (∀y,y∉rawO → Incident y H.val → ω r y=0) ↔
      (∀y:S,y.val∉O → Incident y.val H.val → ω r y=0) := by
    constructor
    · intro h y hy hI;exact h y (fun hh=>hy ((ho y).mp hh)) hI
    · intro h y hy hI
      by_cases hs : y∈S
      · exact h ⟨y,hs⟩ (fun hh=>hy ((ho ⟨y,hs⟩).mpr hh)) hI
      · exact hω r y hs
  simp only [ha,hb]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma publicSamples_restrict (U S : Finset (ℙ K V)) (hSU : S⊆U) {R : ℕ}
    (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0) :
    publicSamples U ω=sampledPoints S (fun r y=>ω r y) := by
  ext x
  rw [←not_iff_not]
  rw [not_mem_sampledPoints]
  simp only [publicSamples,Finset.mem_filter,not_and,not_exists,not_not]
  constructor
  · intro h r y hxy
    subst x
    exact h (hSU y.prop) r
  · intro h hx r
    by_cases hs : x∈S
    · exact h r ⟨x,hs⟩ rfl
    · exact hω r x hs

omit [Finite K] [FiniteDimensional K V] in
lemma publicDecoded_restrict (U S : Finset (ℙ K V)) (hSU : S⊆U)
    (O rawO : ℙ K V→Finset (ℙ K V)) (hO : ∀x,S∩rawO x=O x)
    (b : ℙ K V→ℝ) (z : ℕ) {R : ℕ}
    (ω : Fin R→ℙ K V→ℕ) (hω : ∀r y,y∉S → ω r y=0) :
    publicDecoded U rawO b z ω=decoded U S O b z (fun r y=>ω r y) := by
  unfold publicDecoded decoded
  rw [publicSamples_restrict U S hSU ω hω]
  congr 1
  funext x
  exact publicScore_restrict S (O x) (rawO x) (hO x) (pencil x) (b x) ω hω

end SharpRamseyFive.ScoreGeometry

namespace SharpRamseyFive.PoissonScore
open MeasureTheory ProbabilityTheory MeasurePublicTable
open scoped BigOperators NNReal Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma enclosure_success_mass (S U : Finset ι) (hS : S.Nonempty) (hSU : S⊆U)
    (rho : ℝ≥0) (R : ℕ) (K A : ℝ) (E : Set (Fin R→S→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K)
    (hprob : Real.exp (-A)≤(scheduleMeasure (fun _ : S=>rho/(S.card:ℝ≥0)) R).real E) :
    Real.exp (-(Real.log ((U.card:ℝ)/S.card)*K+A))≤
      (scheduleMeasure (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0) R).real (ambientSuccess S E) := by
  have hh := enclosure_hidden_event_likelihood S U hS hSU rho R K E hsize
  calc
    _ = Real.exp (-Real.log ((U.card:ℝ)/S.card)*K)*Real.exp (-A) := by rw [←Real.exp_add];congr 1;ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hprob (Real.exp_nonneg _)).trans hh

theorem enclosure_search_failure (S U : Finset ι) (hS : S.Nonempty) (hSU : S⊆U)
    (rho : ℝ≥0) (R : ℕ) (K A q : ℝ) (hq : 0≤q) (E : Set (Fin R→S→ℕ))
    (hsize : ∀ω∈E,(sampleCount ω:ℝ)≤K)
    (hprob : Real.exp (-A)≤(scheduleMeasure (fun _ : S=>rho/(S.card:ℝ≥0)) R).real E) :
    let N := ⌈q*Real.exp (Real.log ((U.card:ℝ)/S.card)*K+A)⌉₊
    (Measure.pi (fun _ : Fin N=>scheduleMeasure (fun i=>if i∈U then rho/(U.card:ℝ≥0) else 0) R)).real
      {t | firstIndex (ambientSuccess S E) t=none}≤Real.exp (-q) := by
  dsimp only
  exact finite_cutoff_failure _ _ (Set.to_countable _ |>.measurableSet) hq _
    (enclosure_success_mass S U hS hSU rho R K A E hsize hprob) (Nat.le_ceil _)

end SharpRamseyFive.PoissonScore

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance MeasurePublicTable
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
theorem public_table_decodes (U S : Finset (ℙ K V)) (hSU : S⊆U)
    (O rawO : ℙ K V→Finset (ℙ K V)) (hO : ∀x,S∩rawO x=O x)
    (b : ℙ K V→ℝ) (E : Finset (ℙ K (Dual K V))) (R : ℕ) (s M c : ℝ)
    {N : ℕ} (t : Fin N→Fin R→ℙ K V→ℕ) {i : Fin N}
    (hi : firstIndex (ambientSuccess S (trueScoreSuccess U S O b E R s M c)) t=some i) :
    ∃ z ≤ E.card, (sampleCount (t i):ℝ)≤ s ∧
      ((publicDecoded U rawO b z (t i)).card:ℝ)≤ M ∧
      c≤(((publicDecoded U rawO b z (t i))∩S).card:ℝ) := by
  have hh := firstIndex_some_mem _ t hi
  change (∀r y,y∉S → t i r y=0) ∧
    (fun r (y : S)=>t i r y)∈trueScoreSuccess U S O b E R s M c at hh
  let ω : Fin R→S→ℕ := fun r y=>t i r y
  let z := (emptyTests E (hyperplaneSupport S) ω).card
  refine ⟨z,Finset.card_le_card (Finset.filter_subset _ _),?_,?_,?_⟩
  · rw [sampleCount_restrict S (t i) hh.1]
    exact hh.2.1
  · rw [publicDecoded_restrict U S hSU O rawO hO b z (t i) hh.1]
    exact hh.2.2.1
  · rw [publicDecoded_restrict U S hSU O rawO hO b z (t i) hh.1]
    exact hh.2.2.2

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_UniformCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
variable {A : Type*} [Fintype A]

lemma ceil_ratio_log (q a : ℝ) (hq : 1 ≤ q) (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.log (⌈q/a⌉₊:ℝ) ≤ Real.log (2*q)-Real.log a := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hx : 1 ≤ q/a := (le_div_iff₀ ha).mpr (by simpa using ha1.trans hq)
  have hcpos : (0:ℝ) < ⌈q/a⌉₊ := by exact_mod_cast Nat.ceil_pos.mpr (div_pos hqpos ha)
  have hh : (⌈q/a⌉₊:ℝ) ≤ (2*q)/a := by
    have ht := Nat.ceil_lt_add_one (div_pos hqpos ha).le
    have he : 2*(q/a)=(2*q)/a := by ring
    linarith
  have hl := Real.log_le_log hcpos hh
  rwa [Real.log_div (by positivity : (2*q:ℝ) ≠ 0) ha.ne'] at hl

end SharpRamseyFive.FiniteEntropy

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence CellVariance ScoreRegularity
open MeasureTheory ProbabilityTheory PoissonScore ScoreAcceptance MeasurePublicTable
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma scoreSearchCost_nonneg (S U : Finset (ℙ K V)) (hS : S.Nonempty)
    (hSU : S⊆U) (P τ : ℝ) (hP : 0≤P) (hτ : 0≤τ) :
    0 ≤ scoreSearchCost S U P τ := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hr : (1:ℝ)≤(U.card:ℝ)/S.card := (le_div_iff₀ hs).mpr (by simpa using (show (S.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hSU))
  unfold scoreSearchCost
  exact add_nonneg (mul_nonneg (Real.log_nonneg hr) (by positivity))
    (add_nonneg (by positivity) (Real.log_nonneg (by norm_num)))

omit [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma scoreCutoff_pos (S U : Finset (ℙ K V)) (P τ : ℝ) : 0 < scoreCutoff S U P τ := by
  apply Nat.ceil_pos.mpr
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast (Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  positivity

omit [FiniteDimensional K V] in
theorem score_public_implementation (U S : Finset (ℙ K V)) (hS : S.Nonempty) (hSU : S⊆U)
    (O rawO : ℙ K V→Finset (ℙ K V)) (hO : ∀x,S∩rawO x=O x)
    (b : ℙ K V→ℝ) (E : Finset (ℙ K (Dual K V))) (R : ℕ) (L₀ : ℝ≥0)
    (P τ M : ℝ) (hP : 0≤P) (hτ : 0≤τ)
    (hprob : Real.exp (-8*P*τ)/4≤
      (scheduleMeasure (fun _ : S=>L₀*pointStrength S) R).real
        (trueScoreSuccess U S O b E R (2*(Nat.card K:ℝ)*P) M ((9/10:ℝ)*S.card))) :
    let N := scoreCutoff S U P τ
    let Good := ambientSuccess S (trueScoreSuccess U S O b E R (2*(Nat.card K:ℝ)*P) M ((9/10:ℝ)*S.card))
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U P τ ∧
    (Measure.pi (fun _ : Fin N=>scheduleMeasure
      (fun i=>if i∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)).real
       {t | firstIndex Good t=none}≤Real.exp (-(Nat.card K:ℝ)) ∧
    ∀(t : Fin N→Fin R→ℙ K V→ℕ) (i : Fin N),firstIndex Good t=some i →
      ∃z≤E.card, (sampleCount (t i):ℝ)≤2*(Nat.card K:ℝ)*P ∧
        ((publicDecoded U rawO b z (t i)).card:ℝ)≤M ∧
        (9/10:ℝ)*S.card≤(((publicDecoded U rawO b z (t i))∩S).card:ℝ) := by
  dsimp only
  have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hA := scoreSearchCost_nonneg S U hS hSU P τ hP hτ
  have hexp : Real.exp (-(8*P*τ+Real.log 4))=Real.exp (-8*P*τ)/4 := by
    rw [neg_add,Real.exp_add,Real.exp_neg (Real.log 4),Real.exp_log (by norm_num : (0:ℝ)<4)]
    congr 1; ring_nf
  have hmean : (fun _ : S=>(L₀*(Nat.card K:ℝ≥0))/(S.card:ℝ≥0))=
      (fun _ : S=>L₀*pointStrength S) := by
    funext x
    simp only [pointStrength,mul_div_assoc]
  have hh := enclosure_search_failure S U hS hSU (L₀*(Nat.card K:ℝ≥0)) R
    (2*(Nat.card K:ℝ)*P) (8*P*τ+Real.log 4) (Nat.card K:ℝ) (by positivity)
    (trueScoreSuccess U S O b E R (2*(Nat.card K:ℝ)*P) M ((9/10:ℝ)*S.card))
    (by intro ω hω;exact hω.1) (by rw [hmean,hexp];exact hprob)
  have hcost : Real.log ((U.card:ℝ)/S.card)*(2*(Nat.card K:ℝ)*P)+(8*P*τ+Real.log 4)=scoreSearchCost S U P τ := by
    unfold scoreSearchCost;ring
  refine ⟨?_,hh,?_⟩
  · have hl := FiniteEntropy.ceil_ratio_log (Nat.card K:ℝ) (Real.exp (-scoreSearchCost S U P τ)) hq
      (Real.exp_pos _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA))
    rw [Real.log_exp,sub_neg_eq_add] at hl
    simpa only [scoreCutoff,Real.exp_neg,div_inv_eq_mul] using hl
  · intro t i hi
    exact public_table_decodes U S hSU O rawO hO b E R _ M _ t hi

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BasePublicFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence SubsetEncoding
open MeasureTheory ProbabilityTheory PoissonScore
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma baseTape_marginal (U : Finset (ℙ K V)) (P τ : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (n : Fin (Fintype.card (ℙ K V)+1))
    (E : Set (Fin (sizeScoreCutoff U n P τ) → Fin R → ℙ K V → ℕ)) :
    (baseTapeMeasure U P τ R L₀).real {t | t n∈E}=
      (baseRowMeasure U n P τ R L₀).real E := by
  have hE : MeasurableSet E := Set.Countable.measurableSet (Set.to_countable E)
  have hh := (measurePreserving_eval
    (fun n : Fin (Fintype.card (ℙ K V)+1)=>baseRowMeasure U n P τ R L₀) n).measure_preimage hE.nullMeasurableSet
  exact congrArg ENNReal.toReal hh

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionTwoPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Field K] [Finite K] in
lemma density_three_quarters {d : ℕ} (hd : 1 ≤ d) (hq : 3 ≤ Nat.card K) :
    3 / (4 * (Nat.card K : ℝ)) ≤
      (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d := by
  have hm : 0 < Q (Nat.card K) (d-1) := Q_pos _ _
  have hn : 0 < Q (Nat.card K) d := Q_pos _ _
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [Q_recurrence hd]
  push_cast
  have hq' : (3 : ℝ) ≤ Nat.card K := by exact_mod_cast hq
  have hm' : (1 : ℝ) ≤ Q (Nat.card K) (d-1) := by exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_left hm' (by positivity : (0:ℝ) ≤ Nat.card K)
  nlinarith

theorem sparse_half_rectangle_size {d : ℕ} (hdim : finrank K V = d + 1) (hd : 1 ≤ d) (hq3 : 3 ≤ Nat.card K)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Module.Dual K V)))
    (hsparse : (incidences A B : ℝ) ≤ (A.card : ℝ) * B.card / (2 * Nat.card K)) :
    (A.card : ℝ) * B.card ≤ 16 * (Nat.card K : ℝ) ^ (d+1) := by
  classical
  let q : ℝ := Nat.card K
  let v : ℝ := (A.card : ℝ) * B.card
  let p : ℝ := (Q (Nat.card K) (d-1) : ℝ) / Q (Nat.card K) d
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast (Finite.one_lt_card (α := K)).le
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hp : 3 / (4*q) ≤ p := density_three_quarters hd hq3
  have hpv := mul_le_mul_of_nonneg_right hp hv
  have hlow : v / (4*q) ≤ p*v - incidences A B := by
    change (incidences A B : ℝ) ≤ v / (2*q) at hsparse
    have he : (3 / (4*q)) * v = 3 * (v / (4*q)) := by field_simp
    have he2 : v / (2*q) = 2 * (v / (4*q)) := by field_simp; ring
    rw [he] at hpv
    rw [he2] at hsparse
    linarith
  have hm : |(incidences A B : ℝ) - p*v| ≤ Real.sqrt (q^(d-1)*v) := by
    simpa only [p, q, v, mul_assoc] using incidence_mixing hdim hd A B
  have habs : |(incidences A B : ℝ) - p*v| = p*v - incidences A B := by
    rw [abs_of_nonpos (show (incidences A B : ℝ) - p*v ≤ 0 by
      have hnonneg : 0 ≤ v / (4*q) := by positivity
      linarith)]
    ring
  rw [habs] at hm
  have hs : v / (4*q) ≤ Real.sqrt (q^(d-1)*v) := hlow.trans hm
  have hs2 := (Real.le_sqrt (by positivity) (by positivity)).mp hs
  have he : (v / (4*q))^2 * (16*q^2) = v^2 := by field_simp; ring
  have hm2 := mul_le_mul_of_nonneg_right hs2 (show 0 ≤ 16*q^2 by positivity)
  rw [he] at hm2
  have hexp : q^(d-1)*v*(16*q^2) = (16*q^(d+1))*v := by
    have hd' : d-1 + 2 = d+1 := by omega
    rw [← hd', pow_add]
    ring
  rw [hexp, pow_two] at hm2
  by_cases hv0 : v = 0
  · change v ≤ _
    rw [hv0]
    positivity
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne hv (Ne.symm hv0))).mp hm2

end SharpRamseyFive.ProjectiveIncidence

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseCapturedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence FiniteEntropy MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] in
lemma scoredCaptureLaw_positive (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (Own : ℙ K V→Finset (ℙ K V))
    (Base : ℙ K V→ℝ) (P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (W : Finset (ℙ K V)) (hW : 0 < scoredCaptureLaw X U n Own Base P τ c a R L₀ (some W)) :
    W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ) := by
  obtain ⟨t,ht⟩ := finiteImageLaw_positive (baseTapeMeasure U P τ R L₀)
    (scoredOutcome X U n Own Base P τ c a R) (some W) hW
  dsimp only [scoredOutcome] at ht
  obtain ⟨m,hm,he⟩ := Option.map_eq_some_iff.mp ht
  have hs := chooseMessage_sound _ t m hm
  simpa only [he] using hs

omit [Finite K] [FiniteDimensional K V] in
lemma scoredCaptureLaw_failure (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (Own : ℙ K V→Finset (ℙ K V))
    (Base : ℙ K V→ℝ) (P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (E : Set (Fin (sizeScoreCutoff U n P τ)→Fin R→ℙ K V→ℕ)) (ε : ℝ)
    (hE : (baseRowMeasure U n P τ R L₀).real Eᶜ≤ε)
    (hs : ∀t∈E,∃i : Fin (sizeScoreCutoff U n P τ),∃z : Fin (Fintype.card (ℙ K (Dual K V))+1),
      let W := publicDecoded U Own Base z (t i)
      W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ)) :
    scoredCaptureLaw X U n Own Base P τ c a R L₀ none≤ε := by
  have hm := baseTape_marginal U P τ R L₀ n Eᶜ
  have hsub : {t | scoredOutcome X U n Own Base P τ c a R t=none}⊆{t : BaseTape U P τ R | t n∈Eᶜ} := by
    intro t ht he
    obtain ⟨i,z,hgood⟩ := hs (t n) he
    have hn : ¬∃m : Fin (sizeScoreCutoff U n P τ) × Fin (Fintype.card (ℙ K (Dual K V))+1),
        let W := publicDecoded U Own Base m.2 (t n m.1)
        W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (a*P) ∧ c*X.card≤((W∩X).card:ℝ) := by
      simpa only [Set.mem_ofPred_eq,scoredOutcome,Option.map_eq_none_iff,chooseMessage_none] using ht
    exact hn ⟨(i,z),hgood⟩
  exact (measureReal_mono (μ:=baseTapeMeasure U P τ R L₀) hsub).trans (hm.trans_le hE)

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_ScoredMessage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization NNReal BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Finite K] [FiniteDimensional K V] [Fintype V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))] in
lemma score_training_gap (X S U : Finset (ℙ K V)) (hS : S.Nonempty)
    (hSX : S⊆X) (hXU : X⊆U) (hret : X.card≤4*S.card) :
    Real.log ((U.card:ℝ)/S.card)≤Real.log ((U.card:ℝ)/X.card)+Real.log 4 := by
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hx : (0:ℝ)<X.card := hs.trans_le (by exact_mod_cast Finset.card_le_card hSX)
  have hu : (0:ℝ)<U.card := hx.trans_le (by exact_mod_cast Finset.card_le_card hXU)
  have hr : (X.card:ℝ)≤4*S.card := by exact_mod_cast hret
  have hh : (U.card:ℝ)/S.card≤((U.card:ℝ)/X.card)*4 := by
    apply (div_le_iff₀ hs).mpr
    have hh := mul_le_mul_of_nonneg_left hr (div_nonneg hu.le hx.le)
    field_simp at hh ⊢
    nlinarith
  have hl := Real.log_le_log (div_pos hu hs) hh
  rw [Real.log_mul (div_pos hu hx).ne' (by norm_num)] at hl
  exact hl

omit [Fintype (ℙ K (Dual K V))] in

lemma projective_header_le (σ : ℝ) (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K)
    (hd : finrank K V≤5) :
    Real.log (Fintype.card (ℙ K V)+1:ℝ)≤6*(Nat.card K:ℝ) := by
  have hv := vector_card_le_exp (K:=K) (V:=V) σ hq hd
  have hp : (Fintype.card (ℙ K V):ℝ)≤Nat.card V := by
    exact_mod_cast projective_card_le_vectors (Finset.univ : Finset (ℙ K V))
  have he : Real.exp (5*σ)+1≤Real.exp (6*σ) := by
    have h1 : 1≤Real.exp (5*σ) := Real.one_le_exp_iff.mpr (by linarith)
    have h2 : 2≤Real.exp σ := (by linarith : (2:ℝ)≤σ+1).trans (Real.add_one_le_exp σ)
    have hx : Real.exp (6*σ)=Real.exp (5*σ)*Real.exp σ := by
      rw [←Real.exp_add];congr 1;ring
    rw [hx]
    nlinarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<Fintype.card (ℙ K V)+1)
    (show (Fintype.card (ℙ K V)+1:ℝ)≤Real.exp (6*σ) by linarith)
  rw [Real.log_exp] at hl
  have hσq : σ≤Nat.card K := by rw [←hq];linarith only [Real.add_one_le_exp σ]
  linarith

lemma scored_cost_scalar (q P gap τ : ℝ) (hq : 2≤q) (hP : 1≤P)
    (hgap : 0≤gap) (_hτ : 0≤τ) (hτ1 : τ≤1) :
    13*q+Real.log (2*q)+(gap+Real.log 4)*(2*q*P)+(8*P*τ+Real.log 4)≤
      100*q*P*(gap+P) := by
  have hqp : 0<q := by linarith
  have hp : 0≤P := by linarith
  have hL : Real.log (2*q)≤2*q-1 := Real.log_le_sub_one_of_pos (by positivity)
  have h4 : Real.log (4:ℝ)≤3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4) using 1; norm_num
  have ht := mul_le_mul_of_nonneg_left hτ1 (show 0≤8*P by positivity)
  have hh := mul_le_mul_of_nonneg_right h4 (show 0≤2*q*P by positivity)
  have h₁ : q≤q*P := by nlinarith
  have h₂ : q*P≤q*P*P := by nlinarith
  have h₃ : P≤q*P := by nlinarith
  have h₄ : 0≤q*P*gap := by positivity
  nlinarith

theorem scoredMessage_cost (σ P τ : ℝ) (hσ : 100000≤σ)
    (hq : Real.exp σ=Nat.card K) (hd : finrank K V≤5)
    (hP : 1≤P) (hτ : 0≤τ) (hτ1 : τ≤1)
    (X S U : Finset (ℙ K V)) (hS : S.Nonempty) (hSX : S⊆X)
    (hXU : X⊆U) (hret : X.card≤4*S.card)
    (hN : Real.log (scoreCutoff S U P τ)≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U P τ) :
    Real.log (Fintype.card (ℙ K V)+1:ℝ)+
      Real.log (Fintype.card (ScoredPayload U S.card σ P τ):ℝ)≤
        100*(Nat.card K:ℝ)*P*(Real.log ((U.card:ℝ)/X.card)+P) := by
  have hq2 : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α:=K)
  have hp := projective_header_le σ (by linarith) hq hd
  let : Finite (Dual K V) := Module.finite_of_finite K
  let : Fintype (Dual K V) := Fintype.ofFinite _
  have hz := projective_header_le (K:=K) (V:=Dual K V) σ (by linarith) hq (by simpa using hd)
  have hc := log_card_training_le (V:=V) σ hσ (vector_card_le_exp σ hq hd)
  rw [hq] at hc
  have hs : (0:ℝ)<S.card := by exact_mod_cast hS.card_pos
  have hx : (0:ℝ)<X.card := hs.trans_le (by exact_mod_cast Finset.card_le_card hSX)
  have hgap : 0≤Real.log ((U.card:ℝ)/X.card) := Real.log_nonneg ((le_div_iff₀ hx).mpr (by
    simpa using (show (X.card:ℝ)≤U.card by exact_mod_cast Finset.card_le_card hXU)))
  have hg := score_training_gap X S U hS hSX hXU hret
  have hn0 : (0:ℝ) < scoreCutoff S U P τ := by exact_mod_cast scoreCutoff_pos S U P τ
  have hc0 : (0:ℝ)<Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)) := by
    exact_mod_cast Nat.card_pos (α:=TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
  have hcard : Real.log (Fintype.card (ScoredPayload U S.card σ P τ):ℝ)=
      Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)))+
      (Real.log (scoreCutoff S U P τ)+Real.log (Fintype.card (ℙ K (Dual K V))+1:ℝ)) := by
    have he : sizeScoreCutoff U S.card P τ=scoreCutoff S U P τ := rfl
    simp only [ScoredPayload,Fintype.card_prod,Fintype.card_fin,he,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [←Nat.card_eq_fintype_card (α:=TrainingCode V (listCap σ) (productCap σ) (Nat.card V))]
    rw [Real.log_mul (by exact hc0.ne') (mul_ne_zero hn0.ne' (by positivity)),
      Real.log_mul hn0.ne' (by positivity)]
  rw [hcard]
  have hg' := mul_le_mul_of_nonneg_right hg (show 0≤2*(Nat.card K:ℝ)*P by positivity)
  have hsc := scored_cost_scalar (Nat.card K) P (Real.log ((U.card:ℝ)/X.card)) τ hq2 hP hgap hτ hτ1
  unfold scoreSearchCost at hN
  linarith
end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionFourHighPublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy TrainingCells MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_high_public_predictor {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (2*σ+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) → P η σ D R/10000<g →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (∀j∈H,finrank K (Hyper j)=4) →
      (∀V : Submodule K (I→K),finrank K V=4 → ∃j∈H,Hyper j=V) →
    let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
    let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
    let _a := queryPart H hH (fun j=>flatPoints (Hyper j)) X h
    let _e := queryPart F hF (fun j=>flatPoints (Flat j)) XH p
    (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log (Nat.card (TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))))≤q ∧
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    ∃ Good : Set (Fin N→Fin R→ℙ K (I→K)→ℕ),
      (Measure.pi (fun _ : Fin N=>scheduleMeasure
        (fun x=>if x∈U then (L₀*(Nat.card K:ℝ≥0))/(U.card:ℝ≥0) else 0) R)).real
         Goodᶜ ≤ Real.exp (-(Nat.card K:ℝ)) ∧
      ∀u∈Good,∃ i : Fin N,∃z : Fin (Fintype.card (ℙ K (Dual K (I→K)))+1),
        let W := publicDecoded U (messageOwn c) (messageBase c L₀) z (u i)
        W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
        (9/40:ℝ)*X.card≤((W∩X).card:ℝ) := by
  have hh := eventually_four_high_training_score hη hη' Cb hCb
  have htau := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0:ℝ)<200) (beta_pos hη))).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  have hp := (tendsto_rpow_atTop (mul_pos (by norm_num : (0:ℝ)<10) (beta_pos hη))).eventually
    (eventually_ge_atTop (4:ℝ))
  filter_upwards [hh,htau,hp,eventually_ge_atTop (100000:ℝ)] with σ hh htau hp hσ
  rw [←neg_mul] at htau
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat H hH Hyper X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover
  dsimp only
  let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
  let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
  let a := queryPart H hH (fun j=>flatPoints (Hyper j)) X h
  let e := queryPart F hF (fun j=>flatPoints (Flat j)) XH p
  let raw := twoPublicOwn (greedyList H hH (fun j=>flatPoints (Hyper j)) X h)
    (greedyList F hF (fun j=>flatPoints (Flat j)) XH p)
  change (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) → _
  intro hsmallH hsmallP
  have hp := hh D b τ g R L₀ q K I J F hF Flat H hH Hyper X U T
    hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover hsmallH hsmallP
  change S⊆X ∧ X.card≤4*S.card ∧ _ at hp
  obtain ⟨hSX,hret,hprob⟩ := hp
  have hHX : XH⊆X := peel_subset _ _ _ _ _ _ _
  have hSH : S⊆XH := peel_subset _ _ _ _ _ _ _
  have hret' : (X.card:ℝ)≤4*S.card := by exact_mod_cast hret
  have hSn : 0<(S.card:ℝ) := by nlinarith only [hret',hX,Real.exp_pos (2*σ+g)]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn)
  have hP : 4≤P η σ D R := hp.trans (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hq : 2<q := by exact_mod_cast (show (2:ℝ)<q by rw [←hσq];linarith only [Real.add_one_le_exp σ,hσ])
  have hqp : (0:ℝ)<Nat.card K := by rw [hcard,←hσq];exact Real.exp_pos _
  have hdim : finrank K (I→K)=4+1 := by rw [Module.finrank_pi,hI]
  have hm := sparse_half_rectangle_size (d:=4) hdim (by norm_num) (by omega : 3≤Nat.card K) X T (by
    apply (le_div_iff₀ (by positivity : (0:ℝ)<2*(Nat.card K:ℝ))).mpr
    have := mul_le_mul_of_nonneg_right (hτhi.trans htau.le) (by positivity : (0:ℝ)≤(X.card:ℝ)*T.card)
    nlinarith only [hdens,this])
  have hxx : (X.card:ℝ)^2≤16*Real.exp (5*σ) := by
    have hxt : (X.card:ℝ)≤T.card := by exact_mod_cast hXT
    have he : (Real.exp σ)^5=Real.exp (5*σ) := by rw [←Real.exp_nat_mul];norm_num
    rw [hcard,←hσq,he] at hm
    nlinarith
  have hnhi : (X.card:ℝ)≤4*Real.exp (5*σ/2) := by
    have he : (Real.exp (5*σ/2))^2=Real.exp (5*σ) := by rw [←Real.exp_nat_mul];congr 1;ring
    apply (sq_le_sq₀ (Nat.cast_nonneg _) (by positivity)).mp
    nlinarith only [hxx,he]
  have hghi : g≤σ/2+Real.log 4 := by
    have he : 2*σ+g≤5*σ/2+Real.log 4 := Real.exp_le_exp.mp (by
      rw [Real.exp_add (5*σ/2),Real.exp_log (by norm_num : (0:ℝ)<4)]
      nlinarith only [hnhi,hX])
    linarith only [he]
  obtain ⟨hcost,c,hOwn,hBase⟩ := two_peel_message σ g (P η σ D R)
    (by simpa only [Module.finrank_pi,hI] using le_refl 5) hσ
    (hσq.trans (by rw [hcard])) (by linarith only [hg,hP]) hghi H hH Hyper F hF Flat X hX
  have hd := literal_cell_data S X XH hSX hSH H hH (fun j=>flatPoints (Hyper j)) h F hF (fun j=>flatPoints (Flat j)) p
  change (∀i,family CH CP i⊆S) ∧ (∑i,(family CH CP i).card)≤3*S.card ∧
    (∀x,S∩raw x=CH (a x)∪CP (e x)) ∧ _ at hd
  have hO : ∀x,S∩messageOwn c x=CH (a x)∪CP (e x) := by
    intro x
    rw [hOwn]
    exact hd.2.2.1 x
  have hb' : (fun x=>Real.exp (-(L₀:ℝ)*(1-ownFraction S (CH (a x)) (CP (e x)))))=messageBase c L₀ := by
    funext x
    rw [hBase,hd.2.2.1 x]
    rfl
  rw [hb'] at hprob
  have hx := score_public_implementation U S hS (hSX.trans hXU) (fun x=>CH (a x)∪CP (e x))
    (messageOwn c) hO (messageBase c L₀) (exceptional S (family CH CP)) R L₀
    (P η σ D R) τ ((S.card:ℝ)*Real.exp (10*P η σ D R)) (by linarith only [hP]) hτ.le hprob
  dsimp only at hx
  let Good := ambientSuccess S (trueScoreSuccess U S (fun x=>CH (a x)∪CP (e x)) (messageBase c L₀)
    (exceptional S (family CH CP)) R (2*(Nat.card K:ℝ)*P η σ D R) ((S.card:ℝ)*Real.exp (10*P η σ D R)) ((9/10:ℝ)*S.card))
  refine ⟨?_,hx.1,c,{u | firstIndex Good u≠none},?_,?_⟩
  · simpa only [hcard] using hcost
  · simpa only [Set.compl_ofPred,not_not] using hx.2.1
  · intro u hu
    obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp hu
    obtain ⟨z,hz,_,hsize,hcapture⟩ := hx.2.2 u i hi
    have hz' : z<Fintype.card (ℙ K (Dual K (I→K)))+1 :=
      Nat.lt_succ_of_le (hz.trans (Finset.card_le_univ _))
    refine ⟨i,⟨z,hz'⟩,Finset.filter_subset _ _,?_,?_⟩
    · exact hsize.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hSX) (Real.exp_pos _).le)
    · have hc : ((publicDecoded U (messageOwn c) (messageBase c L₀) z (u i)∩S).card:ℝ)≤
          (publicDecoded U (messageOwn c) (messageBase c L₀) z (u i)∩X).card := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left hSX)
      linarith only [hc,hcapture,hret']

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionFourHighLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy TrainingCells MeasurePublicTable Metadata
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_high_public_law {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (2*σ+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) → P η σ D R/10000<g →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (∀j∈H,finrank K (Hyper j)=4) →
      (∀V : Submodule K (I→K),finrank K V=4 → ∃j∈H,Hyper j=V) →
    let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
    let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
    (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log (Nat.card (TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))))≤q ∧
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    let p₀ := scoredCaptureLaw X U n (messageOwn c) (messageBase c L₀)
      (P η σ D R) τ (9/40) 10 R L₀
    p₀ none≤Real.exp (-(Nat.card K:ℝ)) ∧
    (∀W,0<p₀ (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
      (9/40:ℝ)*X.card≤(W∩X).card) := by
  filter_upwards [eventually_four_high_public_predictor hη hη' Cb hCb] with σ hh
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat H hH Hyper X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover
  let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
  let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
  change (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) → _
  intro hsmallH hsmallP
  obtain ⟨hcost,hN,c,E,hE,hd⟩ := hh D b τ g R L₀ q K I J F hF Flat H hH Hyper X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover hsmallH hsmallP
  let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
  have hf := scoredCaptureLaw_failure X U n (messageOwn c) (messageBase c L₀)
    (P η σ D R) τ (9/40) 10 R L₀ E (Real.exp (-(Nat.card K:ℝ))) hE hd
  have hg := scoredCaptureLaw_positive X U n (messageOwn c) (messageBase c L₀)
    (P η σ D R) τ (9/40) 10 R L₀
  exact ⟨hcost,hN,c,hf,hg⟩

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_BaseFinitePublic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SharpRamseyFive.ScoreGeometry
open Module ProjectiveIncidence Metadata FiniteEntropy MeasureTheory
open scoped Classical LinearAlgebra.Projectivization NNReal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [Fintype V] in
lemma scoredEncoded_exact (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V))
    (t : BaseTape U P τ R) :
    (scoredEncoded X U n σ P τ c a R L₀ code t).map (scoredMessageDecoded U σ P τ R L₀ t)=
      scoredOutcome X U n (messageOwn code) (messageBase code L₀) P τ c a R t := by
  simp only [scoredEncoded,scoredOutcome,Option.map_map]
  rfl

lemma scoredEncoded_law (X U : Finset (ℙ K V))
    (n : Fin (Fintype.card (ℙ K V)+1)) (σ P τ c a : ℝ) (R : ℕ) (L₀ : ℝ≥0)
    (code : TrainingCode V (listCap σ) (productCap σ) (Nat.card V)) :
    finiteImageLaw (baseTapeMeasure U P τ R L₀)
      (fun t=>(scoredEncoded X U n σ P τ c a R L₀ code t).map (scoredMessageDecoded U σ P τ R L₀ t))=
      scoredCaptureLaw X U n (messageOwn code) (messageBase code L₀) P τ c a R L₀ := by
  simp only [scoredEncoded_exact,scoredCaptureLaw]

end SharpRamseyFive.ScoreGeometry

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Geometry_DimensionFourHighProtocol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ScoreGeometry

section
open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy TrainingCells MeasurePublicTable Metadata FiniteEntropy
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

theorem eventually_four_high_protocol_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (Cb : ℝ) (hCb : 0≤Cb) :
    ∀ᶠ σ : ℝ in atTop,∀ (D b τ g : ℝ) (R : ℕ) (L₀ : ℝ≥0),
    ∀ (q : ℕ) (K I J : Type) [Field K] [Finite K] [CharP K q] [Fintype I] [LinearOrder J]
      [Fintype (I→K)] [Fintype (ℙ K (I→K))] [Fintype (ℙ K (Dual K (I→K)))]
      [∀x : ℙ K (I→K),Fintype (RadialLine x)],
    ∀ (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K (I→K))
      (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K (I→K))
      (X U : Finset (ℙ K (I→K))) (T : Finset (ℙ K (Dual K (I→K)))),
      Nat.card K=q → Real.exp σ=q → Fintype.card I=5 →
      Range η σ D R → (L₀:ℝ)=L η σ D → 0≤b → b≤Cb*D*σ^(6*beta η) →
      0<τ → τ≤σ^(-200*beta η) → X⊆U → X.card≤T.card →
      (Nat.card K:ℝ)*(incidences X T:ℝ)≤τ*X.card*T.card →
      (Nat.card K:ℝ)^5*Real.exp (-b)≤(X.card:ℝ)*T.card →
      (X.card:ℝ)=Real.exp (2*σ+g) →
      100*(Nat.card K:ℝ)*P η σ D R<(X.card:ℝ) → P η σ D R/10000<g →
      (∀j∈F,finrank K (Flat j)=3) →
      (∀V : Submodule K (I→K),finrank K V=3 → ∃j∈F,Flat j=V) →
      (∀j∈H,finrank K (Hyper j)=4) →
      (∀V : Submodule K (I→K),finrank K V=4 → ∃j∈H,Hyper j=V) →
    let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
    let ht : 0<t := by positivity
    let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
    let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
    let _hyperQueries := queryPart H hH (fun j=>flatPoints (Hyper j)) X h
    let _flatQueries := queryPart F hF (fun j=>flatPoints (Flat j)) XH p
    (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) →
    let N := scoreCutoff S U (P η σ D R) τ
    Real.log (Nat.card (TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K))))≤q ∧
    Real.log N≤Real.log (2*(Nat.card K:ℝ))+scoreSearchCost S U (P η σ D R) τ ∧
    Real.log (Fintype.card (ℙ K (I→K))+1:ℝ)+
      Real.log (Fintype.card (ScoredPayload U S.card σ (P η σ D R) τ):ℝ)≤
        100*(Nat.card K:ℝ)*P η σ D R*(Real.log ((U.card:ℝ)/X.card)+P η σ D R) ∧
    ∃c : TrainingCode (I→K) (listCap σ) (productCap σ) (Nat.card (I→K)),
    let n : Fin (Fintype.card (ℙ K (I→K))+1) := ⟨S.card,Nat.lt_succ_of_le (Finset.card_le_univ S)⟩
    let p₀ := finiteImageLaw (baseTapeMeasure U (P η σ D R) τ R L₀)
      (fun t=>(scoredEncoded X U n σ (P η σ D R) τ (9/40) 10 R L₀ c t).map
        (scoredMessageDecoded U σ (P η σ D R) τ R L₀ t))
    p₀ none≤Real.exp (-(Nat.card K:ℝ)) ∧
    (∀W,0<p₀ (some W)→W⊆U ∧ (W.card:ℝ)≤(X.card:ℝ)*Real.exp (10*P η σ D R) ∧
      (9/40:ℝ)*X.card≤(W∩X).card) := by
  filter_upwards [eventually_four_high_public_law hη hη' Cb hCb,
    eventually_ge_atTop (100000:ℝ)] with σ hh hσ
  intro D b τ g R L₀ q K I J _ _ _ _ _ _ _ _ _ F hF Flat H hH Hyper X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover
  let XH := peelSet (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let h := peelLength (P η σ D R/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let p := peelLength (P η σ D R/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let CH := clippedPart S H hH (fun j=>flatPoints (Hyper j)) X h
  let CP := clippedPart S F hF (fun j=>flatPoints (Flat j)) XH p
  change (∀i,(CH i).card≤(S.card:ℝ)/25) → (∀j,(CP j).card≤(S.card:ℝ)/25) → _
  intro hsmallH hsmallP
  obtain ⟨hcost,hN,code,hfail,hgood⟩ := hh D b τ g R L₀ q K I J F hF Flat H hH Hyper X U T hcard hσq hI hr hL hb hbhi hτ hτhi hXU hXT hdens hprod hX hn hg hFlat hcover hHyper hHcover hsmallH hsmallP
  have hXHX : XH⊆X := peel_subset _ _ _ _ _ _ _
  have hSXH : S⊆XH := peel_subset _ _ _ _ _ _ _
  have hSX : S⊆X := hSXH.trans hXHX
  have hretH : X.card≤2*XH.card := peel_half _ _ _ _ _ _ _
  have hretP : XH.card≤2*S.card := peel_half _ _ _ _ _ _ _
  have hret : X.card≤4*S.card := by omega
  have hSn : (0:ℝ)<S.card := by
    have hh : (X.card:ℝ)≤4*S.card := by exact_mod_cast hret
    nlinarith only [hh,hX,Real.exp_pos (2*σ+g)]
  have hS : S.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hSn)
  have hP : 1≤P η σ D R :=
    (Real.one_le_rpow (by linarith : (1:ℝ)≤σ) (mul_nonneg (by norm_num) (beta_pos hη).le)).trans
      (finite_bounds hη hη' (by linarith) hr).2.2.2.2.2.1
  have hτ1 : τ≤1 := hτhi.trans (Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
    (by have hb' := beta_pos hη; nlinarith))
  have htotal := scoredMessage_cost σ (P η σ D R) τ hσ (hσq.trans (by rw [hcard]))
    (by rw [Module.finrank_pi,hI]) hP hτ.le hτ1 X S U hS hSX hXU (by omega) hN
  refine ⟨hcost,hN,htotal,code,?_⟩
  dsimp only
  rw [scoredEncoded_law]
  exact ⟨hfail,hgood⟩

end

open Module ProjectiveIncidence ProjectiveTraining GreedyTraining GlobalRadial
open CellVariance ScoreRegularity PoissonScore WeightedPrograms MeasureTheory
open Filter ParameterHierarchy MeasurePublicTable Metadata FiniteEntropy ProjectiveRestriction ReverseCap
open scoped BigOperators LinearAlgebra.Projectivization Classical NNReal Topology

end SharpRamseyFive.ScoreGeometry

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol_oai := @OAI.SharpRamseyFive.ScoreGeometry.eventually_four_high_protocol_oai
