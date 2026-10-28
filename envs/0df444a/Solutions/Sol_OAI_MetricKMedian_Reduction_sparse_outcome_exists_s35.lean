-- Prove2me | solution 1 for OAI.MetricKMedian.Reduction.sparse_outcome_exists_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:18:45.684729+00:00
-- url     : https://prove2.me/submissions/cd6de50a-c391-4ef3-814d-a9a3d78f0cc1

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K044
import Theorems.Thm_OAI_MetricKMedian_Reduction_completion_branch_exists_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem representative_threshold (Q : Finset ℚ) {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ∈ insert 0 Q, 0 ≤ r ∧ (r:ℝ) ≤ B ∧
      ∀ q ∈ Q, ((q:ℝ) ≤ B ↔ q ≤ r) := by
  classical
  let A : Finset ℚ := insert 0 (Q.filter (fun q : ℚ => (q:ℝ) ≤ B))
  have hA : A.Nonempty := insert_nonempty _ _
  let r := A.max' hA
  have hr : r ∈ A := max'_mem A hA
  have hrB : (r:ℝ) ≤ B := by
    rcases mem_insert.mp hr with hr | hr
    · rw [hr,Rat.cast_zero]; exact hB
    · exact (mem_filter.mp hr).2
  refine ⟨r,?_,?_,hrB,?_⟩
  · rcases mem_insert.mp hr with hr | hr
    · exact mem_insert.mpr (Or.inl hr)
    · exact mem_insert_of_mem (mem_filter.mp hr).1
  · exact le_max' A 0 (mem_insert_self _ _)
  · intro q hq
    constructor
    · intro hqB
      exact le_max' A q (mem_insert_of_mem (mem_filter.mpr ⟨hq,hqB⟩))
    · intro hqr
      exact (show (q:ℝ) ≤ (r:ℝ) by exact_mod_cast hqr).trans hrB

theorem mem_deletionChoices {I : Type} [DecidableEq I] (T D : Finset I) (c : ℕ) :
    D ∈ deletionChoices T c ↔ D ⊆ T ∧ D.card ≤ c := by
  simp only [deletionChoices,mem_biUnion,mem_range,mem_powersetCard]
  constructor
  · rintro ⟨m,hm,hsub,hcard⟩
    exact ⟨hsub,by omega⟩
  · rintro ⟨hsub,hcard⟩
    exact ⟨D.card,by omega,hsub,rfl⟩

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem deletion_value_mem (I : Instance) (T U : Finset (Fin I.n)) (c : ℕ)
    (hUT : U ⊆ T) (hcount : T.card-U.card ≤ c) {i : Fin I.n} (hi : i ∈ U) :
    rationalCost I (U.erase i)-rationalCost I U ∈ deletionValues I T c := by
  have hd : T \ U ∈ deletionChoices T c := (mem_deletionChoices T (T \ U) c).mpr
    ⟨sdiff_subset,by rw [card_sdiff_of_subset hUT]; exact hcount⟩
  have he : T \ (T \ U)=U := by
    ext a
    simp only [mem_sdiff]
    exact ⟨fun h => by tauto,fun h => ⟨hUT h,by tauto⟩⟩
  exact mem_biUnion.mpr ⟨T \ U,hd,mem_image.mpr ⟨i,hUT hi,by rw [he]⟩⟩

theorem deleteStep_cases (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) :
    deleteStep I B U=U ∨ ∃ i ∈ U, deleteStep I B U=U.erase i := by
  classical
  unfold deleteStep
  split_ifs with hk he
  · right
    refine ⟨_,?_,rfl⟩
    exact (mem_filter.mp (min'_mem _ he)).1
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem deleteStep_subset (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) :
    deleteStep I B U ⊆ U := by
  rcases deleteStep_cases I B U with he | ⟨i,_,he⟩
  · rw [he]
  · rw [he]; exact erase_subset _ _

theorem deleteStep_card (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) :
    U.card ≤ (deleteStep I B U).card+1 := by
  rcases deleteStep_cases I B U with he | ⟨i,hi,he⟩
  · rw [he]; omega
  · rw [he,card_erase_add_one hi]

theorem deleteStep_congr (I : Instance) (B B' : ℝ) (U : Finset (Fin I.n))
    (htest : ∀ i ∈ U,
      (((rationalCost I (U.erase i)-rationalCost I U:ℚ):ℝ) ≤ B ↔
       ((rationalCost I (U.erase i)-rationalCost I U:ℚ):ℝ) ≤ B')) :
    deleteStep I B U=deleteStep I B' U := by
  classical
  have he : eligible I B U=eligible I B' U := by
    ext i
    simp only [eligible,mem_filter]
    exact and_congr_right (htest i)
  unfold deleteStep
  rw [he]

theorem history_bounds (I : Instance) (B : ℝ) (T : Finset (Fin I.n)) (t : ℕ) :
    deletionHistory I B T t ⊆ T ∧ T.card ≤ (deletionHistory I B T t).card+t := by
  induction t with
  | zero => exact ⟨Subset.rfl,le_rfl⟩
  | succ t ih =>
    refine ⟨(deleteStep_subset I B _).trans ih.1,?_⟩
    have hc := deleteStep_card I B (deletionHistory I B T t)
    change T.card ≤ (deleteStep I B (deletionHistory I B T t)).card+(t+1)
    omega

theorem enumerate_ideal_history (I : Instance) (T : Finset (Fin I.n)) (c : ℕ)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ r ∈ insert 0 (deletionValues I T c),
      ∀ t ≤ c, deletionHistory I B T t=deletionHistory I (r:ℝ) T t := by
  obtain ⟨r,hr,_,_,htest⟩ := representative_threshold (deletionValues I T c) hB
  refine ⟨r,hr,?_⟩
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro htc
    have ht : t ≤ c := by omega
    have hist := ih ht
    simp only [deletionHistory]
    apply (deleteStep_congr I B (r:ℝ) (deletionHistory I B T t) ?_).trans
      (congrArg (deleteStep I (r:ℝ)) hist)
    intro i hi
    have hb := history_bounds I B T t
    have hm := deletion_value_mem I T (deletionHistory I B T t) c hb.1 (by omega) hi
    exact (htest _ hm).trans (by exact_mod_cast (Iff.rfl :
      rationalCost I ((deletionHistory I B T t).erase i)-rationalCost I (deletionHistory I B T t) ≤ r ↔
      rationalCost I ((deletionHistory I B T t).erase i)-rationalCost I (deletionHistory I B T t) ≤ r))

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable (I : Instance)

theorem step_cost {B : ℝ} (hB : 0 ≤ B) (U : Finset (Fin I.n)) :
    cost I (deleteStep I B U) ≤ cost I U+B := by
  classical
  unfold deleteStep
  split_ifs with hk he
  · have hmem := mem_filter.mp (min'_mem (eligible I B U) he)
    have hh := hmem.2
    rw [Rat.cast_sub,I.cast_rationalCost,I.cast_rationalCost] at hh
    linarith only [hh]
  · linarith only [hB]
  · linarith only [hB]

theorem step_budget_lower (B : ℝ) (U : Finset (Fin I.n)) (hU : I.k ≤ U.card) :
    I.k ≤ (deleteStep I B U).card := by
  classical
  unfold deleteStep
  split_ifs with hk he
  · have hi := (mem_filter.mp (min'_mem (eligible I B U) he)).1
    rw [card_erase_of_mem hi]
    omega
  · exact hU
  · exact hU

theorem history_budget_lower (B : ℝ) (T : Finset (Fin I.n)) (hT : I.k ≤ T.card) (t : ℕ) :
    I.k ≤ (deletionHistory I B T t).card := by
  induction t with
  | zero => exact hT
  | succ t ih => exact step_budget_lower I B _ ih

theorem history_cost {B : ℝ} (hB : 0 ≤ B) (T : Finset (Fin I.n)) (t : ℕ) :
    cost I (deletionHistory I B T t) ≤ cost I T+(t:ℝ)*B := by
  induction t with
  | zero => simp only [deletionHistory,Nat.cast_zero,zero_mul,add_zero,le_refl]
  | succ t ih =>
    have hh := step_cost I hB (deletionHistory I B T t)
    change cost I (deletionHistory I B T (t+1)) ≤ _ at hh
    push_cast
    linarith only [ih,hh]

theorem history_fixed (B : ℝ) (T : Finset (Fin I.n))
    (hfix : deleteStep I B T=T) (t : ℕ) : deletionHistory I B T t=T := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [deletionHistory,ih,hfix]

theorem history_succ_left (B : ℝ) (T : Finset (Fin I.n)) (t : ℕ) :
    deletionHistory I B T (t+1)=deletionHistory I B (deleteStep I B T) t := by
  induction t with
  | zero => rfl
  | succ t ih => simpa only [deletionHistory] using congrArg (deleteStep I B) ih

theorem history_endpoint (B : ℝ) (T : Finset (Fin I.n)) (c : ℕ)
    (hT : T.card ≤ I.k+c) :
    let U := deletionHistory I B T c
    U.card ≤ I.k ∨ ∀ i ∈ U, B < cost I (U.erase i)-cost I U := by
  classical
  dsimp only
  induction c generalizing T with
  | zero =>
    left
    simpa only [deletionHistory,Nat.add_zero] using hT
  | succ c ih =>
    by_cases hk : I.k < T.card
    · by_cases he : (eligible I B T).Nonempty
      · let i := (eligible I B T).min' he
        have hi : i ∈ T := (mem_filter.mp (min'_mem _ he)).1
        have hstep : deleteStep I B T=T.erase i := by
          simp only [deleteStep,ite_eq_left hk,dite_eq_left he,i]
        have hcard : (deleteStep I B T).card ≤ I.k+c := by
          rw [hstep,card_erase_of_mem hi]
          omega
        rw [history_succ_left]
        exact ih _ hcard
      · have hfix : deleteStep I B T=T := by simp only [deleteStep,ite_eq_left hk,dite_eq_right he]
        rw [history_fixed I B T hfix (c+1)]
        right
        intro i hi
        have hn : ¬ ((rationalCost I (T.erase i)-rationalCost I T:ℚ):ℝ) ≤ B := by
          intro hh
          exact he ⟨i,mem_filter.mpr ⟨hi,hh⟩⟩
        rw [Rat.cast_sub,I.cast_rationalCost,I.cast_rationalCost] at hn
        exact lt_of_not_ge hn
    · have hfix : deleteStep I B T=T := by simp only [deleteStep,ite_eq_right hk]
      rw [history_fixed I B T hfix (c+1)]
      exact Or.inl (le_of_not_gt hk)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_RationalDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem cast_rationalEligible (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    rationalEligible I B U=eligible I (B:ℝ) U := by
  ext i
  simp only [rationalEligible,eligible,mem_filter,Rat.cast_le]

theorem cast_rationalStep (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) :
    rationalDeleteStep I B U=deleteStep I (B:ℝ) U := by
  simp only [rationalDeleteStep,deleteStep,cast_rationalEligible]

theorem cast_rationalHistory (I : Instance) (B : ℚ) (T : Finset (Fin I.n)) (t : ℕ) :
    rationalHistory I B T t=deletionHistory I (B:ℝ) T t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [rationalHistory,deletionHistory,cast_rationalStep,ih]

theorem ideal_endpoint_mem (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    deletionHistory I B T c ∈ deletionEndpoints I T c := by
  obtain ⟨r,hr,hh⟩ := enumerate_ideal_history I T c hB
  exact mem_image.mpr ⟨r,hr,(cast_rationalHistory I r T c).trans (hh c le_rfl).symm⟩

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

theorem sparse_outcome_exists_s35_oai (F O T : Finset (Fin I.n)) (hOF : O ⊆ F)
    (hO : O.Nonempty) (hk : O.card=I.k) (hTF : T ⊆ F) (hT : T.Nonempty)
    (α η : ℝ) (δ : ℚ) (c b : ℕ) (hc : 0 < c) (hδ : 0 < (δ:ℝ))
    (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η) (hC : 0 < cost I O)
    (hcost : cost I T ≤ α*cost I O) (hcard : T.card ≤ I.k+c)
    (hsp : Sparse (I:=I) F O ((δ:ℝ)*η/(2*c)))
    (hfactor : 1+12*(δ:ℝ) ≤ α+η) (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ)) :
    ∃ S ∈ sparseOutcomes I F T δ c b,
      S ⊆ F ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*cost I O := by
  classical
  by_cases hTk : T.card ≤ I.k
  · refine ⟨T,mem_insert_self _ _,hTF,hT,hTk,?_⟩
    have hηC := mul_nonneg hη.le hC.le
    nlinarith only [hcost,hηC]
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  let B := η*cost I O/c
  have hB : 0 ≤ B := div_nonneg (mul_nonneg hη.le hC.le) hcR.le
  let U := deletionHistory I B T c
  have hUc : I.k ≤ U.card := history_budget_lower I B T (by omega) c
  have hUne : U.Nonempty := card_pos.mp (I.k_pos.trans hUc)
  have hUF : U ⊆ F := (history_bounds I B T c).1.trans hTF
  have hUcst : cost I U ≤ (α+η)*cost I O := by
    have hhistory := history_cost I hB T c
    have hcancel : (c:ℝ)*B=η*cost I O := by dsimp only [B]; field_simp
    rw [hcancel] at hhistory
    nlinarith only [hhistory,hcost]
  have hUm : U ∈ deletionEndpoints I T c := ideal_endpoint_mem I T c hB
  obtain hUk | hstuck := history_endpoint I B T c hcard
  · refine ⟨U,mem_insert_of_mem (mem_biUnion.mpr ⟨U,hUm,mem_insert_self _ _⟩),hUF,hUne,hUk,hUcst⟩
  · by_cases hUk : U.card ≤ I.k
    · exact ⟨U,mem_insert_of_mem (mem_biUnion.mpr ⟨U,hUm,mem_insert_self _ _⟩),hUF,hUne,hUk,hUcst⟩
    obtain ⟨S,hS,hSF,hSne,hSk,hSc⟩ := completion_branch_exists_s35 F O U hOF hO hk hUF
      (by omega) (α+η) η δ c b hc hδ hsmall hη hC hUcst hsp (fun i hi => (hstuck i hi).le) hb
    refine ⟨S,mem_insert_of_mem (mem_biUnion.mpr ⟨U,hUm,mem_insert_of_mem hS⟩),hSF,hSne,hSk,?_⟩
    exact hSc.trans (mul_le_mul_of_nonneg_right hfactor hC.le)

end MetricKMedian.Reduction
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Reduction.sparse_outcome_exists_s35_oai := @OAI.MetricKMedian.Reduction.sparse_outcome_exists_s35_oai
