-- Prove2me | solution 1 for OAI.MetricKMedian.factor_above_threshold_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:43:58.698855+00:00
-- url     : https://prove2.me/submissions/bbd08fc9-75f6-4a8e-8c38-f7258f4c68dd

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K083
import Theorems.Thm_OAI_MetricKMedian_Instance_computedPseudo_spec_s53
import Theorems.Thm_OAI_MetricKMedian_Preparation_exists_rational_all_parameters_s53
import Theorems.Thm_OAI_MetricKMedian_Reduction_reductionOutputs_success_s53

section
-- module Solutions.OAIQ053_KM.KMedian_Optimization_ApproximationSlack
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian

 theorem threshold_bounds : 1 < 1+2/Real.exp 1 ∧ 1+2/Real.exp 1 ≤ 3 := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have he1 : 1 ≤ Real.exp 1 := by exact Real.one_le_exp (by norm_num)
  have h := (div_le_iff₀ he).mpr (show (2:ℝ) ≤ 2*Real.exp 1 by linarith only [he1])
  exact ⟨lt_add_of_pos_right 1 (div_pos (by norm_num) he),by linarith only [h]⟩

 theorem slack_product (A s t : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 3)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (ht : 0 ≤ t) (ht1 : t ≤ s) :
    ((A+s)/(1-s))*(1+s)*(1+t) ≤ A+41*s := by
  have hden : 0 < 1-s := by linarith only [hs1]
  have hd : (A+s)/(1-s) ≤ A+8*s := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hs (show 0 ≤ 7-A-8*s by linarith only [hA,hs1])]
  have hss : s*s ≤ s := by nlinarith
  have hsq : (1+s)*(1+s) ≤ 1+3*s := by nlinarith
  calc
    _  ≤  (A+8*s)*(1+s)*(1+t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hd (by linarith only [hs])) (by linarith only [ht])
    _  ≤  (A+8*s)*((1+s)*(1+s)) := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left (by linarith only [ht1])
      exact mul_nonneg (by linarith only [hA0,hs]) (by linarith only [hs])
    _  ≤  (A+8*s)*(1+3*s) := mul_le_mul_of_nonneg_left hsq (by linarith only [hA0,hs])
    _  ≤  A+41*s := by
      have hAs := mul_le_mul_of_nonneg_right hA hs
      nlinarith only [hss,hAs]

 theorem exists_approximation_slack (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : ℝ) (r : ℕ), 0 < s ∧ s < 1 ∧ 0 < r ∧
      1 < ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ)) ∧
      ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ))+ε/2 ≤ 1+2/Real.exp 1+ε := by
  let s := min (1/2:ℝ) (ε/100)
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1/2 := min_le_left _ _
  have hsε : s ≤ ε/100 := min_le_right _ _
  obtain ⟨r,hr⟩ := exists_nat_gt (3/s)
  have hrR : 0 < (r:ℝ) := lt_trans (by positivity) hr
  have hrN : 0 < r := by exact_mod_cast hrR
  have ht : 3/(r:ℝ) ≤ s := (div_le_iff₀ hrR).mpr (by
    have hh := (div_lt_iff₀ hs).mp hr
    linarith only [hh])
  obtain ⟨hA,hA3⟩ := threshold_bounds
  have hp := slack_product (1+2/Real.exp 1) s (3/(r:ℝ)) (by linarith only [hA]) hA3 hs.le hs1
    (by positivity) ht
  have hbase : 1 < (1+2/Real.exp 1+s)/(1-s) := by
    apply (lt_div_iff₀ (by linarith only [hs1])).mpr
    linarith only [hA,hs]
  have hmul : 1 < ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ)) := by
    have ht0 : 0 ≤ 3/(r:ℝ) := by positivity
    have hp1 : 1 < ((1+2/Real.exp 1+s)/(1-s))*(1+s) := by nlinarith only [hbase,hs]
    nlinarith only [hp1,ht0]
  exact ⟨s,r,hs,by linarith only [hs1],hrN,hmul,by linarith only [hp,hsε,hε]⟩

end MetricKMedian
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseSelect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseSelect
variable {α : Type}

theorem best_spec (P : α → Bool) (cost : α → ℚ) (L : List α) :
    (best P cost L=none ↔ ∀ a∈L,P a=false) ∧
    ∀ a, best P cost L=some a → a∈L ∧ P a=true ∧ ∀ b∈L,P b=true → cost a ≤ cost b := by
  induction L with
  | nil => simp [best]
  | cons a L ih =>
    by_cases ha : P a=true
    · cases hb : best P cost L with
      | none =>
        have hL := ih.1.mp hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro b h
          have he : a=b := Option.some.inj h
          subst b
          refine ⟨List.mem_cons_self,ha,?_⟩
          intro b hmem hP
          rcases List.mem_cons.mp hmem with he | he
          · subst b; exact le_rfl
          · have hf := hL b he
            rw [hP] at hf
            contradiction
      | some b =>
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        simp only [best,ha,ite_true,hb]
        constructor
        · simp only [Option.some_ne_none,List.mem_cons,false_iff]
          intro hh
          have := hh a (Or.inl rfl)
          simp [ha] at this
        · intro z hz
          by_cases hab : cost a ≤ cost b
          · simp only [ite_eq_left hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_self,ha,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_rfl
            · exact hab.trans (hmin z he hP)
          · simp only [ite_eq_right hab,Option.some.injEq] at hz
            subst z
            refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
            intro z hz hP
            rcases List.mem_cons.mp hz with he | he
            · subst z; exact le_of_lt (lt_of_not_ge hab)
            · exact hmin z he hP
    · have haf : P a=false := Bool.eq_false_iff.mpr ha
      simp only [best,haf,Bool.false_eq_true,ite_false]
      constructor
      · rw [ih.1]
        constructor
        · intro h b hb
          rcases List.mem_cons.mp hb with he | he
          · subst b; exact haf
          · exact h b he
        · intro h b hb
          exact h b (List.mem_cons_of_mem a hb)
      · intro b hb
        obtain ⟨hbmem,hbP,hmin⟩ := ih.2 b hb
        refine ⟨List.mem_cons_of_mem a hbmem,hbP,?_⟩
        intro z hz hP
        rcases List.mem_cons.mp hz with he | he
        · subst z
          rw [haf] at hP
          contradiction
        · exact hmin z he hP

end MetricKMedian.SparseSelect
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

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
-- module Solutions.OAIQ053_KM.KMedian_Reduction_ReductionClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                        
section
section
namespace MetricKMedian.Reduction

theorem reduction_parameters (α η : ℝ) (hα : 1 < α) (hη : 0 < η) (c : ℕ) (hc : 0 < c) :
    ∃ (δ : ℚ) (a b : ℕ), 0 < (δ:ℝ) ∧ (δ:ℝ) ≤ 1/6 ∧
      1+12*(δ:ℝ) ≤ α+η ∧
      (3/2:ℝ) ≤ a*((δ:ℝ)*η/(2*c)) ∧
      6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ) := by
  have hsmall : (0:ℝ) < min (1/6) ((α-1)/12) := by
    apply lt_min
    · norm_num
    · exact div_pos (sub_pos.mpr hα) (by norm_num)
  obtain ⟨δ,hδ,hδsmall⟩ := exists_rat_btwn hsmall
  have hd1 : (δ:ℝ) < 1/6 := hδsmall.trans_le (min_le_left _ _)
  have hd2 : (δ:ℝ) < (α-1)/12 := hδsmall.trans_le (min_le_right _ _)
  let ρ := (δ:ℝ)*η/(2*c)
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hρ : 0 < ρ := div_pos (mul_pos hδ hη) (by positivity)
  refine ⟨δ,⌈(3/2:ℝ)/ρ⌉₊,⌈6*(α+η)*c/((δ:ℝ)*η)⌉₊,hδ,hd1.le,?_,?_,Nat.le_ceil _⟩
  · linarith
  · exact (div_le_iff₀ hρ).mp (Nat.le_ceil _)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BoundedEnumerationProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)

 theorem mem_words {α : Type} (xs : List α) (c : ℕ) (ys : List α) :
    ys∈words c xs ↔ ys.length ≤ c ∧ ∀a∈ys,a∈xs := by
  induction c generalizing ys with
  | zero => simp only [words,List.mem_singleton,List.length_eq_zero_iff,Nat.le_zero]; constructor
            · rintro rfl; simp
            · rintro ⟨rfl,_⟩; rfl
  | succ c ih =>
    cases ys with
    | nil => simp [words]
    | cons a ys =>
      simp only [words,List.mem_cons,List.cons_ne_nil,false_or,List.mem_flatMap,List.mem_map,List.cons.injEq]
      constructor
      · rintro ⟨b,hb,z,hz,he,hz'⟩
        subst b
        subst z
        obtain ⟨hl,hm⟩ := (ih ys).mp hz
        exact ⟨by simp only [List.length_cons]; omega,by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hb hm⟩
      · rintro ⟨hl,hm⟩
        refine ⟨a,hm a (by simp),ys,(ih ys).mpr ⟨by simp only [List.length_cons] at hl; omega,?_⟩,rfl,rfl⟩
        intro b hb
        exact hm b (by simp [hb])
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_RestrictionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.Reduction.Enumeration
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
 theorem list_toFinset_map {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → β) (xs : List α) :
    (xs.map f).toFinset=xs.toFinset.image f := by ext b; simp only [List.mem_toFinset,List.mem_map,Finset.mem_image]
 theorem choices_eq_of_mem {α : Type} [DecidableEq α] (T : Finset α) (xs : List α)
    (hx : ∀a,a∈xs ↔ a∈T) (c : ℕ) :
    ((words c xs).map List.toFinset).toFinset=deletionChoices T c := by
  ext D
  simp only [List.mem_toFinset,List.mem_map,mem_deletionChoices]
  constructor
  · rintro ⟨ys,hy,rfl⟩
    obtain ⟨hl,hm⟩ := (mem_words _ _ _).mp hy
    exact ⟨fun a ha => (hx a).mp (hm a (List.mem_toFinset.mp ha)),(List.toFinset_card_le _).trans hl⟩
  · rintro ⟨hsub,hcard⟩
    refine ⟨D.toList,(mem_words _ _ _).mpr ⟨by simpa using hcard,?_⟩,by simp⟩
    intro a ha
    exact (hx a).mpr (hsub (Finset.mem_toList.mp ha))
 theorem choices_toFinset {n : ℕ} (T : Finset (Fin n)) (c : ℕ) : (choices T c).toFinset=deletionChoices T c :=
  choices_eq_of_mem T _ (mem_orderList T) c

 theorem pairs_mem {n : ℕ} (T : Finset (Fin n)) (p : Fin n × Fin n) : p∈pairs T ↔ p∈T×ˢT := by
  simp only [pairs,List.mem_flatMap,List.mem_map,mem_product]
  constructor
  · rintro ⟨i,hi,j,hj,h⟩; cases h; exact ⟨(mem_orderList T _).mp hi,(mem_orderList T _).mp hj⟩
  · rintro ⟨hi,hj⟩; exact ⟨p.1,(mem_orderList T _).mpr hi,p.2,(mem_orderList T _).mpr hj,rfl⟩

 theorem branches_toFinset (I : Instance) (F : Finset (Fin I.n)) (a : ℕ) :
    (branches I F a).toFinset=sparseBranches I F a := by
  unfold branches sparseBranches
  rw [← choices_eq_of_mem (F×ˢF) (pairs F) (pairs_mem F) a]
  simp only [list_toFinset_map,Finset.image_image,Function.comp_def]
end MetricKMedian.Reduction.Enumeration
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open MetricKMedian.MaskProgram
open Preparation.RationalNearest.MaskProgram (erase erase_view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration

 theorem values_toFinset (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    (values I T c).toFinset=deletionValues I T c := by
  ext q
  simp only [values,List.mem_toFinset,List.mem_flatMap,List.mem_map,deletionValues,mem_biUnion,mem_image]
  constructor
  · rintro ⟨D,hD,i,hi,rfl⟩
    exact ⟨D,by rw [← choices_toFinset]; exact List.mem_toFinset.mpr hD,i,(mem_orderList T i).mp hi,rfl⟩
  · rintro ⟨D,hD,i,hi,rfl⟩
    exact ⟨D,by apply List.mem_toFinset.mp; rwa [choices_toFinset],i,(mem_orderList T i).mpr hi,rfl⟩
 theorem endpoints_toFinset (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) :
    (endpoints I T c).toFinset=deletionEndpoints I T c := by
  simp only [endpoints,list_toFinset_map,List.toFinset_cons,values_toFinset,deletionEndpoints]
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_ReductionOutcomesProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.Reduction.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView indices)
open InstanceProgram (Raw view)
open Enumeration
 theorem list_toFinset_flatMap {α β : Type} [DecidableEq α] [DecidableEq β] (f : α → List β) (xs : List α) :
    (xs.flatMap f).toFinset=xs.toFinset.biUnion (fun a => (f a).toFinset) := by
  ext b; simp only [List.mem_toFinset,List.mem_flatMap,mem_biUnion]

 theorem completions_toFinset (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) :
    (completions I F U δ b).toFinset=completionBranches I F U δ b := by
  simp only [completions,list_toFinset_flatMap,list_toFinset_map,choices_toFinset,completionBranches]
  ext S
  simp only [mem_biUnion,mem_image,mem_product,Prod.exists]
  constructor
  · rintro ⟨H,hH,B,hB,he⟩; exact ⟨H,B,⟨hH,hB⟩,he⟩
  · rintro ⟨H,B,⟨hH,hB⟩,he⟩; exact ⟨H,hH,B,hB,he⟩
 theorem outcomes_toFinset (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) :
    (outcomes I F T δ c b).toFinset=sparseOutcomes I F T δ c b := by
  simp only [outcomes,List.toFinset_cons,list_toFinset_flatMap,endpoints_toFinset,completions_toFinset,sparseOutcomes]
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_BranchProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.Input.distance_client_facility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
open Completion.Rational.BestProgram (card card_view)
open Enumeration
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
 theorem allList_toFinset (I : Instance) :
    (allList r hr p c a b δ I).toFinset=reductionOutputs (fun J => J.computedPseudo r hr p c) I δ c a b := by
  unfold allList reductionOutputs
  rw [list_toFinset_flatMap,branches_toFinset]
  apply congrArg ((sparseBranches I I.facilities a).biUnion)
  funext F
  by_cases h : I.k≤F.card
  · simp [branchOut,Branch.allowed,Branch.restricted,h]
    exact outcomes_toFinset I F ((I.restrictFacilities F h).computedPseudo r hr p c) δ c b
  · simp [branchOut,Branch.allowed,h]
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Programs_FinalSelectionProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
open Completion.Rational.BestProgram (card card_view)
 theorem selectList_spec (I : Instance) (L : List (Finset (Fin I.n)))
    (T : Finset (Fin I.n)) (hT : T∈L) (hTF : T⊆I.facilities) (hTne : T.Nonempty) (hTk : T.card≤I.k) :
    selectList I L⊆I.facilities ∧ (selectList I L).Nonempty ∧ (selectList I L).card≤I.k ∧ cost I (selectList I L) ≤ cost I T := by
  have hTp : feasible I T=true := by simp only [feasible,decide_eq_true_eq]; exact ⟨hTF,hTne,hTk⟩
  cases hb : SparseSelect.best (feasible I) (rationalCost I) L with
  | none =>
    have hf := (SparseSelect.best_spec (feasible I) (rationalCost I) L).1.mp hb T hT
    rw [hTp] at hf
    contradiction
  | some S =>
    obtain ⟨_,hS,hmin⟩ := (SparseSelect.best_spec (feasible I) (rationalCost I) L).2 S hb
    have hs : S⊆I.facilities ∧ S.Nonempty ∧ S.card≤I.k := by simpa only [feasible,decide_eq_true_eq] using hS
    simp only [selectList,hb,Option.getD_some]
    refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
    have hc : (rationalCost I S:ℝ)≤(rationalCost I T:ℝ) := by exact_mod_cast hmin T hT hTp
    simpa only [I.cast_rationalCost] using hc
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_OrdinaryListProgram
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
variable (r : ℕ) (hr : 0 < r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
 theorem ordinarySet_spec (α ξ : ℝ) (hc : 0 < c) (hδ : 0<(δ:ℝ)) (hsmall : (δ:ℝ)≤1/6) (hξ : 0<ξ)
    (hfactor : 1+12*(δ:ℝ)≤α+ξ) (ha : (3/2:ℝ)≤a*((δ:ℝ)*ξ/(2*c))) (hb : 6*(α+ξ)*c/((δ:ℝ)*ξ)≤(b:ℝ))
    (hpseudo : ∀ I : Instance, I.computedPseudo r hr p c⊆I.facilities ∧ (I.computedPseudo r hr p c).Nonempty ∧
      (I.computedPseudo r hr p c).card≤I.k+c ∧ cost I (I.computedPseudo r hr p c)≤α*optimum I)
    (I : Instance) : ordinarySet r hr p c a b δ I⊆I.facilities ∧ (ordinarySet r hr p c a b δ I).Nonempty ∧
      (ordinarySet r hr p c a b δ I).card≤I.k ∧ cost I (ordinarySet r hr p c a b δ I)≤(α+ξ)*optimum I := by
  unfold ordinarySet
  split_ifs with hzero
  · obtain ⟨hsub,hne,hk,hcost⟩ := I.zeroOutput_spec hzero
    refine ⟨hsub,hne,hk,?_⟩
    rw [hcost,I.zeroTest_iff.mp hzero,mul_zero]
  · have hz : optimum I≠0 := fun he => hzero (I.zeroTest_iff.mpr he)
    obtain ⟨S,hS,hSF,hSne,hSk,hSc⟩ := reductionOutputs_success_s53 (fun J => J.computedPseudo r hr p c)
      α ξ δ c a b hc hδ hsmall hξ hfactor ha hb hpseudo I (lt_of_le_of_ne I.optimum_nonneg (Ne.symm hz))
    have hm : S∈allList r hr p c a b δ I := by apply List.mem_toFinset.mp; rwa [allList_toFinset]
    obtain ⟨hsub,hne,hk,hcost⟩ := selectList_spec I _ S hm hSF hSne hSk
    exact ⟨hsub,hne,hk,hcost.trans hSc⟩
end MetricKMedian.Reduction.Program
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Main
attribute [-instance] _root_.OAI.MetricKMedian.PCP.Amplifier.bitsDecidableEq _root_.OAI.MetricKMedian.PCP.Compiler.AlphabetProgram.sampleCoding _root_.OAI.MetricKMedian.PCP.Compiler.TableauDirectory.queryCoding _root_.OAI.MetricKMedian.PCP.Compiler.boolHardcoded _root_.OAI.MetricKMedian.PCP.Compiler.functionCoding _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian
open Preparation Finset

theorem exists_internal_program (ε : ℝ) (hε : 0<ε) :
    ∃ algorithm : Instance → List Bool,
      Nonempty (Binary.PolyProgram InstanceProgram.encode id algorithm) ∧
      ∀ I, Correct ε I (algorithm I) := by
  obtain ⟨s,r,hs,hs1,hr,hα,hfactor⟩ := exists_approximation_slack ε hε
  obtain ⟨p⟩ := exists_rational_all_parameters_s53 hs hs
  obtain ⟨C,hC⟩ := exists_nat_gt (max (0:ℝ) (1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)))
  have hCap : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ) := (le_max_right _ _).trans hC.le
  have hCp : 0<C := by exact_mod_cast lt_of_le_of_lt (le_max_left _ _) hC
  let α := ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ))
  have hPseudo : ∀ I : Instance, I.computedPseudo r hr p C⊆I.facilities ∧ (I.computedPseudo r hr p C).Nonempty ∧
      (I.computedPseudo r hr p C).card≤I.k+C ∧ cost I (I.computedPseudo r hr p C)≤α*optimum I :=
    fun I => I.computedPseudo_spec_s53 r hr p hs.le hs hs1 C hCap
  obtain ⟨δ,a,b,hδ,hsδ,hf,ha,hb⟩ := Reduction.reduction_parameters α (ε/2) hα (by positivity) C hCp
  refine ⟨Reduction.Program.algorithm r hr p C a b δ,
    ⟨(Reduction.Program.ordinaryProgram r hr p C a b δ).comp Binary.BooleanLists.unpackProgram⟩,?_⟩
  intro I
  obtain ⟨hOF,hOn,hOk,hCost⟩ := Reduction.Program.ordinarySet_spec r hr p C a b δ α (ε/2) hCp hδ hsδ
    (by positivity) hf ha hb hPseudo I
  refine ⟨Reduction.Program.ordinarySet r hr p C a b δ I,hOF,hOn,hOk,rfl,hCost.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hfactor I.optimum_nonneg

theorem exists_binary_program (ε : ℝ) (hε : 0<ε) :
    ∃ algorithm : Instance → List Bool,
      Nonempty (Binary.PolyProgram encodeInstance id algorithm) ∧ ∀ I, Correct ε I (algorithm I) := by
  obtain ⟨algorithm, ⟨P⟩, hP⟩ := exists_internal_program ε hε
  exact ⟨algorithm, ⟨InputParser.instanceProgram.comp P⟩, hP⟩

theorem main_finite_work : ∀ ε : ℝ, 0<ε →
    ∃ (algorithm : Instance → List Bool) (P : Turing.TM2ComputableInPolyTime encodeInstance id algorithm),
      (∀ k : P.tm.K, Finite (P.tm.Γ k)) ∧ ∀ I, Correct ε I (algorithm I) := by
  intro ε hε
  obtain ⟨algorithm,⟨P⟩,hP⟩ := exists_binary_program ε hε
  exact ⟨algorithm,P.stock,P.finite_work,hP⟩

end MetricKMedian
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Analysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian

theorem factor_above_threshold_s53_oai (ε : ℝ) (hε : 0 < ε) :
    1 + 2 / Real.exp 1 + ε ∈ approximationFactors := by
  obtain ⟨algorithm, p, hp, hcorrect⟩ := main_finite_work ε hε
  exact ⟨algorithm, ⟨p, hp⟩, hcorrect⟩

end MetricKMedian

end Inline_PCPInherited

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.factor_above_threshold_s53_oai := @OAI.MetricKMedian.factor_above_threshold_s53_oai
