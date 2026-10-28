-- Prove2me | solution 1 for OAI.MetricKMedian.Reduction.Program.ordinarySet_spec_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:35:21.314976+00:00
-- url     : https://prove2.me/submissions/6e024d97-4b39-4b44-bd6b-61ef285f02d2

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K074
import Theorems.Thm_OAI_MetricKMedian_Reduction_sparse_branch_exists_s35
import Theorems.Thm_OAI_MetricKMedian_Reduction_sparse_outcome_exists_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalInstanceCost
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem nearest_antitone (I : Instance) (j : Fin I.n)
    {S T : Finset (Fin I.n)} (hS : S.Nonempty) (hST : S ⊆ T) :
    nearest I j T ≤ nearest I j S := by
  obtain ⟨i,hi,he⟩ := I.nearest_attained j S hS
  rw [he]
  exact I.nearest_le j (hST hi)

theorem cost_antitone (I : Instance) {S T : Finset (Fin I.n)}
    (hS : S.Nonempty) (hST : S ⊆ T) : cost I T ≤ cost I S :=
  sum_le_sum (fun j _ => I.nearest_antitone j hS hST)

end Instance
end MetricKMedian
end
end

end OAI
end

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
-- module Solutions.OAIQ035_KM.KMedian_Programs_BoundedEnumerationProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseSelect
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_SparsifyEnumeration
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

theorem sparseBranches_sub (I : Instance) (F : Finset (Fin I.n)) (b : ℕ)
    {F' : Finset (Fin I.n)} (h : F' ∈ sparseBranches I F b) : F' ⊆ F := by
  obtain ⟨P,_,rfl⟩ := mem_image.mp h
  exact filter_subset _ _

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Reduction_BudgetReduction
attribute [-instance] _root_.OAI.MetricKMedian.Instance.instDecidableZeroTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Instance

theorem padded_optimum (I : Instance) :
    ∃ O, O ⊆ I.facilities ∧ O.Nonempty ∧ O.card=I.k ∧ cost I O=optimum I := by
  obtain ⟨S,hSF,hS,hSk,hSc⟩ := I.optimum_attained
  obtain ⟨O,hSO,hOF,hOk⟩ := exists_subsuperset_card_eq hSF hSk I.k_le
  have hO := hS.mono hSO
  refine ⟨O,hOF,hO,hOk,le_antisymm ?_ (I.optimum_le hOF hO hOk.le)⟩
  exact (I.cost_antitone hS hSO).trans_eq hSc

theorem restrict_optimum (I : Instance) (F O : Finset (Fin I.n))
    (hF : I.k ≤ F.card) (hFF : F ⊆ I.facilities) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hOk : O.card ≤ I.k) (hcost : cost I O=optimum I) :
    optimum (I.restrictFacilities F hF)=optimum I := by
  apply le_antisymm
  · exact ((I.restrictFacilities F hF).optimum_le hOF hO hOk).trans_eq hcost
  · obtain ⟨S,hS,hSne,hSk,hSc⟩ := (I.restrictFacilities F hF).optimum_attained
    exact (I.optimum_le (hS.trans hFF) hSne hSk).trans_eq hSc

end Instance

namespace Reduction

theorem reductionOutputs_success
    (pseudo : (I : Instance) → Finset (Fin I.n)) (α η : ℝ) (δ : ℚ) (c a b : ℕ)
    (hc : 0 < c) (hδ : 0 < (δ:ℝ)) (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η)
    (hfactor : 1+12*(δ:ℝ) ≤ α+η)
    (ha : (3/2:ℝ) ≤ a*((δ:ℝ)*η/(2*c)))
    (hb : 6*(α+η)*c/((δ:ℝ)*η) ≤ (b:ℝ))
    (hpseudo : ∀ I, pseudo I ⊆ I.facilities ∧ (pseudo I).Nonempty ∧
      (pseudo I).card ≤ I.k+c ∧ cost I (pseudo I) ≤ α*optimum I)
    (I : Instance) (hopt : 0 < optimum I) :
    ∃ S ∈ reductionOutputs pseudo I δ c a b,
      S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (α+η)*optimum I := by
  let : PseudoMetricSpace (Fin I.n) := I.pseudoMetric
  obtain ⟨O,hOF,hO,hOk,hOc⟩ := I.padded_optimum
  have hC : 0 < cost I O := by rwa [hOc]
  have hcR : (0:ℝ) < c := by exact_mod_cast hc
  have hρ : 0 < (δ:ℝ)*η/(2*c) := div_pos (mul_pos hδ hη) (by positivity)
  obtain ⟨F,hF,hOF',hsp⟩ := sparse_branch_exists_s35 I.facilities O hOF hO hC
    ((δ:ℝ)*η/(2*c)) hρ a ha
  have hFk : I.k ≤ F.card := hOk.symm.le.trans (card_le_card hOF')
  have hFF := sparseBranches_sub I I.facilities a hF
  have hop : optimum (I.restrictFacilities F hFk)=optimum I :=
    I.restrict_optimum F O hFk hFF hOF' hO hOk.le hOc
  obtain ⟨hTF,hT,hTc,hTv⟩ := hpseudo (I.restrictFacilities F hFk)
  change cost I (pseudo (I.restrictFacilities F hFk)) ≤ α*optimum (I.restrictFacilities F hFk) at hTv
  rw [hop,← hOc] at hTv
  obtain ⟨S,hSm,hSF,hS,hSk,hSc⟩ := sparse_outcome_exists_s35 F O
    (pseudo (I.restrictFacilities F hFk)) hOF' hO hOk hTF hT α η δ c b hc hδ hsmall hη
    hC hTv hTc hsp hfactor hb
  refine ⟨S,mem_biUnion.mpr ⟨F,hF,?_⟩,hSF.trans hFF,hS,hSk,?_⟩
  · simp only [dite_eq_left hFk]
    exact hSm
  · rwa [hOc] at hSc

end Reduction
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_RestrictionProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_DeletionProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_ReductionOutcomesProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Programs_BranchProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Programs_FinalSelectionProgram
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
-- module Solutions.OAIQ035_KM.KMedian_Reduction_OrdinaryListProgram
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
 theorem ordinarySet_spec_s35_oai (α ξ : ℝ) (hc : 0 < c) (hδ : 0<(δ:ℝ)) (hsmall : (δ:ℝ)≤1/6) (hξ : 0<ξ)
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
    obtain ⟨S,hS,hSF,hSne,hSk,hSc⟩ := reductionOutputs_success (fun J => J.computedPseudo r hr p c)
      α ξ δ c a b hc hδ hsmall hξ hfactor ha hb hpseudo I (lt_of_le_of_ne I.optimum_nonneg (Ne.symm hz))
    have hm : S∈allList r hr p c a b δ I := by apply List.mem_toFinset.mp; rwa [allList_toFinset]
    obtain ⟨hsub,hne,hk,hcost⟩ := selectList_spec I _ S hm hSF hSne hSk
    exact ⟨hsub,hne,hk,hcost.trans hSc⟩
end MetricKMedian.Reduction.Program
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Reduction.Program.ordinarySet_spec_s35_oai := @OAI.MetricKMedian.Reduction.Program.ordinarySet_spec_s35_oai
