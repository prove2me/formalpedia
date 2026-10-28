-- Prove2me | solution 1 for OAI.SharpRamseyFive.SelectedTuple.eventually_iter_produce
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:47:35.215808+00:00
-- url     : https://prove2.me/submissions/4ec169fa-f3ca-4985-a995-09a4cf8bcb9f

import Mathlib
import Definitions.Def_OAIQ060R004
import Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_eventually_prepared_dispatch

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

end SharpRamseyFive.ParameterHierarchy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

lemma atom_bound_entropy (p : Law α) (A : ℝ)
    (hpa : ∀ a,p a ≤ A) : -Real.log A ≤ entropy p := by
  have hsum : (∑ a,p a*Real.log (p a)) ≤ Real.log A := by
    calc
      _ ≤ ∑ a,p a*Real.log A := Finset.sum_le_sum fun a _ => by
        by_cases h : p a=0
        · simp [h]
        · exact mul_le_mul_of_nonneg_left
            (Real.log_le_log (lt_of_le_of_ne (p.nonneg a) (Ne.symm h)) (hpa a)) (p.nonneg a)
      _ = Real.log A := by rw [←Finset.sum_mul,p.sum_one,one_mul]
  exact neg_le_neg hsum

end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ClassSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.FiniteEntropy

section
open scoped Classical BigOperators
variable {Ω ι κ : Type*} [Fintype Ω] [Fintype κ] [Nonempty κ]

lemma exists_large_class (S : Finset ι) (c : ι → κ) (r : ℕ)
    (h : Fintype.card κ*r ≤ S.card) : ∃ a,r ≤ (classPositions S c a).card := by
  obtain ⟨a,_,ha⟩:=Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s:=S) (t:=Finset.univ) (f:=c) (fun _ _=>Finset.mem_univ _) Finset.univ_nonempty
    (by simpa using h)
  exact ⟨a,ha⟩

theorem fixed_large_class (p : Law Ω) (S : Ω → Finset ι) (c : Ω → ι → κ) (r : ℕ)
    (h : ∀ ω,0 < p ω → Fintype.card κ*r ≤ (S ω).card) :
    ∃ a,(1:ℝ)/Fintype.card κ ≤
      eventMass p (Finset.univ.filter fun ω=>r ≤ (classPositions (S ω) (c ω) a).card) := by
  let choose : Ω → κ := fun ω=>if hp : 0 < p ω then
    (exists_large_class (S ω) (c ω) r (h ω hp)).choose else Classical.choice inferInstance
  have hchoose : ∀ ω,0 < p ω → r ≤ (classPositions (S ω) (c ω) (choose ω)).card := by
    intro ω hp
    simp only [choose,dite_eq_left hp]
    exact (exists_large_class (S ω) (c ω) r (h ω hp)).choose_spec
  have hex : ∃ a,(1:ℝ)/Fintype.card κ ≤ map p choose a := by
    have hcard : (0:ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
    by_contra! hh
    have hs : (∑ a,map p choose a) < ∑ _a:κ,(1:ℝ)/Fintype.card κ :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _=>hh a)
    rw [(map p choose).sum_one] at hs
    have he : (∑ _a:κ,(1:ℝ)/Fintype.card κ)=1 := by simp [hcard.ne']
    rw [he] at hs
    exact lt_irrefl _ hs
  obtain ⟨a,ha⟩:=hex
  refine ⟨a,ha.trans ?_⟩
  simp only [eventMass, Finset.sum_filter]
  change (∑ ω,if choose ω=a then p ω else 0) ≤
    ∑ ω,if r ≤ (classPositions (S ω) (c ω) a).card then p ω else 0
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : 0 < p ω
  · by_cases he : choose ω=a
    · have hω : ω∈Finset.univ.filter (fun ω=>r ≤ (classPositions (S ω) (c ω) a).card) := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _,he ▸ hchoose ω hp⟩
      rw [ite_eq_left he,ite_eq_left ((Finset.mem_filter.mp hω).2)]
    · rw [ite_eq_right he]
      split_ifs <;> first | exact p.nonneg ω | exact le_rfl
  · have hz : p ω=0 := le_antisymm (le_of_not_gt hp) (p.nonneg ω)
    simp only [hz,ite_self,le_refl]

end

open scoped Classical BigOperators

end SharpRamseyFive.FiniteEntropy

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_SelectedTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped BigOperators Classical
open FiniteEntropy
variable {α ι : Type*} [Fintype α] [Fintype ι]

lemma completion_count (I : Finset ι) (v : I → α) :
    (Finset.univ.filter fun s : ι → α => ∀ i : I,s i.val = v i).card =
      Fintype.card α ^ (Fintype.card ι-I.card) := by
  classical
  have he := Fintype.card_congr (completionEquiv I v)
  rw [Fintype.card_fun,Fintype.card_subtype_compl,Fintype.card_coe] at he
  simpa only [Fintype.card_subtype] using he

variable {N l : ℕ}

lemma matching_count (I : {I : Finset (Fin N) // I.card=l}) (f : Fin l → α) :
    (matching I f).card = Fintype.card α ^ (N-l) := by
  let e := I.val.orderIsoOfFin I.property
  have he : matching I f = Finset.univ.filter fun s : Fin N → α =>
      ∀ i : I.val,s i.val = f (e.symm i) := by
    ext s
    simp only [matching,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hs i
      have h := hs (e.symm i)
      have hi : I.val.orderEmbOfFin I.property (e.symm i) = i.val :=
        congrArg Subtype.val (e.apply_symm_apply i)
      rwa [hi] at h
    · intro hs j
      have h := hs (e j)
      change s (I.val.orderEmbOfFin I.property j) = f (e.symm (e j)) at h
      simpa only [e.symm_apply_apply] using h
  rw [he]
  convert (completion_count I.val (fun i => f (e.symm i))) using 1
  · congr
    exact Subsingleton.elim _ _
  · simp only [Fintype.card_fin,I.property]

lemma position_set_count : Fintype.card {I : Finset (Fin N) // I.card=l} = N.choose l := by
  classical
  have he : (Finset.univ.filter fun I : Finset (Fin N) => I.card=l) =
      Finset.univ.powersetCard l := by ext I; simp
  rw [Fintype.card_subtype,he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

theorem occurrence_count (f : Fin l → α) :
    (occurrences (N := N) f).card ≤ N.choose l * Fintype.card α^(N-l) := by
  calc
    _ ≤ ∑ I : {I : Finset (Fin N) // I.card=l},(matching I f).card :=
      Finset.card_biUnion_le
    _ = _ := by simp only [matching_count,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,position_set_count,Nat.cast_id]

theorem selected_atom [Nonempty α] (hl : l ≤ N)
    (p : Law ((Fin N → α) × (Fin l → α))) (C : ℝ) (hC : 0 ≤ C)
    (hstream : ∀ s,first p s ≤ C/(Fintype.card α:ℝ)^N)
    (rev : (Fin l → α) → (Fin l → α))
    (hselect : ∀ s f,0 < p (s,f) →
      s ∈ occurrences f ∨ s ∈ occurrences (rev f)) (f : Fin l → α) :
    second p f ≤ 2*C*(N.choose l:ℝ)/(Fintype.card α:ℝ)^l := by
  classical
  let E := occurrences (N := N) f ∪ occurrences (N := N) (rev f)
  have hm : 0 < (Fintype.card α:ℝ) := by exact_mod_cast Fintype.card_pos
  have hmass : second p f ≤ ∑ s∈E,first p s := by
    change (∑ s,p (s,f)) ≤ _
    calc
      _ ≤ ∑ s,if s∈E then first p s else 0 := by
        apply Finset.sum_le_sum
        intro s _
        by_cases hs : s ∈ E
        · simp only [hs,ite_true]
          exact le_first p s f
        · simp only [hs,ite_false]
          apply le_of_not_gt
          intro hp
          exact hs (Finset.mem_union.mpr (hselect s f hp))
      _ = _ := by rw [←Finset.sum_filter,Finset.filter_univ_mem]
  have hc : E.card ≤ 2*(N.choose l*Fintype.card α^(N-l)) := by
    exact (Finset.card_union_le _ _).trans ((add_le_add (occurrence_count f)
      (occurrence_count (rev f))).trans_eq (by ring))
  have hc' : (E.card:ℝ) ≤ 2*((N.choose l:ℝ)*(Fintype.card α:ℝ)^(N-l)) := by
    exact_mod_cast hc
  calc
    second p f ≤ ∑ s∈E,first p s := hmass
    _ ≤ ∑ _s∈E,C/(Fintype.card α:ℝ)^N := Finset.sum_le_sum fun s _ => hstream s
    _ = (E.card:ℝ)*(C/(Fintype.card α:ℝ)^N) := by simp
    _ ≤ 2*((N.choose l:ℝ)*(Fintype.card α:ℝ)^(N-l))*(C/(Fintype.card α:ℝ)^N) :=
      mul_le_mul_of_nonneg_right hc' (div_nonneg hC (pow_nonneg hm.le _))
    _ = _ := by
      have he : (Fintype.card α:ℝ)^N = (Fintype.card α:ℝ)^(N-l)*(Fintype.card α:ℝ)^l := by
        rw [←pow_add,Nat.sub_add_cancel hl]
      rw [he]
      field_simp

theorem selected_entropy [Nonempty α] (hl : l ≤ N)
    (p : Law ((Fin N → α) × (Fin l → α))) (C : ℝ) (hC : 0 ≤ C)
    (hstream : ∀ s,first p s ≤ C/(Fintype.card α:ℝ)^N)
    (rev : (Fin l → α) → (Fin l → α))
    (hselect : ∀ s f,0 < p (s,f) →
      s ∈ occurrences f ∨ s ∈ occurrences (rev f)) :
    -Real.log (2*C*(N.choose l:ℝ)/(Fintype.card α:ℝ)^l) ≤ entropy (second p) :=
  atom_bound_entropy (second p) _ (selected_atom hl p C hC hstream rev hselect)

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_StageState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open scoped Classical BigOperators
open FiniteEntropy
noncomputable section
variable {α β γ Ω κ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω] [Fintype κ]

namespace SelectedStream
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

theorem entropy_lower [Nonempty α] (hn : n≤N)
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) :
    -Real.log (2*S.density*(N.choose n:ℝ)/(Fintype.card α:ℝ)^n)≤
      entropy (map S.law S.tuple) := by
  have hh:=selected_entropy hn (pair S.law S.stream
    (fun a=>sourceSequence S.reverse S.view (S.tuple a))) S.density S.density_nonneg
    (by simpa only [first_pair] using S.density_bound) id (by
      intro s f hp
      obtain ⟨a,ha,he⟩:=map_positive S.law
        (fun a=>(S.stream a,sourceSequence S.reverse S.view (S.tuple a))) (s,f) hp
      cases he
      exact Or.inl (S.selected a ha))
  simp only [second_pair] at hh
  have he:=entropy_map_le (map S.law S.tuple) (sourceSequence S.reverse S.view)
  rw [map_comp] at he
  exact hh.trans he

end SelectedStream
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

attribute [local instance] OAI.SharpRamseyFive.Marking.markingEndpointsPointDecEq
attribute [local instance] OAI.SharpRamseyFive.Marking.markingEndpointsDualDecEq
attribute [local instance] OAI.SharpRamseyFive.Marking.markingEndpointsPairDecEq
lemma typed_popular_partner (hdim : finrank K V=5)
    (W : ℙ K (Dual K V) → Submodule K (Dual K V)) (r : Fin 5) (b : ℙ K (Dual K V)) :
    ((Finset.univ.filter fun a=>(a,b)∈typedDomain W r true).card:ℝ)≤
      2*(Nat.card K:ℝ)^(4-r.val) := by
  unfold typedDomain
  simp only [↓reduceIte]
  split_ifs with hz
  · by_cases hr : finrank K (W b)=r.val
    · have hsub : (Finset.univ.filter fun a=>(a,b)∈popularDomain W r.val (chooseLevel W r.val)) ⊆
          Finset.univ.filter fun a : ℙ K V=>a.submodule≤(W b).dualCoannihilator := by
        intro a ha
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          ((mem_popularDomain _ _ _ _).mp (Finset.mem_filter.mp ha).2).2.2⟩
      have hc : ((Finset.univ.filter fun a=>(a,b)∈popularDomain W r.val (chooseLevel W r.val)).card:ℝ) ≤
          ((Finset.univ.filter fun a : ℙ K V=>a.submodule≤(W b).dualCoannihilator).card:ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hc.trans (coannihilator_card_bound hdim _ _ hr (by omega))
    · have he : (Finset.univ.filter fun a=>(a,b)∈popularDomain W r.val (chooseLevel W r.val))=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro a ha
        exact hr ((mem_popularDomain _ _ _ _).mp (Finset.mem_filter.mp ha).2).1
      rw [he]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  · have he : (Finset.univ.filter fun a : ℙ K V=>(a,b)∈(∅:Finset (FlagPair K V)))=∅ := by
      ext a
      simp only [Finset.mem_filter,Finset.notMem_empty,and_false]
    rw [he]
    simp only [Finset.card_empty,Nat.cast_zero]
    positivity

end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingClassDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] {N : ℕ}

attribute [local instance] OAI.SharpRamseyFive.Marking.classDomainPointDE
attribute [local instance] OAI.SharpRamseyFive.Marking.classDomainDualDE
attribute [local instance] OAI.SharpRamseyFive.Marking.classDomainDualDualDE
lemma marking_popular_partners_first (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hp' : (m.1 i).1.2.2=true) :
    ∀ a,((Finset.univ.filter fun b=>(a,b)∈markingDomain m i).card:ℝ) ≤
      2*(Nat.card K:ℝ)^((4-(m.1 i).1.1.2.val):ℕ) := by
  intro a
  let W:=decodeState (finiteDecodeRecord (backwardRecord m)) i.rev.val
  let r:=(m.1 i).1.1.2
  have hs : reversedMarkingDomain m i ⊆ typedDomain W r true := by
    simpa only [backwardDomain,finiteTypedDomain,Fin.rev_rev,hp'] using markingDomain_backward m i
  have hc : (Finset.univ.filter fun b=>(a,b)∈markingDomain m i) ⊆
      (Finset.univ.filter fun b=>(b,bidualPoint a)∈typedDomain W r true) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs (Finset.mem_map.mpr
      ⟨(a,b),(Finset.mem_filter.mp hb).2,rfl⟩)⟩
  have hcard : ((Finset.univ.filter fun b=>(a,b)∈markingDomain m i).card:ℝ) ≤
      (Finset.univ.filter fun b=>(b,bidualPoint a)∈typedDomain W r true).card :=
    Nat.cast_le.mpr (Finset.card_le_card hc)
  have hpart := typed_popular_partner (K:=K) (V:=Dual K V)
    (by simpa only [Subspace.dual_finrank_eq] using hdim) W r (bidualPoint a)
  apply hcard.trans
  simpa only [r] using hpart

lemma marking_popular_partners_second (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hp : (m.1 i).1.2.1=true) :
    ∀ b,((Finset.univ.filter fun a=>(a,b)∈markingDomain m i).card:ℝ) ≤
      2*(Nat.card K:ℝ)^((4-(m.1 i).1.1.1.val):ℕ) := by
  intro b
  let W:=decodeState (finiteDecodeRecord (forwardRecord m)) i.val
  let r:=(m.1 i).1.1.1
  have hs : markingDomain m i ⊆ typedDomain W r true := by
    simpa only [forwardDomain,finiteTypedDomain,hp] using markingDomain_forward m i
  have hc : (Finset.univ.filter fun a=>(a,b)∈markingDomain m i) ⊆
      (Finset.univ.filter fun a=>(a,b)∈typedDomain W r true) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs (Finset.mem_filter.mp ha).2⟩
  have hcard : ((Finset.univ.filter fun a=>(a,b)∈markingDomain m i).card:ℝ) ≤
      (Finset.univ.filter fun a=>(a,b)∈typedDomain W r true).card :=
    Nat.cast_le.mpr (Finset.card_le_card hc)
  have hpart := typed_popular_partner (K:=K) (V:=V) hdim W r b
  apply hcard.trans
  simpa only [r] using hpart

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkingClasses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section

lemma slotClass_card : Fintype.card SlotClass=39 := by decide

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N : ℕ}

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))]

local instance slotPointDE_reeb538_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance slotDualDE_reeb538_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
local instance slotDualDualDE_reeb538_1 : DecidableEq (ℙ K (Dual K (Dual K V))) := Classical.decEq _
lemma markingClass_valid (hdim : finrank K V=5) (width : ℝ) (hw : 0 ≤ width)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty) : classValid width m i (markingClass hdim width hw m i) := by
  simp only [markingClass,dite_eq_left hne]
  exact (exists_valid_class hdim width hw m i hne).choose_spec

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_TwoScanContext
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SharpRamseyFive.Marking

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype κ] {N l : ℕ}

attribute [local instance] OAI.SharpRamseyFive.Marking.markedClassFinDE
local instance markedClassPointDE_reeb538_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance markedClassDualDE_reeb538_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
omit [Finite K] in
lemma positive_marked_context (p : Law (κ×(Fin N→FlagPair K V)))
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) :
    ∃ x,0<p (c,x) ∧ markingMessage x=m := by
  obtain ⟨x,_,hx⟩:=Finset.sum_pos_iff_of_nonneg
    (fun x _=>(withMessage p markingMessage).nonneg ((c,m),x)) |>.mp hm
  exact ⟨x,withMessage_support p markingMessage c m x hx⟩

lemma marked_cheap_count (hdim : finrank K V=5) (p : Law (κ×(Fin N→FlagPair K V)))
    (hcons : ∀ c x,0<p (c,x)→TupleConsistent x)
    (c : κ) (m : UnionTranscript (Fin N) (FlagPair K V))
    (hm : 0<first (withMessage p markingMessage) (c,m)) :
    (N:ℝ)-expensiveBound K V≤(unspecified m).card := by
  obtain ⟨x,hx,rfl⟩:=positive_marked_context p c m hm
  have hcard:=unspecified_card twoScanTypes (fun x=>expensiveSet x (Nat.card K))
    (fun x=>reverseExpensive x (Nat.card K)) x
  have hex:=unionExpensive_bound hdim x (hcons c x hx) (Nat.card K)
    (by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K)))
  simp only [Fintype.card_fin] at hcard
  unfold markingMessage expensiveBound
  linarith

theorem marking_fixed_class (hdim : finrank K V=5) (p : Law (κ×(Fin N→FlagPair K V)))
    (hcons : ∀ c x,0<p (c,x)→TupleConsistent x)
    (width : ℝ) (hw : 0≤width) (l : ℕ)
    (hsize : 39*(l:ℝ)+expensiveBound K V≤N) :
    ∃ a : SlotClass,(1:ℝ)/39≤eventMass (first (withMessage p markingMessage))
      (selectedClassEvent l (fun c=>unspecified c.2) (markedCode hdim width hw) a) := by
  have hn : Nonempty SlotClass:=⟨.inl 0⟩
  obtain ⟨a,ha⟩:=fixed_large_class (first (withMessage p markingMessage))
    (fun c=>unspecified c.2) (markedCode hdim width hw) l (by
      intro c hm
      rw [slotClass_card]
      have hh:=marked_cheap_count hdim p hcons c.1 c.2 hm
      exact_mod_cast (show 39*(l:ℝ)≤(unspecified c.2).card by linarith))
  refine ⟨a,?_⟩
  norm_num only [slotClass_card] at ha
  exact ha

end SharpRamseyFive.Marking

end

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_MarkedStreamExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.SelectedTuple
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.Marking.streamClassFinDE
local instance streamClassPointDE_reeb538_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance streamClassDualDE_reeb538_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
lemma actual_marked_class (hdim : finrank K V=5)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible) (ctx : Ω→κ)
    (hcons : ∀ z,0<S.law z→TupleConsistent (S.tuple z))
    (width : ℝ) (hw : 0≤width) (l : ℕ)
    (hsize : 39*(l:ℝ)+expensiveBound K V≤n) :
    ∃ a : SlotClass,(1:ℝ)/39≤eventMass S.law
      (eventPreimage (markedContext ctx S.tuple) (markedEvent hdim width hw l a)) := by
  have hpcons : ∀ c x,0<pair S.law ctx S.tuple (c,x)→TupleConsistent x := by
    intro c x hx
    obtain ⟨z,hz,he⟩:=map_positive S.law (fun z=>(ctx z,S.tuple z)) (c,x) hx
    cases he
    exact hcons z hz
  obtain ⟨a,ha⟩:=marking_fixed_class hdim (pair S.law ctx S.tuple) hpcons width hw l hsize
  refine ⟨a,?_⟩
  rw [markedContext_law,eventMass_map_preimage] at ha
  exact ha

lemma classStream_density (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a)))
    (hm : (1:ℝ)/39≤eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a))) :
    (classStream hdim width hw S ctx hl a hE).density≤39*S.density := by
  change S.density/eventMass S.law _≤39*S.density
  apply (div_le_iff₀ hE).mpr
  have h:=mul_le_mul_of_nonneg_left hm S.density_nonneg
  nlinarith

attribute [local irreducible] unspecified classPositions

lemma markedSelected_valid (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (hl : l≤n) (a : SlotClass) (f : Fin n→FlagPair K V) (ctx : κ)
    (hinc : TupleIncident f) (hcons : TupleConsistent f)
    (hc : (ctx,markingMessage f)∈markedEvent hdim width hw l a) (i : Fin l) :
    classValid width (markingMessage f)
      (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a (ctx,markingMessage f) i) a := by
  have hi:=(marked_indices_properties hdim width hw hl a (ctx,markingMessage f) hc i).2
  have hd:=markedSelected_decodes hdim width hw hl a f ctx hinc hcons hc i
  have hv:=markingClass_valid hdim width hw (markingMessage f) _ ⟨_,hd⟩
  simp only [markedCode] at hi
  rw [hi] at hv
  exact hv

lemma classStream_valid (hdim : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hdim width hw l a)))
    (hinc : ∀ z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀ z,0<S.law z→TupleConsistent (S.tuple z)) :
    ∀ z,0<(classStream hdim width hw S ctx hl a hE).law z→∀ i,
      classValid width (markingMessage (S.tuple z))
        (selectedClassIndices hl (fun c=>unspecified c.2) (markedCode hdim width hw) a
          (markedContext ctx S.tuple z) i) a := by
  intro z hz i
  obtain ⟨hc,hp⟩:=classStream_event hdim width hw S ctx hl a hE z hz
  exact markedSelected_valid hdim width hw hl a (S.tuple z) (ctx z) (hinc z hp) (hcons z hp) hc i
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_DomainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]

variable [Finite K] {N : ℕ}
attribute [local instance] OAI.SharpRamseyFive.Marking.dtPDE
attribute [local instance] OAI.SharpRamseyFive.Marking.dtDDE
attribute [local instance] OAI.SharpRamseyFive.Marking.dtDDDE
lemma marking_highCaps (hd : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (hne : (markingDomain m i).Nonempty)
    (hp : (m.1 i).1.2.1=true) (hp' : (m.1 i).1.2.2=true) :
    HighCaps (markingDomain m i) (m.1 i).1.1.1.val (m.1 i).1.1.2.val := by
  have hh:=marking_popular_caps hd m i hne hp hp'
  exact ⟨markingDomain_card hd m i,hh.2.2.1,hh.2.2.2,
    marking_popular_partners_first hd m i hp',marking_popular_partners_second hd m i hp⟩
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_ReciprocalLossBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical
noncomputable section
variable {Ω β κ : Type} [Fintype Ω] [Fintype β] [Fintype κ]
  {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {Λ J Λ' J' : ℝ}
lemma card_le_of_log_le {a b : ℝ} (ha : 0≤a) (hb : 0<b)
    (h : Real.log a≤Real.log b) : a≤b := by
  rcases eq_or_lt_of_le ha with he|he
  · linarith
  · exact (Real.log_le_log_iff he hb).mp h
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_DescriptionClean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
noncomputable section
variable {Ω β κ : Type} [Fintype Ω] [Fintype κ]
  {n : ℕ} {p : Law Ω} {x : Ω→Fin n→β} {L J : ℝ}
lemma ContextDescription.clean_contains (C : ContextDescription (κ:=κ) p x L J) :
    ∀z,0<p z→∀i,x z i∈C.cleanDomain (C.context z) i := by
  intro z hz i
  have hp : 0 < map p C.context (C.context z) := by
    change 0 < ∑a,if C.context a=C.context z then p a else 0
    have hh:=Finset.single_le_sum (s:=Finset.univ) (a:=z)
      (f:=fun a=>if C.context a=C.context z then p a else 0)
      (fun a _=>by split_ifs; exact p.nonneg a; exact le_rfl) (Finset.mem_univ z)
    simp only at hh
    exact hz.trans_le hh
  simpa only [cleanDomain,ite_eq_left hp] using C.contains z hz i
lemma ContextDescription.clean_cap (C : ContextDescription (κ:=κ) p x L J) :
    ∀c i,((C.cleanDomain c i).card:ℝ)≤Real.exp J := by
  intro c i
  by_cases hp : 0 < map p C.context c
  · obtain ⟨z,hz,rfl⟩:=map_positive p C.context c hp
    have hh:=C.cap z hz i
    rw [cleanDomain,ite_eq_left hp]
    apply card_le_of_log_le (by positivity) (Real.exp_pos _)
    simpa only [Real.log_exp] using hh
  · simp only [cleanDomain,ite_eq_right hp,Finset.card_empty,Nat.cast_zero]
    exact (Real.exp_pos _).le
end
end SharpRamseyFive.FiniteEntropy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_FlagAlphabetLogs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_card_le_two (hd : finrank K V=5) :
    (Fintype.card (ℙ K V):ℝ)≤2*(Nat.card K:ℝ)^4 := by
  have he : (Fintype.card (ℙ K V):ℝ)=∑i∈Finset.range 5,(Nat.card K:ℝ)^i := by
    rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hd]
    push_cast
    rfl
  rw [he]
  have hq : (2:ℝ)≤Nat.card K := by exact_mod_cast Finite.one_lt_card (α:=K)
  have ht:=q_mul_geometric_bound (Nat.card K:ℝ) hq 5
  have hq0 : (0:ℝ)<Nat.card K := by linarith
  have hh : (Nat.card K:ℝ)*(∑i∈Finset.range 5,(Nat.card K:ℝ)^i)≤
      (Nat.card K:ℝ)*(2*(Nat.card K:ℝ)^4) := by nlinarith [ht]
  exact (mul_le_mul_iff_right₀ hq0).mp hh

end
end SharpRamseyFive.Marking

namespace SharpRamseyFive.SelectedTuple
open FiniteEntropy
open scoped Classical BigOperators
noncomputable section

lemma log_choose_le (N n : ℕ) (hn : 0<n) (hnN : n≤N) :
    Real.log (N.choose n)≤(n:ℝ)*(Real.log N-Real.log n+1) := by
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  have hN : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hf : (0:ℝ)<n.factorial := by exact_mod_cast n.factorial_pos
  have hc : (0:ℝ)<N.choose n := by exact_mod_cast Nat.choose_pos hnN
  have h1:=Real.log_le_log hc (Nat.choose_le_pow_div (α:=ℝ) n N)
  rw [Real.log_div (pow_pos hN _).ne' hf.ne',Real.log_pow] at h1
  have h2:=Real.log_le_log (div_pos (pow_pos hp _) hf)
    (Real.pow_div_factorial_le_exp (n:ℝ) hp.le n)
  rw [Real.log_div (pow_pos hp _).ne' hf.ne',Real.log_pow,Real.log_exp] at h2
  nlinarith

variable {α β Ω : Type*} [Fintype α] [Fintype β] [Fintype Ω] [Nonempty α]
variable {N n : ℕ} {admissible : (Fin N→α)→Prop}

omit [Fintype β] [Nonempty α] in
lemma SelectedStream.density_pos (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) :
    0<S.density := by
  have hx : 0<∑ s,map S.law S.stream s := by rw [(map S.law S.stream).sum_one]; norm_num
  obtain ⟨s,_,hs⟩:=Finset.sum_pos_iff_of_nonneg (fun s _=>(map S.law S.stream).nonneg s) |>.mp hx
  have hp:=lt_of_lt_of_le hs (S.density_bound s)
  exact (div_pos_iff.mp hp).resolve_right
    (fun h=>(pow_nonneg (Nat.cast_nonneg _) _).not_gt h.2) |>.1

theorem SelectedStream.entropy_lower_explicit (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (hn : 0<n) (hnN : n≤N) :
    (n:ℝ)*(Real.log (Fintype.card α)-Real.log N+Real.log n-1)-Real.log (2*S.density)≤
      entropy (map S.law S.tuple) := by
  have hα : (0:ℝ)<Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hc : (0:ℝ)<N.choose n := by exact_mod_cast Nat.choose_pos hnN
  have hd : 0<2*S.density := mul_pos (by norm_num) S.density_pos
  have h:=S.entropy_lower hnN
  rw [Real.log_div (mul_pos hd hc).ne' (pow_pos hα _).ne',
    Real.log_mul hd.ne' hc.ne',Real.log_pow] at h
  have hb:=log_choose_le N n hn hnN
  apply le_trans _ h
  have hh:=add_le_add_right (neg_le_neg hb)
    ((n:ℝ)*Real.log (Fintype.card α)-Real.log (2*S.density))
  convert hh using 1 <;> ring

theorem SelectedStream.flag_entropy_lower (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (σ : ℝ) (hσ : 0<σ) (hn : 0<n) (hnN : n≤N)
    (hα : 7*σ≤Real.log (Fintype.card α))
    (hN : (N:ℝ)≤Real.exp (4*σ)*σ) :
    4*σ*n+(n:ℝ)*(Real.log n-σ-Real.log σ-1)-Real.log (2*S.density)≤
      entropy (map S.law S.tuple) := by
  have hNpos : (0:ℝ)<N := by exact_mod_cast (lt_of_lt_of_le hn hnN)
  have hlogN:=Real.log_le_log hNpos hN
  rw [Real.log_mul (Real.exp_pos _).ne' hσ.ne',Real.log_exp] at hlogN
  have nn : (0:ℝ)≤n := Nat.cast_nonneg _
  have h:=S.entropy_lower_explicit hn hnN
  nlinarith

theorem SelectedStream.flag_entropy_lower_fraction
    (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible)
    (σ η c C : ℝ) (hσ : 0<σ) (hc : 0 < c) (hC : S.density≤C)
    (hn : 0<n) (hnN : n≤N) (hα : 7*σ≤Real.log (Fintype.card α))
    (hN : (N:ℝ)≤Real.exp (4*σ)*σ)
    (hlen : c*Real.exp σ*σ^(1+η)≤n) :
    4*σ*n+η*n*Real.log σ+(n:ℝ)*(Real.log c-1)-Real.log (2*C)≤
      entropy (map S.law S.tuple) := by
  have hp : 0 < c*Real.exp σ*σ^(1+η) := mul_pos (mul_pos hc (Real.exp_pos _))
    (Real.rpow_pos_of_pos hσ _)
  have hlogn:=Real.log_le_log hp hlen
  rw [Real.log_mul (mul_pos hc (Real.exp_pos _)).ne'
      (Real.rpow_pos_of_pos hσ _).ne',
    Real.log_mul hc.ne' (Real.exp_pos _).ne',Real.log_exp,
    Real.log_rpow hσ] at hlogn
  have hlogC:=Real.log_le_log (mul_pos (by norm_num : (0:ℝ)<2) S.density_pos)
    (mul_le_mul_of_nonneg_left hC (by norm_num))
  have h:=S.flag_entropy_lower σ hσ hn hnN hα hN
  have nn : (0:ℝ)≤n := Nat.cast_nonneg _
  nlinarith
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_StageNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Asymptotics Real
open scoped Topology
noncomputable section

theorem eventually_stage_recurrence {η : ℝ} (hη : 0<η) (CΔ : ℝ) (_hCΔ : 0≤CΔ) :
    ∀ᶠ σ : ℝ in atTop,∀ (D A Δ : ℝ),0≤D→A≤D*σ^(-η/3)→Δ≤CΔ*D*σ^(6*beta η)→
      σ^beta η*(1+A+Δ*σ^(-η))≤σ^(2*beta η)+D*σ^(-η/4) := by
  have h1 : 0<η/12-beta η := by unfold beta;linarith
  have h2 : 0<3*η/4-7*beta η := by unfold beta;linarith
  have ht1:=tendsto_rpow_neg_atTop h1
  have ht2 : Tendsto (fun σ : ℝ=>CΔ*σ^(-(3*η/4-7*beta η))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop h2).const_mul CΔ
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht1.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    ht2.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with σ hσ hs1 hs2
  intro D A Δ hD hA hΔ
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hbase : σ^beta η≤σ^(2*beta η) := Real.rpow_le_rpow_of_exponent_le hσ (by have := beta_pos hη;linarith)
  have hp1 : σ^beta η*(D*σ^(-η/3))=D*σ^(-η/4)*σ^(-(η/12-beta η)) := by
    calc
      _ =D*(σ^beta η*σ^(-η/3)) := by ring
      _ =_ := by rw [←Real.rpow_add hs,mul_assoc,←Real.rpow_add hs];congr 2;ring
  have hp2 : σ^beta η*(CΔ*D*σ^(6*beta η)*σ^(-η))=
      D*σ^(-η/4)*(CΔ*σ^(-(3*η/4-7*beta η))) := by
    calc
      _ =CΔ*D*(σ^beta η*σ^(6*beta η)*σ^(-η)) := by ring
      _ =_ := by rw [←Real.rpow_add hs,←Real.rpow_add hs];
                 rw [show D*σ^(-η/4)*(CΔ*σ^(-(3*η/4-7*beta η)))=
                   CΔ*D*(σ^(-η/4)*σ^(-(3*η/4-7*beta η))) by ring,
                   ←Real.rpow_add hs];congr 2;ring
  calc
    _ ≤ σ^beta η*(1+D*σ^(-η/3)+(CΔ*D*σ^(6*beta η))*σ^(-η)) := by gcongr
    _ = σ^beta η+D*σ^(-η/4)*σ^(-(η/12-beta η))+
        D*σ^(-η/4)*(CΔ*σ^(-(3*η/4-7*beta η))) := by
      rw [mul_add,mul_add,mul_one,hp1,hp2]
    _ ≤ σ^(2*beta η)+D*σ^(-η/4)*(1/2)+D*σ^(-η/4)*(1/2) := by gcongr
    _ = _ := by ring
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ReciprocalStageArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real Marking ProjectiveIncidence SelectedTuple
open scoped Topology NNReal
noncomputable section

lemma domainSlackConstant_pos : 0<domainSlackConstant := by
  have h1 : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : 0≤Real.log (2*(320/(9/100000)+320)^2) := Real.log_nonneg (by norm_num)
  unfold domainSlackConstant
  linarith

end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_IteratedBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

lemma iterD_eq (σ η : ℝ) (n : ℕ) :
    iterD σ η n=σ^beta η*(1+iterA σ η n+iterDelta σ η n*σ^(-η)) := by
  cases n  <;> simp [iterD,iterA,iterDelta]
lemma iter_budgets_nonneg {σ η : ℝ} (hσ : 0 ≤ σ) (n : ℕ) :
    σ^beta η ≤ iterD σ η n ∧ 0 ≤ iterA σ η n ∧ 0 ≤ iterDelta σ η n := by
  have hC:=domainSlackConstant_pos.le
  have hb:=Real.rpow_nonneg hσ (beta η)
  induction n with
  | zero => dsimp [iterD,iterA,iterDelta];constructor
            · have hh : 0 ≤ 10*σ*σ^(-η) := by positivity
              nlinarith
            · constructor  <;> positivity
  | succ n ih =>
    have hd : 0 ≤ iterD σ η n := hb.trans ih.1
    have hA : 0 ≤ iterD σ η n*σ^(-η/3) := by positivity
    have hΔ : 0 ≤ domainSlackConstant*iterD σ η n*σ^(6*beta η) := by positivity
    dsimp only [iterD,iterA,iterDelta]
    refine ⟨?_,hA,hΔ⟩
    have hh : 0 ≤ domainSlackConstant*iterD σ η n*σ^(6*beta η)*σ^(-η) := by positivity
    nlinarith

theorem eventually_iterD_range {η : ℝ} (hη : 0 < η) (hη' : η < 1/10) :
    ∀ᶠ σ : ℝ in atTop,∀n,iterD σ η n ≤ σ^(1-η/2) := by
  have he0 : 0 < η/2-beta η := by unfold beta;linarith
  have he1 : 0 < 1-η/2-2*beta η := by unfold beta;linarith
  have ht0 : Tendsto (fun σ : ℝ=>11*σ^(-(η/2-beta η))) atTop (𝓝 0) :=
    by simpa using (tendsto_rpow_neg_atTop he0).const_mul 11
  filter_upwards [eventually_ge_atTop (1:ℝ),
    ht0.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    (tendsto_rpow_neg_atTop he1).eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
    (tendsto_rpow_neg_atTop (by linarith : 0 < η/4)).eventually_lt_const (by norm_num : (0:ℝ) < 1/2),
    eventually_stage_recurrence hη domainSlackConstant domainSlackConstant_pos.le]
    with σ hσ h0 h1 hratio hrec
  have hs : 0 < σ := zero_lt_one.trans_le hσ
  have hbase : σ^(2*beta η) ≤ (1/2)*σ^(1-η/2) := by
    have hh:=mul_le_mul_of_nonneg_right h1.le (Real.rpow_nonneg hs.le (1-η/2))
    have hid : σ^(-(1-η/2-2*beta η))*σ^(1-η/2)=σ^(2*beta η) := by
      rw [←Real.rpow_add hs];congr 1;ring
    rwa [hid] at hh
  have hr : σ^(-η/4) ≤ (1:ℝ)/2 := by simpa only [neg_div] using hratio.le
  intro n
  induction n with
  | zero =>
    have hpow : 1 ≤ σ^(1-η) := Real.one_le_rpow hσ (by linarith)
    have hid : 10*σ*σ^(-η)=10*σ^(1-η) := by rw [Real.rpow_sub hs,Real.rpow_one,Real.rpow_neg hs.le];ring
    have hinit : iterD σ η 0 ≤ 11*σ^(1-η+beta η) := by
      dsimp [iterD]
      rw [hid]
      calc
        _  ≤  σ^beta η*(11*σ^(1-η)) := by gcongr;nlinarith
        _ = _ := by rw [mul_left_comm,←Real.rpow_add hs];congr 2;ring
    apply hinit.trans
    have hh:=mul_le_mul_of_nonneg_right h0.le (Real.rpow_nonneg hs.le (1-η/2))
    have hid' : (11*σ^(-(η/2-beta η)))*σ^(1-η/2)=11*σ^(1-η+beta η) := by
      rw [mul_assoc,←Real.rpow_add hs];congr 2;ring
    simpa only [hid',one_mul] using hh
  | succ n ih =>
    have hd:=(iter_budgets_nonneg (η:=η) hs.le n).1
    have h:=hrec (iterD σ η n) (iterA σ η (n+1)) (iterDelta σ η (n+1))
      ((Real.rpow_nonneg hs.le _).trans hd) le_rfl le_rfl
    rw [←iterD_eq] at h
    calc
      _  ≤  σ^(2*beta η)+iterD σ η n*σ^(-η/4) := h
      _  ≤  (1/2)*σ^(1-η/2)+σ^(1-η/2)*(1/2) := by gcongr
      _ = _ := by ring

end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MarkingBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section

lemma marking_budget_bound {σ q η k n A Δ E D : ℝ}
    (hσ : 1≤σ) (_hq : 0<q) (hk : 0<k) (hn : n≤k)
    (hA : 0≤A) (hΔ : 0≤Δ) (hE : E≤9600*q*σ)
    (hlen : q*σ^(1+η)≤2*k)
    (hD : D=σ^beta η*(1+A/k+Δ*σ^(-η))) :
    39*(A+n*Real.log 800+E*Δ)≤(39*(19201+Real.log 800))*k*D*σ^(-beta η) := by
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hcancel : D*σ^(-beta η)=1+A/k+Δ*σ^(-η) := by
    rw [hD,mul_right_comm,←Real.rpow_add hs]
    simp
  have hbase : k*D*σ^(-beta η)=k+A+k*Δ*σ^(-η) := by
    rw [mul_assoc,hcancel]
    field_simp
  have hh : q*σ≤2*k*σ^(-η) := by
    have hh:=mul_le_mul_of_nonneg_right hlen (Real.rpow_nonneg hs.le (-η))
    have he : q*σ^(1+η)*σ^(-η)=q*σ := by
      rw [mul_assoc,←Real.rpow_add hs,show 1+η+-η=(1:ℝ) by ring,Real.rpow_one]
    rwa [he] at hh
  have hlog : 0≤Real.log 800 := Real.log_nonneg (by norm_num)
  have h1:=mul_le_mul_of_nonneg_right hE hΔ
  have h2:=mul_le_mul_of_nonneg_right hh hΔ
  have h3:=mul_le_mul_of_nonneg_right hn hlog
  have hx : 0≤k*Δ*σ^(-η) := by positivity
  have ha : 0≤A*Real.log 800 := mul_nonneg hA hlog
  have hb : 0≤(k*Δ*σ^(-η))*Real.log 800 := mul_nonneg hx hlog
  calc
    _ ≤39*(A+k*Real.log 800+19200*(k*Δ*σ^(-η))) := by nlinarith
    _ ≤(39*(19201+Real.log 800))*(k+A+k*Δ*σ^(-η)) := by nlinarith
    _ =_ := by rw [←hbase];ring

lemma marking_budget_length {σ D k l C c : ℝ} (hσ : 0≤σ) (hD : 0≤D)
    (hC : 0≤C) (hc : 0 < c) (hlen : c*k≤l) (b : ℝ) :
    C*k*D*σ^b≤(C/c)*l*D*σ^b := by
  have hh : k≤l/c := (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hlen)
  calc
    _ ≤C*(l/c)*D*σ^b := by gcongr
    _ =_ := by ring
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Streams_SelectedLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open FiniteEntropy
noncomputable section
variable {Ω α β : Type} [Fintype Ω] [Fintype α] [Fintype β]
  {N n : ℕ} {admissible : (Fin N→α)→Prop}
omit [Fintype β] in
lemma SelectedStream.length_le_source (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible) : n≤N := by
  obtain ⟨z,hz⟩:=S.law.exists_positive
  obtain ⟨e,he⟩:=(mem_occurrences_iff _ _).mp (S.selected z hz)
  have h:=Fintype.card_le_of_injective e e.injective
  simpa only [Fintype.card_fin] using h
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Entropy_MarkingNumerics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
omit [FiniteDimensional K V] [Fintype (ℙ K (Dual K V))] in
lemma point_log_one_add_card (hd : finrank K V=5) (σ : ℝ)
    (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) :
    Real.log (1+Fintype.card (ℙ K V))≤6*σ := by
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hp:=point_card_le_two hd
  have hh : (1:ℝ)+Fintype.card (ℙ K V)≤3*(Nat.card K:ℝ)^4 := by
    have hh : (1:ℝ)≤(Nat.card K:ℝ)^4 := one_le_pow₀ hq1
    linarith
  have ht:=Real.log_le_log (by positivity : (0:ℝ)<1+Fintype.card (ℙ K V)) hh
  rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow,←hq,Real.log_exp] at ht
  have hl : Real.log 3≤2 := by have hh:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3);linarith
  norm_num only [Nat.cast_ofNat] at ht
  linarith
omit [FiniteDimensional K V] in
lemma expensiveBound_coarse [Fintype (ℙ K (Dual K (Dual K V)))] (hd : finrank K V=5) (σ : ℝ)
    (hσ : 1≤σ) (hq : Real.exp σ=Nat.card K) :
    expensiveBound K V≤9600*Real.exp σ*σ := by
  have ha:=point_log_one_add_card hd σ hσ hq
  have hb:=point_log_one_add_card (K:=K) (V:=Dual K V) (by simpa using hd) σ hσ hq
  unfold expensiveBound
  rw [←hq]
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hb ha) (by positivity : (0:ℝ)≤800*Real.exp σ)]

theorem eventually_stream_cheap_entropy {η : ℝ} (hη : 0<η) (c C : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀ (Ω α β : Type) [Fintype Ω] [Fintype α] [Fintype β] [Nonempty α],
    ∀ (N n : ℕ) (admissible : (Fin N→α)→Prop) (S : SelectedStream (Ω:=Ω) (β:=β) N n admissible),
      1≤σ→7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*Real.exp σ*σ^(1+η)≤n→S.density≤C→
      (n:ℝ)*(4*σ+Real.log 153)≤entropy (map S.law S.tuple) := by
  have ht : Tendsto (fun σ : ℝ=>η*Real.log σ) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hη
  have he : Tendsto (fun σ : ℝ=>c*Real.exp σ) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  filter_upwards [ht.eventually_ge_atTop (Real.log 153+2-Real.log c),
    he.eventually_ge_atTop (Real.log (2*C))] with σ ht he
  intro Ω α β _ _ _ _ N n admissible S hσ hα hN hlen hC
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hn : 0<n := by
    have hh : 0<(n:ℝ) := (by positivity : 0 < c*Real.exp σ*σ^(1+η)).trans_le hlen
    exact_mod_cast hh
  have hlog : Real.log (2*C)≤n := by
    have hp : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ c*Real.exp σ)
    nlinarith
  have hb:=S.flag_entropy_lower_fraction σ η c C hs hc hC hn S.length_le_source hα hN hlen
  have hh:=mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg n)
  nlinarith
end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ClassifiedStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy SelectedTuple CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n l : ℕ} {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.Marking.csFinDE
local instance csPDE_reeb538_1 : DecidableEq (ℙ K V) := Classical.decEq _
local instance csDDE_reeb538_1 : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _
omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
lemma classValid_domainClass (hd : finrank K V=5) (width : ℝ)
    (m : UnionTranscript (Fin n) (FlagPair K V)) (i : Fin n) (a : SlotClass)
    (hne : (markingDomain m i).Nonempty) (hc : classValid width m i a) :
    DomainClass width (markingDomain m i) a := by
  rcases a with b|b|⟨r,s⟩
  · exact hc
  · exact hc
  · obtain ⟨hr,hs,hp,hp',hgt⟩:=hc
    refine ⟨hgt,?_⟩
    have hh:=marking_highCaps hd m i hne hp hp'
    simpa only [hr,hs] using hh

lemma classStream_domainClass (hd : finrank K V=5) (width : ℝ) (hw : 0≤width)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N n admissible)
    (ctx : Ω→κ) (hl : l≤n) (a : SlotClass)
    (hE : 0<eventMass S.law (eventPreimage (markedContext ctx S.tuple)
      (markedEvent hd width hw l a)))
    (hinc : ∀z,0<S.law z→TupleIncident (S.tuple z))
    (hcons : ∀z,0<S.law z→TupleConsistent (S.tuple z)) :
    let T:=classStream hd width hw S ctx hl a hE
    ∀c,0 < map T.law (markedContext ctx S.tuple) c→∀i,
      DomainClass width (classDomain hd width hw hl a c i) a := by
  intro T c hc i
  obtain ⟨z,hz,rfl⟩:=map_positive T.law (markedContext ctx S.tuple) c hc
  have hmem:=classStream_contains hd width hw S ctx hl a hE hinc hcons z hz i
  exact classValid_domainClass hd width _ _ a ⟨T.tuple z i,hmem⟩
    (classStream_valid hd width hw S ctx hl a hE hinc hcons z hz i)

end
end SharpRamseyFive.Marking

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_StageCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.ParameterHierarchy
open Filter Real
open scoped Topology
noncomputable section
lemma stage_cuts (n : ℕ) (hn : 40000≤n) :
    8≤n/100 ∧ (n:ℝ)≤200*(n/100:ℕ) ∧
    (100:ℝ)*(n/100:ℕ)≤n ∧ (n/20000:ℕ)≤n/100 ∧
    ((n/20000:ℕ):ℝ)≤(n/100:ℕ)/100 ∧ (n:ℝ)≤40000*(n/20000:ℕ) := by
  have h1 : 8≤n/100 := by omega
  have h2 : n≤200*(n/100) := by omega
  have h3 : 100*(n/100)≤n := by omega
  have h4 : n/20000≤n/100 := by omega
  have h5 : 100*(n/20000)≤n/100 := by omega
  have h6 : n≤40000*(n/20000) := by omega
  refine ⟨h1,?_,?_,h4,?_,?_⟩
  · exact_mod_cast h2
  · exact_mod_cast h3
  · have hh : (100:ℝ)*(n/20000:ℕ)≤(n/100:ℕ) := by exact_mod_cast h5
    linarith
  · exact_mod_cast h6

theorem eventually_marking_small {η : ℝ} (hη : 0<η) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ σ : ℝ in atTop,∀n : ℕ,c*Real.exp σ*σ^(1+η)≤n→
      40000≤n ∧ 19200*Real.exp σ*σ≤n := by
  have ht : Tendsto (fun σ : ℝ=>c*Real.exp σ) atTop atTop :=
    Real.tendsto_exp_atTop.const_mul_atTop hc
  have hp : Tendsto (fun σ : ℝ=>c*σ^η) atTop atTop :=
    (tendsto_rpow_atTop hη).const_mul_atTop hc
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually_ge_atTop 40000,hp.eventually_ge_atTop 19200]
    with σ hσ he hp
  intro n hn
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hpow : 1≤σ^(1+η) := Real.one_le_rpow hσ (by linarith)
  have hm:=mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ c*Real.exp σ)
  have hnreal : (40000:ℝ)≤n := by nlinarith
  have hh:=mul_le_mul_of_nonneg_right hp (by positivity : 0≤Real.exp σ*σ)
  have hid : c*Real.exp σ*σ^(1+η)=(c*σ^η)*(Real.exp σ*σ) := by
    rw [Real.rpow_add hs,Real.rpow_one];ring
  exact ⟨by exact_mod_cast hnreal,by rw [hid] at hn;nlinarith⟩
end
end SharpRamseyFive.ParameterHierarchy

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_ClassPrepared
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.cmFinDE
variable {K V α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype α]

attribute [instance] ClassifiedPrepared.finiteSample ClassifiedPrepared.finiteContext

theorem classify_coded [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
    [Nonempty (ℙ K (Dual K (Dual K V)))]
    {N n m : ℕ} {adm : (Fin N→α)→Prop} {d Λ Δ M B width : ℝ}
    (hd : finrank K V=5) (hw : 0≤width) (hΔ : 0≤Δ)
    (S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M)
    (hm : m≤n) (hsize : 39*(m:ℝ)+expensiveBound K V≤n)
    (hent : n*Real.log (153*(Nat.card K:ℝ)^4)≤entropy (map S.stream.law S.stream.tuple))
    (hB : 39*(Λ+n*Real.log 800+expensiveBound K V*Δ)≤B) :
    Nonempty (ClassifiedPrepared (K:=K) (V:=V) N m adm (39*d)
      (Real.log (153*(Nat.card K:ℝ)^4)) B M width) := by
  let ctx:=S.description.context
  obtain ⟨a,ha⟩:=actual_marked_class hd S.stream ctx S.geometric.consistent width hw m hsize
  have hE : 0<eventMass S.stream.law (eventPreimage (markedContext ctx S.stream.tuple)
      (markedEvent hd width hw m a)) := lt_of_lt_of_le (by norm_num) ha
  have hcheap : 0≤Real.log (153*(Nat.card K:ℝ)^4) := by
    apply Real.log_nonneg
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
    have hh:=one_le_pow₀ (n:=4) hq
    linarith
  let P:=classPrepared hd width hw S.stream ctx hm a hE ha
    S.geometric.incident S.geometric.consistent S.description.cleanDomain
    (Real.exp (Real.log (153*(Nat.card K:ℝ)^4)+Δ)) 0 Λ M
    (Real.one_le_exp_iff.mpr (add_nonneg hcheap hΔ)) S.description.clean_cap
    S.description.clean_contains (by simpa only [Real.log_exp,add_sub_cancel_left] using hΔ)
    (sub_nonpos.mpr hent) S.description.entropy_bound S.geometric.occupancy
  have hBP : 39*(0+Λ+n*Real.log 800+expensiveBound K V*
      (Real.log (Real.exp (Real.log (153*(Nat.card K:ℝ)^4)+Δ))-Real.log (153*(Nat.card K:ℝ)^4)))≤B := by
    simpa only [zero_add,Real.log_exp,add_sub_cancel_left] using hB
  refine ⟨{
    sample := S.sample
    context := (S.code × UnionTranscript (Fin n) (FlagPair K V))
    stream := classStream hd width hw S.stream ctx hm a hE
    ctx := markedContext ctx S.stream.tuple
    prepared := P.mono hBP
    slotClass := a
    classified := ?_
    density_bound := ?_ }⟩
  · exact classStream_domainClass hd width hw S.stream ctx hm a hE
      S.geometric.incident S.geometric.consistent
  · exact (classStream_density hd width hw S.stream ctx hm a hE ha).trans
      (mul_le_mul_of_nonneg_left S.density_bound (by norm_num))
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Marking_CompressionStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
noncomputable section
local instance acsFinDE_reeb538_1 (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
lemma markingStageConstant_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ markingStageConstant c := by
  have hlog : 0≤Real.log 800 := Real.log_nonneg (by norm_num)
  unfold markingStageConstant
  positivity

theorem eventually_actual_compression {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c d Cm : ℝ) (hc : 0 < c) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K V α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))]
      [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (Λ Δ M k₀ D : ℝ)
      (_S : CodedStream (K:=K) (V:=V) N n adm d Λ (Real.log (153*(Nat.card K:ℝ)^4)+Δ) M),
      finrank K V=5→3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→(n:ℝ)≤k₀→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤Λ→0≤Δ→0≤M→M≤Cm*σ→
      D=σ^beta η*(1+Λ/k₀+Δ*σ^(-η))→σ^beta η≤D→D≤σ^(1-η/2)→
      Nonempty (CodedStream (K:=K) (V:=V) N (n/20000) adm (44*d)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) ∨
      Nonempty (CodedStream (K:=K) (V:=Dual K V) N (n/20000) adm (44*d)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) := by
  filter_upwards [eventually_prepared_dispatch hη hη' (c/200) (markingStageConstant c) Cm (39*d)
      (by positivity) (markingStageConstant_nonneg hc) hCm,
    eventually_stream_cheap_entropy hη c d hc,eventually_marking_small hη c hc]
    with σ hstep hent hsmall
  intro q₀ K V α _ _ _ _ _ _ _ _ _ _ _ _ _ _ N n adm Λ Δ M k₀ D S
    hd hq3 hcard hσ hq hα hN hlen hn hk₀ hk₀lo hΛ hΔ hM hMhi hDeq hD hDhi
  have hs : 0<σ := zero_lt_one.trans_le hσ
  have hqpos : (0:ℝ)<Nat.card K := by rw [←hq];positivity
  have hkp : 0<k₀ := by have h:=mul_pos hqpos (Real.rpow_pos_of_pos hs (1+η));linarith
  have hDp : 0<D := (Real.rpow_pos_of_pos hs _).trans_le hD
  have hdpos : 0≤d := S.stream.density_nonneg.trans S.density_bound
  have hlen' : c*Real.exp σ*σ^(1+η)≤n := by rwa [hq]
  obtain ⟨hnlarge,hneglig⟩:=hsmall n hlen'
  obtain ⟨hm8,hmlo,hmhi,hlm,hlhi,hllo⟩:=stage_cuts n hnlarge
  let m:=n/100
  have hmlen : c/200*(Nat.card K:ℝ)*σ^(1+η)≤(m:ℝ) := by dsimp [m];nlinarith
  have hmle : m≤n := Nat.div_le_self _ _
  have hEmark:=expensiveBound_coarse (K:=K) (V:=V) hd σ hσ hq
  have hE : expensiveBound K V≤9600*(Nat.card K:ℝ)*σ := by rwa [hq] at hEmark
  have hsize : 39*(m:ℝ)+expensiveBound K V≤n := by dsimp [m];nlinarith
  have hJ : Real.log (153*(Nat.card K:ℝ)^4)=4*σ+Real.log 153 := by
    rw [Real.log_mul (by norm_num) (pow_pos hqpos _).ne',Real.log_pow,←hq,Real.log_exp]
    norm_num;ring
  have hcheap:=hent S.sample α (FlagPair K V) N n adm S.stream hσ hα hN hlen' S.density_bound
  rw [←hJ] at hcheap
  let B:=markingStageConstant c*(m:ℝ)*D*σ^(-beta η)
  have hB0 : 0≤B := by dsimp [B];exact mul_nonneg (mul_nonneg (mul_nonneg (markingStageConstant_nonneg hc) (Nat.cast_nonneg _)) hDp.le) (Real.rpow_nonneg hs.le _)
  have hbudget : 39*(Λ+n*Real.log 800+expensiveBound K V*Δ)≤B := by
    have hb:=marking_budget_bound hσ hqpos hkp hn hΛ hΔ hE hk₀lo hDeq
    apply hb.trans
    have hmK : (c/200)*k₀≤(m:ℝ) :=
      (mul_le_mul_of_nonneg_left hk₀ (by positivity)).trans (by nlinarith [hmlen])
    exact marking_budget_length hs.le hDp.le (by have:=Real.log_nonneg (show (1:ℝ)≤800 by norm_num);positivity)
      (by positivity) hmK (-beta η)
  obtain ⟨P⟩:=classify_coded hd (by positivity : 0≤D*σ^(3*beta η)) hΔ S hmle hsize (by convert hcheap using 1; congr 1; exact Subsingleton.elim _ _) hbudget
  have hout:=hstep q₀ K V P.sample P.context α N m (n/20000) adm P.stream P.ctx D B M k₀ P.prepared P.slotClass
    hd hq3 hcard hσ hq hα hN P.density_bound hm8 hD hDhi hmlen
    (by exact (by exact_mod_cast hmle : (m:ℝ)≤n).trans (hn.trans hk₀)) hlhi hk₀lo
    hB0 le_rfl hM hMhi P.classified
  have hden : (10/9)*P.stream.density≤44*d := by
    have hh:=P.density_bound
    linarith only [hh,hdpos]
  rcases hout with h|h
  · obtain ⟨out⟩:=h
    exact Or.inl ⟨out.mono hden le_rfl le_rfl⟩
  · obtain ⟨out⟩:=h
    exact Or.inr ⟨out.mono hden le_rfl le_rfl⟩
end
end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_TerminalStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization

noncomputable section
variable (K α : Type) [Field K] [Finite K] [Fintype α]

attribute [instance] PolarState.group PolarState.module PolarState.dimension PolarState.points
  PolarState.hyperplanes PolarState.bipoints PolarState.pointNonempty PolarState.planeNonempty
  PolarState.bipointNonempty
variable {K α}

theorem eventually_polar_compression {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c d Cm : ℝ) (hc : 0 < c) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K α : Type) [Field K] [Finite K] [CharP K q₀]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (Λ Δ M k₀ D : ℝ)
      (_S : PolarState K α N n adm d Λ Δ M),
      3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→(n:ℝ)≤k₀→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤Λ→0≤Δ→0≤M→M≤Cm*σ→
      D=σ^beta η*(1+Λ/k₀+Δ*σ^(-η))→σ^beta η≤D→D≤σ^(1-η/2)→
      Nonempty (PolarState K α N (n/20000) adm (44*d)
        (k₀*D*σ^(-η/3)) (domainSlackConstant*D*σ^(6*beta η)) M) := by
  filter_upwards [eventually_actual_compression hη hη' c d Cm hc hCm] with σ h
  intro q₀ K α _ _ _ _ _ N n adm Λ Δ M k₀ D S hq3 hcard hσ hq hα hN hlen hn hk hklo
    hΛ hΔ hM hMhi hDeq hD hDhi
  have hh:=h q₀ K S.ambient α N n adm Λ Δ M k₀ D S.coded S.dim hq3 hcard hσ hq hα hN
    hlen hn hk hklo hΛ hΔ hM hMhi hDeq hD hDhi
  rcases hh with h|h
  · obtain ⟨T⟩:=h
    exact ⟨PolarState.of S.dim T⟩
  · obtain ⟨T⟩:=h
    let : Fintype (ℙ K (Dual K (Dual K (Dual K S.ambient)))):=
      Fintype.ofEquiv (ℙ K (Dual K S.ambient)) bidualPoint
    let : Nonempty (ℙ K (Dual K (Dual K (Dual K S.ambient)))) :=
      ⟨bidualPoint (Classical.arbitrary (ℙ K (Dual K S.ambient)))⟩
    exact ⟨PolarState.of (by simpa using S.dim) T⟩

end
end

open FiniteEntropy
open scoped Classical BigOperators

end SharpRamseyFive.SelectedTuple

end OAI
end

section
-- module Solutions.OAIQ060_R5.RamseyFive_Iteration_PolarIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section

theorem eventually_iter_produce_oai {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (m : ℕ) (c d Cm : ℝ) (hc : 0 < c) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K α : Type) [Field K] [Finite K] [CharP K q₀]
      [Fintype α] [Nonempty α],
    ∀ (N n : ℕ) (adm : (Fin N→α)→Prop) (M k₀ : ℝ)
      (_ : PolarState K α N n adm d 0 (10*σ) M),
      3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      7*σ≤Real.log (Fintype.card α)→(N:ℝ)≤Real.exp (4*σ)*σ→
      c*(Nat.card K:ℝ)*σ^(1+η)≤n→(n:ℝ)≤k₀→k₀≤(Nat.card K:ℝ)*σ^(1+η)→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤M→M≤Cm*σ→
      Nonempty (PolarState K α N (iterLength n m) adm ((44:ℝ)^m*d)
        (k₀*iterA σ η m) (iterDelta σ η m) M) ∧
      (c/(40000:ℝ)^m)*(Nat.card K:ℝ)*σ^(1+η)≤(iterLength n m:ℝ) ∧ iterLength n m≤n := by
  induction m with
  | zero =>
    filter_upwards [] with σ
    intro q₀ K α _ _ _ _ _ N n adm M k₀ S _ _ _ _ _ _ hlen _ _ _ _ _
    simpa only [iterLength,iterA,iterDelta,pow_zero,one_mul,mul_zero,div_one] using
      (show Nonempty (PolarState K α N n adm d 0 (10*σ) M) ∧
        c*(Nat.card K:ℝ)*σ^(1+η)≤(n:ℝ) ∧ n≤n from ⟨⟨S⟩,hlen,le_rfl⟩)
  | succ m ih =>
    have hcp : 0 < c/(40000:ℝ)^m := by positivity
    filter_upwards [ih,eventually_polar_compression hη hη' (c/(40000:ℝ)^m) ((44:ℝ)^m*d) Cm hcp hCm,
      eventually_marking_small hη (c/(40000:ℝ)^m) hcp,eventually_iterD_range hη hη']
      with σ hI hstep hsmall hrange
    intro q₀ K α _ _ _ _ _ N n adm M k₀ S hq3 hcard hσ hq hα hN hlen hn hk hklo hM hMhi
    obtain ⟨⟨T⟩,hTlen,hTn⟩:=hI q₀ K α N n adm M k₀ S hq3 hcard hσ hq hα hN hlen hn hk hklo hM hMhi
    have hs : 0<σ := zero_lt_one.trans_le hσ
    have hqpos : (0:ℝ)<Nat.card K := by rw [←hq];positivity
    have hkp : 0<k₀ := by
      have hh : 0 < c*(Nat.card K:ℝ)*σ^(1+η) := by positivity
      linarith only [hh,hlen,hn]
    have hnum:=iter_budgets_nonneg hs.le (η:=η) m
    have hlarge:=(hsmall (iterLength n m) (by simpa only [hq] using hTlen)).1
    have hcut:=(stage_cuts (iterLength n m) hlarge).2.2.2.2.2
    have hout:=hstep q₀ K α N (iterLength n m) adm (k₀*iterA σ η m) (iterDelta σ η m) M k₀
      (iterD σ η m) T hq3 hcard hσ hq hα hN hTlen
      ((by exact_mod_cast hTn : (iterLength n m:ℝ)≤n).trans hn) hk hklo
      (mul_nonneg hkp.le hnum.2.1) hnum.2.2 hM hMhi
      (by rw [iterD_eq];congr 2;field_simp) hnum.1 (hrange m)
    refine ⟨?_,?_,(Nat.div_le_self _ _).trans hTn⟩
    · simpa only [iterLength,iterA,iterDelta,pow_succ,mul_assoc,mul_left_comm,mul_comm] using hout
    · change c/(40000:ℝ)^(m+1)*(Nat.card K:ℝ)*σ^(1+η)≤((iterLength n m/20000:ℕ):ℝ)
      have hid : c/(40000:ℝ)^(m+1)*(Nat.card K:ℝ)*σ^(1+η)=
          ((c/(40000:ℝ)^m)*(Nat.card K:ℝ)*σ^(1+η))/40000 := by
        rw [pow_succ];ring
      rw [hid]
      linarith only [hTlen,hcut]

end
end SharpRamseyFive.SelectedTuple

end OAI
end

theorem solution : type_of% @OAI.SharpRamseyFive.SelectedTuple.eventually_iter_produce_oai := @OAI.SharpRamseyFive.SelectedTuple.eventually_iter_produce_oai
