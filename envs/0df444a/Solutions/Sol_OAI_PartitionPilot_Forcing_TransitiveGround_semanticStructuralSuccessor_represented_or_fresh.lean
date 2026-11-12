-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_or_fresh
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:36:53.451199+00:00
-- url     : https://prove2.me/submissions/0c4673df-9c9e-406f-adc0-160d6472b7d7

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P011

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_DecodedFunctionGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u}) {A B : Type u}

theorem decoded_function_graph_mem (s : Presentation A) (t : Presentation B) {f : ZFSet.{u}}
    (hf : f ∈ M.sets) (h : ZFSet.IsFunc s.carrier t.carrier f) :
    s.graph t (s.decodeFunction t f h) ∈ M.sets := by
  rw [s.graph_decodeFunction]
  exact hf

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NonemptyTupleFields
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementIndexCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {level C E U Rf Rc : ZFSet.{u}} (hl : level ∈ M.sets) (hC : C ∈ M.sets)
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hf : Rf ∈ M.sets) (hc : Rc ∈ M.sets) :
    refinementIndexCode level C E U Rf Rc ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 5 _
    (Fin.cases hl (Fin.cases hC (Fin.cases hE (Fin.cases hU
      (Fin.cases hf (Fin.cases hc (fun j => Fin.elim0 j)))))))

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameRenameSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem ordinaryEqualityDecisions_subset (Q order sigma tau : ZFSet.{u}) :
    M.ordinaryEqualityDecisions Q order sigma tau ⊆ Q :=
  fun _ h => (ZFSet.mem_sep.1 h).1

variable {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_ordinaryEqualityDecisionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {n : Nat} (ci oi pi si ti : Fin n) (env : Fin n → ZFSet.{u})
    (sigma tau : (M.nameDomain s).names) (p : P)
    (hc : env ci = s.carrier) (ho : env oi = s.conditionOrder)
    (hp : env pi = s.encode p) (hs : env si = sigma.val.val) (ht : env ti = tau.val.val) :
    Realize M.sets (ordinaryEqualityDecisionFormula ci oi pi si ti) env ↔
      Name.ForcesEq p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesEq q sigma.val tau.val := by
  rw [ordinaryEqualityDecisionFormula, realize_disj]
  let names : Assignment (M.nameDomain s) 2 := extend sigma (extend tau Fin.elim0)
  have meaning (phi : SetFormula 2) := M.realize_ordinaryGroundForcing s pairing unions powers
    separation collection carrier order (0 : Fin 2) 1 phi (extend ci (extend oi Fin.elim0)) pi
    (extend si (extend ti Fin.elim0)) env hc ho p names hp
    (Fin.cases hs (Fin.cases ht (fun i => Fin.elim0 i)))
  exact or_congr (meaning (.equal 0 1)) (meaning (.neg (.equal 0 1)))

theorem ordinaryEqualityDecisions_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (sigma tau : (M.nameDomain s).names) (p : P) :
    s.encode p ∈ M.ordinaryEqualityDecisions s.carrier s.conditionOrder sigma.val.val tau.val.val ↔
      Name.ForcesEq p sigma.val tau.val ∨ ∀ q, q ≤ p → ¬ Name.ForcesEq q sigma.val tau.val := by
  rw [ordinaryEqualityDecisions, ZFSet.mem_sep, and_iff_right (s.encode_mem p)]
  exact M.realize_ordinaryEqualityDecisionFormula s pairing unions powers separation collection
    carrier order 1 2 0 3 4 _ sigma tau p rfl rfl rfl rfl rfl

theorem ordinaryEqualityDecisions_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (sigma tau : (M.nameDomain s).names) :
    ∀ p ∈ s.carrier, ∃ q ∈ M.ordinaryEqualityDecisions s.carrier s.conditionOrder
      sigma.val.val tau.val.val, ZFSet.pair q p ∈ s.conditionOrder := by
  intro z hz
  obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 hz
  obtain ⟨q, below, decided⟩ := decisionWitness_dense (M.nameDomain s) (.equal 0 1)
    (extend sigma (extend tau Fin.elim0)) p
  exact ⟨s.encode q,
    (M.ordinaryEqualityDecisions_entry s pairing unions powers separation collection carrier order
      sigma tau q).2 decided, (s.pair_mem_conditionOrder q p).2 below⟩

end TransitiveGround




end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceNameNormalization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem eval_subset_familySet_of_code_subset (H : ConditionFilter P)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (tau : Name s)
    (shape : tau.val ⊆ ZFSet.prod T s.carrier) :
    eval {p | H.mem p} tau ⊆ eval {p | H.mem p} (familySet ⊤ T valid) := by
  intro x member
  obtain ⟨sigma, p, entry, _, value⟩ := (mem_eval {p | H.mem p} tau x).1 member
  have term : sigma.val ∈ T := (ZFSet.pair_mem_prod.1 (shape entry)).1
  exact (mem_eval_familySet {p | H.mem p} ⊤ H.top_mem T valid x).2
    ⟨sigma, term, value⟩

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RefinementAssignmentLabelNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

variable {G : Type v} [Group G] (a : PosetAction G P)

theorem refinementClass_support (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (R w : Name s) (K : Subgroup G)
    (relation : K ≤ a.stabilizer s R) (representative : K ≤ a.stabilizer s w) :
    K ≤ a.stabilizer s (refinementClass T valid R w) := by
  intro g hg
  change a.act s g _ = _
  rw [act_refinementClass a T valid closed, relation hg, representative hg]

theorem refinementClass_hs (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (children : ∀ z : Name s, z.val ∈ T → HereditarilySymmetric a s F z)
    (R w : Name s) (K : Subgroup G) (member : F.mem K)
    (relation : K ≤ a.stabilizer s R) (representative : K ≤ a.stabilizer s w) :
    HereditarilySymmetric a s F (refinementClass T valid R w) :=
  HereditarilySymmetric.mk
    (F.upward member (refinementClass_support a T valid closed R w K relation representative))
    (fun z p entry => children z ((entry_refinementClass T valid R w z p).1 entry).1)

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundRefinementQuotientNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)
variable (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
include closed

theorem refinementClass_hs_of_hs (F : NormalSubgroupFamily G)
    (children : ∀ w : Name s, w.val ∈ T → HereditarilySymmetric a s F w)
    (R w : Name s) (relation : HereditarilySymmetric a s F R)
    (representative : HereditarilySymmetric a s F w) :
    HereditarilySymmetric a s F (refinementClass T valid R w) :=
  refinementClass_hs a F T valid closed children R w
    (a.stabilizer s R ⊓ a.stabilizer s w) (F.inf relation.symmetric representative.symmetric)
    (fun _ hg => hg.1) (fun _ hg => hg.2)

end PartitionPilot.Forcing.Name



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundAssignmentClassGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem assignmentClassGraph_mem (side : Fin 2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A field T P order top : ZFSet.{u}}
    (hA : A ∈ M.sets) (hField : field ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (hOrder : order ∈ M.sets) (hTop : top ∈ M.sets) :
    M.assignmentClassGraph side A field T P order top ∈ M.sets :=
  M.separation_mem separation (assignmentClassGraphFormula side) _
    (Fin.cases hA (Fin.cases hField (Fin.cases hT (Fin.cases hP
      (Fin.cases hOrder (Fin.cases hTop (fun j => Fin.elim0 j)))))))
    (M.prod_mem pairing unions powers separation hA
      (M.groundRelations_mem pairing unions powers separation hT hP))

private theorem realize_assignmentClassGraphFormula (side : Fin 2)
    (env : Fin 7 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (assignmentClassGraphFormula side) env ↔
      ∃ w : Fin 6 → ZFSet.{u}, (∀ j, w j ∈ M.sets) ∧
        w 0 ∈ env 1 ∧ env 0 = ZFSet.pair (w 0) (w 1) ∧
        w 0 = stageOneAssignment (w 2) (w 3) (w 4) ∧
        ZFSet.pair (w 2) (w 5) ∈ env 2 ∧
        Realize M.sets refinementClassCodeFormula
          ![w 1, env 3, w 5, Fin.cases (w 3) (fun _ => w 4) side,
            env 4, env 5, env 6] := by
  rw [assignmentClassGraphFormula, realize_exBlock]
  apply exists_congr
  intro w
  apply and_congr_right
  intro ground
  have args : (fun j : Fin 7 => extendMany 6 w env
      (![prefixIndex 7 6 1, suffixIndex 7 6 3, prefixIndex 7 6 5,
        Fin.cases (prefixIndex 7 6 3) (fun _ => prefixIndex 7 6 4) side,
        suffixIndex 7 6 4, suffixIndex 7 6 5, suffixIndex 7 6 6] j)) =
      ![w 1, env 3, w 5, Fin.cases (w 3) (fun _ => w 4) side, env 4, env 5, env 6] := by
    funext j
    refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases ?_
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))))) j
    exact Fin.cases rfl (fun _ => rfl) side
  simp only [Realize, BoundedFormula.realize_toFormula M _ _
    (extendMany_members 6 w env ground members), BoundedFormula.truth_orderedPairFormula,
    BoundedFormula.truth_stageOneAssignmentFormula, BoundedFormula.truth_pairMembershipFormula,
    extendMany_prefix, extendMany_suffix, realize_reindex, args]

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem assignmentClassGraph_entry (side : Fin 2)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {A field T : ZFSet.{u}} (hA : A ∈ M.sets) (hField : field ∈ M.sets) (hT : T ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (R u w : Name s)
    (hR : R.val ∈ M.sets) (hu : u.val ∈ M.sets) (hw : w.val ∈ M.sets)
    {i : ZFSet.{u}} (member : stageOneAssignment i u.val w.val ∈ A)
    (lookup : ∀ z, ZFSet.pair i z ∈ field ↔ z = R.val) (y : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u.val w.val) y ∈
      M.assignmentClassGraph side A field T s.carrier s.conditionOrder (s.encode ⊤) ↔
      y = (Name.refinementClass T valid R (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)).val := by
  have hTop := M.transitive carrier (s.encode_mem ⊤)
  have hAssignment := M.transitive hA member
  have hi := M.pair_left hAssignment
  have hBound := M.groundRelations_mem pairing unions powers separation hT carrier
  have hRepresentative : (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side).val ∈ M.sets :=
    Fin.cases hu (fun _ => hw) side
  have representative : (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side).val =
      Fin.cases (motive := fun _ => ZFSet.{u}) u.val (fun _ => w.val) side := Fin.cases rfl (fun _ => rfl) side
  let params : Fin 6 → ZFSet.{u} := ![A, field, T, s.carrier, s.conditionOrder, s.encode ⊤]
  have hp : ∀ j, params j ∈ M.sets := Fin.cases hA (Fin.cases hField (Fin.cases hT
    (Fin.cases carrier (Fin.cases order (Fin.cases hTop (fun j => Fin.elim0 j))))))
  rw [assignmentClassGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨_, hyB⟩, recognized⟩
    have hy := M.transitive hBound hyB
    obtain ⟨v, ground, _, equal, triple, relation, output⟩ :=
      (M.realize_assignmentClassGraphFormula side (extend _ params)
        (Fin.cases (M.orderedPair_mem pairing hAssignment hy) hp)).1 recognized
    obtain ⟨key, value⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨idx, first, second⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 (key.trans triple)
    have rel : v 5 = R.val := (lookup _).1 (idx.symm ▸ relation)
    dsimp only [params, extend, Matrix.cons_val_zero, Matrix.cons_val_succ] at output
    rw [← value, rel, ← first, ← second, ← representative] at output
    exact (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid R _ hR hRepresentative y hy).1 output
  · intro equal
    subst y
    have named := M.refinementClass_mem s pairing unions powers separation collection carrier order
      hT valid R _ hR hRepresentative
    have bound := (M.mem_groundRelations T s.carrier _).2
      ⟨named, Name.refinementClass_subset T valid R _⟩
    refine ⟨⟨member, bound⟩, ?_⟩
    apply (M.realize_assignmentClassGraphFormula side (extend _ params)
      (Fin.cases (M.orderedPair_mem pairing hAssignment named) hp)).2
    refine ⟨![stageOneAssignment i u.val w.val,
      (Name.refinementClass T valid R (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)).val, i, u.val, w.val, R.val],
      Fin.cases hAssignment (Fin.cases named (Fin.cases hi (Fin.cases hu
        (Fin.cases hw (Fin.cases hR (fun j => Fin.elim0 j)))))), member, rfl, rfl,
      (lookup _).2 rfl, ?_⟩
    have realizing := (M.realize_refinementClassCodeFormula s pairing unions powers separation collection
      carrier order hT valid R _ hR hRepresentative _ named).2 rfl
    rw [representative] at realizing
    exact realizing

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionClosure
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundCountable_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets) (nonempty : R.Nonempty)
    (small : M.groundEmbeddable R ZFSet.omega) :
    ∃ g ∈ M.sets, ZFSet.IsFunc ZFSet.omega R g ∧
      ∀ p ∈ R, ∃ n ∈ ZFSet.omega, ZFSet.pair n p ∈ g :=
  M.groundEmbeddable_enumeration pairing unions powers separation hR
    (M.omega_mem separation infinite) nonempty small

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization
universe u

theorem groundSequenceUnion_extends {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) (n : Nat) :
    SetMembers.raw (seq n) ⊆ groundSequenceUnion seq :=
  fun _ hz => (mem_groundSequenceUnion seq _).2 ⟨n, hz⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem descending_function_union_partial (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      Antitone seq → PartialFunctionCode X Y (groundSequenceUnion seq) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq decreasing
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq z).1 hz
    exact (M.smallFunction_raw_properties X Y ZFSet.omega (seq n)).2.1.shape hn
  · intro x y z xy xz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq _).1 xy
    obtain ⟨m, hm⟩ := (mem_groundSequenceUnion seq _).1 xz
    have code := (M.smallFunction_raw_properties X Y ZFSet.omega (seq (max n m))).2.1
    exact code.unique x y z
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_left n m)) hn)
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_right n m)) hm)

theorem descending_function_union_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        groundSequenceUnion seq ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  obtain ⟨ground, small⟩ := M.countable_union_of_sequence_graph pairing unions powers separation infinite choice
    hQ (M.prod_mem pairing unions powers separation hX hY) graph
    (natPresentation.graph_isFunc (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega))
      (fun n => seq n.down))
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.1.shape)
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.2)
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨ground, M.descending_function_union_partial X Y seq decreasing, small⟩

theorem countable_function_lower_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        ∃ p, SetMembers.raw p = groundSequenceUnion seq ∧ ∀ n, p ≤ seq n := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have member := M.descending_function_union_mem pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  let p := SetMembers.ofMem (groundSequenceUnion seq) member
  have raw : SetMembers.raw p = groundSequenceUnion seq := SetMembers.raw_ofMem _ _
  refine ⟨p, raw, fun n => (M.smallFunction_le_iff X Y ZFSet.omega p (seq n)).2 ?_⟩
  rw [raw]
  exact groundSequenceUnion_extends seq n

theorem countable_function_internally_closed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    InternallyCountablyClosed M (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  obtain ⟨p, _, lower⟩ := M.countable_function_lower_bound pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  exact ⟨p, lower⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAttachmentEmbeddings
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing




universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem attachmentIdeal_mem (separation : SeparationSchema M.sets)
    {Q rQ a : ZFSet.{u}} (hQ : Q ∈ M.sets) (hrQ : rQ ∈ M.sets)
    (ha : a ∈ M.sets) : attachmentIdeal Q rQ a ∈ M.sets := by
  let params := extend a (extend rQ Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairMembershipFormula 0 1 2) params
    (Fin.cases ha (Fin.cases hrQ (fun i => Fin.elim0 i))) hQ
  have equal : ZFSet.sep (fun q => BoundedFormula.Truth
      (BoundedFormula.pairMembershipFormula 0 1 2) (extend q params)) Q =
      attachmentIdeal Q rQ a := by
    apply ZFSet.ext
    intro q
    rw [ZFSet.mem_sep, mem_attachmentIdeal, BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround






end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSerialOrbits
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundSerialOrbit
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {W R initial : ZFSet.{u}} (hW : W ∈ M.sets) (hR : R ∈ M.sets)
    (hInitial : initial ∈ W)
    (serial : ∀ x ∈ W, ∃ y ∈ W, ZFSet.pair x y ∈ R) :
    ∃ history ∈ M.sets, ZFSet.IsFunc ZFSet.omega W history ∧
      (∀ y, ZFSet.pair ∅ y ∈ history ↔ y = initial) ∧
      ∀ n ∈ ZFSet.omega, ∀ x y,
        ZFSet.pair n x ∈ history → ZFSet.pair (insert n n) y ∈ history → ZFSet.pair x y ∈ R := by
  obtain ⟨step, hStep, function, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hW hW hR serial
  let s := SetMembers.presentation W
  let f := s.decodeFunction s step function
  let b := SetMembers.ofMem initial hInitial
  have graphGround : s.graph s f ∈ M.sets :=
    M.decoded_function_graph_mem s s hStep function
  let history := natPresentation.graph s (fun n => natIterate f b n.down)
  have historyGround : history ∈ M.sets :=
    M.natural_recursion_graph_mem pairing unions powers separation infinite s f b hW graphGround
  have historyFunction : ZFSet.IsFunc ZFSet.omega W history := natPresentation.graph_isFunc s _
  have canonical (n : Nat) :
      ZFSet.pair (natSetCode n) (s.encode (natIterate f b n)) ∈ history :=
    (natPresentation.pair_mem_graph s (fun n => natIterate f b n.down) ⟨n⟩ _).2 rfl
  have entryValue (n : Nat) (y : ZFSet.{u})
      (entry : ZFSet.pair (natSetCode n) y ∈ history) : y = s.encode (natIterate f b n) := by
    obtain ⟨_, _, unique⟩ := historyFunction.2 (natSetCode n) (natSetCode_mem_omega n)
    exact (unique y entry).trans (unique _ (canonical n)).symm
  refine ⟨history, historyGround, historyFunction, ?_, ?_⟩
  · intro y
    constructor
    · intro entry
      exact (entryValue 0 y entry).trans (SetMembers.raw_ofMem initial hInitial)
    · intro equal
      exact equal.symm ▸ (SetMembers.raw_ofMem initial hInitial ▸ canonical 0)
  · intro n hn x y first second
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have firstValue := entryValue k x first
    have secondValue := entryValue (k + 1) y second
    rw [firstValue, secondValue]
    exact selected (s.decodeFunction_mem s step function (natIterate f b k))

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNameSequenceValues
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem pair_mem_decisionStepGraph (P r U D n p m q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair n p) (ZFSet.pair m q) ∈ decisionStepGraph P r U D ↔
      n ∈ ZFSet.omega ∧ p ∈ P ∧ m ∈ ZFSet.omega ∧ q ∈ P ∧
        m = insert n n ∧ ZFSet.pair q p ∈ r ∧
          ∃ a ∈ U, ZFSet.pair (ZFSet.pair q n) a ∈ D := by
  rw [decisionStepGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, n', hn, p', hp, m', hm, q', hq, a, ha, equal, clock, stronger, decision⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
    exact ⟨hn, hp, hm, hq, clock, stronger, a, ha, decision⟩
  · rintro ⟨hn, hp, hm, hq, clock, stronger, a, ha, decision⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hn, hp⟩,
      ZFSet.pair_mem_prod.2 ⟨hm, hq⟩⟩, n, hn, p, hp, m, hm, q, hq,
      a, ha, rfl, clock, stronger, decision⟩

namespace BoundedFormula
open SetFormula

theorem truth_decisionStepEntryFormula (env : Fin 6 → ZFSet.{u}) :
    Truth decisionStepEntryFormula env ↔
      ∃ n ∈ env 1, ∃ p ∈ env 2, ∃ m ∈ env 1, ∃ q ∈ env 2, ∃ a ∈ env 4,
        env 0 = ZFSet.pair (ZFSet.pair n p) (ZFSet.pair m q) ∧
        m = insert n n ∧ ZFSet.pair q p ∈ env 3 ∧
          ZFSet.pair (ZFSet.pair q n) a ∈ env 5 := by
  simp only [decisionStepEntryFormula, truth_exMem, Truth, truth_pairOfPairsFormula,
    truth_successorFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem decisionStepGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {P r U D : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hU : U ∈ M.sets) (hD : D ∈ M.sets) : decisionStepGraph P r U D ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hW := M.prod_mem pairing unions powers separation hw hP
  let params := extend ZFSet.omega (extend P (extend r (extend U (extend D Fin.elim0))))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hw (Fin.cases hP (Fin.cases hr (Fin.cases hU (Fin.cases hD (fun j => Fin.elim0 j)))))
  have selected := M.bounded_separation_mem separation BoundedFormula.decisionStepEntryFormula
    params members (M.prod_mem pairing unions powers separation hW hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.decisionStepEntryFormula
      (extend z params)) (ZFSet.prod (ZFSet.prod ZFSet.omega P) (ZFSet.prod ZFSet.omega P)) =
        decisionStepGraph P r U D := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, decisionStepGraph, ZFSet.mem_sep,
      BoundedFormula.truth_decisionStepEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem exists_groundDecisionChain
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (order : s.conditionOrder ∈ M.sets) {S U D : ZFSet.{u}}
    (hS : S ∈ M.sets) (hU : U ∈ M.sets) (hD : D ∈ M.sets) (subset : S ⊆ s.carrier)
    (p : P) (hp : s.encode p ∈ S)
    (dense : ∀ n : Nat, ∀ p : P, s.encode p ∈ S →
      ∃ q, q ≤ p ∧ s.encode q ∈ S ∧
        ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) (natSetCode n)) a ∈ D) :
    ∃ seq : Nat → P, seq 0 = p ∧
      natPresentation.graph s (fun n => seq n.down) ∈ M.sets ∧ Antitone seq ∧
      (∀ n, s.encode (seq n) ∈ S) ∧
      ∀ n, ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode (seq (n + 1))) (natSetCode n)) a ∈ D := by
  have hw := M.omega_mem separation infinite
  let W := ZFSet.prod ZFSet.omega S
  let R := decisionStepGraph S s.conditionOrder U D
  have hW : W ∈ M.sets := M.prod_mem pairing unions powers separation hw hS
  have hR : R ∈ M.sets := M.decisionStepGraph_mem pairing unions powers separation infinite hS order hU hD
  have serial : ∀ x ∈ W, ∃ y ∈ W, ZFSet.pair x y ∈ R := by
    intro x hx
    obtain ⟨n, hn, raw, hraw, rfl⟩ := ZFSet.mem_prod.1 hx
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨q, rfl⟩ := (s.mem_carrier raw).1 (subset hraw)
    obtain ⟨r, stronger, hr, a, ha, decision⟩ := dense k q hraw
    exact ⟨ZFSet.pair (natSetCode (k + 1)) (s.encode r),
      ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _, hr⟩,
      (pair_mem_decisionStepGraph _ _ _ _ _ _ _ _).2
        ⟨natSetCode_mem_omega _, hraw, natSetCode_mem_omega _, hr, rfl,
          (s.pair_mem_conditionOrder r q).2 stronger, a, ha, decision⟩⟩
  obtain ⟨history, hHistory, function, zero, next⟩ :=
    M.exists_groundSerialOrbit pairing unions powers separation infinite choice hW hR
      (ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega 0, hp⟩) serial
  let t := natPresentation.product (SetMembers.presentation S)
  let state : Nat → ULift.{u} Nat × SetMembers S :=
    fun n => natPresentation.decodeFunction t history function ⟨n⟩
  have entry (n : Nat) : ZFSet.pair (natSetCode n)
      (ZFSet.pair (natSetCode (state n).1.down) (SetMembers.raw (state n).2)) ∈ history :=
    natPresentation.decodeFunction_mem t history function ⟨n⟩
  have initial : natSetCode (state 0).1.down = natSetCode 0 ∧
      SetMembers.raw (state 0).2 = s.encode p :=
    ZFSet.pair_inj.1 ((zero _).1 (entry 0))
  have steps (n : Nat) := (pair_mem_decisionStepGraph S s.conditionOrder U D
    (natSetCode (state n).1.down) (SetMembers.raw (state n).2)
    (natSetCode (state (n + 1)).1.down) (SetMembers.raw (state (n + 1)).2)).1
      (next (natSetCode n) (natSetCode_mem_omega n) _ _ (entry n) (entry (n + 1)))
  have clock (n : Nat) : (state n).1.down = n := by
    induction n with
    | zero => exact natSetCode_injective initial.1
    | succ n ih =>
      have h : natSetCode (state (n + 1)).1.down = natSetCode ((state n).1.down + 1) :=
        (steps n).2.2.2.2.1
      exact (natSetCode_injective h).trans (congrArg (fun k => k + 1) ih)
  let graph := relationCompose ZFSet.omega W S history (productSecond ZFSet.omega S)
  have graphGround : graph ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hw hW hS hHistory (M.productSecond_mem pairing unions powers separation hw hS)
  have smallFunction : ZFSet.IsFunc ZFSet.omega S graph :=
    relationCompose_function_of_subset function (productSecond_function ZFSet.omega S) (fun _ h => h)
  have graphFunction : ZFSet.IsFunc ZFSet.omega s.carrier graph := by
    refine ⟨?_, smallFunction.2⟩
    intro z hz
    obtain ⟨n, hn, q, hq, rfl⟩ := ZFSet.mem_prod.1 (smallFunction.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hn, subset hq⟩
  let seq : Nat → P := fun n => natPresentation.decodeFunction s graph graphFunction ⟨n⟩
  have projected (n : Nat) : ZFSet.pair (natSetCode n) (SetMembers.raw (state n).2) ∈ graph :=
    (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨natSetCode_mem_omega n, SetMembers.raw_mem _, _,
        ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _, SetMembers.raw_mem _⟩, entry n,
        (mem_productSecond _ _ _).2 ⟨_, natSetCode_mem_omega _, _, SetMembers.raw_mem _, rfl⟩⟩
  have value (n : Nat) : s.encode (seq n) = SetMembers.raw (state n).2 := by
    obtain ⟨_, _, unique⟩ := graphFunction.2 (natSetCode n) (natSetCode_mem_omega n)
    exact (unique _ (natPresentation.decodeFunction_mem s graph graphFunction ⟨n⟩)).trans
      (unique _ (projected n)).symm
  refine ⟨seq, s.injective ((value 0).trans initial.2),
    M.decoded_function_graph_mem natPresentation s graphGround graphFunction, ?_, ?_, ?_⟩
  · apply antitone_nat_of_succ_le
    intro n
    apply (s.pair_mem_conditionOrder _ _).1
    rw [value, value]
    exact (steps n).2.2.2.2.2.1
  · intro n
    rw [value]
    exact SetMembers.raw_mem _
  · intro n
    obtain ⟨a, ha, decision⟩ := (steps n).2.2.2.2.2.2
    refine ⟨a, ha, ?_⟩
    rw [value]
    rw [clock] at decision
    exact decision

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem internally_commonDecisions_denseBelow
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {U D : ZFSet.{u}} (hU : U ∈ M.sets) (hD : D ∈ M.sets)
    (closed : InternallyCountablyClosed M s) (base : P)
    (persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (dense : ∀ n ∈ ZFSet.omega, DenseBelow base
      {q | ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D}) :
    DenseBelow base {q | q ≤ base ∧ ∀ n ∈ ZFSet.omega,
      ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D} := by
  intro p below
  let S := attachmentIdeal s.carrier s.conditionOrder (s.encode base)
  have hS : S ∈ M.sets := M.attachmentIdeal_mem separation carrier order
    (M.transitive carrier (s.encode_mem base))
  have subset : S ⊆ s.carrier := fun _ h => (ZFSet.mem_sep.1 h).1
  have cone (q : P) : s.encode q ∈ S ↔ q ≤ base := by
    rw [mem_attachmentIdeal, s.pair_mem_conditionOrder]
    exact ⟨And.right, fun h => ⟨s.encode_mem q, h⟩⟩
  obtain ⟨seq, initial, graph, decreasing, _, decisions⟩ :=
    M.exists_groundDecisionChain s pairing unions powers separation infinite choice order
      hS hU hD subset p ((cone p).2 below) (fun n q hq => by
        obtain ⟨r, stronger, a, ha, decided⟩ := dense (natSetCode n) (natSetCode_mem_omega n)
          q ((cone q).1 hq)
        exact ⟨r, stronger, (cone r).2 (stronger.trans ((cone q).1 hq)), a, ha, decided⟩)
  obtain ⟨q, lower⟩ := closed seq graph decreasing
  have stronger : q ≤ p := initial ▸ lower 0
  refine ⟨q, stronger, stronger.trans below, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨a, ha, decided⟩ := decisions k
  exact ⟨a, ha, persistent _ q (lower (k + 1)) _ (natSetCode_mem_omega k) a ha decided⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

private theorem enumeratedFamilyDecisions_entry (Q J B g f p n j : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p n) j ∈ enumeratedFamilyDecisions Q J B g f ↔
      p ∈ Q ∧ n ∈ ZFSet.omega ∧ j ∈ J ∧ ZFSet.pair n j ∈ g ∧
        ∃ E ∈ B, ZFSet.pair j E ∈ f ∧ p ∈ E := by
  rw [enumeratedFamilyDecisions, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, p', hp, n', hn, j', hj, E, hE, eq, ng, ef, member⟩
    obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    exact ⟨hp, hn, hj, ng, E, hE, ef, member⟩
  · rintro ⟨hp, hn, hj, ng, E, hE, ef, member⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hp, hn⟩, hj⟩,
      p, hp, n, hn, j, hj, E, hE, rfl, ng, ef, member⟩

private theorem enumeratedFamilyDecisionFormula_truth (env : Fin 7 → ZFSet.{u}) :
    BoundedFormula.Truth enumeratedFamilyDecisionFormula env ↔
      ∃ p ∈ env 1, ∃ n ∈ env 2, ∃ j ∈ env 3, ∃ E ∈ env 4,
        env 0 = ZFSet.pair (ZFSet.pair p n) j ∧ ZFSet.pair n j ∈ env 5 ∧
          ZFSet.pair j E ∈ env 6 ∧ p ∈ E := by
  simp only [enumeratedFamilyDecisionFormula, BoundedFormula.truth_exMem,
    BoundedFormula.Truth, BoundedFormula.truth_orderedTripleFormula,
    BoundedFormula.truth_pairMembershipFormula]
  rfl

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem internally_countableDenseFamily_denseBelow
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {J f : ZFSet.{u}} (hJ : J ∈ M.sets) (hf : f ∈ M.sets)
    (small : M.groundEmbeddable J ZFSet.omega)
    (function : ZFSet.IsFunc J (M.groundPower s.carrier) f)
    (closed : InternallyCountablyClosed M s) (base : P)
    (persistent : ∀ j E, ZFSet.pair j E ∈ f → ∀ p q : P,
      q ≤ p → s.encode p ∈ E → s.encode q ∈ E)
    (dense : ∀ j E, ZFSet.pair j E ∈ f → DenseBelow base {q | s.encode q ∈ E}) :
    DenseBelow base {q | q ≤ base ∧ ∀ j E, ZFSet.pair j E ∈ f → s.encode q ∈ E} := by
  classical
  by_cases nonempty : J.Nonempty
  · obtain ⟨g, hg, enumeration, onto⟩ := M.groundCountable_enumeration
      pairing unions powers separation infinite hJ nonempty small
    let B := M.groundPower s.carrier
    let D := enumeratedFamilyDecisions s.carrier J B g f
    have hN := M.omega_mem separation infinite
    have hB : B ∈ M.sets := M.groundPower_mem powers carrier
    let params := ![s.carrier, ZFSet.omega, J, B, g, f]
    have members : ∀ i, params i ∈ M.sets := Fin.cases carrier (Fin.cases hN
      (Fin.cases hJ (Fin.cases hB (Fin.cases hg (Fin.cases hf (fun i => Fin.elim0 i))))))
    have selected := M.bounded_separation_mem separation enumeratedFamilyDecisionFormula
      params members (M.prod_mem pairing unions powers separation
        (M.prod_mem pairing unions powers separation carrier hN) hJ)
    have hD : D ∈ M.sets := by
      have equal : ZFSet.sep (fun z => BoundedFormula.Truth enumeratedFamilyDecisionFormula
          (extend z params)) (ZFSet.prod (ZFSet.prod s.carrier ZFSet.omega) J) = D := by
        apply ZFSet.ext
        intro z
        change _ ↔ z ∈ enumeratedFamilyDecisions s.carrier J B g f
        rw [ZFSet.mem_sep, enumeratedFamilyDecisions, ZFSet.mem_sep,
          enumeratedFamilyDecisionFormula_truth]
        rfl
      exact equal ▸ selected
    have persistD : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ j ∈ J,
        ZFSet.pair (ZFSet.pair (s.encode p) n) j ∈ D →
          ZFSet.pair (ZFSet.pair (s.encode q) n) j ∈ D := by
      intro p q qp n hn j hj entry
      obtain ⟨_, _, _, ng, E, hE, ef, member⟩ :=
        (enumeratedFamilyDecisions_entry s.carrier J B g f (s.encode p) n j).1 entry
      exact (enumeratedFamilyDecisions_entry s.carrier J B g f (s.encode q) n j).2
        ⟨s.encode_mem q, hn, hj, ng, E, hE, ef, persistent j E ef p q qp member⟩
    have denseD : ∀ n ∈ ZFSet.omega, DenseBelow base
        {q | ∃ j ∈ J, ZFSet.pair (ZFSet.pair (s.encode q) n) j ∈ D} := by
      intro n hn p pb
      obtain ⟨j, ng, _⟩ := enumeration.2 n hn
      have hj := (ZFSet.pair_mem_prod.1 (enumeration.1 ng)).2
      obtain ⟨E, ef, _⟩ := function.2 j hj
      have hE := (ZFSet.pair_mem_prod.1 (function.1 ef)).2
      obtain ⟨q, qp, member⟩ := dense j E ef p pb
      exact ⟨q, qp, j, hj,
        (enumeratedFamilyDecisions_entry s.carrier J B g f (s.encode q) n j).2
          ⟨s.encode_mem q, hn, hj, ng, E, hE, ef, member⟩⟩
    have common := M.internally_commonDecisions_denseBelow s pairing unions powers separation
      infinite choice carrier order hJ hD closed base persistD denseD
    intro p pb
    obtain ⟨q, qp, qb, decisions⟩ := common p pb
    refine ⟨q, qp, qb, ?_⟩
    intro j E ef
    have hj := (ZFSet.pair_mem_prod.1 (function.1 ef)).1
    obtain ⟨n, hn, ng⟩ := onto j hj
    obtain ⟨j', _, entry⟩ := decisions n hn
    obtain ⟨_, _, _, ng', E', _, ef', member⟩ :=
      (enumeratedFamilyDecisions_entry s.carrier J B g f (s.encode q) n j').1 entry
    obtain ⟨_, _, uniqueJ⟩ := enumeration.2 n hn
    have sameJ : j' = j := (uniqueJ _ ng').trans (uniqueJ _ ng).symm
    subst j'
    obtain ⟨_, _, uniqueE⟩ := function.2 j hj
    have sameE : E' = E := (uniqueE _ ef').trans (uniqueE _ ef).symm
    exact sameE ▸ member
  · intro p pb
    refine ⟨p, le_rfl, pb, ?_⟩
    intro j E ef
    exact False.elim (nonempty ⟨j, (ZFSet.pair_mem_prod.1 (function.1 ef)).1⟩)

end TransitiveGround
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowAssignmentCuts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_rowAssignmentCutFormula {n : Nat} (z levels alpha : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (rowAssignmentCutFormula z levels alpha) env ↔
      ∃ row A, env z = ZFSet.pair (ZFSet.pair row A)
        (ZFSet.pair row (assignmentCut (env levels) (env alpha) A)) := by
  rw [rowAssignmentCutFormula, realize_exBlock]
  have actual (f : Fin 5 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (SetFormula.rowAssignmentCutBody z levels alpha).toFormula
        (extendMany 5 f env) ↔
      env z = ZFSet.pair (f 3) (f 4) ∧ f 3 = ZFSet.pair (f 0) (f 1) ∧
        f 4 = ZFSet.pair (f 0) (f 2) ∧
          f 2 = assignmentCut (env levels) (env alpha) (f 1) := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 5 f env ground members)]
    simp only [SetFormula.rowAssignmentCutBody, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_assignmentCutFormula,
      extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨equal, upper, lower, cut⟩ := (actual f ground).1 body
    rw [upper, lower, cut] at equal
    exact ⟨f 0, f 1, equal⟩
  · rintro ⟨row, A, equal⟩
    have pairGround := equal ▸ members z
    have upper := M.pair_left pairGround
    have lower := M.pair_right pairGround
    let cut := assignmentCut (env levels) (env alpha) A
    let f : Fin 5 → ZFSet.{u} := ![row, A, cut, ZFSet.pair row A, ZFSet.pair row cut]
    have ground : ∀ j, f j ∈ M.sets :=
      Fin.cases (M.pair_left upper) (Fin.cases (M.pair_right upper)
        (Fin.cases (M.pair_right lower) (Fin.cases upper
          (Fin.cases lower (fun j => Fin.elim0 j)))))
    exact ⟨f, ground, (actual f ground).2 ⟨equal, rfl, rfl, rfl⟩⟩

theorem rowAssignmentCutGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {upper lower levels alpha : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLower : lower ∈ M.sets)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) :
    rowAssignmentCutGraph upper lower levels alpha ∈ M.sets := by
  let params : Fin 2 → ZFSet.{u} := ![levels, alpha]
  have ground : ∀ j, params j ∈ M.sets :=
    Fin.cases hLevels (Fin.cases hAlpha (fun j => Fin.elim0 j))
  have bound := M.prod_mem pairing unions powers separation hUpper hLower
  have selected := M.separation_mem separation (rowAssignmentCutFormula 0 1 2) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (rowAssignmentCutFormula 0 1 2) (extend z params))
      (ZFSet.prod upper lower) = rowAssignmentCutGraph upper lower levels alpha := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_rowAssignmentCutGraph]
    apply and_congr_right
    intro hz
    exact M.realize_rowAssignmentCutFormula 0 1 2 (extend z params)
      (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRepresentedDomainConditions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

private theorem realize_representedReuseFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (A q P order T idx cu classes : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (representedReuseFormula A q P order T idx cu classes) env ↔
      ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
        stageOneAssignment (env idx) v w ∈ env A ∧
        ZFSet.pair v z ∈ env classes ∧
        stageOneRawForces M (env P) (env order) (env q)
          (.equal 0 1 : SetFormula 2) ![env cu, z] := by
  rw [representedReuseFormula, realize_exBlock]
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (.mem (prefixIndex n 3 0) (suffixIndex n 3 T))
        (.conj (.mem (prefixIndex n 3 1) (suffixIndex n 3 T))
          (.conj (tripleMembershipFormula (suffixIndex n 3 idx) (prefixIndex n 3 0)
            (prefixIndex n 3 1) (suffixIndex n 3 A))
            (.conj (pairMembershipFormula (prefixIndex n 3 0) (prefixIndex n 3 2)
              (suffixIndex n 3 classes))
              (stageOneForcingAt (.equal 0 1 : SetFormula 2) (suffixIndex n 3 q)
                (suffixIndex n 3 P) (suffixIndex n 3 order)
                ![suffixIndex n 3 cu, prefixIndex n 3 2]))))) (extendMany 3 f env) ↔
      f 0 ∈ env T ∧ f 1 ∈ env T ∧
      stageOneAssignment (env idx) (f 0) (f 1) ∈ env A ∧
      ZFSet.pair (f 0) (f 2) ∈ env classes ∧
      stageOneRawForces M (env P) (env order) (env q)
        (.equal 0 1 : SetFormula 2) ![env cu, f 2] := by
    have allGround := extendMany_members 3 f env ground members
    simp only [Realize]
    rw [M.realize_tripleMembershipFormula pairing _ _ _ _ _
      (allGround _) (allGround _) (allGround _) (allGround _),
      M.realize_pairMembershipFormula pairing _ _ _ _ (allGround _) (allGround _) (allGround _),
      M.realize_stageOneForcingAt]
    have values (x y : Fin (n + 3)) :
        (fun j : Fin 2 => extendMany 3 f env (![x, y] j)) =
          ![extendMany 3 f env x, extendMany 3 f env y] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [values]
    simp only [extendMany_prefix, extendMany_suffix, stageOneAssignment]
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨hv, hw, literal, entry, forced⟩ := (actual f ground).1 body
    exact ⟨f 0, hv, f 1, hw, f 2, literal, entry, forced⟩
  · rintro ⟨v, hv, w, hw, z, literal, entry, forced⟩
    have ground : ∀ j, (![v, w, z] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members T) hv) (Fin.cases (M.transitive (members T) hw)
        (Fin.cases (M.pair_right (M.transitive (members classes) entry)) (fun j => Fin.elim0 j)))
    exact ⟨![v, w, z], ground, (actual ![v, w, z] ground).2 ⟨hv, hw, literal, entry, forced⟩⟩

private theorem realize_representedEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (p P order cut T idx u U cu classes : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (representedEntryFormula p P order cut T idx u U cu classes) env ↔
      ∃ row A q, env p = ZFSet.pair row A ∧ ZFSet.pair (env p) q ∈ env cut ∧
        (stageOneRawForces M (env P) (env order) q
          (.neg (.mem 0 1) : SetFormula 2) ![env u, env U] ∨
        (stageOneRawForces M (env P) (env order) q (.mem 0 1 : SetFormula 2) ![env u, env U] ∧
          ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
            stageOneAssignment (env idx) v w ∈ A ∧ ZFSet.pair v z ∈ env classes ∧
            stageOneRawForces M (env P) (env order) q
              (.equal 0 1 : SetFormula 2) ![env cu, z])) := by
  rw [representedEntryFormula, realize_exBlock]
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      Realize M.sets (.conj (BoundedFormula.orderedPairFormula (suffixIndex n 3 p)
        (prefixIndex n 3 0) (prefixIndex n 3 1)).toFormula
        (.conj (pairMembershipFormula (suffixIndex n 3 p) (prefixIndex n 3 2) (suffixIndex n 3 cut))
          (disj (stageOneForcingAt (.neg (.mem 0 1) : SetFormula 2) (prefixIndex n 3 2)
            (suffixIndex n 3 P) (suffixIndex n 3 order) ![suffixIndex n 3 u, suffixIndex n 3 U])
            (.conj (stageOneForcingAt (.mem 0 1 : SetFormula 2) (prefixIndex n 3 2)
              (suffixIndex n 3 P) (suffixIndex n 3 order) ![suffixIndex n 3 u, suffixIndex n 3 U])
              (representedReuseFormula (prefixIndex n 3 1) (prefixIndex n 3 2)
                (suffixIndex n 3 P) (suffixIndex n 3 order) (suffixIndex n 3 T)
                (suffixIndex n 3 idx) (suffixIndex n 3 cu) (suffixIndex n 3 classes))))))
        (extendMany 3 f env) ↔
      env p = ZFSet.pair (f 0) (f 1) ∧ ZFSet.pair (env p) (f 2) ∈ env cut ∧
        (stageOneRawForces M (env P) (env order) (f 2)
          (.neg (.mem 0 1) : SetFormula 2) ![env u, env U] ∨
        (stageOneRawForces M (env P) (env order) (f 2) (.mem 0 1 : SetFormula 2) ![env u, env U] ∧
          ∃ v ∈ env T, ∃ w ∈ env T, ∃ z,
            stageOneAssignment (env idx) v w ∈ f 1 ∧ ZFSet.pair v z ∈ env classes ∧
            stageOneRawForces M (env P) (env order) (f 2)
              (.equal 0 1 : SetFormula 2) ![env cu, z])) := by
    have allGround := extendMany_members 3 f env ground members
    rw [Realize, BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.truth_orderedPairFormula, Realize,
      M.realize_pairMembershipFormula pairing _ _ _ _ (allGround _) (allGround _) (allGround _),
      realize_disj, M.realize_stageOneForcingAt, Realize, M.realize_stageOneForcingAt,
      realize_representedReuseFormula M pairing _ _ _ _ _ _ _ _ _ allGround]
    have values (x y : Fin (n + 3)) :
        (fun j : Fin 2 => extendMany 3 f env (![x, y] j)) =
          ![extendMany 3 f env x, extendMany 3 f env y] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    rw [values]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, body⟩
    exact ⟨f 0, f 1, f 2, (actual f ground).1 body⟩
  · rintro ⟨row, A, q, shape, cutEntry, code⟩
    have ground : ∀ j, (![row, A, q] : Fin 3 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.pair_left (shape ▸ members p)) (Fin.cases (M.pair_right (shape ▸ members p))
        (Fin.cases (M.pair_right (M.transitive (members cut) cutEntry)) (fun j => Fin.elim0 j)))
    exact ⟨![row, A, q], ground, (actual ![row, A, q] ground).2 ⟨shape, cutEntry, code⟩⟩

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
private theorem representedParams_ground {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) :
    ∀ j, (![s.carrier, s.conditionOrder, rowAssignmentCutGraph upper s.carrier levels alpha,
      T, idx, u.val.val, U.val.val, (Name.refinementClass T valid Rc.val u.val).val,
      Name.refinementClassGraph T valid Rc.val T valid] : Fin 9 → ZFSet.{u}) j ∈ M.sets :=
  Fin.cases carrier (Fin.cases order
    (Fin.cases (M.rowAssignmentCutGraph_mem pairing unions powers separation hUpper carrier hLevels hAlpha)
      (Fin.cases hT (Fin.cases hIdx (Fin.cases u.property (Fin.cases U.property
        (Fin.cases (M.refinementClass_mem s pairing unions powers separation collection carrier order
          hT valid Rc.val u.val Rc.property u.property)
          (Fin.cases (M.refinementClassGraph_mem s pairing unions powers separation collection carrier order
            hT hT valid valid Rc.val Rc.property) (fun j => Fin.elim0 j)))))))))

include pairing unions powers separation collection carrier order in
theorem pair_mem_representedDomainConditions {upper levels alpha T : ZFSet.{u}}
    (hUpper : upper ∈ M.sets) (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) {idx : ZFSet.{u}} (hIdx : idx ∈ M.sets)
    (U Rc u : (M.nameDomain s).names) (row A : ZFSet.{u}) (q : P)
    (cut : s.encode q = ZFSet.pair row (assignmentCut levels alpha A)) :
    ZFSet.pair row A ∈ M.representedDomainConditions s upper levels alpha T valid idx U Rc u ↔
      ZFSet.pair row A ∈ upper ∧
      ((∀ r : P, r ≤ q → ¬ Name.ForcesMem r u.val U.val) ∨
        (Name.ForcesMem q u.val U.val ∧ ∃ v w : Name s,
          v.val ∈ T ∧ w.val ∈ T ∧ stageOneAssignment idx v.val w.val ∈ A ∧
          Name.ForcesEq q (Name.refinementClass T valid Rc.val u.val)
            (Name.refinementClass T valid Rc.val v))) := by
  let params : Fin 9 → ZFSet.{u} := ![s.carrier, s.conditionOrder,
    rowAssignmentCutGraph upper s.carrier levels alpha, T, idx, u.val.val, U.val.val,
    (Name.refinementClass T valid Rc.val u.val).val, Name.refinementClassGraph T valid Rc.val T valid]
  have paramsGround := representedParams_ground M s pairing unions powers separation collection carrier order
    hUpper hLevels hAlpha hT valid hIdx U Rc u
  have raw (phi : SetFormula 2) (x y : (M.nameDomain s).names) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode q) phi ![x.val.val, y.val.val] ↔
        Forces (M.nameDomain s) phi ![x, y] q := by
    have fields : (fun j : Fin 2 => (![x, y] j).val.val) = ![x.val.val, y.val.val] := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) j
    have result := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order phi q ![x, y]
    rw [fields] at result
    exact result
  let className (v : (M.nameDomain s).names) : (M.nameDomain s).names :=
    ⟨Name.refinementClass T valid Rc.val v.val,
      M.refinementClass_mem s pairing unions powers separation collection carrier order hT valid
        Rc.val v.val Rc.property v.property⟩
  rw [representedDomainConditions, ZFSet.mem_sep]
  change (ZFSet.pair row A ∈ upper ∧ Realize M.sets (representedEntryFormula 0 1 2 3 4 5 6 7 8 9)
    (extend (ZFSet.pair row A) params)) ↔ _
  apply and_congr_right
  intro member
  rw [realize_representedEntryFormula M pairing _ _ _ _ _ _ _ _ _ _ _
    (Fin.cases (M.transitive hUpper member) paramsGround)]
  change (∃ row' A' q', ZFSet.pair row A = ZFSet.pair row' A' ∧
    ZFSet.pair (ZFSet.pair row A) q' ∈ rowAssignmentCutGraph upper s.carrier levels alpha ∧
    (stageOneRawForces M s.carrier s.conditionOrder q' (.neg (.mem 0 1) : SetFormula 2) ![u.val.val, U.val.val] ∨
      (stageOneRawForces M s.carrier s.conditionOrder q' (.mem 0 1 : SetFormula 2) ![u.val.val, U.val.val] ∧
        ∃ v ∈ T, ∃ w ∈ T, ∃ z, stageOneAssignment idx v w ∈ A' ∧
          ZFSet.pair v z ∈ Name.refinementClassGraph T valid Rc.val T valid ∧
          stageOneRawForces M s.carrier s.conditionOrder q' (.equal 0 1 : SetFormula 2)
            ![(className u).val.val, z]))) ↔ _
  constructor
  · rintro ⟨row', A', q', same, entry, branch⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 same
    have equal := ((pair_mem_rowAssignmentCutGraph upper s.carrier levels alpha row A q').1 entry).2.2
    have eq : q' = s.encode q := equal.trans cut.symm
    rw [eq] at branch
    rcases branch with inactive | ⟨active, v, hv, w, hw, z, literal, classEntry, equal⟩
    · exact Or.inl ((raw (.neg (.mem 0 1)) u U).1 inactive)
    · let vName : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
      have classEqual := (Name.pair_mem_refinementClassGraph T valid Rc.val T valid vName.val z).1 classEntry |>.2
      rw [classEqual] at equal
      exact Or.inr ⟨(raw (.mem 0 1) u U).1 active, vName.val, ⟨w, valid w hw⟩,
        hv, hw, literal, (raw (.equal 0 1) (className u) (className vName)).1 equal⟩
  · intro branch
    refine ⟨row, A, s.encode q, rfl,
      (pair_mem_rowAssignmentCutGraph upper s.carrier levels alpha row A (s.encode q)).2
        ⟨member, s.encode_mem q, cut⟩, ?_⟩
    rcases branch with inactive | ⟨active, v, w, hv, hw, literal, equal⟩
    · exact Or.inl ((raw (.neg (.mem 0 1)) u U).2 inactive)
    · let vName : (M.nameDomain s).names := ⟨v, M.transitive hT hv⟩
      exact Or.inr ⟨(raw (.mem 0 1) u U).2 active, v.val, hv, w.val, hw,
        (className vName).val.val, literal,
        (Name.pair_mem_refinementClassGraph T valid Rc.val T valid v _).2 ⟨hv, rfl⟩,
        (raw (.equal 0 1) (className u) (className vName)).2 equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNiceAssignmentClassFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (members : ∀ j : Fin 15, (M.refinementLevelFormulaData a s b d level T T2 valid) j ∈ M.sets)
include pairing unions powers separation collection members

theorem niceAssignmentClassGraphs_entry {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (idx : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (u w : Name s) (hu : u.val ∈ T) (hw : w.val ∈ T)
    (member : stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val ∈ A) (side : Fin 2) (y : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val) y ∈ M.niceAssignmentClassGraphs a s b d level T T2 valid A side ↔
      y = (Name.refinementClass T valid
        (Fin.cases (motive := fun _ => Name s) Rc.val (fun _ => Rf.val) side)
        (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)).val := by
  have hT : T ∈ M.sets := members 6
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT (members 9) valid
  obtain ⟨_, _, hf, hc, _⟩ := (M.niceRefinementIndex_mem_iff a s b d pairing unions powers
    separation collection carrier order level T T2 valid family C E U Rf Rc).1 idx
  have fine := M.niceNameCandidates_subset a s T2 (d.principalFix C) hf
  have coarse := M.niceNameCandidates_subset a s T2 (d.principalFix C) hc
  have lookup (j : Fin 6) (R : Name s) (bound : R.val ∈ M.groundRelations T2 s.carrier)
      (value : (![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val] j) = R.val) :
      ∀ z, ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) z ∈
        refinementIndexFieldGraph I (M.groundRelations T2 s.carrier) j ↔ z = R.val := by
    intro z
    rw [refinementIndexCode, refinementIndexFieldGraph_entry, value]
    exact ⟨fun h => h.2.2, fun eq => ⟨idx, eq.symm ▸ bound, eq⟩⟩
  refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) side
  · dsimp only [niceAssignmentClassGraphs, Fin.cases_zero]
    exact M.assignmentClassGraph_entry s 0 pairing unions powers separation collection carrier order
      hA (members 5) hT valid Rc.val u w Rc.property (M.transitive hT hu) (M.transitive hT hw)
      member (lookup 5 Rc.val coarse rfl) y
  · dsimp only [niceAssignmentClassGraphs, Fin.cases_succ]
    exact M.assignmentClassGraph_entry s 1 pairing unions powers separation collection carrier order
      hA (members 4) hT valid Rf.val u w Rf.property (M.transitive hT hu) (M.transitive hT hw)
      member (lookup 4 Rf.val fine rfl) y

theorem niceAssignmentClassRequests
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
    (valid2 : ∀ z ∈ T2, IsName s z)
    (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
    (children : ∀ z : Name s, z.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) z)
    (secondChildren : ∀ z : Name s, z.val ∈ T2 →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) z)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (shape : A ⊆ stageOneAssignments I T)
    (small : M.groundEmbeddable A ZFSet.omega) :
    let graphs := M.niceAssignmentClassGraphs a s b d level T T2 valid A
    let bound := M.groundRelations T s.carrier
    let J := relationImage A bound (graphs 0) ∪ relationImage A bound (graphs 1)
    (∀ side, graphs side ∈ M.sets ∧ ZFSet.IsFunc A bound (graphs side)) ∧
    J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
    (∀ z ∈ J, IsName s z) ∧
    ∀ z : Name s, z.val ∈ J →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
      ∀ H : ConditionFilter P, Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := by
  let graphs := M.niceAssignmentClassGraphs a s b d level T T2 valid A
  let bound := M.groundRelations T s.carrier
  have hT : T ∈ M.sets := members 6
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have hb := M.groundRelations_mem pairing unions powers separation hT carrier
  have hOmega := M.omega_mem separation infinite
  have family := M.familySet_mem s ⊤ pairing unions powers separation hT (members 9) valid
  have request (side : Fin 2) (x : ZFSet.{u}) (hx : x ∈ A) :
      ∃ z : Name s, z.val ∈ bound ∧
        HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
        z.val ⊆ ZFSet.prod T s.carrier ∧
        ∀ y, ZFSet.pair x y ∈ graphs side ↔ y = z.val := by
    obtain ⟨i, hi, rawU, hu, rawW, hw, rfl⟩ := (mem_stageOneAssignments I T x).1 (shape hx)
    obtain ⟨C, E, U, Rf, Rc, rfl⟩ := M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
    let u : Name s := ⟨rawU, valid rawU hu⟩
    let w : Name s := ⟨rawW, valid rawW hw⟩
    obtain ⟨_, _, hf, hc, _⟩ := (M.niceRefinementIndex_mem_iff a s b d pairing unions powers
      separation collection carrier order level T T2 valid family C E U Rf Rc).1 hi
    have fineHS := niceNameCode_principal_hs a s d base C directed secondChildren
      ((M.mem_niceNameCandidates a s T2 (d.principalFix C) Rf.val.val).1 hf).2
    have coarseHS := niceNameCode_principal_hs a s d base C directed secondChildren
      ((M.mem_niceNameCandidates a s T2 (d.principalFix C) Rc.val.val).1 hc).2
    have result (R : (M.nameDomain s).names) (z : Name s) (hz : z.val ∈ T)
        (hs : HereditarilySymmetric a s (d.principalSupportFamily base directed) R.val) :
        (Name.refinementClass T valid R.val z).val ∈ bound ∧
        HereditarilySymmetric a s (d.principalSupportFamily base directed)
          (Name.refinementClass T valid R.val z) ∧
        (Name.refinementClass T valid R.val z).val ⊆ ZFSet.prod T s.carrier :=
      ⟨(M.mem_groundRelations T s.carrier _).2
          ⟨M.refinementClass_mem s pairing unions powers separation collection carrier order
            hT valid R.val z R.property (M.transitive hT hz), Name.refinementClass_subset T valid R.val z⟩,
        Name.refinementClass_hs_of_hs a T valid closed _ children R.val z hs (children z hz),
        Name.refinementClass_subset T valid R.val z⟩
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) side
    · exact ⟨Name.refinementClass T valid Rc.val u, (result Rc u hu coarseHS).1,
        (result Rc u hu coarseHS).2.1, (result Rc u hu coarseHS).2.2,
        M.niceAssignmentClassGraphs_entry a s b d level T T2 valid pairing unions powers separation
          collection members hA C E U Rf Rc hi u w hu hw hx 0⟩
    · exact ⟨Name.refinementClass T valid Rf.val w, (result Rf w hw fineHS).1,
        (result Rf w hw fineHS).2.1, (result Rf w hw fineHS).2.2,
        M.niceAssignmentClassGraphs_entry a s b d level T T2 valid pairing unions powers separation
          collection members hA C E U Rf Rc hi u w hu hw hx 1⟩
  have grounds (side : Fin 2) : graphs side ∈ M.sets :=
    M.assignmentClassGraph_mem side pairing unions powers separation hA
      (members (Fin.cases 5 (fun _ => 4) side)) hT carrier order (members 9)
  have functions (side : Fin 2) : ZFSet.IsFunc A bound (graphs side) := by
    refine ⟨?_, ?_⟩
    · intro x h
      unfold graphs niceAssignmentClassGraphs assignmentClassGraph at h
      exact (ZFSet.mem_sep.1 h).1
    · intro x hx
      obtain ⟨z, _, _, _, entries⟩ := request side x hx
      exact ⟨z.val, (entries _).2 rfl, fun y h => (entries y).1 h⟩
  have imageGround (side : Fin 2) := M.relationImage_mem separation hA hb (grounds side)
  have imageSmall (side : Fin 2) := M.groundEmbeddable_function_image pairing unions powers
    separation choice hA hb hOmega (grounds side) (functions side) small
  have imageFacts (side : Fin 2) (y : ZFSet.{u})
      (member : y ∈ relationImage A bound (graphs side)) :
      ∃ z : Name s, y = z.val ∧ HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
        z.val ⊆ ZFSet.prod T s.carrier := by
    obtain ⟨_, x, hx, edge⟩ := (mem_relationImage A bound (graphs side) y).1 member
    obtain ⟨z, _, symmetric, subset, entries⟩ := request side x hx
    exact ⟨z, (entries y).1 edge, symmetric, subset⟩
  have allFacts (y : ZFSet.{u}) (member : y ∈ relationImage A bound (graphs 0) ∪
      relationImage A bound (graphs 1)) :
      ∃ z : Name s, y = z.val ∧ HereditarilySymmetric a s (d.principalSupportFamily base directed) z ∧
        z.val ⊆ ZFSet.prod T s.carrier :=
    (ZFSet.mem_union.1 member).elim (imageFacts 0 y) (imageFacts 1 y)
  refine ⟨fun side => ⟨grounds side, functions side⟩,
    M.binary_union_mem pairing unions (imageGround 0) (imageGround 1),
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      (imageGround 0) (imageGround 1) (imageSmall 0) (imageSmall 1), ?_, ?_⟩
  · intro y member
    obtain ⟨z, rfl, _, _⟩ := allFacts y member
    exact z.property
  · intro z member
    obtain ⟨w, equal, symmetric, subset⟩ := allFacts z.val member
    have same : z = w := Subtype.ext equal
    subst w
    exact ⟨symmetric, fun H => Name.eval_subset_familySet_of_code_subset H T valid z subset⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem mem_assignmentOnIndices (B T A z : ZFSet.{u}) :
    z ∈ assignmentOnIndices B T A ↔ z ∈ A ∧ z ∈ stageOneAssignments B T :=
  ZFSet.mem_sep

theorem assignmentOnIndices_entry (B T A t u w : ZFSet.{u}) :
    stageOneAssignment t u w ∈ assignmentOnIndices B T A ↔
      stageOneAssignment t u w ∈ A ∧ t ∈ B ∧ u ∈ T ∧ w ∈ T := by
  rw [mem_assignmentOnIndices, stageOneAssignment_mem_assignments]

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem assignmentOnIndices_mem {B T A : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentOnIndices B T A ∈ M.sets :=
  M.bounded_separation_mem separation (.mem 0 1)
    (extend (stageOneAssignments B T) Fin.elim0)
    (Fin.cases (M.stageOneAssignments_mem pairing unions powers separation hB hT)
      (fun i => Fin.elim0 i)) hA

theorem assignmentOnIndices_small {B T A N : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets)
    (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentOnIndices B T A) N :=
  M.groundEmbeddable_restrict separation
    (M.assignmentOnIndices_mem pairing unions powers separation hB hT hA) hN
    (fun _ hz => (mem_assignmentOnIndices B T A _).1 hz |>.1) small

theorem assignmentOnIndices_candidate {rows I T B row A : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (member : ZFSet.pair row A ∈ M.stageOneCandidateBound rows I T) :
    ZFSet.pair row (assignmentOnIndices B T A) ∈ M.stageOneCandidateBound rows B T := by
  obtain ⟨hr, hA, _, small⟩ := (M.pair_mem_stageOneCandidateBound rows I T row A).1 member
  exact (M.pair_mem_stageOneCandidateBound rows B T row _).2
    ⟨hr, M.assignmentOnIndices_mem pairing unions powers separation hB hT hA,
      fun _ hz => (mem_assignmentOnIndices B T A _).1 hz |>.2,
      M.assignmentOnIndices_small pairing unions powers separation hB hT hA omega small⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedIndexAssignmentSlices
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem mem_fixedIndexAssignmentPairs (idx T A v w : ZFSet.{u}) :
    ZFSet.pair v w ∈ fixedIndexAssignmentPairs idx T A ↔
      v ∈ T ∧ w ∈ T ∧ stageOneAssignment idx v w ∈ A := by
  rw [fixedIndexAssignmentPairs, mem_relationImage]
  constructor
  · rintro ⟨bound, x, hx, edge⟩
    obtain ⟨i, hi, pair, _, equal⟩ := (mem_productSecond _ _ _).1 edge
    have ei : i = idx := ZFSet.mem_singleton.1 hi
    obtain ⟨ex, ep⟩ := ZFSet.pair_inj.1 equal
    subst i
    subst pair
    exact ⟨(ZFSet.pair_mem_prod.1 bound).1, (ZFSet.pair_mem_prod.1 bound).2,
      ex ▸ (mem_assignmentOnIndices _ _ _ _).1 hx |>.1⟩
  · rintro ⟨hv, hw, old⟩
    have bounds := ZFSet.pair_mem_prod.2 ⟨hv, hw⟩
    exact ⟨bounds, stageOneAssignment idx v w,
      (assignmentOnIndices_entry _ _ _ _ _ _).2 ⟨old, ZFSet.mem_singleton.2 rfl, hv, hw⟩,
      (mem_productSecond _ _ _).2 ⟨idx, ZFSet.mem_singleton.2 rfl, _, bounds, rfl⟩⟩

theorem fixedIndexAssignmentClassGraph_entry (idx T A B graph v w y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair v w) y ∈ fixedIndexAssignmentClassGraph idx T A B graph ↔
      v ∈ T ∧ w ∈ T ∧ stageOneAssignment idx v w ∈ A ∧ y ∈ B ∧
        ZFSet.pair (stageOneAssignment idx v w) y ∈ graph := by
  rw [fixedIndexAssignmentClassGraph, pair_mem_relationCompose, mem_fixedIndexAssignmentPairs]
  constructor
  · rintro ⟨⟨hv, hw, old⟩, hy, x, _, inverse, edge⟩
    have projection := ((pair_mem_relationConverse _ _ _ x (ZFSet.pair v w)).1 inverse).2.2
    obtain ⟨i, hi, pair, _, equal⟩ := (mem_productSecond _ _ _).1 projection
    have ei : i = idx := ZFSet.mem_singleton.1 hi
    obtain ⟨ex, ep⟩ := ZFSet.pair_inj.1 equal
    subst i
    subst pair
    subst x
    exact ⟨hv, hw, old, hy, edge⟩
  · rintro ⟨hv, hw, old, hy, edge⟩
    have bound := ZFSet.pair_mem_prod.2 ⟨hv, hw⟩
    have triple := (stageOneAssignment_mem_assignments {idx} T idx v w).2
      ⟨ZFSet.mem_singleton.2 rfl, hv, hw⟩
    exact ⟨⟨hv, hw, old⟩, hy, _, triple,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨triple, bound,
        (mem_productSecond _ _ _).2 ⟨idx, ZFSet.mem_singleton.2 rfl, _, bound, rfl⟩⟩, edge⟩

theorem fixedIndexAssignmentClassGraph_function {idx T A B graph D : ZFSet.{u}}
    (function : ZFSet.IsFunc D B graph)
    (covered : ∀ v ∈ T, ∀ w ∈ T, stageOneAssignment idx v w ∈ A →
      stageOneAssignment idx v w ∈ D) :
    ZFSet.IsFunc (fixedIndexAssignmentPairs idx T A) B
      (fixedIndexAssignmentClassGraph idx T A B graph) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    unfold fixedIndexAssignmentClassGraph relationCompose at hz
    exact (ZFSet.mem_sep.1 hz).1
  · intro pair member
    have pairBound := (mem_relationImage _ _ _ pair).1 member |>.1
    obtain ⟨v, hv, w, hw, rfl⟩ := ZFSet.mem_prod.1 pairBound
    have old := (mem_fixedIndexAssignmentPairs idx T A v w).1 member |>.2.2
    obtain ⟨y, edge, unique⟩ := function.2 _ (covered v hv w hw old)
    have hy := (ZFSet.pair_mem_prod.1 (function.1 edge)).2
    exact ⟨y, (fixedIndexAssignmentClassGraph_entry _ _ _ _ _ _ _ _).2 ⟨hv, hw, old, hy, edge⟩,
      fun z hz => unique z ((fixedIndexAssignmentClassGraph_entry _ _ _ _ _ _ _ _).1 hz).2.2.2.2⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem fixedIndexAssignmentPairs_mem_small
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {idx T A N : ZFSet.{u}} (hIdx : idx ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    fixedIndexAssignmentPairs idx T A ∈ M.sets ∧
      M.groundEmbeddable (fixedIndexAssignmentPairs idx T A) N := by
  have singleton : ({idx} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hIdx hIdx
  have slice := M.assignmentOnIndices_mem pairing unions powers separation singleton hT hA
  have sliceSmall := M.assignmentOnIndices_small pairing unions powers separation singleton hT hA hN small
  have bound := M.prod_mem pairing unions powers separation hT hT
  have graph := M.productSecond_mem pairing unions powers separation singleton bound
  exact ⟨M.relationImage_mem separation slice bound graph,
    M.groundEmbeddable_function_image pairing unions powers separation choice slice bound hN
      graph (productSecond_function {idx} (ZFSet.prod T T)) sliceSmall⟩

theorem fixedIndexAssignmentClassGraph_mem
    {idx T A B graph : ZFSet.{u}} (hIdx : idx ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hGraph : graph ∈ M.sets) :
    fixedIndexAssignmentClassGraph idx T A B graph ∈ M.sets := by
  have singleton : ({idx} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hIdx hIdx
  have pairs := M.prod_mem pairing unions powers separation hT hT
  have slice := M.assignmentOnIndices_mem pairing unions powers separation singleton hT hA
  have projection := M.productSecond_mem pairing unions powers separation singleton pairs
  have domain := M.relationImage_mem separation slice pairs projection
  have triples := M.stageOneAssignments_mem pairing unions powers separation singleton hT
  exact M.relationCompose_mem pairing unions powers separation domain triples hB
    (M.relationConverse_mem pairing unions powers separation triples pairs projection) hGraph

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAugmentedClassRequests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_assignmentClassRequests
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let I := M.niceRefinementIndices act lower b d alpha T T2 valid
    let selected := assignmentOnIndices I T A
    let graphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid selected
    let bound := M.groundRelations T lower.carrier
    let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
    selected ∈ M.sets ∧ M.groundEmbeddable selected ZFSet.omega ∧
    (∀ side, graphs side ∈ M.sets ∧ ZFSet.IsFunc selected bound (graphs side)) ∧
    J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧
    (∀ z ∈ J, IsName lower z) ∧
    (∀ z : Name lower, z.val ∈ J →
      HereditarilySymmetric act lower (d.principalSupportFamily base directed) z ∧
      ∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
    (∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names)
      (_idx : refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ I)
      (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∀ (side : Fin 2) y, ZFSet.pair (stageOneAssignment
        (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        u.val w.val) y ∈ graphs side ↔
        y = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let I := M.niceRefinementIndices act lower b d alpha T T2 valid
  let selected := assignmentOnIndices I T A
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have fields : ∀ j, M.refinementLevelFormulaData act lower b d alpha T T2 valid j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem _ (M.transitive
      (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion entry))
  have candidate := ((M.mem_refinementHistoryForcing c.carrier T stages packed _).1 condition).1
  have selectedCandidate := M.assignmentOnIndices_candidate pairing unions powers separation
    (fields 0) hT omega candidate
  obtain ⟨_, hSelected, selectedShape, selectedSmall⟩ :=
    (M.pair_mem_stageOneCandidateBound c.carrier I T row selected).1 selectedCandidate
  let image := fun g A => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g) A
  have coordinates := M.semanticStructuralPrefixAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  have emptyImage : ∀ g, image g ∅ = ∅ := fun g =>
    M.structuralAssignmentImage_empty t b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 alpha history (t.encode g)
  obtain ⟨_, closed, children⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T valid1 closed1 symmetric1
  obtain ⟨validSecond, _, secondChildren⟩ := M.refinementHistoryRowNameFamily_transport c
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier a act image coordinates emptyImage
    (d.principalSupportFamily base directed) T2 valid2 closed2 symmetric2
  obtain ⟨graphs, hJ, smallJ, validJ, facts⟩ := M.niceAssignmentClassRequests act lower b d alpha T T2 valid
    pairing unions powers separation collection fields infinite choice base directed validSecond closed
    children secondChildren hSelected selectedShape selectedSmall
  refine ⟨hSelected, selectedSmall, graphs, hJ, smallJ, validJ, facts, ?_⟩
  intro C E U Rf Rc idx u w hu hw inA side y
  have inSelected : stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ selected :=
    (mem_assignmentOnIndices I T A _).2 ⟨inA,
      (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨idx, hu, hw⟩⟩
  exact M.niceAssignmentClassGraphs_entry act lower b d alpha T T2 valid pairing unions powers
    separation collection fields hSelected C E U Rf Rc idx u w hu hw inSelected side y

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefix_fixedIndexClassFamilies
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let I := M.niceRefinementIndices act lower b d alpha T T2 valid
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
    let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    idx ∈ I →
    let oldPairs := fixedIndexAssignmentPairs idx T A
    let bound := M.groundRelations T lower.carrier
    let originalGraphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid
      (assignmentOnIndices I T A)
    let graphs := fun side => fixedIndexAssignmentClassGraph idx T A bound (originalGraphs side)
    let images := fun side => relationImage oldPairs bound (graphs side)
    oldPairs ∈ M.sets ∧ M.groundEmbeddable oldPairs ZFSet.omega ∧
    ∀ side : Fin 2, graphs side ∈ M.sets ∧ ZFSet.IsFunc oldPairs bound (graphs side) ∧
      images side ∈ M.sets ∧ M.groundEmbeddable (images side) ZFSet.omega ∧
      (∀ z ∈ images side, IsName lower z) ∧
      (∀ z, z ∈ images side ↔ ∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
        stageOneAssignment idx v.val w.val ∈ A ∧
        z = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) v (fun _ => w) side)).val) ∧
      (∀ (v w : Name lower), v.val ∈ T → w.val ∈ T →
        stageOneAssignment idx v.val w.val ∈ A → ∀ z,
        ZFSet.pair (ZFSet.pair v.val w.val) z ∈ graphs side ↔
        z = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) v (fun _ => w) side)).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let I := M.niceRefinementIndices act lower b d alpha T T2 valid
  dsimp only
  intro C E U Rf Rc inI
  let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let oldPairs := fixedIndexAssignmentPairs idx T A
  let bound := M.groundRelations T lower.carrier
  let selected := assignmentOnIndices I T A
  let originalGraphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid selected
  let graphs := fun side => fixedIndexAssignmentClassGraph idx T A bound (originalGraphs side)
  let images := fun side => relationImage oldPairs bound (graphs side)
  obtain ⟨_, _, original, _, _, validImages, _, entries⟩ :=
    M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice condition
  have candidate := ((M.mem_refinementHistoryForcing c.carrier T stages packed _).1 condition).1
  obtain ⟨_, hA, _, smallA⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  have hIdx : idx ∈ M.sets := M.refinementIndexCode_mem pairing hAlpha
    (M.transitive nodes (b.encode_mem C)) (M.transitive nodes (b.encode_mem E))
    U.property Rf.property Rc.property
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : lower.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha hPacked) omega
  have hBound := M.groundRelations_mem pairing unions powers separation hT hQ
  obtain ⟨hPairs, smallPairs⟩ := M.fixedIndexAssignmentPairs_mem_small pairing unions powers separation
    choice hIdx hT hA omega smallA
  have covered (v : ZFSet.{u}) (hv : v ∈ T) (w : ZFSet.{u}) (hw : w ∈ T)
      (old : stageOneAssignment idx v w ∈ A) : stageOneAssignment idx v w ∈ selected :=
    (assignmentOnIndices_entry _ _ _ _ _ _).2 ⟨old, inI, hv, hw⟩
  refine ⟨hPairs, smallPairs, ?_⟩
  intro side
  have graphGround : graphs side ∈ M.sets := M.fixedIndexAssignmentClassGraph_mem pairing unions powers
    separation hIdx hT hA hBound (original side).1
  have function : ZFSet.IsFunc oldPairs bound (graphs side) :=
    fixedIndexAssignmentClassGraph_function (original side).2 covered
  have exactEntry (v w : Name lower) (hv : v.val ∈ T) (hw : w.val ∈ T)
      (old : stageOneAssignment idx v.val w.val ∈ A) (z : ZFSet.{u}) :
      ZFSet.pair (ZFSet.pair v.val w.val) z ∈ graphs side ↔
        z = (Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) v (fun _ => w) side)).val := by
    rw [fixedIndexAssignmentClassGraph_entry]
    have entry := entries C E U Rf Rc inI v w hv hw old side z
    constructor
    · intro edge
      exact entry.1 edge.2.2.2.2
    · intro equal
      have edge := entry.2 equal
      exact ⟨hv, hw, old, (ZFSet.pair_mem_prod.1 ((original side).2.1 edge)).2, edge⟩
  have imageSubset : images side ⊆ relationImage selected bound (originalGraphs side) := by
    intro z hz
    obtain ⟨hy, pair, hp, edge⟩ := (mem_relationImage _ _ _ z).1 hz
    have pb := (mem_relationImage _ _ _ pair).1 hp |>.1
    obtain ⟨v, hv, w, hw, rfl⟩ := ZFSet.mem_prod.1 pb
    have fields := (fixedIndexAssignmentClassGraph_entry _ _ _ _ _ _ _ _).1 edge
    exact (mem_relationImage _ _ _ z).2 ⟨hy, _, covered v hv w hw fields.2.2.1, fields.2.2.2.2⟩
  refine ⟨graphGround, function, M.relationImage_mem separation hPairs hBound graphGround,
    M.groundEmbeddable_function_image pairing unions powers separation choice hPairs hBound omega
      graphGround function smallPairs, ?_, ?_, exactEntry⟩
  · intro z hz
    apply validImages z
    have liftImage : ∀ side : Fin 2, ∀ z, z ∈ relationImage selected bound (originalGraphs side) →
        z ∈ relationImage selected bound (originalGraphs 0) ∪ relationImage selected bound (originalGraphs 1) :=
      Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inl hz))
        (Fin.cases (fun _ hz => ZFSet.mem_union.2 (Or.inr hz)) (fun j => Fin.elim0 j))
    exact liftImage side z (imageSubset hz)
  · intro z
    constructor
    · intro hz
      obtain ⟨_, pair, hp, edge⟩ := (mem_relationImage _ _ _ z).1 hz
      have pb := (mem_relationImage _ _ _ pair).1 hp |>.1
      obtain ⟨v, hv, w, hw, rfl⟩ := ZFSet.mem_prod.1 pb
      have old := (mem_fixedIndexAssignmentPairs idx T A v w).1 hp |>.2.2
      let vName : Name lower := ⟨v, valid v hv⟩
      let wName : Name lower := ⟨w, valid w hw⟩
      exact ⟨vName, wName, hv, hw, old, (exactEntry vName wName hv hw old z).1 edge⟩
    · rintro ⟨v, w, hv, hw, old, equal⟩
      have edge := (exactEntry v w hv hw old z).2 equal
      exact (mem_relationImage _ _ _ z).2
        ⟨(ZFSet.pair_mem_prod.1 (function.1 edge)).2, ZFSet.pair v.val w.val,
          (mem_fixedIndexAssignmentPairs _ _ _ _ _).2 ⟨hv, hw, old⟩, edge⟩

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOrdinaryEqualityDecisionFusion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem ordinaryEqualityDecisions_mem (separation : SeparationSchema M.sets)
    {Q order sigma tau : ZFSet.{u}} (hQ : Q ∈ M.sets) (hOrder : order ∈ M.sets)
    (hSigma : sigma ∈ M.sets) (hTau : tau ∈ M.sets) :
    M.ordinaryEqualityDecisions Q order sigma tau ∈ M.sets :=
  (M.definable_ordinaryEqualityDecisions separation).closed ![sigma, Q, order, tau]
    (Fin.cases hSigma (Fin.cases hQ (Fin.cases hOrder (Fin.cases hTau (fun i => Fin.elim0 i)))))

theorem pair_mem_ordinaryEqualityDecisionFamily (T Q order tau sigma D : ZFSet.{u}) :
    ZFSet.pair sigma D ∈ M.ordinaryEqualityDecisionFamily T Q order tau ↔
      sigma ∈ T ∧ D = M.ordinaryEqualityDecisions Q order sigma tau := by
  rw [ordinaryEqualityDecisionFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨x, equal⟩
    obtain ⟨hx, hd⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx ▸ x.property, hd.symm.trans (congrArg (fun y => M.ordinaryEqualityDecisions Q order y tau) hx)⟩
  · rintro ⟨member, rfl⟩
    exact ⟨⟨sigma, member⟩, rfl⟩

theorem ordinaryEqualityDecisionFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T Q order tau : ZFSet.{u}} (hT : T ∈ M.sets) (hQ : Q ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTau : tau ∈ M.sets) :
    M.ordinaryEqualityDecisionFamily T Q order tau ∈ M.sets :=
  (M.definable_ordinaryEqualityDecisions separation).graph_mem pairing separation collection
    ![Q, order, tau] (Fin.cases hQ (Fin.cases hOrder (Fin.cases hTau (fun i => Fin.elim0 i)))) hT

theorem ordinaryEqualityDecisionFamily_function
    (separation : SeparationSchema M.sets)
    {T Q order tau : ZFSet.{u}} (hT : T ∈ M.sets) (hQ : Q ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTau : tau ∈ M.sets) :
    ZFSet.IsFunc T (M.groundPower Q) (M.ordinaryEqualityDecisionFamily T Q order tau) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨sigma, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨sigma.property, (M.mem_groundPower Q _).2
      ⟨M.ordinaryEqualityDecisions_mem separation hQ hOrder (M.transitive hT sigma.property) hTau,
        M.ordinaryEqualityDecisions_subset Q order sigma.val tau⟩⟩
  · intro sigma hSigma
    exact ⟨M.ordinaryEqualityDecisions Q order sigma tau,
      (M.pair_mem_ordinaryEqualityDecisionFamily T Q order tau sigma _).2 ⟨hSigma, rfl⟩,
      fun D entry => (M.pair_mem_ordinaryEqualityDecisionFamily T Q order tau sigma D).1 entry |>.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem ordinaryEqualityDecisions_simultaneous_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (small : M.groundEmbeddable T ZFSet.omega)
    (valid : ∀ sigma ∈ T, IsName s sigma)
    (closed : InternallyCountablyClosed M s) (tau : (M.nameDomain s).names) (base : P) :
    DenseBelow base {q | q ≤ base ∧ ∀ sigma : (M.nameDomain s).names,
      sigma.val.val ∈ T → Name.ForcesEq q sigma.val tau.val ∨
        ∀ r, r ≤ q → ¬ Name.ForcesEq r sigma.val tau.val} := by
  let f := M.ordinaryEqualityDecisionFamily T s.carrier s.conditionOrder tau.val.val
  have hf : f ∈ M.sets := M.ordinaryEqualityDecisionFamily_mem
    pairing separation collection hT carrier order tau.property
  have function : ZFSet.IsFunc T (M.groundPower s.carrier) f :=
    M.ordinaryEqualityDecisionFamily_function separation hT carrier order tau.property
  have persistent : ∀ z E, ZFSet.pair z E ∈ f → ∀ p q : P,
      q ≤ p → s.encode p ∈ E → s.encode q ∈ E := by
    intro z E ef p q qp member
    obtain ⟨hz, rfl⟩ := (M.pair_mem_ordinaryEqualityDecisionFamily
      T s.carrier s.conditionOrder tau.val.val z E).1 ef
    let sigma : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    have first := (M.ordinaryEqualityDecisions_entry s pairing unions powers separation collection
      carrier order sigma tau p).1 member
    apply (M.ordinaryEqualityDecisions_entry s pairing unions powers separation collection
      carrier order sigma tau q).2
    rcases first with equal | negative
    · exact Or.inl (Name.forcesEq_mono equal qp)
    · exact Or.inr (fun r rq => negative r (rq.trans qp))
  have dense : ∀ z E, ZFSet.pair z E ∈ f → DenseBelow base {q | s.encode q ∈ E} := by
    intro z E ef p _
    obtain ⟨hz, rfl⟩ := (M.pair_mem_ordinaryEqualityDecisionFamily
      T s.carrier s.conditionOrder tau.val.val z E).1 ef
    let sigma : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    obtain ⟨raw, member, before⟩ := M.ordinaryEqualityDecisions_dense s pairing unions powers
      separation collection carrier order sigma tau (s.encode p) (s.encode_mem p)
    obtain ⟨q, rfl⟩ := (s.mem_carrier raw).1
      (M.ordinaryEqualityDecisions_subset s.carrier s.conditionOrder z tau.val.val member)
    exact ⟨q, (s.pair_mem_conditionOrder q p).1 before, member⟩
  have common := M.internally_countableDenseFamily_denseBelow s pairing unions powers separation
    infinite choice carrier order hT hf small function closed base persistent dense
  intro p pb
  obtain ⟨q, qp, qb, all⟩ := common p pb
  refine ⟨q, qp, qb, ?_⟩
  intro sigma member
  exact (M.ordinaryEqualityDecisions_entry s pairing unions powers separation collection
    carrier order sigma tau q).1 (all sigma.val.val _
      ((M.pair_mem_ordinaryEqualityDecisionFamily T s.carrier s.conditionOrder tau.val.val
        sigma.val.val _).2 ⟨member, rfl⟩))

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticRepresentedDomainEasyCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open scoped ZFSet
universe u
section Core
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

private theorem domain_decisions_of_row_closed
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (rowClosed : InternallyCountablyClosed M c)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid →
      ∀ u : Name lower, u.val ∈ T →
      ∃ pCut r : SetMembers Q,
        lower.encode pCut = ZFSet.pair row (assignmentCut
          (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
        ((∀ q, q ≤ r → ¬ Name.ForcesMem q u U.val) ∨
          (Name.ForcesMem r u U.val ∧
            ((∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A ∧
              Name.ForcesEq r (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v)) ∨
            (∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
              ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v))))) := by
  classical
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  dsimp only
  intro C E U Rf Rc idx u hu
  let pCut : SetMembers Q := SetMembers.ofMem
    (ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A))
    ((run).carriers.cut_mem condition member)
  have cutCode : lower.encode pCut =
      ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A) :=
    SetMembers.raw_ofMem _ _
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have fields : ∀ j, M.refinementLevelFormulaData act lower b d alpha T T2 valid j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem _ (M.transitive
      (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion entry))
  have lowerCarrier : lower.carrier ∈ M.sets := fields 7
  have lowerOrder : lower.conditionOrder ∈ M.sets := fields 8
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  have closedRestricted := M.semanticStructuralTrace_internally_closed c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
    nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
    cutOrdinal (trace.restrict cutOrdinal subset) infinite choice rowClosed
  dsimp only at closedRestricted
  rw [packedEq] at closedRestricted
  have closed : InternallyCountablyClosed M lower := closedRestricted
  let original : (M.nameDomain lower).names := ⟨u, M.transitive hT hu⟩
  let coarse : (M.nameDomain lower).names := ⟨Name.refinementClass T valid Rc.val u,
    M.refinementClass_mem lower pairing unions powers separation collection lowerCarrier lowerOrder
      hT valid Rc.val u Rc.property original.property⟩
  obtain ⟨activeCut, activeBelow, decided⟩ := decisionWitness_dense
    (M.nameDomain lower) (.mem 0 1) (extend original (extend U Fin.elim0)) pCut
  rcases decided with active | inactive
  · obtain ⟨_, _, families⟩ :=
      M.semanticStructuralPrefix_fixedIndexClassFamilies c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
        topMem topRows hs hh ordinal trace member infinite choice condition C E U Rf Rc idx
    obtain ⟨_, _, wholeImage, smallImage, validImage, imageEntry, _⟩ := families 0
    obtain ⟨r, belowActive, _, decisions⟩ := M.ordinaryEqualityDecisions_simultaneous_dense lower
      pairing unions powers separation collection infinite choice lowerCarrier lowerOrder
      wholeImage smallImage validImage closed coarse activeCut activeCut le_rfl
    refine ⟨pCut, r, cutCode, belowActive.trans activeBelow, Or.inr
      ⟨Name.forcesMem_mono active belowActive, ?_⟩⟩
    by_cases reuse : ∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
        stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
          U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A ∧
        Name.ForcesEq r (Name.refinementClass T valid Rc.val u)
          (Name.refinementClass T valid Rc.val v)
    · exact Or.inl reuse
    · refine Or.inr ?_
      intro v w hv hw old q below equal
      have inImage := (imageEntry (Name.refinementClass T valid Rc.val v).val).2
        ⟨v, w, hv, hw, old, rfl⟩
      let previous : (M.nameDomain lower).names :=
        ⟨Name.refinementClass T valid Rc.val v, M.transitive wholeImage inImage⟩
      rcases decisions previous inImage with positive | negative
      · exact reuse ⟨v, w, hv, hw, old, Name.forcesEq_symm positive⟩
      · exact negative q below (Name.forcesEq_symm equal)
  · exact ⟨pCut, activeCut, cutCode, activeBelow, Or.inl inactive⟩

end Core

variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem semanticStructuralSuccessor_domain_decisions
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u}),
      ∀ (rowAction : a.actionGraph c t ∈ M.sets)
        (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
        (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
        (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
        (supports : supportBasisCode b t d.principalFix ∈ M.sets)
        (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
        (valid1 : ∀ z ∈ T, IsName c.pairEmpty z) (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
        (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
        (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
        (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (topMem : rowTop ∈ c.carrier)
        (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
        (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
        (ordinal : ordinalSetProperty stages)
        (trace : OrdinalRecursionTrace (fun level prior stage => stage =
          M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
            t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
            (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
        (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
        (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 ordinal trace
      let cutOrdinal := ordinalSetProperty_member ordinal member
      let subset := (And.left ordinal) alpha member
      let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      ∀ {row A : ZFSet.{u}},
      ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation Q
      let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
        cutOrdinal carrier T valid1
      let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
        valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace
        (M.transitive hs member) cutOrdinal subset
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid →
      ∀ u : Name lower, u.val ∈ T →
      ∃ pCut r : SetMembers Q,
        lower.encode pCut = ZFSet.pair row (assignmentCut
          (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
        ((∀ q, q ≤ r → ¬ Name.ForcesMem q u U.val) ∨
          (Name.ForcesMem r u U.val ∧
            ((∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A ∧
              Name.ForcesEq r (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v)) ∨
            (∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
              ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v))))) := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows stages history hs hh ordinal trace
    alpha member row A condition
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation
    infinite choice hX two
  exact domain_decisions_of_row_closed M c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier order rowAction group nodes nodeOrder nodeAction
    nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice rowClosed condition

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem semanticStructuralSuccessor_domain_decisions_lift
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u}),
      ∀ (rowAction : a.actionGraph c t ∈ M.sets)
        (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
        (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
        (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
        (supports : supportBasisCode b t d.principalFix ∈ M.sets)
        (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
        (valid1 : ∀ z ∈ T, IsName c.pairEmpty z) (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
        (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
        (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
        (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (topMem : rowTop ∈ c.carrier)
        (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
        (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
        (ordinal : ordinalSetProperty stages)
        (trace : OrdinalRecursionTrace (fun level prior stage => stage =
          M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
            t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
            (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
        (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
        (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 ordinal trace
      let cutOrdinal := ordinalSetProperty_member ordinal member
      let subset := (And.left ordinal) alpha member
      let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      ∀ {row A : ZFSet.{u}},
      ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation Q
      let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
        cutOrdinal carrier T valid1
      let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
        valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace
        (M.transitive hs member) cutOrdinal subset
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid →
      ∀ u : Name lower, u.val ∈ T →
      ∃ pCut r : SetMembers Q,
        lower.encode pCut = ZFSet.pair row (assignmentCut
          (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
        ((∀ q, q ≤ r → ¬ Name.ForcesMem q u U.val) ∨
          (Name.ForcesMem r u U.val ∧
            ((∃ v w : Name lower, v.val ∈ T ∧ w.val ∈ T ∧
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A ∧
              Name.ForcesEq r (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v)) ∨
            (∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
              ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v))))) ∧
        ∃ lowerRow lowerA : ZFSet.{u}, lower.encode r = ZFSet.pair lowerRow lowerA ∧
          let liftedA := assignmentSplice (refinementDataHistoryLevels stages packed T) alpha lowerA A
          ZFSet.pair lowerRow liftedA ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
          ZFSet.pair (ZFSet.pair lowerRow liftedA) (ZFSet.pair row A) ∈
            M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
          A ⊆ liftedA ∧
          ZFSet.pair lowerRow (assignmentCut (refinementDataHistoryLevels stages packed T) alpha liftedA) =
            lower.encode r := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows stages history hs hh ordinal trace
    alpha member row A condition
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
    (M.natSetCode_mem separation infinite 2)
  let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
    (M.natSetCode_mem separation infinite 2)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  intro C E U Rf Rc idx u hu
  obtain ⟨pCut, r, cutCode, below, decisions⟩ :=
    M.semanticStructuralSuccessor_domain_decisions t b d base directed
      pairing unions powers separation collection infinite choice X hX a T T2 rowTop
      rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
      valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows stages history hs hh ordinal trace alpha member condition C E U Rf Rc idx u hu
  obtain ⟨lowerRow, _, lowerA, _, rCode⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier T alpha lowerPacked (SetMembers.raw_mem r))
  change lower.encode r = ZFSet.pair lowerRow lowerA at rCode
  change lower.encode pCut = ZFSet.pair row
    (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A) at cutCode
  have lowerBelow : ZFSet.pair (ZFSet.pair lowerRow lowerA)
      (ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) alpha A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T alpha lowerPacked := by
    change ZFSet.pair (lower.encode r) (lower.encode pCut) ∈ _ at below
    rwa [rCode, cutCode] at below
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  obtain ⟨lifted, extension, exactCut⟩ := historyRun.splice_lifting pairing unions powers separation
    infinite choice hs hPacked hT (M.transitive hs member) ordinal cutOrdinal subset mono condition lowerBelow
  have retained := ((M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    _ _ _ _).1 extension).2.2.2
  refine ⟨pCut, r, cutCode, below, decisions, lowerRow, lowerA, rCode,
    lifted, extension, retained, ?_⟩
  rw [exactCut]
  exact rCode.symm






theorem semanticStructuralSuccessor_represented_or_fresh_oai
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u}),
      ∀ (rowAction : a.actionGraph c t ∈ M.sets)
        (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
        (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
        (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
        (supports : supportBasisCode b t d.principalFix ∈ M.sets)
        (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
        (valid1 : ∀ z ∈ T, IsName c.pairEmpty z) (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
        (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
        (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
        (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
          HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
        (topMem : rowTop ∈ c.carrier)
        (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
        (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
        (ordinal : ordinalSetProperty stages)
        (trace : OrdinalRecursionTrace (fun level prior stage => stage =
          M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
            t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
            (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
        (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
      let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
        (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 ordinal trace
      let cutOrdinal := ordinalSetProperty_member ordinal member
      let subset := (And.left ordinal) alpha member
      let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
        (M.natSetCode_mem separation infinite 2)
      ∀ {row A : ZFSet.{u}},
      ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
        (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation Q
      let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
        cutOrdinal carrier T valid1
      let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite)
        valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace
        (M.transitive hs member) cutOrdinal subset
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices act lower b d alpha T T2 valid →
      ∀ u : Name lower, ∀ (hu : u.val ∈ T),
      ∃ pCut r : SetMembers Q,
        lower.encode pCut = ZFSet.pair row (assignmentCut
          (refinementDataHistoryLevels stages packed T) alpha A) ∧ r ≤ pCut ∧
        ∃ lowerRow lowerA : ZFSet.{u}, lower.encode r = ZFSet.pair lowerRow lowerA ∧
          let liftedA := assignmentSplice (refinementDataHistoryLevels stages packed T) alpha lowerA A
          ZFSet.pair lowerRow liftedA ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
          ZFSet.pair (ZFSet.pair lowerRow liftedA) (ZFSet.pair row A) ∈
            M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
          A ⊆ liftedA ∧
          ZFSet.pair lowerRow (assignmentCut (refinementDataHistoryLevels stages packed T) alpha liftedA) =
            lower.encode r ∧
          (ZFSet.pair lowerRow liftedA ∈ M.representedDomainConditions lower
            (M.refinementHistoryForcing c.carrier T stages packed)
            (refinementDataHistoryLevels stages packed T) alpha T valid
            (refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
            U Rc ⟨u, M.transitive hT hu⟩ ∨
          (Name.ForcesMem r u U.val ∧
            ∀ v w : Name lower, v.val ∈ T → w.val ∈ T →
              stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
                U.val.val Rf.val.val Rc.val.val) v.val w.val ∈ A →
              ∀ q, q ≤ r → ¬ Name.ForcesEq q (Name.refinementClass T valid Rc.val u)
                (Name.refinementClass T valid Rc.val v))) := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows stages history hs hh ordinal trace
    alpha member row A condition
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX
    (M.natSetCode_mem separation infinite 2)
  let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX
    (M.natSetCode_mem separation infinite 2)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  intro C E U Rf Rc idx u hu
  obtain ⟨pCut, r, cutCode, below, decisions, lowerRow, lowerA, rCode,
      lifted, extension, retained, exactCut⟩ :=
    M.semanticStructuralSuccessor_domain_decisions_lift t b d base directed
      pairing unions powers separation collection infinite choice X hX a T T2 rowTop
      rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
      valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows stages history hs hh ordinal trace alpha member condition C E U Rf Rc idx u hu
  refine ⟨pCut, r, cutCode, below, lowerRow, lowerA, rCode, lifted, extension, retained, exactCut, ?_⟩
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hh trace (M.transitive hs member) cutOrdinal subset
  have entry := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
  have fields : ∀ j, M.refinementLevelFormulaData act lower b d alpha T T2 valid j ∈ M.sets :=
    M.refinementFormulaDataCode_fields_mem _ (M.transitive
      (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion entry))
  have lowerCarrier : lower.carrier ∈ M.sets := fields 7
  have lowerOrder : lower.conditionOrder ∈ M.sets := fields 8
  have hUpper := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked
    (M.omega_mem separation infinite)
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hs hPacked hT
  have hIdx := M.refinementIndexCode_mem pairing (M.transitive hs member)
    (M.transitive nodes (b.encode_mem C)) (M.transitive nodes (b.encode_mem E)) U.property Rf.property Rc.property
  have exactEntry := M.pair_mem_representedDomainConditions lower pairing unions powers separation collection
    lowerCarrier lowerOrder hUpper hLevels (M.transitive hs member) hT valid hIdx U Rc
    ⟨u, M.transitive hT hu⟩ lowerRow
    (assignmentSplice (refinementDataHistoryLevels stages packed T) alpha lowerA A) r exactCut.symm
  rcases decisions with inactive | ⟨active, reuse | fresh⟩
  · exact Or.inl (exactEntry.2 ⟨lifted, Or.inl inactive⟩)
  · obtain ⟨v, w, hv, hw, literal, equal⟩ := reuse
    exact Or.inl (exactEntry.2 ⟨lifted, Or.inr ⟨active, v, w, hv, hw, retained literal, equal⟩⟩)
  · exact Or.inr ⟨active, fresh⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_or_fresh_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralSuccessor_represented_or_fresh_oai.{u}
