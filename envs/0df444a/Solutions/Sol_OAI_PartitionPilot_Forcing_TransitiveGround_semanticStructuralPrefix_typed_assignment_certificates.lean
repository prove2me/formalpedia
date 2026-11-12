-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_typed_assignment_certificates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:33:46.807944+00:00
-- url     : https://prove2.me/submissions/849540af-15a8-440e-b560-b011c73742cc

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPrincipalNiceSupportCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem pair_mem_niceSupportRelation (i : I) (tau : ZFSet.{u}) :
    ZFSet.pair (b.encode i) tau ∈ M.niceSupportRelation a s b T K ↔
      tau ∈ M.sets ∧ NiceNameCode a s T (K i) tau := by
  rw [niceSupportRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, sigma, eq, candidate⟩
    obtain ⟨keys, rfl⟩ := ZFSet.pair_inj.1 eq
    have same := b.injective keys
    subst j
    exact (M.mem_niceNameCandidates a s T (K i) tau).1 candidate
  · intro code
    exact ⟨ZFSet.pair_mem_prod.2 ⟨b.encode_mem i,
      (M.mem_niceSupportNameCodes a s T K tau).2 ⟨code.1, i, code.2⟩⟩,
      i, tau, rfl, (M.mem_niceNameCandidates a s T (K i) tau).2 code⟩

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparationForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (K : I → Subgroup G)

omit [OrderTop P] in
private theorem rawForces_pair_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (phi : SetFormula 2) (p : P) (z tau : (M.nameDomain s).names) :
    stageOneRawForces M s.carrier s.conditionOrder (s.encode p) phi ![z.val.val, tau.val.val] ↔
      Forces (M.nameDomain s) phi ![z, tau] p := by
  have fields : (fun j : Fin 2 => (![z, tau] j).val.val) = ![z.val.val, tau.val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  have translated := M.stageOneRawForces_iff s pairing unions powers separation collection
    carrier order phi p ![z, tau]
  rw [fields] at translated
  exact translated

theorem preparationForcingCode_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (T N : ZFSet.{u}) (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (namesGround : N ∈ M.sets) (valid : ∀ tau ∈ N, IsName s tau)
    (z : (M.nameDomain s).names) (F f : ZFSet.{u})
    (range : f ⊆ ZFSet.prod b.carrier N) (p : P) :
    PreparationForcingCode M s.carrier s.conditionOrder (s.encode p) b.carrier
      (M.niceVisibilityGraph a s b T K) z.val.val F f ↔
      M.DecidesVisibilityProfile a s b K T F z.val p ∧
      ∀ v (tau : Name s), tau.val ∈ N → ZFSet.pair v tau.val ∈ f →
        Name.ForcesEq p z.val tau := by
  let vis (v : I) : (M.nameDomain s).names :=
    ⟨M.niceVisibilityName a s T (K v),
      M.pair_right (M.transitive graphGround
        ((M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl))⟩
  have memForces (v : I) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode p)
        (.mem 0 1 : SetFormula 2) ![z.val.val, (vis v).val.val] ↔
        Name.ForcesMem p z.val (vis v).val :=
    rawForces_pair_iff M s pairing unions powers separation collection carrier order
      (.mem 0 1 : SetFormula 2) p z (vis v)
  have negForces (v : I) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode p)
        (.neg (.mem 0 1) : SetFormula 2) ![z.val.val, (vis v).val.val] ↔
        ∀ q : P, q ≤ p → ¬ Name.ForcesMem q z.val (vis v).val :=
    rawForces_pair_iff M s pairing unions powers separation collection carrier order
      (.neg (.mem 0 1) : SetFormula 2) p z (vis v)
  have eqForces (tau : (M.nameDomain s).names) :
      stageOneRawForces M s.carrier s.conditionOrder (s.encode p)
        (.equal 0 1 : SetFormula 2) ![z.val.val, tau.val.val] ↔
        Name.ForcesEq p z.val tau.val :=
    rawForces_pair_iff M s pairing unions powers separation collection carrier order
      (.equal 0 1 : SetFormula 2) p z tau
  constructor
  · rintro ⟨profile, equalities⟩
    constructor
    · intro v
      have decisions := profile (b.encode v) (vis v).val.val
        ((M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl) (b.encode_mem v)
      exact ⟨fun yes => (memForces v).1 (decisions.1 yes),
        fun no => (negForces v).1 (decisions.2 no)⟩
    · intro v tau htau entry
      exact (eqForces ⟨tau, M.transitive namesGround htau⟩).1 (equalities v tau.val entry)
  · rintro ⟨profile, equalities⟩
    constructor
    · intro v V entry hv
      obtain ⟨i, rfl⟩ := (b.mem_carrier v).1 hv
      have eq := (M.pair_mem_niceVisibilityGraph a s b T K i V).1 entry
      subst V
      exact ⟨fun yes => (memForces i).2 ((profile i).1 yes),
        fun no => (negForces i).2 ((profile i).2 no)⟩
    · intro v tau entry
      have htau := (ZFSet.pair_mem_prod.1 (range entry)).2
      let name : (M.nameDomain s).names := ⟨⟨tau, valid tau htau⟩, M.transitive namesGround htau⟩
      exact (eqForces name).2 (equalities v name.val htau entry)

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




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem storedPreparationRequests_typed {G P L : Type u}
    [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
    (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (A : ZFSet.{u}) :
    M.storedPreparationRequests A (M.refinementLevelFormulaData a s b d level T T2 valid) =
      let selected := assignmentOnIndices (M.niceRefinementIndices a s b d level T T2 valid) T A
      let graphs := M.niceAssignmentClassGraphs a s b d level T T2 valid selected
      relationImage selected (M.groundRelations T s.carrier) (graphs 0) ∪
        relationImage selected (M.groundRelations T s.carrier) (graphs 1) := rfl

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundVisibilitySupportIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem mem_visibilitySupportIncidence
    (nodes names visibility top z : ZFSet.{u}) :
    z ∈ visibilitySupportIncidence nodes names visibility top ↔
      ∃ v ∈ nodes, ∃ tau ∈ names, z = ZFSet.pair v tau ∧
        ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V := by
  rw [visibilitySupportIncidence, ZFSet.mem_sep]
  constructor
  · rintro ⟨bound, v, tau, rfl, V, entry, member⟩
    exact ⟨v, (ZFSet.pair_mem_prod.1 bound).1,
      tau, (ZFSet.pair_mem_prod.1 bound).2, rfl, V, entry, member⟩
  · rintro ⟨v, hv, tau, htau, rfl, V, entry, member⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, htau⟩, v, tau, rfl, V, entry, member⟩

theorem pair_mem_visibilitySupportIncidence
    (nodes names visibility top v tau : ZFSet.{u}) :
    ZFSet.pair v tau ∈ visibilitySupportIncidence nodes names visibility top ↔
      v ∈ nodes ∧ tau ∈ names ∧
        ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V := by
  rw [mem_visibilitySupportIncidence]
  constructor
  · rintro ⟨v', hv, tau', htau, equal, witness⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hv, htau, witness⟩
  · rintro ⟨hv, htau, witness⟩
    exact ⟨v, hv, tau, htau, rfl, witness⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

variable {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem visibilitySupportIncidence_candidates (v : I) (tau : ZFSet.{u}) :
    ZFSet.pair (b.encode v) tau ∈ visibilitySupportIncidence b.carrier
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T K) (s.encode ⊤) ↔
      tau ∈ M.sets ∧ NiceNameCode a s T (K v) tau := by
  rw [pair_mem_visibilitySupportIncidence]
  constructor
  · rintro ⟨_, _, V, entry, member⟩
    have equal := (M.pair_mem_niceVisibilityGraph a s b T K v V).1 entry
    rw [equal, M.niceVisibilityName_code] at member
    exact (M.mem_niceNameCandidates a s T (K v) tau).1
      (ZFSet.pair_mem_prod.1 member).1
  · intro code
    have member := (M.mem_niceNameCandidates a s T (K v) tau).2 code
    refine ⟨b.encode_mem v, M.niceNameCandidates_subset a s T (K v) member,
      (M.niceVisibilityName a s T (K v)).val,
      (M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl, ?_⟩
    rw [M.niceVisibilityName_code]
    exact ZFSet.pair_mem_prod.2 ⟨member, ZFSet.mem_singleton.2 rfl⟩

theorem visibilitySupportIncidence_eq_niceSupportRelation :
    visibilitySupportIncidence b.carrier (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T K) (s.encode ⊤) =
      M.niceSupportRelation a s b T K := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨v, hv, tau, _, rfl, _⟩ :=
      (mem_visibilitySupportIncidence _ _ _ _ z).1 member
    obtain ⟨i, rfl⟩ := (b.mem_carrier v).1 hv
    exact (M.pair_mem_niceSupportRelation a s b T K i tau).2
      ((M.visibilitySupportIncidence_candidates a s b T K i tau).1 member)
  · intro member
    obtain ⟨_, i, tau, rfl, _⟩ := ZFSet.mem_sep.1 member
    exact (M.visibilitySupportIncidence_candidates a s b T K i tau).2
      ((M.pair_mem_niceSupportRelation a s b T K i tau).1 member)

end PartitionPilot.Forcing.TransitiveGround

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




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedAlignedReferenceCollisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem preparedCertificateCode_typed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (hT : T ∈ M.sets) (validT : ∀ tau ∈ T, IsName s tau)
    (graphGround : M.niceVisibilityGraph a s b T K ∈ M.sets)
    (nodeOrder meet omega : ZFSet.{u}) (z : (M.nameDomain s).names) (p : P)
    (F B f e names : ZFSet.{u})
    (code : PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier nodeOrder meet (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T K) (s.encode ⊤) omega z.val.val F B f e names) :
    M.TypedPreparedCertificate a s b T K nodeOrder meet omega z.val p F B f e names := by
  obtain ⟨filter, basis, nonempty, sync, incidence, raw⟩ := code
  have supported : f ⊆ M.niceSupportRelation a s b T K := by
    intro entry member
    obtain ⟨v, _, tau, _, rfl⟩ := ZFSet.mem_prod.1 (sync.1.1 member)
    rw [← M.visibilitySupportIncidence_eq_niceSupportRelation a s b T K]
    exact incidence v tau member
  have niceRange : f ⊆ ZFSet.prod B (M.niceSupportNameCodes a s T K) := by
    intro entry member
    obtain ⟨v, hv, tau, _, rfl⟩ := ZFSet.mem_prod.1 (sync.1.1 member)
    have nice := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 (supported member)).1
    exact ZFSet.pair_mem_prod.2 ⟨hv, nice.2⟩
  have namesRange : names ⊆ ZFSet.prod omega (M.niceSupportNameCodes a s T K) := by
    intro entry member
    obtain ⟨n, hn, tau, _, rfl⟩ := ZFSet.mem_prod.1 (sync.2.2.1.1 member)
    obtain ⟨v, nv, _⟩ := sync.2.1.2 n hn
    have vt := sync.2.2.2.2.1 n hn v tau nv member
    exact ZFSet.pair_mem_prod.2 ⟨hn, (ZFSet.pair_mem_prod.1 (niceRange vt)).2⟩
  have narrowed : SynchronizedEnumerationCode omega
      (M.niceSupportNameCodes a s T K) B f e names :=
    ⟨⟨niceRange, sync.1.2⟩, sync.2.1, ⟨namesRange, sync.2.2.1.2⟩,
      sync.2.2.2.1, sync.2.2.2.2.1, sync.2.2.2.2.2⟩
  have range : f ⊆ ZFSet.prod b.carrier (M.groundRelations T s.carrier) := by
    intro entry member
    obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (sync.1.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨filter.subset (basis.1 hv), htau⟩
  have valid : ∀ tau ∈ M.groundRelations T s.carrier, IsName s tau := by
    intro tau member
    exact Name.isName_of_subset validT ((M.mem_groundRelations T s.carrier tau).1 member).2
  have forcing := (M.preparationForcingCode_iff a s b K pairing unions powers separation
    collection carrier order T (M.groundRelations T s.carrier) graphGround
    (M.groundRelations_mem pairing unions powers separation hT carrier) valid z F f range p).1 raw
  refine ⟨filter, basis, nonempty, narrowed, supported, forcing.1, ?_⟩
  intro v _ tau _ entry
  exact forcing.2 v tau (ZFSet.pair_mem_prod.1 (sync.1.1 entry)).2 entry

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedCopyCollisions
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

theorem semanticStructuralPrefix_preparationEnvironment (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed) :
    StoredPreparationEnvironment M fields := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  have exactStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same : fields = M.refinementLevelFormulaData act lower b d alpha T T2 valid :=
    refinementFormulaDataCode_injective ((run).carriers.data.function.unique stored exactStored)
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have members : ∀ j, fields j ∈ M.sets := M.refinementFormulaDataCode_fields_mem fields
    (M.transitive (M.union_mem unions (M.union_mem unions hPacked)) (pair_second_mem_doubleUnion stored))
  refine ⟨?_, members, ?_, ?_⟩
  · rw [same]
    exact lower.conditionOrder_code
  · rw [same]
    intro z hz
    exact Name.isName_of_subset valid ((M.mem_groundRelations T lower.carrier z).1 hz).2
  · rw [same]
    intro v V entry _
    obtain ⟨i, equal⟩ := (M.mem_niceVisibilityGraph act lower b T d.principalFix
      (ZFSet.pair v V)).1 entry
    have value := (ZFSet.pair_inj.1 equal).2
    rw [value]
    exact (M.niceVisibilityName act lower T (d.principalFix i)).property

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

theorem semanticStructuralPrefix_assignmentClassRequest_mem
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
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ fields 0 →
      ∀ (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∀ side : Fin 2,
      let request := Name.refinementClass T valid
        (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
        (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
      request.val ∈ M.storedPreparationRequests A fields ∧ request.val ∈ M.sets ∧
      IsName lower request.val ∧
      HereditarilySymmetric act lower (d.principalSupportFamily base directed) request ∧
      ∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} request ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let I := M.niceRefinementIndices act lower b d alpha T T2 valid
  let selected := assignmentOnIndices I T A
  let graphs := M.niceAssignmentClassGraphs act lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
  obtain ⟨_hSelected, _smallSelected, functions, hJ, _smallJ, validJ, facts, entries⟩ :=
    M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
      nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
      symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice condition
  dsimp only
  intro C E U Rf Rc idx u w hu hw inA side
  let request := Name.refinementClass T valid
    (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
    (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
  let assignment := stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
    U.val.val Rf.val.val Rc.val.val) u.val w.val
  have inSelected : assignment ∈ selected :=
    (mem_assignmentOnIndices I T A assignment).2 ⟨inA,
      (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨idx, hu, hw⟩⟩
  have edge : ZFSet.pair assignment request.val ∈ graphs side :=
    (entries C E U Rf Rc idx u w hu hw inA side request.val).2 rfl
  have bounded : request.val ∈ bound :=
    (ZFSet.pair_mem_prod.1 ((functions side).2.1 edge)).2
  have image : request.val ∈ relationImage selected bound (graphs side) :=
    (mem_relationImage selected bound (graphs side) request.val).2
      ⟨bounded, assignment, inSelected, edge⟩
  have inJ : request.val ∈ J := by
    have sideCases : side = 0 ∨ side = 1 := by omega
    rcases sideCases with zero | one
    · exact ZFSet.mem_union.2 (Or.inl (zero ▸ image))
    · exact ZFSet.mem_union.2 (Or.inr (one ▸ image))
  have actual : request.val ∈ M.storedPreparationRequests A
      (M.refinementLevelFormulaData act lower b d alpha T T2 valid) := by
    rw [M.storedPreparationRequests_typed]
    exact inJ
  exact ⟨actual, M.transitive hJ inJ, validJ request.val inJ, facts request inJ⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
private theorem selectedFamilyCertificate_p0
    (M : TransitiveGround.{u})
    {P order q nodes nodeOrder meet N visibility top omega J W k enumerations z : ZFSet.{u}}
    (family : PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top
      omega J (M.supportedEqualityCertificateBound nodes W)
      (M.synchronizedEnumerationBound nodes W) k enumerations)
    (member : z ∈ J) :
    ∃ F B f e names, F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
      e ∈ M.sets ∧ names ∈ M.sets ∧
      ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
      ZFSet.pair z (ZFSet.pair e names) ∈ enumerations ∧
      PreparedCertificateCode M P order q nodes nodeOrder meet N visibility top omega z F B f e names := by
  obtain ⟨value, edge, _unique⟩ := family.1.2 z member
  have bounded := (ZFSet.pair_mem_prod.1 (family.1.1 edge)).2
  obtain ⟨F, hF, tail, hTail, rfl⟩ := ZFSet.mem_prod.1 bounded
  obtain ⟨B, hB, f, hf, rfl⟩ := ZFSet.mem_prod.1 hTail
  obtain ⟨value, enumerated, _unique⟩ := family.2.1.2 z member
  have bounded := (ZFSet.pair_mem_prod.1 (family.2.1.1 enumerated)).2
  obtain ⟨e, he, names, hn, rfl⟩ := ZFSet.mem_prod.1 bounded
  exact ⟨F, B, f, e, names, ((M.mem_groundPower nodes F).1 hF).1,
    ((M.mem_groundSmallSubsets nodes ZFSet.omega B).1 hB).1,
    ((M.mem_groundRelations nodes W f).1 hf).1,
    ((M.mem_groundRelations ZFSet.omega nodes e).1 he).1,
    ((M.mem_groundRelations ZFSet.omega W names).1 hn).1, edge, enumerated,
    family.2.2 z F B f e names edge enumerated⟩

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

theorem semanticStructuralPrefix_prepared_assignment_certificates
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ fields 0 →
      ∀ (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ upperQ ∧
        sourceA ⊆ A ∧
      ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q ∈ fields 7,
        ZFSet.pair (ZFSet.pair row A) q ∈ rowAssignmentCutGraph upperQ (fields 7)
          (refinementDataHistoryLevels stages packed T) alpha ∧
        PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
          (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
          ZFSet.omega (M.storedPreparationRequests sourceA fields)
          (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
          (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations ∧
      ∀ side : Fin 2,
        let request := Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
        request.val ∈ M.storedPreparationRequests sourceA fields ∧ request.val ∈ M.sets ∧
        IsName lower request.val ∧
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) request ∧
        (∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} request ⊆
          Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
        ∃ F B f e names, F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
          e ∈ M.sets ∧ names ∈ M.sets ∧
          ZFSet.pair request.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
          ZFSet.pair request.val (ZFSet.pair e names) ∈ enumerations ∧
          PreparedCertificateCode M (fields 7) (fields 8) q (fields 10) (fields 11)
            (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
            ZFSet.omega request.val F B f e names := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  dsimp only
  intro C E U Rf Rc idx u w hu hw inA
  let index := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let x := stageOneAssignment index u.val w.val
  obtain ⟨beta, _hBeta, other, otherStored, terms, _nodeCarrier, _meet, _environment,
      sourceRow, sourceA, hSourceA, sourceCondition, sourceSubset, selected,
      k, hk, enumerations, he, q, hq, cut, family⟩ := prepared row A rfl x inA
  have inSource := (mem_assignmentOnIndices (other 0) T sourceA x).1 selected
  have indexOther := (stageOneAssignment_mem_assignments (other 0) T index u.val w.val).1 inSource.2
  have alphaEdge := (run).carriers.data.coverage alpha member fields stored index idx
    u.val hu w.val hw
  have betaEdge := (run).carriers.data.coverage beta _hBeta other otherStored index indexOther.1
    u.val (terms.symm ▸ hu) w.val (terms.symm ▸ hw)
  have equal : beta = alpha := by
    have fn := (run).carriers.data.levels_function
    have hx := (ZFSet.pair_mem_prod.1 (fn.1 alphaEdge)).1
    obtain ⟨_, _, unique⟩ := fn.2 x hx
    exact (unique _ betaEdge).trans (unique _ alphaEdge).symm
  subst beta
  have same : other = fields := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique otherStored stored)
  subst other
  refine ⟨sourceRow, sourceA, hSourceA, sourceCondition, sourceSubset, k, hk,
    enumerations, he, q, hq, cut, family, ?_⟩
  intro side
  let request := Name.refinementClass T valid
    (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
    (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
  have facts := M.semanticStructuralPrefix_assignmentClassRequest_mem c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice
    sourceCondition C E U Rf Rc idx u w hu hw inSource.1 side
  exact ⟨facts.1, facts.2.1, facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2,
    selectedFamilyCertificate_p0 M family facts.1⟩

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

theorem semanticStructuralPrefix_typed_assignment_certificates_oai
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
    let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    ∀ (C E : L) (U Rf Rc : (M.nameDomain lower).names),
      refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ fields 0 →
      ∀ (u w : Name lower), u.val ∈ T → w.val ∈ T →
      stageOneAssignment (refinementIndexCode alpha (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val w.val ∈ A →
      ∃ sourceRow sourceA, sourceA ∈ M.sets ∧ ZFSet.pair sourceRow sourceA ∈ upperQ ∧
        sourceA ⊆ A ∧
      ∃ k ∈ M.sets, ∃ enumerations ∈ M.sets, ∃ q : SetMembers Q,
        ZFSet.pair (ZFSet.pair row A) (lower.encode q) ∈ rowAssignmentCutGraph upperQ (fields 7)
          (refinementDataHistoryLevels stages packed T) alpha ∧
        PreparedCertificateFamilyCode M (fields 7) (fields 8) (lower.encode q) (fields 10) (fields 11)
          (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
          ZFSet.omega (M.storedPreparationRequests sourceA fields)
          (M.supportedEqualityCertificateBound b.carrier (M.groundRelations T upperQ))
          (M.synchronizedEnumerationBound b.carrier (M.groundRelations T upperQ)) k enumerations ∧
      ∀ side : Fin 2,
        let request := Name.refinementClass T valid
          (Fin.cases (motive := fun _ => Name lower) Rc.val (fun _ => Rf.val) side)
          (Fin.cases (motive := fun _ => Name lower) u (fun _ => w) side)
        request.val ∈ M.storedPreparationRequests sourceA fields ∧ request.val ∈ M.sets ∧
        IsName lower request.val ∧
        HereditarilySymmetric act lower (d.principalSupportFamily base directed) request ∧
        (∀ H : ConditionFilter (SetMembers Q), Name.eval {p | H.mem p} request ⊆
          Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)) ∧
        ∃ F B f e names, F ∈ M.sets ∧ B ∈ M.sets ∧ f ∈ M.sets ∧
          e ∈ M.sets ∧ names ∈ M.sets ∧
          ZFSet.pair request.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
          ZFSet.pair request.val (ZFSet.pair e names) ∈ enumerations ∧
          PreparedCertificateCode M (fields 7) (fields 8) (lower.encode q) (fields 10) (fields 11)
            (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
            ZFSet.omega request.val F B f e names ∧
          M.TypedPreparedCertificate act lower b T d.principalFix (fields 11)
            (canonicalMeetGraph (fields 10) (fields 11)) ZFSet.omega request q F B f e names := by
  let instLowerHistoryOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let instLowerHistoryTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have stored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have environment := M.semanticStructuralPrefix_preparationEnvironment c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member fields stored
  dsimp only
  intro C E U Rf Rc idx u w hu hw inA
  obtain ⟨sourceRow, sourceA, hSourceA, sourceCondition, sourceSubset,
      k, hk, enumerations, he, rawq, hq, cut, family, selected⟩ :=
    M.semanticStructuralPrefix_prepared_assignment_certificates c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member infinite choice prepared C E U Rf Rc idx u w hu hw inA
  obtain ⟨q, rfl⟩ := (lower.mem_carrier rawq).1 hq
  refine ⟨sourceRow, sourceA, hSourceA, sourceCondition, sourceSubset,
    k, hk, enumerations, he, q, cut, family, ?_⟩
  intro side
  obtain ⟨requestMember, requestGround, requestValid, requestHS, requestSubset,
    F, B, f, e, names, hF, hB, hf, he, hn, kEdge, enumEdge, rawCode⟩ := selected side
  refine ⟨requestMember, requestGround, requestValid, requestHS, requestSubset,
    F, B, f, e, names, hF, hB, hf, he, hn, kEdge, enumEdge, rawCode, ?_⟩
  exact M.preparedCertificateCode_typed act lower b T d.principalFix pairing unions powers
    separation collection (environment.ground 7) (environment.ground 8) hT valid
    (environment.ground 13) (fields 11) (canonicalMeetGraph (fields 10) (fields 11))
    ZFSet.omega ⟨_, requestGround⟩ q F B f e names rawCode

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_typed_assignment_certificates_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticStructuralPrefix_typed_assignment_certificates_oai.{u}
