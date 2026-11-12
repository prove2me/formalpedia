-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:25:11.177885+00:00
-- url     : https://prove2.me/submissions/b0056ca1-5e7f-4f32-b353-6db54ce0e90d

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_exists_forcedSupportedCertificateFamily

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



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SupportedCertificateRelations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing
universe u

theorem pair_mem_supportedCertificateRelation
    (J PF PB WF nodes N order R inputEval niceEval visibilityEval j F B f : ZFSet.{u}) :
    ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈
        supportedCertificateRelation J PF PB WF nodes N order R inputEval niceEval visibilityEval ↔
      j ∈ J ∧ F ∈ PF ∧ B ∈ PB ∧ f ∈ WF ∧
        ∃ value, ZFSet.pair j value ∈ inputEval ∧
          SupportedEqualityCertificate nodes N order R niceEval visibilityEval value F B f := by
  rw [supportedCertificateRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j', hj, F', hF, B', hB, f', hf, equal, value, evaluated, certificate⟩
    have outer := ZFSet.pair_inj.1 equal
    have middle := ZFSet.pair_inj.1 outer.2
    have inner := ZFSet.pair_inj.1 middle.2
    cases outer.1
    cases middle.1
    cases inner.1
    cases inner.2
    exact ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
  · rintro ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hj, ZFSet.pair_mem_prod.2
      ⟨hF, ZFSet.pair_mem_prod.2 ⟨hB, hf⟩⟩⟩,
      j, hj, F, hF, B, hB, f, hf, rfl, value, evaluated, certificate⟩

end PartitionPilot.Forcing

end

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



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PreparedCertificateCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

theorem truth_synchronizedEnumerationFormula {n} (omega N B f e names : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (synchronizedEnumerationFormula omega N B f e names) env ↔
      SynchronizedEnumerationCode (env omega) (env N) (env B) (env f) (env e) (env names) := by
  simp only [synchronizedEnumerationFormula, Truth, truth_functionFormula,
    truth_exMem, truth_pairMembershipFormula, truth_imp]
  change (ZFSet.IsFunc (env B) (env N) (env f) ∧
    ZFSet.IsFunc (env omega) (env B) (env e) ∧
    ZFSet.IsFunc (env omega) (env N) (env names) ∧
    (∀ v ∈ env B, ∃ n ∈ env omega, ZFSet.pair n v ∈ env e) ∧
    (∀ n ∈ env omega, ∀ v ∈ env B, ∀ tau ∈ env N, ZFSet.pair n v ∈ env e →
      ZFSet.pair n tau ∈ env names → ZFSet.pair v tau ∈ env f) ∧
    (∀ n ∈ env omega, ∀ v ∈ env B, ∀ tau ∈ env N, ZFSet.pair n v ∈ env e →
      ZFSet.pair v tau ∈ env f → ZFSet.pair n tau ∈ env names)) ↔ _
  constructor
  · rintro ⟨ff, ef, nf, onto, forward, backward⟩
    refine ⟨ff, ef, nf, onto, ?_, ?_⟩
    · intro n hn v tau nv nt
      exact forward n hn v (ZFSet.pair_mem_prod.1 (ef.1 nv)).2
        tau (ZFSet.pair_mem_prod.1 (nf.1 nt)).2 nv nt
    · intro n hn v tau nv vt
      exact backward n hn v (ZFSet.pair_mem_prod.1 (ef.1 nv)).2
        tau (ZFSet.pair_mem_prod.1 (ff.1 vt)).2 nv vt
  · rintro ⟨ff, ef, nf, onto, forward, backward⟩
    exact ⟨ff, ef, nf, onto, fun n hn v _ tau _ => forward n hn v tau,
      fun n hn v _ tau _ => backward n hn v tau⟩

theorem truth_certificateEnumerationEntryFormula {n} (entry J E Names omega N k : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (certificateEnumerationEntryFormula entry J E Names omega N k) env ↔
      ∃ j ∈ env J, ∃ e ∈ env E, ∃ names ∈ env Names,
        env entry = ZFSet.pair j (ZFSet.pair e names) ∧
        ∃ F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ env k ∧
          SynchronizedEnumerationCode (env omega) (env N) B f e names := by
  simp only [certificateEnumerationEntryFormula, truth_exPairFields, truth_exGraphFields,
    Truth, truth_synchronizedEnumerationFormula]
  change (∃ j pair, env entry = ZFSet.pair j pair ∧
    ∃ e names, pair = ZFSet.pair e names ∧
    ∃ j' certificate, ZFSet.pair j' certificate ∈ env k ∧
    ∃ F tail, certificate = ZFSet.pair F tail ∧
    ∃ B f, tail = ZFSet.pair B f ∧ j' = j ∧
      j ∈ env J ∧ e ∈ env E ∧ names ∈ env Names ∧
      SynchronizedEnumerationCode (env omega) (env N) B f e names) ↔ _
  constructor
  · rintro ⟨j, pair, eq, e, names, rfl, j', certificate, stored,
      F, tail, rfl, B, f, rfl, rfl, hj, he, hn, code⟩
    exact ⟨j', hj, e, he, names, hn, eq, F, B, f, stored, code⟩
  · rintro ⟨j, hj, e, he, names, hn, eq, F, B, f, stored, code⟩
    exact ⟨j, _, eq, e, names, rfl, j, _, stored, F, _, rfl,
      B, f, rfl, rfl, hj, he, hn, code⟩

end BoundedFormula

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_supportedEqualityCertificateBound (nodes N F B f : ZFSet.{u}) :
    ZFSet.pair F (ZFSet.pair B f) ∈ M.supportedEqualityCertificateBound nodes N ↔
      (F ∈ M.sets ∧ F ⊆ nodes) ∧
      (B ∈ M.sets ∧ B ⊆ nodes ∧ M.groundEmbeddable B ZFSet.omega) ∧
      (f ∈ M.sets ∧ f ⊆ ZFSet.prod nodes N) := by
  rw [supportedEqualityCertificateBound, ZFSet.pair_mem_prod, ZFSet.pair_mem_prod,
    M.mem_groundPower, M.mem_groundSmallSubsets, M.mem_groundRelations]

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionEnumerations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundFunction_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {B N f : ZFSet.{u}} (hB : B ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets)
    (nonempty : B.Nonempty) (small : M.groundEmbeddable B ZFSet.omega)
    (function : ZFSet.IsFunc B N f) :
    ∃ e ∈ M.sets, ∃ names ∈ M.sets,
      ZFSet.IsFunc ZFSet.omega B e ∧ ZFSet.IsFunc ZFSet.omega N names ∧
      (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
      (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
        ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
      (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
        ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  obtain ⟨e, he, enumeration, onto⟩ := M.groundCountable_enumeration
    pairing unions powers separation infinite hB nonempty small
  let names := relationCompose ZFSet.omega B N e f
  have namesGround := M.relationCompose_mem pairing unions powers separation
    (M.omega_mem separation infinite) hB hN he hf
  have namesFunction : ZFSet.IsFunc ZFSet.omega N names :=
    relationCompose_function_of_subset enumeration function (fun _ member => member)
  refine ⟨e, he, names, namesGround, enumeration, namesFunction, onto, ?_, ?_⟩
  · intro n hn v tau nv nt
    obtain ⟨_, _, w, _, nw, wt⟩ := (pair_mem_relationCompose _ _ _ _ _ n tau).1 nt
    obtain ⟨chosen, _, unique⟩ := enumeration.2 n hn
    have equal : w = v := (unique w nw).trans (unique v nv).symm
    exact equal ▸ wt
  · intro n hn v tau nv vt
    have bound := ZFSet.pair_mem_prod.1 (function.1 vt)
    exact (pair_mem_relationCompose _ _ _ _ _ n tau).2 ⟨hn, bound.2, v, bound.1, nv, vt⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCertificateProfileImageFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem synchronizedEnumerationBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) : M.synchronizedEnumerationBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation
    (M.groundRelations_mem pairing unions powers separation omega hNodes)
    (M.groundRelations_mem pairing unions powers separation omega hN)

theorem pair_mem_certificateEnumerationRelation (J nodes N k j e names : ZFSet.{u}) :
    ZFSet.pair j (ZFSet.pair e names) ∈ M.certificateEnumerationRelation J nodes N k ↔
      j ∈ J ∧ e ∈ M.groundRelations ZFSet.omega nodes ∧
      names ∈ M.groundRelations ZFSet.omega N ∧
      ∃ F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k ∧
        SynchronizedEnumerationCode ZFSet.omega N B f e names := by
  rw [certificateEnumerationRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j', hj, e', he, names', hn, eq, F, B, f, stored, code⟩
    obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 tail
    exact ⟨hj, he, hn, F, B, f, stored, code⟩
  · rintro ⟨hj, he, hn, F, B, f, stored, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hj, ZFSet.pair_mem_prod.2 ⟨he, hn⟩⟩,
      j, hj, e, he, names, hn, rfl, F, B, f, stored, code⟩

theorem certificateEnumerationRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J nodes N k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hN : N ∈ M.sets) (hk : k ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.certificateEnumerationRelation J nodes N k ∈ M.sets := by
  have hE := M.groundRelations_mem pairing unions powers separation omega hNodes
  have hNames := M.groundRelations_mem pairing unions powers separation omega hN
  let params := extend J (extend (M.groundRelations ZFSet.omega nodes)
    (extend (M.groundRelations ZFSet.omega N) (extend ZFSet.omega
      (extend N (extend k Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.certificateEnumerationEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hJ (Fin.cases hE (Fin.cases hNames (Fin.cases omega
      (Fin.cases hN (Fin.cases hk (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hJ
      (M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hN omega))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.certificateEnumerationEntryFormula 0 1 2 3 4 5 6)
      (extend z params)) (ZFSet.prod J (M.synchronizedEnumerationBound nodes N)) =
      M.certificateEnumerationRelation J nodes N k := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, certificateEnumerationRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_certificateEnumerationEntryFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

theorem exists_supportedCertificateEnumerations
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J nodes N k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hN : N ∈ M.sets) (hk : k ∈ M.sets)
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k)
    (certificates : ∀ j F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      B.Nonempty ∧ ZFSet.IsFunc B N f) :
    ∃ enumerations ∈ M.sets,
      ZFSet.IsFunc J (M.synchronizedEnumerationBound nodes N) enumerations ∧
      enumerations ⊆ M.certificateEnumerationRelation J nodes N k ∧
      ∀ j F B f e names, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
        ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
        SynchronizedEnumerationCode ZFSet.omega N B f e names := by
  have omega := M.omega_mem separation infinite
  have bound := M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hN omega
  have relation := M.certificateEnumerationRelation_mem pairing unions powers separation
    hJ hNodes hN hk omega
  have total : ∀ j ∈ J, ∃ pair ∈ M.synchronizedEnumerationBound nodes N,
      ZFSet.pair j pair ∈ M.certificateEnumerationRelation J nodes N k := by
    intro j hj
    obtain ⟨c, jc, _⟩ := function.2 j hj
    have hc := (ZFSet.pair_mem_prod.1 (function.1 jc)).2
    obtain ⟨F, _, tail, htail, rfl⟩ := ZFSet.mem_prod.1 hc
    obtain ⟨B, _, f, _, rfl⟩ := ZFSet.mem_prod.1 htail
    have fields := (M.mem_supportedEqualityCertificateBound nodes N F B f).1
      (ZFSet.pair_mem_prod.1 (function.1 jc)).2
    obtain ⟨nonempty, ff⟩ := certificates j F B f jc
    obtain ⟨e, he, names, hn, ef, nf, onto, forward, backward⟩ :=
      M.groundFunction_enumeration pairing unions powers separation infinite
        fields.2.1.1 hN fields.2.2.1 nonempty fields.2.1.2.2 ff
    have eBound : e ∈ M.groundRelations ZFSet.omega nodes := by
      refine (M.mem_groundRelations ZFSet.omega nodes e).2 ⟨he, ?_⟩
      intro z hz
      obtain ⟨n, hno, v, hv, rfl⟩ := ZFSet.mem_prod.1 (ef.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨hno, fields.2.1.2.1 hv⟩
    have nBound := (M.mem_groundRelations ZFSet.omega N names).2 ⟨hn, nf.1⟩
    refine ⟨ZFSet.pair e names, ZFSet.pair_mem_prod.2 ⟨eBound, nBound⟩, ?_⟩
    exact (M.pair_mem_certificateEnumerationRelation J nodes N k j e names).2
      ⟨hj, eBound, nBound, F, B, f, jc, ff, ef, nf, onto, forward, backward⟩
  obtain ⟨enumerations, ground, selectedFunction, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hJ bound relation total
  refine ⟨enumerations, ground, selectedFunction, selected, ?_⟩
  intro j F B f e names stored entry
  obtain ⟨hj, _, _, F', B', f', stored', code⟩ :=
    (M.pair_mem_certificateEnumerationRelation J nodes N k j e names).1 (selected entry)
  obtain ⟨_, _, unique⟩ := function.2 j hj
  have equal := (unique _ stored').trans (unique _ stored).symm
  have tail := (ZFSet.pair_inj.1 equal).2
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 tail
  exact code

end TransitiveGround

end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalEnumeratedCertificateFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {Q : Type u} [PartialOrder Q] [OrderTop Q] (s : Presentation Q)

theorem exists_enumeratedSupportedCertificateFamily
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (_maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (_hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (J : ZFSet.{u}) (_hJ : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
      (_smallJ : M.groundEmbeddable J ZFSet.omega)
      (_hs : ∀ z : Name s, z.val ∈ J →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z)
      (_subset : ∀ z : Name s, z.val ∈ J → Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (p : Q) (_hp : H.mem p),
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes a s T d.principalFix)) k ∧
        k ⊆ M.supportedCertificateFamilyRelation a s b T d.principalFix
          geometry.order J validJ H ∧
        ∃ q, H.mem q ∧ q ≤ p ∧
          Forces (M.nameDomain s) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv a s t b T d.principalFix pairing unions powers
              separation collection carrier geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              _maps _hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground _hJ hk validJ) q ∧
          ∃ enumerations ∈ M.sets,
            ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
              (M.niceSupportNameCodes a s T d.principalFix)) enumerations ∧
            enumerations ⊆ M.certificateEnumerationRelation J b.carrier
              (M.niceSupportNameCodes a s T d.principalFix) k ∧
            (∀ j F B f e names,
              ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
              SynchronizedEnumerationCode ZFSet.omega
                (M.niceSupportNameCodes a s T d.principalFix) B f e names) ∧
            ∀ (z : (M.nameDomain s).names) (F B f : ZFSet.{u}),
              ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              F = M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∧
              MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
              B.Nonempty ∧ M.DecidesVisibilityProfile a s b d.principalFix T F z.val q ∧
              (∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
                ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) ∧
              ∃ e ∈ M.sets, ∃ names ∈ M.sets,
                ZFSet.IsFunc ZFSet.omega B e ∧
                ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes a s T d.principalFix) names ∧
                (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent
    J hJ validJ smallJ hs subsets p hp
  obtain ⟨k, hk, function, selected, q, hq, qp, forced, entries⟩ :=
    fulfilled.exists_forcedSupportedCertificateFamily s collection infinite choice carrier order
      small closed smallD irreflexive a maps T hT valid terms children H genericCoded
      genericFormula descent J hJ validJ smallJ hs subsets p hp
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  have codesGround := M.niceSupportNameCodes_mem a s b T d.principalFix t pairing unions powers
    separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
  have certificates : ∀ j F B f, ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
      B.Nonempty ∧ ZFSet.IsFunc B (M.niceSupportNameCodes a s T d.principalFix) f := by
    intro j F B f stored
    have hj := (ZFSet.pair_mem_prod.1 (function.1 stored)).1
    let z : (M.nameDomain s).names := ⟨⟨j, validJ j hj⟩, M.transitive hJ hj⟩
    have chosen := entries z F B f stored
    obtain ⟨_, _, _, _, _, _, certificate⟩ :=
      (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 (selected stored)
    exact ⟨chosen.2.2.1, certificate.2.2.2.1⟩
  obtain ⟨enumerations, ground, enumerationFunction, enumerationRelation, synchronized⟩ :=
    M.exists_supportedCertificateEnumerations pairing unions powers separation infinite choice
      hJ geometry.carrier_ground codesGround hk function certificates
  exact ⟨k, hk, function, selected, q, hq, qp, forced, enumerations, ground,
    enumerationFunction, enumerationRelation, synchronized, entries⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalPrefixPreparationBatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable {R : Type u} [PartialOrder R] (c : Presentation R)

theorem exists_prefixPreparationBatch_oai
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (rowClosed : InternallyCountablyClosed M c) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) R) (T T2 rowTop : ZFSet.{u})
      (carrier : c.carrier ∈ M.sets) (rowOrder : c.conditionOrder ∈ M.sets)
      (rowAction : a.actionGraph c t ∈ M.sets)
      (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily ⊥ directed) tau)
      (topMem : rowTop ∈ c.carrier)
      (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder),
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
    ∀ (stages history alpha : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
      (member : alpha ∈ stages),
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice rowClosed
  let lowerGround := inputs.1
  let maps := inputs.2.2.1
  let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
    ∀ (row A : ZFSet.{u}) (_condition : ZFSet.pair row A ∈
      M.refinementHistoryForcing c.carrier T stages packed),
  let selected := assignmentOnIndices indices T A
  let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
    ∀ (H : ConditionFilter (SetMembers Q))
      (_genericCoded : H.GenericFor (M.codedFamily lower))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain lower)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
        d.principalFix v ≤ lowerAct.stabilizer lower x.val →
        d.principalFix w ≤ lowerAct.stabilizer lower y.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain lower).names,
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ lowerAct.stabilizer lower τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (p : SetMembers Q) (_hp : H.mem p),
      ∃ (validJ : ∀ z ∈ J, IsName lower z) (hJ : J ∈ M.sets),
        M.groundEmbeddable J ZFSet.omega ∧
        (∀ z : Name lower, z.val ∈ J →
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily ⊥ directed) z ∧
          Name.eval {q | H.mem q} z ⊆ Name.eval {q | H.mem q} (Name.familySet ⊤ T valid)) ∧
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes lowerAct lower T d.principalFix)) k ∧
        k ⊆ M.supportedCertificateFamilyRelation lowerAct lower b T d.principalFix
          geometry.order J validJ H ∧
        ∃ q, H.mem q ∧ q ≤ p ∧
          Forces (M.nameDomain lower) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv lowerAct lower t b T d.principalFix pairing unions powers
              separation collection lowerGround geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              maps hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground hJ hk validJ) q ∧
          ∃ enumerations ∈ M.sets,
            ZFSet.IsFunc J (M.synchronizedEnumerationBound b.carrier
              (M.niceSupportNameCodes lowerAct lower T d.principalFix)) enumerations ∧
            enumerations ⊆ M.certificateEnumerationRelation J b.carrier
              (M.niceSupportNameCodes lowerAct lower T d.principalFix) k ∧
            (∀ j F B f e names,
              ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              ZFSet.pair j (ZFSet.pair e names) ∈ enumerations →
              SynchronizedEnumerationCode ZFSet.omega
                (M.niceSupportNameCodes lowerAct lower T d.principalFix) B f e names) ∧
            ∀ (z : (M.nameDomain lower).names) (F B f : ZFSet.{u}),
              ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
              F = M.visibleSupportProfile lowerAct lower b d T H (Name.eval {p | H.mem p} z.val) ∧
              MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
              B.Nonempty ∧ M.DecidesVisibilityProfile lowerAct lower b d.principalFix T F z.val q ∧
              (∀ v ∈ B, ∀ tau : Name lower, tau.val ∈ M.niceSupportNameCodes lowerAct lower T d.principalFix →
                ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) ∧
              ∃ e ∈ M.sets, ∃ names ∈ M.sets,
                ZFSet.IsFunc ZFSet.omega B e ∧
                ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes lowerAct lower T d.principalFix) names ∧
                (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
                (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                  ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a T T2 rowTop carrier rowOrder rowAction hT hT2 valid1 valid2 closed1 closed2
    children1 children2 topMem topRows
  let nodeOrder : b.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let nodeAction : d.actionGraph b t ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeAction
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let omega := M.omega_mem separation infinite
  intro stages history alpha hs hh ordinal trace member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 ordinal trace
  let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let historyTop := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    (historyRun.carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c (historyRun.carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let lowerAct := M.semanticStructuralPrefixAction c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hh trace hAlpha cutOrdinal subset
  let inputs := M.semanticStructuralPrefix_preparation_inputs c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice rowClosed
  let lowerGround := inputs.1
  let lowerOrder := inputs.2.1
  let maps := inputs.2.2.1
  let lowerClosed := inputs.2.2.2.1
  let terms := inputs.2.2.2.2.1
  let children := inputs.2.2.2.2.2
  let indices := M.niceRefinementIndices lowerAct lower b d alpha T T2 valid
  intro row A condition H genericCoded genericFormula descent p hp
  let selected := assignmentOnIndices indices T A
  let graphs := M.niceAssignmentClassGraphs lowerAct lower b d alpha T T2 valid selected
  let bound := M.groundRelations T lower.carrier
  let J := relationImage selected bound (graphs 0) ∪ relationImage selected bound (graphs 1)
  obtain ⟨_, _, _, hJ, smallJ, validJ, facts, _⟩ :=
    M.semanticStructuralPrefix_assignmentClassRequests c a t b d ⊥ directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrder rowAction
        geometry.actors_ground geometry.carrier_ground nodeOrder nodeAction nodeMaps supports
        hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace member
      infinite choice condition
  refine ⟨validJ, hJ, smallJ, (fun z hz => ⟨(facts z hz).1, (facts z hz).2 H⟩), ?_⟩
  exact fulfilled.exists_enumeratedSupportedCertificateFamily lower collection infinite choice
    lowerGround lowerOrder small lowerClosed smallD irreflexive lowerAct maps T hT valid terms children
    H genericCoded genericFormula descent J hJ validJ smallJ
    (fun z hz => (facts z hz).1) (fun z hz => (facts z hz).2 H) p hp

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_prefixPreparationBatch_oai.{u, v}
