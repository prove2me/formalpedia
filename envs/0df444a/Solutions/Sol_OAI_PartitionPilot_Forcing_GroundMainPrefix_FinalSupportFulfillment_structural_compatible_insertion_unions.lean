-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_compatible_insertion_unions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:33:00.416218+00:00
-- url     : https://prove2.me/submissions/6bbe277c-8aeb-4742-80d7-c4a14d9f306f

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
import Definitions.Def_OAIQ253P010
import Definitions.Def_OAIQ253P011
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_binaryRowStructuralAssignmentImage_dataBound
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_insertion_crossCollisions

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u v
variable {P Q R : Type u} {s : Presentation P}

theorem rename_check (t : Presentation Q) (f : P → Q) (one : P) (x : ZFSet.{u}) :
    rename t f (check s one x) = check t (f one) x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [check, rename_assemble, check]
    apply congrArg (fun names : x → Name t => assemble names (fun _ => f one))
    funext y
    exact ih y.val y.property

theorem rename_check_fixed (f : P → P) (one : P) (fixed : f one = one) (x : ZFSet.{u}) :
    rename s f (check s one x) = check s one x := by
  rw [rename_check, fixed]

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v

namespace PosetAction
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_check [OrderTop P] (g : G) (x : ZFSet.{u}) :
    a.act s g (Name.check s ⊤ x) = Name.check s ⊤ x :=
  Name.rename_check_fixed (a.iso g) ⊤ (a.iso g).map_top x

end PosetAction
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PresentedGroupCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_relationOnFormula {n} (c r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (relationOnFormula c r) env ↔ env r ⊆ ZFSet.prod (env c) (env c) := by
  simp only [relationOnFormula, Truth, truth_exMem, truth_orderedPairFormula]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ZFSet.mem_prod.symm))

theorem truth_partialOrderFormula {n} (c r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (partialOrderFormula c r) env ↔ PartialOrderCode (env c) (env r) := by
  simp only [partialOrderFormula, Truth, truth_relationOnFormula, reflexiveFormula,
    antisymmetricFormula, transitiveFormula, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨shape, refl, antisymm, trans⟩
    exact ⟨shape, refl, fun x hx y hy xy yx => antisymm x hx y hy ⟨xy, yx⟩,
      fun x hx y hy z hz xy yz => trans x hx y hy z hz ⟨xy, yz⟩⟩
  · intro h
    exact ⟨h.relation, h.refl, fun x hx y hy ⟨xy, yx⟩ => h.antisymm x hx y hy xy yx,
      fun x hx y hy z hz ⟨xy, yz⟩ => h.trans x hx y hy z hz xy yz⟩

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_binaryRelationFormula {n} (g f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (binaryRelationFormula g f) env ↔
      env f ⊆ ZFSet.prod (ZFSet.prod (env g) (env g)) (env g) := by
  simp only [binaryRelationFormula, Truth, truth_exMem, truth_orderedTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, y, hy, z, hz, eq⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨ZFSet.pair x y, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, z, hz, eq⟩
  · intro h w hw
    obtain ⟨xy, hxy, z, hz, eq⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact ⟨x, hx, y, hy, z, hz, eq⟩

theorem truth_binaryFunctionFormula {n} (g f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (binaryFunctionFormula g f) env ↔
      ZFSet.IsFunc (ZFSet.prod (env g) (env g)) (env g) (env f) := by
  simp only [binaryFunctionFormula, Truth, truth_binaryRelationFormula, truth_exMem,
    truth_tripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro xy hxy
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    obtain ⟨z, _, rel, unique⟩ := total x hx y hy
    refine ⟨z, rel, ?_⟩
    intro w hw
    exact unique w (ZFSet.pair_mem_prod.1 (shape hw)).2 hw
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx y hy
    obtain ⟨z, rel, unique⟩ := total (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    exact ⟨z, (ZFSet.pair_mem_prod.1 (shape rel)).2, rel, fun w _ hw => unique w hw⟩

end PartitionPilot.Forcing.BoundedFormula



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPartialFunctionSpaces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

namespace PartialFunctionCode

theorem union {X Y p q : ZFSet.{u}} (hp : PartialFunctionCode X Y p) (hq : PartialFunctionCode X Y q)
    (agree : ∀ x y z, ZFSet.pair x y ∈ p → ZFSet.pair x z ∈ q → y = z) :
    PartialFunctionCode X Y (p ∪ q) := by
  refine ⟨fun _ hz => (ZFSet.mem_union.1 hz).elim (fun h => hp.shape h) (fun h => hq.shape h), ?_⟩
  intro x y z hy hz
  rcases ZFSet.mem_union.1 hy with hy | hy
  · rcases ZFSet.mem_union.1 hz with hz | hz
    · exact hp.unique x y z hy hz
    · exact agree x y z hy hz
  · rcases ZFSet.mem_union.1 hz with hz | hz
    · exact (agree x z y hz hy).symm
    · exact hq.unique x y z hy hz

end PartialFunctionCode

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProductActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section



namespace PartitionPilot.SetRealization.Presentation

universe u
variable {I : Type u} [Bot I]

theorem mem_nonbottom_carrier (s : Presentation I) (z : ZFSet.{u}) :
    z ∈ s.nonbottom.carrier ↔ z ∈ s.carrier ∧ z ≠ s.encode ⊥ := by
  change z ∈ ZFSet.sep (fun w => w ≠ s.encode ⊥) s.carrier ↔ _
  exact ZFSet.mem_sep

end PartitionPilot.SetRealization.Presentation

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NamePresentationEquivalences
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u v
variable {P : Type u} {G : Type v} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s t : Presentation P)

theorem act_presentationEquiv (g : G) (τ : Name s) :
    a.act t g (Name.presentationEquiv s t τ) = Name.presentationEquiv s t (a.act s g τ) := by
  change Name.rename t (a.iso g) (Name.rename t id τ) =
    Name.rename t id (Name.rename s (a.iso g) τ)
  rw [Name.rename_comp, Name.rename_comp]
  rfl

theorem stabilizer_presentationEquiv (τ : Name s) :
    a.stabilizer t (Name.presentationEquiv s t τ) = a.stabilizer s τ := by
  apply Subgroup.ext
  intro g
  change a.act t g (Name.presentationEquiv s t τ) = Name.presentationEquiv s t τ ↔ a.act s g τ = τ
  rw [a.act_presentationEquiv]
  exact (Name.presentationEquiv s t).injective.eq_iff

end PartitionPilot.Forcing.PosetAction

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_FinitePrincipalNameSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v
variable {P : Type u} [PartialOrder P] {G : Type v} [Group G]

variable (a : PosetAction G P) (s : Presentation P)

theorem niceNameCode_subset {T z : ZFSet.{u}} {K : Subgroup G}
    (code : NiceNameCode a s T K z) : z ⊆ ZFSet.prod T s.carrier := by
  obtain ⟨τ, equal, subset, _⟩ := code
  exact equal ▸ subset

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_IndexedTupleNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace Name

theorem check_code_eq {P : Type u} (s : Presentation P) (one : P) (x : ZFSet.{u}) :
    (check s one x).val = checkNameCode (s.encode one) x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    change z ∈ (check s one x).val ↔ z ∈ (check (checkCodePresentation (s.encode one)) ⟨()⟩ x).val
    rw [mem_check_code, mem_check_code]
    apply exists_congr
    intro y
    apply and_congr_right
    intro hy
    rw [ih y hy]
    rfl

end Name

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} {s : Presentation P}

theorem rename_indexedTuple (t : Presentation Q) (f : P → Q) (one : P)
    (I : ZFSet.{u}) (names : I.toSet → Name s) :
    rename t f (indexedTuple one I names) =
      indexedTuple (f one) I (fun i => rename t f (names i)) := by
  rw [indexedTuple, rename_assemble, indexedTuple]
  apply congrArg (fun ns : I → Name t => assemble ns (fun _ => f one))
  funext i
  rw [rename_orderedPair, rename_check]

theorem act_indexedTuple {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (g : G) (I : ZFSet.{u}) (names : I.toSet → Name s) :
    a.act s g (indexedTuple ⊤ I names) = indexedTuple ⊤ I (fun i => a.act s g (names i)) := by
  change rename s (a.iso g) _ = _
  rw [rename_indexedTuple, (a.iso g).map_top]
  rfl

end PartitionPilot.Forcing.Name

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RowPositionBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem rowPositionSequence_length {mu delta : ZFSet.{u}}
    (ordinal : ordinalSetProperty mu) (length : delta ∈ insert mu mu) :
    ordinalSetProperty delta ∧ delta ⊆ mu := by
  rcases ZFSet.mem_insert_iff.1 length with rfl | member
  · exact ⟨ordinal, fun _ hx => hx⟩
  · exact ⟨ordinalSetProperty_member ordinal member, fun a ha => ordinal.1 delta member a ha⟩

theorem RowPositionSequenceCode.shape {L r I mu f : ZFSet.{u}}
    (code : RowPositionSequenceCode L r I mu f) (ordinal : ordinalSetProperty mu) :
    f ⊆ ZFSet.prod mu I := by
  obtain ⟨delta, length, function, _⟩ := code
  intro z hz
  obtain ⟨a, ha, x, hx, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨(rowPositionSequence_length ordinal length).2 ha, hx⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_rowPositionSequences {L r I mu f : ZFSet.{u}} (ordinal : ordinalSetProperty mu) :
    f ∈ M.rowPositionSequences L r I mu ↔ f ∈ M.sets ∧ RowPositionSequenceCode L r I mu f := by
  rw [rowPositionSequences, ZFSet.mem_sep, M.mem_groundRelations]
  exact ⟨fun ⟨ground, code⟩ => ⟨ground.1, code⟩,
    fun ⟨ground, code⟩ => ⟨⟨ground, code.shape ordinal⟩, code⟩⟩

theorem rowPositionSequence_data {L r I mu f : ZFSet.{u}}
    (hL : L ∈ M.sets) (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu)
    (member : f ∈ M.rowPositionSequences L r I mu) :
    f ∈ M.sets ∧ ∃ delta ∈ M.sets, ordinalSetProperty delta ∧ delta ⊆ mu ∧
      ZFSet.IsFunc delta I f ∧ ∃ D ∈ L, D ∈ M.sets ∧
        ∀ a x, ZFSet.pair a x ∈ f → ZFSet.pair x D ∈ r := by
  obtain ⟨ground, delta, length, function, D, hD, bounds⟩ :=
    (M.mem_rowPositionSequences ordinal).1 member
  have hdelta : delta ∈ M.sets := (ZFSet.mem_insert_iff.1 length).elim
    (fun equal => equal ▸ hmu) (M.transitive hmu)
  have ordBound := rowPositionSequence_length ordinal length
  exact ⟨ground, delta, hdelta, ordBound.1, ordBound.2, function,
    D, hD, M.transitive hL hD, bounds⟩

end TransitiveGround

end PartitionPilot.Forcing



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



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})






theorem groundCountable_family_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets)
    (countR : M.groundEmbeddable R ZFSet.omega)
    (small : ∀ p ∈ R, M.groundEmbeddable p ZFSet.omega) :
    M.groundEmbeddable (⋃₀ R) ZFSet.omega := by
  classical
  by_cases nonempty : R.Nonempty
  · obtain ⟨g, hg, enumeration, onto⟩ :=
      M.groundCountable_enumeration pairing unions powers separation infinite hR nonempty countR
    exact M.countable_enumerated_union pairing unions powers separation infinite choice
      hR (M.union_mem unions hR) hg enumeration onto
      (fun p hp _ hz => ZFSet.mem_sUnion.2 ⟨p, hp, hz⟩) small
  · have empty : R = ∅ := by
      apply ZFSet.ext
      intro p
      exact ⟨fun hp => False.elim (nonempty ⟨p, hp⟩), fun hp => False.elim (ZFSet.notMem_empty p hp)⟩
    rw [empty, ZFSet.sUnion_empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨R, hR⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableRelationSelections
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

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem countablePartialFunctions_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y p q : ZFSet.{u}}
    (hp : p ∈ M.smallPartialFunctions X Y ZFSet.omega)
    (hq : q ∈ M.smallPartialFunctions X Y ZFSet.omega)
    (agree : ∀ x y z, ZFSet.pair x y ∈ p → ZFSet.pair x z ∈ q → y = z) :
    p ∪ q ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  obtain ⟨hpM, hpCode, hpSmall⟩ := (M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp
  obtain ⟨hqM, hqCode, hqSmall⟩ := (M.mem_smallPartialFunctions X Y ZFSet.omega q).1 hq
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨M.binary_union_mem pairing unions hpM hqM, hpCode.union hqCode agree,
      M.groundCountable_binary_union pairing unions powers separation infinite choice hpM hqM hpSmall hqSmall⟩

theorem countableFunction_common_extension
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ p q : SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      (∀ x y z, ZFSet.pair x y ∈ SetMembers.raw p → ZFSet.pair x z ∈ SetMembers.raw q → y = z) →
      ∃ r, SetMembers.raw r = SetMembers.raw p ∪ SetMembers.raw q ∧ r ≤ p ∧ r ≤ q := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro p q agree
  have member := M.countablePartialFunctions_union pairing unions powers separation infinite choice
    (SetMembers.raw_mem p) (SetMembers.raw_mem q) agree
  let r := SetMembers.ofMem (SetMembers.raw p ∪ SetMembers.raw q) member
  have raw : SetMembers.raw r = SetMembers.raw p ∪ SetMembers.raw q := SetMembers.raw_ofMem _ _
  refine ⟨r, raw, (M.smallFunction_le_iff X Y ZFSet.omega r p).2 ?_,
    (M.smallFunction_le_iff X Y ZFSet.omega r q).2 ?_⟩
  · rw [raw]
    exact fun _ hz => ZFSet.mem_union.2 (Or.inl hz)
  · rw [raw]
    exact fun _ hz => ZFSet.mem_union.2 (Or.inr hz)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation infinite choice

theorem exists_countableRelationSelection {A L R : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (hR : R ∈ M.sets)
    (smallA : M.groundEmbeddable A ZFSet.omega)
    (total : ∀ x ∈ A, ∃ y ∈ L, ZFSet.pair x y ∈ R) :
    ∃ f ∈ M.sets, ZFSet.IsFunc A L f ∧ f ⊆ R ∧
      relationImage A L f ∈ M.sets ∧ M.groundEmbeddable (relationImage A L f) ZFSet.omega := by
  obtain ⟨f,hf,function,selected⟩ := M.uniformize_relation pairing unions powers separation choice hA hL hR total
  exact ⟨f,hf,function,selected,M.relationImage_mem separation hA hL hf,
    M.groundEmbeddable_function_image pairing unions powers separation choice hA hL
      (M.omega_mem separation infinite) hf function smallA⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCoinitialOperations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace BoundedFormula

open SetFormula

theorem truth_coinitialBelowFormula {n} (order F target B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (coinitialBelowFormula order F target B) env ↔
      CoinitialBelowCode (env order) (env F) (env target) (env B) := by
  simp only [coinitialBelowFormula, Truth, truth_exMem, truth_pairMembershipFormula]
  rfl

theorem realize_coinitialBelowFormula (M : TransitiveGround.{u}) {n}
    (order F target B : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (coinitialBelowFormula order F target B).toFormula env ↔
      CoinitialBelowCode (env order) (env F) (env target) (env B) :=
  (realize_toFormula M _ env members).trans
    (truth_coinitialBelowFormula order F target B env)

end BoundedFormula

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedMeetOrderCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_meetOrderFormula {n} (P r μ : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (meetOrderFormula P r μ) env ↔ MeetOrderCode (env P) (env r) (env μ) := by
  simp only [meetOrderFormula, Truth, truth_partialOrderFormula,
    truth_binaryFunctionFormula, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  constructor
  · rintro ⟨order, operation, laws⟩
    have bounds (x y z : ZFSet.{u}) (entry : ZFSet.pair (ZFSet.pair x y) z ∈ env μ) :
        x ∈ env P ∧ y ∈ env P ∧ z ∈ env P := by
      have shape := ZFSet.pair_mem_prod.1 (operation.1 entry)
      exact ⟨(ZFSet.pair_mem_prod.1 shape.1).1,
        (ZFSet.pair_mem_prod.1 shape.1).2, shape.2⟩
    refine ⟨order, operation, ?_, ?_, ?_⟩
    · intro x y z entry
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).1
    · intro x y z entry
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).2.1
    · intro x y z w hw entry wx wy
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).2.2 w hw ⟨wx, wy⟩
  · intro meet
    exact ⟨meet.order, meet.operation, fun x _ y _ z _ entry =>
      ⟨meet.lower_left x y z entry, meet.lower_right x y z entry,
        fun w hw ⟨wx, wy⟩ => meet.greatest x y z w hw entry wx wy⟩⟩

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FixedTopCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace MeetOrderCode

theorem eq_canonicalMeetGraph {L r μ : ZFSet.{u}} (code : MeetOrderCode L r μ) :
    μ = canonicalMeetGraph L r := by
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨a, ha, z, _, rfl⟩ := ZFSet.mem_prod.1 (code.operation.1 hv)
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 ha
    exact (pair_mem_canonicalMeetGraph L r x y z).2 (code.pair_iff.1 hv)
  · intro hv
    obtain ⟨x, hx, y, hy, z, hz, rfl, h⟩ := (mem_canonicalMeetGraph L r v).1 hv
    exact code.pair_iff.2 ⟨hx, hy, hz, h⟩

end MeetOrderCode

end PartitionPilot.Forcing

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowDistinguishing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem mem_rowCoordinateDomain (I C Y p x : ZFSet.{u}) :
    x ∈ rowCoordinateDomain I C Y p ↔
      x ∈ ZFSet.prod I C ∧ ∃ y ∈ Y, ZFSet.pair x y ∈ p := by
  rw [rowCoordinateDomain, mem_relationImage]
  constructor
  · rintro ⟨hx, z, hz, rel⟩
    obtain ⟨a, _, y, hy, eq⟩ := (mem_productFirst (ZFSet.prod I C) Y _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    refine ⟨hx, y, hy, ?_⟩
    rw [entries.2]
    exact entries.1 ▸ hz
  · rintro ⟨hx, y, hy, entry⟩
    exact ⟨hx, ZFSet.pair x y, entry,
      (mem_productFirst (ZFSet.prod I C) Y _).2 ⟨x, hx, y, hy, rfl⟩⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem rowCoordinateDomain_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) : rowCoordinateDomain I C Y p ∈ M.sets := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  exact M.relationImage_mem separation hp coordinates
    (M.productFirst_mem pairing unions powers separation coordinates hY)

theorem rowCoordinateDomain_groundEmbeddable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) : M.groundEmbeddable (rowCoordinateDomain I C Y p) N := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  exact M.groundEmbeddable_function_image pairing unions powers separation choice hp coordinates hN
    (M.productFirst_mem pairing unions powers separation coordinates hY)
    (productFirst_function (ZFSet.prod I C) Y) small

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBinaryRowNames
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
variable (M : TransitiveGround.{u})

theorem entry_binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u})
    (σ : Name (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name.Entry σ (M.binaryRowName I C one i) p ↔ ∃ c ∈ C,
      Name.check (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c = σ ∧
      ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈ SetMembers.raw p := by
  rw [binaryRowName, Name.entry_assemble]
  constructor
  · rintro ⟨z, eq, rfl⟩
    exact ⟨SetMembers.raw z.val.1, SetMembers.raw_mem z.val.1, eq, z.property⟩
  · rintro ⟨c, hc, eq, assigned⟩
    refine ⟨⟨(SetMembers.ofMem c hc, p), ?_⟩, ?_, rfl⟩
    · simpa only [SetMembers.raw_ofMem] using assigned
    · simpa only [SetMembers.raw_ofMem] using eq

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskRepresentativeCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula
universe u

theorem truth_meetFilterFormula {n} (P r μ F : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (meetFilterFormula P r μ F) env ↔
      MeetFilterCode (env P) (env r) (env μ) (env F) := by
  simp only [meetFilterFormula, Truth, truth_exMem, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨subset, ⟨x, hx, _⟩, upward, closed⟩
    exact ⟨subset, ⟨x, hx⟩, upward, fun x hx y hy z entry =>
      closed x hx y hy z (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2 entry⟩
  · intro filter
    obtain ⟨x, hx⟩ := filter.nonempty
    exact ⟨filter.subset, ⟨x, hx, trivial⟩, filter.upward,
      fun x hx y hy z _ entry => filter.closed_meet x hx y hy z entry⟩

theorem realize_meetFilterFormula (M : TransitiveGround.{u}) {n}
    (P r μ F : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (meetFilterFormula P r μ F).toFormula env ↔
      MeetFilterCode (env P) (env r) (env μ) (env F) :=
  (realize_toFormula M _ env members).trans (truth_meetFilterFormula P r μ F env meet)

end BoundedFormula

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFlatSuccessorFullActionGraph
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y G : Type u} [Group G] [PartialOrder X]
variable (a : PosetAction G X) (s : Presentation X) (t : Presentation Y) (b : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {N : ZFSet.{u}} (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
variable (hG : b.carrier ∈ M.sets) (hN : N ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)

theorem smallFunctionAction_entry (g : G) (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N))
    (x : X) (y : Y) :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    ZFSet.pair (s.encode (a.iso g x)) (t.encode y) ∈
      SetMembers.raw ((M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph).iso g p) ↔
        ZFSet.pair (s.encode x) (t.encode y) ∈ SetMembers.raw p := by
  let := M.smallFunctionOrder s.carrier t.carrier N
  rw [raw_smallFunctionAction, pair_mem_graphRename]
  change ZFSet.pair (s.encode ((a.iso g).toEquiv.symm ((a.iso g).toEquiv x))) (t.encode y) ∈ _ ↔ _
  rw [(a.iso g).toEquiv.symm_apply_apply]

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOutsideRowNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

universe u

theorem mem_rowUsedRows (I C Y p i : ZFSet.{u}) :
    i ∈ rowUsedRows I C Y p ↔
      i ∈ I ∧ ∃ c ∈ C, ∃ y ∈ Y, ZFSet.pair (ZFSet.pair i c) y ∈ p := by
  rw [rowUsedRows, mem_relationImage]
  constructor
  · rintro ⟨hi, x, hx, rel⟩
    obtain ⟨j, _, c, hc, eq⟩ := (mem_productFirst I C _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    obtain ⟨_, y, hy, entry⟩ := (mem_rowCoordinateDomain I C Y p x).1 hx
    rw [entries.1, ← entries.2] at entry
    exact ⟨hi, c, hc, y, hy, entry⟩
  · rintro ⟨hi, c, hc, y, hy, entry⟩
    exact ⟨hi, ZFSet.pair i c,
      (mem_rowCoordinateDomain I C Y p _).2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hc⟩, y, hy, entry⟩,
      (mem_productFirst I C _).2 ⟨i, hi, c, hc, rfl⟩⟩

theorem rowUsedRows_subset (I C Y p : ZFSet.{u}) : rowUsedRows I C Y p ⊆ I :=
  fun i hi => ((mem_rowUsedRows I C Y p i).1 hi).1

theorem row_mem_rowUsedRows {I C Y p i c y : ZFSet.{u}}
    (code : PartialFunctionCode (ZFSet.prod I C) Y p)
    (entry : ZFSet.pair (ZFSet.pair i c) y ∈ p) : i ∈ rowUsedRows I C Y p := by
  have bound := ZFSet.pair_mem_prod.1 (code.shape entry)
  have coordinates := ZFSet.pair_mem_prod.1 bound.1
  exact (mem_rowUsedRows I C Y p i).2 ⟨coordinates.1, c, coordinates.2, y, bound.2, entry⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem rowUsedRows_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) : rowUsedRows I C Y p ∈ M.sets :=
  M.relationImage_mem separation
    (M.rowCoordinateDomain_mem pairing unions powers separation hI hC hY hp) hI
    (M.productFirst_mem pairing unions powers separation hI hC)

theorem rowUsedRows_groundEmbeddable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) : M.groundEmbeddable (rowUsedRows I C Y p) N :=
  M.groundEmbeddable_function_image pairing unions powers separation choice
    (M.rowCoordinateDomain_mem pairing unions powers separation hI hC hY hp) hI hN
    (M.productFirst_mem pairing unions powers separation hI hC) (productFirst_function I C)
    (M.rowCoordinateDomain_groundEmbeddable pairing unions powers separation choice hI hC hY hp hN small)

theorem countablePartialFunctions_rowSupport
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hp : p ∈ M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega) :
    rowUsedRows I C Y p ∈ M.sets ∧ M.groundEmbeddable (rowUsedRows I C Y p) ZFSet.omega := by
  obtain ⟨ground, _, small⟩ := (M.mem_smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega p).1 hp
  exact ⟨M.rowUsedRows_mem pairing unions powers separation hI hC hY ground,
    M.rowUsedRows_groundEmbeddable pairing unions powers separation choice
      hI hC hY ground (M.omega_mem separation infinite) small⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowAction_entry :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers
      (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}) (c : SetMembers C) (k : Fin 2),
      ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) (SetMembers.raw c)) (natSetCode k.val) ∈
        SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p) ↔
      ZFSet.pair (ZFSet.pair (s.encode i.val) (SetMembers.raw c)) (natSetCode k.val) ∈
        SetMembers.raw p := by
  let := columnOrder C
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i c k
  exact M.smallFunctionAction_entry (a.rowCoordinates C) (rowCoordinatePresentation s C)
    (natInitialPresentation 2) b pairing unions powers separation
    (M.rowCoordinate_carrier_mem s C pairing unions powers separation hL hC)
    (M.natSetCode_mem separation infinite 2) hG (M.omega_mem separation infinite)
    (M.rowCoordinate_graph_mem a s b C pairing unions powers separation hL hC hG graph)
    g p (i, c) (ULift.up k)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowAction_raw_entry :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}) (c y : ZFSet.{u}), c ∈ C → y ∈ natSetCode 2 →
      (ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) c) y ∈
        SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p) ↔
      ZFSet.pair (ZFSet.pair (s.encode i.val) c) y ∈ SetMembers.raw p) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i c y hc hy
  obtain ⟨k, eq⟩ := ((natInitialPresentation 2).mem_carrier y).1 hy
  change natSetCode k.down.val = y at eq
  have entry := M.internalRowAction_entry a s b C pairing unions powers separation infinite
    hL hC hG graph g p i (SetMembers.ofMem c hc) k.down
  simpa only [SetMembers.raw_ofMem, eq] using entry

theorem internalRowAction_usedRows :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}),
      s.encode (a.iso g i.val) ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2)
        (SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p)) ↔
      s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i
  rw [mem_rowUsedRows, mem_rowUsedRows]
  constructor
  · rintro ⟨_, c, hc, y, hy, entry⟩
    exact ⟨s.nonbottom.encode_mem i, c, hc, y, hy,
      (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
        hL hC hG graph g p i c y hc hy).1 entry⟩
  · rintro ⟨_, c, hc, y, hy, entry⟩
    exact ⟨s.nonbottom.encode_mem (a.nonbottom.iso g i), c, hc, y, hy,
      (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
        hL hC hG graph g p i c y hc hy).2 entry⟩

theorem internalRowAction_usedRows_bounded :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (D : L),
      (∀ i : {i : L // i ≠ ⊥},
        s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      ∀ i : {i : L // i ≠ ⊥},
        s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2)
          (SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
            hL hC hG graph).iso g p)) → i.val ≤ a.iso g D := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p D bound i used
  let j := (a.nonbottom.iso g).symm i
  have image : a.iso g j.val = i.val :=
    congrArg Subtype.val ((a.nonbottom.iso g).apply_symm_apply i)
  have old := (M.internalRowAction_usedRows a s b C pairing unions powers separation infinite
    hL hC hG graph g p j).1 (by rw [image]; exact used)
  have mapped := (a.iso g).monotone (bound j old)
  rw [image] at mapped
  exact mapped

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowName_action (g : G) (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowName s C hL i) =
      M.internalRowName s C hL (a.nonbottom.iso g i) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val)) =
    M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode (a.iso g i.val))
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename c (act.iso g)
    (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val))) q ↔ _
  rw [Name.entry_rename, M.entry_binaryRowName]
  constructor
  · rintro ⟨ν, p, entry, eq, rfl⟩
    obtain ⟨x, hx, rfl, hp⟩ := (M.entry_binaryRowName s.nonbottom.carrier C ⊤
      (s.encode i.val) ν p).1 entry
    refine ⟨x, hx, (act.act_check c g x).symm.trans eq, ?_⟩
    have moved := M.internalRowAction_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i (SetMembers.ofMem x hx) (1 : Fin 2)
    simp only [SetMembers.raw_ofMem] at moved
    exact moved.2 hp
  · rintro ⟨x, hx, rfl, hq⟩
    let p := (act.iso g).symm q
    have pq : act.iso g p = q := (act.iso g).apply_symm_apply q
    have moved := M.internalRowAction_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i (SetMembers.ofMem x hx) (1 : Fin 2)
    simp only [SetMembers.raw_ofMem] at moved
    have hp : ZFSet.pair (ZFSet.pair (s.encode i.val) x) (natSetCode 1) ∈
        SetMembers.raw p := by
      apply moved.1
      change ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) x) (natSetCode 1) ∈
        SetMembers.raw (act.iso g p)
      rw [pq]
      exact hq
    exact ⟨Name.check c ⊤ x, p,
      (M.entry_binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val) _ p).2
        ⟨x, hx, rfl, hp⟩, act.act_check c g x, pq⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSelectedSupportTupleFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowTupleName_action (g : G) (δ : ZFSet.{u})
    (positions : δ.toSet → {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowTupleName s C hL δ positions) =
      M.internalRowTupleName s C hL δ (fun i => a.nonbottom.iso g (positions i)) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (Name.indexedTuple ⊤ δ _) = Name.indexedTuple ⊤ δ _
  rw [Name.act_indexedTuple]
  apply congrArg (Name.indexedTuple ⊤ δ)
  funext i
  exact M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph g (positions i)

theorem internalRowTupleName_supported (δ : ZFSet.{u})
    (positions : δ.toSet → {i : L // i ≠ ⊥}) (D : L)
    (bounded : ∀ i, (positions i).val ≤ D) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    a.principalFix D ≤ act.stabilizer c (M.internalRowTupleName s C hL δ positions) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act c g fixed
  change act.act c g (M.internalRowTupleName s C hL δ positions) = _
  rw [M.internalRowTupleName_action a s b C pairing unions powers separation infinite hL hC hG graph]
  apply congrArg (M.internalRowTupleName s C hL δ)
  funext i
  exact Subtype.ext (fixed (positions i).val (bounded i))

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (z : ZFSet.{u}) : z ∈ M.binaryRowNameGraph I C one ↔
      ∃ i ∈ I, z = ZFSet.pair i (M.binaryRowName I C one i).val := by
  rw [binaryRowNameGraph, ZFSet.mem_range]
  exact ⟨fun ⟨i, eq⟩ => ⟨i.val, i.property, eq.symm⟩,
    fun ⟨i, hi, eq⟩ => ⟨⟨i, hi⟩, eq.symm⟩⟩

theorem pair_mem_binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i x : ZFSet.{u}) : ZFSet.pair i x ∈ M.binaryRowNameGraph I C one ↔
      i ∈ I ∧ x = (M.binaryRowName I C one i).val := by
  rw [M.mem_binaryRowNameGraph I C one]
  constructor
  · rintro ⟨j, hj, eq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem pair_mem_rowTupleFamily (one mu I W rows S f z : ZFSet.{u}) :
    ZFSet.pair f z ∈ rowTupleFamily one mu I W rows S ↔
      f ∈ S ∧ z = rowTupleCode one mu I W rows f := by
  rw [rowTupleFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨g, eq⟩
    obtain ⟨input, output⟩ := ZFSet.pair_inj.1 eq
    exact ⟨input ▸ g.property, output.symm.trans (congrArg (rowTupleCode one mu I W rows) input)⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩





namespace Name
theorem mem_indexedTuple_code {P : Type u} {s : Presentation P} (one : P)
    (δ : ZFSet.{u}) (names : δ.toSet → Name s) (z : ZFSet.{u}) :
    z ∈ (indexedTuple one δ names).val ↔ ∃ i : δ.toSet,
      z = ZFSet.pair (orderedPairNameCode (s.encode one) (check s one i.val).val (names i).val)
        (s.encode one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  simp only [orderedPair_code]
  exact exists_congr (fun _ => eq_comm)

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem binaryRowTupleCode_eq {I C mu δ f : ZFSet.{u}}
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (function : FunctionGraphOn δ f) (subset : δ ⊆ mu)
    (range : ∀ i, function.value i ∈ I) :
    let rows := M.binaryRowNameGraph I C one
    rowTupleCode (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows f =
      (Name.indexedTuple one δ (fun i => M.binaryRowName I C one (function.value i))).val := by
  dsimp only
  apply ZFSet.ext
  intro z
  rw [rowTupleCode, mem_indexedGraphNameCode, Name.mem_indexedTuple_code]
  constructor
  · rintro ⟨i, _, v, entry, equal⟩
    obtain ⟨_, _, x, hx, old, row⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    have hi := function.pair_source old
    have value := function.value_eq_of_entry ⟨i, hi⟩ old
    have rowValue := ((M.pair_mem_binaryRowNameGraph I C one x v).1 row).2
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [Name.check_code_eq, value]
    exact rowValue ▸ equal
  · rintro ⟨i, equal⟩
    have row := (M.pair_mem_binaryRowNameGraph I C one (function.value i) _).2 ⟨range i, rfl⟩
    refine ⟨i.val, subset i.property, (M.binaryRowName I C one (function.value i)).val,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨subset i.property, pair_second_mem_doubleUnion row, function.value i, range i,
          function.value_entry i, row⟩, ?_⟩
    rwa [Name.check_code_eq] at equal

theorem internalRowTupleCode_eq {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (C : ZFSet.{u}) (hL : s.carrier ∈ M.sets)
    {mu δ f : ZFSet.{u}} (function : FunctionGraphOn δ f) (subset : δ ⊆ mu)
    (positions : δ.toSet → {i : L // i ≠ ⊥})
    (values : ∀ i, function.value i = s.encode (positions i).val) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    rowTupleCode (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows f = (M.internalRowTupleName s C hL δ positions).val := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  have range (i : δ.toSet) : function.value i ∈ s.nonbottom.carrier := by
    rw [values i]
    exact s.nonbottom.encode_mem (positions i)
  have eq := M.binaryRowTupleCode_eq (C := C) ⊤ function subset range
  dsimp only at eq
  have names : (fun i => M.binaryRowName s.nonbottom.carrier C ⊤ (function.value i)) =
      (fun i => M.internalRowName s C hL (positions i)) := by
    funext i
    rw [values i]
    rfl
  exact eq.trans (congrArg Subtype.val (congrArg (Name.indexedTuple ⊤ δ) names))

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem mem_rowTupleTerms (one mu I W rows S z : ZFSet.{u}) :
    z ∈ rowTupleTerms one mu I W rows S ↔
      ∃ f ∈ S, z = rowTupleCode one mu I W rows f := by
  rw [rowTupleTerms, mem_functionGraphRange]
  constructor
  · rintro ⟨f, hf, entry⟩
    exact ⟨f, hf, ((pair_mem_rowTupleFamily one mu I W rows S f z).1 entry).2⟩
  · rintro ⟨f, hf, equal⟩
    exact ⟨f, hf, (pair_mem_rowTupleFamily one mu I W rows S f z).2 ⟨hf, equal⟩⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {P : Type u} (c : Presentation P)
variable (one mu I W rows S : ZFSet.{u})
variable (valid : ∀ z ∈ (rowTupleTerms one mu I W rows S), IsName c z)

include valid

theorem pair_mem_liftedRowTupleFamily (f z : ZFSet.{u}) :
    ZFSet.pair f z ∈ (liftedRowTupleFamily c one mu I W rows S valid) ↔
      f ∈ S ∧ ∃ τ : Name c, τ.val = rowTupleCode one mu I W rows f ∧
        z = (Name.rename c.pairEmpty id τ).val := by
  rw [liftedRowTupleFamily, pair_mem_relationCompose]
  constructor
  · rintro ⟨hf, _, x, hx, tuple, rename⟩
    let τ : Name c := ⟨x, valid x hx⟩
    exact ⟨hf, τ, ((pair_mem_rowTupleFamily one mu I W rows S f x).1 tuple).2,
      ((Name.pair_mem_renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid τ z).1 rename).2⟩
  · rintro ⟨hf, τ, tuple, equal⟩
    have member : τ.val ∈ (rowTupleTerms one mu I W rows S) := (mem_rowTupleTerms one mu I W rows S τ.val).2 ⟨f, hf, tuple⟩
    have target : z ∈ (Name.renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid) := (Name.mem_renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid z).2
      ⟨τ, member, equal⟩
    exact ⟨hf, target, τ.val, member,
      (pair_mem_rowTupleFamily one mu I W rows S f τ.val).2 ⟨hf, tuple⟩,
      (Name.pair_mem_renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid τ z).2 ⟨member, equal⟩⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRowTermSetNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L]

theorem rowPositionSequence_decode (s : Presentation L)
    (hL : s.carrier ∈ M.sets) {mu f : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu)
    (member : f ∈ M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu) :
    f ∈ M.sets ∧ ∃ δ ∈ M.sets, ordinalSetProperty δ ∧ δ ⊆ mu ∧
      ∃ function : FunctionGraphOn δ f, ∃ positions : δ.toSet → {i : L // i ≠ ⊥},
        ∃ D : L, (∀ i, function.value i = s.encode (positions i).val) ∧
          ∀ i, (positions i).val ≤ D := by
  obtain ⟨hf, δ, hδ, ordδ, subδ, fn, d, hd, _, bounds⟩ :=
    M.rowPositionSequence_data hL hmu ordinal member
  let function : FunctionGraphOn δ f := ⟨s.nonbottom.carrier, fn⟩
  have range (i : δ.toSet) : function.value i ∈ s.nonbottom.carrier :=
    (ZFSet.pair_mem_prod.1 (fn.1 (function.value_entry i))).2
  have each (i : δ.toSet) : ∃ x : {i : L // i ≠ ⊥}, s.encode x.val = function.value i :=
    (s.nonbottom.mem_carrier (function.value i)).1 (range i)
  let positions (i : δ.toSet) : {i : L // i ≠ ⊥} := Classical.choose (each i)
  have values (i : δ.toSet) : function.value i = s.encode (positions i).val :=
    (Classical.choose_spec (each i)).symm
  obtain ⟨D, rfl⟩ := (s.mem_carrier d).1 hd
  refine ⟨hf, δ, hδ, ordδ, subδ, function, positions, D, values, ?_⟩
  intro i
  have bound := bounds i.val (function.value i) (function.value_entry i)
  rw [values i] at bound
  exact (s.pair_mem_conditionOrder (positions i).val D).1 bound

end

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedRowTupleSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem liftedRowTuple_supported {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ (valid : ∀ z ∈ T, IsName c z) (f : ZFSet.{u}) (τ : Name c.pairEmpty) (D : L),
      ZFSet.pair f τ.val ∈ liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
        (⋃₀ ⋃₀ rows) rows S valid →
      (∀ i x, ZFSet.pair i x ∈ f → ZFSet.pair x (s.encode D) ∈ s.conditionOrder) →
      a.principalFix D ≤ act.stabilizer c.pairEmpty τ := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid f τ D entry bounded
  obtain ⟨hf, σ, source, lifted⟩ := (pair_mem_liftedRowTupleFamily c (c.encode ⊤) mu
    s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid f τ.val).1 entry
  obtain ⟨_, δ, _, _, subset, function, positions, _, values, _⟩ :=
    M.rowPositionSequence_decode s hL hmu ordinal hf
  have bound (i : δ.toSet) : (positions i).val ≤ D := by
    have positionOrder := bounded i.val (function.value i) (function.value_entry i)
    rw [values i] at positionOrder
    exact (s.pair_mem_conditionOrder (positions i).val D).1 positionOrder
  have same : σ = M.internalRowTupleName s C hL δ positions :=
    Subtype.ext (source.trans (M.internalRowTupleCode_eq s C hL function subset positions values))
  have sameLift : τ = Name.presentationEquiv c c.pairEmpty
      (M.internalRowTupleName s C hL δ positions) := by
    apply Subtype.ext
    change τ.val = (Name.rename c.pairEmpty id (M.internalRowTupleName s C hL δ positions)).val
    rw [lifted, same]
  rw [sameLift, act.stabilizer_presentationEquiv]
  exact M.internalRowTupleName_supported a s b C pairing unions powers separation infinite
    hL hC hG graph δ positions D bound

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundQuantifiedGraphFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_allGraphFields {n} (graph : Fin n) (body : SetFormula (n + 2))
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (allGraphFields graph body) env ↔
      ∀ x y, ZFSet.pair x y ∈ env graph →
        Realize M.sets body (extend y (extend x env)) := by
  simp only [allGraphFields, Realize, realize_imp]
  constructor
  · intro holds x y entry
    have pairGround := M.transitive (members graph) entry
    have hx := M.pair_left pairGround
    have hy := M.pair_right pairGround
    exact holds x hx y hy ((BoundedFormula.realize_toFormula M _ _
      (Fin.cases hy (Fin.cases hx members))).2
        ((BoundedFormula.truth_pairMembershipFormula _ _ _ _).2 entry))
  · intro holds x hx y hy entry
    exact holds x y ((BoundedFormula.truth_pairMembershipFormula _ _ _ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hy (Fin.cases hx members))).1 entry))

end TransitiveGround
end PartitionPilot.Forcing

end

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



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preparationForcingFormula {n} (P order q nodes visibility z F f : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (preparationForcingFormula P order q nodes visibility z F f) env ↔
      PreparationForcingCode M (env P) (env order) (env q) (env nodes)
        (env visibility) (env z) (env F) (env f) := by
  rw [preparationForcingFormula, Realize, M.realize_allGraphFields _ _ env members,
    M.realize_allGraphFields _ _ env members]
  simp only [realize_imp, Realize, M.realize_stageOneForcingAt]
  have names (x y : ZFSet.{u}) :
      (fun j : Fin 2 => extend y (extend x env) (![z.succ.succ, 0] j)) = ![env z, y] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)) j
  simp only [names]
  rfl

end TransitiveGround

end PartitionPilot.Forcing


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GeneratedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot
universe u
variable {α : Type u} (P : MeetOrder α) (A : α → Prop)

theorem generatedMeetPredicate_least (F : Compression.MeetFilter P)
    (contains : ∀ a, A a → F.mem a) {x : α} (hx : generatedMeetPredicate P A x) : F.mem x := by
  obtain ⟨a, ha, b, path, lower⟩ := hx
  have hb : F.mem b := by
    clear lower
    induction path with
    | refl => exact contains a ha
    | tail path step ih =>
      obtain ⟨c, hc, rfl⟩ := step
      exact F.closed_meet ih (contains c hc)
  exact F.upward hb lower

theorem generatedMeetPredicate_lower_bound (e : α) (above : ∀ a, A a → P.le e a)
    {x : α} (hx : generatedMeetPredicate P A x) : P.le e x := by
  obtain ⟨a, ha, b, path, lower⟩ := hx
  have hb : P.le e b := by
    clear lower
    induction path with
    | refl => exact above a ha
    | tail path step ih =>
      obtain ⟨c, hc, rfl⟩ := step
      exact P.le_meet ih (above c hc)
  exact P.trans hb lower

end PartitionPilot

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMeetGeneratorSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem pair_mem_meetGeneratorSteps (P μ A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ meetGeneratorSteps P μ A ↔
      x ∈ P ∧ y ∈ P ∧ ∃ a ∈ A, ZFSet.pair (ZFSet.pair x a) y ∈ μ := by
  rw [meetGeneratorSteps, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, y', hy, a, ha, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hy, a, ha, entry⟩
  · rintro ⟨hx, hy, a, ha, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, a, ha, rfl, entry⟩

namespace BoundedFormula

theorem truth_meetGeneratorStepFormula {n} (z P μ A : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (meetGeneratorStepFormula z P μ A) env ↔
      ∃ x ∈ env P, ∃ y ∈ env P, ∃ a ∈ env A,
        env z = ZFSet.pair x y ∧ ZFSet.pair (ZFSet.pair x a) y ∈ env μ := by
  simp only [meetGeneratorStepFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

end BoundedFormula

theorem TransitiveGround.meetGeneratorSteps_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P μ A : ZFSet.{u}} (hP : P ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) :
    meetGeneratorSteps P μ A ∈ M.sets := by
  let params := extend P (extend μ (extend A Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.meetGeneratorStepFormula 0 1 2 3) params
    (Fin.cases hP (Fin.cases hμ (Fin.cases hA (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hP hP)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.meetGeneratorStepFormula 0 1 2 3) (extend z params))
      (ZFSet.prod P P) = meetGeneratorSteps P μ A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, meetGeneratorSteps, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_meetGeneratorStepFormula _ _ _ _ _)
  exact equal ▸ selected

theorem MeetOrderCode.meetGeneratorSteps_iff {P r μ A : ZFSet.{u}}
    (code : MeetOrderCode P r μ) (subset : A ⊆ P) (x y : SetMembers P) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ meetGeneratorSteps P μ A ↔
      meetGeneratorStep code.toSmallMeetOrder (fun a => SetMembers.raw a ∈ A) x y := by
  rw [pair_mem_meetGeneratorSteps]
  constructor
  · rintro ⟨_, _, a, ha, entry⟩
    refine ⟨SetMembers.ofMem a (subset ha), ?_, ?_⟩
    · simpa only [SetMembers.raw_ofMem] using ha
    · apply Eq.symm
      apply (code.toSmallMeetOrder_meet_eq_iff _ _ _).2
      simpa only [SetMembers.raw_ofMem] using entry
  · rintro ⟨a, ha, equal⟩
    exact ⟨SetMembers.raw_mem x, SetMembers.raw_mem y, SetMembers.raw a, ha,
      (code.toSmallMeetOrder_meet_eq_iff _ _ _).1 equal.symm⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundTestedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem generatedMeetFilter_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P r μ A : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) : M.generatedMeetFilter P r μ A ∈ M.sets :=
  M.relationImage_mem separation
    (M.relationImage_mem separation hA hP
      (M.finitePathClosure_mem pairing unions powers separation infinite hP
        (M.meetGeneratorSteps_mem pairing unions powers separation hP hμ hA))) hP hr

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions separation infinite

theorem generatedMeetFilter_small_iff {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) (x : SetMembers P) :
    SetMembers.raw x ∈ M.generatedMeetFilter P r μ A ↔
      generatedMeetPredicate code.toSmallMeetOrder (fun a => SetMembers.raw a ∈ A) x := by
  have paths := M.pair_mem_finitePathClosure pairing unions separation infinite
    (SetMembers.presentation P) (meetGeneratorStep code.toSmallMeetOrder
      (fun a => SetMembers.raw a ∈ A)) (code.meetGeneratorSteps_iff subset) hP
  rw [generatedMeetFilter, mem_relationImage]
  constructor
  · rintro ⟨_, b, hb, lower⟩
    obtain ⟨hbP, a, ha, path⟩ := (mem_relationImage _ _ _ b).1 hb
    let a' := SetMembers.ofMem a (subset ha)
    let b' := SetMembers.ofMem b hbP
    have path' : ZFSet.pair (SetMembers.raw a') (SetMembers.raw b') ∈
        M.finitePathClosure P (meetGeneratorSteps P μ A) := by
      simpa only [a', b', SetMembers.raw_ofMem] using path
    refine ⟨a', ?_, b', (paths a' b').1 path', ?_⟩
    · simpa only [a', SetMembers.raw_ofMem] using ha
    · change ZFSet.pair (SetMembers.raw b') (SetMembers.raw x) ∈ r
      simpa only [b', SetMembers.raw_ofMem] using lower
  · rintro ⟨a, ha, b, path, lower⟩
    exact ⟨SetMembers.raw_mem x, SetMembers.raw b,
      (mem_relationImage _ _ _ _).2 ⟨SetMembers.raw_mem b, SetMembers.raw a, ha,
        (paths a b).2 path⟩, lower⟩

theorem generatedMeetFilter_contains {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) :
    A ⊆ M.generatedMeetFilter P r μ A := by
  intro x hx
  have member := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset
    (SetMembers.ofMem x (subset hx))).2
      (generatedMeetPredicate_contains code.toSmallMeetOrder _
        (by simpa only [SetMembers.raw_ofMem] using hx))
  simpa only [SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_filter {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) (nonempty : A.Nonempty) :
    MeetFilterCode P r μ (M.generatedMeetFilter P r μ A) := by
  have exactMem := M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset
  have typedNonempty : ∃ a : SetMembers P, SetMembers.raw a ∈ A := by
    obtain ⟨a, ha⟩ := nonempty
    exact ⟨SetMembers.ofMem a (subset ha), by
      simpa only [SetMembers.raw_ofMem] using (show a ∈ A from ha)⟩
  let typed := PartitionPilot.generatedMeetFilter code.toSmallMeetOrder
    (fun a => SetMembers.raw a ∈ A) typedNonempty
  have bounded : M.generatedMeetFilter P r μ A ⊆ P :=
    fun x hx => ((mem_relationImage _ _ _ x).1 hx).1
  refine ⟨bounded, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty
    exact ⟨a, M.generatedMeetFilter_contains pairing unions separation infinite hP code subset ha⟩
  · intro x hx y hy lower
    let x' := SetMembers.ofMem x (bounded hx)
    let y' := SetMembers.ofMem y hy
    have hx' : typed.mem x' := (exactMem x').1 (by simpa only [x', SetMembers.raw_ofMem] using hx)
    have lower' : code.toSmallMeetOrder.le x' y' := by
      change ZFSet.pair (SetMembers.raw x') (SetMembers.raw y') ∈ r
      simpa only [x', y', SetMembers.raw_ofMem] using lower
    have member := (exactMem y').2 (typed.upward hx' lower')
    simpa only [y', SetMembers.raw_ofMem] using member
  · intro x hx y hy z entry
    have hz := (ZFSet.pair_mem_prod.1 (code.operation.1 entry)).2
    let x' := SetMembers.ofMem x (bounded hx)
    let y' := SetMembers.ofMem y (bounded hy)
    let z' := SetMembers.ofMem z hz
    have hx' : typed.mem x' := (exactMem x').1 (by simpa only [x', SetMembers.raw_ofMem] using hx)
    have hy' : typed.mem y' := (exactMem y').1 (by simpa only [y', SetMembers.raw_ofMem] using hy)
    have equal : code.toSmallMeetOrder.meet x' y' = z' :=
      (code.toSmallMeetOrder_meet_eq_iff x' y' z').2
        (by simpa only [x', y', z', SetMembers.raw_ofMem] using entry)
    have member := (exactMem z').2 (equal ▸ typed.closed_meet hx' hy')
    simpa only [z', SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_least {P r μ A F : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P)
    (filter : MeetFilterCode P r μ F) (contains : A ⊆ F) :
    M.generatedMeetFilter P r μ A ⊆ F := by
  let typed : Compression.MeetFilter code.toSmallMeetOrder := {
    mem := fun x => SetMembers.raw x ∈ F
    nonempty := by
      obtain ⟨x, hx⟩ := filter.nonempty
      exact ⟨SetMembers.ofMem x (filter.subset hx), by
        simpa only [SetMembers.raw_ofMem] using (show x ∈ F from hx)⟩
    upward := fun {x y} hx lower => filter.upward _ hx _ (SetMembers.raw_mem y) lower
    closed_meet := fun {x y} hx hy => filter.closed_meet _ hx _ hy _ (code.smallMeet_entry x y) }
  intro x hx
  have hxP := ((mem_relationImage _ _ _ x).1 hx).1
  let x' := SetMembers.ofMem x hxP
  have predicate := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset x').1
    (by simpa only [x', SetMembers.raw_ofMem] using hx)
  have member := generatedMeetPredicate_least code.toSmallMeetOrder _ typed
    (fun a ha => contains ha) predicate
  simpa only [typed, x', SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_lower_bound {P r μ A e : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P)
    (he : e ∈ P) (above : ∀ a ∈ A, ZFSet.pair e a ∈ r) :
    ∀ x ∈ M.generatedMeetFilter P r μ A, ZFSet.pair e x ∈ r := by
  intro x hx
  have hxP := ((mem_relationImage _ _ _ x).1 hx).1
  let x' := SetMembers.ofMem x hxP
  let e' := SetMembers.ofMem e he
  have predicate := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset x').1
    (by simpa only [x', SetMembers.raw_ofMem] using hx)
  have lower := generatedMeetPredicate_lower_bound code.toSmallMeetOrder _ e'
    (fun a ha => by
      change ZFSet.pair (SetMembers.raw e') (SetMembers.raw a) ∈ r
      simpa only [e', SetMembers.raw_ofMem] using above _ ha) predicate
  change ZFSet.pair (SetMembers.raw e') (SetMembers.raw x') ∈ r at lower
  simpa only [e', x', SetMembers.raw_ofMem] using lower

end TransitiveGround

universe u

end PartitionPilot.Forcing

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

theorem mem_assignmentIndices (I T A t : ZFSet.{u}) :
    t ∈ assignmentIndices I T A ↔
      t ∈ I ∧ ∃ u ∈ T, ∃ w ∈ T, stageOneAssignment t u w ∈ A := by
  rw [assignmentIndices, mem_relationImage]
  constructor
  · rintro ⟨ht, z, hz, entry⟩
    obtain ⟨i, _, rest, hr, equal⟩ := (mem_productFirst I (ZFSet.prod T T) _).1 entry
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨u, hu, w, hw, rfl⟩ := ZFSet.mem_prod.1 hr
    exact ⟨ht, u, hu, w, hw, hz⟩
  · rintro ⟨ht, u, hu, w, hw, member⟩
    exact ⟨ht, stageOneAssignment t u w, member,
      (mem_productFirst I (ZFSet.prod T T) _).2
        ⟨t, ht, ZFSet.pair u w, ZFSet.pair_mem_prod.2 ⟨hu, hw⟩, rfl⟩⟩

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

theorem assignmentIndices_mem {I T A : ZFSet.{u}}
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentIndices I T A ∈ M.sets :=
  M.relationImage_mem separation hA hI (M.productFirst_mem pairing unions powers separation
    hI (M.prod_mem pairing unions powers separation hT hT))

theorem assignmentOnIndices_mem {B T A : ZFSet.{u}}
    (hB : B ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentOnIndices B T A ∈ M.sets :=
  M.bounded_separation_mem separation (.mem 0 1)
    (extend (stageOneAssignments B T) Fin.elim0)
    (Fin.cases (M.stageOneAssignments_mem pairing unions powers separation hB hT)
      (fun i => Fin.elim0 i)) hA

theorem assignmentIndices_small
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I T A N : ZFSet.{u}} (hI : I ∈ M.sets) (hT : T ∈ M.sets)
    (hA : A ∈ M.sets) (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentIndices I T A) N :=
  M.groundEmbeddable_function_image pairing unions powers separation choice hA hI hN
    (M.productFirst_mem pairing unions powers separation hI
      (M.prod_mem pairing unions powers separation hT hT)) (productFirst_function I (ZFSet.prod T T)) small

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



namespace PartitionPilot.Forcing
universe u

theorem stageOneRawTests_mixed_union (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    {A B lower : ZFSet.{u}} (first : stageOneRawTests M d A lower)
    (second : stageOneRawTests M d B lower)
    (cross : stageOneRawCrossCollisions M d A B lower) :
    stageOneRawTests M d (A ∪ B) lower := by
  refine ⟨?_, ?_⟩
  · intro t ht u hu w hw entry
    exact (ZFSet.mem_union.1 entry).elim
      (first.1 t ht u hu w hw) (second.1 t ht u hu w hw)
  · intro t ht u hu u' hu' w hw w' hw' entry entry'
    rcases ZFSet.mem_union.1 entry with entry | entry
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact first.2 t ht u hu u' hu' w hw w' hw' entry entry'
      · exact (cross t ht u hu u' hu' w hw w' hw' entry entry').1
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact (cross t ht u' hu' u hu w' hw' w hw entry' entry).2
      · exact second.2 t ht u hu u' hu' w hw w' hw' entry entry'





end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem storedPreparationRequests_mem {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (fields : Fin 15 → ZFSet.{u}) (members : ∀ j, fields j ∈ M.sets) :
    M.storedPreparationRequests A fields ∈ M.sets :=
  (M.definable_storedPreparationRequests pairing unions powers separation).closed
    (extend A fields) (Fin.cases hA members)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RowAssignmentTransitionFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace BoundedFormula

private theorem truth_cutGraphProductMember {n : Nat} (z upper lower : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (cutGraphProductMember z upper lower) env ↔ env z ∈ ZFSet.prod (env upper) (env lower) := by
  simp only [cutGraphProductMember, truth_exMem, truth_orderedPairFormula]
  constructor
  · rintro ⟨x, hx, y, hy, equal⟩
    change env z = ZFSet.pair x y at equal
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
  · intro hz
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 hz
    exact ⟨x, hx, y, hy, equal⟩
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_rowAssignmentCutGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n : Nat} (output upper lower levels alpha : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (rowAssignmentCutGraphFormula output upper lower levels alpha) env ↔
      env output = rowAssignmentCutGraph (env upper) (env lower) (env levels) (env alpha) := by
  have ground := M.rowAssignmentCutGraph_mem pairing unions powers separation
    (members upper) (members lower) (members levels) (members alpha)
  apply M.realize_exactSetFormula output _ env (members output) (fun _ hz => M.transitive ground hz)
  intro z hz
  have allGround : ∀ j, (extend z env) j ∈ M.sets := Fin.cases hz members
  change (Realize M.sets (BoundedFormula.cutGraphProductMember 0 upper.succ lower.succ).toFormula
      (extend z env) ∧ Realize M.sets (rowAssignmentCutFormula 0 levels.succ alpha.succ)
      (extend z env)) ↔ _
  rw [BoundedFormula.realize_toFormula M _ _ allGround,
    BoundedFormula.truth_cutGraphProductMember,
    M.realize_rowAssignmentCutFormula 0 levels.succ alpha.succ _ allGround]
  exact (mem_rowAssignmentCutGraph _ _ _ _ z).symm

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFinalInsertionExceptions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.FinalInsertionFamiliesCode
open SetRealization
universe u
variable {Labels P G r μ A c e d F caps actors : ZFSet.{u}}

theorem decodedCaps_entry
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (label : SetMembers Labels) :
    ZFSet.pair (SetMembers.raw label) (SetMembers.raw (family.decodedCaps label)) ∈ caps :=
  (SetMembers.presentation Labels).decodeFunction_mem (SetMembers.presentation P)
    caps family.cap_injection.function label

theorem decodedActors_entry
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (label : SetMembers Labels) :
    ZFSet.pair (SetMembers.raw label) (SetMembers.raw (family.decodedActors label)) ∈ actors :=
  (SetMembers.presentation Labels).decodeFunction_mem (SetMembers.presentation G)
    actors family.actor_injection.function label

end PartitionPilot.Forcing.FinalInsertionFamiliesCode



namespace PartitionPilot.Forcing
open SetFormula
universe u

private theorem pair_mem_capExceptionRelation
    (profiles : Bool) (S Labels P r c caps x label : ZFSet.{u}) :
    ZFSet.pair x label ∈ capExceptionRelation profiles S Labels P r c caps ↔
      x ∈ S ∧ label ∈ Labels ∧ ∃ cap ∈ P, ZFSet.pair label cap ∈ caps ∧
        capExceptionTest profiles r c x cap := by
  rw [capExceptionRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hy, l, hl, cap, hcap, eq, entry, test⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hy, hl, cap, hcap, entry, test⟩
  · rintro ⟨hx, hl, cap, hcap, entry, test⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hl⟩, x, hx, label, hl, cap, hcap,
      rfl, entry, test⟩

private theorem truth_capExceptionEntryFormula {n}
    (profiles : Bool) (z s labels p r c caps : Fin n) (env : Fin n → ZFSet.{u}) :
    BoundedFormula.Truth (capExceptionEntryFormula profiles z s labels p r c caps) env ↔
      ∃ x ∈ env s, ∃ label ∈ env labels, ∃ cap ∈ env p,
        env z = ZFSet.pair x label ∧ ZFSet.pair label cap ∈ env caps ∧
          capExceptionTest profiles (env r) (env c) x cap := by
  cases profiles <;>
    simp only [capExceptionEntryFormula, capExceptionTest, Bool.false_eq_true, ↓reduceIte,
      BoundedFormula.truth_exMem, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_pairMembershipFormula] <;> rfl

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

private theorem capExceptionRelation_mem
    (profiles : Bool) {S Labels P r c caps : ZFSet.{u}}
    (hS : S ∈ M.sets) (hLabels : Labels ∈ M.sets) (hP : P ∈ M.sets)
    (hr : r ∈ M.sets) (hc : c ∈ M.sets) (hCaps : caps ∈ M.sets) :
    capExceptionRelation profiles S Labels P r c caps ∈ M.sets := by
  let params := extend S (extend Labels (extend P (extend r (extend c (extend caps Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (capExceptionEntryFormula profiles 0 1 2 3 4 5 6) params
    (Fin.cases hS (Fin.cases hLabels (Fin.cases hP (Fin.cases hr
      (Fin.cases hc (Fin.cases hCaps (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hS hLabels)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (capExceptionEntryFormula profiles 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod S Labels) = capExceptionRelation profiles S Labels P r c caps := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, capExceptionRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (truth_capExceptionEntryFormula profiles 0 1 2 3 4 5 6 _)
  exact eq ▸ selected

private theorem partial_image_countable
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S Labels rel : ZFSet.{u}} (hS : S ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hRel : rel ∈ M.sets) (code : PartialFunctionCode S Labels rel)
    (smallS : M.groundEmbeddable S ZFSet.omega) :
    M.groundEmbeddable (relationImage S Labels rel) ZFSet.omega := by
  have hImage := M.relationImage_mem separation hS hLabels hRel
  have restricted : PartialFunctionCode S (relationImage S Labels rel) rel := by
    refine ⟨?_, code.unique⟩
    intro z hz
    obtain ⟨x, hx, label, hl, rfl⟩ := ZFSet.mem_prod.1 (code.shape hz)
    exact ZFSet.pair_mem_prod.2 ⟨hx, (mem_relationImage _ _ _ _).2 ⟨hl, x, hx, hz⟩⟩
  obtain ⟨f, hf, injection⟩ := M.groundEmbeddable_of_partial_surjection
    pairing unions powers separation choice hS hImage hRel restricted
    (fun label member => ((mem_relationImage _ _ _ label).1 member).2)
  obtain ⟨g, hg, count⟩ := smallS
  exact ⟨relationCompose (relationImage S Labels rel) S ZFSet.omega f g,
    M.relationCompose_mem pairing unions powers separation hImage hS
      (M.omega_mem separation infinite) hf hg, injection.compose count⟩
end TransitiveGround

namespace FinalInsertionFamiliesCode

theorem exists_ground_countable_exceptions
    {Labels P G r μ A c e d F caps actors Used Profiles extra : ZFSet.{u}}
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLabels : Labels ∈ M.sets) (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hc : c ∈ M.sets) (hCaps : caps ∈ M.sets)
    (hUsed : Used ∈ M.sets) (hProfiles : Profiles ∈ M.sets) (hExtra : extra ∈ M.sets)
    (meet : MeetOrderCode P r μ) (usedSubset : Used ⊆ P)
    (filters : ∀ profile ∈ Profiles, MeetFilterCode P r μ profile)
    (smallUsed : M.groundEmbeddable Used ZFSet.omega)
    (smallProfiles : M.groundEmbeddable Profiles ZFSet.omega)
    (smallExtra : M.groundEmbeddable extra ZFSet.omega) (extraSubset : extra ⊆ Labels) :
    ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ extra ⊆ bad ∧
      ∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
        (∀ node ∈ Used, ZFSet.pair node cap ∈ r → ZFSet.pair node c ∈ r) ∧
        (∀ profile ∈ Profiles, c ∉ profile → cap ∉ profile) := by
  classical
  let nodes := capExceptionRelation false Used Labels P r c caps
  let profiles := capExceptionRelation true Profiles Labels P r c caps
  have hNodes : nodes ∈ M.sets := M.capExceptionRelation_mem pairing unions powers separation
    false hUsed hLabels hP hr hc hCaps
  have hProfilesRel : profiles ∈ M.sets := M.capExceptionRelation_mem pairing unions powers separation
    true hProfiles hLabels hP hr hc hCaps
  have nodesPartial : PartialFunctionCode Used Labels nodes := by
    refine ⟨fun _ entry => (ZFSet.mem_sep.1 entry).1, ?_⟩
    intro node first second one two
    obtain ⟨used, _, cap₁, _, entry₁, negative, below₁⟩ :=
      (pair_mem_capExceptionRelation false Used Labels P r c caps node first).1 one
    obtain ⟨_, _, cap₂, _, entry₂, _, below₂⟩ :=
      (pair_mem_capExceptionRelation false Used Labels P r c caps node second).1 two
    by_contra different
    exact negative (meet.greatest cap₁ cap₂ c node (usedSubset used)
      (family.meets first second cap₁ cap₂ entry₁ entry₂ different) below₁ below₂)
  have profilesPartial : PartialFunctionCode Profiles Labels profiles := by
    refine ⟨fun _ entry => (ZFSet.mem_sep.1 entry).1, ?_⟩
    intro profile first second one two
    obtain ⟨used, _, cap₁, _, entry₁, negative, positive₁⟩ :=
      (pair_mem_capExceptionRelation true Profiles Labels P r c caps profile first).1 one
    obtain ⟨_, _, cap₂, _, entry₂, _, positive₂⟩ :=
      (pair_mem_capExceptionRelation true Profiles Labels P r c caps profile second).1 two
    by_contra different
    exact negative ((filters profile used).closed_meet cap₁ positive₁ cap₂ positive₂ c
      (family.meets first second cap₁ cap₂ entry₁ entry₂ different))
  let nodeBad := relationImage Used Labels nodes
  let profileBad := relationImage Profiles Labels profiles
  have hNodeBad : nodeBad ∈ M.sets := M.relationImage_mem separation hUsed hLabels hNodes
  have hProfileBad : profileBad ∈ M.sets := M.relationImage_mem separation hProfiles hLabels hProfilesRel
  have nodeSmall := M.partial_image_countable pairing unions powers separation infinite choice
    hUsed hLabels hNodes nodesPartial smallUsed
  have profileSmall := M.partial_image_countable pairing unions powers separation infinite choice
    hProfiles hLabels hProfilesRel profilesPartial smallProfiles
  have hBoth := M.binary_union_mem pairing unions hNodeBad hProfileBad
  have smallBoth := M.groundCountable_binary_union pairing unions powers separation infinite choice
    hNodeBad hProfileBad nodeSmall profileSmall
  refine ⟨(nodeBad ∪ profileBad) ∪ extra, M.binary_union_mem pairing unions hBoth hExtra, ?_,
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      hBoth hExtra smallBoth smallExtra, ?_, ?_⟩
  · intro label member
    rcases ZFSet.mem_union.1 member with both | more
    · rcases ZFSet.mem_union.1 both with node | profile
      · exact ((mem_relationImage _ _ _ _).1 node).1
      · exact ((mem_relationImage _ _ _ _).1 profile).1
    · exact extraSubset more
  · intro label member
    exact ZFSet.mem_union.2 (Or.inr member)
  · intro label cap entry good
    have bounds := ZFSet.pair_mem_prod.1 (family.cap_injection.function.1 entry)
    constructor
    · intro node used below
      by_contra negative
      apply good
      apply ZFSet.mem_union.2 ∘ Or.inl
      apply ZFSet.mem_union.2 ∘ Or.inl
      exact (mem_relationImage _ _ _ _).2 ⟨bounds.1, node, used,
        (pair_mem_capExceptionRelation false Used Labels P r c caps node label).2
          ⟨used, bounds.1, cap, bounds.2, entry, negative, below⟩⟩
    · intro profile used negative positive
      apply good
      apply ZFSet.mem_union.2 ∘ Or.inl
      apply ZFSet.mem_union.2 ∘ Or.inr
      exact (mem_relationImage _ _ _ _).2 ⟨bounds.1, profile, used,
        (pair_mem_capExceptionRelation true Profiles Labels P r c caps profile label).2
          ⟨used, bounds.1, cap, bounds.2, entry, negative, positive⟩⟩

end FinalInsertionFamiliesCode
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainLimitCoverageFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_certificateGraphEntryAt {n} (j F B f k : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (certificateGraphEntryAt j F B f k) env ↔
      ZFSet.pair (env j) (ZFSet.pair (env F) (ZFSet.pair (env B) (env f))) ∈ env k := by
  simp only [certificateGraphEntryAt, truth_exGraphFields, Truth,
    truth_exPairFields, truth_orderedPairFormula]
  change (∃ key certificate, ZFSet.pair key certificate ∈ env k ∧ key = env j ∧
    ∃ profile tail, certificate = ZFSet.pair profile tail ∧ profile = env F ∧
      tail = ZFSet.pair (env B) (env f)) ↔ _
  constructor
  · rintro ⟨key, certificate, entry, rfl, profile, tail, rfl, rfl, rfl⟩
    exact entry
  · intro entry
    exact ⟨env j, _, entry, rfl, env F, _, rfl, rfl, rfl⟩

theorem truth_enumerationGraphEntryAt {n} (j e names g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (enumerationGraphEntryAt j e names g) env ↔
      ZFSet.pair (env j) (ZFSet.pair (env e) (env names)) ∈ env g := by
  simp only [enumerationGraphEntryAt, truth_exGraphFields, Truth, truth_orderedPairFormula]
  change (∃ key pair, ZFSet.pair key pair ∈ env g ∧ key = env j ∧
    pair = ZFSet.pair (env e) (env names)) ↔ _
  constructor
  · rintro ⟨key, pair, entry, rfl, rfl⟩
    exact entry
  · intro entry
    exact ⟨env j, _, entry, rfl, rfl⟩





end PartitionPilot.Forcing.BoundedFormula

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



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_visibilitySupportAt {n} (node tau nodes names visibility top : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (visibilitySupportAt node tau nodes names visibility top) env ↔
      ZFSet.pair (env node) (env tau) ∈ visibilitySupportIncidence
        (env nodes) (env names) (env visibility) (env top) := by
  simp only [visibilitySupportAt, Truth, truth_exGraphFields, truth_pairMembershipFormula]
  rw [pair_mem_visibilitySupportIncidence]
  change (env node ∈ env nodes ∧ env tau ∈ env names ∧
    ∃ v V, ZFSet.pair v V ∈ env visibility ∧ v = env node ∧
      ZFSet.pair (env tau) (env top) ∈ V) ↔ _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨v, V, edge, rfl, member⟩
    exact ⟨V, edge, member⟩
  · rintro ⟨V, edge, member⟩
    exact ⟨env node, V, edge, rfl, member⟩

end PartitionPilot.Forcing.BoundedFormula

end

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

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preparedCertificateFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega z F B f e names : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meetCode : MeetOrderCode (env nodes) (env nodeOrder) (env meet)) :
    Realize M.sets
      (preparedCertificateFormula P order q nodes nodeOrder meet N visibility top omega z F B f e names) env ↔
      PreparedCertificateCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
        (env meet) (env N) (env visibility) (env top) (env omega) (env z)
        (env F) (env B) (env f) (env e) (env names) := by
  have nonempty : Realize M.sets (BoundedFormula.exMem B (.equal 0 0)).toFormula env ↔
      (env B).Nonempty := by
    rw [BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_exMem]
    simp only [BoundedFormula.Truth, and_true]
    rfl
  have supported : Realize M.sets (allGraphFields f
      (BoundedFormula.visibilitySupportAt 1 0 nodes.succ.succ N.succ.succ
        visibility.succ.succ top.succ.succ).toFormula) env ↔
      ∀ v tau, ZFSet.pair v tau ∈ env f →
        ZFSet.pair v tau ∈ visibilitySupportIncidence (env nodes) (env N) (env visibility) (env top) := by
    rw [M.realize_allGraphFields _ _ env members]
    constructor
    · intro holds v tau entry
      have pairGround := M.transitive (members f) entry
      exact (BoundedFormula.truth_visibilitySupportAt _ _ _ _ _ _ _).1
        ((BoundedFormula.realize_toFormula M _ _
          (Fin.cases (M.pair_right pairGround) (Fin.cases (M.pair_left pairGround) members))).1
            (holds v tau entry))
    · intro holds v tau entry
      have pairGround := M.transitive (members f) entry
      exact (BoundedFormula.realize_toFormula M _ _
        (Fin.cases (M.pair_right pairGround) (Fin.cases (M.pair_left pairGround) members))).2
          ((BoundedFormula.truth_visibilitySupportAt _ _ _ _ _ _ _).2 (holds v tau entry))
  simp only [preparedCertificateFormula, Realize]
  rw [BoundedFormula.realize_meetFilterFormula M _ _ _ _ env members meetCode,
    BoundedFormula.realize_coinitialBelowFormula M _ _ _ _ env members,
    nonempty, BoundedFormula.realize_toFormula M _ env members,
    BoundedFormula.truth_synchronizedEnumerationFormula, supported,
    M.realize_preparationForcingFormula _ _ _ _ _ _ _ _ env members]
  rfl

end TransitiveGround

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

theorem supportedEqualityCertificateBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.supportedEqualityCertificateBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation (M.groundPower_mem powers hNodes)
    (M.prod_mem pairing unions powers separation
      (M.groundSmallSubsets_mem powers separation hNodes omega)
      (M.groundRelations_mem pairing unions powers separation hNodes hN))

end TransitiveGround

end PartitionPilot.Forcing

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

end TransitiveGround

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preparedCertificateFamilyFormula {n}
    (P order q nodes nodeOrder meet N visibility top omega J C E k enumerations : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meetCode : MeetOrderCode (env nodes) (env nodeOrder) (env meet)) :
    Realize M.sets
      (preparedCertificateFamilyFormula P order q nodes nodeOrder meet N visibility top omega J C E k enumerations) env ↔
      PreparedCertificateFamilyCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
        (env meet) (env N) (env visibility) (env top) (env omega) (env J)
        (env C) (env E) (env k) (env enumerations) := by
  have entries : Realize M.sets
      (SetFormula.preparedFamilyEntries P order q nodes nodeOrder meet N visibility top omega k enumerations) env ↔
      ∀ z F B f e names, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ env k →
        ZFSet.pair z (ZFSet.pair e names) ∈ env enumerations →
        PreparedCertificateCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
          (env meet) (env N) (env visibility) (env top) (env omega) z F B f e names := by
    let body := SetFormula.imp
      (.conj (BoundedFormula.certificateGraphEntryAt 5 4 3 2 k.succ.succ.succ.succ.succ.succ).toFormula
        (BoundedFormula.enumerationGraphEntryAt 5 1 0 enumerations.succ.succ.succ.succ.succ.succ).toFormula)
      (preparedCertificateFormula P.succ.succ.succ.succ.succ.succ order.succ.succ.succ.succ.succ.succ
        q.succ.succ.succ.succ.succ.succ nodes.succ.succ.succ.succ.succ.succ
        nodeOrder.succ.succ.succ.succ.succ.succ meet.succ.succ.succ.succ.succ.succ
        N.succ.succ.succ.succ.succ.succ visibility.succ.succ.succ.succ.succ.succ
        top.succ.succ.succ.succ.succ.succ omega.succ.succ.succ.succ.succ.succ 5 4 3 2 1 0)
    have meaning (z F B f e names : ZFSet.{u})
        (hz : z ∈ M.sets) (hF : F ∈ M.sets) (hB : B ∈ M.sets)
        (hf : f ∈ M.sets) (he : e ∈ M.sets) (hn : names ∈ M.sets) :
        Realize M.sets body (extend names (extend e (extend f (extend B (extend F (extend z env)))))) ↔
        (ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ env k ∧
          ZFSet.pair z (ZFSet.pair e names) ∈ env enumerations →
          PreparedCertificateCode M (env P) (env order) (env q) (env nodes) (env nodeOrder)
            (env meet) (env N) (env visibility) (env top) (env omega) z F B f e names) := by
      have extended : ∀ i, (extend names (extend e (extend f (extend B (extend F (extend z env)))))) i ∈ M.sets := Fin.cases hn (Fin.cases he (Fin.cases hf
        (Fin.cases hB (Fin.cases hF (Fin.cases hz members)))))
      dsimp only [body]
      rw [realize_imp, Realize, BoundedFormula.realize_toFormula M _ _ extended,
        BoundedFormula.truth_certificateGraphEntryAt, BoundedFormula.realize_toFormula M _ _ extended,
        BoundedFormula.truth_enumerationGraphEntryAt,
        M.realize_preparedCertificateFormula
          P.succ.succ.succ.succ.succ.succ order.succ.succ.succ.succ.succ.succ
          q.succ.succ.succ.succ.succ.succ nodes.succ.succ.succ.succ.succ.succ
          nodeOrder.succ.succ.succ.succ.succ.succ meet.succ.succ.succ.succ.succ.succ
          N.succ.succ.succ.succ.succ.succ visibility.succ.succ.succ.succ.succ.succ
          top.succ.succ.succ.succ.succ.succ omega.succ.succ.succ.succ.succ.succ
          5 4 3 2 1 0 _ extended meetCode]
      rfl
    change (∀ z ∈ M.sets, ∀ F ∈ M.sets, ∀ B ∈ M.sets, ∀ f ∈ M.sets,
      ∀ e ∈ M.sets, ∀ names ∈ M.sets,
      Realize M.sets body (extend names (extend e (extend f (extend B (extend F (extend z env))))))) ↔ _
    constructor
    · intro holds z F B f e names stored enumerated
      have kc := M.pair_right (M.transitive (members k) stored)
      have ec := M.pair_right (M.transitive (members enumerations) enumerated)
      have hz := M.pair_left (M.transitive (members k) stored)
      have hF := M.pair_left kc
      have hB := M.pair_left (M.pair_right kc)
      have hf := M.pair_right (M.pair_right kc)
      have he := M.pair_left ec
      have hn := M.pair_right ec
      exact (meaning z F B f e names hz hF hB hf he hn).1
        (holds z hz F hF B hB f hf e he names hn) ⟨stored, enumerated⟩
    · intro holds z hz F hF B hB f hf e he names hn
      exact (meaning z F B f e names hz hF hB hf he hn).2
        (fun h => holds z F B f e names h.1 h.2)
  simp only [preparedCertificateFamilyFormula, Realize]
  rw [BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_functionFormula,
    BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_functionFormula, entries]
  rfl

end TransitiveGround

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem certificateProfileGraph_function {J nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k) :
    ZFSet.IsFunc J (M.groundPower nodes) (M.certificateProfileGraph J nodes W k) :=
  relationCompose_function_of_subset function
    (productFirst_function (M.groundPower nodes)
      (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes W)))
    (fun _ member => member)

theorem pair_mem_certificateProfileGraph {J nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (z F : ZFSet.{u}) :
    ZFSet.pair z F ∈ M.certificateProfileGraph J nodes W k ↔
      ∃ B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k := by
  rw [certificateProfileGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, value, _, edge, projection⟩
    obtain ⟨profile, hp, tail, ht, equal⟩ := (mem_productFirst _ _ _).1 projection
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨B, hB, f, hf, rfl⟩ := ZFSet.mem_prod.1 ht
    exact ⟨B, f, edge⟩
  · rintro ⟨B, f, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have fields := ZFSet.pair_mem_prod.1 bounds.2
    exact ⟨bounds.1, fields.1, _, bounds.2, edge,
      (mem_productFirst _ _ _).2 ⟨F, fields.1, _, fields.2, rfl⟩⟩

theorem mem_certificateProfileImage {J nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (F : ZFSet.{u}) :
    F ∈ M.certificateProfileImage J nodes W k ↔
      ∃ z B f, ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k := by
  rw [certificateProfileImage, mem_relationImage]
  constructor
  · rintro ⟨_, z, _, edge⟩
    obtain ⟨B, f, selected⟩ := (M.pair_mem_certificateProfileGraph function z F).1 edge
    exact ⟨z, B, f, selected⟩
  · rintro ⟨z, B, f, edge⟩
    have projected := (M.pair_mem_certificateProfileGraph function z F).2 ⟨B, f, edge⟩
    have bounds := ZFSet.pair_mem_prod.1 ((M.certificateProfileGraph_function function).1 projected)
    exact ⟨bounds.2, z, bounds.1, projected⟩

theorem certificateProfileGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J nodes W k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hW : W ∈ M.sets) (hk : k ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.certificateProfileGraph J nodes W k ∈ M.sets := by
  have hProfiles := M.groundPower_mem powers hNodes
  have hTail := M.prod_mem pairing unions powers separation
    (M.groundSmallSubsets_mem powers separation hNodes omega)
    (M.groundRelations_mem pairing unions powers separation hNodes hW)
  exact M.relationCompose_mem pairing unions powers separation hJ
    (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega)
    hProfiles hk (M.productFirst_mem pairing unions powers separation hProfiles hTail)

theorem certificateProfileImage_mem_small
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J nodes W k : ZFSet.{u}} (hJ : J ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (hW : W ∈ M.sets) (hk : k ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (smallJ : M.groundEmbeddable J ZFSet.omega) :
    M.certificateProfileImage J nodes W k ∈ M.sets ∧
      M.groundEmbeddable (M.certificateProfileImage J nodes W k) ZFSet.omega := by
  have graph := M.certificateProfileGraph_mem pairing unions powers separation hJ hNodes hW hk omega
  have profiles := M.groundPower_mem powers hNodes
  exact ⟨M.relationImage_mem separation hJ profiles graph,
    M.groundEmbeddable_function_image pairing unions powers separation choice hJ profiles omega
      graph (M.certificateProfileGraph_function function) smallJ⟩

theorem certificateProfileImage_meetFilter
    {P order q nodes nodeOrder meet N visibility top omega J W k enumerations : ZFSet.{u}}
    (family : PreparedCertificateFamilyCode M P order q nodes nodeOrder meet N visibility top omega J
      (M.supportedEqualityCertificateBound nodes W) (M.synchronizedEnumerationBound nodes W)
      k enumerations) {F : ZFSet.{u}}
    (member : F ∈ M.certificateProfileImage J nodes W k) :
    MeetFilterCode nodes nodeOrder meet F := by
  obtain ⟨z, B, f, edge⟩ := (M.mem_certificateProfileImage family.1 F).1 member
  have hz := (ZFSet.pair_mem_prod.1 (family.1.1 edge)).1
  obtain ⟨value, enumerated, _unique⟩ := family.2.1.2 z hz
  have bounds := (ZFSet.pair_mem_prod.1 (family.2.1.1 enumerated)).2
  obtain ⟨e, _he, names, _hn, rfl⟩ := ZFSet.mem_prod.1 bounds
  exact (family.2.2 z F B f e names edge enumerated).1

theorem certificateProfileImage_eq_of_domain_subset {J D nodes W k : ZFSet.{u}}
    (function : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k)
    (subset : J ⊆ D) :
    M.certificateProfileImage D nodes W k = M.certificateProfileImage J nodes W k := by
  apply ZFSet.ext
  intro F
  simp only [certificateProfileImage, certificateProfileGraph, mem_relationImage,
    pair_mem_relationCompose]
  constructor
  · rintro ⟨hF, z, _hzD, _, _, c, hc, edge, projected⟩
    have hz := (ZFSet.pair_mem_prod.1 (function.1 edge)).1
    exact ⟨hF, z, hz, hz, hF, c, hc, edge, projected⟩
  · rintro ⟨hF, z, hz, _, _, c, hc, edge, projected⟩
    exact ⟨hF, z, subset hz, subset hz, hF, c, hc, edge, projected⟩

theorem mem_certificateProfileImageFamily (nodes W z : ZFSet.{u}) :
    z ∈ M.certificateProfileImageFamily nodes W ↔
      ∃ k ∈ M.groundRelations W (M.supportedEqualityCertificateBound nodes W),
        z = ZFSet.pair k (M.certificateProfileImage W nodes W k) := by
  rw [certificateProfileImageFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨k, equal⟩
    exact ⟨k.val, k.property, equal.symm⟩
  · rintro ⟨k, hk, equal⟩
    exact ⟨⟨k, hk⟩, equal.symm⟩

theorem pair_mem_certificateProfileImageFamily (nodes W k image : ZFSet.{u}) :
    ZFSet.pair k image ∈ M.certificateProfileImageFamily nodes W ↔
      k ∈ M.groundRelations W (M.supportedEqualityCertificateBound nodes W) ∧
        image = M.certificateProfileImage W nodes W k := by
  rw [M.mem_certificateProfileImageFamily]
  constructor
  · rintro ⟨r, hr, equal⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hr, value⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨k, hk, rfl⟩

theorem certificateProfileImageFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    {nodes W : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hW : W ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.certificateProfileImageFamily nodes W ∈ M.sets := by
  let C := M.supportedEqualityCertificateBound nodes W
  let PF := M.groundPower nodes
  let projection := productFirst PF
    (ZFSet.prod (M.groundSmallSubsets nodes ZFSet.omega) (M.groundRelations nodes W))
  have hC := M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega
  have hPF := M.groundPower_mem powers hNodes
  have hProjection := M.productFirst_mem pairing unions powers separation hPF
    (M.prod_mem pairing unions powers separation
      (M.groundSmallSubsets_mem powers separation hNodes omega)
      (M.groundRelations_mem pairing unions powers separation hNodes hW))
  let defined := profileImageDefinition M pairing unions powers separation
  change defined.graph (extend W (extend C (extend PF (extend projection Fin.elim0))))
    (M.groundRelations W C) ∈ M.sets
  exact defined.graph_mem pairing separation collection _
    (Fin.cases hW (Fin.cases hC (Fin.cases hPF (Fin.cases hProjection (fun j => Fin.elim0 j)))))
    (M.groundRelations_mem pairing unions powers separation hW hC)

theorem certificateProfileImageFamily_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes W : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hW : W ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    ZFSet.IsFunc (M.groundRelations W (M.supportedEqualityCertificateBound nodes W))
      (M.groundPower (M.groundPower nodes)) (M.certificateProfileImageFamily nodes W) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := (M.mem_certificateProfileImageFamily nodes W z).1 hz
    have groundK := ((M.mem_groundRelations _ _ k).1 hk).1
    have groundGraph := M.certificateProfileGraph_mem pairing unions powers separation
      hW hNodes hW groundK omega
    have groundImage := M.relationImage_mem separation hW (M.groundPower_mem powers hNodes)
      groundGraph
    exact ZFSet.pair_mem_prod.2 ⟨hk, (M.mem_groundPower _ _).2
      ⟨groundImage, fun F member => (mem_relationImage _ _ _ F).1 member |>.1⟩⟩
  · intro k hk
    exact ⟨M.certificateProfileImage W nodes W k,
      (M.pair_mem_certificateProfileImageFamily nodes W k _).2 ⟨hk, rfl⟩,
      fun image edge => ((M.pair_mem_certificateProfileImageFamily nodes W k image).1 edge).2⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNicePreparationWitnessBounds
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

theorem groundRelations_mono {A B C D : ZFSet.{u}} (left : A ⊆ C) (right : B ⊆ D) :
    M.groundRelations A B ⊆ M.groundRelations C D := by
  intro f member
  obtain ⟨ground, shape⟩ := (M.mem_groundRelations A B f).1 member
  refine (M.mem_groundRelations C D f).2 ⟨ground, ?_⟩
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
  exact ZFSet.pair_mem_prod.2 ⟨left ha, right hb⟩

theorem supportedEqualityCertificateBound_mono {nodes N W : ZFSet.{u}} (inside : N ⊆ W) :
    M.supportedEqualityCertificateBound nodes N ⊆ M.supportedEqualityCertificateBound nodes W := by
  intro z hz
  obtain ⟨F, hF, tail, htail, rfl⟩ := ZFSet.mem_prod.1 hz
  obtain ⟨B, hB, f, hf, rfl⟩ := ZFSet.mem_prod.1 htail
  exact ZFSet.pair_mem_prod.2 ⟨hF, ZFSet.pair_mem_prod.2
    ⟨hB, M.groundRelations_mono (fun _ h => h) inside hf⟩⟩

theorem synchronizedEnumerationBound_mono {nodes N W : ZFSet.{u}} (inside : N ⊆ W) :
    M.synchronizedEnumerationBound nodes N ⊆ M.synchronizedEnumerationBound nodes W := by
  intro z hz
  obtain ⟨e, he, names, hn, rfl⟩ := ZFSet.mem_prod.1 hz
  exact ZFSet.pair_mem_prod.2 ⟨he, M.groundRelations_mono (fun _ h => h) inside hn⟩

theorem mem_preparationWitnessBound (nodes T Q r k enumerations : ZFSet.{u}) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q ↔
      r ∈ Q ∧ k ∈ M.groundRelations (M.groundRelations T Q)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q)) ∧
      enumerations ∈ M.groundRelations (M.groundRelations T Q)
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) := by
  simp only [preparationWitnessBound, ZFSet.pair_mem_prod]

theorem preparationWitnessBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes T Q : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hT : T ∈ M.sets)
    (hQ : Q ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.preparationWitnessBound nodes T Q ∈ M.sets := by
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  exact M.prod_mem pairing unions powers separation hQ
    (M.prod_mem pairing unions powers separation
      (M.groundRelations_mem pairing unions powers separation hW
        (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega))
      (M.groundRelations_mem pairing unions powers separation hW
        (M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega)))

theorem preparationWitness_mem_of_local {nodes T Q J N r k enumerations : ZFSet.{u}}
    (requestBound : J ⊆ M.groundRelations T Q) (nameBound : N ⊆ M.groundRelations T Q)
    (hr : r ∈ Q) (hk : k ∈ M.sets) (he : enumerations ∈ M.sets)
    (certificates : ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes N) k)
    (enumerated : ZFSet.IsFunc J (M.synchronizedEnumerationBound nodes N) enumerations) :
    ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q := by
  have localK := (M.mem_groundRelations J (M.supportedEqualityCertificateBound nodes N) k).2
    ⟨hk, certificates.1⟩
  have localE := (M.mem_groundRelations J (M.synchronizedEnumerationBound nodes N) enumerations).2
    ⟨he, enumerated.1⟩
  exact (M.mem_preparationWitnessBound nodes T Q r k enumerations).2
    ⟨hr, M.groundRelations_mono requestBound (M.supportedEqualityCertificateBound_mono nameBound) localK,
      M.groundRelations_mono requestBound (M.synchronizedEnumerationBound_mono nameBound) localE⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (T : ZFSet.{u}) (K : I → Subgroup G)

theorem niceSupportNameCodes_subset_groundRelations {Q : ZFSet.{u}} (carrier : s.carrier ⊆ Q) :
    M.niceSupportNameCodes a s T K ⊆ M.groundRelations T Q := by
  intro z member
  obtain ⟨ground, i, code⟩ := (M.mem_niceSupportNameCodes a s T K z).1 member
  have localBound := (M.mem_groundRelations T s.carrier z).2 ⟨ground, niceNameCode_subset a s code⟩
  exact M.groundRelations_mono (fun _ h => h) carrier localBound

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundVaryingPreparationRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem realize_storedPreparationFormula {n}
    (p y upperOrder cutGraph meet omega C E : Fin n) (fields : Fin 15 → Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (meetCode : MeetOrderCode (env (fields 10)) (env (fields 11)) (env meet)) :
    Realize M.sets (M.storedPreparationFormula pairing unions powers separation
      p y upperOrder cutGraph meet omega C E fields) env ↔
    M.StoredPreparationCode (env upperOrder) (env cutGraph) (env meet) (env omega)
      (env C) (env E) (fun j => env (fields j)) (env p) (env y) := by
  unfold storedPreparationFormula
  rw [realize_exBlock]
  have actual (w : Fin 8 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (transitionBody M pairing unions powers separation
        p y upperOrder cutGraph meet omega C E fields) (extendMany 8 w env) ↔
      (env p = ZFSet.pair (w 0) (w 1) ∧ env y = ZFSet.pair (w 2) (w 5) ∧
        w 5 = ZFSet.pair (w 3) (w 4) ∧ ZFSet.pair (w 2) (env p) ∈ env upperOrder ∧
        ZFSet.pair (w 2) (w 6) ∈ env cutGraph) ∧
      w 7 = M.storedPreparationRequests (w 1) (fun j => env (fields j)) ∧
      PreparedCertificateFamilyCode M (env (fields 7)) (env (fields 8)) (w 6)
        (env (fields 10)) (env (fields 11)) (env meet) (env (fields 14))
        (env (fields 13)) (env (fields 9)) (env omega) (w 7) (env C) (env E) (w 3) (w 4) := by
    have allGround := extendMany_members 8 w env ground members
    dsimp only [transitionBody]
    rw [Realize, Realize, BoundedFormula.realize_toFormula M _ _ allGround]
    have request : Realize M.sets (SetFormula.reindex
        (extend (prefixIndex n 8 7) (extend (prefixIndex n 8 1)
          (fun j => suffixIndex n 8 (fields j))))
        (M.definable_storedPreparationRequests pairing unions powers separation).formula)
        (extendMany 8 w env) ↔
        w 7 = M.storedPreparationRequests (w 1) (fun j => env (fields j)) := by
      rw [realize_reindex, map_extend, map_extend]
      simp only [extendMany_prefix, extendMany_suffix]
      exact (M.definable_storedPreparationRequests pairing unions powers separation).correct
        (extend (w 1) (fun j => env (fields j)))
        (Fin.cases (ground 1) (fun j => members (fields j))) (w 7) (ground 7)
    rw [request, M.realize_preparedCertificateFamilyFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _ allGround (by simpa only [extendMany_suffix] using meetCode)]
    simp only [transitionShape, BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_pairMembershipFormula, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨w, ground, body⟩
    obtain ⟨⟨input, output, tail, below, cut⟩, requests, prepared⟩ := (actual w ground).1 body
    exact ⟨w 0, w 1, w 2, w 3, w 4, w 6, input, tail ▸ output, below, cut, requests ▸ prepared⟩
  · rintro ⟨row, A, r, k, enumerations, q, input, output, below, cut, prepared⟩
    have hp := input ▸ members p
    have hy := output ▸ members y
    have hTail := M.pair_right hy
    have hq := M.pair_right (M.transitive (members cutGraph) cut)
    let J := M.storedPreparationRequests A (fun j => env (fields j))
    have hJ := M.storedPreparationRequests_mem pairing unions powers separation (M.pair_right hp)
      (fun j => env (fields j)) (fun j => members (fields j))
    let w : Fin 8 → ZFSet.{u} := ![row, A, r, k, enumerations, ZFSet.pair k enumerations, q, J]
    have ground : ∀ j, w j ∈ M.sets := Fin.cases (M.pair_left hp)
      (Fin.cases (M.pair_right hp) (Fin.cases (M.pair_left hy)
        (Fin.cases (M.pair_left hTail) (Fin.cases (M.pair_right hTail)
          (Fin.cases hTail (Fin.cases hq (Fin.cases hJ (fun j => Fin.elim0 j))))))))
    exact ⟨w, ground, (actual w ground).2 ⟨⟨input, output, rfl, below, cut⟩, rfl, prepared⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_storedPreparationRelation
    (Q upperOrder nodes T levels alpha meet : ZFSet.{u}) (fields : Fin 15 → ZFSet.{u})
    (p y : ZFSet.{u}) :
    ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T levels alpha meet fields ↔
    p ∈ Q ∧ y ∈ M.preparationWitnessBound nodes T Q ∧
      M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
        meet ZFSet.omega (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) fields p y := by
  rw [storedPreparationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hp, hy⟩, p', y', eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hp, hy, code⟩
  · rintro ⟨hp, hy, code⟩
    exact ⟨⟨hp, hy⟩, p, y, rfl, code⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationCode_pair_iff (packed Q upperOrder nodes T levels omega C E alpha p y : ZFSet.{u}) :
    M.VaryingPreparationCode packed Q upperOrder nodes T levels omega C E
      (ZFSet.pair (ZFSet.pair alpha p) y) ↔
    ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      M.StoredPreparationCode upperOrder (rowAssignmentCutGraph Q (fields 7) levels alpha)
        (canonicalMeetGraph (fields 10) (fields 11)) omega C E fields p y := by
  constructor
  · rintro ⟨alpha', p', y', fields, equal, rest⟩
    obtain ⟨input, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 input
    exact ⟨fields, rest⟩
  · rintro ⟨fields, rest⟩
    exact ⟨alpha, p, y, fields, rfl, rest⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem realize_varyingPreparationFormula {n}
    (z packed Q upperOrder nodes T levels omega C E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.varyingPreparationFormula pairing unions powers separation
      z packed Q upperOrder nodes T levels omega C E) env ↔
    M.VaryingPreparationCode (env packed) (env Q) (env upperOrder) (env nodes) (env T)
      (env levels) (env omega) (env C) (env E) (env z) := by
  unfold varyingPreparationFormula
  rw [realize_exBlock]
  let fs := fun w : Fin 22 → ZFSet.{u} => fun j : Fin 15 =>
    w j.succ.succ.succ.succ.succ.succ.succ
  have actual (w : Fin 22 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (varyingBody M pairing unions powers separation
        z packed Q upperOrder nodes T levels omega C E) (extendMany 22 w env) ↔
      (env z = ZFSet.pair (w 3) (w 2) ∧ w 3 = ZFSet.pair (w 0) (w 1) ∧
        w 4 = refinementFormulaDataCode (fs w) ∧ ZFSet.pair (w 0) (w 4) ∈ env packed ∧
        fs w 6 = env T ∧ fs w 10 = env nodes) ∧
      MeetOrderCode (fs w 10) (fs w 11) (w 5) ∧
      w 6 = rowAssignmentCutGraph (env Q) (fs w 7) (env levels) (w 0) ∧
      M.StoredPreparationCode (env upperOrder) (w 6) (w 5) (env omega)
        (env C) (env E) (fs w) (w 1) (w 2) := by
    have allGround := extendMany_members 22 w env ground members
    dsimp only [varyingBody]
    rw [Realize, Realize, Realize,
      BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.realize_toFormula M _ _ allGround,
      BoundedFormula.truth_meetOrderFormula,
      M.realize_rowAssignmentCutGraphFormula pairing unions powers separation _ _ _ _ _ _ allGround]
    simp only [varyingShape, BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_nonemptyTupleFormula, BoundedFormula.truth_pairMembershipFormula,
      extendMany_prefix, extendMany_suffix]
    apply and_congr_right
    intro _shape
    apply and_congr_right
    intro meet
    apply and_congr_right
    intro _cut
    simpa only [extendMany_prefix, extendMany_suffix] using
      (M.realize_storedPreparationFormula pairing unions powers separation
        (prefixIndex n 22 1) (prefixIndex n 22 2) (suffixIndex n 22 upperOrder)
        (prefixIndex n 22 6) (prefixIndex n 22 5) (suffixIndex n 22 omega)
        (suffixIndex n 22 C) (suffixIndex n 22 E)
        (fun j : Fin 15 => prefixIndex n 22 j.succ.succ.succ.succ.succ.succ.succ)
        (extendMany 22 w env) allGround (by simpa only [extendMany_prefix] using meet))
  constructor
  · rintro ⟨w, ground, body⟩
    obtain ⟨⟨outer, input, tuple, stored, terms, nodesEq⟩, meet, cut, prepared⟩ :=
      (actual w ground).1 body
    have canonical := meet.eq_canonicalMeetGraph
    refine ⟨w 0, w 1, w 2, fs w, input ▸ outer, tuple ▸ stored, terms, nodesEq,
      canonical ▸ meet, ?_⟩
    rw [canonical, cut] at prepared
    exact prepared
  · rintro ⟨alpha, p, y, fields, outer, stored, terms, nodesEq, meet, prepared⟩
    have hInput := M.pair_left (outer ▸ members z)
    have hAlpha := M.pair_left hInput
    have hp := M.pair_right hInput
    have hy := M.pair_right (outer ▸ members z)
    have hRecord := M.pair_right (M.transitive (members packed) stored)
    have hFields := M.refinementFormulaDataCode_fields_mem fields hRecord
    let mu := canonicalMeetGraph (fields 10) (fields 11)
    let cut := rowAssignmentCutGraph (env Q) (fields 7) (env levels) alpha
    have hMu := M.canonicalMeetGraph_mem pairing unions powers separation (hFields 10) (hFields 11)
    have hCut := M.rowAssignmentCutGraph_mem pairing unions powers separation
      (members Q) (hFields 7) (members levels) hAlpha
    let w : Fin 22 → ZFSet.{u} := extend alpha (extend p (extend y
      (extend (ZFSet.pair alpha p) (extend (refinementFormulaDataCode fields)
        (extend mu (extend cut fields))))))
    have ground : ∀ j, w j ∈ M.sets := Fin.cases hAlpha (Fin.cases hp (Fin.cases hy
      (Fin.cases hInput (Fin.cases hRecord (Fin.cases hMu (Fin.cases hCut hFields))))))
    exact ⟨w, ground, (actual w ground).2
      ⟨⟨outer, rfl, rfl, stored, terms, nodesEq⟩, meet, rfl, prepared⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_varyingPreparationRelation
    (stages packed Q upperOrder nodes T alpha p y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T ↔
    alpha ∈ stages ∧ p ∈ Q ∧ y ∈ M.preparationWitnessBound nodes T Q ∧
      ∃ fields : Fin 15 → ZFSet.{u},
        ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
        fields 6 = T ∧ fields 10 = nodes ∧
        MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
        M.StoredPreparationCode upperOrder
          (rowAssignmentCutGraph Q (fields 7) (refinementDataHistoryLevels stages packed T) alpha)
          (canonicalMeetGraph (fields 10) (fields 11)) ZFSet.omega
          (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
          (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) fields p y := by
  simp only [varyingPreparationRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod,
    M.varyingPreparationCode_pair_iff, and_assoc]

include M in
 theorem varyingPreparationRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages packed Q upperOrder nodes T : ZFSet.{u}}
    (hStages : stages ∈ M.sets) (hPacked : packed ∈ M.sets)
    (hQ : Q ∈ M.sets) (hOrder : upperOrder ∈ M.sets)
    (hNodes : nodes ∈ M.sets) (hT : T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets) :
    M.varyingPreparationRelation stages packed Q upperOrder nodes T ∈ M.sets := by
  let W := M.groundRelations T Q
  let C := M.supportedEqualityCertificateBound nodes W
  let E := M.synchronizedEnumerationBound nodes W
  let levels := refinementDataHistoryLevels stages packed T
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  have hC := M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega
  have hE := M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hPacked hT
  let params : Fin 9 → ZFSet.{u} := ![packed, Q, upperOrder, nodes, T, levels, ZFSet.omega, C, E]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hPacked (Fin.cases hQ
    (Fin.cases hOrder (Fin.cases hNodes (Fin.cases hT (Fin.cases hLevels
      (Fin.cases omega (Fin.cases hC (Fin.cases hE (fun j => Fin.elim0 j)))))))))
  let formula : SetFormula 10 :=
    M.varyingPreparationFormula pairing unions powers separation 0 1 2 3 4 5 6 7 8 9
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hStages hQ)
    (M.preparationWitnessBound_mem pairing unions powers separation hNodes hT hQ omega)
  have selected := M.separation_mem separation formula params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets formula (extend z params))
      (ZFSet.prod (ZFSet.prod stages Q) (M.preparationWitnessBound nodes T Q)) =
      M.varyingPreparationRelation stages packed Q upperOrder nodes T := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, varyingPreparationRelation, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_varyingPreparationFormula pairing unions powers separation
      0 1 2 3 4 5 6 7 8 9 (extend z params) (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralDataSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace

theorem semanticStructuralAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    (act).actionGraph (SetMembers.presentation Q) t = rawGraph := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  unfold semanticStructuralAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem semanticStructuralAction_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    ∀ (g : G) (p : SetMembers Q) (r : R) (A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((act).iso g p) = ZFSet.pair (c.encode (a.iso g r))
        (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  intro g p r A code
  have edge := ((act).triple_mem_actionGraph (SetMembers.presentation Q) t g p ((act).iso g p)).2 rfl
  rw [M.semanticStructuralAction_graph] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw ((act).iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c
    (M.structuralForcingCarrier_shape c.carrier t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history)
    (SetMembers.raw_mem ((act).iso g p))
  rw [code, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q _ _ g r q A D).1 edge
  rw [target, row, data]
  rfl

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundStoredVisitCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem varyingPreparationRelation_of_stored
    (stages packed Q upperOrder nodes T alpha p y meet : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u}) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet)
    (entry : ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T := by
  obtain ⟨hp, hy, code⟩ := (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
    (refinementDataHistoryLevels stages packed T) alpha meet fields p y).1 entry
  have equal := meetCode.eq_canonicalMeetGraph
  exact (M.pair_mem_varyingPreparationRelation stages packed Q upperOrder nodes T alpha p y).2
    ⟨hAlpha, hp, hy, fields, stored, terms, nodeCarrier, equal ▸ meetCode, equal ▸ code⟩

theorem varyingPreparationRelation_fiber_iff
    (stages packed Q upperOrder nodes T alpha p y meet dataBound : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u})
    (function : ZFSet.IsFunc stages dataBound packed) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet) :
    ZFSet.pair (ZFSet.pair alpha p) y ∈
        M.varyingPreparationRelation stages packed Q upperOrder nodes T ↔
      ZFSet.pair p y ∈ M.storedPreparationRelation Q upperOrder nodes T
        (refinementDataHistoryLevels stages packed T) alpha meet fields := by
  constructor
  · intro entry
    obtain ⟨_, hp, hy, other, otherStored, _terms, _nodes, _meet, code⟩ :=
      (M.pair_mem_varyingPreparationRelation stages packed Q upperOrder nodes T alpha p y).1 entry
    obtain ⟨_, _, unique⟩ := function.2 alpha hAlpha
    have same : other = fields := refinementFormulaDataCode_injective
      ((unique _ otherStored).trans (unique _ stored).symm)
    subst other
    exact (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields p y).2
      ⟨hp, hy, meetCode.eq_canonicalMeetGraph.symm ▸ code⟩
  · exact M.varyingPreparationRelation_of_stored stages packed Q upperOrder nodes T alpha p y meet
      fields hAlpha stored terms nodeCarrier meetCode





theorem varyingPreparation_visit_certificates
    (stages packed Q upperOrder nodes T alpha row A r payload meet dataBound : ZFSet.{u})
    (fields : Fin 15 → ZFSet.{u})
    (function : ZFSet.IsFunc stages dataBound packed) (hAlpha : alpha ∈ stages)
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed)
    (terms : fields 6 = T) (nodeCarrier : fields 10 = nodes)
    (meetCode : MeetOrderCode (fields 10) (fields 11) meet)
    (entry : ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row A)) (ZFSet.pair r payload) ∈
      M.varyingPreparationRelation stages packed Q upperOrder nodes T) :
    ∃ k enumerations q, payload = ZFSet.pair k enumerations ∧
      k ∈ M.sets ∧ enumerations ∈ M.sets ∧ r ∈ Q ∧ q ∈ fields 7 ∧
      ZFSet.pair r (ZFSet.pair row A) ∈ upperOrder ∧
      ZFSet.pair r q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages packed T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        meet (fields 14) (fields 13) (fields 9) ZFSet.omega
        (M.storedPreparationRequests A fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations := by
  have fixed := (M.varyingPreparationRelation_fiber_iff stages packed Q upperOrder nodes T
    alpha (ZFSet.pair row A) (ZFSet.pair r payload) meet dataBound fields function hAlpha
    stored terms nodeCarrier meetCode).1 entry
  obtain ⟨_, bounded, oldRow, oldA, output, k, enumerations, q, input, value, below, cut, family⟩ :=
    (M.pair_mem_storedPreparationRelation Q upperOrder nodes T
      (refinementDataHistoryLevels stages packed T) alpha meet fields
      (ZFSet.pair row A) (ZFSet.pair r payload)).1 fixed
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 input
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 value
  obtain ⟨hr, hk, he⟩ := (M.mem_preparationWitnessBound nodes T Q r k enumerations).1 bounded
  have hq := (ZFSet.pair_mem_prod.1
    ((mem_rowAssignmentCutGraph _ _ _ _ _).1 cut).1).2
  exact ⟨k, enumerations, q, rfl,
    ((M.mem_groundRelations _ _ k).1 hk).1,
    ((M.mem_groundRelations _ _ enumerations).1 he).1, hr, hq, below, cut, family⟩

end PartitionPilot.Forcing.TransitiveGround

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRetainedPreparationSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem pair_mem_retainedPreparationSelections (A L R p levels x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.retainedPreparationSelections A L R p levels ↔
      x ∈ A ∧ y ∈ L ∧ ∃ alpha row sourceA tail,
        y = ZFSet.pair alpha (ZFSet.pair (ZFSet.pair row sourceA) tail) ∧
        ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row sourceA)) (ZFSet.pair p tail) ∈ R ∧
        sourceA ⊆ A ∧ x ∈ sourceA ∧ ZFSet.pair x alpha ∈ levels := by
  rw [retainedPreparationSelections, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, x', alpha, row, sourceA, tail, equal, rest⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hy, alpha, row, sourceA, tail, value, rest⟩
  · rintro ⟨hx, hy, alpha, row, sourceA, tail, equal, rest⟩
    exact ⟨⟨hx, hy⟩, x, alpha, row, sourceA, tail, congrArg (ZFSet.pair x) equal, rest⟩

private theorem realize_selectionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (z A R p levels : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (selectionFormula z A R p levels) env ↔
      ∃ x alpha row sourceA tail,
        env z = ZFSet.pair x (ZFSet.pair alpha (ZFSet.pair (ZFSet.pair row sourceA) tail)) ∧
        ZFSet.pair (ZFSet.pair alpha (ZFSet.pair row sourceA)) (ZFSet.pair (env p) tail) ∈ env R ∧
        sourceA ⊆ env A ∧ x ∈ sourceA ∧ ZFSet.pair x alpha ∈ env levels := by
  rw [selectionFormula, realize_exBlock]
  have actual (w : Fin 10 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :
      Realize M.sets (selectionBody z A R p levels).toFormula (extendMany 10 w env) ↔
      env z = ZFSet.pair (w 0) (w 1) ∧ w 1 = ZFSet.pair (w 2) (w 9) ∧
      w 9 = ZFSet.pair (w 3) (w 6) ∧ w 3 = ZFSet.pair (w 4) (w 5) ∧
      w 7 = ZFSet.pair (w 2) (w 3) ∧ w 8 = ZFSet.pair (env p) (w 6) ∧
      ZFSet.pair (w 7) (w 8) ∈ env R ∧ w 5 ⊆ env A ∧ w 0 ∈ w 5 ∧
      ZFSet.pair (w 0) (w 2) ∈ env levels := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 10 w env ground members)]
    simp only [selectionBody, BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_pairMembershipFormula, extendMany_prefix, extendMany_suffix]
    rfl
  constructor
  · rintro ⟨w, ground, body⟩
    obtain ⟨outer, value, output, source, input, prepared, edge, subset, member, level⟩ :=
      (actual w ground).1 body
    refine ⟨w 0, w 2, w 4, w 5, w 6, ?_, ?_, subset, member, level⟩
    · simpa only [value, output, source] using outer
    · simpa only [input, prepared, source] using edge
  · rintro ⟨x, alpha, row, sourceA, tail, equal, edge, subset, member, level⟩
    have hz := equal ▸ members z
    have hx := M.pair_left hz
    have hy := M.pair_right hz
    have ha := M.pair_left hy
    have hout := M.pair_right hy
    have hsource := M.pair_left hout
    have htail := M.pair_right hout
    have hinput := M.orderedPair_mem pairing ha hsource
    have hprepared := M.orderedPair_mem pairing (members p) htail
    let w : Fin 10 → ZFSet.{u} := ![x, ZFSet.pair alpha (ZFSet.pair (ZFSet.pair row sourceA) tail),
      alpha, ZFSet.pair row sourceA, row, sourceA, tail,
      ZFSet.pair alpha (ZFSet.pair row sourceA), ZFSet.pair (env p) tail,
      ZFSet.pair (ZFSet.pair row sourceA) tail]
    have ground : ∀ j, w j ∈ M.sets := Fin.cases hx (Fin.cases hy (Fin.cases ha
      (Fin.cases hsource (Fin.cases (M.pair_left hsource) (Fin.cases (M.pair_right hsource)
        (Fin.cases htail (Fin.cases hinput (Fin.cases hprepared
          (Fin.cases hout (fun j => Fin.elim0 j))))))))))
    exact ⟨w, ground, (actual w ground).2
      ⟨equal, rfl, rfl, rfl, rfl, rfl, edge, subset, member, level⟩⟩

theorem retainedPreparationSelections_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A L R p levels : ZFSet.{u}} (hA : A ∈ M.sets) (hL : L ∈ M.sets)
    (hR : R ∈ M.sets) (hp : p ∈ M.sets) (hLevels : levels ∈ M.sets) :
    M.retainedPreparationSelections A L R p levels ∈ M.sets := by
  let params : Fin 4 → ZFSet.{u} := ![A, R, p, levels]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hA (Fin.cases hR
    (Fin.cases hp (Fin.cases hLevels (fun j => Fin.elim0 j))))
  have bound := M.prod_mem pairing unions powers separation hA hL
  have selected := M.separation_mem separation (selectionFormula 0 1 2 3 4) params ground bound
  have equal : ZFSet.sep (fun z => Realize M.sets (selectionFormula 0 1 2 3 4)
      (extend z params)) (ZFSet.prod A L) = M.retainedPreparationSelections A L R p levels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, retainedPreparationSelections, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact realize_selectionFormula M pairing 0 1 2 3 4 (extend z params)
      (Fin.cases (M.transitive bound hz) ground)
  exact equal ▸ selected

theorem exists_retainedPreparationSelection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A L R p levels : ZFSet.{u}} (hA : A ∈ M.sets) (hL : L ∈ M.sets)
    (hR : R ∈ M.sets) (hp : p ∈ M.sets) (hLevels : levels ∈ M.sets)
    (smallA : M.groundEmbeddable A ZFSet.omega)
    (total : ∀ x ∈ A, ∃ y ∈ L,
      ZFSet.pair x y ∈ M.retainedPreparationSelections A L R p levels) :
    ∃ f ∈ M.sets, ZFSet.IsFunc A L f ∧
      f ⊆ M.retainedPreparationSelections A L R p levels ∧
      relationImage A L f ∈ M.sets ∧ M.groundEmbeddable (relationImage A L f) ZFSet.omega :=
  M.exists_countableRelationSelection pairing unions powers separation infinite choice hA hL
    (M.retainedPreparationSelections_mem pairing unions powers separation hA hL hR hp hLevels)
    smallA total

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparedWitnessSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_storedPreparedWitnessSelection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows T stages packed nodes row A : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hT : T ∈ M.sets) (hStages : stages ∈ M.sets)
    (hPacked : packed ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (data : RefinementDataHistory stages packed T)
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing rows T stages packed)
    (prepared : StoredPreparedConditionCode M rows T stages packed nodes (ZFSet.pair row A))
    (nameBounds : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
      fields 14 ⊆ M.groundRelations T (M.refinementHistoryForcing rows T stages packed)) :
    let Q := M.refinementHistoryForcing rows T stages packed
    let L := ZFSet.prod stages (M.preparationWitnessBound nodes T Q)
    ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
      selections ⊆ M.preparedWitnessSelections rows T stages packed nodes (ZFSet.pair row A) A ∧
      relationImage A L selections ∈ M.sets ∧
      M.groundEmbeddable (relationImage A L selections) ZFSet.omega := by
  let Q := M.refinementHistoryForcing rows T stages packed
  let W := M.groundRelations T Q
  let L := ZFSet.prod stages (M.preparationWitnessBound nodes T Q)
  let R := M.varyingPreparationRelation stages packed Q (ZFSet.prod Q Q) nodes T
  let levels := refinementDataHistoryLevels stages packed T
  have omega := M.omega_mem separation infinite
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hPacked omega
  have hp := M.transitive hQ condition
  have hA := M.pair_right hp
  have candidate := ((M.mem_refinementHistoryForcing rows T stages packed _).1 condition).1
  have smallA := ((M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate).2.2.2
  have hL := M.prod_mem pairing unions powers separation hStages
    (M.preparationWitnessBound_mem pairing unions powers separation hNodes hT hQ omega)
  have hR := M.varyingPreparationRelation_mem pairing unions powers separation hStages hPacked hQ
    (M.prod_mem pairing unions powers separation hQ hQ) hNodes hT omega
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hPacked hT
  apply M.exists_retainedPreparationSelection pairing unions powers separation infinite choice
    hA hL hR hp hLevels smallA
  intro x hx
  obtain ⟨alpha, ha, fields, stored, terms, nodeCarrier, meet, _environment,
      sourceRow, sourceA, _hSourceA, sourceCondition, sourceSubset, selected,
      k, hk, enumerations, he, q, _hq, cut, family⟩ := prepared row A rfl x hx
  have requestBound : M.storedPreparationRequests sourceA fields ⊆ W := by
    intro z hz
    apply nameBounds alpha fields stored
    rcases ZFSet.mem_union.1 hz with left | right
    · exact (mem_relationImage _ _ _ _).1 left |>.1
    · exact (mem_relationImage _ _ _ _).1 right |>.1
  have witness (r : ZFSet.{u}) (hr : r ∈ Q) :
      ZFSet.pair r (ZFSet.pair k enumerations) ∈ M.preparationWitnessBound nodes T Q :=
    M.preparationWitness_mem_of_local requestBound (fun _ h => h) hr hk he family.1 family.2.1
  have visit : ZFSet.pair (ZFSet.pair alpha (ZFSet.pair sourceRow sourceA))
      (ZFSet.pair (ZFSet.pair row A) (ZFSet.pair k enumerations)) ∈ R := by
    apply (M.pair_mem_varyingPreparationRelation stages packed Q (ZFSet.prod Q Q) nodes T
      alpha (ZFSet.pair sourceRow sourceA) (ZFSet.pair (ZFSet.pair row A) (ZFSet.pair k enumerations))).2
    exact ⟨ha, sourceCondition, witness _ condition, fields, stored, terms, nodeCarrier, meet,
      sourceRow, sourceA, ZFSet.pair row A, k, enumerations, q, rfl, rfl,
      ZFSet.pair_mem_prod.2 ⟨condition, sourceCondition⟩, cut, family⟩
  have inSource := (mem_assignmentOnIndices (fields 0) T sourceA x).1 selected
  have level : ZFSet.pair x alpha ∈ levels := by
    obtain ⟨idx, hi, u, hu, w, hw, rfl⟩ := (mem_stageOneAssignments _ _ _).1 inSource.2
    exact data.coverage alpha ha fields stored idx hi u (terms.symm ▸ hu) w (terms.symm ▸ hw)
  let y := ZFSet.pair alpha (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))
  have hy : y ∈ L := ZFSet.pair_mem_prod.2 ⟨ha, witness _ sourceCondition⟩
  refine ⟨y, hy, (M.pair_mem_retainedPreparationSelections A L R (ZFSet.pair row A) levels x y).2 ?_⟩
  exact ⟨hx, hy, alpha, sourceRow, sourceA, ZFSet.pair k enumerations, rfl,
    visit, sourceSubset, inSource.1, level⟩

theorem preparedWitnessSelection_entry
    {rows T stages packed nodes p A x alpha sourceRow sourceA k enumerations : ZFSet.{u}}
    (data : RefinementDataHistory stages packed T)
    (entry : ZFSet.pair x (ZFSet.pair alpha
      (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈
      M.preparedWitnessSelections rows T stages packed nodes p A) :
    let Q := M.refinementHistoryForcing rows T stages packed
    alpha ∈ stages ∧ ZFSet.pair sourceRow sourceA ∈ Q ∧ sourceA ⊆ A ∧
      k ∈ M.sets ∧ enumerations ∈ M.sets ∧
    ∃ fields : Fin 15 → ZFSet.{u},
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed ∧
      fields 6 = T ∧ fields 10 = nodes ∧
      MeetOrderCode (fields 10) (fields 11) (canonicalMeetGraph (fields 10) (fields 11)) ∧
      x ∈ assignmentOnIndices (fields 0) T sourceA ∧
    ∃ q ∈ fields 7,
      ZFSet.pair p q ∈ rowAssignmentCutGraph Q (fields 7)
        (refinementDataHistoryLevels stages packed T) alpha ∧
      PreparedCertificateFamilyCode M (fields 7) (fields 8) q (fields 10) (fields 11)
        (canonicalMeetGraph (fields 10) (fields 11)) (fields 14) (fields 13) (fields 9)
        ZFSet.omega (M.storedPreparationRequests sourceA fields)
        (M.supportedEqualityCertificateBound nodes (M.groundRelations T Q))
        (M.synchronizedEnumerationBound nodes (M.groundRelations T Q)) k enumerations := by
  let Q := M.refinementHistoryForcing rows T stages packed
  obtain ⟨_, _, alpha', row', sourceA', tail, equal, visit, sourceSubset, inSource, level⟩ :=
    (M.pair_mem_retainedPreparationSelections _ _ _ _ _ _ _).1 entry
  obtain ⟨rfl, outputEq⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨sourceEq, rfl⟩ := ZFSet.pair_inj.1 outputEq
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 sourceEq
  obtain ⟨ha, sourceCondition, bounded, fields, stored, terms, nodeCarrier, meet, _raw⟩ :=
    (M.pair_mem_varyingPreparationRelation stages packed Q (ZFSet.prod Q Q) nodes T
      alpha (ZFSet.pair sourceRow sourceA) (ZFSet.pair p (ZFSet.pair k enumerations))).1 visit
  obtain ⟨k', enums', q, value, hk, he, _hp, hq, _below, cut, family⟩ :=
    M.varyingPreparation_visit_certificates stages packed Q (ZFSet.prod Q Q) nodes T alpha
      sourceRow sourceA p (ZFSet.pair k enumerations) _ _ fields data.function.to_isFunc ha
      stored terms nodeCarrier meet visit
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 value
  refine ⟨ha, sourceCondition, sourceSubset, hk, he, fields, stored, terms, nodeCarrier,
    meet, ?_, q, hq, cut, family⟩
  apply (mem_assignmentOnIndices (fields 0) T sourceA x).2
  refine ⟨inSource, ?_⟩
  obtain ⟨I, indexEntry, shape⟩ := (pair_mem_refinementHistoryAssignmentLevels
    data.index_function data.index_literal T x alpha).1 level
  have actual := (refinementDataHistoryField_entry data.function fields stored 0 (fields 0)).2 rfl
  have same : I = fields 0 := data.index_function.unique indexEntry actual
  exact same ▸ shape

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticPreparedWitnessSelections
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
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "LQ" => M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "lowerAct" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
include hs hh ordinal trace hAlpha cutOrdinal subset
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "inc" => RecursiveRefinementOrderHistory.inclusionFunction run ordinal cutOrdinal subset
  pairing unions powers separation infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono

include infinite choice
theorem semanticStructuralPreparationWitness_bounds :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
    Q ∈ M.sets ∧ M.preparationWitnessBound b.carrier T Q ∈ M.sets ∧
      LQ ⊆ Q ∧ M.niceSupportNameCodes lowerAct (SetMembers.presentation LQ) T d.principalFix ⊆
        M.groundRelations T Q := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have inside : LQ ⊆ Q := by
    intro x hx
    have included := SetMembers.raw_mem (inc (SetMembers.ofMem x hx))
    rw [(run).inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation
      infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono] at included
    simpa only [SetMembers.raw_ofMem] using included
  exact ⟨hQ, M.preparationWitnessBound_mem pairing unions powers separation nodes hT hQ omega,
    inside, M.niceSupportNameCodes_subset_groundRelations lowerAct (SetMembers.presentation LQ)
      T d.principalFix inside⟩

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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
include hs hh ordinal trace

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace

theorem semanticStructuralTrace_storedPreparation_request_bounds
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (alpha : ZFSet.{u}) (fields : Fin 15 → ZFSet.{u})
    (stored : ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed) :
    let upperQ := M.refinementHistoryForcing c.carrier T stages packed
    fields 10 = b.carrier ∧ fields 11 = b.conditionOrder ∧
      fields 14 ⊆ M.groundRelations T upperQ ∧
    ∀ sourceRow sourceA, ZFSet.pair sourceRow sourceA ∈ upperQ →
      M.storedPreparationRequests sourceA fields ∈ M.sets ∧
      M.groundEmbeddable (M.storedPreparationRequests sourceA fields) ZFSet.omega := by
  have member := (run).carriers.data.function.pair_source stored
  have hAlpha := M.transitive hs member
  have cutOrdinal := ordinalSetProperty_member ordinal member
  have subset := ordinal.1 alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let actual := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have actualStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member
  have same : fields = actual := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique stored actualStored)
  subst fields
  have bounds := M.semanticStructuralPreparationWitness_bounds c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace hAlpha cutOrdinal subset infinite choice
  refine ⟨rfl, rfl, M.groundRelations_mono (fun _ h => h) bounds.2.2.1, ?_⟩
  intro sourceRow sourceA condition
  have requests := M.semanticStructuralPrefix_assignmentClassRequests c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice condition
  exact ⟨requests.2.2.2.1, requests.2.2.2.2.1⟩

theorem semanticStructuralTrace_preparedWitnessSelection
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let L := ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)
    ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
      selections ⊆ M.preparedWitnessSelections c.carrier T stages packed b.carrier (ZFSet.pair row A) A ∧
      relationImage A L selections ∈ M.sets ∧
      M.groundEmbeddable (relationImage A L selections) ZFSet.omega := by
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  apply M.exists_storedPreparedWitnessSelection pairing unions powers separation infinite choice
    carrier hT hs hPacked nodes (run).carriers.data condition prepared
  intro alpha fields stored
  exact (M.semanticStructuralTrace_storedPreparation_request_bounds c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace infinite choice alpha fields stored).2.2.1

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_PreparedWitnessCertificateGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem preparedWitnessCertificateGraph_function (stages Q K E : ZFSet.{u}) :
    ZFSet.IsFunc (ZFSet.prod stages (ZFSet.prod Q (ZFSet.prod K E))) K
      (preparedWitnessCertificateGraph stages Q K E) :=
  relationCompose_function_of_subset
    (relationCompose_function_of_subset (productSecond_function _ _) (productSecond_function _ _)
      (fun _ h => h)) (productFirst_function _ _) (fun _ h => h)

theorem pair_mem_preparedWitnessCertificateGraph (stages Q K E y k : ZFSet.{u}) :
    ZFSet.pair y k ∈ preparedWitnessCertificateGraph stages Q K E ↔
      k ∈ K ∧ ∃ alpha ∈ stages, ∃ source ∈ Q, ∃ enumerations ∈ E,
        y = ZFSet.pair alpha (ZFSet.pair source (ZFSet.pair k enumerations)) := by
  rw [preparedWitnessCertificateGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, hk, tail, _, first, projected⟩
    obtain ⟨k', _, enums, he, equal⟩ := (mem_productFirst _ _ _).1 projected
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨_, _, output, _, first, second⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
    obtain ⟨source, hsource, tail', _, equal⟩ := (mem_productSecond _ _ _).1 second
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨alpha, ha, output', _, equal⟩ := (mem_productSecond _ _ _).1 first
    obtain ⟨value, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hk, alpha, ha, source, hsource, enums, he, value⟩
  · rintro ⟨hk, alpha, ha, source, hs, enums, he, rfl⟩
    have ht := ZFSet.pair_mem_prod.2 ⟨hk, he⟩
    have ho := ZFSet.pair_mem_prod.2 ⟨hs, ht⟩
    have hy := ZFSet.pair_mem_prod.2 ⟨ha, ho⟩
    exact ⟨hy, hk, _, ht,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hy, ht, _, ho,
        (mem_productSecond _ _ _).2 ⟨alpha, ha, _, ho, rfl⟩,
        (mem_productSecond _ _ _).2 ⟨source, hs, _, ht, rfl⟩⟩,
      (mem_productFirst _ _ _).2 ⟨k, hk, enums, he, rfl⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem preparedWitnessCertificateGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {stages Q K E : ZFSet.{u}} (hStages : stages ∈ M.sets) (hQ : Q ∈ M.sets)
    (hK : K ∈ M.sets) (hE : E ∈ M.sets) :
    preparedWitnessCertificateGraph stages Q K E ∈ M.sets := by
  have ht := M.prod_mem pairing unions powers separation hK hE
  have ho := M.prod_mem pairing unions powers separation hQ ht
  have hL := M.prod_mem pairing unions powers separation hStages ho
  exact M.relationCompose_mem pairing unions powers separation hL ht hK
    (M.relationCompose_mem pairing unions powers separation hL ho ht
      (M.productSecond_mem pairing unions powers separation hStages ho)
      (M.productSecond_mem pairing unions powers separation hQ ht))
    (M.productFirst_mem pairing unions powers separation hK hE)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPreparedSelectionProfiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
open scoped ZFSet
universe u
variable (M : TransitiveGround.{u})

theorem preparedSelectionProfiles_ground_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rows T stages packed nodes nodeOrder p A selections : ZFSet.{u}}
    (hRows : rows ∈ M.sets) (hT : T ∈ M.sets) (hStages : stages ∈ M.sets)
    (hPacked : packed ∈ M.sets) (hNodes : nodes ∈ M.sets)
    (data : RefinementDataHistory stages packed T)
    (selected : selections ⊆ M.preparedWitnessSelections rows T stages packed nodes p A)
    (whole : relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound nodes T (M.refinementHistoryForcing rows T stages packed))) selections ∈ M.sets)
    (small : M.groundEmbeddable (relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound nodes T (M.refinementHistoryForcing rows T stages packed))) selections) ZFSet.omega)
    (localData : ∀ alpha (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair alpha (refinementFormulaDataCode fields) ∈ packed →
      fields 10 = nodes ∧ fields 11 = nodeOrder ∧
      fields 14 ⊆ M.groundRelations T (M.refinementHistoryForcing rows T stages packed) ∧
      ∀ sourceRow sourceA,
        ZFSet.pair sourceRow sourceA ∈ M.refinementHistoryForcing rows T stages packed →
        M.storedPreparationRequests sourceA fields ∈ M.sets ∧
        M.groundEmbeddable (M.storedPreparationRequests sourceA fields) ZFSet.omega) :
    let Q := M.refinementHistoryForcing rows T stages packed
    let Profiles := M.preparedSelectionProfiles A stages Q nodes T selections
    Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
      (∀ F ∈ Profiles, MeetFilterCode nodes nodeOrder (canonicalMeetGraph nodes nodeOrder) F) ∧
      ∀ x alpha sourceRow sourceA k enumerations z F B f,
        ZFSet.pair x (ZFSet.pair alpha
          (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈ selections →
        ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k → F ∈ Profiles := by
  let Q := M.refinementHistoryForcing rows T stages packed
  let W := M.groundRelations T Q
  let K := M.groundRelations W (M.supportedEqualityCertificateBound nodes W)
  let E := M.groundRelations W (M.synchronizedEnumerationBound nodes W)
  let L := ZFSet.prod stages (M.preparationWitnessBound nodes T Q)
  let witnesses := relationImage A L selections
  let projection := preparedWitnessCertificateGraph stages Q K E
  let certificates := relationImage witnesses K projection
  let images := relationImage certificates (M.groundPower (M.groundPower nodes))
    (M.certificateProfileImageFamily nodes W)
  have omega := M.omega_mem separation infinite
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation hRows hT hStages hPacked omega
  have hW := M.groundRelations_mem pairing unions powers separation hT hQ
  have hK := M.groundRelations_mem pairing unions powers separation hW
    (M.supportedEqualityCertificateBound_mem pairing unions powers separation hNodes hW omega)
  have hE := M.groundRelations_mem pairing unions powers separation hW
    (M.synchronizedEnumerationBound_mem pairing unions powers separation hNodes hW omega)
  have hProjection := M.preparedWitnessCertificateGraph_mem pairing unions powers separation hStages hQ hK hE
  have hCertificates := M.relationImage_mem separation whole hK hProjection
  have smallCertificates := M.groundEmbeddable_function_image pairing unions powers separation choice
    whole hK omega hProjection (preparedWitnessCertificateGraph_function stages Q K E) small
  have hFamily := M.certificateProfileImageFamily_mem pairing unions powers separation collection hNodes hW omega
  have hImageBound := M.groundPower_mem powers (M.groundPower_mem powers hNodes)
  have familyFunction := M.certificateProfileImageFamily_function pairing unions powers separation hNodes hW omega
  have hImages := M.relationImage_mem separation hCertificates hImageBound hFamily
  have smallImages := M.groundEmbeddable_function_image pairing unions powers separation choice
    hCertificates hImageBound omega hFamily familyFunction smallCertificates
  have certificateData (k : ZFSet.{u}) (member : k ∈ certificates) :
      ∃ J, J ∈ M.sets ∧ M.groundEmbeddable J ZFSet.omega ∧ J ⊆ W ∧
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound nodes W) k ∧
        ∀ F ∈ M.certificateProfileImage J nodes W k,
          MeetFilterCode nodes nodeOrder (canonicalMeetGraph nodes nodeOrder) F := by
    obtain ⟨_, y, hy, projected⟩ := (mem_relationImage _ _ _ _).1 member
    obtain ⟨_, x, _hx, edge⟩ := (mem_relationImage _ _ _ _).1 hy
    obtain ⟨_, alpha, _ha, source, hs, enumerations, _he, rfl⟩ :=
      (pair_mem_preparedWitnessCertificateGraph stages Q K E y k).1 projected
    obtain ⟨sourceRow, _, sourceA, _, rfl⟩ := ZFSet.mem_prod.1
      (M.refinementHistoryForcing_shape rows T stages packed hs)
    obtain ⟨_, sourceCondition, _, _, _, fields, stored, _terms, nodeCarrier, _meet,
      _assignment, q, _hq, _cut, family⟩ := M.preparedWitnessSelection_entry data (selected edge)
    obtain ⟨_nodes, orderEq, nameBound, requests⟩ := localData alpha fields stored
    obtain ⟨hJ, smallJ⟩ := requests sourceRow sourceA sourceCondition
    have Jbound : M.storedPreparationRequests sourceA fields ⊆ W := by
      intro z hz
      apply nameBound
      rcases ZFSet.mem_union.1 hz with left | right
      · exact (mem_relationImage _ _ _ _).1 left |>.1
      · exact (mem_relationImage _ _ _ _).1 right |>.1
    refine ⟨_, hJ, smallJ, Jbound, family.1, ?_⟩
    intro F hF
    have aligned := family
    rw [nodeCarrier, orderEq] at aligned
    exact M.certificateProfileImage_meetFilter aligned hF
  have imagesSmall (image : ZFSet.{u}) (member : image ∈ images) :
      M.groundEmbeddable image ZFSet.omega := by
    obtain ⟨_, k, hk, edge⟩ := (mem_relationImage _ _ _ _).1 member
    obtain ⟨_, rfl⟩ := (M.pair_mem_certificateProfileImageFamily nodes W k image).1 edge
    obtain ⟨J, hJ, smallJ, Jbound, function, _filters⟩ := certificateData k hk
    rw [M.certificateProfileImage_eq_of_domain_subset function Jbound]
    exact (M.certificateProfileImage_mem_small pairing unions powers separation choice hJ hNodes hW
      (((M.mem_groundRelations _ _ k).1 ((mem_relationImage _ _ _ _).1 hk).1).1)
      omega function smallJ).2
  change (⋃₀ images) ∈ M.sets ∧ M.groundEmbeddable (⋃₀ images) ZFSet.omega ∧ _
  refine ⟨M.union_mem unions hImages,
    M.groundCountable_family_union pairing unions powers separation infinite choice hImages smallImages imagesSmall,
    ?_, ?_⟩
  · intro F member
    obtain ⟨image, hi, hF⟩ := ZFSet.mem_sUnion.1 member
    obtain ⟨_, k, hk, edge⟩ := (mem_relationImage _ _ _ _).1 hi
    obtain ⟨_, rfl⟩ := (M.pair_mem_certificateProfileImageFamily nodes W k image).1 edge
    obtain ⟨J, _, _, Jbound, function, filters⟩ := certificateData k hk
    apply filters F
    exact M.certificateProfileImage_eq_of_domain_subset function Jbound ▸ hF
  · intro x alpha sourceRow sourceA k enumerations z F B f edge certificate
    have selectedEdge := selected edge
    dsimp only [preparedWitnessSelections, retainedPreparationSelections] at selectedEdge
    have bounded := (ZFSet.mem_sep.1 selectedEdge).1
    have pairBounds := ZFSet.pair_mem_prod.1 bounded
    have yBound := ZFSet.pair_mem_prod.1 pairBounds.2
    have outputBound := ZFSet.pair_mem_prod.1 yBound.2
    have tailBound := ZFSet.pair_mem_prod.1 outputBound.2
    have hk : k ∈ certificates := (mem_relationImage _ _ _ _).2 ⟨tailBound.1,
      _, (mem_relationImage _ _ _ _).2 ⟨pairBounds.2, x, pairBounds.1, edge⟩,
      (pair_mem_preparedWitnessCertificateGraph stages Q K E _ k).2
        ⟨tailBound.1, alpha, yBound.1, _, outputBound.1, enumerations, tailBound.2, rfl⟩⟩
    obtain ⟨J, _, _, Jbound, function, _⟩ := certificateData k hk
    have familyEdge := (M.pair_mem_certificateProfileImageFamily nodes W k _).2 ⟨tailBound.1, rfl⟩
    have imageBound := (ZFSet.pair_mem_prod.1 (familyFunction.1 familyEdge)).2
    refine ZFSet.mem_sUnion.2 ⟨_, (mem_relationImage _ _ _ _).2 ⟨imageBound, k, hk, familyEdge⟩, ?_⟩
    rw [M.certificateProfileImage_eq_of_domain_subset function Jbound]
    exact (M.mem_certificateProfileImage function F).2 ⟨z, B, f, certificate⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRefinementMixedUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable {row rowA rowB A B : ZFSet.{u}}
local notation "levels" => refinementDataHistoryLevels stages history T
include run

theorem mixed_union_mem_of_candidates (ordinal : ordinalSetProperty stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ C lower stronger, stageOneRawTests M d C lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d C stronger)
    (first : ZFSet.pair rowA A ∈ M.refinementHistoryForcing rows T stages history)
    (second : ZFSet.pair rowB B ∈ M.refinementHistoryForcing rows T stages history)
    (rowBelowA : ZFSet.pair row rowA ∈ rowOrder)
    (rowBelowB : ZFSet.pair row rowB ∈ rowOrder)
    (cross : ∀ beta ∈ stages, ∀ d : Fin 15 → ZFSet.{u},
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ZFSet.pair row (assignmentCut levels beta (A ∪ B)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history) →
      stageOneRawCrossCollisions M d A B
        (ZFSet.pair row (assignmentCut levels beta (A ∪ B))))
    (candidate : ZFSet.pair row (A ∪ B) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T)
    (candidates : ∀ gamma ∈ stages, ZFSet.pair row (assignmentCut levels gamma (A ∪ B)) ∈
      M.stageOneCandidateBound rows
        (refinementDataHistoryIndices gamma (graphRestriction gamma history)) T) :
    ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing rows T stages history := by
  have subsetA : A ⊆ A ∪ B := fun _ h => ZFSet.mem_union.2 (Or.inl h)
  have subsetB : B ⊆ A ∪ B := fun _ h => ZFSet.mem_union.2 (Or.inr h)
  have firstTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 first).2
  have secondTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 second).2
  have step (beta : ZFSet.{u}) (hbeta : beta ∈ stages) (d : Fin 15 → ZFSet.{u})
      (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
      (proved : ZFSet.pair row (assignmentCut levels beta (A ∪ B)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history)) :
      stageOneRawTests M d (A ∪ B) (ZFSet.pair row (assignmentCut levels beta (A ∪ B))) := by
    have storedA := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 firstTests
      beta hbeta (refinementFormulaDataCode d) entry
    have checkedA := (stageTwoConditionCode_pair_iff M d _ beta rowA A).1
      ((packedSuccessorConditionCode_code_iff M _ beta d _).1 storedA)
    have storedB := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 secondTests
      beta hbeta (refinementFormulaDataCode d) entry
    have checkedB := (stageTwoConditionCode_pair_iff M d _ beta rowB B).1
      ((packedSuccessorConditionCode_code_iff M _ beta d _).1 storedB)
    have belowA : ZFSet.pair (ZFSet.pair row (assignmentCut levels beta (A ∪ B)))
        (ZFSet.pair rowA (assignmentCut levels beta A)) ∈ d 8 := by
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem first hbeta, rowBelowA, assignmentCut_mono subsetA⟩
    have belowB : ZFSet.pair (ZFSet.pair row (assignmentCut levels beta (A ∪ B)))
        (ZFSet.pair rowB (assignmentCut levels beta B)) ∈ d 8 := by
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem second hbeta, rowBelowB, assignmentCut_mono subsetB⟩
    exact stageOneRawTests_mixed_union M d
      (mono beta d entry A _ _ checkedA.2 belowA) (mono beta d entry B _ _ checkedB.2 belowB)
      (cross beta hbeta d entry proved)
  have earlier : ∀ gamma ∈ stages, ZFSet.pair row (assignmentCut levels gamma (A ∪ B)) ∈
      M.refinementHistoryForcing rows T gamma (graphRestriction gamma history) := by
    intro gamma
    induction gamma using ZFSet.inductionOn with
    | h gamma ih =>
      intro hgamma
      apply (M.mem_refinementHistoryForcing rows T gamma (graphRestriction gamma history) _).2
      refine ⟨candidates gamma hgamma, ?_⟩
      intro beta hbeta
      have betaFull := ordinal.1 gamma hgamma beta hbeta
      have betaSubset := ordinal.2 gamma hgamma beta hbeta
      obtain ⟨data, entry⟩ := run.carriers.data.function.total betaFull
      obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
      have proved := ih beta hbeta betaFull
      have sameCut := run.carriers.data.prefix_cut (ordinal.1 gamma hgamma) betaSubset
        (assignmentCut levels gamma (A ∪ B))
      refine ⟨refinementFormulaDataCode d, pair_mem_graphRestriction.2 ⟨entry, hbeta⟩, ?_⟩
      apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
      apply (stageTwoConditionCode_pair_iff M d _ beta row _).2
      rw [sameCut, assignmentCut_nested betaSubset]
      refine ⟨(run.carriers.carrier beta d entry).symm ▸ proved, ?_⟩
      exact stageOneRawTests_transfer M d _ (step beta betaFull d entry proved)
        (fun _ _ _ _ _ _ member => assignmentCut_subset levels gamma (A ∪ B) member)
  apply (M.mem_refinementHistoryForcing rows T stages history _).2
  refine ⟨candidate, ?_⟩
  intro beta hbeta
  obtain ⟨data, entry⟩ := run.carriers.data.function.total hbeta
  obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
  refine ⟨refinementFormulaDataCode d, entry, ?_⟩
  apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
  apply (stageTwoConditionCode_pair_iff M d _ beta row _).2
  exact ⟨(run.carriers.carrier beta d entry).symm ▸ earlier beta hbeta,
    step beta hbeta d entry (earlier beta hbeta)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory



namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
include run pairing unions powers separation infinite choice hStages hHistory hT

theorem mixed_union_extension (ordinal : ordinalSetProperty stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ C lower stronger, stageOneRawTests M d C lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d C stronger)
    (rowOrderLaw : PartialOrderCode rows rowOrder) {row rowA rowB A B : ZFSet.{u}}
    (first : ZFSet.pair rowA A ∈ M.refinementHistoryForcing rows T stages history)
    (second : ZFSet.pair rowB B ∈ M.refinementHistoryForcing rows T stages history)
    (rowBelowA : ZFSet.pair row rowA ∈ rowOrder)
    (rowBelowB : ZFSet.pair row rowB ∈ rowOrder)
    (cross : ∀ beta ∈ stages, ∀ d : Fin 15 → ZFSet.{u},
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) beta (A ∪ B)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history) →
      stageOneRawCrossCollisions M d A B (ZFSet.pair row
        (assignmentCut (refinementDataHistoryLevels stages history T) beta (A ∪ B)))) :
    ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing rows T stages history ∧
      ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowA A) ∈
        M.refinementHistoryOrder rows rowOrder T stages history ∧
      ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowB B) ∈
        M.refinementHistoryOrder rows rowOrder T stages history := by
  have firstCandidate := ((M.mem_refinementHistoryForcing rows T stages history _).1 first).1
  have secondCandidate := ((M.mem_refinementHistoryForcing rows T stages history _).1 second).1
  obtain ⟨_, hA, subsetA, smallA⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 firstCandidate
  obtain ⟨_, hB, subsetB, smallB⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 secondCandidate
  have hrow := (ZFSet.pair_mem_prod.1 (rowOrderLaw.relation rowBelowA)).1
  have candidate : ZFSet.pair row (A ∪ B) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T := by
    apply (M.pair_mem_stageOneCandidateBound _ _ _ _ _).2
    refine ⟨hrow, M.binary_union_mem pairing unions hA hB, ?_,
      M.groundCountable_binary_union pairing unions powers separation infinite choice hA hB smallA smallB⟩
    intro z member
    exact (ZFSet.mem_union.1 member).elim (fun h => subsetA h) (fun h => subsetB h)
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have member := run.mixed_union_mem_of_candidates ordinal mono first second rowBelowA rowBelowB cross candidate
    (fun beta hbeta => M.refinementDataHistoryCandidate_cut separation run.carriers.data
      (ordinal.1 beta hbeta) hLevels (M.transitive hStages hbeta) (M.omega_mem separation infinite) candidate)
  refine ⟨member, ?_, ?_⟩
  · exact (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
      ⟨member, first, rowBelowA, fun _ h => ZFSet.mem_union.2 (Or.inl h)⟩
  · exact (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
      ⟨member, second, rowBelowB, fun _ h => ZFSet.mem_union.2 (Or.inr h)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedCopyUnions
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

theorem semanticStructuralTrace_mixed_union_extension
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    ∀ row rowA rowB A B : ZFSet.{u},
      ZFSet.pair rowA A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      ZFSet.pair rowB B ∈ M.refinementHistoryForcing c.carrier T stages packed →
      ZFSet.pair row rowA ∈ c.conditionOrder →
      ZFSet.pair row rowB ∈ c.conditionOrder →
      (∀ beta ∈ stages, ∀ data : Fin 15 → ZFSet.{u},
        ZFSet.pair beta (refinementFormulaDataCode data) ∈ packed →
        ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) beta (A ∪ B)) ∈
          M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed) →
        stageOneRawCrossCollisions M data A B (ZFSet.pair row
          (assignmentCut (refinementDataHistoryLevels stages packed T) beta (A ∪ B)))) →
      ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowA A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowB B) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  dsimp only
  intro row rowA rowB A B first second rowBelowA rowBelowB cross
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact run.mixed_union_extension pairing unions powers separation infinite choice hs hPacked hT
    ordinal mono c.conditionOrder_code first second rowBelowA rowBelowB cross

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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
include hs hh ordinal trace
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "image" => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace

theorem semanticStructuralTrace_insertion_union
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r row : R) (A selections : ZFSet.{u}) (h : G) (D K V : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (selectionFunction : ZFSet.IsFunc A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections)
    (selected : selections ⊆ M.preparedWitnessSelections c.carrier T stages packed b.carrier
      (ZFSet.pair (c.encode r) A) A)
    (whole : relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections ∈ M.sets)
    (smallWhole : M.groundEmbeddable (relationImage A (ZFSet.prod stages
      (M.preparationWitnessBound b.carrier T upperQ)) selections) ZFSet.omega)
    (below : row ≤ r) (belowH : row ≤ a.iso h r)
    (fixed : h ∈ d.principalFix V) (cap : d.iso h D ≤ K)
    (anchorGood : ∀ idx u w E,
      stageOneAssignment idx u w ∈ A →
      ZFSet.pair idx E ∈ refinementIndexFieldGraph I b.carrier 2 →
      ZFSet.pair E (b.encode K) ∈ b.conditionOrder →
      ZFSet.pair E (b.encode V) ∈ b.conditionOrder)
    (profileGood : ∀ F ∈ M.preparedSelectionProfiles A stages upperQ b.carrier T selections,
      b.encode V ∉ F → b.encode K ∉ F)
    (movedData : ∀ z ∈ image (t.encode h) A, ZFSet.pair z (b.encode (d.iso h D)) ∈
      stageOneDataBounds (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples) :
    ZFSet.pair (c.encode row) (A ∪ image (t.encode h) A) ∈ upperQ ∧
      ZFSet.pair (ZFSet.pair (c.encode row) (A ∪ image (t.encode h) A)) (ZFSet.pair (c.encode r) A) ∈
        M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
      ZFSet.pair (ZFSet.pair (c.encode row) (A ∪ image (t.encode h) A))
        (ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A)) ∈
        M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let upper : SetMembers upperQ := SetMembers.ofMem _ source
  have upperCode : SetMembers.raw upper = ZFSet.pair (c.encode r) A := SetMembers.raw_ofMem _ _
  have actionCode := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace h upper r A upperCode
  have sourceAct : ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A) ∈ upperQ :=
    actionCode ▸ SetMembers.raw_mem ((upperAct).iso h upper)
  apply M.semanticStructuralTrace_mixed_union_extension c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice
    (c.encode row) (c.encode r) (c.encode (a.iso h r)) A (image (t.encode h) A)
    source sourceAct ((c.pair_mem_conditionOrder row r).2 below)
    ((c.pair_mem_conditionOrder row (a.iso h r)).2 belowH)
  intro beta member fields stored validCut
  have canonical := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same := refinementFormulaDataCode_injective ((run).carriers.data.function.unique stored canonical)
  rw [same]
  exact M.semanticStructuralPrefix_insertion_crossCollisions c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice small I S mu positions tuples range support
    r row A (A ∪ image (t.encode h) A) selections h D K V source selectionFunction selected whole smallWhole
    below belowH (fun _ member => ZFSet.mem_union.2 (Or.inl member))
    (fun _ member => ZFSet.mem_union.2 (Or.inr member)) fixed cap anchorGood profileGood movedData validCut

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticPreparedProfileSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



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

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
include hs hh ordinal trace

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace

theorem semanticStructuralTrace_preparedProfileSelection
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {row A : ZFSet.{u}}
    (condition : ZFSet.pair row A ∈ M.refinementHistoryForcing c.carrier T stages packed)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair row A)) :
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let L := ZFSet.prod stages (M.preparationWitnessBound b.carrier T Q)
    ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
      selections ⊆ M.preparedWitnessSelections c.carrier T stages packed b.carrier (ZFSet.pair row A) A ∧
      relationImage A L selections ∈ M.sets ∧ M.groundEmbeddable (relationImage A L selections) ZFSet.omega ∧
      let Profiles := M.preparedSelectionProfiles A stages Q b.carrier T selections
      Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
      (∀ F ∈ Profiles, MeetFilterCode b.carrier b.conditionOrder
        (canonicalMeetGraph b.carrier b.conditionOrder) F) ∧
      ∀ x alpha sourceRow sourceA k enumerations z F B f,
        ZFSet.pair x (ZFSet.pair alpha
          (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈ selections →
        ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k → F ∈ Profiles := by
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall⟩ :=
    M.semanticStructuralTrace_preparedWitnessSelection c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace infinite choice condition prepared
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  refine ⟨selections, whole, function, selected, rangeGround, rangeSmall, ?_⟩
  apply M.preparedSelectionProfiles_ground_countable pairing unions powers separation collection
    infinite choice carrier hT hs hPacked nodes (run).carriers.data selected rangeGround rangeSmall
  intro alpha fields stored
  exact M.semanticStructuralTrace_storedPreparation_request_bounds c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice alpha fields stored

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBinaryRowRecordedPreparationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (G nodes nodeOrder basis T T2 stages history : ZFSet.{u})
local notation "I" => refinementDataHistoryIndices stages
  (M.structuralRefinementHistory G nodes nodeOrder basis T T2 stages history)

theorem structuralIndex_anchor_fields {x : ZFSet.{u}} (member : x ∈ I) :
    ∃ v : Fin 6 → ZFSet.{u}, x = nonemptyTupleCode 5 v ∧ v 2 ∈ nodes := by
  obtain ⟨level, _hl, data, entry, hx⟩ := (mem_refinementDataHistoryIndices _ _ _).1 member
  obtain ⟨_, P, order, top, action, _stored, rfl⟩ :=
    M.structuralRefinementHistory_fields G nodes nodeOrder basis T T2 stages history data entry
  obtain ⟨v, equal, bounds⟩ := M.refinementIndices_fields _ _ _ _ _ _ _ _ _ _ _ hx
  exact ⟨v, equal, bounds 2⟩

theorem structuralIndexAnchors_function :
    ZFSet.IsFunc I nodes (refinementIndexFieldGraph I nodes 2) :=
  refinementIndexFieldGraph_function I nodes 2
    (fun _ member => M.structuralIndex_anchor_fields G nodes nodeOrder basis T T2 stages history member)

include M in
 theorem structuralIndexAnchorData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hG : G ∈ M.sets) (hn : nodes ∈ M.sets) (hno : nodeOrder ∈ M.sets)
    (hb : basis ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (hs : stages ∈ M.sets) (hh : history ∈ M.sets) :
    I ∈ M.sets ∧ refinementIndexFieldGraph I nodes 2 ∈ M.sets ∧
      ZFSet.IsFunc I nodes (refinementIndexFieldGraph I nodes 2) := by
  have packed := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![G, nodes, nodeOrder, basis, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hn (Fin.cases hno (Fin.cases hb
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have indices := M.refinementDataHistoryIndices_mem pairing unions powers separation hs packed
  exact ⟨indices, M.refinementIndexFieldGraph_mem pairing unions powers separation indices hn 2,
    M.structuralIndexAnchors_function G nodes nodeOrder basis T T2 stages history⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalStructuralCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem mem_insertionUsedNodes
    (rowNodes columns row I T A nodes anchors v : ZFSet.{u}) :
    v ∈ insertionUsedNodes rowNodes columns row I T A nodes anchors ↔
      v ∈ rowUsedRows rowNodes columns (natSetCode 2) row ∨
      (v ∈ nodes ∧ ∃ idx ∈ I, ∃ u ∈ T, ∃ w ∈ T,
        stageOneAssignment idx u w ∈ A ∧ ZFSet.pair idx v ∈ anchors) := by
  rw [insertionUsedNodes, ZFSet.mem_union, mem_relationImage]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨hv, idx, hi, edge⟩
    obtain ⟨hi, u, hu, w, hw, stored⟩ := (mem_assignmentIndices I T A idx).1 hi
    exact ⟨hv, idx, hi, u, hu, w, hw, stored, edge⟩
  · rintro ⟨hv, idx, hi, u, hu, w, hw, stored, edge⟩
    exact ⟨hv, idx, (mem_assignmentIndices I T A idx).2 ⟨hi, u, hu, w, hw, stored⟩, edge⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem insertionUsedNodes_mem_small
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {rowNodes columns row I T A nodes anchors : ZFSet.{u}}
    (hRowNodes : rowNodes ∈ M.sets) (hColumns : columns ∈ M.sets)
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets)
    (hNodes : nodes ∈ M.sets) (hAnchors : anchors ∈ M.sets)
    (rowCondition : row ∈ M.smallPartialFunctions (ZFSet.prod rowNodes columns) (natSetCode 2) ZFSet.omega)
    (rowSubset : rowNodes ⊆ nodes) (anchorFunction : ZFSet.IsFunc I nodes anchors)
    (smallA : M.groundEmbeddable A ZFSet.omega) :
    insertionUsedNodes rowNodes columns row I T A nodes anchors ∈ M.sets ∧
      M.groundEmbeddable (insertionUsedNodes rowNodes columns row I T A nodes anchors) ZFSet.omega ∧
      insertionUsedNodes rowNodes columns row I T A nodes anchors ⊆ nodes := by
  obtain ⟨hRows, smallRows⟩ := M.countablePartialFunctions_rowSupport pairing unions powers separation
    infinite choice hRowNodes hColumns (M.natSetCode_mem separation infinite 2) rowCondition
  have omega := M.omega_mem separation infinite
  have hIndices := M.assignmentIndices_mem pairing unions powers separation hI hT hA
  have smallIndices := M.assignmentIndices_small pairing unions powers separation choice hI hT hA omega smallA
  have hUsedAnchors := M.relationImage_mem separation hIndices hNodes hAnchors
  have smallAnchors := M.groundEmbeddable_function_image pairing unions powers separation choice
    hIndices hNodes omega hAnchors anchorFunction smallIndices
  refine ⟨M.binary_union_mem pairing unions hRows hUsedAnchors,
    M.groundCountable_binary_union pairing unions powers separation infinite choice
      hRows hUsedAnchors smallRows smallAnchors, ?_⟩
  intro v member
  rcases ZFSet.mem_union.1 member with usedRow | usedAnchor
  · exact rowSubset (rowUsedRows_subset _ _ _ _ usedRow)
  · exact ((mem_relationImage _ _ _ _).1 usedAnchor).1

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowAction_insertion_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∀ (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (h : G) (D K V : L),
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      a.iso h D ≤ K → h ∈ a.principalFix V →
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) →
        i.val ≤ K → i.val ≤ V) →
      ∃ q : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega),
        SetMembers.raw q = SetMembers.raw p ∪ SetMembers.raw (act.iso h p) ∧
        q ≤ p ∧ q ≤ act.iso h p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act p h D K V bound cap fixed avoid
  apply M.countableFunction_common_extension pairing unions powers separation infinite choice
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) p (act.iso h p)
  intro x y z left right
  have pc := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega p).2.1
  have hc := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega (act.iso h p)).2.1
  have coords := (ZFSet.pair_mem_prod.1 (pc.shape left)).1
  have hz := (ZFSet.pair_mem_prod.1 (hc.shape right)).2
  obtain ⟨row, hrow, col, hcol, rfl⟩ := ZFSet.mem_prod.1 coords
  obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier row).1 hrow
  have oldUsed := row_mem_rowUsedRows pc left
  have movedBound := M.internalRowAction_usedRows_bounded a s b C pairing unions powers separation
    infinite hL hC hG graph h p D bound i (row_mem_rowUsedRows hc right)
  have same := fixed i.val (avoid i oldUsed (le_trans movedBound cap))
  have old := (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
    hL hC hG graph h p i col z hcol hz).1 (by rw [same]; exact right)
  exact pc.unique _ y z left old

end PartitionPilot.Forcing.TransitiveGround



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
include fulfilled

theorem generated_insertion (infinite : Realize M.sets infinity Fin.elim0)
    {A c e d : ZFSet.{u}} (hA : A ∈ M.sets)
    (subset : A ⊆ (run.finalGeometry i₀).carrier) (nonempty : A.Nonempty)
    (hc : c ∈ (run.finalGeometry i₀).carrier) (he : e ∈ (run.finalGeometry i₀).carrier)
    (hd : d ∈ (run.finalGeometry i₀).carrier)
    (lower : ZFSet.pair c e ∈ (run.finalGeometry i₀).order)
    (strict : ZFSet.pair e c ∉ (run.finalGeometry i₀).order)
    (bound : ZFSet.pair c d ∈ (run.finalGeometry i₀).order)
    (above : ∀ a ∈ A, ZFSet.pair e a ∈ (run.finalGeometry i₀).order) :
    let geometry := run.finalGeometry i₀
    let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph A
    F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
      A ⊆ F ∧
      (∀ T, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph T → A ⊆ T → F ⊆ T) ∧
      (∀ x ∈ F, ZFSet.pair e x ∈ geometry.order) ∧
      ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
        FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
          geometry.meetGraph geometry.action c e d F caps actors := by
  let geometry := run.finalGeometry i₀
  let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph A
  have ground : F ∈ M.sets := M.generatedMeetFilter_mem pairing unions powers separation infinite
    geometry.carrier_ground geometry.order_ground geometry.meet_ground hA
  have filter := M.generatedMeetFilter_filter pairing unions separation infinite
    geometry.carrier_ground geometry.meet subset nonempty
  have contains := M.generatedMeetFilter_contains pairing unions separation infinite
    geometry.carrier_ground geometry.meet subset
  have allAbove := M.generatedMeetFilter_lower_bound pairing unions separation infinite
    geometry.carrier_ground geometry.meet subset he above
  exact ⟨ground, filter, contains,
    fun _ code includes => M.generatedMeetFilter_least pairing unions separation infinite
      geometry.carrier_ground geometry.meet subset code includes,
    allAbove, fulfilled.insertion c hc e he d hd F ground filter lower strict bound allAbove⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment



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
include fulfilled

theorem generated_insertion_exceptions
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (hLabels : Labels ∈ M.sets)
    {generators c e d Used Profiles extra : ZFSet.{u}}
    (hGenerators : generators ∈ M.sets)
    (subset : generators ⊆ (run.finalGeometry i₀).carrier) (nonempty : generators.Nonempty)
    (hc : c ∈ (run.finalGeometry i₀).carrier) (he : e ∈ (run.finalGeometry i₀).carrier)
    (hd : d ∈ (run.finalGeometry i₀).carrier)
    (lower : ZFSet.pair c e ∈ (run.finalGeometry i₀).order)
    (strict : ZFSet.pair e c ∉ (run.finalGeometry i₀).order)
    (bound : ZFSet.pair c d ∈ (run.finalGeometry i₀).order)
    (above : ∀ a ∈ generators, ZFSet.pair e a ∈ (run.finalGeometry i₀).order)
    (hUsed : Used ∈ M.sets) (hProfiles : Profiles ∈ M.sets) (hExtra : extra ∈ M.sets)
    (usedSubset : Used ⊆ (run.finalGeometry i₀).carrier)
    (filters : ∀ profile ∈ Profiles, MeetFilterCode (run.finalGeometry i₀).carrier
      (run.finalGeometry i₀).order (run.finalGeometry i₀).meetGraph profile)
    (smallUsed : M.groundEmbeddable Used ZFSet.omega)
    (smallProfiles : M.groundEmbeddable Profiles ZFSet.omega)
    (smallExtra : M.groundEmbeddable extra ZFSet.omega) (extraSubset : extra ⊆ Labels) :
    let geometry := run.finalGeometry i₀
    let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators
    F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
      generators ⊆ F ∧
      (∀ filter, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph filter →
        generators ⊆ filter → F ⊆ filter) ∧
      (∀ x ∈ F, ZFSet.pair e x ∈ geometry.order) ∧
      ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
        FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
          geometry.meetGraph geometry.action c e d F caps actors ∧
        ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ extra ⊆ bad ∧
          ∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
            (∀ node ∈ Used, ZFSet.pair node cap ∈ geometry.order →
              ZFSet.pair node c ∈ geometry.order) ∧
            (∀ profile ∈ Profiles, c ∉ profile → cap ∉ profile) := by
  let geometry := run.finalGeometry i₀
  obtain ⟨groundF, filter, contains, least, allAbove, caps, hCaps, actors, hActors, family⟩ :=
    fulfilled.generated_insertion infinite hGenerators subset nonempty hc he hd lower strict bound above
  exact ⟨groundF, filter, contains, least, allAbove, caps, hCaps, actors, hActors, family,
    family.exists_ground_countable_exceptions M pairing unions powers separation infinite choice
      hLabels geometry.carrier_ground geometry.order_ground (M.transitive geometry.carrier_ground hc)
      hCaps hUsed hProfiles hExtra geometry.meet usedSubset filters smallUsed smallProfiles
      smallExtra extraSubset⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




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

theorem structural_insertion_exceptions
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (_hmu : mu ∈ M.sets) (_muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
    (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
    (_stagesOrdinal : ordinalSetProperty stages)
    (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  ∀ (row : SetMembers c.carrier) (A : ZFSet.{u}),
    ZFSet.pair (c.encode row) A ∈ upperQ →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (ZFSet.pair (c.encode row) A) →
  ∀ (generators c0 e0 d0 extra : ZFSet.{u}), Labels ∈ M.sets →
    generators ∈ M.sets → generators ⊆ geometry.carrier → generators.Nonempty →
    c0 ∈ geometry.carrier → e0 ∈ geometry.carrier → d0 ∈ geometry.carrier →
    ZFSet.pair c0 e0 ∈ geometry.order → ZFSet.pair e0 c0 ∉ geometry.order →
    ZFSet.pair c0 d0 ∈ geometry.order →
    (∀ generator ∈ generators, ZFSet.pair e0 generator ∈ geometry.order) →
    extra ∈ M.sets → M.groundEmbeddable extra ZFSet.omega → extra ⊆ Labels →
  let L := ZFSet.prod stages (M.preparationWitnessBound s.carrier lifted upperQ)
  let Used := insertionUsedNodes s.nonbottom.carrier columns (SetMembers.raw row)
    indices lifted A s.carrier anchors
  ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
    selections ⊆ M.preparedWitnessSelections c.carrier lifted stages packed s.carrier
      (ZFSet.pair (c.encode row) A) A ∧
    relationImage A L selections ∈ M.sets ∧
    M.groundEmbeddable (relationImage A L selections) ZFSet.omega ∧
  let Profiles := M.preparedSelectionProfiles A stages upperQ s.carrier lifted selections
  Used ∈ M.sets ∧ M.groundEmbeddable Used ZFSet.omega ∧ Used ⊆ geometry.carrier ∧
  Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
    (∀ F ∈ Profiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
    (∀ x alpha sourceRow sourceA k enumerations z F B f,
      ZFSet.pair x (ZFSet.pair alpha
        (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈ selections →
      ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k → F ∈ Profiles) ∧
  let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators
  F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
    generators ⊆ F ∧
    (∀ filter, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph filter →
      generators ⊆ filter → F ⊆ filter) ∧
    (∀ x ∈ F, ZFSet.pair e0 x ∈ geometry.order) ∧
  ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
    FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
      geometry.meetGraph geometry.action c0 e0 d0 F caps actors ∧
  ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ extra ⊆ bad ∧
    ∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
      (∀ node ∈ Used, ZFSet.pair node cap ∈ geometry.order → ZFSet.pair node c0 ∈ geometry.order) ∧
      (∀ profile ∈ Profiles, c0 ∉ profile → cap ∉ profile) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro row A condition prepared generators c0 e0 d0 extra hLabels hGenerators generatorSubset
    generatorNonempty hc he hd lower strict bound above hExtra smallExtra extraSubset
  have profileSelection := M.semanticStructuralTrace_preparedProfileSelection c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder
    forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2
    closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace infinite choice
    condition prepared
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    profilesGround, profilesSmall, profileFilters, coverage⟩ := profileSelection
  let Profiles := M.preparedSelectionProfiles A stages upperQ s.carrier lifted selections
  have meetEq : canonicalMeetGraph s.carrier s.conditionOrder = geometry.meetGraph := by
    rw [geometry.decoded_order_eq]
    exact geometry.meet.eq_canonicalMeetGraph.symm
  have filters : ∀ F ∈ Profiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F := by
    intro F member
    have filter := profileFilters F member
    rw [meetEq, geometry.decoded_order_eq] at filter
    exact filter
  have candidate := ((M.mem_refinementHistoryForcing c.carrier lifted stages packed _).1 condition).1
  have Adata := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  obtain ⟨indicesGround, anchorsGround, anchorFunction⟩ := M.structuralIndexAnchorData
    b.carrier s.carrier s.conditionOrder (supportBasisCode s b a.principalFix) lifted squared
    stages history pairing unions powers separation collection hG hL order supports hLifted hSquared hs hh
  have used := M.insertionUsedNodes_mem_small pairing unions powers separation infinite choice
    (M.nonbottom_carrier_mem s separation hL) hColumns indicesGround hLifted Adata.2.1 hL
    anchorsGround (SetMembers.raw_mem row) (fun _ h => (s.mem_nonbottom_carrier _).1 h |>.1)
    anchorFunction Adata.2.2.2
  refine ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    used.1, used.2.1, used.2.2, profilesGround, profilesSmall, filters, coverage, ?_⟩
  exact fulfilled.generated_insertion_exceptions infinite choice hLabels hGenerators generatorSubset
    generatorNonempty hc he hd lower strict bound above used.1 profilesGround hExtra used.2.2
    filters used.2.1 profilesSmall smallExtra extraSubset






theorem structural_compatible_insertion_unions_oai
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
  ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
    (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
    (_stagesOrdinal : ordinalSetProperty stages)
    (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  ∀ (row : SetMembers c.carrier) (A : ZFSet.{u}),
    ZFSet.pair (c.encode row) A ∈ upperQ →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (ZFSet.pair (c.encode row) A) →
  ∀ (generators c0 e0 d0 extra : ZFSet.{u}), Labels ∈ M.sets →
    generators ∈ M.sets → generators ⊆ geometry.carrier → generators.Nonempty →
    c0 ∈ geometry.carrier → e0 ∈ geometry.carrier → d0 ∈ geometry.carrier →
    ZFSet.pair c0 e0 ∈ geometry.order → ZFSet.pair e0 c0 ∉ geometry.order →
    ZFSet.pair c0 d0 ∈ geometry.order →
    (∀ generator ∈ generators, ZFSet.pair e0 generator ∈ geometry.order) →
    extra ∈ M.sets → M.groundEmbeddable extra ZFSet.omega → extra ⊆ Labels →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) →
      ZFSet.pair (s.encode i) d0 ∈ geometry.order) →
    (∀ z ∈ A, ZFSet.pair z d0 ∈ stageOneDataBounds A indices lifted S s.carrier mu
      s.nonbottom.carrier s.conditionOrder anchors tuples) →
  let L := ZFSet.prod stages (M.preparationWitnessBound s.carrier lifted upperQ)
  let Used := insertionUsedNodes s.nonbottom.carrier columns (SetMembers.raw row)
    indices lifted A s.carrier anchors
  ∃ selections ∈ M.sets, ZFSet.IsFunc A L selections ∧
    selections ⊆ M.preparedWitnessSelections c.carrier lifted stages packed s.carrier
      (ZFSet.pair (c.encode row) A) A ∧
    relationImage A L selections ∈ M.sets ∧
    M.groundEmbeddable (relationImage A L selections) ZFSet.omega ∧
  let Profiles := M.preparedSelectionProfiles A stages upperQ s.carrier lifted selections
  Used ∈ M.sets ∧ M.groundEmbeddable Used ZFSet.omega ∧ Used ⊆ geometry.carrier ∧
  Profiles ∈ M.sets ∧ M.groundEmbeddable Profiles ZFSet.omega ∧
    (∀ F ∈ Profiles, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F) ∧
    (∀ x alpha sourceRow sourceA k enumerations z F B f,
      ZFSet.pair x (ZFSet.pair alpha
        (ZFSet.pair (ZFSet.pair sourceRow sourceA) (ZFSet.pair k enumerations))) ∈ selections →
      ZFSet.pair z (ZFSet.pair F (ZFSet.pair B f)) ∈ k → F ∈ Profiles) ∧
  let F := M.generatedMeetFilter geometry.carrier geometry.order geometry.meetGraph generators
  F ∈ M.sets ∧ MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
    generators ⊆ F ∧
    (∀ filter, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph filter →
      generators ⊆ filter → F ⊆ filter) ∧
    (∀ x ∈ F, ZFSet.pair e0 x ∈ geometry.order) ∧
  ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
    ∃ family : FinalInsertionFamiliesCode Labels geometry.carrier geometry.actors geometry.order
      geometry.meetGraph geometry.action c0 e0 d0 F caps actors,
  ∃ bad ∈ M.sets, bad ⊆ Labels ∧ M.groundEmbeddable bad ZFSet.omega ∧ extra ⊆ bad ∧
    (∀ label cap, ZFSet.pair label cap ∈ caps → label ∉ bad →
      (∀ node ∈ Used, ZFSet.pair node cap ∈ geometry.order → ZFSet.pair node c0 ∈ geometry.order) ∧
      (∀ profile ∈ Profiles, c0 ∉ profile → cap ∉ profile)) ∧
    (¬ M.groundEmbeddable Labels ZFSet.omega → ∃ label ∈ Labels, label ∉ bad) ∧
    ∀ label : SetMembers Labels, SetMembers.raw label ∉ bad →
      let h := family.decodedActors label
      let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h) A
      ∃ commonRow : SetMembers c.carrier,
        SetMembers.raw commonRow = SetMembers.raw row ∪ SetMembers.raw (act.iso h row) ∧
        ZFSet.pair (c.encode commonRow) (A ∪ movedA) ∈ upperQ ∧
        ZFSet.pair (ZFSet.pair (c.encode commonRow) (A ∪ movedA)) (ZFSet.pair (c.encode row) A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed ∧
        ZFSet.pair (ZFSet.pair (c.encode commonRow) (A ∪ movedA))
          (ZFSet.pair (c.encode (act.iso h row)) movedA) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro row A condition prepared generators c0 e0 d0 extra hLabels hGenerators generatorSubset
    generatorNonempty hc he hd lower strict bound above hExtra smallExtra extraSubset rowD dataD
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    usedGround, usedSmall, usedSubset, profilesGround, profilesSmall, profileFilters, coverage,
    filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, bad, hBad, badSubset, badSmall, containsExtra, good⟩ :=
    fulfilled.structural_insertion_exceptions collection infinite choice columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace row A condition prepared generators c0 e0 d0 extra
      hLabels hGenerators generatorSubset generatorNonempty hc he hd lower strict bound above
      hExtra smallExtra extraSubset
  have available : ¬ M.groundEmbeddable Labels ZFSet.omega → ∃ label ∈ Labels, label ∉ bad := by
    classical
    intro notSmall
    by_contra none
    apply notSmall
    have equal : bad = Labels := by
      apply ZFSet.ext
      intro label
      exact ⟨fun member => badSubset member, fun member => by
        by_contra outside
        exact none ⟨label, member, outside⟩⟩
    rwa [equal] at badSmall
  refine ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    usedGround, usedSmall, usedSubset, profilesGround, profilesSmall, profileFilters, coverage,
    filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, bad, hBad, badSubset, badSmall, containsExtra, good, available, ?_⟩
  intro label goodLabel
  let h := family.decodedActors label
  let cap := family.decodedCaps label
  let V : SetMembers geometry.carrier := SetMembers.ofMem c0 hc
  let D0 : SetMembers geometry.carrier := SetMembers.ofMem d0 hd
  have actorEdge := family.decodedActors_entry label
  have capEdge := family.decodedCaps_entry label
  have goodLaws := good _ _ capEdge goodLabel
  have fixed : h ∈ a.principalFix V := by
    intro v hv
    apply (geometry.action_code.act_eq_iff h v v).2
    apply family.fixes _ _ actorEdge _ (SetMembers.raw_mem v)
    change ZFSet.pair (SetMembers.raw v) (SetMembers.raw V) ∈ geometry.order at hv
    simpa only [V, SetMembers.raw_ofMem] using hv
  have belowCap : a.iso h D0 ≤ cap := by
    change ZFSet.pair (SetMembers.raw (a.iso h D0)) (SetMembers.raw cap) ∈ geometry.order
    apply family.dominates _ _ _ actorEdge capEdge _ (SetMembers.raw_mem _)
    have entry : ZFSet.pair (ZFSet.pair (SetMembers.raw h) (SetMembers.raw D0))
        (SetMembers.raw (a.iso h D0)) ∈ geometry.action := geometry.action_code.act_mem h D0
    change ZFSet.pair (ZFSet.pair (SetMembers.raw h) d0)
      (SetMembers.raw (a.iso h D0)) ∈ geometry.action
    simpa only [D0, SetMembers.raw_ofMem] using entry
  have usedD (i : {i : SetMembers geometry.carrier // i ≠ ⊥})
      (used : s.encode i.val ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row)) :
      i.val ≤ D0 := by
    change ZFSet.pair (SetMembers.raw i.val) (SetMembers.raw D0) ∈ geometry.order
    have bound : ZFSet.pair (SetMembers.raw i.val) d0 ∈ geometry.order := rowD i.val used
    simpa only [D0, SetMembers.raw_ofMem] using bound
  have avoidRows (i : {i : SetMembers geometry.carrier // i ≠ ⊥})
      (used : s.encode i.val ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row))
      (below : i.val ≤ cap) : i.val ≤ V := by
    change ZFSet.pair (SetMembers.raw i.val) (SetMembers.raw V) ∈ geometry.order
    rw [SetMembers.raw_ofMem]
    exact goodLaws.1 _ (ZFSet.mem_union.2 (Or.inl used)) below
  obtain ⟨commonRow, rowCode, below, belowH⟩ := M.internalRowAction_insertion_union a s b columns
    pairing unions powers separation infinite hL hC hG graph choice row h D0 cap V usedD belowCap fixed avoidRows
  have candidate := ((M.mem_refinementHistoryForcing c.carrier lifted stages packed _).1 condition).1
  have Adata := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 candidate
  have originalData : ∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈
      stageOneDataBounds A indices lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples := by
    have code : s.encode D0 = d0 := SetMembers.raw_ofMem d0 hd
    rw [code]
    exact dataD
  have transported := M.binaryRowStructuralAssignmentImage_dataBound a s b columns pairing unions powers
    separation collection infinite hL order hC hG graph nodeMaps supports directed hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace h D0 A Adata.2.1 originalData
  have anchorGood : ∀ idx u w E,
      stageOneAssignment idx u w ∈ A → ZFSet.pair idx E ∈ anchors →
      ZFSet.pair E (s.encode cap) ∈ s.conditionOrder → ZFSet.pair E (s.encode V) ∈ s.conditionOrder := by
    intro idx u w E assignment anchor lowerCap
    have fields := (stageOneAssignment_mem_assignments indices lifted idx u w).1 (Adata.2.2.1 assignment)
    have Ebound : E ∈ s.carrier := (ZFSet.pair_mem_prod.1
      ((M.structuralIndexAnchors_function b.carrier s.carrier s.conditionOrder
        (supportBasisCode s b a.principalFix) lifted squared stages history).1 anchor)).2
    have used := (mem_insertionUsedNodes s.nonbottom.carrier columns (SetMembers.raw row)
      indices lifted A s.carrier anchors E).2 (Or.inr
        ⟨Ebound, idx, fields.1, u, fields.2.1, w, fields.2.2, assignment, anchor⟩)
    rw [geometry.decoded_order_eq] at lowerCap ⊢
    change ZFSet.pair E (SetMembers.raw V) ∈ geometry.order
    rw [SetMembers.raw_ofMem]
    exact goodLaws.1 E used lowerCap
  have profileGood : ∀ F ∈ M.preparedSelectionProfiles A stages upperQ s.carrier lifted selections,
      s.encode V ∉ F → s.encode cap ∉ F := by
    have code : s.encode V = c0 := SetMembers.raw_ofMem c0 hc
    rw [code]
    exact goodLaws.2
  have unionFacts := M.semanticStructuralTrace_insertion_union c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace infinite choice small indices S mu s.nonbottom.carrier tuples
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun D f _ tau entry bound => M.liftedRowTuple_supported a s b columns pairing unions powers separation
      infinite hL hC hG graph hmu muOrdinal valid f tau D entry bound.2)
    row commonRow A selections h D0 cap V condition function selected rangeGround rangeSmall
    below belowH fixed belowCap anchorGood profileGood transported.2.2
  exact ⟨commonRow, rowCode, unionFacts⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_compatible_insertion_unions_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_compatible_insertion_unions_oai.{u, v}
