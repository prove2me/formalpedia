-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology.final_insertion_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:12:51.067452+00:00
-- url     : https://prove2.me/submissions/001f9d6f-48e2-4b00-bcc5-5d7a574ac281

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
import Definitions.Def_OAIQ253P009

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPairCompositions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing

universe u v w

namespace BoundedFormula

open SetFormula

theorem truth_literalTaskFormula {n} (z a c ell e F label : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (literalTaskFormula z a c ell e F label) env ↔
      env z = literalTaskCode (env a) (env c) (env ell) (env e) (env F) (env label) := by
  simp only [literalTaskFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ u ∈ env z, ∃ v ∈ u, env z = ZFSet.pair (env a) v ∧
    ∃ u' ∈ v, ∃ v' ∈ u', v = ZFSet.pair (env c) v' ∧
    ∃ u'' ∈ v', ∃ v'' ∈ u'', v' = ZFSet.pair (env ell) v'' ∧
    ∃ u''' ∈ v'', ∃ v''' ∈ u''', v'' = ZFSet.pair (env e) v''' ∧
      v''' = ZFSet.pair (env F) (env label)) ↔ _
  constructor
  · rintro ⟨_, _, v, _, outer, _, _, v', _, second, _, _, v'', _, third,
      _, _, v''', _, fourth, last⟩
    rw [outer, second, third, fourth, last]
    rfl
  · intro equal
    let v''' := ZFSet.pair (env F) (env label)
    let v'' := ZFSet.pair (env e) v'''
    let v' := ZFSet.pair (env ell) v''
    let v := ZFSet.pair (env c) v'
    have outer : env z = ZFSet.pair (env a) v := equal
    refine ⟨{env a, v}, ?_, v, ZFSet.mem_pair.2 (Or.inr rfl), outer,
      {env c, v'}, ZFSet.mem_pair.2 (Or.inr rfl), v', ZFSet.mem_pair.2 (Or.inr rfl), rfl,
      {env ell, v''}, ZFSet.mem_pair.2 (Or.inr rfl), v'', ZFSet.mem_pair.2 (Or.inr rfl), rfl,
      {env e, v'''}, ZFSet.mem_pair.2 (Or.inr rfl), v''', ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl⟩
    rw [outer]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MapFamilyApplicationGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



open SetFormula
universe u

theorem pair_mem_mapFamilyApplicationGraph (I P Q family i x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i x) y ∈ mapFamilyApplicationGraph I P Q family ↔
      i ∈ I ∧ x ∈ P ∧ y ∈ Q ∧ ∃ f, ZFSet.pair i f ∈ family ∧ ZFSet.pair x y ∈ f := by
  rw [mapFamilyApplicationGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, a, ha, b, hb, f, _, equal, indexed, entry⟩
    obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    exact ⟨hj, ha, hb, f, indexed, entry⟩
  · rintro ⟨hi, hx, hy, f, indexed, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy⟩,
      i, hi, x, hx, y, hy, f, pair_second_mem_doubleUnion indexed, rfl, indexed, entry⟩

namespace BoundedFormula

theorem truth_mapFamilyApplicationEntryFormula {n} (z I P Q B family : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mapFamilyApplicationEntryFormula z I P Q B family) env ↔
      ∃ i ∈ env I, ∃ x ∈ env P, ∃ y ∈ env Q, ∃ f ∈ env B,
        env z = ZFSet.pair (ZFSet.pair i x) y ∧
          ZFSet.pair i f ∈ env family ∧ ZFSet.pair x y ∈ f := by
  simp only [mapFamilyApplicationEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mapFamilyApplicationGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Q family : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQ : Q ∈ M.sets) (hFamily : family ∈ M.sets) :
    mapFamilyApplicationGraph I P Q family ∈ M.sets := by
  have hB := M.union_mem unions (M.union_mem unions hFamily)
  let params := extend I (extend P (extend Q (extend (ZFSet.sUnion (ZFSet.sUnion family)) (extend family Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.mapFamilyApplicationEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hP (Fin.cases hQ (Fin.cases hB (Fin.cases hFamily
      (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hI hP) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.mapFamilyApplicationEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod I P) Q) = mapFamilyApplicationGraph I P Q family := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mapFamilyApplicationGraph, ZFSet.mem_sep,
      BoundedFormula.truth_mapFamilyApplicationEntryFormula]
    rfl
  exact equal ▸ selected

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

theorem mem_copyPullback (A L e F x : ZFSet.{u}) :
    x ∈ copyPullback A L e F ↔
      x ∈ A ∧ ∃ y ∈ F, y ∈ L ∧ ZFSet.pair x y ∈ e := by
  rw [copyPullback, mem_relationImage]
  constructor
  · rintro ⟨hx, y, hy, rel⟩
    exact ⟨hx, y, hy, ((pair_mem_relationConverse A L e x y).1 rel).2⟩
  · rintro ⟨hx, y, hy, hyL, rel⟩
    exact ⟨hx, y, hy, (pair_mem_relationConverse A L e x y).2 ⟨hx, hyL, rel⟩⟩

theorem relationImage_copyPullback {A L e : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e) (F : ZFSet.{u}) :
    relationImage (copyPullback A L e F) L e = F ∩ relationImage A L e := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, ZFSet.mem_inter, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, rel⟩
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    have equal : y = z := (unique y rel).trans (unique z relz).symm
    exact ⟨equal ▸ hz, hy, x, hxA, rel⟩
  · rintro ⟨hyF, hy, x, hx, rel⟩
    exact ⟨hy, x, (mem_copyPullback A L e F x).2 ⟨hx, y, hyF, hy, rel⟩, rel⟩

theorem CoinitialBelowCode.copy {A L e sourceOrder targetOrder F target B : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : CoinitialBelowCode sourceOrder (copyPullback A L e F) target B) :
    CoinitialBelowCode targetOrder F (relationImage target L e) (relationImage B L e) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage B L e y).1 hy
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 (basis.1 hx)
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    exact (unique y rel).trans (unique z relz).symm ▸ hz
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage target L e y).1 hy
    obtain ⟨b, hb, below⟩ := basis.2 x hx
    have hbA := ((mem_copyPullback A L e F b).1 (basis.1 hb)).1
    obtain ⟨b', relb, _⟩ := func.2 b hbA
    have hbL := (ZFSet.pair_mem_prod.1 (func.1 relb)).2
    exact ⟨b', (mem_relationImage B L e b').2 ⟨hbL, b, hb, relb⟩,
      monotone b x b' y below relb rel⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem copyPullback_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A L e F : ZFSet.{u}} (hA : A ∈ M.sets) (hL : L ∈ M.sets)
    (he : e ∈ M.sets) (hF : F ∈ M.sets) : copyPullback A L e F ∈ M.sets :=
  M.relationImage_mem separation hF hA
    (M.relationConverse_mem pairing unions powers separation hA hL he)

theorem internalCountableBelow_copy
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F target : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F) target) :
    M.InternalCountableBelow targetOrder F (relationImage target L e) := by
  obtain ⟨B, hB, small, coinitial⟩ := basis
  have subset : B ⊆ A := fun x hx => ((mem_copyPullback A L e F x).1 (coinitial.1 hx)).1
  exact ⟨relationImage B L e, M.relationImage_mem separation hB hL he,
    M.groundEmbeddable_image pairing unions powers separation hB hL
      (M.omega_mem separation infinite) he code subset small,
    coinitial.copy code.function monotone⟩

theorem internalCountableBelow_copy_pullback
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F)
      (copyPullback A L e F)) :
    M.InternalCountableBelow targetOrder F (F ∩ relationImage A L e) := by
  rw [← relationImage_copyPullback code.function F]
  exact M.internalCountableBelow_copy pairing unions powers separation infinite hL he code monotone basis

end TransitiveGround






theorem pair_mem_basisChoiceRelation (I W order target parts i B : ZFSet.{u}) :
    ZFSet.pair i B ∈ basisChoiceRelation I W order target parts ↔
      i ∈ I ∧ B ∈ W ∧ FiberCoveredCode order target parts i B := by
  rw [basisChoiceRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, A, hA, eq, covers⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hj, hA, covers⟩
  · rintro ⟨hi, hB, covers⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hB⟩, i, hi, B, hB, rfl, covers⟩

namespace BoundedFormula

open SetFormula

theorem truth_fiberCoveredFormula {n} (order target parts i B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fiberCoveredFormula order target parts i B) env ↔
      FiberCoveredCode (env order) (env target) (env parts) (env i) (env B) := by
  simp only [fiberCoveredFormula, Truth, truth_imp, truth_exMem, truth_pairMembershipFormula]
  rfl

theorem truth_basisChoiceEntryFormula {n} (z I W order target parts : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (basisChoiceEntryFormula z I W order target parts) env ↔
      ∃ i ∈ env I, ∃ B ∈ env W, env z = ZFSet.pair i B ∧
        FiberCoveredCode (env order) (env target) (env parts) i B := by
  simp only [basisChoiceEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_fiberCoveredFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem basisChoiceRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W order target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hW : W ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets) :
    basisChoiceRelation I W order target parts ∈ M.sets := by
  let params := extend I (extend W (extend order (extend target (extend parts Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hOrder (Fin.cases hTarget (Fin.cases hParts
      (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hI hW)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) (extend z params)) (ZFSet.prod I W) =
      basisChoiceRelation I W order target parts := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, basisChoiceRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_basisChoiceEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem internalCountableBelow_indexed_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I order F target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hOrder : order ∈ M.sets)
    (hF : F ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets)
    (smallI : M.groundEmbeddable I ZFSet.omega)
    (cover : ∀ x ∈ target, ∃ i ∈ I, ZFSet.pair i x ∈ parts)
    (localBases : ∀ i ∈ I, M.InternalCountableBelow order F (relationFiber target parts i)) :
    M.InternalCountableBelow order F target := by
  have hO := M.omega_mem separation infinite
  let W := M.groundSmallSubsets F ZFSet.omega
  have hW : W ∈ M.sets := M.groundSmallSubsets_mem powers separation hF hO
  have choices := M.basisChoiceRelation_mem pairing unions powers separation hI hW hOrder hTarget hParts
  have total (i : ZFSet.{u}) (hi : i ∈ I) :
      ∃ B ∈ W, ZFSet.pair i B ∈ basisChoiceRelation I W order target parts := by
    obtain ⟨B, hB, smallB, positive, below⟩ := localBases i hi
    have hBW : B ∈ W := (M.mem_groundSmallSubsets F ZFSet.omega B).2 ⟨hB, positive, smallB⟩
    exact ⟨B, hBW, (pair_mem_basisChoiceRelation I W order target parts i B).2
      ⟨hi, hBW, fun x hx rel => below x ((mem_relationFiber target parts i x).2 ⟨hx, rel⟩)⟩⟩
  obtain ⟨g, hg, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hI hW choices total
  let family := relationImage I W g
  have hFamily : family ∈ M.sets := M.relationImage_mem separation hI hW hg
  have smallFamily : M.groundEmbeddable family ZFSet.omega :=
    M.groundEmbeddable_function_image pairing unions powers separation choice hI hW hO hg func smallI
  have candidates (B : ZFSet.{u}) (hB : B ∈ family) : B ∈ W :=
    ((mem_relationImage I W g B).1 hB).1
  have smallBasis (B : ZFSet.{u}) (hB : B ∈ family) : M.groundEmbeddable B ZFSet.omega :=
    ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.2
  refine ⟨family.sUnion, M.union_mem unions hFamily,
    M.groundCountable_family_union pairing unions powers separation infinite choice
      hFamily smallFamily smallBasis, ?_, ?_⟩
  · intro x hx
    obtain ⟨B, hB, xB⟩ := ZFSet.mem_sUnion.1 hx
    exact ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.1 xB
  · intro x hx
    obtain ⟨i, hi, ix⟩ := cover x hx
    obtain ⟨B, chosen, _⟩ := func.2 i hi
    have spec := (pair_mem_basisChoiceRelation I W order target parts i B).1 (selected chosen)
    obtain ⟨b, hb, lower⟩ := spec.2.2 x hx ix
    have hB : B ∈ family := (mem_relationImage I W g B).2 ⟨spec.2.1, i, hi, chosen⟩
    exact ⟨b, ZFSet.mem_sUnion.2 ⟨B, hB, hb⟩, lower⟩

end TransitiveGround

end



namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem InternalCountableBelow.mono {order F target smaller : ZFSet.{u}}
    (basis : M.InternalCountableBelow order F target) (subset : smaller ⊆ target) :
    M.InternalCountableBelow order F smaller := by
  obtain ⟨B, hB, small, positive, below⟩ := basis
  exact ⟨B, hB, small, positive, fun x hx => below x (subset hx)⟩

theorem internalCountableBelow_empty (inhabited : M.sets.Nonempty) (order F : ZFSet.{u}) :
    M.InternalCountableBelow order F ∅ := by
  exact ⟨∅, M.empty_mem inhabited, M.empty_groundEmbeddable ZFSet.omega inhabited,
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx),
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx)⟩

theorem internalCountableBelow_of_countable {order F target : ZFSet.{u}}
    (hTarget : target ∈ M.sets) (small : M.groundEmbeddable target ZFSet.omega)
    (positive : target ⊆ F) (refl : ∀ x ∈ target, ZFSet.pair x x ∈ order) :
    M.InternalCountableBelow order F target :=
  ⟨target, hTarget, small, positive, fun x hx => ⟨x, hx, refl x hx⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologicalBasis
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem mem_birthEssentialSet (F T r birth x : ZFSet.{u}) :
    x ∈ birthEssentialSet F T r birth ↔ x ∈ F ∧
      ∀ y ∈ F, ∀ a ∈ T, ∀ b ∈ T,
        ZFSet.pair y x ∈ r → ZFSet.pair y a ∈ birth → ZFSet.pair x b ∈ birth → a ∉ b :=
  ZFSet.mem_sep

theorem birthEssentialSet_subset (F T r birth : ZFSet.{u}) :
    birthEssentialSet F T r birth ⊆ F := fun _ hx => (ZFSet.mem_sep.1 hx).1

theorem mem_essentialBirthIndices (F T r birth t : ZFSet.{u}) :
    t ∈ essentialBirthIndices F T r birth ↔ t ∈ T ∧
      ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair x t ∈ birth :=
  mem_relationImage _ _ _ _

theorem positive_above_birthEssential {L F T r birth : ZFSet.{u}}
    (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (refl : ∀ x ∈ L, ZFSet.pair x x ∈ r)
    (trans : ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
      ZFSet.pair x y ∈ r → ZFSet.pair y z ∈ r → ZFSet.pair x z ∈ r)
    {x : ZFSet.{u}} (positive : x ∈ F) :
    ∃ y ∈ birthEssentialSet F T r birth, ZFSet.pair y x ∈ r := by
  let S : Set ZFSet.{u} := {t | ∃ y ∈ F, ZFSet.pair y x ∈ r ∧ ZFSet.pair y t ∈ birth}
  obtain ⟨t, xt, _⟩ := born.2 x (subset positive)
  have inhabited : S.Nonempty := ⟨t, x, positive, refl x (subset positive), xt⟩
  obtain ⟨t, ⟨y, hy, below, yt⟩, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨y, (mem_birthEssentialSet F T r birth y).2 ⟨hy, ?_⟩, below⟩
  intro z hz a _ b _ zy za yb earlier
  obtain ⟨_, _, unique⟩ := born.2 y (subset hy)
  have eq : b = t := (unique b yb).trans (unique t yt).symm
  have aS : a ∈ S := ⟨z, hz, trans z (subset hz) y (subset hy) x (subset positive) zy below, za⟩
  exact minimal a aS (eq ▸ earlier)

namespace BoundedFormula

open SetFormula

theorem truth_birthEssentialFormula {n} (x f t r birth : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (birthEssentialFormula x f t r birth) env ↔
      ∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
        ZFSet.pair y (env x) ∈ env r → ZFSet.pair y a ∈ env birth →
          ZFSet.pair (env x) b ∈ env birth → a ∉ b := by
  simp only [birthEssentialFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change (∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
    ZFSet.pair y (env x) ∈ env r ∧ ZFSet.pair y a ∈ env birth ∧
      ZFSet.pair (env x) b ∈ env birth → a ∉ b) ↔ _
  constructor
  · intro h y hy a ha b hb below bornY bornX
    exact h y hy a ha b hb ⟨below, bornY, bornX⟩
  · intro h y hy a ha b hb premises
    exact h y hy a ha b hb premises.1 premises.2.1 premises.2.2

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem birthEssentialSet_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    birthEssentialSet F T r birth ∈ M.sets := by
  let params := extend F (extend T (extend r (extend birth Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.birthEssentialFormula 0 1 2 3 4) params
    (Fin.cases hF (Fin.cases hT (Fin.cases hr (Fin.cases hBirth (fun j => Fin.elim0 j))))) hF
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.birthEssentialFormula 0 1 2 3 4) (extend x params)) F =
      birthEssentialSet F T r birth := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_birthEssentialSet]
    exact and_congr Iff.rfl (BoundedFormula.truth_birthEssentialFormula 0 1 2 3 4 _)
  exact eq ▸ selected

theorem essentialBirthIndices_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    essentialBirthIndices F T r birth ∈ M.sets :=
  M.relationImage_mem separation (M.birthEssentialSet_mem separation hF hT hr hBirth) hT hBirth

theorem exists_essentialBirthRepresentatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    ∃ g ∈ M.sets,
      ZFSet.IsFunc (essentialBirthIndices F T r birth) (birthEssentialSet F T r birth) g ∧
      g ⊆ relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth ∧
      ∀ t ∈ essentialBirthIndices F T r birth,
        ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair t x ∈ g ∧ ZFSet.pair x t ∈ birth := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hConverse := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have total : ∀ t ∈ S, ∃ x ∈ E, ZFSet.pair t x ∈ relationConverse E S birth := by
    intro t ht
    obtain ⟨_, x, hx, born⟩ := (mem_essentialBirthIndices F T r birth t).1 ht
    exact ⟨x, hx, (pair_mem_relationConverse E S birth x t).2 ⟨hx, ht, born⟩⟩
  obtain ⟨g, hg, function, restricted⟩ :=
    M.uniformize_relation pairing unions powers separation choice hS hE hConverse total
  refine ⟨g, hg, function, restricted, ?_⟩
  intro t ht
  obtain ⟨x, chosen, _⟩ := function.2 t ht
  have spec := (pair_mem_relationConverse E S birth x t).1 (restricted chosen)
  exact ⟨x, spec.1, chosen, spec.2.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem internal_countable_basis_of_birth_layers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (order : PartialOrderCode L r) (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (small : M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    M.InternalCountableBelow r F F := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  let parts := relationConverse E S birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hParts : parts ∈ M.sets := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have cover (x : ZFSet.{u}) (hx : x ∈ E) : ∃ t ∈ S, ZFSet.pair t x ∈ parts := by
    obtain ⟨t, xt, _⟩ := born.2 x (subset (birthEssentialSet_subset F T r birth hx))
    have htT := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
    have htS : t ∈ S := (mem_essentialBirthIndices F T r birth t).2 ⟨htT, x, hx, xt⟩
    exact ⟨t, htS, (pair_mem_relationConverse E S birth x t).2 ⟨hx, htS, xt⟩⟩
  obtain ⟨B, hB, smallB, positive, below⟩ := M.internalCountableBelow_indexed_union
    pairing unions powers separation infinite choice hS hr hF hE hParts small cover localBases
  refine ⟨B, hB, smallB, positive, ?_⟩
  intro x hx
  obtain ⟨y, hy, yx⟩ := positive_above_birthEssential subset born order.refl order.trans hx
  obtain ⟨b, hb, byLower⟩ := below y hy
  exact ⟨b, hb, order.trans b (subset (positive hb)) y
    (subset (birthEssentialSet_subset F T r birth hy)) x (subset hx) byLower yx⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNaturalFamilyShift
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem mem_heightColumnFiber (S C Q h c i : ZFSet.{u}) :
    i ∈ heightColumnFiber S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ ∃ q ∈ Q, ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnFiber, mem_relationImage]
  constructor
  · rintro ⟨hi, v, hv, vi⟩
    obtain ⟨a, ha, q, hq, rfl⟩ := ZFSet.mem_prod.1 hv
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    have rel := (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).1 vi
    exact ⟨hi, (ZFSet.pair_mem_prod.1 rel.2.1).1, q, hq, rel.2.2⟩
  · rintro ⟨hi, hc, q, hq, iq⟩
    exact ⟨hi, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hq⟩,
      (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).2
        ⟨hi, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq⟩⟩

theorem pair_mem_heightColumnGraph (S C Q h c i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ heightColumnGraph S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ q ∈ Q ∧ ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨hi, hq, v, hv, iv, vq⟩
    obtain ⟨a, ha, b, _, eq⟩ := (mem_productSecond {c} Q (ZFSet.pair v q)).1 vq
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hi, (ZFSet.pair_mem_prod.1 hv).1, hq, iv⟩
  · rintro ⟨hi, hc, hq, iq⟩
    exact ⟨hi, hq, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq,
      (mem_productSecond {c} Q _).2 ⟨c, ZFSet.mem_singleton.2 rfl, q, hq, rfl⟩⟩

theorem heightColumnGraph_injection {S C Q h : ZFSet.{u}}
    (height : InjectionCode S (ZFSet.prod C Q) h) (c : ZFSet.{u}) :
    InjectionCode (heightColumnFiber S C Q h c) Q (heightColumnGraph S C Q h c) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have shape : z ∈ ZFSet.prod S Q := (ZFSet.mem_sep.1
      (show z ∈ relationCompose S (ZFSet.prod C Q) Q h (productSecond {c} Q) from hz)).1
    obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 shape
    obtain ⟨_, hc, _, iq⟩ := (pair_mem_heightColumnGraph S C Q h c i q).1 hz
    exact ZFSet.pair_mem_prod.2
      ⟨(mem_heightColumnFiber S C Q h c i).2 ⟨hi, hc, q, hq, iq⟩, hq⟩
  · intro i hi
    obtain ⟨hiS, hc, q, hq, iq⟩ := (mem_heightColumnFiber S C Q h c i).1 hi
    refine ⟨q, (pair_mem_heightColumnGraph S C Q h c i q).2 ⟨hiS, hc, hq, iq⟩, ?_⟩
    intro r ir
    have irh := (pair_mem_heightColumnGraph S C Q h c i r).1 ir
    obtain ⟨v, _, unique⟩ := height.function.2 i hiS
    exact (ZFSet.pair_inj.1 ((unique _ irh.2.2.2).trans (unique _ iq).symm)).2
  · intro i j q iq jq
    exact height.injective i j (ZFSet.pair c q)
      ((pair_mem_heightColumnGraph S C Q h c i q).1 iq).2.2.2
      ((pair_mem_heightColumnGraph S C Q h c j q).1 jq).2.2.2

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightColumnFiber_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnFiber S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationImage_mem separation
    (M.prod_mem pairing unions powers separation singleton hQ) hS
    (M.relationConverse_mem pairing unions powers separation hS
      (M.prod_mem pairing unions powers separation hC hQ) hh)

theorem heightColumnGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnGraph S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationCompose_mem pairing unions powers separation hS
    (M.prod_mem pairing unions powers separation hC hQ) hQ hh
    (M.productSecond_mem pairing unions powers separation singleton hQ)

theorem groundEmbeddable_heightColumnFiber
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c N : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) (hN : N ∈ M.sets)
    (height : InjectionCode S (ZFSet.prod C Q) h) (small : M.groundEmbeddable Q N) :
    M.groundEmbeddable (heightColumnFiber S C Q h c) N := by
  obtain ⟨f, hf, code⟩ := small
  exact ⟨relationCompose (heightColumnFiber S C Q h c) Q N (heightColumnGraph S C Q h c) f,
    M.relationCompose_mem pairing unions powers separation
      (M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh hc) hQ hN
      (M.heightColumnGraph_mem pairing unions powers separation hS hC hQ hh hc) hf,
    (heightColumnGraph_injection height c).compose code⟩

end TransitiveGround

end



section

open SetRealization
universe u

theorem ordinalSubset_has_least {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    {S : Set ZFSet.{u}} (subset : ∀ i ∈ S, i ∈ T) (inhabited : S.Nonempty) :
    ∃ i ∈ S, ∀ j ∈ S, i = j ∨ i ∈ j := by
  obtain ⟨i, hi, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨i, hi, ?_⟩
  intro j hj
  rcases ordinalSetProperty_mem_compare ordinal (subset i hi) (subset j hj) with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact False.elim (minimal j hj h)

theorem mem_ordinalIndexTail (S i j : ZFSet.{u}) :
    j ∈ ordinalIndexTail S i ↔ j ∈ S ∧ (i = j ∨ i ∈ j) := ZFSet.mem_sep

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem ordinalIndexTail_mem (separation : SeparationSchema M.sets)
    {S i : ZFSet.{u}} (hS : S ∈ M.sets) (hi : i ∈ M.sets) :
    ordinalIndexTail S i ∈ M.sets := by
  have selected := M.bounded_separation_mem separation (.disj (.equal 1 0) (.mem 1 0))
    (extend i Fin.elim0) (Fin.cases hi (fun j => Fin.elim0 j)) hS
  simpa only [BoundedFormula.truth_disj, BoundedFormula.Truth, extend, Fin.cases_zero,
    show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ, ordinalIndexTail] using selected

theorem groundCountable_descending_heights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S T C Q h : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (subset : S ⊆ T)
    (ordinal : ordinalSetProperty T) (height : InjectionCode S (ZFSet.prod C Q) h)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (antitone : ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d r,
      ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d r) ∈ h →
        d = c ∨ d ∈ c) :
    M.groundEmbeddable S ZFSet.omega := by
  classical
  have hOmega := M.omega_mem separation infinite
  have tails : ∀ c, ∀ i ∈ S, ∀ q, ZFSet.pair i (ZFSet.pair c q) ∈ h →
      M.groundEmbeddable (ordinalIndexTail S i) ZFSet.omega := by
    intro c
    induction c using ZFSet.inductionOn with
    | h c ih =>
      intro i hi q iq
      have hc := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iq)).2).1
      have groundTail := M.ordinalIndexTail_mem separation hS (M.transitive hS hi)
      have groundFiber := M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh
        (M.transitive hC hc)
      have smallFiber := M.groundEmbeddable_heightColumnFiber pairing unions powers separation
        hS hC hQ hh (M.transitive hC hc) hOmega height smallQ
      have columnBelow (k : ZFSet.{u}) (hk : k ∈ S) (later : i = k ∨ i ∈ k)
          (d r : ZFSet.{u}) (kr : ZFSet.pair k (ZFSet.pair d r) ∈ h) : d = c ∨ d ∈ c := by
        rcases later with rfl | later
        · obtain ⟨_, _, unique⟩ := height.function.2 i hi
          exact Or.inl (ZFSet.pair_inj.1 ((unique _ kr).trans (unique _ iq).symm)).1
        · exact antitone i hi k hk later c q d r iq kr
      let lower : Set ZFSet.{u} := {j | j ∈ S ∧ (i = j ∨ i ∈ j) ∧
        ∃ d r, d ∈ c ∧ ZFSet.pair j (ZFSet.pair d r) ∈ h}
      by_cases inhabited : lower.Nonempty
      · obtain ⟨j, hj, minimal⟩ := ordinalSubset_has_least ordinal
          (fun k hk => subset hk.1) inhabited
        obtain ⟨hjS, _, d, r, dc, jr⟩ := hj
        have smallLater := ih d dc j hjS r jr
        have smallUnion := M.groundCountable_binary_union pairing unions powers separation
          infinite choice groundFiber (M.ordinalIndexTail_mem separation hS (M.transitive hS hjS))
          smallFiber smallLater
        apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallUnion
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact ZFSet.mem_union.2 (Or.inl
            ((mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩))
        · have klower : k ∈ lower := ⟨hkS, later, e, s, less, kv⟩
          exact ZFSet.mem_union.2 (Or.inr
            ((mem_ordinalIndexTail S j k).2 ⟨hkS, minimal k klower⟩))
      · apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallFiber
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact (mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩
        · exact False.elim (inhabited ⟨k, hkS, later, e, s, less, kv⟩)
  by_cases inhabited : (S.toSet).Nonempty
  · obtain ⟨i, hi, minimal⟩ := ordinalSubset_has_least ordinal (fun _ hx => subset hx) inhabited
    obtain ⟨v, iv, _⟩ := height.function.2 i hi
    obtain ⟨c, _, q, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iv)).2
    exact M.groundEmbeddable_restrict separation hS hOmega
      (fun j hj => (mem_ordinalIndexTail S i j).2 ⟨hj, minimal j hj⟩) (tails c i hi q iv)
  · have empty : S = ∅ := by
      apply ZFSet.ext
      intro x
      exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
        fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    rw [empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨S, hS⟩

end TransitiveGround






theorem essentialHeightComposite_strict {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt)
    {i j c q d v : ZFSet.{u}} (earlier : i ∈ j)
    (first : ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
    (second : ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height) :
    d ∈ c ∨ (d = c ∧ ZFSet.pair v q ∈ qlt) := by
  obtain ⟨_, _, x, hx, ix, xheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
  obtain ⟨_, _, y, hy, jy, yheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
  have xi := (pair_mem_relationConverse E S birth x i).1 (representatives ix)
  have yj := (pair_mem_relationConverse E S birth y j).1 (representatives jy)
  exact descent x hx y hy i j c q d v xi.2.2 yj.2.2 earlier xheight yheight

theorem essentialHeightComposite_antitone {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt) :
    ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d v,
      ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
      ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
        d = c ∨ d ∈ c := by
  intro i _ j _ earlier c q d v first second
  exact (essentialHeightComposite_strict representatives descent earlier first second).elim
    Or.inr (fun h => Or.inl h.1)

theorem essentialHeightComposite_injection {L S T E C Q birth reps height qlt : ZFSet.{u}}
    (stages : S ⊆ T) (ordinal : ordinalSetProperty T)
    (representatives : ZFSet.IsFunc S E reps)
    (chosenBirths : reps ⊆ relationConverse E S birth)
    (points : E ⊆ L) (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent E birth height qlt) :
    InjectionCode S (ZFSet.prod C Q) (relationCompose S E (ZFSet.prod C Q) reps height) := by
  have function := relationCompose_function_of_subset representatives heights points
  refine ⟨function, ?_⟩
  intro i j z first second
  have iShape := ZFSet.pair_mem_prod.1 (function.1 first)
  have jShape := ZFSet.pair_mem_prod.1 (function.1 second)
  obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 iShape.2
  have notEarlier (a b : ZFSet.{u})
      (aHeight : ZFSet.pair a (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
      (bHeight : ZFSet.pair b (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height) : a ∉ b := by
    intro earlier
    rcases essentialHeightComposite_strict chosenBirths descent earlier aHeight bHeight with h | h
    · exact ZFSet.mem_irrefl c h
    · exact irreflexive q hq h.2
  have eqI := ordinalSetProperty_eq_code_rank i (ordinalSetProperty_member ordinal (stages iShape.1))
  have eqJ := ordinalSetProperty_eq_code_rank j (ordinalSetProperty_member ordinal (stages jShape.1))
  rcases lt_trichotomy (ZFSet.rank i) (ZFSet.rank j) with earlier | equal | later
  · have ij : i ∈ j := by rw [eqI, eqJ, mem_ordinalCode_iff]; exact earlier
    exact False.elim (notEarlier i j first second ij)
  · exact eqI.trans ((congrArg ordinalCode equal).trans eqJ.symm)
  · have ji : j ∈ i := by rw [eqJ, eqI, mem_ordinalCode_iff]; exact later
    exact False.elim (notEarlier j i second first ji)

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_essentialBirthHeights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    ∃ h ∈ M.sets,
      InjectionCode (essentialBirthIndices F T r birth) (ZFSet.prod C Q) h ∧
      (∀ i ∈ essentialBirthIndices F T r birth, ∀ j ∈ essentialBirthIndices F T r birth,
        i ∈ j → ∀ c q d v,
          ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d v) ∈ h →
            d = c ∨ d ∈ c) ∧
      ∀ i z, ZFSet.pair i z ∈ h → ∃ x ∈ birthEssentialSet F T r birth,
        ZFSet.pair x i ∈ birth ∧ ZFSet.pair x z ∈ height := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS := M.essentialBirthIndices_mem separation hF hT hr hBirth
  obtain ⟨reps, hReps, function, chosen, _⟩ :=
    M.exists_essentialBirthRepresentatives pairing unions powers separation choice hF hT hr hBirth
  let h := relationCompose S E (ZFSet.prod C Q) reps height
  have ground : h ∈ M.sets := M.relationCompose_mem pairing unions powers separation hS hE
    (M.prod_mem pairing unions powers separation hC hQ) hReps hHeight
  have subset : S ⊆ T := fun _ hi => (mem_essentialBirthIndices F T r birth _).1 hi |>.1
  have points : E ⊆ L := fun _ hx => positive (birthEssentialSet_subset F T r birth hx)
  refine ⟨h, ground, essentialHeightComposite_injection subset ordinal function chosen points heights
    irreflexive descent, essentialHeightComposite_antitone chosen descent, ?_⟩
  intro i z hiz
  obtain ⟨_, _, x, hx, ix, xz⟩ := (pair_mem_relationCompose S E (ZFSet.prod C Q) reps height i z).1 hiz
  exact ⟨x, hx, ((pair_mem_relationConverse E S birth x i).1 (chosen ix)).2.2, xz⟩

theorem essentialBirthIndices_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega := by
  obtain ⟨h, hh, injection, antitone, _⟩ := M.exists_essentialBirthHeights pairing unions powers
    separation choice hF hT hr hBirth hC hQ hHeight positive ordinal heights irreflexive descent
  exact M.groundCountable_descending_heights pairing unions powers separation infinite choice
    (M.essentialBirthIndices_mem separation hF hT hr hBirth) hC hQ hh
    (fun _ hi => ((mem_essentialBirthIndices F T r birth _).1 hi).1)
    ordinal injection smallQ antitone

end TransitiveGround

end



open SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageFromCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem birthEssential_below_earlier {L F T r μ birth x y a b : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (essential : x ∈ birthEssentialSet F T r birth) (positive : y ∈ F)
    (bornY : ZFSet.pair y a ∈ birth) (bornX : ZFSet.pair x b ∈ birth)
    (earlier : a ∈ b) : ZFSet.pair x y ∈ r ∧ x ≠ y := by
  classical
  have hx := (mem_birthEssentialSet F T r birth x).1 essential
  have xL := filter.subset hx.1
  have yL := filter.subset positive
  have bT := (ZFSet.pair_mem_prod.1 (born.1 bornX)).2
  have lower : ZFSet.pair x y ∈ r := by
    by_contra notLower
    obtain ⟨z, meetXY, _⟩ := meet.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨xL, yL⟩)
    have zL := (ZFSet.pair_mem_prod.1 (meet.operation.1 meetXY)).2
    obtain ⟨c, bornZ, _⟩ := born.2 z zL
    have cT := (ZFSet.pair_mem_prod.1 (born.1 bornZ)).2
    exact hx.2 z (filter.closed_meet x hx.1 y positive z meetXY) c cT b bT
      (meet.lower_left x y z meetXY) bornZ bornX
      (oldMeet x y z a b c bornY bornX earlier notLower meetXY bornZ)
  refine ⟨lower, ?_⟩
  intro equal
  subst y
  obtain ⟨t, _, unique⟩ := born.2 x xL
  have sameBirth : a = b := (unique a bornY).trans (unique b bornX).symm
  exact ZFSet.mem_irrefl b (sameBirth ▸ earlier)

theorem essentialHeightDescent_of_chronological_laws
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt) :
    EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt := by
  intro x hx y hy i j c q d v bornX bornY earlier heightX heightY
  have lower := birthEssential_below_earlier meet filter born oldMeet hy
    (birthEssentialSet_subset F T r birth hx) bornX bornY earlier
  exact strictHeight.strict y (filter.subset (birthEssentialSet_subset F T r birth hy))
    x (filter.subset (birthEssentialSet_subset F T r birth hx)) d v c q
    lower.1 lower.2 heightY heightX

end



section

universe u v

theorem mem_essentialBirthFiber (F T r birth t x : ZFSet.{u}) :
    x ∈ essentialBirthFiber F T r birth t ↔
      x ∈ birthEssentialSet F T r birth ∧ t ∈ T ∧ ZFSet.pair x t ∈ birth := by
  rw [essentialBirthFiber, mem_relationFiber, pair_mem_relationConverse]
  constructor
  · rintro ⟨hx, _, ht, born⟩
    exact ⟨hx, ((mem_essentialBirthIndices F T r birth t).1 ht).1, born⟩
  · rintro ⟨hx, ht, born⟩
    exact ⟨hx, hx, (mem_essentialBirthIndices F T r birth t).2 ⟨ht, x, hx, born⟩, born⟩

theorem essentialBirthFiber_subset (F T r birth t : ZFSet.{u}) :
    essentialBirthFiber F T r birth t ⊆ birthEssentialSet F T r birth :=
  fun _ hx => ((mem_essentialBirthFiber F T r birth t _).1 hx).1

theorem birthEssentials_no_oldBridge {L F T r μ birth t x y : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (hx : x ∈ birthEssentialSet F T r birth) (hy : y ∈ birthEssentialSet F T r birth)
    (xt : ZFSet.pair x t ∈ birth) (yt : ZFSet.pair y t ∈ birth) :
    ¬ OldBridgeCode L r μ birth t x y := by
  have xE := (mem_birthEssentialSet F T r birth x).1 hx
  have yE := (mem_birthEssentialSet F T r birth y).1 hy
  have ht := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
  intro bridge
  rcases bridge with ⟨z, a, meetXY, za, old⟩ | ⟨z, hz, a, za, old, intermediate⟩
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    exact xE.2 z (filter.closed_meet x xE.1 y yE.1 z meetXY) a ha t ht
      (meet.lower_left x y z meetXY) za xt old
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    rcases intermediate with ⟨xz, zy⟩ | ⟨yz, zx⟩
    · exact yE.2 z (filter.upward x xE.1 z hz xz) a ha t ht zy za yt old
    · exact xE.2 z (filter.upward y yE.1 z hz yz) a ha t ht zx za xt old

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem essentialBirthFiber_mem (separation : SeparationSchema M.sets)
    {F T r birth t : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) (ht : t ∈ M.sets) :
    essentialBirthFiber F T r birth t ∈ M.sets := by
  let E := birthEssentialSet F T r birth
  let params := extend t (extend T (extend birth Fin.elim0))
  let φ : BoundedFormula 4 := .conj (.mem 1 2) (BoundedFormula.pairMembershipFormula 0 1 3)
  have selected := M.bounded_separation_mem separation φ params
    (Fin.cases ht (Fin.cases hT (Fin.cases hBirth (fun j => Fin.elim0 j))))
    (M.birthEssentialSet_mem separation hF hT hr hBirth)
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth φ (extend x params)) E =
      essentialBirthFiber F T r birth t := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_essentialBirthFiber]
    exact and_congr Iff.rfl
      (and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 0 1 3 _))
  exact eq ▸ selected

end TransitiveGround

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFilterCopies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem meetFilter_copyPullback {A L rA rL μA μL e F : ZFSet.{u}}
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (nonempty : (copyPullback A L e F).Nonempty) :
    MeetFilterCode A rA μA (copyPullback A L e F) where
  subset := fun x hx => ((mem_copyPullback A L e F x).1 hx).1
  nonempty := nonempty
  upward := by
    intro x hx y hy lower
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨y', yy', _⟩ := embedding.injection.function.2 y hy
    have hyL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 yy')).2
    have hyF := target.upward x' hxF y' hyL (embedding.monotone x y x' y' lower xx' yy')
    exact (mem_copyPullback A L e F y).2 ⟨hy, y', hyF, hyL, yy'⟩
  closed_meet := by
    intro x hx y hy z meetXY
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨_, y', hyF, _, yy'⟩ := (mem_copyPullback A L e F y).1 hy
    have hzA := (ZFSet.pair_mem_prod.1 (source.operation.1 meetXY)).2
    obtain ⟨z', zz', _⟩ := embedding.injection.function.2 z hzA
    have hzL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 zz')).2
    have hzF := target.closed_meet x' hxF y' hyF z'
      (embedding.map_meet x y z x' y' z' meetXY xx' yy' zz')
    exact (mem_copyPullback A L e F z).2 ⟨hzA, z', hzF, hzL, zz'⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem internalCountableBelow_copy_of_all_filters
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L rA rL μA μL e F : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (he : e ∈ M.sets) (hF : F ∈ M.sets)
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (earlier : ∀ P ∈ M.sets, MeetFilterCode A rA μA P → M.InternalCountableBelow rA P P) :
    M.InternalCountableBelow rL F (F ∩ relationImage A L e) := by
  classical
  by_cases nonempty : (copyPullback A L e F).Nonempty
  · have pullbackMember := M.copyPullback_mem pairing unions powers separation hA hL he hF
    have pullbackFilter := meetFilter_copyPullback source target embedding nonempty
    exact M.internalCountableBelow_copy_pullback pairing unions powers separation infinite hL he
      embedding.injection embedding.monotone
      (earlier (copyPullback A L e F) pullbackMember pullbackFilter)
  · refine ⟨∅, M.empty_mem ⟨F, hF⟩, M.empty_groundEmbeddable ZFSet.omega ⟨F, hF⟩,
      ZFSet.empty_subset F, ?_⟩
    intro x hx
    obtain ⟨hxF, image⟩ := ZFSet.mem_inter.1 hx
    obtain ⟨hxL, y, hyA, yx⟩ := (mem_relationImage A L e x).1 image
    exact False.elim (nonempty ⟨y,
      (mem_copyPullback A L e F y).2 ⟨hyA, x, hxF, hxL, yx⟩⟩)

end TransitiveGround

end PartitionPilot.Forcing

end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedProfileImageTests
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace MeetEmbeddingCode
variable {P Q r R μ ν e F x x' : ZFSet.{u}}
variable (embedding : MeetEmbeddingCode P Q r R μ ν e)
variable (source : MeetOrderCode P r μ) (target : MeetOrderCode Q R ν)

include embedding source target in
theorem profilePositive_image_iff (subset : F ⊆ P) (image : ZFSet.pair x x' ∈ e) :
    (∃ f' ∈ relationImage F Q e, ZFSet.pair f' x' ∈ R) ↔
      ∃ f ∈ F, ZFSet.pair f x ∈ r := by
  constructor
  · rintro ⟨f', member, lower⟩
    obtain ⟨_, f, hf, entry⟩ := (mem_relationImage F Q e f').1 member
    exact ⟨f, hf, (embedding.order_iff source target entry image).1 lower⟩
  · rintro ⟨f, hf, lower⟩
    obtain ⟨f', entry, _⟩ := embedding.injection.function.2 f (subset hf)
    exact ⟨f', (mem_relationImage F Q e f').2
      ⟨(ZFSet.pair_mem_prod.1 (embedding.injection.function.1 entry)).2, f, hf, entry⟩,
      embedding.monotone f x f' x' lower entry image⟩

end MeetEmbeddingCode

namespace CodedInsertionProfile
variable {P Q r R μ ν e F c E K c' E' K' x x' : ZFSet.{u}}

theorem at_embedding (profile : CodedInsertionProfile P r μ c E K F)
    (embedding : MeetEmbeddingCode P Q r R μ ν e)
    (source : MeetOrderCode P r μ) (target : MeetOrderCode Q R ν) (subset : F ⊆ P)
    (imageC : ZFSet.pair c c' ∈ e) (imageE : ZFSet.pair E E' ∈ e)
    (imageK : ZFSet.pair K K' ∈ e) (imageX : ZFSet.pair x x' ∈ e)
    (above : ZFSet.pair E' x' ∈ R) :
    ((∃ f' ∈ relationImage F Q e, ZFSet.pair f' x' ∈ R) → ZFSet.pair K' x' ∈ R) ∧
    (¬ (∃ f' ∈ relationImage F Q e, ZFSet.pair f' x' ∈ R) →
      ZFSet.pair (ZFSet.pair K' x') c' ∈ ν) := by
  have hx := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 imageX)).1
  have old := profile x hx ((embedding.order_iff source target imageE imageX).1 above)
  have positive := embedding.profilePositive_image_iff source target subset imageX
  exact ⟨fun hp => embedding.monotone K x K' x' (old.1 (positive.1 hp)) imageK imageX,
    fun hn => embedding.map_meet K x c K' x' c'
      (old.2 (fun hp => hn (positive.2 hp))) imageK imageX imageC⟩

end CodedInsertionProfile
end PartitionPilot.Forcing

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

universe u

theorem literalTaskCode_mem_eligibleTaskSet (P G r μ A R U Labels a c base e F label : ZFSet.{u}) :
    literalTaskCode a c base e F label ∈ eligibleTaskSet P G r μ A R U Labels ↔
      a ∈ P ∧ c ∈ P ∧ base ∈ R ∧ e ∈ P ∧ F ∈ U ∧ label ∈ Labels ∧
        EligibleTaskCode P G r μ A a c base e F := by
  rw [mem_eligibleTaskSet]
  constructor
  · rintro ⟨a', ha, c', hc, base', hBase, e', he, F', hF, label', hLabel, equal, code⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := literalTaskCode_inj.1 equal
    exact ⟨ha, hc, hBase, he, hF, hLabel, code⟩
  · rintro ⟨ha, hc, hBase, he, hF, hLabel, code⟩
    exact ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩

theorem TaskRepresentative.restriction {P r A R U Labels g a c base e F label : ZFSet.{u}}
    (represented : TaskRepresentative P r A R U Labels (literalTaskCode a c base e F label) g) :
    RestrictedActionCode P r A g a c base := by
  obtain ⟨a', _, c', _, base', _, e', _, F', _, label', _, equal, code⟩ := represented
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := literalTaskCode_inj.1 equal
  exact code

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GrowthLayerSourceCongruence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

namespace CodedGrowthLayer

open SetFormula

theorem internal_countable_essentials
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L F T r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hL : L ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (ht : t ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (earlier : ∀ s ∈ t, Space s ∈ M.sets ∧
      MeetOrderCode (Space s) (sourceOrder s) (sourceMeet s) ∧
      ∀ P ∈ M.sets, MeetFilterCode (Space s) (sourceOrder s) (sourceMeet s) P →
        M.InternalCountableBelow (sourceOrder s) P P) :
    M.InternalCountableBelow r F (essentialBirthFiber F T r birth t) := by
  classical
  have groundFiber := M.essentialBirthFiber_mem separation hF hT hr hBirth ht
  have positive : essentialBirthFiber F T r birth t ⊆ F :=
    fun _ hx => birthEssentialSet_subset F T r birth
      (essentialBirthFiber_subset F T r birth t hx)
  have points : essentialBirthFiber F T r birth t ⊆ L := fun _ hx => filter.subset (positive hx)
  cases layer with
  | countablePoints D _ small cover =>
    have subset : essentialBirthFiber F T r birth t ⊆ D := by
      intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    have countableFiber := M.groundEmbeddable_restrict separation groundFiber
      (M.omega_mem separation infinite) subset small
    exact M.internalCountableBelow_of_countable groundFiber countableFiber positive
      (fun x hx => meet.order.refl x (points hx))
  | copies I parts groundI small groundParts index e previous groundCopy embedding cover inCopy =>
    apply M.internalCountableBelow_indexed_union pairing unions powers separation infinite choice
      groundI hr hF groundFiber groundParts small
    · intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    · intro i hi
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i hi)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i hi) hF source filter (embedding i hi) sourceBases
      apply basis.mono
      intro x hx
      obtain ⟨hxFiber, part⟩ := (mem_relationFiber (essentialBirthFiber F T r birth t) parts i x).1 hx
      exact ZFSet.mem_inter.2 ⟨positive hxFiber, inCopy i hi x (points hxFiber) part⟩
  | separated I index e previous groundCopy embedding component cover separated =>
    by_cases inhabited : (essentialBirthFiber F T r birth t).Nonempty
    · obtain ⟨x, hx⟩ := inhabited
      let representative : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨x, points hx, ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2⟩
      let i := component representative
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i) hF source filter (embedding i) sourceBases
      apply basis.mono
      intro y hy
      let current : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨y, points hy, ((mem_essentialBirthFiber F T r birth t y).1 hy).2.2⟩
      have same : component current = i := by
        by_contra different
        exact birthEssentials_no_oldBridge meet filter born
          (essentialBirthFiber_subset F T r birth t hy)
          (essentialBirthFiber_subset F T r birth t hx)
          current.property.2 representative.property.2 (separated current representative different)
      have inside := cover current
      rw [same] at inside
      exact ZFSet.mem_inter.2 ⟨positive hy, inside⟩
    · have empty : essentialBirthFiber F T r birth t = ∅ := by
        apply ZFSet.ext
        intro x
        exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
          fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
      rw [empty]
      exact M.internalCountableBelow_empty ⟨F, hF⟩ r F

end CodedGrowthLayer

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_NonzeroLimitOrdinalCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem not_nonzeroLimitOrdinalCode_successor (b : ZFSet.{u}) :
    ¬ NonzeroLimitOrdinalCode (insert b b) := by
  intro limit
  obtain ⟨c, member, later⟩ := limit.2 b (ZFSet.mem_insert b b)
  rcases ZFSet.mem_insert_iff.1 member with equal | earlier
  · subst c
    exact (lt_irrefl (ZFSet.rank b)) (ZFSet.rank_lt_of_mem later)
  · exact (lt_irrefl (ZFSet.rank b))
      ((ZFSet.rank_lt_of_mem later).trans (ZFSet.rank_lt_of_mem earlier))

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundOmegaOneRowModel
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)

theorem groundOmegaOne_successor {A : ZFSet.{u}}
    (hA : A ∈ M.groundOmegaOne pairing unions powers separation collection infinite) :
    insert A A ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨hAM, ordinal, small⟩ := (spec.2.2.1 A).1 hA
  exact (spec.2.2.1 _).2 ⟨M.insert_mem pairing unions hAM hAM,
    ordinalSetProperty_succ ordinal,
    M.groundEmbeddable_insert pairing unions powers separation infinite hAM hAM small⟩

theorem groundOmegaOne_countable_bound
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets)
    (subset : R ⊆ M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.groundEmbeddable R ZFSet.omega) :
    ∃ B ∈ M.groundOmegaOne pairing unions powers separation collection infinite,
      ∀ A ∈ R, A ∈ B := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have ordinals : ∀ A ∈ R, ordinalSetProperty A := fun A hA => ((spec.2.2.1 A).1 (subset hA)).2.1
  have membersSmall : ∀ A ∈ R, M.groundEmbeddable A ZFSet.omega :=
    fun A hA => ((spec.2.2.1 A).1 (subset hA)).2.2
  have hU := M.union_mem unions hR
  have ordU := ordinalSetProperty_sUnion ordinals
  have smallU := M.groundCountable_family_union pairing unions powers separation infinite choice
    hR small membersSmall
  have uC := (spec.2.2.1 (⋃₀ R)).2 ⟨hU, ordU, smallU⟩
  refine ⟨insert (⋃₀ R) (⋃₀ R),
    M.groundOmegaOne_successor pairing unions powers separation collection infinite uC, ?_⟩
  intro A hA
  have included : A ⊆ ⋃₀ R := fun x hx => ZFSet.mem_sUnion.2 ⟨A, hA, hx⟩
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff A).1 (ordinals A hA)
  obtain ⟨b, eqB⟩ := (ordinalSetProperty_iff (⋃₀ R)).1 ordU
  rw [eqA, eqB] at included ⊢
  rw [← ordinalCode_succ, mem_ordinalCode_iff]
  exact Order.lt_succ_iff.2 ((ordinalCode_subset_iff a b).1 included)

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundOrdinalPartitionInjectionAssembly
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pair_mem_definableRelation {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A B x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.definableRelation φ params A B ↔
      x ∈ A ∧ y ∈ B ∧ Realize M.sets φ (extend x (extend y params)) := by
  rw [definableRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, equal, relation⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, relation⟩
  · rintro ⟨hx, hy, relation⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, relation⟩

theorem realize_definableRelationEntryFormula {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets (definableRelationEntryFormula φ) (extend z (extend A (extend B params))) ↔
      ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair x y ∧ Realize M.sets φ (extend x (extend y params)) := by
  simp only [definableRelationEntryFormula, realize_ex, Realize]
  constructor
  · rintro ⟨x, hx, inA, y, hy, inB, pair, relation⟩
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hy (Fin.cases hx (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    have exactPair := (BoundedFormula.truth_orderedPairFormula 2 1 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ ground).1 pair)
    exact ⟨x, inA, y, inB, exactPair, (realize_binaryApplication M.sets φ _ _ _ _).1 relation⟩
  · rintro ⟨x, hx, y, hy, pair, relation⟩
    have hxM := M.transitive hA hx
    have hyM := M.transitive hB hy
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases hxM (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    exact ⟨x, hxM, hx, y, hyM, hy,
      (BoundedFormula.realize_toFormula M _ _ ground).2
        ((BoundedFormula.truth_orderedPairFormula 2 1 0 _).2 pair),
      (realize_binaryApplication M.sets φ _ _ _ _).2 relation⟩

theorem definableRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    M.definableRelation φ params A B ∈ M.sets := by
  have hProd := M.prod_mem pairing unions powers separation hA hB
  have selected := M.separation_mem separation (definableRelationEntryFormula φ)
    (extend A (extend B params)) (Fin.cases hA (Fin.cases hB members)) hProd
  have equal : ZFSet.sep (fun z => Realize M.sets (definableRelationEntryFormula φ)
      (extend z (extend A (extend B params)))) (ZFSet.prod A B) = M.definableRelation φ params A B := by
    apply ZFSet.ext
    intro z
    rw [definableRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_definableRelationEntryFormula φ params members hA hB z (M.transitive hProd hz)
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



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

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_groundMeetFilters (P r μ F : ZFSet.{u}) :
    F ∈ M.groundMeetFilters P r μ ↔ F ∈ M.sets ∧ MeetFilterCode P r μ F := by
  rw [groundMeetFilters, ZFSet.mem_sep, M.mem_groundPower]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.subset⟩, h.2⟩⟩

end TransitiveGround

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundEligibleCaps
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

theorem literalTaskCode_mem_groundEligibleTasks
    (P G r μ A Labels a c base e F label : ZFSet.{u}) :
    literalTaskCode a c base e F label ∈ M.groundEligibleTasks P G r μ A Labels ↔
      label ∈ Labels ∧ base ∈ M.sets ∧ F ∈ M.sets ∧ EligibleTaskCode P G r μ A a c base e F := by
  rw [groundEligibleTasks, literalTaskCode_mem_eligibleTaskSet,
    M.mem_groundRelations, M.mem_groundMeetFilters]
  constructor
  · rintro ⟨_, _, ⟨hBase, _⟩, _, ⟨hF, _⟩, hLabel, code⟩
    exact ⟨hLabel, hBase, hF, code⟩
  · rintro ⟨hLabel, hBase, hF, code⟩
    obtain ⟨g, _, represented⟩ := code.representative
    exact ⟨code.source_mem, code.target_mem, ⟨hBase, represented.shape⟩,
      code.separator_mem, ⟨hF, code.filter⟩, hLabel, code⟩






end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.PosetActionCode
universe u
variable {G P m one r A g v : ZFSet.{u}}

theorem agreement_identity_iff_fixes (action : PosetActionCode G P m one r A) :
    ActionAgreementBelow P r A g one v ↔
      ∀ x ∈ P, ZFSet.pair x v ∈ r → ZFSet.pair (ZFSet.pair g x) x ∈ A := by
  constructor
  · intro agree x hx lower
    exact (agree x hx x hx lower).2 (action.one x hx)
  · intro fixes x hx y _ lower
    have fixed := fixes x hx lower
    have identity := action.one x hx
    have function : FunctionGraphOn (ZFSet.prod G P) A := ⟨P, action.function⟩
    exact ⟨fun entry => (function.unique entry fixed).symm ▸ identity,
      fun entry => (function.unique entry identity).symm ▸ fixed⟩

end PartitionPilot.Forcing.PosetActionCode



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RectangleFulfillmentAtBound
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

theorem truth_actionAgreementBelowFormula {n} (P r A g h w : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionAgreementBelowFormula P r A g h w) env ↔
      ActionAgreementBelow (env P) (env r) (env A) (env g) (env h) (env w) := by
  simp only [actionAgreementBelowFormula, ActionAgreementBelow, Truth, truth_imp, iff_def,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor <;> exact fun h => h

end BoundedFormula





namespace BoundedFormula

theorem truth_compressionActorFormula {n}
    (P G Q H R B e a Sources Reps top Caps i k : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (compressionActorFormula P G Q H R B e a Sources Reps top Caps i k) env ↔
      CompressionActorCode (env P) (env G) (env Q) (env H) (env R) (env B)
        (env e) (env a) (env Sources) (env Reps) (env top) (env Caps) (env i) (env k) := by
  simp only [compressionActorFormula, CompressionActorCode, Truth, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula,
    truth_actionAgreementBelowFormula, iff_def]
  constructor <;> exact fun h => h

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem choose_compressionActorFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I P G Q H R B e a Sources Reps top Caps : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hQ : Q ∈ M.sets)
    (hH : H ∈ M.sets) (hR : R ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets)
    (ha : a ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hTop : top ∈ M.sets) (hCaps : Caps ∈ M.sets)
    (total : CompressionActorFulfillmentCode I P G Q H R B e a Sources Reps top Caps) :
    ∃ f ∈ M.sets, ZFSet.IsFunc I H f ∧
      ∀ i k, ZFSet.pair i k ∈ f → CompressionActorCode P G Q H R B e a Sources Reps top Caps i k := by
  let params : Fin 12 → ZFSet.{u} := extend P (extend G (extend Q (extend H (extend R (extend B
    (extend e (extend a (extend Sources (extend Reps (extend top (extend Caps Fin.elim0)))))))))))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hP (Fin.cases hG (Fin.cases hQ (Fin.cases hH
    (Fin.cases hR (Fin.cases hB (Fin.cases he (Fin.cases ha (Fin.cases hSources
      (Fin.cases hReps (Fin.cases hTop (Fin.cases hCaps (fun j => Fin.elim0 j))))))))))))
  let φ : SetFormula 14 := (BoundedFormula.compressionActorFormula 2 3 4 5 6 7 8 9 10 11 12 13 0 1).toFormula
  let relation := M.definableRelation φ params I H
  have ground : relation ∈ M.sets := M.definableRelation_mem pairing unions powers separation φ params members hI hH
  have exactCode (i k : ZFSet.{u}) (hi : i ∈ I) (hk : k ∈ H) :
      Realize M.sets φ (extend i (extend k params)) ↔
        CompressionActorCode P G Q H R B e a Sources Reps top Caps i k :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases (M.transitive hI hi) (Fin.cases (M.transitive hH hk) members))).trans
      (BoundedFormula.truth_compressionActorFormula 2 3 4 5 6 7 8 9 10 11 12 13 0 1 _)
  obtain ⟨f, hf, function, included⟩ := M.uniformize_relation pairing unions powers separation choice hI hH ground (by
    intro i hi
    obtain ⟨k, hk, code⟩ := total i hi
    exact ⟨k, hk, (M.pair_mem_definableRelation φ params I H i k).2 ⟨hi, hk, (exactCode i k hi hk).2 code⟩⟩)
  refine ⟨f, hf, function, ?_⟩
  intro i k entry
  obtain ⟨hi, hk, realized⟩ := (M.pair_mem_definableRelation φ params I H i k).1 (included entry)
  exact (exactCode i k hi hk).1 realized

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality
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

theorem internal_chronological_coinitiality
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (ordinal : ordinalSetProperty T)
    (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets,
      InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
        ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ r := by
  have descent := essentialHeightDescent_of_chronological_laws meet filter born oldMeet strictHeight
  have small := M.essentialBirthIndices_countable pairing unions powers separation infinite choice
    hF hT hr hBirth hC hQ hHeight filter.subset ordinal strictHeight.function smallQ irreflexive descent
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    M.internal_countable_basis_of_birth_layers pairing unions powers separation infinite choice
      hF hT hr hBirth meet.order filter.subset born small localBases
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalHistory

variable {M : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

theorem all_filters_internal_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt) :
    ∀ cutoff ∈ T, ∀ F ∈ M.sets,
      MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F →
        M.InternalCountableBelow (history.order cutoff) F F := by
  intro cutoff
  induction cutoff using ZFSet.inductionOn with
  | h cutoff ih =>
    intro hc F hF filter
    have localBases : ∀ t ∈ essentialBirthIndices F T (history.order cutoff) (history.birth cutoff),
        M.InternalCountableBelow (history.order cutoff) F
          (essentialBirthFiber F T (history.order cutoff) (history.birth cutoff) t) := by
      intro t ht
      obtain ⟨htT, x, hx, xt⟩ :=
        (mem_essentialBirthIndices F T (history.order cutoff) (history.birth cutoff) t).1 ht
      have bounded := history.birth_bound cutoff hc x
        (filter.subset (birthEssentialSet_subset F T (history.order cutoff) (history.birth cutoff) hx)) t xt
      apply (history.layer cutoff hc t htT bounded).internal_countable_essentials
        pairing unions powers separation infinite choice (history.space_mem cutoff hc)
        (history.order_mem cutoff hc) (history.birth_mem cutoff hc) hF hT (M.transitive hT htT)
        (history.meet_order cutoff hc) filter (history.birth_function cutoff hc)
      intro s hs
      have hsT : s ∈ T := ordinal.1 t htT s hs
      have before : s ∈ cutoff := bounded.elim
        (fun equal => equal ▸ hs) (fun earlier => ordinal.2 cutoff hc t earlier s hs)
      exact ⟨history.space_mem s hsT, history.meet_order s hsT, ih s before hsT⟩
    obtain ⟨B, hB, f, hf, injection, positive, below⟩ :=
      M.internal_chronological_coinitiality pairing unions powers separation infinite choice
        hF hT (history.order_mem cutoff hc) (history.birth_mem cutoff hc)
        hC hQ (history.height_mem cutoff hc) (history.meet_order cutoff hc) filter
        (history.birth_function cutoff hc) ordinal (history.old_meet cutoff hc)
        (history.strict_height cutoff hc) smallQ irreflexive localBases
    exact ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩

theorem exists_internal_basis
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ M.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff := by
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    history.all_filters_internal_countable pairing unions powers separation infinite choice
      hT hC hQ ordinal smallQ irreflexive cutoff hc F hF filter
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end GroundChronologicalHistory





end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologicalHistory

open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

theorem exists_extension_basis
    (includes : M.sets ⊆ N.sets)
    (pairing : Realize N.sets SetFormula.pairing Fin.elim0)
    (unions : Realize N.sets SetFormula.union Fin.elim0)
    (powers : Realize N.sets powerSet Fin.elim0) (separation : SeparationSchema N.sets)
    (infinite : Realize N.sets SetFormula.infinity Fin.elim0)
    (choice : Realize N.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ N.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff :=
  (history.of_inclusion includes).exists_internal_basis pairing unions powers separation infinite
    choice (includes hT) (includes hC) (includes hQ) ordinal
    (M.groundEmbeddable_of_inclusion N includes smallQ) irreflexive hc hF filter

end PartitionPilot.Forcing.GroundChronologicalHistory



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyFieldAppend
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (newValues : Fin 5 → ZFSet.{u}) (ground : ∀ j, newValues j ∈ M.sets)

theorem appendTime_value_at (j : Fin 5) :
    (fields.appendTime pairing unions newValues ground).value j T = newValues j := by
  apply GroundChronologyFields.value_eq_of_entry
  exact ZFSet.mem_insert _ _

end PartitionPilot.Forcing.GroundChronologyFields

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundChronologicalTransitionTransport
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologicalMainTransition
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target first second : GroundChronologicalMainStage M C D rD}

theorem retargetEq_points
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).map.points = transition.map.points := by
  cases sourceEqual
  cases targetEqual
  rfl

theorem retargetEq_code
    (transition : GroundChronologicalMainTransition source target)
    (sourceEqual : source = first) (targetEqual : target = second) :
    (transition.retargetEq sourceEqual targetEqual).map.code = transition.map.code := by
  cases sourceEqual
  cases targetEqual
  rfl

end PartitionPilot.Forcing.GroundChronologicalMainTransition

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFilterPullbackRecovery
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem pushFilter_copyPullback_eq_of_coinitial {A L rL μL e F : ZFSet.{u}}
    (function : ZFSet.IsFunc A L e) (filter : MeetFilterCode L rL μL F)
    (coinitial : ∀ x ∈ F, ∃ b ∈ F, ∃ a ∈ A,
      ZFSet.pair a b ∈ e ∧ ZFSet.pair b x ∈ rL) :
    pushFilterCode L rL e (copyPullback A L e F) = F := by
  apply ZFSet.ext
  intro x
  rw [mem_pushFilterCode]
  constructor
  · rintro ⟨hx, a, ha, b, _, image, lower⟩
    obtain ⟨haA, c, hc, _, original⟩ := (mem_copyPullback A L e F a).1 ha
    obtain ⟨_, _, unique⟩ := function.2 a haA
    have equal : b = c := (unique b image).trans (unique c original).symm
    exact filter.upward b (equal.symm ▸ hc) x hx lower
  · intro hx
    obtain ⟨b, hb, a, ha, image, lower⟩ := coinitial x hx
    exact ⟨filter.subset hx, a,
      (mem_copyPullback A L e F a).2 ⟨ha, b, hb, filter.subset hb, image⟩,
      b, filter.subset hb, image, lower⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CodedMainPrefixSystems
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem stageGraph_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.stageGraph ↔ z = (run.linked i).code :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

end GroundMainPrefix

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

theorem MainPrefixExtends.refl (T S E : ZFSet.{u}) :
    MainPrefixExtends (mainPrefixCode T S E) (mainPrefixCode T S E) :=
  mainPrefixExtends_iff.2 ⟨fun _ h => h, fun _ h => h, fun _ h => h⟩

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainPrefixInsertionFamilyTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem finalInsertionCaps_ground (j : I) {caps : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hCaps : caps ∈ M.sets) :
    run.finalInsertionCaps j caps ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hLabels
    (run.diagram.stage j).stage.carrier_ground run.limitPoints_ground hCaps (run.limitPointMap_ground j)

theorem finalInsertionActors_ground (j : I) {actors : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hActors : actors ∈ M.sets) :
    run.finalInsertionActors j actors ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hLabels
    (run.diagram.stage j).stage.actors_ground run.limitActors_ground hActors (run.limitActorMap_ground j)

theorem finalInsertionCaps_injection (j : I) {caps : ZFSet.{u}}
    (injection : InjectionCode Labels (run.diagram.stage j).stage.carrier caps) :
    InjectionCode Labels run.limitPoints (run.finalInsertionCaps j caps) :=
  injection.compose (run.limitPointMap_injection j)

theorem finalInsertionActors_injection (j : I) {actors : ZFSet.{u}}
    (injection : InjectionCode Labels (run.diagram.stage j).stage.actors actors) :
    InjectionCode Labels run.limitActors (run.finalInsertionActors j actors) :=
  injection.compose (run.limitActorMap_injection j)

theorem finalInsertionCaps_entry (j : I) {caps label cap' : ZFSet.{u}}
    (injection : InjectionCode Labels (run.diagram.stage j).stage.carrier caps) :
    ZFSet.pair label cap' ∈ run.finalInsertionCaps j caps ↔
      ∃ cap, ZFSet.pair label cap ∈ caps ∧ ZFSet.pair cap cap' ∈ run.limitPointMap j := by
  constructor
  · intro entry
    obtain ⟨_, _, cap, _, old, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact ⟨cap, old, image⟩
  · rintro ⟨cap, old, image⟩
    have oldBounds := ZFSet.pair_mem_prod.1 (injection.function.1 old)
    have imageBounds := ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 image)
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨oldBounds.1, imageBounds.2, cap, oldBounds.2, old, image⟩

theorem finalInsertionActors_entry (j : I) {actors label actor' : ZFSet.{u}}
    (injection : InjectionCode Labels (run.diagram.stage j).stage.actors actors) :
    ZFSet.pair label actor' ∈ run.finalInsertionActors j actors ↔
      ∃ actor, ZFSet.pair label actor ∈ actors ∧ ZFSet.pair actor actor' ∈ run.limitActorMap j := by
  constructor
  · intro entry
    obtain ⟨_, _, actor, _, old, image⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact ⟨actor, old, image⟩
  · rintro ⟨actor, old, image⟩
    have oldBounds := ZFSet.pair_mem_prod.1 (injection.function.1 old)
    have imageBounds := ZFSet.pair_mem_prod.1 ((run.limitActorMap_injection j).function.1 image)
    exact (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨oldBounds.1, imageBounds.2, actor, oldBounds.2, old, image⟩

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitChronologyCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitChronologyFields_terminal (j : Fin 5) :
    run.limitChronologyFields.value j run.cutoffLimit = run.limitTerminalFields j :=
  run.limitPriorFields.appendTime_value_at pairing unions run.limitTerminalFields run.limitTerminalFields_ground j

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_OldProfilePreservationComposition
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

theorem relationImage_composition_on {P Q V F e f : ZFSet.{u}} (subset : F ⊆ P) :
    relationImage (relationImage F Q e) V f = relationImage F V (relationCompose P Q V e f) := by
  apply ZFSet.ext
  intro z
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hz, y, hy, yz⟩
    obtain ⟨hy, x, hx, xy⟩ := (mem_relationImage F Q e y).1 hy
    exact ⟨hz, x, hx, (pair_mem_relationCompose P Q V e f x z).2
      ⟨subset hx, hz, y, hy, xy, yz⟩⟩
  · rintro ⟨hz, x, hx, entry⟩
    obtain ⟨_, _, y, hy, xy, yz⟩ := (pair_mem_relationCompose P Q V e f x z).1 entry
    exact ⟨hz, y, (mem_relationImage F Q e y).2 ⟨hy, x, hx, xy⟩, yz⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIdentityInsertionTasks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem pair_mem_identityIdealGraph (P r C x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ identityIdealGraph P r C ↔
      x = y ∧ x ∈ P ∧ ZFSet.pair x C ∈ r := by
  rw [identityIdealGraph, pair_mem_identityFunctionGraph, mem_attachmentIdeal]

theorem identityIdealGraph_restrictedAction {P G r A m one C : ZFSet.{u}}
    (action : PosetActionCode G P m one r A) (hC : C ∈ P) :
    RestrictedActionCode P r A one C C (identityIdealGraph P r C) where
  shape := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph (attachmentIdeal P r C) z).1 hz
    have member := ((mem_attachmentIdeal P r C x).1 hx).1
    exact ZFSet.pair_mem_prod.2 ⟨member, member⟩
  target_entry := action.one C hC
  entries x hx y hy := by
    rw [pair_mem_identityIdealGraph]
    constructor
    · rintro ⟨rfl, _, lower⟩
      exact ⟨lower, action.one x hx⟩
    · rintro ⟨lower, entry⟩
      have equal := (show FunctionGraphOn (ZFSet.prod G P) A from ⟨P, action.function⟩).unique
        entry (action.one x hx)
      exact ⟨equal.symm, hx, lower⟩

theorem identityInsertion_eligible {P G r μ A m one C E F : ZFSet.{u}}
    (action : PosetActionCode G P m one r A) (hOne : one ∈ G)
    (hC : C ∈ P) (hE : E ∈ P) (filter : MeetFilterCode P r μ F)
    (lower : ZFSet.pair C E ∈ r) (strict : ZFSet.pair E C ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair E x ∈ r) :
    EligibleTaskCode P G r μ A C C (identityIdealGraph P r C) E F :=
  ⟨hC, hC, hE, filter, lower, strict, above,
    one, hOne, identityIdealGraph_restrictedAction action hC⟩

theorem identityInsertionTask_injective (P r C E F : ZFSet.{u}) :
    Function.Injective (identityInsertionTask P r C E F) := by
  intro first second equal
  exact (literalTaskCode_inj.1 equal).2.2.2.2.2

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_identityInsertionTaskGraph (Labels I P r C E F label task : ZFSet.{u}) :
    ZFSet.pair label task ∈ identityInsertionTaskGraph Labels I P r C E F ↔
      label ∈ Labels ∧ task ∈ I ∧ task = identityInsertionTask P r C E F label := by
  rw [identityInsertionTaskGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, equal, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, code⟩
  · rintro ⟨ha, hb, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, label, ha, task, hb, rfl, code⟩

namespace BoundedFormula

theorem truth_identityInsertionGraphEntryFormula {n} (z Labels I C base E F : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (identityInsertionGraphEntryFormula z Labels I C base E F) env ↔
      ∃ label ∈ env Labels, ∃ task ∈ env I, env z = ZFSet.pair label task ∧
        task = literalTaskCode (env C) (env C) (env base) (env E) (env F) label := by
  simp only [identityInsertionGraphEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_literalTaskFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem identityIdealGraph_mem {P r C : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hC : C ∈ P) : identityIdealGraph P r C ∈ M.sets :=
  M.identityFunctionGraph_mem pairing unions powers separation
    (M.attachmentIdeal_mem separation hP hr (M.transitive hP hC))

theorem identityInsertionTask_mem {P G r μ A m one Labels C E F label : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hF : F ∈ M.sets)
    (action : PosetActionCode G P m one r A) (hOne : one ∈ G)
    (hC : C ∈ P) (hE : E ∈ P) (filter : MeetFilterCode P r μ F)
    (lower : ZFSet.pair C E ∈ r) (strict : ZFSet.pair E C ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair E x ∈ r) (hlabel : label ∈ Labels) :
    identityInsertionTask P r C E F label ∈ M.groundEligibleTasks P G r μ A Labels :=
  (M.literalTaskCode_mem_groundEligibleTasks P G r μ A Labels C C (identityIdealGraph P r C)
    E F label).2 ⟨hlabel, M.identityIdealGraph_mem pairing unions powers separation hP hr hC,
      hF, identityInsertion_eligible action hOne hC hE filter lower strict above⟩

theorem identityInsertionTaskGraph_mem {Labels I P r C E F : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hC : C ∈ P) (hE : E ∈ P) (hF : F ∈ M.sets) :
    identityInsertionTaskGraph Labels I P r C E F ∈ M.sets := by
  let params := extend Labels (extend I (extend C (extend (identityIdealGraph P r C)
    (extend E (extend F Fin.elim0)))))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hLabels (Fin.cases hI
    (Fin.cases (M.transitive hP hC) (Fin.cases (M.identityIdealGraph_mem pairing unions powers separation hP hr hC)
      (Fin.cases (M.transitive hP hE) (Fin.cases hF (fun j => Fin.elim0 j))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.identityInsertionGraphEntryFormula 0 1 2 3 4 5 6) params members
    (M.prod_mem pairing unions powers separation hLabels hI)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.identityInsertionGraphEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod Labels I) = identityInsertionTaskGraph Labels I P r C E F := by
    apply ZFSet.ext
    intro z
    rw [identityInsertionTaskGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_identityInsertionGraphEntryFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

theorem identityInsertionTaskGraph_injection {P G r μ A m one Labels C E F : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hF : F ∈ M.sets)
    (action : PosetActionCode G P m one r A) (hOne : one ∈ G)
    (hC : C ∈ P) (hE : E ∈ P) (filter : MeetFilterCode P r μ F)
    (lower : ZFSet.pair C E ∈ r) (strict : ZFSet.pair E C ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair E x ∈ r) :
    InjectionCode Labels (M.groundEligibleTasks P G r μ A Labels)
      (identityInsertionTaskGraph Labels (M.groundEligibleTasks P G r μ A Labels) P r C E F) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  have every (label : ZFSet.{u}) (hlabel : label ∈ Labels) : identityInsertionTask P r C E F label ∈ I :=
    M.identityInsertionTask_mem pairing unions powers separation hP hr hF action hOne hC hE
      filter lower strict above hlabel
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro label hlabel
    refine ⟨identityInsertionTask P r C E F label,
      (pair_mem_identityInsertionTaskGraph Labels I P r C E F _ _).2 ⟨hlabel, every label hlabel, rfl⟩, ?_⟩
    intro task entry
    exact ((pair_mem_identityInsertionTaskGraph Labels I P r C E F _ _).1 entry).2.2
  · intro first second task oneEntry twoEntry
    have firstEq := ((pair_mem_identityInsertionTaskGraph Labels I P r C E F _ _).1 oneEntry).2.2
    have secondEq := ((pair_mem_identityInsertionTaskGraph Labels I P r C E F _ _).1 twoEntry).2.2
    exact identityInsertionTask_injective P r C E F (firstEq.symm.trans secondEq)

theorem identityInsertionTask_fields {P G r μ A m one Labels C E F label : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hF : F ∈ M.sets)
    (action : PosetActionCode G P m one r A) (hOne : one ∈ G)
    (hC : C ∈ P) (hE : E ∈ P) (filter : MeetFilterCode P r μ F)
    (lower : ZFSet.pair C E ∈ r) (strict : ZFSet.pair E C ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair E x ∈ r) (hlabel : label ∈ Labels) (j : Fin 6) :
    ZFSet.pair (identityInsertionTask P r C E F label)
      (literalTaskField C C (identityIdealGraph P r C) E F label j) ∈
      literalTaskFieldGraph (M.groundEligibleTasks P G r μ A Labels) P
        (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels j := by
  have base := identityIdealGraph_restrictedAction action hC
  have hBase := (M.mem_groundRelations P P _).2
    ⟨M.identityIdealGraph_mem pairing unions powers separation hP hr hC, base.shape⟩
  exact (literalTaskFieldGraph_entry_iff hC hC hBase hE
    ((M.mem_groundMeetFilters P r μ F).2 ⟨hF, filter⟩) hlabel j).2
    ⟨M.identityInsertionTask_mem pairing unions powers separation hP hr hF action hOne hC hE
      filter lower strict above hlabel, rfl⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTaskBearingSuccessorDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TaskBearingMainSuccessorCode
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem output_on_linked
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    ∃ extra : Fin 8 → ZFSet.{u}, (∀ j, extra j ∈ M.sets) ∧
      MainSuccessorOutputCode (linkedSuccessorOutputFields source.rawFields target.rawFields
        transition.map.points transition.map.actors extra) ∧
      MainSuccessorTaskBindingsCode M Labels (linkedSuccessorOutputFields source.rawFields target.rawFields
        transition.map.points transition.map.actors extra) := by
  obtain ⟨fields, ground, raw⟩ := code
  have sourceEq := source.rawFields_code.fields_unique raw.1.1
  have targetEq := target.rawFields_code.fields_unique raw.1.2.1
  have pairEq : ZFSet.pair transition.map.points transition.map.actors =
      ZFSet.pair (fields 48) (fields 49) := raw.1.2.2.2.2.1.1
  have maps := ZFSet.pair_inj.1 pairEq
  have output := raw.2.2.1
  have bindings := raw.2.2.2
  rw [← sourceEq, ← targetEq, ← maps.1, ← maps.2] at output bindings
  exact ⟨(fun j => fields (Fin.natAdd 52 j)),
    (fun j => ground (Fin.natAdd 52 j)), output, bindings⟩

end PartitionPilot.Forcing.TaskBearingMainSuccessorCode



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_MainPrefixHistoryUnionRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem MainPrefixHistoryUnionCode.unique {p q r : ZFSet.{u}}
    (first : MainPrefixHistoryUnionCode p q) (second : MainPrefixHistoryUnionCode p r) : q = r := by
  obtain ⟨T, S, E, rfl, fields⟩ := first
  obtain ⟨U, F, G, rfl, fields'⟩ := second
  apply mainPrefixCode_inj.2
  exact ⟨ZFSet.ext (fun x => (fields 0 x).trans (fields' 0 x).symm),
    ZFSet.ext (fun x => (fields 1 x).trans (fields' 1 x).symm),
    ZFSet.ext (fun x => (fields 2 x).trans (fields' 2 x).symm)⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

theorem MainPrefixAtIndex.refl {T q : ZFSet.{u}} (code : MainPrefixAtIndex T q) :
    MainPrefixExtends q q := by
  obtain ⟨S, E, rfl⟩ := code
  exact MainPrefixExtends.refl T S E

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalChronology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

namespace FinalChronology
variable {run} {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)

theorem history_values (s : ZFSet.{u}) :
    chronology.serial.toHistory.space s = run.limitChronologyFields.value 0 s ∧
    chronology.serial.toHistory.order s = run.limitChronologyFields.value 1 s ∧
    chronology.serial.toHistory.meetGraph s = run.limitChronologyFields.value 2 s ∧
    chronology.serial.toHistory.birth s = run.limitChronologyFields.value 3 s ∧
    chronology.serial.toHistory.height s = run.limitChronologyFields.value 4 s :=
  ⟨chronology.values 0 s, chronology.values 1 s, chronology.values 2 s,
    chronology.values 3 s, chronology.values 4 s⟩

theorem terminal_values (i₀ : I) :
    chronology.serial.toHistory.space run.cutoffLimit = (run.finalGeometry i₀).carrier ∧
    chronology.serial.toHistory.order run.cutoffLimit = (run.finalGeometry i₀).order ∧
    chronology.serial.toHistory.meetGraph run.cutoffLimit = (run.finalGeometry i₀).meetGraph ∧
    chronology.serial.toHistory.birth run.cutoffLimit = (run.finalGeometry i₀).birth ∧
    chronology.serial.toHistory.height run.cutoffLimit = (run.finalGeometry i₀).height := by
  obtain ⟨space, order, meet, birth, height⟩ := chronology.history_values run.cutoffLimit
  exact ⟨space.trans (run.limitChronologyFields_terminal 0),
    order.trans (run.limitChronologyFields_terminal 1), meet.trans (run.limitChronologyFields_terminal 2),
    birth.trans (run.limitChronologyFields_terminal 3), height.trans (run.limitChronologyFields_terminal 4)⟩

end FinalChronology

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixRawCoveredAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitPointMap_later_entry {i j : I} (before : i ≤ j) {x y q : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ (run.diagram.transition before).map.points)
    (image : ZFSet.pair x q ∈ run.limitPointMap i) :
    ZFSet.pair y q ∈ run.limitPointMap j :=
  (run.pointPresentation.inclusion_entry j y q).2
    ⟨(run.pointSystem.map_entry_bounds before entry).2,
      ((run.pointPresentation.inclusion_entry i x q).1 image).2.trans
        (run.pointPresentation.limitPoint_transition before entry)⟩

theorem limitPointMap_oldProfilePreservation (preserved : run.PreservesOldProfiles) (i : I) :
    OldProfilePreservationCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
      run.limitPoints run.limitOrder run.limitMeetGraph (run.limitPointMap i)
      (M.groundPower (run.diagram.stage i).stage.carrier) := by
  intro F hF c hc E hE cap hcap profile c' hc' E' hE' cap' hcap' imageC imageE imageCap
  let embedding := run.limitPointMap_meetEmbedding i
  refine ⟨hc', hE', hcap', fun _ member => ((mem_relationImage _ _ _ _).1 member).1,
    ?_, ?_, embedding.monotone c cap c' cap' profile.target_below_cap imageC imageCap,
    fun lower => profile.cap_not_below_target
      ((run.limitPointMap_order_iff i cap c cap' c' imageCap imageC).1 lower),
    fun lower => profile.separator_not_below_cap
      ((run.limitPointMap_order_iff i E cap E' cap' imageE imageCap).1 lower)⟩
  · obtain ⟨f, hf⟩ := profile.nonempty
    obtain ⟨f', entry, _⟩ := embedding.injection.function.2 f (profile.filter_subset hf)
    exact ⟨f', (mem_relationImage _ _ _ _).2
      ⟨(ZFSet.pair_mem_prod.1 (embedding.injection.function.1 entry)).2, f, hf, entry⟩⟩
  · intro q hq above
    obtain ⟨j, x, hx, equal⟩ := run.pointPresentation.limitPoint_coverage hq
    have imageX : ZFSet.pair x q ∈ run.limitPointMap j :=
      (run.pointPresentation.inclusion_entry j x q).2 ⟨hx, equal⟩
    obtain ⟨k, ik, jk⟩ := run.common_upper i j
    obtain ⟨cK, cEntry⟩ := run.pointSystem.map_entry_total ik hc
    obtain ⟨eK, eEntry⟩ := run.pointSystem.map_entry_total ik hE
    obtain ⟨capK, capEntry⟩ := run.pointSystem.map_entry_total ik hcap
    obtain ⟨xK, xEntry⟩ := run.pointSystem.map_entry_total jk hx
    have atStage := preserved i k ik F hF c hc E hE cap hcap profile
      cK (run.pointSystem.map_entry_bounds ik cEntry).2
      eK (run.pointSystem.map_entry_bounds ik eEntry).2
      capK (run.pointSystem.map_entry_bounds ik capEntry).2 cEntry eEntry capEntry
    have tested := atStage.profile.at_embedding (run.limitPointMap_meetEmbedding k)
      (run.diagram.stage k).stage.meet run.limitMeet_code atStage.filter_subset
      (run.limitPointMap_later_entry ik cEntry imageC)
      (run.limitPointMap_later_entry ik eEntry imageE)
      (run.limitPointMap_later_entry ik capEntry imageCap)
      (run.limitPointMap_later_entry jk xEntry imageX) above
    have imageEqual :
        relationImage (relationImage F (run.diagram.stage k).stage.carrier
          (run.diagram.transition ik).map.points) run.limitPoints (run.limitPointMap k) =
        relationImage F run.limitPoints (run.limitPointMap i) :=
      (relationImage_composition_on profile.filter_subset).trans
        (congrArg (relationImage F run.limitPoints) (run.limitPointMap_comp ik))
    rw [imageEqual] at tested
    exact tested

end GroundMainPrefix

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_MainPrefixConditionalStepCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace MainPrefixConditionalStepCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N f old next : ZFSet.{u}}
variable (code : MainPrefixConditionalStepCode M K Labels C D rD N f old next)
include code

theorem selected_of_successor {b S E : ZFSet.{u}}
    (oldCode : old = mainPrefixCode (insert b b) S E) :
    MainPrefixSelectedStepCode f old next := by
  rcases code with selected | ⟨T, F, G, first, limit, _⟩
  · exact selected
  · have index := (mainPrefixCode_inj.1 (oldCode.symm.trans first)).1
    exact False.elim (not_nonzeroLimitOrdinalCode_successor b (index.symm ▸ limit))

end MainPrefixConditionalStepCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_MainPrefixSelectedTraceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace OrdinalRecursionTrace
universe u
variable {B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem mainPrefix_values {i q : ZFSet.{u}} (entry : ZFSet.pair i q ∈ p) :
    q ∈ B ∧ MainPrefixAtIndex (insert i i) q := by
  have step := trace.2 i (trace.1.pair_source entry) q entry
  exact ⟨step.1, step.2.1⟩

theorem mainPrefix_extends {i j q r : ZFSet.{u}}
    (first : ZFSet.pair i q ∈ p) (second : ZFSet.pair j r ∈ p)
    (before : i = j ∨ i ∈ j) : MainPrefixExtends q r := by
  rcases before with rfl | before
  · have equal := trace.1.unique first second
    rw [equal]
    exact (trace.mainPrefix_values second).2.refl
  · have step := trace.2 j (trace.1.pair_source second) r second
    exact step.2.2.1 i q (pair_mem_graphRestriction.2 ⟨first, before⟩)

end OrdinalRecursionTrace

section
universe u

theorem MainPrefixHistoryExtends.union_code {p q T i : ZFSet.{u}}
    (history : MainPrefixHistoryExtends p q) (code : MainPrefixAtIndex T q)
    (last : ZFSet.pair i q ∈ p) : MainPrefixHistoryUnionCode p q := by
  obtain ⟨S, E, rfl⟩ := code
  refine ⟨T, S, E, rfl, ?_⟩
  intro j x
  constructor
  · intro member
    exact ⟨i, T, S, E, last, member⟩
  · rintro ⟨k, U, F, G, entry, member⟩
    have extension := mainPrefixExtends_iff.1 (history k _ entry)
    have subset : (Fin.cases U (Fin.cases F (fun _ => G)) : Fin 3 → ZFSet.{u}) j ⊆
        (Fin.cases T (Fin.cases S (fun _ => E)) : Fin 3 → ZFSet.{u}) j :=
      Fin.cases extension.1 (Fin.cases extension.2.1 (fun _ => extension.2.2)) j
    exact subset member

theorem OrdinalRecursionTrace.mainPrefix_successor_union {B seed g β p q : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) (insert β β) p)
    (last : ZFSet.pair β q ∈ p) : MainPrefixHistoryUnionCode p q := by
  have history : MainPrefixHistoryExtends p q := by
    intro i old entry
    exact trace.mainPrefix_extends entry last (ZFSet.mem_insert_iff.1 (trace.1.pair_source entry))
  exact history.union_code (trace.mainPrefix_values last).2 last

end

section
universe u

theorem MainPrefixTraceStepCode.selected_of_nonzero {B seed g α p y : ZFSet.{u}}
    (step : MainPrefixTraceStepCode B seed g α p y) (nonzero : α ≠ ∅) :
    ∃ input, MainPrefixHistoryUnionCode p input ∧ ZFSet.pair input y ∈ g := by
  rcases step.2.2.2 with ⟨zero, _⟩ | ⟨_, chosen⟩
  · exact False.elim (nonzero zero)
  · exact chosen

namespace OrdinalRecursionTrace
variable {B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
include trace

theorem mainPrefix_successor_entry (ordinal : ordinalSetProperty A)
    {β old next : ZFSet.{u}} (member : insert β β ∈ A)
    (oldEntry : ZFSet.pair β old ∈ p) (nextEntry : ZFSet.pair (insert β β) next ∈ p) :
    ZFSet.pair old next ∈ g := by
  have ordinalIndex := ordinalSetProperty_member ordinal member
  have subset : insert β β ⊆ A := fun x hx => ordinal.1 _ member x hx
  have earlier := trace.restrict ordinalIndex subset
  have oldRestricted : ZFSet.pair β old ∈ graphRestriction (insert β β) p :=
    pair_mem_graphRestriction.2 ⟨oldEntry, ZFSet.mem_insert _ _⟩
  have unionOld := earlier.mainPrefix_successor_union oldRestricted
  have nonzero : insert β β ≠ ∅ := by
    intro zero
    exact ZFSet.notMem_empty β (zero ▸ ZFSet.mem_insert β β)
  obtain ⟨input, unionInput, entry⟩ :=
    (trace.2 _ member next nextEntry).selected_of_nonzero nonzero
  exact unionInput.unique unionOld ▸ entry

end OrdinalRecursionTrace

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_MainPrefixConditionalTraceLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.OrdinalRecursionTrace
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD N f B seed g A p : ZFSet.{u}}
variable (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
variable (chosen : ∀ old next, ZFSet.pair old next ∈ g →
  MainPrefixConditionalStepCode M K Labels C D rD N f old next)
include trace chosen

theorem mainPrefix_selected_successor (ordinal : ordinalSetProperty A)
    {β old next : ZFSet.{u}} (member : insert β β ∈ A)
    (oldEntry : ZFSet.pair β old ∈ p) (nextEntry : ZFSet.pair (insert β β) next ∈ p) :
    MainPrefixSelectedStepCode f old next := by
  have entry := trace.mainPrefix_successor_entry ordinal member oldEntry nextEntry
  obtain ⟨S, E, oldCode⟩ := (trace.mainPrefix_values oldEntry).2
  exact (chosen old next entry).selected_of_successor oldCode

end PartitionPilot.Forcing.OrdinalRecursionTrace

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIndexedImageCovers
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

theorem pair_mem_indexedImageCover (I U V maps y i : ZFSet.{u}) :
    ZFSet.pair y i ∈ indexedImageCover I U V maps ↔
      y ∈ V ∧ i ∈ I ∧ ∃ x ∈ U, ∃ f,
        ZFSet.pair i f ∈ maps ∧ ZFSet.pair x y ∈ f := by
  rw [indexedImageCover, pair_mem_relationCompose]
  constructor
  · rintro ⟨hy, hi, z, _, converse, projection⟩
    obtain ⟨j, hj, x, hx, equal⟩ := (mem_productFirst I U _).1 projection
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    have flattened := (pair_mem_relationConverse _ _ _ _ _).1 converse
    obtain ⟨_, _, _, f, indexed, entry⟩ :=
      (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).1 flattened.2.2
    exact ⟨hy, hi, x, hx, f, indexed, entry⟩
  · rintro ⟨hy, hi, x, hx, f, indexed, entry⟩
    refine ⟨hy, hi, ZFSet.pair i x, ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, ?_, ?_⟩
    · exact (pair_mem_relationConverse _ _ _ _ _).2
        ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy,
          (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).2
            ⟨hi, hx, hy, f, indexed, entry⟩⟩
    · exact (mem_productFirst I U _).2 ⟨i, hi, x, hx, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem indexedImageCover_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I U V maps : ZFSet.{u}} (hI : I ∈ M.sets) (hU : U ∈ M.sets)
    (hV : V ∈ M.sets) (hMaps : maps ∈ M.sets) :
    indexedImageCover I U V maps ∈ M.sets := by
  have product := M.prod_mem pairing unions powers separation hI hU
  exact M.relationCompose_mem pairing unions powers separation hV product hI
    (M.relationConverse_mem pairing unions powers separation product hV
      (M.mapFamilyApplicationGraph_mem pairing unions powers separation hI hU hV hMaps))
    (M.productFirst_mem pairing unions powers separation hI hU)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalExtensionBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalChronology
open SetFormula
universe u v
variable {M N : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem exists_extension_basis (i₀ : I)
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ (run.finalGeometry i₀).order := by
  have terminal := chronology.terminal_values i₀
  have atTerminal : MeetFilterCode (chronology.serial.toHistory.space run.cutoffLimit)
      (chronology.serial.toHistory.order run.cutoffLimit)
      (chronology.serial.toHistory.meetGraph run.cutoffLimit) F := by
    simpa only [terminal.1, terminal.2.1, terminal.2.2.1] using filter
  have basis := chronology.serial.toHistory.exists_extension_basis includes pairingN unionsN powersN
    separationN infiniteN choiceN
    (M.insert_mem pairing unions run.cutoffLimit_ground run.cutoffLimit_ground)
    (run.finalGeometry i₀).columns_ground (run.finalGeometry i₀).coordinates_ground
    chronology.serial.ordinal smallD irreflexive (ZFSet.mem_insert run.cutoffLimit run.cutoffLimit)
    hF atTerminal
  simpa only [terminal.2.1] using basis

end PartitionPilot.Forcing.GroundMainPrefix.FinalChronology

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTaskBearingInsertionFulfillment
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TaskBearingMainSuccessorCode
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}

theorem insertion_data
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code) :
    ∃ Caps ∈ M.sets, ∃ Reps ∈ M.sets,
      source.main.stage.compressionTasks Labels ∈ M.sets ∧
      source.main.stage.compressionSources Labels ∈ M.sets ∧
      TaskCapFamilyCode (source.main.stage.compressionTasks Labels)
        source.main.stage.carrier target.main.stage.carrier target.main.stage.order target.main.stage.meetGraph
        transition.map.points (source.main.stage.compressionTargets Labels)
        (source.main.stage.compressionSeparators Labels) (source.main.stage.compressionFilters Labels)
        (M.groundPower source.main.stage.carrier) Caps ∧
      TaskRepresentativesCode Reps (source.main.stage.compressionTasks Labels)
        source.main.stage.carrier source.main.stage.actors source.main.stage.order source.main.stage.action
        (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
        (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels ∧
      CompressionActorFulfillmentCode (source.main.stage.compressionTasks Labels)
        source.main.stage.carrier source.main.stage.actors target.main.stage.carrier target.main.stage.actors
        target.main.stage.order target.main.stage.action transition.map.points transition.map.actors
        (source.main.stage.compressionSources Labels) Reps source.main.stage.top Caps := by
  obtain ⟨extra, ground, output, bindings⟩ := code.output_on_linked
  obtain ⟨tasks, sources, targets, separators, filters, families, representatives⟩ := bindings
  change extra 0 = source.main.stage.compressionTasks Labels at tasks
  change extra 1 = literalTaskFieldGraph (extra 0) source.main.stage.carrier
    (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
    (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels 0 at sources
  change extra 2 = literalTaskFieldGraph (extra 0) source.main.stage.carrier
    (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
    (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels 1 at targets
  change extra 3 = literalTaskFieldGraph (extra 0) source.main.stage.carrier
    (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
    (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels 3 at separators
  change extra 4 = literalTaskFieldGraph (extra 0) source.main.stage.carrier
    (M.groundRelations source.main.stage.carrier source.main.stage.carrier)
    (M.groundMeetFilters source.main.stage.carrier source.main.stage.order source.main.stage.meetGraph) Labels 4 at filters
  change extra 5 = M.groundPower source.main.stage.carrier at families
  rw [tasks] at sources targets separators filters
  change extra 1 = source.main.stage.compressionSources Labels at sources
  have caps := output.task_caps
  have actors := output.compression_actors
  change TaskCapFamilyCode (extra 0) source.main.stage.carrier target.main.stage.carrier
    target.main.stage.order target.main.stage.meetGraph transition.map.points
    (extra 2) (extra 3) (extra 4) (extra 5) (extra 7) at caps
  change CompressionActorFulfillmentCode (extra 0) source.main.stage.carrier source.main.stage.actors
    target.main.stage.carrier target.main.stage.actors target.main.stage.order target.main.stage.action
    transition.map.points transition.map.actors (extra 1) (extra 6) source.main.stage.top (extra 7) at actors
  rw [tasks, targets, separators, filters, families] at caps
  rw [tasks, sources] at actors
  exact ⟨extra 7, ground 7, extra 6, ground 6, tasks ▸ ground 0,
    sources ▸ ground 1, caps, representatives, actors⟩

end TaskBearingMainSuccessorCode

section
open SetFormula
universe u

theorem pair_mem_identityTaskCapFamily {Labels I P Q r Caps c e F label cap : ZFSet.{u}}
    (function : ZFSet.IsFunc I Q Caps) :
    ZFSet.pair label cap ∈ identityTaskCapFamily Labels I P Q r Caps c e F ↔
      label ∈ Labels ∧ ZFSet.pair (identityInsertionTask P r c e F label) cap ∈ Caps := by
  rw [identityTaskCapFamily, pair_mem_relationCompose]
  constructor
  · rintro ⟨hl, _, i, _, entry, image⟩
    have equal := ((pair_mem_identityInsertionTaskGraph Labels I P r c e F label i).1 entry).2.2
    exact ⟨hl, equal ▸ image⟩
  · rintro ⟨hl, image⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 image)
    exact ⟨hl, bounds.2, _, bounds.1,
      (pair_mem_identityInsertionTaskGraph Labels I P r c e F _ _).2 ⟨hl, bounds.1, rfl⟩, image⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem identityTaskCapFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Labels I P Q r Caps c e F : ZFSet.{u}} (hLabels : Labels ∈ M.sets) (hI : I ∈ M.sets)
    (hP : P ∈ M.sets) (hQ : Q ∈ M.sets) (hr : r ∈ M.sets) (hCaps : Caps ∈ M.sets)
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) :
    identityTaskCapFamily Labels I P Q r Caps c e F ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hLabels hI hQ
    (M.identityInsertionTaskGraph_mem pairing unions powers separation hLabels hI hP hr hc he hF) hCaps

end TransitiveGround

namespace GroundMainTransition
variable {M : TransitiveGround.{u}} {C D rD Labels Caps : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}
variable (transition : GroundMainTransition source target)
local notation "P" => source.carrier
local notation "Q" => target.carrier
local notation "I" => source.compressionTasks Labels
local notation "r" => source.order
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (caps : TaskCapFamilyCode (source.compressionTasks Labels) source.carrier target.carrier
  target.order target.meetGraph transition.points (source.compressionTargets Labels)
  (source.compressionSeparators Labels) (source.compressionFilters Labels) (M.groundPower source.carrier) Caps)
include caps pairing unions powers separation

theorem identityTaskCapFamily_function {c e F : ZFSet.{u}}
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) :
    ZFSet.IsFunc Labels Q (identityTaskCapFamily Labels I P Q r Caps c e F) := by
  have tasks := M.identityInsertionTaskGraph_injection pairing unions powers separation (Labels := Labels)
    source.carrier_ground source.order_ground hF source.action_code source.group_code.identity_mem
    hc he filter lower strict above
  exact relationCompose_function_of_subset tasks.function caps.function (fun _ h => h)

theorem identityTaskCapFamily_profile {c e F label cap c' e' : ZFSet.{u}}
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r)
    (entry : ZFSet.pair label cap ∈ identityTaskCapFamily Labels I P Q r Caps c e F)
    (imageC : ZFSet.pair c c' ∈ transition.points) (imageE : ZFSet.pair e e' ∈ transition.points) :
    CodedCapProfile Q target.order target.meetGraph c' e' cap (relationImage F Q transition.points) := by
  obtain ⟨hl, capEntry⟩ := (pair_mem_identityTaskCapFamily caps.function).1 entry
  have bounds := ZFSet.pair_mem_prod.1 (caps.function.1 capEntry)
  have fields := M.identityInsertionTask_fields pairing unions powers separation source.carrier_ground
    source.order_ground hF source.action_code source.group_code.identity_mem hc he filter lower strict above hl
  exact caps.profiles _ bounds.1 c hc e he F ((M.mem_groundPower P F).2 ⟨hF, filter.subset⟩)
    cap bounds.2 c' (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageC)).2
    e' (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageE)).2
    (fields 1) (fields 3) (fields 4) capEntry imageC imageE

theorem identityTaskCapFamily_meet {c e F first second cap₁ cap₂ c' : ZFSet.{u}}
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r)
    (entry₁ : ZFSet.pair first cap₁ ∈ identityTaskCapFamily Labels I P Q r Caps c e F)
    (entry₂ : ZFSet.pair second cap₂ ∈ identityTaskCapFamily Labels I P Q r Caps c e F)
    (different : first ≠ second) (imageC : ZFSet.pair c c' ∈ transition.points) :
    ZFSet.pair (ZFSet.pair cap₁ cap₂) c' ∈ target.meetGraph := by
  obtain ⟨hl₁, capEntry₁⟩ := (pair_mem_identityTaskCapFamily caps.function).1 entry₁
  obtain ⟨hl₂, capEntry₂⟩ := (pair_mem_identityTaskCapFamily caps.function).1 entry₂
  have bounds₁ := ZFSet.pair_mem_prod.1 (caps.function.1 capEntry₁)
  have bounds₂ := ZFSet.pair_mem_prod.1 (caps.function.1 capEntry₂)
  have fields₁ := M.identityInsertionTask_fields pairing unions powers separation source.carrier_ground
    source.order_ground hF source.action_code source.group_code.identity_mem hc he filter lower strict above hl₁
  have fields₂ := M.identityInsertionTask_fields pairing unions powers separation source.carrier_ground
    source.order_ground hF source.action_code source.group_code.identity_mem hc he filter lower strict above hl₂
  exact caps.common_target _ bounds₁.1 _ bounds₂.1 c hc cap₁ bounds₁.2 cap₂ bounds₂.2 c'
    (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageC)).2
    (fun equal => different (identityInsertionTask_injective P r c e F equal))
    (fields₁ 1) (fields₂ 1) capEntry₁ capEntry₂ imageC

theorem identityTaskCapFamily_injection {c e F : ZFSet.{u}}
    (hc : c ∈ P) (he : e ∈ P) (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) :
    InjectionCode Labels Q (identityTaskCapFamily Labels I P Q r Caps c e F) := by
  refine ⟨transition.identityTaskCapFamily_function pairing unions powers separation caps
    hc he hF filter lower strict above, ?_⟩
  intro first second cap firstEntry secondEntry
  by_cases equal : first = second
  · exact equal
  · obtain ⟨c', imageC, _⟩ := transition.point_embedding.injection.function.2 c hc
    obtain ⟨e', imageE, _⟩ := transition.point_embedding.injection.function.2 e he
    have profile := transition.identityTaskCapFamily_profile pairing unions powers separation caps
      hc he hF filter lower strict above firstEntry imageC imageE
    have meet := transition.identityTaskCapFamily_meet pairing unions powers separation caps
      hc he hF filter lower strict above firstEntry secondEntry equal imageC
    exact (profile.cap_not_below_target (target.meet.greatest cap cap c' cap profile.cap_mem meet
      (target.meet.order.refl cap profile.cap_mem) (target.meet.order.refl cap profile.cap_mem))).elim

end GroundMainTransition

end

section
universe u

namespace TaskRepresentative

theorem identityInsertion_agreement {P G r A R U Labels m one c e F label g : ZFSet.{u}}
    (represented : TaskRepresentative P r A R U Labels (identityInsertionTask P r c e F label) g)
    (action : PosetActionCode G P m one r A) : ActionAgreementBelow P r A g one c := by
  have restriction := represented.restriction
  change RestrictedActionCode P r A g c c (identityIdealGraph P r c) at restriction
  intro x hx y _ lower
  have fixed : ZFSet.pair (ZFSet.pair g x) x ∈ A := restriction.entry_action
    ((pair_mem_identityIdealGraph P r c x x).2 ⟨rfl, hx, lower⟩)
  have identity := action.one x hx
  have function : FunctionGraphOn (ZFSet.prod G P) A := ⟨P, action.function⟩
  exact ⟨fun entry => (function.unique entry fixed).symm ▸ identity,
    fun entry => (function.unique entry identity).symm ▸ fixed⟩

end TaskRepresentative

namespace GroundMainTransition
variable {M : TransitiveGround.{u}} {C D rD Labels Reps Caps : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}
variable (transition : GroundMainTransition source target)

theorem identityCompressionActor_fixes {c e F label k c' : ZFSet.{u}}
    (representatives : TaskRepresentativesCode Reps (source.compressionTasks Labels)
      source.carrier source.actors source.order source.action (M.groundRelations source.carrier source.carrier)
      (M.groundMeetFilters source.carrier source.order source.meetGraph) Labels)
    (hi : identityInsertionTask source.carrier source.order c e F label ∈ source.compressionTasks Labels)
    (actor : CompressionActorCode source.carrier source.actors target.carrier target.actors
      target.order target.action transition.points transition.actors (source.compressionSources Labels)
      Reps source.top Caps (identityInsertionTask source.carrier source.order c e F label) k)
    (imageC : ZFSet.pair c c' ∈ transition.points) :
    ∀ z ∈ target.carrier, ZFSet.pair z c' ∈ target.order →
      ZFSet.pair (ZFSet.pair k z) z ∈ target.action := by
  obtain ⟨hc, hc₂, hb, he, hF, hl, _⟩ := (literalTaskCode_mem_eligibleTaskSet source.carrier source.actors
    source.order source.meetGraph source.action (M.groundRelations source.carrier source.carrier)
    (M.groundMeetFilters source.carrier source.order source.meetGraph) Labels c c
    (identityIdealGraph source.carrier source.order c) e F label).1 hi
  have sourceEntry : ZFSet.pair (identityInsertionTask source.carrier source.order c e F label) c ∈
      source.compressionSources Labels :=
    (literalTaskFieldGraph_entry_iff hc hc₂ hb he hF hl 0).2 ⟨hi, rfl⟩
  obtain ⟨g, repEntry, _⟩ := representatives.1.2 _ hi
  have hg := (ZFSet.pair_mem_prod.1 (representatives.1.1 repEntry)).2
  obtain ⟨g', actorEntry, _⟩ := transition.group_embedding.injection.function.2 g hg
  have hg' := (ZFSet.pair_mem_prod.1 (transition.group_embedding.injection.function.1 actorEntry)).2
  have hc' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageC)).2
  have original := (representatives.2 _ _ repEntry).identityInsertion_agreement source.action_code
  have imageAgreement := transition.agreement g source.identity g' target.identity c c'
    actorEntry transition.group_embedding.one imageC original
  have compressionAgreement := actor.1 c hc g hg g' hg' c' hc' sourceEntry repEntry actorEntry imageC
  intro z hz lower
  exact (compressionAgreement z hz z hz lower).2
    ((imageAgreement z hz z hz lower).2 (target.action_code.one z hz))

end GroundMainTransition
end

namespace TaskBearingMainSuccessorCode
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target : GroundLinkedMainStage M K Labels C D rD}
variable {transition : GroundChronologicalMainTransition source.main target.main}
local notation "P" => source.main.stage.carrier
local notation "r" => source.main.stage.order
local notation "Q" => target.main.stage.carrier
local notation "R" => target.main.stage.order
local notation "ν" => target.main.stage.meetGraph
local notation "H" => target.main.stage.actors
local notation "B" => target.main.stage.action
local notation "points" => transition.map.points

theorem exists_insertionFamilies
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      source.code target.code transition.map.code)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {c e F : ZFSet.{u}} (hLabels : Labels ∈ M.sets) (hc : c ∈ P) (he : e ∈ P)
    (hF : F ∈ M.sets) (filter : MeetFilterCode P r source.main.stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ r) (strict : ZFSet.pair e c ∉ r)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ r) :
    ∃ capFamily ∈ M.sets, ∃ actorFamily ∈ M.sets,
      InjectionCode Labels Q capFamily ∧ InjectionCode Labels H actorFamily ∧
      (∀ label k top' v, ZFSet.pair label k ∈ actorFamily →
        ZFSet.pair source.main.stage.top top' ∈ points →
        (ZFSet.pair (ZFSet.pair k top') v ∈ B ↔ ZFSet.pair label v ∈ capFamily)) ∧
      ∀ c' e', ZFSet.pair c c' ∈ points → ZFSet.pair e e' ∈ points →
        (∀ label k, ZFSet.pair label k ∈ actorFamily →
          ∀ z ∈ Q, ZFSet.pair z c' ∈ R → ZFSet.pair (ZFSet.pair k z) z ∈ B) ∧
        (∀ label k cap, ZFSet.pair label k ∈ actorFamily → ZFSet.pair label cap ∈ capFamily →
          ∀ x x' y, ZFSet.pair x x' ∈ points → ZFSet.pair (ZFSet.pair k x') y ∈ B →
            ZFSet.pair y cap ∈ R) ∧
        (∀ label cap, ZFSet.pair label cap ∈ capFamily →
          CodedCapProfile Q R ν c' e' cap (relationImage F Q points)) ∧
        (∀ first second cap₁ cap₂, ZFSet.pair first cap₁ ∈ capFamily →
          ZFSet.pair second cap₂ ∈ capFamily → first ≠ second →
            ZFSet.pair (ZFSet.pair cap₁ cap₂) c' ∈ ν) := by
  obtain ⟨Caps, hCaps, Reps, hReps, hI, hSources, caps, reps, total⟩ := code.insertion_data
  obtain ⟨taskActors, hActors, actorFunction, actorLaws⟩ := M.choose_compressionActorFamily
    pairing unions powers separation choice hI source.main.stage.carrier_ground
    source.main.stage.actors_ground target.main.stage.carrier_ground target.main.stage.actors_ground
    target.main.stage.order_ground target.main.stage.action_ground transition.map.points_ground
    transition.map.actors_ground hSources hReps source.main.stage.top_ground hCaps total
  let I := source.main.stage.compressionTasks Labels
  let capFamily := identityTaskCapFamily Labels I P Q r Caps c e F
  let actorFamily := identityTaskCapFamily Labels I P H r taskActors c e F
  have capGround : capFamily ∈ M.sets := M.identityTaskCapFamily_mem pairing unions powers separation
    hLabels hI source.main.stage.carrier_ground target.main.stage.carrier_ground
    source.main.stage.order_ground hCaps hc he hF
  have actorGround : actorFamily ∈ M.sets := M.identityTaskCapFamily_mem pairing unions powers separation
    hLabels hI source.main.stage.carrier_ground target.main.stage.actors_ground
    source.main.stage.order_ground hActors hc he hF
  have capInjection : InjectionCode Labels Q capFamily := transition.map.identityTaskCapFamily_injection
    pairing unions powers separation caps hc he hF filter lower strict above
  have tasks := M.identityInsertionTaskGraph_injection pairing unions powers separation (Labels := Labels)
    source.main.stage.carrier_ground source.main.stage.order_ground hF source.main.stage.action_code
    source.main.stage.group_code.identity_mem hc he filter lower strict above
  have function : ZFSet.IsFunc Labels H actorFamily :=
    relationCompose_function_of_subset tasks.function actorFunction (fun _ h => h)
  have topLaw (label k top' v : ZFSet.{u}) (entry : ZFSet.pair label k ∈ actorFamily)
      (imageTop : ZFSet.pair source.main.stage.top top' ∈ points) :
      ZFSet.pair (ZFSet.pair k top') v ∈ B ↔ ZFSet.pair label v ∈ capFamily := by
    obtain ⟨hl, actorEntry⟩ := (pair_mem_identityTaskCapFamily actorFunction).1 entry
    have actor := actorLaws _ _ actorEntry
    have htop' := (ZFSet.pair_mem_prod.1 (transition.map.point_embedding.injection.function.1 imageTop)).2
    constructor
    · intro acted
      have hv := (ZFSet.pair_mem_prod.1 (target.main.stage.action_code.function.1 acted)).2
      exact (pair_mem_identityTaskCapFamily caps.function).2 ⟨hl, (actor.2 top' htop' v hv imageTop).1 acted⟩
    · intro capEntry
      have rawCap := ((pair_mem_identityTaskCapFamily caps.function).1 capEntry).2
      have hv := (ZFSet.pair_mem_prod.1 (caps.function.1 rawCap)).2
      exact (actor.2 top' htop' v hv imageTop).2 rawCap
  have actorInjection : InjectionCode Labels H actorFamily := by
    refine ⟨function, ?_⟩
    intro first second k firstEntry secondEntry
    have hf := (ZFSet.pair_mem_prod.1 (function.1 firstEntry)).1
    have hs := (ZFSet.pair_mem_prod.1 (function.1 secondEntry)).1
    obtain ⟨cap₁, firstCap, _⟩ := capInjection.function.2 first hf
    obtain ⟨cap₂, secondCap, _⟩ := capInjection.function.2 second hs
    obtain ⟨top', imageTop, _⟩ := transition.map.point_embedding.injection.function.2
      source.main.stage.top source.main.stage.top_mem
    have actionFunction : FunctionGraphOn (ZFSet.prod H Q) B := ⟨Q, target.main.stage.action_code.function⟩
    have equal := actionFunction.unique ((topLaw first k top' cap₁ firstEntry imageTop).2 firstCap)
      ((topLaw second k top' cap₂ secondEntry imageTop).2 secondCap)
    exact capInjection.injective first second cap₁ firstCap (equal.symm ▸ secondCap)
  refine ⟨capFamily, capGround, actorFamily, actorGround, capInjection, actorInjection, topLaw, ?_⟩
  intro c' e' imageC imageE
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro label k entry
    have actorEntry := ((pair_mem_identityTaskCapFamily actorFunction).1 entry).2
    have hi := (ZFSet.pair_mem_prod.1 (actorFunction.1 actorEntry)).1
    exact transition.map.identityCompressionActor_fixes reps hi (actorLaws _ _ actorEntry) imageC
  · intro label k cap actorEntry capEntry x x' y image acted
    have hk := (ZFSet.pair_mem_prod.1 (function.1 actorEntry)).2
    have shape := ZFSet.pair_mem_prod.1 (transition.map.point_embedding.injection.function.1 image)
    obtain ⟨top', imageTop, _⟩ := transition.map.point_embedding.injection.function.2
      source.main.stage.top source.main.stage.top_mem
    have htop' := (ZFSet.pair_mem_prod.1 (transition.map.point_embedding.injection.function.1 imageTop)).2
    have topAction := (topLaw label k top' cap actorEntry imageTop).2 capEntry
    have hy := (ZFSet.pair_mem_prod.1 (target.main.stage.action_code.function.1 acted)).2
    have hcap := (ZFSet.pair_mem_prod.1 (target.main.stage.action_code.function.1 topAction)).2
    have below := transition.map.point_embedding.monotone x source.main.stage.top x' top'
      (source.main.stage.greatest x shape.1) image imageTop
    exact target.main.stage.action_code.monotone k hk x' shape.2 top' htop' y hy cap hcap acted topAction below
  · intro label cap entry
    exact transition.map.identityTaskCapFamily_profile pairing unions powers separation caps
      hc he hF filter lower strict above entry imageC imageE
  · intro first second cap₁ cap₂ firstEntry secondEntry different
    exact transition.map.identityTaskCapFamily_meet pairing unions powers separation caps
      hc he hF filter lower strict above firstEntry secondEntry different imageC

end TaskBearingMainSuccessorCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixFinalStrictGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem selectedStep_terminal_entry {old next f : ZFSet.{u}} {i j : I}
    (before : i ≤ j) (adjacent : run.key j = insert (run.key i) (run.key i))
    (oldIndex : MainPrefixAtIndex (insert (run.key i) (run.key i)) old)
    (selected : MainPrefixSelectedStepCode f old next)
    (oldExtension : MainPrefixExtends old run.code)
    (nextExtension : MainPrefixExtends next run.code) :
    ZFSet.pair (run.linked i).code
      (ZFSet.pair (run.linked j).code (run.diagram.transition before).map.code) ∈ f := by
  obtain ⟨F, G, oldEqual⟩ := oldIndex
  obtain ⟨b, S, E, S', E', a, target, z, first, second, _, sourceEntry,
    selectedEntry, targetEntry, mapEntry⟩ := selected
  have same : b = run.key i := setSuccessor_injective
    (mainPrefixCode_inj.1 (first.symm.trans oldEqual)).1
  subst b
  rw [first] at oldExtension
  rw [second] at nextExtension
  have oldIncluded := (mainPrefixExtends_iff.1 oldExtension).2.1
  have nextIncluded := (mainPrefixExtends_iff.1 nextExtension).2
  have sourceEqual := (run.stageGraph_entry i a).1 (oldIncluded sourceEntry)
  have targetActual : ZFSet.pair (run.key j) target ∈ run.stageGraph := by
    rw [adjacent]
    exact nextIncluded.1 targetEntry
  have targetEqual := (run.stageGraph_entry j target).1 targetActual
  have mapActual : ZFSet.pair (ZFSet.pair (run.key j) (run.key i)) z ∈ run.transitionGraph := by
    rw [adjacent]
    exact nextIncluded.2 mapEntry
  have mapEqual := (run.transitionGraph_entry before z).1 mapActual
  rw [sourceEqual, targetEqual, mapEqual] at selectedEntry
  exact selectedEntry

theorem terminal_successor_entry {A B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (domain : run.indices = A) (extension : MainPrefixHistoryExtends p run.code)
    {i j : I} (before : i ≤ j)
    (adjacent : run.key j = insert (run.key i) (run.key i)) :
    ZFSet.pair (run.linked i).code
      (ZFSet.pair (run.linked j).code (run.diagram.transition before).map.code) ∈ f := by
  have oldMember : run.key i ∈ A := domain ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have nextMember : insert (run.key i) (run.key i) ∈ A := by
    rw [← adjacent]
    exact domain ▸ ZFSet.mem_range.2 ⟨j, rfl⟩
  obtain ⟨old, oldEntry⟩ := trace.1.total oldMember
  obtain ⟨next, nextEntry⟩ := trace.1.total nextMember
  have selected := trace.mainPrefix_selected_successor chosen
    (domain ▸ run.indices_ordinal) nextMember oldEntry nextEntry
  exact run.selectedStep_terminal_entry before adjacent (trace.mainPrefix_values oldEntry).2
    selected (extension _ _ oldEntry) (extension _ _ nextEntry)

theorem terminal_successor_taskBearing {A B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = A) (extension : MainPrefixHistoryExtends p run.code)
    {i j : I} (before : i ≤ j)
    (adjacent : run.key j = insert (run.key i) (run.key i)) :
    TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code :=
  tasks _ _ _ (run.terminal_successor_entry trace chosen domain extension before adjacent)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixInsertionSuccessors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem insertionFamilies_of_taskBearing {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {c e F : ZFSet.{u}} (hLabels : Labels ∈ M.sets)
    (hc : c ∈ (run.diagram.stage i).stage.carrier)
    (he : e ∈ (run.diagram.stage i).stage.carrier) (hF : F ∈ M.sets)
    (filter : MeetFilterCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph F)
    (lower : ZFSet.pair c e ∈ (run.diagram.stage i).stage.order)
    (strict : ZFSet.pair e c ∉ (run.diagram.stage i).stage.order)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ (run.diagram.stage i).stage.order) :
    ∃ capFamily ∈ M.sets, ∃ actorFamily ∈ M.sets,
      InjectionCode Labels (run.diagram.stage j).stage.carrier capFamily ∧
      InjectionCode Labels (run.diagram.stage j).stage.actors actorFamily ∧
      (∀ label k top' v, ZFSet.pair label k ∈ actorFamily →
        ZFSet.pair (run.diagram.stage i).stage.top top' ∈ (run.diagram.transition before).map.points →
        (ZFSet.pair (ZFSet.pair k top') v ∈ (run.diagram.stage j).stage.action ↔
          ZFSet.pair label v ∈ capFamily)) ∧
      ∀ c' e', ZFSet.pair c c' ∈ (run.diagram.transition before).map.points →
        ZFSet.pair e e' ∈ (run.diagram.transition before).map.points →
        (∀ label k, ZFSet.pair label k ∈ actorFamily →
          ∀ z ∈ (run.diagram.stage j).stage.carrier,
            ZFSet.pair z c' ∈ (run.diagram.stage j).stage.order →
              ZFSet.pair (ZFSet.pair k z) z ∈ (run.diagram.stage j).stage.action) ∧
        (∀ label k cap, ZFSet.pair label k ∈ actorFamily → ZFSet.pair label cap ∈ capFamily →
          ∀ x x' y, ZFSet.pair x x' ∈ (run.diagram.transition before).map.points →
            ZFSet.pair (ZFSet.pair k x') y ∈ (run.diagram.stage j).stage.action →
              ZFSet.pair y cap ∈ (run.diagram.stage j).stage.order) ∧
        (∀ label cap, ZFSet.pair label cap ∈ capFamily →
          CodedCapProfile (run.diagram.stage j).stage.carrier (run.diagram.stage j).stage.order
            (run.diagram.stage j).stage.meetGraph c' e' cap
            (relationImage F (run.diagram.stage j).stage.carrier
              (run.diagram.transition before).map.points)) ∧
        (∀ first second cap₁ cap₂, ZFSet.pair first cap₁ ∈ capFamily →
          ZFSet.pair second cap₂ ∈ capFamily → first ≠ second →
            ZFSet.pair (ZFSet.pair cap₁ cap₂) c' ∈ (run.diagram.stage j).stage.meetGraph) := by
  let transition := (run.diagram.transition before).retargetEq
    (run.linked_main i).symm (run.linked_main j).symm
  have actual : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code transition.map.code := by
    simpa only [transition, GroundChronologicalMainTransition.retargetEq_code] using code
  have families := actual.exists_insertionFamilies pairing unions powers separation choice hLabels
    (show c ∈ (run.linked i).main.stage.carrier from by simpa only [run.linked_main i] using hc)
    (show e ∈ (run.linked i).main.stage.carrier from by simpa only [run.linked_main i] using he)
    hF (by simpa only [run.linked_main i] using filter)
    (by simpa only [run.linked_main i] using lower)
    (by simpa only [run.linked_main i] using strict)
    (by simpa only [run.linked_main i] using above)
  simpa only [transition, GroundChronologicalMainTransition.retargetEq_points,
    run.linked_main i, run.linked_main j] using families

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixFinalInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem pointStageCover_ground : run.pointStageCover ∈ M.sets :=
  M.indexedImageCover_mem pairing unions powers separation run.indices_ground
    run.carrierUnion_ground run.limitPoints_ground run.limitPointInclusions_ground

theorem pointStageCover_entry (i : I) (y : ZFSet.{u}) :
    ZFSet.pair y (run.key i) ∈ run.pointStageCover ↔
      ∃ x ∈ (run.diagram.stage i).stage.carrier, ZFSet.pair x y ∈ run.limitPointMap i := by
  rw [pointStageCover, pair_mem_indexedImageCover]
  constructor
  · rintro ⟨_, _, x, _, f, indexed, entry⟩
    have equal := (run.limitPointInclusions_entry i f).1 indexed
    subst f
    exact ⟨x, (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).1, entry⟩
  · rintro ⟨x, hx, entry⟩
    exact ⟨(ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection i).function.1 entry)).2,
      ZFSet.mem_range.2 ⟨i, rfl⟩, x, run.pointPresentation.carrier_bound i hx,
      run.limitPointMap i, (run.limitPointInclusions_entry i _).2 rfl, entry⟩

theorem pointStageCover_total {y : ZFSet.{u}} (member : y ∈ run.limitPoints) :
    ∃ i ∈ run.indices, ZFSet.pair y i ∈ run.pointStageCover := by
  obtain ⟨i, x, hx, equal⟩ := run.pointPresentation.limitPoint_coverage member
  exact ⟨run.key i, ZFSet.mem_range.2 ⟨i, rfl⟩,
    (run.pointStageCover_entry i y).2
      ⟨x, hx, (run.pointPresentation.inclusion_entry i x y).2 ⟨hx, equal⟩⟩⟩

theorem exists_groundPointStageCover
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X : ZFSet.{u}} (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints) :
    ∃ f ∈ M.sets, ZFSet.IsFunc X run.indices f ∧ f ⊆ run.pointStageCover ∧
      ∀ y t, ZFSet.pair y t ∈ f → ∃ i : I, run.key i = t ∧
        ∃ x ∈ (run.diagram.stage i).stage.carrier, ZFSet.pair x y ∈ run.limitPointMap i := by
  obtain ⟨f, ground, function, included⟩ :=
    M.uniformize_relation pairing unions powers separation choice hX run.indices_ground
      run.pointStageCover_ground (fun _ hy => run.pointStageCover_total (subset hy))
  refine ⟨f, ground, function, included, ?_⟩
  intro y t entry
  have index := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 index
  exact ⟨i, rfl, (run.pointStageCover_entry i y).1 (included entry)⟩

theorem finalInsertionFamilies_transport (j : I)
    {caps actors c₀ d₀ c e d F : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hCaps : caps ∈ M.sets) (hActors : actors ∈ M.sets)
    (capInjection : InjectionCode Labels (run.diagram.stage j).stage.carrier caps)
    (actorInjection : InjectionCode Labels (run.diagram.stage j).stage.actors actors)
    (imageC : ZFSet.pair c₀ c ∈ run.limitPointMap j)
    (imageD : ZFSet.pair d₀ d ∈ run.limitPointMap j)
    (fixes : ∀ label k, ZFSet.pair label k ∈ actors →
      ∀ z ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair z c₀ ∈ (run.diagram.stage j).stage.order →
        ZFSet.pair (ZFSet.pair k z) z ∈ (run.diagram.stage j).stage.action)
    (dominates : ∀ label k cap, ZFSet.pair label k ∈ actors → ZFSet.pair label cap ∈ caps →
      ∀ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair (ZFSet.pair k d₀) y ∈ (run.diagram.stage j).stage.action →
        ZFSet.pair y cap ∈ (run.diagram.stage j).stage.order)
    (profiles : ∀ label cap cap', ZFSet.pair label cap ∈ caps →
      ZFSet.pair cap cap' ∈ run.limitPointMap j →
      CodedCapProfile run.limitPoints run.limitOrder run.limitMeetGraph c e cap' F)
    (meets : ∀ first second cap₁ cap₂, ZFSet.pair first cap₁ ∈ caps →
      ZFSet.pair second cap₂ ∈ caps → first ≠ second →
      ZFSet.pair (ZFSet.pair cap₁ cap₂) c₀ ∈ (run.diagram.stage j).stage.meetGraph) :
    run.finalInsertionCaps j caps ∈ M.sets ∧ run.finalInsertionActors j actors ∈ M.sets ∧
      FinalInsertionFamiliesCode Labels run.limitPoints run.limitActors run.limitOrder
        run.limitMeetGraph run.limitAction c e d F
        (run.finalInsertionCaps j caps) (run.finalInsertionActors j actors) := by
  refine ⟨run.finalInsertionCaps_ground j hLabels hCaps,
    run.finalInsertionActors_ground j hLabels hActors, ?_⟩
  refine ⟨run.finalInsertionCaps_injection j capInjection,
    run.finalInsertionActors_injection j actorInjection, ?_, ?_, ?_, ?_⟩
  · intro label k' entry
    obtain ⟨k, oldActor, imageK⟩ := (run.finalInsertionActors_entry j actorInjection).1 entry
    have agreement := ((run.diagram.stage j).stage.action_code.agreement_identity_iff_fixes).2
      (fixes label k oldActor)
    have finalAgreement := run.limitMaps_agreement j k (run.diagram.stage j).stage.identity
      k' (run.limitIdentity j) c₀ c imageK (run.limitActorMap_groupEmbedding j j).one imageC agreement
    exact ((run.limitAction_code j).agreement_identity_iff_fixes).1 finalAgreement
  · intro label k' cap' actorEntry capEntry y _ acted
    obtain ⟨k, oldActor, imageK⟩ := (run.finalInsertionActors_entry j actorInjection).1 actorEntry
    obtain ⟨cap, oldCap, imageCap⟩ := (run.finalInsertionCaps_entry j capInjection).1 capEntry
    have hk := (ZFSet.pair_mem_prod.1 (actorInjection.function.1 oldActor)).2
    have hd₀ := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 imageD)).1
    obtain ⟨y₀, stageActed, _⟩ := (run.diagram.stage j).stage.action_code.function.2
      (ZFSet.pair k d₀) (ZFSet.pair_mem_prod.2 ⟨hk, hd₀⟩)
    have hy₀ := (ZFSet.pair_mem_prod.1 ((run.diagram.stage j).stage.action_code.function.1 stageActed)).2
    obtain ⟨y', imageY, _⟩ := (run.limitPointMap_injection j).function.2 y₀ hy₀
    have targetActed := run.limitMaps_equivariant j k k' d₀ y₀ d y' imageK imageD imageY stageActed
    have actionFunction : FunctionGraphOn (ZFSet.prod run.limitActors run.limitPoints) run.limitAction :=
      ⟨run.limitPoints, run.limitAction_function⟩
    have equal : y = y' := actionFunction.unique acted targetActed
    rw [equal]
    exact (run.limitPointMap_meetEmbedding j).monotone y₀ cap y' cap'
      (dominates label k cap oldActor oldCap y₀ hy₀ stageActed) imageY imageCap
  · intro label cap' entry
    obtain ⟨cap, oldCap, imageCap⟩ := (run.finalInsertionCaps_entry j capInjection).1 entry
    exact profiles label cap cap' oldCap imageCap
  · intro first second cap₁' cap₂' firstEntry secondEntry different
    obtain ⟨cap₁, firstCap, firstImage⟩ := (run.finalInsertionCaps_entry j capInjection).1 firstEntry
    obtain ⟨cap₂, secondCap, secondImage⟩ := (run.finalInsertionCaps_entry j capInjection).1 secondEntry
    exact (run.limitPointMap_meetEmbedding j).map_meet cap₁ cap₂ c₀ cap₁' cap₂' c
      (meets first second cap₁ cap₂ firstCap secondCap different) firstImage secondImage imageC

end GroundMainPrefix

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (indices : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
include collection infinite choice indices

theorem exists_countablePointStageCover {X : ZFSet.{u}}
    (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints)
    (small : M.groundEmbeddable X ZFSet.omega) :
    ∃ j : I, ∃ f ∈ M.sets, ZFSet.IsFunc X run.indices f ∧ f ⊆ run.pointStageCover ∧
      (∀ x t, ZFSet.pair x t ∈ f → t ∈ run.key j) ∧
      ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
        ZFSet.pair y x ∈ run.limitPointMap j := by
  obtain ⟨f, ground, function, included, covers⟩ :=
    run.exists_groundPointStageCover choice hX subset
  have rangeGround := M.relationImage_mem separation hX run.indices_ground ground
  have rangeSmall := M.groundEmbeddable_function_image pairing unions powers separation choice
    hX run.indices_ground (M.omega_mem separation infinite) ground function small
  have rangeSubset : relationImage X run.indices f ⊆
      M.groundOmegaOne pairing unions powers separation collection infinite := by
    intro t ht
    rw [← indices]
    exact ((mem_relationImage _ _ _ _).1 ht).1
  obtain ⟨bound, inOmega, strict⟩ := M.groundOmegaOne_countable_bound
    pairing unions powers separation collection infinite choice rangeGround rangeSubset rangeSmall
  have inIndices : bound ∈ run.indices := by rw [indices]; exact inOmega
  obtain ⟨j, equal⟩ := ZFSet.mem_range.1 inIndices
  have strictEntry : ∀ x t, ZFSet.pair x t ∈ f → t ∈ run.key j := by
    intro x t entry
    rw [equal]
    have bounds := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact strict t ((mem_relationImage _ _ _ _).2 ⟨bounds.2, x, bounds.1, entry⟩)
  refine ⟨j, f, ground, function, included, strictEntry, ?_⟩
  intro x hx
  obtain ⟨t, entry, _⟩ := function.2 x hx
  obtain ⟨i, key, y, hy, image⟩ := covers x t entry
  have before : i ≤ j := (run.key_order i j).2 (Or.inr (by rw [key]; exact strictEntry x t entry))
  obtain ⟨z, transition⟩ := run.pointSystem.map_entry_total before hy
  exact ⟨z, (run.pointSystem.map_entry_bounds before transition).2,
    run.limitPointMap_later_entry before transition image⟩

theorem exists_countablePointLocalization {X : ZFSet.{u}}
    (hX : X ∈ M.sets) (subset : X ⊆ run.limitPoints)
    (small : M.groundEmbeddable X ZFSet.omega) :
    ∃ j : I, ∀ x ∈ X, ∃ y ∈ (run.diagram.stage j).stage.carrier,
      ZFSet.pair y x ∈ run.limitPointMap j := by
  obtain ⟨j, _, _, _, _, _, covered⟩ :=
    run.exists_countablePointStageCover collection infinite choice indices hX subset small
  exact ⟨j, covered⟩

end GroundMainPrefix

section
universe u v

namespace CodedCapProfile

theorem of_pushFilter_eq {L r μ c E cap H e F : ZFSet.{u}}
    (profile : CodedCapProfile L r μ c E cap (relationImage H L e))
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (equal : pushFilterCode L r e H = F) : CodedCapProfile L r μ c E cap F := by
  have positive_iff (x : ZFSet.{u}) (hx : x ∈ L) :
      (∃ y ∈ relationImage H L e, ZFSet.pair y x ∈ r) ↔ x ∈ F := by
    rw [← equal, mem_pushFilterCode]
    constructor
    · rintro ⟨y, hy, lower⟩
      obtain ⟨hyL, h, hh, image⟩ := (mem_relationImage H L e y).1 hy
      exact ⟨hx, h, hh, y, hyL, image, lower⟩
    · rintro ⟨_, h, hh, y, hy, image, lower⟩
      exact ⟨y, (mem_relationImage H L e y).2 ⟨hy, h, hh, image⟩, lower⟩
  refine ⟨profile.target_mem, profile.separator_mem, profile.cap_mem, filter.subset,
    filter.nonempty, ?_, profile.target_below_cap, profile.cap_not_below_target,
    profile.separator_not_below_cap⟩
  intro x hx above
  have original := profile.profile x hx above
  constructor
  · rintro ⟨f, hf, lower⟩
    exact original.1 ((positive_iff x hx).2 (filter.upward f hf x hx lower))
  · intro negative
    exact original.2 (fun positive => negative
      ⟨x, (positive_iff x hx).1 positive, meet.order.refl x hx⟩)

end CodedCapProfile

namespace GroundMainPrefix
open SetFormula
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitInsertionProfile {i j : I} (before : i ≤ j)
    (preserved : run.PreservesOldProfiles)
    {H F c E cap c' E' cap' : ZFSet.{u}} (hH : H ∈ M.sets)
    (subset : H ⊆ (run.diagram.stage i).stage.carrier)
    (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
    (equal : pushFilterCode run.limitPoints run.limitOrder (run.limitPointMap i) H = F)
    (profile : CodedCapProfile (run.diagram.stage j).stage.carrier
      (run.diagram.stage j).stage.order (run.diagram.stage j).stage.meetGraph c E cap
      (relationImage H (run.diagram.stage j).stage.carrier (run.diagram.transition before).map.points))
    (imageC : ZFSet.pair c c' ∈ run.limitPointMap j)
    (imageE : ZFSet.pair E E' ∈ run.limitPointMap j)
    (imageCap : ZFSet.pair cap cap' ∈ run.limitPointMap j) :
    CodedCapProfile run.limitPoints run.limitOrder run.limitMeetGraph c' E' cap' F := by
  have whole : relationImage H (run.diagram.stage j).stage.carrier
      (run.diagram.transition before).map.points ∈ M.sets :=
    M.relationImage_mem separation hH (run.diagram.stage j).stage.carrier_ground
      (run.diagram.transition before).map.points_ground
  have hc' := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 imageC)).2
  have hE' := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 imageE)).2
  have hcap' := (ZFSet.pair_mem_prod.1 ((run.limitPointMap_injection j).function.1 imageCap)).2
  have finalProfile := run.limitPointMap_oldProfilePreservation preserved j _
    ((M.mem_groundPower _ _).2 ⟨whole, profile.filter_subset⟩)
    c profile.target_mem E profile.separator_mem cap profile.cap_mem profile
    c' hc' E' hE' cap' hcap' imageC imageE imageCap
  have imageEqual :
      relationImage (relationImage H (run.diagram.stage j).stage.carrier
        (run.diagram.transition before).map.points) run.limitPoints (run.limitPointMap j) =
      relationImage H run.limitPoints (run.limitPointMap i) :=
    (relationImage_composition_on subset).trans
      (congrArg (relationImage H run.limitPoints) (run.limitPointMap_comp before))
  rw [imageEqual] at finalProfile
  exact finalProfile.of_pushFilter_eq run.limitMeet_code filter equal

end GroundMainPrefix
end

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem final_insertion_at {i j : I} (before : i ≤ j)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (preserved : run.PreservesOldProfiles) (hLabels : Labels ∈ M.sets)
    {c₀ e₀ d₀ H c e d F : ZFSet.{u}}
    (hc₀ : c₀ ∈ (run.diagram.stage i).stage.carrier)
    (he₀ : e₀ ∈ (run.diagram.stage i).stage.carrier)
    (hd₀ : d₀ ∈ (run.diagram.stage i).stage.carrier) (hH : H ∈ M.sets)
    (localFilter : MeetFilterCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph H)
    (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
    (equal : pushFilterCode run.limitPoints run.limitOrder (run.limitPointMap i) H = F)
    (imageC : ZFSet.pair c₀ c ∈ run.limitPointMap i)
    (imageE : ZFSet.pair e₀ e ∈ run.limitPointMap i)
    (imageD : ZFSet.pair d₀ d ∈ run.limitPointMap i)
    (lower : ZFSet.pair c₀ e₀ ∈ (run.diagram.stage i).stage.order)
    (strict : ZFSet.pair e₀ c₀ ∉ (run.diagram.stage i).stage.order)
    (above : ∀ x ∈ H, ZFSet.pair e₀ x ∈ (run.diagram.stage i).stage.order) :
    ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      FinalInsertionFamiliesCode Labels run.limitPoints run.limitActors run.limitOrder
        run.limitMeetGraph run.limitAction c e d F caps actors := by
  obtain ⟨caps, hCaps, actors, hActors, capInjection, actorInjection, _, laws⟩ :=
    run.insertionFamilies_of_taskBearing before code choice hLabels hc₀ he₀ hH localFilter
      lower strict above
  obtain ⟨c₁, stepC⟩ := run.pointSystem.map_entry_total before hc₀
  obtain ⟨e₁, stepE⟩ := run.pointSystem.map_entry_total before he₀
  obtain ⟨d₁, stepD⟩ := run.pointSystem.map_entry_total before hd₀
  have finalC := run.limitPointMap_later_entry before stepC imageC
  have finalE := run.limitPointMap_later_entry before stepE imageE
  have finalD := run.limitPointMap_later_entry before stepD imageD
  obtain ⟨fixes, dominates, profiles, meets⟩ := laws c₁ e₁ stepC stepE
  have finalFamilies := run.finalInsertionFamilies_transport j hLabels hCaps hActors
    capInjection actorInjection finalC finalD fixes
    (fun label k cap actor capEntry y _ acted => dominates label k cap actor capEntry
      d₀ d₁ y stepD acted)
    (fun label cap cap' entry imageCap => run.limitInsertionProfile before preserved hH
      localFilter.subset filter equal (profiles label cap entry) finalC finalE imageCap)
    meets
  exact ⟨run.finalInsertionCaps j caps, finalFamilies.1,
    run.finalInsertionActors j actors, finalFamilies.2.1, finalFamilies.2.2⟩

theorem filterPullback_configuration (i : I) {c e d c₀ e₀ d₀ F : ZFSet.{u}}
    (imageC : ZFSet.pair c₀ c ∈ run.limitPointMap i)
    (imageE : ZFSet.pair e₀ e ∈ run.limitPointMap i)
    (imageD : ZFSet.pair d₀ d ∈ run.limitPointMap i)
    (lower : ZFSet.pair c e ∈ run.limitOrder) (strict : ZFSet.pair e c ∉ run.limitOrder)
    (bound : ZFSet.pair c d ∈ run.limitOrder)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ run.limitOrder) :
    ZFSet.pair c₀ e₀ ∈ (run.diagram.stage i).stage.order ∧
    ZFSet.pair e₀ c₀ ∉ (run.diagram.stage i).stage.order ∧
    ZFSet.pair c₀ d₀ ∈ (run.diagram.stage i).stage.order ∧
    ∀ x ∈ copyPullback (run.diagram.stage i).stage.carrier run.limitPoints
        (run.limitPointMap i) F, ZFSet.pair e₀ x ∈ (run.diagram.stage i).stage.order := by
  refine ⟨(run.limitPointMap_order_iff i c₀ e₀ c e imageC imageE).1 lower,
    (fun reverse => strict ((run.limitPointMap_order_iff i e₀ c₀ e c imageE imageC).2 reverse)),
    (run.limitPointMap_order_iff i c₀ d₀ c d imageC imageD).1 bound, ?_⟩
  intro x hx
  obtain ⟨_, y, hy, _, image⟩ := (mem_copyPullback _ _ _ _ x).1 hx
  exact (run.limitPointMap_order_iff i e₀ x e y imageE image).1 (above y hy)

namespace FinalChronology
variable {run} {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem exists_groundFilterLocalization (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (indices : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (coordinateSmall : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F c e d : ZFSet.{u}} (hF : F ∈ M.sets)
    (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
    (hc : c ∈ run.limitPoints) (he : e ∈ run.limitPoints) (hd : d ∈ run.limitPoints) :
    ∃ i c₀ e₀ d₀ H,
      H = copyPullback (run.diagram.stage i).stage.carrier run.limitPoints (run.limitPointMap i) F ∧
      c₀ ∈ (run.diagram.stage i).stage.carrier ∧ e₀ ∈ (run.diagram.stage i).stage.carrier ∧
      d₀ ∈ (run.diagram.stage i).stage.carrier ∧
      ZFSet.pair c₀ c ∈ run.limitPointMap i ∧ ZFSet.pair e₀ e ∈ run.limitPointMap i ∧
      ZFSet.pair d₀ d ∈ run.limitPointMap i ∧ H ∈ M.sets ∧
      MeetFilterCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
        (run.diagram.stage i).stage.meetGraph H ∧
      pushFilterCode run.limitPoints run.limitOrder (run.limitPointMap i) H = F := by
  obtain ⟨B, hB, f, hf, injection, subset, coinitial⟩ :=
    chronology.exists_extension_basis i₀ (fun _ h => h) pairing unions powers separation
      infinite choice coordinateSmall irreflexive hF filter
  obtain ⟨j, covers⟩ := run.exists_countablePointLocalization collection infinite choice indices
    hB (fun _ hb => filter.subset (subset hb)) ⟨f, hf, injection⟩
  obtain ⟨k, c₁, e₁, d₁, hc₁, he₁, hd₁, rfl, rfl, rfl⟩ :=
    run.pointPresentation.triple_coverage hc he hd
  obtain ⟨i, ji, ki⟩ := run.common_upper j k
  obtain ⟨c₀, cStep⟩ := run.pointSystem.map_entry_total ki hc₁
  obtain ⟨e₀, eStep⟩ := run.pointSystem.map_entry_total ki he₁
  obtain ⟨d₀, dStep⟩ := run.pointSystem.map_entry_total ki hd₁
  have imageC := run.limitPointMap_later_entry ki cStep
    ((run.pointPresentation.inclusion_entry k c₁ _).2 ⟨hc₁, rfl⟩)
  have imageE := run.limitPointMap_later_entry ki eStep
    ((run.pointPresentation.inclusion_entry k e₁ _).2 ⟨he₁, rfl⟩)
  have imageD := run.limitPointMap_later_entry ki dStep
    ((run.pointPresentation.inclusion_entry k d₁ _).2 ⟨hd₁, rfl⟩)
  have coversAt : ∀ b ∈ B, ∃ a ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair a b ∈ run.limitPointMap i := by
    intro b hb
    obtain ⟨a, ha, image⟩ := covers b hb
    obtain ⟨a', step⟩ := run.pointSystem.map_entry_total ji ha
    exact ⟨a', (run.pointSystem.map_entry_bounds ji step).2,
      run.limitPointMap_later_entry ji step image⟩
  let H := copyPullback (run.diagram.stage i).stage.carrier run.limitPoints (run.limitPointMap i) F
  have ground : H ∈ M.sets := M.copyPullback_mem pairing unions powers separation
    (run.diagram.stage i).stage.carrier_ground run.limitPoints_ground (run.limitPointMap_ground i) hF
  have nonempty : H.Nonempty := by
    obtain ⟨x, hx⟩ := filter.nonempty
    obtain ⟨b, hb, _⟩ := coinitial x hx
    obtain ⟨a, ha, image⟩ := coversAt b hb
    exact ⟨a, (mem_copyPullback _ _ _ _ a).2 ⟨ha, b, subset hb, filter.subset (subset hb), image⟩⟩
  have localFilter := meetFilter_copyPullback (run.diagram.stage i).stage.meet filter
    (run.limitPointMap_meetEmbedding i) nonempty
  have recovered : pushFilterCode run.limitPoints run.limitOrder (run.limitPointMap i) H = F := by
    apply pushFilter_copyPullback_eq_of_coinitial (run.limitPointMap_injection i).function filter
    intro x hx
    obtain ⟨b, hb, lower⟩ := coinitial x hx
    obtain ⟨a, ha, image⟩ := coversAt b hb
    exact ⟨b, subset hb, a, ha, image, lower⟩
  exact ⟨i, c₀, e₀, d₀, H, rfl, (run.pointSystem.map_entry_bounds ki cStep).2,
    (run.pointSystem.map_entry_bounds ki eStep).2, (run.pointSystem.map_entry_bounds ki dStep).2,
    imageC, imageE, imageD, ground, localFilter, recovered⟩

end FinalChronology

end GroundMainPrefix

namespace GroundMainPrefix.FinalChronology
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem final_insertion_of_trace_oai (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (indices : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code) (preserved : run.PreservesOldProfiles)
    (hLabels : Labels ∈ M.sets) (coordinateSmall : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {c e d F : ZFSet.{u}} (hc : c ∈ run.limitPoints) (he : e ∈ run.limitPoints)
    (hd : d ∈ run.limitPoints) (hF : F ∈ M.sets)
    (filter : MeetFilterCode run.limitPoints run.limitOrder run.limitMeetGraph F)
    (lower : ZFSet.pair c e ∈ run.limitOrder) (strict : ZFSet.pair e c ∉ run.limitOrder)
    (bound : ZFSet.pair c d ∈ run.limitOrder)
    (above : ∀ x ∈ F, ZFSet.pair e x ∈ run.limitOrder) :
    ∃ caps ∈ M.sets, ∃ actors ∈ M.sets,
      FinalInsertionFamiliesCode Labels run.limitPoints run.limitActors run.limitOrder
        run.limitMeetGraph run.limitAction c e d F caps actors := by
  obtain ⟨i, c₀, e₀, d₀, H, pullback, hc₀, he₀, hd₀, imageC, imageE, imageD,
    hH, localFilter, equal⟩ := chronology.exists_groundFilterLocalization i₀ collection infinite
      choice indices coordinateSmall irreflexive hF filter hc he hd
  have configuration := run.filterPullback_configuration i imageC imageE imageD lower strict bound above
  have aboveH : ∀ x ∈ H, ZFSet.pair e₀ x ∈ (run.diagram.stage i).stage.order := by
    simpa only [pullback] using configuration.2.2.2
  have member : run.key i ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    indices ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have next := M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  obtain ⟨j, adjacent⟩ := ZFSet.mem_range.1 (indices.symm ▸ next)
  have before : i ≤ j := (run.key_order i j).2 (by
    rw [adjacent]
    exact Or.inr (ZFSet.mem_insert (run.key i) (run.key i)))
  exact run.final_insertion_at before
    (run.terminal_successor_taskBearing trace chosen tasks indices extension before adjacent)
    choice preserved hLabels hc₀ he₀ hd₀ hH localFilter filter equal imageC imageE imageD
    configuration.1 configuration.2.1 aboveH

end GroundMainPrefix.FinalChronology

end PartitionPilot.Forcing

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology.final_insertion_of_trace_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalChronology.final_insertion_of_trace_oai.{u, v}
