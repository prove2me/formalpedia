-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:32:25.501903+00:00
-- url     : https://prove2.me/submissions/b601859b-cd83-49a6-9851-067233da8174

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalChronology_final_insertion_of_trace
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_exists_rowSemanticQuotientInjectionModel
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_lifted_rows_not_wellorderable_not_choice
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_ordinal_choice
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_exists_groundMainFinalFulfillment
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticBinaryRow_ordinal_partial_cover

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameOrbitBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mem_symmetric_values (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (H : Set P) (x : ZFSet.{u}) :
    x ∈ (a.symmetricDomain s D F).values H ↔
      ∃ τ ∈ D.names, HereditarilySymmetric a s F τ ∧ Name.eval H τ = x := by
  rw [Name.NameDomain.mem_values]
  constructor
  · rintro ⟨τ, ⟨hτ, hs⟩, eq⟩
    exact ⟨τ, hτ, hs, eq⟩
  · rintro ⟨τ, hτ, hs, eq⟩
    exact ⟨τ, ⟨hτ, hs⟩, eq⟩

end PartitionPilot.Forcing.PosetAction


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PartitionPrincipleFormula
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

theorem truth_surjectionFormula {n : Nat} (a b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (surjectionFormula a b f) env ↔ ZFSet.IsFunc (env a) (env b) (env f) ∧
      ∀ y ∈ env b, ∃ x ∈ env a, ZFSet.pair x y ∈ env f := by
  simp only [surjectionFormula, Truth, truth_functionFormula, truth_exMem,
    truth_pairMembershipFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u

theorem realize_partitionPrinciple (M : TransitiveGround.{u}) :
    Realize M.sets partitionPrinciple Fin.elim0 ↔
      ∀ X ∈ M.sets, ∀ Y ∈ M.sets, ∀ f ∈ M.sets, ZFSet.IsFunc X Y f →
        (∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f) → M.groundEmbeddable Y X := by
  change (∀ X ∈ M.sets, ∀ Y ∈ M.sets, ∀ f ∈ M.sets,
    Realize M.sets (imp (BoundedFormula.surjectionFormula (n := 3) 2 1 0).toFormula
      (hasInjectionFormula (n := 3) 1 2)) (extend f (extend Y (extend X Fin.elim0)))) ↔ _
  apply forall_congr' fun X => forall_congr' fun hX =>
    forall_congr' fun Y => forall_congr' fun hY =>
    forall_congr' fun f => forall_congr' fun hf => ?_
  let env := extend f (extend Y (extend X Fin.elim0))
  have members : ∀ j, env j ∈ M.sets :=
    Fin.cases hf (Fin.cases hY (Fin.cases hX (fun j => Fin.elim0 j)))
  rw [realize_imp, M.realize_hasInjectionFormula 1 2 env members,
    BoundedFormula.realize_toFormula M _ env members, BoundedFormula.truth_surjectionFormula]
  exact ⟨fun h function onto => h ⟨function, onto⟩,
    fun h ⟨function, onto⟩ => h function onto⟩

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




namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace BoundedFormula

private theorem coveringPosition_meaning (D f I r mu : ZFSet.{u}) :
    Truth coveringPositionFormula ![D, f, I, r, mu] ↔
      (f = ∅ ∧ ∀ v ∈ I, ¬ ZFSet.pair v D ∈ r) ∨
      (ZFSet.IsFunc mu I f ∧ (∀ i v, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ r) ∧
        ∀ v ∈ I, ZFSet.pair v D ∈ r → ∃ i ∈ mu, ZFSet.pair i v ∈ f) := by
  simp only [coveringPositionFormula, truth_disj, Truth, truth_emptyFormula,
    truth_functionFormula, truth_imp, truth_pairMembershipFormula, truth_exMem]
  change (f = ∅ ∧ ∀ v ∈ I, ¬ ZFSet.pair v D ∈ r) ∨
    (ZFSet.IsFunc mu I f ∧ (∀ i ∈ mu, ∀ v ∈ I, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ r) ∧
      ∀ v ∈ I, ZFSet.pair v D ∈ r → ∃ i ∈ mu, ZFSet.pair i v ∈ f) ↔ _
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨function, bounds, onto⟩
    exact ⟨function, fun i v entry => bounds i (ZFSet.pair_mem_prod.1 (function.1 entry)).1
      v (ZFSet.pair_mem_prod.1 (function.1 entry)).2 entry, onto⟩
  · rintro ⟨function, bounds, onto⟩
    exact ⟨function, fun i _ v _ entry => bounds i v entry, onto⟩
end BoundedFormula
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (N : TransitiveGround.{u})

theorem indexedInjectionCandidates
    (zf : ZFRealization N.sets) {delta Y X p q : ZFSet.{u}}
    (hDelta : delta ∈ N.sets) (hY : Y ∈ N.sets) (hX : X ∈ N.sets)
    (hp : p ∈ N.sets) (hq : q ∈ N.sets)
    (pFunction : FunctionGraphOn delta p) (qFunction : FunctionGraphOn delta q)
    (bounds : ∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q → U ⊆ Y ∧ V ⊆ X)
    (possible : ∀ i ∈ delta, ∀ U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q →
      N.groundEmbeddable U V) :
    ∃ J ∈ N.sets, FunctionGraphOn delta J ∧
      (∀ i S, ZFSet.pair i S ∈ J → S.Nonempty) ∧
      ∀ i S U V f, ZFSet.pair i S ∈ J → ZFSet.pair i U ∈ p →
        ZFSet.pair i V ∈ q → (f ∈ S ↔ f ∈ N.sets ∧ InjectionCode U V f) := by
  have pairing : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powers : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  have separation : SeparationSchema N.sets := zf.2.1
  let PB := ⋃₀ ⋃₀ p
  let QB := ⋃₀ ⋃₀ q
  let W := N.groundRelations Y X
  have hPB : PB ∈ N.sets := N.union_mem unions (N.union_mem unions hp)
  have hQB : QB ∈ N.sets := N.union_mem unions (N.union_mem unions hq)
  have hW : W ∈ N.sets := N.groundRelations_mem pairing unions powers separation hY hX
  let params := extend p (extend q (extend PB (extend QB Fin.elim0)))
  have members : ∀ j, params j ∈ N.sets :=
    Fin.cases hp (Fin.cases hq (Fin.cases hPB (Fin.cases hQB (fun j => Fin.elim0 j))))
  let phi : BoundedFormula 6 := BoundedFormula.exMem 4 (BoundedFormula.exMem 6
    (.conj (BoundedFormula.pairMembershipFormula 2 1 4)
      (.conj (BoundedFormula.pairMembershipFormula 2 0 5)
        (BoundedFormula.injectionFormula 1 0 3))))
  let R := N.definableRelation phi.toFormula params delta W
  have hR : R ∈ N.sets := N.definableRelation_mem pairing unions powers separation
    phi.toFormula params members hDelta hW
  have meaning (i f : ZFSet.{u}) (hi : i ∈ N.sets) (hf : f ∈ N.sets) :
      Realize N.sets phi.toFormula (extend i (extend f params)) ↔
        ∃ U ∈ PB, ∃ V ∈ QB, ZFSet.pair i U ∈ p ∧ ZFSet.pair i V ∈ q ∧ InjectionCode U V f := by
    rw [BoundedFormula.realize_toFormula N phi _ (Fin.cases hi (Fin.cases hf members))]
    simp only [phi, BoundedFormula.truth_exMem, BoundedFormula.Truth,
      BoundedFormula.truth_pairMembershipFormula, BoundedFormula.truth_injectionFormula]
    rfl
  have entry (i U V f : ZFSet.{u}) (ip : ZFSet.pair i U ∈ p) (iq : ZFSet.pair i V ∈ q) :
      ZFSet.pair i f ∈ R ↔ f ∈ N.sets ∧ InjectionCode U V f := by
    rw [N.pair_mem_definableRelation]
    constructor
    · rintro ⟨hi, hf, raw⟩
      have hfN := N.transitive hW hf
      obtain ⟨U', _hU, V', _hV, ip', iq', code⟩ := (meaning i f (N.transitive hDelta hi) hfN).1 raw
      have sameU := pFunction.unique ip' ip
      have sameV := qFunction.unique iq' iq
      exact ⟨hfN, sameU ▸ sameV ▸ code⟩
    · rintro ⟨hf, code⟩
      have hi := pFunction.pair_source ip
      have bound : f ⊆ ZFSet.prod Y X := by
        intro z hz
        obtain ⟨u, hu, v, hv, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
        exact ZFSet.pair_mem_prod.2 ⟨(bounds i U V ip iq).1 hu, (bounds i U V ip iq).2 hv⟩
      refine ⟨hi, (N.mem_groundRelations Y X f).2 ⟨hf, bound⟩,
        (meaning i f (N.transitive hDelta hi) hf).2 ?_⟩
      exact ⟨U, pair_second_mem_doubleUnion ip, V, pair_second_mem_doubleUnion iq, ip, iq, code⟩
  let J := N.relationFiberFamily delta W R
  have hJ : J ∈ N.sets := N.relationFiberFamily_mem pairing unions powers separation hDelta hW hR
  have jFunction : FunctionGraphOn delta J :=
    ⟨_, N.relationFiberFamily_function separation hDelta hW hR⟩
  have exactCandidate (i S U V f : ZFSet.{u}) (j : ZFSet.pair i S ∈ J)
      (ip : ZFSet.pair i U ∈ p) (iq : ZFSet.pair i V ∈ q) :
      f ∈ S ↔ f ∈ N.sets ∧ InjectionCode U V f := by
    have same := ((N.pair_mem_relationFiberFamily delta W R i S).1 j).2.2
    rw [same, mem_relationFiber]
    constructor
    · intro member
      exact (entry i U V f ip iq).1 member.2
    · intro code
      have edge := (entry i U V f ip iq).2 code
      exact ⟨((N.pair_mem_definableRelation phi.toFormula params delta W i f).1 edge).2.1, edge⟩
  refine ⟨J, hJ, jFunction, ?_, exactCandidate⟩
  intro i S j
  have hi := jFunction.pair_source j
  obtain ⟨U, ip⟩ := pFunction.total hi
  obtain ⟨V, iq⟩ := qFunction.total hi
  obtain ⟨f, hf, code⟩ := possible i hi U V ip iq
  exact ⟨f, (exactCandidate i S U V f j ip iq).2 ⟨hf, code⟩⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (N : TransitiveGround.{u})

theorem ordinalPartition_injection_assembly
    (zf : ZFRealization N.sets)
    (acwo : ∀ delta ∈ N.sets, ordinalSetProperty delta →
      ∀ z ∈ N.sets, FunctionGraphOn delta z →
        (∀ beta A, ZFSet.pair beta A ∈ z → A.Nonempty) →
        ∃ c ∈ N.sets, FunctionGraphOn delta c ∧
          ∀ beta A x, ZFSet.pair beta A ∈ z → ZFSet.pair beta x ∈ c → x ∈ A)
    {delta Y X p q : ZFSet.{u}}
    (hDelta : delta ∈ N.sets) (ordinal : ordinalSetProperty delta)
    (hY : Y ∈ N.sets) (hX : X ∈ N.sets) (hp : p ∈ N.sets) (hq : q ∈ N.sets)
    (pFunction : FunctionGraphOn delta p) (qFunction : FunctionGraphOn delta q)
    (bounds : ∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q → U ⊆ Y ∧ V ⊆ X)
    (cover : ∀ y ∈ Y, ∃ i ∈ delta, ∃ U, ZFSet.pair i U ∈ p ∧ y ∈ U)
    (domainDisjoint : ∀ i k U V y, ZFSet.pair i U ∈ p → ZFSet.pair k V ∈ p →
      y ∈ U → y ∈ V → i = k)
    (targetDisjoint : ∀ i k U V x, ZFSet.pair i U ∈ q → ZFSet.pair k V ∈ q →
      x ∈ U → x ∈ V → i = k)
    (possible : ∀ i ∈ delta, ∀ U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q →
      N.groundEmbeddable U V) :
    N.groundEmbeddable Y X := by
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  obtain ⟨J, hJ, jFunction, nonempty, candidates⟩ :=
    N.indexedInjectionCandidates zf hDelta hY hX hp hq pFunction qFunction bounds possible
  obtain ⟨c, hc, cFunction, chosen⟩ := acwo delta hDelta ordinal J hJ jFunction nonempty
  have codes (i U V f : ZFSet.{u}) (ip : ZFSet.pair i U ∈ p)
      (iq : ZFSet.pair i V ∈ q) (entry : ZFSet.pair i f ∈ c) : InjectionCode U V f := by
    obtain ⟨S, indexed⟩ := jFunction.total (cFunction.pair_source entry)
    exact ((candidates i S U V f indexed ip iq).1 (chosen i S f indexed entry)).2
  let family := relationImage delta (⋃₀ ⋃₀ c) c
  let j := ⋃₀ family
  have hFamily : family ∈ N.sets := N.relationImage_mem zf.2.1 hDelta
    (N.union_mem unions (N.union_mem unions hc)) hc
  have hj : j ∈ N.sets := N.union_mem unions hFamily
  have entries (z : ZFSet.{u}) : z ∈ j ↔
      ∃ i ∈ delta, ∃ f, ZFSet.pair i f ∈ c ∧ z ∈ f := by
    rw [ZFSet.mem_sUnion]
    constructor
    · rintro ⟨f, member, zf⟩
      obtain ⟨_bound, i, hi, edge⟩ := (mem_relationImage delta (⋃₀ ⋃₀ c) c f).1 member
      exact ⟨i, hi, f, edge, zf⟩
    · rintro ⟨i, hi, f, edge, zf⟩
      exact ⟨f, (mem_relationImage delta (⋃₀ ⋃₀ c) c f).2
        ⟨pair_second_mem_doubleUnion edge, i, hi, edge⟩, zf⟩
  have localCode (i : ZFSet.{u}) (hi : i ∈ delta) (f : ZFSet.{u}) (edge : ZFSet.pair i f ∈ c) :
      ∃ U V, ZFSet.pair i U ∈ p ∧ ZFSet.pair i V ∈ q ∧ InjectionCode U V f := by
    obtain ⟨U, ip⟩ := pFunction.total hi
    obtain ⟨V, iq⟩ := qFunction.total hi
    exact ⟨U, V, ip, iq, codes i U V f ip iq edge⟩
  refine ⟨j, hj, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · intro z member
    obtain ⟨i, hi, f, edge, zf⟩ := (entries z).1 member
    obtain ⟨U, V, ip, iq, code⟩ := localCode i hi f edge
    obtain ⟨y, hy, x, hx, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 zf)
    exact ZFSet.pair_mem_prod.2 ⟨(bounds i U V ip iq).1 hy, (bounds i U V ip iq).2 hx⟩
  · intro y hy
    obtain ⟨i, hi, U, ip, yu⟩ := cover y hy
    obtain ⟨V, iq⟩ := qFunction.total hi
    obtain ⟨f, edge⟩ := cFunction.total hi
    have code := codes i U V f ip iq edge
    obtain ⟨x, picked, unique⟩ := code.function.2 y yu
    refine ⟨x, (entries _).2 ⟨i, hi, f, edge, picked⟩, ?_⟩
    intro x' other
    obtain ⟨k, hk, g, otherEdge, otherPicked⟩ := (entries _).1 other
    obtain ⟨U', V', kp, kq, otherCode⟩ := localCode k hk g otherEdge
    have inU' := (ZFSet.pair_mem_prod.1 (otherCode.function.1 otherPicked)).1
    have equalIndex : i = k := domainDisjoint i k U U' y ip kp yu inU'
    subst k
    have equalFunction : g = f := cFunction.unique otherEdge edge
    exact unique x' (equalFunction ▸ otherPicked)
  · intro y y' x first second
    obtain ⟨i, hi, f, edge, picked⟩ := (entries _).1 first
    obtain ⟨k, hk, g, otherEdge, otherPicked⟩ := (entries _).1 second
    obtain ⟨U, V, ip, iq, code⟩ := localCode i hi f edge
    obtain ⟨U', V', kp, kq, otherCode⟩ := localCode k hk g otherEdge
    have inV := (ZFSet.pair_mem_prod.1 (code.function.1 picked)).2
    have inV' := (ZFSet.pair_mem_prod.1 (otherCode.function.1 otherPicked)).2
    have equalIndex : i = k := targetDisjoint i k V V' x iq kq inV inV'
    subst k
    have equalFunction : g = f := cFunction.unique otherEdge edge
    exact code.injective y y' x picked (equalFunction ▸ otherPicked)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProjectedRowChooserWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable (s : Presentation P) {G : Type v} [Group G]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

theorem mem_symmetricExtension (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ (M.symmetricExtension s a F H).sets ↔
      ∃ τ ∈ (M.nameDomain s).names, HereditarilySymmetric a s F τ ∧
        Name.eval {q | H.mem q} τ = x :=
  a.mem_symmetric_values s (M.nameDomain s) F {q | H.mem q} x

end PartitionPilot.Forcing.TransitiveGround


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMainFinalSupport
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ data : GroundMainOrdinalConstructionData M K C pairing unions powers separation,
      ∃ ordinalC : ordinalSetProperty C,
        letI := ordinalMainIndexPreorder ordinalC
        ∃ run : GroundMainPrefix M K C C (rationalCarrier data.seed.fractionCode)
            (rationalLtGraph data.seed.fractionCode) pairing unions powers separation (SetMembers C),
          run.indices = C ∧ run.PreservesOldProfiles ∧
          MainPrefixHistoryUnionCode data.history run.code ∧
          MainPrefixHistoryExtends data.history run.code ∧
          (∀ q, MainPrefixHistoryUnionCode data.history q → q = run.code) ∧
          GroundBelow M run.indices K ∧ ZFSet.rank run.code < ZFSet.rank K ∧
          ∃ i₀ : SetMembers C, run.key i₀ = ∅ ∧
            ∃ fulfilled : run.FinalSupportFulfillment data.level i₀,
              let geometry := run.finalGeometry i₀
              let inclusions := run.finalInclusions i₀
              geometry.code ∈ M.sets ∧ ZFSet.rank geometry.code < ZFSet.rank K ∧
              GroundBelow M geometry.carrier K ∧ GroundBelow M geometry.actors K ∧
              inclusions.pointFamily ∈ M.sets ∧ inclusions.actorFamily ∈ M.sets ∧
              ZFSet.rank inclusions.pointFamily < ZFSet.rank K ∧
              ZFSet.rank inclusions.actorFamily < ZFSet.rank K ∧
              fulfilled.chronology.serial.code ∈ M.sets ∧
              ∀ N : TransitiveGround.{u}, M.sets ⊆ N.sets →
                Realize N.sets SetFormula.pairing Fin.elim0 →
                Realize N.sets SetFormula.union Fin.elim0 →
                Realize N.sets powerSet Fin.elim0 → SeparationSchema N.sets →
                Realize N.sets infinity Fin.elim0 → Realize N.sets SetFormula.choice Fin.elim0 →
                ∀ F ∈ N.sets, MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F →
                  ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
                    ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ geometry.order := by
  dsimp only
  obtain ⟨data, ordinalC, run, indices, profiles, terminal, extension, unique, small, rank,
    i₀, zero, fulfilled, codeGround, codeRank, pointSmall, actorSmall, pointMaps,
    actorMaps, pointRank, actorRank, chronologyGround, basis⟩ :=
    M.exists_groundMainFinalFulfillment pairing unions powers separation collection infinite choice hK standard
  let := ordinalMainIndexPreorder ordinalC
  let support : run.FinalSupportFulfillment data.level i₀ := {
    toFinalFulfillment := fulfilled
    insertion := fun c hc e he d hd F hF filter lower strict bound above =>
      fulfilled.chronology.final_insertion_of_trace i₀ collection infinite choice data.trace
        (fun old next entry => (data.steps_entries old next entry).2)
        (fun source target z entry => (data.successors_entries source target z entry).2.2)
        indices extension profiles
        (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
        ⟨data.seed.coordinateInjection, data.seed.injection_ground, data.seed.injection_code⟩
        data.seed.dense.irrefl hc he hd hF filter lower strict bound above }
  exact ⟨data, ordinalC, run, indices, profiles, terminal, extension, unique, small, rank,
    i₀, zero, support, codeGround, codeRank, pointSmall, actorSmall, pointMaps,
    actorMaps, pointRank, actorRank, chronologyGround, basis⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOrdinalImagePartitions
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

theorem pair_mem_ordinalFirstRelation (delta Y R i y : ZFSet.{u}) :
    ZFSet.pair i y ∈ ordinalFirstRelation delta Y R ↔
      ZFSet.pair i y ∈ R ∧ i ∈ delta ∧ y ∈ Y ∧ ∀ k ∈ i, ZFSet.pair k y ∉ R := by
  rw [ordinalFirstRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨entry, j, hj, z, hz, equal, least⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨entry, hj, hz, least⟩
  · rintro ⟨entry, hi, hy, least⟩
    exact ⟨entry, i, hi, y, hy, rfl, least⟩

namespace BoundedFormula

private theorem firstRelationEntry_meaning {n} (z delta Y R : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (firstRelationEntryFormula z delta Y R) env ↔
      ∃ i ∈ env delta, ∃ y ∈ env Y, env z = ZFSet.pair i y ∧
        ∀ k ∈ i, ZFSet.pair k y ∉ env R := by
  simp only [firstRelationEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (N : TransitiveGround.{u})

theorem ordinalFirstRelation_mem (separation : SeparationSchema N.sets)
    {delta Y R : ZFSet.{u}} (hDelta : delta ∈ N.sets) (hY : Y ∈ N.sets) (hR : R ∈ N.sets) :
    ordinalFirstRelation delta Y R ∈ N.sets := by
  let params := extend delta (extend Y (extend R Fin.elim0))
  have ground := N.bounded_separation_mem separation
    (BoundedFormula.firstRelationEntryFormula 0 1 2 3) params
    (Fin.cases hDelta (Fin.cases hY (Fin.cases hR (fun j => Fin.elim0 j)))) hR
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.firstRelationEntryFormula 0 1 2 3) (extend z params)) R =
      ordinalFirstRelation delta Y R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ordinalFirstRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.firstRelationEntry_meaning _ _ _ _ _)
  exact equal ▸ ground

theorem ordinal_image_partitions
    (zf : ZFRealization N.sets) {delta X Y R f : ZFSet.{u}}
    (hDelta : delta ∈ N.sets) (ordinal : ordinalSetProperty delta)
    (hX : X ∈ N.sets) (hY : Y ∈ N.sets) (hR : R ∈ N.sets) (hf : f ∈ N.sets)
    (relation : R ⊆ ZFSet.prod delta X) (function : ZFSet.IsFunc X Y f)
    (onto : ∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f)
    (coverX : ∀ x ∈ X, ∃ i ∈ delta, ZFSet.pair i x ∈ R) :
    ∃ p ∈ N.sets, ∃ q ∈ N.sets,
      FunctionGraphOn delta p ∧ FunctionGraphOn delta q ∧
      (∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q → U ⊆ Y ∧ V ⊆ X) ∧
      (∀ y ∈ Y, ∃ i ∈ delta, ∃ U, ZFSet.pair i U ∈ p ∧ y ∈ U) ∧
      (∀ i k U V y, ZFSet.pair i U ∈ p → ZFSet.pair k V ∈ p → y ∈ U → y ∈ V → i = k) ∧
      (∀ i k U V x, ZFSet.pair i U ∈ q → ZFSet.pair k V ∈ q → x ∈ U → x ∈ V → i = k) ∧
      ∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q →
        (∀ y, y ∈ U ↔ y ∈ Y ∧
          (∃ x ∈ X, ZFSet.pair i x ∈ R ∧ ZFSet.pair x y ∈ f) ∧
          ∀ k ∈ i, ¬ ∃ x ∈ X, ZFSet.pair k x ∈ R ∧ ZFSet.pair x y ∈ f) ∧
        (∀ x, x ∈ V ↔ ZFSet.pair i x ∈ R ∧ ∃ y ∈ U, ZFSet.pair x y ∈ f) ∧
        graphRestriction V f ∈ N.sets ∧ ZFSet.IsFunc V U (graphRestriction V f) ∧
        ∀ y ∈ U, ∃ x ∈ V, ZFSet.pair x y ∈ graphRestriction V f := by
  have pairing := zf.1.2.2.2.1
  have unions := zf.1.2.2.2.2.1
  have powers := zf.1.2.2.2.2.2.1
  have separation : SeparationSchema N.sets := zf.2.1
  let image := relationCompose delta X Y R f
  have hImage : image ∈ N.sets := N.relationCompose_mem pairing unions powers separation hDelta hX hY hR hf
  have imageEntries (i y : ZFSet.{u}) : ZFSet.pair i y ∈ image ↔
      i ∈ delta ∧ y ∈ Y ∧ ∃ x ∈ X, ZFSet.pair i x ∈ R ∧ ZFSet.pair x y ∈ f :=
    pair_mem_relationCompose _ _ _ _ _ _ _
  let first := ordinalFirstRelation delta Y image
  have hFirst : first ∈ N.sets := N.ordinalFirstRelation_mem separation hDelta hY hImage
  have firstUnique (i k y : ZFSet.{u}) (iy : ZFSet.pair i y ∈ first)
      (ky : ZFSet.pair k y ∈ first) : i = k := by
    have a := (pair_mem_ordinalFirstRelation delta Y image i y).1 iy
    have b := (pair_mem_ordinalFirstRelation delta Y image k y).1 ky
    rcases ordinalSetProperty_mem_compare ordinal a.2.1 b.2.1 with less | equal | greater
    · exact (b.2.2.2 i less a.1).elim
    · exact equal
    · exact (a.2.2.2 k greater b.1).elim
  let preimage := relationCompose delta Y X first (relationConverse X Y f)
  have hPreimage : preimage ∈ N.sets := N.relationCompose_mem pairing unions powers separation hDelta hY hX
    hFirst (N.relationConverse_mem pairing unions powers separation hX hY hf)
  let selected := ZFSet.sep (fun z => z ∈ preimage) R
  have hSelected : selected ∈ N.sets := by
    exact N.bounded_separation_mem separation (.mem 0 1) (extend preimage Fin.elim0)
      (Fin.cases hPreimage (fun j => Fin.elim0 j)) hR
  let p := N.relationFiberFamily delta Y first
  let q := N.relationFiberFamily delta X selected
  have hp := N.relationFiberFamily_mem pairing unions powers separation hDelta hY hFirst
  have hq := N.relationFiberFamily_mem pairing unions powers separation hDelta hX hSelected
  have pFunction : FunctionGraphOn delta p :=
    ⟨N.groundPower Y, N.relationFiberFamily_function separation hDelta hY hFirst⟩
  have qFunction : FunctionGraphOn delta q :=
    ⟨N.groundPower X, N.relationFiberFamily_function separation hDelta hX hSelected⟩
  have pEntries (i U : ZFSet.{u}) (entry : ZFSet.pair i U ∈ p) (y : ZFSet.{u}) :
      y ∈ U ↔ y ∈ Y ∧ ZFSet.pair i y ∈ first := by
    have equal := ((N.pair_mem_relationFiberFamily delta Y first i U).1 entry).2.2
    rw [equal, mem_relationFiber]
  have qEntries (i V : ZFSet.{u}) (entry : ZFSet.pair i V ∈ q) (x : ZFSet.{u}) :
      x ∈ V ↔ x ∈ X ∧ ZFSet.pair i x ∈ selected := by
    have equal := ((N.pair_mem_relationFiberFamily delta X selected i V).1 entry).2.2
    rw [equal, mem_relationFiber]
  have sourceEntries (i U V : ZFSet.{u}) (ip : ZFSet.pair i U ∈ p) (iq : ZFSet.pair i V ∈ q)
      (x : ZFSet.{u}) : x ∈ V ↔ ZFSet.pair i x ∈ R ∧ ∃ y ∈ U, ZFSet.pair x y ∈ f := by
    rw [qEntries i V iq x]
    constructor
    · rintro ⟨hx, entry⟩
      obtain ⟨ix, back⟩ := ZFSet.mem_sep.1 entry
      obtain ⟨_, _, y, hy, firstEntry, converse⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 back
      exact ⟨ix, y, (pEntries i U ip y).2 ⟨hy, firstEntry⟩,
        ((pair_mem_relationConverse X Y f x y).1 converse).2.2⟩
    · rintro ⟨ix, y, hy, xy⟩
      have shape := ZFSet.pair_mem_prod.1 (relation ix)
      have firstEntry := (pEntries i U ip y).1 hy
      exact ⟨shape.2, ZFSet.mem_sep.2 ⟨ix,
        (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨shape.1, shape.2, y, firstEntry.1, firstEntry.2,
          (pair_mem_relationConverse X Y f x y).2 ⟨shape.2, firstEntry.1, xy⟩⟩⟩⟩
  refine ⟨p, hp, q, hq, pFunction, qFunction, ?_, ?_, ?_, ?_, ?_⟩
  · intro i U V ip iq
    exact ⟨fun y hy => ((pEntries i U ip y).1 hy).1,
      fun x hx => ((qEntries i V iq x).1 hx).1⟩
  · intro y hy
    obtain ⟨x, hx, xy⟩ := onto y hy
    obtain ⟨j, hj, jx⟩ := coverX x hx
    let indices : Set ZFSet.{u} := {i | i ∈ delta ∧ ZFSet.pair i y ∈ image}
    have inhabited : indices.Nonempty := ⟨j, hj, (imageEntries j y).2 ⟨hj, hy, x, hx, jx, xy⟩⟩
    obtain ⟨i, hi, least⟩ := ZFSet.mem_wf.has_min indices inhabited
    obtain ⟨U, ip⟩ := pFunction.total hi.1
    refine ⟨i, hi.1, U, ip, (pEntries i U ip y).2 ⟨hy, ?_⟩⟩
    exact (pair_mem_ordinalFirstRelation delta Y image i y).2
      ⟨hi.2, hi.1, hy, fun k ki entry => least k ⟨ordinal.1 i hi.1 k ki, entry⟩ ki⟩
  · intro i k U V y ip kp hy hy'
    exact firstUnique i k y ((pEntries i U ip y).1 hy).2 ((pEntries k V kp y).1 hy').2
  · intro i k U V x iq kq hx hx'
    obtain ⟨A, ip⟩ := pFunction.total (qFunction.pair_source iq)
    obtain ⟨B, kp⟩ := pFunction.total (qFunction.pair_source kq)
    obtain ⟨_, y, hy, xy⟩ := (sourceEntries i A U ip iq x).1 hx
    obtain ⟨_, z, hz, xz⟩ := (sourceEntries k B V kp kq x).1 hx'
    obtain ⟨v, _, unique⟩ := function.2 x ((qEntries i U iq x).1 hx).1
    have equal : z = y := (unique z xz).trans (unique y xy).symm
    subst z
    exact firstUnique i k y ((pEntries i A ip y).1 hy).2 ((pEntries k B kp y).1 hz).2
  · intro i U V ip iq
    have hi := pFunction.pair_source ip
    have hV : V ∈ N.sets := N.transitive (N.union_mem unions (N.union_mem unions hq))
      (pair_second_mem_doubleUnion iq)
    have maps (x y : ZFSet.{u}) (hx : x ∈ V) (xy : ZFSet.pair x y ∈ f) : y ∈ U := by
      obtain ⟨_, z, hz, xz⟩ := (sourceEntries i U V ip iq x).1 hx
      obtain ⟨v, _, unique⟩ := function.2 x ((qEntries i V iq x).1 hx).1
      have equal : y = z := (unique y xy).trans (unique z xz).symm
      exact equal.symm ▸ hz
    refine ⟨?_, sourceEntries i U V ip iq, N.graphRestriction_mem unions separation hV hf, ?_, ?_⟩
    · intro y
      rw [pEntries i U ip y]
      constructor
      · rintro ⟨hy, entry⟩
        have firstEntry := (pair_mem_ordinalFirstRelation delta Y image i y).1 entry
        exact ⟨hy, ((imageEntries i y).1 firstEntry.1).2.2,
          fun k ki witness => firstEntry.2.2.2 k ki
            ((imageEntries k y).2 ⟨ordinal.1 i hi k ki, hy, witness⟩)⟩
      · rintro ⟨hy, witness, least⟩
        exact ⟨hy, (pair_mem_ordinalFirstRelation delta Y image i y).2
          ⟨(imageEntries i y).2 ⟨hi, hy, witness⟩, hi, hy,
            fun k ki entry => least k ki ((imageEntries k y).1 entry).2.2⟩⟩
    · refine ⟨?_, ?_⟩
      · intro z hz
        obtain ⟨x, hx, y, rfl, xy⟩ := mem_graphRestriction.1 hz
        exact ZFSet.pair_mem_prod.2 ⟨hx, maps x y hx xy⟩
      · intro x hx
        obtain ⟨y, xy, unique⟩ := function.2 x ((qEntries i V iq x).1 hx).1
        exact ⟨y, pair_mem_graphRestriction.2 ⟨xy, hx⟩,
          fun z xz => unique z (pair_mem_graphRestriction.1 xz).1⟩
    · intro y hy
      have firstEntry := ((pEntries i U ip y).1 hy).2
      obtain ⟨x, hx, ix, xy⟩ := ((imageEntries i y).1
        ((pair_mem_ordinalFirstRelation delta Y image i y).1 firstEntry).1).2.2
      have inV := (sourceEntries i U V ip iq x).2 ⟨ix, y, hy, xy⟩
      exact ⟨x, inV, pair_mem_graphRestriction.2 ⟨xy, inV⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPartialCoverPartitions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_partialCoverOccurrence (delta T X h i x : ZFSet.{u}) :
    ZFSet.pair i x ∈ partialCoverOccurrence delta T X h ↔
      i ∈ delta ∧ x ∈ X ∧ ∃ hi, ZFSet.pair i hi ∈ h ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi := by
  rw [partialCoverOccurrence, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, y, hy, hi, _, equal, entry, covered⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hy, hi, entry, covered⟩
  · rintro ⟨hi, hx, graph, entry, covered⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, i, hi, x, hx, graph,
      pair_second_mem_doubleUnion entry, rfl, entry, covered⟩

namespace BoundedFormula

private theorem partialCoverOccurrence_meaning {n} (z delta T X H h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (partialCoverOccurrenceFormula z delta T X H h) env ↔
      ∃ i ∈ env delta, ∃ x ∈ env X, ∃ hi ∈ env H,
        env z = ZFSet.pair i x ∧ ZFSet.pair i hi ∈ env h ∧ ∃ u ∈ env T, ZFSet.pair u x ∈ hi := by
  simp only [partialCoverOccurrenceFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (N : TransitiveGround.{u})

theorem partialCoverOccurrence_mem
    (pairing : Realize N.sets SetFormula.pairing Fin.elim0)
    (unions : Realize N.sets SetFormula.union Fin.elim0)
    (powers : Realize N.sets powerSet Fin.elim0) (separation : SeparationSchema N.sets)
    {delta T X h : ZFSet.{u}} (hDelta : delta ∈ N.sets) (hT : T ∈ N.sets)
    (hX : X ∈ N.sets) (hh : h ∈ N.sets) : partialCoverOccurrence delta T X h ∈ N.sets := by
  have hH := N.union_mem unions (N.union_mem unions hh)
  let params := extend delta (extend T (extend X (extend (⋃₀ ⋃₀ h) (extend h Fin.elim0))))
  have selected := N.bounded_separation_mem separation
    (BoundedFormula.partialCoverOccurrenceFormula 0 1 2 3 4 5) params
    (Fin.cases hDelta (Fin.cases hT (Fin.cases hX (Fin.cases hH (Fin.cases hh (fun j => Fin.elim0 j))))))
    (N.prod_mem pairing unions powers separation hDelta hX)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.partialCoverOccurrenceFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod delta X) = partialCoverOccurrence delta T X h := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, partialCoverOccurrence, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.partialCoverOccurrence_meaning _ _ _ _ _ _ _)
  exact equal ▸ selected

theorem partialCover_ordinal_partitions
    (zf : ZFRealization N.sets) {delta T X Y h f : ZFSet.{u}}
    (hDelta : delta ∈ N.sets) (ordinal : ordinalSetProperty delta)
    (hT : T ∈ N.sets) (hX : X ∈ N.sets) (hY : Y ∈ N.sets)
    (hh : h ∈ N.sets) (hf : f ∈ N.sets) (family : FunctionGraphOn delta h)
    (function : ZFSet.IsFunc X Y f) (onto : ∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f)
    (cover : ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi) :
    ∃ full ∈ N.sets, ∃ p ∈ N.sets, ∃ q ∈ N.sets,
      FunctionGraphOn delta full ∧ FunctionGraphOn delta p ∧ FunctionGraphOn delta q ∧
      (∀ i U V, ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q → U ⊆ Y ∧ V ⊆ X) ∧
      (∀ y ∈ Y, ∃ i ∈ delta, ∃ U, ZFSet.pair i U ∈ p ∧ y ∈ U) ∧
      (∀ i k U V y, ZFSet.pair i U ∈ p → ZFSet.pair k V ∈ p → y ∈ U → y ∈ V → i = k) ∧
      (∀ i k U V x, ZFSet.pair i U ∈ q → ZFSet.pair k V ∈ q → x ∈ U → x ∈ V → i = k) ∧
      ∀ i hi A U V, ZFSet.pair i hi ∈ h → ZFSet.pair i A ∈ full →
        ZFSet.pair i U ∈ p → ZFSet.pair i V ∈ q →
        (∀ x, x ∈ A ↔ x ∈ X ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi) ∧
        (∀ y, y ∈ U ↔ y ∈ Y ∧ (∃ x ∈ A, ZFSet.pair x y ∈ f) ∧
          ∀ k ∈ i, ∀ B, ZFSet.pair k B ∈ full → ¬ ∃ x ∈ B, ZFSet.pair x y ∈ f) ∧
        (∀ x, x ∈ V ↔ x ∈ A ∧ ∃ y ∈ U, ZFSet.pair x y ∈ f) ∧
        graphRestriction V f ∈ N.sets ∧ ZFSet.IsFunc V U (graphRestriction V f) ∧
        (∀ y ∈ U, ∃ x ∈ V, ZFSet.pair x y ∈ graphRestriction V f) ∧
        ∀ x ∈ V, ∃ u ∈ T, ZFSet.pair u x ∈ hi := by
  have pairing := zf.1.2.2.2.1
  have unions := zf.1.2.2.2.2.1
  have powers := zf.1.2.2.2.2.2.1
  have separation : SeparationSchema N.sets := zf.2.1
  let R := partialCoverOccurrence delta T X h
  have hR : R ∈ N.sets := N.partialCoverOccurrence_mem pairing unions powers separation hDelta hT hX hh
  have relation : R ⊆ ZFSet.prod delta X := fun _ hz => (ZFSet.mem_sep.1 hz).1
  have covering : ∀ x ∈ X, ∃ i ∈ delta, ZFSet.pair i x ∈ R := by
    intro x hx
    obtain ⟨i, hi, g, entry, covered⟩ := cover x hx
    exact ⟨i, hi, (pair_mem_partialCoverOccurrence delta T X h i x).2 ⟨hi, hx, g, entry, covered⟩⟩
  obtain ⟨p, hp, q, hq, pFunction, qFunction, bounds, coverY, disjointY, disjointX, pieces⟩ :=
    N.ordinal_image_partitions zf hDelta ordinal hX hY hR hf relation function onto covering
  let full := N.relationFiberFamily delta X R
  have hFull : full ∈ N.sets := N.relationFiberFamily_mem pairing unions powers separation hDelta hX hR
  have fullFunction : FunctionGraphOn delta full :=
    ⟨N.groundPower X, N.relationFiberFamily_function separation hDelta hX hR⟩
  have fullEntries (i A : ZFSet.{u}) (entry : ZFSet.pair i A ∈ full) (x : ZFSet.{u}) :
      x ∈ A ↔ x ∈ X ∧ ZFSet.pair i x ∈ R := by
    have equal := ((N.pair_mem_relationFiberFamily delta X R i A).1 entry).2.2
    rw [equal, mem_relationFiber]
  refine ⟨full, hFull, p, hp, q, hq, fullFunction, pFunction, qFunction,
    bounds, coverY, disjointY, disjointX, ?_⟩
  intro i hi A U V inH inFull ip iq
  obtain ⟨target, source, hRestrict, restrictFunction, restrictOnto⟩ := pieces i U V ip iq
  have original (x : ZFSet.{u}) : x ∈ A ↔ x ∈ X ∧ ∃ u ∈ T, ZFSet.pair u x ∈ hi := by
    rw [fullEntries i A inFull x]
    constructor
    · rintro ⟨hx, entry⟩
      obtain ⟨_, _, g, inH', covered⟩ := (pair_mem_partialCoverOccurrence delta T X h i x).1 entry
      have equal := family.unique inH' inH
      exact ⟨hx, equal ▸ covered⟩
    · rintro ⟨hx, covered⟩
      exact ⟨hx, (pair_mem_partialCoverOccurrence delta T X h i x).2
        ⟨family.pair_source inH, hx, hi, inH, covered⟩⟩
  have selected (x : ZFSet.{u}) : x ∈ V ↔ x ∈ A ∧ ∃ y ∈ U, ZFSet.pair x y ∈ f := by
    rw [source x]
    constructor
    · rintro ⟨entry, image⟩
      exact ⟨(fullEntries i A inFull x).2 ⟨(ZFSet.pair_mem_prod.1 (relation entry)).2, entry⟩, image⟩
    · rintro ⟨member, image⟩
      exact ⟨((fullEntries i A inFull x).1 member).2, image⟩
  refine ⟨original, ?_, selected, hRestrict, restrictFunction, restrictOnto, ?_⟩
  · intro y
    rw [target y]
    constructor
    · rintro ⟨hy, ⟨x, hx, ix, xy⟩, least⟩
      refine ⟨hy, ⟨x, (fullEntries i A inFull x).2 ⟨hx, ix⟩, xy⟩, ?_⟩
      intro k ki B inFullB witness
      obtain ⟨v, hv, vy⟩ := witness
      have coordinates := (fullEntries k B inFullB v).1 hv
      exact least k ki ⟨v, coordinates.1, coordinates.2, vy⟩
    · rintro ⟨hy, ⟨x, hx, xy⟩, least⟩
      have coordinates := (fullEntries i A inFull x).1 hx
      refine ⟨hy, ⟨x, coordinates.1, coordinates.2, xy⟩, ?_⟩
      intro k ki witness
      obtain ⟨B, inFullB⟩ := fullFunction.total (ordinal.1 i (family.pair_source inH) k ki)
      obtain ⟨v, hv, kv, vy⟩ := witness
      exact least k ki B inFullB ⟨v, (fullEntries k B inFullB v).2 ⟨hv, kv⟩, vy⟩
  · intro x hx
    exact ((original x).1 ((selected x).1 hx).1).2

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundRowCoverPartitionPrinciple
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (N : TransitiveGround.{u})

theorem function_kernel_quotient
    (zf : ZFRealization N.sets) {U V f : ZFSet.{u}}
    (hU : U ∈ N.sets) (hV : V ∈ N.sets) (hf : f ∈ N.sets)
    (function : ZFSet.IsFunc U V f)
    (onto : ∀ x ∈ V, ∃ u ∈ U, ZFSet.pair u x ∈ f) :
    ∃ R ∈ N.sets, EquivalenceRelationCode U R ∧
      (∀ u v, ZFSet.pair u v ∈ R ↔ u ∈ U ∧ v ∈ U ∧
        ∃ x ∈ V, ZFSet.pair u x ∈ f ∧ ZFSet.pair v x ∈ f) ∧
      ∃ a ∈ N.sets, InjectionCode (equivalenceClasses U R) V a ∧
        (∀ x ∈ V, ∃ C ∈ equivalenceClasses U R, ZFSet.pair C x ∈ a) ∧
        (∀ u x, ZFSet.pair u x ∈ f →
          ZFSet.pair (equivalenceClass U R u) x ∈ a) := by
  have pairing : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powers : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  let inverse := relationConverse U V f
  let R := relationCompose U V U f inverse
  have inverseGround := N.relationConverse_mem pairing unions powers zf.2.1 hU hV hf
  have hR : R ∈ N.sets :=
    N.relationCompose_mem pairing unions powers zf.2.1 hU hV hU hf inverseGround
  have entries (u v : ZFSet.{u}) : ZFSet.pair u v ∈ R ↔ u ∈ U ∧ v ∈ U ∧
      ∃ x ∈ V, ZFSet.pair u x ∈ f ∧ ZFSet.pair v x ∈ f := by
    simp only [R, inverse, pair_mem_relationCompose, pair_mem_relationConverse]
    exact ⟨fun ⟨hu, hv, x, hx, ux, _, _, vx⟩ => ⟨hu, hv, x, hx, ux, vx⟩,
      fun ⟨hu, hv, x, hx, ux, vx⟩ => ⟨hu, hv, x, hx, ux, hv, hx, vx⟩⟩
  have unique {u x y : ZFSet.{u}} (ux : ZFSet.pair u x ∈ f)
      (uy : ZFSet.pair u y ∈ f) : x = y := by
    obtain ⟨v, _, unique⟩ := function.2 u (ZFSet.pair_mem_prod.1 (function.1 ux)).1
    exact (unique x ux).trans (unique y uy).symm
  have equivalence : EquivalenceRelationCode U R := by
    refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨x, ux, _⟩ := function.2 u hu
      exact (entries u u).2 ⟨hu, hu, x, (ZFSet.pair_mem_prod.1 (function.1 ux)).2, ux, ux⟩
    · intro u v uv
      obtain ⟨hu, hv, x, hx, ux, vx⟩ := (entries u v).1 uv
      exact (entries v u).2 ⟨hv, hu, x, hx, vx, ux⟩
    · intro u v w uv vw
      obtain ⟨hu, _, x, hx, ux, vx⟩ := (entries u v).1 uv
      obtain ⟨_, hw, y, _, vy, wy⟩ := (entries v w).1 vw
      exact (entries u w).2 ⟨hu, hw, x, hx, ux, (unique vy vx) ▸ wy⟩
  let Q := equivalenceClasses U R
  let classifier := equivalenceClassifier U R
  let backward := relationConverse U Q classifier
  let a := relationCompose Q U V backward f
  have hQ : Q ∈ N.sets := N.equivalenceClasses_mem powers zf.2.1 hU hR
  have hClassifier : classifier ∈ N.sets :=
    N.equivalenceClassifier_mem pairing unions powers zf.2.1 hU hR
  have hBackward : backward ∈ N.sets :=
    N.relationConverse_mem pairing unions powers zf.2.1 hU hQ hClassifier
  have ha : a ∈ N.sets := N.relationCompose_mem pairing unions powers zf.2.1 hQ hU hV hBackward hf
  have aEntries (C x : ZFSet.{u}) : ZFSet.pair C x ∈ a ↔
      C ∈ Q ∧ x ∈ V ∧ ∃ u ∈ U, C = equivalenceClass U R u ∧ ZFSet.pair u x ∈ f := by
    change ZFSet.pair C x ∈ relationCompose Q U V backward f ↔ _
    rw [pair_mem_relationCompose]
    constructor
    · rintro ⟨hC, hx, u, hu, cu, ux⟩
      have uc := (pair_mem_relationConverse U Q classifier u C).1 cu
      have equal := (pair_mem_equivalenceClassifier U R u C).1 uc.2.2
      exact ⟨hC, hx, u, hu, equal.2, ux⟩
    · rintro ⟨hC, hx, u, hu, equal, ux⟩
      exact ⟨hC, hx, u, hu, (pair_mem_relationConverse U Q classifier u C).2
        ⟨hu, hC, (pair_mem_equivalenceClassifier U R u C).2 ⟨hu, equal⟩⟩, ux⟩
  have canonical (u x : ZFSet.{u}) (ux : ZFSet.pair u x ∈ f) :
      ZFSet.pair (equivalenceClass U R u) x ∈ a := by
    obtain ⟨hu, hx⟩ := ZFSet.pair_mem_prod.1 (function.1 ux)
    exact (aEntries _ x).2 ⟨Forcing.equivalenceClass_mem hu, hx, u, hu, rfl, ux⟩
  have injection : InjectionCode Q V a := by
    refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
    · intro C hC
      obtain ⟨u, hu, rfl⟩ := (mem_equivalenceClasses U R C).1 hC
      obtain ⟨x, ux, _⟩ := function.2 u hu
      refine ⟨x, canonical u x ux, ?_⟩
      intro y cy
      obtain ⟨_, _, v, hv, equal, vy⟩ := (aEntries _ y).1 cy
      obtain ⟨_, _, z, _, uz, vz⟩ := (entries u v).1 ((equivalence.class_eq_iff hu hv).1 equal)
      exact (unique vy vz).trans (unique uz ux)
    · intro C D x cx dx
      obtain ⟨_, hx, u, hu, rfl, ux⟩ := (aEntries C x).1 cx
      obtain ⟨_, _, v, hv, rfl, vx⟩ := (aEntries D x).1 dx
      exact (equivalence.class_eq_iff hu hv).2 ((entries u v).2 ⟨hu, hv, x, hx, ux, vx⟩)
  refine ⟨R, hR, equivalence, entries, a, ha, injection, ?_, canonical⟩
  intro x hx
  obtain ⟨u, hu, ux⟩ := onto x hx
  exact ⟨equivalenceClass U R u, Forcing.equivalenceClass_mem hu, canonical u x ux⟩

theorem partialCover_quotient_injection
    (zf : ZFRealization N.sets) {T B X Y X' Y' h f : ZFSet.{u}}
    (quotientInjection : ∀ U ∈ N.sets, ∀ Rf ∈ N.sets, ∀ Rc ∈ N.sets,
      RefinementValidityCode T U Rf Rc →
        N.groundEmbeddable (equivalenceClasses U Rc) (equivalenceClasses U Rf))
    (hT : T ∈ N.sets) (_hX : X ∈ N.sets) (_hY : Y ∈ N.sets)
    (hX' : X' ∈ N.sets) (hY' : Y' ∈ N.sets) (hh : h ∈ N.sets) (hf : f ∈ N.sets)
    (partialCode : PartialFunctionCode T B h) (function : ZFSet.IsFunc X Y f)
    (sourceSubset : X' ⊆ X) (_targetSubset : Y' ⊆ Y)
    (maps : ∀ x ∈ X', ∀ y, ZFSet.pair x y ∈ f → y ∈ Y')
    (onto : ∀ y ∈ Y', ∃ x ∈ X', ZFSet.pair x y ∈ f)
    (covered : ∀ x ∈ X', ∃ u ∈ T, ZFSet.pair u x ∈ h) :
    N.groundEmbeddable Y' X' := by
  have pairing : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powers : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  let inverse := relationConverse T X' h
  let U := relationImage X' T inverse
  have hInverse : inverse ∈ N.sets :=
    N.relationConverse_mem pairing unions powers zf.2.1 hT hX' hh
  have hU : U ∈ N.sets := N.relationImage_mem zf.2.1 hX' hT hInverse
  have uEntries (u : ZFSet.{u}) : u ∈ U ↔ u ∈ T ∧ ∃ x ∈ X', ZFSet.pair u x ∈ h := by
    simp only [U, inverse, mem_relationImage, pair_mem_relationConverse]
    exact ⟨fun ⟨hu, x, hx, _, _, ux⟩ => ⟨hu, x, hx, ux⟩,
      fun ⟨hu, x, hx, ux⟩ => ⟨hu, x, hx, hu, hx, ux⟩⟩
  let h' := ZFSet.sep (fun z => z ∈ ZFSet.prod U X') h
  have hh' : h' ∈ N.sets := N.injection_restriction_mem zf.2.1 hU hX' hh
  have hEntries (u x : ZFSet.{u}) : ZFSet.pair u x ∈ h' ↔
      ZFSet.pair u x ∈ h ∧ u ∈ U ∧ x ∈ X' := by
    exact ZFSet.mem_sep.trans (and_congr_right fun _ => ZFSet.pair_mem_prod)
  have hFunction : ZFSet.IsFunc U X' h' := by
    refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_⟩
    intro u hu
    obtain ⟨_, x, hx, ux⟩ := (uEntries u).1 hu
    exact ⟨x, (hEntries u x).2 ⟨ux, hu, hx⟩,
      fun y uy => partialCode.unique u y x ((hEntries u y).1 uy).1 ux⟩
  have hOnto : ∀ x ∈ X', ∃ u ∈ U, ZFSet.pair u x ∈ h' := by
    intro x hx
    obtain ⟨u, hu, ux⟩ := covered x hx
    have member := (uEntries u).2 ⟨hu, x, hx, ux⟩
    exact ⟨u, member, (hEntries u x).2 ⟨ux, member, hx⟩⟩
  let f' := ZFSet.sep (fun z => z ∈ ZFSet.prod X' Y') f
  have hf' : f' ∈ N.sets := N.injection_restriction_mem zf.2.1 hX' hY' hf
  have fEntries (x y : ZFSet.{u}) : ZFSet.pair x y ∈ f' ↔
      ZFSet.pair x y ∈ f ∧ x ∈ X' ∧ y ∈ Y' := by
    exact ZFSet.mem_sep.trans (and_congr_right fun _ => ZFSet.pair_mem_prod)
  have fFunction : ZFSet.IsFunc X' Y' f' := by
    refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_⟩
    intro x hx
    obtain ⟨y, xy, unique⟩ := function.2 x (sourceSubset hx)
    exact ⟨y, (fEntries x y).2 ⟨xy, hx, maps x hx y xy⟩,
      fun z xz => unique z ((fEntries x z).1 xz).1⟩
  let g := relationCompose U X' Y' h' f'
  have hg : g ∈ N.sets := N.relationCompose_mem pairing unions powers zf.2.1 hU hX' hY' hh' hf'
  have gFunction : ZFSet.IsFunc U Y' g :=
    relationCompose_function_of_subset hFunction fFunction (fun _ hx => hx)
  have gOnto : ∀ y ∈ Y', ∃ u ∈ U, ZFSet.pair u y ∈ g := by
    intro y hy
    obtain ⟨x, hx, xy⟩ := onto y hy
    obtain ⟨u, hu, ux⟩ := hOnto x hx
    exact ⟨u, hu, (pair_mem_relationCompose U X' Y' h' f' u y).2
      ⟨hu, hy, x, hx, ux, (fEntries x y).2 ⟨xy, hx, hy⟩⟩⟩
  obtain ⟨Rf, hRf, fine, fineEntries, a, ha, aInjection, _aOnto, _aCanonical⟩ :=
    N.function_kernel_quotient zf hU hX' hh' hFunction hOnto
  obtain ⟨Rc, hRc, coarse, coarseEntries, b, hb, bInjection, bOnto, _bCanonical⟩ :=
    N.function_kernel_quotient zf hU hY' hg gFunction gOnto
  have refines : Rf ⊆ Rc := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := ZFSet.mem_prod.1 (fine.shape hz)
    obtain ⟨_, _, x, hx, ux, vx⟩ := (fineEntries u v).1 hz
    obtain ⟨y, xy, _⟩ := fFunction.2 x hx
    have hy := (ZFSet.pair_mem_prod.1 (fFunction.1 xy)).2
    exact (coarseEntries u v).2 ⟨hu, hv, y, hy,
      (pair_mem_relationCompose U X' Y' h' f' u y).2 ⟨hu, hy, x, hx, ux, xy⟩,
      (pair_mem_relationCompose U X' Y' h' f' v y).2 ⟨hv, hy, x, hx, vx, xy⟩⟩
  obtain ⟨ell, hEll, ellInjection⟩ := quotientInjection U hU Rf hRf Rc hRc
    ⟨fun u hu => ((uEntries u).1 hu).1, fine, coarse, refines⟩
  have fineGround := N.equivalenceClasses_mem powers zf.2.1 hU hRf
  have coarseGround := N.equivalenceClasses_mem powers zf.2.1 hU hRc
  have imageEq : relationImage (equivalenceClasses U Rc) Y' b = Y' := by
    apply ZFSet.ext
    intro y
    rw [mem_relationImage]
    exact ⟨And.left, fun hy => ⟨hy, bOnto y hy⟩⟩
  have inverseInjection : InjectionCode Y' (equivalenceClasses U Rc)
      (relationConverse (equivalenceClasses U Rc) Y' b) := by
    have inverse := bInjection.converse_image
    rw [imageEq] at inverse
    exact inverse
  have inverseGround := N.relationConverse_mem pairing unions powers zf.2.1 coarseGround hY' hb
  let first := relationCompose Y' (equivalenceClasses U Rc) (equivalenceClasses U Rf)
    (relationConverse (equivalenceClasses U Rc) Y' b) ell
  have firstGround : first ∈ N.sets := N.relationCompose_mem pairing unions powers zf.2.1
    hY' coarseGround fineGround inverseGround hEll
  exact ⟨relationCompose Y' (equivalenceClasses U Rf) X' first a,
    N.relationCompose_mem pairing unions powers zf.2.1 hY' fineGround hX' firstGround ha,
    (inverseInjection.compose ellInjection).compose aInjection⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (N : TransitiveGround.{u})

theorem partitionPrinciple_of_rowCover_quotients
    (zf : ZFRealization N.sets) {T : ZFSet.{u}} (hT : T ∈ N.sets)
    (acwo : ∀ delta ∈ N.sets, ordinalSetProperty delta →
      ∀ z ∈ N.sets, FunctionGraphOn delta z →
        (∀ beta A, ZFSet.pair beta A ∈ z → A.Nonempty) →
        ∃ c ∈ N.sets, FunctionGraphOn delta c ∧
          ∀ beta A x, ZFSet.pair beta A ∈ z → ZFSet.pair beta x ∈ c → x ∈ A)
    (rowCover : ∀ X ∈ N.sets, ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
      ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
        (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode T (⋃₀ ⋃₀ hi) hi) ∧
        ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
          ∃ u ∈ T, ZFSet.pair u x ∈ hi)
    (quotientInjection : ∀ U ∈ N.sets, ∀ Rf ∈ N.sets, ∀ Rc ∈ N.sets,
      RefinementValidityCode T U Rf Rc →
        N.groundEmbeddable (equivalenceClasses U Rc) (equivalenceClasses U Rf)) :
    ∀ X ∈ N.sets, ∀ Y ∈ N.sets, ∀ f ∈ N.sets, ZFSet.IsFunc X Y f →
      (∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f) → N.groundEmbeddable Y X := by
  intro X hX Y hY f hf function onto
  obtain ⟨delta, hDelta, ordinal, h, hh, family, partials, cover⟩ := rowCover X hX
  obtain ⟨full, _hFull, p, hp, q, hq, fullFunction, pFunction, qFunction,
      bounds, coverY, disjointY, disjointX, pieces⟩ :=
    N.partialCover_ordinal_partitions zf hDelta ordinal hT hX hY hh hf family function onto cover
  apply N.ordinalPartition_injection_assembly zf acwo hDelta ordinal hY hX hp hq
    pFunction qFunction bounds coverY disjointY disjointX
  intro i hi U V ip iq
  obtain ⟨g, ig⟩ := family.total hi
  obtain ⟨A, iA⟩ := fullFunction.total hi
  obtain ⟨_original, _least, _source, _hRestrict, restrictFunction, restrictOnto, covered⟩ :=
    pieces i g A U V ig iA ip iq
  have hU : U ∈ N.sets := N.pair_right (N.transitive hp ip)
  have hV : V ∈ N.sets := N.pair_right (N.transitive hq iq)
  have hg : g ∈ N.sets := N.pair_right (N.transitive hh ig)
  apply N.partialCover_quotient_injection zf quotientInjection hT hX hY hV hU hg hf
    (partials i g ig) function (bounds i U V ip iq).2 (bounds i U V ip iq).1
  · intro x hx y xy
    exact (ZFSet.pair_mem_prod.1 (restrictFunction.1
      (pair_mem_graphRestriction.2 ⟨xy, hx⟩))).2
  · intro y hy
    obtain ⟨x, hx, xy⟩ := restrictOnto y hy
    exact ⟨x, hx, (pair_mem_graphRestriction.1 xy).1⟩
  · exact covered

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveOriginalRowFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)
variable {T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M c.carrier T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "upper" => SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)
local notation "inclusion" => M.refinementHistoryRowInclusion c run ordinal carrier

theorem refinementHistory_originalRowFamily_eq (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName c z) :
    Name.renamedFamily upper inclusion X valid = Name.renamedFamily c.pairEmpty id X valid := by
  have codes (tau : Name c) :
      (Name.rename upper inclusion tau).val = (Name.rename c.pairEmpty id tau).val := by
    have unchanged := M.refinementHistoryRowNameLift_val c run ordinal carrier
      (Name.rename c.pairEmpty id tau)
    change (Name.rename upper inclusion (Name.rename c.pairEmpty id tau)).val = _ at unchanged
    rw [Name.rename_comp] at unchanged
    exact unchanged
  apply ZFSet.ext
  intro z
  rw [Name.mem_renamedFamily, Name.mem_renamedFamily]
  exact ⟨fun ⟨tau, member, equal⟩ => ⟨tau, member, equal.trans (codes tau)⟩,
    fun ⟨tau, member, equal⟩ => ⟨tau, member, equal.trans (codes tau).symm⟩⟩

theorem refinementHistory_originalRowFamilySet_eq
    (one : SetMembers (M.refinementHistoryForcing c.carrier T stages history))
    (X : ZFSet.{u}) (valid : ∀ z ∈ X, IsName c z)
    (validDirect : ∀ z ∈ Name.renamedFamily upper inclusion X valid, IsName upper z)
    (validPairEmpty : ∀ z ∈ Name.renamedFamily c.pairEmpty id X valid, IsName upper z) :
    Name.familySet one (Name.renamedFamily upper inclusion X valid) validDirect =
      Name.familySet one (Name.renamedFamily c.pairEmpty id X valid) validPairEmpty := by
  apply Subtype.ext
  rw [Name.familySet_code, Name.familySet_code,
    M.refinementHistory_originalRowFamily_eq c run ordinal carrier]

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundMainFinalPartitionModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable (s : Presentation P) {G : Type v} [Group G]
variable (a : PosetAction G P) (F : Compression.RecursiveMaps.NormalSubgroupFamily G)

theorem symmetricExtension_quotient_injections
    (H : ConditionFilter P) (rowName : Name s)
    (named : ∀ tau : Fin 3 → (M.nameDomain s).names,
      (∀ i, HereditarilySymmetric a s F (tau i).val) →
      RefinementValidityCode (Name.eval {p | H.mem p} rowName)
        (Name.eval {p | H.mem p} (tau 0).val)
        (Name.eval {p | H.mem p} (tau 1).val)
        (Name.eval {p | H.mem p} (tau 2).val) →
      ∃ J ∈ (M.symmetricExtension s a F H).sets,
        InjectionCode
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 2).val))
          (equivalenceClasses (Name.eval {p | H.mem p} (tau 0).val)
            (Name.eval {p | H.mem p} (tau 1).val)) J) :
    ∀ U ∈ (M.symmetricExtension s a F H).sets,
      ∀ Rf ∈ (M.symmetricExtension s a F H).sets,
        ∀ Rc ∈ (M.symmetricExtension s a F H).sets,
          RefinementValidityCode (Name.eval {p | H.mem p} rowName) U Rf Rc →
            (M.symmetricExtension s a F H).groundEmbeddable
              (equivalenceClasses U Rc) (equivalenceClasses U Rf) := by
  intro U hU Rf hRf Rc hRc validity
  obtain ⟨u, hu, symmetricU, equalU⟩ := (M.mem_symmetricExtension s a F H U).1 hU
  obtain ⟨fine, hFine, symmetricFine, equalFine⟩ := (M.mem_symmetricExtension s a F H Rf).1 hRf
  obtain ⟨coarse, hCoarse, symmetricCoarse, equalCoarse⟩ :=
    (M.mem_symmetricExtension s a F H Rc).1 hRc
  let tau : Fin 3 → (M.nameDomain s).names := ![⟨u, hu⟩, ⟨fine, hFine⟩, ⟨coarse, hCoarse⟩]
  have symmetric : ∀ i, HereditarilySymmetric a s F (tau i).val :=
    Fin.cases symmetricU (Fin.cases symmetricFine (Fin.cases symmetricCoarse (fun i => Fin.elim0 i)))
  have actual : RefinementValidityCode (Name.eval {p | H.mem p} rowName)
      (Name.eval {p | H.mem p} (tau 0).val)
      (Name.eval {p | H.mem p} (tau 1).val)
      (Name.eval {p | H.mem p} (tau 2).val) := by
    change RefinementValidityCode (Name.eval {p | H.mem p} rowName)
      (Name.eval {p | H.mem p} u) (Name.eval {p | H.mem p} fine) (Name.eval {p | H.mem p} coarse)
    rwa [equalU, equalFine, equalCoarse]
  obtain ⟨J, hJ, injection⟩ := named tau symmetric actual
  refine ⟨J, hJ, ?_⟩
  change InjectionCode
    (equivalenceClasses (Name.eval {p | H.mem p} u) (Name.eval {p | H.mem p} coarse))
    (equivalenceClasses (Name.eval {p | H.mem p} u) (Name.eval {p | H.mem p} fine)) J at injection
  rwa [equalU, equalFine, equalCoarse] at injection

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

theorem exists_partitionPrinciple_not_choice
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    ∃ N : TransitiveGround.{u}, M.sets ⊆ N.sets ∧ ZFRealization N.sets ∧
      (∀ X ∈ N.sets, ∀ Y ∈ N.sets, ∀ f ∈ N.sets, ZFSet.IsFunc X Y f →
        (∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f) → N.groundEmbeddable Y X) ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have nodeActionGround : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have nodeOrderGround : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  have original := fulfilled.exists_rowSemanticQuotientInjectionModel
    collection infinite choice small hK standard indices labels smallD irreflexive
  obtain ⟨mu, hmu, _hmuK, cardinal, _omegaIncluded, positions, _ground, _below, valid, data⟩ := original
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  obtain ⟨hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2,
    history, hHistory, trace, chosen⟩ := data
  have topMem := c.encode_mem ⊤
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  have omega := M.omega_mem separation infinite
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared K history
  let Q := M.refinementHistoryForcing c.carrier lifted K packed
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared standard.1.1 trace
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted K packed
    historyRun.carriers standard.1.1 carrier (c.encode ⊤) topMem topRows
  let upperAction := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction geometry.actors_ground
    geometry.carrier_ground nodeOrderGround nodeActionGround nodeMaps supports hLifted hSquared omega
    valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
  let upper := SetMembers.presentation Q
  let F := a.principalSupportFamily ⊥ directed
  let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers
    standard.1.1 carrier lifted valid1
  let rowName := Name.familySet (⊤ : SetMembers Q) lifted validUpper
  obtain ⟨H, _atTop, _coded, ordinary, _symmetricGeneric, _projectedGeneric,
    includes, zf, _reflection, named⟩ := chosen (⊤ : SetMembers Q)
  let N := M.symmetricExtension upper upperAction F H
  have quotientInjection := M.symmetricExtension_quotient_injections upper upperAction F H rowName named
  have uncountable : ¬ M.groundEmbeddable columns ZFSet.omega :=
    (M.groundOmegaOne_spec pairing unions powers separation collection infinite).2.2.2
  have covers := M.semanticBinaryRow_ordinal_partial_cover a s b columns
    pairing unions powers separation collection infinite choice geometry.carrier_ground
    nodeOrderGround hColumns geometry.actors_ground nodeActionGround nodeMaps supports directed
    uncountable mu hmu cardinal.1 positions lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 K history hK hHistory standard.1.1 trace
  obtain ⟨validRows, directValid, covers⟩ := covers
  let directRowName : Name upper := Name.familySet (⊤ : SetMembers Q)
    (Name.renamedFamily upper
      (M.refinementHistoryRowInclusion c historyRun.carriers standard.1.1 carrier) T validRows) directValid
  have actualCover :
      let Trow := Name.eval {p | H.mem p} directRowName
      Trow ∈ N.sets ∧
        ∀ X ∈ N.sets, ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
          ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
            (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi) ∧
            ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
              ∃ u ∈ Trow, ZFSet.pair u x ∈ hi := covers H ordinary
  have sameRows : directRowName = rowName :=
    M.refinementHistory_originalRowFamilySet_eq c historyRun.carriers
      standard.1.1 carrier (⊤ : SetMembers Q) T validRows directValid validUpper
  rw [sameRows] at actualCover
  have acwo := fulfilled.structural_ordinal_choice collection infinite choice labels small smallD
    irreflexive columns hColumns hmu cardinal.1 valid hLifted hSquared valid1 valid2 closed1
    closed2 children1 children2 K history hK hHistory standard.1.1 trace H ordinary zf
  have notChoice := fulfilled.structural_lifted_rows_not_wellorderable_not_choice
    collection infinite choice small smallD irreflexive columns hColumns uncountable hmu
    cardinal.1 valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    K history hK hHistory standard.1.1 trace H ordinary zf
  exact ⟨N, includes, zf,
    N.partitionPrinciple_of_rowCover_quotients zf actualCover.1 acwo actualCover.2 quotientInjection,
    notChoice.2.2⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_Separation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_partitionPrinciple_without_choice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    ∃ N : TransitiveGround.{u}, M.sets ⊆ N.sets ∧ ZFRealization N.sets ∧
      (∀ X ∈ N.sets, ∀ Y ∈ N.sets, ∀ f ∈ N.sets, ZFSet.IsFunc X Y f →
        (∀ y ∈ Y, ∃ x ∈ X, ZFSet.pair x y ∈ f) → N.groundEmbeddable Y X) ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
  obtain ⟨data, ordinalC, original⟩ :=
    M.exists_groundMainFinalSupport pairing unions powers separation collection infinite choice hK standard
  let := ordinalMainIndexPreorder ordinalC
  obtain ⟨run, _indices, _profiles, _terminal, _extension, _unique, indexBound, _rank,
    i0, _zero, fulfilled, _geometryProperties⟩ := original
  exact fulfilled.exists_partitionPrinciple_not_choice collection infinite choice small hK standard
    indexBound rfl ⟨data.seed.coordinateInjection, data.seed.injection_ground, data.seed.injection_code⟩
    data.seed.dense.irrefl

theorem exists_model_partitionPrinciple_without_choice_oai
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    ∃ N : TransitiveGround.{u}, M.sets ⊆ N.sets ∧ ZFRealization N.sets ∧
      Realize N.sets partitionPrinciple Fin.elim0 ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
  obtain ⟨N, includes, zf, pp, notChoice⟩ := M.exists_partitionPrinciple_without_choice
    pairing unions powers separation collection infinite choice small hK standard
  exact ⟨N, includes, zf, (N.realize_partitionPrinciple).2 pp, notChoice⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.exists_model_partitionPrinciple_without_choice_oai.{u}
