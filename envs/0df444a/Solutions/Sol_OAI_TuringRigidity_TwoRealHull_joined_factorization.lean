-- Prove2me | solution 1 for OAI.TuringRigidity.TwoRealHull.joined_factorization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:20:38.297136+00:00
-- url     : https://prove2.me/submissions/558d80d4-fe2c-46a7-94dc-16b83de2ca17

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_OriginalRealCohenFactorization_real_factorization

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericFilterName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TransitiveNameModel
open RecursiveNames BoundedSetTheory
universe u

theorem val_genericFilterName (p : ZFSet.{u}) [Top (Conditions p)]
    (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    (genericFilterName p).val G = genericFilterSet p G := by
  apply ZFSet.ext; intro x
  simp only [genericFilterName,Name.mem_val,Name.val_check G hG,mem_genericFilterSet,id_eq]

theorem eval_filterCodeFormula (z p f r : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    filterCodeFormula.Eval (cons z (cons p (cons f (cons r e)))) ↔
      ∃ x ∈ p, ∃ v ∈ r, ZFSet.pair x v ∈ f ∧ z = ZFSet.pair v x := by
  simp only [filterCodeFormula,Formula.Eval,Formula.eval_pairMem,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem mem_filterCode (p f z : ZFSet.{u}) :
    z ∈ filterCode p f ↔ ∃ x ∈ p, ∃ v, ZFSet.pair x v ∈ f ∧ z = ZFSet.pair v x := by
  rw [filterCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,hx,v,_,hv,hz⟩; exact ⟨x,hx,v,hv,hz⟩
  · rintro ⟨x,hx,v,hv,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,x,hx,rfl⟩,x,hx,v,hr,hv,rfl⟩

theorem filterCode_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {p f : ZFSet.{u}} (hp : p ∈ M) (hf : f ∈ M) : filterCode p f ∈ M := by
  have hr := iterUnion_mem M hM hU hf 2
  let e := cons p (cons f (cons (iterUnion 2 f) (fun _ => p)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hp
    rcases i with _|i; exact hf
    rcases i with _|i; exact hr
    exact hp
  have hs := sep_mem M hM hS filterCodeFormula e he
    (product_mem M hM hP hU hPow hS hr hp)
  have heq : ZFSet.sep (fun z => filterCodeFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) p) = filterCode p f := by
    apply ZFSet.ext; intro z
    simp only [filterCode,ZFSet.mem_sep]
    exact and_congr_right (fun _ => eval_filterCodeFormula z p f _ _)
  exact heq ▸ hs

theorem encode_genericFilterName (p d r f : ZFSet.{u}) [Top (Conditions p)]
    (hsub : p ⊆ d) (hf : CheckGraph d r f (label p ⊤)) :
    (genericFilterName p).encode (label p) = filterCode p f := by
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,mem_filterCode]
  constructor
  · rintro ⟨q,hq⟩
    have hx := hsub (label_mem p q)
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 (label p q) hx
    have he := hf.correct _ hx v hv hfv
    refine ⟨label p q,label_mem p q,v,hfv,?_⟩
    simpa only [genericFilterName,id_eq,encode_check,he] using hq.symm
  · rintro ⟨x,hx,v,hfv,hz⟩
    obtain ⟨q,rfl⟩ := label_surjective p hx
    have hfr : FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
    have he := hf.correct _ (hsub hx) v (hfr.value_mem hfv) hfv
    exact ⟨q,by simpa only [genericFilterName,id_eq,encode_check,he] using hz.symm⟩

theorem genericFilterName_mem (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) : genericFilterName p ∈ names M p := by
  obtain ⟨d,hdM,hd,hpd⟩ := internal_transitive_container M hM hP hU hS hR hI hp
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hPow hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label p ⊤) hM hP hU hPow hS hR
    hdM hqM (hM p hp _ (label_mem p ⊤)) hd hq p hpd
  have hsub : p ⊆ hull d q p := fun x hx =>
    hull_transitive d q p hd p (self_mem_hull d q hpd) x hx
  change (genericFilterName p).encode (label p) ∈ M
  rw [encode_genericFilterName p _ _ f hsub hfg]
  exact filterCode_mem M hM hP hU hPow hS hp hf

theorem genericFilterSet_mem_extension (M p : ZFSet.{u}) [Top (Conditions p)]
    (hM : Transitive M) (hP : Pairing M) (hU : BoundedSetTheory.Union M)
    (hPow : PowerSet M) (hS : Separation M) (hR : SigmaReplacement M)
    (hI : Infinity M) (hp : p ∈ M) (G : Set (Conditions p)) (hG : ⊤ ∈ G) :
    genericFilterSet p G ∈ genericExtensionSet M p G :=
  (mem_extensionSet M p G _).mpr ⟨genericFilterName p,
    genericFilterName_mem M p hM hP hU hPow hS hR hI hp,val_genericFilterName p G hG⟩

end TuringRigidity.TransitiveNameModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealGeneratedModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RealGeneratedModel
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanSyntax InternalBooleanBits
open InternalGeneratedAlgebra InternalProjectedGeneric InternalBooleanTop

theorem mem_hull (M X z : ZFSet.{0}) (h : ∃ N, Contains M X N) :
    z ∈ hull M X ↔ ∀ N, Contains M X N → z ∈ N := by
  rw [hull,dite_eq_left h,ZFSet.mem_sep]
  exact ⟨fun hz => hz.2,fun hz => ⟨hz h.choose h.choose_spec,hz⟩⟩

theorem hull_eq_of_least (M X H : ZFSet.{0}) (hH : Contains M X H)
    (hleast : ∀ N, Contains M X N → H ⊆ N) : hull M X = H := by
  apply ZFSet.ext; intro z
  rw [mem_hull M X z ⟨H,hH⟩]
  exact ⟨fun hz => hz H hH,fun hz N hN => hleast N hN hz⟩

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  codeOrder codePreorder

end TuringRigidity.RealGeneratedModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RegularTreeExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RegularTreeExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open RegularTreeRecovery InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem extension_properties (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    let N := genericExtensionSet M c G.carrier
    Transitive N ∧ SourceT N ∧ M ⊆ N ∧ genericFilterSet c G.carrier ∈ N := by
  let _ : Top (Conditions c) := ⟨Classical.choose G.nonempty⟩
  have ht : ⊤ ∈ G.carrier := Classical.choose_spec G.nonempty
  exact ⟨genericExtensionSet_transitive M c hM G.carrier,
    extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
      (InternalCollapse.orderSet_pair c) G hG ht,
    ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht,
    genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht⟩

end TuringRigidity.RegularTreeExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_TwoRealHull
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.TwoRealHull
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RealGeneratedModel CohenColumnRealName InternalCountableOrdinals
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem contains_join_iff (M : ZFSet.{0}) (X Y : Oracle)
    (hN : Contains M (realCode X) (RealGeneratedModel.hull M (realCode X))) (W : ZFSet.{0}) :
    Contains M (realCode (join X Y)) W ↔
      Contains (RealGeneratedModel.hull M (realCode X)) (realCode Y) W := by
  constructor
  · rintro ⟨hW,hTW,hMW,hXY⟩
    have hX := sourceT_real_lower W hW hTW hXY (reduces_join_left X Y)
    have hY := sourceT_real_lower W hW hTW hXY (reduces_join_right X Y)
    refine ⟨hW,hTW,?_,hY⟩
    intro z hz
    exact ((mem_hull M (realCode X) z ⟨_,hN⟩).mp hz) W ⟨hW,hTW,hMW,hX⟩
  · rintro ⟨hW,hTW,hNW,hY⟩
    exact ⟨hW,hTW,fun z hz => hNW (hN.2.2.1 hz),
      sourceT_real_join W hW hTW (hNW hN.2.2.2) hY⟩

theorem hull_join (M : ZFSet.{0}) (X Y : Oracle)
    (hN : Contains M (realCode X) (RealGeneratedModel.hull M (realCode X)))
    (hJ : Contains M (realCode (join X Y)) (RealGeneratedModel.hull M (realCode (join X Y)))) :
    RealGeneratedModel.hull (RealGeneratedModel.hull M (realCode X)) (realCode Y) =
      RealGeneratedModel.hull M (realCode (join X Y)) := by
  apply hull_eq_of_least _ _ _ ((contains_join_iff M X Y hN _).mp hJ)
  intro W hW z hz
  exact ((mem_hull M (realCode (join X Y)) z ⟨_,hJ⟩).mp hz) W
    ((contains_join_iff M X Y hN W).mpr hW)

theorem joined_factorization_oai (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X Y : Oracle)
    (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) :
    let N := RealGeneratedModel.hull M (realCode X)
    let H := RealGeneratedModel.hull N (realCode Y)
    Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧
      ∃ U : GenericFilter (Conditions (poset K)), GroundGeneric H U ∧
        genericExtensionSet H (poset K) U.carrier = genericExtensionSet M (poset K) G.carrier := by
  dsimp only
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (CohenGroundPoset.conditions_mem M _ hM hT
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
        hK.2.1 (sourceT_omega_mem M hM hT))) G hG
  obtain ⟨hN,_,_,_⟩ := OriginalRealCohenFactorization.real_factorization M K hM hT hK
    G hG (realCode X) hX (realCode_subset X)
  obtain ⟨hJ,U,hU,hUE⟩ := OriginalRealCohenFactorization.real_factorization M K hM hT hK
    G hG (realCode (join X Y)) (sourceT_real_join _ hE hTE hX hY) (realCode_subset _)
  have hNJ := (contains_join_iff M X Y hN _).mp hJ
  have he := hull_join M X Y hN hJ
  rw [←he] at hNJ hU hUE
  exact ⟨hN,hNJ,U,hU,hUE⟩

end TuringRigidity.TwoRealHull

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.TwoRealHull.joined_factorization_oai := @OAI.TuringRigidity.TwoRealHull.joined_factorization_oai
