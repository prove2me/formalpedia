-- Prove2me | solution 1 for OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:11:28.902657+00:00
-- url     : https://prove2.me/submissions/a4837d28-612f-446b-857f-dab89f1e6f7b

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_GroundPrefixOverwrite_overwrite_generic
import Theorems.Thm_OAI_TuringRigidity_InternalCohen_prefix_extension_eq_hull
import Theorems.Thm_OAI_TuringRigidity_RealHullIteration_exists_iterated_pair

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformPrograms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformPrograms
open Encodable

variable {X : Type*} {O : X → ℕ →. ℕ}

theorem oracle_free {f : ℕ →. ℕ} (hf : Nat.RecursiveIn ∅ f) :
    ∃ p : OracleCode, ∀ g, OracleCode.eval g p = f := by
  induction hf with
  | zero => exact ⟨.zero,fun _ => rfl⟩
  | succ => exact ⟨.succ,fun _ => rfl⟩
  | left => exact ⟨.left,fun _ => rfl⟩
  | right => exact ⟨.right,fun _ => rfl⟩
  | oracle f hf => simp at hf
  | pair _ _ hc hd =>
    obtain ⟨c,hc⟩ := hc; obtain ⟨d,hd⟩ := hd
    exact ⟨.pair c d,fun g => by simp only [OracleCode.eval,hc g,hd g]; rfl⟩
  | comp _ _ hc hd =>
    obtain ⟨c,hc⟩ := hc; obtain ⟨d,hd⟩ := hd
    exact ⟨.comp c d,fun g => by simp only [OracleCode.eval,hc g,hd g]; rfl⟩
  | prec _ _ hc hd =>
    obtain ⟨c,hc⟩ := hc; obtain ⟨d,hd⟩ := hd
    exact ⟨.prec c d,fun g => by simp only [OracleCode.eval,hc g,hd g]; rfl⟩
  | rfind _ hc =>
    obtain ⟨c,hc⟩ := hc
    exact ⟨.find c,fun g => by simp only [OracleCode.eval,hc g]; rfl⟩

theorem primrec {f : ℕ → ℕ} (hf : Primrec f) : Runs O (fun _ n => Part.some (f n)) := by
  obtain ⟨p,hp⟩ := oracle_free (RecursiveIn.iff_nat.mp (hf.computableIn (O := ∅)))
  exact ⟨p,fun x => hp (O x)⟩

theorem query : Runs O O := ⟨.query,fun _ => rfl⟩

theorem Runs.of_eq {f g : X → ℕ →. ℕ} (hf : Runs O f) (h : ∀ x n, f x n = g x n) : Runs O g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun x => (hp x).trans (funext (h x))⟩

theorem Runs.pair {f g : X → ℕ →. ℕ} (hf : Runs O f) (hg : Runs O g) :
    Runs O (fun x n => Nat.pair <$> f x n <*> g x n) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨.pair p q,fun x => by simp only [OracleCode.eval,hp x,hq x]; rfl⟩

theorem Runs.comp {f g : X → ℕ →. ℕ} (hf : Runs O f) (hg : Runs O g) :
    Runs O (fun x n => g x n >>= f x) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨.comp p q,fun x => by simp only [OracleCode.eval,hp x,hq x]; rfl⟩

theorem total_comp {f g : X → ℕ → ℕ}
    (hf : Runs O (fun x n => Part.some (f x n)))
    (hg : Runs O (fun x n => Part.some (g x n))) :
    Runs O (fun x n => Part.some (f x (g x n))) := by
  simpa using hf.comp hg

theorem total_pair {f g : X → ℕ → ℕ}
    (hf : Runs O (fun x n => Part.some (f x n)))
    (hg : Runs O (fun x n => Part.some (g x n))) :
    Runs O (fun x n => Part.some (Nat.pair (f x n) (g x n))) := by
  simpa [Seq.seq] using hf.pair hg

end TuringRigidity.UniformPrograms

end OAI
end

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenConditions
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing

theorem conditions_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) : conditions ∈ M := by
  obtain ⟨c,hc,hdef⟩ := conditions_exist_absolute_without_choice M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT)
    (alphabet_mem M hM hT)
  have he : c = conditions := ZFSet.ext (fun p => (hdef p).trans (mem_conditions p).symm)
  exact he ▸ hc

attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

end TuringRigidity.InternalCohen

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPrefixHull
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem prefix_extension_eq_of_hull (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A B : Oracle)
    (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A)))
    (hB : AtomicForcing.GroundGeneric M (pushFilter (realFilter B)))
    (he : RealGeneratedModel.hull M (realCode A) = RealGeneratedModel.hull M (realCode B)) :
    genericExtensionSet M conditions (pushFilter (realFilter A)).carrier =
      genericExtensionSet M conditions (pushFilter (realFilter B)).carrier := by
  rw [prefix_extension_eq_hull M hM hT A hA,prefix_extension_eq_hull M hM hT B hB,he]

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteOverwrite
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteOverwrite
open UniformPrograms

theorem overwrite_below (s : List Bool) (A : Oracle) (n : ℕ) (hn : n < s.length) :
    overwrite s A n = s.getD n false := by simp [overwrite,hn]

theorem overwrite_program (s : List Bool) :
    Runs oracleFunction (fun A => oracleFunction (overwrite s A)) := by
  have hp : Primrec (fun z : ℕ =>
      if (Nat.unpair z).1 < s.length then
        (if s.getD (Nat.unpair z).1 false then 1 else 0) else (Nat.unpair z).2) :=
    Primrec.ite (Primrec.nat_lt.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const s.length))
      (Primrec.ite (Primrec.eq.comp ((Primrec.list_getD false).comp (Primrec.const s)
        (Primrec.fst.comp Primrec.unpair)) (Primrec.const true)) (Primrec.const 1) (Primrec.const 0))
      (Primrec.snd.comp Primrec.unpair)
  have hq : Runs oracleFunction (fun A n => Part.some (if A n then 1 else 0)) := query
  apply (_root_.OAI.TuringRigidity.UniformPrograms.total_comp (primrec hp) (_root_.OAI.TuringRigidity.UniformPrograms.total_pair (primrec Primrec.id) hq)).of_eq
  intro A n
  simp only [Nat.unpair_pair,oracleFunction,overwrite,id_eq]
  split <;> rfl

theorem overwrite_reduces (s : List Bool) (A : Oracle) : Reduces (overwrite s A) A := by
  obtain ⟨p,hp⟩ := overwrite_program s
  exact (OracleCode.turingReducible_iff_exists_code _ _).mpr ⟨p,hp A⟩

theorem restore_initial (s : List Bool) (A : Oracle) :
    overwrite (FiniteShuffle.initial A s.length) (overwrite s A) = A := by
  funext n
  by_cases hn : n < s.length
  · rw [overwrite_below _ _ _ (by simpa using hn),FiniteShuffle.prefix_getD _ _ _ hn]
  · simp [overwrite,hn]

theorem degree_overwrite (s : List Bool) (A : Oracle) : degree (overwrite s A) = degree A := by
  apply (degree_eq_iff _ _).mpr
  exact ⟨overwrite_reduces s A,by
    simpa only [restore_initial] using
      overwrite_reduces (FiniteShuffle.initial A s.length) (overwrite s A)⟩

end TuringRigidity.FiniteOverwrite

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GroundPrefixOverwrite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.GroundPrefixOverwrite
open TransitiveNameModel BoundedSetTheory CountableForcing CohenColumnRealName
open FiniteOverwrite
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem overwrite_realizes (s : List Bool) (A : Oracle) :
    ShuffleRequirements.Realizes s (overwrite s A) :=
  fun n hn => (overwrite_below s A n hn).symm

end TuringRigidity.GroundPrefixOverwrite

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteOverwriteHull
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteOverwriteHull
open TransitiveNameModel BoundedSetTheory RealGeneratedModel FiniteOverwrite
open CountableForcing InternalCohen CohenBorelForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem contains_iff_of_degree (M N : ZFSet.{0}) (A B : Oracle)
    (he : degree A = degree B) : Contains M (realCode A) N ↔ Contains M (realCode B) N := by
  obtain ⟨hAB,hBA⟩ := (degree_eq_iff A B).mp he
  constructor
  · rintro ⟨hN,hT,hMN,hA⟩
    exact ⟨hN,hT,hMN,sourceT_real_lower N hN hT hA hBA⟩
  · rintro ⟨hN,hT,hMN,hB⟩
    exact ⟨hN,hT,hMN,sourceT_real_lower N hN hT hB hAB⟩

theorem hull_eq_of_degree (M : ZFSet.{0}) (A B : Oracle)
    (he : degree A = degree B) : RealGeneratedModel.hull M (realCode A) = RealGeneratedModel.hull M (realCode B) := by
  classical
  have hc := fun N => contains_iff_of_degree M N A B he
  by_cases hA : ∃ N, Contains M (realCode A) N
  · have hB : ∃ N, Contains M (realCode B) N :=
      ⟨hA.choose,(hc _).mp hA.choose_spec⟩
    apply ZFSet.ext
    intro z
    rw [mem_hull M _ z hA,mem_hull M _ z hB]
    exact ⟨fun h N hN => h N ((hc N).mpr hN),fun h N hN => h N ((hc N).mp hN)⟩
  · have hB : ¬ ∃ N, Contains M (realCode B) N := fun h =>
      hA ⟨h.choose,(hc _).mpr h.choose_spec⟩
    simp only [RealGeneratedModel.hull,dite_eq_right hA,dite_eq_right hB]

theorem overwrite_hull (M : ZFSet.{0}) (s : List Bool) (A : Oracle) :
    RealGeneratedModel.hull M (realCode (overwrite s A)) = RealGeneratedModel.hull M (realCode A) :=
  hull_eq_of_degree M _ _ (degree_overwrite s A)

theorem overwrite_extension (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A)))
    (s : List Bool) :
    genericExtensionSet M conditions (pushFilter (realFilter (overwrite s A))).carrier =
      genericExtensionSet M conditions (pushFilter (realFilter A)).carrier := by
  exact prefix_extension_eq_of_hull M hM hT _ _
    (GroundPrefixOverwrite.overwrite_generic M hM hT A hA s) hA (overwrite_hull M s A)

end TuringRigidity.FiniteOverwriteHull

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealHullIteration
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RealHullIteration
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals RealGeneratedModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_iterated_prefix_pair_oai (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X Y : Oracle)
    (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (hY : realCode Y ∈ genericExtensionSet M (poset K) G.carrier) (s t : List Bool) :
    let N := RealGeneratedModel.hull M (realCode X)
    let H := RealGeneratedModel.hull N (realCode Y)
    Contains M (realCode X) N ∧ Contains N (realCode Y) H ∧ ∃ L R : Oracle,
      realCode L ∈ genericExtensionSet M (poset K) G.carrier ∧
      realCode R ∈ genericExtensionSet M (poset K) G.carrier ∧
      GroundGeneric H (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) ∧
      GroundGeneric (genericExtensionSet H InternalCohen.conditions
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)).carrier)
        (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) ∧
      ShuffleRequirements.Realizes s L ∧ ShuffleRequirements.Realizes t R := by
  dsimp only
  obtain ⟨hN,hH,L,R,hLE,hRE,hL,hR⟩ := exists_iterated_pair M K hM hT hK G hG X Y hX hY
  let H := RealGeneratedModel.hull (RealGeneratedModel.hull M (realCode X)) (realCode Y)
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (CohenGroundPoset.conditions_mem M _ hM hT
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
        hK.2.1 (sourceT_omega_mem M hM hT))) G hG
  obtain ⟨hF,hTF,_,_⟩ := RegularTreeExtension.extension_properties H InternalCohen.conditions
    hH.1 hH.2.1 (InternalCohen.conditions_mem H hH.1 hH.2.1)
    (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) hL
  have hLs := GroundPrefixOverwrite.overwrite_generic H hH.1 hH.2.1 L hL s
  have hRt := GroundPrefixOverwrite.overwrite_generic _ hF hTF R hR t
  have he := FiniteOverwriteHull.overwrite_extension H hH.1 hH.2.1 L hL s
  refine ⟨hN,hH,FiniteOverwrite.overwrite s L,FiniteOverwrite.overwrite t R,
    sourceT_real_lower _ hE hTE hLE (FiniteOverwrite.overwrite_reduces s L),
    sourceT_real_lower _ hE hTE hRE (FiniteOverwrite.overwrite_reduces t R),
    hLs,?_,GroundPrefixOverwrite.overwrite_realizes s L,GroundPrefixOverwrite.overwrite_realizes t R⟩
  rw [he]
  exact hRt

end TuringRigidity.RealHullIteration

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair_oai := @OAI.TuringRigidity.RealHullIteration.exists_iterated_prefix_pair_oai
