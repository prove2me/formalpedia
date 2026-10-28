-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:17:29.017375+00:00
-- url     : https://prove2.me/submissions/3aa4ed32-900b-4a2b-bbd1-127d11228322

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_uniform_ordinal_definition_symmetric

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CountableForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountableForcing
open Set

theorem exists_generic {P : Type*} [Preorder P] (D : ℕ → Set P)
    (hD : ∀ n, Dense (D n)) (p : P) :
    ∃ G : GenericFilter P, p ∈ G.carrier ∧ GenericFor D G := by
  classical
  choose step hs using hD
  let seq : ℕ → P := fun n => Nat.rec p (fun n q => step n q) n
  have hseq (n : ℕ) : seq (n+1) ≤ seq n ∧ seq (n+1) ∈ D n := hs n (seq n)
  have hanti : Antitone seq := antitone_nat_of_succ_le (fun n => (hseq n).1)
  let G : GenericFilter P := {
    carrier := {q | ∃ n, seq n ≤ q}
    nonempty := ⟨p,0,le_rfl⟩
    upper := fun hpq ⟨n,hn⟩ => ⟨n,hn.trans hpq⟩
    directed := by
      rintro q r ⟨n,hn⟩ ⟨m,hm⟩
      exact ⟨seq (max n m),⟨max n m,le_rfl⟩,
        (hanti (le_max_left _ _)).trans hn,(hanti (le_max_right _ _)).trans hm⟩ }
  exact ⟨G,⟨0,le_rfl⟩,fun n => ⟨seq (n+1),⟨n+1,le_rfl⟩,(hseq n).2⟩⟩

end TuringRigidity.CountableForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenSymmetry
open Set CountableForcing

variable {ι : Type*}

theorem merge_le_left (p q : Condition ι) : merge p q ≤ p := by
  intro i b hb
  simp [merge,hb]

theorem merge_le_right {p q : Condition ι} (h : Compatible p q) : merge p q ≤ q := by
  intro i b hb
  cases hp : p.val i with
  | none => simp [merge,hp,hb]
  | some a => simpa [merge,hp] using congrArg some (h i a b hp hb)

theorem matching_compatible (p q : Condition ι) : Compatible (flip (matchingMask p q) p) q := by
  intro i a b ha hb
  cases hp : p.val i with
  | none => simp [flip,hp] at ha
  | some c =>
    cases c <;> cases b <;> simpa [flip,matchingMask,hp,hb] using ha.symm

end TuringRigidity.CohenSymmetry

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformOracle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open Encodable

namespace UniformOracle
variable {O : Set (ℕ →. ℕ)}

private theorem flag_primrec : Primrec flag := by
  apply (Primrec.cond (Primrec.option_isSome.comp (Primrec.option_getD_default.comp (Primrec.decode (α := Option ℕ))))
    (Primrec.const 0) (Primrec.const 1)).of_eq
  intro n
  change (cond ((decode (α := Option ℕ) n).getD none).isSome 0 1) = _
  cases hh : ((decode (α := Option ℕ) n).getD none).isSome <;> simp only [flag,hh] <;> rfl
private theorem answer_primrec : Primrec answer :=
  Primrec.option_getD_default.comp (Primrec.option_getD_default.comp Primrec.decode)

theorem total_search {E : ℕ → ℕ → Option ℕ}
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E (Nat.unpair z).1 (Nat.unpair z).2))))
    (f : ℕ → ℕ) (hsound : ∀ n m a, a ∈ E n m → a = f n)
    (hcomplete : ∀ n, ∃ m a, a ∈ E n m) :
    Nat.RecursiveIn O (fun n => Part.some (f n)) := by
  have hflag := total_comp (total_primrec flag_primrec) hE
  have hfind := Nat.RecursiveIn.rfind hflag
  have hpair := Nat.RecursiveIn.pair (total_primrec Primrec.id) hfind
  have hrun := Nat.RecursiveIn.comp (total_primrec answer_primrec)
    (Nat.RecursiveIn.comp hE hpair)
  apply hrun.of_eq_tot
  intro n
  have hex : ∃ m, (E n m).isSome = true := by
    obtain ⟨m,a,ha⟩ := hcomplete n
    exact ⟨m, Option.isSome_iff_exists.mpr ⟨a,ha⟩⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hm
  have hval : a = f n := hsound n m a ha
  have hmem : m ∈ Nat.rfind (fun k =>
      (fun v : ℕ => decide (v=0)) <$> Part.some (flag (encode (E n k)))) := by
    apply Nat.mem_rfind.mpr
    constructor
    · simp [flag, m, hm]
    · intro k hk
      have hk' : (E n k).isSome = false := Bool.eq_false_iff.mpr (Nat.find_min hex hk)
      simp [flag, hk']
  apply Part.mem_bind_iff.mpr
  refine ⟨encode (E n m), ?_, ?_⟩
  · apply Part.mem_bind_iff.mpr
    refine ⟨Nat.pair n m, ?_, ?_⟩
    · simp only [Seq.seq]
      apply Part.mem_bind_iff.mpr
      refine ⟨Nat.pair n, (Part.mem_map_iff _).mpr ⟨n,Part.mem_some _,rfl⟩, ?_⟩
      exact (Part.mem_map_iff _).mpr ⟨m,by simpa only [Nat.unpair_pair] using hmem,rfl⟩
    · simp
  · have hea : E n m = some a := Option.mem_def.mp ha
    apply Part.mem_some_iff.mpr
    rw [hea]
    simpa only [answer, Encodable.encodek, Option.getD_some] using hval.symm

theorem trial_recursive (g : ℕ → ℕ) (c : Nat.Partrec.Code) :
    Nat.RecursiveIn {fun n => Part.some (g n)}
      (fun z => Part.some (encode (trial g c (Nat.unpair z).1 (Nat.unpair z).2))) := by
  have hm := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hk := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hn := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp Primrec.unpair)
  have hp := total_comp (prefix_recursive g) hm
  have he := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.encode.comp
    (Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.unpair).pair (Primrec.const c)).pair
        (Primrec.snd.comp Primrec.unpair))))
  exact (total_comp he (total_pair hk (total_pair hp hn))).of_eq (fun z => by
    simp [trial])

end UniformOracle
end TuringRigidity

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

theorem eval_congr (φ : BoundedSetTheory.Formula) (e e' : ℕ → ZFSet.{u})
    (h : ∀ i, i < bound φ → e i = e' i) : φ.Eval e ↔ φ.Eval e' := by
  induction φ generalizing e e' with
  | equal i j => simp only [Formula.Eval,h i (by simp [bound]),h j (by simp [bound])]
  | member i j => simp only [Formula.Eval,h i (by simp [bound]),h j (by simp [bound])]
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e e' (fun i hi => h i (by simp only [bound]; omega)))
      (ihψ e e' (fun i hi => h i (by simp only [bound]; omega)))
  | neg φ ih => exact not_congr (ih e e' h)
  | existsMem i φ ih =>
    have hei := h i (by simp only [bound]; omega)
    simp only [Formula.Eval,hei]
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    apply ih
    intro n hn
    cases n with
    | zero => rfl
    | succ n => exact h n (by simp only [bound]; omega)

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenBitFlip
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenBitFlip
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem flipMatches_graph_iff (A B : ZFSet.{0})
    (p q : Condition (Conditions A)) :
    FlipMatches A B (graph A p) (graph A q) ↔ q = flip (mask A B) p := by
  classical
  constructor
  · intro h
    apply Condition.ext; funext i
    apply Option.ext; intro b
    have hh := h (label A i) (label_mem A i)
    simp only [pair_mem_graph] at hh
    cases b <;> cases hp : p.val i <;>
      by_cases hi : label A i ∈ B <;>
      simp_all [CohenSymmetry.flip,mask]
  · rintro rfl x hx
    obtain ⟨i,rfl⟩ := label_surjective A hx
    simp only [pair_mem_graph]
    cases hp : p.val i <;> by_cases hi : label A i ∈ B <;>
      simp_all [CohenSymmetry.flip,mask]

theorem pair_flipGraph (A B p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ flipGraph A B ↔
      p ∈ conditions A ∧ q ∈ conditions A ∧ FlipMatches A B p q := by
  simp only [flipGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,h⟩
  · rintro ⟨hp,hq,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,h⟩

theorem flipGraph_mem (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) : flipGraph A B ∈ M := by
  have hc := conditions_mem M A hM hT hA
  have hb (b : Bool) : bitSet b ∈ M :=
    hM _ (InternalCohen.alphabet_mem M hM hT) _ ((mem_alphabet _).mpr ⟨b,rfl⟩)
  let e := cons (conditions A) (cons A (cons B (cons (bitSet false) (fun _ => bitSet true))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact hc; exact hA; exact hB; exact hb false; exact hb true
  simpa only [flipGraph,flipMatchesFormula,FlipMatches,Formula.eval_allMem,Formula.eval_iff,
    Formula.eval_pairMem,Formula.eval_disj,Formula.Eval,Formula.eval_orderedPair,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0)
        (flipMatchesFormula 4 5 1 0 6 7)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hc hc)

theorem flipGraph_spec (A B : ZFSet.{0})
    (p q : Conditions (conditions A)) :
    ZFSet.pair (label _ p) (label _ q) ∈ flipGraph A B ↔ q = flipIso A B p := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv A).surjective q
  rw [pair_flipGraph,and_iff_right (label_mem _ _),and_iff_right (label_mem _ _)]
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv A q) = graph A q := label_encode A q
  rw [hp,hq,flipMatches_graph_iff]
  change q = flip (mask A B) p ↔ conditionEquiv A q =
    conditionEquiv A (flip (mask A B) ((conditionEquiv A).symm (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply]
  exact (conditionEquiv A).injective.eq_iff.symm

end TuringRigidity.InternalCohenBitFlip

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenHomogeneity
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenBitFlip
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem matchingSet_mem (M A p q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hp : p ∈ M) (hq : q ∈ M) : matchingSet A p q ∈ M := by
  have hb : bitSet true ∈ M :=
    hM _ (InternalCohen.alphabet_mem M hM hT) _ ((mem_alphabet _).mpr ⟨true,rfl⟩)
  let e := cons p (cons q (fun _ => bitSet true))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hp; exact hq; exact hb
  simpa only [matchingSet,matchingFormula,Formula.eval_disj,Formula.Eval,Formula.eval_pairMem,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (matchingFormula 0 1 2 3) e he hA

theorem mask_matchingSet (A : ZFSet.{0}) (p q : Condition (Conditions A)) :
    mask A (matchingSet A (graph A p) (graph A q)) = matchingMask p q := by
  classical
  funext i
  have hm : label A i ∈ matchingSet A (graph A p) (graph A q) ↔
      (p.val i = some true ∧ q.val i ≠ some true) ∨
      (p.val i ≠ some true ∧ q.val i = some true) := by
    simp only [matchingSet,ZFSet.mem_sep,label_mem,true_and,pair_mem_graph]
  simp only [mask,hm,matchingMask]
  cases hp : p.val i with
  | none => cases hq : q.val i with
    | none => rfl
    | some b => cases b <;> decide
  | some a => cases hq : q.val i with
    | none => cases a <;> decide
    | some b => cases a <;> cases b <;> decide

theorem matching_common_extension (A : ZFSet.{0}) (p q : Conditions (conditions A)) :
    ∃ r, r ≤ flipIso A (matchingSet A (label _ p) (label _ q)) p ∧ r ≤ q := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv A).surjective q
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv A q) = graph A q := label_encode A q
  rw [hp,hq]
  refine ⟨conditionEquiv A (merge (flip (matchingMask p q) p) q),?_,
    (conditionEquiv A).monotone (merge_le_right (matching_compatible p q))⟩
  change conditionEquiv A (merge (flip (matchingMask p q) p) q) ≤
    conditionEquiv A (flip (mask A (matchingSet A (graph A p) (graph A q)))
      ((conditionEquiv A).symm (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply,mask_matchingSet]
  exact (conditionEquiv A).monotone (merge_le_left _ _)

theorem internally_homogeneous (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (p q : Conditions (conditions A)) :
    ∃ w ∈ M, ∃ e : Conditions (conditions A) ≃o Conditions (conditions A),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = e s) ∧
      ∃ r, r ≤ e p ∧ r ≤ q := by
  let B := matchingSet A (label _ p) (label _ q)
  have hc := conditions_mem M A hM hT hA
  have hB : B ∈ M := matchingSet_mem M A _ _ hM hT hA
    (hM _ hc _ (label_mem _ p)) (hM _ hc _ (label_mem _ q))
  exact ⟨flipGraph A B,flipGraph_mem M A B hM hT hA hB,flipIso A B,
    flipGraph_spec A B,matching_common_extension A p q⟩

end TuringRigidity.InternalCohenBitFlip

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TableIndices
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TableIndices
open Encodable UniformOracle CommonIdeal

theorem represents_reduces {Y A : Oracle} {d : Nat.Partrec.Code} (h : Represents Y d A) :
    Reduces A Y := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (trial_recursive (fun k => bit (Y k)) d) (fun n => bit (A n)) h.1 h.2

theorem reduces_iff_represents (A Y : Oracle) :
    Reduces A Y ↔ ∃ d : Nat.Partrec.Code, Represents Y d A :=
  ⟨reduces_represents, fun ⟨_, h⟩ => represents_reduces h⟩

end TuringRigidity.TableIndices

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticOracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable UniformOracle CommonIdeal IndexMatrix TableIndices OracleJump EncodedForcing
noncomputable section

theorem ArithmeticOracle.comp {B : OracleFamily} (hB : ArithmeticOracle B)
    {f : ℕ → ℕ} (hf : Primrec f) : ArithmeticOracle (fun O v => B O (f v)) := by
  exact query_at hB (hf.comp left_primrec) right_primrec

end
end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticRelations
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable CommonIdeal IndexMatrix TableIndices OracleJump
noncomputable section

theorem represents_arith {A B : OracleFamily} (hA : ArithmeticOracle A)
    (hB : ArithmeticOracle B) {e : ℕ → ℕ} (he : Primrec e) :
    Arith (fun O v => Represents (B O v) (machine (e v)) (A O v)) := by
  let c := left_primrec.comp (left_primrec.comp left_primrec)
  let n := right_primrec.comp (left_primrec.comp left_primrec)
  let z := right_primrec.comp left_primrec
  have hr := run_arith hB c (he.comp c) n z right_primrec
  have hb := bit_equal hA c n right_primrec
  have h := ((hr.imp hb).all.all.all).and ((hr.and hb).ex.ex.all)
  apply h.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro ⟨hs,ht⟩
    exact ⟨fun n z a ha => hs n z a (Option.mem_def.mp ha),
      fun n => by obtain ⟨z,a,ha,_⟩ := ht n; exact ⟨z,a,Option.mem_def.mpr ha⟩⟩
  · rintro ⟨hs,ht⟩
    exact ⟨fun n z a ha => hs n z a (Option.mem_def.mpr ha),
      fun n => by obtain ⟨z,a,ha⟩ := ht n; exact ⟨z,a,Option.mem_def.mp ha,hs n z a ha⟩⟩

theorem reduces_arith {A B : OracleFamily} (hA : ArithmeticOracle A)
    (hB : ArithmeticOracle B) : Arith (fun O v => Reduces (A O v) (B O v)) := by
  have h := (represents_arith (hA.comp left_primrec) (hB.comp left_primrec) right_primrec).ex
  apply h.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  rw [reduces_iff_represents]
  constructor
  · rintro ⟨e,he⟩
    exact ⟨machine e,he⟩
  · rintro ⟨e,he⟩
    exact ⟨encode e,by simpa using he⟩

theorem degree_equal_arith {A B : OracleFamily} (hA : ArithmeticOracle A)
    (hB : ArithmeticOracle B) : Arith (fun O v => degree (A O v) = degree (B O v)) :=
  ((reduces_arith hA hB).and (reduces_arith hB hA)).congr
    (fun O v => (degree_eq_iff (A O v) (B O v)).symm)

end
end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticParameterFormula
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open UniformArithmetic
universe u
namespace Formula

theorem oracleParameters_spec {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P)
    (o Q n : ℕ) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (O : Oracles) (hO : ∀ i, e (r i) = realCode (O i)) (N : ℕ) (hn : e n = natSet N) :
    (oracleParameters φ o Q n r).Eval e ↔ P O N := by
  rw [oracleParameters,eval_rename]
  have he : (fun i => e (oracleParameterVars o Q n r i)) = arithmeticEnv (e Q) O N := by
    funext i
    rcases i with _|i; exact hn
    rcases i with _|i; exact ho
    rcases i with _|i; rfl
    exact hO i
  rw [he]
  exact hφ _ hQ _ _

theorem twoOracles_spec {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P)
    (o Q n x y : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (A B : Oracle) (hx : e x = realCode A) (hy : e y = realCode B)
    (N : ℕ) (hn : e n = natSet N) :
    (twoOracles φ o Q n x y).Eval e ↔ P (fun i => if i = 0 then A else B) N := by
  apply oracleParameters_spec hφ o Q n _ e ho hQ _ _ N hn
  intro i; by_cases hi : i = 0 <;> simp only [hi,ite_true,ite_false] <;> assumption
end Formula

theorem degree_equality_bounded : ∃ φ : Formula, ∀ o Q z x y : ℕ, ∀ e : ℕ → ZFSet.{u},
    e o = ZFSet.omega → (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) →
    e z = natSet 0 → ∀ A B : Oracle, e x = realCode A → e y = realCode B →
      ((Formula.twoOracles φ o Q z x y).Eval e ↔ degree A = degree B) := by
  have hp := degree_equal_arith (parameter_arith 0) (parameter_arith 1)
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u} hp
  refine ⟨φ,?_⟩
  intro o Q z x y e ho hQ hz A B hx hy
  simpa using
    Formula.twoOracles_spec hφ o Q z x y e ho hQ A B hx hy 0 hz

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleGroundReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

theorem mem_groundReals (M x : ZFSet.{u}) :
    x ∈ groundReals M ↔ x ∈ M ∧ x ⊆ ZFSet.omega := by
  rw [groundReals,ZFSet.mem_sep,ZFSet.mem_powerset,and_comm]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeCodes
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem degreeCode_subset (R : ZFSet.{u}) (A : Oracle) : degreeCode R A ⊆ R :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem realCode_mem_degreeCode (R : ZFSet.{u}) (A B : Oracle) :
    realCode B ∈ degreeCode R A ↔ realCode B ∈ R ∧ degree B = degree A := by
  rw [degreeCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨hB,C,he,hC⟩
    have hBC := realCode_injective he
    exact ⟨hB,hBC.symm ▸ hC⟩
  · rintro ⟨hB,hBA⟩; exact ⟨hB,B,rfl,hBA⟩

theorem internal_degreeCode (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ x ∈ R, ∃ B : Oracle, realCode B = x)
    {A : Oracle} (hA : A ∈ modelReals M) : degreeCode R A ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet hS hω
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => realCode A)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hω
    rcases i with _|i; exact hQM
    rcases i with _|i; exact hz
    exact hA
  let D := ZFSet.sep (fun x => (Formula.twoOracles φ 1 2 3 0 4).Eval (cons x e)) R
  have hD : D ∈ M := sep_mem M hM hS _ e he hRM
  have hcode : degreeCode R A = D := by
    apply ZFSet.ext; intro x
    by_cases hx : x ∈ R
    · obtain ⟨B,rfl⟩ := hR x hx
      rw [realCode_mem_degreeCode,ZFSet.mem_sep]
      rw [hφ 1 2 3 0 4 (cons (realCode B) e) rfl hQ rfl B A rfl rfl]
    · simp only [degreeCode,D,ZFSet.mem_sep,hx,false_and]
  rw [hcode]
  exact hD

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DegreeSetFormula
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

namespace Formula

theorem degreeSet_spec {φ : Formula} (hφ : DegreeEqualityFormula.{u} φ)
    (o Q z R x D : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w)
    (A : Oracle) (hA : e x = realCode A) :
    (degreeSet φ o Q z R x D).Eval e ↔ e D = degreeCode (e R) A := by
  simp only [degreeSet,Formula.Eval,eval_subset,eval_allMem,eval_iff,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro w
    by_cases hw : w ∈ e R
    · obtain ⟨B,rfl⟩ := hR w hw
      rw [realCode_mem_degreeCode]
      have hh := (h _ hw).trans (hφ (o+1) (Q+1) (z+1) 0 (x+1) (cons (realCode B) e)
        ho hQ hz B A rfl hA)
      exact hh.trans (and_iff_right hw).symm
    · exact ⟨fun h => False.elim (hw (hsub h)),fun h => False.elim (hw (degreeCode_subset _ _ h))⟩
  · intro hd
    refine ⟨hd.symm ▸ degreeCode_subset (e R) A,?_⟩
    intro w hw
    obtain ⟨B,rfl⟩ := hR w hw
    rw [hd,realCode_mem_degreeCode,and_iff_right hw]
    exact (hφ (o+1) (Q+1) (z+1) 0 (x+1) (cons (realCode B) e) ho hQ hz B A rfl hA).symm
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeUniverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem mem_degreeUniverse (R D : ZFSet.{u}) :
    D ∈ degreeUniverse R ↔ ∃ A : Oracle, realCode A ∈ R ∧ D = degreeCode R A := by
  rw [degreeUniverse,ZFSet.mem_sep]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  obtain ⟨A,_,rfl⟩ := h
  exact ZFSet.mem_powerset.mpr (degreeCode_subset R A)

namespace Formula

theorem degreeUniverseMember_spec {φ : Formula} (hφ : DegreeEqualityFormula.{u} φ)
    (o Q z R D : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w) :
    (degreeUniverseMember φ o Q z R D).Eval e ↔ e D ∈ degreeUniverse (e R) := by
  simp only [degreeUniverseMember,Formula.Eval]
  rw [mem_degreeUniverse]
  constructor
  · rintro ⟨w,hw,hd⟩
    obtain ⟨A,rfl⟩ := hR w hw
    exact ⟨A,hw,(degreeSet_spec hφ (o+1) (Q+1) (z+1) (R+1) 0 (D+1)
      (cons (realCode A) e) ho hQ hz hR A rfl).mp hd⟩
  · rintro ⟨A,hA,hd⟩
    exact ⟨realCode A,hA,(degreeSet_spec hφ (o+1) (Q+1) (z+1) (R+1) 0 (D+1)
      (cons (realCode A) e) ho hQ hz hR A rfl).mpr hd⟩
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic
universe u

theorem mem_degreeOrder (R D E : ZFSet.{u}) :
    ZFSet.pair D E ∈ degreeOrder R ↔
      D ∈ degreeUniverse R ∧ E ∈ degreeUniverse R ∧ degreeCodeLE D E := by
  rw [degreeOrder,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,D',hD,E',hE,he,hle⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hD,hE,hle⟩
  · rintro ⟨hD,hE,hle⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨D,hD,E,hE,rfl⟩,D,hD,E,hE,rfl,hle⟩

theorem degree_order_bounded : ∃ φ : Formula, DegreeOrderFormula.{u} φ := by
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u}
    (reduces_arith (parameter_arith 0) (parameter_arith 1))
  refine ⟨φ,?_⟩
  intro o Q z x y e ho hQ hz A B hx hy
  simpa using Formula.twoOracles_spec hφ o Q z x y e ho hQ A B hx hy 0 hz

namespace Formula

theorem degreeLE_spec {φ : Formula} (hφ : DegreeOrderFormula.{u} φ)
    (o Q z D E : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hD : ∀ w ∈ e D, ∃ A : Oracle, realCode A = w)
    (hE : ∀ w ∈ e E, ∃ A : Oracle, realCode A = w) :
    (degreeLE φ o Q z D E).Eval e ↔ degreeCodeLE (e D) (e E) := by
  simp only [degreeLE,Formula.Eval,cons_succ]
  constructor
  · rintro ⟨a,ha,b,hb,hle⟩
    obtain ⟨A,rfl⟩ := hD a ha
    obtain ⟨B,rfl⟩ := hE b hb
    exact ⟨A,B,ha,hb,(hφ (o+2) (Q+2) (z+2) 1 0
      (cons (realCode B) (cons (realCode A) e)) ho hQ hz A B rfl rfl).mp hle⟩
  · rintro ⟨A,B,hA,hB,hle⟩
    exact ⟨realCode A,hA,realCode B,hB,(hφ (o+2) (Q+2) (z+2) 1 0
      (cons (realCode B) (cons (realCode A) e)) ho hQ hz A B rfl rfl).mpr hle⟩

theorem degreeOrderMember_spec {φ : Formula} (hφ : DegreeOrderFormula.{u} φ)
    (o Q z U p : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (R : ZFSet.{u}) (hU : e U = degreeUniverse R)
    (hR : ∀ w ∈ R, ∃ A : Oracle, realCode A = w) :
    (degreeOrderMember φ o Q z U p).Eval e ↔ e p ∈ degreeOrder R := by
  simp only [degreeOrderMember,Formula.Eval,eval_orderedPair,cons_succ,cons_zero]
  rw [hU]
  have hd (D : ZFSet.{u}) (hD : D ∈ degreeUniverse R) : ∀ w ∈ D, ∃ A : Oracle, realCode A = w := by
    obtain ⟨A,_,rfl⟩ := (mem_degreeUniverse R D).mp hD
    exact fun w hw => hR w (degreeCode_subset R A hw)
  constructor
  · rintro ⟨D,hD,E,hE,hp,hle⟩
    rw [hp,mem_degreeOrder]
    exact ⟨hD,hE,(degreeLE_spec hφ (o+2) (Q+2) (z+2) 1 0 (cons E (cons D e))
      ho hQ hz (hd D hD) (hd E hE)).mp hle⟩
  · intro hp
    obtain ⟨_,D,hD,E,hE,he,hle⟩ := ZFSet.mem_sep.mp hp
    exact ⟨D,hD,E,hE,he,(degreeLE_spec hφ (o+2) (Q+2) (z+2) 1 0 (cons E (cons D e))
      ho hQ hz (hd D hD) (hd E hE)).mpr hle⟩
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformPowerName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u

theorem uniform_power_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
    ∃ b : Name (Conditions c), b.encode (label c) ∈ M ∧
      ∀ (G : GenericFilter (Conditions c)), GroundGeneric M G → ⊤ ∈ G.carrier →
        ∀ x, x ∈ b.val G.carrier ↔
          x ∈ genericExtensionSet M c G.carrier ∧ x ⊆ a.val G.carrier := by
  have hS := hT.separation.finitePrefix.bounded
  have hsupport := support_mem M hM hT.pairing hT.union hT.powerSet hS hc hoM ho a ha
  obtain ⟨W,hW,hWdef⟩ := internal_power M hM hT.powerSet hsupport
  have hWsub : ∀ B ∈ W, B ⊆ a.support (label c) := fun B hB => ((hWdef B).mp hB).2
  have hpower : (powerName a W).encode (label c) ∈ M := by
    rw [encode_powerName a W hWsub]
    exact product_mem M hM hT.pairing hT.union hT.powerSet hS hW
      (singleton_mem M hM hT.pairing (hM c hc _ (label_mem c ⊤)))
  refine ⟨powerName a W,hpower,?_⟩
  intro G hG ht x
  constructor
  · intro hx
    obtain ⟨B,hB,hBx⟩ := (mem_val_powerName a W G.carrier ht x).mp hx
    have hcode : (a.restrict (label c) B).encode (label c) ∈ M := by
      rw [Name.encode_restrict _ _ _ (hWsub B hB)]
      exact ((hWdef B).mp hB).1
    exact ⟨(mem_extensionSet M c G.carrier x).mpr ⟨_,hcode,hBx⟩,
      hBx ▸ a.val_restrict_subset (label c) B G⟩
  · rintro ⟨hx,hsub⟩
    obtain ⟨b,hb,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
    obtain ⟨B,hBM,hBS,hBval⟩ := internal_intersection_name M hM hT.pairing hT.union
      hT.powerSet hS hT.replacement.finitePrefix hT.infinity hc hoM ho G hG a b ha hb
    apply (mem_val_powerName a W G.carrier ht _).mpr
    refine ⟨B,(hWdef B).mpr ⟨hBM,hBS⟩,hBval.trans ?_⟩
    apply ZFSet.ext; intro y
    rw [ZFSet.mem_inter]
    exact ⟨And.right,fun hy => ⟨hsub hy,hy⟩⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformOwnRealsName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u

theorem uniform_ownReals_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) :
    ∃ R : Name (Conditions c), R.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        R.val G.carrier = groundReals (genericExtensionSet M c G.carrier) := by
  have hω := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
      (sourceT_omega_mem M hM hT)
  obtain ⟨R,hR,hval⟩ := uniform_power_name M hM hT hc hoM ho (Name.check ZFSet.omega) hω
  refine ⟨R,hR,?_⟩
  intro G hG ht
  apply ZFSet.ext; intro x
  rw [hval G hG ht x,mem_groundReals,Name.val_check G.carrier ht]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformSeparationName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem uniform_separation_name (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : BoundedSetTheory.Formula) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ B ∈ M, B ⊆ a.support (label c) ∧
      ∀ (G : GenericFilter (Conditions c)), GroundGeneric M G → ∀ x,
      x ∈ (a.restrict (label c) B).val G.carrier ↔ x ∈ a.val G.carrier ∧
        φ.Eval (cons x (fun i => (e i).val G.carrier)) := by
  obtain ⟨d,hd,hdT,had,hnd⟩ := finite_container M hM hP hU hS hR hI
    (fun i => (push a e i).encode (label c))
    (by intro i; cases i <;> simp only [push_zero,push_succ]; exact ha; exact he _) (bound φ+2)
  let e' := truncate (bound φ) e
  have he' (i) : (e' i).encode (label c) ∈ d := by
    dsimp only [e',truncate]
    split
    · exact hnd (i+1) (by omega)
    · exact hnd 1 (by omega)
  have hai (i) : (a.child i).encode (label c) ∈ d :=
    names_childClosed d c hdT a had _ (child_relation a i)
  have hpush (i) (n) : (push (a.child i) e' n).encode (label c) ∈ d := by
    cases n with
    | zero => exact hai i
    | succ n => exact he' n
  obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd hc hoM
  let k := ZFSet.prod d d
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  let env := cons d (cons c (cons k (cons o (cons f (fun i => (e' i).encode (label c))))))
  have henv : ∀ i, env i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact hc
    rcases i with _|i; exact hk
    rcases i with _|i; exact hoM
    rcases i with _|i; exact hf
    exact hM d hd _ (he' i)
  let ψ := Formula.existsMem 1 (.existsMem 3 (.conj (Formula.orderedPair 2 1 0)
    (code φ 3 4 5 6 7 (push 1 (fun i => i+8)) 0)))
  let B := ZFSet.sep (fun z => ψ.Eval (cons z env)) (a.support (label c))
  have hBM : B ∈ M := sep_mem M hM hS ψ env henv
    (support_mem M hM hP hU hPow hS hc hoM ho a ha)
  have hBsub : B ⊆ a.support (label c) := fun z hz => (ZFSet.mem_sep.mp hz).1
  have query (i : a.arity) (q : Conditions c) (z : ZFSet.{u}) :=
    eval_code φ hdT ho hfG (push (a.child i) e') (hpush i) q
      (cons (label c q) (cons ((a.child i).encode (label c)) (cons z env)))
      3 4 5 6 7 (push 1 (fun n => n+8)) 0 ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (by intro n; cases n <;> rfl)
  have hB (i : a.arity) (q : Conditions c) (hq : q ≤ a.tag i) :
      ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ B ↔ Forces (push (a.child i) e') φ q := by
    have hs : ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ a.support (label c) :=
      ZFSet.mem_range.mpr ⟨⟨i,⟨q,hq⟩⟩,rfl⟩
    change _ ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep,and_iff_right hs]
    change (Formula.existsMem 1 _).Eval _ ↔ _
    simp only [Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,env]
    constructor
    · rintro ⟨x,hx,r,hr,hxr,hφ⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxr
      exact (query i q _).mp hφ
    · intro hφ
      exact ⟨_,hai i,_,label_mem c q,rfl,(query i q _).mpr hφ⟩
  refine ⟨B,hBM,hBsub,?_⟩
  intro G hG
  have ht (i : a.arity) :
      φ.Eval (cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier)) ↔
        ∃ p ∈ G.carrier, Forces (push (a.child i) e') φ p := by
    have hfinite : φ.Eval (cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier)) ↔
        φ.Eval (fun n => (push (a.child i) e' n).val G.carrier) := by
      apply eval_congr
      intro n hn
      cases n with
      | zero => rfl
      | succ n =>
        simp only [cons_succ,push_succ]
        dsimp only [e',truncate]
        rw [ite_eq_left (by omega)]
    exact hfinite.trans (internal_bounded_truth M hM hP hU hPow hS hR hI hc hoM ho G hG φ _
      (fun n => hM d hd _ (hpush i n)))
  intro x
  constructor
  · intro hx
    have hxa := a.val_restrict_subset (label c) B G hx
    obtain ⟨i,q,hqi,hqb,hqG,hix⟩ := (a.mem_val_restrict (label c) B G.carrier x).mp hx
    have hφ := (ht i).mpr ⟨q,hqG,(hB i q hqi).mp hqb⟩
    exact ⟨hxa,hix ▸ hφ⟩
  · rintro ⟨hxa,hφ⟩
    obtain ⟨i,hi,hix⟩ := (a.mem_val_children G.carrier x).mp hxa
    obtain ⟨p,hp,hf⟩ := (ht i).mp (hix ▸ hφ)
    obtain ⟨q,hq,hqp,hqi⟩ := G.directed hp hi
    exact (a.mem_val_restrict (label c) B G.carrier x).mpr
      ⟨i,q,hqi,(hB i q hqi).mpr (forces_mono φ _ hqp hf),hq,hix⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformProductName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing BoundedForcing
universe u

theorem uniform_product_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a b : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (hb : b.encode (label c) ∈ M) :
    ∃ d : Name (Conditions c), d.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        d.val G.carrier = ZFSet.prod (a.val G.carrier) (b.val G.carrier) := by
  have hS := hT.separation.finitePrefix.bounded
  let U := Name.union (Name.pair a b)
  have hU : U.encode (label c) ∈ M := names_union_closed M c o hM hT.pairing hT.union
    hT.powerSet hS hc hoM ho (names_pair_closed M c hM hT.pairing hc ha hb)
  obtain ⟨P,hP,hPv⟩ := uniform_power_name M hM hT hc hoM ho U hU
  obtain ⟨Q,hQ,hQv⟩ := uniform_power_name M hM hT hc hoM ho P hP
  let e := push a (push b (fun _ => b))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    rcases i with _|_|i; exact ha; exact hb; exact hb
  obtain ⟨B,hB,hBS,hBv⟩ := uniform_separation_name M hM hT.pairing hT.union hT.powerSet
    hS hT.replacement.finitePrefix hT.infinity hc hoM ho productFormula Q hQ e he
  refine ⟨Q.restrict (label c) B,?_,?_⟩
  · rw [Name.encode_restrict _ _ _ hBS]; exact hB
  · intro G hG ht
    let E := genericExtensionSet M c G.carrier
    have hE := genericExtensionSet_transitive M c hM G.carrier
    have hTE := extension_sourceT M hM hT hc hoM ho G hG ht
    have haE : a.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨a,ha,rfl⟩
    have hbE : b.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨b,hb,rfl⟩
    have hUv : U.val G.carrier = a.val G.carrier ∪ b.val G.carrier := by
      rw [Name.val_union,Name.val_pair G.carrier ht,ZFSet.sUnion_pair]
    have hbound : ZFSet.prod (a.val G.carrier) (b.val G.carrier) ⊆ Q.val G.carrier := by
      intro z hz
      obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp hz
      have hxE := hE _ haE x hx
      have hyE := hE _ hbE y hy
      apply (hQv G hG ht _).mpr
      refine ⟨orderedPair_mem E hE hTE.pairing hxE hyE,?_⟩
      intro t htz
      change t ∈ ({({x} : ZFSet.{u}),({x,y} : ZFSet.{u})} : ZFSet.{u}) at htz
      rcases ZFSet.mem_pair.mp htz with rfl|rfl
      · apply (hPv G hG ht _).mpr
        refine ⟨singleton_mem E hE hTE.pairing hxE,?_⟩
        intro w hw
        obtain rfl := ZFSet.mem_singleton.mp hw
        rw [hUv]; exact ZFSet.mem_union.mpr (Or.inl hx)
      · apply (hPv G hG ht _).mpr
        refine ⟨pair_mem E hE hTE.pairing hxE hyE,?_⟩
        intro w hw
        rw [hUv]
        rcases ZFSet.mem_pair.mp hw with rfl|rfl
        · exact ZFSet.mem_union.mpr (Or.inl hx)
        · exact ZFSet.mem_union.mpr (Or.inr hy)
    apply ZFSet.ext; intro z
    rw [hBv G hG z]
    change (_ ∧ productFormula.Eval (cons z (cons (a.val G.carrier)
      (cons (b.val G.carrier) (fun _ => b.val G.carrier))))) ↔ _
    rw [eval_productFormula]
    exact ⟨And.right,fun hz => ⟨hbound hz,hz⟩⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalNameEvaluation
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalNameEvaluation
open TransitiveNameModel RecursiveNames RelationCollapse
universe u

theorem activeRelation_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d g : ZFSet.{u}} (hd : d ∈ M) (hg : g ∈ M) : activeRelation d g ∈ M := by
  simpa only [activeRelation,activeFormula,Formula.Eval,Formula.eval_orderedPair,
    Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded activeFormula (cons d (fun _ => g))
      (by intro i; cases i <;> assumption)
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hd hd)

theorem value_eq (d : ZFSet.{u}) (hd : Transitive d) {c : ZFSet.{u}}
    (G : Set (Conditions c)) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ d) :
    value d (activeRelation d (genericFilterSet c G)) (active_wellFounded _ _) (a.encode (label c)) = a.val G := by
  induction a with
  | mk ι child tag ih =>
    have hc (i : ι) : (child i).encode (label c) ∈ d := by
      have hp := hd _ ha _ (ZFSet.mem_range_self i)
      have hs := hd _ hp _ (ZFSet.mem_pair.mpr (Or.inl rfl))
      exact hd _ hs _ (ZFSet.mem_singleton.mpr rfl)
    apply ZFSet.ext; intro z
    rw [mem_value,Name.mem_val]
    constructor
    · rintro ⟨x,_,hxy,hzx⟩
      obtain ⟨_,_,p,hp,hpa⟩ := (active_pair _ _ _ _).mp hxy
      obtain ⟨i,hi⟩ := ZFSet.mem_range.mp hpa
      obtain ⟨hiX,hiP⟩ := ZFSet.pair_inj.mp hi
      obtain ⟨q,hq,hqp⟩ := (mem_genericFilterSet c G p).mp hp
      have htag : tag i = q := label_injective c (hiP.trans hqp.symm)
      refine ⟨i,htag.symm ▸ hq,?_⟩
      rw [←ih i (hc i),hiX]
      exact hzx.symm
    · rintro ⟨i,hig,hiz⟩
      refine ⟨(child i).encode (label c),hc i,?_,?_⟩
      · exact (active_pair _ _ _ _).mpr ⟨hc i,ha,label c (tag i),
          (mem_genericFilterSet c G _).mpr ⟨tag i,hig,rfl⟩,ZFSet.mem_range_self i⟩
      · exact hiz.symm.trans (ih i (hc i)).symm

theorem name_value_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c : ZFSet.{u}} (G : Set (Conditions c)) (hg : genericFilterSet c G ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) : a.val G ∈ M := by
  obtain ⟨d,hdM,hd,had⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity ha
  obtain ⟨f,hf,hfg⟩ := internal_graph M d (activeRelation d (genericFilterSet c G)) hM
    hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
    hdM (activeRelation_mem M hM hT hdM hg) (active_wellFounded _ _)
  have hp : ZFSet.pair (a.encode (label c))
      (value d (activeRelation d (genericFilterSet c G)) (active_wellFounded _ _) (a.encode (label c))) ∈ f :=
    (hfg.mem_iff (active_wellFounded _ _) _).mpr ⟨_,had,rfl⟩
  have hv := second_mem_doubleUnion hp
  have hi := hM _ (iterUnion_mem M hM hT.union hf 2) _ hv
  rwa [value_eq d hd G a had] at hi

theorem extension_subset (M N : ZFSet.{u}) (hN : Transitive N) (hT : SourceT N) (hMN : M ⊆ N)
    {c : ZFSet.{u}} (G : Set (Conditions c)) (hG : genericFilterSet c G ∈ N) :
    genericExtensionSet M c G ⊆ N := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := (mem_extensionSet M c G x).mp hx
  exact name_value_mem N hN hT G hG a (hMN ha)

end TuringRigidity.BoundedSetTheory.InternalNameEvaluation

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DenseInclusionExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.DenseInclusionExtension
open TransitiveNameModel BoundedSetTheory CountableForcing InternalDenseInclusion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem restrictSet_mem (N a k : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (ha : a ∈ N) (hk : k ∈ N) : restrictSet a k ∈ N := by
  let e := fun _ : ℕ => k
  simpa only [restrictSet,Formula.Eval,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded (.member 0 1) e (fun _ => hk) ha

end TuringRigidity.DenseInclusionExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalOrderIsoTransport
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalOrderIsoTransport
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem imageSet_mem (M b f g : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hb : b ∈ M) (hf : f ∈ M) (hg : g ∈ M) : imageSet b f g ∈ M := by
  let e := cons g (fun _ => f)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hg; exact hf
  simpa only [imageSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 1 3)) e he hb

theorem preimageSet_mem (M a f k : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hf : f ∈ M) (hk : k ∈ M) : preimageSet a f k ∈ M := by
  let e := cons k (fun _ => f)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hk; exact hf
  simpa only [preimageSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 1 0 3)) e he ha

theorem map_ground_generic (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (AutomorphismName.mapFilter e G) := by
  intro D hD hd
  let E := DenseInclusionExtension.restrictSet b D
  have hE := DenseInclusionExtension.restrictSet_mem M b D hM hT hb hD
  have hden : Dense {p : Conditions a | label a p ∈ preimageSet a f E} := by
    intro p
    obtain ⟨q,hqp,hqD⟩ := hd (e p)
    refine ⟨e.symm q,by simpa using e.symm.monotone hqp,?_⟩
    exact ZFSet.mem_sep.mpr ⟨label_mem a _,label b q,ZFSet.mem_sep.mpr ⟨label_mem b q,hqD⟩,(he _ _).mpr (e.apply_symm_apply q).symm⟩
  obtain ⟨p,hp,hpD⟩ := hG (preimageSet a f E) (preimageSet_mem M a f E hM hT ha hf hE) hden
  obtain ⟨_,y,hyD,hpy⟩ := ZFSet.mem_sep.mp hpD
  obtain ⟨hyb,hyD⟩ := ZFSet.mem_sep.mp hyD
  obtain ⟨q,rfl⟩ := label_surjective b hyb
  obtain rfl := (he p q).mp hpy
  exact ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,hyD⟩

theorem mapFilterSet_eq (a b f : ZFSet.{0}) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) :
    genericFilterSet b (AutomorphismName.mapFilter e G).carrier =
      imageSet b f (genericFilterSet a G.carrier) := by
  apply ZFSet.ext; intro y
  constructor
  · intro hy
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet _ _ y).mp hy
    exact ZFSet.mem_sep.mpr ⟨label_mem b q,label a (e.symm q),
      (mem_genericFilterSet _ _ _).mpr ⟨e.symm q,hq,rfl⟩,(he _ _).mpr (e.apply_symm_apply q).symm⟩
  · intro hy
    obtain ⟨hyb,x,hx,hxy⟩ := ZFSet.mem_sep.mp hy
    obtain ⟨q,rfl⟩ := label_surjective b hyb
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    obtain rfl := (he p q).mp hxy
    exact (mem_genericFilterSet _ _ _).mpr ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,rfl⟩

theorem originalFilterSet_eq (a b f : ZFSet.{0}) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) :
    genericFilterSet a G.carrier =
      preimageSet a f (genericFilterSet b (AutomorphismName.mapFilter e G).carrier) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet _ _ x).mp hx
    exact ZFSet.mem_sep.mpr ⟨label_mem a p,label b (e p),
      (mem_genericFilterSet _ _ _).mpr ⟨e p,by simpa [AutomorphismName.mapFilter] using hp,rfl⟩,
      (he p (e p)).mpr rfl⟩
  · intro hx
    obtain ⟨hxa,y,hy,hxy⟩ := ZFSet.mem_sep.mp hx
    obtain ⟨p,rfl⟩ := label_surjective a hxa
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet _ _ y).mp hy
    obtain rfl := (he p q).mp hxy
    exact (mem_genericFilterSet _ _ _).mpr ⟨p,by simpa [AutomorphismName.mapFilter] using hq,rfl⟩

theorem extension_eq (M a b f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hf : f ∈ M) (e : Conditions a ≃o Conditions b)
    (he : ∀ p q, ZFSet.pair (label a p) (label b q) ∈ f ↔ q = e p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M b (AutomorphismName.mapFilter e G).carrier = genericExtensionSet M a G.carrier := by
  let K := AutomorphismName.mapFilter e G
  have hK := map_ground_generic M a b f hM hT ha hb hf e he G hG
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  obtain ⟨hV,hTV,hMV,hkV⟩ := RegularTreeExtension.extension_properties M b hM hT hb K hK
  have hkN : genericFilterSet b K.carrier ∈ genericExtensionSet M a G.carrier := by
    rw [mapFilterSet_eq a b f e he G]
    exact imageSet_mem _ b f _ hN hTN (hMN hb) (hMN hf) hgN
  have hgV : genericFilterSet a G.carrier ∈ genericExtensionSet M b K.carrier := by
    rw [originalFilterSet_eq a b f e he G]
    exact preimageSet_mem _ a f _ hV hTV (hMV ha) (hMV hf) hkV
  apply ZFSet.ext; intro x
  exact ⟨fun hx => InternalNameEvaluation.extension_subset M _ hN hTN hMN K.carrier hkN hx,
    fun hx => InternalNameEvaluation.extension_subset M _ hV hTV hMV G.carrier hgV hx⟩

end TuringRigidity.InternalOrderIsoTransport

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformDegreeUniverseName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open RecursiveNames TransitiveNameModel AtomicForcing CountableForcing BoundedForcing
open RelativeConstructible
universe u

theorem uniform_degreeUniverse_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) :
    ∃ D : Name (Conditions c), D.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        D.val G.carrier = degreeUniverse (groundReals (genericExtensionSet M c G.carrier)) := by
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  have hcheck {x : ZFSet.{u}} (hx : x ∈ M) :
      (Name.check x : Name (Conditions c)).encode (label c) ∈ M :=
    encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hx
  obtain ⟨R,hR,hRv⟩ := uniform_ownReals_name M hM hT hc hoM ho
  obtain ⟨P,hP,hPv⟩ := uniform_power_name M hM hT hc hoM ho R hR
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  let e := push (Name.check ZFSet.omega) (push (Name.check Q) (push (Name.check (natSet 0)) (fun _ => R)))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    rcases i with _|_|_|i
    exact hcheck hω; exact hcheck hQM; exact hcheck hz; exact hR
  obtain ⟨B,hB,hBS,hBv⟩ := uniform_separation_name M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hoM ho
    (Formula.degreeUniverseMember φ 1 2 3 4 0) P hP e he
  refine ⟨P.restrict (label c) B,?_,?_⟩
  · rw [Name.encode_restrict _ _ _ hBS]; exact hB
  · intro G hG ht
    let E := genericExtensionSet M c G.carrier
    have hE := genericExtensionSet_transitive M c hM G.carrier
    have hTE := extension_sourceT M hM hT hc hoM ho G hG ht
    have hr : ∀ w ∈ R.val G.carrier, ∃ A : Oracle, realCode A = w := by
      rw [hRv G hG ht]
      intro w hw
      exact ⟨decodeReal w,realCode_decodeReal ((mem_groundReals E w).mp hw).2⟩
    have hRE : R.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨R,hR,rfl⟩
    have hbound : degreeUniverse (R.val G.carrier) ⊆ P.val G.carrier := by
      intro D hD
      obtain ⟨A,hA,rfl⟩ := (mem_degreeUniverse _ _).mp hD
      exact (hPv G hG ht _).mpr ⟨internal_degreeCode E hE hTE _ hRE hr (hE _ hRE _ hA),
        degreeCode_subset _ A⟩
    have hv : (fun i => (e i).val G.carrier) =
        cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => R.val G.carrier))) := by
      funext i; rcases i with _|_|_|i
      exact Name.val_check G.carrier ht _
      exact Name.val_check G.carrier ht _
      exact Name.val_check G.carrier ht _
      rfl
    rw [←hRv G hG ht]
    apply ZFSet.ext; intro D
    rw [hBv G hG D,hv,Formula.degreeUniverseMember_spec hφ 1 2 3 4 0 _ rfl hQ rfl hr]
    exact ⟨And.right,fun h => ⟨hbound h,h⟩⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformDegreeOrderName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open RecursiveNames TransitiveNameModel AtomicForcing CountableForcing BoundedForcing
open RelativeConstructible
universe u

theorem uniform_degreeOrder_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) :
    ∃ L : Name (Conditions c), L.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        L.val G.carrier = degreeOrder (groundReals (genericExtensionSet M c G.carrier)) := by
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  have hcheck {x : ZFSet.{u}} (hx : x ∈ M) :
      (Name.check x : Name (Conditions c)).encode (label c) ∈ M :=
    encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hx
  obtain ⟨D,hD,hDv⟩ := uniform_degreeUniverse_name M hM hT hc hoM ho
  obtain ⟨P,hP,hPv⟩ := uniform_product_name M hM hT hc hoM ho D D hD hD
  obtain ⟨φ,hφ⟩ := degree_order_bounded.{u}
  let e := push (Name.check ZFSet.omega) (push (Name.check Q) (push (Name.check (natSet 0)) (fun _ => D)))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    rcases i with _|_|_|i
    exact hcheck hω; exact hcheck hQM; exact hcheck hz; exact hD
  obtain ⟨B,hB,hBS,hBv⟩ := uniform_separation_name M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hoM ho
    (Formula.degreeOrderMember φ 1 2 3 4 0) P hP e he
  refine ⟨P.restrict (label c) B,?_,?_⟩
  · rw [Name.encode_restrict _ _ _ hBS]; exact hB
  · intro G hG ht
    let E := genericExtensionSet M c G.carrier
    have hr : ∀ w ∈ groundReals E, ∃ A : Oracle, realCode A = w := by
      intro w hw
      exact ⟨decodeReal w,realCode_decodeReal ((mem_groundReals E w).mp hw).2⟩
    have hv : (fun i => (e i).val G.carrier) =
        cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => D.val G.carrier))) := by
      funext i; rcases i with _|_|_|i
      exact Name.val_check G.carrier ht _
      exact Name.val_check G.carrier ht _
      exact Name.val_check G.carrier ht _
      rfl
    apply ZFSet.ext; intro z
    rw [hBv G hG z,hv,Formula.degreeOrderMember_spec hφ 1 2 3 4 0 _ rfl hQ rfl
      (groundReals E) (hDv G hG ht) hr,hPv G hG ht,hDv G hG ht]
    exact ⟨And.right,fun h => ⟨(ZFSet.mem_sep.mp h).1,h⟩⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTGenericExistence
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals CountableForcing
universe u
noncomputable section

theorem countable_ground_generic (M : ZFSet.{u})
    (hct : (M : Set ZFSet.{u}).Countable) (hne : (M : Set ZFSet.{u}).Nonempty)
    {c : ZFSet.{u}} [Preorder (Conditions c)] (p : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p ∈ G.carrier ∧ AtomicForcing.GroundGeneric M G := by
  classical
  obtain ⟨e,he⟩ := hct.exists_eq_range hne
  let D : ℕ → Set (Conditions c) := fun n =>
    if Dense {q | label c q ∈ e n} then {q | label c q ∈ e n} else Set.univ
  have hd : ∀ n, Dense (D n) := by
    intro n
    dsimp only [D]
    split
    · assumption
    · exact fun q => ⟨q,le_rfl,Set.mem_univ q⟩
  obtain ⟨G,hp,hG⟩ := exists_generic D hd p
  refine ⟨G,hp,?_⟩
  intro a ha had
  have har : a ∈ Set.range e := he ▸ ha
  obtain ⟨n,rfl⟩ := har
  obtain ⟨q,hq,hqd⟩ := hG n
  exact ⟨q,hq,by simpa only [D,ite_eq_left had,Set.mem_ofPred_eq] using hqd⟩

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalHomogeneousTruth
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem top_weak_of_internal_symmetry (M c : ZFSet.{0})
    [OrderTop (Conditions c)] (hM : Transitive M) (hT : SourceT M)
    (hct : (M : Set ZFSet.{0}).Countable) (hc : c ∈ M)
    (hom : ∀ p q : Conditions c, ∃ w ∈ M, ∃ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) ∧
      ∃ r, r ≤ a p ∧ r ≤ q)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) →
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        (φ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          φ.Eval (fun i => (e i).val G.carrier)))
    (p : Conditions c) (hp : Forces e φ p) : Forces e (.neg (.neg φ)) ⊤ := by
  have truthAt (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
      (ψ : BoundedSetTheory.Formula) := internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
    (InternalCollapse.orderSet_mem M hM hT hc) (InternalCollapse.orderSet_pair c)
    G hG ψ e he
  intro q _ hn
  obtain ⟨w,hw,a,ha,r,hrp,hrq⟩ := hom p q
  obtain ⟨G,hr,hG⟩ := ArithmeticTree.countable_ground_generic M hct ⟨c,hc⟩ (a.symm r)
  have hpG : p ∈ G.carrier :=
    G.upper (by simpa using a.symm.monotone hrp) hr
  have hval := (truthAt G hG φ).mpr ⟨p,hpG,hp⟩
  let H := AutomorphismName.mapFilter a G
  have hH : GroundGeneric M H :=
    InternalOrderIsoTransport.map_ground_generic M c c w hM hT hc hc hw a ha G hG
  have hrH : r ∈ H.carrier := hr
  have hqH : q ∈ H.carrier := H.upper hrq hrH
  have hnot := (truthAt H hH (.neg φ)).mpr ⟨q,hqH,hn⟩
  exact hnot ((hinv w hw a ha G hG).mpr hval)

theorem all_generics_of_internal_symmetry (M c : ZFSet.{0})
    [OrderTop (Conditions c)] (hM : Transitive M) (hT : SourceT M)
    (hct : (M : Set ZFSet.{0}).Countable) (hc : c ∈ M)
    (hom : ∀ p q : Conditions c, ∃ w ∈ M, ∃ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) ∧
      ∃ r, r ≤ a p ∧ r ≤ q)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions c))
    (he : ∀ i, (e i).encode (label c) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) →
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        (φ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          φ.Eval (fun i => (e i).val G.carrier)))
    (G₀ : GenericFilter (Conditions c)) (hG₀ : GroundGeneric M G₀)
    (hφ : φ.Eval (fun i => (e i).val G₀.carrier)) :
    Forces e (.neg (.neg φ)) ⊤ ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        φ.Eval (fun i => (e i).val G.carrier) := by
  classical
  have truthAt (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G)
      (ψ : BoundedSetTheory.Formula) := internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
    (InternalCollapse.orderSet_mem M hM hT hc) (InternalCollapse.orderSet_pair c)
    G hG ψ e he
  obtain ⟨p,_,hp⟩ := (truthAt G₀ hG₀ φ).mp hφ
  have ht := top_weak_of_internal_symmetry M c hM hT hct hc hom φ e he hinv p hp
  refine ⟨ht,?_⟩
  intro G hG
  obtain ⟨q,hq⟩ := G.nonempty
  have hv := (truthAt G hG (.neg (.neg φ))).mpr ⟨⊤,G.upper le_top hq,ht⟩
  exact not_not.mp hv

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_HomogeneousDegreeExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible SetModelSatisfaction
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem degreeExtensionFormula_spec (f D L I ρ : ZFSet.{0}) :
    degreeExtensionFormula.Eval (cons f (cons D (cons L (cons I (fun _ => ρ))))) ↔
      IsAction f D L ∧ I ⊆ D ∧ ρ ⊆ f := by
  simp only [degreeExtensionFormula,Formula.Eval,eval_actionFormula,Formula.eval_subset,
    cons_zero,cons_succ]

theorem degree_extension_all_generics (M c I ρ : ZFSet.{0})
    [OrderTop (Conditions c)] (hM : Transitive M) (hT : SourceT M)
    (hct : (M : Set ZFSet.{0}).Countable) (hc : c ∈ M) (hI : I ∈ M) (hρ : ρ ∈ M)
    (hom : ∀ p q : Conditions c, ∃ w ∈ M, ∃ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) ∧
      ∃ r, r ≤ a p ∧ r ≤ q)
    (f : Name (Conditions c)) (hf : f.encode (label c) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) →
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        f.val (AutomorphismName.mapFilter a G).carrier = f.val G.carrier)
    (G₀ : GenericFilter (Conditions c)) (hG₀ : GroundGeneric M G₀)
    (h₀ : OwnDegreeExtension (genericExtensionSet M c G₀.carrier) I ρ (f.val G₀.carrier)) :
    ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
      OwnDegreeExtension (genericExtensionSet M c G.carrier) I ρ (f.val G.carrier) := by
  have hoM := InternalCollapse.orderSet_mem M hM hT hc
  have ho := InternalCollapse.orderSet_pair c
  obtain ⟨D,hD,hDv⟩ := uniform_degreeUniverse_name M hM hT hc hoM ho
  obtain ⟨L,hL,hLv⟩ := uniform_degreeOrder_name M hM hT hc hoM ho
  have hcheck {x : ZFSet.{0}} (hx : x ∈ M) :
      (Name.check x : Name (Conditions c)).encode (label c) ∈ M :=
    encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hx
  let e := push f (push D (push L (push (Name.check I) (fun _ => Name.check ρ))))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    rcases i with _|_|_|_|i
    exact hf; exact hD; exact hL; exact hcheck hI; exact hcheck hρ
  have hs (G : GenericFilter (Conditions c)) (hG : GroundGeneric M G) :
      degreeExtensionFormula.Eval (fun i => (e i).val G.carrier) ↔
        OwnDegreeExtension (genericExtensionSet M c G.carrier) I ρ (f.val G.carrier) := by
    obtain ⟨q,hq⟩ := G.nonempty
    have ht := G.upper le_top hq
    have hv : (fun i => (e i).val G.carrier) =
        cons (f.val G.carrier) (cons (D.val G.carrier) (cons (L.val G.carrier)
          (cons I (fun _ => ρ)))) := by
      funext i; rcases i with _|_|_|_|i
      rfl; rfl; rfl
      exact Name.val_check G.carrier ht _
      exact Name.val_check G.carrier ht _
    rw [hv,degreeExtensionFormula_spec,hDv G hG ht,hLv G hG ht]
    rfl
  have hsym : ∀ w ∈ M, ∀ a : Conditions c ≃o Conditions c,
      (∀ s t, ZFSet.pair (label c s) (label c t) ∈ w ↔ t = a s) →
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        (degreeExtensionFormula.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          degreeExtensionFormula.Eval (fun i => (e i).val G.carrier)) := by
    intro w hw a ha G hG
    have hH := InternalOrderIsoTransport.map_ground_generic M c c w hM hT hc hc hw a ha G hG
    rw [hs _ hH,hs G hG,InternalOrderIsoTransport.extension_eq M c c w hM hT hc hc hw a ha G hG,
      hinv w hw a ha G hG]
  have hall := (all_generics_of_internal_symmetry M c hM hT hct hc hom
    degreeExtensionFormula e he hsym G₀ hG₀ ((hs G₀ hG₀).mpr h₀)).2
  exact fun G hG => (hs G hG).mp (hall G hG)

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformCohenDefinitionExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing BoundedForcing
open CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem uniform_cohen_definition_extension_oai (M A I ρ : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hA : A ∈ M) (hI : I ∈ M) (hρ : ρ ∈ M)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{0}) (hX : X ∈ M)
    (φ : ElementaryModel.SentenceForm)
    (G₀ : GenericFilter (Conditions (conditions A))) (hG₀ : GroundGeneric M G₀)
    (h₀ : OwnDegreeExtension (genericExtensionSet M (conditions A) G₀.carrier) I ρ
      (definedSubset (level (groundReals (genericExtensionSet M (conditions A) G₀.carrier)) δ)
        φ (fun _ : Fin φ.bound => X))) :
    ∃ f : Name (Conditions (conditions A)), f.encode (label (conditions A)) ∈ M ∧
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        f.val G.carrier = definedSubset
          (level (groundReals (genericExtensionSet M (conditions A) G.carrier)) δ)
            φ (fun _ : Fin φ.bound => X) ∧
        OwnDegreeExtension (genericExtensionSet M (conditions A) G.carrier) I ρ (f.val G.carrier) := by
  have hc := conditions_mem M A hM hT hA
  obtain ⟨f,hf,hfv,hinv⟩ := uniform_ordinal_definition_symmetric M (conditions A)
    hM hT hc δ hδ X hX φ
  have hf₀ : OwnDegreeExtension (genericExtensionSet M (conditions A) G₀.carrier) I ρ
      (f.val G₀.carrier) := by rw [hfv G₀ hG₀]; exact h₀
  have hall := degree_extension_all_generics M (conditions A) I ρ hM hT hct hc hI hρ
    (InternalCohenBitFlip.internally_homogeneous M A hM hT hA) f hf hinv G₀ hG₀ hf₀
  exact ⟨f,hf,fun G hG => ⟨hfv G hG,hall G hG⟩⟩

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension_oai := @OAI.TuringRigidity.RelativeConstructible.uniform_cohen_definition_extension_oai
