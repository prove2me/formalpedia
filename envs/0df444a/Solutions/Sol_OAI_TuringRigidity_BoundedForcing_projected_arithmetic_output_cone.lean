-- Prove2me | solution 1 for OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:55:32.301456+00:00
-- url     : https://prove2.me/submissions/cd5dc883-830a-4901-850e-e8061e2b9b11

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_CohenProjectedNameLift_lift_projected_real_name
import Theorems.Thm_OAI_TuringRigidity_ProjectedArithmeticOutputName_representative_in_model

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

end TuringRigidity.InternalCohenBitFlip

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenRestriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenRestriction
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode CohenGroundPoset
open InternalCohen (alphabet)

theorem restrictionFormula_spec (B V p q : ℕ) (e : ℕ → ZFSet.{0}) (hV : e V = alphabet) :
    (restrictionFormula B V p q).Eval e ↔ e q = restrict (e B) (e p) := by
  simp only [restrictionFormula,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,hV]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro z
    exact ⟨fun hz => ZFSet.mem_sep.mpr ⟨hsub hz,(h z (hsub hz)).mp hz⟩,
      fun hz => (h z (ZFSet.mem_sep.mp hz).1).mpr (ZFSet.mem_sep.mp hz).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hz => (ZFSet.mem_sep.mp hz).1,
      fun z hz => ZFSet.mem_sep.trans (and_iff_right hz)⟩

theorem pair_restrictionGraph (A B p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ restrictionGraph A B ↔
      p ∈ conditions A ∧ q ∈ conditions B ∧ q = restrict B p := by
  simp only [restrictionGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,hr⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,hr⟩
  · rintro ⟨hp,hq,hr⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,hr⟩

theorem restrictionGraph_mem (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) : restrictionGraph A B ∈ M := by
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  let e := cons (conditions A) (cons (conditions B) (cons B (fun _ => alphabet)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact hcA; exact hcB; exact hB; exact InternalCohen.alphabet_mem M hM hT
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (restrictionFormula 5 6 1 0)))) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hcB)
  have hs (z p q : ZFSet.{0}) :=
    restrictionFormula_spec 5 6 1 0 (cons q (cons p (cons z e))) rfl
  simpa only [restrictionGraph,Formula.Eval,Formula.eval_orderedPair,
    hs,cons_zero,cons_succ,e] using hh

end TuringRigidity.InternalCohenRestriction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenProjectedGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenProjectedGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing AutomorphismName
open CohenGroundPoset InternalCohenRestriction InternalCohenPartition InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem mem_projected (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (q : Conditions (conditions B)) :
    q ∈ (projected A B hBA G).carrier ↔ ∃ p ∈ G.carrier, project A B hBA p = q := by
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨(factorIso A B hBA).symm (q,r),hr,?_⟩
    exact congrArg Prod.fst ((factorIso A B hBA).apply_symm_apply (q,r))
  · rintro ⟨p,hp,rfl⟩
    refine ⟨(factorIso A B hBA p).2,?_⟩
    change (factorIso A B hBA).symm (factorIso A B hBA p) ∈ G.carrier
    simpa using hp

theorem densePreimage_mem (M A B D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hD : D ∈ M) : densePreimage A B D ∈ M := by
  have hc := conditions_mem M B hM hT hB
  have hR := restrictionGraph_mem M A B hM hT hA hB
  let e := cons (conditions B) (cons (restrictionGraph A B) (fun _ => D))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    exact hc; exact hR; exact hD
  simpa only [densePreimage,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.pairMem 1 0 3) (.member 0 4))) e he
      (conditions_mem M A hM hT hA)

theorem label_densePreimage (A B D : ZFSet.{0}) (hBA : B ⊆ A)
    (p : Conditions (conditions A)) :
    label _ p ∈ densePreimage A B D ↔ label _ (project A B hBA p) ∈ D := by
  rw [densePreimage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,_,hq,hqD⟩
    have he := ((pair_restrictionGraph A B _ q).mp hq).2.2
    rw [label_project,←he]; exact hqD
  · intro h
    exact ⟨label_mem _ p,label _ (project A B hBA p),label_mem _ _,
      (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩,h⟩

theorem densePreimage_dense (A B D : ZFSet.{0}) (hBA : B ⊆ A)
    (hD : Dense {q : Conditions (conditions B) | label _ q ∈ D}) :
    Dense {p : Conditions (conditions A) | label _ p ∈ densePreimage A B D} := by
  intro p
  let e := factorIso A B hBA
  obtain ⟨q,hq,hqD⟩ := hD (e p).1
  let r := e.symm (q,(e p).2)
  have hr : e r = (q,(e p).2) := e.apply_symm_apply _
  refine ⟨r,?_,?_⟩
  · apply e.le_iff_le.mp
    rw [hr]
    exact ⟨hq,le_rfl⟩
  · apply (label_densePreimage A B D hBA r).mpr
    have he := congrArg Prod.fst hr
    change project A B hBA r = q at he
    rw [he]; exact hqD

theorem projected_groundGeneric (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (projected A B hBA G) := by
  intro D hD hd
  obtain ⟨p,hp,hpD⟩ := hG (densePreimage A B D) (densePreimage_mem M A B D hM hT hA hB hD)
    (densePreimage_dense A B D hBA hd)
  exact ⟨project A B hBA p,(mem_projected A B hBA G _).mpr ⟨p,hp,rfl⟩,
    (label_densePreimage A B D hBA p).mp hpD⟩

theorem projected_contains (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) {p : Conditions (conditions A)}
    (hp : p ∈ G.carrier) : project A B hBA p ∈ (projected A B hBA G).carrier :=
  (mem_projected A B hBA G _).mpr ⟨p,hp,rfl⟩

end TuringRigidity.InternalCohenProjectedGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenTailHomogeneity
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenTailHomogeneity
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohenBitFlip InternalCohenRestriction
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder Classical.propDecidable

theorem tailMatchingSet_mem (M A B p q : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hp : p ∈ M) (hq : q ∈ M) :
    tailMatchingSet A B p q ∈ M := by
  simpa only [tailMatchingSet,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.neg (.member 0 1))
      (fun _ => B) (fun _ => hB) (matchingSet_mem M A p q hM hT hA hp hq)

theorem restrict_flip (A B C : ZFSet.{0}) (hBA : B ⊆ A)
    (hBC : ∀ x ∈ B, x ∉ C) (s : Conditions (conditions A)) :
    restrict B (label _ (InternalCohenBitFlip.flipIso A C s)) = restrict B (label _ s) := by
  classical
  have hf := ((pair_flipGraph A C _ _).mp
    ((flipGraph_spec A C s (InternalCohenBitFlip.flipIso A C s)).mpr rfl)).2.2
  apply ZFSet.ext; intro z
  by_cases hz : z ∈ ZFSet.prod B alphabet
  · obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp hz
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    have h := hf x (hBA hx)
    have hb' : bitSet b ∈ alphabet := (mem_alphabet _).mpr ⟨b,rfl⟩
    cases b
    · simpa only [pair_restrict,hx,hb',and_true,hBC x hx,false_and,true_and,
        false_or,not_false_eq_true] using h.1
    · simpa only [pair_restrict,hx,hb',and_true,hBC x hx,false_and,true_and,
        false_or,not_false_eq_true] using h.2
  · simp only [mem_restrict,hz,and_false]

theorem mask_tailMatchingSet (A B : ZFSet.{0})
    (p q : Condition (Conditions A)) (i : Conditions A) :
    mask A (tailMatchingSet A B (graph A p) (graph A q)) i =
      if label A i ∈ B then false else matchingMask p q i := by
  classical
  by_cases hi : label A i ∈ B
  · simp [mask,tailMatchingSet,hi]
  · rw [ite_eq_right hi,← congrFun (mask_matchingSet A p q) i]
    simp only [mask,tailMatchingSet,ZFSet.mem_sep,hi,not_false_eq_true,and_true]

theorem tail_matching_compatible (A B : ZFSet.{0})
    (p q : Condition (Conditions A))
    (hpq : restrict B (graph A p) ⊆ restrict B (graph A q)) :
    Compatible (flip (mask A (tailMatchingSet A B (graph A p) (graph A q))) p) q := by
  classical
  intro i a b ha hb
  by_cases hi : label A i ∈ B
  · have hm : mask A (tailMatchingSet A B (graph A p) (graph A q)) i = false := by
      rw [mask_tailMatchingSet,ite_eq_left hi]
    have hp : p.val i = some a := by simpa [CohenSymmetry.flip,hm] using ha
    have hpair := hpq ((pair_restrict B (graph A p) (label A i) (bitSet a)).mpr
      ⟨(pair_mem_graph A p i a).mpr hp,hi,(mem_alphabet _).mpr ⟨a,rfl⟩⟩)
    have hq := (pair_mem_graph A q i a).mp ((pair_restrict _ _ _ _).mp hpair).1
    exact Option.some.inj (hq.symm.trans hb)
  · have hm : mask A (tailMatchingSet A B (graph A p) (graph A q)) i =
        matchingMask p q i := by rw [mask_tailMatchingSet,ite_eq_right hi]
    exact matching_compatible p q i a b (by simpa only [CohenSymmetry.flip,hm] using ha) hb

theorem tail_matching_common_extension (A B : ZFSet.{0})
    (p q : Conditions (conditions A))
    (hpq : restrict B (label _ p) ⊆ restrict B (label _ q)) :
    ∃ r, r ≤ InternalCohenBitFlip.flipIso A
      (tailMatchingSet A B (label _ p) (label _ q)) p ∧ r ≤ q := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv A).surjective q
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv A q) = graph A q := label_encode A q
  rw [hp,hq] at hpq ⊢
  let m := mask A (tailMatchingSet A B (graph A p) (graph A q))
  refine ⟨conditionEquiv A (merge (flip m p) q),?_,
    (conditionEquiv A).monotone (merge_le_right (tail_matching_compatible A B p q hpq))⟩
  change conditionEquiv A (merge (flip m p) q) ≤
    conditionEquiv A (flip m ((conditionEquiv A).symm (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply]
  exact (conditionEquiv A).monotone (merge_le_left _ _)

theorem internally_tail_homogeneous (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M)
    (hBA : B ⊆ A) (p q : Conditions (conditions A))
    (hpq : restrict B (label _ p) ⊆ restrict B (label _ q)) :
    ∃ w ∈ M, ∃ e : Conditions (conditions A) ≃o Conditions (conditions A),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = e s) ∧
      (∀ s, restrict B (label _ (e s)) = restrict B (label _ s)) ∧
      ∃ r, r ≤ e p ∧ r ≤ q := by
  let C := tailMatchingSet A B (label _ p) (label _ q)
  have hc := conditions_mem M A hM hT hA
  have hC : C ∈ M := tailMatchingSet_mem M A B _ _ hM hT hA hB
    (hM _ hc _ (label_mem _ p)) (hM _ hc _ (label_mem _ q))
  refine ⟨flipGraph A C,flipGraph_mem M A C hM hT hA hC,
    InternalCohenBitFlip.flipIso A C,flipGraph_spec A C,?_,
    tail_matching_common_extension A B p q hpq⟩
  exact restrict_flip A B C hBA (fun x hx h => (ZFSet.mem_sep.mp h).2 hx)

end TuringRigidity.InternalCohenTailHomogeneity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenProjectionSymmetry
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenProjectionSymmetry
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AutomorphismName
open CohenGroundPoset InternalCohenRestriction InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem projected_cone_iff (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (p : Conditions (conditions A)) :
    project A B hBA p ∈ (projected A B hBA G).carrier ↔
      ∃ q ∈ G.carrier, restrict B (label _ p) ⊆ restrict B (label _ q) := by
  constructor
  · intro hp
    obtain ⟨q,hq,he⟩ := (mem_projected A B hBA G _).mp hp
    refine ⟨q,hq,?_⟩
    have hh := congrArg (label (conditions B)) he
    rw [label_project,label_project] at hh
    rw [hh]
  · rintro ⟨q,hq,hpq⟩
    apply (projected A B hBA G).upper (p := project A B hBA q)
    · change label _ (project A B hBA p) ⊆ label _ (project A B hBA q)
      simpa only [label_project] using hpq
    · exact projected_contains A B hBA G hq

end TuringRigidity.InternalCohenProjectionSymmetry

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

theorem halts_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c e n : ℕ → ℕ} (hc : Primrec c) (he : Primrec e) (hn : Primrec n) :
    Arith (fun O v => Halts (B O (c v)) (e v) (n v)) := by
  have h := (run_arith hB (hc.comp (left_primrec.comp left_primrec))
    (he.comp (left_primrec.comp left_primrec))
    (hn.comp (left_primrec.comp left_primrec)) (right_primrec.comp left_primrec)
    right_primrec).ex.ex
  exact h.congr (fun _ _ => by simp only [Halts,left,right,Nat.unpair_pair,Option.mem_def])

theorem jump_arith {B : OracleFamily} (hB : ArithmeticOracle B) :
    ArithmeticOracle (fun O v => jump (B O v)) :=
  (halts_arith hB left_primrec (left_primrec.comp right_primrec)
    (right_primrec.comp right_primrec)).congr (fun _ _ => by simp [jump])

theorem iterate_arith {B : OracleFamily} (hB : ArithmeticOracle B) (k : ℕ) :
    ArithmeticOracle (fun O v => iterate (B O v) k) := by
  induction k with
  | zero => exact hB
  | succ k ih => exact jump_arith ih

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelReals
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelReals
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding
universe u
noncomputable section

theorem realSet_subset (A : Oracle) : realSet.{u} A ⊆ ZFSet.omega :=
  fun _ h => (ZFSet.mem_sep.mp h).1

theorem realSet_oracleOf {x : ZFSet.{u}} (hx : x ⊆ ZFSet.omega) :
    realSet (oracleOf x) = x := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨n,rfl⟩ := (mem_omega y).mp (realSet_subset _ hy)
    simpa [oracleOf] using (nat_mem_realSet _ n).mp hy
  · intro hy
    obtain ⟨n,rfl⟩ := (mem_omega y).mp (hx hy)
    apply (nat_mem_realSet _ _).mpr
    simpa [oracleOf] using hy

end
end TuringRigidity.SetModelReals

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTTreeAbsoluteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelFunctions SetModelReals SetModelSyntax RelationCollapse
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

theorem sourceContext (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) : Context M :=
  ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetDegreeDecoding
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetDegreeDecoding
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding SetModelReals
open PersistentRestrictions PersistentPresentation
universe u
noncomputable section

@[simp] theorem real_mem_degreeSet (A : Oracle) (a : Degree) :
    realSet.{u} A ∈ degreeSet a ↔ degree A = a := by
  simp only [degreeSet,ZFSet.mem_sep,ZFSet.mem_powerset,oracleOf_realSet]
  exact and_iff_right (realSet_subset A)

theorem mem_degreeSet (a : Degree) (x : ZFSet.{u}) :
    x ∈ degreeSet a ↔ ∃ A, x = realSet A ∧ degree A = a := by
  constructor
  · intro hx
    obtain ⟨hs,he⟩ := ZFSet.mem_sep.mp hx
    exact ⟨oracleOf x,(realSet_oracleOf (ZFSet.mem_powerset.mp hs)).symm,he⟩
  · rintro ⟨A,rfl,he⟩
    exact (real_mem_degreeSet A a).mpr he

theorem degreeSet_injective : Function.Injective degreeSet.{u} := by
  intro a b he
  obtain ⟨A,rfl⟩ := degree_surjective a
  exact (real_mem_degreeSet A b).mp (he ▸ (real_mem_degreeSet A (degree A)).mpr rfl)

end
end TuringRigidity.SetDegreeDecoding

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeUniverse
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
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

theorem internal_degreeUniverse (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ w ∈ R, ∃ B : Oracle, realCode B = w) : degreeUniverse R ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet hS hω
  obtain ⟨P,hPM,hP⟩ := internal_power M hM hT.powerSet hRM
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  have hsub : degreeUniverse R ⊆ P := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := (mem_degreeUniverse R D).mp hD
    exact (hP _).mpr ⟨internal_degreeCode M hM hT R hRM hR (hM _ hRM _ hA),
      degreeCode_subset R A⟩
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => R)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hω
    rcases i with _|i; exact hQM
    rcases i with _|i; exact hz
    exact hRM
  have hs := sep_mem M hM hS (Formula.degreeUniverseMember φ 1 2 3 4 0) e he hPM
  have heq : ZFSet.sep (fun D => (Formula.degreeUniverseMember φ 1 2 3 4 0).Eval (cons D e)) P =
      degreeUniverse R := by
    apply ZFSet.ext; intro D
    rw [ZFSet.mem_sep,Formula.degreeUniverseMember_spec hφ 1 2 3 4 0 (cons D e) rfl hQ rfl hR]
    exact ⟨And.right,fun h => ⟨hsub h,h⟩⟩
  exact heq ▸ hs

end TuringRigidity.BoundedSetTheory

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenTailTruth
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenTailHomogeneity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem weak_of_internal_tail_symmetry (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions (conditions A)))
    (he : ∀ i, (e i).encode (label (conditions A)) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions (conditions A) ≃o Conditions (conditions A),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = a s) →
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        (φ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          φ.Eval (fun i => (e i).val G.carrier)))
    (p q : Conditions (conditions A)) (hp : Forces e φ p)
    (hpq : restrict B (label _ p) ⊆ restrict B (label _ q)) :
    Forces e (.neg (.neg φ)) q := by
  have hc := conditions_mem M A hM hT hA
  have truthAt (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G)
      (ψ : BoundedSetTheory.Formula) := internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
    (InternalCollapse.orderSet_mem M hM hT hc) (InternalCollapse.orderSet_pair _)
    G hG ψ e he
  intro u hu hn
  have hpu : restrict B (label _ p) ⊆ restrict B (label _ u) :=
    fun z hz => restrict_mono B _ _ hu (hpq hz)
  obtain ⟨w,hw,a,ha,hfix,r,hrp,hru⟩ :=
    internally_tail_homogeneous M A B hM hT hA hB hBA p u hpu
  obtain ⟨G,hr,hG⟩ := ArithmeticTree.countable_ground_generic M hct ⟨conditions A,hc⟩ (a.symm r)
  have hpG : p ∈ G.carrier := G.upper (by simpa using a.symm.monotone hrp) hr
  have hval := (truthAt G hG φ).mpr ⟨p,hpG,hp⟩
  let H := AutomorphismName.mapFilter a G
  have hH : GroundGeneric M H :=
    InternalOrderIsoTransport.map_ground_generic M _ _ w hM hT hc hc hw a ha G hG
  have hrH : r ∈ H.carrier := hr
  have huH : u ∈ H.carrier := H.upper hru hrH
  have hnot := (truthAt H hH (.neg φ)).mpr ⟨u,huH,hn⟩
  exact hnot ((hinv w hw a ha hfix G hG).mpr hval)

theorem cone_truth_of_internal_tail_symmetry (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (φ : BoundedSetTheory.Formula) (e : ℕ → Name (Conditions (conditions A)))
    (he : ∀ i, (e i).encode (label (conditions A)) ∈ M)
    (hinv : ∀ w ∈ M, ∀ a : Conditions (conditions A) ≃o Conditions (conditions A),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = a s) →
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        (φ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a G).carrier) ↔
          φ.Eval (fun i => (e i).val G.carrier)))
    (p : Conditions (conditions A)) (hp : Forces e φ p)
    (G : GenericFilter (Conditions (conditions A))) (hG : GroundGeneric M G)
    (hcone : ∃ q ∈ G.carrier, restrict B (label _ p) ⊆ restrict B (label _ q)) :
    φ.Eval (fun i => (e i).val G.carrier) := by
  classical
  obtain ⟨q,hq,hpq⟩ := hcone
  have hw := weak_of_internal_tail_symmetry M A B hM hT hct hA hB hBA φ e he hinv p q hp hpq
  have hc := conditions_mem M A hM hT hA
  have hv := (internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
    (InternalCollapse.orderSet_mem M hM hT hc) (InternalCollapse.orderSet_pair _)
    G hG (.neg (.neg φ)) e he).mpr ⟨q,hq,hw⟩
  exact not_not.mp hv

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticOutputSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ExtensionArithmeticRepresentative
open OracleJump UniformArithmetic CommonIdeal IndexMatrix TableIndices BoundedSetTheory Encodable
open PersistentRestrictions

theorem fixed_output_arithmetic (d k : ℕ) :
    Arith (fun O _ => Represents (iterate (join (O 0) (O 1)) k) (machine d) (O 2)) :=
  represents_arith (parameter_arith 2)
    (iterate_arith (join_arith (parameter_arith 0) (parameter_arith 1)) k) (Primrec.const d)

theorem fixed_output_bounded (d k : ℕ) :
    ∃ φ : Formula, DefinesArithmetic.{0} φ
      (fun O _ => Represents (iterate (join (O 0) (O 1)) k) (machine d) (O 2)) :=
  arithmetic_bounded_definition (fixed_output_arithmetic d k)

end TuringRigidity.ExtensionArithmeticRepresentative

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

theorem groundReals_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    groundReals M ∈ M := by
  obtain ⟨R,hR,hdef⟩ := internal_power M hM hT.powerSet (sourceT_omega_mem M hM hT)
  have heq : R = groundReals M := by
    apply ZFSet.ext; intro x
    exact (hdef x).trans (mem_groundReals M x).symm
  exact heq ▸ hR

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeOrder
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic
universe u

theorem degreeCodeLE_actual (R : ZFSet.{u}) {A B : Oracle}
    (hA : realCode A ∈ R) (hB : realCode B ∈ R) :
    degreeCodeLE (degreeCode R A) (degreeCode R B) ↔ degree A ≤ degree B := by
  constructor
  · rintro ⟨C,D,hC,hD,hCD⟩
    have heC := ((realCode_mem_degreeCode R A C).mp hC).2
    have heD := ((realCode_mem_degreeCode R B D).mp hD).2
    rw [←heC,←heD]
    exact hCD
  · intro h
    exact ⟨A,B,(realCode_mem_degreeCode R A A).mpr ⟨hA,rfl⟩,
      (realCode_mem_degreeCode R B B).mpr ⟨hB,rfl⟩,h⟩

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

theorem degreeOrder_actual (R : ZFSet.{u}) {A B : Oracle}
    (hA : realCode A ∈ R) (hB : realCode B ∈ R) :
    ZFSet.pair (degreeCode R A) (degreeCode R B) ∈ degreeOrder R ↔ degree A ≤ degree B := by
  rw [mem_degreeOrder,degreeCodeLE_actual R hA hB]
  exact ⟨fun h => h.2.2,fun h => ⟨(mem_degreeUniverse _ _).mpr ⟨A,hA,rfl⟩,
    (mem_degreeUniverse _ _).mpr ⟨B,hB,rfl⟩,h⟩⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelCountability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open BoundedDefinability SetModelSyntax SetDegreeDecoding SetModelSequences
open PersistentRestrictions PersistentPresentation EncodedForcing
universe u
noncomputable section

variable {M : ZFSet.{u}}

theorem FunctionGraph.unique {f a b x y z : ZFSet.{u}} (h : FunctionGraph f a b)
    (hx : x ∈ a) (hy : y ∈ b) (hz : z ∈ b)
    (hxy : ZFSet.pair x y ∈ f) (hxz : ZFSet.pair x z ∈ f) : y = z := by
  obtain ⟨v,hv,hxv,hu⟩ := h.2 x hx
  exact (hu y hy hxy).trans (hu z hz hxz).symm

end
end TuringRigidity.SetModelCountability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelDegreeUniverse
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetPresentationDecoding SetDegreeDecoding UniformArithmetic
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem represented_of_degreeSet_mem (C : Context M) {a : Degree}
    (ha : degreeSet.{u} a ∈ M) : ∃ A ∈ reals M, degree A = a := by
  obtain ⟨A,rfl⟩ := degree_surjective a
  exact ⟨A,C.transitive _ ha _ ((real_mem_degreeSet A _).mpr rfl),rfl⟩

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelIdealSatisfaction
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem order_code (C : Context M) {L : ZFSet.{u}}
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    {a b : Degree} (ha : degreeSet.{u} a ∈ M) (hb : degreeSet.{u} b ∈ M) :
    ZFSet.pair (degreeSet a) (degreeSet b) ∈ L ↔ a ≤ b := by
  obtain ⟨A,hA,rfl⟩ := represented_of_degreeSet_mem C ha
  obtain ⟨B,hB,rfl⟩ := represented_of_degreeSet_mem C hb
  exact hL A hA B hB

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelActionSatisfaction
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem action_code {I : CountableIdeal} (ρ : I ≃o I) (a b : I) :
    ZFSet.pair (degreeSet.{u} a.val) (degreeSet b.val) ∈ automorphismSet ρ ↔ ρ a = b := by
  rw [mem_automorphismSet]
  constructor
  · rintro ⟨c,he⟩
    obtain ⟨ha,hb⟩ := ZFSet.pair_inj.mp he
    have ha' : a=c := Subtype.ext (degreeSet_injective ha)
    have hb' : b=ρ c := Subtype.ext (degreeSet_injective hb)
    rw [ha',hb']
  · intro h
    exact ⟨a,by rw [h]⟩

theorem action_satisfaction (C : Context M) {L : ZFSet.{u}}
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    {I : CountableIdeal} (hI : idealSet I ∈ M) (ρ : I ≃o I) :
    IsAction (automorphismSet ρ) (idealSet I) L := by
  have hm (a : I) : degreeSet.{u} a.val ∈ M :=
    C.transitive _ hI _ ((mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩)
  have hi (a : I) : degreeSet.{u} a.val ∈ idealSet I :=
    (mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro z hz
    obtain ⟨a,rfl⟩ := (mem_automorphismSet ρ z).mp hz
    exact ⟨degreeSet a.val,hi a,degreeSet (ρ a).val,hi (ρ a),rfl⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
    let a' : I := ⟨a,ha⟩
    refine ⟨degreeSet (ρ a').val,hi (ρ a'),(action_code ρ a' (ρ a')).mpr rfl,?_⟩
    intro z hz hxz
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I z).mp hz
    have hh := (action_code ρ a' ⟨b,hb⟩).mp hxz
    exact congrArg (fun c : I => degreeSet c.val) hh.symm
  · intro y hy
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I y).mp hy
    let b' : I := ⟨b,hb⟩
    exact ⟨degreeSet (ρ.symm b').val,hi (ρ.symm b'),
      (action_code ρ (ρ.symm b') b').mpr (ρ.apply_symm_apply b')⟩
  · intro x hx y hy a ha b hb hab
    obtain ⟨x,hxc,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨y,hyc,rfl⟩ := (mem_idealSet I y).mp hy
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I a).mp ha
    obtain ⟨b,hbc,rfl⟩ := (mem_idealSet I b).mp hb
    have hxa := (action_code ρ ⟨x,hxc⟩ ⟨a,hac⟩).mp hab.1
    have hyb := (action_code ρ ⟨y,hyc⟩ ⟨b,hbc⟩).mp hab.2
    rw [order_code C hL (hm ⟨x,hxc⟩) (hm ⟨y,hyc⟩),
      order_code C hL (hm ⟨a,hac⟩) (hm ⟨b,hbc⟩)]
    change (⟨x,hxc⟩ : I) ≤ ⟨y,hyc⟩ ↔ (⟨a,hac⟩ : I) ≤ ⟨b,hbc⟩
    rw [←hxa,←hyb]
    exact ρ.le_iff_le.symm

theorem extends_sets {I J : CountableIdeal} {ρ : I ≃o I} {σ : J ≃o J}
    {hIJ : I.carrier ⊆ J.carrier} (he : Extends hIJ ρ σ) :
    automorphismSet.{u} ρ ⊆ automorphismSet σ := by
  intro z hz
  obtain ⟨a,rfl⟩ := (mem_automorphismSet ρ z).mp hz
  exact (mem_automorphismSet σ _).mpr ⟨⟨a.val,hIJ a.property⟩,by rw [he a]⟩

theorem ideal_subset {I J : CountableIdeal} (h : I.carrier ⊆ J.carrier) :
    idealSet.{u} I ⊆ idealSet J := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
  exact (mem_idealSet J _).mpr ⟨a,h ha,rfl⟩

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelActionDecoding
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section

theorem decode_action {M : ZFSet.{u}} (C : Context M) {L f : ZFSet.{u}}
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hIM : idealSet I ∈ M) (ha : IsAction f (idealSet I) L) :
    ∃ ρ : I ≃o I, automorphismSet ρ = f := by
  have hi (a : I) : degreeSet.{u} a.val ∈ idealSet I :=
    (mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩
  have hm (a : I) : degreeSet.{u} a.val ∈ M := C.transitive _ hIM _ (hi a)
  have hex (a : I) : ∃ b : I, ZFSet.pair (degreeSet.{u} a.val) (degreeSet b.val) ∈ f := by
    obtain ⟨y,hy,hxy,_⟩ := ha.1.1.2 _ (hi a)
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I y).mp hy
    exact ⟨⟨b,hb⟩,hxy⟩
  choose F hF using hex
  have hle (a b : I) : F a ≤ F b ↔ a ≤ b := by
    have hh := ha.2 _ (hi a) _ (hi b) _ (hi (F a)) _ (hi (F b)) ⟨hF a,hF b⟩
    rw [order_code C hL (hm a) (hm b),order_code C hL (hm (F a)) (hm (F b))] at hh
    exact hh.symm
  have hinj : Function.Injective F := by
    intro a b he
    exact le_antisymm ((hle a b).mp (le_of_eq he)) ((hle b a).mp (le_of_eq he.symm))
  have hsurj : Function.Surjective F := by
    intro b
    obtain ⟨x,hx,hxb⟩ := ha.1.2 _ (hi b)
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I x).mp hx
    refine ⟨⟨a,hac⟩,Subtype.ext (degreeSet_injective ?_)⟩
    exact ha.1.1.unique (hi ⟨a,hac⟩) (hi (F ⟨a,hac⟩)) (hi b) (hF ⟨a,hac⟩) hxb
  let ρ : I ≃o I := { toEquiv := Equiv.ofBijective F ⟨hinj,hsurj⟩, map_rel_iff' := by intro a b; exact hle a b }
  have hpair (a b : I) : ZFSet.pair (degreeSet.{u} a.val) (degreeSet b.val) ∈ f ↔ ρ a = b := by
    constructor
    · intro hab
      apply Subtype.ext
      apply degreeSet_injective
      exact ha.1.1.unique (hi a) (hi (F a)) (hi b) (hF a) hab
    · intro he
      have he' : F a = b := he
      simpa only [he'] using hF a
  refine ⟨ρ,ZFSet.ext (fun z => ?_)⟩
  constructor
  · intro hz
    obtain ⟨a,rfl⟩ := (mem_automorphismSet ρ z).mp hz
    exact (hpair a (ρ a)).mpr rfl
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ha.1.1.1 z hz
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨b,hbc,rfl⟩ := (mem_idealSet I y).mp hy
    exact (action_code ρ ⟨a,hac⟩ ⟨b,hbc⟩).mpr ((hpair ⟨a,hac⟩ ⟨b,hbc⟩).mp hz)

theorem ideal_subset_iff {I J : CountableIdeal} :
    idealSet.{u} I ⊆ idealSet J ↔ I.carrier ⊆ J.carrier := by
  constructor
  · intro h a ha
    obtain ⟨b,hb,he⟩ := (mem_idealSet J _).mp (h ((mem_idealSet I _).mpr ⟨a,ha,rfl⟩))
    exact (degreeSet_injective he).symm ▸ hb
  · exact ideal_subset

theorem extends_sets_iff {I J : CountableIdeal} (hIJ : I.carrier ⊆ J.carrier)
    (ρ : I ≃o I) (σ : J ≃o J) :
    automorphismSet.{u} ρ ⊆ automorphismSet σ ↔ Extends hIJ ρ σ := by
  constructor
  · intro h a
    have hh := h ((mem_automorphismSet ρ _).mpr ⟨a,rfl⟩)
    have he := (action_code σ ⟨a.val,hIJ a.property⟩ ⟨(ρ a).val,hIJ (ρ a).property⟩).mp hh
    exact congrArg Subtype.val he
  · exact extends_sets

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_NativeModelCompatibility
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel SetModelReals SetDegreeDecoding PersistentRestrictions PersistentPresentation
universe u

theorem degreeCode_eq_degreeSet (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u}) (hS : ∀ A : Oracle, realCode A ∈ S ↔ A ∈ modelReals M)
    {A : Oracle} (hA : A ∈ modelReals M) : degreeCode S A = degreeSet (degree A) := by
  apply ZFSet.ext; intro x
  rw [degreeCode,ZFSet.mem_sep,mem_degreeSet]
  constructor
  · rintro ⟨_,B,hB,hBA⟩
    exact ⟨B,hB,hBA⟩
  · rintro ⟨B,rfl,hBA⟩
    have hB := sourceT_real_lower M hM hT hA ((degree_eq_iff B A).mp hBA).1
    exact ⟨(hS B).mpr hB,B,rfl,hBA⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_AmbientDegreeActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel SetDegreeDecoding
universe u

theorem ownRealPower_codes (M R : ZFSet.{u})
    (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M := by
  intro A
  exact (hR _).trans (and_iff_left (realCode_subset A))

theorem ownDegreeUniverse_actual (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    ∀ x, x ∈ degreeUniverse R ↔
      ∃ A ∈ SetModelReals.reals M, x = degreeSet (degree A) := by
  intro x
  rw [mem_degreeUniverse]
  have hr := ownRealPower_codes M R hR
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact ⟨A,(hr A).mp hA,degreeCode_eq_degreeSet M hM hT R hr ((hr A).mp hA)⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨A,(hr A).mpr hA,(degreeCode_eq_degreeSet M hM hT R hr hA).symm⟩

theorem ownDegreeOrder_actual (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    ∀ A ∈ SetModelReals.reals M, ∀ B ∈ SetModelReals.reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ degreeOrder R ↔
        Reduces A B := by
  intro A hA B hB
  have hr := ownRealPower_codes M R hR
  rw [←degreeCode_eq_degreeSet M hM hT R hr hA,
    ←degreeCode_eq_degreeSet M hM hT R hr hB]
  exact degreeOrder_actual R ((hr A).mpr hA) ((hr B).mpr hB)

end TuringRigidity.FullSetForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_AmbientExtensionBody
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
open SetDegreeDecoding PersistentRestrictions SetModelSatisfaction ArithmeticTree
universe u

theorem ownDegreeUniverse_eq_idealSet (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (R : ZFSet.{u})
    (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    degreeUniverse R = idealSet (modelIdeal M hM hT) := by
  apply ZFSet.ext
  intro x
  rw [ownDegreeUniverse_actual M hM hT R hR, mem_idealSet]
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact ⟨degree A,⟨A,hA,rfl⟩,rfl⟩
  · rintro ⟨d,⟨A,hA,rfl⟩,rfl⟩
    exact ⟨A,hA,rfl⟩

end TuringRigidity.FullSetForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OwnDegreeExtensionMeaning
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open TransitiveNameModel BoundedSetTheory SetDegreeDecoding PersistentRestrictions SetModelSatisfaction
open RelativeConstructible FullSetForcing ElementaryModel
universe u

theorem own_degree_extension_iff (E : ZFSet.{0}) [Countable (Conditions E)]
    (hE : Transitive E) (hTE : SourceT E) (I : CountableIdeal) (ρ : I ≃o I) (f : ZFSet.{0}) :
    OwnDegreeExtension E (idealSet I) (automorphismSet ρ) f ↔
      ∃ hIJ : I.carrier ⊆ (modelIdeal E hE hTE).carrier,
        ∃ σ : modelIdeal E hE hTE ≃o modelIdeal E hE hTE,
          automorphismSet σ = f ∧ Extends hIJ ρ σ := by
  have hr : ∀ w ∈ groundReals E, ∃ A : Oracle, realCode A = w := by
    intro w hw
    exact ⟨decodeReal w,realCode_decodeReal ((mem_groundReals E w).mp hw).2⟩
  have hD := internal_degreeUniverse E hE hTE _ (groundReals_mem E hE hTE) hr
  have hd := ownDegreeUniverse_eq_idealSet E hE hTE (groundReals E) (mem_groundReals E)
  have hl := ownDegreeOrder_actual E hE hTE (groundReals E) (mem_groundReals E)
  unfold OwnDegreeExtension
  rw [hd]
  constructor
  · rintro ⟨ha,hij,hext⟩
    have hij' := ideal_subset_iff.mp hij
    obtain ⟨σ,hσ⟩ := decode_action (ArithmeticTree.sourceContext E hE hTE) hl
      (modelIdeal E hE hTE) (hd ▸ hD) ha
    refine ⟨hij',σ,hσ,(extends_sets_iff hij' ρ σ).mp ?_⟩
    rwa [hσ]
  · rintro ⟨hij,σ,hσ,hext⟩
    rw [←hσ]
    exact ⟨action_satisfaction (ArithmeticTree.sourceContext E hE hTE) hl (hd ▸ hD) σ,
      ideal_subset hij,extends_sets hext⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedAutomorphismOutput
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open TransitiveNameModel BoundedSetTheory SetDegreeDecoding PersistentRestrictions
universe u

theorem boundedOutputFormula_raw (f x y D : ZFSet.{u}) :
    boundedOutputFormula.Eval (cons f (cons x (cons y (fun _ => D)))) ↔
      ∃ d ∈ D, ∃ b ∈ D, x ∈ d ∧ y ∈ b ∧ ZFSet.pair d b ∈ f := by
  simp only [boundedOutputFormula,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ]

theorem boundedOutputFormula_spec (I : CountableIdeal) (σ : I ≃o I)
    (A : Oracle) (hA : degree A ∈ I.carrier) (y : ZFSet.{u}) :
    boundedOutputFormula.Eval
      (cons (automorphismSet σ) (cons (realCode A) (cons y (fun _ => idealSet I)))) ↔
      ∃ B : Oracle, realCode B = y ∧ degree B = (σ ⟨degree A,hA⟩).val := by
  rw [boundedOutputFormula_raw]
  constructor
  · rintro ⟨d,_,b,_,had,hbb,hf⟩
    obtain ⟨a,hpair⟩ := (mem_automorphismSet σ _).mp hf
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hpair
    have ha : degree A = a.val := (real_mem_degreeSet A a.val).mp had
    have ha' : (⟨degree A,hA⟩ : I) = a := Subtype.ext ha
    obtain ⟨B,hB,hdeg⟩ := (mem_degreeSet (σ a).val y).mp hbb
    exact ⟨B,hB.symm,by rwa [ha']⟩
  · rintro ⟨B,hB,hdeg⟩
    have hi (a : I) : degreeSet.{u} a.val ∈ idealSet I :=
      (mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩
    refine ⟨degreeSet (degree A),hi ⟨degree A,hA⟩,
      degreeSet (σ ⟨degree A,hA⟩).val,hi (σ ⟨degree A,hA⟩),
      (real_mem_degreeSet A _).mpr rfl,?_,?_⟩
    · rw [←hB]; exact (real_mem_degreeSet B _).mpr hdeg
    · exact (mem_automorphismSet σ _).mpr ⟨⟨degree A,hA⟩,rfl⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_DefinedOutputTailCone
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open InternalCohenProjectionSymmetry InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem defined_output_tail_cone (M C B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : ElementaryModel.SentenceForm)
    (f x y : Name (Conditions (conditions C)))
    (hf : f.encode (label (conditions C)) ∈ M)
    (hx : x.encode (label (conditions C)) ∈ M)
    (hy : y.encode (label (conditions C)) ∈ M)
    (hfv : ∀ G : GenericFilter (Conditions (conditions C)), GroundGeneric M G →
      f.val G.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (conditions C) G.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (hxfix : ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ G : GenericFilter (Conditions (conditions C)),
        x.val (AutomorphismName.mapFilter a G).carrier = x.val G.carrier)
    (hyfix : ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ G : GenericFilter (Conditions (conditions C)),
        y.val (AutomorphismName.mapFilter a G).carrier = y.val G.carrier)
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (houtput : ∃ d ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) G.carrier)),
      ∃ b ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) G.carrier)),
        x.val G.carrier ∈ d ∧ y.val G.carrier ∈ b ∧ ZFSet.pair d b ∈ f.val G.carrier)
    (p₀ : Conditions (conditions C)) (hp₀ : p₀ ∈ G.carrier) :
    ∃ p ∈ G.carrier, p ≤ p₀ ∧
      ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        project C B hBC p ∈ (projected C B hBC H).carrier →
          ∃ d ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
          ∃ b ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
            x.val H.carrier ∈ d ∧ y.val H.carrier ∈ b ∧ ZFSet.pair d b ∈ f.val H.carrier := by
  have hc := conditions_mem M C hM hT hC
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  have ht (H : GenericFilter (Conditions (conditions C))) : ⊤ ∈ H.carrier := by
    obtain ⟨q,hq⟩ := H.nonempty; exact H.upper le_top hq
  obtain ⟨D,hD,hDv⟩ := uniform_degreeUniverse_name M hM hT hc ho (InternalCollapse.orderSet_pair _)
  let e := push f (push x (push y (fun _ => D)))
  have he (i : ℕ) : (e i).encode (label (conditions C)) ∈ M := by
    rcases i with _|_|_|i
    exact hf; exact hx; exact hy; exact hD
  have hev (H : GenericFilter (Conditions (conditions C))) : (fun i => (e i).val H.carrier) =
      cons (f.val H.carrier) (cons (x.val H.carrier) (cons (y.val H.carrier) (fun _ => D.val H.carrier))) := by
    funext i; rcases i with _|_|_|i <;> rfl
  have hinv : ∀ w ∈ M, ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = a s) →
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        (boundedOutputFormula.Eval (fun i => (e i).val (AutomorphismName.mapFilter a H).carrier) ↔
          boundedOutputFormula.Eval (fun i => (e i).val H.carrier)) := by
    intro w hw a ha hfix H hH
    have hHa := InternalOrderIsoTransport.map_ground_generic M _ _ w hM hT hc hc hw a ha H hH
    have hExt := InternalOrderIsoTransport.extension_eq M _ _ w hM hT hc hc hw a ha H hH
    rw [hev _,hev H,hxfix a hfix H,hyfix a hfix H,hfv _ hHa,hfv H hH,
      hDv _ hHa (ht _),hDv H hH (ht H),hExt]
  have hφ : boundedOutputFormula.Eval (fun i => (e i).val G.carrier) := by
    rw [hev G,boundedOutputFormula_raw,hDv G hG (ht G)]
    exact houtput
  obtain ⟨r,hr,hrφ⟩ := (internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc ho
    (InternalCollapse.orderSet_pair _) G hG boundedOutputFormula e he).mp hφ
  obtain ⟨p,hp,hp₀',hpr⟩ := G.directed hp₀ hr
  refine ⟨p,hp,hp₀',?_⟩
  intro H hH hpH
  have hv := cone_truth_of_internal_tail_symmetry M C B hM hT hct hC hB hBC
    boundedOutputFormula e he hinv p (forces_mono _ e hpr hrφ) H hH
    ((projected_cone_iff C B hBC H p).mp hpH)
  rw [hev H,boundedOutputFormula_raw,hDv H hH (ht H)] at hv
  exact hv

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_FixedArithmeticTailCone
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open InternalCohenProjectionSymmetry InternalCohenFactor OracleJump TableIndices IndexMatrix
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem fixed_arithmetic_tail_cone (M C B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (x y : Name (Conditions (conditions C)))
    (hx : x.encode (label (conditions C)) ∈ M)
    (hy : y.encode (label (conditions C)) ∈ M)
    (hxfix : ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ H : GenericFilter (Conditions (conditions C)),
        x.val (AutomorphismName.mapFilter a H).carrier = x.val H.carrier)
    (hyfix : ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ H : GenericFilter (Conditions (conditions C)),
        y.val (AutomorphismName.mapFilter a H).carrier = y.val H.carrier)
    (R : Oracle) (hR : realCode R ∈ M) (d k : ℕ)
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (A X : Oracle) (hxv : x.val G.carrier = realCode A) (hyv : y.val G.carrier = realCode X)
    (hprog : Represents (iterate (join A R) k) (machine d) X)
    (p₀ : Conditions (conditions C)) (hp₀ : p₀ ∈ G.carrier) :
    ∃ p ∈ G.carrier, p ≤ p₀ ∧
      ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        project C B hBC p ∈ (projected C B hBC H).carrier →
          ∃ A' X' : Oracle, x.val H.carrier = realCode A' ∧ y.val H.carrier = realCode X' ∧
            Represents (iterate (join A' R) k) (machine d) X' := by
  have hc := conditions_mem M C hM hT hC
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  have ht (H : GenericFilter (Conditions (conditions C))) : ⊤ ∈ H.carrier := by
    obtain ⟨q,hq⟩ := H.nonempty; exact H.upper le_top hq
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{0} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hω
  have hcheck {z : ZFSet.{0}} (hz : z ∈ M) :
      (Name.check z : Name (Conditions (conditions C))).encode (label (conditions C)) ∈ M :=
    encoded_check_mem M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hz
  obtain ⟨φ,hφ⟩ := ExtensionArithmeticRepresentative.fixed_output_bounded d k
  let ψ : BoundedSetTheory.Formula := .conj (.subset 3 1) (.conj (.subset 5 1) φ)
  let e := push (Name.check (natSet 0)) (push (Name.check ZFSet.omega)
    (push (Name.check Q) (push x (push (Name.check (realCode R)) (fun _ => y)))))
  have he (i : ℕ) : (e i).encode (label (conditions C)) ∈ M := by
    rcases i with _|_|_|_|_|i
    exact hcheck hz; exact hcheck hω; exact hcheck hQM; exact hx; exact hcheck hR; exact hy
  have hev (H : GenericFilter (Conditions (conditions C))) : (fun i => (e i).val H.carrier) =
      cons (natSet 0) (cons ZFSet.omega (cons Q
        (cons (x.val H.carrier) (cons (realCode R) (fun _ => y.val H.carrier))))) := by
    funext i; rcases i with _|_|_|_|_|i
    exact Name.val_check _ (ht H) _
    exact Name.val_check _ (ht H) _
    exact Name.val_check _ (ht H) _
    rfl
    exact Name.val_check _ (ht H) _
    rfl
  have hspec (A' X' : Oracle) :
      φ.Eval (cons (natSet 0) (cons ZFSet.omega (cons Q
        (cons (realCode A') (cons (realCode R) (fun _ => realCode X')))))) ↔
        Represents (iterate (join A' R) k) (machine d) X' := by
    have henv : arithmeticEnv Q (push A' (push R (fun _ => X'))) 0 =
        cons (natSet 0) (cons ZFSet.omega (cons Q
          (cons (realCode A') (cons (realCode R) (fun _ => realCode X'))))) := by
      funext i; rcases i with _|_|_|_|_|i <;> rfl
    simpa only [henv,push] using hφ Q hQ (push A' (push R (fun _ => X'))) 0
  have meaning (H : GenericFilter (Conditions (conditions C))) :
      ψ.Eval (fun i => (e i).val H.carrier) ↔
        ∃ A' X' : Oracle, x.val H.carrier = realCode A' ∧ y.val H.carrier = realCode X' ∧
          Represents (iterate (join A' R) k) (machine d) X' := by
    rw [hev H]
    simp only [ψ,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ]
    constructor
    · rintro ⟨hxs,hys,hformula⟩
      let A' := decodeReal (x.val H.carrier)
      let X' := decodeReal (y.val H.carrier)
      have hxa : x.val H.carrier = realCode A' := (realCode_decodeReal hxs).symm
      have hya : y.val H.carrier = realCode X' := (realCode_decodeReal hys).symm
      refine ⟨A',X',hxa,hya,?_⟩
      rw [hxa,hya] at hformula
      exact (hspec A' X').mp hformula
    · rintro ⟨A',X',hxa,hya,hpr⟩
      rw [hxa,hya]
      exact ⟨realCode_subset A',realCode_subset X',
        (hspec A' X').mpr hpr⟩
  have hinv : ∀ w ∈ M, ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
      (∀ s t, ZFSet.pair (label _ s) (label _ t) ∈ w ↔ t = a s) →
      (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
      ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        (ψ.Eval (fun i => (e i).val (AutomorphismName.mapFilter a H).carrier) ↔
          ψ.Eval (fun i => (e i).val H.carrier)) := by
    intro w hw a ha hfix H hH
    rw [hev _,hev H,hxfix a hfix H,hyfix a hfix H]
  have hv := (meaning G).mpr ⟨A,X,hxv,hyv,hprog⟩
  obtain ⟨r,hr,hrφ⟩ := (internal_bounded_truth M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc ho
    (InternalCollapse.orderSet_pair _) G hG ψ e he).mp hv
  obtain ⟨p,hp,hp₀',hpr⟩ := G.directed hp₀ hr
  refine ⟨p,hp,hp₀',?_⟩
  intro H hH hpH
  exact (meaning H).mp (cone_truth_of_internal_tail_symmetry M C B hM hT hct hC hB hBC
    ψ e he hinv p (forces_mono _ e hpr hrφ) H hH ((projected_cone_iff C B hBC H p).mp hpH))

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalColumnExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalColumnExtension
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenFactor InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem filterImage_mem (N A B g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hA : A ∈ N) (hB : B ∈ N) (hg : g ∈ N) : filterImage A B g ∈ N := by
  have hR := restrictionGraph_mem N A B hN hT hA hB
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 0 1 3)) (cons g (fun _ => restrictionGraph A B))
    (by intro i; cases i; exact hg; exact hR) (conditions_mem N B hN hT hB)
  simpa only [filterImage,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using hs

theorem projected_filter_image (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) :
    genericFilterSet (conditions B) (projected A B hBA G).carrier =
      filterImage A B (genericFilterSet (conditions A) G.carrier) := by
  apply ZFSet.ext; intro q
  rw [mem_genericFilterSet,filterImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨s,hs,rfl⟩
    obtain ⟨p,hp,hps⟩ := (mem_projected A B hBA G s).mp hs
    refine ⟨label_mem _ s,label _ p,(mem_genericFilterSet _ _ _).mpr ⟨p,hp,rfl⟩,?_⟩
    rw [←hps]
    exact (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩
  · rintro ⟨hq,p,hp,hpq⟩
    obtain ⟨r,hr,hrp⟩ := (mem_genericFilterSet (conditions A) G.carrier p).mp hp
    rw [←hrp] at hpq
    have he := ((pair_restrictionGraph A B _ q).mp hpq).2.2
    refine ⟨project A B hBA r,projected_contains A B hBA G hr,?_⟩
    exact (label_project A B hBA r).trans he.symm

theorem column_extension_subset (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (hG : AtomicForcing.GroundGeneric M G) :
    genericExtensionSet M (conditions B) (projected A B hBA G).carrier ⊆
      genericExtensionSet M (conditions A) G.carrier := by
  let N := genericExtensionSet M (conditions A) G.carrier
  have hN := genericExtensionSet_transitive M (conditions A) hM G.carrier
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions (conditions A)) ∈ G.carrier := G.upper le_top hp
  have hc := conditions_mem M A hM hT hA
  have hTN : SourceT N := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair _) G hG ht
  have hMN : M ⊆ N := ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  apply InternalNameEvaluation.extension_subset M N hN hTN hMN
  rw [projected_filter_image A B hBA G]
  apply filterImage_mem N A B _ hN hTN (hMN hA) (hMN hB)
  exact genericFilterSet_mem_extension M _ hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht

end TuringRigidity.InternalColumnExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ProjectedArithmeticOutputName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ProjectedArithmeticOutputName
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open PersistentRestrictions ExtensionArithmeticRepresentative OracleJump
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem projected_output_name (M C B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (I J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
    (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (A R : Oracle) (hA : degree A ∈ J.carrier)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
    (hAN : A ∈ modelReals (genericExtensionSet M (conditions B) (projected C B hBC G).carrier))
    (hRN : R ∈ modelReals (genericExtensionSet M (conditions B) (projected C B hBC G).carrier)) :
    ∃ X : Oracle, degree X = (σ ⟨degree A,hA⟩).val ∧
      Reduces X (iterate (join A R) 5) ∧
      (∃ e : OracleCode, OracleCode.eval (oracleFunction (iterate (join A R) 5)) e = oracleFunction X) ∧
      ∃ y : Name (Conditions (conditions C)), y.encode (label (conditions C)) ∈ M ∧
        y.val G.carrier = realCode X ∧
        ∀ a : Conditions (conditions C) ≃o Conditions (conditions C),
          (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
          ∀ H : GenericFilter (Conditions (conditions C)),
            y.val (AutomorphismName.mapFilter a H).carrier = y.val H.carrier := by
  let H := projected C B hBC G
  let N := genericExtensionSet M (conditions B) H.carrier
  have hH : GroundGeneric M H := projected_groundGeneric M C B hM hT hC hB hBC G hG
  have hc := conditions_mem M B hM hT hB
  have hN := genericExtensionSet_transitive M (conditions B) hM H.carrier
  obtain ⟨p,hp⟩ := H.nonempty
  have hTN := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair _) H hH (H.upper le_top hp)
  obtain ⟨X,hXN,hX,hred,hcode⟩ :=
    representative_in_model N hN hTN I J hIJ ρ σ he hz A R hA hR hAN hRN
  have hxN : realCode X ∈ (N : Set ZFSet.{0}) := hXN
  rw [genericExtensionSet_coe] at hxN
  obtain ⟨τ,hτ,hτv⟩ := hxN
  obtain ⟨y,hy,hyv,hinv⟩ := CohenProjectedNameLift.lift_projected_real_name M C B
    hM hT hC hB hBC τ hτ
  refine ⟨X,hX,hred,hcode,y,hy,?_,hinv⟩
  exact (hyv G hG (by rw [hτv]; exact realCode_subset X)).trans hτv

end TuringRigidity.ProjectedArithmeticOutputName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ProjectedArithmeticOutputCone
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenRestriction InternalCohenProjectedGeneric
open InternalCohenProjectionSymmetry InternalCohenFactor OracleJump TableIndices IndexMatrix
open PersistentRestrictions SetDegreeDecoding ElementaryModel FullSetForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem projected_arithmetic_output_cone_oai (M C B : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hC : C ∈ M) (hB : B ∈ M) (hBC : B ⊆ C)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : ElementaryModel.SentenceForm)
    (I : CountableIdeal) (ρ : I ≃o I)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (R : Oracle) (hRM : realCode R ∈ M)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
    (f : Name (Conditions (conditions C))) (hf : f.encode (label (conditions C)) ∈ M)
    (hfv : ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (conditions C) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (G : GenericFilter (Conditions (conditions C))) (hG : GroundGeneric M G)
    (hOwn : OwnDegreeExtension (genericExtensionSet M (conditions C) G.carrier)
      (idealSet I) (automorphismSet ρ) (f.val G.carrier))
    (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M)
    (A : Oracle) (hτv : τ.val (projected C B hBC G).carrier = realCode A)
    (p₀ : Conditions (conditions C)) (hp₀ : p₀ ∈ G.carrier) :
    ∃ x y : Name (Conditions (conditions C)),
      x.encode (label (conditions C)) ∈ M ∧ y.encode (label (conditions C)) ∈ M ∧
      x.val G.carrier = realCode A ∧
      (∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
        τ.val (projected C B hBC H).carrier ⊆ ZFSet.omega →
          x.val H.carrier = τ.val (projected C B hBC H).carrier) ∧
      ∃ d : ℕ, ∃ p ∈ G.carrier, p ≤ p₀ ∧
        ∀ H : GenericFilter (Conditions (conditions C)), GroundGeneric M H →
          project C B hBC p ∈ (projected C B hBC H).carrier →
            ∃ A' X' : Oracle, x.val H.carrier = realCode A' ∧ y.val H.carrier = realCode X' ∧
              Represents (iterate (join A' R) 5) (machine d) X' ∧
              ∃ a ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
              ∃ b ∈ degreeUniverse (groundReals (genericExtensionSet M (conditions C) H.carrier)),
                realCode A' ∈ a ∧ realCode X' ∈ b ∧ ZFSet.pair a b ∈ f.val H.carrier := by
  have hct : (M : Set ZFSet.{0}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro z hz; exact label_surjective M hz
  have hc := conditions_mem M C hM hT hC
  have ht := G.upper le_top G.nonempty.choose_spec
  let E := genericExtensionSet M (conditions C) G.carrier
  have hE := genericExtensionSet_transitive M (conditions C) hM G.carrier
  have hTE := extension_sourceT M hM hT hc (InternalCollapse.orderSet_mem M hM hT hc)
    (InternalCollapse.orderSet_pair _) G hG ht
  let J := modelIdeal E hE hTE
  obtain ⟨hIJ,σ,hσ,hext⟩ := (own_degree_extension_iff E hE hTE I ρ _).mp hOwn
  have hAN : A ∈ modelReals
      (genericExtensionSet M (conditions B) (projected C B hBC G).carrier) :=
    (mem_extensionSet _ _ _ _).mpr ⟨τ,hτ,hτv⟩
  have hAE : A ∈ modelReals E := by
    change realCode A ∈ E
    exact InternalColumnExtension.column_extension_subset M C B hM hT hC hB hBC G hG hAN
  have hAJ : degree A ∈ J.carrier := ⟨A,hAE,rfl⟩
  have hRN : R ∈ modelReals
      (genericExtensionSet M (conditions B) (projected C B hBC G).carrier) := by
    have hcB := conditions_mem M B hM hT hB
    let H := projected C B hBC G
    exact ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcB H.carrier
      (H.upper le_top H.nonempty.choose_spec) hRM
  obtain ⟨x,hx,hxv,hxfix⟩ := CohenProjectedNameLift.lift_projected_real_name M C B hM hT hC hB hBC τ hτ
  have hxG : x.val G.carrier = realCode A :=
    (hxv G hG (by rw [hτv]; exact realCode_subset A)).trans hτv
  obtain ⟨X,hX,hred,_,y,hy,hyG,hyfix⟩ :=
    ProjectedArithmeticOutputName.projected_output_name M C B hM hT hC hB hBC G hG
      I J hIJ ρ σ hext hz A R hAJ hR hAN hRN
  obtain ⟨c,hprog⟩ := reduces_represents hred
  let d := Encodable.encode c
  have hd : Represents (iterate (join A R) 5) (machine d) X := by simpa only [d,machine_encode] using hprog
  have houtput : ∃ a ∈ degreeUniverse (groundReals E), ∃ b ∈ degreeUniverse (groundReals E),
      x.val G.carrier ∈ a ∧ y.val G.carrier ∈ b ∧ ZFSet.pair a b ∈ f.val G.carrier := by
    rw [ownDegreeUniverse_eq_idealSet E hE hTE (groundReals E) (mem_groundReals E),
      ←hσ,hxG,hyG]
    exact boundedOutputFormula_raw _ _ _ _ |>.mp
      ((boundedOutputFormula_spec J σ A hAJ (realCode X)).mpr ⟨X,rfl,hX⟩)
  obtain ⟨q,hq,hqp₀,hqout⟩ := defined_output_tail_cone M C B hM hT hct hC hB hBC
    δ Z φ f x y hf hx hy hfv hxfix hyfix G hG houtput p₀ hp₀
  obtain ⟨p,hp,hpq,hpcode⟩ := fixed_arithmetic_tail_cone M C B hM hT hct hC hB hBC
    x y hx hy hxfix hyfix R hRM d 5 G hG A X hxG hyG hd q hq
  refine ⟨x,y,hx,hy,hxG,hxv,d,p,hp,hpq.trans hqp₀,?_⟩
  intro H hH hpH
  have hqH : project C B hBC q ∈ (projected C B hBC H).carrier := by
    apply (projected C B hBC H).upper (p := project C B hBC p) _ hpH
    change label _ (project C B hBC q) ⊆ label _ (project C B hBC p)
    simpa only [label_project] using restrict_mono B _ _ hpq
  obtain ⟨A',X',hxa,hya,hrep⟩ := hpcode H hH hpH
  refine ⟨A',X',hxa,hya,hrep,?_⟩
  simpa only [hxa,hya] using hqout H hH hqH

end TuringRigidity.BoundedForcing

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone_oai := @OAI.TuringRigidity.BoundedForcing.projected_arithmetic_output_cone_oai
