-- Prove2me | solution 1 for OAI.TuringRigidity.IteratedGenericCommonIdeal.ideal_of_iterated_generics
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:04:35.606266+00:00
-- url     : https://prove2.me/submissions/faaebcbb-4485-4365-96f9-70090eb771c7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008

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

end UniformOracle
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_BorelGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BorelGeneric
open Set

theorem word_surjective : Function.Surjective word := by
  intro s
  exact ⟨Encodable.encode s,by simp [word]⟩

end TuringRigidity.BorelGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdeal
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CommonIdeal
open Set Encodable

theorem table_total {G : Oracle} {s : List Bool} (h : Extends G s) :
    ∀ k a, a ∈ table s k → a ∈ oracleFunction G k := by
  intro k a ha
  change a ∈ ((s.map bit)[k]? : Part ℕ) at ha
  have hk : k < s.length := by
    by_contra hn
    simp [List.getElem?_eq_none (show (s.map bit).length ≤ k by simp; omega)] at ha
  have he : (s.map bit)[k]? = some (bit (s.getD k false)) := by
    simp [List.getD, hk]
  rw [he] at ha
  have hv : a = bit (s.getD k false) := by simpa using ha
  change a ∈ Part.some (bit (G k))
  rw [h k hk]
  exact Part.mem_some_iff.mpr hv

theorem run_total {A G : Oracle} {p : OracleCode} {s : List Bool}
    (h : Extends G s) (n a : ℕ) (ha : a ∈ run A p s n) :
    a ∈ OracleCode.eval (oracleFunction (join A G)) p n := by
  apply OracleCode.eval_mono (c := p) (n := n) (a := a) ?_ ha
  intro k b hb
  cases hk : k.bodd with
  | false => simpa [partialJoin, oracleFunction, join, hk] using hb
  | true =>
    have ht : b ∈ table s (k/2) := by simpa [partialJoin,hk] using hb
    simpa [oracleFunction,join,hk] using table_total h _ _ ht

theorem table_prefix (G : Oracle) (m : ℕ) :
    table (initialWord G m) = BranchMachine.lookup (UniformOracle.oraclePrefix (fun k => bit (G k)) m) := by
  simp only [table,initialWord,UniformOracle.oraclePrefix,List.map_map,Function.comp_def]
  rfl

theorem run_approximates (A G : Oracle) (p : OracleCode) (n : ℕ) :
    Approximates (OracleCode.eval (oracleFunction (join A G)) p n)
      (fun m => run A p (initialWord G m) n) := by
  have he : partialJoin (oracleFunction A) (oracleFunction G) = oracleFunction (join A G) := by
    funext k
    cases hk : k.bodd <;> simp [partialJoin,oracleFunction,join,hk]
  rw [←he]
  apply OracleCode.eval_approximates
  intro k
  apply BranchMachine.partialJoin_approximates
  · intro k; exact Approximates.const _
  · intro k
    simpa only [table_prefix,oracleFunction,bit] using UniformOracle.prefix_approximates (fun k => bit (G k)) k

theorem prefix_of_extends {G : Oracle} {s : List Bool} (h : Extends G s)
    {m : ℕ} (hm : s.length ≤ m) : s <+: initialWord G m := by
  apply List.prefix_iff_getElem.mpr
  refine ⟨by simpa using hm, ?_⟩
  intro i hi
  have hh := h i hi
  simpa [List.getD,List.getElem?_eq_getElem hi,initialWord,List.getElem_map,List.getElem_range] using hh.symm

theorem run_finite_extension {A G : Oracle} {p : OracleCode} {s : List Bool}
    (h : Extends G s) (n a : ℕ)
    (ha : a ∈ OracleCode.eval (oracleFunction (join A G)) p n) :
    ∃ t, s <+: t ∧ a ∈ run A p t n := by
  obtain ⟨m,hm⟩ := (run_approximates A G p n).2 a ha
  exact ⟨initialWord G (max m s.length),prefix_of_extends h (le_max_right _ _),
    hm _ (le_max_left _ _)⟩

theorem requirement_dense (A : Oracle) (p q : OracleCode) (s t : List Bool) :
    ∃ u v, s <+: u ∧ t <+: v ∧ Requirement A p q u v := by
  classical
  by_cases h : ∃ u v, s <+: u ∧ t <+: v ∧ Disagree A p q u v
  · obtain ⟨u,v,hu,hv,hh⟩ := h
    exact ⟨u,v,hu,hv,Or.inl hh⟩
  · refine ⟨s,t,List.prefix_rfl,List.prefix_rfl,Or.inr ?_⟩
    intro u v n a b hu hv ha hb
    by_contra hab
    exact h ⟨u,v,hu,hv,n,a,b,hab,ha,hb⟩

theorem agree_of_common_output {A G H Y : Oracle} {p q : OracleCode} {s t : List Bool}
    (hs : Extends G s) (ht : Extends H t) (hR : Requirement A p q s t)
    (hp : OracleCode.eval (oracleFunction (join A G)) p = oracleFunction Y)
    (hq : OracleCode.eval (oracleFunction (join A H)) q = oracleFunction Y) :
    Agree A p q s t := by
  rcases hR with ⟨n,a,b,hab,ha,hb⟩ | hR
  · have ha' := run_total hs n a ha
    have hb' := run_total ht n b hb
    rw [hp] at ha'
    rw [hq] at hb'
    exact False.elim (hab (Part.mem_unique ha' hb'))
  · exact hR

theorem agreeing_search_sound {A H Y : Oracle} {p q : OracleCode} {s t : List Bool}
    (ht : Extends H t) (h : Agree A p q s t)
    (hq : OracleCode.eval (oracleFunction (join A H)) q = oracleFunction Y)
    (w : List Bool) (n a : ℕ) (ha : a ∈ run A p (s ++ w) n) : a = bit (Y n) := by
  have hb : bit (Y n) ∈ OracleCode.eval (oracleFunction (join A H)) q n := by
    rw [hq]; exact Part.mem_some _
  obtain ⟨v,hv,hb'⟩ := run_finite_extension ht n (bit (Y n)) hb
  exact h (s ++ w) v n a (bit (Y n)) (List.prefix_append s w) hv ha hb'

theorem agreeing_search_complete {A G Y : Oracle} {p : OracleCode} {s : List Bool}
    (hs : Extends G s)
    (hp : OracleCode.eval (oracleFunction (join A G)) p = oracleFunction Y) (n : ℕ) :
    ∃ w a, a ∈ run A p (s ++ w) n := by
  have ha : bit (Y n) ∈ OracleCode.eval (oracleFunction (join A G)) p n := by
    rw [hp]; exact Part.mem_some _
  obtain ⟨u,⟨w,rfl⟩,hu⟩ := run_finite_extension hs n (bit (Y n)) ha
  exact ⟨w,bit (Y n),hu⟩

end TuringRigidity.CommonIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdealSearch
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CommonIdeal
open Encodable Computable UniformOracle

theorem finiteRun_partrec (p : OracleCode) (s : List Bool) : Partrec₂ (finiteRun p s) := by
  let α := List ℕ × ℕ
  have hword : Computable (fun z : α => s ++ BorelGeneric.word (Nat.unpair z.2).1) :=
    (Primrec.list_append.comp (Primrec.const s)
      (Primrec.option_getD_default.comp (Primrec.decode.comp
        (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))))).to_comp
  have hA : Partrec₂ (fun z : α => BranchMachine.lookup z.1) :=
    BranchMachine.lookup_partrec.comp (fst.comp fst) snd
  have hG : Partrec₂ (fun z : α => table (s ++ BorelGeneric.word (Nat.unpair z.2).1)) :=
    table_partrec.comp (hword.comp fst) snd
  exact (OracleCode.eval_partrec (BranchMachine.partialJoin_partrec hA hG) p).comp
    Computable.id (snd.comp (Computable.unpair.comp snd))

theorem finiteRun_code (p : OracleCode) (s : List Bool) :
    ∃ d : Nat.Partrec.Code, ∀ L w, d.eval (Nat.pair (encode L) w) = finiteRun p s L w := by
  obtain ⟨d,hd⟩ := partrec_code (finiteRun_partrec p s)
  exact ⟨d,fun L w => hd (L,w)⟩

theorem finiteRun_approximates (A : Oracle) (p : OracleCode) (s : List Bool) (w n : ℕ) :
    Approximates (run A p (s ++ BorelGeneric.word w) n)
      (fun m => finiteRun p s (oraclePrefix (fun k => bit (A k)) m) (Nat.pair w n)) := by
  simp only [finiteRun,Nat.unpair_pair]
  apply OracleCode.eval_approximates
  intro k
  apply BranchMachine.partialJoin_approximates
  · exact prefix_approximates (fun k => bit (A k))
  · intro k; exact Approximates.const _

theorem searchTrial_recursive (A : Oracle) (d : Nat.Partrec.Code) :
    Nat.RecursiveIn {oracleFunction A}
      (fun z => Part.some (encode (searchTrial A d (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction A}
  have hn := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hz := Primrec.snd.comp Primrec.unpair
  have hm := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp hz))
  have hw := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp hz))))
  have hk := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.unpair.comp hz))))
  have hL := _root_.OAI.TuringRigidity.UniformOracle.total_comp (prefix_recursive (fun k => bit (A k))) hm
  have he := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.encode.comp (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.fst.comp Primrec.unpair).pair (Primrec.const d)).pair
      (Primrec.snd.comp Primrec.unpair))))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp he (_root_.OAI.TuringRigidity.UniformOracle.total_pair hk (_root_.OAI.TuringRigidity.UniformOracle.total_pair hL (_root_.OAI.TuringRigidity.UniformOracle.total_pair hw hn)))).of_eq (fun z => by simp [searchTrial])

theorem common_output_reduces {A G H Y : Oracle} {p q : OracleCode} {s t : List Bool}
    (hs : Extends G s) (ht : Extends H t) (hR : Requirement A p q s t)
    (hp : OracleCode.eval (oracleFunction (join A G)) p = oracleFunction Y)
    (hq : OracleCode.eval (oracleFunction (join A H)) q = oracleFunction Y) :
    Reduces Y A := by
  have hag := agree_of_common_output hs ht hR hp hq
  obtain ⟨d,hd⟩ := finiteRun_code p s
  apply RecursiveIn.iff_nat.mpr
  apply total_search (searchTrial_recursive A d) (fun n => bit (Y n))
  · intro n z a ha
    have hfinite := Nat.Partrec.Code.evaln_sound ha
    rw [hd] at hfinite
    have hactual := (finiteRun_approximates A p s
      (Nat.unpair (Nat.unpair z).2).1 n).1 (Nat.unpair z).1 a hfinite
    exact agreeing_search_sound ht hag hq _ n a hactual
  · intro n
    obtain ⟨w,a,ha⟩ := agreeing_search_complete hs hp n
    obtain ⟨wcode,hw⟩ := BorelGeneric.word_surjective w
    rw [←hw] at ha
    obtain ⟨m,hm⟩ := (finiteRun_approximates A p s wcode n).2 a ha
    have hfinite := hm m le_rfl
    dsimp only at hfinite
    rw [←hd] at hfinite
    obtain ⟨k,hk⟩ := Nat.Partrec.Code.evaln_complete.mp hfinite
    exact ⟨Nat.pair m (Nat.pair wcode k),a,by simpa [searchTrial] using hk⟩

theorem ideal_of_meets (A G H : Oracle)
    (h : ∀ p q : OracleCode, ∃ s t, Extends G s ∧ Extends H t ∧ Requirement A p q s t) :
    ∀ b : Degree, b ≤ degree A ↔ b ≤ degree (join A G) ∧ b ≤ degree (join A H) := by
  intro b
  obtain ⟨Y,rfl⟩ := degree_surjective b
  constructor
  · intro hY
    exact ⟨reduces_trans hY (reduces_join_left A G),reduces_trans hY (reduces_join_left A H)⟩
  · rintro ⟨hG,hH⟩
    obtain ⟨p,hp⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hG
    obtain ⟨q,hq⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hH
    obtain ⟨s,t,hs,ht,hR⟩ := h p q
    exact common_output_reduces hs ht hR hp hq

end TuringRigidity.CommonIdeal

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelReals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelReals
open BoundedSetTheory TransitiveNameModel SetPresentationDecoding
universe u
noncomputable section

theorem omega_exists (P : ZFSet.{u} → Prop) :
    (∃ x ∈ ZFSet.omega, P x) ↔ ∃ n, P (natSet n) := by
  constructor
  · rintro ⟨x,hx,hP⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,hP⟩
  · rintro ⟨n,hP⟩
    exact ⟨_,(mem_omega _).mpr ⟨n,rfl⟩,hP⟩

end
end TuringRigidity.SetModelReals

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

theorem finiteGraph_zero (f : ℕ → ZFSet.{u}) : finiteGraph 0 f = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [mem_finiteGraph,Nat.not_lt_zero,false_and,exists_false,ZFSet.notMem_empty]

theorem finiteGraph_succ (n : ℕ) (f : ℕ → ZFSet.{u}) :
    finiteGraph (n+1) f = insert (ZFSet.pair (natSet n) (f n)) (finiteGraph n f) := by
  apply ZFSet.ext
  intro z
  simp only [mem_finiteGraph,ZFSet.mem_insert_iff]
  constructor
  · rintro ⟨i,hi,he⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi|rfl
    · exact Or.inr ⟨i,hi,he⟩
    · exact Or.inl he
  · rintro (he|⟨i,hi,he⟩)
    · exact ⟨n,Nat.lt_succ_self n,he⟩
    · exact ⟨i,Nat.lt_succ_of_lt hi,he⟩

theorem finiteGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    (n : ℕ) (f : ℕ → ZFSet.{u}) (hf : ∀ i < n, f i ∈ M) : finiteGraph n f ∈ M := by
  induction n with
  | zero =>
    rw [finiteGraph_zero]
    exact hM _ hω _ ZFSet.omega_zero
  | succ n ih =>
    rw [finiteGraph_succ]
    have hn := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
    have hp := orderedPair_mem M hM hP hn (hf n (Nat.lt_succ_self n))
    have hs := singleton_mem M hM hP hp
    have hu := binary_union_mem M hM hP hU hs (ih (fun i hi => hf i (Nat.lt_succ_of_lt hi)))
    have he : ({ZFSet.pair (natSet n) (f n)} : ZFSet.{u}) ∪ finiteGraph n f =
        insert (ZFSet.pair (natSet n) (f n)) (finiteGraph n f) := by
      apply ZFSet.ext
      intro z
      simp only [ZFSet.mem_union,ZFSet.mem_singleton,ZFSet.mem_insert_iff]
    exact he ▸ hu

theorem eval_traceFormula (n x y p v g w z : ℕ) (e : ℕ → ZFSet.{u})
    (k : ℕ) (hn : e n = natSet k) (hw : e w = ZFSet.omega) (hz : e z = natSet 0) :
    (traceFormula n x y p v g w z).Eval e ↔ Trace (e v) (e g) k (e x) (e y) (e p) := by
  simp only [traceFormula,Formula.Eval,Formula.eval_pairMem,Formula.eval_allMem,
    Formula.eval_imp,Formula.eval_successor,cons_zero,cons_succ,hn,hw,hz,Trace]
  apply and_congr Iff.rfl
  apply and_congr _ Iff.rfl
  constructor
  · intro h i hi a ha hp
    obtain ⟨s,_,hs,b,hb,hpb,hgb⟩ := h (natSet i) ((natSet_mem_natSet i k).mpr hi) a ha hp
    exact ⟨b,hb,by simpa only [hs,natSet] using hpb,hgb⟩
  · intro h i hi a ha hp
    obtain ⟨j,hj,rfl⟩ := (mem_natSet k i).mp hi
    obtain ⟨b,hb,hpb,hgb⟩ := h j hj a ha hp
    exact ⟨natSet (j+1),(mem_omega _).mpr ⟨j+1,rfl⟩,rfl,b,hb,hpb,hgb⟩

theorem iterate_mem {v : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v) {x : ZFSet.{u}} (hx : x ∈ v) (n : ℕ) : F^[n] x ∈ v := by
  induction n with
  | zero => exact hx
  | succ n ih => simpa only [Function.iterate_succ_apply'] using hF _ ih

theorem trace_correct {v g : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x)
    {n : ℕ} {x y p : ZFSet.{u}} (hx : x ∈ v) (ht : Trace v g n x y p) : y = F^[n] x := by
  have hp (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (F^[i] x) ∈ p := by
    induction i with
    | zero => exact ht.1
    | succ i ih =>
      have hv := iterate_mem F hF hx i
      obtain ⟨b,hb,hpb,hgb⟩ := ht.2.1 i (by omega) _ hv (ih (by omega))
      have he := (hg _ hv b hb).mp hgb
      simpa only [he,Function.iterate_succ_apply'] using hpb
  exact (ht.2.2 _ (iterate_mem F hF hx n) (hp n le_rfl)).symm

theorem finiteGraph_trace {v g : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x)
    {x : ZFSet.{u}} (hx : x ∈ v) (n : ℕ) :
    Trace v g n x (F^[n] x) (finiteGraph (n+1) (fun i => F^[i] x)) := by
  refine ⟨(pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_,?_⟩
  · intro i hi a ha hpa
    have he := ((pair_mem_finiteGraph _ _ _ _).mp hpa).2
    subst a
    refine ⟨F^[i+1] x,iterate_mem F hF hx (i+1),
      (pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_⟩
    apply (hg _ (iterate_mem F hF hx i) _ (iterate_mem F hF hx (i+1))).mpr
    exact Function.iterate_succ_apply' F i x
  · intro b _ hpb
    exact ((pair_mem_finiteGraph _ _ _ _).mp hpb).2

end
end TuringRigidity.SetModelIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelIteration
open BoundedSetTheory TransitiveNameModel SetModelReals
universe u
noncomputable section

theorem mem_iterationSet {v : ZFSet.{u}} (F : ZFSet.{u} → ZFSet.{u})
    (hF : ∀ x ∈ v, F x ∈ v) (z : ZFSet.{u}) :
    z ∈ iterationSet v F ↔ ∃ n : ℕ, ∃ x ∈ v,
      z = ZFSet.pair (ZFSet.pair (natSet n) x) (F^[n] x) := by
  rw [iterationSet,ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨n,x,hx,rfl⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨ZFSet.pair_mem_prod.mpr
      ⟨(mem_omega _).mpr ⟨n,rfl⟩,hx⟩,iterate_mem F hF hx n⟩,⟨n,x,hx,rfl⟩⟩

theorem eval_iterationFormula (z v g p d : ZFSet.{u}) :
    iterationFormula.Eval (cons z (cons ZFSet.omega (cons v (cons g
      (cons p (cons (natSet 0) (fun _ => d))))))) ↔
    ∃ n : ℕ, ∃ x ∈ v, ∃ y ∈ v, ∃ t ∈ d, ∃ s ∈ p,
      z = ZFSet.pair t y ∧ t = ZFSet.pair (natSet n) x ∧ Trace v g n x y s := by
  simp only [iterationFormula,Formula.Eval,cons_zero,cons_succ]
  rw [omega_exists]
  apply exists_congr
  intro n
  apply exists_congr
  intro x
  apply and_congr Iff.rfl
  apply exists_congr
  intro y
  apply and_congr Iff.rfl
  apply exists_congr
  intro t
  apply and_congr Iff.rfl
  apply exists_congr
  intro s
  apply and_congr Iff.rfl
  simp only [Formula.eval_orderedPair,cons_zero,cons_succ]
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  exact eval_traceFormula _ _ _ _ _ _ _ _ _ n rfl rfl rfl

theorem iterationSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    {v g : ZFSet.{u}} (hv : v ∈ M) (hgM : g ∈ M)
    (F : ZFSet.{u} → ZFSet.{u}) (hF : ∀ x ∈ v, F x ∈ v)
    (hg : ∀ x ∈ v, ∀ y ∈ v, ZFSet.pair x y ∈ g ↔ y = F x) :
    iterationSet v F ∈ M := by
  have hω := omega_mem M hM hS hI
  have h0 : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  let d := ZFSet.prod ZFSet.omega v
  have hd : d ∈ M := product_mem M hM hP hU hPow hS hω hv
  obtain ⟨p,hp,hpdef⟩ := internal_power M hM hPow hd
  have hprod := product_mem M hM hP hU hPow hS hd hv
  let e := cons ZFSet.omega (cons v (cons g (cons p (cons (natSet 0) (fun _ => d)))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hv
    · exact hgM
    · exact hp
    · exact h0
    · exact hd
  have hs := sep_mem M hM hS iterationFormula e he hprod
  have eq : ZFSet.sep (fun z => iterationFormula.Eval (cons z e)) (ZFSet.prod d v) =
      iterationSet v F := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,mem_iterationSet F hF,
      show iterationFormula.Eval (cons z e) ↔ _ from eval_iterationFormula z v g p d]
    constructor
    · rintro ⟨_,n,x,hx,y,hy,t,ht,s,hs,hz,htx,htrace⟩
      exact ⟨n,x,hx,by rw [hz,htx,trace_correct F hF hg hx htrace]⟩
    · rintro ⟨n,x,hx,rfl⟩
      let s := finiteGraph (n+1) (fun i => F^[i] x)
      have hsM : s ∈ M := finiteGraph_mem M hM hP hU hω _ _
        (fun i _ => hM v hv _ (iterate_mem F hF hx i))
      have hsD : s ⊆ d := by
        intro z hz
        obtain ⟨i,hi,rfl⟩ := (mem_finiteGraph _ _ _).mp hz
        exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨i,rfl⟩,iterate_mem F hF hx i⟩
      have hsP := (hpdef s).mpr ⟨hsM,hsD⟩
      have htD : ZFSet.pair (natSet n) x ∈ d :=
        ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨n,rfl⟩,hx⟩
      refine ⟨ZFSet.pair_mem_prod.mpr ⟨htD,iterate_mem F hF hx n⟩,
        n,x,hx,_,iterate_mem F hF hx n,_,htD,s,hsP,rfl,rfl,?_⟩
      exact finiteGraph_trace F hF hg hx n
  exact eq ▸ hs

end
end TuringRigidity.SetModelIteration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelAddition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem setSucc_nat (n : ℕ) : setSucc (natSet.{u} n) = natSet (n+1) := rfl

theorem setSucc_omega : ∀ x ∈ ZFSet.omega.{u}, setSucc x ∈ ZFSet.omega := by
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact (mem_omega _).mpr ⟨n+1,rfl⟩

theorem pair_mem_successorSet {x y : ZFSet.{u}} (hx : x ∈ ZFSet.omega) (hy : y ∈ ZFSet.omega) :
    ZFSet.pair x y ∈ successorSet ↔ y = setSucc x := by
  simp only [successorSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,hx,hy,true_and,ZFSet.pair_inj]
  constructor
  · rintro ⟨a,ha,he,hs⟩
    exact he ▸ hs
  · intro h
    exact ⟨x,hx,rfl,h⟩

theorem successorSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : successorSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hprod := product_mem M hM hP hU hPow hS hω hω
  have hs := sep_mem M hM hS successorFormula (fun _ => ZFSet.omega) (fun _ => hω) hprod
  have eq : ZFSet.sep (fun z => successorFormula.Eval (cons z (fun _ => ZFSet.omega)))
      (ZFSet.prod ZFSet.omega ZFSet.omega) = successorSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,successorFormula,Formula.Eval,Formula.eval_orderedPair,
      Formula.eval_successor,cons_zero,cons_succ,successorSet]
    apply and_congr Iff.rfl
    constructor
    · rintro ⟨x,hx,y,hy,hz,rfl⟩
      exact ⟨x,hx,hz⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x,hx,setSucc x,setSucc_omega x hx,rfl,rfl⟩
  exact eq ▸ hs

theorem iterate_setSucc (n m : ℕ) : setSucc^[n] (natSet.{u} m) = natSet (m+n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change natSet (m+n+1) = natSet (m+(n+1))
    rw [Nat.add_assoc]

theorem addition_code (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ additionSet ↔ k = n+m := by
  rw [additionSet,mem_iterationSet setSucc setSucc_omega]
  constructor
  · rintro ⟨i,x,hx,he⟩
    obtain ⟨hinput,hout⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hi,rfl⟩ := ZFSet.pair_inj.mp hinput
    have hin := natSet_injective hi
    rw [←hin,iterate_setSucc] at hout
    exact (natSet_injective hout).trans (Nat.add_comm m n)
  · intro hk
    refine ⟨n,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,?_⟩
    rw [iterate_setSucc,hk,Nat.add_comm m n]

theorem additionSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : additionSet.{u} ∈ M :=
  iterationSet_mem M hM hP hU hPow hS hI (omega_mem M hM hS hI)
    (successorSet_mem M hM hP hU hPow hS hI) setSucc setSucc_omega
    (fun _ hx _ hy => pair_mem_successorSet hx hy)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplicationStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem numberPair_injective : Function.Injective numberPair.{u} := by
  intro a b h
  obtain ⟨hl,hr⟩ := ZFSet.pair_inj.mp h
  exact Prod.ext (natSet_injective hl) (natSet_injective hr)

theorem mem_pairNumbers (x : ZFSet.{u}) : x ∈ pairNumbers ↔ ∃ q, x = numberPair q := by
  constructor
  · intro hx
    obtain ⟨a,ha,b,hb,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega a).mp ha
    obtain ⟨m,rfl⟩ := (mem_omega b).mp hb
    exact ⟨(n,m),rfl⟩
  · rintro ⟨q,rfl⟩
    exact ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨q.1,rfl⟩,(mem_omega _).mpr ⟨q.2,rfl⟩⟩

@[simp] theorem addStep_numberPair (n m : ℕ) :
    addStep (numberPair.{u} (n,m)) = numberPair (n,n+m) := by
  have h := Function.leftInverse_invFun numberPair_injective (n,m)
  change Function.invFun numberPair.{u} (numberPair (n,m)) = (n,m) at h
  simp only [addStep,h]

theorem addStep_closed : ∀ x ∈ pairNumbers.{u}, addStep x ∈ pairNumbers := by
  intro x hx
  obtain ⟨⟨n,m⟩,rfl⟩ := (mem_pairNumbers x).mp hx
  rw [addStep_numberPair]
  exact (mem_pairNumbers _).mpr ⟨(n,n+m),rfl⟩

theorem pair_mem_addStepSet {x y : ZFSet.{u}} (hx : x ∈ pairNumbers) (hy : y ∈ pairNumbers) :
    ZFSet.pair x y ∈ addStepSet ↔ y = addStep x := by
  simp only [addStepSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,hx,hy,true_and,ZFSet.pair_inj]
  constructor
  · rintro ⟨a,ha,he,hs⟩
    exact he ▸ hs
  · intro h
    exact ⟨x,hx,rfl,h⟩

theorem eval_addStepFormula (z : ZFSet.{u}) :
    addStepFormula.Eval (cons z (cons ZFSet.omega (cons pairNumbers (fun _ => additionSet)))) ↔
      ∃ x ∈ pairNumbers, z = ZFSet.pair x (addStep x) := by
  simp only [addStepFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ]
  constructor
  · rintro ⟨n,hn,m,hm,k,hk,x,hx,y,hy,hz,hxnm,hynk,hadd⟩
    obtain ⟨i,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨j,rfl⟩ := (mem_omega m).mp hm
    obtain ⟨l,rfl⟩ := (mem_omega k).mp hk
    rw [hxnm] at hadd
    have hl := (addition_code i j l).mp hadd
    refine ⟨x,hx,?_⟩
    rw [hz,hxnm,hynk,hl]
    exact congrArg (ZFSet.pair (numberPair (i,j))) (addStep_numberPair i j).symm
  · rintro ⟨x,hx,hz⟩
    obtain ⟨⟨i,j⟩,rfl⟩ := (mem_pairNumbers x).mp hx
    have hy : numberPair.{u} (i,i+j) ∈ pairNumbers := (mem_pairNumbers _).mpr ⟨_,rfl⟩
    refine ⟨natSet i,(mem_omega _).mpr ⟨i,rfl⟩,natSet j,(mem_omega _).mpr ⟨j,rfl⟩,
      natSet (i+j),(mem_omega _).mpr ⟨i+j,rfl⟩,numberPair (i,j),hx,numberPair (i,i+j),hy,
      ?_,rfl,rfl,(addition_code i j (i+j)).mpr rfl⟩
    simpa only [addStep_numberPair] using hz

theorem addStepSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : addStepSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hp : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have ha := additionSet_mem M hM hP hU hPow hS hI
  have hprod := product_mem M hM hP hU hPow hS hp hp
  let e := cons ZFSet.omega (cons pairNumbers (fun _ => additionSet))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i <;> simp [e,hω,hp,ha]
  have hs := sep_mem M hM hS addStepFormula e he hprod
  have eq : ZFSet.sep (fun z => addStepFormula.Eval (cons z e)) (ZFSet.prod pairNumbers pairNumbers) =
      addStepSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,show ∀ z, addStepFormula.Eval (cons z e) ↔ _ from eval_addStepFormula,
      addStepSet]
  exact eq ▸ hs

theorem iterate_addStep (n m : ℕ) :
    addStep^[n] (numberPair.{u} (m,0)) = numberPair (m,n*m) := by
  induction n with
  | zero => simp only [Function.iterate_zero,Function.id_def,Nat.zero_mul]
  | succ n ih => rw [Function.iterate_succ_apply',ih,addStep_numberPair,Nat.succ_mul,Nat.add_comm]

theorem multiplicationIteration_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : multiplicationIteration.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  exact iterationSet_mem M hM hP hU hPow hS hI
    (product_mem M hM hP hU hPow hS hω hω)
    (addStepSet_mem M hM hP hU hPow hS hI) addStep addStep_closed
    (fun _ hx _ hy => pair_mem_addStepSet hx hy)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelMultiplication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem eval_mulFormula (n m k i d D z : ℕ) (e : ℕ → ZFSet.{u}) (a b c : ℕ)
    (hn : e n = natSet a) (hm : e m = natSet b) (hk : e k = natSet c)
    (hi : e i = multiplicationIteration) (hd : e d = pairNumbers)
    (hD : e D = ZFSet.prod ZFSet.omega pairNumbers) (hz : e z = natSet 0) :
    (mulFormula n m k i d D z).Eval e ↔ c = a*b := by
  simp only [mulFormula,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,hn,hm,hk,hi,hd,hD,hz]
  constructor
  · rintro ⟨s,hs,t,ht,w,hw,hsb,htbc,hwas,hwt⟩
    change ZFSet.pair w t ∈ iterationSet pairNumbers addStep at hwt
    obtain ⟨q,x,hx,he⟩ := (mem_iterationSet addStep addStep_closed _).mp hwt
    obtain ⟨hleft,hright⟩ := ZFSet.pair_inj.mp he
    rw [hwas] at hleft
    obtain ⟨hqa,hxs⟩ := ZFSet.pair_inj.mp hleft
    have hq := natSet_injective hqa
    rw [←hxs,hsb,←hq] at hright
    change t = addStep^[a] (numberPair (b,0)) at hright
    rw [iterate_addStep,htbc] at hright
    exact natSet_injective (ZFSet.pair_inj.mp hright).2
  · intro hc
    have hs : numberPair.{u} (b,0) ∈ pairNumbers := (mem_pairNumbers _).mpr ⟨_,rfl⟩
    have ht : numberPair.{u} (b,c) ∈ pairNumbers := (mem_pairNumbers _).mpr ⟨_,rfl⟩
    have hw : ZFSet.pair (natSet a) (numberPair.{u} (b,0)) ∈ ZFSet.prod ZFSet.omega pairNumbers :=
      ZFSet.pair_mem_prod.mpr ⟨(mem_omega _).mpr ⟨a,rfl⟩,hs⟩
    refine ⟨numberPair (b,0),hs,numberPair (b,c),ht,_,hw,rfl,rfl,rfl,?_⟩
    exact (mem_iterationSet addStep addStep_closed _).mpr
      ⟨a,numberPair (b,0),hs,by rw [iterate_addStep,hc]⟩

theorem multiplication_code (n m k : ℕ) :
    ZFSet.pair (numberPair.{u} (n,m)) (natSet k) ∈ multiplicationSet ↔ k = n*m := by
  simp only [multiplicationSet,ZFSet.mem_sep,ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨_,a,b,he⟩
    obtain ⟨hin,hout⟩ := ZFSet.pair_inj.mp he
    have hab := numberPair_injective hin
    have hn : n = a := congrArg Prod.fst hab
    have hm : m = b := congrArg Prod.snd hab
    simpa only [←hn,←hm] using natSet_injective hout
  · intro hk
    exact ⟨⟨(mem_pairNumbers _).mpr ⟨_,rfl⟩,(mem_omega _).mpr ⟨k,rfl⟩⟩,
      n,m,by rw [hk]⟩

theorem multiplicationSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : multiplicationSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have h0 : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  have hd : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have hD := product_mem M hM hP hU hPow hS hω hd
  have hi := multiplicationIteration_mem M hM hP hU hPow hS hI
  have hprod := product_mem M hM hP hU hPow hS hd hω
  let e := cons ZFSet.omega (cons pairNumbers (cons multiplicationIteration
    (cons (ZFSet.prod ZFSet.omega pairNumbers) (fun _ => natSet 0))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hd
    · exact hi
    · exact hD
    · exact h0
  have hs := sep_mem M hM hS multiplicationFormula e he hprod
  have hφ (z : ZFSet.{u}) : multiplicationFormula.Eval (cons z e) ↔
      ∃ n m, z = ZFSet.pair (numberPair (n,m)) (natSet (n*m)) := by
    simp only [multiplicationFormula,Formula.Eval,Formula.eval_orderedPair,
      cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,m,hm,k,hk,t,ht,hz,htnm,hmu⟩
      obtain ⟨a,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨b,rfl⟩ := (mem_omega m).mp hm
      obtain ⟨c,rfl⟩ := (mem_omega k).mp hk
      have hc := (eval_mulFormula 3 2 1 7 6 8 9
        (cons t (cons (natSet c) (cons (natSet b) (cons (natSet a) (cons z e)))))
        a b c rfl rfl rfl rfl rfl rfl rfl).mp hmu
      exact ⟨a,b,by simpa only [htnm,hc,numberPair] using hz⟩
    · rintro ⟨n,m,rfl⟩
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,
        natSet (n*m),(mem_omega _).mpr ⟨n*m,rfl⟩,numberPair (n,m),
        (mem_pairNumbers _).mpr ⟨_,rfl⟩,rfl,rfl,?_⟩
      exact (eval_mulFormula 3 2 1 7 6 8 9
        (cons (numberPair (n,m)) (cons (natSet (n*m)) (cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (numberPair (n,m)) (natSet (n*m))) e)))))
        n m (n*m) rfl rfl rfl rfl rfl rfl rfl).mpr rfl
  have eq : ZFSet.sep (fun z => multiplicationFormula.Eval (cons z e))
      (ZFSet.prod pairNumbers ZFSet.omega) = multiplicationSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,hφ,multiplicationSet]
  exact eq ▸ hs

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelSequences
universe u
noncomputable section

@[simp] theorem natPair_mem (n m : ℕ) :
    ZFSet.pair (natSet.{u} n) (natSet m) ∈ pairNumbers :=
  (mem_pairNumbers _).mpr ⟨(n,m),rfl⟩

theorem multiplication_code' (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ multiplicationSet ↔ k = n*m :=
  multiplication_code n m k

theorem eval_pairFormula (n m k a b d w : ℕ) (e : ℕ → ZFSet.{u}) (i j l : ℕ)
    (hn : e n = natSet i) (hm : e m = natSet j) (hk : e k = natSet l)
    (ha : e a = additionSet) (hb : e b = multiplicationSet)
    (hd : e d = pairNumbers) (hw : e w = ZFSet.omega) :
    (pairFormula n m k a b d w).Eval e ↔ l = Nat.pair i j := by
  simp only [pairFormula,Formula.eval_disj,Formula.Eval,eval_tripleFormula,
    cons_zero,cons_succ,hn,hm,hk,ha,hb,hd,hw,natSet_mem_natSet]
  simp_rw [omega_exists]
  simp only [natPair_mem,true_and,addition_code,multiplication_code']
  by_cases h : i < j <;> simp [h,Nat.pair]

theorem pairingSet_code : PairingCode pairingSet.{u} := by
  intro n m k
  simp only [pairingSet,ZFSet.mem_sep,ZFSet.pair_mem_prod,natPair_mem,true_and]
  constructor
  · rintro ⟨_,a,b,he⟩
    obtain ⟨hin,hout⟩ := ZFSet.pair_inj.mp he
    have hab : (n,m) = (a,b) := numberPair_injective hin
    have hn : n = a := congrArg Prod.fst hab
    have hm : m = b := congrArg Prod.snd hab
    simpa only [←hn,←hm] using natSet_injective hout
  · intro hk
    exact ⟨(mem_omega _).mpr ⟨k,rfl⟩,n,m,by simp only [hk,numberPair]⟩

theorem pairingSet_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M) : pairingSet.{u} ∈ M := by
  have hω := omega_mem M hM hS hI
  have hd : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have ha := additionSet_mem M hM hP hU hPow hS hI
  have hb := multiplicationSet_mem M hM hP hU hPow hS hI
  have hprod := product_mem M hM hP hU hPow hS hd hω
  let e := cons ZFSet.omega (cons pairNumbers (cons additionSet (fun _ => multiplicationSet)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hd
    · exact ha
    · exact hb
  have hs := sep_mem M hM hS pairingFormula e he hprod
  have hφ (z : ZFSet.{u}) : pairingFormula.Eval (cons z e) ↔
      ∃ n m, z = ZFSet.pair (numberPair (n,m)) (natSet (Nat.pair n m)) := by
    simp only [pairingFormula,Formula.Eval,Formula.eval_orderedPair,
      cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,m,hm,k,hk,t,ht,hz,htnm,hpr⟩
      obtain ⟨a,rfl⟩ := (mem_omega n).mp hn
      obtain ⟨b,rfl⟩ := (mem_omega m).mp hm
      obtain ⟨c,rfl⟩ := (mem_omega k).mp hk
      have hc := (eval_pairFormula 3 2 1 7 8 6 5
        (cons t (cons (natSet c) (cons (natSet b) (cons (natSet a) (cons z e)))))
        a b c rfl rfl rfl rfl rfl rfl rfl).mp hpr
      exact ⟨a,b,by simpa only [htnm,hc,numberPair] using hz⟩
    · rintro ⟨n,m,rfl⟩
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,
        natSet (Nat.pair n m),(mem_omega _).mpr ⟨Nat.pair n m,rfl⟩,numberPair (n,m),
        natPair_mem n m,rfl,rfl,?_⟩
      exact (eval_pairFormula 3 2 1 7 8 6 5
        (cons (numberPair (n,m)) (cons (natSet (Nat.pair n m)) (cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (numberPair (n,m)) (natSet (Nat.pair n m))) e)))))
        n m (Nat.pair n m) rfl rfl rfl rfl rfl rfl rfl).mpr rfl
  have eq : ZFSet.sep (fun z => pairingFormula.Eval (cons z e))
      (ZFSet.prod pairNumbers ZFSet.omega) = pairingSet.{u} := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep,hφ,pairingSet]
  exact eq ▸ hs

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section

variable {M : ZFSet.{u}} (C : Context M)
include C

theorem Context.omega_mem : ZFSet.omega.{u} ∈ M :=
  BoundedSetTheory.omega_mem M C.transitive C.separation C.infinity

theorem Context.nat_mem (n : ℕ) : natSet.{u} n ∈ M :=
  C.transitive _ C.omega_mem _ ((mem_omega _).mpr ⟨n,rfl⟩)

theorem Context.prod_mem {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    ZFSet.prod a b ∈ M :=
  product_mem M C.transitive C.pairing C.union C.power C.separation ha hb

theorem graph_of_formula (f : ℕ → ℕ) (p : Formula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M)
    (hp : ∀ n m, p.Eval (cons (ZFSet.pair (natSet n) (natSet m)) e) ↔ m = f n) :
    HasGraph M f := by
  refine ⟨ZFSet.sep (fun z => p.Eval (cons z e)) pairNumbers,
    sep_mem M C.transitive C.separation p e he (C.prod_mem C.omega_mem C.omega_mem),?_⟩
  intro n m
  simp only [ZFSet.mem_sep,natPair_mem,true_and,hp]

theorem graph_of_relation (f : ℕ → ℕ) (p : Formula) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M)
    (hp : ∀ n m, p.Eval (cons (natSet m) (cons (natSet n) e)) ↔ m = f n) :
    HasGraph M f := by
  let r : ℕ → ℕ := fun i => if i < 2 then i else i+2
  let q : Formula := .existsMem 1 (.existsMem 2
    (.conj (.orderedPair 2 1 0) (p.rename r)))
  let d := cons ZFSet.omega e
  apply graph_of_formula C f q d
  · intro i
    cases i with
    | zero => exact C.omega_mem
    | succ i => exact he i
  · intro n m
    simp only [q,d,Formula.Eval,Formula.eval_orderedPair,Formula.eval_rename_comp,
      cons_zero,cons_succ]
    constructor
    · rintro ⟨x,hx,y,hy,hz,hp'⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hz
      have hh : cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (natSet n) (natSet m)) (cons ZFSet.omega e))) ∘ r =
          cons (natSet m) (cons (natSet n) e) := by
        funext i
        rcases i with _|_|i <;> simp [r,cons]
      rw [hh] at hp'
      exact (hp n m).mp hp'
    · intro h
      refine ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,natSet m,
        (mem_omega _).mpr ⟨m,rfl⟩,rfl,?_⟩
      have hh : cons (natSet m) (cons (natSet n)
          (cons (ZFSet.pair (natSet n) (natSet m)) (cons ZFSet.omega e))) ∘ r =
          cons (natSet m) (cons (natSet n) e) := by
        funext i
        rcases i with _|_|i <;> simp [r,cons]
      rw [hh]
      exact (hp n m).mpr h

theorem const_graph (k : ℕ) : HasGraph M (fun _ => k) := by
  apply graph_of_relation C _ (.equal 0 2) (fun _ => natSet k) (fun _ => C.nat_mem k)
  intro n m
  exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩

theorem id_graph : HasGraph M id := by
  apply graph_of_relation C _ (.equal 0 1) (fun _ => ZFSet.omega) (fun _ => C.omega_mem)
  intro n m
  exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩

theorem succ_graph : HasGraph M Nat.succ := by
  refine ⟨successorSet,successorSet_mem M C.transitive C.pairing C.union C.power
    C.separation C.infinity,?_⟩
  intro n m
  rw [pair_mem_successorSet ((mem_omega _).mpr ⟨n,rfl⟩)
    ((mem_omega _).mpr ⟨m,rfl⟩),setSucc_nat]
  exact ⟨fun h => natSet_injective h,fun h => congrArg natSet h⟩

theorem HasGraph.comp {f g : ℕ → ℕ} (hf : HasGraph M f) (hg : HasGraph M g) :
    HasGraph M (fun n => f (g n)) := by
  obtain ⟨a,ha,hac⟩ := hf
  obtain ⟨b,hb,hbc⟩ := hg
  let e := cons ZFSet.omega (cons a (fun _ => b))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,C.omega_mem,ha,hb]
  apply graph_of_relation C _ (.existsMem 2 (.conj (.pairMem 2 0 5) (.pairMem 0 1 4))) e he
  intro n m
  simp only [Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e]
  rw [omega_exists]
  simp only [hac,hbc]
  constructor
  · rintro ⟨k,rfl,h⟩
    exact h
  · intro h
    exact ⟨g n,rfl,h⟩

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section
variable {M : ZFSet.{u}} (C : Context M)
include C

theorem Context.pairing_mem : pairingSet.{u} ∈ M :=
  pairingSet_mem M C.transitive C.pairing C.union C.power C.separation C.infinity

theorem Context.pairNumbers_mem : pairNumbers.{u} ∈ M := C.prod_mem C.omega_mem C.omega_mem

omit C in
@[simp] theorem pairing_code (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ pairingSet ↔
      k = Nat.pair n m := pairingSet_code n m k

theorem left_graph : HasGraph M (fun n => (Nat.unpair n).1) := by
  let e := cons ZFSet.omega (cons pairNumbers (fun _ => pairingSet))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,C.omega_mem,C.pairNumbers_mem,C.pairing_mem]
  apply graph_of_relation C _ (.existsMem 2 (tripleFormula 1 0 2 5 4)) e he
  intro n m
  simp only [Formula.Eval,eval_tripleFormula,cons_zero,cons_succ,e]
  rw [omega_exists]
  simp only [natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨k,rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair n).2,by rw [h,Nat.pair_unpair]⟩

theorem right_graph : HasGraph M (fun n => (Nat.unpair n).2) := by
  let e := cons ZFSet.omega (cons pairNumbers (fun _ => pairingSet))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [e,C.omega_mem,C.pairNumbers_mem,C.pairing_mem]
  apply graph_of_relation C _ (.existsMem 2 (tripleFormula 0 1 2 5 4)) e he
  intro n m
  simp only [Formula.Eval,eval_tripleFormula,cons_zero,cons_succ,e]
  rw [omega_exists]
  simp only [natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨k,rfl⟩
    simp
  · intro h
    exact ⟨(Nat.unpair n).1,by rw [h,Nat.pair_unpair]⟩

theorem HasGraph.pair {f g : ℕ → ℕ} (hf : HasGraph M f) (hg : HasGraph M g) :
    HasGraph M (fun n => Nat.pair (f n) (g n)) := by
  obtain ⟨a,ha,hac⟩ := hf
  obtain ⟨b,hb,hbc⟩ := hg
  let e := cons ZFSet.omega (cons a (cons b (cons pairNumbers (fun _ => pairingSet))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp [e,C.omega_mem,ha,hb,C.pairNumbers_mem,C.pairing_mem]
  apply graph_of_relation C _ (.existsMem 2 (.existsMem 3
    (.conj (.pairMem 3 1 5) (.conj (.pairMem 3 0 6) (tripleFormula 1 0 2 8 7))))) e he
  intro n m
  simp only [Formula.Eval,Formula.eval_pairMem,eval_tripleFormula,cons_zero,cons_succ,e]
  simp_rw [omega_exists]
  simp only [hac,hbc,natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨i,j,rfl,rfl,h⟩
    exact h
  · intro h
    exact ⟨f n,g n,rfl,rfl,h⟩

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelFunctionIteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section
variable {M : ZFSet.{u}} (C : Context M)
include C

omit C in
theorem natLift_closed (f : ℕ → ℕ) : ∀ x ∈ ZFSet.omega.{u}, natLift f x ∈ ZFSet.omega := by
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact (mem_omega _).mpr ⟨f n,natLift_nat f n⟩

omit C in
theorem iterate_natLift (f : ℕ → ℕ) (n m : ℕ) :
    (natLift f)^[n] (natSet.{u} m) = natSet (f^[n] m) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,natLift_nat,Function.iterate_succ_apply']

omit C in
theorem natIteration_code (f : ℕ → ℕ) (n m k : ℕ) :
    ZFSet.pair (ZFSet.pair (natSet.{u} n) (natSet m)) (natSet k) ∈ natIteration f ↔
      k = f^[n] m := by
  rw [natIteration,mem_iterationSet _ (natLift_closed f)]
  constructor
  · rintro ⟨i,x,hx,he⟩
    obtain ⟨hi,hk⟩ := ZFSet.pair_inj.mp he
    obtain ⟨hnum,rfl⟩ := ZFSet.pair_inj.mp hi
    have hin := natSet_injective hnum
    rw [←hin,iterate_natLift] at hk
    exact natSet_injective hk
  · intro h
    refine ⟨n,natSet m,(mem_omega _).mpr ⟨m,rfl⟩,?_⟩
    rw [iterate_natLift,h]

theorem natIteration_mem {f : ℕ → ℕ} (hf : HasGraph M f) : natIteration.{u} f ∈ M := by
  obtain ⟨g,hg,hgc⟩ := hf
  apply iterationSet_mem M C.transitive C.pairing C.union C.power C.separation C.infinity
    C.omega_mem hg (natLift f) (natLift_closed f)
  intro x hx y hy
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  obtain ⟨m,rfl⟩ := (mem_omega y).mp hy
  rw [hgc,natLift_nat]
  exact ⟨fun h => congrArg natSet h,fun h => natSet_injective h⟩

theorem HasGraph.iterate {f : ℕ → ℕ} (hf : HasGraph M f) :
    HasGraph M (fun v => f^[(Nat.unpair v).2] (Nat.unpair v).1) := by
  let e := cons ZFSet.omega (cons pairNumbers (cons pairingSet (fun _ => natIteration f)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|i <;>
      simp [e,C.omega_mem,C.pairNumbers_mem,C.pairing_mem,natIteration_mem C hf]
  apply graph_of_relation C _ (.existsMem 2 (.existsMem 3 (.existsMem 5
    (.conj (tripleFormula 2 1 4 7 6)
      (.conj (.orderedPair 0 1 2) (.pairMem 0 3 8)))))) e he
  intro n m
  simp only [Formula.Eval,eval_tripleFormula,Formula.eval_orderedPair,Formula.eval_pairMem,
    cons_zero,cons_succ,e]
  simp_rw [omega_exists]
  simp only [natPair_mem,true_and,pairing_code]
  constructor
  · rintro ⟨a,b,t,ht,hn,rfl,h⟩
    rw [natIteration_code] at h
    simpa only [hn,Nat.unpair_pair] using h
  · intro h
    refine ⟨(Nat.unpair n).1,(Nat.unpair n).2,
      ZFSet.pair (natSet (Nat.unpair n).2) (natSet (Nat.unpair n).1),
      natPair_mem _ _,(Nat.pair_unpair n).symm,rfl,?_⟩
    exact (natIteration_code _ _ _ _).mpr h

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelPrimrec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelFunctions
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration SetModelArithmetic
universe u
noncomputable section

variable {M : ZFSet.{u}}

theorem HasGraph.congr {f g : ℕ → ℕ} (hf : HasGraph M f) (h : ∀ n, f n = g n) :
    HasGraph M g := (funext h) ▸ hf

theorem iterate_recStep (f g : ℕ → ℕ) (z n : ℕ) :
    (recStep g)^[n] (recStart f z) = Nat.pair z (Nat.pair n (recValue f g z n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    simp only [recStep,Nat.unpair_pair,recValue]

theorem HasGraph.prec (C : Context M) {f g : ℕ → ℕ}
    (hf : HasGraph M f) (hg : HasGraph M g) :
    HasGraph M (Nat.unpaired (recValue f g)) := by
  have hs : HasGraph M (recStep g) :=
    HasGraph.pair C (left_graph C) (HasGraph.pair C
      (HasGraph.comp C (succ_graph C) (HasGraph.comp C (left_graph C) (right_graph C))) hg)
  have hz : HasGraph M (recStart f) :=
    HasGraph.pair C (id_graph C) (HasGraph.pair C (const_graph C 0) hf)
  have hp := HasGraph.pair C (HasGraph.comp C hz (left_graph C)) (right_graph C)
  have hi := HasGraph.comp C (HasGraph.iterate C hs) hp
  have h := HasGraph.comp C (HasGraph.comp C (right_graph C) (right_graph C)) hi
  apply h.congr
  intro v
  simp only [Nat.unpair_pair,iterate_recStep,Nat.unpaired]

theorem natPrimrec_graph (C : Context M) {f : ℕ → ℕ} (hf : Nat.Primrec f) : HasGraph M f := by
  induction hf with
  | zero => exact const_graph C 0
  | succ => exact succ_graph C
  | left => exact left_graph C
  | right => exact right_graph C
  | pair hf hg ihf ihg => exact HasGraph.pair C ihf ihg
  | comp hf hg ihf ihg => exact HasGraph.comp C ihf ihg
  | prec hf hg ihf ihg => exact HasGraph.prec C ihf ihg

theorem primrec_graph (C : Context M) {f : ℕ → ℕ} (hf : Primrec f) : HasGraph M f :=
  natPrimrec_graph C (Primrec.nat_iff.mp hf)

end
end TuringRigidity.SetModelFunctions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelArithmeticSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable
universe u
noncomputable section

variable {M : ZFSet.{u}}

@[simp] theorem pairCode_nat (i j k : ℕ) :
    PairCode (natSet.{u} i) (natSet j) (natSet k) ↔ k = Nat.pair i j := by
  simp only [PairCode,natPair_mem,true_and,pairing_code]

end
end TuringRigidity.SetModelSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenWordCodeGraph
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory SetModelFunctions SetModelArithmetic SetModelReals
open Encodable EncodedForcing

theorem wordBit_primrec : Primrec wordBit :=
  CommonIdeal.bit_primrec.comp ((Primrec.list_getD false).comp
    (word_primrec.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair))

theorem wordGraphFormula_spec (gl gb : ZFSet.{0})
    (hl : GraphCode gl (fun n => (word n).length)) (hb : GraphCode gb wordBit)
    (n : ℕ) (q : ZFSet.{0}) :
    wordGraphFormula.Eval (wordGraphEnv q (natSet n) gl gb) ↔
      q = wordCode (word n) := by
  simp only [wordGraphFormula,wordGraphEnv,Formula.Eval,Formula.eval_pairMem,
    Formula.eval_functionGraph,Formula.eval_allMem,eval_tripleFormula,
    cons_zero,cons_succ]
  simp_rw [omega_exists]
  simp only [hl]
  constructor
  · rintro ⟨l,rfl,hq,hi⟩
    have hq' : FunctionGraph (natSet (word n).length) alphabet q := hq
    have hbits (i : ℕ) (h : i < (word n).length) :
        ZFSet.pair (natSet i) (bitSet (word n)[i]) ∈ q := by
      obtain ⟨k,b,⟨_,hk⟩,hb',hi'⟩ := hi (natSet i) ((natSet_mem_natSet _ _).mpr h)
      have hk' : k = Nat.pair n i := (pairing_code n i k).mp hk
      have hb'' := (hb k b).mp hb'
      subst k
      subst b
      simpa [wordBit,List.getD,h,bitSet] using hi'
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨x,hx,y,_,rfl⟩ := hq'.1 z hz
      obtain ⟨i,hi,rfl⟩ := (mem_natSet _ _).mp hx
      have hy := hq'.functional ((natSet_mem_natSet _ _).mpr hi) hz (hbits i hi)
      rw [hy]
      exact (mem_wordCode _ _).mpr ⟨⟨i,hi⟩,rfl⟩
    · intro hz
      obtain ⟨i,rfl⟩ := (mem_wordCode _ _).mp hz
      exact hbits i.val i.isLt
  · rintro rfl
    refine ⟨(word n).length,rfl,wordCode_function _,?_⟩
    intro x hx
    obtain ⟨i,hi,rfl⟩ := (mem_natSet _ _).mp hx
    refine ⟨Nat.pair n i,wordBit (Nat.pair n i),⟨natPair_mem _ _,
      (pairing_code _ _ _).mpr rfl⟩,(hb _ _).mpr rfl,?_⟩
    simp only [wordBit,Nat.unpair_pair]
    exact (pair_mem_wordCode _ _ _).mpr ⟨hi,by simp [List.getD,hi]⟩

theorem mem_wordCodeGraph (z : ZFSet.{0}) : z ∈ wordCodeGraph ↔
    ∃ n : ℕ, z = ZFSet.pair (natSet n) (wordCode (word n)) := by
  simp only [wordCodeGraph,ZFSet.mem_range,eq_comm]

theorem pair_mem_wordCodeGraph (n : ℕ) (q : ZFSet.{0}) :
    ZFSet.pair (natSet n) q ∈ wordCodeGraph ↔ q = wordCode (word n) := by
  rw [mem_wordCodeGraph]
  constructor
  · rintro ⟨k,hk⟩
    obtain ⟨hn,hq⟩ := ZFSet.pair_inj.mp hk
    have hn' := natSet_injective hn
    simpa only [← hn'] using hq
  · intro h
    exact ⟨n,by rw [h]⟩

theorem wordCodeGraph_function : FunctionGraph ZFSet.omega conditions wordCodeGraph := by
  constructor
  · intro z hz
    obtain ⟨n,rfl⟩ := (mem_wordCodeGraph z).mp hz
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,wordCode (word n),
      (mem_conditions _).mpr ⟨_,wordCode_function _⟩,rfl⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨wordCode (word n),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,
      (pair_mem_wordCodeGraph _ _).mpr rfl,
      fun y _ hy => (pair_mem_wordCodeGraph n y).mp hy⟩

theorem wordCodeGraph_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) :
    wordCodeGraph ∈ M := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  obtain ⟨gl,hgl,hl⟩ := primrec_graph C (Primrec.list_length.comp word_primrec)
  obtain ⟨gb,hgb,hb⟩ := primrec_graph C wordBit_primrec
  let r : ℕ → ℕ := fun i => if i < 2 then i else i+3
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (wordGraphFormula.rename r)))
  let e := cons ZFSet.omega (cons conditions (cons gl (cons gb
    (cons ZFSet.omega (cons alphabet (cons pairNumbers (fun _ => pairingSet)))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|_|_|i
    · exact C.omega_mem
    · exact conditions_mem M hM hT
    · exact hgl
    · exact hgb
    · exact C.omega_mem
    · exact alphabet_mem M hM hT
    · exact C.pairNumbers_mem
    · exact C.pairing_mem
  have hs := sep_mem M hM C.separation φ e he
    (C.prod_mem C.omega_mem (conditions_mem M hM hT))
  have hspec (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ wordCodeGraph := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_rename_comp,
      cons_zero,cons_succ,e]
    rw [omega_exists,mem_wordCodeGraph]
    have hh (n : ℕ) (q : ZFSet.{0}) :
        cons q (cons (natSet n) (cons z e)) ∘ r = wordGraphEnv q (natSet n) gl gb := by
      funext i
      rcases i with _|_|i <;> simp [r,e,wordGraphEnv,cons]
    simp_rw [show ∀ n q, (cons q (cons (natSet n) (cons z
      (cons ZFSet.omega (cons conditions (cons gl (cons gb (cons ZFSet.omega
      (cons alphabet (cons pairNumbers (fun _ => pairingSet))))))))))) ∘ r =
      wordGraphEnv q (natSet n) gl gb from hh]
    simp_rw [wordGraphFormula_spec gl gb hl hb]
    constructor
    · rintro ⟨n,q,_,hz,rfl⟩
      exact ⟨n,hz⟩
    · rintro ⟨n,rfl⟩
      exact ⟨n,wordCode (word n),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,rfl,rfl⟩
  have heq : ZFSet.sep (fun z => φ.Eval (cons z e))
      (ZFSet.prod ZFSet.omega conditions) = wordCodeGraph := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,hspec]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr (wordCodeGraph_function.1 z hz),hz⟩⟩
  exact heq ▸ hs

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductConditions
open TransitiveNameModel BoundedSetTheory
attribute [local instance] InternalCollapse.order

theorem code_mem (M p s : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hp : p ∈ M) (hs : s ∈ M) : code p s ∈ M := by
  have hn (n : ℕ) : natSet n ∈ M :=
    hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  exact binary_union_mem M hM hT.pairing hT.union
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (singleton_mem M hM hT.pairing (hn 0)) hp)
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (singleton_mem M hM hT.pairing (hn 1)) hs)

theorem codeFormula_spec (p s z z0 z1 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) :
    (codeFormula p s z z0 z1).Eval e ↔ e z = code (e p) (e s) := by
  simp only [codeFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_disj,
    Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,h0,h1]
  constructor
  · rintro ⟨ha,hb,hc⟩
    apply ZFSet.ext; intro x
    exact ⟨fun hx => (mem_code _ _ _).mpr (ha x hx),fun hx =>
      ((mem_code _ _ _).mp hx).elim (fun ⟨y,hy,he⟩ => he ▸ hb y hy)
        (fun ⟨y,hy,he⟩ => he ▸ hc y hy)⟩
  · intro h; rw [h]
    exact ⟨fun x hx => (mem_code _ _ _).mp hx,
      fun x hx => (left_mem _ _ _).mpr hx,fun x hx => (right_mem _ _ _).mpr hx⟩

theorem code_bounded (a b p s : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) :
    code p s ⊆ bound a b :=
  (code_subset _ _ _ _).mpr ⟨fun _ hx => ZFSet.mem_sUnion.mpr ⟨p,hp,hx⟩,
    fun _ hx => ZFSet.mem_sUnion.mpr ⟨s,hs,hx⟩⟩

theorem internal_product (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) :
    ∃ c ∈ M, (∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s) ∧
      ∃ g ∈ M, FunctionGraph (ZFSet.prod a b) c g ∧
        (∀ p ∈ a, ∀ s ∈ b, ∀ z, ZFSet.pair (ZFSet.pair p s) z ∈ g ↔ z = code p s) ∧
        (∀ z ∈ c, ∃ x ∈ ZFSet.prod a b, ZFSet.pair x z ∈ g) := by
  have hbound := code_mem M _ _ hM hT (union_mem M hM hT.union ha) (union_mem M hM hT.union hb)
  obtain ⟨Q,hQ,hQdef⟩ := internal_power M hM hT.powerSet hbound
  have hcode (p s : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) : code p s ∈ Q :=
    (hQdef _).mpr ⟨code_mem M p s hM hT (hM a ha p hp) (hM b hb s hs),code_bounded a b p s hp hs⟩
  let e := cons a (cons b (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    exact ha; exact hb
    all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  let c := Q.sep (fun z => ∃ p ∈ a, ∃ s ∈ b, z = code p s)
  have hsepCode (left right value : ZFSet.{0}) :
      (codeFormula 1 0 2 5 6).Eval (cons right (cons left (cons value e))) ↔
        value = code left right :=
    codeFormula_spec 1 0 2 5 6 _ rfl rfl
  have hc : c ∈ M := by
    simpa only [c,Formula.Eval,hsepCode,
      cons_zero,cons_succ,e] using
      sep_mem M hM hT.separation.finitePrefix.bounded
        (.existsMem 1 (.existsMem 3 (codeFormula 1 0 2 5 6))) e he hQ
  have hcs (z : ZFSet.{0}) : z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s := by
    change (z ∈ Q.sep _) ↔ _
    rw [ZFSet.mem_sep]
    exact ⟨And.right,fun h@⟨p,hp,s,hs,hz⟩ => ⟨hz ▸ hcode p s hp hs,h⟩⟩
  let v := cons (ZFSet.prod a b) (cons c e)
  have hprod := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb
  have hv : ∀ i, v i ∈ M := by
    intro i; rcases i with _|_|i; exact hprod; exact hc; exact he i
  have hgraphCode (left right value point entry : ZFSet.{0}) :
      (codeFormula 1 0 2 9 10).Eval
        (cons right (cons left (cons value (cons point (cons entry v))))) ↔
          value = code left right :=
    codeFormula_spec 1 0 2 9 10 _ rfl rfl
  let φ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0)
    (.existsMem 5 (.existsMem 7 (.conj (.orderedPair 3 1 0) (codeFormula 1 0 2 9 10))))))
  let g := (ZFSet.prod (ZFSet.prod a b) c).sep (fun z => φ.Eval (cons z v))
  have hg : g ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded φ v hv
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hprod hc)
  have hgs (p s z : ZFSet.{0}) (hp : p ∈ a) (hs : s ∈ b) :
      ZFSet.pair (ZFSet.pair p s) z ∈ g ↔ z = code p s := by
    simp only [g,ZFSet.mem_sep,φ,Formula.Eval,Formula.eval_orderedPair,
      hgraphCode,cons_zero,cons_succ,v,e]
    constructor
    · rintro ⟨_,x,_,y,_,hxy,p',_,s',_,hx,hy⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxy
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hx
      exact hy
    · intro hz
      have hzc := (hcs z).mpr ⟨p,hp,s,hs,hz⟩
      have hps := ZFSet.pair_mem_prod.mpr ⟨hp,hs⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hps,hzc⟩,_,hps,z,hzc,rfl,p,hp,s,hs,rfl,hz⟩
  refine ⟨c,hc,hcs,g,hg,⟨?_,?_⟩,(fun p hp s hs z => hgs p s z hp hs),?_⟩
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro x hx
    obtain ⟨p,hp,s,hs,rfl⟩ := ZFSet.mem_prod.mp hx
    exact ⟨code p s,(hcs _).mpr ⟨p,hp,s,hs,rfl⟩,(hgs p s _ hp hs).mpr rfl,
      fun y _ hy => (hgs p s y hp hs).mp hy⟩
  · intro z hz
    obtain ⟨p,hp,s,hs,hz⟩ := (hcs z).mp hz
    exact ⟨ZFSet.pair p s,ZFSet.pair_mem_prod.mpr ⟨hp,hs⟩,(hgs p s z hp hs).mpr hz⟩

end TuringRigidity.TaggedProductConditions

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_TaggedProductGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.TaggedProductGeneric
open TransitiveNameModel BoundedSetTheory CountableForcing TaggedProductConditions
open CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem joint_mem (a b c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (H : GenericFilter (Conditions b))
    (p : Conditions a) (s : Conditions b) :
    productMap a b c hcs (p,s) ∈ (joint a b c hcs G H).carrier ↔
      p ∈ G.carrier ∧ s ∈ H.carrier := by
  change (productIso a b c hcs).symm ((productIso a b c hcs) (p,s)) ∈ (SourceEquationTail.productFilter G H).carrier ↔ _
  rw [OrderIso.symm_apply_apply]
  rfl

theorem sectionSet_mem (M a b D r : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M) (hr : r ∈ M) : sectionSet a b D r ∈ M := by
  let e := cons b (cons D (cons r (cons (natSet 0) (fun _ => natSet 1))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    exact hb; exact hD; exact hr
    all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hsectionCode (left right value : ZFSet.{0}) :
      (codeFormula 2 1 0 6 7).Eval (cons value (cons right (cons left e))) ↔
        value = code left right :=
    codeFormula_spec 2 1 0 6 7 _ rfl rfl
  simpa only [sectionSet,Formula.Eval,hsectionCode,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (codeFormula 2 1 0 6 7) (.subset 5 1)))) e he ha

theorem fiberSet_mem (N b D g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hb : b ∈ N) (hD : D ∈ N) (hg : g ∈ N) : fiberSet b D g ∈ N := by
  let e := cons g (cons D (cons (natSet 0) (fun _ => natSet 1)))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|i
    exact hg; exact hD
    all_goals exact hN _ (sourceT_omega_mem N hN hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)
  have hfiberCode (left right value : ZFSet.{0}) :
      (codeFormula 1 2 0 5 6).Eval (cons value (cons left (cons right e))) ↔
        value = code left right :=
    codeFormula_spec 1 2 0 5 6 _ rfl rfl
  simpa only [fiberSet,Formula.Eval,hfiberCode,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (codeFormula 1 2 0 5 6))) e he hb

theorem sectionSet_dense (a b c D : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (hD : Dense {x : Conditions c | label c x ∈ D}) (r : Conditions b) :
    Dense {p : Conditions a | label a p ∈ sectionSet a b D (label b r)} := by
  intro p
  obtain ⟨x,hx,hxD⟩ := hD (productMap a b c hcs (p,r))
  let y := (productIso a b c hcs).symm x
  have hy : y ≤ (p,r) := by
    have hh := (productIso a b c hcs).symm.monotone hx
    change (productIso a b c hcs).symm x ≤ (productIso a b c hcs).symm ((productIso a b c hcs) (p,r)) at hh
    simpa only [OrderIso.symm_apply_apply] using hh
  have hl : label c x = code (label a y.1) (label b y.2) := by
    rw [←label_productMap a b c hcs y]
    exact congrArg (label c) ((productIso a b c hcs).apply_symm_apply x).symm
  exact ⟨y.1,hy.1,ZFSet.mem_sep.mpr ⟨label_mem a y.1,label b y.2,label_mem b y.2,
    label c x,hxD,hl,hy.2⟩⟩

theorem fiberSet_dense (M a b c D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (hd : Dense {x : Conditions c | label c x ∈ D})
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    Dense {r : Conditions b | label b r ∈ fiberSet b D (genericFilterSet a G.carrier)} := by
  intro r
  obtain ⟨p,hp,hpr⟩ := hG (sectionSet a b D (label b r))
    (sectionSet_mem M a b D _ hM hT ha hb hD (hM b hb _ (label_mem b r)))
    (sectionSet_dense a b c D hcs hd r)
  obtain ⟨_,s,hs,z,hz,hzs,hrs⟩ := ZFSet.mem_sep.mp hpr
  obtain ⟨s,rfl⟩ := label_surjective b hs
  exact ⟨s,hrs,ZFSet.mem_sep.mpr ⟨label_mem b s,label a p,
    (mem_genericFilterSet a G.carrier _).mpr ⟨p,hp,rfl⟩,z,hz,hzs⟩⟩

theorem joint_ground_generic (M a b c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M)
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G)
    (H : GenericFilter (Conditions b))
    (hH : AtomicForcing.GroundGeneric (genericExtensionSet M a G.carrier) H) :
    AtomicForcing.GroundGeneric M (joint a b c hcs G H) := by
  obtain ⟨hN,hTN,hMN,hgN⟩ := RegularTreeExtension.extension_properties M a hM hT ha G hG
  intro D hD hd
  obtain ⟨s,hs,hsE⟩ := hH (fiberSet b D (genericFilterSet a G.carrier))
    (fiberSet_mem _ b D _ hN hTN (hMN hb) (hMN hD) hgN)
    (fiberSet_dense M a b c D hM hT ha hb hD hcs hd G hG)
  obtain ⟨_,p,hp,z,hz,he⟩ := ZFSet.mem_sep.mp hsE
  obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet a G.carrier p).mp hp
  refine ⟨productMap a b c hcs (p,s),(joint_mem a b c hcs G H p s).mpr ⟨hpG,hs⟩,?_⟩
  rw [label_productMap,←he]
  exact hz

end TuringRigidity.TaggedProductGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticCommonRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticCommonRun
open Encodable UniformArithmetic UniformOracle
open EncodedForcing (word)

theorem word_eq (s : ℕ) : BorelGeneric.word s = word s := rfl

theorem run_iff_trial (p : OracleCode) (d : Nat.Partrec.Code)
    (hd : ∀ L w, d.eval (Nat.pair (encode L) w) = CommonIdeal.finiteRun p [] L w)
    (A : Oracle) (s n a : ℕ) :
    a ∈ CommonIdeal.run A p (word s) n ↔
      ∃ m c t, Prefix A m c ∧
        d.evaln t (Nat.pair (encode (UniformArithmetic.table c)) (Nat.pair s n)) = some a := by
  have happrox := CommonIdeal.finiteRun_approximates A p [] s n
  simp only [List.nil_append,word_eq] at happrox
  constructor
  · intro ha
    obtain ⟨m,hm⟩ := happrox.2 a ha
    have hh := hm m le_rfl
    dsimp only at hh
    rw [←hd] at hh
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp hh
    let L := oraclePrefix (fun k => CommonIdeal.bit (A k)) m
    refine ⟨m,encode L,t,?_,?_⟩
    · rw [prefix_iff]
      simp [UniformArithmetic.table,L]
    · simpa [UniformArithmetic.table,L] using ht
  · rintro ⟨m,c,t,hp,ht⟩
    have hh := Nat.Partrec.Code.evaln_sound ht
    rw [hd,(prefix_iff A m c).mp hp] at hh
    exact happrox.1 m a hh

theorem run_arith (p : OracleCode) {s n a : ℕ → ℕ}
    (hs : Primrec s) (hn : Primrec n) (ha : Primrec a) :
    Arith (fun O v => a v ∈ CommonIdeal.run (O 0) p (word (s v)) (n v)) := by
  obtain ⟨d,hd⟩ := CommonIdeal.finiteRun_code p []
  let L := left_primrec
  let R := right_primrec
  let base := L.comp (L.comp L)
  have hO : ArithmeticOracle (fun O _ => O 0) := (Arith.query 0).comp _ R
  have hp := prefix_arith hO (Primrec.const 0) (R.comp (L.comp L)) (R.comp L)
  have ht : Arith (fun (_ : Oracles) v =>
      d.evaln (right v)
        (Nat.pair (encode (UniformArithmetic.table (right (left v))))
          (Nat.pair (s (left (left (left v)))) (n (left (left (left v)))))) =
        some (a (left (left (left v))))) :=
    .pure _ (Primrec.eq.comp
      (Nat.Partrec.Code.primrec_evaln.comp
        ((R.pair (Primrec.const d)).pair
          (Primrec₂.natPair.comp (Primrec.encode.comp (table_primrec.comp (R.comp L)))
            (Primrec₂.natPair.comp (hs.comp base) (hn.comp base)))))
      (Primrec.option_some.comp (ha.comp base)))
  apply (hp.and ht).ex.ex.ex.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  exact (run_iff_trial p d hd (O 0) (s v) (n v) (a v)).symm

end TuringRigidity.ArithmeticCommonRun

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticCommonRequirement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticCommonRequirement
open Encodable UniformArithmetic
open EncodedForcing (word word_primrec)

theorem prefix_arith {s t : ℕ → ℕ} (hs : Primrec s) (ht : Primrec t) :
    Arith (fun (_ : Oracles) v => word (s v) <+: word (t v)) :=
  (Arith.pure _ (Primrec.eq.comp (word_primrec.comp hs)
    (Primrec.list_take.comp (Primrec.list_length.comp (word_primrec.comp hs))
      (word_primrec.comp ht)))).congr (fun _ _ => List.prefix_iff_eq_take.symm)

theorem disagree_arith (p q : OracleCode) {s t : ℕ → ℕ}
    (hs : Primrec s) (ht : Primrec t) :
    Arith (fun O v => CommonIdeal.Disagree (O 0) p q (word (s v)) (word (t v))) := by
  let L := left_primrec
  let R := right_primrec
  let base := L.comp (L.comp L)
  have hp := ArithmeticCommonRun.run_arith p (hs.comp base) (R.comp (L.comp L)) (R.comp L)
  have hq := ArithmeticCommonRun.run_arith q (ht.comp base) (R.comp (L.comp L)) R
  have he := (equal (R.comp L) R).neg
  exact (he.and (hp.and hq)).ex.ex.ex.congr (fun _ _ => by
    simp only [CommonIdeal.Disagree,left,right,Nat.unpair_pair])

theorem agree_arith (p q : OracleCode) {s t : ℕ → ℕ}
    (hs : Primrec s) (ht : Primrec t) :
    Arith (fun O v => CommonIdeal.Agree (O 0) p q (word (s v)) (word (t v))) := by
  let L := left_primrec
  let R := right_primrec
  let L2 := L.comp L
  let L3 := L.comp L2
  let L4 := L.comp L3
  let base := L.comp L4
  have hsu := prefix_arith (hs.comp base) (R.comp L4)
  have htv := prefix_arith (ht.comp base) (R.comp L3)
  have hp := ArithmeticCommonRun.run_arith p (R.comp L4) (R.comp L2) (R.comp L)
  have hq := ArithmeticCommonRun.run_arith q (R.comp L3) (R.comp L2) R
  have he := equal (R.comp L) R
  apply (hsu.imp (htv.imp (hp.imp (hq.imp he)))).all.all.all.all.all.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · intro h u w n a b hu hw ha hb
    exact h (encode u) (encode w) n a b
      (by simpa [word] using hu) (by simpa [word] using hw)
      (by simpa [word] using ha) (by simpa [word] using hb)
  · intro h u w n a b hu hw ha hb
    exact h (word u) (word w) n a b hu hw ha hb

theorem requirement_arith (p q : OracleCode) {s t : ℕ → ℕ}
    (hs : Primrec s) (ht : Primrec t) :
    Arith (fun O v => CommonIdeal.Requirement (O 0) p q (word (s v)) (word (t v))) :=
  (disagree_arith p q hs ht).or (agree_arith p q hs ht)

end TuringRigidity.ArithmeticCommonRequirement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalCohenProductSets
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.NumericalCohenProductSets
open TransitiveNameModel BoundedSetTheory SetModelFunctions SetModelArithmetic
open InternalCohen Encodable UniformArithmetic
open EncodedForcing (word)
open TaggedProductConditions (code)

theorem image_mem (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (B : Oracle) (hB : realCode B ∈ M) : image c B ∈ M := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  obtain ⟨gl,hgl,hl⟩ := primrec_graph C left_primrec
  obtain ⟨gr,hgr,hr⟩ := primrec_graph C right_primrec
  let e := cons (realCode B) (cons ZFSet.omega (cons conditions
    (cons gl (cons gr (cons wordCodeGraph (cons (natSet 0) (fun _ => natSet 1)))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|_|_|i
    · exact hB
    · exact C.omega_mem
    · exact conditions_mem M hM hT
    · exact hgl
    · exact hgr
    · exact wordCodeGraph_mem M hM hT
    all_goals exact hM _ C.omega_mem _ ((mem_omega _).mpr ⟨_,rfl⟩)
  let φ : Formula := .existsMem 1 (.existsMem 3 (.existsMem 4
    (.existsMem 6 (.existsMem 7
      (.conj (.pairMem 4 3 9) (.conj (.pairMem 4 2 10)
        (.conj (.pairMem 3 1 11) (.conj (.pairMem 2 0 11)
          (TaggedProductConditions.codeFormula 1 0 5 12 13)))))))))
  have hspec (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      ∃ n : ℕ, B n = true ∧
        z = code (wordCode (word (left n))) (wordCode (word (right n))) := by
    have hcode (leftCondition rightCondition leftIndex rightIndex index : ZFSet.{0}) :
        (TaggedProductConditions.codeFormula 1 0 5 12 13).Eval
          (cons rightCondition (cons leftCondition (cons rightIndex
            (cons leftIndex (cons index (cons z e)))))) ↔
              z = code leftCondition rightCondition :=
      TaggedProductConditions.codeFormula_spec 1 0 5 12 13 _ rfl rfl
    simp only [φ,Formula.Eval,Formula.eval_pairMem,hcode,
      cons_zero,cons_succ,e]
    constructor
    · rintro ⟨k,hk,i,hi,j,hj,u,_,v,_,hli,hrj,hu,hv,hz⟩
      obtain ⟨n,rfl⟩ := (mem_omega k).mp (realCode_subset B hk)
      obtain ⟨a,rfl⟩ := (mem_omega i).mp hi
      obtain ⟨b,rfl⟩ := (mem_omega j).mp hj
      have ha := (hl n a).mp hli
      have hb := (hr n b).mp hrj
      subst a
      subst b
      rw [(pair_mem_wordCodeGraph _ _).mp hu,(pair_mem_wordCodeGraph _ _).mp hv] at hz
      exact ⟨n,(natSet_mem_realCode B n).mp hk,hz⟩
    · rintro ⟨n,hn,hz⟩
      exact ⟨natSet n,(natSet_mem_realCode B n).mpr hn,
        natSet (left n),(mem_omega _).mpr ⟨_,rfl⟩,
        natSet (right n),(mem_omega _).mpr ⟨_,rfl⟩,
        wordCode (word (left n)),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,
        wordCode (word (right n)),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,
        (hl _ _).mpr rfl,(hr _ _).mpr rfl,
        (pair_mem_wordCodeGraph _ _).mpr rfl,(pair_mem_wordCodeGraph _ _).mpr rfl,hz⟩
  have hs := sep_mem M hM C.separation φ e he hc
  have heq : c.sep (fun z => φ.Eval (cons z e)) = image c B := by
    apply ZFSet.ext
    intro z
    simp only [image,ZFSet.mem_sep,hspec]
  exact heq ▸ hs

theorem image_spec (c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ conditions, ∃ s ∈ conditions, z = code p s)
    (P : List Bool → List Bool → Prop) (B : Oracle)
    (hB : ∀ n, B n = true ↔ P (word (left n)) (word (right n)))
    (s t : List Bool) : code (wordCode s) (wordCode t) ∈ image c B ↔ P s t := by
  rw [image,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,n,hn,he⟩
    obtain ⟨hs,ht⟩ := (TaggedProductConditions.code_injective _ _ _ _).mp he
    rw [wordCode_injective hs,wordCode_injective ht]
    exact (hB n).mp hn
  · intro h
    refine ⟨(hcs _).mpr ⟨_,(mem_conditions _).mpr ⟨_,wordCode_function _⟩,
      _,(mem_conditions _).mpr ⟨_,wordCode_function _⟩,rfl⟩,
      Nat.pair (encode s) (encode t),?_,?_⟩
    · apply (hB _).mpr
      simpa [left,right,word] using h
    · simp [left,right,word]

end TuringRigidity.NumericalCohenProductSets

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCommonRequirements
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCommonRequirements
open TransitiveNameModel BoundedSetTheory InternalCohen Encodable UniformArithmetic
open EncodedForcing (word)
open TaggedProductConditions (code)
open CountableForcing CohenProductSplitting
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem requirementCodes_true (A : Oracle) (p q : OracleCode) (n : ℕ) :
    requirementCodes A p q n = true ↔
      CommonIdeal.Requirement A p q (word (left n)) (word (right n)) :=
  arithmeticReal_true _ _ _

theorem requirementCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ modelReals M) (p q : OracleCode) :
    realCode (requirementCodes A p q) ∈ M :=
  sourceT_arithmetic_comprehension M hM hT
    (ArithmeticCommonRequirement.requirement_arith p q left_primrec right_primrec)
    (fun _ => A) (fun _ => hA)

theorem denseSet_eq_image (c : ZFSet.{0}) (A : Oracle) (p q : OracleCode) :
    denseSet c A p q = NumericalCohenProductSets.image c (requirementCodes A p q) := by
  apply ZFSet.ext
  intro z
  simp only [denseSet,NumericalCohenProductSets.image,ZFSet.mem_sep,requirementCodes_true]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨s,t,hz,h⟩
    refine ⟨Nat.pair (encode s) (encode t),?_,?_⟩
    · simpa [left,right,word] using h
    · simpa [left,right,word] using hz
  · rintro ⟨n,h,hz⟩
    exact ⟨word (left n),word (right n),hz,h⟩

theorem denseSet_mem (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (A : Oracle) (hA : A ∈ modelReals M) (p q : OracleCode) :
    denseSet c A p q ∈ M := by
  rw [denseSet_eq_image]
  exact NumericalCohenProductSets.image_mem M c hM hT hc _
    (requirementCodes_mem M hM hT A hA p q)

theorem denseSet_spec (c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ conditions, ∃ s ∈ conditions, z = code p s)
    (A : Oracle) (p q : OracleCode) (s t : List Bool) :
    code (wordCode s) (wordCode t) ∈ denseSet c A p q ↔ CommonIdeal.Requirement A p q s t := by
  rw [denseSet_eq_image]
  exact NumericalCohenProductSets.image_spec c hcs _ _ (requirementCodes_true A p q) s t

theorem denseSet_dense (c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ conditions, ∃ s ∈ conditions, z = code p s)
    (A : Oracle) (p q : OracleCode) :
    Dense {x : Conditions c | label c x ∈ denseSet c A p q} := by
  intro x
  let I := productIso conditions conditions c hcs
  let y := I.symm x
  let s := conditionEquiv.symm y.1
  let t := conditionEquiv.symm y.2
  obtain ⟨u,v,hu,hv,hreq⟩ := CommonIdeal.requirement_dense A p q s.word t.word
  let u' := conditionEquiv ⟨u⟩
  let v' := conditionEquiv ⟨v⟩
  have hu' : u' ≤ y.1 := by
    simpa only [s,OrderIso.apply_symm_apply] using conditionEquiv.monotone hu
  have hv' : v' ≤ y.2 := by
    simpa only [t,OrderIso.apply_symm_apply] using conditionEquiv.monotone hv
  refine ⟨I (u',v'),?_,?_⟩
  · simpa only [y,OrderIso.apply_symm_apply] using I.monotone (show (u',v') ≤ y from ⟨hu',hv'⟩)
  · change label c (productMap conditions conditions c hcs (u',v')) ∈ denseSet c A p q
    rw [label_productMap]
    change code (label conditions (encodeCondition ⟨u⟩))
      (label conditions (encodeCondition ⟨v⟩)) ∈ denseSet c A p q
    rw [label_encodeCondition,label_encodeCondition,denseSet_spec c hcs]
    exact hreq

end TuringRigidity.InternalCommonRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_IteratedGenericCommonIdeal
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.IteratedGenericCommonIdeal
open TransitiveNameModel BoundedSetTheory InternalCohen CountableForcing AtomicForcing
open CohenProductSplitting CohenBorelForcing InternalCommonRequirements
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem meets_requirements (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ modelReals M) (L R : Oracle)
    (hL : GroundGeneric M (pushFilter (realFilter L)))
    (hR : GroundGeneric (genericExtensionSet M conditions (pushFilter (realFilter L)).carrier)
      (pushFilter (realFilter R))) :
    ∀ p q : OracleCode, ∃ s t : List Bool,
      CommonIdeal.Extends L s ∧ CommonIdeal.Extends R t ∧ CommonIdeal.Requirement A p q s t := by
  have hcnd := conditions_mem M hM hT
  obtain ⟨c,hc,hcs,_⟩ := TaggedProductConditions.internal_product M conditions conditions hM hT hcnd hcnd
  let J := pushFilter (realFilter L)
  let H := pushFilter (realFilter R)
  have hJoint := TaggedProductGeneric.joint_ground_generic M conditions conditions c
    hM hT hcnd hcnd hcs J hL H hR
  intro p q
  obtain ⟨x,hx,hxD⟩ := hJoint (denseSet c A p q)
    (denseSet_mem M c hM hT hc A hA p q) (denseSet_dense c hcs A p q)
  let I := productIso conditions conditions c hcs
  let uv := I.symm x
  have hx' : productMap conditions conditions c hcs uv ∈
      (TaggedProductGeneric.joint conditions conditions c hcs J H).carrier := by
    change I uv ∈ _
    simpa only [uv,OrderIso.apply_symm_apply] using hx
  have huv := (TaggedProductGeneric.joint_mem conditions conditions c hcs J H uv.1 uv.2).mp hx'
  let s := conditionEquiv.symm uv.1
  let t := conditionEquiv.symm uv.2
  have hs : CommonIdeal.Extends L s.word := fun i hi => (huv.1 i hi).symm
  have ht : CommonIdeal.Extends R t.word := fun i hi => (huv.2 i hi).symm
  have hlabel (r : Conditions conditions) :
      label conditions r = wordCode (conditionEquiv.symm r).word := by
    rw [←label_encodeCondition]
    exact congrArg (label conditions) (conditionEquiv.apply_symm_apply r).symm
  have hxD' : label c (I uv) ∈ denseSet c A p q := by
    simpa only [uv,OrderIso.apply_symm_apply] using hxD
  change label c (productMap conditions conditions c hcs uv) ∈ denseSet c A p q at hxD'
  rw [label_productMap,hlabel,hlabel,denseSet_spec c hcs] at hxD'
  exact ⟨s.word,t.word,hs,ht,hxD'⟩

theorem ideal_of_iterated_generics_oai (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : A ∈ modelReals M) (L R : Oracle)
    (hL : GroundGeneric M (pushFilter (realFilter L)))
    (hR : GroundGeneric (genericExtensionSet M conditions (pushFilter (realFilter L)).carrier)
      (pushFilter (realFilter R))) :
    ∀ b : Degree, b ≤ degree A ↔ b ≤ degree (join A L) ∧ b ≤ degree (join A R) :=
  CommonIdeal.ideal_of_meets A L R (meets_requirements M hM hT A hA L R hL hR)

end TuringRigidity.IteratedGenericCommonIdeal

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.IteratedGenericCommonIdeal.ideal_of_iterated_generics_oai := @OAI.TuringRigidity.IteratedGenericCommonIdeal.ideal_of_iterated_generics_oai
