-- Prove2me | solution 1 for OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:53:53.444479+00:00
-- url     : https://prove2.me/submissions/ec0ade48-0d54-41af-a0ad-520f8b1f7db7

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_ArithmeticTree_native_nonidentity_absolute
import Theorems.Thm_OAI_TuringRigidity_ArithmeticTree_native_persistence_absolute

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CountableGroundGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.AtomicForcing
open TransitiveNameModel BoundedSetTheory CountableForcing
universe u

theorem countable_ground_generic (M : ZFSet.{u}) [Countable (Conditions M)]
    (hne : ∃ x, x ∈ M) {c : ZFSet.{u}} [Preorder (Conditions c)] (p : Conditions c) :
    ∃ G : GenericFilter (Conditions c), p ∈ G.carrier ∧ GroundGeneric M G := by
  classical
  obtain ⟨x,hx⟩ := hne
  obtain ⟨m,_⟩ := label_surjective M hx
  let _ : Nonempty (Conditions M) := ⟨m⟩
  obtain ⟨e,he⟩ := exists_surjective_nat (Conditions M)
  let D : ℕ → Set (Conditions c) := fun n =>
    if Dense {q : Conditions c | label c q ∈ label M (e n)} then
      {q | label c q ∈ label M (e n)} else Set.univ
  have hD : ∀ n, Dense (D n) := by
    intro n
    dsimp only [D]
    split
    · assumption
    · exact fun q => ⟨q,le_rfl,Set.mem_univ _⟩
  obtain ⟨G,hp,hG⟩ := exists_generic D hD p
  refine ⟨G,hp,?_⟩
  intro E hEM hE
  obtain ⟨m,hm⟩ := label_surjective M hEM
  obtain ⟨n,rfl⟩ := he m
  have hd : Dense {q : Conditions c | label c q ∈ label M (e n)} := by
    rw [hm]; exact hE
  obtain ⟨q,hq,hqn⟩ := hG n
  refine ⟨q,hq,?_⟩
  simpa only [D,ite_eq_left hd,Set.mem_ofPred_eq,hm] using hqn

end TuringRigidity.AtomicForcing

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCollapseConditions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel
universe u

theorem mem_append (p : ZFSet.{u}) (n : ℕ) (x z : ZFSet.{u}) :
    z ∈ append p n x ↔ z ∈ p ∨ z = ZFSet.pair (natSet n) x := by
  simp only [append,ZFSet.mem_union,ZFSet.mem_singleton]

theorem append_function {A p x : ZFSet.{u}} {n : ℕ}
    (hp : TransitiveNameModel.FunctionGraph (natSet n) A p) (hx : x ∈ A) :
    TransitiveNameModel.FunctionGraph (natSet (n+1)) A (append p n x) := by
  have hold {i y : ZFSet.{u}} (h : ZFSet.pair i y ∈ p) : i ∈ natSet n := by
    obtain ⟨j,hj,z,_,he⟩ := hp.1 _ h
    obtain ⟨rfl,_⟩ := ZFSet.pair_inj.mp he
    exact hj
  constructor
  · intro z hz
    rcases (mem_append p n x z).mp hz with hz|rfl
    · obtain ⟨i,hi,y,hy,rfl⟩ := hp.1 z hz
      exact ⟨i,ZFSet.mem_insert_iff.mpr (Or.inr hi),y,hy,rfl⟩
    · exact ⟨natSet n,ZFSet.mem_insert_iff.mpr (Or.inl rfl),x,hx,rfl⟩
  · intro i hi
    change i ∈ insert (natSet n) (natSet n) at hi
    rcases ZFSet.mem_insert_iff.mp hi with rfl|hi
    · refine ⟨x,hx,(mem_append _ _ _ _).mpr (Or.inr rfl),?_⟩
      intro y _ hy
      rcases (mem_append _ _ _ _).mp hy with hy|hy
      · exact False.elim ((Nat.lt_irrefl n) ((natSet_mem_natSet n n).mp (hold hy)))
      · exact (ZFSet.pair_inj.mp hy).2
    · obtain ⟨y,hy,hiy,hunique⟩ := hp.2 i hi
      refine ⟨y,hy,(mem_append _ _ _ _).mpr (Or.inl hiy),?_⟩
      intro z hz hiz
      rcases (mem_append _ _ _ _).mp hiz with hiz|hiz
      · exact hunique z hz hiz
      · have he := (ZFSet.pair_inj.mp hiz).1
        rw [he] at hi
        exact False.elim ((Nat.lt_irrefl n) ((natSet_mem_natSet n n).mp hi))

theorem append_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {p x : ZFSet.{u}} (hp : p ∈ M) (hx : x ∈ M) (n : ℕ) : append p n x ∈ M :=
  binary_union_mem M hM hT.pairing hT.union hp
    (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing
      (hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)) hx))

theorem conditions_exist (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : ZFSet.{u}} (hA : A ∈ M) :
    ∃ c ∈ M, ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hA)
  let e := cons ZFSet.omega (fun _ => A)
  have he : ∀ i, e i ∈ M := by intro i; cases i <;> assumption
  let c := ZFSet.sep (fun p => (prefixFormula 1 2 0).Eval (cons p e)) Q
  refine ⟨c,sep_mem M hM hS _ e he hQM,fun p => ?_⟩
  rw [ZFSet.mem_sep,eval_prefixFormula 1 2 0 (cons p e) rfl,hQ]
  exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,prefix_subset h.2⟩,h.2⟩⟩

attribute [local instance] order

attribute [local instance] collapsePreorder

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCollapseDense
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

theorem extend_length (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A p : ZFSet.{u}} (hA : A ∈ M) (hpM : p ∈ M) (hp : Prefix A p)
    (hne : ∃ x, x ∈ A) (m : ℕ) :
    ∃ q ∈ M, ∃ k : ℕ, m ≤ k ∧ TransitiveNameModel.FunctionGraph (natSet k) A q ∧ p ⊆ q := by
  obtain ⟨x,hx⟩ := hne
  induction m with
  | zero =>
    obtain ⟨k,hk⟩ := hp
    exact ⟨p,hpM,k,Nat.zero_le _,hk,fun _ h => h⟩
  | succ m ih =>
    obtain ⟨q,hqM,k,hk,hq,hpq⟩ := ih
    by_cases hmk : m+1 ≤ k
    · exact ⟨q,hqM,k,hmk,hq,hpq⟩
    · refine ⟨append q k x,append_mem M hM hT hqM (hM _ hA _ hx) k,k+1,by omega,
        append_function hq hx,fun z hz => ?_⟩
      exact (mem_append _ _ _ _).mpr (Or.inl (hpq hz))

theorem covers_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c x : ZFSet.{u}} (hc : c ∈ M) (hx : x ∈ M) : covers c x ∈ M := by
  let e := cons ZFSet.omega (fun _ => x)
  have he : ∀ i, e i ∈ M := by intro i; cases i <;> first | exact sourceT_omega_mem M hM hT | exact hx
  simpa only [covers,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 3 1)) e he hc

theorem definedAt_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c A : ZFSet.{u}} (hc : c ∈ M) (hA : A ∈ M) (n : ℕ) : definedAt c A n ∈ M := by
  let e := cons A (fun _ => natSet.{u} n)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i
    · exact hA
    · exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨n,rfl⟩)
  simpa only [definedAt,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 3 0 1)) e he hc

theorem covers_dense (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p)
    {x : ZFSet.{u}} (hx : x ∈ A) : Dense {p : Conditions c | label c p ∈ covers c x} := by
  intro p
  obtain ⟨hpM,n,hp⟩ := (hc _).mp (label_mem c p)
  let q := append (label c p) n x
  have hq : q ∈ c := (hc q).mpr ⟨append_mem M hM hT hpM (hM _ hA _ hx) n,n+1,append_function hp hx⟩
  obtain ⟨r,hr⟩ := label_surjective c hq
  refine ⟨r,?_,?_⟩
  · change label c p ⊆ label c r
    rw [hr]
    exact fun z hz => (mem_append _ _ _ _).mpr (Or.inl hz)
  · change label c r ∈ covers c x
    rw [hr,covers,ZFSet.mem_sep]
    exact ⟨hq,natSet n,(mem_omega _).mpr ⟨n,rfl⟩,(mem_append _ _ _ _).mpr (Or.inr rfl)⟩

theorem definedAt_dense (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p)
    (hne : ∃ x, x ∈ A) (n : ℕ) : Dense {p : Conditions c | label c p ∈ definedAt c A n} := by
  intro p
  obtain ⟨hpM,hp⟩ := (hc _).mp (label_mem c p)
  obtain ⟨q,hqM,k,hnk,hq,hpq⟩ := extend_length M hM hT hA hpM hp hne (n+1)
  have hqc : q ∈ c := (hc q).mpr ⟨hqM,k,hq⟩
  obtain ⟨r,hr⟩ := label_surjective c hqc
  obtain ⟨x,hx,hnx,_⟩ := hq.2 (natSet n) ((natSet_mem_natSet n k).mpr (by omega))
  refine ⟨r,?_,?_⟩
  · change label c p ⊆ label c r
    rw [hr]; exact hpq
  · change label c r ∈ definedAt c A n
    rw [hr,definedAt,ZFSet.mem_sep]
    exact ⟨hqc,x,hx,hnx⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCollapseCounting
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel CountableForcing
universe u
attribute [local instance] order collapsePreorder

theorem mem_unionGraph {c : ZFSet.{u}} (G : GenericFilter (Conditions c)) (z : ZFSet.{u}) :
    z ∈ unionGraph G ↔ ∃ p ∈ G.carrier, z ∈ label c p := by
  rw [unionGraph,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨p,hp,hz⟩
    obtain ⟨q,hq,rfl⟩ := (mem_genericFilterSet c G.carrier p).mp hp
    exact ⟨q,hq,hz⟩
  · rintro ⟨p,hp,hz⟩
    exact ⟨label c p,(mem_genericFilterSet c G.carrier _).mpr ⟨p,hp,rfl⟩,hz⟩

theorem unionGraph_functional {A c : ZFSet.{u}}
    (hc : ∀ p ∈ c, Prefix A p) (G : GenericFilter (Conditions c))
    {i x y : ZFSet.{u}} (hx : ZFSet.pair i x ∈ unionGraph G)
    (hy : ZFSet.pair i y ∈ unionGraph G) : x = y := by
  obtain ⟨p,hp,hpx⟩ := (mem_unionGraph G _).mp hx
  obtain ⟨q,hq,hqy⟩ := (mem_unionGraph G _).mp hy
  obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
  obtain ⟨k,hr⟩ := hc _ (label_mem c r)
  have hid : i ∈ natSet k := by
    obtain ⟨j,hj,z,_,he⟩ := hr.1 _ (hrp hpx)
    obtain ⟨rfl,_⟩ := ZFSet.pair_inj.mp he
    exact hj
  exact hr.functional hid (hrp hpx) (hrq hqy)

theorem unionGraph_total (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) (hne : ∃ x, x ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (n : ℕ) :
    ∃ x ∈ A, ZFSet.pair (natSet n) x ∈ unionGraph G := by
  obtain ⟨p,hp,hpn⟩ := hG (definedAt c A n) (definedAt_mem M hM hT hcM hA n)
    (definedAt_dense M hM hT hA hc hne n)
  obtain ⟨_,x,hx,hnx⟩ := ZFSet.mem_sep.mp hpn
  exact ⟨x,hx,(mem_unionGraph G _).mpr ⟨p,hp,hnx⟩⟩

theorem unionGraph_onto (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    ∀ x ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n x ∈ unionGraph G := by
  intro x hx
  obtain ⟨p,hp,hpx⟩ := hG (covers c x) (covers_mem M hM hT hcM (hM _ hA _ hx))
    (covers_dense M hM hT hA hc hx)
  obtain ⟨_,n,hn,hnx⟩ := ZFSet.mem_sep.mp hpx
  exact ⟨n,hn,(mem_unionGraph G _).mpr ⟨p,hp,hnx⟩⟩

theorem unionGraph_function (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) (hne : ∃ x, x ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    TransitiveNameModel.FunctionGraph ZFSet.omega A (unionGraph G) := by
  have hcP : ∀ p ∈ c, Prefix A p := fun p hp => ((hc p).mp hp).2
  constructor
  · intro z hz
    obtain ⟨p,_,hzp⟩ := (mem_unionGraph G z).mp hz
    exact ZFSet.mem_prod.mp (prefix_subset (hcP _ (label_mem c p)) hzp)
  · intro i hi
    obtain ⟨n,rfl⟩ := (mem_omega i).mp hi
    obtain ⟨x,hx,hnx⟩ := unionGraph_total M hM hT hA hcM hc hne G hG n
    exact ⟨x,hx,hnx,fun y _ hny => unionGraph_functional hcP G hny hnx⟩

theorem unionGraph_mem_extension (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c : ZFSet.{u}} (hcM : c ∈ M) (h0 : (∅ : ZFSet.{u}) ∈ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M c G.carrier := by
  let _ := top c h0
  have htop : ⊤ ∈ G.carrier := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact G.upper le_top hp
  have hE := extension_sourceT M hM hT hcM (orderSet_mem M hM hT hcM) (orderSet_pair c) G hG htop
  apply union_mem _ (genericExtensionSet_transitive M c hM G.carrier) hE.union
  exact genericFilterSet_mem_extension M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hcM G.carrier htop

theorem internal_counting (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A c : ZFSet.{u}} (hA : A ∈ M) (hcM : c ∈ M)
    (hc : ∀ p, p ∈ c ↔ p ∈ M ∧ Prefix A p) (hne : ∃ x, x ∈ A)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    InternallyCountable (genericExtensionSet M c G.carrier) A := by
  have h0 : (∅ : ZFSet.{u}) ∈ c :=
    (hc ∅).mpr ⟨hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero,prefix_empty A⟩
  exact ⟨unionGraph G,unionGraph_mem_extension M hM hT hcM h0 G hG,
    unionGraph_function M hM hT hA hcM hc hne G hG,unionGraph_onto M hM hT hA hcM hc G hG⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetPresentationDecoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetPresentationDecoding
open BoundedSetTheory TransitiveNameModel
universe u

theorem class_mem (M : ZFSet.{u}) (hM : Transitive M) (hS : Separation M)
    {d E x : ZFSet.{u}} (hd : d ∈ M) (hE : E ∈ M) (hx : x ∈ M) :
    classSet d E x ∈ M := by
  let e := cons x (cons E (fun _ => d))
  have he : ∀ i, e i ∈ M := by intro i; cases i with
    | zero => exact hx
    | succ i => cases i <;> simp [e,hd,hE]
  simpa only [Formula.eval_pairMem,e,cons_zero,cons_succ,classSet] using
    sep_mem M hM hS (.pairMem 1 0 2) e he hd

theorem quotient_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hPow : PowerSet M) (hS : Separation M)
    {d E a : ZFSet.{u}} (hd : d ∈ M) (hE : E ∈ M) (ha : a ∈ M) :
    quotientSet d E a ∈ M := by
  obtain ⟨p,hp,hpdef⟩ := internal_power M hM hPow hd
  let e := cons a (cons d (fun _ => E))
  have he : ∀ i, e i ∈ M := by intro i; cases i with
    | zero => exact ha
    | succ i => cases i <;> simp [e,hd,hE]
  let φ : Formula := .existsMem 1 (classFormula 1 0 3 4)
  have h := sep_mem M hM hS φ e he hp
  have eq : ZFSet.sep (fun c => φ.Eval (cons c e)) p = quotientSet d E a := by
    apply ZFSet.ext
    intro c
    simp only [ZFSet.mem_sep,φ,Formula.Eval,eval_classFormula,cons_zero,cons_succ,e,
      mem_quotientSet]
    constructor
    · exact And.right
    · rintro ⟨x,hx,rfl⟩
      refine ⟨(hpdef _).mpr ⟨class_mem M hM hS hd hE (hM a ha x hx),?_⟩,⟨x,hx,rfl⟩⟩
      intro y hy
      exact (mem_classSet _ _ _ _).mp hy |>.1
  exact eq ▸ h

theorem eval_actionFormula (z a d E R q : ZFSet.{u}) :
    actionFormula.Eval (cons z (cons a (cons d (cons E (cons R (fun _ => q)))))) ↔
    ∃ x ∈ a, ∃ y ∈ a, ZFSet.pair x y ∈ R ∧
      ∃ c ∈ q, ∃ b ∈ q, c = classSet d E x ∧ b = classSet d E y ∧ z = ZFSet.pair c b := by
  simp only [actionFormula,Formula.Eval,Formula.eval_pairMem,eval_classFormula,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem action_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    {d E a R : ZFSet.{u}} (hd : d ∈ M) (hE : E ∈ M) (ha : a ∈ M) (hR : R ∈ M) :
    actionGraph d E a R ∈ M := by
  let q := quotientSet d E a
  have hq := quotient_mem M hM hPow hS hd hE ha
  have hprod := product_mem M hM hP hU hPow hS hq hq
  let e := cons a (cons d (cons E (cons R (fun _ => q))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp [e,ha,hd,hE,hR,q,hq]
  have h := sep_mem M hM hS actionFormula e he hprod
  have eq : ZFSet.sep (fun z => actionFormula.Eval (cons z e)) (ZFSet.prod q q) =
      actionGraph d E a R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,mem_actionGraph,show actionFormula.Eval (cons z e) ↔ _ from
      eval_actionFormula z a d E R q]
    constructor
    · rintro ⟨_,x,hx,y,hy,hR,c,hc,b,hb,rfl,rfl,hz⟩
      exact ⟨x,hx,y,hy,hR,hz⟩
    · intro h
      obtain ⟨x,hx,y,hy,hxy,rfl⟩ := h
      have hxq : classSet d E x ∈ q := (mem_quotientSet _ _ _ _).mpr ⟨x,hx,rfl⟩
      have hyq : classSet d E y ∈ q := (mem_quotientSet _ _ _ _).mpr ⟨y,hy,rfl⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hxq,hyq⟩,
        ⟨x,hx,y,hy,hxy,_,hxq,_,hyq,rfl,rfl,rfl⟩⟩
  exact eq ▸ h

end TuringRigidity.SetPresentationDecoding

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

theorem internal_reals (M : ZFSet.{u}) (hM : Transitive M)
    (hPow : PowerSet M) (hS : Separation M) (hI : Infinity M) :
    ∃ r ∈ M, ∀ x, x ∈ r ↔ ∃ A ∈ reals M, x = realSet A := by
  obtain ⟨r,hr,hrdef⟩ := internal_power M hM hPow (omega_mem M hM hS hI)
  refine ⟨r,hr,fun x => ?_⟩
  rw [hrdef]
  constructor
  · rintro ⟨hxM,hx⟩
    exact ⟨oracleOf x,by simpa only [reals,Set.mem_ofPred_eq,realSet_oracleOf hx] using hxM,
      (realSet_oracleOf hx).symm⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨hA,realSet_subset A⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
universe u
noncomputable section

theorem parity_ext {α : Sort*} {f g : ℕ → α} (he : ∀ n, f (2*n) = g (2*n))
    (ho : ∀ n, f (2*n+1) = g (2*n+1)) : f = g := by
  funext n
  have hm : n%2 < 2 := Nat.mod_lt n (by decide)
  by_cases h : n%2=0
  · have hn : n=2*(n/2) := by omega
    rw [hn]
    exact he _
  · have hn : n=2*(n/2)+1 := by omega
    rw [hn]
    exact ho _

@[simp] theorem mix_slotMap (e d : ℕ → ZFSet.{u}) (r s : ℕ → ℕ) :
    mix e d ∘ slotMap r s = mix (e ∘ r) (d ∘ s) := by
  apply parity_ext <;> intro n <;> simp

variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem Definable.congr (h : Definable M P) (he : ∀ e, P e ↔ Q e) : Definable M Q := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨p,d,hd,fun e => (hp e).trans (he e)⟩

theorem Definable.subst (h : Definable M P) (r : ℕ → ℕ) :
    Definable M (fun e => P (e ∘ r)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨p.rename (slotMap r id),d,hd,?_⟩
  intro e
  simpa only [Formula.eval_rename_comp,mix_slotMap,Function.comp_id] using hp (e ∘ r)

theorem Definable.neg (h : Definable M P) : Definable M (fun e => ¬ P e) := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨.neg p,d,hd,fun e => not_congr (hp e)⟩

theorem Definable.and (hP : Definable M P) (hQ : Definable M Q) :
    Definable M (fun e => P e ∧ Q e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.conj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i
    unfold mix
    split <;> first | exact hd _ | exact hc _
  · intro e
    simp only [Formula.Eval,Formula.eval_rename_comp,mix_slotMap,Function.comp_id]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    rw [hd',hc',hp,hq]

theorem bind_mix (x : ZFSet.{u}) (e d : ℕ → ZFSet.{u}) :
    cons x (mix e d) ∘ bindSlots = mix (cons x e) d := by
  apply parity_ext
  · intro n
    cases n with
    | zero => rfl
    | succ n => simp
  · intro n
    simp [show 2*n+2 = (2*n+1)+1 from by omega]

theorem Definable.existsParam (h : Definable M P) {a : ZFSet.{u}} (ha : a ∈ M) :
    Definable M (fun e => ∃ x ∈ a, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  let r := slotMap id Nat.succ
  refine ⟨.existsMem 1 ((p.rename r).rename bindSlots),cons a d,?_,?_⟩
  · intro i
    cases i with
    | zero => exact ha
    | succ i => exact hd i
  · intro e
    have hd' : cons a d ∘ Nat.succ = d := rfl
    simp only [r,Formula.Eval,Formula.eval_rename_comp,bind_mix,mix_slotMap,Function.comp_id,hd',hp,
      show mix e (cons a d) 1 = a from rfl]

theorem member_definable (C : Context M) (i j : ℕ) : Definable M (fun e => e i ∈ e j) :=
  ⟨.member (2*i) (2*j),fun _ => ZFSet.omega,fun _ => C.omega_mem,fun e => by simp [Formula.Eval]⟩

theorem equal_param {a : ZFSet.{u}} (ha : a ∈ M) (i : ℕ) :
    Definable M (fun e => e i = a) :=
  ⟨.equal (2*i) 1,fun _ => a,fun _ => ha,fun e => by simp [Formula.Eval,mix]⟩

theorem pairMem_param {a : ZFSet.{u}} (ha : a ∈ M) (i j : ℕ) :
    Definable M (fun e => ZFSet.pair (e i) (e j) ∈ a) :=
  ⟨.pairMem (2*i) (2*j) 1,fun _ => a,fun _ => ha,fun e => by simp [mix]⟩

theorem Definable.sep_mem (C : Context M) (h : Definable M P) (e : ℕ → ZFSet.{u})
    (he : ∀ i, e i ∈ M) {a : ZFSet.{u}} (ha : a ∈ M) :
    ZFSet.sep (fun x => P (cons x e)) a ∈ M := by
  obtain ⟨p,d,hd,hp⟩ := h
  let q := p.rename bindSlots
  have hm : ∀ i, mix e d i ∈ M := by
    intro i
    unfold mix
    split <;> first | exact he _ | exact hd _
  have hs := BoundedSetTheory.sep_mem M C.transitive C.separation q (mix e d) hm ha
  have hh : ZFSet.sep (fun x => q.Eval (cons x (mix e d))) a =
      ZFSet.sep (fun x => P (cons x e)) a := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_sep,q,Formula.eval_rename_comp,bind_mix,hp]
  exact hh ▸ hs

end
end TuringRigidity.BoundedDefinability

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

theorem pairCode_definable (C : Context M) (i j k : ℕ) :
    Definable M (fun e => PairCode (e i) (e j) (e k)) := by
  refine ⟨tripleFormula (2*i) (2*j) (2*k) 1 3,
    cons pairingSet (fun _ => pairNumbers),?_,?_⟩
  · intro n
    cases n with
    | zero => exact C.pairing_mem
    | succ n => exact C.pairNumbers_mem
  · intro e
    simp only [eval_tripleFormula,mix_even,PairCode]
    rfl

@[simp] theorem pairCode_nat (i j k : ℕ) :
    PairCode (natSet.{u} i) (natSet j) (natSet k) ↔ k = Nat.pair i j := by
  simp only [PairCode,natPair_mem,true_and,pairing_code]

theorem pure_definition (C : Context M) (P : ℕ → Prop) (hP : PrimrecPred P) :
    ArithmeticDefinition M (fun _ n => P n) := by
  obtain ⟨d,hd⟩ := hP
  let : DecidablePred P := d
  obtain ⟨g,hg,hgc⟩ := primrec_graph C (Primrec.encode.comp hd)
  let Q := fun e : ℕ → ZFSet.{u} => ∃ x ∈ ZFSet.omega,
    x = natSet 1 ∧ ZFSet.pair (e 0) x ∈ g
  have hQ : Definable M Q :=
    ((equal_param (C.nat_mem 1) 0).and (pairMem_param hg 1 0)).existsParam C.omega_mem
  refine ⟨Q,hQ,?_⟩
  intro e n hn
  simp only [Q,hn,omega_exists]
  constructor
  · rintro ⟨k,hk,hgk⟩
    have hk' : k=1 := natSet_injective hk
    have hh := (hgc n k).mp hgk
    rw [hk'] at hh
    by_contra h
    simp [h] at hh
  · intro h
    exact ⟨1,rfl,(hgc n 1).mpr (by simp [h])⟩

theorem query_definition (C : Context M) (i : ℕ) :
    ArithmeticDefinition M (fun O n => O i n = true) := by
  refine ⟨fun e => e 0 ∈ e (i+1),member_definable C 0 (i+1),?_⟩
  intro e n hn
  simp [hn,oracleOf]

theorem ArithmeticDefinition.neg {P : Predicate} (h : ArithmeticDefinition M P) :
    ArithmeticDefinition M (fun O n => ¬ P O n) := by
  obtain ⟨Q,hQ,hc⟩ := h
  exact ⟨fun e => ¬ Q e,hQ.neg,fun e n hn => not_congr (hc e n hn)⟩

theorem ArithmeticDefinition.and {P R : Predicate}
    (hP : ArithmeticDefinition M P) (hR : ArithmeticDefinition M R) :
    ArithmeticDefinition M (fun O n => P O n ∧ R O n) := by
  obtain ⟨Q,hQ,hc⟩ := hP
  obtain ⟨S,hS,hs⟩ := hR
  exact ⟨fun e => Q e ∧ S e,hQ.and hS,fun e n hn => and_congr (hc e n hn) (hs e n hn)⟩

theorem ArithmeticDefinition.comp (C : Context M) {P : Predicate}
    (h : ArithmeticDefinition M P) {f : ℕ → ℕ} (hf : Primrec f) :
    ArithmeticDefinition M (fun O n => P O (f n)) := by
  obtain ⟨Q,hQ,hc⟩ := h
  obtain ⟨g,hg,hgc⟩ := primrec_graph C hf
  let R := fun e : ℕ → ZFSet.{u} => ∃ x ∈ ZFSet.omega,
    ZFSet.pair (e 0) x ∈ g ∧ Q (cons x e ∘ skipInput 1)
  have hR : Definable M R :=
    ((pairMem_param hg 1 0).and (hQ.subst (skipInput 1))).existsParam C.omega_mem
  refine ⟨R,hR,?_⟩
  intro e n hn
  simp only [R,omega_exists,hn,hgc]
  constructor
  · rintro ⟨k,rfl,hk⟩
    exact (hc (cons (natSet (f n)) e ∘ skipInput 1) (f n) rfl).mp hk
  · intro hh
    exact ⟨f n,rfl,(hc (cons (natSet (f n)) e ∘ skipInput 1) (f n) rfl).mpr hh⟩

theorem ArithmeticDefinition.ex (C : Context M) {P : Predicate}
    (h : ArithmeticDefinition M P) :
    ArithmeticDefinition M (fun O n => ∃ k, P O (Nat.pair n k)) := by
  obtain ⟨Q,hQ,hc⟩ := h
  let R := fun e : ℕ → ZFSet.{u} => ∃ x ∈ ZFSet.omega, ∃ y ∈ ZFSet.omega,
    PairCode (e 0) x y ∧ Q (cons y (cons x e) ∘ skipInput 2)
  have hR : Definable M R :=
    (((pairCode_definable C 2 1 0).and (hQ.subst (skipInput 2))).existsParam
      C.omega_mem).existsParam C.omega_mem
  refine ⟨R,hR,?_⟩
  intro e n hn
  simp only [R,hn]
  simp_rw [omega_exists]
  simp only [pairCode_nat]
  constructor
  · rintro ⟨k,l,rfl,hl⟩
    exact ⟨k,(hc (cons (natSet (Nat.pair n k)) (cons (natSet k) e) ∘ skipInput 2) (Nat.pair n k) rfl).mp hl⟩
  · rintro ⟨k,hk⟩
    exact ⟨k,Nat.pair n k,rfl,(hc (cons (natSet (Nat.pair n k)) (cons (natSet k) e) ∘ skipInput 2) (Nat.pair n k) rfl).mpr hk⟩

theorem arith_definition (C : Context M) {P : Predicate} (h : Arith P) :
    ArithmeticDefinition M P := by
  induction h with
  | pure P hP => exact pure_definition C P hP
  | query i => exact query_definition C i
  | neg h ih => exact ih.neg
  | and h k ih ik => exact ih.and ik
  | ex h ih => exact ih.ex C
  | comp f h hf ih => exact ih.comp C hf

end
end TuringRigidity.SetModelSyntax

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelArithmeticClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable TableIndices IndexMatrix
universe u
noncomputable section

variable {M : ZFSet.{u}}

theorem arithmetic_comprehension (C : Context M) {P : Predicate} (hP : Arith P)
    (O : Oracles) (hO : ∀ i, O i ∈ reals M) (A : Oracle)
    (hA : ∀ n, P O n ↔ A n = true) : A ∈ reals M := by
  obtain ⟨Q,hQ,hc⟩ := arith_definition C hP
  let e : ℕ → ZFSet.{u} := fun i => realSet (O i)
  have he : ∀ i, e i ∈ M := hO
  have hs := hQ.sep_mem C e he C.omega_mem
  have hspec (n : ℕ) : Q (cons (natSet n) e) ↔ A n = true := by
    have hh := hc (cons (natSet n) e) n rfl
    have ho : (fun i => oracleOf (cons (natSet n) e (i+1))) = O := by
      funext i
      exact oracleOf_realSet (O i)
    rw [ho] at hh
    exact hh.trans (hA n)
  have eq : ZFSet.sep (fun x => Q (cons x e)) ZFSet.omega = realSet A := by
    apply ZFSet.ext
    intro x
    by_cases hx : x ∈ ZFSet.omega
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      simp only [ZFSet.mem_sep,hspec,nat_mem_realSet]
      exact and_iff_right ((mem_omega _).mpr ⟨n,rfl⟩)
    · constructor
      · intro h
        exact (hx (ZFSet.mem_sep.mp h).1).elim
      · intro h
        exact (hx (realSet_subset A h)).elim
  change realSet A ∈ M
  exact eq ▸ hs

theorem tableOracle_mem (C : Context M) {B : Oracle} (hB : B ∈ reals M) (e : ℕ) :
    tableOracle B e ∈ reals M := by
  have h : Arith (fun O v => tableGraph (O 0) e v) :=
    tableGraph_arith (parameter_arith 0) (Primrec.const 0) (Primrec.const e) Primrec.id
  apply arithmetic_comprehension C h (fun _ => B) (fun _ => hB) (tableOracle B e)
  intro n
  simp [tableOracle]

theorem lower_mem (C : Context M) {A B : Oracle} (hB : B ∈ reals M) (hAB : Reduces A B) :
    A ∈ reals M := by
  obtain ⟨c,hc⟩ := (reduces_iff_represents A B).mp hAB
  have hc' : Represents B (machine (encode c)) A := by simpa using hc
  rw [←tableOracle_eq hc']
  exact tableOracle_mem C hB (encode c)

end
end TuringRigidity.SetModelSyntax

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

theorem class_eq_degreeSet (M : ZFSet.{u})
    (hLower : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    {d E : ZFSet.{u}} (hd : ∀ x, x ∈ d ↔ ∃ A ∈ reals M, x = realSet A)
    (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {A : Oracle} (hA : A ∈ reals M) :
    classSet d E (realSet A) = degreeSet (degree A) := by
  apply ZFSet.ext
  intro x
  rw [mem_classSet,mem_degreeSet]
  constructor
  · rintro ⟨hx,hAx⟩
    obtain ⟨B,hB,rfl⟩ := (hd x).mp hx
    exact ⟨B,rfl,((hE A hA B hB).mp hAx).symm⟩
  · rintro ⟨B,rfl,hBA⟩
    have hB : B ∈ reals M := hLower hA ((degree_eq_iff B A).mp hBA).1
    exact ⟨(hd _).mpr ⟨B,hB,rfl⟩,(hE A hA B hB).mpr hBA.symm⟩

end
end TuringRigidity.SetDegreeDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelInternalRelations
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
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

theorem orderedPair_definable (C : Context M) (i j k : ℕ) :
    Definable M (fun e => e i = ZFSet.pair (e j) (e k)) :=
  ⟨.orderedPair (2*i) (2*j) (2*k),fun _ => ZFSet.omega,
    fun _ => C.omega_mem,fun e => by simp⟩

theorem binary_definition (C : Context M) (R : Oracle → Oracle → Prop)
    (hR : Arith (fun O _ => R (O 0) (O 1))) :
    Definable M (fun e => R (oracleOf (e 0)) (oracleOf (e 1))) := by
  obtain ⟨Q,hQ,hc⟩ := arith_definition C hR
  apply (hQ.existsParam C.omega_mem).congr
  intro e
  rw [omega_exists]
  constructor
  · rintro ⟨n,hn⟩
    exact (hc (cons (natSet n) e) n rfl).mp hn
  · intro h
    exact ⟨0,(hc (cons (natSet 0) e) 0 rfl).mpr h⟩

theorem internal_binary_relation (C : Context M) (R : Oracle → Oracle → Prop)
    (hR : Arith (fun O _ => R (O 0) (O 1))) :
    ∃ g ∈ M, ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ R A B := by
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  have hd := binary_definition C R hR
  let S := fun e : ℕ → ZFSet.{u} => ∃ x ∈ r, ∃ y ∈ r,
    e 0 = ZFSet.pair x y ∧ R (oracleOf x) (oracleOf y)
  have hS : Definable M S := by
    have h := ((orderedPair_definable C 2 1 0).and
      (hd.subst (fun i => if i=0 then 1 else 0))).existsParam hr
    exact h.existsParam hr
  let g := ZFSet.sep (fun z => S (cons z (fun _ => ZFSet.omega))) (ZFSet.prod r r)
  refine ⟨g,hS.sep_mem C (fun _ => ZFSet.omega) (fun _ => C.omega_mem) (C.prod_mem hr hr),?_⟩
  intro A hA B hB
  have ha : realSet A ∈ r := (hrc _).mpr ⟨A,hA,rfl⟩
  have hb : realSet B ∈ r := (hrc _).mpr ⟨B,hB,rfl⟩
  simp only [g,ZFSet.mem_sep,ZFSet.pair_mem_prod,ha,hb,true_and,S,cons_zero]
  constructor
  · rintro ⟨x,hx,y,hy,hxy,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxy
    simpa only [oracleOf_realSet] using h
  · intro h
    exact ⟨realSet A,ha,realSet B,hb,rfl,by simpa only [oracleOf_realSet] using h⟩

theorem internal_degreeEquality_graph (C : Context M) :
    ∃ g ∈ M, ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ degree A = degree B :=
  internal_binary_relation C (fun A B => degree A = degree B)
    (degree_equal_arith (parameter_arith 0) (parameter_arith 1))

end
end TuringRigidity.SetModelSyntax

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

theorem degree_universe (C : Context M) :
    ∃ D ∈ M, ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A) := by
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  refine ⟨quotientSet r E r,quotient_mem M C.transitive C.power C.separation hr hE hr,?_⟩
  intro x
  rw [mem_quotientSet]
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨A,hA,rfl⟩ := (hrc a).mp ha
    exact ⟨A,hA,hx.trans (class_eq_degreeSet M (lower_mem C) hrc hEc hA)⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨realSet A,(hrc _).mpr ⟨A,hA,rfl⟩,
      (class_eq_degreeSet M (lower_mem C) hrc hEc hA).symm⟩

theorem degree_order (C : Context M) :
    ∃ L ∈ M, ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B := by
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  obtain ⟨E,hE,hEc⟩ := internal_degreeEquality_graph C
  obtain ⟨R,hR,hRc⟩ := internal_binary_relation C Reduces
    (reduces_arith (parameter_arith 0) (parameter_arith 1))
  refine ⟨actionGraph r E r R,
    action_mem M C.transitive C.pairing C.union C.power C.separation hr hE hr hR,?_⟩
  intro A hA B hB
  rw [mem_actionGraph]
  constructor
  · rintro ⟨x,hx,y,hy,hxy,he⟩
    obtain ⟨X,hX,rfl⟩ := (hrc x).mp hx
    obtain ⟨Y,hY,rfl⟩ := (hrc y).mp hy
    rw [class_eq_degreeSet M (lower_mem C) hrc hEc hX,
      class_eq_degreeSet M (lower_mem C) hrc hEc hY] at he
    obtain ⟨ha,hb⟩ := ZFSet.pair_inj.mp he
    have ha' := degreeSet_injective ha
    have hb' := degreeSet_injective hb
    have hab := (hRc X hX Y hY).mp hxy
    exact ((degree_eq_iff A X).mp ha').1.trans
      (hab.trans ((degree_eq_iff B Y).mp hb').2)
  · intro hab
    refine ⟨realSet A,(hrc _).mpr ⟨A,hA,rfl⟩,realSet B,(hrc _).mpr ⟨B,hB,rfl⟩,
      (hRc A hA B hB).mpr hab,?_⟩
    rw [class_eq_degreeSet M (lower_mem C) hrc hEc hA,
      class_eq_degreeSet M (lower_mem C) hrc hEc hB]

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_NativePersistenceSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability ArithmeticTree
universe u
noncomputable section

theorem InternalFormula.realize_rename (p : InternalFormula) (M : ZFSet.{u})
    (v : ℕ → ℕ) (e : ℕ → ZFSet.{u}) :
    (p.rename v).Realize M e ↔ p.Realize M (e ∘ v) := by
  induction p generalizing v e with
  | bounded p => exact p.realize_rename M v e
  | conj p q hp hq => exact and_congr (hp v e) (hq v e)
  | neg p hp => exact not_congr (hp v e)
  | existsSet p hp =>
    change (∃ x ∈ M, (p.rename (liftMap v)).Realize M (cons x e)) ↔ _
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    have he : cons x e ∘ liftMap v = cons x (e ∘ v) := by funext i; cases i <;> rfl
    exact (hp (liftMap v) (cons x e)).trans (he ▸ Iff.rfl)

theorem realize_nonidentityFormula (M : ZFSet.{u}) (hM : Transitive M)
    (D L i : ZFSet.{u}) (hD : D ∈ M) (hL : L ∈ M) (hi : i ∈ M) (hω : ZFSet.omega.{u} ∈ M) :
    nonidentityFormula.Realize M (cons D (cons L (cons i (fun _ => ZFSet.omega)))) ↔
      NativeNonidentity M D L i := by
  change (∃ f ∈ M, _) ↔ ∃ f ∈ M, _
  apply exists_congr
  intro f
  apply and_congr_right
  intro hf
  let e := cons f (cons D (cons L (cons i (fun _ => ZFSet.omega))))
  have he : ∀ j, e j ∈ M := by
    intro j
    rcases j with _|_|_|_|j <;> simp [e,hf,hD,hL,hi,hω]
  have hr : e ∘ nativeSlots = cons D (cons L (cons i (cons f (fun _ => ZFSet.omega)))) := by
    funext j
    rcases j with _|_|_|_|j <;> rfl
  change ((actionFormula 0 3 2).Realize M e ∧
    (setMovedFormula 0 3).Realize M e ∧ (persistenceFormula.rename nativeSlots).Realize M e) ↔ _
  rw [(actionFormula 0 3 2).absolute M hM e he,eval_actionFormula,
    (setMovedFormula 0 3).absolute M hM e he,eval_setMovedFormula,
    InternalFormula.realize_rename,hr]
  rfl

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTAbsolutenessEndpoint
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetModelSyntax SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions
universe u
noncomputable section

theorem source_4_2_2_transitive_countable (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : _root_.OAI.TuringRigidity.SetModelCountability.InternallyCountable M (idealSet I))
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    ∃ D ∈ M, ∃ L ∈ M,
      (∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A)) ∧
      (∀ A ∈ reals M, ∀ B ∈ reals M,
        ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B) ∧
      (∀ ρ : I ≃o I, automorphismSet ρ ∈ M →
        (persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
          (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) ↔ Persistent I ρ)) ∧
      (nonidentityFormula.Realize M (cons D (cons L (cons (idealSet I) (fun _ => ZFSet.omega)))) ↔
        ∃ ρ : I ≃o I, Persistent I ρ ∧ ∃ x : I, ρ x ≠ x) := by
  let C := sourceContext M hM hT
  obtain ⟨D,hDM,hD⟩ := degree_universe C
  obtain ⟨L,hLM,hL⟩ := degree_order C
  exact ⟨D,hDM,L,hLM,hD,hL,
    fun ρ hρ => native_persistence_absolute M hM hT hDM hLM hD hL I hI hct ρ hρ hz,
    (realize_nonidentityFormula M hM D L (idealSet I) hDM hLM hI C.omega_mem).trans
      (native_nonidentity_absolute M hM hT hDM hLM hD hL I hI hct hz)⟩

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceTGenericPersistence
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetModelSyntax SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions CountableForcing
universe u
noncomputable section

theorem nativePersistent_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : _root_.OAI.TuringRigidity.SetModelCountability.InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    NativePersistent M I ρ ↔ Persistent I ρ := by
  constructor
  · rintro ⟨D,hDM,L,hLM,hD,hL,hp⟩
    exact (native_persistence_absolute M hM hT hDM hLM hD hL I hI hct ρ hρ hz).mp hp
  · intro hp
    obtain ⟨D,hDM,L,hLM,hD,hL,hpD,_⟩ := source_4_2_2_transitive_countable M hM hT I hI hct hz
    exact ⟨D,hDM,L,hLM,hD,hL,(hpD ρ hρ).mpr hp⟩

theorem generic_nativePersistent_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (ht : ⊤ ∈ G.carrier)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hct : _root_.OAI.TuringRigidity.SetModelCountability.InternallyCountable (genericExtensionSet M c G.carrier) (idealSet I)) :
    NativePersistent (genericExtensionSet M c G.carrier) I ρ ↔ Persistent I ρ := by
  have hsub := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  exact nativePersistent_iff _ (genericExtensionSet_transitive M c hM G.carrier)
    (extension_sourceT M hM hT hc hoM ho G hG ht) I (hsub hI) hct ρ (hsub hρ) hz

end
end TuringRigidity.ArithmeticTree

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_NativeModelCompatibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel SetModelReals SetDegreeDecoding PersistentRestrictions PersistentPresentation
universe u

theorem native_countability_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    SetModelCountability.InternallyCountable M a ↔ InternallyCountable M a := by
  unfold SetModelCountability.InternallyCountable InternallyCountable
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  have he : ∀ i, cons f (cons ZFSet.omega (fun _ => a)) i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hf
    · exact sourceT_omega_mem M hM hT
    · exact ha
  rw [Formula.absolute _ M hM _ he,SetModelCountability.eval_ontoFormula]
  rfl

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_NativeGenericWitness
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticTree
open BoundedSetTheory TransitiveNameModel SetDegreeDecoding PersistentRestrictions
open CountableForcing AtomicForcing
universe u

theorem SetGenericallyPersistent.persistent {M : ZFSet.{u}}
    (hM : Transitive M) (hT : SourceT M) {I : CountableIdeal}
    (hI : idealSet I ∈ M) {ρ : I ≃o I} (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (h : SetGenericallyPersistent M I ρ) : Persistent I ρ := by
  obtain ⟨c,o,ord,ot,hc,ho,hos,G,hG,hct,hn⟩ := h
  let := ord
  let := ot
  obtain ⟨p,hp⟩ := G.nonempty
  exact (generic_nativePersistent_iff M hM hT hc ho hos G hG
    (G.upper le_top hp) I hI ρ hρ hz hct).mp hn

theorem setGenericallyPersistent_iff_oai (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (I : CountableIdeal)
    (hI : idealSet I ∈ M) (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    SetGenericallyPersistent M I ρ ↔ Persistent I ρ := by
  constructor
  · exact SetGenericallyPersistent.persistent hM hT hI hρ hz
  · intro hp
    obtain ⟨c,hc,hdef⟩ := InternalCollapse.conditions_exist M hM hT hI
    have h0 : (∅ : ZFSet.{u}) ∈ c := (hdef ∅).mpr
      ⟨hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero,InternalCollapse.prefix_empty _⟩
    let := InternalCollapse.order c
    let := InternalCollapse.collapsePreorder c
    let := InternalCollapse.top c h0
    have ho := InternalCollapse.orderSet_mem M hM hT hc
    obtain ⟨G,ht,hG⟩ := AtomicForcing.countable_ground_generic M ⟨c,hc⟩ (⊤ : Conditions c)
    have hne : ∃ x, x ∈ idealSet.{u} I := by
      obtain ⟨d,hd⟩ := I.nonempty
      exact ⟨degreeSet d,(mem_idealSet I _).mpr ⟨d,hd,rfl⟩⟩
    have hcount := InternalCollapse.internal_counting M hM hT hI hc hdef hne G hG
    have hE := genericExtensionSet_transitive M c hM G.carrier
    have hTE := extension_sourceT M hM hT hc ho (InternalCollapse.orderSet_pair c) G hG ht
    have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
    have hct := (native_countability_iff _ hE hTE (hME hI)).mpr hcount
    exact ⟨c,InternalCollapse.orderSet c,inferInstance,inferInstance,hc,ho,
      InternalCollapse.orderSet_pair c,G,hG,hct,
      (generic_nativePersistent_iff M hM hT hc ho (InternalCollapse.orderSet_pair c)
        G hG ht I hI ρ hρ hz hct).mpr hp⟩

end TuringRigidity.ArithmeticTree

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff_oai.{u} := @OAI.TuringRigidity.ArithmeticTree.setGenericallyPersistent_iff_oai.{u}
