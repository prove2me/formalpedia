-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.prescribed_unrestricted_ground_program
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:34:23.238202+00:00
-- url     : https://prove2.me/submissions/b51901d3-2c34-422f-9cc0-12195e162a05

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_BoundedForcing_projected_arithmetic_output_cone
import Theorems.Thm_OAI_TuringRigidity_InternalCohen_groundGeneric_table_simulation
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_prescribed_real_hull_extension

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

theorem Runs.prec {f g : X → ℕ →. ℕ} (hf : Runs O f) (hg : Runs O g) :
    Runs O (fun x p => ((Nat.unpair p).2).rec (f x (Nat.unpair p).1)
      (fun y ih => ih.bind (fun i => g x (Nat.pair (Nat.unpair p).1 (Nat.pair y i))))) := by
  obtain ⟨p,hp⟩ := hf; obtain ⟨q,hq⟩ := hg
  exact ⟨.prec p q,fun x => by simp only [OracleCode.eval,hp x,hq x]; rfl⟩

theorem Runs.find {f : X → ℕ →. ℕ} (hf : Runs O f) :
    Runs O (fun x a => Nat.rfind (fun n => (fun m => decide (m=0)) <$> f x (Nat.pair a n))) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨.find p,fun x => by simp only [OracleCode.eval,hp x]; rfl⟩

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

theorem initial_program (g : X → ℕ → ℕ)
    (hquery : Runs O (fun x n => Part.some (g x n))) :
    Runs O (fun x m => Part.some (encode (UniformOracle.oraclePrefix (g x) m))) := by
  have hy := (primrec (O := O)) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := (primrec (O := O)) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp ((primrec (O := O)) (UniformOracle.appendEncoded_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hquery hy))
  have hp := Runs.prec ((primrec (O := O)) (Primrec.const (encode ([] : List ℕ)))) hs
  have hh := Runs.comp hp (total_pair ((primrec (O := O)) (Primrec.const 0))
    ((primrec (O := O)) Primrec.id))
  apply hh.of_eq
  intro x n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [UniformOracle.appendEncoded,UniformOracle.oraclePrefix,List.range_succ]

private theorem flag_primrec : Primrec flag := by
  apply (Primrec.cond (Primrec.option_isSome.comp (Primrec.option_getD_default.comp (Primrec.decode (α := Option ℕ))))
    (Primrec.const 0) (Primrec.const 1)).of_eq
  intro n
  change (cond ((decode (α := Option ℕ) n).getD none).isSome 0 1) = _
  cases hh : ((decode (α := Option ℕ) n).getD none).isSome <;> simp only [flag,hh] <;> rfl
private theorem answer_primrec : Primrec answer :=
  Primrec.option_getD_default.comp (Primrec.option_getD_default.comp Primrec.decode)

theorem total_search {E : X → ℕ → ℕ → Option ℕ}
    (hE : Runs O (fun x z => Part.some (encode (E x (Nat.unpair z).1 (Nat.unpair z).2))))
    (f : X → ℕ → ℕ) (hsound : ∀ x n m a, a ∈ E x n m → a = f x n)
    (hcomplete : ∀ x n, ∃ m a, a ∈ E x n m) :
    Runs O (fun x n => Part.some (f x n)) := by
  have hflag := total_comp (primrec flag_primrec) hE
  have hfind := Runs.find hflag
  have hpair := Runs.pair (primrec Primrec.id) hfind
  have hrun := Runs.comp (primrec answer_primrec) (Runs.comp hE hpair)
  apply hrun.of_eq
  intro x n
  apply Part.eq_some_iff.mpr
  have hex : ∃ m, (E x n m).isSome = true := by
    obtain ⟨m,a,ha⟩ := hcomplete x n
    exact ⟨m,Option.isSome_iff_exists.mpr ⟨a,ha⟩⟩
  let m := Nat.find hex
  have hm := Nat.find_spec hex
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp hm
  have hval : a = f x n := hsound x n m a ha
  have hmem : m ∈ Nat.rfind (fun k =>
      (fun v : ℕ => decide (v=0)) <$> Part.some (flag (encode (E x n k)))) := by
    apply Nat.mem_rfind.mpr
    constructor
    · simp [flag,m,hm]
    · intro k hk
      have hk' : (E x n k).isSome = false := Bool.eq_false_iff.mpr (Nat.find_min hex hk)
      simp [flag,hk']
  apply Part.mem_bind_iff.mpr
  refine ⟨encode (E x n m),?_,?_⟩
  · apply Part.mem_bind_iff.mpr
    refine ⟨Nat.pair n m,?_,?_⟩
    · simp only [Seq.seq]
      apply Part.mem_bind_iff.mpr
      refine ⟨Nat.pair n,(Part.mem_map_iff _).mpr ⟨n,Part.mem_some _,rfl⟩,?_⟩
      exact (Part.mem_map_iff _).mpr ⟨m,by simpa only [Nat.unpair_pair] using hmem,rfl⟩
    · simp
  · have hea : E x n m = some a := Option.mem_def.mp ha
    apply Part.mem_some_iff.mpr
    rw [hea]
    simpa only [answer,Encodable.encodek,Option.getD_some] using hval.symm

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticOracles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable UniformOracle CommonIdeal IndexMatrix TableIndices OracleJump EncodedForcing
noncomputable section

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

end
end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelRealOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic Encodable TableIndices OracleJump IndexMatrix
universe u

theorem sourceT_real_jump (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : Oracle} (hA : A ∈ modelReals M) : jump A ∈ modelReals M :=
  sourceT_arithmetic_oracle M hM hT (jump_arith (parameter_arith 0))
    (fun _ => A) (fun _ => hA) 0

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

theorem actual_degreeCode_membership (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ C : Oracle, realCode C ∈ R ↔ C ∈ modelReals M)
    {A : Oracle} (hA : A ∈ modelReals M) (B : Oracle) :
    realCode B ∈ degreeCode R A ↔ degree B = degree A := by
  rw [realCode_mem_degreeCode]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  exact (hR B).mpr (sourceT_real_lower M hM hT hA ((degree_eq_iff B A).mp h).1)

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

end TuringRigidity.BoundedSetTheory

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

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGenericUnion
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenGenericUnion
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenSymmetry CohenConditionCode CohenGroundPoset CohenGroundGeneric
open InternalCohen (alphabet mem_alphabet bitSet)
open InternalCollapse (unionGraph mem_unionGraph)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem definedAt_mem (M A x : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hx : x ∈ A) : definedAt A x ∈ M := by
  let e := cons alphabet (fun _ => x)
  have he : ∀ i, e i ∈ M := by
    intro i; cases i
    exact InternalCohen.alphabet_mem M hM hT
    exact hM A hA x hx
  simpa only [definedAt,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.pairMem 3 0 1)) e he (conditions_mem M A hM hT hA)

theorem assign_dense {ι : Type*} (i : ι) :
    Dense {p : Condition ι | ∃ b, p.val i = some b} := by
  classical
  intro p
  cases hi : p.val i with
  | some b => exact ⟨p,le_rfl,b,hi⟩
  | none =>
    let q : Condition ι := {
      val j := if j = i then some false else p.val j
      finite := (p.finite.insert i).subset (by
        intro j hj
        by_cases he : j = i
        · exact Or.inl he
        · exact Or.inr (by simpa [he] using hj)) }
    refine ⟨q,?_,false,by simp [q]⟩
    intro j b hj
    by_cases he : j = i
    · subst j; rw [hi] at hj; cases hj
    · simpa [q,he] using hj

theorem definedAt_dense (A x : ZFSet.{0}) (hx : x ∈ A) :
    Dense {q : Conditions (conditions A) | label _ q ∈ definedAt A x} := by
  let i : Conditions A := equivShrink A ⟨x,hx⟩
  have hi : label A i = x := by simp [i,label]
  intro p
  obtain ⟨q,hq,b,hqb⟩ := assign_dense i ((conditionEquiv A).symm p)
  refine ⟨conditionEquiv A q,by simpa using (conditionEquiv A).monotone hq,?_⟩
  change label _ (encode A q) ∈ definedAt A x
  rw [label_encode,definedAt,ZFSet.mem_sep]
  refine ⟨(mem_conditions A _).mpr (graph_isCondition A q),bitSet b,
    (mem_alphabet _).mpr ⟨b,rfl⟩,?_⟩
  rw [←hi,pair_mem_graph]; exact hqb

theorem union_function (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (G : GenericFilter (Conditions (conditions A)))
    (hG : AtomicForcing.GroundGeneric M G) : FunctionGraph A alphabet (unionGraph G) := by
  constructor
  · intro z hz
    obtain ⟨p,_,hzp⟩ := (mem_unionGraph G z).mp hz
    have hp := ((mem_conditions A _).mp (label_mem _ p)).1
    exact ZFSet.mem_prod.mp (((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp hp).1 hzp)
  · intro x hx
    obtain ⟨p,hp,hpx⟩ := hG (definedAt A x) (definedAt_mem M A x hM hT hA hx)
      (definedAt_dense A x hx)
    obtain ⟨_,b,hb,hpb⟩ := ZFSet.mem_sep.mp hpx
    refine ⟨b,hb,(mem_unionGraph G _).mpr ⟨p,hp,hpb⟩,?_⟩
    intro c hc hxc
    obtain ⟨q,hq,hqc⟩ := (mem_unionGraph G _).mp hxc
    obtain ⟨r,_,hrp,hrq⟩ := G.directed hp hq
    exact ((mem_conditions A _).mp (label_mem _ r)).2 x hx c hc b hb (hrq hqc) (hrp hpb)

theorem union_internal (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (G : GenericFilter (Conditions (conditions A)))
    (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M (conditions A) G.carrier ∧
      FunctionGraph A alphabet (unionGraph G) :=
  ⟨InternalCollapse.unionGraph_mem_extension M hM hT (conditions_mem M A hM hT hA)
      (empty_mem_conditions A) G hG,
    union_function M A hM hT hA G hG⟩

theorem manyColumn_union (M K : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hK : K ∈ M)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : AtomicForcing.GroundGeneric M G) :
    unionGraph G ∈ genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier ∧
      FunctionGraph (ZFSet.prod K ZFSet.omega) alphabet (unionGraph G) :=
  union_internal M _ hM hT (product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)) G hG

end TuringRigidity.CohenGenericUnion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnRealName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
attribute [local instance] InternalCollapse.order CohenNiceNameConstruction.cohenTop
open InternalCohen (bitSet)

theorem eval_realNameFormula (z c f r one C a : ZFSet.{0}) (e : ℕ → ZFSet.{0}) :
    realNameFormula.Eval
      (cons z (cons c (cons ZFSet.omega (cons f (cons r (cons one (cons C (cons a e)))))))) ↔
      ∃ q ∈ c, ∃ n ∈ ZFSet.omega, ∃ v ∈ r, ∃ x ∈ C,
        ZFSet.pair n v ∈ f ∧ x = ZFSet.pair a n ∧
        ZFSet.pair x one ∈ q ∧ z = ZFSet.pair v q := by
  simp only [realNameFormula,BoundedSetTheory.Formula.Eval,BoundedSetTheory.Formula.eval_pairMem,
    BoundedSetTheory.Formula.eval_orderedPair,cons_zero,cons_succ]

theorem mem_realNameCode (K a f z : ZFSet.{0}) (ha : a ∈ K) : z ∈ realNameCode K a f ↔
    ∃ q ∈ poset K, ∃ n ∈ ZFSet.omega, ∃ v,
      ZFSet.pair n v ∈ f ∧ ZFSet.pair (ZFSet.pair a n) (bitSet true) ∈ q ∧ z = ZFSet.pair v q := by
  rw [realNameCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,q,hq,n,hn,v,_,x,_,hv,rfl,hbit,hz⟩; exact ⟨q,hq,n,hn,v,hv,hbit,hz⟩
  · rintro ⟨q,hq,n,hn,v,hv,hbit,rfl⟩
    have hr := second_mem_doubleUnion hv
    exact ⟨ZFSet.mem_prod.mpr ⟨v,hr,q,hq,rfl⟩,q,hq,n,hn,v,hr,ZFSet.pair a n,ZFSet.pair_mem_prod.mpr ⟨ha,hn⟩,hv,rfl,hbit,rfl⟩

theorem realNameCode_mem (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    {f : ZFSet.{0}} (hf : f ∈ M) : realNameCode K a f ∈ M := by
  have hc := (CohenGroundPoset.manyColumn_internal M K hM hT hK).1
  have hω := sourceT_omega_mem M hM hT
  have hr := iterUnion_mem M hM hT.union hf 2
  have h1 : bitSet true ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hK hω
  have haM := hM K hK a ha
  let e := cons (poset K) (cons ZFSet.omega (cons f (cons (iterUnion 2 f) (cons (bitSet true) (cons (ZFSet.prod K ZFSet.omega) (cons a (fun _ => a)))))))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|_|_|_|_|_|i <;> assumption
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded realNameFormula e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hr hc)
  have heq : ZFSet.sep (fun z => realNameFormula.Eval (cons z e))
      (ZFSet.prod (iterUnion 2 f) (poset K)) = realNameCode K a f := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_sep,realNameCode]
    exact and_congr_right (fun _ => eval_realNameFormula z (poset K) f (iterUnion 2 f) (bitSet true)
      (ZFSet.prod K ZFSet.omega) a (fun _ => a))
  exact heq ▸ hs

theorem encode_realName (K a d r f : ZFSet.{0}) (ha : a ∈ K) (hω : ZFSet.omega ⊆ d)
    (hf : CheckGraph d r f (label (poset K) ⊤)) :
    (realName K a).encode (label (poset K)) = realNameCode K a f := by
  have hfr : TransitiveNameModel.FunctionGraph d r f := ⟨hf.2.1,hf.2.2.1⟩
  apply ZFSet.ext; intro z
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range,mem_realNameCode K a f z ha]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hz⟩
    have hn := (mem_omega (natSet n)).mpr ⟨n,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := hf.2.2.1 _ (hω hn)
    have he := hf.correct _ (hω hn) v hv hfv
    refine ⟨label (poset K) q,label_mem _ _,natSet n,hn,v,hfv,hbit,?_⟩
    simpa only [realName,encode_check,he] using hz.symm
  · rintro ⟨q,hq,n,hn,v,hfv,hbit,hz⟩
    obtain ⟨k,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨q,rfl⟩ := label_surjective (poset K) hq
    have he := hf.correct _ (hω hn) v (hfr.value_mem hfv) hfv
    exact ⟨⟨(q,k),hbit⟩,by simpa only [realName,encode_check,he] using hz.symm⟩

theorem realName_internal (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K) :
    (realName K a).encode (label (poset K)) ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨d,hdM,hd,hωd⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hω
  obtain ⟨q,hqM,hq⟩ := internal_power M hM hT.powerSet hdM
  obtain ⟨f,hf,hfg⟩ := internal_checkGraph M d q (label (poset K) ⊤) hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hT.replacement.finitePrefix
    hdM hqM (hM _ ((CohenGroundPoset.manyColumn_internal M K hM hT hK).1) _ (label_mem (poset K) ⊤)) hd hq ZFSet.omega hωd
  have hsub : ZFSet.omega ⊆ hull d q ZFSet.omega := fun x hx =>
    hull_transitive d q ZFSet.omega hd _ (self_mem_hull d q hωd) x hx
  rw [encode_realName K a _ _ f ha hsub hfg]
  exact realNameCode_mem M K a hM hT hK ha hf

end TuringRigidity.CohenColumnRealName

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_SparseCohenFilter
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SparseCohenFilter
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCollapse
open InternalCohen (alphabet bitSet mem_alphabet bitSet_injective)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem finite_covered {c : ZFSet.{0}} (G : GenericFilter (Conditions c))
    (S : Set ZFSet.{0}) (hS : S.Finite)
    (hsub : ∀ z ∈ S, z ∈ unionGraph G) :
    ∃ p ∈ G.carrier, ∀ z ∈ S, z ∈ label c p := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    obtain ⟨p,hp⟩ := G.nonempty
    exact ⟨p,hp,fun _ h => False.elim h⟩
  | @insert z S hz hS ih =>
    obtain ⟨p,hp,hpS⟩ := ih (fun x hx => hsub x (Or.inr hx))
    obtain ⟨q,hq,hqz⟩ := (mem_unionGraph G z).mp (hsub z (Or.inl rfl))
    obtain ⟨r,hr,hrp,hrq⟩ := G.directed hp hq
    refine ⟨r,hr,fun x hx => ?_⟩
    rcases hx with rfl|hx
    · exact hrq hqz
    · exact hrp (hpS x hx)

theorem mem_filter_iff_subset_union (A : ZFSet.{0})
    (G : GenericFilter (Conditions (conditions A)))
    (p : Conditions (conditions A)) :
    p ∈ G.carrier ↔ label _ p ⊆ unionGraph G := by
  constructor
  · intro hp z hz
    exact (mem_unionGraph G z).mpr ⟨p,hp,hz⟩
  · intro hsub
    have hfin := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions A _).mp (label_mem _ p)).1).2
    obtain ⟨q,hq,hqp⟩ := finite_covered G (label _ p) hfin (fun z hz => hsub hz)
    exact G.upper hqp hq

end TuringRigidity.SparseCohenFilter

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnRealValue
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
open InternalCohen (bitSet alphabet mem_alphabet bitSet_injective)
open CohenGroundPoset InternalCohenProjectedGeneric InternalCohenRestriction InternalCohenFactor
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem union_real (K a : ZFSet.{0}) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K)))
    (hfun : FunctionGraph (ZFSet.prod K ZFSet.omega) alphabet (unionGraph G)) :
    ∃ A : Oracle, ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b := by
  classical
  have hn (n : ℕ) : ZFSet.pair a (natSet n) ∈ ZFSet.prod K ZFSet.omega :=
    ZFSet.pair_mem_prod.mpr ⟨ha,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hex (n : ℕ) : ∃ b : Bool,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G := by
    obtain ⟨b,hb,hnb,_⟩ := hfun.2 _ (hn n)
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    exact ⟨b,hnb⟩
  let A : Oracle := fun n => (hex n).choose
  refine ⟨A,fun n b => ⟨fun hb => ?_,fun he => he ▸ (hex n).choose_spec⟩⟩
  obtain ⟨v,hv,hnv,huniq⟩ := hfun.2 _ (hn n)
  exact bitSet_injective ((huniq _ ((mem_alphabet _).mpr ⟨A n,rfl⟩)
    (hex n).choose_spec).trans (huniq _ ((mem_alphabet _).mpr ⟨b,rfl⟩) hb).symm)

theorem val_realName (K a : ZFSet.{0}) (G : GenericFilter (Conditions (poset K)))
    (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) :
    (realName K a).val G.carrier = realCode A := by
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions (poset K)) ∈ G.carrier := G.upper le_top hp
  apply ZFSet.ext; intro z
  rw [realName,Name.mem_val]
  simp only [Name.val_check _ ht]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hq,rfl⟩
    exact (natSet_mem_realCode A n).mpr ((hA n true).mp
      ((mem_unionGraph G _).mpr ⟨q,hq,hbit⟩))
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_omega _).mp (realCode_subset A hz)
    obtain ⟨q,hq,hbit⟩ := (mem_unionGraph G _).mp
      ((hA n true).mpr ((natSet_mem_realCode A n).mp hz))
    exact ⟨⟨(q,n),hbit⟩,hq,rfl⟩

theorem generic_real_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, (realName K a).val G.carrier = realCode A ∧
      (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      realCode A ∈ genericExtensionSet M (poset K) G.carrier := by
  obtain ⟨A,hA⟩ := union_real K a ha G (CohenGenericUnion.manyColumn_union M K hM hT hK G hG).2
  have hv := val_realName K a G A hA
  exact ⟨A,hv,hA,(mem_extensionSet M (poset K) _ _).mpr
    ⟨realName K a,realName_internal M K a hM hT hK ha,hv⟩⟩

theorem singleton_filter_iff (a : ZFSet.{0})
    (G : GenericFilter (Conditions (poset {a}))) (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b)
    (p : Conditions (poset {a})) :
    p ∈ G.carrier ↔ ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → A n = b := by
  rw [SparseCohenFilter.mem_filter_iff_subset_union]
  constructor
  · intro hp n b hb
    exact (hA n b).mp (hp hb)
  · intro hp z hz
    have hsub := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
      ((mem_conditions (ZFSet.prod {a} ZFSet.omega) _).mp (label_mem _ p)).1).1
    obtain ⟨x,hx,b,hb,rfl⟩ := ZFSet.mem_prod.mp (hsub hz)
    obtain ⟨a',ha',n,hn,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain rfl := ZFSet.mem_singleton.mp ha'
    obtain ⟨n,rfl⟩ := (mem_omega _).mp hn
    obtain ⟨b,rfl⟩ := (mem_alphabet _).mp hb
    exact (hA n b).mpr (hp n b hz)

theorem pair_mem_projected_union (C B : ZFSet.{0}) (hBC : B ⊆ C)
    (G : GenericFilter (Conditions (conditions C))) (x : ZFSet.{0}) (hx : x ∈ B) (b : Bool) :
    ZFSet.pair x (bitSet b) ∈ unionGraph (projected C B hBC G) ↔
      ZFSet.pair x (bitSet b) ∈ unionGraph G := by
  rw [InternalCollapse.mem_unionGraph,InternalCollapse.mem_unionGraph]
  constructor
  · rintro ⟨q,hq,hbit⟩
    obtain ⟨p,hp,rfl⟩ := (mem_projected C B hBC G q).mp hq
    rw [label_project,pair_restrict] at hbit
    exact ⟨p,hp,hbit.1⟩
  · rintro ⟨p,hp,hbit⟩
    refine ⟨project C B hBC p,projected_contains C B hBC G hp,?_⟩
    rw [label_project,pair_restrict]
    exact ⟨hbit,hx,(mem_alphabet _).mpr ⟨b,rfl⟩⟩

theorem projected_real_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G) :
    let C := ZFSet.prod K ZFSet.omega
    let B := ZFSet.prod {a} ZFSet.omega
    let hBC := singleton_coordinates_subset K a ha
    ∃ A : Oracle,
      (realName {a} a).val (projected C B hBC G).carrier = realCode A ∧
      (realName K a).val G.carrier = realCode A ∧
      (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      (∀ p : Conditions (poset {a}), p ∈ (projected C B hBC G).carrier ↔ ∀ n b,
        ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → A n = b) := by
  intro C B hBC
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  obtain ⟨A,hv,hA,_⟩ := generic_real_value M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) (projected C B hBC G)
    (projected_groundGeneric M C B hM hT hC hB hBC G hG)
  have hfull (n : ℕ) (b : Bool) :
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ unionGraph G ↔ A n = b := by
    rw [←pair_mem_projected_union C B hBC G _
      (ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,(mem_omega _).mpr ⟨n,rfl⟩⟩) b]
    exact hA n b
  exact ⟨A,hv,val_realName K a G A hfull,hfull,
    singleton_filter_iff a (projected C B hBC G) A hA⟩

end TuringRigidity.CohenColumnRealName

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnPrefixCone
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenProjectedGeneric InternalCohenFactor
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem finite_column_bound (K a : ZFSet.{0}) (p : Conditions (poset K)) :
    ∃ N : ℕ, ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → n < N := by
  have hfin := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
    ((mem_conditions (ZFSet.prod K ZFSet.omega) _).mp (label_mem _ p)).1).2
  let f (b : Bool) (n : ℕ) := ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b)
  have hi (b : Bool) : Function.Injective (f b) := by
    intro n m he
    exact natSet_injective (ZFSet.pair_inj.mp (ZFSet.pair_inj.mp he).1).2
  have hs := (hfin.preimage (hi false).injOn).union (hfin.preimage (hi true).injOn)
  obtain ⟨N,hN⟩ := hs.bddAbove
  refine ⟨N+1,fun n b hn => Nat.lt_succ_of_le (hN ?_)⟩
  cases b
  · exact Or.inl hn
  · exact Or.inr hn

theorem selected_prefix_cone (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (p : Conditions (poset K)) (hp : p ∈ G.carrier) :
    let C := ZFSet.prod K ZFSet.omega
    let B := ZFSet.prod {a} ZFSet.omega
    let hBC := singleton_coordinates_subset K a ha
    ∃ A : Oracle, (realName K a).val G.carrier = realCode A ∧ ∃ N : ℕ,
      ∀ H : GenericFilter (Conditions (poset K)), AtomicForcing.GroundGeneric M H →
      ∀ A' : Oracle, (realName K a).val H.carrier = realCode A' →
        (∀ n < N, A' n = A n) → project C B hBC p ∈ (projected C B hBC H).carrier := by
  intro C B hBC
  obtain ⟨A,_,hval,_,hfilter⟩ := projected_real_value M K a hM hT hK ha G hG
  obtain ⟨N,hN⟩ := finite_column_bound {a} a (project C B hBC p)
  have hpA := (hfilter _).mp (projected_contains C B hBC G hp)
  refine ⟨A,hval,N,fun H hH A' hval' hprefix => ?_⟩
  obtain ⟨AH,_,hvalH,_,hfilterH⟩ := projected_real_value M K a hM hT hK ha H hH
  have he : AH = A' := realCode_injective (hvalH.symm.trans hval')
  subst AH
  apply (hfilterH _).mpr
  intro n b hb
  exact (hprefix n (hN n b hb)).trans (hpA n b hb)

end TuringRigidity.CohenColumnRealName

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalDenseInclusion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalDenseInclusion
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem densePull_mem (M a b D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M) : densePull a b D ∈ M := by
  let e := cons b (fun _ => D)
  have he : ∀ i, e i ∈ M := by intro i; cases i; exact hb; exact hD
  simpa only [densePull,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.member 0 3) (.subset 0 1))) e he ha

end TuringRigidity.InternalDenseInclusion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPrefixDensity
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenPrefixDensity
open TransitiveNameModel BoundedSetTheory InternalCohen CohenConditionCode InternalFiniteSubsets
attribute [local instance] InternalCollapse.order

theorem condition_extends_prefix (q : ZFSet.{0})
    (hq : q ∈ CohenGroundPoset.conditions ZFSet.omega) :
    ∃ s : List Bool, q ⊆ wordCode s := by
  classical
  obtain ⟨p,rfl⟩ := (isCondition_iff_graph _ q).mp ((CohenGroundPoset.mem_conditions _ _).mp hq)
  let f (n : ℕ) : Conditions ZFSet.omega :=
    equivShrink _ ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hfl (n : ℕ) : label ZFSet.omega (f n) = natSet n := by simp [f,label]
  have hfi : Function.Injective f := by
    intro n m h
    exact natSet_injective (by simpa only [hfl] using congrArg (label ZFSet.omega) h)
  have hfin := p.finite.preimage hfi.injOn
  obtain ⟨n,hn⟩ := hfin.bddAbove
  let s := List.ofFn (fun i : Fin (n+1) => (p.val (f i.val)).getD false)
  refine ⟨s,?_⟩
  intro z hz
  obtain ⟨i,b,hib,rfl⟩ := (mem_graph _ p z).mp hz
  obtain ⟨k,hk⟩ := (mem_omega _).mp (label_mem ZFSet.omega i)
  have he : i = f k := label_injective _ (hk.trans (hfl k).symm)
  have hkb : p.val (f k) = some b := he ▸ hib
  have hkn : k < n+1 := Nat.lt_succ_of_le (hn (by
    change p.val (f k) ≠ none
    simp [hkb]))
  rw [he,hfl]
  apply (pair_mem_wordCode s k b).mpr
  refine ⟨by simpa only [s,List.length_ofFn] using hkn,?_⟩
  simp only [s,List.getElem_ofFn,hkb,Option.getD_some]

end TuringRigidity.CohenPrefixDensity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_SparseCohenPrefixGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SparseCohenRealName
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalCohen (bitSet wordCode pair_mem_wordCode)
open CohenBorelForcing ShuffleRequirements InternalDenseInclusion
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem prefix_dense_expansion (D : ZFSet.{0})
    (hD : Dense {p : Conditions InternalCohen.conditions | label _ p ∈ D}) :
    Dense {q : Conditions poset | label _ q ∈ densePull poset InternalCohen.conditions D} := by
  intro p
  obtain ⟨s,hs⟩ := CohenPrefixDensity.condition_extends_prefix _ (label_mem poset p)
  let u : Conditions InternalCohen.conditions := InternalCohen.conditionEquiv ⟨s⟩
  have hu : label _ u = wordCode s := InternalCohen.label_encodeCondition ⟨s⟩
  obtain ⟨q,hqu,hqD⟩ := hD u
  let r := embed InternalCohen.conditions poset CohenPrefixDensity.conditions_subset q
  have hr : label poset r = label InternalCohen.conditions q := label_embed _ _ _ q
  refine ⟨r,?_,?_⟩
  · change label poset p ⊆ label poset r
    rw [hr]
    exact fun z hz => hqu (hu.symm ▸ hs hz)
  · apply ZFSet.mem_sep.mpr
    exact ⟨label_mem poset r,label _ q,label_mem _ q,hqD,by rw [hr]⟩

theorem prefix_ground_generic (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions poset)) (hG : AtomicForcing.GroundGeneric M G)
    (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ InternalCollapse.unionGraph G ↔ A n = b) :
    AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (realFilter A)) := by
  intro D hDM hD
  have hc := CohenGroundPoset.conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)
  have hp := InternalCohen.conditions_mem M hM hT
  obtain ⟨q,hq,hqD⟩ := hG (densePull poset InternalCohen.conditions D)
    (densePull_mem M poset InternalCohen.conditions D hM hT hc hp hDM)
    (prefix_dense_expansion D hD)
  obtain ⟨_,p,hp,hpD,hpq⟩ := ZFSet.mem_sep.mp hqD
  obtain ⟨s,rfl⟩ := (InternalCohen.prefix_iff_wordCode p).mp ((InternalCohen.mem_conditions p).mp hp)
  let t : Conditions InternalCohen.conditions := InternalCohen.conditionEquiv ⟨s⟩
  refine ⟨t,?_,?_⟩
  · have hreal : Realizes s A := by
      intro n hn
      have hb := (hA n s[n]).mp ((InternalCollapse.mem_unionGraph G _).mpr
        ⟨q,hq,hpq ((pair_mem_wordCode s n s[n]).mpr ⟨hn,rfl⟩)⟩)
      simpa only [List.getD,List.getElem?_eq_getElem hn,Option.getD_some] using hb.symm
    simpa only [t,InternalCohen.pushFilter,InternalCohen.conditionEquiv.symm_apply_apply,
      realFilter,Set.mem_ofPred_eq] using hreal
  · change label _ (InternalCohen.encodeCondition ⟨s⟩) ∈ D
    rwa [InternalCohen.label_encodeCondition]

end TuringRigidity.SparseCohenRealName

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalGraphEquiv
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalGraphEquiv
open TransitiveNameModel BoundedSetTheory

theorem graphEquiv_spec (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) (x : Conditions A) (y : Conditions B) :
    ZFSet.pair (label A x) (label B y) ∈ f ↔ y = graphEquiv A B f hf hi hs x := by
  exact ⟨fun h => label_injective B (hf.functional (label_mem A x) h (graphMap_spec A B f hf x)),
    fun h => h.symm ▸ graphMap_spec A B f hf x⟩

end TuringRigidity.InternalGraphEquiv

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenReindex
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohenReindex
open TransitiveNameModel BoundedSetTheory CohenGroundPoset CohenConditionCode CohenSymmetry
open InternalCohen (alphabet bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem matchesFormula_spec (A B f p q bit : ℕ) (e : ℕ → ZFSet.{0}) (hb : e bit = alphabet) :
    (matchesFormula A B f p q bit).Eval e ↔ Matches (e A) (e B) (e f) (e p) (e q) := by
  simp only [Matches,matchesFormula,Formula.eval_allMem,Formula.eval_imp,Formula.eval_iff,
    Formula.eval_pairMem,cons_zero,cons_succ,hb]

theorem matches_graph_iff (A B f : ZFSet.{0}) (e : Conditions A ≃ Conditions B)
    (he : ∀ x : Conditions A, ∀ y : Conditions B,
      ZFSet.pair (label A x) (label B y) ∈ f ↔ y = e x)
    (p : Condition (Conditions A)) (q : Condition (Conditions B)) :
    Matches A B f (graph A p) (graph B q) ↔ q = CohenCoordinates.reindex e p := by
  constructor
  · intro h
    apply Condition.ext; funext j
    apply Option.ext; intro b
    have hh := h (label A (e.symm j)) (label_mem _ _) (label B j) (label_mem _ _)
      ((he _ _).mpr (e.apply_symm_apply j).symm) (bitSet b) ((mem_alphabet _).mpr ⟨b,rfl⟩)
    rw [pair_mem_graph,pair_mem_graph] at hh
    exact hh.symm
  · rintro rfl x hx y hy hxy b hb
    obtain ⟨i,rfl⟩ := label_surjective A hx
    obtain ⟨j,rfl⟩ := label_surjective B hy
    obtain rfl := (he i j).mp hxy
    obtain ⟨b,rfl⟩ := (mem_alphabet b).mp hb
    rw [pair_mem_graph,pair_mem_graph]
    change p.val i = some b ↔ p.val (e.symm (e i)) = some b
    rw [e.symm_apply_apply]

theorem pair_reindexGraph (A B f p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ reindexGraph A B f ↔ p ∈ conditions A ∧ q ∈ conditions B ∧ Matches A B f p q := by
  simp only [reindexGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,h⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,h⟩
  · rintro ⟨hp,hq,h⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,h⟩

theorem reindexGraph_mem (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hf : f ∈ M) : reindexGraph A B f ∈ M := by
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  let e := cons (conditions A) (cons (conditions B) (cons A (cons B (cons f (fun _ => alphabet)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    exact hcA; exact hcB; exact hA; exact hB; exact hf; exact InternalCohen.alphabet_mem M hM hT
  have hmatches (pairValue leftCondition rightCondition : ZFSet.{0}) :
      (matchesFormula 5 6 7 1 0 8).Eval
        (cons rightCondition (cons leftCondition (cons pairValue e))) ↔
        Matches A B f leftCondition rightCondition :=
    matchesFormula_spec 5 6 7 1 0 8 _ rfl
  simpa only [reindexGraph,Formula.Eval,Formula.eval_orderedPair,hmatches,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (matchesFormula 5 6 7 1 0 8)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hcB)

theorem reindexGraph_spec (A B f : ZFSet.{0}) (e : Conditions A ≃ Conditions B)
    (he : ∀ x : Conditions A, ∀ y : Conditions B,
      ZFSet.pair (label A x) (label B y) ∈ f ↔ y = e x)
    (p : Conditions (conditions A)) (q : Conditions (conditions B)) :
    ZFSet.pair (label _ p) (label _ q) ∈ reindexGraph A B f ↔ q = reindexIso A B e p := by
  obtain ⟨p,rfl⟩ := (conditionEquiv A).surjective p
  obtain ⟨q,rfl⟩ := (conditionEquiv B).surjective q
  rw [pair_reindexGraph]
  have hp : label _ (conditionEquiv A p) = graph A p := label_encode A p
  have hq : label _ (conditionEquiv B q) = graph B q := label_encode B q
  rw [and_iff_right (label_mem _ _),and_iff_right (label_mem _ _),hp,hq,matches_graph_iff A B f e he]
  change q = CohenCoordinates.reindex e p ↔
    conditionEquiv B q = conditionEquiv B (CohenCoordinates.reindex e ((conditionEquiv A).symm (conditionEquiv A p)))
  rw [(conditionEquiv A).symm_apply_apply]
  exact (conditionEquiv B).injective.eq_iff.symm

theorem internal_reindex (M A B f : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) (hfM : f ∈ M) (hf : FunctionGraph A B f)
    (hi : ∀ x ∈ A, ∀ x' ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x')
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) :
    ∃ e : Conditions (conditions A) ≃o Conditions (conditions B),
      reindexGraph A B f ∈ M ∧
      (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ reindexGraph A B f ↔ q = e p) ∧
      conditions A ∈ M ∧ InternalCollapse.orderSet (conditions A) ∈ M ∧
      conditions B ∈ M ∧ InternalCollapse.orderSet (conditions B) ∈ M := by
  let e := InternalGraphEquiv.graphEquiv A B f hf hi hs
  exact ⟨reindexIso A B e,reindexGraph_mem M A B f hM hT hA hB hfM,
    reindexGraph_spec A B f e (InternalGraphEquiv.graphEquiv_spec A B f hf hi hs),
    (poset_internal M A hM hT hA).1,(poset_internal M A hM hT hA).2,
    poset_internal M B hM hT hB⟩

end TuringRigidity.InternalCohenReindex

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSingletonColumn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalSingletonColumn
open TransitiveNameModel BoundedSetTheory CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem pair_graph (a W u n : ZFSet.{0}) :
    ZFSet.pair u n ∈ graph a W ↔ n ∈ W ∧ u = ZFSet.pair a n := by
  constructor
  · intro h
    obtain ⟨_,v,_,m,hm,he,hv⟩ := ZFSet.mem_sep.mp h
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hm,hv⟩
  · rintro ⟨hn,hu⟩
    have huA : u ∈ ZFSet.prod {a} W := hu ▸ ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hn⟩
    exact ZFSet.mem_sep.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨huA,hn⟩,u,huA,n,hn,rfl,hu⟩

theorem graph_mem (M a W : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hW : W ∈ M) : graph a W ∈ M := by
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    (singleton_mem M hM hT.pairing ha) hW
  let e := cons (ZFSet.prod {a} W) (cons W (fun _ => a))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hA; exact hW; exact ha
  simpa only [graph,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (.orderedPair 1 5 0)))) e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hA hW)

theorem graph_function (a W : ZFSet.{0}) : FunctionGraph (ZFSet.prod {a} W) W (graph a W) := by
  refine ⟨fun z hz => ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1,?_⟩
  intro u hu
  obtain ⟨x,hx,n,hn,rfl⟩ := ZFSet.mem_prod.mp hu
  have hx_eq : x = a := ZFSet.mem_singleton.mp hx
  subst x
  exact ⟨n,hn,(pair_graph a W _ n).mpr ⟨hn,rfl⟩,fun m _ hm =>
    (ZFSet.pair_inj.mp ((pair_graph a W _ m).mp hm).2).2.symm⟩

theorem graph_injective (a W : ZFSet.{0}) :
    ∀ x ∈ ZFSet.prod {a} W, ∀ x' ∈ ZFSet.prod {a} W, ∀ y ∈ W,
      ZFSet.pair x y ∈ graph a W → ZFSet.pair x' y ∈ graph a W → x = x' := by
  intro x _ x' _ y _ hx hx'
  exact ((pair_graph a W x y).mp hx).2.trans ((pair_graph a W x' y).mp hx').2.symm

theorem graph_onto (a W : ZFSet.{0}) :
    ∀ y ∈ W, ∃ x ∈ ZFSet.prod {a} W, ZFSet.pair x y ∈ graph a W := by
  intro y hy
  exact ⟨ZFSet.pair a y,ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hy⟩,
    (pair_graph a W _ y).mpr ⟨hy,rfl⟩⟩

end TuringRigidity.InternalSingletonColumn

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumnPrefixGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenProjectedGeneric AutomorphismName
open InternalCohen (bitSet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem singleton_iso_bits (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) :
    ∃ e : Conditions (poset {a}) ≃o Conditions SparseCohenRealName.poset,
      ∃ f ∈ M,
        (∀ p q, ZFSet.pair (label _ p) (label _ q) ∈ f ↔ q = e p) ∧
        ∀ p n b, ZFSet.pair (natSet n) (bitSet b) ∈ label _ (e p) ↔
          ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p := by
  let B := ZFSet.prod {a} ZFSet.omega
  have hω := sourceT_omega_mem M hM hT
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (singleton_mem M hM hT.pairing ha) hω
  obtain ⟨e,hf,he,_⟩ := InternalCohenReindex.internal_reindex M B ZFSet.omega
    (InternalSingletonColumn.graph a ZFSet.omega) hM hT hB hω
    (InternalSingletonColumn.graph_mem M a ZFSet.omega hM hT ha hω)
    (InternalSingletonColumn.graph_function a ZFSet.omega)
    (InternalSingletonColumn.graph_injective a ZFSet.omega)
    (InternalSingletonColumn.graph_onto a ZFSet.omega)
  refine ⟨e,_,hf,he,fun p n b => ?_⟩
  have hn : natSet n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  have hm := ((InternalCohenReindex.pair_reindexGraph B ZFSet.omega
    (InternalSingletonColumn.graph a ZFSet.omega) _ _).mp ((he p (e p)).mpr rfl)).2.2
  exact (hm _ (ZFSet.pair_mem_prod.mpr ⟨ZFSet.mem_singleton.mpr rfl,hn⟩) _ hn
    ((InternalSingletonColumn.pair_graph a ZFSet.omega _ _).mpr ⟨hn,rfl⟩)
    (bitSet b) ((mem_alphabet _).mpr ⟨b,rfl⟩)).symm

theorem selected_real_prefix_generic (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (A : Oracle) (hv : (realName K a).val G.carrier = realCode A) :
    AtomicForcing.GroundGeneric M (InternalCohen.pushFilter (CohenBorelForcing.realFilter A)) := by
  let C := ZFSet.prod K ZFSet.omega
  let B := ZFSet.prod {a} ZFSet.omega
  let hBC := singleton_coordinates_subset K a ha
  let H := projected C B hBC G
  have haM := hM K hK a ha
  have hsingle := singleton_mem M hM hT.pairing haM
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  have hH := projected_groundGeneric M C B hM hT hC hB hBC G hG
  obtain ⟨AH,hvH,hbits,_⟩ := generic_real_value M {a} a hM hT hsingle
    (ZFSet.mem_singleton.mpr rfl) H hH
  obtain ⟨AG,hvGH,hvG,_,_⟩ := projected_real_value M K a hM hT hK ha G hG
  have hAG : AG = A := realCode_injective (hvG.symm.trans hv)
  have hAH : AH = AG := realCode_injective (hvH.symm.trans hvGH)
  subst AG; subst AH
  obtain ⟨e,f,hf,he,hbit⟩ := singleton_iso_bits M a hM hT haM
  let L := mapFilter e H
  have hL := InternalOrderIsoTransport.map_ground_generic M (poset {a}) SparseCohenRealName.poset f
    hM hT (conditions_mem M B hM hT hB)
    (conditions_mem M ZFSet.omega hM hT (sourceT_omega_mem M hM hT)) hf e he H hH
  apply SparseCohenRealName.prefix_ground_generic M hM hT L hL A
  intro n b
  rw [←hbits n b,InternalCollapse.mem_unionGraph,InternalCollapse.mem_unionGraph]
  constructor
  · rintro ⟨p,hp,hpb⟩
    refine ⟨e.symm p,hp,?_⟩
    exact (hbit (e.symm p) n b).mp (by simpa only [e.apply_symm_apply] using hpb)
  · rintro ⟨p,hp,hpb⟩
    exact ⟨e p,by simpa only [L,mapFilter,Set.mem_ofPred_eq,e.symm_apply_apply] using hp,
      (hbit p n b).mpr hpb⟩

end TuringRigidity.CohenColumnRealName

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenFiniteFlip
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.CohenFiniteFlip
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCollapse
open CohenGroundPoset InternalCohenBitFlip
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem pair_mem_prefixMask (a : ZFSet.{0}) (s : List Bool) (A : Oracle) (n : ℕ) :
    ZFSet.pair a (natSet n) ∈ prefixMask a s A ↔
      n < s.length ∧ A n ≠ s.getD n false := by
  classical
  rw [prefixMask,ZFSet.mem_range]
  constructor
  · rintro ⟨⟨i,hi⟩,he⟩
    have he' : i.val = n := natSet_injective (ZFSet.pair_inj.mp he).2
    subst n
    exact ⟨i.isLt,by simpa [List.getD,i.isLt] using hi⟩
  · rintro ⟨hn,hd⟩
    exact ⟨⟨⟨n,hn⟩,by simpa [List.getD,hn] using hd⟩,rfl⟩

theorem prefixMask_mem (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (s : List Bool) (A : Oracle) : prefixMask a s A ∈ M := by
  classical
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  apply InternalFiniteSubsets.finite_subset_mem M (ZFSet.prod K ZFSet.omega) _ hM hT hC
  apply (InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mpr
  constructor
  · intro x hx
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp hx
    exact ZFSet.pair_mem_prod.mpr ⟨ha,(mem_omega _).mpr ⟨i.val.val,rfl⟩⟩
  · rw [prefixMask,ZFSet.coe_range]
    exact Set.finite_range _

theorem pair_mem_flip_label (C B : ZFSet.{0}) (p : Conditions (conditions C))
    (x : ZFSet.{0}) (hx : x ∈ C) (b : Bool) :
    ZFSet.pair x (bitSet b) ∈ label _ (flipIso C B p) ↔
      (x ∈ B ∧ ZFSet.pair x (bitSet (!b)) ∈ label _ p) ∨
      (x ∉ B ∧ ZFSet.pair x (bitSet b) ∈ label _ p) := by
  have h := ((pair_flipGraph C B _ _).mp ((flipGraph_spec C B p _).mpr rfl)).2.2 x hx
  cases b
  · exact h.1
  · exact h.2

theorem pair_mem_flip_union (C B : ZFSet.{0}) (G : GenericFilter (Conditions (conditions C)))
    (x : ZFSet.{0}) (hx : x ∈ C) (b : Bool) :
    ZFSet.pair x (bitSet b) ∈ unionGraph (AutomorphismName.mapFilter (flipIso C B) G) ↔
      (x ∈ B ∧ ZFSet.pair x (bitSet (!b)) ∈ unionGraph G) ∨
      (x ∉ B ∧ ZFSet.pair x (bitSet b) ∈ unionGraph G) := by
  constructor
  · intro h
    obtain ⟨q,hq,hbit⟩ := (InternalCollapse.mem_unionGraph _ _).mp h
    let p := (flipIso C B).symm q
    have hq' : q = flipIso C B p := (flipIso C B).apply_symm_apply q |>.symm
    rw [hq',pair_mem_flip_label C B p x hx b] at hbit
    rcases hbit with ⟨hB,hbit⟩ | ⟨hB,hbit⟩
    · exact Or.inl ⟨hB,(InternalCollapse.mem_unionGraph _ _).mpr ⟨p,hq,hbit⟩⟩
    · exact Or.inr ⟨hB,(InternalCollapse.mem_unionGraph _ _).mpr ⟨p,hq,hbit⟩⟩
  · intro h
    rcases h with ⟨hB,hbit⟩ | ⟨hB,hbit⟩
    · obtain ⟨p,hp,hbit⟩ := (InternalCollapse.mem_unionGraph _ _).mp hbit
      exact (InternalCollapse.mem_unionGraph _ _).mpr ⟨flipIso C B p,by simpa [AutomorphismName.mapFilter] using hp,
        (pair_mem_flip_label C B p x hx b).mpr (Or.inl ⟨hB,hbit⟩)⟩
    · obtain ⟨p,hp,hbit⟩ := (InternalCollapse.mem_unionGraph _ _).mp hbit
      exact (InternalCollapse.mem_unionGraph _ _).mpr ⟨flipIso C B p,by simpa [AutomorphismName.mapFilter] using hp,
        (pair_mem_flip_label C B p x hx b).mpr (Or.inr ⟨hB,hbit⟩)⟩

end TuringRigidity.CohenFiniteFlip

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformOracleSimulation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformPrograms
variable {X Z : Type*} {O F H : X → ℕ →. ℕ}

theorem Runs.simulate (h : Runs O F) (p : OracleCode) :
    Runs O (fun x => OracleCode.eval (F x) p) := by
  induction p with
  | zero => exact primrec (Primrec.const 0)
  | succ => exact primrec Primrec.succ
  | left => exact primrec (Primrec.fst.comp Primrec.unpair)
  | right => exact primrec (Primrec.snd.comp Primrec.unpair)
  | query => exact h
  | pair p q hp hq => exact hp.pair hq
  | comp p q hp hq => exact hp.comp hq
  | prec p q hp hq => exact hp.prec hq
  | find p hp => exact hp.find

end TuringRigidity.UniformPrograms

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformJumpSimulation
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformPrograms
open Encodable CommonIdeal TableIndices IndexMatrix OracleJump
noncomputable section
variable {X : Type*}

theorem run_program (Y : X → Oracle) :
    Runs (fun x => oracleFunction (Y x)) (fun x v => Part.some
      (encode (run (Y x) (machine (Nat.unpair v).1)
        (Nat.unpair (Nat.unpair v).2).1 (Nat.unpair (Nat.unpair v).2).2))) := by
  let O := fun x => oracleFunction (Y x)
  let e := Primrec.fst.comp Primrec.unpair
  let rest := Primrec.snd.comp Primrec.unpair
  let n := Primrec.fst.comp (Primrec.unpair.comp rest)
  let z := Primrec.snd.comp (Primrec.unpair.comp rest)
  have he := primrec (O := O) e
  have hn := primrec (O := O) n
  have hm := primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp z))
  have ht := primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp z))
  have hL := total_comp (initial_program (fun x k => bit (Y x k)) query) hm
  let r := Primrec.snd.comp Primrec.unpair
  have hdecode := primrec (O := O) (Primrec.encode.comp (Nat.Partrec.Code.primrec_evaln.comp
    (((Primrec.fst.comp Primrec.unpair).pair
      (machine_primrec.comp (Primrec.fst.comp (Primrec.unpair.comp r)))).pair
      (Primrec.snd.comp (Primrec.unpair.comp r)))))
  exact (total_comp hdecode (total_pair ht (total_pair he (total_pair hL hn)))).of_eq
    (fun x v => by simp [TableIndices.run,UniformOracle.trial])

end
end TuringRigidity.UniformPrograms

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformTableSimulation
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.UniformPrograms
open Encodable CommonIdeal TableIndices IndexMatrix

theorem table_program (d : ℕ) :
    ∃ p : OracleCode, ∀ Y A : Oracle, Represents Y (machine d) A →
      OracleCode.eval (oracleFunction Y) p = oracleFunction A := by
  let X := {s : Oracle × Oracle // Represents s.1 (machine d) s.2}
  let Y := fun s : X => s.val.1
  have hr := total_comp (run_program Y) (primrec
    (Primrec₂.natPair.comp (Primrec.const d) Primrec.id))
  have hr' : Runs (fun s : X => oracleFunction (Y s)) (fun s v =>
      Part.some (encode (TableIndices.run s.val.1 (machine d) (Nat.unpair v).1 (Nat.unpair v).2))) := by
    simpa only [Nat.unpair_pair,Y,id_eq] using hr
  have hs : Runs (fun s => oracleFunction (Y s)) (fun s n => Part.some (bit (s.val.2 n))) :=
    UniformPrograms.total_search hr' (fun (s : X) n => bit (s.val.2 n))
      (fun (s : X) => s.property.1) (fun (s : X) => s.property.2)
  obtain ⟨p,hp⟩ := hs
  exact ⟨p,fun B A h => hp ⟨(B,A),h⟩⟩

theorem program_table (p : OracleCode) :
    ∃ d : ℕ, ∀ Y A : Oracle, OracleCode.eval (oracleFunction Y) p = oracleFunction A →
      Represents Y (machine d) A := by
  have hf : Partrec₂ (fun L : List ℕ => fun n => OracleCode.eval (BranchMachine.lookup L) p n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec p
  obtain ⟨d,hd⟩ := partrec_code hf
  have hd' : ∀ L n, d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) p n :=
    fun L n => hd (L,n)
  refine ⟨encode d,fun Y A he => ?_⟩
  have ha (n : ℕ) : Approximates (oracleFunction A n)
      (fun m => d.eval (Nat.pair (encode (UniformOracle.oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd']
    rw [← he]
    exact OracleCode.eval_approximates (UniformOracle.prefix_approximates (fun k => bit (Y k))) p n
  rw [machine_encode]
  constructor
  · intro n z a hz
    exact Part.mem_some_iff.mp ((ha n).1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound hz))
  · intro n
    obtain ⟨m,hm⟩ := (ha n).2 (bit (A n)) (Part.mem_some _)
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t,bit (A n),by simpa [TableIndices.run,UniformOracle.trial] using ht⟩

theorem Runs.table_simulation {X : Type*} {Y Z : X → Oracle}
    (h : Runs (fun x => oracleFunction (Z x)) (fun x => oracleFunction (Y x))) (d : ℕ) :
    ∃ e : ℕ, ∀ x : X, ∀ A : Oracle, Represents (Y x) (machine d) A →
      Represents (Z x) (machine e) A := by
  obtain ⟨p,hp⟩ := table_program d
  obtain ⟨q,hq⟩ := h.simulate p
  obtain ⟨e,he⟩ := program_table q
  exact ⟨e,fun x A hA => he (Z x) A ((hq x).trans (hp (Y x) A hA))⟩

end TuringRigidity.UniformPrograms

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGroundProgram
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CountableForcing OracleJump
open TableIndices IndexMatrix UniformPrograms
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem selected_column_table_simulation (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (R : Oracle) (hR : realCode R ∈ M) (k d : ℕ) :
    ∃ e : ℕ, ∀ G : GenericFilter (Conditions (CohenColumnRealName.poset K)),
      AtomicForcing.GroundGeneric M G → ∀ A : Oracle,
      (CohenColumnRealName.realName K a).val G.carrier = realCode A →
      ∀ X : Oracle, Represents (iterate (join A R) k) (machine d) X →
        Represents (join A (iterate R k)) (machine e) X := by
  obtain ⟨e,he⟩ := groundGeneric_table_simulation M hM hT R hR k d
  exact ⟨e,fun G hG A hv => he A
    (CohenColumnRealName.selected_real_prefix_generic M K a hM hT hK ha G hG A hv)⟩

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

theorem overwrite_join_program (s : List Bool) (R : Oracle) :
    Runs (fun A => oracleFunction (join A R))
      (fun A => oracleFunction (join (overwrite s A) R)) := by
  have hp : Primrec (fun z : ℕ =>
      if (Nat.unpair z).1.bodd = false ∧ (Nat.unpair z).1 / 2 < s.length then
        (if s.getD ((Nat.unpair z).1 / 2) false then 1 else 0) else (Nat.unpair z).2) :=
    Primrec.ite
      ((Primrec.eq.comp (Primrec.nat_bodd.comp (Primrec.fst.comp Primrec.unpair))
        (Primrec.const false)).and
        (Primrec.nat_lt.comp (Primrec.nat_div.comp (Primrec.fst.comp Primrec.unpair)
          (Primrec.const 2)) (Primrec.const s.length)))
      (Primrec.ite (Primrec.eq.comp ((Primrec.list_getD false).comp (Primrec.const s)
        (Primrec.nat_div.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 2))) (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0))
      (Primrec.snd.comp Primrec.unpair)
  have hq : Runs (fun A => oracleFunction (join A R))
      (fun A n => Part.some (if join A R n then 1 else 0)) := query
  apply (_root_.OAI.TuringRigidity.UniformPrograms.total_comp (primrec hp) (_root_.OAI.TuringRigidity.UniformPrograms.total_pair (primrec Primrec.id) hq)).of_eq
  intro A n
  cases hb : n.bodd <;> by_cases hn : n / 2 < s.length <;>
    simp [oracleFunction,join,overwrite,hb,hn]

end TuringRigidity.FiniteOverwrite

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenPrefixOverwrite
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.CohenFiniteFlip
open TransitiveNameModel BoundedSetTheory CountableForcing InternalCollapse
open CohenGroundPoset InternalCohenBitFlip CohenColumnRealName FiniteOverwrite
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem prefixFilter_value (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (s : List Bool) (A : Oracle)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (hv : (realName K a).val G.carrier = realCode A) :
    (realName K a).val (prefixFilter K a s A G).carrier = realCode (overwrite s A) := by
  obtain ⟨B,hB,hbits,_⟩ := generic_real_value M K a hM hT hK ha G hG
  have hBA : B = A := realCode_injective (hB.symm.trans hv)
  subst B
  apply val_realName K a _ (overwrite s A)
  intro n b
  rw [prefixFilter,pair_mem_flip_union _ _ G _
    (ZFSet.pair_mem_prod.mpr ⟨ha,(mem_omega _).mpr ⟨n,rfl⟩⟩) b,
    pair_mem_prefixMask,hbits n (!b),hbits n b]
  by_cases hn : n < s.length <;> cases hA : A n <;>
    cases hs : s.getD n false <;> cases b <;> simp only [overwrite,hn,hA,hs] <;> decide

theorem prefixFilter_properties (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K) (s : List Bool) (A : Oracle)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (hv : (realName K a).val G.carrier = realCode A) :
    AtomicForcing.GroundGeneric M (prefixFilter K a s A G) ∧
      genericExtensionSet M (poset K) (prefixFilter K a s A G).carrier =
        genericExtensionSet M (poset K) G.carrier ∧
      (realName K a).val (prefixFilter K a s A G).carrier = realCode (overwrite s A) := by
  let C := ZFSet.prod K ZFSet.omega
  let B := prefixMask a s A
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hc := (manyColumn_internal M K hM hT hK).1
  have hf := flipGraph_mem M C B hM hT hC (prefixMask_mem M K a hM hT hK ha s A)
  exact ⟨InternalOrderIsoTransport.map_ground_generic M (poset K) (poset K) (flipGraph C B)
      hM hT hc hc hf (flipIso C B) (flipGraph_spec C B) G hG,
    InternalOrderIsoTransport.extension_eq M (poset K) (poset K) (flipGraph C B)
      hM hT hc hc hf (flipIso C B) (flipGraph_spec C B) G hG,
    prefixFilter_value M K a hM hT hK ha s A G hG hv⟩

end TuringRigidity.CohenFiniteFlip

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleGroundReals
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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

theorem realCode_mem_groundReals (M : ZFSet.{u}) (A : Oracle) :
    realCode A ∈ groundReals M ↔ A ∈ modelReals M := by
  rw [mem_groundReals]
  exact and_iff_left (realCode_subset A)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryModelIdeal
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse SetDegreeDecoding PersistentRestrictions OracleJump
universe u

theorem modelIdeal_mem (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (b : Degree) : b ∈ (modelIdeal M hM hT).carrier ↔ ∃ A ∈ modelReals M, degree A = b := Iff.rfl

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SelectedColumnArithmeticCone
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenProjectedGeneric InternalCohenFactor
open OracleJump TableIndices IndexMatrix PersistentRestrictions SetDegreeDecoding
open ElementaryModel FullSetForcing CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder CohenNiceNameConstruction.cohenTop

theorem selected_column_arithmetic_cone (M K a : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : SentenceForm)
    (I : CountableIdeal) (ρ : I ≃o I)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (R : Oracle) (hRM : realCode R ∈ M)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
    (f : Name (Conditions (poset K))) (hf : f.encode (label (poset K)) ∈ M)
    (hfv : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (poset K) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (hOwn : OwnDegreeExtension (genericExtensionSet M (poset K) G.carrier)
      (idealSet I) (automorphismSet ρ) (f.val G.carrier))
    (p₀ : Conditions (poset K)) (hp₀ : p₀ ∈ G.carrier) :
    let C := ZFSet.prod K ZFSet.omega
    let B := ZFSet.prod {a} ZFSet.omega
    let hBC := singleton_coordinates_subset K a ha
    ∃ d : ℕ, ∃ p ∈ G.carrier, p ≤ p₀ ∧
      ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
        project C B hBC p ∈ (projected C B hBC H).carrier →
        ∃ A X : Oracle, (realName K a).val H.carrier = realCode A ∧
          (∀ n b, ZFSet.pair (ZFSet.pair a (natSet n)) (InternalCohen.bitSet b) ∈
            InternalCollapse.unionGraph H ↔ A n = b) ∧
          Represents (iterate (join A R) 5) (machine d) X ∧
          ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
          ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
            realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f.val H.carrier := by
  intro C B hBC
  have hsingle := singleton_mem M hM hT.pairing (hM K hK a ha)
  have hC := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT)
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hsingle (sourceT_omega_mem M hM hT)
  obtain ⟨A,hτv,_,_,_⟩ := projected_real_value M K a hM hT hK ha G hG
  obtain ⟨x,y,_,_,_,hxv,d,p,hp,hp₀',hcone⟩ :=
    projected_arithmetic_output_cone M C B hM hT hC hB hBC δ Z φ I ρ hz R hRM hR
      f hf hfv G hG hOwn (realName {a} a)
      (realName_internal M {a} a hM hT hsingle (ZFSet.mem_singleton.mpr rfl))
      A hτv p₀ hp₀
  refine ⟨d,p,hp,hp₀',fun H hH hpH => ?_⟩
  obtain ⟨A',X,hx,_,hrep,hout⟩ := hcone H hH hpH
  obtain ⟨AH,hτH,hfull,hbits,_⟩ := projected_real_value M K a hM hT hK ha H hH
  have he : A' = AH := realCode_injective
    (hx.symm.trans ((hxv H hH (hτH.symm ▸ realCode_subset AH)).trans hτH))
  subst A'
  exact ⟨AH,X,hfull,hbits,hrep,hout⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SelectedColumnPrefixProgram
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open RelativeConstructible CohenGroundPoset InternalCohenProjectedGeneric InternalCohenFactor
open OracleJump TableIndices IndexMatrix PersistentRestrictions SetDegreeDecoding
open ElementaryModel FullSetForcing CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem selected_column_prefix_program (M K a : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : SentenceForm)
    (I : CountableIdeal) (ρ : I ≃o I)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (R : Oracle) (hRM : realCode R ∈ M)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
    (f : Name (Conditions (poset K))) (hf : f.encode (label (poset K)) ∈ M)
    (hfv : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (poset K) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (hOwn : OwnDegreeExtension (genericExtensionSet M (poset K) G.carrier)
      (idealSet I) (automorphismSet ρ) (f.val G.carrier))
    : ∃ A₀ : Oracle, ∃ d N : ℕ,
      (realName K a).val G.carrier = realCode A₀ ∧
      ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
        ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
          (∀ n < N, A n = A₀ n) → ∃ X : Oracle,
          Represents (iterate (join A R) 5) (machine d) X ∧
          ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
          ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
            realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f.val H.carrier := by
  obtain ⟨d,p,hp,_,hcone⟩ := selected_column_arithmetic_cone M K a hM hT hK ha
    δ Z φ I ρ hz R hRM hR f hf hfv G hG hOwn ⊤ (G.upper le_top G.nonempty.choose_spec)
  obtain ⟨A₀,hA₀,N,hprefix⟩ := selected_prefix_cone M K a hM hT hK ha G hG p hp
  refine ⟨A₀,d,N,hA₀,fun H hH A hA hearly => ?_⟩
  obtain ⟨AH,X,hAH,_,hrep,hout⟩ := hcone H hH (hprefix H hH A hA hearly)
  have he : AH = A := realCode_injective (hAH.symm.trans hA)
  subst AH
  exact ⟨X,hrep,hout⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedColumnPrefixProgram
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing
open CohenGroundPoset InternalCountableOrdinals ElementaryModel SetDegreeDecoding PersistentRestrictions
open FullSetForcing CohenColumnRealName OracleJump TableIndices IndexMatrix
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem prescribed_column_prefix_program (π : Degree ≃o Degree)
    (M K a : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (ha : a ∈ K)
    (himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    let c := poset K
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT (manyColumn_internal M K hM hT hK.2.1).1
      (manyColumn_internal M K hM hT hK.2.1).2 (InternalCollapse.orderSet_pair c)
        G hG (G.upper le_top G.nonempty.choose_spec)
    let I := modelIdeal M hM hT
    let J := modelIdeal E hE hTE
    ∃ (δ : Ordinal.{0}) (P : Oracle) (φ : SentenceForm) (R : Oracle),
      δ.toZFSet ∈ M ∧ φ.bound ≤ 2 ∧ P ∈ modelReals E ∧
      realCode R ∈ M ∧ degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
      let N := RealGeneratedModel.hull M (realCode P)
      RealGeneratedModel.Contains M (realCode P) N ∧ (N : Set ZFSet.{0}).Countable ∧
        ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
          (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
            fX.val H.carrier = definedSubset
              (level (groundReals (genericExtensionSet N c H.carrier)) δ)
                φ (fun _ : Fin φ.bound => realCode P) ∧
            OwnDegreeExtension (genericExtensionSet N c H.carrier)
              (idealSet I) (automorphismSet ρ) (fX.val H.carrier)) ∧
          ∃ GX : GenericFilter (Conditions c), GroundGeneric N GX ∧
            genericExtensionSet N c GX.carrier = E ∧
            (∃ σ : J ≃o J, RestrictsTo π J σ ∧ fX.val GX.carrier = automorphismSet σ) ∧
            ∃ A₀ : Oracle, ∃ d ℓ : ℕ,
              (realName K a).val GX.carrier = realCode A₀ ∧
              ∀ H : GenericFilter (Conditions c), GroundGeneric N H →
                ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
                  (∀ n < ℓ, A n = A₀ n) → ∃ X : Oracle,
                    Represents (iterate (join A R) 5) (machine d) X ∧
                    ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet N c H.carrier)),
                    ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet N c H.carrier)),
                      realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ fX.val H.carrier := by
  intro c E hE hTE I J
  have hz : degree (jump FixedArithmetic.zero) ∈ I.carrier :=
    ⟨jump FixedArithmetic.zero,sourceT_real_jump M hM hT (sourceT_zero_real M hM hT),rfl⟩
  obtain ⟨R,hRM,hR⟩ := (modelIdeal_mem M hM hT _).mp (ρ.symm ⟨_,hz⟩).property
  have hRglobal : degree R = π.symm (degree (jump FixedArithmetic.zero)) := by
    apply π.injective
    rw [hR,π.apply_symm_apply]
    simpa only [ρ.apply_symm_apply] using hρ (ρ.symm ⟨_,hz⟩)
  obtain ⟨δ,P,φ,hδ,hφ,hP,hN,hNct,fX,hfX,hall,GX,hGX,hExt,σ,hσ,hval⟩ :=
    prescribed_real_hull_extension π M K hM hT hK himages ρ hρ G hG
  let N := RealGeneratedModel.hull M (realCode P)
  let : Countable (N : Set ZFSet.{0}) := hNct.to_subtype
  let : Countable (Conditions N) := Function.Injective.countable
    (f := fun p : Conditions N => (⟨label N p,label_mem N p⟩ : (N : Set ZFSet.{0})))
    (fun x y he => label_injective N (congrArg (fun z : (N : Set ZFSet.{0}) => z.val) he))
  obtain ⟨A₀,d,ℓ,hA₀,hprog⟩ := selected_column_prefix_program N K a hN.1 hN.2.1
    (hN.2.2.1 hK.2.1) ha δ (realCode P) φ I ρ hz R (hN.2.2.1 hRM) hR
    fX hfX (fun H hH => (hall H hH).1) GX hGX (hall GX hGX).2
  exact ⟨δ,P,φ,R,hδ,hφ,hP,hRM,hRglobal,hN,hNct,fX,hfX,hall,GX,hGX,hExt,
    ⟨σ,hσ,hval⟩,A₀,d,ℓ,hA₀,hprog⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedGroundOracleProgram
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing
open CohenGroundPoset InternalCountableOrdinals ElementaryModel SetDegreeDecoding PersistentRestrictions
open FullSetForcing CohenColumnRealName OracleJump TableIndices IndexMatrix
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem prescribed_ground_oracle_program (π : Degree ≃o Degree)
    (M K a : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (ha : a ∈ K)
    (himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    let c := poset K
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT (manyColumn_internal M K hM hT hK.2.1).1
      (manyColumn_internal M K hM hT hK.2.1).2 (InternalCollapse.orderSet_pair c)
        G hG (G.upper le_top G.nonempty.choose_spec)
    let I := modelIdeal M hM hT
    let J := modelIdeal E hE hTE
    ∃ (δ : Ordinal.{0}) (P : Oracle) (φ : SentenceForm) (R : Oracle),
      δ.toZFSet ∈ M ∧ φ.bound ≤ 2 ∧ P ∈ modelReals E ∧
      realCode R ∈ M ∧ degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
      let N := RealGeneratedModel.hull M (realCode P)
      RealGeneratedModel.Contains M (realCode P) N ∧ (N : Set ZFSet.{0}).Countable ∧
        ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
          (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
            fX.val H.carrier = definedSubset
              (level (groundReals (genericExtensionSet N c H.carrier)) δ)
                φ (fun _ : Fin φ.bound => realCode P) ∧
            OwnDegreeExtension (genericExtensionSet N c H.carrier)
              (idealSet I) (automorphismSet ρ) (fX.val H.carrier)) ∧
          ∃ GX : GenericFilter (Conditions c), GroundGeneric N GX ∧
            genericExtensionSet N c GX.carrier = E ∧
            (∃ σ : J ≃o J, RestrictsTo π J σ ∧ fX.val GX.carrier = automorphismSet σ) ∧
            ∃ A₀ : Oracle, ∃ d ℓ : ℕ,
              (realName K a).val GX.carrier = realCode A₀ ∧
              ∀ H : GenericFilter (Conditions c), GroundGeneric N H →
                ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
                  (∀ n < ℓ, A n = A₀ n) → ∃ X : Oracle,
                    Represents (join A (iterate R 5)) (machine d) X ∧
                    ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet N c H.carrier)),
                    ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet N c H.carrier)),
                      realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ fX.val H.carrier := by
  intro c E hE hTE I J
  obtain ⟨δ,P,φ,R,hδ,hφ,hP,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,d,ℓ,hA₀,hprog⟩ :=
    prescribed_column_prefix_program π M K a hM hT hK ha himages ρ hρ G hG
  let N := RealGeneratedModel.hull M (realCode P)
  obtain ⟨e,he⟩ := InternalCohen.selected_column_table_simulation N K a hN.1 hN.2.1
    (hN.2.2.1 hK.2.1) ha R (hN.2.2.1 hRM) 5 d
  refine ⟨δ,P,φ,R,hδ,hφ,hP,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,e,ℓ,hA₀,?_⟩
  intro H hH A hv hprefix
  obtain ⟨X,hX,hrel⟩ := hprog H hH A hv hprefix
  exact ⟨X,he H hH A hv X hX,hrel⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_DefinedPrefixRemoval
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
open CohenGroundPoset CohenColumnRealName CohenFiniteFlip FiniteOverwrite
open TableIndices IndexMatrix
open ElementaryModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem equidegree_mem_ownDegree (E u : ZFSet.{0}) (hE : Transitive E) (hT : SourceT E)
    (hu : u ∈ degreeUniverse (groundReals E)) (A B : Oracle)
    (hB : realCode B ∈ u) (he : degree A = degree B) : realCode A ∈ u := by
  obtain ⟨C,hC,rfl⟩ := (mem_degreeUniverse _ _).mp hu
  have hmem := actual_degreeCode_membership E hE hT (groundReals E)
    (realCode_mem_groundReals E) ((realCode_mem_groundReals E C).mp hC)
  exact (hmem A).mpr (he.trans ((hmem B).mp hB))

theorem defined_value_extension_eq (M c : ZFSet.{0}) (δ : Ordinal.{0})
    (Z : ZFSet.{0}) (φ : SentenceForm) (f : Name (Conditions c))
    (hfv : ∀ H : GenericFilter (Conditions c), GroundGeneric M H →
      f.val H.carrier = definedSubset (level (groundReals (genericExtensionSet M c H.carrier)) δ)
        φ (fun _ : Fin φ.bound => Z))
    (G H : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (hH : GroundGeneric M H)
    (he : genericExtensionSet M c G.carrier = genericExtensionSet M c H.carrier) :
    f.val G.carrier = f.val H.carrier := by
  rw [hfv G hG,hfv H hH,he]

theorem remove_defined_program_prefix (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : SentenceForm)
    (f : Name (Conditions (poset K)))
    (hfv : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (poset K) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (R A₀ : Oracle) (d ℓ : ℕ)
    (hprog : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
        (∀ n < ℓ, A n = A₀ n) → ∃ X : Oracle,
          Represents (join A R) (machine d) X ∧
          ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
          ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
            realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f.val H.carrier) :
    ∃ e : ℕ, ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → ∃ X : Oracle,
        Represents (join A R) (machine e) X ∧
        ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
        ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet M (poset K) H.carrier)),
          realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f.val H.carrier := by
  let s := FiniteShuffle.initial A₀ ℓ
  obtain ⟨e,he⟩ := (overwrite_join_program s R).table_simulation d
  refine ⟨e,fun H hH A hv => ?_⟩
  let Hs := prefixFilter K a s A H
  obtain ⟨hHs,hExt,hval⟩ := prefixFilter_properties M K a hM hT hK ha s A H hH hv
  have hprefix : ∀ n < ℓ, overwrite s A n = A₀ n := by
    intro n hn
    rw [overwrite_below _ _ _ (by simpa [s] using hn),FiniteShuffle.prefix_getD _ _ _ hn]
  obtain ⟨X,hX,u,hu,v,hv',hAu,hXv,hpair⟩ := hprog Hs hHs (overwrite s A) hval hprefix
  have hfEq := defined_value_extension_eq M (poset K) δ Z φ f hfv Hs H hHs hH hExt
  rw [hExt] at hu hv'
  rw [hfEq] at hpair
  obtain ⟨hE,hTE,_,_⟩ := RegularTreeExtension.extension_properties M (poset K) hM hT
    (manyColumn_internal M K hM hT hK).1 H hH
  exact ⟨X,he A X hX,u,hu,v,hv',
    equidegree_mem_ownDegree _ u hE hTE hu A (overwrite s A) hAu
      (degree_overwrite s A).symm,hXv,hpair⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedUnrestrictedGroundProgram
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing
open CohenGroundPoset InternalCountableOrdinals ElementaryModel SetDegreeDecoding PersistentRestrictions
open FullSetForcing CohenColumnRealName OracleJump TableIndices IndexMatrix
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem prescribed_unrestricted_ground_program_oai (π : Degree ≃o Degree)
    (M K a : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (ha : a ∈ K)
    (himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    let c := poset K
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT (manyColumn_internal M K hM hT hK.2.1).1
      (manyColumn_internal M K hM hT hK.2.1).2 (InternalCollapse.orderSet_pair c)
        G hG (G.upper le_top G.nonempty.choose_spec)
    let I := modelIdeal M hM hT
    let J := modelIdeal E hE hTE
    ∃ (δ : Ordinal.{0}) (P : Oracle) (φ : SentenceForm) (R : Oracle),
      δ.toZFSet ∈ M ∧ φ.bound ≤ 2 ∧ P ∈ modelReals E ∧
      realCode R ∈ M ∧ degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
      let N := RealGeneratedModel.hull M (realCode P)
      RealGeneratedModel.Contains M (realCode P) N ∧ (N : Set ZFSet.{0}).Countable ∧
        ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
          (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
            fX.val H.carrier = definedSubset
              (level (groundReals (genericExtensionSet N c H.carrier)) δ)
                φ (fun _ : Fin φ.bound => realCode P) ∧
            OwnDegreeExtension (genericExtensionSet N c H.carrier)
              (idealSet I) (automorphismSet ρ) (fX.val H.carrier)) ∧
          ∃ GX : GenericFilter (Conditions c), GroundGeneric N GX ∧
            genericExtensionSet N c GX.carrier = E ∧
            (∃ σ : J ≃o J, RestrictsTo π J σ ∧ fX.val GX.carrier = automorphismSet σ) ∧
            ∃ A₀ : Oracle, ∃ d : ℕ,
              (realName K a).val GX.carrier = realCode A₀ ∧
              ∀ H : GenericFilter (Conditions c), GroundGeneric N H →
                ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
                  ∃ X : Oracle,
                    Represents (join A (iterate R 5)) (machine d) X ∧
                    ∃ u ∈ degreeUniverse (groundReals (genericExtensionSet N c H.carrier)),
                    ∃ v ∈ degreeUniverse (groundReals (genericExtensionSet N c H.carrier)),
                      realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ fX.val H.carrier := by
  intro c E hE hTE I J
  obtain ⟨δ,P,φ,R,hδ,hφ,hP,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,d,ℓ,hA₀,hprog⟩ :=
    prescribed_ground_oracle_program π M K a hM hT hK ha himages ρ hρ G hG
  let N := RealGeneratedModel.hull M (realCode P)
  obtain ⟨e,he⟩ := remove_defined_program_prefix N K a hN.1 hN.2.1
    (hN.2.2.1 hK.2.1) ha δ (realCode P) φ fX (fun H hH => (hall H hH).1)
    (iterate R 5) A₀ d ℓ hprog
  exact ⟨δ,P,φ,R,hδ,hφ,hP,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,e,hA₀,he⟩

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RelativeConstructible.prescribed_unrestricted_ground_program_oai := @OAI.TuringRigidity.RelativeConstructible.prescribed_unrestricted_ground_program_oai
