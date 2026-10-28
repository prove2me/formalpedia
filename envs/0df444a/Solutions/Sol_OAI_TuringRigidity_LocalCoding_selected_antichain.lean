-- Prove2me | solution 1 for OAI.TuringRigidity.LocalCoding.selected_antichain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:05:23.895617+00:00
-- url     : https://prove2.me/submissions/bd73dd07-b657-4b86-833b-5742b789578c

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_PrefixComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PrefixComputability
open Encodable

variable {O : Set (ℕ →. ℕ)}

theorem total_pair {f g : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n)))
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun n => Part.some (Nat.pair (f n) (g n))) := by
  simpa [Seq.seq] using Nat.RecursiveIn.pair hf hg

theorem appendEncoded_primrec : Primrec₂ appendEncoded :=
  Primrec.encode.comp (Primrec.list_append.comp
    (Primrec.option_getD_default.comp (Primrec.decode.comp Primrec.fst))
    (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))

theorem prefix_recursive (g : ℕ → ℕ) :
    Nat.RecursiveIn {fun n => Part.some (g n)} (fun m => Part.some (encode (oraclePrefix g m))) := by
  have hquery : Nat.RecursiveIn {fun n => Part.some (g n)} (fun n => Part.some (g n)) :=
    .oracle _ (Set.mem_singleton _)
  have hy := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := (total_primrec (O := {fun n => Part.some (g n)})) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp ((total_primrec (O := {fun n => Part.some (g n)})) (appendEncoded_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hquery hy))
  have hp := Nat.RecursiveIn.prec ((total_primrec (O := {fun n => Part.some (g n)})) (Primrec.const (encode ([] : List ℕ)))) hs
  have hh := Nat.RecursiveIn.comp hp
    (total_pair ((total_primrec (O := {fun n => Part.some (g n)})) (Primrec.const 0)) ((total_primrec (O := {fun n => Part.some (g n)})) Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [appendEncoded, oraclePrefix, List.range_succ]

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

end TuringRigidity.PrefixComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_Introreducible
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix _root_.OAI.TuringRigidity.instOrderBotDegree _root_.OAI.TuringRigidity.instSemilatticeSupDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace Introreducible
open Encodable PrefixComputability

theorem prefixCode_injective (X : Oracle) : Function.Injective (prefixCode X) := by
  intro n m h
  simpa using congrArg codeLength h

theorem prefixSet_infinite (X : Oracle) : {c | prefixSet X c = true}.Infinite := by
  apply (Set.infinite_range_of_injective (prefixCode_injective X)).mono
  rintro _ ⟨n, rfl⟩
  exact prefixSet_prefix X n

theorem subset_unbounded {X Z : Oracle}
    (hsub : ∀ c, Z c = true → prefixSet X c = true)
    (hinf : {c | Z c = true}.Infinite) (n : ℕ) :
    ∃ c, Z c = true ∧ n < codeLength c := by
  by_contra h
  have hb : ∀ c, Z c = true → codeLength c ≤ n := by
    intro c hc
    by_contra hn
    exact h ⟨c, hc, Nat.lt_of_not_ge hn⟩
  apply hinf
  apply ((Set.finite_le_nat n).image (prefixCode X)).subset
  intro c hc
  have he := of_decide_eq_true (hsub c hc)
  exact ⟨codeLength c, hb c hc, he⟩

theorem codeList_primrec : Primrec codeList :=
  Primrec.option_getD_default.comp Primrec.decode

theorem codeLength_primrec : Primrec codeLength :=
  Primrec.list_length.comp codeList_primrec

private theorem equalBit_primrec : Primrec equalBit := by
  apply (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)) (Primrec.const 1) (Primrec.const 0)).of_eq
  intro n
  simp [equalBit]

theorem prefixSet_reduces (X : Oracle) : Reduces (prefixSet X) X := by
  apply RecursiveIn.iff_nat.mpr
  have hp := _root_.OAI.TuringRigidity.PrefixComputability.total_comp (prefix_recursive (bit X)) (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec codeLength_primrec)
  have he := _root_.OAI.TuringRigidity.PrefixComputability.total_comp (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec equalBit_primrec)
    (_root_.OAI.TuringRigidity.PrefixComputability.total_pair hp (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec Primrec.id))
  apply he.of_eq
  intro n
  by_cases h : encode (oraclePrefix (bit X) (codeLength n)) = n
  · simp [oracleFunction, prefixSet, equalBit, prefixCode, h]
  · simp [oracleFunction, prefixSet, equalBit, prefixCode, h]

theorem codeBit_primrec : Primrec₂ codeBit :=
  (Primrec.list_getD 0).comp (codeList_primrec.comp Primrec.snd) Primrec.fst

private theorem trialStep_primrec : Primrec trialStep := by
  let hn := Primrec.fst.comp Primrec.unpair
  let hc := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  let hb := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  apply (Primrec.encode.comp (Primrec.ite
    ((Primrec.eq.comp hb (Primrec.const 1)).and
      (Primrec.nat_lt.comp hn (codeLength_primrec.comp hc)))
    (Primrec.option_some.comp (codeBit_primrec.comp hn hc)) (Primrec.const none))).of_eq
  intro p
  simp [trialStep]

theorem trial_recursive (Z : Oracle) :
    Nat.RecursiveIn {oracleFunction Z}
      (fun p => Part.some (encode (trial Z (Nat.unpair p).1 (Nat.unpair p).2))) := by
  have hq : Nat.RecursiveIn {oracleFunction Z} (oracleFunction Z) :=
    .oracle _ (Set.mem_singleton _)
  have hn := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := {oracleFunction Z}) (Primrec.fst.comp Primrec.unpair)
  have hc := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := {oracleFunction Z}) (Primrec.snd.comp Primrec.unpair)
  have ht := _root_.OAI.TuringRigidity.PrefixComputability.total_comp (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec trialStep_primrec)
    (_root_.OAI.TuringRigidity.PrefixComputability.total_pair hn (_root_.OAI.TuringRigidity.PrefixComputability.total_pair hc (_root_.OAI.TuringRigidity.PrefixComputability.total_comp hq hc)))
  apply ht.of_eq
  intro p
  cases hz : Z (Nat.unpair p).2 <;> simp [trialStep, trial, hz]

theorem reduces_of_infinite_subset {X Z : Oracle}
    (hsub : ∀ c, Z c = true → prefixSet X c = true)
    (hinf : {c | Z c = true}.Infinite) : Reduces X Z := by
  apply RecursiveIn.iff_nat.mpr
  change Nat.RecursiveIn {oracleFunction Z} (fun n => Part.some (bit X n))
  apply total_search (trial_recursive Z) (bit X)
  · intro n c a ha
    simp only [trial] at ha
    split at ha
    next h =>
      have he : prefixCode X (codeLength c) = c := of_decide_eq_true (hsub c h.1)
      have ha' : a = codeBit n c := (Option.mem_some_iff.mp ha).symm
      rw [ha', ← he]
      exact codeBit_prefix X n (codeLength c) h.2
    next h => simp at ha
  · intro n
    obtain ⟨c, hc, hn⟩ := subset_unbounded hsub hinf n
    exact ⟨c, codeBit n c, by simp [trial, hc, hn]⟩

theorem prefixSet_degree (X : Oracle) : degree (prefixSet X) = degree X := by
  apply (degree_eq_iff _ _).mpr
  exact ⟨prefixSet_reduces X, reduces_of_infinite_subset (fun _ h => h)
    (prefixSet_infinite X)⟩

end Introreducible
end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingForcing
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingForcing

theorem arbitrary_left_extension (A : ℕ → Oracle) (p : Condition)
    (s : List Bool) (hs : p.left <+: s) :
    ∃ q, Extends A p q ∧ q.left = s := by
  obtain ⟨u, rfl⟩ := hs
  exact ⟨append p u, append_extends A p u, rfl⟩

end TuringRigidity.CodingForcing

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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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

end TuringRigidity.CommonIdeal

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

end TuringRigidity.TableIndices

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveCohen
open Encodable UniformOracle ArithmeticHierarchy OracleJump

theorem sigma1_enumeration {Y : Oracle} {P : ℕ → Prop} (h : Sigma Y 1 P) :
    ∃ e, ∀ n, P n ↔ Halts Y e n := by
  classical
  obtain ⟨Q,hQ,he⟩ := h
  have hf := Nat.RecursiveIn.rfind (recursive_not hQ)
  obtain ⟨e,hd⟩ := partial_table hf
  refine ⟨e,fun n => (he n).trans ?_⟩
  rw [hd n]
  erw [Nat.rfind_dom]
  simp [Quant]

end TuringRigidity.EffectiveCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleEnumeration
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleEnumeration
open PrefixComputability

theorem next_spec (A : Oracle) (hA : {n | A n = true}.Infinite) (n : ℕ) :
    n ≤ next A hA n ∧ A (next A hA n) = true := Nat.find_spec (exists_ge hA n)

private theorem searchFlag_primrec : Primrec searchFlag := by
  exact Primrec.ite ((Primrec.nat_le.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))).and
    (Primrec.eq.comp (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.const 1))) (Primrec.const 0) (Primrec.const 1)

theorem next_recursive (A : Oracle) (hA : {n | A n = true}.Infinite) :
    Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (next A hA n)) := by
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) :=
    .oracle _ (Set.mem_singleton _)
  have hn := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := {oracleFunction A}) (Primrec.fst.comp Primrec.unpair)
  have hm := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := {oracleFunction A}) (Primrec.snd.comp Primrec.unpair)
  have hf := _root_.OAI.TuringRigidity.PrefixComputability.total_comp (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec searchFlag_primrec)
    (_root_.OAI.TuringRigidity.PrefixComputability.total_pair hn (_root_.OAI.TuringRigidity.PrefixComputability.total_pair hm (_root_.OAI.TuringRigidity.PrefixComputability.total_comp hq hm)))
  apply (Nat.RecursiveIn.rfind hf).of_eq_tot
  intro n
  apply Nat.mem_rfind.mpr
  constructor
  · have hs := next_spec A hA n
    simp [searchFlag, hs.1, hs.2]
  · intro m hm'
    have hh : ¬(n ≤ m ∧ A m = true) := Nat.find_min (exists_ge hA n) hm'
    cases ha : A m <;> simp_all [searchFlag]

theorem enumerate_mem (A : Oracle) (hA : {n | A n = true}.Infinite) (n : ℕ) :
    A (enumerate A hA n) = true := by
  cases n <;> exact (next_spec A hA _).2

theorem enumerate_strictMono (A : Oracle) (hA : {n | A n = true}.Infinite) :
    StrictMono (enumerate A hA) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Nat.lt_succ_self _).trans_le (next_spec A hA _).1

theorem le_enumerate (A : Oracle) (hA : {n | A n = true}.Infinite) (n : ℕ) :
    n ≤ enumerate A hA n := (enumerate_strictMono A hA).id_le n

theorem enumerate_recursive (A : Oracle) (hA : {n | A n = true}.Infinite) :
    Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (enumerate A hA n)) := by
  have hnext := next_recursive A hA
  have hbase := _root_.OAI.TuringRigidity.PrefixComputability.total_comp hnext (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec (Primrec.const 0))
  have hstep := _root_.OAI.TuringRigidity.PrefixComputability.total_comp hnext (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec
    (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp Primrec.unpair)))))
  have hrec := Nat.RecursiveIn.prec hbase hstep
  have hr := Nat.RecursiveIn.comp hrec
    (_root_.OAI.TuringRigidity.PrefixComputability.total_pair (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec (Primrec.const 0)) (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec Primrec.id))
  apply hr.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [enumerate]

end TuringRigidity.OracleEnumeration

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingColumns
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingColumns
open PrefixComputability OracleEnumeration

private theorem columnStep_primrec (k cutoff : ℕ) : Primrec (columnStep k cutoff) :=
  Primrec.ite ((Primrec.nat_le.comp (Primrec.const cutoff) (Primrec.fst.comp Primrec.unpair)).and
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.const k))) (Primrec.snd.comp Primrec.unpair) (Primrec.const 0)

theorem column_reduces (A : Oracle) (k cutoff : ℕ) : Reduces (column A k cutoff) A := by
  apply RecursiveIn.iff_nat.mpr
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) :=
    .oracle _ (Set.mem_singleton _)
  have hm := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := {oracleFunction A}) Primrec.id
  have ha := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := {oracleFunction A}) (Primrec.snd.comp Primrec.unpair)
  have hh := _root_.OAI.TuringRigidity.PrefixComputability.total_comp (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec (columnStep_primrec k cutoff))
    (_root_.OAI.TuringRigidity.PrefixComputability.total_pair hm (_root_.OAI.TuringRigidity.PrefixComputability.total_comp hq ha))
  apply hh.of_eq
  intro m
  by_cases hc : cutoff ≤ m ∧ (Nat.unpair m).1 = k <;>
    simp [columnStep, column, oracleFunction, hc]

theorem location_mem (A : Oracle) (hA : {a | A a = true}.Infinite) (k cutoff n : ℕ) :
    column A k cutoff (location A hA k cutoff n) = true := enumerate_mem _ _ _

theorem le_location (A : Oracle) (hA : {a | A a = true}.Infinite) (k cutoff n : ℕ) :
    n ≤ location A hA k cutoff n := le_enumerate _ _ _

theorem location_recursive (A : Oracle) (hA : {a | A a = true}.Infinite) (k cutoff : ℕ) :
    Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (location A hA k cutoff n)) := by
  apply (enumerate_recursive (column A k cutoff) (column_infinite A hA k cutoff)).subst
  intro f hf
  have he : f = oracleFunction (column A k cutoff) := Set.mem_singleton_iff.mp hf
  subst f
  exact RecursiveIn.iff_nat.mp (column_reduces A k cutoff)

theorem readColumn_reduces (A : Oracle) (hA : {a | A a = true}.Infinite)
    (k cutoff : ℕ) (G : Oracle) : Reduces (readColumn A hA k cutoff G) (join G A) := by
  apply RecursiveIn.iff_nat.mpr
  have hloc := (location_recursive A hA k cutoff).subst (O' := {oracleFunction (join G A)})
    (fun f hf => by
      have he : f = oracleFunction A := Set.mem_singleton_iff.mp hf
      subst f
      exact RecursiveIn.iff_nat.mp (reduces_join_right G A))
  have hG := RecursiveIn.iff_nat.mp (reduces_join_left G A)
  exact _root_.OAI.TuringRigidity.PrefixComputability.total_comp hG hloc

end TuringRigidity.CodingColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingDiagonal
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingDiagonal
open CodingForcing CodingColumns Introreducible

theorem prescribe (A : ℕ → Oracle) (p : Condition) (m : ℕ)
    (hm : p.left.length ≤ m) (b : Bool) :
    ∃ q, Extends A p q ∧ m < q.left.length ∧ q.left.getD m false = b := by
  refine ⟨append p (List.replicate (m - p.left.length + 1) b), append_extends A p _, ?_, ?_⟩
  · simp only [append, List.length_append, List.length_replicate]
    omega
  · simp only [append, List.getD_eq_getElem?_getD, List.getElem?_append,
      ite_eq_right (Nat.not_lt.mpr hm)]
    simp

end TuringRigidity.CodingDiagonal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingAgreement
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingAgreement
open CodingForcing

theorem unique_search_sound {A : ℕ → Oracle} {Y G Z : Oracle} {e : OracleCode}
    {p : Condition} (hu : UniqueValues A Y e p) (hG : CommonIdeal.Extends G p.left)
    (he : OracleCode.eval (oracleFunction (join Y G)) e = oracleFunction Z)
    (w : List Bool) (n a : ℕ) (ha : a ∈ CommonIdeal.run Y e (p.left ++ w) n) :
    a = CommonIdeal.bit (Z n) := by
  obtain ⟨q, hpq, hq⟩ := arbitrary_left_extension A p (p.left ++ w) (List.prefix_append _ _)
  obtain ⟨s, hs, hb⟩ := CommonIdeal.run_finite_extension hG n (CommonIdeal.bit (Z n)) (by
    rw [he]
    exact Part.mem_some _)
  obtain ⟨r, hpr, hr⟩ := arbitrary_left_extension A p s hs
  exact hu q r hpq hpr n a (CommonIdeal.bit (Z n)) (hq ▸ ha) (hr ▸ hb)

theorem case1_reduces {A : ℕ → Oracle} {Y G Z : Oracle} {e : OracleCode} {p : Condition}
    (hu : UniqueValues A Y e p) (hG : CommonIdeal.Extends G p.left)
    (he : OracleCode.eval (oracleFunction (join Y G)) e = oracleFunction Z) : Reduces Z Y := by
  obtain ⟨d, hd⟩ := CommonIdeal.finiteRun_code e p.left
  apply RecursiveIn.iff_nat.mpr
  apply UniformOracle.total_search (CommonIdeal.searchTrial_recursive Y d) (fun n => CommonIdeal.bit (Z n))
  · intro n z a ha
    have hf := Nat.Partrec.Code.evaln_sound ha
    rw [hd] at hf
    have hr := (CommonIdeal.finiteRun_approximates Y e p.left
      (Nat.unpair (Nat.unpair z).2).1 n).1 (Nat.unpair z).1 a hf
    exact unique_search_sound hu hG he _ n a hr
  · intro n
    obtain ⟨w, a, ha⟩ := CommonIdeal.agreeing_search_complete hG he n
    obtain ⟨wcode, hw⟩ := BorelGeneric.word_surjective w
    rw [← hw] at ha
    obtain ⟨m, hm⟩ := (CommonIdeal.finiteRun_approximates Y e p.left wcode n).2 a ha
    have hf := hm m le_rfl
    dsimp only at hf
    rw [← hd] at hf
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hf
    exact ⟨Nat.pair m (Nat.pair wcode t), a, by simpa [CommonIdeal.searchTrial] using ht⟩

end TuringRigidity.CodingAgreement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingSplitSearch
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingSplitSearch
open Encodable PrefixComputability CodingLocations

theorem finiteTrial_primrec (d : Nat.Partrec.Code) (base : List Bool) : Primrec₂ (finiteTrial d base) := by
  let hL : Primrec (fun z : List ℕ × Witness => z.1) := Primrec.fst
  let hu : Primrec (fun z : List ℕ × Witness => z.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  let hi : Primrec (fun z : List ℕ × Witness => z.2.1.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  let hb : Primrec (fun z : List ℕ × Witness => z.2.1.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  let hn : Primrec (fun z : List ℕ × Witness => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let ht₀ : Primrec (fun z : List ℕ × Witness => z.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  let ht₁ : Primrec (fun z : List ℕ × Witness => z.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  let hu' := Primrec.list_set.comp hu (hi.pair hb)
  let ha₀ := Nat.Partrec.Code.primrec_evaln.comp
    ((ht₀.pair (Primrec.const d)).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp hL) (Primrec₂.natPair.comp (Primrec.encode.comp hu) hn)))
  let ha₁ := Nat.Partrec.Code.primrec_evaln.comp
    ((ht₁.pair (Primrec.const d)).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp hL) (Primrec₂.natPair.comp (Primrec.encode.comp hu') hn)))
  exact Primrec.ite ((Primrec.nat_lt.comp hi (Primrec.list_length.comp hu)).and
    (((Primrec.eq.comp ha₀ (Primrec.const none)).not).and
      (((Primrec.eq.comp ha₁ (Primrec.const none)).not).and
        (Primrec.eq.comp (Primrec.option_getD_default.comp ha₀)
          (Primrec.option_getD_default.comp ha₁)).not)))
    (Primrec.option_some.comp (Primrec.nat_add.comp (Primrec.const base.length) hi))
    (Primrec.const none)

theorem trial_recursive (Y : Oracle) (d : Nat.Partrec.Code) (base : List Bool) :
    Nat.RecursiveIn {oracleFunction Y} (fun z => Part.some (encode (trial Y d base z))) := by
  have hpre := _root_.OAI.TuringRigidity.PrefixComputability.total_comp (prefix_recursive (fun n => CommonIdeal.bit (Y n)))
    (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec (Primrec.fst.comp Primrec.unpair))
  have hw := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := {oracleFunction Y}) (Primrec.snd.comp Primrec.unpair)
  have hrun := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := {oracleFunction Y}) (Primrec.encode.comp
    ((finiteTrial_primrec d base).comp
      (Primrec.option_getD_default.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.unpair)))
      (Primrec.option_getD_default.comp (Primrec.decode.comp (Primrec.snd.comp Primrec.unpair)))))
  exact (_root_.OAI.TuringRigidity.PrefixComputability.total_comp hrun (_root_.OAI.TuringRigidity.PrefixComputability.total_pair hpre hw)).of_eq (fun z => by simp [trial])

theorem trial_sound (Y : Oracle) (e : OracleCode) (base : List Bool)
    (d : Nat.Partrec.Code)
    (hd : ∀ L w, d.eval (Nat.pair (encode L) w) = CommonIdeal.finiteRun e base L w)
    (z m : ℕ) (h : m ∈ trial Y d base z) : SplittingLocation Y e base m := by
  let L := oraclePrefix (fun n => CommonIdeal.bit (Y n)) (Nat.unpair z).1
  let w := ((decode (α := Witness) (Nat.unpair z).2).getD default)
  change m ∈ finiteTrial d base L w at h
  dsimp only [finiteTrial] at h
  split at h
  next hg =>
    have hm : m = base.length + w.1.2.1 := (Option.mem_some_iff.mp h).symm
    let a := d.evaln w.2.2.1 (Nat.pair (encode L) (Nat.pair (encode w.1.1) w.2.1))
    let b := d.evaln w.2.2.2 (Nat.pair (encode L) (Nat.pair (encode (w.1.1.set w.1.2.1 w.1.2.2)) w.2.1))
    have ha : a.getD 0 ∈ a := by
      cases ha' : a with
      | none => exact False.elim (hg.2.1 ha')
      | some v => simp
    have hb : b.getD 0 ∈ b := by
      cases hb' : b with
      | none => exact False.elim (hg.2.2.1 hb')
      | some v => simp
    have hva := Nat.Partrec.Code.evaln_sound ha
    have hvb := Nat.Partrec.Code.evaln_sound hb
    rw [hd] at hva hvb
    have hA := (CommonIdeal.finiteRun_approximates Y e base (encode w.1.1) w.2.1).1
      (Nat.unpair z).1 (a.getD 0) hva
    have hB := (CommonIdeal.finiteRun_approximates Y e base
      (encode (w.1.1.set w.1.2.1 w.1.2.2)) w.2.1).1 (Nat.unpair z).1 (b.getD 0) hvb
    rw [hm]
    refine ⟨base ++ w.1.1, w.1.2.2, w.2.1, a.getD 0, b.getD 0,
      List.prefix_append _ _, by omega, by simp; omega, hg.2.2.2, ?_, ?_⟩
    · simpa [BorelGeneric.word] using hA
    · simpa [BorelGeneric.word, List.set_append_right] using hB
  next hg => simp at h

theorem trial_complete (Y : Oracle) (e : OracleCode) (base : List Bool)
    (d : Nat.Partrec.Code)
    (hd : ∀ L w, d.eval (Nat.pair (encode L) w) = CommonIdeal.finiteRun e base L w)
    {m : ℕ} (hm : SplittingLocation Y e base m) : ∃ z, m ∈ trial Y d base z := by
  obtain ⟨s, b, n, a, c, ⟨u, rfl⟩, hbase, hms, hac, ha, hc⟩ := hm
  let i := m - base.length
  have hmi : m = base.length + i := by omega
  have hi : i < u.length := by simp only [List.length_append] at hms; omega
  have hc' : c ∈ CommonIdeal.run Y e (base ++ u.set i b) n := by
    simpa [List.set_append_right _ _ hbase] using hc
  have hau : a ∈ CommonIdeal.run Y e (base ++ BorelGeneric.word (encode u)) n := by
    simpa [BorelGeneric.word] using ha
  have hcu : c ∈ CommonIdeal.run Y e (base ++ BorelGeneric.word (encode (u.set i b))) n := by
    simpa [BorelGeneric.word] using hc'
  obtain ⟨M₀, hM₀⟩ := (CommonIdeal.finiteRun_approximates Y e base (encode u) n).2 a hau
  obtain ⟨M₁, hM₁⟩ := (CommonIdeal.finiteRun_approximates Y e base (encode (u.set i b)) n).2 c hcu
  let M := max M₀ M₁
  have hfa := hM₀ M (Nat.le_max_left _ _)
  have hfc := hM₁ M (Nat.le_max_right _ _)
  dsimp only at hfa hfc
  rw [← hd] at hfa hfc
  obtain ⟨t₀, ht₀⟩ := Nat.Partrec.Code.evaln_complete.mp hfa
  obtain ⟨t₁, ht₁⟩ := Nat.Partrec.Code.evaln_complete.mp hfc
  let w : Witness := ((u, i, b), (n, t₀, t₁))
  refine ⟨Nat.pair M (encode w), ?_⟩
  have ht₀' := Option.mem_def.mp ht₀
  have ht₁' := Option.mem_def.mp ht₁
  simp only [UniformOracle.oraclePrefix] at ht₀' ht₁'
  simp [trial, finiteTrial, oraclePrefix, w, ht₀', ht₁', hi, hac, hmi]

theorem splittingLocations_enumerable (Y : Oracle) (e : OracleCode) (base : List Bool) :
    ∃ E : ℕ → Option ℕ,
      Nat.RecursiveIn {oracleFunction Y} (fun z => Part.some (encode (E z))) ∧
      ∀ m, SplittingLocation Y e base m ↔ ∃ z, m ∈ E z := by
  obtain ⟨d, hd⟩ := CommonIdeal.finiteRun_code e base
  refine ⟨trial Y d base, trial_recursive Y d base, ?_⟩
  intro m
  exact ⟨trial_complete Y e base d hd, fun ⟨z, hz⟩ => trial_sound Y e base d hd z m hz⟩

end TuringRigidity.CodingSplitSearch

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_RecursiveInfiniteSubset
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RecursiveInfiniteSubset
open Encodable PrefixComputability

theorem above_spec (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) :
    n ≤ above E h n ∧ above E h n ∈ E (index E h n) := by
  have hs := Nat.find_spec (accepted_exists E h n)
  refine ⟨hs.2, ?_⟩
  change (E (index E h n)).getD 0 ∈ E (index E h n)
  cases he : E (index E h n) with
  | none => exact False.elim (hs.1 he)
  | some a => simp

private theorem flag_primrec : Primrec flag := by
  let hv := Primrec.option_getD_default.comp ((Primrec.decode (α := Option ℕ)).comp (Primrec.snd.comp Primrec.unpair))
  exact Primrec.ite (((Primrec.eq.comp hv (Primrec.const none)).not).and
    (Primrec.nat_le.comp (Primrec.fst.comp Primrec.unpair) (Primrec.option_getD_default.comp hv)))
    (Primrec.const 0) (Primrec.const 1)

theorem index_recursive {O : Set (ℕ →. ℕ)} (E : ℕ → Option ℕ) (h : Unbounded E)
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E z)))) :
    Nat.RecursiveIn O (fun n => Part.some (index E h n)) := by
  have hn := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hz := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := O) (Primrec.snd.comp Primrec.unpair)
  have hf := _root_.OAI.TuringRigidity.PrefixComputability.total_comp (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec flag_primrec) (_root_.OAI.TuringRigidity.PrefixComputability.total_pair hn (_root_.OAI.TuringRigidity.PrefixComputability.total_comp hE hz))
  apply (Nat.RecursiveIn.rfind hf).of_eq_tot
  intro n
  apply Nat.mem_rfind.mpr
  constructor
  · have hs := Nat.find_spec (accepted_exists E h n)
    simp [flag, index, hs.1, hs.2]
  · intro z hz
    have hm := Nat.find_min (accepted_exists E h n) hz
    simp [flag, hm]

theorem above_recursive {O : Set (ℕ →. ℕ)} (E : ℕ → Option ℕ) (h : Unbounded E)
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E z)))) :
    Nat.RecursiveIn O (fun n => Part.some (above E h n)) := by
  have hv := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := O) (Primrec.option_getD_default.comp
    (Primrec.option_getD_default.comp (Primrec.decode (α := Option ℕ))))
  exact (_root_.OAI.TuringRigidity.PrefixComputability.total_comp hv (_root_.OAI.TuringRigidity.PrefixComputability.total_comp hE (index_recursive E h hE))).of_eq
    (fun n => by simp [above])

theorem growing_strictMono (E : ℕ → Option ℕ) (h : Unbounded E) : StrictMono (growing E h) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact (Nat.lt_succ_self _).trans_le (above_spec E h _).1

theorem growing_mem (E : ℕ → Option ℕ) (h : Unbounded E) (n : ℕ) :
    ∃ z, growing E h n ∈ E z := by
  cases n <;> exact ⟨_, (above_spec E h _).2⟩

theorem growing_recursive {O : Set (ℕ →. ℕ)} (E : ℕ → Option ℕ) (h : Unbounded E)
    (hE : Nat.RecursiveIn O (fun z => Part.some (encode (E z)))) :
    Nat.RecursiveIn O (fun n => Part.some (growing E h n)) := by
  have habove := above_recursive E h hE
  have hbase := _root_.OAI.TuringRigidity.PrefixComputability.total_comp habove (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec (Primrec.const 0))
  have hstep := _root_.OAI.TuringRigidity.PrefixComputability.total_comp habove (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec
    (Primrec.succ.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp Primrec.unpair)))))
  have hrec := Nat.RecursiveIn.prec hbase hstep
  have hr := Nat.RecursiveIn.comp hrec
    (_root_.OAI.TuringRigidity.PrefixComputability.total_pair (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec (Primrec.const 0)) (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec Primrec.id))
  apply hr.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [growing]

theorem recursive_range (Y : Oracle) (f : ℕ → ℕ) (hf : StrictMono f)
    (hrec : Nat.RecursiveIn {oracleFunction Y} (fun n => Part.some (f n))) :
    ∃ C : Oracle, Reduces C Y ∧ ∀ m, C m = true ↔ ∃ n, f n = m := by
  let E := fun n => some (f n)
  have hE : Nat.RecursiveIn {oracleFunction Y} (fun n => Part.some (encode (E n))) :=
    _root_.OAI.TuringRigidity.PrefixComputability.total_comp (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec (Primrec.encode.comp (Primrec.option_some.comp Primrec.id))) hrec
  have hu : Unbounded E := fun n => ⟨n, f n, hf.id_le n, by simp [E]⟩
  let C : Oracle := fun m => decide (above E hu m = m)
  refine ⟨C, ?_, ?_⟩
  · apply RecursiveIn.iff_nat.mpr
    have heq := _root_.OAI.TuringRigidity.PrefixComputability.total_primrec (O := {oracleFunction Y})
      (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair)
        (Primrec.snd.comp Primrec.unpair)) (Primrec.const 1) (Primrec.const 0))
    have hh := _root_.OAI.TuringRigidity.PrefixComputability.total_comp heq (_root_.OAI.TuringRigidity.PrefixComputability.total_pair (above_recursive E hu hE) (_root_.OAI.TuringRigidity.PrefixComputability.total_primrec Primrec.id))
    apply hh.of_eq
    intro m
    by_cases he : above E hu m = m <;> simp [oracleFunction, C, he]
  · intro m
    change decide (above E hu m = m) = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · intro he
      exact ⟨index E hu m, he⟩
    · rintro ⟨n, hn⟩
      have hi : index E hu m ≤ n := Nat.find_min' (accepted_exists E hu m) (by simp [E, hn])
      have hs := (above_spec E hu m).1
      have he : above E hu m = f (index E hu m) := by simp [above, E]
      rw [he] at hs ⊢
      exact Nat.le_antisymm ((hf.monotone hi).trans (Nat.le_of_eq hn)) hs

theorem infinite_recursive_subset (Y : Oracle) (E : ℕ → Option ℕ)
    (h : Unbounded E)
    (hE : Nat.RecursiveIn {oracleFunction Y} (fun z => Part.some (encode (E z)))) :
    ∃ C : Oracle, Reduces C Y ∧ {m | C m = true}.Infinite ∧
      ∀ m, C m = true → ∃ z, m ∈ E z := by
  obtain ⟨C, hCY, hC⟩ := recursive_range Y (growing E h) (growing_strictMono E h)
    (growing_recursive E h hE)
  refine ⟨C, hCY, ?_, ?_⟩
  · have heq : {m | C m = true} = Set.range (growing E h) := by
      ext m
      exact hC m
    rw [heq]
    exact Set.infinite_range_of_injective (growing_strictMono E h).injective
  · intro m hm
    obtain ⟨n, rfl⟩ := (hC m).mp hm
    exact growing_mem E h n

end TuringRigidity.RecursiveInfiniteSubset

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingExtraction
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingExtraction
open CodingForcing CodingAgreement CodingLocations CodingSplitSearch PrefixComputability

theorem infinite_column {A : ℕ → Oracle} {Y C : Oracle} {p : Condition}
    (hCY : Reduces C Y) (hinf : {m | C m = true}.Infinite)
    (hC : ∀ m, C m = true → CodingLocation A p m) :
    ∃ k, k < p.active ∧ ∃ Z : Oracle, Reduces Z Y ∧ {a | Z a = true}.Infinite ∧
      ∀ a, Z a = true → A k a = true := by
  let F := fun k : Fin p.active => {m : ℕ | C m = true ∧ (Nat.unpair m).1 = k.val}
  have hex : ∃ k : Fin p.active, (F k).Infinite := by
    by_contra h
    have hf : ∀ k : Fin p.active, (F k).Finite := by
      intro k
      by_contra hi
      exact h ⟨k, hi⟩
    apply hinf
    apply (Set.finite_iUnion hf).subset
    intro m hm
    refine Set.mem_iUnion.mpr ⟨⟨(Nat.unpair m).1, (hC m hm).2.1⟩, ?_⟩
    exact ⟨hm, rfl⟩
  obtain ⟨k, hk⟩ := hex
  let Z : Oracle := fun a => C (Nat.pair k.val a)
  refine ⟨k.val, k.isLt, Z, reduces_trans (column_projection_reduces C k.val) hCY, ?_, ?_⟩
  · intro hZ
    apply hk
    apply (hZ.image (Nat.pair k.val)).subset
    intro m hm
    refine ⟨(Nat.unpair m).2, ?_, ?_⟩
    · change C (Nat.pair k.val (Nat.unpair m).2) = true
      rw [← hm.2, Nat.pair_unpair]
      exact hm.1
    · rw [← hm.2, Nat.pair_unpair]
  · intro a ha
    have hc := (hC (Nat.pair k.val a) ha).2.2
    simpa only [Nat.unpair_pair] using hc

end TuringRigidity.CodingExtraction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingRequirements
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CodingRequirements
open CodingForcing CodingAgreement CodingLocations CodingExtraction

theorem arbitrary_right_extension (A : ℕ → Oracle) (p : Condition)
    (s : List Bool) (hs : p.right <+: s) : ∃ q, Extends A p q ∧ q.right = s := by
  obtain ⟨u, rfl⟩ := hs
  exact ⟨append p u, append_extends A p u, rfl⟩

end TuringRigidity.CodingRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_AntichainCoding
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AntichainCoding
open CodingForcing CodingColumns CodingDiagonal CodingRequirements

theorem swap_join_reduces (G Y : Oracle) : Reduces (join G Y) (join Y G) :=
  join_reduces (reduces_join_right Y G) (reduces_join_left Y G)

end TuringRigidity.AntichainCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteInjury
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteInjury

theorem state_succ (proposal : ℕ → Finset ℕ → Option ℕ) (s : ℕ) :
    state proposal (s+1) = update (state proposal s) (action proposal s) := rfl

theorem action_not_done {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : action proposal s = some t) : t ∉ state proposal s := by
  unfold action accept at h
  cases hp : proposal s (state proposal s) with
  | none => simp [hp] at h
  | some i =>
    simp only [hp, Option.bind_some] at h
    split at h
    · simp at h
    · rename_i hi
      have he := Option.some.inj h
      exact he ▸ hi

theorem done_after_action {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : action proposal s = some t) : t ∈ state proposal (s+1) := by
  simp [state_succ, h, update]

theorem done_persists {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : t ∈ state proposal s)
    (hsmall : ∀ i < t, action proposal s ≠ some i) : t ∈ state proposal (s+1) := by
  rw [state_succ]
  cases ha : action proposal s with
  | none => simpa [ha, update] using h
  | some i =>
    have hle : t ≤ i := by
      by_contra hn
      exact hsmall i (by omega) ha
    simp only [update, Finset.mem_insert, Finset.mem_filter]
    rcases eq_or_lt_of_le hle with he | he
    · exact Or.inl he
    · exact Or.inr ⟨h, he⟩

theorem done_persists_from {proposal : ℕ → Finset ℕ → Option ℕ} {S t : ℕ}
    (h : t ∈ state proposal S)
    (hsmall : ∀ s, S ≤ s → ∀ i < t, action proposal s ≠ some i) :
    ∀ s, S ≤ s → t ∈ state proposal s := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact h
  | succ s hs ih => exact done_persists ih (hsmall s hs)

theorem finite_injury (proposal : ℕ → Finset ℕ → Option ℕ) (t : ℕ) :
    ∃ S, ∀ s, S ≤ s → ∀ i < t, action proposal s ≠ some i := by
  induction t with
  | zero => exact ⟨0, fun _ _ _ hi => by omega⟩
  | succ t ih =>
    obtain ⟨S, hS⟩ := ih
    by_cases hact : ∃ s, S ≤ s ∧ action proposal s = some t
    · obtain ⟨s, hs, ha⟩ := hact
      have hdone := done_after_action ha
      have hpersist := done_persists_from hdone
        (fun u hu => hS u (hs.trans (Nat.le_succ s |>.trans hu)))
      refine ⟨s+1, ?_⟩
      intro u hu i hi he
      by_cases hit : i = t
      · subst i
        exact action_not_done he (hpersist u hu)
      · exact hS u (hs.trans (Nat.le_succ s |>.trans hu)) i (by omega) he
    · refine ⟨S, ?_⟩
      intro s hs i hi he
      by_cases hit : i = t
      · exact hact ⟨s, hs, hit ▸ he⟩
      · exact hS s hs i (by omega) he

open CodingForcing

theorem level_mono {A : ℕ → Oracle} {p q : Condition} {t k : ℕ}
    (h : Extends A (atLevel p t) (atLevel q t)) (hk : k ≤ t) :
    Extends A (atLevel p k) (atLevel q k) := by
  refine ⟨h.1, h.2.1, le_rfl, ?_⟩
  intro m hm hlen
  exact h.2.2.2 m ⟨hm.1, hm.2.1.trans_le hk, hm.2.2⟩ hlen

theorem eventual_level_chain (A : ℕ → Oracle)
    (proposal : ℕ → Finset ℕ → Option ℕ) (p : ℕ → Condition)
    (hstep : ∀ s k, k ≤ s →
      (∀ t, action proposal s = some t → k ≤ t) →
      Extends A (atLevel (p s) k) (atLevel (p (s+1)) k)) (k : ℕ) :
    ∃ S, ∀ s, S ≤ s → ∀ u, s ≤ u →
      Extends A (atLevel (p s) k) (atLevel (p u) k) := by
  obtain ⟨S, hS⟩ := finite_injury proposal k
  refine ⟨max S k, ?_⟩
  intro s hs u hu
  induction u, hu using Nat.le_induction with
  | base => exact extends_refl A _
  | succ u hu ih =>
    apply extends_trans ih
    apply hstep u k ((le_max_right S k).trans (hs.trans hu))
    intro t ht
    by_contra hn
    exact hS u ((le_max_left S k).trans (hs.trans hu)) t (by omega) ht

end TuringRigidity.FiniteInjury

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteInjuryLimits
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteInjury
open CodingForcing

theorem word_prefix {p : ℕ → Condition}
    (h : ∀ s, (p s).left <+: (p (s+1)).left ∧ (p s).right <+: (p (s+1)).right)
    {s u : ℕ} (hsu : s ≤ u) : (p s).left <+: (p u).left ∧ (p s).right <+: (p u).right := by
  induction u, hsu using Nat.le_induction with
  | base => exact ⟨List.prefix_rfl, List.prefix_rfl⟩
  | succ u hu ih => exact ⟨ih.1.trans (h u).1, ih.2.trans (h u).2⟩

theorem limits_extend {p : ℕ → Condition}
    (h : ∀ s, (p s).left <+: (p (s+1)).left ∧ (p s).right <+: (p (s+1)).right)
    (hlen : ∀ s, s ≤ (p s).left.length) (s m : ℕ) (hm : m < (p s).left.length) :
    leftLimit p m = (p s).left.getD m false ∧
      rightLimit p m = (p s).right.getD m false := by
  unfold leftLimit rightLimit
  by_cases hs : s ≤ m+1
  · have hp := word_prefix h hs
    exact ⟨getD_of_prefix hp.1 hm,
      getD_of_prefix hp.2 (by simpa [← (p s).sameLength] using hm)⟩
  · have hp := word_prefix h (Nat.le_of_not_ge hs)
    have hml : m < (p (m+1)).left.length := (Nat.lt_succ_self m).trans_le (hlen (m+1))
    exact ⟨(getD_of_prefix hp.1 hml).symm,
      (getD_of_prefix hp.2 (by simpa [← (p (m+1)).sameLength] using hml)).symm⟩

theorem eventual_column_agreement (A : ℕ → Oracle)
    (proposal : ℕ → Finset ℕ → Option ℕ) (p : ℕ → Condition)
    (hwords : ∀ s, (p s).left <+: (p (s+1)).left ∧ (p s).right <+: (p (s+1)).right)
    (hlen : ∀ s, s ≤ (p s).left.length)
    (hstep : ∀ s k, k ≤ s →
      (∀ t, action proposal s = some t → k ≤ t) →
      Extends A (atLevel (p s) k) (atLevel (p (s+1)) k)) (k : ℕ) :
    ∃ S, ∀ m, (p S).left.length ≤ m → (Nat.unpair m).1 < k →
      A (Nat.unpair m).1 (Nat.unpair m).2 = true → leftLimit p m = rightLimit p m := by
  obtain ⟨S, hS⟩ := eventual_level_chain A proposal p hstep k
  refine ⟨S, ?_⟩
  intro m hm hk ha
  let u := max S (m+1)
  have hlen' : m < (p u).left.length :=
    (Nat.lt_succ_self m).trans_le ((le_max_right _ _).trans (hlen u))
  have hext := hS S le_rfl u (le_max_left _ _)
  have heq := hext.2.2.2 m ⟨hm, hk, ha⟩ hlen'
  have hlim := limits_extend hwords hlen u m hlen'
  exact hlim.1.trans (heq.trans hlim.2.symm)

end TuringRigidity.FiniteInjury

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteInjurySchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteInjurySchedule
open FiniteInjury

theorem visit_missing (seen : Finset ℕ) : visit seen ∉ seen := Nat.find_spec (exists_missing seen)

theorem before_visit (seen : Finset ℕ) {t : ℕ} (h : t < visit seen) : t ∈ seen := by
  have hh := Nat.find_min (exists_missing seen) h
  simpa using hh

theorem reset_preserves {S : Finset ℕ} {a : Option ℕ} {t : ℕ}
    (h : t ∈ S) (ha : ∀ i < t, a ≠ some i) : t ∈ reset S a := by
  cases he : a with
  | none => exact h
  | some i =>
    have hti : t ≤ i := by
      by_contra hn
      exact ha i (by omega) he
    exact Finset.mem_filter.mpr ⟨h,hti⟩

theorem seen_persists {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : t ∈ seen proposal s) (ha : ∀ i < t, action proposal s ≠ some i) :
    t ∈ seen proposal (s+1) :=
  reset_preserves (Finset.mem_insert_of_mem h) ha

theorem visit_recorded {proposal : ℕ → Finset ℕ → Option ℕ} {s : ℕ}
    (ha : ∀ i < scheduled proposal s, action proposal s ≠ some i) :
    scheduled proposal s ∈ seen proposal (s+1) :=
  reset_preserves (Finset.mem_insert_self _ _) ha

theorem fill_prefix {proposal : ℕ → Finset ℕ → Option ℕ} {S t : ℕ}
    (hS : ∀ s, S ≤ s → ∀ i < t, action proposal s ≠ some i) :
    ∀ n, n ≤ t+1 → ∀ j < n, j ∈ seen proposal (S+n) := by
  intro n
  induction n with
  | zero => intro hn j hj; omega
  | succ n ih =>
    intro hn j hj
    have hn' : n ≤ t+1 := by omega
    have hjt : j ≤ t := by omega
    have ha : ∀ i < j, action proposal (S+n) ≠ some i :=
      fun i hi => hS (S+n) (Nat.le_add_right _ _) i (hi.trans_le hjt)
    by_cases hmem : j ∈ seen proposal (S+n)
    · exact seen_persists hmem ha
    · have hjn : j = n := by
        by_contra hne
        exact hmem (ih hn' j (by omega))
      have hvis : scheduled proposal (S+n) = j := by
        apply Nat.le_antisymm
        · exact Nat.find_min' (exists_missing _) hmem
        · by_contra hlt
          have hvlt : visit (seen proposal (S+n)) < n := by
            change ¬ j ≤ scheduled proposal (S+n) at hlt
            dsimp only [scheduled] at hlt
            omega
          exact visit_missing _ (ih hn' _ hvlt)
      have hv := visit_recorded (proposal := proposal) (s := S+n) (by simpa [hvis] using ha)
      simpa [hvis,Nat.add_assoc] using hv

theorem seen_witness {proposal : ℕ → Finset ℕ → Option ℕ} {s t : ℕ}
    (h : t ∈ seen proposal s) : ∃ v, v < s ∧ scheduled proposal v = t ∧
      ∀ u, v ≤ u → u < s → ∀ i < t, action proposal u ≠ some i := by
  induction s with
  | zero => simp [seen] at h
  | succ s ih =>
    have hmem : t ∈ insert (scheduled proposal s) (seen proposal s) := by
      cases ha : action proposal s with
      | none => simpa [seen,ha,reset,scheduled] using h
      | some i => exact (Finset.mem_filter.mp (show t ∈ (insert (scheduled proposal s)
          (seen proposal s)).filter (fun j => j ≤ i) by simpa [seen,ha,reset,scheduled] using h)).1
    have hsafe : ∀ i < t, action proposal s ≠ some i := by
      intro i hi he
      have hh : t ≤ i := (Finset.mem_filter.mp (show t ∈ (insert (scheduled proposal s)
          (seen proposal s)).filter (fun j => j ≤ i) by simpa [seen,he,reset,scheduled] using h)).2
      omega
    rcases Finset.mem_insert.mp hmem with he | hm
    · refine ⟨s,Nat.lt_succ_self s,he.symm,fun u hu hus i hi => ?_⟩
      have hue : u = s := by omega
      exact hue ▸ hsafe i hi
    · obtain ⟨v,hv,he,hkeep⟩ := ih hm
      refine ⟨v,hv.trans (Nat.lt_succ_self s),he,fun u hu hus i hi => ?_⟩
      by_cases hue : u = s
      · exact hue ▸ hsafe i hi
      · exact hkeep u hu (by omega) i hi

theorem surviving_visit (proposal : ℕ → Finset ℕ → Option ℕ) (t : ℕ) :
    ∃ v, scheduled proposal v = t ∧
      ∀ u, v ≤ u → ∀ i < t, action proposal u ≠ some i := by
  obtain ⟨S,hS⟩ := finite_injury proposal t
  have ht := fill_prefix hS (t+1) le_rfl t (Nat.lt_succ_self t)
  obtain ⟨v,hv,he,hkeep⟩ := seen_witness ht
  refine ⟨v,he,fun u hu i hi => ?_⟩
  by_cases hus : u < S+(t+1)
  · exact hkeep u hu hus i hi
  · exact hS u (by omega) i hi

end TuringRigidity.FiniteInjurySchedule

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformProgram
open Encodable Computable

attribute [local instance] OAI.TuringRigidity.UniformProgram.instDecidableEqCode
theorem represent_correct (g : ℕ →. ℕ) (e : OracleCode) :
    OracleCode.eval g (meaning (represent e)) = OracleCode.eval g e := by
  induction e with
  | zero | succ | left | right | query => rfl
  | pair c d hc hd | comp c d hc hd | prec c d hc hd =>
    simp only [represent,meaning,OracleCode.eval,hc,hd]
    rfl
  | find c hc =>
    simp only [represent,meaning,reduceCtorEq,↓reduceIte,OracleCode.eval,hc]
    funext n
    simp [Seq.seq,Part.bind_some]
    apply congrArg Nat.rfind
    funext candidate
    exact congrArg (Part.map (fun value : ℕ => decide (value = 0)))
      (Part.bind_some (Nat.pair n candidate) (OracleCode.eval g c))

end TuringRigidity.UniformProgram

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalDecisive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalPair
open Encodable EncodedForcing CodingForcing UniformProgram IndexMatrix ArithmeticHierarchy

theorem decisive_excludes_common {B Y G₀ G₁ Z : Oracle} {F : ℕ → Oracle} {x : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction B) (meaning (machine (item x 0))) = oracleFunction Y)
    (h₀ : CommonIdeal.Extends G₀ p.left) (h₁ : CommonIdeal.Extends G₁ p.right)
    (he₀ : OracleCode.eval (oracleFunction (join Y G₀)) (meaning (machine (item x 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y G₁)) (meaning (machine (item x 2))) = oracleFunction Z)
    (hd : Decisive B F x p) : False := by
  have hr (i : ℕ) (s : List Bool) (n : ℕ) :
      UniformRun.run B (machine (item x 0)) (machine (item x i)) s n =
        CommonIdeal.run Y (meaning (machine (item x i))) s n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  rcases hd with ⟨n,a,b,hab,ha,hb⟩ | ⟨i,n,hi,hdiv⟩
  · rw [hr] at ha hb
    have ha' := CommonIdeal.run_total h₀ n a ha
    have hb' := CommonIdeal.run_total h₁ n b hb
    rw [he₀] at ha'
    rw [he₁] at hb'
    exact hab (Part.mem_unique ha' hb')
  · rcases hi with rfl | rfl
    · obtain ⟨s,hs,hv⟩ := CommonIdeal.run_finite_extension h₀ n (CommonIdeal.bit (Z n)) (by
        rw [he₀]; exact Part.mem_some _)
      obtain ⟨q,hpq,hq⟩ := CodingForcing.arbitrary_left_extension F p s hs
      have hh := hdiv q hpq (CommonIdeal.bit (Z n))
      simp only [↓reduceIte,hr,hq] at hh
      exact hh hv
    · obtain ⟨s,hs,hv⟩ := CommonIdeal.run_finite_extension h₁ n (CommonIdeal.bit (Z n)) (by
        rw [he₁]; exact Part.mem_some _)
      obtain ⟨q,hpq,hq⟩ := CodingRequirements.arbitrary_right_extension F p s hs
      have hh := hdiv q hpq (CommonIdeal.bit (Z n))
      simp only [show (2 : ℕ) ≠ 1 by decide,↓reduceIte,hr,hq] at hh
      exact hh hv

end TuringRigidity.LocalPair

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalColumnIndices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalColumnIndices
open Encodable UniformOracle EncodedForcing ArithmeticHierarchy

theorem specialized_eval (d : Nat.Partrec.Code) (k L n : ℕ) :
    (specialized d k).eval (Nat.pair L n) = d.eval (Nat.pair L (Nat.pair k n)) := by
  simp [specialized,Nat.Partrec.Code.eval_curry,Nat.Partrec.Code.eval,Seq.seq]
  change (((Part.some (Nat.pair L n)).bind
    (fun input => Part.some (Nat.unpair input).1)).bind
    (fun left => Part.map (Nat.pair left) (Part.map (Nat.pair k)
      ((Part.some (Nat.pair L n)).bind (fun input => Part.some (Nat.unpair input).2))))).bind
    (fun input => d.eval input) = _
  simp

theorem specialized_primrec (d : Nat.Partrec.Code) : Primrec (fun k => encode (specialized d k)) :=
  Primrec.encode.comp (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const _) Primrec.id)

theorem uniform_indices {B A : Oracle} (h : Reduces A B) :
    ∃ index : ℕ → ℕ, Primrec index ∧
      ∀ k, TableIndices.Represents B (IndexMatrix.machine (index k)) (columns A k) := by
  obtain ⟨d,hd⟩ := TableIndices.reduces_represents h
  refine ⟨fun k => encode (specialized d k),specialized_primrec d,fun k => ?_⟩
  simp only [IndexMatrix.machine_encode]
  constructor
  · intro n z a hz
    have he := Nat.Partrec.Code.evaln_sound hz
    change a ∈ (specialized d k).eval
      (Nat.pair (encode (oraclePrefix (fun q => CommonIdeal.bit (B q)) (Nat.unpair z).1)) n) at he
    rw [specialized_eval] at he
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp he
    exact hd.1 (Nat.pair k n) (Nat.pair (Nat.unpair z).1 t) a (by
      simpa only [TableIndices.run,trial,Nat.unpair_pair] using ht)
  · intro n
    obtain ⟨z,a,hz⟩ := hd.2 (Nat.pair k n)
    have he := Nat.Partrec.Code.evaln_sound hz
    change a ∈ d.eval
      (Nat.pair (encode (oraclePrefix (fun q => CommonIdeal.bit (B q)) (Nat.unpair z).1)) (Nat.pair k n)) at he
    rw [← specialized_eval d k] at he
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp he
    exact ⟨Nat.pair (Nat.unpair z).1 t,a,by
      simpa only [TableIndices.run,trial,Nat.unpair_pair] using ht⟩

theorem prefix_recursive_in {O : Set (ℕ →. ℕ)} (g : ℕ → ℕ)
    (hg : Nat.RecursiveIn O (fun n => Part.some (g n))) :
    Nat.RecursiveIn O (fun m => Part.some (encode (oraclePrefix g m))) := by
  have hy := (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := _root_.OAI.TuringRigidity.UniformOracle.total_comp ((_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)) (appendEncoded_primrec.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair hi (_root_.OAI.TuringRigidity.UniformOracle.total_comp hg hy))
  have hp := Nat.RecursiveIn.prec ((_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)) (Primrec.const (encode ([] : List ℕ)))) hs
  have hh := Nat.RecursiveIn.comp hp
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair ((_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)) (Primrec.const 0)) ((_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)) Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    simp [appendEncoded,oraclePrefix,List.range_succ]

theorem selected_prefixes {B A X : Oracle} (h : Reduces A B) (select : ℕ → ℕ)
    (hs : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (select n))) :
    ∃ codes : ℕ → ℕ,
      Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (codes n)) ∧
      ∀ n, LocalColumnCertificates.Presents B (fun k => columns A (select k)) (codes n) n := by
  obtain ⟨index,hi,hindex⟩ := uniform_indices h
  let g := fun k => index (select k)
  have hg : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (g n)) := by
    exact _root_.OAI.TuringRigidity.UniformOracle.total_comp (f := index) (g := select) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hi) hs
  refine ⟨fun n => encode (oraclePrefix g n),prefix_recursive_in g hg,?_⟩
  intro n k hk
  have he : item (encode (oraclePrefix g n)) k = g k := by
    simp [item,oraclePrefix,List.getD_eq_getElem?_getD,hk]
  rw [he]
  exact hindex (select k)

end TuringRigidity.LocalColumnIndices

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalInputs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalInputs
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing CodingForcing
noncomputable section

theorem total_transfer {Y Z : Oracle} {f : ℕ → ℕ}
    (h : Nat.RecursiveIn {oracleFunction Y} (fun n => Part.some (f n))) (hYZ : Reduces Y Z) :
    Nat.RecursiveIn {oracleFunction Z} (fun n => Part.some (f n)) :=
  RecursiveIn.iff_nat.mp (TuringReducible.trans (RecursiveIn.iff_nat.mpr h) hYZ)

theorem Data.request_recursive (D : Data) :
    Nat.RecursiveIn {oracleFunction D.bound} (fun n => Part.some (D.request n)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hc := _root_.OAI.TuringRigidity.UniformOracle.total_comp (total_transfer D.codes_recursive (reduces_join_left D.X (jump D.B)))
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (active_primrec.comp r))
  have hm := Primrec.encode.comp (Primrec.list_cons.comp f
    (Primrec.list_cons.comp (f.comp r) (Primrec.list_cons.comp (r.comp r) (Primrec.const []))))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hm) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hc (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id))).of_eq
    (fun n => by simp only [Nat.unpair_pair]; rfl)

theorem Data.pair_recursive (D : Data) :
    Nat.RecursiveIn {oracleFunction D.bound} (fun n => Part.some (D.pairProcedure n)) :=
  _root_.OAI.TuringRigidity.UniformOracle.total_comp (f := Classical.choose (LocalPair.pair_exists D.B)) (g := D.request)
    (total_transfer (Classical.choose_spec (LocalPair.pair_exists D.B)).1
    (reduces_join_right D.X (jump D.B))) D.request_recursive

theorem Data.pair_spec (D : Data) (x p : ℕ) :
    Extends D.F (condition p) (condition (D.pairProcedure (Nat.pair x p))) ∧
      (UniformAgreement.Disagreement D.B x (condition (D.pairProcedure (Nat.pair x p))) ∨
        ((condition (D.pairProcedure (Nat.pair x p))).active = active p ∧
          LocalAgreement.NoDisagreement D.B D.F x (condition p) ∧
          (LocalPair.Decisive D.B D.F x (condition (D.pairProcedure (Nat.pair x p))) ∨
            (condition (D.pairProcedure (Nat.pair x p)) = condition p ∧
              LocalPair.NoBad D.B D.F x p ∧ LocalPair.Outcome D.B D.F x p)))) := by
  simpa only [Data.pairProcedure,Data.request,Nat.unpair_pair] using
    (Classical.choose_spec (LocalPair.pair_exists D.B)).2 D.F (D.codes (active p)) x p (D.codes_valid _)

theorem Data.open_recursive (D : Data) :
    Nat.RecursiveIn {oracleFunction D.bound} (fun n => Part.some (D.openProcedure n)) :=
  _root_.OAI.TuringRigidity.UniformOracle.total_comp (f := Classical.choose (LocalOpen.uniform_open_decision D.B)) (g := D.request)
    (total_transfer (Classical.choose_spec (LocalOpen.uniform_open_decision D.B)).1
    (reduces_join_right D.X (jump D.B))) D.request_recursive

theorem Data.open_spec (D : Data) (e p : ℕ) :
    Extends D.F (condition p) (condition (D.openProcedure (Nat.pair e p))) ∧
      (Halts D.B e (D.openProcedure (Nat.pair e p)) ∨
        (D.openProcedure (Nat.pair e p) = p ∧
          ∀ q, Extends D.F (condition p) (condition q) → ¬ Halts D.B e q)) := by
  simpa only [Data.openProcedure,Data.request,Nat.unpair_pair] using
    (Classical.choose_spec (LocalOpen.uniform_open_decision D.B)).2 D.F (D.codes (active p)) e p (D.codes_valid _)

end
end TuringRigidity.LocalInputs

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalStage
open Encodable CodingForcing EncodedForcing FiniteInjury
noncomputable section
attribute [local instance] Classical.propDecidable

theorem pairProcedure_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction D.bound} (fun v => Part.some (pairProcedure D v)) := D.pair_recursive

theorem candidate_extends (D : LocalInputs.Data) (t : ℕ) (p : Condition) :
    Extends D.F (atLevel p t) (candidate D t p) := by
  have h := (D.pair_spec t (code (atLevel p t))).1
  rw [condition_code] at h
  exact ⟨h.1,h.2.1,le_rfl,h.2.2.2⟩

theorem scan_spec {D : LocalInputs.Data} {p : Condition} {done : Finset ℕ} {t n i : ℕ}
    (h : scan D p done t n = some i) :
    t ≤ i ∧ i < t+n ∧ i ∉ done ∧ Changes D i p := by
  induction n generalizing t with
  | zero => simp [scan] at h
  | succ n ih =>
    simp only [scan] at h
    split at h
    · rename_i ht
      have he := Option.some.inj h
      subst i
      exact ⟨le_rfl,by omega,ht⟩
    · obtain ⟨hlo,hhi,hd,hc⟩ := ih h
      exact ⟨by omega,by omega,hd,hc⟩

theorem open_extends (D : LocalInputs.Data) (e : ℕ) (p : Condition) :
    Extends D.F p (condition (openProcedure D (Nat.pair e (code p)))) := by
  simpa only [condition_code,openProcedure] using (D.open_spec e (code p)).1

theorem action_not_done (D : LocalInputs.Data) (s : ℕ) (p : State) (t : ℕ)
    (h : stageAction D s p = some t) : t ∉ p.done := (scan_spec h).2.2.1

theorem accept_action (D : LocalInputs.Data) (s : ℕ) (p : State) :
    FiniteInjury.accept p.done (stageAction D s p) = stageAction D s p := by
  cases ha : stageAction D s p with
  | none => simp [FiniteInjury.accept]
  | some t => simp [FiniteInjury.accept,action_not_done D s p t ha]

theorem done_eq (D : LocalInputs.Data) (s : ℕ) :
    (construction D s).done = FiniteInjury.state (proposal D) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change FiniteInjury.update (construction D s).done (stageAction D s (construction D s)) = _
    rw [FiniteInjury.state]
    rw [← ih]
    simp only [proposal,accept_action]

theorem action_eq (D : LocalInputs.Data) (s : ℕ) :
    FiniteInjury.action (proposal D) s = stageAction D s (construction D s) := by
  rw [FiniteInjury.action,← done_eq]
  exact accept_action D s _

theorem seen_eq (D : LocalInputs.Data) (s : ℕ) :
    (construction D s).seen = FiniteInjurySchedule.seen (proposal D) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change FiniteInjurySchedule.reset _ _ = _
    rw [FiniteInjurySchedule.seen,action_eq,← ih]

theorem active_eq (D : LocalInputs.Data) (s : ℕ) : (conditions D s).active = s := by
  cases s <;> rfl

theorem stage_words (D : LocalInputs.Data) (s : ℕ) (p : State) :
    p.condition.left <+: (stageWord D s p).left ∧ p.condition.right <+: (stageWord D s p).right := by
  have ho := open_extends D (FiniteInjurySchedule.visit p.seen) p.condition
  cases ha : stageAction D s p with
  | none => exact ⟨by simpa [stageWord,ha,generic] using ho.1,by simpa [stageWord,ha,generic] using ho.2.1⟩
  | some t =>
    have hc := candidate_extends D t (generic D p)
    exact ⟨by simpa [stageWord,ha] using ho.1.trans hc.1,
      by simpa [stageWord,ha] using ho.2.1.trans hc.2.1⟩

theorem word_growth (D : LocalInputs.Data) (s : ℕ) :
    (conditions D s).left <+: (conditions D (s+1)).left ∧
    (conditions D s).right <+: (conditions D (s+1)).right := by
  have h := stage_words D s (construction D s)
  exact ⟨h.1.trans (List.prefix_append _ _),h.2.trans (List.prefix_append _ _)⟩

theorem length_bound (D : LocalInputs.Data) (s : ℕ) : s ≤ (conditions D s).left.length := by
  induction s with
  | zero => exact Nat.zero_le _
  | succ s ih =>
    have h := (stage_words D s (construction D s)).1.length_le
    change s+1 ≤ ((stageWord D s (construction D s)).left ++ [false]).length
    simp only [List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (ih.trans h) 1

theorem level_step (D : LocalInputs.Data) (s k : ℕ) (hk : k ≤ s)
    (hact : ∀ t, FiniteInjury.action (proposal D) s = some t → k ≤ t) :
    Extends D.F (atLevel (conditions D s) k) (atLevel (conditions D (s+1)) k) := by
  let p := construction D s
  have ho := open_extends D (FiniteInjurySchedule.visit p.seen) p.condition
  have hg : Extends D.F (atLevel p.condition k) (atLevel (generic D p) k) := by
    refine ⟨ho.1,ho.2.1,le_rfl,?_⟩
    intro m hm hlen
    apply ho.2.2.2 m ⟨hm.1,?_,hm.2.2⟩ hlen
    exact hm.2.1.trans_le (by
      change k ≤ (conditions D s).active
      rw [active_eq]
      exact hk)
  have hw : Extends D.F (atLevel (generic D p) k) (atLevel (stageWord D s p) k) := by
    cases ha : stageAction D s p with
    | none => simpa [stageWord,ha] using extends_refl D.F (atLevel (generic D p) k)
    | some t =>
      have hkt : k ≤ t := hact t (by simpa [action_eq,p] using ha)
      have hc := candidate_extends D t (generic D p)
      have hc' : Extends D.F (atLevel (generic D p) t) (atLevel (candidate D t (generic D p)) t) := hc
      simpa [stageWord,ha] using level_mono hc' hkt
  have htail : Extends D.F (atLevel (stageWord D s p) k)
      (atLevel (conditions D (s+1)) k) := append_extends _ _ [false]
  exact extends_trans hg (extends_trans hw htail)

theorem surviving_columns (D : LocalInputs.Data) (k : ℕ) : ∃ S, ∀ m,
    (conditions D S).left.length ≤ m → (Nat.unpair m).1 < k →
    D.F (Nat.unpair m).1 (Nat.unpair m).2 = true →
    leftLimit (conditions D) m = rightLimit (conditions D) m :=
  eventual_column_agreement D.F (proposal D) (conditions D)
    (word_growth D) (length_bound D) (level_step D) k

theorem surviving_generic_visit (D : LocalInputs.Data) (t : ℕ) : ∃ s,
    FiniteInjurySchedule.visit (construction D s).seen = t ∧
      ∀ u, s ≤ u → ∀ i < t, stageAction D u (construction D u) ≠ some i := by
  obtain ⟨s,hs,hh⟩ := FiniteInjurySchedule.surviving_visit (proposal D) t
  refine ⟨s,?_,?_⟩
  · simpa [seen_eq,FiniteInjurySchedule.scheduled] using hs
  · simpa only [action_eq] using hh

end
end TuringRigidity.LocalStage

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_StageRecords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.StageRecords
open Encodable UniformOracle EncodedForcing FiniteInjurySchedule

theorem recur_recursive {O : Set (ℕ →. ℕ)} {z f : ℕ → ℕ}
    (hz : Nat.RecursiveIn O (fun a => Part.some (z a)))
    (hf : Nat.RecursiveIn O (fun a => Part.some (f a))) :
    Nat.RecursiveIn O (fun v => Part.some (recur z f (Nat.unpair v).1 (Nat.unpair v).2)) := by
  apply (Nat.RecursiveIn.prec hz hf).of_eq
  intro v
  generalize hv : Nat.unpair v = p
  obtain ⟨a,n⟩ := p
  simp only [Part.bind_eq_bind]
  clear hv
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih,Part.bind_some,recur]

theorem record_primrec : Primrec record := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem mem_primrec : PrimrecRel (fun n i => i ∈ record n) := by
  have h := Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.snd (record_primrec.comp Primrec.fst))
    (Primrec.list_length.comp (record_primrec.comp Primrec.fst))
  exact h.of_eq (fun p => List.idxOf_lt_length_iff)

theorem nextVisit_recursive {O : Set (ℕ →. ℕ)} :
    Nat.RecursiveIn O (fun n => Part.some (nextVisit n)) := by
  classical
  have h : Primrec (fun v : ℕ => if (Nat.unpair v).2 ∈ record (Nat.unpair v).1 then 1 else 0) :=
    Primrec.ite (mem_primrec.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))
      (Primrec.const 1) (Primrec.const 0)
  apply (Nat.RecursiveIn.rfind (_root_.OAI.TuringRigidity.UniformOracle.total_primrec h)).of_eq_tot
  intro n
  apply Nat.mem_rfind.mpr
  constructor
  · have hn : nextVisit n ∉ record n := by simpa [members,nextVisit] using visit_missing (members n)
    simp [hn]
  · intro i hi
    have hi' : i ∈ record n := by simpa [members] using before_visit (members n) hi
    simp [hi']

theorem filter_primrec : Primrec (fun p : ℕ × ℕ => (record p.1).filter (fun i => i < p.2)) := by
  have h := Primrec.listFilterMap (record_primrec.comp Primrec.fst)
    (Primrec.ite (Primrec.nat_lt.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂
  exact h.of_eq (fun p => by
    induction record p.1 with
    | nil => rfl
    | cons i l ih => by_cases hi : i < p.2 <;> simp [hi,ih])

theorem doneUpdate_primrec : Primrec₂ doneUpdate := by
  have ht : Primrec (fun p : ℕ × ℕ => p.2-1) := Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.fst
    (Primrec.encode.comp (Primrec.list_cons.comp ht (filter_primrec.comp (Primrec.fst.pair ht))))

theorem seenInsert_primrec : Primrec₂ seenInsert := Primrec.encode.comp
  (Primrec.list_cons.comp Primrec.snd (record_primrec.comp Primrec.fst))

theorem seenReset_primrec : Primrec₂ seenReset := Primrec.ite
  (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.fst (Primrec.encode.comp filter_primrec)

theorem members_doneUpdate (n a : ℕ) : members (doneUpdate n a) = FiniteInjury.update (members n) (action a) := by
  by_cases ha : a = 0
  · simp [doneUpdate,ha,action,FiniteInjury.update]
  · ext i
    simp [doneUpdate,ha,action,FiniteInjury.update,members,record]

theorem members_seenReset (n a : ℕ) : members (seenReset n a) = reset (members n) (action a) := by
  by_cases ha : a = 0
  · simp [seenReset,ha,action,reset]
  · ext i
    simp only [seenReset,ite_eq_right ha,action,reset,members,record,encodek,Option.getD_some,
      List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_filter]
    constructor
    · rintro ⟨hm,hi⟩; exact ⟨hm,by omega⟩
    · rintro ⟨hm,hi⟩; exact ⟨hm,by omega⟩

end TuringRigidity.StageRecords

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

theorem levelCode_primrec : Primrec₂ levelCode := Primrec₂.natPair.comp
  (Primrec.encode.comp (left_primrec.comp Primrec.fst))
  (Primrec₂.natPair.comp (Primrec.encode.comp (right_primrec.comp Primrec.fst)) Primrec.snd)

theorem levelCode_eq (p t : ℕ) : levelCode p t = code (atLevel (condition p) t) := rfl

theorem candidate_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (candidate D v)) := by
  have h := _root_.OAI.TuringRigidity.UniformOracle.total_comp (LocalStage.pairProcedure_recursive D)
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp f (levelCode_primrec.comp r f)))
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (levelCode_primrec.comp f r)) (_root_.OAI.TuringRigidity.UniformOracle.total_pair h (_root_.OAI.TuringRigidity.UniformOracle.total_primrec f))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

@[simp] theorem candidate_eq (D : LocalInputs.Data) (t p : ℕ) :
    condition (candidate D (Nat.pair t p)) = LocalStage.candidate D t (condition p) := by
  simp only [candidate,Nat.unpair_pair,levelCode_eq,LocalStage.candidate,condition_code]

theorem scanStep_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (scanStep D v)) := by
  have hc := _root_.OAI.TuringRigidity.UniformOracle.total_comp (candidate_recursive D)
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp (f.comp r) (f.comp f)))
  let v := f
  let c := r
  let p := f.comp (f.comp v)
  let d := r.comp (f.comp v)
  let t := f.comp (r.comp v)
  let prev := r.comp (r.comp v)
  have hm := (mem_primrec.comp d t).not
  have hl := (Primrec.eq.comp (left_primrec.comp c) (left_primrec.comp p)).not
  have hr := (Primrec.eq.comp (right_primrec.comp c) (right_primrec.comp p)).not
  have hpost := Primrec.ite ((Primrec.eq.comp prev (Primrec.const 0)).and (hm.and (hl.or hr)))
    (Primrec.succ.comp t) prev
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hpost) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id) hc)
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem scan_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v =>
      Part.some (scan D (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2)) := by
  simpa only [scan,Nat.pair_unpair] using recur_recursive (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.const 0)) (scanStep_recursive D)

theorem source_scan_succ (D : LocalInputs.Data) (p : Condition) (d : Finset ℕ) (t n : ℕ) :
    LocalStage.scan D p d t (n+1) =
      match LocalStage.scan D p d t n with
      | some i => some i
      | none => if t+n ∉ d ∧ LocalStage.Changes D (t+n) p then some (t+n) else none := by
  induction n generalizing t with
  | zero => simp [LocalStage.scan]
  | succ n ih =>
    change (if t ∉ d ∧ LocalStage.Changes D t p then some t else LocalStage.scan D p d (t+1) (n+1)) =
      match (if t ∉ d ∧ LocalStage.Changes D t p then some t else LocalStage.scan D p d (t+1) n) with
      | some i => some i
      | none => if t+(n+1) ∉ d ∧ LocalStage.Changes D (t+(n+1)) p then some (t+(n+1)) else none
    by_cases ht : t ∉ d ∧ LocalStage.Changes D t p
    · simp only [ite_eq_left ht]
    · simpa only [ite_eq_right ht,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1)

theorem scan_eq (D : LocalInputs.Data) (p d n : ℕ) :
    scan D p d n = actionCode (LocalStage.scan D (condition p) (members d) 0 n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [source_scan_succ]
    change scanStep D (Nat.pair (Nat.pair p d) (Nat.pair n (scan D p d n))) = _
    simp only [scanStep,Nat.unpair_pair,ih,Nat.zero_add]
    have hc : left (candidate D (Nat.pair n p)) ≠ left p ∨
        right (candidate D (Nat.pair n p)) ≠ right p ↔ LocalStage.Changes D n (condition p) := by
      change (condition (candidate D (Nat.pair n p))).left ≠ (condition p).left ∨
        (condition (candidate D (Nat.pair n p))).right ≠ (condition p).right ↔ _
      rw [candidate_eq]
      rfl
    cases he : LocalStage.scan D (condition p) (members d) 0 n with
    | none =>
      by_cases hn : n ∉ record d ∧ LocalStage.Changes D n (condition p)
      · simp_all only [actionCode,members,List.mem_toFinset,true_and]
        simp
      · simp_all only [actionCode,members,List.mem_toFinset,true_and]
        simp
    | some i => simp [actionCode]

end
end TuringRigidity.LocalComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

theorem open_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (LocalStage.openProcedure D v)) :=
  D.open_recursive

theorem generic_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun v => Part.some (genericCanonical D v)) := by
  have hn := _root_.OAI.TuringRigidity.UniformOracle.total_comp (nextVisit_recursive (O := {oracleFunction (D.bound)})) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (r.comp r))
  have hp := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction (D.bound)}) ((levelCode_primrec.comp Primrec.id active_primrec).comp f)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (open_recursive D) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hn hp)
  exact hh.of_eq (fun v => rfl)

theorem stageAction_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun z =>
      Part.some (stageAction D (Nat.unpair z).1 (Nat.unpair z).2)) := by
  have hg := _root_.OAI.TuringRigidity.UniformOracle.total_comp (generic_recursive D) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (scan_recursive D) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_pair hg (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (f.comp (r.comp r)))) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec f))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

@[simp] theorem stageAction_eq (D : LocalInputs.Data) (s v : ℕ) :
    action (stageAction D s v) = LocalStage.stageAction D s (state v) := by
  rw [stageAction,scan_eq,action_actionCode,generic_eq]
  rfl

theorem stageWord_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun z => Part.some (stageWord D z)) := by
  have ha := stageAction_recursive D
  have hg := _root_.OAI.TuringRigidity.UniformOracle.total_comp (generic_recursive D) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r)
  have hc := _root_.OAI.TuringRigidity.UniformOracle.total_comp (candidate_recursive D) (_root_.OAI.TuringRigidity.UniformOracle.total_pair
    (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))) ha) hg)
  have hpost := Primrec.ite (Primrec.eq.comp f (Primrec.const 0)) (f.comp r) (r.comp r)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hpost) (_root_.OAI.TuringRigidity.UniformOracle.total_pair ha (_root_.OAI.TuringRigidity.UniformOracle.total_pair hg hc))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem stageWord_eq (D : LocalInputs.Data) (s v : ℕ) :
    condition (stageWord D (Nat.pair s v)) = LocalStage.stageWord D s (state v) := by
  have he := stageAction_eq D s v
  unfold stageWord
  simp only [Nat.unpair_pair]
  by_cases ha : stageAction D s v = 0
  · have hn : LocalStage.stageAction D s (state v) = none := by simpa only [StageRecords.action,ite_eq_left ha] using he.symm
    simp [ha,LocalStage.stageWord,hn,generic_eq]
  · have hn : LocalStage.stageAction D s (state v) = some (stageAction D s v-1) := by
      simpa only [StageRecords.action,ite_eq_right ha] using he.symm
    simp [ha,LocalStage.stageWord,hn,candidate_eq,generic_eq]

theorem grow_primrec : Primrec₂ grow := Primrec₂.natPair.comp
  (Primrec.encode.comp (Primrec.list_append.comp (left_primrec.comp Primrec.fst) (Primrec.const [false])))
  (Primrec₂.natPair.comp
    (Primrec.encode.comp (Primrec.list_append.comp (right_primrec.comp Primrec.fst) (Primrec.const [false])))
    (Primrec.succ.comp Primrec.snd))

theorem advance_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun z => Part.some (advance D z)) := by
  have ha := stageAction_recursive D
  have hw := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (grow_primrec.comp f r))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (stageWord_recursive D) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec f))
  have hd := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (doneUpdate_primrec.comp f r))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (f.comp (r.comp r))) ha)
  have hs := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction (D.bound)}) (r.comp (r.comp r))
  have hn := _root_.OAI.TuringRigidity.UniformOracle.total_comp nextVisit_recursive hs
  have hi := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (seenInsert_primrec.comp f r)) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hs hn)
  have hreset := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (seenReset_primrec.comp f r)) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hi ha)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_pair hw (_root_.OAI.TuringRigidity.UniformOracle.total_pair hd hreset)
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem advance_eq (D : LocalInputs.Data) (s v : ℕ) :
    state (advance D (Nat.pair s v)) = LocalStage.advance D s (state v) := by
  unfold state advance
  simp only [Nat.unpair_pair,condition_grow,stageWord_eq,members_doneUpdate,
    members_seenReset,members_seenInsert,stageAction_eq]
  rfl

theorem construction_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)} (fun s => Part.some (construction D s)) := by
  have h := recur_recursive (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.const initial))
    (_root_.OAI.TuringRigidity.UniformOracle.total_comp (advance_recursive D) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r))
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp h (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem construction_eq (D : LocalInputs.Data) (s : ℕ) :
    state (construction D s) = LocalStage.construction D s := by
  induction s with
  | zero => simp [construction,recur,initial,state,condition_code,members,record,LocalStage.construction]
  | succ s ih =>
    change state (advance D (Nat.unpair (Nat.pair 0 (Nat.pair s (construction D s)))).2) = _
    rw [Nat.unpair_pair,advance_eq,ih]
    rfl

theorem conditions_recursive (D : LocalInputs.Data) :
    Nat.RecursiveIn {oracleFunction (D.bound)}
      (fun s => Part.some (code (LocalStage.conditions D s))) := by
  have h := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec ((levelCode_primrec.comp Primrec.id active_primrec).comp f))
    (construction_recursive D)
  apply h.of_eq
  intro s
  change Part.some (code (state (construction D s)).condition) = _
  rw [construction_eq]
  rfl

theorem limits_recursive (D : LocalInputs.Data) :
    Reduces (join (leftLimit (LocalStage.conditions D)) (rightLimit (LocalStage.conditions D)))
      (D.bound) := by
  have hs := _root_.OAI.TuringRigidity.UniformOracle.total_comp (conditions_recursive D) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.succ.comp Primrec.nat_div2))
  have hbit : Primrec (fun v : ℕ => CommonIdeal.bit
      ((bif (Nat.unpair v).2.bodd then right (Nat.unpair v).1 else left (Nat.unpair v).1).getD
        (Nat.unpair v).2.div2 false)) := CommonIdeal.bit_primrec.comp
    ((Primrec.list_getD false).comp
      (Primrec.cond (Primrec.nat_bodd.comp r) (right_primrec.comp f) (left_primrec.comp f))
      (Primrec.nat_div2.comp r))
  have h := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hbit) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hs (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id))
  apply RecursiveIn.iff_nat.mpr
  have hl (p : Condition) : left (code p) = p.left := congrArg Condition.left (condition_code p)
  have hr (p : Condition) : right (code p) = p.right := congrArg Condition.right (condition_code p)
  exact h.of_eq (fun n => by
    simp only [Nat.unpair_pair]
    cases hb : n.bodd <;> simp [oracleFunction,join,hb,leftLimit,rightLimit,CommonIdeal.bit,
      hl,hr,Nat.div2_val])

end
end TuringRigidity.LocalComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalLimits
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing FiniteInjury
open LocalStage
noncomputable section
attribute [local instance] Classical.propDecidable

theorem generic_prefix_next (D : LocalInputs.Data) (s : ℕ) :
    (generic D (construction D s)).left <+: (conditions D (s+1)).left ∧
    (generic D (construction D s)).right <+: (conditions D (s+1)).right := by
  have h : (generic D (construction D s)).left <+: (stageWord D s (construction D s)).left ∧
      (generic D (construction D s)).right <+: (stageWord D s (construction D s)).right := by
    cases ha : stageAction D s (construction D s) with
    | none => simp [stageWord,ha]
    | some t =>
      have hc := candidate_extends D t (generic D (construction D s))
      exact ⟨by simpa [stageWord,ha,atLevel] using hc.1,by simpa [stageWord,ha,atLevel] using hc.2.1⟩
  exact ⟨h.1.trans (List.prefix_append _ _),h.2.trans (List.prefix_append _ _)⟩

theorem limits_extend_generic (D : LocalInputs.Data) (s : ℕ) :
    CommonIdeal.Extends (G₀ D) (generic D (construction D s)).left ∧
    CommonIdeal.Extends (G₁ D) (generic D (construction D s)).right := by
  have hp := generic_prefix_next D s
  constructor
  · intro m hm
    have hh := (limits_extend (word_growth D) (length_bound D) (s+1) m (hm.trans_le hp.1.length_le)).1
    exact hh.trans (getD_of_prefix hp.1 hm)
  · intro m hm
    have hn : m < (conditions D (s+1)).left.length := by
      rw [(conditions D (s+1)).sameLength]
      exact hm.trans_le hp.2.length_le
    have hh := (limits_extend (word_growth D) (length_bound D) (s+1) m hn).2
    exact hh.trans (getD_of_prefix hp.2 hm)

theorem meets_dense (D : LocalInputs.Data) {P : ℕ → Prop} (hP : Sigma D.B 1 P)
    (hdense : ∀ p : Condition, ∃ q : ℕ, Extends D.F p (condition q) ∧ P q) :
    ∃ q : ℕ, P q ∧ CommonIdeal.Extends (G₀ D) (condition q).left ∧
      CommonIdeal.Extends (G₁ D) (condition q).right := by
  obtain ⟨e,he⟩ := EffectiveCohen.sigma1_enumeration hP
  obtain ⟨s,hs,_⟩ := surviving_generic_visit D e
  let p := construction D s
  let q := openProcedure D (Nat.pair e (code p.condition))
  have hdec := (D.open_spec e (code p.condition)).2
  change OracleJump.Halts D.B e q ∨
    (q = code p.condition ∧
      ∀ r, Extends D.F (condition (code p.condition)) (condition r) → ¬ OracleJump.Halts D.B e r) at hdec
  have hq : P q := by
    rcases hdec with h | ⟨_,h⟩
    · exact (he q).mpr h
    · obtain ⟨r,hr,hR⟩ := hdense (condition (code p.condition))
      exact False.elim (h r hr ((he r).mp hR))
  refine ⟨q,hq,?_⟩
  have hh := limits_extend_generic D s
  simpa only [generic,hs,p,q] using hh

theorem disagreement_recursive (A X : Oracle) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (loc n)))
    (hX : Reduces X A) : RecursivePred A (fun v =>
      loc (Nat.unpair v).2 < (left (Nat.unpair v).1).length ∧
      (left (Nat.unpair v).1).getD (loc (Nat.unpair v).2) false ≠ X (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hm := _root_.OAI.TuringRigidity.UniformOracle.total_comp hloc (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r)
  have hx := _root_.OAI.TuringRigidity.UniformOracle.total_comp (RecursiveIn.iff_nat.mp hX) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r)
  have hp : Primrec (fun v : ℕ =>
      if (Nat.unpair (Nat.unpair v).2).1 < (left (Nat.unpair v).1).length ∧
        CommonIdeal.bit ((left (Nat.unpair v).1).getD (Nat.unpair (Nat.unpair v).2).1 false) ≠
          (Nat.unpair (Nat.unpair v).2).2 then 1 else 0) :=
    Primrec.ite ((Primrec.nat_lt.comp (f.comp r) (Primrec.list_length.comp (left_primrec.comp f))).and
      ((Primrec.eq.comp (CommonIdeal.bit_primrec.comp ((Primrec.list_getD false).comp
        (left_primrec.comp f) (f.comp r))) (r.comp r)).not)) (Primrec.const 1) (Primrec.const 0)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hp) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec f) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hm hx))
  have hbits (b c : Bool) : (CommonIdeal.bit b ≠ (if c then 1 else 0)) ↔ b ≠ c := by
    cases b <;> cases c <;> decide
  exact hh.of_eq (fun v => by
    simp only [Nat.unpair_pair,hbits]
    by_cases ht : loc (Nat.unpair v).2 < (left (Nat.unpair v).1).length ∧
        (left (Nat.unpair v).1).getD (loc (Nat.unpair v).2) false ≠ X (Nat.unpair v).2
    · simp only [ite_eq_left ht]
    · simp only [ite_eq_right ht])

theorem reads_not_reduces (D : LocalInputs.Data) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction D.B} (fun n => Part.some (loc n)))
    (hunbounded : ∀ N, ∃ n, N ≤ loc n) : ¬ Reduces (fun n => G₀ D (loc n)) D.B := by
  intro hX
  let X : Oracle := fun n => G₀ D (loc n)
  have hP : Sigma D.B 1 (fun p => ∃ n, loc n < (left p).length ∧ (left p).getD (loc n) false ≠ X n) := by
    simpa only [Nat.unpair_pair] using
      (Form.raise (n := 0) (s := true) (disagreement_recursive D.B X loc hloc hX)).ex
  have hdense : ∀ p : Condition, ∃ q : ℕ, Extends D.F p (condition q) ∧
      ∃ n, loc n < (left q).length ∧ (left q).getD (loc n) false ≠ X n := by
    intro p
    obtain ⟨n,hn⟩ := hunbounded p.left.length
    obtain ⟨q,hpq,hql,hqb⟩ := CodingDiagonal.prescribe D.F p (loc n) hn (!(X n))
    refine ⟨code q,by simpa [condition_code] using hpq,n,?_,?_⟩
    · simpa only [show left (code q) = q.left from congrArg Condition.left (condition_code q)] using hql
    · rw [show left (code q) = q.left from congrArg Condition.left (condition_code q),hqb]
      cases X n <;> decide
  obtain ⟨q,⟨n,hn,hne⟩,hl,_⟩ := meets_dense D hP hdense
  exact hne (hl (loc n) hn).symm

theorem common_noncomputable_columns (D : LocalInputs.Data)
    (hA : ∀ k, {a | D.F k a = true}.Infinite) :
    ∀ k, ∃ C : Oracle, Reduces C (join (G₀ D) (D.F k)) ∧
      Reduces C (join (G₁ D) (D.F k)) ∧ ¬ Reduces C (D.F k) := by
  intro k
  obtain ⟨S,hS⟩ := surviving_columns D (k+1)
  let cutoff := (conditions D S).left.length
  let loc := CodingColumns.location (D.F k) (hA k) k cutoff
  have hcol : Reduces (D.F k) D.B := TableIndices.represents_reduces
    (D.codes_valid (k+1) k (Nat.lt_succ_self k))
  have hloc : Nat.RecursiveIn {oracleFunction D.B} (fun n => Part.some (loc n)) :=
    (CodingColumns.location_recursive (D.F k) (hA k) k cutoff).subst (fun f hf => by
      have he : f = oracleFunction (D.F k) := Set.mem_singleton_iff.mp hf
      subst f
      exact RecursiveIn.iff_nat.mp hcol)
  have hn := reads_not_reduces D loc hloc (fun N => ⟨N,CodingColumns.le_location _ _ _ _ _⟩)
  let C := CodingColumns.readColumn (D.F k) (hA k) k cutoff (G₀ D)
  have heq : C = CodingColumns.readColumn (D.F k) (hA k) k cutoff (G₁ D) := by
    funext n
    have hm := CodingColumns.location_mem (D.F k) (hA k) k cutoff n
    simp only [CodingColumns.column] at hm
    split at hm
    next h =>
      apply hS _ h.1
      · rw [h.2]; omega
      · simpa only [h.2] using hm
    next h => simp at hm
  exact ⟨C,CodingColumns.readColumn_reduces _ _ _ _ _,
    heq.symm ▸ CodingColumns.readColumn_reduces _ _ _ _ _,fun h => hn (reduces_trans h hcol)⟩

theorem effective_first_clause (D : LocalInputs.Data)
    (hA : ∀ k, {a | D.F k a = true}.Infinite) :
    Reduces (join (G₀ D) (G₁ D)) (D.bound) ∧
      ∀ k, ∃ C : Oracle, Reduces C (join (G₀ D) (D.F k)) ∧
        Reduces C (join (G₁ D) (D.F k)) ∧ ¬ Reduces C (D.F k) :=
  ⟨LocalComputability.limits_recursive D,common_noncomputable_columns D hA⟩

end
end TuringRigidity.LocalLimits

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalOutcomes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalOutcomes
open ArithmeticHierarchy
open Encodable EncodedForcing CodingForcing FiniteInjury LocalStage
open UniformProgram IndexMatrix
noncomputable section

theorem candidate_decisive (D : LocalInputs.Data) (t : ℕ) (p : Condition)
    (hc : Changes D t p) : LocalPair.Decisive D.B D.F t (candidate D t p) := by
  let p' := atLevel p t
  let q := condition (pairProcedure D (Nat.pair t (code p')))
  obtain ⟨_,hdis | ⟨ha,hn,hd | ⟨he,hrest⟩⟩⟩ :=
    D.pair_spec t (code p')
  · exact Or.inl hdis
  · have haq : q.active = t := by
      change q.active = (condition (code p')).active at ha
      simpa only [condition_code,p',atLevel] using ha
    have heq : atLevel q t = q := by rw [← haq]; cases q; rfl
    change LocalPair.Decisive D.B D.F t (atLevel q t)
    rw [heq]
    exact hd
  · have heq : q = p' := by
      change q = condition (code p') at he
      simpa only [condition_code] using he
    change (atLevel q t).left ≠ p.left ∨ (atLevel q t).right ≠ p.right at hc
    rw [heq] at hc
    exact False.elim (hc.elim (fun h => h rfl) (fun h => h rfl))

theorem limits_extend_action {D : LocalInputs.Data} {s t : ℕ}
    (ha : stageAction D s (construction D s) = some t) :
    CommonIdeal.Extends (LocalLimits.G₀ D) (candidate D t (generic D (construction D s))).left ∧
    CommonIdeal.Extends (LocalLimits.G₁ D) (candidate D t (generic D (construction D s))).right := by
  have hl : (candidate D t (generic D (construction D s))).left <+: (conditions D (s+1)).left := by
    change _ <+: (stageWord D s (construction D s)).left ++ [false]
    simp only [stageWord,ha]
    exact List.prefix_append _ _
  have hr : (candidate D t (generic D (construction D s))).right <+: (conditions D (s+1)).right := by
    change _ <+: (stageWord D s (construction D s)).right ++ [false]
    simp only [stageWord,ha]
    exact List.prefix_append _ _
  constructor
  · intro m hm
    exact ((limits_extend (word_growth D) (length_bound D) (s+1) m (hm.trans_le hl.length_le)).1).trans
      (getD_of_prefix hl hm)
  · intro m hm
    have hn : m < (conditions D (s+1)).left.length := by
      rw [(conditions D (s+1)).sameLength]
      exact hm.trans_le hr.length_le
    exact ((limits_extend (word_growth D) (length_bound D) (s+1) m hn).2).trans (getD_of_prefix hr hm)

theorem action_excludes_common {D : LocalInputs.Data} {Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    stageAction D s (construction D s) ≠ some t := by
  intro ha
  have hc := (scan_spec ha).2.2.2
  obtain ⟨h₀,h₁⟩ := limits_extend_action ha
  exact LocalPair.decisive_excludes_common (F := D.F) hbase h₀ h₁ he₀ he₁ (candidate_decisive D t _ hc)

theorem done_witness (D : LocalInputs.Data) {s t : ℕ} (ht : t ∈ (construction D s).done) :
    ∃ u, u < s ∧ stageAction D u (construction D u) = some t := by
  induction s with
  | zero => simp [construction] at ht
  | succ s ih =>
    change t ∈ FiniteInjury.update (construction D s).done (stageAction D s (construction D s)) at ht
    cases ha : stageAction D s (construction D s) with
    | none =>
      obtain ⟨u,hu,he⟩ := ih (by simpa [ha,FiniteInjury.update] using ht)
      exact ⟨u,by omega,he⟩
    | some i =>
      simp only [ha,FiniteInjury.update,Finset.mem_insert,Finset.mem_filter] at ht
      rcases ht with rfl | ⟨ht,_⟩
      · exact ⟨s,by omega,ha⟩
      · obtain ⟨u,hu,he⟩ := ih ht
        exact ⟨u,by omega,he⟩

theorem common_not_done {D : LocalInputs.Data} {Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    t ∉ (construction D s).done := by
  intro ht
  obtain ⟨u,_,hu⟩ := done_witness D ht
  exact action_excludes_common hbase he₀ he₁ hu

theorem scan_hits {D : LocalInputs.Data} {p : Condition} {d : Finset ℕ} {start n t : ℕ}
    (hlo : start ≤ t) (hhi : t < start+n) (hd : t ∉ d) (hc : Changes D t p) :
    ∃ i, i ≤ t ∧ scan D p d start n = some i := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    by_cases h : start ∉ d ∧ Changes D start p
    · exact ⟨start,hlo,by simp only [scan,ite_eq_left h]⟩
    · have hne : start ≠ t := by rintro rfl; exact h ⟨hd,hc⟩
      obtain ⟨i,hi,he⟩ := ih (start := start+1) (by omega) (by omega)
      exact ⟨i,hi,by simpa only [scan,ite_eq_right h] using he⟩

theorem common_eventually_unchanged {D : LocalInputs.Data} {Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    ∃ S, ∀ s, S ≤ s → ¬ Changes D t (generic D (construction D s)) := by
  obtain ⟨S,hS⟩ := finite_injury (proposal D) (t+1)
  refine ⟨max S (t+1),fun s hs hc => ?_⟩
  obtain ⟨i,hi,he⟩ := scan_hits (start := 0) (n := s) (Nat.zero_le t)
    (by omega) (common_not_done (s := s) hbase he₀ he₁) hc
  apply hS s ((le_max_left _ _).trans hs) i (by omega)
  simpa only [action_eq,stageAction] using he

theorem nonchanging_outcome {D : LocalInputs.Data} {Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hchange : ¬ Changes D t (generic D (construction D s))) :
    let p := atLevel (generic D (construction D s)) t
    LocalAgreement.NoDisagreement D.B D.F t p ∧ LocalPair.NoBad D.B D.F t (code p) ∧
      ((¬ ∃ z, UniformSplit.SplitCert D.B (Nat.pair (UniformPair.request (Nat.pair t (code p))) z)) ∨
        ∃ w, UniformSplit.PointCert D.B (Nat.pair (UniformPair.request (Nat.pair t (code p))) w) ∧
          CodingLocation D.F p (item w 2)) := by
  let p := atLevel (generic D (construction D s)) t
  let q := condition (pairProcedure D (Nat.pair t (code p)))
  have hwords : q.left = p.left ∧ q.right = p.right := by
    change ¬ (q.left ≠ p.left ∨ q.right ≠ p.right) at hchange
    exact ⟨Classical.not_not.mp (fun hn => hchange (Or.inl hn)),
      Classical.not_not.mp (fun hn => hchange (Or.inr hn))⟩
  have hq₀ : CommonIdeal.Extends (LocalLimits.G₀ D) q.left := by
    rw [hwords.1]; exact (LocalLimits.limits_extend_generic D s).1
  have hq₁ : CommonIdeal.Extends (LocalLimits.G₁ D) q.right := by
    rw [hwords.2]; exact (LocalLimits.limits_extend_generic D s).2
  obtain ⟨_,hd | ⟨ha,hn,hd | ⟨he,hbad,hout⟩⟩⟩ :=
    D.pair_spec t (code p)
  · exact False.elim (LocalPair.decisive_excludes_common (F := D.F) hbase hq₀ hq₁ he₀ he₁ (Or.inl hd))
  · exact False.elim (LocalPair.decisive_excludes_common (F := D.F) hbase hq₀ hq₁ he₀ he₁ hd)
  · refine ⟨by simpa only [condition_code] using hn,hbad,?_⟩
    simpa only [LocalPair.Outcome,condition_code] using hout

theorem common_eventually_outcome {D : LocalInputs.Data} {Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    ∃ S, ∀ s, S ≤ s →
      let p := atLevel (generic D (construction D s)) t
      LocalAgreement.NoDisagreement D.B D.F t p ∧ LocalPair.NoBad D.B D.F t (code p) ∧
        ((¬ ∃ z, UniformSplit.SplitCert D.B (Nat.pair (UniformPair.request (Nat.pair t (code p))) z)) ∨
          ∃ w, UniformSplit.PointCert D.B (Nat.pair (UniformPair.request (Nat.pair t (code p))) w) ∧
            CodingLocation D.F p (item w 2)) := by
  obtain ⟨S,hS⟩ := common_eventually_unchanged hbase he₀ he₁
  exact ⟨S,fun s hs => nonchanging_outcome hbase he₀ he₁ (hS s hs)⟩

end
end TuringRigidity.LocalOutcomes

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalExtraction
open ArithmeticHierarchy
open Encodable CodingForcing EncodedForcing UniformProgram IndexMatrix FiniteInjury LocalStage
noncomputable section

theorem noSplit_reduces {A Y G Z : Oracle} {t : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (hG : CommonIdeal.Extends G p.left)
    (he : OracleCode.eval (oracleFunction (join Y G)) (meaning (machine (item t 1))) = oracleFunction Z)
    (hno : ¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) z)) :
    Reduces Z Y := by
  have hrun (w : List Bool) (n : ℕ) :
      UniformRun.run A (machine (item t 0)) (machine (item t 1)) w n =
        CommonIdeal.run Y (meaning (machine (item t 1))) w n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  apply CodingAgreement.case1_reduces (A := columns A) (p := p) ?_ hG he
  intro q r hpq hpr n a b ha hb
  by_contra hab
  rw [← hrun] at ha hb
  apply hno
  refine ⟨encode [n,encode q.left,encode r.left,a,b],?_⟩
  simpa [UniformSplit.SplitCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
    UniformPair.request,item,word,
    show left (code p) = p.left from congrArg Condition.left (condition_code p)] using
    And.intro hpq.1 (And.intro hpr.1 (And.intro hab (And.intro ha hb)))

theorem point_splittingLocation {A Y : Oracle} {t w : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (hw : UniformSplit.PointCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) w)) :
    CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) p.left (item w 2) := by
  have hrun (v : List Bool) (n : ℕ) :
      UniformRun.run A (machine (item t 0)) (machine (item t 1)) v n =
        CommonIdeal.run Y (meaning (machine (item t 1))) v n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  have hh : p.left <+: word (item w 1) ∧ p.left.length ≤ item w 2 ∧
      item w 2 < (word (item w 1)).length ∧ item w 4 ≠ item w 5 ∧
      item w 4 ∈ CommonIdeal.run Y (meaning (machine (item t 1))) (word (item w 1)) (item w 0) ∧
      item w 5 ∈ CommonIdeal.run Y (meaning (machine (item t 1)))
        ((word (item w 1)).set (item w 2) (item w 3).bodd) (item w 0) := by
    rw [← hrun,← hrun]
    simpa [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      UniformPair.request,item,word,
      show left (code p) = p.left from congrArg Condition.left (condition_code p)] using hw
  exact ⟨word (item w 1),(item w 3).bodd,item w 0,item w 4,item w 5,hh⟩

theorem noBad_sound {D : LocalInputs.Data} {Y : Oracle} {t : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (hbad : LocalPair.NoBad D.B D.F t (code p)) {m : ℕ}
    (hm : CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) p.left m) :
    CodingLocation D.F p m := by
  obtain ⟨v,b,n,a,c,hpv,hpm,hmv,hac,ha,hc⟩ := hm
  have hrun (w : List Bool) (n : ℕ) :
      UniformRun.run D.B (machine (item t 0)) (machine (item t 1)) w n =
        CommonIdeal.run Y (meaning (machine (item t 1))) w n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  have hw : UniformSplit.PointCert D.B
      (Nat.pair (UniformPair.request (Nat.pair t (code p))) (encode [n,encode v,m,CommonIdeal.bit b,a,c])) := by
    have hbit : (CommonIdeal.bit b).bodd = b := by cases b <;> rfl
    have hh := And.intro hpv (And.intro hpm (And.intro hmv (And.intro hac
      (And.intro ((hrun v n).symm ▸ ha) ((hrun (v.set m b) n).symm ▸ hc)))))
    simpa [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      UniformPair.request,item,word,hbit,
      show left (code p) = p.left from congrArg Condition.left (condition_code p)] using hh
  have hh := hbad _ hw
  simpa only [condition_code,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ] using hh

theorem common_recursive_locations {D : LocalInputs.Data} {Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hn : ¬ Reduces Z Y) :
    ∃ p : Condition, p.active = t ∧ ∃ C : Oracle, Reduces C Y ∧
      {m | C m = true}.Infinite ∧ ∀ m, C m = true → CodingLocation D.F p m := by
  obtain ⟨S,hS⟩ := LocalOutcomes.common_eventually_outcome hbase he₀ he₁
  let p := atLevel (generic D (construction D S)) t
  have hbad : LocalPair.NoBad D.B D.F t (code p) := (hS S le_rfl).2.1
  obtain ⟨E,hE,hEq⟩ := CodingSplitSearch.splittingLocations_enumerable Y (meaning (machine (item t 1))) p.left
  have hu : RecursiveInfiniteSubset.Unbounded E := by
    intro N
    let s := max (S+1) N
    let q := atLevel (generic D (construction D s)) t
    have hpq : p.left <+: q.left := by
      exact (LocalLimits.generic_prefix_next D S).1.trans
        ((word_prefix (word_growth D) (le_max_left (S+1) N)).1.trans
          (open_extends D _ _).1)
    obtain ⟨_,_,hno | ⟨w,hw,hcoding⟩⟩ := hS s (by dsimp [s]; omega)
    · exact False.elim (hn (noSplit_reduces (p := q) (t := t) hbase
        (LocalLimits.limits_extend_generic D s).1 he₀ hno))
    · have hN : N ≤ q.left.length := by
        exact (le_max_right (S+1) N).trans ((length_bound D s).trans (open_extends D _ _).1.length_le)
      obtain ⟨v,b,n,a,c,hqv,hqm,hmv,hac,ha,hc⟩ := point_splittingLocation hbase hw
      have hpoint : CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) p.left (item w 2) :=
        ⟨v,b,n,a,c,hpq.trans hqv,hpq.length_le.trans hqm,hmv,hac,ha,hc⟩
      obtain ⟨z,hz⟩ := (hEq (item w 2)).mp hpoint
      exact ⟨z,item w 2,hN.trans hqm,hz⟩
  obtain ⟨C,hCY,hCi,hC⟩ := RecursiveInfiniteSubset.infinite_recursive_subset Y E hu hE
  exact ⟨p,rfl,C,hCY,hCi,fun m hm => noBad_sound hbase hbad ((hEq m).mpr (hC m hm))⟩

theorem common_infinite_column {D : LocalInputs.Data} {Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hn : ¬ Reduces Z Y) :
    ∃ k, k < t ∧ ∃ C : Oracle, Reduces C Y ∧ {a | C a = true}.Infinite ∧
      ∀ a, C a = true → D.F k a = true := by
  obtain ⟨p,hp,C,hCY,hCi,hC⟩ := common_recursive_locations hbase he₀ he₁ hn
  simpa only [hp] using CodingExtraction.infinite_column hCY hCi hC

theorem common_lower_computes_column {D : LocalInputs.Data} {Y Z : Oracle}
    (hIntro : ∀ k C, (∀ a, C a = true → D.F k a = true) →
      {a | C a = true}.Infinite → Reduces (D.F k) C)
    (hY : Reduces Y D.B)
    (h₀ : Reduces Z (join Y (LocalLimits.G₀ D)))
    (h₁ : Reduces Z (join Y (LocalLimits.G₁ D)))
    (hn : ¬ Reduces Z Y) : ∃ k, Reduces (D.F k) Y := by
  obtain ⟨b,hb⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hY
  obtain ⟨e,he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h₀
  obtain ⟨f,hf⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h₁
  let t := encode [encode (represent b),encode (represent e),encode (represent f)]
  have hb' : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y := by
    simpa [t,item,machine,represent_correct] using hb
  have he' : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D))) (meaning (machine (item t 1))) = oracleFunction Z := by
    simpa [t,item,machine,represent_correct] using he
  have hf' : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D))) (meaning (machine (item t 2))) = oracleFunction Z := by
    simpa [t,item,machine,represent_correct] using hf
  obtain ⟨k,_,C,hCY,hCi,hC⟩ := common_infinite_column hb' he' hf' hn
  exact ⟨k,reduces_trans (hIntro k C hC hCi) hCY⟩

end
end TuringRigidity.LocalExtraction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_StageNormalization
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.StageNormalization
open Encodable UniformOracle EncodedForcing StageRecords

private theorem prefixStep_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction A} (fun v => Part.some (prefixStep A v)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) := .oracle _ (Set.mem_singleton _)
  have h := _root_.OAI.TuringRigidity.UniformOracle.total_comp hq (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp f (f.comp r)))
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (UniformOracle.appendEncoded_primrec.comp f r))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (r.comp r)) h)
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem prefix_eq (A : Oracle) (k n : ℕ) :
    columnPrefix A k n = Introreducible.prefixCode (columns A k) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change prefixStep A (Nat.pair k (Nat.pair n (columnPrefix A k n))) = _
    simp only [prefixStep,Nat.unpair_pair,ih,UniformOracle.appendEncoded,
      Introreducible.prefixCode,encodek,Option.getD_some,
      PrefixComputability.oraclePrefix,List.range_succ,List.map_append,List.map_cons,List.map_nil]
    rfl

theorem prefix_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction A} (fun v => Part.some (columnPrefix A (Nat.unpair v).1 (Nat.unpair v).2)) :=
  recur_recursive (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.const (encode ([] : List ℕ)))) (prefixStep_recursive A)

theorem normalized_reduces (A : Oracle) : Reduces (normalized A) A := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := _root_.OAI.TuringRigidity.UniformOracle.total_comp (prefix_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp f
    (Introreducible.codeLength_primrec.comp r)))
  have he : Primrec (fun v : ℕ => if (Nat.unpair v).1 = (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp f r) (Primrec.const 1) (Primrec.const 0)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec he) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r))
  apply RecursiveIn.iff_nat.mpr
  exact hh.of_eq (fun v => by simp [Nat.unpair_pair,prefix_eq,normalized,Introreducible.prefixSet,oracleFunction])

theorem normalized_spec (A : Oracle) (k : ℕ) :
    degree (columns (normalized A) k) = degree (columns A k) ∧
      {n | columns (normalized A) k n = true}.Infinite ∧
      ∀ Z : Oracle, (∀ n, Z n = true → columns (normalized A) k n = true) →
        {n | Z n = true}.Infinite → Reduces (columns (normalized A) k) Z := by
  rw [normalized_column]
  exact ⟨Introreducible.prefixSet_degree _,Introreducible.prefixSet_infinite _,fun Z hs hi =>
    reduces_trans (Introreducible.prefixSet_reduces _) (Introreducible.reduces_of_infinite_subset hs hi)⟩

end TuringRigidity.StageNormalization

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_LocalCoding
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.LocalCoding
open EncodedForcing StageNormalization AntichainParameters

theorem selected_coding {A B X : Oracle} (hAB : Reduces A B) (select : ℕ → ℕ)
    (hs : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (select n))) :
    ∃ G₀ G₁ : Oracle, Reduces (join G₀ G₁) (join X (OracleJump.jump B)) ∧
      (∀ k, ∃ C : Oracle, Reduces C (join G₀ (columns A (select k))) ∧
        Reduces C (join G₁ (columns A (select k))) ∧ ¬ Reduces C (columns A (select k))) ∧
      ∀ Y Z : Oracle, Reduces Y B → Reduces Z (join G₀ Y) →
        Reduces Z (join G₁ Y) → ¬ Reduces Z Y → ∃ k, Reduces (columns A (select k)) Y := by
  obtain ⟨codes,hcodes,hvalid⟩ := LocalColumnIndices.selected_prefixes
    (reduces_trans (normalized_reduces A) hAB) select hs
  let D : LocalInputs.Data := ⟨B,X,fun k => columns (normalized A) (select k),codes,hcodes,hvalid⟩
  obtain ⟨hbound,hfirst⟩ := LocalLimits.effective_first_clause D
    (fun k => (normalized_spec A (select k)).2.1)
  refine ⟨LocalLimits.G₀ D,LocalLimits.G₁ D,hbound,?_,?_⟩
  · intro k
    obtain ⟨C,h₀,h₁,hn⟩ := hfirst k
    obtain ⟨hBA,hAB'⟩ := (degree_eq_iff _ _).mp (normalized_spec A (select k)).1
    exact ⟨C,reduces_trans h₀ (join_mono (reduces_refl _) hBA),
      reduces_trans h₁ (join_mono (reduces_refl _) hBA),fun h => hn (reduces_trans h hAB')⟩
  · intro Y Z hY h₀ h₁ hn
    obtain ⟨k,hk⟩ := LocalExtraction.common_lower_computes_column (D := D)
      (fun k => (normalized_spec A (select k)).2.2) hY
      (reduces_trans h₀ (AntichainCoding.swap_join_reduces _ _))
      (reduces_trans h₁ (AntichainCoding.swap_join_reduces _ _)) hn
    exact ⟨k,reduces_trans (((degree_eq_iff _ _).mp (normalized_spec A (select k)).1).2) hk⟩

theorem selected_antichain_oai {A B X : Oracle} (hAB : Reduces A B) (select : ℕ → ℕ)
    (hs : Nat.RecursiveIn {oracleFunction X} (fun n => Part.some (select n)))
    (hAnti : ∀ i j, degree (columns A (select i)) ≤ degree (columns A (select j)) →
      degree (columns A (select i)) = degree (columns A (select j))) :
    ∃ g₀ g₁ : Degree, g₀ ⊔ g₁ ≤ degree (join X (OracleJump.jump B)) ∧
      ∀ x : Degree, CodedAntichain (degree B) g₀ g₁ x ↔ ∃ k, degree (columns A (select k)) = x := by
  obtain ⟨G₀,G₁,hbound,hfirst,hsecond⟩ := selected_coding hAB select hs
  have hm : ∀ k, NontrivialCommonLower (degree B) (degree G₀) (degree G₁) (degree (columns A (select k))) := by
    intro k
    obtain ⟨C,h₀,h₁,hn⟩ := hfirst k
    exact ⟨reduces_trans (CodingExtraction.column_projection_reduces A (select k)) hAB,degree C,h₀,h₁,hn⟩
  have hc : ∀ x, NontrivialCommonLower (degree B) (degree G₀) (degree G₁) x →
      ∃ k, degree (columns A (select k)) ≤ x := by
    intro x hx
    obtain ⟨Y,rfl⟩ := degree_surjective x
    obtain ⟨z,h₀,h₁,hn⟩ := hx.2
    obtain ⟨Z,rfl⟩ := degree_surjective z
    exact hsecond Y Z hx.1 h₀ h₁ hn
  refine ⟨degree G₀,degree G₁,hbound,fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := hc x hx.1
    exact ⟨k,le_antisymm hk (hx.2 _ (hm k) hk)⟩
  · rintro ⟨k,rfl⟩
    refine ⟨hm k,fun y hy hyk => ?_⟩
    obtain ⟨j,hj⟩ := hc y hy
    exact hAnti j k (hj.trans hyk) ▸ hj

end TuringRigidity.LocalCoding

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.LocalCoding.selected_antichain_oai := @OAI.TuringRigidity.LocalCoding.selected_antichain_oai
