-- Prove2me | solution 1 for OAI.TuringRigidity.EnumerationConstruction.enumeration_exists
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:01:17.214118+00:00
-- url     : https://prove2.me/submissions/978c7a56-e81e-49af-8e4f-fc8c4358a312

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006
import Theorems.Thm_OAI_TuringRigidity_FixedArithmetic_frame_exists

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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.instOrderBotDegree _root_.OAI.TuringRigidity.instSemilatticeSupDegree
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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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

end TuringRigidity.CommonIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectiveCohen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveCohen
open Encodable UniformOracle ArithmeticHierarchy OracleJump EffectiveWitness EncodedForcing

theorem decider_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (decider Y x)) :=
  (Classical.choose_spec (word_decision Y)).1

theorem decider_spec (Y : Oracle) (e p : ℕ) :
    word p <+: word (decider Y (Nat.pair e p)) ∧
      (Halts Y e (encode (word (decider Y (Nat.pair e p)))) ∨
        ∀ q : List Bool, word (decider Y (Nat.pair e p)) <+: q → ¬ Halts Y e (encode q)) :=
  (Classical.choose_spec (word_decision Y)).2 e p

theorem grow_primrec : Primrec grow := Primrec.encode.comp
  (Primrec.list_append.comp word_primrec (Primrec.const [false]))

theorem stage_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump Y)} (fun s => Part.some (stage Y s)) := by
  let r := Primrec.snd.comp Primrec.unpair
  have hstep := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec grow_primrec)
    (_root_.OAI.TuringRigidity.UniformOracle.total_comp (decider_recursive Y) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r))
  have hr := Nat.RecursiveIn.prec (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction (jump Y)}) (Primrec.const (encode ([] : List Bool)))) hstep
  have h := Nat.RecursiveIn.comp hr
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.const 0)) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id))
  apply h.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    change (Part.some (stage Y n)).bind _ = _
    rw [Part.bind_some]
    rfl

theorem stage_prefix (Y : Oracle) (s : ℕ) : word (stage Y s) <+: word (stage Y (s+1)) := by
  have h := (decider_spec Y s (stage Y s)).1
  simpa only [stage,grow,word,encodek,Option.getD_some] using
    h.trans (List.prefix_append _ [false])

theorem stage_length (Y : Oracle) (s : ℕ) : s ≤ (word (stage Y s)).length := by
  induction s with
  | zero => exact Nat.zero_le _
  | succ s ih =>
    have hh := (decider_spec Y s (stage Y s)).1.length_le
    simp only [stage,grow,word,encodek,Option.getD_some,List.length_append,List.length_cons,List.length_nil]
    simp only [word] at hh ih
    omega

theorem stage_prefix_of_le (Y : Oracle) {s t : ℕ} (h : s ≤ t) : word (stage Y s) <+: word (stage Y t) := by
  induction t,h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ t ht ih => exact ih.trans (stage_prefix Y t)

theorem generic_extends (Y : Oracle) (s : ℕ) :
    ∀ n < (word (stage Y s)).length, generic Y n = (word (stage Y s)).getD n false := by
  intro n hn
  let t := max s (n+1)
  have h0 := stage_prefix_of_le Y (show s ≤ t from le_max_left _ _)
  have h1 := stage_prefix_of_le Y (show n+1 ≤ t from le_max_right _ _)
  have hn1 : n < (word (stage Y (n+1))).length := (Nat.lt_succ_self n).trans_le (stage_length Y _)
  exact (CodingForcing.getD_of_prefix h1 hn1).symm.trans (CodingForcing.getD_of_prefix h0 hn)

theorem generic_reduces (Y : Oracle) : Reduces (generic Y) (jump Y) := by
  have hs := _root_.OAI.TuringRigidity.UniformOracle.total_comp (stage_recursive Y) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.succ)
  have hv := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (CommonIdeal.bit_primrec.comp
    ((Primrec.list_getD false).comp (word_primrec.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)))) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hs (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id))
  apply RecursiveIn.iff_nat.mpr
  exact hv.of_eq (fun n => by simp [oracleFunction,generic,CommonIdeal.bit])

theorem generic_oneGeneric (Y : Oracle) : OneGeneric Y (generic Y) := by
  intro e
  let w := word (decider Y (Nat.pair e (stage Y e)))
  refine ⟨w,?_,(decider_spec Y e (stage Y e)).2⟩
  intro n hn
  have hw : w <+: word (stage Y (e+1)) := by
    simpa only [w,stage,grow,word,encodek,Option.getD_some] using List.prefix_append w [false]
  exact (generic_extends Y (e+1) n (hn.trans_le hw.length_le)).trans (CodingForcing.getD_of_prefix hw hn)

end TuringRigidity.EffectiveCohen

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

theorem OneGeneric.decides {Y G : Oracle} (hG : OneGeneric Y G)
    {P : ℕ → Prop} (hP : Sigma Y 1 P) : ∃ p : List Bool,
      (∀ n < p.length, G n = p.getD n false) ∧
        (P (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ P (encode q)) := by
  obtain ⟨e,he⟩ := sigma1_enumeration hP
  obtain ⟨p,hp,hd⟩ := hG e
  refine ⟨p,hp,?_⟩
  simpa only [he] using hd

end TuringRigidity.EffectiveCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenHalting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenHalting
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing IndexMatrix

theorem table_primrec : Primrec table := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem agrees_recursive (Y : Oracle) : RecursivePred Y (fun v =>
    Agrees Y (word (Nat.unpair v).1) (table (Nat.unpair v).2)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let p := word_primrec.comp (f.comp f)
  let L := table_primrec.comp (r.comp f)
  let i := r
  let half := Primrec.nat_div.comp i (Primrec.const 2)
  let val := (Primrec.list_getD 0).comp L i
  have ho := recursive_primrecPred Y (Primrec.eq.comp (Primrec.nat_bodd.comp i) (Primrec.const true))
  have hb := recursive_primrecPred Y (Primrec.nat_lt.comp half (Primrec.list_length.comp p))
  have hp := recursive_primrecPred Y (Primrec.eq.comp val
    (bit_primrec.comp ((Primrec.list_getD false).comp p half)))
  have hquery : Nat.RecursiveIn {oracleFunction Y} (oracleFunction Y) := .oracle _ (Set.mem_singleton _)
  have hq : Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some (bit (Y ((Nat.unpair v).2/2)))) := by
    exact _root_.OAI.TuringRigidity.UniformOracle.total_comp (f := fun input => bit (Y input)) hquery (_root_.OAI.TuringRigidity.UniformOracle.total_primrec half)
  have hv := _root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec val) hq
  have heq : Primrec (fun v : ℕ => if (Nat.unpair v).1 = (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp f r) (Primrec.const 1) (Primrec.const 0)
  have hy : RecursivePred Y (fun v => (table (Nat.unpair (Nat.unpair v).1).2).getD (Nat.unpair v).2 0 =
      bit (Y ((Nat.unpair v).2/2))) := by
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec heq) hv).of_eq (fun v => by simp [bit])
  have hi := Form.or (n := 0) (s := true) (recursive_and ho (recursive_and hb hp))
    (recursive_and (recursive_not ho) hy)
  apply Form.congr (n := 0) (s := true) (recursive_bounded_all hi (Primrec.list_length.comp (table_primrec.comp r)))
  intro v
  simp only [Agrees,Nat.unpair_pair]
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  cases i.bodd <;> simp

theorem certificate_recursive (Y : Oracle) : RecursivePred Y (Certificate Y) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have ha := recursive_comp (agrees_recursive Y) (Primrec₂.natPair.comp (r.comp f) (f.comp r))
  have he := Nat.Partrec.Code.primrec_evaln.comp
    (((r.comp r).pair (machine_primrec.comp (f.comp (f.comp f)))).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp (table_primrec.comp (f.comp r))) (r.comp (f.comp f))))
  unfold Certificate
  simpa only [Nat.unpair_pair] using recursive_and ha (recursive_primrecPred Y
    (Primrec.eq.comp (Primrec.option_isSome.comp he) (Primrec.const true)))

theorem openHalts_sigma (Y : Oracle) : Sigma Y 1 (fun v => OpenHalts Y (Nat.unpair v).1 (Nat.unpair v).2) := by
  simpa only [OpenHalts,Nat.pair_unpair] using exists_form (n := 0) (certificate_recursive Y)

theorem initial_getD (G : Oracle) {m i : ℕ} (hi : i < m) : (initial G m).getD i false = G i := by
  simp [initial,List.getD_eq_getElem?_getD,List.getElem?_range hi]

theorem initial_prefix (G : Oracle) (m : ℕ) : Prefix G (initial G m) := by
  intro i hi
  exact (initial_getD G (by simpa using hi)).symm

theorem prefix_initial {G : Oracle} {p : List Bool} (hp : Prefix G p) : p = initial G p.length := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have h := hp i hi
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi, initial, hi] using h.symm

theorem initial_mono (G : Oracle) {m n : ℕ} (h : m ≤ n) : initial G m <+: initial G n := by
  exact (List.prefix_iff_eq_take.mpr (by simp [initial,← List.map_take,List.take_range,min_eq_left h]))

theorem agrees_table {Y G : Oracle} {p : List Bool} {L : List ℕ}
    (hp : Prefix G p) (h : Agrees Y p L) : L = oraclePrefix (fun i => bit (join Y G i)) L.length := by
  apply List.ext_getElem
  · simp [oraclePrefix]
  · intro i hi hj
    have hh := h i hi
    have he : L.getD i 0 = bit (join Y G i) := by
      cases hb : i.bodd with
      | false => simpa [hb,join] using hh
      | true =>
        simp only [hb,↓reduceIte] at hh
        simpa [join,hb,hp (i/2) hh.1] using hh.2
    simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,oraclePrefix,hi] using he

theorem openHalts_sound {Y G : Oracle} {x : ℕ} {p : List Bool}
    (hp : Prefix G p) (h : OpenHalts Y x (encode p)) : Halts (join Y G) (Nat.unpair x).1 (Nat.unpair x).2 := by
  obtain ⟨z,ha,hh⟩ := h
  simp only [Nat.unpair_pair,word,encodek,Option.getD_some] at ha hh
  obtain ⟨a,ha'⟩ := Option.isSome_iff_exists.mp hh
  refine ⟨Nat.pair (table (Nat.unpair z).1).length (Nat.unpair z).2,a,?_⟩
  have ht := agrees_table hp ha
  simpa only [TableIndices.run,trial,Nat.unpair_pair,← ht] using Option.mem_def.mpr ha'

theorem openHalts_complete {Y G : Oracle} {x : ℕ}
    (h : Halts (join Y G) (Nat.unpair x).1 (Nat.unpair x).2) :
    ∃ m, OpenHalts Y x (encode (initial G m)) := by
  obtain ⟨z,a,ha⟩ := h
  let m := (Nat.unpair z).1
  let L := oraclePrefix (fun i => bit (join Y G i)) m
  refine ⟨m,Nat.pair (encode L) (Nat.unpair z).2,?_,?_⟩
  · simp only [Nat.unpair_pair,word,table,encodek,Option.getD_some]
    intro i hi
    have him : i < m := by simpa [L,oraclePrefix] using hi
    have hh : i/2 < m := (Nat.div_le_self i 2).trans_lt him
    have hv : L.getD i 0 = bit (join Y G i) := by
      simp [L,oraclePrefix,List.getD_eq_getElem?_getD,List.getElem?_range him]
    cases hb : i.bodd with
    | false => simpa only [hb,Bool.false_eq_true,↓reduceIte,join] using hv
    | true =>
      simp only [↓reduceIte]
      exact ⟨by simpa using hh, by rw [hv,join,ite_eq_left hb,initial_getD G hh]⟩
  · simp only [Nat.unpair_pair,table,encodek,Option.getD_some]
    exact Option.isSome_iff_exists.mpr ⟨a,ha⟩

theorem openHalts_mono {Y : Oracle} {x : ℕ} {p q : List Bool}
    (hpq : p <+: q) (h : OpenHalts Y x (encode p)) : OpenHalts Y x (encode q) := by
  obtain ⟨z,ha,hh⟩ := h
  refine ⟨z,?_,by simpa only [Nat.unpair_pair] using hh⟩
  simp only [Nat.unpair_pair,word,encodek,Option.getD_some] at ha ⊢
  intro i hi
  have hv := ha i hi
  cases hb : i.bodd with
  | false => simpa only [hb,Bool.false_eq_true,↓reduceIte] using hv
  | true =>
    simp only [hb,↓reduceIte] at hv ⊢
    exact ⟨hv.1.trans_le hpq.length_le,hv.2.trans (congrArg bit
      (CodingForcing.getD_of_prefix hpq hv.1).symm)⟩

end TuringRigidity.CohenHalting

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenLowness
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenLowness
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing
open CohenHalting EffectiveCohen EffectiveWitness

theorem recursive_comp_total {Y : Oracle} {P : ℕ → Prop} {f : ℕ → ℕ}
    (hP : RecursivePred Y P)
    (hf : Nat.RecursiveIn {oracleFunction Y} (fun x => Part.some (f x))) :
    RecursivePred Y (fun x => P (f x)) := by
  classical
  exact _root_.OAI.TuringRigidity.UniformOracle.total_comp hP hf

theorem prefix_recursive (G : Oracle) : RecursivePred G (fun p => Prefix G (word p)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hquery : Nat.RecursiveIn {oracleFunction G} (fun v => Part.some (bit (G (Nat.unpair v).2))) := by
    have hq : Nat.RecursiveIn {oracleFunction G} (oracleFunction G) := .oracle _ (Set.mem_singleton _)
    exact _root_.OAI.TuringRigidity.UniformOracle.total_comp (f := fun input => bit (G input)) hq (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r)
  have hv := _root_.OAI.TuringRigidity.UniformOracle.total_pair hquery (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (bit_primrec.comp
    ((Primrec.list_getD false).comp (word_primrec.comp f) r)))
  have he : Primrec (fun v : ℕ => if (Nat.unpair v).1 = (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp f r) (Primrec.const 1) (Primrec.const 0)
  have hh : RecursivePred G (fun v => G (Nat.unpair v).2 = (word (Nat.unpair v).1).getD (Nat.unpair v).2 false) := by
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec he) hv).of_eq (fun v => by
      simp only [Nat.unpair_pair]
      have hb (a b : Bool) : bit a = bit b ↔ a = b := by cases a <;> cases b <;> simp [bit]
      simp only [hb]
      split <;> rfl)
  simpa only [Prefix,Nat.unpair_pair] using
    recursive_bounded_all hh (Primrec.list_length.comp word_primrec)

theorem extension_sigma (Y : Oracle) : Sigma Y 1 (fun v => Extension Y (Nat.unpair v).1 (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := EncodedForcing.prefix_recursive Y (word_primrec.comp (r.comp f)) (word_primrec.comp r)
  have hh := (openHalts_sigma Y).comp (Primrec₂.natPair.comp (f.comp f)
    (Primrec.encode.comp (word_primrec.comp r)))
  simpa only [Extension,Nat.unpair_pair] using ((Form.raise (n := 0) (s := true) hp).and hh).ex

theorem deciding_recursive {Y G : Oracle} (hG : Reduces G (jump Y)) :
    RecursivePred (jump Y) (Deciding Y G) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := recursive_comp (recursive_transfer (prefix_recursive G) hG) r
  have hh := recursive_comp (form_recursive (openHalts_sigma Y))
    (Primrec₂.natPair.comp f (Primrec.encode.comp (word_primrec.comp r)))
  have hn := recursive_not (form_recursive (extension_sigma Y))
  unfold Deciding
  simpa only [Nat.unpair_pair] using recursive_and hp (Form.or (n := 0) (s := true) hh hn)

theorem deciding_total {Y G : Oracle} (hG : OneGeneric Y G) : ∀ x, ∃ p, Deciding Y G (Nat.pair x p) := by
  intro x
  have hh := (openHalts_sigma Y).comp (Primrec₂.natPair.comp (Primrec.const x) Primrec.id)
  obtain ⟨p,hp,hd⟩ := hG.decides hh
  refine ⟨encode p,?_,?_⟩
  · simpa only [Prefix,Nat.unpair_pair,word,encodek,Option.getD_some] using hp
  · simp only [Nat.unpair_pair] at hd
    simp only [Nat.unpair_pair,word,encodek,Option.getD_some]
    rcases hd with hd | hd
    · exact Or.inl hd
    · refine Or.inr ?_
      rintro ⟨q,hpq,hq⟩
      exact hd (word q) (by simpa [word] using hpq) hq

theorem deciding_correct {Y G : Oracle} {x p : ℕ} (h : Deciding Y G (Nat.pair x p)) :
    OpenHalts Y x (encode (word p)) ↔ Halts (join Y G) (Nat.unpair x).1 (Nat.unpair x).2 := by
  obtain ⟨hp,hd⟩ := h
  simp only [Nat.unpair_pair] at hp hd
  refine ⟨openHalts_sound hp,fun hh => ?_⟩
  rcases hd with hd | hd
  · exact hd
  · exfalso
    apply hd
    obtain ⟨m,hm⟩ := openHalts_complete hh
    let n := max m (word p).length
    have hpm : word p <+: initial G n := by
      rw [prefix_initial hp]
      exact initial_mono G (le_max_right _ _)
    exact ⟨encode (initial G n),by simpa [word] using hpm,
      by simpa [word] using openHalts_mono (initial_mono G (le_max_left _ _)) hm⟩

theorem oneGeneric_low {Y G : Oracle} (hrec : Reduces G (jump Y)) (hgen : OneGeneric Y G) :
    Reduces (jump (join Y G)) (jump Y) := by
  let D := Deciding Y G
  let ht := deciding_total hgen
  let pick : ℕ → ℕ := least D ht
  have hpick : Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (pick x)) :=
    least_recursive (deciding_recursive hrec) ht
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hin := _root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id)
    (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.encode.comp word_primrec)) hpick)
  have hh := recursive_comp_total (form_recursive (openHalts_sigma Y)) hin
  apply RecursiveIn.iff_nat.mpr
  apply hh.of_eq
  intro x
  have he := deciding_correct (least_spec D ht x)
  classical
  simp only [Nat.unpair_pair]
  change Part.some (if OpenHalts Y x (encode (word (pick x))) then 1 else 0) = _
  simp only [pick,he,oracleFunction,jump,Bool.decide_iff]

theorem relative_low_generic (Y : Oracle) : ∃ G : Oracle,
    Reduces G (jump Y) ∧ OneGeneric Y G ∧ degree (jump (join Y G)) = degree (jump Y) := by
  refine ⟨generic Y,generic_reduces Y,generic_oneGeneric Y,?_⟩
  exact (degree_eq_iff _ _).mpr ⟨oneGeneric_low (generic_reduces Y) (generic_oneGeneric Y),
    jump_mono (reduces_join_left Y (generic Y))⟩

end TuringRigidity.CohenLowness

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenRun
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing CommonIdeal IndexMatrix

theorem form_transfer {Y Z : Oracle} {n s P} (h : Form Y n s P) (hYZ : Reduces Y Z) :
    Form Z n s P := by
  induction n generalizing s P with
  | zero => exact recursive_transfer h hYZ
  | succ n ih =>
    obtain ⟨Q,hQ,he⟩ := h
    exact ⟨Q,ih hQ,he⟩

theorem run_table (A : Oracle) (e : OracleCode) : ∃ d : Nat.Partrec.Code,
    ∀ p n a, a ∈ CommonIdeal.run A e (word p) n ↔
      ∃ z, a ∈ TableIndices.run A d (Nat.pair (encode (word p)) n) z := by
  obtain ⟨d,hd⟩ := finiteRun_code e []
  refine ⟨d,fun p n a => ?_⟩
  have ha := finiteRun_approximates A e [] (encode (word p)) n
  simp only [BorelGeneric.word,encodek,Option.getD_some,List.nil_append] at ha
  constructor
  · intro h
    obtain ⟨m,hm⟩ := ha.2 a h
    have hh := hm m le_rfl
    dsimp only at hh
    rw [← hd] at hh
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp hh
    exact ⟨Nat.pair m t,by simpa only [TableIndices.run,trial,Nat.unpair_pair] using ht⟩
  · rintro ⟨z,hz⟩
    have hh := Nat.Partrec.Code.evaln_sound hz
    rw [hd] at hh
    exact ha.1 (Nat.unpair z).1 a hh

theorem run_mem_sigma (A : Oracle) (e : OracleCode) : Sigma A 1 (fun v =>
    (Nat.unpair (Nat.unpair v).2).2 ∈ CommonIdeal.run A e (word (Nat.unpair v).1)
      (Nat.unpair (Nat.unpair v).2).1) := by
  obtain ⟨d,hd⟩ := run_table A e
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hr := _root_.OAI.TuringRigidity.UniformOracle.total_comp (run_uniform_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec₂.natPair.comp (Primrec.const (encode d))
      (Primrec₂.natPair.comp (Primrec₂.natPair.comp
        (Primrec.encode.comp (word_primrec.comp (f.comp f))) (f.comp (r.comp f))) r)))
  have heq : Primrec (fun v : ℕ => if (decode (α := Option ℕ) (Nat.unpair v).1).getD none =
      some (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp (Primrec.option_getD.comp (Primrec.decode.comp f) (Primrec.const none))
      (Primrec.option_some.comp r)) (Primrec.const 1) (Primrec.const 0)
  have hcert : RecursivePred A (fun v => (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 ∈
      TableIndices.run A d (Nat.pair (encode (word (Nat.unpair (Nat.unpair v).1).1))
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1) (Nat.unpair v).2) := by
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec heq) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hr (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (r.comp (r.comp f))))).of_eq
      (fun v => by simp [Option.mem_def])
  apply Form.congr (exists_form (n := 0) hcert)
  intro v
  simp only [Nat.unpair_pair]
  exact (hd _ _ _).symm

end TuringRigidity.CohenRun

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ConservativeExtension
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ConservativeExtension
open CommonIdeal

theorem removes_oracle {A Y G : Oracle} {e : OracleCode} {s : List Bool}
    (hG : Extends G s) (hD : Decide A Y e s)
    (he : OracleCode.eval (oracleFunction (join A G)) e = oracleFunction Y) :
    Reduces Y A := by
  have hu : ∀ t, s <+: t → ∀ n a, a ∈ run A e t n → a = bit (Y n) := by
    rcases hD with ⟨n, a, ha, hn⟩ | hD
    · have hh := run_total hG n a ha
      rw [he] at hh
      exact False.elim (hn (Part.mem_some_iff.mp hh))
    · exact hD
  apply common_output_reduces (G := G) (H := G) (p := e) (q := e)
    (s := s) (t := s) hG hG (Or.inr ?_) he he
  intro u v n a b hu' hv' ha hb
  exact (hu u hu' n a ha).trans (hu v hv' n b hb).symm

end TuringRigidity.ConservativeExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenConservative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenConservative
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing
open CohenHalting CohenRun EffectiveCohen CohenLowness

theorem value_ne_recursive (X : Oracle) : RecursivePred X (fun v =>
    (Nat.unpair v).2 ≠ bit (X (Nat.unpair v).1)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hquery : Nat.RecursiveIn {oracleFunction X} (fun v => Part.some (bit (X (Nat.unpair v).1))) := by
    have hq : Nat.RecursiveIn {oracleFunction X} (oracleFunction X) := .oracle _ (Set.mem_singleton _)
    exact _root_.OAI.TuringRigidity.UniformOracle.total_comp (f := fun input => bit (X input)) hq (_root_.OAI.TuringRigidity.UniformOracle.total_primrec f)
  have he : Primrec (fun v : ℕ => if (Nat.unpair v).1 ≠ (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite ((Primrec.eq.comp f r).not) (Primrec.const 1) (Primrec.const 0)
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec he) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r) hquery)).of_eq
    (fun v => by simp only [Nat.unpair_pair]; split <;> rfl)

theorem disagreement_sigma {A X B : Oracle} (hA : Reduces A B) (hX : Reduces X B)
    (e : OracleCode) : Sigma B 1 (fun p => ∃ n a,
      a ∈ CommonIdeal.run A e (word p) n ∧ a ≠ bit (X n)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hr := form_transfer (run_mem_sigma A e) hA
  have hn := recursive_comp (recursive_transfer (value_ne_recursive X) hX) r
  have hh := (hr.and (Form.raise (n := 0) (s := true) hn)).comp
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (r.comp f) r))
  simpa only [Nat.unpair_pair] using hh.ex.ex

theorem oneGeneric_conservative {B G : Oracle} (hG : OneGeneric B G)
    (A X : Oracle) (hA : Reduces A B) (hX : Reduces X B)
    (h : Reduces X (join A G)) : Reduces X A := by
  obtain ⟨e,he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
  obtain ⟨p,hp,hd⟩ := hG.decides (disagreement_sigma hA hX e)
  apply ConservativeExtension.removes_oracle hp (e := e) (s := p) ?_ he
  rcases hd with hd | hd
  · exact Or.inl (by simpa [word] using hd)
  · refine Or.inr (fun q hpq n a ha => ?_)
    by_contra hn
    exact hd q hpq ⟨n,a,by simpa [word] using ha,hn⟩

end TuringRigidity.CohenConservative

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingAgreement
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleEnumeration
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_RecursiveInfiniteSubset
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenColumns
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenColumns
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CohenHalting EffectiveCohen

theorem eraseWord_getD (i : ℕ) (s : List Bool) (m : ℕ) (hm : m < s.length) :
    (eraseWord i s).getD m false = if (Nat.unpair m).1 = i then false else s.getD m false := by
  simp [eraseWord,List.getD_eq_getElem?_getD,List.getElem?_range hm]

theorem eraseWord_primrec (i : ℕ) : Primrec (eraseWord i) := by
  apply Primrec.list_map (Primrec.list_range.comp Primrec.list_length)
  exact Primrec.ite (Primrec.eq.comp ((Primrec.fst.comp Primrec.unpair).comp Primrec.snd) (Primrec.const i))
    (Primrec.const false) ((Primrec.list_getD false).comp Primrec.fst Primrec.snd)

theorem eraseWord_initial (i : ℕ) (G : Oracle) (N : ℕ) :
    eraseWord i (initial G N) = initial (erase i G) N := by
  apply List.ext_getElem
  · simp
  · intro n hn hm
    have hn' : n < N := by simpa using hn
    have h := eraseWord_getD i (initial G N) n (by simpa using hn')
    rw [initial_getD G hn'] at h
    have he := initial_getD (erase i G) hn'
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,
      List.getElem?_eq_getElem hm,Option.getD_some] using h.trans he.symm

theorem eraseWord_prefix {i : ℕ} {G : Oracle} {s : List Bool} (hs : Prefix G s) :
    Prefix (erase i G) (eraseWord i s) := by
  rw [prefix_initial hs,eraseWord_initial]
  exact initial_prefix _ _

theorem eraseWord_set (i : ℕ) (s : List Bool) (m : ℕ) (hi : (Nat.unpair m).1 = i) (b : Bool) :
    eraseWord i (s.set m b) = eraseWord i s := by
  apply List.ext_getElem
  · simp
  · intro n hn hn'
    have hns : n < s.length := by simpa using hn'
    have h₀ := eraseWord_getD i (s.set m b) n (by simpa using hns)
    have h₁ := eraseWord_getD i s n hns
    have he : (eraseWord i (s.set m b)).getD n false = (eraseWord i s).getD n false := by
      rw [h₀,h₁]
      by_cases hni : (Nat.unpair n).1 = i
      · simp only [ite_eq_left hni]
      · have hmn : m ≠ n := by rintro rfl; exact hni hi
        simp only [ite_eq_right hni,List.getD_eq_getElem?_getD,List.getElem?_set_ne hmn]
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,
      List.getElem?_eq_getElem hn',Option.getD_some] using he

theorem disagrees_sigma (B : Oracle) (i : ℕ) (e : OracleCode) : Sigma B 1 (Disagrees B i e) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let p := f.comp f
  let n := r.comp f
  let m := Primrec₂.natPair.comp (Primrec.const i) n
  have hr := (CohenRun.run_mem_sigma B e).comp
    (Primrec₂.natPair.comp (Primrec.encode.comp ((eraseWord_primrec i).comp (word_primrec.comp p)))
      (Primrec₂.natPair.comp n r))
  have hl := recursive_primrecPred B (Primrec.nat_lt.comp m (Primrec.list_length.comp (word_primrec.comp p)))
  have hv := recursive_primrecPred B ((Primrec.eq.comp r (CommonIdeal.bit_primrec.comp
    ((Primrec.list_getD false).comp (word_primrec.comp p) m))).not)
  have h := ((Form.raise (n := 0) (s := true) hl).and (hr.and (Form.raise (n := 0) (s := true) hv))).ex.ex
  apply h.congr
  intro v
  simp only [Disagrees,Nat.unpair_pair,word,encodek,Option.getD_some]

theorem column_not_reduces {B G : Oracle} (hg : OneGeneric B G) (i : ℕ) :
    ¬ Reduces (columns G i) (join B (erase i G)) := by
  intro h
  obtain ⟨e,he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
  obtain ⟨p,hp,hd⟩ := hg.decides (disagrees_sigma B i e)
  rcases hd with ⟨n,a,hlen,ha,hne⟩ | hd
  · have hv := CommonIdeal.run_total (eraseWord_prefix hp) n a (by simpa [word] using ha)
    rw [he] at hv
    have hav : a = CommonIdeal.bit (G (Nat.pair i n)) := Part.mem_some_iff.mp hv
    apply hne
    rw [hav]
    simpa only [word,encodek,Option.getD_some] using congrArg CommonIdeal.bit (hp _ (by simpa [word] using hlen))
  · let n := p.length
    let m := Nat.pair i n
    have hm : p.length ≤ m := Nat.right_le_pair i n
    have hv : CommonIdeal.bit (G m) ∈ OracleCode.eval (oracleFunction (join B (erase i G))) e n := by
      rw [he]; exact Part.mem_some _
    obtain ⟨L,hL⟩ := (CommonIdeal.run_approximates B (erase i G) e n).2 _ hv
    let N := max (m+1) L
    let q := initial G N
    have hN : m < N := (Nat.lt_succ_self m).trans_le (le_max_left _ _)
    have hpq : p <+: q := by
      rw [prefix_initial hp]
      exact initial_mono G (hm.trans (Nat.le_of_lt hN))
    have hrun : CommonIdeal.bit (G m) ∈ CommonIdeal.run B e (eraseWord i q) n := by
      rw [show eraseWord i q = initial (erase i G) N from eraseWord_initial i G N]
      exact hL N (le_max_right _ _)
    let q' := q.set m (!(G m))
    have hpq' : p <+: q' := CodingOnePoint.prefix_set_of_le hpq m hm _
    apply hd q' hpq'
    refine ⟨n,CommonIdeal.bit (G m),?_,?_,?_⟩
    · simpa [word,q',q,m] using hN
    · have heq : eraseWord i q' = eraseWord i q := eraseWord_set i q m (by simp [m]) _
      simpa only [word,encodek,Option.getD_some,heq] using hrun
    · have hbit : q'.getD m false = !(G m) := by
        simp [q',List.getD_eq_getElem?_getD,show m < q.length by simpa [q] using hN]
      simp only [word,encodek,Option.getD_some]
      change CommonIdeal.bit (G m) ≠ CommonIdeal.bit (q'.getD m false)
      rw [hbit]
      cases G m <;> decide

theorem column_reduces_erase (G : Oracle) (i j : ℕ) (hji : j ≠ i) :
    Reduces (columns G j) (erase i G) := by
  have he : columns (erase i G) j = columns G j := by
    funext n
    simp [columns,erase,hji]
  rw [← he]
  exact CodingExtraction.column_projection_reduces _ _

theorem finite_conservative {B G : Oracle} (hg : OneGeneric B G) (F : Finset ℕ)
    (a y : Degree) (ha : a ≤ degree B) (hy : y ≤ degree B)
    (h : y ≤ a ⊔ F.sup (fun i => degree (columns G i))) : y ≤ a := by
  obtain ⟨A,rfl⟩ := degree_surjective a
  obtain ⟨Y,rfl⟩ := degree_surjective y
  apply CohenConservative.oneGeneric_conservative hg A Y ha hy
  change degree Y ≤ degree A ⊔ degree G
  apply le_trans h
  apply sup_le_sup_left
  apply Finset.sup_le
  intro i _
  exact CodingExtraction.column_projection_reduces G i

theorem independence {B G : Oracle} (hg : OneGeneric B G)
    (a₀ a₁ : Degree) (h₀ : a₀ ≤ degree B) (h₁ : a₁ ≤ degree B)
    (i : ℕ) (F : Finset ℕ) :
    a₀ ⊔ degree (columns G i) ≤ a₁ ⊔ F.sup (fun j => degree (columns G j)) ↔
      a₀ ≤ a₁ ∧ i ∈ F := by
  constructor
  · intro h
    refine ⟨finite_conservative hg F a₁ a₀ h₁ h₀ (le_sup_left.trans h),?_⟩
    by_contra hi
    apply column_not_reduces hg i
    change degree (columns G i) ≤ degree B ⊔ degree (erase i G)
    apply le_trans le_sup_right (le_trans h (sup_le_sup h₁ ?_))
    apply Finset.sup_le
    intro j hj
    exact column_reduces_erase G i j (fun he => hi (he ▸ hj))
  · rintro ⟨ha,hi⟩
    exact sup_le_sup ha (Finset.le_sup (f := fun j => degree (columns G j)) hi)

end TuringRigidity.CohenColumns

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingColumns
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteInjury
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_NormalizedRecovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NormalizedRecovery
open EncodedForcing Encodable UniformOracle Introreducible StageNormalization

theorem trial_recursive (B : Oracle) :
    Nat.RecursiveIn {oracleFunction B} (fun v => Part.some (encode (trial B (Nat.unpair v).1 (Nat.unpair v).2))) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hq : Nat.RecursiveIn {oracleFunction B} (oracleFunction B) := .oracle _ (Set.mem_singleton _)
  have hb := _root_.OAI.TuringRigidity.UniformOracle.total_comp hq (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp (f.comp f) r))
  let n := r.comp (f.comp f)
  let c := r.comp f
  have hpost := Primrec.encode.comp (Primrec.ite
    ((Primrec.eq.comp r (Primrec.const 1)).and (Primrec.nat_lt.comp n (codeLength_primrec.comp c)))
    (Primrec.option_some.comp (codeBit_primrec.comp n c)) (Primrec.const none))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hpost) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id) hb)).of_eq
    (fun v => by cases h : B (Nat.pair (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair v).2) <;>
      simp [trial,h])

theorem normalized_inverse (A : Oracle) : Reduces A (normalized A) := by
  apply RecursiveIn.iff_nat.mpr
  change Nat.RecursiveIn {oracleFunction (normalized A)} (fun n => Part.some (bit A n))
  apply total_search (trial_recursive (normalized A)) (bit A)
  · intro n c a ha
    simp only [trial] at ha
    split at ha
    next h =>
      have he : prefixCode (columns A (Nat.unpair n).1) (codeLength c) = c := by
        simpa [normalized,prefixSet] using h.1
      have ha' : a = codeBit (Nat.unpair n).2 c := (Option.mem_some_iff.mp ha).symm
      rw [ha',← he,codeBit_prefix _ _ _ h.2]
      simp [bit,columns,Nat.pair_unpair]
    next h => simp at ha
  · intro n
    let c := prefixCode (columns A (Nat.unpair n).1) ((Nat.unpair n).2+1)
    refine ⟨c,codeBit (Nat.unpair n).2 c,?_⟩
    simp [trial,normalized,c]

end TuringRigidity.NormalizedRecovery

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingRequirements
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_CodingBounds
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDecoding
open SetCoding RelationCoding ArithmeticModelDecoding

theorem AntichainBelow.mono {p : AntichainCode} {x y : Degree} (hp : AntichainBelow p x) (h : x ≤ y) :
    AntichainBelow p y := ⟨hp.1.trans h,hp.2.1.trans h,hp.2.2.trans h⟩

theorem SetBelow.mono {p : SetCode} {x y : Degree} (hp : SetBelow p x) (h : x ≤ y) :
    SetBelow p y := ⟨hp.1.trans h,hp.2.1.mono h,hp.2.2.mono h⟩

theorem RelationBelow.mono {n : ℕ} {p : RelationCode n} {x y : Degree}
    (hp : RelationBelow p x) (h : x ≤ y) : RelationBelow p y :=
  ⟨fun i => (hp.1 i).mono h,hp.2.mono h⟩

end TuringRigidity.BoundedDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_StablePair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.StablePair
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness IndexMatrix
open CodingForcing UniformProgram UniformAgreement UniformPair

theorem decisive_excludes_common {A Y G₀ G₁ Z : Oracle} {x : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item x 0))) = oracleFunction Y)
    (h₀ : CommonIdeal.Extends G₀ p.left) (h₁ : CommonIdeal.Extends G₁ p.right)
    (he₀ : OracleCode.eval (oracleFunction (join Y G₀)) (meaning (machine (item x 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y G₁)) (meaning (machine (item x 2))) = oracleFunction Z)
    (hd : Decisive A x p) : False := by
  have hr (i : ℕ) (s : List Bool) (n : ℕ) :
      UniformRun.run A (machine (item x 0)) (machine (item x i)) s n =
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
      obtain ⟨q,hpq,hq⟩ := CodingForcing.arbitrary_left_extension (columns A) p s hs
      have hh := hdiv q hpq (CommonIdeal.bit (Z n))
      simp only [↓reduceIte,hr,hq] at hh
      exact hh hv
    · obtain ⟨s,hs,hv⟩ := CommonIdeal.run_finite_extension h₁ n (CommonIdeal.bit (Z n)) (by
        rw [he₁]; exact Part.mem_some _)
      obtain ⟨q,hpq,hq⟩ := CodingRequirements.arbitrary_right_extension (columns A) p s hs
      have hh := hdiv q hpq (CommonIdeal.bit (Z n))
      simp only [show (2 : ℕ) ≠ 1 by decide,↓reduceIte,hr,hq] at hh
      exact hh hv

end TuringRigidity.StablePair

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedStage
open Encodable CodingForcing EncodedForcing FiniteInjury
noncomputable section
attribute [local instance] Classical.propDecidable

theorem pairProcedure_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (pairProcedure A v)) :=
  (Classical.choose_spec (GuardedPair.pair_exists A)).1

theorem candidate_extends (A : Oracle) (t : ℕ) (p : Condition) :
    Extends (columns A) (atLevel p t) (candidate A t p) := by
  have h := ((Classical.choose_spec (GuardedPair.pair_exists A)).2 t (code (atLevel p t))).1
  rw [condition_code] at h
  exact ⟨h.1,h.2.1,le_rfl,h.2.2.2⟩

theorem scan_spec {A : Oracle} {p : Condition} {done : Finset ℕ} {t n i : ℕ}
    (h : scan A p done t n = some i) :
    t ≤ i ∧ i < t+n ∧ i ∉ done ∧ Changes A i p := by
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

theorem open_extends (A : Oracle) (e : ℕ) (p : Condition) :
    Extends (columns A) p (condition (openProcedure A (Nat.pair e (code p)))) := by
  have h := ((Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl A))).2 e (code p)).1
  simpa only [condition_code,openProcedure] using h

theorem action_not_done (A : Oracle) (s : ℕ) (p : State) (t : ℕ)
    (h : stageAction A s p = some t) : t ∉ p.done := (scan_spec h).2.2.1

theorem accept_action (A : Oracle) (s : ℕ) (p : State) :
    FiniteInjury.accept p.done (stageAction A s p) = stageAction A s p := by
  cases ha : stageAction A s p with
  | none => simp [FiniteInjury.accept]
  | some t => simp [FiniteInjury.accept,action_not_done A s p t ha]

theorem done_eq (A : Oracle) (s : ℕ) :
    (construction A s).done = FiniteInjury.state (proposal A) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change FiniteInjury.update (construction A s).done (stageAction A s (construction A s)) = _
    rw [FiniteInjury.state]
    rw [← ih]
    simp only [proposal,accept_action]

theorem action_eq (A : Oracle) (s : ℕ) :
    FiniteInjury.action (proposal A) s = stageAction A s (construction A s) := by
  rw [FiniteInjury.action,← done_eq]
  exact accept_action A s _

theorem seen_eq (A : Oracle) (s : ℕ) :
    (construction A s).seen = FiniteInjurySchedule.seen (proposal A) s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    change FiniteInjurySchedule.reset _ _ = _
    rw [FiniteInjurySchedule.seen,action_eq,← ih]

theorem active_eq (A : Oracle) (s : ℕ) : (conditions A s).active = s := by
  cases s <;> rfl

theorem stage_words (A : Oracle) (s : ℕ) (p : State) :
    p.condition.left <+: (stageWord A s p).left ∧ p.condition.right <+: (stageWord A s p).right := by
  have ho := open_extends A (FiniteInjurySchedule.visit p.seen) p.condition
  cases ha : stageAction A s p with
  | none => exact ⟨by simpa [stageWord,ha,generic] using ho.1,by simpa [stageWord,ha,generic] using ho.2.1⟩
  | some t =>
    have hc := candidate_extends A t (generic A p)
    exact ⟨by simpa [stageWord,ha] using ho.1.trans hc.1,
      by simpa [stageWord,ha] using ho.2.1.trans hc.2.1⟩

theorem word_growth (A : Oracle) (s : ℕ) :
    (conditions A s).left <+: (conditions A (s+1)).left ∧
    (conditions A s).right <+: (conditions A (s+1)).right := by
  have h := stage_words A s (construction A s)
  exact ⟨h.1.trans (List.prefix_append _ _),h.2.trans (List.prefix_append _ _)⟩

theorem length_bound (A : Oracle) (s : ℕ) : s ≤ (conditions A s).left.length := by
  induction s with
  | zero => exact Nat.zero_le _
  | succ s ih =>
    have h := (stage_words A s (construction A s)).1.length_le
    change s+1 ≤ ((stageWord A s (construction A s)).left ++ [false]).length
    simp only [List.length_append,List.length_singleton]
    exact Nat.add_le_add_right (ih.trans h) 1

theorem level_step (A : Oracle) (s k : ℕ) (hk : k ≤ s)
    (hact : ∀ t, FiniteInjury.action (proposal A) s = some t → k ≤ t) :
    Extends (columns A) (atLevel (conditions A s) k) (atLevel (conditions A (s+1)) k) := by
  let p := construction A s
  have ho := open_extends A (FiniteInjurySchedule.visit p.seen) p.condition
  have hg : Extends (columns A) (atLevel p.condition k) (atLevel (generic A p) k) := by
    refine ⟨ho.1,ho.2.1,le_rfl,?_⟩
    intro m hm hlen
    apply ho.2.2.2 m ⟨hm.1,?_,hm.2.2⟩ hlen
    exact hm.2.1.trans_le (by
      change k ≤ (conditions A s).active
      rw [active_eq]
      exact hk)
  have hw : Extends (columns A) (atLevel (generic A p) k) (atLevel (stageWord A s p) k) := by
    cases ha : stageAction A s p with
    | none => simpa [stageWord,ha] using extends_refl (columns A) (atLevel (generic A p) k)
    | some t =>
      have hkt : k ≤ t := hact t (by simpa [action_eq,p] using ha)
      have hc := candidate_extends A t (generic A p)
      have hc' : Extends (columns A) (atLevel (generic A p) t) (atLevel (candidate A t (generic A p)) t) := hc
      simpa [stageWord,ha] using level_mono hc' hkt
  have htail : Extends (columns A) (atLevel (stageWord A s p) k)
      (atLevel (conditions A (s+1)) k) := append_extends _ _ [false]
  exact extends_trans hg (extends_trans hw htail)

theorem surviving_columns (A : Oracle) (k : ℕ) : ∃ S, ∀ m,
    (conditions A S).left.length ≤ m → (Nat.unpair m).1 < k →
    columns A (Nat.unpair m).1 (Nat.unpair m).2 = true →
    leftLimit (conditions A) m = rightLimit (conditions A) m :=
  eventual_column_agreement (columns A) (proposal A) (conditions A)
    (word_growth A) (length_bound A) (level_step A) k

theorem surviving_generic_visit (A : Oracle) (t : ℕ) : ∃ s,
    FiniteInjurySchedule.visit (construction A s).seen = t ∧
      ∀ u, s ≤ u → ∀ i < t, stageAction A u (construction A u) ≠ some i := by
  obtain ⟨s,hs,hh⟩ := FiniteInjurySchedule.surviving_visit (proposal A) t
  refine ⟨s,?_,?_⟩
  · simpa [seen_eq,FiniteInjurySchedule.scheduled] using hs
  · simpa only [action_eq] using hh

end
end TuringRigidity.GuardedStage

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedScan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

theorem levelCode_primrec : Primrec₂ levelCode := Primrec₂.natPair.comp
  (Primrec.encode.comp (left_primrec.comp Primrec.fst))
  (Primrec₂.natPair.comp (Primrec.encode.comp (right_primrec.comp Primrec.fst)) Primrec.snd)

theorem levelCode_eq (p t : ℕ) : levelCode p t = code (atLevel (condition p) t) := rfl

theorem candidate_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (candidate A v)) := by
  have h := _root_.OAI.TuringRigidity.UniformOracle.total_comp (GuardedStage.pairProcedure_recursive A)
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp f (levelCode_primrec.comp r f)))
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (levelCode_primrec.comp f r)) (_root_.OAI.TuringRigidity.UniformOracle.total_pair h (_root_.OAI.TuringRigidity.UniformOracle.total_primrec f))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

@[simp] theorem candidate_eq (A : Oracle) (t p : ℕ) :
    condition (candidate A (Nat.pair t p)) = GuardedStage.candidate A t (condition p) := by
  simp only [candidate,Nat.unpair_pair,levelCode_eq,GuardedStage.candidate,condition_code]

theorem scanStep_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (scanStep A v)) := by
  have hc := _root_.OAI.TuringRigidity.UniformOracle.total_comp (candidate_recursive A)
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

theorem scan_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v =>
      Part.some (scan A (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2)) := by
  simpa only [scan,Nat.pair_unpair] using recur_recursive (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.const 0)) (scanStep_recursive A)

theorem source_scan_succ (A : Oracle) (p : Condition) (d : Finset ℕ) (t n : ℕ) :
    GuardedStage.scan A p d t (n+1) =
      match GuardedStage.scan A p d t n with
      | some i => some i
      | none => if t+n ∉ d ∧ GuardedStage.Changes A (t+n) p then some (t+n) else none := by
  induction n generalizing t with
  | zero => simp [GuardedStage.scan]
  | succ n ih =>
    change (if t ∉ d ∧ GuardedStage.Changes A t p then some t else GuardedStage.scan A p d (t+1) (n+1)) =
      match (if t ∉ d ∧ GuardedStage.Changes A t p then some t else GuardedStage.scan A p d (t+1) n) with
      | some i => some i
      | none => if t+(n+1) ∉ d ∧ GuardedStage.Changes A (t+(n+1)) p then some (t+(n+1)) else none
    by_cases ht : t ∉ d ∧ GuardedStage.Changes A t p
    · simp only [ite_eq_left ht]
    · simpa only [ite_eq_right ht,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1)

theorem scan_eq (A : Oracle) (p d n : ℕ) :
    scan A p d n = actionCode (GuardedStage.scan A (condition p) (members d) 0 n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [source_scan_succ]
    change scanStep A (Nat.pair (Nat.pair p d) (Nat.pair n (scan A p d n))) = _
    simp only [scanStep,Nat.unpair_pair,ih,Nat.zero_add]
    have hc : left (candidate A (Nat.pair n p)) ≠ left p ∨
        right (candidate A (Nat.pair n p)) ≠ right p ↔ GuardedStage.Changes A n (condition p) := by
      change (condition (candidate A (Nat.pair n p))).left ≠ (condition p).left ∨
        (condition (candidate A (Nat.pair n p))).right ≠ (condition p).right ↔ _
      rw [candidate_eq]
      rfl
    cases he : GuardedStage.scan A (condition p) (members d) 0 n with
    | none =>
      by_cases hn : n ∉ record d ∧ GuardedStage.Changes A n (condition p)
      · simp_all only [actionCode,members,List.mem_toFinset,true_and]; simp
      · simp_all only [actionCode,members,List.mem_toFinset,true_and]; simp
    | some i => simp [actionCode]

end
end TuringRigidity.GuardedComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedComputability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedComputability
open Encodable UniformOracle EncodedForcing CodingForcing FiniteInjury StageRecords
noncomputable section
attribute [local instance] Classical.propDecidable

theorem open_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (GuardedStage.openProcedure A v)) :=
  (Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl A))).1

theorem generic_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun v => Part.some (genericCanonical A v)) := by
  have hn := _root_.OAI.TuringRigidity.UniformOracle.total_comp (nextVisit_recursive (O := {oracleFunction (OracleJump.jump A)})) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (r.comp r))
  have hp := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction (OracleJump.jump A)}) ((levelCode_primrec.comp Primrec.id active_primrec).comp f)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (open_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hn hp)
  exact hh.of_eq (fun v => rfl)

theorem stageAction_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z =>
      Part.some (stageAction A (Nat.unpair z).1 (Nat.unpair z).2)) := by
  have hg := _root_.OAI.TuringRigidity.UniformOracle.total_comp (generic_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (scan_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_pair hg (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (f.comp (r.comp r)))) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec f))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

@[simp] theorem stageAction_eq (A : Oracle) (s v : ℕ) :
    action (stageAction A s v) = GuardedStage.stageAction A s (state v) := by
  rw [stageAction,scan_eq,action_actionCode,generic_eq]
  rfl

theorem stageWord_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z => Part.some (stageWord A z)) := by
  have ha := stageAction_recursive A
  have hg := _root_.OAI.TuringRigidity.UniformOracle.total_comp (generic_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r)
  have hc := _root_.OAI.TuringRigidity.UniformOracle.total_comp (candidate_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_pair
    (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))) ha) hg)
  have hpost := Primrec.ite (Primrec.eq.comp f (Primrec.const 0)) (f.comp r) (r.comp r)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hpost) (_root_.OAI.TuringRigidity.UniformOracle.total_pair ha (_root_.OAI.TuringRigidity.UniformOracle.total_pair hg hc))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem stageWord_eq (A : Oracle) (s v : ℕ) :
    condition (stageWord A (Nat.pair s v)) = GuardedStage.stageWord A s (state v) := by
  have he := stageAction_eq A s v
  unfold stageWord
  simp only [Nat.unpair_pair]
  by_cases ha : stageAction A s v = 0
  · have hn : GuardedStage.stageAction A s (state v) = none := by simpa only [StageRecords.action,ite_eq_left ha] using he.symm
    simp [ha,GuardedStage.stageWord,hn,generic_eq]
  · have hn : GuardedStage.stageAction A s (state v) = some (stageAction A s v-1) := by
      simpa only [StageRecords.action,ite_eq_right ha] using he.symm
    simp [ha,GuardedStage.stageWord,hn,candidate_eq,generic_eq]

theorem grow_primrec : Primrec₂ grow := Primrec₂.natPair.comp
  (Primrec.encode.comp (Primrec.list_append.comp (left_primrec.comp Primrec.fst) (Primrec.const [false])))
  (Primrec₂.natPair.comp
    (Primrec.encode.comp (Primrec.list_append.comp (right_primrec.comp Primrec.fst) (Primrec.const [false])))
    (Primrec.succ.comp Primrec.snd))

theorem advance_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun z => Part.some (advance A z)) := by
  have ha := stageAction_recursive A
  have hw := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (grow_primrec.comp f r))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (stageWord_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec f))
  have hd := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (doneUpdate_primrec.comp f r))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (f.comp (r.comp r))) ha)
  have hs := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction (OracleJump.jump A)}) (r.comp (r.comp r))
  have hn := _root_.OAI.TuringRigidity.UniformOracle.total_comp nextVisit_recursive hs
  have hi := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (seenInsert_primrec.comp f r)) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hs hn)
  have hreset := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (seenReset_primrec.comp f r)) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hi ha)
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_pair hw (_root_.OAI.TuringRigidity.UniformOracle.total_pair hd hreset)
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem advance_eq (A : Oracle) (s v : ℕ) :
    state (advance A (Nat.pair s v)) = GuardedStage.advance A s (state v) := by
  unfold state advance
  simp only [Nat.unpair_pair,condition_grow,stageWord_eq,members_doneUpdate,
    members_seenReset,members_seenInsert,stageAction_eq]
  rfl

theorem construction_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)} (fun s => Part.some (construction A s)) := by
  have h := recur_recursive (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.const initial))
    (_root_.OAI.TuringRigidity.UniformOracle.total_comp (advance_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r))
  have hh := _root_.OAI.TuringRigidity.UniformOracle.total_comp h (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id))
  exact hh.of_eq (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem construction_eq (A : Oracle) (s : ℕ) :
    state (construction A s) = GuardedStage.construction A s := by
  induction s with
  | zero => simp [construction,recur,initial,state,condition_code,members,record,GuardedStage.construction]
  | succ s ih =>
    change state (advance A (Nat.unpair (Nat.pair 0 (Nat.pair s (construction A s)))).2) = _
    rw [Nat.unpair_pair,advance_eq,ih]
    rfl

theorem conditions_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (OracleJump.jump A)}
      (fun s => Part.some (code (GuardedStage.conditions A s))) := by
  have h := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec ((levelCode_primrec.comp Primrec.id active_primrec).comp f))
    (construction_recursive A)
  apply h.of_eq
  intro s
  change Part.some (code (state (construction A s)).condition) = _
  rw [construction_eq]
  rfl

theorem limits_recursive (A : Oracle) :
    Reduces (join (leftLimit (GuardedStage.conditions A)) (rightLimit (GuardedStage.conditions A)))
      (OracleJump.jump A) := by
  have hs := _root_.OAI.TuringRigidity.UniformOracle.total_comp (conditions_recursive A) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.succ.comp Primrec.nat_div2))
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
end TuringRigidity.GuardedComputability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedLimits
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing FiniteInjury
open GuardedStage
noncomputable section
attribute [local instance] Classical.propDecidable

theorem generic_prefix_next (A : Oracle) (s : ℕ) :
    (generic A (construction A s)).left <+: (conditions A (s+1)).left ∧
    (generic A (construction A s)).right <+: (conditions A (s+1)).right := by
  have h : (generic A (construction A s)).left <+: (stageWord A s (construction A s)).left ∧
      (generic A (construction A s)).right <+: (stageWord A s (construction A s)).right := by
    cases ha : stageAction A s (construction A s) with
    | none => simp [stageWord,ha]
    | some t =>
      have hc := candidate_extends A t (generic A (construction A s))
      exact ⟨by simpa [stageWord,ha,atLevel] using hc.1,by simpa [stageWord,ha,atLevel] using hc.2.1⟩
  exact ⟨h.1.trans (List.prefix_append _ _),h.2.trans (List.prefix_append _ _)⟩

theorem limits_extend_generic (A : Oracle) (s : ℕ) :
    CommonIdeal.Extends (G₀ A) (generic A (construction A s)).left ∧
    CommonIdeal.Extends (G₁ A) (generic A (construction A s)).right := by
  have hp := generic_prefix_next A s
  constructor
  · intro m hm
    have hh := (limits_extend (word_growth A) (length_bound A) (s+1) m (hm.trans_le hp.1.length_le)).1
    exact hh.trans (getD_of_prefix hp.1 hm)
  · intro m hm
    have hn : m < (conditions A (s+1)).left.length := by
      rw [(conditions A (s+1)).sameLength]
      exact hm.trans_le hp.2.length_le
    have hh := (limits_extend (word_growth A) (length_bound A) (s+1) m hn).2
    exact hh.trans (getD_of_prefix hp.2 hm)

theorem meets_dense (A : Oracle) {P : ℕ → Prop} (hP : Sigma A 1 P)
    (hdense : ∀ p : Condition, ∃ q : ℕ, Extends (columns A) p (condition q) ∧ P q) :
    ∃ q : ℕ, P q ∧ CommonIdeal.Extends (G₀ A) (condition q).left ∧
      CommonIdeal.Extends (G₁ A) (condition q).right := by
  obtain ⟨e,he⟩ := EffectiveCohen.sigma1_enumeration hP
  obtain ⟨s,hs,_⟩ := surviving_generic_visit A e
  let p := construction A s
  let q := openProcedure A (Nat.pair e (code p.condition))
  have hdec := ((Classical.choose_spec (EffectiveForcing.uniform_open_decision A A (reduces_refl A))).2
    e (code p.condition)).2
  change OracleJump.Halts A e q ∨
    (∀ r, Extends (columns A) (condition q) (condition r) → ¬ OracleJump.Halts A e r) at hdec
  have hq : P q := by
    rcases hdec with h | h
    · exact (he q).mpr h
    · obtain ⟨r,hr,hR⟩ := hdense (condition q)
      exact False.elim (h r hr ((he r).mp hR))
  refine ⟨q,hq,?_⟩
  have hh := limits_extend_generic A s
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

theorem reads_not_reduces (A : Oracle) (loc : ℕ → ℕ)
    (hloc : Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (loc n)))
    (hunbounded : ∀ N, ∃ n, N ≤ loc n) : ¬ Reduces (fun n => G₀ A (loc n)) A := by
  intro hX
  let X : Oracle := fun n => G₀ A (loc n)
  have hP : Sigma A 1 (fun p => ∃ n, loc n < (left p).length ∧ (left p).getD (loc n) false ≠ X n) := by
    simpa only [Nat.unpair_pair] using
      (Form.raise (n := 0) (s := true) (disagreement_recursive A X loc hloc hX)).ex
  have hdense : ∀ p : Condition, ∃ q : ℕ, Extends (columns A) p (condition q) ∧
      ∃ n, loc n < (left q).length ∧ (left q).getD (loc n) false ≠ X n := by
    intro p
    obtain ⟨n,hn⟩ := hunbounded p.left.length
    obtain ⟨q,hpq,hql,hqb⟩ := CodingDiagonal.prescribe (columns A) p (loc n) hn (!(X n))
    refine ⟨code q,by simpa [condition_code] using hpq,n,?_,?_⟩
    · simpa only [show left (code q) = q.left from congrArg Condition.left (condition_code q)] using hql
    · rw [show left (code q) = q.left from congrArg Condition.left (condition_code q),hqb]
      cases X n <;> decide
  obtain ⟨q,⟨n,hn,hne⟩,hl,_⟩ := meets_dense A hP hdense
  exact hne (hl (loc n) hn).symm

theorem common_noncomputable_columns (A : Oracle)
    (hA : ∀ k, {a | columns A k a = true}.Infinite) :
    ∀ k, ∃ C : Oracle, Reduces C (join (G₀ A) (columns A k)) ∧
      Reduces C (join (G₁ A) (columns A k)) ∧ ¬ Reduces C (columns A k) := by
  intro k
  obtain ⟨S,hS⟩ := surviving_columns A (k+1)
  let cutoff := (conditions A S).left.length
  let loc := CodingColumns.location (columns A k) (hA k) k cutoff
  have hcol : Reduces (columns A k) A := CodingExtraction.column_projection_reduces A k
  have hloc : Nat.RecursiveIn {oracleFunction A} (fun n => Part.some (loc n)) :=
    (CodingColumns.location_recursive (columns A k) (hA k) k cutoff).subst (fun f hf => by
      have he : f = oracleFunction (columns A k) := Set.mem_singleton_iff.mp hf
      subst f
      exact RecursiveIn.iff_nat.mp hcol)
  have hn := reads_not_reduces A loc hloc (fun N => ⟨N,CodingColumns.le_location _ _ _ _ _⟩)
  let C := CodingColumns.readColumn (columns A k) (hA k) k cutoff (G₀ A)
  have heq : C = CodingColumns.readColumn (columns A k) (hA k) k cutoff (G₁ A) := by
    funext n
    have hm := CodingColumns.location_mem (columns A k) (hA k) k cutoff n
    simp only [CodingColumns.column] at hm
    split at hm
    next h =>
      apply hS _ h.1
      · rw [h.2]; omega
      · simpa only [h.2] using hm
    next h => simp at hm
  exact ⟨C,CodingColumns.readColumn_reduces _ _ _ _ _,
    heq ▸ CodingColumns.readColumn_reduces _ _ _ _ _,fun h => hn (reduces_trans h hcol)⟩

theorem effective_first_clause (A : Oracle)
    (hA : ∀ k, {a | columns A k a = true}.Infinite) :
    Reduces (join (G₀ A) (G₁ A)) (OracleJump.jump A) ∧
      ∀ k, ∃ C : Oracle, Reduces C (join (G₀ A) (columns A k)) ∧
        Reduces C (join (G₁ A) (columns A k)) ∧ ¬ Reduces C (columns A k) :=
  ⟨GuardedComputability.limits_recursive A,common_noncomputable_columns A hA⟩

end
end TuringRigidity.GuardedLimits

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedOutcomes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedOutcomes
open ArithmeticHierarchy
open Encodable EncodedForcing CodingForcing FiniteInjury GuardedStage
open UniformProgram IndexMatrix
noncomputable section

theorem candidate_decisive (A : Oracle) (t : ℕ) (p : Condition)
    (hc : Changes A t p) : StablePair.Decisive A t (candidate A t p) := by
  let p' := atLevel p t
  let q := condition (pairProcedure A (Nat.pair t (code p')))
  obtain ⟨_,hdis | ⟨ha,hn,hd | ⟨he,hrest⟩⟩⟩ :=
    (Classical.choose_spec (GuardedPair.pair_exists A)).2 t (code p')
  · exact Or.inl hdis
  · have haq : q.active = t := by
      change q.active = (condition (code p')).active at ha
      simpa only [condition_code,p',atLevel] using ha
    have heq : atLevel q t = q := by rw [← haq]; cases q; rfl
    change StablePair.Decisive A t (atLevel q t)
    rw [heq]
    exact hd
  · have heq : q = p' := by
      change q = condition (code p') at he
      simpa only [condition_code] using he
    change (atLevel q t).left ≠ p.left ∨ (atLevel q t).right ≠ p.right at hc
    rw [heq] at hc
    exact False.elim (hc.elim (fun h => h rfl) (fun h => h rfl))

theorem limits_extend_action {A : Oracle} {s t : ℕ}
    (ha : stageAction A s (construction A s) = some t) :
    CommonIdeal.Extends (GuardedLimits.G₀ A) (candidate A t (generic A (construction A s))).left ∧
    CommonIdeal.Extends (GuardedLimits.G₁ A) (candidate A t (generic A (construction A s))).right := by
  have hl : (candidate A t (generic A (construction A s))).left <+: (conditions A (s+1)).left := by
    change _ <+: (stageWord A s (construction A s)).left ++ [false]
    simp only [stageWord,ha]
    exact List.prefix_append _ _
  have hr : (candidate A t (generic A (construction A s))).right <+: (conditions A (s+1)).right := by
    change _ <+: (stageWord A s (construction A s)).right ++ [false]
    simp only [stageWord,ha]
    exact List.prefix_append _ _
  constructor
  · intro m hm
    exact ((limits_extend (word_growth A) (length_bound A) (s+1) m (hm.trans_le hl.length_le)).1).trans
      (getD_of_prefix hl hm)
  · intro m hm
    have hn : m < (conditions A (s+1)).left.length := by
      rw [(conditions A (s+1)).sameLength]
      exact hm.trans_le hr.length_le
    exact ((limits_extend (word_growth A) (length_bound A) (s+1) m hn).2).trans (getD_of_prefix hr hm)

theorem action_excludes_common {A Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    stageAction A s (construction A s) ≠ some t := by
  intro ha
  have hc := (scan_spec ha).2.2.2
  obtain ⟨h₀,h₁⟩ := limits_extend_action ha
  exact StablePair.decisive_excludes_common hbase h₀ h₁ he₀ he₁ (candidate_decisive A t _ hc)

theorem done_witness (A : Oracle) {s t : ℕ} (ht : t ∈ (construction A s).done) :
    ∃ u, u < s ∧ stageAction A u (construction A u) = some t := by
  induction s with
  | zero => simp [construction] at ht
  | succ s ih =>
    change t ∈ FiniteInjury.update (construction A s).done (stageAction A s (construction A s)) at ht
    cases ha : stageAction A s (construction A s) with
    | none =>
      obtain ⟨u,hu,he⟩ := ih (by simpa [ha,FiniteInjury.update] using ht)
      exact ⟨u,by omega,he⟩
    | some i =>
      simp only [ha,FiniteInjury.update,Finset.mem_insert,Finset.mem_filter] at ht
      rcases ht with rfl | ⟨ht,_⟩
      · exact ⟨s,by omega,ha⟩
      · obtain ⟨u,hu,he⟩ := ih ht
        exact ⟨u,by omega,he⟩

theorem common_not_done {A Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    t ∉ (construction A s).done := by
  intro ht
  obtain ⟨u,_,hu⟩ := done_witness A ht
  exact action_excludes_common hbase he₀ he₁ hu

theorem scan_hits {A : Oracle} {p : Condition} {d : Finset ℕ} {start n t : ℕ}
    (hlo : start ≤ t) (hhi : t < start+n) (hd : t ∉ d) (hc : Changes A t p) :
    ∃ i, i ≤ t ∧ scan A p d start n = some i := by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    by_cases h : start ∉ d ∧ Changes A start p
    · exact ⟨start,hlo,by simp only [scan,ite_eq_left h]⟩
    · have hne : start ≠ t := by rintro rfl; exact h ⟨hd,hc⟩
      obtain ⟨i,hi,he⟩ := ih (start := start+1) (by omega) (by omega)
      exact ⟨i,hi,by simpa only [scan,ite_eq_right h] using he⟩

theorem common_eventually_unchanged {A Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    ∃ S, ∀ s, S ≤ s → ¬ Changes A t (generic A (construction A s)) := by
  obtain ⟨S,hS⟩ := finite_injury (proposal A) (t+1)
  refine ⟨max S (t+1),fun s hs hc => ?_⟩
  obtain ⟨i,hi,he⟩ := scan_hits (start := 0) (n := s) (Nat.zero_le t)
    (by omega) (common_not_done (s := s) hbase he₀ he₁) hc
  apply hS s ((le_max_left _ _).trans hs) i (by omega)
  simpa only [action_eq,stageAction] using he

theorem nonchanging_outcome {A Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hchange : ¬ Changes A t (generic A (construction A s))) :
    let p := atLevel (generic A (construction A s)) t
    UniformAgreement.NoDisagreement A t p ∧ GuardedPair.NoBad A t p ∧
      ((¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) z)) ∨
        ∃ w, UniformSplit.PointCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) w) ∧
          CodingLocation (columns A) p (item w 2)) := by
  let p := atLevel (generic A (construction A s)) t
  let q := condition (pairProcedure A (Nat.pair t (code p)))
  have hwords : q.left = p.left ∧ q.right = p.right := by
    change ¬ (q.left ≠ p.left ∨ q.right ≠ p.right) at hchange
    exact ⟨Classical.not_not.mp (fun hn => hchange (Or.inl hn)),
      Classical.not_not.mp (fun hn => hchange (Or.inr hn))⟩
  have hq₀ : CommonIdeal.Extends (GuardedLimits.G₀ A) q.left := by
    rw [hwords.1]; exact (GuardedLimits.limits_extend_generic A s).1
  have hq₁ : CommonIdeal.Extends (GuardedLimits.G₁ A) q.right := by
    rw [hwords.2]; exact (GuardedLimits.limits_extend_generic A s).2
  obtain ⟨_,hd | ⟨ha,hn,hd | ⟨he,hbad,hout⟩⟩⟩ :=
    (Classical.choose_spec (GuardedPair.pair_exists A)).2 t (code p)
  · exact False.elim (StablePair.decisive_excludes_common hbase hq₀ hq₁ he₀ he₁ (Or.inl hd))
  · exact False.elim (StablePair.decisive_excludes_common hbase hq₀ hq₁ he₀ he₁ hd)
  · refine ⟨by simpa only [condition_code] using hn,hbad,?_⟩
    simpa only [GuardedPair.Outcome,condition_code] using hout

theorem common_eventually_outcome {A Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    ∃ S, ∀ s, S ≤ s →
      let p := atLevel (generic A (construction A s)) t
      UniformAgreement.NoDisagreement A t p ∧ GuardedPair.NoBad A t p ∧
        ((¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) z)) ∨
          ∃ w, UniformSplit.PointCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) w) ∧
            CodingLocation (columns A) p (item w 2)) := by
  obtain ⟨S,hS⟩ := common_eventually_unchanged hbase he₀ he₁
  exact ⟨S,fun s hs => nonchanging_outcome hbase he₀ he₁ (hS s hs)⟩

end
end TuringRigidity.GuardedOutcomes

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedExtraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedExtraction
open ArithmeticHierarchy
open Encodable CodingForcing EncodedForcing UniformProgram IndexMatrix FiniteInjury GuardedStage
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

theorem noBad_sound {A Y : Oracle} {t : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (hbad : GuardedPair.NoBad A t p) {m : ℕ}
    (hm : CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) p.left m) :
    CodingLocation (columns A) p m := by
  by_contra hnc
  obtain ⟨v,b,n,a,c,hpv,hpm,hmv,hac,ha,hc⟩ := hm
  have hrun (w : List Bool) (n : ℕ) :
      UniformRun.run A (machine (item t 0)) (machine (item t 1)) w n =
        CommonIdeal.run Y (meaning (machine (item t 1))) w n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  apply hbad
  refine ⟨encode [n,encode v,m,CommonIdeal.bit b,a,c],?_,?_⟩
  · have hbit : (CommonIdeal.bit b).bodd = b := by cases b <;> rfl
    have hh := And.intro hpv (And.intro hpm (And.intro hmv (And.intro hac
      (And.intro (hrun v n ▸ ha) (hrun (v.set m b) n ▸ hc)))))
    simpa [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      UniformPair.request,item,word,hbit,
      show left (code p) = p.left from congrArg Condition.left (condition_code p)] using hh
  · simpa [UniformPair.IsCoding,item,condition_code] using hnc

theorem common_recursive_locations {A Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hn : ¬ Reduces Z Y) :
    ∃ p : Condition, p.active = t ∧ ∃ C : Oracle, Reduces C Y ∧
      {m | C m = true}.Infinite ∧ ∀ m, C m = true → CodingLocation (columns A) p m := by
  obtain ⟨S,hS⟩ := GuardedOutcomes.common_eventually_outcome hbase he₀ he₁
  let p := atLevel (generic A (construction A S)) t
  have hbad : GuardedPair.NoBad A t p := (hS S le_rfl).2.1
  obtain ⟨E,hE,hEq⟩ := CodingSplitSearch.splittingLocations_enumerable Y (meaning (machine (item t 1))) p.left
  have hu : RecursiveInfiniteSubset.Unbounded E := by
    intro N
    let s := max (S+1) N
    let q := atLevel (generic A (construction A s)) t
    have hpq : p.left <+: q.left := by
      exact (GuardedLimits.generic_prefix_next A S).1.trans
        ((word_prefix (word_growth A) (le_max_left (S+1) N)).1.trans
          (open_extends A _ _).1)
    obtain ⟨_,_,hno | ⟨w,hw,hcoding⟩⟩ := hS s (by dsimp [s]; omega)
    · exact False.elim (hn (noSplit_reduces (p := q) (t := t) hbase
        (GuardedLimits.limits_extend_generic A s).1 he₀ hno))
    · have hN : N ≤ q.left.length := by
        exact (le_max_right (S+1) N).trans ((length_bound A s).trans (open_extends A _ _).1.length_le)
      obtain ⟨v,b,n,a,c,hqv,hqm,hmv,hac,ha,hc⟩ := point_splittingLocation hbase hw
      have hpoint : CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) p.left (item w 2) :=
        ⟨v,b,n,a,c,hpq.trans hqv,hpq.length_le.trans hqm,hmv,hac,ha,hc⟩
      obtain ⟨z,hz⟩ := (hEq (item w 2)).mp hpoint
      exact ⟨z,item w 2,hN.trans hqm,hz⟩
  obtain ⟨C,hCY,hCi,hC⟩ := RecursiveInfiniteSubset.infinite_recursive_subset Y E hu hE
  exact ⟨p,rfl,C,hCY,hCi,fun m hm => noBad_sound hbase hbad ((hEq m).mpr (hC m hm))⟩

theorem common_infinite_column {A Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hn : ¬ Reduces Z Y) :
    ∃ k, k < t ∧ ∃ C : Oracle, Reduces C Y ∧ {a | C a = true}.Infinite ∧
      ∀ a, C a = true → columns A k a = true := by
  obtain ⟨p,hp,C,hCY,hCi,hC⟩ := common_recursive_locations hbase he₀ he₁ hn
  simpa only [hp] using CodingExtraction.infinite_column hCY hCi hC

theorem common_lower_computes_column {A Y Z : Oracle}
    (hIntro : ∀ k C, (∀ a, C a = true → columns A k a = true) →
      {a | C a = true}.Infinite → Reduces (columns A k) C)
    (hY : Reduces Y A)
    (h₀ : Reduces Z (join Y (GuardedLimits.G₀ A)))
    (h₁ : Reduces Z (join Y (GuardedLimits.G₁ A)))
    (hn : ¬ Reduces Z Y) : ∃ k, Reduces (columns A k) Y := by
  obtain ⟨b,hb⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hY
  obtain ⟨e,he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h₀
  obtain ⟨f,hf⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h₁
  let t := encode [encode (represent b),encode (represent e),encode (represent f)]
  have hb' : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y := by
    simpa [t,item,machine,represent_correct] using hb
  have he' : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A))) (meaning (machine (item t 1))) = oracleFunction Z := by
    simpa [t,item,machine,represent_correct] using he
  have hf' : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A))) (meaning (machine (item t 2))) = oracleFunction Z := by
    simpa [t,item,machine,represent_correct] using hf
  obtain ⟨k,_,C,hCY,hCi,hC⟩ := common_infinite_column hb' he' hf' hn
  exact ⟨k,reduces_trans (hIntro k C hC hCi) hCY⟩

end
end TuringRigidity.GuardedExtraction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_GuardedCoding
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GuardedCoding
open EncodedForcing StageNormalization AntichainParameters

theorem effective_coding (A : Oracle) : ∃ G₀ G₁ : Oracle,
    Reduces (join G₀ G₁) (OracleJump.jump A) ∧
    (∀ k, ∃ C : Oracle, Reduces C (join G₀ (columns A k)) ∧
      Reduces C (join G₁ (columns A k)) ∧ ¬ Reduces C (columns A k)) ∧
    ∀ Y Z : Oracle, Reduces Y A → Reduces Z (join G₀ Y) →
      Reduces Z (join G₁ Y) → ¬ Reduces Z Y → ∃ k, Reduces (columns A k) Y := by
  let B := normalized A
  obtain ⟨hbound,hfirst⟩ := GuardedLimits.effective_first_clause B
    (fun k => (normalized_spec A k).2.1)
  refine ⟨GuardedLimits.G₀ B,GuardedLimits.G₁ B,
    reduces_trans hbound (OracleJump.jump_mono (normalized_reduces A)),?_,?_⟩
  · intro k
    obtain ⟨C,h₀,h₁,hn⟩ := hfirst k
    obtain ⟨hBA,hAB⟩ := (degree_eq_iff _ _).mp (normalized_spec A k).1
    exact ⟨C,reduces_trans h₀ (join_mono (reduces_refl _) hBA),
      reduces_trans h₁ (join_mono (reduces_refl _) hBA),fun h => hn (reduces_trans h hAB)⟩
  · intro Y Z hY h₀ h₁ hn
    obtain ⟨k,hk⟩ := GuardedExtraction.common_lower_computes_column
      (fun k => (normalized_spec A k).2.2)
      (reduces_trans hY (NormalizedRecovery.normalized_inverse A))
      (reduces_trans h₀ (AntichainCoding.swap_join_reduces _ _))
      (reduces_trans h₁ (AntichainCoding.swap_join_reduces _ _)) hn
    exact ⟨k,reduces_trans (((degree_eq_iff _ _).mp (normalized_spec A k).1).2) hk⟩

theorem effective_antichain_parameters (A : Oracle)
    (hAnti : ∀ i j, degree (columns A i) ≤ degree (columns A j) →
      degree (columns A i) = degree (columns A j)) :
    ∃ g₀ g₁ : Degree, g₀ ⊔ g₁ ≤ OracleJump.degreeJump (degree A) ∧
      ∀ x : Degree, CodedAntichain (degree A) g₀ g₁ x ↔ ∃ k, degree (columns A k) = x := by
  obtain ⟨G₀,G₁,hbound,hfirst,hsecond⟩ := effective_coding A
  have hm : ∀ k, NontrivialCommonLower (degree A) (degree G₀) (degree G₁) (degree (columns A k)) := by
    intro k
    obtain ⟨C,h₀,h₁,hn⟩ := hfirst k
    exact ⟨CodingExtraction.column_projection_reduces A k,degree C,h₀,h₁,hn⟩
  have hc : ∀ x, NontrivialCommonLower (degree A) (degree G₀) (degree G₁) x →
      ∃ k, degree (columns A k) ≤ x := by
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

end TuringRigidity.GuardedCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectiveFamilies
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveFamilies
open Encodable EncodedForcing UniformOracle SetCoding BoundedDecoding

theorem reindex_reduces (A : Oracle) {f : ℕ → ℕ} (hf : Primrec f) :
    Reduces (fun n => A (f n)) A := by
  apply RecursiveIn.iff_nat.mpr
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) := .oracle _ (Set.mem_singleton _)
  exact _root_.OAI.TuringRigidity.UniformOracle.total_comp hq (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hf)

theorem slice_reduces (A : Oracle) (i : ℕ) : Reduces (slice A i) A :=
  reindex_reduces A (Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (Primrec.const i) (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair))

theorem mix_reduces (A B : Oracle) : Reduces (mix A B) (join A B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let q := Primrec₂.natPair.comp f (Primrec.nat_div.comp r (Primrec.const 2))
  have hp := Primrec.cond (Primrec.nat_bodd.comp r)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) q) (Primrec.const 1))
    (Primrec.nat_mul.comp (Primrec.const 2) q)
  have hh := reindex_reduces (join A B) hp
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext m
  cases hb : (Nat.unpair m).2.bodd <;> simp [mix,join,columns,hb]
  congr 1
  omega

theorem tuples_reduces (G : Oracle) (n : ℕ) : Reduces (tuples G n) G := by
  induction n with
  | zero => exact RecursiveIn.iff_nat.mpr .zero
  | succ n ih =>
    exact reduces_trans (mix_reduces _ _) (join_reduces ih (slice_reduces G n))

theorem tuples_degree (G : Oracle) (n j : ℕ) :
    degree (columns (tuples G n) j) = (Finset.range n).sup (fun i => degree (columns G (Nat.pair i j))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tuples,mix_column]
    change degree (columns (tuples G n) j) ⊔ degree (columns (slice G n) j) = _
    rw [ih,slice_column,Finset.range_add_one,Finset.sup_insert]
    exact sup_comm _ _

theorem antichainCode_below {F H : Oracle} (hF : Reduces F H)
    (hAnti : ∀ i j, degree (columns F i) ≤ degree (columns F j) →
      degree (columns F i) = degree (columns F j)) :
    ∃ p : AntichainCode, AntichainBelow p (degree (OracleJump.jump H)) ∧
      ∀ x, p.Holds x ↔ ∃ k, degree (columns F k) = x := by
  obtain ⟨g₀,g₁,hg,hcode⟩ := GuardedCoding.effective_antichain_parameters F hAnti
  have hj : OracleJump.degreeJump (degree F) ≤ degree (OracleJump.jump H) := OracleJump.jump_mono hF
  have hb : degree F ≤ degree (OracleJump.jump H) :=
    (show degree F ≤ degree H from hF).trans (OracleJump.degree_le_jump _)
  exact ⟨⟨degree F,g₀,g₁⟩,⟨hb,(le_sup_left.trans hg).trans hj,
    (le_sup_right.trans hg).trans hj⟩,hcode⟩

end TuringRigidity.EffectiveFamilies

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectiveRelations
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectiveRelations
open EncodedForcing EffectiveFamilies CohenColumns EffectiveCohen SetCoding RelationCoding BoundedDecoding

private theorem data_below {A B : Oracle} (hA : Reduces A B) (i j : ℕ) :
    degree (columns A (Nat.pair i j)) ≤ degree B :=
  reduces_trans (CodingExtraction.column_projection_reduces A _) hA

theorem coordinate_code {A B G : Oracle} (hA : Reduces A B) (hg : OneGeneric B G) (i : ℕ) :
    ∃ p : SetCode, p.bound = degree B ∧ SetBelow p (degree (OracleJump.jump (join B G))) ∧
      ∀ x c, p.Graph x c ↔ ∃ j, degree (columns A (Nat.pair i j)) = x ∧
        degree (columns G (Nat.pair i j)) = c := by
  have htag (x y : Degree) (hx : x ≤ degree B) (hy : y ≤ degree B) (j k : ℕ) :
      x ⊔ degree (columns G (Nat.pair i j)) ≤ y ⊔ degree (columns G (Nat.pair i k)) ↔
        x ≤ y ∧ j = k := by
    simpa using independence hg x y hx hy (Nat.pair i j) {Nat.pair i k}
  have hanti : ∀ j k, degree (columns (slice G i) j) ≤ degree (columns (slice G i) k) →
      degree (columns (slice G i) j) = degree (columns (slice G i) k) := by
    intro j k hjk
    have he := (htag ⊥ ⊥ bot_le bot_le j k).mp (by simpa using hjk)
    rw [he.2]
  have had : ∀ j k, degree (columns (mix (slice A i) (slice G i)) j) ≤
      degree (columns (mix (slice A i) (slice G i)) k) →
      degree (columns (mix (slice A i) (slice G i)) j) = degree (columns (mix (slice A i) (slice G i)) k) := by
    intro j k hjk
    have he := (htag _ _ (data_below hA i j) (data_below hA i k) j k).mp (by
      simp only [mix_column,slice_column] at hjk
      exact hjk)
    rw [he.2]
  have htagBound : Reduces (slice G i) (join B G) :=
    reduces_trans (slice_reduces G i) (reduces_join_right B G)
  have hdecBound : Reduces (mix (slice A i) (slice G i)) (join B G) :=
    reduces_trans (mix_reduces _ _) (join_reduces
      (reduces_trans (slice_reduces A i) (reduces_trans hA (reduces_join_left B G))) htagBound)
  obtain ⟨pc,hpcBound,hpc⟩ := antichainCode_below htagBound hanti
  obtain ⟨pa,hpaBound,hpa⟩ := antichainCode_below hdecBound had
  refine ⟨⟨degree B,pc,pa⟩,rfl,?_,fun x c => ?_⟩
  · exact ⟨(le_sup_left : degree B ≤ degree B ⊔ degree G).trans (OracleJump.degree_le_jump _),hpcBound,hpaBound⟩
  · change (x ≤ degree B ∧ pc.Holds c ∧ pa.Holds (x ⊔ c)) ↔ _
    rw [hpc,hpa]
    simp only [slice_column,mix_column]
    constructor
    · rintro ⟨hx,⟨j,rfl⟩,⟨k,hk⟩⟩
      have hl := (htag _ x (data_below hA i k) hx k j).mp hk.le
      have hr := (htag x _ hx (data_below hA i k) j k).mp hk.ge
      have he := hl.2
      subst k
      exact ⟨j,le_antisymm hl.1 hr.1,rfl⟩
    · rintro ⟨j,rfl,rfl⟩
      exact ⟨data_below hA i j,⟨j,rfl⟩,⟨j,rfl⟩⟩

private theorem fin_sup (n : ℕ) (f : ℕ → Degree) :
    Finset.univ.sup (fun i : Fin n => f i.val) = (Finset.range n).sup f := by
  classical
  have he : (Finset.univ : Finset (Fin n)).image Fin.val = Finset.range n := by
    ext m
    simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_range]
    exact ⟨fun ⟨a,ha⟩ => ha ▸ a.isLt,fun hm => ⟨⟨m,hm⟩,rfl⟩⟩
  simpa only [Finset.sup_image,Function.comp_def] using congrArg (fun F : Finset ℕ => F.sup f) he

theorem tag_below_tuple {B G : Oracle} (hg : OneGeneric B G) {n i j k : ℕ}
    (h : degree (columns G (Nat.pair i j)) ≤ degree (columns (tuples G n) k)) : j = k := by
  classical
  let F := (Finset.range n).image (fun l => Nat.pair l k)
  have hh : degree (columns G (Nat.pair i j)) ≤ F.sup (fun l => degree (columns G l)) := by
    simpa only [tuples_degree,F,Finset.sup_image,Function.comp_def] using h
  have hm := (independence hg ⊥ ⊥ bot_le bot_le (Nat.pair i j) F).mp (by simpa using hh)
  obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hm.2
  simpa only [Nat.unpair_pair] using (congrArg (fun m => (Nat.unpair m).2) hl).symm

theorem tuples_antichain {B G : Oracle} (hg : OneGeneric B G) (n : ℕ) :
    ∀ j k, degree (columns (tuples G n) j) ≤ degree (columns (tuples G n) k) →
      degree (columns (tuples G n) j) = degree (columns (tuples G n) k) := by
  intro j k hjk
  cases n with
  | zero => rfl
  | succ n =>
    have htag : degree (columns G (Nat.pair 0 j)) ≤ degree (columns (tuples G (n+1)) j) := by
      rw [tuples_degree]
      exact Finset.le_sup (f := fun i => degree (columns G (Nat.pair i j))) (by simp)
    have he := tag_below_tuple hg (htag.trans hjk)
    rw [he]

theorem relation_code {A B G : Oracle} (hA : Reduces A B) (hg : OneGeneric B G) (n : ℕ) :
    ∃ p : RelationCode n, RelationBelow p (degree (OracleJump.jump (join B G))) ∧
      ∀ v, p.Holds v ↔ ∃ j, ∀ i : Fin n, degree (columns A (Nat.pair i.val j)) = v i := by
  classical
  choose pc hbound hpBound hp using fun i : Fin n => coordinate_code hA hg i.val
  obtain ⟨pt,htBound,ht⟩ := antichainCode_below
    (reduces_trans (tuples_reduces G n) (reduces_join_right B G)) (tuples_antichain hg n)
  refine ⟨⟨pc,pt⟩,⟨hpBound,htBound⟩,fun v => ?_⟩
  constructor
  · rintro ⟨c,hc,hT⟩
    obtain ⟨j,hj⟩ := (ht _).mp hT
    refine ⟨j,fun i => ?_⟩
    obtain ⟨k,hkv,hkc⟩ := (hp i _ _).mp (hc i)
    have hle : degree (columns G (Nat.pair i.val k)) ≤ degree (columns (tuples G n) j) := by
      rw [hkc,hj]
      exact Finset.le_sup (f := c) (Finset.mem_univ i)
    have he := tag_below_tuple hg hle
    simpa only [he] using hkv
  · rintro ⟨j,hj⟩
    let c := fun i : Fin n => degree (columns G (Nat.pair i.val j))
    refine ⟨c,fun i => (hp i _ _).mpr ⟨j,hj i,rfl⟩,(ht _).mpr ⟨j,?_⟩⟩
    rw [tuples_degree]
    exact (fin_sup n (fun i => degree (columns G (Nat.pair i j)))).symm

theorem effective_relation_sequence (A : Oracle) (n : ℕ) :
    ∃ p : RelationCode n, RelationBelow p (degree (OracleJump.jump A)) ∧
      ∀ v, p.Holds v ↔ ∃ j, ∀ i : Fin n, degree (columns A (Nat.pair i.val j)) = v i := by
  obtain ⟨G,hG,hgen,hlow⟩ := CohenLowness.relative_low_generic A
  obtain ⟨p,hp,hcode⟩ := relation_code (reduces_refl A) hgen n
  exact ⟨p,hlow ▸ hp,hcode⟩

end TuringRigidity.EffectiveRelations

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_EffectivePresentation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EffectivePresentation
open EncodedForcing UniformOracle ArithmeticHierarchy EffectiveFamilies EffectiveRelations
open SetCoding RelationCoding BoundedDecoding AntichainParameters
noncomputable section
attribute [local instance] Classical.propDecidable

theorem pick_recursive {A : Oracle} {P : ℕ → Prop} (hP : RecursivePred A P) (j₀ : ℕ) :
    Nat.RecursiveIn {oracleFunction A} (fun j => Part.some (pick P j₀ j)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := Primrec.ite (Primrec.eq.comp r (Primrec.const 1)) f (Primrec.const j₀)
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hp) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id) hP)).of_eq
    (fun j => by by_cases h : P j <;> simp [pick,h])

theorem selected_reduces {A : Oracle} {P : ℕ → Prop} (hP : RecursivePred A P) (j₀ : ℕ) :
    Reduces (selected A P j₀) A := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := _root_.OAI.TuringRigidity.UniformOracle.total_comp (pick_recursive hP j₀) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (r.comp f))
  have hidx := _root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (f.comp f)) hp) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec r)
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) := .oracle _ (Set.mem_singleton _)
  exact RecursiveIn.iff_nat.mpr (_root_.OAI.TuringRigidity.UniformOracle.total_comp hq hidx)

theorem emptyAntichain_holds (x : Degree) : ¬ emptyAntichain.Holds x := by
  simp [emptyAntichain,AntichainCode.Holds,CodedAntichain,NontrivialCommonLower]

theorem emptyRelation_below (n : ℕ) (y : Degree) : RelationBelow (emptyRelation n) y := by
  exact ⟨fun _ => ⟨bot_le,⟨bot_le,bot_le,bot_le⟩,⟨bot_le,bot_le,bot_le⟩⟩,⟨bot_le,bot_le,bot_le⟩⟩

theorem emptyRelation_holds (n : ℕ) (v : Fin n → Degree) : ¬ (emptyRelation n).Holds v := by
  rintro ⟨c,_,hc⟩
  exact emptyAntichain_holds _ hc

theorem effective_coding (A : Oracle) (P : ℕ → Prop) (hP : RecursivePred A P) (n : ℕ) :
    ∃ p : RelationCode n, RelationBelow p (degree (OracleJump.jump A)) ∧
      ∀ v, p.Holds v ↔ ∃ j, P j ∧ ∀ i : Fin n, degree (columns A (Nat.pair i.val j)) = v i := by
  by_cases hne : ∃ j, P j
  · obtain ⟨j₀,hj₀⟩ := hne
    let F := selected A P j₀
    obtain ⟨p,hp,hcode⟩ := effective_relation_sequence F n
    have hbound := OracleJump.jump_mono (selected_reduces hP j₀)
    have hp' : RelationBelow p (degree (OracleJump.jump A)) := by
      refine ⟨fun i => ?_,?_⟩
      · exact ⟨(hp.1 i).1.trans hbound,
          ⟨(hp.1 i).2.1.1.trans hbound,(hp.1 i).2.1.2.1.trans hbound,(hp.1 i).2.1.2.2.trans hbound⟩,
          ⟨(hp.1 i).2.2.1.trans hbound,(hp.1 i).2.2.2.1.trans hbound,(hp.1 i).2.2.2.2.trans hbound⟩⟩
      · exact ⟨hp.2.1.trans hbound,hp.2.2.1.trans hbound,hp.2.2.2.trans hbound⟩
    refine ⟨p,hp',fun v => ?_⟩
    rw [hcode]
    constructor
    · rintro ⟨j,hj⟩
      have hvalid : P (pick P j₀ j) := by by_cases h : P j <;> simp [pick,h,hj₀]
      exact ⟨pick P j₀ j,hvalid,fun i => by simpa only [F,selected_column] using hj i⟩
    · rintro ⟨j,hj,hv⟩
      exact ⟨j,fun i => by simpa only [F,selected_column,pick,ite_eq_left hj] using hv i⟩
  · refine ⟨emptyRelation n,emptyRelation_below _ _,fun v => ?_⟩
    constructor
    · intro h
      exact False.elim (emptyRelation_holds n v h)
    · rintro ⟨j,hj,_⟩
      exact False.elim (hne ⟨j,hj⟩)

end
end TuringRigidity.EffectivePresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_EnumerationConstruction
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EnumerationConstruction
open Encodable EncodedForcing ArithmeticHierarchy UniformOracle OracleJump
open ArithmeticModelDecoding SetCoding RelationCoding BoundedDecoding EnumerationDecoding

theorem rows_reduces (C H : Oracle) : Reduces (rows C H) (join C H) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let p := Primrec₂.natPair.comp (r.comp f) r
  let even := Primrec.nat_mul.comp (Primrec.const 2) p
  have hi := Primrec.ite (Primrec.eq.comp (f.comp f) (Primrec.const 0)) even (Primrec.succ.comp even)
  have hh := EffectiveFamilies.reindex_reduces (join C H) hi
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext v
  by_cases h : (Nat.unpair (Nat.unpair v).1).1 = 0
  · simp only [rows,ite_eq_left h,join_even]
  · simp only [rows,ite_eq_right h,join_odd]

theorem payload_code {C H : Oracle} (hC : Reduces C H) : ∃ p : RelationCode 2,
    RelationBelow p (degree (jump H)) ∧ ∀ a b,
      p.Holds (two a b) ↔ ∃ k, a = degree (columns C k) ∧ b = degree (columns H k) := by
  have hP : RecursivePred (rows C H) (fun _ => True) := by
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.const 1)).of_eq (fun n => by simp)
  obtain ⟨p,hp,hcode⟩ := EffectivePresentation.effective_coding (rows C H) (fun _ => True) hP 2
  have hb := reduces_trans (rows_reduces C H) (join_reduces hC (reduces_refl H))
  refine ⟨p,hp.mono (jump_mono hb),fun a b => ?_⟩
  rw [hcode]
  constructor
  · rintro ⟨k,_,hk⟩
    exact ⟨k,by simpa [two] using (hk 0).symm,by simpa [two] using (hk 1).symm⟩
  · rintro ⟨k,rfl,rfl⟩
    refine ⟨k,trivial,fun i => ?_⟩
    fin_cases i <;> simp [two]

theorem enumeration_exists_oai (H : Oracle) (hz : Reduces (jump FixedArithmetic.zero) H) :
    ∃ c : Enumeration, c.output = (fun k => degree (columns H k)) ∧
      RelationBelow c.successor (degree (jump H)) ∧ RelationBelow c.payload (degree (jump H)) := by
  obtain ⟨K⟩ := FixedArithmetic.frame_exists
  have hC : Reduces K.C H := reduces_trans (reduces_jump K.C) (reduces_trans K.low hz)
  obtain ⟨P,hP,hspec⟩ := payload_code hC
  let c : Enumeration := ⟨fun k => degree (columns K.C k),K.injective,
    fun k => degree (columns H k),K.successor,P,K.spec,hspec⟩
  exact ⟨c,rfl,K.below.mono (reduces_trans hz (reduces_jump H)),hP⟩

end TuringRigidity.EnumerationConstruction

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.EnumerationConstruction.enumeration_exists_oai := @OAI.TuringRigidity.EnumerationConstruction.enumeration_exists_oai
