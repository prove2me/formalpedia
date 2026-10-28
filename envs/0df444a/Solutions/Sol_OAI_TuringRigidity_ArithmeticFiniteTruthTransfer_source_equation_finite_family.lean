-- Prove2me | solution 1 for OAI.TuringRigidity.ArithmeticFiniteTruthTransfer.source_equation_finite_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:53:26.454084+00:00
-- url     : https://prove2.me/submissions/3bc70343-1de8-45a8-b3b6-ce2b315f7c51

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A006

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_ProgramTopology
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace TuringRigidity

namespace OracleCode

theorem eval_eq_oracle_iff (c : OracleCode) (A B : Oracle) :
    eval (oracleFunction A) c = oracleFunction B ↔
      ∀ n, (if B n then 1 else 0) ∈ eval (oracleFunction A) c n := by
  constructor
  · intro h n
    rw [h]
    exact Part.mem_some _
  · intro h
    funext n
    exact Part.eq_some_iff.mpr (h n)

end OracleCode

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_TableIndices
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_UniformArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformArithmetic
open Encodable

theorem Arith.iff {P Q} (hP : Arith P) (hQ : Arith Q) :
    Arith (fun O v => P O v ↔ Q O v) :=
  ((hP.imp hQ).and (hQ.imp hP)).congr (fun _ _ => iff_def.symm)

end TuringRigidity.UniformArithmetic

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

end TuringRigidity.ArithmeticCommonRequirement

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericCoding
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericCoding
open UniformOracle BinarySeries Encodable

theorem count_le (G : Oracle) (n : ℕ) : count G n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change count G n + bit G (2*n+1) ≤ n+1
    unfold bit
    split <;> omega

end TuringRigidity.GenericCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffle
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteShuffle
open GenericCoding UniformOracle BinarySeries

theorem count_agree {n : ℕ} {G H : Oracle} (h : ∀ i, i < n → G (2*i+1) = H (2*i+1)) :
    count G n = count H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change count G n + bit G (2*n+1) = count H n + bit H (2*n+1)
    rw [ih (fun i hi => h i (by omega))]
    simp [bit,h n (by omega)]

theorem code_agree {n : ℕ} {A B G H : Oracle} (ha : Agree n A B) (hg : Agree (2*n) G H) :
    Agree n (code A G) (code B H) := by
  intro i hi
  have hc : count G i = count H i := count_agree (fun j hj => hg (2*j+1) (by omega))
  have ho := hg (2*i+1) (by omega)
  have hl := count_le G i
  simp only [code,←hc,←ho]
  split
  · exact ha _ (by omega)
  · exact hg _ (by omega)

end TuringRigidity.FiniteShuffle

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticPrefixForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticPrefixForcing
open Encodable UniformArithmetic FiniteShuffle ShuffleRequirements
open EncodedForcing (word word_primrec)

theorem avoids_upward (Q : List Bool → Prop) : Upward (Avoid Q) :=
  fun _ _ h hs u hu => hs u (h.trans hu)

theorem decides_dense (Q : List Bool → Prop) (hQ : Upward Q) :
    DenseOpen (Decides Q) := by
  classical
  constructor
  · intro s
    by_cases h : ∃ t, s <+: t ∧ Q t
    · obtain ⟨t,ht,hq⟩ := h
      exact ⟨t,ht,Or.inl hq⟩
    · exact ⟨s,List.prefix_rfl,Or.inr (fun t ht hq => h ⟨t,ht,hq⟩)⟩
  · intro s t h
    exact Or.imp (hQ s t h) (avoids_upward Q s t h)

theorem avoids_arith {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q) :
    ArithmeticPrefix (fun O v => Avoid (Q O v)) := by
  have hp := ArithmeticCommonRequirement.prefix_arith
    (right_primrec.comp left_primrec) right_primrec
  have h := hQ.comp _ (Primrec₂.natPair.comp (left_primrec.comp left_primrec) right_primrec)
  apply (hp.imp h.neg).all.congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  constructor
  · intro h t ht
    have hh := h (encode t)
    simpa only [word,Encodable.encodek,Option.getD_some] using hh (by
      simpa only [word,Encodable.encodek,Option.getD_some] using ht)
  · intro h t ht
    exact h (word t) ht

theorem decides_arith {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q) :
    ArithmeticPrefix (fun O v => Decides (Q O v)) := hQ.or (avoids_arith hQ)

theorem realizes_common {s t : List Bool} {G : Oracle}
    (hs : Realizes s G) (ht : Realizes t G) :
    ∃ u, s <+: u ∧ t <+: u ∧ Realizes u G := by
  refine ⟨initial G (max s.length t.length), ?_, ?_,
    (realizes_initial _ _ _).mpr (fun _ _ => rfl)⟩
  · rw [←prefix_default s]
    exact initial_prefix (by simp) hs
  · rw [←prefix_default t]
    exact initial_prefix (by simp) ht

theorem open_and (Q R : List Bool → Prop) (hQ : Upward Q) (hR : Upward R) (G : Oracle) :
    G ∈ OpenSet (fun s => Q s ∧ R s) ↔ G ∈ OpenSet Q ∧ G ∈ OpenSet R := by
  constructor
  · rintro ⟨s,⟨hq,hr⟩,hs⟩
    exact ⟨⟨s,hq,hs⟩,⟨s,hr,hs⟩⟩
  · rintro ⟨⟨s,hq,hs⟩,⟨t,hr,ht⟩⟩
    obtain ⟨u,hsu,htu,hu⟩ := realizes_common hs ht
    exact ⟨u,⟨hQ s u hsu hq,hR t u htu hr⟩,hu⟩

end TuringRigidity.ArithmeticPrefixForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticGenericTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticGenericTruth
open Encodable UniformArithmetic ArithmeticPrefixForcing FiniteShuffle ShuffleRequirements
open EncodedForcing (word word_primrec)

theorem open_constant (p : Prop) (G : Oracle) : G ∈ OpenSet (fun _ => p) ↔ p := by
  constructor
  · rintro ⟨_,hp,_⟩; exact hp
  · intro hp
    exact ⟨[],hp,fun i hi => by simp at hi⟩

end TuringRigidity.ArithmeticGenericTruth

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

theorem valid_tableOracle (B : Oracle) (e : ℕ) :
    Valid B (machine e) ↔ Represents B (machine e) (tableOracle B e) := by
  constructor
  · intro hv
    obtain ⟨A,hA⟩ := (valid_iff_represents B (machine e)).mp hv
    rw [tableOracle_eq hA]
    exact hA
  · intro h
    exact (valid_iff_represents B (machine e)).mpr ⟨_,h⟩

theorem valid_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {e : ℕ → ℕ} (he : Primrec e) :
    Arith (fun O v => IndexPresentation.Dom (B O v) (e v)) :=
  (represents_arith (tableOracle_arith hB he) hB he).congr
    (fun O v => (valid_tableOracle (B O v) (e v)).symm)

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

end
end TuringRigidity.UniformArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealSelection
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set
namespace TuringRigidity

theorem programOutput_eq (c : OracleCode) (A B : Oracle)
    (h : OracleCode.eval (oracleFunction A) c = oracleFunction B) :
    programOutput c A = B := by
  funext n
  simp only [programOutput, h, oracleFunction, Part.mem_some_iff]
  cases B n <;> simp

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericIdentity
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericIdentity
open Set

theorem total_iff (p : OracleCode) (P A : Oracle) :
    Total p P A ↔ OracleCode.eval (oracleFunction (join A P)) p = oracleFunction (value p P A) := by
  constructor
  · rintro ⟨B,hB⟩
    rw [show value p P A = B from programOutput_eq p _ B hB]
    exact hB
  · intro h; exact ⟨_,h⟩

end TuringRigidity.GenericIdentity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticPrincipalIntersection
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticPrincipalIntersection
open Encodable UniformArithmetic TableIndices IndexMatrix

theorem principal_iff_tables (U L R : Oracle) :
    GenericIdentity.PrincipalIntersection U L R ↔
      Reduces U L ∧ Reduces U R ∧ ∀ e : ℕ, IndexPresentation.Dom L e →
        Reduces (tableOracle L e) R → Reduces (tableOracle L e) U := by
  constructor
  · intro h
    have hU := (h (degree U)).mp le_rfl
    refine ⟨hU.1,hU.2,fun e he hR => ?_⟩
    exact (h (degree (tableOracle L e))).mpr
      ⟨represents_reduces ((valid_tableOracle L e).mp he),hR⟩
  · rintro ⟨hL,hR,h⟩ b
    obtain ⟨A,rfl⟩ := degree_surjective b
    constructor
    · intro hA
      exact ⟨reduces_trans hA hL,reduces_trans hA hR⟩
    · rintro ⟨haL,haR⟩
      change Reduces A R at haR
      change Reduces A U
      obtain ⟨d,hd⟩ := (reduces_iff_represents A L).mp haL
      have he : Represents L (machine (encode d)) A := by simpa using hd
      have hvalid : IndexPresentation.Dom L (encode d) :=
        (valid_iff_represents L _).mpr ⟨A,he⟩
      have ht := tableOracle_eq he
      have hh := h (encode d) hvalid (by simpa only [ht] using haR)
      simpa only [ht] using hh

theorem principal_arith {U L R : OracleFamily}
    (hU : ArithmeticOracle U) (hL : ArithmeticOracle L) (hR : ArithmeticOracle R) :
    Arith (fun O v => GenericIdentity.PrincipalIntersection (U O v) (L O v) (R O v)) := by
  have hleft := reduces_arith hU hL
  have hright := reduces_arith hU hR
  have hd := valid_arith (hL.comp left_primrec) right_primrec
  have hout := tableOracle_arith (hL.comp left_primrec) right_primrec
  have hr := reduces_arith hout (hR.comp left_primrec)
  have hu := reduces_arith hout (hU.comp left_primrec)
  apply (hleft.and (hright.and (hd.imp (hr.imp hu)).all)).congr
  intro O v
  simp only [left,right,Nat.unpair_pair]
  exact (principal_iff_tables (U O v) (L O v) (R O v)).symm

end TuringRigidity.ArithmeticPrincipalIntersection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_UniformPartialGraph
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.UniformPartialGraph
open Encodable UniformOracle CommonIdeal

theorem eval_iff_table (p : OracleCode) :
    ∃ d : Nat.Partrec.Code, ∀ Y : Oracle, ∀ n a : ℕ,
      a ∈ OracleCode.eval (oracleFunction Y) p n ↔
        ∃ z, a ∈ TableIndices.run Y d n z := by
  have hf : Partrec₂ (fun L : List ℕ => fun n =>
      OracleCode.eval (BranchMachine.lookup L) p n) :=
    OracleCode.eval_partrec BranchMachine.lookup_partrec p
  obtain ⟨d, hd⟩ := partrec_code hf
  have hd' (L : List ℕ) (n : ℕ) :
      d.eval (Nat.pair (encode L) n) = OracleCode.eval (BranchMachine.lookup L) p n :=
    hd (L, n)
  refine ⟨d, fun Y n a => ?_⟩
  have ha : Approximates (OracleCode.eval (oracleFunction Y) p n)
      (fun m => d.eval (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n)) := by
    simp only [hd']
    exact OracleCode.eval_approximates (prefix_approximates (fun k => bit (Y k))) p n
  constructor
  · intro h
    obtain ⟨m, hm⟩ := ha.2 a h
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp (hm m le_rfl)
    exact ⟨Nat.pair m t, by simpa [TableIndices.run, trial] using ht⟩
  · rintro ⟨z, hz⟩
    exact ha.1 (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound hz)

end TuringRigidity.UniformPartialGraph

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericTotality
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericIdentity
open Set FiniteShuffle ShuffleRequirements GenericTruth

theorem total_iff_binaryHalts (p : OracleCode) (P A : Oracle) :
    Total p P A ↔ ∀ n, BinaryHalts p P A n := by
  constructor
  · rintro ⟨B,hB⟩ n
    unfold BinaryHalts
    rw [hB]
    cases B n <;> simp [oracleFunction]
  · intro h
    apply (total_iff p P A).mpr
    apply (OracleCode.eval_eq_oracle_iff p _ _).mpr
    intro n
    rcases h n with h0 | h1
    · have hv : value p P A n = false := by
        have hn : ¬ 1 ∈ OracleCode.eval (oracleFunction (join A P)) p n := by
          intro h1
          have he := Part.mem_unique h0 h1
          omega
        simp [value,programOutput,hn]
      simpa [hv] using h0
    · have hv : value p P A n = true := by
        simp [value,programOutput,h1]
      simpa [hv] using h1

end TuringRigidity.GenericIdentity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticProgramGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticProgramGraph
open Encodable UniformArithmetic IndexMatrix GenericIdentity

theorem eval_arith (p : OracleCode) {B : OracleFamily} (hB : ArithmeticOracle B)
    {c n a : ℕ → ℕ} (hc : Primrec c) (hn : Primrec n) (ha : Primrec a) :
    Arith (fun O v => a v ∈ OracleCode.eval (oracleFunction (B O (c v))) p (n v)) := by
  obtain ⟨d, hd⟩ := UniformPartialGraph.eval_iff_table p
  have h := (run_arith hB (hc.comp left_primrec) (Primrec.const (encode d))
    (hn.comp left_primrec) right_primrec (ha.comp left_primrec)).ex
  exact h.congr (fun O v => by
    simpa only [left, right, Nat.unpair_pair, machine_encode, Option.mem_def] using
      (hd (B O (c v)) (n v) (a v)).symm)

theorem output_arith (p : OracleCode) {B : OracleFamily} (hB : ArithmeticOracle B) :
    ArithmeticOracle (fun O v => programOutput p (B O v)) :=
  (eval_arith p hB left_primrec right_primrec (Primrec.const 1)).congr
    (fun _ _ => by simp [programOutput])

theorem value_arith (p : OracleCode) {P A : OracleFamily}
    (hP : ArithmeticOracle P) (hA : ArithmeticOracle A) :
    ArithmeticOracle (fun O v => value p (P O v) (A O v)) :=
  output_arith p (join_arith hA hP)

theorem total_arith (p : OracleCode) {P A : OracleFamily}
    (hP : ArithmeticOracle P) (hA : ArithmeticOracle A) :
    Arith (fun O v => Total p (P O v) (A O v)) := by
  have hB := join_arith hA hP
  have h0 := eval_arith p hB left_primrec right_primrec (Primrec.const 0)
  have h1 := eval_arith p hB left_primrec right_primrec (Primrec.const 1)
  exact (h0.or h1).all.congr (fun O v => by
    simpa only [left, right, Nat.unpair_pair, BinaryHalts] using
      (total_iff_binaryHalts p (P O v) (A O v)).symm)

end TuringRigidity.ArithmeticProgramGraph

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffleComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteShuffleComputation
open Encodable EncodedForcing GenericCoding FiniteShuffle UniformOracle BinarySeries

theorem wordCount_primrec :
    Primrec₂ (fun (p : List Bool) n => count (fun i => p.getD i false) n) := by
  have hs : Primrec (fun z : List Bool × ℕ × ℕ =>
      z.2.2 + if z.1.getD (2*z.2.1+1) false then 1 else 0) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp ((Primrec.list_getD false).comp Primrec.fst
        (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
          (Primrec.fst.comp Primrec.snd)))) (Primrec.const true))
        (Primrec.const 1) (Primrec.const 0))
  exact (Primrec.nat_rec (Primrec.const 0) hs.to₂).of_eq (fun p n => by
    induction n with
    | zero => rfl
    | succ n ih =>
      change _ + _ = count (fun i => p.getD i false) n + bit (fun i => p.getD i false) (2*n+1)
      rw [ih]
      rfl)

theorem wordShuffleBit_primrec :
    Primrec (fun z : List Bool × List Bool × ℕ =>
      code (fun i => z.1.getD i false) (fun i => z.2.1.getD i false) z.2.2) := by
  let hp : Primrec (fun z : List Bool × List Bool × ℕ => z.2.1) :=
    Primrec.fst.comp Primrec.snd
  let hn : Primrec (fun z : List Bool × List Bool × ℕ => z.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hc := wordCount_primrec.comp hp hn
  exact Primrec.ite (Primrec.eq.comp ((Primrec.list_getD false).comp hp
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hn))) (Primrec.const true))
    ((Primrec.list_getD false).comp Primrec.fst hc)
    ((Primrec.list_getD false).comp hp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp hn hc)))

end TuringRigidity.FiniteShuffleComputation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticShuffleGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticShuffleGraph
open Encodable UniformArithmetic FiniteShuffle ShuffleRequirements GenericCoding
open EncodedForcing (word word_primrec)

theorem realizes_arith {B : OracleFamily} (hB : ArithmeticOracle B)
    {c s : ℕ → ℕ} (hc : Primrec c) (hs : Primrec s) :
    Arith (fun O v => Realizes (word (s v)) (B O (c v))) := by
  have hb := Arith.pure (fun v => (word (s (left v))).getD (right v) false = true)
    (Primrec.eq.comp ((Primrec.list_getD false).comp
      (word_primrec.comp (hs.comp left_primrec)) right_primrec) (Primrec.const true))
  have hq := query_at hB (hc.comp left_primrec) right_primrec
  have hl := less right_primrec
    (Primrec.list_length.comp (word_primrec.comp (hs.comp left_primrec)))
  apply (hl.imp (hb.iff hq)).all.congr
  intro O v
  simp only [left, right, Nat.unpair_pair]
  constructor
  · intro h i hi
    have hh := h i hi
    cases hb : (word (s v)).getD i false <;> cases ho : B O (c v) i <;> simp_all
  · intro h i hi
    rw [show (word (s v)).getD i false = B O (c v) i from h i hi]

theorem code_bit_iff (Y L : Oracle) (n : ℕ) :
    code Y L n = true ↔ ∃ s t : ℕ,
      (word s).length = n + 1 ∧ (word t).length = 2 * (n + 1) ∧
      Realizes (word s) Y ∧ Realizes (word t) L ∧
      code (fun i => (word s).getD i false) (fun i => (word t).getD i false) n = true := by
  constructor
  · intro h
    refine ⟨encode (initial Y (n + 1)), encode (initial L (2 * (n + 1))), ?_⟩
    simp only [word, Encodable.encodek, Option.getD_some, prefix_length]
    have hy : Realizes (initial Y (n + 1)) Y :=
      (realizes_initial _ _ _).mpr (fun _ _ => rfl)
    have hl : Realizes (initial L (2 * (n + 1))) L :=
      (realizes_initial _ _ _).mpr (fun _ _ => rfl)
    have he := code_agree (n := n + 1)
      (show Agree (n + 1) (fun i => (initial Y (n+1)).getD i false) Y from
        fun i hi => prefix_getD Y _ i hi)
      (show Agree (2 * (n + 1)) (fun i => (initial L (2*(n+1))).getD i false) L from
        fun i hi => prefix_getD L _ i hi)
    exact ⟨True.intro, True.intro, hy, hl, (he n (by omega)).trans h⟩
  · rintro ⟨s,t,hs,ht,hy,hl,h⟩
    have hy' : Agree (n + 1) (fun i => (word s).getD i false) Y := by
      simpa only [Realizes, hs] using hy
    have hl' : Agree (2 * (n + 1)) (fun i => (word t).getD i false) L := by
      simpa only [Realizes, ht] using hl
    exact ((code_agree hy' hl') n (by omega)).symm.trans h

theorem code_arith {Y L : OracleFamily}
    (hY : ArithmeticOracle Y) (hL : ArithmeticOracle L) :
    ArithmeticOracle (fun O v => code (Y O v) (L O v)) := by
  let base := left_primrec.comp (left_primrec.comp left_primrec)
  let n := right_primrec.comp (left_primrec.comp left_primrec)
  let s := right_primrec.comp left_primrec
  let t := right_primrec
  have hs := equal (Primrec.list_length.comp (word_primrec.comp s)) (Primrec.succ.comp n)
  have ht := equal (Primrec.list_length.comp (word_primrec.comp t))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.succ.comp n))
  have hy := realizes_arith hY base s
  have hl := realizes_arith hL base t
  have hb := Arith.pure _ (Primrec.eq.comp
    (FiniteShuffleComputation.wordShuffleBit_primrec.comp
      ((word_primrec.comp s).pair ((word_primrec.comp t).pair n))) (Primrec.const true))
  exact (hs.and (ht.and (hy.and (hl.and hb)))).ex.ex.congr (fun O v => by
    simpa only [base,n,s,t,left,right,Nat.unpair_pair] using
      (code_bit_iff (Y O (left v)) (L O (left v)) (right v)).symm)

end TuringRigidity.ArithmeticShuffleGraph

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticSourceEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticSourceEquation
open UniformArithmetic ArithmeticProgramGraph ArithmeticShuffleGraph GenericIdentity

theorem equation_arith (p : OracleCode) {P Y L R : OracleFamily}
    (hP : ArithmeticOracle P) (hY : ArithmeticOracle Y)
    (hL : ArithmeticOracle L) (hR : ArithmeticOracle R) :
    Arith (fun O v => SourceEquation p (P O v) (Y O v, L O v, R O v)) := by
  have hYL := code_arith hY hL
  have hYR := code_arith hY hR
  have hi := ArithmeticPrincipalIntersection.principal_arith (value_arith p hP hY)
    (join_arith (value_arith p hP hYL) (value_arith p hP hL))
    (join_arith (value_arith p hP hYR) (value_arith p hP hR))
  exact (total_arith p hP hY).and ((total_arith p hP hL).and
    ((total_arith p hP hR).and ((total_arith p hP hYL).and
      ((total_arith p hP hYR).and hi))))

end TuringRigidity.ArithmeticSourceEquation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticSourceTruth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticSourceTruth
open UniformArithmetic ArithmeticPrefixForcing GenericIdentity GenericTruth ShuffleRequirements

theorem binary_column_arith {B : OracleFamily} (hB : ArithmeticOracle B) (b : Bool) :
    ArithmeticOracle (fun O v => PairGenericSelection.column b (B O v)) := by
  have he := Primrec.nat_mul.comp (Primrec.const 2) right_primrec
  cases b with
  | false => exact query_at hB left_primrec he
  | true => exact query_at hB left_primrec (Primrec.succ.comp he)

theorem triple_equation_arith (p : OracleCode) :
    Arith (fun O _ => SourceEquation p (O 1) (triple (O 0))) :=
  ArithmeticSourceEquation.equation_arith p (parameter_arith 1)
    (binary_column_arith (parameter_arith 0) false)
    (binary_column_arith (binary_column_arith (parameter_arith 0) true) false)
    (binary_column_arith (binary_column_arith (parameter_arith 0) true) true)

end TuringRigidity.ArithmeticSourceTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticPrefixFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticPrefixFamilies
open UniformArithmetic ArithmeticPrefixForcing ShuffleRequirements FiniteShuffle

theorem prefix_comp {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q)
    {f : ℕ → ℕ} (hf : Primrec f) : ArithmeticPrefix (fun O v => Q O (f v)) :=
  (hQ.comp _ (Primrec₂.natPair.comp (hf.comp left_primrec) right_primrec)).congr
    (fun _ _ => by simp only [left,right,Nat.unpair_pair])

theorem prefix_exists {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q) :
    ArithmeticPrefix (fun O v s => ∃ n, Q O (Nat.pair v n) s) :=
  ((hQ.comp _ (Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (left_primrec.comp left_primrec) right_primrec)
    (right_primrec.comp left_primrec))).ex).congr
      (fun _ _ => by simp only [left,right,Nat.unpair_pair])

theorem dense_and {D E : List Bool → Prop} (hD : DenseOpen D) (hE : DenseOpen E) :
    DenseOpen (fun s => D s ∧ E s) := by
  constructor
  · intro s
    obtain ⟨t,hst,ht⟩ := hD.1 s
    obtain ⟨u,htu,hu⟩ := hE.1 t
    exact ⟨u,hst.trans htu,hD.2 t u htu ht,hu⟩
  · intro s t hst hs
    exact ⟨hD.2 s t hst hs.1,hE.2 s t hst hs.2⟩

theorem dense_true : DenseOpen (fun _ : List Bool => True) :=
  ⟨fun s => ⟨s,List.prefix_rfl,True.intro⟩,fun _ _ _ _ => True.intro⟩

theorem avoid_truth_of_decides (Q : List Bool → Prop) (hQ : Upward Q) (G : Oracle)
    (hG : G ∈ OpenSet (Decides Q)) :
    G ∈ OpenSet (Avoid Q) ↔ ¬ G ∈ OpenSet Q := by
  constructor
  · rintro ⟨s,hs,hGs⟩ ⟨t,ht,hGt⟩
    obtain ⟨u,hsu,htu,_⟩ := realizes_common hGs hGt
    exact hs u hsu (hQ t u htu ht)
  · intro hn
    obtain ⟨s,hs,hGs⟩ := hG
    rcases hs with hs | hs
    · exact False.elim (hn ⟨s,hs,hGs⟩)
    · exact ⟨s,hs,hGs⟩

end TuringRigidity.ArithmeticPrefixFamilies

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticTruthRequirements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticTruthRequirements
open UniformArithmetic ArithmeticPrefixForcing ArithmeticPrefixFamilies
open ArithmeticGenericTruth FiniteShuffle ShuffleRequirements
open EncodedForcing (word word_primrec)

theorem arithmetic_truth_requirements {P : Predicate} (hP : Arith P) :
    ∃ Q D : PrefixPredicate, ArithmeticPrefix Q ∧ ArithmeticPrefix D ∧
      (∀ O v, Upward (Q O v)) ∧
      (∀ O v n, DenseOpen (D O (Nat.pair v n))) ∧
      ∀ O v G, GenericFor (fun n => D O (Nat.pair v n)) G →
        (P (Function.update O 0 G) v ↔ G ∈ OpenSet (Q O v)) := by
  have htrue : ArithmeticPrefix (fun _ _ _ => True) :=
    (equal (Primrec.const 0) (Primrec.const 0)).congr (fun _ _ => by simp)
  induction hP with
  | pure P hP =>
    refine ⟨fun _ v _ => P v, fun _ _ _ => True, .pure _ (hP.comp left_primrec), htrue,
      fun _ _ _ _ _ h => h, fun _ _ _ => dense_true, ?_⟩
    intro O v G _
    exact (open_constant _ _).symm
  | query i =>
    by_cases hi : i = 0
    · subst i
      let Q : PrefixPredicate := fun _ v s => v < s.length ∧ s.getD v false = true
      have hQ : ArithmeticPrefix Q :=
        (less left_primrec (Primrec.list_length.comp (word_primrec.comp right_primrec))).and
          (.pure _ (Primrec.eq.comp ((Primrec.list_getD false).comp
            (word_primrec.comp right_primrec) left_primrec) (Primrec.const true)))
      refine ⟨Q,fun _ _ _ => True,hQ,htrue,?_,fun _ _ _ => dense_true,?_⟩
      · intro O v s t hst hs
        exact ⟨lt_of_lt_of_le hs.1 hst.length_le,
          (getD_of_prefix hst v hs.1).symm.trans hs.2⟩
      · intro O v G _
        simp only [Function.update_self]
        constructor
        · intro hv
          refine ⟨initial G (v+1),⟨?_,?_⟩,
            (realizes_initial _ _ _).mpr (fun _ _ => rfl)⟩
          · simp
          · exact (prefix_getD G _ v (by omega)).trans hv
        · rintro ⟨s,hs,hGs⟩
          exact (hGs v hs.1).symm.trans hs.2
    · refine ⟨fun O v _ => O i v = true, fun _ _ _ => True, (Arith.query i).comp _ left_primrec, htrue,
        fun _ _ _ _ _ h => h, fun _ _ _ => dense_true, ?_⟩
      intro O v G _
      simpa only [Function.update_of_ne hi] using (open_constant (O i v = true) G).symm
  | neg h ih =>
    obtain ⟨Q,D,hQ,hD,hup,hden,ht⟩ := ih
    let E : PrefixPredicate := fun O v s => D O v s ∧ Decides (Q O (left v)) s
    have hE : ArithmeticPrefix E := hD.and (prefix_comp (decides_arith hQ) left_primrec)
    refine ⟨fun O v => Avoid (Q O v),E,avoids_arith hQ,hE,
      fun O v => avoids_upward _,?_,?_⟩
    · intro O v n
      simpa only [E,left,Nat.unpair_pair] using
        dense_and (hden O v n) (decides_dense (Q O v) (hup O v))
    · intro O v G hG
      have hGD : GenericFor (fun n => D O (Nat.pair v n)) G := by
        intro n
        obtain ⟨s,hs,hGs⟩ := hG n
        exact ⟨s,hs.1,hGs⟩
      have hdec : G ∈ OpenSet (Decides (Q O v)) := by
        obtain ⟨s,hs,hGs⟩ := hG 0
        exact ⟨s,by simpa only [left,Nat.unpair_pair] using hs.2,hGs⟩
      exact (not_congr (ht O v G hGD)).trans
        (avoid_truth_of_decides (Q O v) (hup O v) G hdec).symm
  | and h k ih ik =>
    obtain ⟨Q,D,hQ,hD,hQu,hDd,hQt⟩ := ih
    obtain ⟨R,E,hR,hE,hRu,hEd,hRt⟩ := ik
    let F : PrefixPredicate := fun O v s =>
      D O (Nat.pair (left v) (left (right v))) s ∧
      E O (Nat.pair (left v) (right (right v))) s
    have hF : ArithmeticPrefix F :=
      (prefix_comp hD (Primrec₂.natPair.comp left_primrec (left_primrec.comp right_primrec))).and
      (prefix_comp hE (Primrec₂.natPair.comp left_primrec (right_primrec.comp right_primrec)))
    refine ⟨fun O v s => Q O v s ∧ R O v s,F,hQ.and hR,hF,
      fun O v s t hst hs => ⟨hQu O v s t hst hs.1,hRu O v s t hst hs.2⟩,?_,?_⟩
    · intro O v n
      simpa only [F,left,right,Nat.unpair_pair] using
        dense_and (hDd O v (left n)) (hEd O v (right n))
    · intro O v G hG
      have hGD : GenericFor (fun n => D O (Nat.pair v n)) G := by
        intro n
        obtain ⟨s,hs,hGs⟩ := hG (Nat.pair n 0)
        exact ⟨s,by simpa only [left,right,Nat.unpair_pair] using hs.1,hGs⟩
      have hGE : GenericFor (fun n => E O (Nat.pair v n)) G := by
        intro n
        obtain ⟨s,hs,hGs⟩ := hG (Nat.pair 0 n)
        exact ⟨s,by simpa only [left,right,Nat.unpair_pair] using hs.2,hGs⟩
      exact (and_congr (hQt O v G hGD) (hRt O v G hGE)).trans
        (open_and (Q O v) (R O v) (hQu O v) (hRu O v) G).symm
  | ex h ih =>
    obtain ⟨Q,D,hQ,hD,hup,hden,ht⟩ := ih
    let E : PrefixPredicate := fun O v =>
      D O (Nat.pair (Nat.pair (left v) (left (right v))) (right (right v)))
    have hE : ArithmeticPrefix E := prefix_comp hD
      (Primrec₂.natPair.comp
        (Primrec₂.natPair.comp left_primrec (left_primrec.comp right_primrec))
        (right_primrec.comp right_primrec))
    refine ⟨fun O v s => ∃ n, Q O (Nat.pair v n) s,E,prefix_exists hQ,hE,?_,?_,?_⟩
    · rintro O v s t hst ⟨n,hn⟩
      exact ⟨n,hup O _ s t hst hn⟩
    · intro O v n
      simpa only [E,left,right,Nat.unpair_pair] using
        hden O (Nat.pair v (left n)) (right n)
    · intro O v G hG
      have hGD (n : ℕ) : GenericFor (fun k => D O (Nat.pair (Nat.pair v n) k)) G := by
        intro k
        simpa only [E,left,right,Nat.unpair_pair] using hG (Nat.pair n k)
      constructor
      · rintro ⟨n,hn⟩
        obtain ⟨s,hs,hGs⟩ := (ht O _ G (hGD n)).mp hn
        exact ⟨s,⟨n,hs⟩,hGs⟩
      · rintro ⟨s,⟨n,hs⟩,hGs⟩
        exact ⟨n,(ht O _ G (hGD n)).mpr ⟨s,hs,hGs⟩⟩
  | comp f h hf ih =>
    obtain ⟨Q,D,hQ,hD,hup,hden,ht⟩ := ih
    let E : PrefixPredicate := fun O v => D O (Nat.pair (f (left v)) (right v))
    refine ⟨fun O v => Q O (f v),E,prefix_comp hQ hf,
      prefix_comp hD (Primrec₂.natPair.comp (hf.comp left_primrec) right_primrec),
      fun O v => hup O (f v),?_,?_⟩
    · intro O v n
      simpa only [E,left,right,Nat.unpair_pair] using hden O (f v) n
    · intro O v G hG
      apply ht O (f v) G
      simpa only [E,left,right,Nat.unpair_pair] using hG

end TuringRigidity.ArithmeticTruthRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticFiniteTruthTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticFiniteTruthTransfer
open UniformArithmetic ArithmeticPrefixForcing ArithmeticPrefixFamilies
open ShuffleRequirements FiniteShuffle GenericIdentity GenericTruth
open EncodedForcing (word)

theorem generic_meets_family {D : PrefixPredicate} (hD : ArithmeticPrefix D)
    (O : Oracles) (v : ℕ) (hd : ∀ n, DenseOpen (D O (Nat.pair v n)))
    (G : Oracle) (hG : Generic O G) :
    GenericFor (fun n => D O (Nat.pair v n)) G := by
  intro n
  have ha : Arith (fun O s => D O (Nat.pair v n) (word s)) :=
    (hD.comp _ (Primrec₂.natPair.comp (Primrec.const (Nat.pair v n)) Primrec.id)).congr
      (fun _ _ => by simp only [left,right,Nat.unpair_pair,id_eq])
  exact hG (fun O s => D O (Nat.pair v n) s) ha (hd n)

theorem finite_family_of_dense {P : Predicate} (hP : Arith P) (O : Oracles) (v : ℕ)
    (hd : ∀ s : List Bool, ∃ H : Oracle,
      Generic O H ∧ Realizes s H ∧ P (Function.update O 0 H) v) :
    ∃ E : PrefixPredicate, ArithmeticPrefix E ∧ (∀ n, DenseOpen (E O n)) ∧
      ∀ G : Oracle, GenericFor (E O) G → P (Function.update O 0 G) v := by
  obtain ⟨Q,D,hQ,hD,hup,hden,ht⟩ := ArithmeticTruthRequirements.arithmetic_truth_requirements hP
  have hqd : DenseOpen (Q O v) := by
    refine ⟨?_,hup O v⟩
    intro s
    obtain ⟨H,hH,hs,hPH⟩ := hd s
    have hHD := generic_meets_family hD O v (hden O v) H hH
    obtain ⟨t,htQ,htH⟩ := (ht O v H hHD).mp hPH
    obtain ⟨u,hsu,htu,_⟩ := realizes_common hs htH
    exact ⟨u,hsu,hup O v t u htu htQ⟩
  let E : PrefixPredicate := fun O n s => D O (Nat.pair v n) s ∧ Q O v s
  have hE : ArithmeticPrefix E :=
    (prefix_comp hD (Primrec₂.natPair.comp (Primrec.const v) Primrec.id)).and
      (prefix_comp hQ (Primrec.const v))
  refine ⟨E,hE,fun n => dense_and (hden O v n) hqd,?_⟩
  intro G hG
  have hGD : GenericFor (fun n => D O (Nat.pair v n)) G := by
    intro n
    obtain ⟨s,hs,hGs⟩ := hG n
    exact ⟨s,hs.1,hGs⟩
  apply (ht O v G hGD).mpr
  obtain ⟨s,hs,hGs⟩ := hG 0
  exact ⟨s,hs.2,hGs⟩

theorem source_equation_finite_family_oai (p : OracleCode) (P : Oracle)
    (hd : ∀ s : List Bool, ∃ H : Oracle,
      Generic (fun _ => P) H ∧ Realizes s H ∧ SourceEquation p P (triple H)) :
    ∃ E : PrefixPredicate, ArithmeticPrefix E ∧
      (∀ n, DenseOpen (E (fun _ => P) n)) ∧
      ∀ G : Oracle, GenericFor (E (fun _ => P)) G → SourceEquation p P (triple G) := by
  have hden : ∀ s : List Bool, ∃ H : Oracle,
      Generic (fun _ => P) H ∧ Realizes s H ∧
        SourceEquation p ((Function.update (fun _ => P) 0 H) 1)
          (triple ((Function.update (fun _ => P) 0 H) 0)) := by
    simpa using hd
  simpa using finite_family_of_dense (ArithmeticSourceTruth.triple_equation_arith p)
    (fun _ => P) 0 hden

end TuringRigidity.ArithmeticFiniteTruthTransfer

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.ArithmeticFiniteTruthTransfer.source_equation_finite_family_oai := @OAI.TuringRigidity.ArithmeticFiniteTruthTransfer.source_equation_finite_family_oai
