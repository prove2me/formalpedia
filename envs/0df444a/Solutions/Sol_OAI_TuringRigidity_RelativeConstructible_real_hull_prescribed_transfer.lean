-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:35:51.06978+00:00
-- url     : https://prove2.me/submissions/42ccda88-fe47-4c16-be52-b3945bd6f68f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_ArithmeticFiniteTruthTransfer_source_equation_finite_family
import Theorems.Thm_OAI_TuringRigidity_GroundIteratedTriple_generic_triple_of_arithmetic
import Theorems.Thm_OAI_TuringRigidity_IteratedGenericCommonIdeal_ideal_of_iterated_generics
import Theorems.Thm_OAI_TuringRigidity_RealHullGenericTriple_exists_generic_prefix_triple
import Theorems.Thm_OAI_TuringRigidity_RealHullIteration_exists_iterated_pair
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_real_hull_generic_column_realizes
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_real_hull_shuffled_column_realizes

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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_BranchFrequency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

namespace UniformOracle

theorem runningSum_recursive {O : Set (ℕ →. ℕ)} {f : ℕ → ℕ}
    (hf : Nat.RecursiveIn O (fun n => Part.some (f n))) :
    Nat.RecursiveIn O (fun n => Part.some (runningSum f n)) := by
  have hy := total_primrec (O := O) (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hi := total_primrec (O := O) (Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.snd.comp Primrec.unpair)))
  have hs := total_comp (total_primrec (Primrec.nat_add.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)))
    (total_pair hi (total_comp hf hy))
  have hp := Nat.RecursiveIn.prec (total_primrec (Primrec.const 0)) hs
  have hh := Nat.RecursiveIn.comp hp
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply hh.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    change (Part.some (runningSum f n)).bind _ = _
    rw [Part.bind_some]
    rfl
end UniformOracle

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericCoding
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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

theorem count_mono (G : Oracle) : Monotone (count G) := by
  apply monotone_nat_of_le_succ
  intro n
  change count G n ≤ count G n + bit G (2*n+1)
  omega

theorem count_unbounded (G : Oracle) (hG : InfiniteOdd G) (k : ℕ) :
    ∃ n, k ≤ count G n := by
  induction k with
  | zero => exact ⟨0,by simp [count,runningSum]⟩
  | succ k ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨m,hm,hb⟩ := hG n
    have hc := count_mono G hm
    refine ⟨m+1,?_⟩
    change k+1 ≤ count G m + bit G (2*m+1)
    simp only [bit,hb,↓reduceIte]
    omega

theorem exists_insertion (G : Oracle) (hG : InfiniteOdd G) (k : ℕ) :
    ∃ n, count G n = k ∧ G (2*n+1) = true := by
  have hi : ∀ m, k < count G m → ∃ n, count G n = k ∧ G (2*n+1) = true := by
    intro m
    induction m with
    | zero => simp [count,runningSum]
    | succ m ih =>
      intro hm
      by_cases hk : k < count G m
      · exact ih hk
      · change k < count G m + bit G (2*m+1) at hm
        cases hb : G (2*m+1) with
        | false => simp [bit,hb] at hm; omega
        | true => exact ⟨m,by simp [bit,hb] at hm; omega,hb⟩
  obtain ⟨m,hm⟩ := count_unbounded G hG (k+1)
  exact hi m (by omega)

theorem count_recursive {O : Set (ℕ →. ℕ)} (G : Oracle)
    (hG : Nat.RecursiveIn O (oracleFunction G)) :
    Nat.RecursiveIn O (fun n => Part.some (count G n)) :=
  runningSum_recursive (_root_.OAI.TuringRigidity.UniformOracle.total_comp hG (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id))))

theorem code_recursive {O : Set (ℕ →. ℕ)} (A G : Oracle)
    (hA : Nat.RecursiveIn O (oracleFunction A)) (hG : Nat.RecursiveIn O (oracleFunction G)) :
    Nat.RecursiveIn O (oracleFunction (code A G)) := by
  have hc := count_recursive G hG
  have ho := _root_.OAI.TuringRigidity.UniformOracle.total_comp hG (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)))
  have ha := _root_.OAI.TuringRigidity.UniformOracle.total_comp hA hc
  have hi := _root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.nat_mul.comp (Primrec.const 2)
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair))))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id) hc)
  have he := _root_.OAI.TuringRigidity.UniformOracle.total_comp hG hi
  have hd : Primrec (fun z : ℕ => if (Nat.unpair z).1=1 then
      (Nat.unpair (Nat.unpair z).2).1 else (Nat.unpair (Nat.unpair z).2).2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 1))
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hd) (_root_.OAI.TuringRigidity.UniformOracle.total_pair ho (_root_.OAI.TuringRigidity.UniformOracle.total_pair ha he))).of_eq (fun n => by
    cases hh : G (2*n+1) <;> simp [code,oracleFunction,hh])

theorem code_reduces (A G : Oracle) : Reduces (code A G) (join A G) := by
  apply RecursiveIn.iff_nat.mpr
  exact code_recursive A G (RecursiveIn.iff_nat.mp (reduces_join_left A G))
    (RecursiveIn.iff_nat.mp (reduces_join_right A G))

theorem recoverDecision_primrec : Primrec recoverDecision :=
  Primrec.ite ((Primrec.eq.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).and
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 1)))
    (Primrec.option_some.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const none)

theorem recoverTrial_recursive (A G : Oracle) :
    Nat.RecursiveIn {oracleFunction (join (code A G) G)}
      (fun z => Part.some (encode (recoverTrial A G (Nat.unpair z).1 (Nat.unpair z).2))) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction (join (code A G) G)}
  have hg : Nat.RecursiveIn O (oracleFunction G) := RecursiveIn.iff_nat.mp (reduces_join_right (code A G) G)
  have ha : Nat.RecursiveIn O (oracleFunction (code A G)) := RecursiveIn.iff_nat.mp (reduces_join_left (code A G) G)
  have hk := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.fst.comp Primrec.unpair)
  have hn := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.snd.comp Primrec.unpair)
  have hc := _root_.OAI.TuringRigidity.UniformOracle.total_comp (count_recursive G hg) hn
  have ho := _root_.OAI.TuringRigidity.UniformOracle.total_comp hg (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.succ.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair))))
  have ha' := _root_.OAI.TuringRigidity.UniformOracle.total_comp ha hn
  have hd := (Primrec.fst.comp Primrec.unpair).pair
    (((Primrec.fst.comp Primrec.unpair).pair
      (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).comp (Primrec.snd.comp Primrec.unpair))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.encode.comp (recoverDecision_primrec.comp hd)))
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair hk (_root_.OAI.TuringRigidity.UniformOracle.total_pair hc (_root_.OAI.TuringRigidity.UniformOracle.total_pair ho ha')))).of_eq (fun z => by simp [recoverTrial,bit])

theorem recoverTrial_sound (A G : Oracle) (k n a : ℕ) (ha : a ∈ recoverTrial A G k n) :
    a = bit A k := by
  unfold recoverTrial recoverDecision at ha
  split at ha
  · rename_i h
    have hg : G (2*n+1) = true := by cases hh : G (2*n+1) <;> simp_all [bit]
    have hk : k = count G n := h.1
    simpa [bit,code,hg,←hk] using (Option.mem_def.mp ha).symm
  · simp at ha

theorem recoverTrial_complete (A G : Oracle) (hG : InfiniteOdd G) (k : ℕ) :
    ∃ n a, a ∈ recoverTrial A G k n := by
  obtain ⟨n,hn,hg⟩ := exists_insertion G hG k
  exact ⟨n,bit A k,by simp [recoverTrial,recoverDecision,hn,hg,bit,code]⟩

theorem set_reduces_code_join (A G : Oracle) (hG : InfiniteOdd G) :
    Reduces A (join (code A G) G) := by
  apply RecursiveIn.iff_nat.mpr
  exact total_search (recoverTrial_recursive A G) (bit A) (recoverTrial_sound A G)
    (recoverTrial_complete A G hG)

theorem join_degree_eq (A G : Oracle) (hG : InfiniteOdd G) :
    degree (join (code A G) G) = degree (join A G) := by
  apply (degree_eq_iff _ _).mpr
  exact ⟨join_reduces (code_reduces A G) (reduces_join_right A G),
    join_reduces (set_reduces_code_join A G hG) (reduces_join_right (code A G) G)⟩

end TuringRigidity.GenericCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffle
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ShuffleRequirements
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ShuffleRequirements
open FiniteShuffle GenericCoding Set

theorem oddHit_denseOpen (N : ℕ) : DenseOpen (OddHit N) := by
  constructor
  · intro s
    let i := N+s.length
    let H : Oracle := fun j => if j < s.length then s.getD j false else true
    refine ⟨initial H (2*i+2),?_,i,by omega,by simp,?_⟩
    · rw [←prefix_default s]
      apply initial_prefix (n := s.length) (m := 2*i+2) (by dsimp [i]; omega)
      intro j hj
      simp [H,hj]
    · rw [prefix_getD _ _ _ (by omega)]
      simp [H,show ¬2*i+1 < s.length by dsimp [i]; omega]
  · intro s t hst
    rintro ⟨i,hNi,hi,hb⟩
    exact ⟨i,hNi,lt_of_lt_of_le hi hst.length_le,(getD_of_prefix hst _ hi).symm.trans hb⟩

theorem infiniteOdd_of_hits (G : Oracle) (hg : GenericFor OddHit G) : InfiniteOdd G := by
  intro N
  obtain ⟨s,⟨i,hNi,hi,hb⟩,hs⟩ := hg N
  exact ⟨i,hNi,(hs _ hi).symm.trans hb⟩

end TuringRigidity.ShuffleRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealSelection
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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

theorem common_lower_transport (π : Degree ≃o Degree) (a l r : Degree)
    (h : ∀ b, b ≤ a ↔ b ≤ l ∧ b ≤ r) :
    ∀ b, b ≤ π a ↔ b ≤ π l ∧ b ≤ π r := by
  intro b
  have hh := h (π.symm b)
  simpa only [π.symm_apply_le] using hh

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericIdentity
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_SourceIdentity
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericIdentity

theorem imageJoin_degree (π : Degree ≃o Degree) (p : OracleCode) (P Y G : Oracle)
    (hG : RepresentsAt π p P G) (hC : RepresentsAt π p P (GenericCoding.code Y G))
    (hi : GenericCoding.InfiniteOdd G) :
    degree (ImageJoin p P Y G) = π (degree (join Y G)) := by
  change degree (value p P (GenericCoding.code Y G)) ⊔ degree (value p P G) = _
  rw [hC.2,hG.2,←π.map_sup]
  exact congrArg π (GenericCoding.join_degree_eq Y G hi)

theorem source_5_4 (π : Degree ≃o Degree) (p : OracleCode) (P Y G0 G1 : Oracle)
    (hG0 : RepresentsAt π p P G0) (hG1 : RepresentsAt π p P G1)
    (hC0 : RepresentsAt π p P (GenericCoding.code Y G0))
    (hC1 : RepresentsAt π p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection Y (join Y G0) (join Y G1)) :
    ∀ b : Degree, b ≤ π (degree Y) ↔
      b ≤ degree (ImageJoin p P Y G0) ∧ b ≤ degree (ImageJoin p P Y G1) := by
  rw [imageJoin_degree π p P Y G0 hG0 hC0 hi0,
    imageJoin_degree π p P Y G1 hG1 hC1 hi1]
  exact common_lower_transport π _ _ _ hI

theorem source_5_5_iff (π : Degree ≃o Degree) (p : OracleCode) (P Y G0 G1 : Oracle)
    (hG0 : RepresentsAt π p P G0) (hG1 : RepresentsAt π p P G1)
    (hC0 : RepresentsAt π p P (GenericCoding.code Y G0))
    (hC1 : RepresentsAt π p P (GenericCoding.code Y G1))
    (hi0 : GenericCoding.InfiniteOdd G0) (hi1 : GenericCoding.InfiniteOdd G1)
    (hI : PrincipalIntersection Y (join Y G0) (join Y G1)) :
    SourceEquation p P (Y,G0,G1) ↔ RepresentsAt π p P Y := by
  have h := source_5_4 π p P Y G0 G1 hG0 hG1 hC0 hC1 hi0 hi1 hI
  constructor
  · rintro ⟨hY,_,_,_,_,he⟩
    refine ⟨hY,le_antisymm ?_ ?_⟩
    · exact (h _).mpr ((he _).mp le_rfl)
    · exact (he _).mpr ((h _).mp le_rfl)
  · rintro ⟨hY,hdeg⟩
    refine ⟨hY,hG0.1,hG1.1,hC0.1,hC1.1,?_⟩
    intro b
    change b ≤ degree (value p P Y) ↔ _
    rw [hdeg]
    exact h b

end TuringRigidity.GenericIdentity

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

theorem canonical_wordCodeGraph (p : List Bool) (q : ZFSet.{0}) :
    ZFSet.pair (natSet (encode p)) q ∈ wordCodeGraph ↔ q = wordCode p := by
  simp only [pair_mem_wordCodeGraph,word,encodek,Option.getD_some]

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenFilters
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory InternalCollapse CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem filter_ext {P : Type*} [Preorder P] (F H : GenericFilter P)
    (h : F.carrier = H.carrier) : F = H := by
  cases F; cases H; cases h; rfl

theorem pull_push (G : GenericFilter Condition) : pullFilter (pushFilter G) = G := by
  have he : (pullFilter (pushFilter G)).carrier = G.carrier := by
    ext p; simp [pullFilter,pushFilter]
  exact filter_ext _ _ he

theorem dense_pull_iff (D : Set (Conditions conditions)) :
    Dense {p : Condition | conditionEquiv p ∈ D} ↔ Dense D := by
  constructor
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv.symm q)
    exact ⟨conditionEquiv p,by simpa using conditionEquiv.monotone hp,hpD⟩
  · intro h q
    obtain ⟨p,hp,hpD⟩ := h (conditionEquiv q)
    exact ⟨conditionEquiv.symm p,by simpa using conditionEquiv.symm.monotone hp,
      by simpa using hpD⟩

theorem groundGeneric_iff (M : ZFSet.{0}) (G : GenericFilter (Conditions conditions)) :
    AtomicForcing.GroundGeneric M G ↔
      ∀ D ∈ M, Dense {p : Condition | wordCode p.word ∈ D} →
        ∃ p ∈ (pullFilter G).carrier, wordCode p.word ∈ D := by
  have hl (p : Condition) : label conditions (conditionEquiv p) = wordCode p.word :=
    label_encodeCondition p
  constructor
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mp (by simpa only [Set.mem_ofPred_eq,hl] using hd)
    obtain ⟨q,hq,hqD⟩ := h D hD hd'
    refine ⟨conditionEquiv.symm q,by simpa [pullFilter] using hq,?_⟩
    simpa only [←hl,OrderIso.apply_symm_apply] using hqD
  · intro h D hD hd
    have hd' := (dense_pull_iff {p | label conditions p ∈ D}).mpr hd
    obtain ⟨q,hq,hqD⟩ := h D hD (by simpa only [Set.mem_ofPred_eq,hl] using hd')
    exact ⟨conditionEquiv q,hq,by simpa only [hl] using hqD⟩

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalCohenSets
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable

theorem wordImage_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : realCode A ∈ M) : wordImage A ∈ M := by
  let e := cons (realCode A) (fun _ => wordCodeGraph)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i with
    | zero => exact hA
    | succ i => exact wordCodeGraph_mem M hM hT
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 0 1 3)) e he (conditions_mem M hM hT)
  simpa only [wordImage,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using hh

theorem wordImage_spec (P : List Bool → Prop) (A : Oracle)
    (hA : ∀ n, A n = true ↔ P (EncodedForcing.word n)) (p : List Bool) :
    wordCode p ∈ wordImage A ↔ P p := by
  rw [wordImage,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,hx,hq⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset _ hx)
    have hp := wordCode_injective ((pair_mem_wordCodeGraph _ _).mp hq)
    rw [hp]
    exact (hA n).mp ((natSet_mem_realCode _ _).mp hx)
  · intro hp
    exact ⟨(mem_conditions _).mpr ⟨_,wordCode_function _⟩,natSet (encode p),
      (natSet_mem_realCode _ _).mpr ((hA _).mpr (by simpa [EncodedForcing.word] using hp)),
      (canonical_wordCodeGraph p _).mpr rfl⟩

end TuringRigidity.InternalCohen

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenOddHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory UniformArithmetic Encodable
open ShuffleRequirements CohenBorelForcing CountableForcing
open EncodedForcing (word word_primrec)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem oddHit_arith (N : ℕ) : Arith (fun (_ : Oracles) v => OddHit N (word v)) := by
  have hi := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) right_primrec)
    (Primrec.const 1)
  have hn := Arith.pure (fun v => N ≤ right v) (Primrec.nat_le.comp (Primrec.const N) right_primrec)
  have hlen := less hi (Primrec.list_length.comp (word_primrec.comp left_primrec))
  have hb := Arith.pure _ (Primrec.eq.comp
    ((Primrec.list_getD false).comp (word_primrec.comp left_primrec) hi) (Primrec.const true))
  exact (hn.and (hlen.and hb)).ex.congr (fun _ _ => by
    simp only [OddHit,left,right,Nat.unpair_pair])

theorem oddHitCodes_true (N n : ℕ) : oddHitCodes N n = true ↔ OddHit N (word n) :=
  arithmeticReal_true _ _ _

theorem oddHitCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (N : ℕ) :
    realCode (oddHitCodes N) ∈ M := by
  apply sourceT_arithmetic_comprehension M hM hT (oddHit_arith N)
  intro _
  change realCode (decodeReal (∅ : ZFSet.{0})) ∈ M
  rw [realCode_decodeReal (fun x h => False.elim (ZFSet.notMem_empty x h))]
  exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨0,rfl⟩)

theorem groundGeneric_infiniteOdd (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : Oracle) (hG : AtomicForcing.GroundGeneric M (pushFilter (realFilter G))) :
    GenericCoding.InfiniteOdd G := by
  apply infiniteOdd_of_hits
  intro N
  have hspec (s : List Bool) := wordImage_spec (OddHit N) (oddHitCodes N) (oddHitCodes_true N) s
  have hd : Dense {p : Condition | wordCode p.word ∈ wordImage (oddHitCodes N)} := by
    intro p
    obtain ⟨s,hps,hs⟩ := (oddHit_denseOpen N).1 p.word
    exact ⟨⟨s⟩,hps,(hspec s).mpr hs⟩
  obtain ⟨p,hp,hpD⟩ := (groundGeneric_iff M _).mp hG (wordImage (oddHitCodes N))
    (wordImage_mem M hM hT _ (oddHitCodes_mem M hM hT N)) hd
  rw [pull_push] at hp
  exact ⟨p.word,(hspec p.word).mp hpD,hp⟩

end TuringRigidity.InternalCohen

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

theorem open_avoid {Q : PrefixPredicate} (hQ : ArithmeticPrefix Q)
    (hup : ∀ O v, Upward (Q O v)) (O : Oracles) (v : ℕ) (G : Oracle)
    (hG : Generic O G) :
    G ∈ OpenSet (Avoid (Q O v)) ↔ ¬ G ∈ OpenSet (Q O v) := by
  constructor
  · rintro ⟨s,hs,hGs⟩ ⟨t,ht,hGt⟩
    obtain ⟨u,hsu,htu,_⟩ := realizes_common hGs hGt
    exact hs u hsu (hup O v t u htu ht)
  · intro hn
    have hd : Arith (fun O n => Decides (Q O v) (word n)) :=
      ((decides_arith hQ).comp _ (Primrec₂.natPair.comp (Primrec.const v) Primrec.id)).congr
        (fun _ _ => by simp only [left,right,Nat.unpair_pair,id_eq])
    obtain ⟨s,hs,hGs⟩ := hG (fun O s => Decides (Q O v) s) hd (decides_dense _ (hup O v))
    rcases hs with hs | hs
    · exact False.elim (hn ⟨s,hs,hGs⟩)
    · exact ⟨s,hs,hGs⟩

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

theorem arithmetic_generic_truth {P : Predicate} (hP : Arith P) :
    ∃ Q : PrefixPredicate, ArithmeticPrefix Q ∧ (∀ O v, Upward (Q O v)) ∧
      ∀ O v G, Generic O G →
        (P (Function.update O 0 G) v ↔ G ∈ OpenSet (Q O v)) := by
  induction hP with
  | pure P hP =>
    refine ⟨fun _ v _ => P v, .pure _ (hP.comp left_primrec),
      fun _ _ _ _ _ h => h, ?_⟩
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
      refine ⟨Q,hQ,?_,?_⟩
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
    · refine ⟨fun O v _ => O i v = true, (Arith.query i).comp _ left_primrec,
        fun _ _ _ _ _ h => h, ?_⟩
      intro O v G _
      simpa only [Function.update_of_ne hi] using (open_constant (O i v = true) G).symm
  | neg h ih =>
    obtain ⟨Q,hQ,hup,ht⟩ := ih
    refine ⟨fun O v => Avoid (Q O v), avoids_arith hQ, fun O v => avoids_upward _, ?_⟩
    intro O v G hG
    exact (not_congr (ht O v G hG)).trans (open_avoid hQ hup O v G hG).symm
  | and h k ih ik =>
    obtain ⟨Q,hQ,hQu,hQt⟩ := ih
    obtain ⟨R,hR,hRu,hRt⟩ := ik
    refine ⟨fun O v s => Q O v s ∧ R O v s, hQ.and hR,
      fun O v s t hst hs => ⟨hQu O v s t hst hs.1,hRu O v s t hst hs.2⟩, ?_⟩
    intro O v G hG
    exact (and_congr (hQt O v G hG) (hRt O v G hG)).trans
      (open_and (Q O v) (R O v) (hQu O v) (hRu O v) G).symm
  | ex h ih =>
    obtain ⟨Q,hQ,hup,ht⟩ := ih
    have he : ArithmeticPrefix (fun O v s => ∃ n, Q O (Nat.pair v n) s) :=
      ((hQ.comp _ (Primrec₂.natPair.comp
        (Primrec₂.natPair.comp (left_primrec.comp left_primrec) right_primrec)
        (right_primrec.comp left_primrec))).ex).congr
          (fun _ _ => by simp only [left,right,Nat.unpair_pair])
    refine ⟨fun O v s => ∃ n, Q O (Nat.pair v n) s, he, ?_, ?_⟩
    · rintro O v s t hst ⟨n,hn⟩
      exact ⟨n,hup O _ s t hst hn⟩
    · intro O v G hG
      constructor
      · rintro ⟨n,hn⟩
        obtain ⟨s,hs,hGs⟩ := (ht O _ G hG).mp hn
        exact ⟨s,⟨n,hs⟩,hGs⟩
      · rintro ⟨s,⟨n,hs⟩,hGs⟩
        exact ⟨n,(ht O _ G hG).mpr ⟨s,hs,hGs⟩⟩
  | comp f h hf ih =>
    obtain ⟨Q,hQ,hup,ht⟩ := ih
    refine ⟨fun O v => Q O (f v), ?_, fun O v => hup O (f v),
      fun O v G hG => ht O (f v) G hG⟩
    exact (hQ.comp _ (Primrec₂.natPair.comp (hf.comp left_primrec) right_primrec)).congr
      (fun _ _ => by simp only [left,right,Nat.unpair_pair])

end TuringRigidity.ArithmeticGenericTruth

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticGenericDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ArithmeticGenericDensity
open UniformArithmetic ArithmeticPrefixForcing ArithmeticGenericTruth ShuffleRequirements
open EncodedForcing (word)

theorem truth_of_dense {P : Predicate} (hP : Arith P) (O : Oracles) (v : ℕ)
    (hd : ∀ s : List Bool, ∃ H : Oracle,
      Generic O H ∧ Realizes s H ∧ P (Function.update O 0 H) v) :
    ∀ G : Oracle, Generic O G → P (Function.update O 0 G) v := by
  obtain ⟨Q,hQ,hup,ht⟩ := arithmetic_generic_truth hP
  have har : Arith (fun O n => Q O v (word n)) :=
    (hQ.comp _ (Primrec₂.natPair.comp (Primrec.const v) Primrec.id)).congr
      (fun _ _ => by simp only [left,right,Nat.unpair_pair,id_eq])
  have hden : FiniteShuffle.DenseOpen (Q O v) := by
    refine ⟨?_,hup O v⟩
    intro s
    obtain ⟨H,hH,hs,hPH⟩ := hd s
    obtain ⟨t,htQ,htH⟩ := (ht O v H hH).mp hPH
    obtain ⟨u,hsu,htu,_⟩ := realizes_common hs htH
    exact ⟨u,hsu,hup O v t u htu htQ⟩
  intro G hG
  exact (ht O v G hG).mpr (hG (fun O s => Q O v s) har hden)

end TuringRigidity.ArithmeticGenericDensity

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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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

theorem source_equation_of_dense (p : OracleCode) (P : Oracle)
    (hd : ∀ s : List Bool, ∃ H : Oracle,
      Generic (fun _ => P) H ∧ Realizes s H ∧ SourceEquation p P (triple H)) :
    ∀ G : Oracle, Generic (fun _ => P) G → SourceEquation p P (triple G) := by
  have hden : ∀ s : List Bool, ∃ H : Oracle,
      Generic (fun _ => P) H ∧ Realizes s H ∧
        SourceEquation p ((Function.update (fun _ => P) 0 H) 1)
          (triple ((Function.update (fun _ => P) 0 H) 0)) := by
    simpa using hd
  simpa using ArithmeticGenericDensity.truth_of_dense (triple_equation_arith p)
    (fun _ => P) 0 hden

end TuringRigidity.ArithmeticSourceTruth

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GroundIteratedTriple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.GroundIteratedTriple
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open InternalCohen CohenBorelForcing UniformArithmetic
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem triple_join (Y L R : Oracle) : GenericTruth.triple (join Y (join L R)) = (Y,L,R) := by
  rw [GenericSourceTransfer.triple_join]
  have hl : PairGenericSelection.column false (join L R) = L := by
    funext n; simp [PairGenericSelection.column]
  have hr : PairGenericSelection.column true (join L R) = R := by
    funext n; simp [PairGenericSelection.column]
  rw [hl,hr]

end TuringRigidity.GroundIteratedTriple

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RealHullPrescribedTruth
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals GenericIdentity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem real_hull_prescribed_transfer_oai (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (X : Oracle) (hX : realCode X ∈ genericExtensionSet M (poset K) G.carrier)
    (π : Degree ≃o Degree) (p : OracleCode) (P : Oracle)
    (hP : realCode P ∈ RealGeneratedModel.hull M (realCode X))
    (hsem : ∀ H : GenericFilter (Conditions (poset K)),
      GroundGeneric (RealGeneratedModel.hull M (realCode X)) H →
      genericExtensionSet (RealGeneratedModel.hull M (realCode X)) (poset K) H.carrier =
        genericExtensionSet M (poset K) G.carrier →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → RepresentsAt π p P A) :
    (∀ s : List Bool, ∃ H : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => P) H ∧
      ShuffleRequirements.Realizes s H ∧ SourceEquation p P (GenericTruth.triple H)) ∧
    (∀ H : Oracle, ArithmeticPrefixForcing.Generic (fun _ => P) H →
      SourceEquation p P (GenericTruth.triple H)) ∧
    (∃ D : ArithmeticPrefixForcing.PrefixPredicate, ArithmeticPrefixForcing.ArithmeticPrefix D ∧
      (∀ n, FiniteShuffle.DenseOpen (D (fun _ => P) n)) ∧
      ∀ H : Oracle, ShuffleRequirements.GenericFor (D (fun _ => P)) H →
        SourceEquation p P (GenericTruth.triple H)) ∧
    ∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
      ArithmeticPrefixForcing.Generic (fun _ => P) Y → RepresentsAt π p P Y := by
  let N := RealGeneratedModel.hull M (realCode X)
  have hrep : ∀ A : Oracle,
      ColumnRealizesExtension N K a (genericExtensionSet M (poset K) G.carrier) A →
      RepresentsAt π p P A := by
    rintro A ⟨H,hH,he,hA⟩
    exact hsem H hH he A hA
  have hordinary : ∀ A : Oracle, realCode A ∈ genericExtensionSet M (poset K) G.carrier →
      GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter A)) →
      RepresentsAt π p P A := fun A hAE hA => hrep A
    (real_hull_generic_column_realizes M K a hM hT hK ha G hG X A hX hAE hA)
  have hshuffle : ∀ Y L : Oracle,
      realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
      realCode L ∈ genericExtensionSet M (poset K) G.carrier →
      GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) →
      RepresentsAt π p P (GenericCoding.code Y L) := fun Y L hYE hLE hL => hrep _
    (real_hull_shuffled_column_realizes M K a hM hT hK ha G hG X Y L hX hYE hLE hL)
  have hd : ∀ s : List Bool, ∃ H : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => P) H ∧
      ShuffleRequirements.Realizes s H ∧ SourceEquation p P (GenericTruth.triple H) := by
    intro s
    obtain ⟨Y,L,R,hbase,hL,hR,hi,hg,hs⟩ := RealHullGenericTriple.exists_generic_prefix_triple
      M K hM hT hK G hG X hX (fun _ => P) (fun _ => hP) s
    have hy := hbase Y (by simp)
    have hl := hbase L (by simp)
    have hr := hbase R (by simp)
    refine ⟨join Y (join L R),hg,hs,?_⟩
    rw [GroundIteratedTriple.triple_join]
    exact (source_5_5_iff π p P Y L R (hordinary L hl.1 hl.2) (hordinary R hr.1 hr.2)
      (hshuffle Y L hy.1 hl.1 hl.2) (hshuffle Y R hy.1 hr.1 hr.2) hL hR hi).mpr
        (hordinary Y hy.1 hy.2)
  have ht := ArithmeticSourceTruth.source_equation_of_dense p P hd
  refine ⟨hd,ht,ArithmeticFiniteTruthTransfer.source_equation_finite_family p P hd,?_⟩
  intro Y hYE hY
  obtain ⟨hN,hH,L,R,hLE,hRE,hL,hR⟩ :=
    RealHullIteration.exists_iterated_pair M K hM hT hK G hG X Y hX hYE
  let H := RealGeneratedModel.hull N (realCode Y)
  obtain ⟨_,_,hHF,_⟩ := RegularTreeExtension.extension_properties H InternalCohen.conditions
    hH.1 hH.2.1 (InternalCohen.conditions_mem H hH.1 hH.2.1)
    (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) hL
  have hLN : GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter L)) :=
    fun D hD hd => hL D (hH.2.2.1 hD) hd
  have hRN : GroundGeneric N (InternalCohen.pushFilter (CohenBorelForcing.realFilter R)) :=
    fun D hD hd => hR D (hHF (hH.2.2.1 hD)) hd
  have hi := IteratedGenericCommonIdeal.ideal_of_iterated_generics H hH.1 hH.2.1
    Y hH.2.2.2 L R hL hR
  have heq := ht (join Y (join L R))
    (GroundIteratedTriple.generic_triple_of_arithmetic N (fun _ => P) (fun _ => hP)
      Y L R hY hH hL hR)
  rw [GroundIteratedTriple.triple_join] at heq
  exact (source_5_5_iff π p P Y L R (hordinary L hLE hLN) (hordinary R hRE hRN)
    (hshuffle Y L hYE hLE hLN) (hshuffle Y R hYE hRE hRN)
    (InternalCohen.groundGeneric_infiniteOdd N hN.1 hN.2.1 L hLN)
    (InternalCohen.groundGeneric_infiniteOdd N hN.1 hN.2.1 R hRN) hi).mp heq

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer_oai := @OAI.TuringRigidity.RelativeConstructible.real_hull_prescribed_transfer_oai
