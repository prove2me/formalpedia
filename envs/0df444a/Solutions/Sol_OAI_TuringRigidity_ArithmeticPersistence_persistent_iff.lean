-- Prove2me | solution 1 for OAI.TuringRigidity.ArithmeticPersistence.persistent_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:22:33.403436+00:00
-- url     : https://prove2.me/submissions/fb26ebfc-0ac0-4765-be6f-404d7e707b87

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_EnumerationConstruction_enumeration_exists
import Theorems.Thm_OAI_TuringRigidity_LocalUnary_localized_copy
import Theorems.Thm_OAI_TuringRigidity_PersistentRestrictionCode_restriction

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticHierarchy
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle

theorem Form.switch {Y n s P} (h : Form Y n (!s) P) : Form Y (n+1) s P := by
  refine ⟨fun v => P (Nat.unpair v).1, h.comp (Primrec.fst.comp Primrec.unpair), ?_⟩
  intro x
  cases s <;> simp [Quant]

theorem Form.all {Y n P} (h : Form Y (n+1) false P) :
    Form Y (n+1) false (fun x => ∀ a, P (Nat.pair x a)) := by
  have hh := h.neg.ex.neg
  simpa only [Bool.not_true, Bool.not_false, not_exists, not_not] using hh

end TuringRigidity.ArithmeticHierarchy

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexMatrix
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexMatrix
open Encodable UniformOracle CommonIdeal TableIndices

theorem valid_normal_form (Y : Oracle) (e : ℕ) :
    Valid Y (machine e) ↔ ∀ q, ∃ r, validMatrix Y e q r := by
  constructor
  · rintro ⟨ht, hc⟩ q
    obtain ⟨z, b, hb⟩ := ht (Nat.unpair q).1
    refine ⟨Nat.pair z (if b then 1 else 0), ?_, ?_⟩
    · cases b <;> simpa [Nat.unpair_pair] using hb
    · dsimp only
      cases ha : run Y (machine e) (Nat.unpair q).1 (Nat.unpair (Nat.unpair q).2).1 with
      | none => exact Or.inl rfl
      | some a =>
        cases hb : run Y (machine e) (Nat.unpair q).1 (Nat.unpair (Nat.unpair q).2).2 with
        | none => exact Or.inr (Or.inl rfl)
        | some b => exact Or.inr (Or.inr (congrArg some
            (hc _ _ _ _ _ (Option.mem_def.mpr ha) (Option.mem_def.mpr hb))))
  · intro h
    constructor
    · intro n
      obtain ⟨r, hr, _⟩ := h (Nat.pair n (Nat.pair 0 0))
      exact ⟨(Nat.unpair r).1, (Nat.unpair r).2.bodd, by simpa using hr⟩
    · intro n z w a b ha hb
      obtain ⟨r, _, hc⟩ := h (Nat.pair n (Nat.pair z w))
      simp only [Nat.unpair_pair] at hc
      rcases hc with hc | hc | hc
      · rw [hc] at ha; simp at ha
      · rw [hc] at hb; simp at hb
      · rw [Option.mem_def.mp ha, Option.mem_def.mp hb] at hc
        exact Option.some.inj hc

theorem checkMatrix_primrec : Primrec checkMatrix := by
  let first := Primrec.fst.comp Primrec.unpair
  let rest := Primrec.snd.comp Primrec.unpair
  let dec : Primrec (fun v : ℕ => (decode (α := Option ℕ) v).getD none) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const none)
  let s := dec.comp (first.comp rest)
  let a := dec.comp (first.comp (rest.comp rest))
  let b := dec.comp (rest.comp (rest.comp rest))
  let want := Primrec.option_some.comp (bit_primrec.comp (Primrec.nat_bodd.comp first))
  exact Primrec.ite ((Primrec.eq.comp s want).and
    (((Primrec.eq.comp a (Primrec.const none)).or (Primrec.eq.comp b (Primrec.const none))).or
      (Primrec.eq.comp a b))) (Primrec.const 1) (Primrec.const 0) |>.of_eq (fun v => by
        simp only [checkMatrix, or_assoc])

theorem validMatrix_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some
      (if validMatrix Y (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1
        (Nat.unpair (Nat.unpair v).2).2 then 1 else 0)) := by
  classical
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  let e := fst
  let q := fst.comp snd
  let r := snd.comp snd
  let n := fst.comp q
  have mk : ∀ (f : ℕ → ℕ), Primrec f → Nat.RecursiveIn O
      (fun v => Part.some (encode (run Y (machine (Nat.unpair v).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).2).1).1 (f v)))) := by
    intro f hf
    have hin := _root_.OAI.TuringRigidity.UniformOracle.total_pair (O := O) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec e) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec n) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hf))
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (run_uniform_recursive Y) hin).of_eq (fun v => by simp)
  have hs := mk _ (fst.comp r)
  have ha := mk _ (fst.comp (snd.comp q))
  have hb := mk _ (snd.comp (snd.comp q))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec checkMatrix_primrec)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (snd.comp r)) (_root_.OAI.TuringRigidity.UniformOracle.total_pair hs (_root_.OAI.TuringRigidity.UniformOracle.total_pair ha hb)))).of_eq (fun v => by
      simp [checkMatrix, validMatrix])

end TuringRigidity.IndexMatrix

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexedOrder
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexedOrder
open Encodable CommonIdeal UniformOracle TableIndices IndexMatrix

theorem reads_values {Y A : Oracle} {e : Nat.Partrec.Code}
    (he : Represents Y e A) (L : List (ℕ × ℕ)) (hL : Reads Y e L) :
    values L = oraclePrefix (fun k => bit (A k)) L.length := by
  apply List.ext_getElem
  · simp [values, oraclePrefix]
  · intro j hj hj'
    have hjL : j < L.length := by simpa [values] using hj
    have hh := he.1 j (L[j].2) (L[j].1) (Option.mem_def.mpr (hL ⟨j, by simpa [values] using hj⟩))
    simpa [values, oraclePrefix] using hh

theorem exists_reads {Y A : Oracle} {e : Nat.Partrec.Code}
    (he : Represents Y e A) (m : ℕ) :
    ∃ L : List (ℕ × ℕ), L.length = m ∧ Reads Y e L := by
  have hh : ∀ j, ∃ z, TableIndices.run Y e j z = some (bit (A j)) := by
    intro j
    obtain ⟨z, a, ha⟩ := he.2 j
    exact ⟨z, by rw [← he.1 j z a ha]; exact Option.mem_def.mp ha⟩
  choose z hz using hh
  let L := (List.range m).map (fun j => (bit (A j), z j))
  refine ⟨L, by simp [L], ?_⟩
  intro j
  simpa [L] using hz j.val

theorem certificate_iff_run {Y A : Oracle} {e : Nat.Partrec.Code}
    (he : Represents Y e A) (d : Nat.Partrec.Code) (n a : ℕ) :
    (∃ z, Certificate Y e d n a z) ↔ ∃ z, TableIndices.run A d n z = some a := by
  constructor
  · rintro ⟨z, hL, hd⟩
    let L := (decode (α := List (ℕ × ℕ)) (Nat.unpair z).1).getD []
    refine ⟨Nat.pair L.length (Nat.unpair z).2, ?_⟩
    have hv := reads_values he L hL
    change d.evaln (Nat.unpair z).2 (Nat.pair (encode (values L)) n) = some a at hd
    simpa only [TableIndices.run, trial, Nat.unpair_pair, ← hv] using hd
  · rintro ⟨z, hz⟩
    obtain ⟨L, hlen, hL⟩ := exists_reads he (Nat.unpair z).1
    refine ⟨Nat.pair (encode L) (Nat.unpair z).2, ?_⟩
    simp only [Certificate, Nat.unpair_pair, encodek, Option.getD_some]
    refine ⟨hL, ?_⟩
    rw [reads_values he L hL, hlen]
    exact hz

theorem order_iff_witness {Y A₀ A₁ : Oracle} {e₀ e₁ : Nat.Partrec.Code}
    (h₀ : Represents Y e₀ A₀) (h₁ : Represents Y e₁ A₁) :
    Reduces A₀ A₁ ↔ ∃ d : Nat.Partrec.Code, OrderWitness Y e₀ e₁ d := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := reduces_represents h
    refine ⟨d, ?_, ?_⟩
    · intro n a b z w hz hw
      obtain ⟨u, hu⟩ := (certificate_iff_run h₁ d n a).mp ⟨z, hz⟩
      obtain ⟨v, hv⟩ := (certificate_iff_run h₁ d n b).mp ⟨w, hw⟩
      exact (hd.1 n u a (Option.mem_def.mpr hu)).trans
        (hd.1 n v b (Option.mem_def.mpr hv)).symm
    · intro n
      obtain ⟨u, a, hu⟩ := hd.2 n
      obtain ⟨z, hz⟩ := (certificate_iff_run h₁ d n a).mpr ⟨u, Option.mem_def.mp hu⟩
      obtain ⟨w, b, hw⟩ := h₀.2 n
      have hab : b = a := (h₀.1 n w b hw).trans (hd.1 n u a hu).symm
      exact ⟨a, z, w, hz, by rw [← hab]; exact Option.mem_def.mp hw⟩
  · rintro ⟨d, hc, ht⟩
    apply represents_reduces (d := d)
    constructor
    · intro n u a hu
      obtain ⟨z, hz⟩ := (certificate_iff_run h₁ d n a).mpr ⟨u, Option.mem_def.mp hu⟩
      obtain ⟨b, w, v, hw, hv⟩ := ht n
      exact (hc n a b z w hz hw).trans (h₀.1 n v b (Option.mem_def.mpr hv))
    · intro n
      obtain ⟨a, z, w, hz, _⟩ := ht n
      obtain ⟨u, hu⟩ := (certificate_iff_run h₁ d n a).mp ⟨z, hz⟩
      exact ⟨u, a, Option.mem_def.mpr hu⟩

end TuringRigidity.IndexedOrder

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_CertificateMatrix
attribute [-instance] _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CertificateMatrix
open Encodable UniformOracle TableIndices IndexMatrix IndexedOrder BoundedRecursive

theorem table_primrec : Primrec table := Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem entry_primrec : Primrec₂ entry :=
  (Primrec.list_getD (0, 0)).comp (table_primrec.comp Primrec.fst) Primrec.snd

theorem entryCheck_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some (entryCheck Y v)) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  let e := fst.comp fst
  let c := snd.comp fst
  let j := snd
  let en := entry_primrec.comp c j
  have hv := _root_.OAI.TuringRigidity.UniformOracle.total_comp (run_uniform_recursive Y)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec e) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec j)
      (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.snd.comp en))))
  have hw := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.encode.comp (Primrec.option_some.comp (Primrec.fst.comp en)))
  have heq := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)
    (Primrec.ite (Primrec.eq.comp fst snd) (Primrec.const 1) (Primrec.const 0))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp heq (_root_.OAI.TuringRigidity.UniformOracle.total_pair hv hw)).of_eq (fun v => by simp only [entryCheck, Nat.unpair_pair, Encodable.encode_injective.eq_iff])

theorem readsCheck_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some (readsCheck Y v)) := by
  have ha := _root_.OAI.TuringRigidity.UniformOracle.total_pair (O := {oracleFunction Y}) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id)
    (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.list_length.comp (table_primrec.comp (Primrec.snd.comp Primrec.unpair))))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (allBelow_recursive (entryCheck_recursive Y)) ha).of_eq (fun v => by simp [readsCheck])

theorem readsCheck_spec (Y : Oracle) (e c : ℕ) :
    readsCheck Y (Nat.pair e c) = 1 ↔ Reads Y (machine e) (table c) := by
  rw [readsCheck, Nat.unpair_pair, allBelow_spec]
  simp only [entryCheck, Nat.unpair_pair, ite_eq_left_iff, Nat.zero_ne_one, imp_false, not_not]
  constructor
  · intro h j
    have hh := h j.val j.isLt
    simpa [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt] using hh
  · intro h j hj
    have hh := h ⟨j, hj⟩
    simpa [entry, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using hh

theorem certificate_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some
      (if Certificate Y (machine (Nat.unpair v).1) (machine (Nat.unpair (Nat.unpair v).2).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).2 then 1 else 0)) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let fst := Primrec.fst.comp Primrec.unpair
  let snd := Primrec.snd.comp Primrec.unpair
  let e := fst
  let d := fst.comp snd
  let n := fst.comp (snd.comp snd)
  let a := fst.comp (snd.comp (snd.comp snd))
  let z := snd.comp (snd.comp (snd.comp snd))
  let L := table_primrec.comp (fst.comp z)
  let vs := Primrec.list_map L (Primrec.fst.comp Primrec.snd).to₂
  have hread := _root_.OAI.TuringRigidity.UniformOracle.total_comp (readsCheck_recursive Y)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec e) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (fst.comp z)))
  let ve := Nat.Partrec.Code.primrec_evaln.comp
    (((snd.comp z).pair (machine_primrec.comp d)).pair
      (Primrec₂.natPair.comp (Primrec.encode.comp vs) n))
  have heval := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)
    (Primrec.ite (Primrec.eq.comp ve (Primrec.option_some.comp a)) (Primrec.const 1) (Primrec.const 0))
  have hand := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)
    (Primrec.ite ((Primrec.eq.comp fst (Primrec.const 1)).and (Primrec.eq.comp snd (Primrec.const 1)))
      (Primrec.const 1) (Primrec.const 0))
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp hand (_root_.OAI.TuringRigidity.UniformOracle.total_pair hread heval)).of_eq (fun v => by
    simp only [Nat.unpair_pair, readsCheck_spec, Certificate, values, table]
    split_ifs <;> simp_all)

end TuringRigidity.CertificateMatrix

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_OrderNormalForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrderNormalForm
open Encodable TableIndices IndexMatrix IndexedOrder CertificateMatrix

theorem witness_normal_form (Y : Oracle) (e₀ e₁ d : ℕ) :
    OrderWitness Y (machine e₀) (machine e₁) (machine d) ↔
      ∀ q, ∃ r, orderMatrix Y e₀ e₁ d q r := by
  constructor
  · rintro ⟨hc, ht⟩ q
    obtain ⟨a, z, w, hz, hw⟩ := ht (Nat.unpair q).1
    exact ⟨Nat.pair a (Nat.pair z w), ⟨by simpa using hz, by simpa using hw⟩,
      hc _ _ _ _ _⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro n a b z w hz hw
      obtain ⟨r, _, hc⟩ := h (Nat.pair 0 (Nat.pair n (Nat.pair a (Nat.pair b (Nat.pair z w)))))
      simp only [Nat.unpair_pair] at hc
      exact hc hz hw
    · intro n
      obtain ⟨r, ⟨hc, ht⟩, _⟩ := h (Nat.pair n 0)
      exact ⟨(Nat.unpair r).1, (Nat.unpair (Nat.unpair r).2).1,
        (Nat.unpair (Nat.unpair r).2).2, by simpa using hc, by simpa using ht⟩

theorem order_normal_form {Y A₀ A₁ : Oracle} {e₀ e₁ : ℕ}
    (h₀ : Represents Y (machine e₀) A₀) (h₁ : Represents Y (machine e₁) A₁) :
    Reduces A₀ A₁ ↔ ∃ d : ℕ, ∀ q : ℕ, ∃ r : ℕ, orderMatrix Y e₀ e₁ d q r := by
  rw [order_iff_witness h₀ h₁]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨encode d, (witness_normal_form Y e₀ e₁ (encode d)).mp ?_⟩
    simpa using hd
  · rintro ⟨d, hd⟩
    exact ⟨machine d, (witness_normal_form Y e₀ e₁ d).mpr hd⟩

end TuringRigidity.OrderNormalForm

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_OrderMatrixRecursive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrderNormalForm
open UniformOracle TableIndices IndexMatrix IndexedOrder CertificateMatrix

private theorem combine_primrec : Primrec combine := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  let t := f
  let h := f.comp s
  let c₀ := f.comp (s.comp s)
  let c₁ := f.comp (s.comp (s.comp s))
  let a := f.comp (s.comp (s.comp (s.comp s)))
  let b := s.comp (s.comp (s.comp (s.comp s)))
  have hp := (Primrec.eq.comp c₀ (Primrec.const 1)).not.or
    ((Primrec.eq.comp c₁ (Primrec.const 1)).not.or (Primrec.eq.comp a b))
  exact Primrec.ite ((Primrec.eq.comp t (Primrec.const 1)).and
    ((Primrec.eq.comp h (Primrec.const 1)).and hp)) (Primrec.const 1) (Primrec.const 0)

theorem orderMatrix_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction Y} (fun v => Part.some
      (if orderMatrix Y (Nat.unpair v).1 (Nat.unpair (Nat.unpair v).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).2).2 then 1 else 0)) := by
  let O : Set (ℕ →. ℕ) := {oracleFunction Y}
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  let e₀ := f
  let e₁ := f.comp s
  let d := f.comp (s.comp s)
  let q := f.comp (s.comp (s.comp s))
  let r := s.comp (s.comp (s.comp s))
  let n := f.comp q
  let challenge := s.comp q
  let m := f.comp challenge
  let a := f.comp (s.comp challenge)
  let b := f.comp (s.comp (s.comp challenge))
  let z := f.comp (s.comp (s.comp (s.comp challenge)))
  let w := s.comp (s.comp (s.comp (s.comp challenge)))
  let answer := f.comp r
  let cert := f.comp (s.comp r)
  let trial := s.comp (s.comp r)
  have mk : ∀ (fn fa fz : ℕ → ℕ), Primrec fn → Primrec fa → Primrec fz →
      Nat.RecursiveIn O (fun v => Part.some
        (if Certificate Y (machine (Nat.unpair (Nat.unpair v).2).1)
          (machine (Nat.unpair (Nat.unpair (Nat.unpair v).2).2).1)
          (fn v) (fa v) (fz v) then 1 else 0)) := by
    intro fn fa fz hn ha hz
    exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (certificate_recursive Y)
      (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec e₁) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec d)
        (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hn) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec ha) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec hz)))))).of_eq
      (fun v => by simp)
  have ht := mk _ _ _ n answer cert
  have hc₀ := mk _ _ _ m a z
  have hc₁ := mk _ _ _ m b w
  have hr := _root_.OAI.TuringRigidity.UniformOracle.total_comp (run_uniform_recursive Y)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec e₀) (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec n) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec trial)))
  have hans := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O) (Primrec.encode.comp (Primrec.option_some.comp answer))
  have heq := _root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := O)
    (Primrec.ite (Primrec.eq.comp f s) (Primrec.const 1) (Primrec.const 0))
  have hout := _root_.OAI.TuringRigidity.UniformOracle.total_comp heq (_root_.OAI.TuringRigidity.UniformOracle.total_pair hr hans)
  exact (_root_.OAI.TuringRigidity.UniformOracle.total_comp (_root_.OAI.TuringRigidity.UniformOracle.total_primrec combine_primrec)
    (_root_.OAI.TuringRigidity.UniformOracle.total_pair ht (_root_.OAI.TuringRigidity.UniformOracle.total_pair hout (_root_.OAI.TuringRigidity.UniformOracle.total_pair hc₀ (_root_.OAI.TuringRigidity.UniformOracle.total_pair hc₁
      (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec a) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec b))))))).of_eq (fun v => by
        simp only [combine, orderMatrix, Nat.unpair_pair, Encodable.encode_injective.eq_iff]
        simp [and_assoc, imp_iff_not_or])

end TuringRigidity.OrderNormalForm

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexJoin
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexJoin
open Encodable Computable UniformOracle CommonIdeal TableIndices

theorem dispatcher_spec (e f : Nat.Partrec.Code) (x : ℕ) :
    dispatcher.eval (Nat.pair (encode (e, f)) x) = dispatch ((e, f), x) :=
  Classical.choose_spec (partrec_code dispatch_partrec) ((e, f), x)

theorem joined_primrec : Primrec₂ joined :=
  Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const dispatcher) Primrec.encode

theorem joined_eval (e f : Nat.Partrec.Code) (L : List ℕ) (n : ℕ) :
    (joined e f).eval (Nat.pair (encode L) n) =
      if n.bodd then f.eval (Nat.pair (encode L) (n/2)) else e.eval (Nat.pair (encode L) (n/2)) := by
  rw [joined, Nat.Partrec.Code.eval_curry, dispatcher_spec]
  simp only [dispatch, Nat.unpair_pair]
  split <;> rfl

theorem joined_represents {Y A B : Oracle} {e f : Nat.Partrec.Code}
    (he : Represents Y e A) (hf : Represents Y f B) :
    Represents Y (joined e f) (join A B) := by
  have hs : ∀ n m a, a ∈ (joined e f).eval
      (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n) → a = bit (join A B n) := by
    intro n m a ha
    rw [joined_eval] at ha
    cases hb : n.bodd with
    | false =>
      simp only [hb, Bool.false_eq_true, ↓reduceIte] at ha
      obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp ha
      have hh := he.1 (n/2) (Nat.pair m t) a (by simpa [TableIndices.run, trial] using ht)
      simpa [join, hb] using hh
    | true =>
      simp only [hb, ↓reduceIte] at ha
      obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp ha
      have hh := hf.1 (n/2) (Nat.pair m t) a (by simpa [TableIndices.run, trial] using ht)
      simpa [join, hb] using hh
  have ht : ∀ n, ∃ m a, a ∈ (joined e f).eval
      (Nat.pair (encode (oraclePrefix (fun k => bit (Y k)) m)) n) := by
    intro n
    cases hb : n.bodd with
    | false =>
      obtain ⟨z, a, ha⟩ := he.2 (n/2)
      exact ⟨(Nat.unpair z).1, a, by
        rw [joined_eval, hb]
        exact Nat.Partrec.Code.evaln_sound ha⟩
    | true =>
      obtain ⟨z, a, ha⟩ := hf.2 (n/2)
      exact ⟨(Nat.unpair z).1, a, by
        rw [joined_eval, hb]
        exact Nat.Partrec.Code.evaln_sound ha⟩
  refine ⟨?_, ?_⟩
  · intro n z a ha
    exact hs n (Nat.unpair z).1 a (Nat.Partrec.Code.evaln_sound ha)
  · intro n
    obtain ⟨m, a, ha⟩ := ht n
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp ha
    exact ⟨Nat.pair m t, a, by simpa [TableIndices.run, trial] using ht⟩

end TuringRigidity.IndexJoin

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexPresentation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexPresentation
open Encodable TableIndices IndexMatrix OrderNormalForm

theorem joinIndex_primrec : Primrec₂ joinIndex :=
  Primrec.encode.comp (IndexJoin.joined_primrec.comp (machine_primrec.comp Primrec.fst)
    (machine_primrec.comp Primrec.snd))

theorem value_below (Y : Oracle) (e : ℕ) : value Y e ≤ degree Y := by
  classical
  by_cases h : Dom Y e
  · simp only [value, dite_eq_left h]
    exact represents_reduces (output_represents _ _)
  · simp [value, h]

theorem le_iff {Y : Oracle} {e f : ℕ} (he : Dom Y e) (hf : Dom Y f) :
    LE Y e f ↔ value Y e ≤ value Y f := by
  rw [value_eq (output_represents Y ⟨machine e, he⟩),
    value_eq (output_represents Y ⟨machine f, hf⟩)]
  exact (order_normal_form (output_represents Y ⟨machine e, he⟩) (output_represents Y ⟨machine f, hf⟩)).symm

theorem join_dom {Y : Oracle} {e f : ℕ} (he : Dom Y e) (hf : Dom Y f) :
    Dom Y (joinIndex e f) := by
  apply (valid_iff_represents _ _).mpr
  refine ⟨join (output Y ⟨machine e, he⟩) (output Y ⟨machine f, hf⟩), ?_⟩
  simpa only [joinIndex, machine_encode] using
    IndexJoin.joined_represents (output_represents Y ⟨machine e, he⟩)
      (output_represents Y ⟨machine f, hf⟩)

theorem join_value {Y : Oracle} {e f : ℕ} (he : Dom Y e) (hf : Dom Y f) :
    value Y (joinIndex e f) = value Y e ⊔ value Y f := by
  have hr : Represents Y (machine (joinIndex e f))
      (join (output Y ⟨machine e, he⟩) (output Y ⟨machine f, hf⟩)) := by
    simpa only [joinIndex, machine_encode] using
      IndexJoin.joined_represents (output_represents Y ⟨machine e, he⟩)
        (output_represents Y ⟨machine f, hf⟩)
  rw [value_eq hr, value_eq (output_represents Y ⟨machine e, he⟩),
    value_eq (output_represents Y ⟨machine f, hf⟩)]
  rfl

end TuringRigidity.IndexPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticAtoms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle IndexMatrix OrderNormalForm IndexPresentation

theorem forall_form {Y n P} (h : Sigma Y n P) :
    Pi Y (n+1) (fun x => ∀ a, P (Nat.pair x a)) := ⟨P, h, fun _ => Iff.rfl⟩

theorem dom_pi (Y : Oracle) {e : ℕ → ℕ} (he : Primrec e) :
    Pi Y 2 (fun x => Dom Y (e x)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hm := _root_.OAI.TuringRigidity.UniformOracle.total_comp (validMatrix_recursive Y) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec₂.natPair.comp (he.comp (f.comp f)) (Primrec₂.natPair.comp (s.comp f) s)))
  have h : RecursivePred Y (fun v => validMatrix Y (e (Nat.unpair (Nat.unpair v).1).1)
      (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2) := by
    exact hm.of_eq (fun v => by simp only [Nat.unpair_pair]; congr 1; split <;> rfl)
  exact (forall_form (exists_form (Y := Y) (n := 0) h)).congr
    (fun x => by simp only [Nat.unpair_pair]; exact (valid_normal_form Y (e x)).symm)

theorem le_sigma (Y : Oracle) {e f : ℕ → ℕ} (he : Primrec e) (hf : Primrec f) :
    Sigma Y 3 (fun x => LE Y (e x) (f x)) := by
  classical
  let a := Primrec.fst.comp Primrec.unpair
  let b := Primrec.snd.comp Primrec.unpair
  let x := a.comp (a.comp a)
  let d := b.comp (a.comp a)
  let q := b.comp a
  let r := b
  have hm := _root_.OAI.TuringRigidity.UniformOracle.total_comp (orderMatrix_recursive Y) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec
    (Primrec₂.natPair.comp (he.comp x) (Primrec₂.natPair.comp (hf.comp x)
      (Primrec₂.natPair.comp d (Primrec₂.natPair.comp q r)))))
  have h : RecursivePred Y (fun v => orderMatrix Y
      (e (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).1)
      (f (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).1)
      (Nat.unpair (Nat.unpair (Nat.unpair v).1).1).2
      (Nat.unpair (Nat.unpair v).1).2 (Nat.unpair v).2) := by
    exact hm.of_eq (fun v => by simp only [Nat.unpair_pair]; congr 1; split <;> rfl)
  exact (exists_form (forall_form (exists_form (Y := Y) (n := 0) h))).congr
    (fun x => by simp only [Nat.unpair_pair]; rfl)

end TuringRigidity.ArithmeticHierarchy

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticFinite
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticHierarchy
open UniformOracle

theorem form_true (Y : Oracle) (n : ℕ) (s : Bool) : Form Y n s (fun _ => True) := by
  induction n with
  | zero =>
    classical
    simpa only [Form, RecursivePred, ↓reduceIte] using
      (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (O := {oracleFunction Y}) (Primrec.const 1))
  | succ n ih => exact ih.raise

theorem Form.finite_all {Y n s k} {P : Fin k → ℕ → Prop}
    (h : ∀ i, Form Y n s (P i)) : Form Y n s (fun x => ∀ i, P i x) := by
  induction k with
  | zero => exact (form_true Y n s).congr (fun x => by simp)
  | succ k ih =>
    exact ((h 0).and (ih (fun i => h i.succ))).congr (fun x => by
      simp only [Fin.forall_fin_succ])

end TuringRigidity.ArithmeticHierarchy

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CountableBound
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CountableBound
open UniformOracle

theorem reduces_sum (A : ℕ → Oracle) (k : ℕ) : Reduces (A k) (sum A) := by
  apply RecursiveIn.iff_nat.mpr
  have hO : Nat.RecursiveIn {oracleFunction (sum A)} (oracleFunction (sum A)) :=
    .oracle _ (Set.mem_singleton _)
  have h := _root_.OAI.TuringRigidity.UniformOracle.total_comp hO (_root_.OAI.TuringRigidity.UniformOracle.total_pair (_root_.OAI.TuringRigidity.UniformOracle.total_primrec (Primrec.const k)) (_root_.OAI.TuringRigidity.UniformOracle.total_primrec Primrec.id))
  exact h.of_eq (fun n => by simp [oracleFunction, sum])

theorem countable_bounded (S : Set Degree) (hS : S.Countable) :
    ∃ b : Degree, ∀ x ∈ S, x ≤ b := by
  by_cases hne : S.Nonempty
  · obtain ⟨f, hf⟩ := hS.exists_eq_range hne
    choose A hA using (fun n => degree_surjective (f n))
    refine ⟨degree (sum A), ?_⟩
    intro x hx
    rw [hf] at hx
    obtain ⟨n, rfl⟩ := hx
    rw [← hA n]
    exact reduces_sum A n
  · exact ⟨⊥, fun x hx => False.elim (hne ⟨x, hx⟩)⟩

end TuringRigidity.CountableBound

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedDecoding
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedDecoding
open AntichainParameters SetCoding RelationCoding

theorem local_nontrivial_iff (y b g₀ g₁ x : Degree) (hb : b ≤ y) (hg₀ : g₀ ≤ y) :
    LocalNontrivial y b g₀ g₁ x ↔ NontrivialCommonLower b g₀ g₁ x := by
  constructor
  · rintro ⟨hx, z, _, hz₀, hz₁, hn⟩
    exact ⟨hx, z, hz₀, hz₁, hn⟩
  · rintro ⟨hx, z, hz₀, hz₁, hn⟩
    exact ⟨hx, z, hz₀.trans (sup_le hg₀ (hx.trans hb)), hz₀, hz₁, hn⟩

theorem local_antichain_iff (y : Degree) (p : AntichainCode) (hp : AntichainBelow p y)
    (x : Degree) : LocalAntichain y p x ↔ p.Holds x := by
  unfold LocalAntichain AntichainCode.Holds CodedAntichain
  simp only [local_nontrivial_iff y p.bound p.left p.right _ hp.1 hp.2.1]
  constructor
  · rintro ⟨hx, hmin⟩
    exact ⟨hx, fun w hw hle => hmin w (hw.1.trans hp.1) hw hle⟩
  · rintro ⟨hx, hmin⟩
    exact ⟨hx, fun w _ hw hle => hmin w hw hle⟩

theorem graph_bounded {y : Degree} {p : SetCode} (hp : SetBelow p y)
    {x c : Degree} (h : p.Graph x c) : x ≤ y ∧ c ≤ y :=
  ⟨h.1.trans hp.1, h.2.1.1.1.trans hp.2.1.1⟩

end TuringRigidity.BoundedDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_AntichainDecoding
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AntichainDecoding
open IndexPresentation ArithmeticHierarchy SetCoding BoundedDecoding

theorem nontrivial_sigma (Y : Oracle) {b l r x : ℕ → ℕ}
    (hb : Primrec b) (hl : Primrec l) (hr : Primrec r) (hx : Primrec x) :
    Sigma Y 4 (fun v => Nontrivial Y (b v) (l v) (r v) (x v)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hdom : Sigma Y 4 (fun v => Dom Y (Nat.unpair v).2) := (dom_pi Y s).switch.raise
  have h₀ := (le_sigma Y s (joinIndex_primrec.comp (hl.comp f) (hx.comp f))).raise
  have h₁ := (le_sigma Y s (joinIndex_primrec.comp (hr.comp f) (hx.comp f))).raise
  have hn : Sigma Y 4 (fun v => ¬ LE Y (Nat.unpair v).2 (x (Nat.unpair v).1)) :=
    (le_sigma Y s (hx.comp f)).neg.switch
  have hw := (hdom.and (h₀.and (h₁.and hn))).ex
  exact ((le_sigma Y hx hb).raise.and hw).congr (fun v => by
    simp only [Nat.unpair_pair]; rfl)

theorem minimal_pi (Y : Oracle) {b l r x : ℕ → ℕ}
    (hb : Primrec b) (hl : Primrec l) (hr : Primrec r) (hx : Primrec x) :
    Pi Y 4 (fun v => Minimal Y (b v) (l v) (r v) (x v)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hd : Pi Y 4 (fun v => ¬ Dom Y (Nat.unpair v).2) := (dom_pi Y s).neg.switch.raise
  have hn := (nontrivial_sigma Y (hb.comp f) (hl.comp f) (hr.comp f) s).neg
  have hw : Pi Y 4 (fun v => ¬ LE Y (Nat.unpair v).2 (x (Nat.unpair v).1)) :=
    (le_sigma Y s (hx.comp f)).neg.raise
  have hxw : Pi Y 4 (fun v => LE Y (x (Nat.unpair v).1) (Nat.unpair v).2) :=
    (le_sigma Y (hx.comp f) s).switch
  exact ((hd.or (hn.or (hw.or hxw))).all).congr (fun v => by
    simp only [Nat.unpair_pair, Minimal, imp_iff_not_or])

theorem antichain_sigma (Y : Oracle) {b l r x : ℕ → ℕ}
    (hb : Primrec b) (hl : Primrec l) (hr : Primrec r) (hx : Primrec x) :
    Sigma Y 5 (fun v => Antichain Y (b v) (l v) (r v) (x v)) :=
  (nontrivial_sigma Y hb hl hr hx).raise.and (minimal_pi Y hb hl hr hx).switch

theorem nontrivial_iff {Y : Oracle} {b l r x : ℕ}
    (hb : Dom Y b) (hl : Dom Y l) (hr : Dom Y r) (hx : Dom Y x) :
    Nontrivial Y b l r x ↔ LocalNontrivial (degree Y)
      (value Y b) (value Y l) (value Y r) (value Y x) := by
  unfold Nontrivial LocalNontrivial
  rw [le_iff hx hb]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨z, hz, h₀, h₁, hn⟩
    refine ⟨value Y z, value_below Y z, ?_, ?_, ?_⟩
    · simpa only [join_value hl hx] using (le_iff hz (join_dom hl hx)).mp h₀
    · simpa only [join_value hr hx] using (le_iff hz (join_dom hr hx)).mp h₁
    · exact fun he => hn ((le_iff hz hx).mpr he)
  · rintro ⟨z, hz, h₀, h₁, hn⟩
    obtain ⟨w, hw, rfl⟩ := value_surjective Y z hz
    exact ⟨w, hw, (le_iff hw (join_dom hl hx)).mpr (by simpa only [join_value hl hx] using h₀),
      (le_iff hw (join_dom hr hx)).mpr (by simpa only [join_value hr hx] using h₁),
      fun he => hn ((le_iff hw hx).mp he)⟩

theorem antichain_iff {Y : Oracle} {b l r x : ℕ}
    (hb : Dom Y b) (hl : Dom Y l) (hr : Dom Y r) (hx : Dom Y x) :
    Antichain Y b l r x ↔ (AntichainCode.mk (value Y b) (value Y l) (value Y r)).Holds
      (value Y x) := by
  rw [← local_antichain_iff (degree Y) _ ⟨value_below Y b, value_below Y l, value_below Y r⟩]
  unfold Antichain LocalAntichain
  rw [nontrivial_iff hb hl hr hx]
  apply and_congr_right
  intro _
  constructor
  · intro hm w hw hn hle
    obtain ⟨i, hi, rfl⟩ := value_surjective Y w hw
    exact (le_iff hx hi).mp (hm i hi ((nontrivial_iff hb hl hr hi).mpr hn)
      ((le_iff hi hx).mpr hle))
  · intro hm w hw hn hle
    exact (le_iff hx hw).mpr (hm (value Y w) (value_below Y w)
      ((nontrivial_iff hb hl hr hw).mp hn) ((le_iff hw hx).mp hle))

end TuringRigidity.AntichainDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_IndexTuples
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IndexTuples
open Encodable IndexPresentation IndexMatrix TableIndices

theorem entry_primrec (i : ℕ) : Primrec (entry i) := by
  induction i with
  | zero => exact Primrec.fst.comp Primrec.unpair
  | succ i ih => exact ih.comp (Primrec.snd.comp Primrec.unpair)

theorem tuple_surjective {n : ℕ} (v : Fin n → ℕ) : ∃ t, ∀ i, entry i.val t = v i := by
  induction n with
  | zero => exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (fun i => v i.succ)
    refine ⟨Nat.pair (v 0) t, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [entry]
    · simpa only [Fin.val_succ, entry, Nat.unpair_pair] using ht j

theorem zero_represents (Y : Oracle) : Represents Y (machine zeroIndex) (fun _ => false) := by
  simp only [zeroIndex, machine_encode]
  constructor
  · intro n z a ha
    have h := Nat.Partrec.Code.evaln_sound ha
    change a ∈ Part.some 0 at h
    exact Part.mem_some_iff.mp h
  · intro n
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp
      (show 0 ∈ Nat.Partrec.Code.zero.eval (Nat.pair (encode ([] : List ℕ)) n) from Part.mem_some 0)
    refine ⟨Nat.pair 0 t, 0, ?_⟩
    simpa [TableIndices.run, UniformOracle.trial, UniformOracle.oraclePrefix] using ht

theorem zero_dom (Y : Oracle) : Dom Y zeroIndex :=
  (valid_iff_represents _ _).mpr ⟨_, zero_represents Y⟩

theorem zero_value (Y : Oracle) : value Y zeroIndex = ⊥ := value_eq (zero_represents Y)

theorem supIndex_primrec (n : ℕ) : Primrec (supIndex n) := by
  induction n with
  | zero => exact Primrec.const _
  | succ n ih =>
    exact joinIndex_primrec.comp (Primrec.fst.comp Primrec.unpair)
      (ih.comp (Primrec.snd.comp Primrec.unpair))

theorem sup_dom {Y : Oracle} {n t : ℕ} (h : ∀ i : Fin n, Dom Y (entry i.val t)) :
    Dom Y (supIndex n t) := by
  induction n generalizing t with
  | zero => exact zero_dom Y
  | succ n ih => exact join_dom (h 0) (ih (fun i => h i.succ))

theorem sup_value {Y : Oracle} {n t : ℕ} (h : ∀ i : Fin n, Dom Y (entry i.val t)) :
    value Y (supIndex n t) = Finset.univ.sup (fun i : Fin n => value Y (entry i.val t)) := by
  induction n generalizing t with
  | zero => simp [supIndex, zero_value]
  | succ n ih =>
    have h0 : Dom Y ((Nat.unpair t).1) := h 0
    rw [supIndex, join_value h0 (sup_dom (fun i : Fin n => h i.succ)),
      ih (fun i : Fin n => h i.succ)]
    apply le_antisymm
    · apply sup_le
      · exact Finset.le_sup (f := fun i : Fin (n+1) => value Y (entry i.val t)) (Finset.mem_univ 0)
      · apply Finset.sup_le
        intro i _
        exact Finset.le_sup (f := fun j : Fin (n+1) => value Y (entry j.val t))
          (Finset.mem_univ i.succ)
    · apply Finset.sup_le
      intro i _
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_sup_left
      · exact (Finset.le_sup (f := fun j : Fin n => value Y (entry j.val (Nat.unpair t).2))
          (Finset.mem_univ j)).trans le_sup_right

end TuringRigidity.IndexTuples

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RelationPresentation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationPresentation
open IndexPresentation IndexTuples ArithmeticHierarchy AntichainDecoding
open SetCoding RelationCoding BoundedDecoding

theorem ACode.holds_iff {Y p x} (hp : ACode.Good Y p) (hx : Dom Y x) :
    p.Holds Y x ↔ (p.decode Y).Holds (value Y x) :=
  antichain_iff hp.1 hp.2.1 hp.2.2 hx

theorem ACode.sigma (Y : Oracle) (p : ACode) {x : ℕ → ℕ} (hx : Primrec x) :
    Sigma Y 5 (fun v => p.Holds Y (x v)) :=
  antichain_sigma Y (Primrec.const _) (Primrec.const _) (Primrec.const _) hx

theorem ACode.exists_code (Y : Oracle) (p : AntichainCode) (hp : AntichainBelow p (degree Y)) :
    ∃ q : ACode, q.Good Y ∧ q.decode Y = p := by
  obtain ⟨b, hb, eb⟩ := value_surjective Y p.bound hp.1
  obtain ⟨l, hl, el⟩ := value_surjective Y p.left hp.2.1
  obtain ⟨r, hr, er⟩ := value_surjective Y p.right hp.2.2
  exact ⟨⟨b,l,r⟩, ⟨hb,hl,hr⟩, by cases p; simp_all [ACode.decode]⟩

theorem SCode.graph_iff {Y p x c} (hp : SCode.Good Y p) (hx : Dom Y x) (hc : Dom Y c) :
    p.Graph Y x c ↔ (p.decode Y).Graph (value Y x) (value Y c) := by
  simp only [SCode.Graph, SetCode.Graph, SCode.decode, le_iff hx hp.1,
    ACode.holds_iff hp.2.1 hc, ACode.holds_iff hp.2.2 (join_dom hx hc), join_value hx hc]

theorem SCode.sigma (Y : Oracle) (p : SCode) {x c : ℕ → ℕ}
    (hx : Primrec x) (hc : Primrec c) : Sigma Y 5 (fun v => p.Graph Y (x v) (c v)) :=
  (le_sigma Y hx (Primrec.const _)).raise.raise.and
    ((p.tags.sigma Y hc).and (p.decorated.sigma Y (joinIndex_primrec.comp hx hc)))

theorem SCode.exists_code (Y : Oracle) (p : SetCode) (hp : SetBelow p (degree Y)) :
    ∃ q : SCode, q.Good Y ∧ q.decode Y = p := by
  obtain ⟨b, hb, eb⟩ := value_surjective Y p.bound hp.1
  obtain ⟨t, ht, et⟩ := ACode.exists_code Y p.tags hp.2.1
  obtain ⟨d, hd, ed⟩ := ACode.exists_code Y p.decorated hp.2.2
  exact ⟨⟨b,t,d⟩, ⟨hb,ht,hd⟩, by cases p; simp_all [SCode.decode]⟩

theorem RCode.sigma {n} (Y : Oracle) (p : RCode n) : Sigma Y 5 (p.Holds Y) := by
  let f := Primrec.fst.comp Primrec.unpair
  let s := Primrec.snd.comp Primrec.unpair
  have hd : Sigma Y 5 (fun v => ∀ i : Fin n, Dom Y (entry i.val v)) :=
    Form.finite_all (fun i => (dom_pi Y (entry_primrec i.val)).switch.raise.raise)
  have hg : Sigma Y 5 (fun v => ∀ i : Fin n, Dom Y (entry i.val (Nat.unpair v).2) ∧
      (p.coordinates i).Graph Y (entry i.val (Nat.unpair v).1) (entry i.val (Nat.unpair v).2)) :=
    Form.finite_all (fun i => ((dom_pi Y ((entry_primrec i.val).comp s)).switch.raise.raise).and
      ((p.coordinates i).sigma Y ((entry_primrec i.val).comp f) ((entry_primrec i.val).comp s)))
  have ht := p.tuples.sigma Y ((supIndex_primrec n).comp s)
  exact (hd.and ((hg.and ht).ex)).congr (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem RCode.holds_iff {n Y} {p : RCode n} (hp : p.Good Y) (v : ℕ) :
    p.Holds Y v ↔ (∀ i : Fin n, Dom Y (entry i.val v)) ∧
      (p.decode Y).Holds (fun i => value Y (entry i.val v)) := by
  unfold RCode.Holds
  apply and_congr_right
  intro hv
  constructor
  · rintro ⟨t, ht, htuple⟩
    refine ⟨fun i => value Y (entry i.val t), fun i => ?_, ?_⟩
    · exact (SCode.graph_iff (hp.1 i) (hv i) (ht i).1).mp (ht i).2
    · have h := (ACode.holds_iff hp.2 (sup_dom (fun i => (ht i).1))).mp htuple
      simpa only [sup_value (fun i => (ht i).1), RCode.decode] using h
  · rintro ⟨c, hc, ht⟩
    have hb : ∀ i, c i ≤ degree Y := by
      intro i
      exact (hc i).2.1.1.1.trans (value_below Y (p.coordinates i).tags.bound)
    choose e he hev using (fun i => value_surjective Y (c i) (hb i))
    obtain ⟨t, het⟩ := tuple_surjective e
    have hdom : ∀ i : Fin n, Dom Y (entry i.val t) := fun i => (het i) ▸ he i
    have hval : (fun i : Fin n => value Y (entry i.val t)) = c := by
      funext i
      rw [het i, hev i]
    refine ⟨t, fun i => ⟨hdom i, ?_⟩, ?_⟩
    · apply (SCode.graph_iff (hp.1 i) (hv i) (hdom i)).mpr
      simpa only [het i, hev i, RCode.decode] using hc i
    · apply (ACode.holds_iff hp.2 (sup_dom hdom)).mpr
      rw [sup_value hdom, hval]
      exact ht

theorem RCode.exists_code {n} (Y : Oracle) (p : RelationCode n)
    (hp : RelationBelow p (degree Y)) : ∃ q : RCode n, q.Good Y ∧ q.decode Y = p := by
  choose c hc ec using (fun i => SCode.exists_code Y (p.coordinates i) (hp.1 i))
  obtain ⟨t, ht, et⟩ := ACode.exists_code Y p.tuples hp.2
  refine ⟨⟨c,t⟩, ⟨hc,ht⟩, ?_⟩
  cases p with
  | mk coords tuples =>
    simp only [RCode.decode]
    congr
    · funext i
      exact ec i

theorem sigma5_decoding {n} (Y : Oracle) (p : RelationCode n)
    (hp : RelationBelow p (degree Y)) :
    Sigma Y 5 (fun v => (∀ i : Fin n, Dom Y (entry i.val v)) ∧
      p.Holds (fun i => value Y (entry i.val v))) := by
  obtain ⟨q, hq, rfl⟩ := RCode.exists_code Y p hp
  exact (q.sigma Y).congr (RCode.holds_iff hq)

end TuringRigidity.RelationPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticModelDecoding
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticModelDecoding
open IndexPresentation IndexTuples ArithmeticHierarchy DecodingTheorem
open SetCoding RelationCoding BoundedDecoding OracleJump

theorem oneIndex_primrec : Primrec oneIndex := Primrec₂.natPair.comp Primrec.id (Primrec.const 0)
theorem twoIndex_primrec : Primrec₂ twoIndex :=
  Primrec₂.natPair.comp Primrec.fst (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0))

theorem presented_one {Y p a} (ha : Dom Y a) :
    Presented Y p (oneIndex a) ↔ p.Holds (one (value Y a)) := by
  have ht : (fun i : Fin 1 => value Y (entry i.val (oneIndex a))) = one (value Y a) := by
    funext i
    fin_cases i
    simp [entry,oneIndex,one]
  have hd : ∀ i : Fin 1, Dom Y (entry i.val (oneIndex a)) := by
    intro i
    fin_cases i
    simpa [entry,oneIndex] using ha
  simp only [Presented,hd,forall_const,true_and,ht]

theorem presented_two {Y p a b} (ha : Dom Y a) (hb : Dom Y b) :
    Presented Y p (twoIndex a b) ↔ p.Holds (two (value Y a) (value Y b)) := by
  have ht : (fun i : Fin 2 => value Y (entry i.val (twoIndex a b))) = two (value Y a) (value Y b) := by
    funext i
    fin_cases i <;> simp [entry,twoIndex,two]
  have hd : ∀ i : Fin 2, Dom Y (entry i.val (twoIndex a b)) := by
    intro i
    fin_cases i
    · simpa [entry,twoIndex] using ha
    · simpa [entry,twoIndex] using hb
  simp only [Presented,hd,forall_const,true_and,ht]

theorem defined_sigma (Y : Oracle) (S : RelationCode 2) (P : RelationCode 1) (z : ℕ)
    (hS : RelationBelow S (degree Y)) (hP : RelationBelow P (degree Y)) :
    Sigma Y 5 (Defined Y S P z) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let start := item_primrec.comp r (Primrec.const 0)
  have hd : Sigma Y 5 (fun v => Dom Y (item (Nat.unpair v).2 0)) :=
    (dom_pi Y start).switch.raise.raise
  have hl := (le_sigma Y start (Primrec.const z)).raise.raise
  have hr := (le_sigma Y (Primrec.const z) start).raise.raise
  have hs := ((RelationPresentation.sigma5_decoding Y S hS).comp
    (twoIndex_primrec.comp (item_primrec.comp (r.comp f) r)
      (item_primrec.comp (r.comp f) (Primrec.succ.comp r)))).bounded_all f
  have hp := (RelationPresentation.sigma5_decoding Y P hP).comp
    (oneIndex_primrec.comp (item_primrec.comp r f))
  exact (((hd.and (hl.and (hr.and hs))).and hp).ex).congr (fun v => by
    simp only [Nat.unpair_pair,Defined,Path,Presented])

theorem path_node {U Y} (c : Copy U) {z : ℕ} (hz : Dom Y z) (he : value Y z = c.node 0)
    {n t : ℕ} (hpath : Path Y c.successor z n t) :
    ∀ i, i ≤ n → Dom Y (item t i) ∧ value Y (item t i) = c.node i := by
  intro i hi
  induction i with
  | zero =>
    exact ⟨hpath.1, (le_antisymm ((le_iff hpath.1 hz).mp hpath.2.1)
      ((le_iff hz hpath.1).mp hpath.2.2.1)).trans he⟩
  | succ i ih =>
    have hprev := ih (by omega)
    have hs := hpath.2.2.2 i (by omega)
    have hnext : Dom Y (item t (i+1)) := by
      simpa [twoIndex,entry] using hs.1 (1 : Fin 2)
    obtain ⟨k,hk,hkn⟩ := (c.successor_spec _ _).mp ((presented_two hprev.1 hnext).mp hs)
    have hki : k = i := c.injective (hk.symm.trans hprev.2)
    exact ⟨hnext, by simpa [hki] using hkn⟩

theorem node_below {U} (Y : Oracle) (c : Copy U)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) : c.node n ≤ degree Y := by
  have hs := (c.successor_spec (c.node n) (c.node (n+1))).mpr ⟨n,rfl,rfl⟩
  obtain ⟨d,hd,_⟩ := hs
  exact (graph_bounded (hS.1 0) (hd 0)).1

theorem defined_iff {U Y} (c : Copy U) {z : ℕ} (hz : Dom Y z) (he : value Y z = c.node 0)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) :
    Defined Y c.successor c.predicate z n ↔ U n := by
  constructor
  · rintro ⟨t,hpath,hp⟩
    have hn := path_node c hz he hpath n le_rfl
    obtain ⟨k,hUk,hk⟩ := (c.predicate_spec _).mp ((presented_one hn.1).mp hp)
    have hkn := c.injective (hk.symm.trans hn.2)
    exact hkn ▸ hUk
  · intro hU
    choose e hd hev using (fun i => value_surjective Y (c.node i) (node_below Y c hS i))
    obtain ⟨t,ht⟩ := (exists_items (n+1) (fun i a => a = e i)).mp
      (fun i _ => ⟨e i,rfl⟩)
    have hdom (i : ℕ) (hi : i ≤ n) : Dom Y (item t i) := by rw [ht i (by omega)]; exact hd i
    have hval (i : ℕ) (hi : i ≤ n) : value Y (item t i) = c.node i := by
      rw [ht i (by omega), hev i]
    refine ⟨t, ⟨hdom 0 (by omega), ?_, ?_, ?_⟩, ?_⟩
    · apply (le_iff (hdom 0 (by omega)) hz).mpr
      rw [hval 0 (by omega),he]
    · apply (le_iff hz (hdom 0 (by omega))).mpr
      rw [hval 0 (by omega),he]
    · intro i hi
      apply (presented_two (hdom i (by omega)) (hdom (i+1) (by omega))).mpr
      apply (c.successor_spec _ _).mpr
      exact ⟨i,hval i (by omega),hval (i+1) (by omega)⟩
    · apply (presented_one (hdom n le_rfl)).mpr
      exact (c.predicate_spec _).mpr ⟨n,hU,hval n le_rfl⟩

theorem unary_decoding {U} (Y : Oracle) (c : Copy U)
    (hS : RelationBelow c.successor (degree Y)) (hP : RelationBelow c.predicate (degree Y)) :
    Sigma Y 5 U ∧ RecursivePred (iterate Y 5) U := by
  obtain ⟨z,hz,he⟩ := value_surjective Y (c.node 0) (node_below Y c hS 0)
  have h := (defined_sigma Y c.successor c.predicate z hS hP).congr (defined_iff c hz he hS)
  exact ⟨h,form_recursive h⟩

end TuringRigidity.ArithmeticModelDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_JumpProperties
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleJump
open Encodable UniformOracle CommonIdeal TableIndices IndexMatrix ArithmeticHierarchy

theorem iterate_mono {Y Z : Oracle} (hYZ : Reduces Y Z) (n : ℕ) :
    Reduces (iterate Y n) (iterate Z n) := by
  induction n with
  | zero => exact hYZ
  | succ n ih => exact jump_mono ih

theorem degreeJump_mono : Monotone degreeJump := by
  intro x y h
  obtain ⟨Y,rfl⟩ := degree_surjective x
  obtain ⟨Z,rfl⟩ := degree_surjective y
  exact jump_mono h

end TuringRigidity.OracleJump

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

end TuringRigidity.LocalColumnIndices

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealInterpretation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealInterpretation
open AntichainParameters SetCoding RelationCoding

theorem coe_finset_sup {I : DegreeIdeal} {α : Type*} (F : Finset α) (f : α → I) :
    (F.sup f).val = F.sup (fun a => (f a).val) := by
  classical
  induction F using Finset.induction_on with
  | empty => rfl
  | @insert a F ha ih => simp only [Finset.sup_insert,coe_sup,ih]

section Formula
variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

theorem map_nontrivial (ρ : α ≃o β) (b g₀ g₁ x : α) :
    nontrivial (ρ b) (ρ g₀) (ρ g₁) (ρ x) ↔ nontrivial b g₀ g₁ x := by
  unfold nontrivial
  simp only [← ρ.map_sup,ρ.le_iff_le]
  constructor
  · rintro ⟨hx,z,h₀,h₁,hn⟩
    obtain ⟨w,rfl⟩ := ρ.surjective z
    exact ⟨hx,w,(ρ.le_iff_le).mp h₀,(ρ.le_iff_le).mp h₁,fun h => hn ((ρ.le_iff_le).mpr h)⟩
  · rintro ⟨hx,z,h₀,h₁,hn⟩
    exact ⟨hx,ρ z,(ρ.le_iff_le).mpr h₀,(ρ.le_iff_le).mpr h₁,fun h => hn ((ρ.le_iff_le).mp h)⟩

theorem map_antichain (ρ : α ≃o β) (b g₀ g₁ x : α) :
    antichain (ρ b) (ρ g₀) (ρ g₁) (ρ x) ↔ antichain b g₀ g₁ x := by
  unfold antichain
  rw [map_nontrivial]
  constructor
  · rintro ⟨hx,hm⟩
    refine ⟨hx,fun y hy hyx => ?_⟩
    exact ρ.le_iff_le.mp (hm (ρ y) ((map_nontrivial ρ _ _ _ _).mpr hy) (ρ.le_iff_le.mpr hyx))
  · rintro ⟨hx,hm⟩
    refine ⟨hx,fun y hy hyx => ?_⟩
    obtain ⟨z,rfl⟩ := ρ.surjective y
    exact ρ.le_iff_le.mpr (hm z ((map_nontrivial ρ _ _ _ _).mp hy) (ρ.le_iff_le.mp hyx))
end Formula

theorem ideal_nontrivial (I : DegreeIdeal) (b g₀ g₁ x : I) :
    nontrivial b g₀ g₁ x ↔ NontrivialCommonLower b.val g₀.val g₁.val x.val := by
  constructor
  · rintro ⟨hx,z,h₀,h₁,hn⟩
    exact ⟨hx,z.val,h₀,h₁,hn⟩
  · rintro ⟨hx,z,h₀,h₁,hn⟩
    exact ⟨hx,⟨z,I.lower h₀ (I.join_mem g₀.property x.property)⟩,h₀,h₁,hn⟩

theorem ideal_antichain (I : DegreeIdeal) (b g₀ g₁ x : I) :
    antichain b g₀ g₁ x ↔ CodedAntichain b.val g₀.val g₁.val x.val := by
  constructor
  · rintro ⟨hx,hm⟩
    refine ⟨(ideal_nontrivial I _ _ _ _).mp hx,fun y hy hyx => ?_⟩
    let y' : I := ⟨y,I.lower hy.1 b.property⟩
    exact hm y' ((ideal_nontrivial I _ _ _ _).mpr hy) hyx
  · rintro ⟨hx,hm⟩
    exact ⟨(ideal_nontrivial I _ _ _ _).mpr hx,fun y hy hyx =>
      hm y.val ((ideal_nontrivial I _ _ _ _).mp hy) hyx⟩

theorem transport_antichain {I J : DegreeIdeal} (ρ : I ≃o J) (b g₀ g₁ x : I) :
    CodedAntichain (ρ b).val (ρ g₀).val (ρ g₁).val (ρ x).val ↔
      CodedAntichain b.val g₀.val g₁.val x.val := by
  rw [← ideal_antichain,← ideal_antichain,map_antichain]

theorem ACode.transport {I J : DegreeIdeal} (ρ : I ≃o J) (p : ACode I) (x : I) :
    (p.map ρ).external.Holds (ρ x).val ↔ p.external.Holds x.val :=
  transport_antichain ρ _ _ _ _

theorem SCode.transport {I J : DegreeIdeal} (ρ : I ≃o J) (p : SCode I) (x c : I) :
    (p.map ρ).external.Graph (ρ x).val (ρ c).val ↔ p.external.Graph x.val c.val := by
  change ((ρ x).val ≤ (ρ p.bound).val ∧ (p.tags.map ρ).external.Holds (ρ c).val ∧
    (p.decorated.map ρ).external.Holds ((ρ x).val ⊔ (ρ c).val)) ↔ _
  rw [← coe_sup,← ρ.map_sup,p.tags.transport ρ c,p.decorated.transport ρ (x ⊔ c)]
  exact and_congr ρ.le_iff_le Iff.rfl

theorem RCode.internal {I : DegreeIdeal} {n : ℕ} (p : RCode I n) (v : Fin n → I) :
    p.external.Holds (fun i => (v i).val) ↔
      ∃ c : Fin n → I, (∀ i, (p.coordinates i).external.Graph (v i).val (c i).val) ∧
        p.tuples.external.Holds (Finset.univ.sup c).val := by
  constructor
  · rintro ⟨c,hc,ht⟩
    have hm : ∀ i, c i ∈ I.carrier := fun i =>
      I.lower (hc i).2.1.1.1 (p.coordinates i).tags.bound.property
    refine ⟨fun i => ⟨c i,hm i⟩,hc,?_⟩
    simpa only [coe_finset_sup,RCode.external] using ht
  · rintro ⟨c,hc,ht⟩
    exact ⟨fun i => (c i).val,hc,by simpa only [coe_finset_sup,RCode.external] using ht⟩

private theorem map_sup_finset {I J : DegreeIdeal} (ρ : I ≃o J) {α : Type*}
    (F : Finset α) (f : α → I) : ρ (F.sup f) = F.sup (fun a => ρ (f a)) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ρ.map_bot
  | @insert a F ha ih => simp only [Finset.sup_insert,ρ.map_sup,ih]

theorem RCode.transport {I J : DegreeIdeal} {n : ℕ} (ρ : I ≃o J) (p : RCode I n) (v : Fin n → I) :
    (p.map ρ).external.Holds (fun i => (ρ (v i)).val) ↔ p.external.Holds (fun i => (v i).val) := by
  classical
  rw [(p.map ρ).internal,p.internal]
  constructor
  · rintro ⟨c,hc,ht⟩
    let d := fun i => ρ.symm (c i)
    have hd : ∀ i, ρ (d i) = c i := fun i => ρ.apply_symm_apply _
    refine ⟨d,fun i => ?_,?_⟩
    · exact ((p.coordinates i).transport ρ (v i) (d i)).mp (by simpa only [hd,RCode.map] using hc i)
    · apply (p.tuples.transport ρ (Finset.univ.sup d)).mp
      have he : ρ (Finset.univ.sup d) = Finset.univ.sup c := by
        rw [map_sup_finset]
        simp only [hd]
      simpa only [he,RCode.map] using ht
  · rintro ⟨c,hc,ht⟩
    refine ⟨fun i => ρ (c i),fun i => ((p.coordinates i).transport ρ (v i) (c i)).mpr (hc i),?_⟩
    have hh := (p.tuples.transport ρ (Finset.univ.sup c)).mpr ht
    simpa only [map_sup_finset,RCode.map] using hh

end TuringRigidity.IdealInterpretation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealLift
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealInterpretation
open SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding

theorem ACode.map_below {I J : DegreeIdeal} (ρ : I ≃o J) (p : ACode I) (b : I)
    (hp : AntichainBelow p.external b.val) : AntichainBelow (p.map ρ).external (ρ b).val :=
  ⟨show ρ p.bound ≤ ρ b from ρ.monotone hp.1,
    show ρ p.left ≤ ρ b from ρ.monotone hp.2.1,
    show ρ p.right ≤ ρ b from ρ.monotone hp.2.2⟩

theorem SCode.map_below {I J : DegreeIdeal} (ρ : I ≃o J) (p : SCode I) (b : I)
    (hp : SetBelow p.external b.val) : SetBelow (p.map ρ).external (ρ b).val :=
  ⟨show ρ p.bound ≤ ρ b from ρ.monotone hp.1,p.tags.map_below ρ b hp.2.1,
    p.decorated.map_below ρ b hp.2.2⟩

theorem RCode.map_below {I J : DegreeIdeal} {n : ℕ} (ρ : I ≃o J) (p : RCode I n) (b : I)
    (hp : RelationBelow p.external b.val) : RelationBelow (p.map ρ).external (ρ b).val :=
  ⟨fun i => (p.coordinates i).map_below ρ b (hp.1 i),p.tuples.map_below ρ b hp.2⟩

theorem RCode.coordinates_mem {I : DegreeIdeal} {n : ℕ} (p : RCode I n) {v : Fin n → Degree}
    (h : p.external.Holds v) (i : Fin n) : v i ∈ I.carrier := by
  obtain ⟨c,hc,_⟩ := h
  exact I.lower (hc i).1 (p.coordinates i).bound.property

theorem RCode.transport_one {I J : DegreeIdeal} (ρ : I ≃o J) (p : RCode I 1) (a : I) :
    (p.map ρ).external.Holds (one (ρ a).val) ↔ p.external.Holds (one a.val) := by
  have hv : (fun _ : Fin 1 => (ρ a).val) = one (ρ a).val := by
    funext i; fin_cases i; rfl
  have hw : (fun _ : Fin 1 => a.val) = one a.val := by
    funext i; fin_cases i; rfl
  simpa only [hv,hw] using p.transport ρ (fun _ => a)

theorem RCode.transport_two {I J : DegreeIdeal} (ρ : I ≃o J) (p : RCode I 2) (a b : I) :
    (p.map ρ).external.Holds (two (ρ a).val (ρ b).val) ↔ p.external.Holds (two a.val b.val) := by
  have hv : (fun i : Fin 2 => (ρ (![a,b] i)).val) = two (ρ a).val (ρ b).val := by
    funext i; fin_cases i <;> rfl
  have hw : (fun i : Fin 2 => (![a,b] i).val) = two a.val b.val := by
    funext i; fin_cases i <;> rfl
  simpa only [hv,hw] using p.transport ρ ![a,b]

end TuringRigidity.IdealInterpretation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealCopy
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealInterpretation
open SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding
noncomputable section

theorem transport_copy {U : ℕ → Prop} {I J : DegreeIdeal} (ρ : I ≃o J)
    (c : Copy U) (b : I) (hS : RelationBelow c.successor b.val) (hP : RelationBelow c.predicate b.val) :
    ∃ d : Copy U, RelationBelow d.successor (ρ b).val ∧ RelationBelow d.predicate (ρ b).val := by
  let S := RCode.ofBelow c.successor b hS
  let P := RCode.ofBelow c.predicate b hP
  have hn (n : ℕ) : c.node n ∈ I.carrier := by
    have hh : S.external.Holds (two (c.node n) (c.node (n+1))) := by
      simpa only [S,RCode.external_ofBelow] using (c.successor_spec _ _).mpr ⟨n,rfl,rfl⟩
    exact S.coordinates_mem hh 0
  let node : ℕ → I := fun n => ⟨c.node n,hn n⟩
  have hi : Function.Injective (fun n => (ρ (node n)).val) := by
    intro i j he
    have hh : ρ (node i) = ρ (node j) := Element.ext _ _ he
    exact c.injective (congrArg Element.val (ρ.injective hh))
  have hsuccessor (a d : J) : (S.map ρ).external.Holds (two a.val d.val) ↔
      ∃ k, a = ρ (node k) ∧ d = ρ (node (k+1)) := by
    have hh := S.transport_two ρ (ρ.symm a) (ρ.symm d)
    simp only [ρ.apply_symm_apply,S,RCode.external_ofBelow] at hh
    rw [hh,c.successor_spec]
    constructor
    · rintro ⟨k,hk,hl⟩
      have he : ρ.symm a = node k := Element.ext _ _ hk
      have hf : ρ.symm d = node (k+1) := Element.ext _ _ hl
      exact ⟨k,by rw [← he,ρ.apply_symm_apply],by rw [← hf,ρ.apply_symm_apply]⟩
    · rintro ⟨k,rfl,rfl⟩
      exact ⟨k,by simp only [ρ.symm_apply_apply,node],by simp only [ρ.symm_apply_apply,node]⟩
  have hpredicate (a : J) : (P.map ρ).external.Holds (one a.val) ↔
      ∃ k, U k ∧ a = ρ (node k) := by
    have hh := P.transport_one ρ (ρ.symm a)
    simp only [ρ.apply_symm_apply,P,RCode.external_ofBelow] at hh
    rw [hh,c.predicate_spec]
    constructor
    · rintro ⟨k,hk,he⟩
      have hf : ρ.symm a = node k := Element.ext _ _ he
      exact ⟨k,hk,by rw [← hf,ρ.apply_symm_apply]⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨k,hk,by simp only [ρ.symm_apply_apply,node]⟩
  have hsglobal (a d : Degree) : (S.map ρ).external.Holds (two a d) ↔
      ∃ k, a = (ρ (node k)).val ∧ d = (ρ (node (k+1))).val := by
    constructor
    · intro h
      have ha : a ∈ J.carrier := (S.map ρ).coordinates_mem h 0
      have hd : d ∈ J.carrier := (S.map ρ).coordinates_mem h 1
      obtain ⟨k,hk,hl⟩ := (hsuccessor ⟨a,ha⟩ ⟨d,hd⟩).mp h
      exact ⟨k,congrArg Element.val hk,congrArg Element.val hl⟩
    · rintro ⟨k,rfl,rfl⟩
      exact (hsuccessor _ _).mpr ⟨k,rfl,rfl⟩
  have hpglobal (a : Degree) : (P.map ρ).external.Holds (one a) ↔
      ∃ k, U k ∧ a = (ρ (node k)).val := by
    constructor
    · intro h
      have ha : a ∈ J.carrier := (P.map ρ).coordinates_mem h 0
      obtain ⟨k,hk,he⟩ := (hpredicate ⟨a,ha⟩).mp h
      exact ⟨k,hk,congrArg Element.val he⟩
    · rintro ⟨k,hk,rfl⟩
      exact (hpredicate _).mpr ⟨k,hk,rfl⟩
  let d : Copy U := ⟨fun k => (ρ (node k)).val,hi,(S.map ρ).external,(P.map ρ).external,hsglobal,hpglobal⟩
  refine ⟨d,S.map_below ρ b ?_,P.map_below ρ b ?_⟩
  · simpa only [S,RCode.external_ofBelow] using hS
  · simpa only [P,RCode.external_ofBelow] using hP

end
end TuringRigidity.IdealInterpretation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealLocality
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealLocality
open OracleJump ArithmeticHierarchy ArithmeticModelDecoding BoundedDecoding IdealInterpretation
noncomputable section

theorem image_arithmetic {I : DegreeIdeal} (ρ : I ≃o I) (z : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (x : I) :
    ∃ X Y : Oracle, degree X = (ρ x).val ∧ degree Y = x.val ⊔ (ρ.symm z).val ∧
      Reduces X (iterate Y 5) := by
  obtain ⟨X,hX⟩ := degree_surjective (ρ x).val
  obtain ⟨c,hS,hP⟩ := LocalUnary.localized_copy X
  let b : I := ρ x ⊔ z
  have hb : degree (join X (jump FixedArithmetic.zero)) = b.val := by
    change degree X ⊔ degree (jump FixedArithmetic.zero) = (ρ x).val ⊔ z.val
    rw [hX,hz]
  obtain ⟨d,hdS,hdP⟩ := transport_copy ρ.symm c b (hb ▸ hS) (hb ▸ hP)
  have he : (ρ.symm b).val = x.val ⊔ (ρ.symm z).val := by
    simp only [b,ρ.symm.map_sup,ρ.symm_apply_apply,coe_sup]
  obtain ⟨Y,hY⟩ := degree_surjective (ρ.symm b).val
  have hY' : degree Y = x.val ⊔ (ρ.symm z).val := hY.trans he
  have hrec := (unary_decoding Y d (hY.symm ▸ hdS) (hY.symm ▸ hdP)).2
  have hXY : Reduces X (iterate Y 5) := by
    apply RecursiveIn.iff_nat.mpr
    exact hrec.of_eq (fun n => by cases hx : X n <;> simp [oracleFunction,hx])
  exact ⟨X,Y,hX,hY',hXY⟩

theorem image_mem {I J : DegreeIdeal} (ρ : I ≃o I) (z : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (hjump : JumpClosed J)
    (hpre : (ρ.symm z).val ∈ J.carrier) (x : I) (hx : x.val ∈ J.carrier) :
    (ρ x).val ∈ J.carrier := by
  obtain ⟨X,Y,hX,hY,hXY⟩ := image_arithmetic ρ z hz x
  have hbase : degree Y ∈ J.carrier := hY.symm ▸ J.join_mem hx hpre
  have hit (n : ℕ) : degree (iterate Y n) ∈ J.carrier := by
    induction n with
    | zero => exact hbase
    | succ n ih => exact hjump _ ih
  exact hX ▸ J.lower hXY (hit 5)

theorem invariant {I J : DegreeIdeal} (ρ : I ≃o I) (z : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (hjump : JumpClosed J)
    (himages : (ρ z).val ⊔ (ρ.symm z).val ∈ J.carrier) (x : I) :
    (ρ x).val ∈ J.carrier ↔ x.val ∈ J.carrier := by
  have hforward := image_mem ρ z hz hjump (J.lower le_sup_right himages)
  have hback := image_mem ρ.symm z hz hjump (J.lower le_sup_left himages)
  exact ⟨fun h => by simpa only [ρ.symm_apply_apply] using hback (ρ x) h,hforward x⟩

theorem source_4_1_4 {I J : DegreeIdeal} (ρ : I ≃o I) (z : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (hJI : J.carrier ⊆ I.carrier)
    (hjump : JumpClosed J) (himages : (ρ z).val ⊔ (ρ.symm z).val ∈ J.carrier) :
    ∃ σ : J ≃o J, ∀ x : J, (σ x).val = (ρ ⟨x.val,hJI x.property⟩).val := by
  let incl : J → I := fun x => ⟨x.val,hJI x.property⟩
  let f : J → J := fun x => ⟨(ρ (incl x)).val,
    (invariant ρ z hz hjump himages (incl x)).mpr x.property⟩
  let g : J → J := fun x => ⟨(ρ.symm (incl x)).val,by
    apply (invariant ρ z hz hjump himages (ρ.symm (incl x))).mp
    simpa only [ρ.apply_symm_apply,incl] using x.property⟩
  have hfg (x : J) : f (g x) = x := by
    apply Element.ext
    change (ρ (ρ.symm (incl x))).val = x.val
    rw [ρ.apply_symm_apply]
  have hgf (x : J) : g (f x) = x := by
    apply Element.ext
    change (ρ.symm (ρ (incl x))).val = x.val
    rw [ρ.symm_apply_apply]
  let σ : J ≃o J :=
    { toEquiv := ⟨f,g,hgf,hfg⟩
      map_rel_iff' := by
        intro x y
        change ρ (incl x) ≤ ρ (incl y) ↔ incl x ≤ incl y
        exact ρ.le_iff_le }
  exact ⟨σ,fun _ => rfl⟩

end
end TuringRigidity.IdealLocality

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentLocality
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentLocality
open IdealInterpretation IdealLocality PersistentRestrictions OracleJump
noncomputable section

theorem extends_symm {I K : CountableIdeal} {hIK : I.carrier ⊆ K.carrier}
    {ρ : I ≃o I} {σ : K ≃o K} (he : Extends hIK ρ σ) :
    Extends hIK ρ.symm σ.symm := by
  intro x
  have h : σ ⟨(ρ.symm x).val,hIK (ρ.symm x).property⟩ = ⟨x.val,hIK x.property⟩ := by
    apply Subtype.ext
    exact (he (ρ.symm x)).trans (congrArg Subtype.val (ρ.apply_symm_apply x))
  have hh := congrArg (fun y => (σ.symm y).val) h
  simpa only [σ.symm_apply_apply] using hh.symm

theorem source_4_1_5 (I J : CountableIdeal) (ρ : I ≃o I)
    (hp : Persistent I ρ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier) (hjump : JumpClosed (ideal J)) :
    ∃ σ : J ≃o J, Extends hIJ ρ σ := by
  obtain ⟨b,hb⟩ := CountableBound.countable_bounded J.carrier J.countable
  obtain ⟨K,hIK,τ,hbK,he⟩ := hp b
  have hJK : J.carrier ⊆ K.carrier := fun x hx => K.lower (hb x hx) hbK
  let z : I := ⟨degree (jump FixedArithmetic.zero),hz⟩
  let zK : ideal K := ⟨z.val,hIK z.property⟩
  have hforward : ((lift τ) zK).val ∈ J.carrier := by
    change (τ ⟨z.val,hIK z.property⟩).val ∈ J.carrier
    rw [he z]
    exact hIJ (ρ z).property
  have hback : ((lift τ).symm zK).val ∈ J.carrier := by
    change (τ.symm ⟨z.val,hIK z.property⟩).val ∈ J.carrier
    rw [extends_symm he z]
    exact hIJ (ρ.symm z).property
  obtain ⟨σ,hσ⟩ := source_4_1_4 (lift τ) zK rfl hJK hjump (J.join_mem hforward hback)
  refine ⟨unlift σ,fun x => ?_⟩
  exact (hσ ⟨x.val,hIJ x.property⟩).trans (he x)

end
end TuringRigidity.PersistentLocality

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_JumpIdeal
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.JumpIdeal
open OracleJump IdealInterpretation IdealLocality PersistentRestrictions PersistentLocality GlobalLocality
noncomputable section

theorem includes (x : Degree) : x ∈ (generated x).carrier := ⟨0,le_rfl⟩

theorem closed (x : Degree) : JumpClosed (ideal (generated x)) := by
  intro y hy
  obtain ⟨n,hn⟩ := hy
  exact ⟨n+1,degreeJump_mono hn⟩

end
end TuringRigidity.JumpIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_EnumerationDecoding
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.EnumerationDecoding
open IndexPresentation IndexTuples ArithmeticHierarchy DecodingTheorem
open SetCoding RelationCoding BoundedDecoding OracleJump ArithmeticModelDecoding

theorem path_node {Y} (c : Enumeration) {z : ℕ} (hz : Dom Y z) (he : value Y z = c.node 0)
    {n t : ℕ} (hpath : Path Y c.successor z n t) :
    ∀ i, i ≤ n → Dom Y (item t i) ∧ value Y (item t i) = c.node i := by
  intro i hi
  induction i with
  | zero =>
    exact ⟨hpath.1, (le_antisymm ((le_iff hpath.1 hz).mp hpath.2.1)
      ((le_iff hz hpath.1).mp hpath.2.2.1)).trans he⟩
  | succ i ih =>
    have hprev := ih (by omega)
    have hs := hpath.2.2.2 i (by omega)
    have hnext : Dom Y (item t (i+1)) := by
      simpa [twoIndex,entry] using hs.1 (1 : Fin 2)
    obtain ⟨k,hk,hkn⟩ := (c.successor_spec _ _).mp ((presented_two hprev.1 hnext).mp hs)
    have hki : k = i := c.injective (hk.symm.trans hprev.2)
    exact ⟨hnext, by simpa [hki] using hkn⟩

theorem node_below  (Y : Oracle) (c : Enumeration)
    (hS : RelationBelow c.successor (degree Y)) (n : ℕ) : c.node n ≤ degree Y := by
  have hs := (c.successor_spec (c.node n) (c.node (n+1))).mpr ⟨n,rfl,rfl⟩
  obtain ⟨d,hd,_⟩ := hs
  exact (graph_bounded (hS.1 0) (hd 0)).1

theorem path_sigma (Y : Oracle) (S : RelationCode 2) (z : ℕ)
    (hS : RelationBelow S (degree Y)) : Sigma Y 5 (fun v => Path Y S z (Nat.unpair v).1 (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let start := item_primrec.comp r (Primrec.const 0)
  have hd : Sigma Y 5 (fun v => Dom Y (item (Nat.unpair v).2 0)) :=
    (dom_pi Y start).switch.raise.raise
  have hl := (le_sigma Y start (Primrec.const z)).raise.raise
  have hr := (le_sigma Y (Primrec.const z) start).raise.raise
  have hs := ((RelationPresentation.sigma5_decoding Y S hS).comp
    (twoIndex_primrec.comp (item_primrec.comp (r.comp f) r)
      (item_primrec.comp (r.comp f) (Primrec.succ.comp r)))).bounded_all f
  exact (hd.and (hl.and (hr.and hs))).congr (fun v => by
    simp only [ArithmeticModelDecoding.Path,Presented,Nat.unpair_pair])

theorem defined_sigma (Y : Oracle) (S P : RelationCode 2) (z : ℕ)
    (hS : RelationBelow S (degree Y)) (hP : RelationBelow P (degree Y)) :
    Sigma Y 5 (fun v => Defined Y S P z (Nat.unpair v).1 (Nat.unpair v).2) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hs := (path_sigma Y S z hS).comp (Primrec₂.natPair.comp (f.comp f) r)
  have hp := (RelationPresentation.sigma5_decoding Y P hP).comp
    (twoIndex_primrec.comp (item_primrec.comp r (f.comp f)) (r.comp f))
  exact ((hs.and hp).ex).congr (fun v => by simp only [Defined,Presented,Nat.unpair_pair])

theorem defined_iff {Y} (c : Enumeration) {z j : ℕ} (hz : Dom Y z) (hj : Dom Y j)
    (he : value Y z = c.node 0) (hS : RelationBelow c.successor (degree Y)) (n : ℕ) :
    Defined Y c.successor c.payload z n j ↔ c.output n = value Y j := by
  constructor
  · rintro ⟨t,hpath,hp⟩
    have hn := path_node c hz he hpath n le_rfl
    obtain ⟨k,hk,hval⟩ := (c.payload_spec _ _).mp ((presented_two hn.1 hj).mp hp)
    have hkn := c.injective (hk.symm.trans hn.2)
    exact hkn ▸ hval.symm
  · intro hU
    choose e hd hev using (fun i => value_surjective Y (c.node i) (node_below Y c hS i))
    obtain ⟨t,ht⟩ := (exists_items (n+1) (fun i a => a = e i)).mp
      (fun i _ => ⟨e i,rfl⟩)
    have hdom (i : ℕ) (hi : i ≤ n) : Dom Y (item t i) := by rw [ht i (by omega)]; exact hd i
    have hval (i : ℕ) (hi : i ≤ n) : value Y (item t i) = c.node i := by
      rw [ht i (by omega),hev i]
    refine ⟨t,⟨hdom 0 (by omega),?_,?_,?_⟩,?_⟩
    · apply (le_iff (hdom 0 (by omega)) hz).mpr
      rw [hval 0 (by omega),he]
    · apply (le_iff hz (hdom 0 (by omega))).mpr
      rw [hval 0 (by omega),he]
    · intro i hi
      apply (presented_two (hdom i (by omega)) (hdom (i+1) (by omega))).mpr
      exact (c.successor_spec _ _).mpr ⟨i,hval i (by omega),hval (i+1) (by omega)⟩
    · apply (presented_two (hdom n le_rfl) hj).mpr
      exact (c.payload_spec _ _).mpr ⟨n,hval n le_rfl,hU.symm⟩

theorem graph_sigma {H Y : Oracle} (hHY : Reduces H Y) (c : Enumeration)
    (hS : RelationBelow c.successor (degree Y)) (hP : RelationBelow c.payload (degree Y)) :
    Sigma Y 5 (fun v => c.output (Nat.unpair v).1 = degree (EncodedForcing.columns H (Nat.unpair v).2)) := by
  obtain ⟨z,hz,he⟩ := value_surjective Y (c.node 0) (node_below Y c hS 0)
  obtain ⟨idx,hidx,hrep⟩ := LocalColumnIndices.uniform_indices hHY
  have hi := (defined_sigma Y c.successor c.payload z hS hP).comp
    (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.unpair)
      (hidx.comp (Primrec.snd.comp Primrec.unpair)))
  apply hi.congr
  intro v
  simp only [Nat.unpair_pair]
  rw [defined_iff c hz ((TableIndices.valid_iff_represents _ _).mpr ⟨_,hrep _⟩) he hS]
  rw [value_eq (hrep _)]

end TuringRigidity.EnumerationDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticPresentation
open OracleJump ArithmeticHierarchy EncodedForcing BoundedDecoding IdealInterpretation
open EnumerationDecoding EnumerationConstruction GlobalLocality
noncomputable section

theorem reduces_iterate (H : Oracle) (n : ℕ) : Reduces H (iterate H n) := by
  induction n with
  | zero => exact reduces_refl H
  | succ n ih => exact reduces_trans ih (reduces_jump _)

end
end TuringRigidity.ArithmeticPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealEnumeration
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealInterpretation
open SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding EnumerationDecoding
noncomputable section

theorem transport_enumeration {I J : DegreeIdeal} (ρ : I ≃o J)
    (c : Enumeration) (b : I) (hS : RelationBelow c.successor b.val) (hP : RelationBelow c.payload b.val)
    (v : ℕ → I) (hv : ∀ n, (v n).val = c.output n) :
    ∃ d : Enumeration, (∀ n, d.output n = (ρ (v n)).val) ∧
      RelationBelow d.successor (ρ b).val ∧ RelationBelow d.payload (ρ b).val := by
  let S := RCode.ofBelow c.successor b hS
  let P := RCode.ofBelow c.payload b hP
  have hn (n : ℕ) : c.node n ∈ I.carrier := by
    have hh : S.external.Holds (two (c.node n) (c.node (n+1))) := by
      simpa only [S,RCode.external_ofBelow] using (c.successor_spec _ _).mpr ⟨n,rfl,rfl⟩
    exact S.coordinates_mem hh 0
  let node : ℕ → I := fun n => ⟨c.node n,hn n⟩
  have hi : Function.Injective (fun n => (ρ (node n)).val) := by
    intro i j he
    have hh : ρ (node i) = ρ (node j) := Element.ext _ _ he
    exact c.injective (congrArg Element.val (ρ.injective hh))
  have hsuccessor (a d : J) : (S.map ρ).external.Holds (two a.val d.val) ↔
      ∃ k, a = ρ (node k) ∧ d = ρ (node (k+1)) := by
    have hh := S.transport_two ρ (ρ.symm a) (ρ.symm d)
    simp only [ρ.apply_symm_apply,S,RCode.external_ofBelow] at hh
    rw [hh,c.successor_spec]
    constructor
    · rintro ⟨k,hk,hl⟩
      have he : ρ.symm a = node k := Element.ext _ _ hk
      have hf : ρ.symm d = node (k+1) := Element.ext _ _ hl
      exact ⟨k,by rw [← he,ρ.apply_symm_apply],by rw [← hf,ρ.apply_symm_apply]⟩
    · rintro ⟨k,rfl,rfl⟩
      exact ⟨k,by simp only [ρ.symm_apply_apply,node],by simp only [ρ.symm_apply_apply,node]⟩
  have hpayload (a d : J) : (P.map ρ).external.Holds (two a.val d.val) ↔
      ∃ k, a = ρ (node k) ∧ d = ρ (v k) := by
    have hh := P.transport_two ρ (ρ.symm a) (ρ.symm d)
    simp only [ρ.apply_symm_apply,P,RCode.external_ofBelow] at hh
    rw [hh,c.payload_spec]
    constructor
    · rintro ⟨k,hk,hl⟩
      have he : ρ.symm a = node k := Element.ext _ _ hk
      have hf : ρ.symm d = v k := Element.ext _ _ (hl.trans (hv k).symm)
      exact ⟨k,by rw [← he,ρ.apply_symm_apply],by rw [← hf,ρ.apply_symm_apply]⟩
    · rintro ⟨k,rfl,rfl⟩
      exact ⟨k,by simp only [ρ.symm_apply_apply,node],by simpa only [ρ.symm_apply_apply] using hv k⟩
  have hsglobal (a d : Degree) : (S.map ρ).external.Holds (two a d) ↔
      ∃ k, a = (ρ (node k)).val ∧ d = (ρ (node (k+1))).val := by
    constructor
    · intro h
      have ha : a ∈ J.carrier := (S.map ρ).coordinates_mem h 0
      have hd : d ∈ J.carrier := (S.map ρ).coordinates_mem h 1
      obtain ⟨k,hk,hl⟩ := (hsuccessor ⟨a,ha⟩ ⟨d,hd⟩).mp h
      exact ⟨k,congrArg Element.val hk,congrArg Element.val hl⟩
    · rintro ⟨k,rfl,rfl⟩
      exact (hsuccessor _ _).mpr ⟨k,rfl,rfl⟩
  have hpglobal (a d : Degree) : (P.map ρ).external.Holds (two a d) ↔
      ∃ k, a = (ρ (node k)).val ∧ d = (ρ (v k)).val := by
    constructor
    · intro h
      have ha : a ∈ J.carrier := (P.map ρ).coordinates_mem h 0
      have hd : d ∈ J.carrier := (P.map ρ).coordinates_mem h 1
      obtain ⟨k,hk,hl⟩ := (hpayload ⟨a,ha⟩ ⟨d,hd⟩).mp h
      exact ⟨k,congrArg Element.val hk,congrArg Element.val hl⟩
    · rintro ⟨k,rfl,rfl⟩
      exact (hpayload _ _).mpr ⟨k,rfl,rfl⟩
  let d : Enumeration := ⟨fun k => (ρ (node k)).val,hi,fun k => (ρ (v k)).val,
    (S.map ρ).external,(P.map ρ).external,hsglobal,hpglobal⟩
  refine ⟨d,fun _ => rfl,S.map_below ρ b ?_,P.map_below ρ b ?_⟩
  · simpa only [S,RCode.external_ofBelow] using hS
  · simpa only [P,RCode.external_ofBelow] using hP

end
end TuringRigidity.IdealInterpretation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealPresentation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.IdealPresentation
open OracleJump ArithmeticHierarchy EncodedForcing BoundedDecoding IdealInterpretation IdealLocality
open EnumerationDecoding EnumerationConstruction
noncomputable section

theorem source_4_1_7 (I J : DegreeIdeal) (H : Oracle) (ρ : J ≃o J)
    (hpres : ∀ x, x ∈ I.carrier ↔ ∃ k, degree (columns H k) = x)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hH : degree H ∈ J.carrier) (hjump : JumpClosed J)
    (hinv : ∀ x : J, (ρ x).val ∈ I.carrier ↔ x.val ∈ I.carrier) :
    Sigma (iterate H 6) 5 (Graph ρ H hH) ∧ RecursivePred (iterate H 11) (Graph ρ H hH) := by
  have hbound (x : Degree) (hx : x ∈ I.carrier) : x ≤ degree H := by
    obtain ⟨k,rfl⟩ := (hpres x).mp hx
    exact CodingExtraction.column_projection_reduces H k
  have hzero : Reduces (jump FixedArithmetic.zero) H := hbound _ hz
  let z : J := ⟨degree (jump FixedArithmetic.zero),J.lower hzero hH⟩
  have hpre : (ρ.symm z).val ≤ degree H := by
    apply hbound
    apply (hinv (ρ.symm z)).mp
    simpa only [ρ.apply_symm_apply,z] using hz
  let b : J := ⟨degree (jump H),hjump _ hH⟩
  obtain ⟨c,hout,hS,hP⟩ := enumeration_exists H hzero
  obtain ⟨d,hdout,hdS,hdP⟩ := transport_enumeration ρ c b hS hP (entry H hH)
    (fun n => by simp only [entry,hout])
  have hb : (ρ b).val ≤ degree (iterate H 6) := by
    obtain ⟨X,Y,hX,hY,hXY⟩ := image_arithmetic ρ z rfl b
    have hYH : Reduces Y (jump H) := by
      change degree Y ≤ degree (jump H)
      rw [hY]
      exact sup_le le_rfl (hpre.trans (reduces_jump H))
    rw [← hX]
    exact reduces_trans hXY (iterate_mono hYH 5)
  have hg := graph_sigma (ArithmeticPresentation.reduces_iterate H 6) d (hdS.mono hb) (hdP.mono hb)
  have h : Sigma (iterate H 6) 5 (Graph ρ H hH) := hg.congr (fun v => by
    simp only [hdout,Graph])
  have hr := form_recursive h
  exact ⟨h,hr⟩

end
end TuringRigidity.IdealPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentPresentation
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentPresentation
open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation IdealLocality PersistentRestrictions PersistentLocality
noncomputable section

theorem source_4_1_8 {I : CountableIdeal} (ρ : I ≃o I) (hp : Persistent I ρ)
    (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    {H : Oracle} (hpres : Presented I H) :
    Sigma (iterate H 6) 5 (Graph ρ hpres) ∧ RecursivePred (iterate H 11) (Graph ρ hpres) := by
  let J := JumpIdeal.generated (degree H)
  have hH : degree H ∈ J.carrier := JumpIdeal.includes _
  have hIJ : I.carrier ⊆ J.carrier := by
    intro x hx
    obtain ⟨k,rfl⟩ := (hpres x).mp hx
    exact J.lower (CodingExtraction.column_projection_reduces H k) hH
  obtain ⟨σ,he⟩ := source_4_1_5 I J ρ hp hz hIJ (JumpIdeal.closed _)
  have hinv : ∀ x : ideal J, ((lift σ) x).val ∈ I.carrier ↔ x.val ∈ I.carrier := by
    intro x
    constructor
    · intro hx
      let y : I := ⟨((lift σ) x).val,hx⟩
      have hh := extends_symm he y
      have hh' : (σ.symm (σ ((bridge J).symm x))).val = (ρ.symm y).val := hh
      rw [σ.symm_apply_apply] at hh'
      change x.val = (ρ.symm y).val at hh'
      rw [hh']
      exact (ρ.symm y).property
    · intro hx
      have hh := he ⟨x.val,hx⟩
      change ((lift σ) x).val = (ρ ⟨x.val,hx⟩).val at hh
      rw [hh]
      exact (ρ ⟨x.val,hx⟩).property
  have hg := (IdealPresentation.source_4_1_7 (ideal I) (ideal J) H (lift σ)
    hpres hz hH (JumpIdeal.closed _) hinv).1
  have hh : Sigma (iterate H 6) 5 (Graph ρ hpres) := hg.congr (fun v => by
    change (σ ⟨degree (columns H (Nat.unpair v).1),_⟩).val = _ ↔ _
    exact Iff.of_eq (congrArg (fun x : Degree => x = degree (columns H (Nat.unpair v).2))
      (he (entry hpres (Nat.unpair v).1))))
  have hr := form_recursive hh
  exact ⟨hh,hr⟩

end
end TuringRigidity.PersistentPresentation

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentCountability
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentCountability
open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions PersistentPresentation
noncomputable section
attribute [local instance] Classical.propDecidable

theorem presentation_exists (I : CountableIdeal) : ∃ H, Presented I H := by
  obtain ⟨f,hf⟩ := I.countable.exists_eq_range I.nonempty
  choose A hA using (fun n => degree_surjective (f n))
  refine ⟨CountableBound.sum A,fun x => ?_⟩
  have hc (k : ℕ) : columns (CountableBound.sum A) k = A k := by
    funext n
    simp only [columns,CountableBound.sum,Nat.unpair_pair]
  simp only [hc,hA,hf,Set.mem_range]

theorem graphOracle_injective {I : CountableIdeal} {H : Oracle}
    (hpres : Presented I H) : Function.Injective (graphOracle hpres) := by
  intro ρ σ he
  apply OrderIso.ext
  funext x
  obtain ⟨n,hn⟩ := (hpres x.val).mp x.property
  obtain ⟨j,hj⟩ := (hpres (ρ x).val).mp (ρ x).property
  have hx : entry hpres n = x := Subtype.ext hn
  have hp : Graph ρ hpres (Nat.pair n j) := by
    simp only [PersistentPresentation.Graph,Nat.unpair_pair,hx,hj]
  have hq : Graph σ hpres (Nat.pair n j) := by
    by_contra hn
    have hh := congrFun he (Nat.pair n j)
    simp only [graphOracle,decide_eq_true hp,decide_eq_false hn] at hh
    cases hh
  apply Subtype.ext
  simpa only [PersistentPresentation.Graph,Nat.unpair_pair,hx,hj] using hq.symm

theorem graphOracle_reduces {I : CountableIdeal} {H Y : Oracle}
    (hpres : Presented I H) (ρ : I ≃o I) (h : RecursivePred Y (Graph ρ hpres)) :
    Reduces (graphOracle hpres ρ) Y := by
  apply RecursiveIn.iff_nat.mpr
  exact h.of_eq (fun n => by simp [oracleFunction,graphOracle])

theorem arithmetic_maps_countable {I : CountableIdeal} {H : Oracle}
    (hpres : Presented I H) (Y : Oracle) :
    {ρ : I ≃o I | RecursivePred Y (Graph ρ hpres)}.Countable := by
  apply ((countable_reduces Y).preimage (graphOracle_injective hpres)).mono
  intro ρ hρ
  exact graphOracle_reduces hpres ρ hρ

end
end TuringRigidity.PersistentCountability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentExtension
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentExtension
open EncodedForcing OracleJump ArithmeticHierarchy IdealInterpretation IdealLocality
open PersistentRestrictions PersistentLocality PersistentPresentation PersistentCountability
noncomputable section

theorem nonpersistent_witness {J : CountableIdeal} {σ : J ≃o J}
    (h : ¬ Persistent J σ) :
    ∃ x, ∀ (K : CountableIdeal) (hJK : J.carrier ⊆ K.carrier) (τ : K ≃o K),
      x ∈ K.carrier → ¬ Extends hJK σ τ := by
  simpa only [Persistent,not_forall,not_exists,not_and] using h

theorem source_4_1_10 (I J : CountableIdeal) (ρ : I ≃o I)
    (hp : Persistent I ρ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hIJ : I.carrier ⊆ J.carrier) (hj : JumpClosed (ideal J)) :
    ∃ σ : J ≃o J, Extends hIJ ρ σ ∧ Persistent J σ := by
  classical
  by_contra hn
  have hnot (σ : J ≃o J) (he : Extends hIJ ρ σ) : ¬ Persistent J σ :=
    fun hpσ => hn ⟨σ,he,hpσ⟩
  obtain ⟨H,hpres⟩ := presentation_exists J
  let S : Set (J ≃o J) := {σ | RecursivePred (iterate H 11) (Graph σ hpres)}
  have hS : S.Countable := arithmetic_maps_countable hpres _
  have : Countable S := hS.to_subtype
  have hwitness (σ : S) : ∃ x, Extends hIJ ρ σ.val →
      ∀ (K : CountableIdeal) (hJK : J.carrier ⊆ K.carrier) (τ : K ≃o K),
        x ∈ K.carrier → ¬ Extends hJK σ.val τ := by
    by_cases he : Extends hIJ ρ σ.val
    · obtain ⟨x,hx⟩ := nonpersistent_witness (hnot σ.val he)
      exact ⟨x,fun _ => hx⟩
    · exact ⟨⊥,fun h => (he h).elim⟩
  choose w hw using hwitness
  let L := JumpIdeal.generated (degree H)
  have hJL : J.carrier ⊆ L.carrier := by
    intro x hx
    obtain ⟨n,rfl⟩ := (hpres x).mp hx
    exact L.lower (CodingExtraction.column_projection_reduces H n) (JumpIdeal.includes _)
  obtain ⟨b,hb⟩ := CountableBound.countable_bounded (Set.range w ∪ L.carrier)
    ((Set.countable_range w).union L.countable)
  obtain ⟨K,hIK,τ,hbK,he⟩ := hp b
  have hLK : L.carrier ⊆ K.carrier := fun x hx => K.lower (hb x (Or.inr hx)) hbK
  have hJK : J.carrier ⊆ K.carrier := fun x hx => hLK (hJL hx)
  obtain ⟨σ,hρ,hτ,hr⟩ := PersistentRestrictionCode.restriction ρ τ hIK he hz
    hIJ hJK hj hpres hLK
  let s : S := ⟨σ,hr⟩
  have hwK : w s ∈ K.carrier := K.lower (hb (w s) (Or.inl ⟨s,rfl⟩)) hbK
  exact hw s hρ K hJK τ hwK hτ

end
end TuringRigidity.PersistentExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalAutomorphism
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericalAutomorphism
open EncodedForcing PersistentRestrictions PersistentPresentation
noncomputable section

theorem action_of_automorphism {I : CountableIdeal} {H : Oracle}
    (hpres : Presented I H) (ρ : I ≃o I) : Action H (Graph ρ hpres) := by
  constructor
  · intro n
    obtain ⟨m,hm⟩ := (hpres (ρ (entry hpres n)).val).mp (ρ (entry hpres n)).property
    exact ⟨m,by simpa only [PersistentPresentation.Graph,Nat.unpair_pair] using hm.symm⟩
  · intro m
    obtain ⟨n,hn⟩ := (hpres (ρ.symm (entry hpres m)).val).mp (ρ.symm (entry hpres m)).property
    have he : entry hpres n = ρ.symm (entry hpres m) := Subtype.ext hn
    refine ⟨n,?_⟩
    simp only [PersistentPresentation.Graph,Nat.unpair_pair]
    rw [he,ρ.apply_symm_apply]
    rfl
  · intro n m n' m' hp hq
    simp only [PersistentPresentation.Graph,Nat.unpair_pair] at hp hq
    rw [← hp,← hq]
    change entry hpres n ≤ entry hpres n' ↔ ρ (entry hpres n) ≤ ρ (entry hpres n')
    exact ρ.le_iff_le.symm
  · intro n m m' hp he
    simpa only [PersistentPresentation.Graph,Nat.unpair_pair,← he] using hp

theorem reconstruct {I : CountableIdeal} {H : Oracle} (hpres : Presented I H)
    {P : ℕ → Prop} (ha : Action H P) :
    ∃ ρ : I ≃o I, ∀ v, P v ↔ Graph ρ hpres v := by
  classical
  let idx (x : I) : ℕ := Classical.choose ((hpres x.val).mp x.property)
  have hidx (x : I) : degree (columns H (idx x)) = x.val :=
    Classical.choose_spec ((hpres x.val).mp x.property)
  let out (n : ℕ) : ℕ := Classical.choose (ha.total n)
  have hout (n : ℕ) : P (Nat.pair n (out n)) := Classical.choose_spec (ha.total n)
  let f (x : I) : I := entry hpres (out (idx x))
  have hf (x : I) (n m : ℕ) (hn : degree (columns H n) = x.val)
      (hp : P (Nat.pair n m)) : (f x).val = degree (columns H m) := by
    apply le_antisymm
    · exact (ha.order _ _ _ _ (hout (idx x)) hp).mp (by rw [hidx,hn])
    · exact (ha.order _ _ _ _ hp (hout (idx x))).mp (by rw [hidx,hn])
  have hle (x y : I) : f x ≤ f y ↔ x ≤ y := by
    have hh := (ha.order _ _ _ _ (hout (idx x)) (hout (idx y))).symm
    change degree (columns H (out (idx x))) ≤ degree (columns H (out (idx y))) ↔ x.val ≤ y.val
    simpa only [hidx] using hh
  have hinj : Function.Injective f := by
    intro x y he
    exact le_antisymm ((hle x y).mp (le_of_eq he)) ((hle y x).mp (le_of_eq he.symm))
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨n,hn⟩ := ha.onto (idx y)
    refine ⟨entry hpres n,Subtype.ext ?_⟩
    exact (hf (entry hpres n) n (idx y) rfl hn).trans (hidx y)
  let ρ : I ≃o I :=
    { toEquiv := Equiv.ofBijective f ⟨hinj,hsurj⟩
      map_rel_iff' := by intro x y; exact hle x y }
  refine ⟨ρ,fun v => ?_⟩
  obtain ⟨⟨n,m⟩,rfl⟩ := Nat.pairEquiv.surjective v
  change P (Nat.pair n m) ↔ Graph ρ hpres (Nat.pair n m)
  simp only [PersistentPresentation.Graph,Nat.unpair_pair]
  constructor
  · intro hp
    exact hf (entry hpres n) n m rfl hp
  · intro hg
    change (f (entry hpres n)).val = degree (columns H m) at hg
    have hnm := hf (entry hpres n) n (out n) rfl (hout n)
    exact ha.saturated n (out n) m (hout n) (hnm.symm.trans hg)

end
end TuringRigidity.NumericalAutomorphism

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalIdeal
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericalIdeal
open EncodedForcing OracleJump IndexPresentation IdealInterpretation IdealLocality
open PersistentRestrictions PersistentLocality PersistentPresentation
noncomputable section

theorem decoded_presentation (H : Oracle) (hc : JumpCode H) : Presented (decode H hc) H :=
  fun _ => Iff.rfl

theorem decoded_closed (H : Oracle) (hc : JumpCode H) : JumpClosed (ideal (decode H hc)) := by
  intro x hx
  obtain ⟨n,rfl⟩ := hx
  obtain ⟨m,hm⟩ := hc.jump n
  exact ⟨m,hm.symm⟩

theorem code_of_ideal {J : CountableIdeal} {H : Oracle} (hp : Presented J H)
    (hj : JumpClosed (ideal J)) : JumpCode H := by
  constructor
  · intro n e _
    obtain ⟨m,hm⟩ := (hp _).mp (J.lower (value_below (columns H n) e) (entry hp n).property)
    exact ⟨m,hm.symm⟩
  · intro n m
    obtain ⟨k,hk⟩ := (hp _).mp (J.join_mem (entry hp n).property (entry hp m).property)
    exact ⟨k,hk.symm⟩
  · intro n
    obtain ⟨m,hm⟩ := (hp _).mp (hj _ (entry hp n).property)
    exact ⟨m,hm.symm⟩

theorem includes_iff {I J : CountableIdeal} {A H : Oracle}
    (hA : Presented I A) (hH : Presented J H) : Includes A H ↔ I.carrier ⊆ J.carrier := by
  constructor
  · intro h x hx
    obtain ⟨n,rfl⟩ := (hA x).mp hx
    obtain ⟨m,hm⟩ := h n
    exact (hH _).mpr ⟨m,hm.symm⟩
  · intro h n
    obtain ⟨m,hm⟩ := (hH _).mp (h (entry hA n).property)
    exact ⟨m,hm.symm⟩

end
end TuringRigidity.NumericalIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_NumericalExtension
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.NumericalExtension
open EncodedForcing PersistentRestrictions PersistentPresentation NumericalAutomorphism
noncomputable section

theorem compatible_iff {I J : CountableIdeal} {A H : Oracle}
    (hA : Presented I A) (hH : Presented J H) (hIJ : I.carrier ⊆ J.carrier)
    (ρ : I ≃o I) (σ : J ≃o J) :
    Compatible A H (Graph ρ hA) (Graph σ hH) ↔ Extends hIJ ρ σ := by
  constructor
  · intro hc x
    obtain ⟨i,hi⟩ := (hA x.val).mp x.property
    obtain ⟨j,hj⟩ := (hA (ρ x).val).mp (ρ x).property
    obtain ⟨n,hn⟩ := (hH x.val).mp (hIJ x.property)
    obtain ⟨m,hm⟩ := (hH (σ ⟨x.val,hIJ x.property⟩).val).mp (σ ⟨x.val,hIJ x.property⟩).property
    have heI : entry hA i = x := Subtype.ext hi
    have heJ : entry hH n = ⟨x.val,hIJ x.property⟩ := Subtype.ext hn
    have hR : Graph ρ hA (Nat.pair i j) := by
      simp only [PersistentPresentation.Graph,Nat.unpair_pair]
      rw [heI,hj]
    have hP : Graph σ hH (Nat.pair n m) := by
      simp only [PersistentPresentation.Graph,Nat.unpair_pair]
      rw [heJ,hm]
    exact hm.symm.trans ((hc i j n m hR hP (hi.trans hn.symm)).symm.trans hj)
  · intro he i j n m hR hP hin
    have hi : (⟨(entry hA i).val,hIJ (entry hA i).property⟩ : J) = entry hH n := Subtype.ext hin
    have hh := he (entry hA i)
    rw [hi] at hh
    simp only [PersistentPresentation.Graph,Nat.unpair_pair] at hR hP
    exact hR.symm.trans (hh.symm.trans hP)

end
end TuringRigidity.NumericalExtension

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistenceCriterion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistenceCriterion
open EncodedForcing OracleJump ArithmeticHierarchy PersistentRestrictions PersistentLocality
open PersistentPresentation PersistentCountability NumericalAutomorphism NumericalIdeal NumericalExtension
noncomputable section

theorem action_congr {H : Oracle} {P Q : ℕ → Prop} (h : ∀ v, P v ↔ Q v) :
    Action H P ↔ Action H Q := by
  have he : P = Q := funext (fun v => propext (h v))
  rw [he]

end
end TuringRigidity.PersistenceCriterion

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticPersistence
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ArithmeticPersistence
open Encodable EncodedForcing OracleJump ArithmeticHierarchy UniformArithmetic
open PersistentRestrictions PersistentLocality PersistentPresentation PersistentCountability
open NumericalAutomorphism NumericalIdeal NumericalExtension
noncomputable section

theorem graph_program {I : CountableIdeal} {H Y : Oracle} (hH : Presented I H)
    (ρ : I ≃o I) (hr : RecursivePred Y (Graph ρ hH)) :
    ∃ e : ℕ, ∀ v, tableOracle Y e v = true ↔ Graph ρ hH v := by
  obtain ⟨d,hd⟩ := TableIndices.reduces_represents (graphOracle_reduces hH ρ hr)
  have hd' : TableIndices.Represents Y (IndexMatrix.machine (encode d)) (graphOracle hH ρ) := by
    simpa only [IndexMatrix.machine_encode] using hd
  refine ⟨encode d,fun v => ?_⟩
  rw [tableOracle_eq hd']
  simp [graphOracle]

theorem persistent_iff_oai {I : CountableIdeal} {A R : Oracle} (hA : Presented I A)
    (ρ : I ≃o I) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (hR : ∀ v, R v = true ↔ Graph ρ hA v) :
    Persistent I ρ ↔ Criterion A R := by
  constructor
  · intro hp H hc hi
    let J := decode H hc
    have hH : Presented J H := decoded_presentation H hc
    have hIJ : I.carrier ⊆ J.carrier := (includes_iff hA hH).mp hi
    obtain ⟨σ,he,hpσ⟩ := PersistentExtension.source_4_1_10 I J ρ hp hz hIJ (decoded_closed H hc)
    obtain ⟨e,hg⟩ := graph_program hH σ (source_4_1_8 σ hpσ (hIJ hz) hH).2
    refine ⟨e,(PersistenceCriterion.action_congr hg).mpr (action_of_automorphism hH σ),?_⟩
    intro i j n m hr hp hin
    exact ((compatible_iff hA hH hIJ ρ σ).mpr he) i j n m
      ((hR _).mp hr) ((hg _).mp hp) hin
  · intro hc x
    let J := JumpIdeal.generated (degree A ⊔ x)
    have hIJ : I.carrier ⊆ J.carrier := by
      intro y hy
      obtain ⟨n,rfl⟩ := (hA y).mp hy
      exact J.lower (le_trans (show degree (columns A n) ≤ degree A from
        CodingExtraction.column_projection_reduces A n) le_sup_left) (JumpIdeal.includes _)
    have hx : x ∈ J.carrier := J.lower le_sup_right (JumpIdeal.includes _)
    obtain ⟨H,hH⟩ := presentation_exists J
    have hj : JumpCode H := code_of_ideal hH (JumpIdeal.closed _)
    have hi : Includes A H := (includes_iff hA hH).mpr hIJ
    obtain ⟨e,ha,hcompat⟩ := hc H hj hi
    obtain ⟨σ,hσ⟩ := reconstruct hH ha
    refine ⟨J,hIJ,σ,hx,(compatible_iff hA hH hIJ ρ σ).mp ?_⟩
    intro i j n m hr hp hin
    exact hcompat i j n m ((hR _).mpr hr) ((hσ _).mpr hp) hin

end
end TuringRigidity.ArithmeticPersistence

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.ArithmeticPersistence.persistent_iff_oai := @OAI.TuringRigidity.ArithmeticPersistence.persistent_iff_oai
