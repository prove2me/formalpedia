-- Prove2me | solution 1 for OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:09:03.808357+00:00
-- url     : https://prove2.me/submissions/7b24114e-9ae3-4f67-a01f-ddca63ba05f9

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_LocalUnary_localized_copy

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

theorem reduces_iff_represents (A Y : Oracle) :
    Reduces A Y ↔ ∃ d : Nat.Partrec.Code, Represents Y d A :=
  ⟨reduces_represents, fun ⟨_, h⟩ => represents_reduces h⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_JumpProperties
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

end TuringRigidity.OracleJump

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

end
end TuringRigidity.PersistentLocality

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

theorem omega_exists (P : ZFSet.{u} → Prop) :
    (∃ x ∈ ZFSet.omega, P x) ↔ ∃ n, P (natSet n) := by
  constructor
  · rintro ⟨x,hx,hP⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨n,hP⟩
  · rintro ⟨n,hP⟩
    exact ⟨_,(mem_omega _).mpr ⟨n,rfl⟩,hP⟩

theorem real_comprehension (M : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hI : Infinity M)
    (A : Oracle) (φ : Formula) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hφ : ∀ n, φ.Eval (cons (natSet n) e) ↔ A n = true) : A ∈ reals M := by
  have h := sep_mem M hM hS φ e he (omega_mem M hM hS hI)
  have eq : ZFSet.sep (fun x => φ.Eval (cons x e)) ZFSet.omega = realSet A := by
    apply ZFSet.ext
    intro x
    by_cases hx : x ∈ ZFSet.omega
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      simp only [ZFSet.mem_sep,hx,true_and,nat_mem_realSet,hφ]
    · simp only [ZFSet.mem_sep,hx,false_and]
      exact iff_false_intro (fun h => hx (realSet_subset A h)) |>.symm
  change realSet A ∈ M
  exact eq ▸ h

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

theorem jump_mem (C : Context M) {A : Oracle} (hA : A ∈ reals M) :
    OracleJump.jump A ∈ reals M := by
  have h : Arith (fun O n => OracleJump.jump (O 0) n = true) :=
    query_at (jump_arith (parameter_arith 0)) (Primrec.const 0) Primrec.id
  exact arithmetic_comprehension C h (fun _ => A) (fun _ => hA) _ (fun _ => Iff.rfl)

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ExtensionArithmeticRepresentative
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ExtensionArithmeticRepresentative
open OracleJump IdealInterpretation IdealLocality PersistentRestrictions PersistentLocality

theorem literal_join_program {I : DegreeIdeal} (σ : I ≃o I) (z x : I)
    (hz : z.val = degree (jump FixedArithmetic.zero)) (A R : Oracle)
    (hA : degree A = x.val) (hR : degree R = (σ.symm z).val) :
    ∃ X : Oracle, degree X = (σ x).val ∧ Reduces X (iterate (join A R) 5) ∧
      ∃ e : OracleCode,
        OracleCode.eval (oracleFunction (iterate (join A R) 5)) e = oracleFunction X := by
  obtain ⟨X,Y,hX,hY,hXY⟩ := image_arithmetic σ z hz x
  have hjoin : degree Y = degree (join A R) := by
    change degree Y = degree A ⊔ degree R
    rw [hA,hR]; exact hY
  have hred : Reduces X (iterate (join A R) 5) :=
    TuringReducible.trans hXY (iterate_mono ((degree_eq_iff _ _).mp hjoin).1 5)
  exact ⟨X,hX,hred,OracleCode.exists_code (RecursiveIn.iff_nat.mp hred)⟩

theorem extension_literal_join_program (I J : CountableIdeal)
    (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
    (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (A R : Oracle) (hA : degree A ∈ J.carrier)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val) :
    ∃ X : Oracle, degree X = (σ ⟨degree A,hA⟩).val ∧ Reduces X (iterate (join A R) 5) ∧
      ∃ e : OracleCode,
        OracleCode.eval (oracleFunction (iterate (join A R) 5)) e = oracleFunction X := by
  let z : I := ⟨degree (jump FixedArithmetic.zero),hz⟩
  let zJ : ideal J := ⟨z.val,hIJ z.property⟩
  let x : ideal J := ⟨degree A,hA⟩
  have hpre : degree R = ((lift σ).symm zJ).val :=
    hR.trans (extends_symm he z).symm
  exact literal_join_program (lift σ) zJ x rfl A R rfl hpre

end TuringRigidity.ExtensionArithmeticRepresentative

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
universe u
noncomputable section

theorem natSet_successor_eq (n m : ℕ) :
    natSet.{u} n = insert (natSet m) (natSet m) ↔ n = m+1 := by
  change natSet n = natSet (m+1) ↔ n = m+1
  exact natSet_injective.eq_iff

theorem join_true_iff (A B : Oracle) (v : ℕ) : join A B v = true ↔
    ∃ n, (v = 2*n ∧ A n = true) ∨ (v = 2*n+1 ∧ B n = true) := by
  constructor
  · intro h
    have hv : v = 2*(v/2) ∨ v = 2*(v/2)+1 := by omega
    refine ⟨v/2,?_⟩
    rcases hv with he|he
    · exact Or.inl ⟨he,(join_even A B (v/2)).symm.trans ((congrArg (join A B) he).symm.trans h)⟩
    · exact Or.inr ⟨he,(join_odd A B (v/2)).symm.trans ((congrArg (join A B) he).symm.trans h)⟩
  · rintro ⟨n,⟨rfl,hA⟩|⟨rfl,hB⟩⟩
    · exact (join_even A B n).trans hA
    · exact (join_odd A B n).trans hB

theorem eval_joinFormula (A B : Oracle) (v : ℕ) :
    joinFormula.Eval (cons (natSet.{u} v) (cons ZFSet.omega (cons (realSet A)
      (cons (realSet B) (cons additionSet (fun _ => pairNumbers)))))) ↔ join A B v = true := by
  simp only [joinFormula,Formula.Eval,Formula.eval_disj,eval_tripleFormula,
    Formula.eval_successor,cons_zero,cons_succ]
  simp_rw [omega_exists]
  simp only [natPair_mem,true_and,addition_code,natSet_successor_eq,nat_mem_realSet]
  rw [join_true_iff]
  simp [two_mul]

theorem join_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    {A B : Oracle} (hA : A ∈ reals M) (hB : B ∈ reals M) : join A B ∈ reals M := by
  have hω := omega_mem M hM hS hI
  have hd : pairNumbers.{u} ∈ M := product_mem M hM hP hU hPow hS hω hω
  have ha := additionSet_mem M hM hP hU hPow hS hI
  let e := cons ZFSet.omega (cons (realSet A) (cons (realSet B)
    (cons additionSet (fun _ => pairNumbers))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|i <;> simp only [e,cons_zero,cons_succ]
    · exact hω
    · exact hA
    · exact hB
    · exact ha
    · exact hd
  exact real_comprehension M hM hS hI (join A B) joinFormula e he (eval_joinFormula A B)

end
end TuringRigidity.SetModelArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ProjectedArithmeticOutputName
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
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

theorem representative_in_model_oai (N : ZFSet.{0}) (hN : Transitive N) (hTN : SourceT N)
    (I J : CountableIdeal) (hIJ : I.carrier ⊆ J.carrier) (ρ : I ≃o I) (σ : J ≃o J)
    (he : Extends hIJ ρ σ) (hz : degree (jump FixedArithmetic.zero) ∈ I.carrier)
    (A R : Oracle) (hA : degree A ∈ J.carrier)
    (hR : degree R = (ρ.symm ⟨degree (jump FixedArithmetic.zero),hz⟩).val)
    (hAN : A ∈ modelReals N) (hRN : R ∈ modelReals N) :
    ∃ X : Oracle, X ∈ modelReals N ∧ degree X = (σ ⟨degree A,hA⟩).val ∧
      Reduces X (iterate (join A R) 5) ∧ ∃ e : OracleCode,
        OracleCode.eval (oracleFunction (iterate (join A R) 5)) e = oracleFunction X := by
  obtain ⟨X,hX,hred,hcode⟩ := extension_literal_join_program I J hIJ ρ σ he hz A R hA hR
  have hj : join A R ∈ SetModelReals.reals N := SetModelArithmetic.join_mem N hN
    hTN.pairing hTN.union hTN.powerSet hTN.separation.finitePrefix.bounded hTN.infinity hAN hRN
  have hi (n : ℕ) : iterate (join A R) n ∈ SetModelReals.reals N := by
    induction n with
    | zero => exact hj
    | succ n ih => exact SetModelSyntax.jump_mem (ArithmeticTree.sourceContext N hN hTN) ih
  exact ⟨X,SetModelSyntax.lower_mem (ArithmeticTree.sourceContext N hN hTN) (hi 5) hred,
    hX,hred,hcode⟩

end TuringRigidity.ProjectedArithmeticOutputName

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model_oai := @OAI.TuringRigidity.ProjectedArithmeticOutputName.representative_in_model_oai
