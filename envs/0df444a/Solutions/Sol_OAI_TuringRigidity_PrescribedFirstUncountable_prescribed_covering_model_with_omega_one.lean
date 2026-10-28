-- Prove2me | solution 1 for OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:29:27.394752+00:00
-- url     : https://prove2.me/submissions/be0143f7-c702-4bae-811c-7e7e65ad3473

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_ArithmeticTree_setGenericallyPersistent_iff
import Theorems.Thm_OAI_TuringRigidity_LocalUnary_localized_copy
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_ground_idealSet_mem_relativeModel
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_persistent_modelIdeal_graph_mem_relativeModel

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_PersistentRestrictions
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PersistentRestrictions
open Set

theorem subset_hullSet (π : Degree ≃o Degree) (S : Set Degree) : S ⊆ hullSet π S := by
  intro a ha
  exact Set.mem_iUnion.mpr ⟨0, Or.inr ha⟩

theorem hullSet_forward (π : Degree ≃o Degree) (S : Set Degree)
    {a : Degree} (ha : a ∈ hullSet π S) : π a ∈ hullSet π S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inl ⟨a, hn, rfl⟩)⟩

theorem hullSet_backward (π : Degree ≃o Degree) (S : Set Degree)
    {a : Degree} (ha : a ∈ hullSet π S) : π.symm a ∈ hullSet π S := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr (Or.inr (Or.inl ⟨a, hn, rfl⟩))⟩

theorem countable_invariant_hull (π : Degree ≃o Degree) (S : Set Degree)
    (hS : S.Countable) : ∃ J : CountableIdeal, S ⊆ J.carrier ∧
      (∀ a ∈ J.carrier, π a ∈ J.carrier) ∧
      (∀ a ∈ J.carrier, π.symm a ∈ J.carrier) := by
  exact ⟨invariantHull π S hS, subset_hullSet π S,
    fun _ ha => hullSet_forward π S ha, fun _ ha => hullSet_backward π S ha⟩

theorem persistent_of_global_restriction (π : Degree ≃o Degree)
    (I : CountableIdeal) (ρ : I ≃o I) (hρ : RestrictsTo π I ρ) : Persistent I ρ := by
  intro x
  obtain ⟨J, hS, hf, hb⟩ := countable_invariant_hull π (insert x I.carrier)
    (I.countable.insert x)
  let hIJ : I.carrier ⊆ J.carrier := fun _ ha => hS (Or.inr ha)
  refine ⟨J, hIJ, restrict π J hf hb, hS (Or.inl rfl), ?_⟩
  intro a
  exact hρ a

end TuringRigidity.PersistentRestrictions

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory
universe u

namespace SentenceForm

theorem finite_support (p : SentenceForm) (D : Set ZFSet.{u})
    (e f : ℕ → ZFSet.{u}) (h : ∀ i, i < p.bound → e i = f i) :
    p.Sat D e ↔ p.Sat D f := by
  induction p generalizing e f with
  | equal i j =>
    have hi := h i (by simp only [bound]; omega)
    have hj := h j (by simp only [bound]; omega)
    simp only [Sat,hi,hj]
  | member i j =>
    have hi := h i (by simp only [bound]; omega)
    have hj := h j (by simp only [bound]; omega)
    simp only [Sat,hi,hj]
  | conj p q ihp ihq =>
    exact and_congr (ihp e f (fun i hi => h i (by simp only [bound]; omega)))
      (ihq e f (fun i hi => h i (by simp only [bound]; omega)))
  | neg p ih => exact not_congr (ih e f h)
  | ex p ih =>
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply ih
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact h i (by simp only [bound] at h ⊢; omega)

theorem sat_rename (p : SentenceForm) (v : ℕ → ℕ)
    (D : Set ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (p.rename v).Sat D e ↔ p.Sat D (fun i => e (v i)) := by
  induction p generalizing v e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp v e) (ihq v e)
  | neg p ih => exact not_congr (ih v e)
  | ex p ih =>
    apply exists_congr; intro x
    apply and_congr_right; intro _
    have he : (fun i => cons x e (match i with | 0 => 0 | j+1 => v j+1)) =
        cons x (fun i => e (v i)) := by funext i; cases i <;> rfl
    exact (ih _ _).trans (he ▸ Iff.rfl)
end SentenceForm

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CountableElementaryHull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory
universe u

theorem prefix_agrees (n : ℕ) (e : ℕ → ZFSet.{u}) :
    ∀ i, i < n → listEnv (envPrefix n e) i = e i := by
  induction n generalizing e with
  | zero => omega
  | succ n ih =>
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact ih (fun j => e (j+1)) i (by omega)

theorem prefix_members (n : ℕ) (e : ℕ → ZFSet.{u}) (D : Set ZFSet.{u})
    (he : ∀ i, e i ∈ D) : ∀ x ∈ envPrefix n e, x ∈ D := by
  induction n generalizing e with
  | zero => simp [envPrefix]
  | succ n ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl|hx
    · exact he 0
    · exact ih _ (fun i => he (i+1)) x hx

theorem witness_spec (p : SentenceForm) (xs : List ZFSet.{u})
    (h : ∃ x : ZFSet.{u}, p.Sat Set.univ (cons x (listEnv xs))) :
    p.Sat Set.univ (cons (witness p xs) (listEnv xs)) := by
  classical
  simp only [witness,dite_eq_left h]
  exact Classical.choose_spec h

theorem stage_mono (a : ℕ → ZFSet.{u}) : Monotone (stage a) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  exact Or.inl hx

theorem parameter_mem (a : ℕ → ZFSet.{u}) (n : ℕ) : a n ∈ hull a :=
  Set.mem_iUnion.mpr ⟨0,⟨n,rfl⟩⟩

theorem list_in_stage (a : ℕ → ZFSet.{u}) (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ hull a) : ∃ n, ∀ x ∈ xs, x ∈ stage a n := by
  induction xs with
  | nil => exact ⟨0,by simp⟩
  | cons x xs ih =>
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp (hxs x (by simp))
    obtain ⟨m,hm⟩ := ih (fun y hy => hxs y (by simp [hy]))
    refine ⟨max n m,?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl|hy
    · exact stage_mono a (Nat.le_max_left n m) hn
    · exact stage_mono a (Nat.le_max_right n m) (hm y hy)

theorem witness_mem (a : ℕ → ZFSet.{u}) (p : SentenceForm) (xs : List ZFSet.{u})
    (hxs : ∀ x ∈ xs, x ∈ hull a) : witness p xs ∈ hull a := by
  obtain ⟨n,hn⟩ := list_in_stage a xs hxs
  exact Set.mem_iUnion.mpr ⟨n+1,Or.inr ⟨p,xs,hn,rfl⟩⟩

theorem hull_elementary (a : ℕ → ZFSet.{u}) : Elementary (hull a) := by
  intro p
  induction p with
  | equal => intros; rfl
  | member => intros; rfl
  | conj p q ihp ihq => intro e he; exact and_congr (ihp e he) (ihq e he)
  | neg p ih => intro e he; exact not_congr (ih e he)
  | ex p ih =>
    intro e he
    constructor
    · rintro ⟨x,hx,hp⟩
      exact ⟨x,Set.mem_univ x,(ih (cons x e) (by intro i; cases i <;> simp [cons,he,hx])).mp hp⟩
    · rintro ⟨x,_,hp⟩
      let xs := envPrefix p.bound e
      have eq (y : ZFSet.{u}) : p.Sat Set.univ (cons y (listEnv xs)) ↔
          p.Sat Set.univ (cons y e) := by
        apply p.finite_support
        intro i hi
        cases i with
        | zero => rfl
        | succ i => exact prefix_agrees p.bound e i (by omega)
      have hw := witness_mem a p xs (prefix_members p.bound e (hull a) he)
      have hs := (eq _).mp (witness_spec p xs ⟨x,(eq x).mpr hp⟩)
      exact ⟨_,hw,(ih (cons (witness p xs) e)
        (by intro i; cases i <;> simp [cons,he,hw])).mpr hs⟩

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalInfinity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

theorem omega_transitive : Transitive ZFSet.omega.{u} := by
  intro x hx y hy
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  obtain ⟨i,_,rfl⟩ := (mem_natSet n y).mp hy
  exact (mem_omega _).mpr ⟨i,rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

namespace ChoiceCode
open Formula

theorem eval_graph (a f : ℕ) (e : ℕ → ZFSet.{u}) :
    (graph a f).Eval e ↔ ChoiceGraph (e a) (e f) := by
  simp only [graph,ChoiceGraph,Formula.Eval,eval_allMem,eval_orderedPair,
    eval_pairMem,eval_imp,cons_zero,cons_succ]
end ChoiceCode

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryCollapse
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

theorem mem_hullSet (a : ℕ → ZFSet.{u}) (x : ZFSet.{u}) : x ∈ hullSet a ↔ x ∈ hull a := by
  classical
  simp only [hullSet,ZFSet.mem_range]
  exact ⟨fun ⟨y,hy⟩ => hy ▸ y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩

instance hullSet_countable (a : ℕ → ZFSet.{u}) : Countable (Conditions (hullSet a)) := by
  let : Countable (hull a) := (hull_countable a).to_subtype
  exact Function.Injective.countable (f := fun x : Conditions (hullSet a) =>
    (⟨label _ x,(mem_hullSet a _).mp (label_mem _ x)⟩ : hull a))
    (fun x y h => label_injective (hullSet a) (congrArg (fun z : hull a => z.val) h))

theorem hullSet_extensional (a : ℕ → ZFSet.{u}) : StructureExtensional (hullSet a) := by
  intro x hx y hy he
  let e := cons x (fun _ => y)
  have hen : ∀ i, e i ∈ hull a := by
    intro i; cases i <;> simp only [e,cons_zero,cons_succ]
    · exact (mem_hullSet a x).mp hx
    · exact (mem_hullSet a y).mp hy
  let p := SentenceForm.all (SentenceForm.iff (.member 0 1) (.member 0 2))
  have hs : p.Sat (hull a) e := by
    simp only [p,SentenceForm.sat_all,SentenceForm.sat_iff,SentenceForm.Sat,
      cons_zero,cons_succ,e]
    exact fun z hz => he z ((mem_hullSet a z).mpr hz)
  have ht := (hull_elementary a p e hen).mp hs
  simp only [p,SentenceForm.sat_all,SentenceForm.sat_iff,SentenceForm.Sat,
    cons_zero,cons_succ,e,Set.mem_univ,forall_const] at ht
  exact ZFSet.ext ht

theorem mem_collapsed (d z : ZFSet.{u}) :
    z ∈ collapsed d ↔ ∃ x ∈ d, z = structureMap d x := by
  rw [collapsed,ZFSet.mem_range]
  constructor
  · rintro ⟨x,rfl⟩; exact ⟨_,label_mem _ x,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨i,rfl⟩ := label_surjective d hx
    exact ⟨i,rfl⟩

theorem collapsed_transitive (d : ZFSet.{u}) : Transitive (collapsed d) := by
  intro x hx y hy
  obtain ⟨z,_,rfl⟩ := (mem_collapsed d x).mp hx
  obtain ⟨w,hw,_,rfl⟩ := (mem_value d (membershipRelation d) _ z y).mp hy
  exact (mem_collapsed d _).mpr ⟨w,hw,rfl⟩

theorem collapse_injective (d : ZFSet.{u}) (he : StructureExtensional d)
    (x : ZFSet.{u}) (hx : x ∈ d) (y : ZFSet.{u}) (hy : y ∈ d)
    (h : structureMap d x = structureMap d y) : x = y :=
  value_injective (membershipRelation_wellFounded d) (membershipRelation_extensional he) x hx y hy h

theorem collapse_membership (d : ZFSet.{u}) (he : StructureExtensional d)
    (x : ZFSet.{u}) (hx : x ∈ d) (y : ZFSet.{u}) (hy : y ∈ d) :
    structureMap d x ∈ structureMap d y ↔ x ∈ y := by
  rw [structureMap,value_mem_iff (membershipRelation_wellFounded d)
    (membershipRelation_extensional he) hx,membershipRelation_pair]
  simp only [hx,hy,true_and]

theorem collapse_fixed (d x : ZFSet.{u}) (hx : x ∈ d)
    (h : ∀ y ∈ x, y ∈ d ∧ structureMap d y = y) : structureMap d x = x := by
  apply ZFSet.ext; intro y
  rw [structureMap,mem_value]
  constructor
  · rintro ⟨z,_,hz,hy⟩
    have hzx := ((membershipRelation_pair d z x).mp hz).2.2
    change y = structureMap d z at hy
    rw [(h z hzx).2] at hy
    exact hy ▸ hzx
  · intro hy
    refine ⟨y,(h y hy).1,(membershipRelation_pair d y x).mpr ⟨(h y hy).1,hx,hy⟩,?_⟩
    exact (h y hy).2.symm

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementarySatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

theorem SentenceForm.collapse_sat (p : SentenceForm) (d : ZFSet.{u})
    (hd : StructureExtensional d) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ d) :
    p.Sat (d : Set ZFSet) e ↔ p.Sat (collapsed d : Set ZFSet) (fun i => structureMap d (e i)) := by
  induction p generalizing e with
  | equal i j => exact ⟨congrArg (structureMap d),collapse_injective d hd _ (he i) _ (he j)⟩
  | member i j => exact (collapse_membership d hd _ (he i) _ (he j)).symm
  | conj p q ihp ihq => exact and_congr (ihp e he) (ihq e he)
  | neg p ih => exact not_congr (ih e he)
  | ex p ih =>
    have hen (x : ZFSet.{u}) (hx : x ∈ d) : ∀ i, cons x e i ∈ d := by
      intro i; cases i <;> simp [cons,he,hx]
    constructor
    · rintro ⟨x,hx,hp⟩
      refine ⟨_,(mem_collapsed d _).mpr ⟨x,hx,rfl⟩,?_⟩
      have h := (ih (cons x e) (hen x hx)).mp hp
      rwa [map_cons] at h
    · rintro ⟨y,hy,hp⟩
      obtain ⟨x,hx,rfl⟩ := (mem_collapsed d y).mp hy
      refine ⟨x,hx,(ih (cons x e) (hen x hx)).mpr ?_⟩
      rwa [map_cons]

theorem collapsed_hull_valid (a : ℕ → ZFSet.{u}) : Valid (collapsed (hullSet a)) := by
  intro p hp e he
  choose f hf heq using fun i => (mem_collapsed (hullSet a) (e i)).mp (he i)
  have hfe : (fun i => structureMap (hullSet a) (f i)) = e := by
    funext i; exact (heq i).symm
  have hh : (hullSet a : Set ZFSet) = hull a := by ext x; exact mem_hullSet a x
  have hs : p.Sat (hullSet a : Set ZFSet) f := by
    rw [hh]
    exact (hull_elementary a p f (fun i => (mem_hullSet a _).mp (hf i))).mpr (hp f)
  have ht := (p.collapse_sat (hullSet a) (hullSet_extensional a) f hf).mp hs
  rwa [hfe] at ht

theorem bounded_sat (p : Formula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromBounded p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp e) (ihq e)
  | neg p ih => exact not_congr (ih e)
  | existsMem i p ih =>
    simp only [fromBounded,SentenceForm.Sat,Formula.Realize,cons_zero,cons_succ]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => and_congr_right (fun _ => ih (cons x e)))

theorem bounded_univ (p : Formula) (e : ℕ → ZFSet.{u}) :
    (fromBounded p).Sat Set.univ e ↔ p.Eval e := by
  induction p generalizing e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp e) (ihq e)
  | neg p ih => exact not_congr (ih e)
  | existsMem i p ih =>
    simp only [fromBounded,SentenceForm.Sat,Formula.Eval,cons_zero,cons_succ,Set.mem_univ,true_and]
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

theorem sigma_sat (p : SigmaFormula) (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (fromSigma p).Sat (M : Set ZFSet) e ↔ p.Realize M e := by
  induction p generalizing e with
  | bounded p => exact bounded_sat p M e
  | existsSet p ih =>
    apply exists_congr; intro x
    exact and_congr_right (fun _ => ih (cons x e))

end TuringRigidity.ElementaryModel

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel
universe u

theorem relativeModel_subset (M R : ZFSet.{u}) : relativeModel M R ⊆ M :=
  fun _ hx => (ZFSet.mem_sep.mp hx).1

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GlobalJumpRestriction
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.PersistentLocality
open IdealInterpretation IdealLocality PersistentRestrictions OracleJump

theorem global_jump_restriction (π : Degree ≃o Degree) (J : CountableIdeal)
    (hjump : JumpClosed (ideal J))
    (himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ J.carrier) :
    ∃ ρ : J ≃o J, RestrictsTo π J ρ ∧ Persistent J ρ := by
  let τ : fullIdeal ≃o fullIdeal := fullEquiv.symm.trans (π.trans fullEquiv)
  let z : fullIdeal := fullEquiv (degree (jump FixedArithmetic.zero))
  obtain ⟨σ,hσ⟩ := source_4_1_4 τ z rfl
    (J := ideal J) (fun _ _ => Set.mem_univ _) hjump himages
  let ρ := unlift σ
  have hρ : RestrictsTo π J ρ := by
    intro x
    exact (hσ ⟨x.val,x.property⟩).symm
  exact ⟨ρ,hρ,persistent_of_global_restriction π J ρ hρ⟩

end TuringRigidity.PersistentLocality

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementaryAxioms
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel SentenceForm
universe u

theorem Valid.pairing {M : ZFSet.{u}} (hv : Valid M) : Pairing M := by
  intro a ha b hb
  let p := ex (all (iff (.member 0 1) (disj (.equal 0 2) (.equal 0 3))))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only [p,Sat,sat_all,sat_iff,sat_disj,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ⟨{e 0,e 1},fun x => ZFSet.mem_pair⟩
  have h := hv p hp (cons a (fun _ => b)) (by intro i; cases i <;> assumption)
  simpa only [p,Sat,sat_all,sat_iff,sat_disj,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem Valid.union {M : ZFSet.{u}} (hv : Valid M) : BoundedSetTheory.Union M := by
  intro a ha
  let p := ex (all (iff (.member 0 1) (ex (.conj (.member 0 3) (.member 1 0)))))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only [p,Sat,sat_all,sat_iff,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ⟨ZFSet.sUnion (e 0),fun x => ZFSet.mem_sUnion⟩
  have h := hv p hp (fun _ => a) (fun _ => ha)
  simpa only [p,Sat,sat_all,sat_iff,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem Valid.powerSet {M : ZFSet.{u}} (hv : Valid M) : PowerSet M := by
  intro a ha
  let p := ex (all (iff (.member 0 1) (all (imp (.member 0 1) (.member 0 3)))))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only [p,Sat,sat_all,sat_iff,sat_imp,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ⟨ZFSet.powerset (e 0),fun x => ZFSet.mem_powerset⟩
  have h := hv p hp (fun _ => a) (fun _ => ha)
  simpa only [p,Sat,sat_all,sat_iff,sat_imp,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem Valid.infinity {M : ZFSet.{u}} (hv : Valid M) (hne : ∃ a, a ∈ M) : Infinity M := by
  obtain ⟨a,ha⟩ := hne
  let p := ex (.conj (ex (.conj (.member 0 1) (all (.neg (.member 0 1)))))
    (all (imp (.member 0 1) (ex (.conj (.member 0 2)
      (all (iff (.member 0 1) (disj (.equal 0 2) (.member 0 2)))))))))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only [p,Sat,sat_all,sat_iff,sat_imp,sat_disj,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    refine ⟨ZFSet.omega,⟨∅,ZFSet.omega_zero,ZFSet.notMem_empty⟩,?_⟩
    intro x hx
    exact ⟨insert x x,ZFSet.omega_succ hx,fun z => ZFSet.mem_insert_iff⟩
  have h := hv p hp (fun _ => a) (fun _ => ha)
  simpa only [Infinity,p,Sat,sat_all,sat_iff,sat_imp,sat_disj,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem ambient_choice_graph (a : ZFSet.{u}) (hn : ∀ x ∈ a, ∃ y, y ∈ x) :
    ∃ f : ZFSet.{u}, ChoiceGraph a f := by
  classical
  let pick (x : Conditions a) := Classical.choose (hn (label a x) (label_mem a x))
  have hp (x : Conditions a) : pick x ∈ label a x := Classical.choose_spec (hn _ (label_mem a x))
  let f := ZFSet.range (fun x : Conditions a => ZFSet.pair (label a x) (pick x))
  refine ⟨f,?_,?_⟩
  · intro z hz
    obtain ⟨x,rfl⟩ := ZFSet.mem_range.mp hz
    exact ⟨_,label_mem _ x,_,hp x,rfl⟩
  · intro x hx
    obtain ⟨i,rfl⟩ := label_surjective a hx
    refine ⟨pick i,hp i,ZFSet.mem_range_self i,?_⟩
    intro z _ hz
    obtain ⟨j,hj⟩ := ZFSet.mem_range.mp hz
    obtain ⟨he,hz⟩ := ZFSet.pair_inj.mp hj
    have hj : j = i := label_injective a he
    exact hz.symm.trans (congrArg pick hj)

theorem Valid.choice {M : ZFSet.{u}} (hv : Valid M) (hM : Transitive M) : Choice M := by
  intro a ha hn
  let p := imp (all (imp (.member 0 1) (ex (.member 0 1))))
    (ex (fromBounded (ChoiceCode.graph 1 0)))
  have hp : ∀ e : ℕ → ZFSet.{u}, p.Sat Set.univ e := by
    intro e
    simp only [p,sat_imp,sat_all,Sat,bounded_univ,ChoiceCode.eval_graph,
      cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ambient_choice_graph (e 0)
  have h := hv p hp (fun _ => a) (fun _ => ha)
  simp only [p,sat_imp,sat_all,Sat,bounded_sat,cons_zero,cons_succ] at h
  obtain ⟨f,hf,hfg⟩ := h (fun x hx hxa => by
    obtain ⟨y,hy⟩ := hn x hxa
    exact ⟨y,hM x hx y hy,hy⟩)
  refine ⟨f,hf,?_⟩
  have hb := (Formula.absolute (ChoiceCode.graph 1 0) M hM (cons f (fun _ => a))
    (by intro i; cases i <;> assumption)).mp hfg
  exact (ChoiceCode.eval_graph 1 0 _).mp hb

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementarySchemas
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel SentenceForm
universe u

private theorem sat_sepMap (q : SentenceForm) (D : Set ZFSet.{u})
    (x b a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (q.rename sepMap).Sat D (cons x (cons b (cons a e))) ↔ q.Sat D (cons x e) := by
  rw [sat_rename]
  have he : (fun i => cons x (cons b (cons a e)) (sepMap i)) = cons x e := by
    funext i; cases i <;> rfl
  rw [he]

private theorem sat_relationMap (q : SentenceForm) (D : Set ZFSet.{u})
    (y x a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (q.rename relationMap).Sat D (cons y (cons x (cons a e))) ↔ q.Sat D (cons y (cons x e)) := by
  rw [sat_rename]
  have he : (fun i => cons y (cons x (cons a e)) (relationMap i)) = cons y (cons x e) := by
    funext i; rcases i with _|_|i <;> rfl
  rw [he]

private theorem sat_uniqueMap (q : SentenceForm) (D : Set ZFSet.{u})
    (z y x a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (q.rename uniqueMap).Sat D (cons z (cons y (cons x (cons a e)))) ↔ q.Sat D (cons z (cons x e)) := by
  rw [sat_rename]
  have he : (fun i => cons z (cons y (cons x (cons a e))) (uniqueMap i)) = cons z (cons x e) := by
    funext i; rcases i with _|_|i <;> rfl
  rw [he]

private theorem sat_imageMap (q : SentenceForm) (D : Set ZFSet.{u})
    (x y b a : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (q.rename imageMap).Sat D (cons x (cons y (cons b (cons a e)))) ↔ q.Sat D (cons y (cons x e)) := by
  rw [sat_rename]
  have he : (fun i => cons x (cons y (cons b (cons a e))) (imageMap i)) = cons y (cons x e) := by
    funext i; rcases i with _|_|i <;> rfl
  rw [he]

theorem Valid.separate {M : ZFSet.{u}} (hv : Valid M) (q : SentenceForm)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a : ZFSet.{u}) (ha : a ∈ M) :
    ∃ b ∈ M, ∀ x ∈ M, x ∈ b ↔ x ∈ a ∧ q.Sat (M : Set ZFSet) (cons x e) := by
  let p := ex (all (iff (.member 0 1) (.conj (.member 0 2) (q.rename sepMap))))
  have hp : ∀ v : ℕ → ZFSet.{u}, p.Sat Set.univ v := by
    intro v
    let e' := fun i => v (i+1)
    have hv' : v = cons (v 0) e' := by funext i; cases i <;> rfl
    rw [hv']
    simp only [p,Sat,sat_all,sat_iff,sat_sepMap,cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ⟨ZFSet.sep (fun x => q.Sat Set.univ (cons x e')) (v 0),fun x => ZFSet.mem_sep⟩
  have h := hv p hp (cons a e) (by intro i; cases i <;> simp [cons,he,ha])
  simpa only [p,Sat,sat_all,sat_iff,sat_sepMap,cons_zero,cons_succ,SetLike.mem_coe] using h

theorem ambient_image (a : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (ht : ∀ x ∈ a, ∃ y, R x y ∧ ∀ z, R x z → z = y) :
    ∃ b : ZFSet.{u}, ∀ y, y ∈ b ↔ ∃ x ∈ a, R x y := by
  classical
  let f (i : Conditions a) := Classical.choose (ht (label a i) (label_mem a i))
  have hf (i : Conditions a) : R (label a i) (f i) ∧ ∀ z, R (label a i) z → z = f i :=
    Classical.choose_spec (ht _ (label_mem a i))
  refine ⟨ZFSet.range f,?_⟩
  intro y; rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i,rfl⟩; exact ⟨_,label_mem a i,(hf i).1⟩
  · rintro ⟨x,hx,hr⟩
    obtain ⟨i,rfl⟩ := label_surjective a hx
    exact ⟨i,((hf i).2 y hr).symm⟩

theorem Valid.replace {M : ZFSet.{u}} (hv : Valid M) (hM : Transitive M) (q : SentenceForm)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a : ZFSet.{u}) (ha : a ∈ M)
    (ht : ∀ x ∈ a, ∃ y ∈ M, q.Sat (M : Set ZFSet) (cons y (cons x e)) ∧
      ∀ z ∈ M, q.Sat (M : Set ZFSet) (cons z (cons x e)) → z = y) :
    ∃ b ∈ M, ∀ y ∈ M, y ∈ b ↔ ∃ x ∈ a, q.Sat (M : Set ZFSet) (cons y (cons x e)) := by
  let p := imp
    (all (imp (.member 0 1) (ex (.conj (q.rename relationMap)
      (all (imp (q.rename uniqueMap) (.equal 0 1)))))))
    (ex (all (iff (.member 0 1) (ex (.conj (.member 0 3) (q.rename imageMap))))))
  have hp : ∀ v : ℕ → ZFSet.{u}, p.Sat Set.univ v := by
    intro v
    let e' := fun i => v (i+1)
    have hv' : v = cons (v 0) e' := by funext i; cases i <;> rfl
    rw [hv']
    simp only [p,Sat,sat_all,sat_iff,sat_imp,sat_relationMap,sat_uniqueMap,sat_imageMap,
      cons_zero,cons_succ,Set.mem_univ,true_and,forall_const]
    exact ambient_image (v 0) (fun x y => q.Sat Set.univ (cons y (cons x e')))
  have h := hv p hp (cons a e) (by intro i; cases i <;> simp [cons,he,ha])
  simp only [p,Sat,sat_all,sat_iff,sat_imp,sat_relationMap,sat_uniqueMap,sat_imageMap,
    cons_zero,cons_succ] at h
  obtain ⟨b,hb,hbdef⟩ := h (fun x _ hx => ht x hx)
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [hbdef y hy]
  exact ⟨fun ⟨x,_,hx,hr⟩ => ⟨x,hx,hr⟩,fun ⟨x,hx,hr⟩ => ⟨x,hM a ha x hx,hx,hr⟩⟩

theorem Valid.sigmaSeparation {M : ZFSet.{u}} (hv : Valid M) : SigmaSeparation M := by
  intro p e he a ha
  obtain ⟨b,hb,h⟩ := hv.separate (fromSigma p) e he a ha
  exact ⟨b,hb,fun x hx => (h x hx).trans (and_congr_right (fun _ => sigma_sat p M _))⟩

theorem Valid.sigmaReplacement {M : ZFSet.{u}} (hv : Valid M) (hM : Transitive M) : SigmaReplacement M := by
  intro p e he a ha ht
  obtain ⟨b,hb,h⟩ := hv.replace hM (fromSigma p) e he a ha (by
    intro x hx
    obtain ⟨y,hy,hp,hu⟩ := ht x hx
    exact ⟨y,hy,(sigma_sat p M _).mpr hp,fun z hz hpz => hu z hz ((sigma_sat p M _).mp hpz)⟩)
  refine ⟨b,hb,?_⟩
  intro y hy
  rw [h y hy]
  apply exists_congr; intro x
  exact and_congr_right (fun _ => sigma_sat p M _)

theorem Valid.sourceT {M : ZFSet.{u}} (hv : Valid M) (hM : Transitive M)
    (hne : ∃ a, a ∈ M) : SourceT M :=
  sourceT_of_finite_schemas M hM hv.pairing hv.union hv.powerSet hv.sigmaSeparation
    (hv.sigmaReplacement hM) (hv.infinity hne) (hv.choice hM)

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_ParameterCoveringModels
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

theorem seed_naturals (A : ℕ → Oracle) (n : ℕ) : natSet.{u} n ∈ hullSet (realSeed A) := by
  apply (mem_hullSet _ _).mpr
  have h := parameter_mem (realSeed.{u} A) (Nat.pair 0 n)
  simpa [realSeed] using h

theorem seed_reals (A : ℕ → Oracle) (n : ℕ) : realCode.{u} (A n) ∈ hullSet (realSeed A) := by
  apply (mem_hullSet _ _).mpr
  have h := parameter_mem (realSeed.{u} A) (Nat.pair 1 n)
  simpa [realSeed] using h

theorem collapse_nat_fixed (A : ℕ → Oracle) (n : ℕ) :
    structureMap (hullSet (realSeed.{u} A)) (natSet n) = natSet n := by
  apply structureMap_fixed omega_transitive
  · intro z hz
    obtain ⟨i,rfl⟩ := (mem_omega z).mp hz
    exact seed_naturals A i
  · exact (mem_omega _).mpr ⟨n,rfl⟩

theorem collapse_real_fixed (A : ℕ → Oracle) (n : ℕ) :
    structureMap (hullSet (realSeed.{u} A)) (realCode (A n)) = realCode (A n) := by
  apply collapse_fixed _ _ (seed_reals A n)
  intro y hy
  obtain ⟨i,rfl⟩ := (mem_omega y).mp (realCode_subset (A n) hy)
  exact ⟨seed_naturals A i,collapse_nat_fixed A i⟩

theorem collapsed_hull_sourceT (a : ℕ → ZFSet.{u}) : SourceT (collapsed (hullSet a)) := by
  apply (collapsed_hull_valid a).sourceT (collapsed_transitive _)
  exact ⟨_,(mem_collapsed _ _).mpr ⟨a 0,(mem_hullSet a _).mpr (parameter_mem a 0),rfl⟩⟩

end TuringRigidity.ElementaryModel

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

theorem modelIdeal_jump (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M) :
    IdealLocality.JumpClosed (PersistentLocality.ideal (modelIdeal M hM hT)) := by
  rintro b ⟨A,hA,rfl⟩
  exact ⟨jump A,sourceT_real_jump M hM hT hA,rfl⟩

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedModelRestriction
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions ArithmeticTree
universe u

theorem prescribed_model_restriction (π : Degree ≃o Degree)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) :
    ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
      RestrictsTo π _ ρ ∧ Persistent _ ρ ∧
      automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
      SetGenericallyPersistent M _ ρ := by
  obtain ⟨ρ,hr,hp⟩ := PersistentLocality.global_jump_restriction π _
    (modelIdeal_jump M hM hT) himages
  have hd := persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hp
  have hI := relativeModel_subset M _ (ground_idealSet_mem_relativeModel M hM hT)
  have hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ (modelIdeal M hM hT).carrier :=
    ⟨_,sourceT_real_jump M hM hT (sourceT_zero_real M hM hT),rfl⟩
  exact ⟨ρ,hr,hp,hd,(setGenericallyPersistent_iff M hM hT _ hI ρ
    (relativeModel_subset M _ hd) hz).mpr hp⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedCoveringModel
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel RelationCollapse SetDegreeDecoding
open PersistentRestrictions ArithmeticTree
universe u

theorem prescribed_covering_model (π : Degree ≃o Degree) (A : ℕ → Oracle) :
    ∃ M : ZFSet.{u}, ∃ hM : Transitive M, ∃ hT : SourceT M,
      ∃ hcount : Countable (Conditions M),
        letI := hcount
        Valid M ∧ (∀ n, A n ∈ modelReals M) ∧
        (π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
          π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) ∧
        ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
          RestrictsTo π _ ρ ∧ Persistent _ ρ ∧
          automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
          SetGenericallyPersistent M _ ρ := by
  obtain ⟨B,hB⟩ := degree_surjective
    (π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)))
  let S : ℕ → Oracle | 0 => B | n+1 => A n
  let M := collapsed (hullSet (realSeed.{u} S))
  have hM : Transitive M := collapsed_transitive _
  have hT : SourceT M := collapsed_hull_sourceT _
  have hs (n : ℕ) : S n ∈ modelReals M :=
    (mem_collapsed _ _).mpr ⟨realCode (S n),seed_reals S n,(collapse_real_fixed S n).symm⟩
  have hi : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier :=
    ⟨B,hs 0,hB⟩
  exact ⟨M,hM,hT,inferInstance,collapsed_hull_valid _,fun n => hs (n+1),hi,
    prescribed_model_restriction π M hM hT hi⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalCountableOrdinals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCountableOrdinals
open TransitiveNameModel BoundedSetTheory InternalCountableClosure

theorem firstUncountable_below (M L : ZFSet.{0}) (hM : Transitive M)
    (hL : L ∈ M) (hord : L.IsOrdinal)
    (hunc : ¬ (L = ∅ ∨ InternallyCountable M L)) :
    ∃ K, FirstUncountable M K ∧ K ⊆ L := by
  classical
  have h : ∀ L : ZFSet.{0}, L ∈ M → L.IsOrdinal →
      ¬ (L = ∅ ∨ InternallyCountable M L) → ∃ K, FirstUncountable M K ∧ K ⊆ L := by
    intro L
    induction L using ZFSet.mem_wf.induction with
    | h L ih =>
      intro hLM ho hu
      by_cases hs : ∀ a ∈ L, a = ∅ ∨ InternallyCountable M a
      · exact ⟨L,⟨ho,hLM,hu,hs⟩,fun _ h => h⟩
      · push Not at hs
        obtain ⟨a,ha,hac⟩ := hs
        obtain ⟨K,hK,hKa⟩ := ih a ha (hM L hLM a ha) (ho.mem ha) (not_or.mpr hac)
        exact ⟨K,hK,fun x hx => ho.subset_of_mem ha (hKa hx)⟩
  exact h L hL hord hunc

end TuringRigidity.InternalCountableOrdinals

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalUncountableSentence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalUncountableSentence
open TransitiveNameModel BoundedSetTheory ElementaryModel

theorem ontoMatrix_spec (f ω A : ℕ) (e : ℕ → ZFSet.{0}) :
    (ontoMatrix f ω A).Eval e ↔ FunctionGraph (e ω) (e A) (e f) ∧
      ∀ x ∈ e A, ∃ n ∈ e ω, ZFSet.pair n x ∈ e f := by
  simp only [ontoMatrix,Formula.Eval,Formula.eval_functionGraph,Formula.eval_allMem,
    Formula.eval_pairMem,FunctionGraph,cons_zero,cons_succ]

theorem countableSentence_spec (M : ZFSet.{0}) (hM : Transitive M) (A ω : ℕ)
    (e : ℕ → ZFSet.{0}) (he : ∀ i, e i ∈ M) (hω : e ω = ZFSet.omega) :
    (countableSentence A ω).Sat (M : Set ZFSet) e ↔ InternallyCountable M (e A) := by
  change (∃ f ∈ M, (fromBounded _).Sat _ (cons f e)) ↔ _
  unfold InternallyCountable
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  rw [bounded_sat,Formula.absolute _ M hM _ (by intro i; cases i; exact hf; exact he _),ontoMatrix_spec]
  simp only [cons_zero,cons_succ,hω]

theorem uncountableOrdinalSentence_spec (M : ZFSet.{0}) (hM : Transitive M)
    (e : ℕ → ZFSet.{0}) (he : ∀ i, e i ∈ M) (hω : e 1 = ZFSet.omega) :
    uncountableOrdinalSentence.Sat (M : Set ZFSet) e ↔
      (e 0).IsOrdinal ∧ ¬ (e 0 = ∅ ∨ InternallyCountable M (e 0)) := by
  change (fromBounded _).Sat _ e ∧ (¬ (fromBounded _).Sat _ e) ∧
    ¬ (countableSentence 0 1).Sat _ e ↔ _
  rw [bounded_sat,Formula.absolute _ M hM e he,bounded_sat,Formula.absolute _ M hM e he,
    countableSentence_spec M hM 0 1 e he hω]
  simp only [Formula.Eval,Formula.eval_transitive,Formula.eval_allMem,Formula.eval_empty,
    cons_zero,ZFSet.isOrdinal_iff_forall_mem_isTransitive,not_or]
  rfl

end TuringRigidity.InternalUncountableSentence

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ValidFirstUncountable
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.ValidFirstUncountable
open TransitiveNameModel BoundedSetTheory ElementaryModel InternalCountableOrdinals
open InternalUncountableSentence InternalGraphEquiv

theorem card_le_of_graph (A B f : ZFSet.{0}) (hf : FunctionGraph A B f)
    (hs : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ f) : B.card ≤ A.card := by
  have hsurj : Function.Surjective (graphMap A B f hf) := by
    intro y
    obtain ⟨x,hx,hxy⟩ := hs (label B y) (label_mem B y)
    obtain ⟨x,rfl⟩ := label_surjective A hx
    exact ⟨x,label_injective B (hf.functional (label_mem A x) (graphMap_spec A B f hf x) hxy)⟩
  exact Cardinal.mk_le_of_surjective hsurj

theorem ambient_larger_ordinal (W : ZFSet.{0}) :
    ∃ K : ZFSet.{0}, K.IsOrdinal ∧ K ≠ ∅ ∧
      ¬ (∃ f, FunctionGraph W K f ∧ ∀ y ∈ K, ∃ x ∈ W, ZFSet.pair x y ∈ f) := by
  let K : ZFSet.{0} := (Order.succ W.card).ord.toZFSet
  have hcard : K.card = Order.succ W.card := by
    dsimp only [K]
    rw [Ordinal.card_toZFSet,Cardinal.card_ord]
  refine ⟨K,ZFSet.isOrdinal_toZFSet _,?_,?_⟩
  · intro he
    have hh := congrArg ZFSet.card he
    rw [hcard,ZFSet.card_empty] at hh
    exact Cardinal.succ_ne_zero W.card hh
  · rintro ⟨f,hf,hs⟩
    have hle := card_le_of_graph W K f hf hs
    rw [hcard] at hle
    exact (Order.lt_succ W.card).not_ge hle

theorem ambient_sentence (e : ℕ → ZFSet.{0}) :
    (SentenceForm.ex uncountableOrdinalSentence).Sat Set.univ e := by
  obtain ⟨K,hK,hne,hunc⟩ := ambient_larger_ordinal (e 0)
  refine ⟨K,Set.mem_univ _,?_⟩
  change (fromBounded _).Sat _ _ ∧ (¬ (fromBounded _).Sat _ _) ∧ ¬ (countableSentence 0 1).Sat _ _
  rw [bounded_univ,bounded_univ]
  constructor
  · simp only [Formula.Eval,Formula.eval_transitive,Formula.eval_allMem,cons_zero]
    exact ZFSet.isOrdinal_iff_forall_mem_isTransitive.mp hK
  constructor
  · simpa only [Formula.eval_empty,cons_zero] using hne
  · rintro ⟨f,_,hf⟩
    exact hunc ⟨f,(ontoMatrix_spec 0 2 1 _).mp ((bounded_univ _ _).mp hf)⟩

theorem firstUncountable_exists (M : ZFSet.{0}) (hM : Transitive M) (hV : Valid M)
    (hne : ∃ a, a ∈ M) : ∃ K, FirstUncountable M K := by
  have hT := hV.sourceT hM hne
  have hω := sourceT_omega_mem M hM hT
  have h := hV (.ex uncountableOrdinalSentence) ambient_sentence (fun _ => ZFSet.omega) (fun _ => hω)
  obtain ⟨L,hL,hs⟩ := h
  have he : ∀ i, cons L (fun _ => ZFSet.omega) i ∈ M := by
    intro i; cases i; exact hL; exact hω
  obtain ⟨hord,hunc⟩ := (uncountableOrdinalSentence_spec M hM _ he rfl).mp hs
  obtain ⟨K,hK,_⟩ := firstUncountable_below M L hM hL hord hunc
  exact ⟨K,hK⟩

end TuringRigidity.ValidFirstUncountable

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedFirstUncountable
attribute [-instance] _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PrescribedFirstUncountable
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible SetDegreeDecoding
open PersistentRestrictions ArithmeticTree

theorem prescribed_covering_model_with_omega_one_oai (π : Degree ≃o Degree) (A : ℕ → Oracle) :
    ∃ M : ZFSet.{0}, ∃ hM : Transitive M, ∃ hT : SourceT M,
      ∃ hcount : Countable (Conditions M),
        letI := hcount
        Valid M ∧ (∃ K, InternalCountableOrdinals.FirstUncountable M K) ∧ (∀ n, A n ∈ modelReals M) ∧
        (π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
          π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier) ∧
        ∃ ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
          RestrictsTo π _ ρ ∧ Persistent _ ρ ∧
          automorphismSet ρ ∈ relativeModel M (groundReals M) ∧
          SetGenericallyPersistent M _ ρ := by
  obtain ⟨M,hM,hT,hcount,hV,hA,hi,hρ⟩ := prescribed_covering_model.{0} π A
  have hK := ValidFirstUncountable.firstUncountable_exists M hM hV ⟨realCode (A 0),hA 0⟩
  exact ⟨M,hM,hT,hcount,hV,hK,hA,hi,hρ⟩

end TuringRigidity.PrescribedFirstUncountable

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one_oai := @OAI.TuringRigidity.PrescribedFirstUncountable.prescribed_covering_model_with_omega_one_oai
