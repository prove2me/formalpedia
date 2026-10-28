-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:32:30.223449+00:00
-- url     : https://prove2.me/submissions/02769fd5-48a6-4302-abbd-00079d63eb16

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_PrescribedFirstUncountable_prescribed_covering_model_with_omega_one
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_prescribed_unrestricted_ground_program
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_real_hull_prescribed_transfer

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_OracleCode
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix _root_.OAI.TuringRigidity.instOrderBotDegree _root_.OAI.TuringRigidity.instSemilatticeSupDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem countable_degree_fiber (a : Degree) : {A : Oracle | degree A = a}.Countable := by
  obtain ⟨B, rfl⟩ := degree_surjective a
  apply (countable_reduces B).mono
  intro A hA
  exact ((degree_eq_iff A B).mp hA).1

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

namespace OpenFiber
variable {X : Type*} {α β : Type} [TopologicalSpace X]

theorem const (p : Part α) : OpenFiber (fun _ : X => p) := by
  intro a
  by_cases h : a ∈ p <;> simp [h]

theorem map {f : X → Part α} (hf : OpenFiber f) (g : α → β) :
    OpenFiber (fun x => (f x).map g) := by
  intro b
  have heq : {x | b ∈ (f x).map g} =
      ⋃ a : α, {x : X | g a = b} ∩ {x | a ∈ f x} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, Part.mem_map_iff]
    exact ⟨fun ⟨a,ha,hg⟩ => ⟨a,hg,ha⟩, fun ⟨a,hg,ha⟩ => ⟨a,ha,hg⟩⟩
  rw [heq]
  apply isOpen_iUnion
  intro a
  have hg : IsOpen {x : X | g a = b} := by by_cases h : g a = b <;> simp [h]
  exact hg.inter (hf a)

theorem bind {f : X → Part α} {g : X → α → Part β}
    (hf : OpenFiber f) (hg : ∀ a, OpenFiber (fun x => g x a)) :
    OpenFiber (fun x => (f x).bind (g x)) := by
  intro b
  have heq : {x | b ∈ (f x).bind (g x)} =
      ⋃ a : α, {x | a ∈ f x} ∩ {x | b ∈ g x a} := by
    ext x
    simp [Part.mem_bind_iff]
  rw [heq]
  exact isOpen_iUnion (fun a => (hf a).inter (hg a b))

theorem seq {f : X → Part (α → β)} {g : X → Part α}
    (hf : OpenFiber f) (hg : OpenFiber g) :
    OpenFiber (fun x => f x <*> g x) := by
  exact hf.bind (fun k => hg.map k)

theorem some [TopologicalSpace α] [DiscreteTopology α] {f : X → α} (hf : Continuous f) :
    OpenFiber (fun x => Part.some (f x)) := by
  intro a
  simpa [Set.preimage, Part.mem_some_iff, eq_comm] using
    (isOpen_discrete ({a} : Set α)).preimage hf

theorem rfind {p : X → ℕ → Part Bool} (hp : ∀ n, OpenFiber (fun x => p x n)) :
    OpenFiber (fun x => Nat.rfind (p x)) := by
  intro n
  have heq : {x | n ∈ Nat.rfind (p x)} =
      {x | true ∈ p x n} ∩ ⋂ k : Fin n, {x | false ∈ p x k.val} := by
    ext x
    constructor
    · intro h
      have hr := Nat.mem_rfind.mp h
      exact ⟨hr.1, Set.mem_iInter.mpr (fun k => hr.2 k.isLt)⟩
    · rintro ⟨h,hmin⟩
      exact Nat.mem_rfind.mpr ⟨h,fun {k} hk => Set.mem_iInter.mp hmin ⟨k,hk⟩⟩
  rw [heq]
  exact (hp n true).inter (isOpen_iInter_of_finite (fun k : Fin n => hp k.val false))
end OpenFiber

namespace OracleCode

theorem eval_openFiber {X : Type*} [TopologicalSpace X] (O : X → ℕ → ℕ)
    (hO : ∀ n, Continuous (fun x => O x n)) (c : OracleCode) :
    ∀ n, OpenFiber (fun x => eval (fun k => Part.some (O x k)) c n) := by
  induction c with
  | zero => intro n; exact OpenFiber.const _
  | succ => intro n; exact OpenFiber.const _
  | left => intro n; exact OpenFiber.const _
  | right => intro n; exact OpenFiber.const _
  | query => intro n; exact OpenFiber.some (hO n)
  | pair c d hc hd => intro n; exact (OpenFiber.map (hc n) Nat.pair).seq (hd n)
  | comp c d hc hd => intro n; exact (hd n).bind (fun k => hc k)
  | prec c d hc hd =>
      intro p
      have hrec : ∀ k : ℕ, OpenFiber (fun x =>
          Nat.rec (eval (fun j => Part.some (O x j)) c (Nat.unpair p).1)
            (fun y ih => ih.bind (fun i =>
              eval (fun j => Part.some (O x j)) d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k) := by
        intro k
        induction k with
        | zero => exact hc _
        | succ k ih => exact ih.bind (fun i => hd _)
      exact hrec (Nat.unpair p).2
  | find c hc =>
      intro n
      exact OpenFiber.rfind (fun k => (hc (Nat.pair n k)).map (fun m => decide (m=0)))

theorem halting_set_open (c : OracleCode) (n m : ℕ) :
    IsOpen {A : Oracle | m ∈ eval (oracleFunction A) c n} := by
  have hO : ∀ n : ℕ, Continuous (fun A : Oracle => if A n then (1 : ℕ) else 0) := by
    intro n
    exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      (continuous_apply n)
  exact eval_openFiber _ hO c n m

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteShuffle
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FiniteShuffle
open GenericCoding UniformOracle BinarySeries

theorem Agree.mono {n m : ℕ} {A B : Oracle} (h : Agree n A B) (hm : m ≤ n) :
    Agree m A B := fun i hi => h i (by omega)

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

theorem realizes_default (s : List Bool) : Realizes s (fun i => s.getD i false) :=
  fun _ _ => rfl

theorem realizes_isOpen (s : List Bool) : IsOpen {G | Realizes s G} := by
  have he : {G | Realizes s G} = ⋂ i : Fin s.length, {G : Oracle | G i = s.getD i false} := by
    ext G
    simp only [mem_ofPred_eq,mem_iInter]
    exact ⟨fun h i => (h i i.isLt).symm,fun h i hi => (h ⟨i,hi⟩).symm⟩
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  have hc : Continuous (fun G : Oracle => G (i : ℕ)) := continuous_apply _
  simpa only [Set.preimage,Set.mem_singleton_iff] using
    (isOpen_discrete ({s.getD i false} : Set Bool)).preimage hc

end TuringRigidity.ShuffleRequirements

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericTopology
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericTopology
open FiniteShuffle ShuffleRequirements GenericCoding Set

theorem cylinder_basis (U : Set Oracle) (hu : IsOpen U) (G : Oracle) (hg : G ∈ U) :
    ∃ n, ∀ H, Agree n G H → H ∈ U := by
  classical
  obtain ⟨I,u,huI,hsub⟩ := isOpen_pi_iff.mp hu G hg
  refine ⟨I.sup id + 1,?_⟩
  intro H hH
  apply hsub
  intro i hi
  have hl : i ≤ I.sup id := Finset.le_sup (f := id) hi
  rw [←hH i (by omega)]
  exact (huI i hi).2

end TuringRigidity.GenericTopology

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_IdealSelection
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericTruth
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericTruth
open FiniteShuffle ShuffleRequirements GenericTopology Set Filter Encodable

theorem cylinderIn_denseOpen (U : Set Oracle) (ho : IsOpen U) (hd : Dense U) :
    DenseOpen (CylinderIn U) := by
  constructor
  · intro s
    obtain ⟨H,hs,hHU⟩ := hd.inter_open_nonempty {G | Realizes s G} (realizes_isOpen s)
      ⟨fun i => s.getD i false,realizes_default s⟩
    obtain ⟨n,hn⟩ := cylinder_basis U ho H hHU
    refine ⟨initial H (max n s.length),?_,?_⟩
    · rw [←prefix_default s]
      simpa only [prefix_length] using initial_prefix (n := s.length) (m := max n s.length) (le_max_right _ _) hs
    · intro G hG
      exact hn G (((realizes_initial H G _).mp hG).mono (le_max_left _ _))
  · intro s t hst hs G hG
    exact hs G (realizes_mono hst hG)

end TuringRigidity.GenericTruth

end OAI
end

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenGroundGeneric
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CohenGroundGeneric
open Set TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AutomorphismName
open CohenSymmetry CohenConditionCode CohenGroundPoset
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem exists_extension (M A : ZFSet.{0}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M)
    (p : Condition (Conditions A)) :
    ∃ G : GenericFilter (Conditions (conditions A)), encode A p ∈ G.carrier ∧
      AtomicForcing.GroundGeneric M G ∧
      M ⊆ genericExtensionSet M (conditions A) G.carrier ∧
      Transitive (genericExtensionSet M (conditions A) G.carrier) ∧
      SourceT (genericExtensionSet M (conditions A) G.carrier) ∧
      AtomicForcing.Generic (names M (conditions A)) G := by
  let _ := InternalCollapse.top (conditions A) (empty_mem_conditions A)
  have hc := conditions_mem M A hM hT hA
  have ho := InternalCollapse.orderSet_mem M hM hT hc
  obtain ⟨G,hp,hG⟩ := AtomicForcing.countable_ground_generic M ⟨A,hA⟩ (encode A p)
  have ht : (⊤ : Conditions (conditions A)) ∈ G.carrier := G.upper le_top hp
  refine ⟨G,hp,hG,?_,genericExtensionSet_transitive M _ hM G.carrier,?_,?_⟩
  · exact ground_inclusion_set M _ hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  · exact extension_sourceT M hM hT hc ho (InternalCollapse.orderSet_pair _) G hG ht
  · exact AtomicForcing.groundGeneric_atomic M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc ho
      (InternalCollapse.orderSet_pair _) G hG

end TuringRigidity.CohenGroundGeneric

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

theorem sourceT_real_iterate (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {A : Oracle} (hA : A ∈ modelReals M) (n : ℕ) : iterate A n ∈ modelReals M := by
  induction n with
  | zero => exact hA
  | succ n ih => exact sourceT_real_jump M hM hT ih

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_FiniteOverwrite
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FiniteOverwrite
open UniformPrograms

theorem overwrite_below (s : List Bool) (A : Oracle) (n : ℕ) (hn : n < s.length) :
    overwrite s A n = s.getD n false := by simp [overwrite,hn]

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_ProgramContinuity
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
namespace GenericIdentity
open Set

theorem value_continuousOn (p : OracleCode) (P : Oracle) (S : Set Oracle)
    (hS : ∀ A ∈ S, Total p P A) : ContinuousOn (value p P) S := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply continuous_pi
  intro n
  have hO : Continuous (fun A : S => join A.val P) := by
    apply continuous_pi
    intro i
    dsimp only [join]
    split
    · exact continuous_const
    · exact (continuous_apply _).comp continuous_subtype_val
  have hf (b : Bool) : IsOpen {A : S | value p P A.val n = b} := by
    have he : {A : S | value p P A.val n = b} =
        (fun A : S => join A.val P) ⁻¹'
          {B | (if b then 1 else 0) ∈ OracleCode.eval (oracleFunction B) p n} := by
      ext A
      simp only [mem_ofPred_eq,mem_preimage]
      rw [(total_iff p P A.val).mp (hS A.val A.property)]
      simp only [oracleFunction,Part.mem_some_iff]
      cases b <;> cases value p P A.val n <;> simp
    rw [he]
    exact (OracleCode.halting_set_open p n _).preimage hO
  apply continuous_def.mpr
  intro U _
  have he : (fun A : S => value p P A.val n) ⁻¹' U =
      ⋃ b : Bool, ⋃ (_ : b ∈ U), {A : S | value p P A.val n = b} := by
    ext A; simp
  change IsOpen ((fun A : S => value p P A.val n) ⁻¹' U)
  rw [he]
  exact isOpen_iUnion (fun b => isOpen_iUnion (fun _ => hf b))

end GenericIdentity

end TuringRigidity

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

theorem binaryHalts_isOpen (p : OracleCode) (P : Oracle) (n : ℕ) :
    IsOpen {A | BinaryHalts p P A n} := by
  have hO : Continuous (fun A : Oracle => join A P) := by
    apply continuous_pi
    intro i
    dsimp only [join]
    split
    · exact continuous_const
    · exact continuous_apply _
  exact ((OracleCode.halting_set_open p n 0).union
    (OracleCode.halting_set_open p n 1)).preimage hO

theorem generic_totality_of_dense (p : OracleCode) (P : Oracle)
    (hd : Dense {A | Total p P A}) :
    ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
      (∀ A, GenericFor D A → Total p P A) ∧
      ContinuousOn (value p P) {A | GenericFor D A} := by
  let D := fun n => CylinderIn {A | BinaryHalts p P A n}
  have hD : ∀ n, DenseOpen (D n) := by
    intro n
    apply cylinderIn_denseOpen _ (binaryHalts_isOpen p P n)
    exact hd.mono (fun A hA => (total_iff_binaryHalts p P A).mp hA n)
  have ht : ∀ A, GenericFor D A → Total p P A := by
    intro A hA
    apply (total_iff_binaryHalts p P A).mpr
    intro n
    obtain ⟨s,hs,hAs⟩ := hA n
    exact hs A hAs
  exact ⟨D,hD,ht,value_continuousOn p P _ ht⟩

end TuringRigidity.GenericIdentity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_CohenProgramTotality
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset CohenColumnRealName CohenFiniteFlip FiniteOverwrite GenericIdentity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem column_program_totality_dense (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (p : OracleCode) (R : Oracle)
    (ht : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → Total p R A) :
    _root_.Dense {A | Total p R A} := by
  obtain ⟨A₀,hA₀,_,_⟩ := generic_real_value M K a hM hT hK ha G hG
  apply dense_iff_inter_open.mpr
  rintro U hU ⟨B,hB⟩
  obtain ⟨n,hn⟩ := GenericTopology.cylinder_basis U hU B hB
  let s := FiniteShuffle.initial B n
  obtain ⟨hGs,_,hval⟩ := prefixFilter_properties M K a hM hT hK ha s A₀ G hG hA₀
  refine ⟨overwrite s A₀,hn _ ?_,ht _ hGs _ hval⟩
  intro i hi
  rw [overwrite_below _ _ _ (by simpa [s] using hi),FiniteShuffle.prefix_getD _ _ _ hi]

theorem column_program_generic_totality (M K a : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (p : OracleCode) (R : Oracle)
    (ht : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A → Total p R A) :
    ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
      (∀ A, ShuffleRequirements.GenericFor D A → Total p R A) ∧
      ContinuousOn (value p R) {A | ShuffleRequirements.GenericFor D A} :=
  generic_totality_of_dense p R (column_program_totality_dense M K a hM hT hK ha G hG p R ht)

end TuringRigidity.RelativeConstructible

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

end TuringRigidity.UniformPrograms

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

end
end TuringRigidity.SetModelReals

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

end
end TuringRigidity.SetDegreeDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OwnProgramValue
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory PersistentRestrictions SetDegreeDecoding
open GenericIdentity TableIndices IndexMatrix

theorem own_program_of_table (d : ℕ) :
    ∃ p : OracleCode, ∀ (E f : ZFSet.{0}) (R A : Oracle),
      (∃ X : Oracle, Represents (join A R) (machine d) X ∧
        ∃ u ∈ degreeUniverse (groundReals E), ∃ v ∈ degreeUniverse (groundReals E),
          realCode A ∈ u ∧ realCode X ∈ v ∧ ZFSet.pair u v ∈ f) → OwnProgramAt E f p R A := by
  obtain ⟨p,hp⟩ := UniformPrograms.table_program d
  refine ⟨p,fun E f R A ⟨X,hX,hrel⟩ => ?_⟩
  have he := hp (join A R) X hX
  refine ⟨⟨X,he⟩,?_⟩
  have hv : value p R A = X := programOutput_eq p (join A R) X he
  rwa [hv]

theorem graph_pair_action (I : CountableIdeal) (σ : I ≃o I) (A B : Oracle)
    (u v : ZFSet.{0}) (hAu : realCode A ∈ u) (hBv : realCode B ∈ v)
    (hpair : ZFSet.pair u v ∈ automorphismSet σ) :
    ∃ hA : degree A ∈ I.carrier, degree B = (σ ⟨degree A,hA⟩).val := by
  obtain ⟨a,he⟩ := (mem_automorphismSet σ _).mp hpair
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  have ha : degree A = a.val := (real_mem_degreeSet A a.val).mp hAu
  have hA : degree A ∈ I.carrier := ha.symm ▸ a.property
  have he' : (⟨degree A,hA⟩ : I) = a := Subtype.ext ha
  exact ⟨hA,by rw [he']; exact (real_mem_degreeSet B _).mp hBv⟩

theorem OwnProgramAt.action (E : ZFSet.{0}) (I : CountableIdeal) (σ : I ≃o I)
    (p : OracleCode) (R A : Oracle) (h : OwnProgramAt E (automorphismSet σ) p R A) :
    ∃ hA : degree A ∈ I.carrier, degree (value p R A) = (σ ⟨degree A,hA⟩).val := by
  obtain ⟨u,_,v,_,hAu,hBv,hpair⟩ := h.2
  exact graph_pair_action I σ A (value p R A) u v hAu hBv hpair

theorem OwnProgramAt.prescribed (E : ZFSet.{0}) (I : CountableIdeal) (σ : I ≃o I)
    (π : Degree ≃o Degree) (hσ : RestrictsTo π I σ)
    (p : OracleCode) (R A : Oracle) (h : OwnProgramAt E (automorphismSet σ) p R A) :
    Total p R A ∧ degree (value p R A) = π (degree A) := by
  obtain ⟨hA,hval⟩ := h.action E I σ p R A
  exact ⟨h.1,hval.trans (hσ ⟨degree A,hA⟩).symm⟩

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

theorem nonempty (M K : ZFSet.{0}) (hK : FirstUncountable M K) : ∃ x, x ∈ K := by
  classical
  by_contra h
  apply hK.2.2.1; left
  apply ZFSet.ext; intro x
  exact ⟨fun hx => False.elim (h ⟨x,hx⟩),fun hx => False.elim (ZFSet.notMem_empty x hx)⟩

end TuringRigidity.InternalCountableOrdinals

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_DefinedPrefixRemoval
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
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

theorem defined_value_extension_eq (M c : ZFSet.{0}) (δ : Ordinal.{0})
    (Z : ZFSet.{0}) (φ : SentenceForm) (f : Name (Conditions c))
    (hfv : ∀ H : GenericFilter (Conditions c), GroundGeneric M H →
      f.val H.carrier = definedSubset (level (groundReals (genericExtensionSet M c H.carrier)) δ)
        φ (fun _ : Fin φ.bound => Z))
    (G H : GenericFilter (Conditions c)) (hG : GroundGeneric M G) (hH : GroundGeneric M H)
    (he : genericExtensionSet M c G.carrier = genericExtensionSet M c H.carrier) :
    f.val G.carrier = f.val H.carrier := by
  rw [hfv G hG,hfv H hH,he]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedOracleValue
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

theorem prescribed_oracle_value (π : Degree ≃o Degree)
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
            ∃ (A₀ : Oracle) (p : OracleCode),
              (realName K a).val GX.carrier = realCode A₀ ∧
              (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
                ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
                  OwnProgramAt (genericExtensionSet N c H.carrier) (fX.val H.carrier)
                    p (iterate R 5) A) ∧
              (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
                genericExtensionSet N c H.carrier = E →
                ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
                  GenericIdentity.Total p (iterate R 5) A ∧
                    degree (GenericIdentity.value p (iterate R 5) A) = π (degree A)) ∧
              ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
                (∀ A, ShuffleRequirements.GenericFor D A → GenericIdentity.Total p (iterate R 5) A) ∧
                ContinuousOn (GenericIdentity.value p (iterate R 5))
                  {A | ShuffleRequirements.GenericFor D A} := by
  intro c E hE hTE I J
  obtain ⟨δ,P,φ,R,hδ,hφ,hP,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,d,hA₀,hprog⟩ :=
    prescribed_unrestricted_ground_program π M K a hM hT hK ha himages ρ hρ G hG
  let N := RealGeneratedModel.hull M (realCode P)
  obtain ⟨p,hp⟩ := own_program_of_table d
  have hown : ∀ H : GenericFilter (Conditions c), GroundGeneric N H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
        OwnProgramAt (genericExtensionSet N c H.carrier) (fX.val H.carrier) p (iterate R 5) A := by
    intro H hH A hv
    exact hp _ _ _ _ (hprog H hH A hv)
  refine ⟨δ,P,φ,R,hδ,hφ,hP,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,p,hA₀,hown,?_,?_⟩
  · intro H hH he A hv
    obtain ⟨σ,hσπ,hσf⟩ := hσ
    have hfEq := defined_value_extension_eq N c δ (realCode P) φ fX
      (fun H hH => (hall H hH).1) H GX hH hGX (he.trans hExt.symm)
    have hA := hown H hH A hv
    rw [he,hfEq,hσf] at hA
    exact hA.prescribed E J σ π hσπ p (iterate R 5) A
  · exact column_program_generic_totality N K a hN.1 hN.2.1 (hN.2.2.1 hK.2.1) ha GX hGX
      p (iterate R 5) (fun H hH A hv => (hown H hH A hv).1)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedArithmeticGenericProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenColumnRealName InternalCountableOrdinals ElementaryModel PersistentRestrictions
open GenericIdentity OracleJump
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem prescribed_arithmetic_generic_program (π : Degree ≃o Degree)
    (M K : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K)
    (himages : π (degree (jump FixedArithmetic.zero)) ⊔
      π.symm (degree (jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G) :
    ∃ (R : Oracle) (p : OracleCode), realCode R ∈ M ∧
      degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
      (∀ H : Oracle, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) H →
        SourceEquation p (iterate R 5) (GenericTruth.triple H)) ∧
      (∃ D : ArithmeticPrefixForcing.PrefixPredicate, ArithmeticPrefixForcing.ArithmeticPrefix D ∧
        (∀ n, FiniteShuffle.DenseOpen (D (fun _ => iterate R 5) n)) ∧
        ∀ H : Oracle, ShuffleRequirements.GenericFor (D (fun _ => iterate R 5)) H →
          SourceEquation p (iterate R 5) (GenericTruth.triple H)) ∧
      (∀ Y : Oracle, realCode Y ∈ genericExtensionSet M (poset K) G.carrier →
        ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) Y →
          RepresentsAt π p (iterate R 5) Y) ∧
      ∃ D : ℕ → List Bool → Prop, (∀ n, FiniteShuffle.DenseOpen (D n)) ∧
        (∀ A, ShuffleRequirements.GenericFor D A → Total p (iterate R 5) A) ∧
        ContinuousOn (value p (iterate R 5)) {A | ShuffleRequirements.GenericFor D A} := by
  obtain ⟨a,ha⟩ := InternalCountableOrdinals.nonempty M K hK
  obtain ⟨δ,X,φ,R,hδ,hφ,hX,hRM,hR,hN,hNct,fX,hfX,hall,GX,hGX,hExt,hσ,A₀,p,hA₀,hown,hsem,hcont⟩ :=
    prescribed_oracle_value π M K a hM hT hK ha himages ρ hρ G hG
  have hP := sourceT_real_iterate _ hN.1 hN.2.1 (hN.2.2.1 hRM) 5
  obtain ⟨_,ht,hfinite,hrep⟩ := real_hull_prescribed_transfer M K a hM hT hK ha G hG
    X hX π p (iterate R 5) hP hsem
  exact ⟨R,p,hRM,hR,ht,hfinite,hrep,hcont⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GlobalArithmeticGenericProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing ElementaryModel PersistentRestrictions
open GenericIdentity OracleJump CohenColumnRealName
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem global_arithmetic_generic_program_oai (π : Degree ≃o Degree) :
    ∃ (R : Oracle) (p : OracleCode),
      degree R = π.symm (degree (jump FixedArithmetic.zero)) ∧
      ∀ Y : Oracle, ArithmeticPrefixForcing.Generic (fun _ => iterate R 5) Y →
        RepresentsAt π p (iterate R 5) Y := by
  classical
  by_contra hnone
  push Not at hnone
  let d := π.symm (degree (jump FixedArithmetic.zero))
  let C := {R : Oracle // degree R = d} × OracleCode
  let : Countable {R : Oracle // degree R = d} := (countable_degree_fiber d).to_subtype
  obtain ⟨R₀,hR₀⟩ := degree_surjective d
  let : Nonempty C := ⟨(⟨R₀,hR₀⟩,OracleCode.zero)⟩
  have hw : ∀ c : C, ∃ Y : Oracle,
      ArithmeticPrefixForcing.Generic (fun _ => iterate c.1.val 5) Y ∧
      ¬ RepresentsAt π c.2 (iterate c.1.val 5) Y := by
    intro c
    exact hnone c.1.val c.2 c.1.property
  choose W hWg hWbad using hw
  obtain ⟨e,he⟩ := exists_surjective_nat C
  obtain ⟨M,hM,hT,hcount,_,⟨K,hK⟩,hWM,himages,ρ,hρ,_,_,_⟩ :=
    PrescribedFirstUncountable.prescribed_covering_model_with_omega_one π (fun n => W (e n))
  let := hcount
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hK.2.1 (sourceT_omega_mem M hM hT)
  obtain ⟨G,_,hG,hME,_,_,_⟩ := CohenGroundGeneric.exists_extension M (ZFSet.prod K ZFSet.omega)
    hM hT hA ⊤
  obtain ⟨R,p,_,hR,_,_,hrep,_⟩ :=
    prescribed_arithmetic_generic_program π M K hM hT hK himages ρ hρ G hG
  let c : C := (⟨R,hR⟩,p)
  obtain ⟨n,hn⟩ := he c
  have hW : W c ∈ modelReals M := by simpa only [hn] using hWM n
  exact hWbad c (hrep (W c) (hME hW) (hWg c))

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program_oai := @OAI.TuringRigidity.RelativeConstructible.global_arithmetic_generic_program_oai
