-- Prove2me | solution 1 for OAI.TuringRigidity.ManuscriptMain.rigidity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:24:30.009998+00:00
-- url     : https://prove2.me/submissions/f158f586-ef84-4ec9-a7c8-ebde76bf51fe

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_PrescribedFirstUncountable_prescribed_covering_model_with_omega_one
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_global_arithmetic_generic_program
import Theorems.Thm_OAI_TuringRigidity_main_of_representation

section
-- module Solutions.OAIQ064_DR.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

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

theorem success_measurable {X : Type*} [MeasurableSpace X]
    (c : OracleCode) (A B : X → Oracle) (hA : Measurable A) (hB : Measurable B) :
    MeasurableSet {x | eval (oracleFunction (A x)) c = oracleFunction (B x)} := by
  have hv : ∀ n, Measurable (fun x => if B x n then (1 : ℕ) else 0) := by
    intro n
    exact (measurable_of_countable (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      ((measurable_pi_apply n).comp hB)
  have hh (n m : ℕ) : MeasurableSet {x | m ∈ eval (oracleFunction (A x)) c n} :=
    (halting_set_open c n m).measurableSet.preimage hA
  simp_rw [eval_eq_oracle_iff]
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro n
  have heq : {x | (if B x n then 1 else 0) ∈ eval (oracleFunction (A x)) c n} =
      ⋃ m : ℕ, {x | (if B x n then 1 else 0) = m} ∩
        {x | m ∈ eval (oracleFunction (A x)) c n} := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun m => (measurableSet_eq_fun (hv n) measurable_const).inter (hh n m))
end OracleCode

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Effective_ProgramSelection
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology
namespace TuringRigidity

theorem leastSuccess_spec {X : Type*} (R : X → ℕ → Prop) (hex : ∀ x, ∃ n, R x n)
    (x : X) : R x (leastSuccess R hex x) := by
  classical
  exact Nat.find_spec (hex x)

theorem leastSuccess_eq_iff {X : Type*} (R : X → ℕ → Prop) (hex : ∀ x, ∃ n, R x n)
    (x : X) (n : ℕ) : leastSuccess R hex x = n ↔ R x n ∧ ∀ k < n, ¬ R x k := by
  classical
  exact Nat.find_eq_iff (hex x)

theorem leastSuccess_measurable {X : Type*} [MeasurableSpace X] (R : X → ℕ → Prop)
    (hex : ∀ x, ∃ n, R x n) (hR : ∀ n, MeasurableSet {x | R x n}) :
    Measurable (leastSuccess R hex) := by
  apply measurable_to_countable'
  intro n
  have heq : (leastSuccess R hex) ⁻¹' {n} =
      {x | R x n} ∩ ⋂ k : Fin n, {x | ¬ R x k.val} := by
    ext x
    constructor
    · intro h
      have hr := (leastSuccess_eq_iff R hex x n).mp h
      exact ⟨hr.1, Set.mem_iInter.mpr (fun k => hr.2 k.val k.isLt)⟩
    · rintro ⟨h,hmin⟩
      exact (leastSuccess_eq_iff R hex x n).mpr ⟨h,fun k hk => Set.mem_iInter.mp hmin ⟨k,hk⟩⟩
  rw [heq]
  exact (hR n).inter (MeasurableSet.iInter (fun k : Fin n => (hR k.val).compl))

theorem codeEnumeration_surjective : Function.Surjective codeEnumeration := by
  intro c
  refine ⟨Encodable.encode c, ?_⟩
  simp [codeEnumeration]

theorem join_measurable {X : Type*} [MeasurableSpace X] (A B : X → Oracle)
    (hA : Measurable A) (hB : Measurable B) : Measurable (fun x => join (A x) (B x)) := by
  apply Measurable.of_eval
  intro n
  by_cases hn : n.bodd = true
  · simpa [join, hn, Function.comp_def] using (measurable_pi_apply (n/2)).comp hB
  · simpa [join, hn, Function.comp_def] using (measurable_pi_apply (n/2)).comp hA

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_BorelGeneric
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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

variable {X : Type*} [MeasurableSpace X]
variable (R : X → ℕ → ℕ → Prop)
variable (hd : ∀ x n s, ∃ t, Ext s t ∧ R x n t)

omit [MeasurableSpace X] in
theorem next_spec (n : ℕ) (x : X) (s : ℕ) :
    Ext s (next R hd n (x,s)) ∧ R x n (next R hd n (x,s)) :=
  leastSuccess_spec (fun z : X × ℕ => fun t => Ext z.2 t ∧ R z.1 n t)
    (fun z => hd z.1 n z.2) (x,s)

theorem next_measurable (hR : ∀ n t, MeasurableSet {x | R x n t}) (n : ℕ) :
    Measurable (next R hd n) := by
  apply leastSuccess_measurable
  intro t
  exact ((Set.to_countable {s : ℕ | Ext s t}).measurableSet.preimage measurable_snd).inter
    ((hR n t).preimage measurable_fst)

theorem stage_measurable (hR : ∀ n t, MeasurableSet {x | R x n t}) :
    ∀ n, Measurable (stage R hd n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (next_measurable R hd hR n).comp (measurable_id.prodMk ih)

omit [MeasurableSpace X] in
theorem stage_prefix (x : X) (n : ℕ) :
    word (stage R hd n x) <+: word (stage R hd (n+1) x) :=
  (next_spec R hd n x (stage R hd n x)).1.1

omit [MeasurableSpace X] in
theorem stage_length (x : X) (n : ℕ) : n ≤ (word (stage R hd n x)).length := by
  induction n with
  | zero => omega
  | succ n ih =>
    have h := (next_spec R hd n x (stage R hd n x)).1.2
    change n+1 ≤ (word (next R hd n (x,stage R hd n x))).length
    omega

omit [MeasurableSpace X] in
theorem stage_prefix_of_le (x : X) {n m : ℕ} (h : n ≤ m) :
    word (stage R hd n x) <+: word (stage R hd m x) := by
  induction m, h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ m h ih => exact ih.trans (stage_prefix R hd x m)

theorem generic_measurable (hR : ∀ n t, MeasurableSet {x | R x n t}) :
    Measurable (generic R hd) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_of_countable (fun k : ℕ => (word k).getD i false)).comp
    (stage_measurable R hd hR (i+1))

private theorem getD_prefix {s t : List Bool} (h : s <+: t) (i : ℕ) (hi : i < s.length) :
    s.getD i false = t.getD i false := by
  obtain ⟨u,rfl⟩ := h
  simp [List.getD, List.getElem?_append, hi]

omit [MeasurableSpace X] in
theorem meets_stage (x : X) (n : ℕ) : Meets (generic R hd x) (stage R hd n x) := by
  intro i hi
  dsimp only [generic]
  rcases le_total n (i+1) with hn | hn
  · exact (getD_prefix (stage_prefix_of_le R hd x hn) i hi).symm
  · exact getD_prefix (stage_prefix_of_le R hd x hn) i (by
      have hl := stage_length R hd x (i+1)
      omega)

include hd in

theorem borel_generic_selection (hR : ∀ n t, MeasurableSet {x | R x n t}) :
    ∃ G : X → Oracle, Measurable G ∧ ∀ x n, ∃ t, R x n t ∧ Meets (G x) t := by
  refine ⟨generic R hd,generic_measurable R hd hR,?_⟩
  intro x n
  exact ⟨stage R hd (n+1) x,(next_spec R hd n x (stage R hd n x)).2,
    meets_stage R hd x (n+1)⟩

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

theorem requirement_dense (A : Oracle) (p q : OracleCode) (s t : List Bool) :
    ∃ u v, s <+: u ∧ t <+: v ∧ Requirement A p q u v := by
  classical
  by_cases h : ∃ u v, s <+: u ∧ t <+: v ∧ Disagree A p q u v
  · obtain ⟨u,v,hu,hv,hh⟩ := h
    exact ⟨u,v,hu,hv,Or.inl hh⟩
  · refine ⟨s,t,List.prefix_rfl,List.prefix_rfl,Or.inr ?_⟩
    intro u v n a b hu hv ha hb
    by_contra hab
    exact h ⟨u,v,hu,hv,n,a,b,hab,ha,hb⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdealBorel
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OracleCode
theorem eval_partial_openFiber {X : Type*} [TopologicalSpace X] (O : X → ℕ →. ℕ)
    (hO : ∀ n, OpenFiber (fun x => O x n)) (c : OracleCode) :
    ∀ n, OpenFiber (fun x => eval (O x) c n) := by
  induction c with
  | zero => intro n; exact OpenFiber.const _
  | succ => intro n; exact OpenFiber.const _
  | left => intro n; exact OpenFiber.const _
  | right => intro n; exact OpenFiber.const _
  | query => intro n; exact hO n
  | pair c d hc hd => intro n; exact (OpenFiber.map (hc n) Nat.pair).seq (hd n)
  | comp c d hc hd => intro n; exact (hd n).bind (fun k => hc k)
  | prec c d hc hd =>
      intro p
      have hrec : ∀ k : ℕ, OpenFiber (fun x =>
          Nat.rec (eval (O x) c (Nat.unpair p).1)
            (fun y ih => ih.bind (fun i =>
              eval (O x) d (Nat.pair (Nat.unpair p).1 (Nat.pair y i)))) k) := by
        intro k
        induction k with
        | zero => exact hc _
        | succ k ih => exact ih.bind (fun i => hd _)
      exact hrec (Nat.unpair p).2
  | find c hc =>
      intro n
      exact OpenFiber.rfind (fun k => (hc (Nat.pair n k)).map (fun m => decide (m=0)))

end TuringRigidity.OracleCode
namespace TuringRigidity.CommonIdeal
open Set

theorem run_open (p : OracleCode) (s : List Bool) (n a : ℕ) :
    IsOpen {A : Oracle | a ∈ run A p s n} := by
  apply OracleCode.eval_partial_openFiber
  intro k
  unfold partialJoin
  split
  · exact OpenFiber.const _
  · apply OpenFiber.some
    exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℕ) else 0)).comp
      (continuous_apply (k/2))

theorem disagree_measurable (p q : OracleCode) (s t : List Bool) :
    MeasurableSet {A | Disagree A p q s t} := by
  simp only [Disagree, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro a
  apply MeasurableSet.iUnion
  intro b
  by_cases h : a ≠ b
  · have he : {A : Oracle | a ≠ b ∧ a ∈ run A p s n ∧ b ∈ run A q t n} =
        {A | a ∈ run A p s n} ∩ {A | b ∈ run A q t n} := by
      ext A
      exact ⟨fun hx => hx.2,fun hx => ⟨h,hx⟩⟩
    rw [he]
    exact (run_open p s n a).measurableSet.inter (run_open q t n b).measurableSet
  · simp [h]

theorem agree_measurable (p q : OracleCode) (s t : List Bool) :
    MeasurableSet {A | Agree A p q s t} := by
  have he : {A | Agree A p q s t} =
      (⋃ (u : List Bool) (v : List Bool), {A | s <+: u ∧ t <+: v ∧ Disagree A p q u v})ᶜ := by
    ext A
    simp only [mem_compl_iff,mem_iUnion,mem_ofPred_eq]
    constructor
    · intro h ⟨u,v,hu,hv,n,a,b,hab,ha,hb⟩
      exact hab (h u v n a b hu hv ha hb)
    · intro h u v n a b hu hv ha hb
      by_contra hab
      exact h ⟨u,v,hu,hv,n,a,b,hab,ha,hb⟩
  rw [he]
  apply MeasurableSet.compl
  apply MeasurableSet.iUnion
  intro u
  apply MeasurableSet.iUnion
  intro v
  by_cases hs : s <+: u ∧ t <+: v
  · simpa [hs.1,hs.2] using disagree_measurable p q u v
  · have hfalse : ¬ (s <+: u ∧ t <+: v) := hs
    convert MeasurableSet.empty (α := Oracle) using 1
    all_goals try with_reducible_and_instances rfl
    ext A
    simp only [mem_ofPred_eq,mem_empty_iff_false,iff_false,not_and]
    intro hsu htv
    exact False.elim (hfalse ⟨hsu,htv⟩)

theorem requirement_measurable (p q : OracleCode) (s t : List Bool) :
    MeasurableSet {A | Requirement A p q s t} :=
  (disagree_measurable p q s t).union (agree_measurable p q s t)

end TuringRigidity.CommonIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdealSearch
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
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

theorem ideal_of_meets (A G H : Oracle)
    (h : ∀ p q : OracleCode, ∃ s t, Extends G s ∧ Extends H t ∧ Requirement A p q s t) :
    ∀ b : Degree, b ≤ degree A ↔ b ≤ degree (join A G) ∧ b ≤ degree (join A H) := by
  intro b
  obtain ⟨Y,rfl⟩ := degree_surjective b
  constructor
  · intro hY
    exact ⟨reduces_trans hY (reduces_join_left A G),reduces_trans hY (reduces_join_left A H)⟩
  · rintro ⟨hG,hH⟩
    obtain ⟨p,hp⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hG
    obtain ⟨q,hq⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hH
    obtain ⟨s,t,hs,ht,hR⟩ := h p q
    exact common_output_reduces hs ht hR hp hq

end TuringRigidity.CommonIdeal

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_CommonIdealSelection
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.CommonIdeal
open Set Encodable

theorem pad_extends (s : List Bool) : Extends (pad s) s := fun _ _ => rfl

theorem extends_of_prefix {G : Oracle} {s t : List Bool} (h : s <+: t)
    (ht : Extends G t) : Extends G s := by
  obtain ⟨u,rfl⟩ := h
  intro i hi
  rw [ht i (by simp; omega)]
  simp [List.getD,List.getElem?_append,hi]

theorem join_columns (G : Oracle) : join (even G) (odd G) = G := by
  funext n
  have hn := Nat.bodd_add_div2 n
  cases hb : n.bodd with
  | false =>
    have he : 2*(n/2) = n := by simpa [hb,Nat.div2_val] using hn
    simp [join,even,hb,he]
  | true =>
    have he : 2*(n/2)+1 = n := by simpa [hb,Nat.div2_val,Nat.add_comm] using hn
    simp [join,odd,hb,he]

theorem embeds_initialWord (s t : List Bool) (M : ℕ)
    (hs : 2*s.length ≤ M) (ht : 2*t.length ≤ M) :
    Embeds (initialWord (join (pad s) (pad t)) M) s t := by
  intro G hG
  constructor
  · intro i hi
    have hh := hG (2*i) (by simp; omega)
    rw [prefix_getD _ _ _ (by omega),join_even] at hh
    exact hh
  · intro i hi
    have hh := hG (2*i+1) (by simp; omega)
    rw [prefix_getD _ _ _ (by omega),join_odd] at hh
    exact hh

theorem join_extends_input (r u v : List Bool)
    (hu : initialWord (even (pad r)) r.length <+: u)
    (hv : initialWord (odd (pad r)) r.length <+: v) :
    Extends (join (pad u) (pad v)) r := by
  have hU := extends_of_prefix hu (pad_extends u)
  have hV := extends_of_prefix hv (pad_extends v)
  intro n hn
  have hhalf : n/2 < r.length := by omega
  have hU' := hU (n/2) (by simpa using hhalf)
  have hV' := hV (n/2) (by simpa using hhalf)
  rw [prefix_getD _ _ _ hhalf] at hU' hV'
  have heq : join (pad u) (pad v) n = join (even (pad r)) (odd (pad r)) n := by
    unfold join
    split
    · exact hV'
    · exact hU'
  rw [heq,join_columns]
  rfl

theorem family_dense (A : Oracle) (n c : ℕ) :
    ∃ d, BorelGeneric.Ext c d ∧ family A n d := by
  let r := BorelGeneric.word c
  obtain ⟨u,v,hu,hv,hR⟩ := requirement_dense A
    (codeEnumeration (Nat.unpair n).1) (codeEnumeration (Nat.unpair n).2)
    (initialWord (even (pad r)) r.length) (initialWord (odd (pad r)) r.length)
  let M := 2*(u.length+v.length+r.length+1)
  let w := initialWord (join (pad u) (pad v)) M
  obtain ⟨d,hd⟩ := BorelGeneric.word_surjective w
  refine ⟨d,?_,?_⟩
  · constructor
    · rw [hd]
      exact prefix_of_extends (join_extends_input r u v hu hv) (by dsimp [M]; omega)
    · rw [hd]
      simp only [w,prefix_length]
      dsimp [M,r]
      omega
  · refine ⟨u,v,?_,hR⟩
    rw [hd]
    exact embeds_initialWord u v M (by dsimp [M]; omega) (by dsimp [M]; omega)

theorem family_measurable (n c : ℕ) : MeasurableSet {A | family A n c} := by
  simp only [family,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro s
  apply MeasurableSet.iUnion
  intro t
  by_cases he : Embeds (BorelGeneric.word c) s t
  · simpa [he] using requirement_measurable
      (codeEnumeration (Nat.unpair n).1) (codeEnumeration (Nat.unpair n).2) s t
  · simp [he]

theorem ideal_of_family (A G : Oracle)
    (h : ∀ n, ∃ c, family A n c ∧ BorelGeneric.Meets G c) :
    ∀ b : Degree, b ≤ degree A ↔
      b ≤ degree (join A (even G)) ∧ b ≤ degree (join A (odd G)) := by
  apply ideal_of_meets
  intro p q
  obtain ⟨i,hi⟩ := codeEnumeration_surjective p
  obtain ⟨j,hj⟩ := codeEnumeration_surjective q
  obtain ⟨c,⟨s,t,he,hR⟩,hG⟩ := h (Nat.pair i j)
  have hh := he G hG
  refine ⟨s,t,hh.1,hh.2,?_⟩
  simpa only [Nat.unpair_pair,hi,hj] using hR

end TuringRigidity.CommonIdeal

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

theorem Agree.mono {n m : ℕ} {A B : Oracle} (h : Agree n A B) (hm : m ≤ n) :
    Agree m A B := fun i hi => h i (by omega)

theorem Agree.trans {n : ℕ} {A B C : Oracle} (h : Agree n A B) (h' : Agree n B C) :
    Agree n A C := fun i hi => (h i hi).trans (h' i hi)

theorem prefix_agree {A B : Oracle} {n : ℕ} (h : Agree n A B) : initial A n = initial B n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi' : i < n := by simpa using hi
    simpa [initial] using h i hi'

theorem count_agree {n : ℕ} {G H : Oracle} (h : ∀ i, i < n → G (2*i+1) = H (2*i+1)) :
    count G n = count H n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change count G n + bit G (2*n+1) = count H n + bit H (2*n+1)
    rw [ih (fun i hi => h i (by omega))]
    simp [bit,h n (by omega)]

theorem count_constant {n : ℕ} {G : Oracle} (h : OddBound n G) {m : ℕ} (hm : n ≤ m) :
    count G m = count G n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    change count G m + bit G (2*m+1) = count G n
    simp [bit,h m hm,ih]

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

theorem code_agree_inserted {n : ℕ} {A B G : Oracle} (hg : OddBound n G) (ha : Agree n A B) :
    code A G = code B G := by
  funext i
  unfold code
  split
  · rename_i hb
    have hi : i < n := by
      by_contra hi
      have := hg i (by omega)
      simp_all
    exact ha _ (lt_of_le_of_lt (count_le G i) hi)
  · rfl

theorem freeze_bound (n : ℕ) (G : Oracle) : OddBound n (freeze n G) := by
  intro i hi
  simp [freeze,show ¬i<n by omega]

theorem agree_of_columns {n : ℕ} {G H : Oracle}
    (he : ∀ i, i < n → G (2*i) = H (2*i))
    (ho : ∀ i, i < n → G (2*i+1) = H (2*i+1)) : Agree (2*n) G H := by
  intro i hi
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have hh : i = 2*(i/2) := by omega
    rw [hh]
    exact he _ (by omega)
  · have hh : i = 2*(i/2)+1 := by omega
    rw [hh]
    exact ho _ (by omega)

theorem freeze_agree (n : ℕ) (G : Oracle) : Agree (2*n) G (freeze n G) := by
  apply agree_of_columns
  · intro i hi; simp [freeze]
  · intro i hi; simp [freeze,hi]

theorem extendEven_count (n : ℕ) (G T : Oracle) (i : ℕ) :
    count (extendEven n G T) i = count G i :=
  count_agree (fun j hj => by simp [extendEven])

theorem extendEven_agree (n : ℕ) (G T : Oracle) : Agree (2*n) G (extendEven n G T) := by
  apply agree_of_columns
  · intro i hi; simp [extendEven,hi]
  · intro i hi; simp [extendEven]

theorem extendEven_code (n : ℕ) (A G T : Oracle) (hg : OddBound n G)
    (ht : Agree (n + count G n) (code A G) T) : code A (extendEven n G T) = T := by
  funext i
  simp only [code]
  rw [extendEven_count]
  simp only [extendEven,join_odd,join_even]
  have hcn := count_le G n
  by_cases hi : i < n + count G n
  · rw [←ht i hi]
    unfold code
    split
    · rfl
    · have hsub : i - count G i < n := by
        by_cases hin : i < n
        · omega
        · rw [count_constant hg (by omega)]
          omega
      simp [hsub]
  · have hin : n ≤ i := by omega
    have hc := count_constant hg hin
    rw [hg i hin]
    simp only [Bool.false_eq_true,↓reduceIte,hc]
    have hl := count_le G n
    have hn : ¬i-count G n<n := by omega
    rw [ite_eq_right hn]
    congr 1
    omega

theorem agree_of_prefix {A : Oracle} {n : ℕ} {t : List Bool} (h : initial A n <+: t) :
    Agree n A (fun i => t.getD i false) := by
  obtain ⟨u,hu⟩ := h
  intro i hi
  rw [←hu]
  simpa [List.getD,List.getElem?_append,hi] using (prefix_getD A n i hi).symm

theorem odd_null_extension (D : List Bool → Prop) (hd : DenseOpen D)
    (n : ℕ) (A G : Oracle) (hg : OddBound n G) :
    ∃ m H, n < m ∧ Agree (2*n) G H ∧
      (∀ i, H (2*i+1) = G (2*i+1)) ∧ D (initial (code A H) m) := by
  obtain ⟨t,ht,hD⟩ := hd.1 (initial (code A G) (n + count G n + 1))
  let T : Oracle := fun i => t.getD i false
  have ha : Agree (n + count G n) (code A G) T :=
    (agree_of_prefix ht).mono (by omega)
  have he := extendEven_code n A G T hg ha
  refine ⟨t.length,extendEven n G T,?_,extendEven_agree n G T,?_,?_⟩
  · have hl := ht.length_le
    simp only [prefix_length] at hl
    omega
  · intro i; simp [extendEven]
  · rw [he]
    change D (initial (fun i => t.getD i false) t.length)
    rw [prefix_default]
    exact hD

theorem finite_extension (D : List Bool → Prop) (hd : DenseOpen D)
    (S : Finset Oracle) (n : ℕ) (G : Oracle) (hg : OddBound n G) :
    ∃ m H, n ≤ m ∧ Agree (2*n) G H ∧
      (∀ i, H (2*i+1) = G (2*i+1)) ∧
      ∀ A ∈ S, ∃ l, l ≤ m ∧ D (initial (code A H) l) := by
  classical
  induction S using Finset.induction_on generalizing n G with
  | empty => exact ⟨n,G,le_rfl,fun _ _ => rfl,fun _ => rfl,by simp⟩
  | @insert A S hAS ih =>
    obtain ⟨m,H,hnm,hGH,hoH,hS⟩ := ih n G hg
    have hb : OddBound m H := by
      intro i hi
      rw [hoH i]
      exact hg i (by omega)
    obtain ⟨k,K,hmk,hHK,hoK,hD⟩ := odd_null_extension D hd m A H hb
    refine ⟨k,K,by omega,hGH.trans (hHK.mono (by omega)),
      fun i => (hoK i).trans (hoH i),?_⟩
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact ⟨k,le_rfl,hD⟩
    · obtain ⟨l,hl,hDl⟩ := hS B hB
      refine ⟨l,by omega,?_⟩
      have hc : Agree l (code B H) (code B K) :=
        code_agree (fun _ _ => rfl) (hHK.mono (by omega))
      rwa [←prefix_agree hc]

theorem all_extension (D : List Bool → Prop) (hd : DenseOpen D) (n : ℕ) (G : Oracle) :
    ∃ m H, n ≤ m ∧ Agree (2*n) G H ∧ OddBound n H ∧
      ∀ A, ∃ l, l ≤ m ∧ D (initial (code A H) l) := by
  classical
  let f : (Fin n → Bool) → Oracle := fun s i => if hi : i < n then s ⟨i,hi⟩ else false
  let S : Finset Oracle := Finset.univ.image f
  obtain ⟨m,H,hnm,hGH,ho,hS⟩ := finite_extension D hd S n (freeze n G) (freeze_bound n G)
  have hb : OddBound n H := fun i hi => (ho i).trans (freeze_bound n G i hi)
  refine ⟨m,H,hnm,(freeze_agree n G).trans hGH,hb,?_⟩
  intro A
  let a : Fin n → Bool := fun i => A i
  have ha : f a ∈ S := Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  obtain ⟨l,hl,hD⟩ := hS (f a) ha
  have he : code (f a) H = code A H := code_agree_inserted hb (by
    intro i hi
    simp [f,a,hi])
  exact ⟨l,hl,by simpa [he] using hD⟩

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

theorem transfer_mono (D : List Bool → Prop) {s t : List Bool}
    (h : s <+: t) (hs : Transfer D s) : Transfer D t := by
  intro A
  obtain ⟨r,hr,hG⟩ := hs A
  exact ⟨r,hr,fun G hg => hG G (realizes_mono h hg)⟩

theorem transfer_denseOpen (D : List Bool → Prop) (hd : DenseOpen D) : DenseOpen (Transfer D) := by
  refine ⟨?_,fun _ _ h hs => transfer_mono D h hs⟩
  intro s
  let G : Oracle := fun i => s.getD i false
  obtain ⟨m,H,hnm,hGH,hb,hD⟩ := all_extension D hd (s.length+1) G
  refine ⟨initial H (2*m),?_,?_⟩
  · rw [←prefix_default s]
    apply initial_prefix (n := s.length) (m := 2*m) (by omega)
    exact hGH.mono (by omega)
  · intro A
    obtain ⟨l,hl,hDl⟩ := hD A
    refine ⟨initial (code A H) l,hDl,?_⟩
    intro K hK
    apply (realizes_initial _ _ _).mpr
    exact code_agree (fun _ _ => rfl)
      (((realizes_initial H K (2*m)).mp hK).mono (by omega))

theorem generic_transfer (D : ℕ → List Bool → Prop) (G : Oracle)
    (hg : GenericFor (fun n => Transfer (D n)) G) (A : Oracle) : GenericFor D (code A G) := by
  intro n
  obtain ⟨s,hs,hGs⟩ := hg n
  obtain ⟨t,ht,hGt⟩ := hs A
  exact ⟨t,ht,hGt G hGs⟩

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

theorem requirements_denseOpen (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n)) (n : ℕ) :
    DenseOpen (Requirements D n) := by
  unfold Requirements
  split
  · exact hd _
  · split
    · exact transfer_denseOpen _ (hd _)
    · exact oddHit_denseOpen _

theorem requirements_spec (D : ℕ → List Bool → Prop) (G : Oracle)
    (hg : GenericFor (Requirements D) G) :
    GenericFor D G ∧ InfiniteOdd G ∧ ∀ A, GenericFor D (code A G) := by
  have h0 : GenericFor D G := by
    intro n
    simpa [OpenSet,Requirements,Nat.unpair_pair] using hg (Nat.pair n 0)
  have h1 : GenericFor (fun n => Transfer (D n)) G := by
    intro n
    simpa [OpenSet,Requirements,Nat.unpair_pair] using hg (Nat.pair n 1)
  have h2 : GenericFor OddHit G := by
    intro n
    simpa [OpenSet,Requirements,Nat.unpair_pair] using hg (Nat.pair n 2)
  exact ⟨h0,infiniteOdd_of_hits G h2,fun A => generic_transfer D G h1 A⟩

theorem coded_dense (D : List Bool → Prop) (hd : DenseOpen D) (s : ℕ) :
    ∃ t, BorelGeneric.Ext s t ∧ D (BorelGeneric.word t) := by
  obtain ⟨u,hu,hD⟩ := hd.1 (BorelGeneric.word s ++ [false])
  obtain ⟨t,ht⟩ := BorelGeneric.word_surjective u
  refine ⟨t,⟨?_,?_⟩,by simpa [ht] using hD⟩
  · rw [ht]
    exact (List.prefix_append _ _).trans hu
  · have hl := hu.length_le
    simp only [List.length_append,List.length_singleton] at hl
    rw [ht]
    omega

theorem realizes_iff_meets (G : Oracle) (s : ℕ) :
    Realizes (BorelGeneric.word s) G ↔ BorelGeneric.Meets G s := by
  exact ⟨fun h i hi => (h i hi).symm,fun h i hi => (h i hi).symm⟩

theorem requirements_borel {X : Type*} [MeasurableSpace X]
    (D : ℕ → List Bool → Prop) (n t : ℕ) :
    MeasurableSet {_x : X | Requirements D n (BorelGeneric.word t)} := by
  by_cases h : Requirements D n (BorelGeneric.word t) <;> simp [h]

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

theorem borel_selection_with_requirements {X : Type*} [MeasurableSpace X]
    (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n))
    (R : X → ℕ → ℕ → Prop)
    (hRd : ∀ x n s, ∃ t, BorelGeneric.Ext s t ∧ R x n t)
    (hRm : ∀ n t, MeasurableSet {x | R x n t}) :
    ∃ G : X → Oracle, Measurable G ∧ ∀ x,
      (GenericFor D (G x) ∧ InfiniteOdd (G x) ∧ ∀ A, GenericFor D (code A (G x))) ∧
      ∀ n, ∃ t, R x n t ∧ BorelGeneric.Meets (G x) t := by
  have hc : ∀ x n s, ∃ t, BorelGeneric.Ext s t ∧ Combined D R x n t := by
    intro x n s
    unfold Combined
    split
    · exact coded_dense _ (requirements_denseOpen D hd _) s
    · exact hRd x _ s
  have hm : ∀ n t, MeasurableSet {x | Combined D R x n t} := by
    intro n t
    unfold Combined
    split
    · exact requirements_borel D _ _
    · exact hRm _ _
  obtain ⟨G,hG,hreq⟩ := BorelGeneric.borel_generic_selection (Combined D R) hc hm
  refine ⟨G,hG,?_⟩
  intro x
  constructor
  · apply requirements_spec
    intro n
    obtain ⟨t,ht,hGt⟩ := hreq x (2*n)
    exact ⟨BorelGeneric.word t,by simpa [Combined] using ht,(realizes_iff_meets _ _).mpr hGt⟩
  · intro n
    obtain ⟨t,ht,hGt⟩ := hreq x (2*n+1)
    exact ⟨t,by simpa [Combined,Nat.add_div] using ht,hGt⟩

end TuringRigidity.GenericTopology

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PairGenericSelection
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.PairGenericSelection
open FiniteShuffle ShuffleRequirements GenericTopology GenericCoding Set

theorem column_agree (b : Bool) {n : ℕ} {G H : Oracle} (h : Agree (2*n) G H) :
    Agree n (column b G) (column b H) := by
  intro i hi
  cases b <;> simp only [column,Bool.false_eq_true,↓reduceIte] <;> apply h <;> omega

theorem column_measurable (b : Bool) : Measurable (column b) := by
  apply Measurable.of_eval
  intro n
  cases b <;> exact measurable_pi_apply _

theorem column_denseOpen (D : List Bool → Prop) (hd : DenseOpen D) (b : Bool) :
    DenseOpen (ColumnRequirement D b) := by
  constructor
  · intro s
    let G : Oracle := fun i => s.getD i false
    let n := s.length+1
    obtain ⟨t,ht,hD⟩ := hd.1 (initial (column b G) n)
    let T : Oracle := fun i => t.getD i false
    let H : Oracle := if b then join (column false G) T else join T (column true G)
    have hcol : column b H = T := by
      funext i
      cases b <;> simp [H,column]
    have hl : n ≤ t.length := by simpa only [prefix_length] using ht.length_le
    have hpair : Agree (2*n) G H := by
      apply agree_of_columns
      · intro i hi
        cases b
        · simpa [H,column,T] using agree_of_prefix ht i hi
        · simp [H,column]
      · intro i hi
        cases b
        · simp [H,column]
        · simpa [H,column,T] using agree_of_prefix ht i hi
    refine ⟨initial H (2*t.length),?_,t,hD,?_⟩
    · rw [←prefix_default s]
      exact initial_prefix (n := s.length) (m := 2*t.length) (by dsimp [n] at hl; omega)
        (hpair.mono (by dsimp [n]; omega))
    · intro K hK
      have hc := column_agree b ((realizes_initial H K (2*t.length)).mp hK)
      rw [hcol] at hc
      exact hc
  · intro s t hst
    rintro ⟨u,hD,hu⟩
    exact ⟨u,hD,fun G hG => hu G (realizes_mono hst hG)⟩

theorem pair_requirements_denseOpen (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n))
    (n : ℕ) : DenseOpen (PairRequirements D n) :=
  column_denseOpen _ (requirements_denseOpen D hd _) _

theorem pair_requirements_spec (D : ℕ → List Bool → Prop) (G : Oracle)
    (hg : GenericFor (PairRequirements D) G) (b : Bool) :
    GenericFor D (column b G) ∧ InfiniteOdd (column b G) ∧
      ∀ A, GenericFor D (code A (column b G)) := by
  apply requirements_spec
  intro n
  have h : G ∈ OpenSet (ColumnRequirement (Requirements D n) b) := by
    cases b
    · simpa [OpenSet,PairRequirements] using hg (2*n)
    · simpa [OpenSet,PairRequirements,Nat.add_div] using hg (2*n+1)
  obtain ⟨s,⟨t,ht,hcol⟩,hs⟩ := h
  exact ⟨t,ht,hcol G hs⟩

theorem borel_pair_selection {X : Type*} [MeasurableSpace X]
    (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n))
    (R : X → ℕ → ℕ → Prop)
    (hRd : ∀ x n s, ∃ t, BorelGeneric.Ext s t ∧ R x n t)
    (hRm : ∀ n t, MeasurableSet {x | R x n t}) :
    ∃ Z : X → Oracle, Measurable Z ∧
      (∀ x b, GenericFor D (column b (Z x)) ∧ InfiniteOdd (column b (Z x)) ∧
        ∀ A, GenericFor D (code A (column b (Z x)))) ∧
      ∀ x n, ∃ t, R x n t ∧ BorelGeneric.Meets (Z x) t := by
  obtain ⟨Z,hZ,hreq⟩ := borel_selection_with_requirements (PairRequirements D)
    (pair_requirements_denseOpen D hd) R hRd hRm
  exact ⟨Z,hZ,fun x b => pair_requirements_spec D (Z x) (hreq x).1.1 b,
    fun x => (hreq x).2⟩

end TuringRigidity.PairGenericSelection

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericCodingBorel
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.GenericCoding
open Set UniformOracle BinarySeries

theorem query_measurable {X : Type*} [MeasurableSpace X]
    (A : X → Oracle) (q : X → ℕ) (hA : Measurable A) (hq : Measurable q) :
    Measurable (fun x => A x (q x)) := by
  apply measurable_to_countable'
  intro b
  change MeasurableSet {x | A x (q x) = b}
  have he : {x | A x (q x) = b} = ⋃ n : ℕ, {x | q x = n} ∩ {x | A x n = b} := by
    ext x
    simp only [mem_ofPred_eq,mem_iUnion,mem_inter_iff]
    exact ⟨fun h => ⟨q x,rfl,h⟩,fun ⟨n,hn,h⟩ => by simpa [hn] using h⟩
  rw [he]
  exact MeasurableSet.iUnion (fun n => (measurableSet_eq_fun hq measurable_const).inter
    (measurableSet_eq_fun ((measurable_pi_apply n).comp hA) measurable_const))

theorem count_measurable (n : ℕ) : Measurable (fun G : Oracle => count G n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hb : Measurable (fun G : Oracle => bit G (2*n+1)) :=
      (measurable_of_countable (fun b : Bool => if b then (1 : ℕ) else 0)).comp
        (measurable_pi_apply (2*n+1))
    exact (measurable_of_countable (fun z : ℕ × ℕ => z.1+z.2)).comp (ih.prodMk hb)

theorem code_measurable : Measurable (Function.uncurry code) := by
  apply Measurable.of_eval
  intro n
  have hc : Measurable (fun p : Oracle × Oracle => count p.2 n) := (count_measurable n).comp measurable_snd
  have ha := query_measurable (fun p : Oracle × Oracle => p.1) (fun p => count p.2 n) measurable_fst hc
  have hi : Measurable (fun p : Oracle × Oracle => 2*(n-count p.2 n)) :=
    (measurable_of_countable (fun k : ℕ => 2*(n-k))).comp hc
  have he := query_measurable (fun p : Oracle × Oracle => p.2) _ measurable_snd hi
  have ho : Measurable (fun p : Oracle × Oracle => p.2 (2*n+1)) :=
    (measurable_pi_apply (2*n+1)).comp measurable_snd
  exact (measurable_of_countable (fun z : Bool × Bool × Bool => if z.1 then z.2.1 else z.2.2)).comp
    (ho.prodMk (ha.prodMk he))

end TuringRigidity.GenericCoding

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

theorem programOutput_measurable (c : OracleCode) : Measurable (programOutput c) := by
  apply Measurable.of_eval
  intro n
  apply measurable_to_countable'
  intro b
  cases b with
  | false =>
    convert (OracleCode.halting_set_open c n 1).measurableSet.compl using 1
    all_goals try with_reducible_and_instances rfl
    ext A
    simp [programOutput]
  | true =>
    convert (OracleCode.halting_set_open c n 1).measurableSet using 1
    all_goals try with_reducible_and_instances rfl
    ext A
    simp [programOutput]

theorem programOutput_eq (c : OracleCode) (A B : Oracle)
    (h : OracleCode.eval (oracleFunction A) c = oracleFunction B) :
    programOutput c A = B := by
  funext n
  simp only [programOutput, h, oracleFunction, Part.mem_some_iff]
  cases B n <;> simp

theorem reduces_measurable {X : Type*} [MeasurableSpace X]
    (A B : X → Oracle) (hA : Measurable A) (hB : Measurable B) :
    MeasurableSet {x | Reduces (A x) (B x)} := by
  have he : {x | Reduces (A x) (B x)} =
      ⋃ c : OracleCode, {x | OracleCode.eval (oracleFunction (B x)) c = oracleFunction (A x)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion]
    exact OracleCode.turingReducible_iff_exists_code _ _
  rw [he]
  exact MeasurableSet.iUnion (fun c => OracleCode.success_measurable c B A hB hA)

theorem exists_programOutput (A B : Oracle) (h : Reduces B A) :
    ∃ n, programOutput (codeEnumeration n) A = B := by
  obtain ⟨c,hc⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
  obtain ⟨n,hn⟩ := codeEnumeration_surjective c
  exact ⟨n,by simpa [hn] using programOutput_eq c A B hc⟩

theorem borel_of_ideal_intersection {X : Type*} [MeasurableSpace X]
    (L R : X → Oracle) (hL : Measurable L) (hR : Measurable R)
    (d : X → Degree)
    (hd : ∀ x b, b ≤ d x ↔ b ≤ degree (L x) ∧ b ≤ degree (R x)) :
    ∃ F : X → Oracle, Measurable F ∧ ∀ x, degree (F x) = d x := by
  let C : ℕ → X → Oracle := fun n x => programOutput (codeEnumeration n) (L x)
  have hC (n : ℕ) : Measurable (C n) := (programOutput_measurable _).comp hL
  let S : X → ℕ → Prop := fun x n =>
    Reduces (C n x) (L x) ∧ Reduces (C n x) (R x) ∧
    ∀ k, Reduces (C k x) (L x) ∧ Reduces (C k x) (R x) → Reduces (C k x) (C n x)
  have hS (n : ℕ) : MeasurableSet {x | S x n} := by
    have hb (k : ℕ) : MeasurableSet {x | Reduces (C k x) (L x) ∧ Reduces (C k x) (R x)} :=
      (reduces_measurable _ _ (hC k) hL).inter (reduces_measurable _ _ (hC k) hR)
    have hm : MeasurableSet {x | ∀ k, Reduces (C k x) (L x) ∧ Reduces (C k x) (R x) → Reduces (C k x) (C n x)} := by
      simp only [Set.ofPred_forall]
      apply MeasurableSet.iInter
      intro k
      have he : {x | Reduces (C k x) (L x) ∧ Reduces (C k x) (R x) → Reduces (C k x) (C n x)} =
          {x | Reduces (C k x) (L x) ∧ Reduces (C k x) (R x)}ᶜ ∪
          {x | Reduces (C k x) (C n x)} := by ext x; simp only [mem_ofPred_eq, mem_union, mem_compl_iff]; tauto
      rw [he]
      exact (hb k).compl.union (reduces_measurable _ _ (hC k) (hC n))
    exact (reduces_measurable _ _ (hC n) hL).inter
      ((reduces_measurable _ _ (hC n) hR).inter hm)
  have hex : ∀ x, ∃ n, S x n := by
    intro x
    obtain ⟨B,hB⟩ := degree_surjective (d x)
    have hb : Reduces B (L x) ∧ Reduces B (R x) := (hd x (degree B)).mp (by rw [hB])
    obtain ⟨n,hn⟩ := exists_programOutput (L x) B hb.1
    have hc : C n x = B := hn
    refine ⟨n,?_,?_,?_⟩
    · simpa [hc] using hb.1
    · simpa [hc] using hb.2
    · intro k hk
      change degree (C k x) ≤ degree (C n x)
      rw [hc,hB]
      exact (hd x _).mpr hk
  let e := leastSuccess S hex
  have he : Measurable e := leastSuccess_measurable S hex hS
  have hout : Measurable (fun x => C (e x) x) := by
    apply Measurable.of_eval
    intro i
    apply measurable_to_countable'
    intro b
    have heq : {x | C (e x) x i = b} = ⋃ n : ℕ, {x | e x = n} ∩ {x | C n x i = b} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      exact ⟨fun h => ⟨e x,rfl,h⟩,fun ⟨n,hn,h⟩ => by simpa [hn] using h⟩
    change MeasurableSet {x | C (e x) x i = b}
    rw [heq]
    exact MeasurableSet.iUnion (fun n => (measurableSet_eq_fun he measurable_const).inter
      (measurableSet_eq_fun ((measurable_pi_apply i).comp (hC n)) measurable_const))
  refine ⟨fun x => C (e x) x,hout,?_⟩
  intro x
  have hs := leastSuccess_spec S hex x
  change S x (e x) at hs
  apply le_antisymm
  · exact (hd x _).mpr ⟨hs.1,hs.2.1⟩
  · obtain ⟨B,hB⟩ := degree_surjective (d x)
    have hb : Reduces B (L x) ∧ Reduces B (R x) := (hd x (degree B)).mp (by rw [hB])
    obtain ⟨n,hn⟩ := exists_programOutput (L x) B hb.1
    have hc : C n x = B := hn
    have hh := hs.2.2 n (by simpa [hc] using hb)
    change degree (C n x) ≤ degree (C (e x) x) at hh
    simpa [hc,hB] using hh

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericAssembly
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem representative_from_generic_coding (π : Degree ≃o Degree)
    (F : Oracle → Oracle) (hF : Measurable F)
    (C : Oracle → Oracle → Oracle) (hC : Measurable (Function.uncurry C))
    (G : Bool → Oracle → Oracle) (hG : ∀ b, Measurable (G b))
    (hgen : ∀ A b, degree (F (G b A)) = π (degree (G b A)))
    (hcoded : ∀ A b, degree (F (C A (G b A))) = π (degree (C A (G b A))))
    (hideal : ∀ A a, a ≤ degree A ↔
      a ≤ degree (join (C A (G false A)) (G false A)) ∧
      a ≤ degree (join (C A (G true A)) (G true A))) :
    ∃ H : Oracle → Oracle, Measurable H ∧ ∀ A, degree (H A) = π (degree A) := by
  let L : Bool → Oracle → Oracle := fun b A => join (F (C A (G b A))) (F (G b A))
  have hL (b : Bool) : Measurable (L b) :=
    join_measurable _ _ (hF.comp (hC.comp (measurable_id.prodMk (hG b)))) (hF.comp (hG b))
  have hdegree (A : Oracle) (b : Bool) :
      degree (L b A) = π (degree (join (C A (G b A)) (G b A))) := by
    dsimp only [L]
    change degree (F (C A (G b A))) ⊔ degree (F (G b A)) =
      π (degree (C A (G b A)) ⊔ degree (G b A))
    rw [hcoded A b, hgen A b, π.map_sup]
  apply borel_of_ideal_intersection (L false) (L true) (hL false) (hL true)
    (fun A => π (degree A))
  intro A a
  rw [hdegree A false,hdegree A true]
  exact common_lower_transport π _ _ _ (hideal A) a

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_RepresentationEndgame
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity

theorem representative_from_selected_generics (π : Degree ≃o Degree)
    (F : Oracle → Oracle) (hF : Measurable F)
    (G : Bool → Oracle → Oracle) (hG : ∀ b, Measurable (G b))
    (hinfinite : ∀ A b, GenericCoding.InfiniteOdd (G b A))
    (hgen : ∀ A b, degree (F (G b A)) = π (degree (G b A)))
    (hcoded : ∀ A b, degree (F (GenericCoding.code A (G b A))) =
      π (degree (GenericCoding.code A (G b A))))
    (hideal : ∀ A a, a ≤ degree A ↔
      a ≤ degree (join A (G false A)) ∧ a ≤ degree (join A (G true A))) :
    ∃ H : Oracle → Oracle, Measurable H ∧ ∀ A, degree (H A) = π (degree A) := by
  apply representative_from_generic_coding π F hF GenericCoding.code GenericCoding.code_measurable
    G hG hgen hcoded
  intro A a
  rw [GenericCoding.join_degree_eq A (G false A) (hinfinite A false),
    GenericCoding.join_degree_eq A (G true A) (hinfinite A true)]
  exact hideal A a

theorem representative_from_generic_program (π : Degree ≃o Degree) (p : OracleCode) (P : Oracle)
    (G : Bool → Oracle → Oracle) (hG : ∀ b, Measurable (G b))
    (hinfinite : ∀ A b, GenericCoding.InfiniteOdd (G b A))
    (hgen : ∀ A b, ∃ B, OracleCode.eval (oracleFunction (join (G b A) P)) p = oracleFunction B ∧
      degree B = π (degree (G b A)))
    (hcoded : ∀ A b, ∃ B, OracleCode.eval (oracleFunction (join (GenericCoding.code A (G b A)) P)) p =
      oracleFunction B ∧ degree B = π (degree (GenericCoding.code A (G b A))))
    (hideal : ∀ A a, a ≤ degree A ↔
      a ≤ degree (join A (G false A)) ∧ a ≤ degree (join A (G true A))) :
    ∃ H : Oracle → Oracle, Measurable H ∧ ∀ A, degree (H A) = π (degree A) := by
  let F : Oracle → Oracle := fun Y => programOutput p (join Y P)
  have hF : Measurable F := (programOutput_measurable p).comp
    (join_measurable _ _ measurable_id measurable_const)
  apply representative_from_selected_generics π F hF G hG hinfinite
  · intro A b
    obtain ⟨B,hp,hB⟩ := hgen A b
    change degree (programOutput p (join (G b A) P)) = _
    rw [programOutput_eq p _ B hp]
    exact hB
  · intro A b
    obtain ⟨B,hp,hB⟩ := hcoded A b
    change degree (programOutput p (join (GenericCoding.code A (G b A)) P)) = _
    rw [programOutput_eq p _ B hp]
    exact hB
  · exact hideal

end TuringRigidity

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GenericRepresentation
attribute [-instance] _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity
open FiniteShuffle ShuffleRequirements PairGenericSelection

theorem selected_generic_ideal (D : ℕ → List Bool → Prop) (hd : ∀ n, DenseOpen (D n)) :
    ∃ G : Bool → Oracle → Oracle, (∀ b, Measurable (G b)) ∧
      (∀ A b, GenericFor D (G b A) ∧ GenericCoding.InfiniteOdd (G b A) ∧
        ∀ Y, GenericFor D (GenericCoding.code Y (G b A))) ∧
      ∀ A a, a ≤ degree A ↔ a ≤ degree (join A (G false A)) ∧ a ≤ degree (join A (G true A)) := by
  obtain ⟨Z,hZ,hgeneric,hfamily⟩ := borel_pair_selection D hd CommonIdeal.family
    CommonIdeal.family_dense CommonIdeal.family_measurable
  refine ⟨fun b A => column b (Z A),fun b => (column_measurable b).comp hZ,hgeneric,?_⟩
  intro A a
  exact CommonIdeal.ideal_of_family A (Z A) (hfamily A) a

theorem borel_of_generic_program (π : Degree ≃o Degree) (h : GenericProgramRepresentation π) :
    ∃ H : Oracle → Oracle, Measurable H ∧ ∀ A, degree (H A) = π (degree A) := by
  obtain ⟨D,hD,P,p,hp⟩ := h
  obtain ⟨G,hG,hgeneric,hideal⟩ := selected_generic_ideal D hD
  exact representative_from_generic_program π p P G hG
    (fun A b => (hgeneric A b).2.1)
    (fun A b => hp (G b A) (hgeneric A b).1)
    (fun A b => hp (GenericCoding.code A (G b A)) ((hgeneric A b).2.2 A)) hideal

end TuringRigidity

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_CohenForcing_InternalCohenRequirements
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableCertificate _root_.OAI.TuringRigidity.CertificateMatrix.instDecidableReads _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.IndexMatrix.instDecidableValidMatrix _root_.OAI.TuringRigidity.OrderNormalForm.instDecidableOrderMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing
open FiniteShuffle ShuffleRequirements
attribute [local instance] BoundedSetTheory.InternalCollapse.order
  BoundedSetTheory.InternalCollapse.collapsePreorder

theorem openRequirement_dense (E : ZFSet.{0})
    (hE : CountableForcing.Dense {p : Condition | wordCode p.word ∈ E}) :
    DenseOpen (openRequirement E) := by
  constructor
  · intro s
    obtain ⟨t,ht,htE⟩ := hE ⟨s⟩
    exact ⟨t.word,ht,t,List.prefix_rfl,htE⟩
  · rintro s t hst ⟨q,hqs,hq⟩
    exact ⟨q,hqs.trans hst,hq⟩

theorem ground_family (M : ZFSet.{0}) [Countable (Conditions M)] (hne : ∃ x, x ∈ M) :
    ∃ D : ℕ → List Bool → Prop, (∀ n, DenseOpen (D n)) ∧
      ∀ A : Oracle, ShuffleRequirements.GenericFor D A ↔
        AtomicForcing.GroundGeneric M (pushFilter (realFilter A)) := by
  classical
  obtain ⟨x,hx⟩ := hne
  obtain ⟨m,_⟩ := label_surjective M hx
  let _ : Nonempty (Conditions M) := ⟨m⟩
  obtain ⟨e,he⟩ := exists_surjective_nat (Conditions M)
  let good (n : ℕ) := CountableForcing.Dense {p : Condition | wordCode p.word ∈ label M (e n)}
  let D (n : ℕ) (s : List Bool) := if good n then openRequirement (label M (e n)) s else True
  have hD : ∀ n, DenseOpen (D n) := by
    intro n; dsimp only [D]; split
    · exact openRequirement_dense _ ‹good n›
    · exact ⟨fun s => ⟨s,List.prefix_rfl,True.intro⟩,fun _ _ _ _ => True.intro⟩
  refine ⟨D,hD,fun A => ?_⟩
  rw [groundGeneric_iff,pull_push]
  constructor
  · intro h E hEM hE
    obtain ⟨q,hq⟩ := label_surjective M hEM
    obtain ⟨n,rfl⟩ := he q
    have hg : good n := by dsimp only [good]; rw [hq]; exact hE
    obtain ⟨s,hs,hAs⟩ := h n
    dsimp only [D] at hs
    rw [ite_eq_left hg] at hs
    obtain ⟨t,ht,htE⟩ := hs
    exact ⟨t,realizes_mono ht hAs,by simpa only [hq] using htE⟩
  · intro h n
    by_cases hg : good n
    · obtain ⟨t,ht,htE⟩ := h (label M (e n)) (label_mem M (e n)) hg
      exact ⟨t.word,by dsimp only [D]; rw [ite_eq_left hg]; exact ⟨t,List.prefix_rfl,htE⟩,ht⟩
    · exact ⟨[],by dsimp only [D]; rw [ite_eq_right hg]; trivial,by intro i hi; simp at hi⟩

end TuringRigidity.InternalCohen

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GroundArithmeticGeneric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.GroundArithmeticGeneric
open TransitiveNameModel BoundedSetTheory UniformArithmetic ArithmeticPrefixForcing
open InternalCohen CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem ground_arithmetic (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (O : Oracles) (hO : ∀ i, realCode (O i) ∈ M) (G : Oracle)
    (hG : AtomicForcing.GroundGeneric M (pushFilter (realFilter G))) :
    Generic O G := by
  intro D hD hd
  let A := arithmeticReal (fun O n => D O (EncodedForcing.word n)) O
  have hA : realCode A ∈ M := sourceT_arithmetic_comprehension M hM hT hD O hO
  have hspec (s : List Bool) : wordCode s ∈ wordImage A ↔ D O s :=
    wordImage_spec (D O) A (arithmeticReal_true _ O) s
  have hden : Dense {q : Condition | wordCode q.word ∈ wordImage A} := by
    intro q
    obtain ⟨s,hqs,hs⟩ := hd.1 q.word
    exact ⟨⟨s⟩,hqs,(hspec s).mpr hs⟩
  obtain ⟨q,hq,hqD⟩ := (groundGeneric_iff M _).mp hG (wordImage A)
    (wordImage_mem M hM hT A hA) hden
  rw [pull_push] at hq
  exact ⟨q.word,(hspec q.word).mp hqD,hq⟩

end TuringRigidity.GroundArithmeticGeneric

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ManuscriptMain
open TransitiveNameModel BoundedSetTheory CountableForcing GenericIdentity OracleJump

theorem generic_program_representation (π : Degree ≃o Degree) : GenericProgramRepresentation π := by
  obtain ⟨R,p,_,hrep⟩ := RelativeConstructible.global_arithmetic_generic_program π
  obtain ⟨M,hM,hT,hcount,_,_,hRM,_,_⟩ :=
    PrescribedFirstUncountable.prescribed_covering_model_with_omega_one π (fun _ => R)
  let := hcount
  have hP := sourceT_real_iterate M hM hT (hRM 0) 5
  obtain ⟨D,hD,hground⟩ := InternalCohen.ground_family M ⟨realCode.{0} R,hRM 0⟩
  refine ⟨D,hD,iterate R 5,p,?_⟩
  intro A hA
  have ha := GroundArithmeticGeneric.ground_arithmetic M hM hT (fun _ => iterate R 5)
    (fun _ => hP) A ((hground A).mp hA)
  obtain ⟨ht,hπ⟩ := hrep A ha
  exact ⟨value p (iterate R 5) A,(total_iff p (iterate R 5) A).mp ht,hπ⟩

theorem borel_representation : BorelRepresentation :=
  fun π => borel_of_generic_program π (generic_program_representation π)

theorem rigidity_oai : MainTheorem := main_of_representation borel_representation

end TuringRigidity.ManuscriptMain

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.ManuscriptMain.rigidity_oai := @OAI.TuringRigidity.ManuscriptMain.rigidity_oai
