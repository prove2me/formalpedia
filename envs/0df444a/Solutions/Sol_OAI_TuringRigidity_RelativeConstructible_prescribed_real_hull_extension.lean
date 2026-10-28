-- Prove2me | solution 1 for OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:33:39.283786+00:00
-- url     : https://prove2.me/submissions/b31bfe93-7e83-40df-8691-ad7bd8adde82

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_DegreeRigidity
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_FullSetForcing_prescribed_one_real_names
import Theorems.Thm_OAI_TuringRigidity_OriginalRealDefinitionTransport_original_definition_transport
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_definablePower_mem
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_ground_idealSet_mem_relativeModel
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_persistent_modelIdeal_graph_mem_relativeModel
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_stageCertificate_uniformSigma
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_uniform_cohen_definition_extension
import Theorems.Thm_OAI_TuringRigidity_RelativeConstructible_uniform_hierarchy_certificate

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
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
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

theorem degree_equal_arith {A B : OracleFamily} (hA : ArithmeticOracle A)
    (hB : ArithmeticOracle B) : Arith (fun O v => degree (A O v) = degree (B O v)) :=
  ((reduces_arith hA hB).and (reduces_arith hB hA)).congr
    (fun O v => (degree_eq_iff (A O v) (B O v)).symm)

end
end TuringRigidity.UniformArithmetic

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_BoundedSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory
universe u

theorem eval_congr (φ : BoundedSetTheory.Formula) (e e' : ℕ → ZFSet.{u})
    (h : ∀ i, i < bound φ → e i = e' i) : φ.Eval e ↔ φ.Eval e' := by
  induction φ generalizing e e' with
  | equal i j => simp only [Formula.Eval,h i (by simp [bound]),h j (by simp [bound])]
  | member i j => simp only [Formula.Eval,h i (by simp [bound]),h j (by simp [bound])]
  | conj φ ψ ihφ ihψ =>
    exact and_congr (ihφ e e' (fun i hi => h i (by simp only [bound]; omega)))
      (ihψ e e' (fun i hi => h i (by simp only [bound]; omega)))
  | neg φ ih => exact not_congr (ih e e' h)
  | existsMem i φ ih =>
    have hei := h i (by simp only [bound]; omega)
    simp only [Formula.Eval,hei]
    apply exists_congr
    intro x
    apply and_congr_right
    intro _
    apply ih
    intro n hn
    cases n with
    | zero => rfl
    | succ n => exact h n (by simp only [bound]; omega)

end TuringRigidity.BoundedForcing

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Computability_ArithmeticParameterFormula
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open UniformArithmetic
universe u
namespace Formula

theorem oracleParameters_spec {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P)
    (o Q n : ℕ) (r : ℕ → ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (O : Oracles) (hO : ∀ i, e (r i) = realCode (O i)) (N : ℕ) (hn : e n = natSet N) :
    (oracleParameters φ o Q n r).Eval e ↔ P O N := by
  rw [oracleParameters,eval_rename]
  have he : (fun i => e (oracleParameterVars o Q n r i)) = arithmeticEnv (e Q) O N := by
    funext i
    rcases i with _|i; exact hn
    rcases i with _|i; exact ho
    rcases i with _|i; rfl
    exact hO i
  rw [he]
  exact hφ _ hQ _ _

theorem twoOracles_spec {φ : Formula} {P : Predicate} (hφ : DefinesArithmetic.{u} φ P)
    (o Q n x y : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q)
    (A B : Oracle) (hx : e x = realCode A) (hy : e y = realCode B)
    (N : ℕ) (hn : e n = natSet N) :
    (twoOracles φ o Q n x y).Eval e ↔ P (fun i => if i = 0 then A else B) N := by
  apply oracleParameters_spec hφ o Q n _ e ho hQ _ _ N hn
  intro i; by_cases hi : i = 0 <;> simp only [hi,ite_true,ite_false] <;> assumption
end Formula

theorem degree_equality_bounded : ∃ φ : Formula, ∀ o Q z x y : ℕ, ∀ e : ℕ → ZFSet.{u},
    e o = ZFSet.omega → (∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) →
    e z = natSet 0 → ∀ A B : Oracle, e x = realCode A → e y = realCode B →
      ((Formula.twoOracles φ o Q z x y).Eval e ↔ degree A = degree B) := by
  have hp := degree_equal_arith (parameter_arith 0) (parameter_arith 1)
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u} hp
  refine ⟨φ,?_⟩
  intro o Q z x y e ho hQ hz A B hx hy
  simpa using
    Formula.twoOracles_spec hφ o Q z x y e ho hQ A B hx hy 0 hz

end TuringRigidity.BoundedSetTheory

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

end SentenceForm

end TuringRigidity.ElementaryModel

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_DefinablePower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem mem_definedSubset (A x : ZFSet.{u}) (p : SentenceForm)
    {n : ℕ} (v : Fin n → ZFSet.{u}) :
    x ∈ definedSubset A p v ↔ x ∈ A ∧ p.Sat (A : Set ZFSet) (cons x (tupleEnv v)) :=
  ZFSet.mem_sep

theorem definableOver_subset {A S : ZFSet.{u}} (h : DefinableOver A S) : S ⊆ A := by
  obtain ⟨n,p,v,_,_,rfl⟩ := h
  exact fun _ hx => (mem_definedSubset A _ p v).mp hx |>.1

theorem mem_definablePower (A S : ZFSet.{u}) :
    S ∈ definablePower A ↔ DefinableOver A S := by
  rw [definablePower,ZFSet.mem_sep]
  exact ⟨And.right,fun h => ⟨ZFSet.mem_powerset.mpr (definableOver_subset h),h⟩⟩

theorem self_mem_definablePower (A : ZFSet.{u}) : A ∈ definablePower A := by
  apply (mem_definablePower A A).mpr
  refine ⟨0,.equal 0 0,Fin.elim0,by decide,fun i => Fin.elim0 i,?_⟩
  apply ZFSet.ext; intro x
  simp [mem_definedSubset,SentenceForm.Sat]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

theorem mem_seed (R x : ZFSet.{u}) :
    x ∈ seed R ↔ ∃ n : ℕ, x ∈ iterUnion n ({R} : ZFSet) := by
  rw [seed,ZFSet.mem_sUnion]
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨n,rfl⟩ := ZFSet.mem_range.mp ha
    exact ⟨n,hx⟩
  · rintro ⟨n,hx⟩
    exact ⟨_,ZFSet.mem_range_self (f := fun index : ℕ => iterUnion index ({R} : ZFSet.{u})) n,hx⟩

theorem parameter_mem_seed (R : ZFSet.{u}) : R ∈ seed R :=
  (mem_seed R R).mpr ⟨0,ZFSet.mem_singleton.mpr rfl⟩

theorem seed_transitive (R : ZFSet.{u}) : Transitive (seed R) := by
  intro x hx y hy
  obtain ⟨n,hn⟩ := (mem_seed R x).mp hx
  exact (mem_seed R y).mpr ⟨n+1,ZFSet.mem_sUnion.mpr ⟨x,hn,hy⟩⟩

theorem parameter_subset_seed (R : ZFSet.{u}) : R ⊆ seed R :=
  fun x hx => seed_transitive R R (parameter_mem_seed R) x hx

theorem seed_minimal (R M : ZFSet.{u}) (hM : Transitive M) (hR : R ∈ M) : seed R ⊆ M := by
  intro x hx
  obtain ⟨n,hn⟩ := (mem_seed R x).mp hx
  have sub : ∀ n : ℕ, iterUnion n ({R} : ZFSet) ⊆ M := by
    intro n
    induction n with
    | zero => intro y hy; obtain rfl := ZFSet.mem_singleton.mp hy; exact hR
    | succ n ih =>
      intro y hy
      obtain ⟨z,hz,hy⟩ := ZFSet.mem_sUnion.mp hy
      exact hM z (ih hz) y hy
  exact sub n hn

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleStages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel
universe u

theorem mem_stage (R o x : ZFSet.{u}) :
    x ∈ stage R o ↔ x ∈ seed R ∨ ∃ i ∈ o, x ∈ definablePower (stage R i) := by
  rw [stage,ZFSet.mem_union,ZFSet.mem_sUnion]
  apply or_congr_right
  constructor
  · rintro ⟨a,ha,hx⟩
    obtain ⟨i,rfl⟩ := ZFSet.mem_range.mp ha
    exact ⟨_,((equivShrink o).symm i).property,hx⟩
  · rintro ⟨i,hi,hx⟩
    refine ⟨_,ZFSet.mem_range.mpr ⟨equivShrink o ⟨i,hi⟩,rfl⟩,?_⟩
    simpa using hx

theorem seed_subset_stage (R o : ZFSet.{u}) : seed R ⊆ stage R o :=
  fun x hx => (mem_stage R o x).mpr (Or.inl hx)

theorem stage_zero (R : ZFSet.{u}) : stage R ∅ = seed R := by
  apply ZFSet.ext; intro x
  simp [mem_stage]

theorem definablePower_subset_stage (R : ZFSet.{u}) {i j : ZFSet.{u}} (hi : i ∈ j) :
    definablePower (stage R i) ⊆ stage R j :=
  fun x hx => (mem_stage R j x).mpr (Or.inr ⟨i,hi,hx⟩)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_ConstructibleGroundReals
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

theorem groundReals_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    groundReals M ∈ M := by
  obtain ⟨R,hR,hdef⟩ := internal_power M hM hT.powerSet (sourceT_omega_mem M hM hT)
  have heq : R = groundReals M := by
    apply ZFSet.ext; intro x
    exact (hdef x).trans (mem_groundReals M x).symm
  exact heq ▸ hR

end TuringRigidity.RelativeConstructible

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

theorem realSet_oracleOf {x : ZFSet.{u}} (hx : x ⊆ ZFSet.omega) :
    realSet (oracleOf x) = x := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨n,rfl⟩ := (mem_omega y).mp (realSet_subset _ hy)
    simpa [oracleOf] using (nat_mem_realSet _ n).mp hy
  · intro hy
    obtain ⟨n,rfl⟩ := (mem_omega y).mp (hx hy)
    apply (nat_mem_realSet _ _).mpr
    simpa [oracleOf] using hy

end
end TuringRigidity.SetModelReals

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

theorem Definable.existsMem (h : Definable M P) (i : ℕ) :
    Definable M (fun e => ∃ x ∈ e i, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.existsMem (2*i) (p.rename bindSlots),d,hd,?_⟩
  intro e
  simp only [Formula.Eval,mix_even,Formula.eval_rename_comp,bind_mix,hp]

theorem member_definable (C : Context M) (i j : ℕ) : Definable M (fun e => e i ∈ e j) :=
  ⟨.member (2*i) (2*j),fun _ => ZFSet.omega,fun _ => C.omega_mem,fun e => by simp [Formula.Eval]⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SetSatisfactionBounded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem setBounded_eval (p : SentenceForm) (a : ℕ) (v : ℕ → ℕ)
    (e : ℕ → ZFSet.{u}) :
    (setBounded p a v).Eval e ↔ p.Sat (e a : Set ZFSet) (fun i => e (v i)) := by
  induction p generalizing a v e with
  | equal => rfl
  | member => rfl
  | conj p q ihp ihq => exact and_congr (ihp a v e) (ihq a v e)
  | neg p ih => exact not_congr (ih a v e)
  | ex p ih =>
    simp only [setBounded,Formula.Eval,SentenceForm.Sat]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    have he : (fun i => cons x e (match i with | 0 => 0 | j+1 => v j+1)) =
        cons x (fun i => e (v i)) := by funext i; cases i <;> rfl
    exact (ih (a+1) _ (cons x e)).trans (he ▸ Iff.rfl)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceSupportFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open ElementaryModel RelativeConstructible BoundedSetTheory TransitiveNameModel
open BoundedDefinability SetModelFunctions SetModelReals
universe u

variable {M : ZFSet.{u}}

theorem defPairMem (C : Context M) (i j g : ℕ) :
    Definable M (fun e => ZFSet.pair (e i) (e j) ∈ e g) :=
  ⟨.pairMem (2*i) (2*j) (2*g),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by simp only [Formula.eval_pairMem,mix_even]⟩

end TuringRigidity.SentenceCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchyGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem HierarchyGraph.correct {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (x : ZFSet.{u}) (hx : x ∈ d)
    (v : ZFSet.{u}) (hv : v ∈ r) (hfv : ZFSet.pair x v ∈ f) :
    v = definablePower (stage R x) := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    obtain ⟨A,_,hs,rfl⟩ := h.2.2 x hx v hv hfv
    congr 1
    apply ZFSet.ext; intro z
    rw [mem_stage]
    constructor
    · intro hz
      rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
      · exact Or.inl hz
      · rw [ih y hy (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,hz⟩
    · rintro (hz|⟨y,hy,hz⟩)
      · exact hs.1 hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← ih y hy (h.1 x hx y hy) w hw hfw] at hz
        exact hs.2.2 y hy w hw hfw hz

theorem HierarchyGraph.mem_iff {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (definablePower (stage R x)) := by
  constructor
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := h.2.1.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx v hv hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := h.2.1.2 x hx
    rw [← h.correct x hx v hv hfv]
    exact hfv

theorem HierarchyGraph.unique {M N R d r t f g : ZFSet.{u}}
    (hf : HierarchyGraph M (seed R) d r f) (hg : HierarchyGraph N (seed R) d t g) : f = g := by
  apply ZFSet.ext; intro z
  exact (hf.mem_iff z).trans (hg.mem_iff z).symm

theorem mem_stageImage (s x f z : ZFSet.{u}) :
    z ∈ stageImage s x f ↔ z ∈ s ∨ ∃ y ∈ x, ∃ w, ZFSet.pair y w ∈ f ∧ z ∈ w := by
  rw [stageImage,ZFSet.mem_union,ZFSet.mem_sep]
  apply or_congr_right
  constructor
  · rintro ⟨_,y,hy,w,_,hf,hz⟩; exact ⟨y,hy,w,hf,hz⟩
  · rintro ⟨y,hy,w,hf,hz⟩
    have hw := second_mem_doubleUnion hf
    exact ⟨ZFSet.mem_sUnion.mpr ⟨w,hw,hz⟩,y,hy,w,hw,hf,hz⟩

theorem stageImage_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {s x f : ZFSet.{u}} (hs : s ∈ M) (hx : x ∈ M) (hf : f ∈ M) : stageImage s x f ∈ M := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hr := iterUnion_mem M hM hT.union hf 2
  have hd := (((defPairMem C 1 0 4).and (member_definable C 2 0)).existsMem 4).existsMem 1
  let e := cons x (cons f (fun _ => iterUnion 2 f))
  have he : ∀ i, e i ∈ M := by intro i; rcases i with _|_|i; exact hx; exact hf; exact hr
  exact binary_union_mem M hM hT.pairing hT.union hs
    (hd.sep_mem C e he (union_mem M hM hT.union hr))

theorem hierarchyGraph_of_mem_iff (M R d f : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hfM : f ∈ M) (hd : Transitive d)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (definablePower (stage R x))) :
    HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = definablePower (stage R x) := by
    rw [hf]
    constructor
    · rintro ⟨y,hy,he⟩
      obtain ⟨rfl,hv⟩ := ZFSet.pair_inj.mp he
      exact ⟨hy,hv⟩
    · rintro ⟨hx,rfl⟩; exact ⟨x,hx,rfl⟩
  refine ⟨hd,⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (hf z).mp hz
    exact ⟨x,hx,_,second_mem_doubleUnion hz,rfl⟩
  · intro x hx
    have hp := (hpair x _).mpr ⟨hx,rfl⟩
    exact ⟨_,second_mem_doubleUnion hp,hp,fun v _ hv => (hpair x v).mp hv |>.2⟩
  · intro x hx v _ hv
    have he := (hpair x v).mp hv |>.2
    subst v
    have hA : stageImage (seed R) x f = stage R x := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,mem_stage]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        rw [(hpair y w).mp hw |>.2] at hz
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hpair y _).mpr ⟨hd x hx y hy,rfl⟩,hz⟩
    refine ⟨stage R x,hA ▸ stageImage_mem M hM hT hs (hM d hdM x hx) hfM,?_,rfl⟩
    refine ⟨seed_subset_stage R x,?_,?_⟩
    · intro z hz
      rcases (mem_stage R x z).mp hz with hz|⟨y,hy,hz⟩
      · exact Or.inl hz
      · have hp := (hpair y _).mpr ⟨hd x hx y hy,rfl⟩
        exact Or.inr ⟨y,hy,_,second_mem_doubleUnion hp,hp,hz⟩
    · intro y hy w _ hw
      rw [(hpair y w).mp hw |>.2]
      exact definablePower_subset_stage R hy

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalHierarchyRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem internal_hierarchyGraph (M R d q : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hs : seed R ∈ M) (hdM : d ∈ M) (hqM : q ∈ M) (hd : Transitive d)
    (hq : ∀ c, c ∈ q ↔ c ∈ M ∧ c ⊆ d) (x : ZFSet.{u}) (hx : x ∈ d) :
    ∃ f ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q x) (iterUnion 2 f) f := by
  let hP := hT.pairing
  let hU := hT.union
  let hS := hT.separation.finitePrefix.bounded
  let hR := hT.replacement.finitePrefix
  obtain ⟨p,e,he,hp⟩ := uniform_hierarchy_certificate M R d q hM hT hs hdM hqM hd hq
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have hxM := hM d hdM x hx
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) :
        p.Realize M (cons f (cons y e)) ↔
          ∃ r ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q y) r f :=
      hp y (hd x hx y hy) f hf
    obtain ⟨b,hb,hbdef⟩ := hR p e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M hM hU hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, HierarchyGraph M (seed R) (_root_.OAI.TuringRigidity.BoundedSetTheory.hull d q y) r f := by
      constructor
      · intro hf
        have hfM := hM b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hd x hx y hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M hM hU hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔
        ∃ y ∈ x, ∃ w ∈ _root_.OAI.TuringRigidity.BoundedSetTheory.hull d q y, z = ZFSet.pair w (definablePower (stage R w)) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        exact ⟨y,hy,(hfg.mem_iff z).mp hzf⟩
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (hd x hx y hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hU hf 2,hfg⟩,(hfg.mem_iff z).mpr ⟨w,hw,hz⟩⟩
    have hvalue : stageImage (seed R) x g = stage R x := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,mem_stage]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hw,hz⟩
        obtain ⟨a,_,v,_,hp⟩ := (hg _).mp hw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr
          ⟨y,hy,y,self_mem_hull d q (hd x hx y hy),rfl⟩,hz⟩
    have hvM : definablePower (stage R x) ∈ M := definablePower_mem M _ hM hT
      (hvalue ▸ stageImage_mem M hM hT hs hxM hgM)
    let f := g ∪ ({ZFSet.pair x (definablePower (stage R x))} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hP hU hgM
      (singleton_mem M hM hP (orderedPair_mem M hM hP hxM hvM))
    refine ⟨f,hfM,hierarchyGraph_of_mem_iff M R _ f hM hT hs
      (hull_mem M d q hM hS hdM hqM hxM) hfM (hull_transitive d q x hd) ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (definablePower (stage R x))} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,w,hw,hz⟩|hz)
      · exact ⟨w,(hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mpr
          (Or.inr ⟨y,hy,hw⟩),hz⟩
      · exact ⟨x,self_mem_hull d q hx,hz⟩
    · rintro ⟨w,hw,hz⟩
      rcases (hull_unfold M d q hM hP hU hS hR hdM hqM hd hq hx w).mp hw with rfl|⟨y,hy,hw⟩
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,w,hw,hz⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalConstructibleHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem seed_mem (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) :
    seed R ∈ M := by
  obtain ⟨b,hb,hdef⟩ := collect_unionIterates M hM hT.pairing hT.union
    hT.replacement.finitePrefix (sourceT_omega_mem M hM hT)
    (singleton_mem M hM hT.pairing hR)
  have he : ZFSet.sUnion b = seed R := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sUnion,mem_seed]
    constructor
    · rintro ⟨a,ha,hz⟩
      obtain ⟨n,rfl⟩ := (hdef a).mp ha
      exact ⟨n,hz⟩
    · rintro ⟨n,hz⟩
      exact ⟨_,(hdef _).mpr ⟨n,rfl⟩,hz⟩
  exact he ▸ union_mem M hM hT.union hb

theorem internal_hierarchy_cover (M R o : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (ho : o ∈ M) :
    ∃ d ∈ M, ∃ f ∈ M, o ∈ d ∧
      HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  obtain ⟨c,hc,hct,hoc⟩ := internal_transitive_container M hM hT.pairing hT.union
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity ho
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hT.powerSet hc
  obtain ⟨f,hf,hfg⟩ := internal_hierarchyGraph M R c q hM hT (seed_mem M R hM hT hR)
    hc hq hct hqdef o hoc
  exact ⟨hull c q o,hull_mem M c q hM hT.separation.finitePrefix.bounded hc hq ho,
    f,hf,self_mem_hull c q hoc,hfg⟩

theorem stage_mem (M R o : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (ho : o ∈ M) : stage R o ∈ M := by
  obtain ⟨d,_,f,hf,hod,hfg⟩ := internal_hierarchy_cover M R o hM hT hR ho
  obtain ⟨v,hv,hfv,_⟩ := hfg.2.1.2 o hod
  have hvM : v ∈ M := hM _ (iterUnion_mem M hM hT.union hf 2) v hv
  rw [hfg.correct o hod v hv hfv] at hvM
  exact hM _ hvM _ (self_mem_definablePower (stage R o))

end TuringRigidity.RelativeConstructible

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

theorem internal_degreeCode (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ x ∈ R, ∃ B : Oracle, realCode B = x)
    {A : Oracle} (hA : A ∈ modelReals M) : degreeCode R A ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet hS hω
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => realCode A)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hω
    rcases i with _|i; exact hQM
    rcases i with _|i; exact hz
    exact hA
  let D := ZFSet.sep (fun x => (Formula.twoOracles φ 1 2 3 0 4).Eval (cons x e)) R
  have hD : D ∈ M := sep_mem M hM hS _ e he hRM
  have hcode : degreeCode R A = D := by
    apply ZFSet.ext; intro x
    by_cases hx : x ∈ R
    · obtain ⟨B,rfl⟩ := hR x hx
      rw [realCode_mem_degreeCode,ZFSet.mem_sep]
      rw [hφ 1 2 3 0 4 (cons (realCode B) e) rfl hQ rfl B A rfl rfl]
    · simp only [degreeCode,D,ZFSet.mem_sep,hx,false_and]
  rw [hcode]
  exact hD

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_DegreeSetFormula
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
universe u

namespace Formula

theorem degreeSet_spec {φ : Formula} (hφ : DegreeEqualityFormula.{u} φ)
    (o Q z R x D : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w)
    (A : Oracle) (hA : e x = realCode A) :
    (degreeSet φ o Q z R x D).Eval e ↔ e D = degreeCode (e R) A := by
  simp only [degreeSet,Formula.Eval,eval_subset,eval_allMem,eval_iff,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro w
    by_cases hw : w ∈ e R
    · obtain ⟨B,rfl⟩ := hR w hw
      rw [realCode_mem_degreeCode]
      have hh := (h _ hw).trans (hφ (o+1) (Q+1) (z+1) 0 (x+1) (cons (realCode B) e)
        ho hQ hz B A rfl hA)
      exact hh.trans (and_iff_right hw).symm
    · exact ⟨fun h => False.elim (hw (hsub h)),fun h => False.elim (hw (degreeCode_subset _ _ h))⟩
  · intro hd
    refine ⟨hd.symm ▸ degreeCode_subset (e R) A,?_⟩
    intro w hw
    obtain ⟨B,rfl⟩ := hR w hw
    rw [hd,realCode_mem_degreeCode,and_iff_right hw]
    exact (hφ (o+1) (Q+1) (z+1) 0 (x+1) (cons (realCode B) e) ho hQ hz B A rfl hA).symm
end Formula

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeUniverse
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
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

namespace Formula

theorem degreeUniverseMember_spec {φ : Formula} (hφ : DegreeEqualityFormula.{u} φ)
    (o Q z R D : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ f : ℕ → ℕ, ∀ k, finiteNaturalGraph f k ∈ e Q) (hz : e z = natSet 0)
    (hR : ∀ w ∈ e R, ∃ B : Oracle, realCode B = w) :
    (degreeUniverseMember φ o Q z R D).Eval e ↔ e D ∈ degreeUniverse (e R) := by
  simp only [degreeUniverseMember,Formula.Eval]
  rw [mem_degreeUniverse]
  constructor
  · rintro ⟨w,hw,hd⟩
    obtain ⟨A,rfl⟩ := hR w hw
    exact ⟨A,hw,(degreeSet_spec hφ (o+1) (Q+1) (z+1) (R+1) 0 (D+1)
      (cons (realCode A) e) ho hQ hz hR A rfl).mp hd⟩
  · rintro ⟨A,hA,hd⟩
    exact ⟨realCode A,hA,(degreeSet_spec hφ (o+1) (Q+1) (z+1) (R+1) 0 (D+1)
      (cons (realCode A) e) ho hQ hz hR A rfl).mpr hd⟩
end Formula

theorem internal_degreeUniverse (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hRM : R ∈ M)
    (hR : ∀ w ∈ R, ∃ B : Oracle, realCode B = w) : degreeUniverse R ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  have hz : natSet.{u} 0 ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨0,rfl⟩)
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union hT.powerSet hS hω
  obtain ⟨P,hPM,hP⟩ := internal_power M hM hT.powerSet hRM
  obtain ⟨φ,hφ⟩ := degree_equality_bounded.{u}
  have hsub : degreeUniverse R ⊆ P := by
    intro D hD
    obtain ⟨A,hA,rfl⟩ := (mem_degreeUniverse R D).mp hD
    exact (hP _).mpr ⟨internal_degreeCode M hM hT R hRM hR (hM _ hRM _ hA),
      degreeCode_subset R A⟩
  let e := cons ZFSet.omega (cons Q (cons (natSet 0) (fun _ => R)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hω
    rcases i with _|i; exact hQM
    rcases i with _|i; exact hz
    exact hRM
  have hs := sep_mem M hM hS (Formula.degreeUniverseMember φ 1 2 3 4 0) e he hPM
  have heq : ZFSet.sep (fun D => (Formula.degreeUniverseMember φ 1 2 3 4 0).Eval (cons D e)) P =
      degreeUniverse R := by
    apply ZFSet.ext; intro D
    rw [ZFSet.mem_sep,Formula.degreeUniverseMember_spec hφ 1 2 3 4 0 (cons D e) rfl hQ rfl hR]
    exact ⟨And.right,fun h => ⟨hsub h,h⟩⟩
  exact heq ▸ hs

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ModelDegreeOrder
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic
universe u

theorem degreeCodeLE_actual (R : ZFSet.{u}) {A B : Oracle}
    (hA : realCode A ∈ R) (hB : realCode B ∈ R) :
    degreeCodeLE (degreeCode R A) (degreeCode R B) ↔ degree A ≤ degree B := by
  constructor
  · rintro ⟨C,D,hC,hD,hCD⟩
    have heC := ((realCode_mem_degreeCode R A C).mp hC).2
    have heD := ((realCode_mem_degreeCode R B D).mp hD).2
    rw [←heC,←heD]
    exact hCD
  · intro h
    exact ⟨A,B,(realCode_mem_degreeCode R A A).mpr ⟨hA,rfl⟩,
      (realCode_mem_degreeCode R B B).mpr ⟨hB,rfl⟩,h⟩

theorem mem_degreeOrder (R D E : ZFSet.{u}) :
    ZFSet.pair D E ∈ degreeOrder R ↔
      D ∈ degreeUniverse R ∧ E ∈ degreeUniverse R ∧ degreeCodeLE D E := by
  rw [degreeOrder,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,D',hD,E',hE,he,hle⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hD,hE,hle⟩
  · rintro ⟨hD,hE,hle⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨D,hD,E,hE,rfl⟩,D,hD,E,hE,rfl,hle⟩

theorem degreeOrder_actual (R : ZFSet.{u}) {A B : Oracle}
    (hA : realCode A ∈ R) (hB : realCode B ∈ R) :
    ZFSet.pair (degreeCode R A) (degreeCode R B) ∈ degreeOrder R ↔ degree A ≤ degree B := by
  rw [mem_degreeOrder,degreeCodeLE_actual R hA hB]
  exact ⟨fun h => h.2.2,fun h => ⟨(mem_degreeUniverse _ _).mpr ⟨A,hA,rfl⟩,
    (mem_degreeUniverse _ _).mpr ⟨B,hB,rfl⟩,h⟩⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel
universe u

theorem ground_seed_shape (M : ZFSet.{u}) (hM : Transitive M) :
    seed (groundReals M) = insert (groundReals M) (groundReals M) := by
  let R := groundReals M
  have htrans : Transitive (insert R R) := by
    intro a ha b hb
    rcases ZFSet.mem_insert_iff.mp ha with rfl|ha
    · exact ZFSet.mem_insert_iff.mpr (Or.inr hb)
    · obtain ⟨haM,haω⟩ := (mem_groundReals M a).mp ha
      have hbω := haω hb
      have hbsub : b ⊆ ZFSet.omega := fun z hz => omega_transitive b hbω z hz
      exact ZFSet.mem_insert_iff.mpr (Or.inr ((mem_groundReals M b).mpr ⟨hM a haM b hb,hbsub⟩))
  apply ZFSet.ext; intro x
  constructor
  · exact fun hx => seed_minimal R _ htrans (ZFSet.mem_insert R R) hx
  · intro hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact parameter_mem_seed R
    · exact parameter_subset_seed R hx

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformSeparationName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem uniform_separation_name (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : Separation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : BoundedSetTheory.Formula) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ B ∈ M, B ⊆ a.support (label c) ∧
      ∀ (G : GenericFilter (Conditions c)), GroundGeneric M G → ∀ x,
      x ∈ (a.restrict (label c) B).val G.carrier ↔ x ∈ a.val G.carrier ∧
        φ.Eval (cons x (fun i => (e i).val G.carrier)) := by
  obtain ⟨d,hd,hdT,had,hnd⟩ := finite_container M hM hP hU hS hR hI
    (fun i => (push a e i).encode (label c))
    (by intro i; cases i <;> simp only [push_zero,push_succ]; exact ha; exact he _) (bound φ+2)
  let e' := truncate (bound φ) e
  have he' (i) : (e' i).encode (label c) ∈ d := by
    dsimp only [e',truncate]
    split
    · exact hnd (i+1) (by omega)
    · exact hnd 1 (by omega)
  have hai (i) : (a.child i).encode (label c) ∈ d :=
    names_childClosed d c hdT a had _ (child_relation a i)
  have hpush (i) (n) : (push (a.child i) e' n).encode (label c) ∈ d := by
    cases n with
    | zero => exact hai i
    | succ n => exact he' n
  obtain ⟨f,hf,hfG⟩ := internal_atomic_graph M hM hP hU hPow hS hd hc hoM
  let k := ZFSet.prod d d
  have hk : k ∈ M := product_mem M hM hP hU hPow hS hd hd
  let env := cons d (cons c (cons k (cons o (cons f (fun i => (e' i).encode (label c))))))
  have henv : ∀ i, env i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact hc
    rcases i with _|i; exact hk
    rcases i with _|i; exact hoM
    rcases i with _|i; exact hf
    exact hM d hd _ (he' i)
  let ψ := Formula.existsMem 1 (.existsMem 3 (.conj (Formula.orderedPair 2 1 0)
    (code φ 3 4 5 6 7 (push 1 (fun i => i+8)) 0)))
  let B := ZFSet.sep (fun z => ψ.Eval (cons z env)) (a.support (label c))
  have hBM : B ∈ M := sep_mem M hM hS ψ env henv
    (support_mem M hM hP hU hPow hS hc hoM ho a ha)
  have hBsub : B ⊆ a.support (label c) := fun z hz => (ZFSet.mem_sep.mp hz).1
  have query (i : a.arity) (q : Conditions c) (z : ZFSet.{u}) :=
    eval_code φ hdT ho hfG (push (a.child i) e') (hpush i) q
      (cons (label c q) (cons ((a.child i).encode (label c)) (cons z env)))
      3 4 5 6 7 (push 1 (fun n => n+8)) 0 ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
      (by intro n; cases n <;> rfl)
  have hB (i : a.arity) (q : Conditions c) (hq : q ≤ a.tag i) :
      ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ B ↔ Forces (push (a.child i) e') φ q := by
    have hs : ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ a.support (label c) :=
      ZFSet.mem_range.mpr ⟨⟨i,⟨q,hq⟩⟩,rfl⟩
    change _ ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep,and_iff_right hs]
    change (Formula.existsMem 1 _).Eval _ ↔ _
    simp only [Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,env]
    constructor
    · rintro ⟨x,hx,r,hr,hxr,hφ⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hxr
      exact (query i q _).mp hφ
    · intro hφ
      exact ⟨_,hai i,_,label_mem c q,rfl,(query i q _).mpr hφ⟩
  refine ⟨B,hBM,hBsub,?_⟩
  intro G hG
  have ht (i : a.arity) :
      φ.Eval (cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier)) ↔
        ∃ p ∈ G.carrier, Forces (push (a.child i) e') φ p := by
    have hfinite : φ.Eval (cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier)) ↔
        φ.Eval (fun n => (push (a.child i) e' n).val G.carrier) := by
      apply eval_congr
      intro n hn
      cases n with
      | zero => rfl
      | succ n =>
        simp only [cons_succ,push_succ]
        dsimp only [e',truncate]
        rw [ite_eq_left (by omega)]
    exact hfinite.trans (internal_bounded_truth M hM hP hU hPow hS hR hI hc hoM ho G hG φ _
      (fun n => hM d hd _ (hpush i n)))
  intro x
  constructor
  · intro hx
    have hxa := a.val_restrict_subset (label c) B G hx
    obtain ⟨i,q,hqi,hqb,hqG,hix⟩ := (a.mem_val_restrict (label c) B G.carrier x).mp hx
    have hφ := (ht i).mpr ⟨q,hqG,(hB i q hqi).mp hqb⟩
    exact ⟨hxa,hix ▸ hφ⟩
  · rintro ⟨hxa,hφ⟩
    obtain ⟨i,hi,hix⟩ := (a.mem_val_children G.carrier x).mp hxa
    obtain ⟨p,hp,hf⟩ := (ht i).mp (hix ▸ hφ)
    obtain ⟨q,hq,hqp,hqi⟩ := G.directed hp hi
    exact (a.mem_val_restrict (label c) B G.carrier x).mpr
      ⟨i,q,hqi,(hB i q hqi).mpr (forces_mono φ _ hqp hf),hq,hix⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformDefinedSubsetName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel RecursiveNames
open BoundedForcing AtomicForcing CountableForcing
universe u

theorem uniform_definedSubset_name (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r t : Conditions c, ZFSet.pair (label c r) (label c t) ∈ o ↔ r ≤ t)
    (A a : Name (Conditions c)) (hA : A.encode (label c) ∈ M)
    (ha : a.encode (label c) ∈ M) (φ : SentenceForm) :
    ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G →
        f.val G.carrier = definedSubset (A.val G.carrier) φ
          (fun _ : Fin φ.bound => a.val G.carrier) := by
  let e := push A (fun _ => a)
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    cases i; exact hA; exact ha
  let ψ := setBounded φ 1 (fun i => if i = 0 then 0 else 2)
  obtain ⟨B,hB,hBS,hval⟩ := uniform_separation_name M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity
      hc hoM ho ψ A hA e he
  refine ⟨A.restrict (label c) B,?_,?_⟩
  · rw [Name.encode_restrict _ _ _ hBS]; exact hB
  · intro G hG
    apply ZFSet.ext; intro x
    rw [hval G hG x,mem_definedSubset]
    apply and_congr_right; intro _
    rw [setBounded_eval]
    apply φ.finite_support
    intro i hi
    cases i with
    | zero => rfl
    | succ i =>
      change a.val G.carrier = tupleEnv (fun _ : Fin φ.bound => a.val G.carrier) i
      simp only [tupleEnv,dite_eq_left (show i < φ.bound by omega)]

theorem uniform_checked_definition_name (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r t : Conditions c, ZFSet.pair (label c r) (label c t) ∈ o ↔ r ≤ t)
    (A : Name (Conditions c)) (hA : A.encode (label c) ∈ M)
    (X : ZFSet.{u}) (hX : X ∈ M) (φ : SentenceForm) :
    ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        f.val G.carrier = definedSubset (A.val G.carrier) φ
          (fun _ : Fin φ.bound => X) := by
  have hcX := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hX
  obtain ⟨f,hf,hval⟩ := uniform_definedSubset_name M hM hT hc hoM ho
    A (Name.check X) hA hcX φ
  refine ⟨f,hf,?_⟩
  intro G hG ht
  simpa only [Name.val_check G.carrier ht X] using hval G hG

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformNameValueCover
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}}

theorem uniform_name_value_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {W : ZFSet.{u}} (hW : W ∈ M) [Top (Conditions c)] :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ g : Set (Conditions c), ⊤ ∈ g → ∀ b : Name (Conditions c),
        b.encode (label c) ∈ W → b.val g ∈ N.val g := by
  let V := ZFSet.sep (fun x => (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c))) W
  have hV : V ∈ M := sigma_sep_mem M hM hS (NameValidity.Code.valid 1 0) (fun _ => c) (fun _ => hc) hW
  have valid (x : ZFSet.{u}) (hx : x ∈ M) :
      (NameValidity.Code.valid 1 0).Realize M (cons x (fun _ => c)) ↔
        ∃ a : Name (Conditions c), a.encode (label c) = x :=
    NameValidity.realize_valid M hM hP hU hPow hS.bounded hR hI _
      (by intro i; cases i <;> assumption) 1 0
  have hvalid (x : ZFSet.{u}) (hx : x ∈ V) : ∃ a : Name (Conditions c), a.encode (label c) = x :=
    (valid x (hM V hV x hx)).mp (ZFSet.mem_sep.mp hx).2
  let p : Conditions c := ⊤
  have hN : (coverName V hvalid p).encode (label c) ∈ M := by
    rw [encode_coverName]
    exact product_mem M hM hP hU hPow hS.bounded hV
      (singleton_mem M hM hP (hM c hc _ (label_mem c p)))
  refine ⟨coverName V hvalid p,hN,?_⟩
  intro g ht b hb
  apply val_mem_coverName V hvalid g p ht b
  exact ZFSet.mem_sep.mpr ⟨hb,(valid _ (hM W hW _ hb)).mpr ⟨b,rfl⟩⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformExtensionWitnessCover
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem uniform_extension_witness_cover (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) [Top (Conditions c)] :
    ∃ N : Name (Conditions c), N.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
      ∀ x ∈ a.val G.carrier,
        (∃ y ∈ genericExtensionSet M c G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val G.carrier)))) →
        ∃ y ∈ N.val G.carrier,
          φ.Realize (genericExtensionSet M c G.carrier) (cons y (cons x (fun i => (e i).val G.carrier))) := by
  obtain ⟨d,hd,hdt,had⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI ha
  obtain ⟨W,hW,hbound⟩ := forcing_witness_bound M hM hP hU hPow hS hR hI hAC hc hoM ho φ e he hd
  obtain ⟨N,hN,hcover⟩ := uniform_name_value_cover M hM hP hU hPow hS hR hI hc hW
  refine ⟨N,hN,?_⟩
  intro G hG ht x hx hw
  obtain ⟨b,hbd,rfl⟩ := name_of_value_member d hdt a had G.carrier x hx
  have hb := hM d hd _ hbd
  obtain ⟨y,hy,hφ⟩ := hw
  obtain ⟨v,hv,rfl⟩ := (mem_extensionSet M c G.carrier y).mp hy
  have env (v : Name (Conditions c)) (hv : v.encode (label c) ∈ M) :
      ∀ i, (push v (push b e) i).encode (label c) ∈ M := by
    intro i; rcases i with _|i; exact hv
    rcases i with _|i; exact hb
    exact he i
  have values (v : Name (Conditions c)) : (fun i => (push v (push b e) i).val G.carrier) =
      cons (v.val G.carrier) (cons (b.val G.carrier) (fun i => (e i).val G.carrier)) := by
    funext i; rcases i with _|i; rfl
    rcases i with _|i <;> rfl
  rw [← values v] at hφ
  obtain ⟨p,hp,hforce⟩ := (internal_sigma_truth M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG
    φ (push v (push b e)) (env v hv)).mp hφ
  obtain ⟨w,hw,hforcew⟩ := hbound b hbd p ⟨v,hv,hforce⟩
  have hwM := hM W hW _ hw
  have hφw := (internal_sigma_truth M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG
    φ (push w (push b e)) (env w hwM)).mpr ⟨p,hp,hforcew⟩
  rw [values w] at hφw
  exact ⟨w.val G.carrier,hcover G.carrier ht w hw,hφw⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformHierarchyStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem HierarchyGraph.stageStep_iff {M R d r f : ZFSet.{u}}
    (h : HierarchyGraph M (seed R) d r f) (x : ZFSet.{u}) (hx : x ∈ d) (A : ZFSet.{u}) :
    StageStep (seed R) f r x A ↔ A = stage R x := by
  constructor
  · intro hs
    apply ZFSet.ext; intro z
    rw [mem_stage]
    constructor
    · intro hz
      rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
      · exact Or.inl hz
      · rw [h.correct y (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,hz⟩
    · rintro (hz|⟨y,hy,hz⟩)
      · exact hs.1 hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← h.correct y (h.1 x hx y hy) w hw hfw] at hz
        exact hs.2.2 y hy w hw hfw hz
  · rintro rfl
    refine ⟨seed_subset_stage R x,?_,?_⟩
    · intro z hz
      rcases (mem_stage R x z).mp hz with hz|⟨y,hy,hz⟩
      · exact Or.inl hz
      · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1 x hx y hy)
        rw [← h.correct y (h.1 x hx y hy) w hw hfw] at hz
        exact Or.inr ⟨y,hy,w,hw,hfw,hz⟩
    · intro y hy w hw hfw
      rw [h.correct y (h.1 x hx y hy) w hw hfw]
      exact definablePower_subset_stage R hy

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformPowerName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.AtomicForcing
open Set RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
universe u

theorem uniform_power_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
    ∃ b : Name (Conditions c), b.encode (label c) ∈ M ∧
      ∀ (G : GenericFilter (Conditions c)), GroundGeneric M G → ⊤ ∈ G.carrier →
        ∀ x, x ∈ b.val G.carrier ↔
          x ∈ genericExtensionSet M c G.carrier ∧ x ⊆ a.val G.carrier := by
  have hS := hT.separation.finitePrefix.bounded
  have hsupport := support_mem M hM hT.pairing hT.union hT.powerSet hS hc hoM ho a ha
  obtain ⟨W,hW,hWdef⟩ := internal_power M hM hT.powerSet hsupport
  have hWsub : ∀ B ∈ W, B ⊆ a.support (label c) := fun B hB => ((hWdef B).mp hB).2
  have hpower : (powerName a W).encode (label c) ∈ M := by
    rw [encode_powerName a W hWsub]
    exact product_mem M hM hT.pairing hT.union hT.powerSet hS hW
      (singleton_mem M hM hT.pairing (hM c hc _ (label_mem c ⊤)))
  refine ⟨powerName a W,hpower,?_⟩
  intro G hG ht x
  constructor
  · intro hx
    obtain ⟨B,hB,hBx⟩ := (mem_val_powerName a W G.carrier ht x).mp hx
    have hcode : (a.restrict (label c) B).encode (label c) ∈ M := by
      rw [Name.encode_restrict _ _ _ (hWsub B hB)]
      exact ((hWdef B).mp hB).1
    exact ⟨(mem_extensionSet M c G.carrier x).mpr ⟨_,hcode,hBx⟩,
      hBx ▸ a.val_restrict_subset (label c) B G⟩
  · rintro ⟨hx,hsub⟩
    obtain ⟨b,hb,rfl⟩ := (mem_extensionSet M c G.carrier x).mp hx
    obtain ⟨B,hBM,hBS,hBval⟩ := internal_intersection_name M hM hT.pairing hT.union
      hT.powerSet hS hT.replacement.finitePrefix hT.infinity hc hoM ho G hG a b ha hb
    apply (mem_val_powerName a W G.carrier ht _).mpr
    refine ⟨B,(hWdef B).mpr ⟨hBM,hBS⟩,hBval.trans ?_⟩
    apply ZFSet.ext; intro y
    rw [ZFSet.mem_inter]
    exact ⟨And.right,fun hy => ⟨hsub hy,hy⟩⟩

end TuringRigidity.AtomicForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformOwnRealsName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u

theorem uniform_ownReals_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) :
    ∃ R : Name (Conditions c), R.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        R.val G.carrier = groundReals (genericExtensionSet M c G.carrier) := by
  have hω := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
      (sourceT_omega_mem M hM hT)
  obtain ⟨R,hR,hval⟩ := uniform_power_name M hM hT hc hoM ho (Name.check ZFSet.omega) hω
  refine ⟨R,hR,?_⟩
  intro G hG ht
  apply ZFSet.ext; intro x
  rw [hval G hG ht x,mem_groundReals,Name.val_check G.carrier ht]

theorem uniform_zero_stage_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) :
    ∃ A : Name (Conditions c), A.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        A.val G.carrier = stage (groundReals (genericExtensionSet M c G.carrier)) ∅ := by
  obtain ⟨R,hR,hval⟩ := uniform_ownReals_name M hM hT hc hoM ho
  let P := Name.pair (Name.pair R R) R
  have hRR := names_pair_closed M c hM hT.pairing hc hR hR
  have hP : P.encode (label c) ∈ M := names_pair_closed M c hM hT.pairing hc hRR hR
  have hA : (Name.union P).encode (label c) ∈ M := by
    rw [encode_union c o ho]
    exact unionCode_mem M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hP hc hoM
  refine ⟨Name.union P,hA,?_⟩
  intro G hG ht
  rw [Name.val_union,stage_zero,ground_seed_shape _ (genericExtensionSet_transitive M c hM G.carrier)]
  dsimp only [P]
  rw [Name.val_pair G.carrier ht,Name.val_pair G.carrier ht,hval G hG ht]
  apply ZFSet.ext; intro x
  simp only [ZFSet.mem_sUnion,ZFSet.mem_insert_iff,ZFSet.mem_singleton]
  constructor
  · rintro ⟨y,hy,hx⟩
    rcases hy with rfl|rfl
    · exact Or.inl (by simpa only [ZFSet.mem_insert_iff,ZFSet.mem_singleton,or_self] using hx)
    · exact Or.inr hx
  · rintro (rfl|hx)
    · exact ⟨_,Or.inl rfl,ZFSet.mem_insert _ _⟩
    · exact ⟨_,Or.inr rfl,hx⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformSigmaHierarchy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem stageCertificate_iff (E R x A : ZFSet.{u}) (hE : Transitive E) (hTE : SourceT E)
    (hR : R ∈ E) (hx : x ∈ E) :
    (∃ d ∈ E, ∃ f ∈ E, ∃ r ∈ E, x ∈ d ∧
      HierarchyGraph E (seed R) d r f ∧ StageStep (seed R) f r x A) ↔ A = stage R x := by
  constructor
  · rintro ⟨d,_,f,_,r,_,hxd,hg,hs⟩
    exact (hg.stageStep_iff x hxd A).mp hs
  · intro h
    obtain ⟨d,hd,f,hf,hxd,hg⟩ := internal_hierarchy_cover E R x hE hTE hR hx
    exact ⟨d,hd,f,hf,_,iterUnion_mem E hE hTE.union hf 2,hxd,hg,
      (hg.stageStep_iff x hxd A).mpr h⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformSigmaSeparationName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u
variable {c : ZFSet.{u}} [Preorder (Conditions c)]

theorem uniform_sigma_separation_name (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M) (hS : SigmaSeparation M)
    (hR : SigmaReplacement M) (hI : Infinity M) (hc : c ∈ M)
    {o : ZFSet.{u}} (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M) :
    ∃ B ∈ M, B ⊆ a.support (label c) ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ∀ x,
      x ∈ (a.restrict (label c) B).val G.carrier ↔ x ∈ a.val G.carrier ∧
        φ.Realize (genericExtensionSet M c G.carrier)
          (cons x (fun i => (e i).val G.carrier)) := by
  let env := cons c (cons o (fun i => (e i).encode (label c)))
  have henv : ∀ i, env i ∈ M := by
    intro i; rcases i with _|i; exact hc
    rcases i with _|i; exact hoM
    exact he i
  let ψ := SigmaFormula.existsSet (.existsSet
    (SigmaFormula.andBounded (.orderedPair 2 1 0)
      (SigmaCode.forcing φ 3 4 0 (push 1 (fun i => i+5)))))
  let B := ZFSet.sep (fun z => ψ.Realize M (cons z env)) (a.support (label c))
  have hBM : B ∈ M := sigma_sep_mem M hM hS ψ env henv
    (support_mem M hM hP hU hPow hS.bounded hc hoM ho a ha)
  have hBsub : B ⊆ a.support (label c) := fun z hz => (ZFSet.mem_sep.mp hz).1
  have hai (i) : (a.child i).encode (label c) ∈ M :=
    names_childClosed M c hM a ha _ (child_relation a i)
  have hpush (i) (n) : (push (a.child i) e n).encode (label c) ∈ M := by
    cases n with
    | zero => exact hai i
    | succ n => exact he n
  have hpair (z x q : ZFSet.{u}) (hz : z ∈ M) (hx : x ∈ M) (hq : q ∈ M) :
      (Formula.orderedPair 2 1 0).Realize M (cons q (cons x (cons z env))) ↔ z = ZFSet.pair x q := by
    rw [Formula.absolute _ M hM _ (by
      intro n; rcases n with _|n; exact hq
      rcases n with _|n; exact hx
      rcases n with _|n; exact hz
      exact henv n)]
    exact Formula.eval_orderedPair 2 1 0 _
  have hB (i : a.arity) (q : Conditions c) (hq : q ≤ a.tag i) :
      ZFSet.pair ((a.child i).encode (label c)) (label c q) ∈ B ↔
        SigmaForces M (push (a.child i) e) φ q := by
    let z := ZFSet.pair ((a.child i).encode (label c)) (label c q)
    have hqM := hM c hc _ (label_mem c q)
    have hz : z ∈ M := orderedPair_mem M hM hP (hai i) hqM
    have query := realize_sigmaForcing M hM hP hU hPow hS.bounded hR hI ho φ
      (push (a.child i) e) q
      (cons (label c q) (cons ((a.child i).encode (label c)) (cons z env)))
      (by
        intro n; rcases n with _|n; exact hqM
        rcases n with _|n; exact hai i
        rcases n with _|n; exact hz
        exact henv n)
      3 4 0 (push 1 (fun n => n+5)) rfl rfl rfl
      (by intro n; cases n <;> rfl)
    have hs : z ∈ a.support (label c) := ZFSet.mem_range.mpr ⟨⟨i,⟨q,hq⟩⟩,rfl⟩
    change z ∈ ZFSet.sep _ _ ↔ _
    rw [ZFSet.mem_sep,and_iff_right hs]
    simp only [ψ,SigmaFormula.Realize,SigmaFormula.realize_andBounded]
    constructor
    · rintro ⟨x,hx,r,hr,hxr,hφ⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp ((hpair z x r hz hx hr).mp hxr)
      exact query.mp hφ
    · intro hφ
      exact ⟨_,hai i,_,hqM,(hpair z _ _ hz (hai i) hqM).mpr rfl,query.mpr hφ⟩
  refine ⟨B,hBM,hBsub,?_⟩
  intro G hG
  have ht (i : a.arity) :
      φ.Realize (genericExtensionSet M c G.carrier)
        (cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier)) ↔
        ∃ p ∈ G.carrier, SigmaForces M (push (a.child i) e) φ p := by
    have hev : (fun n => (push (a.child i) e n).val G.carrier) =
        cons ((a.child i).val G.carrier) (fun n => (e n).val G.carrier) := by
      funext n; cases n <;> rfl
    rw [←hev]
    exact internal_sigma_truth M hM hP hU hPow hS.bounded hR hI hc hoM ho G hG φ _ (hpush i)
  intro x
  constructor
  · intro hx
    have hxa := a.val_restrict_subset (label c) B G hx
    obtain ⟨i,q,hqi,hqb,hqG,hix⟩ := (a.mem_val_restrict (label c) B G.carrier x).mp hx
    have hφ := (ht i).mpr ⟨q,hqG,(hB i q hqi).mp hqb⟩
    exact ⟨hxa,hix ▸ hφ⟩
  · rintro ⟨hxa,hφ⟩
    obtain ⟨i,hi,hix⟩ := (a.mem_val_children G.carrier x).mp hxa
    obtain ⟨p,hp,hf⟩ := (ht i).mp (hix ▸ hφ)
    obtain ⟨q,hq,hqp,hqi⟩ := G.directed hp hi
    exact (a.mem_val_restrict (label c) B G.carrier x).mpr
      ⟨i,q,hqi,(hB i q hqi).mpr (sigma_mono M φ _ hqp hf),hq,hix⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformSigmaUniqueName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u

theorem uniform_sigma_unique_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (φ : SigmaFormula) (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M)
    (e : ℕ → Name (Conditions c)) (he : ∀ i, (e i).encode (label c) ∈ M)
    (F : Set (Conditions c) → ZFSet.{u})
    (hF : ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
      F G.carrier ∈ genericExtensionSet M c G.carrier ∧
      ∀ y ∈ genericExtensionSet M c G.carrier,
        φ.Realize (genericExtensionSet M c G.carrier)
          (cons y (cons (a.val G.carrier) (fun i => (e i).val G.carrier))) ↔ y = F G.carrier) :
    ∃ A : Name (Conditions c), A.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        A.val G.carrier = F G.carrier := by
  have hp := names_pair_closed M c hM hT.pairing hc ha ha
  obtain ⟨N,hN,hNv⟩ := uniform_extension_witness_cover M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
    hc hoM ho φ e he (Name.pair a a) hp
  have hep (i : ℕ) : (push a e i).encode (label c) ∈ M := by
    cases i; exact ha; exact he _
  obtain ⟨B,hB,hBS,hBv⟩ := uniform_sigma_separation_name M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hc hoM ho φ N hN (push a e) hep
  let S := N.restrict (label c) B
  have hS : S.encode (label c) ∈ M := by
    dsimp only [S]; rw [Name.encode_restrict _ _ _ hBS]; exact hB
  refine ⟨Name.union S,names_union_closed M c o hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hc hoM ho hS,?_⟩
  intro G hG ht
  obtain ⟨hFm,hFv⟩ := hF G hG ht
  have hE := genericExtensionSet_transitive M c hM G.carrier
  have hNE := (mem_extensionSet M c G.carrier _).mpr ⟨N,hN,rfl⟩
  have haV : a.val G.carrier ∈ (Name.pair a a).val G.carrier := by
    rw [Name.val_pair G.carrier ht]
    exact ZFSet.mem_pair.mpr (Or.inl rfl)
  obtain ⟨y,hy,hφ⟩ := hNv G hG ht _ haV ⟨_,hFm,(hFv _ hFm).mpr rfl⟩
  have hyF : y = F G.carrier := (hFv y (hE _ hNE y hy)).mp hφ
  have hsval : S.val G.carrier = ({F G.carrier} : ZFSet.{u}) := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_singleton]
    have hv := hBv G hG z
    have heval : (fun i => (push a e i).val G.carrier) =
        cons (a.val G.carrier) (fun i => (e i).val G.carrier) := by
      funext i; cases i <;> rfl
    rw [heval] at hv
    rw [hv]
    constructor
    · rintro ⟨hz,hφz⟩; exact (hFv z (hE _ hNE z hz)).mp hφz
    · rintro rfl; exact ⟨hyF ▸ hy,(hFv _ hFm).mpr rfl⟩
  rw [Name.val_union,hsval,ZFSet.sUnion_singleton]

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformOrdinalStageName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
open AtomicForcing BoundedForcing BoundedDefinability SetModelFunctions
universe u

theorem uniform_named_stage (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (a : Name (Conditions c)) (ha : a.encode (label c) ∈ M) :
    ∃ A : Name (Conditions c), A.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        A.val G.carrier = stage (groundReals (genericExtensionSet M c G.carrier))
          (a.val G.carrier) := by
  obtain ⟨p,d,hd,hp⟩ := stageCertificate_uniformSigma M hM hT
  obtain ⟨S,hS,hSv⟩ := uniform_zero_stage_name M hM hT hc hoM ho
  let e : ℕ → Name (Conditions c) := push S (fun n => Name.check (d n))
  have he (i : ℕ) : (e i).encode (label c) ∈ M := by
    cases i with
    | zero => exact hS
    | succ i =>
      exact encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
        hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc (hd i)
  let r : ℕ → ℕ := fun i => if i % 2 = 0 then
    (if i / 2 = 0 then 0 else if i / 2 = 1 then 1 else 2) else i/2+3
  apply uniform_sigma_unique_name M hM hT hc hoM ho (p.rename r) a ha e he
    (fun g => stage (groundReals (genericExtensionSet M c g)) (a.val g))
  intro G hG ht
  let E := genericExtensionSet M c G.carrier
  have hE := genericExtensionSet_transitive M c hM G.carrier
  have hTE := extension_sourceT M hM hT hc hoM ho G hG ht
  have hME := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  have hR := groundReals_mem E hE hTE
  have haE : a.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨a,ha,rfl⟩
  have hSE : S.val G.carrier ∈ E := (mem_extensionSet M c G.carrier _).mpr ⟨S,hS,rfl⟩
  refine ⟨stage_mem E _ _ hE hTE hR haE,?_⟩
  intro y hy
  have heval : (fun i => (e i).val G.carrier) = cons (S.val G.carrier) d := by
    funext i; cases i with
    | zero => rfl
    | succ i => exact Name.val_check G.carrier ht (d i)
  rw [heval,SigmaFormula.realize_rename]
  let v := cons y (cons (a.val G.carrier) (fun _ => S.val G.carrier))
  have hv : ∀ i, v i ∈ E := by
    intro i; rcases i with _|_|i; exact hy; exact haE; exact hSE
  have hr : cons y (cons (a.val G.carrier) (cons (S.val G.carrier) d)) ∘ r = mix v d := by
    apply parity_ext
    · intro n
      rcases n with _|_|n
      · rfl
      · rfl
      · simp [r,v,Function.comp_apply,mix,cons,show ¬ 2 * (n+1+1) ≤ 1 by omega]
    · intro n; simp [r,Function.comp_apply,mix,Nat.add_div]
  change p.Realize E (cons y (cons (a.val G.carrier) (cons (S.val G.carrier) d)) ∘ r) ↔ _
  rw [hr,hp E hE hTE hME v hv]
  change (∃ d' ∈ E, ∃ f ∈ E, ∃ t ∈ E, a.val G.carrier ∈ d' ∧
    HierarchyGraph E (S.val G.carrier) d' t f ∧
      StageStep (S.val G.carrier) f t (a.val G.carrier) y) ↔ _
  rw [hSv G hG ht,stage_zero]
  exact stageCertificate_iff E _ _ y hE hTE hR haE

theorem uniform_ordinal_level_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (δ : Ordinal.{u}) (hδ : δ.toZFSet ∈ M) :
    ∃ A : Name (Conditions c), A.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        A.val G.carrier = level (groundReals (genericExtensionSet M c G.carrier)) δ := by
  have ha := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc hδ
  obtain ⟨A,hA,hAv⟩ := uniform_named_stage M hM hT hc hoM ho (Name.check δ.toZFSet) ha
  refine ⟨A,hA,?_⟩
  intro G hG ht
  simpa only [Name.val_check G.carrier ht,level] using hAv G hG ht

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformOrdinalDefinitionName
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing
open AtomicForcing BoundedForcing
universe u

theorem uniform_ordinal_definition_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (δ : Ordinal.{u}) (hδ : δ.toZFSet ∈ M) (X : ZFSet.{u}) (hX : X ∈ M) (φ : SentenceForm) :
    ∃ f : Name (Conditions c), f.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        f.val G.carrier = definedSubset
          (level (groundReals (genericExtensionSet M c G.carrier)) δ)
            φ (fun _ : Fin φ.bound => X) := by
  obtain ⟨A,hA,hAv⟩ := uniform_ordinal_level_name M hM hT hc hoM ho δ hδ
  obtain ⟨f,hf,hfv⟩ := uniform_checked_definition_name M hM hT hc hoM ho A hA X hX φ
  exact ⟨f,hf,fun G hG ht => by rw [hfv G hG ht,hAv G hG ht]⟩

end TuringRigidity.RelativeConstructible

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

theorem mem_degreeSet (a : Degree) (x : ZFSet.{u}) :
    x ∈ degreeSet a ↔ ∃ A, x = realSet A ∧ degree A = a := by
  constructor
  · intro hx
    obtain ⟨hs,he⟩ := ZFSet.mem_sep.mp hx
    exact ⟨oracleOf x,(realSet_oracleOf (ZFSet.mem_powerset.mp hs)).symm,he⟩
  · rintro ⟨A,rfl,he⟩
    exact (real_mem_degreeSet A a).mpr he

theorem degreeSet_injective : Function.Injective degreeSet.{u} := by
  intro a b he
  obtain ⟨A,rfl⟩ := degree_surjective a
  exact (real_mem_degreeSet A b).mp (he ▸ (real_mem_degreeSet A (degree A)).mpr rfl)

end
end TuringRigidity.SetDegreeDecoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelCountability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open BoundedDefinability SetModelSyntax SetDegreeDecoding SetModelSequences
open PersistentRestrictions PersistentPresentation EncodedForcing
universe u
noncomputable section

variable {M : ZFSet.{u}}

theorem FunctionGraph.unique {f a b x y z : ZFSet.{u}} (h : FunctionGraph f a b)
    (hx : x ∈ a) (hy : y ∈ b) (hz : z ∈ b)
    (hxy : ZFSet.pair x y ∈ f) (hxz : ZFSet.pair x z ∈ f) : y = z := by
  obtain ⟨v,hv,hxv,hu⟩ := h.2 x hx
  exact (hu y hy hxy).trans (hu z hz hxz).symm

end
end TuringRigidity.SetModelCountability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelDegreeUniverse
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetPresentationDecoding SetDegreeDecoding UniformArithmetic
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem represented_of_degreeSet_mem (C : Context M) {a : Degree}
    (ha : degreeSet.{u} a ∈ M) : ∃ A ∈ reals M, degree A = a := by
  obtain ⟨A,rfl⟩ := degree_surjective a
  exact ⟨A,C.transitive _ ha _ ((real_mem_degreeSet A _).mpr rfl),rfl⟩

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelIdealSatisfaction
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem order_code (C : Context M) {L : ZFSet.{u}}
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    {a b : Degree} (ha : degreeSet.{u} a ∈ M) (hb : degreeSet.{u} b ∈ M) :
    ZFSet.pair (degreeSet a) (degreeSet b) ∈ L ↔ a ≤ b := by
  obtain ⟨A,hA,rfl⟩ := represented_of_degreeSet_mem C ha
  obtain ⟨B,hB,rfl⟩ := represented_of_degreeSet_mem C hb
  exact hL A hA B hB

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelActionSatisfaction
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem action_code {I : CountableIdeal} (ρ : I ≃o I) (a b : I) :
    ZFSet.pair (degreeSet.{u} a.val) (degreeSet b.val) ∈ automorphismSet ρ ↔ ρ a = b := by
  rw [mem_automorphismSet]
  constructor
  · rintro ⟨c,he⟩
    obtain ⟨ha,hb⟩ := ZFSet.pair_inj.mp he
    have ha' : a=c := Subtype.ext (degreeSet_injective ha)
    have hb' : b=ρ c := Subtype.ext (degreeSet_injective hb)
    rw [ha',hb']
  · intro h
    exact ⟨a,by rw [h]⟩

theorem action_satisfaction (C : Context M) {L : ZFSet.{u}}
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    {I : CountableIdeal} (hI : idealSet I ∈ M) (ρ : I ≃o I) :
    IsAction (automorphismSet ρ) (idealSet I) L := by
  have hm (a : I) : degreeSet.{u} a.val ∈ M :=
    C.transitive _ hI _ ((mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩)
  have hi (a : I) : degreeSet.{u} a.val ∈ idealSet I :=
    (mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro z hz
    obtain ⟨a,rfl⟩ := (mem_automorphismSet ρ z).mp hz
    exact ⟨degreeSet a.val,hi a,degreeSet (ρ a).val,hi (ρ a),rfl⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
    let a' : I := ⟨a,ha⟩
    refine ⟨degreeSet (ρ a').val,hi (ρ a'),(action_code ρ a' (ρ a')).mpr rfl,?_⟩
    intro z hz hxz
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I z).mp hz
    have hh := (action_code ρ a' ⟨b,hb⟩).mp hxz
    exact congrArg (fun c : I => degreeSet c.val) hh.symm
  · intro y hy
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I y).mp hy
    let b' : I := ⟨b,hb⟩
    exact ⟨degreeSet (ρ.symm b').val,hi (ρ.symm b'),
      (action_code ρ (ρ.symm b') b').mpr (ρ.apply_symm_apply b')⟩
  · intro x hx y hy a ha b hb hab
    obtain ⟨x,hxc,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨y,hyc,rfl⟩ := (mem_idealSet I y).mp hy
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I a).mp ha
    obtain ⟨b,hbc,rfl⟩ := (mem_idealSet I b).mp hb
    have hxa := (action_code ρ ⟨x,hxc⟩ ⟨a,hac⟩).mp hab.1
    have hyb := (action_code ρ ⟨y,hyc⟩ ⟨b,hbc⟩).mp hab.2
    rw [order_code C hL (hm ⟨x,hxc⟩) (hm ⟨y,hyc⟩),
      order_code C hL (hm ⟨a,hac⟩) (hm ⟨b,hbc⟩)]
    change (⟨x,hxc⟩ : I) ≤ ⟨y,hyc⟩ ↔ (⟨a,hac⟩ : I) ≤ ⟨b,hbc⟩
    rw [←hxa,←hyb]
    exact ρ.le_iff_le.symm

theorem extends_sets {I J : CountableIdeal} {ρ : I ≃o I} {σ : J ≃o J}
    {hIJ : I.carrier ⊆ J.carrier} (he : Extends hIJ ρ σ) :
    automorphismSet.{u} ρ ⊆ automorphismSet σ := by
  intro z hz
  obtain ⟨a,rfl⟩ := (mem_automorphismSet ρ z).mp hz
  exact (mem_automorphismSet σ _).mpr ⟨⟨a.val,hIJ a.property⟩,by rw [he a]⟩

theorem ideal_subset {I J : CountableIdeal} (h : I.carrier ⊆ J.carrier) :
    idealSet.{u} I ⊆ idealSet J := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
  exact (mem_idealSet J _).mpr ⟨a,h ha,rfl⟩

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_SetModelActionDecoding
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section

theorem decode_action {M : ZFSet.{u}} (C : Context M) {L f : ZFSet.{u}}
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hIM : idealSet I ∈ M) (ha : IsAction f (idealSet I) L) :
    ∃ ρ : I ≃o I, automorphismSet ρ = f := by
  have hi (a : I) : degreeSet.{u} a.val ∈ idealSet I :=
    (mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩
  have hm (a : I) : degreeSet.{u} a.val ∈ M := C.transitive _ hIM _ (hi a)
  have hex (a : I) : ∃ b : I, ZFSet.pair (degreeSet.{u} a.val) (degreeSet b.val) ∈ f := by
    obtain ⟨y,hy,hxy,_⟩ := ha.1.1.2 _ (hi a)
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I y).mp hy
    exact ⟨⟨b,hb⟩,hxy⟩
  choose F hF using hex
  have hle (a b : I) : F a ≤ F b ↔ a ≤ b := by
    have hh := ha.2 _ (hi a) _ (hi b) _ (hi (F a)) _ (hi (F b)) ⟨hF a,hF b⟩
    rw [order_code C hL (hm a) (hm b),order_code C hL (hm (F a)) (hm (F b))] at hh
    exact hh.symm
  have hinj : Function.Injective F := by
    intro a b he
    exact le_antisymm ((hle a b).mp (le_of_eq he)) ((hle b a).mp (le_of_eq he.symm))
  have hsurj : Function.Surjective F := by
    intro b
    obtain ⟨x,hx,hxb⟩ := ha.1.2 _ (hi b)
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I x).mp hx
    refine ⟨⟨a,hac⟩,Subtype.ext (degreeSet_injective ?_)⟩
    exact ha.1.1.unique (hi ⟨a,hac⟩) (hi (F ⟨a,hac⟩)) (hi b) (hF ⟨a,hac⟩) hxb
  let ρ : I ≃o I := { toEquiv := Equiv.ofBijective F ⟨hinj,hsurj⟩, map_rel_iff' := by intro a b; exact hle a b }
  have hpair (a b : I) : ZFSet.pair (degreeSet.{u} a.val) (degreeSet b.val) ∈ f ↔ ρ a = b := by
    constructor
    · intro hab
      apply Subtype.ext
      apply degreeSet_injective
      exact ha.1.1.unique (hi a) (hi (F a)) (hi b) (hF a) hab
    · intro he
      have he' : F a = b := he
      simpa only [he'] using hF a
  refine ⟨ρ,ZFSet.ext (fun z => ?_)⟩
  constructor
  · intro hz
    obtain ⟨a,rfl⟩ := (mem_automorphismSet ρ z).mp hz
    exact (hpair a (ρ a)).mpr rfl
  · intro hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ha.1.1.1 z hz
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨b,hbc,rfl⟩ := (mem_idealSet I y).mp hy
    exact (action_code ρ ⟨a,hac⟩ ⟨b,hbc⟩).mpr ((hpair ⟨a,hac⟩ ⟨b,hbc⟩).mp hz)

theorem ideal_subset_iff {I J : CountableIdeal} :
    idealSet.{u} I ⊆ idealSet J ↔ I.carrier ⊆ J.carrier := by
  constructor
  · intro h a ha
    obtain ⟨b,hb,he⟩ := (mem_idealSet J _).mp (h ((mem_idealSet I _).mpr ⟨a,ha,rfl⟩))
    exact (degreeSet_injective he).symm ▸ hb
  · exact ideal_subset

theorem extends_sets_iff {I J : CountableIdeal} (hIJ : I.carrier ⊆ J.carrier)
    (ρ : I ≃o I) (σ : J ≃o J) :
    automorphismSet.{u} ρ ⊆ automorphismSet σ ↔ Extends hIJ ρ σ := by
  constructor
  · intro h a
    have hh := h ((mem_automorphismSet ρ _).mpr ⟨a,rfl⟩)
    have he := (action_code σ ⟨a.val,hIJ a.property⟩ ⟨(ρ a).val,hIJ (ρ a).property⟩).mp hh
    exact congrArg Subtype.val he
  · exact extends_sets

end
end TuringRigidity.SetModelSatisfaction

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_NativeModelCompatibility
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel SetModelReals SetDegreeDecoding PersistentRestrictions PersistentPresentation
universe u

theorem degreeCode_eq_degreeSet (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u}) (hS : ∀ A : Oracle, realCode A ∈ S ↔ A ∈ modelReals M)
    {A : Oracle} (hA : A ∈ modelReals M) : degreeCode S A = degreeSet (degree A) := by
  apply ZFSet.ext; intro x
  rw [degreeCode,ZFSet.mem_sep,mem_degreeSet]
  constructor
  · rintro ⟨_,B,hB,hBA⟩
    exact ⟨B,hB,hBA⟩
  · rintro ⟨B,rfl,hBA⟩
    have hB := sourceT_real_lower M hM hT hA ((degree_eq_iff B A).mp hBA).1
    exact ⟨(hS B).mpr hB,B,rfl,hBA⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_AmbientDegreeActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel SetDegreeDecoding
universe u

theorem ownRealPower_codes (M R : ZFSet.{u})
    (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    ∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M := by
  intro A
  exact (hR _).trans (and_iff_left (realCode_subset A))

theorem ownDegreeUniverse_actual (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    ∀ x, x ∈ degreeUniverse R ↔
      ∃ A ∈ SetModelReals.reals M, x = degreeSet (degree A) := by
  intro x
  rw [mem_degreeUniverse]
  have hr := ownRealPower_codes M R hR
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact ⟨A,(hr A).mp hA,degreeCode_eq_degreeSet M hM hT R hr ((hr A).mp hA)⟩
  · rintro ⟨A,hA,rfl⟩
    exact ⟨A,(hr A).mpr hA,(degreeCode_eq_degreeSet M hM hT R hr hA).symm⟩

theorem ownDegreeOrder_actual (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (R : ZFSet.{u}) (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    ∀ A ∈ SetModelReals.reals M, ∀ B ∈ SetModelReals.reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ degreeOrder R ↔
        Reduces A B := by
  intro A hA B hB
  have hr := ownRealPower_codes M R hR
  rw [←degreeCode_eq_degreeSet M hM hT R hr hA,
    ←degreeCode_eq_degreeSet M hM hT R hr hB]
  exact degreeOrder_actual R ((hr A).mpr hA) ((hr B).mpr hB)

end TuringRigidity.FullSetForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_AmbientExtensionBody
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
open SetDegreeDecoding PersistentRestrictions SetModelSatisfaction ArithmeticTree
universe u

theorem ownDegreeUniverse_eq_idealSet (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (R : ZFSet.{u})
    (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    degreeUniverse R = idealSet (modelIdeal M hM hT) := by
  apply ZFSet.ext
  intro x
  rw [ownDegreeUniverse_actual M hM hT R hR, mem_idealSet]
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact ⟨degree A,⟨A,hA,rfl⟩,rfl⟩
  · rintro ⟨d,⟨A,hA,rfl⟩,rfl⟩
    exact ⟨A,hA,rfl⟩

end TuringRigidity.FullSetForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OriginalRealUniformDefinition
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OriginalRealDefinitionTransport
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames
open CohenGroundPoset InternalCountableOrdinals RelativeConstructible ElementaryModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem original_uniform_definition (M K : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hK : FirstUncountable M K)
    (τ f : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (hf : f.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : AtomicForcing.GroundGeneric M G) (hreal : τ.val G.carrier ⊆ ZFSet.omega)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (φ : SentenceForm)
    (hX : τ.val G.carrier ∈ level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
    (hdef : f.val G.carrier = definedSubset (level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
        φ (fun _ : Fin φ.bound => τ.val G.carrier)) :
    let c := conditions (ZFSet.prod K ZFSet.omega)
    let X := τ.val G.carrier
    let N := RealGeneratedModel.hull M X
    RealGeneratedModel.Contains M X N ∧
      ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
        (∀ H : GenericFilter (Conditions c), AtomicForcing.GroundGeneric N H →
          fX.val H.carrier = definedSubset
            (level (groundReals (genericExtensionSet N c H.carrier)) δ)
              φ (fun _ : Fin φ.bound => X)) ∧
        ∃ GX : GenericFilter (Conditions c), AtomicForcing.GroundGeneric N GX ∧
          genericExtensionSet N c GX.carrier = genericExtensionSet M c G.carrier ∧
          fX.val GX.carrier = f.val G.carrier ∧
          X ∈ level (groundReals (genericExtensionSet N c GX.carrier)) δ := by
  intro c X N
  obtain ⟨hN,GX,hGX,hExt,f₀,_,hf₀,_,_,_,_,hXL,hdef₀⟩ :=
    original_definition_transport M K hM hT hK τ f hτ hf G hG hreal δ hδ φ hX hdef
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK.2.1 (sourceT_omega_mem M hM hT)
  have hc : c ∈ N := hN.2.2.1 (conditions_mem M _ hM hT hA)
  obtain ⟨fX,hfX,hfv⟩ := uniform_ordinal_definition_name N hN.1 hN.2.1 hc
    (InternalCollapse.orderSet_mem N hN.1 hN.2.1 hc) (InternalCollapse.orderSet_pair c)
    δ (hN.2.2.1 hδ) X hN.2.2.2 φ
  have hall (H : GenericFilter (Conditions c)) (hH : AtomicForcing.GroundGeneric N H) :
      fX.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet N c H.carrier)) δ)
          φ (fun _ : Fin φ.bound => X) := by
    obtain ⟨q,hq⟩ := H.nonempty
    exact hfv H hH (H.upper le_top hq)
  exact ⟨hN,fX,hfX,hall,GX,hGX,hExt,(hall GX hGX).trans (hdef₀.symm.trans hf₀),hXL⟩

end TuringRigidity.OriginalRealDefinitionTransport

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OriginalRealUniformExtension
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OriginalRealDefinitionTransport
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing
open CohenGroundPoset InternalCountableOrdinals RelativeConstructible ElementaryModel
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem original_uniform_extension (M K I ρ : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hct : (M : Set ZFSet.{0}).Countable)
    (hK : FirstUncountable M K) (hI : I ∈ M) (hρ : ρ ∈ M)
    (τ f : Name (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hτ : τ.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (hf : f.encode (label (conditions (ZFSet.prod K ZFSet.omega))) ∈ M)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : GroundGeneric M G) (hreal : τ.val G.carrier ⊆ ZFSet.omega)
    (δ : Ordinal.{0}) (hδ : δ.toZFSet ∈ M) (φ : SentenceForm)
    (hX : τ.val G.carrier ∈ level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
    (hdef : f.val G.carrier = definedSubset (level (groundReals
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier)) δ)
        φ (fun _ : Fin φ.bound => τ.val G.carrier))
    (hext : OwnDegreeExtension
      (genericExtensionSet M (conditions (ZFSet.prod K ZFSet.omega)) G.carrier) I ρ (f.val G.carrier)) :
    let c := conditions (ZFSet.prod K ZFSet.omega)
    let X := τ.val G.carrier
    let N := RealGeneratedModel.hull M X
    RealGeneratedModel.Contains M X N ∧ (N : Set ZFSet.{0}).Countable ∧
      ∃ fX : Name (Conditions c), fX.encode (label c) ∈ N ∧
        (∀ H : GenericFilter (Conditions c), GroundGeneric N H →
          fX.val H.carrier = definedSubset
            (level (groundReals (genericExtensionSet N c H.carrier)) δ)
              φ (fun _ : Fin φ.bound => X) ∧
          OwnDegreeExtension (genericExtensionSet N c H.carrier) I ρ (fX.val H.carrier)) ∧
        ∃ GX : GenericFilter (Conditions c), GroundGeneric N GX ∧
          genericExtensionSet N c GX.carrier = genericExtensionSet M c G.carrier ∧
          fX.val GX.carrier = f.val G.carrier := by
  intro c X N
  obtain ⟨hN,f₀,_,hf₀,GX,hGX,hExt,hval₀,_⟩ :=
    original_uniform_definition M K hM hT hK τ f hτ hf G hG hreal δ hδ φ hX hdef
  have hA := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK.2.1 (sourceT_omega_mem M hM hT)
  have hc : c ∈ N := hN.2.2.1 (conditions_mem M _ hM hT hA)
  have hNE : N ⊆ genericExtensionSet M c G.carrier := by
    rw [←hExt]
    obtain ⟨q,hq⟩ := GX.nonempty
    exact ground_inclusion_set N c hN.1 hN.2.1.pairing hN.2.1.union hN.2.1.powerSet
      hN.2.1.separation.finitePrefix.bounded hN.2.1.replacement.finitePrefix hN.2.1.infinity
      hc GX.carrier (GX.upper le_top hq)
  have hNct : (N : Set ZFSet.{0}).Countable := by
    have hEct : (genericExtensionSet M c G.carrier : Set ZFSet.{0}).Countable := by
      rw [genericExtensionSet_coe]
      exact genericExtension_countable M c hct G.carrier
    exact hEct.mono hNE
  have h₀ : OwnDegreeExtension (genericExtensionSet N c GX.carrier) I ρ
      (definedSubset (level (groundReals (genericExtensionSet N c GX.carrier)) δ)
        φ (fun _ : Fin φ.bound => X)) := by
    rw [←hf₀ GX hGX,hval₀,hExt]
    exact hext
  obtain ⟨fX,hfX,hfv⟩ := uniform_cohen_definition_extension N (ZFSet.prod K ZFSet.omega) I ρ
    hN.1 hN.2.1 hNct (hN.2.2.1 hA) (hN.2.2.1 hI) (hN.2.2.1 hρ)
    δ (hN.2.2.1 hδ) X hN.2.2.2 φ GX hGX h₀
  exact ⟨hN,hNct,fX,hfX,hfv,GX,hGX,hExt,
    (hfv GX hGX).1.trans ((hf₀ GX hGX).symm.trans hval₀)⟩

end TuringRigidity.OriginalRealDefinitionTransport

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_OwnDegreeExtensionMeaning
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedForcing
open TransitiveNameModel BoundedSetTheory SetDegreeDecoding PersistentRestrictions SetModelSatisfaction
open RelativeConstructible FullSetForcing ElementaryModel
universe u

theorem own_degree_extension_iff (E : ZFSet.{0}) [Countable (Conditions E)]
    (hE : Transitive E) (hTE : SourceT E) (I : CountableIdeal) (ρ : I ≃o I) (f : ZFSet.{0}) :
    OwnDegreeExtension E (idealSet I) (automorphismSet ρ) f ↔
      ∃ hIJ : I.carrier ⊆ (modelIdeal E hE hTE).carrier,
        ∃ σ : modelIdeal E hE hTE ≃o modelIdeal E hE hTE,
          automorphismSet σ = f ∧ Extends hIJ ρ σ := by
  have hr : ∀ w ∈ groundReals E, ∃ A : Oracle, realCode A = w := by
    intro w hw
    exact ⟨decodeReal w,realCode_decodeReal ((mem_groundReals E w).mp hw).2⟩
  have hD := internal_degreeUniverse E hE hTE _ (groundReals_mem E hE hTE) hr
  have hd := ownDegreeUniverse_eq_idealSet E hE hTE (groundReals E) (mem_groundReals E)
  have hl := ownDegreeOrder_actual E hE hTE (groundReals E) (mem_groundReals E)
  unfold OwnDegreeExtension
  rw [hd]
  constructor
  · rintro ⟨ha,hij,hext⟩
    have hij' := ideal_subset_iff.mp hij
    obtain ⟨σ,hσ⟩ := decode_action (ArithmeticTree.sourceContext E hE hTE) hl
      (modelIdeal E hE hTE) (hd ▸ hD) ha
    refine ⟨hij',σ,hσ,(extends_sets_iff hij' ρ σ).mp ?_⟩
    rwa [hσ]
  · rintro ⟨hij,σ,hσ,hext⟩
    rw [←hσ]
    exact ⟨action_satisfaction (ArithmeticTree.sourceContext E hE hTE) hl (hd ▸ hD) σ,
      ideal_subset hij,extends_sets hext⟩

end TuringRigidity.BoundedForcing

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_PrescribedRealHullExtension
attribute [-instance] _root_.OAI.TuringRigidity.LocalSourceEquation.instSemilatticeSupSubtypeDegreeMemSetCarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing BoundedForcing
open CohenGroundPoset InternalCountableOrdinals ElementaryModel SetDegreeDecoding PersistentRestrictions
open FullSetForcing OriginalRealDefinitionTransport
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem prescribed_real_hull_extension_oai (π : Degree ≃o Degree)
    (M K : ZFSet.{0}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K)
    (himages : π (degree (OracleJump.jump FixedArithmetic.zero)) ⊔
      π.symm (degree (OracleJump.jump FixedArithmetic.zero)) ∈ (modelIdeal M hM hT).carrier)
    (ρ : modelIdeal M hM hT ≃o modelIdeal M hM hT) (hρ : RestrictsTo π _ ρ)
    (G : GenericFilter (Conditions (conditions (ZFSet.prod K ZFSet.omega))))
    (hG : GroundGeneric M G) :
    let c := conditions (ZFSet.prod K ZFSet.omega)
    let E := genericExtensionSet M c G.carrier
    let hE := genericExtensionSet_transitive M c hM G.carrier
    let hTE := extension_sourceT M hM hT (manyColumn_internal M K hM hT hK.2.1).1
      (manyColumn_internal M K hM hT hK.2.1).2 (InternalCollapse.orderSet_pair c)
        G hG (G.upper le_top G.nonempty.choose_spec)
    let I := modelIdeal M hM hT
    let J := modelIdeal E hE hTE
    ∃ (δ : Ordinal.{0}) (P : Oracle) (φ : SentenceForm),
      δ.toZFSet ∈ M ∧ φ.bound ≤ 2 ∧ P ∈ modelReals E ∧
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
            ∃ σ : J ≃o J, RestrictsTo π J σ ∧ fX.val GX.carrier = automorphismSet σ := by
  intro c E hE hTE I J
  have hc := (manyColumn_internal M K hM hT hK.2.1).1
  have ho := (manyColumn_internal M K hM hT hK.2.1).2
  have ht : (⊤ : Conditions c) ∈ G.carrier := G.upper le_top G.nonempty.choose_spec
  have hI : idealSet I ∈ M := relativeModel_subset M _ (ground_idealSet_mem_relativeModel M hM hT)
  have hρM : automorphismSet ρ ∈ M := relativeModel_subset M _
    (persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ
      (persistent_of_global_restriction π I ρ hρ))
  have hct : (M : Set ZFSet.{0}).Countable := by
    apply (Set.countable_range (label M)).mono
    intro x hx; exact label_surjective M hx
  obtain ⟨hIJ,σ,hr,he,_,δ,P,φ,hδ,hP,hφ,hPL,hdef,f,a,hf,ha,hfv,hav⟩ :=
    prescribed_one_real_names π M hM hT himages hc ho (InternalCollapse.orderSet_pair c) G hG ht ρ hρ
  have hreal : a.val G.carrier ⊆ ZFSet.omega := hav.symm ▸ realCode_subset P
  have hX : a.val G.carrier ∈ level (groundReals E) δ := hav.symm ▸ hPL
  have hdef' : f.val G.carrier = definedSubset (level (groundReals E) δ) φ
      (fun _ : Fin φ.bound => a.val G.carrier) := by
    rw [hav,hfv]; exact hdef
  have hext : OwnDegreeExtension E (idealSet I) (automorphismSet ρ) (f.val G.carrier) :=
    (own_degree_extension_iff E hE hTE I ρ _).mpr ⟨hIJ,σ,hfv.symm,he⟩
  obtain ⟨hN,hNct,fX,hfX,hall,GX,hGX,hExt,hval⟩ :=
    original_uniform_extension M K (idealSet I) (automorphismSet ρ) hM hT hct hK hI hρM
      a f ha hf G hG hreal δ hδ φ hX hdef' hext
  rw [hav] at hN hNct hfX hall hGX hExt
  exact ⟨δ,P,φ,hδ,hφ,hP,hN,hNct,fX,hfX,hall,GX,hGX,hExt,σ,hr,hval.trans hfv⟩

end TuringRigidity.RelativeConstructible

end OAI
end

theorem solution : type_of% @OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension_oai := @OAI.TuringRigidity.RelativeConstructible.prescribed_real_hull_extension_oai
