-- Prove2me | solution 1 for OAI.TuringRigidity.OrdinalCoding.cofinal_padded_code_certificates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T01:06:39.323886+00:00
-- url     : https://prove2.me/submissions/779cf8ce-bf34-4bf1-a219-e088315de4f8

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ064A008
import Theorems.Thm_OAI_TuringRigidity_OrdinalArithmetic_internal_explicit_omega_threshold
import Theorems.Thm_OAI_TuringRigidity_OrdinalCoding_padded_certificates_of_lower_closure
import Theorems.Thm_OAI_TuringRigidity_OrdinalCoding_vectorCode_certificates_at_levels

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

theorem subset_of_mem_definablePower {A S : ZFSet.{u}}
    (h : S ∈ definablePower A) : S ⊆ A :=
  definableOver_subset ((mem_definablePower A S).mp h)

theorem subset_definablePower {A : ZFSet.{u}} (hA : Transitive A) : A ⊆ definablePower A := by
  intro S hS
  apply (mem_definablePower A S).mpr
  refine ⟨1,.member 0 1,fun _ => S,by decide,fun _ => hS,?_⟩
  apply ZFSet.ext; intro x
  simp only [mem_definedSubset,SentenceForm.Sat,cons_zero,cons_succ]
  simp only [tupleEnv,show 0 < 1 by decide,dite_eq_left]
  exact ⟨fun hx => ⟨hA S hS x hx,hx⟩,And.right⟩

theorem definablePower_transitive {A : ZFSet.{u}} (hA : Transitive A) :
    Transitive (definablePower A) := by
  intro S hS x hx
  exact subset_definablePower hA (subset_of_mem_definablePower hS hx)

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

theorem stage_transitive (R o : ZFSet.{u}) : Transitive (stage R o) := by
  induction o using ZFSet.inductionOn with
  | h o ih =>
    intro x hx y hy
    rcases (mem_stage R o x).mp hx with hx|⟨i,hi,hx⟩
    · exact seed_subset_stage R o (seed_transitive R x hx y hy)
    · exact (mem_stage R o y).mpr (Or.inr ⟨i,hi,definablePower_transitive (ih i hi) x hx y hy⟩)

theorem stage_mono (R : ZFSet.{u}) {i j : ZFSet.{u}} (hij : i ⊆ j) : stage R i ⊆ stage R j := by
  intro x hx
  rcases (mem_stage R i x).mp hx with hx|⟨k,hk,hx⟩
  · exact seed_subset_stage R j hx
  · exact (mem_stage R j x).mpr (Or.inr ⟨k,hij hk,hx⟩)

theorem definablePower_subset_stage (R : ZFSet.{u}) {i j : ZFSet.{u}} (hi : i ∈ j) :
    definablePower (stage R i) ⊆ stage R j :=
  fun x hx => (mem_stage R j x).mpr (Or.inr ⟨i,hi,hx⟩)

theorem stage_succ (R o : ZFSet.{u}) :
    stage R (insert o o) = definablePower (stage R o) := by
  apply ZFSet.ext; intro x
  constructor
  · intro hx
    rcases (mem_stage R (insert o o) x).mp hx with hseed|⟨i,hi,hdef⟩
    · exact subset_definablePower (stage_transitive R o) (seed_subset_stage R o hseed)
    · rcases ZFSet.mem_insert_iff.mp hi with he|hi
      · simpa only [he] using hdef
      · exact subset_definablePower (stage_transitive R o) (definablePower_subset_stage R hi hdef)
  · intro hx; exact definablePower_subset_stage R (ZFSet.mem_insert o o) hx

theorem level_zero (R : ZFSet.{u}) : level R 0 = seed R := by
  rw [level,Ordinal.toZFSet_zero,stage_zero]

theorem level_succ (R : ZFSet.{u}) (o : Ordinal.{u}) :
    level R (o+1) = definablePower (level R o) := by
  simp only [level,Ordinal.toZFSet_add_one,stage_succ]

theorem level_mono (R : ZFSet.{u}) {i j : Ordinal.{u}} (hij : i ≤ j) : level R i ⊆ level R j :=
  stage_mono R (Ordinal.toZFSet_monotone hij)

theorem level_transitive (R : ZFSet.{u}) (o : Ordinal.{u}) : Transitive (level R o) :=
  stage_transitive R o.toZFSet

theorem mem_level_limit (R x : ZFSet.{u}) (o : Ordinal.{u}) (ho : Order.IsSuccLimit o) :
    x ∈ level R o ↔ ∃ i < o, x ∈ level R i := by
  constructor
  · intro hx
    rcases (mem_stage R o.toZFSet x).mp hx with hx|⟨a,ha,hx⟩
    · refine ⟨0,Ordinal.natCast_lt_of_isSuccLimit ho 0,?_⟩
      rwa [level_zero]
    · obtain ⟨i,hi,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ha
      refine ⟨i+1,ho.succ_lt hi,?_⟩
      rwa [level_succ]
  · rintro ⟨i,hi,hx⟩
    exact level_mono R hi.le hx

end TuringRigidity.RelativeConstructible

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_ElementarySatisfaction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

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

end
end TuringRigidity.SetModelIteration

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

theorem Definable.congr (h : Definable M P) (he : ∀ e, P e ↔ Q e) : Definable M Q := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨p,d,hd,fun e => (hp e).trans (he e)⟩

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

theorem Definable.existsMem (h : Definable M P) (i : ℕ) :
    Definable M (fun e => ∃ x ∈ e i, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.existsMem (2*i) (p.rename bindSlots),d,hd,?_⟩
  intro e
  simp only [Formula.Eval,mix_even,Formula.eval_rename_comp,bind_mix,hp]

theorem member_definable (C : Context M) (i j : ℕ) : Definable M (fun e => e i ∈ e j) :=
  ⟨.member (2*i) (2*j),fun _ => ZFSet.omega,fun _ => C.omega_mem,fun e => by simp [Formula.Eval]⟩

theorem equal_param {a : ZFSet.{u}} (ha : a ∈ M) (i : ℕ) :
    Definable M (fun e => e i = a) :=
  ⟨.equal (2*i) 1,fun _ => a,fun _ => ha,fun e => by simp [Formula.Eval,mix]⟩

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SentenceCodeDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.SentenceCoding
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions SetModelSyntax
universe u

variable {M : ZFSet.{u}}

theorem defOr {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hP : Definable M P) (hQ : Definable M Q) : Definable M (fun e => P e ∨ Q e) :=
  (hP.neg.and hQ.neg).neg.congr (fun _ => by tauto)

theorem defImp {P Q : (ℕ → ZFSet.{u}) → Prop}
    (hP : Definable M P) (hQ : Definable M Q) : Definable M (fun e => P e → Q e) :=
  (hP.and hQ.neg).neg.congr (fun _ => by tauto)

theorem defAllMem {P : (ℕ → ZFSet.{u}) → Prop}
    (h : Definable M P) (i : ℕ) : Definable M (fun e => ∀ x ∈ e i, P (cons x e)) :=
  (h.neg.existsMem i).neg.congr (fun _ => by simp)

theorem defSubset (C : Context M) (i j : ℕ) : Definable M (fun e => e i ⊆ e j) :=
  defAllMem (member_definable C 0 (j+1)) i

end TuringRigidity.SentenceCoding

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaParameterized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u

variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem Definable.toSigma (hM : Transitive M) (h : Definable M P) : SigmaDefinable M P := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.bounded p,d,hd,?_⟩
  intro e he
  exact (p.absolute M hM (mix e d) (by
    intro i; unfold mix; split <;> first | exact he _ | exact hd _)).trans (hp e)

theorem SigmaDefinable.existsSet (h : SigmaDefinable M P) :
    SigmaDefinable M (fun e => ∃ x ∈ M, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨.existsSet (p.rename bindSlots),d,hd,?_⟩
  intro e he
  simp only [SigmaFormula.Realize,SigmaFormula.realize_rename]
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  have hh := bind_mix x e d
  change (p.Realize M (cons x (mix e d) ∘ bindSlots)) ↔ _
  rw [hh]
  exact hp (cons x e) (by intro i; cases i; exact hx; exact he _)

theorem SigmaDefinable.congr (h : SigmaDefinable M P)
    (hPQ : ∀ e, (∀ i, e i ∈ M) → (P e ↔ Q e)) : SigmaDefinable M Q := by
  obtain ⟨p,d,hd,hp⟩ := h
  exact ⟨p,d,hd,fun e he => (hp e he).trans (hPQ e he)⟩

end TuringRigidity.BoundedDefinability

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

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaParameterizedClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.BoundedDefinability
open BoundedSetTheory TransitiveNameModel SetModelFunctions
universe u
variable {M : ZFSet.{u}} {P Q : (ℕ → ZFSet.{u}) → Prop}

theorem SigmaDefinable.subst (h : SigmaDefinable M P) (r : ℕ → ℕ) :
    SigmaDefinable M (fun e => P (e ∘ r)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  refine ⟨p.rename (slotMap r id),d,hd,?_⟩
  intro e he
  rw [SigmaFormula.realize_rename]
  change p.Realize M (mix e d ∘ slotMap r id) ↔ _
  simpa only [mix_slotMap,Function.comp_id] using hp (e ∘ r) (fun i => he (r i))

theorem SigmaDefinable.and (hP : SigmaDefinable M P) (hQ : SigmaDefinable M Q) :
    SigmaDefinable M (fun e => P e ∧ Q e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.conj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i; unfold mix; split <;> first | exact hd _ | exact hc _
  · intro e he
    rw [SigmaFormula.realize_conj,SigmaFormula.realize_rename,SigmaFormula.realize_rename]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    change p.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i)) ∧
      q.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i+1)) ↔ _
    rw [mix_slotMap,mix_slotMap,Function.comp_id,hd',hc',hp e he,hq e he]

theorem SigmaDefinable.or (h0 : (∅ : ZFSet.{u}) ∈ M)
    (hP : SigmaDefinable M P) (hQ : SigmaDefinable M Q) :
    SigmaDefinable M (fun e => P e ∨ Q e) := by
  obtain ⟨p,d,hd,hp⟩ := hP
  obtain ⟨q,c,hc,hq⟩ := hQ
  refine ⟨.disj (p.rename (slotMap id (fun i => 2*i)))
    (q.rename (slotMap id (fun i => 2*i+1))),mix d c,?_,?_⟩
  · intro i; unfold mix; split <;> first | exact hd _ | exact hc _
  · intro e he
    rw [SigmaFormula.realize_disj M h0,SigmaFormula.realize_rename,SigmaFormula.realize_rename]
    have hd' : mix d c ∘ (fun i => 2*i) = d := by funext i; simp
    have hc' : mix d c ∘ (fun i => 2*i+1) = c := by funext i; simp
    change p.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i)) ∨
      q.Realize M (mix e (mix d c) ∘ slotMap id (fun i => 2*i+1)) ↔ _
    rw [mix_slotMap,mix_slotMap,Function.comp_id,hd',hc',hp e he,hq e he]

theorem SigmaDefinable.impBounded (C : Context M)
    (hP : Definable M P) (hQ : SigmaDefinable M Q) :
    SigmaDefinable M (fun e => P e → Q e) := by
  apply ((hP.neg.toSigma C.transitive).or (C.nat_mem 0) hQ).congr
  intro e _
  classical
  tauto

theorem SigmaDefinable.allMem (hM : Transitive M) (hT : SourceT M)
    (h : SigmaDefinable M P) (a : ℕ) :
    SigmaDefinable M (fun e => ∀ x ∈ e a, P (cons x e)) := by
  obtain ⟨p,d,hd,hp⟩ := h
  have hC := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  refine ⟨.allMem (2*a) (p.rename bindSlots),d,hd,?_⟩
  intro e he
  rw [SigmaFormula.realize_allMem M hM hT.pairing hT.union hT.separation.finitePrefix.bounded
    hT.replacement.finitePrefix hT.infinity hC _ _ _ (by
      intro i; unfold mix; split <;> first | exact he _ | exact hd _),mix_even]
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  rw [SigmaFormula.realize_rename]
  change p.Realize M (cons x (mix e d) ∘ bindSlots) ↔ _
  rw [bind_mix]
  exact hp (cons x e) (by intro i; cases i; exact hM _ (he a) x hx; exact he _)

end TuringRigidity.BoundedDefinability

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_HierarchySyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u
variable {M : ZFSet.{u}}

theorem stageStep_definable (C : Context M) (s f r x A : ℕ) :
    Definable M (fun e => StageStep (e s) (e f) (e r) (e x) (e A)) := by
  have hn := defAllMem (defOr (member_definable C 0 (s+1))
    ((((defPairMem C 1 0 (f+3)).and (member_definable C 2 0)).existsMem (r+2)).existsMem (x+1))) A
  have hc := defAllMem (defAllMem (defImp (defPairMem C 1 0 (f+2))
    (defSubset C 0 (A+2))) (r+1)) x
  exact (defSubset C s A).and (hn.and hc)

theorem functionGraph_definable (C : Context M) (d r f : ℕ) :
    Definable M (fun e => FunctionGraph (e d) (e r) (e f)) := by
  refine ⟨.functionGraph (2*f) (2*d) (2*r),fun _ => ZFSet.omega,
    fun _ => C.omega_mem,?_⟩
  intro e
  simp only [Formula.eval_functionGraph,mix_even,FunctionGraph]

theorem sigma_binary_relation (P : ZFSet.{u} → ZFSet.{u} → Prop)
    (h : SigmaDefinable M (fun e => P (e 1) (e 0))) :
    ∃ p : SigmaFormula, ∃ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ M) ∧
      ∀ x ∈ M, ∀ y ∈ M, p.Realize M (cons y (cons x a)) ↔ P x y := by
  obtain ⟨p,a,ha,hp⟩ := h
  let r : ℕ → ℕ := fun i => if i % 2 = 0 then (if i / 2 = 0 then 0 else 1) else i/2+2
  refine ⟨p.rename r,a,ha,?_⟩
  intro x hx y hy
  rw [SigmaFormula.realize_rename]
  have he : cons y (cons x a) ∘ r = mix (cons y (fun _ => x)) a := by
    apply parity_ext
    · intro n
      cases n with
      | zero => rfl
      | succ n => simp [r,show ¬ 2 * (n+1) ≤ 1 by omega]
    · intro n; simp [r,Nat.add_div]
  change p.Realize M (cons y (cons x a) ∘ r) ↔ _
  rw [he]
  exact hp (cons y (fun _ => x)) (by intro i; cases i; exact hy; exact hx)

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

theorem internal_ordinal_zero (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    (0 : Ordinal.{u}).toZFSet ∈ M := by
  rw [Ordinal.toZFSet_zero]
  exact hM _ (sourceT_omega_mem M hM hT) _ ZFSet.omega_zero

theorem internal_ordinal_succ (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : (o+1).toZFSet ∈ M := by
  rw [Ordinal.toZFSet_add_one]
  have eq : insert o.toZFSet o.toZFSet = ({o.toZFSet} : ZFSet.{u}) ∪ o.toZFSet := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
  rw [eq]
  exact binary_union_mem M hM hT.pairing hT.union
    (singleton_mem M hM hT.pairing ho) ho

theorem internal_ordinal_max (M : ZFSet.{u}) {i j : Ordinal.{u}}
    (hi : i.toZFSet ∈ M) (hj : j.toZFSet ∈ M) : (max i j).toZFSet ∈ M := by
  rcases le_total i j with h|h
  · simpa only [max_eq_right h] using hj
  · simpa only [max_eq_left h] using hi

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_RelativeModelSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel BoundedDefinability SetModelFunctions
universe u

theorem eval_ordinalFormula (i : ℕ) (e : ℕ → ZFSet.{u}) :
    (ordinalFormula i).Eval e ↔ (e i).IsOrdinal := by
  rw [ZFSet.isOrdinal_iff_forall_mem_isTransitive]
  simp only [ordinalFormula,Formula.Eval,Formula.eval_transitive,
    Formula.eval_allMem,cons_zero]
  rfl

theorem ordinal_definable {M : ZFSet.{u}} (C : Context M) (i : ℕ) :
    Definable M (fun e => (e i).IsOrdinal) :=
  ⟨ordinalFormula (2*i),fun _ => ZFSet.omega,fun _ => C.omega_mem,
    fun e => by rw [eval_ordinalFormula,mix_even]⟩

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem mem_ordinalCut (A x : ZFSet.{u}) :
    x ∈ ordinalCut A ↔ x ∈ A ∧ x.IsOrdinal := ZFSet.mem_sep

theorem ordinalCut_isOrdinal (A : ZFSet.{u}) (hA : Transitive A) :
    (ordinalCut A).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro x hx y hy
    obtain ⟨hx,ho⟩ := (mem_ordinalCut A x).mp hx
    exact (mem_ordinalCut A y).mpr ⟨hA x hx y hy,ho.mem hy⟩
  · intro x hx; exact ((mem_ordinalCut A x).mp hx).2

theorem ordinalHeight_toZFSet (A : ZFSet.{u}) (hA : Transitive A) :
    (ordinalHeight A).toZFSet = ordinalCut A := (ordinalCut_isOrdinal A hA).toZFSet_rank_eq

theorem ordinal_mem_iff_height (A : ZFSet.{u}) (hA : Transitive A) (o : Ordinal.{u}) :
    o.toZFSet ∈ A ↔ o < ordinalHeight A := by
  rw [← Ordinal.toZFSet_mem_toZFSet_iff,ordinalHeight_toZFSet A hA,mem_ordinalCut]
  exact (and_iff_left (ZFSet.isOrdinal_toZFSet o)).symm

theorem ordinal_subset_iff_height (A : ZFSet.{u}) (hA : Transitive A) (o : Ordinal.{u}) :
    o.toZFSet ⊆ A ↔ o ≤ ordinalHeight A := by
  rw [← Ordinal.toZFSet_subset_toZFSet_iff,ordinalHeight_toZFSet A hA]
  constructor
  · intro h x hx
    exact (mem_ordinalCut A x).mpr ⟨h hx,(ZFSet.isOrdinal_toZFSet o).mem hx⟩
  · intro h x hx; exact ((mem_ordinalCut A x).mp (h hx)).1

theorem ordinalSentence_bound : ordinalSentence.bound = 1 := by rfl

theorem ordinalSentence_spec (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : e 0 ∈ A) :
    ordinalSentence.Sat (A : Set ZFSet) e ↔ (e 0).IsOrdinal := by
  have hs := ordinalSentence.finite_support (A : Set ZFSet) e (fun _ => e 0) (by
    intro i hi
    rw [ordinalSentence_bound] at hi
    have : i = 0 := by omega
    subst i; rfl)
  rw [hs]
  exact (bounded_sat _ _ _).trans
    (((ordinalFormula 0).absolute A hA _ (fun _ => he)).trans (eval_ordinalFormula 0 _))

theorem ordinalCut_mem_definablePower (A : ZFSet.{u}) (hA : Transitive A) :
    ordinalCut A ∈ definablePower A := by
  apply (mem_definablePower A _).mpr
  refine ⟨0,ordinalSentence,Fin.elim0,by rw [ordinalSentence_bound],fun i => Fin.elim0 i,?_⟩
  apply ZFSet.ext; intro x
  rw [mem_ordinalCut,mem_definedSubset]
  apply and_congr_right; intro hx
  exact (ordinalSentence_spec A hA (cons x (tupleEnv (Fin.elim0 : Fin 0 → ZFSet.{u}))) hx).symm

theorem ordinal_definablePower_iff (A : ZFSet.{u}) (hA : Transitive A) (o : Ordinal.{u}) :
    o.toZFSet ∈ definablePower A ↔ o ≤ ordinalHeight A := by
  constructor
  · intro ho
    exact (ordinal_subset_iff_height A hA o).mp (subset_of_mem_definablePower ho)
  · intro ho
    rcases lt_or_eq_of_le ho with ho|rfl
    · exact subset_definablePower hA ((ordinal_mem_iff_height A hA o).mpr ho)
    · rw [ordinalHeight_toZFSet A hA]
      exact ordinalCut_mem_definablePower A hA

theorem ordinalHeight_definablePower (A : ZFSet.{u}) (hA : Transitive A) :
    ordinalHeight (definablePower A) = ordinalHeight A + 1 := by
  apply le_antisymm
  · by_contra h
    have hm := (ordinal_mem_iff_height _ (definablePower_transitive hA) _).mpr (lt_of_not_ge h)
    have := (ordinal_definablePower_iff A hA _).mp hm
    exact (not_le_of_gt (lt_add_one (ordinalHeight A))) this
  · apply Order.add_one_le_iff.mpr
    exact (ordinal_mem_iff_height _ (definablePower_transitive hA) _).mp
      ((ordinal_definablePower_iff A hA _).mpr le_rfl)

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_LevelOrdinalHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem ordinalHeight_level (R : ZFSet.{u}) (o : Ordinal.{u}) :
    ordinalHeight (level R o) = ordinalHeight (seed R) + o := by
  induction o using Ordinal.limitRecOn with
  | zero => simp only [level_zero,add_zero]
  | add_one o ih =>
    rw [level_succ,ordinalHeight_definablePower _ (level_transitive R o),ih,add_assoc]
  | limit o ho ih =>
    apply le_antisymm
    · by_contra h
      have hx := (ordinal_mem_iff_height _ (level_transitive R o) _).mpr (lt_of_not_ge h)
      obtain ⟨i,hi,hx⟩ := (mem_level_limit R _ o ho).mp hx
      have hx' := (ordinal_mem_iff_height _ (level_transitive R i) _).mp hx
      rw [ih i hi] at hx'
      exact (not_lt_of_ge (add_le_add (le_refl (ordinalHeight (seed R))) hi.le)) hx'
    · by_contra h
      obtain ⟨i,hi,hi'⟩ := Ordinal.lt_add_iff_of_isSuccLimit ho |>.mp (lt_of_not_ge h)
      rw [← ih i hi] at hi'
      have hx := (ordinal_mem_iff_height _ (level_transitive R i) _).mpr hi'
      have hx' := level_mono R hi.le hx
      exact (lt_irrefl _) ((ordinal_mem_iff_height _ (level_transitive R o) _).mp hx')

theorem ordinal_mem_level_iff (R : ZFSet.{u}) (o a : Ordinal.{u}) :
    a.toZFSet ∈ level R o ↔ a < ordinalHeight (seed R) + o := by
  rw [ordinal_mem_iff_height _ (level_transitive R o),ordinalHeight_level]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalHeightDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem ordinalCut_mem_model (M A : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hA : A ∈ M) : ordinalCut A ∈ M := by
  have hs := sep_mem M hM hS (ordinalFormula 0) (fun _ => A) (fun _ => hA) hA
  have heq : A.sep (fun x => (ordinalFormula 0).Eval (cons x (fun _ => A))) = ordinalCut A := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep,mem_ordinalCut,eval_ordinalFormula,cons_zero]
  exact heq ▸ hs

theorem ordinalHeight_mem_model (M A : ZFSet.{u}) (hM : Transitive M)
    (hS : Separation M) (hA : A ∈ M) (hAt : Transitive A) :
    (ordinalHeight A).toZFSet ∈ M := by
  rw [ordinalHeight_toZFSet A hAt]
  exact ordinalCut_mem_model M A hM hS hA

theorem internal_ordinal_downward (M : ZFSet.{u}) (hM : Transitive M)
    {a b : Ordinal.{u}} (hb : b.toZFSet ∈ M) (hab : a ≤ b) : a.toZFSet ∈ M := by
  rcases lt_or_eq_of_le hab with h|rfl
  · exact hM _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr h)
  · exact hb

theorem internal_difference_successor (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    (a-b+1).toZFSet ∈ M :=
  internal_ordinal_succ M hM hT _
    (internal_ordinal_downward M hM ha (Ordinal.sub_le_self a b))

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderType
attribute [-instance] _root_.OAI.TuringRigidity.BoundedSetTheory.InternalGeneric.extension_countable _root_.OAI.TuringRigidity.ElementaryModel.collapsed_countable _root_.OAI.TuringRigidity.InternalCohen.cohenTop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem value_isOrdinal {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) (x : ZFSet.{u}) (hx : x ∈ d) :
    (value d r wf x).IsOrdinal := by
  induction x using wf.induction with
  | h x ih =>
    apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
    constructor
    · intro y hy z hz
      obtain ⟨b,hb,hbx,rfl⟩ := (mem_value d r wf x y).mp hy
      obtain ⟨a,ha,hab,rfl⟩ := (mem_value d r wf b z).mp hz
      exact (mem_value d r wf x _).mpr ⟨a,ha,ht a ha b hb x hx hab hbx,rfl⟩
    · intro y hy
      obtain ⟨a,ha,hax,rfl⟩ := (mem_value d r wf x y).mp hy
      exact ih a ⟨ha,hax⟩ ha

theorem mem_ordinalRange (d r : ZFSet.{u}) (wf : WellFounded (Rel d r)) (z : ZFSet.{u}) :
    z ∈ ordinalRange d r wf ↔ ∃ x ∈ d, z = value d r wf x := by
  rw [ordinalRange,ZFSet.mem_range]
  constructor
  · rintro ⟨s,hs⟩; exact ⟨label d s,label_mem d s,hs.symm⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨s,rfl⟩ := label_surjective d hx
    exact ⟨s,rfl⟩

theorem ordinalRange_isOrdinal {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) : (ordinalRange d r wf).IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  constructor
  · intro x hx y hy
    obtain ⟨a,_,rfl⟩ := (mem_ordinalRange d r wf x).mp hx
    obtain ⟨b,hb,_,rfl⟩ := (mem_value d r wf a y).mp hy
    exact (mem_ordinalRange d r wf _).mpr ⟨b,hb,rfl⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := (mem_ordinalRange d r wf x).mp hx
    exact value_isOrdinal wf ht a ha

theorem orderType_toZFSet {d r : ZFSet.{u}} (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) : (orderType d r wf).toZFSet = ordinalRange d r wf :=
  (ordinalRange_isOrdinal wf ht).toZFSet_rank_eq

theorem orderType_internal (M d r : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (hd : d ∈ M) (hr : r ∈ M) (wf : WellFounded (Rel d r))
    (ht : TransitiveOn d r) :
    (orderType d r wf).toZFSet ∈ M ∧
      ∃ f ∈ M, Graph d r d (orderType d r wf).toZFSet f ∧
        ∀ z ∈ (orderType d r wf).toZFSet, ∃ x ∈ d, ZFSet.pair x z ∈ f := by
  obtain ⟨f,hf,hg⟩ := internal_graph M d r hM hP hU hPow hS hR hd hr wf
  have heq : graphRange d f = ordinalRange d r wf := by
    apply ZFSet.ext; intro z
    exact (hg.range_iff wf z).trans (mem_ordinalRange d r wf z).symm
  have hm : ordinalRange d r wf ∈ M := heq ▸ graphRange_mem M hM hU hS hd hf
  rw [orderType_toZFSet wf ht]
  refine ⟨hm,f,hf,?_,?_⟩
  · refine ⟨(fun _ hx => hx),(fun _ _ _ hy _ => hy),?_,?_,?_⟩
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := (hg.mem_iff wf z).mp hz
      exact ⟨x,hx,_,(mem_ordinalRange d r wf _).mpr ⟨x,hx,rfl⟩,rfl⟩
    · intro x hx
      refine ⟨value d r wf x,(mem_ordinalRange d r wf _).mpr ⟨x,hx,rfl⟩,
        (hg.mem_iff wf _).mpr ⟨x,hx,rfl⟩,?_⟩
      intro z _ hxz
      obtain ⟨y,_,he⟩ := (hg.mem_iff wf _).mp hxz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      rfl
    · intro x hx z _ hxz
      obtain ⟨y,hy,he⟩ := (hg.mem_iff wf _).mp hxz
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      constructor
      · intro z hz
        obtain ⟨y,hy,hyx,rfl⟩ := (mem_value d r wf x z).mp hz
        exact ⟨y,hy,hyx,(hg.mem_iff wf _).mpr ⟨y,hy,rfl⟩⟩
      · intro y hy hyx z _ hyz
        obtain ⟨w,_,he⟩ := (hg.mem_iff wf _).mp hyz
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
        exact (mem_value d r wf x _).mpr ⟨y,hy,hyx,rfl⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := (mem_ordinalRange d r wf z).mp hz
    exact ⟨x,hx,(hg.mem_iff wf _).mpr ⟨x,hx,rfl⟩⟩

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderTypeSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

theorem OrderTypeCertificate.exact {d r a f : ZFSet.{u}}
    (wf : WellFounded (Rel d r)) (ht : TransitiveOn d r)
    (hc : OrderTypeCertificate d r a f) : a = (orderType d r wf).toZFSet := by
  rw [orderType_toZFSet wf ht]
  apply ZFSet.ext; intro z
  rw [mem_ordinalRange]
  constructor
  · intro hz
    obtain ⟨x,hx,hxz⟩ := hc.2.2 z hz
    exact ⟨x,hx,hc.2.1.correct wf x hx z hz hxz⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨z,hz,hxz,_⟩ := hc.2.1.2.2.2.1 x hx
    exact hc.2.1.correct wf x hx z hz hxz ▸ hz

theorem orderTypeCertificate_exists (M d r : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hd : d ∈ M) (hr : r ∈ M)
    (wf : WellFounded (Rel d r)) (ht : TransitiveOn d r) :
    (orderType d r wf).toZFSet ∈ M ∧
      ∃ f ∈ M, OrderTypeCertificate d r (orderType d r wf).toZFSet f := by
  obtain ⟨ha,f,hf,hg,ho⟩ := orderType_internal M d r hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hd hr wf ht
  exact ⟨ha,f,hf,ZFSet.isOrdinal_toZFSet _,hg,ho⟩

theorem orderTypeMatrix_eval (a d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (orderTypeMatrix a d r f).Eval e ↔ OrderTypeCertificate (e d) (e r) (e a) (e f) := by
  simp only [orderTypeMatrix,OrderTypeCertificate,Formula.Eval,eval_ordinalFormula,
    Code.eval_graph,Formula.eval_allMem,Formula.eval_pairMem,cons_zero,cons_succ]

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalOrderPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem value_of_ordinal_presentation (d r : ZFSet.{u}) (o : Ordinal.{u})
    (wf : WellFounded (Rel d r)) (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y)
    (x : ZFSet.{u}) (hx : x ∈ d) : value d r wf x = j x := by
  induction x using wf.induction with
  | h x ih =>
    apply ZFSet.ext; intro z
    rw [mem_value]
    constructor
    · rintro ⟨y,hy,hyx,rfl⟩
      rw [ih y ⟨hy,hyx⟩ hy]
      exact (he y hy x hx).mp hyx
    · intro hz
      have hzo := (ZFSet.isOrdinal_toZFSet o).subset_of_mem (hj x hx) hz
      obtain ⟨y,hy,hyz⟩ := hs z hzo
      have hyx : ZFSet.pair y x ∈ r := (he y hy x hx).mpr (hyz ▸ hz)
      exact ⟨y,hy,hyx,hyz.symm.trans (ih y ⟨hy,hyx⟩ hy).symm⟩

theorem orderType_of_ordinal_presentation (d r : ZFSet.{u}) (o : Ordinal.{u})
    (wf : WellFounded (Rel d r)) (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y) :
    orderType d r wf = o := by
  have hr : ordinalRange d r wf = o.toZFSet := by
    apply ZFSet.ext; intro z
    rw [mem_ordinalRange]
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [value_of_ordinal_presentation d r o wf j hj hs he x hx]
      exact hj x hx
    · intro hz
      obtain ⟨x,hx,heq⟩ := hs z hz
      exact ⟨x,hx,heq.symm.trans (value_of_ordinal_presentation d r o wf j hj hs he x hx).symm⟩
  unfold orderType
  rw [hr,Ordinal.rank_toZFSet]

theorem ordinal_internal_of_presentation (M d r : ZFSet.{u}) (o : Ordinal.{u})
    (hM : Transitive M) (hT : SourceT M) (hd : d ∈ M) (hr : r ∈ M) (hon : On d r)
    (j : ZFSet.{u} → ZFSet.{u})
    (hj : ∀ x ∈ d, j x ∈ o.toZFSet)
    (hs : ∀ z ∈ o.toZFSet, ∃ x ∈ d, j x = z)
    (he : ∀ x ∈ d, ∀ y ∈ d, ZFSet.pair x y ∈ r ↔ j x ∈ j y) :
    o.toZFSet ∈ M ∧ ∃ f ∈ M, Presents d f j ∧ OrderTypeCertificate d r o.toZFSet f := by
  have wf : WellFounded (Rel d r) := by
    apply (InvImage.wf j ZFSet.mem_wf).mono
    intro x y hxy
    exact (he x hxy.1 y (right_mem hon hxy.2)).mp hxy.2
  have ht : TransitiveOn d r := by
    intro x hx y hy z hz hxy hyz
    apply (he x hx z hz).mpr
    exact ((ZFSet.isOrdinal_toZFSet o).mem (hj z hz)).subset_of_mem
      ((he y hy z hz).mp hyz) ((he x hx y hy).mp hxy)
  have hval := value_of_ordinal_presentation d r o wf j hj hs he
  have heq := orderType_of_ordinal_presentation d r o wf j hj hs he
  obtain ⟨ha,f,hf,hc⟩ := orderTypeCertificate_exists M d r hM hT hd hr wf ht
  rw [heq] at ha hc
  refine ⟨ha,f,hf,?_,hc⟩
  intro z
  rw [hc.2.1.mem_iff wf]
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  rw [hval x hx]

end TuringRigidity.RelationCollapse

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

theorem productLessFormula_eval (a b x y : ℕ) (e : ℕ → ZFSet.{u}) :
    (productLessFormula a b x y).Eval e ↔ ProductLess (e a) (e b) (e x) (e y) := by
  simp [productLessFormula,Formula.Eval,ProductLess]

theorem productRelationFormula_eval (a b p : ZFSet.{u}) :
    productRelationFormula.Eval (cons p (cons (ZFSet.prod b a) (cons a (fun _ => b)))) ↔
      ∃ x ∈ ZFSet.prod b a, ∃ y ∈ ZFSet.prod b a,
        p = ZFSet.pair x y ∧ ProductLess a b x y := by
  simp [productRelationFormula,Formula.Eval,productLessFormula_eval]

theorem productRelation_mem (M a b : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (ha : a ∈ M) (hb : b ∈ M) : productRelation a b ∈ M := by
  have hd := product_mem M hM hP hU hPow hS hb ha
  let e := cons (ZFSet.prod b a) (cons a (fun _ => b))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact hd
    · exact ha
    · exact hb
  have hs := sep_mem M hM hS productRelationFormula e he
    (product_mem M hM hP hU hPow hS hd hd)
  have eq : ZFSet.sep (fun p => productRelationFormula.Eval (cons p e))
      (ZFSet.prod (ZFSet.prod b a) (ZFSet.prod b a)) = productRelation a b := by
    apply ZFSet.ext; intro p
    simp only [productRelation,ZFSet.mem_sep,e,productRelationFormula_eval]
  exact eq ▸ hs

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

theorem productValue_mem (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ ZFSet.prod b.toZFSet a.toZFSet) : productValue a x ∈ (a*b).toZFSet := by
  obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
  obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
  obtain ⟨d,hd,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
  rw [productValue_pair,Ordinal.rank_toZFSet,Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff]
  exact Ordinal.lt_mul_iff.mpr ⟨c,hc,d,hd,rfl⟩

theorem productValue_surjective (a b : Ordinal.{u}) (z : ZFSet.{u})
    (hz : z ∈ (a*b).toZFSet) :
    ∃ x ∈ ZFSet.prod b.toZFSet a.toZFSet, productValue a x = z := by
  obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
  obtain ⟨q,hq,r,hr,rfl⟩ := Ordinal.lt_mul_iff.mp hc
  refine ⟨ZFSet.pair q.toZFSet r.toZFSet,ZFSet.mem_prod.mpr
    ⟨_,Ordinal.toZFSet_mem_toZFSet_iff.mpr hq,_,Ordinal.toZFSet_mem_toZFSet_iff.mpr hr,rfl⟩,?_⟩
  rw [productValue_pair,Ordinal.rank_toZFSet,Ordinal.rank_toZFSet]

theorem productRelation_transitive (a b : Ordinal.{u}) :
    TransitiveOn (ZFSet.prod b.toZFSet a.toZFSet) (productRelation a.toZFSet b.toZFSet) := by
  intro x hx y hy z hz hxy hyz
  apply (productValue_relation a b x hx z hz).mpr
  exact ((ZFSet.isOrdinal_toZFSet (a*b)).mem (productValue_mem a b z hz)).subset_of_mem
    ((productValue_relation a b y hy z hz).mp hyz) ((productValue_relation a b x hx y hy).mp hxy)

theorem product_orderType (a b : Ordinal.{u}) :
    orderType (ZFSet.prod b.toZFSet a.toZFSet) (productRelation a.toZFSet b.toZFSet)
      (productRelation_wellFounded a b) = a*b :=
  orderType_of_ordinal_presentation _ _ _ _ (productValue a)
    (productValue_mem a b) (productValue_surjective a b) (productValue_relation a b)

theorem ordinal_mul_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    (a*b).toZFSet ∈ M ∧ ∃ f ∈ M,
      Presents (ZFSet.prod b.toZFSet a.toZFSet) f (productValue a) ∧
      OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
        (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f :=
  ordinal_internal_of_presentation M _ _ _ hM hT
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hb ha)
    (productRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded ha hb)
    (productRelation_on _ _) (productValue a) (productValue_mem a b)
    (productValue_surjective a b) (productValue_relation a b)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductSyntax
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem productDomainMatrix_eval (d a b : ℕ) (e : ℕ → ZFSet.{u}) :
    (productDomainMatrix d a b).Eval e ↔ e d = ZFSet.prod (e b) (e a) := by
  simp only [productDomainMatrix,Formula.Eval,Formula.eval_allMem,
    Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ]
  constructor
  · rintro ⟨hsub,hsup⟩
    apply ZFSet.ext; intro x
    constructor
    · intro hx; exact ZFSet.mem_prod.mpr (hsub x hx)
    · intro hx
      obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
      exact hsup s hs t ht
  · intro heq
    rw [heq]
    exact ⟨fun x hx => ZFSet.mem_prod.mp hx,
      fun s hs t ht => ZFSet.mem_prod.mpr ⟨s,hs,t,ht,rfl⟩⟩

theorem productRelationMatrix_eval (r d a b : ℕ) (e : ℕ → ZFSet.{u})
    (hd : e d = ZFSet.prod (e b) (e a)) :
    (productRelationMatrix r d a b).Eval e ↔ e r = productRelation (e a) (e b) := by
  simp only [productRelationMatrix,Formula.Eval,Formula.eval_allMem,Formula.eval_orderedPair,
    Formula.eval_imp,Formula.eval_pairMem,cons_zero,cons_succ]
  have h3 (x y p : ZFSet.{u}) := productLessFormula_eval (a+3) (b+3) 1 0
    (cons y (cons x (cons p e)))
  have h2 (x y : ZFSet.{u}) := productLessFormula_eval (a+2) (b+2) 1 0
    (cons y (cons x e))
  simp only [h3,h2,cons_zero,cons_succ,hd]
  constructor
  · rintro ⟨hr,hall⟩
    apply ZFSet.ext; intro p
    constructor
    · intro hp
      obtain ⟨x,hx,y,hy,rfl,hxy⟩ := hr p hp
      exact (pair_mem_productRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩
    · intro hp
      obtain ⟨_,x,hx,y,hy,rfl,hxy⟩ := ZFSet.mem_sep.mp hp
      exact hall x hx y hy hxy
  · intro heq
    rw [heq]
    exact ⟨fun p hp => (ZFSet.mem_sep.mp hp).2,
      fun x hx y hy hxy => (pair_mem_productRelation _ _ _ _).mpr ⟨hx,hy,hxy⟩⟩

theorem productMatrix_eval (c a b d r f : ℕ) (e : ℕ → ZFSet.{u}) :
    (productMatrix c a b d r f).Eval e ↔
      e d = ZFSet.prod (e b) (e a) ∧ e r = productRelation (e a) (e b) ∧
      OrderTypeCertificate (e d) (e r) (e c) (e f) := by
  simp only [productMatrix,Formula.Eval,productDomainMatrix_eval]
  apply and_congr_right; intro hd
  rw [productRelationMatrix_eval r d a b e hd,orderTypeMatrix_eval]

theorem productSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    productSentence.Sat (A : Set ZFSet) e ↔
      ∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A,
        d = ZFSet.prod (e 2) (e 1) ∧ r = productRelation (e 1) (e 2) ∧
          OrderTypeCertificate d r (e 0) f := by
  change (∃ d ∈ A, ∃ r ∈ A, ∃ f ∈ A,
    (fromBounded _).Sat _ (cons f (cons r (cons d e)))) ↔ _
  apply exists_congr; intro d
  apply and_congr_right; intro hd
  apply exists_congr; intro r
  apply and_congr_right; intro hr
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  rw [bounded_sat,Formula.absolute _ A hA _ (by
    intro i; rcases i with _|_|_|i <;> simp [cons,he,hd,hr,hf]),productMatrix_eval]
  rfl

theorem productSentence_sound (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSentence.Sat (A : Set ZFSet) e → e 0 = (a*b).toZFSet := by
  intro h
  obtain ⟨d,_,r,_,f,_,hd,hr,hc⟩ := (productSentence_semantics A hA e he).mp h
  rw [ha,hb] at hd hr
  rw [hd,hr] at hc
  exact (hc.exact (productRelation_wellFounded a b) (productRelation_transitive a b)).trans
    (congrArg Ordinal.toZFSet (product_orderType a b))

theorem productSentence_spec_of_certificate (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hd : ZFSet.prod b.toZFSet a.toZFSet ∈ A)
    (hr : productRelation a.toZFSet b.toZFSet ∈ A)
    (hf : ∃ f ∈ A, OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
      (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f) :
    productSentence.Sat (A : Set ZFSet) e ↔ e 0 = (a*b).toZFSet := by
  refine ⟨productSentence_sound A hA e he a b ha hb,?_⟩
  intro hc
  obtain ⟨f,hf,hcert⟩ := hf
  apply (productSentence_semantics A hA e he).mpr
  exact ⟨_,hd,_,hr,f,hf,by rw [ha,hb],by rw [ha,hb],hc ▸ hcert⟩

theorem productSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSentence.Sat (M : Set ZFSet) e ↔ e 0 = (a*b).toZFSet := by
  have haM : a.toZFSet ∈ M := ha ▸ he 1
  have hbM : b.toZFSet ∈ M := hb ▸ he 2
  obtain ⟨_,f,hf,_,hc⟩ := ordinal_mul_internal M hM hT a b haM hbM
  exact productSentence_spec_of_certificate M hM e he a b ha hb
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hbM haM)
    (productRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded haM hbM)
    ⟨f,hf,hc⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem toZFSet_nat (n : ℕ) : (n : Ordinal.{u}).toZFSet = natSet n := by
  induction n with
  | zero => simp [natSet]
  | succ n ih => rw [Nat.cast_add_one,Ordinal.toZFSet_add_one,ih]; rfl

theorem toZFSet_omega : Ordinal.omega0.toZFSet = ZFSet.omega.{u} := by
  apply ZFSet.ext; intro x
  rw [Ordinal.mem_toZFSet_iff,mem_omega]
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp ha
    exact ⟨n,toZFSet_nat n⟩
  · rintro ⟨n,rfl⟩
    exact ⟨n,Ordinal.natCast_lt_omega0 n,toZFSet_nat n⟩

theorem ordinal_mul_omega_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (a*Ordinal.omega0).toZFSet ∈ M := by
  have ho : Ordinal.omega0.toZFSet ∈ M := by
    simpa only [toZFSet_omega] using
      omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  exact (ordinal_mul_internal M hM hT a Ordinal.omega0 ha ho).1

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalProductReplacement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem productSigma_sentence : fromSigma productSigma = productSentence := rfl

theorem productSigma_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) (a b : Ordinal.{u})
    (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    productSigma.Realize M e ↔ e 0 = (a*b).toZFSet := by
  rw [← sigma_sat,productSigma_sentence]
  exact productSentence_sourceT M hM hT e he a b ha hb

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerStage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

theorem omegaPower_members (a : Ordinal.{u}) (z : ZFSet.{u}) :
    z ∈ (Ordinal.omega0 ^ a).toZFSet ↔ z ∈ (1 : Ordinal.{u}).toZFSet ∨
      ∃ x ∈ a.toZFSet, z ∈ omegaNext x := by
  constructor
  · intro hz
    by_cases ha : a = 0
    · left; simpa [ha] using hz
    · obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      obtain ⟨b,hb,n,hn⟩ := (Ordinal.lt_omega0_opow ha).mp hc
      refine Or.inr ⟨b.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hb,?_⟩
      rw [omegaNext,Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff]
      exact hn.trans (Ordinal.opow_mul_lt_opow (Ordinal.natCast_lt_omega0 n) (lt_add_one b))
  · rintro (hz|⟨x,hx,hz⟩)
    · exact Ordinal.toZFSet_monotone (Order.one_le_iff_ne_zero.mpr (Ordinal.opow_ne_zero _ Ordinal.omega0_ne_zero)) hz
    · obtain ⟨b,hb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
      change z ∈ (Ordinal.omega0 ^ (b.toZFSet.rank+1)).toZFSet at hz
      rw [Ordinal.rank_toZFSet] at hz
      exact Ordinal.toZFSet_monotone
        (Ordinal.opow_le_opow_right Ordinal.omega0_pos (Order.succ_le_of_lt hb)) hz

theorem OmegaGraph.correct {M d r f : ZFSet.{u}} (h : OmegaGraph M d r f)
    (x : ZFSet.{u}) (hx : x ∈ d) (v : ZFSet.{u}) (hv : v ∈ r)
    (hfv : ZFSet.pair x v ∈ f) : v = omegaNext x := by
  induction x using ZFSet.inductionOn generalizing v with
  | h x ih =>
    obtain ⟨A,_,hs,_,rfl⟩ := h.2.2 x hx v hv hfv
    have hxo := h.1.mem hx
    have he : A = (Ordinal.omega0 ^ x.rank).toZFSet := by
      apply ZFSet.ext; intro z
      rw [omegaPower_members,hxo.toZFSet_rank_eq]
      constructor
      · intro hz
        rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
        · exact Or.inl hz
        · exact Or.inr ⟨y,hy,(ih y hy (h.1.subset_of_mem hx hy) w hw hfw) ▸ hz⟩
      · rintro (hz|⟨y,hy,hz⟩)
        · exact hs.1 hz
        · obtain ⟨w,hw,hfw,_⟩ := h.2.1.2 y (h.1.subset_of_mem hx hy)
          rw [← ih y hy (h.1.subset_of_mem hx hy) w hw hfw] at hz
          exact hs.2.2 y hy w hw hfw hz
    rw [he,Ordinal.rank_toZFSet,omegaNext,Ordinal.opow_add_one]

theorem OmegaGraph.mem_iff {M d r f : ZFSet.{u}} (h : OmegaGraph M d r f) (z : ZFSet.{u}) :
    z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x) := by
  constructor
  · intro hz
    obtain ⟨x,hx,v,hv,rfl⟩ := h.2.1.1 z hz
    exact ⟨x,hx,by rw [h.correct x hx v hv hz]⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨v,hv,hfv,_⟩ := h.2.1.2 x hx
    rw [← h.correct x hx v hv hfv]
    exact hfv

theorem OmegaGraph.unique {M N d r t f g : ZFSet.{u}}
    (hf : OmegaGraph M d r f) (hg : OmegaGraph N d t g) : f = g := by
  apply ZFSet.ext; intro z
  exact (hf.mem_iff z).trans (hg.mem_iff z).symm

theorem omegaStageImage (d f x : ZFSet.{u}) (hd : d.IsOrdinal) (hx : x ∈ d)
    (hf : ∀ z, z ∈ f ↔ ∃ y ∈ d, z = ZFSet.pair y (omegaNext y)) :
    stageImage (1 : Ordinal.{u}).toZFSet x f = (Ordinal.omega0 ^ x.rank).toZFSet := by
  apply ZFSet.ext; intro z
  rw [mem_stageImage,omegaPower_members,(hd.mem hx).toZFSet_rank_eq]
  apply or_congr_right
  constructor
  · rintro ⟨y,hy,w,hfw,hz⟩
    obtain ⟨v,_,hp⟩ := (hf _).mp hfw
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact ⟨y,hy,hz⟩
  · rintro ⟨y,hy,hz⟩
    exact ⟨y,hy,_,(hf _).mpr ⟨y,hd.subset_of_mem hx hy,rfl⟩,hz⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem insert_self_mem (M : ZFSet.{u}) (hM : Transitive M) (hP : Pairing M)
    (hU : BoundedSetTheory.Union M) {x : ZFSet.{u}} (hx : x ∈ M) : insert x x ∈ M := by
  have he : insert x x = ({x} : ZFSet.{u}) ∪ x := by
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_insert_iff,ZFSet.mem_union,ZFSet.mem_singleton]
  rw [he]
  exact binary_union_mem M hM hP hU (singleton_mem M hM hP hx) hx

theorem omegaGraph_of_mem_iff (M d f : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hdM : d ∈ M) (hfM : f ∈ M) (hd : d.IsOrdinal)
    (hf : ∀ z, z ∈ f ↔ ∃ x ∈ d, z = ZFSet.pair x (omegaNext x)) :
    OmegaGraph M d (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hpair (x v : ZFSet.{u}) : ZFSet.pair x v ∈ f ↔ x ∈ d ∧ v = omegaNext x := by
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
    have hA := omegaStageImage d f x hd hx hf
    refine ⟨(Ordinal.omega0 ^ x.rank).toZFSet,
      hA ▸ stageImage_mem M hM hT h1 (hM d hdM x hx) hfM,?_,ZFSet.isOrdinal_toZFSet _,?_⟩
    · refine ⟨?_,?_,?_⟩
      · intro z hz; exact (omegaPower_members x.rank z).mpr (Or.inl hz)
      · intro z hz
        rcases (omegaPower_members x.rank z).mp hz with hz|⟨y,hy,hz⟩
        · exact Or.inl hz
        · rw [(hd.mem hx).toZFSet_rank_eq] at hy
          have hp := (hpair y _).mpr ⟨hd.subset_of_mem hx hy,rfl⟩
          exact Or.inr ⟨y,hy,_,second_mem_doubleUnion hp,hp,hz⟩
      · intro y hy w _ hw z hz
        rw [(hpair y w).mp hw |>.2] at hz
        exact (omegaPower_members x.rank z).mpr
          (Or.inr ⟨y,(hd.mem hx).toZFSet_rank_eq.symm ▸ hy,hz⟩)
    · rw [omegaNext,Ordinal.opow_add_one,Ordinal.rank_toZFSet]

theorem mulOmega_sigmaDefinable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    SigmaDefinable M (fun e => (e 1).IsOrdinal ∧ e 0 = ((e 1).rank*Ordinal.omega0).toZFSet) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have ho := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  let p := SigmaFormula.conj (.bounded (ordinalFormula 2))
    (productSigma.rename (fun i => if i = 0 then 0 else if i = 1 then 2 else 1))
  refine ⟨p,fun _ => ZFSet.omega,fun _ => ho,?_⟩
  intro e he
  rw [SigmaFormula.realize_conj]
  have hoSem : (SigmaFormula.bounded (ordinalFormula 2)).Realize M
      (mix e (fun _ => ZFSet.omega)) ↔ (e 1).IsOrdinal := by
    rw [SigmaFormula.Realize,Formula.absolute _ M hM _ (by
      intro i; unfold mix; split; exact he _; exact ho),eval_ordinalFormula]
    rfl
  rw [hoSem]
  apply and_congr_right; intro heo
  rw [SigmaFormula.realize_rename]
  exact productSigma_sourceT M hM hT _ (by
    intro i; change mix e (fun _ => ZFSet.omega)
      (if i = 0 then 0 else if i = 1 then 2 else 1) ∈ M
    split; exact he 0
    split; exact he 1
    exact ho) (e 1).rank Ordinal.omega0 heo.toZFSet_rank_eq.symm toZFSet_omega.symm

theorem omegaGraph_sigmaDefinable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (d r f : ℕ) : SigmaDefinable M (fun e => OmegaGraph M (e d) (e r) (e f)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact C.nat_mem 1
  have hs : SigmaDefinable M (fun e =>
      StageStep (1 : Ordinal.{u}).toZFSet (e (f+3)) (e (r+3)) (e 2) (e 0)) := by
    have hb := (stageStep_definable C 0 (f+4) (r+4) 3 1).toSigma hM
    have hc := ((equal_param h1 0).toSigma hM).and hb
    exact hc.existsSet.congr (fun e _ => by simp [h1])
  have hv : SigmaDefinable M (fun e => (e 0).IsOrdinal ∧
      e 1 = ((e 0).rank*Ordinal.omega0).toZFSet) :=
    (mulOmega_sigmaDefinable M hM hT).subst (fun i => if i = 0 then 1 else 0)
  have hi := SigmaDefinable.impBounded C (defPairMem C 1 0 (f+2)) (hs.and hv).existsSet
  exact ((ordinal_definable C d).toSigma hM).and
    (((functionGraph_definable C d r f).toSigma hM).and
      ((hi.allMem hM hT (r+1)).allMem hM hT d))

theorem uniform_omega_certificate (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ f ∈ M, p.Realize M (cons f (cons x e)) ↔
        ∃ r ∈ M, OmegaGraph M (insert x x) r f := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hd : Definable M (fun e => e 0 = insert (e 3) (e 3)) := by
    refine ⟨.successor 0 6,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.eval_successor,mix]
  have hg := (hd.toSigma hM).and (omegaGraph_sigmaDefinable M hM hT 0 1 2)
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation (fun x f => ∃ r ∈ M,
    ∃ d ∈ M, d = insert x x ∧ OmegaGraph M d r f) hg.existsSet.existsSet
  refine ⟨p,e,he,?_⟩
  intro x hx f hf
  rw [hp x hx f hf]
  constructor
  · rintro ⟨r,hr,d,_,rfl,h⟩; exact ⟨r,hr,h⟩
  · rintro ⟨r,hr,h⟩
    exact ⟨r,hr,insert x x,insert_self_mem M hM hT.pairing hT.union hx,rfl,h⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalOmegaPower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions
universe u

theorem internal_omegaGraph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x : ZFSet.{u}) (hxM : x ∈ M) (hxo : x.IsOrdinal) :
    ∃ f ∈ M, OmegaGraph M (insert x x) (iterUnion 2 f) f := by
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  obtain ⟨p,e,he,hp⟩ := uniform_omega_certificate M hM hT
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have cert (y f : ZFSet.{u}) (hy : y ∈ x) (hf : f ∈ M) := hp y (hM x hxM y hy) f hf
    obtain ⟨b,hb,hbdef⟩ := hT.replacement.finitePrefix p e he x hxM (by
      intro y hy
      obtain ⟨f,hf,hfg⟩ := ih y hy (hM x hxM y hy) (hxo.mem hy)
      refine ⟨f,hf,(cert y f hy hf).mpr
        ⟨_,iterUnion_mem M hM hT.union hf 2,hfg⟩,?_⟩
      intro g hg hcg
      obtain ⟨r,_,hgg⟩ := (cert y g hy hg).mp hcg
      exact hgg.unique hfg)
    have hbg (f : ZFSet.{u}) : f ∈ b ↔
        ∃ y ∈ x, ∃ r ∈ M, OmegaGraph M (insert y y) r f := by
      constructor
      · intro hf
        have hfM := hM b hb f hf
        obtain ⟨y,hy,hc⟩ := (hbdef f hfM).mp hf
        exact ⟨y,hy,(cert y f hy hfM).mp hc⟩
      · rintro ⟨y,hy,r,hr,hg⟩
        obtain ⟨f',hf',hg'⟩ := ih y hy (hM x hxM y hy) (hxo.mem hy)
        have heq := hg.unique hg'
        have hfM : f ∈ M := heq ▸ hf'
        exact (hbdef f hfM).mpr ⟨y,hy,(cert y f hy hfM).mpr ⟨r,hr,hg⟩⟩
    let g := ZFSet.sUnion b
    have hgM : g ∈ M := union_mem M hM hT.union hb
    have hg (z : ZFSet.{u}) : z ∈ g ↔ ∃ y ∈ x, z = ZFSet.pair y (omegaNext y) := by
      constructor
      · intro hz
        obtain ⟨f,hf,hzf⟩ := ZFSet.mem_sUnion.mp hz
        obtain ⟨y,hy,r,_,hfg⟩ := (hbg f).mp hf
        obtain ⟨w,hw,hz⟩ := (hfg.mem_iff z).mp hzf
        rcases ZFSet.mem_insert_iff.mp hw with rfl|hw
        · exact ⟨w,hy,hz⟩
        · exact ⟨w,hxo.subset_of_mem hy hw,hz⟩
      · rintro ⟨y,hy,hz⟩
        obtain ⟨f,hf,hfg⟩ := ih y hy (hM x hxM y hy) (hxo.mem hy)
        exact ZFSet.mem_sUnion.mpr ⟨f,(hbg f).mpr
          ⟨y,hy,_,iterUnion_mem M hM hT.union hf 2,hfg⟩,
          (hfg.mem_iff z).mpr ⟨y,ZFSet.mem_insert_iff.mpr (Or.inl rfl),hz⟩⟩
    have hvalue : stageImage (1 : Ordinal.{u}).toZFSet x g =
        (Ordinal.omega0 ^ x.rank).toZFSet := by
      apply ZFSet.ext; intro z
      rw [mem_stageImage,omegaPower_members,hxo.toZFSet_rank_eq]
      apply or_congr_right
      constructor
      · rintro ⟨y,hy,w,hfw,hz⟩
        obtain ⟨v,_,hp⟩ := (hg _).mp hfw
        obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
        exact ⟨y,hy,hz⟩
      · rintro ⟨y,hy,hz⟩
        exact ⟨y,hy,_,(hg _).mpr ⟨y,hy,rfl⟩,hz⟩
    have hpow : (Ordinal.omega0 ^ x.rank).toZFSet ∈ M :=
      hvalue ▸ stageImage_mem M hM hT h1 hxM hgM
    have hvM : omegaNext x ∈ M := by
      rw [omegaNext,Ordinal.opow_add_one]
      exact ordinal_mul_omega_internal M hM hT _ hpow
    let f := g ∪ ({ZFSet.pair x (omegaNext x)} : ZFSet.{u})
    have hfM : f ∈ M := binary_union_mem M hM hT.pairing hT.union hgM
      (singleton_mem M hM hT.pairing (orderedPair_mem M hM hT.pairing hxM hvM))
    have hsucc : (insert x x).IsOrdinal := by
      rw [← hxo.toZFSet_rank_eq,← Ordinal.toZFSet_add_one]
      exact ZFSet.isOrdinal_toZFSet _
    refine ⟨f,hfM,omegaGraph_of_mem_iff M _ f hM hT
      (insert_self_mem M hM hT.pairing hT.union hxM) hfM hsucc ?_⟩
    intro z
    change z ∈ g ∪ ({ZFSet.pair x (omegaNext x)} : ZFSet.{u}) ↔ _
    rw [ZFSet.mem_union,ZFSet.mem_singleton,hg]
    constructor
    · rintro (⟨y,hy,hz⟩|hz)
      · exact ⟨y,ZFSet.mem_insert_of_mem _ hy,hz⟩
      · exact ⟨x,ZFSet.mem_insert_iff.mpr (Or.inl rfl),hz⟩
    · rintro ⟨y,hy,hz⟩
      rcases ZFSet.mem_insert_iff.mp hy with rfl|hy
      · exact Or.inr hz
      · exact Or.inl ⟨y,hy,hz⟩

theorem ordinal_omega_opow_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (Ordinal.omega0 ^ a).toZFSet ∈ M := by
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph M hM hT a.toZFSet ha (ZFSet.isOrdinal_toZFSet a)
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hv := omegaStageImage _ f a.toZFSet hg.1 (ZFSet.mem_insert_iff.mpr (Or.inl rfl)) hg.mem_iff
  rw [Ordinal.rank_toZFSet] at hv
  exact hv ▸ stageImage_mem M hM hT h1 ha hf

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerDefinability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem omegaStageStep_exact {M d r f x A : ZFSet.{u}} (hg : OmegaGraph M d r f)
    (hx : x ∈ d) (hs : StageStep (1 : Ordinal.{u}).toZFSet f r x A) :
    A = (Ordinal.omega0 ^ x.rank).toZFSet := by
  apply ZFSet.ext; intro z
  rw [omegaPower_members,(hg.1.mem hx).toZFSet_rank_eq]
  constructor
  · intro hz
    rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨y,hy,(hg.correct y (hg.1.subset_of_mem hx hy) w hw hfw) ▸ hz⟩
  · rintro (hz|⟨y,hy,hz⟩)
    · exact hs.1 hz
    · obtain ⟨w,hw,hfw,_⟩ := hg.2.1.2 y (hg.1.subset_of_mem hx hy)
      rw [← hg.correct y (hg.1.subset_of_mem hx hy) w hw hfw] at hz
      exact hs.2.2 y hy w hw hfw hz

theorem omegaPower_sigmaDefinable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    SigmaDefinable M (fun e => (e 1).IsOrdinal ∧ e 0 = (Ordinal.omega0 ^ (e 1).rank).toZFSet) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]; exact C.nat_mem 1
  have hd : Definable M (fun e => e 0 = insert (e 4) (e 4)) := by
    refine ⟨.successor 0 8,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.eval_successor,mix]
  have hs : SigmaDefinable M (fun e =>
      StageStep (1 : Ordinal.{u}).toZFSet (e 2) (e 1) (e 4) (e 3)) := by
    have hb := (stageStep_definable C 0 3 2 5 4).toSigma hM
    exact (((equal_param h1 0).toSigma hM).and hb).existsSet.congr (fun e _ => by simp [h1])
  have hg := (hd.toSigma hM).and ((omegaGraph_sigmaDefinable M hM hT 0 1 2).and hs)
  apply hg.existsSet.existsSet.existsSet.congr
  intro e he
  change (∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
    d = insert (e 1) (e 1) ∧ OmegaGraph M d r f ∧
      StageStep (1 : Ordinal.{u}).toZFSet f r (e 1) (e 0)) ↔ _
  constructor
  · rintro ⟨f,_,r,_,d,_,rfl,hg,hs⟩
    have hx : e 1 ∈ insert (e 1) (e 1) := ZFSet.mem_insert_iff.mpr (Or.inl rfl)
    exact ⟨hg.1.mem hx,omegaStageStep_exact hg hx hs⟩
  · rintro ⟨ho,hy⟩
    obtain ⟨f,hf,hg⟩ := internal_omegaGraph M hM hT (e 1) (he 1) ho
    have hx : e 1 ∈ insert (e 1) (e 1) := ZFSet.mem_insert_iff.mpr (Or.inl rfl)
    obtain ⟨v,hv,hfv,_⟩ := hg.2.1.2 (e 1) hx
    obtain ⟨A,_,hA,_⟩ := hg.2.2 (e 1) hx v hv hfv
    have hAy : A = e 0 := (omegaStageStep_exact hg hx hA).trans hy.symm
    exact ⟨f,hf,_,iterUnion_mem M hM hT.union hf 2,_,
      insert_self_mem M hM hT.pairing hT.union (he 1),rfl,hg,hAy ▸ hA⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Syntax_SigmaSequenceTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel BoundedDefinability SetModelFunctions SetModelIteration RelativeConstructible
universe u

theorem sequenceTrace_sigma (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : SigmaDefinable M (fun e => S (e 1) (e 0))) :
    SigmaDefinable M (fun e => SequenceTrace M S (e 0) (e 1) (e 2) (e 3) (e 4) (e 5) (e 6)) := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hcore : Definable M (fun e => e 3 = insert (e 0) (e 0) ∧ FunctionGraph (e 3) (e 4) (e 5) ∧
      e 6 = ∅ ∧ ZFSet.pair (e 6) (e 1) ∈ e 5 ∧ ZFSet.pair (e 0) (e 2) ∈ e 5) := by
    refine ⟨.conj (.successor 6 0) (.conj (.functionGraph 10 6 8)
      (.conj (.empty 12) (.conj (.pairMem 12 2 10) (.pairMem 0 4 10)))),
      fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e
    simp [Formula.Eval,Formula.eval_successor,Formula.eval_functionGraph,
      Formula.eval_empty,Formula.eval_pairMem,mix,FunctionGraph]
  have hAnte : Definable M (fun e => ZFSet.pair (e 3) (e 1) ∈ e 9 ∧
      ZFSet.pair (e 2) (e 0) ∈ e 9) := by
    refine ⟨.conj (.pairMem 6 2 18) (.pairMem 4 0 18),
      fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.Eval,Formula.eval_pairMem,mix]
  have himp := SigmaDefinable.impBounded C hAnte hS
  have hall := (himp.allMem hM hT 7).allMem hM hT 6
  have hsucc : Definable M (fun e => e 0 = insert (e 1) (e 1)) := by
    refine ⟨.successor 0 2,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.eval_successor,mix]
  have hstep := (((hsucc.toSigma hM).and hall).existsSet).allMem hM hT 0
  exact ((hcore.toSigma hM).and hstep).congr (fun _ _ => by
    simp only [SequenceTrace,cons_zero,cons_succ,and_assoc])

theorem SequenceTrace.correct (M : ZFSet.{u}) (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (s : ℕ → ZFSet.{u}) (hS : ∀ i w, S (s i) w → w = s (i+1))
    (n : ℕ) {y d r f z : ZFSet.{u}}
    (h : SequenceTrace M S (natSet n) (s 0) y d r f z) : y = s n := by
  obtain ⟨rfl,hfun,rfl,hzero,hy,hstep⟩ := h
  have hd : insert (natSet.{u} n) (natSet n) = natSet (n+1) := rfl
  rw [hd] at hfun
  have computes (i : ℕ) (hi : i ≤ n) : ZFSet.pair (natSet i) (s i) ∈ f := by
    induction i with
    | zero => exact hzero
    | succ i ih =>
      have hip := ih (by omega)
      have hiv : s i ∈ r := by
        obtain ⟨x,_,v,hv,heq⟩ := hfun.1 _ hip
        obtain ⟨_,rfl⟩ := ZFSet.pair_inj.mp heq
        exact hv
      have hjd : natSet.{u} (i+1) ∈ natSet (n+1) := (natSet_mem_natSet _ _).mpr (by omega)
      obtain ⟨w,hw,hjw,_⟩ := hfun.2 _ hjd
      obtain ⟨j,_,hj,hs⟩ := hstep (natSet i) ((natSet_mem_natSet _ _).mpr (by omega))
      have hj' : j = natSet (i+1) := hj
      have hs' := hs (s i) hiv w hw ⟨hip,hj' ▸ hjw⟩
      exact (hS i w hs') ▸ hjw
  exact hfun.functional ((natSet_mem_natSet _ _).mpr (Nat.lt_succ_self n)) hy (computes n le_rfl)

theorem sequenceTrace_exists (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u} → ZFSet.{u} → Prop) (s : ℕ → ZFSet.{u})
    (hs : ∀ i, s i ∈ M) (hstep : ∀ i, S (s i) (s (i+1))) (n : ℕ) :
    ∃ z ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M, SequenceTrace M S (natSet n) (s 0) (s n) d r f z := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  let f := finiteGraph (n+1) s
  have hf : f ∈ M := finiteGraph_mem M hM hT.pairing hT.union C.omega_mem _ s (fun i _ => hs i)
  let r := iterUnion 2 f
  have hr := iterUnion_mem M hM hT.union hf 2
  have hval (i : ℕ) (hi : i < n+1) : s i ∈ r :=
    second_mem_doubleUnion ((pair_mem_finiteGraph _ _ _ _).mpr ⟨hi,rfl⟩)
  have hfun : FunctionGraph (natSet (n+1)) r f := by
    constructor
    · intro z hz
      obtain ⟨i,hi,rfl⟩ := (mem_finiteGraph _ _ _).mp hz
      exact ⟨natSet i,(natSet_mem_natSet _ _).mpr hi,s i,hval i hi,rfl⟩
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) x).mp hx
      refine ⟨s i,hval i hi,(pair_mem_finiteGraph _ _ _ _).mpr ⟨hi,rfl⟩,?_⟩
      intro y _ hy
      exact ((pair_mem_finiteGraph _ _ _ _).mp hy).2
  refine ⟨∅,C.nat_mem 0,f,hf,r,hr,natSet (n+1),C.nat_mem _,rfl,hfun,rfl,
    (pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,
    (pair_mem_finiteGraph _ _ _ _).mpr ⟨by omega,rfl⟩,?_⟩
  intro i hi
  obtain ⟨i,hi,rfl⟩ := (mem_natSet n i).mp hi
  refine ⟨natSet (i+1),C.nat_mem _,rfl,?_⟩
  intro v _ w _ hp
  rw [((pair_mem_finiteGraph _ _ _ _).mp hp.1).2,
    ((pair_mem_finiteGraph _ _ _ _).mp hp.2).2]
  exact hstep i

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalSigmaSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel BoundedDefinability SetModelFunctions SetModelIteration RelativeConstructible
universe u

theorem sequenceValue_sigma (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : SigmaDefinable M (fun e => S (e 1) (e 0)))
    (x : ZFSet.{u}) (hx : x ∈ M) :
    SigmaDefinable M (fun e => ∃ z ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
      SequenceTrace M S (e 1) x (e 0) d r f z) := by
  have ht := (sequenceTrace_sigma M hM hT S hS).subst
    (fun i => match i with | 0 => 5 | 1 => 6 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 2 | _ => 3)
  have hv := ht.existsSet.existsSet.existsSet.existsSet
  have hs := hv.subst (fun i => if i=0 then 1 else if i=1 then 2 else 0)
  have h := (((equal_param hx 0).toSigma hM).and hs).existsSet
  apply h.congr
  intro e _
  change (∃ x' ∈ M, x'=x ∧ ∃ z ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
    SequenceTrace M S (e 1) x' (e 0) d r f z) ↔ _
  exact ⟨fun ⟨_,_,he,hv⟩ => he ▸ hv,fun hv => ⟨x,hx,rfl,hv⟩⟩

theorem sigma_sequence_range_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (S : ZFSet.{u} → ZFSet.{u} → Prop)
    (hS : SigmaDefinable M (fun e => S (e 1) (e 0)))
    (s : ℕ → ZFSet.{u}) (hs : ∀ n, s n ∈ M)
    (hstep : ∀ n, S (s n) (s (n+1)))
    (hunique : ∀ n y, S (s n) y → y = s (n+1)) :
    ∃ B ∈ M, ∀ y, y ∈ B ↔ ∃ n, y = s n := by
  obtain ⟨p,e,he,hp⟩ := sigma_binary_relation
    (fun n y => ∃ z ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
      SequenceTrace M S n (s 0) y d r f z)
    (sequenceValue_sigma M hM hT S hS (s 0) (hs 0))
  have hω := sourceT_omega_mem M hM hT
  have hv (n : ℕ) (y : ZFSet.{u}) (hy : y ∈ M) :
      p.Realize M (cons y (cons (natSet n) e)) ↔ y = s n := by
    rw [hp _ (hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)) y hy]
    constructor
    · rintro ⟨z,_,f,_,r,_,d,_,h⟩
      exact SequenceTrace.correct M S s hunique n h
    · rintro rfl
      exact sequenceTrace_exists M hM hT S s hs hstep n
  obtain ⟨B,hB,hdef⟩ := hT.replacement.finitePrefix p e he ZFSet.omega hω (by
    intro n hn
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨s n,hs n,(hv n (s n) (hs n)).mpr rfl,
      fun y hy h => (hv n y hy).mp h⟩)
  refine ⟨B,hB,?_⟩
  intro y
  constructor
  · intro hy
    have hyM := hM B hB y hy
    obtain ⟨n,hn,h⟩ := (hdef y hyM).mp hy
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    exact ⟨n,(hv n y hyM).mp h⟩
  · rintro ⟨n,rfl⟩
    exact (hdef (s n) (hs n)).mpr ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,
      (hv n (s n) (hs n)).mpr rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_InternalOmegaFixedPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory BoundedDefinability RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem omega_fixed_point_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (θ : Ordinal.{u}) (hθ : θ.toZFSet ∈ M) :
    (Ordinal.nfp (fun a : Ordinal.{u} => Ordinal.omega0 ^ a) θ).toZFSet ∈ M := by
  let F : Ordinal.{u} → Ordinal.{u} := fun a => Ordinal.omega0 ^ a
  let s : ℕ → ZFSet.{u} := fun n => (F^[n] θ).toZFSet
  let S : ZFSet.{u} → ZFSet.{u} → Prop := fun x y =>
    x.IsOrdinal ∧ y = (Ordinal.omega0 ^ x.rank).toZFSet
  have hs (n : ℕ) : s n ∈ M := by
    induction n with
    | zero => exact hθ
    | succ n ih =>
      simpa only [s,Function.iterate_succ_apply',F] using
        ordinal_omega_opow_internal M hM hT (F^[n] θ) ih
  have hstep (n : ℕ) : S (s n) (s (n+1)) := by
    refine ⟨ZFSet.isOrdinal_toZFSet _,?_⟩
    simp only [s,Function.iterate_succ_apply',F,Ordinal.rank_toZFSet]
  have hu (n : ℕ) (y : ZFSet.{u}) (h : S (s n) y) : y = s (n+1) := by
    simpa only [s,Function.iterate_succ_apply',F,Ordinal.rank_toZFSet] using h.2
  obtain ⟨B,hB,hdef⟩ := sigma_sequence_range_internal M hM hT S
    (omegaPower_sigmaDefinable M hM hT) s hs hstep hu
  have heq : (Ordinal.nfp F θ).toZFSet = ZFSet.sUnion B := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sUnion]
    constructor
    · intro hz
      obtain ⟨a,ha,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
      obtain ⟨n,hn⟩ := Ordinal.lt_nfp_iff.mp ha
      exact ⟨s n,(hdef _).mpr ⟨n,rfl⟩,Ordinal.toZFSet_mem_toZFSet_iff.mpr hn⟩
    · rintro ⟨t,ht,hz⟩
      obtain ⟨n,rfl⟩ := (hdef t).mp ht
      exact Ordinal.toZFSet_monotone (Ordinal.iterate_le_nfp F θ n) hz
  rw [heq]
  exact union_mem M hM hT.union hB

theorem cofinal_internal_omega_fixed_points (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (θ : Ordinal.{u}) (hθ : θ.toZFSet ∈ M) :
    ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ θ < β ∧ Order.IsSuccLimit β ∧ Ordinal.omega0 ^ β = β := by
  let F : Ordinal.{u} → Ordinal.{u} := fun a => Ordinal.omega0 ^ a
  let β := Ordinal.nfp F (θ+1)
  have hb : θ < β := (lt_add_one θ).trans_le (Ordinal.le_nfp F (θ+1))
  have hfix : Ordinal.omega0 ^ β = β := Ordinal.nfp_fp (Ordinal.isNormal_opow Ordinal.one_lt_omega0) (θ+1)
  refine ⟨β,omega_fixed_point_internal M hM hT (θ+1) (internal_ordinal_succ M hM hT θ hθ),hb,?_,hfix⟩
  rw [← hfix]
  exact Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt (lt_of_le_of_lt zero_le hb))

end TuringRigidity.OrdinalArithmetic

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
-- module Solutions.OAIQ064_DR.DegreeRigidity_Representation_GroundSeedOrdinalHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem natSet_isOrdinal (n : ℕ) : (natSet.{u} n).IsOrdinal := by
  induction n with
  | zero => exact ZFSet.isOrdinal_empty
  | succ n ih => exact ZFSet.isOrdinal_succ ih

theorem omega_isOrdinal : ZFSet.omega.{u}.IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  refine ⟨omega_transitive,?_⟩
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact natSet_isOrdinal n

theorem omega_mem_groundReals (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ZFSet.omega ∈ groundReals M :=
  (mem_groundReals M _).mpr ⟨sourceT_omega_mem M hM hT,fun _ h => h⟩

theorem groundReals_not_isOrdinal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ¬ (groundReals M).IsOrdinal := by
  let s : ZFSet.{u} := {natSet 1}
  have h1ω : natSet.{u} 1 ∈ ZFSet.omega := (mem_omega _).mpr ⟨1,rfl⟩
  have hsM : s ∈ M := singleton_mem M hM hT.pairing
    (hM _ (sourceT_omega_mem M hM hT) _ h1ω)
  have hsR : s ∈ groundReals M := (mem_groundReals M s).mpr ⟨hsM,by
    intro x hx
    obtain rfl := ZFSet.mem_singleton.mp hx
    exact h1ω⟩
  intro h
  have hs := h.mem hsR
  have hz : natSet.{u} 0 ∈ s := hs.isTransitive.mem_trans ((natSet_mem_natSet 0 1).mpr (by decide))
    (ZFSet.mem_singleton.mpr rfl)
  have he : (0 : ℕ) = 1 := natSet_injective (ZFSet.mem_singleton.mp hz)
  exact Nat.zero_ne_one he

theorem ordinalCut_ground_seed (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ordinalCut (seed (groundReals M)) = insert ZFSet.omega ZFSet.omega := by
  apply ZFSet.ext; intro x
  rw [mem_ordinalCut,ground_seed_shape M hM]
  constructor
  · rintro ⟨hx,ho⟩
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact False.elim (groundReals_not_isOrdinal M hM hT ho)
    · exact ZFSet.mem_insert_iff.mpr
        ((ho.subset_iff_eq_or_mem omega_isOrdinal).mp ((mem_groundReals M x).mp hx).2)
  · intro hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact ⟨ZFSet.mem_insert_of_mem _ (omega_mem_groundReals M hM hT),omega_isOrdinal⟩
    · have hxR : x ∈ groundReals M := (mem_groundReals M x).mpr
        ⟨hM _ (sourceT_omega_mem M hM hT) _ hx,fun y hy => omega_transitive x hx y hy⟩
      exact ⟨ZFSet.mem_insert_of_mem _ hxR,omega_isOrdinal.mem hx⟩

theorem ordinalHeight_ground_seed (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ordinalHeight (seed (groundReals M)) = (insert ZFSet.omega ZFSet.omega : ZFSet.{u}).rank := by
  unfold ordinalHeight
  rw [ordinalCut_ground_seed M hM hT]

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_Constructibility_UniformHeightDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u
attribute [local irreducible] Construction.ownRealsMembership SentenceForm.bound

theorem ground_seed_offset (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ordinalHeight (seed (groundReals M)) = realSeedOffset := ordinalHeight_ground_seed M hM hT

theorem heightDomainIndex_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (heightDomainIndex a).toZFSet ∈ M :=
  internal_difference_successor M hM hT a realSeedOffset ha

end TuringRigidity.RelativeConstructible

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OmegaPowerCertificates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem ProductCertificates.mono {M N : ZFSet.{u}} {a b : Ordinal.{u}}
    (h : ProductCertificates M a b) (hMN : M ⊆ N) : ProductCertificates N a b :=
  ⟨hMN h.1,hMN h.2.1,let ⟨f,hf,hc⟩ := h.2.2; ⟨f,hMN hf,hc⟩⟩

theorem OmegaPowerCertificates.mono {M N x : ZFSet.{u}}
    (h : OmegaPowerCertificates M x) (hMN : M ⊆ N) : OmegaPowerCertificates N x := by
  obtain ⟨hd,f,hf,r,hr,hg,hp⟩ := h
  refine ⟨hMN hd,f,hMN hf,r,hMN hr,⟨hg.1,hg.2.1,?_⟩,fun t ht => (hp t ht).mono hMN⟩
  intro t ht v hv hfv
  obtain ⟨A,hA,hs,ho,he⟩ := hg.2.2 t ht v hv hfv
  exact ⟨A,hMN hA,hs,ho,he⟩

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalCodeDomains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory ElementaryModel RelativeConstructible
universe u

theorem padded_height_index_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (ha : (paddedCode v β).toZFSet ∈ M) :
    (heightDomainIndex (paddedCode v β)).toZFSet ∈ M :=
  heightDomainIndex_internal M hM hT _ ha

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

theorem taggedClause_eval (a b t v x y : ℕ) (cmp : Bool) (e : ℕ → ZFSet.{u}) :
    (taggedClause a b t v x y cmp).Eval e ↔
      ∃ s ∈ e a, ∃ q ∈ e b, e x = ZFSet.pair (e t) s ∧
        e y = ZFSet.pair (e v) q ∧ (if cmp then s ∈ q else True) := by
  cases cmp <;> simp [taggedClause, Formula.Eval]

theorem sumLessFormula_eval (a b z o x y : ℕ) (e : ℕ → ZFSet.{u})
    (hz : e z = ∅) (ho : e o = {∅}) :
    (sumLessFormula a b z o x y).Eval e ↔ SumLess (e a) (e b) (e x) (e y) := by
  simp [sumLessFormula, taggedClause_eval, hz, ho, SumLess, leftNode, rightNode]

theorem sumRelationFormula_eval (a b p : ZFSet.{u}) :
    sumRelationFormula.Eval
      (cons p (cons (sumDomain a b) (cons a (cons b (cons ∅ (fun _ => {∅})))))) ↔
      ∃ x ∈ sumDomain a b, ∃ y ∈ sumDomain a b,
        p = ZFSet.pair x y ∧ SumLess a b x y := by
  simp only [sumRelationFormula, Formula.Eval, Formula.eval_orderedPair,
    cons_zero, cons_succ]
  apply exists_congr; intro x
  apply and_congr_right; intro _
  apply exists_congr; intro y
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact sumLessFormula_eval _ _ _ _ _ _ _ rfl rfl

theorem sumDomain_mem (M a b : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (h0 : (∅ : ZFSet.{u}) ∈ M) (ha : a ∈ M) (hb : b ∈ M) :
    sumDomain a b ∈ M := by
  have h1 := singleton_mem M hM hP h0
  exact binary_union_mem M hM hP hU
    (product_mem M hM hP hU hPow hS h1 ha)
    (product_mem M hM hP hU hPow hS (singleton_mem M hM hP h1) hb)

theorem sumRelation_mem (M a b : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (h0 : (∅ : ZFSet.{u}) ∈ M) (ha : a ∈ M) (hb : b ∈ M) :
    sumRelation a b ∈ M := by
  have hd := sumDomain_mem M a b hM hP hU hPow hS h0 ha hb
  have h1 := singleton_mem M hM hP h0
  let e := cons (sumDomain a b) (cons a (cons b (cons ∅ (fun _ => {∅}))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|i; exact hd
    rcases i with _|i; exact ha
    rcases i with _|i; exact hb
    rcases i with _|i; exact h0
    exact h1
  have hs := sep_mem M hM hS sumRelationFormula e he
    (product_mem M hM hP hU hPow hS hd hd)
  have eq : ZFSet.sep (fun p => sumRelationFormula.Eval (cons p e))
      (ZFSet.prod (sumDomain a b) (sumDomain a b)) = sumRelation a b := by
    apply ZFSet.ext; intro p
    simp only [sumRelation, ZFSet.mem_sep, e, sumRelationFormula_eval]
  exact eq ▸ hs

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumPresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse
universe u

attribute [local simp] leftNode_inj rightNode_inj leftNode_ne_rightNode rightNode_ne_leftNode

theorem sumValue_mem (a b : Ordinal.{u}) (x : ZFSet.{u})
    (hx : x ∈ sumDomain a.toZFSet b.toZFSet) : sumValue a x ∈ (a+b).toZFSet := by
  rcases (mem_sumDomain _ _ _).mp hx with ⟨s,hs,rfl⟩|⟨s,hs,rfl⟩
  · rw [sumValue_left]
    exact Ordinal.toZFSet_monotone le_self_add hs
  · obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    rw [sumValue_right,Ordinal.rank_toZFSet,Ordinal.toZFSet_mem_toZFSet_iff]
    exact (add_lt_add_iff_left a).mpr hc

theorem sumValue_surjective (a b : Ordinal.{u}) (z : ZFSet.{u})
    (hz : z ∈ (a+b).toZFSet) :
    ∃ x ∈ sumDomain a.toZFSet b.toZFSet, sumValue a x = z := by
  obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hz
  by_cases h : c < a
  · exact ⟨leftNode c.toZFSet,(mem_sumDomain _ _ _).mpr
      (Or.inl ⟨c.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr h,rfl⟩),sumValue_left _ _⟩
  · have hle := le_of_not_gt h
    have hb : c-a < b := (Ordinal.sub_lt_of_le hle).mpr hc
    refine ⟨rightNode (c-a).toZFSet,(mem_sumDomain _ _ _).mpr
      (Or.inr ⟨(c-a).toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hb,rfl⟩),?_⟩
    rw [sumValue_right,Ordinal.rank_toZFSet,Ordinal.add_sub_cancel_of_le hle]

theorem ordinal_add_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    (a+b).toZFSet ∈ M ∧ ∃ f ∈ M,
      Presents (sumDomain a.toZFSet b.toZFSet) f (sumValue a) ∧
      OrderTypeCertificate (sumDomain a.toZFSet b.toZFSet)
        (sumRelation a.toZFSet b.toZFSet) (a+b).toZFSet f := by
  have h0 := hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ZFSet.omega_zero
  exact ordinal_internal_of_presentation M _ _ _ hM hT
    (sumDomain_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded h0 ha hb)
    (sumRelation_mem M _ _ hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded h0 ha hb)
    (sumRelation_on _ _) (sumValue a) (sumValue_mem a b)
    (sumValue_surjective a b) (sumValue_relation a b)

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_OrdinalCodes_OrdinalSumClosure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem ordinal_mul_two_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (a*2).toZFSet ∈ M := by
  rw [Ordinal.mul_two]
  exact (ordinal_add_internal M hM hT a a ha ha).1

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_InternalOrdinalCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory OrdinalArithmetic RelativeConstructible
universe u

theorem pairCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x y : Ordinal.{u}) (hx : x.toZFSet ∈ M) (hy : y.toZFSet ∈ M) :
    (pairCode x y).toZFSet ∈ M := by
  unfold pairCode
  split
  · exact (ordinal_add_internal M hM hT _ _
      (ordinal_omega_opow_internal M hM hT _ (internal_ordinal_succ M hM hT x hx))
      (ordinal_omega_opow_internal M hM hT y hy)).1
  · exact (ordinal_add_internal M hM hT _ _
      (ordinal_mul_two_internal M hM hT _
        (ordinal_omega_opow_internal M hM hT _ (internal_ordinal_succ M hM hT y hy)))
      (ordinal_omega_opow_internal M hM hT x hx)).1

theorem vectorCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (hv : ∀ i, (v i).toZFSet ∈ M) :
    (vectorCode v).toZFSet ∈ M := by
  induction n with
  | zero =>
    simpa only [vectorCode,zero_add] using internal_ordinal_succ M hM hT 0 (internal_ordinal_zero M hM hT)
  | succ n ih =>
    exact pairCode_internal M hM hT _ _ (hv 0) (ih _ (fun i => hv i.succ))

theorem paddedCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (hβ : β.toZFSet ∈ M) :
    (paddedCode v β).toZFSet ∈ M :=
  pairCode_internal M hM hT _ _ hβ (vectorCode_internal M hM hT v hv)

theorem padded_height_index_from_inputs (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (hβ : β.toZFSet ∈ M) :
    (heightDomainIndex (paddedCode v β)).toZFSet ∈ M :=
  padded_height_index_internal M hM hT v β (paddedCode_internal M hM hT v β hv hβ)

end TuringRigidity.OrdinalCoding

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_RecursiveOmegaBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalCoding
universe u

theorem lower_omega_closure_of_fixed_point (M : ZFSet.{u}) (θ β : Ordinal.{u})
    (hbound : ∀ a : Ordinal.{u}, OmegaPowerCertificates
      (level (groundReals M) (θ+Ordinal.omega0 ^ (a+1))) a.toZFSet)
    (hβ : Order.IsSuccLimit β) (hθ : θ < β) (hfix : Ordinal.omega0 ^ β = β) :
    ∀ c < β, (Ordinal.omega0 ^ c).toZFSet ∈ level (groundReals M) β ∧
      OmegaPowerCertificates (level (groundReals M) β) c.toZFSet := by
  intro c hc
  have hv : Ordinal.omega0 ^ c < β := hfix ▸
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hc
  have hs : Ordinal.omega0 ^ (c+1) < β := hfix ▸
    (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (hβ.succ_lt hc)
  have hsum : θ+Ordinal.omega0 ^ (c+1) < β := by
    rw [← hfix] at hθ hs ⊢
    exact Ordinal.isPrincipal_add_omega0_opow β hθ hs
  refine ⟨?_,(hbound c).mono (level_mono _ hsum.le)⟩
  rw [ordinal_mem_level_iff]
  exact hv.trans_le le_add_self

end TuringRigidity.OrdinalArithmetic

end OAI
end

section
-- module Solutions.OAIQ064_DR.DegreeRigidity_SetModels_CofinalPaddedDecoder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible OrdinalArithmetic
universe u

theorem cofinal_padded_code_certificates_oai (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) {n : ℕ} (v : Fin n → Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (θ : Ordinal.{u}) (hθ : θ.toZFSet ∈ M) :
    ∃ β : Ordinal.{u}, β.toZFSet ∈ M ∧ θ < β ∧ realSeedOffset < β ∧
      (heightDomainIndex (paddedCode v β)).toZFSet ∈ M ∧
      PaddedCodeCertificates (level (groundReals M) (heightDomainIndex (paddedCode v β))) v β := by
  obtain ⟨τ,hτ,homega⟩ := internal_explicit_omega_threshold M hM hT
  obtain ⟨η,hη,hvec⟩ := vectorCode_certificates_at_levels M hM hT v hv
  have hk := vectorCode_internal M hM hT v hv
  have hoffM : realSeedOffset.toZFSet ∈ M := by
    rw [← ground_seed_offset M hM hT]
    exact ordinalHeight_mem_model M _ hM hT.separation.finitePrefix.bounded
      (seed_mem M _ hM hT (groundReals_mem M hM hT)) (seed_transitive _)
  let γ := max θ (max τ (max η (max realSeedOffset (vectorCode v))))
  have hγ : γ.toZFSet ∈ M := internal_ordinal_max M hθ
    (internal_ordinal_max M hτ (internal_ordinal_max M hη (internal_ordinal_max M hoffM hk)))
  obtain ⟨β,hβM,hγβ,hβ,hfix⟩ := cofinal_internal_omega_fixed_points M hM hT γ hγ
  have hθβ : θ < β := (le_max_left _ _).trans_lt hγβ
  have htail : max τ (max η (max realSeedOffset (vectorCode v))) < β :=
    (le_max_right _ _).trans_lt hγβ
  have hτβ : τ < β := (le_max_left _ _).trans_lt htail
  have htail' : max η (max realSeedOffset (vectorCode v)) < β := (le_max_right _ _).trans_lt htail
  have hηβ : η < β := (le_max_left _ _).trans_lt htail'
  have hlast : max realSeedOffset (vectorCode v) < β := (le_max_right _ _).trans_lt htail'
  have hoffβ : realSeedOffset < β := (le_max_left _ _).trans_lt hlast
  have hkβ : vectorCode v < β := (le_max_right _ _).trans_lt hlast
  have hoff : realSeedOffset+β=β := by
    have h := Ordinal.add_omega0_opow (a := realSeedOffset) (b := β) (by rw [hfix]; exact hoffβ)
    simpa only [hfix] using h
  have hpow := lower_omega_closure_of_fixed_point M τ β homega hβ hτβ hfix
  have hc := padded_certificates_of_lower_closure M hM hT v β hβ hoff hkβ
    (hvec β hηβ.le).2 hpow
  exact ⟨β,hβM,hθβ,hoffβ,padded_height_index_from_inputs M hM hT v β hv hβM,hc⟩

end TuringRigidity.OrdinalCoding

end OAI
end

theorem solution.{u} : type_of% @OAI.TuringRigidity.OrdinalCoding.cofinal_padded_code_certificates_oai.{u} := @OAI.TuringRigidity.OrdinalCoding.cofinal_padded_code_certificates_oai.{u}
