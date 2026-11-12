-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_ordinal_choice
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:32:22.861109+00:00
-- url     : https://prove2.me/submissions/37e9706f-ad0c-4c23-af67-2a6be3f57bf1

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P011
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalFulfillment_structural_bounds_with
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_compatible_insertion_unions
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_support_prepared_strengthening

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GenericPartialFunctions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



section

universe u
variable {P : Type u} [Preorder P]

theorem exists_filter_meeting_sequence (p : P) (D : Nat → Set P)
    (dense : ∀ n, Dense (D n)) :
    ∃ H : ConditionFilter P, H.mem p ∧ ∀ n, H.Meets (D n) := by
  classical
  let next (n : Nat) (q : P) : P := Classical.choose (dense n q)
  have next_le (n : Nat) (q : P) : next n q ≤ q := (Classical.choose_spec (dense n q)).1
  have next_mem (n : Nat) (q : P) : next n q ∈ D n := (Classical.choose_spec (dense n q)).2
  let chain : Nat → P := Nat.rec p next
  have step (n : Nat) : chain (n + 1) ≤ chain n := next_le n (chain n)
  have down : Antitone chain := antitone_nat_of_succ_le step
  let H : ConditionFilter P := {
    mem := fun q => ∃ n, chain n ≤ q
    nonempty := ⟨p, 0, le_rfl⟩
    upward := by
      rintro q r ⟨n, nq⟩ qr
      exact ⟨n, nq.trans qr⟩
    directed := by
      rintro q r ⟨n, nq⟩ ⟨m, mr⟩
      exact ⟨chain (max n m), ⟨max n m, le_rfl⟩,
        (down (le_max_left n m)).trans nq, (down (le_max_right n m)).trans mr⟩ }
  exact ⟨H, ⟨0, le_rfl⟩, fun n => ⟨chain (n + 1), ⟨n + 1, le_rfl⟩, next_mem n (chain n)⟩⟩

theorem exists_generic_for_countable_family (p : P) (family : Set (Set P))
    (small : family.Countable) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor family := by
  classical
  let listed := Set.enumerateCountable small (Set.univ : Set P)
  let D (n : Nat) : Set P := if Dense (listed n) then listed n else Set.univ
  have dense (n : Nat) : Dense (D n) := by
    dsimp [D]
    split_ifs with h
    · exact h
    · exact fun q => ⟨q, le_rfl, Set.mem_univ q⟩
  obtain ⟨H, hp, meets⟩ := exists_filter_meeting_sequence p D dense
  refine ⟨H, hp, ?_⟩
  intro E hE hDense
  obtain ⟨n, hn⟩ := Set.subset_range_enumerate small (Set.univ : Set P) hE
  have eq : D n = E := by
    dsimp [D, listed]
    simp only [hn, ite_eq_left hDense]
  exact eq ▸ meets n






end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_EvaluatedDomains
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace Name

open SetRealization
universe u v
variable {P : Type u} {s : Presentation P}

theorem mem_eval_assemble (H : Set P) {α : Type v} [Small.{u} α]
    (names : α → Name s) (conditions : α → P) (x : ZFSet.{u}) :
    x ∈ eval H (assemble names conditions) ↔
      ∃ i, conditions i ∈ H ∧ eval H (names i) = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨i, rfl, rfl⟩ := (entry_assemble names conditions σ p).1 entry
    exact ⟨i, hp, eq⟩
  · rintro ⟨i, hp, eq⟩
    exact ⟨names i, conditions i,
      (entry_assemble names conditions _ _).2 ⟨i, rfl, rfl⟩, hp, eq⟩

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forcesEq_refl (σ : Name s) (p : P) : ForcesEq p σ σ := by
  induction σ using inductionOn generalizing p with
  | step σ ih =>
    rw [ForcesEq]
    constructor
    · intro ρ r hr q _ qr
      exact ⟨q, le_rfl, ρ, r, hr, qr, ih ρ r hr q⟩
    · intro ρ r hr q _ qr
      exact ⟨q, le_rfl, ρ, r, hr, qr, ih ρ r hr q⟩

theorem forcesMem_entry {σ τ : Name s} {r : P} (entry : Entry σ τ r) :
    ForcesMem r σ τ := forcesMem_of_witness ⟨σ, r, entry, le_rfl, forcesEq_refl σ r⟩

end Name



namespace Name

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem eval_check (H : Set P) (one : P) (hone : one ∈ H) (x : ZFSet.{u}) :
    eval H (check s one x) = x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [check]
    apply ZFSet.ext
    intro z
    rw [mem_eval_assemble]
    constructor
    · rintro ⟨y, _, eq⟩
      rw [ih y.val y.property] at eq
      exact eq ▸ y.property
    · intro hz
      exact ⟨⟨z, hz⟩, hone, ih z hz⟩

theorem eval_singleton (H : Set P) (one : P) (hone : one ∈ H) (σ : Name s) :
    eval H (singleton one σ) = {eval H σ} := by
  apply ZFSet.ext
  intro x
  rw [singleton, mem_eval_assemble, ZFSet.mem_singleton]
  constructor
  · rintro ⟨_, _, eq⟩
    exact eq.symm
  · intro eq
    exact ⟨(), hone, eq.symm⟩

theorem eval_unorderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (unorderedPair one σ τ) = {eval H σ, eval H τ} := by
  apply ZFSet.ext
  intro x
  rw [unorderedPair, mem_eval_assemble, ZFSet.mem_pair]
  constructor
  · rintro ⟨b, _, eq⟩
    cases b with
    | false => exact Or.inr eq.symm
    | true => exact Or.inl eq.symm
  · rintro (eq | eq)
    · exact ⟨true, hone, eq.symm⟩
    · exact ⟨false, hone, eq.symm⟩

theorem eval_orderedPair (H : Set P) (one : P) (hone : one ∈ H) (σ τ : Name s) :
    eval H (orderedPair one σ τ) = ZFSet.pair (eval H σ) (eval H τ) := by
  rw [orderedPair, eval_unorderedPair H one hone,
    eval_singleton H one hone, eval_unorderedPair H one hone]
  rfl

end Name



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CountableCoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u

theorem natPair_upper (a b : Nat) : natPair a b < (a + b + 1) * (a + b + 1) := by
  unfold natPair
  rw [Nat.succ_mul_succ]
  omega

theorem natPair_sum_lt {a b c d : Nat} (less : a + b < c + d) : natPair a b < natPair c d := by
  have step : a + b + 1 ≤ c + d := by omega
  have sq := Nat.mul_le_mul step step
  have bound := natPair_upper a b
  unfold natPair at *
  omega

theorem natPair_injective {a b c d : Nat} (eq : natPair a b = natPair c d) : a = c ∧ b = d := by
  have sums : a + b = c + d := by
    have h₁ : ¬ a + b < c + d := fun h => Nat.ne_of_lt (natPair_sum_lt h) eq
    have h₂ : ¬ c + d < a + b := fun h => Nat.ne_of_lt (natPair_sum_lt h) eq.symm
    omega
  unfold natPair at eq
  rw [sums] at eq
  omega

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CountableSetFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



namespace SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forces_ex_iff (D : Name.NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (p : P) :
    Forces D (ex φ) env p ↔ DenseBelow p {q | ∃ τ : D.names, Forces D φ (extend τ env) q} := by
  classical
  change (∀ q, q ≤ p → ¬ ∀ τ : D.names, ∀ r, r ≤ q → ¬ Forces D φ (extend τ env) r) ↔ _
  constructor
  · intro h q qp
    have witness := h q qp
    push Not at witness
    obtain ⟨τ, r, rq, hφ⟩ := witness
    exact ⟨r, rq, τ, hφ⟩
  · intro dense q qp allNeg
    obtain ⟨r, rq, τ, hφ⟩ := dense q qp
    exact allNeg τ r rq hφ

end SetFormula



namespace SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem ex_witness_in_filter (D : Name.NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) {p : P} (hp : H.mem p) (h : Forces D (ex φ) env p) :
    ∃ τ : D.names, ∃ q, H.mem q ∧ q ≤ p ∧ Forces D φ (extend τ env) q := by
  have truth := forces_sound D H generic (ex φ) env hp h
  obtain ⟨x, hx, hxφ⟩ := (realize_ex _ φ _).1 truth
  obtain ⟨τ, rfl⟩ := hx
  rw [← evalAssignment_extend] at hxφ
  obtain ⟨q, hq, hφ⟩ := (forcing_truth D H generic φ (extend τ env)).1 hxφ
  obtain ⟨r, hr, rp, rq⟩ := H.directed hp hq
  exact ⟨τ, r, hr, rp, forces_mono D φ (extend τ env) hφ rq⟩

end SetFormula



namespace SetFormula

open Compression.RecursiveMaps

theorem natCode_injective {n : Nat} : Function.Injective (@natCode n) := by
  intro φ
  induction φ with
  | equal i j =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have parts := natPair_injective (natPair_injective eq).2
      exact congrArg₂ SetFormula.equal (Fin.ext parts.1) (Fin.ext parts.2)
    all_goals have bad := (natPair_injective eq).1; omega
  | mem i j =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have parts := natPair_injective (natPair_injective eq).2
      exact congrArg₂ SetFormula.mem (Fin.ext parts.1) (Fin.ext parts.2)
    all_goals have bad := (natPair_injective eq).1; omega
  | neg φ ih =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · exact congrArg SetFormula.neg (ih (natPair_injective eq).2)
    all_goals have bad := (natPair_injective eq).1; omega
  | conj φ χ ihφ ihχ =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have parts := natPair_injective (natPair_injective eq).2
      exact congrArg₂ SetFormula.conj (ihφ parts.1) (ihχ parts.2)
    · have bad := (natPair_injective eq).1; omega
  | all φ ih =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · exact congrArg SetFormula.all (ih (natPair_injective eq).2)

instance countable (n : Nat) : Countable (SetFormula n) := natCode_injective.countable

end SetFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CountableFormulaFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] [Countable P] {s : Presentation P}

theorem atomicFamily_countable (D : NameDomain s) (small : D.names.Countable) :
    (atomicFamily D).Countable := by
  let : Countable D.names := small
  let memSet (z : P × D.names × D.names) := Localized z.1 (MemWitness z.2.1.val z.2.2.val)
  let eqSet (z : D.names × D.names) := EqDecisionWitness z.1.val z.2.val
  apply ((Set.countable_range memSet).union (Set.countable_range eqSet)).mono
  intro E hE
  rcases hE with ⟨p, σ, τ, hσ, hτ, rfl⟩ | ⟨σ, τ, hσ, hτ, rfl⟩
  · exact Or.inl ⟨(p, ⟨σ, hσ⟩, ⟨τ, hτ⟩), rfl⟩
  · exact Or.inr ⟨(⟨σ, hσ⟩, ⟨τ, hτ⟩), rfl⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] [Countable P] {s : Presentation P}

theorem formulaFamily_countable (D : Name.NameDomain s) (small : D.names.Countable) :
    (formulaFamily D).Countable := by
  let : Countable D.names := small
  let decisions (z : Σ n, SetFormula n × Assignment D n) := DecisionWitness D z.2.1 z.2.2
  let universals (z : Σ n, SetFormula (n + 1) × Assignment D n) := AllDecisionWitness D z.2.1 z.2.2
  apply ((Name.atomicFamily_countable D small).union
    ((Set.countable_range decisions).union (Set.countable_range universals))).mono
  intro E hE
  rcases hE with atomic | (⟨n, φ, env, rfl⟩ | ⟨n, φ, env, rfl⟩)
  · exact Or.inl atomic
  · exact Or.inr (Or.inl ⟨⟨n, φ, env⟩, rfl⟩)
  · exact Or.inr (Or.inr ⟨⟨n, φ, env⟩, rfl⟩)

end PartitionPilot.Forcing.SetFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NatUnionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

theorem functionGraphOn_sUnion {A W : ZFSet.{u}}
    (shape : ∀ f ∈ W, ∃ B, B ⊆ A ∧ FunctionGraphOn B f)
    (cover : ∀ x ∈ A, ∃ f ∈ W, ∃ y, ZFSet.pair x y ∈ f)
    (agree : ∀ f ∈ W, ∀ g ∈ W, ∀ x y z,
      ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z) :
    FunctionGraphOn A (⋃₀ W) := by
  refine ⟨⋃₀ ⋃₀ (⋃₀ W), ?_, ?_⟩
  · intro z hz
    obtain ⟨f, hf, entry⟩ := ZFSet.mem_sUnion.1 hz
    obtain ⟨B, subset, func⟩ := shape f hf
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (func.to_isFunc.1 entry)
    exact ZFSet.pair_mem_prod.2 ⟨subset hx, pair_second_mem_doubleUnion hz⟩
  · intro x hx
    obtain ⟨f, hf, y, entry⟩ := cover x hx
    refine ⟨y, ZFSet.mem_sUnion.2 ⟨f, hf, entry⟩, ?_⟩
    intro z hz
    obtain ⟨g, hg, rel⟩ := ZFSet.mem_sUnion.1 hz
    exact agree g hg f hf x z y rel entry

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_OrbitPairGraphNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u v
variable {P Q R : Type u} {s : Presentation P}

theorem rename_check (t : Presentation Q) (f : P → Q) (one : P) (x : ZFSet.{u}) :
    rename t f (check s one x) = check t (f one) x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [check, rename_assemble, check]
    apply congrArg (fun names : x → Name t => assemble names (fun _ => f one))
    funext y
    exact ih y.val y.property

theorem rename_check_fixed (f : P → P) (one : P) (fixed : f one = one) (x : ZFSet.{u}) :
    rename s f (check s one x) = check s one x := by
  rw [rename_check, fixed]

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u v

namespace PosetAction
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_check [OrderTop P] (g : G) (x : ZFSet.{u}) :
    a.act s g (Name.check s ⊤ x) = Name.check s ⊤ x :=
  Name.rename_check_fixed (a.iso g) ⊤ (a.iso g).map_top x

theorem stabilizer_conjugation (g : G) (τ : Name s) :
    a.stabilizer s (a.act s g τ) = (a.stabilizer s τ).map (conjugateHom g) := by
  apply Subgroup.ext
  intro h
  constructor
  · intro fixed
    let k := g⁻¹ * h * g
    have eq : conjugateHom g k = h := by simp [conjugateHom, k, mul_assoc]
    refine Subgroup.mem_map.2 ⟨k, ?_, eq⟩
    change a.act s (g⁻¹ * h * g) τ = τ
    rw [a.act_mul, a.act_mul]
    change a.act s h (a.act s g τ) = a.act s g τ at fixed
    rw [fixed, a.act_inv_left]
  · intro member
    obtain ⟨k, fixed, rfl⟩ := Subgroup.mem_map.1 member
    change a.act s (g * k * g⁻¹) (a.act s g τ) = a.act s g τ
    change a.act s k τ = τ at fixed
    rw [a.act_mul, a.act_mul, a.act_inv_left, fixed]

end PosetAction
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps
universe u v w
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

namespace HereditarilySymmetric
variable {a : PosetAction G P} {s : Presentation P} {F : NormalSubgroupFamily G}

theorem translated {τ : Name s} (h : HereditarilySymmetric a s F τ) (g : G) :
    HereditarilySymmetric a s F (a.act s g τ) := by
  induction τ using Name.inductionOn with
  | step τ ih =>
    refine HereditarilySymmetric.mk ?_ ?_
    · rw [a.stabilizer_conjugation]
      exact F.conjugate g h.symmetric
    · intro ν p entry
      change Name.Entry ν (Name.rename s (a.iso g) τ) p at entry
      obtain ⟨σ, q, hσ, rfl, _⟩ := (Name.entry_rename s (a.iso g) τ ν p).1 entry
      exact ih σ q hσ (h.member hσ)

theorem assemble {α : Type w} [Small.{u} α] (names : α → Name s) (conditions : α → P)
    (sym : F.mem (a.stabilizer s (Name.assemble names conditions)))
    (children : ∀ i, HereditarilySymmetric a s F (names i)) :
    HereditarilySymmetric a s F (Name.assemble names conditions) := by
  refine HereditarilySymmetric.mk sym ?_
  intro σ p entry
  obtain ⟨i, rfl, _⟩ := (Name.entry_assemble names conditions σ p).1 entry
  exact children i

theorem assemble_common [OrderTop P] {α : Type w} [Small.{u} α]
    (names : α → Name s) (children : ∀ i, HereditarilySymmetric a s F (names i))
    (K : Subgroup G) (hK : F.mem K) (fixed : ∀ g ∈ K, ∀ i, a.act s g (names i) = names i) :
    HereditarilySymmetric a s F (Name.assemble names (fun _ => ⊤)) := by
  apply assemble names (fun _ => ⊤) _ children
  apply F.upward hK
  intro g hg
  change Name.rename s (a.iso g) (Name.assemble names (fun _ => ⊤)) = _
  rw [Name.rename_assemble]
  have top : a.iso g ⊤ = ⊤ := (a.iso g).map_top
  simp only [top]
  apply congrArg (fun ns : α → Name s => Name.assemble ns (fun _ => ⊤))
  funext i
  exact fixed g hg i

theorem check [OrderTop P] (a : PosetAction G P) (s : Presentation P)
    (F : NormalSubgroupFamily G) (x : ZFSet.{u}) :
    HereditarilySymmetric a s F (Name.check s ⊤ x) := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    rw [Name.check]
    exact assemble_common (fun y : x => Name.check s ⊤ y.val)
      (fun y => ih y.val y.property) ⊤ F.top (fun g _ y => a.act_check s g y.val)

theorem singleton [OrderTop P] {τ : Name s} (h : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.singleton ⊤ τ) :=
  assemble_common (fun _ : Unit => τ) (fun _ => h) (a.stabilizer s τ) h.symmetric
    (fun _ fixed _ => fixed)

theorem unorderedPair [OrderTop P] {σ τ : Name s}
    (hσ : HereditarilySymmetric a s F σ) (hτ : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.unorderedPair ⊤ σ τ) := by
  apply assemble_common (fun b : Bool => if b then σ else τ)
    (fun b => by cases b; exact hτ; exact hσ)
    (a.stabilizer s σ ⊓ a.stabilizer s τ) (F.inf hσ.symmetric hτ.symmetric)
  intro g fixed b
  cases b
  · exact fixed.2
  · exact fixed.1

theorem orderedPair [OrderTop P] {σ τ : Name s}
    (hσ : HereditarilySymmetric a s F σ) (hτ : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (Name.orderedPair ⊤ σ τ) :=
  hσ.singleton.unorderedPair (hσ.unorderedPair hτ)

end HereditarilySymmetric
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem nameDomain_countable (small : M.sets.Countable) : (M.nameDomain s).names.Countable :=
  small.preimage Subtype.val_injective

theorem conditions_countable (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets) :
    Countable P := by
  let : Countable M.sets := small
  let f : P → M.sets := fun p => ⟨s.encode p, M.transitive carrier (s.encode_mem p)⟩
  have injective : Function.Injective f := fun _ _ h => s.injective (congrArg Subtype.val h)
  exact injective.countable

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameOrbitBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mem_symmetric_values (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (H : Set P) (x : ZFSet.{u}) :
    x ∈ (a.symmetricDomain s D F).values H ↔
      ∃ τ ∈ D.names, HereditarilySymmetric a s F τ ∧ Name.eval H τ = x := by
  rw [Name.NameDomain.mem_values]
  constructor
  · rintro ⟨τ, ⟨hτ, hs⟩, eq⟩
    exact ⟨τ, hτ, hs, eq⟩
  · rintro ⟨τ, hτ, hs, eq⟩
    exact ⟨τ, ⟨hτ, hs⟩, eq⟩

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mem_orbitCodes (D : Name.NameDomain s) (W y : ZFSet.{u}) :
    y ∈ a.orbitCodes s D W ↔ ∃ g σ, σ ∈ D.names ∧ σ.val ∈ W ∧ y = (a.act s g σ).val := by
  rw [orbitCodes, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨g, σ⟩, eq⟩
    exact ⟨g, σ.val.val, σ.val.property, σ.property, eq.symm⟩
  · rintro ⟨g, σ, hσ, hW, eq⟩
    exact ⟨(g, ⟨⟨σ, hσ⟩, hW⟩), eq.symm⟩

end PartitionPilot.Forcing.PosetAction

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_OrdinalRecursionTraces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

open scoped ZFSet
universe u

namespace OrdinalRecursionTrace

variable {R : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → Prop}

theorem restriction_eq_of_common_values {A B C f g : ZFSet.{u}}
    (first : FunctionGraphOn A f) (second : FunctionGraphOn B g)
    (left : C ⊆ A) (right : C ⊆ B)
    (agree : ∀ x ∈ C, ∀ y z, ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z) :
    graphRestriction C f = graphRestriction C g := by
  apply ZFSet.ext
  intro w
  constructor
  · intro hw
    obtain ⟨V, function⟩ := first.restrict left
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 hw)
    obtain ⟨xy, hx⟩ := pair_mem_graphRestriction.1 hw
    obtain ⟨z, xz⟩ := second.total (right hx)
    exact pair_mem_graphRestriction.2 ⟨agree x hx y z xy xz ▸ xz, hx⟩
  · intro hw
    obtain ⟨V, function⟩ := second.restrict right
    obtain ⟨x, _, z, _, rfl⟩ := ZFSet.mem_prod.1 (function.1 hw)
    obtain ⟨xz, hx⟩ := pair_mem_graphRestriction.1 hw
    obtain ⟨y, xy⟩ := first.total (left hx)
    exact pair_mem_graphRestriction.2 ⟨agree x hx y z xy xz ▸ xy, hx⟩

theorem overlap {A B T f g : ZFSet.{u}}
    (first : OrdinalRecursionTrace R A f) (second : OrdinalRecursionTrace R B g)
    (ordinalA : ordinalSetProperty A) (ordinalB : ordinalSetProperty B)
    (left : A ⊆ T) (_right : B ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z) :
    ∀ β ∈ A, β ∈ B → ∀ y z, ZFSet.pair β y ∈ f → ZFSet.pair β z ∈ g → y = z := by
  intro β
  induction β using ZFSet.inductionOn with
  | h β ih =>
    intro hβA hβB y z hy hz
    have beforeA : β ⊆ A := fun x hx => ordinalA.1 β hβA x hx
    have beforeB : β ⊆ B := fun x hx => ordinalB.1 β hβB x hx
    have prefixes : graphRestriction β f = graphRestriction β g :=
      restriction_eq_of_common_values first.1 second.1 beforeA beforeB
        (fun x hx a b xa xb => ih x hx (beforeA hx) (beforeB hx) a b xa xb)
    have prefixTrace := first.restrict (ordinalSetProperty_member ordinalA hβA) beforeA
    have firstStep := first.2 β hβA y hy
    have secondStep := second.2 β hβB z hz
    rw [← prefixes] at secondStep
    exact stepUnique β (left hβA) (graphRestriction β f) prefixTrace y z firstStep secondStep

theorem unique {A T f g : ZFSet.{u}}
    (first : OrdinalRecursionTrace R A f) (second : OrdinalRecursionTrace R A g)
    (ordinalA : ordinalSetProperty A) (subset : A ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z) : f = g := by
  have eq := restriction_eq_of_common_values first.1 second.1 (fun _ hx => hx) (fun _ hx => hx)
    (fun x hx y z xy xz => first.overlap second ordinalA ordinalA subset subset stepUnique x hx hx y z xy xz)
  simpa only [first.1.restriction_eq, second.1.restriction_eq] using eq

theorem restriction_insert_last {A B f : ZFSet.{u}} (function : FunctionGraphOn A f)
    (subset : B ⊆ A) (y : ZFSet.{u}) :
    graphRestriction B (insert (ZFSet.pair A y) f) = graphRestriction B f := by
  apply restriction_eq_of_common_values (function.insert (ZFSet.mem_irrefl A) y) function
    (fun _ hx => ZFSet.mem_insert_of_mem A (subset hx)) subset
  intro x hx z w xz xw
  rcases ZFSet.mem_insert_iff.1 xz with eq | xz
  · have same : x = A := (ZFSet.pair_inj.1 eq).1
    exact False.elim (ZFSet.mem_irrefl A (same ▸ subset hx))
  · exact function.unique xz xw

theorem succ {A f y : ZFSet.{u}} (trace : OrdinalRecursionTrace R A f)
    (ordinalA : ordinalSetProperty A) (step : R A f y) :
    OrdinalRecursionTrace R (insert A A) (insert (ZFSet.pair A y) f) := by
  refine ⟨trace.1.insert (ZFSet.mem_irrefl A) y, ?_⟩
  intro β hβ z hz
  rcases ZFSet.mem_insert_iff.1 hβ with eq | hβ
  · subst β
    have value : z = y := (trace.1.insert (ZFSet.mem_irrefl A) y).unique hz
      (ZFSet.mem_insert _ _)
    rw [restriction_insert_last trace.1 (fun _ hx => hx) y, trace.1.restriction_eq, value]
    exact step
  · rw [restriction_insert_last trace.1 (fun x hx => ordinalA.1 β hβ x hx) y]
    rcases ZFSet.mem_insert_iff.1 hz with eq | hz
    · have same : β = A := (ZFSet.pair_inj.1 eq).1
      exact False.elim (ZFSet.mem_irrefl A (same ▸ hβ))
    · exact trace.2 β hβ z hz

theorem sUnion {A T W : ZFSet.{u}} (subset : A ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z)
    (members : ∀ f ∈ W, ∃ B, ordinalSetProperty B ∧ B ⊆ A ∧ OrdinalRecursionTrace R B f)
    (cover : ∀ β ∈ A, ∃ f ∈ W, ∃ y, ZFSet.pair β y ∈ f) :
    OrdinalRecursionTrace R A (⋃₀ W) := by
  have agree : ∀ f ∈ W, ∀ g ∈ W, ∀ x y z,
      ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ g → y = z := by
    intro f hf g hg x y z xy xz
    obtain ⟨B, ordinalB, boundB, first⟩ := members f hf
    obtain ⟨C, ordinalC, boundC, second⟩ := members g hg
    exact first.overlap second ordinalB ordinalC (fun _ hx => subset (boundB hx))
      (fun _ hx => subset (boundC hx)) stepUnique x
      (first.1.pair_source xy) (second.1.pair_source xz) y z xy xz
  have function : FunctionGraphOn A (⋃₀ W) := functionGraphOn_sUnion
    (fun f hf => by
      obtain ⟨B, _, bound, trace⟩ := members f hf
      exact ⟨B, bound, trace.1⟩) cover agree
  refine ⟨function, ?_⟩
  intro β _ y hy
  obtain ⟨f, hf, βy⟩ := ZFSet.mem_sUnion.1 hy
  obtain ⟨B, ordinalB, boundB, trace⟩ := members f hf
  have βB := trace.1.pair_source βy
  have beforeB : β ⊆ B := fun x hx => ordinalB.1 β βB x hx
  have prefixes : graphRestriction β (⋃₀ W) = graphRestriction β f := by
    apply restriction_eq_of_common_values function trace.1 (fun _ hx => boundB (beforeB hx)) beforeB
    intro x _ z w xz xw
    obtain ⟨g, hg, xz⟩ := ZFSet.mem_sUnion.1 xz
    exact agree g hg f hf x z w xz xw
  rw [prefixes]
  exact trace.2 β βB y βy

theorem sUnion_successors {A T W : ZFSet.{u}} (ordinalA : ordinalSetProperty A)
    (subset : A ⊆ T)
    (stepUnique : ∀ β ∈ T, ∀ p, OrdinalRecursionTrace R β p →
      ∀ y z, R β p y → R β p z → y = z)
    (members : ∀ f ∈ W, ∃ β ∈ A, OrdinalRecursionTrace R (insert β β) f)
    (cover : ∀ β ∈ A, ∃ f ∈ W, OrdinalRecursionTrace R (insert β β) f) :
    OrdinalRecursionTrace R A (⋃₀ W) := by
  apply sUnion subset stepUnique
  · intro f hf
    obtain ⟨β, hβ, trace⟩ := members f hf
    refine ⟨insert β β, ordinalSetProperty_succ (ordinalSetProperty_member ordinalA hβ), ?_, trace⟩
    intro x hx
    exact (ZFSet.mem_insert_iff.1 hx).elim (fun eq => eq ▸ hβ) (fun hx => ordinalA.1 β hβ x hx)
  · intro β hβ
    obtain ⟨f, hf, trace⟩ := cover β hβ
    obtain ⟨y, βy⟩ := trace.1.total (ZFSet.mem_insert β β)
    exact ⟨f, hf, y, βy⟩

end OrdinalRecursionTrace

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GraphValueMembershipFormula
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_graphValueMemberFormula {n} (x z beta : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphValueMemberFormula x z beta) env ↔
      ∃ A, ZFSet.pair (env beta) A ∈ env z ∧ env x ∈ A := by
  simp only [graphValueMemberFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  change (∃ pair ∈ env z, ∃ unordered ∈ pair, ∃ A ∈ unordered,
    ZFSet.pair (env beta) A ∈ env z ∧ env x ∈ A) ↔ _
  constructor
  · rintro ⟨pair, _pairMember, unordered, _unorderedMember, A, _valueMember, edge, member⟩
    exact ⟨A, edge, member⟩
  · rintro ⟨A, edge, member⟩
    exact ⟨ZFSet.pair (env beta) A, edge, {env beta, A}, ZFSet.mem_pair.2 (Or.inr rfl),
      A, ZFSet.mem_pair.2 (Or.inr rfl), edge, member⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.SetFormula
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem realize_graphValueMember_values (D : Name.NameDomain s) (H : Set P)
    {n} (x z beta : Fin n) (env : Assignment D n) :
    Realize (D.values H) (BoundedFormula.graphValueMemberFormula x z beta).toFormula
      (evalAssignment H env) ↔
      ∃ A, ZFSet.pair (Name.eval H (env beta).val) A ∈ Name.eval H (env z).val ∧
        Name.eval H (env x).val ∈ A := by
  let N : TransitiveGround := ⟨D.values H, D.values_transitive H⟩
  exact (BoundedFormula.realize_toFormula N _ _ (fun i => ⟨env i, rfl⟩)).trans
    (BoundedFormula.truth_graphValueMemberFormula x z beta (evalAssignment H env))

end PartitionPilot.Forcing.SetFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCompleteProjectionGenericity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem codedFamily_countable (small : M.sets.Countable) : (M.codedFamily s).Countable :=
  small.image _

end TransitiveGround



namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem exists_coded_ordinary_generic (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  have ordinary := formulaFamily_countable (M.nameDomain s) (M.nameDomain_countable s small)
  obtain ⟨H, member, generic⟩ := exists_generic_for_countable_family p
    (M.codedFamily s ∪ formulaFamily (M.nameDomain s))
    ((M.codedFamily_countable s small).union ordinary)
  exact ⟨H, member, (fun E hE => generic E (Or.inl hE)),
    fun E hE => generic E (Or.inr hE)⟩

end TransitiveGround



namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem ordinary_generic_meets_coded_dense (H : ConditionFilter P)
    (ordinary : H.GenericFor (formulaFamily (M.nameDomain s))) {E : Set P}
    (code : s.subset E ∈ M.sets) (dense : Dense E) : H.Meets E := by
  have emptyGround : (∅ : ZFSet.{u}) ∈ M.sets := M.empty_mem ⟨s.subset E, code⟩
  let witness : Name s := ⟨ZFSet.prod {∅} (s.subset E), IsName.mk
    (by
      intro z hz
      obtain ⟨x, hx, y, hy, shape⟩ := ZFSet.mem_prod.1 hz
      obtain ⟨p, _hp, rfl⟩ := (s.mem_subset E y).1 hy
      have empty : x = ∅ := ZFSet.mem_singleton.1 hx
      exact ⟨∅, p, shape.trans (congrArg (fun v => ZFSet.pair v (s.encode p)) empty)⟩)
    (by
      intro y p member
      have empty : y = ∅ := ZFSet.mem_singleton.1 (ZFSet.pair_mem_prod.1 member).1
      exact empty.symm ▸ (Name.empty s).property)⟩
  have witnessGround : witness.val ∈ M.sets := M.prod_mem pairing unions powers separation
    (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing emptyGround emptyGround) code
  have entries (sigma : Name s) (p : P) :
      Name.Entry sigma witness p ↔ sigma = Name.empty s ∧ p ∈ E := by
    constructor
    · intro entry
      have components : sigma.val ∈ {∅} ∧ s.encode p ∈ s.subset E :=
        ZFSet.pair_mem_prod.1 entry
      exact ⟨Subtype.ext (ZFSet.mem_singleton.1 components.1),
        (s.encode_mem_subset E p).1 components.2⟩
    · rintro ⟨rfl, member⟩
      exact ZFSet.pair_mem_prod.2
        ⟨ZFSet.mem_singleton.2 rfl, (s.encode_mem_subset E p).2 member⟩
  have forced (p : P) : Name.ForcesMem p (Name.empty s) witness := by
    apply Name.forcesMem_of_dense
    intro q _qp
    obtain ⟨r, rq, member⟩ := dense q
    exact ⟨r, rq, Name.forcesMem_entry ((entries (Name.empty s) r).2 ⟨rfl, member⟩)⟩
  obtain ⟨p, hp⟩ := H.nonempty
  have member := Name.forcesMem_sound (M.nameDomain s) H
    (fun E hE => ordinary E (Or.inl hE)) emptyGround witnessGround hp (forced p)
  obtain ⟨sigma, q, entry, hq, _equal⟩ := (Name.mem_eval {r | H.mem r} witness _).1 member
  exact ⟨q, hq, ((entries sigma q).1 entry).2⟩

end TransitiveGround



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameRenameSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation collection carrier order

theorem realize_candidateForcingFormula {n : Nat} (phi : SetFormula (n + 1))
    (env : Assignment (M.nameDomain s) n) (W : ZFSet.{u})
    (valid : ∀ z ∈ W, IsName s z) (p : P) :
    Realize M.sets (candidateForcingFormula phi)
      (extend (s.encode p) (extend W (extend s.carrier
        (extend s.conditionOrder (fun i => (env i).val.val))))) ↔
      ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
        Forces (M.nameDomain s) phi (extend tau env) p := by
  let params := extend (s.encode p) (extend W (extend s.carrier
    (extend s.conditionOrder (fun i => (env i).val.val))))
  change Realize M.sets (candidateForcingFormula phi) params ↔ _
  rw [candidateForcingFormula, realize_ex]
  constructor
  · rintro ⟨z, hz, member, forced⟩
    change z ∈ W at member
    let tau : (M.nameDomain s).names := ⟨⟨z, valid z member⟩, hz⟩
    refine ⟨tau, member, ?_⟩
    exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 phi (extend 3 (extend 4 Fin.elim0)) 1
      (extend 0 (fun i => i.succ.succ.succ.succ.succ)) (extend z params)
      rfl rfl p (extend tau env) rfl (Fin.cases rfl (fun _ => rfl))).1 forced
  · rintro ⟨tau, member, forced⟩
    refine ⟨tau.val.val, tau.property, member, ?_⟩
    exact (M.realize_ordinaryGroundForcing s pairing unions powers separation collection
      carrier order 0 1 phi (extend 3 (extend 4 Fin.elim0)) 1
      (extend 0 (fun i => i.succ.succ.succ.succ.succ)) (extend tau.val.val params)
      rfl rfl p (extend tau env) rfl (Fin.cases rfl (fun _ => rfl))).2 forced

theorem candidateForcingSet_mem {n : Nat} (phi : SetFormula (n + 1))
    (env : Assignment (M.nameDomain s) n) (W : ZFSet.{u}) (ground : W ∈ M.sets)
    (valid : ∀ z ∈ W, IsName s z) :
    s.subset (fun p => ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
      Forces (M.nameDomain s) phi (extend tau env) p) ∈ M.sets := by
  let params := extend W (extend s.carrier (extend s.conditionOrder (fun i => (env i).val.val)))
  have equal : s.subset (fun p => ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
      Forces (M.nameDomain s) phi (extend tau env) p) =
      ZFSet.sep (fun z => Realize M.sets (candidateForcingFormula phi) (extend z params)) s.carrier := by
    apply ZFSet.ext
    intro z
    rw [s.mem_subset, ZFSet.mem_sep]
    constructor
    · rintro ⟨p, forced, rfl⟩
      exact ⟨s.encode_mem p, (M.realize_candidateForcingFormula s pairing unions powers separation
        collection carrier order phi env W valid p).2 forced⟩
    · rintro ⟨member, truth⟩
      obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 member
      exact ⟨p, (M.realize_candidateForcingFormula s pairing unions powers separation collection
        carrier order phi env W valid p).1 truth, rfl⟩
  rw [equal]
  exact M.separation_mem separation (candidateForcingFormula phi) params
    (Fin.cases ground (Fin.cases carrier (Fin.cases order (fun i => (env i).property)))) carrier

end PartitionPilot.Forcing.TransitiveGround

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundGraphValueDescendantWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} (s : Presentation P)

theorem mem_childFamilyCodes (W : ZFSet.{u}) (valid : ∀ z ∈ W, IsName s z)
    (y : ZFSet.{u}) :
    y ∈ childFamilyCodes s W ↔
      ∃ tau : Name s, tau.val ∈ W ∧ ∃ sigma : Name s, ∃ p,
        Entry sigma tau p ∧ y = sigma.val := by
  rw [childFamilyCodes, mem_relationImage]
  constructor
  · rintro ⟨_, q, _, coded⟩
    have raw := ((pair_mem_relationConverse _ _ _ y q).1 coded).2.2
    obtain ⟨x, hx, entry⟩ := ZFSet.mem_sUnion.1 raw
    let tau : Name s := ⟨x, valid x hx⟩
    obtain ⟨sigma, p, shape⟩ := entries_cover tau entry
    refine ⟨tau, hx, sigma, p, ?_, (ZFSet.pair_inj.1 shape).1⟩
    change ZFSet.pair sigma.val (s.encode p) ∈ x
    rw [← shape]
    exact entry
  · rintro ⟨tau, htau, sigma, p, entry, rfl⟩
    have raw : ZFSet.pair sigma.val (s.encode p) ∈ ZFSet.sUnion W :=
      ZFSet.mem_sUnion.2 ⟨tau.val, htau, entry⟩
    have bound := pair_first_mem_doubleUnion raw
    exact ⟨bound, s.encode p, s.encode_mem p,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨bound, s.encode_mem p, raw⟩⟩

theorem childFamilyCodes_valid (W : ZFSet.{u}) (valid : ∀ z ∈ W, IsName s z) :
    ∀ z ∈ childFamilyCodes s W, IsName s z := by
  intro z member
  obtain ⟨tau, _, sigma, _, _, rfl⟩ := (mem_childFamilyCodes s W valid z).1 member
  exact sigma.property

theorem childFamilyCodes_hs {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (W : ZFSet.{u}) (valid : ∀ z ∈ W, IsName s z)
    (symmetric : ∀ tau : Name s, tau.val ∈ W → HereditarilySymmetric a s F tau)
    (sigma : Name s) (member : sigma.val ∈ childFamilyCodes s W) :
    HereditarilySymmetric a s F sigma := by
  obtain ⟨tau, htau, child, p, entry, equal⟩ :=
    (mem_childFamilyCodes s W valid sigma.val).1 member
  have same : sigma = child := Subtype.ext equal
  exact same.symm ▸ (symmetric tau htau).member entry

theorem eval_member_childFamilyCodes (W : ZFSet.{u}) (valid : ∀ z ∈ W, IsName s z)
    (H : Set P) (tau : Name s) (htau : tau.val ∈ W) (x : ZFSet.{u})
    (member : x ∈ eval H tau) :
    ∃ sigma : Name s, sigma.val ∈ childFamilyCodes s W ∧ eval H sigma = x := by
  obtain ⟨sigma, p, entry, _hp, equal⟩ := (mem_eval H tau x).1 member
  exact ⟨sigma, (mem_childFamilyCodes s W valid sigma.val).2 ⟨tau, htau, sigma, p, entry, rfl⟩, equal⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem childFamilyCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (W : ZFSet.{u}) (ground : W ∈ M.sets) :
    Name.childFamilyCodes s W ∈ M.sets := by
  have entries := M.union_mem unions ground
  have bound := M.union_mem unions (M.union_mem unions entries)
  exact M.relationImage_mem separation carrier bound
    (M.relationConverse_mem pairing unions powers separation bound carrier entries)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} (s : Presentation P)

theorem descendantFamilyCodes_valid (tau : Name s) (n : Nat) :
    ∀ z ∈ descendantFamilyCodes s tau n, IsName s z := by
  induction n with
  | zero =>
    intro z member
    have same : z = tau.val := ZFSet.mem_singleton.1 member
    exact same.symm ▸ tau.property
  | succ n ih => exact childFamilyCodes_valid s _ ih

theorem descendantFamilyCodes_hs {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (tau : Name s) (symmetric : HereditarilySymmetric a s F tau) (n : Nat) :
    ∀ sigma : Name s, sigma.val ∈ descendantFamilyCodes s tau n →
      HereditarilySymmetric a s F sigma := by
  induction n with
  | zero =>
    intro sigma member
    have same : sigma = tau := Subtype.ext (ZFSet.mem_singleton.1 member)
    exact same.symm ▸ symmetric
  | succ n ih =>
    exact childFamilyCodes_hs s a F _ (descendantFamilyCodes_valid s tau n) ih

theorem value_member_fourthDescendant (H : Set P) (tau : Name s)
    (beta A x : ZFSet.{u}) (edge : ZFSet.pair beta A ∈ eval H tau) (member : x ∈ A) :
    ∃ sigma : Name s, sigma.val ∈ descendantFamilyCodes s tau 4 ∧ eval H sigma = x := by
  have zero : tau.val ∈ descendantFamilyCodes s tau 0 := ZFSet.mem_singleton.2 rfl
  obtain ⟨pairName, first, pairValue⟩ := eval_member_childFamilyCodes s
    (descendantFamilyCodes s tau 0) (descendantFamilyCodes_valid s tau 0) H tau zero _ edge
  have pairMember : ({beta, A} : ZFSet.{u}) ∈ eval H pairName := by
    rw [pairValue]
    exact ZFSet.mem_pair.2 (Or.inr rfl)
  obtain ⟨unorderedName, second, unorderedValue⟩ := eval_member_childFamilyCodes s
    (descendantFamilyCodes s tau 1) (descendantFamilyCodes_valid s tau 1) H pairName first _ pairMember
  have valueMember : A ∈ eval H unorderedName := by
    rw [unorderedValue]
    exact ZFSet.mem_pair.2 (Or.inr rfl)
  obtain ⟨valueName, third, valueValue⟩ := eval_member_childFamilyCodes s
    (descendantFamilyCodes s tau 2) (descendantFamilyCodes_valid s tau 2) H unorderedName second _ valueMember
  have elementMember : x ∈ eval H valueName := valueValue.symm ▸ member
  exact eval_member_childFamilyCodes s (descendantFamilyCodes s tau 3)
    (descendantFamilyCodes_valid s tau 3) H valueName third x elementMember

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem descendantFamilyCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (tau : Name s) (ground : tau.val ∈ M.sets) (n : Nat) :
    Name.descendantFamilyCodes s tau n ∈ M.sets := by
  induction n with
  | zero =>
    simpa only [Name.descendantFamilyCodes, ZFSet.pair_eq_singleton] using
      M.unorderedPair_mem pairing ground ground
  | succ n ih => exact M.childFamilyCodes_mem s pairing unions powers separation carrier _ ih

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem graphValue_fourthDescendant_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets)
    (z beta : (M.nameDomain s).names) (base : P)
    (forced : Forces (M.nameDomain s)
      (ex (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula)
      (extend z (extend beta Fin.elim0)) base) :
    DenseBelow base {q | ∃ tau : (M.nameDomain s).names,
      tau.val.val ∈ Name.descendantFamilyCodes s z.val 4 ∧
      Forces (M.nameDomain s) (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula
        (extend tau (extend z (extend beta Fin.elim0))) q} := by
  have descendants := M.descendantFamilyCodes_mem s pairing unions powers separation carrier
    z.val z.property 4
  intro p below
  obtain ⟨H, hp, _coded, ordinary⟩ := M.exists_coded_ordinary_generic s small carrier p
  obtain ⟨tau, q, hq, _qbase, witness⟩ := ex_witness_in_filter (M.nameDomain s) H ordinary
    (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula
    (extend z (extend beta Fin.elim0)) (H.upward hp below) forced
  have truth := (realize_graphValueMember_values (M.nameDomain s) {r | H.mem r} 0 1 2
    (extend tau (extend z (extend beta Fin.elim0)))).1
      (forces_sound (M.nameDomain s) H ordinary _ _ hq witness)
  obtain ⟨A, edge, member⟩ := truth
  obtain ⟨sigma, child, same⟩ := Name.value_member_fourthDescendant s {r | H.mem r}
    z.val (Name.eval {r | H.mem r} beta.val) A (Name.eval {r | H.mem r} tau.val) edge member
  let candidate : (M.nameDomain s).names := ⟨sigma, M.transitive descendants child⟩
  have actual : Realize ((M.nameDomain s).values {r | H.mem r})
      (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula
      (evalAssignment {r | H.mem r} (extend candidate (extend z (extend beta Fin.elim0)))) := by
    apply (realize_graphValueMember_values (M.nameDomain s) {r | H.mem r} 0 1 2 _).2
    exact ⟨A, edge, same.symm ▸ member⟩
  obtain ⟨r, hr, recorded⟩ := (forcing_truth (M.nameDomain s) H ordinary
    (BoundedFormula.graphValueMemberFormula 0 1 2).toFormula
    (extend candidate (extend z (extend beta Fin.elim0)))).1 actual
  obtain ⟨common, _member, toP, toR⟩ := H.directed hp hr
  exact ⟨common, toP, candidate, child, forces_mono (M.nameDomain s) _ _ recorded toR⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_IndexedTupleNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u





namespace Name
variable {P : Type u} {s : Presentation P} {I f : ZFSet.{u}}

theorem mem_eval_indexedGraphName (H : Set P) (one : P) (hone : one ∈ H)
    (function : FunctionGraphOn I f) (names : ∀ i, IsName s (function.value i)) (z : ZFSet.{u}) :
    z ∈ eval H (indexedGraphName one function names) ↔
      ∃ i : I, ZFSet.pair i.val (eval H ⟨function.value i, names i⟩) = z := by
  rw [indexedGraphName, mem_eval_assemble]
  simp only [hone, true_and]
  apply exists_congr
  intro index
  let named : Name s := ⟨function.value index, names index⟩
  change eval H (orderedPair one (check s one index.val) named) = z ↔
    ZFSet.pair index.val (eval H named) = z
  rw [eval_orderedPair H one hone, eval_check H one hone]

theorem pair_mem_eval_indexedGraphName (H : Set P) (one : P) (hone : one ∈ H)
    (function : FunctionGraphOn I f) (names : ∀ i, IsName s (function.value i))
    (i : I.toSet) (x : ZFSet.{u}) :
    ZFSet.pair i.val x ∈ eval H (indexedGraphName one function names) ↔
      eval H ⟨function.value i, names i⟩ = x := by
  rw [mem_eval_indexedGraphName H one hone]
  constructor
  · rintro ⟨j, equal⟩
    have ji : j = i := Subtype.ext (ZFSet.pair_inj.1 equal).1
    subst j
    exact (ZFSet.pair_inj.1 equal).2
  · intro equal
    exact ⟨i, congrArg (ZFSet.pair i.val) equal⟩

theorem eval_indexedGraphName_function (H : Set P) (one : P) (hone : one ∈ H)
    (function : FunctionGraphOn I f) (names : ∀ i, IsName s (function.value i)) :
    ZFSet.IsFunc I (ZFSet.range (fun i : I => eval H ⟨function.value i, names i⟩))
      (eval H (indexedGraphName one function names)) := by
  constructor
  · intro z hz
    obtain ⟨i, rfl⟩ := (mem_eval_indexedGraphName H one hone function names z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨i.property, ZFSet.mem_range.2 ⟨i, rfl⟩⟩
  · intro i hi
    let j : I.toSet := ⟨i, hi⟩
    refine ⟨eval H ⟨function.value j, names j⟩,
      (pair_mem_eval_indexedGraphName H one hone function names j _).2 rfl, ?_⟩
    intro x hx
    exact ((pair_mem_eval_indexedGraphName H one hone function names j x).1 hx).symm

end Name

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} {s : Presentation P}

theorem rename_indexedTuple (t : Presentation Q) (f : P → Q) (one : P)
    (I : ZFSet.{u}) (names : I.toSet → Name s) :
    rename t f (indexedTuple one I names) =
      indexedTuple (f one) I (fun i => rename t f (names i)) := by
  rw [indexedTuple, rename_assemble, indexedTuple]
  apply congrArg (fun ns : I → Name t => assemble ns (fun _ => f one))
  funext i
  rw [rename_orderedPair, rename_check]

theorem act_indexedTuple {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (g : G) (I : ZFSet.{u}) (names : I.toSet → Name s) :
    a.act s g (indexedTuple ⊤ I names) = indexedTuple ⊤ I (fun i => a.act s g (names i)) := by
  change rename s (a.iso g) _ = _
  rw [rename_indexedTuple, (a.iso g).map_top]
  rfl

theorem indexedTuple_supported {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (I : ZFSet.{u}) (names : I.toSet → Name s)
    (K : Subgroup G) (fixed : ∀ g ∈ K, ∀ i, a.act s g (names i) = names i) :
    K ≤ a.stabilizer s (indexedTuple ⊤ I names) := by
  intro g hg
  change a.act s g (indexedTuple ⊤ I names) = _
  rw [act_indexedTuple]
  exact congrArg (indexedTuple ⊤ I) (funext (fixed g hg))

theorem indexedTuple_hs {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G) (I : ZFSet.{u})
    (names : I.toSet → Name s) (K : Subgroup G) (hK : F.mem K)
    (fixed : ∀ g ∈ K, ∀ i, a.act s g (names i) = names i)
    (children : ∀ i, HereditarilySymmetric a s F (names i)) :
    HereditarilySymmetric a s F (indexedTuple ⊤ I names) := by
  apply HereditarilySymmetric.assemble
  · exact F.upward hK (indexedTuple_supported a I names K fixed)
  · intro i
    exact (HereditarilySymmetric.check a s F i.val).orderedPair (children i)

end PartitionPilot.Forcing.Name

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_OrbitImageFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_codedNameActionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (g : G) (x y : ZFSet.{u}) (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets codedNameActionFormula (extend (t.encode g) (extend x (extend y
      (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      ∃ σ : (M.nameDomain s).names, σ.val.val = x ∧ y = (a.act s g σ.val).val := by
  rw [codedNameActionFormula]
  change (Realize M.sets _ _ ∧ Realize M.sets _ _ ∧ Realize M.sets _ _) ↔ _
  simp only [realize_domainApplication, map_extend, map_empty]
  constructor
  · rintro ⟨nameX, nameY, action⟩
    have nx := (M.realize_uniformNameFormula s pairing unions powers separation collection carrier x hx).1 nameX
    have ny := (M.realize_uniformNameFormula s pairing unions powers separation collection carrier y hy).1 nameY
    have eq := (M.realize_nameActionFormula a s t pairing unions powers separation collection carrier group maps
      g ⟨x, nx⟩ ⟨y, ny⟩ hx hy).1 action
    exact ⟨⟨⟨x, nx⟩, hx⟩, rfl, (congrArg Subtype.val eq).symm⟩
  · rintro ⟨σ, rfl, rfl⟩
    refine ⟨(M.realize_uniformNameFormula s pairing unions powers separation collection carrier _ hx).2 σ.val.property,
      (M.realize_uniformNameFormula s pairing unions powers separation collection carrier _ hy).2
        (a.act s g σ.val).property, ?_⟩
    exact (M.realize_nameActionFormula a s t pairing unions powers separation collection carrier group maps
      g σ.val (a.act s g σ.val) hx hy).2 rfl

theorem realize_orbitImageFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (W z y : ZFSet.{u}) (hz : z ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets orbitImageFormula (extend z (extend y (orbitParameters a s t W))) ↔
      ∃ g, ∃ σ : (M.nameDomain s).names, σ.val.val ∈ W ∧
        z = ZFSet.pair (t.encode g) σ.val.val ∧ y = (a.act s g σ.val).val := by
  rw [orbitImageFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨g, member, shape, action⟩ := (M.realize_exConditions t 5 _
      (extend x (extend z (extend y (orbitParameters a s t W)))) group rfl).1 rest
    rw [realize_atomicApplication, map_extend, map_extend, map_empty] at action
    obtain ⟨σ, eq, output⟩ := (M.realize_codedNameActionFormula a s t pairing unions powers separation collection
      carrier group maps g x y hx hy).1 action
    have raw := (M.realize_orderedPairFormula pairing 2 0 1
      (extend (t.encode g) (extend x (extend z (extend y (orbitParameters a s t W))))) hz
      (M.transitive group (t.encode_mem g)) hx).1 shape
    exact ⟨g, σ, eq.symm ▸ member, raw.trans (congrArg (ZFSet.pair (t.encode g)) eq.symm), output⟩
  · rintro ⟨g, σ, member, shape, output⟩
    refine ⟨σ.val.val, σ.property, ?_⟩
    apply (M.realize_exConditions t 5 _
      (extend σ.val.val (extend z (extend y (orbitParameters a s t W)))) group rfl).2
    refine ⟨g, member, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 2 0 1
        (extend (t.encode g) (extend σ.val.val (extend z (extend y (orbitParameters a s t W))))) hz
        (M.transitive group (t.encode_mem g)) σ.property).2 shape
    · rw [realize_atomicApplication, map_extend, map_extend, map_empty]
      exact (M.realize_codedNameActionFormula a s t pairing unions powers separation collection
        carrier group maps g σ.val.val y σ.property hy).2 ⟨σ, rfl, output⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMixtureTermBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem orbitCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) : a.orbitCodes s (M.nameDomain s) W ∈ M.sets := by
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers group hW
  apply M.definable_image_mem separation collection orbitImageFormula (orbitParameters a s t W)
    (Fin.cases hW (Fin.cases carrier (Fin.cases group (Fin.cases maps (fun i => Fin.elim0 i))))) hB
  · intro y hy
    obtain ⟨g, σ, hσ, _, rfl⟩ := (a.mem_orbitCodes s (M.nameDomain s) W y).1 hy
    exact M.act_mem s a t pairing unions powers separation collection carrier maps g σ hσ
  · intro y hy
    rw [a.mem_orbitCodes]
    constructor
    · rintro ⟨g, σ, hσ, hσW, eq⟩
      have hb := pairBound (t.encode g) (t.encode_mem g) σ.val hσW
      exact ⟨ZFSet.pair (t.encode g) σ.val, hb,
        (M.realize_orbitImageFormula a s t pairing unions powers separation collection carrier group maps W _ y
          (M.transitive hB hb) hy).2 ⟨g, ⟨σ, hσ⟩, hσW, rfl, eq⟩⟩
    · rintro ⟨z, hz, rel⟩
      obtain ⟨g, σ, hσW, _, eq⟩ := (M.realize_orbitImageFormula a s t pairing unions powers separation collection
        carrier group maps W z y (M.transitive hB hz) hy).1 rel
      exact ⟨g, σ.val, σ.property, hσW, eq⟩
  · intro z hz y hy w hw rely relw
    obtain ⟨g, σ, _, shape, eqy⟩ := (M.realize_orbitImageFormula a s t pairing unions powers separation collection
      carrier group maps W z y (M.transitive hB hz) hy).1 rely
    obtain ⟨h, τ, _, shape', eqw⟩ := (M.realize_orbitImageFormula a s t pairing unions powers separation collection
      carrier group maps W z w (M.transitive hB hz) hw).1 relw
    have parts := ZFSet.pair_inj.1 (shape.symm.trans shape')
    have gh := t.injective parts.1
    have names : σ.val = τ.val := Subtype.ext parts.2
    rw [eqy, eqw, gh, names]

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_NaturalStepFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

namespace BoundedFormula

theorem truth_graphRestrictionFormula {n} (p a b f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphRestrictionFormula p a b f) env ↔
      env p = ZFSet.sep (fun z => z ∈ ZFSet.prod (env a) (env b)) (env f) := by
  simp only [graphRestrictionFormula, Truth, truth_imp, truth_productElementFormula]
  change ((∀ z ∈ env p, z ∈ env f ∧ z ∈ ZFSet.prod (env a) (env b)) ∧
    (∀ z ∈ env f, z ∈ ZFSet.prod (env a) (env b) → z ∈ env p)) ↔ _
  constructor
  · rintro ⟨forward, backward⟩
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨forward z, fun hz => backward z hz.1 hz.2⟩
  · intro eq
    rw [eq]
    exact ⟨fun z hz => ZFSet.mem_sep.1 hz, fun z hz bound => ZFSet.mem_sep.2 ⟨hz, bound⟩⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_graphRestrictionFormula {n} (p a b f : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (BoundedFormula.graphRestrictionFormula p a b f).toFormula env ↔
      env p = ZFSet.sep (fun z => z ∈ ZFSet.prod (env a) (env b)) (env f) :=
  (BoundedFormula.realize_toFormula M _ _ members).trans
    (BoundedFormula.truth_graphRestrictionFormula p a b f env)

end TransitiveGround

end




open SetFormula
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem realize_ordinalRecursionTraceFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    Realize M.sets (ordinalRecursionTraceFormula φ) (extend A (extend f params)) ↔
      OrdinalRecursionTrace (groundRecursionStep M φ params) A f := by
  rw [ordinalRecursionTraceFormula, realize_ex]
  constructor
  · rintro ⟨B, hB, function, steps⟩
    have mem3 : ∀ i, extend B (extend A (extend f params)) i ∈ M.sets :=
      Fin.cases hB (Fin.cases hA (Fin.cases hf members))
    have func : ZFSet.IsFunc A B f := (BoundedFormula.truth_functionFormula 1 0 2 _).1
      ((BoundedFormula.realize_toFormula M _ _ mem3).1 function)
    refine ⟨⟨B, func⟩, ?_⟩
    intro a ha y ay
    have haM := M.transitive hA ha
    have hyB := (ZFSet.pair_mem_prod.1 (func.1 ay)).2
    have hyM := M.transitive hB hyB
    have first := (realize_imp M.sets _ _ _).1 (steps a haM) ha
    have second := (realize_imp M.sets _ _ _).1 (first y hyM) hyB
    have mem5 : ∀ i, extend y (extend a (extend B (extend A (extend f params)))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases haM mem3)
    have pairCode := (BoundedFormula.realize_toFormula M _ _ mem5).2
      ((BoundedFormula.truth_pairMembershipFormula 1 0 4 _).2 ay)
    obtain ⟨p, hp, restricted, step⟩ := (realize_ex M.sets _ _).1
      ((realize_imp M.sets _ _ _).1 second pairCode)
    have eq := (M.realize_graphRestrictionFormula 0 2 3 5 _ (Fin.cases hp mem5)).1 restricted
    have same : p = graphRestriction a f := eq.trans (graphRestriction_eq_sep func).symm
    rw [realize_reindex, map_extend, map_extend, map_extend] at step
    change Realize M.sets φ (extend a (extend p (extend y params))) at step
    rw [same] at hp step
    exact ⟨hp, hyM, step⟩
  · intro trace
    let B := ZFSet.sUnion (ZFSet.sUnion f)
    have hB : B ∈ M.sets := M.union_mem unions (M.union_mem unions hf)
    have func : ZFSet.IsFunc A B f := trace.1.to_isFunc
    have mem3 : ∀ i, extend B (extend A (extend f params)) i ∈ M.sets :=
      Fin.cases hB (Fin.cases hA (Fin.cases hf members))
    refine ⟨B, hB, (BoundedFormula.realize_toFormula M _ _ mem3).2
      ((BoundedFormula.truth_functionFormula 1 0 2 _).2 func), ?_⟩
    intro a haM
    apply (realize_imp M.sets _ _ _).2
    intro ha y hyM
    apply (realize_imp M.sets _ _ _).2
    intro _
    apply (realize_imp M.sets _ _ _).2
    intro pairCode
    have mem5 : ∀ i, extend y (extend a (extend B (extend A (extend f params)))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases haM mem3)
    have ay := (BoundedFormula.truth_pairMembershipFormula 1 0 4 _).1
      ((BoundedFormula.realize_toFormula M _ _ mem5).1 pairCode)
    obtain ⟨hp, _, step⟩ := trace.2 a ha y ay
    apply (realize_ex M.sets _ _).2
    refine ⟨graphRestriction a f, hp,
      (M.realize_graphRestrictionFormula 0 2 3 5 _ (Fin.cases hp mem5)).2
        (graphRestriction_eq_sep func), ?_⟩
    rw [realize_reindex, map_extend, map_extend, map_extend]
    exact step

theorem realize_ordinalSuccessorTraceFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {a f : ZFSet.{u}}
    (ha : a ∈ M.sets) (hf : f ∈ M.sets) :
    Realize M.sets (ordinalSuccessorTraceFormula φ) (extend a (extend f params)) ↔
      OrdinalRecursionTrace (groundRecursionStep M φ params) (insert a a) f := by
  rw [ordinalSuccessorTraceFormula, realize_ex]
  constructor
  · rintro ⟨A, hA, successor, trace⟩
    have eq := (BoundedFormula.truth_successorFormula 0 1 _).1
      ((BoundedFormula.realize_toFormula M _ _
        (Fin.cases hA (Fin.cases ha (Fin.cases hf members)))).1 successor)
    rw [realize_reindex, map_extend, map_extend] at trace
    change Realize M.sets (ordinalRecursionTraceFormula φ) (extend A (extend f params)) at trace
    have code := (M.realize_ordinalRecursionTraceFormula unions φ params members hA hf).1 trace
    exact eq ▸ code
  · intro trace
    have hA := M.insert_mem pairing unions ha ha
    refine ⟨insert a a, hA, (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hA (Fin.cases ha (Fin.cases hf members)))).2
        ((BoundedFormula.truth_successorFormula 0 1 _).2 rfl), ?_⟩
    rw [realize_reindex, map_extend, map_extend]
    exact (M.realize_ordinalRecursionTraceFormula unions φ params members hA hf).2 trace

end TransitiveGround





end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundIntervalRecursion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem collect_ordinalSuccessorTraces
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (traces : ∀ β ∈ A, ∃ f ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M φ params) (insert β β) f) :
    ∃ family ∈ M.sets,
      (∀ f ∈ family, ∃ β ∈ A,
        OrdinalRecursionTrace (groundRecursionStep M φ params) (insert β β) f) ∧
      ∀ β ∈ A, ∃ f ∈ family,
        OrdinalRecursionTrace (groundRecursionStep M φ params) (insert β β) f := by
  have witnesses : ∀ β ∈ A, ∃ f ∈ M.sets,
      Realize M.sets (ordinalSuccessorTraceFormula φ) (extend β (extend f params)) := by
    intro β hβ
    obtain ⟨f, hf, trace⟩ := traces β hβ
    exact ⟨f, hf, (M.realize_ordinalSuccessorTraceFormula pairing unions φ params
      members (M.transitive hA hβ) hf).2 trace⟩
  obtain ⟨W, hW, covers⟩ := M.collection_witness collection (ordinalSuccessorTraceFormula φ)
    params members hA witnesses
  let family := ZFSet.sep (fun f => Realize M.sets
    (relationImageFormula (ordinalSuccessorTraceFormula φ)) (extend f (extend A params))) W
  have hFamily : family ∈ M.sets := M.separation_mem separation
    (relationImageFormula (ordinalSuccessorTraceFormula φ)) (extend A params)
    (Fin.cases hA members) hW
  refine ⟨family, hFamily, ?_, ?_⟩
  · intro f hf
    obtain ⟨hfW, selected⟩ := ZFSet.mem_sep.1 hf
    obtain ⟨β, hβ, relation⟩ := (M.realize_relationImageFormula
      (ordinalSuccessorTraceFormula φ) params A f hA).1 selected
    exact ⟨β, hβ, (M.realize_ordinalSuccessorTraceFormula pairing unions φ params
      members (M.transitive hA hβ) (M.transitive hW hfW)).1 relation⟩
  · intro β hβ
    obtain ⟨f, hfW, relation⟩ := covers β hβ
    have selected := (M.realize_relationImageFormula (ordinalSuccessorTraceFormula φ)
      params A f hA).2 ⟨β, hβ, relation⟩
    exact ⟨f, ZFSet.mem_sep.2 ⟨hfW, selected⟩,
      (M.realize_ordinalSuccessorTraceFormula pairing unions φ params members
        (M.transitive hA hβ) (M.transitive hW hfW)).1 relation⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem groundRecursionStep_unique_on_traces {T : ZFSet.{u}} {k : Nat}
    {φ : SetFormula (k + 3)} {params : Fin k → ZFSet.{u}}
    (step : GroundOrdinalStepClosure M T φ params) :
    ∀ α ∈ T, ∀ p, OrdinalRecursionTrace (groundRecursionStep M φ params) α p →
      ∀ y z, groundRecursionStep M φ params α p y →
        groundRecursionStep M φ params α p z → y = z := by
  intro α hα p trace y z first second
  obtain ⟨w, _, _, unique⟩ := step α hα p first.1 trace
  exact (unique y first.2.1 first.2.2).trans (unique z second.2.1 second.2.2).symm

theorem exists_ordinalRecursionTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (ordinal : ordinalSetProperty T)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets)
    (step : GroundOrdinalStepClosure M T φ params) :
    ∃ f ∈ M.sets, OrdinalRecursionTrace (groundRecursionStep M φ params) T f := by
  have unique := M.groundRecursionStep_unique_on_traces step
  have successors : ∀ α ∈ T, ∃ f ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M φ params) (insert α α) f := by
    intro α
    induction α using ZFSet.inductionOn with
    | h α ih =>
      intro hα
      have hαM := M.transitive hT hα
      have ordinalα := ordinalSetProperty_member ordinal hα
      have subsetα : α ⊆ T := fun β hβ => ordinal.1 α hα β hβ
      obtain ⟨family, hFamily, traces, covers⟩ := M.collect_ordinalSuccessorTraces pairing unions
        separation collection φ params members hαM
        (fun β hβ => ih β hβ (subsetα hβ))
      have prefixTrace := OrdinalRecursionTrace.sUnion_successors ordinalα subsetα unique traces covers
      have hPrefix := M.union_mem unions hFamily
      obtain ⟨y, hy, relation, _⟩ := step α hα family.sUnion hPrefix prefixTrace
      exact ⟨insert (ZFSet.pair α y) family.sUnion,
        M.insert_mem pairing unions (M.orderedPair_mem pairing hαM hy) hPrefix,
        prefixTrace.succ ordinalα ⟨hPrefix, hy, relation⟩⟩
  obtain ⟨family, hFamily, traces, covers⟩ := M.collect_ordinalSuccessorTraces pairing unions
    separation collection φ params members hT successors
  exact ⟨family.sUnion, M.union_mem unions hFamily,
    OrdinalRecursionTrace.sUnion_successors ordinal (fun _ hx => hx) unique traces covers⟩

theorem ordinalRecursionTrace_entry {T f : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    {k : Nat} {φ : SetFormula (k + 3)} {params : Fin k → ZFSet.{u}}
    (step : GroundOrdinalStepClosure M T φ params)
    (trace : OrdinalRecursionTrace (groundRecursionStep M φ params) T f) :
    ∀ α ∈ T, ∀ y ∈ M.sets, ZFSet.pair α y ∈ f ↔
      Realize M.sets φ (extend α (extend (graphRestriction α f) (extend y params))) := by
  intro α hα y hy
  constructor
  · intro entry
    exact (trace.2 α hα y entry).2.2
  · intro relation
    obtain ⟨w, entry⟩ := trace.1.total hα
    have stepW := trace.2 α hα w entry
    have prefixTrace := trace.restrict (ordinalSetProperty_member ordinal hα)
      (fun β hβ => ordinal.1 α hα β hβ)
    have equal := M.groundRecursionStep_unique_on_traces step α hα _ prefixTrace y w
      ⟨stepW.1, hy, relation⟩ stepW
    rw [equal]
    exact entry

theorem exists_unique_ordinalRecursionTrace
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (ordinal : ordinalSetProperty T)
    {k : Nat} (φ : SetFormula (k + 3)) (params : Fin k → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets)
    (step : GroundOrdinalStepClosure M T φ params) :
    ∃ f ∈ M.sets, OrdinalRecursionTrace (groundRecursionStep M φ params) T f ∧
      (∀ g, OrdinalRecursionTrace (groundRecursionStep M φ params) T g → g = f) ∧
      ∀ α ∈ T, ∀ y ∈ M.sets, ZFSet.pair α y ∈ f ↔
        Realize M.sets φ (extend α (extend (graphRestriction α f) (extend y params))) := by
  obtain ⟨f, hf, trace⟩ := M.exists_ordinalRecursionTrace pairing unions separation collection
    hT ordinal φ params members step
  exact ⟨f, hf, trace, fun g other => other.unique trace ordinal (fun _ hx => hx)
    (M.groundRecursionStep_unique_on_traces step), M.ordinalRecursionTrace_entry ordinal step trace⟩

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCumulativeHierarchyLevels
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_cumulativeNext (a p x : ZFSet.{u}) :
    x ∈ M.cumulativeNext a p ↔
      x ∈ M.sets ∧ ∃ b ∈ a, ∃ v, ZFSet.pair b v ∈ p ∧ x ⊆ v := by
  rw [cumulativeNext, ZFSet.mem_sep, M.mem_groundPower]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hx, b, hb, v, entry, subset⟩
    exact ⟨⟨hx, fun z hz => ZFSet.mem_sUnion.2
      ⟨v, pair_second_mem_doubleUnion entry, subset hz⟩⟩, b, hb, v, entry, subset⟩

theorem realize_cumulativeMemberFormula {n} (x a p : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeMemberFormula x a p) env ↔
      ∃ b ∈ env a, ∃ v, ZFSet.pair b v ∈ env p ∧ env x ⊆ v := by
  simp only [cumulativeMemberFormula, realize_ex, Realize]
  constructor
  · rintro ⟨b, hbM, hb, v, hvM, pairCode, subsetCode⟩
    have mem2 : ∀ i, extend v (extend b env) i ∈ M.sets :=
      Fin.cases hvM (Fin.cases hbM members)
    exact ⟨b, hb, v,
      (BoundedFormula.truth_pairMembershipFormula 1 0 p.succ.succ _).1
        ((BoundedFormula.realize_toFormula M _ _ mem2).1 pairCode),
      (BoundedFormula.truth_subsetFormula x.succ.succ 0 _).1
        ((BoundedFormula.realize_toFormula M _ _ mem2).1 subsetCode)⟩
  · rintro ⟨b, hb, v, entry, subset⟩
    have hbM := M.transitive (members a) hb
    have hvM : v ∈ M.sets := M.transitive
      (M.transitive (M.transitive (members p) entry)
        (ZFSet.mem_pair.2 (Or.inr rfl))) (ZFSet.mem_pair.2 (Or.inr rfl))
    have mem2 : ∀ i, extend v (extend b env) i ∈ M.sets :=
      Fin.cases hvM (Fin.cases hbM members)
    exact ⟨b, hbM, hb, v, hvM,
      (BoundedFormula.realize_toFormula M _ _ mem2).2
        ((BoundedFormula.truth_pairMembershipFormula 1 0 p.succ.succ _).2 entry),
      (BoundedFormula.realize_toFormula M _ _ mem2).2
        ((BoundedFormula.truth_subsetFormula x.succ.succ 0 _).2 subset)⟩

theorem cumulativeNext_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets)
    {a p : ZFSet.{u}} (ha : a ∈ M.sets) (hp : p ∈ M.sets) :
    M.cumulativeNext a p ∈ M.sets := by
  let params := extend a (extend p Fin.elim0)
  have members : ∀ i, params i ∈ M.sets := Fin.cases ha (Fin.cases hp (fun i => Fin.elim0 i))
  have hBound := M.groundPower_mem powers
    (M.union_mem unions (M.union_mem unions (M.union_mem unions hp)))
  have selected := M.separation_mem separation (cumulativeMemberFormula 0 1 2)
    params members hBound
  have equal : ZFSet.sep (fun x => Realize M.sets (cumulativeMemberFormula 0 1 2)
      (extend x params)) (M.groundPower (⋃₀ ⋃₀ ⋃₀ p)) = M.cumulativeNext a p := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, cumulativeNext, ZFSet.mem_sep]
    constructor
    · rintro ⟨hx, code⟩
      exact ⟨hx, (M.realize_cumulativeMemberFormula 0 1 2 _
        (Fin.cases (M.transitive hBound hx) members)).1 code⟩
    · rintro ⟨hx, witness⟩
      exact ⟨hx, (M.realize_cumulativeMemberFormula 0 1 2 _
        (Fin.cases (M.transitive hBound hx) members)).2 witness⟩
  exact equal ▸ selected

theorem realize_cumulativeStepFormula {a p y : ZFSet.{u}}
    (ha : a ∈ M.sets) (hp : p ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets cumulativeStepFormula (extend a (extend p (extend y Fin.elim0))) ↔
      y = M.cumulativeNext a p := by
  simp only [cumulativeStepFormula, realize_imp, Realize]
  have decode (x : ZFSet.{u}) (hx : x ∈ M.sets) :=
    M.realize_cumulativeMemberFormula 0 1 2
      (extend x (extend a (extend p (extend y Fin.elim0))))
      (Fin.cases hx (Fin.cases ha (Fin.cases hp (Fin.cases hy (fun i => Fin.elim0 i)))))
  constructor
  · intro property
    apply ZFSet.ext
    intro x
    rw [M.mem_cumulativeNext]
    constructor
    · intro hx
      have hxM := M.transitive hy hx
      exact ⟨hxM, (decode x hxM).1 ((property x hxM).1 hx)⟩
    · rintro ⟨hx, witness⟩
      exact (property x hx).2 ((decode x hx).2 witness)
  · intro equal x hx
    constructor
    · intro member
      exact (decode x hx).2 ((M.mem_cumulativeNext a p x).1 (equal ▸ member)).2
    · intro witness
      exact equal ▸ (M.mem_cumulativeNext a p x).2 ⟨hx, (decode x hx).1 witness⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCumulativeHierarchyCode
variable {M : TransitiveGround.{u}} {T H : ZFSet.{u}}

theorem function (code : GroundCumulativeHierarchyCode M T H) : FunctionGraphOn T H := code.1

theorem entry_iff (code : GroundCumulativeHierarchyCode M T H)
    {a v : ZFSet.{u}} (ha : a ∈ T) (entry : ZFSet.pair a v ∈ H) (x : ZFSet.{u}) :
    x ∈ v ↔ x ∈ M.sets ∧ ∃ b ∈ a, ∃ w, ZFSet.pair b w ∈ H ∧ x ⊆ w := by
  rw [code.2 a ha v entry, M.mem_cumulativeNext]
  constructor
  · rintro ⟨hx, b, hb, w, edge, subset⟩
    exact ⟨hx, b, hb, w, (pair_mem_graphRestriction.1 edge).1, subset⟩
  · rintro ⟨hx, b, hb, w, edge, subset⟩
    exact ⟨hx, b, hb, w, pair_mem_graphRestriction.2 ⟨edge, hb⟩, subset⟩

theorem unique (code : GroundCumulativeHierarchyCode M T H)
    {J : ZFSet.{u}} (other : GroundCumulativeHierarchyCode M T J)
    (ordinal : ordinalSetProperty T) : H = J :=
  OrdinalRecursionTrace.unique code other ordinal (fun _ hx => hx)
    (fun _ _ _ _ _ _ first second => first.trans second.symm)

end GroundCumulativeHierarchyCode

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundCumulativeHierarchy
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (ordinal : ordinalSetProperty T) :
    ∃ H ∈ M.sets, GroundCumulativeHierarchyCode M T H ∧
      ∀ J, GroundCumulativeHierarchyCode M T J → J = H := by
  have closure : GroundOrdinalStepClosure M T cumulativeStepFormula Fin.elim0 := by
    intro a ha p hp _
    have haM := M.transitive hT ha
    have hy := M.cumulativeNext_mem unions powers separation haM hp
    refine ⟨M.cumulativeNext a p, hy,
      (M.realize_cumulativeStepFormula haM hp hy).2 rfl, ?_⟩
    intro z hz relation
    exact (M.realize_cumulativeStepFormula haM hp hz).1 relation
  obtain ⟨H, hH, trace, _, _⟩ := M.exists_unique_ordinalRecursionTrace
    pairing unions separation collection hT ordinal cumulativeStepFormula Fin.elim0
    (fun i => Fin.elim0 i) closure
  have code : GroundCumulativeHierarchyCode M T H := by
    refine ⟨trace.1, ?_⟩
    intro a ha v entry
    have step := trace.2 a ha v entry
    exact (M.realize_cumulativeStepFormula (M.transitive hT ha) step.1 step.2.1).1 step.2.2
  exact ⟨H, hH, code, fun J other => other.unique code ordinal⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundCumulativeHierarchyCode
open SetRealization
open scoped ZFSet
universe u
variable {M : TransitiveGround.{u}} {T H : ZFSet.{u}}
variable (code : GroundCumulativeHierarchyCode M T H) (ordinal : ordinalSetProperty T)
include code ordinal

theorem mem_iff_rank_lt {a v : ZFSet.{u}} (ha : a ∈ T)
    (entry : ZFSet.pair a v ∈ H) (x : ZFSet.{u}) :
    x ∈ v ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank a := by
  have all : ∀ a ∈ T, ∀ v, ZFSet.pair a v ∈ H → ∀ x,
      x ∈ v ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank a := by
    intro a
    induction a using ZFSet.inductionOn with
    | h a ih =>
      intro ha v entry x
      rw [code.entry_iff ha entry x]
      constructor
      · rintro ⟨hx, b, hb, w, edge, subset⟩
        have hbT := ordinal.1 a ha b hb
        have rankLe : ZFSet.rank x ≤ ZFSet.rank b := ZFSet.rank_le_iff.2
          (fun z hz => ((ih b hb hbT w edge z).1 (subset hz)).2)
        exact ⟨hx, rankLe.trans_lt (ZFSet.rank_lt_of_mem hb)⟩
      · rintro ⟨hx, rankLt⟩
        let b := ordinalCode (ZFSet.rank x)
        have hb : b ∈ a := by
          rw [ordinalSetProperty_eq_code_rank a (ordinalSetProperty_member ordinal ha)]
          exact (mem_ordinalCode_iff _ _).2 rankLt
        have hbT := ordinal.1 a ha b hb
        obtain ⟨w, edge⟩ := code.function.total hbT
        refine ⟨hx, b, hb, w, edge, ?_⟩
        intro z hz
        apply (ih b hb hbT w edge z).2
        refine ⟨M.transitive hx hz, ?_⟩
        simpa only [b, rank_ordinalCode] using ZFSet.rank_lt_of_mem hz
  exact all a ha v entry x

theorem value_transitive {a v : ZFSet.{u}} (ha : a ∈ T)
    (entry : ZFSet.pair a v ∈ H) : setTransitive v := by
  intro x hx z hz
  obtain ⟨hxM, rankX⟩ := (code.mem_iff_rank_lt ordinal ha entry x).1 hx
  exact (code.mem_iff_rank_lt ordinal ha entry z).2
    ⟨M.transitive hxM hz, (ZFSet.rank_lt_of_mem hz).trans rankX⟩

theorem value_rank {a v : ZFSet.{u}} (ha : a ∈ T)
    (entry : ZFSet.pair a v ∈ H) (haM : a ∈ M.sets) : ZFSet.rank v = ZFSet.rank a := by
  apply le_antisymm
  · exact ZFSet.rank_le_iff.2 (fun x hx => ((code.mem_iff_rank_lt ordinal ha entry x).1 hx).2)
  · apply ZFSet.rank_le_iff.2
    intro b hb
    exact ZFSet.rank_lt_of_mem ((code.mem_iff_rank_lt ordinal ha entry b).2
      ⟨M.transitive haM hb, ZFSet.rank_lt_of_mem hb⟩)

end PartitionPilot.Forcing.GroundCumulativeHierarchyCode

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCumulativeHierarchyCode
variable {M : TransitiveGround.{u}} {T H : ZFSet.{u}}

theorem value_mem (_code : GroundCumulativeHierarchyCode M T H)
    (hH : H ∈ M.sets) {a v : ZFSet.{u}} (entry : ZFSet.pair a v ∈ H) : v ∈ M.sets :=
  M.pair_right (M.transitive hH entry)

theorem ground_trace_iff
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (hT : T ∈ M.sets) (hH : H ∈ M.sets) :
    OrdinalRecursionTrace (groundRecursionStep M cumulativeStepFormula Fin.elim0) T H ↔
      GroundCumulativeHierarchyCode M T H := by
  constructor
  · intro trace
    refine ⟨trace.1, ?_⟩
    intro a ha v entry
    have step := trace.2 a ha v entry
    exact (M.realize_cumulativeStepFormula (M.transitive hT ha) step.1 step.2.1).1 step.2.2
  · intro code
    refine ⟨code.1, ?_⟩
    intro a ha v entry
    have haM := M.transitive hT ha
    have hp := M.graphRestriction_mem unions separation haM hH
    have hv := code.value_mem hH entry
    exact ⟨hp, hv, (M.realize_cumulativeStepFormula haM hp hv).2 (code.2 a ha v entry)⟩

end GroundCumulativeHierarchyCode

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundCumulativeLevel
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {a : ZFSet.{u}} (ha : a ∈ M.sets) (ordinal : ordinalSetProperty a) :
    ∃ H ∈ M.sets, ∃ V ∈ M.sets,
      GroundCumulativeHierarchyCode M (insert a a) H ∧ ZFSet.pair a V ∈ H ∧
      (∀ x, x ∈ V ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank a) ∧
      setTransitive V ∧ ZFSet.rank V = ZFSet.rank a := by
  have hs := M.insert_mem pairing unions ha ha
  have ordinalS := ordinalSetProperty_succ ordinal
  obtain ⟨H, hH, code, _⟩ := M.exists_groundCumulativeHierarchy pairing unions powers
    separation collection hs ordinalS
  obtain ⟨V, entry⟩ := code.function.total (ZFSet.mem_insert a a)
  exact ⟨H, hH, V, code.value_mem hH entry, code, entry,
    code.mem_iff_rank_lt ordinalS (ZFSet.mem_insert a a) entry,
    code.value_transitive ordinalS (ZFSet.mem_insert a a) entry,
    code.value_rank ordinalS (ZFSet.mem_insert a a) entry ha⟩

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRegularFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_cumulativeLevelFormula_iff_graph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n} (a v : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeLevelFormula a v) env ↔
      ∃ H ∈ M.sets, GroundCumulativeHierarchyCode M (insert (env a) (env a)) H ∧
        ZFSet.pair (env a) (env v) ∈ H := by
  rw [cumulativeLevelFormula, realize_ex]
  have hS := M.insert_mem pairing unions (members a) (members a)
  constructor
  · rintro ⟨H, hH, trace, entry⟩
    rw [realize_reindex, map_extend, map_extend] at trace
    have empty : (fun i : Fin 0 => extend H env (Fin.elim0 i)) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    rw [empty] at trace
    have code := (M.realize_ordinalSuccessorTraceFormula pairing unions cumulativeStepFormula
      Fin.elim0 (fun i => Fin.elim0 i) (members a) hH).1 trace
    exact ⟨H, hH, (GroundCumulativeHierarchyCode.ground_trace_iff unions separation hS hH).1 code,
      (BoundedFormula.truth_pairMembershipFormula a.succ v.succ 0 _).1
        ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hH members)).1 entry)⟩
  · rintro ⟨H, hH, code, entry⟩
    refine ⟨H, hH, ?_, (BoundedFormula.realize_toFormula M _ _ (Fin.cases hH members)).2
      ((BoundedFormula.truth_pairMembershipFormula a.succ v.succ 0 _).2 entry)⟩
    rw [realize_reindex, map_extend, map_extend]
    have empty : (fun i : Fin 0 => extend H env (Fin.elim0 i)) = Fin.elim0 :=
      funext (fun i => Fin.elim0 i)
    rw [empty]
    exact (M.realize_ordinalSuccessorTraceFormula pairing unions cumulativeStepFormula
      Fin.elim0 (fun i => Fin.elim0 i) (members a) hH).2
        ((GroundCumulativeHierarchyCode.ground_trace_iff unions separation hS hH).2 code)

theorem realize_cumulativeLevelFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n} (a v : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (ordinal : ordinalSetProperty (env a)) :
    Realize M.sets (cumulativeLevelFormula a v) env ↔
      ∀ x, x ∈ env v ↔ x ∈ M.sets ∧ ZFSet.rank x < ZFSet.rank (env a) := by
  rw [M.realize_cumulativeLevelFormula_iff_graph pairing unions separation a v env members]
  constructor
  · rintro ⟨H, _, code, entry⟩
    exact code.mem_iff_rank_lt (ordinalSetProperty_succ ordinal) (ZFSet.mem_insert _ _) entry
  · intro property
    obtain ⟨H, hH, V, _, code, entry, exactV, _, _⟩ := M.exists_groundCumulativeLevel
      pairing unions powers separation collection (members a) ordinal
    have equal : env v = V := ZFSet.ext (fun x => (property x).trans (exactV x).symm)
    exact ⟨H, hH, code, equal ▸ entry⟩

theorem realize_cumulativeRankLtFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {n} (x a : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (ordinal : ordinalSetProperty (env a)) :
    Realize M.sets (cumulativeRankLtFormula x a) env ↔
      ZFSet.rank (env x) < ZFSet.rank (env a) := by
  rw [cumulativeRankLtFormula, realize_ex]
  constructor
  · rintro ⟨V, hV, level, member⟩
    have exactV := (M.realize_cumulativeLevelFormula pairing unions powers separation collection
      a.succ 0 (extend V env) (Fin.cases hV members) ordinal).1 level
    exact ((exactV (env x)).1 member).2
  · intro bound
    obtain ⟨_, _, V, hV, _, _, exactV, _, _⟩ := M.exists_groundCumulativeLevel
      pairing unions powers separation collection (members a) ordinal
    exact ⟨V, hV, (M.realize_cumulativeLevelFormula pairing unions powers separation collection
      a.succ 0 (extend V env) (Fin.cases hV members) ordinal).2 exactV,
      (exactV (env x)).2 ⟨members x, bound⟩⟩

end TransitiveGround

end

section
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_cumulativeRankValueFormula {n} (x b : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (cumulativeRankValueFormula x b) env ↔
      env b = ordinalCode (ZFSet.rank (env x)) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula b).toFormula env ∧
    Realize M.sets (ex _) env) ↔ _
  rw [BoundedFormula.realize_ordinalFormula M b env members, ← ordinalSetProperty_iff,
    realize_ex]
  constructor
  · rintro ⟨ordinal, s, hs, successor, first, second⟩
    have eqS := (BoundedFormula.truth_successorFormula 0 b.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hs members)).1 successor)
    change s = insert (env b) (env b) at eqS
    have ordinalS : ordinalSetProperty s := eqS ▸ ordinalSetProperty_succ ordinal
    have upper := (M.realize_cumulativeRankLtFormula pairing unions powers separation collection
      x.succ 0 (extend s env) (Fin.cases hs members) ordinalS).1 first
    change ZFSet.rank (env x) < ZFSet.rank s at upper
    have lower : ¬ ZFSet.rank (env x) < ZFSet.rank (env b) := by
      intro less
      exact second ((M.realize_cumulativeRankLtFormula pairing unions powers separation collection
        x.succ b.succ (extend s env) (Fin.cases hs members) ordinal).2 less)
    have rankS : ZFSet.rank s = Order.succ (ZFSet.rank (env b)) := by
      rw [eqS, ZFSet.rank_insert, max_eq_left (Order.le_succ _)]
    rw [rankS, Order.lt_succ_iff] at upper
    have equal := le_antisymm upper (le_of_not_gt lower)
    exact (ordinalSetProperty_eq_code_rank (env b) ordinal).trans (congrArg ordinalCode equal.symm)
  · intro equal
    have ordinal : ordinalSetProperty (env b) := equal ▸ ordinalSetProperty_ordinalCode _
    have hs := M.insert_mem pairing unions (members b) (members b)
    have mem2 : ∀ i, extend (insert (env b) (env b)) env i ∈ M.sets := Fin.cases hs members
    have ranks : ZFSet.rank (env b) = ZFSet.rank (env x) := by rw [equal, rank_ordinalCode]
    refine ⟨ordinal, insert (env b) (env b), hs,
      (BoundedFormula.realize_toFormula M _ _ mem2).2
        ((BoundedFormula.truth_successorFormula 0 b.succ _).2 rfl), ?_, ?_⟩
    · apply (M.realize_cumulativeRankLtFormula pairing unions powers separation collection
        x.succ 0 _ mem2 (ordinalSetProperty_succ ordinal)).2
      change ZFSet.rank (env x) < ZFSet.rank (insert (env b) (env b))
      rw [ZFSet.rank_insert, max_eq_left (Order.le_succ _), ranks]
      exact Order.lt_succ _
    · intro property
      have less := (M.realize_cumulativeRankLtFormula pairing unions powers separation collection
        x.succ b.succ _ mem2 ordinal).1 property
      exact (lt_irrefl (ZFSet.rank (env x))) (ranks ▸ less)

end TransitiveGround

end

open SetFormula SetRealization
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundChoiceEnumerationSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem mem_enumerationRemainder (A a p x : ZFSet.{u}) :
    x ∈ enumerationRemainder A a p ↔ x ∈ A ∧ ¬ ∃ b ∈ a, ZFSet.pair b x ∈ p :=
  ZFSet.mem_sep

namespace BoundedFormula

theorem truth_enumerationRemainderFormula {n} (R A a p : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (enumerationRemainderFormula R A a p) env ↔
      env R = enumerationRemainder (env A) (env a) (env p) := by
  simp only [enumerationRemainderFormula, Truth, truth_imp, truth_exMem,
    truth_pairMembershipFormula, ← iff_def]
  change ((∀ x ∈ env R, x ∈ env A) ∧ ∀ x ∈ env A,
    x ∈ env R ↔ ¬ ∃ b ∈ env a, ZFSet.pair b x ∈ env p) ↔ _
  constructor
  · rintro ⟨subset, spec⟩
    apply ZFSet.ext
    intro x
    rw [mem_enumerationRemainder]
    exact ⟨fun hx => ⟨subset x hx, (spec x (subset x hx)).1 hx⟩,
      fun ⟨hx, unused⟩ => (spec x hx).2 unused⟩
  · intro equal
    rw [equal]
    exact ⟨fun _ hx => (mem_enumerationRemainder _ _ _ _).1 hx |>.1,
      fun x hx => by rw [mem_enumerationRemainder]; exact and_iff_right hx⟩

theorem truth_choiceEnumerationStepFormula {n} (A F c a p y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (choiceEnumerationStepFormula A F c a p y) env ↔
      ChoiceEnumerationStep (env A) (env F) (env c) (env a) (env p) (env y) := by
  simp only [choiceEnumerationStepFormula, truth_disj, truth_exMem, Truth,
    truth_enumerationRemainderFormula, truth_pairMembershipFormula]
  change ((∃ R ∈ env F, R = enumerationRemainder (env A) (env a) (env p) ∧
    ZFSet.pair R (env y) ∈ env c) ∨
    (¬ (∃ x ∈ env A, ¬ ∃ b ∈ env a, ZFSet.pair b x ∈ env p) ∧ env y = env A)) ↔ _
  have nonempty : (enumerationRemainder (env A) (env a) (env p)).Nonempty ↔
      ∃ x ∈ env A, ¬ ∃ b ∈ env a, ZFSet.pair b x ∈ env p := by
    change (∃ x, x ∈ enumerationRemainder (env A) (env a) (env p)) ↔ _
    simp only [mem_enumerationRemainder]
  simp only [ChoiceEnumerationStep, nonempty]

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem enumerationRemainder_mem (separation : SeparationSchema M.sets)
    {A a p : ZFSet.{u}} (hA : A ∈ M.sets) (ha : a ∈ M.sets) (hp : p ∈ M.sets) :
    enumerationRemainder A a p ∈ M.sets := by
  let formula : BoundedFormula 3 := .neg (BoundedFormula.exMem 1
    (BoundedFormula.pairMembershipFormula 0 1 3))
  let params := extend a (extend p Fin.elim0)
  have ground := M.bounded_separation_mem separation formula params
    (Fin.cases ha (Fin.cases hp (fun i => Fin.elim0 i))) hA
  have equal : ZFSet.sep (fun x => BoundedFormula.Truth formula (extend x params)) A =
      enumerationRemainder A a p := by
    apply ZFSet.ext
    intro x
    simp only [ZFSet.mem_sep, enumerationRemainder, formula, BoundedFormula.Truth,
      BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ ground

theorem choiceEnumerationStep_exists_unique (separation : SeparationSchema M.sets)
    {A c a p : ZFSet.{u}} (hA : A ∈ M.sets) (ha : a ∈ M.sets) (hp : p ∈ M.sets)
    (code : ChoiceFunctionCode (M.nonemptyGroundSubsets A) c) :
    ∃ y ∈ M.sets, ChoiceEnumerationStep A (M.nonemptyGroundSubsets A) c a p y ∧
      ∀ z, ChoiceEnumerationStep A (M.nonemptyGroundSubsets A) c a p z → z = y := by
  classical
  let R := enumerationRemainder A a p
  have hR := M.enumerationRemainder_mem separation hA ha hp
  have subset : R ⊆ A := fun _ hx => (mem_enumerationRemainder _ _ _ _).1 hx |>.1
  by_cases nonempty : R.Nonempty
  · have member := (M.mem_nonemptyGroundSubsets A R).2 ⟨hR, subset, nonempty⟩
    obtain ⟨y, entry, unique⟩ := code.function.2 R member
    have hy := code.chosen R y entry
    refine ⟨y, M.transitive hA (subset hy), Or.inl ⟨R, member, rfl, entry⟩, ?_⟩
    intro z step
    rcases step with ⟨S, _, rfl, selected⟩ | ⟨empty, _⟩
    · exact unique z selected
    · exact False.elim (empty nonempty)
  · refine ⟨A, hA, Or.inr ⟨nonempty, rfl⟩, ?_⟩
    intro z step
    rcases step with ⟨S, member, rfl, _⟩ | ⟨_, equal⟩
    · exact False.elim (nonempty ((M.mem_nonemptyGroundSubsets A _).1 member).2.2)
    · exact equal

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOrdinalEnumerationFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem choiceEnumerationStep_fresh {A F c a p y : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (step : ChoiceEnumerationStep A F c a p y)
    (nonempty : (enumerationRemainder A a p).Nonempty) :
    y ∈ enumerationRemainder A a p := by
  rcases step with ⟨R, _, rfl, entry⟩ | ⟨empty, _⟩
  · exact choice.chosen _ _ entry
  · exact False.elim (empty nonempty)

theorem choiceEnumerationTrace_injection {A F c T f : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty T)
    (trace : OrdinalRecursionTrace (ChoiceEnumerationStep A F c) T f)
    (unused : ∀ a ∈ T, (enumerationRemainder A a (graphRestriction a f)).Nonempty) :
    InjectionCode T A f := by
  have fresh : ∀ a ∈ T, ∀ y, ZFSet.pair a y ∈ f →
      y ∈ A ∧ ¬ ∃ b ∈ a, ZFSet.pair b y ∈ f := by
    intro a ha y entry
    have hy := (mem_enumerationRemainder A a (graphRestriction a f) y).1
      (choiceEnumerationStep_fresh choice (trace.2 a ha y entry) (unused a ha))
    exact ⟨hy.1, fun ⟨b, hb, byEntry⟩ =>
      hy.2 ⟨b, hb, pair_mem_graphRestriction.2 ⟨byEntry, hb⟩⟩⟩
  refine ⟨⟨?_, trace.1.to_isFunc.2⟩, ?_⟩
  · intro z hz
    obtain ⟨a, ha, y, rfl⟩ := trace.1.shape z hz
    exact ZFSet.pair_mem_prod.2 ⟨ha, (fresh a ha y hz).1⟩
  · intro a b y first second
    have ha := trace.1.pair_source first
    have hb := trace.1.pair_source second
    rcases ordinalSetProperty_mem_compare ordinal ha hb with before | equal | after
    · exact False.elim ((fresh b hb y second).2 ⟨a, before, first⟩)
    · exact equal
    · exact False.elim ((fresh a ha y first).2 ⟨b, after, second⟩)

theorem exists_first_enumerationExhaustion {A T f : ZFSet.{u}}
    (ordinal : ordinalSetProperty T)
    (exhausted : ∃ a ∈ T, ¬ (enumerationRemainder A a (graphRestriction a f)).Nonempty) :
    ∃ a ∈ T, ¬ (enumerationRemainder A a (graphRestriction a f)).Nonempty ∧
      ∀ b ∈ a, (enumerationRemainder A b (graphRestriction b f)).Nonempty := by
  classical
  obtain ⟨a, ha, exhausted⟩ := exhausted
  induction a using ZFSet.inductionOn with
  | h a ih =>
    by_cases earlier : ∃ b ∈ a, ¬ (enumerationRemainder A b (graphRestriction b f)).Nonempty
    · obtain ⟨b, hb, empty⟩ := earlier
      exact ih b hb (ordinal.1 a ha b hb) empty
    · exact ⟨a, ha, exhausted, fun b hb => by
        by_contra empty
        exact earlier ⟨b, hb, empty⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundOrdinalEnumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ∃ T ∈ M.sets, ∃ f ∈ M.sets, ordinalSetProperty T ∧ InjectionCode T A f ∧
      ∀ x ∈ A, ∃ a ∈ T, ZFSet.pair a x ∈ f := by
  classical
  let F := M.nonemptyGroundSubsets A
  have hF := M.nonemptyGroundSubsets_mem powers separation hA
  obtain ⟨c, hc, chooser⟩ := M.choice_witness choice hF
    (fun R hR => ((M.mem_nonemptyGroundSubsets A R).1 hR).2.2)
  obtain ⟨H, hH, ordinal, _, impossible⟩ := M.exists_groundHartogs
    pairing unions powers separation collection hA
  let params := extend A (extend F (extend c Fin.elim0))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hA (Fin.cases hF (Fin.cases hc (fun i => Fin.elim0 i)))
  let φ : BoundedFormula 6 := BoundedFormula.choiceEnumerationStepFormula 3 4 5 0 1 2
  have recognize (a p y : ZFSet.{u}) (ha : a ∈ M.sets) (hp : p ∈ M.sets)
      (hy : y ∈ M.sets) :
      Realize M.sets φ.toFormula (extend a (extend p (extend y params))) ↔
        ChoiceEnumerationStep A F c a p y :=
    (BoundedFormula.realize_toFormula M φ _
      (Fin.cases ha (Fin.cases hp (Fin.cases hy members)))).trans
      (BoundedFormula.truth_choiceEnumerationStepFormula 3 4 5 0 1 2 _)
  have closure : GroundOrdinalStepClosure M H φ.toFormula params := by
    intro a ha p hp _
    have haM := M.transitive hH ha
    obtain ⟨y, hy, relation, unique⟩ := M.choiceEnumerationStep_exists_unique
      separation hA haM hp chooser
    exact ⟨y, hy, (recognize a p y haM hp hy).2 relation,
      fun z hz step => unique z ((recognize a p z haM hp hz).1 step)⟩
  obtain ⟨f, hf, groundTrace⟩ := M.exists_ordinalRecursionTrace pairing unions separation
    collection hH ordinal φ.toFormula params members closure
  have trace : OrdinalRecursionTrace (ChoiceEnumerationStep A F c) H f := by
    refine ⟨groundTrace.1, ?_⟩
    intro a ha y entry
    have step := groundTrace.2 a ha y entry
    exact (recognize a _ y (M.transitive hH ha) step.1 step.2.1).1 step.2.2
  have exhausted : ∃ a ∈ H,
      ¬ (enumerationRemainder A a (graphRestriction a f)).Nonempty := by
    by_contra none
    apply impossible
    exact ⟨f, hf, choiceEnumerationTrace_injection chooser ordinal trace (fun a ha => by
      by_contra empty
      exact none ⟨a, ha, empty⟩)⟩
  obtain ⟨T, hT, empty, unused⟩ := exists_first_enumerationExhaustion ordinal exhausted
  have ordinalT := ordinalSetProperty_member ordinal hT
  have subset : T ⊆ H := fun a ha => ordinal.1 T hT a ha
  have hTM := M.transitive hH hT
  have restricted := trace.restrict ordinalT subset
  have injection : InjectionCode T A (graphRestriction T f) :=
    choiceEnumerationTrace_injection chooser ordinalT restricted (fun a ha => by
      rw [graphRestriction_restrict (fun b hb => ordinalT.1 a ha b hb)]
      exact unused a ha)
  refine ⟨T, hTM, graphRestriction T f,
    M.graphRestriction_mem unions separation hTM hf, ordinalT, injection, ?_⟩
  intro x hx
  by_contra missing
  apply empty
  refine ⟨x, (mem_enumerationRemainder _ _ _ _).2 ⟨hx, ?_⟩⟩
  exact missing

end TransitiveGround

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundOrdinarySubmodelReflection
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)

theorem mem_ordinaryExtension (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ (M.ordinaryExtension s H).sets ↔
      ∃ τ ∈ (M.nameDomain s).names, Name.eval {q | H.mem q} τ = x :=
  (M.nameDomain s).mem_values {q | H.mem q} x

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProjectedRowChooserWitnesses
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable (s : Presentation P) {G : Type v} [Group G]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

theorem mem_symmetricExtension (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ (M.symmetricExtension s a F H).sets ↔
      ∃ τ ∈ (M.nameDomain s).names, HereditarilySymmetric a s F τ ∧
        Name.eval {q | H.mem q} τ = x :=
  a.mem_symmetric_values s (M.nameDomain s) F {q | H.mem q} x

theorem symmetricExtension_subset_ordinaryExtension (H : ConditionFilter P) :
    (M.symmetricExtension s a F H).sets ⊆ (M.ordinaryExtension s H).sets := by
  intro x hx
  obtain ⟨τ, ground, _, equal⟩ := (M.mem_symmetricExtension s a F H x).1 hx
  exact (M.mem_ordinaryExtension s H x).2 ⟨τ, ground, equal⟩

theorem ground_subset_symmetricExtension [OrderTop P]
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    M.sets ⊆ (M.symmetricExtension s a F H).sets := by
  intro x hx
  exact (M.mem_symmetricExtension s a F H x).2 ⟨Name.check s ⊤ x,
    M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) x hx,
    HereditarilySymmetric.check a s F x, Name.eval_check {q | H.mem q} ⊤ H.top_mem x⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mem_supportedFamilyCodes (K : Subgroup G) (W : ZFSet.{u}) (tau : Name s) :
    tau.val ∈ supportedFamilyCodes a s K W ↔ tau.val ∈ W ∧ K ≤ a.stabilizer s tau := by
  rw [supportedFamilyCodes, ZFSet.mem_sep]
  constructor
  · rintro ⟨member, sigma, equal, fixed⟩
    have same : sigma = tau := Subtype.ext equal
    exact ⟨member, same ▸ fixed⟩
  · rintro ⟨member, fixed⟩
    exact ⟨member, tau, rfl, fixed⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem supportedFamilyCodes_mem (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (i : I) (hi : b.encode i ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z) :
    Name.supportedFamilyCodes a s (K i) W ∈ M.sets := by
  let params := extend (b.encode i) (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0))))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hi (Fin.cases carrier (Fin.cases group (Fin.cases supports
      (Fin.cases maps (fun j => Fin.elim0 j)))))
  have selected := M.separation_mem separation nameSupportFormula params members hW
  have equal : ZFSet.sep (fun z => Realize M.sets nameSupportFormula (extend z params)) W =
      Name.supportedFamilyCodes a s (K i) W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, Name.supportedFamilyCodes, ZFSet.mem_sep]
    apply and_congr_right
    intro member
    let tau : Name s := ⟨z, valid z member⟩
    have meaning : Realize M.sets nameSupportFormula (extend z params) ↔
        K i ≤ a.stabilizer s tau :=
      M.realize_nameSupportFormula a s t b K pairing unions powers separation collection
        carrier group supports maps i hi tau (M.transitive hW member)
    rw [meaning]
    constructor
    · intro fixed
      exact ⟨tau, rfl, fixed⟩
    · rintro ⟨sigma, sigmaCode, fixed⟩
      have same : sigma = tau := Subtype.ext sigmaCode
      exact same ▸ fixed
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable {G : Type v} [Group G]

theorem supportedNameSequence_function_mem
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (carrier : s.carrier ∈ M.sets)
    {I f : ZFSet.{u}} (hI : I ∈ M.sets) (hf : f ∈ M.sets)
    (function : FunctionGraphOn I f) (names : ∀ i, IsName s (function.value i))
    (K : Subgroup G) (support : F.mem K)
    (fixed : ∀ g ∈ K, ∀ i, a.act s g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩)
    (children : ∀ i, HereditarilySymmetric a s F ⟨function.value i, names i⟩)
    (H : ConditionFilter P) :
    let sequence := Name.indexedGraphName ⊤ function names
    sequence.val ∈ M.sets ∧ K ≤ a.stabilizer s sequence ∧
      HereditarilySymmetric a s F sequence ∧
      ZFSet.IsFunc I (ZFSet.range (fun i : I => Name.eval {p | H.mem p} ⟨function.value i, names i⟩))
        (Name.eval {p | H.mem p} sequence) ∧
      Name.eval {p | H.mem p} sequence ∈ (M.symmetricExtension s a F H).sets := by
  let sequence := Name.indexedGraphName ⊤ function names
  have ground := M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) hI hf function names
  have supported : K ≤ a.stabilizer s sequence :=
    Name.indexedTuple_supported a I (fun i => ⟨function.value i, names i⟩) K fixed
  have symmetric : HereditarilySymmetric a s F sequence :=
    Name.indexedTuple_hs a F I (fun i => ⟨function.value i, names i⟩) K support fixed children
  exact ⟨ground, supported, symmetric,
    Name.eval_indexedGraphName_function {p | H.mem p} ⊤ H.top_mem function names,
    (M.mem_symmetricExtension s a F H _).2 ⟨sequence, ground, symmetric, rfl⟩⟩

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundSupportedEqualityChoices
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem pair_mem_ordinalIndexedChoiceGraph (A T e x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ ordinalIndexedChoiceGraph A T e ↔
      x ∈ A ∧ y ∈ x ∧ OrdinalChoiceValue T e x y := by
  rw [ordinalIndexedChoiceGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, y', hy, eq, least⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hx, hy, least⟩
  · rintro ⟨hx, hy, least⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_sUnion.2 ⟨x, hx, hy⟩⟩,
      x, hx, y, hy, rfl, least⟩

theorem ordinalIndexedChoiceGraph_choice {A T e : ZFSet.{u}}
    (ordinal : ordinalSetProperty T) (function : FunctionGraphOn T e)
    (meets : ∀ x ∈ A, ∃ i ∈ T, ∃ y ∈ x, ZFSet.pair i y ∈ e) :
    ChoiceFunctionCode A (ordinalIndexedChoiceGraph A T e) := by
  obtain ⟨B, function⟩ := function
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro x hx
    let indices : Set ZFSet.{u} := {i | i ∈ T ∧ ∃ y ∈ x, ZFSet.pair i y ∈ e}
    have inhabited : indices.Nonempty := by
      obtain ⟨i, hi, y, hy, entry⟩ := meets x hx
      exact ⟨i, hi, y, hy, entry⟩
    obtain ⟨i, hi, minimal⟩ := ZFSet.mem_wf.has_min indices inhabited
    obtain ⟨hiT, y, hy, entry⟩ := hi
    have least : OrdinalChoiceValue T e x y := by
      refine ⟨i, hiT, entry, ?_⟩
      intro j hji z hz rel
      exact minimal j ⟨ordinal.1 i hiT j hji, z, hz, rel⟩ hji
    refine ⟨y, (pair_mem_ordinalIndexedChoiceGraph A T e x y).2 ⟨hx, hy, least⟩, ?_⟩
    intro z hz
    obtain ⟨_, zx, j, hjT, jz, smaller⟩ := (pair_mem_ordinalIndexedChoiceGraph A T e x z).1 hz
    rcases ordinalSetProperty_mem_compare ordinal hiT hjT with before | equal | after
    · exact False.elim (smaller i before y hy entry)
    · subst j
      obtain ⟨v, _, unique⟩ := function.2 i hiT
      exact (unique z jz).trans (unique y entry).symm
    · exact False.elim (minimal j ⟨hjT, z, zx, jz⟩ after)
  · intro x y entry
    exact ((pair_mem_ordinalIndexedChoiceGraph A T e x y).1 entry).2.1

namespace BoundedFormula

theorem truth_ordinalChoiceValueFormula {n} (T e x y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (ordinalChoiceValueFormula T e x y) env ↔
      OrdinalChoiceValue (env T) (env e) (env x) (env y) := by
  simp only [ordinalChoiceValueFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  rfl

theorem truth_ordinalIndexedChoiceEntryFormula {n} (z A T e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (ordinalIndexedChoiceEntryFormula z A T e) env ↔
      ∃ x ∈ env A, ∃ y ∈ x, env z = ZFSet.pair x y ∧ OrdinalChoiceValue (env T) (env e) x y := by
  simp only [ordinalIndexedChoiceEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_ordinalChoiceValueFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem ordinalIndexedChoiceGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A T e : ZFSet.{u}} (hA : A ∈ M.sets) (hT : T ∈ M.sets) (he : e ∈ M.sets) :
    ordinalIndexedChoiceGraph A T e ∈ M.sets := by
  let env := extend A (extend T (extend e Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.ordinalIndexedChoiceEntryFormula 0 1 2 3) env
    (Fin.cases hA (Fin.cases hT (Fin.cases he (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hA (M.union_mem unions hA))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.ordinalIndexedChoiceEntryFormula 0 1 2 3) (extend z env))
      (ZFSet.prod A (⋃₀ A)) = ordinalIndexedChoiceGraph A T e := by
    apply ZFSet.ext
    intro z
    rw [ordinalIndexedChoiceGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_ordinalIndexedChoiceEntryFormula _ _ _ _ _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable {G : Type v} [Group G]

theorem supportedNameFamily_graph_choice
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (carrier : s.carrier ∈ M.sets)
    {W : ZFSet.{u}} (hW : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z)
    (K : Subgroup G) (support : F.mem K)
    (fixed : ∀ psi : Name s, psi.val ∈ W → K ≤ a.stabilizer s psi)
    (children : ∀ psi : Name s, psi.val ∈ W → HereditarilySymmetric a s F psi)
    (H : ConditionFilter P) (zf : ZFRealization (M.symmetricExtension s a F H).sets)
    {delta z : ZFSet.{u}}
    (hDelta : delta ∈ (M.symmetricExtension s a F H).sets)
    (hz : z ∈ (M.symmetricExtension s a F H).sets) (function : FunctionGraphOn delta z)
    (available : ∀ beta ∈ delta, ∃ psi : Name s, psi.val ∈ W ∧
      ∃ A, ZFSet.pair beta A ∈ z ∧ Name.eval {p | H.mem p} psi ∈ A) :
    ∃ f ∈ (M.symmetricExtension s a F H).sets, FunctionGraphOn delta f ∧
      ∀ beta A x, ZFSet.pair beta A ∈ z → ZFSet.pair beta x ∈ f → x ∈ A := by
  let N := M.symmetricExtension s a F H
  have pairingN : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unionsN : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powersN : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  have separationN : SeparationSchema N.sets := zf.2.1
  obtain ⟨T, hT, e, he, ordinal, injection, onto⟩ :=
    M.exists_groundOrdinalEnumeration pairing unions powers separation collection choice hW
  let enumeration : FunctionGraphOn T e := ⟨W, injection.function⟩
  have values : ∀ i, enumeration.value i ∈ W := by
    intro i
    exact (ZFSet.pair_mem_prod.1 (injection.function.1 (enumeration.value_entry i))).2
  have names : ∀ i, IsName s (enumeration.value i) := fun i => valid _ (values i)
  have sequence := M.supportedNameSequence_function_mem s a F pairing unions powers separation
    collection carrier hT he enumeration names K support
    (fun g hg i => fixed ⟨enumeration.value i, names i⟩ (values i) hg)
    (fun i => children ⟨enumeration.value i, names i⟩ (values i)) H
  let E := Name.eval {p | H.mem p} (Name.indexedGraphName ⊤ enumeration names)
  have hE : E ∈ N.sets := sequence.2.2.2.2
  have evalFunction : FunctionGraphOn T E := ⟨_, sequence.2.2.2.1⟩
  have includes := M.ground_subset_symmetricExtension s a F
    pairing unions powers separation collection carrier H
  have hTN : T ∈ N.sets := includes hT
  let B := ⋃₀ ⋃₀ z
  let A := relationImage delta B z
  have hB : B ∈ N.sets := N.union_mem unionsN (N.union_mem unionsN hz)
  have hA : A ∈ N.sets := N.relationImage_mem separationN hDelta hB hz
  have imageEntry {beta Y : ZFSet.{u}} (edge : ZFSet.pair beta Y ∈ z) : Y ∈ A :=
    (mem_relationImage delta B z Y).2
      ⟨pair_second_mem_doubleUnion edge, beta, function.pair_source edge, edge⟩
  have meets : ∀ Y ∈ A, ∃ i ∈ T, ∃ x ∈ Y, ZFSet.pair i x ∈ E := by
    intro Y member
    obtain ⟨_bound, beta, hBeta, edge⟩ := (mem_relationImage delta B z Y).1 member
    obtain ⟨psi, hPsi, Y', otherEdge, memberValue⟩ := available beta hBeta
    have same : Y' = Y := function.unique otherEdge edge
    rw [same] at memberValue
    obtain ⟨i, hi, code⟩ := onto psi.val hPsi
    let j : T.toSet := ⟨i, hi⟩
    have valueEq : enumeration.value j = psi.val := enumeration.value_eq_of_entry j code
    have nameEq : (⟨enumeration.value j, names j⟩ : Name s) = psi := Subtype.ext valueEq
    refine ⟨i, hi, Name.eval {p | H.mem p} psi, memberValue, ?_⟩
    exact (Name.pair_mem_eval_indexedGraphName {p | H.mem p} ⊤ H.top_mem
      enumeration names j _).2 (congrArg (Name.eval {p | H.mem p}) nameEq)
  let c := ordinalIndexedChoiceGraph A T E
  have hc : c ∈ N.sets := N.ordinalIndexedChoiceGraph_mem pairingN unionsN powersN separationN hA hTN hE
  have chooser : ChoiceFunctionCode A c := ordinalIndexedChoiceGraph_choice ordinal evalFunction meets
  let f := relationCompose delta A (⋃₀ A) z c
  have hf : f ∈ N.sets := N.relationCompose_mem pairingN unionsN powersN separationN
    hDelta hA (N.union_mem unionsN hA) hz hc
  have code : ZFSet.IsFunc delta (⋃₀ A) f := by
    refine ⟨fun _ member => (ZFSet.mem_sep.1 member).1, ?_⟩
    intro beta hBeta
    obtain ⟨Y, edge⟩ := function.total hBeta
    have member := imageEntry edge
    obtain ⟨x, chosen, unique⟩ := chooser.function.2 Y member
    have hx := chooser.chosen Y x chosen
    refine ⟨x, (pair_mem_relationCompose delta A (⋃₀ A) z c beta x).2
      ⟨hBeta, ZFSet.mem_sUnion.2 ⟨Y, member, hx⟩, Y, member, edge, chosen⟩, ?_⟩
    intro y yEdge
    obtain ⟨_key, _range, Y', _member, other, picked⟩ :=
      (pair_mem_relationCompose delta A (⋃₀ A) z c beta y).1 yEdge
    have same : Y' = Y := function.unique other edge
    exact unique y (same ▸ picked)
  refine ⟨f, hf, ⟨⋃₀ A, code⟩, ?_⟩
  intro beta Y x edge chosen
  obtain ⟨_key, _range, Y', _member, other, picked⟩ :=
    (pair_mem_relationCompose delta A (⋃₀ A) z c beta x).1 chosen
  have same : Y' = Y := function.unique other edge
  exact same ▸ chooser.chosen Y' x picked

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFinalInsertionExceptions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace FinalInsertionFamiliesCode
variable {Labels P G r μ A c e d F caps actors : ZFSet.{u}}
variable (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
include family

theorem tests (order : PartialOrderCode P r) (filter : MeetFilterCode P r μ F)
    {label cap v : ZFSet.{u}} (entry : ZFSet.pair label cap ∈ caps)
    (hv : v ∈ P) (above : ZFSet.pair e v ∈ r) :
    (v ∈ F → ZFSet.pair cap v ∈ r) ∧
      (v ∉ F → ZFSet.pair (ZFSet.pair cap v) c ∈ μ) := by
  have profile := (family.profiles label cap entry).profile v hv above
  refine ⟨fun member => profile.1 ⟨v, member, order.refl v hv⟩, ?_⟩
  intro negative
  apply profile.2
  rintro ⟨f, hf, lower⟩
  exact negative (filter.upward f hf v hv lower)

end FinalInsertionFamiliesCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.FinalInsertionFamiliesCode
open SetRealization
universe u
variable {Labels P G r μ A c e d F caps actors : ZFSet.{u}}

theorem decodedCaps_entry
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (label : SetMembers Labels) :
    ZFSet.pair (SetMembers.raw label) (SetMembers.raw (family.decodedCaps label)) ∈ caps :=
  (SetMembers.presentation Labels).decodeFunction_mem (SetMembers.presentation P)
    caps family.cap_injection.function label

theorem decodedActors_entry
    (family : FinalInsertionFamiliesCode Labels P G r μ A c e d F caps actors)
    (label : SetMembers Labels) :
    ZFSet.pair (SetMembers.raw label) (SetMembers.raw (family.decodedActors label)) ∈ actors :=
  (SetMembers.presentation Labels).decodeFunction_mem (SetMembers.presentation G)
    actors family.actor_injection.function label

end PartitionPilot.Forcing.FinalInsertionFamiliesCode



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalRowOrdinaryZF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

include fulfilled

theorem decoded_strict_growth :
    let geometry := run.finalGeometry i₀
    letI := geometry.meet.order.toPartialOrder
    ∀ x : SetMembers geometry.carrier, ∃ y : SetMembers geometry.carrier, x < y := by
  let geometry := run.finalGeometry i₀
  let := geometry.meet.order.toPartialOrder
  dsimp only
  intro x
  obtain ⟨y, hy, lower, strict⟩ := fulfilled.growth _ (SetMembers.raw_mem x)
  refine ⟨SetMembers.ofMem y hy, lt_iff_le_not_ge.2 ⟨?_, ?_⟩⟩
  · change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (SetMembers.ofMem y hy))
      ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using lower
  · change ¬ ZFSet.pair (SetMembers.raw (SetMembers.ofMem y hy)) (SetMembers.raw x)
      ∈ geometry.order
    simpa only [SetMembers.raw_ofMem] using strict

end GroundMainPrefix.FinalFulfillment

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralDataSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
open scoped ZFSet
local notation "rawGraph" => rawRowAssignmentActionGraph t.carrier Q c.carrier (⋃₀ ⋃₀ Q)
  (M.structuralAssignments t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history)
  (a.actionGraph c t)
  (M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history)
include hs hh ordinal trace

local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace

theorem semanticStructuralAction_graph :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    (act).actionGraph (SetMembers.presentation Q) t = rawGraph := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  unfold semanticStructuralAction
  exact PosetActionCode.toPresentedPosetAction_graph _ _ _

theorem semanticStructuralAction_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    ∀ (g : G) (p : SetMembers Q) (r : R) (A : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw ((act).iso g p) = ZFSet.pair (c.encode (a.iso g r))
        (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  intro g p r A code
  have edge := ((act).triple_mem_actionGraph (SetMembers.presentation Q) t g p ((act).iso g p)).2 rfl
  rw [M.semanticStructuralAction_graph] at edge
  change ZFSet.pair (ZFSet.pair (t.encode g) (SetMembers.raw p)) (SetMembers.raw ((act).iso g p)) ∈ _ at edge
  obtain ⟨q, D, _, target⟩ := exists_presentedRowAssignmentCoordinates c
    (M.structuralForcingCarrier_shape c.carrier t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history)
    (SetMembers.raw_mem ((act).iso g p))
  rw [code, target] at edge
  obtain ⟨_, _, row, data⟩ := (presentedRowAssignmentGraph_entry a c t Q _ _ g r q A D).1 edge
  rw [target, row, data]
  rfl

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparedWitnessSelections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem StoredSupportPreparedConditionCode.forget
    {M : TransitiveGround.{u}} {rows T stages history nodes p S : ZFSet.{u}}
    (prepared : StoredSupportPreparedConditionCode M rows T stages history nodes p S) :
    StoredPreparedConditionCode M rows T stages history nodes p := by
  intro row A equal x member
  obtain ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meet, environment,
    sourceRow, sourceA, hSourceA, source, subset, selected,
    k, hk, enumerations, he, q, hq, cut, family, _supportBound⟩ := prepared row A equal x member
  exact ⟨alpha, hAlpha, fields, stored, terms, nodeCarrier, meet, environment,
    sourceRow, sourceA, hSourceA, source, subset, selected,
    k, hk, enumerations, he, q, hq, cut, family⟩

end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalStructuralCommonSupportInduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

omit a t in
theorem localized_mem (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {E : Set P} (hE : s.subset E ∈ M.sets) (r : P) : s.subset (Localized r E) ∈ M.sets := by
  let params := extend (s.subset E) (extend s.carrier (extend s.conditionOrder (extend (s.encode r) Fin.elim0)))
  have members : ∀ i, params i ∈ M.sets := Fin.cases hE (Fin.cases carrier
    (Fin.cases order (Fin.cases (M.transitive carrier (s.encode_mem r)) (fun i => Fin.elim0 i))))
  have selected := M.bounded_separation_mem separation BoundedFormula.localizedWitnessFormula params members carrier
  have correct (q : P) : BoundedFormula.Truth BoundedFormula.localizedWitnessFormula
      (extend (s.encode q) params) ↔ q ∈ Localized r E := by
    simp only [BoundedFormula.localizedWitnessFormula, BoundedFormula.truth_disj, BoundedFormula.Truth,
      BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
    change (s.encode q ∈ s.subset E ∨ ¬ ∃ z ∈ s.carrier,
      ZFSet.pair z (s.encode q) ∈ s.conditionOrder ∧
      ZFSet.pair z (s.encode r) ∈ s.conditionOrder) ↔ _
    erw [s.encode_mem_subset]
    have compat : (∃ z ∈ s.carrier, ZFSet.pair z (s.encode q) ∈ s.conditionOrder ∧
        ZFSet.pair z (s.encode r) ∈ s.conditionOrder) ↔ Compatible q r := by
      constructor
      · rintro ⟨z,hz,hq,hr⟩
        obtain ⟨z,rfl⟩ := (s.mem_carrier z).1 hz
        exact ⟨z,(s.pair_mem_conditionOrder _ _).1 hq,(s.pair_mem_conditionOrder _ _).1 hr⟩
      · rintro ⟨z,hq,hr⟩
        exact ⟨s.encode z,s.encode_mem z,(s.pair_mem_conditionOrder _ _).2 hq,
          (s.pair_mem_conditionOrder _ _).2 hr⟩
    rw [compat]
    rfl
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.localizedWitnessFormula
      (extend z params)) s.carrier = s.subset (Localized r E) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,rel⟩
      obtain ⟨q,rfl⟩ := (s.mem_carrier z).1 hz
      exact (s.encode_mem_subset _ q).2 ((correct q).1 rel)
    · intro hz
      obtain ⟨q,hq,rfl⟩ := (s.mem_subset _ z).1 hz
      exact ⟨s.encode_mem q,(correct q).2 hq⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
include pairing unions powers separation carrier order

theorem ordinary_generic_meets_coded_denseBelow (H : ConditionFilter P)
    (ordinary : H.GenericFor (formulaFamily (M.nameDomain s)))
    {base : P} (member : H.mem base) {E : Set P}
    (ground : s.subset E ∈ M.sets) (dense : DenseBelow base E) : H.Meets E := by
  have localized := M.localized_mem s separation carrier order ground base
  obtain ⟨q, hq, good | bad⟩ := M.ordinary_generic_meets_coded_dense s pairing unions powers
    separation H ordinary localized (localized_dense dense)
  · exact ⟨q, hq, good⟩
  · exact False.elim (bad (H.compatible hq member))

theorem ordinary_generic_candidate_witness (collection : CollectionSchema M.sets)
    {n : Nat} (phi : SetFormula (n + 1)) (env : Assignment (M.nameDomain s) n)
    (W : ZFSet.{u}) (ground : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z)
    (H : ConditionFilter P) (ordinary : H.GenericFor (formulaFamily (M.nameDomain s)))
    {base : P} (member : H.mem base)
    (dense : DenseBelow base {q | ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
      Forces (M.nameDomain s) phi (extend tau env) q}) :
    ∃ tau : (M.nameDomain s).names, tau.val.val ∈ W ∧
      ∃ q, H.mem q ∧ Forces (M.nameDomain s) phi (extend tau env) q := by
  have code := M.candidateForcingSet_mem s pairing unions powers separation collection carrier order
    phi env W ground valid
  obtain ⟨q, hq, tau, candidate, forced⟩ :=
    M.ordinary_generic_meets_coded_denseBelow s pairing unions powers separation carrier order
      H ordinary member code dense
  exact ⟨tau, candidate, q, hq, forced⟩

end PartitionPilot.Forcing.TransitiveGround


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalStructuralCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet




namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [PartialOrder L]

theorem compressed_name_support (a : PosetAction G P) (s : Presentation P)
    (d : PosetAction G L) (g : G) (D E : L) (tau : Name s)
    (support : d.principalFix D ≤ a.stabilizer s tau)
    (below : d.iso g D ≤ E) :
    d.principalFix E ≤ a.stabilizer s (a.act s g tau) := by
  rw [a.stabilizer_conjugation]
  have moved : d.principalFix (d.iso g D) ≤
      (a.stabilizer s tau).map (Compression.RecursiveMaps.CosetGeometry.OrderAction.conjugateHom g) := by
    rw [← principalFix_map_conjugate]
    exact Subgroup.map_mono support
  exact le_trans (d.principalFix_antitone below) moved

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_compression
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
  ∀ (_hLifted : lifted ∈ M.sets) (_hSquared : squared ∈ M.sets)
    (_valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (_valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (_closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (_closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (_children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (_children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (_hs : stages ∈ M.sets) (_hh : history ∈ M.sets)
    (_stagesOrdinal : ordinalSetProperty stages)
    (_trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  ∀ (row : SetMembers c.carrier) (A : ZFSet.{u}),
    ZFSet.pair (c.encode row) A ∈ upperQ →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (ZFSet.pair (c.encode row) A) →
  ∀ (V E D0 : SetMembers geometry.carrier), V < E → V ≤ D0 →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) → i ≤ D0) →
    (∀ z ∈ A, ZFSet.pair z (s.encode D0) ∈ stageOneDataBounds A indices lifted S s.carrier mu
      s.nonbottom.carrier s.conditionOrder anchors tuples) →
  ∃ (h : SetMembers geometry.actors) (cap : SetMembers geometry.carrier),
    h ∈ a.principalFix V ∧ V < cap ∧ cap ≤ E ∧ a.iso h D0 ≤ cap ∧
    let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h) A
    ∃ commonRow : SetMembers c.carrier,
      SetMembers.raw commonRow = SetMembers.raw row ∪ SetMembers.raw (act.iso h row) ∧
      ZFSet.pair (c.encode commonRow) (A ∪ movedA) ∈ upperQ ∧
      ZFSet.pair (ZFSet.pair (c.encode commonRow) (A ∪ movedA)) (ZFSet.pair (c.encode row) A) ∈
        M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed ∧
      ZFSet.pair (ZFSet.pair (c.encode commonRow) (A ∪ movedA))
        (ZFSet.pair (c.encode (act.iso h row)) movedA) ∈
        M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let indices := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph indices s.carrier 2
  intro row A condition prepared V E D0 lower bound rowD dataD
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have labelGround : Labels ∈ M.sets := labels.symm ▸ spec.1
  have labelLarge : ¬ M.groundEmbeddable Labels ZFSet.omega := labels.symm ▸ spec.2.2.2
  have generatorGround : ({s.encode E} : ZFSet.{u}) ∈ M.sets :=
    M.insert_mem pairing unions (M.transitive hL (s.encode_mem E)) (M.empty_mem ⟨s.carrier, hL⟩)
  have generatorSubset : ({s.encode E} : ZFSet.{u}) ⊆ geometry.carrier := by
    intro z hz
    have same := ZFSet.mem_singleton.1 hz
    subst z
    exact s.encode_mem E
  have generatorNonempty : ({s.encode E} : ZFSet.{u}).Nonempty :=
    ⟨s.encode E, ZFSet.mem_singleton.2 rfl⟩
  have above : ∀ z ∈ ({s.encode E} : ZFSet.{u}), ZFSet.pair (s.encode E) z ∈ geometry.order := by
    intro z hz
    have same := ZFSet.mem_singleton.1 hz
    subst z
    exact geometry.meet.order.refl _ (s.encode_mem E)
  have rawRowD : ∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw row) →
      ZFSet.pair (s.encode i) (s.encode D0) ∈ geometry.order := fun i hi => rowD i hi
  obtain ⟨selections, whole, function, selected, rangeGround, rangeSmall,
    usedGround, usedSmall, usedSubset, profilesGround, profilesSmall, profileFilters, coverage,
    filterGround, filterCode, contains, least, filterAbove, caps, hCaps, actors, hActors,
    family, bad, hBad, badSubset, badSmall, containsExtra, good, available, unionsFor⟩ :=
    fulfilled.structural_compatible_insertion_unions collection infinite choice small columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace row A condition prepared
      {s.encode E} (s.encode V) (s.encode E) (s.encode D0) ∅
      labelGround generatorGround generatorSubset generatorNonempty (s.encode_mem V)
      (s.encode_mem E) (s.encode_mem D0) (le_of_lt lower) (not_le_of_gt lower) bound above
      (M.empty_mem ⟨s.carrier, hL⟩) (M.empty_groundEmbeddable ZFSet.omega ⟨s.carrier, hL⟩)
      (fun _ member => (ZFSet.notMem_empty _ member).elim) rawRowD dataD
  obtain ⟨label, labelMember, goodLabel⟩ := available labelLarge
  let chosen : SetMembers Labels := SetMembers.ofMem label labelMember
  have chosenGood : SetMembers.raw chosen ∉ bad := by
    simpa only [chosen, SetMembers.raw_ofMem] using goodLabel
  let h := family.decodedActors chosen
  let cap := family.decodedCaps chosen
  have actorEdge := family.decodedActors_entry chosen
  have capEdge := family.decodedCaps_entry chosen
  have fixed : h ∈ a.principalFix V := by
    intro v hv
    exact (geometry.action_code.act_eq_iff h v v).2
      (family.fixes _ _ actorEdge _ (s.encode_mem v) hv)
  have profile := family.profiles _ _ capEdge
  have strictCap : V < cap := lt_iff_le_not_ge.2 ⟨profile.target_below_cap, profile.cap_not_below_target⟩
  have capBelow : cap ≤ E :=
    ((family.tests geometry.meet.order filterCode capEdge (s.encode_mem E)
      (geometry.meet.order.refl _ (s.encode_mem E))).1
        (contains (ZFSet.mem_singleton.2 rfl)))
  have movedBound : a.iso h D0 ≤ cap :=
    family.dominates _ _ _ actorEdge capEdge _ (s.encode_mem _) (geometry.action_code.act_mem h D0)
  exact ⟨h, cap, fixed, strictCap, capBelow, movedBound, unionsFor chosen chosenGood⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalCompressedNameForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_compressed_name_forcing
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ {n : Nat} (phi : SetFormula (n + 1)) (tau : (M.nameDomain upper).names)
    (tail : Fin n → (M.nameDomain upper).names) (V E : SetMembers geometry.carrier)
    (p : SetMembers upperQ), V < E →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) tau.val →
    (∀ j, a.principalFix V ≤ upperAct.stabilizer upper (tail j).val) →
    Forces (M.nameDomain upper) phi (extend tau tail) p →
    ∃ g : SetMembers geometry.actors, g ∈ a.principalFix V ∧
    ∃ sigma : (M.nameDomain upper).names,
      sigma.val = upperAct.act upper g tau.val ∧
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) sigma.val ∧
      a.principalFix E ≤ upperAct.stabilizer upper sigma.val ∧
    ∃ r q : SetMembers upperQ,
      r ≤ p ∧ StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw r) ∧
      q ≤ r ∧ q ≤ upperAct.iso g r ∧ q ≤ p ∧ q ≤ upperAct.iso g p ∧
      Forces (M.nameDomain upper) phi (extend sigma tail) q := by
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro upperAct upper n phi tau tail V E p strict hsTau fixedTail forced
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection hG hL order graph supports hLifted hSquared hs hh
  have hGraph : upperAct.actionGraph upper b ∈ M.sets := by
    erw [M.semanticStructuralAction_graph]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection hG hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments forcingAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b pairing unions powers separation
    collection hQ hG hGraph
  have closed : ∀ g nu, nu ∈ (M.nameDomain upper).names →
      upperAct.act upper g nu ∈ (M.nameDomain upper).names :=
    M.act_mem upper upperAct b pairing unions powers separation collection hQ maps
  obtain ⟨B, supportTau⟩ := hsTau.symmetric
  obtain ⟨rawR, memberR, belowRaw, support, _hSupport, _subsetSupport, _smallSupport, prepared⟩ :=
    fulfilled.structural_support_prepared_strengthening collection infinite choice small smallD
      irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace (SetMembers.raw p) (SetMembers.raw_mem p)
  let r : SetMembers upperQ := SetMembers.ofMem rawR memberR
  have rRaw : SetMembers.raw r = rawR := SetMembers.raw_ofMem _ _
  have below : r ≤ p := by
    change ZFSet.pair (SetMembers.raw r) (SetMembers.raw p) ∈ _
    rw [rRaw]
    exact belowRaw
  have preparedR : StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier
      (SetMembers.raw r) := by
    rw [rRaw]
    exact prepared.forget
  let sourceRow := M.refinementHistoryRowFunction c lifted stages packed r
  obtain ⟨A, rCode⟩ := M.refinementHistoryRowFunction_coordinates c lifted stages packed r
  obtain ⟨dBound, vd, bd, usedD, dataD⟩ := fulfilled.toFinalFulfillment.structural_bounds_with
    collection infinite choice columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    r sourceRow A V B rCode
  have condition : ZFSet.pair (c.encode sourceRow) A ∈ upperQ := rCode ▸ SetMembers.raw_mem r
  have preparedCode : StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier
      (ZFSet.pair (c.encode sourceRow) A) := rCode ▸ preparedR
  obtain ⟨g, cap, fixed, _strictCap, capE, movedD, commonRow, _rowCode, memberQ, toR, toMovedR⟩ :=
    fulfilled.structural_compression collection infinite choice labels small columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace sourceRow A condition preparedCode V E dBound
      strict vd usedD dataD
  let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode g) A
  let rawQ := ZFSet.pair (c.encode commonRow) (A ∪ movedA)
  let q : SetMembers upperQ := SetMembers.ofMem rawQ memberQ
  have qRaw : SetMembers.raw q = rawQ := SetMembers.raw_ofMem _ _
  have qr : q ≤ r := by
    change ZFSet.pair (SetMembers.raw q) (SetMembers.raw r) ∈ _
    rw [qRaw, rCode]
    exact toR
  have movedCode : SetMembers.raw (upperAct.iso g r) =
      ZFSet.pair (c.encode (act.iso g sourceRow)) movedA :=
    M.semanticStructuralAction_coordinates c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace g r sourceRow A rCode
  have qgr : q ≤ upperAct.iso g r := by
    change ZFSet.pair (SetMembers.raw q) (SetMembers.raw (upperAct.iso g r)) ∈ _
    rw [qRaw, movedCode]
    exact toMovedR
  let sigma : (M.nameDomain upper).names := ⟨upperAct.act upper g tau.val, closed g tau.val tau.property⟩
  have supported : a.principalFix E ≤ upperAct.stabilizer upper sigma.val :=
    upperAct.compressed_name_support upper a g dBound E tau.val
      ((a.principalFix_antitone bd).trans supportTau) (movedD.trans capE)
  have forcedR := forces_mono (M.nameDomain upper) phi (extend tau tail) forced below
  have translated := (upperAct.formula_forces_act_iff upper (M.nameDomain upper) closed g
    phi (extend tau tail) r).2 forcedR
  have envEq : upperAct.actAssignment upper (M.nameDomain upper) closed g (extend tau tail) =
      extend sigma tail := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · apply Subtype.ext
      exact fixedTail i fixed
  rw [envEq] at translated
  exact ⟨g, fixed, sigma, rfl, hsTau.translated g, supported,
    r, q, below, preparedR, qr, qgr, qr.trans below,
    qgr.trans ((upperAct.iso g).monotone below),
    forces_mono (M.nameDomain upper) phi (extend sigma tail) translated qgr⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundMainFinalGraphValueCandidateAvailability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mem_graphValueCandidateCodes (K : Subgroup G) (tau psi : Name s) :
    psi.val ∈ M.graphValueCandidateCodes a s K tau ↔
      (∃ g : G, ∃ sigma : Name s, sigma.val ∈ M.sets ∧
        sigma.val ∈ Name.descendantFamilyCodes s tau 4 ∧ psi.val = (a.act s g sigma).val) ∧
      K ≤ a.stabilizer s psi := by
  rw [graphValueCandidateCodes, Name.mem_supportedFamilyCodes, a.mem_orbitCodes]
  rfl

theorem graphValueCandidateCodes_hs (F : NormalSubgroupFamily G)
    (K : Subgroup G) (tau : Name s) (symmetric : HereditarilySymmetric a s F tau)
    (psi : Name s) (member : psi.val ∈ M.graphValueCandidateCodes a s K tau) :
    HereditarilySymmetric a s F psi := by
  obtain ⟨⟨g, sigma, _ground, child, equal⟩, _fixed⟩ :=
    (M.mem_graphValueCandidateCodes a s K tau psi).1 member
  have same : psi = a.act s g sigma := Subtype.ext equal
  exact same.symm ▸ (Name.descendantFamilyCodes_hs s a F tau symmetric 4 sigma child).translated g

theorem graphValueCandidateCodes_mem {I : Type u}
    (t : Presentation G) (b : Presentation I) (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (i : I) (hi : b.encode i ∈ M.sets) (tau : Name s) (ground : tau.val ∈ M.sets) :
    M.graphValueCandidateCodes a s (K i) tau ∈ M.sets := by
  have descendants := M.descendantFamilyCodes_mem s pairing unions powers separation carrier tau ground 4
  have orbit := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps _ descendants
  apply M.supportedFamilyCodes_mem a s t b K pairing unions powers separation collection
    carrier group supports maps i hi _ orbit
  intro z member
  obtain ⟨g, sigma, _ground, _child, rfl⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.descendantFamilyCodes s tau 4) z).1 member
  exact (a.act s g sigma).property

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v

theorem graphValueCandidateDensity_of_compression (M : TransitiveGround.{u})
    {G P : Type u} [Group G] [PartialOrder P] (action : PosetAction G P)
    (presentation : Presentation P) (F : Compression.RecursiveMaps.NormalSubgroupFamily G)
    (lowerSupport upperSupport : Subgroup G) (prepared : P → Prop)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (small : M.sets.Countable) (carrier : presentation.carrier ∈ M.sets)
    (z beta : (M.nameDomain presentation).names) (base : P)
    (symmetric : HereditarilySymmetric action presentation F z.val)
    (forced : Forces (M.nameDomain presentation)
      (ex (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula)
      (extend z (extend beta Fin.elim0)) base)
    (compress : ∀ tau : (M.nameDomain presentation).names,
      HereditarilySymmetric action presentation F tau.val →
      ∀ p, Forces (M.nameDomain presentation) (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
        (extend tau (extend z (extend beta Fin.elim0))) p →
      ∃ g : G, g ∈ lowerSupport ∧ ∃ sigma : (M.nameDomain presentation).names,
        sigma.val = action.act presentation g tau.val ∧
        HereditarilySymmetric action presentation F sigma.val ∧
        upperSupport ≤ action.stabilizer presentation sigma.val ∧
        ∃ r q : P, r ≤ p ∧ prepared r ∧ q ≤ r ∧ q ≤ action.iso g r ∧
          q ≤ p ∧ q ≤ action.iso g p ∧
          Forces (M.nameDomain presentation) (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
            (extend sigma (extend z (extend beta Fin.elim0))) q) :
    GraphValueCandidateDensity M action presentation upperSupport z beta base := by
  have descendants := M.graphValue_fourthDescendant_dense presentation pairing unions powers separation
    small carrier z beta base forced
  intro p below
  obtain ⟨q, qp, tau, child, witness⟩ := descendants p below
  have hsTau := Name.descendantFamilyCodes_hs presentation action F z.val symmetric 4 tau.val child
  obtain ⟨g, _fixed, sigma, same, _hsSigma, supported,
      _prepared, common, _below, _preparedCode, _toPrepared, _toMovedPrepared,
      toQ, _toMovedQ, recorded⟩ := compress tau hsTau q witness
  have candidate : sigma.val.val ∈ M.graphValueCandidateCodes action presentation upperSupport z.val := by
    apply (M.mem_graphValueCandidateCodes action presentation upperSupport z.val sigma.val).2
    exact ⟨⟨g, tau.val, tau.property, child, congrArg Subtype.val same⟩, supported⟩
  exact ⟨common, toQ.trans qp, sigma, candidate, recorded⟩

variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_graphValue_candidates_dense
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (z beta : (M.nameDomain upper).names) (V E : SetMembers geometry.carrier)
    (base : SetMembers upperQ), V < E →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z.val →
    a.principalFix V ≤ upperAct.stabilizer upper z.val →
    a.principalFix V ≤ upperAct.stabilizer upper beta.val →
    Forces (M.nameDomain upper) (ex (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula)
      (extend z (extend beta Fin.elim0)) base →
    GraphValueCandidateDensity M upperAct upper (a.principalFix E) z beta base := by
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro upperAct upper z beta V E base strict symmetric fixedZ fixedBeta forced
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  exact graphValueCandidateDensity_of_compression M upperAct upper
    (a.principalSupportFamily ⊥ directed) (a.principalFix V) (a.principalFix E)
    (fun r : SetMembers upperQ => StoredPreparedConditionCode M c.carrier lifted stages packed
      s.carrier (SetMembers.raw r)) pairing unions powers separation small hQ z beta base symmetric forced
    (fun tau hsTau p witness => fulfilled.structural_compressed_name_forcing
      collection infinite choice labels small smallD irreflexive columns hColumns hmu muOrdinal
      valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace
      (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula tau
      (extend z (extend beta Fin.elim0)) V E p strict hsTau
      (Fin.cases fixedZ (Fin.cases fixedBeta (fun j => Fin.elim0 j))) witness)

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_graphValue_candidate_availability
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ (z : (M.nameDomain upper).names) (V E : SetMembers geometry.carrier), V < E →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z.val →
    a.principalFix V ≤ upperAct.stabilizer upper z.val →
    let W := M.graphValueCandidateCodes upperAct upper (a.principalFix E) z.val
    W ∈ M.sets ∧ (∀ x ∈ W, IsName upper x) ∧
      (∀ psi : Name upper, psi.val ∈ W →
        a.principalFix E ≤ upperAct.stabilizer upper psi ∧
        HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) psi) ∧
      ∀ beta ∈ M.sets, ∀ H : ConditionFilter (SetMembers upperQ),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
        (∃ A, ZFSet.pair beta A ∈ Name.eval {p | H.mem p} z.val ∧ A.Nonempty) →
        ∃ psi : Name upper, psi.val ∈ W ∧
          ∃ A, ZFSet.pair beta A ∈ Name.eval {p | H.mem p} z.val ∧
            Name.eval {p | H.mem p} psi ∈ A := by
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro historyRun
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  intro upperAct upper z V E strict symmetric fixedZ W
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection hG hL order graph supports hLifted hSquared hs hh
  have hGraph : upperAct.actionGraph upper b ∈ M.sets := by
    erw [M.semanticStructuralAction_graph]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection hG hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments forcingAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b pairing unions powers separation
    collection hQ hG hGraph
  have groundW : W ∈ M.sets := M.graphValueCandidateCodes_mem upperAct upper b s a.principalFix
    pairing unions powers separation collection hQ hG supports maps E
    (M.transitive hL (s.encode_mem E)) z.val z.property
  have validW : ∀ x ∈ W, IsName upper x := by
    intro x member
    dsimp only [W, TransitiveGround.graphValueCandidateCodes, Name.supportedFamilyCodes] at member
    rw [ZFSet.mem_sep] at member
    obtain ⟨psi, same, _fixed⟩ := member.2
    exact same ▸ psi.property
  refine ⟨groundW, validW, ?_, ?_⟩
  · intro psi member
    exact ⟨((M.mem_graphValueCandidateCodes upperAct upper (a.principalFix E) z.val psi).1 member).2,
      M.graphValueCandidateCodes_hs upperAct upper (a.principalSupportFamily ⊥ directed)
        (a.principalFix E) z.val symmetric psi member⟩
  · intro beta hBeta H ordinary nonempty
    have orderQ : upper.conditionOrder ∈ M.sets := by
      rw [M.refinementHistoryDecodedOrder_eq c.conditionOrder_code lifted stages packed]
      exact M.refinementHistoryOrder_mem pairing unions powers separation
        carrier forcingOrder hLifted hs hPacked omega
    let betaName : (M.nameDomain upper).names := ⟨Name.check upper ⊤ beta,
      M.check_mem upper ⊤ pairing unions powers separation collection
        (M.transitive hQ (upper.encode_mem ⊤)) beta hBeta⟩
    have checked : Name.eval {p | H.mem p} betaName.val = beta :=
      Name.eval_check {p | H.mem p} ⊤ H.top_mem beta
    obtain ⟨A, edge, x, hx⟩ := nonempty
    obtain ⟨sigma, child, same⟩ := Name.value_member_fourthDescendant upper {p | H.mem p}
      z.val beta A x edge hx
    have descendants := M.descendantFamilyCodes_mem upper pairing unions powers separation hQ
      z.val z.property 4
    let original : (M.nameDomain upper).names := ⟨sigma, M.transitive descendants child⟩
    have truth : Realize ((M.nameDomain upper).values {p | H.mem p})
        (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
        (evalAssignment {p | H.mem p} (extend original (extend z (extend betaName Fin.elim0)))) := by
      apply (realize_graphValueMember_values (M.nameDomain upper) {p | H.mem p} 0 1 2 _).2
      refine ⟨A, ?_, same.symm ▸ hx⟩
      change ZFSet.pair (Name.eval {p | H.mem p} betaName.val) A ∈ Name.eval {p | H.mem p} z.val
      rw [checked]
      exact edge
    obtain ⟨base, hBase, forced⟩ := (forcing_truth (M.nameDomain upper) H ordinary
      (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
      (extend original (extend z (extend betaName Fin.elim0)))).1 truth
    have existence : Forces (M.nameDomain upper)
        (ex (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula)
        (extend z (extend betaName Fin.elim0)) base := by
      apply (forces_ex_iff (M.nameDomain upper) _ _ base).2
      intro q below
      exact ⟨q, le_rfl, original, forces_mono (M.nameDomain upper) _ _ forced below⟩
    have fixedBeta : a.principalFix V ≤ upperAct.stabilizer upper betaName.val :=
      fun g _ => upperAct.act_check upper g beta
    have density := fulfilled.structural_graphValue_candidates_dense collection infinite choice
      labels small smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared
      valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
      z betaName V E base strict symmetric fixedZ fixedBeta existence
    obtain ⟨candidate, member, q, hq, recorded⟩ := M.ordinary_generic_candidate_witness upper
      pairing unions powers separation hQ orderQ collection
      (BoundedFormula.graphValueMemberFormula (n := 3) 0 1 2).toFormula
      (extend z (extend betaName Fin.elim0)) W groundW validW H ordinary hBase density
    have actual := (realize_graphValueMember_values (M.nameDomain upper) {p | H.mem p} 0 1 2
      (extend candidate (extend z (extend betaName Fin.elim0)))).1
        (forces_sound (M.nameDomain upper) H ordinary _ _ hq recorded)
    obtain ⟨value, edgeValue, memberValue⟩ := actual
    change ZFSet.pair (Name.eval {p | H.mem p} betaName.val) value ∈
      Name.eval {p | H.mem p} z.val at edgeValue
    rw [checked] at edgeValue
    exact ⟨candidate.val, member, value, edgeValue, memberValue⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundExtensionOrdinals
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula Compression.RecursiveMaps
universe u v

namespace Name

theorem rank_eval_le_code_rank {P : Type u} {s : Presentation P} (H : Set P) (tau : Name s) :
    ZFSet.rank (eval H tau) ≤ ZFSet.rank tau.val := by
  induction tau using inductionOn with
  | step tau ih =>
    apply ZFSet.rank_le_iff.2
    intro x hx
    obtain ⟨sigma, p, entry, _active, rfl⟩ := (mem_eval H tau x).1 hx
    exact (ih sigma p entry).trans_lt (entry_rank_lt entry)

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem ordinalCode_rank_mem {x : ZFSet.{u}} (hx : x ∈ M.sets) :
    ordinalCode (ZFSet.rank x) ∈ M.sets := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    have witnesses : ∀ y ∈ x, ∃ beta ∈ M.sets,
        Realize M.sets (cumulativeRankValueFormula 0 1)
          (extend y (extend beta Fin.elim0)) := by
      intro y hy
      have hyM := M.transitive hx hy
      have hRank := ih y hy hyM
      refine ⟨ordinalCode (ZFSet.rank y), hRank, ?_⟩
      exact (M.realize_cumulativeRankValueFormula pairing unions powers separation collection
        0 1 _ (Fin.cases hyM (Fin.cases hRank (fun i => Fin.elim0 i)))).2 rfl
    obtain ⟨B, hB, collected⟩ := M.collection_witness collection
      (cumulativeRankValueFormula 0 1) Fin.elim0 (fun i => Fin.elim0 i) hx witnesses
    let O := ZFSet.sep ordinalSetProperty B
    have hO : O ∈ M.sets := by
      have selected := M.bounded_separation_mem separation (BoundedFormula.ordinalFormula 0)
        Fin.elim0 (fun i => Fin.elim0 i) hB
      have equal : ZFSet.sep (fun z => BoundedFormula.Truth
          (BoundedFormula.ordinalFormula 0) (extend z Fin.elim0)) B = O := by
        apply ZFSet.ext
        intro z
        rw [ZFSet.mem_sep, ZFSet.mem_sep]
        apply and_congr Iff.rfl
        exact (BoundedFormula.truth_ordinalFormula 0 _).trans (ordinalSetProperty_iff z).symm
      exact equal ▸ selected
    have ordinals : ∀ beta ∈ O, ordinalSetProperty beta := fun _ member => (ZFSet.mem_sep.1 member).2
    let U := ZFSet.sUnion O
    have hU : U ∈ M.sets := M.union_mem unions hO
    have ordinalU : ordinalSetProperty U := ordinalSetProperty_sUnion ordinals
    have bound : ZFSet.rank x ≤ Order.succ (ZFSet.rank U) := by
      apply ZFSet.rank_le_iff.2
      intro y hy
      obtain ⟨beta, hb, rankValue⟩ := collected y hy
      have equal : beta = ordinalCode (ZFSet.rank y) :=
        (M.realize_cumulativeRankValueFormula pairing unions powers separation collection
          0 1 _ (Fin.cases (M.transitive hx hy)
            (Fin.cases (M.transitive hB hb) (fun i => Fin.elim0 i)))).1 rankValue
      have member : ordinalCode (ZFSet.rank y) ∈ O :=
        ZFSet.mem_sep.2 ⟨equal ▸ hb, ordinalSetProperty_ordinalCode _⟩
      have subset : ordinalCode (ZFSet.rank y) ⊆ U :=
        fun z hz => ZFSet.mem_sUnion.2 ⟨_, member, hz⟩
      have rankLe : ZFSet.rank y ≤ ZFSet.rank U := by
        simpa only [rank_ordinalCode] using ZFSet.rank_mono subset
      exact rankLe.trans_lt (Order.lt_succ _)
    have hSucc : insert U U ∈ M.sets := M.insert_mem pairing unions hU hU
    have hNext : insert (insert U U) (insert U U) ∈ M.sets :=
      M.insert_mem pairing unions hSucc hSucc
    apply M.transitive hNext
    rw [ordinalSetProperty_eq_code_rank U ordinalU, ← ordinalCode_succ, ← ordinalCode_succ,
      mem_ordinalCode_iff]
    exact Order.lt_succ_iff.2 bound

theorem ordinal_eval_mem {P : Type u} (s : Presentation P) (H : Set P)
    (tau : Name s) (ground : tau.val ∈ M.sets)
    (ordinal : ordinalSetProperty (Name.eval H tau)) : Name.eval H tau ∈ M.sets := by
  have codeGround := M.ordinalCode_rank_mem pairing unions powers separation collection ground
  have successorGround := M.insert_mem pairing unions codeGround codeGround
  apply M.transitive successorGround
  rw [ordinalSetProperty_eq_code_rank (Name.eval H tau) ordinal,
    ← ordinalCode_succ, mem_ordinalCode_iff]
  exact Order.lt_succ_iff.2 (Name.rank_eval_le_code_rank H tau)

theorem ordinaryExtension_ordinal_mem {P : Type u} [Preorder P]
    (s : Presentation P) (H : ConditionFilter P) {delta : ZFSet.{u}}
    (member : delta ∈ (M.ordinaryExtension s H).sets) (ordinal : ordinalSetProperty delta) :
    delta ∈ M.sets := by
  obtain ⟨tau, ground, rfl⟩ := (M.mem_ordinaryExtension s H delta).1 member
  exact M.ordinal_eval_mem pairing unions powers separation collection s {p | H.mem p} tau ground ordinal

theorem symmetricExtension_ordinal_mem {P : Type u} [PartialOrder P]
    (s : Presentation P) {G : Type v} [Group G] (a : PosetAction G P)
    (F : NormalSubgroupFamily G) (H : ConditionFilter P) {delta : ZFSet.{u}}
    (member : delta ∈ (M.symmetricExtension s a F H).sets) (ordinal : ordinalSetProperty delta) :
    delta ∈ M.sets :=
  M.ordinaryExtension_ordinal_mem pairing unions powers separation collection s H
    (M.symmetricExtension_subset_ordinaryExtension s a F H member) ordinal

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundMainFinalPartitionModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)

theorem structural_ordinal_choice_oai
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  ∀ H : ConditionFilter (SetMembers upperQ),
    H.GenericFor (formulaFamily (M.nameDomain upper)) →
    let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
    ZFRealization N.sets →
      ∀ delta ∈ N.sets, ordinalSetProperty delta →
        ∀ z ∈ N.sets, FunctionGraphOn delta z →
          (∀ beta A, ZFSet.pair beta A ∈ z → A.Nonempty) →
          ∃ f ∈ N.sets, FunctionGraphOn delta f ∧
            ∀ beta A x, ZFSet.pair beta A ∈ z → ZFSet.pair beta x ∈ f → x ∈ A := by
  intro geometry
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  intro s b a directed hL hG hC order graph nodeMaps supports
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro historyRun
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    historyRun.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  intro upperAct upper H ordinary N zf delta hDelta ordinal z hz function nonempty
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  have groundDelta : delta ∈ M.sets := M.symmetricExtension_ordinal_mem
    pairing unions powers separation collection upper upperAct
    (a.principalSupportFamily ⊥ directed) H hDelta ordinal
  obtain ⟨zName, groundZ, symmetric, same⟩ :=
    (M.mem_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H z).1 hz
  obtain ⟨V, fixedZ⟩ := symmetric.symmetric
  obtain ⟨E, strict⟩ := fulfilled.toFinalFulfillment.decoded_strict_growth V
  let original : (M.nameDomain upper).names := ⟨zName, groundZ⟩
  have candidates := fulfilled.structural_graphValue_candidate_availability
    collection infinite choice labels small smallD irreflexive columns hColumns hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace original V E strict symmetric fixedZ
  let W := M.graphValueCandidateCodes upperAct upper (a.principalFix E) zName
  have groundW : W ∈ M.sets := candidates.1
  have validW : ∀ x ∈ W, IsName upper x := candidates.2.1
  have fixed : ∀ psi : Name upper, psi.val ∈ W →
      a.principalFix E ≤ upperAct.stabilizer upper psi := fun psi member =>
    (candidates.2.2.1 psi member).1
  have children : ∀ psi : Name upper, psi.val ∈ W →
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) psi :=
    fun psi member => (candidates.2.2.1 psi member).2
  apply M.supportedNameFamily_graph_choice upper upperAct (a.principalSupportFamily ⊥ directed)
    pairing unions powers separation collection choice hQ groundW validW
    (a.principalFix E) ⟨E, le_rfl⟩ fixed children H zf hDelta hz function
  intro beta member
  have groundBeta : beta ∈ M.sets := M.transitive groundDelta member
  obtain ⟨A, edge⟩ := function.total member
  have edgeOriginal : ZFSet.pair beta A ∈ Name.eval {p | H.mem p} original.val := by
    rw [show Name.eval {p | H.mem p} original.val = z from same]
    exact edge
  obtain ⟨psi, candidate, B, betaB, chosen⟩ := candidates.2.2.2 beta groundBeta H ordinary
    ⟨A, edgeOriginal, nonempty beta A edge⟩
  exact ⟨psi, candidate, B, same ▸ betaB, chosen⟩






end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_ordinal_choice_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_ordinal_choice_oai.{u, v}
