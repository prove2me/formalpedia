-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_forcedSupportedCertificateFamily
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:17:39.863655+00:00
-- url     : https://prove2.me/submissions/e78f57e6-78af-42ec-9725-d1670d388aaa

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

section

open SetRealization
universe u v
variable {P : Type u}

namespace Name
variable {s : Presentation P}

theorem not_entry_empty (σ : Name s) (p : P) : ¬ Entry σ (empty s) p :=
  ZFSet.notMem_empty _

end Name
end



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

theorem eval_empty (H : Set P) : eval H (empty s) = ∅ := by
  apply ZFSet.ext
  intro x
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, h, _, _⟩
    exact False.elim (not_entry_empty σ p h)
  · exact False.elim ∘ ZFSet.notMem_empty x

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



namespace Name.NameDomain

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem values_extensionality (D : NameDomain s) (H : Set P)
    {x y : ZFSet.{u}} (hx : x ∈ D.values H) (hy : y ∈ D.values H)
    (agree : ∀ z ∈ D.values H, z ∈ x ↔ z ∈ y) : x = y := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (agree z (D.values_transitive H hx hz)).1 hz
  · intro hz
    exact (agree z (D.values_transitive H hy hz)).2 hz

theorem values_foundation (D : NameDomain s) (H : Set P)
    {x : ZFSet.{u}} (hx : x ∈ D.values H) (nonempty : x ≠ ∅) :
    ∃ y ∈ D.values H, y ∈ x ∧ x ∩ y = ∅ := by
  obtain ⟨y, yx, disjoint⟩ := ZFSet.regularity x nonempty
  exact ⟨y, D.values_transitive H hx yx, yx, disjoint⟩

end Name.NameDomain

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
variable {P : Type u} {s : Presentation P}

theorem realize_extensionality (D : Name.NameDomain s) (H : Set P) :
    Realize (D.values H) extensionality Fin.elim0 := by
  classical
  simp only [extensionality, Realize, imp, extend, Fin.cases_zero,
    not_and, not_not]
  intro x hx y hy agree
  apply D.values_extensionality H hx hy
  intro z hz
  exact ⟨(agree z hz).1, (agree z hz).2⟩

theorem realize_foundation (D : Name.NameDomain s) (H : Set P) :
    Realize (D.values H) foundation Fin.elim0 := by
  classical
  simp only [foundation, Realize, imp, ex, extend, Fin.cases_zero,
    not_and, not_not, not_forall, exists_prop]
  intro x hx inhabited
  obtain ⟨w, _, wx⟩ := inhabited
  have nonempty : x ≠ ∅ := by
    intro eq
    rw [eq] at wx
    exact ZFSet.notMem_empty w wx
  obtain ⟨y, hy, yx, disjoint⟩ := D.values_foundation H hx nonempty
  refine ⟨y, hy, yx, ?_⟩
  rintro ⟨z, _, zx, zy⟩
  have member : z ∈ x ∩ y := ZFSet.mem_inter.2 ⟨zx, zy⟩
  rw [disjoint] at member
  exact ZFSet.notMem_empty z member

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

theorem exists_generic_formulaFamily (D : Name.NameDomain s) (small : D.names.Countable) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (formulaFamily D) :=
  exists_generic_for_countable_family p _ (formulaFamily_countable D small)

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

theorem rename_empty (t : Presentation Q) (f : P → Q) :
    rename t f (empty s) = empty t := by
  apply ext
  intro σ p
  rw [entry_rename]
  constructor
  · rintro ⟨ν, q, h, _, _⟩
    exact False.elim (not_entry_empty ν q h)
  · exact False.elim ∘ not_entry_empty σ p

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

end HereditarilySymmetric
end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.Name.NameDomain

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem empty_mem (D : NameDomain s) (nonempty : D.names.Nonempty) : empty s ∈ D.names := by
  classical
  have step : ∀ τ : Name s, τ ∈ D.names → empty s ∈ D.names := by
    intro τ
    induction τ using inductionOn with
    | step τ ih =>
      intro hτ
      by_cases member : ∃ σ p, Entry σ τ p
      · obtain ⟨σ, p, entry⟩ := member
        exact ih σ p entry (D.children hτ entry)
      · have eq : τ = empty s := by
          apply Name.ext
          intro σ p
          constructor
          · intro h
            exact False.elim (member ⟨σ, p, h⟩)
          · intro h
            exact False.elim (not_entry_empty σ p h)
        exact eq ▸ hτ
  obtain ⟨τ, hτ⟩ := nonempty
  exact step τ hτ

theorem empty_value_mem (D : NameDomain s) (nonempty : D.names.Nonempty) (H : Set P) :
    (∅ : ZFSet.{u}) ∈ D.values H :=
  (D.mem_values H ∅).2 ⟨empty s, D.empty_mem nonempty, eval_empty H⟩

end PartitionPilot.Forcing.Name.NameDomain

namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

theorem empty_hs (a : PosetAction G P) (s : Presentation P) (F : NormalSubgroupFamily G) :
    HereditarilySymmetric a s F (Name.empty s) := by
  refine HereditarilySymmetric.mk (F.upward F.top ?_) ?_
  · intro g _
    exact Name.rename_empty s (a.iso g)
  · intro σ p entry
    exact False.elim (Name.not_entry_empty σ p entry)

end PartitionPilot.Forcing.PosetAction

namespace PartitionPilot.Forcing.SetFormula

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem realize_emptySet (D : Name.NameDomain s) (nonempty : D.names.Nonempty) (H : Set P) :
    Realize (D.values H) emptySet Fin.elim0 := by
  rw [emptySet, realize_ex]
  refine ⟨∅, D.empty_value_mem nonempty H, ?_⟩
  intro x _ member
  exact ZFSet.notMem_empty x member

end PartitionPilot.Forcing.SetFormula

end



namespace PartitionPilot.Compression.RecursiveMaps.NormalSubgroupFamily

universe u
variable {G : Type u} [Group G]

theorem fin_iInf (F : NormalSubgroupFamily G) {n : Nat}
    (K : Fin n → Subgroup G) (hK : ∀ i, F.mem (K i)) : F.mem (⨅ i, K i) := by
  induction n with
  | zero =>
    apply F.upward F.top
    apply le_iInf
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    have split : (⨅ i, K i) = K 0 ⊓ ⨅ i : Fin n, K i.succ := by
      apply le_antisymm
      · exact le_inf (iInf_le K 0) (le_iInf (fun i => iInf_le K i.succ))
      · apply le_iInf
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact inf_le_left
        · exact le_trans inf_le_right (iInf_le (fun j : Fin n => K j.succ) j)
    rw [split]
    exact F.inf (hK 0) (ih (fun i => K i.succ) (fun i => hK i.succ))

end PartitionPilot.Compression.RecursiveMaps.NormalSubgroupFamily



namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem nameDomain_nonempty (nonempty : M.sets.Nonempty) : (M.nameDomain s).names.Nonempty :=
  ⟨Name.empty s, M.empty_mem nonempty⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameMixingRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem entry_unionName (τ σ : Name s) (p : P) : Entry σ (unionName τ) p ↔
    ∃ ν r q, Entry ν τ r ∧ Entry σ ν q ∧ p ≤ r ∧ p ≤ q := by
  rw [unionName, entry_assemble]
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨z.val.1.1.val.1, z.val.1.1.val.2, z.val.1.2.val.2,
      z.val.1.1.property, z.val.1.2.property, z.property⟩
  · rintro ⟨ν, r, q, topEntry, child, pr, pq⟩
    exact ⟨⟨(⟨⟨(ν, r), topEntry⟩, ⟨(σ, q), child⟩⟩, p), pr, pq⟩, rfl, rfl⟩

theorem eval_unionName (H : ConditionFilter P) (τ : Name s) :
    eval {p | H.mem p} (unionName τ) = ZFSet.sUnion (eval {p | H.mem p} τ) := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨σ, p, entry, hp, value⟩
    obtain ⟨ν, r, q, topEntry, child, pr, pq⟩ := (entry_unionName τ σ p).1 entry
    exact ⟨eval {p | H.mem p} ν,
      (mem_eval _ τ _).2 ⟨ν, r, topEntry, H.upward hp pr, rfl⟩,
      (mem_eval _ ν x).2 ⟨σ, q, child, H.upward hp pq, value⟩⟩
  · rintro ⟨y, hy, hx⟩
    obtain ⟨ν, r, topEntry, hr, rfl⟩ := (mem_eval _ τ y).1 hy
    obtain ⟨σ, q, child, hq, value⟩ := (mem_eval _ ν x).1 hx
    obtain ⟨p, hp, pr, pq⟩ := H.directed hr hq
    exact ⟨σ, p, (entry_unionName τ σ p).2 ⟨ν, r, q, topEntry, child, pr, pq⟩, hp, value⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_unionName (g : G) (τ : Name s) :
    a.act s g (Name.unionName τ) = Name.unionName (a.act s g τ) := by
  apply Name.ext
  intro σ p
  obtain ⟨σ, rfl⟩ := (a.nameEquiv s g).surjective σ
  obtain ⟨p, rfl⟩ := (a.iso g).surjective p
  change Name.Entry (a.act s g σ) (a.act s g (Name.unionName τ)) (a.iso g p) ↔
    Name.Entry (a.act s g σ) (Name.unionName (a.act s g τ)) (a.iso g p)
  rw [a.entry_act, Name.entry_unionName, Name.entry_unionName]
  constructor
  · rintro ⟨ν, r, q, topEntry, child, pr, pq⟩
    exact ⟨a.act s g ν, a.iso g r, a.iso g q,
      (a.entry_act s g ν τ r).2 topEntry, (a.entry_act s g σ ν q).2 child,
      (a.iso g).monotone pr, (a.iso g).monotone pq⟩
  · rintro ⟨ν, r, q, topEntry, child, pr, pq⟩
    obtain ⟨ν, rfl⟩ := (a.nameEquiv s g).surjective ν
    obtain ⟨r, rfl⟩ := (a.iso g).surjective r
    obtain ⟨q, rfl⟩ := (a.iso g).surjective q
    exact ⟨ν, r, q, (a.entry_act s g ν τ r).1 topEntry,
      (a.entry_act s g σ ν q).1 child, (a.iso g).le_iff_le.1 pr, (a.iso g).le_iff_le.1 pq⟩

theorem unionName_hs (F : NormalSubgroupFamily G) {τ : Name s}
    (hτ : HereditarilySymmetric a s F τ) : HereditarilySymmetric a s F (Name.unionName τ) := by
  refine HereditarilySymmetric.mk (F.upward hτ.symmetric ?_) ?_
  · intro g fixed
    change a.act s g (Name.unionName τ) = Name.unionName τ
    rw [a.act_unionName]
    exact congrArg Name.unionName fixed
  · intro σ p entry
    obtain ⟨ν, r, q, topEntry, child, _, _⟩ := (Name.entry_unionName τ σ p).1 entry
    exact (hτ.member topEntry).member child

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.Name

open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem entry_envelope (τ σ : Name s) (p : P) :
    Entry σ (envelope τ) p ↔ ∃ r, Entry σ τ r ∧ p ≤ r := by
  simp only [envelope, entry_selectName, and_true]

theorem selectName_subset_envelope (R : Name s → P → Prop) (τ : Name s) :
    (selectName R τ).val ⊆ (envelope τ).val := by
  intro z hz
  obtain ⟨σ, p, rfl⟩ := entries_cover (selectName R τ) hz
  obtain ⟨r, old, pr, _⟩ := (entry_selectName R τ σ p).1 hz
  exact (entry_envelope τ σ p).2 ⟨r, old, pr⟩

omit [Preorder P] in
theorem eval_mono (H : Set P) {σ τ : Name s} (sub : σ.val ⊆ τ.val) :
    eval H σ ⊆ eval H τ := by
  intro x hx
  obtain ⟨ν, p, entry, hp, eq⟩ := (mem_eval H σ x).1 hx
  exact (mem_eval H τ x).2 ⟨ν, p, sub entry, hp, eq⟩

theorem eval_envelope (H : ConditionFilter P) (τ : Name s) :
    eval {p | H.mem p} (envelope τ) = eval {p | H.mem p} τ := by
  apply ZFSet.ext
  intro x
  rw [mem_eval, mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨r, old, pr⟩ := (entry_envelope τ σ p).1 entry
    exact ⟨σ, r, old, H.upward hp pr, eq⟩
  · rintro ⟨σ, p, entry, hp, eq⟩
    exact ⟨σ, p, (entry_envelope τ σ p).2 ⟨p, entry, le_rfl⟩, hp, eq⟩

theorem separationName_true (D : NameDomain s) {τ : Name s} (hτ : τ ∈ D.names) :
    separationName D (.equal 0 0) Fin.elim0 τ = envelope τ := by
  apply ext
  intro σ p
  rw [entry_separationName, entry_envelope]
  constructor
  · rintro ⟨r, old, pr, _⟩
    exact ⟨r, old, pr⟩
  · rintro ⟨r, old, pr⟩
    exact ⟨r, old, pr, D.children hτ old, forcesEq_refl σ p⟩

omit [Preorder P] in
theorem rename_mono (f : P → P) {σ τ : Name s} (sub : σ.val ⊆ τ.val) :
    (rename s f σ).val ⊆ (rename s f τ).val := by
  intro z hz
  obtain ⟨ν, p, rfl⟩ := entries_cover (rename s f σ) hz
  obtain ⟨χ, q, entry, eq, hp⟩ := (entry_rename s f σ ν p).1 hz
  exact (entry_rename s f τ ν p).2 ⟨χ, q, sub entry, eq, hp⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_envelope (g : G) (τ : Name s) :
    a.act s g (Name.envelope τ) = Name.envelope (a.act s g τ) :=
  a.act_selectName s g (fun _ _ => True) (fun _ _ => True) (fun _ _ => Iff.rfl) τ

theorem envelope_hs (F : NormalSubgroupFamily G) {τ : Name s}
    (hτ : HereditarilySymmetric a s F τ) : HereditarilySymmetric a s F (Name.envelope τ) := by
  refine HereditarilySymmetric.mk (F.upward hτ.symmetric ?_) ?_
  · intro g hg
    change a.act s g (Name.envelope τ) = Name.envelope τ
    rw [a.act_envelope, show a.act s g τ = τ from hg]
  · intro σ p entry
    obtain ⟨r, old, _⟩ := (Name.entry_envelope τ σ p).1 entry
    exact hτ.member old

theorem act_subset_iff_fixed (g : G) {σ τ : Name s} (fixed : a.act s g τ = τ) :
    (a.act s g σ).val ⊆ τ.val ↔ σ.val ⊆ τ.val := by
  constructor
  · intro sub
    have h := Name.rename_mono (a.iso g⁻¹) sub
    change (a.act s g⁻¹ (a.act s g σ)).val ⊆ (a.act s g⁻¹ τ).val at h
    rw [a.act_inv_left, ← fixed, a.act_inv_left] at h
    exact h
  · intro sub
    have h := Name.rename_mono (a.iso g) sub
    change (a.act s g σ).val ⊆ (a.act s g τ).val at h
    rwa [fixed] at h

end PartitionPilot.Forcing.PosetAction

end


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

open SetRealization Compression.RecursiveMaps SetFormula
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem separationName_hs (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (F : NormalSubgroupFamily G) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) {τ : Name s} (hτ : HereditarilySymmetric a s F τ)
    (params : ∀ i, HereditarilySymmetric a s F (env i).val) :
    HereditarilySymmetric a s F (Name.separationName D φ env τ) := by
  let K := a.stabilizer s τ ⊓ ⨅ i, a.stabilizer s (env i).val
  have hK : F.mem K := F.inf hτ.symmetric
    (F.fin_iInf (fun i => a.stabilizer s (env i).val) (fun i => (params i).symmetric))
  refine HereditarilySymmetric.mk (F.upward hK ?_) ?_
  · intro g hg
    have fixedτ : a.act s g τ = τ := hg.1
    have fixedEnv : a.actAssignment s D closed g env = env := by
      funext i
      apply Subtype.ext
      exact (iInf_le (fun j => a.stabilizer s (env j).val) i) hg.2
    change a.act s g (Name.separationName D φ env τ) = Name.separationName D φ env τ
    rw [a.act_separationName s D closed, fixedτ, fixedEnv]
  · intro σ p entry
    obtain ⟨r, old, _, _⟩ := (Name.entry_separationName D φ env τ σ p).1 entry
    exact hτ.member old

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem symmetricDomain_translated (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (g : G) {τ : Name s} (hτ : τ ∈ (a.symmetricDomain s D F).names) :
    a.act s g τ ∈ (a.symmetricDomain s D F).names :=
  ⟨closed g τ hτ.1, hτ.2.translated g⟩

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


section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem entry_codedPower [OrderTop P] (D : NameDomain s) (W : ZFSet.{u}) (σ : Name s) (p : P) :
    Entry σ (codedPower D W) p ↔ σ ∈ D.names ∧ σ.val ∈ W ∧ p = ⊤ := by
  rw [codedPower, entry_assemble]
  constructor
  · rintro ⟨i, rfl, rfl⟩
    exact ⟨i.val.property, i.property, rfl⟩
  · rintro ⟨hσ, hW, rfl⟩
    exact ⟨⟨⟨σ, hσ⟩, hW⟩, rfl, rfl⟩

theorem mem_eval_codedPower [OrderTop P] (D : NameDomain s) (W : ZFSet.{u})
    (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ eval {p | H.mem p} (codedPower D W) ↔
      ∃ σ ∈ D.names, σ.val ∈ W ∧ eval {p | H.mem p} σ = x := by
  rw [mem_eval]
  constructor
  · rintro ⟨σ, p, entry, _, eq⟩
    obtain ⟨hσ, hW, _⟩ := (entry_codedPower D W σ p).1 entry
    exact ⟨σ, hσ, hW, eq⟩
  · rintro ⟨σ, hσ, hW, eq⟩
    exact ⟨σ, ⊤, (entry_codedPower D W σ ⊤).2 ⟨hσ, hW, rfl⟩, H.top_mem, eq⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P)

theorem act_codedPower_fixed (D : Name.NameDomain s)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (W : ZFSet.{u}) (g : G)
    (invariant : ∀ σ ∈ D.names, (a.act s g σ).val ∈ W ↔ σ.val ∈ W) :
    a.act s g (Name.codedPower D W) = Name.codedPower D W := by
  apply Name.ext
  intro σ p
  obtain ⟨σ, rfl⟩ := (a.nameEquiv s g).surjective σ
  obtain ⟨p, rfl⟩ := (a.iso g).surjective p
  change Name.Entry (a.act s g σ) (a.act s g (Name.codedPower D W)) (a.iso g p) ↔ _
  rw [a.entry_act, Name.entry_codedPower, Name.entry_codedPower]
  constructor
  · rintro ⟨hσ, hW, rfl⟩
    exact ⟨closed g σ hσ, (invariant σ hσ).2 hW, (a.iso g).map_top⟩
  · rintro ⟨hσ, hW, hp⟩
    have old : σ ∈ D.names := by
      have h := closed g⁻¹ (a.act s g σ) hσ
      simpa only [a.act_inv_left] using h
    exact ⟨old, (invariant σ old).1 hW, (a.iso g).injective (hp.trans (a.iso g).map_top.symm)⟩

theorem codedPower_hs (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (W : ZFSet.{u}) (τ : Name s) (hτ : HereditarilySymmetric a s F τ)
    (bounded : ∀ σ ∈ (a.symmetricDomain s D F).names, σ.val ∈ W ↔ σ.val ⊆ τ.val) :
    HereditarilySymmetric a s F (Name.codedPower (a.symmetricDomain s D F) W) := by
  let E := a.symmetricDomain s D F
  have moved : ∀ g σ, σ ∈ E.names → a.act s g σ ∈ E.names :=
    fun g _ h => a.symmetricDomain_translated s D F closed g h
  refine HereditarilySymmetric.mk (F.upward hτ.symmetric ?_) ?_
  · intro g hg
    apply a.act_codedPower_fixed s E moved W g
    intro σ hσ
    rw [bounded _ (moved g σ hσ), bounded σ hσ]
    exact a.act_subset_iff_fixed s g hg
  · intro σ p entry
    exact ((Name.entry_codedPower E W σ p).1 entry).1.2

end PartitionPilot.Forcing.PosetAction

end


namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps SetFormula
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)
variable (D : Name.NameDomain s) (F : NormalSubgroupFamily G)

theorem symmetricDomain_nonempty (nonempty : D.names.Nonempty) :
    (a.symmetricDomain s D F).names.Nonempty :=
  ⟨Name.empty s, D.empty_mem nonempty, a.empty_hs s F⟩

theorem symmetric_values_pair [OrderTop P]
    (pairs : ∀ σ ∈ D.names, ∀ τ ∈ D.names, Name.unorderedPair ⊤ σ τ ∈ D.names)
    (H : ConditionFilter P) {x y : ZFSet.{u}}
    (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p})
    (hy : y ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ({x, y} : ZFSet.{u}) ∈ (a.symmetricDomain s D F).values {p | H.mem p} := by
  obtain ⟨σ, hσ, symσ, rfl⟩ := (a.mem_symmetric_values s D F _ x).1 hx
  obtain ⟨τ, hτ, symτ, rfl⟩ := (a.mem_symmetric_values s D F _ y).1 hy
  exact (a.mem_symmetric_values s D F _ _).2
    ⟨Name.unorderedPair ⊤ σ τ, pairs σ hσ τ hτ, symσ.unorderedPair symτ,
      Name.eval_unorderedPair _ ⊤ H.top_mem σ τ⟩

theorem symmetric_values_union
    (unions : ∀ τ ∈ D.names, Name.unionName τ ∈ D.names)
    (H : ConditionFilter P) {x : ZFSet.{u}}
    (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ZFSet.sUnion x ∈ (a.symmetricDomain s D F).values {p | H.mem p} := by
  obtain ⟨τ, hτ, symτ, rfl⟩ := (a.mem_symmetric_values s D F _ x).1 hx
  exact (a.mem_symmetric_values s D F _ _).2
    ⟨Name.unionName τ, unions τ hτ, a.unionName_hs s F symτ, Name.eval_unionName H τ⟩

theorem symmetric_values_separation
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s D F)))
    {n : Nat} (φ : SetFormula (n + 1)) (env : Assignment (a.symmetricDomain s D F) n)
    (separated : ∀ τ ∈ (a.symmetricDomain s D F).names,
      Name.separationName (a.symmetricDomain s D F) φ env τ ∈ D.names)
    {x : ZFSet.{u}} (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ZFSet.sep (fun z => Realize ((a.symmetricDomain s D F).values {p | H.mem p}) φ
      (extend z (evalAssignment {p | H.mem p} env))) x ∈
        (a.symmetricDomain s D F).values {p | H.mem p} := by
  obtain ⟨τ, hτ, rfl⟩ := ((a.symmetricDomain s D F).mem_values _ x).1 hx
  refine (a.mem_symmetric_values s D F _ _).2
    ⟨Name.separationName (a.symmetricDomain s D F) φ env τ, separated τ hτ, ?_, ?_⟩
  · exact a.separationName_hs s (a.symmetricDomain s D F)
      (fun g _ h => a.symmetricDomain_translated s D F closed g h) F φ env hτ.2
      (fun i => (env i).property.2)
  · exact Name.eval_separationName (a.symmetricDomain s D F) H generic φ env hτ

theorem symmetric_values_separation_params
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s D F)))
    {n : Nat} (φ : SetFormula (n + 1))
    (separated : ∀ (env : Assignment (a.symmetricDomain s D F) n)
      τ, τ ∈ (a.symmetricDomain s D F).names →
      Name.separationName (a.symmetricDomain s D F) φ env τ ∈ D.names)
    (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ (a.symmetricDomain s D F).values {p | H.mem p})
    {x : ZFSet.{u}} (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ZFSet.sep (fun z => Realize ((a.symmetricDomain s D F).values {p | H.mem p}) φ
      (extend z params)) x ∈ (a.symmetricDomain s D F).values {p | H.mem p} := by
  classical
  have reps := fun i => ((a.symmetricDomain s D F).mem_values _ (params i)).1 (members i)
  choose names inDomain values using reps
  let env : Assignment (a.symmetricDomain s D F) n := fun i => ⟨names i, inDomain i⟩
  have evals : evalAssignment {p | H.mem p} env = params := funext values
  have h := a.symmetric_values_separation s D F closed H generic φ env (separated env) hx
  rw [evals] at h
  exact h

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

theorem mem_orbitCodes_of_mem (D : Name.NameDomain s) {W : ZFSet.{u}} {σ : Name s}
    (hσ : σ ∈ D.names) (hW : σ.val ∈ W) : σ.val ∈ a.orbitCodes s D W := by
  exact (a.mem_orbitCodes s D W σ.val).2 ⟨1, σ, hσ, hW, congrArg Subtype.val (a.act_one s σ).symm⟩

theorem act_mem_orbitCodes_iff (D : Name.NameDomain s) (W : ZFSet.{u}) (g : G) (σ : Name s) :
    (a.act s g σ).val ∈ a.orbitCodes s D W ↔ σ.val ∈ a.orbitCodes s D W := by
  rw [a.mem_orbitCodes, a.mem_orbitCodes]
  constructor
  · rintro ⟨h, τ, hτ, hW, eq⟩
    have names : a.act s g σ = a.act s h τ := Subtype.ext eq
    refine ⟨g⁻¹ * h, τ, hτ, hW, ?_⟩
    rw [a.act_mul, ← names, a.act_inv_left]
  · rintro ⟨h, τ, hτ, hW, eq⟩
    have names : σ = a.act s h τ := Subtype.ext eq
    refine ⟨g * h, τ, hτ, hW, ?_⟩
    rw [names, a.act_mul]

theorem orbitCodedPower_hs [OrderTop P] (D : Name.NameDomain s) (F : NormalSubgroupFamily G)
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names) (W : ZFSet.{u}) :
    HereditarilySymmetric a s F (Name.codedPower (a.symmetricDomain s D F) (a.orbitCodes s D W)) := by
  let E := a.symmetricDomain s D F
  refine HereditarilySymmetric.mk (F.upward F.top ?_) ?_
  · intro g _
    apply a.act_codedPower_fixed s E (fun h _ hx => a.symmetricDomain_translated s D F closed h hx)
      (a.orbitCodes s D W) g
    exact fun σ _ => a.act_mem_orbitCodes_iff s D W g σ
  · intro σ p entry
    exact ((Name.entry_codedPower E (a.orbitCodes s D W) σ p).1 entry).1.2

end PartitionPilot.Forcing.PosetAction

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_UnionEntryFormula
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} {s : Presentation P}

theorem realize_pairing (U : Set ZFSet.{u})
    (pairs : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U) :
    Realize U pairing Fin.elim0 := by
  simp only [pairing, realize_ex, realize_imp, realize_disj, Realize]
  intro x hx y hy
  refine ⟨{x, y}, pairs x hx y hy, ?_⟩
  intro z _
  exact ⟨ZFSet.mem_pair.1, ZFSet.mem_pair.2⟩

theorem realize_union (D : Name.NameDomain s) (H : Set P)
    (unions : ∀ x ∈ D.values H, ZFSet.sUnion x ∈ D.values H) :
    Realize (D.values H) union Fin.elim0 := by
  simp only [union, realize_ex, realize_imp, Realize]
  intro x hx
  refine ⟨ZFSet.sUnion x, unions x hx, ?_⟩
  intro z _
  constructor
  · intro member
    obtain ⟨w, wx, zw⟩ := ZFSet.mem_sUnion.1 member
    exact ⟨w, D.values_transitive H hx wx, wx, zw⟩
  · rintro ⟨w, _, wx, zw⟩
    exact ZFSet.mem_sUnion.2 ⟨w, wx, zw⟩

variable {G : Type v} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (D : Name.NameDomain s) (F : NormalSubgroupFamily G)

theorem realize_symmetric_pairing [OrderTop P]
    (pairs : ∀ σ ∈ D.names, ∀ τ ∈ D.names, Name.unorderedPair ⊤ σ τ ∈ D.names)
    (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s D F).values {p | H.mem p}) pairing Fin.elim0 :=
  realize_pairing _ (fun _ hx _ hy => a.symmetric_values_pair s D F pairs H hx hy)

theorem realize_symmetric_union
    (unions : ∀ τ ∈ D.names, Name.unionName τ ∈ D.names) (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s D F).values {p | H.mem p}) union Fin.elim0 :=
  realize_union _ _ (fun _ hx => a.symmetric_values_union s D F unions H hx)

theorem symmetric_separation_scheme
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s D F)))
    (separated : ∀ {n} (φ : SetFormula (n + 1))
      (env : Assignment (a.symmetricDomain s D F) n) τ,
      τ ∈ (a.symmetricDomain s D F).names →
      Name.separationName (a.symmetricDomain s D F) φ env τ ∈ D.names)
    {n : Nat} (φ : SetFormula (n + 1)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ (a.symmetricDomain s D F).values {p | H.mem p})
    {x : ZFSet.{u}} (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ∃ y ∈ (a.symmetricDomain s D F).values {p | H.mem p},
      ∀ z, z ∈ y ↔ z ∈ x ∧
        Realize ((a.symmetricDomain s D F).values {p | H.mem p}) φ (extend z params) := by
  refine ⟨ZFSet.sep (fun z => Realize ((a.symmetricDomain s D F).values {p | H.mem p})
      φ (extend z params)) x,
    a.symmetric_values_separation_params s D F closed H generic φ (separated φ) params members hx,
    ?_⟩
  intro z
  exact ZFSet.mem_sep

end PartitionPilot.Forcing.SetFormula



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u})

variable {P : Type u} (s : Presentation P)

theorem pairName_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (one : P) (hone : s.encode one ∈ M.sets) {σ τ : Name s}
    (hσ : σ ∈ (M.nameDomain s).names) (hτ : τ ∈ (M.nameDomain s).names) :
    Name.unorderedPair one σ τ ∈ (M.nameDomain s).names := by
  change (Name.unorderedPair one σ τ).val ∈ M.sets
  rw [pairName_code]
  exact M.unorderedPair_mem pairing (M.orderedPair_mem pairing hσ hone)
    (M.orderedPair_mem pairing hτ hone)

theorem symmetric_pairing {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p})
      SetFormula.pairing Fin.elim0 :=
  realize_symmetric_pairing a (M.nameDomain s) F
    (fun _ hσ _ hτ => M.pairName_mem s pairing ⊤
      (M.transitive carrier (s.encode_mem ⊤)) hσ hτ) H

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_unionEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (env : Fin 4 → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets unionEntryFormula env ↔
      ∃ x ∈ M.sets, ∃ p ∈ M.sets, ∃ ν ∈ M.sets, ∃ r ∈ M.sets, ∃ q ∈ M.sets,
        env 0 = ZFSet.pair x p ∧ p ∈ env 2 ∧ r ∈ env 2 ∧ q ∈ env 2 ∧
        ZFSet.pair ν r ∈ env 1 ∧ ZFSet.pair x q ∈ ν ∧
        ZFSet.pair p r ∈ env 3 ∧ ZFSet.pair p q ∈ env 3 := by
  simp only [unionEntryFormula, realize_ex]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  apply exists_congr
  intro ν
  apply and_congr_right
  intro hν
  apply exists_congr
  intro r
  apply and_congr_right
  intro hr
  apply exists_congr
  intro q
  apply and_congr_right
  intro hq
  let e := extend q (extend r (extend ν (extend p (extend x env))))
  change (Realize M.sets (orderedPairFormula 5 4 3) e ∧ p ∈ env 2 ∧ r ∈ env 2 ∧ q ∈ env 2 ∧
    Realize M.sets (pairMembershipFormula 2 1 6) e ∧
    Realize M.sets (pairMembershipFormula 4 0 2) e ∧
    Realize M.sets (pairMembershipFormula 3 1 8) e ∧
    Realize M.sets (pairMembershipFormula 3 0 8) e) ↔ _
  rw [M.realize_orderedPairFormula pairing 5 4 3 e (members 0) hx hp,
    M.realize_pairMembershipFormula pairing 2 1 6 e hν hr (members 1),
    M.realize_pairMembershipFormula pairing 4 0 2 e hx hq hν,
    M.realize_pairMembershipFormula pairing 3 1 8 e hp hr (members 3),
    M.realize_pairMembershipFormula pairing 3 0 8 e hp hq (members 3)]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.Name

open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem mem_eval_codedPower_iff (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (separated : ∀ {n} (φ : SetFormula (n + 1)) (env : Assignment D n) τ,
      τ ∈ D.names → separationName D φ env τ ∈ D.names)
    (τ : D.names) (W : ZFSet.{u})
    (bounded : ∀ σ ∈ D.names, σ.val ∈ W ↔ σ.val ⊆ (envelope τ.val).val)
    (z : ZFSet.{u}) (hz : z ∈ D.values {p | H.mem p}) :
    z ∈ eval {p | H.mem p} (codedPower D W) ↔ z ⊆ eval {p | H.mem p} τ.val := by
  rw [mem_eval_codedPower]
  constructor
  · rintro ⟨σ, hσ, hW, rfl⟩
    have sub := eval_mono {p | H.mem p} ((bounded σ hσ).1 hW)
    rwa [eval_envelope] at sub
  · intro sub
    obtain ⟨ν, hν, value⟩ := (NameDomain.mem_values D _ z).1 hz
    let env : Assignment D 1 := extend ⟨ν, hν⟩ Fin.elim0
    let σ := separationName D (.mem 0 1) env τ.val
    have hσ : σ ∈ D.names := separated (.mem 0 1) env τ.val τ.property
    refine ⟨σ, hσ, (bounded σ hσ).2 (selectName_subset_envelope _ _), ?_⟩
    change eval {p | H.mem p} (separationName D (.mem 0 1) env τ.val) = z
    rw [eval_separationName D H generic (.mem 0 1) env τ.property]
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    change (x ∈ eval {p | H.mem p} τ.val ∧ x ∈ eval {p | H.mem p} ν) ↔ x ∈ z
    rw [value]
    exact ⟨And.right, fun hx => ⟨sub hx, hx⟩⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.SetFormula

universe u

theorem realize_powerSet_of_witnesses (U : Set ZFSet.{u})
    (transitive : ∀ x ∈ U, ∀ z ∈ x, z ∈ U)
    (witnesses : ∀ x ∈ U, ∃ y ∈ U, ∀ z ∈ U, z ∈ y ↔ z ⊆ x) :
    Realize U powerSet Fin.elim0 := by
  simp only [powerSet, realize_ex, realize_imp, Realize]
  intro x hx
  obtain ⟨y, hy, spec⟩ := witnesses x hx
  refine ⟨y, hy, ?_⟩
  intro z hz
  constructor
  · intro zy w _ wz
    exact (spec z hz).1 zy wz
  · intro sub
    exact (spec z hz).2 (fun w hw => sub w (transitive z hz w hw) hw)

end PartitionPilot.Forcing.SetFormula

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_DecodedFunctionGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u}) {A B : Type u}

theorem decoded_function_graph_mem (s : Presentation A) (t : Presentation B) {f : ZFSet.{u}}
    (hf : f ∈ M.sets) (h : ZFSet.IsFunc s.carrier t.carrier f) :
    s.graph t (s.decodeFunction t f h) ∈ M.sets := by
  rw [s.graph_decodeFunction]
  exact hf

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ConditionQuantifiers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization
open scoped ZFSet
universe u
variable {P : Type u} {s : Presentation P}

theorem grandchild_mem_bound {σ ν τ : Name s} {r q : P}
    (outer : Entry ν τ r) (inner : Entry σ ν q) : σ.val ∈ grandchildrenBound τ := by
  have h₁ : ({ν.val} : ZFSet.{u}) ∈ ⋃₀ τ.val :=
    ZFSet.mem_sUnion.2 ⟨ZFSet.pair ν.val (s.encode r), outer, ZFSet.mem_pair.2 (Or.inl rfl)⟩
  have h₂ : ν.val ∈ ⋃₀ (⋃₀ τ.val) :=
    ZFSet.mem_sUnion.2 ⟨{ν.val}, h₁, ZFSet.mem_singleton.2 rfl⟩
  have h₃ : ZFSet.pair σ.val (s.encode q) ∈ ⋃₀ (⋃₀ (⋃₀ τ.val)) :=
    ZFSet.mem_sUnion.2 ⟨ν.val, h₂, inner⟩
  have h₄ : ({σ.val} : ZFSet.{u}) ∈ ⋃₀ (⋃₀ (⋃₀ (⋃₀ τ.val))) :=
    ZFSet.mem_sUnion.2 ⟨ZFSet.pair σ.val (s.encode q), h₃, ZFSet.mem_pair.2 (Or.inl rfl)⟩
  exact ZFSet.mem_sUnion.2 ⟨{σ.val}, h₄, ZFSet.mem_singleton.2 rfl⟩

theorem unionName_subset_bound [Preorder P] (τ : Name s) (C : ZFSet.{u})
    (bound : ∀ x ∈ grandchildrenBound τ, ∀ y ∈ s.carrier, ZFSet.pair x y ∈ C) :
    (unionName τ).val ⊆ C := by
  intro z hz
  obtain ⟨σ, p, rfl⟩ := entries_cover (unionName τ) hz
  obtain ⟨ν, r, q, outer, inner, _, _⟩ := (entry_unionName τ σ p).1 hz
  exact bound σ.val (grandchild_mem_bound outer inner) (s.encode p) (s.encode_mem p)

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem grandchildrenBound_mem (unions : Realize M.sets SetFormula.union Fin.elim0)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) : Name.grandchildrenBound τ ∈ M.sets :=
  M.union_mem unions (M.union_mem unions (M.union_mem unions (M.union_mem unions (M.union_mem unions hτ))))

theorem exists_unionName_bound [Preorder P]
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (carrier : s.carrier ∈ M.sets)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) :
    ∃ C ∈ M.sets, (Name.unionName τ).val ⊆ C := by
  obtain ⟨C, hC, bound⟩ := M.exists_pair_bound pairing unions powers
    (M.grandchildrenBound_mem s unions hτ) carrier
  exact ⟨C, hC, Name.unionName_subset_bound τ C bound⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem unionEntryParams_mem (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) :
    ∀ i, Name.unionEntryParams τ i ∈ M.sets := by
  intro i
  refine Fin.cases hτ (fun j => ?_) i
  refine Fin.cases carrier (fun k => ?_) j
  exact Fin.cases order (fun l => Fin.elim0 l) k

theorem unionEntry_iff_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) {z : ZFSet.{u}} (hz : z ∈ M.sets) :
    Realize M.sets unionEntryFormula (extend z (Name.unionEntryParams τ)) ↔
      z ∈ (Name.unionName τ).val := by
  have members : ∀ i, extend z (Name.unionEntryParams τ) i ∈ M.sets :=
    fun i => Fin.cases hz (M.unionEntryParams_mem s carrier order hτ) i
  rw [M.realize_unionEntryFormula pairing _ members]
  change (∃ x ∈ M.sets, ∃ p ∈ M.sets, ∃ ν ∈ M.sets, ∃ r ∈ M.sets, ∃ q ∈ M.sets,
    z = ZFSet.pair x p ∧ p ∈ s.carrier ∧ r ∈ s.carrier ∧ q ∈ s.carrier ∧
    ZFSet.pair ν r ∈ τ.val ∧ ZFSet.pair x q ∈ ν ∧
    ZFSet.pair p r ∈ s.conditionOrder ∧ ZFSet.pair p q ∈ s.conditionOrder) ↔ _
  constructor
  · rintro ⟨x, _, pc, _, v, _, rc, _, qc, _, eq, hp, hr, hq, outer, inner, pr, pq⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier pc).1 hp
    obtain ⟨r, rfl⟩ := (s.mem_carrier rc).1 hr
    obtain ⟨q, rfl⟩ := (s.mem_carrier qc).1 hq
    let ν : Name s := ⟨v, Name.isName_of_pair_mem τ v r outer⟩
    let σ : Name s := ⟨x, Name.isName_of_pair_mem ν x q inner⟩
    rw [eq]
    change Name.Entry σ (Name.unionName τ) p
    exact (Name.entry_unionName τ σ p).2
      ⟨ν, r, q, outer, inner, (s.pair_mem_conditionOrder p r).1 pr,
        (s.pair_mem_conditionOrder p q).1 pq⟩
  · intro member
    obtain ⟨σ, p, rfl⟩ := Name.entries_cover (Name.unionName τ) member
    obtain ⟨ν, r, q, outer, inner, pr, pq⟩ := (Name.entry_unionName τ σ p).1 member
    have hν := (M.nameDomain s).children hτ outer
    have hσ := (M.nameDomain s).children hν inner
    exact ⟨σ.val, hσ, s.encode p, M.transitive carrier (s.encode_mem p),
      ν.val, hν, s.encode r, M.transitive carrier (s.encode_mem r),
      s.encode q, M.transitive carrier (s.encode_mem q), rfl,
      s.encode_mem p, s.encode_mem r, s.encode_mem q, outer, inner,
      (s.pair_mem_conditionOrder p r).2 pr, (s.pair_mem_conditionOrder p q).2 pq⟩

theorem unionName_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {τ : Name s} (hτ : τ ∈ (M.nameDomain s).names) :
    Name.unionName τ ∈ (M.nameDomain s).names := by
  obtain ⟨C, hC, bound⟩ := M.exists_unionName_bound s pairing unions powers carrier hτ
  have selected := M.separation_mem separation unionEntryFormula (Name.unionEntryParams τ)
    (M.unionEntryParams_mem s carrier order hτ) hC
  have eq : ZFSet.sep (fun z => Realize M.sets unionEntryFormula
      (extend z (Name.unionEntryParams τ))) C = (Name.unionName τ).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, formula⟩
      exact (M.unionEntry_iff_mem s pairing carrier order hτ (M.transitive hC hz)).1 formula
    · intro hz
      exact ⟨bound hz,
        (M.unionEntry_iff_mem s pairing carrier order hτ (M.transitive hC (bound hz))).2 hz⟩
  change (Name.unionName τ).val ∈ M.sets
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] (s : Presentation P)

theorem symmetric_union {G : Type v} [Group G]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p})
      SetFormula.union Fin.elim0 :=
  realize_symmetric_union a (M.nameDomain s) F
    (fun _ hτ => M.unionName_mem s pairing unions powers separation carrier order hτ) H

end PartitionPilot.Forcing.TransitiveGround

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

theorem codedFamily_of_code {E : Set P} (code : s.subset E ∈ M.sets) : E ∈ M.codedFamily s := by
  refine ⟨s.subset E, code, ?_⟩
  apply Set.ext
  intro p
  exact s.encode_mem_subset E p

end TransitiveGround



section
open SetRealization
universe u

namespace SetFormula
variable {P : Type u} [Preorder P] [Countable P] {s : Presentation P}

theorem forces_iff_all_generics (D : Name.NameDomain s) (small : D.names.Countable)
    {n : Nat} (phi : SetFormula n) (env : Assignment D n) (p : P) :
    Forces D phi env p ↔
      ∀ H : ConditionFilter P, H.mem p → H.GenericFor (formulaFamily D) →
        Realize (D.values {q | H.mem q}) phi (evalAssignment {q | H.mem q} env) := by
  constructor
  · intro forced H member generic
    exact forces_sound D H generic phi env member forced
  · intro truth
    by_contra bad
    obtain ⟨q, below, negative⟩ := not_forces_refine_neg D phi env bad
    obtain ⟨H, member, generic⟩ := exists_generic_formulaFamily D small q
    have yes := truth H (H.upward member below) generic
    have no := forces_sound D H generic (.neg phi) env member negative
    exact no yes

end SetFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem ordinaryForces_iff_all_generics (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (p : P) :
    Forces (M.nameDomain s) phi env p ↔
      ∀ H : ConditionFilter P, H.mem p → H.GenericFor (formulaFamily (M.nameDomain s)) →
        Realize ((M.nameDomain s).values {q | H.mem q}) phi
          (evalAssignment {q | H.mem q} env) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  exact forces_iff_all_generics (M.nameDomain s) (M.nameDomain_countable s small) phi env p

end TransitiveGround
end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProductActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem identityPosetAction_graph_eq {G P : Type u} [Group G] [PartialOrder P]
    (s : Presentation P) (g : G) :
    s.graph s ((identityPosetAction G P).iso g) = identityFunctionGraph s.carrier := by
  apply ZFSet.ext
  intro z
  rw [s.mem_graph, mem_identityFunctionGraph]
  constructor
  · rintro ⟨p, eq⟩
    exact ⟨s.encode p, s.encode_mem p, eq.symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    exact ⟨p, rfl⟩

theorem identityPosetAction_conditionMapFamily {P : Type u} [PartialOrder P]
    (s : Presentation P) :
    (identityPosetAction (Equiv.Perm (ULift.{u} Unit)) P).conditionMapFamily
      s trivialGroupPresentation = {ZFSet.pair ∅ (identityFunctionGraph s.carrier)} := by
  apply ZFSet.ext
  intro z
  rw [PosetAction.conditionMapFamily, ZFSet.mem_range, ZFSet.mem_singleton]
  constructor
  · rintro ⟨g, eq⟩
    change ZFSet.pair ∅ (s.graph s ((identityPosetAction _ P).iso g)) = z at eq
    rw [identityPosetAction_graph_eq] at eq
    exact eq.symm
  · intro eq
    refine ⟨1, ?_⟩
    change ZFSet.pair ∅ (s.graph s ((identityPosetAction (Equiv.Perm (ULift.{u} Unit)) P).iso 1)) = z
    rw [identityPosetAction_graph_eq]
    exact eq.symm

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem trivialGroupPresentation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (nonempty : M.sets.Nonempty) :
    trivialGroupPresentation.carrier ∈ M.sets := by
  change ({∅} : ZFSet.{u}) ∈ M.sets
  simpa only [ZFSet.pair_eq_singleton] using
    M.unorderedPair_mem pairing (M.empty_mem nonempty) (M.empty_mem nonempty)

theorem identityPosetAction_conditionMapFamily_mem {P : Type u} [PartialOrder P]
    (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) :
    (identityPosetAction (Equiv.Perm (ULift.{u} Unit)) P).conditionMapFamily
      s trivialGroupPresentation ∈ M.sets := by
  rw [identityPosetAction_conditionMapFamily]
  have entry := M.orderedPair_mem pairing (M.empty_mem ⟨s.carrier, carrier⟩)
    (M.identityFunctionGraph_mem pairing unions powers separation carrier)
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing entry entry

end TransitiveGround

end PartitionPilot.Forcing


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_SymmetricGroundForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem realize_nameSymmetryFormula (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) :
    Realize M.sets nameSymmetryFormula (extend τ.val (symmetryParameters a s t b K)) ↔
      F.mem (a.stabilizer s τ) := by
  let env := extend τ.val (symmetryParameters a s t b K)
  rw [basis (a.stabilizer s τ), nameSymmetryFormula,
    M.realize_exConditions b 3 _ env indices rfl]
  apply exists_congr
  intro i
  rw [M.realize_allConditions t 3 _ (extend (b.encode i) env) group rfl]
  change (∀ g, Realize M.sets _ _) ↔ ∀ g, g ∈ K i → a.act s g τ = τ
  apply forall_congr'
  intro g
  let e := extend (t.encode g) (extend (b.encode i) env)
  rw [realize_imp, M.realize_pairMembershipFormula pairing 1 0 6 e
    (M.transitive indices (b.encode_mem i)) (M.transitive group (t.encode_mem g)) supports]
  change (ZFSet.pair (b.encode i) (t.encode g) ∈ supportBasisCode b t K → Realize M.sets _ e) ↔ _
  rw [pair_mem_supportBasisCode]
  apply forall_congr'
  intro _
  rw [realize_atomicApplication, map_extend, map_extend, map_empty]
  exact M.realize_nameActionFormula a s t pairing unions powers separation collection carrier group maps g τ τ hτ hτ

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem realize_hereditaryStepFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    (params : Fin 5 → ZFSet.{u}) (hc : params 0 = s.carrier)
    (x R : ZFSet.{u}) (hx : x ∈ M.sets) (hr : R ∈ M.sets) :
    Realize M.sets hereditaryStepFormula (extend x (extend R params)) ↔
      Realize M.sets nameSymmetryFormula (extend x params) ∧ NameCodeStep s R x := by
  change (Realize M.sets _ _ ∧ Realize M.sets _ _) ↔ _
  rw [realize_domainApplication, realize_binaryApplication, map_extend, map_empty]
  change (Realize M.sets nameSymmetryFormula (extend x params) ∧
    Realize M.sets nameCodeStepFormula (extend x (extend R (extend (params 0) Fin.elim0)))) ↔ _
  rw [hc, M.realize_nameCodeStepFormula s pairing carrier x R hx hr]

theorem hereditaryCertificate_isName
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (carrier : s.carrier ∈ M.sets)
    (params : Fin 5 → ZFSet.{u}) (hc : params 0 = s.carrier)
    {R : ZFSet.{u}} (hr : R ∈ M.sets)
    (certificate : Realize M.sets hereditaryCertificateFormula (extend R params)) :
    ∀ x ∈ R, IsName s x := by
  apply nameCodePostfixed_sound s R
  intro x hx
  exact ((M.realize_hereditaryStepFormula s pairing carrier params hc x R (M.transitive hr hx) hr).1
    ((realize_imp M.sets _ _ _).1 (certificate x (M.transitive hr hx)) hx)).2

variable {I G : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (t : Presentation G) (b : Presentation I)

theorem hereditaryCertificate_sound (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {R : ZFSet.{u}} (hr : R ∈ M.sets)
    (certificate : Realize M.sets hereditaryCertificateFormula (extend R (symmetryParameters a s t b K))) :
    ∀ τ : Name s, τ.val ∈ R → HereditarilySymmetric a s F τ := by
  intro τ
  induction τ using Name.inductionOn with
  | step τ ih =>
    intro hτ
    have hτM := M.transitive hr hτ
    have step := (M.realize_hereditaryStepFormula s pairing carrier (symmetryParameters a s t b K)
      rfl τ.val R hτM hr).1 ((realize_imp M.sets _ _ _).1 (certificate τ.val hτM) hτ)
    apply HereditarilySymmetric.mk
    · exact (M.realize_nameSymmetryFormula a s t b F K basis pairing unions powers separation collection
        carrier group indices supports maps τ hτM).1 step.1
    · intro σ p entry
      obtain ⟨x, hx, q, shape⟩ := step.2 _ entry
      have eq := (ZFSet.pair_inj.1 shape).1
      exact ih σ p entry (eq ▸ hx)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem exists_hereditary_certificate (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) (hs : HereditarilySymmetric a s F τ) :
    ∃ R ∈ M.sets, Realize M.sets hereditaryCertificateFormula
      (extend R (symmetryParameters a s t b K)) ∧ τ.val ∈ R := by
  obtain ⟨T, hT, τT, trans⟩ := M.exists_transitiveCover pairing unions separation collection τ.val hτ
  let D := a.symmetricDomain s (namesInTransitiveSet s T (fun hx hy => trans _ hx _ hy)) F
  let params := symmetryParameters a s t b K
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases carrier (Fin.cases group (Fin.cases indices (Fin.cases supports
      (Fin.cases maps (fun i => Fin.elim0 i)))))
  have mono : ∀ R ∈ M.sets, ∀ S ∈ M.sets, R ⊆ T → S ⊆ T → R ⊆ S →
      definableOperator M.sets hereditaryStepFormula params T R ⊆
        definableOperator M.sets hereditaryStepFormula params T S := by
    intro R hr S hS _ _ sub x hx
    obtain ⟨hxT, step⟩ := ZFSet.mem_sep.1 hx
    have hxM := M.transitive hT hxT
    obtain ⟨sym, children⟩ := (M.realize_hereditaryStepFormula s pairing carrier params rfl x R hxM hr).1 step
    exact ZFSet.mem_sep.2 ⟨hxT, (M.realize_hereditaryStepFormula s pairing carrier params rfl x S hxM hS).2
      ⟨sym, nameCodeStep_mono s sub children⟩⟩
  obtain ⟨R, hr, bound, fixed, _⟩ := M.exists_greatest_definable_fixedPoint unions powers separation
    hereditaryStepFormula params members hT mono
  have certificate : Realize M.sets hereditaryCertificateFormula (extend R params) := by
    apply (M.realize_postfixedFormula hereditaryStepFormula params hr bound).2
    rw [fixed]
  have pre : ∀ ν ∈ D.names, NameCodeStep s R ν.val → ν.val ∈ R := by
    intro ν hν step
    have hνM := M.transitive hT hν.1
    have sym := (M.realize_nameSymmetryFormula a s t b F K basis pairing unions powers separation collection
      carrier group indices supports maps ν hνM).2 hν.2.symmetric
    have member : ν.val ∈ definableOperator M.sets hereditaryStepFormula params T R :=
      ZFSet.mem_sep.2 ⟨hν.1,
        (M.realize_hereditaryStepFormula s pairing carrier params rfl ν.val R hνM hr).2 ⟨sym, step⟩⟩
    rwa [fixed] at member
  exact ⟨R, hr, certificate, nameCodePrefixed_complete s D R pre τ ⟨τT, hs⟩⟩

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem realize_uniformHereditaryFormula (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (x : ZFSet.{u}) (hx : x ∈ M.sets) :
    Realize M.sets uniformHereditaryFormula (extend x (symmetryParameters a s t b K)) ↔
      ∃ h : IsName s x, HereditarilySymmetric a s F ⟨x, h⟩ := by
  rw [uniformHereditaryFormula, realize_ex]
  constructor
  · rintro ⟨R, hr, certificate, member⟩
    have cert := (realize_domainApplication M.sets hereditaryCertificateFormula _ _ _).1 certificate
    have name := M.hereditaryCertificate_isName s pairing carrier (symmetryParameters a s t b K) rfl hr cert x member
    exact ⟨name, M.hereditaryCertificate_sound s a t b F K basis pairing unions powers separation collection
      carrier group indices supports maps hr cert ⟨x, name⟩ member⟩
  · rintro ⟨name, hs⟩
    obtain ⟨R, hr, certificate, member⟩ := M.exists_hereditary_certificate a s t b F K basis
      pairing unions powers separation collection carrier group indices supports maps ⟨x, name⟩ hx hs
    exact ⟨R, hr, (realize_domainApplication M.sets hereditaryCertificateFormula _ _ _).2 certificate, member⟩

theorem domainMeaning_liftedHereditary (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {k : Nat} (c g i j l : Fin k) (constants : Fin k → ZFSet.{u})
    (hc : constants c = s.carrier) (hg : constants g = t.carrier) (hi : constants i = b.carrier)
    (hj : constants j = supportBasisCode b t K) (hl : constants l = a.conditionMapFamily s t) :
    M.DomainMeaning s (a.symmetricDomain s (M.nameDomain s) F)
      (liftedHereditaryFormula c g i j l) constants := by
  intro x hx
  rw [liftedHereditaryFormula, realize_domainApplication,
    map_extend, map_extend, map_extend, map_extend, map_extend, map_empty]
  change Realize M.sets uniformHereditaryFormula (extend x
    (extend (constants c) (extend (constants g) (extend (constants i)
      (extend (constants j) (extend (constants l) Fin.elim0)))))) ↔ _
  rw [hc, hg, hi, hj, hl]
  change Realize M.sets uniformHereditaryFormula (extend x (symmetryParameters a s t b K)) ↔ _
  rw [M.realize_uniformHereditaryFormula a s t b F K basis pairing unions powers separation collection
      carrier group indices supports maps x hx]
  constructor
  · rintro ⟨name, hs⟩
    exact ⟨⟨⟨x, name⟩, hx, hs⟩, rfl⟩
  · rintro ⟨τ, rfl⟩
    exact ⟨τ.val.property, τ.property.2⟩

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


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetricSeparationName_mem (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {n : Nat} (φ : SetFormula (n + 1))
    (nameEnv : Assignment (a.symmetricDomain s (M.nameDomain s) F) n)
    (τ : (a.symmetricDomain s (M.nameDomain s) F).names) :
    (Name.separationName (a.symmetricDomain s (M.nameDomain s) F) φ nameEnv τ.val).val ∈ M.sets := by
  let D := a.symmetricDomain s (M.nameDomain s) F
  let context := extend s.carrier (extend s.conditionOrder (extend t.carrier (extend b.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) (fun i => (nameEnv i).val.val))))))
  let params : Fin 6 → Fin (n + 6) := extend 0 (extend 1 (extend 2 (extend 3 (extend 4 (extend 5 Fin.elim0)))))
  have members : ∀ i, context i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (Fin.cases group (Fin.cases indices (Fin.cases supports
      (Fin.cases maps (fun i => (nameEnv i).property.1))))))
  apply M.separationName_mem s D (fun _ h => h.1) pairing unions powers separation carrier order
    symmetricGroundPrimitives φ params (fun i => i.succ.succ.succ.succ.succ.succ) context members rfl rfl
  · exact M.equalityMeaning_lifted s D (fun _ h => h.1) pairing unions powers separation collection
      carrier order 0 1 _ rfl rfl
  · exact M.domainMeaning_liftedHereditary a s t b F K basis pairing unions powers separation collection
      carrier group indices supports maps 0 2 3 4 5 _ rfl rfl rfl rfl rfl
  · exact fun _ => rfl

theorem symmetric_separation (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F))) :
    SeparationSchema ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) := by
  intro n φ params members x hx
  obtain ⟨y, hy, spec⟩ := symmetric_separation_scheme a (M.nameDomain s) F
    (fun g τ hτ => M.act_mem s a t pairing unions powers separation collection carrier maps g τ hτ)
    H generic (fun ψ env τ hτ => M.symmetricSeparationName_mem a s t b F K basis
      pairing unions powers separation collection carrier order group indices supports maps ψ env ⟨τ, hτ⟩)
    φ params members hx
  exact ⟨y, hy, fun z _ => spec z⟩

end PartitionPilot.Forcing.TransitiveGround


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSymmetricPowerSet
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
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P] (s : Presentation P)

theorem realize_codedPowerEntryFormula (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {k m : Nat} (N : SetFormula (k + 1)) (params : Fin k → Fin m) (zi wi ti : Fin m)
    (env : Fin m → ZFSet.{u})
    (domain : M.DomainMeaning s D N (fun j => env (params j)))
    (top : env ti = s.encode ⊤) (htop : env ti ∈ M.sets) (hz : env zi ∈ M.sets) :
    Realize M.sets (codedPowerEntryFormula N params zi wi ti) env ↔
      env zi ∈ (Name.codedPower D (env wi)).val := by
  rw [codedPowerEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, hW, name, shape⟩
    rw [realize_domainApplication] at name
    obtain ⟨σ, rfl⟩ := (domain x hx).1 name
    have eq := (M.realize_orderedPairFormula pairing zi.succ 0 ti.succ
      (extend σ.val.val env) hz hx htop).1 shape
    change env zi = ZFSet.pair σ.val.val (env ti) at eq
    rw [eq, top]
    exact (Name.entry_codedPower D (env wi) σ.val ⊤).2 ⟨σ.property, hW, rfl⟩
  · intro member
    obtain ⟨σ, p, eq⟩ := Name.entries_cover (Name.codedPower D (env wi)) member
    have entry : Name.Entry σ (Name.codedPower D (env wi)) p := by
      change ZFSet.pair σ.val (s.encode p) ∈ (Name.codedPower D (env wi)).val
      rwa [← eq]
    obtain ⟨hσ, hW, rfl⟩ := (Name.entry_codedPower D (env wi) σ p).1 entry
    refine ⟨σ.val, ground σ hσ, hW, ?_, ?_⟩
    · rw [realize_domainApplication]
      exact (domain σ.val (ground σ hσ)).2 ⟨⟨σ, hσ⟩, rfl⟩
    · apply (M.realize_orderedPairFormula pairing zi.succ 0 ti.succ
        (extend σ.val env) hz (ground σ hσ) htop).2
      change env zi = ZFSet.pair σ.val (env ti)
      rwa [top]

theorem codedPower_mem (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets)
    {k : Nat} (N : SetFormula (k + 1)) (params : Fin k → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) (domain : M.DomainMeaning s D N params)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) : (Name.codedPower D W).val ∈ M.sets := by
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hW carrier
  have bound : (Name.codedPower D W).val ⊆ B := by
    intro z hz
    obtain ⟨σ, p, rfl⟩ := Name.entries_cover (Name.codedPower D W) hz
    obtain ⟨_, hσ, _⟩ := (Name.entry_codedPower D W σ p).1 hz
    exact pairBound σ.val hσ (s.encode p) (s.encode_mem p)
  let formula := codedPowerEntryFormula N (fun j => j.succ.succ.succ) 0 1 2
  let context := extend W (extend (s.encode ⊤) params)
  have htop := M.transitive carrier (s.encode_mem ⊤)
  have correct : ∀ z ∈ M.sets, Realize M.sets formula (extend z context) ↔
      z ∈ (Name.codedPower D W).val := by
    intro z hz
    exact M.realize_codedPowerEntryFormula s D ground pairing N (fun j => j.succ.succ.succ)
      0 1 2 (extend z context) domain rfl htop hz
  have selected := M.separation_mem separation formula context
    (Fin.cases hW (Fin.cases htop members)) hB
  have eq : ZFSet.sep (fun z => Realize M.sets formula (extend z context)) B =
      (Name.codedPower D W).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (correct z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (correct z (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetricEnvelope_mem (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : (a.symmetricDomain s (M.nameDomain s) F).names) : (Name.envelope τ.val).val ∈ M.sets := by
  rw [← Name.separationName_true _ τ.property]
  exact M.symmetricSeparationName_mem a s t b F K basis pairing unions powers separation collection
    carrier order group indices supports maps (.equal 0 0) Fin.elim0 τ

theorem symmetricCodedPower_mem [OrderTop P] (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) :
    (Name.codedPower (a.symmetricDomain s (M.nameDomain s) F) W).val ∈ M.sets := by
  apply M.codedPower_mem s (a.symmetricDomain s (M.nameDomain s) F) (fun _ h => h.1)
    pairing unions powers separation carrier (liftedHereditaryFormula 0 1 2 3 4)
    (symmetryParameters a s t b K) _ _ W hW
  · exact Fin.cases carrier (Fin.cases group (Fin.cases indices
      (Fin.cases supports (Fin.cases maps (fun i => Fin.elim0 i)))))
  · exact M.domainMeaning_liftedHereditary a s t b F K basis pairing unions powers separation collection
      carrier group indices supports maps 0 1 2 3 4 _ rfl rfl rfl rfl rfl

theorem symmetric_powerSet [OrderTop P] (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F))) :
    Realize ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) powerSet Fin.elim0 := by
  let D := a.symmetricDomain s (M.nameDomain s) F
  have closed : ∀ g τ, τ ∈ (M.nameDomain s).names → a.act s g τ ∈ (M.nameDomain s).names :=
    fun g τ hτ => M.act_mem s a t pairing unions powers separation collection carrier maps g τ hτ
  have moved : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names :=
    fun g _ hτ => a.symmetricDomain_translated s (M.nameDomain s) F closed g hτ
  have separated : ∀ {n} (φ : SetFormula (n + 1)) (env : Assignment D n) τ,
      τ ∈ D.names → Name.separationName D φ env τ ∈ D.names := by
    intro n φ env τ hτ
    exact ⟨M.symmetricSeparationName_mem a s t b F K basis pairing unions powers separation collection
      carrier order group indices supports maps φ env ⟨τ, hτ⟩,
      a.separationName_hs s D moved F φ env hτ.2 (fun i => (env i).property.2)⟩
  apply realize_powerSet_of_witnesses (D.values {p | H.mem p})
    (fun _ hx _ hz => D.values_transitive _ hx hz)
  intro x hx
  obtain ⟨τ, hτ, rfl⟩ := (Name.NameDomain.mem_values D _ x).1 hx
  have envelopeM := M.symmetricEnvelope_mem a s t b F K basis pairing unions powers separation collection
    carrier order group indices supports maps ⟨τ, hτ⟩
  obtain ⟨W, hW, subsets⟩ := M.power_witness powers envelopeM
  have bounded : ∀ σ ∈ D.names, σ.val ∈ W ↔ σ.val ⊆ (Name.envelope τ).val :=
    fun σ hσ => subsets σ.val hσ.1
  have powerM := M.symmetricCodedPower_mem a s t b F K basis pairing unions powers separation collection
    carrier group indices supports maps W hW
  have powerHS := a.codedPower_hs s (M.nameDomain s) F closed W (Name.envelope τ)
    (a.envelope_hs s F hτ.2) bounded
  refine ⟨Name.eval {p | H.mem p} (Name.codedPower D W),
    (Name.NameDomain.mem_values D _ _).2 ⟨Name.codedPower D W, ⟨powerM, powerHS⟩, rfl⟩, ?_⟩
  intro z hz
  exact Name.mem_eval_codedPower_iff D H generic separated ⟨τ, hτ⟩ W bounded z hz

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


section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem ground_subset_symmetric_values {G : Type u} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (F : Compression.RecursiveMaps.NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    M.sets ⊆ (a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p} := by
  intro x hx
  exact (Name.NameDomain.mem_values _ _ _).2 ⟨Name.check s ⊤ x,
    ⟨M.check_mem s ⊤ pairing unions powers separation collection (M.transitive carrier (s.encode_mem ⊤)) x hx,
      HereditarilySymmetric.check a s F x⟩, Name.eval_check _ ⊤ H.top_mem x⟩

end PartitionPilot.Forcing.TransitiveGround

end


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



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)

theorem inputEvaluationName_entry (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName s z)
    (tau : Name s) (H : ConditionFilter P) (x : ZFSet.{u}) :
    ZFSet.pair tau.val x ∈ eval {p | H.mem p} (inputEvaluationName s J valid) ↔
      tau.val ∈ J ∧ eval {p | H.mem p} tau = x := by
  rw [inputEvaluationName,
    mem_eval_indexedGraphName {p | H.mem p} ⊤ H.top_mem (inputFunction J)
      (inputValid s J valid)]
  constructor
  · rintro ⟨i, equal⟩
    obtain ⟨code, value⟩ := ZFSet.pair_inj.1 equal
    have same : (⟨(inputFunction J).value i, inputValid s J valid i⟩ : Name s) = tau :=
      Subtype.ext ((inputValue J i).trans code)
    exact ⟨code ▸ i.property, same ▸ value⟩
  · rintro ⟨member, value⟩
    let i : J.toSet := ⟨tau.val, member⟩
    have same : (⟨(inputFunction J).value i, inputValid s J valid i⟩ : Name s) = tau :=
      Subtype.ext (inputValue J i)
    exact ⟨i, congrArg (ZFSet.pair tau.val) (same ▸ value)⟩

end Name

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {P : Type u}

theorem mem_namePool (s : Presentation P) (B x : ZFSet.{u}) :
    x ∈ namePool s B ↔ x ∈ B ∧ IsName s x := ZFSet.mem_sep

namespace TransitiveGround

theorem namePool_mem (M : TransitiveGround.{u}) (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) {B : ZFSet.{u}} (hB : B ∈ M.sets) :
    namePool s B ∈ M.sets := by
  have selected := M.separation_mem separation uniformNameFormula (extend s.carrier Fin.elim0)
    (Fin.cases carrier (fun j => Fin.elim0 j)) hB
  have equal : ZFSet.sep (fun x => Realize M.sets uniformNameFormula
      (extend x (extend s.carrier Fin.elim0))) B = namePool s B := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_namePool]
    apply and_congr_right
    intro hx
    exact M.realize_uniformNameFormula s pairing unions powers separation collection
      carrier x (M.transitive hB hx)
  exact equal ▸ selected

end TransitiveGround

namespace Name
variable {s : Presentation P}

theorem child_mem_namePool {σ β : Name s} {p : P} (entry : Entry σ β p) :
    σ.val ∈ namePool s (ZFSet.sUnion (ZFSet.sUnion β.val)) :=
  (mem_namePool _ _ _).2 ⟨child_mem_doubleUnion entry, σ.property⟩

theorem indexedGraphName_covers_eval (H : Set P) (one : P) (hone : one ∈ H)
    (β : Name s) {I f : ZFSet.{u}} (function : FunctionGraphOn I f)
    (names : ∀ i, IsName s (function.value i))
    (onto : ∀ v ∈ namePool s (ZFSet.sUnion (ZFSet.sUnion β.val)),
      ∃ i ∈ I, ZFSet.pair i v ∈ f) :
    ∀ x ∈ eval H β, ∃ i ∈ I, ZFSet.pair i x ∈ eval H (indexedGraphName one function names) := by
  intro x hx
  obtain ⟨σ, p, entry, _, value⟩ := (mem_eval H β x).1 hx
  obtain ⟨i, hi, named⟩ := onto σ.val (child_mem_namePool entry)
  let j : I.toSet := ⟨i, hi⟩
  have rawEqual := function.value_eq_of_entry j named
  have nameEqual : (⟨function.value j, names j⟩ : Name s) = σ := Subtype.ext rawEqual
  refine ⟨i, hi, (pair_mem_eval_indexedGraphName H one hone function names j x).2 ?_⟩
  exact (congrArg (eval H) nameEqual).trans value

end Name

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ForcingWitnessFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_forcingWitnessFormula (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 2))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (zi yi : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params A.carrier) = s.carrier) (ho : env (params A.order) = s.conditionOrder)
    (atomic : M.EqualityMeaning s D A.equality (fun j => env (params j)))
    (domain : M.DomainMeaning s D A.domain (fun j => env (params j)))
    (nameEnv : Assignment D n) (hnames : ∀ i, env (names i) = (nameEnv i).val.val)
    (hz : env zi ∈ M.sets) (hy : env yi ∈ M.sets) :
    Realize M.sets (forcingWitnessFormula A φ params names zi yi) env ↔
      ∃ σ : D.names, ∃ p, env zi = ZFSet.pair σ.val.val (s.encode p) ∧
        ∃ ρ : D.names, ρ.val.val = env yi ∧ Forces D φ (extend σ (extend ρ nameEnv)) p := by
  rw [forcingWitnessFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, body⟩
    obtain ⟨p, shape, source, target, forced⟩ := (M.realize_exConditions s (params A.carrier).succ _
      (extend x env) carrier hc).1 body
    rw [realize_domainApplication] at source target
    obtain ⟨σ, eq⟩ := (domain x hx).1 source
    obtain ⟨ρ, eqρ⟩ := (domain (env yi) hy).1 target
    let e := extend (s.encode p) (extend x env)
    have raw := (M.realize_orderedPairFormula pairing zi.succ.succ 1 0 e hz hx
      (M.transitive carrier (s.encode_mem p))).1 shape
    refine ⟨σ, p, raw.trans (congrArg (fun z => ZFSet.pair z (s.encode p)) eq.symm), ρ, eqρ, ?_⟩
    exact (M.realize_forcingTranslation s D ground pairing carrier order A φ
      (fun j => (params j).succ.succ) 0 (extend 1 (extend yi.succ.succ (fun j => (names j).succ.succ)))
      e hc ho atomic domain p (extend σ (extend ρ nameEnv)) rfl
      (Fin.cases eq.symm (Fin.cases eqρ.symm hnames))).1 forced
  · rintro ⟨σ, p, shape, ρ, eqρ, forced⟩
    refine ⟨σ.val.val, ground σ.val σ.property, ?_⟩
    apply (M.realize_exConditions s (params A.carrier).succ _ (extend σ.val.val env) carrier hc).2
    let e := extend (s.encode p) (extend σ.val.val env)
    refine ⟨p, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing zi.succ.succ 1 0 e hz (ground σ.val σ.property)
        (M.transitive carrier (s.encode_mem p))).2 shape
    · rw [realize_domainApplication]
      exact (domain σ.val.val (ground σ.val σ.property)).2 ⟨σ, rfl⟩
    · rw [realize_domainApplication]
      exact (domain (env yi) hy).2 ⟨ρ, eqρ⟩
    · exact (M.realize_forcingTranslation s D ground pairing carrier order A φ
        (fun j => (params j).succ.succ) 0 (extend 1 (extend yi.succ.succ (fun j => (names j).succ.succ)))
        e hc ho atomic domain p (extend σ (extend ρ nameEnv)) rfl
        (Fin.cases rfl (Fin.cases eqρ.symm hnames))).2 forced

end PartitionPilot.Forcing.TransitiveGround

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSymmetricCollection
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetricForcingWitnessBound (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {n : Nat} (φ : SetFormula (n + 2))
    (nameEnv : Assignment (a.symmetricDomain s (M.nameDomain s) F) n)
    (τ : (a.symmetricDomain s (M.nameDomain s) F).names) :
    ∃ W ∈ M.sets, ∀ σ : (a.symmetricDomain s (M.nameDomain s) F).names, ∀ p,
      (∃ r, Name.Entry σ.val τ.val r) →
      (∃ ρ : (a.symmetricDomain s (M.nameDomain s) F).names,
        Forces (a.symmetricDomain s (M.nameDomain s) F) φ (extend σ (extend ρ nameEnv)) p) →
      ∃ ρ : (a.symmetricDomain s (M.nameDomain s) F).names, ρ.val.val ∈ W ∧
        Forces (a.symmetricDomain s (M.nameDomain s) F) φ (extend σ (extend ρ nameEnv)) p := by
  let D := a.symmetricDomain s (M.nameDomain s) F
  let context := extend s.carrier (extend s.conditionOrder (extend t.carrier (extend b.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) (fun i => (nameEnv i).val.val))))))
  let params : Fin 6 → Fin (n + 6) := extend 0 (extend 1 (extend 2 (extend 3 (extend 4 (extend 5 Fin.elim0)))))
  have members : ∀ i, context i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (Fin.cases group (Fin.cases indices (Fin.cases supports
      (Fin.cases maps (fun i => (nameEnv i).property.1))))))
  let selected := forcingWitnessFormula symmetricGroundPrimitives φ (fun j => (params j).succ.succ)
    (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ) 0 1
  have correct : ∀ z ∈ M.sets, ∀ y ∈ M.sets,
      Realize M.sets selected (extend z (extend y context)) ↔
        ∃ σ : D.names, ∃ p, z = ZFSet.pair σ.val.val (s.encode p) ∧
          ∃ ρ : D.names, ρ.val.val = y ∧ Forces D φ (extend σ (extend ρ nameEnv)) p := by
    intro z hz y hy
    apply M.realize_forcingWitnessFormula s D (fun _ h => h.1) pairing carrier order symmetricGroundPrimitives φ
      (fun j => (params j).succ.succ) (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ)
      0 1 (extend z (extend y context)) rfl rfl _ _ nameEnv (fun _ => rfl) hz hy
    · exact M.equalityMeaning_lifted s D (fun _ h => h.1) pairing unions powers separation collection
        carrier order 0 1 _ rfl rfl
    · exact M.domainMeaning_liftedHereditary a s t b F K basis pairing unions powers separation collection
        carrier group indices supports maps 0 2 3 4 5 _ rfl rfl rfl rfl rfl
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers
    (M.union_mem unions (M.union_mem unions τ.property.1)) carrier
  obtain ⟨W, hW, witnesses⟩ := M.partialCollection_witness collection selected context members hB
  refine ⟨W, hW, ?_⟩
  intro σ p entry possible
  obtain ⟨r, entry⟩ := entry
  have hb := pairBound σ.val.val (Name.child_mem_doubleUnion entry) (s.encode p) (s.encode_mem p)
  have hz := M.transitive hB hb
  have existsRaw : ∃ y ∈ M.sets, Realize M.sets selected
      (extend (ZFSet.pair σ.val.val (s.encode p)) (extend y context)) := by
    obtain ⟨ρ, forced⟩ := possible
    exact ⟨ρ.val.val, ρ.property.1, (correct _ hz _ ρ.property.1).2 ⟨σ, p, rfl, ρ, rfl, forced⟩⟩
  obtain ⟨y, hy, rel⟩ := witnesses _ hb existsRaw
  obtain ⟨ν, q, shape, ρ, eqρ, forced⟩ := (correct _ hz y (M.transitive hW hy)).1 rel
  have parts := ZFSet.pair_inj.1 shape
  have names : σ = ν := Subtype.ext (Subtype.ext parts.1)
  have conditions : p = q := s.injective parts.2
  refine ⟨ρ, eqρ.symm ▸ hy, ?_⟩
  rwa [← names, ← conditions] at forced

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetric_collection (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F))) :
    CollectionSchema ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) := by
  classical
  let D := a.symmetricDomain s (M.nameDomain s) F
  intro n φ params members X hX total
  have reps := fun i => (D.mem_values _ (params i)).1 (members i)
  choose names inDomain values using reps
  let env : Assignment D n := fun i => ⟨names i, inDomain i⟩
  have evals : evalAssignment {p | H.mem p} env = params := funext values
  obtain ⟨τ, hτ, rfl⟩ := (D.mem_values _ X).1 hX
  obtain ⟨W, hW, bounds⟩ := M.symmetricForcingWitnessBound a s t b F K basis
    pairing unions powers separation collection carrier order group indices supports maps φ env ⟨τ, hτ⟩
  have orbitM := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW
  let C := Name.codedPower D (a.orbitCodes s (M.nameDomain s) W)
  have groundC := M.symmetricCodedPower_mem a s t b F K basis pairing unions powers separation collection
    carrier group indices supports maps _ orbitM
  have symC := a.orbitCodedPower_hs s (M.nameDomain s) F
    (fun g σ hσ => M.act_mem s a t pairing unions powers separation collection carrier maps g σ hσ) W
  have hC : C ∈ D.names := ⟨groundC, symC⟩
  refine ⟨Name.eval {p | H.mem p} C, (D.mem_values _ _).2 ⟨C, hC, rfl⟩, ?_⟩
  intro x hx member
  obtain ⟨σ, r, entry, _, value⟩ := (Name.mem_eval _ τ x).1 member
  have hσ := D.children hτ entry
  obtain ⟨y, hy, rel⟩ := total x hx member
  obtain ⟨ρ, hρ, valueρ⟩ := (D.mem_values _ y).1 hy
  have truth : Realize (D.values {p | H.mem p}) φ
      (evalAssignment {p | H.mem p} (extend ⟨σ, hσ⟩ (extend ⟨ρ, hρ⟩ env))) := by
    rw [evalAssignment_extend, evalAssignment_extend, value, valueρ, evals]
    exact rel
  obtain ⟨p, hp, forced⟩ := (forcing_truth D H generic φ (extend ⟨σ, hσ⟩ (extend ⟨ρ, hρ⟩ env))).1 truth
  obtain ⟨ν, νW, forcedν⟩ := bounds ⟨σ, hσ⟩ p ⟨r, entry⟩ ⟨⟨ρ, hρ⟩, forced⟩
  have orbitν := a.mem_orbitCodes_of_mem s (M.nameDomain s) ν.property.1 νW
  have νC : Name.eval {p | H.mem p} ν.val ∈ Name.eval {p | H.mem p} C :=
    (Name.mem_eval_codedPower D _ H _).2 ⟨ν.val, ν.property, orbitν, rfl⟩
  have truthν := forces_sound D H generic φ (extend ⟨σ, hσ⟩ (extend ν env)) hp forcedν
  rw [evalAssignment_extend, evalAssignment_extend, value, evals] at truthν
  exact ⟨Name.eval {p | H.mem p} ν.val, (D.mem_values _ _).2 ⟨ν.val, ν.property, rfl⟩, νC, truthν⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundHartogs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetric_replacement (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F))) :
    ReplacementSchema ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) :=
  replacement_of_collection_separation _
    (M.symmetric_collection a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic)
    (M.symmetric_separation a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic)

end PartitionPilot.Forcing.TransitiveGround

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMixtureNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.SetFormula

universe u

theorem realize_infinity_of_witness (U : Set ZFSet.{u})
    (transitive : ∀ x ∈ U, ∀ z ∈ x, z ∈ U)
    (I : ZFSet.{u}) (hI : I ∈ U) (empty : (∅ : ZFSet.{u}) ∈ I)
    (successor : ∀ x ∈ I, insert x x ∈ I) : Realize U infinity Fin.elim0 := by
  simp only [infinity, emptySetFormula, successorFormula, realize_ex, realize_imp, realize_disj, Realize]
  refine ⟨I, hI, ⟨∅, transitive I hI ∅ empty, empty, fun z _ => ZFSet.notMem_empty z⟩, ?_⟩
  intro x _ hx
  refine ⟨insert x x, transitive I hI _ (successor x hx), successor x hx, ?_⟩
  intro z _
  exact ⟨ZFSet.mem_insert_iff.1, ZFSet.mem_insert_iff.2⟩

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u})

theorem symmetric_infinity {P G : Type u} [Group G] [PartialOrder P] [OrderTop P]
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) infinity Fin.elim0 := by
  obtain ⟨I, hI, empty, successor⟩ := M.infinity_witness infinite
  let D := a.symmetricDomain s (M.nameDomain s) F
  exact realize_infinity_of_witness (D.values {p | H.mem p})
    (fun _ hx _ hz => D.values_transitive _ hx hz) I
    (M.ground_subset_symmetric_values s a F pairing unions powers separation collection carrier H hI)
    empty successor

end PartitionPilot.Forcing.TransitiveGround

end



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetric_ZF (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F))) :
    ZFRealization ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) := by
  let D := a.symmetricDomain s (M.nameDomain s) F
  have nonempty := a.symmetricDomain_nonempty s (M.nameDomain s) F
    (M.nameDomain_nonempty s ⟨s.carrier, carrier⟩)
  refine ⟨⟨realize_extensionality D _, realize_foundation D _, realize_emptySet D nonempty _,
    M.symmetric_pairing s a F pairing carrier H,
    M.symmetric_union s a F pairing unions powers separation carrier order H,
    M.symmetric_powerSet a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic,
    M.symmetric_infinity s a F pairing unions powers separation collection infinite carrier H⟩, ?_, ?_⟩
  · exact M.symmetric_separation a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic
  · exact M.symmetric_replacement a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic

end PartitionPilot.Forcing.TransitiveGround


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_AllSupportFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u v

theorem allSupportFamily_basis (G : Type u) [Group G] (H : Subgroup G) :
    (allSupportFamily G).mem H ↔ ∃ i, allSupportBasis G i ≤ H :=
  ⟨fun _ => ⟨⟨0⟩, bot_le⟩, fun _ => True.intro⟩

namespace PosetAction
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem allSupport_hs (τ : Name s) :
    HereditarilySymmetric a s (allSupportFamily G) τ := by
  induction τ using Name.inductionOn with
  | step τ ih => exact HereditarilySymmetric.mk True.intro ih

theorem symmetricDomain_allSupport (D : Name.NameDomain s) :
    a.symmetricDomain s D (allSupportFamily G) = D := by
  have names : (a.symmetricDomain s D (allSupportFamily G)).names = D.names := by
    apply Set.ext
    intro τ
    exact ⟨fun h => h.1, fun h => ⟨h, a.allSupport_hs s τ⟩⟩
  have ext : ∀ E F : Name.NameDomain s, E.names = F.names → E = F := by
    intro E F same
    cases E
    cases F
    cases same
    rfl
  exact ext _ _ names

end PosetAction

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundAllSupportCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {G : Type u} [Group G] (t : Presentation G)

theorem allSupportBasisCode_eq_singleton :
    supportBasisCode (natInitialPresentation 1) t (allSupportBasis G) =
      ({ZFSet.pair (natSetCode 0) (t.encode 1)} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro z
  rw [supportBasisCode, Presentation.mem_subset, ZFSet.mem_singleton]
  constructor
  · rintro ⟨⟨i, g⟩, member, equal⟩
    have one : g = 1 := Subgroup.mem_bot.1 member
    have index : i = (⟨0⟩ : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
    subst i
    subst g
    exact equal.symm
  · rintro rfl
    exact ⟨(⟨0⟩, 1), Subgroup.one_mem _, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

omit [Group G] in
theorem allSupportIndices_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (group : t.carrier ∈ M.sets) : (natInitialPresentation 1).carrier ∈ M.sets := by
  have empty := M.empty_mem ⟨t.carrier, group⟩
  have singleton := M.unorderedPair_mem pairing empty empty
  simp only [natInitialPresentation, natSetCode_succ, natSetCode_zero]
  simp only [ZFSet.pair_eq_singleton] at singleton
  exact singleton

theorem allSupportBasisCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (group : t.carrier ∈ M.sets) :
    supportBasisCode (natInitialPresentation 1) t (allSupportBasis G) ∈ M.sets := by
  rw [allSupportBasisCode_eq_singleton]
  have empty := M.empty_mem ⟨t.carrier, group⟩
  have one := M.transitive group (t.encode_mem 1)
  have pair := M.orderedPair_mem pairing empty one
  simpa only [natSetCode_zero, ZFSet.pair_eq_singleton] using
    M.unorderedPair_mem pairing pair pair

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPrincipalNiceSupportCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem pair_mem_niceSupportRelation (i : I) (tau : ZFSet.{u}) :
    ZFSet.pair (b.encode i) tau ∈ M.niceSupportRelation a s b T K ↔
      tau ∈ M.sets ∧ NiceNameCode a s T (K i) tau := by
  rw [niceSupportRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, sigma, eq, candidate⟩
    obtain ⟨keys, rfl⟩ := ZFSet.pair_inj.1 eq
    have same := b.injective keys
    subst j
    exact (M.mem_niceNameCandidates a s T (K i) tau).1 candidate
  · intro code
    exact ⟨ZFSet.pair_mem_prod.2 ⟨b.encode_mem i,
      (M.mem_niceSupportNameCodes a s T K tau).2 ⟨code.1, i, code.2⟩⟩,
      i, tau, rfl, (M.mem_niceNameCandidates a s T (K i) tau).2 code⟩

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionClosure
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundCountable_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets) (nonempty : R.Nonempty)
    (small : M.groundEmbeddable R ZFSet.omega) :
    ∃ g ∈ M.sets, ZFSet.IsFunc ZFSet.omega R g ∧
      ∀ p ∈ R, ∃ n ∈ ZFSet.omega, ZFSet.pair n p ∈ g :=
  M.groundEmbeddable_enumeration pairing unions powers separation hR
    (M.omega_mem separation infinite) nonempty small

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})






theorem groundCountable_family_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets)
    (countR : M.groundEmbeddable R ZFSet.omega)
    (small : ∀ p ∈ R, M.groundEmbeddable p ZFSet.omega) :
    M.groundEmbeddable (⋃₀ R) ZFSet.omega := by
  classical
  by_cases nonempty : R.Nonempty
  · obtain ⟨g, hg, enumeration, onto⟩ :=
      M.groundCountable_enumeration pairing unions powers separation infinite hR nonempty countR
    exact M.countable_enumerated_union pairing unions powers separation infinite choice
      hR (M.union_mem unions hR) hg enumeration onto
      (fun p hp _ hz => ZFSet.mem_sUnion.2 ⟨p, hp, hz⟩) small
  · have empty : R = ∅ := by
      apply ZFSet.ext
      intro p
      exact ⟨fun hp => False.elim (nonempty ⟨p, hp⟩), fun hp => False.elim (ZFSet.notMem_empty p hp)⟩
    rw [empty, ZFSet.sUnion_empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨R, hR⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCoinitialOperations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem mem_copyPullback (A L e F x : ZFSet.{u}) :
    x ∈ copyPullback A L e F ↔
      x ∈ A ∧ ∃ y ∈ F, y ∈ L ∧ ZFSet.pair x y ∈ e := by
  rw [copyPullback, mem_relationImage]
  constructor
  · rintro ⟨hx, y, hy, rel⟩
    exact ⟨hx, y, hy, ((pair_mem_relationConverse A L e x y).1 rel).2⟩
  · rintro ⟨hx, y, hy, hyL, rel⟩
    exact ⟨hx, y, hy, (pair_mem_relationConverse A L e x y).2 ⟨hx, hyL, rel⟩⟩

theorem relationImage_copyPullback {A L e : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e) (F : ZFSet.{u}) :
    relationImage (copyPullback A L e F) L e = F ∩ relationImage A L e := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, ZFSet.mem_inter, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, rel⟩
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    have equal : y = z := (unique y rel).trans (unique z relz).symm
    exact ⟨equal ▸ hz, hy, x, hxA, rel⟩
  · rintro ⟨hyF, hy, x, hx, rel⟩
    exact ⟨hy, x, (mem_copyPullback A L e F x).2 ⟨hx, y, hyF, hy, rel⟩, rel⟩

theorem CoinitialBelowCode.copy {A L e sourceOrder targetOrder F target B : ZFSet.{u}}
    (func : ZFSet.IsFunc A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : CoinitialBelowCode sourceOrder (copyPullback A L e F) target B) :
    CoinitialBelowCode targetOrder F (relationImage target L e) (relationImage B L e) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage B L e y).1 hy
    obtain ⟨hxA, z, hz, _, relz⟩ := (mem_copyPullback A L e F x).1 (basis.1 hx)
    obtain ⟨w, _, unique⟩ := func.2 x hxA
    exact (unique y rel).trans (unique z relz).symm ▸ hz
  · intro y hy
    obtain ⟨_, x, hx, rel⟩ := (mem_relationImage target L e y).1 hy
    obtain ⟨b, hb, below⟩ := basis.2 x hx
    have hbA := ((mem_copyPullback A L e F b).1 (basis.1 hb)).1
    obtain ⟨b', relb, _⟩ := func.2 b hbA
    have hbL := (ZFSet.pair_mem_prod.1 (func.1 relb)).2
    exact ⟨b', (mem_relationImage B L e b').2 ⟨hbL, b, hb, relb⟩,
      monotone b x b' y below relb rel⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem copyPullback_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A L e F : ZFSet.{u}} (hA : A ∈ M.sets) (hL : L ∈ M.sets)
    (he : e ∈ M.sets) (hF : F ∈ M.sets) : copyPullback A L e F ∈ M.sets :=
  M.relationImage_mem separation hF hA
    (M.relationConverse_mem pairing unions powers separation hA hL he)

theorem internalCountableBelow_copy
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F target : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F) target) :
    M.InternalCountableBelow targetOrder F (relationImage target L e) := by
  obtain ⟨B, hB, small, coinitial⟩ := basis
  have subset : B ⊆ A := fun x hx => ((mem_copyPullback A L e F x).1 (coinitial.1 hx)).1
  exact ⟨relationImage B L e, M.relationImage_mem separation hB hL he,
    M.groundEmbeddable_image pairing unions powers separation hB hL
      (M.omega_mem separation infinite) he code subset small,
    coinitial.copy code.function monotone⟩

theorem internalCountableBelow_copy_pullback
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L e sourceOrder targetOrder F : ZFSet.{u}}
    (hL : L ∈ M.sets) (he : e ∈ M.sets) (code : InjectionCode A L e)
    (monotone : ∀ x y x' y', ZFSet.pair x y ∈ sourceOrder →
      ZFSet.pair x x' ∈ e → ZFSet.pair y y' ∈ e → ZFSet.pair x' y' ∈ targetOrder)
    (basis : M.InternalCountableBelow sourceOrder (copyPullback A L e F)
      (copyPullback A L e F)) :
    M.InternalCountableBelow targetOrder F (F ∩ relationImage A L e) := by
  rw [← relationImage_copyPullback code.function F]
  exact M.internalCountableBelow_copy pairing unions powers separation infinite hL he code monotone basis

end TransitiveGround






theorem pair_mem_basisChoiceRelation (I W order target parts i B : ZFSet.{u}) :
    ZFSet.pair i B ∈ basisChoiceRelation I W order target parts ↔
      i ∈ I ∧ B ∈ W ∧ FiberCoveredCode order target parts i B := by
  rw [basisChoiceRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, A, hA, eq, covers⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hj, hA, covers⟩
  · rintro ⟨hi, hB, covers⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hi, hB⟩, i, hi, B, hB, rfl, covers⟩

namespace BoundedFormula

open SetFormula

theorem truth_fiberCoveredFormula {n} (order target parts i B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fiberCoveredFormula order target parts i B) env ↔
      FiberCoveredCode (env order) (env target) (env parts) (env i) (env B) := by
  simp only [fiberCoveredFormula, Truth, truth_imp, truth_exMem, truth_pairMembershipFormula]
  rfl

theorem truth_basisChoiceEntryFormula {n} (z I W order target parts : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (basisChoiceEntryFormula z I W order target parts) env ↔
      ∃ i ∈ env I, ∃ B ∈ env W, env z = ZFSet.pair i B ∧
        FiberCoveredCode (env order) (env target) (env parts) i B := by
  simp only [basisChoiceEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_fiberCoveredFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem basisChoiceRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W order target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hW : W ∈ M.sets)
    (hOrder : order ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets) :
    basisChoiceRelation I W order target parts ∈ M.sets := by
  let params := extend I (extend W (extend order (extend target (extend parts Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hOrder (Fin.cases hTarget (Fin.cases hParts
      (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hI hW)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.basisChoiceEntryFormula 0 1 2 3 4 5) (extend z params)) (ZFSet.prod I W) =
      basisChoiceRelation I W order target parts := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, basisChoiceRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_basisChoiceEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem internalCountableBelow_indexed_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I order F target parts : ZFSet.{u}} (hI : I ∈ M.sets) (hOrder : order ∈ M.sets)
    (hF : F ∈ M.sets) (hTarget : target ∈ M.sets) (hParts : parts ∈ M.sets)
    (smallI : M.groundEmbeddable I ZFSet.omega)
    (cover : ∀ x ∈ target, ∃ i ∈ I, ZFSet.pair i x ∈ parts)
    (localBases : ∀ i ∈ I, M.InternalCountableBelow order F (relationFiber target parts i)) :
    M.InternalCountableBelow order F target := by
  have hO := M.omega_mem separation infinite
  let W := M.groundSmallSubsets F ZFSet.omega
  have hW : W ∈ M.sets := M.groundSmallSubsets_mem powers separation hF hO
  have choices := M.basisChoiceRelation_mem pairing unions powers separation hI hW hOrder hTarget hParts
  have total (i : ZFSet.{u}) (hi : i ∈ I) :
      ∃ B ∈ W, ZFSet.pair i B ∈ basisChoiceRelation I W order target parts := by
    obtain ⟨B, hB, smallB, positive, below⟩ := localBases i hi
    have hBW : B ∈ W := (M.mem_groundSmallSubsets F ZFSet.omega B).2 ⟨hB, positive, smallB⟩
    exact ⟨B, hBW, (pair_mem_basisChoiceRelation I W order target parts i B).2
      ⟨hi, hBW, fun x hx rel => below x ((mem_relationFiber target parts i x).2 ⟨hx, rel⟩)⟩⟩
  obtain ⟨g, hg, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hI hW choices total
  let family := relationImage I W g
  have hFamily : family ∈ M.sets := M.relationImage_mem separation hI hW hg
  have smallFamily : M.groundEmbeddable family ZFSet.omega :=
    M.groundEmbeddable_function_image pairing unions powers separation choice hI hW hO hg func smallI
  have candidates (B : ZFSet.{u}) (hB : B ∈ family) : B ∈ W :=
    ((mem_relationImage I W g B).1 hB).1
  have smallBasis (B : ZFSet.{u}) (hB : B ∈ family) : M.groundEmbeddable B ZFSet.omega :=
    ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.2
  refine ⟨family.sUnion, M.union_mem unions hFamily,
    M.groundCountable_family_union pairing unions powers separation infinite choice
      hFamily smallFamily smallBasis, ?_, ?_⟩
  · intro x hx
    obtain ⟨B, hB, xB⟩ := ZFSet.mem_sUnion.1 hx
    exact ((M.mem_groundSmallSubsets F ZFSet.omega B).1 (candidates B hB)).2.1 xB
  · intro x hx
    obtain ⟨i, hi, ix⟩ := cover x hx
    obtain ⟨B, chosen, _⟩ := func.2 i hi
    have spec := (pair_mem_basisChoiceRelation I W order target parts i B).1 (selected chosen)
    obtain ⟨b, hb, lower⟩ := spec.2.2 x hx ix
    have hB : B ∈ family := (mem_relationImage I W g B).2 ⟨spec.2.1, i, hi, chosen⟩
    exact ⟨b, ZFSet.mem_sUnion.2 ⟨B, hB, hb⟩, lower⟩

end TransitiveGround

end



namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem InternalCountableBelow.mono {order F target smaller : ZFSet.{u}}
    (basis : M.InternalCountableBelow order F target) (subset : smaller ⊆ target) :
    M.InternalCountableBelow order F smaller := by
  obtain ⟨B, hB, small, positive, below⟩ := basis
  exact ⟨B, hB, small, positive, fun x hx => below x (subset hx)⟩

theorem internalCountableBelow_empty (inhabited : M.sets.Nonempty) (order F : ZFSet.{u}) :
    M.InternalCountableBelow order F ∅ := by
  exact ⟨∅, M.empty_mem inhabited, M.empty_groundEmbeddable ZFSet.omega inhabited,
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx),
    fun _ hx => False.elim (ZFSet.notMem_empty _ hx)⟩

theorem internalCountableBelow_of_countable {order F target : ZFSet.{u}}
    (hTarget : target ∈ M.sets) (small : M.groundEmbeddable target ZFSet.omega)
    (positive : target ⊆ F) (refl : ∀ x ∈ target, ZFSet.pair x x ∈ order) :
    M.InternalCountableBelow order F target :=
  ⟨target, hTarget, small, positive, fun x hx => ⟨x, hx, refl x hx⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologicalBasis
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem mem_birthEssentialSet (F T r birth x : ZFSet.{u}) :
    x ∈ birthEssentialSet F T r birth ↔ x ∈ F ∧
      ∀ y ∈ F, ∀ a ∈ T, ∀ b ∈ T,
        ZFSet.pair y x ∈ r → ZFSet.pair y a ∈ birth → ZFSet.pair x b ∈ birth → a ∉ b :=
  ZFSet.mem_sep

theorem birthEssentialSet_subset (F T r birth : ZFSet.{u}) :
    birthEssentialSet F T r birth ⊆ F := fun _ hx => (ZFSet.mem_sep.1 hx).1

theorem mem_essentialBirthIndices (F T r birth t : ZFSet.{u}) :
    t ∈ essentialBirthIndices F T r birth ↔ t ∈ T ∧
      ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair x t ∈ birth :=
  mem_relationImage _ _ _ _

theorem positive_above_birthEssential {L F T r birth : ZFSet.{u}}
    (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (refl : ∀ x ∈ L, ZFSet.pair x x ∈ r)
    (trans : ∀ x ∈ L, ∀ y ∈ L, ∀ z ∈ L,
      ZFSet.pair x y ∈ r → ZFSet.pair y z ∈ r → ZFSet.pair x z ∈ r)
    {x : ZFSet.{u}} (positive : x ∈ F) :
    ∃ y ∈ birthEssentialSet F T r birth, ZFSet.pair y x ∈ r := by
  let S : Set ZFSet.{u} := {t | ∃ y ∈ F, ZFSet.pair y x ∈ r ∧ ZFSet.pair y t ∈ birth}
  obtain ⟨t, xt, _⟩ := born.2 x (subset positive)
  have inhabited : S.Nonempty := ⟨t, x, positive, refl x (subset positive), xt⟩
  obtain ⟨t, ⟨y, hy, below, yt⟩, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨y, (mem_birthEssentialSet F T r birth y).2 ⟨hy, ?_⟩, below⟩
  intro z hz a _ b _ zy za yb earlier
  obtain ⟨_, _, unique⟩ := born.2 y (subset hy)
  have eq : b = t := (unique b yb).trans (unique t yt).symm
  have aS : a ∈ S := ⟨z, hz, trans z (subset hz) y (subset hy) x (subset positive) zy below, za⟩
  exact minimal a aS (eq ▸ earlier)

namespace BoundedFormula

open SetFormula

theorem truth_birthEssentialFormula {n} (x f t r birth : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (birthEssentialFormula x f t r birth) env ↔
      ∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
        ZFSet.pair y (env x) ∈ env r → ZFSet.pair y a ∈ env birth →
          ZFSet.pair (env x) b ∈ env birth → a ∉ b := by
  simp only [birthEssentialFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change (∀ y ∈ env f, ∀ a ∈ env t, ∀ b ∈ env t,
    ZFSet.pair y (env x) ∈ env r ∧ ZFSet.pair y a ∈ env birth ∧
      ZFSet.pair (env x) b ∈ env birth → a ∉ b) ↔ _
  constructor
  · intro h y hy a ha b hb below bornY bornX
    exact h y hy a ha b hb ⟨below, bornY, bornX⟩
  · intro h y hy a ha b hb premises
    exact h y hy a ha b hb premises.1 premises.2.1 premises.2.2

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem birthEssentialSet_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    birthEssentialSet F T r birth ∈ M.sets := by
  let params := extend F (extend T (extend r (extend birth Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.birthEssentialFormula 0 1 2 3 4) params
    (Fin.cases hF (Fin.cases hT (Fin.cases hr (Fin.cases hBirth (fun j => Fin.elim0 j))))) hF
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.birthEssentialFormula 0 1 2 3 4) (extend x params)) F =
      birthEssentialSet F T r birth := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_birthEssentialSet]
    exact and_congr Iff.rfl (BoundedFormula.truth_birthEssentialFormula 0 1 2 3 4 _)
  exact eq ▸ selected

theorem essentialBirthIndices_mem (separation : SeparationSchema M.sets)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    essentialBirthIndices F T r birth ∈ M.sets :=
  M.relationImage_mem separation (M.birthEssentialSet_mem separation hF hT hr hBirth) hT hBirth

theorem exists_essentialBirthRepresentatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) :
    ∃ g ∈ M.sets,
      ZFSet.IsFunc (essentialBirthIndices F T r birth) (birthEssentialSet F T r birth) g ∧
      g ⊆ relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth ∧
      ∀ t ∈ essentialBirthIndices F T r birth,
        ∃ x ∈ birthEssentialSet F T r birth, ZFSet.pair t x ∈ g ∧ ZFSet.pair x t ∈ birth := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hConverse := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have total : ∀ t ∈ S, ∃ x ∈ E, ZFSet.pair t x ∈ relationConverse E S birth := by
    intro t ht
    obtain ⟨_, x, hx, born⟩ := (mem_essentialBirthIndices F T r birth t).1 ht
    exact ⟨x, hx, (pair_mem_relationConverse E S birth x t).2 ⟨hx, ht, born⟩⟩
  obtain ⟨g, hg, function, restricted⟩ :=
    M.uniformize_relation pairing unions powers separation choice hS hE hConverse total
  refine ⟨g, hg, function, restricted, ?_⟩
  intro t ht
  obtain ⟨x, chosen, _⟩ := function.2 t ht
  have spec := (pair_mem_relationConverse E S birth x t).1 (restricted chosen)
  exact ⟨x, spec.1, chosen, spec.2.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem internal_countable_basis_of_birth_layers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (order : PartialOrderCode L r) (subset : F ⊆ L) (born : ZFSet.IsFunc L T birth)
    (small : M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    M.InternalCountableBelow r F F := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  let parts := relationConverse E S birth
  have hE : E ∈ M.sets := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS : S ∈ M.sets := M.essentialBirthIndices_mem separation hF hT hr hBirth
  have hParts : parts ∈ M.sets := M.relationConverse_mem pairing unions powers separation hE hS hBirth
  have cover (x : ZFSet.{u}) (hx : x ∈ E) : ∃ t ∈ S, ZFSet.pair t x ∈ parts := by
    obtain ⟨t, xt, _⟩ := born.2 x (subset (birthEssentialSet_subset F T r birth hx))
    have htT := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
    have htS : t ∈ S := (mem_essentialBirthIndices F T r birth t).2 ⟨htT, x, hx, xt⟩
    exact ⟨t, htS, (pair_mem_relationConverse E S birth x t).2 ⟨hx, htS, xt⟩⟩
  obtain ⟨B, hB, smallB, positive, below⟩ := M.internalCountableBelow_indexed_union
    pairing unions powers separation infinite choice hS hr hF hE hParts small cover localBases
  refine ⟨B, hB, smallB, positive, ?_⟩
  intro x hx
  obtain ⟨y, hy, yx⟩ := positive_above_birthEssential subset born order.refl order.trans hx
  obtain ⟨b, hb, byLower⟩ := below y hy
  exact ⟨b, hb, order.trans b (subset (positive hb)) y
    (subset (birthEssentialSet_subset F T r birth hy)) x (subset hx) byLower yx⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundNaturalFamilyShift
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem mem_heightColumnFiber (S C Q h c i : ZFSet.{u}) :
    i ∈ heightColumnFiber S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ ∃ q ∈ Q, ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnFiber, mem_relationImage]
  constructor
  · rintro ⟨hi, v, hv, vi⟩
    obtain ⟨a, ha, q, hq, rfl⟩ := ZFSet.mem_prod.1 hv
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    have rel := (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).1 vi
    exact ⟨hi, (ZFSet.pair_mem_prod.1 rel.2.1).1, q, hq, rel.2.2⟩
  · rintro ⟨hi, hc, q, hq, iq⟩
    exact ⟨hi, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hq⟩,
      (pair_mem_relationConverse S (ZFSet.prod C Q) h i (ZFSet.pair c q)).2
        ⟨hi, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq⟩⟩

theorem pair_mem_heightColumnGraph (S C Q h c i q : ZFSet.{u}) :
    ZFSet.pair i q ∈ heightColumnGraph S C Q h c ↔
      i ∈ S ∧ c ∈ C ∧ q ∈ Q ∧ ZFSet.pair i (ZFSet.pair c q) ∈ h := by
  rw [heightColumnGraph, pair_mem_relationCompose]
  constructor
  · rintro ⟨hi, hq, v, hv, iv, vq⟩
    obtain ⟨a, ha, b, _, eq⟩ := (mem_productSecond {c} Q (ZFSet.pair v q)).1 vq
    have ac := ZFSet.mem_singleton.1 ha
    subst a
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hi, (ZFSet.pair_mem_prod.1 hv).1, hq, iv⟩
  · rintro ⟨hi, hc, hq, iq⟩
    exact ⟨hi, hq, ZFSet.pair c q, ZFSet.pair_mem_prod.2 ⟨hc, hq⟩, iq,
      (mem_productSecond {c} Q _).2 ⟨c, ZFSet.mem_singleton.2 rfl, q, hq, rfl⟩⟩

theorem heightColumnGraph_injection {S C Q h : ZFSet.{u}}
    (height : InjectionCode S (ZFSet.prod C Q) h) (c : ZFSet.{u}) :
    InjectionCode (heightColumnFiber S C Q h c) Q (heightColumnGraph S C Q h c) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have shape : z ∈ ZFSet.prod S Q := (ZFSet.mem_sep.1
      (show z ∈ relationCompose S (ZFSet.prod C Q) Q h (productSecond {c} Q) from hz)).1
    obtain ⟨i, hi, q, hq, rfl⟩ := ZFSet.mem_prod.1 shape
    obtain ⟨_, hc, _, iq⟩ := (pair_mem_heightColumnGraph S C Q h c i q).1 hz
    exact ZFSet.pair_mem_prod.2
      ⟨(mem_heightColumnFiber S C Q h c i).2 ⟨hi, hc, q, hq, iq⟩, hq⟩
  · intro i hi
    obtain ⟨hiS, hc, q, hq, iq⟩ := (mem_heightColumnFiber S C Q h c i).1 hi
    refine ⟨q, (pair_mem_heightColumnGraph S C Q h c i q).2 ⟨hiS, hc, hq, iq⟩, ?_⟩
    intro r ir
    have irh := (pair_mem_heightColumnGraph S C Q h c i r).1 ir
    obtain ⟨v, _, unique⟩ := height.function.2 i hiS
    exact (ZFSet.pair_inj.1 ((unique _ irh.2.2.2).trans (unique _ iq).symm)).2
  · intro i j q iq jq
    exact height.injective i j (ZFSet.pair c q)
      ((pair_mem_heightColumnGraph S C Q h c i q).1 iq).2.2.2
      ((pair_mem_heightColumnGraph S C Q h c j q).1 jq).2.2.2

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightColumnFiber_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnFiber S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationImage_mem separation
    (M.prod_mem pairing unions powers separation singleton hQ) hS
    (M.relationConverse_mem pairing unions powers separation hS
      (M.prod_mem pairing unions powers separation hC hQ) hh)

theorem heightColumnGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) :
    heightColumnGraph S C Q h c ∈ M.sets := by
  have singleton : ({c} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hc hc
  exact M.relationCompose_mem pairing unions powers separation hS
    (M.prod_mem pairing unions powers separation hC hQ) hQ hh
    (M.productSecond_mem pairing unions powers separation singleton hQ)

theorem groundEmbeddable_heightColumnFiber
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {S C Q h c N : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (hc : c ∈ M.sets) (hN : N ∈ M.sets)
    (height : InjectionCode S (ZFSet.prod C Q) h) (small : M.groundEmbeddable Q N) :
    M.groundEmbeddable (heightColumnFiber S C Q h c) N := by
  obtain ⟨f, hf, code⟩ := small
  exact ⟨relationCompose (heightColumnFiber S C Q h c) Q N (heightColumnGraph S C Q h c) f,
    M.relationCompose_mem pairing unions powers separation
      (M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh hc) hQ hN
      (M.heightColumnGraph_mem pairing unions powers separation hS hC hQ hh hc) hf,
    (heightColumnGraph_injection height c).compose code⟩

end TransitiveGround

end



section

open SetRealization
universe u

theorem ordinalSubset_has_least {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    {S : Set ZFSet.{u}} (subset : ∀ i ∈ S, i ∈ T) (inhabited : S.Nonempty) :
    ∃ i ∈ S, ∀ j ∈ S, i = j ∨ i ∈ j := by
  obtain ⟨i, hi, minimal⟩ := ZFSet.mem_wf.has_min S inhabited
  refine ⟨i, hi, ?_⟩
  intro j hj
  rcases ordinalSetProperty_mem_compare ordinal (subset i hi) (subset j hj) with h | h | h
  · exact Or.inr h
  · exact Or.inl h
  · exact False.elim (minimal j hj h)

theorem mem_ordinalIndexTail (S i j : ZFSet.{u}) :
    j ∈ ordinalIndexTail S i ↔ j ∈ S ∧ (i = j ∨ i ∈ j) := ZFSet.mem_sep

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem ordinalIndexTail_mem (separation : SeparationSchema M.sets)
    {S i : ZFSet.{u}} (hS : S ∈ M.sets) (hi : i ∈ M.sets) :
    ordinalIndexTail S i ∈ M.sets := by
  have selected := M.bounded_separation_mem separation (.disj (.equal 1 0) (.mem 1 0))
    (extend i Fin.elim0) (Fin.cases hi (fun j => Fin.elim0 j)) hS
  simpa only [BoundedFormula.truth_disj, BoundedFormula.Truth, extend, Fin.cases_zero,
    show (1 : Fin 2) = Fin.succ 0 from rfl, Fin.cases_succ, ordinalIndexTail] using selected

theorem groundCountable_descending_heights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S T C Q h : ZFSet.{u}} (hS : S ∈ M.sets) (hC : C ∈ M.sets)
    (hQ : Q ∈ M.sets) (hh : h ∈ M.sets) (subset : S ⊆ T)
    (ordinal : ordinalSetProperty T) (height : InjectionCode S (ZFSet.prod C Q) h)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (antitone : ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d r,
      ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d r) ∈ h →
        d = c ∨ d ∈ c) :
    M.groundEmbeddable S ZFSet.omega := by
  classical
  have hOmega := M.omega_mem separation infinite
  have tails : ∀ c, ∀ i ∈ S, ∀ q, ZFSet.pair i (ZFSet.pair c q) ∈ h →
      M.groundEmbeddable (ordinalIndexTail S i) ZFSet.omega := by
    intro c
    induction c using ZFSet.inductionOn with
    | h c ih =>
      intro i hi q iq
      have hc := (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iq)).2).1
      have groundTail := M.ordinalIndexTail_mem separation hS (M.transitive hS hi)
      have groundFiber := M.heightColumnFiber_mem pairing unions powers separation hS hC hQ hh
        (M.transitive hC hc)
      have smallFiber := M.groundEmbeddable_heightColumnFiber pairing unions powers separation
        hS hC hQ hh (M.transitive hC hc) hOmega height smallQ
      have columnBelow (k : ZFSet.{u}) (hk : k ∈ S) (later : i = k ∨ i ∈ k)
          (d r : ZFSet.{u}) (kr : ZFSet.pair k (ZFSet.pair d r) ∈ h) : d = c ∨ d ∈ c := by
        rcases later with rfl | later
        · obtain ⟨_, _, unique⟩ := height.function.2 i hi
          exact Or.inl (ZFSet.pair_inj.1 ((unique _ kr).trans (unique _ iq).symm)).1
        · exact antitone i hi k hk later c q d r iq kr
      let lower : Set ZFSet.{u} := {j | j ∈ S ∧ (i = j ∨ i ∈ j) ∧
        ∃ d r, d ∈ c ∧ ZFSet.pair j (ZFSet.pair d r) ∈ h}
      by_cases inhabited : lower.Nonempty
      · obtain ⟨j, hj, minimal⟩ := ordinalSubset_has_least ordinal
          (fun k hk => subset hk.1) inhabited
        obtain ⟨hjS, _, d, r, dc, jr⟩ := hj
        have smallLater := ih d dc j hjS r jr
        have smallUnion := M.groundCountable_binary_union pairing unions powers separation
          infinite choice groundFiber (M.ordinalIndexTail_mem separation hS (M.transitive hS hjS))
          smallFiber smallLater
        apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallUnion
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact ZFSet.mem_union.2 (Or.inl
            ((mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩))
        · have klower : k ∈ lower := ⟨hkS, later, e, s, less, kv⟩
          exact ZFSet.mem_union.2 (Or.inr
            ((mem_ordinalIndexTail S j k).2 ⟨hkS, minimal k klower⟩))
      · apply M.groundEmbeddable_restrict separation groundTail hOmega _ smallFiber
        intro k hk
        obtain ⟨hkS, later⟩ := (mem_ordinalIndexTail S i k).1 hk
        obtain ⟨v, kv, _⟩ := height.function.2 k hkS
        obtain ⟨e, he, s, hs, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 kv)).2
        rcases columnBelow k hkS later e s kv with eq | less
        · subst e
          exact (mem_heightColumnFiber S C Q h c k).2 ⟨hkS, he, s, hs, kv⟩
        · exact False.elim (inhabited ⟨k, hkS, later, e, s, less, kv⟩)
  by_cases inhabited : (S.toSet).Nonempty
  · obtain ⟨i, hi, minimal⟩ := ordinalSubset_has_least ordinal (fun _ hx => subset hx) inhabited
    obtain ⟨v, iv, _⟩ := height.function.2 i hi
    obtain ⟨c, _, q, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (height.function.1 iv)).2
    exact M.groundEmbeddable_restrict separation hS hOmega
      (fun j hj => (mem_ordinalIndexTail S i j).2 ⟨hj, minimal j hj⟩) (tails c i hi q iv)
  · have empty : S = ∅ := by
      apply ZFSet.ext
      intro x
      exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
        fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    rw [empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨S, hS⟩

end TransitiveGround






theorem essentialHeightComposite_strict {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt)
    {i j c q d v : ZFSet.{u}} (earlier : i ∈ j)
    (first : ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
    (second : ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height) :
    d ∈ c ∨ (d = c ∧ ZFSet.pair v q ∈ qlt) := by
  obtain ⟨_, _, x, hx, ix, xheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 first
  obtain ⟨_, _, y, hy, jy, yheight⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 second
  have xi := (pair_mem_relationConverse E S birth x i).1 (representatives ix)
  have yj := (pair_mem_relationConverse E S birth y j).1 (representatives jy)
  exact descent x hx y hy i j c q d v xi.2.2 yj.2.2 earlier xheight yheight

theorem essentialHeightComposite_antitone {S E C Q birth reps height qlt : ZFSet.{u}}
    (representatives : reps ⊆ relationConverse E S birth)
    (descent : EssentialHeightDescent E birth height qlt) :
    ∀ i ∈ S, ∀ j ∈ S, i ∈ j → ∀ c q d v,
      ZFSet.pair i (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
      ZFSet.pair j (ZFSet.pair d v) ∈ relationCompose S E (ZFSet.prod C Q) reps height →
        d = c ∨ d ∈ c := by
  intro i _ j _ earlier c q d v first second
  exact (essentialHeightComposite_strict representatives descent earlier first second).elim
    Or.inr (fun h => Or.inl h.1)

theorem essentialHeightComposite_injection {L S T E C Q birth reps height qlt : ZFSet.{u}}
    (stages : S ⊆ T) (ordinal : ordinalSetProperty T)
    (representatives : ZFSet.IsFunc S E reps)
    (chosenBirths : reps ⊆ relationConverse E S birth)
    (points : E ⊆ L) (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent E birth height qlt) :
    InjectionCode S (ZFSet.prod C Q) (relationCompose S E (ZFSet.prod C Q) reps height) := by
  have function := relationCompose_function_of_subset representatives heights points
  refine ⟨function, ?_⟩
  intro i j z first second
  have iShape := ZFSet.pair_mem_prod.1 (function.1 first)
  have jShape := ZFSet.pair_mem_prod.1 (function.1 second)
  obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 iShape.2
  have notEarlier (a b : ZFSet.{u})
      (aHeight : ZFSet.pair a (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height)
      (bHeight : ZFSet.pair b (ZFSet.pair c q) ∈ relationCompose S E (ZFSet.prod C Q) reps height) : a ∉ b := by
    intro earlier
    rcases essentialHeightComposite_strict chosenBirths descent earlier aHeight bHeight with h | h
    · exact ZFSet.mem_irrefl c h
    · exact irreflexive q hq h.2
  have eqI := ordinalSetProperty_eq_code_rank i (ordinalSetProperty_member ordinal (stages iShape.1))
  have eqJ := ordinalSetProperty_eq_code_rank j (ordinalSetProperty_member ordinal (stages jShape.1))
  rcases lt_trichotomy (ZFSet.rank i) (ZFSet.rank j) with earlier | equal | later
  · have ij : i ∈ j := by rw [eqI, eqJ, mem_ordinalCode_iff]; exact earlier
    exact False.elim (notEarlier i j first second ij)
  · exact eqI.trans ((congrArg ordinalCode equal).trans eqJ.symm)
  · have ji : j ∈ i := by rw [eqJ, eqI, mem_ordinalCode_iff]; exact later
    exact False.elim (notEarlier j i second first ji)

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_essentialBirthHeights
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    ∃ h ∈ M.sets,
      InjectionCode (essentialBirthIndices F T r birth) (ZFSet.prod C Q) h ∧
      (∀ i ∈ essentialBirthIndices F T r birth, ∀ j ∈ essentialBirthIndices F T r birth,
        i ∈ j → ∀ c q d v,
          ZFSet.pair i (ZFSet.pair c q) ∈ h → ZFSet.pair j (ZFSet.pair d v) ∈ h →
            d = c ∨ d ∈ c) ∧
      ∀ i z, ZFSet.pair i z ∈ h → ∃ x ∈ birthEssentialSet F T r birth,
        ZFSet.pair x i ∈ birth ∧ ZFSet.pair x z ∈ height := by
  let E := birthEssentialSet F T r birth
  let S := essentialBirthIndices F T r birth
  have hE := M.birthEssentialSet_mem separation hF hT hr hBirth
  have hS := M.essentialBirthIndices_mem separation hF hT hr hBirth
  obtain ⟨reps, hReps, function, chosen, _⟩ :=
    M.exists_essentialBirthRepresentatives pairing unions powers separation choice hF hT hr hBirth
  let h := relationCompose S E (ZFSet.prod C Q) reps height
  have ground : h ∈ M.sets := M.relationCompose_mem pairing unions powers separation hS hE
    (M.prod_mem pairing unions powers separation hC hQ) hReps hHeight
  have subset : S ⊆ T := fun _ hi => (mem_essentialBirthIndices F T r birth _).1 hi |>.1
  have points : E ⊆ L := fun _ hx => positive (birthEssentialSet_subset F T r birth hx)
  refine ⟨h, ground, essentialHeightComposite_injection subset ordinal function chosen points heights
    irreflexive descent, essentialHeightComposite_antitone chosen descent, ?_⟩
  intro i z hiz
  obtain ⟨_, _, x, hx, ix, xz⟩ := (pair_mem_relationCompose S E (ZFSet.prod C Q) reps height i z).1 hiz
  exact ⟨x, hx, ((pair_mem_relationConverse E S birth x i).1 (chosen ix)).2.2, xz⟩

theorem essentialBirthIndices_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T r birth C Q height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (positive : F ⊆ L) (ordinal : ordinalSetProperty T)
    (heights : ZFSet.IsFunc L (ZFSet.prod C Q) height)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (descent : EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt) :
    M.groundEmbeddable (essentialBirthIndices F T r birth) ZFSet.omega := by
  obtain ⟨h, hh, injection, antitone, _⟩ := M.exists_essentialBirthHeights pairing unions powers
    separation choice hF hT hr hBirth hC hQ hHeight positive ordinal heights irreflexive descent
  exact M.groundCountable_descending_heights pairing unions powers separation infinite choice
    (M.essentialBirthIndices_mem separation hF hT hr hBirth) hC hQ hh
    (fun _ hi => ((mem_essentialBirthIndices F T r birth _).1 hi).1)
    ordinal injection smallQ antitone

end TransitiveGround

end



open SetFormula
universe u


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageFromCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem birthEssential_below_earlier {L F T r μ birth x y a b : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (essential : x ∈ birthEssentialSet F T r birth) (positive : y ∈ F)
    (bornY : ZFSet.pair y a ∈ birth) (bornX : ZFSet.pair x b ∈ birth)
    (earlier : a ∈ b) : ZFSet.pair x y ∈ r ∧ x ≠ y := by
  classical
  have hx := (mem_birthEssentialSet F T r birth x).1 essential
  have xL := filter.subset hx.1
  have yL := filter.subset positive
  have bT := (ZFSet.pair_mem_prod.1 (born.1 bornX)).2
  have lower : ZFSet.pair x y ∈ r := by
    by_contra notLower
    obtain ⟨z, meetXY, _⟩ := meet.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨xL, yL⟩)
    have zL := (ZFSet.pair_mem_prod.1 (meet.operation.1 meetXY)).2
    obtain ⟨c, bornZ, _⟩ := born.2 z zL
    have cT := (ZFSet.pair_mem_prod.1 (born.1 bornZ)).2
    exact hx.2 z (filter.closed_meet x hx.1 y positive z meetXY) c cT b bT
      (meet.lower_left x y z meetXY) bornZ bornX
      (oldMeet x y z a b c bornY bornX earlier notLower meetXY bornZ)
  refine ⟨lower, ?_⟩
  intro equal
  subst y
  obtain ⟨t, _, unique⟩ := born.2 x xL
  have sameBirth : a = b := (unique a bornY).trans (unique b bornX).symm
  exact ZFSet.mem_irrefl b (sameBirth ▸ earlier)

theorem essentialHeightDescent_of_chronological_laws
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt) :
    EssentialHeightDescent (birthEssentialSet F T r birth) birth height qlt := by
  intro x hx y hy i j c q d v bornX bornY earlier heightX heightY
  have lower := birthEssential_below_earlier meet filter born oldMeet hy
    (birthEssentialSet_subset F T r birth hx) bornX bornY earlier
  exact strictHeight.strict y (filter.subset (birthEssentialSet_subset F T r birth hy))
    x (filter.subset (birthEssentialSet_subset F T r birth hx)) d v c q
    lower.1 lower.2 heightY heightX

end



section

universe u v

theorem mem_essentialBirthFiber (F T r birth t x : ZFSet.{u}) :
    x ∈ essentialBirthFiber F T r birth t ↔
      x ∈ birthEssentialSet F T r birth ∧ t ∈ T ∧ ZFSet.pair x t ∈ birth := by
  rw [essentialBirthFiber, mem_relationFiber, pair_mem_relationConverse]
  constructor
  · rintro ⟨hx, _, ht, born⟩
    exact ⟨hx, ((mem_essentialBirthIndices F T r birth t).1 ht).1, born⟩
  · rintro ⟨hx, ht, born⟩
    exact ⟨hx, hx, (mem_essentialBirthIndices F T r birth t).2 ⟨ht, x, hx, born⟩, born⟩

theorem essentialBirthFiber_subset (F T r birth t : ZFSet.{u}) :
    essentialBirthFiber F T r birth t ⊆ birthEssentialSet F T r birth :=
  fun _ hx => ((mem_essentialBirthFiber F T r birth t _).1 hx).1

theorem birthEssentials_no_oldBridge {L F T r μ birth t x y : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (hx : x ∈ birthEssentialSet F T r birth) (hy : y ∈ birthEssentialSet F T r birth)
    (xt : ZFSet.pair x t ∈ birth) (yt : ZFSet.pair y t ∈ birth) :
    ¬ OldBridgeCode L r μ birth t x y := by
  have xE := (mem_birthEssentialSet F T r birth x).1 hx
  have yE := (mem_birthEssentialSet F T r birth y).1 hy
  have ht := (ZFSet.pair_mem_prod.1 (born.1 xt)).2
  intro bridge
  rcases bridge with ⟨z, a, meetXY, za, old⟩ | ⟨z, hz, a, za, old, intermediate⟩
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    exact xE.2 z (filter.closed_meet x xE.1 y yE.1 z meetXY) a ha t ht
      (meet.lower_left x y z meetXY) za xt old
  · have ha := (ZFSet.pair_mem_prod.1 (born.1 za)).2
    rcases intermediate with ⟨xz, zy⟩ | ⟨yz, zx⟩
    · exact yE.2 z (filter.upward x xE.1 z hz xz) a ha t ht zy za yt old
    · exact xE.2 z (filter.upward y yE.1 z hz yz) a ha t ht zx za xt old

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem essentialBirthFiber_mem (separation : SeparationSchema M.sets)
    {F T r birth t : ZFSet.{u}} (hF : F ∈ M.sets) (hT : T ∈ M.sets)
    (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets) (ht : t ∈ M.sets) :
    essentialBirthFiber F T r birth t ∈ M.sets := by
  let E := birthEssentialSet F T r birth
  let params := extend t (extend T (extend birth Fin.elim0))
  let φ : BoundedFormula 4 := .conj (.mem 1 2) (BoundedFormula.pairMembershipFormula 0 1 3)
  have selected := M.bounded_separation_mem separation φ params
    (Fin.cases ht (Fin.cases hT (Fin.cases hBirth (fun j => Fin.elim0 j))))
    (M.birthEssentialSet_mem separation hF hT hr hBirth)
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth φ (extend x params)) E =
      essentialBirthFiber F T r birth t := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_essentialBirthFiber]
    exact and_congr Iff.rfl
      (and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 0 1 3 _))
  exact eq ▸ selected

end TransitiveGround

end



end PartitionPilot.Forcing

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

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFilterCopies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem meetFilter_copyPullback {A L rA rL μA μL e F : ZFSet.{u}}
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (nonempty : (copyPullback A L e F).Nonempty) :
    MeetFilterCode A rA μA (copyPullback A L e F) where
  subset := fun x hx => ((mem_copyPullback A L e F x).1 hx).1
  nonempty := nonempty
  upward := by
    intro x hx y hy lower
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨y', yy', _⟩ := embedding.injection.function.2 y hy
    have hyL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 yy')).2
    have hyF := target.upward x' hxF y' hyL (embedding.monotone x y x' y' lower xx' yy')
    exact (mem_copyPullback A L e F y).2 ⟨hy, y', hyF, hyL, yy'⟩
  closed_meet := by
    intro x hx y hy z meetXY
    obtain ⟨_, x', hxF, _, xx'⟩ := (mem_copyPullback A L e F x).1 hx
    obtain ⟨_, y', hyF, _, yy'⟩ := (mem_copyPullback A L e F y).1 hy
    have hzA := (ZFSet.pair_mem_prod.1 (source.operation.1 meetXY)).2
    obtain ⟨z', zz', _⟩ := embedding.injection.function.2 z hzA
    have hzL := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 zz')).2
    have hzF := target.closed_meet x' hxF y' hyF z'
      (embedding.map_meet x y z x' y' z' meetXY xx' yy' zz')
    exact (mem_copyPullback A L e F z).2 ⟨hzA, z', hzF, hzL, zz'⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem internalCountableBelow_copy_of_all_filters
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A L rA rL μA μL e F : ZFSet.{u}}
    (hA : A ∈ M.sets) (hL : L ∈ M.sets) (he : e ∈ M.sets) (hF : F ∈ M.sets)
    (source : MeetOrderCode A rA μA) (target : MeetFilterCode L rL μL F)
    (embedding : MeetEmbeddingCode A L rA rL μA μL e)
    (earlier : ∀ P ∈ M.sets, MeetFilterCode A rA μA P → M.InternalCountableBelow rA P P) :
    M.InternalCountableBelow rL F (F ∩ relationImage A L e) := by
  classical
  by_cases nonempty : (copyPullback A L e F).Nonempty
  · have pullbackMember := M.copyPullback_mem pairing unions powers separation hA hL he hF
    have pullbackFilter := meetFilter_copyPullback source target embedding nonempty
    exact M.internalCountableBelow_copy_pullback pairing unions powers separation infinite hL he
      embedding.injection embedding.monotone
      (earlier (copyPullback A L e F) pullbackMember pullbackFilter)
  · refine ⟨∅, M.empty_mem ⟨F, hF⟩, M.empty_groundEmbeddable ZFSet.omega ⟨F, hF⟩,
      ZFSet.empty_subset F, ?_⟩
    intro x hx
    obtain ⟨hxF, image⟩ := ZFSet.mem_inter.1 hx
    obtain ⟨hxL, y, hyA, yx⟩ := (mem_relationImage A L e x).1 image
    exact False.elim (nonempty ⟨y,
      (mem_copyPullback A L e F y).2 ⟨hyA, x, hxF, hxL, yx⟩⟩)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundAttachmentEmbeddings
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing




universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem attachmentIdeal_mem (separation : SeparationSchema M.sets)
    {Q rQ a : ZFSet.{u}} (hQ : Q ∈ M.sets) (hrQ : rQ ∈ M.sets)
    (ha : a ∈ M.sets) : attachmentIdeal Q rQ a ∈ M.sets := by
  let params := extend a (extend rQ Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairMembershipFormula 0 1 2) params
    (Fin.cases ha (Fin.cases hrQ (fun i => Fin.elim0 i))) hQ
  have equal : ZFSet.sep (fun q => BoundedFormula.Truth
      (BoundedFormula.pairMembershipFormula 0 1 2) (extend q params)) Q =
      attachmentIdeal Q rQ a := by
    apply ZFSet.ext
    intro q
    rw [ZFSet.mem_sep, mem_attachmentIdeal, BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround






end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GrowthLayerSourceCongruence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

namespace CodedGrowthLayer

open SetFormula

theorem internal_countable_essentials
    {M : TransitiveGround.{u}} {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {L F T r μ birth t : ZFSet.{u}}
    (layer : CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hL : L ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (ht : t ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth)
    (earlier : ∀ s ∈ t, Space s ∈ M.sets ∧
      MeetOrderCode (Space s) (sourceOrder s) (sourceMeet s) ∧
      ∀ P ∈ M.sets, MeetFilterCode (Space s) (sourceOrder s) (sourceMeet s) P →
        M.InternalCountableBelow (sourceOrder s) P P) :
    M.InternalCountableBelow r F (essentialBirthFiber F T r birth t) := by
  classical
  have groundFiber := M.essentialBirthFiber_mem separation hF hT hr hBirth ht
  have positive : essentialBirthFiber F T r birth t ⊆ F :=
    fun _ hx => birthEssentialSet_subset F T r birth
      (essentialBirthFiber_subset F T r birth t hx)
  have points : essentialBirthFiber F T r birth t ⊆ L := fun _ hx => filter.subset (positive hx)
  cases layer with
  | countablePoints D _ small cover =>
    have subset : essentialBirthFiber F T r birth t ⊆ D := by
      intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    have countableFiber := M.groundEmbeddable_restrict separation groundFiber
      (M.omega_mem separation infinite) subset small
    exact M.internalCountableBelow_of_countable groundFiber countableFiber positive
      (fun x hx => meet.order.refl x (points hx))
  | copies I parts groundI small groundParts index e previous groundCopy embedding cover inCopy =>
    apply M.internalCountableBelow_indexed_union pairing unions powers separation infinite choice
      groundI hr hF groundFiber groundParts small
    · intro x hx
      exact cover x (points hx) ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2
    · intro i hi
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i hi)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i hi) hF source filter (embedding i hi) sourceBases
      apply basis.mono
      intro x hx
      obtain ⟨hxFiber, part⟩ := (mem_relationFiber (essentialBirthFiber F T r birth t) parts i x).1 hx
      exact ZFSet.mem_inter.2 ⟨positive hxFiber, inCopy i hi x (points hxFiber) part⟩
  | separated I index e previous groundCopy embedding component cover separated =>
    by_cases inhabited : (essentialBirthFiber F T r birth t).Nonempty
    · obtain ⟨x, hx⟩ := inhabited
      let representative : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨x, points hx, ((mem_essentialBirthFiber F T r birth t x).1 hx).2.2⟩
      let i := component representative
      obtain ⟨groundA, source, sourceBases⟩ := earlier (index i) (previous i)
      have basis := M.internalCountableBelow_copy_of_all_filters pairing unions powers separation
        infinite groundA hL (groundCopy i) hF source filter (embedding i) sourceBases
      apply basis.mono
      intro y hy
      let current : {x : ZFSet.{u} // x ∈ L ∧ ZFSet.pair x t ∈ birth} :=
        ⟨y, points hy, ((mem_essentialBirthFiber F T r birth t y).1 hy).2.2⟩
      have same : component current = i := by
        by_contra different
        exact birthEssentials_no_oldBridge meet filter born
          (essentialBirthFiber_subset F T r birth t hy)
          (essentialBirthFiber_subset F T r birth t hx)
          current.property.2 representative.property.2 (separated current representative different)
      have inside := cover current
      rw [same] at inside
      exact ZFSet.mem_inter.2 ⟨positive hy, inside⟩
    · have empty : essentialBirthFiber F T r birth t = ∅ := by
        apply ZFSet.ext
        intro x
        exact ⟨fun hx => False.elim (inhabited ⟨x, hx⟩),
          fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
      rw [empty]
      exact M.internalCountableBelow_empty ⟨F, hF⟩ r F

end CodedGrowthLayer

end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceSupportEvaluation
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
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

variable [OrderTop P]

theorem niceSupportEvaluationName_entry (tau : Name s)
    (member : tau.val ∈ M.niceSupportNameCodes a s T K)
    (H : ConditionFilter P) (x : ZFSet.{u}) :
    ZFSet.pair tau.val x ∈ Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K) ↔
      Name.eval {p | H.mem p} tau = x := by
  let i : (M.niceSupportNameCodes a s T K).toSet := ⟨tau.val, member⟩
  have same : (⟨(codeFunction (M.niceSupportNameCodes a s T K)).value i,
      codeIsName M a s T K i⟩ : Name s) = tau := Subtype.ext (codeValue _ i)
  exact (Name.pair_mem_eval_indexedGraphName {p | H.mem p} ⊤ H.top_mem
    (codeFunction (M.niceSupportNameCodes a s T K)) (codeIsName M a s T K) i x).trans
      (by rw [same])

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNameSequenceForcingWitness
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula SetRealization
universe u

namespace Name
variable {P : Type u} [Preorder P] (s : Presentation P)

theorem sequenceDecision_mono (one : P) (τ : Name s) {p q : P}
    (before : q ≤ p) {n a : ZFSet.{u}} (decision : sequenceDecision s one τ p n a) :
    sequenceDecision s one τ q n a := forcesMem_mono decision before

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_nameSequenceDecisionFormula (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (τ : (M.nameDomain s).names) (p : P) (n a : ZFSet.{u})
    (hn : n ∈ M.sets) (ha : a ∈ M.sets) :
    Realize M.sets nameSequenceDecisionFormula
      (extend (s.encode p) (extend n (extend a (extend τ.val.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode one) Fin.elim0))))))) ↔
      Name.sequenceDecision s one τ.val p n a := by
  have hone := M.transitive carrier (s.encode_mem one)
  have hp := M.transitive carrier (s.encode_mem p)
  have hpair := M.orderedPair_mem pairing hn ha
  have hcheck := M.check_mem s one pairing unions powers separation collection hone _ hpair
  let checked : (M.nameDomain s).names := ⟨Name.check s one (ZFSet.pair n a), hcheck⟩
  let env := extend (s.encode p) (extend n (extend a (extend τ.val.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode one) Fin.elim0))))))
  have forcing :
      Realize M.sets
        (forcingTranslation (ordinaryGroundPrimitives 0 1) (.mem 0 1)
          (extend 6 (extend 7 Fin.elim0)) 2 (extend 0 (extend 5 Fin.elim0)))
        (extend checked.val.val (extend (ZFSet.pair n a) env)) ↔
      Name.sequenceDecision s one τ.val p n a :=
    M.realize_ordinaryGroundForcing s pairing unions powers separation collection carrier order
      0 1 (.mem 0 1) (extend 6 (extend 7 Fin.elim0)) 2 (extend 0 (extend 5 Fin.elim0))
      _ rfl rfl p (extend checked (extend τ Fin.elim0)) rfl
      (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))
  rw [nameSequenceDecisionFormula, realize_ex]
  constructor
  · rintro ⟨v, hv, rest⟩
    obtain ⟨w, hw, pair, check, forced⟩ := (realize_ex M.sets _ _).1 rest
    have pairEq : v = ZFSet.pair n a := (M.realize_orderedPairFormula pairing 1 3 4
      (extend w (extend v env)) hv hn ha).1 pair
    rw [realize_binaryApplication, map_extend, map_empty] at check
    have checkEq := (M.realize_uniformCheckFormula s one pairing unions powers separation collection
      hone v w hv hw).1 check
    subst v
    subst w
    exact forcing.1 forced
  · intro decision
    refine ⟨ZFSet.pair n a, hpair, ?_⟩
    rw [realize_ex]
    refine ⟨checked.val.val, hcheck, ?_, ?_, forcing.2 decision⟩
    · exact (M.realize_orderedPairFormula pairing 1 3 4
        (extend checked.val.val (extend (ZFSet.pair n a) env)) hpair hn ha).2 rfl
    · rw [realize_binaryApplication, map_extend, map_empty]
      exact (M.realize_uniformCheckFormula s one pairing unions powers separation collection
        hone _ _ hpair hcheck).2 rfl

end TransitiveGround

namespace Name
variable {P : Type u} [Preorder P] (s : Presentation P)

theorem mem_sequenceDecisionRelation (one : P) (τ : Name s) (N U z : ZFSet.{u}) :
    z ∈ sequenceDecisionRelation s one τ N U ↔
      ∃ p : P, ∃ n ∈ N, ∃ a ∈ U,
        z = ZFSet.pair (ZFSet.pair (s.encode p) n) a ∧ sequenceDecision s one τ p n a := by
  rw [sequenceDecisionRelation, ZFSet.mem_sep]
  refine ⟨fun h => h.2, ?_⟩
  rintro ⟨p, n, hn, a, ha, rfl, decision⟩
  exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨s.encode_mem p, hn⟩, ha⟩,
    p, n, hn, a, ha, rfl, decision⟩

theorem sequenceDecisionRelation_entry (one : P) (τ : Name s) (N U : ZFSet.{u})
    (p : P) (n a : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ sequenceDecisionRelation s one τ N U ↔
      n ∈ N ∧ a ∈ U ∧ sequenceDecision s one τ p n a := by
  rw [mem_sequenceDecisionRelation]
  constructor
  · rintro ⟨q, m, hm, b, hb, equal, decision⟩
    obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨condition, rfl⟩ := ZFSet.pair_inj.1 inner
    have same := s.injective condition
    subst q
    exact ⟨hm, hb, decision⟩
  · rintro ⟨hn, ha, decision⟩
    exact ⟨p, n, hn, a, ha, rfl, decision⟩

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_nameSequenceDecisionEntryFormula (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (τ : (M.nameDomain s).names) {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets nameSequenceDecisionEntryFormula
      (extend z (extend N (extend U (extend τ.val.val
        (extend s.carrier (extend s.conditionOrder (extend (s.encode one) Fin.elim0))))))) ↔
      z ∈ Name.sequenceDecisionRelation s one τ.val N U := by
  let env := extend z (extend N (extend U (extend τ.val.val
    (extend s.carrier (extend s.conditionOrder (extend (s.encode one) Fin.elim0))))))
  have members : ∀ j, env j ∈ M.sets := Fin.cases hz (Fin.cases hN (Fin.cases hU
    (Fin.cases τ.property (Fin.cases carrier (Fin.cases order
      (Fin.cases (M.transitive carrier (s.encode_mem one)) (fun i => Fin.elim0 i)))))))
  have shape (p n a : ZFSet.{u}) (hp : p ∈ M.sets) (hn : n ∈ M.sets) (ha : a ∈ M.sets) :
      Realize M.sets (BoundedFormula.orderedTripleFormula 3 2 1 0).toFormula
        (extend a (extend n (extend p env))) ↔ z = ZFSet.pair (ZFSet.pair p n) a :=
    (BoundedFormula.realize_toFormula M _ _ (Fin.cases ha (Fin.cases hn (Fin.cases hp members)))).trans
      (BoundedFormula.truth_orderedTripleFormula 3 2 1 0 _)
  rw [nameSequenceDecisionEntryFormula, realize_ex, Name.mem_sequenceDecisionRelation]
  constructor
  · rintro ⟨v, hv, rest⟩
    obtain ⟨n, hnM, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨a, haM, hvP, hn, ha, pair, decision⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨p, rfl⟩ := (s.mem_carrier v).1 hvP
    rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
      map_extend, map_extend, map_empty] at decision
    exact ⟨p, n, hn, a, ha, (shape _ _ _ hv hnM haM).1 pair,
      (M.realize_nameSequenceDecisionFormula s one pairing unions powers separation collection
        carrier order τ p n a hnM haM).1 decision⟩
  · rintro ⟨p, n, hn, a, ha, pair, decision⟩
    have hp := M.transitive carrier (s.encode_mem p)
    have hnM := M.transitive hN hn
    have haM := M.transitive hU ha
    refine ⟨s.encode p, hp, ?_⟩
    rw [realize_ex]
    refine ⟨n, hnM, ?_⟩
    rw [realize_ex]
    refine ⟨a, haM, s.encode_mem p, hn, ha, (shape _ _ _ hp hnM haM).2 pair, ?_⟩
    rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
      map_extend, map_extend, map_empty]
    exact (M.realize_nameSequenceDecisionFormula s one pairing unions powers separation collection
      carrier order τ p n a hnM haM).2 decision

theorem sequenceDecisionRelation_mem (one : P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (τ : (M.nameDomain s).names) {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets) :
    Name.sequenceDecisionRelation s one τ.val N U ∈ M.sets := by
  let params := extend N (extend U (extend τ.val.val (extend s.carrier
    (extend s.conditionOrder (extend (s.encode one) Fin.elim0)))))
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation carrier hN) hU
  have selected := M.separation_mem separation nameSequenceDecisionEntryFormula params
    (Fin.cases hN (Fin.cases hU (Fin.cases τ.property (Fin.cases carrier
      (Fin.cases order (Fin.cases (M.transitive carrier (s.encode_mem one))
        (fun i => Fin.elim0 i))))))) bound
  have equal : ZFSet.sep (fun z => Realize M.sets nameSequenceDecisionEntryFormula (extend z params))
      (ZFSet.prod (ZFSet.prod s.carrier N) U) = Name.sequenceDecisionRelation s one τ.val N U := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, code⟩
      exact (M.realize_nameSequenceDecisionEntryFormula s one pairing unions powers separation
        collection carrier order τ hN hU z (M.transitive bound hz)).1 code
    · intro hz
      have bounded := (ZFSet.mem_sep.1 hz).1
      exact ⟨bounded, (M.realize_nameSequenceDecisionEntryFormula s one pairing unions powers separation
        collection carrier order τ hN hU z (M.transitive bound bounded)).2 hz⟩
  exact equal ▸ selected

end TransitiveGround
end

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (carrier : s.carrier ∈ M.sets)

theorem sequenceFunction_eval {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets)
    (τ : (M.nameDomain s).names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s))) {p₀ : P} (hp₀ : H.mem p₀)
    (forced : Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ) p₀) :
    ZFSet.IsFunc N U (Name.eval {q | H.mem q} τ.val) := by
  let env := M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  have truth := forces_sound (M.nameDomain s) H generic _ env hp₀ forced
  have function := (BoundedFormula.truth_functionFormula 0 1 2
    (evalAssignment {q | H.mem q} env)).1
      ((BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨env j, rfl⟩)).1 truth)
  change ZFSet.IsFunc (Name.eval {q | H.mem q} (Name.check s ⊤ N))
    (Name.eval {q | H.mem q} (Name.check s ⊤ U)) (Name.eval {q | H.mem q} τ.val) at function
  simpa only [Name.eval_check (s := s) {q | H.mem q} ⊤ H.top_mem] using function

include pairing unions powers separation collection carrier in
theorem sequenceDecision_reading (τ : (M.nameDomain s).names) (n a : ZFSet.{u})
    (hn : n ∈ M.sets) (ha : a ∈ M.sets) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    ZFSet.pair n a ∈ Name.eval {q | H.mem q} τ.val ↔
      ∃ p, H.mem p ∧ Name.sequenceDecision s ⊤ τ.val p n a := by
  have hcheck := M.check_mem s ⊤ pairing unions powers separation collection
    (M.transitive carrier (s.encode_mem ⊤)) _ (M.orderedPair_mem pairing hn ha)
  have exactReading := Name.eval_mem_iff_forcesMem (M.nameDomain s) H
    (fun E member => generic E (Or.inl member)) hcheck τ.property
  simpa only [Name.eval_check (s := s) {q | H.mem q} ⊤ H.top_mem, Name.sequenceDecision] using exactReading

theorem sequenceDecision_unique_below (small : M.sets.Countable)
    {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets) (τ : (M.nameDomain s).names)
    {p₀ : P}
    (forced : Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ) p₀)
    {p : P} (before : p ≤ p₀) {n a b : ZFSet.{u}} (hn : n ∈ N) (ha : a ∈ U) (hb : b ∈ U)
    (first : Name.sequenceDecision s ⊤ τ.val p n a)
    (second : Name.sequenceDecision s ⊤ τ.val p n b) : a = b := by
  let : Countable P := M.conditions_countable s small carrier
  obtain ⟨H, hp, generic⟩ := exists_generic_formulaFamily (M.nameDomain s)
    (M.nameDomain_countable s small) p
  have function := M.sequenceFunction_eval s pairing unions powers separation collection carrier
    hN hU τ H generic (H.upward hp before) forced
  have firstEntry := (M.sequenceDecision_reading s pairing unions powers separation collection carrier
    τ n a (M.transitive hN hn) (M.transitive hU ha) H generic).2 ⟨p, hp, first⟩
  have secondEntry := (M.sequenceDecision_reading s pairing unions powers separation collection carrier
    τ n b (M.transitive hN hn) (M.transitive hU hb) H generic).2 ⟨p, hp, second⟩
  obtain ⟨v, _, unique⟩ := function.2 n hn
  exact (unique a firstEntry).trans (unique b secondEntry).symm

theorem sequenceDecision_dense_below (small : M.sets.Countable)
    {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets) (τ : (M.nameDomain s).names)
    {p₀ : P}
    (forced : Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ) p₀)
    {n : ZFSet.{u}} (hn : n ∈ N) :
    DenseBelow p₀ {q | ∃ a ∈ U, Name.sequenceDecision s ⊤ τ.val q n a} := by
  intro q before
  let : Countable P := M.conditions_countable s small carrier
  obtain ⟨H, hq, generic⟩ := exists_generic_formulaFamily (M.nameDomain s)
    (M.nameDomain_countable s small) q
  have function := M.sequenceFunction_eval s pairing unions powers separation collection carrier
    hN hU τ H generic (H.upward hq before) forced
  obtain ⟨a, entry, _⟩ := function.2 n hn
  have ha : a ∈ U := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  obtain ⟨r, hr, decision⟩ := (M.sequenceDecision_reading s pairing unions powers separation collection
    carrier τ n a (M.transitive hN hn) (M.transitive hU ha) H generic).1 entry
  obtain ⟨t, _, tq, tr⟩ := H.directed hq hr
  exact ⟨t, tq, a, ha, Name.sequenceDecision_mono s ⊤ τ.val tr decision⟩

end TransitiveGround

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P]
variable (s : Presentation P)

theorem exists_sequenceFunction_forcing
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (carrier : s.carrier ∈ M.sets)
    {N U : ZFSet.{u}} (hN : N ∈ M.sets) (hU : U ∈ M.sets)
    (τ : (M.nameDomain s).names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (function : ZFSet.IsFunc N U (Name.eval {q | H.mem q} τ.val)) :
    ∃ p, H.mem p ∧ Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ) p := by
  let env := M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier hN hU τ
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive {q | H.mem q}⟩
  apply (forcing_truth (M.nameDomain s) H generic _ env).1
  apply (BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨env j, rfl⟩)).2
  apply (BoundedFormula.truth_functionFormula 0 1 2 (evalAssignment {q | H.mem q} env)).2
  change ZFSet.IsFunc (Name.eval {q | H.mem q} (Name.check s ⊤ N))
    (Name.eval {q | H.mem q} (Name.check s ⊤ U)) (Name.eval {q | H.mem q} τ.val)
  simpa only [Name.eval_check (s := s) {q | H.mem q} ⊤ H.top_mem] using function

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSerialOrbits
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundSerialOrbit
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {W R initial : ZFSet.{u}} (hW : W ∈ M.sets) (hR : R ∈ M.sets)
    (hInitial : initial ∈ W)
    (serial : ∀ x ∈ W, ∃ y ∈ W, ZFSet.pair x y ∈ R) :
    ∃ history ∈ M.sets, ZFSet.IsFunc ZFSet.omega W history ∧
      (∀ y, ZFSet.pair ∅ y ∈ history ↔ y = initial) ∧
      ∀ n ∈ ZFSet.omega, ∀ x y,
        ZFSet.pair n x ∈ history → ZFSet.pair (insert n n) y ∈ history → ZFSet.pair x y ∈ R := by
  obtain ⟨step, hStep, function, selected⟩ :=
    M.uniformize_relation pairing unions powers separation choice hW hW hR serial
  let s := SetMembers.presentation W
  let f := s.decodeFunction s step function
  let b := SetMembers.ofMem initial hInitial
  have graphGround : s.graph s f ∈ M.sets :=
    M.decoded_function_graph_mem s s hStep function
  let history := natPresentation.graph s (fun n => natIterate f b n.down)
  have historyGround : history ∈ M.sets :=
    M.natural_recursion_graph_mem pairing unions powers separation infinite s f b hW graphGround
  have historyFunction : ZFSet.IsFunc ZFSet.omega W history := natPresentation.graph_isFunc s _
  have canonical (n : Nat) :
      ZFSet.pair (natSetCode n) (s.encode (natIterate f b n)) ∈ history :=
    (natPresentation.pair_mem_graph s (fun n => natIterate f b n.down) ⟨n⟩ _).2 rfl
  have entryValue (n : Nat) (y : ZFSet.{u})
      (entry : ZFSet.pair (natSetCode n) y ∈ history) : y = s.encode (natIterate f b n) := by
    obtain ⟨_, _, unique⟩ := historyFunction.2 (natSetCode n) (natSetCode_mem_omega n)
    exact (unique y entry).trans (unique _ (canonical n)).symm
  refine ⟨history, historyGround, historyFunction, ?_, ?_⟩
  · intro y
    constructor
    · intro entry
      exact (entryValue 0 y entry).trans (SetMembers.raw_ofMem initial hInitial)
    · intro equal
      exact equal.symm ▸ (SetMembers.raw_ofMem initial hInitial ▸ canonical 0)
  · intro n hn x y first second
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have firstValue := entryValue k x first
    have secondValue := entryValue (k + 1) y second
    rw [firstValue, secondValue]
    exact selected (s.decodeFunction_mem s step function (natIterate f b k))

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNameSequenceValues
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem pair_mem_decisionStepGraph (P r U D n p m q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair n p) (ZFSet.pair m q) ∈ decisionStepGraph P r U D ↔
      n ∈ ZFSet.omega ∧ p ∈ P ∧ m ∈ ZFSet.omega ∧ q ∈ P ∧
        m = insert n n ∧ ZFSet.pair q p ∈ r ∧
          ∃ a ∈ U, ZFSet.pair (ZFSet.pair q n) a ∈ D := by
  rw [decisionStepGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, n', hn, p', hp, m', hm, q', hq, a, ha, equal, clock, stronger, decision⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
    exact ⟨hn, hp, hm, hq, clock, stronger, a, ha, decision⟩
  · rintro ⟨hn, hp, hm, hq, clock, stronger, a, ha, decision⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hn, hp⟩,
      ZFSet.pair_mem_prod.2 ⟨hm, hq⟩⟩, n, hn, p, hp, m, hm, q, hq,
      a, ha, rfl, clock, stronger, decision⟩

namespace BoundedFormula
open SetFormula

theorem truth_decisionStepEntryFormula (env : Fin 6 → ZFSet.{u}) :
    Truth decisionStepEntryFormula env ↔
      ∃ n ∈ env 1, ∃ p ∈ env 2, ∃ m ∈ env 1, ∃ q ∈ env 2, ∃ a ∈ env 4,
        env 0 = ZFSet.pair (ZFSet.pair n p) (ZFSet.pair m q) ∧
        m = insert n n ∧ ZFSet.pair q p ∈ env 3 ∧
          ZFSet.pair (ZFSet.pair q n) a ∈ env 5 := by
  simp only [decisionStepEntryFormula, truth_exMem, Truth, truth_pairOfPairsFormula,
    truth_successorFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem decisionStepGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {P r U D : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hU : U ∈ M.sets) (hD : D ∈ M.sets) : decisionStepGraph P r U D ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hW := M.prod_mem pairing unions powers separation hw hP
  let params := extend ZFSet.omega (extend P (extend r (extend U (extend D Fin.elim0))))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hw (Fin.cases hP (Fin.cases hr (Fin.cases hU (Fin.cases hD (fun j => Fin.elim0 j)))))
  have selected := M.bounded_separation_mem separation BoundedFormula.decisionStepEntryFormula
    params members (M.prod_mem pairing unions powers separation hW hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.decisionStepEntryFormula
      (extend z params)) (ZFSet.prod (ZFSet.prod ZFSet.omega P) (ZFSet.prod ZFSet.omega P)) =
        decisionStepGraph P r U D := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, decisionStepGraph, ZFSet.mem_sep,
      BoundedFormula.truth_decisionStepEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem exists_groundDecisionChain
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (order : s.conditionOrder ∈ M.sets) {S U D : ZFSet.{u}}
    (hS : S ∈ M.sets) (hU : U ∈ M.sets) (hD : D ∈ M.sets) (subset : S ⊆ s.carrier)
    (p : P) (hp : s.encode p ∈ S)
    (dense : ∀ n : Nat, ∀ p : P, s.encode p ∈ S →
      ∃ q, q ≤ p ∧ s.encode q ∈ S ∧
        ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) (natSetCode n)) a ∈ D) :
    ∃ seq : Nat → P, seq 0 = p ∧
      natPresentation.graph s (fun n => seq n.down) ∈ M.sets ∧ Antitone seq ∧
      (∀ n, s.encode (seq n) ∈ S) ∧
      ∀ n, ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode (seq (n + 1))) (natSetCode n)) a ∈ D := by
  have hw := M.omega_mem separation infinite
  let W := ZFSet.prod ZFSet.omega S
  let R := decisionStepGraph S s.conditionOrder U D
  have hW : W ∈ M.sets := M.prod_mem pairing unions powers separation hw hS
  have hR : R ∈ M.sets := M.decisionStepGraph_mem pairing unions powers separation infinite hS order hU hD
  have serial : ∀ x ∈ W, ∃ y ∈ W, ZFSet.pair x y ∈ R := by
    intro x hx
    obtain ⟨n, hn, raw, hraw, rfl⟩ := ZFSet.mem_prod.1 hx
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨q, rfl⟩ := (s.mem_carrier raw).1 (subset hraw)
    obtain ⟨r, stronger, hr, a, ha, decision⟩ := dense k q hraw
    exact ⟨ZFSet.pair (natSetCode (k + 1)) (s.encode r),
      ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _, hr⟩,
      (pair_mem_decisionStepGraph _ _ _ _ _ _ _ _).2
        ⟨natSetCode_mem_omega _, hraw, natSetCode_mem_omega _, hr, rfl,
          (s.pair_mem_conditionOrder r q).2 stronger, a, ha, decision⟩⟩
  obtain ⟨history, hHistory, function, zero, next⟩ :=
    M.exists_groundSerialOrbit pairing unions powers separation infinite choice hW hR
      (ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega 0, hp⟩) serial
  let t := natPresentation.product (SetMembers.presentation S)
  let state : Nat → ULift.{u} Nat × SetMembers S :=
    fun n => natPresentation.decodeFunction t history function ⟨n⟩
  have entry (n : Nat) : ZFSet.pair (natSetCode n)
      (ZFSet.pair (natSetCode (state n).1.down) (SetMembers.raw (state n).2)) ∈ history :=
    natPresentation.decodeFunction_mem t history function ⟨n⟩
  have initial : natSetCode (state 0).1.down = natSetCode 0 ∧
      SetMembers.raw (state 0).2 = s.encode p :=
    ZFSet.pair_inj.1 ((zero _).1 (entry 0))
  have steps (n : Nat) := (pair_mem_decisionStepGraph S s.conditionOrder U D
    (natSetCode (state n).1.down) (SetMembers.raw (state n).2)
    (natSetCode (state (n + 1)).1.down) (SetMembers.raw (state (n + 1)).2)).1
      (next (natSetCode n) (natSetCode_mem_omega n) _ _ (entry n) (entry (n + 1)))
  have clock (n : Nat) : (state n).1.down = n := by
    induction n with
    | zero => exact natSetCode_injective initial.1
    | succ n ih =>
      have h : natSetCode (state (n + 1)).1.down = natSetCode ((state n).1.down + 1) :=
        (steps n).2.2.2.2.1
      exact (natSetCode_injective h).trans (congrArg (fun k => k + 1) ih)
  let graph := relationCompose ZFSet.omega W S history (productSecond ZFSet.omega S)
  have graphGround : graph ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hw hW hS hHistory (M.productSecond_mem pairing unions powers separation hw hS)
  have smallFunction : ZFSet.IsFunc ZFSet.omega S graph :=
    relationCompose_function_of_subset function (productSecond_function ZFSet.omega S) (fun _ h => h)
  have graphFunction : ZFSet.IsFunc ZFSet.omega s.carrier graph := by
    refine ⟨?_, smallFunction.2⟩
    intro z hz
    obtain ⟨n, hn, q, hq, rfl⟩ := ZFSet.mem_prod.1 (smallFunction.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hn, subset hq⟩
  let seq : Nat → P := fun n => natPresentation.decodeFunction s graph graphFunction ⟨n⟩
  have projected (n : Nat) : ZFSet.pair (natSetCode n) (SetMembers.raw (state n).2) ∈ graph :=
    (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨natSetCode_mem_omega n, SetMembers.raw_mem _, _,
        ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _, SetMembers.raw_mem _⟩, entry n,
        (mem_productSecond _ _ _).2 ⟨_, natSetCode_mem_omega _, _, SetMembers.raw_mem _, rfl⟩⟩
  have value (n : Nat) : s.encode (seq n) = SetMembers.raw (state n).2 := by
    obtain ⟨_, _, unique⟩ := graphFunction.2 (natSetCode n) (natSetCode_mem_omega n)
    exact (unique _ (natPresentation.decodeFunction_mem s graph graphFunction ⟨n⟩)).trans
      (unique _ (projected n)).symm
  refine ⟨seq, s.injective ((value 0).trans initial.2),
    M.decoded_function_graph_mem natPresentation s graphGround graphFunction, ?_, ?_, ?_⟩
  · apply antitone_nat_of_succ_le
    intro n
    apply (s.pair_mem_conditionOrder _ _).1
    rw [value, value]
    exact (steps n).2.2.2.2.2.1
  · intro n
    rw [value]
    exact SetMembers.raw_mem _
  · intro n
    obtain ⟨a, ha, decision⟩ := (steps n).2.2.2.2.2.2
    refine ⟨a, ha, ?_⟩
    rw [value]
    rw [clock] at decision
    exact decision

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem pair_mem_decisionValues (U D p n a : ZFSet.{u}) :
    ZFSet.pair n a ∈ decisionValues U D p ↔
      n ∈ ZFSet.omega ∧ a ∈ U ∧ ZFSet.pair (ZFSet.pair p n) a ∈ D := by
  rw [decisionValues, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, m, hm, b, hb, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hm, hb, entry⟩
  · rintro ⟨hn, ha, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hn, ha⟩, n, hn, a, ha, rfl, entry⟩

theorem mem_commonDecisionConditions (P U D p : ZFSet.{u}) :
    p ∈ commonDecisionConditions P U D ↔
      p ∈ P ∧ ∀ n ∈ ZFSet.omega, ∃ a ∈ U, ZFSet.pair (ZFSet.pair p n) a ∈ D :=
  ZFSet.mem_sep

theorem mem_decisionDenseCode (P r U D base p : ZFSet.{u}) :
    p ∈ decisionDenseCode P r U D base ↔
      p ∈ P ∧ ((ZFSet.pair p base ∈ r ∧ p ∈ commonDecisionConditions P U D) ∨
        ¬ ∃ q ∈ P, ZFSet.pair q p ∈ r ∧ ZFSet.pair q base ∈ r) :=
  ZFSet.mem_sep

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem decisionValues_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {U D p : ZFSet.{u}} (hU : U ∈ M.sets) (hD : D ∈ M.sets) (hp : p ∈ M.sets) :
    decisionValues U D p ∈ M.sets := by
  let formula : BoundedFormula 5 := BoundedFormula.exMem 1 (BoundedFormula.exMem 3
    (.conj (BoundedFormula.orderedPairFormula 2 1 0)
      (BoundedFormula.tripleMembershipFormula 6 1 0 5)))
  let params := extend ZFSet.omega (extend U (extend D (extend p Fin.elim0)))
  have hw := M.omega_mem separation infinite
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hw (Fin.cases hU (Fin.cases hD (Fin.cases hp (fun j => Fin.elim0 j))))
  have ground := M.bounded_separation_mem separation formula params members
    (M.prod_mem pairing unions powers separation hw hU)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth formula (extend z params))
      (ZFSet.prod ZFSet.omega U) = decisionValues U D p := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep, decisionValues, formula, BoundedFormula.truth_exMem,
      BoundedFormula.Truth, BoundedFormula.truth_orderedPairFormula,
      BoundedFormula.truth_tripleMembershipFormula]
    rfl
  exact equal ▸ ground

theorem commonDecisionConditions_mem
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P U D : ZFSet.{u}} (hP : P ∈ M.sets) (hU : U ∈ M.sets) (hD : D ∈ M.sets) :
    commonDecisionConditions P U D ∈ M.sets := by
  let formula : BoundedFormula 4 := .allMem 1 (BoundedFormula.exMem 3
    (BoundedFormula.tripleMembershipFormula 2 1 0 5))
  let params := extend ZFSet.omega (extend U (extend D Fin.elim0))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases (M.omega_mem separation infinite) (Fin.cases hU (Fin.cases hD (fun j => Fin.elim0 j)))
  have ground := M.bounded_separation_mem separation formula params members hP
  have equal : ZFSet.sep (fun p => BoundedFormula.Truth formula (extend p params)) P =
      commonDecisionConditions P U D := by
    apply ZFSet.ext
    intro p
    simp only [ZFSet.mem_sep, commonDecisionConditions, formula, BoundedFormula.Truth,
      BoundedFormula.truth_exMem, BoundedFormula.truth_tripleMembershipFormula]
    rfl
  exact equal ▸ ground

theorem decisionDenseCode_mem
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P r U D base : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hU : U ∈ M.sets) (hD : D ∈ M.sets) (hbase : base ∈ M.sets) :
    decisionDenseCode P r U D base ∈ M.sets := by
  let formula : BoundedFormula 5 := BoundedFormula.disj
    (.conj (BoundedFormula.pairMembershipFormula 0 3 2) (.mem 0 4))
    (.neg (BoundedFormula.exMem 1 (.conj (BoundedFormula.pairMembershipFormula 0 1 3)
      (BoundedFormula.pairMembershipFormula 0 4 3))))
  let common := commonDecisionConditions P U D
  let params := extend P (extend r (extend base (extend common Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hP (Fin.cases hr (Fin.cases hbase
      (Fin.cases (M.commonDecisionConditions_mem separation infinite hP hU hD) (fun j => Fin.elim0 j))))
  have ground := M.bounded_separation_mem separation formula params members hP
  have equal : ZFSet.sep (fun p => BoundedFormula.Truth formula (extend p params)) P =
      decisionDenseCode P r U D base := by
    apply ZFSet.ext
    intro p
    simp only [ZFSet.mem_sep, decisionDenseCode, formula, BoundedFormula.truth_disj,
      BoundedFormula.Truth, BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ ground

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem internally_commonDecisions_denseBelow
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {U D : ZFSet.{u}} (hU : U ∈ M.sets) (hD : D ∈ M.sets)
    (closed : InternallyCountablyClosed M s) (base : P)
    (persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (dense : ∀ n ∈ ZFSet.omega, DenseBelow base
      {q | ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D}) :
    DenseBelow base {q | q ≤ base ∧ ∀ n ∈ ZFSet.omega,
      ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D} := by
  intro p below
  let S := attachmentIdeal s.carrier s.conditionOrder (s.encode base)
  have hS : S ∈ M.sets := M.attachmentIdeal_mem separation carrier order
    (M.transitive carrier (s.encode_mem base))
  have subset : S ⊆ s.carrier := fun _ h => (ZFSet.mem_sep.1 h).1
  have cone (q : P) : s.encode q ∈ S ↔ q ≤ base := by
    rw [mem_attachmentIdeal, s.pair_mem_conditionOrder]
    exact ⟨And.right, fun h => ⟨s.encode_mem q, h⟩⟩
  obtain ⟨seq, initial, graph, decreasing, _, decisions⟩ :=
    M.exists_groundDecisionChain s pairing unions powers separation infinite choice order
      hS hU hD subset p ((cone p).2 below) (fun n q hq => by
        obtain ⟨r, stronger, a, ha, decided⟩ := dense (natSetCode n) (natSetCode_mem_omega n)
          q ((cone q).1 hq)
        exact ⟨r, stronger, (cone r).2 (stronger.trans ((cone q).1 hq)), a, ha, decided⟩)
  obtain ⟨q, lower⟩ := closed seq graph decreasing
  have stronger : q ≤ p := initial ▸ lower 0
  refine ⟨q, stronger, stronger.trans below, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨a, ha, decided⟩ := decisions k
  exact ⟨a, ha, persistent _ q (lower (k + 1)) _ (natSetCode_mem_omega k) a ha decided⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u
variable {P : Type u} [Preorder P] (s : Presentation P)

theorem decisionDenseCode_eq (U D : ZFSet.{u}) (base : P) :
    s.subset (Localized base {q | q ≤ base ∧ ∀ n ∈ ZFSet.omega,
      ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D}) =
      decisionDenseCode s.carrier s.conditionOrder U D (s.encode base) := by
  have compatible (p : P) :
      (∃ q ∈ s.carrier, ZFSet.pair q (s.encode p) ∈ s.conditionOrder ∧
        ZFSet.pair q (s.encode base) ∈ s.conditionOrder) ↔ Compatible p base := by
    constructor
    · rintro ⟨q, hq, below, belowBase⟩
      obtain ⟨q, rfl⟩ := (s.mem_carrier q).1 hq
      exact ⟨q, (s.pair_mem_conditionOrder _ _).1 below,
        (s.pair_mem_conditionOrder _ _).1 belowBase⟩
    · rintro ⟨q, below, belowBase⟩
      exact ⟨s.encode q, s.encode_mem q, (s.pair_mem_conditionOrder _ _).2 below,
        (s.pair_mem_conditionOrder _ _).2 belowBase⟩
  have each (p : P) :
      s.encode p ∈ decisionDenseCode s.carrier s.conditionOrder U D (s.encode base) ↔
        p ∈ Localized base {q | q ≤ base ∧ ∀ n ∈ ZFSet.omega,
          ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D} := by
    simp only [mem_decisionDenseCode, mem_commonDecisionConditions,
      s.pair_mem_conditionOrder, s.encode_mem, true_and, compatible, Localized, Set.mem_ofPred_eq]
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, hp, rfl⟩ := (s.mem_subset _ z).1 hz
    exact (each p).2 hp
  · intro hz
    have bound := (mem_decisionDenseCode _ _ _ _ _ z).1 hz
    obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 bound.1
    exact (s.encode_mem_subset _ p).2 ((each p).1 hz)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem generic_common_decisions
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {U D : ZFSet.{u}} (hU : U ∈ M.sets) (hD : D ∈ M.sets)
    (closed : InternallyCountablyClosed M s) (base : P)
    (persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (dense : ∀ n ∈ ZFSet.omega, DenseBelow base
      {q | ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D})
    (H : ConditionFilter P) (generic : H.GenericFor (M.codedFamily s)) (hbase : H.mem base) :
    ∃ q, H.mem q ∧ q ≤ base ∧ ∀ n ∈ ZFSet.omega,
      ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D := by
  have density := M.internally_commonDecisions_denseBelow s pairing unions powers separation infinite choice
    carrier order hU hD closed base persistent dense
  have code := M.decisionDenseCode_mem separation infinite carrier order hU hD
    (M.transitive carrier (s.encode_mem base))
  rw [← decisionDenseCode_eq s U D base] at code
  exact H.meets_below generic hbase (M.codedFamily_of_code s code) density

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

variable {P : Type u} [Preorder P] (s : Presentation P)

theorem decisionValues_eq_reading {U D f : ZFSet.{u}} (base : P)
    (persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (unique : ∀ p : P, p ≤ base → ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ∀ b ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode p) n) b ∈ D → a = b)
    (H : ConditionFilter P) {q : P} (hq : H.mem q) (below : q ≤ base)
    (total : ∀ n ∈ ZFSet.omega, ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (function : ZFSet.IsFunc ZFSet.omega U f)
    (realizes : ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ZFSet.pair n a ∈ f →
      ∃ p, H.mem p ∧ ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D) :
    decisionValues U D (s.encode q) = f := by
  have agree (p : P) (hp : H.mem p) (n : ZFSet.{u}) (hn : n ∈ ZFSet.omega)
      (a b : ZFSet.{u}) (ha : a ∈ U) (hb : b ∈ U)
      (first : ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
      (second : ZFSet.pair (ZFSet.pair (s.encode p) n) b ∈ D) : a = b := by
    obtain ⟨r, _, rq, rp⟩ := H.directed hq hp
    exact unique r (rq.trans below) n hn a ha b hb
      (persistent q r rq n hn a ha first) (persistent p r rp n hn b hb second)
  have same (n : ZFSet.{u}) (hn : n ∈ ZFSet.omega) (a : ZFSet.{u}) (ha : a ∈ U) :
      ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D ↔ ZFSet.pair n a ∈ f := by
    constructor
    · intro decision
      obtain ⟨b, entry, _⟩ := function.2 n hn
      have hb := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
      obtain ⟨p, hp, read⟩ := realizes n hn b hb entry
      exact (agree p hp n hn a b ha hb decision read).symm ▸ entry
    · intro entry
      obtain ⟨b, hb, decision⟩ := total n hn
      obtain ⟨p, hp, read⟩ := realizes n hn a ha entry
      exact agree p hp n hn b a hb ha decision read ▸ decision
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨n, hn, a, ha, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    exact (same n hn a ha).1 ((pair_mem_decisionValues _ _ _ _ _).1 hz).2.2
  · intro hz
    obtain ⟨n, hn, a, ha, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    exact (pair_mem_decisionValues _ _ _ _ _).2 ⟨hn, ha, (same n hn a ha).2 hz⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem generic_decision_reading_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {U D : ZFSet.{u}} (hU : U ∈ M.sets) (hD : D ∈ M.sets)
    (closed : InternallyCountablyClosed M s) (base : P)
    (persistent : ∀ p q : P, q ≤ p → ∀ n ∈ ZFSet.omega, ∀ a ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D)
    (unique : ∀ p : P, p ≤ base → ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ∀ b ∈ U,
      ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D →
        ZFSet.pair (ZFSet.pair (s.encode p) n) b ∈ D → a = b)
    (dense : ∀ n ∈ ZFSet.omega, DenseBelow base
      {q | ∃ a ∈ U, ZFSet.pair (ZFSet.pair (s.encode q) n) a ∈ D})
    (H : ConditionFilter P) (generic : H.GenericFor (M.codedFamily s)) (hbase : H.mem base)
    {f : ZFSet.{u}} (function : ZFSet.IsFunc ZFSet.omega U f)
    (realizes : ∀ n ∈ ZFSet.omega, ∀ a ∈ U, ZFSet.pair n a ∈ f →
      ∃ p, H.mem p ∧ ZFSet.pair (ZFSet.pair (s.encode p) n) a ∈ D) :
    f ∈ M.sets ∧ ∃ q, H.mem q ∧ q ≤ base ∧ decisionValues U D (s.encode q) = f := by
  obtain ⟨q, hq, below, total⟩ := M.generic_common_decisions s pairing unions powers separation
    infinite choice carrier order hU hD closed base persistent dense H generic hbase
  have equal := decisionValues_eq_reading s base persistent unique H hq below total function realizes
  exact ⟨equal ▸ M.decisionValues_mem pairing unions powers separation infinite hU hD
    (M.transitive carrier (s.encode_mem q)), q, hq, below, equal⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection infinite choice carrier order in
theorem sequence_value_ground (small : M.sets.Countable)
    {U : ZFSet.{u}} (hU : U ∈ M.sets) (closed : InternallyCountablyClosed M s)
    (τ : (M.nameDomain s).names) (H : ConditionFilter P)
    (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    {base : P} (hbase : H.mem base)
    (forced : Forces (M.nameDomain s) (BoundedFormula.functionFormula 0 1 2).toFormula
      (M.sequenceFunctionNameEnv s pairing unions powers separation collection carrier
        (M.omega_mem separation infinite) hU τ) base) :
    Name.eval {q | H.mem q} τ.val ∈ M.sets ∧
      ∃ q, H.mem q ∧ q ≤ base ∧ decisionValues U
        (Name.sequenceDecisionRelation s ⊤ τ.val ZFSet.omega U) (s.encode q) =
          Name.eval {q | H.mem q} τ.val := by
  have hN := M.omega_mem separation infinite
  have hD := M.sequenceDecisionRelation_mem s ⊤ pairing unions powers separation collection
    carrier order τ hN hU
  have function := M.sequenceFunction_eval s pairing unions powers separation collection carrier
    hN hU τ H genericFormula hbase forced
  refine M.generic_decision_reading_ground s pairing unions powers separation infinite choice
    carrier order hU hD closed base ?_ ?_ ?_ H genericCoded hbase function ?_
  · intro p q before n hn a ha entry
    have decision := (Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U p n a).1 entry
    exact (Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U q n a).2
      ⟨hn, ha, Name.sequenceDecision_mono s ⊤ τ.val before decision.2.2⟩
  · intro p before n hn a ha b hb first second
    exact M.sequenceDecision_unique_below s pairing unions powers separation collection carrier
      small hN hU τ forced before hn ha hb
      ((Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U p n a).1 first).2.2
      ((Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U p n b).1 second).2.2
  · intro n hn q before
    obtain ⟨r, rq, a, ha, decision⟩ := M.sequenceDecision_dense_below s pairing unions powers
      separation collection carrier small hN hU τ forced hn q before
    exact ⟨r, rq, a, ha,
      (Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U r n a).2 ⟨hn, ha, decision⟩⟩
  · intro n hn a ha entry
    obtain ⟨p, hp, decision⟩ := (M.sequenceDecision_reading s pairing unions powers separation
      collection carrier τ n a (M.transitive hN hn) (M.transitive hU ha) H genericFormula).1 entry
    exact ⟨p, hp,
      (Name.sequenceDecisionRelation_entry s ⊤ τ.val ZFSet.omega U p n a).2 ⟨hn, ha, decision⟩⟩

include pairing unions powers separation collection infinite choice carrier order in
theorem sequence_value_ground_of_function (small : M.sets.Countable)
    {U : ZFSet.{u}} (hU : U ∈ M.sets) (closed : InternallyCountablyClosed M s)
    (τ : (M.nameDomain s).names) (H : ConditionFilter P)
    (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    (function : ZFSet.IsFunc ZFSet.omega U (Name.eval {q | H.mem q} τ.val)) :
    Name.eval {q | H.mem q} τ.val ∈ M.sets ∧
      ∃ q, H.mem q ∧ decisionValues U
        (Name.sequenceDecisionRelation s ⊤ τ.val ZFSet.omega U) (s.encode q) =
          Name.eval {q | H.mem q} τ.val := by
  obtain ⟨base, hbase, forced⟩ := M.exists_sequenceFunction_forcing s pairing unions powers
    separation collection carrier (M.omega_mem separation infinite) hU τ H genericFormula function
  obtain ⟨ground, q, hq, _, equal⟩ := M.sequence_value_ground s pairing unions powers separation
    collection infinite choice carrier order small hU closed τ H genericCoded genericFormula hbase forced
  exact ⟨ground, q, hq, equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRenamedNameFamilyBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (d : PosetAction G L) (base : L)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T : ZFSet.{u}) (H : ConditionFilter P)

theorem encode_mem_visibleSupportProfile (z : ZFSet.{u}) (v : L) :
    b.encode v ∈ M.visibleSupportProfile a s b d T H z ↔
      z ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) :=
  b.encode_mem_subset _ v

theorem visibleSupportProfile_upward (z : ZFSet.{u}) {v w : L} (lower : v ≤ w)
    (member : b.encode v ∈ M.visibleSupportProfile a s b d T H z) :
    b.encode w ∈ M.visibleSupportProfile a s b d T H z := by
  have seen := (M.encode_mem_visibleSupportProfile a s b d T H z v).1 member
  obtain ⟨τ, candidate, equal⟩ :=
    (M.mem_eval_niceVisibilityName a s T (d.principalFix v) _ H.top_mem z).1 seen
  have data := (M.name_mem_niceNameCandidates a s T (d.principalFix v) τ).1 candidate
  apply (M.encode_mem_visibleSupportProfile a s b d T H z w).2
  apply (M.mem_eval_niceVisibilityName a s T (d.principalFix w) _ H.top_mem z).2
  exact ⟨τ, (M.name_mem_niceNameCandidates a s T (d.principalFix w) τ).2
    ⟨data.1, data.2.1, le_trans (d.principalFix_antitone lower) data.2.2⟩, equal⟩

variable (valid : ∀ z ∈ T, IsName s z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
variable (z : (M.nameDomain s).names)
variable (hs : HereditarilySymmetric a s (d.principalSupportFamily base directed) z.val)
variable (subset : Name.eval {p | H.mem p} z.val ⊆
  Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))

include system generic hs subset in
theorem visibleSupportProfile_nonempty :
    (M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)).Nonempty := by
  obtain ⟨v, support⟩ := hs.symmetric
  exact ⟨b.encode v, (M.encode_mem_visibleSupportProfile a s b d T H _ v).2
    (system.normalization_visible v z support H generic subset)⟩

variable (meet : L → L → L)
variable (descent : ∀ (v w : L) (x y : (M.nameDomain s).names),
  d.principalFix v ≤ a.stabilizer s x.val →
  d.principalFix w ≤ a.stabilizer s y.val →
  HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
  HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
  Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
  ∃ τ : (M.nameDomain s).names,
    HereditarilySymmetric a s (d.principalSupportFamily base directed) τ.val ∧
    d.principalFix (meet v w) ≤ a.stabilizer s τ.val ∧
    Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)

include system generic subset descent in
theorem visibleSupportProfile_meet (v w : L)
    (left : b.encode v ∈ M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val))
    (right : b.encode w ∈ M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)) :
    b.encode (meet v w) ∈ M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) := by
  obtain ⟨x, hx, ex⟩ := (M.mem_eval_niceVisibilityName a s T (d.principalFix v) _ H.top_mem _).1
    ((M.encode_mem_visibleSupportProfile a s b d T H _ v).1 left)
  obtain ⟨y, hy, ey⟩ := (M.mem_eval_niceVisibilityName a s T (d.principalFix w) _ H.top_mem _).1
    ((M.encode_mem_visibleSupportProfile a s b d T H _ w).1 right)
  have dx := (M.name_mem_niceNameCandidates a s T (d.principalFix v) x).1 hx
  have dy := (M.name_mem_niceNameCandidates a s T (d.principalFix w) y).1 hy
  obtain ⟨τ, _, fixed, equal⟩ := descent v w ⟨x, dx.1⟩ ⟨y, dy.1⟩ dx.2.2 dy.2.2
    (system.candidate_hs v x hx) (system.candidate_hs w y hy) (ex.trans ey.symm)
  have target : Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} z.val := equal.trans ex
  have bounded : Name.eval {p | H.mem p} τ.val ⊆
      Name.eval {p | H.mem p} (Name.familySet ⊤ T valid) := target.symm ▸ subset
  apply (M.encode_mem_visibleSupportProfile a s b d T H _ (meet v w)).2
  exact target ▸ system.normalization_visible (meet v w) τ fixed H generic bounded

include system generic hs subset descent in
theorem visibleSupportProfile_filter :
    MeetFilterCode b.carrier b.conditionOrder ((b.product b).graph b (fun vw => meet vw.1 vw.2))
      (M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)) := by
  refine ⟨b.subset_carrier _, M.visibleSupportProfile_nonempty a s b d base directed T H
    valid system generic z hs subset, ?_, ?_⟩
  · intro x hx y hy lower
    obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (b.subset_carrier _ hx)
    obtain ⟨w, rfl⟩ := (b.mem_carrier y).1 hy
    exact M.visibleSupportProfile_upward a s b d T H _ ((b.pair_mem_conditionOrder v w).1 lower) hx
  · intro x hx y hy out entry
    obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (b.subset_carrier _ hx)
    obtain ⟨w, rfl⟩ := (b.mem_carrier y).1 (b.subset_carrier _ hy)
    have outCarrier := (ZFSet.pair_mem_prod.1
      (((b.product b).graph_isFunc b (fun vw => meet vw.1 vw.2)).1 entry)).2
    obtain ⟨k, rfl⟩ := (b.mem_carrier out).1 outCarrier
    have equal := ((b.product b).pair_mem_graph b (fun vw => meet vw.1 vw.2) (v, w) k).1 entry
    exact equal ▸ M.visibleSupportProfile_meet a s b d base directed T H valid system generic z
      subset meet descent v w hx hy

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_VisibilityProfileFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_supportedEqualitySequenceFormula (env : Fin 6 → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets supportedEqualitySequenceFormula env ↔
      ZFSet.IsFunc (env 0) (env 1) (env 2) ∧
      ∀ v ∈ env 0, ∀ tau ∈ env 1, ZFSet.pair v tau ∈ env 2 →
        ZFSet.pair v tau ∈ env 3 ∧ ZFSet.pair tau (env 5) ∈ env 4 := by
  have function := (BoundedFormula.realize_toFormula M
    (BoundedFormula.functionFormula 0 1 2) env members).trans
      (BoundedFormula.truth_functionFormula 0 1 2 env)
  constructor
  · intro realized
    refine ⟨function.1 realized.1, ?_⟩
    intro v hv tau ht entry
    have hvM := M.transitive (members 0) hv
    have htM := M.transitive (members 1) ht
    have atNode := (realize_imp M.sets _ _ _).1 (realized.2 v hvM) hv
    have atCode := (realize_imp M.sets _ _ _).1 (atNode tau htM) ht
    have result := (realize_imp M.sets _ _ _).1 atCode
      ((M.realize_stageOnePairLookup 1 0 4 _ (Fin.cases htM (Fin.cases hvM members))).2 entry)
    exact ⟨(M.realize_stageOnePairLookup 1 0 5 _ (Fin.cases htM (Fin.cases hvM members))).1 result.1,
      (M.realize_stageOnePairLookup 0 7 6 _ (Fin.cases htM (Fin.cases hvM members))).1 result.2⟩
  · rintro ⟨isFunction, meaning⟩
    refine ⟨function.2 isFunction, ?_⟩
    intro v hvM
    apply (realize_imp M.sets _ _ _).2
    intro hv tau htM
    apply (realize_imp M.sets _ _ _).2
    intro ht
    apply (realize_imp M.sets _ _ _).2
    intro entry
    have result := meaning v hv tau ht
      ((M.realize_stageOnePairLookup 1 0 4 _ (Fin.cases htM (Fin.cases hvM members))).1 entry)
    exact ⟨(M.realize_stageOnePairLookup 1 0 5 _ (Fin.cases htM (Fin.cases hvM members))).2 result.1,
      (M.realize_stageOnePairLookup 0 7 6 _ (Fin.cases htM (Fin.cases hvM members))).2 result.2⟩

end TransitiveGround

namespace TransitiveGround
variable (N : TransitiveGround.{u})

theorem realize_visibilityProfileFormula (env : Fin 4 → ZFSet.{u})
    (members : ∀ i, env i ∈ N.sets) :
    Realize N.sets visibilityProfileFormula env ↔
      ∀ v ∈ env 2, ∀ V ∈ N.sets, ZFSet.pair v V ∈ env 1 → (env 0 ∈ V ↔ v ∈ env 3) := by
  constructor
  · intro realized v hv V hV entry
    have hvN := N.transitive (members 2) hv
    have atNode := (realize_imp N.sets _ _ _).1 (realized v hvN) hv
    have atValue := (realize_imp N.sets _ _ _).1 (atNode V hV)
      ((N.realize_stageOnePairLookup 1 0 3 _ (Fin.cases hV (Fin.cases hvN members))).2 entry)
    exact ⟨(realize_imp N.sets _ _ _).1 atValue.1,
      (realize_imp N.sets _ _ _).1 atValue.2⟩
  · intro meaning v hvN
    apply (realize_imp N.sets _ _ _).2
    intro hv V hV
    apply (realize_imp N.sets _ _ _).2
    intro entry
    have exactProfile := meaning v hv V hV
      ((N.realize_stageOnePairLookup 1 0 3 _ (Fin.cases hV (Fin.cases hvN members))).1 entry)
    exact ⟨(realize_imp N.sets _ _ _).2 exactProfile.1,
      (realize_imp N.sets _ _ _).2 exactProfile.2⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPreparationForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)

theorem niceVisibilityEvaluationName_entry (T : ZFSet.{u}) (K : I → Subgroup G)
    (H : ConditionFilter P) (v : I) (V : ZFSet.{u}) :
    ZFSet.pair (b.encode v) V ∈ Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K) ↔
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v)) = V := by
  let i : b.carrier.toSet := ⟨b.encode v, b.encode_mem v⟩
  have equal := (M.niceVisibilityGraph_function a s b T K).value_eq_of_entry i
    ((M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl)
  have names : (⟨(M.niceVisibilityGraph_function a s b T K).value i,
      visibilityValues_isName M a s b T K i⟩ : Name s) = M.niceVisibilityName a s T (K v) :=
    Subtype.ext equal
  exact (Name.pair_mem_eval_indexedGraphName {p | H.mem p} ⊤ H.top_mem
    (M.niceVisibilityGraph_function a s b T K) (visibilityValues_isName M a s b T K) i V).trans
    (by rw [names])

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)
variable (K : I → Subgroup G)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

theorem realize_visibilityProfileEnv (F : ZFSet.{u}) (hF : F ∈ M.sets)
    (z : (M.nameDomain s).names) (H : ConditionFilter P) :
    Realize ((M.nameDomain s).values {p | H.mem p}) visibilityProfileFormula
      (evalAssignment {p | H.mem p}
        (M.visibilityProfileEnv a s t b K pairing unions powers separation collection carrier group nodes supports maps hT valid F hF z)) ↔
      ∀ v : I, Name.eval {p | H.mem p} z.val ∈
        Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v)) ↔ b.encode v ∈ F := by
  let env := M.visibilityProfileEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid F hF z
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {p | H.mem p},
    (M.nameDomain s).values_transitive _⟩
  have fields : evalAssignment {p | H.mem p} env =
      ![Name.eval {p | H.mem p} z.val,
        Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K), b.carrier, F] := by
    funext i
    refine Fin.cases rfl (Fin.cases rfl (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))) i
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
  have meaning := N.realize_visibilityProfileFormula (evalAssignment {p | H.mem p} env)
    (fun i => ⟨env i, rfl⟩)
  rw [fields] at meaning
  change Realize N.sets visibilityProfileFormula (evalAssignment {p | H.mem p} env) ↔ _
  rw [fields, meaning]
  constructor
  · intro allNodes v
    have visibilityGround := M.niceVisibilityName_mem a s t b K pairing unions powers separation collection
      carrier group supports maps hT valid v (M.transitive nodes (b.encode_mem v))
    exact allNodes (b.encode v) (b.encode_mem v) _ ⟨⟨_, visibilityGround⟩, rfl⟩
      ((M.niceVisibilityEvaluationName_entry a s b T K H v _).2 rfl)
  · intro typed code hcode V hV entry
    obtain ⟨v, rfl⟩ := (b.mem_carrier code).1 hcode
    have equal := (M.niceVisibilityEvaluationName_entry a s b T K H v V).1 entry
    exact equal ▸ typed v

theorem forces_visibilityProfile_iff (small : M.sets.Countable)
    (F : ZFSet.{u}) (hF : F ∈ M.sets) (z : (M.nameDomain s).names) (p : P) :
    Forces (M.nameDomain s) visibilityProfileFormula
      (M.visibilityProfileEnv a s t b K pairing unions powers separation collection carrier group nodes supports maps hT valid F hF z) p ↔
      M.DecidesVisibilityProfile a s b K T F z.val p := by
  let env := M.visibilityProfileEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid F hF z
  let vis (v : I) : (M.nameDomain s).names := ⟨M.niceVisibilityName a s T (K v),
    M.niceVisibilityName_mem a s t b K pairing unions powers separation collection
      carrier group supports maps hT valid v (M.transitive nodes (b.encode_mem v))⟩
  have global := M.ordinaryForces_iff_all_generics s small carrier visibilityProfileFormula env p
  constructor
  · intro forced v
    have profile (H : ConditionFilter P) (hp : H.mem p)
        (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :=
      (M.realize_visibilityProfileEnv a s t b K pairing unions powers separation collection
        carrier group nodes supports maps hT valid F hF z H).1 (global.1 forced H hp generic) v
    constructor
    · intro yes
      apply (M.ordinaryForces_iff_all_generics s small carrier (.mem 0 1) ![z, vis v] p).2
      intro H hp generic
      exact (profile H hp generic).2 yes
    · intro no
      change Forces (M.nameDomain s) (.neg (.mem 0 1)) ![z, vis v] p
      apply (M.ordinaryForces_iff_all_generics s small carrier (.neg (.mem 0 1)) ![z, vis v] p).2
      intro H hp generic member
      exact no ((profile H hp generic).1 member)
  · intro decisions
    apply global.2
    intro H hp generic
    apply (M.realize_visibilityProfileEnv a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid F hF z H).2
    intro v
    by_cases member : b.encode v ∈ F
    · have atom : Forces (M.nameDomain s) (.mem 0 1 : SetFormula 2) ![z, vis v] p := by
        exact (decisions v).1 member
      have positive := forces_sound (M.nameDomain s) H generic (.mem 0 1 : SetFormula 2) ![z, vis v] hp atom
      exact ⟨fun _ => member, fun _ => positive⟩
    · have atom : Forces (M.nameDomain s) (.neg (.mem 0 1) : SetFormula 2) ![z, vis v] p := by
        exact (decisions v).2 member
      have negative := forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1) : SetFormula 2) ![z, vis v] hp atom
      exact ⟨fun yes => False.elim (negative yes), fun yes => False.elim (member yes)⟩

end PartitionPilot.Forcing.TransitiveGround




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

theorem ground_subset_ordinaryExtension [OrderTop P]
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    M.sets ⊆ (M.ordinaryExtension s H).sets := by
  intro x hx
  exact (M.mem_ordinaryExtension s H x).2 ⟨Name.check s ⊤ x,
    M.check_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) x hx,
    Name.eval_check {q | H.mem q} ⊤ H.top_mem x⟩

end TransitiveGround

section
open SetFormula
universe u

namespace GroundSequenceReflection
variable {M N : TransitiveGround.{u}} {P : ZFSet.{u}}
variable (reflection : GroundSequenceReflection M N P)
include reflection

theorem enumeration
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    {X : ZFSet.{u}} (hX : X ∈ N.sets) (subset : X ⊆ P) (nonempty : X.Nonempty)
    (small : N.groundEmbeddable X ZFSet.omega) :
    ∃ f ∈ M.sets, f ∈ N.sets ∧ ZFSet.IsFunc ZFSet.omega X f ∧
      ZFSet.IsFunc ZFSet.omega P f ∧ relationImage ZFSet.omega P f = X := by
  obtain ⟨f, hf, function, onto⟩ :=
    N.groundCountable_enumeration pairingN unionsN powersN separationN infiniteN hX nonempty small
  have enlarged : ZFSet.IsFunc ZFSet.omega P f := by
    refine ⟨?_, function.2⟩
    intro z hz
    obtain ⟨n, hn, x, hx, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hn, subset hx⟩
  refine ⟨f, reflection f hf enlarged, hf, function, enlarged, ?_⟩
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨_, n, _, entry⟩ := (mem_relationImage _ _ _ x).1 hx
    exact (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  · intro hx
    obtain ⟨n, hn, entry⟩ := onto x hx
    exact (mem_relationImage _ _ _ x).2 ⟨subset hx, n, hn, entry⟩

theorem countable_subset
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (hP : P ∈ M.sets) {X : ZFSet.{u}} (hX : X ∈ N.sets) (subset : X ⊆ P)
    (small : N.groundEmbeddable X ZFSet.omega) :
    X ∈ M.sets ∧ M.groundEmbeddable X ZFSet.omega := by
  classical
  by_cases nonempty : X.Nonempty
  · obtain ⟨f, hf, _, _, function, range_eq⟩ :=
      reflection.enumeration pairingN unionsN powersN separationN infiniteN hX subset nonempty small
    have hOmega := M.omega_mem separation infinite
    have omegaSmall : M.groundEmbeddable ZFSet.omega ZFSet.omega :=
      ⟨identityFunctionGraph ZFSet.omega,
        M.identityFunctionGraph_mem pairing unions powers separation hOmega,
        identityFunctionGraph_injection ZFSet.omega⟩
    have rangeGround := M.relationImage_mem separation hOmega hP hf
    have rangeSmall := M.groundEmbeddable_function_image pairing unions powers separation choice
      hOmega hP hOmega hf function omegaSmall
    rw [range_eq] at rangeGround rangeSmall
    exact ⟨rangeGround, rangeSmall⟩
  · have empty : X = ∅ := by
      apply ZFSet.ext
      intro x
      exact ⟨fun hx => False.elim (nonempty ⟨x, hx⟩),
        fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    rw [empty]
    exact ⟨M.empty_mem ⟨P, hP⟩, M.empty_groundEmbeddable ZFSet.omega ⟨P, hP⟩⟩

end GroundSequenceReflection

end

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include pairing unions powers separation collection carrier order in
theorem ordinary_ZF_of_conditionMaps {G : Type u} [Group G]
    (a : PosetAction G P) (t : Presentation G)
    (infinite : Realize M.sets infinity Fin.elim0)
    (group : t.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    ZFRealization (M.ordinaryExtension s H).sets := by
  have allGeneric : H.GenericFor
      (formulaFamily (a.symmetricDomain s (M.nameDomain s) (allSupportFamily G))) := by
    rw [a.symmetricDomain_allSupport]
    exact generic
  have checked := M.symmetric_ZF a s t (natInitialPresentation 1) (allSupportFamily G)
    (allSupportBasis G) (allSupportFamily_basis G) pairing unions powers separation collection infinite
    carrier order group (M.allSupportIndices_mem t pairing group)
    (M.allSupportBasisCode_mem t pairing group) maps H allGeneric
  rw [a.symmetricDomain_allSupport] at checked
  exact checked

include pairing unions powers separation collection carrier order in
theorem ordinaryExtension_ZF (infinite : Realize M.sets infinity Fin.elim0)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    ZFRealization (M.ordinaryExtension s H).sets :=
  M.ordinary_ZF_of_conditionMaps s pairing unions powers separation collection carrier order
    (identityPosetAction (Equiv.Perm (ULift.{u} Unit)) P) trivialGroupPresentation infinite
    (M.trivialGroupPresentation_mem pairing ⟨s.carrier, carrier⟩)
    (M.identityPosetAction_conditionMapFamily_mem s pairing unions powers separation carrier) H generic

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

include pairing unions powers separation collection carrier group nodes supports maps hT valid in
theorem visibleSupportProfile_mem_ordinary
    (order : s.conditionOrder ∈ M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (z : (M.nameDomain s).names) :
    M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∈
      (M.ordinaryExtension s H).sets := by
  let N := M.ordinaryExtension s H
  let graph := Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T d.principalFix)
  have hz : Name.eval {p | H.mem p} z.val ∈ N.sets := ⟨z, rfl⟩
  have hgraph : graph ∈ N.sets := ⟨⟨_, M.niceVisibilityEvaluationName_mem a s b t d.principalFix
    pairing unions powers separation collection carrier group nodes supports maps hT valid⟩, rfl⟩
  have hnodes : b.carrier ∈ N.sets := M.ground_subset_ordinaryExtension s pairing unions powers
    separation collection carrier H nodes
  have hvisibility (v : L) :
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) ∈ N.sets :=
    ⟨⟨_, M.niceVisibilityName_mem a s t b d.principalFix pairing unions powers separation collection
      carrier group supports maps hT valid v (M.transitive nodes (b.encode_mem v))⟩, rfl⟩
  let phi : SetFormula 3 := ex (.conj (BoundedFormula.pairMembershipFormula 1 0 3).toFormula (.mem 2 0))
  let params : Fin 2 → ZFSet.{u} := ![Name.eval {p | H.mem p} z.val, graph]
  have members : ∀ i, params i ∈ N.sets :=
    Fin.cases hz (Fin.cases hgraph (fun i => Fin.elim0 i))
  have meaning (v : L) : Realize N.sets phi (extend (b.encode v) params) ↔
      Name.eval {p | H.mem p} z.val ∈
        Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) := by
    rw [show phi = ex (.conj (BoundedFormula.pairMembershipFormula 1 0 3).toFormula (.mem 2 0)) from rfl,
      realize_ex]
    constructor
    · rintro ⟨V, hV, entry, member⟩
      have coded : ZFSet.pair (b.encode v) V ∈ graph :=
        (N.realize_stageOnePairLookup 1 0 3 _
          (Fin.cases hV (Fin.cases (N.transitive hnodes (b.encode_mem v)) members))).1 entry
      have equal := (M.niceVisibilityEvaluationName_entry a s b T d.principalFix H v V).1 coded
      exact equal.symm ▸ member
    · intro member
      refine ⟨_, hvisibility v, ?_, member⟩
      exact (N.realize_stageOnePairLookup 1 0 3 _
        (Fin.cases (hvisibility v) (Fin.cases (N.transitive hnodes (b.encode_mem v)) members))).2
        ((M.niceVisibilityEvaluationName_entry a s b T d.principalFix H v _).2 rfl)
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order infinite H generic
  have selected := N.separation_mem zf.2.1 phi params members hnodes
  have equal : ZFSet.sep (fun x => Realize N.sets phi (extend x params)) b.carrier =
      M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (ZFSet.mem_sep.1 hx).1
      exact (M.encode_mem_visibleSupportProfile a s b d T H _ v).2
        ((meaning v).1 (ZFSet.mem_sep.1 hx).2)
    · intro hx
      obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (b.subset_carrier _ hx)
      exact ZFSet.mem_sep.2 ⟨b.encode_mem v,
        (meaning v).2 ((M.encode_mem_visibleSupportProfile a s b d T H _ v).1 hx)⟩
  exact equal ▸ selected

include pairing unions powers separation collection carrier group nodes supports maps hT valid in
theorem exists_forced_visibleSupportProfile (small : M.sets.Countable)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (z : (M.nameDomain s).names)
    (ground : M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∈ M.sets)
    (p : P) (hp : H.mem p) :
    ∃ q, H.mem q ∧ q ≤ p ∧
      Forces (M.nameDomain s) visibilityProfileFormula
        (M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
          carrier group nodes supports maps hT valid
          (M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)) ground z) q ∧
      M.DecidesVisibilityProfile a s b d.principalFix T
        (M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)) z.val q := by
  let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
  let env := M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
    carrier group nodes supports maps hT valid F ground z
  have truth : Realize ((M.nameDomain s).values {p | H.mem p}) visibilityProfileFormula
      (evalAssignment {p | H.mem p} env) :=
    (M.realize_visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
      carrier group nodes supports maps hT valid F ground z H).2
      (fun v => (M.encode_mem_visibleSupportProfile a s b d T H _ v).symm)
  obtain ⟨r, hr, forced⟩ := (forcing_truth (M.nameDomain s) H generic visibilityProfileFormula env).1 truth
  obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
  have forcedQ := forces_mono (M.nameDomain s) visibilityProfileFormula env forced qr
  exact ⟨q, hq, qp, forcedQ,
    (M.forces_visibilityProfile_iff a s t b d.principalFix pairing unions powers separation collection
      carrier group nodes supports maps hT valid small F ground z q).1 forcedQ⟩

end TransitiveGround

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P]
variable (s : Presentation P)

theorem ordinaryExtension_sequenceReflection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) {U : ZFSet.{u}} (hU : U ∈ M.sets)
    (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter P) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s))) :
    GroundSequenceReflection M (M.ordinaryExtension s H) U := by
  intro f hf function
  obtain ⟨τ, hτ, rfl⟩ := (M.mem_ordinaryExtension s H f).1 hf
  exact (M.sequence_value_ground_of_function s pairing unions powers separation collection infinite choice
    carrier order small hU closed ⟨τ, hτ⟩ H genericCoded genericFormula function).1

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SupportedCertificateRelations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem pair_mem_supportedEqualityRelation (B N R E value v tau : ZFSet.{u}) :
    ZFSet.pair v tau ∈ supportedEqualityRelation B N R E value ↔
      v ∈ B ∧ tau ∈ N ∧ ZFSet.pair v tau ∈ R ∧ ZFSet.pair tau value ∈ E := by
  rw [supportedEqualityRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, w, hw, sigma, hsigma, equal, support, evaluated⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hw, hsigma, support, evaluated⟩
  · rintro ⟨hv, htau, support, evaluated⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, htau⟩, v, hv, tau, htau, rfl, support, evaluated⟩

namespace BoundedFormula

theorem truth_supportedEqualityEntryFormula {n} (entry B N R E value : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (supportedEqualityEntryFormula entry B N R E value) env ↔
      ∃ v ∈ env B, ∃ tau ∈ env N, env entry = ZFSet.pair v tau ∧
        ZFSet.pair v tau ∈ env R ∧ ZFSet.pair tau (env value) ∈ env E := by
  simp only [supportedEqualityEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem supportedEqualityRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {B N R E value : ZFSet.{u}} (hB : B ∈ M.sets) (hN : N ∈ M.sets)
    (hR : R ∈ M.sets) (hE : E ∈ M.sets) (hvalue : value ∈ M.sets) :
    supportedEqualityRelation B N R E value ∈ M.sets := by
  let params := extend B (extend N (extend R (extend E (extend value Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.supportedEqualityEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hB (Fin.cases hN (Fin.cases hR (Fin.cases hE (Fin.cases hvalue (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hB hN)
  have equal : ZFSet.sep (fun entry => BoundedFormula.Truth
      (BoundedFormula.supportedEqualityEntryFormula 0 1 2 3 4 5) (extend entry params))
      (ZFSet.prod B N) = supportedEqualityRelation B N R E value := by
    apply ZFSet.ext
    intro entry
    rw [ZFSet.mem_sep, supportedEqualityRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_supportedEqualityEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G) (H : ConditionFilter P)

theorem supportedEqualityRelation_entry (B value : ZFSet.{u}) (v : L) (tau : Name s) :
    ZFSet.pair (b.encode v) tau.val ∈ supportedEqualityRelation B
      (M.niceSupportNameCodes a s T K) (M.niceSupportRelation a s b T K)
      (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K)) value ↔
      b.encode v ∈ B ∧ tau.val ∈ M.sets ∧ NiceNameCode a s T (K v) tau.val ∧
        Name.eval {p | H.mem p} tau = value := by
  rw [pair_mem_supportedEqualityRelation]
  constructor
  · rintro ⟨hv, htau, support, evaluated⟩
    have code := (M.pair_mem_niceSupportRelation a s b T K v tau.val).1 support
    exact ⟨hv, code.1, code.2, (M.niceSupportEvaluationName_entry a s T K tau htau H value).1 evaluated⟩
  · rintro ⟨hv, ground, code, evaluated⟩
    have member := (M.mem_niceSupportNameCodes a s T K tau.val).2 ⟨ground, v, code⟩
    exact ⟨hv, member, (M.pair_mem_niceSupportRelation a s b T K v tau.val).2 ⟨ground, code⟩,
      (M.niceSupportEvaluationName_entry a s T K tau member H value).2 evaluated⟩

theorem supportedEqualityRelation_total {B value : ZFSet.{u}}
    (subset : B ⊆ b.carrier)
    (visible : ∀ v : L, b.encode v ∈ B → value ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v))) :
    ∀ v ∈ B, ∃ tau ∈ M.niceSupportNameCodes a s T K,
      ZFSet.pair v tau ∈ supportedEqualityRelation B
        (M.niceSupportNameCodes a s T K) (M.niceSupportRelation a s b T K)
        (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K)) value := by
  intro raw member
  obtain ⟨v, rfl⟩ := (b.mem_carrier raw).1 (subset member)
  obtain ⟨tau, candidate, evaluated⟩ :=
    (M.mem_eval_niceVisibilityName a s T (K v) _ H.top_mem value).1 (visible v member)
  have code := (M.mem_niceNameCandidates a s T (K v) tau.val).1 candidate
  exact ⟨tau.val, (M.mem_niceSupportNameCodes a s T K tau.val).2 ⟨code.1, v, code.2⟩,
    (M.supportedEqualityRelation_entry a s b T K H B value v tau).2
      ⟨member, code.1, code.2, evaluated⟩⟩

theorem supportedEqualityRelation_mem_ordinary (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {B : ZFSet.{u}} (hB : B ∈ M.sets) (z : (M.nameDomain s).names) :
    supportedEqualityRelation B (M.niceSupportNameCodes a s T K) (M.niceSupportRelation a s b T K)
      (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K))
      (Name.eval {p | H.mem p} z.val) ∈ (M.ordinaryExtension s H).sets := by
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order infinite H generic
  have nameGround := M.niceSupportEvaluationName_mem a s T K t b pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  exact (M.ordinaryExtension s H).supportedEqualityRelation_mem zf.1.2.2.2.1 zf.1.2.2.2.2.1
    zf.1.2.2.2.2.2.1 zf.2.1 (includes hB)
    (includes (M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation collection
      carrier group nodes supports maps hT valid))
    (includes (M.niceSupportRelation_mem a s b T K t pairing unions powers separation collection
      carrier group nodes supports maps hT valid))
    ⟨⟨_, nameGround⟩, rfl⟩ ⟨z, rfl⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

theorem pair_mem_supportedCertificateRelation
    (J PF PB WF nodes N order R inputEval niceEval visibilityEval j F B f : ZFSet.{u}) :
    ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∈
        supportedCertificateRelation J PF PB WF nodes N order R inputEval niceEval visibilityEval ↔
      j ∈ J ∧ F ∈ PF ∧ B ∈ PB ∧ f ∈ WF ∧
        ∃ value, ZFSet.pair j value ∈ inputEval ∧
          SupportedEqualityCertificate nodes N order R niceEval visibilityEval value F B f := by
  rw [supportedCertificateRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j', hj, F', hF, B', hB, f', hf, equal, value, evaluated, certificate⟩
    have outer := ZFSet.pair_inj.1 equal
    have middle := ZFSet.pair_inj.1 outer.2
    have inner := ZFSet.pair_inj.1 middle.2
    cases outer.1
    cases middle.1
    cases inner.1
    cases inner.2
    exact ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
  · rintro ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hj, ZFSet.pair_mem_prod.2
      ⟨hF, ZFSet.pair_mem_prod.2 ⟨hB, hf⟩⟩⟩,
      j, hj, F, hF, B, hB, f, hf, rfl, value, evaluated, certificate⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOrdinaryCountableFunctions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundSequenceReflection
open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {U : ZFSet.{u}}

theorem countable_domain_function (reflection : GroundSequenceReflection M N U)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (included : M.sets ⊆ N.sets) {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hU : U ∈ M.sets)
    (small : M.groundEmbeddable A ZFSet.omega)
    (hf : f ∈ N.sets) (function : ZFSet.IsFunc A U f) : f ∈ M.sets := by
  classical
  by_cases nonempty : A.Nonempty
  · obtain ⟨e, he, enumeration, onto⟩ := M.groundCountable_enumeration
      pairing unions powers separation infinite hA nonempty small
    have omega := M.omega_mem separation infinite
    let sequence := relationCompose ZFSet.omega A U e f
    have sequenceFunction : ZFSet.IsFunc ZFSet.omega U sequence :=
      relationCompose_function_of_subset enumeration function (fun _ member => member)
    have sequenceGround := reflection sequence
      (N.relationCompose_mem pairingN unionsN powersN separationN
        (included omega) (included hA) (included hU) (included he) hf) sequenceFunction
    have recovered : relationCompose A ZFSet.omega U
        (relationConverse ZFSet.omega A e) sequence = f := by
      apply ZFSet.ext
      intro z
      constructor
      · intro member
        obtain ⟨a, ha, n, hn, v, _, rfl, inverse, value⟩ :=
          (mem_relationCompose _ _ _ _ _ z).1 member
        have na := ((pair_mem_relationConverse ZFSet.omega A e n a).1 inverse).2.2
        obtain ⟨_, _, a', _, na', av⟩ := (pair_mem_relationCompose _ _ _ _ _ n v).1 value
        obtain ⟨x, _, unique⟩ := enumeration.2 n hn
        have equal : a' = a := (unique a' na').trans (unique a na).symm
        exact equal ▸ av
      · intro member
        obtain ⟨a, ha, v, hv, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
        obtain ⟨n, hn, entry⟩ := onto a ha
        exact (pair_mem_relationCompose _ _ _ _ _ a v).2
          ⟨ha, hv, n, hn, (pair_mem_relationConverse ZFSet.omega A e n a).2 ⟨hn, ha, entry⟩,
            (pair_mem_relationCompose _ _ _ _ _ n v).2 ⟨hn, hv, a, ha, entry, member⟩⟩
    rw [← recovered]
    exact M.relationCompose_mem pairing unions powers separation hA omega hU
      (M.relationConverse_mem pairing unions powers separation omega hA he) sequenceGround
  · have empty : f = ∅ := by
      apply ZFSet.ext
      intro z
      constructor
      · intro member
        obtain ⟨a, ha, _, _, _⟩ := ZFSet.mem_prod.1 (function.1 member)
        exact False.elim (nonempty ⟨a, ha⟩)
      · intro member
        exact False.elim (ZFSet.notMem_empty z member)
    rw [empty]
    exact M.empty_mem ⟨A, hA⟩

end PartitionPilot.Forcing.GroundSequenceReflection



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)

theorem ordinaryExtension_countableDomainFunction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) {A U : ZFSet.{u}} (hA : A ∈ M.sets) (hU : U ∈ M.sets)
    (domainSmall : M.groundEmbeddable A ZFSet.omega)
    (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter P) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    {f : ZFSet.{u}} (hf : f ∈ (M.ordinaryExtension s H).sets)
    (function : ZFSet.IsFunc A U f) : f ∈ M.sets := by
  have reflection := M.ordinaryExtension_sequenceReflection s pairing unions powers separation
    collection infinite choice carrier order small hU closed H genericCoded genericFormula
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  exact reflection.countable_domain_function pairing unions powers separation infinite
    zf.1.2.2.2.1 zf.1.2.2.2.2.1 zf.1.2.2.2.2.2.1 zf.2.1
    (M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H)
    hA hU domainSmall hf function

end PartitionPilot.Forcing.TransitiveGround

end

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
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem choice_of_witnesses
    (witnesses : ∀ A ∈ M.sets, (∀ x ∈ A, x.Nonempty) →
      ∃ f ∈ M.sets, ChoiceFunctionCode A f) :
    Realize M.sets SetFormula.choice Fin.elim0 := by
  intro A hA
  apply (realize_imp M.sets _ _ _).2
  intro premise
  have nonempty : ∀ x ∈ A, x.Nonempty := by
    have raw := (BoundedFormula.realize_toFormula M
      (BoundedFormula.allMem 0 (BoundedFormula.nonemptyFormula 0))
      (extend A Fin.elim0) (Fin.cases hA (fun i => Fin.elim0 i))).1 premise
    intro x hx
    exact (BoundedFormula.truth_nonemptyFormula 0 _).1 (raw x hx)
  obtain ⟨f, hf, code⟩ := witnesses A hA nonempty
  apply (realize_ex M.sets _ _).2
  refine ⟨f, hf, ?_⟩
  apply (BoundedFormula.realize_toFormula M _ _
    (Fin.cases hf (Fin.cases hA (fun i => Fin.elim0 i)))).2
  exact (BoundedFormula.truth_choiceFunctionFormula 1 0 _).2 code

variable {P : Type u} [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))

include pairing unions powers separation collection infinite choice carrier order generic in
theorem ordinaryExtension_choice_witness {A : ZFSet.{u}}
    (hA : A ∈ (M.ordinaryExtension s H).sets) (nonempty : ∀ x ∈ A, x.Nonempty) :
    ∃ f ∈ (M.ordinaryExtension s H).sets, ChoiceFunctionCode A f := by
  let N := M.ordinaryExtension s H
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order infinite H generic
  have pairingN : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unionsN : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powersN : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  have separationN : SeparationSchema N.sets := zf.2.1
  have hUnion := N.union_mem unionsN hA
  obtain ⟨β, hβ, value⟩ := (M.mem_ordinaryExtension s H (⋃₀ A)).1 hUnion
  have boundM := M.union_mem unions (M.union_mem unions hβ)
  have poolM := M.namePool_mem s pairing unions powers separation collection carrier boundM
  obtain ⟨T, hT, f, hf, ordinal, injection, onto⟩ :=
    M.exists_groundOrdinalEnumeration pairing unions powers separation collection choice poolM
  let function : FunctionGraphOn T f := ⟨_, injection.function⟩
  have names : ∀ i, IsName s (function.value i) := by
    intro i
    exact ((mem_namePool s _ _).1
      (ZFSet.pair_mem_prod.1 (injection.function.1 (function.value_entry i))).2).2
  let η := Name.indexedGraphName ⊤ function names
  have hη : η ∈ (M.nameDomain s).names :=
    M.indexedGraphName_mem s ⊤ pairing unions powers separation collection
      (M.transitive carrier (s.encode_mem ⊤)) hT hf function names
  let e := Name.eval {q | H.mem q} η
  have he : e ∈ N.sets := (M.mem_ordinaryExtension s H e).2 ⟨η, hη, rfl⟩
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H
  have hTN : T ∈ N.sets := includes hT
  have enumeration : FunctionGraphOn T e :=
    ⟨_, Name.eval_indexedGraphName_function {q | H.mem q} ⊤ H.top_mem function names⟩
  have covers := Name.indexedGraphName_covers_eval {q | H.mem q} ⊤ H.top_mem β function names onto
  have meets : ∀ x ∈ A, ∃ i ∈ T, ∃ y ∈ x, ZFSet.pair i y ∈ e := by
    intro x hx
    obtain ⟨y, hy⟩ := nonempty x hx
    have member : y ∈ Name.eval {q | H.mem q} β := by
      rw [value]
      exact ZFSet.mem_sUnion.2 ⟨x, hx, hy⟩
    obtain ⟨i, hi, entry⟩ := covers y member
    exact ⟨i, hi, y, hy, entry⟩
  exact ⟨ordinalIndexedChoiceGraph A T e,
    N.ordinalIndexedChoiceGraph_mem pairingN unionsN powersN separationN hA hTN he,
    ordinalIndexedChoiceGraph_choice ordinal enumeration meets⟩

include pairing unions powers separation collection infinite choice carrier order generic in
theorem ordinaryExtension_choice :
    Realize (M.ordinaryExtension s H).sets SetFormula.choice Fin.elim0 := by
  apply (M.ordinaryExtension s H).choice_of_witnesses
  intro A hA nonempty
  exact M.ordinaryExtension_choice_witness s pairing unions powers separation collection infinite choice
    carrier order H generic hA nonempty

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (T : ZFSet.{u}) (K : L → Subgroup G)

theorem exists_ground_supportedEqualityChoice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (H : ConditionFilter P) (genericCoded : H.GenericFor (M.codedFamily s))
    (genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
    {B : ZFSet.{u}} (hB : B ∈ M.sets) (smallB : M.groundEmbeddable B ZFSet.omega)
    (subset : B ⊆ b.carrier) (z : (M.nameDomain s).names)
    (visible : ∀ v : L, b.encode v ∈ B → Name.eval {p | H.mem p} z.val ∈
      Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v))) :
    ∃ f ∈ M.sets, ZFSet.IsFunc B (M.niceSupportNameCodes a s T K) f ∧
      f ⊆ supportedEqualityRelation B (M.niceSupportNameCodes a s T K)
        (M.niceSupportRelation a s b T K)
        (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K))
        (Name.eval {p | H.mem p} z.val) := by
  let N := M.ordinaryExtension s H
  have codesGround := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have relationGround := M.supportedEqualityRelation_mem_ordinary a s b T K H t pairing unions powers
    separation collection infinite carrier order group nodes supports maps hT valid genericFormula hB z
  have total := M.supportedEqualityRelation_total a s b T K H subset visible
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  have choiceN := M.ordinaryExtension_choice s pairing unions powers separation collection infinite
    choice carrier order H genericFormula
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H
  obtain ⟨f, hf, function, selected⟩ := N.uniformize_relation zf.1.2.2.2.1 zf.1.2.2.2.2.1
    zf.1.2.2.2.2.2.1 zf.2.1 choiceN (includes hB) (includes codesGround) relationGround total
  have ground := M.ordinaryExtension_countableDomainFunction_mem s pairing unions powers separation
    collection infinite choice carrier order small hB codesGround smallB closed H genericCoded
    genericFormula hf function
  exact ⟨f, ground, function, selected⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GeneratedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot
universe u
variable {α : Type u} (P : MeetOrder α) (A : α → Prop)

theorem generatedMeetPredicate_least (F : Compression.MeetFilter P)
    (contains : ∀ a, A a → F.mem a) {x : α} (hx : generatedMeetPredicate P A x) : F.mem x := by
  obtain ⟨a, ha, b, path, lower⟩ := hx
  have hb : F.mem b := by
    clear lower
    induction path with
    | refl => exact contains a ha
    | tail path step ih =>
      obtain ⟨c, hc, rfl⟩ := step
      exact F.closed_meet ih (contains c hc)
  exact F.upward hb lower

end PartitionPilot

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_SmallCodedMeetActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace MeetOrderCode

variable {P r μ : ZFSet.{u}} (code : MeetOrderCode P r μ)

theorem smallMeet_graph_eq :
    ((SetMembers.presentation P).product (SetMembers.presentation P)).graph
      (SetMembers.presentation P) (fun xy => code.toSmallMeetOrder.meet xy.1 xy.2) = μ :=
  ((SetMembers.presentation P).product (SetMembers.presentation P)).graph_decodeFunction
    (SetMembers.presentation P) μ code.operation

end MeetOrderCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMeetGeneratorSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem pair_mem_meetGeneratorSteps (P μ A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ meetGeneratorSteps P μ A ↔
      x ∈ P ∧ y ∈ P ∧ ∃ a ∈ A, ZFSet.pair (ZFSet.pair x a) y ∈ μ := by
  rw [meetGeneratorSteps, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x', hx, y', hy, a, ha, equal, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hy, a, ha, entry⟩
  · rintro ⟨hx, hy, a, ha, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, a, ha, rfl, entry⟩

namespace BoundedFormula

theorem truth_meetGeneratorStepFormula {n} (z P μ A : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (meetGeneratorStepFormula z P μ A) env ↔
      ∃ x ∈ env P, ∃ y ∈ env P, ∃ a ∈ env A,
        env z = ZFSet.pair x y ∧ ZFSet.pair (ZFSet.pair x a) y ∈ env μ := by
  simp only [meetGeneratorStepFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

end BoundedFormula

theorem TransitiveGround.meetGeneratorSteps_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P μ A : ZFSet.{u}} (hP : P ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) :
    meetGeneratorSteps P μ A ∈ M.sets := by
  let params := extend P (extend μ (extend A Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.meetGeneratorStepFormula 0 1 2 3) params
    (Fin.cases hP (Fin.cases hμ (Fin.cases hA (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hP hP)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.meetGeneratorStepFormula 0 1 2 3) (extend z params))
      (ZFSet.prod P P) = meetGeneratorSteps P μ A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, meetGeneratorSteps, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_meetGeneratorStepFormula _ _ _ _ _)
  exact equal ▸ selected

theorem MeetOrderCode.meetGeneratorSteps_iff {P r μ A : ZFSet.{u}}
    (code : MeetOrderCode P r μ) (subset : A ⊆ P) (x y : SetMembers P) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ meetGeneratorSteps P μ A ↔
      meetGeneratorStep code.toSmallMeetOrder (fun a => SetMembers.raw a ∈ A) x y := by
  rw [pair_mem_meetGeneratorSteps]
  constructor
  · rintro ⟨_, _, a, ha, entry⟩
    refine ⟨SetMembers.ofMem a (subset ha), ?_, ?_⟩
    · simpa only [SetMembers.raw_ofMem] using ha
    · apply Eq.symm
      apply (code.toSmallMeetOrder_meet_eq_iff _ _ _).2
      simpa only [SetMembers.raw_ofMem] using entry
  · rintro ⟨a, ha, equal⟩
    exact ⟨SetMembers.raw_mem x, SetMembers.raw_mem y, SetMembers.raw a, ha,
      (code.toSmallMeetOrder_meet_eq_iff _ _ _).1 equal.symm⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundTestedMeetFilters
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
variable (M : TransitiveGround.{u})

theorem generatedMeetFilter_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P r μ A : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets)
    (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) : M.generatedMeetFilter P r μ A ∈ M.sets :=
  M.relationImage_mem separation
    (M.relationImage_mem separation hA hP
      (M.finitePathClosure_mem pairing unions powers separation infinite hP
        (M.meetGeneratorSteps_mem pairing unions powers separation hP hμ hA))) hP hr

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions separation infinite

theorem generatedMeetFilter_small_iff {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) (x : SetMembers P) :
    SetMembers.raw x ∈ M.generatedMeetFilter P r μ A ↔
      generatedMeetPredicate code.toSmallMeetOrder (fun a => SetMembers.raw a ∈ A) x := by
  have paths := M.pair_mem_finitePathClosure pairing unions separation infinite
    (SetMembers.presentation P) (meetGeneratorStep code.toSmallMeetOrder
      (fun a => SetMembers.raw a ∈ A)) (code.meetGeneratorSteps_iff subset) hP
  rw [generatedMeetFilter, mem_relationImage]
  constructor
  · rintro ⟨_, b, hb, lower⟩
    obtain ⟨hbP, a, ha, path⟩ := (mem_relationImage _ _ _ b).1 hb
    let a' := SetMembers.ofMem a (subset ha)
    let b' := SetMembers.ofMem b hbP
    have path' : ZFSet.pair (SetMembers.raw a') (SetMembers.raw b') ∈
        M.finitePathClosure P (meetGeneratorSteps P μ A) := by
      simpa only [a', b', SetMembers.raw_ofMem] using path
    refine ⟨a', ?_, b', (paths a' b').1 path', ?_⟩
    · simpa only [a', SetMembers.raw_ofMem] using ha
    · change ZFSet.pair (SetMembers.raw b') (SetMembers.raw x) ∈ r
      simpa only [b', SetMembers.raw_ofMem] using lower
  · rintro ⟨a, ha, b, path, lower⟩
    exact ⟨SetMembers.raw_mem x, SetMembers.raw b,
      (mem_relationImage _ _ _ _).2 ⟨SetMembers.raw_mem b, SetMembers.raw a, ha,
        (paths a b).2 path⟩, lower⟩

theorem generatedMeetFilter_contains {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) :
    A ⊆ M.generatedMeetFilter P r μ A := by
  intro x hx
  have member := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset
    (SetMembers.ofMem x (subset hx))).2
      (generatedMeetPredicate_contains code.toSmallMeetOrder _
        (by simpa only [SetMembers.raw_ofMem] using hx))
  simpa only [SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_filter {P r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P) (nonempty : A.Nonempty) :
    MeetFilterCode P r μ (M.generatedMeetFilter P r μ A) := by
  have exactMem := M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset
  have typedNonempty : ∃ a : SetMembers P, SetMembers.raw a ∈ A := by
    obtain ⟨a, ha⟩ := nonempty
    exact ⟨SetMembers.ofMem a (subset ha), by
      simpa only [SetMembers.raw_ofMem] using (show a ∈ A from ha)⟩
  let typed := PartitionPilot.generatedMeetFilter code.toSmallMeetOrder
    (fun a => SetMembers.raw a ∈ A) typedNonempty
  have bounded : M.generatedMeetFilter P r μ A ⊆ P :=
    fun x hx => ((mem_relationImage _ _ _ x).1 hx).1
  refine ⟨bounded, ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := nonempty
    exact ⟨a, M.generatedMeetFilter_contains pairing unions separation infinite hP code subset ha⟩
  · intro x hx y hy lower
    let x' := SetMembers.ofMem x (bounded hx)
    let y' := SetMembers.ofMem y hy
    have hx' : typed.mem x' := (exactMem x').1 (by simpa only [x', SetMembers.raw_ofMem] using hx)
    have lower' : code.toSmallMeetOrder.le x' y' := by
      change ZFSet.pair (SetMembers.raw x') (SetMembers.raw y') ∈ r
      simpa only [x', y', SetMembers.raw_ofMem] using lower
    have member := (exactMem y').2 (typed.upward hx' lower')
    simpa only [y', SetMembers.raw_ofMem] using member
  · intro x hx y hy z entry
    have hz := (ZFSet.pair_mem_prod.1 (code.operation.1 entry)).2
    let x' := SetMembers.ofMem x (bounded hx)
    let y' := SetMembers.ofMem y (bounded hy)
    let z' := SetMembers.ofMem z hz
    have hx' : typed.mem x' := (exactMem x').1 (by simpa only [x', SetMembers.raw_ofMem] using hx)
    have hy' : typed.mem y' := (exactMem y').1 (by simpa only [y', SetMembers.raw_ofMem] using hy)
    have equal : code.toSmallMeetOrder.meet x' y' = z' :=
      (code.toSmallMeetOrder_meet_eq_iff x' y' z').2
        (by simpa only [x', y', z', SetMembers.raw_ofMem] using entry)
    have member := (exactMem z').2 (equal ▸ typed.closed_meet hx' hy')
    simpa only [z', SetMembers.raw_ofMem] using member

theorem generatedMeetFilter_least {P r μ A F : ZFSet.{u}}
    (hP : P ∈ M.sets) (code : MeetOrderCode P r μ) (subset : A ⊆ P)
    (filter : MeetFilterCode P r μ F) (contains : A ⊆ F) :
    M.generatedMeetFilter P r μ A ⊆ F := by
  let typed : Compression.MeetFilter code.toSmallMeetOrder := {
    mem := fun x => SetMembers.raw x ∈ F
    nonempty := by
      obtain ⟨x, hx⟩ := filter.nonempty
      exact ⟨SetMembers.ofMem x (filter.subset hx), by
        simpa only [SetMembers.raw_ofMem] using (show x ∈ F from hx)⟩
    upward := fun {x y} hx lower => filter.upward _ hx _ (SetMembers.raw_mem y) lower
    closed_meet := fun {x y} hx hy => filter.closed_meet _ hx _ hy _ (code.smallMeet_entry x y) }
  intro x hx
  have hxP := ((mem_relationImage _ _ _ x).1 hx).1
  let x' := SetMembers.ofMem x hxP
  have predicate := (M.generatedMeetFilter_small_iff pairing unions separation infinite hP code subset x').1
    (by simpa only [x', SetMembers.raw_ofMem] using hx)
  have member := generatedMeetPredicate_least code.toSmallMeetOrder _ typed
    (fun a ha => contains ha) predicate
  simpa only [typed, x', SetMembers.raw_ofMem] using member

end TransitiveGround

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem generatedMeetFilter_eq_of_coinitial
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {P r μ B F : ZFSet.{u}} (hP : P ∈ M.sets) (meet : MeetOrderCode P r μ)
    (filter : MeetFilterCode P r μ F) (subset : B ⊆ F)
    (coinitial : ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ r) :
    M.generatedMeetFilter P r μ B = F := by
  have bounded : B ⊆ P := fun _ hx => filter.subset (subset hx)
  have nonempty : B.Nonempty := by
    obtain ⟨x, hx⟩ := filter.nonempty
    obtain ⟨b, hb, _⟩ := coinitial x hx
    exact ⟨b, hb⟩
  have generated := M.generatedMeetFilter_filter pairing unions separation infinite hP meet bounded nonempty
  have contains := M.generatedMeetFilter_contains pairing unions separation infinite hP meet bounded
  have least := M.generatedMeetFilter_least pairing unions separation infinite hP meet bounded filter subset
  apply ZFSet.ext
  intro x
  refine ⟨fun hx => least hx, ?_⟩
  intro hx
  obtain ⟨b, hb, lower⟩ := coinitial x hx
  exact generated.upward b (contains hb) x (filter.subset hx) lower

end TransitiveGround

namespace GroundSequenceReflection
variable {M N : TransitiveGround.{u}} {P : ZFSet.{u}}
variable (reflection : GroundSequenceReflection M N P)
include reflection

theorem coinitial_filter
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    {r μ B F : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (meet : MeetOrderCode P r μ) (hB : B ∈ N.sets)
    (small : N.groundEmbeddable B ZFSet.omega)
    (filter : MeetFilterCode P r μ F) (subset : B ⊆ F)
    (coinitial : ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ r) :
    B ∈ M.sets ∧ M.groundEmbeddable B ZFSet.omega ∧
      M.generatedMeetFilter P r μ B = F ∧ F ∈ M.sets := by
  obtain ⟨ground, countable⟩ := reflection.countable_subset pairing unions powers separation infinite choice
    pairingN unionsN powersN separationN infiniteN hP hB
    (fun _ hb => filter.subset (subset hb)) small
  have equal := M.generatedMeetFilter_eq_of_coinitial pairing unions separation infinite
    hP meet filter subset coinitial
  have generatedGround := M.generatedMeetFilter_mem pairing unions powers separation infinite hP hr hμ ground
  exact ⟨ground, countable, equal, equal ▸ generatedGround⟩

end GroundSequenceReflection
end

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundSerializedChronologyTimeEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem internal_chronological_coinitiality
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (ordinal : ordinalSetProperty T)
    (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets,
      InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
        ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ r := by
  have descent := essentialHeightDescent_of_chronological_laws meet filter born oldMeet strictHeight
  have small := M.essentialBirthIndices_countable pairing unions powers separation infinite choice
    hF hT hr hBirth hC hQ hHeight filter.subset ordinal strictHeight.function smallQ irreflexive descent
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    M.internal_countable_basis_of_birth_layers pairing unions powers separation infinite choice
      hF hT hr hBirth meet.order filter.subset born small localBases
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalHistory

variable {M : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

theorem all_filters_internal_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt) :
    ∀ cutoff ∈ T, ∀ F ∈ M.sets,
      MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F →
        M.InternalCountableBelow (history.order cutoff) F F := by
  intro cutoff
  induction cutoff using ZFSet.inductionOn with
  | h cutoff ih =>
    intro hc F hF filter
    have localBases : ∀ t ∈ essentialBirthIndices F T (history.order cutoff) (history.birth cutoff),
        M.InternalCountableBelow (history.order cutoff) F
          (essentialBirthFiber F T (history.order cutoff) (history.birth cutoff) t) := by
      intro t ht
      obtain ⟨htT, x, hx, xt⟩ :=
        (mem_essentialBirthIndices F T (history.order cutoff) (history.birth cutoff) t).1 ht
      have bounded := history.birth_bound cutoff hc x
        (filter.subset (birthEssentialSet_subset F T (history.order cutoff) (history.birth cutoff) hx)) t xt
      apply (history.layer cutoff hc t htT bounded).internal_countable_essentials
        pairing unions powers separation infinite choice (history.space_mem cutoff hc)
        (history.order_mem cutoff hc) (history.birth_mem cutoff hc) hF hT (M.transitive hT htT)
        (history.meet_order cutoff hc) filter (history.birth_function cutoff hc)
      intro s hs
      have hsT : s ∈ T := ordinal.1 t htT s hs
      have before : s ∈ cutoff := bounded.elim
        (fun equal => equal ▸ hs) (fun earlier => ordinal.2 cutoff hc t earlier s hs)
      exact ⟨history.space_mem s hsT, history.meet_order s hsT, ih s before hsT⟩
    obtain ⟨B, hB, f, hf, injection, positive, below⟩ :=
      M.internal_chronological_coinitiality pairing unions powers separation infinite choice
        hF hT (history.order_mem cutoff hc) (history.birth_mem cutoff hc)
        hC hQ (history.height_mem cutoff hc) (history.meet_order cutoff hc) filter
        (history.birth_function cutoff hc) ordinal (history.old_meet cutoff hc)
        (history.strict_height cutoff hc) smallQ irreflexive localBases
    exact ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩

theorem exists_internal_basis
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ M.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff := by
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    history.all_filters_internal_countable pairing unions powers separation infinite choice
      hT hC hQ ordinal smallQ irreflexive cutoff hc F hF filter
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end GroundChronologicalHistory





end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologicalHistory

open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

theorem exists_extension_basis
    (includes : M.sets ⊆ N.sets)
    (pairing : Realize N.sets SetFormula.pairing Fin.elim0)
    (unions : Realize N.sets SetFormula.union Fin.elim0)
    (powers : Realize N.sets powerSet Fin.elim0) (separation : SeparationSchema N.sets)
    (infinite : Realize N.sets SetFormula.infinity Fin.elim0)
    (choice : Realize N.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ N.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff :=
  (history.of_inclusion includes).exists_internal_basis pairing unions powers separation infinite
    choice (includes hT) (includes hC) (includes hQ) ordinal
    (M.groundEmbeddable_of_inclusion N includes smallQ) irreflexive hc hF filter

end PartitionPilot.Forcing.GroundChronologicalHistory



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyFieldAppend
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {T : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (newValues : Fin 5 → ZFSet.{u}) (ground : ∀ j, newValues j ∈ M.sets)

theorem appendTime_value_at (j : Fin 5) :
    (fields.appendTime pairing unions newValues ground).value j T = newValues j := by
  apply GroundChronologyFields.value_eq_of_entry
  exact ZFSet.mem_insert _ _

end PartitionPilot.Forcing.GroundChronologyFields

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainLimitCoverageFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_supportedCertificateFormula {n}
    (nodes N order R niceEval visibilityEval value F B f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (supportedCertificateFormula nodes N order R niceEval visibilityEval value F B f) env ↔
      SupportedEqualityCertificate (env nodes) (env N) (env order) (env R)
        (env niceEval) (env visibilityEval) (env value) (env F) (env B) (env f) := by
  classical
  simp only [supportedCertificateFormula, Truth, truth_exMem, truth_pairMembershipFormula,
    truth_functionFormula, truth_exGraphFields, truth_imp, not_exists, not_and, not_not,
    ← iff_def]
  rfl

theorem truth_supportedCertificateEntryFormula {n}
    (entry J PF PB WF nodes N order R inputEval niceEval visibilityEval : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (supportedCertificateEntryFormula entry J PF PB WF nodes N order R
      inputEval niceEval visibilityEval) env ↔
      ∃ j ∈ env J, ∃ F ∈ env PF, ∃ B ∈ env PB, ∃ f ∈ env WF,
        env entry = ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) ∧
        ∃ value, ZFSet.pair j value ∈ env inputEval ∧
          SupportedEqualityCertificate (env nodes) (env N) (env order) (env R)
            (env niceEval) (env visibilityEval) value F B f := by
  simp only [supportedCertificateEntryFormula, truth_exPairFields, Truth,
    truth_exGraphFields, truth_supportedCertificateFormula]
  change (∃ j tail, env entry = ZFSet.pair j tail ∧
    ∃ F rest, tail = ZFSet.pair F rest ∧
    ∃ B f, rest = ZFSet.pair B f ∧
      j ∈ env J ∧ F ∈ env PF ∧ B ∈ env PB ∧ f ∈ env WF ∧
      ∃ j' value, ZFSet.pair j' value ∈ env inputEval ∧ j' = j ∧
        SupportedEqualityCertificate (env nodes) (env N) (env order) (env R)
          (env niceEval) (env visibilityEval) value F B f) ↔ _
  constructor
  · rintro ⟨j, tail, equal, F, rest, rfl, B, f, rfl, hj, hF, hB, hf,
      j', value, evaluated, rfl, certificate⟩
    exact ⟨j', hj, F, hF, B, hB, f, hf, equal, value, evaluated, certificate⟩
  · rintro ⟨j, hj, F, hF, B, hB, f, hf, equal, value, evaluated, certificate⟩
    exact ⟨j, _, equal, F, _, rfl, B, f, rfl, hj, hF, hB, hf,
      j, value, evaluated, rfl, certificate⟩





end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SupportedCertificateFamilyFormulas
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

theorem supportedCertificateRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {J PF PB WF nodes N order R inputEval niceEval visibilityEval : ZFSet.{u}}
    (hJ : J ∈ M.sets) (hPF : PF ∈ M.sets) (hPB : PB ∈ M.sets) (hWF : WF ∈ M.sets)
    (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets) (hOrder : order ∈ M.sets)
    (hR : R ∈ M.sets) (hInput : inputEval ∈ M.sets) (hNice : niceEval ∈ M.sets)
    (hVisibility : visibilityEval ∈ M.sets) :
    supportedCertificateRelation J PF PB WF nodes N order R inputEval niceEval visibilityEval ∈ M.sets := by
  let params : Fin 11 → ZFSet.{u} := ![J, PF, PB, WF, nodes, N, order, R,
    inputEval, niceEval, visibilityEval]
  have members : ∀ i, params i ∈ M.sets := by
    exact (Fin.cases hJ (Fin.cases hPF (Fin.cases hPB (Fin.cases hWF (Fin.cases hNodes (Fin.cases hN (Fin.cases hOrder (Fin.cases hR (Fin.cases hInput (Fin.cases hNice (Fin.cases hVisibility (fun i => Fin.elim0 i))))))))))))
  have bound := M.prod_mem pairing unions powers separation hJ
    (M.prod_mem pairing unions powers separation hPF
      (M.prod_mem pairing unions powers separation hPB hWF))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.supportedCertificateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11)
    params members bound
  have equal : ZFSet.sep (fun entry => BoundedFormula.Truth
      (BoundedFormula.supportedCertificateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11)
      (extend entry params)) (ZFSet.prod J (ZFSet.prod PF (ZFSet.prod PB WF))) =
      supportedCertificateRelation J PF PB WF nodes N order R inputEval niceEval visibilityEval := by
    apply ZFSet.ext
    intro entry
    rw [ZFSet.mem_sep, supportedCertificateRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_supportedCertificateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 _)
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_supportedCertificateFamilyFormula (env : Fin 12 → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets supportedCertificateFamilyFormula env ↔
      env 0 ⊆ supportedCertificateRelation (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) (env 11) := by
  rw [supportedCertificateFamilyFormula, BoundedFormula.realize_toFormula M _ env members]
  change (∀ entry ∈ env 0, BoundedFormula.Truth
    (BoundedFormula.supportedCertificateEntryFormula 0 2 3 4 5 6 7 8 9 10 11 12)
      (extend entry env)) ↔ _
  constructor
  · intro allEntries entry member
    obtain ⟨j, hj, F, hF, B, hB, f, hf, equal, value, evaluated, certificate⟩ :=
      (BoundedFormula.truth_supportedCertificateEntryFormula 0 2 3 4 5 6 7 8 9 10 11 12 _).1
        (allEntries entry member)
    change entry = ZFSet.pair j (ZFSet.pair F (ZFSet.pair B f)) at equal
    rw [equal]
    exact (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2
      ⟨hj, hF, hB, hf, value, evaluated, certificate⟩
  · intro selected entry member
    obtain ⟨_, witness⟩ := ZFSet.mem_sep.1 (selected member)
    exact (BoundedFormula.truth_supportedCertificateEntryFormula 0 2 3 4 5 6 7 8 9 10 11 12 _).2 witness

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixLimitChronologyCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitChronologyFields_terminal (j : Fin 5) :
    run.limitChronologyFields.value j run.cutoffLimit = run.limitTerminalFields j :=
  run.limitPriorFields.appendTime_value_at pairing unions run.limitTerminalFields run.limitTerminalFields_ground j

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalChronology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

namespace FinalChronology
variable {run} {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)

theorem history_values (s : ZFSet.{u}) :
    chronology.serial.toHistory.space s = run.limitChronologyFields.value 0 s ∧
    chronology.serial.toHistory.order s = run.limitChronologyFields.value 1 s ∧
    chronology.serial.toHistory.meetGraph s = run.limitChronologyFields.value 2 s ∧
    chronology.serial.toHistory.birth s = run.limitChronologyFields.value 3 s ∧
    chronology.serial.toHistory.height s = run.limitChronologyFields.value 4 s :=
  ⟨chronology.values 0 s, chronology.values 1 s, chronology.values 2 s,
    chronology.values 3 s, chronology.values 4 s⟩

theorem terminal_values (i₀ : I) :
    chronology.serial.toHistory.space run.cutoffLimit = (run.finalGeometry i₀).carrier ∧
    chronology.serial.toHistory.order run.cutoffLimit = (run.finalGeometry i₀).order ∧
    chronology.serial.toHistory.meetGraph run.cutoffLimit = (run.finalGeometry i₀).meetGraph ∧
    chronology.serial.toHistory.birth run.cutoffLimit = (run.finalGeometry i₀).birth ∧
    chronology.serial.toHistory.height run.cutoffLimit = (run.finalGeometry i₀).height := by
  obtain ⟨space, order, meet, birth, height⟩ := chronology.history_values run.cutoffLimit
  exact ⟨space.trans (run.limitChronologyFields_terminal 0),
    order.trans (run.limitChronologyFields_terminal 1), meet.trans (run.limitChronologyFields_terminal 2),
    birth.trans (run.limitChronologyFields_terminal 3), height.trans (run.limitChronologyFields_terminal 4)⟩

end FinalChronology

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalExtensionBases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalChronology
open SetFormula
universe u v
variable {M N : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)
include chronology

theorem exists_extension_basis (i₀ : I)
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ (run.finalGeometry i₀).order := by
  have terminal := chronology.terminal_values i₀
  have atTerminal : MeetFilterCode (chronology.serial.toHistory.space run.cutoffLimit)
      (chronology.serial.toHistory.order run.cutoffLimit)
      (chronology.serial.toHistory.meetGraph run.cutoffLimit) F := by
    simpa only [terminal.1, terminal.2.1, terminal.2.2.1] using filter
  have basis := chronology.serial.toHistory.exists_extension_basis includes pairingN unionsN powersN
    separationN infiniteN choiceN
    (M.insert_mem pairing unions run.cutoffLimit_ground run.cutoffLimit_ground)
    (run.finalGeometry i₀).columns_ground (run.finalGeometry i₀).coordinates_ground
    chronology.serial.ordinal smallD irreflexive (ZFSet.mem_insert run.cutoffLimit run.cutoffLimit)
    hF atTerminal
  simpa only [terminal.2.1] using basis

end PartitionPilot.Forcing.GroundMainPrefix.FinalChronology

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalOrdinaryInsertion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment
open SetFormula
universe u v
variable {M N : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalSupportFulfillment level i₀)
variable (reflection : GroundSequenceReflection M N (run.finalGeometry i₀).carrier)
include fulfilled reflection

theorem reflected_extension_basis
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (includes : M.sets ⊆ N.sets)
    (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
    (unionsN : Realize N.sets SetFormula.union Fin.elim0)
    (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
    (infiniteN : Realize N.sets infinity Fin.elim0)
    (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
      (run.finalGeometry i₀).meetGraph F) :
    ∃ B ∈ M.sets, B ∈ N.sets ∧ M.groundEmbeddable B ZFSet.omega ∧ B ⊆ F ∧
      (∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ (run.finalGeometry i₀).order) ∧
      M.generatedMeetFilter (run.finalGeometry i₀).carrier (run.finalGeometry i₀).order
        (run.finalGeometry i₀).meetGraph B = F ∧ F ∈ M.sets := by
  obtain ⟨B, hB, f, hf, injection, subset, coinitial⟩ :=
    fulfilled.chronology.exists_extension_basis i₀ includes pairingN unionsN powersN separationN
      infiniteN choiceN smallD irreflexive hF filter
  obtain ⟨ground, countable, equal, filterGround⟩ := reflection.coinitial_filter
    pairing unions powers separation infinite choice pairingN unionsN powersN separationN infiniteN
    (run.finalGeometry i₀).carrier_ground (run.finalGeometry i₀).order_ground
    (run.finalGeometry i₀).meet_ground (run.finalGeometry i₀).meet hB ⟨f, hf, injection⟩
    filter subset coinitial
  exact ⟨B, ground, hB, countable, subset, coinitial, equal, filterGround⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalDecidedVisibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

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
variable {Q : Type u} [PartialOrder Q] [OrderTop Q] (s : Presentation Q)

theorem exists_decided_visibilityProfile
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (z : (M.nameDomain s).names)
      (_hs : HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z.val)
      (_subset : Name.eval {p | H.mem p} z.val ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (p : Q) (_hp : H.mem p),
      let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
      ∃ ground : F ∈ M.sets,
        MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
        ∃ B ∈ M.sets, M.groundEmbeddable B ZFSet.omega ∧ B ⊆ F ∧
          (∀ x ∈ F, ∃ v ∈ B, ZFSet.pair v x ∈ geometry.order) ∧
          ∃ q, H.mem q ∧ q ≤ p ∧
            Forces (M.nameDomain s) visibilityProfileFormula
              (M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
                carrier geometry.actors_ground geometry.carrier_ground
                (geometry.decoded_supportBasis_ground pairing unions powers separation)
                maps hT valid F ground z) q ∧
            M.DecidesVisibilityProfile a s b d.principalFix T F z.val q := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent z hs subset p hp
  let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  have system := M.niceNameSystem a s t pairing unions powers separation collection carrier order
    maps hT valid terms b d ⊥ directed geometry.actors_ground geometry.carrier_ground supports children
  have filter : MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F := by
    have coded := M.visibleSupportProfile_filter a s b d ⊥ directed T H valid system genericFormula
      z hs subset geometry.meet.smallMeet descent
    have meetGraph : (b.product b).graph b (fun vw => geometry.meet.smallMeet vw.1 vw.2) =
        geometry.meetGraph := geometry.meet.smallMeet_graph_eq
    have orderGraph : b.conditionOrder = geometry.order := geometry.decoded_order_eq
    rw [meetGraph, orderGraph] at coded
    exact coded
  have inExtension := M.visibleSupportProfile_mem_ordinary a s t b d pairing unions powers separation
    collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid order
    infinite H genericFormula z
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  have choiceN := M.ordinaryExtension_choice s pairing unions powers separation collection infinite
    choice carrier order H genericFormula
  have reflection := M.ordinaryExtension_sequenceReflection s pairing unions powers separation collection
    infinite choice carrier order small geometry.carrier_ground closed H genericCoded genericFormula
  obtain ⟨B, hB, _, countable, contained, coinitial, _, ground⟩ :=
    fulfilled.reflected_extension_basis reflection infinite choice
      (M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H)
      zf.1.2.2.2.1 zf.1.2.2.2.2.1 zf.1.2.2.2.2.2.1 zf.2.1 zf.1.2.2.2.2.2.2 choiceN
      smallD irreflexive inExtension filter
  refine ⟨ground, filter, B, hB, countable, contained, coinitial, ?_⟩
  exact M.exists_forced_visibleSupportProfile a s t b d pairing unions powers separation collection
    carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid small H
    genericFormula z ground p hp

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalSupportedCertificateFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_supportedEqualityCertificateBound (nodes N F B f : ZFSet.{u}) :
    ZFSet.pair F (ZFSet.pair B f) ∈ M.supportedEqualityCertificateBound nodes N ↔
      (F ∈ M.sets ∧ F ⊆ nodes) ∧
      (B ∈ M.sets ∧ B ⊆ nodes ∧ M.groundEmbeddable B ZFSet.omega) ∧
      (f ∈ M.sets ∧ f ⊆ ZFSet.prod nodes N) := by
  rw [supportedEqualityCertificateBound, ZFSet.pair_mem_prod, ZFSet.pair_mem_prod,
    M.mem_groundPower, M.mem_groundSmallSubsets, M.mem_groundRelations]

theorem supportedEqualityCertificateBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes N : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hN : N ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.supportedEqualityCertificateBound nodes N ∈ M.sets :=
  M.prod_mem pairing unions powers separation (M.groundPower_mem powers hNodes)
    (M.prod_mem pairing unions powers separation
      (M.groundSmallSubsets_mem powers separation hNodes omega)
      (M.groundRelations_mem pairing unions powers separation hNodes hN))

theorem supportedEqualityCertificate_mem {nodes N F B f : ZFSet.{u}}
    (hF : F ∈ M.sets) (profile : F ⊆ nodes) (hB : B ∈ M.sets)
    (basis : B ⊆ F) (small : M.groundEmbeddable B ZFSet.omega)
    (hf : f ∈ M.sets) (function : ZFSet.IsFunc B N f) :
    ZFSet.pair F (ZFSet.pair B f) ∈ M.supportedEqualityCertificateBound nodes N := by
  refine (M.mem_supportedEqualityCertificateBound nodes N F B f).2
    ⟨⟨hF, profile⟩, ⟨hB, fun _ member => profile (basis member), small⟩, hf, ?_⟩
  intro entry member
  obtain ⟨v, hv, tau, htau, rfl⟩ := ZFSet.mem_prod.1 (function.1 member)
  exact ZFSet.pair_mem_prod.2 ⟨profile (basis hv), htau⟩

end TransitiveGround

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation I) (K : I → Subgroup G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

theorem realize_supportedEqualitySequenceEnv (B f : ZFSet.{u})
    (hB : B ∈ M.sets) (hf : f ∈ M.sets) (z : (M.nameDomain s).names)
    (H : ConditionFilter P) :
    Realize ((M.nameDomain s).values {p | H.mem p}) supportedEqualitySequenceFormula
      (evalAssignment {p | H.mem p}
        (M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
          carrier group nodes supports maps hT valid B f hB hf z)) ↔
      ZFSet.IsFunc B (M.niceSupportNameCodes a s T K) f ∧
      ∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
        ZFSet.pair v tau.val ∈ f →
        ZFSet.pair v tau.val ∈ M.niceSupportRelation a s b T K ∧
        Name.eval {p | H.mem p} tau = Name.eval {p | H.mem p} z.val := by
  let env := M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid B f hB hf z
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {p | H.mem p},
    (M.nameDomain s).values_transitive _⟩
  have fields : evalAssignment {p | H.mem p} env =
      ![B, M.niceSupportNameCodes a s T K, f, M.niceSupportRelation a s b T K,
        Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K),
        Name.eval {p | H.mem p} z.val] := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
      (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)))))) i
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
  have meaning := N.realize_supportedEqualitySequenceFormula
    (evalAssignment {p | H.mem p} env) (fun i => ⟨env i, rfl⟩)
  rw [fields] at meaning
  change Realize N.sets supportedEqualitySequenceFormula (evalAssignment {p | H.mem p} env) ↔ _
  rw [fields, meaning]
  constructor
  · rintro ⟨function, allEntries⟩
    refine ⟨function, ?_⟩
    intro v hv tau ht entry
    have result := allEntries v hv tau.val ht entry
    exact ⟨result.1, (M.niceSupportEvaluationName_entry a s T K tau ht H _).1 result.2⟩
  · rintro ⟨function, allEntries⟩
    refine ⟨function, ?_⟩
    intro v hv code hc entry
    let tau : Name s := ⟨code, M.niceSupportNameCodes_valid a s T K code hc⟩
    have result := allEntries v hv tau hc entry
    exact ⟨result.1, (M.niceSupportEvaluationName_entry a s T K tau hc H _).2 result.2⟩

theorem forces_supportedEqualitySequence_entry (small : M.sets.Countable)
    (B f : ZFSet.{u}) (hB : B ∈ M.sets) (hf : f ∈ M.sets)
    (z : (M.nameDomain s).names) (p : P)
    (forced : Forces (M.nameDomain s) supportedEqualitySequenceFormula
      (M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
        carrier group nodes supports maps hT valid B f hB hf z) p)
    (v : ZFSet.{u}) (hv : v ∈ B) (tau : Name s)
    (ht : tau.val ∈ M.niceSupportNameCodes a s T K) (entry : ZFSet.pair v tau.val ∈ f) :
    Name.ForcesEq p z.val tau := by
  let named : (M.nameDomain s).names :=
    ⟨tau, ((M.mem_niceSupportNameCodes a s T K tau.val).1 ht).1⟩
  change Forces (M.nameDomain s) (.equal 0 1 : SetFormula 2) ![z, named] p
  apply (M.ordinaryForces_iff_all_generics s small carrier (.equal 0 1) ![z, named] p).2
  intro H hp generic
  have truth := forces_sound (M.nameDomain s) H generic supportedEqualitySequenceFormula
    (M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid B f hB hf z) hp forced
  have result := (M.realize_supportedEqualitySequenceEnv a s t b K pairing unions powers separation
    collection carrier group nodes supports maps hT valid B f hB hf z H).1 truth
  exact (result.2 v hv tau ht entry).2.symm

theorem exists_forced_supportedEqualitySequence (small : M.sets.Countable)
    (B f : ZFSet.{u}) (hB : B ∈ M.sets) (hf : f ∈ M.sets)
    (z : (M.nameDomain s).names) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (function : ZFSet.IsFunc B (M.niceSupportNameCodes a s T K) f)
    (meaning : ∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
      ZFSet.pair v tau.val ∈ f →
      ZFSet.pair v tau.val ∈ M.niceSupportRelation a s b T K ∧
      Name.eval {p | H.mem p} tau = Name.eval {p | H.mem p} z.val)
    (p : P) (hp : H.mem p) :
    ∃ q, H.mem q ∧ q ≤ p ∧
      Forces (M.nameDomain s) supportedEqualitySequenceFormula
        (M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
          carrier group nodes supports maps hT valid B f hB hf z) q ∧
      ∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T K →
        ZFSet.pair v tau.val ∈ f →
        ZFSet.pair v tau.val ∈ M.niceSupportRelation a s b T K ∧ Name.ForcesEq q z.val tau := by
  let env := M.supportedEqualitySequenceEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid B f hB hf z
  have truth := (M.realize_supportedEqualitySequenceEnv a s t b K pairing unions powers separation
    collection carrier group nodes supports maps hT valid B f hB hf z H).2 ⟨function, meaning⟩
  obtain ⟨r, hr, forced⟩ := (forcing_truth (M.nameDomain s) H generic
    supportedEqualitySequenceFormula env).1 truth
  obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
  have forcedQ := forces_mono (M.nameDomain s) supportedEqualitySequenceFormula env forced qr
  refine ⟨q, hq, qp, forcedQ, ?_⟩
  intro v hv tau ht entry
  exact ⟨(meaning v hv tau ht entry).1,
    M.forces_supportedEqualitySequence_entry a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid small B f hB hf z q forcedQ v hv tau ht entry⟩

end TransitiveGround

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)

theorem supportedCertificateFamilyRelation_mem_ordinary (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
    {nodeOrder J : ZFSet.{u}} (hNodeOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
    M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H ∈
      (M.ordinaryExtension s H).sets := by
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation
    collection carrier H
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection
    carrier order infinite H generic
  have hN := M.niceSupportNameCodes_mem a s b T K t pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have hInput := M.inputEvaluationName_mem s pairing unions powers separation collection carrier hJ validJ
  have hNice := M.niceSupportEvaluationName_mem a s T K t b pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  have hVisibility := M.niceVisibilityEvaluationName_mem a s b t K pairing unions powers separation
    collection carrier group nodes supports maps hT valid
  exact (M.ordinaryExtension s H).supportedCertificateRelation_mem
    zf.1.2.2.2.1 zf.1.2.2.2.2.1 zf.1.2.2.2.2.2.1 zf.2.1
    (includes hJ) (includes (M.groundPower_mem powers nodes))
    (includes (M.groundSmallSubsets_mem powers separation nodes (M.omega_mem separation infinite)))
    (includes (M.groundRelations_mem pairing unions powers separation nodes hN))
    (includes nodes) (includes hN) (includes hNodeOrder)
    (includes (M.niceSupportRelation_mem a s b T K t pairing unions powers separation
      collection carrier group nodes supports maps hT valid))
    ⟨⟨_, hInput⟩, rfl⟩ ⟨⟨_, hNice⟩, rfl⟩ ⟨⟨_, hVisibility⟩, rfl⟩

end TransitiveGround

namespace GroundMainPrefix.FinalSupportFulfillment
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
variable {Q : Type u} [PartialOrder Q] [OrderTop Q] (s : Presentation Q)

theorem exists_supportedEqualityBasis
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (z : (M.nameDomain s).names)
      (_hs : HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z.val)
      (_subset : Name.eval {p | H.mem p} z.val ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (p : Q) (_hp : H.mem p),
      let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
      ∃ ground : F ∈ M.sets,
        MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
        ∃ (B : ZFSet.{u}) (hB : B ∈ M.sets),
          M.groundEmbeddable B ZFSet.omega ∧ B ⊆ F ∧
          (∀ x ∈ F, ∃ v ∈ B, ZFSet.pair v x ∈ geometry.order) ∧
          ∃ (f : ZFSet.{u}) (hf : f ∈ M.sets),
            ZFSet.IsFunc B (M.niceSupportNameCodes a s T d.principalFix) f ∧
            ∃ q, H.mem q ∧ q ≤ p ∧
              Forces (M.nameDomain s) visibilityProfileFormula
                (M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
                  carrier geometry.actors_ground geometry.carrier_ground
                  (geometry.decoded_supportBasis_ground pairing unions powers separation)
                  maps hT valid F ground z) q ∧
              M.DecidesVisibilityProfile a s b d.principalFix T F z.val q ∧
              Forces (M.nameDomain s) supportedEqualitySequenceFormula
                (M.supportedEqualitySequenceEnv a s t b d.principalFix
                  pairing unions powers separation collection carrier geometry.actors_ground
                  geometry.carrier_ground
                  (geometry.decoded_supportBasis_ground pairing unions powers separation)
                  maps hT valid B f hB hf z) q ∧
              ∀ (v : SetMembers geometry.carrier), b.encode v ∈ B →
                ∀ τ : Name s, ZFSet.pair (b.encode v) τ.val ∈ f →
                  τ.val ∈ M.sets ∧ τ.val ⊆ ZFSet.prod T s.carrier ∧
                  HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ ∧
                  d.principalFix v ≤ a.stabilizer s τ ∧ Name.ForcesEq q z.val τ := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent z hs subset p hp
  let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  obtain ⟨ground, filter, B, hB, smallB, contained, coinitial, q₀, hq₀, q₀p, profile, _⟩ :=
    fulfilled.exists_decided_visibilityProfile s collection infinite choice carrier order small
      closed smallD irreflexive a maps T hT valid terms children H genericCoded genericFormula
      descent z hs subset p hp
  have inNodes : B ⊆ b.carrier := fun _ member => filter.subset (contained member)
  have visible : ∀ v : SetMembers geometry.carrier, b.encode v ∈ B →
      Name.eval {p | H.mem p} z.val ∈
        Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) := by
    intro v hv
    exact (M.encode_mem_visibleSupportProfile a s b d T H _ v).1 (contained hv)
  obtain ⟨f, hf, function, selected⟩ := M.exists_ground_supportedEqualityChoice a s t b T
    d.principalFix pairing unions powers separation collection infinite choice carrier order
    geometry.actors_ground geometry.carrier_ground supports maps hT valid small closed H
    genericCoded genericFormula hB smallB inNodes z visible
  have meaning : ∀ raw ∈ B, ∀ τ : Name s,
      τ.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair raw τ.val ∈ f →
      ZFSet.pair raw τ.val ∈ M.niceSupportRelation a s b T d.principalFix ∧
      Name.eval {p | H.mem p} τ = Name.eval {p | H.mem p} z.val := by
    intro raw _ τ ht entry
    have facts := (pair_mem_supportedEqualityRelation B _ _ _ _ raw τ.val).1 (selected entry)
    exact ⟨facts.2.2.1,
      (M.niceSupportEvaluationName_entry a s T d.principalFix τ ht H _).1 facts.2.2.2⟩
  obtain ⟨q, hq, qq₀, forced, entries⟩ := M.exists_forced_supportedEqualitySequence a s t b
    d.principalFix pairing unions powers separation collection carrier geometry.actors_ground
    geometry.carrier_ground supports maps hT valid small B f hB hf z H genericFormula
    function meaning q₀ hq₀
  have profileQ := forces_mono (M.nameDomain s) visibilityProfileFormula _ profile qq₀
  have decisions := (M.forces_visibilityProfile_iff a s t b d.principalFix pairing unions powers
    separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps
    hT valid small F ground z q).1 profileQ
  refine ⟨ground, filter, B, hB, smallB, contained, coinitial, f, hf, function,
    q, hq, le_trans qq₀ q₀p, profileQ, decisions, forced, ?_⟩
  intro v hv τ entry
  have member := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  have certificate := entries (b.encode v) hv τ member entry
  have code := (M.pair_mem_niceSupportRelation a s b T d.principalFix v τ.val).1 certificate.1
  have nice := (niceNameCode_iff a s τ).1 code.2
  exact ⟨code.1, nice.1, niceNameCode_principal_hs a s d ⊥ v directed children code.2,
    nice.2, certificate.2⟩

theorem exists_supportedCertificateFamily
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (_maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (_hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (J : ZFSet.{u}) (_hJ : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
      (_smallJ : M.groundEmbeddable J ZFSet.omega)
      (_hs : ∀ z : Name s, z.val ∈ J →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z)
      (_subset : ∀ z : Name s, z.val ∈ J → Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid)),
      ∃ k ∈ M.sets,
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes a s T d.principalFix)) k ∧
        k ⊆ M.supportedCertificateFamilyRelation a s b T d.principalFix
          geometry.order J validJ H := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent
    J hJ validJ smallJ hs subsets
  let codes := M.niceSupportNameCodes a s T d.principalFix
  let bound := M.supportedEqualityCertificateBound b.carrier codes
  let relation := M.supportedCertificateFamilyRelation a s b T d.principalFix
    geometry.order J validJ H
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  have codesGround := M.niceSupportNameCodes_mem a s b T d.principalFix t pairing unions powers
    separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
  have boundGround := M.supportedEqualityCertificateBound_mem pairing unions powers separation
    geometry.carrier_ground codesGround (M.omega_mem separation infinite)
  have relationGround := M.supportedCertificateFamilyRelation_mem_ordinary a s b T d.principalFix
    t pairing unions powers separation collection infinite carrier order geometry.actors_ground
    geometry.carrier_ground supports maps hT valid geometry.order_ground hJ validJ H genericFormula
  have total : ∀ raw ∈ J, ∃ certificate ∈ bound, ZFSet.pair raw certificate ∈ relation := by
    intro raw member
    let z : (M.nameDomain s).names := ⟨⟨raw, validJ raw member⟩, M.transitive hJ member⟩
    let F := M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val)
    obtain ⟨hF, filter, B, hB, smallB, contained, coinitial, f, hf, function,
        q, hq, _, _, _, forced, _⟩ :=
      fulfilled.exists_supportedEqualityBasis s collection infinite choice carrier order small
        closed smallD irreflexive a maps T hT valid terms children H genericCoded genericFormula
        descent z (hs z.val member) (subsets z.val member) ⊤ H.top_mem
    have certificateBound := M.supportedEqualityCertificate_mem hF filter.subset hB contained
      smallB hf function
    refine ⟨ZFSet.pair F (ZFSet.pair B f), certificateBound, ?_⟩
    change ZFSet.pair raw (ZFSet.pair F (ZFSet.pair B f)) ∈ supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _
    apply (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).2
    have boundFields := (M.mem_supportedEqualityCertificateBound b.carrier codes F B f).1 certificateBound
    refine ⟨member, (M.mem_groundPower _ _).2 boundFields.1,
      (M.mem_groundSmallSubsets _ _ _).2 boundFields.2.1,
      (M.mem_groundRelations _ _ _).2 boundFields.2.2,
      Name.eval {p | H.mem p} z.val,
      (Name.inputEvaluationName_entry s J validJ z.val H _).2 ⟨member, rfl⟩,
      filter.subset, contained, coinitial, function, ?_, ?_⟩
    · intro rawNode V entry inNodes
      obtain ⟨v, rfl⟩ := (b.mem_carrier rawNode).1 inNodes
      have equal := (M.niceVisibilityEvaluationName_entry a s b T d.principalFix H v V).1 entry
      rw [← equal]
      exact (M.encode_mem_visibleSupportProfile a s b d T H _ v).symm
    · have truth := forces_sound (M.nameDomain s) H genericFormula supportedEqualitySequenceFormula
        (M.supportedEqualitySequenceEnv a s t b d.principalFix pairing unions powers separation
          collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
          B f hB hf z) hq forced
      have meaning := (M.realize_supportedEqualitySequenceEnv a s t b d.principalFix pairing unions
        powers separation collection carrier geometry.actors_ground geometry.carrier_ground supports
        maps hT valid B f hB hf z H).1 truth
      intro v hv rawName inCodes entry
      let tau : Name s := ⟨rawName, M.niceSupportNameCodes_valid a s T d.principalFix rawName inCodes⟩
      have result := meaning.2 v hv tau inCodes entry
      exact ⟨result.1, (M.niceSupportEvaluationName_entry a s T d.principalFix tau inCodes H _).2 result.2⟩
  let extension := M.ordinaryExtension s H
  have zf := M.ordinaryExtension_ZF s pairing unions powers separation collection carrier order
    infinite H genericFormula
  have choiceN := M.ordinaryExtension_choice s pairing unions powers separation collection infinite
    choice carrier order H genericFormula
  have includes := M.ground_subset_ordinaryExtension s pairing unions powers separation collection carrier H
  obtain ⟨k, hk, function, selected⟩ := extension.uniformize_relation zf.1.2.2.2.1 zf.1.2.2.2.2.1
    zf.1.2.2.2.2.2.1 zf.2.1 choiceN (includes hJ) (includes boundGround) relationGround total
  have ground := M.ordinaryExtension_countableDomainFunction_mem s pairing unions powers separation
    collection infinite choice carrier order small hJ boundGround smallJ closed H genericCoded
    genericFormula hk function
  exact ⟨k, ground, function, selected⟩

end GroundMainPrefix.FinalSupportFulfillment

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSupportedCertificateFamilyDecisions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (omega : ZFSet.omega ∈ M.sets)

theorem realize_supportedCertificateFamilyEnv (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P) :
    Realize ((M.nameDomain s).values {p | H.mem p}) supportedCertificateFamilyFormula
      (evalAssignment {p | H.mem p}
        (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
          carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ)) ↔
      k ⊆ M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H := by
  let env := M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
    carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ
  let extension : TransitiveGround.{u} := ⟨(M.nameDomain s).values {p | H.mem p},
    (M.nameDomain s).values_transitive _⟩
  have fields : evalAssignment {p | H.mem p} env =
      ![k, J, M.groundPower b.carrier, M.groundSmallSubsets b.carrier ZFSet.omega,
        M.groundRelations b.carrier (M.niceSupportNameCodes a s T K), b.carrier,
        M.niceSupportNameCodes a s T K, nodeOrder, M.niceSupportRelation a s b T K,
        Name.eval {p | H.mem p} (Name.inputEvaluationName s J validJ),
        Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K),
        Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K)] := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))))))))))) i
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · exact Name.eval_check _ ⊤ H.top_mem _
    · rfl
    · rfl
    · rfl
  have meaning := extension.realize_supportedCertificateFamilyFormula
    (evalAssignment {p | H.mem p} env) (fun i => ⟨env i, rfl⟩)
  rw [fields] at meaning
  change Realize extension.sets supportedCertificateFamilyFormula
    (evalAssignment {p | H.mem p} env) ↔ _
  rw [fields]
  exact meaning

theorem exists_forced_supportedCertificateFamily (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (selected : k ⊆ M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H)
    (p : P) (hp : H.mem p) :
    ∃ q, H.mem q ∧ q ≤ p ∧
      Forces (M.nameDomain s) supportedCertificateFamilyFormula
        (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
          carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) q := by
  let env := M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
    carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ
  have truth := (M.realize_supportedCertificateFamilyEnv a s t b T K pairing unions powers separation
    collection carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ H).2 selected
  obtain ⟨r, hr, forced⟩ := (forcing_truth (M.nameDomain s) H generic
    supportedCertificateFamilyFormula env).1 truth
  obtain ⟨q, hq, qp, qr⟩ := H.directed hp hr
  exact ⟨q, hq, qp, forces_mono (M.nameDomain s) supportedCertificateFamilyFormula env forced qr⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation L)
variable (T : ZFSet.{u}) (K : L → Subgroup G)
private theorem actual_certificate (nodeOrder J k : ZFSet.{u})
    (validJ : ∀ z ∈ J, IsName s z) (H : ConditionFilter P) (z : Name s)
    (F B f : ZFSet.{u})
    (selected : k ⊆ M.supportedCertificateFamilyRelation a s b T K nodeOrder J validJ H)
    (entry : ZFSet.pair z.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k) :
    SupportedEqualityCertificate b.carrier (M.niceSupportNameCodes a s T K) nodeOrder
      (M.niceSupportRelation a s b T K)
      (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T K))
      (Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T K))
      (Name.eval {p | H.mem p} z) F B f := by
  obtain ⟨_, _, _, _, value, evaluated, certificate⟩ :=
    (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 (selected entry)
  have equal := (Name.inputEvaluationName_entry s J validJ z H value).1 evaluated
  exact equal.2.symm ▸ certificate

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (omega : ZFSet.omega ∈ M.sets)

theorem forces_supportedCertificateFamily_profile (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (small : M.sets.Countable)
    (z : (M.nameDomain s).names) (F B f : ZFSet.{u})
    (q : P) (forced : Forces (M.nameDomain s) supportedCertificateFamilyFormula
      (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
        carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) q)
    (entry : ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k)
    (hF : F ∈ M.sets) : M.DecidesVisibilityProfile a s b K T F z.val q := by
  apply (M.forces_visibilityProfile_iff a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid small F hF z q).1
  apply (M.ordinaryForces_iff_all_generics s small carrier visibilityProfileFormula
    (M.visibilityProfileEnv a s t b K pairing unions powers separation collection
      carrier group nodes supports maps hT valid F hF z) q).2
  intro H hq generic
  have truth := forces_sound (M.nameDomain s) H generic supportedCertificateFamilyFormula
    (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
      carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) hq forced
  have selected := (M.realize_supportedCertificateFamilyEnv a s t b T K pairing unions powers
    separation collection carrier group nodes supports maps hT valid omega nodeOrder J k
    hOrder hJ hk validJ H).1 truth
  have certificate := actual_certificate M a s b T K nodeOrder J k validJ H z.val F B f selected entry
  apply (M.realize_visibilityProfileEnv a s t b K pairing unions powers separation collection
    carrier group nodes supports maps hT valid F hF z H).2
  intro v
  exact certificate.2.2.2.2.1 (b.encode v)
    (Name.eval {p | H.mem p} (M.niceVisibilityName a s T (K v)))
    ((M.niceVisibilityEvaluationName_entry a s b T K H v _).2 rfl) (b.encode_mem v)

theorem forces_supportedCertificateFamily_equality (nodeOrder J k : ZFSet.{u})
    (hOrder : nodeOrder ∈ M.sets) (hJ : J ∈ M.sets) (hk : k ∈ M.sets)
    (validJ : ∀ z ∈ J, IsName s z) (small : M.sets.Countable)
    (z : (M.nameDomain s).names) (F B f : ZFSet.{u})
    (q : P) (forced : Forces (M.nameDomain s) supportedCertificateFamilyFormula
      (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
        carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) q)
    (entry : ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k)
    (v : ZFSet.{u}) (hv : v ∈ B) (tau : Name s)
    (ht : tau.val ∈ M.niceSupportNameCodes a s T K)
    (selectedEntry : ZFSet.pair v tau.val ∈ f) : Name.ForcesEq q z.val tau := by
  let named : (M.nameDomain s).names :=
    ⟨tau, ((M.mem_niceSupportNameCodes a s T K tau.val).1 ht).1⟩
  change Forces (M.nameDomain s) (.equal 0 1 : SetFormula 2) ![z, named] q
  apply (M.ordinaryForces_iff_all_generics s small carrier (.equal 0 1) ![z, named] q).2
  intro H hq generic
  have truth := forces_sound (M.nameDomain s) H generic supportedCertificateFamilyFormula
    (M.supportedCertificateFamilyEnv a s t b T K pairing unions powers separation collection
      carrier group nodes supports maps hT valid omega nodeOrder J k hOrder hJ hk validJ) hq forced
  have selected := (M.realize_supportedCertificateFamilyEnv a s t b T K pairing unions powers
    separation collection carrier group nodes supports maps hT valid omega nodeOrder J k
    hOrder hJ hk validJ H).1 truth
  have certificate := actual_certificate M a s b T K nodeOrder J k validJ H z.val F B f selected entry
  have result := certificate.2.2.2.2.2 v hv tau.val ht selectedEntry
  exact ((M.niceSupportEvaluationName_entry a s T K tau ht H _).1 result.2).symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSupportedCertificateProfiles
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem SupportedEqualityCertificate.basis_nonempty
    {nodes N order R niceEval visibilityEval value F B f : ZFSet.{u}}
    (certificate : SupportedEqualityCertificate nodes N order R niceEval visibilityEval value F B f)
    (nonempty : F.Nonempty) : B.Nonempty := by
  obtain ⟨v, hv⟩ := nonempty
  obtain ⟨w, hw, _⟩ := certificate.2.2.1 v hv
  exact ⟨w, hw⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

theorem supportedCertificate_profile_eq
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
    (d : PosetAction G L) (T : ZFSet.{u}) (H : ConditionFilter P)
    {N order R niceEval value F B f : ZFSet.{u}}
    (certificate : SupportedEqualityCertificate b.carrier N order R niceEval
      (Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T d.principalFix))
      value F B f) :
    F = M.visibleSupportProfile a s b d T H value := by
  have describes (v : L) :
      value ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) ↔
        b.encode v ∈ F :=
    certificate.2.2.2.2.1 (b.encode v) _
      ((M.niceVisibilityEvaluationName_entry a s b T d.principalFix H v _).2 rfl)
      (b.encode_mem v)
  apply ZFSet.ext
  intro x
  constructor
  · intro member
    obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (certificate.1 member)
    exact (M.encode_mem_visibleSupportProfile a s b d T H value v).2 ((describes v).2 member)
  · intro member
    obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (b.subset_carrier _ member)
    exact (describes v).1 ((M.encode_mem_visibleSupportProfile a s b d T H value v).1 member)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionEnumerations
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

theorem groundFunction_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {B N f : ZFSet.{u}} (hB : B ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets)
    (nonempty : B.Nonempty) (small : M.groundEmbeddable B ZFSet.omega)
    (function : ZFSet.IsFunc B N f) :
    ∃ e ∈ M.sets, ∃ names ∈ M.sets,
      ZFSet.IsFunc ZFSet.omega B e ∧ ZFSet.IsFunc ZFSet.omega N names ∧
      (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
      (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
        ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
      (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
        ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  obtain ⟨e, he, enumeration, onto⟩ := M.groundCountable_enumeration
    pairing unions powers separation infinite hB nonempty small
  let names := relationCompose ZFSet.omega B N e f
  have namesGround := M.relationCompose_mem pairing unions powers separation
    (M.omega_mem separation infinite) hB hN he hf
  have namesFunction : ZFSet.IsFunc ZFSet.omega N names :=
    relationCompose_function_of_subset enumeration function (fun _ member => member)
  refine ⟨e, he, names, namesGround, enumeration, namesFunction, onto, ?_, ?_⟩
  · intro n hn v tau nv nt
    obtain ⟨_, _, w, _, nw, wt⟩ := (pair_mem_relationCompose _ _ _ _ _ n tau).1 nt
    obtain ⟨chosen, _, unique⟩ := enumeration.2 n hn
    have equal : w = v := (unique w nw).trans (unique v nv).symm
    exact equal ▸ wt
  · intro n hn v tau nv vt
    have bound := ZFSet.pair_mem_prod.1 (function.1 vt)
    exact (pair_mem_relationCompose _ _ _ _ _ n tau).2 ⟨hn, bound.2, v, bound.1, nv, vt⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalEnumeratedCertificateFamilies
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
variable {Q : Type u} [PartialOrder Q] [OrderTop Q] (s : Presentation Q)

theorem exists_forcedSupportedCertificateFamily_oai
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (small : M.sets.Countable) (closed : InternallyCountablyClosed M s)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let b := SetMembers.presentation geometry.carrier
    let t := SetMembers.presentation geometry.actors
    let d := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    ∀ (a : PosetAction (SetMembers geometry.actors) Q)
      (_maps : a.conditionMapFamily s t ∈ M.sets)
      (T : ZFSet.{u}) (_hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
      (_terms : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
      (_children : ∀ τ : Name s, τ.val ∈ T →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ)
      (H : ConditionFilter Q) (_genericCoded : H.GenericFor (M.codedFamily s))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain s)))
      (_descent : ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain s).names),
        d.principalFix v ≤ a.stabilizer s x.val →
        d.principalFix w ≤ a.stabilizer s y.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) x.val →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) y.val →
        Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
        ∃ τ : (M.nameDomain s).names,
          HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) τ.val ∧
          d.principalFix (geometry.meet.smallMeet v w) ≤ a.stabilizer s τ.val ∧
          Name.eval {p | H.mem p} τ.val = Name.eval {p | H.mem p} x.val)
      (J : ZFSet.{u}) (_hJ : J ∈ M.sets) (validJ : ∀ z ∈ J, IsName s z)
      (_smallJ : M.groundEmbeddable J ZFSet.omega)
      (_hs : ∀ z : Name s, z.val ∈ J →
        HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) z)
      (_subset : ∀ z : Name s, z.val ∈ J → Name.eval {p | H.mem p} z ⊆
        Name.eval {p | H.mem p} (Name.familySet ⊤ T valid))
      (p : Q) (_hp : H.mem p),
      ∃ (k : ZFSet.{u}) (hk : k ∈ M.sets),
        ZFSet.IsFunc J (M.supportedEqualityCertificateBound b.carrier
          (M.niceSupportNameCodes a s T d.principalFix)) k ∧
        k ⊆ M.supportedCertificateFamilyRelation a s b T d.principalFix
          geometry.order J validJ H ∧
        ∃ q, H.mem q ∧ q ≤ p ∧
          Forces (M.nameDomain s) supportedCertificateFamilyFormula
            (M.supportedCertificateFamilyEnv a s t b T d.principalFix pairing unions powers
              separation collection carrier geometry.actors_ground geometry.carrier_ground
              (geometry.decoded_supportBasis_ground pairing unions powers separation)
              _maps _hT valid (M.omega_mem separation infinite) geometry.order J k
              geometry.order_ground _hJ hk validJ) q ∧
          ∀ (z : (M.nameDomain s).names) (F B f : ZFSet.{u}),
            ZFSet.pair z.val.val (ZFSet.pair F (ZFSet.pair B f)) ∈ k →
            F = M.visibleSupportProfile a s b d T H (Name.eval {p | H.mem p} z.val) ∧
            MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F ∧
            B.Nonempty ∧ M.DecidesVisibilityProfile a s b d.principalFix T F z.val q ∧
            (∀ v ∈ B, ∀ tau : Name s, tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
              ZFSet.pair v tau.val ∈ f → Name.ForcesEq q z.val tau) ∧
            ∃ e ∈ M.sets, ∃ names ∈ M.sets,
              ZFSet.IsFunc ZFSet.omega B e ∧
              ZFSet.IsFunc ZFSet.omega (M.niceSupportNameCodes a s T d.principalFix) names ∧
              (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
              (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
              (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
                ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let b := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  let d := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  dsimp only
  intro a maps T hT valid terms children H genericCoded genericFormula descent
    J hJ validJ smallJ hs subsets p hp
  have supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  have omega := M.omega_mem separation infinite
  have codesGround := M.niceSupportNameCodes_mem a s b T d.principalFix t pairing unions powers
    separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
  obtain ⟨k, hk, function, selected⟩ := fulfilled.exists_supportedCertificateFamily s collection
    infinite choice carrier order small closed smallD irreflexive a maps T hT valid terms children
    H genericCoded genericFormula descent J hJ validJ smallJ hs subsets
  obtain ⟨q, hq, qp, forced⟩ := M.exists_forced_supportedCertificateFamily a s t b T d.principalFix
    pairing unions powers separation collection carrier geometry.actors_ground geometry.carrier_ground
    supports maps hT valid omega geometry.order J k geometry.order_ground hJ hk validJ H
    genericFormula selected p hp
  refine ⟨k, hk, function, selected, q, hq, qp, forced, ?_⟩
  intro z F B f entry
  have bound := ZFSet.pair_mem_prod.1 (function.1 entry)
  have fields := (M.mem_supportedEqualityCertificateBound b.carrier
    (M.niceSupportNameCodes a s T d.principalFix) F B f).1 bound.2
  obtain ⟨_, _, _, _, value, evaluated, certificate⟩ :=
    (pair_mem_supportedCertificateRelation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).1 (selected entry)
  have valueEqual := (Name.inputEvaluationName_entry s J validJ z.val H value).1 evaluated
  have actual : SupportedEqualityCertificate b.carrier
      (M.niceSupportNameCodes a s T d.principalFix) geometry.order
      (M.niceSupportRelation a s b T d.principalFix)
      (Name.eval {p | H.mem p} (M.niceSupportEvaluationName a s T d.principalFix))
      (Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T d.principalFix))
      (Name.eval {p | H.mem p} z.val) F B f := valueEqual.2.symm ▸ certificate
  have profileEqual := M.supportedCertificate_profile_eq a s b d T H actual
  obtain ⟨_, profileFilter, _⟩ := fulfilled.exists_decided_visibilityProfile s collection infinite
    choice carrier order small closed smallD irreflexive a maps T hT valid terms children
    H genericCoded genericFormula descent z (hs z.val bound.1) (subsets z.val bound.1) p hp
  have filter : MeetFilterCode geometry.carrier geometry.order geometry.meetGraph F :=
    profileEqual.symm ▸ profileFilter
  have nonempty := actual.basis_nonempty filter.nonempty
  have decisions := M.forces_supportedCertificateFamily_profile a s t b T d.principalFix
    pairing unions powers separation collection carrier geometry.actors_ground geometry.carrier_ground
    supports maps hT valid omega geometry.order J k geometry.order_ground hJ hk validJ small
    z F B f q forced entry fields.1.1
  refine ⟨profileEqual, filter, nonempty, decisions, ?_, ?_⟩
  · intro v hv tau ht selectedEntry
    exact M.forces_supportedCertificateFamily_equality a s t b T d.principalFix pairing unions powers
      separation collection carrier geometry.actors_ground geometry.carrier_ground supports maps hT valid
      omega geometry.order J k geometry.order_ground hJ hk validJ small z F B f q forced entry
      v hv tau ht selectedEntry
  · exact M.groundFunction_enumeration pairing unions powers separation infinite fields.2.1.1
      codesGround fields.2.2.1 nonempty fields.2.1.2.2 actual.2.2.2.1

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_forcedSupportedCertificateFamily_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_forcedSupportedCertificateFamily_oai.{u, v}
