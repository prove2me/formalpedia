-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.countableRow_semanticStructuralTrace_jointZF_sequenceReflection
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:25:41.617209+00:00
-- url     : https://prove2.me/submissions/54422288-fa60-4a69-a0a9-c911a3b24f87

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompleteProjectionPredensity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section
universe u v
variable {Upper : Type u} {Lower : Type v} [PartialOrder Upper] [PartialOrder Lower]

namespace CompleteProjection
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)
include projection

theorem dense_preimage {E : Set Lower} (dense : Dense E) :
    Dense {p : Upper | restriction p ∈ E} := by
  intro p
  obtain ⟨q, below, member⟩ := dense (restriction p)
  obtain ⟨r, rp, equal⟩ := projection.lift p q below
  refine ⟨r, rp, ?_⟩
  change restriction r ∈ E
  rw [equal]
  exact member

theorem projectedFilter_mem_iff (H : ConditionFilter Upper) (q : Lower) :
    (projection.projectedFilter H).mem q ↔
      ∃ p : Upper, H.mem p ∧ restriction p = q := by
  constructor
  · intro member
    exact ⟨inclusion q, member, projection.retract q⟩
  · rintro ⟨p, member, rfl⟩
    exact H.upward member (projection.le_include_restriction p)

theorem projectedFilter_meets_iff (H : ConditionFilter Upper) (E : Set Lower) :
    (projection.projectedFilter H).Meets E ↔ H.Meets {p : Upper | restriction p ∈ E} := by
  constructor
  · rintro ⟨q, member, hq⟩
    obtain ⟨p, hp, rfl⟩ := (projection.projectedFilter_mem_iff H q).1 member
    exact ⟨p, hp, hq⟩
  · rintro ⟨p, member, hp⟩
    exact ⟨restriction p, (projection.projectedFilter_mem_iff H (restriction p)).2
      ⟨p, member, rfl⟩, hp⟩

theorem projectedFilter_generic (H : ConditionFilter Upper) (family : Set (Set Lower))
    (generic : H.GenericFor ((fun E : Set Lower => {p : Upper | restriction p ∈ E}) '' family)) :
    (projection.projectedFilter H).GenericFor family := by
  intro E member dense
  exact (projection.projectedFilter_meets_iff H E).2
    (generic _ ⟨E, member, rfl⟩ (projection.dense_preimage dense))

end CompleteProjection
end



end PartitionPilot.Forcing

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

theorem codedFamily_of_code {E : Set P} (code : s.subset E ∈ M.sets) : E ∈ M.codedFamily s := by
  refine ⟨s.subset E, code, ?_⟩
  apply Set.ext
  intro p
  exact s.encode_mem_subset E p

theorem symmetric_names_countable {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G) (small : M.sets.Countable) :
    (a.symmetricDomain s (M.nameDomain s) F).names.Countable :=
  (M.nameDomain_countable s small).mono (fun _ h => h.1)

end TransitiveGround



namespace TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u v w
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable (s : Presentation P) {G : Type w} [Group G]

theorem exists_joint_projection_generic (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets)
    {J : Type v} [Countable J] (Q : J → Type u) [∀ j, PartialOrder (Q j)]
    (t : ∀ j, Presentation (Q j)) (pi : ∀ j, P →o Q j) (inc : ∀ j, Q j ↪o P)
    (projection : ∀ j, CompleteProjection (pi j) (inc j)) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F)) ∧
      ∀ j, ((projection j).projectedFilter H).GenericFor (M.codedFamily (t j)) ∧
        ((projection j).projectedFilter H).GenericFor (formulaFamily (M.nameDomain (t j))) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  let projectedConditionsCountable (index : J) : Countable (Q index) :=
    (inc index).injective.countable
  let lower (j : J) : Set (Set (Q j)) :=
    M.codedFamily (t j) ∪ formulaFamily (M.nameDomain (t j))
  let lifted (j : J) : Set (Set P) :=
    (fun E : Set (Q j) => {q : P | pi j q ∈ E}) '' lower j
  have lowerCountable (j : J) : (lower j).Countable :=
    (M.codedFamily_countable (t j) small).union
      (formulaFamily_countable (M.nameDomain (t j)) (M.nameDomain_countable (t j) small))
  have liftedCountable : (⋃ j, lifted j).Countable :=
    Set.countable_iUnion (fun j => (lowerCountable j).image _)
  have ordinary := formulaFamily_countable (M.nameDomain s) (M.nameDomain_countable s small)
  have symmetric := formulaFamily_countable (a.symmetricDomain s (M.nameDomain s) F)
    (M.symmetric_names_countable s a F small)
  obtain ⟨H, hp, generic⟩ := exists_generic_for_countable_family p
    (M.codedFamily s ∪ (formulaFamily (M.nameDomain s) ∪
      (formulaFamily (a.symmetricDomain s (M.nameDomain s) F) ∪ ⋃ j, lifted j)))
    ((M.codedFamily_countable s small).union (ordinary.union (symmetric.union liftedCountable)))
  refine ⟨H, hp, (fun E hE => generic E (Or.inl hE)),
    (fun E hE => generic E (Or.inr (Or.inl hE))),
    (fun E hE => generic E (Or.inr (Or.inr (Or.inl hE)))), ?_⟩
  intro j
  have projected : ((projection j).projectedFilter H).GenericFor (lower j) :=
    (projection j).projectedFilter_generic H (lower j) (by
      intro E hE
      exact generic E (Or.inr (Or.inr (Or.inr (Set.mem_iUnion.2 ⟨j, hE⟩)))))
  exact ⟨(fun E hE => projected E (Or.inl hE)), fun E hE => projected E (Or.inr hE)⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_FinitePrincipalNameSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.PosetAction

open Compression.RecursiveMaps Compression.RecursiveMaps.CosetGeometry.OrderAction
universe u
variable {G I : Type u} [Group G] [PartialOrder I] (a : PosetAction G I)

theorem principalSupportFamily_basis (C : I) (directed : ∀ C D : I, ∃ E, C ≤ E ∧ D ≤ E)
    (H : Subgroup G) : (a.principalSupportFamily C directed).mem H ↔ ∃ D, a.principalFix D ≤ H := Iff.rfl

end PartitionPilot.Forcing.PosetAction



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableFunctionClosure
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing

open SetRealization
universe u

theorem groundSequenceUnion_extends {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) (n : Nat) :
    SetMembers.raw (seq n) ⊆ groundSequenceUnion seq :=
  fun _ hz => (mem_groundSequenceUnion seq _).2 ⟨n, hz⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem descending_function_union_partial (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      Antitone seq → PartialFunctionCode X Y (groundSequenceUnion seq) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq decreasing
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq z).1 hz
    exact (M.smallFunction_raw_properties X Y ZFSet.omega (seq n)).2.1.shape hn
  · intro x y z xy xz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq _).1 xy
    obtain ⟨m, hm⟩ := (mem_groundSequenceUnion seq _).1 xz
    have code := (M.smallFunction_raw_properties X Y ZFSet.omega (seq (max n m))).2.1
    exact code.unique x y z
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_left n m)) hn)
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_right n m)) hm)

theorem descending_function_union_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        groundSequenceUnion seq ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  obtain ⟨ground, small⟩ := M.countable_union_of_sequence_graph pairing unions powers separation infinite choice
    hQ (M.prod_mem pairing unions powers separation hX hY) graph
    (natPresentation.graph_isFunc (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega))
      (fun n => seq n.down))
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.1.shape)
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.2)
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨ground, M.descending_function_union_partial X Y seq decreasing, small⟩

theorem countable_function_lower_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        ∃ p, SetMembers.raw p = groundSequenceUnion seq ∧ ∀ n, p ≤ seq n := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have member := M.descending_function_union_mem pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  let p := SetMembers.ofMem (groundSequenceUnion seq) member
  have raw : SetMembers.raw p = groundSequenceUnion seq := SetMembers.raw_ofMem _ _
  refine ⟨p, raw, fun n => (M.smallFunction_le_iff X Y ZFSet.omega p (seq n)).2 ?_⟩
  rw [raw]
  exact groundSequenceUnion_extends seq n

theorem countable_function_internally_closed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    InternallyCountablyClosed M (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  obtain ⟨p, _, lower⟩ := M.countable_function_lower_bound pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  exact ⟨p, lower⟩

end TransitiveGround

end PartitionPilot.Forcing

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

end PartitionPilot.Forcing.TransitiveGround


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

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralPrefixPreparationInputs
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
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "Cuts" => {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ≤ stages}
local notation "lower" => (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier T (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hs hh ordinal trace infinite choice

theorem semanticStructuralTrace_jointZF (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
      M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
    let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
      (run).restriction ordinal j.property.2.1 j.property.2.2 c.conditionOrder_code
    let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
      (run).inclusion ordinal j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
        hs hPacked hT j.property.1 carrier rowTop topMem topRows mono c.conditionOrder_code
    let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
      M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace j.val j.property.1
        j.property.2.1 j.property.2.2 infinite choice
    let s := SetMembers.presentation Q
    let F := d.principalSupportFamily base directed
    ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
      H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily ((act).symmetricDomain s (M.nameDomain s) F)) ∧
      (∀ j : Cuts,
        ((projections j).projectedFilter H).GenericFor
          (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))) ∧
        ((projections j).projectedFilter H).GenericFor
          (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))))) ∧
      M.sets ⊆ ((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
      ZFRealization (((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
    M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let : Countable M.sets := small
  let intoGround : Cuts → M.sets := fun j => ⟨j.val, j.property.1⟩
  have injective : Function.Injective intoGround := by
    intro j k equal
    apply Subtype.ext
    exact congrArg (fun x : M.sets => x.val) equal
  let : Countable Cuts := injective.countable
  let s := SetMembers.presentation Q
  let F := d.principalSupportFamily base directed
  have hQ : s.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hOrder : s.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hs hPacked omega
  have hGraph : (act).actionGraph s t ∈ M.sets := by
    rw [M.semanticStructuralAction_graph]
    exact M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier rowAction group nodes nodeOrder nodeAction supports hT hT2 hs hh omega
  have maps := M.conditionMapFamily_mem_of_actionGraph (act) s t pairing unions powers separation
    collection hQ group hGraph
  dsimp only
  intro p
  obtain ⟨H, hp, ground, ordinary, symmetric, projected⟩ :=
    M.exists_joint_projection_generic s (act) F small hQ lower
      (fun j => SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))
      (fun j => (run).restriction ordinal j.property.2.1 j.property.2.2 c.conditionOrder_code)
      (fun j => (run).inclusion ordinal j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
        hs hPacked hT j.property.1 carrier rowTop topMem topRows mono c.conditionOrder_code)
      (fun j => M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace j.val j.property.1
        j.property.2.1 j.property.2.2 infinite choice) p
  exact ⟨H, hp, ground, ordinary, symmetric, projected,
    M.ground_subset_symmetric_values s (act) F pairing unions powers separation collection hQ H,
    M.symmetric_ZF (act) s t b F d.principalFix (d.principalSupportFamily_basis base directed)
      pairing unions powers separation collection infinite hQ hOrder group nodes supports maps H symmetric⟩

end PartitionPilot.Forcing.TransitiveGround




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
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "Cuts" => {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ≤ stages}
local notation "lower" => (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier T (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hs hh ordinal trace infinite choice

theorem semanticStructuralTrace_sequenceReflection
    (rowClosed : InternallyCountablyClosed M c) (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let s := SetMembers.presentation Q
    ∀ (H : ConditionFilter (SetMembers Q)),
      H.GenericFor (M.codedFamily s) →
      H.GenericFor (formulaFamily (M.nameDomain s)) →
      ∀ U ∈ M.sets,
        GroundSequenceReflection M (M.ordinaryExtension s H) U ∧
        GroundSequenceReflection M
          (M.symmetricExtension s (act) (d.principalSupportFamily base directed) H) U := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    (run).carriers ordinal carrier rowTop topMem topRows
  let s := SetMembers.presentation Q
  have hQ : s.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have hOrder : s.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hs hPacked omega
  have closed := M.semanticStructuralTrace_internally_closed c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice rowClosed
  dsimp only
  intro H coded ordinary U hU
  have reflection := M.ordinaryExtension_sequenceReflection s pairing unions powers separation
    collection infinite choice hQ hOrder small hU closed H coded ordinary
  refine ⟨reflection, ?_⟩
  intro f hf function
  exact reflection f
    (M.symmetricExtension_subset_ordinaryExtension s (act)
      (d.principalSupportFamily base directed) H hf) function

theorem semanticStructuralTrace_jointZF_sequenceReflection
    (rowClosed : InternallyCountablyClosed M c) (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
      M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
    let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
      (run).restriction ordinal j.property.2.1 j.property.2.2 c.conditionOrder_code
    let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
      (run).inclusion ordinal j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
        hs hPacked hT j.property.1 carrier rowTop topMem topRows mono c.conditionOrder_code
    let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
      M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace j.val j.property.1
        j.property.2.1 j.property.2.2 infinite choice
    let s := SetMembers.presentation Q
    let F := d.principalSupportFamily base directed
    ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
      H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily ((act).symmetricDomain s (M.nameDomain s) F)) ∧
      (∀ j : Cuts,
        ((projections j).projectedFilter H).GenericFor
          (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))) ∧
        ((projections j).projectedFilter H).GenericFor
          (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))))) ∧
      M.sets ⊆ ((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
      ZFRealization (((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) ∧
      (∀ U ∈ M.sets,
        GroundSequenceReflection M (M.ordinaryExtension s H) U ∧
        GroundSequenceReflection M (M.symmetricExtension s (act) F H) U) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
    M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
  dsimp only
  intro p
  obtain ⟨H, hp, coded, ordinary, symmetric, projected, contains, zf⟩ :=
    M.semanticStructuralTrace_jointZF c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace infinite choice small p
  refine ⟨H, hp, coded, ordinary, symmetric, projected, contains, zf, ?_⟩
  exact M.semanticStructuralTrace_sequenceReflection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice rowClosed small H coded ordinary

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableRowSequenceReflection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G L : Type u} [Group G] [PartialOrder L]
variable (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)






theorem countableRow_semanticStructuralTrace_jointZF_sequenceReflection_oai
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X : ZFSet.{u}) (hX : X ∈ M.sets) (small : M.sets.Countable) :
    letI := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
    let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
    ∀ (a : PosetAction G (SetMembers (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)))
      (T T2 rowTop : ZFSet.{u})
    (rowAction : a.actionGraph c t ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
    (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
    (topMem : rowTop ∈ c.carrier)
    (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history),
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
    let rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
    let omega := M.omega_mem separation infinite
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let Q := M.refinementHistoryForcing c.carrier T stages packed
    let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ stages}
    let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier T (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
      t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 ordinal trace
    let witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
    let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
      pairing unions powers separation collection group nodes supports hh hT witnesses
    let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
      ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
      (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
        (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    let act := M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace
    letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
      M.refinementHistoryPartialOrder c.conditionOrder_code T j.val (graphRestriction j.val packed)
    let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
      (run).restriction ordinal j.property.2.1 j.property.2.2 c.conditionOrder_code
    let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
      (run).inclusion ordinal j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
        hs hPacked hT j.property.1 carrier rowTop topMem topRows mono c.conditionOrder_code
    let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
      M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace j.val j.property.1
        j.property.2.1 j.property.2.2 infinite choice
    let s := SetMembers.presentation Q
    let F := d.principalSupportFamily base directed
    ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
      H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily ((act).symmetricDomain s (M.nameDomain s) F)) ∧
      (∀ j : Cuts,
        ((projections j).projectedFilter H).GenericFor
          (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))) ∧
        ((projections j).projectedFilter H).GenericFor
          (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier T j.val (graphRestriction j.val packed)))))) ∧
      M.sets ⊆ ((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
      ZFRealization (((act).symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) ∧
      (∀ U ∈ M.sets,
        GroundSequenceReflection M (M.ordinaryExtension s H) U ∧
        GroundSequenceReflection M (M.symmetricExtension s (act) F H) U) := by
  let := M.smallFunctionOrder X (natSetCode 2) ZFSet.omega
  let c := SetMembers.presentation (M.smallPartialFunctions X (natSetCode 2) ZFSet.omega)
  dsimp only
  intro a T T2 rowTop rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows stages history hs hh ordinal trace
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite hX two
  have rowOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite hX two
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation infinite choice hX two
  exact M.semanticStructuralTrace_jointZF_sequenceReflection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 (M.omega_mem separation infinite) valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace infinite choice rowClosed small

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.countableRow_semanticStructuralTrace_jointZF_sequenceReflection_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.countableRow_semanticStructuralTrace_jointZF_sequenceReflection_oai.{u}
