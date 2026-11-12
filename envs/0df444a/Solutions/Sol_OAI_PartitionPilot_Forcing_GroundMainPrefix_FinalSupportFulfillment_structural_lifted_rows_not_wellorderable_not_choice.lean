-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_lifted_rows_not_wellorderable_not_choice
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:32:21.336252+00:00
-- url     : https://prove2.me/submissions/d35ee7eb-f790-4d22-81e1-c43d7a32eb30

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_dense_mixture_equalities
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_support_prepared_strengthening
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_binaryRowStructuralAssignmentImage_dataBound
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_aligned_copy_crossCollisions

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
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



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

theorem eval_rename (t : Presentation Q) (f : P → Q) (H : Set Q) (τ : Name s) :
    eval H (rename t f τ) = eval {p | f p ∈ H} τ := by
  induction τ using inductionOn with
  | step τ ih =>
    apply ZFSet.ext
    intro x
    rw [mem_eval, mem_eval]
    constructor
    · rintro ⟨ν, q, h, hq, eq⟩
      obtain ⟨σ, p, hp, rfl, rfl⟩ := (entry_rename t f τ ν q).1 h
      exact ⟨σ, p, hp, hq, (ih σ p hp).symm.trans eq⟩
    · rintro ⟨σ, p, hp, hq, eq⟩
      exact ⟨rename t f σ, f p,
        (entry_rename t f τ _ _).2 ⟨σ, p, hp, rfl, rfl⟩,
        hq, (ih σ p hp).trans eq⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NameMixingRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

theorem entry_nameRank_lt {σ τ : Name s} {p : P} (h : Entry σ τ p) :
    nameRank σ < nameRank τ :=
  ZFSet.rank_lt_of_mem ((mem_eval Set.univ τ _).2 ⟨σ, p, h, Set.mem_univ _, rfl⟩)

theorem nameRank_rename (t : Presentation Q) (f : P → Q) (τ : Name s) :
    nameRank (rename t f τ) = nameRank τ := by
  unfold nameRank
  rw [eval_rename]
  rfl

theorem rank_eval_le (H : Set P) (τ : Name s) : ZFSet.rank (eval H τ) ≤ nameRank τ := by
  induction τ using inductionOn with
  | step τ ih =>
    rw [ZFSet.rank_le_iff]
    intro x hx
    obtain ⟨σ, p, entry, _, rfl⟩ := (mem_eval H τ x).1 hx
    exact (ih σ p entry).trans_lt (entry_nameRank_lt entry)

end PartitionPilot.Forcing.Name



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] [Small.{u} G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem entry_mix (K : Subgroup G) (p : P) (τ σ : Name s) (q : P) :
    Name.Entry σ (a.mix s K p τ) q ↔
      ∃ g ∈ K, ∃ ν r, Name.Entry ν τ r ∧ a.act s g ν = σ ∧
        q ≤ a.iso g p ∧ q ≤ a.iso g r := by
  rw [mix, Name.entry_assemble]
  constructor
  · rintro ⟨z, eq, rfl⟩
    exact ⟨z.val.1.val, z.val.1.property, z.val.2.1.val.1, z.val.2.1.val.2,
      z.val.2.1.property, eq, z.property⟩
  · rintro ⟨g, hg, ν, r, entry, eq, lower⟩
    exact ⟨⟨(⟨g, hg⟩, ⟨(ν, r), entry⟩, q), lower⟩, eq, rfl⟩

theorem mix_entry_translated (K : Subgroup G) (p : P) (τ : Name s)
    {σ : Name s} {q : P} (entry : Name.Entry σ (a.mix s K p τ) q)
    {h : G} (hh : h ∈ K) :
    Name.Entry (a.act s h σ) (a.mix s K p τ) (a.iso h q) := by
  obtain ⟨g, hg, ν, r, old, eq, qp, qr⟩ := (a.entry_mix s K p τ σ q).1 entry
  apply (a.entry_mix s K p τ _ _).2
  refine ⟨h * g, K.mul_mem hh hg, ν, r, old, ?_, ?_, ?_⟩
  · rw [a.act_mul, eq]
  · rw [a.mul]
    exact (a.iso h).monotone qp
  · rw [a.mul]
    exact (a.iso h).monotone qr

theorem mix_fixed (K : Subgroup G) (p : P) (τ : Name s) {g : G} (hg : g ∈ K) :
    a.act s g (a.mix s K p τ) = a.mix s K p τ := by
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename s (a.iso g) (a.mix s K p τ)) q ↔ _
  rw [Name.entry_rename]
  constructor
  · rintro ⟨ν, r, entry, eq, hr⟩
    change a.act s g ν = σ at eq
    have h := a.mix_entry_translated s K p τ entry hg
    simpa only [eq, hr] using h
  · intro entry
    have moved := a.mix_entry_translated s K p τ entry (K.inv_mem hg)
    refine ⟨a.act s g⁻¹ σ, a.iso g⁻¹ q, moved, a.act_inv_right s g σ, ?_⟩
    rw [← a.mul, mul_inv_cancel, a.one]

end PartitionPilot.Forcing.PosetAction


namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem nameRank_act (g : G) (τ : Name s) :
    Name.nameRank (a.act s g τ) = Name.nameRank τ :=
  Name.nameRank_rename s (a.iso g) τ

end PartitionPilot.Forcing.PosetAction

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPartialFunctionSpaces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

namespace PartialFunctionCode

theorem union {X Y p q : ZFSet.{u}} (hp : PartialFunctionCode X Y p) (hq : PartialFunctionCode X Y q)
    (agree : ∀ x y z, ZFSet.pair x y ∈ p → ZFSet.pair x z ∈ q → y = z) :
    PartialFunctionCode X Y (p ∪ q) := by
  refine ⟨fun _ hz => (ZFSet.mem_union.1 hz).elim (fun h => hp.shape h) (fun h => hq.shape h), ?_⟩
  intro x y z hy hz
  rcases ZFSet.mem_union.1 hy with hy | hy
  · rcases ZFSet.mem_union.1 hz with hz | hz
    · exact hp.unique x y z hy hz
    · exact agree x y z hy hz
  · rcases ZFSet.mem_union.1 hz with hz | hz
    · exact (agree x z y hz hy).symm
    · exact hq.unique x y z hy hz

end PartialFunctionCode

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_UniqueFiberForcing
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

theorem truth_uniqueFiberFormula {n} (s x f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (uniqueFiberFormula s x f) env ↔ env x ∈ env s ∧
      ZFSet.pair (env s) (env x) ∈ env f ∧
      ∀ z ∈ env s, ZFSet.pair (env s) z ∈ env f → z = env x := by
  simp only [uniqueFiberFormula, Truth, truth_pairMembershipFormula, truth_imp]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.SetFormula

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem realize_uniqueFiber_values (D : Name.NameDomain s) (H : Set P)
    {n} (i j k : Fin n) (env : Assignment D n) :
    Realize (D.values H) (BoundedFormula.uniqueFiberFormula i j k).toFormula (evalAssignment H env) ↔
      Name.eval H (env j).val ∈ Name.eval H (env i).val ∧
      ZFSet.pair (Name.eval H (env i).val) (Name.eval H (env j).val) ∈ Name.eval H (env k).val ∧
      ∀ z ∈ Name.eval H (env i).val,
        ZFSet.pair (Name.eval H (env i).val) z ∈ Name.eval H (env k).val →
          z = Name.eval H (env j).val := by
  let N : TransitiveGround := ⟨D.values H, D.values_transitive H⟩
  exact (BoundedFormula.realize_toFormula N _ _ (fun l => ⟨env l, rfl⟩)).trans
    (BoundedFormula.truth_uniqueFiberFormula i j k (evalAssignment H env))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.PosetAction

open SetRealization SetFormula
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

theorem uniqueFiber_eq_of_fixed_names (a : PosetAction G P) (s : Presentation P)
    (D : Name.NameDomain s) (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (g : G) (S x f : D.names)
    (fixedS : a.act s g S.val = S.val) (fixedF : a.act s g f.val = f.val)
    (p : P)
    (forced : Forces D (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula
      (extend S (extend x (extend f Fin.elim0))) p)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily D))
    (hp : H.mem p) (hgp : H.mem (a.iso g p)) :
    Name.eval {q | H.mem q} x.val = Name.eval {q | H.mem q} (a.act s g x.val) := by
  let env := extend S (extend x (extend f Fin.elim0))
  have original := (realize_uniqueFiber_values D {q | H.mem q} 0 1 2 env).1
    (forces_sound D H generic _ env hp forced)
  have moved := (a.formula_forces_act_iff s D closed g
    (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula env p).2 forced
  have translated := (realize_uniqueFiber_values D {q | H.mem q} 0 1 2
    (a.actAssignment s D closed g env)).1
    (forces_sound D H generic _ _ hgp moved)
  change Name.eval {q | H.mem q} (a.act s g x.val) ∈ Name.eval {q | H.mem q} (a.act s g S.val) ∧
    ZFSet.pair (Name.eval {q | H.mem q} (a.act s g S.val))
      (Name.eval {q | H.mem q} (a.act s g x.val)) ∈ Name.eval {q | H.mem q} (a.act s g f.val) ∧ _
    at translated
  rw [fixedS, fixedF] at translated
  exact (original.2.2 _ translated.1 translated.2.1).symm

end PartitionPilot.Forcing.PosetAction

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

end CompleteProjection
end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundPresentedPreimages
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {P Q : Type u} (s : Presentation P) (t : Presentation Q) (f : P → Q)

theorem preimageCode_eq (X : ZFSet.{u}) :
    s.subset (fun point => t.encode (f point) ∈ X) =
      relationImage X s.carrier (relationConverse s.carrier t.carrier (s.graph t f)) := by
  apply ZFSet.ext
  intro z
  rw [s.mem_subset, mem_relationImage]
  constructor
  · rintro ⟨p, member, rfl⟩
    exact ⟨s.encode_mem p, t.encode (f p), member,
      (pair_mem_relationConverse _ _ _ _ _).2
        ⟨s.encode_mem p, t.encode_mem (f p), (s.pair_mem_graph t f p (f p)).2 rfl⟩⟩
  · rintro ⟨_, y, member, entry⟩
    have raw := (pair_mem_relationConverse _ _ _ _ _).1 entry
    obtain ⟨p, equal⟩ := (s.mem_graph t f _).1 raw.2.2
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    exact ⟨p, by rw [right]; exact member, left⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u}

theorem presentedPreimage_mem (s : Presentation P) (t : Presentation Q) (f : P → Q)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets) (graph : s.graph t f ∈ M.sets)
    {X : ZFSet.{u}} (hX : X ∈ M.sets) :
    s.subset (fun point => t.encode (f point) ∈ X) ∈ M.sets := by
  rw [s.preimageCode_eq t f X]
  exact M.relationImage_mem separation hX hs
    (M.relationConverse_mem pairing unions powers separation hs ht graph)

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

theorem codedFamily_countable (small : M.sets.Countable) : (M.codedFamily s).Countable :=
  small.image _

theorem codedFamily_of_code {E : Set P} (code : s.subset E ∈ M.sets) : E ∈ M.codedFamily s := by
  refine ⟨s.subset E, code, ?_⟩
  apply Set.ext
  intro p
  exact s.encode_mem_subset E p

theorem generic_meets_coded_dense [Preorder P] (H : ConditionFilter P)
    (generic : H.GenericFor (M.codedFamily s)) {E : Set P}
    (code : s.subset E ∈ M.sets) (dense : Dense E) : H.Meets E :=
  generic E (M.codedFamily_of_code s code) dense

theorem symmetric_names_countable {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G) (small : M.sets.Countable) :
    (a.symmetricDomain s (M.nameDomain s) F).names.Countable :=
  (M.nameDomain_countable s small).mono (fun _ h => h.1)

theorem exists_joint_generic {G : Type v} [Group G] [PartialOrder P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F)) := by
  let conditionsCountable : Countable P := M.conditions_countable s small carrier
  have ordinary := formulaFamily_countable (M.nameDomain s) (M.nameDomain_countable s small)
  have symmetric := formulaFamily_countable (a.symmetricDomain s (M.nameDomain s) F)
    (M.symmetric_names_countable s a F small)
  obtain ⟨H, hp, generic⟩ := exists_generic_for_countable_family p
    (M.codedFamily s ∪ (formulaFamily (M.nameDomain s) ∪
      formulaFamily (a.symmetricDomain s (M.nameDomain s) F)))
    ((M.codedFamily_countable s small).union (ordinary.union symmetric))
  exact ⟨H, hp, (fun E hE => generic E (Or.inl hE)),
    (fun E hE => generic E (Or.inr (Or.inl hE))),
    fun E hE => generic E (Or.inr (Or.inr hE))⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NamePresentationEquivalences
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small _root_.OAI.PartitionPilot.Forcing.Name.unionIndices_small _root_.OAI.PartitionPilot.Forcing.PosetAction.mixIndices_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
universe u
variable {P : Type u} (s : Presentation P)

theorem encode_intoSet (B : ZFSet.{u}) (sub : s.carrier ⊆ B) (p : P) :
    (SetMembers.presentation B).encode (s.intoSet B sub p) = s.encode p :=
  SetMembers.raw_ofMem _ _

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.PosetAction
open SetRealization
universe u v
variable {P : Type u} {G : Type v} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s t : Presentation P)

theorem act_presentationEquiv (g : G) (τ : Name s) :
    a.act t g (Name.presentationEquiv s t τ) = Name.presentationEquiv s t (a.act s g τ) := by
  change Name.rename t (a.iso g) (Name.rename t id τ) =
    Name.rename t id (Name.rename s (a.iso g) τ)
  rw [Name.rename_comp, Name.rename_comp]
  rfl

theorem stabilizer_presentationEquiv (τ : Name s) :
    a.stabilizer t (Name.presentationEquiv s t τ) = a.stabilizer s τ := by
  apply Subgroup.ext
  intro g
  change a.act t g (Name.presentationEquiv s t τ) = Name.presentationEquiv s t τ ↔ a.act s g τ = τ
  rw [a.act_presentationEquiv]
  exact (Name.presentationEquiv s t).injective.eq_iff

end PartitionPilot.Forcing.PosetAction

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
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem mem_immediateChildCodes (τ : Name s) (y : ZFSet.{u}) :
    y ∈ immediateChildCodes τ ↔ ∃ σ : Name s, ∃ p, Entry σ τ p ∧ y = σ.val := by
  rw [immediateChildCodes, mem_relationImage]
  constructor
  · rintro ⟨_, q, _, entry⟩
    have raw := ((pair_mem_relationConverse _ _ _ y q).1 entry).2.2
    obtain ⟨σ, p, shape⟩ := entries_cover τ raw
    refine ⟨σ, p, ?_, (ZFSet.pair_inj.1 shape).1⟩
    change ZFSet.pair σ.val (s.encode p) ∈ τ.val
    rw [← shape]
    exact raw
  · rintro ⟨σ, p, entry, rfl⟩
    have bound := child_mem_doubleUnion entry
    exact ⟨bound, s.encode p, s.encode_mem p,
      (pair_mem_relationConverse _ _ _ _ _).2 ⟨bound, s.encode_mem p, entry⟩⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem immediateChildCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (τ : Name s) (ground : τ.val ∈ M.sets) :
    Name.immediateChildCodes τ ∈ M.sets := by
  have bound := M.union_mem unions (M.union_mem unions ground)
  exact M.relationImage_mem separation carrier bound
    (M.relationConverse_mem pairing unions powers separation bound carrier ground)

end PartitionPilot.Forcing.TransitiveGround

end


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

theorem check_code_eq {P : Type u} (s : Presentation P) (one : P) (x : ZFSet.{u}) :
    (check s one x).val = checkNameCode (s.encode one) x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    change z ∈ (check s one x).val ↔ z ∈ (check (checkCodePresentation (s.encode one)) ⟨()⟩ x).val
    rw [mem_check_code, mem_check_code]
    apply exists_congr
    intro y
    apply and_congr_right
    intro hy
    rw [ih y hy]
    rfl

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



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mixtureTermCodes_mem (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (ground : τ.val ∈ M.sets) :
    M.mixtureTermCodes a s τ ∈ M.sets :=
  M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps _
    (M.immediateChildCodes_mem s pairing unions powers separation carrier τ ground)

theorem mixtureTermCodes_valid (τ : Name s) :
    ∀ y ∈ M.mixtureTermCodes a s τ, IsName s y := by
  intro y member
  obtain ⟨g, σ, _, _, rfl⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) y).1 member
  exact (a.act s g σ).property

theorem mixtureTermCodes_hs (F : NormalSubgroupFamily G) (τ : Name s)
    (hs : HereditarilySymmetric a s F τ) (ψ : Name s)
    (member : ψ.val ∈ M.mixtureTermCodes a s τ) : HereditarilySymmetric a s F ψ := by
  obtain ⟨g, σ, _, child, equal⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) ψ.val).1 member
  obtain ⟨ν, p, entry, childEqual⟩ := (Name.mem_immediateChildCodes τ σ.val).1 child
  have source : σ = ν := Subtype.ext childEqual
  subst σ
  have moved : ψ = a.act s g ν := Subtype.ext equal
  rw [moved]
  exact (hs.member entry).translated g

theorem mixtureTermCodes_rank (τ ψ : Name s)
    (member : ψ.val ∈ M.mixtureTermCodes a s τ) : Name.nameRank ψ < Name.nameRank τ := by
  obtain ⟨g, σ, _, child, equal⟩ :=
    (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) ψ.val).1 member
  obtain ⟨ν, p, entry, childEqual⟩ := (Name.mem_immediateChildCodes τ σ.val).1 child
  have source : σ = ν := Subtype.ext childEqual
  subst σ
  have moved : ψ = a.act s g ν := Subtype.ext equal
  rw [moved, a.nameRank_act]
  exact Name.entry_nameRank_lt entry

theorem mix_subset_mixtureTermCodes (τ : Name s) (ground : τ.val ∈ M.sets)
    (K : Subgroup G) (p : P) :
    (a.mix s K p τ).val ⊆ ZFSet.prod (M.mixtureTermCodes a s τ) s.carrier := by
  intro z member
  obtain ⟨σ, q, rfl⟩ := Name.entries_cover (a.mix s K p τ) member
  obtain ⟨g, _, ν, r, entry, rfl, _, _⟩ := (a.entry_mix s K p τ σ q).1 member
  refine ZFSet.pair_mem_prod.2 ⟨?_, s.encode_mem q⟩
  exact (a.mem_orbitCodes s (M.nameDomain s) (Name.immediateChildCodes τ) _).2
    ⟨g, ν, (M.nameDomain s).children ground entry,
      (Name.mem_immediateChildCodes τ ν.val).2 ⟨ν, r, entry, rfl⟩, rfl⟩

end PartitionPilot.Forcing.TransitiveGround

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

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem entry_restrictBelow (p : P) (τ σ : Name s) (q : P) :
    Entry σ (restrictBelow p τ) q ↔ ∃ r, Entry σ τ r ∧ q ≤ r ∧ q ≤ p :=
  entry_selectName _ τ σ q

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_restrictionEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets restrictionEntryFormula (extend z (extend τ.val (extend (s.encode p)
      (extend s.carrier (extend s.conditionOrder Fin.elim0))))) ↔
      z ∈ (Name.restrictBelow p τ).val := by
  let base := extend z (extend τ.val (extend (s.encode p) (extend s.carrier (extend s.conditionOrder Fin.elim0))))
  have hp := M.transitive carrier (s.encode_mem p)
  rw [restrictionEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨q, rest⟩ := (M.realize_exConditions s 4 _ (extend x base) carrier rfl).1 rest
    obtain ⟨r, shape, old, qr, qp⟩ := (M.realize_exConditions s 5 _
      (extend (s.encode q) (extend x base)) carrier rfl).1 rest
    let e := extend (s.encode r) (extend (s.encode q) (extend x base))
    have hq := M.transitive carrier (s.encode_mem q)
    have hr := M.transitive carrier (s.encode_mem r)
    have raw := (M.realize_pairMembershipFormula pairing 2 0 4 e hx hr hτ).1 old
    let σ : Name s := ⟨x, Name.isName_of_pair_mem τ x r raw⟩
    have eq := (M.realize_orderedPairFormula pairing 3 2 1 e hz hx hq).1 shape
    change z = ZFSet.pair x (s.encode q) at eq
    rw [eq]
    exact (Name.entry_restrictBelow p τ σ q).2 ⟨r, raw,
      (M.realize_conditionLE s pairing carrier order 1 0 7 e q r rfl rfl rfl).1 qr,
      (M.realize_conditionLE s pairing carrier order 1 5 7 e q p rfl rfl rfl).1 qp⟩
  · intro member
    obtain ⟨σ, q, eq⟩ := Name.entries_cover (Name.restrictBelow p τ) member
    have entry : Name.Entry σ (Name.restrictBelow p τ) q := by
      change ZFSet.pair σ.val (s.encode q) ∈ (Name.restrictBelow p τ).val
      rwa [← eq]
    obtain ⟨r, old, qr, qp⟩ := (Name.entry_restrictBelow p τ σ q).1 entry
    have hσ := (M.nameDomain s).children hτ old
    refine ⟨σ.val, hσ, ?_⟩
    apply (M.realize_exConditions s 4 _ (extend σ.val base) carrier rfl).2
    refine ⟨q, ?_⟩
    apply (M.realize_exConditions s 5 _ (extend (s.encode q) (extend σ.val base)) carrier rfl).2
    let e := extend (s.encode r) (extend (s.encode q) (extend σ.val base))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing 3 2 1 e hz hσ (M.transitive carrier (s.encode_mem q))).2 eq
    · exact (M.realize_pairMembershipFormula pairing 2 0 4 e hσ (M.transitive carrier (s.encode_mem r)) hτ).2 old
    · exact (M.realize_conditionLE s pairing carrier order 1 0 7 e q r rfl rfl rfl).2 qr
    · exact (M.realize_conditionLE s pairing carrier order 1 5 7 e q p rfl rfl rfl).2 qp

theorem restrictBelow_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) : (Name.restrictBelow p τ).val ∈ M.sets := by
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers
    (M.union_mem unions (M.union_mem unions hτ)) carrier
  have bound : (Name.restrictBelow p τ).val ⊆ B := by
    intro z hz
    obtain ⟨σ, q, rfl⟩ := Name.entries_cover (Name.restrictBelow p τ) hz
    obtain ⟨r, old, _, _⟩ := (Name.entry_restrictBelow p τ σ q).1 hz
    exact pairBound σ.val (Name.child_mem_doubleUnion old) (s.encode q) (s.encode_mem q)
  let context := extend τ.val (extend (s.encode p) (extend s.carrier (extend s.conditionOrder Fin.elim0)))
  have selected := M.separation_mem separation restrictionEntryFormula context
    (Fin.cases hτ (Fin.cases (M.transitive carrier (s.encode_mem p))
      (Fin.cases carrier (Fin.cases order (fun i => Fin.elim0 i))))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets restrictionEntryFormula (extend z context)) B =
      (Name.restrictBelow p τ).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_restrictionEntryFormula s pairing carrier order p τ hτ z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (M.realize_restrictionEntryFormula s pairing carrier order p τ hτ z
        (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.PosetAction

open SetRealization
universe u
variable {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mem_subgroupOrbitCodes (K : Subgroup G) (τ : Name s) (y : ZFSet.{u}) :
    y ∈ a.subgroupOrbitCodes s K τ ↔ ∃ g ∈ K, y = (a.act s g τ).val := by
  rw [subgroupOrbitCodes, ZFSet.mem_range]
  constructor
  · rintro ⟨g, eq⟩
    exact ⟨g.val, g.property, eq.symm⟩
  · rintro ⟨g, hg, eq⟩
    exact ⟨⟨g, hg⟩, eq.symm⟩

theorem entry_act_restrictBelow (g : G) (p : P) (τ σ : Name s) (q : P) :
    Name.Entry σ (a.act s g (Name.restrictBelow p τ)) q ↔
      ∃ ν r, Name.Entry ν τ r ∧ a.act s g ν = σ ∧ q ≤ a.iso g p ∧ q ≤ a.iso g r := by
  change Name.Entry σ (Name.rename s (a.iso g) (Name.restrictBelow p τ)) q ↔ _
  rw [Name.entry_rename]
  constructor
  · rintro ⟨ν, c, entry, eq, cq⟩
    obtain ⟨r, old, cr, cp⟩ := (Name.entry_restrictBelow p τ ν c).1 entry
    refine ⟨ν, r, old, eq, ?_, ?_⟩
    · rw [← cq]
      exact (a.iso g).monotone cp
    · rw [← cq]
      exact (a.iso g).monotone cr
  · rintro ⟨ν, r, old, eq, qp, qr⟩
    refine ⟨ν, (a.iso g).symm q, (Name.entry_restrictBelow p τ ν _).2 ⟨r, old, ?_, ?_⟩,
      eq, (a.iso g).apply_symm_apply q⟩
    · exact (a.iso g).le_iff_le.1 (by simpa only [OrderIso.apply_symm_apply] using qr)
    · exact (a.iso g).le_iff_le.1 (by simpa only [OrderIso.apply_symm_apply] using qp)

theorem mix_code_union (K : Subgroup G) (p : P) (τ : Name s) :
    (a.mix s K p τ).val = ⋃₀ (a.subgroupOrbitCodes s K (Name.restrictBelow p τ)) := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sUnion]
  constructor
  · intro hz
    obtain ⟨σ, q, eq⟩ := Name.entries_cover (a.mix s K p τ) hz
    have entry : Name.Entry σ (a.mix s K p τ) q := by
      change ZFSet.pair σ.val (s.encode q) ∈ (a.mix s K p τ).val
      rwa [← eq]
    obtain ⟨g, hg, ν, r, old, moved, qp, qr⟩ := (a.entry_mix s K p τ σ q).1 entry
    refine ⟨(a.act s g (Name.restrictBelow p τ)).val,
      (a.mem_subgroupOrbitCodes s K _ _).2 ⟨g, hg, rfl⟩, ?_⟩
    rw [eq]
    exact (a.entry_act_restrictBelow s g p τ σ q).2 ⟨ν, r, old, moved, qp, qr⟩
  · rintro ⟨w, hw, hz⟩
    obtain ⟨g, hg, rfl⟩ := (a.mem_subgroupOrbitCodes s K _ w).1 hw
    obtain ⟨σ, q, eq⟩ := Name.entries_cover (a.act s g (Name.restrictBelow p τ)) hz
    have entry : Name.Entry σ (a.act s g (Name.restrictBelow p τ)) q := by
      change ZFSet.pair σ.val (s.encode q) ∈ (a.act s g (Name.restrictBelow p τ)).val
      rwa [← eq]
    obtain ⟨ν, r, old, moved, qp, qr⟩ := (a.entry_act_restrictBelow s g p τ σ q).1 entry
    rw [eq]
    exact (a.entry_mix s K p τ σ q).2 ⟨g, hg, ν, r, old, moved, qp, qr⟩

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_subgroupOrbitFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (τ : Name s) (hτ : τ.val ∈ M.sets) (y : ZFSet.{u}) (hy : y ∈ M.sets) :
    Realize M.sets subgroupOrbitFormula (extend y (extend τ.val (extend (t.subset (fun g => g ∈ K))
      (extend s.carrier (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0)))))) ↔
      y ∈ a.subgroupOrbitCodes s K τ := by
  rw [subgroupOrbitFormula, M.realize_exConditions t 4 _ _ group rfl, a.mem_subgroupOrbitCodes]
  apply exists_congr
  intro g
  change (t.encode g ∈ t.subset (fun g => g ∈ K) ∧ Realize M.sets _ _) ↔ _
  rw [t.encode_mem_subset]
  apply and_congr_right
  intro _
  rw [realize_atomicApplication, map_extend, map_extend, map_empty]
  change Realize M.sets codedNameActionFormula (extend (t.encode g) (extend τ.val (extend y
    (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔ _
  rw [M.realize_codedNameActionFormula a s t pairing unions powers separation collection carrier group maps g τ.val y hτ hy]
  constructor
  · rintro ⟨σ, eq, output⟩
    have names : σ.val = τ := Subtype.ext eq
    rwa [names] at output
  · intro eq
    exact ⟨⟨τ, hτ⟩, rfl, eq⟩

theorem subgroupOrbitCodes_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) : a.subgroupOrbitCodes s K τ ∈ M.sets := by
  let W := ({τ.val, τ.val} : ZFSet.{u})
  have hW : W ∈ M.sets := M.unorderedPair_mem pairing hτ hτ
  let B := a.orbitCodes s (M.nameDomain s) W
  have hB := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW
  have bound : a.subgroupOrbitCodes s K τ ⊆ B := by
    intro y hy
    obtain ⟨g, _, eq⟩ := (a.mem_subgroupOrbitCodes s K τ y).1 hy
    exact (a.mem_orbitCodes s (M.nameDomain s) W y).2
      ⟨g, τ, hτ, ZFSet.mem_pair.2 (Or.inl rfl), eq⟩
  let context := extend τ.val (extend (t.subset (fun g => g ∈ K))
    (extend s.carrier (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))
  have selected := M.separation_mem separation subgroupOrbitFormula context
    (Fin.cases hτ (Fin.cases hK (Fin.cases carrier (Fin.cases group (Fin.cases maps (fun i => Fin.elim0 i)))))) hB
  have eq : ZFSet.sep (fun y => Realize M.sets subgroupOrbitFormula (extend y context)) B =
      a.subgroupOrbitCodes s K τ := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hy, rel⟩
      exact (M.realize_subgroupOrbitFormula a s t pairing unions powers separation collection carrier group maps K τ hτ y
        (M.transitive hB hy)).1 rel
    · intro hy
      exact ⟨bound hy, (M.realize_subgroupOrbitFormula a s t pairing unions powers separation collection carrier group maps K τ hτ y
        (M.transitive hB (bound hy))).2 hy⟩
  exact eq ▸ selected

theorem mix_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) : (a.mix s K p τ).val ∈ M.sets := by
  rw [a.mix_code_union]
  exact M.union_mem unions (M.subgroupOrbitCodes_mem a s t pairing unions powers separation collection carrier group maps K hK
    (Name.restrictBelow p τ) (M.restrictBelow_mem s pairing unions powers separation carrier order p τ hτ))

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RowPositionBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem rowPositionSequence_length {mu delta : ZFSet.{u}}
    (ordinal : ordinalSetProperty mu) (length : delta ∈ insert mu mu) :
    ordinalSetProperty delta ∧ delta ⊆ mu := by
  rcases ZFSet.mem_insert_iff.1 length with rfl | member
  · exact ⟨ordinal, fun _ hx => hx⟩
  · exact ⟨ordinalSetProperty_member ordinal member, fun a ha => ordinal.1 delta member a ha⟩

theorem RowPositionSequenceCode.shape {L r I mu f : ZFSet.{u}}
    (code : RowPositionSequenceCode L r I mu f) (ordinal : ordinalSetProperty mu) :
    f ⊆ ZFSet.prod mu I := by
  obtain ⟨delta, length, function, _⟩ := code
  intro z hz
  obtain ⟨a, ha, x, hx, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨(rowPositionSequence_length ordinal length).2 ha, hx⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_rowPositionSequences {L r I mu f : ZFSet.{u}} (ordinal : ordinalSetProperty mu) :
    f ∈ M.rowPositionSequences L r I mu ↔ f ∈ M.sets ∧ RowPositionSequenceCode L r I mu f := by
  rw [rowPositionSequences, ZFSet.mem_sep, M.mem_groundRelations]
  exact ⟨fun ⟨ground, code⟩ => ⟨ground.1, code⟩,
    fun ⟨ground, code⟩ => ⟨⟨ground, code.shape ordinal⟩, code⟩⟩

theorem rowPositionSequence_data {L r I mu f : ZFSet.{u}}
    (hL : L ∈ M.sets) (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu)
    (member : f ∈ M.rowPositionSequences L r I mu) :
    f ∈ M.sets ∧ ∃ delta ∈ M.sets, ordinalSetProperty delta ∧ delta ⊆ mu ∧
      ZFSet.IsFunc delta I f ∧ ∃ D ∈ L, D ∈ M.sets ∧
        ∀ a x, ZFSet.pair a x ∈ f → ZFSet.pair x D ∈ r := by
  obtain ⟨ground, delta, length, function, D, hD, bounds⟩ :=
    (M.mem_rowPositionSequences ordinal).1 member
  have hdelta : delta ∈ M.sets := (ZFSet.mem_insert_iff.1 length).elim
    (fun equal => equal ▸ hmu) (M.transitive hmu)
  have ordBound := rowPositionSequence_length ordinal length
  exact ⟨ground, delta, hdelta, ordBound.1, ordBound.2, function,
    D, hD, M.transitive hL hD, bounds⟩

end TransitiveGround

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundFunctionCoordinateDensity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace PartialFunctionCode

theorem insert_entry {X Y p x y : ZFSet.{u}} (h : PartialFunctionCode X Y p)
    (hx : x ∈ X) (hy : y ∈ Y)
    (agree : ∀ z, ZFSet.pair x z ∈ p → z = y) :
    PartialFunctionCode X Y (insert (ZFSet.pair x y) p) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with eq | hz
    · exact eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
    · exact h.shape hz
  · intro a b c hb hc
    rcases ZFSet.mem_insert_iff.1 hb with eqb | oldb
    · obtain ⟨ax, by'⟩ := ZFSet.pair_inj.1 eqb
      rcases ZFSet.mem_insert_iff.1 hc with eqc | oldc
      · exact by'.trans (ZFSet.pair_inj.1 eqc).2.symm
      · exact by'.trans (agree c (ax ▸ oldc)).symm
    · rcases ZFSet.mem_insert_iff.1 hc with eqc | oldc
      · obtain ⟨ax, cy⟩ := ZFSet.pair_inj.1 eqc
        exact (agree b (ax ▸ oldb)).trans cy.symm
      · exact h.unique a b c oldb oldc

end PartialFunctionCode

namespace TransitiveGround

open SetRealization SetFormula
variable (M : TransitiveGround.{u})

theorem countablePartialFunctions_insert
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {X Y p x y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets)
    (hp : p ∈ M.smallPartialFunctions X Y ZFSet.omega) (hx : x ∈ X) (hy : y ∈ Y)
    (agree : ∀ z, ZFSet.pair x z ∈ p → z = y) :
    insert (ZFSet.pair x y) p ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  obtain ⟨hpM, code, small⟩ := (M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp
  have entry := M.orderedPair_mem pairing (M.transitive hX hx) (M.transitive hY hy)
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨M.insert_mem pairing unions entry hpM, code.insert_entry hx hy agree,
      M.groundEmbeddable_insert pairing unions powers separation infinite hpM entry small⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundRowDistinguishing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem mem_rowCoordinateDomain (I C Y p x : ZFSet.{u}) :
    x ∈ rowCoordinateDomain I C Y p ↔
      x ∈ ZFSet.prod I C ∧ ∃ y ∈ Y, ZFSet.pair x y ∈ p := by
  rw [rowCoordinateDomain, mem_relationImage]
  constructor
  · rintro ⟨hx, z, hz, rel⟩
    obtain ⟨a, _, y, hy, eq⟩ := (mem_productFirst (ZFSet.prod I C) Y _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    refine ⟨hx, y, hy, ?_⟩
    rw [entries.2]
    exact entries.1 ▸ hz
  · rintro ⟨hx, y, hy, entry⟩
    exact ⟨hx, ZFSet.pair x y, entry,
      (mem_productFirst (ZFSet.prod I C) Y _).2 ⟨x, hx, y, hy, rfl⟩⟩

theorem mem_rowUsedColumns (I C Y p c : ZFSet.{u}) :
    c ∈ rowUsedColumns I C Y p ↔
      c ∈ C ∧ ∃ i ∈ I, ∃ y ∈ Y, ZFSet.pair (ZFSet.pair i c) y ∈ p := by
  rw [rowUsedColumns, mem_relationImage]
  constructor
  · rintro ⟨hc, x, hx, rel⟩
    obtain ⟨i, hi, d, _, eq⟩ := (mem_productSecond I C _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    obtain ⟨_, y, hy, entry⟩ := (mem_rowCoordinateDomain I C Y p x).1 hx
    rw [entries.1, ← entries.2] at entry
    exact ⟨hc, i, hi, y, hy, entry⟩
  · rintro ⟨hc, i, hi, y, hy, entry⟩
    exact ⟨hc, ZFSet.pair i c,
      (mem_rowCoordinateDomain I C Y p _).2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hc⟩, y, hy, entry⟩,
      (mem_productSecond I C _).2 ⟨i, hi, c, hc, rfl⟩⟩

theorem rowUsedColumns_subset (I C Y p : ZFSet.{u}) : rowUsedColumns I C Y p ⊆ C :=
  fun c hc => ((mem_rowUsedColumns I C Y p c).1 hc).1

theorem not_mem_rowUsedColumns_iff {I C Y p c : ZFSet.{u}}
    (code : PartialFunctionCode (ZFSet.prod I C) Y p) (hc : c ∈ C) :
    c ∉ rowUsedColumns I C Y p ↔
      ∀ i y, ZFSet.pair (ZFSet.pair i c) y ∉ p := by
  constructor
  · intro fresh i y entry
    have bound := ZFSet.pair_mem_prod.1 (code.shape entry)
    have coordinates := ZFSet.pair_mem_prod.1 bound.1
    exact fresh ((mem_rowUsedColumns I C Y p c).2 ⟨hc, i, coordinates.1, y, bound.2, entry⟩)
  · intro fresh used
    obtain ⟨_, i, _, y, _, entry⟩ := (mem_rowUsedColumns I C Y p c).1 used
    exact fresh i y entry

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem rowCoordinateDomain_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) : rowCoordinateDomain I C Y p ∈ M.sets := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  exact M.relationImage_mem separation hp coordinates
    (M.productFirst_mem pairing unions powers separation coordinates hY)

theorem rowCoordinateDomain_groundEmbeddable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) : M.groundEmbeddable (rowCoordinateDomain I C Y p) N := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  exact M.groundEmbeddable_function_image pairing unions powers separation choice hp coordinates hN
    (M.productFirst_mem pairing unions powers separation coordinates hY)
    (productFirst_function (ZFSet.prod I C) Y) small

theorem rowUsedColumns_groundEmbeddable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) : M.groundEmbeddable (rowUsedColumns I C Y p) N :=
  M.groundEmbeddable_function_image pairing unions powers separation choice
    (M.rowCoordinateDomain_mem pairing unions powers separation hI hC hY hp) hC hN
    (M.productSecond_mem pairing unions powers separation hI hC) (productSecond_function I C)
    (M.rowCoordinateDomain_groundEmbeddable pairing unions powers separation choice hI hC hY hp hN small)

theorem exists_fresh_rowColumn
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) (large : ¬ M.groundEmbeddable C N) :
    ∃ c ∈ C, c ∉ rowUsedColumns I C Y p := by
  classical
  have columns := M.rowUsedColumns_groundEmbeddable pairing unions powers separation choice
    hI hC hY hp hN small
  by_contra! full
  have eq : rowUsedColumns I C Y p = C := by
    apply ZFSet.ext
    intro c
    exact ⟨fun hc => rowUsedColumns_subset I C Y p hc, full c⟩
  exact large (eq ▸ columns)

theorem countablePartialFunctions_fresh_column
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hp : p ∈ M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    ∃ c ∈ C, ∀ i y, ZFSet.pair (ZFSet.pair i c) y ∉ p := by
  obtain ⟨ground, code, small⟩ := (M.mem_smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega p).1 hp
  obtain ⟨c, hc, fresh⟩ := M.exists_fresh_rowColumn pairing unions powers separation choice
    hI hC hY ground (M.omega_mem separation infinite) small uncountable
  exact ⟨c, hc, (not_mem_rowUsedColumns_iff code hc).1 fresh⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem countablePartialFunctions_insert_two_rows
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C Y p i j c a b : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)
    (hi : i ∈ I) (hj : j ∈ I) (hc : c ∈ C) (ha : a ∈ Y) (hb : b ∈ Y)
    (distinct : i ≠ j) (fresh : ∀ k y, ZFSet.pair (ZFSet.pair k c) y ∉ p) :
    insert (ZFSet.pair (ZFSet.pair j c) b)
      (insert (ZFSet.pair (ZFSet.pair i c) a) p) ∈
        M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega := by
  have coordinates := M.prod_mem pairing unions powers separation hI hC
  have first := M.countablePartialFunctions_insert pairing unions powers separation infinite
    coordinates hY hp (ZFSet.pair_mem_prod.2 ⟨hi, hc⟩) ha
    (fun y entry => False.elim (fresh i y entry))
  apply M.countablePartialFunctions_insert pairing unions powers separation infinite
    coordinates hY first (ZFSet.pair_mem_prod.2 ⟨hj, hc⟩) hb
  intro y entry
  rcases ZFSet.mem_insert_iff.1 entry with eq | old
  · exact False.elim (distinct (ZFSet.pair_inj.1 (ZFSet.pair_inj.1 eq).1).1.symm)
  · exact False.elim (fresh j y old)

theorem rowDistinguishing_dense
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y i j : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hi : i ∈ I) (hj : j ∈ I) (distinct : i ≠ j)
    (values : ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
    Dense (M.rowDistinguishing I C Y i j) := by
  let := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
  intro p
  obtain ⟨c, hc, fresh⟩ := M.countablePartialFunctions_fresh_column
    pairing unions powers separation infinite choice hI hC hY (SetMembers.raw_mem p) uncountable
  obtain ⟨a, ha, b, hb, ne⟩ := values
  have extended := M.countablePartialFunctions_insert_two_rows
    pairing unions powers separation infinite hI hC hY (SetMembers.raw_mem p)
    hi hj hc ha hb distinct fresh
  let q := SetMembers.ofMem
    (insert (ZFSet.pair (ZFSet.pair j c) b)
      (insert (ZFSet.pair (ZFSet.pair i c) a) (SetMembers.raw p))) extended
  have rawq : SetMembers.raw q = insert (ZFSet.pair (ZFSet.pair j c) b)
      (insert (ZFSet.pair (ZFSet.pair i c) a) (SetMembers.raw p)) :=
    SetMembers.raw_ofMem _ _
  refine ⟨q, (M.smallFunction_le_iff (ZFSet.prod I C) Y ZFSet.omega q p).2 ?_, ?_⟩
  · intro z hz
    rw [rawq]
    exact ZFSet.mem_insert_of_mem _ (ZFSet.mem_insert_of_mem _ hz)
  · refine ⟨c, hc, a, ha, b, hb, ne, ?_, ?_⟩
    · rw [rawq]
      exact ZFSet.mem_insert_of_mem _ (ZFSet.mem_insert _ _)
    · rw [rawq]
      exact ZFSet.mem_insert _ _

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRowGenerics
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
variable (M : TransitiveGround.{u})

theorem mem_countableGenericGraph (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega))) (z : ZFSet.{u}),
      z ∈ M.countableGenericGraph X Y H ↔ ∃ p, H.mem p ∧ z ∈ SetMembers.raw p := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro H z
  rw [countableGenericGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨p, hp, hz⟩
    exact ⟨(M.smallFunction_raw_properties X Y ZFSet.omega p).2.1.shape hz, p, hp, hz⟩

theorem countableGenericGraph_extends (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega))) p,
      H.mem p → SetMembers.raw p ⊆ M.countableGenericGraph X Y H := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro H p hp z hz
  exact (M.mem_countableGenericGraph X Y H z).2 ⟨p, hp, hz⟩

theorem countableGenericGraph_partial (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions X Y ZFSet.omega)),
      PartialFunctionCode X Y (M.countableGenericGraph X Y H) := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro H
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x y z hy hz
  obtain ⟨p, hp, py⟩ := (M.mem_countableGenericGraph X Y H _).1 hy
  obtain ⟨q, hq, qz⟩ := (M.mem_countableGenericGraph X Y H _).1 hz
  obtain ⟨r, _, rp, rq⟩ := H.directed hp hq
  have code := (M.smallFunction_raw_properties X Y ZFSet.omega r).2.1
  exact code.unique x y z
    ((M.smallFunction_le_iff X Y ZFSet.omega r p).1 rp py)
    ((M.smallFunction_le_iff X Y ZFSet.omega r q).1 rq qz)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_rowDistinguishingFormula {n} (p i j c y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowDistinguishingFormula p i j c y) env ↔
      ∃ k ∈ env c, ∃ a ∈ env y, ∃ b ∈ env y, a ≠ b ∧
        ZFSet.pair (ZFSet.pair (env i) k) a ∈ env p ∧
        ZFSet.pair (ZFSet.pair (env j) k) b ∈ env p := by
  simp only [rowDistinguishingFormula, truth_exMem, Truth, truth_tripleMembershipFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem rowDistinguishing_code_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C Y i j : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hi : i ∈ I) (hj : j ∈ I) :
    (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)).subset
      (M.rowDistinguishing I C Y i j) ∈ M.sets := by
  let s := SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)
  let params := extend i (extend j (extend C (extend Y Fin.elim0)))
  have members : ∀ k, params k ∈ M.sets :=
    Fin.cases (M.transitive hI hi) (Fin.cases (M.transitive hI hj)
      (Fin.cases hC (Fin.cases hY (fun k => Fin.elim0 k))))
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) hY
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.rowDistinguishingFormula 0 1 2 3 4) params members carrier
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.rowDistinguishingFormula 0 1 2 3 4) (extend z params))
      (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega) =
        s.subset (M.rowDistinguishing I C Y i j) := by
    apply ZFSet.ext
    intro z
    erw [ZFSet.mem_sep, s.mem_subset]
    constructor
    · rintro ⟨hz, rel⟩
      obtain ⟨p, rfl⟩ := (s.mem_carrier z).1 hz
      exact ⟨p, (BoundedFormula.truth_rowDistinguishingFormula 0 1 2 3 4 _).1 rel, rfl⟩
    · rintro ⟨p, distinguishing, rfl⟩
      exact ⟨s.encode_mem p,
        (BoundedFormula.truth_rowDistinguishingFormula 0 1 2 3 4 _).2 distinguishing⟩
  exact eq ▸ selected

theorem generic_meets_rowDistinguishing
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y i j : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hi : i ∈ I) (hj : j ∈ I) (distinct : i ≠ j)
    (values : ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)),
      H.GenericFor (M.codedFamily
        (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega))) →
      H.Meets (M.rowDistinguishing I C Y i j) := by
  let := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
  intro H generic
  exact M.generic_meets_coded_dense _ H generic
    (M.rowDistinguishing_code_mem pairing unions powers separation infinite hI hC hY hi hj)
    (M.rowDistinguishing_dense pairing unions powers separation infinite choice
      hI hC hY hi hj distinct values uncountable)

theorem countableGenericGraph_rows_separated
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y i j : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hi : i ∈ I) (hj : j ∈ I) (distinct : i ≠ j)
    (values : ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega)),
      H.GenericFor (M.codedFamily
        (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega))) →
      ∃ c ∈ C, ∃ a ∈ Y, ∃ b ∈ Y, a ≠ b ∧
        ZFSet.pair (ZFSet.pair i c) a ∈ M.countableGenericGraph (ZFSet.prod I C) Y H ∧
        ZFSet.pair (ZFSet.pair j c) b ∈ M.countableGenericGraph (ZFSet.prod I C) Y H ∧
        ZFSet.pair (ZFSet.pair j c) a ∉ M.countableGenericGraph (ZFSet.prod I C) Y H := by
  let := M.smallFunctionOrder (ZFSet.prod I C) Y ZFSet.omega
  intro H generic
  obtain ⟨p, hp, c, hc, a, ha, b, hb, ne, first, second⟩ :=
    M.generic_meets_rowDistinguishing pairing unions powers separation infinite choice
      hI hC hY hi hj distinct values uncountable H generic
  have includes := M.countableGenericGraph_extends (ZFSet.prod I C) Y H p hp
  have firstEntry := includes first
  have secondEntry := includes second
  refine ⟨c, hc, a, ha, b, hb, ne, firstEntry, secondEntry, ?_⟩
  intro sameValue
  exact ne ((M.countableGenericGraph_partial (ZFSet.prod I C) Y H).unique
    (ZFSet.pair j c) a b sameValue secondEntry)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBinaryRows
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem mem_two_iff (x : ZFSet.{u}) :
    x ∈ natSetCode 2 ↔ x = natSetCode 0 ∨ x = natSetCode 1 := by
  rw [mem_natSetCode]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩

theorem two_distinct_values :
    ∃ a ∈ natSetCode 2, ∃ b ∈ natSetCode 2, a ≠ (b : ZFSet.{u}) := by
  refine ⟨natSetCode 0, (mem_two_iff _).2 (Or.inl rfl),
    natSetCode 1, (mem_two_iff _).2 (Or.inr rfl), ?_⟩
  intro eq
  have impossible := natSetCode_injective eq
  omega

namespace TransitiveGround

open SetRealization SetFormula
variable (M : TransitiveGround.{u})

theorem mem_binaryGenericRow (I C : ZFSet.{u}) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ (H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))) (i c : ZFSet.{u}),
      c ∈ M.binaryGenericRow I C H i ↔ c ∈ C ∧
        ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈
          M.countableGenericGraph (ZFSet.prod I C) (natSetCode 2) H := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H i c
  exact ZFSet.mem_sep

theorem binaryGenericRow_ne
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C i j : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hi : i ∈ I) (hj : j ∈ I) (distinct : i ≠ j)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)),
      H.GenericFor (M.codedFamily (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))) →
      M.binaryGenericRow I C H i ≠ M.binaryGenericRow I C H j := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H generic same
  obtain ⟨c, hc, a, ha, b, hb, ne, first, second, absent⟩ :=
    M.countableGenericGraph_rows_separated pairing unions powers separation infinite choice
      hI hC (M.natSetCode_mem separation infinite 2) hi hj distinct
      two_distinct_values uncountable H generic
  rcases (mem_two_iff a).1 ha with rfl | rfl
  · rcases (mem_two_iff b).1 hb with rfl | rfl
    · exact ne rfl
    · have right := (M.mem_binaryGenericRow I C H j c).2 ⟨hc, second⟩
      have left := (M.mem_binaryGenericRow I C H i c).1 (same ▸ right)
      have impossible := natSetCode_injective
        ((M.countableGenericGraph_partial (ZFSet.prod I C) (natSetCode 2) H).unique
          (ZFSet.pair i c) (natSetCode 1) (natSetCode 0) left.2 first)
      omega
  · have left := (M.mem_binaryGenericRow I C H i c).2 ⟨hc, first⟩
    exact absent ((M.mem_binaryGenericRow I C H j c).1 (same ▸ left)).2

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBinaryRowNames
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
variable (M : TransitiveGround.{u})

theorem entry_binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u})
    (σ : Name (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name.Entry σ (M.binaryRowName I C one i) p ↔ ∃ c ∈ C,
      Name.check (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c = σ ∧
      ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈ SetMembers.raw p := by
  rw [binaryRowName, Name.entry_assemble]
  constructor
  · rintro ⟨z, eq, rfl⟩
    exact ⟨SetMembers.raw z.val.1, SetMembers.raw_mem z.val.1, eq, z.property⟩
  · rintro ⟨c, hc, eq, assigned⟩
    refine ⟨⟨(SetMembers.ofMem c hc, p), ?_⟩, ?_, rfl⟩
    · simpa only [SetMembers.raw_ofMem] using assigned
    · simpa only [SetMembers.raw_ofMem] using eq

theorem mem_binaryRowName_code (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i z : ZFSet.{u}) :
    z ∈ (M.binaryRowName I C one i).val ↔ ∃ c ∈ C,
      ∃ p ∈ M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega,
        z = ZFSet.pair (Name.check (SetMembers.presentation
          (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c).val p ∧
        ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈ p := by
  constructor
  · intro hz
    obtain ⟨σ, p, eq⟩ := Name.entries_cover (M.binaryRowName I C one i) hz
    change z = ZFSet.pair σ.val (SetMembers.raw p) at eq
    have entry : Name.Entry σ (M.binaryRowName I C one i) p := by
      change ZFSet.pair σ.val (SetMembers.raw p) ∈ (M.binaryRowName I C one i).val
      rw [← eq]
      exact hz
    obtain ⟨c, hc, child, assigned⟩ := (M.entry_binaryRowName I C one i σ p).1 entry
    refine ⟨c, hc, SetMembers.raw p, SetMembers.raw_mem p, ?_, assigned⟩
    rw [child]
    exact eq
  · rintro ⟨c, hc, p, hp, eq, assigned⟩
    have entry := (M.entry_binaryRowName I C one i _ (SetMembers.ofMem p hp)).2
      ⟨c, hc, rfl, by simpa only [SetMembers.raw_ofMem] using assigned⟩
    change ZFSet.pair (Name.check (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one c).val
        (SetMembers.raw (SetMembers.ofMem p hp)) ∈ (M.binaryRowName I C one i).val at entry
    rw [SetMembers.raw_ofMem] at entry
    exact eq.symm ▸ entry

theorem mem_eval_binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (H : Set (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (hone : one ∈ H) (i x : ZFSet.{u}) :
    x ∈ Name.eval H (M.binaryRowName I C one i) ↔ x ∈ C ∧
      ∃ p, p ∈ H ∧ ZFSet.pair (ZFSet.pair i x) (natSetCode 1) ∈ SetMembers.raw p := by
  rw [Name.mem_eval]
  constructor
  · rintro ⟨σ, p, entry, hp, eq⟩
    obtain ⟨c, hc, rfl, assigned⟩ := (M.entry_binaryRowName I C one i σ p).1 entry
    rw [Name.eval_check H one hone] at eq
    exact ⟨eq ▸ hc, p, hp, eq ▸ assigned⟩
  · rintro ⟨hx, p, hp, assigned⟩
    exact ⟨Name.check (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) one x, p,
      (M.entry_binaryRowName I C one i _ p).2 ⟨x, hx, rfl, assigned⟩,
      hp, Name.eval_check H one hone x⟩

theorem eval_binaryRowName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)),
      H.mem one → ∀ i : ZFSet.{u},
      Name.eval {p | H.mem p} (M.binaryRowName I C one i) = M.binaryGenericRow I C H i := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H hone i
  apply ZFSet.ext
  intro x
  rw [M.mem_eval_binaryRowName I C one {p | H.mem p} hone i x,
    M.mem_binaryGenericRow I C H i x,
    M.mem_countableGenericGraph (ZFSet.prod I C) (natSetCode 2) H]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBinaryRowSets
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
variable (M : TransitiveGround.{u})

theorem entry_binaryRowSetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (σ : Name (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name.Entry σ (M.binaryRowSetName I C one) p ↔
      ∃ i ∈ I, M.binaryRowName I C one i = σ ∧ one = p := by
  rw [binaryRowSetName, Name.entry_assemble]
  constructor
  · rintro ⟨i, eq, condition⟩
    exact ⟨SetMembers.raw i, SetMembers.raw_mem i, eq, condition⟩
  · rintro ⟨i, hi, eq, condition⟩
    exact ⟨SetMembers.ofMem i hi, by simpa only [SetMembers.raw_ofMem] using eq, condition⟩

theorem mem_binaryRowSetName_code (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (z : ZFSet.{u}) :
    z ∈ (M.binaryRowSetName I C one).val ↔ ∃ i ∈ I,
      z = ZFSet.pair (M.binaryRowName I C one i).val (SetMembers.raw one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    exact ⟨SetMembers.raw i, SetMembers.raw_mem i, eq.symm⟩
  · rintro ⟨i, hi, eq⟩
    refine ⟨SetMembers.ofMem i hi, ?_⟩
    simpa only [SetMembers.presentation, SetMembers.raw_ofMem] using eq.symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundBinaryRowNameCodes
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
variable (M : TransitiveGround.{u})

theorem realize_binaryRowEntryFormula (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hC : C ∈ M.sets)
    (hQ : M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega ∈ M.sets)
    (hi : i ∈ M.sets) (hbit : (natSetCode 1 : ZFSet.{u}) ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets (binaryRowEntryFormula 0 1 2 3 4 5)
      (extend z (extend C (extend
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
          (extend i (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))))) ↔
      z ∈ (M.binaryRowName I C one i).val := by
  let Q := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let s := SetMembers.presentation Q
  have hone : s.encode one ∈ M.sets := M.transitive hQ (SetMembers.raw_mem one)
  have children (c : ZFSet.{u}) (hc : c ∈ C) : (Name.check s one c).val ∈ M.sets :=
    M.check_mem s one pairing unions powers separation collection hone c (M.transitive hC hc)
  have assignment (c p w : ZFSet.{u}) (hc : c ∈ M.sets) (hp : p ∈ M.sets) (hw : w ∈ M.sets) :
      Realize M.sets (BoundedFormula.tripleMembershipFormula 6 2 8 1).toFormula
        (extend w (extend p (extend c (extend z (extend C (extend Q
          (extend i (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0))))))))) ↔
        ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈ p :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hw (Fin.cases hp (Fin.cases hc (Fin.cases hz (Fin.cases hC
        (Fin.cases hQ (Fin.cases hi (Fin.cases hone (Fin.cases hbit (fun j => Fin.elim0 j))))))))))).trans
      (BoundedFormula.truth_tripleMembershipFormula 6 2 8 1 _)
  rw [binaryRowEntryFormula, realize_ex]
  constructor
  · rintro ⟨c, hcM, rest⟩
    obtain ⟨p, hpM, rest⟩ := (realize_ex M.sets _ _).1 rest
    obtain ⟨w, hwM, hc, hp, checked, assigned, shape⟩ := (realize_ex M.sets _ _).1 rest
    rw [realize_binaryApplication, map_extend, map_empty] at checked
    have eq := (M.realize_uniformCheckFormula s one pairing unions powers separation collection
      hone c w hcM hwM).1 checked
    have pair := (M.realize_orderedPairFormula pairing 3 0 1 _ hz hwM hpM).1 shape
    apply (M.mem_binaryRowName_code I C one i z).2
    exact ⟨c, hc, p, hp,
      pair.trans (congrArg (fun v => ZFSet.pair v p) eq), (assignment c p w hcM hpM hwM).1 assigned⟩
  · intro member
    obtain ⟨c, hc, p, hp, shape, assigned⟩ := (M.mem_binaryRowName_code I C one i z).1 member
    have hcM := M.transitive hC hc
    have hpM := M.transitive hQ hp
    refine ⟨c, hcM, ?_⟩
    rw [realize_ex]
    refine ⟨p, hpM, ?_⟩
    rw [realize_ex]
    refine ⟨(Name.check s one c).val, children c hc, hc, hp, ?_, ?_, ?_⟩
    · rw [realize_binaryApplication, map_extend, map_empty]
      exact (M.realize_uniformCheckFormula s one pairing unions powers separation collection
        hone c _ hcM (children c hc)).2 rfl
    · exact (assignment c p _ hcM hpM (children c hc)).2 assigned
    · exact (M.realize_orderedPairFormula pairing 3 0 1 _ hz (children c hc) hpM).2 shape

theorem binaryRowName_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i : ZFSet.{u}) (hi : i ∈ M.sets) : (M.binaryRowName I C one i).val ∈ M.sets := by
  let Q := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let s := SetMembers.presentation Q
  have hQ : Q ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone : s.encode one ∈ M.sets := M.transitive hQ (SetMembers.raw_mem one)
  have hcheck := M.check_mem s one pairing unions powers separation collection hone C hC
  have childBound (c : ZFSet.{u}) (hc : c ∈ C) :
      (Name.check s one c).val ∈ ZFSet.sUnion (ZFSet.sUnion (Name.check s one C).val) :=
    Name.child_mem_doubleUnion ((Name.entry_check one C (Name.check s one c) one).2 ⟨c, hc, rfl, rfl⟩)
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers
    (M.union_mem unions (M.union_mem unions hcheck)) hQ
  have bound : (M.binaryRowName I C one i).val ⊆ B := by
    intro z hz
    obtain ⟨c, hc, p, hp, eq, _⟩ := (M.mem_binaryRowName_code I C one i z).1 hz
    exact eq.symm ▸ pairBound _ (childBound c hc) p hp
  let params := extend C (extend Q (extend i (extend (SetMembers.raw one)
    (extend (natSetCode 1) Fin.elim0))))
  have hbit := M.natSetCode_mem separation infinite 1
  have selected := M.separation_mem separation (binaryRowEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hC (Fin.cases hQ (Fin.cases hi (Fin.cases hone
      (Fin.cases hbit (fun j => Fin.elim0 j)))))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets (binaryRowEntryFormula 0 1 2 3 4 5)
      (extend z params)) B = (M.binaryRowName I C one i).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selected

theorem realize_binaryRowCodeFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i w : ZFSet.{u}) (hi : i ∈ M.sets) (hw : w ∈ M.sets) :
    Realize M.sets binaryRowCodeFormula (extend i (extend w (extend C (extend
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
        (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))))) ↔
      w = (M.binaryRowName I C one i).val := by
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hname := M.binaryRowName_mem pairing unions powers separation collection infinite hI hC one i hi
  have hbit := M.natSetCode_mem separation infinite 1
  rw [binaryRowCodeFormula]
  constructor
  · intro spec
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      have hzM := M.transitive hw hz
      have rel := (realize_imp M.sets _ _ _).1 (spec z hzM).1 hz
      rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
        map_extend, map_empty] at rel
      exact (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z hzM).1 rel
    · intro hz
      have hzM := M.transitive hname hz
      apply (realize_imp M.sets _ _ _).1 (spec z hzM).2
      rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
        map_extend, map_empty]
      exact (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z hzM).2 hz
  · intro eq z hzM
    constructor
    · apply (realize_imp M.sets _ _ _).2
      intro hz
      rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
        map_extend, map_empty]
      exact (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z hzM).2 (eq ▸ hz)
    · apply (realize_imp M.sets _ _ _).2
      intro rel
      rw [realize_reindex, map_extend, map_extend, map_extend, map_extend, map_extend,
        map_extend, map_empty] at rel
      exact eq.symm ▸ (M.realize_binaryRowEntryFormula I C one i pairing unions powers separation collection
        hC hQ hi hbit z hzM).1 rel

theorem exists_binaryRowName_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    ∃ W ∈ M.sets, ∀ i ∈ I, (M.binaryRowName I C one i).val ∈ W := by
  let Q := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  have hQ : Q ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone := M.transitive hQ (SetMembers.raw_mem one)
  let params := extend C (extend Q (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hC (Fin.cases hQ
    (Fin.cases hone (Fin.cases (M.natSetCode_mem separation infinite 1) (fun j => Fin.elim0 j))))
  have witnesses : ∀ i ∈ I, ∃ w ∈ M.sets,
      Realize M.sets binaryRowCodeFormula (extend i (extend w params)) := by
    intro i hi
    have hiM := M.transitive hI hi
    have hname := M.binaryRowName_mem pairing unions powers separation collection infinite hI hC one i hiM
    exact ⟨(M.binaryRowName I C one i).val, hname,
      (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
        hI hC one i _ hiM hname).2 rfl⟩
  obtain ⟨W, hW, covers⟩ := M.collection_witness collection binaryRowCodeFormula params members hI witnesses
  refine ⟨W, hW, ?_⟩
  intro i hi
  obtain ⟨w, hw, code⟩ := covers i hi
  have eq := (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
    hI hC one i w (M.transitive hI hi) (M.transitive hW hw)).1 code
  exact eq ▸ hw

theorem realize_binaryRowSetEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets binaryRowSetEntryFormula (extend z (extend I (extend C (extend
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
        (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))))) ↔
      z ∈ (M.binaryRowSetName I C one).val := by
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone := M.transitive hQ (SetMembers.raw_mem one)
  rw [binaryRowSetEntryFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, rest⟩
    obtain ⟨w, hwM, hi, code, shape⟩ := (realize_ex M.sets _ _).1 rest
    rw [realize_binaryApplication, map_extend, map_extend, map_extend, map_extend, map_empty] at code
    have eq := (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
      hI hC one i w hiM hwM).1 code
    have pair := (M.realize_orderedPairFormula pairing 2 0 6 _ hz hwM hone).1 shape
    exact (M.mem_binaryRowSetName_code I C one z).2
      ⟨i, hi, pair.trans (congrArg (fun v => ZFSet.pair v (SetMembers.raw one)) eq)⟩
  · intro member
    obtain ⟨i, hi, shape⟩ := (M.mem_binaryRowSetName_code I C one z).1 member
    have hiM := M.transitive hI hi
    have hname := M.binaryRowName_mem pairing unions powers separation collection infinite hI hC one i hiM
    refine ⟨i, hiM, ?_⟩
    rw [realize_ex]
    refine ⟨(M.binaryRowName I C one i).val, hname, hi, ?_, ?_⟩
    · rw [realize_binaryApplication, map_extend, map_extend, map_extend, map_extend, map_empty]
      exact (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
        hI hC one i _ hiM hname).2 rfl
    · exact (M.realize_orderedPairFormula pairing 2 0 6 _ hz hname hone).2 shape

theorem binaryRowSetName_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    (M.binaryRowSetName I C one).val ∈ M.sets := by
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone := M.transitive hQ (SetMembers.raw_mem one)
  obtain ⟨W, hW, inW⟩ := M.exists_binaryRowName_bound pairing unions powers separation collection infinite
    hI hC one
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hW
    (M.unorderedPair_mem pairing hone hone)
  have bound : (M.binaryRowSetName I C one).val ⊆ B := by
    intro z hz
    obtain ⟨i, hi, eq⟩ := (M.mem_binaryRowSetName_code I C one z).1 hz
    exact eq.symm ▸ pairBound _ (inW i hi) _ (ZFSet.mem_pair.2 (Or.inl rfl))
  let params := extend I (extend C (extend
    (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
      (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0))))
  have selected := M.separation_mem separation binaryRowSetEntryFormula params
    (Fin.cases hI (Fin.cases hC (Fin.cases hQ (Fin.cases hone
      (Fin.cases (M.natSetCode_mem separation infinite 1) (fun j => Fin.elim0 j)))))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets binaryRowSetEntryFormula
      (extend z params)) B = (M.binaryRowSetName I C one).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_binaryRowSetEntryFormula pairing unions powers separation collection infinite
        hI hC one z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (M.realize_binaryRowSetEntryFormula pairing unions powers separation collection infinite
        hI hC one z (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableRelationSelections
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

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem countablePartialFunctions_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y p q : ZFSet.{u}}
    (hp : p ∈ M.smallPartialFunctions X Y ZFSet.omega)
    (hq : q ∈ M.smallPartialFunctions X Y ZFSet.omega)
    (agree : ∀ x y z, ZFSet.pair x y ∈ p → ZFSet.pair x z ∈ q → y = z) :
    p ∪ q ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  obtain ⟨hpM, hpCode, hpSmall⟩ := (M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp
  obtain ⟨hqM, hqCode, hqSmall⟩ := (M.mem_smallPartialFunctions X Y ZFSet.omega q).1 hq
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨M.binary_union_mem pairing unions hpM hqM, hpCode.union hqCode agree,
      M.groundCountable_binary_union pairing unions powers separation infinite choice hpM hqM hpSmall hqSmall⟩

theorem countableFunction_common_extension
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ p q : SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      (∀ x y z, ZFSet.pair x y ∈ SetMembers.raw p → ZFSet.pair x z ∈ SetMembers.raw q → y = z) →
      ∃ r, SetMembers.raw r = SetMembers.raw p ∪ SetMembers.raw q ∧ r ≤ p ∧ r ≤ q := by
  let := M.smallFunctionOrder X Y ZFSet.omega
  intro p q agree
  have member := M.countablePartialFunctions_union pairing unions powers separation infinite choice
    (SetMembers.raw_mem p) (SetMembers.raw_mem q) agree
  let r := SetMembers.ofMem (SetMembers.raw p ∪ SetMembers.raw q) member
  have raw : SetMembers.raw r = SetMembers.raw p ∪ SetMembers.raw q := SetMembers.raw_ofMem _ _
  refine ⟨r, raw, (M.smallFunction_le_iff X Y ZFSet.omega r p).2 ?_,
    (M.smallFunction_le_iff X Y ZFSet.omega r q).2 ?_⟩
  · rw [raw]
    exact fun _ hz => ZFSet.mem_union.2 (Or.inl hz)
  · rw [raw]
    exact fun _ hz => ZFSet.mem_union.2 (Or.inr hz)

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFlatSuccessorFullActionGraph
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y G : Type u} [Group G] [PartialOrder X]
variable (a : PosetAction G X) (s : Presentation X) (t : Presentation Y) (b : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {N : ZFSet.{u}} (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
variable (hG : b.carrier ∈ M.sets) (hN : N ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)

theorem smallFunctionAction_entry (g : G) (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N))
    (x : X) (y : Y) :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    ZFSet.pair (s.encode (a.iso g x)) (t.encode y) ∈
      SetMembers.raw ((M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph).iso g p) ↔
        ZFSet.pair (s.encode x) (t.encode y) ∈ SetMembers.raw p := by
  let := M.smallFunctionOrder s.carrier t.carrier N
  rw [raw_smallFunctionAction, pair_mem_graphRename]
  change ZFSet.pair (s.encode ((a.iso g).toEquiv.symm ((a.iso g).toEquiv x))) (t.encode y) ∈ _ ↔ _
  rw [(a.iso g).toEquiv.symm_apply_apply]

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundOutsideRowNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing

universe u

theorem mem_rowUsedRows (I C Y p i : ZFSet.{u}) :
    i ∈ rowUsedRows I C Y p ↔
      i ∈ I ∧ ∃ c ∈ C, ∃ y ∈ Y, ZFSet.pair (ZFSet.pair i c) y ∈ p := by
  rw [rowUsedRows, mem_relationImage]
  constructor
  · rintro ⟨hi, x, hx, rel⟩
    obtain ⟨j, _, c, hc, eq⟩ := (mem_productFirst I C _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    obtain ⟨_, y, hy, entry⟩ := (mem_rowCoordinateDomain I C Y p x).1 hx
    rw [entries.1, ← entries.2] at entry
    exact ⟨hi, c, hc, y, hy, entry⟩
  · rintro ⟨hi, c, hc, y, hy, entry⟩
    exact ⟨hi, ZFSet.pair i c,
      (mem_rowCoordinateDomain I C Y p _).2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hc⟩, y, hy, entry⟩,
      (mem_productFirst I C _).2 ⟨i, hi, c, hc, rfl⟩⟩

theorem row_mem_rowUsedRows {I C Y p i c y : ZFSet.{u}}
    (code : PartialFunctionCode (ZFSet.prod I C) Y p)
    (entry : ZFSet.pair (ZFSet.pair i c) y ∈ p) : i ∈ rowUsedRows I C Y p := by
  have bound := ZFSet.pair_mem_prod.1 (code.shape entry)
  have coordinates := ZFSet.pair_mem_prod.1 bound.1
  exact (mem_rowUsedRows I C Y p i).2 ⟨coordinates.1, c, coordinates.2, y, bound.2, entry⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowAction_entry :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers
      (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}) (c : SetMembers C) (k : Fin 2),
      ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) (SetMembers.raw c)) (natSetCode k.val) ∈
        SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p) ↔
      ZFSet.pair (ZFSet.pair (s.encode i.val) (SetMembers.raw c)) (natSetCode k.val) ∈
        SetMembers.raw p := by
  let := columnOrder C
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i c k
  exact M.smallFunctionAction_entry (a.rowCoordinates C) (rowCoordinatePresentation s C)
    (natInitialPresentation 2) b pairing unions powers separation
    (M.rowCoordinate_carrier_mem s C pairing unions powers separation hL hC)
    (M.natSetCode_mem separation infinite 2) hG (M.omega_mem separation infinite)
    (M.rowCoordinate_graph_mem a s b C pairing unions powers separation hL hC hG graph)
    g p (i, c) (ULift.up k)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowAction_raw_entry :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}) (c y : ZFSet.{u}), c ∈ C → y ∈ natSetCode 2 →
      (ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) c) y ∈
        SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p) ↔
      ZFSet.pair (ZFSet.pair (s.encode i.val) c) y ∈ SetMembers.raw p) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i c y hc hy
  obtain ⟨k, eq⟩ := ((natInitialPresentation 2).mem_carrier y).1 hy
  change natSetCode k.down.val = y at eq
  have entry := M.internalRowAction_entry a s b C pairing unions powers separation infinite
    hL hC hG graph g p i (SetMembers.ofMem c hc) k.down
  simpa only [SetMembers.raw_ofMem, eq] using entry

theorem internalRowAction_usedRows :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}),
      s.encode (a.iso g i.val) ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2)
        (SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p)) ↔
      s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i
  rw [mem_rowUsedRows, mem_rowUsedRows]
  constructor
  · rintro ⟨_, c, hc, y, hy, entry⟩
    exact ⟨s.nonbottom.encode_mem i, c, hc, y, hy,
      (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
        hL hC hG graph g p i c y hc hy).1 entry⟩
  · rintro ⟨_, c, hc, y, hy, entry⟩
    exact ⟨s.nonbottom.encode_mem (a.nonbottom.iso g i), c, hc, y, hy,
      (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
        hL hC hG graph g p i c y hc hy).2 entry⟩

theorem internalRowAction_usedRows_bounded :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (D : L),
      (∀ i : {i : L // i ≠ ⊥},
        s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      ∀ i : {i : L // i ≠ ⊥},
        s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2)
          (SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
            hL hC hG graph).iso g p)) → i.val ≤ a.iso g D := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p D bound i used
  let j := (a.nonbottom.iso g).symm i
  have image : a.iso g j.val = i.val :=
    congrArg Subtype.val ((a.nonbottom.iso g).apply_symm_apply i)
  have old := (M.internalRowAction_usedRows a s b C pairing unions powers separation infinite
    hL hC hG graph g p j).1 (by rw [image]; exact used)
  have mapped := (a.iso g).monotone (bound j old)
  rw [image] at mapped
  exact mapped

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowName_action (g : G) (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowName s C hL i) =
      M.internalRowName s C hL (a.nonbottom.iso g i) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val)) =
    M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode (a.iso g i.val))
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename c (act.iso g)
    (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val))) q ↔ _
  rw [Name.entry_rename, M.entry_binaryRowName]
  constructor
  · rintro ⟨ν, p, entry, eq, rfl⟩
    obtain ⟨x, hx, rfl, hp⟩ := (M.entry_binaryRowName s.nonbottom.carrier C ⊤
      (s.encode i.val) ν p).1 entry
    refine ⟨x, hx, (act.act_check c g x).symm.trans eq, ?_⟩
    have moved := M.internalRowAction_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i (SetMembers.ofMem x hx) (1 : Fin 2)
    simp only [SetMembers.raw_ofMem] at moved
    exact moved.2 hp
  · rintro ⟨x, hx, rfl, hq⟩
    let p := (act.iso g).symm q
    have pq : act.iso g p = q := (act.iso g).apply_symm_apply q
    have moved := M.internalRowAction_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i (SetMembers.ofMem x hx) (1 : Fin 2)
    simp only [SetMembers.raw_ofMem] at moved
    have hp : ZFSet.pair (ZFSet.pair (s.encode i.val) x) (natSetCode 1) ∈
        SetMembers.raw p := by
      apply moved.1
      change ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) x) (natSetCode 1) ∈
        SetMembers.raw (act.iso g p)
      rw [pq]
      exact hq
    exact ⟨Name.check c ⊤ x, p,
      (M.entry_binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val) _ p).2
        ⟨x, hx, rfl, hp⟩, act.act_check c g x, pq⟩

theorem internalRowName_supported (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    a.principalFix i.val ≤ act.stabilizer c (M.internalRowName s C hL i) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act c g fixed
  change act.act c g (M.internalRowName s C hL i) = M.internalRowName s C hL i
  rw [M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph]
  apply congrArg (M.internalRowName s C hL)
  exact Subtype.ext (fixed i.val le_rfl)

theorem internalRowName_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) (M.internalRowName s C hL i) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  refine HereditarilySymmetric.mk ⟨i.val,
    M.internalRowName_supported a s b C pairing unions powers separation infinite hL hC hG graph i⟩ ?_
  intro σ p entry
  obtain ⟨x, _, rfl, _⟩ := (M.entry_binaryRowName s.nonbottom.carrier C ⊤
    (s.encode i.val) σ p).1 entry
  exact HereditarilySymmetric.check act c (a.principalSupportFamily ⊥ directed) x

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowSetName_action (g : G) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowSetName s C hL) = M.internalRowSetName s C hL := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (M.binaryRowSetName s.nonbottom.carrier C ⊤) =
    M.binaryRowSetName s.nonbottom.carrier C ⊤
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename c (act.iso g)
    (M.binaryRowSetName s.nonbottom.carrier C ⊤)) q ↔ _
  rw [Name.entry_rename, M.entry_binaryRowSetName]
  constructor
  · rintro ⟨ν, p, entry, eq, rfl⟩
    obtain ⟨x, hx, rfl, rfl⟩ := (M.entry_binaryRowSetName s.nonbottom.carrier C ⊤ ν p).1 entry
    obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier x).1 hx
    refine ⟨s.nonbottom.encode (a.nonbottom.iso g i), s.nonbottom.encode_mem _, ?_,
      (act.iso g).map_top.symm⟩
    have moved := M.internalRowName_action a s b C pairing unions powers separation infinite
      hL hC hG graph g i
    exact moved.symm.trans eq
  · rintro ⟨x, hx, rfl, rfl⟩
    obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier x).1 hx
    let j := (a.nonbottom.iso g).symm i
    refine ⟨M.internalRowName s C hL j, ⊤,
      (M.entry_binaryRowSetName s.nonbottom.carrier C ⊤ _ ⊤).2
        ⟨s.nonbottom.encode j, s.nonbottom.encode_mem j, rfl, rfl⟩, ?_,
      (act.iso g).map_top⟩
    change act.act c g (M.internalRowName s C hL j) = M.internalRowName s C hL i
    rw [M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph]
    exact congrArg (M.internalRowName s C hL) ((a.nonbottom.iso g).apply_symm_apply i)

theorem internalRowSetName_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) (M.internalRowSetName s C hL) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  refine HereditarilySymmetric.mk ⟨⊥, ?_⟩ ?_
  · intro g _
    exact M.internalRowSetName_action a s b C pairing unions powers separation infinite hL hC hG graph g
  · intro σ p entry
    obtain ⟨x, hx, rfl, _⟩ := (M.entry_binaryRowSetName s.nonbottom.carrier C ⊤ σ p).1 entry
    obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier x).1 hx
    exact M.internalRowName_hs a s b C pairing unions powers separation infinite hL hC hG graph directed i

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

open SetRealization
universe u

theorem outsideRowIndices_subset {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (B : L) : outsideRowIndices s B ⊆ s.nonbottom.carrier :=
  fun _ hx => (ZFSet.mem_sep.1 hx).1

theorem encode_mem_outsideRowIndices {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (B : L) (i : {i : L // i ≠ ⊥}) :
    s.encode i.val ∈ outsideRowIndices s B ↔ ¬ i.val ≤ B := by
  rw [outsideRowIndices, ZFSet.mem_sep, s.pair_mem_conditionOrder]
  exact ⟨And.right, fun hi => ⟨s.nonbottom.encode_mem i, hi⟩⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem entry_binaryRowSubsetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (J : ZFSet.{u})
    (σ : Name (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name.Entry σ (M.binaryRowSubsetName I C one J) p ↔
      ∃ i ∈ J, M.binaryRowName I C one i = σ ∧ one = p := by
  rw [binaryRowSubsetName, Name.entry_assemble]
  constructor
  · rintro ⟨i, eq, condition⟩
    exact ⟨SetMembers.raw i, SetMembers.raw_mem i, eq, condition⟩
  · rintro ⟨i, hi, eq, condition⟩
    exact ⟨SetMembers.ofMem i hi, by simpa only [SetMembers.raw_ofMem] using eq, condition⟩

theorem mem_binaryRowSubsetName_code (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (J z : ZFSet.{u}) :
    z ∈ (M.binaryRowSubsetName I C one J).val ↔ ∃ i ∈ J,
      z = ZFSet.pair (M.binaryRowName I C one i).val (SetMembers.raw one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    exact ⟨SetMembers.raw i, SetMembers.raw_mem i, eq.symm⟩
  · rintro ⟨i, hi, eq⟩
    refine ⟨SetMembers.ofMem i hi, ?_⟩
    simpa only [SetMembers.presentation, SetMembers.raw_ofMem] using eq.symm

theorem eval_binaryRowSubsetName_subset (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (J : ZFSet.{u}) (subset : J ⊆ I)
    (H : Set (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))) :
    Name.eval H (M.binaryRowSubsetName I C one J) ⊆ Name.eval H (M.binaryRowSetName I C one) := by
  intro x hx
  obtain ⟨σ, p, entry, hp, eq⟩ := (Name.mem_eval H _ x).1 hx
  obtain ⟨i, hi, child, condition⟩ := (M.entry_binaryRowSubsetName I C one J σ p).1 entry
  exact (Name.mem_eval H _ x).2 ⟨σ, p,
    (M.entry_binaryRowSetName I C one σ p).2 ⟨i, subset hi, child, condition⟩, hp, eq⟩

variable {L G : Type u} [Group G] [PartialOrder L] [OrderBot L]

theorem entry_internalOutsideRowsName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    ∀ (σ : Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)))
      (p : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      Name.Entry σ (M.internalOutsideRowsName s C hL B) p ↔
        ∃ i : {i : L // i ≠ ⊥}, ¬ i.val ≤ B ∧ M.internalRowName s C hL i = σ ∧ ⊤ = p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro σ p
  rw [internalOutsideRowsName, M.entry_binaryRowSubsetName]
  constructor
  · rintro ⟨x, hx, child, condition⟩
    obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier x).1 (outsideRowIndices_subset s B hx)
    exact ⟨i, (encode_mem_outsideRowIndices s B i).1 hx, child, condition⟩
  · rintro ⟨i, hi, child, condition⟩
    exact ⟨s.encode i.val, (encode_mem_outsideRowIndices s B i).2 hi, child, condition⟩

theorem mem_eval_internalOutsideRowsName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) (x : ZFSet.{u}),
      x ∈ Name.eval {p | H.mem p} (M.internalOutsideRowsName s C hL B) ↔
        ∃ i : {i : L // i ≠ ⊥}, ¬ i.val ≤ B ∧
          M.binaryGenericRow s.nonbottom.carrier C H (s.encode i.val) = x := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H x
  rw [Name.mem_eval]
  constructor
  · rintro ⟨σ, p, entry, _, eq⟩
    obtain ⟨i, hi, rfl, _⟩ := (M.entry_internalOutsideRowsName s C hL B σ p).1 entry
    change Name.eval {p | H.mem p} (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val)) = x at eq
    rw [M.eval_binaryRowName s.nonbottom.carrier C ⊤ H H.top_mem] at eq
    exact ⟨i, hi, eq⟩
  · rintro ⟨i, hi, eq⟩
    exact ⟨M.internalRowName s C hL i, ⊤,
      (M.entry_internalOutsideRowsName s C hL B _ ⊤).2 ⟨i, hi, rfl, rfl⟩, H.top_mem,
      (M.eval_binaryRowName s.nonbottom.carrier C ⊤ H H.top_mem (s.encode i.val)).trans eq⟩

theorem eval_internalOutsideRowsName_subset (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      Name.eval {p | H.mem p} (M.internalOutsideRowsName s C hL B) ⊆
        Name.eval {p | H.mem p} (M.internalRowSetName s C hL) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H
  exact M.eval_binaryRowSubsetName_subset s.nonbottom.carrier C ⊤ (outsideRowIndices s B)
    (outsideRowIndices_subset s B) {p | H.mem p}

theorem eval_internalOutsideRowsName_nonempty (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) (outside : ∃ i : L, ¬ i ≤ B) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      (Name.eval {p | H.mem p} (M.internalOutsideRowsName s C hL B)).Nonempty := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro H
  obtain ⟨i, hi⟩ := outside
  have nonbottom : i ≠ ⊥ := by
    intro eq
    exact hi (eq ▸ bot_le)
  exact ⟨M.binaryGenericRow s.nonbottom.carrier C H (s.encode i),
    (M.mem_eval_internalOutsideRowsName s C hL B H _).2 ⟨⟨i, nonbottom⟩, hi, rfl⟩⟩

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalOutsideRowsName_action (B : L) (g : G) (fixed : g ∈ a.principalFix B) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalOutsideRowsName s C hL B) = M.internalOutsideRowsName s C hL B := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  have preserves (i : {i : L // i ≠ ⊥}) :
      ¬ (a.nonbottom.iso g i).val ≤ B ↔ ¬ i.val ≤ B := by
    apply not_congr
    change a.iso g i.val ≤ B ↔ i.val ≤ B
    calc
      a.iso g i.val ≤ B ↔ a.iso g i.val ≤ a.iso g B := by rw [fixed B le_rfl]
      _ ↔ i.val ≤ B := (a.iso g).map_rel_iff
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename c (act.iso g) (M.internalOutsideRowsName s C hL B)) q ↔ _
  rw [Name.entry_rename, M.entry_internalOutsideRowsName]
  constructor
  · rintro ⟨ν, p, entry, eq, rfl⟩
    obtain ⟨i, hi, rfl, rfl⟩ := (M.entry_internalOutsideRowsName s C hL B ν p).1 entry
    refine ⟨a.nonbottom.iso g i, (preserves i).2 hi, ?_, (act.iso g).map_top.symm⟩
    have moved := M.internalRowName_action a s b C pairing unions powers separation infinite
      hL hC hG graph g i
    exact moved.symm.trans eq
  · rintro ⟨i, hi, rfl, rfl⟩
    let j := (a.nonbottom.iso g).symm i
    have image : a.nonbottom.iso g j = i := (a.nonbottom.iso g).apply_symm_apply i
    have outside : ¬ j.val ≤ B := (preserves j).1 (by rw [image]; exact hi)
    refine ⟨M.internalRowName s C hL j, ⊤,
      (M.entry_internalOutsideRowsName s C hL B _ ⊤).2 ⟨j, outside, rfl, rfl⟩, ?_,
      (act.iso g).map_top⟩
    change act.act c g (M.internalRowName s C hL j) = M.internalRowName s C hL i
    rw [M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph]
    exact congrArg (M.internalRowName s C hL) image

theorem internalOutsideRowsName_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k) (B : L) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) (M.internalOutsideRowsName s C hL B) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  refine HereditarilySymmetric.mk ⟨B, ?_⟩ ?_
  · intro g fixed
    exact M.internalOutsideRowsName_action a s b C pairing unions powers separation infinite
      hL hC hG graph B g fixed
  · intro σ p entry
    obtain ⟨i, _, rfl, _⟩ := (M.entry_internalOutsideRowsName s C hL B σ p).1 entry
    exact M.internalRowName_hs a s b C pairing unions powers separation infinite hL hC hG graph directed i

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundPrincipalSupportZF
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G : Type u} [Group G]
variable (t : Presentation G) (b : Presentation I) (K : I → Subgroup G)

theorem supportBasis_fiber_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (separation : SeparationSchema M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (i : I) :
    t.subset (fun g => g ∈ K i) ∈ M.sets := by
  have hi := M.transitive indices (b.encode_mem i)
  let params := extend (b.encode i) (extend (supportBasisCode b t K) Fin.elim0)
  have selected := M.separation_mem separation (pairMembershipFormula 1 0 2) params
    (Fin.cases hi (Fin.cases supports (fun j => Fin.elim0 j))) group
  have eq : ZFSet.sep (fun y => Realize M.sets (pairMembershipFormula 1 0 2) (extend y params)) t.carrier =
      t.subset (fun g => g ∈ K i) := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hy, rel⟩
      obtain ⟨g, rfl⟩ := (t.mem_carrier y).1 hy
      apply (t.encode_mem_subset (fun g => g ∈ K i) g).2
      exact (pair_mem_supportBasisCode b t K i g).1
        ((M.realize_pairMembershipFormula pairing 1 0 2 (extend (t.encode g) params)
          hi (M.transitive group hy) supports).1 rel)
    · intro hy
      obtain ⟨g, hg, rfl⟩ := (t.mem_subset (fun g => g ∈ K i) y).1 hy
      exact ⟨t.encode_mem g, (M.realize_pairMembershipFormula pairing 1 0 2
        (extend (t.encode g) params) hi (M.transitive group (t.encode_mem g)) supports).2
        ((pair_mem_supportBasisCode b t K i g).2 hg)⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInternalRowsInZF
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

theorem internalRowName_mem (s : Presentation L) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets)
    (i : {i : L // i ≠ ⊥}) : (M.internalRowName s C hL i).val ∈ M.sets := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowName_mem pairing unions powers separation collection infinite
    (M.nonbottom_carrier_mem s separation hL) hC ⊤ (s.encode i.val)
    (M.transitive hL (s.encode_mem i.val))

theorem eval_internalRowName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      Name.eval {p | H.mem p} (M.internalRowName s C hL i) =
        M.binaryGenericRow s.nonbottom.carrier C H (s.encode i.val) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H
  exact M.eval_binaryRowName s.nonbottom.carrier C ⊤ H H.top_mem (s.encode i.val)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundInternalRowSetZF
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
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

theorem internalRowSetName_mem (s : Presentation L) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) :
    (M.internalRowSetName s C hL).val ∈ M.sets := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowSetName_mem pairing unions powers separation collection infinite
    (M.nonbottom_carrier_mem s separation hL) hC ⊤

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSelectedSupportTupleFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowTupleName_action (g : G) (δ : ZFSet.{u})
    (positions : δ.toSet → {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowTupleName s C hL δ positions) =
      M.internalRowTupleName s C hL δ (fun i => a.nonbottom.iso g (positions i)) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (Name.indexedTuple ⊤ δ _) = Name.indexedTuple ⊤ δ _
  rw [Name.act_indexedTuple]
  apply congrArg (Name.indexedTuple ⊤ δ)
  funext i
  exact M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph g (positions i)

theorem internalRowTupleName_supported (δ : ZFSet.{u})
    (positions : δ.toSet → {i : L // i ≠ ⊥}) (D : L)
    (bounded : ∀ i, (positions i).val ≤ D) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    a.principalFix D ≤ act.stabilizer c (M.internalRowTupleName s C hL δ positions) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act c g fixed
  change act.act c g (M.internalRowTupleName s C hL δ positions) = _
  rw [M.internalRowTupleName_action a s b C pairing unions powers separation infinite hL hC hG graph]
  apply congrArg (M.internalRowTupleName s C hL δ)
  funext i
  exact Subtype.ext (fixed (positions i).val (bounded i))

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (z : ZFSet.{u}) : z ∈ M.binaryRowNameGraph I C one ↔
      ∃ i ∈ I, z = ZFSet.pair i (M.binaryRowName I C one i).val := by
  rw [binaryRowNameGraph, ZFSet.mem_range]
  exact ⟨fun ⟨i, eq⟩ => ⟨i.val, i.property, eq.symm⟩,
    fun ⟨i, hi, eq⟩ => ⟨⟨i, hi⟩, eq.symm⟩⟩

theorem pair_mem_binaryRowNameGraph (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (i x : ZFSet.{u}) : ZFSet.pair i x ∈ M.binaryRowNameGraph I C one ↔
      i ∈ I ∧ x = (M.binaryRowName I C one i).val := by
  rw [M.mem_binaryRowNameGraph I C one]
  constructor
  · rintro ⟨j, hj, eq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hj, rfl⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨i, hi, rfl⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem pair_mem_rowTupleFamily (one mu I W rows S f z : ZFSet.{u}) :
    ZFSet.pair f z ∈ rowTupleFamily one mu I W rows S ↔
      f ∈ S ∧ z = rowTupleCode one mu I W rows f := by
  rw [rowTupleFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨g, eq⟩
    obtain ⟨input, output⟩ := ZFSet.pair_inj.1 eq
    exact ⟨input ▸ g.property, output.symm.trans (congrArg (rowTupleCode one mu I W rows) input)⟩
  · rintro ⟨hf, rfl⟩
    exact ⟨⟨f, hf⟩, rfl⟩





namespace Name
theorem mem_indexedTuple_code {P : Type u} {s : Presentation P} (one : P)
    (δ : ZFSet.{u}) (names : δ.toSet → Name s) (z : ZFSet.{u}) :
    z ∈ (indexedTuple one δ names).val ↔ ∃ i : δ.toSet,
      z = ZFSet.pair (orderedPairNameCode (s.encode one) (check s one i.val).val (names i).val)
        (s.encode one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  simp only [orderedPair_code]
  exact exists_congr (fun _ => eq_comm)

end Name

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem binaryRowTupleCode_eq {I C mu δ f : ZFSet.{u}}
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (function : FunctionGraphOn δ f) (subset : δ ⊆ mu)
    (range : ∀ i, function.value i ∈ I) :
    let rows := M.binaryRowNameGraph I C one
    rowTupleCode (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows f =
      (Name.indexedTuple one δ (fun i => M.binaryRowName I C one (function.value i))).val := by
  dsimp only
  apply ZFSet.ext
  intro z
  rw [rowTupleCode, mem_indexedGraphNameCode, Name.mem_indexedTuple_code]
  constructor
  · rintro ⟨i, _, v, entry, equal⟩
    obtain ⟨_, _, x, hx, old, row⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    have hi := function.pair_source old
    have value := function.value_eq_of_entry ⟨i, hi⟩ old
    have rowValue := ((M.pair_mem_binaryRowNameGraph I C one x v).1 row).2
    refine ⟨⟨i, hi⟩, ?_⟩
    rw [Name.check_code_eq, value]
    exact rowValue ▸ equal
  · rintro ⟨i, equal⟩
    have row := (M.pair_mem_binaryRowNameGraph I C one (function.value i) _).2 ⟨range i, rfl⟩
    refine ⟨i.val, subset i.property, (M.binaryRowName I C one (function.value i)).val,
      (pair_mem_relationCompose _ _ _ _ _ _ _).2
        ⟨subset i.property, pair_second_mem_doubleUnion row, function.value i, range i,
          function.value_entry i, row⟩, ?_⟩
    rwa [Name.check_code_eq] at equal

theorem internalRowTupleCode_eq {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (C : ZFSet.{u}) (hL : s.carrier ∈ M.sets)
    {mu δ f : ZFSet.{u}} (function : FunctionGraphOn δ f) (subset : δ ⊆ mu)
    (positions : δ.toSet → {i : L // i ≠ ⊥})
    (values : ∀ i, function.value i = s.encode (positions i).val) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    rowTupleCode (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows f = (M.internalRowTupleName s C hL δ positions).val := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  have range (i : δ.toSet) : function.value i ∈ s.nonbottom.carrier := by
    rw [values i]
    exact s.nonbottom.encode_mem (positions i)
  have eq := M.binaryRowTupleCode_eq (C := C) ⊤ function subset range
  dsimp only at eq
  have names : (fun i => M.binaryRowName s.nonbottom.carrier C ⊤ (function.value i)) =
      (fun i => M.internalRowName s C hL (positions i)) := by
    funext i
    rw [values i]
    rfl
  exact eq.trans (congrArg Subtype.val (congrArg (Name.indexedTuple ⊤ δ) names))

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem mem_rowTupleTerms (one mu I W rows S z : ZFSet.{u}) :
    z ∈ rowTupleTerms one mu I W rows S ↔
      ∃ f ∈ S, z = rowTupleCode one mu I W rows f := by
  rw [rowTupleTerms, mem_functionGraphRange]
  constructor
  · rintro ⟨f, hf, entry⟩
    exact ⟨f, hf, ((pair_mem_rowTupleFamily one mu I W rows S f z).1 entry).2⟩
  · rintro ⟨f, hf, equal⟩
    exact ⟨f, hf, (pair_mem_rowTupleFamily one mu I W rows S f z).2 ⟨hf, equal⟩⟩

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundCompleteProjectionAtomicTruth
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
variable (M : TransitiveGround.{u}) {P Q : Type u}

theorem rename_between_mem (s : Presentation P) (t : Presentation Q)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (τ : Name s) (hτ : τ.val ∈ M.sets) : (Name.rename t f τ).val ∈ M.sets := by
  let U := s.carrier ∪ t.carrier
  let D := ZFSet.sep (fun x => x ∉ s.carrier) U
  let F := s.graph t f
  let G := F ∪ identityFunctionGraph D
  have subS : s.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inl hx)
  have subT : t.carrier ⊆ U := fun _ hx => ZFSet.mem_union.2 (Or.inr hx)
  have hU : U ∈ M.sets := M.binary_union_mem pairing unions hs ht
  have hD : D ∈ M.sets := M.bounded_separation_mem separation (.neg (.mem 0 1))
    (extend s.carrier Fin.elim0) (Fin.cases hs (fun i => Fin.elim0 i)) hU
  have hG : G ∈ M.sets := M.binary_union_mem pairing unions hf
    (M.identityFunctionGraph_mem pairing unions powers separation hD)
  have ff := s.graph_isFunc t f
  have full : ZFSet.IsFunc U U G := by
    constructor
    · intro z hz
      rcases ZFSet.mem_union.1 hz with old | identity
      · obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (ff.1 old)
        exact ZFSet.mem_prod.2 ⟨x, subS hx, y, subT hy, eq⟩
      · obtain ⟨x, hx, rfl⟩ := (mem_identityFunctionGraph D z).1 identity
        exact ZFSet.pair_mem_prod.2 ⟨(ZFSet.mem_sep.1 hx).1, (ZFSet.mem_sep.1 hx).1⟩
    · intro x hx
      by_cases source : x ∈ s.carrier
      · obtain ⟨y, entry, unique⟩ := ff.2 x source
        refine ⟨y, ZFSet.mem_union.2 (Or.inl entry), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact unique z old
        · exact False.elim ((ZFSet.mem_sep.1
            ((pair_mem_identityFunctionGraph D x z).1 identity).2).2 source)
      · refine ⟨x, ZFSet.mem_union.2 (Or.inr
          ((pair_mem_identityFunctionGraph D x x).2 ⟨rfl, ZFSet.mem_sep.2 ⟨hx, source⟩⟩)), ?_⟩
        intro z hz
        rcases ZFSet.mem_union.1 hz with old | identity
        · exact False.elim (source (ZFSet.pair_mem_prod.1 (ff.1 old)).1)
        · exact ((pair_mem_identityFunctionGraph D x z).1 identity).1.symm
  let u := SetMembers.presentation U
  let es := s.intoSet U subS
  let et := t.intoSet U subT
  let h := u.decodeFunction u G full
  have commute (p : P) : h (es p) = et (f p) := by
    apply (u.decodeFunction_iff u G full (es p) (et (f p))).2
    rw [s.encode_intoSet U subS, t.encode_intoSet U subT]
    exact ZFSet.mem_union.2 (Or.inl ((s.pair_mem_graph t f p (f p)).2 rfl))
  have sourceCode := Name.rename_val_of_encode u es (s.encode_intoSet U subS) τ
  have ground := M.rename_mem u pairing unions powers separation collection hU h
    ((u.graph_decodeFunction u G full).symm ▸ hG)
    (Name.rename u es τ) (sourceCode ▸ hτ)
  have equation : Name.rename u h (Name.rename u es τ) =
      Name.rename u et (Name.rename t f τ) := by
    rw [Name.rename_comp, Name.rename_comp]
    apply congrArg (fun k => Name.rename u k τ)
    funext p
    exact commute p
  rw [equation, Name.rename_val_of_encode u et (t.encode_intoSet U subT)] at ground
  exact ground

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {P : Type u} (s : Presentation P)

theorem pairEmpty_forwardGraph :
    s.graph s.pairEmpty id = pairedGraph s.carrier s.carrier {∅}
      (identityFunctionGraph s.carrier) (constantFamilyGraph s.carrier ∅) := by
  apply ZFSet.ext
  intro z
  rw [s.mem_graph, mem_pairedGraph]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨s.encode p, s.encode_mem p, s.encode p, s.encode_mem p,
      ∅, ZFSet.mem_singleton.2 rfl, rfl,
      (pair_mem_identityFunctionGraph _ _ _).2 ⟨rfl, s.encode_mem p⟩,
      (pair_mem_constantFamilyGraph _ _ _ _).2 ⟨s.encode_mem p, rfl⟩⟩
  · rintro ⟨x, hx, y, _, e, _, rfl, identity, constant⟩
    have xy := ((pair_mem_identityFunctionGraph _ _ _).1 identity).1
    have empty := ((pair_mem_constantFamilyGraph _ _ _ _).1 constant).2
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    subst y
    subst e
    exact ⟨p, rfl⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {P : Type u} (s : Presentation P)
include pairing unions powers separation

theorem pairEmpty_forwardGraph_mem (hs : s.carrier ∈ M.sets) : s.graph s.pairEmpty id ∈ M.sets := by
  rw [s.pairEmpty_forwardGraph]
  have empty := M.empty_mem ⟨s.carrier, hs⟩
  have single : ({∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing empty empty
  exact M.pairedGraph_mem pairing unions powers separation hs hs single
    (M.identityFunctionGraph_mem pairing unions powers separation hs)
    (M.constantFamilyGraph_mem pairing unions powers separation hs empty)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {P : Type u} (c : Presentation P)
variable (one mu I W rows S : ZFSet.{u})
variable (valid : ∀ z ∈ (rowTupleTerms one mu I W rows S), IsName c z)

include valid

theorem pair_mem_liftedRowTupleFamily (f z : ZFSet.{u}) :
    ZFSet.pair f z ∈ (liftedRowTupleFamily c one mu I W rows S valid) ↔
      f ∈ S ∧ ∃ τ : Name c, τ.val = rowTupleCode one mu I W rows f ∧
        z = (Name.rename c.pairEmpty id τ).val := by
  rw [liftedRowTupleFamily, pair_mem_relationCompose]
  constructor
  · rintro ⟨hf, _, x, hx, tuple, rename⟩
    let τ : Name c := ⟨x, valid x hx⟩
    exact ⟨hf, τ, ((pair_mem_rowTupleFamily one mu I W rows S f x).1 tuple).2,
      ((Name.pair_mem_renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid τ z).1 rename).2⟩
  · rintro ⟨hf, τ, tuple, equal⟩
    have member : τ.val ∈ (rowTupleTerms one mu I W rows S) := (mem_rowTupleTerms one mu I W rows S τ.val).2 ⟨f, hf, tuple⟩
    have target : z ∈ (Name.renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid) := (Name.mem_renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid z).2
      ⟨τ, member, equal⟩
    exact ⟨hf, target, τ.val, member,
      (pair_mem_rowTupleFamily one mu I W rows S f τ.val).2 ⟨hf, tuple⟩,
      (Name.pair_mem_renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid τ z).2 ⟨member, equal⟩⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRowTermSetNames
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L]

theorem rowPositionSequence_decode (s : Presentation L)
    (hL : s.carrier ∈ M.sets) {mu f : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu)
    (member : f ∈ M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu) :
    f ∈ M.sets ∧ ∃ δ ∈ M.sets, ordinalSetProperty δ ∧ δ ⊆ mu ∧
      ∃ function : FunctionGraphOn δ f, ∃ positions : δ.toSet → {i : L // i ≠ ⊥},
        ∃ D : L, (∀ i, function.value i = s.encode (positions i).val) ∧
          ∀ i, (positions i).val ≤ D := by
  obtain ⟨hf, δ, hδ, ordδ, subδ, fn, d, hd, _, bounds⟩ :=
    M.rowPositionSequence_data hL hmu ordinal member
  let function : FunctionGraphOn δ f := ⟨s.nonbottom.carrier, fn⟩
  have range (i : δ.toSet) : function.value i ∈ s.nonbottom.carrier :=
    (ZFSet.pair_mem_prod.1 (fn.1 (function.value_entry i))).2
  have each (i : δ.toSet) : ∃ x : {i : L // i ≠ ⊥}, s.encode x.val = function.value i :=
    (s.nonbottom.mem_carrier (function.value i)).1 (range i)
  let positions (i : δ.toSet) : {i : L // i ≠ ⊥} := Classical.choose (each i)
  have values (i : δ.toSet) : function.value i = s.encode (positions i).val :=
    (Classical.choose_spec (each i)).symm
  obtain ⟨D, rfl⟩ := (s.mem_carrier d).1 hd
  refine ⟨hf, δ, hδ, ordδ, subδ, function, positions, D, values, ?_⟩
  intro i
  have bound := bounds i.val (function.value i) (function.value_entry i)
  rw [values i] at bound
  exact (s.pair_mem_conditionOrder (positions i).val D).1 bound

end

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedRowTupleSupports
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem liftedRowTuple_supported {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ (valid : ∀ z ∈ T, IsName c z) (f : ZFSet.{u}) (τ : Name c.pairEmpty) (D : L),
      ZFSet.pair f τ.val ∈ liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
        (⋃₀ ⋃₀ rows) rows S valid →
      (∀ i x, ZFSet.pair i x ∈ f → ZFSet.pair x (s.encode D) ∈ s.conditionOrder) →
      a.principalFix D ≤ act.stabilizer c.pairEmpty τ := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid f τ D entry bounded
  obtain ⟨hf, σ, source, lifted⟩ := (pair_mem_liftedRowTupleFamily c (c.encode ⊤) mu
    s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid f τ.val).1 entry
  obtain ⟨_, δ, _, _, subset, function, positions, _, values, _⟩ :=
    M.rowPositionSequence_decode s hL hmu ordinal hf
  have bound (i : δ.toSet) : (positions i).val ≤ D := by
    have positionOrder := bounded i.val (function.value i) (function.value_entry i)
    rw [values i] at positionOrder
    exact (s.pair_mem_conditionOrder (positions i).val D).1 positionOrder
  have same : σ = M.internalRowTupleName s C hL δ positions :=
    Subtype.ext (source.trans (M.internalRowTupleCode_eq s C hL function subset positions values))
  have sameLift : τ = Name.presentationEquiv c c.pairEmpty
      (M.internalRowTupleName s C hL δ positions) := by
    apply Subtype.ext
    change τ.val = (Name.rename c.pairEmpty id (M.internalRowTupleName s C hL δ positions)).val
    rw [lifted, same]
  rw [sameLift, act.stabilizer_presentationEquiv]
  exact M.internalRowTupleName_supported a s b C pairing unions powers separation infinite
    hL hC hG graph δ positions D bound

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundOutsideRowCodes
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
variable (M : TransitiveGround.{u})

theorem realize_binaryRowSubsetEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C J : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (hJ : J ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets binaryRowSetEntryFormula (extend z (extend J (extend C (extend
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
        (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))))) ↔
      z ∈ (M.binaryRowSubsetName I C one J).val := by
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone := M.transitive hQ (SetMembers.raw_mem one)
  rw [binaryRowSetEntryFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, rest⟩
    obtain ⟨w, hwM, hi, code, shape⟩ := (realize_ex M.sets _ _).1 rest
    rw [realize_binaryApplication, map_extend, map_extend, map_extend, map_extend, map_empty] at code
    have eq := (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
      hI hC one i w hiM hwM).1 code
    have pair := (M.realize_orderedPairFormula pairing 2 0 6 _ hz hwM hone).1 shape
    exact (M.mem_binaryRowSubsetName_code I C one J z).2
      ⟨i, hi, pair.trans (congrArg (fun v => ZFSet.pair v (SetMembers.raw one)) eq)⟩
  · intro member
    obtain ⟨i, hi, shape⟩ := (M.mem_binaryRowSubsetName_code I C one J z).1 member
    have hiM := M.transitive hJ hi
    have hname := M.binaryRowName_mem pairing unions powers separation collection infinite hI hC one i hiM
    refine ⟨i, hiM, ?_⟩
    rw [realize_ex]
    refine ⟨(M.binaryRowName I C one i).val, hname, hi, ?_, ?_⟩
    · rw [realize_binaryApplication, map_extend, map_extend, map_extend, map_extend, map_empty]
      exact (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
        hI hC one i _ hiM hname).2 rfl
    · exact (M.realize_orderedPairFormula pairing 2 0 6 _ hz hname hone).2 shape

theorem binaryRowSubsetName_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C J : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (hJ : J ∈ M.sets) (subset : J ⊆ I) :
    (M.binaryRowSubsetName I C one J).val ∈ M.sets := by
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have hone := M.transitive hQ (SetMembers.raw_mem one)
  obtain ⟨W, hW, inW⟩ := M.exists_binaryRowName_bound pairing unions powers separation collection infinite
    hI hC one
  obtain ⟨D, hD, pairBound⟩ := M.exists_pair_bound pairing unions powers hW
    (M.unorderedPair_mem pairing hone hone)
  have bound : (M.binaryRowSubsetName I C one J).val ⊆ D := by
    intro z hz
    obtain ⟨i, hi, eq⟩ := (M.mem_binaryRowSubsetName_code I C one J z).1 hz
    exact eq.symm ▸ pairBound _ (inW i (subset hi)) _ (ZFSet.mem_pair.2 (Or.inl rfl))
  let params := extend J (extend C (extend
    (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
      (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0))))
  have selected := M.separation_mem separation binaryRowSetEntryFormula params
    (Fin.cases hJ (Fin.cases hC (Fin.cases hQ (Fin.cases hone
      (Fin.cases (M.natSetCode_mem separation infinite 1) (fun j => Fin.elim0 j)))))) hD
  have eq : ZFSet.sep (fun z => Realize M.sets binaryRowSetEntryFormula
      (extend z params)) D = (M.binaryRowSubsetName I C one J).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_binaryRowSubsetEntryFormula pairing unions powers separation collection infinite
        hI hC one hJ z (M.transitive hD hz)).1 rel
    · intro hz
      exact ⟨bound hz, (M.realize_binaryRowSubsetEntryFormula pairing unions powers separation collection infinite
        hI hC one hJ z (M.transitive hD (bound hz))).2 hz⟩
  exact eq ▸ selected

theorem outsideRowIndices_mem {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (B : L) (separation : SeparationSchema M.sets)
    (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets) :
    outsideRowIndices s B ∈ M.sets := by
  have hB := M.transitive hL (s.encode_mem B)
  let params := extend (s.encode B) (extend s.conditionOrder Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (.neg (BoundedFormula.pairMembershipFormula 0 1 2)) params
    (Fin.cases hB (Fin.cases order (fun j => Fin.elim0 j)))
    (M.nonbottom_carrier_mem s separation hL)
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (.neg (BoundedFormula.pairMembershipFormula 0 1 2)) (extend x params))
      s.nonbottom.carrier = outsideRowIndices s B := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, outsideRowIndices, ZFSet.mem_sep]
    exact and_congr Iff.rfl (not_congr (BoundedFormula.truth_pairMembershipFormula 0 1 2 _))
  exact eq ▸ selected

theorem internalOutsideRowsName_mem {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets)
    (order : s.conditionOrder ∈ M.sets) (B : L) :
    (M.internalOutsideRowsName s C hL B).val ∈ M.sets := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowSubsetName_mem pairing unions powers separation collection infinite
    (M.nonbottom_carrier_mem s separation hL) hC ⊤
    (M.outsideRowIndices_mem s B separation hL order) (outsideRowIndices_subset s B)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSeparatedRowConditions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.PosetAction

universe u
variable {G L : Type u} [Group G] [PartialOrder L]

theorem moved_ne_of_separated (a : PosetAction G L) (g : G) (B D i : L)
    (overlap : ∀ x, x ≤ D → x ≤ a.iso g D → x ≤ B)
    (inside : i ≤ D) (outside : ¬ i ≤ B) : a.iso g i ≠ i := by
  intro fixed
  have moved := (a.iso g).monotone inside
  rw [fixed] at moved
  exact outside (overlap i inside moved)

end PartitionPilot.Forcing.PosetAction

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundInternalRowChoice
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
variable (N : TransitiveGround.{u})

theorem exists_function_choosing_subsets
    (powers : Realize N.sets powerSet Fin.elim0)
    (separation : SeparationSchema N.sets)
    (choice : Realize N.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ N.sets) :
    ∃ f ∈ N.sets, ∀ S ∈ N.sets, S ⊆ R → S.Nonempty →
      ∃ x ∈ S, ZFSet.pair S x ∈ f ∧ ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x := by
  obtain ⟨W, hW, subsets⟩ := N.power_witness powers hR
  let A := ZFSet.sep (fun S => S.Nonempty) W
  have hA : A ∈ N.sets := by
    have selected := N.bounded_separation_mem separation (BoundedFormula.nonemptyFormula 0)
      Fin.elim0 (fun i => Fin.elim0 i) hW
    have eq : ZFSet.sep (fun S => BoundedFormula.Truth (BoundedFormula.nonemptyFormula 0)
        (extend S Fin.elim0)) W = A := by
      apply ZFSet.ext
      intro S
      simp only [A, ZFSet.mem_sep, BoundedFormula.truth_nonemptyFormula]
      rfl
    exact eq ▸ selected
  obtain ⟨f, hf, code⟩ := N.choice_witness choice hA
    (fun S hS => (ZFSet.mem_sep.1 hS).2)
  refine ⟨f, hf, ?_⟩
  intro S hS subset nonempty
  have member : S ∈ A := ZFSet.mem_sep.2 ⟨(subsets S hS).2 subset, nonempty⟩
  obtain ⟨x, chosen, unique⟩ := code.function.2 S member
  exact ⟨x, code.chosen S x chosen, chosen, fun z _ hz => unique z hz⟩

end PartitionPilot.Forcing.TransitiveGround



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMixtureDensityRecovery
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem mix_mem_mixtureCandidates (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (τ : Name s) (ground : τ.val ∈ M.sets) (p : P) :
    (a.mix s K p τ).val ∈ M.niceNameCandidates a s (M.mixtureTermCodes a s τ) K := by
  apply (M.name_mem_niceNameCandidates a s _ K _).2
  exact ⟨M.mix_mem a s t pairing unions powers separation collection carrier order group maps K hK p τ ground,
    M.mix_subset_mixtureTermCodes a s τ ground K p, fun _ hg => a.mix_fixed s K p τ hg⟩

theorem mixture_candidate_data (F : NormalSubgroupFamily G) (K : Subgroup G)
    (member : F.mem K) (τ : Name s) (hs : HereditarilySymmetric a s F τ)
    (σ : Name s) (candidate : σ.val ∈ M.niceNameCandidates a s (M.mixtureTermCodes a s τ) K) :
    σ.val ∈ M.sets ∧ K ≤ a.stabilizer s σ ∧ HereditarilySymmetric a s F σ ∧
      Name.nameRank σ ≤ Name.nameRank τ := by
  have data := (M.name_mem_niceNameCandidates a s _ K σ).1 candidate
  refine ⟨data.1, data.2.2,
    niceNameCode_hs a s F member (M.mixtureTermCodes_hs a s F τ hs)
      ((niceNameCode_iff a s σ).2 data.2), ?_⟩
  change ZFSet.rank (Name.eval Set.univ σ) ≤ Name.nameRank τ
  rw [ZFSet.rank_le_iff]
  intro value memValue
  obtain ⟨ν, p, entry, _, rfl⟩ := (Name.mem_eval Set.univ σ value).1 memValue
  exact (Name.rank_eval_le Set.univ ν).trans_lt
    (M.mixtureTermCodes_rank a s τ ν (Name.entry_term_of_subset data.2.1 entry))

variable [OrderTop P]

theorem mixture_visibility_mem {I : Type u} (t : Presentation G) (b : Presentation I)
    (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : Name s) (ground : τ.val ∈ M.sets) (i : I) (hi : b.encode i ∈ M.sets) :
    (M.niceVisibilityName a s (M.mixtureTermCodes a s τ) (K i)).val ∈ M.sets :=
  M.niceVisibilityName_mem a s t b K pairing unions powers separation collection carrier group supports maps
    (M.mixtureTermCodes_mem a s t pairing unions powers separation collection carrier group maps τ ground)
    (M.mixtureTermCodes_valid a s τ) i hi

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P I : Type u} [Group G]
variable [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation I) (K : I → Subgroup G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t K ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)

include pairing unions powers separation collection carrier order group indices supports maps in
theorem forcesMem_mixtureVisibility_of_dense
    (i : I) (x : Name s) (ground : x.val ∈ M.sets) (p₀ : P)
    (dense : DenseBelow p₀ {p | Name.ForcesEq p x (a.mix s (K i) p x)}) :
    Name.ForcesMem p₀ x (M.niceVisibilityName a s (M.mixtureTermCodes a s x) (K i)) := by
  have subgroup := M.supportBasis_fiber_mem t b K pairing separation group indices supports i
  intro q below
  obtain ⟨p, pq, equal⟩ := dense q below
  refine ⟨p, pq, a.mix s (K i) p x, ⊤, ?_, le_top, equal⟩
  apply (M.entry_niceVisibilityName a s (M.mixtureTermCodes a s x) (K i) _ ⊤).2
  exact ⟨M.mix_mem_mixtureCandidates a s t pairing unions powers separation collection
    carrier order group maps (K i) subgroup x ground p, rfl⟩

include pairing unions powers separation collection carrier order group indices supports maps in
theorem exists_mixtureCandidate_of_dense
    (F : NormalSubgroupFamily G) (i : I) (member : F.mem (K i))
    (x : Name s) (ground : x.val ∈ M.sets) (symmetric : HereditarilySymmetric a s F x)
    (p₀ : P) (dense : DenseBelow p₀ {p | Name.ForcesEq p x (a.mix s (K i) p x)})
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    (active : H.mem p₀) :
    ∃ z : Name s,
      z.val ∈ M.niceNameCandidates a s (M.mixtureTermCodes a s x) (K i) ∧
      z.val ∈ M.sets ∧ HereditarilySymmetric a s F z ∧
      K i ≤ a.stabilizer s z ∧ Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {q | H.mem q} z = Name.eval {q | H.mem q} x := by
  have visibility := M.mixture_visibility_mem a s t b K pairing unions powers separation
    collection carrier group supports maps x ground i (M.transitive indices (b.encode_mem i))
  have forced := M.forcesMem_mixtureVisibility_of_dense a s t b K pairing unions powers
    separation collection carrier order group indices supports maps i x ground p₀ dense
  have atomic : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE => generic E (Or.inl hE)
  have value := Name.forcesMem_sound (M.nameDomain s) H atomic ground visibility active forced
  obtain ⟨z, candidate, equal⟩ :=
    (M.mem_eval_niceVisibilityName a s (M.mixtureTermCodes a s x) (K i)
      {q | H.mem q} H.top_mem (Name.eval {q | H.mem q} x)).1 value
  obtain ⟨groundZ, support, hs, rank⟩ :=
    M.mixture_candidate_data a s F (K i) member x symmetric z candidate
  exact ⟨z, candidate, groundZ, hs, support, rank, equal⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundProjectedRowUniqueFibers
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
variable (M : TransitiveGround.{u})

theorem completeProjection_codedGeneric_of_ordinary
    {Upper Lower : Type u} [PartialOrder Upper] [PartialOrder Lower]
    (upper : Presentation Upper) (lower : Presentation Lower)
    {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
    (projection : CompleteProjection restriction inclusion)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (upperCarrier : upper.carrier ∈ M.sets) (lowerCarrier : lower.carrier ∈ M.sets)
    (restrictionGround : upper.graph lower restriction ∈ M.sets)
    (H : ConditionFilter Upper)
    (ordinary : H.GenericFor (formulaFamily (M.nameDomain upper))) :
    (projection.projectedFilter H).GenericFor (M.codedFamily lower) := by
  intro E member dense
  obtain ⟨X, ground, rfl⟩ := member
  have preimage := M.presentedPreimage_mem upper lower restriction
    pairing unions powers separation upperCarrier lowerCarrier restrictionGround ground
  exact (projection.projectedFilter_meets_iff H _).2
    (M.ordinary_generic_meets_coded_dense upper pairing unions powers separation
      H ordinary preimage (projection.dense_preimage dense))

theorem completeProjection_binaryRowValues_ne
    {Upper : Type u} [PartialOrder Upper] (upper : Presentation Upper)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (upperCarrier : upper.carrier ∈ M.sets) :
    let R := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    let lower := SetMembers.presentation R
    ∀ (restriction : Upper →o SetMembers R) (inclusion : SetMembers R ↪o Upper)
      (_projection : CompleteProjection restriction inclusion),
      upper.graph lower restriction ∈ M.sets →
      ∀ (H : ConditionFilter Upper),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
        ∀ (one : SetMembers R), H.mem (inclusion one) →
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          Name.eval {p | H.mem p}
            (Name.rename upper inclusion (M.binaryRowName I C one i)) ≠
          Name.eval {p | H.mem p}
            (Name.rename upper inclusion (M.binaryRowName I C one j)) := by
  let R := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let lower := SetMembers.presentation R
  dsimp only
  intro restriction inclusion projection restrictionGround H ordinary one hone i hi j hj distinct
  have lowerCarrier : lower.carrier ∈ M.sets :=
    M.countablePartialFunctions_mem pairing unions powers separation infinite
      (M.prod_mem pairing unions powers separation hI hC)
      (M.natSetCode_mem separation infinite 2)
  have generic := M.completeProjection_codedGeneric_of_ordinary upper lower projection
    pairing unions powers separation upperCarrier lowerCarrier restrictionGround H ordinary
  have hone' : (projection.projectedFilter H).mem one := hone
  intro equal
  have same : Name.eval {p | (projection.projectedFilter H).mem p} (M.binaryRowName I C one i) =
      Name.eval {p | (projection.projectedFilter H).mem p} (M.binaryRowName I C one j) := by
    simpa only [Name.eval_rename, CompleteProjection.projectedFilter, Set.mem_ofPred_eq] using equal
  rw [M.eval_binaryRowName I C one (projection.projectedFilter H) hone',
    M.eval_binaryRowName I C one (projection.projectedFilter H) hone'] at same
  exact M.binaryGenericRow_ne pairing unions powers separation infinite choice
    hI hC hi hj distinct uncountable (projection.projectedFilter H) generic same

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u})

theorem projectedBinaryRows_uniqueFiber_incompatible
    {Upper G : Type u} [PartialOrder Upper] [Group G]
    (upper : Presentation Upper) (t : Presentation G)
    (a : PosetAction G Upper) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (upperCarrier : (upper).carrier ∈ M.sets)
    (maps : a.conditionMapFamily upper t ∈ M.sets) :
    let R := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    let lower := SetMembers.presentation R
    ∀ (restriction : Upper →o SetMembers R) (inclusion : SetMembers R ↪o Upper)
      (_projection : CompleteProjection restriction inclusion),
      (upper).graph lower restriction ∈ M.sets →
      ∀ (one : SetMembers R), (∀ q : SetMembers R, q ≤ one) →
      ∀ (S x f : (M.nameDomain upper).names) (g : G),
        a.act upper g S.val = S.val → a.act upper g f.val = f.val →
        ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          x.val = Name.rename upper inclusion (M.binaryRowName I C one i) →
          a.act upper g x.val = Name.rename upper inclusion (M.binaryRowName I C one j) →
          ∀ p : Upper,
            Forces (M.nameDomain upper) (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula
              (extend S (extend x (extend f Fin.elim0))) p →
            ¬ Compatible p (a.iso g p) := by
  let R := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  let lower := SetMembers.presentation R
  dsimp only
  intro restriction inclusion projection restrictionGround one greatest S x f g fixedS fixedF
    i hi j hj distinct originalRow movedRow p forced compatible
  obtain ⟨r, rp, rgp⟩ := compatible
  obtain ⟨H, hr, _coded, ordinary, _symmetric⟩ :=
    M.exists_joint_generic upper a F small upperCarrier r
  have closed : ∀ g tau, tau ∈ (M.nameDomain upper).names →
      a.act upper g tau ∈ (M.nameDomain upper).names :=
    M.act_mem upper a t pairing unions powers separation collection upperCarrier maps
  have equal := a.uniqueFiber_eq_of_fixed_names upper (M.nameDomain upper) closed
    g S x f fixedS fixedF p forced H ordinary (H.upward hr rp) (H.upward hr rgp)
  rw [movedRow, originalRow] at equal
  have hone : H.mem (inclusion one) :=
    H.upward hr ((projection.le_include_iff r one).2 (greatest (restriction r)))
  exact M.completeProjection_binaryRowValues_ne upper pairing unions powers separation infinite
    choice hI hC uncountable upperCarrier restriction inclusion projection restrictionGround
    H ordinary one hone i hi j hj distinct equal

end PartitionPilot.Forcing.TransitiveGround

end

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

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {L G Upper : Type u}
variable [Group G] [PartialOrder L] [OrderBot L] [PartialOrder Upper]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (upper : Presentation Upper) (e : PosetAction G Upper)
variable (upperCarrier : upper.carrier ∈ M.sets)

include directed collection upperCarrier

theorem liftedInternalRowSet_mem :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let R := M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let lower := SetMembers.presentation R
    ∀ (inclusion : SetMembers R → Upper), lower.graph upper inclusion ∈ M.sets →
      (∀ g p, inclusion (act.iso g p) = e.iso g (inclusion p)) →
      ∀ H : ConditionFilter Upper,
        Name.eval {p | H.mem p} (Name.rename upper inclusion (M.internalRowSetName s C hL)) ∈
          (M.symmetricExtension upper e (a.principalSupportFamily ⊥ directed) H).sets := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  dsimp only
  intro inclusion inclusionGround equivariant H
  apply (M.mem_symmetricExtension upper e (a.principalSupportFamily ⊥ directed) H _).2
  have lowerGround := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC)
    (M.natSetCode_mem separation infinite 2)
  refine ⟨_, M.rename_between_mem _ upper pairing unions powers separation collection
    lowerGround upperCarrier inclusion inclusionGround _
      (M.internalRowSetName_mem s C pairing unions powers separation collection infinite hL hC), ?_, rfl⟩
  exact (M.internalRowSetName_hs a s b C pairing unions powers separation infinite hL hC hG
    graph directed).rename e upper inclusion equivariant

theorem liftedInternalRows_chooser_witness
    (order : s.conditionOrder ∈ M.sets) (unbounded : ∀ B : L, ∃ i : L, ¬ i ≤ B) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let R := M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let lower := SetMembers.presentation R
    ∀ (restriction : Upper →o SetMembers R) (inclusion : SetMembers R ↪o Upper)
      (_projection : CompleteProjection restriction inclusion),
      lower.graph upper inclusion ∈ M.sets →
      (∀ g p, inclusion (act.iso g p) = e.iso g (inclusion p)) →
      ∀ (H : ConditionFilter Upper), H.GenericFor (formulaFamily (M.nameDomain upper)) →
      let N := M.symmetricExtension upper e (a.principalSupportFamily ⊥ directed) H
      let rows := Name.eval {p | H.mem p} (Name.rename upper inclusion (M.internalRowSetName s C hL))
      ∀ f ∈ N.sets,
        (∀ S ∈ N.sets, S ⊆ rows → S.Nonempty →
          ∃ x ∈ S, ZFSet.pair S x ∈ f ∧ ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x) →
        ∃ (B : L) (i : {i : L // i ≠ ⊥})
          (sn xn fn : (M.nameDomain upper).names),
          ¬ i.val ≤ B ∧
          sn.val = Name.rename upper inclusion (M.internalOutsideRowsName s C hL B) ∧
          xn.val = Name.rename upper inclusion (M.internalRowName s C hL i) ∧
          a.principalFix B ≤ e.stabilizer upper sn.val ∧
          a.principalFix B ≤ e.stabilizer upper fn.val ∧
          ∃ p : Upper, H.mem p ∧
            Forces (M.nameDomain upper) (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula
              (extend sn (extend xn (extend fn Fin.elim0))) p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let R := M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let lower := SetMembers.presentation R
  dsimp only
  intro restriction inclusion projection inclusionGround equivariant H ordinary f hf selection
  let F := a.principalSupportFamily (⊥ : L) directed
  let N := M.symmetricExtension upper e F H
  let K := projection.projectedFilter H
  have lowerGround : lower.carrier ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers
    separation infinite (M.prod_mem pairing unions powers separation
      (M.nonbottom_carrier_mem s separation hL) hC) (M.natSetCode_mem separation infinite 2)
  have renameGround (tau : Name lower) (ground : tau.val ∈ M.sets) :
      (Name.rename upper inclusion tau).val ∈ M.sets :=
    M.rename_between_mem lower upper pairing unions powers separation collection lowerGround
      upperCarrier inclusion inclusionGround tau ground
  have evalLift (tau : Name lower) :
      Name.eval {p | H.mem p} (Name.rename upper inclusion tau) = Name.eval {p | K.mem p} tau :=
    Name.eval_rename upper inclusion {p | H.mem p} tau
  obtain ⟨fname, groundF, hsF, rfl⟩ := (M.mem_symmetricExtension upper e F H f).1 hf
  obtain ⟨B, fixedF⟩ := hsF.symmetric
  let Sname := Name.rename upper inclusion (M.internalOutsideRowsName s C hL B)
  have groundS : Sname.val ∈ M.sets := renameGround _
    (M.internalOutsideRowsName_mem s C pairing unions powers separation collection infinite hL hC order B)
  have hsS : HereditarilySymmetric e upper F Sname :=
    (M.internalOutsideRowsName_hs a s b C pairing unions powers separation infinite hL hC hG graph
      directed B).rename e upper inclusion equivariant
  have hS : Name.eval {p | H.mem p} Sname ∈ N.sets :=
    (M.mem_symmetricExtension upper e F H _).2 ⟨Sname, groundS, hsS, rfl⟩
  have subset : Name.eval {p | H.mem p} Sname ⊆
      Name.eval {p | H.mem p} (Name.rename upper inclusion (M.internalRowSetName s C hL)) := by
    change Name.eval {p | H.mem p} (Name.rename upper inclusion _) ⊆ _
    rw [evalLift, evalLift]
    exact M.eval_internalOutsideRowsName_subset s C hL B K
  have nonempty : (Name.eval {p | H.mem p} Sname).Nonempty := by
    change (Name.eval {p | H.mem p} (Name.rename upper inclusion _)).Nonempty
    rw [evalLift]
    exact M.eval_internalOutsideRowsName_nonempty s C hL B (unbounded B) K
  obtain ⟨x, hx, chosen, unique⟩ := selection _ hS subset nonempty
  have hxK : x ∈ Name.eval {p | K.mem p} (M.internalOutsideRowsName s C hL B) := by
    rw [← evalLift]
    exact hx
  obtain ⟨i, outside, rowValue⟩ := (M.mem_eval_internalOutsideRowsName s C hL B K x).1 hxK
  let rowName := Name.rename upper inclusion (M.internalRowName s C hL i)
  have groundRow : rowName.val ∈ M.sets := renameGround _
    (M.internalRowName_mem s C pairing unions powers separation collection infinite hL hC i)
  let sn : (M.nameDomain upper).names := ⟨Sname, groundS⟩
  let xn : (M.nameDomain upper).names := ⟨rowName, groundRow⟩
  let fn : (M.nameDomain upper).names := ⟨fname, groundF⟩
  let env := extend sn (extend xn (extend fn Fin.elim0))
  have rowEq : Name.eval {p | H.mem p} rowName = x :=
    (evalLift _).trans ((M.eval_internalRowName s C hL i K).trans rowValue)
  have truth : Realize ((M.nameDomain upper).values {p | H.mem p})
      (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula (evalAssignment {p | H.mem p} env) := by
    apply (realize_uniqueFiber_values (M.nameDomain upper) {p | H.mem p} 0 1 2 env).2
    change Name.eval {p | H.mem p} rowName ∈ Name.eval {p | H.mem p} Sname ∧
      ZFSet.pair (Name.eval {p | H.mem p} Sname) (Name.eval {p | H.mem p} rowName) ∈
        Name.eval {p | H.mem p} fname ∧
      ∀ z ∈ Name.eval {p | H.mem p} Sname,
        ZFSet.pair (Name.eval {p | H.mem p} Sname) z ∈ Name.eval {p | H.mem p} fname →
          z = Name.eval {p | H.mem p} rowName
    rw [rowEq]
    exact ⟨hx, chosen, unique⟩
  obtain ⟨p, hp, forced⟩ := (forcing_truth (M.nameDomain upper) H ordinary
    (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula env).1 truth
  refine ⟨B, i, sn, xn, fn, outside, rfl, rfl, ?_, fixedF, p, hp, forced⟩
  intro g fixed
  change e.act upper g (Name.rename upper inclusion _) = Name.rename upper inclusion _
  rw [act.act_rename_of_equivariant e lower upper inclusion equivariant]
  exact congrArg (Name.rename upper inclusion)
    (M.internalOutsideRowsName_action a s b C pairing unions powers separation infinite hL hC hG
      graph B g fixed)

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

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RepresentativeIndexSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
universe u

theorem stageOneRawTests_mixed_union (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})
    {A B lower : ZFSet.{u}} (first : stageOneRawTests M d A lower)
    (second : stageOneRawTests M d B lower)
    (cross : stageOneRawCrossCollisions M d A B lower) :
    stageOneRawTests M d (A ∪ B) lower := by
  refine ⟨?_, ?_⟩
  · intro t ht u hu w hw entry
    exact (ZFSet.mem_union.1 entry).elim
      (first.1 t ht u hu w hw) (second.1 t ht u hu w hw)
  · intro t ht u hu u' hu' w hw w' hw' entry entry'
    rcases ZFSet.mem_union.1 entry with entry | entry
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact first.2 t ht u hu u' hu' w hw w' hw' entry entry'
      · exact (cross t ht u hu u' hu' w hw w' hw' entry entry').1
    · rcases ZFSet.mem_union.1 entry' with entry' | entry'
      · exact (cross t ht u' hu' u hu w' hw' w hw entry' entry).2
      · exact second.2 t ht u hu u' hu' w hw w' hw' entry entry'





end PartitionPilot.Forcing




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ForcingHistoryTestDecomposition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe u

theorem forcingHistoryConditionCode_empty (M : TransitiveGround.{u})
    (history levels z : ZFSet.{u}) : ForcingHistoryConditionCode M ∅ history levels z :=
  fun alpha member => False.elim (ZFSet.notMem_empty alpha member)

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundForcingHistorySuccessors
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

theorem forcingHistoryConditions_empty (rows I T history levels : ZFSet.{u}) :
    M.forcingHistoryConditions rows I T ∅ history levels = M.stageOneCandidateBound rows I T := by
  apply ZFSet.ext
  intro z
  rw [M.mem_forcingHistoryConditions]
  exact ⟨And.left, fun member => ⟨member, forcingHistoryConditionCode_empty M history levels z⟩⟩

theorem forcingHistoryConditions_initial {rows : ZFSet.{u}} (hRows : rows ∈ M.sets)
    (T history levels : ZFSet.{u}) :
    M.forcingHistoryConditions rows ∅ T ∅ history levels = ZFSet.prod rows {∅} := by
  rw [M.forcingHistoryConditions_empty]
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨row, hrow, A, _, subset, _, rfl⟩ := (M.mem_stageOneCandidateBound _ _ _ _).1 member
    have empty : A = ∅ := by
      apply ZFSet.ext
      intro x
      constructor
      · intro hx
        obtain ⟨t, ht, _, _, _, _, _⟩ := (mem_stageOneAssignments ∅ T x).1 (subset hx)
        exact False.elim (ZFSet.notMem_empty t ht)
      · intro hx
        exact False.elim (ZFSet.notMem_empty x hx)
    exact ZFSet.pair_mem_prod.2 ⟨hrow, ZFSet.mem_singleton.2 empty⟩
  · intro member
    obtain ⟨row, hrow, A, hA, rfl⟩ := ZFSet.mem_prod.1 member
    obtain rfl := ZFSet.mem_singleton.1 hA
    exact M.stageOneCandidateBound_empty hRows hrow

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalSeparatedActors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem decoded_unbounded
    (growth : ∀ x ∈ geometry.carrier, ∃ y ∈ geometry.carrier,
      ZFSet.pair x y ∈ geometry.order ∧ ¬ ZFSet.pair y x ∈ geometry.order) :
    letI := geometry.meet.order.toPartialOrder
    ∀ x : SetMembers geometry.carrier, ∃ y : SetMembers geometry.carrier, ¬ y ≤ x := by
  let := geometry.meet.order.toPartialOrder
  intro x
  obtain ⟨y, hy, _, strict⟩ := growth _ (SetMembers.raw_mem x)
  refine ⟨SetMembers.ofMem y hy, ?_⟩
  change ¬ ZFSet.pair (SetMembers.raw (SetMembers.ofMem y hy)) (SetMembers.raw x) ∈ geometry.order
  simpa only [SetMembers.raw_ofMem] using strict

end GroundMainFinalGeometry

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RefinementBirthEnumerationFairness
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

theorem refinementHistoryForcing_initial {rows : ZFSet.{u}} (hRows : rows ∈ M.sets)
    (T history : ZFSet.{u}) : M.refinementHistoryForcing rows T ∅ history = ZFSet.prod rows {∅} := by
  have indices : refinementDataHistoryIndices ∅ history = ∅ := by
    apply ZFSet.ext
    intro x
    constructor
    · intro member
      obtain ⟨alpha, impossible, _⟩ := (mem_refinementHistoryIndices ∅ _ x).1 member
      exact False.elim (ZFSet.notMem_empty alpha impossible)
    · intro member
      exact False.elim (ZFSet.notMem_empty x member)
  rw [refinementHistoryForcing, indices]
  exact M.forcingHistoryConditions_initial hRows T history _

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRowCompleteProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {R : Type u}
variable (c : Presentation R) (T stages history : ZFSet.{u})
local notation "Q" => M.refinementHistoryForcing c.carrier T stages history
local notation "upper" => SetMembers.presentation Q

theorem refinementHistoryRowFunction_graph :
    (upper).graph c (M.refinementHistoryRowFunction c T stages history) =
      rowAssignmentRows Q c.carrier (Q).sUnion.sUnion :=
  (upper).graph_decodeFunction c _ _

variable [PartialOrder R]

variable (run : RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "incl" => M.refinementHistoryRowInclusion c run.carriers ordinal carrier
local notation "res" => M.refinementHistoryRowFunction c T stages history

theorem refinementHistoryRow_retract (q : R) : res (incl q) = q :=
  M.refinementHistoryRowFunction_code c T stages history (incl q) q ∅
    (M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier q)

theorem refinementHistoryRow_le_include :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    ∀ p : SetMembers Q, ∀ q : R,
      p ≤ M.refinementHistoryRowEmbedding c T stages history run ordinal carrier q ↔ res p ≤ q := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  intro p q
  obtain ⟨A, pCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history p
  have incCode : SetMembers.raw (incl q) = ZFSet.pair (c.encode q) ∅ :=
    M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier q
  have hp := SetMembers.raw_mem p
  have hq := SetMembers.raw_mem (incl q)
  rw [pCode] at hp
  rw [incCode] at hq
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw (incl q)) ∈ _ ↔ res p ≤ q
  rw [pCode, incCode, M.pair_mem_refinementHistoryOrder]
  constructor
  · intro below
    exact (c.pair_mem_conditionOrder _ _).1 below.2.2.1
  · intro below
    exact ⟨hp, hq, (c.pair_mem_conditionOrder _ _).2 below,
      fun z hz => (ZFSet.notMem_empty z hz).elim⟩

theorem refinementHistoryRowInclusion_graph :
    c.graph upper incl = c.graph c.pairEmpty id := by
  apply ZFSet.ext
  intro z
  rw [c.mem_graph, c.mem_graph]
  constructor
  · rintro ⟨p, rfl⟩
    rw [M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier]
    exact ⟨p, rfl⟩
  · rintro ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    rw [M.refinementHistoryRowInclusion_encode c run.carriers ordinal carrier]
    rfl

theorem refinementHistoryRowGraphs_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hQ : Q ∈ M.sets) :
    (upper).graph c res ∈ M.sets ∧ c.graph upper incl ∈ M.sets := by
  constructor
  · rw [M.refinementHistoryRowFunction_graph]
    exact M.rowAssignmentRows_mem pairing unions powers separation hQ carrier
      (M.union_mem unions (M.union_mem unions hQ))
  · rw [M.refinementHistoryRowInclusion_graph c T stages history run ordinal carrier]
    exact M.pairEmpty_forwardGraph_mem pairing unions powers separation c carrier

private theorem assignmentCut_zero (levels A : ZFSet.{u}) : assignmentCut levels ∅ A = ∅ := by
  apply ZFSet.ext
  intro z
  simp only [mem_assignmentCut, ZFSet.notMem_empty, false_and, exists_false, and_false]

theorem refinementHistoryRow_completeProjection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
    (top : ZFSet.{u}) (topMem : top ∈ c.carrier)
    (topRows : ∀ row ∈ c.carrier, ZFSet.pair row top ∈ c.conditionOrder)
    (mono : ∀ beta (fields : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode fields) ∈ history →
      ∀ A lower stronger, stageOneRawTests M fields A lower →
        ZFSet.pair stronger lower ∈ fields 8 → stageOneRawTests M fields A stronger) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
    CompleteProjection (M.refinementHistoryRowRestriction c T stages history)
      (M.refinementHistoryRowEmbedding c T stages history run ordinal carrier) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages history
  refine ⟨M.refinementHistoryRow_retract c T stages history run ordinal carrier,
    M.refinementHistoryRow_le_include c T stages history run ordinal carrier, ?_⟩
  intro p q below
  let Q0 := M.refinementHistoryForcing c.carrier T ∅ (graphRestriction ∅ history)
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T ∅ (graphRestriction ∅ history)
  have zeroSubset : (∅ : ZFSet.{u}) ⊆ stages := fun z hz => (ZFSet.notMem_empty z hz).elim
  have hEmpty : (∅ : ZFSet.{u}) ∈ M.sets := M.empty_mem ⟨c.carrier, carrier⟩
  let cut := run.restriction ordinal ordinalSetProperty_empty zeroSubset c.conditionOrder_code
  have projection := run.completeProjection ordinal ordinalSetProperty_empty zeroSubset
    pairing unions powers separation infinite choice hStages hHistory hT hEmpty carrier
    top topMem topRows mono c.conditionOrder_code
  have zeroCode : ZFSet.pair (c.encode q) ∅ ∈ Q0 := by
    change ZFSet.pair (c.encode q) ∅ ∈ M.refinementHistoryForcing c.carrier T ∅ (graphRestriction ∅ history)
    rw [M.refinementHistoryForcing_initial carrier T (graphRestriction ∅ history)]
    exact ZFSet.pair_mem_prod.2 ⟨c.encode_mem q, ZFSet.mem_singleton.2 rfl⟩
  let q0 : SetMembers Q0 := SetMembers.ofMem (ZFSet.pair (c.encode q) ∅) zeroCode
  have q0Code : SetMembers.raw q0 = ZFSet.pair (c.encode q) ∅ := SetMembers.raw_ofMem _ _
  obtain ⟨A, pCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history p
  have cutCode : SetMembers.raw (cut p) = ZFSet.pair (c.encode (res p)) ∅ := by
    change SetMembers.raw (run.restrictionFunction ordinal ordinalSetProperty_empty zeroSubset p) = _
    rw [run.restrictionFunction_raw ordinal ordinalSetProperty_empty zeroSubset p (c.encode (res p)) A pCode,
      assignmentCut_zero]
  have cutMember := SetMembers.raw_mem (cut p)
  rw [cutCode] at cutMember
  have belowZero : q0 ≤ cut p := by
    change ZFSet.pair (SetMembers.raw q0) (SetMembers.raw (cut p)) ∈ _
    rw [q0Code, cutCode, M.pair_mem_refinementHistoryOrder]
    exact ⟨zeroCode, cutMember, (c.pair_mem_conditionOrder _ _).2 below, fun _ hz => hz⟩
  obtain ⟨r, rp, exactCut⟩ := projection.lift p q0 belowZero
  refine ⟨r, rp, ?_⟩
  obtain ⟨B, rCode⟩ := M.refinementHistoryRowFunction_coordinates c T stages history r
  have cutR : SetMembers.raw (cut r) = ZFSet.pair (c.encode (res r)) ∅ := by
    change SetMembers.raw (run.restrictionFunction ordinal ordinalSetProperty_empty zeroSubset r) = _
    rw [run.restrictionFunction_raw ordinal ordinalSetProperty_empty zeroSubset r (c.encode (res r)) B rCode,
      assignmentCut_zero]
  have equal := congrArg SetMembers.raw exactCut
  change SetMembers.raw (cut r) = SetMembers.raw q0 at equal
  rw [cutR, q0Code] at equal
  exact c.injective (ZFSet.pair_injective equal).1

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStageTwoNamePositionSupports
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace CompleteProjection
universe u
variable {G P Q : Type u} [Group G] [PartialOrder P] [PartialOrder Q]
variable {restriction : Q →o P} {inclusion : P ↪o Q}

theorem inclusion_equivariant (projection : CompleteProjection restriction inclusion)
    (upper : PosetAction G Q) (lower : PosetAction G P)
    (equivariant : ∀ g q, restriction (upper.iso g q) = lower.iso g (restriction q))
    (g : G) (p : P) : upper.iso g (inclusion p) = inclusion (lower.iso g p) := by
  have forward (h : G) (q : P) : upper.iso h (inclusion q) ≤ inclusion (lower.iso h q) := by
    apply (projection.le_include_iff _ _).2
    rw [equivariant, projection.retract]
  apply le_antisymm (forward g p)
  have back := (upper.iso g).monotone (forward g⁻¹ (lower.iso g p))
  have cancel : lower.iso g⁻¹ (lower.iso g p) = p := by
    rw [← lower.mul, inv_mul_cancel, lower.one]
  rw [cancel, ← upper.mul, mul_inv_cancel, upper.one] at back
  exact back

end CompleteProjection

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundRecursiveRefinementMixedUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable {row rowA rowB A B : ZFSet.{u}}
local notation "levels" => refinementDataHistoryLevels stages history T
include run

theorem mixed_union_mem_of_candidates (ordinal : ordinalSetProperty stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ C lower stronger, stageOneRawTests M d C lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d C stronger)
    (first : ZFSet.pair rowA A ∈ M.refinementHistoryForcing rows T stages history)
    (second : ZFSet.pair rowB B ∈ M.refinementHistoryForcing rows T stages history)
    (rowBelowA : ZFSet.pair row rowA ∈ rowOrder)
    (rowBelowB : ZFSet.pair row rowB ∈ rowOrder)
    (cross : ∀ beta ∈ stages, ∀ d : Fin 15 → ZFSet.{u},
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ZFSet.pair row (assignmentCut levels beta (A ∪ B)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history) →
      stageOneRawCrossCollisions M d A B
        (ZFSet.pair row (assignmentCut levels beta (A ∪ B))))
    (candidate : ZFSet.pair row (A ∪ B) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T)
    (candidates : ∀ gamma ∈ stages, ZFSet.pair row (assignmentCut levels gamma (A ∪ B)) ∈
      M.stageOneCandidateBound rows
        (refinementDataHistoryIndices gamma (graphRestriction gamma history)) T) :
    ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing rows T stages history := by
  have subsetA : A ⊆ A ∪ B := fun _ h => ZFSet.mem_union.2 (Or.inl h)
  have subsetB : B ⊆ A ∪ B := fun _ h => ZFSet.mem_union.2 (Or.inr h)
  have firstTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 first).2
  have secondTests := ((M.mem_refinementHistoryForcing rows T stages history _).1 second).2
  have step (beta : ZFSet.{u}) (hbeta : beta ∈ stages) (d : Fin 15 → ZFSet.{u})
      (entry : ZFSet.pair beta (refinementFormulaDataCode d) ∈ history)
      (proved : ZFSet.pair row (assignmentCut levels beta (A ∪ B)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history)) :
      stageOneRawTests M d (A ∪ B) (ZFSet.pair row (assignmentCut levels beta (A ∪ B))) := by
    have storedA := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 firstTests
      beta hbeta (refinementFormulaDataCode d) entry
    have checkedA := (stageTwoConditionCode_pair_iff M d _ beta rowA A).1
      ((packedSuccessorConditionCode_code_iff M _ beta d _).1 storedA)
    have storedB := (forcingHistoryConditionCode_lookup_iff run.carriers.data.function).1 secondTests
      beta hbeta (refinementFormulaDataCode d) entry
    have checkedB := (stageTwoConditionCode_pair_iff M d _ beta rowB B).1
      ((packedSuccessorConditionCode_code_iff M _ beta d _).1 storedB)
    have belowA : ZFSet.pair (ZFSet.pair row (assignmentCut levels beta (A ∪ B)))
        (ZFSet.pair rowA (assignmentCut levels beta A)) ∈ d 8 := by
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem first hbeta, rowBelowA, assignmentCut_mono subsetA⟩
    have belowB : ZFSet.pair (ZFSet.pair row (assignmentCut levels beta (A ∪ B)))
        (ZFSet.pair rowB (assignmentCut levels beta B)) ∈ d 8 := by
      rw [run.order beta d entry]
      exact (M.pair_mem_refinementHistoryOrder rows rowOrder T beta (graphRestriction beta history)
        _ _ _ _).2 ⟨proved, run.carriers.cut_mem second hbeta, rowBelowB, assignmentCut_mono subsetB⟩
    exact stageOneRawTests_mixed_union M d
      (mono beta d entry A _ _ checkedA.2 belowA) (mono beta d entry B _ _ checkedB.2 belowB)
      (cross beta hbeta d entry proved)
  have earlier : ∀ gamma ∈ stages, ZFSet.pair row (assignmentCut levels gamma (A ∪ B)) ∈
      M.refinementHistoryForcing rows T gamma (graphRestriction gamma history) := by
    intro gamma
    induction gamma using ZFSet.inductionOn with
    | h gamma ih =>
      intro hgamma
      apply (M.mem_refinementHistoryForcing rows T gamma (graphRestriction gamma history) _).2
      refine ⟨candidates gamma hgamma, ?_⟩
      intro beta hbeta
      have betaFull := ordinal.1 gamma hgamma beta hbeta
      have betaSubset := ordinal.2 gamma hgamma beta hbeta
      obtain ⟨data, entry⟩ := run.carriers.data.function.total betaFull
      obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
      have proved := ih beta hbeta betaFull
      have sameCut := run.carriers.data.prefix_cut (ordinal.1 gamma hgamma) betaSubset
        (assignmentCut levels gamma (A ∪ B))
      refine ⟨refinementFormulaDataCode d, pair_mem_graphRestriction.2 ⟨entry, hbeta⟩, ?_⟩
      apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
      apply (stageTwoConditionCode_pair_iff M d _ beta row _).2
      rw [sameCut, assignmentCut_nested betaSubset]
      refine ⟨(run.carriers.carrier beta d entry).symm ▸ proved, ?_⟩
      exact stageOneRawTests_transfer M d _ (step beta betaFull d entry proved)
        (fun _ _ _ _ _ _ member => assignmentCut_subset levels gamma (A ∪ B) member)
  apply (M.mem_refinementHistoryForcing rows T stages history _).2
  refine ⟨candidate, ?_⟩
  intro beta hbeta
  obtain ⟨data, entry⟩ := run.carriers.data.function.total hbeta
  obtain ⟨d, rfl⟩ := run.carriers.data.decoded beta data entry
  refine ⟨refinementFormulaDataCode d, entry, ?_⟩
  apply (packedSuccessorConditionCode_code_iff M _ beta d _).2
  apply (stageTwoConditionCode_pair_iff M d _ beta row _).2
  exact ⟨(run.carriers.carrier beta d entry).symm ▸ earlier beta hbeta,
    step beta hbeta d entry (earlier beta hbeta)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory



namespace PartitionPilot.Forcing.RecursiveRefinementOrderHistory
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {rows rowOrder T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementOrderHistory M rows rowOrder T stages history)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hStages : stages ∈ M.sets) (hHistory : history ∈ M.sets) (hT : T ∈ M.sets)
include run pairing unions powers separation infinite choice hStages hHistory hT

theorem mixed_union_extension (ordinal : ordinalSetProperty stages)
    (mono : ∀ beta (d : Fin 15 → ZFSet.{u}),
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ∀ C lower stronger, stageOneRawTests M d C lower →
        ZFSet.pair stronger lower ∈ d 8 → stageOneRawTests M d C stronger)
    (rowOrderLaw : PartialOrderCode rows rowOrder) {row rowA rowB A B : ZFSet.{u}}
    (first : ZFSet.pair rowA A ∈ M.refinementHistoryForcing rows T stages history)
    (second : ZFSet.pair rowB B ∈ M.refinementHistoryForcing rows T stages history)
    (rowBelowA : ZFSet.pair row rowA ∈ rowOrder)
    (rowBelowB : ZFSet.pair row rowB ∈ rowOrder)
    (cross : ∀ beta ∈ stages, ∀ d : Fin 15 → ZFSet.{u},
      ZFSet.pair beta (refinementFormulaDataCode d) ∈ history →
      ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages history T) beta (A ∪ B)) ∈
        M.refinementHistoryForcing rows T beta (graphRestriction beta history) →
      stageOneRawCrossCollisions M d A B (ZFSet.pair row
        (assignmentCut (refinementDataHistoryLevels stages history T) beta (A ∪ B)))) :
    ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing rows T stages history ∧
      ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowA A) ∈
        M.refinementHistoryOrder rows rowOrder T stages history ∧
      ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowB B) ∈
        M.refinementHistoryOrder rows rowOrder T stages history := by
  have firstCandidate := ((M.mem_refinementHistoryForcing rows T stages history _).1 first).1
  have secondCandidate := ((M.mem_refinementHistoryForcing rows T stages history _).1 second).1
  obtain ⟨_, hA, subsetA, smallA⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 firstCandidate
  obtain ⟨_, hB, subsetB, smallB⟩ := (M.pair_mem_stageOneCandidateBound _ _ _ _ _).1 secondCandidate
  have hrow := (ZFSet.pair_mem_prod.1 (rowOrderLaw.relation rowBelowA)).1
  have candidate : ZFSet.pair row (A ∪ B) ∈
      M.stageOneCandidateBound rows (refinementDataHistoryIndices stages history) T := by
    apply (M.pair_mem_stageOneCandidateBound _ _ _ _ _).2
    refine ⟨hrow, M.binary_union_mem pairing unions hA hB, ?_,
      M.groundCountable_binary_union pairing unions powers separation infinite choice hA hB smallA smallB⟩
    intro z member
    exact (ZFSet.mem_union.1 member).elim (fun h => subsetA h) (fun h => subsetB h)
  have hLevels := M.refinementDataHistoryLevels_mem pairing unions powers separation hStages hHistory hT
  have member := run.mixed_union_mem_of_candidates ordinal mono first second rowBelowA rowBelowB cross candidate
    (fun beta hbeta => M.refinementDataHistoryCandidate_cut separation run.carriers.data
      (ordinal.1 beta hbeta) hLevels (M.transitive hStages hbeta) (M.omega_mem separation infinite) candidate)
  refine ⟨member, ?_, ?_⟩
  · exact (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
      ⟨member, first, rowBelowA, fun _ h => ZFSet.mem_union.2 (Or.inl h)⟩
  · exact (M.pair_mem_refinementHistoryOrder rows rowOrder T stages history _ _ _ _).2
      ⟨member, second, rowBelowB, fun _ h => ZFSet.mem_union.2 (Or.inr h)⟩

end PartitionPilot.Forcing.RecursiveRefinementOrderHistory

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedCopyUnions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


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

theorem semanticStructuralTrace_mixed_union_extension
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    ∀ row rowA rowB A B : ZFSet.{u},
      ZFSet.pair rowA A ∈ M.refinementHistoryForcing c.carrier T stages packed →
      ZFSet.pair rowB B ∈ M.refinementHistoryForcing c.carrier T stages packed →
      ZFSet.pair row rowA ∈ c.conditionOrder →
      ZFSet.pair row rowB ∈ c.conditionOrder →
      (∀ beta ∈ stages, ∀ data : Fin 15 → ZFSet.{u},
        ZFSet.pair beta (refinementFormulaDataCode data) ∈ packed →
        ZFSet.pair row (assignmentCut (refinementDataHistoryLevels stages packed T) beta (A ∪ B)) ∈
          M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed) →
        stageOneRawCrossCollisions M data A B (ZFSet.pair row
          (assignmentCut (refinementDataHistoryLevels stages packed T) beta (A ∪ B)))) →
      ZFSet.pair row (A ∪ B) ∈ M.refinementHistoryForcing c.carrier T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowA A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
        ZFSet.pair (ZFSet.pair row (A ∪ B)) (ZFSet.pair rowB B) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  dsimp only
  intro row rowA rowB A B first second rowBelowA rowBelowB cross
  have run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  exact run.mixed_union_extension pairing unions powers separation infinite choice hs hPacked hT
    ordinal mono c.conditionOrder_code first second rowBelowA rowBelowB cross

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
include hs hh ordinal trace
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "upperQ" => M.refinementHistoryForcing c.carrier T stages packed
local notation "image" => M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 stages history
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace

theorem semanticStructuralTrace_aligned_copy_union
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r oldRow row : R) (A oldA : ZFSet.{u}) (g h : G) (D X V : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair (c.encode r) A))
    (belowOld : row ≤ oldRow) (oldBelowG : oldRow ≤ a.iso g r) (belowH : row ≤ a.iso h r)
    (contains : image (t.encode g) A ⊆ oldA)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (overlap : meet (d.iso h D) X = d.iso h V)
    (meetLeft : meet (d.iso h D) X ≤ d.iso h D)
    (meetRight : meet (d.iso h D) X ≤ X)
    (meetGreatest : ∀ z : L, z ≤ d.iso h D → z ≤ X → z ≤ meet (d.iso h D) X)
    (newData : ∀ z ∈ image (t.encode h) A, ZFSet.pair z (b.encode (d.iso h D)) ∈
      stageOneDataBounds (image (t.encode h) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (oldData : ∀ z ∈ oldA, ZFSet.pair z (b.encode X) ∈
      stageOneDataBounds oldA I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (descent : ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member ordinal member
      let subset := (And.left ordinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
      let lower := SetMembers.presentation Q
      let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : L) (x y : (M.nameDomain lower).names),
          d.principalFix v ≤ act.stabilizer lower x.val →
          d.principalFix w ≤ act.stabilizer lower y.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) x.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau.val ∧
            d.principalFix (meet v w) ≤ act.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) :
    ZFSet.pair (c.encode row) (image (t.encode h) A ∪ oldA) ∈ upperQ ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h) A ∪ oldA))
      (ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h) A ∪ oldA))
      (ZFSet.pair (c.encode oldRow) oldA) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let upperAct := M.semanticStructuralAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  let original : SetMembers upperQ := SetMembers.ofMem _ source
  have originalCode : SetMembers.raw original = ZFSet.pair (c.encode r) A := SetMembers.raw_ofMem _ _
  have movedCode := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace h original r A originalCode
  have movedSource : ZFSet.pair (c.encode (a.iso h r)) (image (t.encode h) A) ∈ upperQ :=
    movedCode ▸ SetMembers.raw_mem (upperAct.iso h original)
  apply M.semanticStructuralTrace_mixed_union_extension c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace infinite choice
    (c.encode row) (c.encode (a.iso h r)) (c.encode oldRow) (image (t.encode h) A) oldA
    movedSource oldSource ((c.pair_mem_conditionOrder _ _).2 belowH)
    ((c.pair_mem_conditionOrder _ _).2 belowOld)
  intro alpha member data stored validCut
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member ordinal member
  let subset := (And.left ordinal) alpha member
  let lowerPacked := graphRestriction alpha packed
  let Q := M.refinementHistoryForcing c.carrier T alpha lowerPacked
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let act := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hh trace hAlpha cutOrdinal subset
  let fields := M.refinementLevelFormulaData act lower b d alpha T T2 valid
  have canonicalStored := M.semanticStructuralPrefix_refinementData_entry c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have same : data = fields := refinementFormulaDataCode_injective
    ((run).carriers.data.function.unique stored canonicalStored)
  subst data
  exact M.semanticStructuralPrefix_aligned_copy_crossCollisions c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member infinite choice small meet I S mu positions tuples range support
    r oldRow row A oldA g h D X V source oldSource prepared belowOld oldBelowG belowH contains
    relative overlap meetLeft meetRight meetGreatest (descent alpha member) newData oldData validCut

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticOrdinalRowOrbitCovers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet




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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T →
  (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 →
  (a.act c.pairEmpty g tau).val ∈ T2)
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
local notation "upper" => SetMembers.presentation Q
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
  T T2 ordinal trace
local notation "rowFunction" => M.refinementHistoryRowFunction c T stages packed
local notation "rowInclusion" => M.refinementHistoryRowInclusion c (RecursiveRefinementOrderHistory.carriers run) ordinal carrier
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace
include hs hh ordinal trace infinite choice

theorem semanticStructuralTrace_rowProjection :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    CompleteProjection (M.refinementHistoryRowRestriction c T stages packed)
        (M.refinementHistoryRowEmbedding c T stages packed run ordinal carrier) ∧
      (upper).graph c rowFunction ∈ M.sets ∧
      c.graph upper rowInclusion ∈ M.sets ∧
      (∀ p row A, SetMembers.raw p = ZFSet.pair (c.encode row) A → rowFunction p = row) ∧
      (∀ row, (upper).encode (rowInclusion row) = ZFSet.pair (c.encode row) ∅) ∧
      (∀ g p, rowFunction ((upperAct).iso g p) = a.iso g (rowFunction p)) ∧
      (∀ g row, rowInclusion (a.iso g row) = (upperAct).iso g (rowInclusion row)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have projection := M.refinementHistoryRow_completeProjection c T stages packed run ordinal carrier
    pairing unions powers separation infinite choice hs hPacked hT rowTop topMem topRows mono
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have grounds := M.refinementHistoryRowGraphs_mem c T stages packed run ordinal carrier
    pairing unions powers separation hQ
  have equivariant : ∀ g p,
      rowFunction ((upperAct).iso g p) = a.iso g (rowFunction p) := by
    intro g p
    obtain ⟨A, code⟩ := M.refinementHistoryRowFunction_coordinates c T stages packed p
    exact M.refinementHistoryRowFunction_code c T stages packed ((upperAct).iso g p)
      (a.iso g (rowFunction p))
      (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A)
      (M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
        topMem topRows hs hh ordinal trace g p (rowFunction p) A code)
  refine ⟨projection, grounds.1, grounds.2,
    M.refinementHistoryRowFunction_code c T stages packed,
    M.refinementHistoryRowInclusion_encode c (RecursiveRefinementOrderHistory.carriers run) ordinal carrier,
    equivariant, ?_⟩
  intro g row
  exact (projection.inclusion_equivariant upperAct a equivariant g row).symm

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticRepresentedDomainEasyCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open scoped ZFSet
universe u
private theorem decoded_property_congr
    {G R : Type u} [Group G] [PartialOrder R]
    (M : TransitiveGround.{u}) (c : Presentation R) (t : Presentation G)
    (T alpha rowGraph packed1 packed2 assignments1 assignments2 action1 action2 : ZFSet.{u})
    (packedEq : packed1 = packed2) (assignmentsEq : assignments1 = assignments2)
    (actionEq : action1 = action2)
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop)
    (code1 : letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1
      let Q1 := M.refinementHistoryForcing c.carrier T alpha packed1
      PosetActionCode t.carrier Q1 ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
        (SetMembers.presentation Q1).conditionOrder
        (rawRowAssignmentActionGraph t.carrier Q1 c.carrier (⋃₀ ⋃₀ Q1) assignments1 rowGraph action1))
    (code2 : letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2
      let Q2 := M.refinementHistoryForcing c.carrier T alpha packed2
      PosetActionCode t.carrier Q2 ((t.product t).graph t (fun gh => gh.1 * gh.2)) (t.encode 1)
        (SetMembers.presentation Q2).conditionOrder
        (rawRowAssignmentActionGraph t.carrier Q2 c.carrier (⋃₀ ⋃₀ Q2) assignments2 rowGraph action2)) :
    Property (M.refinementHistoryForcing c.carrier T alpha packed1)
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1)
      (letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed1
       code1.toPresentedPosetAction t (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha packed1))) ↔
    Property (M.refinementHistoryForcing c.carrier T alpha packed2)
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2)
      (letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha packed2
       code2.toPresentedPosetAction t (SetMembers.presentation
        (M.refinementHistoryForcing c.carrier T alpha packed2))) := by
  subst packed2
  subst assignments2
  subst action2
  rfl

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

variable {stages history alpha : ZFSet.{u}} (hh : history ∈ M.sets)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (hAlpha : alpha ∈ M.sets) (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hh trace hAlpha cutOrdinal subset

theorem semanticStructuralPrefixAction_restricted_property
    (Property : ∀ (domainSet : ZFSet.{u}) (order : PartialOrder (SetMembers domainSet)),
      @PosetAction G _ (SetMembers domainSet) order → Prop) :
    Property
      (M.refinementHistoryForcing c.carrier T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha (graphRestriction alpha history)))
      (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 alpha (graphRestriction alpha history)))
      (M.semanticStructuralAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hAlpha (M.graphRestriction_mem unions separation hAlpha hh)
        cutOrdinal (trace.restrict cutOrdinal subset)) ↔
    Property Q (M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked)
      (M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes
        nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
        symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset) := by
  have packedEq := (M.structuralRefinementHistory_history_restrict t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 alpha history).trans
      (M.structuralRefinementHistory_domain_restrict t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 subset)
  unfold semanticStructuralAction semanticStructuralPrefixAction
  exact decoded_property_congr M c t T alpha (a.actionGraph c t) _ _ _ _ _ _ packedEq
    (M.structuralAssignments_history_restrict t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 alpha history)
    (M.structuralAssignmentActionGraph_history_restrict t.carrier b.carrier b.conditionOrder
      (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 alpha history)
    Property _ _

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticStructuralOrderCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

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
include hs hh ordinal trace

local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace

theorem semanticStructuralOrder_action_coordinates :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    ∀ (g : G) (p q : SetMembers Q) (row oldRow : R) (A oldA : ZFSet.{u}),
      SetMembers.raw p = ZFSet.pair (c.encode row) A →
      SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA →
      q ≤ (upperAct).iso g p →
      oldRow ≤ a.iso g row ∧
        M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A ⊆ oldA := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  intro g p q row oldRow A oldA originalCode oldCode below
  have moved := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace g p row A originalCode
  have belowRaw : ZFSet.pair (SetMembers.raw q) (SetMembers.raw ((upperAct).iso g p)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := below
  rw [oldCode, moved] at belowRaw
  have fields := (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed
    (c.encode oldRow) oldA (c.encode (a.iso g row)) _).1 belowRaw
  exact ⟨(c.pair_mem_conditionOrder oldRow (a.iso g row)).1 fields.2.2.1, fields.2.2.2⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalRowRectangles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

local notation "Q" => SetMembers (M.smallPartialFunctions
  (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)

theorem internalRowAction_aligned_agrees :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∀ (p r : Q) (D X V : L) (g h : G),
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i.val ≤ X) →
      r ≤ act.iso g p →
      (∀ i, i ≤ a.iso h D → i ≤ X → i ≤ a.iso h V) →
      (∀ i, i ≤ V → a.iso h i = a.iso g i) →
      ∀ x y z, ZFSet.pair x y ∈ SetMembers.raw r →
        ZFSet.pair x z ∈ SetMembers.raw (act.iso h p) → y = z := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act p r D X V g h bp br reference overlap agree x y z left right
  have rc := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega r).2.1
  have hc := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega (act.iso h p)).2.1
  have coords := (ZFSet.pair_mem_prod.1 (rc.shape left)).1
  have hz := (ZFSet.pair_mem_prod.1 (hc.shape right)).2
  obtain ⟨row, hrow, c, hcol, rfl⟩ := ZFSet.mem_prod.1 coords
  obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier row).1 hrow
  have ri := br i (row_mem_rowUsedRows rc left)
  have hi := M.internalRowAction_usedRows_bounded a s b C pairing unions powers separation
    infinite hL hC hG graph h p D bp i (row_mem_rowUsedRows hc right)
  have below := overlap i.val hi ri
  let j := (a.nonbottom.iso h).symm i
  have image : a.iso h j.val = i.val :=
    congrArg Subtype.val ((a.nonbottom.iso h).apply_symm_apply i)
  have oldV : j.val ≤ V := by
    have moved : a.iso h j.val ≤ a.iso h V := by rw [image]; exact below
    simpa only [OrderIso.symm_apply_apply] using (a.iso h).symm.monotone moved
  have same : a.iso g j.val = i.val := (agree j.val oldV).symm.trans image
  have old := (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
    hL hC hG graph h p j c z hcol hz).1 (by rw [image]; exact right)
  have copied := (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
    hL hC hG graph g p j c z hcol hz).2 old
  rw [same] at copied
  have inherited := (M.smallFunction_le_iff (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega r (act.iso g p)).1 reference copied
  exact rc.unique _ y z left inherited

theorem internalRowAction_one_copy_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∀ (p r : Q) (D X V : L) (g h : G),
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i.val ≤ X) →
      r ≤ act.iso g p →
      (∀ i, i ≤ a.iso h D → i ≤ X → i ≤ a.iso h V) →
      (∀ i, i ≤ V → a.iso h i = a.iso g i) →
      ∃ t : Q, SetMembers.raw t = SetMembers.raw r ∪ SetMembers.raw (act.iso h p) ∧
        t ≤ r ∧ t ≤ act.iso h p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act p r D X V g h bp br reference overlap agree
  exact M.countableFunction_common_extension pairing unions powers separation infinite choice
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) r (act.iso h p)
    (M.internalRowAction_aligned_agrees a s b C pairing unions powers separation infinite
      hL hC hG graph p r D X V g h bp br reference overlap agree)

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
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

theorem decoded_separate_at :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    ∀ W d X : SetMembers geometry.carrier, W ≤ d → W ≤ X →
      ∃ h : SetMembers geometry.actors,
        h ∈ geometry.decodedAction.principalFix W ∧
        geometry.meet.smallMeet (geometry.decodedAction.iso h d) X = W := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  dsimp only
  intro W d X wd wx
  obtain ⟨k, hk, fixed, y, hy, action, meet⟩ := fulfilled.separates
    _ (SetMembers.raw_mem W) _ (SetMembers.raw_mem d) _ (SetMembers.raw_mem X) wd wx
  let h := SetMembers.ofMem k hk
  have acted : geometry.action_code.act h d = SetMembers.ofMem y hy :=
    (geometry.action_code.act_eq_iff _ _ _).2
      (by simpa only [h, SetMembers.raw_ofMem] using action)
  refine ⟨h, ?_, ?_⟩
  · intro z lower
    apply (geometry.action_code.act_eq_iff _ _ _).2
    simpa only [h, SetMembers.raw_ofMem] using fixed _ (SetMembers.raw_mem z) lower
  · apply (geometry.meet.smallMeet_eq_iff _ _ _).2
    change ZFSet.pair (ZFSet.pair (SetMembers.raw (geometry.action_code.act h d))
      (SetMembers.raw X)) (SetMembers.raw W) ∈ geometry.meetGraph
    simpa only [acted, SetMembers.raw_ofMem] using meet

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

include collection order nodeMaps supports

theorem binaryRowStructural_aligned_copy_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L) {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (muOrdinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
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
    let forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared stages history
    let I := refinementDataHistoryIndices stages packed
    let anchors := refinementIndexFieldGraph I s.carrier 2
    let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace
    ∀ (p q : SetMembers upperQ) (r oldRow : SetMembers c.carrier) (A oldA : ZFSet.{u})
      (g h : G) (D X V : L),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA →
      StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
      q ≤ upperAct.iso g p →
      (∀ i : L, s.encode i ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i ≤ D) →
      (∀ i : L, s.encode i ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw oldRow) → i ≤ X) →
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
      (∀ z ∈ oldA, ZFSet.pair z (s.encode X) ∈
        stageOneDataBounds oldA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
      g⁻¹ * h ∈ a.principalFix V →
      meet (a.iso h D) X = a.iso h V →
      meet (a.iso h D) X ≤ a.iso h D →
      meet (a.iso h D) X ≤ X →
      (∀ z : L, z ≤ a.iso h D → z ≤ X → z ≤ meet (a.iso h D) X) →
      (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
        let hAlpha := M.transitive hs member
        let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
        let subset := (And.left stagesOrdinal) alpha member
        let lowerPacked := graphRestriction alpha packed
        let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
        letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
        let lower := SetMembers.presentation Q
        let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
          pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
          nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
          topMem topRows hh trace hAlpha cutOrdinal subset
        ∀ (H : ConditionFilter (SetMembers Q)),
          H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
          ∀ (v w : L) (x y : (M.nameDomain lower).names),
            a.principalFix v ≤ localAct.stabilizer lower x.val →
            a.principalFix w ≤ localAct.stabilizer lower y.val →
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
            Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
            ∃ tau : (M.nameDomain lower).names,
              HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
              a.principalFix (meet v w) ≤ localAct.stabilizer lower tau.val ∧
              Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
      let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h) A
      ∃ row : SetMembers c.carrier, ∃ result : SetMembers upperQ,
        SetMembers.raw row = SetMembers.raw oldRow ∪ SetMembers.raw (act.iso h r) ∧
        SetMembers.raw result = ZFSet.pair (c.encode row) (movedA ∪ oldA) ∧
        result ≤ upperAct.iso h p ∧ result ≤ q := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace coordinates two carrier forcingOrder
    forcingAction omega topMem topRows packed I anchors upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro upperAct p q r oldRow A oldA g h D X V pCode qCode prepared below usedD usedX dataD dataX
    relative overlap meetLeft meetRight meetGreatest descent movedA
  have source : ZFSet.pair (c.encode r) A ∈ upperQ := pCode ▸ SetMembers.raw_mem p
  have oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ := qCode ▸ SetMembers.raw_mem q
  have reference := M.semanticStructuralOrder_action_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hs hh stagesOrdinal trace g p q r oldRow A oldA pCode qCode below
  have agree (i : L) (hi : i ≤ V) : a.iso h i = a.iso g i := by
    have fixed := relative i hi
    have moved := congrArg (a.iso g) fixed
    simpa only [a.mul, a.point_inv_right] using moved
  obtain ⟨row, rowCode, rowBelowOld, rowBelowH⟩ :=
    M.internalRowAction_one_copy_union a s b C pairing unions powers separation infinite hL hC hG graph
      choice r oldRow D X V g h (fun i hi => usedD i.val hi) (fun i hi => usedX i.val hi)
      reference.1 (fun i hi hx => overlap ▸ meetGreatest i hi hx) agree
  have candidate := (M.mem_refinementHistoryForcing c.carrier lifted stages packed
    (ZFSet.pair (c.encode r) A)).1 source |>.1
  have hA : A ∈ M.sets := ((M.mem_groundSmallSubsets _ _ A).1 (ZFSet.pair_mem_prod.1 candidate).2).1
  have transported := M.binaryRowStructuralAssignmentImage_dataBound a s b C pairing unions powers
    separation collection infinite hL order hC hG graph nodeMaps supports directed hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace h D A hA dataD
  have unionFacts := M.semanticStructuralTrace_aligned_copy_union c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace infinite choice small meet I S mu s.nonbottom.carrier tuples
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun D f _ tau entry bound => M.liftedRowTuple_supported a s b C pairing unions powers separation
      infinite hL hC hG graph hmu muOrdinal valid f tau D entry bound.2)
    r oldRow row A oldA g h D X V source oldSource (pCode ▸ prepared)
    rowBelowOld reference.1 rowBelowH reference.2 relative overlap meetLeft meetRight meetGreatest
    transported.2.2 dataX descent
  let result : SetMembers upperQ := SetMembers.ofMem _ unionFacts.1
  have resultCode : SetMembers.raw result = ZFSet.pair (c.encode row) (movedA ∪ oldA) :=
    SetMembers.raw_ofMem _ _
  have movedCode := M.semanticStructuralAction_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace h p r A pCode
  refine ⟨row, result, rowCode, resultCode, ?_, ?_⟩
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw (upperAct.iso h p)) ∈ _
    rw [resultCode, movedCode]
    exact unionFacts.2.1
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw q) ∈ _
    rw [resultCode, qCode]
    exact unionFacts.2.2

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
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

theorem structural_separating_copy_union
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
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
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
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
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  ∀ (p q : SetMembers upperQ) (r oldRow : SetMembers c.carrier) (A oldA : ZFSet.{u})
    (g1 g2 : SetMembers geometry.actors) (dBound X W : SetMembers geometry.carrier),
    SetMembers.raw p = ZFSet.pair (c.encode r) A →
    SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
    q ≤ upperAct.iso g1 p →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw r) → i ≤ dBound) →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw oldRow) → i ≤ X) →
    (∀ z ∈ A, ZFSet.pair z (s.encode dBound) ∈
      stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    (∀ z ∈ oldA, ZFSet.pair z (s.encode X) ∈
      stageOneDataBounds oldA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    W ≤ dBound → g1 ∈ a.principalFix W → g2 ∈ a.principalFix W →
    a.iso g1 dBound ≤ X → a.iso g2 dBound ≤ X →
    (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∃ h : SetMembers geometry.actors,
      h ∈ a.principalFix W ∧
      geometry.meet.smallMeet (a.iso h dBound) X = W ∧
      geometry.meet.smallMeet (a.iso h dBound) (a.iso g1 dBound) = W ∧
      geometry.meet.smallMeet (a.iso h dBound) (a.iso g2 dBound) = W ∧
    (let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h) A;
    ∃ row : SetMembers c.carrier, ∃ result : SetMembers upperQ,
      SetMembers.raw row = SetMembers.raw oldRow ∪ SetMembers.raw (act.iso h r) ∧
      SetMembers.raw result = ZFSet.pair (c.encode row) (movedA ∪ oldA) ∧
      result ≤ q ∧ result ≤ upperAct.iso h p) := by
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
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
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  intro p q r oldRow A oldA g1 g2 dBound X W pCode qCode prepared below
    usedD usedX dataD dataX wd fixed1 fixed2 bound1 bound2 descent
  have fixedLower (g : SetMembers geometry.actors) (fixed : g ∈ a.principalFix W) :
      W ≤ a.iso g dBound := by
    have lower := (a.iso g).monotone wd
    rw [fixed W le_rfl] at lower
    exact lower
  obtain ⟨h, fixed, overlap⟩ := fulfilled.decoded_separate_at W dBound X wd
    ((fixedLower g1 fixed1).trans bound1)
  have relative : g1⁻¹ * h ∈ a.principalFix W :=
    (a.principalFix W).mul_mem ((a.principalFix W).inv_mem fixed1) fixed
  have overlapMoved : geometry.meet.smallMeet (a.iso h dBound) X = a.iso h W :=
    overlap.trans (fixed W le_rfl).symm
  obtain ⟨row, result, rowCode, resultCode, toH, toOld⟩ :=
    M.binaryRowStructural_aligned_copy_union a s b columns pairing unions powers separation
      collection infinite hL order hC hG graph nodeMaps supports directed choice small geometry.meet.smallMeet
      hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace p q r oldRow A oldA g1 h dBound X W
      pCode qCode prepared below usedD usedX dataD dataX relative overlapMoved
      (geometry.meet.toSmallMeetOrder.meet_le_left _ _)
      (geometry.meet.toSmallMeetOrder.meet_le_right _ _)
      (fun _ left right => geometry.meet.toSmallMeetOrder.le_meet left right) descent
  have apart (Y : SetMembers geometry.carrier) (wy : W ≤ Y) (yx : Y ≤ X) :
      geometry.meet.smallMeet (a.iso h dBound) Y = W := by
    apply le_antisymm
    · rw [← overlap]
      exact geometry.meet.toSmallMeetOrder.le_meet
        (geometry.meet.toSmallMeetOrder.meet_le_left _ _)
        (le_trans (geometry.meet.toSmallMeetOrder.meet_le_right _ _) yx)
    · exact geometry.meet.toSmallMeetOrder.le_meet (fixedLower h fixed) wy
  exact ⟨h, fixed, overlap, apart _ (fixedLower g1 fixed1) bound1,
    apart _ (fixedLower g2 fixed2) bound2, row, result, rowCode, resultCode, toOld, toH⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

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






theorem structural_common_support
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
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
  ∀ (H : ConditionFilter (SetMembers upperQ))
    (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain upper)))
    (V W : SetMembers geometry.carrier) (x y : Name upper),
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) x →
    Name.eval {p | H.mem p} x = Name.eval {p | H.mem p} y →
    (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∃ z : Name upper, z.val ∈ M.sets ∧
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z ∧
      a.principalFix (geometry.meet.smallMeet V W) ≤ upperAct.stabilizer upper z ∧
      Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {p | H.mem p} z = Name.eval {p | H.mem p} x := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
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
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
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
  let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  intro H genericFormula V W x y groundX groundY supportX supportY symmetric values descent
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have recursive := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let historyTop := M.refinementHistoryOrderTop c.conditionOrder_code lifted stages packed
    recursive.carriers stagesOrdinal carrier (c.encode ⊤) topMem topRows
  have upperCarrier : upper.carrier ∈ M.sets :=
    M.refinementHistoryForcing_mem pairing unions powers separation carrier hLifted hs hPacked omega
  have upperOrder : upper.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier forcingOrder
      hLifted hs hPacked omega
  have upperGraph : upperAct.actionGraph upper b ∈ M.sets := by
    erw [M.semanticStructuralAction_graph]
    exact M.structuralForcingActionGraph_mem pairing unions powers separation collection
      carrier forcingAction hG hL order graph supports hLifted hSquared hs hh omega
  have upperMaps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b
    pairing unions powers separation collection upperCarrier hG upperGraph
  have atoms : H.GenericFor (Name.atomicFamily (M.nameDomain upper)) :=
    fun E member => genericFormula E (Or.inl member)
  obtain ⟨p0, active, equal⟩ :=
    (Name.eval_eq_iff_forcesEq (M.nameDomain upper) H atoms groundX groundY).1 values
  have dense := fulfilled.structural_dense_mixture_equalities collection infinite choice small
    smallD irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2
    closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    p0 V W x y groundX groundY supportX supportY equal descent
  obtain ⟨z, _candidate, groundZ, hsZ, supportZ, rankZ, valueZ⟩ :=
    M.exists_mixtureCandidate_of_dense upperAct upper b s a.principalFix
      pairing unions powers separation collection upperCarrier upperOrder hG hL supports upperMaps
      (a.principalSupportFamily ⊥ directed) (geometry.meet.smallMeet V W)
      ⟨geometry.meet.smallMeet V W, le_rfl⟩ x groundX symmetric p0 dense H genericFormula active
  exact ⟨z, groundZ, hsZ, supportZ, rankZ, valueZ⟩






theorem structural_common_support_all_stages
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
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
  ∀ (H : ConditionFilter (SetMembers upperQ))
    (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain upper)))
    (V W : SetMembers geometry.carrier) (x y : Name upper),
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) x →
    Name.eval {p | H.mem p} x = Name.eval {p | H.mem p} y →
    ∃ z : Name upper, z.val ∈ M.sets ∧
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) z ∧
      a.principalFix (geometry.meet.smallMeet V W) ≤ upperAct.stabilizer upper z ∧
      Name.nameRank z ≤ Name.nameRank x ∧
      Name.eval {p | H.mem p} z = Name.eval {p | H.mem p} x := by
  let geometry := run.finalGeometry i₀
  let geometryGroup := geometry.group_code.toGroup
  let geometryOrder := geometry.meet.order.toPartialOrder
  let geometryBottom := geometry.decodedBottom
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
  let rowOrder := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let rowTop := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
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
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages
  induction stages using ZFSet.inductionOn with
  | h stages ih =>
    intro history hs hh stagesOrdinal trace
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
    let historyOrder := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace
    let upper := SetMembers.presentation upperQ
    intro H genericFormula V W x y groundX groundY supportX supportY symmetric values
    apply fulfilled.structural_common_support collection infinite choice small smallD irreflexive
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace
      H genericFormula V W x y groundX groundY supportX supportY symmetric values
    intro alpha member
    let hAlpha := M.transitive hs member
    let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
    let subset := (And.left stagesOrdinal) alpha member
    let Property : ∀ (Q : ZFSet.{u}) (orderQ : PartialOrder (SetMembers Q)),
        @PosetAction (SetMembers geometry.actors) _ (SetMembers Q) orderQ → Prop :=
      fun Q orderQ actionQ =>
        letI := orderQ
        let presentation := SetMembers.presentation Q
        ∀ (filter : ConditionFilter (SetMembers Q)),
          filter.GenericFor (formulaFamily (M.nameDomain presentation)) →
          ∀ (v w : SetMembers geometry.carrier) (first second : Name presentation),
            first.val ∈ M.sets → second.val ∈ M.sets →
            a.principalFix v ≤ actionQ.stabilizer presentation first →
            a.principalFix w ≤ actionQ.stabilizer presentation second →
            HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) first →
            Name.eval {q | filter.mem q} first = Name.eval {q | filter.mem q} second →
            ∃ z : Name presentation, z.val ∈ M.sets ∧
              HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) z ∧
              a.principalFix (geometry.meet.smallMeet v w) ≤ actionQ.stabilizer presentation z ∧
              Name.nameRank z ≤ Name.nameRank first ∧
              Name.eval {q | filter.mem q} z = Name.eval {q | filter.mem q} first
    have earlier := ih alpha member (graphRestriction alpha history) hAlpha
      (M.graphRestriction_mem unions separation hAlpha hh) cutOrdinal
      (trace.restrict cutOrdinal subset)
    have transferred := (M.semanticStructuralPrefixAction_restricted_property c act b s a ⊥
      directed lifted squared (c.encode ⊤) pairing unions powers separation collection
      carrier forcingOrder forcingAction hG hL order graph nodeMaps supports hLifted hSquared
      omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hh trace hAlpha cutOrdinal subset Property).1 earlier
    dsimp only
    intro lowerH _coded ordinary v w first second firstSupport secondSupport firstHS _secondHS equal
    obtain ⟨z, groundZ, symmetricZ, supportZ, _rankZ, valueZ⟩ := transferred lowerH ordinary
      v w first.val second.val first.property second.property firstSupport secondSupport firstHS equal
    exact ⟨⟨z, groundZ⟩, symmetricZ, supportZ, valueZ⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInternalNoChooserConsequences
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
variable (N : TransitiveGround.{u})

theorem ordinalSurjection_chooses_subsets
    (pairing : Realize N.sets SetFormula.pairing Fin.elim0)
    (unions : Realize N.sets SetFormula.union Fin.elim0)
    (powers : Realize N.sets powerSet Fin.elim0)
    (separation : SeparationSchema N.sets)
    {X T e : ZFSet.{u}} (hX : X ∈ N.sets) (hT : T ∈ N.sets)
    (he : e ∈ N.sets) (ordinal : ordinalSetProperty T)
    (function : ZFSet.IsFunc T X e)
    (covers : ∀ x ∈ X, ∃ i ∈ T, ZFSet.pair i x ∈ e) :
    ∃ f ∈ N.sets, ∀ S ∈ N.sets, S ⊆ X → S.Nonempty →
      ∃ x ∈ S, ZFSet.pair S x ∈ f ∧
        ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x := by
  let A := N.nonemptyGroundSubsets X
  have hA : A ∈ N.sets := N.nonemptyGroundSubsets_mem powers separation hX
  have meets : ∀ S ∈ A, ∃ i ∈ T, ∃ x ∈ S, ZFSet.pair i x ∈ e := by
    intro S member
    obtain ⟨_ground, subset, x, hx⟩ := (N.mem_nonemptyGroundSubsets X S).1 member
    obtain ⟨i, hi, edge⟩ := covers x (subset hx)
    exact ⟨i, hi, x, hx, edge⟩
  have code := ordinalIndexedChoiceGraph_choice ordinal ⟨X, function⟩ meets
  refine ⟨ordinalIndexedChoiceGraph A T e,
    N.ordinalIndexedChoiceGraph_mem pairing unions powers separation hA hT he, ?_⟩
  intro S hS subset nonempty
  have member : S ∈ A := (N.mem_nonemptyGroundSubsets X S).2 ⟨hS, subset, nonempty⟩
  obtain ⟨x, edge, unique⟩ := code.function.2 S member
  exact ⟨x, code.chosen S x edge, edge, fun z _ hz => unique z hz⟩

theorem noChooser_no_ordinal_surjection_not_choice
    (zf : ZFRealization N.sets) {X : ZFSet.{u}} (hX : X ∈ N.sets)
    (noChooser : ¬ ∃ f ∈ N.sets, ∀ S ∈ N.sets, S ⊆ X → S.Nonempty →
      ∃ x ∈ S, ZFSet.pair S x ∈ f ∧
        ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x) :
    (¬ ∃ T ∈ N.sets, ordinalSetProperty T ∧
      ∃ e ∈ N.sets, ZFSet.IsFunc T X e ∧
        ∀ x ∈ X, ∃ i ∈ T, ZFSet.pair i x ∈ e) ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
  have pairing : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powers : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  constructor
  · rintro ⟨T, hT, ordinal, e, he, function, covers⟩
    exact noChooser (N.ordinalSurjection_chooses_subsets pairing unions powers zf.2.1
      hX hT he ordinal function covers)
  · intro choice
    exact noChooser (N.exists_function_choosing_subsets powers zf.2.1 choice hX)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainFinalStructuralPrefixDescent
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

theorem structural_prefix_descent
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
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
  ∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val := by
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
  intro alpha member
  let hAlpha := M.transitive hs member
  let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
  let subset := (And.left stagesOrdinal) alpha member
  let Property : ∀ (Q : ZFSet.{u}) (orderQ : PartialOrder (SetMembers Q)),
      @PosetAction (SetMembers geometry.actors) _ (SetMembers Q) orderQ → Prop :=
    fun Q orderQ actionQ =>
      letI := orderQ
      let presentation := SetMembers.presentation Q
      ∀ (filter : ConditionFilter (SetMembers Q)),
        filter.GenericFor (formulaFamily (M.nameDomain presentation)) →
        ∀ (v w : SetMembers geometry.carrier) (first second : Name presentation),
          first.val ∈ M.sets → second.val ∈ M.sets →
          a.principalFix v ≤ actionQ.stabilizer presentation first →
          a.principalFix w ≤ actionQ.stabilizer presentation second →
          HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) first →
          Name.eval {q | filter.mem q} first = Name.eval {q | filter.mem q} second →
          ∃ z : Name presentation, z.val ∈ M.sets ∧
            HereditarilySymmetric actionQ presentation (a.principalSupportFamily ⊥ directed) z ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ actionQ.stabilizer presentation z ∧
            Name.nameRank z ≤ Name.nameRank first ∧
            Name.eval {q | filter.mem q} z = Name.eval {q | filter.mem q} first
  have earlier := fulfilled.structural_common_support_all_stages
    collection infinite choice small smallD irreflexive columns hColumns hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    alpha (graphRestriction alpha history) hAlpha
    (M.graphRestriction_mem unions separation hAlpha hh) cutOrdinal
    (trace.restrict cutOrdinal subset)
  have transferred := (M.semanticStructuralPrefixAction_restricted_property c act b s a ⊥
    directed lifted squared (c.encode ⊤) pairing unions powers separation collection
    carrier forcingOrder forcingAction hG hL order graph nodeMaps supports hLifted hSquared
    omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
    hh trace hAlpha cutOrdinal subset Property).1 earlier
  intro lowerH _coded ordinary v w first second firstSupport secondSupport firstHS _secondHS equal
  obtain ⟨z, groundZ, symmetricZ, supportZ, _rankZ, valueZ⟩ := transferred lowerH ordinary
    v w first.val second.val first.property second.property firstSupport secondSupport firstHS equal
  exact ⟨⟨z, groundZ⟩, symmetricZ, supportZ, valueZ⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalStructuralRowNoChooser
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

theorem structural_lifted_rows_no_chooser
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable columns ZFSet.omega)
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
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
  let recursive := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let inclusion := M.refinementHistoryRowEmbedding c lifted stages packed recursive stagesOrdinal carrier
  ∀ (H : ConditionFilter (SetMembers upperQ)),
    H.GenericFor (formulaFamily (M.nameDomain upper)) →
    let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
    let rowSet := Name.eval {p | H.mem p}
      (Name.rename upper inclusion (M.internalRowSetName s columns hL))
    rowSet ∈ N.sets ∧
      ¬ ∃ f ∈ N.sets, ∀ S ∈ N.sets, S ⊆ rowSet → S.Nonempty →
        ∃ x ∈ S, ZFSet.pair S x ∈ f ∧ ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x := by
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
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
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  let recursive := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let inclusion := M.refinementHistoryRowEmbedding c lifted stages packed recursive stagesOrdinal carrier
  intro H ordinary
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
  have projectionData := M.semanticStructuralTrace_rowProjection c act b s a ⊥ directed
    lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder
    forcingAction hG hL order graph nodeMaps supports hLifted hSquared omega
    valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh stagesOrdinal trace
    infinite choice
  have rowSetGround := M.liftedInternalRowSet_mem a s b columns directed pairing unions powers
    separation collection infinite hL hC hG graph upper upperAct hQ inclusion
    projectionData.2.2.1 projectionData.2.2.2.2.2.2 H
  refine ⟨rowSetGround, ?_⟩
  rintro ⟨f, hf, selection⟩
  obtain ⟨B, i, sn, xn, fn, outside, snCode, xnCode, fixedS, fixedF, p0, _hp0, forced0⟩ :=
    M.liftedInternalRows_chooser_witness a s b columns directed pairing unions powers separation
      collection infinite hL hC hG graph upper upperAct hQ order
      (geometry.decoded_unbounded fulfilled.growth)
      (M.refinementHistoryRowRestriction c lifted stages packed) inclusion projectionData.1
      projectionData.2.2.1 projectionData.2.2.2.2.2.2 H ordinary f hf selection
  obtain ⟨rawP, memberP, belowRaw, support, _hSupport, _subsetSupport, _smallSupport, prepared⟩ :=
    fulfilled.structural_support_prepared_strengthening collection infinite choice small smallD
      irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace (SetMembers.raw p0) (SetMembers.raw_mem p0)
  let p : SetMembers upperQ := SetMembers.ofMem rawP memberP
  have pRaw : SetMembers.raw p = rawP := SetMembers.raw_ofMem _ _
  have below : p ≤ p0 := by
    change ZFSet.pair (SetMembers.raw p) (SetMembers.raw p0) ∈ _
    rw [pRaw]
    exact belowRaw
  have forced := forces_mono (M.nameDomain upper) (BoundedFormula.uniqueFiberFormula 0 1 2).toFormula
    (extend sn (extend xn (extend fn Fin.elim0))) forced0 below
  have preparedP : StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier
      (SetMembers.raw p) := by
    rw [pRaw]
    exact prepared.forget
  let sourceRow := M.refinementHistoryRowFunction c lifted stages packed p
  obtain ⟨A, pCode⟩ := M.refinementHistoryRowFunction_coordinates c lifted stages packed p
  obtain ⟨dBound, bd, id, usedD, dataD⟩ := fulfilled.toFinalFulfillment.structural_bounds_with
    collection infinite choice columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    p sourceRow A B i.val pCode
  have descent := fulfilled.structural_prefix_descent collection infinite choice small smallD
    irreflexive columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace
  obtain ⟨g, fixed, overlap, _overlap1, _overlap2, row, result, _rowCode, _resultCode, toP, toMoved⟩ :=
    fulfilled.toFinalFulfillment.structural_separating_copy_union collection infinite choice small
      columns hColumns hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2
      children1 children2 stages history hs hh stagesOrdinal trace
      p p sourceRow sourceRow A A 1 1 dBound dBound B pCode pCode preparedP
      (by change p ≤ upperAct.iso 1 p; rw [upperAct.one]) usedD usedD dataD dataD bd
      (a.principalFix B).one_mem (a.principalFix B).one_mem
      (by change a.iso 1 dBound ≤ dBound; rw [a.one]) (by change a.iso 1 dBound ≤ dBound; rw [a.one]) descent
  have distinctNode : a.iso g i.val ≠ i.val := a.moved_ne_of_separated g B dBound i.val
    (fun x xd xg => by
      rw [← overlap]
      exact geometry.meet.toSmallMeetOrder.le_meet xg xd) id outside
  have movedCode : upperAct.act upper g xn.val =
      Name.rename upper inclusion (M.internalRowName s columns hL (a.nonbottom.iso g i)) := by
    rw [xnCode, act.act_rename_of_equivariant upperAct c upper inclusion
      projectionData.2.2.2.2.2.2,
      M.internalRowName_action a s b columns pairing unions powers separation infinite hL hC hG graph]
  exact M.projectedBinaryRows_uniqueFiber_incompatible upper b upperAct
    (a.principalSupportFamily ⊥ directed) pairing unions powers separation collection infinite choice
    small (M.nonbottom_carrier_mem s separation hL) hC uncountable hQ maps
    (M.refinementHistoryRowRestriction c lifted stages packed) inclusion projectionData.1
    projectionData.2.1 ⊤ (fun _ => le_top) sn xn fn g (fixedS fixed) (fixedF fixed)
    (s.encode i.val) (s.nonbottom.encode_mem i)
    (s.encode (a.iso g i.val)) (s.nonbottom.encode_mem (a.nonbottom.iso g i))
    (fun equal => distinctNode (s.injective equal).symm) xnCode movedCode p forced
    ⟨result, toP, toMoved⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundMainFinalStructuralRowNonchoice
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

theorem structural_lifted_rows_not_wellorderable_not_choice_oai
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable columns ZFSet.omega)
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
  let recursive := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let inclusion := M.refinementHistoryRowEmbedding c lifted stages packed recursive stagesOrdinal carrier
  ∀ (H : ConditionFilter (SetMembers upperQ)),
    H.GenericFor (formulaFamily (M.nameDomain upper)) →
    let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
    let rowSet := Name.eval {p | H.mem p}
      (Name.rename upper inclusion (M.internalRowSetName s columns hL))
    ZFRealization N.sets →
      rowSet ∈ N.sets ∧
      (¬ ∃ index ∈ N.sets, ordinalSetProperty index ∧
        ∃ enumeration ∈ N.sets, ZFSet.IsFunc index rowSet enumeration ∧
          ∀ x ∈ rowSet, ∃ i ∈ index, ZFSet.pair i x ∈ enumeration) ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
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
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  let recursive := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
    (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared stagesOrdinal trace
  let inclusion := M.refinementHistoryRowEmbedding c lifted stages packed recursive stagesOrdinal carrier
  intro H ordinary zf
  have noChooser := fulfilled.structural_lifted_rows_no_chooser collection infinite choice small
    smallD irreflexive columns hColumns uncountable hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace H ordinary
  exact ⟨noChooser.1,
    TransitiveGround.noChooser_no_ordinal_surjection_not_choice
      (M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H)
      zf noChooser.1 noChooser.2⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_lifted_rows_not_wellorderable_not_choice_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_lifted_rows_not_wellorderable_not_choice_oai.{u, v}
