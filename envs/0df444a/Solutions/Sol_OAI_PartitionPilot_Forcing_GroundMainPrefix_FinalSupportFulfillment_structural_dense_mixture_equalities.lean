-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_dense_mixture_equalities
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:32:19.860861+00:00
-- url     : https://prove2.me/submissions/6d21d9c1-6398-4755-83fa-23716da2b5cd

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_exists_groundStoredPreparedStrengthening
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_binaryRowStructuralAssignmentImage_dataBound
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_aligned_copy_crossCollisions
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_InitialRowForcing
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.OrderAction

universe u
variable {A G : Type u} [Group G] {P : MeetOrder A} (a : OrderAction G P)

theorem act_inv_left (g : G) (x : A) : (a.iso g⁻¹).toFun ((a.iso g).toFun x) = x := by
  rw [← a.mul, inv_mul_cancel, a.one]

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.OrderAction



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

end PosetAction
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps.CosetGeometry
universe u v
variable {A G : Type v} [Group G] {L : MeetOrder A} (geom : OrderAction G L)
variable {P : Type u} [PartialOrder P] (a : PosetAction G P) (s : Presentation P)

theorem act_eq_of_support_agreement {C : A} {τ : Name s} {g h : G}
    (support : geom.fixSubgroup C ≤ a.stabilizer s τ)
    (agree : ∀ z, L.le z C → (geom.iso g).toFun z = (geom.iso h).toFun z) :
    a.act s g τ = a.act s h τ := by
  have fixed : h⁻¹ * g ∈ geom.fixSubgroup C := by
    intro z hz
    rw [geom.mul, agree z hz, geom.act_inv_left]
  have eq := support fixed
  change a.act s (h⁻¹ * g) τ = τ at eq
  have translated := congrArg (a.act s h) eq
  rw [a.act_mul, a.act_inv_right] at translated
  exact translated

end PartitionPilot.Forcing.PosetAction



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

theorem mem_eval_mix (K : Subgroup G) (p : P) (τ : Name s)
    (H : ConditionFilter P) (x : ZFSet.{u}) :
    x ∈ Name.eval {q | H.mem q} (a.mix s K p τ) ↔
      ∃ g ∈ K, H.mem (a.iso g p) ∧ x ∈ Name.eval {q | H.mem q} (a.act s g τ) := by
  rw [Name.mem_eval]
  constructor
  · rintro ⟨σ, q, entry, hq, eq⟩
    obtain ⟨g, hg, ν, r, old, rfl, qp, qr⟩ := (a.entry_mix s K p τ σ q).1 entry
    refine ⟨g, hg, H.upward hq qp, ?_⟩
    apply (Name.mem_eval {q | H.mem q} (a.act s g τ) x).2
    exact ⟨a.act s g ν, a.iso g r, (a.entry_act s g ν τ r).2 old,
      H.upward hq qr, eq⟩
  · rintro ⟨g, hg, hp, hx⟩
    obtain ⟨σ, q, entry, hq, eq⟩ := (Name.mem_eval {q | H.mem q} (a.act s g τ) x).1 hx
    change Name.Entry σ (Name.rename s (a.iso g) τ) q at entry
    obtain ⟨ν, r, old, rfl, rfl⟩ := (Name.entry_rename s (a.iso g) τ σ q).1 entry
    obtain ⟨c, hc, cp, cr⟩ := H.directed hp hq
    exact ⟨a.act s g ν, c,
      (a.entry_mix s K p τ _ c).2 ⟨g, hg, ν, r, old, rfl, cp, cr⟩, hc, eq⟩

theorem eval_mix_of_active_equal (K : Subgroup G) (p : P) (τ : Name s)
    (H : ConditionFilter P) (hp : H.mem p)
    (agree : ∀ g ∈ K, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g τ) = Name.eval {q | H.mem q} τ) :
    Name.eval {q | H.mem q} (a.mix s K p τ) = Name.eval {q | H.mem q} τ := by
  apply ZFSet.ext
  intro x
  rw [a.mem_eval_mix s]
  constructor
  · rintro ⟨g, hg, active, hx⟩
    rwa [agree g hg active] at hx
  · intro hx
    refine ⟨1, K.one_mem, ?_, ?_⟩
    · simpa only [a.one] using hp
    · simpa only [a.act_one] using hx

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

theorem ordinaryForces_iff_all_joint_generics (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) {n : Nat} (phi : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (p : P) :
    Forces (M.nameDomain s) phi env p ↔
      ∀ H : ConditionFilter P, H.mem p → H.GenericFor (M.codedFamily s) →
        H.GenericFor (formulaFamily (M.nameDomain s)) →
        Realize ((M.nameDomain s).values {q | H.mem q}) phi
          (evalAssignment {q | H.mem q} env) := by
  constructor
  · intro forced H member _ generic
    exact forces_sound (M.nameDomain s) H generic phi env member forced
  · intro truth
    by_contra bad
    obtain ⟨q, below, negative⟩ := not_forces_refine_neg (M.nameDomain s) phi env bad
    obtain ⟨H, member, coded, ordinary⟩ := M.exists_coded_ordinary_generic s small carrier q
    exact (forces_sound (M.nameDomain s) H ordinary (.neg phi) env member negative)
      (truth H (H.upward member below) coded ordinary)

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

end PartitionPilot.Forcing.TransitiveGround



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundLiftedRowTupleProvenance
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RowCopyRefinements
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall _root_.OAI.PartitionPilot.Forcing.Name.boundedNames_small
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem separated_copies_agree (K : Subgroup G) (Sep : G → G → Prop)
    (p : P) (x y : Name s) (H : ConditionFilter P)
    (generic : H.GenericFor (a.copyWitnessFamily s K Sep p x y))
    (xy : ∀ g, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g x) = Name.eval {q | H.mem q} (a.act s g y))
    (rectangles : ∀ g₁ ∈ K, ∀ g₂ ∈ K, Sep g₁ g₂ → ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.RectangleWitness s p x y g₁ g₂))
    {g₁ g₂ : G} (hg₁ : g₁ ∈ K) (hg₂ : g₂ ∈ K) (sep : Sep g₁ g₂)
    (active₁ : H.mem (a.iso g₁ p)) (active₂ : H.mem (a.iso g₂ p)) :
    Name.eval {q | H.mem q} (a.act s g₁ x) = Name.eval {q | H.mem q} (a.act s g₂ x) := by
  obtain ⟨r, hr, r₁, r₂⟩ := H.directed active₁ active₂
  obtain ⟨q, hq, h₁, h₂, q₁, q₂, hx₁, hx₂, hy⟩ :=
    H.meets_below generic hr (Or.inl ⟨r, g₁, g₂, rfl⟩)
      (rectangles g₁ hg₁ g₂ hg₂ sep r r₁ r₂)
  have eq₁ := xy h₁ (H.upward hq q₁)
  have eq₂ := xy h₂ (H.upward hq q₂)
  rw [hx₁] at eq₁
  rw [hx₂] at eq₂
  exact eq₁.trans ((congrArg (Name.eval {q | H.mem q}) hy).trans eq₂.symm)

theorem active_copies_agree (K : Subgroup G) (Sep : G → G → Prop)
    (p : P) (x y : Name s) (H : ConditionFilter P)
    (generic : H.GenericFor (a.copyWitnessFamily s K Sep p x y))
    (xy : ∀ g, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g x) = Name.eval {q | H.mem q} (a.act s g y))
    (rectangles : ∀ g₁ ∈ K, ∀ g₂ ∈ K, Sep g₁ g₂ → ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.RectangleWitness s p x y g₁ g₂))
    (separation : ∀ g₁ ∈ K, ∀ g₂ ∈ K, ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.SeparationWitness K Sep p g₁ g₂))
    {g₁ g₂ : G} (hg₁ : g₁ ∈ K) (hg₂ : g₂ ∈ K)
    (active₁ : H.mem (a.iso g₁ p)) (active₂ : H.mem (a.iso g₂ p)) :
    Name.eval {q | H.mem q} (a.act s g₁ x) = Name.eval {q | H.mem q} (a.act s g₂ x) := by
  obtain ⟨r, hr, r₁, r₂⟩ := H.directed active₁ active₂
  obtain ⟨q, hq, h, hh, qh, sep₁, sep₂⟩ :=
    H.meets_below generic hr (Or.inr ⟨r, g₁, g₂, rfl⟩)
      (separation g₁ hg₁ g₂ hg₂ r r₁ r₂)
  have active := H.upward hq qh
  have eq₁ := a.separated_copies_agree s K Sep p x y H generic xy rectangles hh hg₁ sep₁ active active₁
  have eq₂ := a.separated_copies_agree s K Sep p x y H generic xy rectangles hh hg₂ sep₂ active active₂
  exact eq₁.symm.trans eq₂

theorem mix_capture_from_refinements [Small.{u} G] (K : Subgroup G) (Sep : G → G → Prop)
    (p : P) (x y : Name s) (H : ConditionFilter P)
    (generic : H.GenericFor (a.copyWitnessFamily s K Sep p x y)) (hp : H.mem p)
    (xy : ∀ g, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g x) = Name.eval {q | H.mem q} (a.act s g y))
    (rectangles : ∀ g₁ ∈ K, ∀ g₂ ∈ K, Sep g₁ g₂ → ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.RectangleWitness s p x y g₁ g₂))
    (separation : ∀ g₁ ∈ K, ∀ g₂ ∈ K, ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.SeparationWitness K Sep p g₁ g₂)) :
    Name.eval {q | H.mem q} (a.mix s K p x) = Name.eval {q | H.mem q} x := by
  apply a.eval_mix_of_active_equal s K p x H hp
  intro g hg active
  have eq := a.active_copies_agree s K Sep p x y H generic xy rectangles separation
    hg K.one_mem active (by simpa only [a.one] using hp)
  simpa only [a.act_one] using eq

end PartitionPilot.Forcing.PosetAction



end

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

theorem separatedActorPairs_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    let a := geometry.decodedAction
    let t := SetMembers.presentation geometry.actors
    ∀ (d W : SetMembers geometry.carrier),
      (t.product t).subset (fun gh => geometry.meet.smallMeet (a.iso gh.1 d) (a.iso gh.2 d) = W) ∈ M.sets := by
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let a := geometry.decodedAction
  let s := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  dsimp only
  intro d W
  let params := extend (SetMembers.raw d) (extend (SetMembers.raw W)
    (extend geometry.carrier (extend geometry.actors (extend geometry.action (extend geometry.meetGraph Fin.elim0)))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases (M.transitive geometry.carrier_ground (SetMembers.raw_mem d))
      (Fin.cases (M.transitive geometry.carrier_ground (SetMembers.raw_mem W))
        (Fin.cases geometry.carrier_ground (Fin.cases geometry.actors_ground
          (Fin.cases geometry.action_ground (Fin.cases geometry.meet_ground (fun i => Fin.elim0 i))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.separatedActorsFormula params members
    (M.prod_mem pairing unions powers separation geometry.actors_ground geometry.actors_ground)
  have correct (z : ZFSet.{u}) : BoundedFormula.Truth BoundedFormula.separatedActorsFormula
      (extend z params) ↔ z ∈ (t.product t).subset
        (fun gh => geometry.meet.smallMeet (a.iso gh.1 d) (a.iso gh.2 d) = W) := by
    simp only [BoundedFormula.separatedActorsFormula, BoundedFormula.truth_exMem, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_tripleMembershipFormula]
    change (∃ h₁ ∈ geometry.actors, ∃ h₂ ∈ geometry.actors,
      ∃ x ∈ geometry.carrier, ∃ y ∈ geometry.carrier,
      z = ZFSet.pair h₁ h₂ ∧ ZFSet.pair (ZFSet.pair h₁ (SetMembers.raw d)) x ∈ geometry.action ∧
      ZFSet.pair (ZFSet.pair h₂ (SetMembers.raw d)) y ∈ geometry.action ∧
      ZFSet.pair (ZFSet.pair x y) (SetMembers.raw W) ∈ geometry.meetGraph) ↔ _
    have action (g : SetMembers geometry.actors) (x : SetMembers geometry.carrier) :
        ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw d)) (SetMembers.raw x) ∈ geometry.action ↔
        a.iso g d = x := by
      rw [← geometry.decoded_action_eq]
      exact a.triple_mem_actionGraph s t g d x
    constructor
    · rintro ⟨h₁,hh₁,h₂,hh₂,x,hx,y,hy,shape,first,second,meet⟩
      obtain ⟨g₁,rfl⟩ := (t.mem_carrier h₁).1 hh₁
      obtain ⟨g₂,rfl⟩ := (t.mem_carrier h₂).1 hh₂
      obtain ⟨x,rfl⟩ := (s.mem_carrier x).1 hx
      obtain ⟨y,rfl⟩ := (s.mem_carrier y).1 hy
      have first' := (action g₁ x).1 first
      have second' := (action g₂ y).1 second
      apply ((t.product t).mem_subset _ z).2
      refine ⟨(g₁,g₂),?_,shape.symm⟩
      rw [first',second']
      exact (geometry.meet.smallMeet_eq_iff x y W).2 meet
    · intro hz
      obtain ⟨⟨g₁,g₂⟩,meet,shape⟩ := ((t.product t).mem_subset _ z).1 hz
      exact ⟨t.encode g₁,t.encode_mem g₁,t.encode g₂,t.encode_mem g₂,
        s.encode (a.iso g₁ d),s.encode_mem _,s.encode (a.iso g₂ d),s.encode_mem _,
        shape.symm,(action g₁ _).2 rfl,(action g₂ _).2 rfl,
        (geometry.meet.smallMeet_eq_iff _ _ W).1 meet⟩
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.separatedActorsFormula
      (extend z params)) (ZFSet.prod geometry.actors geometry.actors) =
      (t.product t).subset (fun gh => geometry.meet.smallMeet (a.iso gh.1 d) (a.iso gh.2 d) = W) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,correct]
    exact ⟨And.right,fun hz => ⟨(t.product t).subset_carrier _ hz,hz⟩⟩
  exact eq ▸ selected

end GroundMainFinalGeometry

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticAlignedRectangleUnions
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

theorem semanticStructuralTrace_aligned_rectangle_union
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L)
    (I S mu positions tuples : ZFSet.{u})
    (range : ∀ f z, ZFSet.pair f z ∈ tuples → z ∈ T)
    (support : ∀ (D : L), ∀ f ∈ S, ∀ u : Name c.pairEmpty, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer c.pairEmpty u)
    (r oldRow row : R) (A oldA : ZFSet.{u}) (g1 g2 h1 h2 : G) (D X V W : L)
    (source : ZFSet.pair (c.encode r) A ∈ upperQ)
    (oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ)
    (prepared : StoredPreparedConditionCode M c.carrier T stages packed b.carrier (ZFSet.pair (c.encode r) A))
    (belowOld : row ≤ oldRow)
    (oldBelowG1 : oldRow ≤ a.iso g1 r) (oldBelowG2 : oldRow ≤ a.iso g2 r)
    (belowH1 : row ≤ a.iso h1 r) (belowH2 : row ≤ a.iso h2 r)
    (contains1 : image (t.encode g1) A ⊆ oldA)
    (contains2 : image (t.encode g2) A ⊆ oldA)
    (relative1 : g1⁻¹ * h1 ∈ d.principalFix V)
    (relative2 : g2⁻¹ * h2 ∈ d.principalFix V)
    (between : h1⁻¹ * h2 ∈ d.principalFix W)
    (overlap1 : meet (d.iso h1 D) X = d.iso h1 V)
    (overlap2 : meet (d.iso h2 D) X = d.iso h2 V)
    (overlap12 : meet (d.iso h1 D) (d.iso h2 D) = d.iso h1 W)
    (meetComm : ∀ x y : L, meet x y = meet y x)
    (meetLeft : ∀ x y : L, meet x y ≤ x)
    (meetRight : ∀ x y : L, meet x y ≤ y)
    (meetGreatest : ∀ x y z : L, z ≤ x → z ≤ y → z ≤ meet x y)
    (data1 : ∀ z ∈ image (t.encode h1) A, ZFSet.pair z (b.encode (d.iso h1 D)) ∈
      stageOneDataBounds (image (t.encode h1) A) I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples)
    (data2 : ∀ z ∈ image (t.encode h2) A, ZFSet.pair z (b.encode (d.iso h2 D)) ∈
      stageOneDataBounds (image (t.encode h2) A) I T S b.carrier mu positions b.conditionOrder
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
    ZFSet.pair (c.encode row) (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)) ∈ upperQ ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)))
      (ZFSet.pair (c.encode oldRow) oldA) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)))
      (ZFSet.pair (c.encode (a.iso h1 r)) (image (t.encode h1) A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
    ZFSet.pair (ZFSet.pair (c.encode row) (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)))
      (ZFSet.pair (c.encode (a.iso h2 r)) (image (t.encode h2) A)) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let upperAct := M.semanticStructuralAction c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  let original : SetMembers upperQ := SetMembers.ofMem _ source
  have originalCode : SetMembers.raw original = ZFSet.pair (c.encode r) A := SetMembers.raw_ofMem _ _
  have movedSource (j : G) : ZFSet.pair (c.encode (a.iso j r)) (image (t.encode j) A) ∈ upperQ := by
    have movedCode := M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace j original r A originalCode
    exact movedCode ▸ SetMembers.raw_mem (upperAct.iso j original)
  have first := M.semanticStructuralTrace_aligned_copy_union c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
    infinite choice small meet I S mu positions tuples range support
    r oldRow row A oldA g1 h1 D X V source oldSource prepared belowOld oldBelowG1 belowH1 contains1
    relative1 overlap1 (meetLeft _ _) (meetRight _ _) (meetGreatest _ _) data1 oldData descent
  have sameW : d.iso h2 W = d.iso h1 W := by
    have equal := congrArg (d.iso h1) (between W le_rfl)
    rw [d.mul, d.point_inv_right] at equal
    exact equal
  have overlap21 : meet (d.iso h2 D) (d.iso h1 D) = d.iso h2 W :=
    (meetComm _ _).trans (overlap12.trans sameW.symm)
  have full : ZFSet.pair (c.encode row)
      (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)) ∈ upperQ := by
    refine (M.semanticStructuralTrace_mixed_union_extension c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace infinite choice
      (c.encode row) (c.encode (a.iso h2 r)) (c.encode row)
      (image (t.encode h2) A) (image (t.encode h1) A ∪ oldA)
      (movedSource h2) first.1 ((c.pair_mem_conditionOrder _ _).2 belowH2)
      ((c.pair_mem_conditionOrder _ _).2 le_rfl) ?_).1
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
    have againstOld := M.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
      infinite choice small meet I S mu positions tuples range support
      r oldRow row A oldA (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)) g2 h2 D X V
      source oldSource prepared belowOld oldBelowG2 belowH2 contains2
      (fun _ hz => ZFSet.mem_union.2 (Or.inl hz))
      (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr hz))))
      relative2 overlap2 (meetLeft _ _) (meetRight _ _) (meetGreatest _ _) (descent alpha member)
      data2 oldData validCut
    have againstFirst := M.semanticStructuralPrefix_aligned_copy_crossCollisions_at_larger_cut c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
      infinite choice small meet I S mu positions tuples range support
      r (a.iso h1 r) row A (image (t.encode h1) A)
      (image (t.encode h2) A ∪ (image (t.encode h1) A ∪ oldA)) h1 h2 D (d.iso h1 D) W
      source (movedSource h1) prepared belowH1 le_rfl belowH2 (fun _ hz => hz)
      (fun _ hz => ZFSet.mem_union.2 (Or.inl hz))
      (fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz))))
      between overlap21 (meetLeft _ _) (meetRight _ _) (meetGreatest _ _) (descent alpha member)
      data2 data1 validCut
    intro idx hi u hu u' hu' w hw w' hw' newMember oldMember
    rcases ZFSet.mem_union.1 oldMember with inFirst | inOld
    · exact againstFirst idx hi u hu u' hu' w hw w' hw' newMember inFirst
    · exact againstOld idx hi u hu u' hu' w hw w' hw' newMember inOld
  refine ⟨full, ?_, ?_, ?_⟩
  · exact (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed _ _ _ _).2
      ⟨full, oldSource, (c.pair_mem_conditionOrder _ _).2 belowOld,
        fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inr hz)))⟩
  · exact (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed _ _ _ _).2
      ⟨full, movedSource h1, (c.pair_mem_conditionOrder _ _).2 belowH1,
        fun _ hz => ZFSet.mem_union.2 (Or.inr (ZFSet.mem_union.2 (Or.inl hz)))⟩
  · exact (M.pair_mem_refinementHistoryOrder c.carrier c.conditionOrder T stages packed _ _ _ _).2
      ⟨full, movedSource h2, (c.pair_mem_conditionOrder _ _).2 belowH2,
        fun _ hz => ZFSet.mem_union.2 (Or.inl hz)⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundMainFinalRectangleActionData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

theorem decoded_rectangle_action_data :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    let a := geometry.decodedAction
    ∀ (V W d X : SetMembers geometry.carrier) (g₁ g₂ : SetMembers geometry.actors),
      ExternalRectangleCode geometry.carrier geometry.actors geometry.order
        geometry.meetGraph geometry.action (SetMembers.raw V) (SetMembers.raw W)
        (SetMembers.raw d) (SetMembers.raw g₁) (SetMembers.raw g₂) →
      a.iso g₁ d ≤ X → a.iso g₂ d ≤ X →
      ∃ h₁ h₂ : SetMembers geometry.actors,
        RectangleAtBoundCode geometry.carrier geometry.order geometry.meetGraph geometry.action
          (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw d)
          (SetMembers.raw g₁) (SetMembers.raw g₂) (SetMembers.raw X)
          (SetMembers.raw h₁) (SetMembers.raw h₂) ∧
        g₁⁻¹ * h₁ ∈ a.principalFix V ∧
        g₂⁻¹ * h₂ ∈ a.principalFix V ∧
        h₁⁻¹ * h₂ ∈ a.principalFix W ∧
        geometry.meet.smallMeet (a.iso h₁ d) X = a.iso h₁ V ∧
        geometry.meet.smallMeet (a.iso h₂ d) X = a.iso h₂ V ∧
        geometry.meet.smallMeet (a.iso h₁ d) (a.iso h₂ d) = a.iso h₁ W := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let a := geometry.decodedAction
  dsimp only
  intro V W d X g₁ g₂ request bound₁ bound₂
  have upper (g : SetMembers geometry.actors) (bound : a.iso g d ≤ X) :
      ∀ y ∈ geometry.carrier,
        ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw d)) y ∈ geometry.action →
        ZFSet.pair y (SetMembers.raw X) ∈ geometry.order := by
    intro y hy entry
    have acted := (geometry.action_code.act_eq_iff g d (SetMembers.ofMem y hy)).2
      (by simpa only [SetMembers.raw_ofMem] using entry)
    change ZFSet.pair (SetMembers.raw (geometry.action_code.act g d)) (SetMembers.raw X)
      ∈ geometry.order at bound
    simpa only [acted, SetMembers.raw_ofMem] using bound
  obtain ⟨k, hk, l, hl, rectangle⟩ := fulfilled.rectangles
    _ _ _ _ _ _ request (SetMembers.raw_mem X) (upper g₁ bound₁) (upper g₂ bound₂)
  let h₁ := SetMembers.ofMem k hk
  let h₂ := SetMembers.ofMem l hl
  have code : RectangleAtBoundCode geometry.carrier geometry.order geometry.meetGraph
      geometry.action (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw d)
      (SetMembers.raw g₁) (SetMembers.raw g₂) (SetMembers.raw X)
      (SetMembers.raw h₁) (SetMembers.raw h₂) := by
    simpa only [h₁, h₂, SetMembers.raw_ofMem] using rectangle
  have agree (g h : SetMembers geometry.actors) (v : SetMembers geometry.carrier)
      (rawAgree : ActionAgreementBelow geometry.carrier geometry.order geometry.action
        (SetMembers.raw g) (SetMembers.raw h) (SetMembers.raw v)) :
      ∀ i, i ≤ v → a.iso g i = a.iso h i := by
    intro i lower
    apply SetMembers.raw_injective
    exact rawAgree.entry_eq geometry.action_code (SetMembers.raw_mem h) (SetMembers.raw_mem i)
      lower (geometry.action_code.act_mem g i) (geometry.action_code.act_mem h i)
  have agree₁ := agree h₁ g₁ V code.first_agreement
  have agree₂ := agree h₂ g₂ V code.second_agreement
  have agreeW := agree h₁ h₂ W code.common_agreement
  obtain ⟨v, hv, w, hw, y, hy, z, hz, t, ht,
    gv, hwv, ky, lz, kt, _, meet₁, meet₂, meetW⟩ := code.values
  have value (g : SetMembers geometry.actors) (x : SetMembers geometry.carrier)
      (y : ZFSet.{u}) (hy : y ∈ geometry.carrier)
      (entry : ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw x)) y ∈ geometry.action) :
      SetMembers.raw (a.iso g x) = y := by
    have acted := (geometry.action_code.act_eq_iff g x (SetMembers.ofMem y hy)).2
      (by simpa only [SetMembers.raw_ofMem] using entry)
    exact (congrArg SetMembers.raw acted).trans (SetMembers.raw_ofMem y hy)
  have eqv := value g₁ V v hv gv
  have eqw := value g₂ V w hw hwv
  have eqy := value h₁ d y hy ky
  have eqz := value h₂ d z hz lz
  have eqt := value h₁ W t ht kt
  have relative (g h : SetMembers geometry.actors) (v : SetMembers geometry.carrier)
      (agreement : ∀ i, i ≤ v → a.iso h i = a.iso g i) :
      g⁻¹ * h ∈ a.principalFix v := by
    intro i lower
    rw [a.mul, agreement i lower, a.point_inv_left]
  refine ⟨h₁, h₂, code, relative g₁ h₁ V agree₁, relative g₂ h₂ V agree₂,
    relative h₁ h₂ W (fun i lower => (agreeW i lower).symm), ?_, ?_, ?_⟩
  · rw [agree₁ V le_rfl]
    apply (geometry.meet.smallMeet_eq_iff _ _ _).2
    change ZFSet.pair (ZFSet.pair (SetMembers.raw (a.iso h₁ d)) (SetMembers.raw X))
      (SetMembers.raw (a.iso g₁ V)) ∈ geometry.meetGraph
    rw [eqy, eqv]
    exact meet₁
  · rw [agree₂ V le_rfl]
    apply (geometry.meet.smallMeet_eq_iff _ _ _).2
    change ZFSet.pair (ZFSet.pair (SetMembers.raw (a.iso h₂ d)) (SetMembers.raw X))
      (SetMembers.raw (a.iso g₂ V)) ∈ geometry.meetGraph
    rw [eqz, eqw]
    exact meet₂
  · apply (geometry.meet.smallMeet_eq_iff _ _ _).2
    change ZFSet.pair (ZFSet.pair (SetMembers.raw (a.iso h₁ d))
      (SetMembers.raw (a.iso h₂ d))) (SetMembers.raw (a.iso h₁ W)) ∈ geometry.meetGraph
    rw [eqy, eqz, eqt]
    exact meetW

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

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

theorem internalRowAction_rectangle_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∀ (p r : Q) (D X V W : L) (g₁ g₂ h₁ h₂ : G),
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i.val ≤ X) →
      r ≤ act.iso g₁ p → r ≤ act.iso g₂ p →
      (∀ i, i ≤ V → a.iso h₁ i = a.iso g₁ i) →
      (∀ i, i ≤ V → a.iso h₂ i = a.iso g₂ i) →
      (∀ i, i ≤ W → a.iso h₁ i = a.iso h₂ i) →
      (∀ i, i ≤ a.iso h₁ D → i ≤ X → i ≤ a.iso h₁ V) →
      (∀ i, i ≤ a.iso h₂ D → i ≤ X → i ≤ a.iso h₂ V) →
      (∀ i, i ≤ a.iso h₁ D → i ≤ a.iso h₂ D → i ≤ a.iso h₁ W) →
      ∃ t : Q, SetMembers.raw t =
          (SetMembers.raw r ∪ SetMembers.raw (act.iso h₁ p)) ∪ SetMembers.raw (act.iso h₂ p) ∧
        t ≤ r ∧ t ≤ act.iso h₁ p ∧ t ≤ act.iso h₂ p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act p r D X V W g₁ g₂ h₁ h₂ bp br ref₁ ref₂ agree₁ agree₂ agreeW overlap₁ overlap₂ overlapW
  have one := M.internalRowAction_aligned_agrees a s b C pairing unions powers separation infinite
    hL hC hG graph p r D X V g₁ h₁ bp br ref₁ overlap₁ agree₁
  have two := M.internalRowAction_aligned_agrees a s b C pairing unions powers separation infinite
    hL hC hG graph p r D X V g₂ h₂ bp br ref₂ overlap₂ agree₂
  have movedBound := M.internalRowAction_usedRows_bounded a s b C pairing unions powers separation
    infinite hL hC hG graph h₂ p D bp
  have pair := M.internalRowAction_aligned_agrees a s b C pairing unions powers separation infinite
    hL hC hG graph p (act.iso h₂ p) D (a.iso h₂ D) W h₂ h₁ bp movedBound
      le_rfl overlapW agreeW
  obtain ⟨q, rawq, qr, qh₁⟩ := M.countableFunction_common_extension pairing unions powers separation
    infinite choice (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) r (act.iso h₁ p) one
  have compatible : ∀ x y z, ZFSet.pair x y ∈ SetMembers.raw q →
      ZFSet.pair x z ∈ SetMembers.raw (act.iso h₂ p) → y = z := by
    intro x y z left right
    rw [rawq] at left
    rcases ZFSet.mem_union.1 left with left | left
    · exact two x y z left right
    · exact (pair x z y right left).symm
  obtain ⟨t, rawt, tq, th₂⟩ := M.countableFunction_common_extension pairing unions powers separation
    infinite choice (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) q (act.iso h₂ p) compatible
  refine ⟨t, ?_, le_trans tq qr, le_trans tq qh₁, th₂⟩
  exact rawt.trans (congrArg (fun z => z ∪ SetMembers.raw (act.iso h₂ p)) rawq)

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem decoded_rectangle_request :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    let a := geometry.decodedAction
    ∀ (V W d : SetMembers geometry.carrier) (g h : SetMembers geometry.actors),
      V ≤ d → W ≤ d →
      g ∈ a.principalFix (geometry.meet.smallMeet V W) →
      h ∈ a.principalFix (geometry.meet.smallMeet V W) →
      geometry.meet.smallMeet (a.iso g d) (a.iso h d) = geometry.meet.smallMeet V W →
      ExternalRectangleCode geometry.carrier geometry.actors geometry.order
        geometry.meetGraph geometry.action (SetMembers.raw V) (SetMembers.raw W)
        (SetMembers.raw d) (SetMembers.raw g) (SetMembers.raw h) := by
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  intro a V W d g h vd wd fixesG fixesH separated
  let meet := geometry.meet.smallMeet V W
  refine ⟨SetMembers.raw_mem V, SetMembers.raw_mem W, SetMembers.raw_mem d,
    SetMembers.raw_mem g, SetMembers.raw_mem h, vd, wd,
    SetMembers.raw meet, SetMembers.raw_mem meet, geometry.meet.smallMeet_entry V W, ?_, ?_⟩
  · intro x hx y hy lower
    let z := SetMembers.ofMem x hx
    let value := SetMembers.ofMem y hy
    have below : z ≤ meet := by
      change ZFSet.pair (SetMembers.raw z) (SetMembers.raw meet) ∈ geometry.order
      simpa only [z, SetMembers.raw_ofMem] using lower
    have agree : a.iso g z = a.iso h z := (fixesG z below).trans (fixesH z below).symm
    change geometry.action_code.act g z = geometry.action_code.act h z at agree
    have iff : ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw z)) (SetMembers.raw value)
        ∈ geometry.action ↔
        ZFSet.pair (ZFSet.pair (SetMembers.raw h) (SetMembers.raw z)) (SetMembers.raw value)
        ∈ geometry.action := by
      rw [← geometry.action_code.act_eq_iff, ← geometry.action_code.act_eq_iff, agree]
    simpa only [z, value, SetMembers.raw_ofMem] using iff
  · intro y hy z hz v hv entries
    have first := (geometry.action_code.act_eq_iff g d (SetMembers.ofMem y hy)).2
      (by simpa only [SetMembers.raw_ofMem] using entries.1)
    have second := (geometry.action_code.act_eq_iff h d (SetMembers.ofMem z hz)).2
      (by simpa only [SetMembers.raw_ofMem] using entries.2.1)
    have last := (geometry.action_code.act_eq_iff g meet (SetMembers.ofMem v hv)).2
      (by simpa only [SetMembers.raw_ofMem] using entries.2.2)
    have same : geometry.meet.smallMeet (SetMembers.ofMem y hy) (SetMembers.ofMem z hz) =
        SetMembers.ofMem v hv := by
      rw [← first, ← second]
      exact separated.trans ((fixesG meet le_rfl).symm.trans last)
    simpa only [SetMembers.raw_ofMem] using (geometry.meet.smallMeet_eq_iff _ _ _).1 same

end PartitionPilot.Forcing.GroundMainFinalGeometry

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalStructuralRectangleRefinements
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

theorem binaryRowStructural_aligned_rectangle_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L)
    (meetComm : ∀ x y : L, meet x y = meet y x)
    (meetLeft : ∀ x y : L, meet x y ≤ x)
    (meetRight : ∀ x y : L, meet x y ≤ y)
    (meetGreatest : ∀ x y z : L, z ≤ x → z ≤ y → z ≤ meet x y)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (muOrdinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
      (g1 g2 h1 h2 : G) (D X V W : L),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA →
      StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
      q ≤ upperAct.iso g1 p → q ≤ upperAct.iso g2 p →
      (∀ i : L, s.encode i ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i ≤ D) →
      (∀ i : L, s.encode i ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw oldRow) → i ≤ X) →
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
      (∀ z ∈ oldA, ZFSet.pair z (s.encode X) ∈
        stageOneDataBounds oldA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
      g1⁻¹ * h1 ∈ a.principalFix V → g2⁻¹ * h2 ∈ a.principalFix V →
      h1⁻¹ * h2 ∈ a.principalFix W →
      meet (a.iso h1 D) X = a.iso h1 V →
      meet (a.iso h2 D) X = a.iso h2 V →
      meet (a.iso h1 D) (a.iso h2 D) = a.iso h1 W →
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
      let movedA1 := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h1) A
      let movedA2 := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h2) A
      ∃ row : SetMembers c.carrier, ∃ result : SetMembers upperQ,
        SetMembers.raw row = (SetMembers.raw oldRow ∪ SetMembers.raw (act.iso h1 r)) ∪
          SetMembers.raw (act.iso h2 r) ∧
        SetMembers.raw result = ZFSet.pair (c.encode row) (movedA2 ∪ (movedA1 ∪ oldA)) ∧
        result ≤ q ∧ result ≤ upperAct.iso h1 p ∧ result ≤ upperAct.iso h2 p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace coordinates two carrier forcingOrder
    forcingAction omega topMem topRows packed I anchors upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro upperAct p q r oldRow A oldA g1 g2 h1 h2 D X V W pCode qCode prepared below1 below2
    usedD usedX dataD dataX relative1 relative2 between overlap1 overlap2 overlap12 descent movedA1 movedA2
  have source : ZFSet.pair (c.encode r) A ∈ upperQ := pCode ▸ SetMembers.raw_mem p
  have oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ := qCode ▸ SetMembers.raw_mem q
  have reference1 := M.semanticStructuralOrder_action_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hs hh stagesOrdinal trace g1 p q r oldRow A oldA pCode qCode below1
  have reference2 := M.semanticStructuralOrder_action_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hs hh stagesOrdinal trace g2 p q r oldRow A oldA pCode qCode below2
  have agree (g h : G) (B : L) (relative : g⁻¹ * h ∈ a.principalFix B)
      (i : L) (hi : i ≤ B) : a.iso h i = a.iso g i := by
    have moved := congrArg (a.iso g) (relative i hi)
    simpa only [a.mul, a.point_inv_right] using moved
  obtain ⟨row, rowCode, rowBelowOld, rowBelowH1, rowBelowH2⟩ :=
    M.internalRowAction_rectangle_union a s b C pairing unions powers separation infinite hL hC hG graph
      choice r oldRow D X V W g1 g2 h1 h2
      (fun i hi => usedD i.val hi) (fun i hi => usedX i.val hi) reference1.1 reference2.1
      (agree g1 h1 V relative1) (agree g2 h2 V relative2)
      (fun i hi => (agree h1 h2 W between i hi).symm)
      (fun i hi hx => overlap1 ▸ meetGreatest _ _ i hi hx)
      (fun i hi hx => overlap2 ▸ meetGreatest _ _ i hi hx)
      (fun i hi hj => overlap12 ▸ meetGreatest _ _ i hi hj)
  have candidate := (M.mem_refinementHistoryForcing c.carrier lifted stages packed
    (ZFSet.pair (c.encode r) A)).1 source |>.1
  have hA : A ∈ M.sets := ((M.mem_groundSmallSubsets _ _ A).1 (ZFSet.pair_mem_prod.1 candidate).2).1
  have transported1 := M.binaryRowStructuralAssignmentImage_dataBound a s b C pairing unions powers
    separation collection infinite hL order hC hG graph nodeMaps supports directed hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace h1 D A hA dataD
  have transported2 := M.binaryRowStructuralAssignmentImage_dataBound a s b C pairing unions powers
    separation collection infinite hL order hC hG graph nodeMaps supports directed hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace h2 D A hA dataD
  have unionFacts := M.semanticStructuralTrace_aligned_rectangle_union c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace infinite choice small meet I S mu s.nonbottom.carrier tuples
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun D f _ tau entry bound => M.liftedRowTuple_supported a s b C pairing unions powers separation
      infinite hL hC hG graph hmu muOrdinal valid f tau D entry bound.2)
    r oldRow row A oldA g1 g2 h1 h2 D X V W source oldSource (pCode ▸ prepared)
    rowBelowOld reference1.1 reference2.1 rowBelowH1 rowBelowH2 reference1.2 reference2.2
    relative1 relative2 between overlap1 overlap2 overlap12 meetComm meetLeft meetRight meetGreatest
    transported1.2.2 transported2.2.2 dataX descent
  let result : SetMembers upperQ := SetMembers.ofMem _ unionFacts.1
  have resultCode : SetMembers.raw result = ZFSet.pair (c.encode row) (movedA2 ∪ (movedA1 ∪ oldA)) :=
    SetMembers.raw_ofMem _ _
  have movedCode (h : G) := M.semanticStructuralAction_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace h p r A pCode
  refine ⟨row, result, rowCode, resultCode, ?_, ?_, ?_⟩
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw q) ∈ _
    rw [resultCode, qCode]
    exact unionFacts.2.1
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw (upperAct.iso h1 p)) ∈ _
    rw [resultCode, movedCode h1]
    exact unionFacts.2.2.1
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw (upperAct.iso h2 p)) ∈ _
    rw [resultCode, movedCode h2]
    exact unionFacts.2.2.2

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

theorem structural_rectangle_union
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
    (g1 g2 : SetMembers geometry.actors) (dBound X V W : SetMembers geometry.carrier),
    SetMembers.raw p = ZFSet.pair (c.encode r) A →
    SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
    q ≤ upperAct.iso g1 p → q ≤ upperAct.iso g2 p →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw r) → i ≤ dBound) →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw oldRow) → i ≤ X) →
    (∀ z ∈ A, ZFSet.pair z (s.encode dBound) ∈
      stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    (∀ z ∈ oldA, ZFSet.pair z (s.encode X) ∈
      stageOneDataBounds oldA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    ExternalRectangleCode geometry.carrier geometry.actors geometry.order geometry.meetGraph geometry.action
      (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw dBound)
      (SetMembers.raw g1) (SetMembers.raw g2) →
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
    ∃ h1 h2 : SetMembers geometry.actors,
      RectangleAtBoundCode geometry.carrier geometry.order geometry.meetGraph geometry.action
        (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw dBound)
        (SetMembers.raw g1) (SetMembers.raw g2) (SetMembers.raw X)
        (SetMembers.raw h1) (SetMembers.raw h2) ∧
    (let movedA1 := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h1) A;
    let movedA2 := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h2) A;
    ∃ row : SetMembers c.carrier, ∃ result : SetMembers upperQ,
      SetMembers.raw row = (SetMembers.raw oldRow ∪ SetMembers.raw (act.iso h1 r)) ∪
        SetMembers.raw (act.iso h2 r) ∧
      SetMembers.raw result = ZFSet.pair (c.encode row) (movedA2 ∪ (movedA1 ∪ oldA)) ∧
      result ≤ q ∧ result ≤ upperAct.iso h1 p ∧ result ≤ upperAct.iso h2 p) := by
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
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  intro p q r oldRow A oldA g1 g2 dBound X V W pCode qCode prepared below1 below2
    usedD usedX dataD dataX request bound1 bound2 descent
  have meetComm (x y : SetMembers geometry.carrier) :
      geometry.meet.smallMeet x y = geometry.meet.smallMeet y x := by
    apply le_antisymm
    · exact geometry.meet.toSmallMeetOrder.le_meet
        (geometry.meet.toSmallMeetOrder.meet_le_right _ _) (geometry.meet.toSmallMeetOrder.meet_le_left _ _)
    · exact geometry.meet.toSmallMeetOrder.le_meet
        (geometry.meet.toSmallMeetOrder.meet_le_right _ _) (geometry.meet.toSmallMeetOrder.meet_le_left _ _)
  obtain ⟨h1, h2, rectangle, relative1, relative2, between, overlap1, overlap2, overlap12⟩ :=
    fulfilled.decoded_rectangle_action_data V W dBound X g1 g2 request bound1 bound2
  refine ⟨h1, h2, rectangle, ?_⟩
  exact M.binaryRowStructural_aligned_rectangle_union a s b columns pairing unions powers separation
    collection infinite hL order hC hG graph nodeMaps supports directed choice small geometry.meet.smallMeet
    meetComm geometry.meet.toSmallMeetOrder.meet_le_left geometry.meet.toSmallMeetOrder.meet_le_right
    (fun _ _ _ left right => geometry.meet.toSmallMeetOrder.le_meet left right) hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace p q r oldRow A oldA g1 g2 h1 h2 dBound X V W pCode qCode prepared below1 below2
    usedD usedX dataD dataX relative1 relative2 between overlap1 overlap2 overlap12 descent






theorem structural_rectangle_refinement
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
  let upper := SetMembers.presentation upperQ
  ∀ (p : SetMembers upperQ) (sourceRow : SetMembers c.carrier) (A : ZFSet.{u})
    (dBound V W : SetMembers geometry.carrier) (x y : Name upper),
    SetMembers.raw p = ZFSet.pair (c.encode sourceRow) A →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈
      rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw sourceRow) → i ≤ dBound) →
    (∀ z ∈ A, ZFSet.pair z (s.encode dBound) ∈
      stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    V ≤ dBound → W ≤ dBound →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
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
    ∀ (g1 g2 : SetMembers geometry.actors),
      g1 ∈ a.principalFix (geometry.meet.smallMeet V W) →
      g2 ∈ a.principalFix (geometry.meet.smallMeet V W) →
      geometry.meet.smallMeet (a.iso g1 dBound) (a.iso g2 dBound) = geometry.meet.smallMeet V W →
      ∀ r, r ≤ upperAct.iso g1 p → r ≤ upperAct.iso g2 p →
        DenseBelow r (upperAct.RectangleWitness upper p x y g1 g2) := by
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
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  let upper := SetMembers.presentation upperQ
  intro p sourceRow A dBound V W x y pCode prepared usedD dataD vd wd sx sy descent
    g1 g2 fixed1 fixed2 separated r ref1 ref2 q qr
  obtain ⟨rawRow, rowMem, oldA, _, qCodeRaw⟩ := ZFSet.mem_prod.1
    (M.refinementHistoryForcing_shape c.carrier lifted stages packed (SetMembers.raw_mem q))
  let oldRow := SetMembers.ofMem rawRow rowMem
  have qCode : SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA := by
    exact qCodeRaw.trans (congrArg (fun z => ZFSet.pair z oldA)
      (SetMembers.raw_ofMem rawRow rowMem).symm)
  obtain ⟨X, upper1, upper2, usedX, dataX⟩ := fulfilled.structural_bounds_with
    collection infinite choice columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    q oldRow oldA (a.iso g1 dBound) (a.iso g2 dBound) qCode
  have request := geometry.decoded_rectangle_request V W dBound g1 g2 vd wd fixed1 fixed2 separated
  obtain ⟨h1, h2, rectangle, _row, result, _rowCode, _resultCode, belowQ, below1, below2⟩ :=
    fulfilled.structural_rectangle_union collection infinite choice small columns hColumns
      hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace p q sourceRow oldRow A oldA g1 g2 dBound X V W
      pCode qCode prepared (le_trans qr ref1) (le_trans qr ref2) usedD usedX dataD dataX
      request upper1 upper2 descent
  have agree (g h : SetMembers geometry.actors) (v : SetMembers geometry.carrier)
      (rawAgree : ActionAgreementBelow geometry.carrier geometry.order geometry.action
        (SetMembers.raw g) (SetMembers.raw h) (SetMembers.raw v)) :
      ∀ i, i ≤ v → a.iso g i = a.iso h i := by
    intro i lower
    apply SetMembers.raw_injective
    exact rawAgree.entry_eq geometry.action_code (SetMembers.raw_mem h) (SetMembers.raw_mem i)
      lower (geometry.action_code.act_mem g i) (geometry.action_code.act_mem h i)
  let geom := geometry.action_code.toOrderAction geometry.group_code geometry.meet
  exact ⟨result, belowQ, h1, h2, below1, below2,
    upperAct.act_eq_of_support_agreement geom upper sx (agree h1 g1 V rectangle.first_agreement),
    upperAct.act_eq_of_support_agreement geom upper sx (agree h2 g2 V rectangle.second_agreement),
    upperAct.act_eq_of_support_agreement geom upper sy (agree h1 h2 W rectangle.common_agreement)⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalStructuralSeparationRefinements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
open scoped ZFSet
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

theorem structural_separation_refinement
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
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid
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
  ∀ (p : SetMembers upperQ) (sourceRow : SetMembers c.carrier) (A : ZFSet.{u})
    (W dBound : SetMembers geometry.carrier),
    SetMembers.raw p = ZFSet.pair (c.encode sourceRow) A →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw sourceRow) → i ≤ dBound) →
    (∀ z ∈ A, ZFSet.pair z (s.encode dBound) ∈
      stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    W ≤ dBound →
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
    ∀ (g1 g2 : SetMembers geometry.actors),
      g1 ∈ a.principalFix W → g2 ∈ a.principalFix W →
      ∀ r, r ≤ upperAct.iso g1 p →
        DenseBelow r (upperAct.SeparationWitness (a.principalFix W)
          (fun g h => geometry.meet.smallMeet (a.iso g dBound) (a.iso h dBound) = W) p g1 g2) := by
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
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  intro p sourceRow A W dBound pCode prepared usedD dataD wd descent
    g1 g2 fixed1 fixed2 r ref1 q qr
  obtain ⟨oldRow, oldA, _, qCode⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier lifted stages packed) (SetMembers.raw_mem q)
  obtain ⟨X, bound1, bound2, usedX, dataX⟩ := fulfilled.structural_bounds_with
    collection infinite choice columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    q oldRow oldA (a.iso g1 dBound) (a.iso g2 dBound) qCode
  obtain ⟨h, fixed, _, apart1, apart2, _, result, _, _, toOld, toCopy⟩ :=
    fulfilled.structural_separating_copy_union collection infinite choice small columns hColumns
      hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace p q sourceRow oldRow A oldA g1 g2 dBound X W
      pCode qCode prepared (le_trans qr ref1) usedD usedX dataD dataX wd fixed1 fixed2
      bound1 bound2 descent
  exact ⟨result, toOld, h, fixed, toCopy, apart1, apart2⟩

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

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem separationWitness_mem (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (action : a.actionGraph s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (Sep : G → G → Prop)
    (hSep : (t.product t).subset (fun gh => Sep gh.1 gh.2) ∈ M.sets)
    (p : P) (g₁ g₂ : G) : s.subset (a.SeparationWitness K Sep p g₁ g₂) ∈ M.sets := by
  let params := extend (s.encode p) (extend (t.encode g₁) (extend (t.encode g₂)
    (extend (t.subset (fun g => g ∈ K)) (extend ((t.product t).subset (fun gh => Sep gh.1 gh.2))
      (extend s.carrier (extend t.carrier (extend (a.actionGraph s t)
        (extend s.conditionOrder Fin.elim0))))))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases (M.transitive carrier (s.encode_mem p))
      (Fin.cases (M.transitive group (t.encode_mem g₁))
        (Fin.cases (M.transitive group (t.encode_mem g₂))
          (Fin.cases hK (Fin.cases hSep (Fin.cases carrier
            (Fin.cases group (Fin.cases action (Fin.cases order (fun i => Fin.elim0 i)))))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.separationWitnessFormula params members carrier
  have correct (q : P) : BoundedFormula.Truth BoundedFormula.separationWitnessFormula
      (extend (s.encode q) params) ↔ q ∈ a.SeparationWitness K Sep p g₁ g₂ := by
    simp only [BoundedFormula.separationWitnessFormula, BoundedFormula.separationWitnessBody,
      BoundedFormula.truth_exMem, BoundedFormula.Truth,
      BoundedFormula.truth_tripleMembershipFormula, BoundedFormula.truth_pairMembershipFormula]
    change (∃ h ∈ t.carrier, ∃ p' ∈ s.carrier,
      h ∈ t.subset (fun g => g ∈ K) ∧ ZFSet.pair (ZFSet.pair h (s.encode p)) p' ∈ a.actionGraph s t ∧
      ZFSet.pair (s.encode q) p' ∈ s.conditionOrder ∧
      ZFSet.pair h (t.encode g₁) ∈ (t.product t).subset (fun gh => Sep gh.1 gh.2) ∧
      ZFSet.pair h (t.encode g₂) ∈ (t.product t).subset (fun gh => Sep gh.1 gh.2)) ↔ _
    have sep (g h : G) : ZFSet.pair (t.encode g) (t.encode h) ∈
        (t.product t).subset (fun gh => Sep gh.1 gh.2) ↔ Sep g h :=
      (t.product t).encode_mem_subset _ (g,h)
    constructor
    · rintro ⟨h,hh,p',hp',fixed,acted,lower,first,second⟩
      obtain ⟨h,rfl⟩ := (t.mem_carrier h).1 hh
      obtain ⟨p',rfl⟩ := (s.mem_carrier p').1 hp'
      rw [a.triple_mem_actionGraph] at acted
      exact ⟨h,(t.encode_mem_subset _ h).1 fixed,
        acted ▸ (s.pair_mem_conditionOrder _ _).1 lower,(sep h g₁).1 first,(sep h g₂).1 second⟩
    · rintro ⟨h,fixed,lower,first,second⟩
      exact ⟨t.encode h,t.encode_mem h,s.encode (a.iso h p),s.encode_mem _,
        (t.encode_mem_subset _ h).2 fixed,(a.triple_mem_actionGraph s t h p _).2 rfl,
        (s.pair_mem_conditionOrder _ _).2 lower,(sep h g₁).2 first,(sep h g₂).2 second⟩
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.separationWitnessFormula
      (extend z params)) s.carrier = s.subset (a.SeparationWitness K Sep p g₁ g₂) := by
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


section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (action : a.actionGraph s t ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
include pairing unions powers separation collection carrier order group action maps

omit order action in
private theorem coded_action (g : G) (x : Name s) (hx : x.val ∈ M.sets)
    (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets codedNameActionFormula (extend (t.encode g) (extend x.val (extend z
      (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      z = (a.act s g x).val := by
  rw [M.realize_codedNameActionFormula a s t pairing unions powers separation collection
    carrier group maps g x.val z hx hz]
  constructor
  · rintro ⟨y, eq, out⟩
    have same : y.val = x := Subtype.ext eq
    simpa only [same] using out
  · intro eq
    exact ⟨⟨x, hx⟩, rfl, eq⟩

theorem realize_rectangleWitnessFormula (p : P) (x y : Name s)
    (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets) (g₁ g₂ : G) (q : P) :
    Realize M.sets rectangleWitnessFormula
      (extend (s.encode q) (rectangleParameters a s t p x y g₁ g₂)) ↔
      q ∈ a.RectangleWitness s p x y g₁ g₂ := by
  have cp (r : P) := M.transitive carrier (s.encode_mem r)
  have cg (g : G) := M.transitive group (t.encode_mem g)
  have ax (g : G) := M.act_mem s a t pairing unions powers separation collection carrier maps g x hx
  rw [rectangleWitnessFormula, M.realize_exConditions t 8 _ _ group rfl]
  apply exists_congr
  intro h₁
  rw [M.realize_exConditions t 9 _ _ group rfl]
  apply exists_congr
  intro h₂
  rw [M.realize_exConditions s 8 _ _ carrier rfl]
  change (∃ p₁, Realize M.sets _ _) ↔ _
  have body (p₁ p₂ : P) :
      Realize M.sets rectangleBodyFormula (extend (s.encode p₂) (extend (s.encode p₁)
        (extend (t.encode h₂) (extend (t.encode h₁)
          (extend (s.encode q) (rectangleParameters a s t p x y g₁ g₂)))))) ↔
      a.iso h₁ p = p₁ ∧ a.iso h₂ p = p₂ ∧ q ≤ p₁ ∧ q ≤ p₂ ∧
        a.act s h₁ x = a.act s g₁ x ∧ a.act s h₂ x = a.act s g₂ x ∧
        a.act s h₁ y = a.act s h₂ y := by
    let env := extend (s.encode p₂) (extend (s.encode p₁) (extend (t.encode h₂)
      (extend (t.encode h₁) (extend (s.encode q) (rectangleParameters a s t p x y g₁ g₂)))))
    have members : ∀ i, env i ∈ M.sets := (Fin.cases (cp p₂) (Fin.cases (cp p₁) (Fin.cases (cg h₂) (Fin.cases (cg h₁) (Fin.cases (cp q) (Fin.cases (M.transitive carrier (s.encode_mem p)) (Fin.cases (hx) (Fin.cases (hy) (Fin.cases (ax g₁) (Fin.cases (ax g₂) (Fin.cases (carrier) (Fin.cases (order) (Fin.cases (group) (Fin.cases (action) (Fin.cases (maps) (fun i => Fin.elim0 i))))))))))))))))
    rw [rectangleBodyFormula]
    change (Realize M.sets rectangleOrderFormula.toFormula env ∧ _ ∧ _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ members]
    simp only [rectangleOrderFormula, BoundedFormula.Truth,
      BoundedFormula.truth_tripleMembershipFormula, BoundedFormula.truth_pairMembershipFormula]
    change ((ZFSet.pair (ZFSet.pair (t.encode h₁) (s.encode p)) (s.encode p₁) ∈ a.actionGraph s t ∧
      ZFSet.pair (ZFSet.pair (t.encode h₂) (s.encode p)) (s.encode p₂) ∈ a.actionGraph s t ∧
      ZFSet.pair (s.encode q) (s.encode p₁) ∈ s.conditionOrder ∧
      ZFSet.pair (s.encode q) (s.encode p₂) ∈ s.conditionOrder) ∧ _ ∧ _ ∧ _) ↔ _
    rw [a.triple_mem_actionGraph, a.triple_mem_actionGraph,
      s.pair_mem_conditionOrder, s.pair_mem_conditionOrder]
    simp only [realize_ex]
    change ((_ ∧ _ ∧ _ ∧ _) ∧ _ ∧ _ ∧
      (∃ z ∈ M.sets, Realize M.sets _ _ ∧ Realize M.sets _ _)) ↔ _
    simp only [realize_atomicApplication, map_extend, map_empty]
    change ((a.iso h₁ p = p₁ ∧ a.iso h₂ p = p₂ ∧ q ≤ p₁ ∧ q ≤ p₂) ∧
      Realize M.sets codedNameActionFormula (extend (t.encode h₁) (extend x.val (extend (a.act s g₁ x).val (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ∧
      Realize M.sets codedNameActionFormula (extend (t.encode h₂) (extend x.val (extend (a.act s g₂ x).val (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ∧
      (∃ z ∈ M.sets, Realize M.sets codedNameActionFormula (extend (t.encode h₁) (extend y.val (extend z (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ∧
        Realize M.sets codedNameActionFormula (extend (t.encode h₂) (extend y.val (extend z (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))))) ↔ _
    rw [M.coded_action a s t pairing unions powers separation collection carrier group maps h₁ x hx _ (ax g₁),
      M.coded_action a s t pairing unions powers separation collection carrier group maps h₂ x hx _ (ax g₂)]
    have common : (∃ z ∈ M.sets,
        Realize M.sets codedNameActionFormula (extend (t.encode h₁) (extend y.val (extend z
          (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0))))) ∧
        Realize M.sets codedNameActionFormula (extend (t.encode h₂) (extend y.val (extend z
          (extend s.carrier (extend (a.conditionMapFamily s t) Fin.elim0)))))) ↔
        a.act s h₁ y = a.act s h₂ y := by
      constructor
      · rintro ⟨z, hz, first, second⟩
        rw [M.coded_action a s t pairing unions powers separation collection carrier group maps h₁ y hy z hz] at first
        rw [M.coded_action a s t pairing unions powers separation collection carrier group maps h₂ y hy z hz] at second
        exact Subtype.ext (first.symm.trans second)
      · intro eq
        have hz := M.act_mem s a t pairing unions powers separation collection carrier maps h₁ y hy
        refine ⟨(a.act s h₁ y).val, hz, ?_, ?_⟩
        · exact (M.coded_action a s t pairing unions powers separation collection carrier group maps h₁ y hy _ hz).2 rfl
        · exact (M.coded_action a s t pairing unions powers separation collection carrier group maps h₂ y hy _ hz).2 (congrArg Subtype.val eq)
    rw [common]
    constructor
    · rintro ⟨⟨e₁,e₂,b₁,b₂⟩,x₁,x₂,yy⟩
      exact ⟨e₁,e₂,b₁,b₂,Subtype.ext x₁.symm,Subtype.ext x₂.symm,yy⟩
    · rintro ⟨e₁,e₂,b₁,b₂,x₁,x₂,yy⟩
      exact ⟨⟨e₁,e₂,b₁,b₂⟩,congrArg Subtype.val x₁.symm,congrArg Subtype.val x₂.symm,yy⟩
  constructor
  · rintro ⟨p₁, rest⟩
    obtain ⟨p₂, rest⟩ := (M.realize_exConditions s 9 _ _ carrier rfl).1 rest
    obtain ⟨rfl,rfl,b₁,b₂,x₁,x₂,yy⟩ := (body p₁ p₂).1 rest
    exact ⟨b₁,b₂,x₁,x₂,yy⟩
  · rintro ⟨b₁,b₂,x₁,x₂,yy⟩
    refine ⟨a.iso h₁ p, (M.realize_exConditions s 9 _ _ carrier rfl).2 ⟨a.iso h₂ p, ?_⟩⟩
    exact (body _ _).2 ⟨rfl,rfl,b₁,b₂,x₁,x₂,yy⟩

theorem rectangleWitness_mem (p : P) (x y : Name s)
    (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets) (g₁ g₂ : G) :
    s.subset (a.RectangleWitness s p x y g₁ g₂) ∈ M.sets := by
  let params := rectangleParameters a s t p x y g₁ g₂
  have ax (g : G) := M.act_mem s a t pairing unions powers separation collection carrier maps g x hx
  have members : ∀ i, params i ∈ M.sets := (Fin.cases (M.transitive carrier (s.encode_mem p)) (Fin.cases (hx) (Fin.cases (hy) (Fin.cases (ax g₁) (Fin.cases (ax g₂) (Fin.cases (carrier) (Fin.cases (order) (Fin.cases (group) (Fin.cases (action) (Fin.cases (maps) (fun i => Fin.elim0 i)))))))))))
  have selected := M.separation_mem separation rectangleWitnessFormula params members carrier
  have eq : ZFSet.sep (fun z => Realize M.sets rectangleWitnessFormula (extend z params)) s.carrier =
      s.subset (a.RectangleWitness s p x y g₁ g₂) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,rel⟩
      obtain ⟨q,rfl⟩ := (s.mem_carrier z).1 hz
      exact (s.encode_mem_subset _ q).2 ((M.realize_rectangleWitnessFormula a s t pairing unions powers separation collection carrier order group action maps p x y hx hy g₁ g₂ q).1 rel)
    · intro hz
      obtain ⟨q,hq,rfl⟩ := (s.mem_subset _ z).1 hz
      exact ⟨s.encode_mem q,(M.realize_rectangleWitnessFormula a s t pairing unions powers separation collection carrier order group action maps p x y hx hy g₁ g₂ q).2 hq⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem copyWitnessFamily_coded
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (action : a.actionGraph s t ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (Sep : G → G → Prop)
    (hSep : (t.product t).subset (fun gh => Sep gh.1 gh.2) ∈ M.sets)
    (p : P) (x y : Name s) (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets) :
    a.copyWitnessFamily s K Sep p x y ⊆ M.codedFamily s := by
  intro E member
  rcases member with ⟨r,g₁,g₂,rfl⟩ | ⟨r,g₁,g₂,rfl⟩
  · exact M.codedFamily_of_code s (M.localized_mem s separation carrier order
      (M.rectangleWitness_mem a s t pairing unions powers separation collection
        carrier order group action maps p x y hx hy g₁ g₂) r)
  · exact M.codedFamily_of_code s (M.localized_mem s separation carrier order
      (M.separationWitness_mem a s t separation carrier order group action K hK Sep hSep p g₁ g₂) r)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem forcesEq_mix_of_copy_refinements
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (small : M.sets.Countable)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (action : a.actionGraph s t ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (K : Subgroup G) (hK : t.subset (fun g => g ∈ K) ∈ M.sets)
    (Sep : G → G → Prop)
    (hSep : (t.product t).subset (fun gh => Sep gh.1 gh.2) ∈ M.sets)
    (p : P) (x y : Name s) (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets)
    (equal : Name.ForcesEq p x y)
    (rectangles : ∀ g₁ ∈ K, ∀ g₂ ∈ K, Sep g₁ g₂ → ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p →
        DenseBelow r (a.RectangleWitness s p x y g₁ g₂))
    (separating : ∀ g₁ ∈ K, ∀ g₂ ∈ K, ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p →
        DenseBelow r (a.SeparationWitness K Sep p g₁ g₂)) :
    Name.ForcesEq p x (a.mix s K p x) := by
  have groundMix := M.mix_mem a s t pairing unions powers separation collection
    carrier order group maps K hK p x hx
  have witnesses := M.copyWitnessFamily_coded a s t pairing unions powers separation
    collection carrier order group action maps K hK Sep hSep p x y hx hy
  let env : Assignment (M.nameDomain s) 2 :=
    extend ⟨x, hx⟩ (extend ⟨a.mix s K p x, groundMix⟩ Fin.elim0)
  change Forces (M.nameDomain s) (.equal 0 1) env p
  apply (M.ordinaryForces_iff_all_joint_generics s small carrier (.equal 0 1) env p).2
  intro H active coded ordinary
  change Name.eval {q | H.mem q} x = Name.eval {q | H.mem q} (a.mix s K p x)
  have copies : H.GenericFor (a.copyWitnessFamily s K Sep p x y) :=
    fun E hE => coded E (witnesses hE)
  have atomic : H.GenericFor (Name.atomicFamily (M.nameDomain s)) :=
    fun E hE => ordinary E (Or.inl hE)
  have translated : ∀ g, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g x) =
        Name.eval {q | H.mem q} (a.act s g y) := by
    intro g member
    exact Name.forcesEq_sound (M.nameDomain s) H atomic _
      (M.act_mem s a t pairing unions powers separation collection carrier maps g x hx) _
      (M.act_mem s a t pairing unions powers separation collection carrier maps g y hy)
      _ member (a.forcesEq_act s g equal)
  exact (a.mix_capture_from_refinements s K Sep p x y H copies active translated
    rectangles separating).symm

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

theorem structural_mixture_forcing
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
  ∀ (p : SetMembers upperQ) (sourceRow : SetMembers c.carrier) (A : ZFSet.{u})
    (V W : SetMembers geometry.carrier) (x y : Name upper),
    SetMembers.raw p = ZFSet.pair (c.encode sourceRow) A →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    Name.ForcesEq p x y →
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
    Name.ForcesEq p x
      (upperAct.mix upper (a.principalFix (geometry.meet.smallMeet V W)) p x) := by
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
  intro p sourceRow A V W x y pCode prepared hx hy sx sy equal descent
  obtain ⟨dBound, vd, wd, usedD, dataD⟩ := fulfilled.structural_bounds_with
    collection infinite choice columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    p sourceRow A V W pCode
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix,
      lifted, squared, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers
    separation carrier hLifted hs hPacked omega
  have hOrder : upper.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact M.refinementHistoryOrder_mem pairing unions powers separation carrier forcingOrder
      hLifted hs hPacked omega
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
  let B := geometry.meet.smallMeet V W
  have hK := M.supportBasis_fiber_mem b s a.principalFix pairing separation hG hL supports B
  have hSep := geometry.separatedActorPairs_mem pairing unions powers separation dBound B
  apply M.forcesEq_mix_of_copy_refinements upperAct upper b pairing unions powers separation
    collection small hQ hOrder hG hGraph maps (a.principalFix B) hK
    (fun g h => geometry.meet.smallMeet (a.iso g dBound) (a.iso h dBound) = B)
    hSep p x y hx hy equal
  · intro g1 fixed1 g2 fixed2 separated r ref1 ref2
    exact fulfilled.structural_rectangle_refinement
      collection infinite choice small columns hColumns hmu muOrdinal valid hLifted hSquared
      valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
      p sourceRow A dBound V W x y pCode prepared usedD dataD vd wd sx sy descent
      g1 g2 fixed1 fixed2 separated r ref1 ref2
  · intro g1 fixed1 g2 fixed2 r ref1 _ref2
    exact fulfilled.structural_separation_refinement
      collection infinite choice small columns hColumns hmu muOrdinal valid hLifted hSquared
      valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
      p sourceRow A B dBound pCode prepared usedD dataD
      (le_trans (geometry.meet.toSmallMeetOrder.meet_le_left V W) vd) descent
      g1 g2 fixed1 fixed2 r ref1

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment




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

theorem structural_dense_mixture_equalities_oai
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
  ∀ (p0 : SetMembers upperQ) (V W : SetMembers geometry.carrier) (x y : Name upper),
    x.val ∈ M.sets → y.val ∈ M.sets →
    a.principalFix V ≤ upperAct.stabilizer upper x →
    a.principalFix W ≤ upperAct.stabilizer upper y →
    Name.ForcesEq p0 x y →
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
    DenseBelow p0 {p | Name.ForcesEq p x
      (upperAct.mix upper (a.principalFix (geometry.meet.smallMeet V W)) p x)} := by
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
  intro p0 V W x y groundX groundY supportX supportY equal descent q below0
  have rowClosed := M.countable_function_internally_closed pairing unions powers separation
    infinite choice coordinates two
  obtain ⟨rawP, memberP, pq, prepared⟩ := fulfilled.exists_groundStoredPreparedStrengthening c
    collection infinite choice small smallD irreflexive rowClosed act lifted squared (c.encode ⊤)
    carrier forcingOrder forcingAction hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    topMem topRows stages history hs hh stagesOrdinal trace descent (SetMembers.raw q) (SetMembers.raw_mem q)
  let p : SetMembers upperQ := SetMembers.ofMem rawP memberP
  have pRaw : SetMembers.raw p = rawP := SetMembers.raw_ofMem _ _
  have below : p ≤ q := by
    change ZFSet.pair (SetMembers.raw p) (SetMembers.raw q) ∈
      M.refinementHistoryOrder c.carrier c.conditionOrder lifted stages packed
    rw [pRaw]
    exact pq
  have preparedP : StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier
      (SetMembers.raw p) := by
    rw [pRaw]
    exact prepared
  obtain ⟨sourceRow, A, _, pCode⟩ := exists_presentedRowAssignmentCoordinates c
    (M.refinementHistoryForcing_shape c.carrier lifted stages packed) (SetMembers.raw_mem p)
  refine ⟨p, below, ?_⟩
  exact fulfilled.toFinalFulfillment.structural_mixture_forcing
    collection infinite choice small columns hColumns hmu muOrdinal valid hLifted hSquared
    valid1 valid2 closed1 closed2 children1 children2 stages history hs hh stagesOrdinal trace
    p sourceRow A V W x y pCode preparedP groundX groundY supportX supportY
    (Name.forcesEq_mono equal (le_trans below below0)) descent






end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_dense_mixture_equalities_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.structural_dense_mixture_equalities_oai.{u, v}
