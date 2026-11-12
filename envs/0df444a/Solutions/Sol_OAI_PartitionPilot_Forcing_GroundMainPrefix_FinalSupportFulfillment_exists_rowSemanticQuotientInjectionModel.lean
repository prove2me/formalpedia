-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_rowSemanticQuotientInjectionModel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:26:11.266409+00:00
-- url     : https://prove2.me/submissions/47b2e8ca-4297-40dc-973c-f59b5fafea41

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
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundMainPrefix_FinalSupportFulfillment_structural_refinement_quotient_injection
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_countableRow_semanticStructuralTrace_jointZF_sequenceReflection

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

end PosetAction
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps
universe u v w
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]

namespace HereditarilySymmetric
variable {a : PosetAction G P} {s : Presentation P} {F : NormalSubgroupFamily G}

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundProductActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section



namespace PartitionPilot.SetRealization.Presentation

universe u
variable {I : Type u} [Bot I]

theorem nonbottom_encode (s : Presentation I) (x : {x : I // x ≠ ⊥}) :
    s.nonbottom.encode x = s.encode x.val := rfl

theorem mem_nonbottom_carrier (s : Presentation I) (z : ZFSet.{u}) :
    z ∈ s.nonbottom.carrier ↔ z ∈ s.carrier ∧ z ≠ s.encode ⊥ := by
  change z ∈ ZFSet.sep (fun w => w ≠ s.encode ⊥) s.carrier ↔ _
  exact ZFSet.mem_sep

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.PosetAction

universe u v
variable {G : Type v} [Group G] {I : Type u} [PartialOrder I] [OrderBot I]

theorem nonbottom_iso_val (a : PosetAction G I) (g : G) (x : {x : I // x ≠ ⊥}) :
    (a.nonbottom.iso g x).val = a.iso g x.val := rfl

end PartitionPilot.Forcing.PosetAction

end


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



namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} (s t : Presentation P)

theorem eval_presentationEquiv (H : Set P) (τ : Name s) :
    eval H (presentationEquiv s t τ) = eval H τ :=
  eval_rename t id H τ

end PartitionPilot.Forcing.Name

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

namespace PartitionPilot.Forcing.HereditarilySymmetric
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} {G : Type v} [Group G] [PartialOrder P]
variable {a : PosetAction G P} {s : Presentation P} {F : NormalSubgroupFamily G}

theorem presentationEquiv (t : Presentation P) {τ : Name s}
    (hs : HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a t F (Name.presentationEquiv s t τ) := by
  induction τ using Name.inductionOn with
  | step τ ih =>
    refine .mk ?_ ?_
    · rw [a.stabilizer_presentationEquiv]
      exact hs.symmetric
    · intro ν p entry
      obtain ⟨σ, q, old, rfl, _⟩ := (Name.entry_rename t id τ ν p).1 entry
      exact ih σ q old (hs.member old)

end PartitionPilot.Forcing.HereditarilySymmetric

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundNiceNameNormalization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps SetFormula
universe u v
namespace Name
variable {P : Type u} {s : Presentation P}

theorem familySet_hs {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (familySet ⊤ T valid) := by
  refine HereditarilySymmetric.mk (F.upward F.top ?_) ?_
  · intro g _
    exact act_familySet a T valid closed g
  · intro τ p entry
    exact children τ ((entry_familySet ⊤ T valid τ p).1 entry).1

end Name

end PartitionPilot.Forcing



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

namespace BoundedFormula

theorem truth_rowPositionSequenceAtFormula {n} (L r I delta f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowPositionSequenceAtFormula L r I delta f) env ↔
      RowPositionSequenceAt (env L) (env r) (env I) (env delta) (env f) := by
  simp only [rowPositionSequenceAtFormula, Truth, truth_functionFormula,
    truth_exMem, truth_imp, truth_pairMembershipFormula]
  change (ZFSet.IsFunc (env delta) (env I) (env f) ∧
    ∃ D ∈ env L, ∀ a ∈ env delta, ∀ x ∈ env I,
      ZFSet.pair a x ∈ env f → ZFSet.pair x D ∈ env r) ↔ _
  constructor
  · rintro ⟨function, D, hD, bounds⟩
    refine ⟨function, D, hD, ?_⟩
    intro a x entry
    have shape := ZFSet.pair_mem_prod.1 (function.1 entry)
    exact bounds a shape.1 x shape.2 entry
  · rintro ⟨function, D, hD, bounds⟩
    exact ⟨function, D, hD, fun a _ x _ entry => bounds a x entry⟩

theorem truth_rowPositionSequenceFormula {n} (L r I mu f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rowPositionSequenceFormula L r I mu f) env ↔
      RowPositionSequenceCode (env L) (env r) (env I) (env mu) (env f) := by
  simp only [rowPositionSequenceFormula, truth_disj, truth_exMem, truth_rowPositionSequenceAtFormula]
  change (RowPositionSequenceAt (env L) (env r) (env I) (env mu) (env f) ∨
    ∃ delta ∈ env mu, RowPositionSequenceAt (env L) (env r) (env I) delta (env f)) ↔ _
  constructor
  · rintro (whole | ⟨delta, hdelta, code⟩)
    · exact ⟨env mu, ZFSet.mem_insert _ _, whole⟩
    · exact ⟨delta, ZFSet.mem_insert_of_mem _ hdelta, code⟩
  · rintro ⟨delta, hdelta, code⟩
    rcases ZFSet.mem_insert_iff.1 hdelta with equal | hdelta
    · exact Or.inl (equal ▸ code)
    · exact Or.inr ⟨delta, hdelta, code⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_rowPositionSequences {L r I mu f : ZFSet.{u}} (ordinal : ordinalSetProperty mu) :
    f ∈ M.rowPositionSequences L r I mu ↔ f ∈ M.sets ∧ RowPositionSequenceCode L r I mu f := by
  rw [rowPositionSequences, ZFSet.mem_sep, M.mem_groundRelations]
  exact ⟨fun ⟨ground, code⟩ => ⟨ground.1, code⟩,
    fun ⟨ground, code⟩ => ⟨⟨ground, code.shape ordinal⟩, code⟩⟩

theorem rowPositionSequences_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {L r I mu : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hmu : mu ∈ M.sets) : M.rowPositionSequences L r I mu ∈ M.sets := by
  let formula : BoundedFormula 5 := BoundedFormula.rowPositionSequenceFormula 1 2 3 4 0
  let params := extend L (extend r (extend I (extend mu Fin.elim0)))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hL (Fin.cases hr (Fin.cases hI (Fin.cases hmu (fun i => Fin.elim0 i))))
  have ground := M.bounded_separation_mem separation formula params members
    (M.groundRelations_mem pairing unions powers separation hmu hI)
  have equal : ZFSet.sep (fun f => BoundedFormula.Truth formula (extend f params))
      (M.groundRelations mu I) = M.rowPositionSequences L r I mu := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_sep, rowPositionSequences, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_rowPositionSequenceFormula 1 2 3 4 0 _)
  exact equal ▸ ground

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

theorem empty_mem_rowPositionSequences {L r I mu : ZFSet.{u}}
    (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) (inhabited : L.Nonempty) :
    (∅ : ZFSet.{u}) ∈ M.rowPositionSequences L r I mu := by
  obtain ⟨D, hD⟩ := inhabited
  have length : (∅ : ZFSet.{u}) ∈ insert mu mu := by
    obtain ⟨o, rfl⟩ := (ordinalSetProperty_iff mu).1 ordinal
    rw [← ordinalCode_succ, ← ordinalCode_zero]
    exact (mem_ordinalCode_iff _ _).2 (Order.lt_succ_iff.2 zero_le)
  exact (M.mem_rowPositionSequences ordinal).2
    ⟨M.empty_mem ⟨mu, hmu⟩, ∅, length,
      ⟨ZFSet.empty_subset _, fun a ha => False.elim (ZFSet.notMem_empty a ha)⟩,
      D, hD, fun a x entry => False.elim (ZFSet.notMem_empty (ZFSet.pair a x) entry)⟩

end TransitiveGround

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCantorDiagonal
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

namespace BoundedFormula

theorem truth_injectionDiagonalFormula {n} (x p f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (injectionDiagonalFormula x p f) env ↔
      ∃ X ∈ env p, ZFSet.pair X (env x) ∈ env f ∧ env x ∉ X := by
  simp only [injectionDiagonalFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_injectionDiagonal (A f x : ZFSet.{u}) :
    x ∈ M.injectionDiagonal A f ↔
      x ∈ A ∧ ∃ X ∈ M.groundPower A, ZFSet.pair X x ∈ f ∧ x ∉ X := ZFSet.mem_sep

theorem injectionDiagonal_mem
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    M.injectionDiagonal A f ∈ M.sets := by
  let params := extend (M.groundPower A) (extend f Fin.elim0)
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases (M.groundPower_mem powers hA) (Fin.cases hf (fun i => Fin.elim0 i))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.injectionDiagonalFormula 0 1 2) params members hA
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.injectionDiagonalFormula 0 1 2) (extend x params)) A =
      M.injectionDiagonal A f := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, M.mem_injectionDiagonal, BoundedFormula.truth_injectionDiagonalFormula]
    rfl
  exact eq ▸ selected

theorem groundPower_not_embeddable_self
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : ¬ M.groundEmbeddable (M.groundPower A) A := by
  classical
  rintro ⟨f, hf, code⟩
  let D := M.injectionDiagonal A f
  have hD : D ∈ M.groundPower A := (M.mem_groundPower A D).2
    ⟨M.injectionDiagonal_mem powers separation hA hf,
      fun _ hx => (M.mem_injectionDiagonal A f _).1 hx |>.1⟩
  obtain ⟨y, entry, _⟩ := code.function.2 D hD
  have hy : y ∈ A := (ZFSet.pair_mem_prod.1 (code.function.1 entry)).2
  have outside : y ∉ D := by
    intro inside
    obtain ⟨_, X, _, image, missing⟩ := (M.mem_injectionDiagonal A f y).1 inside
    have same : X = D := code.injective X D y image entry
    exact missing (same.symm ▸ inside)
  exact outside ((M.mem_injectionDiagonal A f y).2 ⟨hy, D, hD, entry, outside⟩)

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

end PartitionPilot.Forcing.TransitiveGround

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

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {L G : Type u} [PartialOrder L] [OrderBot L] [Group G]

theorem pair_mem_rowPositionSequenceAction (a : PosetAction G L) (s : Presentation L)
    (g : G) (mu f i : ZFSet.{u}) (x : {x : L // x ≠ ⊥}) :
    ZFSet.pair i (s.encode (a.iso g x.val)) ∈ rowPositionSequenceAction a s g mu f ↔
      i ∈ mu ∧ ZFSet.pair i (s.encode x.val) ∈ f := by
  rw [rowPositionSequenceAction, pair_mem_relationCompose]
  constructor
  · rintro ⟨hi, _, y, hy, entry, moved⟩
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
    have equal := (s.nonbottom.pair_mem_graph s.nonbottom (a.nonbottom.iso g)
      y (a.nonbottom.iso g x)).1 moved
    have same := (a.nonbottom.iso g).injective equal
    exact ⟨hi, same ▸ entry⟩
  · rintro ⟨hi, entry⟩
    exact ⟨hi, s.nonbottom.encode_mem (a.nonbottom.iso g x), s.encode x.val,
      s.nonbottom.encode_mem x, entry,
      (s.nonbottom.pair_mem_graph s.nonbottom (a.nonbottom.iso g) x _).2 rfl⟩

theorem rowPositionSequenceAction_function (a : PosetAction G L) (s : Presentation L)
    (g : G) {mu delta f : ZFSet.{u}} (subset : delta ⊆ mu)
    (function : ZFSet.IsFunc delta s.nonbottom.carrier f) :
    ZFSet.IsFunc delta s.nonbottom.carrier (rowPositionSequenceAction a s g mu f) := by
  constructor
  · intro z hz
    obtain ⟨i, _, y, _, x, hx, rfl, entry, _⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨(ZFSet.pair_mem_prod.1 (function.1 entry)).1, hx⟩
  · intro i hi
    obtain ⟨x, entry, unique⟩ := function.2 i hi
    obtain ⟨x, rfl⟩ := (s.nonbottom.mem_carrier x).1
      (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    refine ⟨s.encode (a.iso g x.val),
      (pair_mem_rowPositionSequenceAction a s g mu f i x).2 ⟨subset hi, entry⟩, ?_⟩
    intro y hy
    have hyI := ((pair_mem_relationCompose _ _ _ _ _ i y).1 hy).2.1
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hyI
    let old := (a.nonbottom.iso g).symm y
    have target : a.nonbottom.iso g old = y := (a.nonbottom.iso g).apply_symm_apply y
    have original : ZFSet.pair i (s.encode old.val) ∈ f := by
      apply ((pair_mem_rowPositionSequenceAction a s g mu f i old).1 ?_).2
      simpa only [← PosetAction.nonbottom_iso_val, target, Presentation.nonbottom_encode] using hy
    have same : old = x := s.nonbottom.injective (unique _ original)
    exact congrArg s.nonbottom.encode ((congrArg (a.nonbottom.iso g) same).symm.trans target).symm

theorem rowPositionSequenceAction_code (a : PosetAction G L) (s : Presentation L)
    (g : G) {mu f : ZFSet.{u}} (ordinal : ordinalSetProperty mu)
    (code : RowPositionSequenceCode s.carrier s.conditionOrder s.nonbottom.carrier mu f) :
    RowPositionSequenceCode s.carrier s.conditionOrder s.nonbottom.carrier mu
      (rowPositionSequenceAction a s g mu f) := by
  obtain ⟨delta, length, function, d, hd, bounds⟩ := code
  have subset := (rowPositionSequence_length ordinal length).2
  obtain ⟨D, rfl⟩ := (s.mem_carrier d).1 hd
  have movedFunction := rowPositionSequenceAction_function a s g subset function
  refine ⟨delta, length, movedFunction, s.encode (a.iso g D), s.encode_mem _, ?_⟩
  intro i x entry
  obtain ⟨_, _, y, hy, original, moved⟩ := (pair_mem_relationCompose _ _ _ _ _ i x).1 entry
  obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
  obtain ⟨v, hv⟩ := (s.nonbottom.mem_graph s.nonbottom (a.nonbottom.iso g) _).1 moved
  obtain ⟨same, value⟩ := ZFSet.pair_inj.1 hv
  have equal : v = y := s.nonbottom.injective same
  have lower := (s.pair_mem_conditionOrder y.val D).1 (bounds i _ original)
  have result := (s.pair_mem_conditionOrder (a.iso g y.val) (a.iso g D)).2 ((a.iso g).monotone lower)
  rw [equal] at value
  exact value ▸ result

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowPositionSequenceAction_mem (a : PosetAction G L) (s : Presentation L) (b : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hL : s.carrier ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (graph : a.actionGraph s b ∈ M.sets) {mu f : ZFSet.{u}}
    (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) (g : G)
    (member : f ∈ M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu) :
    rowPositionSequenceAction a s g mu f ∈
      M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu := by
  obtain ⟨hf, code⟩ := (M.mem_rowPositionSequences ordinal).1 member
  have hI := M.nonbottom_carrier_mem s separation hL
  have ha := M.nonbottom_actionGraph_mem a s b separation hL hG graph
  have actionSection := M.actionGraph_section_mem a.nonbottom s.nonbottom b pairing unions powers
    separation hI ha g (M.transitive hG (b.encode_mem g))
  exact (M.mem_rowPositionSequences ordinal).2
    ⟨M.relationCompose_mem pairing unions powers separation hmu hI hI hf actionSection,
      rowPositionSequenceAction_code a s g ordinal code⟩

end TransitiveGround

end PartitionPilot.Forcing

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



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundOrdinalPartitionInjectionAssembly
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pair_mem_definableRelation {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A B x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.definableRelation φ params A B ↔
      x ∈ A ∧ y ∈ B ∧ Realize M.sets φ (extend x (extend y params)) := by
  rw [definableRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, equal, relation⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, relation⟩
  · rintro ⟨hx, hy, relation⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, relation⟩

theorem realize_definableRelationEntryFormula {n} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets (definableRelationEntryFormula φ) (extend z (extend A (extend B params))) ↔
      ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair x y ∧ Realize M.sets φ (extend x (extend y params)) := by
  simp only [definableRelationEntryFormula, realize_ex, Realize]
  constructor
  · rintro ⟨x, hx, inA, y, hy, inB, pair, relation⟩
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hy (Fin.cases hx (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    have exactPair := (BoundedFormula.truth_orderedPairFormula 2 1 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ ground).1 pair)
    exact ⟨x, inA, y, inB, exactPair, (realize_binaryApplication M.sets φ _ _ _ _).1 relation⟩
  · rintro ⟨x, hx, y, hy, pair, relation⟩
    have hxM := M.transitive hA hx
    have hyM := M.transitive hB hy
    have ground : ∀ i, (extend y (extend x (extend z (extend A (extend B params))))) i ∈ M.sets :=
      Fin.cases hyM (Fin.cases hxM (Fin.cases hz (Fin.cases hA (Fin.cases hB members))))
    exact ⟨x, hxM, hx, y, hyM, hy,
      (BoundedFormula.realize_toFormula M _ _ ground).2
        ((BoundedFormula.truth_orderedPairFormula 2 1 0 _).2 pair),
      (realize_binaryApplication M.sets φ _ _ _ _).2 relation⟩

theorem definableRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (φ : SetFormula (n + 2)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    M.definableRelation φ params A B ∈ M.sets := by
  have hProd := M.prod_mem pairing unions powers separation hA hB
  have selected := M.separation_mem separation (definableRelationEntryFormula φ)
    (extend A (extend B params)) (Fin.cases hA (Fin.cases hB members)) hProd
  have equal : ZFSet.sep (fun z => Realize M.sets (definableRelationEntryFormula φ)
      (extend z (extend A (extend B params)))) (ZFSet.prod A B) = M.definableRelation φ params A B := by
    apply ZFSet.ext
    intro z
    rw [definableRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_definableRelationEntryFormula φ params members hA hB z (M.transitive hProd hz)
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



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

theorem internalRowTupleName_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (δ : ZFSet.{u}) (positions : δ.toSet → {i : L // i ≠ ⊥}) (D : L)
    (bounded : ∀ i, (positions i).val ≤ D) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed)
      (M.internalRowTupleName s C hL δ positions) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  apply Name.indexedTuple_hs act (a.principalSupportFamily ⊥ directed) δ
    (fun i => M.internalRowName s C hL (positions i)) (a.principalFix D) ⟨D, le_rfl⟩
  · intro g fixed i
    rw [M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph]
    apply congrArg (M.internalRowName s C hL)
    exact Subtype.ext (fixed (positions i).val (bounded i))
  · intro i
    exact M.internalRowName_hs a s b C pairing unions powers separation infinite
      hL hC hG graph directed (positions i)

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

theorem binaryRowNameGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    M.binaryRowNameGraph I C one ∈ M.sets := by
  obtain ⟨W, hW, bounds⟩ := M.exists_binaryRowName_bound pairing unions powers separation collection infinite hI hC one
  let Q := M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  have hQ : Q ∈ M.sets := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  let params := extend C (extend Q (extend (SetMembers.raw one) (extend (natSetCode 1) Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hC (Fin.cases hQ
    (Fin.cases (M.transitive hQ (SetMembers.raw_mem one))
      (Fin.cases (M.natSetCode_mem separation infinite 1) (fun j => Fin.elim0 j))))
  have grounded := M.definableRelation_mem pairing unions powers separation binaryRowCodeFormula params members hI hW
  have equal : M.definableRelation binaryRowCodeFormula params I W = M.binaryRowNameGraph I C one := by
    apply ZFSet.ext
    intro z
    constructor
    · intro hz
      obtain ⟨i, hi, x, hx, rfl, formula⟩ := (ZFSet.mem_sep.1 hz).2
      have eq := (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
        hI hC one i x (M.transitive hI hi) (M.transitive hW hx)).1 formula
      exact (M.pair_mem_binaryRowNameGraph I C one i x).2 ⟨hi, eq⟩
    · intro hz
      obtain ⟨i, hi, rfl⟩ := (M.mem_binaryRowNameGraph I C one z).1 hz
      exact (M.pair_mem_definableRelation binaryRowCodeFormula params I W i _).2
        ⟨hi, bounds i hi, (M.realize_binaryRowCodeFormula pairing unions powers separation collection infinite
          hI hC one i _ (M.transitive hI hi) (M.transitive hW (bounds i hi))).2 rfl⟩
  exact equal ▸ grounded

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

theorem rowTupleFamily_function (one mu I W rows S : ZFSet.{u}) :
    FunctionGraphOn S (rowTupleFamily one mu I W rows S) := by
  have eq : ZFSet.range (fun f : S => f.val) = S := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_range]
    exact ⟨fun ⟨g, eq⟩ => eq ▸ g.property, fun hf => ⟨⟨f, hf⟩, rfl⟩⟩
  have function := familyCodeGraph_function (fun f : S => f.val)
    (fun f => rowTupleCode one mu I W rows f.val) Subtype.val_injective
  simp only [eq] at function
  exact function

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem rowTupleFamily_mem {one mu I W rows S : ZFSet.{u}}
    (hone : one ∈ M.sets) (hmu : mu ∈ M.sets) (hI : I ∈ M.sets)
    (hW : W ∈ M.sets) (hrows : rows ∈ M.sets) (hS : S ∈ M.sets) :
    rowTupleFamily one mu I W rows S ∈ M.sets :=
  (M.definable_rowTupleCode pairing unions powers separation collection).graph_mem pairing separation collection
    (extend one (extend mu (extend I (extend W (extend rows Fin.elim0)))))
    (Fin.cases hone (Fin.cases hmu (Fin.cases hI (Fin.cases hW
      (Fin.cases hrows (fun j => Fin.elim0 j)))))) hS

theorem binaryRowTupleFamily_mem (infinite : Realize M.sets infinity Fin.elim0)
    {L r I C mu : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    let rows := M.binaryRowNameGraph I C one
    rowTupleFamily (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows
      (M.rowPositionSequences L r I mu) ∈ M.sets := by
  have hrows := M.binaryRowNameGraph_mem pairing unions powers separation collection infinite hI hC one
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  exact M.rowTupleFamily_mem pairing unions powers separation collection
    (M.transitive hQ (SetMembers.raw_mem one)) hmu hI
    (M.union_mem unions (M.union_mem unions hrows)) hrows
    (M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu)

end TransitiveGround





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

theorem rowTupleTerms_function (one mu I W rows S : ZFSet.{u}) :
    ZFSet.IsFunc S (rowTupleTerms one mu I W rows S) (rowTupleFamily one mu I W rows S) :=
  functionGraphRange_function (rowTupleFamily_function one mu I W rows S)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowTupleTerms_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {one mu I W rows S : ZFSet.{u}} (hS : S ∈ M.sets)
    (family : rowTupleFamily one mu I W rows S ∈ M.sets) :
    rowTupleTerms one mu I W rows S ∈ M.sets :=
  M.functionGraphRange_mem unions separation hS family

theorem rowTupleTerms_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {one mu I W rows S K : ZFSet.{u}} (hS : S ∈ M.sets) (hK : K ∈ M.sets)
    (family : rowTupleFamily one mu I W rows S ∈ M.sets) (small : GroundBelow M S K) :
    GroundBelow M (rowTupleTerms one mu I W rows S) K :=
  small.function_image pairing unions powers separation choice hS
    (M.union_mem unions (M.union_mem unions family)) hK family
    (rowTupleFamily_function one mu I W rows S).to_isFunc

theorem binaryRowTupleTerms_mem_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L r I C mu K : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hmu : mu ∈ M.sets) (hK : K ∈ M.sets)
    (small : GroundBelow M (M.rowPositionSequences L r I mu) K)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    let S := M.rowPositionSequences L r I mu
    let rows := M.binaryRowNameGraph I C one
    let family := rowTupleFamily (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S
    let T := rowTupleTerms (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S
    family ∈ M.sets ∧ T ∈ M.sets ∧ ZFSet.IsFunc S T family ∧ GroundBelow M T K := by
  have hS := M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu
  have family := M.binaryRowTupleFamily_mem pairing unions powers separation collection infinite
    hL hr hI hC hmu one
  exact ⟨family, M.rowTupleTerms_mem unions separation hS family,
    rowTupleTerms_function _ _ _ _ _ _,
    M.rowTupleTerms_below pairing unions powers separation choice hS hK family small⟩

end TransitiveGround

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_PairFamilyEvaluation
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
variable {P : Type u} {s : Presentation P}

variable {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

theorem orderedPairNameFamily_hs {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z)
    (childrenX : ∀ τ : Name s, τ.val ∈ X → HereditarilySymmetric a s F τ)
    (childrenY : ∀ τ : Name s, τ.val ∈ Y → HereditarilySymmetric a s F τ) :
    ∀ τ : Name s, τ.val ∈ orderedPairNameFamily (s.encode ⊤) X Y →
      HereditarilySymmetric a s F τ := by
  intro τ hτ
  obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y τ.val).1 hτ
  let σ : Name s := ⟨x, validX x hx⟩
  let ν : Name s := ⟨y, validY y hy⟩
  have same : τ = Name.orderedPair ⊤ σ ν :=
    Subtype.ext (equal.trans (Name.orderedPair_code ⊤ σ ν).symm)
  rw [same]
  exact (childrenX σ hx).orderedPair (childrenY ν hy)

theorem orderedPairNameFamily_closed {X Y : ZFSet.{u}}
    (validX : ∀ z ∈ X, IsName s z) (validY : ∀ z ∈ Y, IsName s z)
    (closedX : ∀ g (τ : Name s), τ.val ∈ X → (a.act s g τ).val ∈ X)
    (closedY : ∀ g (τ : Name s), τ.val ∈ Y → (a.act s g τ).val ∈ Y) :
    ∀ g (τ : Name s), τ.val ∈ orderedPairNameFamily (s.encode ⊤) X Y →
      (a.act s g τ).val ∈ orderedPairNameFamily (s.encode ⊤) X Y := by
  intro g τ hτ
  obtain ⟨x, hx, y, hy, equal⟩ := (mem_orderedPairNameFamily _ X Y τ.val).1 hτ
  let σ : Name s := ⟨x, validX x hx⟩
  let ν : Name s := ⟨y, validY y hy⟩
  have same : τ = Name.orderedPair ⊤ σ ν :=
    Subtype.ext (equal.trans (Name.orderedPair_code ⊤ σ ν).symm)
  have acted : a.act s g τ = Name.orderedPair ⊤ (a.act s g σ) (a.act s g ν) := by
    rw [same]
    change Name.rename s (a.iso g) _ = _
    rw [Name.rename_orderedPair, (a.iso g).map_top]
    rfl
  exact (mem_orderedPairNameFamily _ X Y _).2
    ⟨(a.act s g σ).val, closedX g σ hx, (a.act s g ν).val, closedY g ν hy,
      (congrArg Subtype.val acted).trans (Name.orderedPair_code ⊤ _ _)⟩

theorem iteratedPairNameFamily_hs {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) (n : Nat) :
    ∀ τ : Name s, τ.val ∈ iteratedPairNameFamily (s.encode ⊤) T n →
      HereditarilySymmetric a s F τ := by
  induction n with
  | zero => exact children
  | succ n ih =>
    exact orderedPairNameFamily_hs a F
      (iteratedPairNameFamily_valid ⊤ valid n) valid ih children

theorem iteratedPairNameFamily_closed {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T) (n : Nat) :
    ∀ g (τ : Name s), τ.val ∈ iteratedPairNameFamily (s.encode ⊤) T n →
      (a.act s g τ).val ∈ iteratedPairNameFamily (s.encode ⊤) T n := by
  induction n with
  | zero => exact closed
  | succ n ih =>
    exact orderedPairNameFamily_closed a
      (iteratedPairNameFamily_valid ⊤ valid n) valid ih closed

theorem iteratedPairNameFamilySet_invariant {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (n : Nat) (g : G) :
    a.act s g (Name.familySet ⊤ (iteratedPairNameFamily (s.encode ⊤) T n)
      (iteratedPairNameFamily_valid ⊤ valid n)) =
        Name.familySet ⊤ (iteratedPairNameFamily (s.encode ⊤) T n)
          (iteratedPairNameFamily_valid ⊤ valid n) :=
  Name.act_familySet a _ _ (iteratedPairNameFamily_closed a valid closed n) g

theorem iteratedPairNameFamilySet_hs {T : ZFSet.{u}}
    (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) (n : Nat) :
    HereditarilySymmetric a s F
      (Name.familySet ⊤ (iteratedPairNameFamily (s.encode ⊤) T n)
        (iteratedPairNameFamily_valid ⊤ valid n)) :=
  Name.familySet_hs a F _ _ (iteratedPairNameFamily_closed a valid closed n)
    (iteratedPairNameFamily_hs a F valid children n)

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_RenamedPairNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u}

theorem exists_uniformRename_between (s : Presentation P) (t : Presentation Q)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets) :
    ∃ G ∈ M.sets,
      G = s.graph t f ∪ identityFunctionGraph
        (ZFSet.sep (fun x => x ∉ s.carrier) (s.carrier ∪ t.carrier)) ∧
      ∀ (σ : Name s) (τ : Name t), σ.val ∈ M.sets → τ.val ∈ M.sets →
        (Realize M.sets uniformRenameFormula
          (extend σ.val (extend τ.val (extend (s.carrier ∪ t.carrier) (extend G Fin.elim0)))) ↔
          Name.rename t f σ = τ) := by
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
  refine ⟨G, hG, rfl, ?_⟩
  intro σ τ hσ hτ
  have sourceCode := Name.rename_val_of_encode u es (s.encode_intoSet U subS) σ
  have targetCode := Name.rename_val_of_encode u et (t.encode_intoSet U subT) τ
  have graph : u.graph u h = G := u.graph_decodeFunction u G full
  have exactFormula := M.realize_uniformRenameFormula u pairing unions powers separation collection hU h
    (graph ▸ hG) (Name.rename u es σ) (Name.rename u et τ)
    (sourceCode ▸ hσ) (targetCode ▸ hτ)
  change Realize M.sets uniformRenameFormula
    (extend (Name.rename u es σ).val (extend (Name.rename u et τ).val
      (extend U (extend (u.graph u h) Fin.elim0)))) ↔ _ at exactFormula
  rw [sourceCode, targetCode, graph] at exactFormula
  refine exactFormula.trans ?_
  have equation : Name.rename u h (Name.rename u es σ) =
      Name.rename u et (Name.rename t f σ) := by
    rw [Name.rename_comp, Name.rename_comp]
    apply congrArg (fun k => Name.rename u k σ)
    funext p
    exact commute p
  rw [equation]
  constructor
  · intro equal
    apply Subtype.ext
    have codes := congrArg Subtype.val equal
    simpa only [Name.rename_val_of_encode u et (t.encode_intoSet U subT)] using codes
  · intro equal
    exact congrArg (Name.rename u et) equal

end PartitionPilot.Forcing.TransitiveGround

section

namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P Q : Type u} {s : Presentation P}

theorem renameFamilyGraph_function (t : Presentation Q) (f : P → Q)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) :
    ZFSet.IsFunc T (renamedFamily t f T valid) (renameFamilyGraph t f T valid) := by
  apply functionGraphRange_function
  have keys : ZFSet.range (fun x : T => x.val) = T := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_range]
    exact ⟨fun ⟨y, eq⟩ => eq ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  simpa only [keys, renameFamilyGraph] using familyCodeGraph_function (fun x : T => x.val)
    (fun x => (rename t f ⟨x.val, valid x.val x.property⟩).val) Subtype.val_injective

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P Q : Type u} (s : Presentation P) (t : Presentation Q)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem renameFamilyGraph_mem (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ x ∈ T, IsName s x) :
    Name.renameFamilyGraph t f T valid ∈ M.sets := by
  obtain ⟨G, hG, _, recognizes⟩ := M.exists_uniformRename_between s t
    pairing unions powers separation collection hs ht f hf
  let U := s.carrier ∪ t.carrier
  let params := extend t.carrier (extend U (extend G Fin.elim0))
  have hU : U ∈ M.sets := M.binary_union_mem pairing unions hs ht
  have meaning (σ : Name s) (hσ : σ.val ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets renamedNameFamilyPairFormula (extend σ.val (extend z params)) ↔
        z = ZFSet.pair σ.val (Name.rename t f σ).val := by
    rw [renamedNameFamilyPairFormula, realize_ex]
    constructor
    · rintro ⟨v, hv, named, renamed, pair⟩
      rw [realize_domainApplication, map_extend, map_empty] at named
      have validV : IsName t v :=
        (M.realize_uniformNameFormula t pairing unions powers separation collection ht v hv).1 named
      rw [realize_binaryApplication, map_extend, map_extend, map_empty] at renamed
      have eq := (recognizes σ ⟨v, validV⟩ hσ hv).1 renamed
      have pairEq := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hσ hv).1 pair
      exact (congrArg Subtype.val eq).symm ▸ pairEq
    · intro equal
      have hv := M.rename_between_mem s t pairing unions powers separation collection hs ht f hf σ hσ
      refine ⟨(Name.rename t f σ).val, hv, ?_, ?_, ?_⟩
      · rw [realize_domainApplication, map_extend, map_empty]
        exact (M.realize_uniformNameFormula t pairing unions powers separation collection ht _ hv).2
          (Name.rename t f σ).property
      · rw [realize_binaryApplication, map_extend, map_extend, map_empty]
        exact (recognizes σ (Name.rename t f σ) hσ hv).2 rfl
      · exact (M.realize_orderedPairFormula pairing 2 1 0 _ hz hσ hv).2 equal
  apply M.definable_image_mem separation collection renamedNameFamilyPairFormula params
    (Fin.cases ht (Fin.cases hU (Fin.cases hG (fun i => Fin.elim0 i)))) hT
  · intro z hz
    obtain ⟨σ, hσ, rfl⟩ := (Name.mem_renameFamilyGraph t f T valid z).1 hz
    exact M.orderedPair_mem pairing (M.transitive hT hσ)
      (M.rename_between_mem s t pairing unions powers separation collection hs ht f hf σ (M.transitive hT hσ))
  · intro z hz
    rw [Name.mem_renameFamilyGraph]
    constructor
    · rintro ⟨σ, hσ, eq⟩
      exact ⟨σ.val, hσ, (meaning σ (M.transitive hT hσ) z hz).2 eq⟩
    · rintro ⟨x, hx, rel⟩
      exact ⟨⟨x, valid x hx⟩, hx, (meaning ⟨x, valid x hx⟩ (M.transitive hT hx) z hz).1 rel⟩
  · intro x hx y hy z hz first second
    exact ((meaning ⟨x, valid x hx⟩ (M.transitive hT hx) y hy).1 first).trans
      ((meaning ⟨x, valid x hx⟩ (M.transitive hT hx) z hz).1 second).symm

theorem renamedFamily_mem (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (f : P → Q) (hf : s.graph t f ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ x ∈ T, IsName s x) :
    Name.renamedFamily t f T valid ∈ M.sets :=
  M.functionGraphRange_mem unions separation hT
    (M.renameFamilyGraph_mem s t pairing unions powers separation collection hs ht f hf T hT valid)

end PartitionPilot.Forcing.TransitiveGround

end

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} {s : Presentation P}

theorem presentationFamily_injection (t : Presentation P)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x) :
    InjectionCode T (renamedFamily t id T valid) (renameFamilyGraph t id T valid) := by
  refine ⟨renameFamilyGraph_function t id T valid, ?_⟩
  intro x y z first second
  obtain ⟨σ, _, shapeσ⟩ := (mem_renameFamilyGraph t id T valid (ZFSet.pair x z)).1 first
  obtain ⟨τ, _, shapeτ⟩ := (mem_renameFamilyGraph t id T valid (ZFSet.pair y z)).1 second
  obtain ⟨rfl, eqσ⟩ := ZFSet.pair_inj.1 shapeσ
  obtain ⟨rfl, eqτ⟩ := ZFSet.pair_inj.1 shapeτ
  have images : presentationEquiv s t σ = presentationEquiv s t τ :=
    Subtype.ext (eqσ.symm.trans eqτ)
  exact congrArg Subtype.val ((presentationEquiv s t).injective images)

theorem eval_renamedFamily (t : Presentation P) (T : ZFSet.{u})
    (valid : ∀ x ∈ T, IsName s x) (H : Set P) (x : ZFSet.{u}) :
    (∃ τ : Name t, τ.val ∈ renamedFamily t id T valid ∧ eval H τ = x) ↔
      ∃ σ : Name s, σ.val ∈ T ∧ eval H σ = x := by
  constructor
  · rintro ⟨τ, hτ, equal⟩
    obtain ⟨σ, hσ, codes⟩ := (mem_renamedFamily t id T valid τ.val).1 hτ
    have names : τ = presentationEquiv s t σ := Subtype.ext codes
    exact ⟨σ, hσ, by rw [names, eval_presentationEquiv] at equal; exact equal⟩
  · rintro ⟨σ, hσ, equal⟩
    exact ⟨presentationEquiv s t σ, (mem_renamedFamily t id T valid _).2 ⟨σ, hσ, rfl⟩,
      (eval_presentationEquiv s t H σ).trans equal⟩

variable {G : Type v} [Group G] [PartialOrder P]

theorem renamedFamily_closed (a : PosetAction G P) (t : Presentation P)
    (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x)
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T) :
    ∀ g (τ : Name t), τ.val ∈ renamedFamily t id T valid →
      (a.act t g τ).val ∈ renamedFamily t id T valid := by
  intro g τ hτ
  obtain ⟨σ, hσ, codes⟩ := (mem_renamedFamily t id T valid τ.val).1 hτ
  have names : τ = presentationEquiv s t σ := Subtype.ext codes
  rw [names, a.act_presentationEquiv]
  exact (mem_renamedFamily t id T valid _).2 ⟨a.act s g σ, closed g σ hσ, rfl⟩

theorem renamedFamily_hs (a : PosetAction G P) (t : Presentation P)
    (F : NormalSubgroupFamily G) (T : ZFSet.{u}) (valid : ∀ x ∈ T, IsName s x)
    (children : ∀ σ : Name s, σ.val ∈ T → HereditarilySymmetric a s F σ) :
    ∀ τ : Name t, τ.val ∈ renamedFamily t id T valid → HereditarilySymmetric a t F τ := by
  intro τ hτ
  obtain ⟨σ, hσ, codes⟩ := (mem_renamedFamily t id T valid τ.val).1 hτ
  have names : τ = presentationEquiv s t σ := Subtype.ext codes
  exact names.symm ▸ (children σ hσ).presentationEquiv t

end PartitionPilot.Forcing.Name

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

theorem pairEmpty_inverseGraph :
    s.pairEmpty.graph s id = relationConverse s.carrier s.pairEmpty.carrier (s.graph s.pairEmpty id) := by
  apply ZFSet.ext
  intro z
  rw [s.pairEmpty.mem_graph, mem_relationConverse]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨s.encode p, s.encode_mem p, s.pairEmpty.encode p, s.pairEmpty.encode_mem p, rfl,
      (s.pair_mem_graph s.pairEmpty id p p).2 rfl⟩
  · rintro ⟨x, hx, y, hy, rfl, entry⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨q, rfl⟩ := (s.pairEmpty.mem_carrier y).1 hy
    have eq := (s.pair_mem_graph s.pairEmpty id p q).1 entry
    change p = q at eq
    subst q
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

theorem pairEmpty_carrier_mem (hs : s.carrier ∈ M.sets) : s.pairEmpty.carrier ∈ M.sets := by
  have empty := M.empty_mem ⟨s.carrier, hs⟩
  have single : ({∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing empty empty
  exact M.prod_mem pairing unions powers separation hs single

theorem pairEmpty_forwardGraph_mem (hs : s.carrier ∈ M.sets) : s.graph s.pairEmpty id ∈ M.sets := by
  rw [s.pairEmpty_forwardGraph]
  have empty := M.empty_mem ⟨s.carrier, hs⟩
  have single : ({∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing empty empty
  exact M.pairedGraph_mem pairing unions powers separation hs hs single
    (M.identityFunctionGraph_mem pairing unions powers separation hs)
    (M.constantFamilyGraph_mem pairing unions powers separation hs empty)

theorem pairEmpty_inverseGraph_mem (hs : s.carrier ∈ M.sets) : s.pairEmpty.graph s id ∈ M.sets := by
  rw [s.pairEmpty_inverseGraph]
  exact M.relationConverse_mem pairing unions powers separation hs
    (M.pairEmpty_carrier_mem pairing unions powers separation s hs)
    (M.pairEmpty_forwardGraph_mem pairing unions powers separation s hs)

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
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P]
variable {G : Type v} [Group G] (a : PosetAction G P) (s : Presentation P)
variable (F : NormalSubgroupFamily G)

theorem pairEmpty_nameFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (T : ZFSet.{u}) (hT : T ∈ M.sets)
    (valid : ∀ x ∈ T, IsName s x)
    (closed : ∀ g (σ : Name s), σ.val ∈ T → (a.act s g σ).val ∈ T)
    (children : ∀ σ : Name s, σ.val ∈ T → HereditarilySymmetric a s F σ) :
    let lifted := Name.renamedFamily s.pairEmpty id T valid
    let graph := Name.renameFamilyGraph s.pairEmpty id T valid
    lifted ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
      (∀ x ∈ lifted, IsName s.pairEmpty x) ∧
      (∀ σ : Name s.pairEmpty, σ.val ∈ lifted → HereditarilySymmetric a s.pairEmpty F σ) ∧
      (∀ g (σ : Name s.pairEmpty), σ.val ∈ lifted → (a.act s.pairEmpty g σ).val ∈ lifted) ∧
      ∀ (H : Set P) (x : ZFSet.{u}),
        (∃ τ : Name s.pairEmpty, τ.val ∈ lifted ∧ Name.eval H τ = x) ↔
          ∃ σ : Name s, σ.val ∈ T ∧ Name.eval H σ = x := by
  have target := M.pairEmpty_carrier_mem pairing unions powers separation s hs
  have map := M.pairEmpty_forwardGraph_mem pairing unions powers separation s hs
  exact ⟨M.renamedFamily_mem s s.pairEmpty pairing unions powers separation collection hs target id map T hT valid,
    M.renameFamilyGraph_mem s s.pairEmpty pairing unions powers separation collection hs target id map T hT valid,
    Name.presentationFamily_injection s.pairEmpty T valid,
    Name.renamedFamily_valid s.pairEmpty id T valid,
    Name.renamedFamily_hs a s.pairEmpty F T valid children,
    Name.renamedFamily_closed a s.pairEmpty T valid closed,
    Name.eval_renamedFamily s.pairEmpty T valid⟩

end PartitionPilot.Forcing.TransitiveGround

section

namespace PartitionPilot.Forcing.Name
open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem renamedFamily_inverse (t : Presentation P) (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) :
    renamedFamily s id (renamedFamily t id T valid) (renamedFamily_valid t id T valid) = T := by
  apply ZFSet.ext
  intro z
  rw [mem_renamedFamily]
  constructor
  · rintro ⟨τ, hτ, equal⟩
    obtain ⟨σ, hσ, codes⟩ := (mem_renamedFamily t id T valid τ.val).1 hτ
    have same : τ = rename t id σ := Subtype.ext codes
    rw [same, rename_comp, Function.id_comp, rename_id] at equal
    exact equal.symm ▸ hσ
  · intro hz
    let σ : Name s := ⟨z, valid z hz⟩
    refine ⟨rename t id σ, (mem_renamedFamily t id T valid _).2 ⟨σ, hz, rfl⟩, ?_⟩
    rw [rename_comp, Function.id_comp, rename_id]

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}

theorem renamedFamily_below (s t : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (forward : s.graph t id ∈ M.sets) (backward : t.graph s id ∈ M.sets)
    {T K : ZFSet.{u}} (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (small : GroundBelow M T K) :
    GroundBelow M (Name.renamedFamily t id T valid) K := by
  have hLifted := M.renamedFamily_mem s t pairing unions powers separation collection hs ht id forward T hT valid
  have validLifted := Name.renamedFamily_valid t id T valid
  have hInverse := M.renameFamilyGraph_mem t s pairing unions powers separation collection ht hs id backward
    (Name.renamedFamily t id T valid) hLifted validLifted
  have inverse := Name.presentationFamily_injection s (Name.renamedFamily t id T valid) validLifted
  rw [Name.renamedFamily_inverse] at inverse
  exact small.of_embeddable pairing unions powers separation hLifted hT hK ⟨_, hInverse, inverse⟩

theorem pairEmpty_renamedFamily_below (s : Presentation P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) {T K : ZFSet.{u}} (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (valid : ∀ z ∈ T, IsName s z) (small : GroundBelow M T K) :
    GroundBelow M (Name.renamedFamily s.pairEmpty id T valid) K :=
  M.renamedFamily_below s s.pairEmpty pairing unions powers separation collection hs
    (M.pairEmpty_carrier_mem pairing unions powers separation s hs)
    (M.pairEmpty_forwardGraph_mem pairing unions powers separation s hs)
    (M.pairEmpty_inverseGraph_mem pairing unions powers separation s hs) hT hK valid small

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStandardInaccessible
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)

theorem groundOmegaOne_subset_of_not_countable {α : ZFSet.{u}}
    (ordinal : ordinalSetProperty α) (uncountable : ¬ M.groundEmbeddable α ZFSet.omega) :
    M.groundOmegaOne pairing unions powers separation collection infinite ⊆ α := by
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff α).1 ordinal
  obtain ⟨c, eqC⟩ := (ordinalSetProperty_iff _).1 spec.2.1
  by_cases lower : a < c
  · have inside : α ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
      rw [eqA, eqC, mem_ordinalCode_iff]
      exact lower
    exact False.elim (uncountable ((spec.2.2.1 α).1 inside).2.2)
  · rw [eqC, eqA, ordinalCode_subset_iff]
    exact le_of_not_gt lower

end TransitiveGround

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (hK : K ∈ M.sets)
include conditions hK

theorem groundOmegaOne_bound :
    ∃ α ∈ K, M.groundOmegaOne pairing unions powers separation collection infinite ⊆ α := by
  have hOmega := M.omega_mem separation infinite
  have hPower := M.groundPower_mem powers hOmega
  obtain ⟨α, hα, f, hf, injection⟩ := conditions.2.2.2 ZFSet.omega conditions.2.1
  have hAlpha := M.transitive hK hα
  have uncountable : ¬ M.groundEmbeddable α ZFSet.omega := by
    rintro ⟨g, hg, countable⟩
    apply M.groundPower_not_embeddable_self powers separation hOmega
    exact ⟨relationCompose (M.groundPower ZFSet.omega) α ZFSet.omega f g,
      M.relationCompose_mem pairing unions powers separation hPower hAlpha hOmega hf hg,
      injection.compose countable⟩
  exact ⟨α, hα, M.groundOmegaOne_subset_of_not_countable pairing unions powers separation
    collection infinite (ordinalSetProperty_member conditions.1 hα) uncountable⟩

theorem groundOmegaOne_below :
    GroundBelow M (M.groundOmegaOne pairing unions powers separation collection infinite) K := by
  obtain ⟨α, hα, subset⟩ := conditions.groundOmegaOne_bound pairing unions powers separation
    collection infinite hK
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  exact ⟨α, hα, identityFunctionGraph C,
    M.identityFunctionGraph_mem pairing unions powers separation
      (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1,
    (identityFunctionGraph_injection C).retarget subset⟩

theorem groundOmegaOne_mem :
    M.groundOmegaOne pairing unions powers separation collection infinite ∈ K := by
  obtain ⟨α, hα, subset⟩ := conditions.groundOmegaOne_bound pairing unions powers separation
    collection infinite hK
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  obtain ⟨c, eqC⟩ := (ordinalSetProperty_iff _).1 spec.2.1
  obtain ⟨a, eqA⟩ := (ordinalSetProperty_iff α).1 (ordinalSetProperty_member conditions.1 hα)
  have bound : c ≤ a := by
    rw [eqC, eqA] at subset
    exact (ordinalCode_subset_iff c a).1 subset
  rcases lt_or_eq_of_le bound with lower | same
  · apply conditions.1.1 α hα
    rw [eqC, eqA, mem_ordinalCode_iff]
    exact lower
  · rw [eqC, same, ← eqA]
    exact hα

end GroundInaccessibleConditions




end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBelowRelationSpaces
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {A B K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation

theorem relations (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) :
    GroundBelow M (M.groundRelations A B) K :=
  strong.power_closed pairing unions powers separation
    (M.prod_mem pairing unions powers separation hA hB) hK
    (product pairing unions powers separation hA hB hK ordinal strong first second)

theorem partialFunctions (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) :
    GroundBelow M (M.partialFunctions A B) K :=
  (relations pairing unions powers separation hA hB hK ordinal strong first second).restrict
    separation (M.partialFunctions_mem pairing unions powers separation hA hB) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

end PartitionPilot.Forcing.GroundBelow

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ForcingHistoryOutputFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_stageOneCandidateFormula {n : Nat} (rows I T N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (stageOneCandidateFormula rows I T N z) env ↔
      env z ∈ ZFSet.prod (env rows)
        (M.groundSmallSubsets (stageOneAssignments (env I) (env T)) (env N)) := by
  rw [stageOneCandidateFormula, realize_exBlock]
  have actual (fields : Fin 2 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets (.conj
        (BoundedFormula.orderedPairFormula (suffixIndex n 2 z) (prefixIndex n 2 0)
          (prefixIndex n 2 1)).toFormula
        (.conj (.mem (prefixIndex n 2 0) (suffixIndex n 2 rows))
          (.conj (BoundedFormula.stageOneAssignmentsSubsetFormula (prefixIndex n 2 1)
            (suffixIndex n 2 I) (suffixIndex n 2 T)).toFormula
            (hasInjectionFormula (prefixIndex n 2 1) (suffixIndex n 2 N)))))
        (extendMany 2 fields env) ↔
      env z = ZFSet.pair (fields 0) (fields 1) ∧ fields 0 ∈ env rows ∧
        fields 1 ⊆ stageOneAssignments (env I) (env T) ∧
        M.groundEmbeddable (fields 1) (env N) := by
    have bounds := extendMany_members 2 fields env ground members
    rw [Realize, BoundedFormula.realize_toFormula M _ _ bounds,
      BoundedFormula.truth_orderedPairFormula]
    apply and_congr Iff.rfl
    change (_ ∧ Realize M.sets _ _) ↔ _
    apply and_congr Iff.rfl
    rw [Realize, BoundedFormula.realize_toFormula M _ _ bounds,
      BoundedFormula.truth_stageOneAssignmentsSubsetFormula, M.realize_hasInjectionFormula _ _ _ bounds]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨fields, ground, body⟩
    obtain ⟨equal, row, subset, small⟩ := (actual fields ground).1 body
    rw [equal, ZFSet.pair_mem_prod, M.mem_groundSmallSubsets]
    exact ⟨row, ground 1, subset, small⟩
  · intro member
    obtain ⟨row, hrow, A, hA, equal⟩ := ZFSet.mem_prod.1 member
    obtain ⟨hA, subset, small⟩ := (M.mem_groundSmallSubsets _ _ _).1 hA
    have ground : ∀ j : Fin 2, (![row, A] : Fin 2 → ZFSet.{u}) j ∈ M.sets :=
      Fin.cases (M.transitive (members rows) hrow) (Fin.cases hA (fun j => Fin.elim0 j))
    exact ⟨![row, A], ground, (actual ![row, A] ground).2 ⟨equal, hrow, subset, small⟩⟩

theorem realize_stageOneCandidateFormula_omega {n : Nat} (rows I T N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (naturals : env N = ZFSet.omega) :
    Realize M.sets (stageOneCandidateFormula rows I T N z) env ↔
      env z ∈ M.stageOneCandidateBound (env rows) (env I) (env T) := by
  rw [M.realize_stageOneCandidateFormula rows I T N z env members, naturals]
  rfl

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_forcingHistoryConditionsOutputFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets)
    {n : Nat} (output rows I T stages history levels N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (naturals : env N = ZFSet.omega) :
    Realize M.sets (forcingHistoryConditionsOutputFormula output rows I T stages history levels N) env ↔
      env output = M.forcingHistoryConditions (env rows) (env I) (env T)
        (env stages) (env history) (env levels) := by
  apply M.realize_exactSetFormula output _ env (members output)
  · intro z member
    have candidate := ((M.mem_forcingHistoryConditions _ _ _ _ _ _ _).1 member).1
    obtain ⟨row, hrow, A, ground, _, _, equal⟩ :=
      (M.mem_stageOneCandidateBound _ _ _ _).1 candidate
    exact equal ▸ M.orderedPair_mem pairing (M.transitive (members rows) hrow) ground
  · intro z ground
    rw [Realize, M.mem_forcingHistoryConditions]
    exact and_congr
      (M.realize_stageOneCandidateFormula_omega rows.succ I.succ T.succ N.succ 0
        (extend z env) (Fin.cases ground members) naturals)
      (M.realize_forcingHistoryConditionFormula pairing separation stages.succ history.succ levels.succ 0
        (extend z env) (Fin.cases ground members))

end TransitiveGround
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

variable [Group G] (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem binaryRowTupleTerms_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    ∀ z ∈ rowTupleTerms (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S,
      ∃ τ : Name c, τ.val = z ∧ HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) τ := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  dsimp only
  intro z hz
  obtain ⟨f, hf, rfl⟩ := (mem_rowTupleTerms _ _ _ _ _ _ z).1 hz
  obtain ⟨_, δ, _, _, subset, function, positions, D, values, bounded⟩ :=
    M.rowPositionSequence_decode s hL hmu ordinal hf
  refine ⟨M.internalRowTupleName s C hL δ positions, ?_, ?_⟩
  · exact (M.internalRowTupleCode_eq s C hL function subset positions values).symm
  · exact M.internalRowTupleName_hs a s b C pairing unions powers separation infinite
      hL hC hG graph directed δ positions D bounded

end

section
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

theorem binaryRowTupleTerms_action {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu s.nonbottom.carrier
      (⋃₀ ⋃₀ rows) rows S
    ∀ (g : G) (τ : Name c), τ.val ∈ T → (act.act c g τ).val ∈ T := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  dsimp only
  intro g τ member
  obtain ⟨f, hf, equal⟩ := (mem_rowTupleTerms _ _ _ _ _ _ τ.val).1 member
  obtain ⟨_, δ, _, _, subset, function, positions, _, values, _⟩ :=
    M.rowPositionSequence_decode s hL hmu ordinal hf
  have original : ZFSet.IsFunc δ s.nonbottom.carrier f := by
    refine ⟨?_, function.to_isFunc.2⟩
    intro z hz
    obtain ⟨i, hi, y, rfl⟩ := function.shape z hz
    have value := (function.value_eq_of_entry ⟨i, hi⟩ hz).symm.trans (values ⟨i, hi⟩)
    exact ZFSet.pair_mem_prod.2 ⟨hi, value.symm ▸ s.nonbottom.encode_mem (positions ⟨i, hi⟩)⟩
  let moved := rowPositionSequenceAction a s g mu f
  have hmoved := M.rowPositionSequenceAction_mem a s b pairing unions powers separation
    hL hG graph hmu ordinal g hf
  let movedFunction : FunctionGraphOn δ moved :=
    ⟨s.nonbottom.carrier, rowPositionSequenceAction_function a s g subset original⟩
  have movedValues (i : δ.toSet) :
      movedFunction.value i = s.encode (a.nonbottom.iso g (positions i)).val := by
    apply movedFunction.value_eq_of_entry
    apply (pair_mem_rowPositionSequenceAction a s g mu f i.val (positions i)).2
    refine ⟨subset i.property, ?_⟩
    rw [← values i]
    exact function.value_entry i
  have actual : τ = M.internalRowTupleName s C hL δ positions :=
    Subtype.ext (equal.trans (M.internalRowTupleCode_eq s C hL function subset positions values))
  rw [actual, M.internalRowTupleName_action a s b C pairing unions powers separation infinite
    hL hC hG graph]
  apply (mem_rowTupleTerms _ _ _ _ _ _ _).2
  exact ⟨moved, hmoved,
    (M.internalRowTupleCode_eq s C hL movedFunction subset
      (fun i => a.nonbottom.iso g (positions i)) movedValues).symm⟩

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

include collection order
theorem binaryRowTermSetName_exists (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    T ∈ M.sets ∧ ∃ τ : Name c, τ.val ∈ M.sets ∧ τ.val = ZFSet.prod T {c.encode ⊤} ∧
      HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) τ ∧
      (∀ g : G, act.act c g τ = τ) ∧
      ∀ (H : Set (SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))), ⊤ ∈ H →
        ∀ x, x ∈ Name.eval H τ ↔ ∃ σ : Name c, σ.val ∈ T ∧ Name.eval H σ = x := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  have hI := M.nonbottom_carrier_mem s separation hL
  have hS : S ∈ M.sets := M.rowPositionSequences_mem pairing unions powers separation hL order hI hmu
  have hfamily := M.binaryRowTupleFamily_mem pairing unions powers separation collection infinite hL order hI hC hmu ⊤
  have hT : T ∈ M.sets := M.rowTupleTerms_mem unions separation hS hfamily
  have each := M.binaryRowTupleTerms_hs a s b C pairing unions powers separation infinite
    hL hC hG graph directed hmu ordinal
  have valid (z : ZFSet.{u}) (hz : z ∈ T) : IsName c z := by
    obtain ⟨σ, eq, _⟩ := each z hz
    exact eq ▸ σ.property
  have children (σ : Name c) (hσ : σ.val ∈ T) :
      HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) σ := by
    obtain ⟨ν, eq, hs⟩ := each σ.val hσ
    have same : ν = σ := Subtype.ext eq
    exact same ▸ hs
  have closed := M.binaryRowTupleTerms_action a s b C pairing unions powers separation infinite
    hL hC hG graph hmu ordinal
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  refine ⟨hT, Name.familySet ⊤ T valid,
    M.familySet_mem c ⊤ pairing unions powers separation hT (M.transitive hQ (c.encode_mem ⊤)) valid,
    Name.familySet_code ⊤ T valid,
    Name.familySet_hs act (a.principalSupportFamily ⊥ directed) T valid closed children,
    Name.act_familySet act T valid closed, ?_⟩
  intro H hone x
  exact Name.mem_eval_familySet H ⊤ hone T valid x

end

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainFinalRowTerms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0)
variable (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

namespace GroundStandardInaccessible
variable {K : ZFSet.{u}} (standard : GroundStandardInaccessible M K)
include standard

theorem groundOmegaOne_mem (hK : K ∈ M.sets) :
    M.groundOmegaOne pairing unions powers separation collection infinite ∈ K :=
  (standard.to_conditions pairing unions powers separation hK).groundOmegaOne_mem
    pairing unions powers separation collection infinite hK

end GroundStandardInaccessible
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem rowPositionSequences_below {L r I mu K : ZFSet.{u}}
    (hL : L ∈ M.sets) (hr : r ∈ M.sets) (hI : I ∈ M.sets)
    (hmu : mu ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (muSmall : GroundBelow M mu K) (positionsSmall : GroundBelow M I K) :
    GroundBelow M (M.rowPositionSequences L r I mu) K :=
  (GroundBelow.relations pairing unions powers separation hmu hI hK ordinal strong
    muSmall positionsSmall).restrict separation
    (M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

theorem exists_infiniteGroundCardinal_bound
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {I K : ZFSet.{u}} (hI : I ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K) (small : GroundBelow M I K) :
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable I mu := by
  let Omega := M.groundOmegaOne pairing unions powers separation collection infinite
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have hOmega : Omega ∈ M.sets := spec.1
  have omegaBelow : GroundBelow M Omega K := GroundBelow.of_member pairing unions powers
    separation hK (standard.groundOmegaOne_mem pairing unions powers separation collection infinite hK)
  obtain ⟨gamma, hgammaK, first, second⟩ := small.common_bound omegaBelow standard.1.1
  have hgamma := M.transitive hK hgammaK
  obtain ⟨mu, hmu, cardinal, bound, f, hf, forward, _, _⟩ :=
    M.exists_groundCardinalRepresentative pairing unions powers separation hgamma
      (ordinalSetProperty_member standard.1.1 hgammaK)
  have hmuK : mu ∈ K := bound.elim (fun equal => equal ▸ hgammaK)
    (fun member => standard.1.1.1 gamma hgammaK mu member)
  obtain ⟨g, hg, intoGamma⟩ := first
  have positions : M.groundEmbeddable I mu :=
    ⟨relationCompose I gamma mu g f,
      M.relationCompose_mem pairing unions powers separation hI hgamma hmu hg hf,
      intoGamma.compose forward⟩
  obtain ⟨e, he, omegaIntoGamma⟩ := second
  have omegaIntoMu : M.groundEmbeddable Omega mu :=
    ⟨relationCompose Omega gamma mu e f,
      M.relationCompose_mem pairing unions powers separation hOmega hgamma hmu he hf,
      omegaIntoGamma.compose forward⟩
  have uncountable : ¬ M.groundEmbeddable mu ZFSet.omega := by
    rintro ⟨b, hb, intoOmega⟩
    obtain ⟨a, ha, intoMu⟩ := omegaIntoMu
    exact spec.2.2.2 ⟨relationCompose Omega mu ZFSet.omega a b,
      M.relationCompose_mem pairing unions powers separation hOmega hmu
        (M.omega_mem separation infinite) ha hb, intoMu.compose intoOmega⟩
  have infiniteBound : ZFSet.omega ⊆ mu := by
    obtain ⟨o, equal⟩ := (ordinalSetProperty_iff mu).1 cardinal.1
    by_cases lower : Ordinal.omega0 ≤ o
    · rw [equal, ← ordinalCode_omega, ordinalCode_subset_iff]
      exact lower
    · have subset : mu ⊆ ZFSet.omega := by
        rw [equal, ← ordinalCode_omega, ordinalCode_subset_iff]
        exact le_of_lt (lt_of_not_ge lower)
      exact False.elim (uncountable ⟨identityFunctionGraph mu,
        M.identityFunctionGraph_mem pairing unions powers separation hmu,
        (identityFunctionGraph_injection mu).retarget subset⟩)
  exact ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions⟩

theorem exists_smallRowPositionSequences
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {L r I K : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K) (small : GroundBelow M I K) :
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable I mu ∧ M.rowPositionSequences L r I mu ∈ M.sets ∧
      GroundBelow M (M.rowPositionSequences L r I mu) K := by
  obtain ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions⟩ :=
    M.exists_infiniteGroundCardinal_bound pairing unions powers separation collection infinite
      hI hK standard small
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions,
    M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu,
    M.rowPositionSequences_below pairing unions powers separation hL hr hI hmu hK
      conditions.1 conditions.2.2.2
      (GroundBelow.of_member pairing unions powers separation hK hmuK) small⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem finalGeometry_below (i₀ : I) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    GroundBelow M (run.finalGeometry i₀).carrier K ∧ GroundBelow M (run.finalGeometry i₀).actors K :=
  ⟨run.limitPoints_below choice hK standard indices, run.limitActors_below choice hK standard indices⟩

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

namespace GroundMainFinalGeometry
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem exists_rowPositionSequences
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (small : GroundBelow M geometry.carrier K) :
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let positions := (SetMembers.presentation geometry.carrier).nonbottom.carrier
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable positions mu ∧
      M.rowPositionSequences geometry.carrier geometry.order positions mu ∈ M.sets ∧
      GroundBelow M (M.rowPositionSequences geometry.carrier geometry.order positions mu) K ∧
      (∅ : ZFSet.{u}) ∈ M.rowPositionSequences geometry.carrier geometry.order positions mu := by
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  have hPositions := M.nonbottom_carrier_mem s separation geometry.carrier_ground
  have positionsSmall : GroundBelow M s.nonbottom.carrier K :=
    small.restrict separation hPositions hK (fun z member => (s.mem_nonbottom_carrier z).1 member |>.1)
  obtain ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions, ground, below⟩ :=
    M.exists_smallRowPositionSequences pairing unions powers separation collection infinite
      geometry.carrier_ground geometry.order_ground hPositions hK standard positionsSmall
  exact ⟨mu, hmu, hmuK, cardinal, infiniteBound, positions, ground, below,
    M.empty_mem_rowPositionSequences hmu cardinal.1 ⟨geometry.bottom, geometry.bottom_mem⟩⟩

end GroundMainFinalGeometry

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_finalRowPositionSequences (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let positions := (SetMembers.presentation geometry.carrier).nonbottom.carrier
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable positions mu ∧
      M.rowPositionSequences geometry.carrier geometry.order positions mu ∈ M.sets ∧
      GroundBelow M (M.rowPositionSequences geometry.carrier geometry.order positions mu) K ∧
      (∅ : ZFSet.{u}) ∈ M.rowPositionSequences geometry.carrier geometry.order positions mu :=
  (run.finalGeometry i₀).exists_rowPositionSequences pairing unions powers separation
    collection infinite hK standard (run.finalGeometry_below i₀ choice hK standard indices).1

end GroundMainPrefix
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundInvariantNamePowers
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

theorem orderedPairNameFamily_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {one X Y K : ZFSet.{u}}
    (hone : one ∈ M.sets) (hX : X ∈ M.sets) (hY : Y ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K)
    (smallX : GroundBelow M X K) (smallY : GroundBelow M Y K) :
    GroundBelow M (orderedPairNameFamily one X Y) K := by
  obtain ⟨ordinal, omega, regular, strong⟩ := standard.to_conditions pairing unions powers separation hK
  have hSingleton : ({one} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hone hone
  have singletonSmall := GroundBelow.singleton pairing unions powers separation infinite hK omega hone
  have hUnion := M.binary_union_mem pairing unions hX hY
  have unionSmall := GroundBelow.binary_union pairing unions powers separation infinite choice
    hX hY hK omega ordinal regular strong smallX smallY
  have hFirst := M.prod_mem pairing unions powers separation hUnion hSingleton
  have firstSmall := GroundBelow.product pairing unions powers separation hUnion hSingleton hK
    ordinal strong unionSmall singletonSmall
  have hPower := M.groundPower_mem powers hFirst
  have powerSmall := strong.power_closed pairing unions powers separation hFirst hK firstSmall
  have hSecond := M.prod_mem pairing unions powers separation hPower hSingleton
  have secondSmall := GroundBelow.product pairing unions powers separation hPower hSingleton hK
    ordinal strong powerSmall singletonSmall
  have boundSmall := strong.power_closed pairing unions powers separation hSecond hK secondSmall
  exact boundSmall.restrict separation
    (M.orderedPairNameFamily_mem pairing unions powers separation hone hX hY) hK
    (M.orderedPairNameFamily_subset_bound pairing hone hX hY)

theorem iteratedPairNameFamily_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {one T K : ZFSet.{u}}
    (hone : one ∈ M.sets) (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (standard : GroundStandardInaccessible M K) (small : GroundBelow M T K) (n : Nat) :
    GroundBelow M (iteratedPairNameFamily one T n) K := by
  induction n with
  | zero => exact small
  | succ n ih =>
      exact M.orderedPairNameFamily_below pairing unions powers separation infinite choice hone
        (M.iteratedPairNameFamily_mem pairing unions powers separation hone hT n) hT hK standard ih small

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable {G : Type v} [Group G] (a : PosetAction G P) (s : Presentation P)
variable (F : NormalSubgroupFamily G)

theorem invariantNamePowers
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {T K : ZFSet.{u}} (hone : s.encode ⊤ ∈ M.sets)
    (hT : T ∈ M.sets) (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (small : GroundBelow M T K) (valid : ∀ z ∈ T, IsName s z)
    (closed : ∀ g (τ : Name s), τ.val ∈ T → (a.act s g τ).val ∈ T)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) :
    ∀ n : Nat, let terms := iteratedPairNameFamily (s.encode ⊤) T n
      terms ∈ M.sets ∧ GroundBelow M terms K ∧
      (∀ z ∈ terms, IsName s z) ∧
      (∀ σ : Name s, σ.val ∈ terms → HereditarilySymmetric a s F σ) ∧
      ∃ τ : Name s, τ.val ∈ M.sets ∧ τ.val = ZFSet.prod terms {s.encode ⊤} ∧
        HereditarilySymmetric a s F τ ∧ (∀ g, a.act s g τ = τ) ∧
        ∀ H : Set P, ⊤ ∈ H → ∀ x,
          x ∈ Name.eval H τ ↔ ∃ σ : Name s, σ.val ∈ terms ∧ Name.eval H σ = x := by
  intro n
  let terms := iteratedPairNameFamily (s.encode ⊤) T n
  have hTerms := M.iteratedPairNameFamily_mem pairing unions powers separation hone hT n
  have typed := iteratedPairNameFamily_valid (s := s) ⊤ valid n
  refine ⟨hTerms, M.iteratedPairNameFamily_below pairing unions powers separation infinite choice
    hone hT hK standard small n, typed, iteratedPairNameFamily_hs a F valid children n,
    Name.familySet ⊤ terms typed,
    M.familySet_mem s ⊤ pairing unions powers separation hTerms hone typed,
    Name.familySet_code ⊤ terms typed,
    iteratedPairNameFamilySet_hs a F valid closed children n,
    iteratedPairNameFamilySet_invariant a valid closed n, ?_⟩
  intro H top x
  exact Name.mem_eval_familySet H ⊤ top terms typed x

end PartitionPilot.Forcing.TransitiveGround

end

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

theorem exists_rowTermSystem
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, geometry.carrier_ground⟩
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let supports := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
      let family := rowTupleFamily (c.encode ⊤) mu s.nonbottom.carrier
        (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier
        (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
      S ∈ M.sets ∧ GroundBelow M S K ∧ (∅ : ZFSet.{u}) ∈ S ∧
      family ∈ M.sets ∧ ZFSet.IsFunc S T family ∧ T ∈ M.sets ∧ GroundBelow M T K ∧
      ∀ n : Nat, let terms := iteratedPairNameFamily (c.encode ⊤) T n
        terms ∈ M.sets ∧ GroundBelow M terms K ∧
        (∀ z ∈ terms, IsName c z) ∧
        (∀ σ : Name c, σ.val ∈ terms → HereditarilySymmetric act c supports σ) ∧
        ∃ τ : Name c, τ.val ∈ M.sets ∧ τ.val = ZFSet.prod terms {c.encode ⊤} ∧
          HereditarilySymmetric act c supports τ ∧ (∀ g, act.act c g τ = τ) ∧
          ∀ H : Set (SetMembers (M.smallPartialFunctions
            (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)), ⊤ ∈ H → ∀ x,
            x ∈ Name.eval H τ ↔ ∃ σ : Name c, σ.val ∈ terms ∧ Name.eval H σ = x := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  let supports := a.principalSupportFamily (⊥ : SetMembers geometry.carrier) directed
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, hS, smallS, empty⟩ :=
    run.exists_finalRowPositionSequences i₀ collection infinite choice hK standard indices
  have sequenceEqual := congrArg
    (fun r => M.rowPositionSequences s.carrier r s.nonbottom.carrier mu) geometry.decoded_order_eq
  have groundS := (congrArg (fun A => A ∈ M.sets) sequenceEqual).mpr hS
  have belowS := (congrArg (fun A => GroundBelow M A K) sequenceEqual).mpr smallS
  have emptyS := (congrArg (fun A => (∅ : ZFSet.{u}) ∈ A) sequenceEqual).mpr empty
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, groundS, belowS, emptyS, ?_⟩
  have hI := M.nonbottom_carrier_mem s separation geometry.carrier_ground
  obtain ⟨family, _, function, smallT⟩ :=
    M.binaryRowTupleTerms_mem_below pairing unions powers separation collection infinite choice
      geometry.carrier_ground order hI hColumns hmu hK belowS ⊤
  have base := M.binaryRowTermSetName_exists a s b columns pairing unions powers separation collection infinite
    geometry.carrier_ground hColumns geometry.actors_ground action order directed hmu cardinal.1
  have hT := base.1
  have each := M.binaryRowTupleTerms_hs a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action directed hmu cardinal.1
  have closed := M.binaryRowTupleTerms_action a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action hmu cardinal.1
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hColumns) (M.natSetCode_mem separation infinite 2)
  refine ⟨family, function, hT, smallT, ?_⟩
  apply M.invariantNamePowers act c supports pairing unions powers separation infinite choice
    (M.transitive hQ (c.encode_mem ⊤)) hT hK standard smallT
  · intro z hz
    obtain ⟨τ, equal, _⟩ := each z hz
    exact equal ▸ τ.property
  · exact closed
  · intro σ hσ
    obtain ⟨τ, equal, hs⟩ := each σ.val hσ
    have same : τ = σ := Subtype.ext equal
    exact same ▸ hs

end GroundMainPrefix.FinalFulfillment

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RefinementDataHistoryEntryFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_refinementDataHistoryLevelsEntryFormula {n : Nat}
    (stages history T z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (refinementDataHistoryLevelsEntryFormula stages history T z) env ↔
      env z ∈ refinementDataHistoryLevels (env stages) (env history) (env T) := by
  simp only [refinementDataHistoryLevelsEntryFormula, truth_exPairFields, Truth,
    truth_refinementDataHistoryIndicesEntryFormula, truth_tupleFieldFormula]
  change (∃ assignment xi, env z = ZFSet.pair assignment xi ∧
    ∃ i tail, assignment = ZFSet.pair i tail ∧ ∃ u w, tail = ZFSet.pair u w ∧
      i ∈ refinementDataHistoryIndices (env stages) (env history) ∧ u ∈ env T ∧ w ∈ env T ∧
        xi ∈ env stages ∧ ∃ fields : Fin 6 → ZFSet.{u},
          i = nonemptyTupleCode 5 fields ∧ xi = fields 0) ↔ _
  constructor
  · rintro ⟨assignment, xi, equal, i, tail, pair, u, w, tailEq, hi, hu, hw, hxi, fields⟩
    rw [equal]
    apply (pair_mem_refinementDataHistoryLevels _ _ _ _ _).2
    exact ⟨i, hi, u, hu, w, hw, pair.trans (congrArg (ZFSet.pair i) tailEq), hxi, fields⟩
  · intro member
    have raw := member
    unfold refinementDataHistoryLevels refinementHistoryAssignmentLevels assignmentIndexLevels relationCompose at raw
    have shape := (ZFSet.mem_sep.1 raw).1
    obtain ⟨assignment, _, xi, _, equal⟩ := ZFSet.mem_prod.1 shape
    rw [equal] at member
    obtain ⟨i, hi, u, hu, w, hw, pair, hxi, fields⟩ :=
      (pair_mem_refinementDataHistoryLevels _ _ _ _ _).1 member
    exact ⟨assignment, xi, equal, i, ZFSet.pair u w, pair, u, w, rfl, hi, hu, hw, hxi, fields⟩

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundDefinableRefinementHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_refinementDataHistoryLevelsSetFormula {n : Nat}
    (output stages history T : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (refinementDataHistoryLevelsSetFormula output stages history T) env ↔
      env output = refinementDataHistoryLevels (env stages) (env history) (env T) := by
  have ground := M.refinementDataHistoryLevels_mem pairing unions powers separation
    (members stages) (members history) (members T)
  apply M.realize_exactSetFormula output _ env (members output)
    (fun _ member => M.transitive ground member)
  intro z hz
  exact (BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)).trans
    (BoundedFormula.truth_refinementDataHistoryLevelsEntryFormula stages.succ history.succ T.succ 0 _)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RefinementHistoryOrderOutputFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_refinementHistoryForcingOutputFormula {n : Nat}
    (output rows T stages history N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (naturals : env N = ZFSet.omega) :
    Realize M.sets (refinementHistoryForcingOutputFormula output rows T stages history N) env ↔
      env output = M.refinementHistoryForcing (env rows) (env T) (env stages) (env history) := by
  rw [refinementHistoryForcingOutputFormula, realize_exBlock]
  have actual (fields : Fin 2 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets (.conj
        (refinementDataHistoryIndicesSetFormula (prefixIndex n 2 0)
          (suffixIndex n 2 stages) (suffixIndex n 2 history))
        (.conj (refinementDataHistoryLevelsSetFormula (prefixIndex n 2 1)
          (suffixIndex n 2 stages) (suffixIndex n 2 history) (suffixIndex n 2 T))
          (forcingHistoryConditionsOutputFormula (suffixIndex n 2 output) (suffixIndex n 2 rows)
            (prefixIndex n 2 0) (suffixIndex n 2 T) (suffixIndex n 2 stages)
            (suffixIndex n 2 history) (prefixIndex n 2 1) (suffixIndex n 2 N))))
        (extendMany 2 fields env) ↔
      fields 0 = refinementDataHistoryIndices (env stages) (env history) ∧
        fields 1 = refinementDataHistoryLevels (env stages) (env history) (env T) ∧
        env output = M.forcingHistoryConditions (env rows) (fields 0) (env T)
          (env stages) (env history) (fields 1) := by
    have bounds := extendMany_members 2 fields env ground members
    apply and_congr
    · simpa only [extendMany_prefix, extendMany_suffix] using
        M.realize_refinementDataHistoryIndicesSetFormula pairing unions powers separation
          (prefixIndex n 2 0) (suffixIndex n 2 stages) (suffixIndex n 2 history)
          (extendMany 2 fields env) bounds
    apply and_congr
    · simpa only [extendMany_prefix, extendMany_suffix] using
        M.realize_refinementDataHistoryLevelsSetFormula pairing unions powers separation
          (prefixIndex n 2 1) (suffixIndex n 2 stages) (suffixIndex n 2 history) (suffixIndex n 2 T)
          (extendMany 2 fields env) bounds
    · simpa only [extendMany_prefix, extendMany_suffix] using
        M.realize_forcingHistoryConditionsOutputFormula pairing separation
          (suffixIndex n 2 output) (suffixIndex n 2 rows) (prefixIndex n 2 0)
          (suffixIndex n 2 T) (suffixIndex n 2 stages) (suffixIndex n 2 history)
          (prefixIndex n 2 1) (suffixIndex n 2 N) (extendMany 2 fields env) bounds
          (by simpa only [extendMany_suffix] using naturals)
  constructor
  · rintro ⟨fields, ground, body⟩
    obtain ⟨indices, levels, outputEq⟩ := (actual fields ground).1 body
    rw [indices, levels] at outputEq
    exact outputEq
  · intro equal
    let fields : Fin 2 → ZFSet.{u} :=
      ![refinementDataHistoryIndices (env stages) (env history),
        refinementDataHistoryLevels (env stages) (env history) (env T)]
    have ground : ∀ j, fields j ∈ M.sets :=
      Fin.cases (M.refinementDataHistoryIndices_mem pairing unions powers separation
        (members stages) (members history))
        (Fin.cases (M.refinementDataHistoryLevels_mem pairing unions powers separation
          (members stages) (members history) (members T)) (fun j => Fin.elim0 j))
    exact ⟨fields, ground, (actual fields ground).2 ⟨rfl, rfl, equal⟩⟩

end TransitiveGround
end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStructuralForcingActionGraphs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

theorem realize_structuralForcingCarrierFormula {n : Nat}
    (output rows G nodes nodeOrder basis T T2 stages history N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) (naturals : env N = ZFSet.omega) :
    Realize M.sets (M.structuralForcingCarrierFormula pairing unions powers separation collection
      output rows G nodes nodeOrder basis T T2 stages history N) env ↔
      env output = M.structuralForcingCarrier (env rows) (env G) (env nodes) (env nodeOrder)
        (env basis) (env T) (env T2) (env stages) (env history) := by
  unfold structuralForcingCarrierFormula
  rw [realize_ex]
  let params : Fin 8 → ZFSet.{u} := ![env G, env nodes, env nodeOrder, env basis, env T, env T2, env stages, env history]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases (members G) (Fin.cases (members nodes)
    (Fin.cases (members nodeOrder) (Fin.cases (members basis) (Fin.cases (members T)
      (Fin.cases (members T2) (Fin.cases (members stages) (Fin.cases (members history) (fun j => Fin.elim0 j))))))))
  have args (H : ZFSet.{u}) :
      (fun j : Fin 8 => extend H env
        (![G.succ, nodes.succ, nodeOrder.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ] j)) = params := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))) j
  have meaning (H : ZFSet.{u}) (hH : H ∈ M.sets) :
      Realize M.sets (.conj
        (reindex (extend 0 ![G.succ, nodes.succ, nodeOrder.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ])
          (M.definable_structuralRefinementHistory pairing unions powers separation collection).formula)
        (refinementHistoryForcingOutputFormula output.succ rows.succ T.succ stages.succ 0 N.succ))
        (extend H env) ↔
      H = M.structuralRefinementHistory (env G) (env nodes) (env nodeOrder) (env basis)
        (env T) (env T2) (env stages) (env history) ∧
      env output = M.refinementHistoryForcing (env rows) (env T) (env stages) H := by
    apply and_congr
    · rw [realize_reindex, map_extend, args]
      exact (M.definable_structuralRefinementHistory pairing unions powers separation collection).correct
        params ground H hH
    · exact M.realize_refinementHistoryForcingOutputFormula pairing unions powers separation
        output.succ rows.succ T.succ stages.succ 0 N.succ (extend H env) (Fin.cases hH members) naturals
  constructor
  · rintro ⟨H, hH, holds⟩
    obtain ⟨rfl, equal⟩ := (meaning H hH).1 holds
    exact equal
  · intro equal
    have packed := (M.definable_structuralRefinementHistory pairing unions powers separation collection).closed params ground
    exact ⟨_, packed, (meaning _ packed).2 ⟨rfl, equal⟩⟩

end PartitionPilot.Forcing.TransitiveGround




end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundStructuralForcingHistoryConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

include pairing unions powers separation collection in
theorem structuralForcingStage_mem (env : Fin 13 → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) :
    M.structuralForcingStage (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)
      (env 7) (env 8) (env 9) (env 10) (env 11) (env 12) ∈ M.sets := by
  have carrier := M.structuralForcingCarrier_mem pairing unions powers separation collection
    ![env 0, env 4, env 5, env 6, env 8, env 9, env 10, env 11, env 12]
    (Fin.cases (members 0) (Fin.cases (members 4) (Fin.cases (members 5)
      (Fin.cases (members 6) (Fin.cases (members 8) (Fin.cases (members 9)
        (Fin.cases (members 10) (Fin.cases (members 11) (Fin.cases (members 12) (fun j => Fin.elim0 j)))))))))) omega
  exact (M.definable_structuralForcingStageFromCarrier pairing unions powers separation collection).closed
    (extend _ env) (Fin.cases carrier members)

theorem realize_structuralForcingStageFormula {n : Nat}
    (output rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) (naturals : env N = ZFSet.omega) :
    Realize M.sets (M.structuralForcingStageFormula pairing unions powers separation collection
      output rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 stages history N) env ↔
      env output = M.structuralForcingStage (env rows) (env rowOrder) (env rowTop) (env rowAction)
        (env G) (env nodes) (env nodeOrder) (env nodeAction) (env basis) (env T) (env T2) (env stages) (env history) := by
  unfold structuralForcingStageFormula
  rw [realize_ex]
  let params : Fin 13 → ZFSet.{u} := ![env rows, env rowOrder, env rowTop, env rowAction,
    env G, env nodes, env nodeOrder, env nodeAction, env basis, env T, env T2, env stages, env history]
  have ground : ∀ j, params j ∈ M.sets := Fin.cases (members rows) (Fin.cases (members rowOrder)
    (Fin.cases (members rowTop) (Fin.cases (members rowAction) (Fin.cases (members G)
      (Fin.cases (members nodes) (Fin.cases (members nodeOrder) (Fin.cases (members nodeAction)
        (Fin.cases (members basis) (Fin.cases (members T) (Fin.cases (members T2)
          (Fin.cases (members stages) (Fin.cases (members history) (fun j => Fin.elim0 j)))))))))))))
  have args (Q : ZFSet.{u}) :
      (fun j : Fin 14 => extend Q env (![0, rows.succ, rowOrder.succ, rowTop.succ, rowAction.succ,
        G.succ, nodes.succ, nodeOrder.succ, nodeAction.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ] j)) =
      extend Q params := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))))))))))) j
  have meaning (Q : ZFSet.{u}) (hQ : Q ∈ M.sets) :
      Realize M.sets (.conj
        (M.structuralForcingCarrierFormula pairing unions powers separation collection
          0 rows.succ G.succ nodes.succ nodeOrder.succ basis.succ T.succ T2.succ stages.succ history.succ N.succ)
        (reindex (extend output.succ ![0, rows.succ, rowOrder.succ, rowTop.succ, rowAction.succ,
          G.succ, nodes.succ, nodeOrder.succ, nodeAction.succ, basis.succ, T.succ, T2.succ, stages.succ, history.succ])
          (M.definable_structuralForcingStageFromCarrier pairing unions powers separation collection).formula))
        (extend Q env) ↔
      Q = M.structuralForcingCarrier (env rows) (env G) (env nodes) (env nodeOrder) (env basis)
        (env T) (env T2) (env stages) (env history) ∧
      env output = M.structuralForcingStageFromCarrier Q (env rows) (env rowOrder) (env rowTop) (env rowAction)
        (env G) (env nodes) (env nodeOrder) (env nodeAction) (env basis) (env T) (env T2) (env stages) (env history) := by
    apply and_congr
    · exact M.realize_structuralForcingCarrierFormula pairing unions powers separation collection
        0 rows.succ G.succ nodes.succ nodeOrder.succ basis.succ T.succ T2.succ stages.succ history.succ N.succ
        (extend Q env) (Fin.cases hQ members) naturals
    · rw [realize_reindex, map_extend, args]
      exact (M.definable_structuralForcingStageFromCarrier pairing unions powers separation collection).correct
        (extend Q params) (Fin.cases hQ ground) (env output) (members output)
  constructor
  · rintro ⟨Q, hQ, holds⟩
    obtain ⟨rfl, equal⟩ := (meaning Q hQ).1 holds
    exact equal
  · intro equal
    have carrier := M.structuralForcingCarrier_mem pairing unions powers separation collection
      ![env rows, env G, env nodes, env nodeOrder, env basis, env T, env T2, env stages, env history]
      (Fin.cases (members rows) (Fin.cases (members G) (Fin.cases (members nodes)
        (Fin.cases (members nodeOrder) (Fin.cases (members basis) (Fin.cases (members T)
          (Fin.cases (members T2) (Fin.cases (members stages) (Fin.cases (members history) (fun j => Fin.elim0 j))))))))))
      (naturals ▸ members N)
    exact ⟨_, carrier, (meaning _ carrier).2 ⟨rfl, equal⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)

theorem realize_structuralForcingStepFormula (params : Fin 12 → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) (naturals : params 11 = ZFSet.omega)
    {alpha prior output : ZFSet.{u}} (ha : alpha ∈ M.sets) (hp : prior ∈ M.sets) (ho : output ∈ M.sets) :
    Realize M.sets (M.structuralForcingStepFormula pairing unions powers separation collection)
      (extend alpha (extend prior (extend output params))) ↔
    output = M.structuralForcingStage (params 0) (params 1) (params 2) (params 3) (params 4)
      (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) alpha prior :=
  M.realize_structuralForcingStageFormula pairing unions powers separation collection
    2 3 4 5 6 7 8 9 10 11 12 13 0 1 14 _ (Fin.cases ha (Fin.cases hp (Fin.cases ho members))) naturals

theorem structuralForcingStepClosure (params : Fin 12 → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) (naturals : params 11 = ZFSet.omega)
    {stages : ZFSet.{u}} (hs : stages ∈ M.sets) :
    GroundOrdinalStepClosure M stages (M.structuralForcingStepFormula pairing unions powers separation collection) params := by
  intro alpha halpha prior hprior _trace
  have ha := M.transitive hs halpha
  let args : Fin 13 → ZFSet.{u} := ![params 0,params 1,params 2,params 3,params 4,params 5,
    params 6,params 7,params 8,params 9,params 10,alpha,prior]
  have ground : ∀ j, args j ∈ M.sets := by
    exact Fin.cases (members 0) (Fin.cases (members 1) (Fin.cases (members 2) (Fin.cases (members 3)
      (Fin.cases (members 4) (Fin.cases (members 5) (Fin.cases (members 6) (Fin.cases (members 7)
        (Fin.cases (members 8) (Fin.cases (members 9) (Fin.cases (members 10)
          (Fin.cases ha (Fin.cases hprior (fun j => Fin.elim0 j)))))))))))))
  have outputGround := M.structuralForcingStage_mem pairing unions powers separation collection args ground
    (naturals ▸ members 11)
  refine ⟨_, outputGround, ?_, ?_⟩
  · exact (M.realize_structuralForcingStepFormula pairing unions powers separation collection params members naturals
      ha hprior outputGround).2 rfl
  · intro output ho recognized
    exact (M.realize_structuralForcingStepFormula pairing unions powers separation collection params members naturals
      ha hprior ho).1 recognized

theorem exists_structuralForcingTrace (params : Fin 12 → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) (naturals : params 11 = ZFSet.omega)
    {stages : ZFSet.{u}} (hs : stages ∈ M.sets) (ordinal : ordinalSetProperty stages) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M
        (M.structuralForcingStepFormula pairing unions powers separation collection) params) stages history ∧
      OrdinalRecursionTrace (fun alpha prior output =>
        output = M.structuralForcingStage (params 0) (params 1) (params 2) (params 3) (params 4)
          (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) alpha prior) stages history ∧
      (∀ other, OrdinalRecursionTrace (groundRecursionStep M
        (M.structuralForcingStepFormula pairing unions powers separation collection) params) stages other → other = history) ∧
      ∀ alpha ∈ stages, ∀ output ∈ M.sets,
        ZFSet.pair alpha output ∈ history ↔
          output = M.structuralForcingStage (params 0) (params 1) (params 2) (params 3) (params 4)
            (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) alpha (graphRestriction alpha history) := by
  obtain ⟨history, hh, trace, unique, entry⟩ := M.exists_unique_ordinalRecursionTrace pairing unions separation collection
    hs ordinal (M.structuralForcingStepFormula pairing unions powers separation collection) params members
    (M.structuralForcingStepClosure pairing unions powers separation collection params members naturals hs)
  refine ⟨history, hh, trace, ⟨trace.1, ?_⟩, unique, ?_⟩
  · intro alpha halpha output stored
    have step := trace.2 alpha halpha output stored
    exact (M.realize_structuralForcingStepFormula pairing unions powers separation collection params members naturals
      (M.transitive hs halpha) step.1 step.2.1).1 step.2.2
  intro alpha halpha output ho
  have ha := M.transitive hs halpha
  exact (entry alpha halpha output ho).trans
    (M.realize_structuralForcingStepFormula pairing unions powers separation collection params members naturals
      ha (M.graphRestriction_mem unions separation ha hh) ho)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})
variable (rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2 : ZFSet.{u})

theorem structuralForcingTrace_stageOrderTop {stages history : ZFSet.{u}}
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace
      (fun level prior stage => stage = M.structuralForcingStage rows rowOrder rowTop rowAction
        G nodes nodeOrder nodeAction basis T T2 level prior) stages history)
    (hRows : rows ∈ M.sets) (rowOrderLaw : PartialOrderCode rows rowOrder)
    (topMem : rowTop ∈ rows) (topRows : ∀ row ∈ rows, ZFSet.pair row rowTop ∈ rowOrder) :
    ∀ level P order top action, ZFSet.pair level (forcingStageCode P order top action) ∈ history →
      PartialOrderCode P order ∧ top ∈ P ∧ ∀ p ∈ P, ZFSet.pair p top ∈ order := by
  intro level P order top action stored
  have hl := trace.1.pair_source stored
  have cutOrdinal := ordinalSetProperty_member ordinal hl
  have earlier := trace.restrict cutOrdinal (ordinal.1 level hl)
  have run := M.structuralForcingTrace_recursiveOrder rows rowOrder rowTop rowAction G nodes
    nodeOrder nodeAction basis T T2 cutOrdinal earlier
  have equal := (trace.2 level hl _ stored).trans
    (M.structuralForcingStage_eq rows rowOrder rowTop rowAction G nodes nodeOrder nodeAction basis T T2
      level (graphRestriction level history))
  obtain ⟨rfl, rfl, rfl, rfl⟩ := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 equal
  exact ⟨M.refinementHistoryOrder_partialOrder rowOrderLaw T level _,
    run.carriers.empty_assignments cutOrdinal hRows topMem,
    run.carriers.greatest cutOrdinal hRows topMem topRows⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})





theorem exists_structuralForcingHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (params : Fin 12 → ZFSet.{u}) (members : ∀ j, params j ∈ M.sets)
    (naturals : params 11 = ZFSet.omega)
    {stages : ZFSet.{u}} (hStages : stages ∈ M.sets) (ordinal : ordinalSetProperty stages)
    (rowOrderLaw : PartialOrderCode (params 0) (params 1))
    (topMem : params 2 ∈ params 0)
    (topRows : ∀ row ∈ params 0, ZFSet.pair row (params 2) ∈ params 1) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (fun level prior stage =>
        stage = M.structuralForcingStage (params 0) (params 1) (params 2) (params 3) (params 4)
          (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) level prior) stages history ∧
      M.structuralRefinementHistory (params 4) (params 5) (params 6) (params 8) (params 9) (params 10)
        stages history ∈ M.sets ∧
      RecursiveRefinementOrderHistory M (params 0) (params 1) (params 9) stages
        (M.structuralRefinementHistory (params 4) (params 5) (params 6) (params 8) (params 9) (params 10)
          stages history) ∧
      ∀ level P order top action, ZFSet.pair level (forcingStageCode P order top action) ∈ history →
        PartialOrderCode P order ∧ top ∈ P ∧ ∀ p ∈ P, ZFSet.pair p top ∈ order := by
  obtain ⟨history, hHistory, _groundTrace, trace, _unique, _lookup⟩ :=
    M.exists_structuralForcingTrace pairing unions powers separation collection params members naturals hStages ordinal
  refine ⟨history, hHistory, trace, ?_, ?_, ?_⟩
  · exact (M.definable_structuralRefinementHistory pairing unions powers separation collection).closed
      ![params 4, params 5, params 6, params 8, params 9, params 10, stages, history]
      (Fin.cases (members 4) (Fin.cases (members 5) (Fin.cases (members 6)
        (Fin.cases (members 8) (Fin.cases (members 9) (Fin.cases (members 10)
          (Fin.cases hStages (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
  · exact M.structuralForcingTrace_recursiveOrder (params 0) (params 1) (params 2) (params 3)
      (params 4) (params 5) (params 6) (params 7) (params 8) (params 9) (params 10) ordinal trace
  · exact M.structuralForcingTrace_stageOrderTop (params 0) (params 1) (params 2) (params 3)
      (params 4) (params 5) (params 6) (params 7) (params 8) (params 9) (params 10)
      ordinal trace (members 0) rowOrderLaw topMem topRows

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundSemanticFairPreparationLimits
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

theorem exists_semanticStructuralForcingHistory
    {stages : ZFSet.{u}} (hs : stages ∈ M.sets) (ordinal : ordinalSetProperty stages) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
          t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 level prior) stages history ∧
      M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 stages history ∈ M.sets ∧
      RecursiveRefinementOrderHistory M c.carrier c.conditionOrder T stages
        (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) T T2 stages history) ∧
      ∀ level P order top action,
        ZFSet.pair level (forcingStageCode P order top action) ∈ history →
        RawRefinementStageWitness M t b d base directed T T2 level P order top action := by
  let params : Fin 12 → ZFSet.{u} := ![c.carrier, c.conditionOrder, rowTop, a.actionGraph c t,
    t.carrier, b.carrier, b.conditionOrder, d.actionGraph b t,
    supportBasisCode b t d.principalFix, T, T2, ZFSet.omega]
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases carrier (Fin.cases rowOrderGround (Fin.cases (M.transitive carrier topMem)
      (Fin.cases rowAction (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder
        (Fin.cases nodeAction (Fin.cases supports (Fin.cases hT (Fin.cases hT2
          (Fin.cases omega (fun j => Fin.elim0 j))))))))))))
  obtain ⟨history, hh, trace, hPacked, run, _orderTop⟩ :=
    M.exists_structuralForcingHistory pairing unions powers separation collection params members rfl hs ordinal
      c.conditionOrder_code topMem topRows
  exact ⟨history, hh, trace, hPacked, run,
    structuralForcingTrace_witnesses M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [OrderTop R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem pairEmpty_semanticStructuralHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : c.carrier ∈ M.sets) (order : c.conditionOrder ∈ M.sets)
    (action : a.actionGraph c t ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets)
    (T : ZFSet.{u}) (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName c z)
    (closed : ∀ g (tau : Name c), tau.val ∈ T → (a.act c g tau).val ∈ T)
    (children : ∀ tau : Name c, tau.val ∈ T →
      HereditarilySymmetric a c (d.principalSupportFamily base directed) tau) :
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let graph := Name.renameFamilyGraph c.pairEmpty id T valid
    lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
      (∀ z ∈ lifted, IsName c.pairEmpty z) ∧ (∀ z ∈ squared, IsName c.pairEmpty z) ∧
      (∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (a.act c.pairEmpty g tau).val ∈ lifted) ∧
      (∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (a.act c.pairEmpty g tau).val ∈ squared) ∧
      (∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau) ∧
      (∀ tau : Name c.pairEmpty, tau.val ∈ squared →
        HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau) ∧
      ∀ stages ∈ M.sets, ordinalSetProperty stages → ∃ history ∈ M.sets,
        OrdinalRecursionTrace (fun level prior stage => stage =
          M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (a.actionGraph c t)
            t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
            (supportBasisCode b t d.principalFix) lifted squared level prior) stages history ∧
        M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
          (supportBasisCode b t d.principalFix) lifted squared stages history ∈ M.sets ∧
        RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted stages
          (M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
            (supportBasisCode b t d.principalFix) lifted squared stages history) ∧
        ∀ level P order top action,
          ZFSet.pair level (forcingStageCode P order top action) ∈ history →
          RawRefinementStageWitness M t b d base directed lifted squared level P order top action := by
  obtain ⟨hLifted, hGraph, injection, valid1, hs1, closed1, _⟩ :=
    M.pairEmpty_nameFamily a c (d.principalSupportFamily base directed)
      pairing unions powers separation collection carrier T hT valid closed children
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  have pairedCarrier := M.pairEmpty_carrier_mem pairing unions powers separation c carrier
  have hTop := M.transitive pairedCarrier (c.pairEmpty.encode_mem ⊤)
  have hSquared : squared ∈ M.sets :=
    M.orderedPairNameFamily_mem pairing unions powers separation hTop hLifted hLifted
  have valid2 : ∀ z ∈ squared, IsName c.pairEmpty z := orderedPairNameFamily_valid ⊤ valid1 valid1
  have closed2 := orderedPairNameFamily_closed a valid1 valid1 closed1 closed1
  have hs2 := orderedPairNameFamily_hs a (d.principalSupportFamily base directed) valid1 valid1 hs1 hs1
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph d b t pairing unions powers separation collection
    nodes group nodeAction
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  refine ⟨hLifted, hSquared, hGraph, injection, valid1, valid2, closed1, closed2, hs1, hs2, ?_⟩
  intro stages hStages ordinal
  exact M.exists_semanticStructuralForcingHistory c a t b d base directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier order action group nodes nodeOrder nodeAction
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 hs1 hs2
    (c.encode_mem ⊤) topRows hStages ordinal

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

theorem semanticStructuralCurrent_stage
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history) :
    ∃ P order top action,
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history = forcingStageCode P order top action ∧
      (P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets) ∧
      RawRefinementStageWitness M t b d base directed T T2 stages P order top action := by
  have ground := M.structuralForcingStage_mem pairing unions powers separation collection
    ![c.carrier, c.conditionOrder, rowTop, a.actionGraph c t, t.carrier, b.carrier,
      b.conditionOrder, d.actionGraph b t, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases carrier (Fin.cases rowOrderGround (Fin.cases (M.transitive carrier topMem) (Fin.cases rowAction (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases nodeAction (Fin.cases supports (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))))))) omega
  have equal := M.structuralForcingStage_eq c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history
  change M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history ∈ M.sets at ground
  rw [equal] at ground
  exact ⟨_, _, _, _, equal, M.forcingStageCode_fields ground,
    semanticStructuralCurrent_witness M c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hs hh ordinal trace _ _ _ _ equal.symm⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundMainFinalSemanticStructuralZF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



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

theorem exists_rowSemanticStructuralHistory
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, geometry.carrier_ground⟩
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let directed := geometry.decoded_directed fulfilled.directed
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
      T ∈ M.sets ∧ GroundBelow M T K ∧ ∃ valid : ∀ z ∈ T, IsName c z,
        let lifted := Name.renamedFamily c.pairEmpty id T valid
        let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
        let graph := Name.renameFamilyGraph c.pairEmpty id T valid
        lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          (∀ z ∈ lifted, IsName c.pairEmpty z) ∧ (∀ z ∈ squared, IsName c.pairEmpty z) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          ∀ stages ∈ M.sets, ordinalSetProperty stages → ∃ history ∈ M.sets,
            OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) stages history ∧
            M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
              (supportBasisCode s b a.principalFix) lifted squared stages history ∈ M.sets ∧
            RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted stages
              (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared stages history) ∧
            ∀ level P order top action,
              ZFSet.pair level (forcingStageCode P order top action) ∈ history →
              RawRefinementStageWitness M b s a ⊥ directed lifted squared level P order top action := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground order action
  obtain ⟨mu, hmu, hmuK, cardinal, omega, positions, _, _, _, _, _, _, _, stageTerms⟩ :=
    fulfilled.exists_rowTermSystem collection infinite choice hK standard indices
  obtain ⟨ground, below, valid, children, _⟩ := stageTerms 0
  have closed := M.binaryRowTupleTerms_action a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action hmu cardinal.1
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid, ?_⟩
  exact M.pairEmpty_semanticStructuralHistory c act b s a ⊥ directed
    pairing unions powers separation collection carrier forcingOrder forcingAction
    geometry.actors_ground geometry.carrier_ground order action supports
    (M.omega_mem separation infinite) _ ground valid closed children






theorem exists_rowSemanticStructuralFinalHistory
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, geometry.carrier_ground⟩
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let directed := geometry.decoded_directed fulfilled.directed
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
      T ∈ M.sets ∧ GroundBelow M T K ∧ ∃ valid : ∀ z ∈ T, IsName c z,
        let lifted := Name.renamedFamily c.pairEmpty id T valid
        let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
        let graph := Name.renameFamilyGraph c.pairEmpty id T valid
        lifted ∈ M.sets ∧ squared ∈ M.sets ∧ graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          (∀ z ∈ lifted, IsName c.pairEmpty z) ∧ (∀ z ∈ squared, IsName c.pairEmpty z) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted) ∧
          (∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          (∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau) ∧
          ∀ stages ∈ M.sets, ordinalSetProperty stages → ∃ history ∈ M.sets,
            OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) stages history ∧
            M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
              (supportBasisCode s b a.principalFix) lifted squared stages history ∈ M.sets ∧
            RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted stages
              (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared stages history) ∧
            (∀ level P order top action,
              ZFSet.pair level (forcingStageCode P order top action) ∈ history →
              RawRefinementStageWitness M b s a ⊥ directed lifted squared level P order top action) ∧
            ∃ P order top action,
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared stages history =
                  forcingStageCode P order top action ∧
              (P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets) ∧
              RawRefinementStageWitness M b s a ⊥ directed lifted squared stages P order top action := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have action : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have two := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  have forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground action
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground order action
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground action
  have original := fulfilled.exists_rowSemanticStructuralHistory collection infinite choice hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, valid, data⟩ := data
  obtain ⟨hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, histories⟩ := data
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, ?_⟩
  intro stages hStages ordinal
  obtain ⟨history, hHistory, trace, hPacked, historyRun, witnesses⟩ := histories stages hStages ordinal
  refine ⟨history, hHistory, trace, hPacked, historyRun, witnesses, ?_⟩
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  exact M.semanticStructuralCurrent_stage c act b s a ⊥ directed _ _ (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction
    geometry.actors_ground geometry.carrier_ground order action nodeMaps supports hLifted hSquared
    (M.omega_mem separation infinite) valid1 valid2 closed1 closed2 children1 children2
    (c.encode_mem ⊤) topRows hStages hHistory ordinal trace






theorem exists_rowSemanticStructuralSequenceReflection
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, geometry.carrier_ground⟩
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let directed := geometry.decoded_directed fulfilled.directed
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
      T ∈ M.sets ∧ GroundBelow M T K ∧ ∃ valid : ∀ z ∈ T, IsName c z,
        let lifted := Name.renamedFamily c.pairEmpty id T valid
        let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
        let graph := Name.renameFamilyGraph c.pairEmpty id T valid
        ∃ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
          (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
          (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
          (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
          (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
          (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
          (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau),
          graph ∈ M.sets ∧ InjectionCode T lifted graph ∧
          ∃ (history : ZFSet.{u}) (hHistory : history ∈ M.sets)
            (trace : OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) K history),
            M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
              (supportBasisCode s b a.principalFix) lifted squared K history ∈ M.sets ∧
            RecursiveRefinementOrderHistory M c.carrier c.conditionOrder lifted K
              (M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared K history) ∧
            (∀ level P order top action,
              ZFSet.pair level (forcingStageCode P order top action) ∈ history →
              RawRefinementStageWitness M b s a ⊥ directed lifted squared level P order top action) ∧
            ∃ P order top action,
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared K history =
                  forcingStageCode P order top action ∧
              (P ∈ M.sets ∧ order ∈ M.sets ∧ top ∈ M.sets ∧ action ∈ M.sets) ∧
              RawRefinementStageWitness M b s a ⊥ directed lifted squared K P order top action ∧
              let coordinateGround := M.prod_mem pairing unions powers separation
                (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
              let nodeActionGround : a.actionGraph s b ∈ M.sets :=
                geometry.decoded_action_eq.symm ▸ geometry.action_ground
              let nodeOrderGround : s.conditionOrder ∈ M.sets :=
                geometry.decoded_order_eq.symm ▸ geometry.order_ground
              let forcingActionGround := M.internalRowActionGraph_mem a s b columns
                pairing unions powers separation infinite geometry.carrier_ground hColumns
                geometry.actors_ground nodeActionGround
              let supportGround := M.principalSupportBasis_mem a s b pairing unions powers separation
                geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
              let nodeMapsGround := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
                collection geometry.carrier_ground geometry.actors_ground nodeActionGround
              let topMem := c.encode_mem ⊤
              let topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
                intro row member
                obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
                exact (c.pair_mem_conditionOrder p ⊤).2 le_top
              let two := M.natSetCode_mem separation infinite 2
              let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinateGround two
              let forcingOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinateGround two
              let omega := M.omega_mem separation infinite
              let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared K history
              let Q := M.refinementHistoryForcing c.carrier lifted K packed
              let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ K}
              let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier lifted (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
              let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b) (supportBasisCode s b a.principalFix) lifted squared standard.1.1 trace
              let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
              let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared K history
                pairing unions powers separation collection geometry.actors_ground geometry.carrier_ground supportGround hHistory hLifted witnesses
              let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
                ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, lifted, squared, K, history]
                (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrderGround (Fin.cases supportGround
                  (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hK (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
              letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted K packed
              let upperAction := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
              letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
                M.refinementHistoryPartialOrder c.conditionOrder_code lifted j.val (graphRestriction j.val packed)
              let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
                (run).restriction standard.1.1 j.property.2.1 j.property.2.2 c.conditionOrder_code
              let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
                (run).inclusion standard.1.1 j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
                  hK hPacked hLifted j.property.1 carrier (c.encode ⊤) topMem topRows mono c.conditionOrder_code
              let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
                M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace j.val j.property.1
                  j.property.2.1 j.property.2.2 infinite choice
              let upperPres := SetMembers.presentation Q
              let F := a.principalSupportFamily ⊥ directed
              P = Q ∧
              ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
                H.mem p ∧ H.GenericFor (M.codedFamily upperPres) ∧
                H.GenericFor (formulaFamily (M.nameDomain upperPres)) ∧
                H.GenericFor (formulaFamily ((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F)) ∧
                (∀ j : Cuts,
                  ((projections j).projectedFilter H).GenericFor
                    (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier lifted j.val (graphRestriction j.val packed)))) ∧
                  ((projections j).projectedFilter H).GenericFor
                    (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier lifted j.val (graphRestriction j.val packed)))))) ∧
                M.sets ⊆ ((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F).values {q | H.mem q} ∧
                ZFRealization (((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F).values {q | H.mem q}) ∧
                (∀ U ∈ M.sets,
                  GroundSequenceReflection M (M.ordinaryExtension upperPres H) U ∧
                  GroundSequenceReflection M (M.symmetricExtension upperPres (upperAction) F H) U) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have nodeActionGround : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have nodeOrderGround : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  have original := fulfilled.exists_rowSemanticStructuralFinalHistory collection infinite choice hK standard indices
  refine original.elim (fun mu data => ?_)
  obtain ⟨hmu, hmuK, cardinal, omega, positions, ground, below, valid, data⟩ := data
  obtain ⟨hLifted, hSquared, hGraph, injection, valid1, valid2,
    closed1, closed2, children1, children2, histories⟩ := data
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omega, positions, ground, below, valid,
    hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2, hGraph, injection, ?_⟩
  obtain ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, action, code, fields, witness⟩ := histories K hK standard.1.1
  refine ⟨history, hHistory, trace, hPacked, historyRun, witnesses,
    P, forcingOrder, top, action, code, fields, witness, ?_⟩
  have topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (ZFSet.sUnion (ZFSet.sUnion rows)) rows S
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  have canonical := M.structuralForcingStage_eq c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
    b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
    (supportBasisCode s b a.principalFix) lifted squared K history
  have equalFields := (forcingStageCode_eq_iff _ _ _ _ _ _ _ _).1 (code.symm.trans canonical)
  refine ⟨equalFields.1, ?_⟩
  exact M.countableRow_semanticStructuralTrace_jointZF_sequenceReflection b s a ⊥ directed
    pairing unions powers separation collection infinite choice
    (ZFSet.prod s.nonbottom.carrier columns) coordinates small act lifted squared (c.encode ⊤)
    forcingAction geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround
    nodeMaps supports hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    (c.encode_mem ⊤) topRows K history hK hHistory standard.1.1 trace






end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundStructuralFullIndexSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {A B N K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem smallPartialFunctions (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hN : N ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (first : GroundBelow M A K) (second : GroundBelow M B K) :
    GroundBelow M (M.smallPartialFunctions A B N) K :=
  (partialFunctions pairing unions powers separation hA hB hK ordinal strong first second).restrict
    separation (M.smallPartialFunctions_mem pairing unions powers separation hA hB hN) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

end PartitionPilot.Forcing.GroundBelow

namespace PartitionPilot.Forcing.GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {I C K : ZFSet.{u}}

theorem binaryRowCarrier
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (indices : GroundBelow M I K) (columns : GroundBelow M C K) :
    GroundBelow M (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega) K := by
  have hOmega := M.transitive hK conditions.2.1
  have hTwo := M.transitive hOmega (natSetCode_mem_omega 2)
  have twoBelow := of_member pairing unions powers separation hK
    (conditions.1.1 ZFSet.omega conditions.2.1 _ (natSetCode_mem_omega 2))
  exact smallPartialFunctions pairing unions powers separation
    (M.prod_mem pairing unions powers separation hI hC) hTwo hOmega hK
    conditions.1 conditions.2.2.2
    (product pairing unions powers separation hI hC hK conditions.1 conditions.2.2.2 indices columns)
    twoBelow

end PartitionPilot.Forcing.GroundBelow

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






theorem exists_rowSemanticQuotientInjectionModel_oai
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K)
    (labels : Labels = M.groundOmegaOne pairing unions powers separation collection infinite)
    (smallD : M.groundEmbeddable D ZFSet.omega)
    (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, geometry.carrier_ground⟩
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let directed := geometry.decoded_directed fulfilled.directed
    ∃ mu ∈ M.sets, mu ∈ K ∧ GroundCardinal M mu ∧ ZFSet.omega ⊆ mu ∧
      M.groundEmbeddable s.nonbottom.carrier mu ∧
      let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
      let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
      let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
      T ∈ M.sets ∧ GroundBelow M T K ∧ ∃ valid : ∀ z ∈ T, IsName c z,
        let lifted := Name.renamedFamily c.pairEmpty id T valid
        let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
        ∃ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
          (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
          (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
          (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
          (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
          (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
          (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
            HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau),
          ∃ (history : ZFSet.{u}) (hHistory : history ∈ M.sets)
            (trace : OrdinalRecursionTrace (fun level prior stage => stage =
              M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
                (supportBasisCode s b a.principalFix) lifted squared level prior) K history),
              let coordinateGround := M.prod_mem pairing unions powers separation
                (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
              let nodeActionGround : a.actionGraph s b ∈ M.sets :=
                geometry.decoded_action_eq.symm ▸ geometry.action_ground
              let nodeOrderGround : s.conditionOrder ∈ M.sets :=
                geometry.decoded_order_eq.symm ▸ geometry.order_ground
              let forcingActionGround := M.internalRowActionGraph_mem a s b columns
                pairing unions powers separation infinite geometry.carrier_ground hColumns
                geometry.actors_ground nodeActionGround
              let supportGround := M.principalSupportBasis_mem a s b pairing unions powers separation
                geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
              let nodeMapsGround := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
                collection geometry.carrier_ground geometry.actors_ground nodeActionGround
              let topMem := c.encode_mem ⊤
              let topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
                intro row member
                obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
                exact (c.pair_mem_conditionOrder p ⊤).2 le_top
              let two := M.natSetCode_mem separation infinite 2
              let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinateGround two
              let forcingOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinateGround two
              let omega := M.omega_mem separation infinite
              let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
                (supportBasisCode s b a.principalFix) lifted squared K history
              let Q := M.refinementHistoryForcing c.carrier lifted K packed
              let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ K}
              let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier lifted (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
              let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
                b.carrier s.carrier s.conditionOrder (a.actionGraph s b) (supportBasisCode s b a.principalFix) lifted squared standard.1.1 trace
              let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
              let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared K history
                pairing unions powers separation collection geometry.actors_ground geometry.carrier_ground supportGround hHistory hLifted witnesses
              let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
                ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, lifted, squared, K, history]
                (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrderGround (Fin.cases supportGround
                  (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hK (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
              letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted K packed
              let upperAction := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
              letI : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
                M.refinementHistoryPartialOrder c.conditionOrder_code lifted j.val (graphRestriction j.val packed)
              let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
                (historyRun).restriction standard.1.1 j.property.2.1 j.property.2.2 c.conditionOrder_code
              let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
                (historyRun).inclusion standard.1.1 j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
                  hK hPacked hLifted j.property.1 carrier (c.encode ⊤) topMem topRows mono c.conditionOrder_code
              let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
                M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace j.val j.property.1
                  j.property.2.1 j.property.2.2 infinite choice
              let upperPres := SetMembers.presentation Q
              let F := a.principalSupportFamily ⊥ directed
              letI := M.refinementHistoryOrderTop c.conditionOrder_code lifted K packed
                historyRun.carriers standard.1.1 carrier (c.encode ⊤) topMem topRows
              let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers
                standard.1.1 carrier lifted valid1
              ∀ p : SetMembers Q, ∃ H : ConditionFilter (SetMembers Q),
                H.mem p ∧ H.GenericFor (M.codedFamily upperPres) ∧
                H.GenericFor (formulaFamily (M.nameDomain upperPres)) ∧
                H.GenericFor (formulaFamily ((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F)) ∧
                (∀ j : Cuts,
                  ((projections j).projectedFilter H).GenericFor
                    (M.codedFamily (SetMembers.presentation (M.refinementHistoryForcing c.carrier lifted j.val (graphRestriction j.val packed)))) ∧
                  ((projections j).projectedFilter H).GenericFor
                    (formulaFamily (M.nameDomain (SetMembers.presentation (M.refinementHistoryForcing c.carrier lifted j.val (graphRestriction j.val packed)))))) ∧
                M.sets ⊆ ((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F).values {q | H.mem q} ∧
                ZFRealization (((upperAction).symmetricDomain upperPres (M.nameDomain upperPres) F).values {q | H.mem q}) ∧
                (∀ U ∈ M.sets,
                  GroundSequenceReflection M (M.ordinaryExtension upperPres H) U ∧
                  GroundSequenceReflection M (M.symmetricExtension upperPres (upperAction) F H) U) ∧
                (∀ tau : Fin 3 → (M.nameDomain upperPres).names,
                  (∀ i, HereditarilySymmetric upperAction upperPres F (tau i).val) →
                  RefinementValidityCode
                    (Name.eval {q | H.mem q} (Name.familySet ⊤ lifted validUpper))
                    (Name.eval {q | H.mem q} (tau 0).val) (Name.eval {q | H.mem q} (tau 1).val)
                    (Name.eval {q | H.mem q} (tau 2).val) →
                  ∃ J ∈ (M.symmetricExtension upperPres upperAction F H).sets,
                    InjectionCode
                      (equivalenceClasses (Name.eval {q | H.mem q} (tau 0).val)
                        (Name.eval {q | H.mem q} (tau 2).val))
                      (equivalenceClasses (Name.eval {q | H.mem q} (tau 0).val)
                        (Name.eval {q | H.mem q} (tau 1).val)) J) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  have hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, geometry.carrier_ground⟩
  have nodeActionGround : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  have nodeOrderGround : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  have directed := geometry.decoded_directed fulfilled.directed
  have coordinates := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  have forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground nodeActionGround
  have supports := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  have nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  have original := fulfilled.toFinalFulfillment.exists_rowSemanticStructuralSequenceReflection
    collection infinite choice small hK standard indices
  obtain ⟨mu, hmu, hmuK, cardinal, omegaIncluded, positions, ground, below, valid, data⟩ := original
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  obtain ⟨hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2,
    _hGraph, _injection, history, hHistory, trace, _hPacked0, _historyRun0, _witnesses0,
    _P, _order0, _top0, _action0, _code0, _fields0, _witness0, final⟩ := data
  dsimp only
  refine ⟨mu, hmu, hmuK, cardinal, omegaIncluded, positions, ground, below, valid,
    hLifted, hSquared, valid1, valid2, closed1, closed2, children1, children2,
    history, hHistory, trace, ?_⟩
  let coordinateGround := M.prod_mem pairing unions powers separation
    (M.nonbottom_carrier_mem s separation geometry.carrier_ground) hColumns
  let nodeActionGround : a.actionGraph s b ∈ M.sets :=
    geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeOrderGround : s.conditionOrder ∈ M.sets :=
    geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let forcingActionGround := M.internalRowActionGraph_mem a s b columns
    pairing unions powers separation infinite geometry.carrier_ground hColumns
    geometry.actors_ground nodeActionGround
  let supportGround := M.principalSupportBasis_mem a s b pairing unions powers separation
    geometry.carrier_ground geometry.actors_ground nodeOrderGround nodeActionGround
  let nodeMapsGround := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection geometry.carrier_ground geometry.actors_ground nodeActionGround
  let topMem := c.encode_mem ⊤
  let topRows : ∀ row ∈ c.carrier, ZFSet.pair row (c.encode ⊤) ∈ c.conditionOrder := by
    intro row member
    obtain ⟨p, rfl⟩ := (c.mem_carrier row).1 member
    exact (c.pair_mem_conditionOrder p ⊤).2 le_top
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinateGround two
  let forcingOrderGround := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinateGround two
  let omega := M.omega_mem separation infinite
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared K history
  let Q := M.refinementHistoryForcing c.carrier lifted K packed
  let Cuts := {alpha : ZFSet // alpha ∈ M.sets ∧ ordinalSetProperty alpha ∧ alpha ⊆ K}
  let lower := (fun j : Cuts => SetMembers (M.refinementHistoryForcing c.carrier lifted (Subtype.val j) (graphRestriction (Subtype.val j) packed)))
  let historyRun := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
    b.carrier s.carrier s.conditionOrder (a.actionGraph s b) (supportBasisCode s b a.principalFix) lifted squared standard.1.1 trace
  let witnesses := M.structuralForcingTrace_witnesses c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
  let mono := M.structuralHistory_rawTests_mono b s a ⊥ directed lifted squared K history
    pairing unions powers separation collection geometry.actors_ground geometry.carrier_ground supportGround hHistory hLifted witnesses
  let hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, lifted, squared, K, history]
    (Fin.cases geometry.actors_ground (Fin.cases geometry.carrier_ground (Fin.cases nodeOrderGround (Fin.cases supportGround
      (Fin.cases hLifted (Fin.cases hSquared (Fin.cases hK (Fin.cases hHistory (fun j => Fin.elim0 j)))))))))
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted K packed
  let upperAction := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace
  let : ∀ j : Cuts, PartialOrder (lower j) := fun j =>
    M.refinementHistoryPartialOrder c.conditionOrder_code lifted j.val (graphRestriction j.val packed)
  let restrictions : ∀ j : Cuts, SetMembers Q →o lower j := fun j =>
    (historyRun).restriction standard.1.1 j.property.2.1 j.property.2.2 c.conditionOrder_code
  let inclusions : ∀ j : Cuts, lower j ↪o SetMembers Q := fun j =>
    (historyRun).inclusion standard.1.1 j.property.2.1 j.property.2.2 pairing unions powers separation infinite choice
      hK hPacked hLifted j.property.1 carrier (c.encode ⊤) topMem topRows mono c.conditionOrder_code
  let projections : ∀ j, CompleteProjection (restrictions j) (inclusions j) := fun j =>
    M.semanticStructuralTrace_completeProjection c act b s a ⊥ directed lifted squared (c.encode ⊤) pairing unions powers separation collection carrier forcingOrderGround forcingActionGround geometry.actors_ground geometry.carrier_ground nodeOrderGround nodeActionGround nodeMapsGround supportGround hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hK hHistory standard.1.1 trace j.val j.property.1
      j.property.2.1 j.property.2.2 infinite choice
  let upperPres := SetMembers.presentation Q
  let F := a.principalSupportFamily ⊥ directed
  let := M.refinementHistoryOrderTop c.conditionOrder_code lifted K packed
    historyRun.carriers standard.1.1 carrier (c.encode ⊤) topMem topRows
  let validUpper := M.refinementHistoryRowNameFamily_valid c historyRun.carriers
    standard.1.1 carrier lifted valid1
  have conditions := standard.to_conditions pairing unions powers separation hK
  have nodeSize : GroundBelow M s.carrier K :=
    (run.finalGeometry_below i₀ choice hK standard indices).1
  have hPositions := M.nonbottom_carrier_mem s separation geometry.carrier_ground
  have positionSize : GroundBelow M s.nonbottom.carrier K :=
    nodeSize.restrict separation hPositions hK (fun z member => (s.mem_nonbottom_carrier z).1 member |>.1)
  have columnSize := conditions.groundOmegaOne_below pairing unions powers separation collection infinite hK
  have rowSize : GroundBelow M c.carrier K :=
    GroundBelow.binaryRowCarrier pairing unions powers separation hPositions hColumns hK
      conditions positionSize columnSize
  have liftedSize : GroundBelow M lifted K := M.pairEmpty_renamedFamily_below c
    pairing unions powers separation collection carrier ground hK valid below
  obtain ⟨_carrierEq, chosen⟩ := final
  intro p
  obtain ⟨H, hp, coded, ordinary, symmetricGeneric, projectedGeneric, includes, zf, reflection⟩ := chosen p
  refine ⟨H, hp, coded, ordinary, symmetricGeneric, projectedGeneric, includes, zf, reflection, ?_⟩
  intro tau symmetric validity
  apply fulfilled.structural_refinement_quotient_injection collection infinite choice labels small smallD
    irreflexive columns hColumns hmu cardinal.1 valid hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 K history hK hHistory standard.1.1 trace standard rowSize liftedSize H ordinary
    _ tau symmetric validity
  intro beta member
  exact projectedGeneric ⟨beta, M.transitive hK member,
    ordinalSetProperty_member standard.1.1 member, (And.left standard.1.1) beta member⟩






end PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment

end OAI
end

theorem solution.{u, v} : type_of% @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_rowSemanticQuotientInjectionModel_oai.{u, v} := @OAI.PartitionPilot.Forcing.GroundMainPrefix.FinalSupportFulfillment.exists_rowSemanticQuotientInjectionModel_oai.{u, v}
