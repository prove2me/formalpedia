-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:28:30.480336+00:00
-- url     : https://prove2.me/submissions/e21e0b9f-3ea1-4303-8523-8a8fbca2040e

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
import Definitions.Def_OAIQ253P010
import Definitions.Def_OAIQ253P011

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

namespace FunctionGraphOn

theorem empty : FunctionGraphOn (∅ : ZFSet.{u}) ∅ :=
  ⟨∅, ZFSet.empty_subset _, fun x hx => False.elim (ZFSet.notMem_empty x hx)⟩

end FunctionGraphOn

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



namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u
variable {G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P)

theorem entry_orbitPairGraph (tuple tau sigma : Name s) (p : P) :
    Entry sigma (orbitPairGraph a s tuple tau) p ↔
      ∃ g : G, orderedPair ⊤ (a.act s g tuple) (a.act s g tau) = sigma ∧ p = ⊤ := by
  rw [orbitPairGraph, entry_assemble]
  exact exists_congr (fun _ => and_congr_right (fun _ => eq_comm))

theorem mem_eval_orbitPairGraph (tuple tau : Name s) (H : Set P) (topMember : (⊤ : P) ∈ H)
    (z : ZFSet.{u}) :
    z ∈ eval H (orbitPairGraph a s tuple tau) ↔
      ∃ g : G, ZFSet.pair (eval H (a.act s g tuple)) (eval H (a.act s g tau)) = z := by
  rw [mem_eval]
  constructor
  · rintro ⟨sigma, p, entry, _hp, equal⟩
    obtain ⟨g, rfl, rfl⟩ := (entry_orbitPairGraph a s tuple tau sigma p).1 entry
    exact ⟨g, (eval_orderedPair H ⊤ topMember _ _).symm.trans equal⟩
  · rintro ⟨g, equal⟩
    exact ⟨orderedPair ⊤ (a.act s g tuple) (a.act s g tau), ⊤,
      (entry_orbitPairGraph a s tuple tau _ ⊤).2 ⟨g, rfl, rfl⟩,
      topMember, (eval_orderedPair H ⊤ topMember _ _).trans equal⟩

private theorem act_pair (g : G) (x y : Name s) :
    a.act s g (orderedPair ⊤ x y) = orderedPair ⊤ (a.act s g x) (a.act s g y) := by
  change rename s (a.iso g) (orderedPair ⊤ x y) = _
  rw [rename_orderedPair, (a.iso g).map_top]
  rfl

theorem act_orbitPairGraph (tuple tau : Name s) (g : G) :
    a.act s g (orbitPairGraph a s tuple tau) = orbitPairGraph a s tuple tau := by
  apply Name.ext
  intro sigma p
  change Entry sigma (rename s (a.iso g) (orbitPairGraph a s tuple tau)) p ↔ _
  rw [entry_rename, entry_orbitPairGraph]
  constructor
  · rintro ⟨nu, q, entry, equal, condition⟩
    obtain ⟨h, rfl, rfl⟩ := (entry_orbitPairGraph a s tuple tau nu q).1 entry
    change a.act s g (orderedPair ⊤ (a.act s h tuple) (a.act s h tau)) = sigma at equal
    rw [act_pair, ← a.act_mul, ← a.act_mul] at equal
    exact ⟨g * h, equal, condition.symm.trans (a.iso g).map_top⟩
  · rintro ⟨h, rfl, rfl⟩
    refine ⟨orderedPair ⊤ (a.act s (g⁻¹ * h) tuple) (a.act s (g⁻¹ * h) tau), ⊤,
      (entry_orbitPairGraph a s tuple tau _ ⊤).2 ⟨g⁻¹ * h, rfl, rfl⟩, ?_, (a.iso g).map_top⟩
    change a.act s g (orderedPair ⊤ (a.act s (g⁻¹ * h) tuple) (a.act s (g⁻¹ * h) tau)) = _
    rw [act_pair, ← a.act_mul, ← a.act_mul, mul_inv_cancel_left]

theorem orbitPairGraph_hs (F : NormalSubgroupFamily G) (tuple tau : Name s)
    (tupleHS : HereditarilySymmetric a s F tuple) (tauHS : HereditarilySymmetric a s F tau) :
    HereditarilySymmetric a s F (orbitPairGraph a s tuple tau) := by
  apply HereditarilySymmetric.mk (F.upward F.top ?_) ?_
  · intro g _
    exact act_orbitPairGraph a s tuple tau g
  · intro sigma p entry
    obtain ⟨g, rfl, _⟩ := (entry_orbitPairGraph a s tuple tau sigma p).1 entry
    exact (tupleHS.translated g).orderedPair (tauHS.translated g)

end PartitionPilot.Forcing.Name



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

theorem codedFamily_of_code {E : Set P} (code : s.subset E ∈ M.sets) : E ∈ M.codedFamily s := by
  refine ⟨s.subset E, code, ?_⟩
  apply Set.ext
  intro p
  exact s.encode_mem_subset E p

theorem generic_meets_coded_dense [Preorder P] (H : ConditionFilter P)
    (generic : H.GenericFor (M.codedFamily s)) {E : Set P}
    (code : s.subset E ∈ M.sets) (dense : Dense E) : H.Meets E :=
  generic E (M.codedFamily_of_code s code) dense

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

theorem mem_eval_indexedTuple (H : Set P) (one : P) (hone : one ∈ H)
    (I : ZFSet.{u}) (names : I.toSet → Name s) (z : ZFSet.{u}) :
    z ∈ eval H (indexedTuple one I names) ↔
      ∃ i : I, ZFSet.pair i.val (eval H (names i)) = z := by
  rw [indexedTuple, mem_eval_assemble]
  simp only [hone, true_and, eval_orderedPair H one hone, eval_check H one hone]

theorem pair_mem_eval_indexedTuple (H : Set P) (one : P) (hone : one ∈ H)
    (I : ZFSet.{u}) (names : I.toSet → Name s) (i : I.toSet) (x : ZFSet.{u}) :
    ZFSet.pair i.val x ∈ eval H (indexedTuple one I names) ↔ eval H (names i) = x := by
  rw [mem_eval_indexedTuple H one hone]
  constructor
  · rintro ⟨j, eq⟩
    have ji : j = i := Subtype.ext (ZFSet.pair_inj.1 eq).1
    subst j
    exact (ZFSet.pair_inj.1 eq).2
  · intro eq
    exact ⟨i, congrArg (ZFSet.pair i.val) eq⟩

theorem eval_indexedTuple_eq_iff (H : Set P) (one : P) (hone : one ∈ H)
    (I : ZFSet.{u}) (names other : I.toSet → Name s) :
    eval H (indexedTuple one I names) = eval H (indexedTuple one I other) ↔
      ∀ i, eval H (names i) = eval H (other i) := by
  constructor
  · intro eq i
    have entry := (pair_mem_eval_indexedTuple H one hone I other i _).2 rfl
    rw [← eq] at entry
    exact (pair_mem_eval_indexedTuple H one hone I names i _).1 entry
  · intro eq
    apply ZFSet.ext
    intro z
    rw [mem_eval_indexedTuple H one hone, mem_eval_indexedTuple H one hone]
    exact exists_congr (fun i => by rw [eq i])

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRefinementPairClassGraphs
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
namespace GroundDefinableFunction
variable {M : TransitiveGround.{u}} {n : Nat}
variable {f : (Fin (n + 1) → ZFSet.{u}) → ZFSet.{u}}

theorem pair_mem_graph (defined : GroundDefinableFunction M f)
    (params : Fin n → ZFSet.{u}) (A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ defined.graph params A ↔ x ∈ A ∧ y = f (extend x params) := by
  rw [mem_graph]
  constructor
  · rintro ⟨w, hw, equal⟩
    obtain ⟨rfl, value⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hw, value⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem graph_function (defined : GroundDefinableFunction M f)
    (params : Fin n → ZFSet.{u}) (A : ZFSet.{u}) :
    FunctionGraphOn A (defined.graph params A) := by
  have equal : ZFSet.range (fun x : A => x.val) = A := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨w, equal⟩
      exact equal ▸ w.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  simpa only [graph, equal] using familyCodeGraph_function (fun x : A => x.val)
    (fun x => f (extend x.val params)) Subtype.val_injective

end GroundDefinableFunction
end




section
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
include pairing unions powers separation collection carrier group maps

private theorem orbitCodeEntry_meaning (W O y : ZFSet.{u}) (hy : y ∈ M.sets) :
    Realize M.sets orbitCodeEntryFormula
      (extend y (extend W (extend O (extend s.carrier (extend t.carrier
        (extend (a.conditionMapFamily s t) Fin.elim0)))))) ↔
      y ∈ a.orbitCodes s (M.nameDomain s) W := by
  rw [orbitCodeEntryFormula, realize_ex]
  constructor
  · rintro ⟨z, hz, relation⟩
    simp only [realize_binaryApplication, map_extend, map_empty] at relation
    change Realize M.sets orbitImageFormula (extend z (extend y (orbitParameters a s t W))) at relation
    obtain ⟨g, sigma, member, _shape, value⟩ :=
      (M.realize_orbitImageFormula a s t pairing unions powers separation collection carrier group maps
        W z y hz hy).1 relation
    exact (a.mem_orbitCodes s (M.nameDomain s) W y).2 ⟨g, sigma.val, sigma.property, member, value⟩
  · intro member
    obtain ⟨g, sigma, ground, inW, value⟩ := (a.mem_orbitCodes s (M.nameDomain s) W y).1 member
    let z := ZFSet.pair (t.encode g) sigma.val
    have hz : z ∈ M.sets := M.orderedPair_mem pairing (M.transitive group (t.encode_mem g)) ground
    refine ⟨z, hz, ?_⟩
    simp only [realize_binaryApplication, map_extend, map_empty]
    change Realize M.sets orbitImageFormula (extend z (extend y (orbitParameters a s t W)))
    exact (M.realize_orbitImageFormula a s t pairing unions powers separation collection carrier group maps
      W z y hz hy).2 ⟨g, ⟨sigma, ground⟩, inW, rfl, value⟩

private theorem orbitCodeEquality_meaning (W O : ZFSet.{u}) (hW : W ∈ M.sets) (hO : O ∈ M.sets) :
    Realize M.sets orbitCodeEqualityFormula
      (extend W (extend O (extend s.carrier (extend t.carrier
        (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      O = a.orbitCodes s (M.nameDomain s) W := by
  have ground := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW
  exact M.realize_exactSetFormula 1 orbitCodeEntryFormula _ hO
    (fun z member => M.transitive ground member)
    (fun z hz => orbitCodeEntry_meaning M a s t pairing unions powers separation collection carrier group maps W O z hz)

private theorem orbitCodeFamilyPair_meaning (W z : ZFSet.{u}) (hW : W ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets orbitCodeFamilyPairFormula
      (extend W (extend z (extend s.carrier (extend t.carrier
        (extend (a.conditionMapFamily s t) Fin.elim0))))) ↔
      z = ZFSet.pair W (a.orbitCodes s (M.nameDomain s) W) := by
  rw [orbitCodeFamilyPairFormula, realize_ex]
  constructor
  · rintro ⟨O, hO, equality, pair⟩
    simp only [realize_binaryApplication, map_extend, map_empty] at equality
    change Realize M.sets orbitCodeEqualityFormula
      (extend W (extend O (extend s.carrier (extend t.carrier
        (extend (a.conditionMapFamily s t) Fin.elim0))))) at equality
    have value := (orbitCodeEquality_meaning M a s t pairing unions powers separation collection
      carrier group maps W O hW hO).1 equality
    have shape := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hW hO).1 pair
    exact shape.trans (congrArg (ZFSet.pair W) value)
  · intro equal
    have hO := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW
    refine ⟨a.orbitCodes s (M.nameDomain s) W, hO, ?_, ?_⟩
    · simp only [realize_binaryApplication, map_extend, map_empty]
      change Realize M.sets orbitCodeEqualityFormula
        (extend W (extend (a.orbitCodes s (M.nameDomain s) W) (extend s.carrier
          (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0)))))
      exact (orbitCodeEquality_meaning M a s t pairing unions powers separation collection
        carrier group maps W _ hW hO).2 rfl
    · exact (M.realize_orderedPairFormula pairing 2 1 0 _ hz hW hO).2 equal

omit pairing unions powers separation collection carrier group maps in
theorem mem_orbitCodeFamily (F z : ZFSet.{u}) :
    z ∈ M.orbitCodeFamily a s F ↔ ∃ W ∈ F, z = ZFSet.pair W (a.orbitCodes s (M.nameDomain s) W) := by
  rw [orbitCodeFamily, mem_familyCodeGraph]
  constructor
  · rintro ⟨W, equal⟩
    exact ⟨W.val, W.property, equal.symm⟩
  · rintro ⟨W, member, equal⟩
    exact ⟨⟨W, member⟩, equal.symm⟩

omit pairing unions powers separation collection carrier group maps in
theorem orbitCodeFamily_function (F : ZFSet.{u}) : FunctionGraphOn F (M.orbitCodeFamily a s F) := by
  have domain : ZFSet.range (fun W : F => W.val) = F := by
    apply ZFSet.ext
    intro W
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨V, rfl⟩
      exact V.property
    · intro member
      exact ⟨⟨W, member⟩, rfl⟩
  simpa only [orbitCodeFamily, domain] using familyCodeGraph_function (fun W : F => W.val)
    (fun W => a.orbitCodes s (M.nameDomain s) W.val) Subtype.val_injective

theorem orbitCodeFamily_mem {F : ZFSet.{u}} (hF : F ∈ M.sets) : M.orbitCodeFamily a s F ∈ M.sets := by
  let params := extend s.carrier (extend t.carrier (extend (a.conditionMapFamily s t) Fin.elim0))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases carrier (Fin.cases group (Fin.cases maps (fun j => Fin.elim0 j)))
  apply M.definable_image_mem separation collection orbitCodeFamilyPairFormula params members hF
  · intro z member
    obtain ⟨W, inF, rfl⟩ := (M.mem_orbitCodeFamily a s F z).1 member
    have hW := M.transitive hF inF
    exact M.orderedPair_mem pairing hW
      (M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW)
  · intro z hz
    rw [M.mem_orbitCodeFamily]
    exact exists_congr (fun W => and_congr_right (fun inF =>
      (orbitCodeFamilyPair_meaning M a s t pairing unions powers separation collection
        carrier group maps W z (M.transitive hF inF) hz).symm))
  · intro W inF y hy z hz first second
    exact ((orbitCodeFamilyPair_meaning M a s t pairing unions powers separation collection
      carrier group maps W y (M.transitive hF inF) hy).1 first).trans
      ((orbitCodeFamilyPair_meaning M a s t pairing unions powers separation collection
        carrier group maps W z (M.transitive hF inF) hz).1 second).symm

end TransitiveGround
end



open SetRealization SetFormula
universe u


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



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem exists_groundNameSupportChoice
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z)
    (symmetric : ∀ tau : Name s, tau.val ∈ W →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau) :
    ∃ f ∈ M.sets, ZFSet.IsFunc W b.carrier f ∧
      ∀ (tau : Name s) (D : L), ZFSet.pair tau.val (b.encode D) ∈ f →
        tau.val ∈ W ∧ d.principalFix D ≤ a.stabilizer s tau := by
  let params := extend s.carrier (extend t.carrier (extend (supportBasisCode b t d.principalFix)
    (extend (a.conditionMapFamily s t) Fin.elim0)))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases carrier (Fin.cases group (Fin.cases supports (Fin.cases maps (fun j => Fin.elim0 j))))
  let relation := M.definableRelation nameSupportFormula params W b.carrier
  have ground : relation ∈ M.sets :=
    M.definableRelation_mem pairing unions powers separation nameSupportFormula params members hW nodes
  have meaning (tau : Name s) (member : tau.val ∈ W) (D : L) :
      Realize M.sets nameSupportFormula (extend tau.val (extend (b.encode D) params)) ↔
        d.principalFix D ≤ a.stabilizer s tau :=
    M.realize_nameSupportFormula a s t b d.principalFix pairing unions powers separation collection
      carrier group supports maps D (M.transitive nodes (b.encode_mem D)) tau (M.transitive hW member)
  have total : ∀ z ∈ W, ∃ v ∈ b.carrier, ZFSet.pair z v ∈ relation := by
    intro z member
    let tau : Name s := ⟨z, valid z member⟩
    obtain ⟨D, supported⟩ := (symmetric tau member).symmetric
    exact ⟨b.encode D, b.encode_mem D,
      (M.pair_mem_definableRelation nameSupportFormula params W b.carrier z (b.encode D)).2
        ⟨member, b.encode_mem D, (meaning tau member D).2 supported⟩⟩
  obtain ⟨f, hf, function, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hW nodes ground total
  refine ⟨f, hf, function, ?_⟩
  intro tau D entry
  have chosen := (M.pair_mem_definableRelation nameSupportFormula params W b.carrier
    tau.val (b.encode D)).1 (selected entry)
  exact ⟨chosen.1, (meaning tau chosen.1 D).1 chosen.2.2⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace BoundedFormula

private theorem coveringPosition_meaning (D f I r mu : ZFSet.{u}) :
    Truth coveringPositionFormula ![D, f, I, r, mu] ↔
      (f = ∅ ∧ ∀ v ∈ I, ¬ ZFSet.pair v D ∈ r) ∨
      (ZFSet.IsFunc mu I f ∧ (∀ i v, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ r) ∧
        ∀ v ∈ I, ZFSet.pair v D ∈ r → ∃ i ∈ mu, ZFSet.pair i v ∈ f) := by
  simp only [coveringPositionFormula, truth_disj, Truth, truth_emptyFormula,
    truth_functionFormula, truth_imp, truth_pairMembershipFormula, truth_exMem]
  change (f = ∅ ∧ ∀ v ∈ I, ¬ ZFSet.pair v D ∈ r) ∨
    (ZFSet.IsFunc mu I f ∧ (∀ i ∈ mu, ∀ v ∈ I, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ r) ∧
      ∀ v ∈ I, ZFSet.pair v D ∈ r → ∃ i ∈ mu, ZFSet.pair i v ∈ f) ↔ _
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨function, bounds, onto⟩
    exact ⟨function, fun i v entry => bounds i (ZFSet.pair_mem_prod.1 (function.1 entry)).1
      v (ZFSet.pair_mem_prod.1 (function.1 entry)).2 entry, onto⟩
  · rintro ⟨function, bounds, onto⟩
    exact ⟨function, fun i _ v _ entry => bounds i v entry, onto⟩
end BoundedFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (b : Presentation L)

theorem exists_groundCoveringRowPositions
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (nodes : b.carrier ∈ M.sets) (order : b.conditionOrder ∈ M.sets)
    (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu)
    (small : M.groundEmbeddable b.nonbottom.carrier mu) :
    let S := M.rowPositionSequences b.carrier b.conditionOrder b.nonbottom.carrier mu
    ∃ selected ∈ M.sets, ZFSet.IsFunc b.carrier S selected ∧
      ∀ (D : L) f, ZFSet.pair (b.encode D) f ∈ selected →
        f ∈ S ∧ ∃ delta, (delta = ∅ ∨ delta = mu) ∧ FunctionGraphOn delta f ∧
          (∀ i v, ZFSet.pair i v ∈ f → v ∈ b.nonbottom.carrier ∧ ZFSet.pair v (b.encode D) ∈ b.conditionOrder) ∧
          ∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i ∈ delta, ZFSet.pair i (b.encode v) ∈ f := by
  intro S
  have hI := M.nonbottom_carrier_mem b separation nodes
  have hS := M.rowPositionSequences_mem pairing unions powers separation nodes order hI hmu
  let params := extend b.nonbottom.carrier (extend b.conditionOrder (extend mu Fin.elim0))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hI (Fin.cases order (Fin.cases hmu (fun j => Fin.elim0 j)))
  let formula := BoundedFormula.coveringPositionFormula.toFormula
  let relation := M.definableRelation formula params b.carrier S
  have hRelation := M.definableRelation_mem pairing unions powers separation formula params members nodes hS
  have meaning (D f : ZFSet.{u}) (hD : D ∈ M.sets) (hf : f ∈ M.sets) :
      Realize M.sets formula (extend D (extend f params)) ↔
      (f = ∅ ∧ ∀ v ∈ b.nonbottom.carrier, ¬ ZFSet.pair v D ∈ b.conditionOrder) ∨
      (ZFSet.IsFunc mu b.nonbottom.carrier f ∧
        (∀ i v, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ b.conditionOrder) ∧
        ∀ v ∈ b.nonbottom.carrier, ZFSet.pair v D ∈ b.conditionOrder →
          ∃ i ∈ mu, ZFSet.pair i v ∈ f) := by
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hD (Fin.cases hf members))]
    exact BoundedFormula.coveringPosition_meaning D f b.nonbottom.carrier b.conditionOrder mu
  have total : ∀ D ∈ b.carrier, ∃ f ∈ S, ZFSet.pair D f ∈ relation := by
    intro D hD
    let ideal := ZFSet.sep (fun v => ZFSet.pair v D ∈ b.conditionOrder) b.nonbottom.carrier
    have hDM := M.transitive nodes hD
    have hIdeal : ideal ∈ M.sets := by
      have selected := M.bounded_separation_mem separation
        (BoundedFormula.pairMembershipFormula 0 1 2) (extend D (extend b.conditionOrder Fin.elim0))
        (Fin.cases hDM (Fin.cases order (fun j => Fin.elim0 j))) hI
      simp only [BoundedFormula.truth_pairMembershipFormula] at selected
      exact selected
    by_cases inhabited : ideal.Nonempty
    · have idealSmall : M.groundEmbeddable ideal mu := by
        obtain ⟨f, hf, inject⟩ := small
        exact ⟨ZFSet.sep (fun z => z ∈ ZFSet.prod ideal mu) f,
          M.injection_restriction_mem separation hIdeal hmu hf,
          inject.restrict (fun _ h => (ZFSet.mem_sep.1 h).1)⟩
      obtain ⟨f, hf, function, onto⟩ := M.groundEmbeddable_enumeration pairing unions powers separation hIdeal hmu inhabited idealSmall
      have retarget : ZFSet.IsFunc mu b.nonbottom.carrier f :=
        ⟨fun z hz => by
          obtain ⟨i, hi, v, hv, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
          exact ZFSet.pair_mem_prod.2 ⟨hi, (ZFSet.mem_sep.1 hv).1⟩, function.2⟩
      have bounds : ∀ i v, ZFSet.pair i v ∈ f → ZFSet.pair v D ∈ b.conditionOrder :=
        fun _ _ h => (ZFSet.mem_sep.1 (ZFSet.pair_mem_prod.1 (function.1 h)).2).2
      have code : RowPositionSequenceCode b.carrier b.conditionOrder b.nonbottom.carrier mu f :=
        ⟨mu, ZFSet.mem_insert _ _, retarget, D, hD, bounds⟩
      have inS := (M.mem_rowPositionSequences ordinal).2 ⟨hf, code⟩
      exact ⟨f, inS, (M.pair_mem_definableRelation formula params b.carrier S D f).2
        ⟨hD, inS, (meaning D f hDM hf).2 (Or.inr ⟨retarget, bounds,
          fun v hv below => onto v (ZFSet.mem_sep.2 ⟨hv, below⟩)⟩)⟩⟩
    · have empty := M.empty_mem ⟨b.carrier, nodes⟩
      have inS : (∅ : ZFSet.{u}) ∈ S := M.empty_mem_rowPositionSequences hmu ordinal ⟨D, hD⟩
      exact ⟨∅, inS, (M.pair_mem_definableRelation formula params b.carrier S D ∅).2
        ⟨hD, inS, (meaning D ∅ hDM empty).2 (Or.inl ⟨rfl,
          fun v hv below => inhabited ⟨v, ZFSet.mem_sep.2 ⟨hv, below⟩⟩⟩)⟩⟩
  obtain ⟨selected, hSelected, function, included⟩ := M.uniformize_relation pairing unions powers separation choice
    nodes hS hRelation total
  refine ⟨selected, hSelected, function, ?_⟩
  intro D f entry
  have chosen := (M.pair_mem_definableRelation formula params b.carrier S (b.encode D) f).1 (included entry)
  refine ⟨chosen.2.1, ?_⟩
  have truth := (meaning (b.encode D) f (M.transitive nodes (b.encode_mem D))
    (M.transitive hS chosen.2.1)).1 chosen.2.2
  have nonbottom (v : L) (h : v ≠ ⊥) : b.encode v ∈ b.nonbottom.carrier :=
    (b.nonbottom.mem_carrier _).2 ⟨⟨v, h⟩, rfl⟩
  rcases truth with ⟨rfl, none⟩ | ⟨func, bounds, onto⟩
  · exact ⟨∅, Or.inl rfl, FunctionGraphOn.empty,
      fun i v entry => (ZFSet.notMem_empty _ entry).elim,
      fun v hv below => (none _ (nonbottom v hv) ((b.pair_mem_conditionOrder v D).2 below)).elim⟩
  · exact ⟨mu, Or.inr rfl, ⟨b.nonbottom.carrier, func⟩,
      fun i v entry => ⟨(ZFSet.pair_mem_prod.1 (func.1 entry)).2, bounds i v entry⟩,
      fun v hv below => onto _ (nonbottom v hv) ((b.pair_mem_conditionOrder v D).2 below)⟩

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

end TransitiveGround

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L) (C : ZFSet.{u})
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem exists_groundSupportTupleFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (order : b.conditionOrder ∈ M.sets) (hC : C ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu)
    (small : M.groundEmbeddable b.nonbottom.carrier mu)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) (valid : ∀ z ∈ W, IsName s z)
    (symmetric : ∀ tau : Name s, tau.val ∈ W →
      HereditarilySymmetric a s (d.principalSupportFamily ⊥ directed) tau) :
    letI := M.smallFunctionOrder (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨b.carrier, nodes⟩
    let rows := M.binaryRowNameGraph b.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences b.carrier b.conditionOrder b.nonbottom.carrier mu
    let T := rowTupleTerms (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
      (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu b.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∃ supportChoice ∈ M.sets, ∃ positionChoice ∈ M.sets, ∃ tupleChoice ∈ M.sets,
      ZFSet.IsFunc W b.carrier supportChoice ∧ ZFSet.IsFunc b.carrier S positionChoice ∧
      ZFSet.IsFunc W T tupleChoice ∧
      ∀ (tau : Name s) z, ZFSet.pair tau.val z ∈ tupleChoice →
        ∃ D : L, ∃ f ∈ S,
          ZFSet.pair tau.val (b.encode D) ∈ supportChoice ∧
          ZFSet.pair (b.encode D) f ∈ positionChoice ∧
          d.principalFix D ≤ a.stabilizer s tau ∧
          ∃ delta ∈ M.sets, ordinalSetProperty delta ∧ delta ⊆ mu ∧
          ∃ function : FunctionGraphOn delta f, ∃ positions : delta.toSet → {v : L // v ≠ ⊥},
            (∀ i, function.value i = b.encode (positions i).val) ∧
            (∀ i, (positions i).val ≤ D) ∧
            (∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i, (positions i).val = v) ∧
            z = (M.internalRowTupleName b C nodes delta positions).val := by
  let := M.smallFunctionOrder (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨b.carrier, nodes⟩
  intro rows S T
  have hI := M.nonbottom_carrier_mem b separation nodes
  have hS := M.rowPositionSequences_mem pairing unions powers separation nodes order hI hmu
  let tuples := rowTupleFamily (SetMembers.raw (⊤ : SetMembers (M.smallPartialFunctions
    (ZFSet.prod b.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) mu b.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
  have hTuples : tuples ∈ M.sets := M.binaryRowTupleFamily_mem pairing unions powers separation collection infinite
    nodes order hI hC hmu ⊤
  have hT : T ∈ M.sets := M.rowTupleTerms_mem unions separation hS hTuples
  have tupleFunction : ZFSet.IsFunc S T tuples := rowTupleTerms_function _ _ _ _ _ _
  obtain ⟨supportChoice, hSupport, supportFunction, supported⟩ := M.exists_groundNameSupportChoice
    a s t b d ⊥ directed pairing unions powers separation collection choice carrier group nodes
    supports maps W hW valid symmetric
  obtain ⟨positionChoice, hPosition, positionFunction, positionValues⟩ := M.exists_groundCoveringRowPositions
    b pairing unions powers separation choice nodes order mu hmu ordinal small
  let positionForName := relationCompose W b.carrier S supportChoice positionChoice
  have hPositionForName : positionForName ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hW nodes hS hSupport hPosition
  have positionForNameFunction : ZFSet.IsFunc W S positionForName :=
    relationCompose_function_of_subset supportFunction positionFunction (fun _ h => h)
  let tupleChoice := relationCompose W S T positionForName tuples
  have hTupleChoice : tupleChoice ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hW hS hT hPositionForName hTuples
  refine ⟨supportChoice, hSupport, positionChoice, hPosition, tupleChoice, hTupleChoice,
    supportFunction, positionFunction,
    relationCompose_function_of_subset positionForNameFunction tupleFunction (fun _ h => h), ?_⟩
  intro tau z entry
  obtain ⟨_, _, f, hf, namePosition, tupleEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
  obtain ⟨_, _, v, hv, supportEntry, positionEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 namePosition
  obtain ⟨D, rfl⟩ := (b.mem_carrier v).1 hv
  obtain ⟨_, delta, domain, function, bounds, onto⟩ := positionValues D f positionEntry
  have hDelta : delta ∈ M.sets := domain.elim (fun equal => equal.symm ▸ M.empty_mem ⟨mu, hmu⟩)
    (fun equal => equal.symm ▸ hmu)
  have deltaOrdinal : ordinalSetProperty delta := domain.elim
    (fun equal => equal.symm ▸ ordinalSetProperty_empty) (fun equal => equal.symm ▸ ordinal)
  have subset : delta ⊆ mu := domain.elim
    (fun equal => equal.symm ▸ ZFSet.empty_subset mu) (fun equal => equal.symm ▸ (fun _ h => h))
  have each (i : delta.toSet) : ∃ v : {v : L // v ≠ ⊥}, b.encode v.val = function.value i :=
    (b.nonbottom.mem_carrier _).1 (bounds i.val (function.value i) (function.value_entry i)).1
  let positions (i : delta.toSet) := Classical.choose (each i)
  have values (i : delta.toSet) : function.value i = b.encode (positions i).val :=
    (Classical.choose_spec (each i)).symm
  have bounded (i : delta.toSet) : (positions i).val ≤ D := by
    have bound := (bounds i.val (function.value i) (function.value_entry i)).2
    rw [values i] at bound
    exact (b.pair_mem_conditionOrder _ _).1 bound
  have covers (v : L) (hv : v ≠ ⊥) (below : v ≤ D) : ∃ i, (positions i).val = v := by
    obtain ⟨i, hi, entry⟩ := onto v hv below
    let j : delta.toSet := ⟨i, hi⟩
    refine ⟨j, b.injective ?_⟩
    exact (values j).symm.trans (function.value_eq_of_entry j entry)
  have code := ((pair_mem_rowTupleFamily _ _ _ _ _ _ f z).1 tupleEntry).2
  have exactTuple := M.internalRowTupleCode_eq b C nodes function subset positions values
  dsimp only at exactTuple
  exact ⟨D, f, hf, supportEntry, positionEntry, (supported tau D supportEntry).2,
    delta, hDelta, deltaOrdinal, subset, function, positions, values, bounded, covers,
    code.trans exactTuple⟩

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




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]

theorem exists_groundOrdinalFixedNameSequence
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets)
    {W f : ZFSet.{u}} (hW : W ∈ M.sets) (hf : f ∈ M.sets)
    (function : FunctionGraphOn W f) (names : ∀ i, IsName s (function.value i))
    (fixed : ∀ g i, a.act s g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩)
    (children : ∀ i, HereditarilySymmetric a s F ⟨function.value i, names i⟩) :
    ∃ I ∈ M.sets, ordinalSetProperty I ∧
      ∃ q ∈ M.sets, ∃ qFunction : FunctionGraphOn I q,
      ∃ qNames : ∀ j, IsName s (qFunction.value j),
        (∀ g j, a.act s g ⟨qFunction.value j, qNames j⟩ = ⟨qFunction.value j, qNames j⟩) ∧
        (∀ j, HereditarilySymmetric a s F ⟨qFunction.value j, qNames j⟩) ∧
        (∀ i : W.toSet, ∃ j : I.toSet,
          (⟨qFunction.value j, qNames j⟩ : Name s) = ⟨function.value i, names i⟩) ∧
        (∀ j : I.toSet, ∃ i : W.toSet,
          (⟨qFunction.value j, qNames j⟩ : Name s) = ⟨function.value i, names i⟩) ∧
        ∀ H : ConditionFilter P,
          let sequence := Name.indexedGraphName ⊤ qFunction qNames
          sequence.val ∈ M.sets ∧ HereditarilySymmetric a s F sequence ∧
          ZFSet.IsFunc I (ZFSet.range (fun j : I => Name.eval {p | H.mem p}
            ⟨qFunction.value j, qNames j⟩)) (Name.eval {p | H.mem p} sequence) ∧
          Name.eval {p | H.mem p} sequence ∈ (M.symmetricExtension s a F H).sets := by
  obtain ⟨I, hI, enumeration, hEnumeration, ordinal, injection, onto⟩ :=
    M.exists_groundOrdinalEnumeration pairing unions powers separation collection choice hW
  let V := functionGraphRange W f
  have hV : V ∈ M.sets := M.functionGraphRange_mem unions separation hW hf
  let q := relationCompose I W V enumeration f
  have hq : q ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hI hW hV hEnumeration hf
  have qFunction : FunctionGraphOn I q := ⟨V, relationCompose_function_of_subset
    injection.1 (functionGraphRange_function function) (fun _ h => h)⟩
  have each (j : I.toSet) : ∃ i : W.toSet, qFunction.value j = function.value i := by
    obtain ⟨_, _, x, hx, _, edge⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 (qFunction.value_entry j)
    exact ⟨⟨x, hx⟩, (function.value_eq_of_entry ⟨x, hx⟩ edge).symm⟩
  let source (j : I.toSet) := Classical.choose (each j)
  have value (j : I.toSet) := Classical.choose_spec (each j)
  have qNames (j : I.toSet) : IsName s (qFunction.value j) := (value j).symm ▸ names (source j)
  have actual (j : I.toSet) : (⟨qFunction.value j, qNames j⟩ : Name s) =
      ⟨function.value (source j), names (source j)⟩ := Subtype.ext (value j)
  have qFixed (g : G) (j : I.toSet) : a.act s g ⟨qFunction.value j, qNames j⟩ = ⟨qFunction.value j, qNames j⟩ := by
    rw [actual j]
    exact fixed g (source j)
  have qChildren (j : I.toSet) : HereditarilySymmetric a s F ⟨qFunction.value j, qNames j⟩ := by
    rw [actual j]
    exact children (source j)
  refine ⟨I, hI, ordinal, q, hq, qFunction, qNames, qFixed, qChildren, ?_,
    (fun j => ⟨source j, actual j⟩), ?_⟩
  · intro i
    obtain ⟨j, hj, enumerated⟩ := onto i.val i.property
    have edge : ZFSet.pair j (function.value i) ∈ q := (pair_mem_relationCompose _ _ _ _ _ _ _).2
      ⟨hj, (mem_functionGraphRange W f _).2 ⟨i.val, i.property, function.value_entry i⟩,
        i.val, i.property, enumerated, function.value_entry i⟩
    exact ⟨⟨j, hj⟩, Subtype.ext (qFunction.value_eq_of_entry ⟨j, hj⟩ edge)⟩
  · intro H sequence
    have package := M.supportedNameSequence_function_mem s a F pairing unions powers separation
      collection carrier hI hq qFunction qNames ⊤ F.top (fun g _ j => qFixed g j) qChildren H
    exact ⟨package.1, package.2.2.1, package.2.2.2.1, package.2.2.2.2⟩

end PartitionPilot.Forcing.TransitiveGround



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

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing.TransitiveGround

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRowTupleEvaluation
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
variable (M : TransitiveGround.{u}) {L : Type u} [PartialOrder L] [OrderBot L]
variable (s : Presentation L) (C : ZFSet.{u}) (hL : s.carrier ∈ M.sets)

theorem internalRowTupleName_eval_eq_iff
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (hC : C ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (δ : ZFSet.{u}) (positions other : δ.toSet → {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      H.GenericFor (M.codedFamily (SetMembers.presentation (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) →
      (Name.eval {p | H.mem p} (M.internalRowTupleName s C hL δ positions) =
        Name.eval {p | H.mem p} (M.internalRowTupleName s C hL δ other) ↔ positions = other) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H generic
  constructor
  · intro eq
    have values := (Name.eval_indexedTuple_eq_iff {p | H.mem p} ⊤ H.top_mem δ
      (fun i => M.internalRowName s C hL (positions i))
      (fun i => M.internalRowName s C hL (other i))).1 eq
    funext i
    apply Subtype.ext
    apply s.injective
    by_contra distinct
    have separated := M.binaryGenericRow_ne pairing unions powers separation infinite choice
      (M.nonbottom_carrier_mem s separation hL) hC
      (s.nonbottom.encode_mem (positions i)) (s.nonbottom.encode_mem (other i))
      distinct uncountable H generic
    apply separated
    have ev := values i
    change Name.eval {p | H.mem p} (M.binaryRowName s.nonbottom.carrier C ⊤
      (s.encode (positions i).val)) = Name.eval {p | H.mem p}
      (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode (other i).val)) at ev
    simpa only [M.eval_binaryRowName s.nonbottom.carrier C ⊤ H H.top_mem,
      Presentation.nonbottom_encode] using ev
  · rintro rfl
    rfl

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundSelectedOrbitNameFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem exists_groundOrbitNameCodeFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (one J : ZFSet.{u}) (hOne : one ∈ M.sets) (hJ : J ∈ M.sets) :
    ∃ family ∈ M.sets, FunctionGraphOn J family ∧
      ∀ sigma z, ZFSet.pair sigma z ∈ family ↔
        sigma ∈ J ∧ z = ZFSet.prod (a.orbitCodes s (M.nameDomain s) {sigma}) {one} := by
  let singleton := (M.definable_singleton pairing).graph Fin.elim0 J
  have singletonFunction : FunctionGraphOn J singleton :=
    (M.definable_singleton pairing).graph_function Fin.elim0 J
  have singletonGround : singleton ∈ M.sets :=
    (M.definable_singleton pairing).graph_mem pairing separation collection Fin.elim0 (fun j => Fin.elim0 j) hJ
  let S := functionGraphRange J singleton
  have hS : S ∈ M.sets := M.functionGraphRange_mem unions separation hJ singletonGround
  let orbits := M.orbitCodeFamily a s S
  have orbitFunction : FunctionGraphOn S orbits := M.orbitCodeFamily_function a s S
  have orbitGround : orbits ∈ M.sets :=
    M.orbitCodeFamily_mem a s t pairing unions powers separation collection carrier group maps hS
  let O := functionGraphRange S orbits
  have hO : O ∈ M.sets := M.functionGraphRange_mem unions separation hS orbitGround
  let topPairs := (orbitTopPairsDefinition M pairing unions powers separation).graph (extend one Fin.elim0) O
  have topFunction : FunctionGraphOn O topPairs :=
    (orbitTopPairsDefinition M pairing unions powers separation).graph_function _ O
  have topGround : topPairs ∈ M.sets :=
    (orbitTopPairsDefinition M pairing unions powers separation).graph_mem pairing separation collection
      (extend one Fin.elim0) (Fin.cases hOne (fun j => Fin.elim0 j)) hO
  let V := functionGraphRange O topPairs
  have hV : V ∈ M.sets := M.functionGraphRange_mem unions separation hO topGround
  let first := relationCompose J S O singleton orbits
  have firstFunction : ZFSet.IsFunc J O first := relationCompose_function_of_subset
    (functionGraphRange_function singletonFunction) (functionGraphRange_function orbitFunction) (fun _ h => h)
  have firstGround : first ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hJ hS hO singletonGround orbitGround
  let family := relationCompose J O V first topPairs
  have function : FunctionGraphOn J family := ⟨V, relationCompose_function_of_subset
    firstFunction (functionGraphRange_function topFunction) (fun _ h => h)⟩
  have ground : family ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hJ hO hV firstGround topGround
  have values (sigma z : ZFSet.{u}) (entry : ZFSet.pair sigma z ∈ family) :
      sigma ∈ J ∧ z = ZFSet.prod (a.orbitCodes s (M.nameDomain s) {sigma}) {one} := by
    obtain ⟨inJ, _, orbit, _, firstEntry, topEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    obtain ⟨_, _, input, _, singletonEntry, orbitEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 firstEntry
    have inputValue := ((M.definable_singleton pairing).pair_mem_graph Fin.elim0 J sigma input).1 singletonEntry |>.2
    have topValue := ((orbitTopPairsDefinition M pairing unions powers separation).pair_mem_graph
      (extend one Fin.elim0) O orbit z).1 topEntry |>.2
    obtain ⟨W, _, pairEqual⟩ := (M.mem_orbitCodeFamily a s S (ZFSet.pair input orbit)).1 orbitEntry
    obtain ⟨rfl, orbitValue⟩ := ZFSet.pair_inj.1 pairEqual
    change input = {sigma} at inputValue
    change z = ZFSet.prod orbit {one} at topValue
    exact ⟨inJ, topValue.trans (congrArg (fun X => ZFSet.prod X {one})
      (orbitValue.trans (congrArg (a.orbitCodes s (M.nameDomain s)) inputValue)))⟩
  refine ⟨family, ground, function, ?_⟩
  intro sigma z
  refine ⟨values sigma z, ?_⟩
  rintro ⟨inJ, equal⟩
  obtain ⟨w, entry⟩ := function.total inJ
  exact ((values sigma w entry).2.trans equal.symm) ▸ entry

end TransitiveGround
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

private theorem selectedImage_value {W T choice tau tuple : ZFSet.{u}}
    (function : ZFSet.IsFunc W T choice) (entry : ZFSet.pair tau tuple ∈ choice) :
    ⋃₀ relationImage {tau} T choice = tuple := by
  have single : relationImage {tau} T choice = {tuple} := by
    apply ZFSet.ext
    intro z
    rw [mem_relationImage, ZFSet.mem_singleton]
    constructor
    · rintro ⟨_, x, hx, edge⟩
      have same := ZFSet.mem_singleton.1 hx
      subst x
      exact (show FunctionGraphOn W choice from ⟨T, function⟩).unique edge entry
    · rintro rfl
      exact ⟨(ZFSet.pair_mem_prod.1 (function.1 entry)).2,
        tau, ZFSet.mem_singleton.2 rfl, entry⟩
  rw [single]
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨X, hX, member⟩
    exact (ZFSet.mem_singleton.1 hX) ▸ member
  · intro member
    exact ⟨tuple, ZFSet.mem_singleton.2 rfl, member⟩

theorem exists_groundSelectedOrbitNameFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (one W T choice : ZFSet.{u}) (hOne : one ∈ M.sets) (hW : W ∈ M.sets)
    (hT : T ∈ M.sets) (hChoice : choice ∈ M.sets) (function : ZFSet.IsFunc W T choice) :
    ∃ family ∈ M.sets, FunctionGraphOn W family ∧
      ∀ tau tuple, ZFSet.pair tau tuple ∈ choice → ∀ z,
        ZFSet.pair tau z ∈ family ↔
          z = ZFSet.prod (a.orbitCodes s (M.nameDomain s) {orderedPairNameCode one tuple tau}) {one} := by
  let params := extend one (extend T (extend choice Fin.elim0))
  let joints := (selectedJointDefinition M pairing unions separation).graph params W
  have jointGround : joints ∈ M.sets :=
    (selectedJointDefinition M pairing unions separation).graph_mem pairing separation collection params
      (Fin.cases hOne (Fin.cases hT (Fin.cases hChoice (fun j => Fin.elim0 j)))) hW
  have jointFunction : FunctionGraphOn W joints :=
    (selectedJointDefinition M pairing unions separation).graph_function params W
  let J := functionGraphRange W joints
  have hJ : J ∈ M.sets := M.functionGraphRange_mem unions separation hW jointGround
  obtain ⟨orbits, hOrbits, orbitFunction, orbitValues⟩ := M.exists_groundOrbitNameCodeFamily
    a s t pairing unions powers separation collection carrier group maps one J hOne hJ
  let O := functionGraphRange J orbits
  have hO : O ∈ M.sets := M.functionGraphRange_mem unions separation hJ hOrbits
  let family := relationCompose W J O joints orbits
  have familyGround : family ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hW hJ hO jointGround hOrbits
  have familyFunction : FunctionGraphOn W family := ⟨O, relationCompose_function_of_subset
    (functionGraphRange_function jointFunction) (functionGraphRange_function orbitFunction) (fun _ h => h)⟩
  have values (tau tuple : ZFSet.{u}) (selected : ZFSet.pair tau tuple ∈ choice)
      (z : ZFSet.{u}) (entry : ZFSet.pair tau z ∈ family) :
      z = ZFSet.prod (a.orbitCodes s (M.nameDomain s) {orderedPairNameCode one tuple tau}) {one} := by
    obtain ⟨_, _, joint, _, jointEntry, orbitEntry⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    have jointValue := ((selectedJointDefinition M pairing unions separation).pair_mem_graph params W tau joint).1 jointEntry |>.2
    change joint = orderedPairNameCode one (⋃₀ relationImage {tau} T choice) tau at jointValue
    rw [selectedImage_value function selected] at jointValue
    exact ((orbitValues joint z).1 orbitEntry).2.trans
      (congrArg (fun x => ZFSet.prod (a.orbitCodes s (M.nameDomain s) {x}) {one}) jointValue)
  refine ⟨family, familyGround, familyFunction, ?_⟩
  intro tau tuple selected z
  refine ⟨values tau tuple selected z, ?_⟩
  intro equal
  obtain ⟨w, entry⟩ := familyFunction.total (ZFSet.pair_mem_prod.1 (function.1 selected)).1
  exact ((values tau tuple selected w entry).trans equal.symm) ▸ entry

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOrdinalPartialMapCovers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]

theorem exists_ordinalPartialMapCover
    (s : Presentation P) (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (carrier : s.carrier ∈ M.sets)
    {W f : ZFSet.{u}} (hW : W ∈ M.sets) (hf : f ∈ M.sets)
    (function : FunctionGraphOn W f) (names : ∀ i, IsName s (function.value i))
    (fixed : ∀ g i, a.act s g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩)
    (children : ∀ i, HereditarilySymmetric a s F ⟨function.value i, names i⟩)
    (H : ConditionFilter P) (Trow X : ZFSet.{u})
    (partialMaps : ∀ i : W.toSet,
      let hi := Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name s)
      PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi)
    (covers : ∀ x ∈ X, ∃ i : W.toSet, ∃ u ∈ Trow,
      ZFSet.pair u x ∈ Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name s)) :
    let N := M.symmetricExtension s a F H
    ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
      ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
        (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi) ∧
        ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
          ∃ u ∈ Trow, ZFSet.pair u x ∈ hi := by
  intro N
  obtain ⟨delta, hDelta, ordinal, q, _hq, qFunction, qNames, _fixed, _children,
    forward, backward, sequences⟩ := M.exists_groundOrdinalFixedNameSequence s a F
      pairing unions powers separation collection choice carrier hW hf function names fixed children
  have sequenceData := sequences H
  dsimp only at sequenceData
  let sequence := Name.indexedGraphName (s := s) (⊤ : P) qFunction qNames
  let h := Name.eval {p | H.mem p} sequence
  have hFunction : FunctionGraphOn delta h := ⟨_, sequenceData.2.2.1⟩
  have groundSubset := M.ground_subset_symmetricExtension s a F
    pairing unions powers separation collection carrier H
  refine ⟨delta, groundSubset hDelta, ordinal, h, sequenceData.2.2.2, hFunction, ?_, ?_⟩
  · intro i hi entry
    let j : delta.toSet := ⟨i, hFunction.pair_source entry⟩
    have value := (Name.pair_mem_eval_indexedTuple {p | H.mem p} (⊤ : P) H.top_mem delta
      (fun j => ⟨qFunction.value j, qNames j⟩) j hi).1 entry
    obtain ⟨k, same⟩ := backward j
    have equal := (congrArg (Name.eval {p | H.mem p}) same).symm.trans value
    exact Eq.mp (congrArg (fun v => PartialFunctionCode Trow (⋃₀ ⋃₀ v) v) equal) (partialMaps k)
  · intro x member
    obtain ⟨i, u, inRow, edge⟩ := covers x member
    obtain ⟨j, same⟩ := forward i
    let hi := Name.eval {p | H.mem p} (⟨qFunction.value j, qNames j⟩ : Name s)
    refine ⟨j.val, j.property, hi,
      (Name.pair_mem_eval_indexedTuple {p | H.mem p} (⊤ : P) H.top_mem delta
        (fun j => ⟨qFunction.value j, qNames j⟩) j hi).2 rfl, u, inRow, ?_⟩
    exact Eq.mpr (congrArg (fun v => ZFSet.pair u x ∈ v)
      (congrArg (Name.eval {p | H.mem p}) same)) edge

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
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

private theorem acted_pair (g : G) (x y : Name s) :
    a.act s g (Name.orderedPair ⊤ x y) = Name.orderedPair ⊤ (a.act s g x) (a.act s g y) := by
  change Name.rename s (a.iso g) (Name.orderedPair ⊤ x y) = _
  rw [Name.rename_orderedPair, (a.iso g).map_top]
  rfl

theorem orbitPairGraph_code_eq (tuple tau : Name s)
    (jointGround : (Name.orderedPair ⊤ tuple tau).val ∈ M.sets) :
    (Name.orbitPairGraph a s tuple tau).val =
      ZFSet.prod (a.orbitCodes s (M.nameDomain s) {(Name.orderedPair ⊤ tuple tau).val})
        {s.encode ⊤} := by
  have orbitMembers (y : ZFSet.{u}) :
      y ∈ a.orbitCodes s (M.nameDomain s) {(Name.orderedPair ⊤ tuple tau).val} ↔
        ∃ g : G, y = (Name.orderedPair ⊤ (a.act s g tuple) (a.act s g tau)).val := by
    rw [a.mem_orbitCodes]
    constructor
    · rintro ⟨g, sigma, _ground, member, equal⟩
      have same : sigma = Name.orderedPair ⊤ tuple tau := Subtype.ext (ZFSet.mem_singleton.1 member)
      rw [same, acted_pair] at equal
      exact ⟨g, equal⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, Name.orderedPair ⊤ tuple tau, jointGround, ZFSet.mem_singleton.2 rfl,
        (congrArg Subtype.val (acted_pair a s g tuple tau)).symm⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨sigma, p, code⟩ := Name.entries_cover (Name.orbitPairGraph a s tuple tau) member
    have entry : Name.Entry sigma (Name.orbitPairGraph a s tuple tau) p := by
      change ZFSet.pair sigma.val (s.encode p) ∈ (Name.orbitPairGraph a s tuple tau).val
      exact code ▸ member
    obtain ⟨g, rfl, rfl⟩ := (Name.entry_orbitPairGraph a s tuple tau sigma p).1 entry
    rw [code, ZFSet.pair_mem_prod]
    exact ⟨(orbitMembers _).2 ⟨g, rfl⟩, ZFSet.mem_singleton.2 rfl⟩
  · intro member
    obtain ⟨x, hx, y, hy, shape⟩ := ZFSet.mem_prod.1 member
    obtain ⟨g, rfl⟩ := (orbitMembers x).1 hx
    have topEq := ZFSet.mem_singleton.1 hy
    rw [topEq] at shape
    have entry := (Name.entry_orbitPairGraph a s tuple tau _ ⊤).2 ⟨g, rfl, rfl⟩
    change ZFSet.pair (Name.orderedPair ⊤ (a.act s g tuple) (a.act s g tau)).val
      (s.encode ⊤) ∈ (Name.orbitPairGraph a s tuple tau).val at entry
    exact shape.symm ▸ entry

end PartitionPilot.Forcing.TransitiveGround



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

theorem internalRowTuple_equal_relativeFix
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (delta : ZFSet.{u}) (positions : delta.toSet → {i : L // i ≠ ⊥}) (D : L)
    (covers : ∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i, (positions i).val = v) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let lower := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))),
      H.GenericFor (M.codedFamily lower) → ∀ g h : G,
      Name.eval {p | H.mem p} (act.act lower g (M.internalRowTupleName s C hL delta positions)) =
        Name.eval {p | H.mem p} (act.act lower h (M.internalRowTupleName s C hL delta positions)) →
      h⁻¹ * g ∈ a.principalFix D := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act lower H generic g h equal
  rw [M.internalRowTupleName_action a s b C pairing unions powers separation infinite hL hC hG graph,
    M.internalRowTupleName_action a s b C pairing unions powers separation infinite hL hC hG graph] at equal
  have coordinates := (M.internalRowTupleName_eval_eq_iff s C hL pairing unions powers separation
    infinite choice hC uncountable delta (fun i => a.nonbottom.iso g (positions i))
      (fun i => a.nonbottom.iso h (positions i)) H generic).1 equal
  intro v below
  by_cases bottom : v = ⊥
  · subst v
    exact (a.iso (h⁻¹ * g)).map_bot
  · obtain ⟨i, atPosition⟩ := covers v bottom below
    have aligned : a.iso g v = a.iso h v := by
      have value := congrArg Subtype.val (congrFun coordinates i)
      change a.iso g (positions i).val = a.iso h (positions i).val at value
      simpa only [atPosition] using value
    rw [a.mul, aligned, a.point_inv_left]

theorem liftedRowOrbit_function
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (delta : ZFSet.{u}) (positions : delta.toSet → {i : L // i ≠ ⊥}) (D : L)
    (covers : ∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i, (positions i).val = v)
    {Upper : Type u} [PartialOrder Upper] [OrderTop Upper]
    (upper : Presentation Upper) (e : PosetAction G Upper) (upperGround : upper.carrier ∈ M.sets) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let lower := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (restriction : Upper →o SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (inclusion : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega) ↪o Upper)
      (_projection : CompleteProjection restriction inclusion),
      upper.graph lower restriction ∈ M.sets →
      (∀ g p, inclusion (act.iso g p) = e.iso g (inclusion p)) →
      ∀ (H : ConditionFilter Upper), H.GenericFor (formulaFamily (M.nameDomain upper)) →
      ∀ (tau : Name upper), a.principalFix D ≤ e.stabilizer upper tau →
      let tuple := Name.rename upper inclusion (M.internalRowTupleName s C hL delta positions)
      ZFSet.IsFunc (ZFSet.range (fun g : G => Name.eval {p | H.mem p} (e.act upper g tuple)))
        (ZFSet.range (fun g : G => Name.eval {p | H.mem p} (e.act upper g tau)))
        (Name.eval {p | H.mem p} (Name.orbitPairGraph e upper tuple tau)) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act lower restriction inclusion projection restrictionGround equivariant H ordinary tau supported tuple
  have lowerGround : lower.carrier ∈ M.sets :=
    M.countablePartialFunctions_mem pairing unions powers separation infinite
      (M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC)
      (M.natSetCode_mem separation infinite 2)
  have generic := M.completeProjection_codedGeneric_of_ordinary upper lower projection
    pairing unions powers separation upperGround lowerGround restrictionGround H ordinary
  have sameTarget (g h : G)
      (equal : Name.eval {p | H.mem p} (e.act upper g tuple) =
        Name.eval {p | H.mem p} (e.act upper h tuple)) : e.act upper g tau = e.act upper h tau := by
    have lowerEqual :
        Name.eval {p | (projection.projectedFilter H).mem p}
          (act.act lower g (M.internalRowTupleName s C hL delta positions)) =
        Name.eval {p | (projection.projectedFilter H).mem p}
          (act.act lower h (M.internalRowTupleName s C hL delta positions)) := by
      change Name.eval {p | H.mem p} (e.act upper g (Name.rename upper inclusion _)) =
        Name.eval {p | H.mem p} (e.act upper h (Name.rename upper inclusion _)) at equal
      rw [act.act_rename_of_equivariant e lower upper inclusion equivariant,
        act.act_rename_of_equivariant e lower upper inclusion equivariant,
        Name.eval_rename, Name.eval_rename] at equal
      exact equal
    have relative := M.internalRowTuple_equal_relativeFix a s b C pairing unions powers separation infinite
      hL hC hG graph choice uncountable delta positions D covers
      (projection.projectedFilter H) generic g h lowerEqual
    have fixed : e.act upper (h⁻¹ * g) tau = tau := supported relative
    have moved := congrArg (e.act upper h) fixed
    rw [← e.act_mul, mul_inv_cancel_left] at moved
    exact moved
  constructor
  · intro z member
    obtain ⟨g, rfl⟩ := (Name.mem_eval_orbitPairGraph e upper tuple tau {p | H.mem p} H.top_mem z).1 member
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨g, rfl⟩, ZFSet.mem_range.2 ⟨g, rfl⟩⟩
  · intro x member
    obtain ⟨g, rfl⟩ := ZFSet.mem_range.1 member
    refine ⟨Name.eval {p | H.mem p} (e.act upper g tau),
      (Name.mem_eval_orbitPairGraph e upper tuple tau {p | H.mem p} H.top_mem _).2 ⟨g, rfl⟩, ?_⟩
    intro y entry
    obtain ⟨h, equal⟩ := (Name.mem_eval_orbitPairGraph e upper tuple tau {p | H.mem p} H.top_mem _).1 entry
    have parts := ZFSet.pair_inj.1 equal
    exact parts.2.symm.trans (congrArg (Name.eval {p | H.mem p}) (sameTarget h g parts.1))

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
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
include order nodeMaps supports choice

theorem semanticBinaryRow_orbit_cover
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu)
    (small : M.groundEmbeddable s.nonbottom.carrier mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (T T2 : ZFSet.{u}) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (act.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (act.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) T T2 level prior) stages history),
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
      (supportBasisCode s b a.principalFix) T T2 stages history
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
      (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) T T2 ordinal trace
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      run.carriers ordinal carrier (c.encode ⊤) topMem topRows
    let upper := SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed T T2 (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace
    let inclusion := M.refinementHistoryRowEmbedding c T stages packed run ordinal carrier
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let RowTerms := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ (W : ZFSet.{u}) (_hW : W ∈ M.sets) (validW : ∀ z ∈ W, IsName upper z),
      (∀ tau : Name upper, tau.val ∈ W → HereditarilySymmetric upperAct upper
        (a.principalSupportFamily ⊥ directed) tau) →
      ∃ validRows : ∀ z ∈ RowTerms, IsName c z,
      ∃ validUpper : ∀ z ∈ Name.renamedFamily upper inclusion RowTerms validRows, IsName upper z,
      let rowName := Name.familySet (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed))
        (Name.renamedFamily upper inclusion RowTerms validRows) validUpper
      rowName.val ∈ M.sets ∧
        (∀ g, upperAct.act upper g rowName = rowName) ∧
        HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) rowName ∧
      ∃ family ∈ M.sets, ∃ function : FunctionGraphOn W family,
      ∃ names : ∀ i, IsName upper (function.value i),
        (∀ g i, upperAct.act upper g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩) ∧
        (∀ i, HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed)
          ⟨function.value i, names i⟩) ∧
        ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed))),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          let sequence := Name.indexedGraphName (s := upper)
            (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)) function names
          rowName.val ∈ M.sets ∧ sequence.val ∈ M.sets ∧
          HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) sequence ∧
          Name.eval {p | H.mem p} rowName ∈ (M.symmetricExtension upper upperAct
            (a.principalSupportFamily ⊥ directed) H).sets ∧
          Name.eval {p | H.mem p} sequence ∈ (M.symmetricExtension upper upperAct
            (a.principalSupportFamily ⊥ directed) H).sets ∧
          ZFSet.IsFunc W (ZFSet.range (fun i : W =>
            Name.eval {p | H.mem p} ⟨function.value i, names i⟩)) (Name.eval {p | H.mem p} sequence) ∧
          ∀ i : W.toSet,
            let orbit := Name.eval {p | H.mem p} ⟨function.value i, names i⟩
            PartialFunctionCode (Name.eval {p | H.mem p} rowName) (⋃₀ ⋃₀ orbit) orbit ∧
            ∃ x ∈ Name.eval {p | H.mem p} rowName,
              ZFSet.pair x (Name.eval {p | H.mem p} ⟨i.val, validW i.val i.property⟩) ∈ orbit := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
  intro act c T T2 hT hT2 valid1 valid2 closed1 closed2 children1 children2 stages history hs hh ordinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed run
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    run.carriers ordinal carrier (c.encode ⊤) topMem topRows
  intro upper upperAct inclusion rows S RowTerms W hW validW symmetricW
  have rowProjection := M.semanticStructuralTrace_rowProjection c act b s a ⊥ directed T T2 (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
    hs hh ordinal trace infinite choice
  have projection := rowProjection.1
  have restrictionGround := rowProjection.2.1
  have inclusionGround := rowProjection.2.2.1
  have equivariant := rowProjection.2.2.2.2.2.2
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hs hPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection hG hL order graph supports hT hT2 hs hh
  have hGraph : upperAct.actionGraph upper b ∈ M.sets := by
    have graphEq := M.semanticStructuralAction_graph c act b s a ⊥ directed T T2 (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hs hh ordinal trace
    change upperAct.actionGraph upper b = _ at graphEq
    rw [graphEq]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection hG hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments forcingAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b pairing unions powers separation
    collection hQ hG hGraph
  have hI := M.nonbottom_carrier_mem s separation hL
  have hS := M.rowPositionSequences_mem pairing unions powers separation hL order hI hmu
  have tupleGraphGround := M.binaryRowTupleFamily_mem pairing unions powers separation collection infinite
    hL order hI hC hmu ⊤
  have hRowTerms : RowTerms ∈ M.sets := M.rowTupleTerms_mem unions separation hS tupleGraphGround
  have rowData := M.binaryRowTupleTerms_hs a s b C pairing unions powers separation infinite
    hL hC hG graph directed hmu muOrdinal
  have validRows (z : ZFSet.{u}) (member : z ∈ RowTerms) : IsName c z := by
    obtain ⟨tau, equal, _⟩ := rowData z member
    exact equal ▸ tau.property
  have rowHS (tau : Name c) (member : tau.val ∈ RowTerms) :
      HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) tau := by
    obtain ⟨sigma, equal, symmetric⟩ := rowData tau.val member
    exact (show sigma = tau from Subtype.ext equal) ▸ symmetric
  let lifted := Name.renamedFamily upper inclusion RowTerms validRows
  let renameGraph := Name.renameFamilyGraph upper inclusion RowTerms validRows
  have hLifted : lifted ∈ M.sets := M.renamedFamily_mem c upper pairing unions powers separation
    collection carrier hQ inclusion inclusionGround RowTerms hRowTerms validRows
  have hRenameGraph : renameGraph ∈ M.sets := M.renameFamilyGraph_mem c upper pairing unions powers separation
    collection carrier hQ inclusion inclusionGround RowTerms hRowTerms validRows
  have validUpper (z : ZFSet.{u}) (member : z ∈ lifted) : IsName upper z := by
    obtain ⟨tau, _, equal⟩ := (Name.mem_renamedFamily upper inclusion RowTerms validRows z).1 member
    exact equal.symm ▸ (Name.rename upper inclusion tau).property
  have liftedHS (tau : Name upper) (member : tau.val ∈ lifted) :
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) tau := by
    obtain ⟨sigma, inRows, equal⟩ := (Name.mem_renamedFamily upper inclusion RowTerms validRows tau.val).1 member
    have same : tau = Name.rename upper inclusion sigma := Subtype.ext equal
    exact same.symm ▸ HereditarilySymmetric.rename upperAct upper inclusion equivariant (rowHS sigma inRows)
  have liftedClosed (g : G) (tau : Name upper) (member : tau.val ∈ lifted) :
      (upperAct.act upper g tau).val ∈ lifted := by
    obtain ⟨sigma, inRows, equal⟩ := (Name.mem_renamedFamily upper inclusion RowTerms validRows tau.val).1 member
    have same : tau = Name.rename upper inclusion sigma := Subtype.ext equal
    have moved := M.binaryRowTupleTerms_action a s b C pairing unions powers separation infinite
      hL hC hG graph hmu muOrdinal g sigma inRows
    apply (Name.mem_renamedFamily upper inclusion RowTerms validRows _).2
    refine ⟨act.act c g sigma, moved, ?_⟩
    rw [same, act.act_rename_of_equivariant upperAct c upper inclusion equivariant]
  let rowName := Name.familySet (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)) lifted validUpper
  have topGround := M.transitive hQ (upper.encode_mem (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)))
  have rowNameGround : rowName.val ∈ M.sets := M.familySet_mem upper ⊤ pairing unions powers separation hLifted topGround validUpper
  have rowNameFixed := Name.act_familySet upperAct lifted validUpper liftedClosed
  have rowNameHS := Name.familySet_hs upperAct (a.principalSupportFamily ⊥ directed) lifted validUpper liftedClosed liftedHS
  have supportPackage := M.exists_groundSupportTupleFamily upperAct upper b s a C directed pairing unions powers separation
    collection infinite choice hQ hG hL order hC supports maps mu hmu muOrdinal small W hW validW symmetricW
  dsimp only at supportPackage
  let supportChoice := Classical.choose supportPackage
  have supportRest := Classical.choose_spec supportPackage
  let positionChoice := Classical.choose supportRest.2
  have positionRest := Classical.choose_spec supportRest.2
  let tupleChoice := Classical.choose positionRest.2
  have tupleRest := Classical.choose_spec positionRest.2
  have hTupleChoice := tupleRest.1
  have tupleChoiceFunction := tupleRest.2.2.2.1
  have chosenData := tupleRest.2.2.2.2
  let liftedChoice := relationCompose W RowTerms lifted tupleChoice renameGraph
  have liftedChoiceGround : liftedChoice ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hW hRowTerms hLifted hTupleChoice hRenameGraph
  have liftedChoiceFunction : ZFSet.IsFunc W lifted liftedChoice := relationCompose_function_of_subset
    tupleChoiceFunction (Name.renameFamilyGraph_function upper inclusion RowTerms validRows) (fun _ h => h)
  have orbitPackage := M.exists_groundSelectedOrbitNameFamily upperAct upper b pairing unions powers separation
    collection hQ hG maps (upper.encode ⊤) W lifted liftedChoice topGround hW hLifted
    liftedChoiceGround liftedChoiceFunction
  let family := Classical.choose orbitPackage
  have orbitRest := Classical.choose_spec orbitPackage
  have hFamily := orbitRest.1
  have function := orbitRest.2.1
  have familyValues := orbitRest.2.2
  have each (i : W.toSet) : ∃ tuple : Name upper, tuple.val ∈ lifted ∧
      function.value i = (Name.orbitPairGraph upperAct upper tuple ⟨i.val, validW i.val i.property⟩).val ∧
      ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed))),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
        ZFSet.IsFunc (ZFSet.range (fun g : G => Name.eval {p | H.mem p} (upperAct.act upper g tuple)))
          (ZFSet.range (fun g : G => Name.eval {p | H.mem p}
            (upperAct.act upper g ⟨i.val, validW i.val i.property⟩)))
          (Name.eval {p | H.mem p} (Name.orbitPairGraph upperAct upper tuple ⟨i.val, validW i.val i.property⟩)) := by
    let tau : Name upper := ⟨i.val, validW i.val i.property⟩
    obtain ⟨z, chosen, _⟩ := tupleChoiceFunction.2 i.val i.property
    have inRows := (ZFSet.pair_mem_prod.1 (tupleChoiceFunction.1 chosen)).2
    obtain ⟨D, f, _, _, _, supported, delta, hDelta, _, _, fn, positions, values, bounded, covers, exactCode⟩ :=
      chosenData tau z chosen
    let source := M.internalRowTupleName s C hL delta positions
    let tuple := Name.rename upper inclusion source
    have sourceIn : source.val ∈ RowTerms := exactCode ▸ inRows
    have tupleIn : tuple.val ∈ lifted := (Name.mem_renamedFamily upper inclusion RowTerms validRows _).2
      ⟨source, sourceIn, rfl⟩
    have renamed := (Name.pair_mem_renameFamilyGraph upper inclusion RowTerms validRows source tuple.val).2
      ⟨sourceIn, rfl⟩
    have liftedEntry : ZFSet.pair tau.val tuple.val ∈ liftedChoice :=
      (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨i.property, tupleIn, source.val, sourceIn, exactCode ▸ chosen, renamed⟩
    have jointGround : (Name.orderedPair (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)) tuple tau).val ∈ M.sets := by
      rw [Name.orderedPair_code]
      exact M.orderedPairNameCode_mem pairing topGround (M.transitive hLifted tupleIn) (M.transitive hW i.property)
    have code := M.orbitPairGraph_code_eq upperAct upper tuple tau jointGround
    rw [Name.orderedPair_code] at code
    have entry := (familyValues tau.val tuple.val liftedEntry _).2 code
    refine ⟨tuple, tupleIn, function.value_eq_of_entry i entry, ?_⟩
    intro H ordinary
    exact M.liftedRowOrbit_function a s b C pairing unions powers separation infinite hL hC hG graph
      choice uncountable delta positions D covers upper upperAct hQ
      (M.refinementHistoryRowRestriction c T stages packed) inclusion projection restrictionGround equivariant H ordinary tau supported
  let selectedTuple (i : W.toSet) := Classical.choose (each i)
  have selectedData (i : W.toSet) := Classical.choose_spec (each i)
  have names (i : W.toSet) : IsName upper (function.value i) :=
    (selectedData i).2.1.symm ▸ (Name.orbitPairGraph upperAct upper (selectedTuple i)
      ⟨i.val, validW i.val i.property⟩).property
  have actual (i : W.toSet) : (⟨function.value i, names i⟩ : Name upper) =
      Name.orbitPairGraph upperAct upper (selectedTuple i) ⟨i.val, validW i.val i.property⟩ :=
    Subtype.ext (selectedData i).2.1
  have fixed (g : G) (i : W.toSet) : upperAct.act upper g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩ := by
    rw [actual i]
    exact Name.act_orbitPairGraph upperAct upper _ _ g
  have children (i : W.toSet) : HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed)
      ⟨function.value i, names i⟩ := by
    rw [actual i]
    exact Name.orbitPairGraph_hs upperAct upper (a.principalSupportFamily ⊥ directed) _ _
      (liftedHS (selectedTuple i) (selectedData i).1) (symmetricW _ i.property)
  refine ⟨validRows, ?_⟩
  refine ⟨validUpper, ?_⟩
  dsimp only
  refine ⟨rowNameGround, rowNameFixed, rowNameHS,
    family, hFamily, function, names, fixed, children, ?_⟩
  intro H ordinary
  have package := M.supportedNameSequence_function_mem upper upperAct (a.principalSupportFamily ⊥ directed)
    pairing unions powers separation collection hQ hW hFamily function names ⊤
    (a.principalSupportFamily ⊥ directed).top (fun g _ i => fixed g i) children H
  refine ⟨rowNameGround, package.1, package.2.2.1,
    (M.mem_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H _).2
      ⟨rowName, rowNameGround, rowNameHS, rfl⟩, package.2.2.2.2, package.2.2.2.1, ?_⟩
  intro i
  let orbit := Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name upper)
  have fn := (selectedData i).2.2 H ordinary
  have within (g : G) : Name.eval {p | H.mem p} (upperAct.act upper g (selectedTuple i)) ∈
      Name.eval {p | H.mem p} rowName :=
    (Name.mem_eval_familySet {p | H.mem p} ⊤ H.top_mem lifted validUpper _).2
      ⟨upperAct.act upper g (selectedTuple i), liftedClosed g _ (selectedData i).1, rfl⟩
  have orbitEq : orbit = Name.eval {p | H.mem p} (Name.orbitPairGraph upperAct upper
      (selectedTuple i) ⟨i.val, validW i.val i.property⟩) := congrArg (Name.eval {p | H.mem p}) (actual i)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have original := hz
    change z ∈ orbit at hz
    rw [orbitEq] at hz
    obtain ⟨g, rfl⟩ := (Name.mem_eval_orbitPairGraph upperAct upper _ _ {p | H.mem p} H.top_mem z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨within g, pair_second_mem_doubleUnion original⟩
  · intro x y z first second
    change ZFSet.pair x y ∈ orbit at first
    change ZFSet.pair x z ∈ orbit at second
    have functionOn : FunctionGraphOn _ _ := ⟨_, fn⟩
    exact functionOn.unique (orbitEq ▸ first) (orbitEq ▸ second)
  · refine ⟨Name.eval {p | H.mem p} (selectedTuple i), ?_, ?_⟩
    · simpa only [upperAct.act_one] using within (1 : G)
    · change ZFSet.pair (Name.eval {p | H.mem p} (selectedTuple i))
        (Name.eval {p | H.mem p} ⟨i.val, validW i.val i.property⟩) ∈ orbit
      rw [orbitEq]
      apply (Name.mem_eval_orbitPairGraph upperAct upper _ _ {p | H.mem p} H.top_mem _).2
      exact ⟨1, congrArg₂ ZFSet.pair
        (congrArg (Name.eval {p | H.mem p}) (upperAct.act_one upper (selectedTuple i)))
        (congrArg (Name.eval {p | H.mem p}) (upperAct.act_one upper ⟨i.val, validW i.val i.property⟩))⟩

end PartitionPilot.Forcing.TransitiveGround




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
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
include order nodeMaps supports choice

theorem semanticBinaryRow_ordinal_partial_cover_oai
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu)
    (small : M.groundEmbeddable s.nonbottom.carrier mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (T T2 : ZFSet.{u}) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (act.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (act.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) T T2 level prior) stages history),
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
      (supportBasisCode s b a.principalFix) T T2 stages history
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
      (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) T T2 ordinal trace
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      run.carriers ordinal carrier (c.encode ⊤) topMem topRows
    let upper := SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed T T2 (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace
    let inclusion := M.refinementHistoryRowEmbedding c T stages packed run ordinal carrier
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let RowTerms := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∃ validRows : ∀ z ∈ RowTerms, IsName c z,
    ∃ validUpper : ∀ z ∈ Name.renamedFamily upper inclusion RowTerms validRows, IsName upper z,
    let rowName := Name.familySet (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed))
      (Name.renamedFamily upper inclusion RowTerms validRows) validUpper
    ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed))),
      H.GenericFor (formulaFamily (M.nameDomain upper)) →
      let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
      let Trow := Name.eval {p | H.mem p} rowName
      Trow ∈ N.sets ∧
      ∀ X ∈ N.sets, ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
        ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
          (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi) ∧
          ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
            ∃ u ∈ Trow, ZFSet.pair u x ∈ hi := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
  intro act c T T2 hT hT2 valid1 valid2 closed1 closed2 children1 children2 stages history hs hh ordinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed run
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    run.carriers ordinal carrier (c.encode ⊤) topMem topRows
  intro upper upperAct inclusion rows S RowTerms
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hs hPacked omega
  have cover := M.semanticBinaryRow_orbit_cover a s b C pairing unions powers separation collection
    infinite choice hL order hC hG graph nodeMaps supports directed uncountable mu hmu muOrdinal small
    T T2 hT hT2 valid1 valid2 closed1 closed2 children1 children2 stages history hs hh ordinal trace
  dsimp only at cover
  have emptyGround := M.empty_mem ⟨mu, hmu⟩
  have base := cover ∅ emptyGround (fun z hz => False.elim (ZFSet.notMem_empty z hz))
    (fun tau member => False.elim (ZFSet.notMem_empty tau.val member))
  let validRows := Classical.choose base
  have baseRows := Classical.choose_spec base
  let validUpper := Classical.choose baseRows
  have baseData := Classical.choose_spec baseRows
  refine ⟨validRows, ?_⟩
  refine ⟨validUpper, ?_⟩
  dsimp only
  intro H ordinary
  let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
  let Trow := Name.eval {p | H.mem p} (Name.familySet
    (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed))
    (Name.renamedFamily upper inclusion RowTerms validRows) validUpper)
  have groundSubset := M.ground_subset_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed)
    pairing unions powers separation collection hQ H
  refine ⟨(M.mem_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H _).2
    ⟨_, baseData.1, baseData.2.2.1, rfl⟩, ?_⟩
  intro X hX
  obtain ⟨tau, tauGround, tauHS, tauValue⟩ :=
    (M.mem_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H X).1 hX
  have singletonGround : ({tau.val} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing tauGround tauGround
  have singletonValid (z : ZFSet.{u}) (hz : z ∈ ({tau.val} : ZFSet.{u})) : IsName upper z :=
    (ZFSet.mem_singleton.1 hz).symm ▸ tau.property
  have singletonHS (sigma : Name upper) (member : sigma.val ∈ ({tau.val} : ZFSet.{u})) :
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) sigma :=
    (show sigma = tau from Subtype.ext (ZFSet.mem_singleton.1 member)).symm ▸ tauHS
  let W := Name.childFamilyCodes upper {tau.val}
  have hW : W ∈ M.sets := M.childFamilyCodes_mem upper pairing unions powers separation hQ _ singletonGround
  have validW := Name.childFamilyCodes_valid upper {tau.val} singletonValid
  have symmetricW := Name.childFamilyCodes_hs upper upperAct (a.principalSupportFamily ⊥ directed)
    {tau.val} singletonValid singletonHS
  have selected := cover W hW validW symmetricW
  have selectedRows := Classical.choose_spec selected
  have selectedData := Classical.choose_spec selectedRows
  let family := Classical.choose selectedData.2.2.2
  have familyData := Classical.choose_spec selectedData.2.2.2
  let function := Classical.choose familyData.2
  have functionData := Classical.choose_spec familyData.2
  let names := Classical.choose functionData
  have nameData := Classical.choose_spec functionData
  have original := nameData.2.2 H ordinary
  refine M.exists_ordinalPartialMapCover upper upperAct (a.principalSupportFamily ⊥ directed)
    pairing unions powers separation collection choice hQ hW familyData.1
    function names nameData.1 nameData.2.1 H Trow X
    (fun i => (original.2.2.2.2.2.2 i).1) ?_
  intro x member
  have originalMember : x ∈ Name.eval {p | H.mem p} tau :=
    Eq.mpr (congrArg (fun A => x ∈ A) tauValue) member
  have childWitness : ∃ sigma : Name upper, sigma.val ∈ W ∧
      Name.eval {p | H.mem p} sigma = x :=
    Name.eval_member_childFamilyCodes upper {tau.val} singletonValid
      {p | H.mem p} tau (ZFSet.mem_singleton.2 rfl) x originalMember
  let sigma := Classical.choose childWitness
  have sigmaData := Classical.choose_spec childWitness
  let i : W.toSet := ⟨sigma.val, sigmaData.1⟩
  have rangeWitness : ∃ u ∈ Trow, ZFSet.pair u (Name.eval {p | H.mem p} sigma) ∈
      Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name upper) :=
    (original.2.2.2.2.2.2 i).2
  let u := Classical.choose rangeWitness
  have uData := Classical.choose_spec rangeWitness
  refine ⟨i, u, uData.1, ?_⟩
  exact Eq.mp (congrArg (fun v => ZFSet.pair u v ∈
    Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name upper)) sigmaData.2) uData.2

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.semanticBinaryRow_ordinal_partial_cover_oai.{u}
