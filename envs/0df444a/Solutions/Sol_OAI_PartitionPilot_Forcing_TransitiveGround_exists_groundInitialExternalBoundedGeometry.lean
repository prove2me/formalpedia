-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T05:58:34.204769+00:00
-- url     : https://prove2.me/submissions/afab586d-2114-454b-a16f-b3318f937ad0

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Data.List.Chain
import Mathlib.Data.Prod.Lex
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.ZFC.Rank
import Definitions.Def_PartitionPrinciple
import Definitions.Def_OAIQ253P007

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_Compression
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot

section

universe u v

theorem profile_at_shadow {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (c e K : α) (F : α → Prop)
    (old_profile : Profile P c e K F)
    (e_not_le_K : ¬ P.le e K)
    (x : β) (above_e : Q.le (i.toFun e) x)
    (shadow : HasOldShadow i x) :
    (PositiveOver i F x → Q.le (i.toFun K) x) ∧
    (¬ PositiveOver i F x → Q.meet (i.toFun K) x = i.toFun c) := by
  cases shadow with
  | intro l hl =>
    have part := hl.left
    have shadow_meet := hl.right
    have e_le_l : P.le e l := (part e).mp above_e
    have x_not_le_K : ¬ Q.le x (i.toFun K) := by
      intro hx
      exact e_not_le_K ((i.le_iff e K).mp (Q.trans above_e hx))
    have positives : PositiveOver i F x ↔ Positive P F l := by
      constructor
      · intro hp
        cases hp with
        | intro f hf => exact ⟨f, hf.left, (part f).mp hf.right⟩
      · intro hp
        cases hp with
        | intro f hf => exact ⟨f, hf.left, (part f).mpr hf.right⟩
    have inherited := old_profile l e_le_l
    constructor
    · intro hp
      exact (part K).mpr (inherited.left (positives.mp hp))
    · intro hn
      have hn_old : ¬ Positive P F l := fun hp => hn (positives.mpr hp)
      calc
        Q.meet (i.toFun K) x = Q.meet x (i.toFun K) := meet_comm Q _ _
        _ = i.toFun (P.meet l K) := shadow_meet K x_not_le_K
        _ = i.toFun (P.meet K l) := congrArg i.toFun (meet_comm P l K)
        _ = i.toFun c := congrArg i.toFun (inherited.right hn_old)

theorem profile_persists_one_step {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (c e K : α) (F : α → Prop)
    (nonempty_F : ∃ f, F f)
    (old_profile : Profile P c e K F)
    (e_not_le_K : ¬ P.le e K)
    (extension : PermittedExtension i) :
    ProfileOver i c e K F := by
  intro x above_e
  cases extension x with
  | inl old =>
    cases old with
    | intro a ha =>
      cases ha
      have e_le_a : P.le e a := (i.le_iff e a).mp above_e
      have positives : PositiveOver i F (i.toFun a) ↔ Positive P F a := by
        constructor
        · intro hp
          cases hp with
          | intro f hf => exact ⟨f, hf.left, (i.le_iff f a).mp hf.right⟩
        · intro hp
          cases hp with
          | intro f hf => exact ⟨f, hf.left, (i.le_iff f a).mpr hf.right⟩
      have inherited := old_profile a e_le_a
      constructor
      · intro hp
        exact (i.le_iff K a).mpr (inherited.left (positives.mp hp))
      · intro hn
        have hn_old : ¬ Positive P F a := fun hp => hn (positives.mpr hp)
        calc
          Q.meet (i.toFun K) (i.toFun a) = i.toFun (P.meet K a) :=
            (i.map_meet K a).symm
          _ = i.toFun c := congrArg i.toFun (inherited.right hn_old)
  | inr fresh =>
    cases fresh with
    | inl shadow =>
      exact profile_at_shadow i c e K F old_profile e_not_le_K x above_e shadow
    | inr top =>
      constructor
      · intro _
        exact top (i.toFun K)
      · intro hn
        cases nonempty_F with
        | intro f hf => exact False.elim (hn ⟨f, hf, top (i.toFun f)⟩)

end



namespace Attachment

universe u v w

variable {O : Type u} {N : Type v} {I : Type w} {P : MeetOrder O}

theorem has_old_shadow (d : Data P N I) (local_meets : ComponentMeets d) (x : N) :
    HasOldShadow (oldEmbedding d local_meets) (.inr x) := by
  refine ⟨d.shadow x, fun _ => Iff.rfl, ?_⟩
  intro a h
  exact meet_eq d local_meets (shadow_meet d x a h)

theorem permitted_extension (d : Data P N I) (local_meets : ComponentMeets d) :
    PermittedExtension (oldEmbedding d local_meets) := by
  intro x
  cases x with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr x => exact Or.inr (Or.inl (has_old_shadow d local_meets x))

theorem attachment_preserves_profile (d : Data P N I) (local_meets : ComponentMeets d)
    (c e K : O) (F : O → Prop) (nonempty_F : ∃ f, F f)
    (old_profile : Profile P c e K F) (e_not_le_K : ¬ P.le e K) :
    ProfileOver (oldEmbedding d local_meets) c e K F :=
  profile_persists_one_step (oldEmbedding d local_meets) c e K F
    nonempty_F old_profile e_not_le_K (permitted_extension d local_meets)

end Attachment



namespace Attachment

universe u v w

namespace Templates

variable {O : Type u} {I : Type w} {P : MeetOrder O} (b : Templates.{u,v,w} P I)

theorem persistence (c e K : O) (F : O → Prop) (nonempty_F : ∃ f, F f)
    (old_profile : Profile P c e K F) (e_not_le_K : ¬ P.le e K) :
    ProfileOver b.oldEmbedding c e K F :=
  attachment_preserves_profile b.data b.component_meets c e K F nonempty_F old_profile e_not_le_K

end Templates
end Attachment




universe u v w

namespace Attachment.Templates

variable {O : Type u} {I : Type w} {P : MeetOrder O} (b : Templates.{u,v,w} P I)

theorem positive_old_iff (i : I) (a : O) :
    Positive b.extension (b.originalFamily i) (.inl a) ↔ b.upper i a := by
  constructor
  · rintro ⟨f, hf, hfa⟩
    cases f with
    | inl f => exact b.upper_up i hf hfa
    | inr f => exact False.elim hf
  · intro ha
    exact ⟨.inl a, ha, P.refl a⟩

theorem positive_new_iff (i : I) (x : b.Fresh) :
    Positive b.extension (b.originalFamily i) (.inr x) ↔ b.upper i (b.shadow x) := by
  constructor
  · rintro ⟨f, hf, hfx⟩
    cases f with
    | inl f => exact b.upper_up i hf hfx
    | inr f => exact False.elim hf
  · intro hx
    exact ⟨.inl (b.shadow x), hx, P.refl _⟩

theorem cap_shadow (i : I) (t : b.Space i)
    (top : ∀ y, (b.order i).le y t)
    (outside : ¬ (b.order i).le t (b.anchor i)) :
    b.shadow (b.cap i t outside) = b.base i := by
  change (b.embed i).toFun (cut (b.order i) (b.anchor i) t) = _
  have hcut : cut (b.order i) (b.anchor i) t =
      ⟨b.anchor i, (b.order i).refl _⟩ := by
    apply Subtype.ext
    exact (b.order i).antisymm ((b.order i).meet_le_right _ _)
      ((b.order i).le_meet (top _) ((b.order i).refl _))
  exact congrArg (b.embed i).toFun hcut

theorem cap_strict_above_base (i : I) (t : b.Space i)
    (top : ∀ y, (b.order i).le y t)
    (outside : ¬ (b.order i).le t (b.anchor i)) :
    b.extension.le (.inl (b.base i)) (.inr (b.cap i t outside)) ∧
    ¬ b.extension.le (.inr (b.cap i t outside)) (.inl (b.base i)) := by
  constructor
  · change P.le (b.base i) (b.shadow (b.cap i t outside))
    rw [b.cap_shadow i t top outside]
    exact P.refl _
  · exact b.data.base_not_upper i

theorem separator_not_below_cap (i : I) (t : b.Space i)
    (top : ∀ y, (b.order i).le y t)
    (outside : ¬ (b.order i).le t (b.anchor i)) :
    ¬ b.extension.le (.inl (b.separator i)) (.inr (b.cap i t outside)) := by
  intro h
  change P.le (b.separator i) (b.shadow (b.cap i t outside)) at h
  rw [b.cap_shadow i t top outside] at h
  exact b.separator_not_le_base i h

theorem initial_profile (i : I) (t : b.Space i)
    (top : ∀ y, (b.order i).le y t)
    (outside : ¬ (b.order i).le t (b.anchor i)) :
    Profile b.extension (.inl (b.base i)) (.inl (b.separator i))
      (.inr (b.cap i t outside)) (b.originalFamily i) := by
  intro x above_e
  cases x with
  | inl a =>
    constructor
    · intro hp
      exact (b.positive_old_iff i a).mp hp
    · intro hn
      have not_upper : ¬ b.upper i a := fun ha => hn ((b.positive_old_iff i a).mpr ha)
      calc
        b.extension.meet (.inr (b.cap i t outside)) (.inl a) =
            .inl (P.meet (b.shadow (b.cap i t outside)) a) :=
          b.shadow_meet_eq _ a not_upper
        _ = .inl (P.meet (b.base i) a) := by rw [b.cap_shadow i t top outside]
        _ = .inl (b.base i) := congrArg Sum.inl
          (meet_eq_left_of_le P (P.trans (b.base_le_separator i) above_e))
  | inr x =>
    have different : i ≠ x.1 := by
      intro same
      have hs := b.data.shadow_le_base x
      change P.le (b.shadow x) (b.base x.1) at hs
      rw [← same] at hs
      exact b.separator_not_le_base i (P.trans above_e hs)
    have not_xk : ¬ b.extension.le (.inr x) (.inr (b.cap i t outside)) := by
      intro h
      exact b.separator_not_below_cap i t top outside (b.extension.trans above_e h)
    constructor
    · intro hp
      exact (b.cross_le_iff _ x different).mpr ((b.positive_new_iff i x).mp hp)
    · intro hn
      have not_kx : ¬ b.extension.le (.inr (b.cap i t outside)) (.inr x) := by
        intro h
        exact hn ((b.positive_new_iff i x).mpr ((b.cross_le_iff _ x different).mp h))
      calc
        b.extension.meet (.inr (b.cap i t outside)) (.inr x) =
            .inl (P.meet (b.shadow (b.cap i t outside)) (b.shadow x)) :=
          b.cross_meet_eq _ x different not_kx not_xk
        _ = .inl (P.meet (b.base i) (b.shadow x)) := by rw [b.cap_shadow i t top outside]
        _ = .inl (b.base i) := congrArg Sum.inl
          (meet_eq_left_of_le P (P.trans (b.base_le_separator i) above_e))

end Attachment.Templates

namespace Compression

theorem range_completion_from_accounting {A : Type u} {J : Type v}
    (P : MeetOrder A) (Original : A → Prop) (base cap : J → A) (s : J → A → A)
    (base_filled : ∀ i x, P.le x (base i) → ∃ y, s i y = x)
    (old_shadow : ∀ i x, Original x → P.le x (cap i) → P.le x (base i))
    (separation : ∀ i j, i ≠ j →
      P.le (cap i) (base j) ∨ P.le (cap j) (base i) ∨
      P.meet (cap i) (cap j) = P.meet (base i) (base j))
    (accounting : ∀ x, Original x ∨
      ∃ j y, s j y = x ∧ P.le x (cap j) ∧ ¬ P.le x (base j)) :
    ∀ i x, P.le x (cap i) → ∃ y, s i y = x := by
  classical
  intro i x hxi
  cases accounting x with
  | inl old => exact base_filled i x (old_shadow i x old hxi)
  | inr new =>
    rcases new with ⟨j, y, hy, hxj, not_base⟩
    by_cases same : j = i
    · cases same
      exact ⟨y, hy⟩
    · cases separation j i same with
      | inl hjci => exact base_filled i x (P.trans hxj hjci)
      | inr h =>
        cases h with
        | inl hicj => exact False.elim (not_base (P.trans hxi hicj))
        | inr hmeet =>
          have hxmeet : P.le x (P.meet (base j) (base i)) := hmeet ▸ P.le_meet hxj hxi
          exact base_filled i x (P.trans hxmeet (P.meet_le_right _ _))

end Compression

end PartitionPilot

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveMaps
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z

namespace Inputs

variable {O : Type u} {I : Type w} {P : MeetOrder O}
    {b : Templates.{u,v,w} P I} {Task : Type z} (d : Inputs b Task)

theorem fresh_accounting (T : O) (top : ∀ p, P.le p T) (z : d.nextBatch.Fresh) :
    ∃ i x, d.lift i x = .inr z ∧
      d.nextBatch.extension.le (.inr z) (.inl ((d.previous i).toFun T)) ∧
      ¬ d.nextBatch.extension.le (.inr z) (.inl ((d.previous i).toFun (d.source i))) := by
  rcases z with ⟨⟨i, ⟨h, eligible⟩⟩, y⟩
  refine ⟨i, .inr ⟨h, y⟩, d.lift_new_outside i ⟨h, y⟩ eligible, ?_, ?_⟩
  · exact d.fresh_below_cap i ⟨h, y⟩ eligible T top
  · exact d.fresh_outside_base i ⟨h, y⟩ eligible

end Inputs
end PartitionPilot.Compression.RecursiveMaps

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



namespace PartitionPilot.Forcing
universe u

namespace NatUnionCode

theorem constant (A : ZFSet.{u}) : NatUnionCode (fun _ => A) A := by
  intro x
  exact ⟨fun hx => ⟨0, hx⟩, fun ⟨_, hx⟩ => hx⟩

theorem prod_left {stages : Nat → ZFSet.{u}} {union : ZFSet.{u}}
    (code : NatUnionCode stages union) (A : ZFSet.{u}) :
    NatUnionCode (fun n => ZFSet.prod A (stages n)) (ZFSet.prod A union) := by
  intro z
  constructor
  · rintro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨n, hn⟩ := (code y).1 hy
    exact ⟨n, ZFSet.pair_mem_prod.2 ⟨hx, hn⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hn
    exact ZFSet.pair_mem_prod.2 ⟨hx, code.subset n hy⟩

theorem prod {A B : Nat → ZFSet.{u}} {U V : ZFSet.{u}}
    (left : NatUnionCode A U) (right : NatUnionCode B V)
    (leftMono : ∀ n m, n ≤ m → A n ⊆ A m)
    (rightMono : ∀ n m, n ≤ m → B n ⊆ B m) :
    NatUnionCode (fun n => ZFSet.prod (A n) (B n)) (ZFSet.prod U V) := by
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨n, hn⟩ := (left x).1 hx
    obtain ⟨m, hm⟩ := (right y).1 hy
    exact ⟨max n m, ZFSet.pair_mem_prod.2
      ⟨leftMono n _ (le_max_left n m) hn, rightMono m _ (le_max_right n m) hm⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hn
    exact ZFSet.pair_mem_prod.2 ⟨left.subset n hx, right.subset n hy⟩

theorem isFunc {A B f : Nat → ZFSet.{u}} {U V F : ZFSet.{u}}
    (domain : NatUnionCode A U) (range : NatUnionCode B V) (graph : NatUnionCode f F)
    (functions : ∀ n, ZFSet.IsFunc (A n) (B n) (f n))
    (graphMono : ∀ n m, n ≤ m → f n ⊆ f m) : ZFSet.IsFunc U V F := by
  constructor
  · intro z hz
    obtain ⟨n, hn⟩ := (graph z).1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((functions n).1 hn)
    exact ZFSet.pair_mem_prod.2 ⟨domain.subset n hx, range.subset n hy⟩
  · intro x hx
    obtain ⟨n, hn⟩ := (domain x).1 hx
    obtain ⟨y, entry, _⟩ := (functions n).2 x hn
    refine ⟨y, graph.subset n entry, ?_⟩
    intro z hz
    obtain ⟨m, hm⟩ := (graph _).1 hz
    have first := graphMono n (max n m) (le_max_left n m) entry
    have second := graphMono m (max n m) (le_max_right n m) hm
    have inDomain := (ZFSet.pair_mem_prod.1 ((functions (max n m)).1 first)).1
    obtain ⟨_, _, unique⟩ := (functions (max n m)).2 x inDomain
    exact (unique z second).trans (unique y first).symm

theorem function_entry_iff {A B f : Nat → ZFSet.{u}} {U V F : ZFSet.{u}}
    (graph : NatUnionCode f F) (function : ZFSet.IsFunc U V F)
    (functions : ∀ n, ZFSet.IsFunc (A n) (B n) (f n))
    (n : Nat) {x y : ZFSet.{u}} (hx : x ∈ A n) :
    ZFSet.pair x y ∈ F ↔ ZFSet.pair x y ∈ f n := by
  constructor
  · intro entry
    obtain ⟨z, old, _⟩ := (functions n).2 x hx
    have oldUnion := graph.subset n old
    have inDomain := (ZFSet.pair_mem_prod.1 (function.1 oldUnion)).1
    obtain ⟨_, _, unique⟩ := function.2 x inDomain
    have equal : y = z := (unique y entry).trans (unique z oldUnion).symm
    exact equal.symm ▸ old
  · exact fun entry => graph.subset n entry

end NatUnionCode

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_HeightAttachment
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

open Attachment

universe u v w z

namespace AttachmentHeight

variable {O : Type u} {I : Type w} {H : Type z} {P : MeetOrder O} {R : HeightOrder H}
    (b : Templates.{u,v,w} P I) (old : StrictHeight P R)
    (component : ∀ i, StrictHeight (b.order i) R)

theorem bound_preserved
    (upper : ∀ x : b.Fresh, R.lt ((component x.1).value x.2.val) (old.value (b.separator x.1)))
    (bound : H) (old_bound : ∀ x, R.Weak (old.value x) bound) :
    ∀ x, R.Weak (value b old component x) bound := by
  intro x
  cases x with
  | inl x => exact old_bound x
  | inr x => exact Or.inr (R.lt_weak (upper x) (old_bound (b.separator x.1)))

end AttachmentHeight
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_DenseInterpolation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u v w

namespace LinearHeightOrder

variable {A : Type u} (R : LinearHeightOrder A)

theorem weak_refl (x : A) : R.Weak x x := Or.inl rfl

theorem weak_trans {x y z : A} (h : R.Weak x y) (h' : R.Weak y z) : R.Weak x z := by
  rcases h with rfl | h
  · exact h'
  · exact Or.inr (R.lt_weak h h')

theorem list_max (a : A) (xs : List A) :
    ∃ m, (m = a ∨ m ∈ xs) ∧ R.Weak a m ∧ ∀ x ∈ xs, R.Weak x m := by
  induction xs with
  | nil => exact ⟨a, Or.inl rfl, R.weak_refl a, by simp⟩
  | cons x xs ih =>
    rcases ih with ⟨m, hm, ha, hx⟩
    rcases R.compare x m with h | eq | h
    · refine ⟨m, ?_, ha, ?_⟩
      · rcases hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_cons_of_mem x hm)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inr h
        · exact hx y hy
    · refine ⟨m, ?_, ha, ?_⟩
      · exact Or.inr (List.mem_cons.mpr (Or.inl eq.symm))
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl eq
        · exact hx y hy
    · refine ⟨x, Or.inr (List.mem_cons_self), R.weak_trans ha (Or.inr h), ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact R.weak_refl _
      · exact R.weak_trans (hx y hy) (Or.inr h)

theorem list_min (a : A) (xs : List A) :
    ∃ m, (m = a ∨ m ∈ xs) ∧ R.Weak m a ∧ ∀ x ∈ xs, R.Weak m x := by
  rcases R.reverse.list_max a xs with ⟨m, hm, ha, hx⟩
  refine ⟨m, hm, ?_, ?_⟩
  · rcases ha with eq | h
    · exact Or.inl eq.symm
    · exact Or.inr h
  · intro x h
    rcases hx x h with eq | h'
    · exact Or.inl eq.symm
    · exact Or.inr h'

end LinearHeightOrder

namespace DenseHeightOrder

variable {D : Type v} (R : DenseHeightOrder D)

theorem finite_gap (lo hi : D) (lower upper : List D)
    (gap : R.lt lo hi)
    (lower_hi : ∀ x ∈ lower, R.lt x hi)
    (lo_upper : ∀ y ∈ upper, R.lt lo y)
    (separated : ∀ x ∈ lower, ∀ y ∈ upper, R.lt x y) :
    ∃ z, R.lt lo z ∧ R.lt z hi ∧
      (∀ x ∈ lower, R.lt x z) ∧ (∀ y ∈ upper, R.lt z y) := by
  rcases R.toLinearHeightOrder.list_max lo lower with ⟨a, ha, hlo, hlow⟩
  rcases R.toLinearHeightOrder.list_min hi upper with ⟨b, hb, hhi, hupp⟩
  have ab : R.lt a b := by
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact gap
      · exact lo_upper b hb
    · rcases hb with rfl | hb
      · exact lower_hi a ha
      · exact separated a ha b hb
  rcases R.between a b ab with ⟨z, az, zb⟩
  exact ⟨z, R.weak_lt hlo az, R.lt_weak zb hhi,
    fun x hx => R.weak_lt (hlow x hx) az,
    fun y hy => R.lt_weak zb (hupp y hy)⟩

end DenseHeightOrder

namespace CountableInterpolation

variable {A : Type u} {D : Type v} (S : LinearHeightOrder A)
    (R : DenseHeightOrder D) (enumerate : Nat → A) (lo hi : D)

variable {S R enumerate lo hi}

theorem next_exists {n : Nat} (p : Partial S R enumerate lo hi n) (gap : R.lt lo hi) :
    ∃ z, R.lt lo z ∧ R.lt z hi ∧
      (∀ i, i < n → S.lt (enumerate i) (enumerate n) → R.lt (p.value i) z) ∧
      (∀ i, i < n → S.lt (enumerate n) (enumerate i) → R.lt z (p.value i)) ∧
      (∀ i, i < n → enumerate i = enumerate n → p.value i = z) := by
  classical
  by_cases seen : ∃ i, i < n ∧ enumerate i = enumerate n
  · rcases seen with ⟨j, hj, he⟩
    refine ⟨p.value j, p.lower j hj, p.upper j hj, ?_, ?_, ?_⟩
    · intro i h h'
      exact p.strict i j h hj (he ▸ h')
    · intro i h h'
      exact p.strict j i hj h (he ▸ h')
    · intro i h h'
      exact p.equal i j h hj (h'.trans he.symm)
  · let lowers := ((List.range n).filter (fun i => S.lt (enumerate i) (enumerate n))).map p.value
    let uppers := ((List.range n).filter (fun i => S.lt (enumerate n) (enumerate i))).map p.value
    have lower_spec : ∀ x, x ∈ lowers ↔ ∃ i, i < n ∧ S.lt (enumerate i) (enumerate n) ∧ p.value i = x := by
      intro x
      simp only [lowers, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨i, ⟨h, h'⟩, eq⟩
        exact ⟨i, h, h', eq⟩
      · rintro ⟨i, h, h', eq⟩
        exact ⟨i, ⟨h, h'⟩, eq⟩
    have upper_spec : ∀ x, x ∈ uppers ↔ ∃ i, i < n ∧ S.lt (enumerate n) (enumerate i) ∧ p.value i = x := by
      intro x
      simp only [uppers, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨i, ⟨h, h'⟩, eq⟩
        exact ⟨i, h, h', eq⟩
      · rintro ⟨i, h, h', eq⟩
        exact ⟨i, ⟨h, h'⟩, eq⟩
    have lh : ∀ x ∈ lowers, R.lt x hi := by
      intro x hx
      rcases (lower_spec x).mp hx with ⟨i, h, _, rfl⟩
      exact p.upper i h
    have lu : ∀ x ∈ uppers, R.lt lo x := by
      intro x hx
      rcases (upper_spec x).mp hx with ⟨i, h, _, rfl⟩
      exact p.lower i h
    have sep : ∀ x ∈ lowers, ∀ y ∈ uppers, R.lt x y := by
      intro x hx y hy
      rcases (lower_spec x).mp hx with ⟨i, h, h', rfl⟩
      rcases (upper_spec y).mp hy with ⟨j, k, k', rfl⟩
      exact p.strict i j h k (S.trans h' k')
    rcases R.finite_gap lo hi lowers uppers gap lh lu sep with ⟨z, hz, zh, hl, hu⟩
    refine ⟨z, hz, zh, ?_, ?_, ?_⟩
    · intro i h h'
      exact hl _ ((lower_spec _).mpr ⟨i, h, h', rfl⟩)
    · intro i h h'
      exact hu _ ((upper_spec _).mpr ⟨i, h, h', rfl⟩)
    · intro i h eq
      exact False.elim (seen ⟨i, h, eq⟩)

end CountableInterpolation

end PartitionPilot.Compression.RecursiveMaps

end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_PresentedGroupCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {G : Type u} [Group G] (s : Presentation G)

theorem groupCode : GroupCode s.carrier
    ((s.product s).graph s (fun xy => xy.1 * xy.2))
    (s.graph s (fun x => x⁻¹)) (s.encode 1) := by
  refine ⟨(s.product s).graph_isFunc s _, s.graph_isFunc s _, s.encode_mem 1, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    exact ((s.product s).pair_mem_graph s _ (1, a) a).2 (one_mul a)
  · intro x hx
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    exact ((s.product s).pair_mem_graph s _ (a, 1) a).2 (mul_one a)
  · intro x hx y hy entry
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (s.mem_carrier y).1 hy
    have inverse := (s.pair_mem_graph s _ a b).1 entry
    apply ((s.product s).pair_mem_graph s _ (b, a) 1).2
    rw [← inverse, inv_mul_cancel]
  · intro x hx y hy z hz a ha b hb c hc xy yz az
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨z, rfl⟩ := (s.mem_carrier z).1 hz
    obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (s.mem_carrier b).1 hb
    obtain ⟨c, rfl⟩ := (s.mem_carrier c).1 hc
    have first := ((s.product s).pair_mem_graph s _ (x, y) a).1 xy
    have second := ((s.product s).pair_mem_graph s _ (y, z) b).1 yz
    have third := ((s.product s).pair_mem_graph s _ (a, z) c).1 az
    apply ((s.product s).pair_mem_graph s _ (x, b) c).2
    rw [← second, ← mul_assoc, first, third]

end PartitionPilot.SetRealization.Presentation

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundPairCompositions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.FunctionGraphOn

universe u
variable {I f : ZFSet.{u}}

theorem value_mem_doubleUnion (h : FunctionGraphOn I f) (i : {i : ZFSet.{u} // i ∈ I}) :
    h.value i ∈ ⋃₀ ⋃₀ f :=
  pair_second_mem_doubleUnion (h.value_entry i)

end PartitionPilot.Forcing.FunctionGraphOn



namespace PartitionPilot.Forcing

universe u v w

theorem literalTaskField_map {α : Type v} {β : Type w} (f : α → β)
    (a c ell e F label : α) (j : Fin 6) :
    f (literalTaskField a c ell e F label j) =
      literalTaskField (f a) (f c) (f ell) (f e) (f F) (f label) j := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
    (Fin.cases ?_ (fun i => Fin.elim0 i)))))) j <;> rfl

namespace BoundedFormula

open SetFormula

theorem truth_literalTaskFormula {n} (z a c ell e F label : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (literalTaskFormula z a c ell e F label) env ↔
      env z = literalTaskCode (env a) (env c) (env ell) (env e) (env F) (env label) := by
  simp only [literalTaskFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ u ∈ env z, ∃ v ∈ u, env z = ZFSet.pair (env a) v ∧
    ∃ u' ∈ v, ∃ v' ∈ u', v = ZFSet.pair (env c) v' ∧
    ∃ u'' ∈ v', ∃ v'' ∈ u'', v' = ZFSet.pair (env ell) v'' ∧
    ∃ u''' ∈ v'', ∃ v''' ∈ u''', v'' = ZFSet.pair (env e) v''' ∧
      v''' = ZFSet.pair (env F) (env label)) ↔ _
  constructor
  · rintro ⟨_, _, v, _, outer, _, _, v', _, second, _, _, v'', _, third,
      _, _, v''', _, fourth, last⟩
    rw [outer, second, third, fourth, last]
    rfl
  · intro equal
    let v''' := ZFSet.pair (env F) (env label)
    let v'' := ZFSet.pair (env e) v'''
    let v' := ZFSet.pair (env ell) v''
    let v := ZFSet.pair (env c) v'
    have outer : env z = ZFSet.pair (env a) v := equal
    refine ⟨{env a, v}, ?_, v, ZFSet.mem_pair.2 (Or.inr rfl), outer,
      {env c, v'}, ZFSet.mem_pair.2 (Or.inr rfl), v', ZFSet.mem_pair.2 (Or.inr rfl), rfl,
      {env ell, v''}, ZFSet.mem_pair.2 (Or.inr rfl), v'', ZFSet.mem_pair.2 (Or.inr rfl), rfl,
      {env e, v'''}, ZFSet.mem_pair.2 (Or.inr rfl), v''', ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl⟩
    rw [outer]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

theorem truth_literalTaskFieldEntryFormula {n} (j : Fin 6) (z I P R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (literalTaskFieldEntryFormula j z I P R U Labels) env ↔
      ∃ i ∈ env I, ∃ a ∈ env P, ∃ c ∈ env P, ∃ ell ∈ env R, ∃ e ∈ env P,
        ∃ F ∈ env U, ∃ label ∈ env Labels,
          env z = ZFSet.pair i (literalTaskField a c ell e F label j) ∧
            i = literalTaskCode a c ell e F label := by
  simp only [literalTaskFieldEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_literalTaskFormula]
  simp only [literalTaskField_map]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ParentSupportCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_relationToProductFormula {n} (a c q f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relationToProductFormula a c q f) env ↔
      env f ⊆ ZFSet.prod (env a) (ZFSet.prod (env c) (env q)) := by
  simp only [relationToProductFormula, Truth, truth_exMem, truth_orderedRightTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, d, hd, v, hv, equal⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨x, hx, ZFSet.pair d v, ZFSet.pair_mem_prod.2 ⟨hd, hv⟩, equal⟩
  · intro h w hw
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 hy
    exact ⟨x, hx, d, hd, v, hv, equal⟩

theorem truth_functionToProductFormula {n} (a c q f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (functionToProductFormula a c q f) env ↔
      ZFSet.IsFunc (env a) (ZFSet.prod (env c) (env q)) (env f) := by
  simp only [functionToProductFormula, Truth, truth_relationToProductFormula, truth_exMem,
    truth_rightTripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨d, _, v, _, entry, unique⟩ := total x hx
    refine ⟨ZFSet.pair d v, entry, ?_⟩
    intro y hy
    obtain ⟨b, hb, z, hz, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (shape hy)).2
    have both : b = d ∧ z = v := unique b hb z hz hy
    obtain ⟨rfl, rfl⟩ := both
    rfl
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨y, entry, unique⟩ := total x hx
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (shape entry)).2
    refine ⟨d, hd, v, hv, entry, ?_⟩
    intro b _ z _ hz
    exact ZFSet.pair_injective (unique _ hz)

end PartitionPilot.Forcing.BoundedFormula



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MapFamilyApplicationGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



open SetFormula
universe u

theorem pair_mem_mapFamilyApplicationGraph (I P Q family i x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i x) y ∈ mapFamilyApplicationGraph I P Q family ↔
      i ∈ I ∧ x ∈ P ∧ y ∈ Q ∧ ∃ f, ZFSet.pair i f ∈ family ∧ ZFSet.pair x y ∈ f := by
  rw [mapFamilyApplicationGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, a, ha, b, hb, f, _, equal, indexed, entry⟩
    obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    exact ⟨hj, ha, hb, f, indexed, entry⟩
  · rintro ⟨hi, hx, hy, f, indexed, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy⟩,
      i, hi, x, hx, y, hy, f, pair_second_mem_doubleUnion indexed, rfl, indexed, entry⟩

namespace BoundedFormula

theorem truth_mapFamilyApplicationEntryFormula {n} (z I P Q B family : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mapFamilyApplicationEntryFormula z I P Q B family) env ↔
      ∃ i ∈ env I, ∃ x ∈ env P, ∃ y ∈ env Q, ∃ f ∈ env B,
        env z = ZFSet.pair (ZFSet.pair i x) y ∧
          ZFSet.pair i f ∈ env family ∧ ZFSet.pair x y ∈ f := by
  simp only [mapFamilyApplicationEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mapFamilyApplicationGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Q family : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQ : Q ∈ M.sets) (hFamily : family ∈ M.sets) :
    mapFamilyApplicationGraph I P Q family ∈ M.sets := by
  have hB := M.union_mem unions (M.union_mem unions hFamily)
  let params := extend I (extend P (extend Q (extend (ZFSet.sUnion (ZFSet.sUnion family)) (extend family Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.mapFamilyApplicationEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hP (Fin.cases hQ (Fin.cases hB (Fin.cases hFamily
      (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hI hP) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.mapFamilyApplicationEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod I P) Q) = mapFamilyApplicationGraph I P Q family := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mapFamilyApplicationGraph, ZFSet.mem_sep,
      BoundedFormula.truth_mapFamilyApplicationEntryFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_DecodedGroundGroups
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroupCode

open SetRealization
universe u
variable {G m i e : ZFSet.{u}} (h : GroupCode G m i e)

theorem inverse_graph_eq :
    letI := h.toGroup
    (SetMembers.presentation G).graph (SetMembers.presentation G) (fun x => x⁻¹) = i := by
  let := h.toGroup
  exact (SetMembers.presentation G).graph_decodeFunction (SetMembers.presentation G) i h.inv_function

end PartitionPilot.Forcing.GroupCode

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLiteralTaskFieldRecognition
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

theorem literalTaskBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P R U Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) : literalTaskBound P R U Labels ∈ M.sets :=
  M.prod_mem pairing unions powers separation hP
    (M.prod_mem pairing unions powers separation hP
      (M.prod_mem pairing unions powers separation hR
        (M.prod_mem pairing unions powers separation hP
          (M.prod_mem pairing unions powers separation hU hLabels))))

theorem literalTaskFieldBound_mem
    {P R U Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) (j : Fin 6) :
    literalTaskFieldBound P R U Labels j ∈ M.sets :=
  Fin.cases hP (Fin.cases hP (Fin.cases hR (Fin.cases hP
    (Fin.cases hU (Fin.cases hLabels (fun i => Fin.elim0 i)))))) j

theorem literalTaskFieldGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P R U Labels : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) (j : Fin 6) :
    literalTaskFieldGraph I P R U Labels j ∈ M.sets := by
  let params := extend I (extend P (extend R (extend U (extend Labels Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.literalTaskFieldEntryFormula j 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hP (Fin.cases hR (Fin.cases hU (Fin.cases hLabels
      (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hI
      (M.literalTaskFieldBound_mem hP hR hU hLabels j))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.literalTaskFieldEntryFormula j 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod I (literalTaskFieldBound P R U Labels j)) =
      literalTaskFieldGraph I P R U Labels j := by
    apply ZFSet.ext
    intro z
    rw [literalTaskFieldGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_literalTaskFieldEntryFormula j 0 1 2 3 4 5 _)
  exact equal ▸ selected

theorem literalTaskFieldFamilies
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P R U Labels : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (subset : I ⊆ literalTaskBound P R U Labels) :
    ∀ j : Fin 6, literalTaskFieldGraph I P R U Labels j ∈ M.sets ∧
      ZFSet.IsFunc I (literalTaskFieldBound P R U Labels j) (literalTaskFieldGraph I P R U Labels j) :=
  fun j => ⟨M.literalTaskFieldGraph_mem pairing unions powers separation hI hP hR hU hLabels j,
    literalTaskFieldGraph_function subset j⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FiniteWordMapCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

namespace BoundedFormula

theorem truth_finiteWordMapFormula {k} (omega a b e f g : Fin k)
    (env : Fin k → ZFSet.{u}) :
    Truth (finiteWordMapFormula omega a b e f g) env ↔
      FiniteWordMapCode (env omega) (env a) (env b) (env e) (env f) (env g) := by
  simp only [finiteWordMapFormula, truth_exMem, Truth, truth_functionFormula,
    truth_imp, truth_pairMembershipFormula, FiniteWordMapCode]
  rfl

end BoundedFormula

theorem finiteWordMapCode_iff {B D : Type u} (s : Presentation B) (t : Presentation D)
    (e : B → D) (xs : List B) (ys : List D) :
    FiniteWordMapCode ZFSet.omega s.carrier t.carrier (s.graph t e)
      (finiteWordGraph s xs) (finiteWordGraph t ys) ↔ ys = xs.map e := by
  constructor
  · rintro ⟨n, hn, first, second, maps⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have firstLength := finiteWord_domain_unique first (finiteWordGraph_function s xs)
    have secondLength := finiteWord_domain_unique second (finiteWordGraph_function t ys)
    have length : ys.length = (xs.map e).length := by simp only [List.length_map]; omega
    apply List.ext_get length
    intro i hi hj
    have hxs : i < xs.length := by simpa only [List.length_map] using hj
    have entry := maps (natSetCode i) ((natSetCode_mem_iff i n).2 (by omega))
      (s.encode (xs.get ⟨i, hxs⟩)) (s.encode_mem _)
      (t.encode (ys.get ⟨i, hi⟩)) (t.encode_mem _)
      ((pair_mem_finiteWordGraph s xs i _).2 ⟨hxs, rfl⟩)
      ((pair_mem_finiteWordGraph t ys i _).2 ⟨hi, rfl⟩)
    have same := (s.pair_mem_graph t e _ _).1 entry
    simpa only [List.get_eq_getElem, List.getElem_map] using same.symm
  · rintro rfl
    refine ⟨natSetCode xs.length, natSetCode_mem_omega _, finiteWordGraph_function s xs, ?_, ?_⟩
    · simpa only [List.length_map] using finiteWordGraph_function t (xs.map e)
    · intro i hi x _ y _ source target
      obtain ⟨k, hk, rfl⟩ := (mem_natSetCode i xs.length).1 hi
      obtain ⟨_, rfl⟩ := (pair_mem_finiteWordGraph s xs k x).1 source
      obtain ⟨_, rfl⟩ := (pair_mem_finiteWordGraph t (xs.map e) k y).1 target
      apply (s.pair_mem_graph t e _ _).2
      simp only [List.get_eq_getElem, List.getElem_map]

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FiniteWordOperations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem finiteWordGraph_reverse_entry {B : Type u} (s : Presentation B)
    (xs : List B) (i : Nat) (a : ZFSet.{u}) :
    ZFSet.pair (natSetCode i) a ∈ finiteWordGraph s xs.reverse ↔
      ∃ j, i + j + 1 = xs.length ∧ ZFSet.pair (natSetCode j) a ∈ finiteWordGraph s xs := by
  constructor
  · intro entry
    obtain ⟨hi, value⟩ := (pair_mem_finiteWordGraph s xs.reverse i a).1 entry
    have bound : i < xs.length := by simpa only [List.length_reverse] using hi
    have hj : xs.length - 1 - i < xs.length := by omega
    refine ⟨xs.length - 1 - i, by omega, (pair_mem_finiteWordGraph s xs _ a).2 ⟨hj, ?_⟩⟩
    simpa only [List.get_eq_getElem, List.getElem_reverse] using value
  · rintro ⟨j, sum, entry⟩
    obtain ⟨hj, value⟩ := (pair_mem_finiteWordGraph s xs j a).1 entry
    have hi : i < xs.reverse.length := by simp only [List.length_reverse]; omega
    have equal : xs.length - 1 - i = j := by omega
    apply (pair_mem_finiteWordGraph s xs.reverse i a).2
    refine ⟨hi, ?_⟩
    simpa only [List.get_eq_getElem, List.getElem_reverse, equal] using value

theorem finiteWordGraph_reverse_code {B : Type u} (s : Presentation B) (xs : List B) :
    FiniteWordReverseCode s.carrier ZFSet.omega natAddGraph
      (finiteWordGraph s xs) (finiteWordGraph s xs.reverse) := by
  refine ⟨natSetCode xs.length, natSetCode_mem_omega _, finiteWordGraph_function s xs, ?_, ?_⟩
  · simpa only [List.length_reverse] using finiteWordGraph_function s xs.reverse
  · intro i hi a _
    obtain ⟨k, _, rfl⟩ := (mem_natSetCode i xs.length).1 hi
    rw [finiteWordGraph_reverse_entry]
    constructor
    · rintro ⟨j, sum, entry⟩
      have hj := (ZFSet.pair_mem_prod.1 ((finiteWordGraph_function s xs).1 entry)).1
      refine ⟨natSetCode j, hj, natSetCode (k + j), (natSetCode_mem_iff _ _).2 (by omega),
        (pair_mem_natAddGraph _ _ _).2 rfl, ?_, entry⟩
      exact (congrArg natSetCode sum).symm
    · rintro ⟨j, hj, l, hl, sum, successor, entry⟩
      obtain ⟨j, _, rfl⟩ := (mem_natSetCode j xs.length).1 hj
      obtain ⟨l, _, rfl⟩ := (mem_natSetCode l xs.length).1 hl
      have added := (pair_mem_natAddGraph _ _ _).1 sum
      have length : xs.length = l + 1 := natSetCode_injective successor
      exact ⟨j, by omega, entry⟩

theorem FiniteWordReverseCode.unique {A f h h' : ZFSet.{u}}
    (first : FiniteWordReverseCode A ZFSet.omega natAddGraph f h)
    (second : FiniteWordReverseCode A ZFSet.omega natAddGraph f h') : h = h' := by
  obtain ⟨n, hn, funF, funH, entries⟩ := first
  obtain ⟨n', hn', funF', funH', entries'⟩ := second
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode _).1 hn
  obtain ⟨n', rfl⟩ := (mem_omega_iff_natSetCode _).1 hn'
  have same := finiteWord_domain_unique funF' funF
  subst n'
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (funH.1 hz)
    exact (entries' i hi a ha).2 ((entries i hi a ha).1 hz)
  · intro hz
    obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (funH'.1 hz)
    exact (entries i hi a ha).2 ((entries' i hi a ha).1 hz)

theorem finiteWordReverseCode_iff {B : Type u} (s : Presentation B) (xs : List B) (h : ZFSet.{u}) :
    FiniteWordReverseCode s.carrier ZFSet.omega natAddGraph (finiteWordGraph s xs) h ↔
      h = finiteWordGraph s xs.reverse :=
  ⟨fun code => code.unique (finiteWordGraph_reverse_code s xs),
    fun equal => equal.symm ▸ finiteWordGraph_reverse_code s xs⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_FiniteWordOperationFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_finiteWordAppendFormula {k} (a omega add f g h : Fin k)
    (env : Fin k → ZFSet.{u}) :
    Truth (finiteWordAppendFormula a omega add f g h) env ↔
      FiniteWordAppendCode (env a) (env omega) (env add) (env f) (env g) (env h) := by
  simp only [finiteWordAppendFormula, truth_exMem, Truth, truth_functionFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_disj, truth_imp,
    ← iff_def, FiniteWordAppendCode]
  rfl

theorem truth_finiteWordReverseFormula {k} (a omega add f h : Fin k)
    (env : Fin k → ZFSet.{u}) :
    Truth (finiteWordReverseFormula a omega add f h) env ↔
      FiniteWordReverseCode (env a) (env omega) (env add) (env f) (env h) := by
  simp only [finiteWordReverseFormula, truth_exMem, Truth, truth_functionFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_successorFormula,
    truth_imp, ← iff_def, FiniteWordReverseCode]
  rfl

end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalAlphabetInversion
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

theorem pair_mem_externalSymbolInverseGraph (G S inv x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ externalSymbolInverseGraph G S inv ↔
      ExternalSymbolInverseEntry G S inv x y := by
  constructor
  · intro h
    obtain ⟨_, x', _, y', _, eq, entry⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact entry
  · intro entry
    have bounds : x ∈ externalGeneratorAlphabet G S ∧ y ∈ externalGeneratorAlphabet G S := by
      rcases entry with ⟨g, hg, h, hh, rfl, rfl, _⟩ | ⟨s, hs, b, rfl, rfl⟩
      · exact ⟨(externalActorSymbol_mem G S g).2 hg, (externalActorSymbol_mem G S h).2 hh⟩
      · exact ⟨(externalLetterSymbol_mem G S s b).2 hs,
          (externalLetterSymbol_mem G S s (!b)).2 hs⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 bounds,
      x, bounds.1, y, bounds.2, rfl, entry⟩

theorem externalSymbolInverseGraph_eq_graph {J L : Type u} [Inv J]
    (s : Presentation J) (t : Presentation L) :
    externalSymbolInverseGraph s.carrier t.carrier (s.graph s Inv.inv) =
      (externalGeneratorAlphabetPresentation s t).graph
        (externalGeneratorAlphabetPresentation s t) externalSymbolInverse := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  constructor
  · intro hz
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    rcases (pair_mem_externalSymbolInverseGraph _ _ _ x y).1 hz with
      ⟨g, hg, h, hh, rfl, rfl, entry⟩ | ⟨a, ha, b, rfl, rfl⟩
    · obtain ⟨g, rfl⟩ := (s.mem_carrier g).1 hg
      obtain ⟨h, rfl⟩ := (s.mem_carrier h).1 hh
      have eq := (s.pair_mem_graph s Inv.inv g h).1 entry
      subst h
      exact ⟨.inl g, rfl⟩
    · obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
      exact ⟨.inr (a, b), rfl⟩
  · rintro ⟨x, rfl⟩
    apply (pair_mem_externalSymbolInverseGraph _ _ _ _ _).2
    cases x with
    | inl g =>
      exact Or.inl ⟨s.encode g, s.encode_mem g, s.encode g⁻¹, s.encode_mem g⁻¹,
        rfl, rfl, (s.pair_mem_graph s Inv.inv g g⁻¹).2 rfl⟩
    | inr p => exact Or.inr ⟨t.encode p.1, t.encode_mem p.1, p.2, rfl, rfl⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace BoundedFormula

theorem truth_externalSymbolInverseFormula {n} (x y G S inv zero one : Fin n)
    (env : Fin n → ZFSet.{u}) (hZero : env zero = natSetCode 0)
    (hOne : env one = natSetCode 1) :
    Truth (externalSymbolInverseFormula x y G S inv zero one) env ↔
      ExternalSymbolInverseEntry (env G) (env S) (env inv) (env x) (env y) := by
  simp only [externalSymbolInverseFormula, truth_disj, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_orderedRightTripleFormula]
  change ((∃ g ∈ env G, ∃ h ∈ env G,
    env x = ZFSet.pair (env zero) g ∧ env y = ZFSet.pair (env zero) h ∧
      ZFSet.pair g h ∈ env inv) ∨ ∃ s ∈ env S,
    (env x = ZFSet.pair (env one) (ZFSet.pair s (env zero)) ∧
      env y = ZFSet.pair (env one) (ZFSet.pair s (env one))) ∨
    (env x = ZFSet.pair (env one) (ZFSet.pair s (env one)) ∧
      env y = ZFSet.pair (env one) (ZFSet.pair s (env zero)))) ↔ _
  rw [hZero, hOne]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨s, hs, h | h⟩
    · exact ⟨s, hs, false, h⟩
    · exact ⟨s, hs, true, h⟩
  · rintro ⟨s, hs, b, h⟩
    cases b with
    | false => exact ⟨s, hs, Or.inl h⟩
    | true => exact ⟨s, hs, Or.inr h⟩

theorem truth_externalSymbolInverseEntryFormula {n}
    (z alphabet G S inv zero one : Fin n) (env : Fin n → ZFSet.{u})
    (hZero : env zero = natSetCode 0) (hOne : env one = natSetCode 1) :
    Truth (externalSymbolInverseEntryFormula z alphabet G S inv zero one) env ↔
      ∃ x ∈ env alphabet, ∃ y ∈ env alphabet,
        env z = ZFSet.pair x y ∧ ExternalSymbolInverseEntry (env G) (env S) (env inv) x y := by
  simp only [externalSymbolInverseEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  apply exists_congr
  intro y
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl
    (truth_externalSymbolInverseFormula 1 0 G.succ.succ S.succ.succ inv.succ.succ
      zero.succ.succ one.succ.succ _ hZero hOne)

end BoundedFormula

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem externalSymbolInverseGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G S inv : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hInv : inv ∈ M.sets) :
    externalSymbolInverseGraph G S inv ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨G, hG⟩
  have hOne : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  let params := extend (externalGeneratorAlphabet G S) (extend G (extend S (extend inv
    (extend (natSetCode 0) (extend (natSetCode 1) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalSymbolInverseEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hAlphabet (Fin.cases hG (Fin.cases hS (Fin.cases hInv
      (Fin.cases hZero (Fin.cases hOne (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hAlphabet hAlphabet)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalSymbolInverseEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod (externalGeneratorAlphabet G S) (externalGeneratorAlphabet G S)) =
        externalSymbolInverseGraph G S inv := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, externalSymbolInverseGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_externalSymbolInverseEntryFormula 0 1 2 3 4 5 6 _ rfl rfl)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteWordLength
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

namespace BoundedFormula

theorem truth_finiteWordLengthEntryFormula {n} (z omega alphabet words : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (finiteWordLengthEntryFormula z omega alphabet words) env ↔
      ∃ f ∈ env words, ∃ N ∈ env omega,
        env z = ZFSet.pair f N ∧ ZFSet.IsFunc N (env alphabet) f := by
  simp only [finiteWordLengthEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_functionFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem pair_mem_finiteWordLengthGraph (A f N : ZFSet.{u}) :
    ZFSet.pair f N ∈ M.finiteWordLengthGraph A ↔
      f ∈ M.finiteWords A ∧ N ∈ ZFSet.omega ∧ ZFSet.IsFunc N A f := by
  rw [finiteWordLengthGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, g, hg, K, hK, eq, function⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hg, hK, function⟩
  · rintro ⟨hf, hN, function⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hf, hN⟩, f, hf, N, hN, rfl, function⟩

theorem finiteWordLengthGraph_function (A : ZFSet.{u}) :
    ZFSet.IsFunc (M.finiteWords A) ZFSet.omega (M.finiteWordLengthGraph A) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro f hf
  obtain ⟨_, n, function⟩ := (M.mem_finiteWords A f).1 hf
  refine ⟨natSetCode n, (M.pair_mem_finiteWordLengthGraph A f _).2
    ⟨hf, natSetCode_mem_omega n, function⟩, ?_⟩
  intro N entry
  obtain ⟨_, hN, other⟩ := (M.pair_mem_finiteWordLengthGraph A f N).1 entry
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode N).1 hN
  exact congrArg natSetCode (finiteWord_domain_unique other function)

theorem finiteWordLengthGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : M.finiteWordLengthGraph A ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hA
  have space := M.prod_mem pairing unions powers separation hWords hOmega
  let params := extend ZFSet.omega (extend A (extend (M.finiteWords A) Fin.elim0))
  have selected := M.separation_mem separation
    (BoundedFormula.finiteWordLengthEntryFormula 0 1 2 3).toFormula params
    (Fin.cases hOmega (Fin.cases hA (Fin.cases hWords (fun j => Fin.elim0 j)))) space
  have correct (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets (BoundedFormula.finiteWordLengthEntryFormula 0 1 2 3).toFormula
        (extend z params) ↔
      ∃ f ∈ M.finiteWords A, ∃ N ∈ ZFSet.omega,
        z = ZFSet.pair f N ∧ ZFSet.IsFunc N A f :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hz (Fin.cases hOmega (Fin.cases hA (Fin.cases hWords
        (fun j => Fin.elim0 j)))))).trans
      (BoundedFormula.truth_finiteWordLengthEntryFormula 0 1 2 3 _)
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.finiteWordLengthEntryFormula 0 1 2 3).toFormula (extend z params))
      (ZFSet.prod (M.finiteWords A) ZFSet.omega) = M.finiteWordLengthGraph A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finiteWordLengthGraph, ZFSet.mem_sep]
    exact and_congr_right (fun hz => correct z (M.transitive space hz))
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteWordLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula

theorem truth_finiteWordMapEntryFormula {k} (z wordsA wordsB omega a b e : Fin k)
    (env : Fin k → ZFSet.{u}) :
    Truth (finiteWordMapEntryFormula z wordsA wordsB omega a b e) env ↔
      ∃ f ∈ env wordsA, ∃ g ∈ env wordsB, env z = ZFSet.pair f g ∧
        FiniteWordMapCode (env omega) (env a) (env b) (env e) f g := by
  simp only [finiteWordMapEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_finiteWordMapFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pair_mem_finiteWordMapGraph (A B e f g : ZFSet.{u}) :
    ZFSet.pair f g ∈ M.finiteWordMapGraph A B e ↔
      f ∈ M.finiteWords A ∧ g ∈ M.finiteWords B ∧
        FiniteWordMapCode ZFSet.omega A B e f g := by
  rw [finiteWordMapGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, x, hx, y, hy, eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hx, hy, code⟩
  · rintro ⟨hf, hg, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hf, hg⟩, f, hf, g, hg, rfl, code⟩

theorem finiteWordMapGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B e : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets) :
    M.finiteWordMapGraph A B e ∈ M.sets := by
  have hw := M.omega_mem separation infinite
  have hWA := M.finiteWords_mem pairing unions powers separation infinite hA
  have hWB := M.finiteWords_mem pairing unions powers separation infinite hB
  let params := extend ZFSet.omega (extend A (extend B (extend e
    (extend (M.finiteWords A) (extend (M.finiteWords B) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.finiteWordMapEntryFormula 0 5 6 1 2 3 4) params
    (Fin.cases hw (Fin.cases hA (Fin.cases hB (Fin.cases he
      (Fin.cases hWA (Fin.cases hWB (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hWA hWB)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.finiteWordMapEntryFormula 0 5 6 1 2 3 4) (extend z params))
      (ZFSet.prod (M.finiteWords A) (M.finiteWords B)) = M.finiteWordMapGraph A B e := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finiteWordMapGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_finiteWordMapEntryFormula 0 5 6 1 2 3 4 _)
  exact eq ▸ selected

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable {B D : Type u} (s : Presentation B) (t : Presentation D) (e : B → D)
variable (hB : s.carrier ∈ M.sets) (hD : t.carrier ∈ M.sets)

theorem finiteWordMapGraph_eq_graph :
    M.finiteWordMapGraph s.carrier t.carrier (s.graph t e) =
      (finiteWordPresentation s M pairing unions separation infinite hB).graph
        (finiteWordPresentation t M pairing unions separation infinite hD) (List.map e) := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  change z ∈ M.finiteWordMapGraph s.carrier t.carrier (s.graph t e) ↔
    ∃ xs, ZFSet.pair (finiteWordGraph s xs) (finiteWordGraph t (xs.map e)) = z
  constructor
  · intro hz
    obtain ⟨f, hf, g, hg, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    obtain ⟨xs, rfl⟩ := (finiteWords_exact_lists s M pairing unions separation infinite hB f).1 hf
    obtain ⟨ys, rfl⟩ := (finiteWords_exact_lists t M pairing unions separation infinite hD g).1 hg
    have code := ((M.pair_mem_finiteWordMapGraph _ _ _ _ _).1 hz).2.2
    have eq := (finiteWordMapCode_iff s t e xs ys).1 code
    subst ys
    exact ⟨xs, rfl⟩
  · rintro ⟨xs, rfl⟩
    exact (M.pair_mem_finiteWordMapGraph _ _ _ _ _).2
      ⟨finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs,
        finiteWordGraph_mem_finiteWords t M pairing unions separation infinite hD (xs.map e),
        (finiteWordMapCode_iff s t e xs (xs.map e)).2 rfl⟩

end TransitiveGround





namespace BoundedFormula

theorem truth_finiteWordAppendEntryFormula {n} (z words alphabet omega add : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (finiteWordAppendEntryFormula z words alphabet omega add) env ↔
      ∃ f ∈ env words, ∃ g ∈ env words, ∃ h ∈ env words,
        env z = ZFSet.pair (ZFSet.pair f g) h ∧
          FiniteWordAppendCode (env alphabet) (env omega) (env add) f g h := by
  simp only [finiteWordAppendEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_finiteWordAppendFormula]
  rfl

theorem truth_finiteWordReverseEntryFormula {n} (z words alphabet omega add : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (finiteWordReverseEntryFormula z words alphabet omega add) env ↔
      ∃ f ∈ env words, ∃ h ∈ env words, env z = ZFSet.pair f h ∧
        FiniteWordReverseCode (env alphabet) (env omega) (env add) f h := by
  simp only [finiteWordReverseEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_finiteWordReverseFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem pair_mem_finiteWordReverseGraph (A f h : ZFSet.{u}) :
    ZFSet.pair f h ∈ M.finiteWordReverseGraph A ↔
      f ∈ M.finiteWords A ∧ h ∈ M.finiteWords A ∧
        FiniteWordReverseCode A ZFSet.omega natAddGraph f h := by
  rw [finiteWordReverseGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, f', hf, h', hh, eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hf, hh, code⟩
  · rintro ⟨hf, hh, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hf, hh⟩, f, hf, h, hh, rfl, code⟩

theorem finiteWordAppendGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : M.finiteWordAppendGraph A ∈ M.sets := by
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hA
  have hOmega := M.omega_mem separation infinite
  have hAdd := M.natAddGraph_mem pairing unions powers separation infinite
  have domain := M.prod_mem pairing unions powers separation hWords hWords
  have bound := M.prod_mem pairing unions powers separation domain hWords
  let params := extend (M.finiteWords A) (extend A (extend ZFSet.omega (extend natAddGraph Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.finiteWordAppendEntryFormula 0 1 2 3 4) params
    (Fin.cases hWords (Fin.cases hA (Fin.cases hOmega (Fin.cases hAdd (fun j => Fin.elim0 j))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.finiteWordAppendEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod (M.finiteWords A) (M.finiteWords A)) (M.finiteWords A)) =
        M.finiteWordAppendGraph A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finiteWordAppendGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_finiteWordAppendEntryFormula 0 1 2 3 4 _)
  exact eq ▸ selected

theorem finiteWordReverseGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : M.finiteWordReverseGraph A ∈ M.sets := by
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hA
  have hOmega := M.omega_mem separation infinite
  have hAdd := M.natAddGraph_mem pairing unions powers separation infinite
  have bound := M.prod_mem pairing unions powers separation hWords hWords
  let params := extend (M.finiteWords A) (extend A (extend ZFSet.omega (extend natAddGraph Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.finiteWordReverseEntryFormula 0 1 2 3 4) params
    (Fin.cases hWords (Fin.cases hA (Fin.cases hOmega (Fin.cases hAdd (fun j => Fin.elim0 j))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.finiteWordReverseEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (M.finiteWords A) (M.finiteWords A)) = M.finiteWordReverseGraph A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finiteWordReverseGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_finiteWordReverseEntryFormula 0 1 2 3 4 _)
  exact eq ▸ selected

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

theorem finiteWordReverseGraph_eq_graph {B : Type u} (s : Presentation B)
    (hB : s.carrier ∈ M.sets) :
    M.finiteWordReverseGraph s.carrier =
      (finiteWordPresentation s M pairing unions separation infinite hB).graph
        (finiteWordPresentation s M pairing unions separation infinite hB) List.reverse := by
  apply ZFSet.ext
  intro z
  rw [Presentation.mem_graph]
  change z ∈ M.finiteWordReverseGraph s.carrier ↔
    ∃ xs : List B, ZFSet.pair (finiteWordGraph s xs) (finiteWordGraph s xs.reverse) = z
  constructor
  · intro hz
    obtain ⟨f, hf, h, _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    obtain ⟨xs, rfl⟩ := (finiteWords_exact_lists s M pairing unions separation infinite hB f).1 hf
    have code := ((M.pair_mem_finiteWordReverseGraph _ _ _).1 hz).2.2
    have eq := (finiteWordReverseCode_iff s xs h).1 code
    subst h
    exact ⟨xs, rfl⟩
  · rintro ⟨xs, rfl⟩
    exact (M.pair_mem_finiteWordReverseGraph _ _ _).2
      ⟨finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs,
        finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs.reverse,
        finiteWordGraph_reverse_code s xs⟩

include pairing unions separation infinite in
theorem finiteWordAppendGraph_function {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ZFSet.IsFunc (ZFSet.prod (M.finiteWords A) (M.finiteWords A)) (M.finiteWords A)
      (M.finiteWordAppendGraph A) := by
  let s := SetMembers.presentation A
  change ZFSet.IsFunc (ZFSet.prod (M.finiteWords s.carrier) (M.finiteWords s.carrier))
    (M.finiteWords s.carrier) (M.finiteWordAppendGraph s.carrier)
  rw [M.finiteWordAppendGraph_eq_graph pairing unions separation infinite s hA]
  exact ((finiteWordPresentation s M pairing unions separation infinite hA).product
    (finiteWordPresentation s M pairing unions separation infinite hA)).graph_isFunc
      (finiteWordPresentation s M pairing unions separation infinite hA) _

include pairing unions separation infinite in
theorem finiteWordReverseGraph_function {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ZFSet.IsFunc (M.finiteWords A) (M.finiteWords A) (M.finiteWordReverseGraph A) := by
  let s := SetMembers.presentation A
  change ZFSet.IsFunc (M.finiteWords s.carrier) (M.finiteWords s.carrier)
    (M.finiteWordReverseGraph s.carrier)
  rw [M.finiteWordReverseGraph_eq_graph pairing unions separation infinite s hA]
  exact (finiteWordPresentation s M pairing unions separation infinite hA).graph_isFunc
    (finiteWordPresentation s M pairing unions separation infinite hA) _

end TransitiveGround






private theorem compose_presentation_graphs {A B C : Type u}
    (s : Presentation A) (t : Presentation B) (v : Presentation C) (f : A → B) (g : B → C) :
    relationCompose s.carrier t.carrier v.carrier (s.graph t f) (t.graph v g) =
      s.graph v (fun x => g (f x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_relationCompose, Presentation.mem_graph]
  constructor
  · rintro ⟨x, hx, y, hy, w, hw, rfl, first, second⟩
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (t.mem_carrier y).1 hy
    obtain ⟨c, rfl⟩ := (v.mem_carrier w).1 hw
    have ab := (s.pair_mem_graph t f a b).1 first
    have bc := (t.pair_mem_graph v g b c).1 second
    subst b
    subst c
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨s.encode a, s.encode_mem a, t.encode (f a), t.encode_mem (f a),
      v.encode (g (f a)), v.encode_mem (g (f a)), rfl,
      (s.pair_mem_graph t f a (f a)).2 rfl,
      (t.pair_mem_graph v g (f a) (g (f a))).2 rfl⟩

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem externalInverseWordGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {G S inv : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hInv : inv ∈ M.sets) :
    M.externalInverseWordGraph G S inv ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hSymbols := M.externalSymbolInverseGraph_mem pairing unions powers separation hG hS hInv
  exact M.relationCompose_mem pairing unions powers separation hWords hWords hWords
    (M.finiteWordMapGraph_mem pairing unions powers separation infinite hAlphabet hAlphabet hSymbols)
    (M.finiteWordReverseGraph_mem pairing unions powers separation infinite hAlphabet)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {J L : Type u} [Inv J] (s : Presentation J) (t : Presentation L)
variable (hAlphabet : externalGeneratorAlphabet s.carrier t.carrier ∈ M.sets)

theorem externalInverseWordGraph_eq_graph :
    M.externalInverseWordGraph s.carrier t.carrier (s.graph s Inv.inv) =
      (finiteWordPresentation (externalGeneratorAlphabetPresentation s t)
        M pairing unions separation infinite hAlphabet).graph
      (finiteWordPresentation (externalGeneratorAlphabetPresentation s t)
        M pairing unions separation infinite hAlphabet) externalWordInverse := by
  unfold externalInverseWordGraph
  dsimp only
  rw [externalSymbolInverseGraph_eq_graph]
  have mapEq := M.finiteWordMapGraph_eq_graph pairing unions separation infinite
    (externalGeneratorAlphabetPresentation s t) (externalGeneratorAlphabetPresentation s t)
    externalSymbolInverse hAlphabet hAlphabet
  change M.finiteWordMapGraph (externalGeneratorAlphabet s.carrier t.carrier)
    (externalGeneratorAlphabet s.carrier t.carrier)
    ((externalGeneratorAlphabetPresentation s t).graph
      (externalGeneratorAlphabetPresentation s t) externalSymbolInverse) = _ at mapEq
  rw [mapEq]
  have reverseEq := M.finiteWordReverseGraph_eq_graph pairing unions separation infinite
    (externalGeneratorAlphabetPresentation s t) hAlphabet
  change M.finiteWordReverseGraph (externalGeneratorAlphabet s.carrier t.carrier) = _ at reverseEq
  rw [reverseEq]
  let p := finiteWordPresentation (externalGeneratorAlphabetPresentation s t)
    M pairing unions separation infinite hAlphabet
  exact compose_presentation_graphs p p p (List.map externalSymbolInverse) List.reverse

end TransitiveGround

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

theorem taggedBirth_old_iff {P N birth stamp x t : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair x t ∈ taggedBirth P N birth stamp ↔ ZFSet.pair x t ∈ birth := by
  rw [pair_mem_taggedBirth]
  exact ⟨fun h => h.elim id (fun h => False.elim (taggedExtension_disjoint P N x hx h.1)), Or.inl⟩

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ActionPostcompositionCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem actionPostcompose_subset (P A g base : ZFSet.{u}) :
    actionPostcompose P A g base ⊆ ZFSet.prod P P :=
  fun _ hv => (ZFSet.mem_sep.1 hv).1

theorem pair_mem_actionPostcompose (P A g base x z : ZFSet.{u}) :
    ZFSet.pair x z ∈ actionPostcompose P A g base ↔
      x ∈ P ∧ z ∈ P ∧ ∃ y ∈ P,
        ZFSet.pair x y ∈ base ∧ ZFSet.pair (ZFSet.pair g y) z ∈ A := by
  rw [actionPostcompose, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hz⟩, a, _, b, _, equal, witness⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hx, hz, witness⟩
  · rintro ⟨hx, hz, witness⟩
    exact ⟨⟨hx, hz⟩, x, hx, z, hz, rfl, witness⟩

theorem PosetActionCode.raw_mul_iff {G P m e r A g h k x z : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m) (hx : x ∈ P) (hz : z ∈ P) :
    ZFSet.pair (ZFSet.pair k x) z ∈ A ↔
      ∃ y ∈ P, ZFSet.pair (ZFSet.pair h x) y ∈ A ∧ ZFSet.pair (ZFSet.pair g y) z ∈ A := by
  constructor
  · intro entry
    obtain ⟨y, first, _⟩ := action.function.2 (ZFSet.pair h x)
      (ZFSet.pair_mem_prod.2 ⟨hh, hx⟩)
    have hy := (ZFSet.pair_mem_prod.1 (action.function.1 first)).2
    obtain ⟨w, second, _⟩ := action.function.2 (ZFSet.pair g y)
      (ZFSet.pair_mem_prod.2 ⟨hg, hy⟩)
    have hw := (ZFSet.pair_mem_prod.1 (action.function.1 second)).2
    have composed := action.mul g hg h hh k hk x hx y hy w hw product first second
    obtain ⟨v, _, unique⟩ := action.function.2 (ZFSet.pair k x)
      (ZFSet.pair_mem_prod.2 ⟨hk, hx⟩)
    have equal : w = z := (unique w composed).trans (unique z entry).symm
    exact ⟨y, hy, first, equal ▸ second⟩
  · rintro ⟨y, hy, first, second⟩
    exact action.mul g hg h hh k hk x hx y hy z hz product first second

theorem actionPostcompose_one {G P m e r A base : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (shape : base ⊆ ZFSet.prod P P) :
    actionPostcompose P A e base = base := by
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨x, _, z, _, rfl⟩ := ZFSet.mem_prod.1 (actionPostcompose_subset P A e base hv)
    obtain ⟨_, _, y, hy, entry, acted⟩ := (pair_mem_actionPostcompose P A e base x z).1 hv
    have identity := action.one y hy
    obtain ⟨w, _, unique⟩ := action.function.2 (ZFSet.pair e y)
      (ZFSet.pair_mem_prod.1 (action.function.1 identity)).1
    have equal : z = y := (unique z acted).trans (unique y identity).symm
    exact equal.symm ▸ entry
  · intro hv
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (shape hv)
    exact (pair_mem_actionPostcompose P A e base x y).2
      ⟨hx, hy, y, hy, hv, action.one y hy⟩

theorem actionPostcompose_mul {G P m e r A base g h k : ZFSet.{u}}
    (action : PosetActionCode G P m e r A)
    (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m) :
    actionPostcompose P A k base = actionPostcompose P A g (actionPostcompose P A h base) := by
  apply ZFSet.ext
  intro v
  constructor
  · intro hv
    obtain ⟨x, _, z, _, rfl⟩ := ZFSet.mem_prod.1 (actionPostcompose_subset P A k base hv)
    obtain ⟨hx, hz, y, hy, entry, acted⟩ := (pair_mem_actionPostcompose P A k base x z).1 hv
    obtain ⟨w, hw, first, second⟩ := (action.raw_mul_iff hg hh hk product hy hz).1 acted
    exact (pair_mem_actionPostcompose P A g (actionPostcompose P A h base) x z).2
      ⟨hx, hz, w, hw, (pair_mem_actionPostcompose P A h base x w).2
        ⟨hx, hw, y, hy, entry, first⟩, second⟩
  · intro hv
    obtain ⟨x, _, z, _, rfl⟩ := ZFSet.mem_prod.1
      (actionPostcompose_subset P A g (actionPostcompose P A h base) hv)
    obtain ⟨hx, hz, w, hw, entry, acted⟩ :=
      (pair_mem_actionPostcompose P A g (actionPostcompose P A h base) x z).1 hv
    obtain ⟨_, _, y, hy, first, second⟩ := (pair_mem_actionPostcompose P A h base x w).1 entry
    exact (pair_mem_actionPostcompose P A k base x z).2
      ⟨hx, hz, y, hy, first, (action.raw_mul_iff hg hh hk product hy hz).2
        ⟨w, hw, second, acted⟩⟩

theorem RestrictedActionCode.transport {G P m e r A g δ k source target target' base : ZFSet.{u}}
    (code : RestrictedActionCode P r A g source target base)
    (action : PosetActionCode G P m e r A)
    (hg : g ∈ G) (hδ : δ ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair δ g) k ∈ m)
    (targetEntry : ZFSet.pair (ZFSet.pair δ target) target' ∈ A) :
    RestrictedActionCode P r A k source target' (actionPostcompose P A δ base) := by
  have firstShape := ZFSet.pair_mem_prod.1 (action.function.1 code.target_entry)
  have hsource := (ZFSet.pair_mem_prod.1 firstShape.1).2
  have htarget := firstShape.2
  have htarget' := (ZFSet.pair_mem_prod.1 (action.function.1 targetEntry)).2
  refine ⟨actionPostcompose_subset P A δ base,
    action.mul δ hδ g hg k hk source hsource target htarget target' htarget'
      product code.target_entry targetEntry, ?_⟩
  intro x hx z hz
  rw [pair_mem_actionPostcompose]
  constructor
  · rintro ⟨_, _, y, hy, entry, acted⟩
    have old := (code.entries x hx y hy).1 entry
    exact ⟨old.1, (action.raw_mul_iff hδ hg hk product hx hz).2 ⟨y, hy, old.2, acted⟩⟩
  · rintro ⟨lower, entry⟩
    obtain ⟨y, hy, first, second⟩ := (action.raw_mul_iff hδ hg hk product hx hz).1 entry
    exact ⟨hx, hz, y, hy, (code.entries x hx y hy).2 ⟨lower, first⟩, second⟩

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedFilterImages
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

theorem mem_actionImage (P A g F y : ZFSet.{u}) :
    y ∈ actionImage P A g F ↔
      y ∈ P ∧ ∃ x ∈ F, ZFSet.pair (ZFSet.pair g x) y ∈ A :=
  ZFSet.mem_sep

theorem actionImage_subset (P A g F : ZFSet.{u}) : actionImage P A g F ⊆ P :=
  fun y hy => ((mem_actionImage P A g F y).1 hy).1

theorem actionImage_one {G P m e r A F : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subset : F ⊆ P) :
    actionImage P A e F = F := by
  apply ZFSet.ext
  intro y
  constructor
  · intro hy
    obtain ⟨_, x, hx, entry⟩ := (mem_actionImage P A e F y).1 hy
    obtain ⟨z, _, unique⟩ := action.function.2 (ZFSet.pair e x)
      (ZFSet.pair_mem_prod.1 (action.function.1 (action.one x (subset hx)))).1
    have equal : y = x := (unique y entry).trans (unique x (action.one x (subset hx))).symm
    exact equal.symm ▸ hx
  · intro hy
    exact (mem_actionImage P A e F y).2 ⟨subset hy, y, hy, action.one y (subset hy)⟩

theorem actionImage_mul {G P m e r A F g h k : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subset : F ⊆ P)
    (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m) :
    actionImage P A k F = actionImage P A g (actionImage P A h F) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hzP, x, hx, entry⟩ := (mem_actionImage P A k F z).1 hz
    obtain ⟨y, hy, _⟩ := action.function.2 (ZFSet.pair h x) (ZFSet.pair_mem_prod.2 ⟨hh, subset hx⟩)
    have hyP := (ZFSet.pair_mem_prod.1 (action.function.1 hy)).2
    obtain ⟨w, hw, _⟩ := action.function.2 (ZFSet.pair g y) (ZFSet.pair_mem_prod.2 ⟨hg, hyP⟩)
    have hwP := (ZFSet.pair_mem_prod.1 (action.function.1 hw)).2
    have composed := action.mul g hg h hh k hk x (subset hx) y hyP w hwP product hy hw
    obtain ⟨v, _, unique⟩ := action.function.2 (ZFSet.pair k x) (ZFSet.pair_mem_prod.2 ⟨hk, subset hx⟩)
    have equal : w = z := (unique w composed).trans (unique z entry).symm
    exact (mem_actionImage P A g (actionImage P A h F) z).2
      ⟨hzP, y, (mem_actionImage P A h F y).2 ⟨hyP, x, hx, hy⟩, equal ▸ hw⟩
  · intro hz
    obtain ⟨hzP, y, hy, entry⟩ := (mem_actionImage P A g (actionImage P A h F) z).1 hz
    obtain ⟨hyP, x, hx, first⟩ := (mem_actionImage P A h F y).1 hy
    exact (mem_actionImage P A k F z).2
      ⟨hzP, x, hx, action.mul g hg h hh k hk x (subset hx) y hyP z hzP product first entry⟩

theorem actionImage_lower_bound {G P m e r A F g s t : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subset : F ⊆ P)
    (hg : g ∈ G) (hs : s ∈ P) (entry : ZFSet.pair (ZFSet.pair g s) t ∈ A)
    (lower : ∀ x ∈ F, ZFSet.pair s x ∈ r) :
    ∀ y ∈ actionImage P A g F, ZFSet.pair t y ∈ r := by
  intro y hy
  obtain ⟨hyP, x, hx, acted⟩ := (mem_actionImage P A g F y).1 hy
  have ht := (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2
  exact action.monotone g hg s hs x (subset hx) t ht y hyP entry acted (lower x hx)

theorem actionImage_filter {G P m inv e r μ A F g : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (filter : MeetFilterCode P r μ F) :
    MeetFilterCode P r μ (actionImage P A g F) := by
  refine ⟨actionImage_subset P A g F, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := filter.nonempty
    obtain ⟨y, entry, _⟩ := action.function.2 (ZFSet.pair g x)
      (ZFSet.pair_mem_prod.2 ⟨hg, filter.subset hx⟩)
    exact ⟨y, (mem_actionImage P A g F y).2
      ⟨(ZFSet.pair_mem_prod.1 (action.function.1 entry)).2, x, hx, entry⟩⟩
  · intro x hx y hy lower
    obtain ⟨_, a, ha, first⟩ := (mem_actionImage P A g F x).1 hx
    obtain ⟨b, hb, second⟩ := action.raw_preimage group hg hy
    exact (mem_actionImage P A g F y).2
      ⟨hy, b, filter.upward a ha b hb ((action.raw_order_iff group meet.order hg first second).1 lower),
        second⟩
  · intro x hx y hy z entry
    obtain ⟨hxP, a, ha, first⟩ := (mem_actionImage P A g F x).1 hx
    obtain ⟨hyP, b, hb, second⟩ := (mem_actionImage P A g F y).1 hy
    obtain ⟨c, oldMeet, _⟩ := meet.operation.2 (ZFSet.pair a b)
      (ZFSet.pair_mem_prod.2 ⟨filter.subset ha, filter.subset hb⟩)
    have hc := filter.closed_meet a ha b hb c oldMeet
    obtain ⟨d, third, _⟩ := action.function.2 (ZFSet.pair g c)
      (ZFSet.pair_mem_prod.2 ⟨hg, filter.subset hc⟩)
    have newMeet := action.raw_map_meet group meet hg oldMeet first second third
    obtain ⟨w, _, unique⟩ := meet.operation.2 (ZFSet.pair x y)
      (ZFSet.pair_mem_prod.2 ⟨hxP, hyP⟩)
    have equal : d = z := (unique d newMeet).trans (unique z entry).symm
    exact (mem_actionImage P A g F z).2
      ⟨(ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2, c, hc, equal ▸ third⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedRangeCompletion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace CompressionRangeAccounting
variable {P0 I U R MU Maps Bases Caps : ZFSet.{u}}
variable (accounting : CompressionRangeAccounting P0 I U R MU Maps Bases Caps)
include accounting

theorem range_completion (meet : MeetOrderCode U R MU) (maps : FunctionGraphOn I Maps)
    (embeddings : ∀ i f, ZFSet.pair i f ∈ Maps → MeetEmbeddingCode U U R R MU MU f)
    (bases : ZFSet.IsFunc I U Bases) (caps : ZFSet.IsFunc I U Caps) :
    ∀ i ∈ I, ∀ f k, ZFSet.pair i f ∈ Maps → ZFSet.pair i k ∈ Caps →
      ∀ x ∈ U, ZFSet.pair x k ∈ R → ∃ y ∈ U, ZFSet.pair y x ∈ f := by
  let baseGraph : FunctionGraphOn I Bases := ⟨U, bases⟩
  let capGraph : FunctionGraphOn I Caps := ⟨U, caps⟩
  let base (i : {i : ZFSet.{u} // i ∈ I}) : {x : ZFSet.{u} // x ∈ U} :=
    ⟨baseGraph.value i, (ZFSet.pair_mem_prod.1 (bases.1 (baseGraph.value_entry i))).2⟩
  let cap (i : {i : ZFSet.{u} // i ∈ I}) : {x : ZFSet.{u} // x ∈ U} :=
    ⟨capGraph.value i, (ZFSet.pair_mem_prod.1 (caps.1 (capGraph.value_entry i))).2⟩
  let embedding (i : {i : ZFSet.{u} // i ∈ I}) :=
    embeddings i.val (maps.value i) (maps.value_entry i)
  let s (i : {i : ZFSet.{u} // i ∈ I}) := (embedding i).toMeetEmbedding meet meet
  have baseFilled : ∀ i x, meet.toMeetOrder.le x (base i) → ∃ y, (s i).toFun y = x := by
    intro i x below
    obtain ⟨y, hy, entry⟩ := accounting.base_filled i.val i.property
      (maps.value i) (base i).val (maps.value_entry i) (baseGraph.value_entry i) x.val x.property below
    exact ⟨⟨y, hy⟩, ((embedding i).toMeetEmbedding_eq_iff meet meet ⟨y, hy⟩ x).2 entry⟩
  have shadow : ∀ i x, x.val ∈ P0 → meet.toMeetOrder.le x (cap i) →
      meet.toMeetOrder.le x (base i) := by
    intro i x original below
    exact accounting.old_shadow i.val i.property (base i).val (cap i).val
      (baseGraph.value_entry i) (capGraph.value_entry i) x.val original below
  have separation : ∀ i j, i ≠ j →
      meet.toMeetOrder.le (cap i) (base j) ∨ meet.toMeetOrder.le (cap j) (base i) ∨
      meet.toMeetOrder.meet (cap i) (cap j) = meet.toMeetOrder.meet (base i) (base j) := by
    intro i j different
    have rawDifferent : i.val ≠ j.val := fun equal => different (Subtype.ext equal)
    rcases accounting.cap_separation i.val i.property j.val j.property rawDifferent
      (base i).val (base j).val (cap i).val (cap j).val
      (baseGraph.value_entry i) (baseGraph.value_entry j)
      (capGraph.value_entry i) (capGraph.value_entry j) with first | second | common
    · exact Or.inl first
    · exact Or.inr (Or.inl second)
    · obtain ⟨z, capsMeet, basesMeet⟩ := common
      apply Or.inr ∘ Or.inr
      apply Subtype.ext
      let operation : FunctionGraphOn (ZFSet.prod U U) MU := ⟨U, meet.operation⟩
      exact (operation.unique (meet.toMeetOrder_meet_entry (cap i) (cap j)) capsMeet).trans
        (operation.unique (meet.toMeetOrder_meet_entry (base i) (base j)) basesMeet).symm
  have accounted : ∀ x : {x : ZFSet.{u} // x ∈ U}, x.val ∈ P0 ∨
      ∃ j y, (s j).toFun y = x ∧ meet.toMeetOrder.le x (cap j) ∧ ¬ meet.toMeetOrder.le x (base j) := by
    intro x
    rcases accounting.fresh_accounting x.val x.property with original | fresh
    · exact Or.inl original
    · obtain ⟨j, hj, f, k, b, y, hy, indexed, capped, based, entry, below, outside⟩ := fresh
      let i : {i : ZFSet.{u} // i ∈ I} := ⟨j, hj⟩
      have fEq := maps.value_eq_of_entry i indexed
      have kEq := capGraph.value_eq_of_entry i capped
      have bEq := baseGraph.value_eq_of_entry i based
      refine Or.inr ⟨i, ⟨y, hy⟩, ?_, ?_, ?_⟩
      · apply ((embedding i).toMeetEmbedding_eq_iff meet meet ⟨y, hy⟩ x).2
        exact fEq.symm ▸ entry
      · change ZFSet.pair x.val (capGraph.value i) ∈ R
        exact kEq.symm ▸ below
      · change ZFSet.pair x.val (baseGraph.value i) ∉ R
        exact bEq.symm ▸ outside
  have complete := Compression.range_completion_from_accounting meet.toMeetOrder
    (fun x => x.val ∈ P0) base cap (fun i => (s i).toFun) baseFilled shadow separation accounted
  intro i hi f k indexed capped x hx below
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have fEq := maps.value_eq_of_entry j indexed
  have kEq := capGraph.value_eq_of_entry j capped
  obtain ⟨y, equal⟩ := complete j ⟨x, hx⟩ (show ZFSet.pair x (capGraph.value j) ∈ R from kEq.symm ▸ below)
  refine ⟨y.val, y.property, ?_⟩
  have entry := ((embedding j).toMeetEmbedding_eq_iff meet meet y ⟨x, hx⟩).1 equal
  exact fEq ▸ entry

theorem range_iff (meet : MeetOrderCode U R MU) (maps : FunctionGraphOn I Maps)
    (embeddings : ∀ i f, ZFSet.pair i f ∈ Maps → MeetEmbeddingCode U U R R MU MU f)
    (bases : ZFSet.IsFunc I U Bases) (caps : ZFSet.IsFunc I U Caps)
    (bounded : ∀ i ∈ I, ∀ f k, ZFSet.pair i f ∈ Maps → ZFSet.pair i k ∈ Caps →
      ∀ x y, ZFSet.pair x y ∈ f → ZFSet.pair y k ∈ R)
    {i f k x : ZFSet.{u}} (hi : i ∈ I) (indexed : ZFSet.pair i f ∈ Maps)
    (capped : ZFSet.pair i k ∈ Caps) :
    (∃ y ∈ U, ZFSet.pair y x ∈ f) ↔ x ∈ U ∧ ZFSet.pair x k ∈ R := by
  constructor
  · rintro ⟨y, _, entry⟩
    exact ⟨(ZFSet.pair_mem_prod.1 ((embeddings i f indexed).injection.function.1 entry)).2,
      bounded i hi f k indexed capped y x entry⟩
  · rintro ⟨hx, below⟩
    exact accounting.range_completion meet maps embeddings bases caps i hi f k indexed capped x hx below

end CompressionRangeAccounting

end PartitionPilot.Forcing

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





namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_naturalStepFormula {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {a p y base : ZFSet.{u}} (ha : a ∈ M.sets) (hp : p ∈ M.sets)
    (hy : y ∈ M.sets) (hb : base ∈ M.sets) :
    Realize M.sets (naturalStepFormula φ) (extend a (extend p (extend y (extend base params)))) ↔
      (a = ∅ ∧ y = base) ∨ ∃ m ∈ M.sets, ∃ x ∈ M.sets,
        a = insert m m ∧ ZFSet.pair m x ∈ p ∧
          Realize M.sets φ (extend x (extend y params)) := by
  have mem4 : ∀ i, extend a (extend p (extend y (extend base params))) i ∈ M.sets :=
    Fin.cases ha (Fin.cases hp (Fin.cases hy (Fin.cases hb members)))
  rw [naturalStepFormula, realize_disj]
  apply or_congr
  · change (Realize M.sets (BoundedFormula.emptyFormula 0).toFormula _ ∧ y = base) ↔ _
    exact and_congr ((BoundedFormula.realize_toFormula M _ _ mem4).trans
      (BoundedFormula.truth_emptyFormula _ _)) Iff.rfl
  · rw [realize_ex]
    apply exists_congr
    intro m
    apply and_congr_right
    intro hm
    rw [realize_ex]
    apply exists_congr
    intro x
    apply and_congr_right
    intro hx
    have mem6 : ∀ i, extend x (extend m (extend a (extend p (extend y (extend base params))))) i ∈ M.sets :=
      Fin.cases hx (Fin.cases hm mem4)
    change (Realize M.sets (BoundedFormula.successorFormula 2 1).toFormula _ ∧
      Realize M.sets (BoundedFormula.pairMembershipFormula 1 0 3).toFormula _ ∧ _) ↔ _
    rw [BoundedFormula.realize_toFormula M _ _ mem6, BoundedFormula.truth_successorFormula,
      BoundedFormula.realize_toFormula M _ _ mem6, BoundedFormula.truth_pairMembershipFormula,
      realize_reindex, map_extend, map_extend]
    rfl

end TransitiveGround

theorem natSetCode_succ_eq_insert_iff (n : Nat) (x : ZFSet.{u}) :
    natSetCode (n + 1) = insert x x ↔ x = natSetCode n := by
  constructor
  · intro equal
    have member : x ∈ natSetCode (n + 1) := equal.symm ▸ ZFSet.mem_insert x x
    obtain ⟨j, _, rfl⟩ := (mem_natSetCode x (n + 1)).1 member
    have codes : natSetCode (n + 1) = natSetCode (j + 1) := equal
    exact congrArg natSetCode (Nat.add_right_cancel (natSetCode_injective codes)).symm
  · rintro rfl
    rfl


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IntervalSequenceFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing

universe u

theorem leastIntervalNextCandidate_unique {N A D rA rD e lo hi p c x y : ZFSet.{u}}
    (injection : InjectionCode D ZFSet.omega c)
    (hx : leastIntervalNextCandidate N A D rA rD e lo hi p c x)
    (hy : leastIntervalNextCandidate N A D rA rD e lo hi p c y) : x = y := by
  obtain ⟨xValid, n, hn, xn, leastX⟩ := hx
  obtain ⟨yValid, m, hm, ym, leastY⟩ := hy
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rcases lt_trichotomy k l with smaller | equal | larger
  · exact False.elim (leastY x xValid.1 xValid (natSetCode k)
      ((natSetCode_mem_iff k l).2 smaller) xn)
  · subst l
    exact injection.injective x y (natSetCode k) xn ym
  · exact False.elim (leastX y yValid.1 yValid (natSetCode l)
      ((natSetCode_mem_iff l k).2 larger) ym)

theorem leastIntervalNextCandidate_exists_unique {N A D rA rD e lo hi p c : ZFSet.{u}}
    (injection : InjectionCode D ZFSet.omega c)
    (candidate : ∃ y, intervalNextCandidate N A D rA rD e lo hi p y) :
    ∃! y, leastIntervalNextCandidate N A D rA rD e lo hi p c y := by
  classical
  let valid : Nat → Prop := fun n => ∃ y, intervalNextCandidate N A D rA rD e lo hi p y ∧
    ZFSet.pair y (natSetCode n) ∈ c
  have existsValid : ∃ n, valid n := by
    obtain ⟨y, hy⟩ := candidate
    obtain ⟨a, entry, _⟩ := injection.function.2 y hy.1
    have aNat := (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode a).1 aNat
    exact ⟨n, y, hy, entry⟩
  obtain ⟨y, hy, entry⟩ := Nat.find_spec existsValid
  have selected : leastIntervalNextCandidate N A D rA rD e lo hi p c y := by
    refine ⟨hy, natSetCode (Nat.find existsValid), natSetCode_mem_omega _, entry, ?_⟩
    intro z _ hz m hm smaller
    obtain ⟨k, lower, equal⟩ := (mem_natSetCode m (Nat.find existsValid)).1 hm
    have validK : valid k := ⟨z, hz, equal ▸ smaller⟩
    exact Nat.not_lt_of_ge (Nat.find_min' existsValid validK) lower
  exact ⟨y, selected, fun z hz => leastIntervalNextCandidate_unique injection hz selected⟩

namespace BoundedFormula

open SetFormula

theorem truth_iffFormula {n} (φ ψ : BoundedFormula n) (env : Fin n → ZFSet.{u}) :
    Truth (iffFormula φ ψ) env ↔ (Truth φ env ↔ Truth ψ env) := by
  simp only [iffFormula, Truth, truth_imp]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

theorem truth_intervalNextCandidateFormula {n} (N A D rA rD e lo hi p y : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalNextCandidateFormula N A D rA rD e lo hi p y) env ↔
      intervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) (env y) := by
  simp only [intervalNextCandidateFormula, Truth, truth_pairMembershipFormula,
    truth_imp, truth_iffFormula]
  rfl

theorem truth_leastIntervalNextCandidateFormula {n} (N A D rA rD e lo hi p c y omega : Fin n)
    (env : Fin n → ZFSet.{u}) (hOmega : env omega = ZFSet.omega) :
    Truth (leastIntervalNextCandidateFormula N A D rA rD e lo hi p c y omega) env ↔
      leastIntervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) (env c) (env y) := by
  simp only [leastIntervalNextCandidateFormula, Truth, truth_exMem, truth_imp,
    truth_pairMembershipFormula, truth_intervalNextCandidateFormula]
  change (intervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
      (env lo) (env hi) (env p) (env y) ∧
    ∃ k ∈ env omega, ZFSet.pair (env y) k ∈ env c ∧
      ∀ z ∈ env D, intervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) z → ∀ m ∈ k, ZFSet.pair z m ∉ env c) ↔ _
  rw [hOmega]
  rfl

theorem realize_leastIntervalNextCandidateFormula (M : TransitiveGround.{u}) {n}
    (N A D rA rD e lo hi p c y omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (hOmega : env omega = ZFSet.omega) :
    Realize M.sets (leastIntervalNextCandidateFormula N A D rA rD e lo hi p c y omega).toFormula env ↔
      leastIntervalNextCandidate (env N) (env A) (env D) (env rA) (env rD) (env e)
        (env lo) (env hi) (env p) (env c) (env y) :=
  (realize_toFormula M _ env members).trans
    (truth_leastIntervalNextCandidateFormula N A D rA rD e lo hi p c y omega env hOmega)

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem realize_intervalSequenceStepFormula (M : TransitiveGround.{u})
    (env : Fin 12 → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (hOmega : env 11 = ZFSet.omega) :
    Realize M.sets intervalSequenceStepFormula env ↔
      leastIntervalNextCandidate (env 0) (env 3) (env 4) (env 5) (env 6) (env 7)
        (env 8) (env 9) (env 1) (env 10) (env 2) :=
  BoundedFormula.realize_leastIntervalNextCandidateFormula M 0 3 4 5 6 7 8 9 1 10 2 11
    env members hOmega

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_FiniteIntervalExtension
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

theorem intervalComparisons_of_preserved {A D rA rD a b z y : ZFSet.{u}}
    (source : StrictLinearOrderCode A rA) (target : StrictLinearOrderCode D rD)
    (ha : a ∈ A) (hb : b ∈ A) (hz : z ∈ D) (hy : y ∈ D)
    (same : a = b → z = y)
    (forward : ZFSet.pair a b ∈ rA → ZFSet.pair z y ∈ rD)
    (backward : ZFSet.pair b a ∈ rA → ZFSet.pair y z ∈ rD) :
    (a = b ↔ z = y) ∧ (ZFSet.pair a b ∈ rA ↔ ZFSet.pair z y ∈ rD) ∧
      (ZFSet.pair b a ∈ rA ↔ ZFSet.pair y z ∈ rD) := by
  refine ⟨⟨same, ?_⟩, ⟨forward, ?_⟩, ⟨backward, ?_⟩⟩
  · intro equal
    rcases source.compare a ha b hb with less | equalSource | more
    · have rel := forward less
      rw [equal] at rel
      exact False.elim (target.irrefl y hy rel)
    · exact equalSource
    · have rel := backward more
      rw [equal] at rel
      exact False.elim (target.irrefl y hy rel)
  · intro rel
    rcases source.compare a ha b hb with less | equal | more
    · exact less
    · rw [same equal] at rel
      exact False.elim (target.irrefl y hy rel)
    · exact False.elim (target.irrefl z hz (target.trans z y z rel (backward more)))
  · intro rel
    rcases source.compare a ha b hb with less | equal | more
    · exact False.elim (target.irrefl y hy (target.trans y z y rel (forward less)))
    · rw [same equal] at rel
      exact False.elim (target.irrefl y hy rel)
    · exact more

theorem finite_intervalNextCandidate_exists
    {A D rA rD e lo hi p : ZFSet.{u}} (n : Nat)
    (code : IntervalSequenceCode (natSetCode n) A D rA rD e lo hi p)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ y, intervalNextCandidate (natSetCode n) A D rA rD e lo hi p y := by
  classical
  let enumerate : Nat → {a : ZFSet.{u} // a ∈ A} := fun k =>
    ⟨Classical.choose (enumeration.2 (natSetCode k) (natSetCode_mem_omega k)),
      (ZFSet.pair_mem_prod.1 (enumeration.1
        (Classical.choose_spec (enumeration.2 (natSetCode k) (natSetCode_mem_omega k))).1)).2⟩
  have enumerateEntry (k : Nat) : ZFSet.pair (natSetCode k) (enumerate k).val ∈ e :=
    (Classical.choose_spec (enumeration.2 (natSetCode k) (natSetCode_mem_omega k))).1
  let value : Nat → {q : ZFSet.{u} // q ∈ D} := fun k =>
    if hk : k < n then
      ⟨Classical.choose (code.function.2 (natSetCode k) ((natSetCode_mem_iff k n).2 hk)),
        (ZFSet.pair_mem_prod.1 (code.function.1
          (Classical.choose_spec (code.function.2 (natSetCode k)
            ((natSetCode_mem_iff k n).2 hk))).1)).2⟩
    else ⟨lo, loD⟩
  have valueEntry (k : Nat) (hk : k < n) :
      ZFSet.pair (natSetCode k) (value k).val ∈ p := by
    dsimp only [value]
    rw [dite_eq_left hk]
    exact (Classical.choose_spec (code.function.2 (natSetCode k)
      ((natSetCode_mem_iff k n).2 hk))).1
  let initial : CountableInterpolation.Partial source.toLinearHeightOrder target.toDenseHeightOrder
      enumerate ⟨lo, loD⟩ ⟨hi, hiD⟩ n := {
    value := value
    lower := fun k hk => (code.inside _ _ (valueEntry k hk)).1
    upper := fun k hk => (code.inside _ _ (valueEntry k hk)).2
    strict := fun i j hi hj less => (code.order _ _ _ _ _ _
      (enumerateEntry i) (enumerateEntry j) (valueEntry i hi) (valueEntry j hj)).1 less
    equal := fun i j hi hj equal => Subtype.ext ((code.agree _ _ _ _ _ _
      (enumerateEntry i) (enumerateEntry j) (valueEntry i hi) (valueEntry j hj)).1
        (congrArg Subtype.val equal)) }
  obtain ⟨y, lower, upper, forward, backward, same⟩ := CountableInterpolation.next_exists initial gap
  refine ⟨y.val, y.property, lower, upper, ?_⟩
  intro i hi a _ b _ z _ ea eb iz
  obtain ⟨k, hk, rfl⟩ := (mem_natSetCode i n).1 hi
  have enumFunction : FunctionGraphOn ZFSet.omega e := ⟨A, enumeration⟩
  have valueFunction : FunctionGraphOn (natSetCode n) p := ⟨D, code.function⟩
  have first : (enumerate k).val = a := enumFunction.unique (enumerateEntry k) ea
  have second : (enumerate n).val = b := enumFunction.unique (enumerateEntry n) eb
  have previous : (value k).val = z := valueFunction.unique (valueEntry k hk) iz
  have comparisons := intervalComparisons_of_preserved source target.toStrictLinearOrderCode
    (enumerate k).property (enumerate n).property (value k).property y.property
    (fun equal => congrArg Subtype.val (same k hk (Subtype.ext equal)))
    (forward k hk) (backward k hk)
  change ((enumerate k).val = (enumerate n).val ↔ (value k).val = y.val) ∧
    (ZFSet.pair (enumerate k).val (enumerate n).val ∈ rA ↔ ZFSet.pair (value k).val y.val ∈ rD) ∧
    (ZFSet.pair (enumerate n).val (enumerate k).val ∈ rA ↔ ZFSet.pair y.val (value k).val ∈ rD)
    at comparisons
  rw [first, second, previous] at comparisons
  exact comparisons

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_IntervalTraceValidity
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem intervalSequence_of_next
    {N A D rA rD e lo hi t : ZFSet.{u}}
    (source : StrictLinearOrderCode A rA) (target : StrictLinearOrderCode D rD)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (natural : N ⊆ ZFSet.omega) (function : FunctionGraphOn N t)
    (next : ∀ i ∈ N, ∀ y, ZFSet.pair i y ∈ t →
      intervalNextCandidate i A D rA rD e lo hi (graphRestriction i t) y) :
    IntervalSequenceCode N A D rA rD e lo hi t := by
  have functionD : ZFSet.IsFunc N D t := by
    refine ⟨?_, function.to_isFunc.2⟩
    intro w hw
    obtain ⟨i, hiN, y, rfl⟩ := function.shape w hw
    exact ZFSet.pair_mem_prod.2 ⟨hiN, (next i hiN y hw).1⟩
  have pairwise : ∀ i j a b q z,
      ZFSet.pair i a ∈ e → ZFSet.pair j b ∈ e →
      ZFSet.pair i q ∈ t → ZFSet.pair j z ∈ t →
      (a = b ↔ q = z) ∧ (ZFSet.pair a b ∈ rA ↔ ZFSet.pair q z ∈ rD) ∧
        (ZFSet.pair b a ∈ rA ↔ ZFSet.pair z q ∈ rD) := by
    intro i j a b q z ia jb iq jz
    have iN := function.pair_source iq
    have jN := function.pair_source jz
    have aA := (ZFSet.pair_mem_prod.1 (enumeration.1 ia)).2
    have bA := (ZFSet.pair_mem_prod.1 (enumeration.1 jb)).2
    have qD := (ZFSet.pair_mem_prod.1 (functionD.1 iq)).2
    have zD := (ZFSet.pair_mem_prod.1 (functionD.1 jz)).2
    obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode i).1 (natural iN)
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode j).1 (natural jN)
    rcases lt_trichotomy m n with earlier | same | later
    · exact (next (natSetCode n) jN z jz).2.2.2
        (natSetCode m) ((natSetCode_mem_iff m n).2 earlier)
        a aA b bA q qD ia jb (pair_mem_graphRestriction.2 ⟨iq,
          (natSetCode_mem_iff m n).2 earlier⟩)
    · subst n
      have equalSource : a = b := (show FunctionGraphOn ZFSet.omega e from ⟨A, enumeration⟩).unique ia jb
      have equalTarget : q = z := function.unique iq jz
      subst b
      subst z
      exact ⟨iff_of_true rfl rfl,
        iff_of_false (source.irrefl a aA) (target.irrefl q qD),
        iff_of_false (source.irrefl a aA) (target.irrefl q qD)⟩
    · have reversed := (next (natSetCode m) iN q iq).2.2.2
        (natSetCode n) ((natSetCode_mem_iff n m).2 later)
        b bA a aA z zD jb ia (pair_mem_graphRestriction.2 ⟨jz,
          (natSetCode_mem_iff n m).2 later⟩)
      exact ⟨by simpa only [eq_comm] using reversed.1, reversed.2.2, reversed.2.1⟩
  refine ⟨functionD, ?_, ?_, ?_⟩
  · intro i y iy
    have candidate := next i (function.pair_source iy) y iy
    exact ⟨candidate.2.1, candidate.2.2.1⟩
  · intro i j a b q z ia jb iq jz
    exact (pairwise i j a b q z ia jb iq jz).1
  · intro i j a b q z ia jb iq jz
    exact (pairwise i j a b q z ia jb iq jz).2.1

end PartitionPilot.Forcing

end

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



namespace PartitionPilot.Forcing

open SetFormula SetRealization
universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem exists_ground_intervalSequence
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A D rA rD e lo hi c : ZFSet.{u}}
    (hA : A ∈ M.sets) (hD : D ∈ M.sets) (hrA : rA ∈ M.sets)
    (hrD : rD ∈ M.sets) (he : e ∈ M.sets) (hc : c ∈ M.sets)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ t ∈ M.sets, IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t ∧
      OrdinalRecursionTrace
        (groundRecursionStep M intervalSequenceStepFormula (intervalSequenceParams A D rA rD e lo hi c))
        ZFSet.omega t ∧
      ∀ s, OrdinalRecursionTrace
        (groundRecursionStep M intervalSequenceStepFormula (intervalSequenceParams A D rA rD e lo hi c))
        ZFSet.omega s → s = t := by
  have hw := M.omega_mem separation infinite
  have hlo := M.transitive hD loD
  have hhi := M.transitive hD hiD
  let params := intervalSequenceParams A D rA rD e lo hi c
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hA (Fin.cases hD (Fin.cases hrA (Fin.cases hrD (Fin.cases he
      (Fin.cases hlo (Fin.cases hhi (Fin.cases hc (Fin.cases hw (fun i => Fin.elim0 i)))))))))
  have decode (N p y : ZFSet.{u}) (hN : N ∈ M.sets) (hp : p ∈ M.sets) (hy : y ∈ M.sets) :
      Realize M.sets intervalSequenceStepFormula (extend N (extend p (extend y params))) ↔
        leastIntervalNextCandidate N A D rA rD e lo hi p c y :=
    M.realize_intervalSequenceStepFormula (extend N (extend p (extend y params)))
      (Fin.cases hN (Fin.cases hp (Fin.cases hy members))) rfl
  have valid {N p : ZFSet.{u}} (natural : N ⊆ ZFSet.omega)
      (trace : OrdinalRecursionTrace (groundRecursionStep M intervalSequenceStepFormula params) N p) :
      IntervalSequenceCode N A D rA rD e lo hi p := by
    apply intervalSequence_of_next source target.toStrictLinearOrderCode enumeration natural trace.1
    intro i hiN y entry
    have step := trace.2 i hiN y entry
    exact ((decode i (graphRestriction i p) y (M.transitive hw (natural hiN))
      step.1 step.2.1).1 step.2.2).1
  have closure : GroundOrdinalStepClosure M ZFSet.omega intervalSequenceStepFormula params := by
    intro N hN p hp trace
    have hNM := M.transitive hw hN
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode N).1 hN
    have natural : natSetCode n ⊆ (ZFSet.omega : ZFSet.{u}) := by
      intro i hiN
      obtain ⟨k, _, rfl⟩ := (mem_natSetCode i n).1 hiN
      exact natSetCode_mem_omega k
    have prefixValid := valid natural trace
    have candidate := finite_intervalNextCandidate_exists n prefixValid enumeration source target
      loD hiD gap
    obtain ⟨y, selected, unique⟩ := leastIntervalNextCandidate_exists_unique injection candidate
    have hy := M.transitive hD selected.1.1
    exact ⟨y, hy, (decode _ p y hNM hp hy).2 selected,
      fun z hz relation => unique z ((decode _ p z hNM hp hz).1 relation)⟩
  have ordinal : ordinalSetProperty (ZFSet.omega : ZFSet.{u}) := by
    rw [← ordinalCode_omega]
    exact ordinalSetProperty_ordinalCode Ordinal.omega0
  obtain ⟨t, ht, trace, unique, _⟩ := M.exists_unique_ordinalRecursionTrace
    pairing unions separation collection hw ordinal intervalSequenceStepFormula params members closure
  exact ⟨t, ht, valid (fun _ hi => hi) trace, trace, unique⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_IntervalEmbeddingFamilyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

theorem leastInjectionMember_unique {A f d b : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f)
    (hd : leastInjectionMember A f d) (hb : leastInjectionMember A f b) : d = b := by
  obtain ⟨dA, n, hn, dn, leastD⟩ := hd
  obtain ⟨bA, m, hm, bm, leastB⟩ := hb
  obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  obtain ⟨l, rfl⟩ := (mem_omega_iff_natSetCode m).1 hm
  rcases lt_trichotomy k l with smaller | equal | larger
  · exact False.elim (leastB d dA (natSetCode k) ((natSetCode_mem_iff k l).2 smaller) dn)
  · subst l
    exact injection.injective d b (natSetCode k) dn bm
  · exact False.elim (leastD b bA (natSetCode l) ((natSetCode_mem_iff l k).2 larger) bm)

theorem leastInjectionMember_exists_unique {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    ∃! d, leastInjectionMember A f d := by
  classical
  let valid : Nat → Prop := fun n => ∃ d ∈ A, ZFSet.pair d (natSetCode n) ∈ f
  have existsValid : ∃ n, valid n := by
    obtain ⟨d, hd⟩ := nonempty
    obtain ⟨n, entry, _⟩ := injection.function.2 d hd
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1
      (ZFSet.pair_mem_prod.1 (injection.function.1 entry)).2
    exact ⟨k, d, hd, entry⟩
  obtain ⟨d, hd, entry⟩ := Nat.find_spec existsValid
  have selected : leastInjectionMember A f d := by
    refine ⟨hd, natSetCode (Nat.find existsValid), natSetCode_mem_omega _, entry, ?_⟩
    intro x hx m hm smaller
    obtain ⟨k, lower, equal⟩ := (mem_natSetCode m (Nat.find existsValid)).1 hm
    have validK : valid k := ⟨x, hx, equal ▸ smaller⟩
    exact Nat.not_lt_of_ge (Nat.find_min' existsValid validK) lower
  exact ⟨d, selected, fun b hb => leastInjectionMember_unique injection hb selected⟩

theorem canonicalEnumerationDefault_least {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    leastInjectionMember A f (canonicalEnumerationDefault A f) := by
  classical
  have existsDefault := (leastInjectionMember_exists_unique injection nonempty).exists
  simpa only [canonicalEnumerationDefault, dite_eq_left existsDefault] using Classical.choose_spec existsDefault

theorem canonicalEnumeration_isFunc {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    ZFSet.IsFunc ZFSet.omega A (canonicalEnumeration A f) :=
  defaultInverse_isFunc injection (canonicalEnumerationDefault_least injection nonempty).1

theorem canonicalEnumeration_onto {A f : ZFSet.{u}}
    (injection : InjectionCode A ZFSet.omega f) :
    ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ canonicalEnumeration A f :=
  defaultInverse_onto injection (canonicalEnumerationDefault A f)

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem canonicalEnumerationDefault_mem {A f : ZFSet.{u}} (hA : A ∈ M.sets)
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    canonicalEnumerationDefault A f ∈ M.sets :=
  M.transitive hA (canonicalEnumerationDefault_least injection nonempty).1

theorem canonicalEnumeration_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (injection : InjectionCode A ZFSet.omega f) (nonempty : A.Nonempty) :
    canonicalEnumeration A f ∈ M.sets :=
  M.defaultInverse_mem pairing unions powers separation hA hOmega hf
    (M.canonicalEnumerationDefault_mem hA injection nonempty)

end TransitiveGround






theorem intervalSequenceGraph_subset (A D e t : ZFSet.{u}) :
    intervalSequenceGraph A D e t ⊆ ZFSet.prod A D :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_intervalSequenceGraph (A D e t z : ZFSet.{u}) :
    z ∈ intervalSequenceGraph A D e t ↔
      ∃ n ∈ ZFSet.omega, ∃ a ∈ A, ∃ q ∈ D,
        z = ZFSet.pair a q ∧ ZFSet.pair n a ∈ e ∧ ZFSet.pair n q ∈ t := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨n, hn, a, ha, q, hq, rfl, en, tn⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨ha, hq⟩, n, hn, a, ha, q, hq, rfl, en, tn⟩

theorem pair_mem_intervalSequenceGraph (A D e t a q : ZFSet.{u}) :
    ZFSet.pair a q ∈ intervalSequenceGraph A D e t ↔
      a ∈ A ∧ q ∈ D ∧ ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e ∧ ZFSet.pair n q ∈ t := by
  rw [mem_intervalSequenceGraph]
  constructor
  · rintro ⟨n, hn, b, hb, z, hz, equal, en, tn⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hb, hz, n, hn, en, tn⟩
  · rintro ⟨ha, hq, n, hn, en, tn⟩
    exact ⟨n, hn, a, ha, q, hq, rfl, en, tn⟩

theorem intervalSequenceGraph_isFunc {A D rA rD e lo hi t : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e) :
    ZFSet.IsFunc A D (intervalSequenceGraph A D e t) := by
  refine ⟨intervalSequenceGraph_subset A D e t, ?_⟩
  intro a ha
  obtain ⟨n, hn, en⟩ := onto a ha
  obtain ⟨q, tn, _⟩ := code.function.2 n hn
  have hq := (ZFSet.pair_mem_prod.1 (code.function.1 tn)).2
  refine ⟨q, (pair_mem_intervalSequenceGraph A D e t a q).2 ⟨ha, hq, n, hn, en, tn⟩, ?_⟩
  intro z hz
  obtain ⟨_, _, m, _, em, tm⟩ := (pair_mem_intervalSequenceGraph A D e t a z).1 hz
  exact (code.agree m n a a z q em en tm tn).1 rfl

theorem intervalSequenceGraph_injection {A D rA rD e lo hi t : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e) :
    InjectionCode A D (intervalSequenceGraph A D e t) := by
  refine ⟨intervalSequenceGraph_isFunc code onto, ?_⟩
  intro a b q ha hb
  obtain ⟨_, _, n, _, en, tn⟩ := (pair_mem_intervalSequenceGraph A D e t a q).1 ha
  obtain ⟨_, _, m, _, em, tm⟩ := (pair_mem_intervalSequenceGraph A D e t b q).1 hb
  exact (code.agree n m a b q q en em tn tm).2 rfl

theorem intervalSequenceGraph_order_iff {A D rA rD e lo hi t a b q z : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (ha : ZFSet.pair a q ∈ intervalSequenceGraph A D e t)
    (hb : ZFSet.pair b z ∈ intervalSequenceGraph A D e t) :
    ZFSet.pair q z ∈ rD ↔ ZFSet.pair a b ∈ rA := by
  obtain ⟨_, _, n, _, en, tn⟩ := (pair_mem_intervalSequenceGraph A D e t a q).1 ha
  obtain ⟨_, _, m, _, em, tm⟩ := (pair_mem_intervalSequenceGraph A D e t b z).1 hb
  exact (code.order n m a b q z en em tn tm).symm

theorem intervalSequenceGraph_inside {A D rA rD e lo hi t a q : ZFSet.{u}}
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (entry : ZFSet.pair a q ∈ intervalSequenceGraph A D e t) :
    ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD := by
  obtain ⟨_, _, n, _, _, tn⟩ := (pair_mem_intervalSequenceGraph A D e t a q).1 entry
  exact code.inside n q tn






namespace BoundedFormula

open SetFormula

theorem truth_intervalSequenceEntryFormula {n} (z a d e t omega : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalSequenceEntryFormula z a d e t omega) env ↔
      ∃ i ∈ env omega, ∃ x ∈ env a, ∃ q ∈ env d,
        env z = ZFSet.pair x q ∧ ZFSet.pair i x ∈ env e ∧ ZFSet.pair i q ∈ env t := by
  simp only [intervalSequenceEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem intervalSequenceGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A D e t : ZFSet.{u}} (hA : A ∈ M.sets) (hD : D ∈ M.sets)
    (he : e ∈ M.sets) (ht : t ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets) :
    intervalSequenceGraph A D e t ∈ M.sets := by
  let params := extend A (extend D (extend e (extend t (extend ZFSet.omega Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.intervalSequenceEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hA (Fin.cases hD (Fin.cases he (Fin.cases ht
      (Fin.cases hOmega (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hA hD)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.intervalSequenceEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod A D) = intervalSequenceGraph A D e t := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, intervalSequenceGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_intervalSequenceEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

theorem intervalSequenceDescent_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A D rA rD e lo hi t : ZFSet.{u}} (hA : A ∈ M.sets) (hD : D ∈ M.sets)
    (he : e ∈ M.sets) (ht : t ∈ M.sets) (hOmega : ZFSet.omega ∈ M.sets)
    (code : IntervalSequenceCode ZFSet.omega A D rA rD e lo hi t)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e) :
    intervalSequenceGraph A D e t ∈ M.sets ∧
      InjectionCode A D (intervalSequenceGraph A D e t) ∧
      (∀ a q, ZFSet.pair a q ∈ intervalSequenceGraph A D e t →
        ZFSet.pair lo q ∈ rD ∧ ZFSet.pair q hi ∈ rD) ∧
      (∀ a b q z, ZFSet.pair a q ∈ intervalSequenceGraph A D e t →
        ZFSet.pair b z ∈ intervalSequenceGraph A D e t →
        (ZFSet.pair q z ∈ rD ↔ ZFSet.pair a b ∈ rA)) :=
  ⟨M.intervalSequenceGraph_mem pairing unions powers separation hA hD he ht hOmega,
    intervalSequenceGraph_injection code onto,
    fun _ _ entry => intervalSequenceGraph_inside code entry,
    fun _ _ _ _ left right => intervalSequenceGraph_order_iff code left right⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetFormula SetRealization Compression.RecursiveMaps.RationalHeights
universe u

theorem intervalEmbeddingCode_empty (D rA rD lo hi : ZFSet.{u}) :
    IntervalEmbeddingCode ∅ D rA rD lo hi ∅ := by
  refine ⟨⟨⟨ZFSet.empty_subset _, fun a ha => False.elim (ZFSet.notMem_empty a ha)⟩, ?_⟩, ?_, ?_⟩
  · intro a b q entry _
    exact False.elim (ZFSet.notMem_empty _ entry)
  · intro a b q z entry _
    exact False.elim (ZFSet.notMem_empty _ entry)
  · intro a q entry
    exact False.elim (ZFSet.notMem_empty _ entry)

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem exists_intervalEmbedding_of_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A D rA rD e lo hi c : ZFSet.{u}}
    (hA : A ∈ M.sets) (hD : D ∈ M.sets) (hrA : rA ∈ M.sets)
    (hrD : rD ∈ M.sets) (he : e ∈ M.sets) (hc : c ∈ M.sets)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (enumeration : ZFSet.IsFunc ZFSet.omega A e)
    (onto : ∀ a ∈ A, ∃ n ∈ ZFSet.omega, ZFSet.pair n a ∈ e)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ f ∈ M.sets, IntervalEmbeddingCode A D rA rD lo hi f := by
  obtain ⟨t, ht, sequence, _, _⟩ := M.exists_ground_intervalSequence
    pairing unions separation collection infinite hA hD hrA hrD he hc
    source target injection enumeration loD hiD gap
  obtain ⟨member, inj, inside, order⟩ := M.intervalSequenceDescent_spec
    pairing unions powers separation hA hD he ht (M.omega_mem separation infinite) sequence onto
  exact ⟨intervalSequenceGraph A D e t, member, inj,
    fun a b q z first second => (order a b q z first second).symm, inside⟩

theorem exists_intervalEmbedding
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A D rA rD lo hi c : ZFSet.{u}}
    (hA : A ∈ M.sets) (hD : D ∈ M.sets) (hrA : rA ∈ M.sets)
    (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (source : StrictLinearOrderCode A rA) (target : DenseOrderCode D rD)
    (injection : InjectionCode D ZFSet.omega c)
    (small : M.groundEmbeddable A ZFSet.omega)
    (loD : lo ∈ D) (hiD : hi ∈ D) (gap : ZFSet.pair lo hi ∈ rD) :
    ∃ f ∈ M.sets, IntervalEmbeddingCode A D rA rD lo hi f := by
  by_cases nonempty : A.Nonempty
  · obtain ⟨sourceCode, hSourceCode, sourceInjection⟩ := small
    have he := M.canonicalEnumeration_mem pairing unions powers separation
      hA hSourceCode (M.omega_mem separation infinite) sourceInjection nonempty
    have enumeration := canonicalEnumeration_isFunc sourceInjection nonempty
    have onto := canonicalEnumeration_onto sourceInjection
    exact M.exists_intervalEmbedding_of_enumeration pairing unions powers separation collection infinite
      hA hD hrA hrD he hc source target injection enumeration onto loD hiD gap
  · have empty : A = ∅ := by
      apply ZFSet.ext
      intro a
      exact ⟨fun ha => False.elim (nonempty ⟨a, ha⟩), fun ha => False.elim (ZFSet.notMem_empty a ha)⟩
    exact ⟨∅, M.empty_mem ⟨D, hD⟩, empty ▸ intervalEmbeddingCode_empty D rA rD lo hi⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

theorem pair_mem_intervalEmbeddingRelation (I W As rs los his D rD i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ intervalEmbeddingRelation I W As rs los his D rD ↔
      i ∈ I ∧ f ∈ W ∧ intervalEmbeddingCandidate As rs los his D rD i f := by
  rw [intervalEmbeddingRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hf⟩, j, _, g, _, equal, valid⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hf, valid⟩
  · rintro ⟨hi, hf, valid⟩
    exact ⟨⟨hi, hf⟩, i, hi, f, hf, rfl, valid⟩

namespace IntervalEmbeddingFamilyInputs

variable {I As rs los his D rD : ZFSet.{u}}
    (d : IntervalEmbeddingFamilyInputs I As rs los his D rD)

theorem candidate_iff (i : {i : ZFSet.{u} // i ∈ I}) (f : ZFSet.{u}) :
    intervalEmbeddingCandidate As rs los his D rD i.val f ↔
      IntervalEmbeddingCode (d.sources.value i) D (d.orders.value i) rD
        (d.lows.value i) (d.highs.value i) f := by
  constructor
  · rintro ⟨A, _, rA, _, lo, _, hi, _, entryA, entryR, entryLo, entryHi, code⟩
    have eA := d.sources.value_eq_of_entry i entryA
    have eR := d.orders.value_eq_of_entry i entryR
    have eLo := d.lows.value_eq_of_entry i entryLo
    have eHi := d.highs.value_eq_of_entry i entryHi
    rw [eA, eR, eLo, eHi]
    exact code
  · intro code
    exact ⟨d.sources.value i, d.sources.value_mem_doubleUnion i,
      d.orders.value i, d.orders.value_mem_doubleUnion i,
      d.lows.value i, d.lower_mem i, d.highs.value i, d.upper_mem i,
      d.sources.value_entry i, d.orders.value_entry i,
      d.lows.value_entry i, d.highs.value_entry i, code⟩

theorem embedding_subset_bound (i : {i : ZFSet.{u} // i ∈ I}) {f : ZFSet.{u}}
    (code : IntervalEmbeddingCode (d.sources.value i) D (d.orders.value i) rD
      (d.lows.value i) (d.highs.value i) f) :
    f ⊆ ZFSet.prod (familyPointBound As) D := by
  intro z hz
  obtain ⟨a, ha, q, hq, rfl⟩ := ZFSet.mem_prod.1 (code.injection.function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨mem_familyPointBound_of_entry (d.sources.value_entry i) ha, hq⟩

end IntervalEmbeddingFamilyInputs

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_IntervalEmbeddingFormulas
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

theorem truth_intervalEmbeddingFormula {n} (A D rA rD lo hi f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (intervalEmbeddingFormula A D rA rD lo hi f) env ↔
      IntervalEmbeddingCode (env A) (env D) (env rA) (env rD) (env lo) (env hi) (env f) := by
  simp only [intervalEmbeddingFormula, Truth, truth_injectionFormula,
    truth_imp, truth_pairMembershipFormula, truth_iffFormula]
  change (InjectionCode (env A) (env D) (env f) ∧
    (∀ a ∈ env A, ∀ b ∈ env A, ∀ q ∈ env D, ∀ z ∈ env D,
      ZFSet.pair a q ∈ env f → ZFSet.pair b z ∈ env f →
        (ZFSet.pair a b ∈ env rA ↔ ZFSet.pair q z ∈ env rD)) ∧
    (∀ a ∈ env A, ∀ q ∈ env D, ZFSet.pair a q ∈ env f →
      ZFSet.pair (env lo) q ∈ env rD ∧ ZFSet.pair q (env hi) ∈ env rD)) ↔ _
  constructor
  · rintro ⟨injection, order, inside⟩
    refine ⟨injection, ?_, ?_⟩
    · intro a b q z first second
      have aq := ZFSet.pair_mem_prod.1 (injection.function.1 first)
      have bz := ZFSet.pair_mem_prod.1 (injection.function.1 second)
      exact order a aq.1 b bz.1 q aq.2 z bz.2 first second
    · intro a q entry
      have aq := ZFSet.pair_mem_prod.1 (injection.function.1 entry)
      exact inside a aq.1 q aq.2 entry
  · intro code
    refine ⟨code.injection, ?_, ?_⟩
    · intro a _ b _ q _ z _ first second
      exact code.order a b q z first second
    · intro a _ q _ entry
      exact code.inside a q entry

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundIntervalEmbeddingRelation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_intervalEmbeddingCandidateFormula {n}
    (As rs los his D rD i f boundAs boundRs : Fin n) (env : Fin n → ZFSet.{u})
    (sourceBound : env boundAs = ⋃₀ ⋃₀ env As)
    (orderBound : env boundRs = ⋃₀ ⋃₀ env rs) :
    Truth (intervalEmbeddingCandidateFormula As rs los his D rD i f boundAs boundRs) env ↔
      intervalEmbeddingCandidate (env As) (env rs) (env los) (env his)
        (env D) (env rD) (env i) (env f) := by
  simp only [intervalEmbeddingCandidateFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_intervalEmbeddingFormula]
  change (∃ A ∈ env boundAs, ∃ rA ∈ env boundRs, ∃ lo ∈ env D, ∃ hi ∈ env D,
    ZFSet.pair (env i) A ∈ env As ∧ ZFSet.pair (env i) rA ∈ env rs ∧
    ZFSet.pair (env i) lo ∈ env los ∧ ZFSet.pair (env i) hi ∈ env his ∧
    IntervalEmbeddingCode A (env D) rA (env rD) lo hi (env f)) ↔ _
  rw [sourceBound, orderBound]
  rfl

theorem truth_intervalEmbeddingRelationEntryFormula {n}
    (z I W As rs los his D rD boundAs boundRs : Fin n) (env : Fin n → ZFSet.{u})
    (sourceBound : env boundAs = ⋃₀ ⋃₀ env As)
    (orderBound : env boundRs = ⋃₀ ⋃₀ env rs) :
    Truth (intervalEmbeddingRelationEntryFormula z I W As rs los his D rD boundAs boundRs) env ↔
      ∃ i ∈ env I, ∃ f ∈ env W, env z = ZFSet.pair i f ∧
        intervalEmbeddingCandidate (env As) (env rs) (env los) (env his)
          (env D) (env rD) i f := by
  simp only [intervalEmbeddingRelationEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro f
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_intervalEmbeddingCandidateFormula
    As.succ.succ rs.succ.succ los.succ.succ his.succ.succ D.succ.succ
    rD.succ.succ 1 0 boundAs.succ.succ boundRs.succ.succ
    (extend f (extend i env)) sourceBound orderBound)

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem intervalEmbeddingRelation_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W As rs los his D rD : ZFSet.{u}}
    (hI : I ∈ M.sets) (hW : W ∈ M.sets) (hAs : As ∈ M.sets) (hrs : rs ∈ M.sets)
    (hlos : los ∈ M.sets) (hhis : his ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    intervalEmbeddingRelation I W As rs los his D rD ∈ M.sets := by
  have sourceBound := M.union_mem unions (M.union_mem unions hAs)
  have orderBound := M.union_mem unions (M.union_mem unions hrs)
  let params := extend I (extend W (extend As (extend rs (extend los (extend his
    (extend D (extend rD (extend (⋃₀ ⋃₀ As) (extend (⋃₀ ⋃₀ rs) Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.intervalEmbeddingRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hAs (Fin.cases hrs (Fin.cases hlos
      (Fin.cases hhis (Fin.cases hD (Fin.cases hrD (Fin.cases sourceBound
        (Fin.cases orderBound (fun j => Fin.elim0 j)))))))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.intervalEmbeddingRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10)
      (extend z params)) (ZFSet.prod I W) =
      intervalEmbeddingRelation I W As rs los his D rD := by
    apply ZFSet.ext
    intro z
    rw [intervalEmbeddingRelation, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_intervalEmbeddingRelationEntryFormula 0 1 2 3 4 5 6 7 8 9 10
        (extend z params) rfl rfl)
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_TemplateHeightRangeCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

theorem taggedHeightGraph_old_entry {P N H old fresh x h : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair x h ∈ taggedHeightGraph P N H old fresh ↔ ZFSet.pair x h ∈ old := by
  constructor
  · intro member
    rcases ZFSet.mem_union.1 member with member | member
    · exact member
    · obtain ⟨q, _, v, _, equal, _⟩ := (ZFSet.mem_sep.1 member).2
      exact False.elim (pair_tag_not_mem P q ((ZFSet.pair_inj.1 equal).1 ▸ hx))
  · exact fun member => ZFSet.mem_union.2 (Or.inl member)

theorem taggedHeightGraph_fresh_entry {P N H old fresh x h : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P H old) (freshFunction : ZFSet.IsFunc N H fresh) :
    ZFSet.pair (ZFSet.pair P x) h ∈ taggedHeightGraph P N H old fresh ↔
      ZFSet.pair x h ∈ fresh := by
  constructor
  · intro member
    rcases ZFSet.mem_union.1 member with member | member
    · exact False.elim (pair_tag_not_mem P x (ZFSet.pair_mem_prod.1 (oldFunction.1 member)).1)
    · obtain ⟨q, _, v, _, equal, entry⟩ := (ZFSet.mem_sep.1 member).2
      obtain ⟨left, rfl⟩ := ZFSet.pair_inj.1 equal
      exact (ZFSet.pair_inj.1 left).2.symm ▸ entry
  · intro entry
    have shape := ZFSet.pair_mem_prod.1 (freshFunction.1 entry)
    exact ZFSet.mem_union.2 (Or.inr (ZFSet.mem_sep.2
      ⟨ZFSet.pair_mem_prod.2 ⟨pair_mem_taggedExtension.2 shape.1, shape.2⟩,
        x, shape.1, h, shape.2, rfl, entry⟩))

theorem taggedHeightGraph_function {P N H old fresh : ZFSet.{u}}
    (oldFunction : ZFSet.IsFunc P H old) (freshFunction : ZFSet.IsFunc N H fresh) :
    ZFSet.IsFunc (taggedExtension P N) H (taggedHeightGraph P N H old fresh) := by
  refine ⟨?_, ?_⟩
  · intro w member
    rcases ZFSet.mem_union.1 member with member | member
    · obtain ⟨x, hx, h, hh, rfl⟩ := ZFSet.mem_prod.1 (oldFunction.1 member)
      exact ZFSet.pair_mem_prod.2 ⟨old_mem_taggedExtension hx, hh⟩
    · exact (ZFSet.mem_sep.1 member).1
  · intro x hx
    rcases mem_taggedExtension.1 hx with old | ⟨q, hq, rfl⟩
    · obtain ⟨h, entry, unique⟩ := oldFunction.2 x old
      exact ⟨h, (taggedHeightGraph_old_entry old).2 entry,
        fun y hy => unique y ((taggedHeightGraph_old_entry old).1 hy)⟩
    · obtain ⟨h, entry, unique⟩ := freshFunction.2 q hq
      exact ⟨h, (taggedHeightGraph_fresh_entry oldFunction freshFunction).2 entry,
        fun y hy => unique y ((taggedHeightGraph_fresh_entry oldFunction freshFunction).1 hy)⟩

theorem heightOrderRestriction_linear {B R r : ZFSet.{u}}
    (linear : StrictLinearOrderCode B r) (subset : R ⊆ B) :
    StrictLinearOrderCode R (heightOrderRestriction R r) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).2, ?_, ?_, ?_⟩
  · intro a ha entry
    exact linear.irrefl a (subset ha) (ZFSet.mem_sep.1 entry).1
  · intro a b c first second
    obtain ⟨ab, ha, _⟩ := (pair_mem_heightOrderRestriction R r a b).1 first
    obtain ⟨bc, _, hc⟩ := (pair_mem_heightOrderRestriction R r b c).1 second
    exact (pair_mem_heightOrderRestriction R r a c).2 ⟨linear.trans a b c ab bc, ha, hc⟩
  · intro a ha b hb
    rcases linear.compare a (subset ha) b (subset hb) with ab | equal | ba
    · exact Or.inl ((pair_mem_heightOrderRestriction R r a b).2 ⟨ab, ha, hb⟩)
    · exact Or.inr (Or.inl equal)
    · exact Or.inr (Or.inr ((pair_mem_heightOrderRestriction R r b a).2 ⟨ba, hb, ha⟩))

theorem function_on_relationImage {A B h : ZFSet.{u}} (function : ZFSet.IsFunc A B h) :
    ZFSet.IsFunc A (relationImage A B h) h := by
  refine ⟨?_, function.2⟩
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨ha, (mem_relationImage A B h b).2 ⟨hb, a, ha, hz⟩⟩

theorem pair_mem_heightImageFamily (I W Qs Bs Hs i R : ZFSet.{u}) :
    ZFSet.pair i R ∈ heightImageFamily I W Qs Bs Hs ↔
      i ∈ I ∧ R ∈ W ∧ heightImageCandidate Qs Bs Hs i R := by
  rw [heightImageFamily, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hR⟩, j, _, S, _, equal, candidate⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hR, candidate⟩
  · rintro ⟨hi, hR, candidate⟩
    exact ⟨⟨hi, hR⟩, i, hi, R, hR, rfl, candidate⟩

theorem pair_mem_heightOrderFamily (I W Rs brs i r : ZFSet.{u}) :
    ZFSet.pair i r ∈ heightOrderFamily I W Rs brs ↔
      i ∈ I ∧ r ∈ W ∧ heightOrderCandidate Rs brs i r := by
  rw [heightOrderFamily, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hi, hr⟩, j, _, s, _, equal, candidate⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hi, hr, candidate⟩
  · rintro ⟨hi, hr, candidate⟩
    exact ⟨⟨hi, hr⟩, i, hi, r, hr, rfl, candidate⟩

namespace BoundedFormula

open SetFormula

theorem truth_heightImageEquationFormula {n} (R Q B h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (heightImageEquationFormula R Q B h) env ↔
      env R = relationImage (env Q) (env B) (env h) := by
  simp only [heightImageEquationFormula, Truth, truth_imp, truth_imageMemberFormula]
  change ((∀ x ∈ env R, x ∈ env B ∧ ∃ q ∈ env Q, ZFSet.pair q x ∈ env h) ∧
    (∀ x ∈ env B, (∃ q ∈ env Q, ZFSet.pair q x ∈ env h) → x ∈ env R)) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro x
    rw [mem_relationImage]
    exact ⟨subset x, fun hx => covers x hx.1 hx.2⟩
  · intro equal
    constructor
    · intro x hx
      exact (mem_relationImage _ _ _ x).1 (equal ▸ hx)
    · intro x hx image
      exact equal.symm ▸ (mem_relationImage _ _ _ x).2 ⟨hx, image⟩

theorem truth_heightOrderEquationFormula {n} (r R s : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (heightOrderEquationFormula r R s) env ↔
      env r = heightOrderRestriction (env R) (env s) := by
  simp only [heightOrderEquationFormula, Truth, truth_imp, truth_productElementFormula]
  change ((∀ x ∈ env r, x ∈ env s ∧ x ∈ ZFSet.prod (env R) (env R)) ∧
    (∀ x ∈ env s, x ∈ ZFSet.prod (env R) (env R) → x ∈ env r)) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro x
    rw [heightOrderRestriction, ZFSet.mem_sep]
    exact ⟨subset x, fun hx => covers x hx.1 hx.2⟩
  · intro equal
    constructor
    · intro x hx
      have member : x ∈ heightOrderRestriction (env R) (env s) := equal ▸ hx
      exact ZFSet.mem_sep.1 member
    · intro x hx bound
      exact equal.symm ▸ ZFSet.mem_sep.2 ⟨hx, bound⟩

theorem truth_heightImageCandidateFormula {n} (Qs Bs Hs i R qb bb hb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqQ : env qb = ⋃₀ ⋃₀ env Qs)
    (eqB : env bb = ⋃₀ ⋃₀ env Bs) (eqH : env hb = ⋃₀ ⋃₀ env Hs) :
    Truth (heightImageCandidateFormula Qs Bs Hs i R qb bb hb) env ↔
      heightImageCandidate (env Qs) (env Bs) (env Hs) (env i) (env R) := by
  simp only [heightImageCandidateFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_heightImageEquationFormula]
  change (∃ Q ∈ env qb, ∃ B ∈ env bb, ∃ h ∈ env hb,
    ZFSet.pair (env i) Q ∈ env Qs ∧ ZFSet.pair (env i) B ∈ env Bs ∧
    ZFSet.pair (env i) h ∈ env Hs ∧ env R = relationImage Q B h) ↔ _
  rw [eqQ, eqB, eqH]
  rfl

theorem truth_heightOrderCandidateFormula {n} (Rs brs i r rb sb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqR : env rb = ⋃₀ ⋃₀ env Rs)
    (eqS : env sb = ⋃₀ ⋃₀ env brs) :
    Truth (heightOrderCandidateFormula Rs brs i r rb sb) env ↔
      heightOrderCandidate (env Rs) (env brs) (env i) (env r) := by
  simp only [heightOrderCandidateFormula, truth_exMem, Truth,
    truth_pairMembershipFormula, truth_heightOrderEquationFormula]
  change (∃ R ∈ env rb, ∃ s ∈ env sb,
    ZFSet.pair (env i) R ∈ env Rs ∧ ZFSet.pair (env i) s ∈ env brs ∧
    env r = heightOrderRestriction R s) ↔ _
  rw [eqR, eqS]
  rfl

theorem truth_heightImageFamilyEntryFormula {n} (z I W Qs Bs Hs qb bb hb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqQ : env qb = ⋃₀ ⋃₀ env Qs)
    (eqB : env bb = ⋃₀ ⋃₀ env Bs) (eqH : env hb = ⋃₀ ⋃₀ env Hs) :
    Truth (heightImageFamilyEntryFormula z I W Qs Bs Hs qb bb hb) env ↔
      ∃ i ∈ env I, ∃ R ∈ env W, env z = ZFSet.pair i R ∧
        heightImageCandidate (env Qs) (env Bs) (env Hs) i R := by
  simp only [heightImageFamilyEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro R
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_heightImageCandidateFormula Qs.succ.succ Bs.succ.succ
    Hs.succ.succ 1 0 qb.succ.succ bb.succ.succ hb.succ.succ
    (extend R (extend i env)) eqQ eqB eqH)

theorem truth_heightOrderFamilyEntryFormula {n} (z I W Rs brs rb sb : Fin n)
    (env : Fin n → ZFSet.{u}) (eqR : env rb = ⋃₀ ⋃₀ env Rs)
    (eqS : env sb = ⋃₀ ⋃₀ env brs) :
    Truth (heightOrderFamilyEntryFormula z I W Rs brs rb sb) env ↔
      ∃ i ∈ env I, ∃ r ∈ env W, env z = ZFSet.pair i r ∧
        heightOrderCandidate (env Rs) (env brs) i r := by
  simp only [heightOrderFamilyEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro i
  apply and_congr_right
  intro _
  apply exists_congr
  intro r
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (truth_heightOrderCandidateFormula Rs.succ.succ brs.succ.succ
    1 0 rb.succ.succ sb.succ.succ (extend r (extend i env)) eqR eqS)

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTemplateIntervalFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

section

universe u

theorem pair_mem_batchHeightEndpointRelation
    (I P C D As Es Ss oldH rD i c lo hi : ZFSet.{u}) :
    ZFSet.pair i (ZFSet.pair c (ZFSet.pair lo hi)) ∈
      batchHeightEndpointRelation I P C D As Es Ss oldH rD ↔
    i ∈ I ∧ c ∈ C ∧ lo ∈ D ∧ hi ∈ D ∧
      ∃ a ∈ ZFSet.sUnion (ZFSet.sUnion As), ∃ ell ∈ ZFSet.sUnion (ZFSet.sUnion Es),
      ∃ b ∈ P, ∃ e ∈ P, ∃ d ∈ C, ∃ v ∈ D,
      ZFSet.pair i a ∈ As ∧ ZFSet.pair i ell ∈ Es ∧ ZFSet.pair a b ∈ ell ∧
      ZFSet.pair i e ∈ Ss ∧ ZFSet.pair b (ZFSet.pair c lo) ∈ oldH ∧
      ZFSet.pair e (ZFSet.pair d v) ∈ oldH ∧ ZFSet.pair lo hi ∈ rD ∧
      ((c = d ∧ hi = v) ∨ c ∈ d) := by
  rw [batchHeightEndpointRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, j, hj, a, ha, ell, hell, b, hb, e, he,
      c', hc, lo', hlo, hi', hhi, d, hd, v, hv, equal, rest⟩
    obtain ⟨ij, restEq⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨cc, restEq'⟩ := ZFSet.pair_inj.1 restEq
    obtain ⟨ll, hh⟩ := ZFSet.pair_inj.1 restEq'
    subst j
    subst c'
    subst lo'
    subst hi'
    exact ⟨hj, hc, hlo, hhi, a, ha, ell, hell, b, hb, e, he, d, hd, v, hv, rest⟩
  · rintro ⟨hiI, hc, hlo, hhi, a, ha, ell, hell, b, hb, e, he, d, hd, v, hv, rest⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hiI, ZFSet.pair_mem_prod.2
      ⟨hc, ZFSet.pair_mem_prod.2 ⟨hlo, hhi⟩⟩⟩,
      i, hiI, a, ha, ell, hell, b, hb, e, he, c, hc, lo, hlo, hi, hhi, d, hd, v, hv, rfl, rest⟩

namespace AttachmentBatchInputs

variable {P rP μP I Qs rs μs As Es Fs Ss C D oldH rD : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

theorem endpoint_base_entry (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.pair (d.anchor i) (d.templates.base i).val ∈ d.embed i :=
  (d.fiber i).baseMap_entry _

include d in
theorem batchHeightEndpointRelation_total
    (old : StrictLexHeightCode P C D rP oldH rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD) :
    ∀ i ∈ I, ∃ t ∈ ZFSet.prod C (ZFSet.prod D D),
      ZFSet.pair i t ∈ batchHeightEndpointRelation I P C D As Es Ss oldH rD := by
  intro i hi
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  obtain ⟨baseHeight, baseEntry, _⟩ := old.function.2 (d.templates.base j).val (d.templates.base j).property
  obtain ⟨c, hc, lo, hlo, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (old.function.1 baseEntry)).2
  obtain ⟨sepHeight, sepEntry, _⟩ := old.function.2 (d.separator j) (d.fiber j).separator_mem
  obtain ⟨c', hc', v, hv, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (old.function.1 sepEntry)).2
  have different : (d.templates.base j).val ≠ d.separator j := by
    intro equal
    have bad := (d.fiber j).separator_not_le_base _ (d.endpoint_base_entry j)
    rw [equal] at bad
    exact bad (d.oldOrder.order.refl _ (d.fiber j).separator_mem)
  have strict := old.strict _ (d.templates.base j).property _ (d.fiber j).separator_mem
    c lo c' v ((d.fiber j).base_le_separator _ (d.endpoint_base_entry j)) different baseEntry sepEntry
  have construct (upper : ZFSet.{u}) (hupper : upper ∈ D) (gap : ZFSet.pair lo upper ∈ rD)
      (rule : (c = c' ∧ upper = v) ∨ c ∈ c') :
      ∃ t ∈ ZFSet.prod C (ZFSet.prod D D),
        ZFSet.pair i t ∈ batchHeightEndpointRelation I P C D As Es Ss oldH rD := by
    refine ⟨ZFSet.pair c (ZFSet.pair lo upper),
      ZFSet.pair_mem_prod.2 ⟨hc, ZFSet.pair_mem_prod.2 ⟨hlo, hupper⟩⟩,
      (pair_mem_batchHeightEndpointRelation _ _ _ _ _ _ _ _ _ _ _ _ _).2 ?_⟩
    exact ⟨hi, hc, hlo, hupper, d.anchor j, d.anchors.value_mem_doubleUnion j,
      d.embed j, d.embeddings.value_mem_doubleUnion j, (d.templates.base j).val,
      (d.templates.base j).property, d.separator j, (d.fiber j).separator_mem, c', hc', v, hv,
      d.anchor_entry j, d.embed_entry j, d.endpoint_base_entry j, d.separator_entry j,
      baseEntry, sepEntry, gap, rule⟩
  rcases strict with smaller | ⟨same, gap⟩
  · obtain ⟨upper, hupper, gap⟩ := above lo hlo
    exact construct upper hupper gap (Or.inr smaller)
  · exact construct v hv gap (Or.inl ⟨same, rfl⟩)

theorem batchHeightEndpointRelation_laws
    (old : StrictLexHeightCode P C D rP oldH rD)
    (i : {i : ZFSet.{u} // i ∈ I}) {c lo hi : ZFSet.{u}}
    (entry : ZFSet.pair i.val (ZFSet.pair c (ZFSet.pair lo hi)) ∈
      batchHeightEndpointRelation I P C D As Es Ss oldH rD) :
    ZFSet.pair (d.templates.base i).val (ZFSet.pair c lo) ∈ oldH ∧
      ZFSet.pair lo hi ∈ rD ∧ ∀ c' v,
      ZFSet.pair (d.separator i) (ZFSet.pair c' v) ∈ oldH →
        (c = c' ∧ hi = v) ∨ c ∈ c' := by
  obtain ⟨_, _, _, _, a, _, ell, _, b, _, e, _, c', _, v, _,
    ia, iell, ab, ie, bH, eH, gap, rule⟩ :=
      (pair_mem_batchHeightEndpointRelation _ _ _ _ _ _ _ _ _ _ _ _ _).1 entry
  have aeq := d.anchors.value_eq_of_entry i ia
  have elleq := d.embeddings.value_eq_of_entry i iell
  have eeq := d.separators.value_eq_of_entry i ie
  change d.anchor i = a at aeq
  change d.embed i = ell at elleq
  change d.separator i = e at eeq
  subst a
  subst ell
  subst e
  have beq := (functionCode_partial (d.fiber i).base_function).unique _ _ _ ab (d.endpoint_base_entry i)
  subst b
  refine ⟨bH, gap, ?_⟩
  intro c'' v' entry'
  have equal := (functionCode_partial old.function).unique _ _ _ eH entry'
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  exact rule

end AttachmentBatchInputs

end



namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_intervalEmbedding_family
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I As rs los his D rD c : ZFSet.{u}}
    (d : IntervalEmbeddingFamilyInputs I As rs los his D rD)
    (hI : I ∈ M.sets) (hAs : As ∈ M.sets) (hrs : rs ∈ M.sets)
    (hlos : los ∈ M.sets) (hhis : his ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
    (small : ∀ i, M.groundEmbeddable (d.sources.value i) ZFSet.omega) :
    ∃ family ∈ M.sets,
      ZFSet.IsFunc I (M.groundRelations (familyPointBound As) D) family ∧
      ∀ (i : {i : ZFSet.{u} // i ∈ I}) f, ZFSet.pair i.val f ∈ family →
        IntervalEmbeddingCode (d.sources.value i) D (d.orders.value i) rD
          (d.lows.value i) (d.highs.value i) f := by
  let W := M.groundRelations (familyPointBound As) D
  have hW : W ∈ M.sets := M.groundRelations_mem pairing unions powers separation
    (M.familyPointBound_mem unions hAs) hD
  have hR := M.intervalEmbeddingRelation_mem pairing unions powers separation
    hI hW hAs hrs hlos hhis hD hrD
  have total : ∀ i ∈ I, ∃ f ∈ W,
      ZFSet.pair i f ∈ intervalEmbeddingRelation I W As rs los his D rD := by
    intro i hi
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    obtain ⟨f, hf, code⟩ := M.exists_intervalEmbedding
      pairing unions powers separation collection infinite
      (d.sources.value_mem M hAs j) hD (d.orders.value_mem M hrs j) hrD hc
      (d.source_order j) target injection (small j) (d.lower_mem j) (d.upper_mem j) (d.gap j)
    have bound : f ∈ W := (M.mem_groundRelations (familyPointBound As) D f).2
      ⟨hf, d.embedding_subset_bound j code⟩
    exact ⟨f, bound, (pair_mem_intervalEmbeddingRelation I W As rs los his D rD i f).2
      ⟨hi, bound, (d.candidate_iff j f).2 code⟩⟩
  obtain ⟨family, member, function, subset⟩ := M.uniformize_relation
    pairing unions powers separation choice hI hW hR total
  refine ⟨family, member, function, ?_⟩
  intro i f entry
  exact (d.candidate_iff i f).1
    ((pair_mem_intervalEmbeddingRelation I W As rs los his D rD i.val f).1 (subset entry)).2.2

end TransitiveGround




universe u

namespace BoundedFormula

open SetFormula

theorem truth_endpointRightTripleFormula {n} (z x y w : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (endpointRightTripleFormula z x y w) env ↔
      env z = ZFSet.pair (env x) (ZFSet.pair (env y) (env w)) := by
  simp only [endpointRightTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ a ∈ env z, ∃ b ∈ a, b = ZFSet.pair (env y) (env w) ∧ env z = ZFSet.pair (env x) b) ↔ _
  constructor
  · rintro ⟨a, _, b, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env x, ZFSet.pair (env y) (env w)}, ?_, ZFSet.pair (env y) (env w),
      ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

theorem truth_endpointRightMembershipFormula {n} (x y w f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (endpointRightMembershipFormula x y w f) env ↔
      ZFSet.pair (env x) (ZFSet.pair (env y) (env w)) ∈ env f := by
  simp only [endpointRightMembershipFormula, truth_exMem, truth_endpointRightTripleFormula]
  change (∃ a ∈ env f, a = ZFSet.pair (env x) (ZFSet.pair (env y) (env w))) ↔ _
  constructor
  · rintro ⟨a, ha, equal⟩
    exact equal ▸ ha
  · intro ha
    exact ⟨_, ha, rfl⟩

theorem truth_endpointTupleFormula {n} (z i c lo hi : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (endpointTupleFormula z i c lo hi) env ↔
      env z = ZFSet.pair (env i) (ZFSet.pair (env c) (ZFSet.pair (env lo) (env hi))) := by
  simp only [endpointTupleFormula, truth_exMem, Truth, truth_endpointRightTripleFormula,
    truth_orderedPairFormula]
  change (∃ a ∈ env z, ∃ b ∈ a, b = ZFSet.pair (env c) (ZFSet.pair (env lo) (env hi)) ∧
    env z = ZFSet.pair (env i) b) ↔ _
  constructor
  · rintro ⟨a, _, b, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env i, ZFSet.pair (env c) (ZFSet.pair (env lo) (env hi))}, ?_,
      ZFSet.pair (env c) (ZFSet.pair (env lo) (env hi)), ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

theorem truth_batchHeightEndpointFormula (env : Fin 12 → ZFSet.{u}) :
    Truth batchHeightEndpointFormula env ↔
    ∃ i ∈ env 1, ∃ a ∈ env 10, ∃ ell ∈ env 11, ∃ b ∈ env 2, ∃ e ∈ env 2,
    ∃ c ∈ env 3, ∃ lo ∈ env 4, ∃ hi ∈ env 4, ∃ d ∈ env 3, ∃ v ∈ env 4,
      env 0 = ZFSet.pair i (ZFSet.pair c (ZFSet.pair lo hi)) ∧
      ZFSet.pair i a ∈ env 5 ∧ ZFSet.pair i ell ∈ env 6 ∧ ZFSet.pair a b ∈ ell ∧
      ZFSet.pair i e ∈ env 7 ∧ ZFSet.pair b (ZFSet.pair c lo) ∈ env 8 ∧
      ZFSet.pair e (ZFSet.pair d v) ∈ env 8 ∧ ZFSet.pair lo hi ∈ env 9 ∧
      ((c = d ∧ hi = v) ∨ c ∈ d) := by
  simp only [batchHeightEndpointFormula, truth_exMem, Truth, truth_disj,
    truth_endpointTupleFormula, truth_endpointRightMembershipFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

theorem endpointProjection_functions {I C D f : ZFSet.{u}}
    (func : ZFSet.IsFunc I (ZFSet.prod C (ZFSet.prod D D)) f) :
    ZFSet.IsFunc I C (endpointColumns I C D f) ∧
      ZFSet.IsFunc I D (endpointLows I C D f) ∧ ZFSet.IsFunc I D (endpointHighs I C D f) := by
  have pairs : ZFSet.IsFunc I (ZFSet.prod D D) (endpointPairs I C D f) :=
    relationCompose_function_of_subset func (productSecond_function C (ZFSet.prod D D)) (fun _ h => h)
  exact ⟨relationCompose_function_of_subset func (productFirst_function C (ZFSet.prod D D)) (fun _ h => h),
    relationCompose_function_of_subset pairs (productFirst_function D D) (fun _ h => h),
    relationCompose_function_of_subset pairs (productSecond_function D D) (fun _ h => h)⟩

theorem endpointProjection_entries {I C D f i c lo hi : ZFSet.{u}}
    (hiI : i ∈ I) (hc : c ∈ C) (hlo : lo ∈ D) (hhi : hi ∈ D)
    (entry : ZFSet.pair i (ZFSet.pair c (ZFSet.pair lo hi)) ∈ f) :
    ZFSet.pair i c ∈ endpointColumns I C D f ∧
      ZFSet.pair i lo ∈ endpointLows I C D f ∧ ZFSet.pair i hi ∈ endpointHighs I C D f := by
  have hpair := ZFSet.pair_mem_prod.2 ⟨hlo, hhi⟩
  have htriple := ZFSet.pair_mem_prod.2 ⟨hc, hpair⟩
  have pairs : ZFSet.pair i (ZFSet.pair lo hi) ∈ endpointPairs I C D f :=
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hiI, hpair, _, htriple, entry,
      (mem_productSecond C (ZFSet.prod D D) _).2 ⟨c, hc, _, hpair, rfl⟩⟩
  exact ⟨(pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hiI, hc, _, htriple, entry,
      (mem_productFirst C (ZFSet.prod D D) _).2 ⟨c, hc, _, hpair, rfl⟩⟩,
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hiI, hlo, _, hpair, pairs,
      (mem_productFirst D D _).2 ⟨lo, hlo, hi, hhi, rfl⟩⟩,
    (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨hiI, hhi, _, hpair, pairs,
      (mem_productSecond D D _).2 ⟨lo, hlo, hi, hhi, rfl⟩⟩⟩

theorem batchHeightEndpointCode_of_selection
    {P rP μP I Qs rs μs As Es Fs Ss C D oldH rD f : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (old : StrictLexHeightCode P C D rP oldH rD)
    (func : ZFSet.IsFunc I (ZFSet.prod C (ZFSet.prod D D)) f)
    (selected : f ⊆ batchHeightEndpointRelation I P C D As Es Ss oldH rD) :
    BatchHeightEndpointCode d C D oldH rD
      (endpointColumns I C D f) (endpointLows I C D f) (endpointHighs I C D f) := by
  obtain ⟨columns, lows, highs⟩ := endpointProjection_functions func
  have atIndex (i : {i : ZFSet.{u} // i ∈ I}) :
      ∃ c lo hi, ZFSet.pair i.val c ∈ endpointColumns I C D f ∧
        ZFSet.pair i.val lo ∈ endpointLows I C D f ∧ ZFSet.pair i.val hi ∈ endpointHighs I C D f ∧
        ZFSet.pair (d.templates.base i).val (ZFSet.pair c lo) ∈ oldH ∧ ZFSet.pair lo hi ∈ rD ∧
        ∀ c' v, ZFSet.pair (d.separator i) (ZFSet.pair c' v) ∈ oldH →
          (c = c' ∧ hi = v) ∨ c ∈ c' := by
    obtain ⟨t, entry, _⟩ := func.2 i.val i.property
    obtain ⟨c, hc, pair, hpair, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (func.1 entry)).2
    obtain ⟨lo, hlo, hi, hhi, rfl⟩ := ZFSet.mem_prod.1 hpair
    obtain ⟨ce, le, he⟩ := endpointProjection_entries i.property hc hlo hhi entry
    exact ⟨c, lo, hi, ce, le, he, d.batchHeightEndpointRelation_laws old i (selected entry)⟩
  refine ⟨columns, lows, highs, ?_, ?_, ?_⟩
  · intro i c lo ce le
    obtain ⟨c', lo', hi, ce', le', _, base, _⟩ := atIndex i
    have ec := (functionCode_partial columns).unique _ _ _ ce' ce
    have el := (functionCode_partial lows).unique _ _ _ le' le
    exact ec ▸ el ▸ base
  · intro i lo hi le he
    obtain ⟨c, lo', hi', _, le', he', _, gap, _⟩ := atIndex i
    have el := (functionCode_partial lows).unique _ _ _ le' le
    have eh := (functionCode_partial highs).unique _ _ _ he' he
    exact el ▸ eh ▸ gap
  · intro i c hi c' v ce he sep
    obtain ⟨c'', lo, hi', ce', _, he', _, _, upper⟩ := atIndex i
    have ec := (functionCode_partial columns).unique _ _ _ ce' ce
    have eh := (functionCode_partial highs).unique _ _ _ he' he
    exact ec ▸ eh ▸ upper c' v sep

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem batchHeightEndpointRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P C D As Es Ss oldH rD : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hOld : oldH ∈ M.sets) (hrD : rD ∈ M.sets) :
    batchHeightEndpointRelation I P C D As Es Ss oldH rD ∈ M.sets := by
  have ha := M.union_mem unions (M.union_mem unions hAs)
  have he := M.union_mem unions (M.union_mem unions hEs)
  let params := extend I (extend P (extend C (extend D (extend As (extend Es (extend Ss
    (extend oldH (extend rD (extend (ZFSet.sUnion (ZFSet.sUnion As))
      (extend (ZFSet.sUnion (ZFSet.sUnion Es)) Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.batchHeightEndpointFormula params
    (Fin.cases hI (Fin.cases hP (Fin.cases hC (Fin.cases hD (Fin.cases hAs (Fin.cases hEs
      (Fin.cases hSs (Fin.cases hOld (Fin.cases hrD (Fin.cases ha (Fin.cases he (fun j => Fin.elim0 j))))))))))))
    (M.prod_mem pairing unions powers separation hI
      (M.prod_mem pairing unions powers separation hC (M.prod_mem pairing unions powers separation hD hD)))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.batchHeightEndpointFormula
      (extend z params)) (ZFSet.prod I (ZFSet.prod C (ZFSet.prod D D))) =
      batchHeightEndpointRelation I P C D As Es Ss oldH rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, batchHeightEndpointRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchHeightEndpointFormula _)
  exact equal ▸ selected

theorem endpointProjections_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C D f : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hf : f ∈ M.sets) :
    endpointColumns I C D f ∈ M.sets ∧ endpointLows I C D f ∈ M.sets ∧
      endpointHighs I C D f ∈ M.sets := by
  have hDD := M.prod_mem pairing unions powers separation hD hD
  have hT := M.prod_mem pairing unions powers separation hC hDD
  have hPairs : endpointPairs I C D f ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hI hT hDD hf (M.productSecond_mem pairing unions powers separation hC hDD)
  exact ⟨M.relationCompose_mem pairing unions powers separation hI hT hC hf
      (M.productFirst_mem pairing unions powers separation hC hDD),
    M.relationCompose_mem pairing unions powers separation hI hDD hD hPairs
      (M.productFirst_mem pairing unions powers separation hD hD),
    M.relationCompose_mem pairing unions powers separation hI hDD hD hPairs
      (M.productSecond_mem pairing unions powers separation hD hD)⟩

theorem exists_batchHeightEndpoints
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P rP μP I Qs rs μs As Es Fs Ss C D oldH rD : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (old : StrictLexHeightCode P C D rP oldH rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hOld : oldH ∈ M.sets) (hrD : rD ∈ M.sets) :
    ∃ Cs ∈ M.sets, ∃ los ∈ M.sets, ∃ his ∈ M.sets,
      BatchHeightEndpointCode d C D oldH rD Cs los his := by
  have hT := M.prod_mem pairing unions powers separation hC (M.prod_mem pairing unions powers separation hD hD)
  have hRelation := M.batchHeightEndpointRelation_mem pairing unions powers separation
    hI hP hC hD hAs hEs hSs hOld hrD
  obtain ⟨f, hf, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice
    hI hT hRelation (d.batchHeightEndpointRelation_total old above)
  obtain ⟨hc, hl, hh⟩ := M.endpointProjections_mem pairing unions powers separation hI hC hD hf
  exact ⟨endpointColumns I C D f, hc, endpointLows I C D f, hl, endpointHighs I C D f, hh,
    batchHeightEndpointCode_of_selection d old func selected⟩

end TransitiveGround






namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D old rD Cs los his : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)

include t in
theorem intervalInputs (e : BatchHeightEndpointCode d C D old rD Cs los his) :
    IntervalEmbeddingFamilyInputs I Vs vrs los his D rD where
  sources := t.ranges
  orders := t.orders
  lows := ⟨D, e.lows⟩
  highs := ⟨D, e.highs⟩
  source_order := t.linear
  lower_mem i := (ZFSet.pair_mem_prod.1 (e.lows.1
    ((show FunctionGraphOn I los from ⟨D, e.lows⟩).value_entry i))).2
  upper_mem i := (ZFSet.pair_mem_prod.1 (e.highs.1
    ((show FunctionGraphOn I his from ⟨D, e.highs⟩).value_entry i))).2
  gap i := e.gap i _ _
    ((show FunctionGraphOn I los from ⟨D, e.lows⟩).value_entry i)
    ((show FunctionGraphOn I his from ⟨D, e.highs⟩).value_entry i)

end TemplateHeightFamilyInputs

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_templateIntervalFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D old rD Cs los his c : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)
    (e : BatchHeightEndpointCode d C D old rD Cs los his)
    (hI : I ∈ M.sets) (hVs : Vs ∈ M.sets) (hvrs : vrs ∈ M.sets)
    (hlos : los ∈ M.sets) (hhis : his ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (target : DenseOrderCode D rD) (injection : InjectionCode D ZFSet.omega c)
    (small : ∀ i, M.groundEmbeddable (t.ranges.value i) ZFSet.omega) :
    ∃ family ∈ M.sets,
      ZFSet.IsFunc I (M.groundRelations (familyPointBound Vs) D) family ∧
      ∀ (i : {i : ZFSet.{u} // i ∈ I}) lo hi f,
        ZFSet.pair i.val lo ∈ los → ZFSet.pair i.val hi ∈ his →
        ZFSet.pair i.val f ∈ family →
        IntervalEmbeddingCode (t.ranges.value i) D (t.orders.value i) rD lo hi f := by
  obtain ⟨family, member, function, valid⟩ := M.exists_intervalEmbedding_family
    pairing unions powers separation collection infinite choice (t.intervalInputs e)
    hI hVs hvrs hlos hhis hD hrD hc target injection small
  refine ⟨family, member, function, ?_⟩
  intro i lo hi f lower upper entry
  have code := valid i f entry
  have sameLo := (t.intervalInputs e).lows.value_eq_of_entry i lower
  have sameHi := (t.intervalInputs e).highs.value_eq_of_entry i upper
  rw [sameLo, sameHi] at code
  exact code

end TransitiveGround


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedTemplateShadowLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.CodedTemplateAttachment
universe u v w
variable {J : Type v} {P r μ N inside shadow upper : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

theorem encoded_shadow_meet (q : b.Fresh) (p : {p : ZFSet.{u} // p ∈ P})
    (notAbove : ZFSet.pair (d.encode (.inr q)) p.val ∉ d.order) :
    ZFSet.pair (ZFSet.pair (d.encode (.inr q)) p.val)
      (old.toMeetOrder.meet (b.shadow q) p).val ∈ d.meetGraph := by
  have eq := b.shadow_meet_eq q p (fun lower => notAbove ((d.le_encode _ _).2 lower))
  have result := d.encoded_meet_entry (.inr q) (.inl p)
  rw [eq] at result
  exact result

end PartitionPilot.Forcing.CodedTemplateAttachment

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalWordRewriteFormulas
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

theorem truth_actorSingletonWordFormula {n} (w zero g : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actorSingletonWordFormula w zero g) env ↔
      env w = {ZFSet.pair (env zero) (ZFSet.pair (env zero) (env g))} := by
  simp only [actorSingletonWordFormula, truth_exMem, Truth,
    truth_nonemptyTupleFormula, truth_singletonFormula]
  change (∃ z ∈ env w, z = ZFSet.pair (env zero) (ZFSet.pair (env zero) (env g)) ∧
    env w = {z}) ↔ _
  constructor
  · rintro ⟨z, _, rfl, eq⟩
    exact eq
  · intro eq
    exact ⟨_, eq.symm ▸ ZFSet.mem_singleton.2 rfl, rfl, eq⟩

theorem truth_actorDoubleWordFormula {n} (w zero unit g h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actorDoubleWordFormula w zero unit g h) env ↔
      env w = {ZFSet.pair (env zero) (ZFSet.pair (env zero) (env g)),
        ZFSet.pair (env unit) (ZFSet.pair (env zero) (env h))} := by
  simp only [actorDoubleWordFormula, truth_exMem, Truth,
    truth_nonemptyTupleFormula, truth_unorderedPairFormula]
  change (∃ z ∈ env w, ∃ v ∈ env w,
    z = ZFSet.pair (env zero) (ZFSet.pair (env zero) (env g)) ∧
    v = ZFSet.pair (env unit) (ZFSet.pair (env zero) (env h)) ∧ env w = {z, v}) ↔ _
  constructor
  · rintro ⟨z, _, v, _, rfl, rfl, eq⟩
    exact eq
  · intro eq
    exact ⟨_, eq.symm ▸ ZFSet.mem_pair.2 (Or.inl rfl),
      _, eq.symm ▸ ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl, eq⟩

theorem truth_signedDoubleWordFormula {n} (w zero unit s a b : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (signedDoubleWordFormula w zero unit s a b) env ↔
      env w = {ZFSet.pair (env zero) (ZFSet.pair (env unit) (ZFSet.pair (env s) (env a))),
        ZFSet.pair (env unit) (ZFSet.pair (env unit) (ZFSet.pair (env s) (env b)))} := by
  simp only [signedDoubleWordFormula, truth_exMem, Truth,
    truth_nonemptyTupleFormula, truth_unorderedPairFormula]
  change (∃ z ∈ env w, ∃ v ∈ env w,
    z = ZFSet.pair (env zero) (ZFSet.pair (env unit) (ZFSet.pair (env s) (env a))) ∧
    v = ZFSet.pair (env unit) (ZFSet.pair (env unit) (ZFSet.pair (env s) (env b))) ∧
    env w = {z, v}) ↔ _
  constructor
  · rintro ⟨z, _, v, _, rfl, rfl, eq⟩
    exact eq
  · intro eq
    exact ⟨_, eq.symm ▸ ZFSet.mem_pair.2 (Or.inl rfl),
      _, eq.symm ▸ ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl, eq⟩

theorem truth_externalWordAtomicFormula {n} (zero unit G S m one l r : Fin n)
    (env : Fin n → ZFSet.{u}) (zeroValue : env zero = natSetCode 0)
    (unitValue : env unit = natSetCode 1) :
    Truth (externalWordAtomicFormula zero unit G S m one l r) env ↔
      ExternalWordAtomicCode (env G) (env S) (env m) (env one) (env l) (env r) := by
  simp only [externalWordAtomicFormula, truth_disj, truth_exMem, Truth,
    truth_actorSingletonWordFormula, truth_actorDoubleWordFormula, truth_signedDoubleWordFormula,
    truth_emptyFormula, truth_tripleMembershipFormula]
  change ((env one ∈ env G ∧ env l = {ZFSet.pair (env zero) (ZFSet.pair (env zero) (env one))} ∧ env r = ∅) ∨
    (∃ g ∈ env G, ∃ h ∈ env G, ∃ k ∈ env G, ZFSet.pair (ZFSet.pair g h) k ∈ env m ∧
      env l = {ZFSet.pair (env zero) (ZFSet.pair (env zero) g), ZFSet.pair (env unit) (ZFSet.pair (env zero) h)} ∧
      env r = {ZFSet.pair (env zero) (ZFSet.pair (env zero) k)}) ∨
    (∃ s ∈ env S,
      (env l = {ZFSet.pair (env zero) (ZFSet.pair (env unit) (ZFSet.pair s (env zero))),
          ZFSet.pair (env unit) (ZFSet.pair (env unit) (ZFSet.pair s (env unit)))} ∨
        env l = {ZFSet.pair (env zero) (ZFSet.pair (env unit) (ZFSet.pair s (env unit))),
          ZFSet.pair (env unit) (ZFSet.pair (env unit) (ZFSet.pair s (env zero)))}) ∧ env r = ∅)) ↔ _
  rw [zeroValue, unitValue]
  rfl

theorem truth_externalWordStepFormula {n} (W append zero unit G S m one f g : Fin n)
    (env : Fin n → ZFSet.{u}) (zeroValue : env zero = natSetCode 0)
    (unitValue : env unit = natSetCode 1) :
    Truth (externalWordStepFormula W append zero unit G S m one f g) env ↔
      ExternalWordStepCode (env W) (env append) (env G) (env S) (env m) (env one) (env f) (env g) := by
  simp only [externalWordStepFormula, truth_exMem, Truth, truth_tripleMembershipFormula, truth_disj,
    ExternalWordStepCode]
  constructor
  · rintro ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr, atomic, left, right, direction⟩
    exact ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr,
      (truth_externalWordAtomicFormula zero.succ.succ.succ.succ.succ.succ
        unit.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ
        S.succ.succ.succ.succ.succ.succ m.succ.succ.succ.succ.succ.succ
        one.succ.succ.succ.succ.succ.succ 3 2
        (extend pr (extend pl (extend r (extend l (extend post (extend pre env)))))) zeroValue unitValue).1 atomic, left, right, direction⟩
  · rintro ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr, atomic, left, right, direction⟩
    exact ⟨pre, hp, post, hq, l, hl, r, hr, pl, hpl, pr, hpr,
      (truth_externalWordAtomicFormula zero.succ.succ.succ.succ.succ.succ
        unit.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ
        S.succ.succ.succ.succ.succ.succ m.succ.succ.succ.succ.succ.succ
        one.succ.succ.succ.succ.succ.succ 3 2
        (extend pr (extend pl (extend r (extend l (extend post (extend pre env)))))) zeroValue unitValue).2 atomic, left, right, direction⟩

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalRewriteSteps
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

theorem truth_externalWordStepEntryFormula {n} (z W append zero unit G S m one : Fin n)
    (env : Fin n → ZFSet.{u}) (zeroValue : env zero = natSetCode 0)
    (unitValue : env unit = natSetCode 1) :
    Truth (externalWordStepEntryFormula z W append zero unit G S m one) env ↔
      ∃ f ∈ env W, ∃ g ∈ env W, env z = ZFSet.pair f g ∧
        ExternalWordStepCode (env W) (env append) (env G) (env S) (env m) (env one) f g := by
  simp only [externalWordStepEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  constructor
  · rintro ⟨f, hf, g, hg, equal, step⟩
    exact ⟨f, hf, g, hg, equal,
      (truth_externalWordStepFormula W.succ.succ append.succ.succ zero.succ.succ unit.succ.succ
        G.succ.succ S.succ.succ m.succ.succ one.succ.succ 1 0 (extend g (extend f env)) zeroValue unitValue).1 step⟩
  · rintro ⟨f, hf, g, hg, equal, step⟩
    exact ⟨f, hf, g, hg, equal,
      (truth_externalWordStepFormula W.succ.succ append.succ.succ zero.succ.succ unit.succ.succ
        G.succ.succ S.succ.succ m.succ.succ one.succ.succ 1 0 (extend g (extend f env)) zeroValue unitValue).2 step⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalWordStepGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {W append G S m one : ZFSet.{u}}
    (hW : W ∈ M.sets) (hAppend : append ∈ M.sets) (hG : G ∈ M.sets)
    (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    externalWordStepGraph W append G S m one ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨W, hW⟩
  have hUnit : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  let params := extend W (extend append (extend (natSetCode 0) (extend (natSetCode 1)
    (extend G (extend S (extend m (extend one Fin.elim0)))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalWordStepEntryFormula 0 1 2 3 4 5 6 7 8) params
    (Fin.cases hW (Fin.cases hAppend (Fin.cases hZero (Fin.cases hUnit
      (Fin.cases hG (Fin.cases hS (Fin.cases hm (Fin.cases hOne (fun j => Fin.elim0 j)))))))))
    (M.prod_mem pairing unions powers separation hW hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalWordStepEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (ZFSet.prod W W) = externalWordStepGraph W append G S m one := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, externalWordStepGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalWordStepEntryFormula
      0 1 2 3 4 5 6 7 8 _ rfl rfl)
  exact equal ▸ selected

theorem externalWordSteps_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {G S m one : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets)
    (hm : m ∈ M.sets) (hOne : one ∈ M.sets) : M.externalWordSteps G S m one ∈ M.sets := by
  have alphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  exact M.externalWordStepGraph_mem pairing unions powers separation
    (M.finiteWords_mem pairing unions powers separation infinite alphabet)
    (M.finiteWordAppendGraph_mem pairing unions powers separation infinite alphabet) hG hS hm hOne

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundExternalWordQuotient
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

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite

theorem externalWordEquivalence_mem {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    M.externalWordEquivalence G S m one ∈ M.sets :=
  M.finitePathClosure_mem pairing unions powers separation infinite
    (M.finiteWords_mem pairing unions powers separation infinite
      (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS))
    (M.externalWordSteps_mem pairing unions powers separation infinite hG hS hm hOne)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ExternalWordInverseEvaluation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.ExternalWordRewrite
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (J S : Type u) [Group J]

theorem symbolValue_inverse (a : Alphabet J S) :
    symbolValue J S (externalSymbolInverse a) = (symbolValue J S a)⁻¹ := by
  cases a with
  | inl g => exact map_inv (old J S) g
  | inr p =>
    change free J S (FreeGroup.mk [(p.1, !p.2)]) = (free J S (FreeGroup.mk [p]))⁻¹
    rw [← map_inv, FreeGroup.inv_mk]
    rfl

theorem evalWord_inverse (xs : List (Alphabet J S)) :
    evalWord J S ((xs.map externalSymbolInverse).reverse) = (evalWord J S xs)⁻¹ := by
  induction xs with
  | nil => exact (inv_one : (1 : External J S)⁻¹ = 1).symm
  | cons a xs ih =>
    rw [List.map_cons, List.reverse_cons]
    have append (v w : List (Alphabet J S)) :
        evalWord J S (v ++ w) = evalWord J S v * evalWord J S w :=
      (evalWord J S).map_mul v w
    rw [append, ih]
    have singleton : evalWord J S [externalSymbolInverse a] = (symbolValue J S a)⁻¹ := by
      exact symbolValue_inverse J S a
    have cons : evalWord J S (a :: xs) = symbolValue J S a * evalWord J S xs := by
      exact (evalWord J S).map_mul (FreeMonoid.of a) (FreeMonoid.ofList xs)
    rw [singleton, cons, mul_inv_rev]

end PartitionPilot.Forcing.ExternalWordRewrite

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundQuotientBinaryOperations
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

theorem truth_quotientBinaryEntryFormula {n} (z w q classifier op : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (quotientBinaryEntryFormula z w q classifier op) env ↔
      env z ∈ quotientBinaryGraph (env w) (env q) (env classifier) (env op) := by
  simp only [quotientBinaryEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, mem_quotientBinaryGraph]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem quotientBinaryGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {W Q classifier op : ZFSet.{u}} (hW : W ∈ M.sets) (hQ : Q ∈ M.sets)
    (hc : classifier ∈ M.sets) (ho : op ∈ M.sets) :
    quotientBinaryGraph W Q classifier op ∈ M.sets := by
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hQ hQ) hQ
  let params := extend W (extend Q (extend classifier (extend op Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.quotientBinaryEntryFormula 0 1 2 3 4) params
    (Fin.cases hW (Fin.cases hQ (Fin.cases hc (Fin.cases ho (fun i => Fin.elim0 i))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.quotientBinaryEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod Q Q) Q) = quotientBinaryGraph W Q classifier op := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_quotientBinaryEntryFormula]
    change (z ∈ ZFSet.prod (ZFSet.prod Q Q) Q ∧ z ∈ quotientBinaryGraph W Q classifier op) ↔ _
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundQuotientUnaryOperations
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

theorem mem_quotientUnaryGraph (W Q classifier op z : ZFSet.{u}) :
    z ∈ quotientUnaryGraph W Q classifier op ↔
      ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair a b ∧ ∃ x ∈ W, ∃ y ∈ W,
        ZFSet.pair x a ∈ classifier ∧ ZFSet.pair y b ∈ classifier ∧ ZFSet.pair x y ∈ op := by
  rw [quotientUnaryGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨a, ha, b, hb, eq, rest⟩
  exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, a, ha, b, hb, eq, rest⟩

theorem quotientUnaryGraph_eq_graph {A B : Type u} (s : Presentation A) (t : Presentation B)
    (q : A → B) (source : A → A) (target : B → B)
    (onto : Function.Surjective q) (compatible : ∀ x, q (source x) = target (q x)) :
    quotientUnaryGraph s.carrier t.carrier (s.graph t q) (s.graph s source) = t.graph t target := by
  apply ZFSet.ext
  intro z
  rw [mem_quotientUnaryGraph, Presentation.mem_graph]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, x, hx, y, hy, xa, yb, op⟩
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    have first := (s.pair_mem_graph t q x a).1 xa
    have output := (s.pair_mem_graph t q y b).1 yb
    have value := (s.pair_mem_graph s source x y).1 op
    have equal : target a = b := by
      rw [← first, ← compatible, value]
      exact output
    exact ⟨a, by rw [equal]⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := onto a
    exact ⟨t.encode (q x), t.encode_mem _, t.encode (target (q x)), t.encode_mem _, rfl,
      s.encode x, s.encode_mem _, s.encode (source x), s.encode_mem _,
      (s.pair_mem_graph t q _ _).2 rfl, (s.pair_mem_graph t q _ _).2 (compatible x),
      (s.pair_mem_graph s source _ _).2 rfl⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_quotientUnaryEntryFormula {n} (z w q classifier op : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (quotientUnaryEntryFormula z w q classifier op) env ↔
      env z ∈ quotientUnaryGraph (env w) (env q) (env classifier) (env op) := by
  simp only [quotientUnaryEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, mem_quotientUnaryGraph]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem quotientUnaryGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {W Q classifier op : ZFSet.{u}} (hW : W ∈ M.sets) (hQ : Q ∈ M.sets)
    (hc : classifier ∈ M.sets) (ho : op ∈ M.sets) :
    quotientUnaryGraph W Q classifier op ∈ M.sets := by
  have bound := M.prod_mem pairing unions powers separation hQ hQ
  let params := extend W (extend Q (extend classifier (extend op Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.quotientUnaryEntryFormula 0 1 2 3 4) params
    (Fin.cases hW (Fin.cases hQ (Fin.cases hc (Fin.cases ho (fun i => Fin.elim0 i))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.quotientUnaryEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod Q Q) = quotientUnaryGraph W Q classifier op := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_quotientUnaryEntryFormula]
    change (z ∈ ZFSet.prod Q Q ∧ z ∈ quotientUnaryGraph W Q classifier op) ↔ _
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalGroupOperationGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite in
theorem externalGroupOperations_ground {G S m inv one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets)
    (hInv : inv ∈ M.sets) (hOne : one ∈ M.sets) :
    M.externalGroupCarrier G S m one ∈ M.sets ∧
      M.externalGroupMultiplication G S m one ∈ M.sets ∧
      M.externalGroupInverse G S m inv one ∈ M.sets ∧
      M.externalGroupIdentity G S m one ∈ M.sets ∧
      M.externalGroupProjection G S m one ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hE := M.externalWordEquivalence_mem pairing unions powers separation infinite hG hS hm hOne
  have hQ := M.equivalenceClasses_mem powers separation hWords hE
  have hProjection := M.equivalenceClassifier_mem pairing unions powers separation hWords hE
  exact ⟨hQ,
    M.quotientBinaryGraph_mem pairing unions powers separation hWords hQ hProjection
      (M.finiteWordAppendGraph_mem pairing unions powers separation infinite hAlphabet),
    M.quotientUnaryGraph_mem pairing unions powers separation hWords hQ hProjection
      (M.externalInverseWordGraph_mem pairing unions powers separation infinite hG hS hInv),
    M.equivalenceClass_mem separation hWords hE (M.empty_mem ⟨G, hG⟩), hProjection⟩

variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

theorem externalGroupInverse_eq_graph :
    let q := M.externalGroupPresentation pairing unions powers separation infinite s t hG hS
    M.externalGroupInverse s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2)) (s.graph s Inv.inv) (s.encode 1) =
      q.graph q Inv.inv := by
  dsimp only
  unfold externalGroupInverse externalGroupProjection
  rw [M.externalGroupClassifier_eq_graph pairing unions powers separation infinite s t hG hS]
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  rw [M.externalInverseWordGraph_eq_graph pairing unions separation infinite s t hAlphabet]
  exact quotientUnaryGraph_eq_graph
    (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M pairing unions separation infinite hAlphabet)
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    (ExternalWordRewrite.evalWord J L) externalWordInverse Inv.inv
    (ExternalWordRewrite.evalWord_surjective J L) (ExternalWordRewrite.evalWord_inverse J L)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBatchHeightGraphs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_componentHeightEntryFormula {n}
    (w I Qs B Hs Cs E C D boundQs boundHs boundE : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (componentHeightEntryFormula w I Qs B Hs Cs E C D boundQs boundHs boundE) env ↔
      ∃ i ∈ env I, ∃ Q ∈ env boundQs, ∃ g ∈ env boundHs, ∃ f ∈ env boundE,
        ∃ q ∈ Q, ∃ a ∈ env B, ∃ c ∈ env C, ∃ z ∈ env D,
          env w = ZFSet.pair (ZFSet.pair i q) (ZFSet.pair c z) ∧
          ZFSet.pair i Q ∈ env Qs ∧ ZFSet.pair i g ∈ env Hs ∧ ZFSet.pair i f ∈ env E ∧
          ZFSet.pair i c ∈ env Cs ∧ ZFSet.pair q a ∈ g ∧ ZFSet.pair a z ∈ f := by
  simp only [componentHeightEntryFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

theorem truth_taggedHeightEntryFormula {n} (w P N H fresh : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taggedHeightEntryFormula w P N H fresh) env ↔
      ∃ x ∈ env N, ∃ h ∈ env H,
        env w = ZFSet.pair (ZFSet.pair (env P) x) h ∧ ZFSet.pair x h ∈ env fresh := by
  simp only [taggedHeightEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem componentHeightGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs B Hs Cs E C D : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hB : B ∈ M.sets) (hHs : Hs ∈ M.sets)
    (hCs : Cs ∈ M.sets) (hE : E ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    componentHeightGraph I Qs B Hs Cs E C D ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have hBound := M.union_mem unions (M.union_mem unions hHs)
  have eBound := M.union_mem unions (M.union_mem unions hE)
  let params := extend I (extend Qs (extend B (extend Hs (extend Cs (extend E
    (extend C (extend D (extend (⋃₀ ⋃₀ Qs) (extend (⋃₀ ⋃₀ Hs)
      (extend (⋃₀ ⋃₀ E) Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.componentHeightEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) params
    (Fin.cases hI (Fin.cases hQs (Fin.cases hB (Fin.cases hHs (Fin.cases hCs
      (Fin.cases hE (Fin.cases hC (Fin.cases hD (Fin.cases qBound
        (Fin.cases hBound (Fin.cases eBound (fun i => Fin.elim0 i))))))))))))
    (M.prod_mem pairing unions powers separation
      (M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs)
      (M.prod_mem pairing unions powers separation hC hD))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.componentHeightEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) (extend z params))
      (ZFSet.prod (indexedAttachmentDomain I Qs) (ZFSet.prod C D)) =
      componentHeightGraph I Qs B Hs Cs E C D := by
    apply ZFSet.ext
    intro z
    rw [componentHeightGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_componentHeightEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 _)
  exact equal ▸ selected

theorem taggedHeightGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P N H old fresh : ZFSet.{u}}
    (hP : P ∈ M.sets) (hN : N ∈ M.sets) (hH : H ∈ M.sets)
    (hold : old ∈ M.sets) (hfresh : fresh ∈ M.sets) :
    taggedHeightGraph P N H old fresh ∈ M.sets := by
  let params := extend P (extend N (extend H (extend fresh Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.taggedHeightEntryFormula 0 1 2 3 4) params
    (Fin.cases hP (Fin.cases hN (Fin.cases hH (Fin.cases hfresh (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation
      (M.taggedExtension_mem pairing unions powers separation hP hN) hH)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.taggedHeightEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (taggedExtension P N) H) =
      ZFSet.sep (fun w => ∃ x ∈ N, ∃ h ∈ H,
        w = ZFSet.pair (ZFSet.pair P x) h ∧ ZFSet.pair x h ∈ fresh)
        (ZFSet.prod (taggedExtension P N) H) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taggedHeightEntryFormula 0 1 2 3 4 _)
  exact M.binary_union_mem pairing unions hold (equal ▸ selected)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableProducts
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem countableProduct_injection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B f g : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hf : f ∈ M.sets) (hg : g ∈ M.sets)
    (first : InjectionCode A ZFSet.omega f) (second : InjectionCode B ZFSet.omega g) :
    ∃ h ∈ M.sets, InjectionCode (ZFSet.prod A B) ZFSet.omega h := by
  have hw := M.omega_mem separation infinite
  have hAB := M.prod_mem pairing unions powers separation hA hB
  have hww := M.prod_mem pairing unions powers separation hw hw
  have product := M.relationProduct_mem pairing unions powers separation hA hB hw hw hf hg
  obtain ⟨c, hc, pairingCode⟩ := M.omega_product_countable pairing unions powers separation infinite
  exact ⟨relationCompose (ZFSet.prod A B) (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega
      (relationProduct A B ZFSet.omega ZFSet.omega f g) c,
    M.relationCompose_mem pairing unions powers separation hAB hww hw product hc,
    (relationProduct_injection first second).compose pairingCode⟩

theorem groundEmbeddable_product
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (first : M.groundEmbeddable A ZFSet.omega) (second : M.groundEmbeddable B ZFSet.omega) :
    M.groundEmbeddable (ZFSet.prod A B) ZFSet.omega := by
  obtain ⟨f, hf, firstCode⟩ := first
  obtain ⟨g, hg, secondCode⟩ := second
  exact M.countableProduct_injection pairing unions powers separation infinite hA hB hf hg firstCode secondCode

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_HeightColumnBoundLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem mem_heightColumns_of_entry {P C D old x c q : ZFSet.{u}}
    (function : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (entry : ZFSet.pair x (ZFSet.pair c q) ∈ old) : c ∈ heightColumns P C D old := by
  have shape := ZFSet.pair_mem_prod.1 (function.1 entry)
  have coordinates := ZFSet.pair_mem_prod.1 shape.2
  exact (mem_relationImage _ _ _ c).2 ⟨coordinates.1, ZFSet.pair c q,
    (mem_relationImage _ _ _ _).2 ⟨shape.2, x, shape.1, entry⟩,
    (mem_productFirst C D _).2 ⟨c, coordinates.1, q, coordinates.2, rfl⟩⟩

theorem height_range_subset_columns {P L C D old height : ZFSet.{u}}
    (columns : ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height →
      c ∈ heightColumns P C D old) :
    relationImage L (ZFSet.prod C D) height ⊆ ZFSet.prod (heightColumns P C D old) D := by
  intro y hy
  obtain ⟨hy, x, _, entry⟩ := (mem_relationImage L (ZFSet.prod C D) height y).1 hy
  obtain ⟨c, _, q, hq, rfl⟩ := ZFSet.mem_prod.1 hy
  exact ZFSet.pair_mem_prod.2 ⟨columns x c q entry, hq⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightColumns_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P C D old : ZFSet.{u}} (hP : P ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hOld : old ∈ M.sets) : heightColumns P C D old ∈ M.sets :=
  M.relationImage_mem separation
    (M.relationImage_mem separation hP (M.prod_mem pairing unions powers separation hC hD) hOld)
    hC (M.productFirst_mem pairing unions powers separation hC hD)

theorem heightColumns_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P C D old : ZFSet.{u}} (hP : P ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hOld : old ∈ M.sets)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega) :
    M.groundEmbeddable (heightColumns P C D old) ZFSet.omega :=
  M.groundEmbeddable_function_image pairing unions powers separation choice
    (M.relationImage_mem separation hP (M.prod_mem pairing unions powers separation hC hD) hOld)
    hC (M.omega_mem separation infinite)
    (M.productFirst_mem pairing unions powers separation hC hD) (productFirst_function C D) small

theorem countable_height_range_of_old_columns
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P L C D old height : ZFSet.{u}}
    (hP : P ∈ M.sets) (hL : L ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) (hHeight : height ∈ M.sets)
    (oldSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega)
    (coordinateSmall : M.groundEmbeddable D ZFSet.omega)
    (columns : ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height →
      c ∈ heightColumns P C D old) :
    relationImage L (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage L (ZFSet.prod C D) height) ZFSet.omega := by
  have rangeMember := M.relationImage_mem separation hL
    (M.prod_mem pairing unions powers separation hC hD) hHeight
  have smallColumns := M.heightColumns_countable pairing unions powers separation infinite choice
    hP hC hD hOld oldSmall
  have smallProduct := M.groundEmbeddable_product pairing unions powers separation infinite
    (M.heightColumns_mem pairing unions powers separation hP hC hD hOld) hD
    smallColumns coordinateSmall
  exact ⟨rangeMember, M.groundEmbeddable_restrict separation rangeMember
    (M.omega_mem separation infinite) (height_range_subset_columns columns) smallProduct⟩

end TransitiveGround

theorem heightColumns_subset_of_bound {P C D height K : ZFSet.{u}}
    (bound : ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height → c ∈ K) :
    heightColumns P C D height ⊆ K := by
  intro c hc
  obtain ⟨_, y, hy, projected⟩ :=
    (mem_relationImage (relationImage P (ZFSet.prod C D) height) C (productFirst C D) c).1 hc
  obtain ⟨a, ha, q, hq, equal⟩ := (mem_productFirst C D _).1 projected
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  obtain ⟨_, x, _, entry⟩ := (mem_relationImage P (ZFSet.prod C D) height _).1 hy
  exact bound x c q entry

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundTemplateHeightRanges
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing

universe u

namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Bs brs Hs : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t : TemplateHeightFamilyInputs d Bs brs Hs)

theorem heightImageCandidate_iff (i : {i : ZFSet.{u} // i ∈ I}) (R : ZFSet.{u}) :
    heightImageCandidate Qs Bs Hs i.val R ↔
      R = relationImage (d.space i) (t.ranges.value i) (t.heights.value i) := by
  constructor
  · rintro ⟨Q, _, B, _, h, _, eQ, eB, eh, equal⟩
    have eqQ := d.spaces.unique eQ (d.space_entry i)
    have eqB := t.ranges.unique eB (t.ranges.value_entry i)
    have eqh := t.heights.unique eh (t.heights.value_entry i)
    exact eqQ ▸ eqB ▸ eqh ▸ equal
  · intro equal
    exact ⟨d.space i, d.spaces.value_mem_doubleUnion i,
      t.ranges.value i, t.ranges.value_mem_doubleUnion i,
      t.heights.value i, t.heights.value_mem_doubleUnion i,
      d.space_entry i, t.ranges.value_entry i, t.heights.value_entry i, equal⟩

end TemplateHeightFamilyInputs

theorem heightOrderCandidate_iff {I Rs brs : ZFSet.{u}}
    (ranges : FunctionGraphOn I Rs) (orders : FunctionGraphOn I brs)
    (i : {i : ZFSet.{u} // i ∈ I}) (r : ZFSet.{u}) :
    heightOrderCandidate Rs brs i.val r ↔
      r = heightOrderRestriction (ranges.value i) (orders.value i) := by
  constructor
  · rintro ⟨R, _, s, _, eR, es, equal⟩
    exact ranges.unique eR (ranges.value_entry i) ▸ orders.unique es (orders.value_entry i) ▸ equal
  · intro equal
    exact ⟨ranges.value i, ranges.value_mem_doubleUnion i,
      orders.value i, orders.value_mem_doubleUnion i,
      ranges.value_entry i, orders.value_entry i, equal⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem heightImageFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W Qs Bs Hs : ZFSet.{u}}
    (hI : I ∈ M.sets) (hW : W ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hBs : Bs ∈ M.sets) (hHs : Hs ∈ M.sets) : heightImageFamily I W Qs Bs Hs ∈ M.sets := by
  have qBound := M.union_mem unions (M.union_mem unions hQs)
  have bBound := M.union_mem unions (M.union_mem unions hBs)
  have hBound := M.union_mem unions (M.union_mem unions hHs)
  let params := extend I (extend W (extend Qs (extend Bs (extend Hs
    (extend (⋃₀ ⋃₀ Qs) (extend (⋃₀ ⋃₀ Bs) (extend (⋃₀ ⋃₀ Hs) Fin.elim0)))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.heightImageFamilyEntryFormula 0 1 2 3 4 5 6 7 8) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hQs (Fin.cases hBs (Fin.cases hHs
      (Fin.cases qBound (Fin.cases bBound (Fin.cases hBound (fun i => Fin.elim0 i)))))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.heightImageFamilyEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (ZFSet.prod I W) = heightImageFamily I W Qs Bs Hs := by
    apply ZFSet.ext
    intro z
    rw [heightImageFamily, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_heightImageFamilyEntryFormula 0 1 2 3 4 5 6 7 8 _ rfl rfl rfl)
  exact equal ▸ selected

theorem heightOrderFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I W Rs brs : ZFSet.{u}}
    (hI : I ∈ M.sets) (hW : W ∈ M.sets) (hRs : Rs ∈ M.sets) (hbrs : brs ∈ M.sets) :
    heightOrderFamily I W Rs brs ∈ M.sets := by
  have rBound := M.union_mem unions (M.union_mem unions hRs)
  have sBound := M.union_mem unions (M.union_mem unions hbrs)
  let params := extend I (extend W (extend Rs (extend brs
    (extend (⋃₀ ⋃₀ Rs) (extend (⋃₀ ⋃₀ brs) Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.heightOrderFamilyEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hRs (Fin.cases hbrs
      (Fin.cases rBound (Fin.cases sBound (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.heightOrderFamilyEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod I W) = heightOrderFamily I W Rs brs := by
    apply ZFSet.ext
    intro z
    rw [heightOrderFamily, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_heightOrderFamilyEntryFormula 0 1 2 3 4 5 6 _ rfl rfl)
  exact equal ▸ selected

theorem exists_templateHeightRanges
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P rP μP I Qs rs μs As Es Fs Ss Bs brs Hs : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (t₀ : TemplateHeightFamilyInputs d Bs brs Hs)
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hBs : Bs ∈ M.sets)
    (hbrs : brs ∈ M.sets) (hHs : Hs ∈ M.sets) :
    ∃ Rs ∈ M.sets, ∃ ors ∈ M.sets, ∃ t : TemplateHeightFamilyInputs d Rs ors Hs,
      (∀ i, t.ranges.value i = relationImage (d.space i) (t₀.ranges.value i) (t₀.heights.value i)) ∧
      (∀ i, t.orders.value i = heightOrderRestriction (t.ranges.value i) (t₀.orders.value i)) := by
  let B := familyPointBound Bs
  have hB : B ∈ M.sets := M.familyPointBound_mem unions hBs
  let W := M.groundPower B
  have hW : W ∈ M.sets := M.groundPower_mem powers hB
  let Rs := heightImageFamily I W Qs Bs Hs
  have hRs : Rs ∈ M.sets := M.heightImageFamily_mem pairing unions powers separation hI hW hQs hBs hHs
  have imageGround (i : {i : ZFSet.{u} // i ∈ I}) :
      relationImage (d.space i) (t₀.ranges.value i) (t₀.heights.value i) ∈ M.sets :=
    M.relationImage_mem separation (d.spaces.value_mem M hQs i)
      (t₀.ranges.value_mem M hBs i) (t₀.heights.value_mem M hHs i)
  have imageBound (i : {i : ZFSet.{u} // i ∈ I}) :
      relationImage (d.space i) (t₀.ranges.value i) (t₀.heights.value i) ⊆ B := by
    intro a ha
    exact mem_familyPointBound_of_entry (t₀.ranges.value_entry i) ((mem_relationImage _ _ _ a).1 ha).1
  have rangesFunction : ZFSet.IsFunc I W Rs := by
    refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
    intro i hi
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    let R := relationImage (d.space j) (t₀.ranges.value j) (t₀.heights.value j)
    have hR : R ∈ W := (M.mem_groundPower B R).2 ⟨imageGround j, imageBound j⟩
    exact ⟨R, (pair_mem_heightImageFamily I W Qs Bs Hs i R).2
      ⟨hi, hR, (t₀.heightImageCandidate_iff j R).2 rfl⟩,
      fun R' entry => (t₀.heightImageCandidate_iff j R').1
        ((pair_mem_heightImageFamily I W Qs Bs Hs i R').1 entry).2.2⟩
  let ranges : FunctionGraphOn I Rs := ⟨W, rangesFunction⟩
  have rangesEqual (i : {i : ZFSet.{u} // i ∈ I}) :
      ranges.value i = relationImage (d.space i) (t₀.ranges.value i) (t₀.heights.value i) :=
    (t₀.heightImageCandidate_iff i _).1
      ((pair_mem_heightImageFamily I W Qs Bs Hs i.val _).1 (ranges.value_entry i)).2.2
  have rangesBound (i : {i : ZFSet.{u} // i ∈ I}) : ranges.value i ⊆ B :=
    rangesEqual i ▸ imageBound i
  let U := M.groundRelations B B
  have hU : U ∈ M.sets := M.groundRelations_mem pairing unions powers separation hB hB
  let ors := heightOrderFamily I U Rs brs
  have hors : ors ∈ M.sets := M.heightOrderFamily_mem pairing unions powers separation hI hU hRs hbrs
  have ordersFunction : ZFSet.IsFunc I U ors := by
    refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
    intro i hi
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    let r := heightOrderRestriction (ranges.value j) (t₀.orders.value j)
    have hr : r ∈ M.sets := M.injection_restriction_mem separation
      (ranges.value_mem M hRs j) (ranges.value_mem M hRs j) (t₀.orders.value_mem M hbrs j)
    have bound : r ⊆ ZFSet.prod B B := by
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).2
      exact ZFSet.pair_mem_prod.2 ⟨rangesBound j ha, rangesBound j hb⟩
    exact ⟨r, (pair_mem_heightOrderFamily I U Rs brs i r).2
      ⟨hi, (M.mem_groundRelations B B r).2 ⟨hr, bound⟩,
        (heightOrderCandidate_iff ranges t₀.orders j r).2 rfl⟩,
      fun s entry => (heightOrderCandidate_iff ranges t₀.orders j s).1
        ((pair_mem_heightOrderFamily I U Rs brs i s).1 entry).2.2⟩
  let orders : FunctionGraphOn I ors := ⟨U, ordersFunction⟩
  have ordersEqual (i : {i : ZFSet.{u} // i ∈ I}) :
      orders.value i = heightOrderRestriction (ranges.value i) (t₀.orders.value i) :=
    (heightOrderCandidate_iff ranges t₀.orders i _).1
      ((pair_mem_heightOrderFamily I U Rs brs i.val _).1 (orders.value_entry i)).2.2
  have functions (i : {i : ZFSet.{u} // i ∈ I}) :
      ZFSet.IsFunc (d.space i) (ranges.value i) (t₀.heights.value i) := by
    rw [rangesEqual i]
    exact function_on_relationImage (t₀.function i)
  let t : TemplateHeightFamilyInputs d Rs ors Hs :=
    { ranges := ranges
      orders := orders
      heights := t₀.heights
      linear := fun i => by
        rw [ordersEqual i]
        apply heightOrderRestriction_linear (t₀.linear i)
        intro a ha
        rw [rangesEqual i] at ha
        exact ((mem_relationImage _ _ _ a).1 ha).1
      function := functions
      strict := fun i x y a b below different first second => by
        rw [ordersEqual i]
        exact (pair_mem_heightOrderRestriction _ _ a b).2
          ⟨t₀.strict i x y a b below different first second,
            (ZFSet.pair_mem_prod.1 ((functions i).1 first)).2,
            (ZFSet.pair_mem_prod.1 ((functions i).1 second)).2⟩ }
  exact ⟨Rs, hRs, ors, hors, t, rangesEqual, ordersEqual⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalGenerators
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

namespace BoundedFormula

theorem truth_externalActorSymbolEntryFormula {n} (z G alphabet zero : Fin n)
    (env : Fin n → ZFSet.{u}) (hZero : env zero = natSetCode 0) :
    Truth (externalActorSymbolEntryFormula z G alphabet zero) env ↔
      ∃ g ∈ env G, ∃ a ∈ env alphabet, env z = ZFSet.pair g a ∧ a = externalActorSymbol g := by
  simp only [externalActorSymbolEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ g ∈ env G, ∃ a ∈ env alphabet, env z = ZFSet.pair g a ∧
    a = ZFSet.pair (env zero) g) ↔ _
  rw [hZero]
  rfl

theorem truth_externalGeneratorSymbolEntryFormula {n} (z S alphabet one : Fin n)
    (env : Fin n → ZFSet.{u}) (hOne : env one = natSetCode 1) :
    Truth (externalGeneratorSymbolEntryFormula z S alphabet one) env ↔
      ∃ s ∈ env S, ∃ a ∈ env alphabet, env z = ZFSet.pair s a ∧ a = externalLetterSymbol s true := by
  simp only [externalGeneratorSymbolEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_orderedRightTripleFormula]
  change (∃ s ∈ env S, ∃ a ∈ env alphabet, env z = ZFSet.pair s a ∧
    a = ZFSet.pair (env one) (ZFSet.pair s (env one))) ↔ _
  rw [hOne]
  rfl

end BoundedFormula

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem externalActorSymbolGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G S : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    externalActorSymbolGraph G S ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨G, hG⟩
  let params := extend G (extend (externalGeneratorAlphabet G S) (extend (natSetCode 0) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalActorSymbolEntryFormula 0 1 2 3) params
    (Fin.cases hG (Fin.cases hAlphabet (Fin.cases hZero (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hG hAlphabet)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalActorSymbolEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod G (externalGeneratorAlphabet G S)) = externalActorSymbolGraph G S := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, externalActorSymbolGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalActorSymbolEntryFormula 0 1 2 3 _ rfl)
  exact equal ▸ selected

theorem externalGeneratorSymbolGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G S : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    externalGeneratorSymbolGraph G S ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨G, hG⟩
  have hOne : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  let params := extend S (extend (externalGeneratorAlphabet G S) (extend (natSetCode 1) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalGeneratorSymbolEntryFormula 0 1 2 3) params
    (Fin.cases hS (Fin.cases hAlphabet (Fin.cases hOne (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hS hAlphabet)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalGeneratorSymbolEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod S (externalGeneratorAlphabet G S)) = externalGeneratorSymbolGraph G S := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, externalGeneratorSymbolGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalGeneratorSymbolEntryFormula 0 1 2 3 _ rfl)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

section

namespace PartitionPilot.Forcing

open SetRealization SetFormula
universe u

namespace BoundedFormula

theorem truth_singletonWordFormula {n} (w zero x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (singletonWordFormula w zero x) env ↔ env w = {ZFSet.pair (env zero) (env x)} := by
  simp only [singletonWordFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_singletonFormula]
  change (∃ z ∈ env w, z = ZFSet.pair (env zero) (env x) ∧ env w = {z}) ↔ _
  constructor
  · rintro ⟨z, _, rfl, eq⟩
    exact eq
  · intro eq
    exact ⟨_, eq.symm ▸ ZFSet.mem_singleton.2 rfl, rfl, eq⟩

theorem truth_singletonWordEntryFormula {n} (z A W zero : Fin n)
    (env : Fin n → ZFSet.{u}) (hZero : env zero = natSetCode 0) :
    Truth (singletonWordEntryFormula z A W zero) env ↔
      ∃ x ∈ env A, ∃ w ∈ env W, env z = ZFSet.pair x w ∧ w = wordSingleton x := by
  simp only [singletonWordEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_singletonWordFormula]
  change (∃ x ∈ env A, ∃ w ∈ env W, env z = ZFSet.pair x w ∧
    w = {ZFSet.pair (env zero) x}) ↔ _
  rw [hZero]
  rfl

end BoundedFormula

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem singletonWordGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A W : ZFSet.{u}} (hA : A ∈ M.sets) (hW : W ∈ M.sets) :
    singletonWordGraph A W ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨A, hA⟩
  let params := extend A (extend W (extend (natSetCode 0) Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.singletonWordEntryFormula 0 1 2 3) params
    (Fin.cases hA (Fin.cases hW (Fin.cases hZero (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hA hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.singletonWordEntryFormula 0 1 2 3) (extend z params)) (ZFSet.prod A W) =
      singletonWordGraph A W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, singletonWordGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_singletonWordEntryFormula 0 1 2 3 _ rfl)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite in
theorem externalGroup_code_of_presentation {J L : Type u} [Group J]
    (s : Presentation J) (t : Presentation L)
    (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets) :
    GroupCode
      (M.externalGroupCarrier s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
      (M.externalGroupMultiplication s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
      (M.externalGroupInverse s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2))
        (s.graph s Inv.inv) (s.encode 1))
      (M.externalGroupIdentity s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) := by
  rw [M.externalGroupMultiplication_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalGroupInverse_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalGroupIdentity_eq_encode pairing unions powers separation infinite s t hG hS]
  exact (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).groupCode

include pairing unions powers separation infinite in
theorem externalGroup_code {G S m inv one : ZFSet.{u}} (group : GroupCode G m inv one)
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    GroupCode (M.externalGroupCarrier G S m one) (M.externalGroupMultiplication G S m one)
      (M.externalGroupInverse G S m inv one) (M.externalGroupIdentity G S m one) := by
  let := group.toGroup
  have code := M.externalGroup_code_of_presentation pairing unions powers separation infinite
    (SetMembers.presentation G) (SetMembers.presentation S) hG hS
  rw [group.multiplication_graph_eq, group.inverse_graph_eq, group.identity_code_eq] at code
  exact code

include pairing unions powers separation infinite in
theorem externalGroupData {G S m inv one : ZFSet.{u}} (group : GroupCode G m inv one)
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hInv : inv ∈ M.sets) :
    GroundExternalGroupData M G S m inv one := by
  have ground := M.externalGroupOperations_ground pairing unions powers separation infinite hG hS hm hInv
    (M.transitive hG group.identity_mem)
  exact ⟨ground.1, ground.2.1, ground.2.2.1, ground.2.2.2.1, ground.2.2.2.2,
    M.externalGroup_code pairing unions powers separation infinite group hG hS⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite in
theorem externalSymbolClasses_mem {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    M.externalSymbolClasses G S m one ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hE := M.externalWordEquivalence_mem pairing unions powers separation infinite hG hS hm hOne
  have hQ := M.equivalenceClasses_mem powers separation hWords hE
  have hProjection := M.equivalenceClassifier_mem pairing unions powers separation hWords hE
  exact M.relationCompose_mem pairing unions powers separation hAlphabet hWords hQ
    (M.singletonWordGraph_mem pairing unions powers separation hAlphabet hWords) hProjection

include pairing unions powers separation infinite in
theorem externalGeneratorGraphs_mem {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    M.externalOldInclusion G S m one ∈ M.sets ∧
      M.externalChildGenerators G S m one ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hE := M.externalWordEquivalence_mem pairing unions powers separation infinite hG hS hm hOne
  have hQ := M.equivalenceClasses_mem powers separation hWords hE
  have hClasses := M.externalSymbolClasses_mem pairing unions powers separation infinite hG hS hm hOne
  exact ⟨M.relationCompose_mem pairing unions powers separation hG hAlphabet hQ
      (M.externalActorSymbolGraph_mem pairing unions powers separation hG hS) hClasses,
    M.relationCompose_mem pairing unions powers separation hS hAlphabet hQ
      (M.externalGeneratorSymbolGraph_mem pairing unions powers separation hG hS) hClasses⟩

variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

include pairing unions powers separation infinite hG hS in
theorem externalGeneratorGraphs_injections :
    InjectionCode s.carrier
      (M.externalGroupCarrier s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
      (M.externalOldInclusion s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) ∧
    InjectionCode t.carrier
      (M.externalGroupCarrier s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
      (M.externalChildGenerators s.carrier t.carrier ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) := by
  rw [M.externalOldInclusion_eq_graph pairing unions powers separation infinite s t hG hS,
    M.externalChildGenerators_eq_graph pairing unions powers separation infinite s t hG hS]
  have generatorInj : Function.Injective (generator J L) :=
    (Monoid.CoprodI.of_injective (M := Factor J L) true).comp FreeGroup.of_injective
  let q := M.externalGroupPresentation pairing unions powers separation infinite s t hG hS
  exact ⟨s.graph_injection q _ (old_injective J L), t.graph_injection q _ generatorInj⟩

include pairing unions powers separation infinite in
theorem externalGeneratorGraphs_ground_injections {G S m inv one : ZFSet.{u}}
    (group : GroupCode G m inv one) (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) :
    M.externalOldInclusion G S m one ∈ M.sets ∧
      InjectionCode G (M.externalGroupCarrier G S m one) (M.externalOldInclusion G S m one) ∧
      M.externalChildGenerators G S m one ∈ M.sets ∧
      InjectionCode S (M.externalGroupCarrier G S m one) (M.externalChildGenerators G S m one) := by
  let := group.toGroup
  have maps := M.externalGeneratorGraphs_injections pairing unions powers separation infinite
    (SetMembers.presentation G) (SetMembers.presentation S) hG hS
  rw [group.multiplication_graph_eq, group.identity_code_eq] at maps
  have ground := M.externalGeneratorGraphs_mem pairing unions powers separation infinite hG hS hm
    (M.transitive hG group.identity_mem)
  exact ⟨ground.1, maps.1, ground.2, maps.2⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionStampBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem compressionStamp_ordinal {base : ZFSet.{u}} (ordinal : ordinalSetProperty base) (n : Nat) :
    ordinalSetProperty (compressionStamp base n) := by
  induction n with
  | zero => exact ordinalSetProperty_succ ordinal
  | succ n ih => exact ordinalSetProperty_succ ih

theorem compressionStamp_union_ordinal {base limit : ZFSet.{u}}
    (ordinal : ordinalSetProperty base) (union : NatUnionCode (compressionStamp base) limit) :
    ordinalSetProperty limit := by
  constructor
  · intro y hy z hz
    obtain ⟨n, yn⟩ := (union y).1 hy
    exact union.subset n ((compressionStamp_ordinal ordinal n).1 y yn z hz)
  · intro y hy
    obtain ⟨n, yn⟩ := (union y).1 hy
    exact (compressionStamp_ordinal ordinal n).2 y yn

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open scoped ZFSet
universe u

namespace FunctionGraphOn
variable {family : ZFSet.{u}}

theorem natValue_entry_iff (function : FunctionGraphOn ZFSet.omega family) (n : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode n) y ∈ family ↔ y = function.natValue n := by
  constructor
  · exact fun entry => function.unique entry (function.natValue_entry n)
  · exact fun equal => equal.symm ▸ function.natValue_entry n

end FunctionGraphOn

theorem naturalFamilyUnion_code {family : ZFSet.{u}}
    (function : FunctionGraphOn ZFSet.omega family) :
    NatUnionCode function.natValue (naturalFamilyUnion family) := by
  intro x
  rw [naturalFamilyUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨value, member, hx⟩
    obtain ⟨_, index, hi, entry⟩ := (mem_relationImage _ _ _ value).1 member
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode index).1 hi
    exact ⟨n, ((function.natValue_entry_iff n value).1 entry) ▸ hx⟩
  · rintro ⟨n, hx⟩
    have entry := function.natValue_entry n
    exact ⟨function.natValue n, (mem_relationImage _ _ _ _).2
      ⟨pair_second_mem_doubleUnion entry, natSetCode n, natSetCode_mem_omega n, entry⟩, hx⟩

namespace TransitiveGround
open SetFormula

theorem naturalFamilyUnion_mem (M : TransitiveGround.{u})
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets) {family : ZFSet.{u}} (hFamily : family ∈ M.sets) :
    naturalFamilyUnion family ∈ M.sets :=
  M.union_mem unions (M.relationImage_mem separation hω
    (M.union_mem unions (M.union_mem unions hFamily)) hFamily)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_naturalStep_zero {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {p y base : ZFSet.{u}} (hzero : natSetCode 0 ∈ M.sets)
    (hp : p ∈ M.sets) (hy : y ∈ M.sets) (hb : base ∈ M.sets) :
    Realize M.sets (naturalStepFormula φ)
      (extend (natSetCode 0) (extend p (extend y (extend base params)))) ↔ y = base := by
  rw [M.realize_naturalStepFormula φ params members hzero hp hy hb]
  constructor
  · rintro (⟨_, equal⟩ | ⟨m, _, x, _, equal, _⟩)
    · exact equal
    · have impossible : m ∈ natSetCode 0 := equal.symm ▸ ZFSet.mem_insert m m
      exact False.elim (ZFSet.notMem_empty m impossible)
  · intro equal
    exact Or.inl ⟨rfl, equal⟩

theorem realize_naturalStep_succ {k : Nat} (φ : SetFormula (k + 2))
    (params : Fin k → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    (n : Nat) {p y base : ZFSet.{u}} (hn : natSetCode n ∈ M.sets)
    (hnext : natSetCode (n + 1) ∈ M.sets)
    (hp : p ∈ M.sets) (hy : y ∈ M.sets) (hb : base ∈ M.sets) :
    Realize M.sets (naturalStepFormula φ)
      (extend (natSetCode (n + 1)) (extend p (extend y (extend base params)))) ↔
      ∃ x ∈ M.sets, ZFSet.pair (natSetCode n) x ∈ p ∧
        Realize M.sets φ (extend x (extend y params)) := by
  rw [M.realize_naturalStepFormula φ params members hnext hp hy hb]
  constructor
  · rintro (⟨empty, _⟩ | ⟨m, _, x, hx, equal, entry, next⟩)
    · exact False.elim (ZFSet.notMem_empty (natSetCode n)
        (empty ▸ ZFSet.mem_insert (natSetCode n) (natSetCode n)))
    · have same := (natSetCode_succ_eq_insert_iff n m).1 equal
      exact ⟨x, hx, same ▸ entry, next⟩
  · rintro ⟨x, hx, entry, next⟩
    exact Or.inr ⟨natSetCode n, hn, x, hx, rfl, entry, next⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})
variable {k : Nat} (φ : SetFormula (k + 2)) (params : Fin k → ZFSet.{u})
variable (members : ∀ i, params i ∈ M.sets)
variable (value : Nat → ZFSet.{u}) (values : ∀ n, value n ∈ M.sets)
variable (nextValue : ∀ n y, y ∈ M.sets →
  (Realize M.sets φ (extend (value n) (extend y params)) ↔ y = value (n + 1)))

include members values nextValue

theorem definableNaturalTrace_value {N t : ZFSet.{u}} (hN : N ∈ M.sets)
    (ordinal : ordinalSetProperty N)
    (trace : OrdinalRecursionTrace
      (groundRecursionStep M (naturalStepFormula φ) (extend (value 0) params)) N t) :
    ∀ n, natSetCode n ∈ N → ∀ y, ZFSet.pair (natSetCode n) y ∈ t → y = value n := by
  intro n
  induction n with
  | zero =>
    intro hn y entry
    obtain ⟨hp, hy, relation⟩ := trace.2 _ hn y entry
    exact (M.realize_naturalStep_zero φ params members (M.transitive hN hn)
      hp hy (values 0)).1 relation
  | succ n ih =>
    intro hn y entry
    have previous : natSetCode n ∈ natSetCode (n + 1) :=
      (natSetCode_mem_iff n (n + 1)).2 (Nat.lt_succ_self n)
    have hnN := ordinal.1 _ hn _ previous
    obtain ⟨hp, hy, relation⟩ := trace.2 _ hn y entry
    obtain ⟨x, _, oldEntry, next⟩ := (M.realize_naturalStep_succ φ params members n
      (M.transitive hN hnN) (M.transitive hN hn) hp hy (values 0)).1 relation
    have equal := ih hnN x (pair_mem_graphRestriction.1 oldEntry).1
    rw [equal] at next
    exact (nextValue n y hy).1 next

theorem definableNaturalStepClosure (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets) :
    GroundOrdinalStepClosure M ZFSet.omega (naturalStepFormula φ) (extend (value 0) params) := by
  intro a ha p hp trace
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode a).1 ha
  have hn (j : Nat) : natSetCode j ∈ M.sets := M.transitive hω (natSetCode_mem_omega j)
  cases n with
  | zero =>
    refine ⟨value 0, values 0,
      (M.realize_naturalStep_zero φ params members (hn 0) hp (values 0) (values 0)).2 rfl, ?_⟩
    intro y hy relation
    exact (M.realize_naturalStep_zero φ params members (hn 0) hp hy (values 0)).1 relation
  | succ n =>
    have previous : natSetCode n ∈ natSetCode (n + 1) :=
      (natSetCode_mem_iff n (n + 1)).2 (Nat.lt_succ_self n)
    have ordinal : ordinalSetProperty (natSetCode (n + 1) : ZFSet.{u}) := by
      rw [← ordinalCode_nat]
      exact ordinalSetProperty_ordinalCode _
    have entryValue := M.definableNaturalTrace_value φ params members value values nextValue
      (hn (n + 1)) ordinal trace
    obtain ⟨x, entry⟩ := trace.1.total previous
    have equal := entryValue n previous x entry
    have canonical : ZFSet.pair (natSetCode n) (value n) ∈ p := equal ▸ entry
    refine ⟨value (n + 1), values (n + 1), ?_, ?_⟩
    · exact (M.realize_naturalStep_succ φ params members n (hn n) (hn (n + 1))
        hp (values (n + 1)) (values 0)).2
          ⟨value n, values n, canonical, (nextValue n _ (values (n + 1))).2 rfl⟩
    · intro y hy relation
      obtain ⟨x, _, oldEntry, next⟩ := (M.realize_naturalStep_succ φ params members n
        (hn n) (hn (n + 1)) hp hy (values 0)).1 relation
      have same := entryValue n previous x oldEntry
      rw [same] at next
      exact (nextValue n y hy).1 next

theorem exists_definableNaturalHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace
        (groundRecursionStep M (naturalStepFormula φ) (extend (value 0) params))
        ZFSet.omega history ∧
      (∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = value n) ∧
      (∀ other, OrdinalRecursionTrace
        (groundRecursionStep M (naturalStepFormula φ) (extend (value 0) params))
        ZFSet.omega other → other = history) := by
  have hω := M.omega_mem separation infinite
  have ordinal : ordinalSetProperty (ZFSet.omega : ZFSet.{u}) := by
    rw [← ordinalCode_omega]
    exact ordinalSetProperty_ordinalCode Ordinal.omega0
  obtain ⟨history, hh, trace, unique, _⟩ := M.exists_unique_ordinalRecursionTrace pairing unions
    separation collection hω ordinal (naturalStepFormula φ) (extend (value 0) params)
    (Fin.cases (values 0) members)
    (M.definableNaturalStepClosure φ params members value values nextValue hω)
  refine ⟨history, hh, trace, ?_, unique⟩
  intro n y
  have hn := natSetCode_mem_omega n
  have entryValue := M.definableNaturalTrace_value φ params members value values nextValue
    hω ordinal trace
  constructor
  · exact entryValue n hn y
  · intro equal
    obtain ⟨z, entry⟩ := trace.1.total hn
    exact equal.symm ▸ (entryValue n hn z entry ▸ entry)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem compressionStamp_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {base : ZFSet.{u}} (hBase : base ∈ M.sets) (n : Nat) :
    compressionStamp base n ∈ M.sets := by
  induction n with
  | zero => exact M.insert_mem pairing unions hBase hBase
  | succ n ih => exact M.insert_mem pairing unions ih ih

theorem exists_groundCompressionStamps
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {base : ZFSet.{u}} (hBase : base ∈ M.sets) (ordinal : ordinalSetProperty base) :
    ∃ stamps ∈ M.sets, ∃ limit ∈ M.sets,
      limit = naturalFamilyUnion stamps ∧ CompressionStampCode base stamps limit := by
  let formula : SetFormula 2 := (BoundedFormula.successorFormula 1 0).toFormula
  have values : ∀ n, compressionStamp base n ∈ M.sets := M.compressionStamp_mem pairing unions hBase
  have nextValue : ∀ n y, y ∈ M.sets →
      (Realize M.sets formula (extend (compressionStamp base n) (extend y Fin.elim0)) ↔
        y = compressionStamp base (n + 1)) := by
    intro n y hy
    exact (BoundedFormula.realize_toFormula M (BoundedFormula.successorFormula 1 0)
      (extend (compressionStamp base n) (extend y Fin.elim0))
      (Fin.cases (values n) (Fin.cases hy (fun i => Fin.elim0 i)))).trans
        (BoundedFormula.truth_successorFormula 1 0 _)
  obtain ⟨stamps, hStamps, trace, entries, _⟩ :=
    M.exists_definableNaturalHistory formula Fin.elim0 (fun i => Fin.elim0 i)
      (compressionStamp base) values nextValue pairing unions separation collection infinite
  have valueEq (n : Nat) : trace.1.natValue n = compressionStamp base n :=
    (entries n _).1 (trace.1.natValue_entry n)
  have unionCode : NatUnionCode (compressionStamp base) (naturalFamilyUnion stamps) := by
    intro x
    simpa only [valueEq] using (naturalFamilyUnion_code trace.1 x)
  have stampBelow (n : Nat) : compressionStamp base n ∈ naturalFamilyUnion stamps :=
    unionCode.subset (n + 1) (ZFSet.mem_insert _ _)
  refine ⟨stamps, hStamps, naturalFamilyUnion stamps,
    M.naturalFamilyUnion_mem unions separation (M.omega_mem separation infinite) hStamps, rfl,
    ⟨⟨?_, ?_⟩, entries, unionCode, compressionStamp_union_ordinal ordinal unionCode⟩⟩
  · intro z hz
    obtain ⟨i, hi, y, rfl⟩ := trace.1.shape z hz
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode i).1 hi
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, (entries n y).1 hz ▸ stampBelow n⟩
  · obtain ⟨_, function⟩ := trace.1
    exact function.2

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundActionFilterImages
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

theorem truth_actionImageFormula {n} (y A g F : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (actionImageFormula y A g F) env ↔
      ∃ x ∈ env F, ZFSet.pair (ZFSet.pair (env g) x) (env y) ∈ env A := by
  simp only [actionImageFormula, truth_exMem, truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem actionImage_mem (separation : SeparationSchema M.sets)
    {P A g F : ZFSet.{u}} (hP : P ∈ M.sets) (hA : A ∈ M.sets)
    (hg : g ∈ M.sets) (hF : F ∈ M.sets) : actionImage P A g F ∈ M.sets := by
  let params := extend A (extend g (extend F Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.actionImageFormula 0 1 2 3) params
    (Fin.cases hA (Fin.cases hg (Fin.cases hF (fun i => Fin.elim0 i)))) hP
  have equal : ZFSet.sep (fun y => BoundedFormula.Truth
      (BoundedFormula.actionImageFormula 0 1 2 3) (extend y params)) P =
      actionImage P A g F := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, mem_actionImage, BoundedFormula.truth_actionImageFormula]
    rfl
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskRepresentativeCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace BoundedFormula

open SetFormula
universe u

theorem truth_meetFilterFormula {n} (P r μ F : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (meetFilterFormula P r μ F) env ↔
      MeetFilterCode (env P) (env r) (env μ) (env F) := by
  simp only [meetFilterFormula, Truth, truth_exMem, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨subset, ⟨x, hx, _⟩, upward, closed⟩
    exact ⟨subset, ⟨x, hx⟩, upward, fun x hx y hy z entry =>
      closed x hx y hy z (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2 entry⟩
  · intro filter
    obtain ⟨x, hx⟩ := filter.nonempty
    exact ⟨filter.subset, ⟨x, hx, trivial⟩, filter.upward,
      fun x hx y hy z _ entry => filter.closed_meet x hx y hy z entry⟩

theorem truth_restrictedActionFormula {n} (P r A g source target base : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (restrictedActionFormula P r A g source target base) env ↔
      RestrictedActionCode (env P) (env r) (env A) (env g) (env source) (env target) (env base) := by
  simp only [restrictedActionFormula, Truth, truth_relationBetweenFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_imp, ← iff_def]
  exact ⟨fun ⟨shape, target, entries⟩ => ⟨shape, target, entries⟩,
    fun code => ⟨code.shape, code.target_entry, code.entries⟩⟩

end BoundedFormula

universe u

namespace BoundedFormula

open SetFormula

theorem truth_eligibleTaskFormula {n} (P G r μ A source target base separator F : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (eligibleTaskFormula P G r μ A source target base separator F) env ↔
      EligibleTaskCode (env P) (env G) (env r) (env μ) (env A)
        (env source) (env target) (env base) (env separator) (env F) := by
  simp only [eligibleTaskFormula, Truth, truth_pairMembershipFormula, truth_exMem,
    truth_restrictedActionFormula, truth_meetFilterFormula P r μ F env meet]
  constructor
  · rintro ⟨hs, ht, he, filter, lower, strict, upper, representative⟩
    exact ⟨hs, ht, he, filter, lower, strict, upper, representative⟩
  · intro code
    exact ⟨code.source_mem, code.target_mem, code.separator_mem, code.filter,
      code.lower, code.strict, code.upper, code.representative⟩

end BoundedFormula

theorem literalTaskCode_mem_eligibleTaskSet (P G r μ A R U Labels a c base e F label : ZFSet.{u}) :
    literalTaskCode a c base e F label ∈ eligibleTaskSet P G r μ A R U Labels ↔
      a ∈ P ∧ c ∈ P ∧ base ∈ R ∧ e ∈ P ∧ F ∈ U ∧ label ∈ Labels ∧
        EligibleTaskCode P G r μ A a c base e F := by
  rw [mem_eligibleTaskSet]
  constructor
  · rintro ⟨a', ha, c', hc, base', hBase, e', he, F', hF, label', hLabel, equal, code⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := literalTaskCode_inj.1 equal
    exact ⟨ha, hc, hBase, he, hF, hLabel, code⟩
  · rintro ⟨ha, hc, hBase, he, hF, hLabel, code⟩
    exact ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, rfl, code⟩

namespace BoundedFormula

open SetFormula

theorem truth_eligibleTaskEntryFormula {n} (z P G r μ A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Truth (eligibleTaskEntryFormula z P G r μ A R U Labels) env ↔
      env z ∈ eligibleTaskSet (env P) (env G) (env r) (env μ) (env A) (env R) (env U) (env Labels) := by
  rw [mem_eligibleTaskSet]
  simp only [eligibleTaskEntryFormula, truth_exMem, Truth, truth_literalTaskFormula]
  refine exists_congr fun a => and_congr_right fun _ =>
    exists_congr fun c => and_congr_right fun _ =>
    exists_congr fun base => and_congr_right fun _ =>
    exists_congr fun e => and_congr_right fun _ =>
    exists_congr fun F => and_congr_right fun _ =>
    exists_congr fun label => and_congr_right fun _ => ?_
  exact and_congr Iff.rfl (truth_eligibleTaskFormula _ _ _ _ _ _ _ _ _ _
    (extend label (extend F (extend e (extend base (extend c (extend a env)))))) meet)

end BoundedFormula

theorem TaskRepresentative.restriction {P r A R U Labels g a c base e F label : ZFSet.{u}}
    (represented : TaskRepresentative P r A R U Labels (literalTaskCode a c base e F label) g) :
    RestrictedActionCode P r A g a c base := by
  obtain ⟨a', _, c', _, base', _, e', _, F', _, label', _, equal, code⟩ := represented
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := literalTaskCode_inj.1 equal
  exact code

theorem pair_mem_taskRepresentativeRelation (I P G r A R U Labels task g : ZFSet.{u}) :
    ZFSet.pair task g ∈ taskRepresentativeRelation I P G r A R U Labels ↔
      task ∈ I ∧ g ∈ G ∧ TaskRepresentative P r A R U Labels task g := by
  constructor
  · intro h
    obtain ⟨_, t, ht, h, hh, equal, represents⟩ := ZFSet.mem_sep.1 h
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ht, hh, represents⟩
  · rintro ⟨ht, hg, represents⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨ht, hg⟩, task, ht, g, hg, rfl, represents⟩

theorem eligibleTask_representative_total (P G r μ A R U Labels : ZFSet.{u}) :
    ∀ task ∈ eligibleTaskSet P G r μ A R U Labels, ∃ g ∈ G,
      ZFSet.pair task g ∈ taskRepresentativeRelation
        (eligibleTaskSet P G r μ A R U Labels) P G r A R U Labels := by
  intro task ht
  obtain ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, equal, code⟩ :=
    (mem_eligibleTaskSet P G r μ A R U Labels task).1 ht
  obtain ⟨g, hg, represents⟩ := code.representative
  exact ⟨g, hg, (pair_mem_taskRepresentativeRelation _ _ _ _ _ _ _ _ _ _).2
    ⟨ht, hg, a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, equal, represents⟩⟩

namespace BoundedFormula

open SetFormula

theorem truth_taskRepresentativeFormula {n} (task g P r A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskRepresentativeFormula task g P r A R U Labels) env ↔
      TaskRepresentative (env P) (env r) (env A) (env R) (env U) (env Labels) (env task) (env g) := by
  simp only [taskRepresentativeFormula, truth_exMem, Truth, truth_literalTaskFormula,
    truth_restrictedActionFormula, TaskRepresentative]
  rfl

theorem truth_taskRepresentativeEntryFormula {n} (z I P G r A R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskRepresentativeEntryFormula z I P G r A R U Labels) env ↔
      ∃ task ∈ env I, ∃ g ∈ env G, env z = ZFSet.pair task g ∧
        TaskRepresentative (env P) (env r) (env A) (env R) (env U) (env Labels) task g := by
  simp only [taskRepresentativeEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_taskRepresentativeFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundActionPostcomposition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_actionPostcomposeEntryFormula {n} (v P A g base : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionPostcomposeEntryFormula v P A g base) env ↔
      ∃ x ∈ env P, ∃ z ∈ env P, env v = ZFSet.pair x z ∧
        ∃ y ∈ env P, ZFSet.pair x y ∈ env base ∧
          ZFSet.pair (ZFSet.pair (env g) y) z ∈ env A := by
  simp only [actionPostcomposeEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

theorem truth_actionPostcomposeFormula {n} (P A g base output : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionPostcomposeFormula P A g base output) env ↔
      env output = actionPostcompose (env P) (env A) (env g) (env base) := by
  simp only [actionPostcomposeFormula, Truth, truth_relationBetweenFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, truth_imp, truth_exMem, ← iff_def]
  constructor
  · rintro ⟨shape, entries⟩
    apply ZFSet.ext
    intro v
    constructor
    · intro hv
      obtain ⟨x, hx, z, hz, rfl⟩ := ZFSet.mem_prod.1 (shape hv)
      exact (pair_mem_actionPostcompose _ _ _ _ x z).2 ⟨hx, hz, (entries x hx z hz).1 hv⟩
    · intro hv
      obtain ⟨x, hx, z, hz, rfl⟩ := ZFSet.mem_prod.1 (actionPostcompose_subset _ _ _ _ hv)
      exact (entries x hx z hz).2 ((pair_mem_actionPostcompose _ _ _ _ x z).1 hv).2.2
  · intro equal
    refine ⟨equal ▸ actionPostcompose_subset _ _ _ _, ?_⟩
    intro x hx z hz
    change ZFSet.pair x z ∈ env output ↔ ∃ y ∈ env P,
      ZFSet.pair x y ∈ env base ∧ ZFSet.pair (ZFSet.pair (env g) y) z ∈ env A
    rw [equal, pair_mem_actionPostcompose]
    exact ⟨fun h => h.2.2, fun h => ⟨hx, hz, h⟩⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem actionPostcompose_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P A g base : ZFSet.{u}} (hP : P ∈ M.sets) (hA : A ∈ M.sets)
    (hg : g ∈ M.sets) (hbase : base ∈ M.sets) : actionPostcompose P A g base ∈ M.sets := by
  let params := extend P (extend A (extend g (extend base Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.actionPostcomposeEntryFormula 0 1 2 3 4) params
    (Fin.cases hP (Fin.cases hA (Fin.cases hg (Fin.cases hbase (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hP hP)
  have equal : ZFSet.sep (fun v => BoundedFormula.Truth
      (BoundedFormula.actionPostcomposeEntryFormula 0 1 2 3 4) (extend v params))
      (ZFSet.prod P P) = actionPostcompose P A g base := by
    apply ZFSet.ext
    intro v
    rw [ZFSet.mem_sep, actionPostcompose, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_actionPostcomposeEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_TaskTransportCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem EligibleTaskCode.transport {P G r μ A a c base s F m inv e δ c' s' : ZFSet.{u}}
    (code : EligibleTaskCode P G r μ A a c base s F)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hδ : δ ∈ G)
    (target : ZFSet.pair (ZFSet.pair δ c) c' ∈ A)
    (separator : ZFSet.pair (ZFSet.pair δ s) s' ∈ A) :
    EligibleTaskCode P G r μ A a c' (actionPostcompose P A δ base) s' (actionImage P A δ F) := by
  refine ⟨code.source_mem, (ZFSet.pair_mem_prod.1 (action.function.1 target)).2,
    (ZFSet.pair_mem_prod.1 (action.function.1 separator)).2,
    actionImage_filter group action meet hδ code.filter,
    (action.raw_order_iff group meet.order hδ target separator).2 code.lower,
    fun h => code.strict ((action.raw_order_iff group meet.order hδ separator target).1 h),
    actionImage_lower_bound action code.filter.subset hδ code.separator_mem separator code.upper, ?_⟩
  obtain ⟨g, hg, represented⟩ := code.representative
  obtain ⟨k, product, _⟩ := group.mul_function.2 (ZFSet.pair δ g) (ZFSet.pair_mem_prod.2 ⟨hδ, hg⟩)
  have hk := (ZFSet.pair_mem_prod.1 (group.mul_function.1 product)).2
  exact ⟨k, hk, represented.transport action hg hδ hk product target⟩

theorem TaskTransportCode.unique {G P m e r A R U Labels g t t' t'' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hg : g ∈ G)
    (first : TaskTransportCode P R U Labels A g t t')
    (second : TaskTransportCode P R U Labels A g t t'') : t' = t'' := by
  obtain ⟨a, _, c, hc, base, _, s, hs, F, _, label, _, c', _, base', _, s', _, F', _,
    old, new, target, separator, baseEq, filterEq⟩ := first
  obtain ⟨b, _, d, _, ell, _, v, _, J, _, tag, _, d', _, ell', _, v', _, J', _,
    old', new', target', separator', baseEq', filterEq'⟩ := second
  obtain ⟨ha, hd, hell, hv, hJ, htag⟩ := literalTaskCode_inj.1 (old.symm.trans old')
  subst b d ell v J tag
  obtain ⟨w, _, uniqueC⟩ := action.function.2 (ZFSet.pair g c) (ZFSet.pair_mem_prod.2 ⟨hg, hc⟩)
  obtain ⟨v, _, uniqueS⟩ := action.function.2 (ZFSet.pair g s) (ZFSet.pair_mem_prod.2 ⟨hg, hs⟩)
  have hc' := (uniqueC c' target).trans (uniqueC d' target').symm
  have hs' := (uniqueS s' separator).trans (uniqueS v' separator').symm
  rw [new, new', hc', hs', baseEq, baseEq', filterEq, filterEq']

theorem TaskTransportCode.one {G P m e r A R U Labels t : ZFSet.{u}}
    (action : PosetActionCode G P m e r A)
    (shape : ∀ base ∈ R, base ⊆ ZFSet.prod P P) (subsets : ∀ F ∈ U, F ⊆ P)
    (ht : t ∈ literalTaskBound P R U Labels) : TaskTransportCode P R U Labels A e t t := by
  obtain ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel, rfl⟩ :=
    (mem_literalTaskBound P R U Labels t).1 ht
  exact ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel,
    c, hc, base, hbase, s, hs, F, hF, rfl, rfl, action.one c hc, action.one s hs,
    (actionPostcompose_one action (shape base hbase)).symm,
    (actionImage_one action (subsets F hF)).symm⟩

theorem TaskTransportCode.mul {G P m e r A R U Labels g h k t t' t'' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subsets : ∀ F ∈ U, F ⊆ P)
    (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m)
    (first : TaskTransportCode P R U Labels A h t t')
    (second : TaskTransportCode P R U Labels A g t' t'') :
    TaskTransportCode P R U Labels A k t t'' := by
  obtain ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel,
    c', hc', base', _, s', hs', F', _, old, middle, target, separator, baseEq, filterEq⟩ := first
  obtain ⟨b, _, d, _, ell, _, v, _, J, _, tag, _,
    d', hd', ell', hell', v', hv', J', hJ', middle', new, target', separator', baseEq', filterEq'⟩ := second
  obtain ⟨ha', hd, hell, hv, hJ, htag⟩ := literalTaskCode_inj.1 (middle.symm.trans middle')
  subst b d ell v J tag
  refine ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel,
    d', hd', ell', hell', v', hv', J', hJ', old, new,
    action.mul g hg h hh k hk c hc c' hc' d' hd' product target target',
    action.mul g hg h hh k hk s hs s' hs' v' hv' product separator separator', ?_, ?_⟩
  · rw [baseEq', baseEq, actionPostcompose_mul action hg hh hk product]
  · rw [filterEq', filterEq, actionImage_mul action (subsets F hF) hg hh hk product]

theorem taskTransportGraph_subset (G I P R U Labels A : ZFSet.{u}) :
    taskTransportGraph G I P R U Labels A ⊆ ZFSet.prod (ZFSet.prod G I) I :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem triple_mem_taskTransportGraph (G I P R U Labels A g t t' : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g t) t' ∈ taskTransportGraph G I P R U Labels A ↔
      g ∈ G ∧ t ∈ I ∧ t' ∈ I ∧ TaskTransportCode P R U Labels A g t t' := by
  rw [taskTransportGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, g', hg, s, hs, s', hs', equal, transported⟩
    obtain ⟨pairEq, last⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨first, middle⟩ := ZFSet.pair_inj.1 pairEq
    subst g' s s'
    exact ⟨hg, hs, hs', transported⟩
  · rintro ⟨hg, ht, ht', transported⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, ht⟩, ht'⟩,
      g, hg, t, ht, t', ht', rfl, transported⟩

theorem taskTransportGraph_function {G I P R U Labels A m e r : ZFSet.{u}}
    (action : PosetActionCode G P m e r A)
    (total : ∀ g ∈ G, ∀ t ∈ I, ∃ t' ∈ I, TaskTransportCode P R U Labels A g t t') :
    ZFSet.IsFunc (ZFSet.prod G I) I (taskTransportGraph G I P R U Labels A) := by
  refine ⟨taskTransportGraph_subset G I P R U Labels A, ?_⟩
  intro v hv
  obtain ⟨g, hg, t, ht, rfl⟩ := ZFSet.mem_prod.1 hv
  obtain ⟨t', ht', transported⟩ := total g hg t ht
  refine ⟨t', (triple_mem_taskTransportGraph G I P R U Labels A g t t').2
    ⟨hg, ht, ht', transported⟩, ?_⟩
  intro t'' entry
  have parts := (triple_mem_taskTransportGraph G I P R U Labels A g t t'').1 entry
  exact TaskTransportCode.unique action hg parts.2.2.2 transported

theorem taskTransportGraph_one {G I P R U Labels A m e r : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (he : e ∈ G)
    (shape : ∀ base ∈ R, base ⊆ ZFSet.prod P P) (subsets : ∀ F ∈ U, F ⊆ P)
    (bound : I ⊆ literalTaskBound P R U Labels) :
    ∀ t ∈ I, ZFSet.pair (ZFSet.pair e t) t ∈ taskTransportGraph G I P R U Labels A := by
  intro t ht
  exact (triple_mem_taskTransportGraph G I P R U Labels A e t t).2
    ⟨he, ht, ht, TaskTransportCode.one action shape subsets (bound ht)⟩

theorem taskTransportGraph_mul {G I P R U Labels A m e r : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (subsets : ∀ F ∈ U, F ⊆ P)
    {g h k t t' t'' : ZFSet.{u}} (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m)
    (first : ZFSet.pair (ZFSet.pair h t) t' ∈ taskTransportGraph G I P R U Labels A)
    (second : ZFSet.pair (ZFSet.pair g t') t'' ∈ taskTransportGraph G I P R U Labels A) :
    ZFSet.pair (ZFSet.pair k t) t'' ∈ taskTransportGraph G I P R U Labels A := by
  have parts := (triple_mem_taskTransportGraph G I P R U Labels A h t t').1 first
  have parts' := (triple_mem_taskTransportGraph G I P R U Labels A g t' t'').1 second
  exact (triple_mem_taskTransportGraph G I P R U Labels A k t t'').2
    ⟨hk, parts.2.1, parts'.2.2.1,
      TaskTransportCode.mul action subsets hg hh hk product parts.2.2.2 parts'.2.2.2⟩

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskTransportFormulas
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

theorem truth_actionImageEqualityFormula {n} (P A g F output : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionImageEqualityFormula P A g F output) env ↔
      env output = actionImage (env P) (env A) (env g) (env F) := by
  simp only [actionImageEqualityFormula, Truth, truth_imp, truth_actionImageFormula, ← iff_def]
  constructor
  · rintro ⟨subset, entries⟩
    apply ZFSet.ext
    intro y
    rw [mem_actionImage]
    exact ⟨fun hy => ⟨subset y hy, (entries y (subset y hy)).1 hy⟩,
      fun hy => (entries y hy.1).2 hy.2⟩
  · intro equal
    refine ⟨?_, ?_⟩
    · intro y hy
      exact actionImage_subset _ _ _ _ (equal ▸ hy)
    · intro y hy
      change y ∈ env output ↔ ∃ x ∈ env F, ZFSet.pair (ZFSet.pair (env g) x) y ∈ env A
      rw [equal, mem_actionImage]
      exact ⟨And.right, fun h => ⟨hy, h⟩⟩

theorem truth_taskTransportFormula {n} (P R U Labels A g t t' : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskTransportFormula P R U Labels A g t t') env ↔
      TaskTransportCode (env P) (env R) (env U) (env Labels) (env A) (env g) (env t) (env t') := by
  simp only [taskTransportFormula, truth_exMem, Truth, truth_literalTaskFormula,
    truth_tripleMembershipFormula, truth_actionPostcomposeFormula, truth_actionImageEqualityFormula]
  rfl

theorem truth_taskTransportEntryFormula {n} (z G I P R U Labels A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taskTransportEntryFormula z G I P R U Labels A) env ↔
      ∃ g ∈ env G, ∃ t ∈ env I, ∃ t' ∈ env I,
        env z = ZFSet.pair (ZFSet.pair g t) t' ∧
          TaskTransportCode (env P) (env R) (env U) (env Labels) (env A) g t t' := by
  simp only [taskTransportEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_taskTransportFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_CodedRecursiveTaskActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

theorem CodedAttachmentCovariance.monotone
    {G P N m e r A B inside shadow upper : ZFSet.{u}}
    (covariance : CodedAttachmentCovariance G P N A B inside shadow upper)
    (old : PosetActionCode G P m e r A) (fresh : SetActionCode G N m e B) :
    ∀ g ∈ G, ∀ p ∈ taggedExtension P N, ∀ q ∈ taggedExtension P N,
      ∀ p' ∈ taggedExtension P N, ∀ q' ∈ taggedExtension P N,
        ZFSet.pair (ZFSet.pair g p) p' ∈ taggedActionGraph G P N A B →
        ZFSet.pair (ZFSet.pair g q) q' ∈ taggedActionGraph G P N A B →
        ZFSet.pair p q ∈ codedAttachmentOrder P N r inside shadow upper →
        ZFSet.pair p' q' ∈ codedAttachmentOrder P N r inside shadow upper := by
  intro g hg p _ q _ p' hp' q' hq' first second lower
  have compared := ((pair_mem_codedAttachmentOrder P N r inside shadow upper p q).1 lower).2.2
  apply (pair_mem_codedAttachmentOrder P N r inside shadow upper p' q').2
  refine ⟨hp', hq', ?_⟩
  rcases compared with oldOld | oldFresh | freshOld | freshFresh
  · obtain ⟨hp, hq, below⟩ := oldOld
    have actedP := (taggedActionGraph_old_iff hp).1 first
    have actedQ := (taggedActionGraph_old_iff hq).1 second
    have hp'P := (old.toSetAction.entry_shape actedP).2.2
    have hq'P := (old.toSetAction.entry_shape actedQ).2.2
    exact Or.inl ⟨hp'P, hq'P, old.monotone g hg p hp q hq p' hp'P q' hq'P actedP actedQ below⟩
  · obtain ⟨hp, t, ht, s, hs, rfl, shadowEntry, below⟩ := oldFresh
    have actedP := (taggedActionGraph_old_iff hp).1 first
    have hp'P := (old.toSetAction.entry_shape actedP).2.2
    obtain ⟨t', ht', rfl, actedT⟩ := (taggedActionGraph_fresh_iff old.toSetAction fresh).1 second
    obtain ⟨s', actedS, _⟩ := old.function.2 (ZFSet.pair g s) (ZFSet.pair_mem_prod.2 ⟨hg, hs⟩)
    have hs' := (old.toSetAction.entry_shape actedS).2.2
    exact Or.inr (Or.inl ⟨hp'P, t', ht', s', hs', rfl,
      covariance.shadow g hg t ht t' ht' s hs s' hs' actedT actedS shadowEntry,
      old.monotone g hg p hp s hs p' hp'P s' hs' actedP actedS below⟩)
  · obtain ⟨hq, t, ht, rfl, upperEntry⟩ := freshOld
    obtain ⟨t', ht', rfl, actedT⟩ := (taggedActionGraph_fresh_iff old.toSetAction fresh).1 first
    have actedQ := (taggedActionGraph_old_iff hq).1 second
    have hq'P := (old.toSetAction.entry_shape actedQ).2.2
    exact Or.inr (Or.inr (Or.inl ⟨hq'P, t', ht', rfl,
      covariance.upper g hg t ht t' ht' q hq q' hq'P actedT actedQ upperEntry⟩))
  · obtain ⟨s, hs, t, ht, rfl, rfl, below⟩ := freshFresh
    obtain ⟨s', hs', rfl, actedS⟩ := (taggedActionGraph_fresh_iff old.toSetAction fresh).1 first
    obtain ⟨t', ht', rfl, actedT⟩ := (taggedActionGraph_fresh_iff old.toSetAction fresh).1 second
    refine Or.inr (Or.inr (Or.inr ⟨s', hs', t', ht', rfl, rfl, ?_⟩))
    rcases below with internal | ⟨v, hv, shadowEntry, upperEntry⟩
    · exact Or.inl (covariance.inside g hg s hs t ht s' hs' t' ht' actedS actedT internal)
    · obtain ⟨v', actedV, _⟩ := old.function.2 (ZFSet.pair g v) (ZFSet.pair_mem_prod.2 ⟨hg, hv⟩)
      have hv' := (old.toSetAction.entry_shape actedV).2.2
      exact Or.inr ⟨v', hv',
        covariance.shadow g hg t ht t' ht' v hv v' hv' actedT actedV shadowEntry,
        covariance.upper g hg s hs s' hs' v hv v' hv' actedS actedV upperEntry⟩

theorem PosetActionCode.tagged_attachment
    {G P N m e r A B inside shadow upper : ZFSet.{u}}
    (old : PosetActionCode G P m e r A) (fresh : SetActionCode G N m e B)
    (covariance : CodedAttachmentCovariance G P N A B inside shadow upper) :
    PosetActionCode G (taggedExtension P N) m e
      (codedAttachmentOrder P N r inside shadow upper) (taggedActionGraph G P N A B) :=
  ⟨(old.toSetAction.tagged fresh).function, (old.toSetAction.tagged fresh).one,
    (old.toSetAction.tagged fresh).mul, covariance.monotone old fresh⟩

end

open Compression.RecursiveMaps
universe u

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundTestedMeetFilters
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem mem_groundMeetFilters (P r μ F : ZFSet.{u}) :
    F ∈ M.groundMeetFilters P r μ ↔ F ∈ M.sets ∧ MeetFilterCode P r μ F := by
  rw [groundMeetFilters, ZFSet.mem_sep, M.mem_groundPower]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.subset⟩, h.2⟩⟩

theorem groundMeetFilters_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets)
    {P r μ : ZFSet.{u}} (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundMeetFilters P r μ ∈ M.sets := by
  let params := extend P (extend r (extend μ Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.meetFilterFormula 1 2 3 0) params
    (Fin.cases hP (Fin.cases hr (Fin.cases hμ (fun i => Fin.elim0 i))))
    (M.groundPower_mem powers hP)
  have equal : ZFSet.sep (fun F => BoundedFormula.Truth
      (BoundedFormula.meetFilterFormula 1 2 3 0) (extend F params)) (M.groundPower P) =
      M.groundMeetFilters P r μ := by
    apply ZFSet.ext
    intro F
    rw [ZFSet.mem_sep, groundMeetFilters, ZFSet.mem_sep]
    exact and_congr_right (fun _ =>
      BoundedFormula.truth_meetFilterFormula 1 2 3 0 (extend F params) meet)
  exact equal ▸ selected

end TransitiveGround

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_EligibleTaskCovariance
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem literalTask_fresh_iff {I P R U Labels r a c base s F label q : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hb : base ∈ R) (hs : s ∈ P)
    (hF : F ∈ U) (hl : label ∈ Labels) :
    ZFSet.pair (literalTaskCode a c base s F label) q ∈
      indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
        (literalTaskSourceGraph I P R U Labels) ↔
      literalTaskCode a c base s F label ∈ I ∧ q ∈ P ∧ ZFSet.pair q a ∉ r := by
  rw [pair_mem_indexedAttachmentFresh]
  constructor
  · rintro ⟨hi, Q, r', a', eQ, er, ea, hq, fresh⟩
    obtain rfl := ((pair_mem_constantFamilyGraph I P _ Q).1 eQ).2
    obtain rfl := ((pair_mem_constantFamilyGraph I r _ r').1 er).2
    obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 ea).2
    exact ⟨hi, hq, fresh⟩
  · rintro ⟨hi, hq, fresh⟩
    exact ⟨hi, P, r, a, (pair_mem_constantFamilyGraph I P _ P).2 ⟨hi, rfl⟩,
      (pair_mem_constantFamilyGraph I r _ r).2 ⟨hi, rfl⟩,
      (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).2 ⟨hi, rfl⟩, hq, fresh⟩

theorem literalTask_shadow_iff {I P R U Labels μ a c base s F label q x : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hb : base ∈ R) (hs : s ∈ P)
    (hF : F ∈ U) (hl : label ∈ Labels) :
    ZFSet.pair (ZFSet.pair (literalTaskCode a c base s F label) q) x ∈
      batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) ↔
      literalTaskCode a c base s F label ∈ I ∧
        ZFSet.pair q x ∈ attachmentShadowGraph P P μ base a := by
  rw [pair_mem_batchAttachmentShadowGraph]
  constructor
  · rintro ⟨hi, Q, μ', a', base', eQ, eμ, ea, eb, entry⟩
    obtain rfl := ((pair_mem_constantFamilyGraph I P _ Q).1 eQ).2
    obtain rfl := ((pair_mem_constantFamilyGraph I μ _ μ').1 eμ).2
    obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 ea).2
    obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).1 eb).2
    exact ⟨hi, entry⟩
  · rintro ⟨hi, entry⟩
    exact ⟨hi, P, μ, a, base,
      (pair_mem_constantFamilyGraph I P _ P).2 ⟨hi, rfl⟩,
      (pair_mem_constantFamilyGraph I μ _ μ).2 ⟨hi, rfl⟩,
      (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).2 ⟨hi, rfl⟩,
      (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).2 ⟨hi, rfl⟩, entry⟩

theorem literalTask_upper_iff {I P R U Labels a c base s F label q x : ZFSet.{u}}
    (ha : a ∈ P) (hc : c ∈ P) (hb : base ∈ R) (hs : s ∈ P)
    (hF : F ∈ U) (hl : label ∈ Labels) :
    ZFSet.pair (ZFSet.pair (literalTaskCode a c base s F label) q) x ∈
      batchAttachmentUpperGraph I P (constantFamilyGraph I P)
        (literalTaskFilterGraph I P R U Labels) ↔
      literalTaskCode a c base s F label ∈ I ∧ q ∈ P ∧ x ∈ P ∧ x ∈ F := by
  rw [pair_mem_batchAttachmentUpperGraph]
  constructor
  · rintro ⟨hi, hx, Q, F', eQ, eF, hq, upper⟩
    obtain rfl := ((pair_mem_constantFamilyGraph I P _ Q).1 eQ).2
    obtain rfl := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 4).1 eF).2
    exact ⟨hi, hq, hx, upper⟩
  · rintro ⟨hi, hq, hx, upper⟩
    exact ⟨hi, hx, P, F, (pair_mem_constantFamilyGraph I P _ P).2 ⟨hi, rfl⟩,
      (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 4).2 ⟨hi, rfl⟩, hq, upper⟩

theorem constantTask_inside_iff (I P r t q s v : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair t q) (ZFSet.pair s v) ∈
      batchAttachmentInsideGraph I (constantFamilyGraph I P) (constantFamilyGraph I r) ↔
      t = s ∧ t ∈ I ∧ q ∈ P ∧ v ∈ P ∧ ZFSet.pair q v ∈ r := by
  rw [pair_mem_batchAttachmentInsideGraph]
  constructor
  · rintro ⟨equal, ht, Q, r', eQ, er, hq, hv, lower⟩
    obtain rfl := ((pair_mem_constantFamilyGraph I P t Q).1 eQ).2
    obtain rfl := ((pair_mem_constantFamilyGraph I r t r').1 er).2
    exact ⟨equal, ht, hq, hv, lower⟩
  · rintro ⟨equal, ht, hq, hv, lower⟩
    exact ⟨equal, ht, P, r, (pair_mem_constantFamilyGraph I P t P).2 ⟨ht, rfl⟩,
      (pair_mem_constantFamilyGraph I r t r).2 ⟨ht, rfl⟩, hq, hv, lower⟩

namespace TaskTransportCode

variable {I P R U Labels A g t t' : ZFSet.{u}}
variable (transport : TaskTransportCode P R U Labels A g t t')
include transport

theorem source_eq {a a' : ZFSet.{u}}
    (first : ZFSet.pair t a ∈ literalTaskSourceGraph I P R U Labels)
    (second : ZFSet.pair t' a' ∈ literalTaskSourceGraph I P R U Labels) : a = a' := by
  obtain ⟨b, hb, c, hc, base, hbase, s, hs, F, hF, label, hl,
    c', hc', base', hbase', s', hs', F', hF', rfl, rfl, _⟩ := transport
  have left := ((literalTaskFieldGraph_entry_iff hb hc hbase hs hF hl 0).1 first).2
  have right := ((literalTaskFieldGraph_entry_iff hb hc' hbase' hs' hF' hl 0).1 second).2
  exact left.trans right.symm

theorem base_eq {base base' : ZFSet.{u}}
    (first : ZFSet.pair t base ∈ literalTaskBaseGraph I P R U Labels)
    (second : ZFSet.pair t' base' ∈ literalTaskBaseGraph I P R U Labels) :
    base' = actionPostcompose P A g base := by
  obtain ⟨a, ha, c, hc, b, hb, s, hs, F, hF, label, hl,
    c', hc', b', hb', s', hs', F', hF', rfl, rfl, _, _, equal, _⟩ := transport
  have left := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).1 first).2
  have right := ((literalTaskFieldGraph_entry_iff ha hc' hb' hs' hF' hl 2).1 second).2
  exact right.trans (equal.trans (congrArg (actionPostcompose P A g) left.symm))

theorem fresh_iff {r q : ZFSet.{u}} (ht : t ∈ I) (ht' : t' ∈ I) :
    ZFSet.pair t q ∈ indexedAttachmentFresh I (constantFamilyGraph I P)
      (constantFamilyGraph I r) (literalTaskSourceGraph I P R U Labels) ↔
    ZFSet.pair t' q ∈ indexedAttachmentFresh I (constantFamilyGraph I P)
      (constantFamilyGraph I r) (literalTaskSourceGraph I P R U Labels) := by
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl,
    c', hc', base', hb', s', hs', F', hF', rfl, rfl, _⟩ := transport
  rw [literalTask_fresh_iff ha hc hb hs hF hl,
    literalTask_fresh_iff ha hc' hb' hs' hF' hl]
  exact and_congr (iff_of_true ht ht') Iff.rfl

theorem shadow_covariant {G m e r μ q x x' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (ht' : t' ∈ I)
    (shadow : ZFSet.pair (ZFSet.pair t q) x ∈
      batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels))
    (acted : ZFSet.pair (ZFSet.pair g x) x' ∈ A) :
    ZFSet.pair (ZFSet.pair t' q) x' ∈
      batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) := by
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl,
    c', hc', base', hb', s', hs', F', hF', rfl, rfl, _, _, equal, _⟩ := transport
  have old := ((literalTask_shadow_iff ha hc hb hs hF hl).1 shadow).2
  obtain ⟨hq, hx, b, hbp, meet, entry⟩ := (pair_mem_attachmentShadowGraph P P μ base a q x).1 old
  have hx' := (ZFSet.pair_mem_prod.1 (action.function.1 acted)).2
  apply (literalTask_shadow_iff ha hc' hb' hs' hF' hl).2
  refine ⟨ht', (pair_mem_attachmentShadowGraph P P μ base' a q x').2
    ⟨hq, hx', b, hbp, meet, ?_⟩⟩
  rw [equal]
  exact (pair_mem_actionPostcompose P A g base b x').2 ⟨hbp, hx', x, hx, entry, acted⟩

theorem upper_covariant {G m e r q x x' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (ht' : t' ∈ I)
    (upper : ZFSet.pair (ZFSet.pair t q) x ∈
      batchAttachmentUpperGraph I P (constantFamilyGraph I P) (literalTaskFilterGraph I P R U Labels))
    (acted : ZFSet.pair (ZFSet.pair g x) x' ∈ A) :
    ZFSet.pair (ZFSet.pair t' q) x' ∈
      batchAttachmentUpperGraph I P (constantFamilyGraph I P) (literalTaskFilterGraph I P R U Labels) := by
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl,
    c', hc', base', hb', s', hs', F', hF', rfl, rfl, _, _, _, equal⟩ := transport
  obtain ⟨_, hq, _, hxF⟩ := (literalTask_upper_iff ha hc hb hs hF hl).1 upper
  have hx' := (ZFSet.pair_mem_prod.1 (action.function.1 acted)).2
  apply (literalTask_upper_iff ha hc' hb' hs' hF' hl).2
  refine ⟨ht', hq, hx', ?_⟩
  rw [equal]
  exact (mem_actionImage P A g F x').2 ⟨hx', x, hxF, acted⟩

theorem inside_covariant {G m e r s s' q v : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hg : g ∈ G)
    (second : TaskTransportCode P R U Labels A g s s') (ht' : t' ∈ I)
    (inside : ZFSet.pair (ZFSet.pair t q) (ZFSet.pair s v) ∈
      batchAttachmentInsideGraph I (constantFamilyGraph I P) (constantFamilyGraph I r)) :
    ZFSet.pair (ZFSet.pair t' q) (ZFSet.pair s' v) ∈
      batchAttachmentInsideGraph I (constantFamilyGraph I P) (constantFamilyGraph I r) := by
  obtain ⟨equal, _, hq, hv, lower⟩ := (constantTask_inside_iff I P r t q s v).1 inside
  subst s
  exact (constantTask_inside_iff I P r t' q s' v).2
    ⟨TaskTransportCode.unique action hg transport second, ht', hq, hv, lower⟩

end TaskTransportCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBatchAttachment
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.AttachmentBatchInputs

universe u
variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
include d

theorem batch_template_order_iff (i : {i : ZFSet.{u} // i ∈ I})
    {x y x' y' : ZFSet.{u}}
    (hx : ZFSet.pair x x' ∈ batchTemplateGraph I P Qs rs As Es i.val)
    (hy : ZFSet.pair y y' ∈ batchTemplateGraph I P Qs rs As Es i.val) :
    ZFSet.pair x' y' ∈ d.batchOrder ↔ ZFSet.pair x y ∈ d.rel i :=
  d.coding.encoded_embedding_order_iff (d.fiber i).templateOrder (d.templates.templateEmbedding i)
    (d.batch_template_fiber_function i) (d.batch_template_graph_entry i) hx hy

theorem batch_template_old_agreement (i : {i : ZFSet.{u} // i ∈ I})
    {q p : ZFSet.{u}} (entry : ZFSet.pair q p ∈ d.embed i) :
    ZFSet.pair q p ∈ batchTemplateGraph I P Qs rs As Es i.val ∧
      ZFSet.pair p p ∈ attachmentOldEmbeddingGraph P := by
  have shape := ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 entry)
  exact ⟨(pair_mem_batchTemplateGraph I P Qs rs As Es i.val q p).2
    ((d.batch_template_entry_iff i q p).2 (Or.inl entry)),
    (pair_mem_attachmentOldEmbeddingGraph P p p).2 ⟨shape.2, rfl⟩⟩

end PartitionPilot.Forcing.AttachmentBatchInputs

namespace PartitionPilot.Forcing.AttachmentBatchInputs
universe u
variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

theorem batch_old_lower_iff (i : {i : ZFSet.{u} // i ∈ I}) {q s p : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i)) (hp : p ∈ P)
    (hs : ZFSet.pair (ZFSet.pair i.val q) s ∈ batchAttachmentShadowGraph I P Qs μs As Es) :
    ZFSet.pair p (ZFSet.pair P (ZFSet.pair i.val q)) ∈ d.batchOrder ↔ ZFSet.pair p s ∈ rP := by
  have eq := d.coding.shadow_value (d.batchFreshNode i hq) s hs
  rw [eq]
  exact d.coding.old_lower_iff ⟨p, hp⟩ (d.batchFreshNode i hq)

theorem batch_old_upper_iff (i : {i : ZFSet.{u} // i ∈ I}) {q p : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i)) (hp : p ∈ P) :
    ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) p ∈ d.batchOrder ↔ p ∈ d.filter i :=
  d.coding.old_upper_iff (d.batchFreshNode i hq) ⟨p, hp⟩

theorem batch_cross_lower_iff (i j : {i : ZFSet.{u} // i ∈ I}) {q t s : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i))
    (ht : t ∈ freshPart (d.space j) (d.rel j) (d.anchor j)) (different : i ≠ j)
    (hs : ZFSet.pair (ZFSet.pair j.val t) s ∈ batchAttachmentShadowGraph I P Qs μs As Es) :
    ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) (ZFSet.pair P (ZFSet.pair j.val t)) ∈
      d.batchOrder ↔ s ∈ d.filter i := by
  have eq := d.coding.shadow_value (d.batchFreshNode j ht) s hs
  rw [eq]
  exact d.coding.cross_lower_iff (d.batchFreshNode i hq) (d.batchFreshNode j ht) different

theorem batch_shadow_meet_code (i : {i : ZFSet.{u} // i ∈ I}) {q p s v : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i)) (hp : p ∈ P)
    (hs : ZFSet.pair (ZFSet.pair i.val q) s ∈ batchAttachmentShadowGraph I P Qs μs As Es)
    (oldMeet : ZFSet.pair (ZFSet.pair s p) v ∈ μP)
    (notAbove : ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) p ∉ d.batchOrder) :
    ZFSet.pair (ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) p) v ∈ d.batchMeetGraph := by
  let x := d.batchFreshNode i hq
  let y : {p : ZFSet.{u} // p ∈ P} := ⟨p, hp⟩
  have sameShadow := d.coding.shadow_value x s hs
  obtain ⟨m, _, unique⟩ := d.oldOrder.operation.2
    (ZFSet.pair (d.templates.shadow x).val p)
    (ZFSet.pair_mem_prod.2 ⟨(d.templates.shadow x).property, hp⟩)
  have sameMeet : v = (d.oldOrder.toMeetOrder.meet (d.templates.shadow x) y).val :=
    (unique v (sameShadow ▸ oldMeet)).trans
      (unique _ (d.oldOrder.toMeetOrder_meet_entry (d.templates.shadow x) y)).symm
  exact sameMeet.symm ▸ d.coding.encoded_shadow_meet x y notAbove

theorem batch_cross_meet_code (i j : {i : ZFSet.{u} // i ∈ I}) {q t s z v : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i))
    (ht : t ∈ freshPart (d.space j) (d.rel j) (d.anchor j)) (different : i ≠ j)
    (hs : ZFSet.pair (ZFSet.pair i.val q) s ∈ batchAttachmentShadowGraph I P Qs μs As Es)
    (hz : ZFSet.pair (ZFSet.pair j.val t) z ∈ batchAttachmentShadowGraph I P Qs μs As Es)
    (oldMeet : ZFSet.pair (ZFSet.pair s z) v ∈ μP)
    (notQT : ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q))
      (ZFSet.pair P (ZFSet.pair j.val t)) ∉ d.batchOrder)
    (notTQ : ZFSet.pair (ZFSet.pair P (ZFSet.pair j.val t))
      (ZFSet.pair P (ZFSet.pair i.val q)) ∉ d.batchOrder) :
    ZFSet.pair (ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q))
      (ZFSet.pair P (ZFSet.pair j.val t))) v ∈ d.batchMeetGraph := by
  let x := d.batchFreshNode i hq
  let y := d.batchFreshNode j ht
  have sameS := d.coding.shadow_value x s hs
  have sameZ := d.coding.shadow_value y z hz
  obtain ⟨m, _, unique⟩ := d.oldOrder.operation.2
    (ZFSet.pair (d.templates.shadow x).val (d.templates.shadow y).val)
    (ZFSet.pair_mem_prod.2 ⟨(d.templates.shadow x).property, (d.templates.shadow y).property⟩)
  have sameMeet : v = (d.oldOrder.toMeetOrder.meet (d.templates.shadow x) (d.templates.shadow y)).val :=
    (unique v (sameS ▸ sameZ ▸ oldMeet)).trans
      (unique _ (d.oldOrder.toMeetOrder_meet_entry (d.templates.shadow x) (d.templates.shadow y))).symm
  exact sameMeet.symm ▸ d.coding.encoded_cross_meet x y different notQT notTQ

end PartitionPilot.Forcing.AttachmentBatchInputs

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundEligibleCaps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem PosetActionCode.raw_fixes_top {G P m inv e r A g T : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (group : GroupCode G m inv e)
    (order : PartialOrderCode P r) (hg : g ∈ G) (hT : T ∈ P)
    (greatest : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    ZFSet.pair (ZFSet.pair g T) T ∈ A := by
  obtain ⟨y, entry, _⟩ := action.function.2 (ZFSet.pair g T)
    (ZFSet.pair_mem_prod.2 ⟨hg, hT⟩)
  have hy := (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2
  obtain ⟨x, hx, preimage⟩ := action.raw_preimage group hg hT
  have lower := (action.raw_order_iff group order hg preimage entry).2 (greatest x hx)
  have equal : y = T := order.antisymm y hy T hT (greatest y hy) lower
  exact equal ▸ entry

theorem EligibleTaskCode.source_proper
    {G P m inv e r μ A source target base separator F T : ZFSet.{u}}
    (code : EligibleTaskCode P G r μ A source target base separator F)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hT : T ∈ P)
    (greatest : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    ZFSet.pair source T ∈ r ∧ ZFSet.pair T source ∉ r := by
  refine ⟨greatest source code.source_mem, ?_⟩
  intro lower
  have sourceEq : source = T := meet.order.antisymm source code.source_mem T hT
    (greatest source code.source_mem) lower
  obtain ⟨g, hg, restriction⟩ := code.representative
  have topEntry := action.raw_fixes_top group meet.order hg hT greatest
  have targetEntry : ZFSet.pair (ZFSet.pair g T) target ∈ A := sourceEq ▸ restriction.target_entry
  obtain ⟨y, _, unique⟩ := action.function.2 (ZFSet.pair g T)
    (ZFSet.pair_mem_prod.2 ⟨hg, hT⟩)
  have targetEq : target = T := (unique target targetEntry).trans (unique T topEntry).symm
  exact code.strict (targetEq.symm ▸ greatest separator code.separator_mem)






end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundEligibleTasks_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundEligibleTasks P G r μ A Labels ∈ M.sets := by
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  have hR : R ∈ M.sets := M.groundRelations_mem pairing unions powers separation hP hP
  have hU : U ∈ M.sets := M.groundMeetFilters_mem powers separation hP hr hμ meet
  let params := extend P (extend G (extend r (extend μ (extend A
    (extend R (extend U (extend Labels Fin.elim0)))))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hP (Fin.cases hG (Fin.cases hr (Fin.cases hμ (Fin.cases hA
      (Fin.cases hR (Fin.cases hU (Fin.cases hLabels (fun i => Fin.elim0 i))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.eligibleTaskEntryFormula 0 1 2 3 4 5 6 7 8) params members
    (M.literalTaskBound_mem pairing unions powers separation hP hR hU hLabels)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.eligibleTaskEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (literalTaskBound P R U Labels) = M.groundEligibleTasks P G r μ A Labels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_eligibleTaskEntryFormula _ _ _ _ _ _ _ _ _ _ meet]
    exact ⟨And.right, fun hz => ⟨eligibleTaskSet_subset P G r μ A R U Labels hz, hz⟩⟩
  exact equal ▸ selected

theorem literalTaskCode_mem_groundEligibleTasks
    (P G r μ A Labels a c base e F label : ZFSet.{u}) :
    literalTaskCode a c base e F label ∈ M.groundEligibleTasks P G r μ A Labels ↔
      label ∈ Labels ∧ base ∈ M.sets ∧ F ∈ M.sets ∧ EligibleTaskCode P G r μ A a c base e F := by
  rw [groundEligibleTasks, literalTaskCode_mem_eligibleTaskSet,
    M.mem_groundRelations, M.mem_groundMeetFilters]
  constructor
  · rintro ⟨_, _, ⟨hBase, _⟩, _, ⟨hF, _⟩, hLabel, code⟩
    exact ⟨hLabel, hBase, hF, code⟩
  · rintro ⟨hLabel, hBase, hF, code⟩
    obtain ⟨g, _, represented⟩ := code.representative
    exact ⟨code.source_mem, code.target_mem, ⟨hBase, represented.shape⟩,
      code.separator_mem, ⟨hF, code.filter⟩, hLabel, code⟩






theorem groundEligibleTaskFields
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    I ∈ M.sets ∧ constantFamilyGraph I P ∈ M.sets ∧
      constantFamilyGraph I r ∈ M.sets ∧ constantFamilyGraph I μ ∈ M.sets ∧
      ∀ j : Fin 6, literalTaskFieldGraph I P R U Labels j ∈ M.sets ∧
        ZFSet.IsFunc I (literalTaskFieldBound P R U Labels j) (literalTaskFieldGraph I P R U Labels j) := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hR := M.groundRelations_mem pairing unions powers separation hP hP
  have hU := M.groundMeetFilters_mem powers separation hP hr hμ meet
  exact ⟨hI, M.constantFamilyGraph_mem pairing unions powers separation hI hP,
    M.constantFamilyGraph_mem pairing unions powers separation hI hr,
    M.constantFamilyGraph_mem pairing unions powers separation hI hμ,
    M.literalTaskFieldFamilies pairing unions powers separation hI hP hR hU hLabels
      (eligibleTaskSet_subset P G r μ A _ _ Labels)⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem taskRepresentativeRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P G r A R U Labels : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hA : A ∈ M.sets)
    (hR : R ∈ M.sets) (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) :
    taskRepresentativeRelation I P G r A R U Labels ∈ M.sets := by
  let params := extend I (extend P (extend G (extend r (extend A
    (extend R (extend U (extend Labels Fin.elim0)))))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hI (Fin.cases hP (Fin.cases hG (Fin.cases hr (Fin.cases hA
      (Fin.cases hR (Fin.cases hU (Fin.cases hLabels (fun i => Fin.elim0 i))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.taskRepresentativeEntryFormula 0 1 2 3 4 5 6 7 8) params members
    (M.prod_mem pairing unions powers separation hI hG)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.taskRepresentativeEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (ZFSet.prod I G) = taskRepresentativeRelation I P G r A R U Labels := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, taskRepresentativeRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taskRepresentativeEntryFormula _ _ _ _ _ _ _ _ _ _)
  exact equal ▸ selected

theorem exists_groundTaskRepresentatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    ∃ representatives ∈ M.sets, ZFSet.IsFunc I G representatives ∧
      (∀ task g, ZFSet.pair task g ∈ representatives →
        TaskRepresentative P r A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels task g) ∧
      (∀ a c base e F label g, ZFSet.pair (literalTaskCode a c base e F label) g ∈ representatives →
        RestrictedActionCode P r A g a c base) := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hR := M.groundRelations_mem pairing unions powers separation hP hP
  have hU := M.groundMeetFilters_mem powers separation hP hr hμ meet
  obtain ⟨representatives, ground, function, subset⟩ := M.uniformize_relation
    pairing unions powers separation choice hI hG
    (M.taskRepresentativeRelation_mem pairing unions powers separation hI hP hG hr hA hR hU hLabels)
    (eligibleTask_representative_total P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
  have represents : ∀ task g, ZFSet.pair task g ∈ representatives →
      TaskRepresentative P r A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels task g :=
    fun _ _ entry => ((pair_mem_taskRepresentativeRelation _ _ _ _ _ _ _ _ _ _).1 (subset entry)).2.2
  exact ⟨representatives, ground, function, represents,
    fun _ _ _ _ _ _ _ entry => (represents _ _ entry).restriction⟩






end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround

variable (M : TransitiveGround.{u})
variable {P G r μ A Labels m inv one T : ZFSet.{u}}
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
  (meet : MeetOrderCode P r μ) (hT : T ∈ P)
  (greatest : ∀ x ∈ P, ZFSet.pair x T ∈ r)
include group action meet hT greatest

theorem groundEligibleTask_cap_fresh {i : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels) :
    ZFSet.pair i T ∈ indexedAttachmentFresh (M.groundEligibleTasks P G r μ A Labels)
      (constantFamilyGraph (M.groundEligibleTasks P G r μ A Labels) P)
      (constantFamilyGraph (M.groundEligibleTasks P G r μ A Labels) r)
      (literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels) P
        (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) := by
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl, rfl, code⟩ :=
    (mem_eligibleTaskSet P G r μ A _ _ Labels i).1 hi
  exact (literalTask_fresh_iff ha hc hb hs hF hl).2
    ⟨hi, hT, (code.source_proper group action meet hT greatest).2⟩

theorem groundEligibleTask_cap_entry {i : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    ZFSet.pair (ZFSet.pair i T) (eligibleTaskCap P T i) ∈
      batchAttachmentTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) := by
  have fresh := M.groundEligibleTask_cap_fresh group action meet hT greatest hi
  exact (pair_mem_batchAttachmentTemplateGraph _ _ _ _ _ _ _ _ _).2
    ⟨indexedAttachmentFresh_subset _ _ _ _ fresh, pair_mem_taggedExtension.2 fresh,
      Or.inr ⟨fresh, rfl⟩⟩

theorem groundEligibleTask_cap_mem {i : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels) :
    eligibleTaskCap P T i ∈ (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batchCarrier :=
  pair_mem_taggedExtension.2 (M.groundEligibleTask_cap_fresh group action meet hT greatest hi)

omit group action in
theorem groundEligibleTask_cap_shadow {i c : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    ZFSet.pair (ZFSet.pair i T) c ∈ batchAttachmentShadowGraph I P
      (constantFamilyGraph I P) (constantFamilyGraph I μ)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) := by
  obtain ⟨a, ha, b, hb, base, hbase, s, hs, F, hF, label, hl, rfl, code⟩ :=
    (mem_eligibleTaskSet P G r μ A _ _ Labels i).1 hi
  obtain rfl := ((literalTaskFieldGraph_entry_iff ha hb hbase hs hF hl 1).1 target).2
  have topMeet : ZFSet.pair (ZFSet.pair T a) a ∈ μ := meet.pair_iff.2
    ⟨hT, ha, ha, greatest a ha, meet.order.refl a ha,
      fun _ _ _ lower => lower⟩
  obtain ⟨g, _, represented⟩ := code.representative
  have baseEntry := (represented.entries a ha c hb).2
    ⟨meet.order.refl a ha, represented.target_entry⟩
  exact (literalTask_shadow_iff ha hb hbase hs hF hl).2
    ⟨hi, (pair_mem_attachmentShadowGraph _ _ _ _ _ _ _).2
      ⟨hT, hb, a, ha, topMeet, baseEntry⟩⟩

theorem groundEligibleTask_negative_cap {i c F v w : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (filter : ZFSet.pair i F ∈ literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (hv : v ∈ P) (negative : v ∉ F)
    (entry : ZFSet.pair (ZFSet.pair (eligibleTaskCap P T i) v) w ∈
      (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batchMeetGraph) :
    ZFSet.pair (ZFSet.pair c v) w ∈ μ ∧ ZFSet.pair w c ∈ r ∧
      ZFSet.pair w c ∈ (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).batchOrder := by
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let j : {i : ZFSet.{u} // i ∈ M.groundEligibleTasks P G r μ A Labels} := ⟨i, hi⟩
  have fresh := M.groundEligibleTask_cap_fresh group action meet hT greatest hi
  have freshT : T ∈ freshPart (d.space j) (d.rel j) (d.anchor j) :=
    (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
      (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 fresh
  have shadow := M.groundEligibleTask_cap_shadow meet hT greatest hi target
  have hc := (ZFSet.pair_mem_prod.1 (d.batch_shadow_function.1 shadow)).2
  have filterEq : d.filter j = F := (d.filters.unique filter (d.filter_entry j)).symm
  have notAbove : ZFSet.pair (eligibleTaskCap P T i) v ∉ d.batchOrder := by
    intro lower
    have positive := (d.batch_old_upper_iff j freshT hv).1 lower
    exact negative (filterEq ▸ positive)
  obtain ⟨z, oldMeet, _⟩ := meet.operation.2 (ZFSet.pair c v)
    (ZFSet.pair_mem_prod.2 ⟨hc, hv⟩)
  have newMeet := d.batch_shadow_meet_code j freshT hv shadow oldMeet notAbove
  obtain ⟨_, _, unique⟩ := d.batch_meetOrder.operation.2
    (ZFSet.pair (eligibleTaskCap P T i) v)
    (ZFSet.pair_mem_prod.2 ⟨M.groundEligibleTask_cap_mem group action meet hT greatest hi,
      old_mem_taggedExtension hv⟩)
  have equal : w = z := (unique w entry).trans (unique z newMeet).symm
  have oldW : ZFSet.pair (ZFSet.pair c v) w ∈ μ := equal.symm ▸ oldMeet
  have lower := meet.lower_left c v w oldW
  have hw := (ZFSet.pair_mem_prod.1 (meet.operation.1 oldW)).2
  exact ⟨oldW, lower, (d.coding.le_encode (.inl ⟨w, hw⟩) (.inl ⟨c, hc⟩)).2 lower⟩

end TransitiveGround






end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundRecursiveActions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem taskTransportGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G I P R U Labels A : ZFSet.{u}} (hG : G ∈ M.sets) (hI : I ∈ M.sets)
    (hP : P ∈ M.sets) (hR : R ∈ M.sets) (hU : U ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hA : A ∈ M.sets) :
    taskTransportGraph G I P R U Labels A ∈ M.sets := by
  let params := extend G (extend I (extend P (extend R (extend U (extend Labels (extend A Fin.elim0))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.taskTransportEntryFormula 0 1 2 3 4 5 6 7) params
    (Fin.cases hG (Fin.cases hI (Fin.cases hP (Fin.cases hR (Fin.cases hU
      (Fin.cases hLabels (Fin.cases hA (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG hI) hI)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.taskTransportEntryFormula 0 1 2 3 4 5 6 7) (extend z params))
      (ZFSet.prod (ZFSet.prod G I) I) = taskTransportGraph G I P R U Labels A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, taskTransportGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_taskTransportEntryFormula 0 1 2 3 4 5 6 7 _)
  exact equal ▸ selected

theorem literalTask_transport_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e a c base s F label δ c' s' : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hδ : δ ∈ G)
    (ht : literalTaskCode a c base s F label ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair (ZFSet.pair δ c) c' ∈ A)
    (separator : ZFSet.pair (ZFSet.pair δ s) s' ∈ A) :
    literalTaskCode a c' (actionPostcompose P A δ base) s' (actionImage P A δ F) label ∈
      M.groundEligibleTasks P G r μ A Labels := by
  have old := (M.literalTaskCode_mem_groundEligibleTasks P G r μ A Labels a c base s F label).1 ht
  exact (M.literalTaskCode_mem_groundEligibleTasks P G r μ A Labels a c'
    (actionPostcompose P A δ base) s' (actionImage P A δ F) label).2
    ⟨old.1, M.actionPostcompose_mem pairing unions powers separation hP hA (M.transitive hG hδ) old.2.1,
      M.actionImage_mem separation hP hA (M.transitive hG hδ) old.2.2.1,
      old.2.2.2.transport group action meet hδ target separator⟩

theorem groundTaskTransport_total
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    ∀ δ ∈ G, ∀ t ∈ M.groundEligibleTasks P G r μ A Labels,
      ∃ t' ∈ M.groundEligibleTasks P G r μ A Labels,
        TaskTransportCode P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels A δ t t' := by
  intro δ hδ t ht
  obtain ⟨a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel, equal, _⟩ :=
    (mem_eligibleTaskSet P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels t).1 ht
  subst t
  obtain ⟨c', target, _⟩ := action.function.2 (ZFSet.pair δ c) (ZFSet.pair_mem_prod.2 ⟨hδ, hc⟩)
  obtain ⟨s', separator, _⟩ := action.function.2 (ZFSet.pair δ s) (ZFSet.pair_mem_prod.2 ⟨hδ, hs⟩)
  have newTask := M.literalTask_transport_mem pairing unions powers separation hP hG hA
    group action meet hδ ht target separator
  have fields := (literalTaskCode_mem_eligibleTaskSet P G r μ A
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels a c'
    (actionPostcompose P A δ base) s' (actionImage P A δ F) label).1 newTask
  exact ⟨_, newTask, a, ha, c, hc, base, hbase, s, hs, F, hF, label, hlabel,
    c', fields.2.1, actionPostcompose P A δ base, fields.2.2.1,
    s', fields.2.2.2.1, actionImage P A δ F, fields.2.2.2.2.1,
    rfl, rfl, target, separator, rfl, rfl⟩

theorem groundTaskTransport_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    ZFSet.IsFunc (ZFSet.prod G (M.groundEligibleTasks P G r μ A Labels))
      (M.groundEligibleTasks P G r μ A Labels) (M.groundTaskTransport P G r μ A Labels) :=
  taskTransportGraph_function action
    (M.groundTaskTransport_total pairing unions powers separation hP hG hA group action meet)

theorem groundTaskTransport_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (meet : MeetOrderCode P r μ) :
    M.groundTaskTransport P G r μ A Labels ∈ M.sets :=
  M.taskTransportGraph_mem pairing unions powers separation hG
    (M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet)
    hP (M.groundRelations_mem pairing unions powers separation hP hP)
    (M.groundMeetFilters_mem powers separation hP hr hμ meet) hLabels hA

theorem groundTaskTransport_one {P G r μ A Labels m e : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (he : e ∈ G) :
    ∀ t ∈ M.groundEligibleTasks P G r μ A Labels,
      ZFSet.pair (ZFSet.pair e t) t ∈ M.groundTaskTransport P G r μ A Labels :=
  taskTransportGraph_one action he
    (fun base hbase => ((M.mem_groundRelations P P base).1 hbase).2)
    (fun F hF => ((M.mem_groundMeetFilters P r μ F).1 hF).2.subset)
    (eligibleTaskSet_subset P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)

theorem groundTaskTransport_mul {P G r μ A Labels m e g h k t t' t'' : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (hg : g ∈ G) (hh : h ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair g h) k ∈ m)
    (first : ZFSet.pair (ZFSet.pair h t) t' ∈ M.groundTaskTransport P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair g t') t'' ∈ M.groundTaskTransport P G r μ A Labels) :
    ZFSet.pair (ZFSet.pair k t) t'' ∈ M.groundTaskTransport P G r μ A Labels :=
  taskTransportGraph_mul action
    (fun F hF => ((M.mem_groundMeetFilters P r μ F).1 hF).2.subset) hg hh hk product first second

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

theorem constantTemplateFresh_subset (I P r anchors : ZFSet.{u}) :
    indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r) anchors ⊆
      ZFSet.prod I P := by
  intro z hz
  obtain ⟨i, hi, q, rfl, Q, r', a, space, _, _, hq, _⟩ :=
    (mem_indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r) anchors z).1 hz
  have equal := ((pair_mem_constantFamilyGraph I P i Q).1 space).2
  exact ZFSet.pair_mem_prod.2 ⟨hi, equal ▸ hq⟩

namespace TransitiveGround

open SetFormula

theorem groundTaskTransport_setAction (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    SetActionCode G (M.groundEligibleTasks P G r μ A Labels) m e
      (M.groundTaskTransport P G r μ A Labels) := by
  refine ⟨M.groundTaskTransport_function pairing unions powers separation hP hG hA group action meet,
    M.groundTaskTransport_one action group.identity_mem, ?_⟩
  intro g hg h hh k hk _ _ _ _ _ _ product first second
  exact M.groundTaskTransport_mul action hg hh hk product first second

theorem groundEligibleFreshAction_setAction (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels)
    SetActionCode G N m e (M.groundEligibleFreshAction P G r μ A Labels) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  apply indexedTaskActionGraph_setAction
    (M.groundTaskTransport_setAction pairing unions powers separation hP hG hA group action meet)
    (constantTemplateFresh_subset I P r (literalTaskSourceGraph I P R U Labels))
  intro g _ i hi j hj q _ fresh entry
  have transported := ((triple_mem_taskTransportGraph G I P R U Labels A g i j).1 entry).2.2.2
  exact (transported.fresh_iff hi hj).1 fresh

end TransitiveGround






namespace ActionAgreementBelow

variable {P r A g h v : ZFSet.{u}}
variable (agree : ActionAgreementBelow P r A g h v)
include agree

theorem symm : ActionAgreementBelow P r A h g v :=
  fun x hx y hy lower => (agree x hx y hy lower).symm

theorem image_subset {G m inv e μ F : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hh : h ∈ G)
    (filter : MeetFilterCode P r μ F) (positive : v ∈ F) :
    actionImage P A g F ⊆ actionImage P A h F := by
  intro y hy
  obtain ⟨hyP, x, hx, image⟩ := (mem_actionImage P A g F y).1 hy
  obtain ⟨w, entry, _⟩ := meet.operation.2 (ZFSet.pair x v)
    (ZFSet.pair_mem_prod.2 ⟨filter.subset hx, filter.subset positive⟩)
  have hwF := filter.closed_meet x hx v positive w entry
  have hwP := filter.subset hwF
  obtain ⟨z, shared, _⟩ := action.function.2 (ZFSet.pair g w) (ZFSet.pair_mem_prod.2 ⟨hg, hwP⟩)
  have hzP := (ZFSet.pair_mem_prod.1 (action.function.1 shared)).2
  have shared' := (agree w hwP z hzP (meet.lower_right x v w entry)).1 shared
  have hzF : z ∈ actionImage P A h F := (mem_actionImage P A h F z).2 ⟨hzP, w, hwF, shared'⟩
  have lower := action.monotone g hg w hwP x (filter.subset hx) z hzP y hyP
    shared image (meet.lower_left x v w entry)
  exact (actionImage_filter group action meet hh filter).upward z hzF y hyP lower

theorem actionImage_eq {G m inv e μ F : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hh : h ∈ G)
    (filter : MeetFilterCode P r μ F) (positive : v ∈ F) :
    actionImage P A g F = actionImage P A h F := by
  apply ZFSet.ext
  intro y
  exact ⟨fun hy => agree.image_subset group action meet hg hh filter positive hy,
    fun hy => agree.symm.image_subset group action meet hh hg filter positive hy⟩

theorem postcompose_eq {base : ZFSet.{u}}
    (bound : ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x y ∈ base → ZFSet.pair y v ∈ r) :
    actionPostcompose P A g base = actionPostcompose P A h base := by
  have inclusion {b c : ZFSet.{u}} (same : ActionAgreementBelow P r A b c v) :
      actionPostcompose P A b base ⊆ actionPostcompose P A c base := by
    intro z hz
    obtain ⟨x, _, y, _, rfl⟩ := ZFSet.mem_prod.1 (actionPostcompose_subset P A b base hz)
    obtain ⟨hx, hy, w, hw, entry, acted⟩ := (pair_mem_actionPostcompose P A b base x y).1 hz
    exact (pair_mem_actionPostcompose P A c base x y).2
      ⟨hx, hy, w, hw, entry, (same w hw y hy (bound x hx w hw entry)).1 acted⟩
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => inclusion agree hz, fun hz => inclusion agree.symm hz⟩

end ActionAgreementBelow

theorem EligibleTaskCode.base_below_positive
    {P G r μ A source target base separator F m e v x y : ZFSet.{u}}
    (code : EligibleTaskCode P G r μ A source target base separator F)
    (action : PosetActionCode G P m e r A) (order : PartialOrderCode P r)
    (positive : v ∈ F) (entry : ZFSet.pair x y ∈ base) : ZFSet.pair y v ∈ r := by
  obtain ⟨k, hk, represented⟩ := code.representative
  have shape := ZFSet.pair_mem_prod.1 (represented.shape entry)
  have lower := (represented.entries x shape.1 y shape.2).1 entry
  have yt := action.monotone k hk x shape.1 source code.source_mem y shape.2 target code.target_mem
    lower.2 represented.target_entry lower.1
  exact order.trans y shape.2 separator code.separator_mem v (code.filter.subset positive)
    (order.trans y shape.2 target code.target_mem separator code.separator_mem yt code.lower)
    (code.upper v positive)

theorem TaskTransportCode.literal_outputs
    {P R U Labels A g a c base s F label t' : ZFSet.{u}}
    (transport : TaskTransportCode P R U Labels A g (literalTaskCode a c base s F label) t') :
    ∃ c' ∈ P, ∃ base' ∈ R, ∃ s' ∈ P, ∃ F' ∈ U,
      t' = literalTaskCode a c' base' s' F' label ∧
      ZFSet.pair (ZFSet.pair g c) c' ∈ A ∧ ZFSet.pair (ZFSet.pair g s) s' ∈ A ∧
      base' = actionPostcompose P A g base ∧ F' = actionImage P A g F := by
  obtain ⟨a₀, _, c₀, _, b₀, _, s₀, _, F₀, _, l₀, _,
    c', hc', b', hb', s', hs', F', hF', old, new, target, separator, baseEq, filterEq⟩ := transport
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := literalTaskCode_inj.1 old
  exact ⟨c', hc', b', hb', s', hs', F', hF', new, target, separator, baseEq, filterEq⟩

theorem TaskTransportCode.positive_agreement
    {P G r μ A R U Labels m inv e g h v a c base s F label t' t'' : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hh : h ∈ G)
    (code : EligibleTaskCode P G r μ A a c base s F)
    (agree : ActionAgreementBelow P r A g h v) (positive : v ∈ F)
    (first : TaskTransportCode P R U Labels A g (literalTaskCode a c base s F label) t')
    (second : TaskTransportCode P R U Labels A h (literalTaskCode a c base s F label) t'') : t' = t'' := by
  obtain ⟨c', _, base', _, s', _, F', _, new, target, separator, baseEq, filterEq⟩ := first.literal_outputs
  obtain ⟨c'', _, base'', _, s'', _, F'', _, new', target', separator', baseEq', filterEq'⟩ := second.literal_outputs
  have sv := code.upper v positive
  have cv := meet.order.trans c code.target_mem s code.separator_mem v (code.filter.subset positive) code.lower sv
  have sameC := agree.entry_eq action hh code.target_mem cv target target'
  have sameS := agree.entry_eq action hh code.separator_mem sv separator separator'
  have sameBase : base' = base'' := baseEq.trans ((agree.postcompose_eq
    (fun _ _ _ _ entry => code.base_below_positive action meet.order positive entry)).trans baseEq'.symm)
  have sameFilter : F' = F'' := filterEq.trans
    ((agree.actionImage_eq group action meet hg hh code.filter positive).trans filterEq'.symm)
  rw [new, new', sameC, sameS, sameBase, sameFilter]

namespace TransitiveGround

variable (M : TransitiveGround.{u})

theorem groundTaskTransport_positive_agreement
    {P G r μ A Labels m inv e g h v a c base s F label t' t'' : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (agree : ActionAgreementBelow P r A g h v) (positive : v ∈ F)
    (first : ZFSet.pair (ZFSet.pair g (literalTaskCode a c base s F label)) t' ∈
      M.groundTaskTransport P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair h (literalTaskCode a c base s F label)) t'' ∈
      M.groundTaskTransport P G r μ A Labels) : t' = t'' := by
  have parts := (triple_mem_taskTransportGraph G (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels A g _ t').1 first
  have parts' := (triple_mem_taskTransportGraph G (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels A h _ t'').1 second
  have code := ((M.literalTaskCode_mem_groundEligibleTasks P G r μ A Labels a c base s F label).1 parts.2.1).2.2.2
  exact TaskTransportCode.positive_agreement group action meet parts.1 parts'.1 code agree positive
    parts.2.2.2 parts'.2.2.2

end TransitiveGround






end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_EligibleBatchEquivariance
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

theorem groundEligibleFreshAction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundEligibleFreshAction P G r μ A Labels ∈ M.sets := by
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs (fields 0).1
  exact M.indexedTaskActionGraph_mem pairing unions powers separation hG hI hP hN
    (M.groundTaskTransport_mem pairing unions powers separation hP hG hr hμ hA hLabels meet)

theorem groundEligibleBatchAction_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (meet : MeetOrderCode P r μ) : M.groundEligibleBatchAction P G r μ A Labels ∈ M.sets := by
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs (fields 0).1
  exact M.taggedActionGraph_mem pairing unions powers separation hG hP hN hA
    (M.groundEligibleFreshAction_mem pairing unions powers separation hP hG hr hμ hA hLabels meet)

theorem groundEligibleBatchCovariance
    {P G r μ A Labels m e : ZFSet.{u}} (action : PosetActionCode G P m e r A) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels)
    CodedAttachmentCovariance G P N A (M.groundEligibleFreshAction P G r μ A Labels)
      (batchAttachmentInsideGraph I (constantFamilyGraph I P) (constantFamilyGraph I r))
      (batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels))
      (batchAttachmentUpperGraph I P (constantFamilyGraph I P) (literalTaskFilterGraph I P R U Labels)) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
    (literalTaskSourceGraph I P R U Labels)
  let T := M.groundTaskTransport P G r μ A Labels
  refine ⟨?_, ?_, ?_⟩
  · intro g hg q _ t _ q' _ t' _ first second inside
    obtain ⟨_, _, _, i, _, i', hi', x, _, rfl, rfl, firstTask⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g q q').1 first
    obtain ⟨_, _, _, j, _, j', _, y, _, rfl, rfl, secondTask⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g t t').1 second
    have ti := ((triple_mem_taskTransportGraph G I P R U Labels A g i i').1 firstTask).2.2.2
    have tj := ((triple_mem_taskTransportGraph G I P R U Labels A g j j').1 secondTask).2.2.2
    exact ti.inside_covariant action hg tj hi' inside
  · intro g _ q _ q' _ p _ p' _ first acted shadow
    obtain ⟨_, _, _, i, _, i', hi', x, _, rfl, rfl, task⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g q q').1 first
    have ti := ((triple_mem_taskTransportGraph G I P R U Labels A g i i').1 task).2.2.2
    exact ti.shadow_covariant action hi' shadow acted
  · intro g _ q _ q' _ p _ p' _ first acted upper
    obtain ⟨_, _, _, i, _, i', hi', x, _, rfl, rfl, task⟩ :=
      (triple_mem_indexedTaskActionGraph G I P N T g q q').1 first
    have ti := ((triple_mem_taskTransportGraph G I P R U Labels A g i i').1 task).2.2.2
    exact ti.upper_covariant action hi' upper acted

theorem groundEligibleBatchAction_code
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    PosetActionCode G d.batchCarrier m e d.batchOrder (M.groundEligibleBatchAction P G r μ A Labels) :=
  action.tagged_attachment
    (M.groundEligibleFreshAction_setAction pairing unions powers separation hP hG hA group action meet)
    (M.groundEligibleBatchCovariance action)

theorem groundEligibleBatchAction_old_iff
    {P G r μ A Labels g x y : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair (ZFSet.pair g x) y ∈ M.groundEligibleBatchAction P G r μ A Labels ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A :=
  taggedActionGraph_old_iff hx

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround

universe u
variable (M : TransitiveGround.{u})

theorem groundEligibleBatchAction_representation
    {P G r μ A Labels m inv e δ i j q x y : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ)
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let representation := batchAttachmentTemplateGraph I P
      (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels)
    ZFSet.pair (ZFSet.pair i q) x ∈ representation →
    ZFSet.pair (ZFSet.pair j q) y ∈ representation →
    ZFSet.pair (ZFSet.pair δ x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let Qs := constantFamilyGraph I P
  let rs := constantFamilyGraph I r
  let As := literalTaskSourceGraph I P R U Labels
  let Es := literalTaskBaseGraph I P R U Labels
  let N := indexedAttachmentFresh I Qs rs As
  let T := M.groundTaskTransport P G r μ A Labels
  let B := M.groundEligibleFreshAction P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  dsimp only
  intro first second
  obtain ⟨hδ, hi, hj, transport⟩ :=
    (triple_mem_taskTransportGraph G I P R U Labels A δ i j).1 task
  let ii : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  let jj : {i : ZFSet.{u} // i ∈ I} := ⟨j, hj⟩
  obtain ⟨domain, _, branch⟩ :=
    (pair_mem_batchAttachmentTemplateGraph I P Qs rs As Es i q x).1 first
  obtain ⟨_, Q, fieldQ, hqQ⟩ := (pair_mem_indexedAttachmentDomain I Qs i q).1 domain
  have equalQ := ((pair_mem_constantFamilyGraph I P i Q).1 fieldQ).2
  have hq : q ∈ P := equalQ ▸ hqQ
  have newDomain : ZFSet.pair j q ∈ indexedAttachmentDomain I Qs :=
    (pair_mem_indexedAttachmentDomain I Qs j q).2
      ⟨hj, P, (pair_mem_constantFamilyGraph I P j P).2 ⟨hj, rfl⟩, hq⟩
  rcases branch with ⟨base, field, image⟩ | ⟨fresh, equal⟩
  · have image' : ZFSet.pair q x ∈ d.embed ii :=
      d.embeddings.unique field (d.embed_entry ii) ▸ image
    have hx := (ZFSet.pair_mem_prod.1 ((d.fiber ii).base_function.1 image')).2
    obtain ⟨v, acted, _⟩ := action.function.2 (ZFSet.pair δ x)
      (ZFSet.pair_mem_prod.2 ⟨hδ, hx⟩)
    have hv := (action.toSetAction.entry_shape acted).2.2
    have baseEq := transport.base_eq field (d.embed_entry jj)
    have newImage : ZFSet.pair q v ∈ d.embed jj := by
      rw [baseEq]
      exact (pair_mem_actionPostcompose P A δ base q v).2 ⟨hq, hv, x, hx, image, acted⟩
    have newEntry : ZFSet.pair (ZFSet.pair j q) v ∈
        batchAttachmentTemplateGraph I P Qs rs As Es :=
      (pair_mem_batchAttachmentTemplateGraph I P Qs rs As Es j q v).2
        ⟨newDomain, old_mem_taggedExtension hv, Or.inl ⟨d.embed jj, d.embed_entry jj, newImage⟩⟩
    have same : v = y := d.batch_template_unique jj newEntry second
    apply (triple_mem_taggedActionGraph G P N A B δ x y).2
    exact Or.inl (same ▸ acted)
  · have newFresh : ZFSet.pair j q ∈ N := (transport.fresh_iff hi hj).1 fresh
    have newEntry : ZFSet.pair (ZFSet.pair j q) (ZFSet.pair P (ZFSet.pair j q)) ∈
        batchAttachmentTemplateGraph I P Qs rs As Es :=
      (pair_mem_batchAttachmentTemplateGraph I P Qs rs As Es j q _).2
        ⟨newDomain, pair_mem_taggedExtension.2 newFresh, Or.inr ⟨newFresh, rfl⟩⟩
    have same : ZFSet.pair P (ZFSet.pair j q) = y := d.batch_template_unique jj newEntry second
    have moved : ZFSet.pair (ZFSet.pair δ (ZFSet.pair i q)) (ZFSet.pair j q) ∈ B :=
      (triple_mem_indexedTaskActionGraph G I P N T δ (ZFSet.pair i q) (ZFSet.pair j q)).2
        ⟨hδ, fresh, newFresh, i, hi, j, hj, q, hq, rfl, rfl, task⟩
    exact (triple_mem_taggedActionGraph G P N A B δ x y).2
      (Or.inr ⟨hδ, ZFSet.pair i q, fresh, ZFSet.pair j q, newFresh, equal, same.symm, moved⟩)

theorem groundEligibleBatchAction_equivariant
    {P G r μ A Labels m inv e δ i j q x y : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ)
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let copies := batchTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels)
    ZFSet.pair q x ∈ copies i → ZFSet.pair q y ∈ copies j →
    ZFSet.pair (ZFSet.pair δ x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
  dsimp only
  intro first second
  exact M.groundEligibleBatchAction_representation group action meet task
    ((pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).1 first)
    ((pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).1 second)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_EligibleBatchAgreement
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

universe u

theorem groundEligibleFreshAction_positive_agreement (M : TransitiveGround.{u})
    {P G r μ A Labels m inv e g h v q q' q'' : ZFSet.{u}}
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (agree : ActionAgreementBelow P r A g h v)
    (first : ZFSet.pair (ZFSet.pair g q) q' ∈ M.groundEligibleFreshAction P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair h q) q'' ∈ M.groundEligibleFreshAction P G r μ A Labels)
    (upper : ZFSet.pair q v ∈ batchAttachmentUpperGraph
      (M.groundEligibleTasks P G r μ A Labels) P
      (constantFamilyGraph (M.groundEligibleTasks P G r μ A Labels) P)
      (literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels) P
        (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)) : q' = q'' := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let N := indexedAttachmentFresh I (constantFamilyGraph I P) (constantFamilyGraph I r)
    (literalTaskSourceGraph I P R U Labels)
  let T := M.groundTaskTransport P G r μ A Labels
  obtain ⟨_, _, _, i, hi, i', _, x, _, source, target, firstTask⟩ :=
    (triple_mem_indexedTaskActionGraph G I P N T g q q').1 first
  obtain ⟨_, _, _, j, _, j', _, y, _, source', target', secondTask⟩ :=
    (triple_mem_indexedTaskActionGraph G I P N T h q q'').1 second
  have indices : i = j := (ZFSet.pair_inj.1 (source.symm.trans source')).1
  have points : x = y := (ZFSet.pair_inj.1 (source.symm.trans source')).2
  subst j y
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F, hF, label, hl, equal, _⟩ :=
    (mem_eligibleTaskSet P G r μ A R U Labels i).1 hi
  subst i
  rw [source] at upper
  have positive := ((literalTask_upper_iff ha hc hb hs hF hl).1 upper).2.2.2
  have same := M.groundTaskTransport_positive_agreement group action meet agree positive firstTask secondTask
  exact target.trans ((congrArg (fun task => ZFSet.pair task x) same).trans target'.symm)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

theorem codedAttachmentOrder_below_old
    {P N r inside shadow upper x v : ZFSet.{u}} (hv : v ∈ P) :
    ZFSet.pair x v ∈ codedAttachmentOrder P N r inside shadow upper ↔
      (x ∈ P ∧ ZFSet.pair x v ∈ r) ∨
        ∃ q ∈ N, x = ZFSet.pair P q ∧ ZFSet.pair q v ∈ upper := by
  rw [pair_mem_codedAttachmentOrder]
  constructor
  · rintro ⟨_, _, old | oldFresh | freshOld | freshFresh⟩
    · exact Or.inl ⟨old.1, old.2.2⟩
    · obtain ⟨_, q, _, _, _, equal, _⟩ := oldFresh
      exact False.elim (pair_tag_not_mem P q (equal ▸ hv))
    · exact Or.inr freshOld.2
    · obtain ⟨_, _, t, _, _, equal, _⟩ := freshFresh
      exact False.elim (pair_tag_not_mem P t (equal ▸ hv))
  · rintro (⟨hx, lower⟩ | ⟨q, hq, rfl, upperEntry⟩)
    · exact ⟨old_mem_taggedExtension hx, old_mem_taggedExtension hv, Or.inl ⟨hx, hv, lower⟩⟩
    · exact ⟨pair_mem_taggedExtension.2 hq, old_mem_taggedExtension hv,
        Or.inr (Or.inr (Or.inl ⟨hv, q, hq, rfl, upperEntry⟩))⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundEligibleBatchAction_agreement
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv e g h v : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv e) (action : PosetActionCode G P m e r A)
    (meet : MeetOrderCode P r μ) (hg : g ∈ G) (hh : h ∈ G) (hv : v ∈ P)
    (agree : ActionAgreementBelow P r A g h v) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ActionAgreementBelow d.batchCarrier d.batchOrder (M.groundEligibleBatchAction P G r μ A Labels) g h v := by
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let B := M.groundEligibleBatchAction P G r μ A Labels
  have full := M.groundEligibleBatchAction_code (Labels := Labels)
    pairing unions powers separation hP hG hA group action meet
  have fresh := M.groundEligibleFreshAction_setAction (Labels := Labels)
    pairing unions powers separation hP hG hA group action meet
  have outputs {x y z : ZFSet.{u}} (lower : ZFSet.pair x v ∈ d.batchOrder)
      (first : ZFSet.pair (ZFSet.pair g x) y ∈ B)
      (second : ZFSet.pair (ZFSet.pair h x) z ∈ B) : y = z := by
    rcases (codedAttachmentOrder_below_old hv).1 lower with ⟨hx, below⟩ | ⟨q, _, rfl, upper⟩
    · exact agree.entry_eq action hh hx below
        ((M.groundEligibleBatchAction_old_iff hx).1 first)
        ((M.groundEligibleBatchAction_old_iff hx).1 second)
    · obtain ⟨q', _, rfl, firstFresh⟩ :=
        (taggedActionGraph_fresh_iff action.toSetAction fresh).1 first
      obtain ⟨q'', _, rfl, secondFresh⟩ :=
        (taggedActionGraph_fresh_iff action.toSetAction fresh).1 second
      exact congrArg (ZFSet.pair P)
        (M.groundEligibleFreshAction_positive_agreement group action meet agree firstFresh secondFresh upper)
  change ActionAgreementBelow d.batchCarrier d.batchOrder B g h v
  intro x hx y _ lower
  constructor
  · intro first
    obtain ⟨z, second, _⟩ := full.function.2 (ZFSet.pair h x) (ZFSet.pair_mem_prod.2 ⟨hh, hx⟩)
    exact (outputs lower first second).symm ▸ second
  · intro second
    obtain ⟨z, first, _⟩ := full.function.2 (ZFSet.pair g x) (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
    exact outputs lower first second ▸ first

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_InitialRepresentativeAgreement
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem RestrictedActionCode.base_action_iff
    {P G m one r A g source target base x y : ZFSet.{u}}
    (code : RestrictedActionCode P r A g source target base)
    (action : PosetActionCode G P m one r A) (hx : x ∈ P)
    (below : ZFSet.pair x source ∈ r) :
    ZFSet.pair x y ∈ base ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A := by
  constructor
  · intro entry
    have hy := (ZFSet.pair_mem_prod.1 (code.shape entry)).2
    exact ((code.entries x hx y hy).1 entry).2
  · intro entry
    have hy := (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2
    exact (code.entries x hx y hy).2 ⟨below, entry⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem groundEligibleTask_representative_base_iff
    {P G r μ A Labels m inv one i g a x y : ZFSet.{u}}
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ)
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (represented : TaskRepresentative P r A (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels i g)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (hx : x ∈ P) (below : ZFSet.pair x a ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    ZFSet.pair x y ∈ batchTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) i ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  obtain ⟨a', ha, c, hc, base, hb, s, hs, F, hF, label, hl, equal, restriction⟩ := represented
  have aEq : a = a' := ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 (equal ▸ source)).2
  have anchorEq : d.anchor j = a := d.anchors.unique (d.anchor_entry j) source
  have relEq : d.rel j = r := ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry j)).2
  have baseEntry : ZFSet.pair i base ∈ literalTaskBaseGraph I P
      (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels := by
    rw [equal]
    exact (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).2 ⟨equal ▸ hi, rfl⟩
  have baseEq : d.embed j = base := d.embeddings.unique (d.embed_entry j) baseEntry
  have notFresh : x ∉ freshPart (d.space j) (d.rel j) (d.anchor j) := by
    intro fresh
    exact ((mem_freshPart _ _ _ _).1 fresh).2 (relEq.symm ▸ anchorEq.symm ▸ below)
  rw [M.groundEligibleBatchAction_old_iff hx]
  rw [pair_mem_batchTemplateGraph]
  change (ZFSet.pair (ZFSet.pair j.val x) y ∈ _ ↔ _)
  rw [d.batch_template_entry_iff, baseEq]
  have onlyBase : (ZFSet.pair x y ∈ base ∨
      x ∈ freshPart (d.space j) (d.rel j) (d.anchor j) ∧
        y = ZFSet.pair P (ZFSet.pair j.val x)) ↔ ZFSet.pair x y ∈ base :=
    ⟨fun h => h.elim id (fun h => False.elim (notFresh h.1)), Or.inl⟩
  exact onlyBase.trans (restriction.base_action_iff action hx (aEq ▸ below))

theorem exists_groundInitialRepresentatives
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Qs := constantFamilyGraph I P
    let rs := constantFamilyGraph I r
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P Qs rs As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    let B := M.groundEligibleBatchAction P G r μ A Labels
    Maps ∈ M.sets ∧ FunctionGraphOn I Maps ∧
      (∀ i S, ZFSet.pair i S ∈ Maps →
        MeetEmbeddingCode P d.batchCarrier r d.batchOrder μ d.batchMeetGraph S) ∧
      B ∈ M.sets ∧ PosetActionCode G d.batchCarrier m one d.batchOrder B ∧
      ∃ representatives ∈ M.sets, ZFSet.IsFunc I G representatives ∧
        (∀ i g, ZFSet.pair i g ∈ representatives → TaskRepresentative P r A R U Labels i g) ∧
        (∀ i a g S x y, ZFSet.pair i a ∈ As → ZFSet.pair i g ∈ representatives →
          ZFSet.pair i S ∈ Maps → x ∈ P → ZFSet.pair x a ∈ r →
            (ZFSet.pair x y ∈ S ↔ ZFSet.pair (ZFSet.pair g x) y ∈ B)) := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨hMaps, maps, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  obtain ⟨representatives, ground, function, represents, _⟩ :=
    M.exists_groundTaskRepresentatives pairing unions powers separation choice
      hP hG hr hμ hA hLabels meet
  refine ⟨hMaps, maps, ?_,
    M.groundEligibleBatchAction_mem pairing unions powers separation hP hG hr hμ hA hLabels meet,
    M.groundEligibleBatchAction_code pairing unions powers separation hP hG hA group action meet,
    representatives, ground, function, represents, ?_⟩
  · intro i S entry
    obtain ⟨hi, equal⟩ := (entries i S).1 entry
    let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
    have spaceEq : d.space j = P := ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry j)).2
    have relEq : d.rel j = r := ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry j)).2
    have meetEq : d.meet j = μ := ((pair_mem_constantFamilyGraph I μ _ _).1 (d.meet_entry j)).2
    rw [equal]
    simpa only [spaceEq, relEq, meetEq] using d.batch_template_embedding_code j
  · intro i a g S x y source representative mapEntry hx below
    obtain ⟨hi, equal⟩ := (entries i S).1 mapEntry
    rw [equal]
    exact M.groundEligibleTask_representative_base_iff group action meet hi
      (represents i g representative) source hx below

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RepresentativeProductAgreement
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem TaskTransportCode.representative_product_agreement
    {P R U Labels A δ i j G m one r g h k I a : ZFSet.{u}}
    (transport : TaskTransportCode P R U Labels A δ i j)
    (action : PosetActionCode G P m one r A)
    (hδ : δ ∈ G) (hg : g ∈ G) (hk : k ∈ G)
    (product : ZFSet.pair (ZFSet.pair δ g) k ∈ m)
    (first : TaskRepresentative P r A R U Labels i g)
    (second : TaskRepresentative P r A R U Labels j h)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph I P R U Labels) :
    ActionAgreementBelow P r A k h a := by
  obtain ⟨a', ha, c, hc, base, hb, s, hs, F, hF, label, hl,
    c', _, base', _, s', _, F', _, old, new, target, _, baseEq, _⟩ := transport
  have aEq : a = a' :=
    ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 (old ▸ source)).2
  have oldRestriction := (old ▸ first).restriction
  have newRestriction := (new ▸ second).restriction
  have composed := oldRestriction.transport action hg hδ hk product target
  rw [baseEq] at newRestriction
  intro x hx y _ lower
  exact (composed.base_action_iff action hx (aEq ▸ lower)).symm.trans
    (newRestriction.base_action_iff action hx (aEq ▸ lower))

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_InitialRecursiveTaskLaws
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

theorem groundInitialMap_cap_base
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one T i S a c : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hT : T ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ As →
      ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
      ZFSet.IsFunc P d.batchCarrier S ∧
        ZFSet.pair T (eligibleTaskCap P T i) ∈ S ∧ ZFSet.pair a c ∈ S := by
  dsimp only
  intro mapEntry source target
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨_, _, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  obtain ⟨hi, mapEq⟩ := (entries i S).1 mapEntry
  rw [mapEq]
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have spaceEq : d.space j = P := ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry j)).2
  have function : ZFSet.IsFunc P d.batchCarrier
      (batchTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r)
        (literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
        (literalTaskBaseGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) i) := by
    simpa only [spaceEq] using d.batch_template_fiber_function j
  refine ⟨function, (pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).2
    (M.groundEligibleTask_cap_entry group action meet hT top hi), ?_⟩
  obtain ⟨a', ha, c', hc, base, hb, s, hs, F, hF, label, hl, equal, code⟩ :=
    (mem_eligibleTaskSet P G r μ A _ _ Labels i).1 hi
  have aEq : a = a' :=
    ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 0).1 (equal ▸ source)).2
  have cEq : c = c' :=
    ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 1).1 (equal ▸ target)).2
  have baseEntry : ZFSet.pair i base ∈ literalTaskBaseGraph I P
      (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels := by
    rw [equal]
    exact (literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 2).2 ⟨equal ▸ hi, rfl⟩
  have baseEq : d.embed j = base := d.embeddings.unique (d.embed_entry j) baseEntry
  obtain ⟨g, _, represented⟩ := code.representative
  have entry : ZFSet.pair a' c' ∈ base :=
    (represented.entries a' ha c' hc).2 ⟨meet.order.refl a' ha, represented.target_entry⟩
  rw [aEq, cEq]
  exact (d.batch_template_old_agreement j (baseEq.symm ▸ entry)).1

theorem groundInitialMap_negative_cap
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one T i S a c F K b v w : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hT : T ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x T ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ As →
      ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
      ZFSet.pair i F ∈ literalTaskFilterGraph I P R U Labels →
      ZFSet.pair T K ∈ S → ZFSet.pair a b ∈ S → v ∈ P → v ∉ F →
      ZFSet.pair (ZFSet.pair K v) w ∈ d.batchMeetGraph → ZFSet.pair w b ∈ d.batchOrder := by
  dsimp only
  intro mapEntry source target filter cap base hv negative entry
  obtain ⟨function, capEntry, baseEntry⟩ := M.groundInitialMap_cap_base
    pairing unions powers separation hP hG hr hμ hA hLabels group action meet hT top
    mapEntry source target
  obtain ⟨_, _, uniqueCap⟩ := function.2 T hT
  have capEq : K = eligibleTaskCap P T i :=
    (uniqueCap K cap).trans (uniqueCap _ capEntry).symm
  have sourceShape := (ZFSet.mem_sep.1 source).1
  have ha := (ZFSet.pair_mem_prod.1 sourceShape).2
  obtain ⟨_, _, uniqueBase⟩ := function.2 a ha
  have baseEq : b = c := (uniqueBase b base).trans (uniqueBase c baseEntry).symm
  have hi := (ZFSet.pair_mem_prod.1 sourceShape).1
  exact baseEq.symm ▸ (M.groundEligibleTask_negative_cap group action meet hT top hi
    target filter hv negative (capEq ▸ entry)).2.2

theorem groundInitialTask_source
    {P G r μ A Labels δ i j a b : ZFSet.{u}}
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels)
    (first : ZFSet.pair i a ∈ literalTaskSourceGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels)
    (second : ZFSet.pair j b ∈ literalTaskSourceGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels) : a = b := by
  have transport := ((triple_mem_taskTransportGraph G
    (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
    (M.groundMeetFilters P r μ) Labels A δ i j).1 task).2.2.2
  exact transport.source_eq first second

theorem groundInitialTask_intertwine
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one δ i j S S' q x y : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ)
    (task : ZFSet.pair (ZFSet.pair δ i) j ∈ M.groundTaskTransport P G r μ A Labels) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
      (constantFamilyGraph I r) (literalTaskSourceGraph I P R U Labels)
      (literalTaskBaseGraph I P R U Labels)
    ZFSet.pair i S ∈ Maps → ZFSet.pair j S' ∈ Maps →
      ZFSet.pair q x ∈ S → ZFSet.pair q y ∈ S' →
      ZFSet.pair (ZFSet.pair δ x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
  dsimp only
  intro first second image image'
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨_, _, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  have firstEq := ((entries i S).1 first).2
  have secondEq := ((entries j S').1 second).2
  exact M.groundEligibleBatchAction_equivariant group action meet task
    (firstEq ▸ image) (secondEq ▸ image')

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_InitialRecursiveActionAgreement
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

theorem groundInitialTaskAction
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
      (constantFamilyGraph I r) As (literalTaskBaseGraph I P R U Labels)
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    let B := M.groundEligibleBatchAction P G r μ A Labels
    ∀ Reps (h : CodedRecursiveMapInputs d I Maps As Reps G m inv one B),
      CodedRecursiveTaskAction h (M.groundTaskTransport P G r μ A Labels) := by
  dsimp only
  intro Reps h
  refine ⟨M.groundTaskTransport_setAction pairing unions powers separation hP hG hA
    group action meet, ?_, ?_⟩
  · intro g i j a b task first second
    exact M.groundInitialTask_source task first second
  · intro g i j S S' q x y task first second image image'
    exact M.groundInitialTask_intertwine pairing unions powers separation hP hG hr hμ hA hLabels
      group action meet task first second image image'

theorem groundInitialTask_positive_agreement
    {P G r μ A Labels m inv one g h v i i' i'' F : ZFSet.{u}}
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (agree : ActionAgreementBelow P r A g h v)
    (filter : ZFSet.pair i F ∈ literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (positive : v ∈ F)
    (first : ZFSet.pair (ZFSet.pair g i) i' ∈ M.groundTaskTransport P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair h i) i'' ∈ M.groundTaskTransport P G r μ A Labels) :
    i' = i'' := by
  have hi := ((triple_mem_taskTransportGraph G _ P _ _ Labels A g i i').1 first).2.1
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F', hF, label, hl, equal, _⟩ :=
    (mem_eligibleTaskSet P G r μ A _ _ Labels i).1 hi
  have filterEq : F = F' :=
    ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 4).1 (equal ▸ filter)).2
  exact M.groundTaskTransport_positive_agreement group action meet agree
    (filterEq ▸ positive) (equal ▸ first) (equal ▸ second)

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_RecursiveStateFieldEnvironments
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing

universe u

namespace RecursiveStateData

theorem field_injective : Function.Injective field.{u} := by
  intro first second equal
  cases first
  cases second
  congr 1
  · exact congrFun equal (0 : Fin 13)
  · exact congrFun equal (1 : Fin 13)
  · exact congrFun equal (2 : Fin 13)
  · exact congrFun equal (3 : Fin 13)
  · exact congrFun equal (4 : Fin 13)
  · exact congrFun equal (5 : Fin 13)
  · exact congrFun equal (6 : Fin 13)
  · exact congrFun equal (7 : Fin 13)
  · exact congrFun equal (8 : Fin 13)
  · exact congrFun equal (9 : Fin 13)
  · exact congrFun equal (10 : Fin 13)
  · exact congrFun equal (11 : Fin 13)
  · exact congrFun equal (12 : Fin 13)

theorem code_injective : Function.Injective code.{u} := by
  intro first second equal
  exact field_injective (nonemptyTupleCode_injective 12 equal)

end RecursiveStateData

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem recursiveStateData_code_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (state : RecursiveStateData.{u}) (ground : ∀ j, state.field j ∈ M.sets) :
    state.code ∈ M.sets := M.nonemptyTupleCode_mem pairing 12 state.field ground

theorem recursiveStateData_field_mem (state : RecursiveStateData.{u})
    (ground : state.code ∈ M.sets) : ∀ j, state.field j ∈ M.sets :=
  M.nonemptyTupleCode_field_mem 12 state.field ground

theorem recursiveStateCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {D rD μD J Qs rs μs As Es Fs Ss Maps A : ZFSet.{u}}
    (hD : D ∈ M.sets)
    (hrD : rD ∈ M.sets)
    (hμD : μD ∈ M.sets)
    (hJ : J ∈ M.sets)
    (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets)
    (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets)
    (hEs : Es ∈ M.sets)
    (hFs : Fs ∈ M.sets)
    (hSs : Ss ∈ M.sets)
    (hMaps : Maps ∈ M.sets)
    (hA : A ∈ M.sets)
    : recursiveStateCode D rD μD J Qs rs μs As Es Fs Ss Maps A ∈ M.sets :=
  M.recursiveStateData_code_mem pairing ⟨D, rD, μD, J, Qs, rs, μs, As, Es, Fs, Ss, Maps, A⟩
    (Fin.cases hD (Fin.cases hrD (Fin.cases hμD (Fin.cases hJ (Fin.cases hQs (Fin.cases hrs (Fin.cases hμs (Fin.cases hAs (Fin.cases hEs (Fin.cases hFs (Fin.cases hSs (Fin.cases hMaps (Fin.cases hA ((fun i => Fin.elim0 i)))))))))))))))

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.RecursiveStateData
universe u

theorem ofFields_field (state : RecursiveStateData.{u}) : ofFields state.field = state := by
  cases state
  rfl

theorem field_ofFields (fields : Fin 13 → ZFSet.{u}) : (ofFields fields).field = fields := by
  funext j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  refine Fin.cases rfl (fun j => ?_) j
  exact Fin.elim0 j

theorem code_ofFields (fields : Fin 13 → ZFSet.{u}) :
    (ofFields fields).code = nonemptyTupleCode 12 fields := by
  rw [code, field_ofFields]

theorem successorCodeFromEnvironment_spec (state : RecursiveStateData.{u})
    (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u}) :
    successorCodeFromEnvironment M (state.successorEnvironment I Sources Reps G T) =
      (state.successor M I Sources Reps G T).code := by
  simp only [successorCodeFromEnvironment, successorEnvironment, Fin.addCases_left]
  rw [ofFields_field]
  rfl

end PartitionPilot.Forcing.RecursiveStateData

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_InitialCompressionAccounting
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

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem code_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    state.data.code ∈ M.sets := by
  rw [← state.inputs_toState]
  exact M.recursiveStateCode_mem pairing state.ground.carrier state.ground.order
    state.ground.meet state.ground.indices state.ground.spaces state.ground.relations
    state.ground.meets state.ground.anchors state.ground.embeddings state.ground.filters
    state.ground.separators state.ground.maps state.ground.action

end GroundCompressionState

end

section
universe u

namespace CodedRecursiveMapInputs
variable {P0 τ D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable (h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

theorem accounting_next
    (entries : ∀ i f, ZFSet.pair i f ∈ h.groundLiftFamily M next ↔ i ∈ I ∧ f = h.liftSection M next i)
    (inputs : CodedRecursiveMapInputs next I (h.groundLiftFamily M next) Sources Reps
      G m inv one (h.nextActionGraph T))
    (hτ : τ ∈ D) (top : ∀ x ∈ D, ZFSet.pair x τ ∈ rD)
    (accounted : FiniteCompressionAccounting P0 I Sources τ h.toState) :
    FiniteCompressionAccounting P0 I Sources τ inputs.toState := by
  intro x hx
  change x ∈ next.batchCarrier at hx
  obtain ⟨X, rfl⟩ := h.nextEncode_surjective M next x hx
  cases X with
  | inl X =>
    rw [h.nextEncode_old]
    rcases accounted (d.coding.encode X) (d.coding.encode_mem X) with original | accounted
    · exact Or.inl original
    · obtain ⟨i, hi, S, a, k, b, y, hy, indexed, source, cap, base, image, lower, outside⟩ := accounted
      have function := (h.valid i S indexed).injection.function
      have ha := (ZFSet.pair_mem_prod.1 (h.sources.1 source)).2
      have hk := (ZFSet.pair_mem_prod.1 (function.1 cap)).2
      have hb := (ZFSet.pair_mem_prod.1 (function.1 base)).2
      refine Or.inr ⟨i, hi, h.liftSection M next i, a, k, b, y,
        old_mem_taggedExtension hy, (entries _ _).2 ⟨hi, rfl⟩, source,
        (h.liftSection_old_iff M next indexed hτ).2 cap,
        (h.liftSection_old_iff M next indexed ha).2 base,
        (h.liftSection_old_iff M next indexed hy).2 image, ?_, ?_⟩
      · exact (next.old_order_iff (d.coding.encode_mem X) hk).2 lower
      · exact fun nextLower => outside ((next.old_order_iff (d.coding.encode_mem X) hb).1 nextLower)
  | inr q =>
    obtain ⟨i, y, image, below, outside⟩ := h.toInputs.fresh_accounting
      ⟨τ, hτ⟩ (fun x => top x.val x.property) q
    let S := h.maps.value i
    let k := d.coding.encode ((h.toInputs.previous i).toFun ⟨τ, hτ⟩)
    let b := d.coding.encode ((h.toInputs.previous i).toFun (h.toInputs.source i))
    have indexed : ZFSet.pair i.val S ∈ Maps := h.maps.value_entry i
    have cap : ZFSet.pair τ k ∈ S := h.toInputs_previous_entry i ⟨τ, hτ⟩
    have base : ZFSet.pair (h.source i).val b ∈ S :=
      h.toInputs_previous_entry i (h.source i)
    refine Or.inr ⟨i.val, i.property, h.liftSection M next i.val, (h.source i).val, k, b,
      d.coding.encode y, d.coding.encode_mem y,
      (entries _ _).2 ⟨i.property, rfl⟩, h.source_entry i,
      (h.liftSection_old_iff M next indexed hτ).2 cap,
      (h.liftSection_old_iff M next indexed (h.source i).property).2 base, ?_, ?_, ?_⟩
    · have lifted := h.liftSection_entry M next i y
      exact image ▸ lifted
    · exact (h.next_le_encode M next (.inr q) (.inl ((h.toInputs.previous i).toFun ⟨τ, hτ⟩))).2 below
    · exact fun lower => outside ((h.next_le_encode M next (.inr q)
        (.inl ((h.toInputs.previous i).toFun (h.toInputs.source i)))).1 lower)

end CodedRecursiveMapInputs

end

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialCompressionInvariant
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Sources := literalTaskSourceGraph I P R U Labels
    let Filters := literalTaskFilterGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
      (constantFamilyGraph I r) Sources (literalTaskBaseGraph I P R U Labels)
    let B := M.groundEligibleBatchAction P G r μ A Labels
    let T := M.groundTaskTransport P G r μ A Labels
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ Maps ∈ M.sets ∧
      B ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ inputs : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one B,
          RecursiveCompressionInvariant seed inputs ∧ CodedRecursiveTaskAction inputs T := by
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let Sources := literalTaskSourceGraph I P R U Labels
  let Filters := literalTaskFilterGraph I P R U Labels
  let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
    (constantFamilyGraph I r) Sources (literalTaskBaseGraph I P R U Labels)
  let B := M.groundEligibleBatchAction P G r μ A Labels
  let T := M.groundTaskTransport P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, _, _, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨hMaps, maps, valid, hB, currentAction,
    Reps, hReps, reps, represents, agreement⟩ :=
    M.exists_groundInitialRepresentatives pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet
  let inputs : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one B :=
    ⟨maps, (fields 0).2, reps, group, currentAction, valid, agreement⟩
  have seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters := by
    refine ⟨meet, action, hτ, (fields 0).2, ⟨_, (fields 4).2⟩, ?_, ?_⟩
    · intro δ i j g k product a transport source firstRep secondRep productEntry
      have transported := (triple_mem_taskTransportGraph G I P R U Labels A δ i j).1 transport
      have hg := (ZFSet.pair_mem_prod.1 (reps.1 firstRep)).2
      have hp := (ZFSet.pair_mem_prod.1 (group.mul_function.1 productEntry)).2
      exact transported.2.2.2.representative_product_agreement action transported.1 hg hp
        productEntry (represents i g firstRep) (represents j k secondRep) source
    · intro g k v i j l F oldAgree filter positive first second
      exact M.groundInitialTask_positive_agreement group action meet oldAgree filter positive first second
  have invariant : RecursiveCompressionInvariant seed inputs := by
    refine ⟨fun _ hx => hx, fun _ _ _ _ => Iff.rfl, fun _ _ _ _ _ => Iff.rfl,
      ?_, top, ?_, ?_⟩
    · intro g x hx y
      exact M.groundEligibleBatchAction_old_iff hx
    · intro g hg k hk v hv oldAgree
      exact M.groundEligibleBatchAction_agreement pairing unions powers separation
        hP hG hA group action meet hg hk hv oldAgree
    · intro i S a F cap base v w mapEntry source filter capEntry baseEntry hv negative entry
      have hi := inputs.maps.pair_source mapEntry
      obtain ⟨a', ha, c, hc, ell, hell, sep, hsep, F', hF, label, hl, equal, _⟩ :=
        (mem_eligibleTaskSet P G r μ A R U Labels i).1 hi
      have target : ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels := by
        rw [equal]
        exact (literalTaskFieldGraph_entry_iff ha hc hell hsep hF hl 1).2 ⟨equal ▸ hi, rfl⟩
      exact M.groundInitialMap_negative_cap pairing unions powers separation
        hP hG hr hμ hA hLabels group action meet hτ top mapEntry source target filter
        capEntry baseEntry hv negative entry
  exact ⟨hI, (fields 0).1, (fields 4).1, hMaps, hB,
    M.groundTaskTransport_mem pairing unions powers separation hP hG hr hμ hA hLabels meet,
    Reps, hReps, seed, inputs, invariant,
    M.groundInitialTaskAction pairing unions powers separation hP hG hr hμ hA hLabels
      group action meet Reps inputs⟩

theorem exists_groundInitialCompressionState
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Sources := literalTaskSourceGraph I P R U Labels
    let Filters := literalTaskFilterGraph I P R U Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ G ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ state : GroundCompressionState M seed,
          state.data = M.initialCompressionData P G r μ A Labels := by
  obtain ⟨hI, hSources, hFilters, hMaps, hB, hT, Reps, hReps, seed, inputs, invariant, task⟩ :=
    M.exists_groundInitialCompressionInvariant pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  obtain ⟨_, hQs, hrs, hμs, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  have ground : RecursiveGroundFields M inputs :=
    ⟨hP, hr, hμ, hI, hQs, hrs, hμs, hSources, (fields 2).1, hFilters,
      (fields 3).1, hMaps, hB⟩
  let state : GroundCompressionState M seed :=
    ⟨inputs.toState, _, inputs, task, invariant, ground⟩
  exact ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, state, rfl⟩

end TransitiveGround

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem initialCompressionData_accounting
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels
    FiniteCompressionAccounting P I Sources τ (M.initialCompressionData P G r μ A Labels) := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let Sources := literalTaskSourceGraph I P (M.groundRelations P P)
    (M.groundMeetFilters P r μ) Labels
  let Es := literalTaskBaseGraph I P (M.groundRelations P P)
    (M.groundMeetFilters P r μ) Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  obtain ⟨hI, hQs, hrs, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels meet
  obtain ⟨_, _, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs (fields 0).1 (fields 2).1
  intro x hx
  change x ∈ d.batchCarrier at hx
  obtain ⟨X, rfl⟩ := d.coding.encode_surjective x hx
  cases X with
  | inl p => exact Or.inl p.property
  | inr q =>
    let i := q.1
    let S := batchTemplateGraph I P (constantFamilyGraph I P) (constantFamilyGraph I r) Sources Es i.val
    have spaceEq : d.space i = P :=
      ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry i)).2
    have relEq : d.rel i = r :=
      ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry i)).2
    have function : ZFSet.IsFunc P d.batchCarrier S := by
      simpa only [spaceEq] using d.batch_template_fiber_function i
    have anchorP : d.anchor i ∈ P := by
      simpa only [spaceEq] using (d.fiber i).anchor_mem
    obtain ⟨k, cap, _⟩ := function.2 τ hτ
    obtain ⟨b, base, _⟩ := function.2 (d.anchor i) anchorP
    have image : ZFSet.pair q.2.val.val (d.coding.encode (.inr q)) ∈ S := by
      apply (pair_mem_batchTemplateGraph _ _ _ _ _ _ _ _ _).2
      apply (d.batch_template_entry_iff i _ _).2
      exact Or.inr ⟨(mem_freshPart _ _ _ _).2 ⟨q.2.val.property, q.2.property⟩, rfl⟩
    have pointP : q.2.val.val ∈ P := by
      have member : q.2.val.val ∈ d.space i := q.2.val.property
      simpa only [spaceEq] using member
    refine Or.inr ⟨i.val, i.property, S, d.anchor i, k, b, q.2.val.val, pointP,
      (entries _ _).2 ⟨i.property, rfl⟩, d.anchor_entry i, cap, base, image, ?_, ?_⟩
    · exact (d.batch_template_order_iff i image cap).2 (relEq.symm ▸ top _ pointP)
    · intro lower
      exact q.2.property ((d.batch_template_order_iff i image base).1 lower)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialCompressionHistory
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

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)

include pairing unions powers separation hI hSources hReps hG hT in
theorem canonical_iterate_code_mem (n : Nat) :
    (state.data.iterate M I Sources Reps G T n).code ∈ M.sets := by
  rw [← state.iterate_data pairing unions powers separation hI hSources hReps hG hT n]
  exact (state.iterate pairing unions powers separation hI hSources hReps hG hT n).code_mem pairing

end GroundCompressionState
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_decodedSuccessorFormula
    (definition : GroundDefinableFunction M (RecursiveStateData.successorCodeFromEnvironment M))
    (params : Fin 5 → ZFSet.{u}) (members : ∀ i, params i ∈ M.sets)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets (decodedSuccessorFormula definition.formula) (extend x (extend y params)) ↔
      ∃ fields : Fin 13 → ZFSet.{u}, (∀ i, fields i ∈ M.sets) ∧
        x = nonemptyTupleCode 12 fields ∧
        y = RecursiveStateData.successorCodeFromEnvironment M
          (Fin.addCases (m := 13) (n := 5) fields params) := by
  rw [decodedSuccessorFormula, realize_exBlock]
  apply exists_congr
  intro fields
  apply and_congr_right
  intro hfields
  have henv : ∀ i, extendMany 13 fields (extend x (extend y params)) i ∈ M.sets :=
    extendMany_members 13 fields _ hfields (Fin.cases hx (Fin.cases hy members))
  change (Realize M.sets (BoundedFormula.nonemptyTupleFormula 12
      (suffixIndex 7 13 0) (prefixIndex 7 13)).toFormula _ ∧ _) ↔ _
  rw [BoundedFormula.realize_toFormula M _ _ henv, BoundedFormula.truth_nonemptyTupleFormula,
    realize_reindex, map_extend]
  have fieldsEqual : (fun i => extendMany 13 fields (extend x (extend y params))
      (prefixIndex 7 13 i)) = fields := by
    funext i
    exact extendMany_prefix 13 fields _ i
  have envEqual : (fun i => extendMany 13 fields (extend x (extend y params))
      (Fin.addCases (m := 13) (n := 5) (prefixIndex 7 13)
        (fun j => suffixIndex 7 13 j.succ.succ) i)) =
      Fin.addCases (m := 13) (n := 5) fields params := by
    funext i
    refine Fin.addCases (m := 13) (n := 5) (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.addCases_left]
      exact extendMany_prefix 13 fields _ j
    · simp only [Fin.addCases_right]
      exact extendMany_suffix 13 fields _ j.succ.succ
  rw [fieldsEqual, envEqual, extendMany_suffix, extendMany_suffix]
  change (x = nonemptyTupleCode 12 fields ∧
    Realize M.sets definition.formula
      (extend y (Fin.addCases (m := 13) (n := 5) fields params))) ↔ _
  rw [definition.correct _ (fun i =>
    Fin.addCases (m := 13) (n := 5)
      (fun j => by simpa only [Fin.addCases_left] using hfields j)
      (fun j => by simpa only [Fin.addCases_right] using members j) i) y hy]

theorem realize_recursiveSuccessorCode
    (definition : GroundDefinableFunction M (RecursiveStateData.successorCodeFromEnvironment M))
    (state : RecursiveStateData.{u}) (hstate : state.code ∈ M.sets)
    {I Sources Reps G T y : ZFSet.{u}}
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) (hy : y ∈ M.sets) :
    Realize M.sets (decodedSuccessorFormula definition.formula)
      (extend state.code (extend y (extend I (extend Sources
        (extend Reps (extend G (extend T Fin.elim0))))))) ↔
      y = (state.successor M I Sources Reps G T).code := by
  rw [M.realize_decodedSuccessorFormula definition _
    (Fin.cases hI (Fin.cases hSources (Fin.cases hReps (Fin.cases hG (Fin.cases hT
      (fun i => Fin.elim0 i)))))) hstate hy]
  constructor
  · rintro ⟨fields, _, code, next⟩
    have equal : RecursiveStateData.ofFields fields = state :=
      RecursiveStateData.code_injective ((RecursiveStateData.code_ofFields fields).trans code.symm)
    have fieldsEqual : fields = state.field := by
      rw [← RecursiveStateData.field_ofFields fields, equal]
    rw [fieldsEqual] at next
    exact next.trans (state.successorCodeFromEnvironment_spec M I Sources Reps G T)
  · intro next
    refine ⟨state.field, M.recursiveStateData_field_mem state hstate, rfl, ?_⟩
    exact next.trans (state.successorCodeFromEnvironment_spec M I Sources Reps G T).symm

end TransitiveGround
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundHistory
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    let φ := M.compressionSuccessorFormula pairing unions powers separation
    let params := extend state.data.code
      (extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0)))))
    ∃ history ∈ M.sets,
      OrdinalRecursionTrace (groundRecursionStep M (naturalStepFormula φ) params) ZFSet.omega history ∧
      (∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔
        y = (state.data.iterate M I Sources Reps G T n).code) ∧
      (∀ other, OrdinalRecursionTrace (groundRecursionStep M (naturalStepFormula φ) params)
        ZFSet.omega other → other = history) ∧
      ∀ n, ∃ current : GroundCompressionState M seed,
        current.data = state.data.iterate M I Sources Reps G T n := by
  dsimp only
  let φ := M.compressionSuccessorFormula pairing unions powers separation
  let params := extend I (extend Sources (extend Reps (extend G (extend T Fin.elim0))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hI (Fin.cases hSources (Fin.cases hReps (Fin.cases hG
      (Fin.cases hT (fun i => Fin.elim0 i)))))
  let value (n : Nat) := (state.data.iterate M I Sources Reps G T n).code
  have values : ∀ n, value n ∈ M.sets :=
    state.canonical_iterate_code_mem pairing unions powers separation hI hSources hReps hG hT
  have nextValue : ∀ n y, y ∈ M.sets →
      (Realize M.sets φ (extend (value n) (extend y params)) ↔ y = value (n + 1)) := by
    intro n y hy
    exact M.realize_recursiveSuccessorCode
      (M.definable_recursiveSuccessorCode pairing unions powers separation)
      (state.data.iterate M I Sources Reps G T n) (values n) hI hSources hReps hG hT hy
  obtain ⟨history, hh, trace, entries, unique⟩ :=
    M.exists_definableNaturalHistory φ params members value values nextValue
      pairing unions separation collection infinite
  exact ⟨history, hh, trace, entries, unique,
    state.canonical_iterate_valid pairing unions powers separation hI hSources hReps hG hT⟩

end GroundCompressionState
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionHeightSteps
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open Compression.RecursiveMaps
universe u

namespace BoundedFormula

theorem truth_lexHeightEntryFormula {n} (z C D rD : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (lexHeightEntryFormula z C D rD) env ↔
      ∃ c ∈ env C, ∃ q ∈ env D, ∃ d ∈ env C, ∃ v ∈ env D,
        env z = ZFSet.pair (ZFSet.pair c q) (ZFSet.pair d v) ∧
          (c ∈ d ∨ (c = d ∧ ZFSet.pair q v ∈ env rD)) := by
  simp only [lexHeightEntryFormula, truth_exMem, Truth, truth_disj,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem lexHeightOrder_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {C D rD : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    lexHeightOrder C D rD ∈ M.sets := by
  have carrier := M.prod_mem pairing unions powers separation hC hD
  let params := extend C (extend D (extend rD Fin.elim0))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.lexHeightEntryFormula 0 1 2 3) params
    (Fin.cases hC (Fin.cases hD (Fin.cases hrD (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation carrier carrier)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.lexHeightEntryFormula 0 1 2 3) (extend z params))
      (ZFSet.prod (ZFSet.prod C D) (ZFSet.prod C D)) = lexHeightOrder C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, lexHeightOrder, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_lexHeightEntryFormula 0 1 2 3 _)
  exact equal ▸ selected

end TransitiveGround






theorem batchHeightGraph_old_entry {P I Qs rs As Vs Hs Cs E C D old x h : ZFSet.{u}}
    (hx : x ∈ P) :
    ZFSet.pair x h ∈ batchHeightGraph P I Qs rs As Vs Hs Cs E C D old ↔ ZFSet.pair x h ∈ old :=
  taggedHeightGraph_old_entry hx

namespace TemplateHeightFamilyInputs

variable {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D rD old Cs los his E : ZFSet.{u}}
  {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
  (t : TemplateHeightFamilyInputs d Vs vrs Hs)
  (e : BatchHeightEndpointCode d C D old rD Cs los his)
  (embeddings : FunctionGraphOn I E)
  (maps : ∀ i, IntervalEmbeddingCode (t.ranges.value i) D (t.orders.value i) rD
    (e.low i) (e.high i) (embeddings.value i))

include t e embeddings maps

theorem batch_fresh_function :
    ZFSet.IsFunc (indexedAttachmentFresh I Qs rs As) (ZFSet.prod C D)
      (batchFreshHeightGraph I Qs rs As Vs Hs Cs E C D) := by
  have full := t.batch_component_function e embeddings maps
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_⟩
  intro x hx
  obtain ⟨y, entry, unique⟩ := full.2 x (indexedAttachmentFresh_subset I Qs rs As hx)
  exact ⟨y, ZFSet.mem_sep.2 ⟨entry, ZFSet.pair_mem_prod.2
    ⟨hx, (ZFSet.pair_mem_prod.1 (full.1 entry)).2⟩⟩,
    fun z hz => unique z (ZFSet.mem_sep.1 hz).1⟩

theorem batch_height_function (oldCode : StrictLexHeightCode P C D rP old rD) :
    ZFSet.IsFunc d.batchCarrier (ZFSet.prod C D)
      (batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) :=
  taggedHeightGraph_function oldCode.function (t.batch_fresh_function e embeddings maps)

theorem encoded_height_entry (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD)
    (x : {p : ZFSet.{u} // p ∈ P} ⊕ d.templates.Fresh) :
    ZFSet.pair (d.coding.encode x) ((t.extendedHeight e embeddings maps oldCode columns target).value x).val ∈
      batchHeightGraph P I Qs rs As Vs Hs Cs E C D old := by
  cases x with
  | inl x =>
    exact (batchHeightGraph_old_entry x.property).2 (oldCode.value_entry x)
  | inr x =>
    apply (taggedHeightGraph_fresh_entry oldCode.function (t.batch_fresh_function e embeddings maps)).2
    exact ZFSet.mem_sep.2 ⟨t.componentValue_entry e embeddings maps x.1 x.2.val,
      ZFSet.pair_mem_prod.2 ⟨d.freshCode_mem x, (t.componentValue e embeddings maps x.1 x.2.val).property⟩⟩

theorem batchHeightGraph_strictLex (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    StrictLexHeightCode d.batchCarrier C D d.batchOrder
      (batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) rD := by
  have function := t.batch_height_function e embeddings maps oldCode
  refine ⟨function, ?_⟩
  intro x hx y hy c q b v lower different first second
  obtain ⟨s, rfl⟩ := d.coding.encode_surjective x hx
  obtain ⟨z, rfl⟩ := d.coding.encode_surjective y hy
  have strict := (t.extendedHeight e embeddings maps oldCode columns target).strict s z
    ((d.coding.le_encode s z).1 lower) (fun same => different (congrArg d.coding.encode same))
  have graph : FunctionGraphOn d.batchCarrier (batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) :=
    ⟨ZFSet.prod C D, function⟩
  have eqs := graph.unique (t.encoded_height_entry e embeddings maps oldCode columns target s) first
  have eqz := graph.unique (t.encoded_height_entry e embeddings maps oldCode columns target z) second
  change ZFSet.pair ((t.extendedHeight e embeddings maps oldCode columns target).value s).val
    ((t.extendedHeight e embeddings maps oldCode columns target).value z).val ∈ lexHeightOrder C D rD at strict
  rw [eqs, eqz] at strict
  exact ((pair_mem_lexHeightOrder C D rD c q b v).1 strict).2.2.2.2

theorem batchHeightGraph_bound_preserved (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD)
    {bound : ZFSet.{u}} (hBound : bound ∈ ZFSet.prod C D)
    (oldBound : ∀ x ∈ P, ∀ h, ZFSet.pair x h ∈ old → h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD) :
    ∀ x ∈ d.batchCarrier, ∀ h,
      ZFSet.pair x h ∈ batchHeightGraph P I Qs rs As Vs Hs Cs E C D old →
        h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD := by
  let R := (lexHeightOrder_code columns target).toLinearHeightOrder.toHeightOrder
  have oldWeak : ∀ x, R.Weak ((oldCode.toStrictHeight d.oldOrder columns target).value x) ⟨bound, hBound⟩ := by
    intro x
    rcases oldBound x.val x.property (oldCode.value x).val (oldCode.value_entry x) with same | less
    · exact Or.inl (Subtype.ext same)
    · exact Or.inr less
  have preserved := AttachmentHeight.bound_preserved d.templates
    (oldCode.toStrictHeight d.oldOrder columns target)
    (t.componentStrictHeight e embeddings maps columns target)
    (t.component_upper e embeddings maps oldCode columns target) ⟨bound, hBound⟩ oldWeak
  intro x hx h entry
  obtain ⟨s, rfl⟩ := d.coding.encode_surjective x hx
  have graph : FunctionGraphOn d.batchCarrier (batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) :=
    ⟨ZFSet.prod C D, t.batch_height_function e embeddings maps oldCode⟩
  have eqs := graph.unique (t.encoded_height_entry e embeddings maps oldCode columns target s) entry
  rcases preserved s with same | less
  · exact Or.inl (eqs.symm.trans (congrArg Subtype.val same))
  · apply Or.inr
    change ZFSet.pair ((t.extendedHeight e embeddings maps oldCode columns target).value s).val bound ∈
      lexHeightOrder C D rD at less
    exact eqs ▸ less

end TemplateHeightFamilyInputs

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

theorem FunctionGraphOn.constant_value {I x : ZFSet.{u}}
    (graph : FunctionGraphOn I (constantFamilyGraph I x)) (i : {i : ZFSet.{u} // i ∈ I}) :
    graph.value i = x :=
  ((pair_mem_constantFamilyGraph I x _ _).1 (graph.value_entry i)).2

theorem StrictLexHeightCode.strict_entry {P C D r old rD x y a b : ZFSet.{u}}
    (code : StrictLexHeightCode P C D r old rD) (lower : ZFSet.pair x y ∈ r)
    (different : x ≠ y) (first : ZFSet.pair x a ∈ old) (second : ZFSet.pair y b ∈ old) :
    ZFSet.pair a b ∈ lexHeightOrder C D rD := by
  have hx := ZFSet.pair_mem_prod.1 (code.function.1 first)
  have hy := ZFSet.pair_mem_prod.1 (code.function.1 second)
  obtain ⟨c, hc, q, hq, rfl⟩ := ZFSet.mem_prod.1 hx.2
  obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 hy.2
  exact (pair_mem_lexHeightOrder C D rD c q d v).2
    ⟨hc, hq, hd, hv, code.strict x hx.1 y hy.1 c q d v lower different first second⟩

namespace AttachmentBatchInputs
variable {P rP μP I Qs rs μs As Es Fs Ss P0 r0 C D old rD : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)

theorem constantTemplateHeights
    (spaces : ∀ i, d.space i = P0) (relations : ∀ i, d.rel i = r0)
    (code : StrictLexHeightCode P0 C D r0 old rD)
    (columns : ordinalSetProperty C) (target : StrictLinearOrderCode D rD) :
    TemplateHeightFamilyInputs d (constantFamilyGraph I (ZFSet.prod C D))
      (constantFamilyGraph I (lexHeightOrder C D rD)) (constantFamilyGraph I old) := by
  have rangeGraph : FunctionGraphOn I (constantFamilyGraph I (ZFSet.prod C D)) :=
    ⟨_, constantFamilyGraph_function I (ZFSet.prod C D)⟩
  have orderGraph : FunctionGraphOn I (constantFamilyGraph I (lexHeightOrder C D rD)) :=
    ⟨_, constantFamilyGraph_function I (lexHeightOrder C D rD)⟩
  have heightGraph : FunctionGraphOn I (constantFamilyGraph I old) :=
    ⟨_, constantFamilyGraph_function I old⟩
  refine {
    ranges := rangeGraph
    orders := orderGraph
    heights := heightGraph
    linear := ?_
    function := ?_
    strict := ?_
  }
  · intro i
    simpa only [FunctionGraphOn.constant_value] using lexHeightOrder_code columns target
  · intro i
    simpa only [FunctionGraphOn.constant_value, spaces i] using code.function
  · intro i x y a b lower different first second
    simp only [FunctionGraphOn.constant_value] at first second ⊢
    exact code.strict_entry (relations i ▸ lower) different first second

end AttachmentBatchInputs






theorem batchHeightGraph_columns
    {P rP μP I Qs rs μs As Es Fs Ss Vs Hs C D old rD Cs los his E : ZFSet.{u}}
    {d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss}
    (e : BatchHeightEndpointCode d C D old rD Cs los his)
    (oldFunction : ZFSet.IsFunc P (ZFSet.prod C D) old)
    (x c q : ZFSet.{u})
    (entry : ZFSet.pair x (ZFSet.pair c q) ∈
      batchHeightGraph P I Qs rs As Vs Hs Cs E C D old) :
    c ∈ heightColumns P C D old := by
  rcases ZFSet.mem_union.1 entry with oldEntry | freshEntry
  · exact mem_heightColumns_of_entry oldFunction oldEntry
  · obtain ⟨y, hy, h, _, equal, height⟩ := (ZFSet.mem_sep.1 freshEntry).2
    have sameHeight := (ZFSet.pair_inj.1 equal).2
    subst h
    obtain ⟨i, hi, p, equalY, _⟩ := (mem_indexedAttachmentFresh I Qs rs As y).1 hy
    subst y
    have component := (ZFSet.mem_sep.1 height).1
    obtain ⟨_, _, _, Q, g, f, _, _, _, _, column, _⟩ :=
      (pair_mem_componentHeightGraph I Qs (familyPointBound Vs) Hs Cs E C D i p c q).1 component
    exact mem_heightColumns_of_entry oldFunction
      (e.base ⟨i, hi⟩ c (e.low ⟨i, hi⟩) column (e.low_entry ⟨i, hi⟩))

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem batchFreshHeightGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I Qs rs As Vs Hs Cs E C D : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hVs : Vs ∈ M.sets) (hHs : Hs ∈ M.sets) (hCs : Cs ∈ M.sets) (hE : E ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) :
    batchFreshHeightGraph I Qs rs As Vs Hs Cs E C D ∈ M.sets :=
  M.injection_restriction_mem separation
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
    (M.prod_mem pairing unions powers separation hC hD)
    (M.componentHeightGraph_mem pairing unions powers separation hI hQs
      (M.familyPointBound_mem unions hVs) hHs hCs hE hC hD)

theorem batchHeightGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P I Qs rs As Vs Hs Cs E C D old : ZFSet.{u}}
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hVs : Vs ∈ M.sets) (hHs : Hs ∈ M.sets)
    (hCs : Cs ∈ M.sets) (hE : E ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hOld : old ∈ M.sets) : batchHeightGraph P I Qs rs As Vs Hs Cs E C D old ∈ M.sets :=
  M.taggedHeightGraph_mem pairing unions powers separation hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
    (M.prod_mem pairing unions powers separation hC hD) hOld
    (M.batchFreshHeightGraph_mem pairing unions powers separation
      hI hQs hrs hAs hVs hHs hCs hE hC hD)

theorem exists_batchHeight
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D old rD c : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hVs : Vs ∈ M.sets) (hvrs : vrs ∈ M.sets) (hHs : Hs ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hOld : old ∈ M.sets) (hc : c ∈ M.sets)
    (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (oldSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega)
    (templateSmall : ∀ i, M.groundEmbeddable (t.ranges.value i) ZFSet.omega) :
    ∃ height ∈ M.sets,
      StrictLexHeightCode d.batchCarrier C D d.batchOrder height rD ∧
      (∀ p ∈ P, ∀ h, ZFSet.pair p h ∈ height ↔ ZFSet.pair p h ∈ old) ∧
      relationImage d.batchCarrier (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage d.batchCarrier (ZFSet.prod C D) height) ZFSet.omega ∧
      (∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height → c ∈ heightColumns P C D old) ∧
      ∀ bound ∈ ZFSet.prod C D,
        (∀ p ∈ P, ∀ h, ZFSet.pair p h ∈ old →
          h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD) →
        ∀ x ∈ d.batchCarrier, ∀ h, ZFSet.pair x h ∈ height →
          h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD := by
  obtain ⟨Cs, hCs, los, hlos, his, hhis, endpoints⟩ := M.exists_batchHeightEndpoints
    pairing unions powers separation choice d oldCode above
    hI hP hC hD hAs hEs hSs hOld hrD
  obtain ⟨E, hE, family, valid⟩ := M.exists_templateIntervalFamily
    pairing unions powers separation collection infinite choice t endpoints
    hI hVs hvrs hlos hhis hD hrD hc target coordinateInjection templateSmall
  let embeddings : FunctionGraphOn I E := ⟨M.groundRelations (familyPointBound Vs) D, family⟩
  have maps : ∀ i, IntervalEmbeddingCode (t.ranges.value i) D (t.orders.value i) rD
      (endpoints.low i) (endpoints.high i) (embeddings.value i) := by
    intro i
    exact valid i _ _ _ (endpoints.low_entry i) (endpoints.high_entry i) (embeddings.value_entry i)
  let height := batchHeightGraph P I Qs rs As Vs Hs Cs E C D old
  have hHeight : height ∈ M.sets := M.batchHeightGraph_mem pairing unions powers separation
    hP hI hQs hrs hAs hVs hHs hCs hE hC hD hOld
  have hL : d.batchCarrier ∈ M.sets := M.taggedExtension_mem pairing unions powers separation hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
  have columnLaw : ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height →
      c ∈ heightColumns P C D old := batchHeightGraph_columns endpoints oldCode.function
  obtain ⟨rangeMember, rangeSmall⟩ := M.countable_height_range_of_old_columns
    pairing unions powers separation infinite choice hP hL hC hD hOld hHeight
    oldSmall ⟨c, hc, coordinateInjection⟩ columnLaw
  refine ⟨height, hHeight,
    t.batchHeightGraph_strictLex endpoints embeddings maps oldCode columns target.toStrictLinearOrderCode,
    (fun p hp h => batchHeightGraph_old_entry hp), rangeMember, rangeSmall, columnLaw, ?_⟩
  intro bound hBound oldBound
  exact t.batchHeightGraph_bound_preserved endpoints embeddings maps oldCode columns
    target.toStrictLinearOrderCode hBound oldBound

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_batchHeight_of_countable_ranges
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P rP μP I Qs rs μs As Es Fs Ss Vs vrs Hs C D old rD c : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (t : TemplateHeightFamilyInputs d Vs vrs Hs)
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hSs : Ss ∈ M.sets)
    (hVs : Vs ∈ M.sets) (hvrs : vrs ∈ M.sets) (hHs : Hs ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hOld : old ∈ M.sets) (hc : c ∈ M.sets)
    (oldCode : StrictLexHeightCode P C D rP old rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (oldSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) old) ZFSet.omega)
    (templateSmall : ∀ i, M.groundEmbeddable
      (relationImage (d.space i) (t.ranges.value i) (t.heights.value i)) ZFSet.omega) :
    ∃ height ∈ M.sets,
      StrictLexHeightCode d.batchCarrier C D d.batchOrder height rD ∧
      (∀ p ∈ P, ∀ h, ZFSet.pair p h ∈ height ↔ ZFSet.pair p h ∈ old) ∧
      relationImage d.batchCarrier (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage d.batchCarrier (ZFSet.prod C D) height) ZFSet.omega ∧
      (∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height → c ∈ heightColumns P C D old) ∧
      ∀ bound ∈ ZFSet.prod C D,
        (∀ p ∈ P, ∀ h, ZFSet.pair p h ∈ old →
          h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD) →
        ∀ x ∈ d.batchCarrier, ∀ h, ZFSet.pair x h ∈ height →
          h = bound ∨ ZFSet.pair h bound ∈ lexHeightOrder C D rD := by
  obtain ⟨Rs, hRs, ors, hors, restricted, rangeEq, _⟩ :=
    M.exists_templateHeightRanges pairing unions powers separation t hI hQs hVs hvrs hHs
  have small : ∀ i, M.groundEmbeddable (restricted.ranges.value i) ZFSet.omega := by
    intro i
    rw [rangeEq i]
    exact templateSmall i
  exact M.exists_batchHeight pairing unions powers separation collection infinite choice d restricted
    hP hI hQs hrs hAs hEs hSs hRs hors hHs hC hD hrD hOld hc oldCode columns target above
    coordinateInjection oldSmall small

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_height_step
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {C D rD c original old : ZFSet.{u}}
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (hOriginal : original ∈ M.sets) (hOld : old ∈ M.sets)
    (originalCode : StrictLexHeightCode P0 C D r0 original rD)
    (oldCode : StrictLexHeightCode state.data.D C D state.data.rD old rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P0 (ZFSet.prod C D) original) ZFSet.omega)
    (oldSmall : M.groundEmbeddable (relationImage state.data.D (ZFSet.prod C D) old) ZFSet.omega) :
    ∃ height ∈ M.sets,
      StrictLexHeightCode state.data.currentCarrier C D state.data.currentOrder height rD ∧
      (∀ x ∈ state.data.D, ∀ y, ZFSet.pair x y ∈ height ↔ ZFSet.pair x y ∈ old) ∧
      relationImage state.data.currentCarrier (ZFSet.prod C D) height ∈ M.sets ∧
      M.groundEmbeddable (relationImage state.data.currentCarrier (ZFSet.prod C D) height) ZFSet.omega ∧
      (∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ height → a ∈ heightColumns state.data.D C D old) ∧
      ∀ bound ∈ ZFSet.prod C D,
        (∀ x ∈ state.data.D, ∀ y, ZFSet.pair x y ∈ old →
          y = bound ∨ ZFSet.pair y bound ∈ lexHeightOrder C D rD) →
        ∀ x ∈ state.data.currentCarrier, ∀ y, ZFSet.pair x y ∈ height →
          y = bound ∨ ZFSet.pair y bound ∈ lexHeightOrder C D rD := by
  have spaces : ∀ i, state.batch.space i = P0 :=
    fun i => ((constant.space_entry_iff _ _).1 (state.batch.space_entry i)).2
  have relations : ∀ i, state.batch.rel i = r0 :=
    fun i => ((constant.relation_entry_iff _ _).1 (state.batch.rel_entry i)).2
  let templates := state.batch.constantTemplateHeights spaces relations originalCode columns
    target.toStrictLinearOrderCode
  have templateSmall : ∀ i, M.groundEmbeddable
      (relationImage (state.batch.space i) (templates.ranges.value i) (templates.heights.value i))
      ZFSet.omega := by
    intro i
    simpa only [FunctionGraphOn.constant_value, spaces i] using originalSmall
  have hValues := M.prod_mem pairing unions powers separation hC hD
  have hOrder := M.lexHeightOrder_mem pairing unions powers separation hC hD hrD
  exact M.exists_batchHeight_of_countable_ranges pairing unions powers separation collection infinite choice
    state.batch templates state.ground.carrier state.ground.indices state.ground.spaces state.ground.relations
    state.ground.anchors state.ground.embeddings state.ground.separators
    (M.constantFamilyGraph_mem pairing unions powers separation state.ground.indices hValues)
    (M.constantFamilyGraph_mem pairing unions powers separation state.ground.indices hOrder)
    (M.constantFamilyGraph_mem pairing unions powers separation state.ground.indices hOriginal)
    hC hD hrD hOld hc oldCode columns target above coordinateInjection oldSmall templateSmall

end PartitionPilot.Forcing.GroundCompressionState

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBoundedCompressionHeights
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_column_bounded_height_step
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {C D rD c original old : ZFSet.{u}}
    (hP0 : P0 ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (hOriginal : original ∈ M.sets) (hOld : old ∈ M.sets)
    (originalCode : StrictLexHeightCode P0 C D r0 original rD)
    (oldCode : StrictLexHeightCode state.data.D C D state.data.rD old rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P0 (ZFSet.prod C D) original) ZFSet.omega)
    (extension : original ⊆ old)
    (bounded : ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ old → a ∈ heightColumns P0 C D original) :
    ∃ height ∈ M.sets,
      StrictLexHeightCode state.data.currentCarrier C D state.data.currentOrder height rD ∧
      old ⊆ height ∧ original ⊆ height ∧
      ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ height → a ∈ heightColumns P0 C D original := by
  have oldSmall := (M.countable_height_range_of_old_columns pairing unions powers separation infinite choice
    hP0 state.ground.carrier hC hD hOriginal hOld originalSmall ⟨c, hc, coordinateInjection⟩ bounded).2
  obtain ⟨height, hHeight, code, restrict, _, _, columnBound, _⟩ := state.exists_height_step
    pairing unions powers separation collection infinite choice constant hC hD hrD hc hOriginal hOld
    originalCode oldCode columns target above coordinateInjection originalSmall oldSmall
  have inclusion : old ⊆ height := by
    intro z hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (oldCode.function.1 hz)
    exact (restrict x hx y).2 hz
  refine ⟨height, hHeight, code, inclusion, fun _ hx => inclusion (extension hx), ?_⟩
  intro x a q entry
  exact heightColumns_subset_of_bound bounded (columnBound x a q entry)

end PartitionPilot.Forcing.GroundCompressionState

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RectangleFulfillmentAtBound
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

theorem truth_actionAgreementBelowFormula {n} (P r A g h w : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionAgreementBelowFormula P r A g h w) env ↔
      ActionAgreementBelow (env P) (env r) (env A) (env g) (env h) (env w) := by
  simp only [actionAgreementBelowFormula, ActionAgreementBelow, Truth, truth_imp, iff_def,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor <;> exact fun h => h

theorem truth_externalRectangleFormula {n} (P G r μ A c b d g h : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalRectangleFormula P G r μ A c b d g h) env ↔
      ExternalRectangleCode (env P) (env G) (env r) (env μ) (env A)
        (env c) (env b) (env d) (env g) (env h) := by
  simp only [externalRectangleFormula, ExternalRectangleCode, rectangleSeparatedFormula,
    Truth, truth_exMem, truth_imp, truth_actionAgreementBelowFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

theorem truth_externalRectanglesEntryFormula {n} (t P G r μ A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalRectanglesEntryFormula t P G r μ A) env ↔
      ∃ c ∈ env P, ∃ b ∈ env P, ∃ d ∈ env P, ∃ g ∈ env G, ∃ h ∈ env G,
        env t = externalRectangleCode c b d g h ∧
          ExternalRectangleCode (env P) (env G) (env r) (env μ) (env A) c b d g h := by
  simp only [externalRectanglesEntryFormula, truth_exMem, Truth,
    truth_externalRectangleTupleFormula, truth_externalRectangleFormula]
  rfl

end BoundedFormula





end PartitionPilot.Forcing



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


namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem partialOrder {P r : Nat → ZFSet.{u}} {L R : ZFSet.{u}}
    (carrier : NatUnionCode P L) (relation : NatUnionCode r R)
    (orders : ∀ n, PartialOrderCode (P n) (r n))
    (relationMono : ∀ n m, n ≤ m → r n ⊆ r m) : PartialOrderCode L R := by
  constructor
  · intro z hz
    obtain ⟨n, hn⟩ := (relation z).1 hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((orders n).relation hn)
    exact ZFSet.pair_mem_prod.2 ⟨carrier.subset n hx, carrier.subset n hy⟩
  · intro x hx
    obtain ⟨n, hn⟩ := (carrier x).1 hx
    exact relation.subset n ((orders n).refl x hn)
  · intro x _ y _ xy yx
    obtain ⟨n, hn⟩ := (relation _).1 xy
    obtain ⟨m, hm⟩ := (relation _).1 yx
    have first := relationMono n (max n m) (le_max_left n m) hn
    have second := relationMono m (max n m) (le_max_right n m) hm
    have shape := ZFSet.pair_mem_prod.1 ((orders (max n m)).relation first)
    exact (orders (max n m)).antisymm x shape.1 y shape.2 first second
  · intro x _ y _ z _ xy yz
    obtain ⟨n, hn⟩ := (relation _).1 xy
    obtain ⟨m, hm⟩ := (relation _).1 yz
    have first := relationMono n (max n m) (le_max_left n m) hn
    have second := relationMono m (max n m) (le_max_right n m) hm
    have xyShape := ZFSet.pair_mem_prod.1 ((orders (max n m)).relation first)
    have yzShape := ZFSet.pair_mem_prod.1 ((orders (max n m)).relation second)
    exact relation.subset (max n m)
      ((orders (max n m)).trans x xyShape.1 y xyShape.2 z yzShape.2 first second)

theorem order_entry_iff {P r : Nat → ZFSet.{u}} {R : ZFSet.{u}}
    (relation : NatUnionCode r R)
    (relationMono : ∀ n m, n ≤ m → r n ⊆ r m)
    (oldOrder : ∀ n m, n ≤ m → ∀ x ∈ P n, ∀ y ∈ P n,
      ZFSet.pair x y ∈ r m ↔ ZFSet.pair x y ∈ r n)
    (n : Nat) {x y : ZFSet.{u}} (hx : x ∈ P n) (hy : y ∈ P n) :
    ZFSet.pair x y ∈ R ↔ ZFSet.pair x y ∈ r n := by
  constructor
  · intro entry
    obtain ⟨m, hm⟩ := (relation _).1 entry
    exact (oldOrder n (max n m) (le_max_left n m) x hx y hy).1
      (relationMono m _ (le_max_right n m) hm)
  · exact fun entry => relation.subset n entry

theorem meetOrder {P r μ : Nat → ZFSet.{u}} {L R M : ZFSet.{u}}
    (carrier : NatUnionCode P L) (relation : NatUnionCode r R) (operation : NatUnionCode μ M)
    (codes : ∀ n, MeetOrderCode (P n) (r n) (μ n))
    (carrierMono : ∀ n m, n ≤ m → P n ⊆ P m)
    (relationMono : ∀ n m, n ≤ m → r n ⊆ r m)
    (operationMono : ∀ n m, n ≤ m → μ n ⊆ μ m) : MeetOrderCode L R M := by
  refine ⟨carrier.partialOrder relation (fun n => (codes n).order) relationMono,
    (carrier.prod carrier carrierMono carrierMono).isFunc carrier operation
      (fun n => (codes n).operation) operationMono, ?_, ?_, ?_⟩
  · intro x y z entry
    obtain ⟨n, hn⟩ := (operation _).1 entry
    exact relation.subset n ((codes n).lower_left x y z hn)
  · intro x y z entry
    obtain ⟨n, hn⟩ := (operation _).1 entry
    exact relation.subset n ((codes n).lower_right x y z hn)
  · intro x y z w _ meet wx wy
    obtain ⟨n, hn⟩ := (operation _).1 meet
    obtain ⟨i, hi⟩ := (relation _).1 wx
    obtain ⟨j, hj⟩ := (relation _).1 wy
    let k := max n (max i j)
    have nk : n ≤ k := le_max_left n (max i j)
    have ik : i ≤ k := (le_max_left i j).trans (le_max_right n (max i j))
    have jk : j ≤ k := (le_max_right i j).trans (le_max_right n (max i j))
    have meetK := operationMono n k nk hn
    have wxK := relationMono i k ik hi
    have wyK := relationMono j k jk hj
    have wK := (ZFSet.pair_mem_prod.1 ((codes k).order.relation wxK)).1
    exact relation.subset k ((codes k).greatest x y z w wK meetK wxK wyK)

theorem meet_entry_iff {P r μ : Nat → ZFSet.{u}} {L R M : ZFSet.{u}}
    (operation : NatUnionCode μ M) (unionCode : MeetOrderCode L R M)
    (codes : ∀ n, MeetOrderCode (P n) (r n) (μ n))
    (n : Nat) {x y z : ZFSet.{u}} (hx : x ∈ P n) (hy : y ∈ P n) :
    ZFSet.pair (ZFSet.pair x y) z ∈ M ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ n :=
  operation.function_entry_iff unionCode.operation (fun n => (codes n).operation) n
    (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)

end PartitionPilot.Forcing.NatUnionCode



namespace PartitionPilot.Forcing
universe u v w

theorem CodedInsertionProfile.iff_profile {L r μ c e K F : ZFSet.{u}}
    (meet : MeetOrderCode L r μ) (hc : c ∈ L) (he : e ∈ L) (hK : K ∈ L)
    (subset : F ⊆ L) :
    CodedInsertionProfile L r μ c e K F ↔
      Profile meet.toMeetOrder ⟨c, hc⟩ ⟨e, he⟩ ⟨K, hK⟩ (fun f => f.val ∈ F) := by
  have positive (x : {x : ZFSet.{u} // x ∈ L}) :
      Positive meet.toMeetOrder (fun f => f.val ∈ F) x ↔
        ∃ f ∈ F, ZFSet.pair f x.val ∈ r := by
    constructor
    · rintro ⟨f, hf, lower⟩
      exact ⟨f.val, hf, lower⟩
    · rintro ⟨f, hf, lower⟩
      exact ⟨⟨f, subset hf⟩, hf, lower⟩
  constructor
  · intro profile x above
    have inherited := profile x.val x.property above
    refine ⟨fun hx => inherited.1 ((positive x).1 hx), ?_⟩
    intro negative
    have entry := inherited.2 (fun hx => negative ((positive x).2 hx))
    apply Subtype.ext
    exact (show FunctionGraphOn (ZFSet.prod L L) μ from ⟨L, meet.operation⟩).unique
      (meet.toMeetOrder_meet_entry ⟨K, hK⟩ x) entry
  · intro profile x hx above
    have inherited := profile ⟨x, hx⟩ above
    refine ⟨fun positiveRaw => inherited.1 ((positive ⟨x, hx⟩).2 positiveRaw), ?_⟩
    intro negative
    have equal := inherited.2 (fun hp => negative ((positive ⟨x, hx⟩).1 hp))
    have entry := meet.toMeetOrder_meet_entry ⟨K, hK⟩ ⟨x, hx⟩
    rw [equal] at entry
    exact entry

namespace CodedTemplateAttachment
variable {J : Type v} {P r μ N inside shadow upper c e K F : ZFSet.{u}}
variable {old : MeetOrderCode P r μ} {b : Attachment.Templates.{u+1,w,v} old.toMeetOrder J}
variable (d : CodedTemplateAttachment old b N inside shadow upper)

theorem insertion_profile_persists (hc : c ∈ P) (he : e ∈ P) (hK : K ∈ P)
    (subset : F ⊆ P) (nonempty : ∃ f, f ∈ F)
    (profile : CodedInsertionProfile P r μ c e K F)
    (separated : ZFSet.pair e K ∉ r) :
    CodedInsertionProfile d.carrier d.order d.meetGraph c e K F := by
  have nonemptyTyped : ∃ f : {f : ZFSet.{u} // f ∈ P}, f.val ∈ F := by
    obtain ⟨f, hf⟩ := nonempty
    exact ⟨⟨f, subset hf⟩, hf⟩
  have inherited := b.persistence ⟨c, hc⟩ ⟨e, he⟩ ⟨K, hK⟩ (fun f => f.val ∈ F)
    nonemptyTyped ((CodedInsertionProfile.iff_profile old hc he hK subset).1 profile) separated
  intro x hx above
  obtain ⟨q, rfl⟩ := d.encode_surjective x hx
  have positive : (∃ f ∈ F, ZFSet.pair f (d.encode q) ∈ d.order) ↔
      PositiveOver b.oldEmbedding (fun f => f.val ∈ F) q := by
    constructor
    · rintro ⟨f, hf, lower⟩
      exact ⟨⟨f, subset hf⟩, hf, (d.le_encode (.inl ⟨f, subset hf⟩) q).1 lower⟩
    · rintro ⟨f, hf, lower⟩
      exact ⟨f.val, hf, (d.le_encode (.inl f) q).2 lower⟩
  have atPoint := inherited q ((d.le_encode (.inl ⟨e, he⟩) q).1 above)
  refine ⟨fun hp => (d.le_encode (.inl ⟨K, hK⟩) q).2 (atPoint.1 (positive.1 hp)), ?_⟩
  intro negative
  have equal := atPoint.2 (fun hp => negative (positive.2 hp))
  have entry := d.encoded_meet_entry (.inl ⟨K, hK⟩) q
  change b.extension.meet (.inl ⟨K, hK⟩) q = .inl ⟨c, hc⟩ at equal
  rw [equal] at entry
  exact entry

end CodedTemplateAttachment

theorem AttachmentBatchInputs.insertion_profile_persists
    {P r μ J Qs rs μs As Es Fs Ss c e K F : ZFSet.{u}}
    (d : AttachmentBatchInputs P r μ J Qs rs μs As Es Fs Ss)
    (hc : c ∈ P) (he : e ∈ P) (hK : K ∈ P)
    (subset : F ⊆ P) (nonempty : ∃ f, f ∈ F)
    (profile : CodedInsertionProfile P r μ c e K F)
    (separated : ZFSet.pair e K ∉ r) :
    CodedInsertionProfile d.batchCarrier d.batchOrder d.batchMeetGraph c e K F :=
  d.coding.insertion_profile_persists hc he hK subset nonempty profile separated

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem insertionProfile {P r μ : Nat → ZFSet.{u}} {L R M c e K F : ZFSet.{u}}
    (relation : NatUnionCode r R) (operation : NatUnionCode μ M)
    (orders : ∀ n, PartialOrderCode (P n) (r n))
    (relationMono : ∀ n m, n ≤ m → r n ⊆ r m)
    (profiles : ∀ n, CodedInsertionProfile (P n) (r n) (μ n) c e K F) :
    CodedInsertionProfile L R M c e K F := by
  intro v _ above
  obtain ⟨n, aboveN⟩ := (relation _).1 above
  constructor
  · rintro ⟨f, hf, below⟩
    obtain ⟨m, belowM⟩ := (relation _).1 below
    have aboveCommon := relationMono n (max n m) (le_max_left n m) aboveN
    have belowCommon := relationMono m (max n m) (le_max_right n m) belowM
    have hv := (ZFSet.pair_mem_prod.1 ((orders (max n m)).relation aboveCommon)).2
    exact relation.subset (max n m)
      ((profiles (max n m) v hv aboveCommon).1 ⟨f, hf, belowCommon⟩)
  · intro negative
    have hv := (ZFSet.pair_mem_prod.1 ((orders n).relation aboveN)).2
    apply operation.subset n
    apply (profiles n v hv aboveN).2
    rintro ⟨f, hf, below⟩
    exact negative ⟨f, hf, relation.subset n below⟩

end PartitionPilot.Forcing.NatUnionCode


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundBatchBirths
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace NatUnionCode
universe u

theorem oldMeet {r μ birth : Nat → ZFSet.{u}} {R MU B : ZFSet.{u}}
    (relation : NatUnionCode r R) (operation : NatUnionCode μ MU)
    (born : NatUnionCode birth B)
    (laws : ∀ n, OldMeetCode (r n) (μ n) (birth n))
    (operationMono : ∀ n m, n ≤ m → μ n ⊆ μ m)
    (birthMono : ∀ n m, n ≤ m → birth n ⊆ birth m) : OldMeetCode R MU B := by
  intro x y z a b c ya xb ab notLower xy zc
  obtain ⟨i, hi⟩ := (born _).1 ya
  obtain ⟨j, hj⟩ := (born _).1 xb
  obtain ⟨k, hk⟩ := (operation _).1 xy
  obtain ⟨l, hl⟩ := (born _).1 zc
  let n := max (max i j) (max k l)
  have iN : i ≤ n := (le_max_left i j).trans (le_max_left (max i j) (max k l))
  have jN : j ≤ n := (le_max_right i j).trans (le_max_left (max i j) (max k l))
  have kN : k ≤ n := (le_max_left k l).trans (le_max_right (max i j) (max k l))
  have lN : l ≤ n := (le_max_right k l).trans (le_max_right (max i j) (max k l))
  exact laws n x y z a b c (birthMono i n iN hi) (birthMono j n jN hj) ab
    (fun lower => notLower (relation.subset n lower)) (operationMono k n kN hk)
    (birthMono l n lN hl)

end NatUnionCode

namespace AttachmentBatchInputs
universe u
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

theorem batchBirth_oldMeet {T birth stamp : ZFSet.{u}}
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (oldMeet : OldMeetCode r μ birth) :
    OldMeetCode d.batchOrder d.batchMeetGraph (d.batchBirth birth stamp) := by
  intro x y z a b c ya xb ab notLower meetEntry zc
  rcases (pair_mem_taggedBirth _ _ _ _ x b).1 xb with oldx | ⟨freshx, rfl⟩
  · have hx := (ZFSet.pair_mem_prod.1 (born.1 oldx)).1
    rcases (pair_mem_taggedBirth _ _ _ _ y a).1 ya with oldy | ⟨_, rfl⟩
    · have hy := (ZFSet.pair_mem_prod.1 (born.1 oldy)).1
      have oldEntry := (d.old_meet_iff hx hy).1 meetEntry
      have hz := (ZFSet.pair_mem_prod.1 (d.oldOrder.operation.1 oldEntry)).2
      exact oldMeet x y z a b c oldy oldx ab
        (fun lower => notLower ((d.old_order_iff hx hy).2 lower)) oldEntry
        ((taggedBirth_old_iff hz).1 zc)
    · exact False.elim (ZFSet.mem_asymm (earlier x b oldx) ab)
  · rcases (pair_mem_taggedBirth _ _ _ _ y a).1 ya with oldy | ⟨_, rfl⟩
    · have hy := (ZFSet.pair_mem_prod.1 (born.1 oldy)).1
      obtain ⟨p, hp, q, hq, equal⟩ := ZFSet.mem_prod.1 freshx
      obtain rfl := ZFSet.mem_singleton.1 hp
      subst x
      obtain ⟨q', rfl⟩ := d.freshCode_surjective q hq
      let v := d.oldOrder.toMeetOrder.meet (d.templates.shadow q') ⟨y, hy⟩
      have other : ZFSet.pair (ZFSet.pair (d.coding.encode (.inr q')) y) v.val ∈ d.batchMeetGraph :=
        d.coding.encoded_shadow_meet q' ⟨y, hy⟩ notLower
      have equal : z = v.val :=
        (show FunctionGraphOn (ZFSet.prod d.batchCarrier d.batchCarrier) d.batchMeetGraph from
          ⟨d.batchCarrier, d.batch_meetOrder.operation⟩).unique meetEntry other
      subst z
      exact earlier v.val c ((taggedBirth_old_iff v.property).1 zc)
    · exact False.elim (ZFSet.mem_irrefl _ ab)

end AttachmentBatchInputs

open SetRealization SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_NatActionUnions
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem posetAction {P r a : Nat → ZFSet.{u}} {G m e L R A : ZFSet.{u}}
    (carrier : NatUnionCode P L) (relation : NatUnionCode r R) (action : NatUnionCode a A)
    (codes : ∀ n, PosetActionCode G (P n) m e (r n) (a n))
    (relationMono : ∀ n j, n ≤ j → r n ⊆ r j)
    (actionMono : ∀ n j, n ≤ j → a n ⊆ a j) : PosetActionCode G L m e R A := by
  refine ⟨(carrier.prod_left G).isFunc carrier action (fun n => (codes n).function) actionMono,
    ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨n, hn⟩ := (carrier p).1 hp
    exact action.subset n ((codes n).one p hn)
  · intro g hg h hh k hk p _ q _ v _ product first second
    obtain ⟨i, hi⟩ := (action _).1 first
    obtain ⟨j, hj⟩ := (action _).1 second
    let n := max i j
    have firstN := actionMono i n (le_max_left i j) hi
    have secondN := actionMono j n (le_max_right i j) hj
    have firstShape := ZFSet.pair_mem_prod.1 ((codes n).function.1 firstN)
    have secondShape := ZFSet.pair_mem_prod.1 ((codes n).function.1 secondN)
    exact action.subset n ((codes n).mul g hg h hh k hk
      p (ZFSet.pair_mem_prod.1 firstShape.1).2 q firstShape.2 v secondShape.2 product firstN secondN)
  · intro g hg p _ q _ v _ w _ first second lower
    obtain ⟨i, hi⟩ := (action _).1 first
    obtain ⟨j, hj⟩ := (action _).1 second
    obtain ⟨k, hk⟩ := (relation _).1 lower
    let n := max k (max i j)
    have kn : k ≤ n := le_max_left k (max i j)
    have inN : i ≤ n := (le_max_left i j).trans (le_max_right k (max i j))
    have jn : j ≤ n := (le_max_right i j).trans (le_max_right k (max i j))
    have firstN := actionMono i n inN hi
    have secondN := actionMono j n jn hj
    have firstShape := ZFSet.pair_mem_prod.1 ((codes n).function.1 firstN)
    have secondShape := ZFSet.pair_mem_prod.1 ((codes n).function.1 secondN)
    exact relation.subset n ((codes n).monotone g hg
      p (ZFSet.pair_mem_prod.1 firstShape.1).2
      q (ZFSet.pair_mem_prod.1 secondShape.1).2 v firstShape.2 w secondShape.2
      firstN secondN (relationMono k n kn hk))

theorem action_entry_iff {P r a : Nat → ZFSet.{u}} {G m e L R A : ZFSet.{u}}
    (action : NatUnionCode a A) (unionCode : PosetActionCode G L m e R A)
    (codes : ∀ n, PosetActionCode G (P n) m e (r n) (a n))
    (n : Nat) {g x y : ZFSet.{u}} (hx : x ∈ P n) :
    ZFSet.pair (ZFSet.pair g x) y ∈ A ↔ ZFSet.pair (ZFSet.pair g x) y ∈ a n := by
  by_cases hg : g ∈ G
  · exact action.function_entry_iff unionCode.function (fun n => (codes n).function) n
      (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
  · constructor
    · intro entry
      exact (hg (ZFSet.pair_mem_prod.1
        (ZFSet.pair_mem_prod.1 (unionCode.function.1 entry)).1).1).elim
    · intro entry
      exact (hg (ZFSet.pair_mem_prod.1
        (ZFSet.pair_mem_prod.1 ((codes n).function.1 entry)).1).1).elim

end PartitionPilot.Forcing.NatUnionCode

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCoherentHeightUnion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem strictLexHeight {P r h : Nat → ZFSet.{u}} {U R H C D rD : ZFSet.{u}}
    (carrier : NatUnionCode P U) (relation : NatUnionCode r R) (height : NatUnionCode h H)
    (orders : ∀ n, PartialOrderCode (P n) (r n))
    (codes : ∀ n, StrictLexHeightCode (P n) C D (r n) (h n) rD)
    (heightMono : ∀ n m, n ≤ m → h n ⊆ h m) : StrictLexHeightCode U C D R H rD := by
  have function := carrier.isFunc (NatUnionCode.constant (ZFSet.prod C D)) height
    (fun n => (codes n).function) heightMono
  refine ⟨function, ?_⟩
  intro x _ y _ c q d v lower different first second
  obtain ⟨n, finiteLower⟩ := (relation (ZFSet.pair x y)).1 lower
  have bounds := ZFSet.pair_mem_prod.1 ((orders n).relation finiteLower)
  exact (codes n).strict x bounds.1 y bounds.2 c q d v finiteLower different
    ((height.function_entry_iff function (fun n => (codes n).function) n bounds.1).1 first)
    ((height.function_entry_iff function (fun n => (codes n).function) n bounds.2).1 second)

theorem height_entry_iff {P r h : Nat → ZFSet.{u}} {U R H C D rD : ZFSet.{u}}
    (height : NatUnionCode h H) (code : StrictLexHeightCode U C D R H rD)
    (codes : ∀ n, StrictLexHeightCode (P n) C D (r n) (h n) rD)
    (n : Nat) {x y : ZFSet.{u}} (hx : x ∈ P n) :
    ZFSet.pair x y ∈ H ↔ ZFSet.pair x y ∈ h n :=
  height.function_entry_iff code.function (fun n => (codes n).function) n hx

theorem height_column_bound {h : Nat → ZFSet.{u}} {H B : ZFSet.{u}}
    (height : NatUnionCode h H)
    (bounded : ∀ n x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h n → c ∈ B) :
    ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ H → c ∈ B := by
  intro x c q entry
  obtain ⟨n, finiteEntry⟩ := (height (ZFSet.pair x (ZFSet.pair c q))).1 entry
  exact bounded n x c q finiteEntry

end PartitionPilot.Forcing.NatUnionCode



namespace PartitionPilot.Forcing
universe u

theorem natGraphMono_of_adjacent {graphs : Nat → ZFSet.{u}}
    (adjacent : ∀ n, graphs n ⊆ graphs (n + 1)) :
    ∀ n m, n ≤ m → graphs n ⊆ graphs m := by
  intro n m before
  induction m, before using Nat.le_induction with
  | base => exact fun _ hx => hx
  | succ m _ ih => exact fun _ hx => adjacent m (ih hx)

namespace TransitiveGround
open SetFormula

theorem exists_groundCoherentHeightUnion (M : TransitiveGround.{u})
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    {family U R C D rD B : ZFSet.{u}} {P r : Nat → ZFSet.{u}}
    (hFamily : family ∈ M.sets) (function : FunctionGraphOn ZFSet.omega family)
    (carrier : NatUnionCode P U) (relation : NatUnionCode r R)
    (orders : ∀ n, PartialOrderCode (P n) (r n))
    (codes : ∀ n, StrictLexHeightCode (P n) C D (r n) (function.natValue n) rD)
    (adjacent : ∀ n, function.natValue n ⊆ function.natValue (n + 1))
    (columns : ∀ n x c q, ZFSet.pair x (ZFSet.pair c q) ∈ function.natValue n → c ∈ B) :
    ∃ height ∈ M.sets,
      NatUnionCode function.natValue height ∧ StrictLexHeightCode U C D R height rD ∧
      (∀ n x, x ∈ P n → ∀ y, ZFSet.pair x y ∈ height ↔
        ZFSet.pair x y ∈ function.natValue n) ∧
      ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ height → c ∈ B := by
  have exactUnion := naturalFamilyUnion_code function
  have code := carrier.strictLexHeight relation exactUnion orders codes (natGraphMono_of_adjacent adjacent)
  exact ⟨naturalFamilyUnion family, M.naturalFamilyUnion_mem unions separation hω hFamily,
    exactUnion, code,
    fun n x hx _ => exactUnion.height_entry_iff code codes n hx,
    exactUnion.height_column_bound columns⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteAccounting
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem successor_accounting (accounted : FiniteCompressionAccounting P0 I Sources τ state.data) :
    FiniteCompressionAccounting P0 I Sources τ (state.data.successor M I Sources Reps G T) := by
  obtain ⟨next, _, _, _, _, _, _, _, _, _, entries, inputs, _⟩ :=
    state.task.exists_groundSuccessor M pairing unions powers separation
      (state.invariant.compatible state.task) hI state.ground.indices state.ground.carrier
      state.ground.order state.ground.spaces state.ground.relations state.ground.meets
      state.ground.anchors state.ground.embeddings state.ground.filters state.ground.separators
      state.ground.maps hSources hReps hG state.ground.action hT
  have old : FiniteCompressionAccounting P0 I Sources τ state.inputs.toState :=
    state.inputs_toState.symm ▸ accounted
  have result := state.inputs.accounting_next M next entries inputs
    (state.invariant.originalSubset seed.top_mem) state.invariant.top old
  rw [state.inputs.toState_successor M next inputs, state.inputs_toState] at result
  exact result

theorem canonical_iterate_accounting
    (initial : FiniteCompressionAccounting P0 I Sources τ state.data) (n : Nat) :
    FiniteCompressionAccounting P0 I Sources τ (state.data.iterate M I Sources Reps G T n) := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    have step := current.successor_accounting pairing unions powers separation hI hSources hReps hG hT
      (equal.symm ▸ ih)
    rw [equal, ← RecursiveStateData.iterate_succ] at step
    exact step

end PartitionPilot.Forcing.GroundCompressionState

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_HistoryFieldFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_stateFieldFormula {n} (code value : Fin n) (j : Fin 13)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (state : RecursiveStateData.{u}) (coded : env code = state.code) :
    Realize M.sets (stateFieldFormula code value j) env ↔ env value = state.field j := by
  rw [stateFieldFormula, realize_exBlock]
  constructor
  · rintro ⟨fields, fieldMembers, tuple, entry⟩
    have equal := (BoundedFormula.truth_nonemptyTupleFormula 12 (suffixIndex n 13 code)
      (prefixIndex n 13) _).1
      ((BoundedFormula.realize_toFormula M _ _ (extendMany_members 13 fields env fieldMembers members)).1 tuple)
    simp only [extendMany_suffix, extendMany_prefix] at equal
    have fieldsEqual : fields = state.field :=
      nonemptyTupleCode_injective 12 (equal.symm.trans coded)
    change extendMany 13 fields env (suffixIndex n 13 value) =
      extendMany 13 fields env (prefixIndex n 13 j) at entry
    simpa only [extendMany_suffix, extendMany_prefix, fieldsEqual] using entry
  · intro equal
    have fieldMembers := M.recursiveStateData_field_mem state (coded ▸ members code)
    refine ⟨state.field, fieldMembers, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _
        (extendMany_members 13 state.field env fieldMembers members)).2
      apply (BoundedFormula.truth_nonemptyTupleFormula 12 (suffixIndex n 13 code)
        (prefixIndex n 13) _).2
      simp only [extendMany_suffix, extendMany_prefix]
      exact coded
    · change extendMany 13 state.field env (suffixIndex n 13 value) =
        extendMany 13 state.field env (prefixIndex n 13 j)
      simpa only [extendMany_suffix, extendMany_prefix] using equal

theorem realize_historyFieldValueFormula {k} (index value history : Fin k) (j : Fin 13)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ env history ↔ y = (states n).code)
    (n : Nat) (indexEq : env index = natSetCode n) :
    Realize M.sets (historyFieldValueFormula index value history j) env ↔
      env value = (states n).field j := by
  rw [historyFieldValueFormula, realize_ex]
  constructor
  · rintro ⟨code, hcode, entry, projected⟩
    have extended : ∀ i, extend code env i ∈ M.sets := Fin.cases hcode members
    have actual := (BoundedFormula.truth_pairMembershipFormula index.succ 0 history.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 entry)
    change ZFSet.pair (env index) code ∈ env history at actual
    rw [indexEq] at actual
    exact (M.realize_stateFieldFormula 0 value.succ j (extend code env) extended
      (states n) ((entries n code).1 actual)).1 projected
  · intro equal
    have entry : ZFSet.pair (natSetCode n) (states n).code ∈ env history :=
      (entries n _).2 rfl
    have hcode := M.pair_right (M.transitive (members history) entry)
    have extended : ∀ i, extend (states n).code env i ∈ M.sets := Fin.cases hcode members
    refine ⟨(states n).code, hcode, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ extended).2
      apply (BoundedFormula.truth_pairMembershipFormula index.succ 0 history.succ _).2
      change ZFSet.pair (env index) (states n).code ∈ env history
      exact indexEq.symm ▸ entry
    · exact (M.realize_stateFieldFormula 0 value.succ j _ extended (states n) rfl).2 equal

theorem realize_historyFieldPairFormula {k} (index output history : Fin k) (j : Fin 13)
    (env : Fin k → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ env history ↔ y = (states n).code)
    (n : Nat) (indexEq : env index = natSetCode n) :
    Realize M.sets (historyFieldPairFormula index output history j) env ↔
      env output = ZFSet.pair (natSetCode n) ((states n).field j) := by
  rw [historyFieldPairFormula, realize_ex]
  constructor
  · rintro ⟨value, hvalue, specified, pair⟩
    have extended : ∀ i, extend value env i ∈ M.sets := Fin.cases hvalue members
    have valueEq := (M.realize_historyFieldValueFormula index.succ 0 history.succ j
      (extend value env) extended states entries n indexEq).1 specified
    have pairEq := (BoundedFormula.truth_orderedPairFormula output.succ index.succ 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 pair)
    change env output = ZFSet.pair (env index) value at pairEq
    exact pairEq.trans (congrArg₂ ZFSet.pair indexEq valueEq)
  · intro equal
    have codeM := M.pair_right (M.transitive (members history) ((entries n _).2 rfl))
    have valueM := M.recursiveStateData_field_mem (states n) codeM j
    have extended : ∀ i, extend ((states n).field j) env i ∈ M.sets := Fin.cases valueM members
    refine ⟨(states n).field j, valueM, ?_, ?_⟩
    · exact (M.realize_historyFieldValueFormula index.succ 0 history.succ j _ extended
        states entries n indexEq).2 rfl
    · apply (BoundedFormula.realize_toFormula M _ _ extended).2
      apply (BoundedFormula.truth_orderedPairFormula output.succ index.succ 0 _).2
      change env output = ZFSet.pair (env index) ((states n).field j)
      exact equal.trans (congrArg (fun x => ZFSet.pair x ((states n).field j)) indexEq.symm)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundHistoryFields
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundStateFieldFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    {history : ZFSet.{u}} (hHistory : history ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = (states n).code)
    (j : Fin 13) :
    ∃ family ∈ M.sets, FunctionGraphOn ZFSet.omega family ∧
      ∀ n y, ZFSet.pair (natSetCode n) y ∈ family ↔ y = (states n).field j := by
  let params := extend history Fin.elim0
  have paramsM : ∀ i, params i ∈ M.sets := Fin.cases hHistory (fun i => Fin.elim0 i)
  have fieldsM (n : Nat) : (states n).field j ∈ M.sets :=
    M.recursiveStateData_field_mem (states n)
      (M.pair_right (M.transitive hHistory ((entries n _).2 rfl))) j
  have naturalM (n : Nat) : natSetCode n ∈ M.sets := M.transitive hω (natSetCode_mem_omega n)
  have total : ∀ x ∈ M.sets, x ∈ ZFSet.omega → ∃ z ∈ M.sets,
      Realize M.sets (historyFieldPairFormula 0 1 2 j) (extend x (extend z params)) ∧
      ∀ w ∈ M.sets,
        Realize M.sets (historyFieldPairFormula 0 1 2 j) (extend x (extend w params)) → w = z := by
    intro x hx hxω
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hxω
    have pairM := M.orderedPair_mem pairing hx (fieldsM n)
    refine ⟨ZFSet.pair (natSetCode n) ((states n).field j), pairM, ?_, ?_⟩
    · exact (M.realize_historyFieldPairFormula 0 1 2 j _
        (Fin.cases hx (Fin.cases pairM paramsM)) states entries n rfl).2 rfl
    · intro w hw specified
      exact (M.realize_historyFieldPairFormula 0 1 2 j _
        (Fin.cases hx (Fin.cases hw paramsM)) states entries n rfl).1 specified
  obtain ⟨family, hFamily, image⟩ := replacement_of_collection_separation M.sets collection separation
    (historyFieldPairFormula 0 1 2 j) params paramsM ZFSet.omega hω total
  have allEntries (z : ZFSet.{u}) :
      z ∈ family ↔ ∃ n, z = ZFSet.pair (natSetCode n) ((states n).field j) := by
    constructor
    · intro member
      have hz := M.transitive hFamily member
      obtain ⟨x, hx, hxω, specified⟩ := (image z hz).1 member
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hxω
      exact ⟨n, (M.realize_historyFieldPairFormula 0 1 2 j _
        (Fin.cases hx (Fin.cases hz paramsM)) states entries n rfl).1 specified⟩
    · rintro ⟨n, rfl⟩
      have pairM := M.orderedPair_mem pairing (naturalM n) (fieldsM n)
      apply (image _ pairM).2
      exact ⟨natSetCode n, naturalM n, natSetCode_mem_omega n,
        (M.realize_historyFieldPairFormula 0 1 2 j _
          (Fin.cases (naturalM n) (Fin.cases pairM paramsM)) states entries n rfl).2 rfl⟩
  have exactEntries (n : Nat) (y : ZFSet.{u}) :
      ZFSet.pair (natSetCode n) y ∈ family ↔ y = (states n).field j := by
    rw [allEntries]
    constructor
    · rintro ⟨m, equal⟩
      obtain ⟨index, value⟩ := ZFSet.pair_inj.1 equal
      have same : n = m := natSetCode_injective index
      exact same ▸ value
    · intro equal
      exact ⟨n, congrArg (ZFSet.pair (natSetCode n)) equal⟩
  refine ⟨family, hFamily, ⟨⋃₀ ⋃₀ family, ?_, ?_⟩, exactEntries⟩
  · intro z member
    obtain ⟨n, rfl⟩ := (allEntries z).1 member
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, pair_second_mem_doubleUnion member⟩
  · intro x hx
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
    refine ⟨(states n).field j, (exactEntries n _).2 rfl, ?_⟩
    intro y hy
    exact (exactEntries n y).1 hy

theorem exists_groundStateFieldUnion
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    {history : ZFSet.{u}} (hHistory : history ∈ M.sets)
    (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = (states n).code)
    (j : Fin 13) :
    ∃ family ∈ M.sets, ∃ range ∈ M.sets, ∃ union ∈ M.sets,
      FunctionGraphOn ZFSet.omega family ∧
      (∀ n y, ZFSet.pair (natSetCode n) y ∈ family ↔ y = (states n).field j) ∧
      (∀ y, y ∈ range ↔ ∃ n, y = (states n).field j) ∧
      union = ⋃₀ range ∧ (∀ x, x ∈ union ↔ ∃ n, x ∈ (states n).field j) := by
  obtain ⟨family, hFamily, function, exactEntries⟩ :=
    M.exists_groundStateFieldFamily pairing separation collection hω hHistory states entries j
  let range := relationImage ZFSet.omega (⋃₀ ⋃₀ family) family
  have hRange := M.relationImage_mem separation hω (M.union_mem unions (M.union_mem unions hFamily)) hFamily
  have exactRange (y : ZFSet.{u}) : y ∈ range ↔ ∃ n, y = (states n).field j := by
    rw [mem_relationImage]
    constructor
    · rintro ⟨_, x, hx, entry⟩
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
      exact ⟨n, (exactEntries n y).1 entry⟩
    · rintro ⟨n, equal⟩
      have entry := (exactEntries n y).2 equal
      exact ⟨pair_second_mem_doubleUnion entry, natSetCode n, natSetCode_mem_omega n, entry⟩
  refine ⟨family, hFamily, range, hRange, ⋃₀ range, M.union_mem unions hRange,
    function, exactEntries, exactRange, rfl, ?_⟩
  intro x
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨field, member, hx⟩
    obtain ⟨n, equal⟩ := (exactRange field).1 member
    exact ⟨n, equal ▸ hx⟩
  · rintro ⟨n, hx⟩
    exact ⟨(states n).field j, (exactRange _).2 ⟨n, rfl⟩, hx⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionOrigins
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem injection {D C f : Nat → ZFSet.{u}} {U V F : ZFSet.{u}}
    (domain : NatUnionCode D U) (range : NatUnionCode C V) (graph : NatUnionCode f F)
    (injections : ∀ n, InjectionCode (D n) (C n) (f n))
    (graphMono : ∀ n m, n ≤ m → f n ⊆ f m) : InjectionCode U V F := by
  refine ⟨domain.isFunc range graph (fun n => (injections n).function) graphMono, ?_⟩
  intro x y z first second
  obtain ⟨n, hn⟩ := (graph _).1 first
  obtain ⟨m, hm⟩ := (graph _).1 second
  exact (injections (max n m)).injective x y z
    (graphMono n _ (le_max_left n m) hn) (graphMono m _ (le_max_right n m) hm)

theorem meetEmbedding {D C rD rC μD μC f : Nat → ZFSet.{u}}
    {U V RU RV MU MV F : ZFSet.{u}}
    (domain : NatUnionCode D U) (range : NatUnionCode C V)
    (domainOrder : NatUnionCode rD RU) (rangeOrder : NatUnionCode rC RV)
    (domainMeet : NatUnionCode μD MU) (rangeMeet : NatUnionCode μC MV)
    (graph : NatUnionCode f F)
    (embeddings : ∀ n, MeetEmbeddingCode (D n) (C n) (rD n) (rC n) (μD n) (μC n) (f n))
    (graphMono : ∀ n m, n ≤ m → f n ⊆ f m)
    (orderMono : ∀ n m, n ≤ m → rD n ⊆ rD m)
    (meetMono : ∀ n m, n ≤ m → μD n ⊆ μD m) :
    MeetEmbeddingCode U V RU RV MU MV F := by
  refine ⟨domain.injection range graph (fun n => (embeddings n).injection) graphMono, ?_, ?_⟩
  · intro x y x' y' lower first second
    obtain ⟨n, hn⟩ := (domainOrder _).1 lower
    obtain ⟨j, hj⟩ := (graph _).1 first
    obtain ⟨k, hk⟩ := (graph _).1 second
    let m := max n (max j k)
    have nle : n ≤ m := le_max_left _ _
    have jle : j ≤ m := (le_max_left j k).trans (le_max_right n _)
    have kle : k ≤ m := (le_max_right j k).trans (le_max_right n _)
    exact rangeOrder.subset m ((embeddings m).monotone x y x' y'
      (orderMono n m nle hn) (graphMono j m jle hj) (graphMono k m kle hk))
  · intro x y z x' y' z' meet first second third
    obtain ⟨n, hn⟩ := (domainMeet _).1 meet
    obtain ⟨i, hi⟩ := (graph _).1 first
    obtain ⟨j, hj⟩ := (graph _).1 second
    obtain ⟨k, hk⟩ := (graph _).1 third
    let m := max n (max i (max j k))
    have nle : n ≤ m := le_max_left _ _
    have ile : i ≤ m := (le_max_left i _).trans (le_max_right n _)
    have jle : j ≤ m := ((le_max_left j k).trans (le_max_right i _)).trans (le_max_right n _)
    have kle : k ≤ m := ((le_max_right j k).trans (le_max_right i _)).trans (le_max_right n _)
    exact rangeMeet.subset m ((embeddings m).map_meet x y z x' y' z'
      (meetMono n m nle hn) (graphMono i m ile hi) (graphMono j m jle hj) (graphMono k m kle hk))

theorem shift {stages : Nat → ZFSet.{u}} {union : ZFSet.{u}}
    (code : NatUnionCode stages union) (first : stages 0 ⊆ stages 1) :
    NatUnionCode (fun n => stages (n + 1)) union := by
  intro x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (code x).1 hx
    cases n with
    | zero => exact ⟨0, first hn⟩
    | succ n => exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact code.subset (n + 1) hn

end PartitionPilot.Forcing.NatUnionCode



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem canonical_iterate_profile {c e K F : ZFSet.{u}}
    (hc : c ∈ state.data.currentCarrier) (he : e ∈ state.data.currentCarrier)
    (hK : K ∈ state.data.currentCarrier) (subset : F ⊆ state.data.currentCarrier)
    (nonempty : ∃ f, f ∈ F)
    (profile : CodedInsertionProfile state.data.currentCarrier state.data.currentOrder
      state.data.currentMeet c e K F)
    (separated : ZFSet.pair e K ∉ state.data.currentOrder) (n : Nat) :
    CodedInsertionProfile (state.data.iterate M I Sources Reps G T n).currentCarrier
      (state.data.iterate M I Sources Reps G T n).currentOrder
      (state.data.iterate M I Sources Reps G T n).currentMeet c e K F := by
  induction n with
  | zero => exact profile
  | succ n ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT (n + 1)
    have coherent := state.canonical_iterate_coherent pairing unions powers separation
      hI hSources hReps hG hT (Nat.zero_le n)
    have hcOld : c ∈ current.data.D := by
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor]
        using coherent.currentCarrier hc
    have heOld : e ∈ current.data.D := by
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor]
        using coherent.currentCarrier he
    have hKOld : K ∈ current.data.D := by
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor]
        using coherent.currentCarrier hK
    have subsetOld : F ⊆ current.data.D := by
      intro f hf
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor]
        using coherent.currentCarrier (subset hf)
    have profileOld : CodedInsertionProfile current.data.D current.data.rD current.data.μD c e K F := by
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor] using ih
    have separatedOld : ZFSet.pair e K ∉ current.data.rD := by
      intro below
      have later : ZFSet.pair e K ∈ (state.data.iterate M I Sources Reps G T n).currentOrder := by
        simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor] using below
      exact separated ((coherent.currentOrder e he K hK).1 later)
    have result := current.batch.insertion_profile_persists hcOld heOld hKOld
      subsetOld nonempty profileOld separatedOld
    change CodedInsertionProfile current.data.currentCarrier current.data.currentOrder
      current.data.currentMeet c e K F at result
    simpa only [equal] using result

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundUnion
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    Nonempty (GroundCompressionUnionData M state.data I Sources Reps G m one T) := by
  classical
  let stages := state.data.iterate M I Sources Reps G T
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  have allFields : ∀ j : Fin 13, ∃ U ∈ M.sets,
      NatUnionCode (fun n => (stages n).field j) U := by
    intro j
    obtain ⟨_, _, _, _, U, hU, _, _, _, _, exactUnion⟩ :=
      M.exists_groundStateFieldUnion pairing unions separation collection
        (M.omega_mem separation infinite) hHistory stages entries j
    exact ⟨U, hU, exactUnion⟩
  choose fields ground exactFields using allFields
  have codes := state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT
  have mono {n k : Nat} (h : n ≤ k) :=
    state.canonical_iterate_graphs_mono pairing unions powers separation hI hSources hReps hG hT h
  have carrierUnion : NatUnionCode (fun n => (stages n).D) (fields 0) := exactFields 0
  have orderUnion : NatUnionCode (fun n => (stages n).rD) (fields 1) := exactFields 1
  have meetUnion : NatUnionCode (fun n => (stages n).μD) (fields 2) := exactFields 2
  have actionUnion : NatUnionCode (fun n => (stages n).A) (fields 12) := exactFields 12
  have currentCarrier : NatUnionCode (fun n => (stages n).currentCarrier) (fields 0) :=
    carrierUnion.shift (mono (Nat.zero_le 1)).1
  have currentOrder : NatUnionCode (fun n => (stages n).currentOrder) (fields 1) :=
    orderUnion.shift (mono (Nat.zero_le 1)).2.1
  have currentMeet : NatUnionCode (fun n => (stages n).currentMeet) (fields 2) :=
    meetUnion.shift (mono (Nat.zero_le 1)).2.2.1
  have unionMeet : MeetOrderCode (fields 0) (fields 1) (fields 2) :=
    carrierUnion.meetOrder orderUnion meetUnion (fun n => (codes n).1)
      (fun _ _ h => (mono h).1) (fun _ _ h => (mono h).2.1) (fun _ _ h => (mono h).2.2.1)
  have unionAction : PosetActionCode G (fields 0) m one (fields 1) (fields 12) :=
    currentCarrier.posetAction currentOrder actionUnion (fun n => (codes n).2.2.1)
      (fun _ _ h => (mono h).2.2.2.2.1) (fun _ _ h => (mono h).2.2.2.2.2.2.1)
  exact ⟨⟨fields, ground, exactFields, currentCarrier, currentOrder, currentMeet, unionMeet, unionAction⟩⟩

end GroundCompressionState

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)

theorem union_original_subset : P0 ⊆ data.fields 0 := by
  intro x hx
  exact (data.fieldUnion 0).subset 0 (state.invariant.originalSubset hx)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_order_iff (n : Nat) {x y : ZFSet.{u}}
    (hx : x ∈ (state.data.iterate M I Sources Reps G T n).D)
    (hy : y ∈ (state.data.iterate M I Sources Reps G T n).D) :
    ZFSet.pair x y ∈ data.fields 1 ↔ ZFSet.pair x y ∈ (state.data.iterate M I Sources Reps G T n).rD :=
  (data.fieldUnion 1).order_entry_iff
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation hI hSources hReps hG hT h).2.1)
    (fun _ _ h => (state.canonical_iterate_coherent pairing unions powers separation hI hSources hReps hG hT h).order)
    n hx hy

theorem union_meet_iff (n : Nat) {x y z : ZFSet.{u}}
    (hx : x ∈ (state.data.iterate M I Sources Reps G T n).D)
    (hy : y ∈ (state.data.iterate M I Sources Reps G T n).D) :
    ZFSet.pair (ZFSet.pair x y) z ∈ data.fields 2 ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ (state.data.iterate M I Sources Reps G T n).μD :=
  (data.fieldUnion 2).meet_entry_iff data.meet
    (fun n => (state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT n).1) n hx hy

theorem union_action_iff (n : Nat) {g x y : ZFSet.{u}}
    (hx : x ∈ (state.data.iterate M I Sources Reps G T n).currentCarrier) :
    ZFSet.pair (ZFSet.pair g x) y ∈ data.fields 12 ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ (state.data.iterate M I Sources Reps G T n).A :=
  (data.fieldUnion 12).action_entry_iff data.action
    (fun n => (state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT n).2.2.1) n hx

theorem union_original_order_iff {x y : ZFSet.{u}} (hx : x ∈ P0) (hy : y ∈ P0) :
    ZFSet.pair x y ∈ data.fields 1 ↔ ZFSet.pair x y ∈ r0 :=
  (state.union_order_iff data pairing unions powers separation hI hSources hReps hG hT 0
    (state.invariant.originalSubset hx) (state.invariant.originalSubset hy)).trans
      (state.invariant.originalOrder x hx y hy)

theorem union_original_meet_iff {x y z : ZFSet.{u}} (hx : x ∈ P0) (hy : y ∈ P0) :
    ZFSet.pair (ZFSet.pair x y) z ∈ data.fields 2 ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ0 :=
  (state.union_meet_iff data pairing unions powers separation hI hSources hReps hG hT 0
    (state.invariant.originalSubset hx) (state.invariant.originalSubset hy)).trans
      (state.invariant.originalMeet x hx y hy z)

theorem union_original_action_iff {g x y : ZFSet.{u}} (hx : x ∈ P0) :
    ZFSet.pair (ZFSet.pair g x) y ∈ data.fields 12 ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A0 :=
  (state.union_action_iff data pairing unions powers separation hI hSources hReps hG hT 0
    (old_mem_taggedExtension (state.invariant.originalSubset hx))).trans
      (state.invariant.originalAction g x hx y)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
universe u

namespace GroundCompressionState
open SetFormula
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_original_agreement {g h v : ZFSet.{u}} (hg : g ∈ G) (hh : h ∈ G) (hv : v ∈ P0)
    (agreement : ActionAgreementBelow P0 r0 A0 g h v) :
    ActionAgreementBelow (data.fields 0) (data.fields 1) (data.fields 12) g h v := by
  intro x _ y _ below
  obtain ⟨n, lower⟩ := (data.currentOrder _).1 below
  have codes := state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT n
  have hx := (ZFSet.pair_mem_prod.1 (codes.2.1.order.relation lower)).1
  have finiteAgreement : ActionAgreementBelow
      (state.data.iterate M I Sources Reps G T n).currentCarrier
      (state.data.iterate M I Sources Reps G T n).currentOrder
      (state.data.iterate M I Sources Reps G T n).A g h v := by
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    have agree := current.invariant.agreement g hg h hh v hv agreement
    change ActionAgreementBelow current.data.currentCarrier current.data.currentOrder current.data.A g h v at agree
    simpa only [equal] using agree
  have restrict (k : ZFSet.{u}) := state.union_action_iff data pairing unions powers separation
    hI hSources hReps hG hT n (g := k) (y := y) hx
  constructor
  · intro entry
    have first := (restrict g).1 entry
    have hy := (ZFSet.pair_mem_prod.1 (codes.2.2.1.function.1 first)).2
    exact (restrict h).2 ((finiteAgreement x hx y hy lower).1 first)
  · intro entry
    have second := (restrict h).1 entry
    have hy := (ZFSet.pair_mem_prod.1 (codes.2.2.1.function.1 second)).2
    exact (restrict g).2 ((finiteAgreement x hx y hy lower).2 second)

theorem union_original_data :
    CompressionOriginalData P0 r0 μ0 A0 G (data.fields 0) (data.fields 1) (data.fields 2) (data.fields 12) :=
  ⟨state.union_original_subset data,
    fun _ hx _ hy => state.union_original_order_iff data pairing unions powers separation hI hSources hReps hG hT hx hy,
    fun _ hx _ hy _ => state.union_original_meet_iff data pairing unions powers separation hI hSources hReps hG hT hx hy,
    fun _ _ hx _ => state.union_original_action_iff data pairing unions powers separation hI hSources hReps hG hT hx,
    fun _ hg _ hh _ hv agree => state.union_original_agreement data pairing unions powers separation
      hI hSources hReps hG hT hg hh hv agree⟩

end GroundCompressionState






namespace GroundCompressionOrigin
open SetFormula
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)

include origin in
theorem union_original_data
    (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    CompressionOriginalData P0 r0 μ0 A0 G (data.fields 0) (data.fields 1) (data.fields 2) (data.fields 12) := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  exact state.union_original_data data pairing unions powers separation hI hSources hReps hG hT

end GroundCompressionOrigin

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompressionUnionBaseFilling
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem mapFamilySection_union {D C families : Nat → ZFSet.{u}}
    {I U V allFamilies : ZFSet.{u}}
    (domain : NatUnionCode D U) (range : NatUnionCode C V)
    (familyUnion : NatUnionCode families allFamilies)
    (maps : ∀ n, FunctionGraphOn I (families n))
    (functions : ∀ n i f, ZFSet.pair i f ∈ families n → ZFSet.IsFunc (D n) (C n) f)
    (i : {i : ZFSet.{u} // i ∈ I}) :
    NatUnionCode (fun n => (maps n).value i)
      (indexedRelationSection U V (mapFamilyApplicationGraph I U V allFamilies) i.val) := by
  intro z
  constructor
  · intro member
    obtain ⟨x, _, y, _, rfl, entry⟩ := (mem_indexedRelationSection _ _ _ _ _).1 member
    obtain ⟨_, _, _, f, indexed, value⟩ := (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).1 entry
    obtain ⟨n, oldIndexed⟩ := (familyUnion _).1 indexed
    have equal := (maps n).value_eq_of_entry i oldIndexed
    refine ⟨n, ?_⟩
    change ZFSet.pair x y ∈ (maps n).value i
    rw [equal]
    exact value
  · rintro ⟨n, member⟩
    have indexed := (maps n).value_entry i
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((functions n i.val _ indexed).1 member)
    apply (pair_mem_indexedRelationSection _ _ _ _ _ _).2
    refine ⟨domain.subset n hx, range.subset n hy, ?_⟩
    exact (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).2
      ⟨i.property, domain.subset n hx, range.subset n hy, (maps n).value i,
        familyUnion.subset n indexed, member⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_groundMapUnionFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {D C families : Nat → ZFSet.{u}} {I U V allFamilies : ZFSet.{u}}
    (hI : I ∈ M.sets) (hU : U ∈ M.sets) (hV : V ∈ M.sets) (hFamilies : allFamilies ∈ M.sets)
    (domain : NatUnionCode D U) (range : NatUnionCode C V)
    (familyUnion : NatUnionCode families allFamilies)
    (maps : ∀ n, FunctionGraphOn I (families n))
    (functions : ∀ n i f, ZFSet.pair i f ∈ families n → ZFSet.IsFunc (D n) (C n) f) :
    ∃ result ∈ M.sets, FunctionGraphOn I result ∧
      ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ f, ZFSet.pair i.val f ∈ result →
        NatUnionCode (fun n => (maps n).value i) f := by
  let flat := mapFamilyApplicationGraph I U V allFamilies
  have hFlat := M.mapFamilyApplicationGraph_mem pairing unions powers separation hI hU hV hFamilies
  obtain ⟨hResult, resultFunction, entries⟩ :=
    M.indexedRelationSections_spec pairing unions powers separation hI hU hV hFlat
  refine ⟨M.indexedRelationSections I U V flat, hResult, ⟨_, resultFunction⟩, ?_⟩
  intro i f entry
  have equal := ((entries i.val f).1 entry).2
  rw [equal]
  exact mapFamilySection_union domain range familyUnion maps functions i

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMeetEmbeddingUnionFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {D C rD rC μD μC families : Nat → ZFSet.{u}}
    {I U V RU RV MU MV allFamilies : ZFSet.{u}}
    (hI : I ∈ M.sets) (hU : U ∈ M.sets) (hV : V ∈ M.sets) (hFamilies : allFamilies ∈ M.sets)
    (domain : NatUnionCode D U) (range : NatUnionCode C V)
    (domainOrder : NatUnionCode rD RU) (rangeOrder : NatUnionCode rC RV)
    (domainMeet : NatUnionCode μD MU) (rangeMeet : NatUnionCode μC MV)
    (familyUnion : NatUnionCode families allFamilies)
    (maps : ∀ n, FunctionGraphOn I (families n))
    (embeddings : ∀ n i f, ZFSet.pair i f ∈ families n →
      MeetEmbeddingCode (D n) (C n) (rD n) (rC n) (μD n) (μC n) f)
    (mapMono : ∀ n m, n ≤ m → ∀ i f g,
      ZFSet.pair i f ∈ families n → ZFSet.pair i g ∈ families m → f ⊆ g)
    (orderMono : ∀ n m, n ≤ m → rD n ⊆ rD m)
    (meetMono : ∀ n m, n ≤ m → μD n ⊆ μD m) :
    ∃ result ∈ M.sets, FunctionGraphOn I result ∧
      ∀ i f, ZFSet.pair i f ∈ result →
        MeetEmbeddingCode U V RU RV MU MV f ∧
        (∀ z, z ∈ f ↔ ∃ n, ∃ old, ZFSet.pair i old ∈ families n ∧ z ∈ old) ∧
        ∀ n old, ZFSet.pair i old ∈ families n → ∀ x ∈ D n, ∀ y,
          ZFSet.pair x y ∈ f ↔ ZFSet.pair x y ∈ old := by
  obtain ⟨result, hResult, resultFunction, sections⟩ :=
    M.exists_groundMapUnionFamily pairing unions powers separation hI hU hV hFamilies
      domain range familyUnion maps (fun n i f entry => (embeddings n i f entry).injection.function)
  refine ⟨result, hResult, resultFunction, ?_⟩
  intro i f entry
  have hi : i ∈ I := resultFunction.pair_source entry
  let task : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have graph := sections task f entry
  have finiteEmbedding (n : Nat) := embeddings n i _ ((maps n).value_entry task)
  have increasing : ∀ n m, n ≤ m → (maps n).value task ⊆ (maps m).value task :=
    fun n m lower => mapMono n m lower i _ _ ((maps n).value_entry task) ((maps m).value_entry task)
  have full := domain.meetEmbedding range domainOrder rangeOrder domainMeet rangeMeet
    graph finiteEmbedding increasing orderMono meetMono
  refine ⟨full, ?_, ?_⟩
  · intro z
    rw [graph z]
    constructor
    · rintro ⟨n, member⟩
      exact ⟨n, (maps n).value task, (maps n).value_entry task, member⟩
    · rintro ⟨n, old, indexed, member⟩
      have equal := (maps n).value_eq_of_entry task indexed
      refine ⟨n, ?_⟩
      change z ∈ (maps n).value task
      rw [equal]
      exact member
  · intro n old indexed x hx y
    have equal := (maps n).value_eq_of_entry task indexed
    exact (graph.function_entry_iff full.injection.function
      (fun n => (finiteEmbedding n).injection.function) n hx).trans
        (by rw [equal])

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundUnionMaps
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (union : GroundCompressionUnionData M state.data I Sources Reps G m one T) :
    ∃ maps ∈ M.sets, FunctionGraphOn I maps ∧
      ∀ i f, ZFSet.pair i f ∈ maps →
        MeetEmbeddingCode (union.fields 0) (union.fields 0) (union.fields 1) (union.fields 1)
          (union.fields 2) (union.fields 2) f ∧
        (∀ z, z ∈ f ↔ ∃ n, ∃ old,
          ZFSet.pair i old ∈ (state.data.iterate M I Sources Reps G T n).Maps ∧ z ∈ old) ∧
        ∀ n old, ZFSet.pair i old ∈ (state.data.iterate M I Sources Reps G T n).Maps →
          ∀ x ∈ (state.data.iterate M I Sources Reps G T n).D, ∀ y,
            ZFSet.pair x y ∈ f ↔ ZFSet.pair x y ∈ old := by
  have codes := state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT
  have mono {n k : Nat} (before : n ≤ k) :=
    state.canonical_iterate_graphs_mono pairing unions powers separation hI hSources hReps hG hT before
  exact M.exists_groundMeetEmbeddingUnionFamily pairing unions powers separation
    hI (union.ground 0) (union.ground 0) (union.ground 11)
    (union.fieldUnion 0) union.currentCarrier (union.fieldUnion 1) union.currentOrder
    (union.fieldUnion 2) union.currentMeet (union.fieldUnion 11)
    (fun n => (codes n).2.2.2.1) (fun n => (codes n).2.2.2.2)
    (fun _ _ before => (mono before).2.2.2.2.2.2.2)
    (fun _ _ before => (mono before).2.1) (fun _ _ before => (mono before).2.2.1)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundAlgebra
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    Nonempty (GroundCompressionAlgebra M state.data I Sources Reps G m one T) := by
  obtain ⟨union⟩ := state.exists_groundUnion pairing unions powers separation collection infinite
    hI hSources hReps hG hT
  obtain ⟨maps, ground, function, correct⟩ := state.exists_groundUnionMaps
    pairing unions powers separation hI hSources hReps hG hT union
  exact ⟨⟨union, maps, ground, function, fun i f entry => (correct i f entry).1,
    fun i f entry => (correct i f entry).2.1, fun i f entry => (correct i f entry).2.2⟩⟩

end GroundCompressionState

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_fresh_accounting
    (initial : FiniteCompressionAccounting P0 I Sources τ state.data) :
    ∀ x ∈ algebra.union.fields 0, x ∈ P0 ∨
      ∃ i ∈ I, ∃ f a k b, ∃ y ∈ algebra.union.fields 0,
        ZFSet.pair i f ∈ algebra.maps ∧ ZFSet.pair i a ∈ Sources ∧
        ZFSet.pair τ k ∈ f ∧ ZFSet.pair a b ∈ f ∧ ZFSet.pair y x ∈ f ∧
        ZFSet.pair x k ∈ algebra.union.fields 1 ∧ ZFSet.pair x b ∉ algebra.union.fields 1 := by
  intro x hx
  obtain ⟨n, hn⟩ := (algebra.union.currentCarrier x).1 hx
  rcases state.canonical_iterate_accounting pairing unions powers separation hI hSources hReps hG hT
    initial n x hn with original | accounted
  · exact Or.inl original
  · obtain ⟨i, hi, S, a, k, b, y, hy, indexed, source, cap, base, image, lower, outside⟩ := accounted
    obtain ⟨f, unionIndexed⟩ := algebra.function.total hi
    have finite := (state.canonical_iterate_codes pairing unions powers separation
      hI hSources hReps hG hT n).2.2.2.2 i S indexed
    have hb := (ZFSet.pair_mem_prod.1 (finite.injection.function.1 base)).2
    have reflect := algebra.union.currentOrder.order_entry_iff
      (fun _ _ before => (state.canonical_iterate_graphs_mono pairing unions powers separation
        hI hSources hReps hG hT before).2.2.2.2.1)
      (fun _ _ before => (state.canonical_iterate_coherent pairing unions powers separation
        hI hSources hReps hG hT before).currentOrder) n hn hb
    refine Or.inr ⟨i, hi, f, a, k, b, y, (algebra.union.fieldUnion 0).subset n hy,
      unionIndexed, source,
      (algebra.entries i f unionIndexed _).2 ⟨n, S, indexed, cap⟩,
      (algebra.entries i f unionIndexed _).2 ⟨n, S, indexed, base⟩,
      (algebra.entries i f unionIndexed _).2 ⟨n, S, indexed, image⟩,
      algebra.union.currentOrder.subset n lower, ?_⟩
    exact fun unionLower => outside (reflect.1 unionLower)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_map_equivariant {g i j f f' x y z : ZFSet.{u}}
    (transport : ZFSet.pair (ZFSet.pair g i) j ∈ T)
    (firstMap : ZFSet.pair i f ∈ algebra.maps) (secondMap : ZFSet.pair j f' ∈ algebra.maps)
    (first : ZFSet.pair x y ∈ f) (second : ZFSet.pair x z ∈ f') :
    ZFSet.pair (ZFSet.pair g y) z ∈ algebra.union.fields 12 := by
  have hx := (ZFSet.pair_mem_prod.1 ((algebra.embedding i f firstMap).injection.function.1 first)).1
  obtain ⟨n, hn⟩ := (algebra.union.fieldUnion 0 x).1 hx
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  obtain ⟨old, oldEntry⟩ := current.inputs.maps.total (algebra.function.pair_source firstMap)
  obtain ⟨old', oldEntry'⟩ := current.inputs.maps.total (algebra.function.pair_source secondMap)
  have canonicalOld : ZFSet.pair i old ∈ (state.data.iterate M I Sources Reps G T n).Maps := by
    simpa only [equal] using oldEntry
  have canonicalOld' : ZFSet.pair j old' ∈ (state.data.iterate M I Sources Reps G T n).Maps := by
    simpa only [equal] using oldEntry'
  have firstOld := (algebra.restrict i f firstMap n old canonicalOld x hn y).1 first
  have secondOld := (algebra.restrict j f' secondMap n old' canonicalOld' x hn z).1 second
  apply (algebra.union.fieldUnion 12).subset n
  have intertwined := current.task.intertwine g i j old old' x y z
    transport oldEntry oldEntry' firstOld secondOld
  rw [equal] at intertwined
  exact intertwined

theorem union_map_agrees_on_source {i f a g x y : ZFSet.{u}}
    (map : ZFSet.pair i f ∈ algebra.maps) (source : ZFSet.pair i a ∈ Sources)
    (representative : ZFSet.pair i g ∈ Reps)
    (below : ZFSet.pair x a ∈ algebra.union.fields 1) :
    ZFSet.pair x y ∈ f ↔ ZFSet.pair (ZFSet.pair g x) y ∈ algebra.union.fields 12 := by
  obtain ⟨n, lower⟩ := (algebra.union.fieldUnion 1 (ZFSet.pair x a)).1 below
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have lowerCurrent : ZFSet.pair x a ∈ current.data.rD := by
    rw [equal]
    exact lower
  have hx := (ZFSet.pair_mem_prod.1 (current.batch.oldOrder.order.relation lowerCurrent)).1
  have hxCanonical : x ∈ (state.data.iterate M I Sources Reps G T n).D := by
    simpa only [equal] using hx
  obtain ⟨old, oldEntry⟩ := current.inputs.maps.total (algebra.function.pair_source map)
  have canonicalOld : ZFSet.pair i old ∈ (state.data.iterate M I Sources Reps G T n).Maps := by
    simpa only [equal] using oldEntry
  have agreement : ZFSet.pair x y ∈ old ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ (state.data.iterate M I Sources Reps G T n).A := by
    simpa only [equal] using current.inputs.agreement i a g old x y
      source representative oldEntry hx lowerCurrent
  exact (algebra.restrict i f map n old canonicalOld x hxCanonical y).trans
    (agreement.trans (state.union_action_iff algebra.union pairing unions powers separation
      hI hSources hReps hG hT n (old_mem_taggedExtension hxCanonical)).symm)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)

theorem union_sources_function : ZFSet.IsFunc I (algebra.union.fields 0) Sources := by
  refine ⟨?_, seed.sources.2⟩
  intro z hz
  obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (seed.sources.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨hi, state.union_original_subset algebra.union ha⟩

theorem union_top_arguments_function :
    ZFSet.IsFunc I (algebra.union.fields 0) (constantFamilyGraph I τ) := by
  refine ⟨?_, (constantFamilyGraph_function I τ).2⟩
  intro z hz
  obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 ((constantFamilyGraph_function I τ).1 hz)
  have equal := ZFSet.mem_singleton.1 ha
  subst a
  exact ZFSet.pair_mem_prod.2 ⟨hi, state.union_original_subset algebra.union seed.top_mem⟩

theorem union_bases_function : ZFSet.IsFunc I (algebra.union.fields 0) algebra.bases :=
  familyEvaluationGraph_function algebra.function.to_isFunc (state.union_sources_function algebra)
    (fun i f entry => (algebra.embedding i f entry).injection.function)

theorem union_caps_function : ZFSet.IsFunc I (algebra.union.fields 0) (algebra.caps τ) :=
  familyEvaluationGraph_function algebra.function.to_isFunc (state.union_top_arguments_function algebra)
    (fun i f entry => (algebra.embedding i f entry).injection.function)

theorem union_base_entry_iff {i f a b : ZFSet.{u}} (map : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ Sources) :
    ZFSet.pair i b ∈ algebra.bases ↔ ZFSet.pair a b ∈ f := by
  rw [GroundCompressionAlgebra.bases,
    familyEvaluationGraph_entry_iff algebra.function.to_isFunc (state.union_sources_function algebra) map source]
  exact ⟨fun h => h.2, fun h => ⟨(ZFSet.pair_mem_prod.1
    ((algebra.embedding i f map).injection.function.1 h)).2, h⟩⟩

theorem union_cap_entry_iff {i f k : ZFSet.{u}} (map : ZFSet.pair i f ∈ algebra.maps) :
    ZFSet.pair i k ∈ algebra.caps τ ↔ ZFSet.pair τ k ∈ f := by
  have argument := (pair_mem_constantFamilyGraph I τ i τ).2
    ⟨(ZFSet.pair_mem_prod.1 (algebra.function.to_isFunc.1 map)).1, rfl⟩
  rw [GroundCompressionAlgebra.caps,
    familyEvaluationGraph_entry_iff algebra.function.to_isFunc (state.union_top_arguments_function algebra) map argument]
  exact ⟨fun h => h.2, fun h => ⟨(ZFSet.pair_mem_prod.1
    ((algebra.embedding i f map).injection.function.1 h)).2, h⟩⟩

theorem union_markings_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) :
    algebra.bases ∈ M.sets ∧ algebra.caps τ ∈ M.sets := by
  have hValues := M.union_mem unions (M.union_mem unions algebra.ground)
  have hτ := M.transitive state.ground.carrier (state.invariant.originalSubset seed.top_mem)
  exact ⟨M.familyEvaluationGraph_mem pairing unions powers separation hI (algebra.union.ground 0)
      (algebra.union.ground 0) hValues algebra.ground hSources,
    M.familyEvaluationGraph_mem pairing unions powers separation hI (algebra.union.ground 0)
      (algebra.union.ground 0) hValues algebra.ground
      (M.constantFamilyGraph_mem pairing unions powers separation hI hτ)⟩

end GroundCompressionState
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_top {x : ZFSet.{u}} (hx : x ∈ algebra.union.fields 0) :
    ZFSet.pair x τ ∈ algebra.union.fields 1 := by
  obtain ⟨n, hn⟩ := (algebra.union.fieldUnion 0 x).1 hx
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have hxCurrent : x ∈ current.data.D := by
    rw [equal]
    exact hn
  apply (algebra.union.fieldUnion 1).subset n
  have belowTop := current.invariant.top x hxCurrent
  rw [equal] at belowTop
  exact belowTop

theorem union_map_base_filling {i f a g b x : ZFSet.{u}}
    (map : ZFSet.pair i f ∈ algebra.maps) (source : ZFSet.pair i a ∈ Sources)
    (representative : ZFSet.pair i g ∈ Reps) (base : ZFSet.pair a b ∈ f)
    (hx : x ∈ algebra.union.fields 0) (below : ZFSet.pair x b ∈ algebra.union.fields 1) :
    ∃ y ∈ algebra.union.fields 0, ZFSet.pair y x ∈ f := by
  have hg := (ZFSet.pair_mem_prod.1 (state.inputs.representatives.1 representative)).2
  have ha := (ZFSet.pair_mem_prod.1 ((algebra.embedding i f map).injection.function.1 base)).1
  have actedBase := (state.union_map_agrees_on_source algebra pairing unions powers separation
    hI hSources hReps hG hT map source representative (algebra.union.meet.order.refl a ha)).1 base
  obtain ⟨y, hy, acted⟩ := algebra.union.action.raw_preimage state.inputs.group hg hx
  have belowSource := (algebra.union.action.raw_order_iff state.inputs.group
    algebra.union.meet.order hg acted actedBase).1 below
  exact ⟨y, hy, (state.union_map_agrees_on_source algebra pairing unions powers separation
    hI hSources hReps hG hT map source representative belowSource).2 acted⟩

theorem union_map_range_below_cap {i f k x y : ZFSet.{u}}
    (map : ZFSet.pair i f ∈ algebra.maps) (cap : ZFSet.pair τ k ∈ f)
    (image : ZFSet.pair x y ∈ f) : ZFSet.pair y k ∈ algebra.union.fields 1 := by
  have embedding := algebra.embedding i f map
  have hx := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 image)).1
  exact embedding.monotone x τ y k
    (state.union_top algebra pairing unions powers separation hI hSources hReps hG hT hx) image cap

end PartitionPilot.Forcing.GroundCompressionState

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundExternalRequestSetRecognition
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

theorem externalRequestKinds_function (I P Rectangles : ZFSet.{u}) :
    FunctionGraphOn (externalRequestCarrier I P Rectangles) (externalRequestKinds I P Rectangles) :=
  (show FunctionGraphOn (ZFSet.prod externalRequestTags (externalRequestPayloadBound I P Rectangles))
    (productFirst externalRequestTags (externalRequestPayloadBound I P Rectangles)) from
    ⟨_, productFirst_function _ _⟩).restrict (externalRequestCarrier_subset I P Rectangles)

theorem externalRequestPayloads_function (I P Rectangles : ZFSet.{u}) :
    FunctionGraphOn (externalRequestCarrier I P Rectangles) (externalRequestPayloads I P Rectangles) :=
  (show FunctionGraphOn (ZFSet.prod externalRequestTags (externalRequestPayloadBound I P Rectangles))
    (productSecond externalRequestTags (externalRequestPayloadBound I P Rectangles)) from
    ⟨_, productSecond_function _ _⟩).restrict (externalRequestCarrier_subset I P Rectangles)

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation

theorem externalRectangleBound_mem {P G : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets) :
    externalRectangleBound P G ∈ M.sets :=
  M.prod_mem pairing unions powers separation hP
    (M.prod_mem pairing unions powers separation hP
      (M.prod_mem pairing unions powers separation hP (M.prod_mem pairing unions powers separation hG hG)))

theorem externalRectangles_mem {P G r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets)
    (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) : externalRectangles P G r μ A ∈ M.sets := by
  let params := extend P (extend G (extend r (extend μ (extend A Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalRectanglesEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hP (Fin.cases hG (Fin.cases hr (Fin.cases hμ (Fin.cases hA (fun i => Fin.elim0 i))))))
    (M.externalRectangleBound_mem pairing unions powers separation hP hG)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalRectanglesEntryFormula 0 1 2 3 4 5) (extend z params))
      (externalRectangleBound P G) = externalRectangles P G r μ A := by
    apply ZFSet.ext
    intro z
    rw [externalRectangles, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalRectanglesEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

omit powers separation in
private theorem tag_mem (inhabited : M.sets.Nonempty) (n : Nat) : natSetCode n ∈ M.sets := by
  induction n with
  | zero => exact M.empty_mem inhabited
  | succ n ih => exact M.insert_mem pairing unions ih ih

omit unions powers separation in
private theorem singleton_mem {x : ZFSet.{u}} (hx : x ∈ M.sets) : ({x} : ZFSet.{u}) ∈ M.sets := by
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hx hx

theorem externalRequestCarrier_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalRequestCarrier I P Rectangles ∈ M.sets := by
  have tag := M.tag_mem pairing unions ⟨P, hP⟩
  exact M.binary_union_mem pairing unions
    (M.binary_union_mem pairing unions
      (M.prod_mem pairing unions powers separation (M.singleton_mem pairing (tag 0)) hI)
      (M.prod_mem pairing unions powers separation (M.singleton_mem pairing (tag 1)) hP))
    (M.prod_mem pairing unions powers separation (M.singleton_mem pairing (tag 2)) hRectangles)

theorem externalChildLetters_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalChildLetters I P Rectangles ∈ M.sets := by
  have tag := M.tag_mem pairing unions ⟨P, hP⟩
  exact M.binary_union_mem pairing unions
    (M.prod_mem pairing unions powers separation
      (M.externalRequestCarrier_mem pairing unions powers separation hI hP hRectangles)
      (M.singleton_mem pairing (tag 0)))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation (M.singleton_mem pairing (tag 2)) hRectangles)
      (M.singleton_mem pairing (tag 1)))

omit powers separation in
private theorem fieldBounds_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalRequestTags ∈ M.sets ∧ externalRequestPayloadBound I P Rectangles ∈ M.sets := by
  have tag := M.tag_mem pairing unions ⟨P, hP⟩
  exact ⟨M.insert_mem pairing unions (tag 0)
      (M.insert_mem pairing unions (tag 1) (M.singleton_mem pairing (tag 2))),
    M.binary_union_mem pairing unions (M.binary_union_mem pairing unions hI hP) hRectangles⟩

theorem externalRequestKinds_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalRequestKinds I P Rectangles ∈ M.sets := by
  have bounds := M.fieldBounds_mem pairing unions hI hP hRectangles
  exact M.graphRestriction_mem unions separation
    (M.externalRequestCarrier_mem pairing unions powers separation hI hP hRectangles)
    (M.productFirst_mem pairing unions powers separation bounds.1 bounds.2)

theorem externalRequestPayloads_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalRequestPayloads I P Rectangles ∈ M.sets := by
  have bounds := M.fieldBounds_mem pairing unions hI hP hRectangles
  exact M.graphRestriction_mem unions separation
    (M.externalRequestCarrier_mem pairing unions powers separation hI hP hRectangles)
    (M.productSecond_mem pairing unions powers separation bounds.1 bounds.2)

theorem groundExternalRequestData {I P G r μ A : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) :
    let Rectangles := externalRectangles P G r μ A
    let Requests := externalRequestCarrier I P Rectangles
    Rectangles ∈ M.sets ∧ Requests ∈ M.sets ∧ externalChildLetters I P Rectangles ∈ M.sets ∧
      externalRequestKinds I P Rectangles ∈ M.sets ∧
      externalRequestPayloads I P Rectangles ∈ M.sets ∧
      FunctionGraphOn Requests (externalRequestKinds I P Rectangles) ∧
      FunctionGraphOn Requests (externalRequestPayloads I P Rectangles) := by
  dsimp only
  have rectangles := M.externalRectangles_mem pairing unions powers separation hP hG hr hμ hA
  exact ⟨rectangles, M.externalRequestCarrier_mem pairing unions powers separation hI hP rectangles,
    M.externalChildLetters_mem pairing unions powers separation hI hP rectangles,
    M.externalRequestKinds_mem pairing unions powers separation hI hP rectangles,
    M.externalRequestPayloads_mem pairing unions powers separation hI hP rectangles,
    externalRequestKinds_function I P _, externalRequestPayloads_function I P _⟩

end TransitiveGround

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionBirthData
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing
universe u

theorem firstAppearanceBirth_subset (U T Ps stamps oldBirth : ZFSet.{u}) :
    firstAppearanceBirth U T Ps stamps oldBirth ⊆ ZFSet.prod U T :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem pair_mem_firstAppearanceBirth (U T Ps stamps oldBirth x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ firstAppearanceBirth U T Ps stamps oldBirth ↔
      x ∈ U ∧ t ∈ T ∧ (ZFSet.pair x t ∈ oldBirth ∨ ∃ n ∈ ZFSet.omega, ∃ D E,
        ZFSet.pair n D ∈ Ps ∧ ZFSet.pair (insert n n) E ∈ Ps ∧
          ZFSet.pair n t ∈ stamps ∧ x ∈ E ∧ x ∉ D) := by
  rw [firstAppearanceBirth, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, ht⟩, old | ⟨n, hn, D, E, y, s, equal, before, after, stamp, fresh⟩⟩
    · exact ⟨hx, ht, Or.inl old⟩
    · obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
      exact ⟨hx, ht, Or.inr ⟨n, hn, D, E, before, after, stamp, fresh⟩⟩
  · rintro ⟨hx, ht, old | ⟨n, hn, D, E, before, after, stamp, fresh⟩⟩
    · exact ⟨⟨hx, ht⟩, Or.inl old⟩
    · exact ⟨⟨hx, ht⟩, Or.inr ⟨n, hn, D, E, x, t, rfl, before, after, stamp, fresh⟩⟩

theorem firstAppearanceBirth_nat_iff {U T Ps stamps oldBirth : ZFSet.{u}}
    (P stamp : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (times : ∀ n t, ZFSet.pair (natSetCode n) t ∈ stamps ↔ t = stamp n)
    (x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ firstAppearanceBirth U T Ps stamps oldBirth ↔
      x ∈ U ∧ t ∈ T ∧ (ZFSet.pair x t ∈ oldBirth ∨
        ∃ n, x ∈ P (n + 1) ∧ x ∉ P n ∧ t = stamp n) := by
  rw [pair_mem_firstAppearanceBirth]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨n, hn, D, E, before, after, stampEntry, hx, outside⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have oldEq := (domains k D).1 before
    have newEq := (domains (k + 1) E).1 after
    exact ⟨k, newEq ▸ hx, oldEq ▸ outside, (times k t).1 stampEntry⟩
  · rintro ⟨n, hx, outside, equal⟩
    exact ⟨natSetCode n, natSetCode_mem_omega n, P n, P (n + 1),
      (domains n _).2 rfl, (domains (n + 1) _).2 rfl, (times n t).2 equal, hx, outside⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_firstAppearanceBirthEntryFormula {k}
    (z omega u t domains stamps old bound : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (firstAppearanceBirthEntryFormula z omega u t domains stamps old bound) env ↔
      env z ∈ env old ∨ ∃ n ∈ env omega, ∃ m ∈ env omega,
        ∃ D ∈ env bound, ∃ E ∈ env bound, ∃ x ∈ env u, ∃ a ∈ env t,
          env z = ZFSet.pair x a ∧ m = insert n n ∧ ZFSet.pair n D ∈ env domains ∧
            ZFSet.pair m E ∈ env domains ∧ ZFSet.pair n a ∈ env stamps ∧ x ∈ E ∧ x ∉ D := by
  simp only [firstAppearanceBirthEntryFormula, truth_disj, truth_exMem, Truth,
    truth_orderedPairFormula, truth_successorFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem firstAppearanceBirth_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps stamps oldBirth : ZFSet.{u}}
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hU : U ∈ M.sets) (hT : T ∈ M.sets) (hPs : Ps ∈ M.sets)
    (hStamps : stamps ∈ M.sets) (hOld : oldBirth ∈ M.sets) :
    firstAppearanceBirth U T Ps stamps oldBirth ∈ M.sets := by
  have hBound := M.union_mem unions (M.union_mem unions hPs)
  let params := extend ZFSet.omega (extend U (extend T (extend Ps (extend stamps
    (extend oldBirth (extend (⋃₀ ⋃₀ Ps) Fin.elim0))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.firstAppearanceBirthEntryFormula 0 1 2 3 4 5 6 7) params
    (Fin.cases hω (Fin.cases hU (Fin.cases hT (Fin.cases hPs (Fin.cases hStamps
      (Fin.cases hOld (Fin.cases hBound (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation hU hT)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.firstAppearanceBirthEntryFormula 0 1 2 3 4 5 6 7) (extend z params))
      (ZFSet.prod U T) = firstAppearanceBirth U T Ps stamps oldBirth := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, firstAppearanceBirth, ZFSet.mem_sep,
      BoundedFormula.truth_firstAppearanceBirthEntryFormula]
    change (_ ∧ (z ∈ oldBirth ∨ _)) ↔ _
    apply and_congr_right
    intro bound
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨n, hn, m, _, D, _, E, _, x, _, t, _, pair, successor, before, after, stamp, fresh⟩
      rw [successor] at after
      exact ⟨n, hn, D, E, x, t, pair, before, after, stamp, fresh⟩
    · rintro ⟨n, hn, D, E, x, t, rfl, before, after, stamp, fresh⟩
      have successorMem : insert n n ∈ ZFSet.omega := by
        obtain ⟨j, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
        exact natSetCode_mem_omega (j + 1)
      have points := ZFSet.pair_mem_prod.1 bound
      exact ⟨n, hn, insert n n, successorMem, D, pair_second_mem_doubleUnion before,
        E, pair_second_mem_doubleUnion after, x, points.1, t, points.2,
        rfl, rfl, before, after, stamp, fresh⟩
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

namespace NatBirthExtensionCode
variable {P stamp : Nat → ZFSet.{u}} {old birth U T : ZFSet.{u}}

variable (code : NatBirthExtensionCode P stamp old birth)
include code

theorem restriction_union (carrier : NatUnionCode P U)
    (born : ZFSet.IsFunc (P 0) T old) :
    NatUnionCode (fun n => graphRestriction (P n) birth) birth := by
  intro z
  constructor
  · intro hz
    obtain ⟨x, t, rfl⟩ := code.shape z hz
    have hx : x ∈ U := by
      rcases (code.entries x t).1 hz with original | ⟨n, hn, _, _⟩
      · exact carrier.subset 0 (ZFSet.pair_mem_prod.1 (born.1 original)).1
      · exact carrier.subset (n + 1) hn
    obtain ⟨n, hn⟩ := (carrier x).1 hx
    exact ⟨n, pair_mem_graphRestriction.2 ⟨hz, hn⟩⟩
  · rintro ⟨n, hn⟩
    exact graphRestriction_subset (P n) birth hn

end NatBirthExtensionCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem firstAppearanceBirth_code {U T Ps stamps oldBirth : ZFSet.{u}}
    (P stamp : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (times : ∀ n t, ZFSet.pair (natSetCode n) t ∈ stamps ↔ t = stamp n)
    (carrier : NatUnionCode P U) (born : ZFSet.IsFunc (P 0) T oldBirth)
    (inRange : ∀ n, stamp n ∈ T) :
    NatBirthExtensionCode P stamp oldBirth (firstAppearanceBirth U T Ps stamps oldBirth) := by
  constructor
  · intro z entry
    obtain ⟨x, _, t, _, equal⟩ :=
      ZFSet.mem_prod.1 (firstAppearanceBirth_subset U T Ps stamps oldBirth entry)
    exact ⟨x, t, equal⟩
  · intro x t
    rw [firstAppearanceBirth_nat_iff P stamp domains times]
    constructor
    · exact fun entry => entry.2.2
    · intro entry
      have bounds : x ∈ U ∧ t ∈ T := by
        rcases entry with before | ⟨n, hx, _, rfl⟩
        · have oldBounds := ZFSet.pair_mem_prod.1 (born.1 before)
          exact ⟨carrier.subset 0 oldBounds.1, oldBounds.2⟩
        · exact ⟨carrier.subset (n + 1) hx, inRange n⟩
      exact ⟨bounds.1, bounds.2, entry⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundFirstAppearanceBirth
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps stamps oldBirth : ZFSet.{u}}
    (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hU : U ∈ M.sets) (hT : T ∈ M.sets) (hPs : Ps ∈ M.sets)
    (hStamps : stamps ∈ M.sets) (hOld : oldBirth ∈ M.sets)
    (P stamp : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (times : ∀ n t, ZFSet.pair (natSetCode n) t ∈ stamps ↔ t = stamp n)
    (carrier : NatUnionCode P U) (born : ZFSet.IsFunc (P 0) T oldBirth)
    (inRange : ∀ n, stamp n ∈ T) :
    ∃ birth ∈ M.sets, birth = firstAppearanceBirth U T Ps stamps oldBirth ∧
      NatBirthExtensionCode P stamp oldBirth birth :=
  ⟨firstAppearanceBirth U T Ps stamps oldBirth,
    M.firstAppearanceBirth_mem pairing unions powers separation hω hU hT hPs hStamps hOld,
    rfl, firstAppearanceBirth_code P stamp domains times carrier born inRange⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable {base stamps limit old birth : ZFSet.{u}}
variable (code : NatBirthExtensionCode (fun n => (state.data.iterate M I Sources Reps G T n).D)
    (compressionStamp base) old birth)
variable (born : ZFSet.IsFunc state.data.D limit old)
variable (times : CompressionStampCode base stamps limit)
include pairing unions powers separation hI hSources hReps hG hT code

include data born times in
theorem canonical_birth_oldMeet
    (oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base)
    (oldMeet : OldMeetCode state.data.rD state.data.μD old) (n : Nat) :
    OldMeetCode (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) := by
  induction n with
  | zero =>
    rw [code.restriction_zero
      (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
        hI hSources hReps hG hT h).1) born]
    exact oldMeet
  | succ n ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    have finite : ZFSet.IsFunc current.data.D limit
        (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) := by
      simpa only [equal] using state.canonical_birth_function data pairing unions powers separation
        hI hSources hReps hG hT code born times n
    have oldLaw : OldMeetCode current.data.rD current.data.μD
        (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) := by
      simpa only [equal] using ih
    have earlier (x t : ZFSet.{u})
        (h : ZFSet.pair x t ∈ graphRestriction (state.data.iterate M I Sources Reps G T n).D birth) :=
      state.canonical_birth_before_stamp pairing unions powers separation
        hI hSources hReps hG hT code oldBound n h
    have result := current.batch.batchBirth_oldMeet finite earlier oldLaw
    change OldMeetCode current.data.currentOrder current.data.currentMeet
      (taggedBirth current.data.D current.data.fresh
        (graphRestriction (state.data.iterate M I Sources Reps G T n).D birth)
        (compressionStamp base n)) at result
    rw [state.canonical_birth_step pairing unions powers separation hI hSources hReps hG hT code born n]
    simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor] using result

end PartitionPilot.Forcing.GroundCompressionState



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_CompressionExternalTileOverlaps
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

theorem externalCompressionField_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I V F : ZFSet.{u}} (hI : I ∈ M.sets) (hV : V ∈ M.sets) (hF : F ∈ M.sets) :
    externalCompressionField I V F ∈ M.sets := by
  have zero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨I, hI⟩
  have single : ({natSetCode 0} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing zero zero
  exact M.relationCompose_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation single hI) hI hV
    (M.productSecond_mem pairing unions powers separation single hI) hF

end TransitiveGround

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

theorem external_fields_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) :
    completion.externalMaps ∈ M.sets ∧ completion.externalCaps ∈ M.sets ∧
      FunctionGraphOn (ZFSet.prod {natSetCode 0} I) completion.externalMaps ∧
      ZFSet.IsFunc (ZFSet.prod {natSetCode 0} I) (completion.algebra.union.fields 0) completion.externalCaps :=
  ⟨M.externalCompressionField_mem pairing unions powers separation hI
      (M.union_mem unions (M.union_mem unions completion.algebra.ground)) completion.algebra.ground,
    M.externalCompressionField_mem pairing unions powers separation hI
      (completion.algebra.union.ground 0) completion.caps_ground,
    ⟨_, externalCompressionField_function completion.algebra.function.to_isFunc⟩,
    externalCompressionField_function completion.caps_function⟩

end GroundCompressionCompletion

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)

theorem completion_of_accounting
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (accounting : CompressionRangeAccounting P0 I (algebra.union.fields 0)
      (algebra.union.fields 1) (algebra.union.fields 2) algebra.maps algebra.bases (algebra.caps τ)) :
    Nonempty (GroundCompressionCompletion M state.data I Sources Reps G m one T τ) := by
  obtain ⟨basesGround, capsGround⟩ := state.union_markings_ground algebra
    pairing unions powers separation hI hSources
  refine ⟨{
    algebra := algebra
    bases_ground := basesGround
    caps_ground := capsGround
    bases_function := state.union_bases_function algebra
    caps_function := state.union_caps_function algebra
    top_mem := state.union_original_subset algebra.union seed.top_mem
    top := fun _ hx => state.union_top algebra pairing unions powers separation
      hI hSources hReps hG hT hx
    range := ?_
    equivariant := ?_
    source_agreement := ?_
  }⟩
  · intro i f k x indexed capped
    apply accounting.range_iff algebra.union.meet algebra.function algebra.embedding
      (state.union_bases_function algebra) (state.union_caps_function algebra) ?_
      (algebra.function.pair_source indexed) indexed capped
    intro j _ graph cap map capEntry y z image
    exact state.union_map_range_below_cap algebra pairing unions powers separation
      hI hSources hReps hG hT map ((state.union_cap_entry_iff algebra map).1 capEntry) image
  · intro g i j f h x y z transport firstMap secondMap first second
    exact state.union_map_equivariant algebra pairing unions powers separation
      hI hSources hReps hG hT transport firstMap secondMap first second
  · intro i f a g x y map source representative below
    exact state.union_map_agrees_on_source algebra pairing unions powers separation
      hI hSources hReps hG hT map source representative below

end PartitionPilot.Forcing.GroundCompressionState



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_InitialCompressionUnionProfiles
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace AttachmentBatchInputs
universe u
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

theorem original_positive_iff (i : {i : ZFSet.{u} // i ∈ I})
    (x : {p : ZFSet.{u} // p ∈ P} ⊕ d.templates.Fresh) :
    (∃ f ∈ d.filter i, ZFSet.pair f (d.coding.encode x) ∈ d.batchOrder) ↔
      Positive d.templates.extension (d.templates.originalFamily i) x := by
  constructor
  · rintro ⟨f, hf, lower⟩
    let old : {p : ZFSet.{u} // p ∈ P} := ⟨f, (d.fiber i).filter.subset hf⟩
    exact ⟨.inl old, hf, (d.coding.le_encode (.inl old) x).1 lower⟩
  · rintro ⟨f, hf, lower⟩
    cases f with
    | inl f => exact ⟨f.val, hf, (d.coding.le_encode (.inl f) x).2 lower⟩
    | inr f => exact False.elim hf

theorem initial_cap_profile (i : {i : ZFSet.{u} // i ∈ I}) (t : d.templates.Space i)
    (top : ∀ y, (d.templates.order i).le y t)
    (outside : ¬ (d.templates.order i).le t (d.templates.anchor i)) :
    let cap := d.coding.encode (.inr (d.templates.cap i t outside))
    CodedInsertionProfile d.batchCarrier d.batchOrder d.batchMeetGraph
      (d.templates.base i).val (d.separator i) cap (d.filter i) ∧
    ZFSet.pair (d.templates.base i).val cap ∈ d.batchOrder ∧
    ZFSet.pair cap (d.templates.base i).val ∉ d.batchOrder ∧
    ZFSet.pair (d.separator i) cap ∉ d.batchOrder := by
  dsimp only
  have profile := d.templates.initial_profile i t top outside
  have strict := d.templates.cap_strict_above_base i t top outside
  have separated := d.templates.separator_not_below_cap i t top outside
  refine ⟨?_, (d.coding.le_encode _ _).2 strict.1,
    fun lower => strict.2 ((d.coding.le_encode _ _).1 lower),
    fun lower => separated ((d.coding.le_encode _ _).1 lower)⟩
  intro v hv above
  obtain ⟨x, rfl⟩ := d.coding.encode_surjective v hv
  have aboveTyped := (d.coding.le_encode (.inl (d.templates.separator i)) x).1 above
  have result := profile x aboveTyped
  constructor
  · intro positive
    exact (d.coding.le_encode _ _).2 (result.1 ((d.original_positive_iff i x).1 positive))
  · intro negative
    have equal := result.2 (fun positive => negative ((d.original_positive_iff i x).2 positive))
    have entry := d.coding.encoded_meet_entry (.inr (d.templates.cap i t outside)) x
    rw [equal] at entry
    exact entry

end AttachmentBatchInputs

section
universe u

namespace AttachmentBatchInputs
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}

theorem fresh_shadow_separation
    (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)
    (i j : {i : ZFSet.{u} // i ∈ I}) {q t b c : ZFSet.{u}}
    (hq : q ∈ freshPart (d.space i) (d.rel i) (d.anchor i))
    (ht : t ∈ freshPart (d.space j) (d.rel j) (d.anchor j))
    (different : i ≠ j)
    (hb : ZFSet.pair (ZFSet.pair i.val q) b ∈ batchAttachmentShadowGraph I P Qs μs As Es)
    (hc : ZFSet.pair (ZFSet.pair j.val t) c ∈ batchAttachmentShadowGraph I P Qs μs As Es) :
    ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q)) c ∈ d.batchOrder ∨
    ZFSet.pair (ZFSet.pair P (ZFSet.pair j.val t)) b ∈ d.batchOrder ∨
    ∃ z, ZFSet.pair (ZFSet.pair (ZFSet.pair P (ZFSet.pair i.val q))
      (ZFSet.pair P (ZFSet.pair j.val t))) z ∈ d.batchMeetGraph ∧
      ZFSet.pair (ZFSet.pair b c) z ∈ d.batchMeetGraph := by
  classical
  have bP := (ZFSet.pair_mem_prod.1 (d.batch_shadow_function.1 hb)).2
  have cP := (ZFSet.pair_mem_prod.1 (d.batch_shadow_function.1 hc)).2
  by_cases first : c ∈ d.filter i
  · exact Or.inl ((d.batch_old_upper_iff i hq cP).2 first)
  by_cases second : b ∈ d.filter j
  · exact Or.inr (Or.inl ((d.batch_old_upper_iff j ht bP).2 second))
  have notIJ := fun lower => first ((d.batch_cross_lower_iff i j hq ht different hc).1 lower)
  have notJI := fun lower => second ((d.batch_cross_lower_iff j i ht hq different.symm hb).1 lower)
  let x : {p : ZFSet.{u} // p ∈ P} := ⟨b, bP⟩
  let y : {p : ZFSet.{u} // p ∈ P} := ⟨c, cP⟩
  refine Or.inr (Or.inr ⟨(d.oldOrder.toMeetOrder.meet x y).val, ?_, ?_⟩)
  · exact d.batch_cross_meet_code i j hq ht different hb hc
      (d.oldOrder.toMeetOrder_meet_entry x y) notIJ notJI
  · exact d.old_meet_entry (d.oldOrder.toMeetOrder_meet_entry x y)

end AttachmentBatchInputs

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})
variable {P G r μ A Labels m inv one T : ZFSet.{u}}
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (meet : MeetOrderCode P r μ) (hT : T ∈ P) (top : ∀ x ∈ P, ZFSet.pair x T ∈ r)
include group action meet hT top

theorem groundEligibleTask_old_below_cap_iff {i c v : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels) (hv : v ∈ P) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair v (eligibleTaskCap P T i) ∈ d.batchOrder ↔ ZFSet.pair v c ∈ d.batchOrder := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have fresh := M.groundEligibleTask_cap_fresh group action meet hT top hi
  have hq := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 fresh
  have shadow := M.groundEligibleTask_cap_shadow meet hT top hi target
  have hc := (ZFSet.pair_mem_prod.1 (d.batch_shadow_function.1 shadow)).2
  exact (d.batch_old_lower_iff j hq hv shadow).trans
    (d.coding.le_encode (.inl ⟨v, hv⟩) (.inl ⟨c, hc⟩)).symm

theorem groundEligibleTask_cap_separation {i j b c : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (hj : j ∈ M.groundEligibleTasks P G r μ A Labels) (different : i ≠ j)
    (targetI : ZFSet.pair i b ∈ literalTaskTargetGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels)
    (targetJ : ZFSet.pair j c ∈ literalTaskTargetGraph
      (M.groundEligibleTasks P G r μ A Labels) P (M.groundRelations P P)
      (M.groundMeetFilters P r μ) Labels) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair (eligibleTaskCap P T i) c ∈ d.batchOrder ∨
    ZFSet.pair (eligibleTaskCap P T j) b ∈ d.batchOrder ∨
    ∃ z, ZFSet.pair (ZFSet.pair (eligibleTaskCap P T i) (eligibleTaskCap P T j)) z ∈ d.batchMeetGraph ∧
      ZFSet.pair (ZFSet.pair b c) z ∈ d.batchMeetGraph := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let k : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  let l : {i : ZFSet.{u} // i ∈ I} := ⟨j, hj⟩
  have freshI := M.groundEligibleTask_cap_fresh group action meet hT top hi
  have freshJ := M.groundEligibleTask_cap_fresh group action meet hT top hj
  have hq := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry k) (d.rel_entry k) (d.anchor_entry k)).1 freshI
  have ht := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry l) (d.rel_entry l) (d.anchor_entry l)).1 freshJ
  exact d.fresh_shadow_separation k l hq ht (fun equal => different (congrArg Subtype.val equal))
    (M.groundEligibleTask_cap_shadow meet hT top hi targetI)
    (M.groundEligibleTask_cap_shadow meet hT top hj targetJ)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
variable (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
include pairing unions powers separation hP hG hr hμ hA hLabels

theorem groundInitialMap_cap_base_values {i S a c K b : ZFSet.{u}} :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ As →
    ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair T K ∈ S → ZFSet.pair a b ∈ S →
    K = eligibleTaskCap P T i ∧ b = c := by
  dsimp only
  intro indexed source target cap base
  obtain ⟨function, capEntry, baseEntry⟩ := M.groundInitialMap_cap_base
    pairing unions powers separation hP hG hr hμ hA hLabels group action meet hT top
    indexed source target
  let graph : FunctionGraphOn P S := ⟨_, function⟩
  exact ⟨graph.unique cap capEntry, graph.unique base baseEntry⟩

theorem groundInitialMap_old_below_cap_iff {i S a c K b v : ZFSet.{u}} :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ As →
    ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair T K ∈ S → ZFSet.pair a b ∈ S → v ∈ P →
    (ZFSet.pair v K ∈ d.batchOrder ↔ ZFSet.pair v b ∈ d.batchOrder) := by
  dsimp only
  intro indexed source target cap base hv
  obtain ⟨capEq, baseEq⟩ := M.groundInitialMap_cap_base_values
    group action meet hT top pairing unions powers separation hP hG hr hμ hA hLabels
    indexed source target cap base
  have hi := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).1
  rw [capEq, baseEq]
  exact M.groundEligibleTask_old_below_cap_iff group action meet hT top hi target hv

theorem groundInitialMap_cap_separation {i j S V a a' c c' K K' b b' : ZFSet.{u}} :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Es := literalTaskBaseGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r) As Es
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    ZFSet.pair i S ∈ Maps → ZFSet.pair j V ∈ Maps →
    ZFSet.pair i a ∈ As → ZFSet.pair j a' ∈ As →
    ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair j c' ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair T K ∈ S → ZFSet.pair T K' ∈ V →
    ZFSet.pair a b ∈ S → ZFSet.pair a' b' ∈ V → i ≠ j →
    ZFSet.pair K b' ∈ d.batchOrder ∨ ZFSet.pair K' b ∈ d.batchOrder ∨
    ∃ z, ZFSet.pair (ZFSet.pair K K') z ∈ d.batchMeetGraph ∧
      ZFSet.pair (ZFSet.pair b b') z ∈ d.batchMeetGraph := by
  dsimp only
  intro indexed indexed' source source' target target' cap cap' base base' different
  obtain ⟨capEq, baseEq⟩ := M.groundInitialMap_cap_base_values
    group action meet hT top pairing unions powers separation hP hG hr hμ hA hLabels
    indexed source target cap base
  obtain ⟨capEq', baseEq'⟩ := M.groundInitialMap_cap_base_values
    group action meet hT top pairing unions powers separation hP hG hr hμ hA hLabels
    indexed' source' target' cap' base'
  have hi := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).1
  have hj := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source').1).1
  rw [capEq, capEq', baseEq, baseEq']
  exact M.groundEligibleTask_cap_separation group action meet hT top hi hj different target target'

end TransitiveGround
end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable {P G r μ A Labels m inv one T : ZFSet.{u}}
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (meet : MeetOrderCode P r μ) (hT : T ∈ P) (top : ∀ x ∈ P, ZFSet.pair x T ∈ r)
include group action meet hT top

theorem groundEligibleTask_initial_profile {i c e F : ZFSet.{u}}
    (hi : i ∈ M.groundEligibleTasks P G r μ A Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (separator : ZFSet.pair i e ∈ literalTaskSeparatorGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (filter : ZFSet.pair i F ∈ literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    c ∈ P ∧ e ∈ P ∧ eligibleTaskCap P T i ∈ d.batchCarrier ∧ F ⊆ P ∧ F.Nonempty ∧
      CodedInsertionProfile d.batchCarrier d.batchOrder d.batchMeetGraph c e (eligibleTaskCap P T i) F ∧
      ZFSet.pair c (eligibleTaskCap P T i) ∈ d.batchOrder ∧
      ZFSet.pair (eligibleTaskCap P T i) c ∉ d.batchOrder ∧
      ZFSet.pair e (eligibleTaskCap P T i) ∉ d.batchOrder := by
  dsimp only
  let I := M.groundEligibleTasks P G r μ A Labels
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have spaceEq : d.space j = P := ((pair_mem_constantFamilyGraph I P _ _).1 (d.space_entry j)).2
  have relEq : d.rel j = r := ((pair_mem_constantFamilyGraph I r _ _).1 (d.rel_entry j)).2
  have fresh := M.groundEligibleTask_cap_fresh group action meet hT top hi
  have freshT := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
    (d.space_entry j) (d.rel_entry j) (d.anchor_entry j)).1 fresh
  have parts := (mem_freshPart _ _ _ T).1 freshT
  let t : d.templates.Space j := ⟨T, parts.1⟩
  have outside : ¬ (d.templates.order j).le t (d.templates.anchor j) := parts.2
  have greatest : ∀ y, (d.templates.order j).le y t := by
    intro y
    change ZFSet.pair y.val T ∈ d.rel j
    rw [relEq]
    have hy : y.val ∈ d.space j := y.property
    exact top y.val (by simpa only [spaceEq] using hy)
  let cap := d.templates.cap j t outside
  have shadow : ZFSet.pair (d.freshCode cap) c ∈
      batchAttachmentShadowGraph I P (constantFamilyGraph I P) (constantFamilyGraph I μ)
        (literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
        (literalTaskBaseGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :=
    M.groundEligibleTask_cap_shadow meet hT top hi target
  have baseEq : (d.templates.base j).val = c := by
    have equal := d.freshCode_shadow_value cap c shadow
    change c = (d.templates.shadow (d.templates.cap j t outside)).val at equal
    rw [d.templates.cap_shadow j t greatest outside] at equal
    exact equal.symm
  have separatorEq : d.separator j = e := d.separators.unique (d.separator_entry j) separator
  have filterEq : d.filter j = F := d.filters.unique (d.filter_entry j) filter
  have hcP : c ∈ P := baseEq ▸ (d.templates.base j).property
  have heP : e ∈ P := separatorEq ▸ (d.fiber j).separator_mem
  have filterSubset : F ⊆ P := filterEq ▸ (d.fiber j).filter.subset
  have nonempty : F.Nonempty := filterEq ▸ (d.fiber j).filter.nonempty
  refine ⟨hcP, heP, M.groundEligibleTask_cap_mem group action meet hT top hi,
    filterSubset, nonempty, ?_⟩
  have laws := d.initial_cap_profile j t greatest outside
  have capEq : d.coding.encode (.inr (d.templates.cap j t outside)) = eligibleTaskCap P T i := rfl
  simpa only [baseEq, separatorEq, filterEq, capEq] using laws

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
variable (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
include pairing unions powers separation hP hG hr hμ hA hLabels

theorem groundInitialMap_profile {i S a c e F K b : ZFSet.{u}} :
    let initial := M.initialCompressionData P G r μ A Labels
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    ZFSet.pair i S ∈ initial.Maps →
    ZFSet.pair i a ∈ literalTaskSourceGraph I P R U Labels →
    ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels →
    ZFSet.pair i e ∈ literalTaskSeparatorGraph I P R U Labels →
    ZFSet.pair i F ∈ literalTaskFilterGraph I P R U Labels →
    ZFSet.pair T K ∈ S → ZFSet.pair a b ∈ S →
      b = c ∧ b ∈ initial.currentCarrier ∧ e ∈ initial.currentCarrier ∧ K ∈ initial.currentCarrier ∧
      F ⊆ initial.currentCarrier ∧ F.Nonempty ∧
      CodedInsertionProfile initial.currentCarrier initial.currentOrder initial.currentMeet b e K F ∧
      ZFSet.pair b K ∈ initial.currentOrder ∧ ZFSet.pair K b ∉ initial.currentOrder ∧
      ZFSet.pair e K ∉ initial.currentOrder := by
  dsimp only
  intro indexed source target separator filter cap base
  obtain ⟨capEq, baseEq⟩ := M.groundInitialMap_cap_base_values group action meet hT top
    pairing unions powers separation hP hG hr hμ hA hLabels indexed source target cap base
  have hi := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).1
  refine ⟨baseEq, ?_⟩
  rw [capEq, baseEq]
  obtain ⟨hcP, heP, hk, subset, nonempty, laws⟩ :=
    M.groundEligibleTask_initial_profile group action meet hT top hi target separator filter
  exact ⟨old_mem_taggedExtension hcP, old_mem_taggedExtension heP, hk,
    fun _ hf => old_mem_taggedExtension (subset hf), nonempty, laws⟩

end TransitiveGround

namespace GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_profile {c e K F : ZFSet.{u}}
    (hc : c ∈ state.data.currentCarrier) (he : e ∈ state.data.currentCarrier)
    (hK : K ∈ state.data.currentCarrier) (subset : F ⊆ state.data.currentCarrier)
    (nonempty : ∃ f, f ∈ F)
    (profile : CodedInsertionProfile state.data.currentCarrier state.data.currentOrder
      state.data.currentMeet c e K F)
    (separated : ZFSet.pair e K ∉ state.data.currentOrder) :
    CodedInsertionProfile (data.fields 0) (data.fields 1) (data.fields 2) c e K F :=
  data.currentOrder.insertionProfile data.currentMeet
    (fun n => (state.canonical_iterate_codes pairing unions powers separation
      hI hSources hReps hG hT n).2.1.order)
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).2.2.2.2.1)
    (state.canonical_iterate_profile pairing unions powers separation
      hI hSources hReps hG hT hc he hK subset nonempty profile separated)

theorem union_separator_not_below_cap {e K : ZFSet.{u}}
    (he : e ∈ state.data.currentCarrier) (hK : K ∈ state.data.currentCarrier)
    (separated : ZFSet.pair e K ∉ state.data.currentOrder) :
    ZFSet.pair e K ∉ data.fields 1 := by
  intro below
  exact separated ((state.union_order_iff data pairing unions powers separation
    hI hSources hReps hG hT 1 he hK).1 below)

end GroundCompressionState

namespace GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P r μ A τ I Sources Reps G m inv one T Filters Labels : ZFSet.{u}}
variable {seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
variable (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hP hG hr hμ hA hLabels hI hSources hReps hT

theorem union_initial_profile
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i f a c e F K : ZFSet.{u}} (indexed : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (separator : ZFSet.pair i e ∈ literalTaskSeparatorGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (filter : ZFSet.pair i F ∈ literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (cap : ZFSet.pair τ K ∈ f) :
    CodedCapProfile (algebra.union.fields 0) (algebra.union.fields 1) (algebra.union.fields 2) c e K F := by
  have ha : a ∈ P := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).2
  have haD : a ∈ state.data.D := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using ha
  have hτD : τ ∈ state.data.D := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using seed.top_mem
  obtain ⟨old, oldEntry⟩ := state.inputs.maps.total (algebra.function.pair_source indexed)
  obtain ⟨b, base, _⟩ := (state.inputs.valid i old oldEntry).injection.function.2 a haD
  have capOld := (algebra.restrict i f indexed 0 old oldEntry τ hτD K).1 cap
  have indexedOld : ZFSet.pair i old ∈ (M.initialCompressionData P G r μ A Labels).Maps := by
    simpa only [initialData] using oldEntry
  have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
  obtain ⟨baseEq, hc, he, hK, subset, nonempty, profile, lower, reverse, separate⟩ :=
    M.groundInitialMap_profile state.inputs.group seed.originalAction seed.originalOrder seed.top_mem top
      pairing unions powers separation hP hG hr hμ hA hLabels
      indexedOld source target separator filter capOld base
  subst b
  have first : CodedCapProfile state.data.currentCarrier state.data.currentOrder state.data.currentMeet c e K F := by
    rw [initialData]
    exact ⟨hc, he, hK, subset, nonempty, profile, lower, reverse, separate⟩
  refine ⟨algebra.union.currentCarrier.subset 0 first.target_mem,
    algebra.union.currentCarrier.subset 0 first.separator_mem,
    algebra.union.currentCarrier.subset 0 first.cap_mem,
    fun _ hf => algebra.union.currentCarrier.subset 0 (first.filter_subset hf), first.nonempty,
    state.union_profile algebra.union pairing unions powers separation hI hSources hReps hG hT
      first.target_mem first.separator_mem first.cap_mem first.filter_subset first.nonempty
      first.profile first.separator_not_below_cap,
    algebra.union.currentOrder.subset 0 first.target_below_cap, ?_, ?_⟩
  · intro below
    exact first.cap_not_below_target ((state.union_order_iff algebra.union pairing unions powers separation
      hI hSources hReps hG hT 1 first.cap_mem first.target_mem).1 below)
  · exact state.union_separator_not_below_cap algebra.union pairing unions powers separation
      hI hSources hReps hG hT first.separator_mem first.cap_mem first.separator_not_below_cap

theorem initial_union_profiles
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    (initialSources : Sources = literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    CodedCompressionProfiles (algebra.union.fields 0) (algebra.union.fields 1) (algebra.union.fields 2)
      (algebra.caps τ)
      (literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
      (literalTaskSeparatorGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
      (literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) := by
  intro i c e K F cap target separator filter
  have hi := (ZFSet.pair_mem_prod.1 ((state.union_caps_function algebra).1 cap)).1
  obtain ⟨f, indexed⟩ := algebra.function.total hi
  obtain ⟨a, source, _⟩ := seed.sources.2 i hi
  rw [initialSources] at source
  exact state.union_initial_profile algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData indexed source target separator filter
    ((state.union_cap_entry_iff algebra indexed).1 cap)

end GroundCompressionState

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialCompressionCompletion
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P r μ A τ I Sources Reps G m inv one T Filters Labels : ZFSet.{u}}
variable {seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
variable (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)

include pairing unions powers separation hP hG hr hμ hA hLabels in
theorem initial_map_marks
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i f a k b : ZFSet.{u}} (indexed : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (cap : ZFSet.pair τ k ∈ f) (base : ZFSet.pair a b ∈ f) :
    ∃ old c, ZFSet.pair i old ∈ (M.initialCompressionData P G r μ A Labels).Maps ∧
      ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels ∧
      ZFSet.pair τ k ∈ old ∧ ZFSet.pair a b ∈ old := by
  have ha : a ∈ P := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).2
  have hi : i ∈ M.groundEligibleTasks P G r μ A Labels :=
    (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).1
  obtain ⟨old, oldEntry⟩ := state.inputs.maps.total (algebra.function.pair_source indexed)
  have hτD : τ ∈ state.data.D := by
    simp only [initialData]
    exact seed.top_mem
  have haD : a ∈ state.data.D := by
    simp only [initialData]
    exact ha
  have capOld := (algebra.restrict i f indexed 0 old oldEntry τ hτD k).1 cap
  have baseOld := (algebra.restrict i f indexed 0 old oldEntry a haD b).1 base
  obtain ⟨_, _, _, _, fields⟩ := M.groundEligibleTaskFields
    pairing unions powers separation hP hG hr hμ hA hLabels seed.originalOrder
  obtain ⟨c, target, _⟩ := (fields 1).2.2 i hi
  refine ⟨old, c, ?_, target, capOld, baseOld⟩
  simpa only [initialData] using oldEntry

variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hP hG hr hμ hA hLabels hI hSources hReps hT

theorem union_initial_old_shadow
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i f a k b x : ZFSet.{u}} (indexed : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (cap : ZFSet.pair τ k ∈ f) (base : ZFSet.pair a b ∈ f) (hx : x ∈ P)
    (below : ZFSet.pair x k ∈ algebra.union.fields 1) : ZFSet.pair x b ∈ algebra.union.fields 1 := by
  obtain ⟨old, c, indexedOld, target, capOld, baseOld⟩ := state.initial_map_marks algebra
    pairing unions powers separation hP hG hr hμ hA hLabels initialData indexed source cap base
  have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
  obtain ⟨function, _, _⟩ := M.groundInitialMap_cap_base
    pairing unions powers separation hP hG hr hμ hA hLabels
    state.inputs.group seed.originalAction seed.originalOrder seed.top_mem top indexedOld source target
  have hxCurrent : x ∈ state.data.currentCarrier := old_mem_taggedExtension (by
    simp only [initialData]
    exact hx)
  have hkCurrent : k ∈ state.data.currentCarrier := by
    simp only [initialData]
    exact (ZFSet.pair_mem_prod.1 (function.1 capOld)).2
  have finiteBelow : ZFSet.pair x k ∈ state.data.currentOrder :=
    (state.union_order_iff algebra.union pairing unions powers separation hI hSources hReps hG hT
      1 hxCurrent hkCurrent).1 below
  have initialBelow : ZFSet.pair x k ∈ (M.initialCompressionData P G r μ A Labels).currentOrder := by
    simpa only [initialData] using finiteBelow
  have result := (M.groundInitialMap_old_below_cap_iff state.inputs.group seed.originalAction
    seed.originalOrder seed.top_mem top pairing unions powers separation hP hG hr hμ hA hLabels
    indexedOld source target capOld baseOld hx).1 initialBelow
  apply algebra.union.currentOrder.subset 0
  simp only [initialData]
  exact result

omit hI hSources hReps hT in
theorem union_initial_cap_separation
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i j f g a c k l b d : ZFSet.{u}}
    (firstMap : ZFSet.pair i f ∈ algebra.maps) (secondMap : ZFSet.pair j g ∈ algebra.maps)
    (firstSource : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (secondSource : ZFSet.pair j c ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (firstCap : ZFSet.pair τ k ∈ f) (secondCap : ZFSet.pair τ l ∈ g)
    (firstBase : ZFSet.pair a b ∈ f) (secondBase : ZFSet.pair c d ∈ g) (different : i ≠ j) :
    ZFSet.pair k d ∈ algebra.union.fields 1 ∨ ZFSet.pair l b ∈ algebra.union.fields 1 ∨
      ∃ z, ZFSet.pair (ZFSet.pair k l) z ∈ algebra.union.fields 2 ∧
        ZFSet.pair (ZFSet.pair b d) z ∈ algebra.union.fields 2 := by
  obtain ⟨old, target, indexedOld, targetEntry, capOld, baseOld⟩ := state.initial_map_marks algebra
    pairing unions powers separation hP hG hr hμ hA hLabels initialData firstMap firstSource firstCap firstBase
  obtain ⟨old', target', indexedOld', targetEntry', capOld', baseOld'⟩ := state.initial_map_marks algebra
    pairing unions powers separation hP hG hr hμ hA hLabels initialData secondMap secondSource secondCap secondBase
  have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
  have result := M.groundInitialMap_cap_separation state.inputs.group seed.originalAction
    seed.originalOrder seed.top_mem top pairing unions powers separation hP hG hr hμ hA hLabels
    indexedOld indexedOld' firstSource secondSource targetEntry targetEntry' capOld capOld' baseOld baseOld' different
  rcases result with first | second | common
  · apply Or.inl
    apply algebra.union.currentOrder.subset 0
    simp only [initialData]
    exact first
  · apply Or.inr ∘ Or.inl
    apply algebra.union.currentOrder.subset 0
    simp only [initialData]
    exact second
  · obtain ⟨z, capsMeet, basesMeet⟩ := common
    refine Or.inr (Or.inr ⟨z, ?_, ?_⟩)
    · apply algebra.union.currentMeet.subset 0
      simp only [initialData]
      exact capsMeet
    · apply algebra.union.currentMeet.subset 0
      simp only [initialData]
      exact basesMeet

end PartitionPilot.Forcing.GroundCompressionState

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialCompletedCompressionCertificates
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P r μ A τ I Sources Reps G m inv one T Filters Labels : ZFSet.{u}}
variable {seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)

theorem initial_union_range_accounting
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets)
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    (initialIndices : I = M.groundEligibleTasks P G r μ A Labels)
    (initialSources : Sources = literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    CompressionRangeAccounting P I (algebra.union.fields 0)
      (algebra.union.fields 1) (algebra.union.fields 2) algebra.maps algebra.bases (algebra.caps τ) := by
  have sourceLiteral {i a : ZFSet.{u}} (source : ZFSet.pair i a ∈ Sources) :
      ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
        P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels := initialSources ▸ source
  refine {
    original_subset := state.union_original_subset algebra.union
    base_filled := ?_
    old_shadow := ?_
    cap_separation := ?_
    fresh_accounting := ?_
  }
  · intro i hi f b indexed based x hx below
    obtain ⟨a, source, _⟩ := seed.sources.2 i hi
    obtain ⟨g, representative, _⟩ := state.inputs.representatives.2 i hi
    exact state.union_map_base_filling algebra pairing unions powers separation hI hSources hReps hG hT
      indexed source representative ((state.union_base_entry_iff algebra indexed source).1 based) hx below
  · intro i hi b k based capped x hx below
    obtain ⟨f, indexed⟩ := algebra.function.total hi
    obtain ⟨a, source, _⟩ := seed.sources.2 i hi
    exact state.union_initial_old_shadow algebra pairing unions powers separation
      hP hG hr hμ hA hLabels hI hSources hReps hT initialData indexed (sourceLiteral source)
      ((state.union_cap_entry_iff algebra indexed).1 capped)
      ((state.union_base_entry_iff algebra indexed source).1 based) hx below
  · intro i hi j hj different b c k l basedI basedJ cappedI cappedJ
    obtain ⟨f, indexedI⟩ := algebra.function.total hi
    obtain ⟨g, indexedJ⟩ := algebra.function.total hj
    obtain ⟨a, sourceI, _⟩ := seed.sources.2 i hi
    obtain ⟨d, sourceJ, _⟩ := seed.sources.2 j hj
    exact state.union_initial_cap_separation algebra pairing unions powers separation
      hP hG hr hμ hA hLabels initialData indexedI indexedJ (sourceLiteral sourceI) (sourceLiteral sourceJ)
      ((state.union_cap_entry_iff algebra indexedI).1 cappedI)
      ((state.union_cap_entry_iff algebra indexedJ).1 cappedJ)
      ((state.union_base_entry_iff algebra indexedI sourceI).1 basedI)
      ((state.union_base_entry_iff algebra indexedJ sourceJ).1 basedJ) different
  · have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
      simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
    have initialAccounting : FiniteCompressionAccounting P I Sources τ state.data := by
      simpa only [initialData, initialIndices, initialSources] using
        (M.initialCompressionData_accounting pairing unions powers separation
          hP hG hr hμ hA hLabels state.inputs.group seed.originalAction seed.originalOrder seed.top_mem top)
    intro x hx
    rcases state.union_fresh_accounting algebra pairing unions powers separation
      hI hSources hReps hG hT initialAccounting x hx with original | fresh
    · exact Or.inl original
    · obtain ⟨i, hi, f, a, k, b, y, hy, indexed, source, cap, base, image, below, outside⟩ := fresh
      exact Or.inr ⟨i, hi, f, k, b, y, hy, indexed,
        (state.union_cap_entry_iff algebra indexed).2 cap,
        (state.union_base_entry_iff algebra indexed source).2 base, image, below, outside⟩

end PartitionPilot.Forcing.GroundCompressionState



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundCoherentHeightChoices
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

theorem pair_mem_stagedGraphRelation (W n m h k : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair n h) (ZFSet.pair m k) ∈ stagedGraphRelation W ↔
      ZFSet.pair n h ∈ W ∧ ZFSet.pair m k ∈ W ∧ m = insert n n ∧ h ⊆ k := by
  rw [stagedGraphRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨first, second⟩, a, b, c, d, equal, successor, subset⟩
    obtain ⟨firstEq, secondEq⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 firstEq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 secondEq
    exact ⟨first, second, successor, subset⟩
  · rintro ⟨first, second, successor, subset⟩
    exact ⟨⟨first, second⟩, n, m, h, k, rfl, successor, subset⟩

namespace BoundedFormula

theorem truth_stagedGraphEntryFormula {n} (z omega b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (stagedGraphEntryFormula z omega b) env ↔
      ∃ a ∈ env omega, ∃ c ∈ env omega, ∃ h ∈ env b, ∃ k ∈ env b,
        env z = ZFSet.pair (ZFSet.pair a h) (ZFSet.pair c k) ∧ c = insert a a ∧ h ⊆ k := by
  simp only [stagedGraphEntryFormula, truth_exMem, Truth, truth_pairOfPairsFormula,
    truth_successorFormula, truth_subsetFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem stagedGraphRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {W B : ZFSet.{u}} (hW : W ∈ M.sets) (hB : B ∈ M.sets)
    (shape : W ⊆ ZFSet.prod ZFSet.omega B) : stagedGraphRelation W ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  let params := extend ZFSet.omega (extend B Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.stagedGraphEntryFormula 0 1 2)
    params (Fin.cases hOmega (Fin.cases hB (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation hW hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.stagedGraphEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod W W) = stagedGraphRelation W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, stagedGraphRelation, ZFSet.mem_sep,
      BoundedFormula.truth_stagedGraphEntryFormula]
    change (_ ∧ ∃ n ∈ ZFSet.omega, ∃ m ∈ ZFSet.omega, ∃ h ∈ B, ∃ k ∈ B,
      z = ZFSet.pair (ZFSet.pair n h) (ZFSet.pair m k) ∧ m = insert n n ∧ h ⊆ k) ↔ _
    constructor
    · rintro ⟨bound, n, _, m, _, h, _, k, _, eq, successor, subset⟩
      exact ⟨bound, n, m, h, k, eq, successor, subset⟩
    · rintro ⟨bound, n, m, h, k, rfl, successor, subset⟩
      have points := ZFSet.pair_mem_prod.1 bound
      have first := ZFSet.pair_mem_prod.1 (shape points.1)
      have second := ZFSet.pair_mem_prod.1 (shape points.2)
      exact ⟨bound, n, first.1, m, second.1, h, first.2, k, second.2, rfl, successor, subset⟩
  exact equal ▸ selected

theorem exists_groundCoherentChoices
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {W B initial : ZFSet.{u}} (hW : W ∈ M.sets) (hB : B ∈ M.sets)
    (shape : W ⊆ ZFSet.prod ZFSet.omega B) (start : ZFSet.pair ∅ initial ∈ W)
    (extendable : ∀ n ∈ ZFSet.omega, ∀ h, ZFSet.pair n h ∈ W →
      ∃ k, ZFSet.pair (insert n n) k ∈ W ∧ h ⊆ k) :
    ∃ history ∈ M.sets, ZFSet.IsFunc ZFSet.omega B history ∧
      (∀ h, ZFSet.pair ∅ h ∈ history ↔ h = initial) ∧
      (∀ n ∈ ZFSet.omega, ∀ h, ZFSet.pair n h ∈ history → ZFSet.pair n h ∈ W) ∧
      ∀ n ∈ ZFSet.omega, ∀ h k,
        ZFSet.pair n h ∈ history → ZFSet.pair (insert n n) k ∈ history → h ⊆ k := by
  have hOmega := M.omega_mem separation infinite
  have relationGround := M.stagedGraphRelation_mem pairing unions powers separation infinite hW hB shape
  have serial : ∀ x ∈ W, ∃ y ∈ W, ZFSet.pair x y ∈ stagedGraphRelation W := by
    intro x hx
    obtain ⟨n, hn, h, _, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨k, next, subset⟩ := extendable n hn h hx
    exact ⟨ZFSet.pair (insert n n) k, next,
      (pair_mem_stagedGraphRelation W n (insert n n) h k).2 ⟨hx, next, rfl, subset⟩⟩
  obtain ⟨orbit, hOrbit, orbitFunction, zero, step⟩ :=
    M.exists_groundSerialOrbit pairing unions powers separation infinite choice hW relationGround start serial
  have stageValue : ∀ n : Nat, ∀ z, ZFSet.pair (natSetCode n) z ∈ orbit →
      ∃ h, z = ZFSet.pair (natSetCode n) h := by
    intro n
    induction n with
    | zero =>
      intro z entry
      exact ⟨initial, (zero z).1 entry⟩
    | succ n ih =>
      intro z entry
      obtain ⟨w, previous, _⟩ := orbitFunction.2 (natSetCode n) (natSetCode_mem_omega n)
      obtain ⟨h, rfl⟩ := ih w previous
      have rel := step (natSetCode n) (natSetCode_mem_omega n) _ z previous entry
      obtain ⟨_, a, b, c, d, equal, successor, _⟩ := ZFSet.mem_sep.1 rel
      obtain ⟨source, target⟩ := ZFSet.pair_inj.1 equal
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 source
      refine ⟨d, ?_⟩
      rw [successor] at target
      exact target
  have stageValueRaw (n z : ZFSet.{u}) (hn : n ∈ ZFSet.omega)
      (entry : ZFSet.pair n z ∈ orbit) : ∃ h, z = ZFSet.pair n h := by
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact stageValue k z entry
  let history := relationCompose ZFSet.omega W B orbit (productSecond ZFSet.omega B)
  have historyGround : history ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hOmega hW hB hOrbit (M.productSecond_mem pairing unions powers separation hOmega hB)
  have historyFunction : ZFSet.IsFunc ZFSet.omega B history :=
    relationCompose_function_of_subset orbitFunction (productSecond_function ZFSet.omega B) shape
  have projected (n h : ZFSet.{u}) (hn : n ∈ ZFSet.omega) :
      ZFSet.pair n h ∈ history ↔ ZFSet.pair n (ZFSet.pair n h) ∈ orbit := by
    change ZFSet.pair n h ∈ relationCompose _ _ _ _ _ ↔ _
    rw [pair_mem_relationCompose]
    constructor
    · rintro ⟨_, _, z, _, entry, projection⟩
      obtain ⟨k, rfl⟩ := stageValueRaw n z hn entry
      obtain ⟨a, _, b, _, equal⟩ := (mem_productSecond _ _ _).1 projection
      obtain ⟨first, second⟩ := ZFSet.pair_inj.1 equal
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
      exact second ▸ entry
    · intro entry
      have point := (ZFSet.pair_mem_prod.1 (orbitFunction.1 entry)).2
      have inB := (ZFSet.pair_mem_prod.1 (shape point)).2
      exact ⟨hn, inB, ZFSet.pair n h, point, entry,
        (mem_productSecond _ _ _).2 ⟨n, hn, h, inB, rfl⟩⟩
  refine ⟨history, historyGround, historyFunction, ?_, ?_, ?_⟩
  · intro h
    rw [projected ∅ h (natSetCode_mem_omega 0), zero, ZFSet.pair_inj]
    exact ⟨And.right, fun eq => ⟨rfl, eq⟩⟩
  · intro n hn h entry
    exact (ZFSet.pair_mem_prod.1 (orbitFunction.1 ((projected n h hn).1 entry))).2
  · intro n hn h k first second
    have successorMem : insert n n ∈ ZFSet.omega := by
      obtain ⟨j, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      exact natSetCode_mem_omega (j + 1)
    have rel := step n hn _ _ ((projected n h hn).1 first)
      ((projected (insert n n) k successorMem).1 second)
    exact ((pair_mem_stagedGraphRelation W n (insert n n) h k).1 rel).2.2.2

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_StrictLexHeightFormulas
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

theorem truth_strictLexHeightFormula {n} (P C D r height rD : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (strictLexHeightFormula P C D r height rD) env ↔
      StrictLexHeightCode (env P) (env C) (env D) (env r) (env height) (env rD) := by
  simp only [strictLexHeightFormula, Truth, truth_functionToProductFormula, truth_imp,
    truth_disj, truth_pairMembershipFormula, truth_rightTripleMembershipFormula]
  constructor
  · rintro ⟨function, strict⟩
    refine ⟨function, ?_⟩
    intro x hx y hy c q d v lower different first second
    have firstBounds := ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 first)).2
    have secondBounds := ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 second)).2
    exact strict x hx y hy c firstBounds.1 q firstBounds.2 d secondBounds.1 v secondBounds.2
      ⟨lower, different, first, second⟩
  · intro code
    refine ⟨code.function, ?_⟩
    intro x hx y hy c _ q _ d _ v _ condition
    exact code.strict x hx y hy c q d v condition.1 condition.2.1
      condition.2.2.1 condition.2.2.2

theorem truth_heightColumnsBoundFormula {n} (P C D height columns : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (heightColumnsBoundFormula P C D height columns) env ↔
      ∀ x ∈ env P, ∀ c ∈ env C, ∀ q ∈ env D,
        ZFSet.pair x (ZFSet.pair c q) ∈ env height → c ∈ env columns := by
  simp only [heightColumnsBoundFormula, Truth, truth_imp, truth_rightTripleMembershipFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CompressionPrefixCoinitiality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old T0 C Q qlt original : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (heights : GroundCompressionHeightData M state.data I Sources Reps G m one T data P0 C Q qlt original)
variable (prior : GroundChronologicalHistory M T0 C Q qlt)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable (ordinal : ordinalSetProperty T0) (hBase : base ∈ T0)
variable (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
variable (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
variable (initialMeet : state.data.μD = μ0)
variable (priorSpace : prior.space base = P0) (priorOrder : prior.order base = r0)
variable (priorMeet : prior.meetGraph base = μ0) (priorBirth : prior.birth base = old)

local notation "history" => state.prefixHistory data births heights prior pairing unions powers separation
  hI hSources hReps hG hT ordinal hBase constant initialDomain initialOrder initialMeet
  priorSpace priorOrder priorMeet priorBirth

theorem prefixHistory_old {s : ZFSet.{u}} (before : s ∈ base ∨ s = base) :
    (history).space s = prior.space s ∧ (history).order s = prior.order s ∧
    (history).meetGraph s = prior.meetGraph s ∧ (history).birth s = prior.birth s ∧
    (history).height s = prior.height s :=
  state.prefixFields_old data births heights prior before

theorem prefixHistory_stamp (n : Nat) :
    (history).space (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).D ∧
    (history).order (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).rD ∧
    (history).meetGraph (compressionStamp base n) = (state.data.iterate M I Sources Reps G T (n + 1)).μD ∧
    (history).birth (compressionStamp base n) =
      graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth ∧
    (history).height (compressionStamp base n) = heights.function.natValue (n + 1) :=
  state.prefixFields_stamp data births heights prior n

theorem prefixHistory_limit :
    (history).space births.limit = data.fields 0 ∧ (history).order births.limit = data.fields 1 ∧
    (history).meetGraph births.limit = data.fields 2 ∧ (history).birth births.limit = births.birth ∧
    (history).height births.limit = heights.height :=
  state.prefixFields_limit data births heights prior

end PartitionPilot.Forcing.GroundCompressionState



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionBirths
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_birthRestrictionFamilyEntryFormula {k}
    (z omega domainsBound relations t domains birth : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (birthRestrictionFamilyEntryFormula z omega domainsBound relations t domains birth) env ↔
      ∃ n ∈ env omega, ∃ P ∈ env domainsBound, ∃ b ∈ env relations,
        env z = ZFSet.pair n b ∧ ZFSet.pair n P ∈ env domains ∧
          b = ZFSet.sep (fun w => w ∈ ZFSet.prod P (env t)) (env birth) := by
  simp only [birthRestrictionFamilyEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_graphRestrictionFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem birthRestrictionFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps birth : ZFSet.{u}} (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hU : U ∈ M.sets) (hT : T ∈ M.sets) (hPs : Ps ∈ M.sets) (hBirth : birth ∈ M.sets)
    (born : ZFSet.IsFunc U T birth) : M.birthRestrictionFamily U T Ps birth ∈ M.sets := by
  have hBound := M.union_mem unions (M.union_mem unions hPs)
  have hRelations := M.groundRelations_mem pairing unions powers separation hU hT
  let params := extend ZFSet.omega (extend (⋃₀ ⋃₀ Ps) (extend (M.groundRelations U T)
    (extend T (extend Ps (extend birth Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.birthRestrictionFamilyEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hω (Fin.cases hBound (Fin.cases hRelations (Fin.cases hT
      (Fin.cases hPs (Fin.cases hBirth (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation hω hRelations)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.birthRestrictionFamilyEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod ZFSet.omega (M.groundRelations U T)) = M.birthRestrictionFamily U T Ps birth := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, birthRestrictionFamily, ZFSet.mem_sep,
      BoundedFormula.truth_birthRestrictionFamilyEntryFormula]
    change (_ ∧ ∃ n ∈ ZFSet.omega, ∃ P ∈ ⋃₀ ⋃₀ Ps, ∃ b ∈ M.groundRelations U T,
      z = ZFSet.pair n b ∧ ZFSet.pair n P ∈ Ps ∧
        b = ZFSet.sep (fun w => w ∈ ZFSet.prod P T) birth) ↔ _
    simp only [graphRestriction_eq_sep born]
  exact equal ▸ selected

theorem birthRestrictionFamily_entries
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps birth : ZFSet.{u}} (hPs : Ps ∈ M.sets) (hBirth : birth ∈ M.sets)
    (P : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (born : ZFSet.IsFunc U T birth) (n : Nat) (b : ZFSet.{u}) :
    ZFSet.pair (natSetCode n) b ∈ M.birthRestrictionFamily U T Ps birth ↔
      b = graphRestriction (P n) birth := by
  constructor
  · intro member
    obtain ⟨_, k, _, D, _, c, _, equal, entry, restriction⟩ := ZFSet.mem_sep.1 member
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact (domains n D).1 entry ▸ restriction
  · intro equal
    have entry := (domains n (P n)).2 rfl
    have hP := M.pair_right (M.transitive hPs entry)
    have hRestriction := M.graphRestriction_mem unions separation hP hBirth
    have relation : b ∈ M.groundRelations U T := (M.mem_groundRelations U T b).2 ⟨
      equal.symm ▸ hRestriction, fun z hz => born.1
        (graphRestriction_subset (P n) birth (equal ▸ hz))⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, relation⟩,
      natSetCode n, natSetCode_mem_omega n, P n, pair_second_mem_doubleUnion entry,
      b, relation, rfl, entry, equal⟩

theorem exists_groundBirthRestrictionFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U T Ps birth : ZFSet.{u}} (hω : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    (hU : U ∈ M.sets) (hT : T ∈ M.sets) (hPs : Ps ∈ M.sets) (hBirth : birth ∈ M.sets)
    (P : Nat → ZFSet.{u})
    (domains : ∀ n D, ZFSet.pair (natSetCode n) D ∈ Ps ↔ D = P n)
    (born : ZFSet.IsFunc U T birth) :
    ∃ family ∈ M.sets, FunctionGraphOn ZFSet.omega family ∧
      ∀ n b, ZFSet.pair (natSetCode n) b ∈ family ↔ b = graphRestriction (P n) birth := by
  have entries := M.birthRestrictionFamily_entries unions separation hPs hBirth P domains born
  refine ⟨M.birthRestrictionFamily U T Ps birth,
    M.birthRestrictionFamily_mem pairing unions powers separation hω hU hT hPs hBirth born,
    ⟨M.groundRelations U T, ?_, ?_⟩, entries⟩
  · exact fun z hz => (ZFSet.mem_sep.1 hz).1
  · intro n hn
    obtain ⟨j, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact ⟨graphRestriction (P j) birth, (entries j _).2 rfl,
      fun b hb => (entries j b).1 hb⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundBirthData
    (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {base old : ZFSet.{u}} (hBase : base ∈ M.sets) (hOld : old ∈ M.sets)
    (ordinal : ordinalSetProperty base) (oldFunction : FunctionGraphOn state.data.D old)
    (oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base)
    (oldMeet : OldMeetCode state.data.rD state.data.μD old) :
    Nonempty (GroundCompressionBirthData M state.data I Sources Reps G m one T data base old) := by
  obtain ⟨stamps, hStamps, limit, hLimit, _, times⟩ := M.exists_groundCompressionStamps
    pairing unions separation collection infinite hBase ordinal
  have born : ZFSet.IsFunc state.data.D limit old := by
    refine ⟨?_, oldFunction.to_isFunc.2⟩
    intro z hz
    obtain ⟨x, hx, t, rfl⟩ := oldFunction.shape z hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, times.union.subset 0
      (compressionStamp_old_mem (oldBound x t hz) 0)⟩
  have hω := M.omega_mem separation infinite
  let stages := state.data.iterate M I Sources Reps G T
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  obtain ⟨domains, hDomains, _, domainEntries⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hω hHistory stages entries 0
  obtain ⟨birth, hBirth, _, extension⟩ := M.exists_groundFirstAppearanceBirth
    pairing unions powers separation hω (data.ground 0) hLimit hDomains hStamps hOld
    (fun n => (stages n).D) (compressionStamp base) domainEntries times.entries
    (data.fieldUnion 0) born times.stamp_mem_limit
  have mono : ∀ n k, n ≤ k → (stages n).D ⊆ (stages k).D :=
    fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).1
  have function := extension.function (data.fieldUnion 0) mono born times.stamp_mem_limit
  obtain ⟨family, hFamily, familyFunction, familyEntries⟩ := M.exists_groundBirthRestrictionFamily
    pairing unions powers separation hω (data.ground 0) hLimit hDomains hBirth
    (fun n => (stages n).D) domainEntries function
  have finite := state.canonical_birth_oldMeet data pairing unions powers separation
    hI hSources hReps hG hT extension born times oldBound oldMeet
  have unionBirth := extension.restriction_union (data.fieldUnion 0) born
  have unionOldMeet := (data.fieldUnion 1).oldMeet (data.fieldUnion 2) unionBirth finite
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation
      hI hSources hReps hG hT h).2.2.1)
    (fun _ _ h => NatBirthExtensionCode.restriction_mono mono h)
  refine ⟨⟨stamps, hStamps, limit, hLimit, times, birth, hBirth, extension,
    family, hFamily, familyFunction, familyEntries, born, oldBound, function,
    extension.restriction_zero mono born, finite, unionOldMeet, ?_⟩⟩
  intro x entry
  exact ZFSet.mem_irrefl limit (ZFSet.pair_mem_prod.1 (function.1 entry)).2

end PartitionPilot.Forcing.GroundCompressionState

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialCompressionOrigin
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem heightCandidateStates_subset (B Ps Rs C D rD original K : ZFSet.{u}) :
    heightCandidateStates B Ps Rs C D rD original K ⊆ ZFSet.prod ZFSet.omega B :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem mem_heightCandidateStates (B Ps Rs C D rD original K z : ZFSet.{u}) :
    z ∈ heightCandidateStates B Ps Rs C D rD original K ↔
      ∃ n ∈ ZFSet.omega, ∃ h ∈ B, ∃ P ∈ Ps.sUnion.sUnion, ∃ r ∈ Rs.sUnion.sUnion,
        z = ZFSet.pair n h ∧ ZFSet.pair n P ∈ Ps ∧ ZFSet.pair n r ∈ Rs ∧
        StrictLexHeightCode P C D r h rD ∧ original ⊆ h ∧
        ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h → c ∈ K := by
  rw [heightCandidateStates, ZFSet.mem_sep]
  constructor
  · exact fun member => member.2
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨n, hn, h, hh, _, _, _, _, heq, _⟩ := witness
    rw [heq]
    exact ZFSet.pair_mem_prod.2 ⟨hn, hh⟩

theorem pair_mem_heightCandidateStates {B Ps Rs C D rD original K n h P r : ZFSet.{u}}
    (domains : FunctionGraphOn ZFSet.omega Ps) (orders : FunctionGraphOn ZFSet.omega Rs)
    (domainEntry : ZFSet.pair n P ∈ Ps) (orderEntry : ZFSet.pair n r ∈ Rs) :
    ZFSet.pair n h ∈ heightCandidateStates B Ps Rs C D rD original K ↔
      h ∈ B ∧ StrictLexHeightCode P C D r h rD ∧ original ⊆ h ∧
      ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h → c ∈ K := by
  rw [mem_heightCandidateStates]
  constructor
  · rintro ⟨m, _, f, hf, Q, _, s, _, equal, first, second, code, old, columns⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    have domainEq := domains.unique first domainEntry
    have orderEq := orders.unique second orderEntry
    subst Q
    subst s
    exact ⟨hf, code, old, columns⟩
  · rintro ⟨hh, code, old, columns⟩
    exact ⟨n, domains.pair_source domainEntry, h, hh,
      P, pair_second_mem_doubleUnion domainEntry, r, pair_second_mem_doubleUnion orderEntry,
      rfl, domainEntry, orderEntry, code, old, columns⟩





namespace BoundedFormula
open SetFormula

theorem truth_heightCandidateEntryFormula {n}
    (z omega B Ps Rs C D rD original K boundPs boundRs : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (heightCandidateEntryFormula z omega B Ps Rs C D rD original K boundPs boundRs) env ↔
      ∃ a ∈ env omega, ∃ h ∈ env B, ∃ P ∈ env boundPs, ∃ r ∈ env boundRs,
        env z = ZFSet.pair a h ∧ ZFSet.pair a P ∈ env Ps ∧ ZFSet.pair a r ∈ env Rs ∧
        StrictLexHeightCode P (env C) (env D) r h (env rD) ∧ env original ⊆ h ∧
        ∀ x c q, ZFSet.pair x (ZFSet.pair c q) ∈ h → c ∈ env K := by
  simp only [heightCandidateEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_strictLexHeightFormula, truth_subsetFormula,
    truth_heightColumnsBoundFormula]
  constructor
  · rintro ⟨a, ha, h, hh, P, hP, r, hr, heq, domain, order, code, old, columns⟩
    refine ⟨a, ha, h, hh, P, hP, r, hr, heq, domain, order, code, old, ?_⟩
    intro x c q entry
    have shape := ZFSet.pair_mem_prod.1 (code.function.1 entry)
    have coordinates := ZFSet.pair_mem_prod.1 shape.2
    exact columns x shape.1 c coordinates.1 q coordinates.2 entry
  · rintro ⟨a, ha, h, hh, P, hP, r, hr, heq, domain, order, code, old, columns⟩
    exact ⟨a, ha, h, hh, P, hP, r, hr, heq, domain, order, code, old,
      fun x _ c _ q _ entry => columns x c q entry⟩

end BoundedFormula

namespace TransitiveGround
open SetFormula

theorem heightCandidateStates_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hOmega : (ZFSet.omega : ZFSet.{u}) ∈ M.sets)
    {B Ps Rs C D rD original K : ZFSet.{u}}
    (hB : B ∈ M.sets) (hPs : Ps ∈ M.sets) (hRs : Rs ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hOriginal : original ∈ M.sets) (hK : K ∈ M.sets) :
    heightCandidateStates B Ps Rs C D rD original K ∈ M.sets := by
  have boundPs := M.union_mem unions (M.union_mem unions hPs)
  have boundRs := M.union_mem unions (M.union_mem unions hRs)
  let params := extend ZFSet.omega (extend B (extend Ps (extend Rs (extend C
    (extend D (extend rD (extend original (extend K
      (extend Ps.sUnion.sUnion (extend Rs.sUnion.sUnion Fin.elim0))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.heightCandidateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) params
    (Fin.cases hOmega (Fin.cases hB (Fin.cases hPs (Fin.cases hRs (Fin.cases hC
      (Fin.cases hD (Fin.cases hrD (Fin.cases hOriginal (Fin.cases hK
        (Fin.cases boundPs (Fin.cases boundRs (fun i => Fin.elim0 i))))))))))))
    (M.prod_mem pairing unions powers separation hOmega hB)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.heightCandidateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11) (extend z params))
      (ZFSet.prod ZFSet.omega B) = heightCandidateStates B Ps Rs C D rD original K := by
    apply ZFSet.ext
    intro z
    rw [heightCandidateStates, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_heightCandidateEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 _)
  exact equal ▸ selected

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem initialCompressionData_template_constancy (P G r μ A Labels : ZFSet.{u}) :
    RecursiveTemplateConstancy P r μ (M.initialCompressionData P G r μ A Labels) :=
  ⟨rfl, rfl, rfl⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (union : GroundCompressionUnionData M state.data I Sources Reps G m one T)
include union

theorem exists_groundHeightFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {Ps Rs C D rD c original : ZFSet.{u}}
    (hPs : Ps ∈ M.sets) (hRs : Rs ∈ M.sets)
    (domains : FunctionGraphOn ZFSet.omega Ps) (orders : FunctionGraphOn ZFSet.omega Rs)
    (domainEntries : ∀ n P, ZFSet.pair (natSetCode n) P ∈ Ps ↔
      P = (state.data.iterate M I Sources Reps G T n).D)
    (orderEntries : ∀ n r, ZFSet.pair (natSetCode n) r ∈ Rs ↔
      r = (state.data.iterate M I Sources Reps G T n).rD)
    (hP0 : P0 ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hrD : rD ∈ M.sets) (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P0 C D r0 original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P0 (ZFSet.prod C D) original) ZFSet.omega) :
    ∃ family ∈ M.sets, FunctionGraphOn ZFSet.omega family ∧
      (∀ h, ZFSet.pair (natSetCode 0) h ∈ family ↔ h = original) ∧
      (∀ n h, ZFSet.pair (natSetCode n) h ∈ family →
        StrictLexHeightCode (state.data.iterate M I Sources Reps G T n).D C D
          (state.data.iterate M I Sources Reps G T n).rD h rD ∧ original ⊆ h ∧
          ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ h → a ∈ heightColumns P0 C D original) ∧
      ∀ n h k, ZFSet.pair (natSetCode n) h ∈ family →
        ZFSet.pair (natSetCode (n + 1)) k ∈ family → h ⊆ k := by
  let stages := state.data.iterate M I Sources Reps G T
  let B := M.groundRelations (union.fields 0) (ZFSet.prod C D)
  let K := heightColumns P0 C D original
  let W := heightCandidateStates B Ps Rs C D rD original K
  have hOmega := M.omega_mem separation infinite
  have hB : B ∈ M.sets := M.groundRelations_mem pairing unions powers separation
    (union.ground 0) (M.prod_mem pairing unions powers separation hC hD)
  have hK : K ∈ M.sets := M.heightColumns_mem pairing unions powers separation hP0 hC hD hOriginal
  have hW : W ∈ M.sets := M.heightCandidateStates_mem pairing unions powers separation
    hOmega hB hPs hRs hC hD hrD hOriginal hK
  have graphBound {P height : ZFSet.{u}} (ground : height ∈ M.sets)
      (function : ZFSet.IsFunc P (ZFSet.prod C D) height)
      (subset : P ⊆ union.fields 0) : height ∈ B := by
    apply (M.mem_groundRelations _ _ _).2
    refine ⟨ground, ?_⟩
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨subset hx, hy⟩
  have candidate (n : Nat) (height : ZFSet.{u}) :
      ZFSet.pair (natSetCode n) height ∈ W ↔ height ∈ B ∧
        StrictLexHeightCode (stages n).D C D (stages n).rD height rD ∧ original ⊆ height ∧
        ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ height → a ∈ K :=
    pair_mem_heightCandidateStates domains orders
      ((domainEntries n _).2 rfl) ((orderEntries n _).2 rfl)
  have originalAtZero : StrictLexHeightCode (stages 0).D C D (stages 0).rD original rD := by
    simpa only [stages, RecursiveStateData.iterate_zero, initialDomain, initialOrder] using originalCode
  have start : ZFSet.pair ∅ original ∈ W := by
    apply (candidate 0 original).2
    exact ⟨graphBound hOriginal originalAtZero.function ((union.fieldUnion 0).subset 0),
      originalAtZero, fun _ hx => hx, fun _ _ _ entry => mem_heightColumns_of_entry originalCode.function entry⟩
  have extendable : ∀ n ∈ ZFSet.omega, ∀ old, ZFSet.pair n old ∈ W →
      ∃ height, ZFSet.pair (insert n n) height ∈ W ∧ old ⊆ height := by
    intro index hIndex old member
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode index).1 hIndex
    obtain ⟨oldBound, oldCode, extension, bounded⟩ := (candidate n old).1 member
    have hOld := ((M.mem_groundRelations _ _ _).1 oldBound).1
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    have currentConstant : RecursiveTemplateConstancy P0 r0 μ0 current.data := by
      rw [equal]
      exact constant.iterate M I Sources Reps G T n
    have currentCode : StrictLexHeightCode current.data.D C D current.data.rD old rD := by
      simpa only [equal] using oldCode
    obtain ⟨height, hHeight, heightCode, inclusion, originalInclusion, columnBound⟩ :=
      current.exists_column_bounded_height_step pairing unions powers separation collection infinite choice
        currentConstant hP0 hC hD hrD hc hOriginal hOld originalCode currentCode columns target above
        coordinateInjection originalSmall extension bounded
    have nextCode : StrictLexHeightCode (stages (n + 1)).D C D (stages (n + 1)).rD height rD := by
      change StrictLexHeightCode (stages n).currentCarrier C D (stages n).currentOrder height rD
      simpa only [equal] using heightCode
    refine ⟨height, ?_, inclusion⟩
    exact (candidate (n + 1) height).2
      ⟨graphBound hHeight nextCode.function ((union.fieldUnion 0).subset (n + 1)),
        nextCode, originalInclusion, columnBound⟩
  obtain ⟨family, hFamily, function, zero, selected, adjacent⟩ := M.exists_groundCoherentChoices
    pairing unions powers separation infinite choice hW hB
      (heightCandidateStates_subset _ _ _ _ _ _ _ _) start extendable
  refine ⟨family, hFamily, ⟨B, function⟩, zero, ?_, ?_⟩
  · intro n height entry
    exact ((candidate n height).1 (selected _ (natSetCode_mem_omega n) height entry)).2
  · intro n height next first second
    exact adjacent (natSetCode n) (natSetCode_mem_omega n) height next first second

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (union : GroundCompressionUnionData M state.data I Sources Reps G m one T)

theorem exists_groundHeightData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (initialDomain : state.data.D = P0) (initialOrder : state.data.rD = r0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {C D rD c original : ZFSet.{u}}
    (hP0 : P0 ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hrD : rD ∈ M.sets) (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P0 C D r0 original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P0 (ZFSet.prod C D) original) ZFSet.omega) :
    Nonempty (GroundCompressionHeightData M state.data I Sources Reps G m one T union P0 C D rD original) := by
  have hOmega := M.omega_mem separation infinite
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  obtain ⟨Ps, hPs, domains, domainEntries⟩ := M.exists_groundStateFieldFamily pairing separation collection
    hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 0
  obtain ⟨Rs, hRs, orders, orderEntries⟩ := M.exists_groundStateFieldFamily pairing separation collection
    hOmega hHistory (state.data.iterate M I Sources Reps G T) entries 1
  obtain ⟨family, hFamily, function, zero, finite, adjacent⟩ := state.exists_groundHeightFamily union
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT
    initialDomain initialOrder constant hPs hRs domains orders domainEntries orderEntries
    hP0 hC hD hrD hc hOriginal originalCode columns target above coordinateInjection originalSmall
  have zeroEq : function.natValue 0 = original := (zero _).1 (function.natValue_entry 0)
  have codes := fun n => (finite n _ (function.natValue_entry n)).1
  have mono := fun n => adjacent n _ _ (function.natValue_entry n) (function.natValue_entry (n + 1))
  have columnBounds := fun n => (finite n _ (function.natValue_entry n)).2.2
  obtain ⟨height, hHeight, exactUnion, code, exactEntries, bound⟩ := M.exists_groundCoherentHeightUnion
    unions separation hOmega hFamily function (union.fieldUnion 0) (union.fieldUnion 1)
    (fun n => (state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT n).1.order)
    codes mono columnBounds
  obtain ⟨rangeGround, rangeCountable⟩ := M.countable_height_range_of_old_columns
    pairing unions powers separation infinite choice hP0 (union.ground 0) hC hD hOriginal hHeight
    originalSmall ⟨c, hc, coordinateInjection⟩ bound
  refine ⟨{
    family := family
    family_ground := hFamily
    function := function
    zero := zeroEq
    finite := codes
    adjacent := mono
    height := height
    height_ground := hHeight
    exact_union := exactUnion
    code := code
    finite_entries := exactEntries
    original_entries := ?_
    range_ground := rangeGround
    range_countable := rangeCountable
    columns := bound
  }⟩
  intro x hx y
  have hxZero : x ∈ (state.data.iterate M I Sources Reps G T 0).D := by
    simpa only [RecursiveStateData.iterate_zero, initialDomain] using hx
  simpa only [zeroEq] using exactEntries 0 x hxZero y

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})





theorem exists_groundInitialCompressionOrigin
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        Nonempty (GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior) := by
  dsimp only
  have hOld : old ∈ M.sets := priorBirth ▸ prior.birth_mem base baseMember
  have oldFunction : FunctionGraphOn P old := by
    rw [← priorSpace, ← priorBirth]
    exact ⟨T0, prior.birth_function base baseMember⟩
  have oldBound : ∀ x t, ZFSet.pair x t ∈ old → t ∈ base ∨ t = base := by
    intro x t entry
    have priorEntry : ZFSet.pair x t ∈ prior.birth base := priorBirth.symm ▸ entry
    have hx := (ZFSet.pair_mem_prod.1 ((prior.birth_function base baseMember).1 priorEntry)).1
    exact (prior.birth_bound base baseMember x hx t priorEntry).symm
  have oldMeet : OldMeetCode r μ old := by
    rw [← priorOrder, ← priorMeet, ← priorBirth]
    exact prior.old_meet base baseMember
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, state, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  refine ⟨hI, hSources, hFilters, hT, Reps, hReps, ⟨seed, state, initialData⟩, ?_⟩
  rw [← initialData]
  obtain ⟨algebra⟩ := state.exists_groundAlgebra pairing unions powers separation collection infinite
    hI hSources hReps hG hT
  have accounting := state.initial_union_range_accounting algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl rfl
  obtain ⟨completion⟩ := state.completion_of_accounting algebra pairing unions powers separation
    hI hSources hReps hG hT accounting
  have initialDomain : state.data.D = P := by rw [initialData]; rfl
  have initialOrder : state.data.rD = r := by rw [initialData]; rfl
  have constant : RecursiveTemplateConstancy P r μ state.data := by
    rw [initialData]
    exact M.initialCompressionData_template_constancy P G r μ A Labels
  obtain ⟨heights⟩ := state.exists_groundHeightData completion.algebra.union
    pairing unions powers separation collection infinite choice hI hSources hReps hG hT
    initialDomain initialOrder constant hP hC hD hrD hc hOriginal originalCode columns target above
    coordinateInjection originalSmall
  have profiles := state.initial_union_profiles completion.algebra pairing unions powers separation
    hP hG hr hμ hA hLabels hI hSources hReps hT initialData rfl
  have initialBirthFunction : FunctionGraphOn state.data.D old := initialDomain.symm ▸ oldFunction
  have initialOldMeet : OldMeetCode state.data.rD state.data.μD old := by
    rw [initialData]
    exact oldMeet
  obtain ⟨births⟩ := state.exists_groundBirthData completion.algebra.union
    pairing unions powers separation collection infinite hI hSources hReps hG hT
    hBase hOld (ordinalSetProperty_member ordinal baseMember) initialBirthFunction oldBound initialOldMeet
  have initialMeet : state.data.μD = μ := by rw [initialData]; rfl
  let history := state.prefixHistory completion.algebra.union births heights prior
    pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
    initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth
  refine ⟨⟨⟨⟨⟨completion, heights⟩, profiles⟩, births⟩, history, priorHeight, ?_, ?_, ?_⟩⟩
  · intro s before
    exact state.prefixHistory_old completion.algebra.union births heights prior
      pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
      initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth before
  · intro n
    exact state.prefixHistory_stamp completion.algebra.union births heights prior
      pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
      initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth n
  · exact state.prefixHistory_limit completion.algebra.union births heights prior
      pairing unions powers separation hI hSources hReps hG hT ordinal baseMember constant
      initialDomain initialOrder initialMeet priorSpace priorOrder priorMeet priorBirth

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialExternalGroup
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

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P r μ A : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

theorem externalWordData
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) :
    GroundExternalWordData M initial I Sources Reps G m one T τ P r μ A completion := by
  obtain ⟨rectangles, requests, letters, kinds, payloads, kindFunction, payloadFunction⟩ :=
    M.groundExternalRequestData pairing unions powers separation hI hP hG hr hμ hA
  obtain ⟨maps, caps, mapFunction, capFunction⟩ :=
    completion.external_fields_ground pairing unions powers separation hI
  have alphabet : externalRequestAlphabet I P G r μ A ∈ M.sets :=
    M.externalGeneratorAlphabet_mem pairing unions powers separation hG letters
  exact {
    rectangles_ground := rectangles
    requests_ground := requests
    letters_ground := letters
    kinds_ground := kinds
    payloads_ground := payloads
    kinds_function := kindFunction
    payloads_function := payloadFunction
    maps_ground := maps
    caps_ground := caps
    maps_function := mapFunction
    caps_function := capFunction
    alphabet_ground := alphabet
    words_ground := M.finiteWords_mem pairing unions powers separation infinite alphabet
    append_ground := M.finiteWordAppendGraph_mem pairing unions powers separation infinite alphabet
    reverse_ground := M.finiteWordReverseGraph_mem pairing unions powers separation infinite alphabet
    length_ground := M.finiteWordLengthGraph_mem pairing unions powers separation infinite alphabet
    append_function := M.finiteWordAppendGraph_function pairing unions separation infinite alphabet
    reverse_function := M.finiteWordReverseGraph_function pairing unions separation infinite alphabet
    length_function := M.finiteWordLengthGraph_function _ }

end GroundCompressionCompletion

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundCompressionStarIncidence
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionOrigin
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P r μ A τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P r μ A τ I Sources Reps G m inv one T Filters)

include origin in
theorem externalGeometryInputs
    (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets)
    (group : GroupCode G m inv one) (hm : m ∈ M.sets) (hInv : inv ∈ M.sets) :
    GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion := by
  have words := completion.externalWordData pairing unions powers separation infinite hI hP hG hr hμ hA
  have generators := M.externalGeneratorGraphs_ground_injections pairing unions powers separation infinite
    group hG words.letters_ground hm
  exact ⟨words, M.externalGroupData pairing unions powers separation infinite group hG words.letters_ground hm hInv,
    generators.1, generators.2.1, generators.2.2.1, generators.2.2.2,
    origin.union_original_data completion.algebra.union pairing unions powers separation hI hSources hReps hG hT⟩

end GroundCompressionOrigin

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialExternalGeometryInputs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, ⟨compression⟩⟩ :=
    M.exists_groundInitialCompressionOrigin pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels group action meet hτ top hC hD hrD hc hOriginal
      originalCode columns target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression,
    origin.externalGeometryInputs compression.born.profiled.heighted.completion
      pairing unions powers separation infinite hI hSources hReps hG hT hP hr hμ hA group hm hInv⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBoundedExternalBirths
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem exists_groundInitialExternalBoundedGeometry_oai
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ C D rD c original base old T0 : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hm : m ∈ M.sets) (hInv : inv ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ M.sets) (hOriginal : original ∈ M.sets)
    (originalCode : StrictLexHeightCode P C D r original rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P (ZFSet.prod C D) original) ZFSet.omega)
    (hBase : base ∈ M.sets) (prior : GroundChronologicalHistory M T0 C D rD)
    (ordinal : ordinalSetProperty T0) (baseMember : base ∈ T0)
    (priorSpace : prior.space base = P) (priorOrder : prior.order base = r)
    (priorMeet : prior.meetGraph base = μ) (priorBirth : prior.birth base = old)
    (priorHeight : prior.height base = original) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let Sources := literalTaskSourceGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Filters := literalTaskFilterGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Targets := literalTaskTargetGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let Separators := literalTaskSeparatorGraph I P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
          P r μ A τ I Sources Reps G m inv one T Filters,
        ∃ compression : GroundChronologicalCompression M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T τ P C D rD original Targets Separators Filters base old T0 prior,
          GroundExternalGeometryInputs M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m inv one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion ∧
          GroundExternalBoundedGeometryData M (M.initialCompressionData P G r μ A Labels)
            I Sources Reps G m one T τ P r μ A compression.born.profiled.heighted.completion := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data⟩ :=
    M.exists_groundInitialExternalGeometryInputs pairing unions powers separation collection infinite choice
      hP hG hr hμ hA hLabels hm hInv group action meet hτ top hC hD hrD hc hOriginal
      originalCode columns target above coordinateInjection originalSmall hBase prior ordinal baseMember
      priorSpace priorOrder priorMeet priorBirth priorHeight
  exact ⟨hI, hSources, hFilters, hT, Reps, hReps, origin, compression, data,
    data.externalGeometryData group action pairing unions powers separation infinite hG hP,
    data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP⟩

end TransitiveGround

open SetFormula
universe u

end PartitionPilot.Forcing

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.exists_groundInitialExternalBoundedGeometry_oai.{u}
