-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:12:52.851808+00:00
-- url     : https://prove2.me/submissions/faf422c0-0d0a-4123-a52d-2479d109265e

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
import Definitions.Def_OAIQ253P009
import Theorems.Thm_OAI_PartitionPilot_Forcing_GroundInitialMainSuccessorData_exists_rankedTargetSerialization
import Theorems.Thm_OAI_PartitionPilot_Forcing_TransitiveGround_exists_groundInitialMainSuccessor

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SetRankBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.SetRealization

universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) {x y : ZFSet.{u}}
include limit

theorem rank_singleton_lt (hx : ZFSet.rank x < o) : ZFSet.rank {x} < o := by
  rw [ZFSet.rank_singleton]
  exact limit.succ_lt hx

theorem rank_unorderedPair_lt (hx : ZFSet.rank x < o) (hy : ZFSet.rank y < o) :
    ZFSet.rank {x, y} < o := by
  rw [ZFSet.rank_pair]
  exact max_lt (limit.succ_lt hx) (limit.succ_lt hy)

theorem rank_orderedPair_lt (hx : ZFSet.rank x < o) (hy : ZFSet.rank y < o) :
    ZFSet.rank (ZFSet.pair x y) < o :=
  rank_unorderedPair_lt limit (rank_singleton_lt limit hx) (rank_unorderedPair_lt limit hx hy)

end PartitionPilot.SetRealization

end

end OAI
end

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

end PartitionPilot

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_NodeCoding
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps



section

universe u

theorem positive_imageFamily {A B : Type u} {P : MeetOrder A} {Q : MeetOrder B}
    (e : MeetEmbedding P Q) (F : A → Prop) (x : B) :
    Positive Q (imageFamily e F) x ↔ PositiveOver e F x := by
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hy⟩
    exact ⟨a, ha, hy⟩
  · rintro ⟨a, ha, hy⟩
    exact ⟨e.toFun a, ⟨a, ha, rfl⟩, hy⟩

end



end PartitionPilot.Compression.RecursiveMaps

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RationalOrderBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Compression.RecursiveMaps.RationalHeights

namespace Fraction

theorem lt_trans {a b c : Fraction} (ab : Lt a b) (bc : Lt b c) : Lt a c := by
  apply cancel_lt b.den_pos
  have h₁ := Int.mul_lt_mul_of_pos_right ab c.den_pos
  have h₂ := Int.mul_lt_mul_of_pos_right bc a.den_pos
  have eq : (b.num * (a.den : Int)) * c.den = (b.num * (c.den : Int)) * a.den := by
    simp [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  rw [eq] at h₁
  have h := Int.lt_trans h₁ h₂
  simpa only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] using h

theorem mediant_between (a b : Fraction) (h : Lt a b) :
    Lt a (mediant a b) ∧ Lt (mediant a b) b := by
  change a.num * (b.den : Int) < b.num * (a.den : Int) at h
  constructor
  · change a.num * ((a.den + b.den : Nat) : Int) < (a.num + b.num) * (a.den : Int)
    rw [Int.natCast_add, Int.mul_add, Int.add_mul]
    omega
  · change (a.num + b.num) * (b.den : Int) < b.num * ((a.den + b.den : Nat) : Int)
    rw [Int.natCast_add, Int.mul_add, Int.add_mul]
    omega

theorem lt_above (a : Fraction) : Lt a (above a) := by
  have pos := Int.mul_pos a.den_pos a.den_pos
  change a.num * (a.den : Int) < (a.num + (a.den : Int)) * a.den
  rw [Int.add_mul]
  omega

end Fraction

namespace Rational

theorem irrefl (a : Rational) : ¬ lt a a := by
  induction a using Quotient.ind with
  | _ a => exact Int.lt_irrefl _

theorem trans {a b c : Rational} (h : lt a b) (h' : lt b c) : lt a c := by
  induction a, b, c using Quotient.inductionOn₃ with
  | _ a b c => exact Fraction.lt_trans h h'

theorem compare (a b : Rational) : lt a b ∨ a = b ∨ lt b a := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b =>
    have h : a.num * (b.den : Int) < b.num * (a.den : Int) ∨
        a.num * (b.den : Int) = b.num * (a.den : Int) ∨
        b.num * (a.den : Int) < a.num * (b.den : Int) := by omega
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl (Quotient.sound h))
    · exact Or.inr (Or.inr h)

theorem between (a b : Rational) (h : lt a b) : ∃ c, lt a c ∧ lt c b := by
  induction a, b using Quotient.inductionOn₂ with
  | _ a b => exact ⟨mk (a.mediant b), Fraction.mediant_between a b h⟩

theorem unbounded_above (a : Rational) : ∃ b, lt a b := by
  induction a using Quotient.ind with
  | _ a => exact ⟨mk a.above, a.lt_above⟩

end Rational

namespace Fraction

theorem below_lt (a : Fraction) : Lt (below a) a := by
  have positive := Int.mul_pos a.den_pos a.den_pos
  change (a.num - (a.den : Int)) * a.den < a.num * (a.den : Int)
  rw [Int.sub_mul]
  omega

end Fraction

namespace Rational

theorem unbounded_below (a : Rational) : ∃ b, lt b a := by
  induction a using Quotient.ind with
  | _ a => exact ⟨mk a.below, a.below_lt⟩

end Rational

end PartitionPilot.Compression.RecursiveMaps.RationalHeights

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_PrincipalBatch
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps



section




open Attachment
universe u v w

namespace IdealEmbedding

variable {A : Type u} {B : Type v} {C : Type w}
    {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}

theorem greatest_part (f : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) (x : B) (a : A) :
    Q.le (f.toFun a) x ↔ P.le a (f.projection top x) := by
  rw [← f.le_iff, f.projection_spec]
  constructor
  · intro h
    exact Q.le_meet h ((f.le_iff _ _).mpr (greatest a))
  · intro h
    exact Q.trans h (Q.meet_le_left _ _)

end IdealEmbedding
end



end PartitionPilot.Compression.RecursiveMaps

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_ProfileTransport
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u
variable {A B C : Type u} {P : MeetOrder A} {Q : MeetOrder B} {R : MeetOrder C}

theorem profileOver_iff_image (e : MeetEmbedding P Q) (c v K : A) (F : A → Prop) :
    ProfileOver e c v K F ↔
      Profile Q (e.toFun c) (e.toFun v) (e.toFun K) (imageFamily e F) := by
  constructor
  · intro h x above
    exact ⟨fun hp => (h x above).1 ((positive_imageFamily e F x).mp hp),
      fun hn => (h x above).2 (fun hp => hn ((positive_imageFamily e F x).mpr hp))⟩
  · intro h x above
    exact ⟨fun hp => (h x above).1 ((positive_imageFamily e F x).mpr hp),
      fun hn => (h x above).2 (fun hp => hn ((positive_imageFamily e F x).mp hp))⟩

theorem IdealEmbedding.hasOldShadow (e : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) (x : B) : HasOldShadow e.toMeetEmbedding x := by
  refine ⟨e.projection top x, e.greatest_part top greatest x, ?_⟩
  intro a _
  rw [e.map_meet, e.projection_spec]
  apply Q.antisymm
  · exact Q.le_meet
      (Q.le_meet (Q.meet_le_left _ _) (Q.trans (Q.meet_le_right _ _) ((e.le_iff _ _).mpr (greatest a))))
      (Q.meet_le_right _ _)
  · exact Q.le_meet (Q.trans (Q.meet_le_left _ _) (Q.meet_le_left _ _)) (Q.meet_le_right _ _)

theorem IdealEmbedding.preservesProfiles (e : IdealEmbedding P Q) (top : A)
    (greatest : ∀ a, P.le a top) : PreservesProfiles e.toMeetEmbedding := by
  intro c v K F nonempty separate profile
  exact profile_persists_one_step e.toMeetEmbedding c v K F nonempty profile separate
    (fun x => Or.inr (Or.inl (e.hasOldShadow top greatest x)))

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



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_graphFiberInclusionFormula {n} (x y f g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (graphFiberInclusionFormula x y f g) env ↔
      ∀ z, ZFSet.pair (env x) z ∈ env f → ZFSet.pair (env y) z ∈ env g := by
  simp only [graphFiberInclusionFormula, Truth, truth_imp,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  change (∀ p ∈ env f, ∀ a ∈ p, ∀ z ∈ a,
    p = ZFSet.pair (env x) z → ZFSet.pair (env y) z ∈ env g) ↔ _
  constructor
  · intro h z entry
    exact h (ZFSet.pair (env x) z) entry {env x, z}
      (ZFSet.mem_pair.2 (Or.inr rfl)) z (ZFSet.mem_pair.2 (Or.inr rfl)) rfl
  · intro h p hp a _ z _ equal
    exact h z (equal ▸ hp)

theorem truth_graphFiberEqualityFormula {n} (x y f g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (graphFiberEqualityFormula x y f g) env ↔
      ∀ z, ZFSet.pair (env x) z ∈ env f ↔ ZFSet.pair (env y) z ∈ env g := by
  simp only [graphFiberEqualityFormula, Truth, truth_graphFiberInclusionFormula]
  exact ⟨fun h z => ⟨h.1 z, h.2 z⟩, fun h => ⟨fun z => (h z).1, fun z => (h z).2⟩⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_relationOnFormula {n} (c r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (relationOnFormula c r) env ↔ env r ⊆ ZFSet.prod (env c) (env c) := by
  simp only [relationOnFormula, Truth, truth_exMem, truth_orderedPairFormula]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ZFSet.mem_prod.symm))

theorem truth_partialOrderFormula {n} (c r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (partialOrderFormula c r) env ↔ PartialOrderCode (env c) (env r) := by
  simp only [partialOrderFormula, Truth, truth_relationOnFormula, reflexiveFormula,
    antisymmetricFormula, transitiveFormula, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨shape, refl, antisymm, trans⟩
    exact ⟨shape, refl, fun x hx y hy xy yx => antisymm x hx y hy ⟨xy, yx⟩,
      fun x hx y hy z hz xy yz => trans x hx y hy z hz ⟨xy, yz⟩⟩
  · intro h
    exact ⟨h.relation, h.refl, fun x hx y hy ⟨xy, yx⟩ => h.antisymm x hx y hy xy yx,
      fun x hx y hy z hz ⟨xy, yz⟩ => h.trans x hx y hy z hz xy yz⟩

theorem truth_topFormula {n} (c r t : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (topFormula c r t) env ↔ env t ∈ env c ∧ ∀ x ∈ env c, ZFSet.pair x (env t) ∈ env r := by
  simp only [topFormula, Truth, truth_pairMembershipFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

theorem truth_binaryRelationFormula {n} (g f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (binaryRelationFormula g f) env ↔
      env f ⊆ ZFSet.prod (ZFSet.prod (env g) (env g)) (env g) := by
  simp only [binaryRelationFormula, Truth, truth_exMem, truth_orderedTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, y, hy, z, hz, eq⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨ZFSet.pair x y, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, z, hz, eq⟩
  · intro h w hw
    obtain ⟨xy, hxy, z, hz, eq⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact ⟨x, hx, y, hy, z, hz, eq⟩

theorem truth_binaryFunctionFormula {n} (g f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (binaryFunctionFormula g f) env ↔
      ZFSet.IsFunc (ZFSet.prod (env g) (env g)) (env g) (env f) := by
  simp only [binaryFunctionFormula, Truth, truth_binaryRelationFormula, truth_exMem,
    truth_tripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro xy hxy
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    obtain ⟨z, _, rel, unique⟩ := total x hx y hy
    refine ⟨z, rel, ?_⟩
    intro w hw
    exact unique w (ZFSet.pair_mem_prod.1 (shape hw)).2 hw
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx y hy
    obtain ⟨z, rel, unique⟩ := total (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    exact ⟨z, (ZFSet.pair_mem_prod.1 (shape rel)).2, rel, fun w _ hw => unique w hw⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

theorem truth_groupFormula {n} (g m i e : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (groupFormula g m i e) env ↔ GroupCode (env g) (env m) (env i) (env e) := by
  simp only [groupFormula, Truth, truth_binaryFunctionFormula, truth_functionFormula,
    groupIdentityFormula, groupInverseFormula, groupAssociativeFormula,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨mul, inv, one, identity, inverse, assoc⟩
    exact ⟨mul, inv, one, fun x hx => (identity x hx).1,
      fun x hx => (identity x hx).2, inverse,
      fun x hx y hy z hz a ha b hb c hc xy yz az => assoc x hx y hy z hz a ha b hb c hc ⟨xy, yz, az⟩⟩
  · intro h
    exact ⟨h.mul_function, h.inv_function, h.identity_mem,
      fun x hx => ⟨h.one_mul x hx, h.mul_one x hx⟩, h.inv_mul,
      fun x hx y hy z hz a ha b hb c hc ⟨xy, yz, az⟩ => h.mul_assoc x hx y hy z hz a ha b hb c hc xy yz az⟩

end BoundedFormula

end PartitionPilot.Forcing



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



namespace PartitionPilot.Forcing

universe u v w

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundChronologyPairs
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

namespace BoundedFormula

theorem truth_chronologyPairsEquationFormula {n} (J T : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyPairsEquationFormula J T) env ↔ env J = chronologyPairs (env T) := by
  simp only [chronologyPairsEquationFormula, Truth, truth_chronologyPairFormula,
    truth_imp, truth_disj, truth_pairMembershipFormula]
  change ((∀ z ∈ env J, z ∈ chronologyPairs (env T)) ∧
    ∀ s ∈ env T, ∀ t ∈ env T, (t = s ∨ t ∈ s) → ZFSet.pair s t ∈ env J) ↔ _
  constructor
  · rintro ⟨subset, cover⟩
    apply ZFSet.ext
    intro z
    refine ⟨subset z, ?_⟩
    intro hz
    obtain ⟨s, hs, t, ht, rfl, before⟩ := (mem_chronologyPairs (env T) z).1 hz
    exact cover s hs t ht before
  · intro equal
    rw [equal]
    exact ⟨fun _ hz => hz, fun s hs t ht before =>
      (pair_mem_chronologyPairs (env T) s t).2 ⟨hs, ht, before⟩⟩

theorem realize_chronologyPairsEquationFormula (M : TransitiveGround.{u}) {n}
    (J T : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyPairsEquationFormula J T).toFormula env ↔ env J = chronologyPairs (env T) :=
  (realize_toFormula M _ env members).trans (truth_chronologyPairsEquationFormula J T env)

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CodedInjectiveCones
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

namespace BoundedFormula

theorem truth_graphDiagonalFormula {n} (f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphDiagonalFormula f) env ↔ GraphDiagonalCode (env f) := by
  simp only [graphDiagonalFormula, Truth, truth_imp, truth_orderedPairFormula]
  change (∀ p ∈ env f, ∀ a ∈ p, ∀ x ∈ a, ∀ b ∈ p, ∀ y ∈ b,
    p = ZFSet.pair x y → x = y) ↔ _
  constructor
  · intro h x y entry
    exact h (ZFSet.pair x y) entry {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      x (ZFSet.mem_pair.2 (Or.inl rfl)) {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      y (ZFSet.mem_pair.2 (Or.inr rfl)) rfl
  · intro h p hp a _ x _ b _ y _ equal
    exact h x y (equal ▸ hp)

theorem truth_graphCompositionFormula {n} (f g h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (graphCompositionFormula f g h) env ↔ GraphCompositionCode (env f) (env g) (env h) := by
  simp only [graphCompositionFormula, Truth, truth_imp, truth_orderedPairFormula,
    truth_graphFiberEqualityFormula]
  change (∀ p ∈ env f, ∀ a ∈ p, ∀ x ∈ a, ∀ b ∈ p, ∀ y ∈ b,
    p = ZFSet.pair x y → ∀ z, (ZFSet.pair y z ∈ env g ↔ ZFSet.pair x z ∈ env h)) ↔ _
  constructor
  · intro law x y entry
    exact law (ZFSet.pair x y) entry {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      x (ZFSet.mem_pair.2 (Or.inl rfl)) {x, y} (ZFSet.mem_pair.2 (Or.inr rfl))
      y (ZFSet.mem_pair.2 (Or.inr rfl)) rfl
  · intro law p hp a _ x _ b _ y _ equal
    exact law x y (equal ▸ hp)

end BoundedFormula

end



section
universe u

theorem graphDiagonalCode_identity (A : ZFSet.{u}) : GraphDiagonalCode (identityFunctionGraph A) :=
  fun x y entry => ((pair_mem_identityFunctionGraph A x y).1 entry).1

theorem graphCompositionCode_relationCompose {A B C f g : ZFSet.{u}}
    (first : ZFSet.IsFunc A B f) (second : ZFSet.IsFunc B C g) :
    GraphCompositionCode f g (relationCompose A B C f g) := by
  intro x y xy z
  constructor
  · intro yz
    have bounds := ZFSet.pair_mem_prod.1 (first.1 xy)
    have target := (ZFSet.pair_mem_prod.1 (second.1 yz)).2
    exact (pair_mem_relationCompose A B C f g x z).2
      ⟨bounds.1, target, y, bounds.2, xy, yz⟩
  · intro xz
    obtain ⟨_, _, v, _, xv, vz⟩ := (pair_mem_relationCompose A B C f g x z).1 xz
    have equal := (show FunctionGraphOn A f from ⟨B, first⟩).unique xv xy
    exact equal ▸ vz





end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SeparationFulfillmentCodes
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

theorem truth_productRelationFormula {n} (a b c f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productRelationFormula a b c f) env ↔
      env f ⊆ ZFSet.prod (ZFSet.prod (env a) (env b)) (env c) := by
  simp only [productRelationFormula, Truth, truth_exMem, truth_orderedTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, y, hy, z, hz, eq⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨ZFSet.pair x y, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, z, hz, eq⟩
  · intro h w hw
    obtain ⟨xy, hxy, z, hz, eq⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact ⟨x, hx, y, hy, z, hz, eq⟩

theorem truth_productFunctionFormula {n} (a b c f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productFunctionFormula a b c f) env ↔
      ZFSet.IsFunc (ZFSet.prod (env a) (env b)) (env c) (env f) := by
  simp only [productFunctionFormula, Truth, truth_productRelationFormula, truth_exMem,
    truth_tripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro xy hxy
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    obtain ⟨z, _, rel, unique⟩ := total x hx y hy
    exact ⟨z, rel, fun w hw => unique w (ZFSet.pair_mem_prod.1 (shape hw)).2 hw⟩
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx y hy
    obtain ⟨z, rel, unique⟩ := total (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
    exact ⟨z, (ZFSet.pair_mem_prod.1 (shape rel)).2, rel, fun w _ hw => unique w hw⟩

end BoundedFormula




universe u

namespace BoundedFormula

open SetFormula

theorem truth_posetActionFormula {n} (g p m e r a : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (posetActionFormula g p m e r a) env ↔
      PosetActionCode (env g) (env p) (env m) (env e) (env r) (env a) := by
  simp only [posetActionFormula, Truth, truth_productFunctionFormula, actionOneFormula,
    actionMulFormula, actionMonotoneFormula, truth_tripleMembershipFormula,
    truth_pairMembershipFormula, truth_imp]
  constructor
  · rintro ⟨function, one, mul, monotone⟩
    exact ⟨function, one,
      fun g hg h hh k hk p hp q hq r hr gh hpq gr => mul g hg h hh k hk p hp q hq r hr ⟨gh, hpq, gr⟩,
      fun g hg p hp q hq r hr s hs gr gs pq => monotone g hg p hp q hq r hr s hs ⟨gr, gs, pq⟩⟩
  · intro h
    exact ⟨h.function, h.one,
      fun g hg j hj k hk p hp q hq r hr ⟨gj, jq, gr⟩ => h.mul g hg j hj k hk p hp q hq r hr gj jq gr,
      fun g hg p hp q hq r hr s hs ⟨gr, gs, pq⟩ => h.monotone g hg p hp q hq r hr s hs gr gs pq⟩

end BoundedFormula


end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedSumPresentations
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.RationalHeights
universe u

theorem pair_mem_fractionLtGraph (a b : Fraction) :
    ZFSet.pair (fractionEncode a) (fractionEncode b) ∈ fractionLtGraph.{u} ↔ Fraction.Lt a b := by
  constructor
  · intro h
    obtain ⟨c, d, equal, rel⟩ := (ZFSet.mem_sep.1 h).2
    have parts := ZFSet.pair_inj.1 equal
    obtain rfl := fractionEncode_injective parts.1
    obtain rfl := fractionEncode_injective parts.2
    exact rel
  · intro rel
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨fractionEncode_mem a, fractionEncode_mem b⟩,
      a, b, rfl, rel⟩

end PartitionPilot.Forcing

end


end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_GroundCountableQuotients
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

universe u

theorem canonicalRepresentativesInjection_code {S E c : ZFSet.{u}}
    (injection : InjectionCode S ZFSet.omega c) :
    InjectionCode (canonicalRepresentatives S E c) ZFSet.omega (canonicalRepresentativesInjection S E c) :=
  injection.restrict (canonicalRepresentatives_subset S E c)

namespace BoundedFormula

open SetFormula

theorem truth_canonicalRepresentativeFormula {n} (x s e c omega : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (canonicalRepresentativeFormula x s e c omega) env ↔
      ∃ k ∈ env omega, ZFSet.pair (env x) k ∈ env c ∧
        ∀ y ∈ env s, ZFSet.pair (env x) y ∈ env e → ∀ m ∈ k, ZFSet.pair y m ∉ env c := by
  simp only [canonicalRepresentativeFormula, truth_exMem, Truth, truth_imp, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem canonicalRepresentatives_mem (separation : SeparationSchema M.sets)
    {S E c : ZFSet.{u}} (hS : S ∈ M.sets) (hE : E ∈ M.sets) (hc : c ∈ M.sets)
    (hOmega : ZFSet.omega ∈ M.sets) : canonicalRepresentatives S E c ∈ M.sets := by
  let params := extend S (extend E (extend c (extend ZFSet.omega Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.canonicalRepresentativeFormula 0 1 2 3 4) params
    (Fin.cases hS (Fin.cases hE (Fin.cases hc (Fin.cases hOmega (fun i => Fin.elim0 i))))) hS
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.canonicalRepresentativeFormula 0 1 2 3 4) (extend x params)) S =
      canonicalRepresentatives S E c := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_canonicalRepresentatives]
    exact and_congr Iff.rfl (BoundedFormula.truth_canonicalRepresentativeFormula 0 1 2 3 4 _)
  exact eq ▸ selected

theorem canonicalRepresentativesInjection_mem (separation : SeparationSchema M.sets)
    {S E c : ZFSet.{u}} (hS : S ∈ M.sets) (hE : E ∈ M.sets) (hc : c ∈ M.sets)
    (hOmega : ZFSet.omega ∈ M.sets) : canonicalRepresentativesInjection S E c ∈ M.sets :=
  M.injection_restriction_mem separation
    (M.canonicalRepresentatives_mem separation hS hE hc hOmega) hOmega hc

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_RationalCodeLaws
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.RationalHeights
universe u

theorem rationalLtGraph_subset (c : ZFSet.{u}) :
    rationalLtGraph c ⊆ ZFSet.prod (rationalCarrier c) (rationalCarrier c) :=
  fun _ h => (ZFSet.mem_sep.1 h).2

theorem pair_mem_rationalLtGraph {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) (r s : Rational) :
    ZFSet.pair (rationalEncode hc r) (rationalEncode hc s) ∈ rationalLtGraph c ↔ Rational.lt r s := by
  have first := (rationalEncode_spec hc r).1
  have second := (rationalEncode_spec hc s).1
  rw [rationalLtGraph, ZFSet.mem_sep]
  have lookup : ZFSet.pair (rationalEncode hc r) (rationalEncode hc s) ∈ fractionLtGraph ↔
      Rational.lt r s := by
    obtain ⟨a, ha, ar⟩ := rationalEncode_class hc r
    obtain ⟨b, hb, bs⟩ := rationalEncode_class hc s
    rw [← ha, ← hb, pair_mem_fractionLtGraph, ← ar, ← bs]
    exact Iff.rfl
  exact ⟨fun h => lookup.1 h.1,
    fun h => ⟨lookup.2 h, ZFSet.pair_mem_prod.2 ⟨first, second⟩⟩⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open Compression.RecursiveMaps.RationalHeights
universe u

theorem rational_denseOrderCode {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) :
    DenseOrderCode (rationalCarrier c) (rationalLtGraph c) := by
  refine ⟨⟨rationalLtGraph_subset c, ?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 hx
    exact fun h => Rational.irrefl a.down ((pair_mem_rationalLtGraph hc _ _).1 h)
  · intro x y z xy yz
    have shape := ZFSet.pair_mem_prod.1 (rationalLtGraph_subset c xy)
    have hz := (ZFSet.pair_mem_prod.1 (rationalLtGraph_subset c yz)).2
    obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 shape.1
    obtain ⟨b, rfl⟩ := ((rationalPresentation hc).mem_carrier y).1 shape.2
    obtain ⟨d, rfl⟩ := ((rationalPresentation hc).mem_carrier z).1 hz
    exact (pair_mem_rationalLtGraph hc _ _).2 (Rational.trans
      ((pair_mem_rationalLtGraph hc _ _).1 xy) ((pair_mem_rationalLtGraph hc _ _).1 yz))
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := ((rationalPresentation hc).mem_carrier y).1 hy
    rcases Rational.compare a.down b.down with less | same | more
    · exact Or.inl ((pair_mem_rationalLtGraph hc _ _).2 less)
    · exact Or.inr (Or.inl (congrArg (rationalEncode hc) same))
    · exact Or.inr (Or.inr ((pair_mem_rationalLtGraph hc _ _).2 more))
  · intro x y xy
    have shape := ZFSet.pair_mem_prod.1 (rationalLtGraph_subset c xy)
    obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 shape.1
    obtain ⟨b, rfl⟩ := ((rationalPresentation hc).mem_carrier y).1 shape.2
    obtain ⟨d, ad, db⟩ := Rational.between _ _ ((pair_mem_rationalLtGraph hc _ _).1 xy)
    exact ⟨rationalEncode hc d, (rationalEncode_spec hc d).1,
      (pair_mem_rationalLtGraph hc _ _).2 ad, (pair_mem_rationalLtGraph hc _ _).2 db⟩

theorem rationalCarrier_nonempty {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) : ∃ x, x ∈ rationalCarrier c :=
  ⟨rationalEncode hc (Rational.mk ⟨0, 1, by decide⟩), (rationalEncode_spec hc _).1⟩

theorem rational_no_endpoints {c : ZFSet.{u}}
    (hc : InjectionCode fractionCarrier ZFSet.omega c) :
    ∀ x ∈ rationalCarrier c,
      (∃ y ∈ rationalCarrier c, ZFSet.pair y x ∈ rationalLtGraph c) ∧
      (∃ y ∈ rationalCarrier c, ZFSet.pair x y ∈ rationalLtGraph c) := by
  intro x hx
  obtain ⟨a, rfl⟩ := ((rationalPresentation hc).mem_carrier x).1 hx
  obtain ⟨b, ba⟩ := Rational.unbounded_below a.down
  obtain ⟨d, ad⟩ := Rational.unbounded_above a.down
  exact ⟨⟨rationalEncode hc b, (rationalEncode_spec hc b).1,
      (pair_mem_rationalLtGraph hc _ _).2 ba⟩,
    ⟨rationalEncode hc d, (rationalEncode_spec hc d).1,
      (pair_mem_rationalLtGraph hc _ _).2 ad⟩⟩

end PartitionPilot.Forcing

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

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_FiniteFamilyRankBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot
universe u
namespace SetRealization

theorem rank_functionGraph_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {A B f : ZFSet.{u}} (function : ZFSet.IsFunc A B f)
    (source : ZFSet.rank A < o) (target : ZFSet.rank B < o) :
    ZFSet.rank f < o :=
  (ZFSet.rank_mono function.1).trans_lt (rank_product_lt limit source target)

end SetRealization

namespace Forcing
open SetRealization

theorem rank_nonemptyTupleCode_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (k : Nat) (fields : Fin (k + 1) → ZFSet.{u}) (bounds : ∀ j, ZFSet.rank (fields j) < o) :
    ZFSet.rank (nonemptyTupleCode k fields) < o := by
  induction k with
  | zero => exact bounds 0
  | succ k ih => exact rank_orderedPair_lt limit (bounds 0) (ih _ (fun j => bounds j.succ))

end Forcing
end PartitionPilot



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem rank_finiteRange_lt (n : Nat) (f : Fin n → ZFSet.{u})
    (bounds : ∀ i, ZFSet.rank (f i) < o) : ZFSet.rank (ZFSet.range f) < o := by
  induction n with
  | zero =>
    have empty : ZFSet.range f = ∅ := by
      apply ZFSet.ext
      intro x
      rw [ZFSet.mem_range]
      exact ⟨fun ⟨i, _⟩ => Fin.elim0 i, fun hx => False.elim (ZFSet.notMem_empty x hx)⟩
    simpa only [empty, ZFSet.rank_empty] using limit.pos
  | succ n ih =>
    have split : ZFSet.range f = insert (f 0) (ZFSet.range (fun i : Fin n => f i.succ)) := by
      apply ZFSet.ext
      intro x
      rw [ZFSet.mem_range, ZFSet.mem_insert_iff, ZFSet.mem_range]
      constructor
      · rintro ⟨i, equal⟩
        exact Fin.cases (fun h => Or.inl h.symm) (fun j h => Or.inr ⟨j, h⟩) i equal
      · rintro (equal | ⟨i, equal⟩)
        · exact ⟨0, equal.symm⟩
        · exact ⟨i.succ, equal⟩
    rw [split, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt (bounds 0)) (ih _ (fun i => bounds i.succ))

theorem rank_constantFamilyGraph_lt {I x : ZFSet.{u}}
    (domain : ZFSet.rank I < o) (value : ZFSet.rank x < o) :
    ZFSet.rank (constantFamilyGraph I x) < o :=
  rank_functionGraph_lt limit (constantFamilyGraph_function I x) domain
    (rank_singleton_lt limit value)

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
universe u v

theorem rank_finiteCodeRange_lt {I : Type v} [Small.{u} I] [Finite I]
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (value : I → ZFSet.{u})
    (bounds : ∀ i, ZFSet.rank (value i) < o) :
    ZFSet.rank (ZFSet.range value) < o := by
  classical
  let := Fintype.ofFinite I
  let e := Fintype.equivFin I
  have equal : ZFSet.range value = ZFSet.range (fun i => value (e.symm i)) := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_range]
    exact ⟨fun ⟨i, hi⟩ => ⟨e i, by simpa only [e.symm_apply_apply] using hi⟩,
      fun ⟨i, hi⟩ => ⟨e.symm i, hi⟩⟩
  rw [equal]
  exact rank_finiteRange_lt limit _ _ (fun i => bounds (e.symm i))

theorem familyCodeGraph_finite_rank_lt {I : Type v} [Small.{u} I] [Finite I]
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (key value : I → ZFSet.{u})
    (keys : ∀ i, ZFSet.rank (key i) < o) (values : ∀ i, ZFSet.rank (value i) < o) :
    ZFSet.rank (familyCodeGraph key value) < o :=
  rank_finiteCodeRange_lt limit _
    (fun i => rank_orderedPair_lt limit (keys i) (values i))

end



open SetRealization SetFormula
universe u


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

end PartitionPilot.Forcing.BoundedFormula

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

theorem truth_finiteWordAppendEntryFormula {n} (z words alphabet omega add : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (finiteWordAppendEntryFormula z words alphabet omega add) env ↔
      ∃ f ∈ env words, ∃ g ∈ env words, ∃ h ∈ env words,
        env z = ZFSet.pair (ZFSet.pair f g) h ∧
          FiniteWordAppendCode (env alphabet) (env omega) (env add) f g h := by
  simp only [finiteWordAppendEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_finiteWordAppendFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

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

end TransitiveGround






end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundRationalCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing



section

open Compression.RecursiveMaps.RationalHeights
universe u

theorem exists_mem_omega_code (p : ZFSet.{u} → Prop) :
    (∃ x ∈ ZFSet.omega, p x) ↔ ∃ n : Nat, p (natSetCode n) := by
  constructor
  · rintro ⟨x, hx, hp⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
    exact ⟨n, hp⟩
  · rintro ⟨n, hp⟩
    exact ⟨_, natSetCode_mem_omega n, hp⟩

theorem positiveMagnitude_ofNat (n m : Nat) :
    positiveMagnitude (natSetCode (Fraction.intCode (Int.ofNat n)))
      (natSetCode m) natAddGraph.{u} ↔ m = n := by
  rw [positiveMagnitude, pair_mem_natAddGraph]
  simp only [Fraction.intCode]
  omega

theorem positiveMagnitude_negSucc (n m : Nat) :
    ¬ positiveMagnitude (natSetCode (Fraction.intCode (Int.negSucc n)))
      (natSetCode m) natAddGraph.{u} := by
  rw [positiveMagnitude, pair_mem_natAddGraph]
  simp only [Fraction.intCode]
  omega

theorem negativeMagnitude_ofNat (n m : Nat) :
    ¬ negativeMagnitude (natSetCode (Fraction.intCode (Int.ofNat n)))
      (natSetCode m) ZFSet.omega natAddGraph.{u} (natSetCode 1) := by
  simp only [negativeMagnitude, exists_mem_omega_code, pair_mem_natAddGraph, Fraction.intCode]
  omega

theorem negativeMagnitude_negSucc (n m : Nat) :
    negativeMagnitude (natSetCode (Fraction.intCode (Int.negSucc n)))
      (natSetCode m) ZFSet.omega natAddGraph.{u} (natSetCode 1) ↔ m = n + 1 := by
  simp only [negativeMagnitude, exists_mem_omega_code, pair_mem_natAddGraph, Fraction.intCode]
  constructor
  · rintro ⟨k, d, hm, hd, hn⟩
    omega
  · intro hm
    exact ⟨n, n + n, hm, rfl, by omega⟩

theorem fractionComparison_code (strict : Bool) (a b : Fraction) :
    fractionComparison strict (natSetCode (Fraction.intCode a.num)) (natSetCode a.den)
      (natSetCode (Fraction.intCode b.num)) (natSetCode b.den)
      ZFSet.omega natAddGraph.{u} natMulGraph (natSetCode 1) ↔
        (if strict then Fraction.Lt a b else Fraction.Equiv a b) := by
  rcases a with ⟨an, ad, ha⟩
  rcases b with ⟨bn, bd, hb⟩
  cases an <;> cases bn <;> cases strict <;>
    simp only [fractionComparison, exists_mem_omega_code, pair_mem_natMulGraph,
      positiveMagnitude_ofNat, positiveMagnitude_negSucc, negativeMagnitude_ofNat,
      negativeMagnitude_negSucc, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      natSetCode_injective.eq_iff, natSetCode_mem_iff]
  all_goals rename_i an bn
  all_goals have pa := Nat.mul_pos (Nat.succ_pos an) hb
  all_goals have pb := Nat.mul_pos (Nat.succ_pos bn) ha
  all_goals simp only [Fraction.Equiv, Fraction.Lt]
  all_goals try simp only [Int.negSucc_eq, Int.ofNat_eq_natCast, ← Int.natCast_succ, Int.neg_mul, ← Int.natCast_mul]
  all_goals simp only [false_and, and_false, false_or, or_false, exists_eq_left, exists_eq_right,
    and_self, exists_and_left]
  all_goals try simp only [Nat.succ_eq_add_one] at *
  all_goals try simp only [exists_false, exists_eq, false_iff, true_iff]
  all_goals omega

namespace BoundedFormula

open SetFormula

theorem truth_positiveMagnitudeFormula {n} (code magnitude add : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (positiveMagnitudeFormula code magnitude add) env ↔
      positiveMagnitude (env code) (env magnitude) (env add) :=
  truth_tripleMembershipFormula magnitude magnitude code add env

theorem truth_negativeMagnitudeFormula {n} (code magnitude W add one : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (negativeMagnitudeFormula code magnitude W add one) env ↔
      negativeMagnitude (env code) (env magnitude) (env W) (env add) (env one) := by
  simp only [negativeMagnitudeFormula, truth_exMem, Truth, truth_tripleMembershipFormula]
  rfl

theorem truth_fractionComparisonFormula {n} (strict : Bool) (a ad b bd W add mul one : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (fractionComparisonFormula strict a ad b bd W add mul one) env ↔
      fractionComparison strict (env a) (env ad) (env b) (env bd)
        (env W) (env add) (env mul) (env one) := by
  cases strict <;>
    simp only [fractionComparisonFormula, truth_exMem, Truth, truth_tripleMembershipFormula,
      truth_positiveMagnitudeFormula, truth_negativeMagnitudeFormula, truth_disj,
      Bool.false_eq_true, ite_false, if_false, ite_true, if_true, not_true_eq_false]
  all_goals rfl

end BoundedFormula

end



section

open Compression.RecursiveMaps.RationalHeights
universe u

namespace BoundedFormula

open SetFormula

theorem truth_fractionGraphFormula (strict : Bool) (env : Fin 6 → ZFSet.{u}) :
    Truth (fractionGraphFormula strict) env ↔
      ∃ x ∈ env 1, ∃ y ∈ env 1, env 0 = ZFSet.pair x y ∧
        ∃ a ∈ env 2, ∃ ad ∈ env 2, ∃ b ∈ env 2, ∃ bd ∈ env 2,
          x = ZFSet.pair a ad ∧ y = ZFSet.pair b bd ∧
          fractionComparison strict a ad b bd (env 2) (env 3) (env 4) (env 5) := by
  simp only [fractionGraphFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_fractionComparisonFormula]
  rfl

theorem fractionGraphFormula_iff (strict : Bool) (z : ZFSet.{u}) :
    Truth (fractionGraphFormula strict)
      (extend z (extend fractionCarrier (extend ZFSet.omega (extend natAddGraph
        (extend natMulGraph (extend (natSetCode 1) Fin.elim0)))))) ↔
      ∃ a b : Fraction, z = ZFSet.pair (fractionEncode a) (fractionEncode b) ∧
        (if strict then Fraction.Lt a b else Fraction.Equiv a b) := by
  rw [truth_fractionGraphFormula]
  change (∃ x ∈ fractionCarrier, ∃ y ∈ fractionCarrier, z = ZFSet.pair x y ∧
    ∃ a ∈ ZFSet.omega, ∃ ad ∈ ZFSet.omega, ∃ b ∈ ZFSet.omega, ∃ bd ∈ ZFSet.omega,
      x = ZFSet.pair a ad ∧ y = ZFSet.pair b bd ∧
      fractionComparison strict a ad b bd ZFSet.omega natAddGraph natMulGraph (natSetCode 1)) ↔ _
  constructor
  · rintro ⟨x, hx, y, hy, equal, n, _, d, _, k, _, e, _, ex, ey, compare⟩
    obtain ⟨a, rfl⟩ := (mem_fractionCarrier x).1 hx
    obtain ⟨b, rfl⟩ := (mem_fractionCarrier y).1 hy
    have pa := ZFSet.pair_inj.1 ex
    have pb := ZFSet.pair_inj.1 ey
    exact ⟨a, b, equal, (fractionComparison_code strict a b).1
      (pa.1.symm ▸ pa.2.symm ▸ pb.1.symm ▸ pb.2.symm ▸ compare)⟩
  · rintro ⟨a, b, equal, compare⟩
    exact ⟨fractionEncode a, fractionEncode_mem a, fractionEncode b, fractionEncode_mem b,
      equal, natSetCode (Fraction.intCode a.num), natSetCode_mem_omega _,
      natSetCode a.den, natSetCode_mem_omega _, natSetCode (Fraction.intCode b.num),
      natSetCode_mem_omega _, natSetCode b.den, natSetCode_mem_omega _, rfl, rfl,
      (fractionComparison_code strict a b).2 compare⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem fractionCarrier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : fractionCarrier ∈ M.sets := by
  have hW := M.omega_mem separation infinite
  have h0 := M.natSetCode_mem separation infinite 0
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.neg (BoundedFormula.equal 0 1)) (extend (natSetCode 0) Fin.elim0)
    (Fin.cases h0 (fun j => Fin.elim0 j)) hW
  exact M.prod_mem pairing unions powers separation hW selected

theorem fractionComparisonGraph_mem (strict : Bool)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) :
    (if strict then fractionLtGraph else fractionEquivGraph) ∈ M.sets := by
  have hF := M.fractionCarrier_mem pairing unions powers separation infinite
  have hW := M.omega_mem separation infinite
  have hAdd := M.natAddGraph_mem pairing unions powers separation infinite
  have hMul := M.natMulGraph_mem pairing unions powers separation infinite
  have hOne := M.natSetCode_mem separation infinite 1
  let params := extend fractionCarrier (extend ZFSet.omega
    (extend natAddGraph (extend natMulGraph (extend (natSetCode 1) Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.fractionGraphFormula strict)
    params (Fin.cases hF (Fin.cases hW (Fin.cases hAdd
      (Fin.cases hMul (Fin.cases hOne (fun j => Fin.elim0 j))))))
    (M.prod_mem pairing unions powers separation hF hF)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.fractionGraphFormula strict) (extend z params))
      (ZFSet.prod fractionCarrier fractionCarrier) =
        (if strict then fractionLtGraph else fractionEquivGraph) := by
    cases strict <;> apply ZFSet.ext <;> intro z
    all_goals simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, fractionLtGraph,
      fractionEquivGraph, ZFSet.mem_sep]
    all_goals exact and_congr Iff.rfl (BoundedFormula.fractionGraphFormula_iff _ z)
  exact equal ▸ selected

theorem fractionEquivGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : fractionEquivGraph ∈ M.sets :=
  M.fractionComparisonGraph_mem false pairing unions powers separation infinite

theorem fractionLtGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : fractionLtGraph ∈ M.sets :=
  M.fractionComparisonGraph_mem true pairing unions powers separation infinite

end TransitiveGround

end



namespace TransitiveGround

open SetFormula SetRealization Compression.RecursiveMaps.RationalHeights
universe u
variable (M : TransitiveGround.{u})

theorem fractionCarrier_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0) :
    M.groundEmbeddable fractionCarrier ZFSet.omega := by
  have subset : fractionCarrier.{u} ⊆ ZFSet.prod ZFSet.omega ZFSet.omega := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.mem_sep.1 hy).1⟩
  exact M.groundEmbeddable_restrict separation
    (M.fractionCarrier_mem pairing unions powers separation infinite)
    (M.omega_mem separation infinite) subset
    (M.omega_product_countable pairing unions powers separation infinite)

theorem rationalCarrier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {c : ZFSet.{u}} (hc : c ∈ M.sets) : rationalCarrier c ∈ M.sets :=
  M.canonicalRepresentatives_mem separation
    (M.fractionCarrier_mem pairing unions powers separation infinite)
    (M.fractionEquivGraph_mem pairing unions powers separation infinite) hc
    (M.omega_mem separation infinite)

theorem rationalLtGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {c : ZFSet.{u}} (hc : c ∈ M.sets) : rationalLtGraph c ∈ M.sets :=
  M.injection_restriction_mem separation
    (M.rationalCarrier_mem pairing unions powers separation infinite hc)
    (M.rationalCarrier_mem pairing unions powers separation infinite hc)
    (M.fractionLtGraph_mem pairing unions powers separation infinite)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBelowFunctionGraphs
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

theorem realize_groundBelowFormula {n} (a k : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (groundBelowFormula a k) env ↔ GroundBelow M (env a) (env k) := by
  rw [groundBelowFormula, realize_ex]
  constructor
  · rintro ⟨β, hβ, bound, witness⟩
    exact ⟨β, bound, (M.realize_hasInjectionFormula a.succ 0 (extend β env)
      (Fin.cases hβ members)).1 witness⟩
  · rintro ⟨β, bound, witness⟩
    have hβ := M.transitive (members k) bound
    exact ⟨β, hβ, bound, (M.realize_hasInjectionFormula a.succ 0 (extend β env)
      (Fin.cases hβ members)).2 witness⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

open scoped ZFSet

theorem pair_mem_functionSourceProjection (A f z x : ZFSet.{u}) :
    ZFSet.pair z x ∈ functionSourceProjection A f ↔
      z ∈ f ∧ x ∈ A ∧ ∃ y, z = ZFSet.pair x y := by
  rw [functionSourceProjection, pair_mem_graphRestriction, mem_productFirst]
  constructor
  · rintro ⟨⟨a, ha, b, _, equal⟩, hz⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hz, ha, b, rfl⟩
  · rintro ⟨hz, hx, y, rfl⟩
    exact ⟨⟨x, hx, y, pair_second_mem_doubleUnion hz, rfl⟩, hz⟩

theorem functionSourceProjection_injection {A f : ZFSet.{u}}
    (function : FunctionGraphOn A f) : InjectionCode f A (functionSourceProjection A f) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨z, hz, x, rfl, entry⟩ := mem_graphRestriction.1 hp
    have hx := (ZFSet.pair_mem_prod.1 ((productFirst_function A (⋃₀ ⋃₀ f)).1 entry)).2
    exact ZFSet.pair_mem_prod.2 ⟨hz, hx⟩
  · intro z hz
    obtain ⟨x, hx, y, rfl⟩ := function.shape z hz
    refine ⟨x, (pair_mem_functionSourceProjection _ _ _ _).2 ⟨hz, hx, y, rfl⟩, ?_⟩
    intro a entry
    obtain ⟨_, _, b, equal⟩ := (pair_mem_functionSourceProjection _ _ _ _).1 entry
    exact (ZFSet.pair_inj.1 equal).1.symm
  · intro z w x first second
    obtain ⟨hz, _, y, rfl⟩ := (pair_mem_functionSourceProjection _ _ _ _).1 first
    obtain ⟨hw, _, b, rfl⟩ := (pair_mem_functionSourceProjection _ _ _ _).1 second
    exact congrArg (ZFSet.pair x) (function.unique hz hw)

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem functionSourceProjection_mem {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) : functionSourceProjection A f ∈ M.sets :=
  M.graphRestriction_mem unions separation hf (M.productFirst_mem pairing unions powers separation
    hA (M.union_mem unions (M.union_mem unions hf)))

theorem functionGraph_embeds_source {A f : ZFSet.{u}}
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) (function : FunctionGraphOn A f) :
    M.groundEmbeddable f A :=
  ⟨functionSourceProjection A f, M.functionSourceProjection_mem pairing unions powers separation hA hf,
    functionSourceProjection_injection function⟩

end TransitiveGround

namespace GroundBelow
variable {M : TransitiveGround.{u}} {A B f K : ZFSet.{u}}

theorem functionGraphOn (small : GroundBelow M A K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) (hK : K ∈ M.sets)
    (function : FunctionGraphOn A f) : GroundBelow M f K :=
  small.of_embeddable pairing unions powers separation hf hA hK
    (M.functionGraph_embeds_source pairing unions powers separation hA hf function)

theorem functionGraph (small : GroundBelow M A K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hf : f ∈ M.sets) (hK : K ∈ M.sets)
    (function : ZFSet.IsFunc A B f) : GroundBelow M f K :=
  small.functionGraphOn pairing unions powers separation hA hf hK ⟨B, function⟩

end GroundBelow

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

namespace BoundedFormula
open SetFormula

theorem truth_mainStageFormula {n} (z P r μ G m inv one A bottom top height : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainStageFormula z P r μ G m inv one A bottom top height) env ↔
      env z = mainStageCode (env P) (env r) (env μ) (env G) (env m) (env inv) (env one) (env A) (env bottom) (env top) (env height) := by
  rw [mainStageFormula, truth_nonemptyTupleFormula]
  rfl

theorem realize_mainStageFormula (M : TransitiveGround.{u}) {n}
    (z P r μ G m inv one A bottom top height : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (mainStageFormula z P r μ G m inv one A bottom top height).toFormula env ↔
      env z = mainStageCode (env P) (env r) (env μ) (env G) (env m) (env inv) (env one) (env A) (env bottom) (env top) (env height) :=
  (realize_toFormula M _ env members).trans (truth_mainStageFormula z P r μ G m inv one A bottom top height env)

end BoundedFormula

end



end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedChronologyCodes
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

theorem truth_oldMeetFormula {n} (L T r μ birth : Fin n) (env : Fin n → ZFSet.{u})
    (function : ZFSet.IsFunc (env L) (env T) (env birth)) :
    Truth (oldMeetFormula L T r μ birth) env ↔ OldMeetCode (env r) (env μ) (env birth) := by
  simp only [oldMeetFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  constructor
  · intro property x y z a b c bornY bornX earlier notLower meetXY bornZ
    have xBounds := ZFSet.pair_mem_prod.1 (function.1 bornX)
    have yBounds := ZFSet.pair_mem_prod.1 (function.1 bornY)
    have zBounds := ZFSet.pair_mem_prod.1 (function.1 bornZ)
    exact property x xBounds.1 y yBounds.1 z zBounds.1 a yBounds.2 b xBounds.2 c zBounds.2
      ⟨bornY, bornX, earlier, notLower, meetXY, bornZ⟩
  · intro property x _ y _ z _ a _ b _ c _ condition
    exact property x y z a b c condition.1 condition.2.1 condition.2.2.1
      condition.2.2.2.1 condition.2.2.2.2.1 condition.2.2.2.2.2

theorem truth_birthBoundFormula {n} (L T birth s : Fin n) (env : Fin n → ZFSet.{u})
    (function : ZFSet.IsFunc (env L) (env T) (env birth)) :
    Truth (birthBoundFormula L T birth s) env ↔
      ∀ x ∈ env L, ∀ t, ZFSet.pair x t ∈ env birth → t = env s ∨ t ∈ env s := by
  simp only [birthBoundFormula, Truth, truth_imp, truth_pairMembershipFormula, truth_disj]
  exact ⟨fun bound x hx t entry => bound x hx t
      (ZFSet.pair_mem_prod.1 (function.1 entry)).2 entry,
    fun bound x hx t _ entry => bound x hx t entry⟩

end PartitionPilot.Forcing.BoundedFormula

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_BoundedMeetOrderCodes
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

theorem truth_meetOrderFormula {n} (P r μ : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (meetOrderFormula P r μ) env ↔ MeetOrderCode (env P) (env r) (env μ) := by
  simp only [meetOrderFormula, Truth, truth_partialOrderFormula,
    truth_binaryFunctionFormula, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  constructor
  · rintro ⟨order, operation, laws⟩
    have bounds (x y z : ZFSet.{u}) (entry : ZFSet.pair (ZFSet.pair x y) z ∈ env μ) :
        x ∈ env P ∧ y ∈ env P ∧ z ∈ env P := by
      have shape := ZFSet.pair_mem_prod.1 (operation.1 entry)
      exact ⟨(ZFSet.pair_mem_prod.1 shape.1).1,
        (ZFSet.pair_mem_prod.1 shape.1).2, shape.2⟩
    refine ⟨order, operation, ?_, ?_, ?_⟩
    · intro x y z entry
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).1
    · intro x y z entry
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).2.1
    · intro x y z w hw entry wx wy
      have h := bounds x y z entry
      exact (laws x h.1 y h.2.1 z h.2.2 entry).2.2 w hw ⟨wx, wy⟩
  · intro meet
    exact ⟨meet.order, meet.operation, fun x _ y _ z _ entry =>
      ⟨meet.lower_left x y z entry, meet.lower_right x y z entry,
        fun w hw ⟨wx, wy⟩ => meet.greatest x y z w hw entry wx wy⟩⟩

end PartitionPilot.Forcing.BoundedFormula

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

theorem realize_functionGraphOnFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {n} (a f : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (functionGraphOnFormula a f) env ↔ FunctionGraphOn (env a) (env f) := by
  rw [functionGraphOnFormula, realize_ex]
  constructor
  · rintro ⟨B, hB, code⟩
    exact ⟨B, (BoundedFormula.truth_functionFormula a.succ 0 f.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hB members)).1 code)⟩
  · intro code
    have range := M.union_mem unions (M.union_mem unions (members f))
    exact ⟨ZFSet.sUnion (ZFSet.sUnion (env f)), range,
      (BoundedFormula.realize_toFormula M _ _ (Fin.cases range members)).2
        ((BoundedFormula.truth_functionFormula a.succ 0 f.succ _).2 code.to_isFunc)⟩

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCountableLayerCodes
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

theorem truth_countableLayerFormula {n} (L birth t D N injection : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (countableLayerFormula L birth t D N injection) env ↔
      CountableLayerCode (env L) (env birth) (env t) (env D) (env N) (env injection) := by
  simp only [countableLayerFormula, Truth, truth_injectionFormula, truth_imp,
    truth_pairMembershipFormula]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.small, h.cover⟩⟩

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLayerBirthFibers
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

theorem truth_layerBirthFiberFormula {n} (F L birth t : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (layerBirthFiberFormula F L birth t) env ↔
      env F = layerBirthFiber (env L) (env birth) (env t) := by
  simp only [layerBirthFiberFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change ((∀ x ∈ env F, x ∈ env L) ∧ ∀ x ∈ env L,
    (x ∈ env F → ZFSet.pair x (env t) ∈ env birth) ∧
      (ZFSet.pair x (env t) ∈ env birth → x ∈ env F)) ↔ _
  constructor
  · rintro ⟨subset, spec⟩
    apply ZFSet.ext
    intro x
    rw [mem_layerBirthFiber]
    exact ⟨fun hx => ⟨subset x hx, (spec x (subset x hx)).1 hx⟩,
      fun ⟨hx, born⟩ => (spec x hx).2 born⟩
  · intro eq
    rw [eq]
    exact ⟨fun _ hx => (mem_layerBirthFiber _ _ _ _).1 hx |>.1,
      fun x hx => ⟨fun born => (mem_layerBirthFiber _ _ _ _).1 born |>.2,
        fun born => (mem_layerBirthFiber _ _ _ _).2 ⟨hx, born⟩⟩⟩

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaggedGrowthLayerFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_oldBridgeFormula {n} (L r μ birth t x y : Fin n) (env : Fin n → ZFSet.{u})
    (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Truth (oldBridgeFormula L r μ birth t x y) env ↔
      OldBridgeCode (env L) (env r) (env μ) (env birth) (env t) (env x) (env y) := by
  simp only [oldBridgeFormula, truth_disj, truth_exMem, Truth,
    truth_tripleMembershipFormula, truth_pairMembershipFormula, OldBridgeCode]
  constructor
  · rintro (⟨z, _, a, ha, entry, born⟩ | ⟨z, hz, a, ha, born, bridge⟩)
    · exact Or.inl ⟨z, a, entry, born, ha⟩
    · exact Or.inr ⟨z, hz, a, born, ha, bridge⟩
  · rintro (⟨z, a, entry, born, ha⟩ | ⟨z, hz, a, born, ha, bridge⟩)
    · exact Or.inl ⟨z, (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2, a, ha, entry, born⟩
    · exact Or.inr ⟨z, hz, a, ha, born, bridge⟩

theorem truth_meetEmbeddingFormula {n} (P L rP rL μP μL e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (meetEmbeddingFormula P L rP rL μP μL e) env ↔
      MeetEmbeddingCode (env P) (env L) (env rP) (env rL) (env μP) (env μL) (env e) := by
  simp only [meetEmbeddingFormula, Truth, truth_injectionFormula, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨injection, monotone, meet⟩
    have bounds {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env e) :
        x ∈ env P ∧ y ∈ env L := ZFSet.pair_mem_prod.1 (injection.function.1 entry)
    refine ⟨injection, ?_, ?_⟩
    · intro x y x' y' lower first second
      exact monotone x (bounds first).1 y (bounds second).1
        x' (bounds first).2 y' (bounds second).2 ⟨lower, first, second⟩
    · intro x y z x' y' z' output first second third
      exact meet x (bounds first).1 y (bounds second).1 z (bounds third).1
        x' (bounds first).2 y' (bounds second).2 z' (bounds third).2
        ⟨output, first, second, third⟩
  · intro code
    exact ⟨code.injection,
      fun x _ y _ x' _ y' _ h => code.monotone x y x' y' h.1 h.2.1 h.2.2,
      fun x _ y _ z _ x' _ y' _ z' _ h =>
        code.map_meet x y z x' y' z' h.1 h.2.1 h.2.2.1 h.2.2.2⟩

theorem truth_groupEmbeddingFormula {n} (G H mG mH oneG oneH e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (groupEmbeddingFormula G H mG mH oneG oneH e) env ↔
      GroupEmbeddingCode (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env e) := by
  simp only [groupEmbeddingFormula, Truth, truth_injectionFormula, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor
  · rintro ⟨injection, one, mul⟩
    have bounds {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env e) :
        x ∈ env G ∧ y ∈ env H := ZFSet.pair_mem_prod.1 (injection.function.1 entry)
    refine ⟨injection, one, ?_⟩
    intro a b c a' b' c' product first second third
    exact mul a (bounds first).1 b (bounds second).1 c (bounds third).1
      a' (bounds first).2 b' (bounds second).2 c' (bounds third).2
      ⟨product, first, second, third⟩
  · intro code
    exact ⟨code.injection, code.one, fun a _ b _ c _ a' _ b' _ c' _ h =>
      code.mul a b c a' b' c' h.1 h.2.1 h.2.2.1 h.2.2.2⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_doubleUnionMemberFormula {n} (x f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (doubleUnionMemberFormula x f) env ↔ env x ∈ ⋃₀ ⋃₀ env f := by
  simp only [doubleUnionMemberFormula, truth_exMem, Truth]
  change (∃ a ∈ env f, ∃ b ∈ a, env x ∈ b) ↔ _
  constructor
  · rintro ⟨a, ha, b, hb, hx⟩
    exact ZFSet.mem_sUnion.2 ⟨b, ZFSet.mem_sUnion.2 ⟨a, ha, hb⟩, hx⟩
  · intro hx
    obtain ⟨b, hb, hx⟩ := ZFSet.mem_sUnion.1 hx
    obtain ⟨a, ha, hb⟩ := ZFSet.mem_sUnion.1 hb
    exact ⟨a, ha, b, hb, hx⟩

theorem truth_doubleUnionEquationFormula {n} (B f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (doubleUnionEquationFormula B f) env ↔ env B = ⋃₀ ⋃₀ env f := by
  simp only [doubleUnionEquationFormula, Truth, truth_doubleUnionMemberFormula]
  change ((∀ x ∈ env B, x ∈ ⋃₀ ⋃₀ env f) ∧
    ∀ a ∈ env f, ∀ b ∈ a, ∀ x ∈ b, x ∈ env B) ↔ _
  constructor
  · rintro ⟨subset, cover⟩
    apply ZFSet.ext
    intro x
    refine ⟨subset x, ?_⟩
    intro hx
    obtain ⟨b, hb, hx⟩ := ZFSet.mem_sUnion.1 hx
    obtain ⟨a, ha, hb⟩ := ZFSet.mem_sUnion.1 hb
    exact cover a ha b hb x hx
  · intro equal
    rw [equal]
    exact ⟨fun _ hx => hx, fun a ha b hb x hx =>
      ZFSet.mem_sUnion.2 ⟨b, ZFSet.mem_sUnion.2 ⟨a, ha, hb⟩, hx⟩⟩

theorem truth_copyEmbeddingFamilyFormula {n}
    (Qs rs μs L r μ t I Indices Maps W QB RB MB : Fin n) (env : Fin n → ZFSet.{u})
    (maps : ZFSet.IsFunc (env I) (env W) (env Maps))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) (eqR : env RB = ⋃₀ ⋃₀ env rs)
    (eqM : env MB = ⋃₀ ⋃₀ env μs) :
    Truth (copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB) env ↔
      CopyEmbeddingFamilyCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env t) (env I) (env Indices) (env Maps) := by
  simp only [copyEmbeddingFamilyFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_meetEmbeddingFormula]
  constructor
  · intro property i hi s hs e P R V index map qField rField mField
    have hP : P ∈ env QB := eqQ.symm ▸ pair_second_mem_doubleUnion qField
    have hR : R ∈ env RB := eqR.symm ▸ pair_second_mem_doubleUnion rField
    have hV : V ∈ env MB := eqM.symm ▸ pair_second_mem_doubleUnion mField
    exact property i hi s hs e (ZFSet.pair_mem_prod.1 (maps.1 map)).2
      P hP R hR V hV ⟨index, map, qField, rField, mField⟩
  · intro code i hi s hs e _ P _ R _ V _ condition
    exact code i hi s hs e P R V condition.1 condition.2.1 condition.2.2.1
      condition.2.2.2.1 condition.2.2.2.2

theorem truth_copyImageCoverFormula {n} (Qs L t I parts Indices Maps W QB : Fin n)
    (env : Fin n → ZFSet.{u}) (maps : ZFSet.IsFunc (env I) (env W) (env Maps))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) :
    Truth (copyImageCoverFormula Qs L t I parts Indices Maps W QB) env ↔
      CopyImageCoverCode (env Qs) (env L) (env t) (env I) (env parts) (env Indices) (env Maps) := by
  simp only [copyImageCoverFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_imageMemberFormula]
  constructor
  · intro property i hi s hs e P x hx index map qField part
    have hP : P ∈ env QB := eqQ.symm ▸ pair_second_mem_doubleUnion qField
    exact (mem_relationImage P (env L) e x).2 ⟨hx,
      property i hi s hs e (ZFSet.pair_mem_prod.1 (maps.1 map)).2
        P hP x hx ⟨index, map, qField, part⟩⟩
  · intro code i hi s hs e _ P _ x hx condition
    exact ((mem_relationImage P (env L) e x).1
      (code i hi s hs e P x hx condition.1 condition.2.1 condition.2.2.1 condition.2.2.2)).2

end BoundedFormula





namespace BoundedFormula

theorem truth_copyLayerFormula {n}
    (Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (copyLayerFormula Qs rs μs L r μ birth t I parts Indices Maps W N injection QB RB MB) env ↔
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth) (env t)
        (env I) (env parts) (env Indices) (env Maps) (env W) (env N) (env injection) := by
  simp only [copyLayerFormula, Truth, truth_doubleUnionEquationFormula, truth_injectionFormula,
    truth_functionFormula, truth_imp, truth_pairMembershipFormula, truth_exMem]
  constructor
  · rintro ⟨eqQ, eqR, eqM, small, indices, maps, embedding, cover, inCopy⟩
    exact ⟨eqQ, eqR, eqM, small, indices, maps,
      (truth_copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB
        env maps eqQ eqR eqM).1 embedding,
      cover, (truth_copyImageCoverFormula Qs L t I parts Indices Maps W QB env maps eqQ).1 inCopy⟩
  · rintro ⟨eqQ, eqR, eqM, code⟩
    exact ⟨eqQ, eqR, eqM, code.small, code.indices, code.maps,
      (truth_copyEmbeddingFamilyFormula Qs rs μs L r μ t I Indices Maps W QB RB MB
        env code.maps eqQ eqR eqM).2 code.embedding,
      code.cover, (truth_copyImageCoverFormula Qs L t I parts Indices Maps W QB env code.maps eqQ).2
        code.inCopy⟩

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_componentImageCoverFormula {n}
    (Qs L t I Components Indices Maps W QB : Fin n) (env : Fin n → ZFSet.{u})
    (maps : ZFSet.IsFunc (env I) (env W) (env Maps)) (eqQ : env QB = ⋃₀ ⋃₀ env Qs) :
    Truth (componentImageCoverFormula Qs L t I Components Indices Maps W QB) env ↔
      ComponentImageCoverCode (env Qs) (env L) (env t) (env I)
        (env Components) (env Indices) (env Maps) := by
  simp only [componentImageCoverFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_imageMemberFormula]
  constructor
  · intro property i hi s hs e P x hx index map qField part
    have hP : P ∈ env QB := eqQ.symm ▸ pair_second_mem_doubleUnion qField
    exact (mem_relationImage P (env L) e x).2 ⟨hx,
      property i hi s hs e (ZFSet.pair_mem_prod.1 (maps.1 map)).2
        P hP x hx ⟨index, map, qField, part⟩⟩
  · intro code i hi s hs e _ P _ x hx condition
    exact ((mem_relationImage P (env L) e x).1
      (code i hi s hs e P x hx condition.1 condition.2.1 condition.2.2.1 condition.2.2.2)).2

theorem truth_componentSeparationFormula {n} (L r μ birth t F I Components : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Truth (componentSeparationFormula L r μ birth t F I Components) env ↔
      ComponentSeparationCode (env L) (env r) (env μ) (env birth)
        (env t) (env F) (env I) (env Components) := by
  simp only [componentSeparationFormula, Truth, truth_imp, truth_pairMembershipFormula]
  constructor
  · intro property x hx y hy i hi j hj first second different
    exact (truth_oldBridgeFormula L.succ.succ.succ.succ r.succ.succ.succ.succ
      μ.succ.succ.succ.succ birth.succ.succ.succ.succ t.succ.succ.succ.succ 3 2
      (extend j (extend i (extend y (extend x env)))) meet).1
      (property x hx y hy i hi j hj ⟨first, second, different⟩)
  · intro code x hx y hy i hi j hj condition
    exact (truth_oldBridgeFormula L.succ.succ.succ.succ r.succ.succ.succ.succ
      μ.succ.succ.succ.succ birth.succ.succ.succ.succ t.succ.succ.succ.succ 3 2
      (extend j (extend i (extend y (extend x env)))) meet).2
      (code x hx y hy i hi j hj condition.1 condition.2.1 condition.2.2)

theorem truth_separatedLayerFormula {n}
    (Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u})
    (meet : MeetOrderCode (env L) (env r) (env μ))
    (eqQ : env QB = ⋃₀ ⋃₀ env Qs) (eqR : env RB = ⋃₀ ⋃₀ env rs)
    (eqM : env MB = ⋃₀ ⋃₀ env μs) :
    Truth (separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB) env ↔
      SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env birth) (env t) (env I) (env Indices) (env Maps) (env W) (env Components) (env F) := by
  simp only [separatedLayerFormula, Truth, truth_functionFormula, truth_layerBirthFiberFormula]
  constructor
  · rintro ⟨indices, maps, fiber, components, embeddings, cover, separated⟩
    exact ⟨indices, maps, fiber, components,
      (truth_copyEmbeddingFamilyFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ env maps eqQ eqR eqM).1 embeddings,
      (truth_componentImageCoverFormula _ _ _ _ _ _ _ _ _ env maps eqQ).1 cover,
      (truth_componentSeparationFormula _ _ _ _ _ _ _ _ env meet).1 separated⟩
  · intro code
    exact ⟨code.indices, code.maps, code.fiber, code.components,
      (truth_copyEmbeddingFamilyFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ env code.maps eqQ eqR eqM).2 code.embedding,
      (truth_componentImageCoverFormula _ _ _ _ _ _ _ _ _ env code.maps eqQ).2 code.cover,
      (truth_componentSeparationFormula _ _ _ _ _ _ _ _ env meet).2 code.separated⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_growthTagFormula (k : Nat) {n} (z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (growthTagFormula k z) env ↔ env z = natSetCode k := by
  induction k generalizing n with
  | zero => exact truth_emptyFormula z env
  | succ k ih =>
    simp only [growthTagFormula, truth_exMem, Truth, truth_successorFormula, ih]
    change (∃ x ∈ env z, env z = insert x x ∧ x = natSetCode k) ↔ _
    constructor
    · rintro ⟨x, _, equal, rfl⟩
      exact equal
    · intro equal
      exact ⟨natSetCode k, equal.symm ▸ (show natSetCode k ∈ natSetCode (k + 1) from by
        rw [natSetCode_succ]; exact ZFSet.mem_insert _ _), equal, rfl⟩

theorem truth_countableTaggedLayerFormula {n} (z tag D injection L birth t N : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (countableTaggedLayerFormula z tag D injection L birth t N) env ↔
      env tag = natSetCode 0 ∧ env z = countableLayerWitness (env D) (env injection) ∧
        CountableLayerCode (env L) (env birth) (env t) (env D) (env N) (env injection) := by
  simp only [countableTaggedLayerFormula, Truth, truth_growthTagFormula,
    truth_nonemptyTupleFormula, truth_countableLayerFormula]
  constructor
  · rintro ⟨tagged, tuple, code⟩
    refine ⟨tagged, ?_, code⟩
    simpa only [countableLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
  · rintro ⟨tagged, tuple, code⟩
    refine ⟨tagged, ?_, code⟩
    simpa only [countableLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple

theorem truth_copyTaggedLayerFormula {n}
    (z tag I parts Indices Maps W injection Qs rs μs L r μ birth t N QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (copyTaggedLayerFormula z tag I parts Indices Maps W injection Qs rs μs L r μ birth t N QB RB MB) env ↔
      env tag = natSetCode 1 ∧ env z = copyLayerWitness (env I) (env parts) (env Indices)
        (env Maps) (env W) (env injection) ∧
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
        (env t) (env I) (env parts) (env Indices) (env Maps) (env W) (env N) (env injection) := by
  simp only [copyTaggedLayerFormula, Truth, truth_growthTagFormula,
    truth_nonemptyTupleFormula, truth_copyLayerFormula]
  constructor
  · rintro ⟨tagged, tuple, rest⟩
    refine ⟨tagged, ?_, rest⟩
    simpa only [copyLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
  · rintro ⟨tagged, tuple, rest⟩
    refine ⟨tagged, ?_, rest⟩
    simpa only [copyLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple

theorem truth_separatedTaggedLayerFormula {n}
    (z tag I Indices Maps W Components F Qs rs μs L r μ birth t QB RB MB : Fin n)
    (env : Fin n → ZFSet.{u}) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Truth (separatedTaggedLayerFormula z tag I Indices Maps W Components F Qs rs μs L r μ birth t QB RB MB) env ↔
      env tag = natSetCode 2 ∧ env z = separatedLayerWitness (env I) (env Indices)
        (env Maps) (env W) (env Components) (env F) ∧
      env QB = ⋃₀ ⋃₀ env Qs ∧ env RB = ⋃₀ ⋃₀ env rs ∧ env MB = ⋃₀ ⋃₀ env μs ∧
      SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
        (env t) (env I) (env Indices) (env Maps) (env W) (env Components) (env F) := by
  simp only [separatedTaggedLayerFormula, Truth, truth_growthTagFormula,
    truth_nonemptyTupleFormula, truth_doubleUnionEquationFormula]
  constructor
  · rintro ⟨tagged, tuple, eqQ, eqR, eqM, recognized⟩
    refine ⟨tagged, ?_, eqQ, eqR, eqM, ?_⟩
    · simpa only [separatedLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
    · exact (truth_separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB
        env meet eqQ eqR eqM).1 recognized
  · rintro ⟨tagged, tuple, eqQ, eqR, eqM, code⟩
    refine ⟨tagged, ?_, eqQ, eqR, eqM, ?_⟩
    · simpa only [separatedLayerWitness, nonemptyTupleCode, Fin.cases_zero, Fin.cases_succ, tagged] using tuple
    · exact (truth_separatedLayerFormula Qs rs μs L r μ birth t I Indices Maps W Components F QB RB MB
        env meet eqQ eqR eqM).2 code

end PartitionPilot.Forcing.BoundedFormula

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_LiteralQuotientRankBounds
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
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem rank_natSetCode_lt (n : Nat) : ZFSet.rank (natSetCode n) < o := by
  induction n with
  | zero => simpa only [natSetCode_zero, ZFSet.rank_empty] using limit.pos
  | succ n ih =>
    rw [natSetCode_succ, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt ih) ih

theorem rank_equivalenceClasses_lt {A : ZFSet.{u}} (E : ZFSet.{u})
    (carrier : ZFSet.rank A < o) : ZFSet.rank (equivalenceClasses A E) < o := by
  have subset : equivalenceClasses A E ⊆ ZFSet.powerset A :=
    fun _ hx => (ZFSet.mem_sep.1 hx).1
  have bound := ZFSet.rank_mono subset
  rw [ZFSet.rank_powerset] at bound
  exact bound.trans_lt (limit.succ_lt carrier)

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundStrongLimitFormulas
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
namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_relativePowerFormula {n} (a p : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (relativePowerFormula a p) env ↔ env p = M.groundPower (env a) := by
  simp only [relativePowerFormula, realize_imp, Realize]
  have subset (x : ZFSet.{u}) (hx : x ∈ M.sets) :=
    (BoundedFormula.realize_toFormula M (BoundedFormula.subsetFormula 0 a.succ)
      (extend x env) (Fin.cases hx members)).trans
        (BoundedFormula.truth_subsetFormula 0 a.succ (extend x env))
  constructor
  · intro property
    apply ZFSet.ext
    intro x
    rw [M.mem_groundPower]
    constructor
    · intro hx
      have hxM := M.transitive (members p) hx
      exact ⟨hxM, (subset x hxM).1 ((property x hxM).1 hx)⟩
    · rintro ⟨hxM, included⟩
      exact (property x hxM).2 ((subset x hxM).2 included)
  · intro equal x hx
    constructor
    · intro entry
      change x ∈ env p at entry
      rw [equal, M.mem_groundPower] at entry
      exact (subset x hx).2 entry.2
    · intro included
      change x ∈ env p
      rw [equal, M.mem_groundPower]
      exact ⟨hx, (subset x hx).1 included⟩

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

open SetFormula SetRealization
universe u

end PartitionPilot.Forcing

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



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

namespace CompressionStampCode
variable {base stamps limit K : ZFSet.{u}} (code : CompressionStampCode base stamps limit)
include code

theorem function_into_bound (values : ∀ n, compressionStamp base n ∈ K) :
    ZFSet.IsFunc ZFSet.omega K stamps := by
  refine ⟨?_, code.function.2⟩
  intro z hz
  obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
  exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega n, (code.entries n y).1 hz ▸ values n⟩

theorem successor_mem_limit {a : ZFSet.{u}} (ha : a ∈ limit) : insert a a ∈ limit := by
  obtain ⟨n, member⟩ := (code.union a).1 ha
  rw [ordinalSetProperty_eq_code_rank a (ordinalSetProperty_member code.ordinal ha),
    ← ordinalCode_succ, ordinalSetProperty_eq_code_rank limit code.ordinal, mem_ordinalCode_iff]
  exact (Order.succ_le_iff.2 (ZFSet.rank_lt_of_mem member)).trans_lt
    (ZFSet.rank_lt_of_mem (code.stamp_mem_limit n))

theorem rank_isLimit : Order.IsSuccLimit (ZFSet.rank limit) := by
  apply Order.isSuccLimit_iff_of_orderBot.2
  refine ⟨ne_of_gt (bot_le.trans_lt (ZFSet.rank_lt_of_mem code.base_mem_limit)), ?_⟩
  rw [Order.isSuccPrelimit_iff_succ_lt]
  intro a ha
  have member : ordinalCode a ∈ limit := by
    rw [ordinalSetProperty_eq_code_rank limit code.ordinal, mem_ordinalCode_iff]
    exact ha
  have bound := ZFSet.rank_lt_of_mem (code.successor_mem_limit member)
  rw [← ordinalCode_succ, rank_ordinalCode] at bound
  exact bound

end CompressionStampCode

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
include conditions pairing unions powers separation infinite hK

theorem compressionStamp_mem {base : ZFSet.{u}} (hBase : base ∈ K) (n : Nat) :
    compressionStamp base n ∈ K := by
  induction n with
  | zero => exact conditions.successor_mem pairing unions powers separation infinite hK hBase
  | succ n ih => exact conditions.successor_mem pairing unions powers separation infinite hK ih

theorem compressionStamp_limit_mem {base stamps limit : ZFSet.{u}}
    (code : CompressionStampCode base stamps limit) (hBase : base ∈ K)
    (hStamps : stamps ∈ M.sets) : limit ∈ K := by
  have values := conditions.compressionStamp_mem pairing unions powers separation infinite hK hBase
  obtain ⟨δ, hδ, bounded⟩ := conditions.2.2.1 ZFSet.omega conditions.2.1 stamps hStamps
    (code.function_into_bound values)
  have subset : limit ⊆ δ := by
    intro x hx
    obtain ⟨n, member⟩ := (code.union x).1 hx
    exact (ordinalSetProperty_member conditions.1 hδ).1 (compressionStamp base n)
      (bounded _ _ ((code.entries n _).2 rfl)) x member
  obtain ⟨l, eqLimit⟩ := (ordinalSetProperty_iff limit).1 code.ordinal
  obtain ⟨d, eqDelta⟩ := (ordinalSetProperty_iff δ).1 (ordinalSetProperty_member conditions.1 hδ)
  obtain ⟨k, eqK⟩ := (ordinalSetProperty_iff K).1 conditions.1
  rw [eqLimit, eqDelta, ordinalCode_subset_iff] at subset
  rw [eqDelta, eqK, mem_ordinalCode_iff] at hδ
  rw [eqLimit, eqK, mem_ordinalCode_iff]
  exact subset.trans_lt hδ

end GroundInaccessibleConditions

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundCompressionStamps_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K base : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hBase : base ∈ K) :
    ∃ stamps ∈ M.sets, ∃ limit ∈ M.sets,
      limit = naturalFamilyUnion stamps ∧ CompressionStampCode base stamps limit ∧
        limit ∈ K ∧ Order.IsSuccLimit (ZFSet.rank limit) ∧ base ∈ limit := by
  obtain ⟨stamps, hStamps, limit, hLimit, equal, code⟩ :=
    M.exists_groundCompressionStamps pairing unions separation collection infinite
      (M.transitive hK hBase) (ordinalSetProperty_member conditions.1 hBase)
  exact ⟨stamps, hStamps, limit, hLimit, equal, code,
    conditions.compressionStamp_limit_mem pairing unions powers separation infinite hK code hBase hStamps,
    code.rank_isLimit, code.base_mem_limit⟩

end TransitiveGround
end PartitionPilot.Forcing

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

end PartitionPilot.Forcing

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

end PartitionPilot.Forcing.GroundBelow

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundEligibleCaps
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

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem literalTaskBound_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P R U Labels : ZFSet.{u}} (points : ZFSet.rank P < o) (relations : ZFSet.rank R < o)
    (filters : ZFSet.rank U < o) (labels : ZFSet.rank Labels < o) :
    ZFSet.rank (literalTaskBound P R U Labels) < o :=
  rank_product_lt limit points (rank_product_lt limit points
    (rank_product_lt limit relations (rank_product_lt limit points (rank_product_lt limit filters labels))))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem groundPower_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {A : ZFSet.{u}} (bound : ZFSet.rank A < o) : ZFSet.rank (M.groundPower A) < o := by
  have subset : M.groundPower A ⊆ ZFSet.powerset A := fun _ hz => (ZFSet.mem_sep.1 hz).1
  have rankBound := ZFSet.rank_mono subset
  rw [ZFSet.rank_powerset] at rankBound
  exact rankBound.trans_lt (limit.succ_lt bound)

theorem groundRelations_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {A B : ZFSet.{u}} (source : ZFSet.rank A < o) (target : ZFSet.rank B < o) :
    ZFSet.rank (M.groundRelations A B) < o :=
  M.groundPower_rank_lt limit (rank_product_lt limit source target)

theorem groundMeetFilters_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P : ZFSet.{u}} (r μ : ZFSet.{u}) (points : ZFSet.rank P < o) :
    ZFSet.rank (M.groundMeetFilters P r μ) < o :=
  (ZFSet.rank_mono (show M.groundMeetFilters P r μ ⊆ M.groundPower P
    from fun _ hz => (ZFSet.mem_sep.1 hz).1)).trans_lt (M.groundPower_rank_lt limit points)

theorem groundEligibleTasks_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P Labels : ZFSet.{u}} (G r μ A : ZFSet.{u})
    (points : ZFSet.rank P < o) (labels : ZFSet.rank Labels < o) :
    ZFSet.rank (M.groundEligibleTasks P G r μ A Labels) < o :=
  (ZFSet.rank_mono (eligibleTaskSet_subset P G r μ A (M.groundRelations P P)
    (M.groundMeetFilters P r μ) Labels)).trans_lt
      (literalTaskBound_rank_lt limit points (M.groundRelations_rank_lt limit points points)
        (M.groundMeetFilters_rank_lt limit r μ points) labels)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace GroundBelow
variable {M : TransitiveGround.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem meetFilters {P r μ K : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hK : K ∈ M.sets)
    (meet : MeetOrderCode P r μ) (strong : GroundStrongLimit M K) (small : GroundBelow M P K) :
    GroundBelow M (M.groundMeetFilters P r μ) K :=
  (strong.power_closed pairing unions powers separation hP hK small).restrict separation
    (M.groundMeetFilters_mem powers separation hP hr hμ meet) hK
    (fun _ member => (ZFSet.mem_sep.1 member).1)

theorem literalTaskBound {P R U Labels K : ZFSet.{u}}
    (hP : P ∈ M.sets) (hR : R ∈ M.sets) (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (points : GroundBelow M P K) (relations : GroundBelow M R K)
    (filters : GroundBelow M U K) (labels : GroundBelow M Labels K) :
    GroundBelow M (Forcing.literalTaskBound P R U Labels) K := by
  have combine {X Y : ZFSet.{u}} (first : X ∈ M.sets ∧ GroundBelow M X K)
      (second : Y ∈ M.sets ∧ GroundBelow M Y K) :
      ZFSet.prod X Y ∈ M.sets ∧ GroundBelow M (ZFSet.prod X Y) K :=
    ⟨M.prod_mem pairing unions powers separation first.1 second.1,
      GroundBelow.product pairing unions powers separation first.1 second.1 hK ordinal strong first.2 second.2⟩
  exact (combine ⟨hP, points⟩ (combine ⟨hP, points⟩ (combine ⟨hR, relations⟩
    (combine ⟨hP, points⟩ (combine ⟨hU, filters⟩ ⟨hLabels, labels⟩))))).2

end GroundBelow

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem groundEligibleTasks_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels K : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets)
    (meet : MeetOrderCode P r μ) (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (points : GroundBelow M P K) (labels : GroundBelow M Labels K) :
    GroundBelow M (M.groundEligibleTasks P G r μ A Labels) K := by
  have hR := M.groundRelations_mem pairing unions powers separation hP hP
  have hU := M.groundMeetFilters_mem powers separation hP hr hμ meet
  have relations := GroundBelow.relations pairing unions powers separation hP hP hK ordinal strong points points
  have filters := GroundBelow.meetFilters pairing unions powers separation hP hr hμ hK meet strong points
  have bound := GroundBelow.literalTaskBound pairing unions powers separation hP hR hU hLabels hK
    ordinal strong points relations filters labels
  exact bound.restrict separation
    (M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet) hK
    (eligibleTaskSet_subset P G r μ A (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)

end TransitiveGround
end PartitionPilot.Forcing



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
open SetRealization
universe u

theorem rank_taggedExtension_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P N : ZFSet.{u}} (points : ZFSet.rank P < o) (fresh : ZFSet.rank N < o) :
    ZFSet.rank (taggedExtension P N) < o := by
  rw [taggedExtension, ZFSet.rank_union]
  exact max_lt points (rank_product_lt limit (rank_singleton_lt limit points) fresh)

namespace RecursiveTemplateConstancy
variable {P r μ : ZFSet.{u}} {initial : RecursiveStateData.{u}}
variable (constant : RecursiveTemplateConstancy P r μ initial)
include constant

theorem fresh_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (indices : ZFSet.rank initial.J < o) (templates : ZFSet.rank P < o) :
    ZFSet.rank initial.fresh < o := by
  have subset : initial.fresh ⊆ ZFSet.prod initial.J P := by
    intro z hz
    have domain := indexedAttachmentFresh_subset initial.J initial.Qs initial.rs initial.As hz
    obtain ⟨i, hi, q, rfl, Q, entry, hq⟩ := (mem_indexedAttachmentDomain _ _ _).1 domain
    exact ZFSet.pair_mem_prod.2 ⟨hi, (constant.space_entry_iff i Q).1 entry |>.2 ▸ hq⟩
  exact (ZFSet.rank_mono subset).trans_lt (rank_product_lt limit indices templates)

theorem currentCarrier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank initial.D < o) (indices : ZFSet.rank initial.J < o)
    (templates : ZFSet.rank P < o) : ZFSet.rank initial.currentCarrier < o :=
  rank_taggedExtension_lt limit points (constant.fresh_rank_lt limit indices templates)

theorem iterate_carrier_ranks (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u})
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank initial.D < o) (indices : ZFSet.rank initial.J < o)
    (templates : ZFSet.rank P < o) (tasks : ZFSet.rank I < o) (n : Nat) :
    ZFSet.rank (initial.iterate M I Sources Reps G T n).D < o ∧
      ZFSet.rank (initial.iterate M I Sources Reps G T n).J < o := by
  induction n with
  | zero => exact ⟨points, indices⟩
  | succ n ih =>
    rw [RecursiveStateData.iterate_succ]
    refine ⟨(constant.iterate M I Sources Reps G T n).currentCarrier_rank_lt limit ih.1 ih.2 templates, ?_⟩
    exact (ZFSet.rank_mono (recursiveAttachmentIndices_subset _ _ _ _ _ _)).trans_lt
      (rank_product_lt limit tasks ih.2)

end RecursiveTemplateConstancy

theorem NatUnionCode.rank_le {sets : Nat → ZFSet.{u}} {U : ZFSet.{u}} (code : NatUnionCode sets U)
    {o : Ordinal.{u}} (bounds : ∀ n, ZFSet.rank (sets n) < o) : ZFSet.rank U ≤ o := by
  apply ZFSet.rank_le_iff.2
  intro x hx
  obtain ⟨n, member⟩ := (code x).1 hx
  exact (ZFSet.rank_lt_of_mem member).trans (bounds n)

namespace GroundCompressionUnionData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (data : GroundCompressionUnionData M initial I Sources Reps G m one T)

theorem carrier_rank_le {P r μ : ZFSet.{u}} (constant : RecursiveTemplateConstancy P r μ initial)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank initial.D < o) (indices : ZFSet.rank initial.J < o)
    (templates : ZFSet.rank P < o) (tasks : ZFSet.rank I < o) :
    ZFSet.rank (data.fields 0) ≤ o :=
  (data.fieldUnion 0).rank_le
    (fun n => (constant.iterate_carrier_ranks M I Sources Reps G T limit points indices templates tasks n).1)

end GroundCompressionUnionData

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
include pairing unions powers separation hI hSources hReps hG hT

theorem union_order_iff (n : Nat) {x y : ZFSet.{u}}
    (hx : x ∈ (state.data.iterate M I Sources Reps G T n).D)
    (hy : y ∈ (state.data.iterate M I Sources Reps G T n).D) :
    ZFSet.pair x y ∈ data.fields 1 ↔ ZFSet.pair x y ∈ (state.data.iterate M I Sources Reps G T n).rD :=
  (data.fieldUnion 1).order_entry_iff
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation hI hSources hReps hG hT h).2.1)
    (fun _ _ h => (state.canonical_iterate_coherent pairing unions powers separation hI hSources hReps hG hT h).order)
    n hx hy

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

end TransitiveGround

open SetFormula
universe u

end PartitionPilot.Forcing

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

end GroundCompressionState

section
open SetFormula
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)

theorem union_input_capProfile
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {c e K F : ZFSet.{u}}
    (profile : CodedCapProfile state.data.D state.data.rD state.data.μD c e K F) :
    CodedCapProfile (data.fields 0) (data.fields 1) (data.fields 2) c e K F := by
  have hc : c ∈ state.data.currentCarrier := old_mem_taggedExtension profile.target_mem
  have he : e ∈ state.data.currentCarrier := old_mem_taggedExtension profile.separator_mem
  have hK : K ∈ state.data.currentCarrier := old_mem_taggedExtension profile.cap_mem
  have subset : F ⊆ state.data.currentCarrier := fun _ hf => old_mem_taggedExtension (profile.filter_subset hf)
  have first := state.batch.insertion_profile_persists profile.target_mem profile.separator_mem
    profile.cap_mem profile.filter_subset profile.nonempty profile.profile profile.separator_not_below_cap
  have separated : ZFSet.pair e K ∉ state.data.currentOrder := by
    intro lower
    exact profile.separator_not_below_cap
      ((state.batch.old_order_iff profile.separator_mem profile.cap_mem).1 lower)
  refine ⟨(data.fieldUnion 0).subset 0 profile.target_mem,
    (data.fieldUnion 0).subset 0 profile.separator_mem,
    (data.fieldUnion 0).subset 0 profile.cap_mem,
    fun _ hf => (data.fieldUnion 0).subset 0 (profile.filter_subset hf), profile.nonempty,
    state.union_profile data pairing unions powers separation hI hSources hReps hG hT
      hc he hK subset profile.nonempty first separated, ?_, ?_, ?_⟩
  · exact (state.union_order_iff data pairing unions powers separation hI hSources hReps hG hT
      0 profile.target_mem profile.cap_mem).2 profile.target_below_cap
  · intro lower
    exact profile.cap_not_below_target ((state.union_order_iff data pairing unions powers separation
      hI hSources hReps hG hT 0 profile.cap_mem profile.target_mem).1 lower)
  · intro lower
    exact profile.separator_not_below_cap ((state.union_order_iff data pairing unions powers separation
      hI hSources hReps hG hT 0 profile.separator_mem profile.cap_mem).1 lower)

end GroundCompressionState

namespace GroundCompressionOrigin
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)

include origin in
theorem union_input_capProfile
    (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {c e K F : ZFSet.{u}} (profile : CodedCapProfile initial.D initial.rD initial.μD c e K F) :
    CodedCapProfile (data.fields 0) (data.fields 1) (data.fields 2) c e K F := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  exact state.union_input_capProfile data pairing unions powers separation
    hI hSources hReps hG hT profile

end GroundCompressionOrigin
end

end PartitionPilot.Forcing

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

end PartitionPilot.Forcing.BoundedFormula

end

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



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_chronologyPointFormula {n} (T C D rD s L r μ birth height : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyPointFormula T C D rD s L r μ birth height) env ↔
      ChronologyPointCode (env T) (env C) (env D) (env rD) (env s)
        (env L) (env r) (env μ) (env birth) (env height) := by
  simp only [chronologyPointFormula, Truth, truth_meetOrderFormula,
    truth_functionFormula, truth_strictLexHeightFormula]
  constructor
  · rintro ⟨meet, function, bound, old, strict⟩
    exact ⟨meet, function, (truth_birthBoundFormula L T birth s env function).1 bound,
      (truth_oldMeetFormula L T r μ birth env function).1 old, strict⟩
  · intro code
    exact ⟨code.meet, code.birth_function,
      (truth_birthBoundFormula L T birth s env code.birth_function).2 code.birth_bound,
      (truth_oldMeetFormula L T r μ birth env code.birth_function).2 code.old_meet,
      code.strict_height⟩

end BoundedFormula





namespace BoundedFormula

theorem truth_chronologyFunctionsFormula {n} (T V : Fin n) (graphs : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyFunctionsFormula T V graphs) env ↔
      ∀ j, ZFSet.IsFunc (env T) (env V) (env (graphs j)) := by
  simp only [chronologyFunctionsFormula, Truth, truth_functionFormula]
  exact ⟨fun ⟨a, b, c, d, e⟩ => Fin.cases a (Fin.cases b (Fin.cases c
      (Fin.cases d (Fin.cases e (fun i => Fin.elim0 i))))),
    fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩⟩

theorem truth_chronologyCoreFormula {n} (T V C D rD : Fin n) (graphs : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyCoreFormula T V C D rD graphs) env ↔
      ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j)) := by
  simp only [chronologyCoreFormula, Truth, truth_chronologyFunctionsFormula,
    chronologyPointsFormula, truth_imp, truth_pairMembershipFormula, truth_chronologyPointFormula]
  constructor
  · rintro ⟨function, point⟩
    refine ⟨function, ?_⟩
    intro s hs L r μ birth height eL er eμ eb eh
    exact point s hs L (ZFSet.pair_mem_prod.1 ((function 0).1 eL)).2
      r (ZFSet.pair_mem_prod.1 ((function 1).1 er)).2
      μ (ZFSet.pair_mem_prod.1 ((function 2).1 eμ)).2
      birth (ZFSet.pair_mem_prod.1 ((function 3).1 eb)).2
      height (ZFSet.pair_mem_prod.1 ((function 4).1 eh)).2 ⟨eL, er, eμ, eb, eh⟩
  · intro code
    exact ⟨code.function, fun s hs L _ r _ μ _ birth _ height _ ⟨eL, er, eμ, eb, eh⟩ =>
      code.point s hs L r μ birth height eL er eμ eb eh⟩

theorem realize_chronologyCoreFormula (M : TransitiveGround.{u}) {n}
    (T V C D rD : Fin n) (graphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyCoreFormula T V C D rD graphs).toFormula env ↔
      ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j)) :=
  (realize_toFormula M _ env members).trans (truth_chronologyCoreFormula T V C D rD graphs env)

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundSerializedChronology
universe u
variable {M : TransitiveGround.{u}} {T T' C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)

theorem castTime_code (equal : T = T') : (serial.castTime equal).code = serial.code := by
  cases equal
  rfl

theorem castTime_value (equal : T = T') (j : Fin 5) (s : ZFSet.{u}) :
    (serial.castTime equal).fields.value j s = serial.fields.value j s := by
  cases equal
  rfl

end PartitionPilot.Forcing.GroundSerializedChronology

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



namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem initialCompressionData_template_constancy (P G r μ A Labels : ZFSet.{u}) :
    RecursiveTemplateConstancy P r μ (M.initialCompressionData P G r μ A Labels) :=
  ⟨rfl, rfl, rfl⟩

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

namespace TransitiveGround

open SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem finiteWords_subset_powerset (A : ZFSet.{u}) :
    M.finiteWords A ⊆ ZFSet.powerset (ZFSet.prod ZFSet.omega A) := by
  intro f hf
  have relation := (ZFSet.mem_sep.1 hf).1
  exact ZFSet.mem_powerset.2 ((M.mem_groundRelations ZFSet.omega A f).1 relation).2

theorem finiteWords_rank_le (A : ZFSet.{u}) :
    ZFSet.rank (M.finiteWords A) ≤ Order.succ (ZFSet.rank (ZFSet.prod ZFSet.omega A)) := by
  have bound := ZFSet.rank_mono (M.finiteWords_subset_powerset A)
  rwa [ZFSet.rank_powerset] at bound

theorem finiteWords_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) {A : ZFSet.{u}}
    (omega : ZFSet.rank ZFSet.omega < o) (alphabet : ZFSet.rank A < o) :
    ZFSet.rank (M.finiteWords A) < o :=
  (M.finiteWords_rank_le A).trans_lt (limit.succ_lt (rank_product_lt limit omega alphabet))

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_IdealInsertionProfileTransport
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.IdealEmbeddingCode
open Compression Compression.RecursiveMaps
universe u
variable {P Q rP rQ μP μQ e : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
variable (source : MeetOrderCode P rP μP) (target : MeetOrderCode Q rQ μQ)

include code source target in
theorem capProfile {top c v K F c' v' K' : ZFSet.{u}}
    (hTop : top ∈ P) (greatest : ∀ x ∈ P, ZFSet.pair x top ∈ rP)
    (profile : CodedCapProfile P rP μP c v K F)
    (imageC : ZFSet.pair c c' ∈ e) (imageV : ZFSet.pair v v' ∈ e) (imageK : ZFSet.pair K K' ∈ e) :
    CodedCapProfile Q rQ μQ c' v' K' (relationImage F Q e) := by
  let embed := code.toIdealEmbedding source target
  have hc' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 imageC)).2
  have hv' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 imageV)).2
  have hK' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 imageK)).2
  have subset : relationImage F Q e ⊆ Q := by
    intro x hx
    exact ((mem_relationImage _ _ _ _).1 hx).1
  have nonempty : ∃ f, f ∈ relationImage F Q e := by
    obtain ⟨f, hf⟩ := profile.nonempty
    obtain ⟨y, entry, _⟩ := code.injection.function.2 f (profile.filter_subset hf)
    exact ⟨y, (mem_relationImage _ _ _ _).2 ⟨(ZFSet.pair_mem_prod.1 (code.injection.function.1 entry)).2, f, hf, entry⟩⟩
  have old := (CodedInsertionProfile.iff_profile source profile.target_mem profile.separator_mem profile.cap_mem
    profile.filter_subset).1 profile.profile
  have ne : ∃ f : {f : ZFSet.{u} // f ∈ P}, f.val ∈ F := by
    obtain ⟨f, hf⟩ := profile.nonempty
    exact ⟨⟨f, profile.filter_subset hf⟩, hf⟩
  have inherited := embed.preservesProfiles ⟨top,hTop⟩ (fun x => greatest x.val x.property)
    ⟨c,profile.target_mem⟩ ⟨v,profile.separator_mem⟩ ⟨K,profile.cap_mem⟩ (fun f => f.val ∈ F)
    ne profile.separator_not_below_cap old
  have ec : embed.toFun ⟨c,profile.target_mem⟩ = ⟨c',hc'⟩ :=
    (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target _ _).2 imageC
  have ev : embed.toFun ⟨v,profile.separator_mem⟩ = ⟨v',hv'⟩ :=
    (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target _ _).2 imageV
  have ek : embed.toFun ⟨K,profile.cap_mem⟩ = ⟨K',hK'⟩ :=
    (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target _ _).2 imageK
  have pred : (fun y : {y : ZFSet.{u} // y ∈ Q} => y.val ∈ relationImage F Q e) =
      imageFamily embed.toMeetEmbedding (fun f => f.val ∈ F) := by
    funext y
    apply propext
    rw [mem_relationImage]
    constructor
    · rintro ⟨_, x, hx, entry⟩
      exact ⟨⟨x,profile.filter_subset hx⟩, hx,
        (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target _ y).2 entry⟩
    · rintro ⟨x, hx, equal⟩
      exact ⟨y.property, x.val, hx,
        (code.toMeetEmbeddingCode.toMeetEmbedding_eq_iff source target x y).1 equal⟩
  have transported := (profileOver_iff_image embed.toMeetEmbedding _ _ _ _).1 inherited
  rw [ec, ev, ek, ← pred] at transported
  exact ⟨hc', hv', hK', subset, nonempty,
    (CodedInsertionProfile.iff_profile target hc' hv' hK' subset).2 transported,
    code.monotone _ _ _ _ profile.target_below_cap imageC imageK,
    fun lower => profile.cap_not_below_target (code.reflect _ _ _ _ imageK imageC lower),
    fun lower => profile.separator_not_below_cap (code.reflect _ _ _ _ imageV imageK lower)⟩

end PartitionPilot.Forcing.IdealEmbeddingCode

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_ExternalRequestRankBounds
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
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem externalRectangleBound_rank_lt {P G : ZFSet.{u}}
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (externalRectangleBound P G) < o :=
  rank_product_lt limit points (rank_product_lt limit points
    (rank_product_lt limit points (rank_product_lt limit actors actors)))

theorem externalRectangles_rank_lt {P G : ZFSet.{u}} (r μ A : ZFSet.{u})
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (externalRectangles P G r μ A) < o :=
  (ZFSet.rank_mono (show externalRectangles P G r μ A ⊆ externalRectangleBound P G from
    fun _ hx => (ZFSet.mem_sep.1 hx).1)).trans_lt
      (externalRectangleBound_rank_lt limit points actors)

theorem externalRequestCarrier_rank_lt {I P Rectangles : ZFSet.{u}}
    (indices : ZFSet.rank I < o) (points : ZFSet.rank P < o)
    (rectangles : ZFSet.rank Rectangles < o) :
    ZFSet.rank (externalRequestCarrier I P Rectangles) < o := by
  have tag := fun n => rank_singleton_lt limit (rank_natSetCode_lt limit n)
  rw [externalRequestCarrier, ZFSet.rank_union, ZFSet.rank_union]
  exact max_lt (max_lt (rank_product_lt limit (tag 0) indices)
    (rank_product_lt limit (tag 1) points)) (rank_product_lt limit (tag 2) rectangles)

theorem externalChildLetters_rank_lt {I P Rectangles : ZFSet.{u}}
    (indices : ZFSet.rank I < o) (points : ZFSet.rank P < o)
    (rectangles : ZFSet.rank Rectangles < o) :
    ZFSet.rank (externalChildLetters I P Rectangles) < o := by
  have tag := fun n => rank_singleton_lt limit (rank_natSetCode_lt limit n)
  rw [externalChildLetters, ZFSet.rank_union]
  exact max_lt
    (rank_product_lt limit (externalRequestCarrier_rank_lt limit indices points rectangles) (tag 0))
    (rank_product_lt limit (rank_product_lt limit (tag 2) rectangles) (tag 1))

theorem externalGeneratorAlphabet_rank_lt {G S : ZFSet.{u}}
    (actors : ZFSet.rank G < o) (letters : ZFSet.rank S < o) :
    ZFSet.rank (externalGeneratorAlphabet G S) < o := by
  rw [externalGeneratorAlphabet, ZFSet.rank_union]
  exact max_lt
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 0)) actors)
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 1))
      (rank_product_lt limit letters (rank_natSetCode_lt limit 2)))

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalStarCarrierRanks
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
variable (M : TransitiveGround.{u})
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem externalGroupCarrier_rank_lt {G S : ZFSet.{u}} (m one : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o)
    (actors : ZFSet.rank G < o) (letters : ZFSet.rank S < o) :
    ZFSet.rank (M.externalGroupCarrier G S m one) < o :=
  rank_equivalenceClasses_lt limit (M.externalWordEquivalence G S m one)
    (M.finiteWords_rank_lt limit omega (externalGeneratorAlphabet_rank_lt limit actors letters))

theorem externalRequestGroup_rank_lt {I P G : ZFSet.{u}} (r μ A m one : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (M.externalGroupCarrier G
      (externalChildLetters I P (externalRectangles P G r μ A)) m one) < o :=
  M.externalGroupCarrier_rank_lt limit m one omega actors
    (externalChildLetters_rank_lt limit indices points (externalRectangles_rank_lt limit r μ A points actors))

end TransitiveGround

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem externalPointCarrier_rank_lt {P r μ A : ZFSet.{u}}
    (actors : ZFSet.rank (M.externalGroupCarrier G
      (externalChildLetters I P (externalRectangles P G r μ A)) m one) < o)
    (completed : ZFSet.rank (completion.algebra.union.fields 0) < o) :
    ZFSet.rank (completion.externalPointCarrier P r μ A) < o :=
  rank_equivalenceClasses_lt limit (completion.externalFlatEquivalence P r μ A)
    (rank_product_lt limit actors completed)

theorem externalPointCarrier_rank_lt_of_inputs {P : ZFSet.{u}} (r μ A : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o)
    (completed : ZFSet.rank (completion.algebra.union.fields 0) < o) :
    ZFSet.rank (completion.externalPointCarrier P r μ A) < o :=
  completion.externalPointCarrier_rank_lt limit
    (M.externalRequestGroup_rank_lt limit r μ A m one omega indices points actors) completed

theorem externalBoundedCarrier_rank_lt {P : ZFSet.{u}} (r μ A : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o)
    (completed : ZFSet.rank (completion.algebra.union.fields 0) < o) :
    ZFSet.rank (completion.externalBoundedCarrier P r μ A) < o :=
  rank_fixedTopCarrier_lt limit
    (completion.externalPointCarrier_rank_lt_of_inputs limit r μ A omega indices points actors completed)

end GroundCompressionCompletion
end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainTransitionValidityCodes
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

theorem truth_mainTransitionLawsFormula {n}
    (P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mainTransitionLawsFormula P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors) env ↔
    MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H)
      (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ)
      (env heightP) (env heightQ) (env points) (env actors) := by
  simp only [mainTransitionLawsFormula, transitionOrderFormula, transitionEquivarianceFormula,
    transitionHeightFormula, transitionAgreementFormula, Truth, truth_meetEmbeddingFormula,
    truth_groupEmbeddingFormula, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula, truth_graphFiberEqualityFormula, truth_actionAgreementBelowFormula]
  constructor
  · rintro ⟨point, order, group, equivariant, bottom, height, agreement⟩
    have pb {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env points) : x ∈ env P ∧ y ∈ env Q :=
      ZFSet.pair_mem_prod.1 (point.injection.function.1 entry)
    have ab {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env actors) : x ∈ env G ∧ y ∈ env H :=
      ZFSet.pair_mem_prod.1 (group.injection.function.1 entry)
    refine ⟨point, ?_, group, ?_, bottom, ?_, ?_⟩
    · intro x y x' y' xx yy
      have h := order x (pb xx).1 y (pb yy).1 x' (pb xx).2 y' (pb yy).2 ⟨xx, yy⟩
      exact ⟨h.1, h.2⟩
    · intro g g' x y x' y' gg xx yy act
      exact equivariant g (ab gg).1 g' (ab gg).2 x (pb xx).1 y (pb yy).1
        x' (pb xx).2 y' (pb yy).2 ⟨gg, xx, yy, act⟩
    · intro x y z entry
      exact height x (pb entry).1 y (pb entry).2 entry z
    · intro g h g' h' v v' gg hh vv agree
      exact agreement g (ab gg).1 h (ab hh).1 g' (ab gg).2 h' (ab hh).2
        v (pb vv).1 v' (pb vv).2 ⟨gg, hh, vv, agree⟩
  · intro code
    refine ⟨code.point_embedding, ?_, code.group_embedding, ?_, code.bottom, ?_, ?_⟩
    · intro x _ y _ x' _ y' _ h
      exact ⟨(code.order_iff x y x' y' h.1 h.2).1, (code.order_iff x y x' y' h.1 h.2).2⟩
    · intro g _ g' _ x _ y _ x' _ y' _ h
      exact code.equivariant g g' x y x' y' h.1 h.2.1 h.2.2.1 h.2.2.2
    · intro x _ y _ entry z
      exact code.height x y z entry
    · intro g _ h _ g' _ h' _ v _ v' _ entries
      exact code.agreement g h g' h' v v' entries.1 entries.2.1 entries.2.2.1 entries.2.2.2

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainTransitionValidity
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

theorem truth_validMainTransitionCodeFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors) env ↔
      env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H)
        (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ)
        (env heightP) (env heightQ) (env points) (env actors) := by
  simp only [validMainTransitionCodeFormula, Truth, truth_orderedPairFormula,
    truth_mainTransitionLawsFormula]

end BoundedFormula
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTwoStageMainDiagram
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

namespace GroundChronologicalMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundChronologicalMainStage M C D rD)

theorem birth_ground : stage.birth ∈ M.sets :=
  stage.history.birth_mem stage.cutoff (ZFSet.mem_insert _ _)

end GroundChronologicalMainStage

end

section
open SetFormula
universe u

namespace BoundedFormula

theorem truth_graphCutoffEqualityFormula {n} (cutoff source target : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (graphCutoffEqualityFormula cutoff source target) env ↔
      ∀ s, s = env cutoff ∨ s ∈ env cutoff → ∀ x,
        ZFSet.pair s x ∈ env source ↔ ZFSet.pair s x ∈ env target := by
  simp only [graphCutoffEqualityFormula, Truth, truth_graphFiberEqualityFormula]
  constructor
  · rintro ⟨terminal, earlier⟩ s (rfl | hs) x
    · exact terminal x
    · exact earlier s hs x
  · intro h
    exact ⟨h _ (Or.inl rfl), fun s hs => h s (Or.inr hs)⟩

theorem truth_chronologyGraphPrefixFormula {n} (cutoff : Fin n) (source target : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyGraphPrefixFormula cutoff source target) env ↔
      ChronologyGraphPrefixCode (env cutoff) (fun j => env (source j)) (fun j => env (target j)) := by
  simp only [chronologyGraphPrefixFormula, Truth, truth_graphCutoffEqualityFormula]
  exact ⟨fun ⟨a, b, c, d, e⟩ => Fin.cases a (Fin.cases b (Fin.cases c
      (Fin.cases d (Fin.cases e (fun i => Fin.elim0 i))))),
    fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩⟩

theorem truth_chronologicalTransitionExtraFormula {n}
    (P Q points sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u})
    (shape : env points ⊆ ZFSet.prod (env P) (env Q)) :
    Truth (chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs) env ↔
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j)) := by
  simp only [chronologicalTransitionExtraFormula, Truth, truth_disj, transitionHeightFormula,
    truth_imp, truth_pairMembershipFormula, truth_graphFiberEqualityFormula,
    truth_chronologyGraphPrefixFormula]
  constructor
  · rintro ⟨cutoff, birth, history⟩
    refine ⟨cutoff, ?_, history⟩
    intro x y t entry
    have bounds := ZFSet.pair_mem_prod.1 (shape entry)
    exact birth x bounds.1 y bounds.2 entry t
  · intro h
    exact ⟨h.cutoff_le, fun x _ y _ entry t => h.birth x y t entry, h.history_prefix⟩

theorem truth_oldBirthFiberCoverageFormula {n} (P points birth cutoff : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (oldBirthFiberCoverageFormula P points birth cutoff) env ↔
      OldBirthFiberCoverageCode (env P) (env points) (env birth) (env cutoff) := by
  simp only [oldBirthFiberCoverageFormula, Truth, truth_imp, truth_orderedPairFormula,
    truth_disj, truth_exMem, truth_pairMembershipFormula]
  change (∀ p ∈ env birth, ∀ a ∈ p, ∀ y ∈ a, ∀ b ∈ p, ∀ t ∈ b,
    (p = ZFSet.pair y t ∧ (t = env cutoff ∨ t ∈ env cutoff)) →
      ∃ x ∈ env P, ZFSet.pair x y ∈ env points) ↔ _
  constructor
  · intro h y t entry before
    exact h (ZFSet.pair y t) entry {y, t} (ZFSet.mem_pair.2 (Or.inr rfl)) y
      (ZFSet.mem_pair.2 (Or.inl rfl)) {y, t} (ZFSet.mem_pair.2 (Or.inr rfl)) t
      (ZFSet.mem_pair.2 (Or.inr rfl)) ⟨rfl, before⟩
  · intro h p hp a _ y _ b _ t _ data
    exact h y t (data.1 ▸ hp) data.2

end BoundedFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundBelowMainGraphs
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
variable {M : TransitiveGround.{u}} {C D rD K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets)
include pairing unions powers separation hK

namespace GroundMainTransition

theorem graphs_below {source target : GroundMainStage M C D rD}
    (transition : GroundMainTransition source target)
    (points : GroundBelow M source.carrier K) (actors : GroundBelow M source.actors K) :
    GroundBelow M transition.points K ∧ GroundBelow M transition.actors K :=
  ⟨points.functionGraph pairing unions powers separation source.carrier_ground transition.points_ground hK
      transition.point_embedding.injection.function,
    actors.functionGraph pairing unions powers separation source.actors_ground transition.actors_ground hK
      transition.group_embedding.injection.function⟩

end GroundMainTransition
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_GroundMainCodeRanks
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
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

namespace GroundMainStage
variable (stage : GroundMainStage M C D rD) {o : Ordinal.{u}}

theorem field_rank_lt (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank stage.carrier < o) (actors : ZFSet.rank stage.actors < o)
    (columns : ZFSet.rank C < o) (coordinates : ZFSet.rank D < o) :
    ∀ j, ZFSet.rank (stage.field j) < o := by
  have pp := rank_product_lt limit points points
  have gg := rank_product_lt limit actors actors
  have order := (ZFSet.rank_mono stage.meet.order.relation).trans_lt pp
  have meet := rank_functionGraph_lt limit stage.meet.operation pp points
  have mul := rank_functionGraph_lt limit stage.group_code.mul_function gg actors
  have inv := rank_functionGraph_lt limit stage.group_code.inv_function actors actors
  have one := (ZFSet.rank_lt_of_mem stage.group_code.identity_mem).trans actors
  have action := rank_functionGraph_lt limit stage.action_code.function
    (rank_product_lt limit actors points) points
  have bottom := (ZFSet.rank_lt_of_mem stage.bottom_mem).trans points
  have top := (ZFSet.rank_lt_of_mem stage.top_mem).trans points
  have height := rank_functionGraph_lt limit stage.height_code.function points
    (rank_product_lt limit columns coordinates)
  exact Fin.cases points (Fin.cases order (Fin.cases meet (Fin.cases actors (Fin.cases mul
    (Fin.cases inv (Fin.cases one (Fin.cases action (Fin.cases bottom (Fin.cases top
      (Fin.cases height (fun i => Fin.elim0 i)))))))))))

theorem code_rank_lt (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank stage.carrier < o) (actors : ZFSet.rank stage.actors < o)
    (columns : ZFSet.rank C < o) (coordinates : ZFSet.rank D < o) :
    ZFSet.rank stage.code < o :=
  rank_nonemptyTupleCode_lt limit 10 stage.field (stage.field_rank_lt limit points actors columns coordinates)

theorem code_rank_lt_inaccessible
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (points : ZFSet.rank stage.carrier < ZFSet.rank K) (actors : ZFSet.rank stage.actors < ZFSet.rank K)
    (columns : ZFSet.rank C < ZFSet.rank K) (coordinates : ZFSet.rank D < ZFSet.rank K) :
    ZFSet.rank stage.code < ZFSet.rank K :=
  stage.code_rank_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    points actors columns coordinates

end GroundMainStage

namespace GroundMainTransition
variable {source target : GroundMainStage M C D rD}
variable (transition : GroundMainTransition source target) {o : Ordinal.{u}}

theorem graphs_rank_lt (limit : Order.IsSuccLimit o)
    (sourcePoints : ZFSet.rank source.carrier < o) (targetPoints : ZFSet.rank target.carrier < o)
    (sourceActors : ZFSet.rank source.actors < o) (targetActors : ZFSet.rank target.actors < o) :
    ZFSet.rank transition.points < o ∧ ZFSet.rank transition.actors < o :=
  ⟨rank_functionGraph_lt limit transition.point_embedding.injection.function sourcePoints targetPoints,
    rank_functionGraph_lt limit transition.group_embedding.injection.function sourceActors targetActors⟩

theorem code_rank_lt (limit : Order.IsSuccLimit o)
    (sourcePoints : ZFSet.rank source.carrier < o) (targetPoints : ZFSet.rank target.carrier < o)
    (sourceActors : ZFSet.rank source.actors < o) (targetActors : ZFSet.rank target.actors < o) :
    ZFSet.rank transition.code < o := by
  have bounds := transition.graphs_rank_lt limit sourcePoints targetPoints sourceActors targetActors
  exact rank_orderedPair_lt limit bounds.1 bounds.2

theorem code_rank_lt_inaccessible
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (sourcePoints : ZFSet.rank source.carrier < ZFSet.rank K)
    (targetPoints : ZFSet.rank target.carrier < ZFSet.rank K)
    (sourceActors : ZFSet.rank source.actors < ZFSet.rank K)
    (targetActors : ZFSet.rank target.actors < ZFSet.rank K) :
    ZFSet.rank transition.code < ZFSet.rank K :=
  transition.code_rank_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    sourcePoints targetPoints sourceActors targetActors

end GroundMainTransition
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBelowInitialCompression
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation choice

theorem indexedAttachmentDomain {I Qs : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (family : FunctionGraphOn I Qs) (indices : GroundBelow M I K)
    (templates : ∀ i Q, ZFSet.pair i Q ∈ Qs → GroundBelow M Q K) :
    GroundBelow M (Forcing.indexedAttachmentDomain I Qs) K := by
  have hBound := M.union_mem unions (M.union_mem unions hQs)
  have hRange := M.relationImage_mem separation hI hBound hQs
  have points := GroundBelow.indexed_sUnion pairing unions powers separation choice hI hBound hQs hK
    ordinal regular strong indices family.to_isFunc templates
  have small := GroundBelow.product pairing unions powers separation hI (M.union_mem unions hRange)
    hK ordinal strong indices points
  apply small.restrict separation (M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs) hK
  intro z hz
  obtain ⟨i, hi, q, rfl, Q, entry, hq⟩ := (mem_indexedAttachmentDomain I Qs z).1 hz
  exact ZFSet.pair_mem_prod.2 ⟨hi, ZFSet.mem_sUnion.2
    ⟨Q, (mem_relationImage I Qs.sUnion.sUnion Qs Q).2
      ⟨pair_second_mem_doubleUnion entry, i, hi, entry⟩, hq⟩⟩

theorem indexedAttachmentFresh {I Qs rs As : ZFSet.{u}}
    (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (strong : GroundStrongLimit M K) (family : FunctionGraphOn I Qs) (indices : GroundBelow M I K)
    (templates : ∀ i Q, ZFSet.pair i Q ∈ Qs → GroundBelow M Q K) :
    GroundBelow M (Forcing.indexedAttachmentFresh I Qs rs As) K :=
  (GroundBelow.indexedAttachmentDomain pairing unions powers separation choice hI hQs hK
    ordinal regular strong family indices templates).restrict separation
      (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs) hK
      (indexedAttachmentFresh_subset I Qs rs As)

variable (infinite : Realize M.sets infinity Fin.elim0)
include infinite

theorem taggedExtension {P N : ZFSet.{u}}
    (hP : P ∈ M.sets) (hN : N ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (old : GroundBelow M P K) (fresh : GroundBelow M N K) :
    GroundBelow M (Forcing.taggedExtension P N) K := by
  have hSingle : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  exact GroundBelow.binary_union pairing unions powers separation infinite choice hP
    (M.prod_mem pairing unions powers separation hSingle hN) hK omega ordinal regular strong old
    (GroundBelow.product pairing unions powers separation hSingle hN hK ordinal strong
      (GroundBelow.singleton pairing unions powers separation infinite hK omega hP) fresh)

theorem batchCarrier {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (hP : P ∈ M.sets) (hI : I ∈ M.sets) (hQs : Qs ∈ M.sets)
    (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hK : K ∈ M.sets) (omega : ZFSet.omega ∈ K)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K) (strong : GroundStrongLimit M K)
    (old : GroundBelow M P K) (indices : GroundBelow M I K)
    (templates : ∀ i Q, ZFSet.pair i Q ∈ Qs → GroundBelow M Q K) :
    GroundBelow M d.batchCarrier K :=
  GroundBelow.taggedExtension pairing unions powers separation choice infinite hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
    hK omega ordinal regular strong old
    (GroundBelow.indexedAttachmentFresh pairing unions powers separation choice hI hQs hrs hAs hK
      ordinal regular strong d.spaces indices templates)

end GroundBelow

namespace GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
include pairing unions powers separation infinite choice

theorem currentCarrier_below {P r μ K : ZFSet.{u}}
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ state.data)
    (templates : GroundBelow M P K) (old : GroundBelow M state.data.D K)
    (indices : GroundBelow M state.data.J K) : GroundBelow M state.data.currentCarrier K := by
  apply GroundBelow.batchCarrier pairing unions powers separation choice infinite state.batch
    state.ground.carrier state.ground.indices state.ground.spaces state.ground.relations state.ground.anchors
    hK conditions.2.1 conditions.1 conditions.2.2.1 conditions.2.2.2 old indices
  intro i Q entry
  obtain rfl := ((constant.space_entry_iff i Q).1 entry).2
  exact templates

theorem canonical_iterate_below
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {P r μ K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ state.data)
    (templates : GroundBelow M P K) (old : GroundBelow M state.data.D K)
    (indices : GroundBelow M state.data.J K) (tasks : GroundBelow M I K) (n : Nat) :
    GroundBelow M (state.data.iterate M I Sources Reps G T n).D K ∧
      GroundBelow M (state.data.iterate M I Sources Reps G T n).J K := by
  induction n with
  | zero => exact ⟨old, indices⟩
  | succ n ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid
      pairing unions powers separation hI hSources hReps hG hT n
    have currentOld : GroundBelow M current.data.D K := by rw [equal]; exact ih.1
    have currentIndices : GroundBelow M current.data.J K := by rw [equal]; exact ih.2
    have currentConstant : RecursiveTemplateConstancy P r μ current.data := by
      rw [equal]
      exact constant.iterate M I Sources Reps G T n
    rw [RecursiveStateData.iterate_succ, ← equal]
    change GroundBelow M current.data.currentCarrier K ∧
      GroundBelow M (recursiveAttachmentIndices I current.data.J current.data.D
        current.data.Fs.sUnion.sUnion Sources current.data.Fs) K
    refine ⟨current.currentCarrier_below pairing unions powers separation infinite choice
      hK conditions currentConstant templates currentOld currentIndices, ?_⟩
    have bound := GroundBelow.product pairing unions powers separation hI current.ground.indices hK
      conditions.1 conditions.2.2.2 tasks currentIndices
    exact bound.restrict separation
      (M.recursiveAttachmentIndices_mem pairing unions powers separation hI current.ground.indices
        current.ground.carrier (M.union_mem unions (M.union_mem unions current.ground.filters))
        hSources current.ground.filters) hK (recursiveAttachmentIndices_subset _ _ _ _ _ _)

end GroundCompressionState

open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem history_field_union_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K history U : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (hHistory : history ∈ M.sets) (states : Nat → RecursiveStateData.{u})
    (entries : ∀ n y, ZFSet.pair (natSetCode n) y ∈ history ↔ y = (states n).code)
    (j : Fin 13) (small : ∀ n, GroundBelow M ((states n).field j) K)
    (code : NatUnionCode (fun n => (states n).field j) U) : GroundBelow M U K := by
  have hOmega := M.omega_mem separation infinite
  obtain ⟨family, hFamily, function, actual⟩ := M.exists_groundStateFieldFamily
    pairing separation collection hOmega hHistory states entries j
  have hBound := M.union_mem unions (M.union_mem unions hFamily)
  have sizes : ∀ i A, ZFSet.pair i A ∈ family → GroundBelow M A K := by
    intro i A entry
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode i).1 (function.pair_source entry)
    rw [(actual n A).1 entry]
    exact small n
  have bound := GroundBelow.indexed_sUnion pairing unions powers separation choice hOmega hBound hFamily hK
    conditions.1 conditions.2.2.1 conditions.2.2.2
    (GroundBelow.of_member pairing unions powers separation hK conditions.2.1) function.to_isFunc sizes
  have same : U = (relationImage ZFSet.omega family.sUnion.sUnion family).sUnion := by
    apply ZFSet.ext
    intro x
    rw [code x, ZFSet.mem_sUnion]
    constructor
    · rintro ⟨n, hx⟩
      have entry := (actual n ((states n).field j)).2 rfl
      exact ⟨(states n).field j,
        (mem_relationImage _ _ _ _).2
          ⟨pair_second_mem_doubleUnion entry, natSetCode n, natSetCode_mem_omega n, entry⟩, hx⟩
    · rintro ⟨A, hA, hx⟩
      obtain ⟨_, i, hi, entry⟩ := (mem_relationImage _ _ _ _).1 hA
      obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode i).1 hi
      refine ⟨n, ?_⟩
      change x ∈ (states n).field j
      exact (actual n A).1 entry ▸ hx
  exact same.symm ▸ bound

end TransitiveGround

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem union_below (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {P r μ K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ state.data)
    (templates : GroundBelow M P K) (old : GroundBelow M state.data.D K)
    (indices : GroundBelow M state.data.J K) (tasks : GroundBelow M I K) :
    GroundBelow M (data.fields 0) K := by
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  exact M.history_field_union_below pairing unions powers separation collection infinite choice
    hK conditions hHistory (state.data.iterate M I Sources Reps G T) entries 0
    (fun n => (state.canonical_iterate_below pairing unions powers separation infinite choice
      hI hSources hReps hG hT hK conditions constant templates old indices tasks n).1)
    (data.fieldUnion 0)

end GroundCompressionState

namespace GroundCompressionOrigin
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)

include origin in
theorem union_below (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    {P r μ K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ initial)
    (templates : GroundBelow M P K) (old : GroundBelow M initial.D K)
    (indices : GroundBelow M initial.J K) (tasks : GroundBelow M I K) :
    GroundBelow M (data.fields 0) K := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  exact state.union_below data pairing unions powers separation collection infinite choice
    hI hSources hReps hG hT hK conditions constant templates old indices tasks

end GroundCompressionOrigin

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem initialCompressionUnion_below
    {P G r μ A Labels τ Sources Reps m inv one T Filters K : ZFSet.{u}}
    (origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
      P r μ A τ (M.groundEligibleTasks P G r μ A Labels) Sources Reps G m inv one T Filters)
    (data : GroundCompressionUnionData M (M.initialCompressionData P G r μ A Labels)
      (M.groundEligibleTasks P G r μ A Labels) Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (hSources : Sources ∈ M.sets)
    (hReps : Reps ∈ M.sets) (hT : T ∈ M.sets) (hK : K ∈ M.sets)
    (meet : MeetOrderCode P r μ) (conditions : GroundInaccessibleConditions M K)
    (points : GroundBelow M P K) (labels : GroundBelow M Labels K) :
    GroundBelow M (data.fields 0) K := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have tasks := M.groundEligibleTasks_below pairing unions powers separation
    hP hG hr hμ hA hLabels hK meet conditions.1 conditions.2.2.2 points labels
  exact origin.union_below data pairing unions powers separation collection infinite choice
    hI hSources hReps hG hT hK conditions
    (M.initialCompressionData_template_constancy P G r μ A Labels) points points tasks tasks

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundHistoryUnionBounds
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundInaccessibleConditions
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets)
include conditions pairing unions powers separation hK

theorem product {A B : ZFSet.{u}}
    (first : A ∈ M.sets ∧ GroundBelow M A K) (second : B ∈ M.sets ∧ GroundBelow M B K) :
    ZFSet.prod A B ∈ M.sets ∧ GroundBelow M (ZFSet.prod A B) K :=
  ⟨M.prod_mem pairing unions powers separation first.1 second.1,
    GroundBelow.product pairing unions powers separation first.1 second.1 hK
      conditions.1 conditions.2.2.2 first.2 second.2⟩

include infinite in
theorem singleton {a : ZFSet.{u}} (ha : a ∈ M.sets) :
    ({a} : ZFSet.{u}) ∈ M.sets ∧ GroundBelow M ({a} : ZFSet.{u}) K := by
  refine ⟨?_, GroundBelow.singleton pairing unions powers separation infinite hK conditions.2.1 ha⟩
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ha ha

include infinite in
theorem natural (n : Nat) : natSetCode n ∈ M.sets ∧ GroundBelow M (natSetCode n) K :=
  ⟨M.natSetCode_mem separation infinite n,
    GroundBelow.of_member pairing unions powers separation hK
      (conditions.1.1 ZFSet.omega conditions.2.1 _ (natSetCode_mem_omega n))⟩

include infinite choice in
theorem binary_union {A B : ZFSet.{u}}
    (first : A ∈ M.sets ∧ GroundBelow M A K) (second : B ∈ M.sets ∧ GroundBelow M B K) :
    A ∪ B ∈ M.sets ∧ GroundBelow M (A ∪ B) K :=
  ⟨M.binary_union_mem pairing unions first.1 second.1,
    GroundBelow.binary_union pairing unions powers separation infinite choice first.1 second.1 hK
      conditions.2.1 conditions.1 conditions.2.2.1 conditions.2.2.2 first.2 second.2⟩

end PartitionPilot.Forcing.GroundInaccessibleConditions

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundBelowExternalPoints
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {A K : ZFSet.{u}}

theorem finiteWords
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hA : A ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (omegaBelow : ZFSet.omega ∈ K) (alphabet : GroundBelow M A K) :
    GroundBelow M (M.finiteWords A) K := by
  have natural := GroundBelow.of_member pairing unions powers separation hK omegaBelow
  have relations := GroundBelow.relations pairing unions powers separation
    (M.omega_mem separation infinite) hA hK ordinal strong natural alphabet
  exact relations.restrict separation (M.finiteWords_mem pairing unions powers separation infinite hA)
    hK (fun _ member => (ZFSet.mem_sep.1 member).1)

end GroundBelow

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalGroupCarrier_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {G S m one K : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (omegaBelow : ZFSet.omega ∈ K) (alphabet : GroundBelow M (externalGeneratorAlphabet G S) K) :
    GroundBelow M (M.externalGroupCarrier G S m one) K := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hRelation := M.externalWordEquivalence_mem pairing unions powers separation infinite hG hS hm hOne
  exact GroundBelow.equivalenceClasses pairing unions powers separation hWords hRelation hK strong
    (GroundBelow.finiteWords pairing unions powers separation infinite hAlphabet hK ordinal strong omegaBelow alphabet)

end TransitiveGround
end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
include pairing unions powers separation hK conditions

theorem externalRectangleBound_below {P G : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (smallP : GroundBelow M P K) (smallG : GroundBelow M G K) :
    GroundBelow M (externalRectangleBound P G) K := by
  have product := @GroundInaccessibleConditions.product M K conditions pairing unions powers separation hK
  exact (product ⟨hP, smallP⟩ (product ⟨hP, smallP⟩
    (product ⟨hP, smallP⟩ (product ⟨hG, smallG⟩ ⟨hG, smallG⟩)))).2

theorem externalRectangles_below {P G r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets)
    (hμ : μ ∈ M.sets) (hA : A ∈ M.sets)
    (smallP : GroundBelow M P K) (smallG : GroundBelow M G K) :
    GroundBelow M (externalRectangles P G r μ A) K := by
  exact (M.externalRectangleBound_below pairing unions powers separation hK conditions hP hG smallP smallG).restrict
    separation (M.externalRectangles_mem pairing unions powers separation hP hG hr hμ hA) hK
    (fun _ hz => (ZFSet.mem_sep.1 hz).1)

include infinite choice

theorem externalRequestCarrier_below {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets)
    (smallI : GroundBelow M I K) (smallP : GroundBelow M P K)
    (smallRectangles : GroundBelow M Rectangles K) :
    GroundBelow M (externalRequestCarrier I P Rectangles) K := by
  have product := @GroundInaccessibleConditions.product M K conditions pairing unions powers separation hK
  have join := @GroundInaccessibleConditions.binary_union M K conditions pairing unions powers separation infinite choice hK
  have tag := fun n => conditions.singleton pairing unions powers separation infinite hK
    (M.natSetCode_mem separation infinite n)
  exact (join (join (product (tag 0) ⟨hI, smallI⟩) (product (tag 1) ⟨hP, smallP⟩))
    (product (tag 2) ⟨hRectangles, smallRectangles⟩)).2

theorem externalChildLetters_below {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets)
    (smallI : GroundBelow M I K) (smallP : GroundBelow M P K)
    (smallRectangles : GroundBelow M Rectangles K) :
    GroundBelow M (externalChildLetters I P Rectangles) K := by
  have product := @GroundInaccessibleConditions.product M K conditions pairing unions powers separation hK
  have join := @GroundInaccessibleConditions.binary_union M K conditions pairing unions powers separation infinite choice hK
  have tag := fun n => conditions.singleton pairing unions powers separation infinite hK
    (M.natSetCode_mem separation infinite n)
  have requests := M.externalRequestCarrier_below pairing unions powers separation infinite choice hK conditions
    hI hP hRectangles smallI smallP smallRectangles
  exact (join (product ⟨M.externalRequestCarrier_mem pairing unions powers separation hI hP hRectangles,
      requests⟩ (tag 0)) (product (product (tag 2) ⟨hRectangles, smallRectangles⟩) (tag 1))).2

theorem externalGeneratorAlphabet_below {G S : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets)
    (smallG : GroundBelow M G K) (smallS : GroundBelow M S K) :
    GroundBelow M (externalGeneratorAlphabet G S) K := by
  have product := @GroundInaccessibleConditions.product M K conditions pairing unions powers separation hK
  have join := @GroundInaccessibleConditions.binary_union M K conditions pairing unions powers separation infinite choice hK
  have tag := fun n => conditions.singleton pairing unions powers separation infinite hK
    (M.natSetCode_mem separation infinite n)
  exact (join (product (tag 0) ⟨hG, smallG⟩)
    (product (tag 1) (product ⟨hS, smallS⟩ (conditions.natural pairing unions powers separation infinite hK 2)))).2

theorem externalGroupCarrier_below_of_carriers {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets)
    (smallG : GroundBelow M G K) (smallS : GroundBelow M S K) :
    GroundBelow M (M.externalGroupCarrier G S m one) K :=
  M.externalGroupCarrier_below pairing unions powers separation infinite hG hS hm hOne hK
    conditions.1 conditions.2.2.2 conditions.2.1
    (M.externalGeneratorAlphabet_below pairing unions powers separation infinite choice hK conditions hG hS smallG smallS)

end TransitiveGround

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A K : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hK : K ∈ M.sets)
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "actors" => M.externalGroupCarrier G letters m one
local notation "U" => completion.algebra.union.fields 0
include data pairing unions powers separation infinite hP hG hK

theorem externalPointCarrier_below
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (groupSmall : GroundBelow M actors K) (pointsSmall : GroundBelow M U K) :
    GroundBelow M (completion.externalPointCarrier P r μ A) K := by
  have quotient := data.point_quotient_ground pairing unions powers separation infinite hP hG
  have hProduct := M.prod_mem pairing unions powers separation
    data.group.carrier_mem (completion.algebra.union.ground 0)
  have smallProduct := GroundBelow.product pairing unions powers separation
    data.group.carrier_mem (completion.algebra.union.ground 0) hK ordinal strong groupSmall pointsSmall
  exact GroundBelow.equivalenceClasses pairing unions powers separation
    hProduct quotient.1 hK strong smallProduct

theorem externalBoundedCarrier_below
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (conditions : GroundInaccessibleConditions M K)
    (groupSmall : GroundBelow M actors K) (pointsSmall : GroundBelow M U K) :
    GroundBelow M (completion.externalBoundedCarrier P r μ A) K := by
  have hQ := (data.point_quotient_ground pairing unions powers separation infinite hP hG).2.2.1
  exact GroundBelow.insert pairing unions powers separation infinite choice hQ hQ hK conditions.2.1
    conditions.1 conditions.2.2.1 conditions.2.2.2
    (data.externalPointCarrier_below pairing unions powers separation infinite hP hG hK
      conditions.1 conditions.2.2.2 groupSmall pointsSmall)

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalProfilePreservation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetFormula
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

theorem externalOriginal_filterImage_eq (P r μ A B : ZFSet.{u}) {F : ZFSet.{u}}
    (subset : F ⊆ P) :
    relationImage F B (completion.externalOriginalEmbedding P r μ A) =
      relationImage F B (completion.externalCopyGraph P r μ A
        (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)) := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, entry⟩
    exact ⟨hy, x, hx, ((completion.externalOriginalEmbedding_entry_iff P r μ A x y).1 entry).1⟩
  · rintro ⟨hy, x, hx, entry⟩
    exact ⟨hy, x, hx, (completion.externalOriginalEmbedding_entry_iff P r μ A x y).2 ⟨entry, subset hx⟩⟩

end GroundCompressionCompletion

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P0 ∈ M.sets)
include data group oldAction pairing unions powers separation infinite hG hP
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalBoundedCarrier P0 r0 μ0 A0
local notation "originalGraph" => completion.externalOriginalEmbedding P0 r0 μ0 A0

theorem externalBounded_original_capProfile
    {c e K F c' e' K' : ZFSet.{u}}
    (profile : CodedCapProfile U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) c e K F)
    (subset : F ⊆ P0)
    (imageC : ZFSet.pair c c' ∈ originalGraph)
    (imageE : ZFSet.pair e e' ∈ originalGraph)
    (imageK : ZFSet.pair K K' ∈ originalGraph) :
    CodedCapProfile B (completion.externalBoundedOrder P0 r0 μ0 A0)
      (completion.externalBoundedMeet P0 r0 μ0 A0) c' e' K'
      (relationImage F B originalGraph) := by
  have geometry := data.externalBoundedGeometryData group oldAction
    pairing unions powers separation infinite hG hP
  rw [completion.externalOriginal_filterImage_eq P0 r0 μ0 A0 B subset]
  exact (geometry.copies _ data.group.group_code.identity_mem).capProfile
    completion.algebra.union.meet geometry.meet completion.top_mem completion.top profile
    ((completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 c c').1 imageC).1
    ((completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 e e').1 imageE).1
    ((completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 K K').1 imageK).1

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalRawPriorLayers
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)

local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "E" => completion.externalIdentityCopyGraph P0 r0 μ0 A0

include births in
theorem priorFiber_image {t y : ZFSet.{u}}
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (born : ZFSet.pair y t ∈ births.birth) :
    ∃ x ∈ U, ZFSet.pair x y ∈ E := by
  rcases (pair_mem_ownerBirthGraph _ _ _ _ _ _ _ _).1 born with oldEntry | freshEntry
  · exact (mem_relationImage U B E y).1
      (ZFSet.pair_mem_prod.1 (births.seed_function.1 oldEntry)).1 |>.2
  · obtain ⟨_, _, _, n, hn, _, stamp⟩ := freshEntry
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have later := compressionStamp_old_mem oldTime n
    rw [← (births.times.entries n t).1 stamp] at later
    exact (ZFSet.mem_irrefl t later).elim

end PartitionPilot.Forcing.GroundExternalBirthData

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundCompressionCarrierRankBounds
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

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem exists_rank_limit_above (conditions : GroundInaccessibleConditions M K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) {o : Ordinal.{u}} (bound : o < ZFSet.rank K) :
    ∃ L ∈ K, Order.IsSuccLimit (ZFSet.rank L) ∧ o < ZFSet.rank L := by
  have hBase : ordinalCode o ∈ K := by
    rw [ordinalSetProperty_eq_code_rank K conditions.1]
    exact (mem_ordinalCode_iff o (ZFSet.rank K)).2 bound
  obtain ⟨_, _, L, _, _, _, hL, limit, above⟩ := M.exists_groundCompressionStamps_below
    pairing unions powers separation collection infinite hK conditions hBase
  refine ⟨L, hL, limit, ?_⟩
  simpa only [rank_ordinalCode] using ZFSet.rank_lt_of_mem above

end GroundInaccessibleConditions

namespace GroundCompressionUnionData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (data : GroundCompressionUnionData M initial I Sources Reps G m one T)

theorem carrier_rank_lt_inaccessible
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K P r μ : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (constant : RecursiveTemplateConstancy P r μ initial)
    (points : ZFSet.rank initial.D < ZFSet.rank K) (indices : ZFSet.rank initial.J < ZFSet.rank K)
    (templates : ZFSet.rank P < ZFSet.rank K) (tasks : ZFSet.rank I < ZFSet.rank K) :
    ZFSet.rank (data.fields 0) < ZFSet.rank K := by
  let b := max (ZFSet.rank initial.D) (max (ZFSet.rank initial.J) (max (ZFSet.rank P) (ZFSet.rank I)))
  have bound : b < ZFSet.rank K := max_lt points (max_lt indices (max_lt templates tasks))
  obtain ⟨L, hL, limit, above⟩ := conditions.exists_rank_limit_above
    pairing unions powers separation collection infinite hK bound
  have pointBound : ZFSet.rank initial.D ≤ b := le_max_left _ _
  have indexBound : ZFSet.rank initial.J ≤ b := (le_max_left _ _).trans (le_max_right _ _)
  have templateBound : ZFSet.rank P ≤ b :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have taskBound : ZFSet.rank I ≤ b :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  exact (data.carrier_rank_le constant limit (pointBound.trans_lt above) (indexBound.trans_lt above)
    (templateBound.trans_lt above) (taskBound.trans_lt above)).trans_lt (ZFSet.rank_lt_of_mem hL)

end GroundCompressionUnionData

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem initialCompressionUnion_rank_lt
    {P G r μ A Labels Sources Reps m one T K : ZFSet.{u}}
    (data : GroundCompressionUnionData M (M.initialCompressionData P G r μ A Labels)
      (M.groundEligibleTasks P G r μ A Labels) Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (points : ZFSet.rank P < ZFSet.rank K) (labels : ZFSet.rank Labels < ZFSet.rank K) :
    ZFSet.rank (data.fields 0) < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks := M.groundEligibleTasks_rank_lt limit G r μ A points labels
  exact data.carrier_rank_lt_inaccessible pairing unions powers separation collection infinite hK conditions
    (M.initialCompressionData_template_constancy P G r μ A Labels) points tasks points tasks

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainSuccessorProfilePreservation
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
local notation "completion" => certificate.compression.born.profiled.heighted.completion

theorem target_rank_lt_of_components {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (omega : ZFSet.rank ZFSet.omega < o)
    (indices : ZFSet.rank (source.stage.compressionTasks Labels) < o)
    (points : ZFSet.rank source.stage.carrier < o)
    (actors : ZFSet.rank source.stage.actors < o)
    (completed : ZFSet.rank ((completion).algebra.union.fields 0) < o) :
    ZFSet.rank certificate.target.stage.carrier < o ∧
      ZFSet.rank certificate.target.stage.actors < o := by
  constructor
  · rw [certificate.target_fields.1]
    exact (completion).externalBoundedCarrier_rank_lt limit source.stage.order source.stage.meetGraph
      source.stage.action omega indices points actors completed
  · rw [certificate.target_fields.2.2.2.1]
    exact M.externalRequestGroup_rank_lt limit source.stage.order source.stage.meetGraph
      source.stage.action source.stage.multiplication source.stage.identity omega indices points actors

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (points : ZFSet.rank source.stage.carrier < ZFSet.rank K)
variable (labels : ZFSet.rank Labels < ZFSet.rank K)
include certificate pairing unions powers separation collection infinite hK conditions points labels

theorem compression_union_rank_lt :
    ZFSet.rank ((completion).algebra.union.fields 0) < ZFSet.rank K :=
  M.initialCompressionUnion_rank_lt (completion).algebra.union
    pairing unions powers separation collection infinite hK conditions points labels

theorem target_rank_lt (actors : ZFSet.rank source.stage.actors < ZFSet.rank K) :
    ZFSet.rank certificate.target.stage.carrier < ZFSet.rank K ∧
      ZFSet.rank certificate.target.stage.actors < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have tasks := M.groundEligibleTasks_rank_lt limit source.stage.actors source.stage.order
    source.stage.meetGraph source.stage.action points labels
  exact certificate.target_rank_lt_of_components limit (ZFSet.rank_lt_of_mem conditions.2.1)
    tasks points actors
    (certificate.compression_union_rank_lt pairing unions powers separation collection infinite
      hK conditions points labels)

theorem target_code_rank_lt (actors : ZFSet.rank source.stage.actors < ZFSet.rank K)
    (columns : ZFSet.rank C < ZFSet.rank K) (coordinates : ZFSet.rank D < ZFSet.rank K) :
    ZFSet.rank certificate.target.stage.code < ZFSet.rank K := by
  have target := certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions points labels actors
  exact certificate.target.stage.code_rank_lt
    (conditions.rank_isLimit pairing unions powers separation infinite hK)
    target.1 target.2 columns coordinates

theorem transition_code_rank_lt (actors : ZFSet.rank source.stage.actors < ZFSet.rank K) :
    ZFSet.rank certificate.transition.map.code < ZFSet.rank K := by
  have target := certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions points labels actors
  exact certificate.transition.map.code_rank_lt
    (conditions.rank_isLimit pairing unions powers separation infinite hK)
    points target.1 actors target.2

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (sourceTime : source.cutoff ∈ K)
include certificate pairing unions powers separation infinite hK conditions sourceTime

theorem compression_limit_mem : certificate.compression.born.births.limit ∈ K :=
  conditions.compressionStamp_limit_mem pairing unions powers separation infinite hK
    certificate.compression.born.births.times sourceTime certificate.compression.born.births.stamps_ground

theorem external_limit_mem : certificate.births.limit ∈ K :=
  conditions.compressionStamp_limit_mem pairing unions powers separation infinite hK
    certificate.births.times
    (certificate.compression_limit_mem pairing unions powers separation infinite hK conditions sourceTime)
    certificate.births.stamps_ground

theorem target_cutoff_mem : certificate.target.cutoff ∈ K := by
  rw [certificate.target_cutoff]
  exact certificate.external_limit_mem pairing unions powers separation infinite hK conditions sourceTime

theorem target_time_domain_mem : insert certificate.target.cutoff certificate.target.cutoff ∈ K :=
  conditions.successor_mem pairing unions powers separation infinite hK
    (certificate.target_cutoff_mem pairing unions powers separation infinite hK conditions sourceTime)

theorem target_birth_rank_lt
    (points : ZFSet.rank certificate.target.stage.carrier < ZFSet.rank K) :
    ZFSet.rank certificate.target.birth < ZFSet.rank K :=
  rank_functionGraph_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    certificate.target.birth_function points
    (ZFSet.rank_lt_of_mem
      (certificate.target_time_domain_mem pairing unions powers separation infinite hK conditions sourceTime))

end GroundInitialMainSuccessorData

section
universe u

namespace GroundCompressionBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T base old : ZFSet.{u}}
variable {union : GroundCompressionUnionData M initial I Sources Reps G m one T}

theorem prior_entry (births : GroundCompressionBirthData M initial I Sources Reps G m one T union base old)
    {x t : ZFSet.{u}} (before : t = base ∨ t ∈ base) (entry : ZFSet.pair x t ∈ births.birth) :
    x ∈ initial.D ∧ ZFSet.pair x t ∈ old := by
  rcases (births.extension.entries x t).1 entry with original | ⟨n, _, _, equal⟩
  · exact ⟨(ZFSet.pair_mem_prod.1 (births.initial_function.1 original)).1, original⟩
  · have absurd := compressionStamp_old_mem before.symm n
    rw [← equal] at absurd
    exact (ZFSet.mem_irrefl t absurd).elim

end GroundCompressionBirthData

namespace GroundExternalBirthData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 base old : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (compressionBirths : GroundCompressionBirthData M initial I Sources Reps G m one T
  completion.algebra.union base old)
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 compressionBirths.limit compressionBirths.birth completion)

theorem originalFiber_image (initialDomain : initial.D = P0) {y t : ZFSet.{u}}
    (before : t = base ∨ t ∈ base) (entry : ZFSet.pair y t ∈ births.birth) :
    ∃ x ∈ P0, ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0 := by
  have earlier : t ∈ compressionBirths.limit := before.elim
    (fun equal => equal.symm ▸ compressionBirths.times.base_mem_limit)
    (fun member => compressionBirths.times.ordinal.1 base compressionBirths.times.base_mem_limit t member)
  obtain ⟨x, _, copied⟩ := births.priorFiber_image (Or.inl earlier) entry
  have original := compressionBirths.prior_entry before ((births.preserves_seed x y t copied).1 entry)
  have hx : x ∈ P0 := initialDomain ▸ original.1
  exact ⟨x, hx, (completion.externalOriginalEmbedding_entry_iff P0 r0 μ0 A0 x y).2 ⟨copied, hx⟩⟩

theorem boundedOriginalFiber_image (initialDomain : initial.D = P0) {y t : ZFSet.{u}}
    (before : t = base ∨ t ∈ base) (entry : ZFSet.pair y t ∈ births.boundedBirth) :
    ∃ x ∈ P0, ZFSet.pair x y ∈ completion.externalOriginalEmbedding P0 r0 μ0 A0 := by
  have earlier : t ∈ compressionBirths.limit := before.elim
    (fun equal => equal.symm ▸ compressionBirths.times.base_mem_limit)
    (fun member => compressionBirths.times.ordinal.1 base compressionBirths.times.base_mem_limit t member)
  have final : t ∈ births.limit := births.times.ordinal.1 compressionBirths.limit
    births.times.base_mem_limit t earlier
  exact births.originalFiber_image compressionBirths initialDomain before
    ((fixedTopBirth_earlier_iff final).1 entry)

end GroundExternalBirthData

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem oldBirthFiberCoverage : OldBirthFiberCoverageCode source.stage.carrier
    certificate.transition.map.points certificate.target.birth source.cutoff := by
  intro y t entry before
  rw [certificate.target_birth] at entry
  rw [certificate.point_graph]
  exact certificate.births.boundedOriginalFiber_image certificate.compression.born.births rfl before entry

theorem coversOldBirths : certificate.transition.CoversOldBirths :=
  certificate.oldBirthFiberCoverage

end GroundInitialMainSuccessorData
end

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem capProfile_preserved
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {c e K F c' e' K' : ZFSet.{u}}
    (profile : CodedCapProfile source.stage.carrier source.stage.order source.stage.meetGraph c e K F)
    (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points)
    (imageE : ZFSet.pair e e' ∈ certificate.transition.map.points)
    (imageK : ZFSet.pair K K' ∈ certificate.transition.map.points) :
    CodedCapProfile certificate.target.stage.carrier certificate.target.stage.order
      certificate.target.stage.meetGraph c' e' K'
      (relationImage F certificate.target.stage.carrier certificate.transition.map.points) := by
  have inherited := certificate.origin.union_input_capProfile
    certificate.compression.born.profiled.heighted.completion.algebra.union
    pairing unions powers separation certificate.indices_ground certificate.sources_ground
    certificate.representatives_ground source.stage.actors_ground certificate.task_action_ground profile
  obtain ⟨points, order, meet, _⟩ := certificate.target_fields
  rw [points, order, meet, certificate.point_graph]
  rw [certificate.point_graph] at imageC imageE imageK
  exact certificate.external.inputs.externalBounded_original_capProfile
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground inherited profile.filter_subset imageC imageE imageK

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageInvariant
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
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable {P G r μ A Labels K : ZFSet.{u}}
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets)
variable (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets)
variable (meet : MeetOrderCode P r μ) (conditions : GroundInaccessibleConditions M K)
variable (smallP : GroundBelow M P K) (smallG : GroundBelow M G K) (smallLabels : GroundBelow M Labels K)
include pairing unions powers separation infinite choice hP hG hr hμ hA hLabels hK meet conditions smallP smallG smallLabels

theorem groundInitialExternalLetters_below :
    GroundBelow M (externalChildLetters (M.groundEligibleTasks P G r μ A Labels) P
      (externalRectangles P G r μ A)) K := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have smallI := M.groundEligibleTasks_below pairing unions powers separation
    hP hG hr hμ hA hLabels hK meet conditions.1 conditions.2.2.2 smallP smallLabels
  have hRectangles := M.externalRectangles_mem pairing unions powers separation hP hG hr hμ hA
  have rectangles := M.externalRectangles_below pairing unions powers separation hK conditions
    hP hG hr hμ hA smallP smallG
  exact M.externalChildLetters_below pairing unions powers separation infinite choice hK conditions
    hI hP hRectangles smallI smallP rectangles

theorem groundInitialExternalGroup_below {m one : ZFSet.{u}}
    (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    GroundBelow M (M.externalGroupCarrier G
      (externalChildLetters (M.groundEligibleTasks P G r μ A Labels) P (externalRectangles P G r μ A)) m one) K := by
  have hI := M.groundEligibleTasks_mem pairing unions powers separation hP hG hr hμ hA hLabels meet
  have hRectangles := M.externalRectangles_mem pairing unions powers separation hP hG hr hμ hA
  have hLetters := M.externalChildLetters_mem pairing unions powers separation hI hP hRectangles
  have letters := M.groundInitialExternalLetters_below pairing unions powers separation infinite choice
    hP hG hr hμ hA hLabels hK meet conditions smallP smallG smallLabels
  exact M.externalGroupCarrier_below_of_carriers pairing unions powers separation infinite choice
    hK conditions hG hLetters hm hOne smallG letters

end TransitiveGround

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets)
variable (conditions : GroundInaccessibleConditions M K)
variable (points : GroundBelow M source.stage.carrier K)
variable (labels : GroundBelow M Labels K)
local notation "completion" => certificate.compression.born.profiled.heighted.completion
include certificate pairing unions powers separation collection infinite choice hLabels hK conditions points labels

theorem compression_union_below : GroundBelow M ((completion).algebra.union.fields 0) K := by
  exact M.initialCompressionUnion_below certificate.origin (completion).algebra.union
    pairing unions powers separation collection infinite choice
    source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground source.stage.meet_ground
    source.stage.action_ground hLabels certificate.sources_ground certificate.representatives_ground
    certificate.task_action_ground hK source.stage.meet conditions points labels

theorem target_below (actors : GroundBelow M source.stage.actors K) :
    GroundBelow M certificate.target.stage.carrier K ∧
      GroundBelow M certificate.target.stage.actors K := by
  have groupSmall := M.groundInitialExternalGroup_below pairing unions powers separation infinite choice
    source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground source.stage.meet_ground
    source.stage.action_ground hLabels hK source.stage.meet conditions points actors labels
    source.stage.multiplication_ground source.stage.identity_ground
  have unionSmall := certificate.compression_union_below pairing unions powers separation collection infinite
    choice hLabels hK conditions points labels
  constructor
  · rw [certificate.target_fields.1]
    exact certificate.external.inputs.externalBoundedCarrier_below pairing unions powers separation infinite
      source.stage.carrier_ground source.stage.actors_ground hK choice conditions groupSmall unionSmall
  · rw [certificate.target_fields.2.2.2.1]
    exact groupSmall

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets)
include certificate pairing unions powers separation hK

theorem transition_graphs_below (points : GroundBelow M source.stage.carrier K)
    (actors : GroundBelow M source.stage.actors K) :
    GroundBelow M certificate.transition.map.points K ∧
      GroundBelow M certificate.transition.map.actors K :=
  certificate.transition.map.graphs_below pairing unions powers separation hK points actors

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}

theorem standard_bounds (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (pointSize : GroundBelow M source.stage.carrier K)
    (actorSize : GroundBelow M source.stage.actors K) (labelSize : GroundBelow M Labels K)
    (pointRank : ZFSet.rank source.stage.carrier < ZFSet.rank K)
    (actorRank : ZFSet.rank source.stage.actors < ZFSet.rank K)
    (labelRank : ZFSet.rank Labels < ZFSet.rank K) (sourceTime : source.cutoff ∈ K)
    (columnRank : ZFSet.rank C < ZFSet.rank K) (coordinateRank : ZFSet.rank D < ZFSet.rank K) :
    GroundBelow M certificate.target.stage.carrier K ∧
      GroundBelow M certificate.target.stage.actors K ∧
        ZFSet.rank certificate.target.stage.carrier < ZFSet.rank K ∧
          ZFSet.rank certificate.target.stage.actors < ZFSet.rank K ∧
            ZFSet.rank certificate.target.stage.code < ZFSet.rank K ∧
              certificate.target.cutoff ∈ K ∧
                ZFSet.rank certificate.target.birth < ZFSet.rank K ∧
                  GroundBelow M certificate.transition.map.points K ∧
                    GroundBelow M certificate.transition.map.actors K ∧
                      ZFSet.rank certificate.transition.map.code < ZFSet.rank K := by
  have conditions := standard.to_conditions pairing unions powers separation hK
  have sizes := certificate.target_below pairing unions powers separation collection infinite choice
    hLabels hK conditions pointSize labelSize actorSize
  have ranks := certificate.target_rank_lt pairing unions powers separation collection infinite
    hK conditions pointRank labelRank actorRank
  have maps := certificate.transition_graphs_below pairing unions powers separation hK pointSize actorSize
  exact ⟨sizes.1, sizes.2, ranks.1, ranks.2,
    certificate.target_code_rank_lt pairing unions powers separation collection infinite
      hK conditions pointRank labelRank actorRank columnRank coordinateRank,
    certificate.target_cutoff_mem pairing unions powers separation infinite hK conditions sourceTime,
    certificate.target_birth_rank_lt pairing unions powers separation infinite hK conditions sourceTime ranks.1,
    maps.1, maps.2,
    certificate.transition_code_rank_lt pairing unions powers separation collection infinite
      hK conditions pointRank labelRank actorRank⟩

end GroundInitialMainSuccessorData

open SetFormula SetRealization
universe u

namespace GroundChronologicalMainStage
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

namespace Invariant
variable {source : GroundChronologicalMainStage M C D rD} {K Labels : ZFSet.{u}}
variable (invariant : source.Invariant K Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
include invariant pairing unions powers separation infinite hK conditions

theorem code_rank_lt : ZFSet.rank source.stage.code < ZFSet.rank K :=
  source.stage.code_rank_lt_inaccessible pairing unions powers separation infinite hK conditions
    invariant.points_rank invariant.actors_rank invariant.columns_rank invariant.coordinates_rank

end Invariant

end GroundChronologicalMainStage

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD K Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}

theorem target_invariant (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hLabels : Labels ∈ M.sets) (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (invariant : source.Invariant K Labels) : certificate.target.Invariant K Labels := by
  have bounds := certificate.standard_bounds pairing unions powers separation collection infinite choice
    hLabels hK standard invariant.points_small invariant.actors_small invariant.labels_small
    invariant.points_rank invariant.actors_rank invariant.labels_rank invariant.cutoff_mem
    invariant.columns_rank invariant.coordinates_rank
  exact ⟨bounds.1, bounds.2.1, invariant.labels_small, bounds.2.2.1, bounds.2.2.2.1,
    invariant.labels_rank, bounds.2.2.2.2.2.1, invariant.columns_rank, invariant.coordinates_rank⟩

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedMainInvariantCodes
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

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_linkedMainInvariantFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D P G cutoff serial : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainInvariantFormula K Labels C D P G cutoff serial) env ↔
      LinkedMainInvariantCode M (env K) (env Labels) (env C) (env D)
        (env P) (env G) (env cutoff) (env serial) := by
  change (Realize M.sets (groundBelowFormula P K) env ∧
    Realize M.sets (groundBelowFormula G K) env ∧
    Realize M.sets (groundBelowFormula Labels K) env ∧
    Realize M.sets (cumulativeRankLtFormula P K) env ∧
    Realize M.sets (cumulativeRankLtFormula G K) env ∧
    Realize M.sets (cumulativeRankLtFormula Labels K) env ∧ env cutoff ∈ env K ∧
    Realize M.sets (cumulativeRankLtFormula C K) env ∧
    Realize M.sets (cumulativeRankLtFormula D K) env ∧
    Realize M.sets (cumulativeRankLtFormula serial K) env) ↔ _
  rw [M.realize_groundBelowFormula P K env members,
    M.realize_groundBelowFormula G K env members,
    M.realize_groundBelowFormula Labels K env members,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection P K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection G K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection Labels K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection C K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection D K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection serial K env members ordinal]
  rfl

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundGrowthLayerRecognition
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

namespace TransitiveGround
variable (M : TransitiveGround.{u})

private theorem realize_boundedExBlock {n} (k : Nat) (φ : BoundedFormula (n + k))
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (exBlock k φ.toFormula) env ↔
      ∃ fields : Fin k → ZFSet.{u}, (∀ i, fields i ∈ M.sets) ∧
        BoundedFormula.Truth φ (extendMany k fields env) := by
  rw [realize_exBlock]
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (BoundedFormula.realize_toFormula M φ _
      (extendMany_members k fields env ground members)).1 recognized⟩
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (BoundedFormula.realize_toFormula M φ _
      (extendMany_members k fields env ground members)).2 recognized⟩

theorem realize_countableGrowthWitnessFormula {n} (z L birth t N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (countableGrowthWitnessFormula z L birth t N) env ↔
      ∃ D injection, env z = countableLayerWitness D injection ∧
        CountableLayerCode (env L) (env birth) (env t) D (env N) injection := by
  rw [countableGrowthWitnessFormula, M.realize_boundedExBlock _ _ env members]
  constructor
  · rintro ⟨fields, _, recognized⟩
    have meaning := (BoundedFormula.truth_countableTaggedLayerFormula
      (suffixIndex n 3 z) (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2)
      (suffixIndex n 3 L) (suffixIndex n 3 birth) (suffixIndex n 3 t) (suffixIndex n 3 N)
      (extendMany 3 fields env)).1 recognized
    simp only [extendMany_prefix, extendMany_suffix] at meaning
    exact ⟨fields 1, fields 2, meaning.2⟩
  · rintro ⟨D, injection, equal, code⟩
    let fields : Fin 3 → ZFSet.{u} := Fin.cases (natSetCode 0) (Fin.cases D (fun _ => injection))
    have hWitness : countableLayerWitness D injection ∈ M.sets := equal ▸ members z
    have ground : ∀ i, fields i ∈ M.sets :=
      M.nonemptyTupleCode_field_mem 2 fields hWitness
    refine ⟨fields, ground, ?_⟩
    apply (BoundedFormula.truth_countableTaggedLayerFormula
      (suffixIndex n 3 z) (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2)
      (suffixIndex n 3 L) (suffixIndex n 3 birth) (suffixIndex n 3 t) (suffixIndex n 3 N)
      (extendMany 3 fields env)).2
    simp only [extendMany_prefix, extendMany_suffix]
    exact ⟨rfl, equal, code⟩

theorem realize_copyGrowthWitnessFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (z Qs rs μs L r μ birth t N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (copyGrowthWitnessFormula z Qs rs μs L r μ birth t N) env ↔
      ∃ I parts Indices Maps W injection,
        env z = copyLayerWitness I parts Indices Maps W injection ∧
        CopyLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
          (env t) I parts Indices Maps W (env N) injection := by
  rw [copyGrowthWitnessFormula, M.realize_boundedExBlock _ _ env members]
  constructor
  · rintro ⟨fields, _, recognized⟩
    have meaning := (BoundedFormula.truth_copyTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (suffixIndex n 10 N) (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env)).1 recognized
    simp only [extendMany_prefix, extendMany_suffix] at meaning
    exact ⟨fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
      meaning.2.1, meaning.2.2.2.2.2⟩
  · rintro ⟨I, parts, Indices, Maps, W, injection, equal, code⟩
    let stored : Fin 7 → ZFSet.{u} := Fin.cases (natSetCode 1) (Fin.cases I (Fin.cases parts
      (Fin.cases Indices (Fin.cases Maps (Fin.cases W (fun _ => injection))))))
    have hWitness : nonemptyTupleCode 6 stored ∈ M.sets := by
      change copyLayerWitness I parts Indices Maps W injection ∈ M.sets
      exact equal ▸ members z
    have storedGround := M.nonemptyTupleCode_field_mem 6 stored hWitness
    let fields : Fin 10 → ZFSet.{u} := Fin.cases (natSetCode 1) (Fin.cases I (Fin.cases parts
      (Fin.cases Indices (Fin.cases Maps (Fin.cases W (Fin.cases injection
        (Fin.cases (⋃₀ ⋃₀ env Qs) (Fin.cases (⋃₀ ⋃₀ env rs) (fun _ => ⋃₀ ⋃₀ env μs)))))))))
    have ground : ∀ i, fields i ∈ M.sets :=
      (Fin.cases (storedGround 0) (Fin.cases (storedGround 1) (Fin.cases (storedGround 2) (Fin.cases (storedGround 3) (Fin.cases (storedGround 4) (Fin.cases (storedGround 5) (Fin.cases (storedGround 6) (Fin.cases (M.union_mem unions (M.union_mem unions (members Qs))) (Fin.cases (M.union_mem unions (M.union_mem unions (members rs))) (fun _ => (M.union_mem unions (M.union_mem unions (members μs)))))))))))))
    refine ⟨fields, ground, ?_⟩
    apply (BoundedFormula.truth_copyTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (suffixIndex n 10 N) (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env)).2
    simp only [extendMany_prefix, extendMany_suffix]
    exact ⟨rfl, equal, rfl, rfl, rfl, code⟩

theorem realize_separatedGrowthWitnessFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (z Qs rs μs L r μ birth t : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Realize M.sets (separatedGrowthWitnessFormula z Qs rs μs L r μ birth t) env ↔
      ∃ I Indices Maps W Components F,
        env z = separatedLayerWitness I Indices Maps W Components F ∧
        SeparatedLayerCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ) (env birth)
          (env t) I Indices Maps W Components F := by
  rw [separatedGrowthWitnessFormula, M.realize_boundedExBlock _ _ env members]
  constructor
  · rintro ⟨fields, _, recognized⟩
    have liftedMeet : MeetOrderCode
        (extendMany 10 fields env (suffixIndex n 10 L))
        (extendMany 10 fields env (suffixIndex n 10 r))
        (extendMany 10 fields env (suffixIndex n 10 μ)) := by
      simpa only [extendMany_suffix] using meet
    have meaning := (BoundedFormula.truth_separatedTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env) liftedMeet).1 recognized
    simp only [extendMany_prefix, extendMany_suffix] at meaning
    exact ⟨fields 1, fields 2, fields 3, fields 4, fields 5, fields 6,
      meaning.2.1, meaning.2.2.2.2.2⟩
  · rintro ⟨I, Indices, Maps, W, Components, F, equal, code⟩
    let stored : Fin 7 → ZFSet.{u} := Fin.cases (natSetCode 2) (Fin.cases I (Fin.cases Indices
      (Fin.cases Maps (Fin.cases W (Fin.cases Components (fun _ => F))))))
    have hWitness : nonemptyTupleCode 6 stored ∈ M.sets := by
      change separatedLayerWitness I Indices Maps W Components F ∈ M.sets
      exact equal ▸ members z
    have storedGround := M.nonemptyTupleCode_field_mem 6 stored hWitness
    let fields : Fin 10 → ZFSet.{u} := Fin.cases (natSetCode 2) (Fin.cases I (Fin.cases Indices
      (Fin.cases Maps (Fin.cases W (Fin.cases Components (Fin.cases F
        (Fin.cases (⋃₀ ⋃₀ env Qs) (Fin.cases (⋃₀ ⋃₀ env rs) (fun _ => ⋃₀ ⋃₀ env μs)))))))))
    have ground : ∀ i, fields i ∈ M.sets :=
      (Fin.cases (storedGround 0) (Fin.cases (storedGround 1) (Fin.cases (storedGround 2) (Fin.cases (storedGround 3) (Fin.cases (storedGround 4) (Fin.cases (storedGround 5) (Fin.cases (storedGround 6) (Fin.cases (M.union_mem unions (M.union_mem unions (members Qs))) (Fin.cases (M.union_mem unions (M.union_mem unions (members rs))) (fun _ => (M.union_mem unions (M.union_mem unions (members μs)))))))))))))
    refine ⟨fields, ground, ?_⟩
    have liftedMeet : MeetOrderCode
        (extendMany 10 fields env (suffixIndex n 10 L))
        (extendMany 10 fields env (suffixIndex n 10 r))
        (extendMany 10 fields env (suffixIndex n 10 μ)) := by
      simpa only [extendMany_suffix] using meet
    apply (BoundedFormula.truth_separatedTaggedLayerFormula
      (suffixIndex n 10 z) (prefixIndex n 10 0) (prefixIndex n 10 1) (prefixIndex n 10 2)
      (prefixIndex n 10 3) (prefixIndex n 10 4) (prefixIndex n 10 5) (prefixIndex n 10 6)
      (suffixIndex n 10 Qs) (suffixIndex n 10 rs) (suffixIndex n 10 μs) (suffixIndex n 10 L)
      (suffixIndex n 10 r) (suffixIndex n 10 μ) (suffixIndex n 10 birth) (suffixIndex n 10 t)
      (prefixIndex n 10 7) (prefixIndex n 10 8) (prefixIndex n 10 9)
      (extendMany 10 fields env) liftedMeet).2
    simp only [extendMany_prefix, extendMany_suffix]
    exact ⟨rfl, equal, rfl, rfl, rfl, code⟩

theorem realize_growthLayerWitnessFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (z Qs rs μs L r μ birth t N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (meet : MeetOrderCode (env L) (env r) (env μ)) :
    Realize M.sets (growthLayerWitnessFormula z Qs rs μs L r μ birth t N) env ↔
      GrowthLayerWitnessCode (env Qs) (env rs) (env μs) (env L) (env r) (env μ)
        (env birth) (env t) (env N) (env z) := by
  rw [growthLayerWitnessFormula, realize_disj, realize_disj,
    M.realize_countableGrowthWitnessFormula z L birth t N env members,
    M.realize_copyGrowthWitnessFormula unions z Qs rs μs L r μ birth t N env members,
    M.realize_separatedGrowthWitnessFormula unions z Qs rs μs L r μ birth t env members meet]
  rfl

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SerializedChronologyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

namespace ChronologyCoreCode
theorem meet_of_entries {T V C D rD s L r μ birth : ZFSet.{u}}
    {graphs : Fin 5 → ZFSet.{u}} (core : ChronologyCoreCode T V C D rD graphs)
    (hs : s ∈ T) (eL : ZFSet.pair s L ∈ graphs 0) (er : ZFSet.pair s r ∈ graphs 1)
    (eμ : ZFSet.pair s μ ∈ graphs 2) (eb : ZFSet.pair s birth ∈ graphs 3) :
    MeetOrderCode L r μ := by
  obtain ⟨height, entry, _⟩ := (core.function 4).2 s hs
  exact (core.point s hs L r μ birth height eL er eμ eb entry).meet
end ChronologyCoreCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_SerializedChronologyFormulas
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_chronologyLayerLookupFormula {n} (T : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologyLayerLookupFormula T graphs layers s t L r μ birth z) env ↔
      ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
        (env s) (env t) (env L) (env r) (env μ) (env birth) (env z) := by
  simp only [chronologyLayerLookupFormula, Truth, truth_disj, truth_pairMembershipFormula,
    truth_tripleMembershipFormula, ChronologyLayerLookup]
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_chronologyLayerClause
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (T V C D rD N : Fin n) (graphs : Fin 5 → Fin n)
    (layers s t L r μ birth z : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets)
    (core : ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j))) :
    Realize M.sets (chronologyLayerClause T N graphs layers s t L r μ birth z) env ↔
      (ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
        (env s) (env t) (env L) (env r) (env μ) (env birth) (env z) →
        GrowthLayerWitnessCode (env (graphs 0)) (env (graphs 1)) (env (graphs 2))
          (env L) (env r) (env μ) (env birth) (env t) (env N) (env z)) := by
  rw [chronologyLayerClause, realize_imp]
  have lookup := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_chronologyLayerLookupFormula T graphs layers s t L r μ birth z env)
  have recognized (h : ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
      (env s) (env t) (env L) (env r) (env μ) (env birth) (env z)) :=
    M.realize_growthLayerWitnessFormula unions z (graphs 0) (graphs 1) (graphs 2)
      L r μ birth t N env members
      (core.meet_of_entries h.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1)
  exact ⟨fun h actual => (recognized actual).1 (h (lookup.2 actual)),
    fun h actual => (recognized (lookup.1 actual)).2 (h (lookup.1 actual))⟩

theorem realize_chronologyLayerEntriesFormula
    (unions : Realize M.sets SetFormula.union Fin.elim0) {n}
    (T V C D rD N : Fin n) (graphs : Fin 5 → Fin n) (layers : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (core : ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j))) :
    Realize M.sets (chronologyLayerEntriesFormula T N graphs layers) env ↔
      ChronologyLayerEntries (env T) (env N) (fun j => env (graphs j)) (env layers) := by
  let old := suffixIndex n 7
  let field := prefixIndex n 7
  let body := chronologyLayerClause (old T) (old N) (fun j => old (graphs j))
    (old layers) (field 0) (field 1) (field 2) (field 3) (field 4) (field 5) (field 6)
  have clause (values : Fin 7 → ZFSet.{u}) (ground : ∀ i, values i ∈ M.sets) :
      Realize M.sets body (extendMany 7 values env) ↔
        (ChronologyLayerLookup (env T) (fun j => env (graphs j)) (env layers)
          (values 0) (values 1) (values 2) (values 3) (values 4) (values 5) (values 6) →
          GrowthLayerWitnessCode (env (graphs 0)) (env (graphs 1)) (env (graphs 2))
            (values 2) (values 3) (values 4) (values 5) (values 1) (env N) (values 6)) := by
    have lifted : ChronologyCoreCode ((extendMany 7 values env) (old T))
        ((extendMany 7 values env) (old V)) ((extendMany 7 values env) (old C))
        ((extendMany 7 values env) (old D)) ((extendMany 7 values env) (old rD))
        (fun j => (extendMany 7 values env) (old (graphs j))) := by
      simpa only [old, extendMany_suffix] using core
    simpa only [body, old, field, extendMany_prefix, extendMany_suffix] using
      M.realize_chronologyLayerClause unions (old T) (old V) (old C) (old D) (old rD)
        (old N) (fun j => old (graphs j)) (old layers) (field 0) (field 1) (field 2)
        (field 3) (field 4) (field 5) (field 6) (extendMany 7 values env)
        (extendMany_members 7 values env ground members) lifted
  change Realize M.sets (allBlock 7 body) env ↔ _
  rw [realize_allBlock]
  constructor
  · intro recognized s hs t ht earlier L r μ birth z eL er eμ eb entry
    let values : Fin 7 → ZFSet.{u} := Fin.cases s (Fin.cases t (Fin.cases L
      (Fin.cases r (Fin.cases μ (Fin.cases birth (fun _ => z))))))
    have ground : ∀ i, values i ∈ M.sets :=
      Fin.cases (M.transitive (members T) hs) (Fin.cases (M.transitive (members T) ht)
        (Fin.cases (M.pair_right (M.transitive (members (graphs 0)) eL))
          (Fin.cases (M.pair_right (M.transitive (members (graphs 1)) er))
            (Fin.cases (M.pair_right (M.transitive (members (graphs 2)) eμ))
              (Fin.cases (M.pair_right (M.transitive (members (graphs 3)) eb))
                (fun _ => M.pair_right (M.transitive (members layers) entry)))))))
    exact (clause values ground).1 (recognized values ground) ⟨hs, ht, earlier, eL, er, eμ, eb, entry⟩
  · intro code values ground
    apply (clause values ground).2
    rintro ⟨hs, ht, earlier, eL, er, eμ, eb, entry⟩
    exact code _ hs _ ht earlier _ _ _ _ _ eL er eμ eb entry

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_chronologyLayerFunctionFormula {n} (T W layers : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyLayerFunctionFormula T W layers) env ↔
      ZFSet.IsFunc (chronologyPairs (env T)) (env W) (env layers) := by
  rw [chronologyLayerFunctionFormula, realize_ex]
  constructor
  · rintro ⟨J, hJ, recognized, function⟩
    have equal := (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
      (extend J env) (Fin.cases hJ members)).1 recognized
    have actual := (BoundedFormula.realize_toFormula M _ (extend J env) (Fin.cases hJ members)).1 function
    have code := (BoundedFormula.truth_functionFormula 0 W.succ layers.succ (extend J env)).1 actual
    exact equal ▸ code
  · intro function
    have hJ := M.chronologyPairs_mem pairing unions powers separation (members T)
    exact ⟨chronologyPairs (env T), hJ,
      (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
        (extend (chronologyPairs (env T)) env) (Fin.cases hJ members)).2 rfl,
      (BoundedFormula.realize_toFormula M _ _ (Fin.cases hJ members)).2
        ((BoundedFormula.truth_functionFormula 0 W.succ layers.succ _).2 function)⟩

theorem realize_serializedChronologyFormula {n} (T V C D rD N : Fin n)
    (graphs : Fin 5 → Fin n) (W layers : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (serializedChronologyFormula T V C D rD N graphs W layers) env ↔
      SerializedChronologyCode (env T) (env V) (env C) (env D) (env rD) (env N)
        (fun j => env (graphs j)) (env W) (env layers) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula T).toFormula env ∧
    Realize M.sets (BoundedFormula.chronologyCoreFormula T V C D rD graphs).toFormula env ∧
    Realize M.sets (chronologyLayerFunctionFormula T W layers) env ∧
    Realize M.sets (chronologyLayerEntriesFormula T N graphs layers) env) ↔ _
  rw [BoundedFormula.realize_ordinalFormula M T env members, ← ordinalSetProperty_iff,
    BoundedFormula.realize_chronologyCoreFormula M T V C D rD graphs env members,
    M.realize_chronologyLayerFunctionFormula pairing unions powers separation T W layers env members]
  constructor
  · rintro ⟨ordinal, core, function, entries⟩
    exact ⟨ordinal, core, function,
      (M.realize_chronologyLayerEntriesFormula unions T V C D rD N graphs layers env members core).1 entries⟩
  · intro code
    exact ⟨code.ordinal, code.core, code.function,
      (M.realize_chronologyLayerEntriesFormula unions T V C D rD N graphs layers env members code.core).2 code.entries⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundFiniteSeedBounds
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

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem finite_seed_bounds (conditions : GroundInaccessibleConditions M K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets) (n : Nat) :
    natSetCode n ∈ M.sets ∧ M.groundEmbeddable (natSetCode n) ZFSet.omega ∧
      GroundBelow M (natSetCode n) K ∧ ZFSet.rank (natSetCode n) < ZFSet.rank K := by
  have bounds := conditions.natural pairing unions powers separation infinite hK n
  exact ⟨bounds.1, M.natSetCode_countable pairing unions powers separation infinite n,
    bounds.2, rank_natSetCode_lt
      (conditions.rank_isLimit pairing unions powers separation infinite hK) n⟩

end GroundInaccessibleConditions

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialMainStage
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {injection : ZFSet.{u}} (hInjection : injection ∈ M.sets)
variable (injected : InjectionCode stage.carrier ZFSet.omega injection)

theorem initialSerializedChronology_values {s : ZFSet.{u}}
    (hs : s ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u})) :
    let history := (stage.initialSerializedChronology pairing unions powers separation hInjection injected).toHistory
    history.space s = stage.carrier ∧ history.order s = stage.order ∧
      history.meetGraph s = stage.meetGraph ∧ history.birth s = stage.initialBirth ∧
      history.height s = stage.height :=
  ⟨stage.initialGroundChronologyFields_value pairing unions powers separation 0 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 1 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 2 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 3 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 4 hs⟩

theorem initialSerializedChronology_code_ground :
    (stage.initialSerializedChronology pairing unions powers separation hInjection injected).code ∈ M.sets :=
  (stage.initialSerializedChronology pairing unions powers separation hInjection injected).code_ground pairing

end GroundMainStage

namespace GroundMainStage
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
variable (points : ZFSet.rank stage.carrier < o) (height : ZFSet.rank stage.height < o)
include limit points height

theorem initialChronologyField_rank_lt : ∀ j, ZFSet.rank (stage.initialChronologyField j) < o := by
  have pp := rank_product_lt limit points points
  have order := (ZFSet.rank_mono stage.meet.order.relation).trans_lt pp
  have meet := rank_functionGraph_lt limit stage.meet.operation pp points
  have zero : ZFSet.rank (∅ : ZFSet.{u}) < o := by simpa only [ZFSet.rank_empty] using limit.pos
  have birth := rank_constantFamilyGraph_lt limit points zero
  exact Fin.cases points (Fin.cases order (Fin.cases meet (Fin.cases birth
    (Fin.cases height (fun i => Fin.elim0 i)))))

theorem initialChronologyBound_rank_lt : ZFSet.rank stage.initialChronologyBound < o :=
  rank_finiteRange_lt limit 5 _ (stage.initialChronologyField_rank_lt limit points height)

theorem initialChronologyGraph_rank_lt : ∀ j, ZFSet.rank (stage.initialChronologyGraph j) < o :=
  fun j => rank_constantFamilyGraph_lt limit (rank_natSetCode_lt limit 1)
    (stage.initialChronologyField_rank_lt limit points height j)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {injection : ZFSet.{u}} (hInjection : injection ∈ M.sets)
variable (injected : InjectionCode stage.carrier ZFSet.omega injection)

theorem initialSerializedChronology_code_rank_lt (omega : ZFSet.rank (ZFSet.omega : ZFSet.{u}) < o) :
    ZFSet.rank (stage.initialSerializedChronology pairing unions powers separation hInjection injected).code < o := by
  let serial := stage.initialSerializedChronology pairing unions powers separation hInjection injected
  have time : ZFSet.rank (insert (∅ : ZFSet.{u}) ∅) < o := rank_natSetCode_lt limit 1
  have fieldsCode : ZFSet.rank serial.fields.code < o :=
    rank_nonemptyTupleCode_lt limit 6 _ (Fin.cases time
      (Fin.cases (stage.initialChronologyBound_rank_lt limit points height)
        (stage.initialChronologyGraph_rank_lt limit points height)))
  have injectionRank := rank_functionGraph_lt limit injected.function points omega
  have witness : ZFSet.rank (countableLayerWitness stage.carrier injection) < o :=
    rank_nonemptyTupleCode_lt limit 2 _
      (Fin.cases (rank_natSetCode_lt limit 0) (Fin.cases points (fun _ => injectionRank)))
  have layerBound : ZFSet.rank serial.layerBound < o := rank_singleton_lt limit witness
  have pairs := (ZFSet.rank_mono (chronologyPairs_subset (insert (∅ : ZFSet.{u}) ∅))).trans_lt
    (rank_product_lt limit time time)
  have layers : ZFSet.rank serial.layers < o := rank_constantFamilyGraph_lt limit pairs witness
  exact rank_nonemptyTupleCode_lt limit 2 _ (Fin.cases fieldsCode (Fin.cases layerBound (fun _ => layers)))

omit limit points height in
theorem initialSerializedChronology_code_rank_lt_inaccessible
    (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (points : ZFSet.rank stage.carrier < ZFSet.rank K)
    (height : ZFSet.rank stage.height < ZFSet.rank K) :
    ZFSet.rank (stage.initialSerializedChronology pairing unions powers separation hInjection injected).code <
      ZFSet.rank K :=
  stage.initialSerializedChronology_code_rank_lt
    (conditions.rank_isLimit pairing unions powers separation infinite hK) points height
    pairing unions powers separation hInjection injected (ZFSet.rank_lt_of_mem conditions.2.1)

end GroundMainStage

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialSeedSerializationRanks
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
open scoped ZFSet
universe u

theorem fractionCarrier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (omega : ZFSet.rank ZFSet.omega < o) : ZFSet.rank (fractionCarrier.{u}) < o := by
  have subset : fractionCarrier.{u} ⊆ ZFSet.prod ZFSet.omega ZFSet.omega := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.mem_sep.1 hy).1⟩
  exact (ZFSet.rank_mono subset).trans_lt (rank_product_lt limit omega omega)

theorem rationalCarrier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (c : ZFSet.{u}) (omega : ZFSet.rank ZFSet.omega < o) :
    ZFSet.rank (rationalCarrier c) < o :=
  (ZFSet.rank_mono (rationalCarrier_subset c)).trans_lt (fractionCarrier_rank_lt limit omega)

theorem rationalLtGraph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (c : ZFSet.{u}) (omega : ZFSet.rank ZFSet.omega < o) :
    ZFSet.rank (rationalLtGraph c) < o :=
  (ZFSet.rank_mono (rationalLtGraph_subset c)).trans_lt
    (rank_product_lt limit (rationalCarrier_rank_lt limit c omega)
      (rationalCarrier_rank_lt limit c omega))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rational_seed_pair {c : ZFSet.{u}}
    (carrier : rationalCarrier c ∈ M.sets) (code : InjectionCode fractionCarrier ZFSet.omega c) :
    ∃ d0 ∈ M.sets, ∃ d1 ∈ M.sets,
      d0 ∈ rationalCarrier c ∧ d1 ∈ rationalCarrier c ∧ ZFSet.pair d0 d1 ∈ rationalLtGraph c := by
  obtain ⟨d0, h0⟩ := rationalCarrier_nonempty code
  obtain ⟨d1, h1, gap⟩ := (rational_no_endpoints code d0 h0).2
  exact ⟨d0, M.transitive carrier h0, d1, M.transitive carrier h1, h0, h1, gap⟩

theorem exists_groundRationalSeed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K) :
    ∃ c ∈ M.sets, InjectionCode fractionCarrier ZFSet.omega c ∧
      rationalCarrier c ∈ M.sets ∧ rationalLtGraph c ∈ M.sets ∧
      ∃ f ∈ M.sets, InjectionCode (rationalCarrier c) ZFSet.omega f ∧
        DenseOrderCode (rationalCarrier c) (rationalLtGraph c) ∧
        ZFSet.rank (rationalCarrier c) < ZFSet.rank K ∧
        ZFSet.rank (rationalLtGraph c) < ZFSet.rank K ∧
        (∀ x ∈ rationalCarrier c,
          (∃ y ∈ rationalCarrier c, ZFSet.pair y x ∈ rationalLtGraph c) ∧
          (∃ y ∈ rationalCarrier c, ZFSet.pair x y ∈ rationalLtGraph c)) ∧
        ∃ d0 ∈ M.sets, ∃ d1 ∈ M.sets,
          d0 ∈ rationalCarrier c ∧ d1 ∈ rationalCarrier c ∧ ZFSet.pair d0 d1 ∈ rationalLtGraph c := by
  obtain ⟨c, hc, code⟩ := M.fractionCarrier_countable pairing unions powers separation infinite
  have carrier := M.rationalCarrier_mem pairing unions powers separation infinite hc
  have relation := M.rationalLtGraph_mem pairing unions powers separation infinite hc
  have injection := M.canonicalRepresentativesInjection_mem separation
    (M.fractionCarrier_mem pairing unions powers separation infinite)
    (M.fractionEquivGraph_mem pairing unions powers separation infinite) hc
    (M.omega_mem separation infinite)
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have omega := ZFSet.rank_lt_of_mem conditions.2.1
  exact ⟨c, hc, code, carrier, relation,
    canonicalRepresentativesInjection fractionCarrier fractionEquivGraph c, injection,
    canonicalRepresentativesInjection_code code, rational_denseOrderCode code,
    rationalCarrier_rank_lt limit c omega, rationalLtGraph_rank_lt limit c omega,
    rational_no_endpoints code, M.rational_seed_pair carrier code⟩

end TransitiveGround

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

theorem initialMainChronological_invariant {K C D rD c d0 d1 Labels : ZFSet.{u}}
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) (gap : ZFSet.pair d0 d1 ∈ rD)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (labels : GroundBelow M Labels K) (labelRank : ZFSet.rank Labels < ZFSet.rank K)
    (columnRank : ZFSet.rank C < ZFSet.rank K) (coordinateRank : ZFSet.rank D < ZFSet.rank K) :
    (M.initialMainChronological pairing unions powers separation infinite hC hD hrD hc h0 h1 gap).Invariant K Labels := by
  have points := conditions.finite_seed_bounds pairing unions powers separation infinite hK 2
  have actors := conditions.finite_seed_bounds pairing unions powers separation infinite hK 1
  have zero : (∅ : ZFSet.{u}) ∈ K :=
    conditions.1.1 ZFSet.omega conditions.2.1 _ (natSetCode_mem_omega 0)
  exact ⟨points.2.2.1, actors.2.2.1, labels, points.2.2.2, actors.2.2.2,
    labelRank, zero, columnRank, coordinateRank⟩

theorem exists_groundInitialMainSeed (collection : CollectionSchema M.sets)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K) :
    Nonempty (GroundInitialMainSeedData M K
      (M.groundOmegaOne pairing unions powers separation collection infinite)) := by
  obtain ⟨c, hc, fraction, hD, hrD, f, hf, injection, dense, rankD, _rankR, endpoints,
    lo, _hlo, hi, _hhi, loMem, hiMem, gap⟩ :=
    M.exists_groundRationalSeed pairing unions powers separation infinite hK conditions
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have column : (∅ : ZFSet.{u}) ∈ C := (spec.2.2.1 ∅).2
    ⟨M.empty_mem ⟨C, spec.1⟩, ordinalSetProperty_empty,
      M.empty_groundEmbeddable ZFSet.omega ⟨C, spec.1⟩⟩
  have labelSize := conditions.groundOmegaOne_below pairing unions powers separation collection infinite hK
  have columnRank := ZFSet.rank_lt_of_mem
    (conditions.groundOmegaOne_mem pairing unions powers separation collection infinite hK)
  let source := M.initialMainChronological pairing unions powers separation infinite
    spec.1 hD hrD column loMem hiMem gap
  exact ⟨{
    fractionCode := c
    fraction_ground := hc
    fraction_injection := fraction
    coordinateInjection := f
    injection_ground := hf
    injection_code := injection
    dense := dense
    no_endpoints := endpoints
    lo := lo
    hi := hi
    lo_mem := loMem
    hi_mem := hiMem
    gap := gap
    source := source
    points_eq := rfl
    actors_eq := rfl
    bottom_eq := rfl
    top_eq := rfl
    stage_code := rfl
    cutoff_zero := rfl
    birth_eq := rfl
    invariant := M.initialMainChronological_invariant pairing unions powers separation infinite
      spec.1 hD hrD column loMem hiMem gap hK conditions labelSize columnRank columnRank rankD }⟩

end TransitiveGround

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
open SetFormula SetRealization
open scoped ZFSet
universe u
namespace GroundInitialMainSeedData
variable {M : TransitiveGround.{u}} {K C : ZFSet.{u}}
variable (seed : GroundInitialMainSeedData M K C)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
include infinite hK conditions

theorem initialSerializedChronology_code_rank_lt {injection : ZFSet.{u}}
    (hInjection : injection ∈ M.sets)
    (injected : InjectionCode seed.source.stage.carrier ZFSet.omega injection) :
    ZFSet.rank (seed.source.stage.initialSerializedChronology pairing unions powers separation
      hInjection injected).code < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have height := rank_functionGraph_lt limit seed.source.stage.height_code.function
    seed.invariant.points_rank (rank_product_lt limit seed.invariant.columns_rank seed.invariant.coordinates_rank)
  exact seed.source.stage.initialSerializedChronology_code_rank_lt_inaccessible
    pairing unions powers separation hInjection injected infinite hK conditions seed.invariant.points_rank height

theorem exists_rankedInitialSerialization :
    ∃ injection ∈ M.sets, ∃ injected : InjectionCode seed.source.stage.carrier ZFSet.omega injection,
      ∃ hInjection : injection ∈ M.sets,
        let serial := seed.source.stage.initialSerializedChronology pairing unions powers separation hInjection injected
        serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
          serial.fields.graph = seed.source.stage.initialChronologyGraph ∧
          serial.toHistory.space ∅ = seed.source.stage.carrier ∧
          serial.toHistory.order ∅ = seed.source.stage.order ∧
          serial.toHistory.meetGraph ∅ = seed.source.stage.meetGraph ∧
          serial.toHistory.birth ∅ = seed.source.birth ∧
          serial.toHistory.height ∅ = seed.source.stage.height := by
  have small : M.groundEmbeddable seed.source.stage.carrier ZFSet.omega := by
    rw [seed.points_eq]
    exact M.natSetCode_countable pairing unions powers separation infinite 2
  obtain ⟨injection, hInjection, injected⟩ := small
  have values := seed.source.stage.initialSerializedChronology_values pairing unions powers separation
    hInjection injected (ZFSet.mem_insert _ _)
  have birth : seed.source.stage.initialBirth = seed.source.birth := by
    rw [GroundMainStage.initialBirth, seed.points_eq, seed.birth_eq]
  exact ⟨injection, hInjection, injected, hInjection,
    seed.source.stage.initialSerializedChronology_code_ground pairing unions powers separation hInjection injected,
    seed.initialSerializedChronology_code_rank_lt pairing unions powers separation infinite hK conditions hInjection injected,
    rfl, values.1, values.2.1, values.2.2.1, values.2.2.2.1.trans birth, values.2.2.2.2⟩

end GroundInitialMainSeedData
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainStageCandidates
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_bottomFormula {n} (P r b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (bottomFormula P r b) env ↔
      env b ∈ env P ∧ ∀ x ∈ env P, ZFSet.pair (env b) x ∈ env r := by
  simp only [bottomFormula, Truth, truth_pairMembershipFormula]
  rfl

theorem truth_productEquationFormula {n} (B C D : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productEquationFormula B C D) env ↔ env B = ZFSet.prod (env C) (env D) := by
  simp only [productEquationFormula, Truth, truth_productElementFormula,
    truth_pairMembershipFormula]
  change ((∀ z ∈ env B, z ∈ ZFSet.prod (env C) (env D)) ∧
    ∀ c ∈ env C, ∀ d ∈ env D, ZFSet.pair c d ∈ env B) ↔ _
  constructor
  · rintro ⟨subset, covers⟩
    apply ZFSet.ext
    intro z
    refine ⟨subset z, ?_⟩
    rintro hz
    obtain ⟨c, hc, d, hd, rfl⟩ := ZFSet.mem_prod.1 hz
    exact covers c hc d hd
  · rintro equal
    rw [equal]
    exact ⟨fun _ h => h, fun _ hc _ hd => ZFSet.pair_mem_prod.2 ⟨hc, hd⟩⟩

theorem truth_mainStageLawsFormula {n}
    (P r μ G m inv one A b t height C D rD : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainStageLawsFormula P r μ G m inv one A b t height C D rD) env ↔
      MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) := by
  simp only [mainStageLawsFormula, Truth, truth_meetOrderFormula, truth_groupFormula,
    truth_posetActionFormula, truth_bottomFormula, truth_topFormula, truth_strictLexHeightFormula]
  exact ⟨fun ⟨meet, group, action, ⟨hb, least⟩, ⟨ht, greatest⟩, height⟩ =>
    ⟨meet, group, action, hb, least, ht, greatest, height⟩,
    fun h => ⟨h.meet, h.group, h.action, ⟨h.bottom_mem, h.least⟩,
      ⟨h.top_mem, h.greatest⟩, h.height_code⟩⟩

theorem truth_mainStageWitnessFormula {n}
    (P r μ G m inv one A b t height C D rD B R N f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainStageWitnessFormula P r μ G m inv one A b t height C D rD B R N f) env ↔
      MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) ∧
      env B = ZFSet.prod (env C) (env D) ∧
      env R = relationImage (env P) (env B) (env height) ∧
      InjectionCode (env R) (env N) (env f) := by
  simp only [mainStageWitnessFormula, Truth, truth_mainStageLawsFormula,
    truth_productEquationFormula, truth_imageSetFormula, truth_injectionFormula]

theorem realize_mainStageWitnessFormula (M : TransitiveGround.{u}) {n}
    (P r μ G m inv one A b t height C D rD B R N f : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets
      (mainStageWitnessFormula P r μ G m inv one A b t height C D rD B R N f).toFormula env ↔
      MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) ∧
      env B = ZFSet.prod (env C) (env D) ∧
      env R = relationImage (env P) (env B) (env height) ∧
      InjectionCode (env R) (env N) (env f) :=
  (realize_toFormula M _ env members).trans
    (truth_mainStageWitnessFormula P r μ G m inv one A b t height C D rD B R N f env)

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
  (unions : Realize M.sets SetFormula.union Fin.elim0)
  (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_mainStageValidityFormula {n}
    (P r μ G m inv one A b t height C D rD N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega) :
    Realize M.sets (mainStageValidityFormula P r μ G m inv one A b t height C D rD N) env ↔
      MainStageValidity M (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) := by
  simp only [mainStageValidityFormula, realize_ex]
  constructor
  · rintro ⟨B, hB, R, hR, f, hf, realized⟩
    have code := (BoundedFormula.realize_mainStageWitnessFormula M
      P.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ G.succ.succ.succ
      m.succ.succ.succ inv.succ.succ.succ one.succ.succ.succ A.succ.succ.succ
      b.succ.succ.succ t.succ.succ.succ height.succ.succ.succ C.succ.succ.succ
      D.succ.succ.succ rD.succ.succ.succ 2 1 N.succ.succ.succ 0
      (extend f (extend R (extend B env)))
      (Fin.cases hf (Fin.cases hR (Fin.cases hB members)))).1 realized
    change MainStageLaws (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
      (env A) (env b) (env t) (env height) (env C) (env D) (env rD) ∧
      B = ZFSet.prod (env C) (env D) ∧
      R = relationImage (env P) B (env height) ∧ InjectionCode R (env N) f at code
    obtain ⟨laws, rfl, rfl, injection⟩ := code
    rw [omega] at injection
    exact ⟨laws, f, hf, injection⟩
  · rintro ⟨laws, f, hf, injection⟩
    let B := ZFSet.prod (env C) (env D)
    let R := relationImage (env P) B (env height)
    have hB : B ∈ M.sets := M.prod_mem pairing unions powers separation (members C) (members D)
    have hR : R ∈ M.sets := M.relationImage_mem separation (members P) hB (members height)
    refine ⟨B, hB, R, hR, f, hf, ?_⟩
    apply (BoundedFormula.realize_mainStageWitnessFormula M
      P.succ.succ.succ r.succ.succ.succ μ.succ.succ.succ G.succ.succ.succ
      m.succ.succ.succ inv.succ.succ.succ one.succ.succ.succ A.succ.succ.succ
      b.succ.succ.succ t.succ.succ.succ height.succ.succ.succ C.succ.succ.succ
      D.succ.succ.succ rD.succ.succ.succ 2 1 N.succ.succ.succ 0
      (extend f (extend R (extend B env)))
      (Fin.cases hf (Fin.cases hR (Fin.cases hB members)))).2
    refine ⟨laws, rfl, rfl, ?_⟩
    change InjectionCode R (env N) f
    rw [omega]
    exact injection

theorem realize_validMainStageCodeFormula {n}
    (z P r μ G m inv one A b t height C D rD N : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega) :
    Realize M.sets (validMainStageCodeFormula z P r μ G m inv one A b t height C D rD N) env ↔
      env z = mainStageCode (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) ∧
      MainStageValidity M (env P) (env r) (env μ) (env G) (env m) (env inv) (env one)
        (env A) (env b) (env t) (env height) (env C) (env D) (env rD) :=
  and_congr (BoundedFormula.realize_mainStageFormula M z P r μ G m inv one A b t height env members)
    (M.realize_mainStageValidityFormula pairing unions powers separation
      P r μ G m inv one A b t height C D rD N env members omega)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_CodedMainPrefixSystems
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundChronologicalMainStage M C D rD}
variable (sourceFields : GroundChronologyFields M (insert source.cutoff source.cutoff))
variable (targetFields : GroundChronologyFields M (insert target.cutoff target.cutoff))
variable (sourceAgreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
  sourceFields.value j s = source.history.fieldValue j s)
variable (targetAgreement : ∀ j s, s ∈ insert target.cutoff target.cutoff →
  targetFields.value j s = target.history.fieldValue j s)

include sourceAgreement targetAgreement

theorem field_laws (transition : GroundChronologicalMainTransition source target) :
    ChronologicalTransitionLaws transition.map.points source.cutoff target.cutoff source.birth target.birth
      sourceFields.graph targetFields.graph := by
  refine ⟨transition.cutoff_le, transition.birth, ?_⟩
  apply (sourceFields.graphPrefixCode_iff_values targetFields (fun s before =>
    ⟨ZFSet.mem_insert_iff.2 before, ZFSet.mem_insert_iff.2 (transition.prefix_bound before)⟩)).2
  intro j s before
  rw [sourceAgreement j s (ZFSet.mem_insert_iff.2 before),
    targetAgreement j s (ZFSet.mem_insert_iff.2 (transition.prefix_bound before))]
  have h := transition.history_prefix s before
  exact Fin.cases h.1.symm (Fin.cases h.2.1.symm (Fin.cases h.2.2.1.symm
    (Fin.cases h.2.2.2.1.symm (Fin.cases h.2.2.2.2.symm (fun i => Fin.elim0 i))))) j

end GroundChronologicalMainTransition
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem code_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K) : ZFSet.rank linked.code < ZFSet.rank K :=
  rank_nonemptyTupleCode_lt (conditions.rank_isLimit pairing unions powers separation infinite hK) 2 _
    (Fin.cases (linked.invariant.code_rank_lt pairing unions powers separation infinite hK conditions)
      (Fin.cases (ZFSet.rank_lt_of_mem linked.invariant.cutoff_mem) (fun _ => linked.serial_rank)))

end GroundLinkedMainStage

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem code_ground : run.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 _ (Fin.cases run.indices_ground
    (Fin.cases run.stages_ground (fun _ => run.transitions_ground)))

theorem stageGraph_function : FunctionGraphOn run.indices run.stageGraph :=
  familyCodeGraph_function run.key _ run.key_injective

theorem transitionGraph_function : FunctionGraphOn (chronologyPairs run.indices) run.transitionGraph := by
  have function := familyCodeGraph_function (mainTransitionIndexKey run.key)
    (fun p => (run.diagram.transition p.property).map.code)
    (mainTransitionIndexKey_injective run.key run.key_injective)
  rw [mainTransitionIndex_range run.key run.key_order] at function
  exact function

theorem stageGraph_entry (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (run.key i) z ∈ run.stageGraph ↔ z = (run.linked i).code :=
  pair_mem_familyCodeGraph run.key _ run.key_injective i z

end GroundMainPrefix

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundInitialMainSeedData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K C : ZFSet.{u}}
variable (seed : GroundInitialMainSeedData M K C)

theorem initialSerialization_agreement
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {injection : ZFSet.{u}} (hInjection : injection ∈ M.sets)
    (injected : InjectionCode seed.source.stage.carrier ZFSet.omega injection) :
    let serial := seed.source.stage.initialSerializedChronology pairing unions powers separation hInjection injected
    ∀ j t, t ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u}) →
      serial.fields.value j t = seed.source.history.fieldValue j t := by
  dsimp only
  intro j t ht
  have zero : t = ∅ := by
    simpa only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false] using ht
  subst t
  have values := seed.source.stage.initialSerializedChronology_values pairing unions powers separation
    hInjection injected (ZFSet.mem_insert (∅ : ZFSet.{u}) ∅)
  have carrier := (congrArg seed.source.history.space seed.cutoff_zero).symm.trans seed.source.carrier_eq
  have order := (congrArg seed.source.history.order seed.cutoff_zero).symm.trans seed.source.order_eq
  have meet := (congrArg seed.source.history.meetGraph seed.cutoff_zero).symm.trans seed.source.meet_eq
  have height := (congrArg seed.source.history.height seed.cutoff_zero).symm.trans seed.source.height_eq
  have birth : seed.source.stage.initialBirth = seed.source.history.birth ∅ := by
    have equal : seed.source.stage.initialBirth = seed.source.birth := by
      rw [GroundMainStage.initialBirth, seed.points_eq, seed.birth_eq]
    exact equal.trans (congrArg seed.source.history.birth seed.cutoff_zero)
  exact Fin.cases (values.1.trans carrier.symm)
    (Fin.cases (values.2.1.trans order.symm)
      (Fin.cases (values.2.2.1.trans meet.symm)
        (Fin.cases (values.2.2.2.1.trans birth)
          (Fin.cases (values.2.2.2.2.trans height.symm) (fun i => Fin.elim0 i))))) j

end PartitionPilot.Forcing.GroundInitialMainSeedData



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLinkedMainStageCodeLaws
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

theorem GroundSerializedChronology.code_eq_literal {M : TransitiveGround.{u}}
    {T C D rD : ZFSet.{u}} (serial : GroundSerializedChronology M T C D rD) :
    serial.code = serializedChronologyCode T serial.fields.bound serial.fields.graph
      serial.layerBound serial.layers := rfl

theorem SerializedChronologyCode.toGround_code {M : TransitiveGround.{u}}
    {T V C D rD N W layers : ZFSet.{u}} {graphs : Fin 5 → ZFSet.{u}}
    (code : SerializedChronologyCode T V C D rD N graphs W layers)
    (hT : T ∈ M.sets) (hV : V ∈ M.sets) (hGraphs : ∀ j, graphs j ∈ M.sets)
    (hW : W ∈ M.sets) (hLayers : layers ∈ M.sets) (omega : N = ZFSet.omega) :
    (code.toGround hT hV hGraphs hW hLayers omega).code =
      serializedChronologyCode T V graphs W layers := rfl

namespace BoundedFormula

theorem truth_serializedChronologyTupleFormula {n} (z history T V : Fin n)
    (graphs : Fin 5 → Fin n) (W layers : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (serializedChronologyTupleFormula z history T V graphs W layers) env ↔
      env history = nonemptyTupleCode 6 (Fin.cases (env T) (Fin.cases (env V) (fun j => env (graphs j)))) ∧
        env z = serializedChronologyCode (env T) (env V) (fun j => env (graphs j)) (env W) (env layers) := by
  simp only [serializedChronologyTupleFormula, Truth, truth_nonemptyTupleFormula]
  have map2 {k : Nat} (a : Fin n) (f : Fin k → Fin n) :
      (fun j => env (Fin.cases a f j)) = Fin.cases (env a) (fun j => env (f j)) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  simp only [map2]
  constructor
  · rintro ⟨history, code⟩
    rw [history] at code
    exact ⟨history, code⟩
  · rintro ⟨history, code⟩
    unfold serializedChronologyCode at code
    rw [← history] at code
    exact ⟨history, code⟩

end BoundedFormula

end

section
open SetFormula
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_serializedChronologyCandidateFormula_raw {n} (z C D rD N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (serializedChronologyCandidateFormula z C D rD N) env ↔
      ∃ fields : Fin 10 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
        fields 9 = nonemptyTupleCode 6 (Fin.cases (fields 0) (Fin.cases (fields 1)
          (chronologyCandidateGraphs fields))) ∧
        env z = serializedChronologyCode (fields 0) (fields 1)
          (chronologyCandidateGraphs fields) (fields 7) (fields 8) ∧
        SerializedChronologyCode (fields 0) (fields 1) (env C) (env D) (env rD) (env N)
          (chronologyCandidateGraphs fields) (fields 7) (fields 8) := by
  rw [serializedChronologyCandidateFormula, realize_exBlock]
  let old := suffixIndex n 10
  let field := prefixIndex n 10
  let graphs := chronologyCandidateGraphs field
  have actual (values : Fin 10 → ZFSet.{u}) (ground : ∀ j, values j ∈ M.sets) :
      (Realize M.sets
        (BoundedFormula.serializedChronologyTupleFormula (old z) (field 9) (field 0) (field 1)
          graphs (field 7) (field 8)).toFormula (extendMany 10 values env) ∧
       Realize M.sets
        (serializedChronologyFormula (field 0) (field 1) (old C) (old D) (old rD) (old N)
          graphs (field 7) (field 8)) (extendMany 10 values env)) ↔
      values 9 = nonemptyTupleCode 6 (Fin.cases (values 0) (Fin.cases (values 1)
        (chronologyCandidateGraphs values))) ∧
      env z = serializedChronologyCode (values 0) (values 1)
        (chronologyCandidateGraphs values) (values 7) (values 8) ∧
      SerializedChronologyCode (values 0) (values 1) (env C) (env D) (env rD) (env N)
        (chronologyCandidateGraphs values) (values 7) (values 8) := by
    have mems := extendMany_members 10 values env ground members
    have tuple := (BoundedFormula.realize_toFormula M _ _ mems).trans
      (BoundedFormula.truth_serializedChronologyTupleFormula (old z) (field 9) (field 0)
        (field 1) graphs (field 7) (field 8) (extendMany 10 values env))
    have code := M.realize_serializedChronologyFormula pairing unions powers separation
      (field 0) (field 1) (old C) (old D) (old rD) (old N) graphs (field 7) (field 8)
      (extendMany 10 values env) mems
    have graphMap : (fun j => extendMany 10 values env (graphs j)) = chronologyCandidateGraphs values := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
    rw [tuple, code, graphMap]
    simp only [field, old, extendMany_prefix, extendMany_suffix, and_assoc]
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).1 recognized⟩
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).2 recognized⟩

theorem realize_serializedChronologyCandidateFormula {n} (z C D rD N : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) (omega : env N = ZFSet.omega) :
    Realize M.sets (serializedChronologyCandidateFormula z C D rD N) env ↔
      ∃ T, ∃ serial : GroundSerializedChronology M T (env C) (env D) (env rD), serial.code = env z := by
  rw [M.realize_serializedChronologyCandidateFormula_raw pairing unions powers separation z C D rD N env members]
  constructor
  · rintro ⟨fields, ground, _, equal, code⟩
    have hGraphs : ∀ j, chronologyCandidateGraphs fields j ∈ M.sets :=
      Fin.cases (ground 2) (Fin.cases (ground 3) (Fin.cases (ground 4)
        (Fin.cases (ground 5) (fun _ => ground 6))))
    exact ⟨fields 0, code.toGround (ground 0) (ground 1) hGraphs (ground 7) (ground 8) omega,
      (code.toGround_code (ground 0) (ground 1) hGraphs (ground 7) (ground 8) omega).trans equal.symm⟩
  · rintro ⟨T, serial, equal⟩
    let fields : Fin 10 → ZFSet.{u} := Fin.cases T (Fin.cases serial.fields.bound
      (Fin.cases (serial.fields.graph 0) (Fin.cases (serial.fields.graph 1)
        (Fin.cases (serial.fields.graph 2) (Fin.cases (serial.fields.graph 3)
          (Fin.cases (serial.fields.graph 4) (Fin.cases serial.layerBound
            (Fin.cases serial.layers (fun _ => serial.fields.code)))))))))
    have ground : ∀ j, fields j ∈ M.sets := Fin.cases serial.fields.time_ground
      (Fin.cases serial.fields.bound_ground (Fin.cases (serial.fields.graph_ground 0)
        (Fin.cases (serial.fields.graph_ground 1) (Fin.cases (serial.fields.graph_ground 2)
          (Fin.cases (serial.fields.graph_ground 3) (Fin.cases (serial.fields.graph_ground 4)
            (Fin.cases serial.layer_bound_ground (Fin.cases serial.layers_ground
              (fun _ => serial.fields.code_ground pairing)))))))))
    have graphEq : chronologyCandidateGraphs fields = serial.fields.graph := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun i => Fin.elim0 i))))) j
    refine ⟨fields, ground, ?_, ?_, ?_⟩
    · rw [graphEq]
      rfl
    · rw [graphEq]
      exact equal.symm.trans serial.code_eq_literal
    · rw [graphEq, omega]
      exact serial.raw_code

omit pairing unions powers separation in
theorem mem_serializedChronologyCandidates (B C D rD z : ZFSet.{u}) :
    z ∈ M.serializedChronologyCandidates B C D rD ↔
      z ∈ B ∧ ∃ T, ∃ serial : GroundSerializedChronology M T C D rD, serial.code = z := ZFSet.mem_sep

theorem serializedChronologyCandidates_mem
    (infinite : Realize M.sets infinity Fin.elim0) {B C D rD : ZFSet.{u}}
    (hB : B ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    M.serializedChronologyCandidates B C D rD ∈ M.sets := by
  let params := extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))
  have ground : ∀ i, params i ∈ M.sets := Fin.cases hC (Fin.cases hD (Fin.cases hrD
    (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))
  have selected := M.separation_mem separation (serializedChronologyCandidateFormula 0 1 2 3 4)
    params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (serializedChronologyCandidateFormula 0 1 2 3 4)
      (extend z params)) B = M.serializedChronologyCandidates B C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_serializedChronologyCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_serializedChronologyCandidateFormula pairing unions powers separation
      0 1 2 3 4 (extend z params) (Fin.cases (M.transitive hB hz) ground) rfl
  exact equal ▸ selected

omit pairing unions powers separation in
theorem serializedChronology_code_mem_candidates {B T C D rD : ZFSet.{u}}
    (serial : GroundSerializedChronology M T C D rD) (bound : serial.code ∈ B) :
    serial.code ∈ M.serializedChronologyCandidates B C D rD :=
  (M.mem_serializedChronologyCandidates B C D rD serial.code).2 ⟨bound, T, serial, rfl⟩

end TransitiveGround

namespace BoundedFormula

theorem truth_linkedMainStageTupleFormula {n} (z a t h : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (linkedMainStageTupleFormula z a t h) env ↔
      env z = linkedMainStageCode (env a) (env t) (env h) := by
  rw [linkedMainStageTupleFormula, truth_nonemptyTupleFormula]
  have map : (fun j : Fin 3 => env (Fin.cases a (Fin.cases t (fun _ => h)) j)) =
      Fin.cases (env a) (Fin.cases (env t) (fun _ => env h)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) j
  rw [map]
  rfl

theorem truth_linkedTerminalFormula {n} (t T P r μ h : Fin n) (graphs : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (linkedTerminalFormula t T P r μ h graphs) env ↔
      ordinalSetProperty (env t) ∧ env T = insert (env t) (env t) ∧
      ZFSet.pair (env t) (env P) ∈ env (graphs 0) ∧
      ZFSet.pair (env t) (env r) ∈ env (graphs 1) ∧
      ZFSet.pair (env t) (env μ) ∈ env (graphs 2) ∧
      ZFSet.pair (env t) (env h) ∈ env (graphs 4) := by
  simp only [linkedTerminalFormula, Truth, truth_ordinalFormula, truth_successorFormula,
    truth_pairMembershipFormula, ← ordinalSetProperty_iff]
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_linkedMainStageRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N z : Fin n)
    (f : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainStageRawFormula K Labels C D rD N z f) env ↔
      LinkedMainStageRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N) (env z)
        (fun j => env (f j)) := by
  have outer := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_linkedMainStageTupleFormula z (f 22) (f 11) (f 23) env)
  have stage := M.realize_validMainStageCodeFormula pairing unions powers separation
    (f 22) (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) (f 8) (f 9) (f 10) C D rD N env members omega
  have tuple := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_serializedChronologyTupleFormula (f 23) (f 21) (f 12) (f 13)
      (linkedChronologyGraphs f) (f 19) (f 20) env)
  have serial := M.realize_serializedChronologyFormula pairing unions powers separation
    (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20) env members
  have terminal := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_linkedTerminalFormula (f 11) (f 12) (f 0) (f 1) (f 2) (f 10)
      (linkedChronologyGraphs f) env)
  have invariant := M.realize_linkedMainInvariantFormula pairing unions powers separation collection
    K Labels C D (f 0) (f 3) (f 11) (f 23) env members ordinal
  have map : (fun j => env (linkedChronologyGraphs f j)) = linkedChronologyGraphs (fun j => env (f j)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  change (Realize M.sets (BoundedFormula.linkedMainStageTupleFormula z (f 22) (f 11) (f 23)).toFormula env ∧
    Realize M.sets (validMainStageCodeFormula (f 22) (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6)
      (f 7) (f 8) (f 9) (f 10) C D rD N) env ∧
    Realize M.sets (BoundedFormula.serializedChronologyTupleFormula (f 23) (f 21) (f 12) (f 13)
      (linkedChronologyGraphs f) (f 19) (f 20)).toFormula env ∧
    Realize M.sets (serializedChronologyFormula (f 12) (f 13) C D rD N (linkedChronologyGraphs f) (f 19) (f 20)) env ∧
    Realize M.sets (BoundedFormula.linkedTerminalFormula (f 11) (f 12) (f 0) (f 1) (f 2) (f 10)
      (linkedChronologyGraphs f)).toFormula env ∧
    Realize M.sets (linkedMainInvariantFormula K Labels C D (f 0) (f 3) (f 11) (f 23)) env) ↔ _
  rw [outer, stage, tuple, serial, terminal, invariant, map]
  simp only [LinkedMainStageRawCode, and_assoc]
  rfl

end TransitiveGround

end

section
open SetFormula
universe u

namespace LinkedMainStageRawCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N z : ZFSet.{u}} {f : Fin 24 → ZFSet.{u}}

theorem exists_linked
    (raw : LinkedMainStageRawCode M K Labels C D rD N z f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : ∀ j, f j ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (omega : N = ZFSet.omega) :
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z := by
  obtain ⟨outer, stageEq, valid, _, serialEq, code, ordinal, domain, eP, er, eμ, eh, inv⟩ := raw
  let stage := GroundMainStage.ofValidity pairing unions powers separation
    (ground 0) (ground 1) (ground 2) (ground 3) (ground 4) (ground 5) (ground 7) (ground 10) hC hD hrD valid
  have code' : SerializedChronologyCode (insert (f 11) (f 11)) (f 13) C D rD N
      (linkedChronologyGraphs f) (f 19) (f 20) := domain ▸ code
  have graphsGround : ∀ j, linkedChronologyGraphs f j ∈ M.sets :=
    Fin.cases (ground 14) (Fin.cases (ground 15) (Fin.cases (ground 16)
      (Fin.cases (ground 17) (fun _ => ground 18))))
  let serial := code'.toGround (domain ▸ ground 12) (ground 13) graphsGround (ground 19) (ground 20) omega
  let main : GroundChronologicalMainStage M C D rD :=
    { stage := stage
      cutoff := f 11
      cutoff_ground := ground 11
      cutoff_ordinal := ordinal
      history := serial.toHistory
      carrier_eq := serial.fields.value_eq_of_entry 0 eP
      order_eq := serial.fields.value_eq_of_entry 1 er
      meet_eq := serial.fields.value_eq_of_entry 2 eμ
      height_eq := serial.fields.value_eq_of_entry 4 eh }
  have serialCode : serial.code = f 23 := by
    change serializedChronologyCode (insert (f 11) (f 11)) (f 13) (linkedChronologyGraphs f) (f 19) (f 20) = f 23
    rw [← domain]
    exact serialEq.symm
  obtain ⟨ps, gs, ls, pr, gr, lr, tm, cr, dr, sr⟩ := inv
  let linked : GroundLinkedMainStage M K Labels C D rD :=
    { main := main
      serial := serial
      agreement := fun j _ _ => Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j
      invariant := ⟨ps, gs, ls, pr, gr, lr, tm, cr, dr⟩
      serial_rank := serialCode ▸ sr }
  refine ⟨linked, ?_⟩
  change linkedMainStageCode stage.code (f 11) serial.code = z
  have scode : stage.code = f 22 := stageEq.symm
  rw [scode, serialCode]
  exact outer.symm

end LinkedMainStageRawCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem rawFields_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    ∀ j, linked.rawFields j ∈ M.sets :=
  (Fin.cases (linked.main.stage.carrier_ground) (Fin.cases (linked.main.stage.order_ground) (Fin.cases (linked.main.stage.meet_ground) (Fin.cases (linked.main.stage.actors_ground) (Fin.cases (linked.main.stage.multiplication_ground) (Fin.cases (linked.main.stage.inverse_ground) (Fin.cases (linked.main.stage.identity_ground) (Fin.cases (linked.main.stage.action_ground) (Fin.cases (linked.main.stage.bottom_ground) (Fin.cases (linked.main.stage.top_ground) (Fin.cases (linked.main.stage.height_ground) (Fin.cases (linked.main.cutoff_ground) (Fin.cases (linked.serial.fields.time_ground) (Fin.cases (linked.serial.fields.bound_ground) (Fin.cases (linked.serial.fields.graph_ground 0) (Fin.cases (linked.serial.fields.graph_ground 1) (Fin.cases (linked.serial.fields.graph_ground 2) (Fin.cases (linked.serial.fields.graph_ground 3) (Fin.cases (linked.serial.fields.graph_ground 4) (Fin.cases (linked.serial.layer_bound_ground) (Fin.cases (linked.serial.layers_ground) (Fin.cases (linked.serial.fields.code_ground pairing) (Fin.cases (linked.main.stage.code_mem pairing) (fun _ => linked.serial.code_ground pairing))))))))))))))))))))))))

end GroundLinkedMainStage

namespace LinkedMainStageRawCode
variable {M : TransitiveGround.{u}} {K Labels C D rD N z : ZFSet.{u}}
variable {f g : Fin 24 → ZFSet.{u}}

theorem exists_linked_fields
    (raw : LinkedMainStageRawCode M K Labels C D rD N z f)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (ground : ∀ j, f j ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (omega : N = ZFSet.omega) :
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z ∧ linked.rawFields = f := by
  obtain ⟨linked, equal⟩ := raw.exists_linked pairing unions powers separation ground hC hD hrD omega
  refine ⟨linked, equal, ?_⟩
  rw [omega] at raw
  have actual := linked.rawFields_code
  rw [equal] at actual
  exact actual.fields_unique raw

end LinkedMainStageRawCode
end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedMainTransitionRawCodes
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

theorem truth_chronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (chronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs) env ↔
      env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ) (env heightP) (env heightQ) (env points) (env actors) ∧
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j)) := by
  change (Truth (validMainTransitionCodeFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors) env ∧
    Truth (chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff sourceBirth targetBirth
      sourceGraphs targetGraphs) env) ↔ _
  rw [truth_validMainTransitionCodeFormula]
  constructor
  · rintro ⟨⟨encoded, laws⟩, chronological⟩
    exact ⟨encoded, laws, (truth_chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs env laws.point_embedding.injection.function.1).1 chronological⟩
  · rintro ⟨encoded, laws, chronological⟩
    exact ⟨⟨encoded, laws⟩, (truth_chronologicalTransitionExtraFormula P Q points sourceCutoff targetCutoff
      sourceBirth targetBirth sourceGraphs targetGraphs env laws.point_embedding.injection.function.1).2 chronological⟩

theorem truth_coveredChronologicalMainTransitionFormula {n}
    (z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth : Fin n)
    (sourceGraphs targetGraphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (coveredChronologicalMainTransitionFormula z P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors sourceCutoff targetCutoff sourceBirth targetBirth sourceGraphs targetGraphs) env ↔
      (env z = ZFSet.pair (env points) (env actors) ∧
      MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H) (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ) (env heightP) (env heightQ) (env points) (env actors) ∧
      ChronologicalTransitionLaws (env points) (env sourceCutoff) (env targetCutoff)
        (env sourceBirth) (env targetBirth) (fun j => env (sourceGraphs j))
          (fun j => env (targetGraphs j))) ∧
      OldBirthFiberCoverageCode (env P) (env points) (env targetBirth) (env sourceCutoff) := by
  simp only [coveredChronologicalMainTransitionFormula, Truth,
    truth_chronologicalMainTransitionFormula, truth_oldBirthFiberCoverageFormula]

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

theorem truth_linkedTransitionLawsFormula {n} (z points actors sourceBirth targetBirth : Fin n)
    (f g : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (linkedTransitionLawsFormula z points actors sourceBirth targetBirth f g) env ↔
      LinkedTransitionLawsCode (env z) (env points) (env actors) (env sourceBirth) (env targetBirth)
        (fun j => env (f j)) (fun j => env (g j)) := by
  have map (h : Fin 24 → Fin n) : (fun j => env (linkedChronologyGraphs h j)) =
      linkedChronologyGraphs (fun j => env (h j)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl)))) j
  simp only [linkedTransitionLawsFormula, Truth, truth_pairMembershipFormula,
    truth_coveredChronologicalMainTransitionFormula, map, LinkedTransitionLawsCode]

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_linkedMainTransitionRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : Fin n)
    (source target : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainTransitionRawFormula K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth source target) env ↔
      LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
        (env sourceCode) (env targetCode) (env z) (env points) (env actors) (env sourceBirth) (env targetBirth)
          (fun j => env (source j)) (fun j => env (target j)) := by
  have first := M.realize_linkedMainStageRawFormula pairing unions powers separation collection
    K Labels C D rD N sourceCode source env members omega ordinal
  have second := M.realize_linkedMainStageRawFormula pairing unions powers separation collection
    K Labels C D rD N targetCode target env members omega ordinal
  have laws := (BoundedFormula.realize_toFormula M _ env members).trans
    (BoundedFormula.truth_linkedTransitionLawsFormula z points actors sourceBirth targetBirth source target env)
  exact and_congr first (and_congr second laws)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_TaskCapFamilyCodes
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

theorem truth_codedInsertionProfileFormula {n} (L r μ c E K F : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedInsertionProfileFormula L r μ c E K F) env ↔
      CodedInsertionProfile (env L) (env r) (env μ) (env c) (env E) (env K) (env F) := by
  simp only [codedInsertionProfileFormula, Truth, truth_imp, truth_exMem,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

theorem truth_codedCapProfileFormula {n} (L r μ c E K F : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedCapProfileFormula L r μ c E K F) env ↔
      CodedCapProfile (env L) (env r) (env μ) (env c) (env E) (env K) (env F) := by
  simp only [codedCapProfileFormula, Truth, truth_subsetFormula, truth_exMem,
    truth_codedInsertionProfileFormula, truth_pairMembershipFormula, and_true]
  constructor
  · rintro ⟨hc, hE, hK, subset, nonempty, profile, lower, strict, separated⟩
    exact ⟨hc, hE, hK, subset, nonempty, profile, lower, strict, separated⟩
  · intro code
    exact ⟨code.target_mem, code.separator_mem, code.cap_mem, code.filter_subset,
      code.nonempty, code.profile, code.target_below_cap, code.cap_not_below_target,
      code.separator_not_below_cap⟩

theorem truth_imageProfilePositiveFormula {n} (F Q e R x : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (imageProfilePositiveFormula F Q e R x) env ↔
      ∃ f ∈ relationImage (env F) (env Q) (env e), ZFSet.pair f (env x) ∈ env R := by
  simp only [imageProfilePositiveFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  constructor
  · rintro ⟨y, hy, ⟨f, hf, entry⟩, lower⟩
    exact ⟨y, (mem_relationImage _ _ _ _).2 ⟨hy, f, hf, entry⟩, lower⟩
  · rintro ⟨y, hy, lower⟩
    obtain ⟨hy, f, hf, entry⟩ := (mem_relationImage _ _ _ _).1 hy
    exact ⟨y, hy, ⟨f, hf, entry⟩, lower⟩

theorem truth_imageInsertionProfileFormula {n} (Q R ν c E K F e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (imageInsertionProfileFormula Q R ν c E K F e) env ↔
      CodedInsertionProfile (env Q) (env R) (env ν) (env c) (env E) (env K)
        (relationImage (env F) (env Q) (env e)) := by
  simp only [imageInsertionProfileFormula, Truth, truth_imp, truth_imageProfilePositiveFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

theorem truth_imageCapProfileFormula {n} (Q R ν c E K F e : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (imageCapProfileFormula Q R ν c E K F e) env ↔
      CodedCapProfile (env Q) (env R) (env ν) (env c) (env E) (env K)
        (relationImage (env F) (env Q) (env e)) := by
  simp only [imageCapProfileFormula, Truth, truth_exMem, truth_pairMembershipFormula,
    truth_imageInsertionProfileFormula]
  constructor
  · rintro ⟨hc, hE, hK, ⟨y, hy, f, hf, entry⟩, profile, lower, strict, separated⟩
    exact ⟨hc, hE, hK, fun _ h => ((mem_relationImage _ _ _ _).1 h).1,
      ⟨y, (mem_relationImage _ _ _ _).2 ⟨hy, f, hf, entry⟩⟩,
      profile, lower, strict, separated⟩
  · intro code
    obtain ⟨y, hy⟩ := code.nonempty
    obtain ⟨hy, f, hf, entry⟩ := (mem_relationImage _ _ _ _).1 hy
    exact ⟨code.target_mem, code.separator_mem, code.cap_mem, ⟨y, hy, f, hf, entry⟩,
      code.profile, code.target_below_cap, code.cap_not_below_target,
      code.separator_not_below_cap⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing
universe u

namespace BoundedFormula
open SetFormula

theorem truth_oldProfilePreservationFormula {n} (P r μ Q R ν e Filters : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (oldProfilePreservationFormula P r μ Q R ν e Filters) env ↔
      OldProfilePreservationCode (env P) (env r) (env μ) (env Q) (env R) (env ν)
        (env e) (env Filters) := by
  simp only [oldProfilePreservationFormula, Truth, truth_imp, truth_codedCapProfileFormula,
    truth_imageCapProfileFormula, truth_pairMembershipFormula]
  rfl

theorem realize_oldProfilePreservationFormula (M : TransitiveGround.{u}) {n}
    (P r μ Q R ν e Filters : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (oldProfilePreservationFormula P r μ Q R ν e Filters).toFormula env ↔
      OldProfilePreservationCode (env P) (env r) (env μ) (env Q) (env R) (env ν)
        (env e) (env Filters) :=
  (realize_toFormula M _ env members).trans
    (truth_oldProfilePreservationFormula P r μ Q R ν e Filters env)

end BoundedFormula

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_OldProfilePreservationComposition
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

theorem relationImage_identity_on {P F : ZFSet.{u}} (subset : F ⊆ P) :
    relationImage F P (identityFunctionGraph P) = F := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage]
  constructor
  · rintro ⟨_, x, hx, entry⟩
    exact ((pair_mem_identityFunctionGraph P x y).1 entry).1 ▸ hx
  · intro hy
    exact ⟨subset hy, y, hy, (pair_mem_identityFunctionGraph P y y).2 ⟨rfl, subset hy⟩⟩

namespace OldProfilePreservationCode

theorem identity (P r μ Filters : ZFSet.{u}) :
    OldProfilePreservationCode P r μ P r μ (identityFunctionGraph P) Filters := by
  intro F _ c _ E _ K _ profile c' _ E' _ K' _ first second third
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph P c c').1 first
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph P E E').1 second
  obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph P K K').1 third
  rw [relationImage_identity_on profile.filter_subset]
  exact profile

end OldProfilePreservationCode

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundInitialSeedMatchedSerialization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInitialMainSeedData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K C : ZFSet.{u}}
variable (seed : GroundInitialMainSeedData M K C)

theorem exists_matchedInitialSerialization
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K) :
    ∃ serial : GroundSerializedChronology M (insert seed.source.cutoff seed.source.cutoff)
        C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
        ∀ j t, t ∈ insert seed.source.cutoff seed.source.cutoff →
          serial.fields.value j t = seed.source.history.fieldValue j t := by
  obtain ⟨injection, _, injected, hInjection, ground, rank, _⟩ :=
    seed.exists_rankedInitialSerialization pairing unions powers separation infinite hK conditions
  let original := seed.source.stage.initialSerializedChronology pairing unions powers separation hInjection injected
  have timeEq : (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u}) = insert seed.source.cutoff seed.source.cutoff :=
    congrArg (fun t => insert t t) seed.cutoff_zero.symm
  let serial := original.castTime timeEq
  refine ⟨serial, ?_, ?_, ?_⟩
  · exact (original.castTime_code timeEq).symm ▸ ground
  · exact (congrArg ZFSet.rank (original.castTime_code timeEq)).symm ▸ rank
  · intro j t ht
    have zeroDomain : t ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u}) := timeEq.symm ▸ ht
    exact (original.castTime_value timeEq j t).trans
      (seed.initialSerialization_agreement pairing unions powers separation hInjection injected j t zeroDomain)

end PartitionPilot.Forcing.GroundInitialMainSeedData

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixFieldFamilies
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
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

theorem transitionGraph_rank_le_code : ZFSet.rank run.transitionGraph ≤ ZFSet.rank run.code := by
  simpa only [code, Fin.cases_zero, Fin.cases_succ] using
    (rank_nonemptyTupleCode_field_le 2
      (Fin.cases run.indices (Fin.cases run.stageGraph (fun _ => run.transitionGraph))) (0 : Fin 1).succ.succ)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixConePreservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable {S : ZFSet.{u}} (subset : S ⊆ run.indices)
include subset

theorem restrict_indices (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S) :
    (run.restrict subset ground ordinal).indices = S := run.restrictedKey_range subset

theorem restrict_stageGraph (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S) :
    (run.restrict subset ground ordinal).stageGraph = graphRestriction S run.stageGraph :=
  run.restrictedStageGraph_eq subset

theorem restrict_transitionGraph (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S) :
    (run.restrict subset ground ordinal).transitionGraph =
      graphRestriction (chronologyPairs S) run.transitionGraph := run.restrictedTransitionGraph_eq subset

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem restrict_code_rank_lt {S : ZFSet.{u}} (subset : S ⊆ run.indices)
    (ground : S ∈ M.sets) (ordinal : ordinalSetProperty S)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (oldRank : ZFSet.rank run.code < o) :
    ZFSet.rank (run.restrict subset ground ordinal).code < o := by
  have indices : ZFSet.rank (run.restrict subset ground ordinal).indices < o := by
    rw [run.restrict_indices subset ground ordinal]
    exact (ZFSet.rank_mono subset).trans_lt (run.indices_rank_le_code.trans_lt oldRank)
  have stages : ZFSet.rank (run.restrict subset ground ordinal).stageGraph < o := by
    rw [run.restrict_stageGraph subset ground ordinal]
    exact (ZFSet.rank_mono (graphRestriction_subset S run.stageGraph)).trans_lt
      (run.stageGraph_rank_le_code.trans_lt oldRank)
  have transitions : ZFSet.rank (run.restrict subset ground ordinal).transitionGraph < o := by
    rw [run.restrict_transitionGraph subset ground ordinal]
    exact (ZFSet.rank_mono (graphRestriction_subset (chronologyPairs S) run.transitionGraph)).trans_lt
      (run.transitionGraph_rank_le_code.trans_lt oldRank)
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases indices (Fin.cases stages (fun _ => transitions)))

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLinkedTransitionRetarget
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

namespace LinkedMainTransitionRawCode
variable {M : TransitiveGround.{u}}
variable {K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : ZFSet.{u}}
variable {source target : Fin 24 → ZFSet.{u}}

theorem exists_transition
    (raw : LinkedMainTransitionRawCode M K Labels C D rD N sourceCode targetCode z points actors
      sourceBirth targetBirth source target)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (sourceGround : ∀ j, source j ∈ M.sets) (targetGround : ∀ j, target j ∈ M.sets)
    (hPoints : points ∈ M.sets) (hActors : actors ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (omega : N = ZFSet.omega) :
    LinkedMainTransitionCode M K Labels C D rD sourceCode targetCode z := by
  obtain ⟨s, hs, sf⟩ := raw.1.exists_linked_fields pairing unions powers separation sourceGround hC hD hrD omega
  obtain ⟨t, ht, tf⟩ := raw.2.1.exists_linked_fields pairing unions powers separation targetGround hC hD hrD omega
  obtain ⟨sb, tb, ⟨encoded, ordinary, chronological⟩, coverage⟩ := raw.2.2
  rw [← sf] at sb coverage
  rw [← tf] at tb
  rw [← sf, ← tf] at ordinary chronological
  change ZFSet.pair s.main.cutoff sourceBirth ∈ s.serial.fields.graph 3 at sb
  change ZFSet.pair t.main.cutoff targetBirth ∈ t.serial.fields.graph 3 at tb
  have sourceEq : sourceBirth = s.main.birth :=
    (s.serial.fields.value_eq_of_entry 3 sb).symm.trans s.terminal_values.2.2.2.1
  have targetEq : targetBirth = t.main.birth :=
    (t.serial.fields.value_eq_of_entry 3 tb).symm.trans t.terminal_values.2.2.2.1
  rw [s.rawFields_graphs, t.rawFields_graphs, sourceEq, targetEq] at chronological
  rw [targetEq] at coverage
  let map : GroundMainTransition s.main.stage t.main.stage :=
    GroundMainTransition.ofLaws hPoints hActors ordinary
  let transition := GroundChronologicalMainTransition.ofFieldLaws s.serial.fields t.serial.fields
    s.agreement t.agreement map chronological
  exact ⟨s, t, hs, ht, transition, encoded.symm, coverage⟩

end LinkedMainTransitionRawCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (source target : GroundLinkedMainStage M K Labels C D rD)

theorem transition_rawFields
    (transition : GroundChronologicalMainTransition source.main target.main)
    (coverage : transition.CoversOldBirths) :
    LinkedMainTransitionRawCode M K Labels C D rD ZFSet.omega source.code target.code
      transition.map.code transition.map.points transition.map.actors source.main.birth target.main.birth
      source.rawFields target.rawFields := by
  refine ⟨source.rawFields_code, target.rawFields_code, ?_, ?_, ⟨rfl, transition.map.laws, ?_⟩, coverage⟩
  · change ZFSet.pair source.main.cutoff source.main.birth ∈ source.serial.fields.graph 3
    rw [← source.terminal_values.2.2.2.1]
    exact source.serial.fields.value_entry 3 (ZFSet.mem_insert _ _)
  · change ZFSet.pair target.main.cutoff target.main.birth ∈ target.serial.fields.graph 3
    rw [← target.terminal_values.2.2.2.1]
    exact target.serial.fields.value_entry 3 (ZFSet.mem_insert _ _)
  · rw [source.rawFields_graphs, target.rawFields_graphs]
    exact transition.field_laws source.serial.fields target.serial.fields source.agreement target.agreement

end GroundLinkedMainStage

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_linkedMainTransitionFormula_raw {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      ∃ fields : Fin 52 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
        LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
          (env sourceCode) (env targetCode) (env z) (fields 48) (fields 49) (fields 50) (fields 51)
          (fun j => fields (j.castAdd 28)) (fun j => fields (Fin.natAdd 24 (j.castAdd 4))) := by
  rw [linkedMainTransitionFormula, realize_exBlock]
  have actual (fields : Fin 52 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    M.realize_linkedMainTransitionRawFormula pairing unions powers separation collection
      (suffixIndex n 52 K) (suffixIndex n 52 Labels) (suffixIndex n 52 C) (suffixIndex n 52 D)
      (suffixIndex n 52 rD) (suffixIndex n 52 N) (suffixIndex n 52 sourceCode)
      (suffixIndex n 52 targetCode) (suffixIndex n 52 z)
      (prefixIndex n 52 48) (prefixIndex n 52 49) (prefixIndex n 52 50) (prefixIndex n 52 51)
      (fun j => prefixIndex n 52 (j.castAdd 28)) (fun j => prefixIndex n 52 (Fin.natAdd 24 (j.castAdd 4)))
      (extendMany 52 fields env) (extendMany_members 52 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).1 recognized⟩
  · rintro ⟨fields, ground, raw⟩
    exact ⟨fields, ground, (actual fields ground).2 raw⟩

theorem realize_linkedMainTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      LinkedMainTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
        (env sourceCode) (env targetCode) (env z) := by
  rw [M.realize_linkedMainTransitionFormula_raw pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z env members omega ordinal]
  constructor
  · rintro ⟨fields, ground, raw⟩
    exact raw.exists_transition pairing unions powers separation
      (fun j => ground (j.castAdd 28)) (fun j => ground (Fin.natAdd 24 (j.castAdd 4)))
      (ground 48) (ground 49) (members C) (members D) (members rD) omega
  · rintro ⟨source, target, sourceEq, targetEq, transition, codeEq, coverage⟩
    let extra : Fin 4 → ZFSet.{u} := Fin.cases transition.map.points (Fin.cases transition.map.actors
      (Fin.cases source.main.birth (fun _ => target.main.birth)))
    let fields : Fin 52 → ZFSet.{u} := Fin.addCases (m := 24) (n := 28) source.rawFields (Fin.addCases (m := 24) (n := 4) target.rawFields extra)
    have extraGround : ∀ j, extra j ∈ M.sets :=
      Fin.cases transition.map.points_ground (Fin.cases transition.map.actors_ground
        (Fin.cases source.main.birth_ground (fun _ => target.main.birth_ground)))
    have grounded : ∀ j, fields j ∈ M.sets := by
      intro j
      refine Fin.addCases (m := 24) (n := 28) ?_ ?_ j
      · intro k
        simpa only [fields, Fin.addCases_left] using source.rawFields_ground pairing k
      · intro k
        refine Fin.addCases (m := 24) (n := 4) ?_ ?_ k
        · intro a
          simpa only [fields, Fin.addCases_right, Fin.addCases_left] using target.rawFields_ground pairing a
        · intro a
          simpa only [fields, Fin.addCases_right] using extraGround a
    refine ⟨fields, grounded, ?_⟩
    have smap : (fun j : Fin 24 => fields (j.castAdd 28)) = source.rawFields := by
      funext j
      simp only [fields, Fin.addCases_left]
    have tmap : (fun j : Fin 24 => fields (Fin.natAdd 24 (j.castAdd 4))) = target.rawFields := by
      funext j
      simp only [fields, Fin.addCases_right, Fin.addCases_left]
    rw [smap, tmap, omega]
    change LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) ZFSet.omega
      (env sourceCode) (env targetCode) (env z) transition.map.points transition.map.actors
      source.main.birth target.main.birth source.rawFields target.rawFields
    rw [← sourceEq, ← targetEq, ← codeEq]
    exact source.transition_rawFields target transition coverage

end TransitiveGround
end

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem linked_transition_code {i j : I} (before : i ≤ j) :
    LinkedMainTransitionCode M K Labels C D rD (run.linked i).code (run.linked j).code
      (run.diagram.transition before).map.code := by
  refine ⟨run.linked i, run.linked j, rfl, rfl, ?_⟩
  rw [run.linked_main i, run.linked_main j]
  exact ⟨run.diagram.transition before, rfl, run.coverage before⟩

theorem stageGraph_valid {i a : ZFSet.{u}} (entry : ZFSet.pair i a ∈ run.stageGraph) :
    ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = a := by
  obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source entry)
  exact ⟨run.linked j, ((run.stageGraph_entry j a).1 entry).symm⟩

theorem transitionGraph_valid {i j a b z : ZFSet.{u}}
    (first : ZFSet.pair i a ∈ run.stageGraph) (second : ZFSet.pair j b ∈ run.stageGraph)
    (entry : ZFSet.pair (ZFSet.pair j i) z ∈ run.transitionGraph) :
    LinkedMainTransitionCode M K Labels C D rD a b z := by
  obtain ⟨s, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source first)
  obtain ⟨t, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source second)
  have order := ((pair_mem_chronologyPairs _ _ _).1
    (run.transitionGraph_function.pair_source entry)).2.2
  have before := (run.key_order s t).2 order
  rw [(run.stageGraph_entry s a).1 first, (run.stageGraph_entry t b).1 second,
    (run.transitionGraph_entry before z).1 entry]
  exact run.linked_transition_code before

theorem transitionGraph_identity {i p a : ZFSet.{u}}
    (entry : ZFSet.pair (ZFSet.pair i i) (ZFSet.pair p a) ∈ run.transitionGraph) :
    GraphDiagonalCode p ∧ GraphDiagonalCode a := by
  have domain := (pair_mem_chronologyPairs _ _ _).1 (run.transitionGraph_function.pair_source entry)
  obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 domain.1
  have equal := (run.transitionGraph_entry (le_refl j) (ZFSet.pair p a)).1 entry
  rw [run.diagram.self] at equal
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  exact ⟨graphDiagonalCode_identity _, graphDiagonalCode_identity _⟩

theorem transitionGraph_composition {i j k p₁ a₁ p₂ a₂ p₃ a₃ : ZFSet.{u}}
    (first : ZFSet.pair (ZFSet.pair j i) (ZFSet.pair p₁ a₁) ∈ run.transitionGraph)
    (second : ZFSet.pair (ZFSet.pair k j) (ZFSet.pair p₂ a₂) ∈ run.transitionGraph)
    (third : ZFSet.pair (ZFSet.pair k i) (ZFSet.pair p₃ a₃) ∈ run.transitionGraph) :
    GraphCompositionCode p₁ p₂ p₃ ∧ GraphCompositionCode a₁ a₂ a₃ := by
  have domain₁ := (pair_mem_chronologyPairs _ _ _).1 (run.transitionGraph_function.pair_source first)
  have domain₂ := (pair_mem_chronologyPairs _ _ _).1 (run.transitionGraph_function.pair_source second)
  obtain ⟨s, rfl⟩ := ZFSet.mem_range.1 domain₁.2.1
  obtain ⟨t, rfl⟩ := ZFSet.mem_range.1 domain₁.1
  obtain ⟨v, rfl⟩ := ZFSet.mem_range.1 domain₂.1
  have before₁ := (run.key_order s t).2 domain₁.2.2
  have before₂ := (run.key_order t v).2 domain₂.2.2
  have equal₁ := (run.transitionGraph_entry before₁ _).1 first
  have equal₂ := (run.transitionGraph_entry before₂ _).1 second
  have equal₃ := (run.transitionGraph_entry (le_trans before₁ before₂) _).1 third
  rw [run.diagram.comp before₁ before₂] at equal₃
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal₁
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal₂
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal₃
  exact ⟨graphCompositionCode_relationCompose
      (run.diagram.transition before₁).map.point_embedding.injection.function
      (run.diagram.transition before₂).map.point_embedding.injection.function,
    graphCompositionCode_relationCompose
      (run.diagram.transition before₁).map.group_embedding.injection.function
      (run.diagram.transition before₂).map.group_embedding.injection.function⟩

theorem graph_code : MainPrefixGraphCode M K Labels C D rD run.indices run.stageGraph run.transitionGraph where
  ordinal := run.indices_ordinal
  stages := run.stageGraph_function
  transitions := run.transitionGraph_function
  stage_valid := fun _ _ entry => run.stageGraph_valid entry
  transition_valid := fun _ _ _ _ _ first second entry => run.transitionGraph_valid first second entry
  identity := fun _ _ _ entry => run.transitionGraph_identity entry
  composition := fun _ _ _ _ _ _ _ _ _ first second third => run.transitionGraph_composition first second third

end GroundMainPrefix

section
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mainPrefixCode_fields_mem {T S E : ZFSet.{u}} (ground : mainPrefixCode T S E ∈ M.sets) :
    T ∈ M.sets ∧ S ∈ M.sets ∧ E ∈ M.sets := by
  let fields : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
  have encoded : nonemptyTupleCode 2 fields ∈ M.sets := ground
  have each := M.nonemptyTupleCode_field_mem 2 fields encoded
  exact ⟨each 0, each 1, each 2⟩

end TransitiveGround

namespace BoundedFormula

theorem truth_mainPrefixTupleFormula {n} (z T S E : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainPrefixTupleFormula z T S E) env ↔ env z = mainPrefixCode (env T) (env S) (env E) := by
  rw [mainPrefixTupleFormula, truth_nonemptyTupleFormula]
  have map : (fun j : Fin 3 => env (Fin.cases T (Fin.cases S (fun _ => E)) j)) =
      Fin.cases (env T) (Fin.cases (env S) (fun _ => env E)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) j
  rw [map]
  rfl

theorem realize_mainPrefixTupleFormula (M : TransitiveGround.{u}) {n}
    (z T S E : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixTupleFormula z T S E).toFormula env ↔
      env z = mainPrefixCode (env T) (env S) (env E) :=
  (realize_toFormula M _ env members).trans (truth_mainPrefixTupleFormula z T S E env)

end BoundedFormula

end

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundSerializedCandidateLevels
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

theorem exists_groundMainCandidateLevel
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {K : ZFSet.{u}}
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) :
    Nonempty (GroundMainCandidateLevel M K) := by
  obtain ⟨H, hH, V, hV, hierarchy, entry, membership, _, _⟩ :=
    M.exists_groundCumulativeLevel pairing unions powers separation collection hK ordinal
  exact ⟨⟨H, hH, V, hV, hierarchy, entry, membership⟩⟩

end TransitiveGround





namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem validChronologies_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {C D rD : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.validChronologies C D rD ∈ M.sets :=
  M.serializedChronologyCandidates_mem pairing unions powers separation infinite
    level.carrier_ground hC hD hrD

theorem ranked_mem_validChronologies
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {T C D rD : ZFSet.{u}} (serial : GroundSerializedChronology M T C D rD)
    (rank : ZFSet.rank serial.code < ZFSet.rank K) :
    serial.code ∈ level.validChronologies C D rD :=
  M.serializedChronology_code_mem_candidates serial
    ((level.membership _).2 ⟨serial.code_ground pairing, rank⟩)

end GroundMainCandidateLevel

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundTaskBearingSuccessorDecoding
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include certificate pairing unions powers separation infinite

theorem oldProfilePreservation (Filters : ZFSet.{u}) :
    OldProfilePreservationCode source.stage.carrier source.stage.order source.stage.meetGraph
      certificate.target.stage.carrier certificate.target.stage.order certificate.target.stage.meetGraph
      certificate.transition.map.points Filters := by
  intro F _ c _ e _ K _ profile c' _ e' _ K' _ imageC imageE imageK
  exact certificate.capProfile_preserved pairing unions powers separation infinite
    profile imageC imageE imageK

end PartitionPilot.Forcing.GroundInitialMainSuccessorData



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundLinkedMainStageLevels
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
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_linkedMainStageFormula_raw {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainStageFormula K Labels C D rD N z) env ↔
      ∃ f : Fin 24 → ZFSet.{u}, (∀ j, f j ∈ M.sets) ∧
        LinkedMainStageRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N) (env z) f := by
  rw [linkedMainStageFormula, realize_exBlock]
  have actual (f : Fin 24 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :=
    M.realize_linkedMainStageRawFormula pairing unions powers separation collection
      (suffixIndex n 24 K) (suffixIndex n 24 Labels) (suffixIndex n 24 C) (suffixIndex n 24 D)
      (suffixIndex n 24 rD) (suffixIndex n 24 N) (suffixIndex n 24 z) (prefixIndex n 24)
      (extendMany 24 f env) (extendMany_members 24 f env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f, ground, (actual f ground).1 recognized⟩
  · rintro ⟨f, ground, raw⟩
    exact ⟨f, ground, (actual f ground).2 raw⟩

theorem realize_linkedMainStageFormula {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainStageFormula K Labels C D rD N z) env ↔
      ∃ linked : GroundLinkedMainStage M (env K) (env Labels) (env C) (env D) (env rD),
        linked.code = env z := by
  rw [M.realize_linkedMainStageFormula_raw pairing unions powers separation collection
    K Labels C D rD N z env members omega ordinal]
  constructor
  · rintro ⟨f, ground, raw⟩
    exact raw.exists_linked pairing unions powers separation ground (members C) (members D) (members rD) omega
  · rintro ⟨linked, equal⟩
    refine ⟨linked.rawFields, linked.rawFields_ground pairing, ?_⟩
    rw [omega, ← equal]
    exact linked.rawFields_code

end TransitiveGround

end PartitionPilot.Forcing



end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundOmegaOneTaskBearingSuccessorFunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialMainSeedSuccessorRanked
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) seed.source C,
          ∃ initial : GroundSerializedChronology M (insert seed.source.cutoff seed.source.cutoff)
              C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
            ∃ successor : GroundSerializedChronology M
                (insert certificate.target.cutoff certificate.target.cutoff)
                C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
              level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
              initial.code ∈ M.sets ∧ ZFSet.rank initial.code < ZFSet.rank K ∧
              initial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∧
              (∀ j t, t ∈ insert seed.source.cutoff seed.source.cutoff →
                initial.fields.value j t = seed.source.history.fieldValue j t) ∧
              successor.code ∈ M.sets ∧ ZFSet.rank successor.code < ZFSet.rank K ∧
              successor.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∧
              (∀ j t, t ∈ insert certificate.target.cutoff certificate.target.cutoff →
                successor.fields.value j t = certificate.target.history.fieldValue j t) ∧
              certificate.target.Invariant K C ∧
              ZFSet.rank certificate.transition.map.code < ZFSet.rank K ∧
              successor.fields.value 0 certificate.target.cutoff = certificate.target.stage.carrier ∧
              successor.fields.value 1 certificate.target.cutoff = certificate.target.stage.order ∧
              successor.fields.value 2 certificate.target.cutoff = certificate.target.stage.meetGraph ∧
              successor.fields.value 3 certificate.target.cutoff = certificate.target.birth ∧
              successor.fields.value 4 certificate.target.cutoff = certificate.target.stage.height := by
  dsimp only
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨level⟩ := M.exists_groundMainCandidateLevel pairing unions powers separation collection hK conditions.1
  obtain ⟨seed⟩ := M.exists_groundInitialMainSeed pairing unions powers separation infinite collection hK conditions
  obtain ⟨initial, initialGround, initialRank, initialAgreement⟩ :=
    seed.exists_matchedInitialSerialization pairing unions powers separation infinite hK conditions
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  obtain ⟨certificate⟩ := M.exists_groundInitialMainSuccessor pairing unions powers separation
    collection infinite choice seed.source hC seed.injection_ground seed.dense
    (fun lo hlo => (seed.no_endpoints lo hlo).2) seed.injection_code
  obtain ⟨successor, successorGround, successorRank, successorMember, successorAgreement, terminal⟩ :=
    certificate.exists_rankedTargetSerialization pairing unions powers separation collection infinite choice
      hK conditions seed.invariant level initial initialRank initialAgreement
  have invariant := certificate.target_invariant pairing unions powers separation collection infinite
    choice hC hK standard seed.invariant
  have transitionRank := certificate.transition.map.code_rank_lt_inaccessible pairing unions powers separation infinite
    hK conditions seed.invariant.points_rank invariant.points_rank seed.invariant.actors_rank invariant.actors_rank
  exact ⟨level, seed, certificate, initial, successor,
    level.validChronologies_ground pairing unions powers separation infinite seed.source.stage.columns_ground
      seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    initialGround, initialRank, level.ranked_mem_validChronologies pairing initial initialRank, initialAgreement,
    successorGround, successorRank, successorMember, successorAgreement, invariant, transitionRank, terminal⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixPreservedSeeds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {I : Type v} [Small.{u} I] [Preorder I] [Finite I]

variable {pairing unions powers separation}
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
variable (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
variable (conditions : GroundInaccessibleConditions M K)
variable (keys : ∀ i, ZFSet.rank (run.key i) < ZFSet.rank K)
include infinite hK conditions keys

theorem finite_stageGraph_rank_lt : ZFSet.rank run.stageGraph < ZFSet.rank K :=
  familyCodeGraph_finite_rank_lt (conditions.rank_isLimit pairing unions powers separation infinite hK)
    run.key _ keys (fun i => (run.linked i).code_rank_lt pairing unions powers separation infinite hK conditions)

omit keys [Finite I] in
theorem transition_code_rank_lt {i j : I} (before : i ≤ j) :
    ZFSet.rank (run.diagram.transition before).map.code < ZFSet.rank K := by
  have invariants (k : I) : (run.diagram.stage k).Invariant K Labels :=
    run.linked_main k ▸ (run.linked k).invariant
  exact (run.diagram.transition before).map.code_rank_lt_inaccessible
    pairing unions powers separation infinite hK conditions
    (invariants i).points_rank (invariants j).points_rank
    (invariants i).actors_rank (invariants j).actors_rank

attribute [local instance] OAI.PartitionPilot.Forcing.GroundMainPrefix.instFiniteMainTransitionIndex
theorem finite_transitionGraph_rank_lt : ZFSet.rank run.transitionGraph < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact familyCodeGraph_finite_rank_lt limit _ _
    (fun p => rank_orderedPair_lt limit (keys p.val.2) (keys p.val.1))
    (fun p => run.transition_code_rank_lt infinite hK conditions p.property)

theorem finite_code_rank_lt : ZFSet.rank run.code < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases (rank_finiteCodeRange_lt limit run.key keys)
      (Fin.cases (run.finite_stageGraph_rank_lt infinite hK conditions keys)
        (fun _ => run.finite_transitionGraph_rank_lt infinite hK conditions keys)))

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (first second : GroundLinkedMainStage M K Labels C D rD)
variable (step : GroundChronologicalMainTransition first.main second.main)
variable (coverage : step.CoversOldBirths)

theorem twoStage_indices :
    (twoStage pairing unions powers separation first second step coverage).indices = natSetCode 2 :=
  finiteMainIndexKey_range 2

theorem twoStage_stageGraph_zero (z : ZFSet.{u}) :
    ZFSet.pair (natSetCode 0) z ∈
      (twoStage pairing unions powers separation first second step coverage).stageGraph ↔ z = first.code :=
  (twoStage pairing unions powers separation first second step coverage).stageGraph_entry 0 z

theorem twoStage_stageGraph_one (z : ZFSet.{u}) :
    ZFSet.pair (natSetCode 1) z ∈
      (twoStage pairing unions powers separation first second step coverage).stageGraph ↔ z = second.code :=
  (twoStage pairing unions powers separation first second step coverage).stageGraph_entry 1 z

theorem twoStage_transitionGraph_zero_one (z : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 1) (natSetCode 0)) z ∈
      (twoStage pairing unions powers separation first second step coverage).transitionGraph ↔ z = step.map.code :=
  (twoStage pairing unions powers separation first second step coverage).transitionGraph_entry
    (show (0 : Fin 2) ≤ 1 from by decide) z

theorem twoStage_code_rank_lt (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K) :
    ZFSet.rank (twoStage pairing unions powers separation first second step coverage).code < ZFSet.rank K := by
  apply (twoStage pairing unions powers separation first second step coverage).finite_code_rank_lt
    infinite hK conditions
  intro i
  exact rank_natSetCode_lt (conditions.rank_isLimit pairing unions powers separation infinite hK) i.val

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source middle target first second : GroundChronologicalMainStage M C D rD}

theorem identity_preservesOldProfiles
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (stage : GroundChronologicalMainStage M C D rD) :
    (identity pairing unions powers separation stage).PreservesOldProfiles :=
  OldProfilePreservationCode.identity stage.stage.carrier stage.stage.order stage.stage.meetGraph
    (M.groundPower stage.stage.carrier)

end GroundChronologicalMainTransition

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialTwoStageMainPrefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) seed.source C,
          ∃ first second : GroundLinkedMainStage M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode),
            ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
              first.main = seed.source ∧ second.main = certificate.target ∧
              first.serial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∧
              second.serial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∧
              run.indices = natSetCode 2 ∧ run.code ∈ M.sets ∧ ZFSet.rank run.code < ZFSet.rank K ∧
              run.linked 0 = first ∧ run.linked 1 = second ∧
              run.diagram.stage 0 = seed.source ∧ run.diagram.stage 1 = certificate.target ∧
              (∀ z, ZFSet.pair (natSetCode 0) z ∈ run.stageGraph ↔ z = first.code) ∧
              (∀ z, ZFSet.pair (natSetCode 1) z ∈ run.stageGraph ↔ z = second.code) ∧
              (∀ z, ZFSet.pair (ZFSet.pair (natSetCode 1) (natSetCode 0)) z ∈ run.transitionGraph ↔
                z = certificate.transition.map.code) ∧
              (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.points =
                certificate.transition.map.points ∧
              (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.actors =
                certificate.transition.map.actors := by
  dsimp only
  obtain ⟨level, seed, certificate, initial, successor, _candidateGround,
    _initialGround, initialRank, initialMember, initialAgreement,
    _successorGround, successorRank, successorMember, successorAgreement,
    targetInvariant, _transitionRank, _terminal⟩ :=
    M.exists_groundInitialMainSeedSuccessorRanked pairing unions powers separation
      collection infinite choice hK standard
  let first : GroundLinkedMainStage M K
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) :=
    ⟨seed.source, initial, initialAgreement, seed.invariant, initialRank⟩
  let second : GroundLinkedMainStage M K
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      (M.groundOmegaOne pairing unions powers separation collection infinite)
      (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode) :=
    ⟨certificate.target, successor, successorAgreement, targetInvariant, successorRank⟩
  let run := GroundMainPrefix.twoStage pairing unions powers separation first second
    certificate.transition certificate.coversOldBirths
  have conditions := standard.to_conditions pairing unions powers separation hK
  exact ⟨level, seed, certificate, first, second, run, rfl, rfl, initialMember, successorMember,
    GroundMainPrefix.twoStage_indices pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths,
    run.code_ground,
    GroundMainPrefix.twoStage_code_rank_lt pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths infinite hK conditions,
    rfl, rfl, rfl, rfl,
    GroundMainPrefix.twoStage_stageGraph_zero pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths,
    GroundMainPrefix.twoStage_stageGraph_one pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths,
    GroundMainPrefix.twoStage_transitionGraph_zero_one pairing unions powers separation first second
      certificate.transition certificate.coversOldBirths,
    rfl, rfl⟩

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

theorem restrict_preservesOldProfiles (preserved : run.PreservesOldProfiles)
    {S : ZFSet.{u}} (subset : S ⊆ run.indices) (ground : S ∈ M.sets)
    (ordinal : ordinalSetProperty S) :
    (run.restrict subset ground ordinal).PreservesOldProfiles := by
  intro i j before
  exact preserved i.val j.val before

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (Fin 2))

theorem zero_key_of_two_indices (indices : run.indices = natSetCode 2) :
    run.key 0 = natSetCode 0 := by
  have member : natSetCode 0 ∈ run.indices := by
    rw [indices]
    exact (natSetCode_mem_iff 0 2).2 (by decide)
  obtain ⟨i, equal⟩ := ZFSet.mem_range.1 member
  obtain equalKeys | below := (run.key_order 0 i).1 (Fin.zero_le i)
  · exact equalKeys.trans equal
  · rw [equal] at below
    exact False.elim (ZFSet.notMem_empty _ below)

theorem exists_initialRestriction (indices : run.indices = natSetCode 2)
    (preserved : run.PreservesOldProfiles)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (oldRank : ZFSet.rank run.code < o) :
    ∃ initial : GroundMainPrefix M K Labels C D rD pairing unions powers separation
        {i : Fin 2 // run.key i ∈ natSetCode 1},
      initial.indices = natSetCode 1 ∧ initial.PreservesOldProfiles ∧
      ZFSet.rank initial.code < o ∧
      initial.stageGraph = graphRestriction (natSetCode 1) run.stageGraph ∧
      initial.transitionGraph = graphRestriction (chronologyPairs (natSetCode 1)) run.transitionGraph ∧
      (∀ i, initial.linked i = run.linked i.val) ∧
      ∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = run.diagram.stage 0 := by
  have oneMember : natSetCode 1 ∈ run.indices := by
    rw [indices]
    exact (natSetCode_mem_iff 1 2).2 (by decide)
  have subset : natSetCode 1 ⊆ run.indices := by
    intro x hx
    rw [indices]
    obtain ⟨n, hn, rfl⟩ := (mem_natSetCode x 1).1 hx
    exact (natSetCode_mem_iff n 2).2 (by omega)
  have ground := M.transitive run.indices_ground oneMember
  have ordinal := ordinalSetProperty_member run.indices_ordinal oneMember
  let initial := run.restrict subset ground ordinal
  have zeroMember : run.key 0 ∈ natSetCode 1 := by
    rw [run.zero_key_of_two_indices indices]
    exact (natSetCode_mem_iff 0 1).2 (by decide)
  exact ⟨initial, run.restrict_indices subset ground ordinal,
    run.restrict_preservesOldProfiles preserved subset ground ordinal,
    run.restrict_code_rank_lt subset ground ordinal limit oldRank,
    run.restrict_stageGraph subset ground ordinal,
    run.restrict_transitionGraph subset ground ordinal, fun _ => rfl,
    ⟨0, zeroMember⟩, run.zero_key_of_two_indices indices, rfl⟩

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}

theorem preservesOldProfiles_of_zero_one
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (Fin 2))
    (crossing : (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).PreservesOldProfiles) :
    run.PreservesOldProfiles := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro before
      rw [run.diagram.self]
      exact GroundChronologicalMainTransition.identity_preservesOldProfiles
        pairing unions powers separation (run.diagram.stage 0)
    · rw [Fin.eq_zero j]
      intro _
      exact crossing
  · rw [Fin.eq_zero i]
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro before
      exact False.elim ((by decide : ¬ (1 : Fin 2) ≤ 0) before)
    · rw [Fin.eq_zero j]
      intro before
      rw [run.diagram.self]
      exact GroundChronologicalMainTransition.identity_preservesOldProfiles
        pairing unions powers separation (run.diagram.stage 1)

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_LinkedProfileTransitionRawCodes
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
theorem realize_linkedProfilePreservingTransitionRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : Fin n)
    (source target : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedProfilePreservingTransitionRawFormula K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth Families source target) env ↔
    LinkedProfilePreservingTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD)
      (env N) (env sourceCode) (env targetCode) (env z) (env points) (env actors)
      (env sourceBirth) (env targetBirth) (env Families)
      (fun j => env (source j)) (fun j => env (target j)) :=
  (M.realize_linkedMainTransitionRawFormula pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth source target
    env members omega ordinal).and
    ((M.realize_relativePowerFormula (source 0) Families env members).and
      (BoundedFormula.realize_oldProfilePreservationFormula M (source 0) (source 1) (source 2)
        (target 0) (target 1) (target 2) points Families env members))

end TransitiveGround

namespace LinkedProfilePreservingTransitionRawCode
variable {M : TransitiveGround.{u}}
variable {K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : ZFSet.{u}}
variable {source target : Fin 24 → ZFSet.{u}}

theorem exists_transition
    (raw : LinkedProfilePreservingTransitionRawCode M K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth Families source target)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (sourceGround : ∀ j, source j ∈ M.sets) (targetGround : ∀ j, target j ∈ M.sets)
    (hPoints : points ∈ M.sets) (hActors : actors ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (omega : N = ZFSet.omega) :
    LinkedProfilePreservingTransitionCode M K Labels C D rD sourceCode targetCode z := by
  rw [omega] at raw
  obtain ⟨s, t, sourceEqual, targetEqual, transition, equal, covered⟩ :=
    raw.1.exists_transition pairing unions powers separation sourceGround targetGround
      hPoints hActors hC hD hrD rfl
  have sourceCode := s.rawFields_code
  have targetCode := t.rawFields_code
  rw [sourceEqual] at sourceCode
  rw [targetEqual] at targetCode
  have sourceFields := sourceCode.fields_unique raw.1.1
  have targetFields := targetCode.fields_unique raw.1.2.1
  have mapEqual : ZFSet.pair transition.map.points transition.map.actors = ZFSet.pair points actors :=
    equal.trans raw.1.2.2.2.2.1.1
  have pointsEqual := (ZFSet.pair_inj.1 mapEqual).1
  have preservation := raw.2.2
  rw [raw.2.1, ← sourceFields, ← targetFields] at preservation
  refine ⟨s, t, sourceEqual, targetEqual, transition, equal, covered, ?_⟩
  change OldProfilePreservationCode s.main.stage.carrier s.main.stage.order s.main.stage.meetGraph
    t.main.stage.carrier t.main.stage.order t.main.stage.meetGraph
    transition.map.points (M.groundPower s.main.stage.carrier)
  rw [pointsEqual]
  exact preservation

end LinkedProfilePreservingTransitionRawCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (source target : GroundLinkedMainStage M K Labels C D rD)
theorem profileTransition_rawFields
    (transition : GroundChronologicalMainTransition source.main target.main)
    (covered : transition.CoversOldBirths) (preserved : transition.PreservesOldProfiles) :
    LinkedProfilePreservingTransitionRawCode M K Labels C D rD ZFSet.omega source.code target.code
      transition.map.code transition.map.points transition.map.actors source.main.birth target.main.birth
      (M.groundPower source.main.stage.carrier) source.rawFields target.rawFields :=
  ⟨source.transition_rawFields target transition covered, rfl, preserved⟩

end GroundLinkedMainStage

end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_MainPrefixValidityFormulas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

theorem truth_pairedTransitionEntryFormula {n} (i j p a E : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (pairedTransitionEntryFormula i j p a E) env ↔
      ZFSet.pair (ZFSet.pair (env j) (env i)) (ZFSet.pair (env p) (env a)) ∈ env E := by
  simp only [pairedTransitionEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_orderedTripleFormula]
  change (∃ w ∈ env E, ∃ b ∈ w, ∃ c ∈ b, c = ZFSet.pair (env p) (env a) ∧
    w = ZFSet.pair (ZFSet.pair (env j) (env i)) c) ↔ _
  constructor
  · rintro ⟨w, hw, b, _, c, _, rfl, rfl⟩
    exact hw
  · intro entry
    refine ⟨_, entry, {ZFSet.pair (env j) (env i), ZFSet.pair (env p) (env a)},
      ZFSet.mem_pair.2 (Or.inr rfl), _, ZFSet.mem_pair.2 (Or.inr rfl), rfl, rfl⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixIdentityFormula {n} (E : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixIdentityFormula E) env ↔
      ∀ i p a, ZFSet.pair (ZFSet.pair i i) (ZFSet.pair p a) ∈ env E →
        GraphDiagonalCode p ∧ GraphDiagonalCode a := by
  rw [mainPrefixIdentityFormula, realize_allBlock]
  have actual (fields : Fin 3 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    BoundedFormula.realize_toFormula M
      (BoundedFormula.imp
        (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 3 0) (prefixIndex n 3 0)
          (prefixIndex n 3 1) (prefixIndex n 3 2) (suffixIndex n 3 E))
        (.conj (BoundedFormula.graphDiagonalFormula (prefixIndex n 3 1))
          (BoundedFormula.graphDiagonalFormula (prefixIndex n 3 2))))
      (extendMany 3 fields env) (extendMany_members 3 fields env ground members)
  simp only [BoundedFormula.truth_imp, BoundedFormula.Truth,
    BoundedFormula.truth_pairedTransitionEntryFormula, BoundedFormula.truth_graphDiagonalFormula,
    extendMany_prefix, extendMany_suffix] at actual
  constructor
  · intro recognized i p a entry
    have hg := M.transitive (members E) entry
    let fields : Fin 3 → ZFSet.{u} := Fin.cases i (Fin.cases p (fun _ => a))
    have ground : ∀ j, fields j ∈ M.sets := Fin.cases (M.pair_left (M.pair_left hg))
      (Fin.cases (M.pair_left (M.pair_right hg)) (fun _ => M.pair_right (M.pair_right hg)))
    exact (actual fields ground).1 (recognized fields ground) entry
  · intro law fields ground
    exact (actual fields ground).2 (law (fields 0) (fields 1) (fields 2))

theorem realize_mainPrefixCompositionFormula {n} (E : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixCompositionFormula E) env ↔
      ∀ i j k p₁ a₁ p₂ a₂ p₃ a₃,
        ZFSet.pair (ZFSet.pair j i) (ZFSet.pair p₁ a₁) ∈ env E →
        ZFSet.pair (ZFSet.pair k j) (ZFSet.pair p₂ a₂) ∈ env E →
        ZFSet.pair (ZFSet.pair k i) (ZFSet.pair p₃ a₃) ∈ env E →
        GraphCompositionCode p₁ p₂ p₃ ∧ GraphCompositionCode a₁ a₂ a₃ := by
  rw [mainPrefixCompositionFormula, realize_allBlock]
  have actual (fields : Fin 9 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    BoundedFormula.realize_toFormula M
      (BoundedFormula.imp
        (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 9 0) (prefixIndex n 9 1)
          (prefixIndex n 9 3) (prefixIndex n 9 4) (suffixIndex n 9 E))
        (BoundedFormula.imp
          (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 9 1) (prefixIndex n 9 2)
            (prefixIndex n 9 5) (prefixIndex n 9 6) (suffixIndex n 9 E))
          (BoundedFormula.imp
            (BoundedFormula.pairedTransitionEntryFormula (prefixIndex n 9 0) (prefixIndex n 9 2)
              (prefixIndex n 9 7) (prefixIndex n 9 8) (suffixIndex n 9 E))
            (.conj (BoundedFormula.graphCompositionFormula (prefixIndex n 9 3) (prefixIndex n 9 5) (prefixIndex n 9 7))
              (BoundedFormula.graphCompositionFormula (prefixIndex n 9 4) (prefixIndex n 9 6) (prefixIndex n 9 8))))))
      (extendMany 9 fields env) (extendMany_members 9 fields env ground members)
  simp only [BoundedFormula.truth_imp, BoundedFormula.Truth,
    BoundedFormula.truth_pairedTransitionEntryFormula, BoundedFormula.truth_graphCompositionFormula,
    extendMany_prefix, extendMany_suffix] at actual
  constructor
  · intro recognized i j k p₁ a₁ p₂ a₂ p₃ a₃ first second third
    have h₁ := M.transitive (members E) first
    have h₂ := M.transitive (members E) second
    have h₃ := M.transitive (members E) third
    let fields : Fin 9 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases k (Fin.cases p₁
      (Fin.cases a₁ (Fin.cases p₂ (Fin.cases a₂ (Fin.cases p₃ (fun _ => a₃))))))))
    have ground : ∀ a, fields a ∈ M.sets := Fin.cases (M.pair_right (M.pair_left h₁))
      (Fin.cases (M.pair_left (M.pair_left h₁)) (Fin.cases (M.pair_left (M.pair_left h₂))
      (Fin.cases (M.pair_left (M.pair_right h₁)) (Fin.cases (M.pair_right (M.pair_right h₁))
      (Fin.cases (M.pair_left (M.pair_right h₂)) (Fin.cases (M.pair_right (M.pair_right h₂))
      (Fin.cases (M.pair_left (M.pair_right h₃)) (fun _ => M.pair_right (M.pair_right h₃)))))))))
    exact (actual fields ground).1 (recognized fields ground) first second third
  · intro law fields ground
    exact (actual fields ground).2 (law (fields 0) (fields 1) (fields 2) (fields 3)
      (fields 4) (fields 5) (fields 6) (fields 7) (fields 8))

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_mainPrefixStagesFormula {n} (K Labels C D rD N S : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixStagesFormula K Labels C D rD N S) env ↔
      ∀ i a, ZFSet.pair i a ∈ env S →
        ∃ linked : GroundLinkedMainStage M (env K) (env Labels) (env C) (env D) (env rD),
          linked.code = a := by
  rw [mainPrefixStagesFormula, realize_allBlock]
  have actual (fields : Fin 2 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.pairMembershipFormula (prefixIndex n 2 0) (prefixIndex n 2 1)
          (suffixIndex n 2 S)).toFormula
          (linkedMainStageFormula (suffixIndex n 2 K) (suffixIndex n 2 Labels)
            (suffixIndex n 2 C) (suffixIndex n 2 D) (suffixIndex n 2 rD)
            (suffixIndex n 2 N) (prefixIndex n 2 1))) (extendMany 2 fields env) ↔
        ZFSet.pair (fields 0) (fields 1) ∈ env S →
          ∃ linked : GroundLinkedMainStage M (env K) (env Labels) (env C) (env D) (env rD),
            linked.code = fields 1 := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 2 fields env ground members), BoundedFormula.truth_pairMembershipFormula,
      M.realize_linkedMainStageFormula pairing unions powers separation collection _ _ _ _ _ _ _ _
        (extendMany_members 2 fields env ground members)
        (by simpa only [extendMany_suffix] using omega)
        (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
    rfl
  constructor
  · intro recognized i a entry
    have hg := M.transitive (members S) entry
    let fields : Fin 2 → ZFSet.{u} := Fin.cases i (fun _ => a)
    have ground : ∀ j, fields j ∈ M.sets := Fin.cases (M.pair_left hg) (fun _ => M.pair_right hg)
    exact (actual fields ground).1 (recognized fields ground) entry
  · intro law fields ground
    exact (actual fields ground).2 (law (fields 0) (fields 1))

theorem realize_mainPrefixTransitionsFormula {n} (K Labels C D rD N S E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixTransitionsFormula K Labels C D rD N S E) env ↔
      ∀ i j a b z, ZFSet.pair i a ∈ env S → ZFSet.pair j b ∈ env S →
        ZFSet.pair (ZFSet.pair j i) z ∈ env E →
        LinkedMainTransitionCode M (env K) (env Labels) (env C) (env D) (env rD) a b z := by
  rw [mainPrefixTransitionsFormula, realize_allBlock]
  have actual (fields : Fin 5 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.conj
          (BoundedFormula.pairMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 2) (suffixIndex n 5 S))
          (.conj (BoundedFormula.pairMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 3) (suffixIndex n 5 S))
            (BoundedFormula.tripleMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 0) (prefixIndex n 5 4)
              (suffixIndex n 5 E)))).toFormula
          (linkedMainTransitionFormula (suffixIndex n 5 K) (suffixIndex n 5 Labels) (suffixIndex n 5 C)
            (suffixIndex n 5 D) (suffixIndex n 5 rD) (suffixIndex n 5 N)
            (prefixIndex n 5 2) (prefixIndex n 5 3) (prefixIndex n 5 4))) (extendMany 5 fields env) ↔
        (ZFSet.pair (fields 0) (fields 2) ∈ env S ∧ ZFSet.pair (fields 1) (fields 3) ∈ env S ∧
          ZFSet.pair (ZFSet.pair (fields 1) (fields 0)) (fields 4) ∈ env E) →
        LinkedMainTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
          (fields 2) (fields 3) (fields 4) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 5 fields env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_pairMembershipFormula,
      BoundedFormula.truth_tripleMembershipFormula]
    rw [M.realize_linkedMainTransitionFormula pairing unions powers separation collection _ _ _ _ _ _ _ _ _ _
      (extendMany_members 5 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · intro recognized i j a b z first second third
    have h₁ := M.transitive (members S) first
    have h₂ := M.transitive (members S) second
    have h₃ := M.transitive (members E) third
    let fields : Fin 5 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases a (Fin.cases b (fun _ => z))))
    have ground : ∀ k, fields k ∈ M.sets := Fin.cases (M.pair_left h₁)
      (Fin.cases (M.pair_left h₂) (Fin.cases (M.pair_right h₁)
        (Fin.cases (M.pair_right h₂) (fun _ => M.pair_right h₃))))
    exact (actual fields ground).1 (recognized fields ground) ⟨first, second, third⟩
  · intro law fields ground
    exact (actual fields ground).2 (fun entries =>
      law (fields 0) (fields 1) (fields 2) (fields 3) (fields 4) entries.1 entries.2.1 entries.2.2)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundLinkedProfileTransitionRecognition
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
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_linkedProfilePreservingTransitionFormula_raw {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedProfilePreservingTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      ∃ fields : Fin 53 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
        LinkedProfilePreservingTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
          (env sourceCode) (env targetCode) (env z) (fields 48) (fields 49) (fields 50) (fields 51) (fields 52)
          (fun j => fields (j.castAdd 29)) (fun j => fields (Fin.natAdd 24 (j.castAdd 5))) := by
  rw [linkedProfilePreservingTransitionFormula, realize_exBlock]
  have actual (fields : Fin 53 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    M.realize_linkedProfilePreservingTransitionRawFormula pairing unions powers separation collection
      (suffixIndex n 53 K) (suffixIndex n 53 Labels) (suffixIndex n 53 C) (suffixIndex n 53 D)
      (suffixIndex n 53 rD) (suffixIndex n 53 N) (suffixIndex n 53 sourceCode)
      (suffixIndex n 53 targetCode) (suffixIndex n 53 z)
      (prefixIndex n 53 48) (prefixIndex n 53 49) (prefixIndex n 53 50) (prefixIndex n 53 51) (prefixIndex n 53 52)
      (fun j => prefixIndex n 53 (j.castAdd 29)) (fun j => prefixIndex n 53 (Fin.natAdd 24 (j.castAdd 5)))
      (extendMany 53 fields env) (extendMany_members 53 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).1 recognized⟩
  · rintro ⟨fields, ground, raw⟩
    exact ⟨fields, ground, (actual fields ground).2 raw⟩

theorem realize_linkedProfilePreservingTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedProfilePreservingTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      LinkedProfilePreservingTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
        (env sourceCode) (env targetCode) (env z) := by
  rw [M.realize_linkedProfilePreservingTransitionFormula_raw pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z env members omega ordinal]
  constructor
  · rintro ⟨fields, ground, raw⟩
    exact raw.exists_transition pairing unions powers separation
      (fun j => ground (j.castAdd 29)) (fun j => ground (Fin.natAdd 24 (j.castAdd 5)))
      (ground 48) (ground 49) (members C) (members D) (members rD) omega
  · rintro ⟨source, target, sourceEq, targetEq, transition, codeEq, coverage, preserved⟩
    let extra : Fin 5 → ZFSet.{u} := Fin.cases transition.map.points (Fin.cases transition.map.actors
      (Fin.cases source.main.birth (Fin.cases target.main.birth
        (fun _ => M.groundPower source.main.stage.carrier))))
    let fields : Fin 53 → ZFSet.{u} := Fin.addCases (m := 24) (n := 29) source.rawFields (Fin.addCases (m := 24) (n := 5) target.rawFields extra)
    have extraGround : ∀ j, extra j ∈ M.sets :=
      Fin.cases transition.map.points_ground (Fin.cases transition.map.actors_ground
        (Fin.cases source.main.birth_ground (Fin.cases target.main.birth_ground
          (fun _ => M.groundPower_mem powers source.main.stage.carrier_ground))))
    have grounded : ∀ j, fields j ∈ M.sets := by
      intro j
      refine Fin.addCases (m := 24) (n := 29) ?_ ?_ j
      · intro k
        simpa only [fields, Fin.addCases_left] using source.rawFields_ground pairing k
      · intro k
        refine Fin.addCases (m := 24) (n := 5) ?_ ?_ k
        · intro a
          simpa only [fields, Fin.addCases_right, Fin.addCases_left] using target.rawFields_ground pairing a
        · intro a
          simpa only [fields, Fin.addCases_right] using extraGround a
    refine ⟨fields, grounded, ?_⟩
    have smap : (fun j : Fin 24 => fields (j.castAdd 29)) = source.rawFields := by
      funext j
      simp only [fields, Fin.addCases_left]
    have tmap : (fun j : Fin 24 => fields (Fin.natAdd 24 (j.castAdd 5))) = target.rawFields := by
      funext j
      simp only [fields, Fin.addCases_right, Fin.addCases_left]
    rw [smap, tmap, omega]
    change LinkedProfilePreservingTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) ZFSet.omega
      (env sourceCode) (env targetCode) (env z) transition.map.points transition.map.actors
      (source.main.birth) (target.main.birth)
      (M.groundPower source.main.stage.carrier) source.rawFields target.rawFields
    rw [← sourceEq, ← targetEq, ← codeEq]
    exact source.profileTransition_rawFields target transition coverage preserved

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_MainPrefixHistoryUnionRecognition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ZFSet



namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem linked_profile_code (preserved : run.PreservesOldProfiles) {i j : I} (before : i ≤ j) :
    LinkedProfilePreservingTransitionCode M K Labels C D rD
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code := by
  refine ⟨run.linked i, run.linked j, rfl, rfl, ?_⟩
  rw [run.linked_main i, run.linked_main j]
  exact ⟨run.diagram.transition before, rfl, run.coverage before, preserved i j before⟩

theorem profile_graph_code (preserved : run.PreservesOldProfiles) :
    MainPrefixProfileGraphCode M K Labels C D rD run.stageGraph run.transitionGraph := by
  intro i j a b z first second entry
  obtain ⟨s, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source first)
  obtain ⟨t, rfl⟩ := ZFSet.mem_range.1 (run.stageGraph_function.pair_source second)
  have order := ((pair_mem_chronologyPairs _ _ _).1
    (run.transitionGraph_function.pair_source entry)).2.2
  have before := (run.key_order s t).2 order
  rw [(run.stageGraph_entry s a).1 first, (run.stageGraph_entry t b).1 second,
    (run.transitionGraph_entry before z).1 entry]
  exact run.linked_profile_code preserved before

end GroundMainPrefix

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem preserved_code (preserved : run.PreservesOldProfiles) :
    PreservedMainPrefixCode M K Labels C D rD run.code :=
  ⟨run.indices, run.stageGraph, run.transitionGraph, rfl, run.graph_code, run.profile_graph_code preserved⟩

end GroundMainPrefix

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_mainPrefixProfileGraphFormula {n} (K Labels C D rD N S E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixProfileGraphFormula K Labels C D rD N S E) env ↔
      MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (env S) (env E) := by
  rw [mainPrefixProfileGraphFormula, realize_allBlock]
  have actual (fields : Fin 5 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets
        (imp (BoundedFormula.conj
          (BoundedFormula.pairMembershipFormula (prefixIndex n 5 0) (prefixIndex n 5 2) (suffixIndex n 5 S))
          (.conj (BoundedFormula.pairMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 3) (suffixIndex n 5 S))
            (BoundedFormula.tripleMembershipFormula (prefixIndex n 5 1) (prefixIndex n 5 0) (prefixIndex n 5 4)
              (suffixIndex n 5 E)))).toFormula
          (linkedProfilePreservingTransitionFormula (suffixIndex n 5 K) (suffixIndex n 5 Labels) (suffixIndex n 5 C)
            (suffixIndex n 5 D) (suffixIndex n 5 rD) (suffixIndex n 5 N)
            (prefixIndex n 5 2) (prefixIndex n 5 3) (prefixIndex n 5 4))) (extendMany 5 fields env) ↔
        (ZFSet.pair (fields 0) (fields 2) ∈ env S ∧ ZFSet.pair (fields 1) (fields 3) ∈ env S ∧
          ZFSet.pair (ZFSet.pair (fields 1) (fields 0)) (fields 4) ∈ env E) →
        LinkedProfilePreservingTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
          (fields 2) (fields 3) (fields 4) := by
    rw [realize_imp, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 5 fields env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_pairMembershipFormula,
      BoundedFormula.truth_tripleMembershipFormula]
    rw [M.realize_linkedProfilePreservingTransitionFormula pairing unions powers separation collection _ _ _ _ _ _ _ _ _ _
      (extendMany_members 5 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)]
    simp only [extendMany_prefix, extendMany_suffix]
  constructor
  · intro recognized i j a b z first second third
    have h₁ := M.transitive (members S) first
    have h₂ := M.transitive (members S) second
    have h₃ := M.transitive (members E) third
    let fields : Fin 5 → ZFSet.{u} := Fin.cases i (Fin.cases j (Fin.cases a (Fin.cases b (fun _ => z))))
    have ground : ∀ k, fields k ∈ M.sets := Fin.cases (M.pair_left h₁)
      (Fin.cases (M.pair_left h₂) (Fin.cases (M.pair_right h₁)
        (Fin.cases (M.pair_right h₂) (fun _ => M.pair_right h₃))))
    exact (actual fields ground).1 (recognized fields ground) ⟨first, second, third⟩
  · intro law fields ground
    exact (actual fields ground).2 (fun entries =>
      law (fields 0) (fields 1) (fields 2) (fields 3) (fields 4) entries.1 entries.2.1 entries.2.2)

end TransitiveGround
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundInitialPreservedMainPrefix
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
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_mainPrefixGraphBodyFormula {n} (K Labels C D rD N T S E J : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K))
    (pairs : env J = chronologyPairs (env T)) :
    Realize M.sets (mainPrefixGraphBodyFormula K Labels C D rD N T S E J) env ↔
      MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (env T) (env S) (env E) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula T).toFormula env ∧
    Realize M.sets (functionGraphOnFormula T S) env ∧
    Realize M.sets (functionGraphOnFormula J E) env ∧
    Realize M.sets (mainPrefixStagesFormula K Labels C D rD N S) env ∧
    Realize M.sets (mainPrefixTransitionsFormula K Labels C D rD N S E) env ∧
    Realize M.sets (mainPrefixIdentityFormula E) env ∧
    Realize M.sets (mainPrefixCompositionFormula E) env) ↔ _
  rw [BoundedFormula.realize_ordinalFormula M T env members, ← ordinalSetProperty_iff,
    M.realize_functionGraphOnFormula unions T S env members,
    M.realize_functionGraphOnFormula unions J E env members,
    M.realize_mainPrefixStagesFormula pairing unions powers separation collection K Labels C D rD N S env members omega ordinal,
    M.realize_mainPrefixTransitionsFormula pairing unions powers separation collection K Labels C D rD N S E env members omega ordinal,
    M.realize_mainPrefixIdentityFormula E env members,
    M.realize_mainPrefixCompositionFormula E env members, pairs]
  constructor
  · rintro ⟨ord, stages, transitions, valid, maps, self, comp⟩
    exact ⟨ord, stages, transitions, valid, maps, self, comp⟩
  · intro code
    exact ⟨code.ordinal, code.stages, code.transitions, code.stage_valid,
      code.transition_valid, code.identity, code.composition⟩

theorem realize_mainPrefixGraphFormula {n} (K Labels C D rD N T S E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixGraphFormula K Labels C D rD N T S E) env ↔
      MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (env T) (env S) (env E) := by
  rw [mainPrefixGraphFormula, realize_ex]
  constructor
  · rintro ⟨J, hJ, equation, body⟩
    have pairs := (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
      (extend J env) (Fin.cases hJ members)).1 equation
    exact (M.realize_mainPrefixGraphBodyFormula pairing unions powers separation collection
      K.succ Labels.succ C.succ D.succ rD.succ N.succ T.succ S.succ E.succ 0
      (extend J env) (Fin.cases hJ members) omega ordinal pairs).1 body
  · intro code
    have ground := M.chronologyPairs_mem pairing unions powers separation (members T)
    refine ⟨chronologyPairs (env T), ground, ?_, ?_⟩
    · exact (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
        (extend (chronologyPairs (env T)) env) (Fin.cases ground members)).2 rfl
    · exact (M.realize_mainPrefixGraphBodyFormula pairing unions powers separation collection
        K.succ Labels.succ C.succ D.succ rD.succ N.succ T.succ S.succ E.succ 0
        (extend (chronologyPairs (env T)) env) (Fin.cases ground members) omega ordinal rfl).2 code

end TransitiveGround

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixFormula K Labels C D rD N z) env ↔
      MainPrefixCode M (env K) (env Labels) (env C) (env D) (env rD) (env z) := by
  rw [mainPrefixFormula, realize_exBlock]
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      (Realize M.sets (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2)).toFormula
          (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
          (field 0) (field 1) (field 2)) (extendMany 3 f env)) ↔
      env z = mainPrefixCode (f 0) (f 1) (f 2) ∧
        MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 0) (f 1) (f 2) := by
    have mems := extendMany_members 3 f env ground members
    have tuple := BoundedFormula.realize_mainPrefixTupleFormula M
      (old z) (field 0) (field 1) (field 2) (extendMany 3 f env) mems
    have code := M.realize_mainPrefixGraphFormula pairing unions powers separation collection
      (old K) (old Labels) (old C) (old D) (old rD) (old N) (field 0) (field 1) (field 2)
      (extendMany 3 f env) mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)
    rw [tuple, code]
    simp only [old, field, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f 0, f 1, f 2, (actual f ground).1 recognized⟩
  · rintro ⟨T, S, E, encoded, code⟩
    have ground := M.mainPrefixCode_fields_mem (encoded ▸ members z)
    let f : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have fieldsGround : ∀ j, f j ∈ M.sets := Fin.cases ground.1 (Fin.cases ground.2.1 (fun _ => ground.2.2))
    exact ⟨f, fieldsGround, (actual f fieldsGround).2 ⟨encoded, code⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem code_valid : MainPrefixCode M K Labels C D rD run.code :=
  ⟨run.indices, run.stageGraph, run.transitionGraph, rfl, run.graph_code⟩

end GroundMainPrefix

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_mainPrefixCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.mainPrefixCandidates B K Labels C D rD ↔
      z ∈ B ∧ MainPrefixCode M K Labels C D rD z := ZFSet.mem_sep

theorem mainPrefixCandidates_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {B K Labels C D rD : ZFSet.{u}} (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (ordinal : ordinalSetProperty K) : M.mainPrefixCandidates B K Labels C D rD ∈ M.sets := by
  let params := extend K (extend Labels (extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))))
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hK (Fin.cases hLabels (Fin.cases hC
    (Fin.cases hD (Fin.cases hrD (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))))
  have selected := M.separation_mem separation (mainPrefixFormula 1 2 3 4 5 6 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (mainPrefixFormula 1 2 3 4 5 6 0)
      (extend z params)) B = M.mainPrefixCandidates B K Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_mainPrefixCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_mainPrefixFormula pairing unions powers separation collection 1 2 3 4 5 6 0
      (extend z params) (Fin.cases (M.transitive hB hz) ground) rfl ordinal
  exact equal ▸ selected

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem validMainPrefixes_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) {Labels C D rD : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.validMainPrefixes Labels C D rD ∈ M.sets :=
  M.mainPrefixCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hLabels hC hD hrD ordinal

theorem mem_validMainPrefixes {Labels C D rD z : ZFSet.{u}} :
    z ∈ level.validMainPrefixes Labels C D rD ↔
      z ∈ level.carrier ∧ MainPrefixCode M K Labels C D rD z :=
  M.mem_mainPrefixCandidates level.carrier K Labels C D rD z

theorem prefix_mem_validMainPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    {Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (rank : ZFSet.rank run.code < ZFSet.rank K) : run.code ∈ level.validMainPrefixes Labels C D rD :=
  level.mem_validMainPrefixes.2 ⟨(level.membership _).2 ⟨run.code_ground, rank⟩, run.code_valid⟩

end GroundMainCandidateLevel
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_initialMainPrefixCandidate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) seed.source C,
          ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
            level.validMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
            run.code ∈ level.validMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            run.indices = natSetCode 2 ∧ run.code ∈ M.sets ∧ ZFSet.rank run.code < ZFSet.rank K ∧
            (run.linked 0).main = seed.source ∧ (run.linked 1).main = certificate.target ∧
            (run.linked 0).serial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            (run.linked 1).serial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            run.diagram.stage 0 = seed.source ∧ run.diagram.stage 1 = certificate.target ∧
            (∀ z, ZFSet.pair (ZFSet.pair (natSetCode 1) (natSetCode 0)) z ∈ run.transitionGraph ↔
              z = certificate.transition.map.code) ∧
            (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.points =
              certificate.transition.map.points ∧
            (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.actors =
              certificate.transition.map.actors := by
  dsimp only
  obtain ⟨level, seed, certificate, first, second, run, firstMain, secondMain,
    firstMember, secondMember, indices, ground, rank, firstLinked, secondLinked,
    stageZero, stageOne, _entryZero, _entryOne, entryTransition, points, actors⟩ :=
    M.exists_groundInitialTwoStageMainPrefix pairing unions powers separation
      collection infinite choice hK standard
  have conditions := standard.to_conditions pairing unions powers separation hK
  refine ⟨level, seed, certificate, run,
    level.validMainPrefixes_ground pairing unions powers separation collection infinite hK
      conditions.1 seed.source.stage.columns_ground seed.source.stage.columns_ground
      seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    level.prefix_mem_validMainPrefixes run rank, indices, ground, rank,
    ?_, ?_, ?_, ?_, stageZero, stageOne, entryTransition, points, actors⟩
  · exact firstLinked ▸ firstMain
  · exact secondLinked ▸ secondMain
  · exact firstLinked ▸ firstMember
  · exact secondLinked ▸ secondMember

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preservedMainPrefixFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (preservedMainPrefixFormula K Labels C D rD N z) env ↔
      PreservedMainPrefixCode M (env K) (env Labels) (env C) (env D) (env rD) (env z) := by
  rw [preservedMainPrefixFormula, realize_exBlock]
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      (Realize M.sets (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2)).toFormula
          (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
          (field 0) (field 1) (field 2)) (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixProfileGraphFormula (old K) (old Labels) (old C) (old D)
          (old rD) (old N) (field 1) (field 2)) (extendMany 3 f env)) ↔
      env z = mainPrefixCode (f 0) (f 1) (f 2) ∧
        MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 0) (f 1) (f 2) ∧
        MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 1) (f 2) := by
    have mems := extendMany_members 3 f env ground members
    have tuple := BoundedFormula.realize_mainPrefixTupleFormula M
      (old z) (field 0) (field 1) (field 2) (extendMany 3 f env) mems
    have code := M.realize_mainPrefixGraphFormula pairing unions powers separation collection
      (old K) (old Labels) (old C) (old D) (old rD) (old N) (field 0) (field 1) (field 2)
      (extendMany 3 f env) mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)
    have profiles := M.realize_mainPrefixProfileGraphFormula pairing unions powers separation collection
      (old K) (old Labels) (old C) (old D) (old rD) (old N) (field 1) (field 2)
      (extendMany 3 f env) mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)
    rw [tuple, code, profiles]
    simp only [old, field, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f 0, f 1, f 2, (actual f ground).1 recognized⟩
  · rintro ⟨T, S, E, encoded, code, preserved⟩
    have ground := M.mainPrefixCode_fields_mem (encoded ▸ members z)
    let f : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have fieldsGround : ∀ j, f j ∈ M.sets := Fin.cases ground.1 (Fin.cases ground.2.1 (fun _ => ground.2.2))
    exact ⟨f, fieldsGround, (actual f fieldsGround).2 ⟨encoded, code, preserved⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialPreservedMainPrefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) seed.source C,
          ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
            PreservedMainPrefixCode M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) run.code ∧
            run.PreservesOldProfiles ∧
            run.code ∈ level.validMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            run.indices = natSetCode 2 ∧ run.code ∈ M.sets ∧ ZFSet.rank run.code < ZFSet.rank K ∧
            run.diagram.stage 0 = seed.source ∧ run.diagram.stage 1 = certificate.target ∧
            (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.code =
              certificate.transition.map.code := by
  dsimp only
  obtain ⟨level, seed, certificate, run, _, member, indices, ground, rank,
    _, _, _, _, first, second, _entry, points, actors⟩ :=
    M.exists_initialMainPrefixCandidate pairing unions powers separation collection infinite choice hK standard
  have crossing : (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).PreservesOldProfiles := by
    unfold GroundChronologicalMainTransition.PreservesOldProfiles
    rw [points, first, second]
    exact certificate.oldProfilePreservation pairing unions powers separation infinite
      (M.groundPower seed.source.stage.carrier)
  have preserved := run.preservesOldProfiles_of_zero_one crossing
  have exactMap : (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.code =
      certificate.transition.map.code := congrArg₂ ZFSet.pair points actors
  exact ⟨level, seed, certificate, run, run.preserved_code preserved, preserved, member,
    indices, ground, rank, first, second, exactMap⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixRawCoveredAppend
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula SetRealization
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem mem_preservedMainPrefixCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.preservedMainPrefixCandidates B K Labels C D rD ↔
      z ∈ B ∧ PreservedMainPrefixCode M K Labels C D rD z := ZFSet.mem_sep

theorem preservedMainPrefixCandidates_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {B K Labels C D rD : ZFSet.{u}} (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (ordinal : ordinalSetProperty K) : M.preservedMainPrefixCandidates B K Labels C D rD ∈ M.sets := by
  let params := extend K (extend Labels (extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))))
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hK (Fin.cases hLabels (Fin.cases hC
    (Fin.cases hD (Fin.cases hrD (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))))
  have selected := M.separation_mem separation (preservedMainPrefixFormula 1 2 3 4 5 6 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (preservedMainPrefixFormula 1 2 3 4 5 6 0)
      (extend z params)) B = M.preservedMainPrefixCandidates B K Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_preservedMainPrefixCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_preservedMainPrefixFormula pairing unions powers separation collection 1 2 3 4 5 6 0
      (extend z params) (Fin.cases (M.transitive hB hz) ground) rfl ordinal
  exact equal ▸ selected

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem preservedMainPrefixes_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) {Labels C D rD : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.preservedMainPrefixes Labels C D rD ∈ M.sets :=
  M.preservedMainPrefixCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hLabels hC hD hrD ordinal

theorem mem_preservedMainPrefixes {Labels C D rD z : ZFSet.{u}} :
    z ∈ level.preservedMainPrefixes Labels C D rD ↔
      z ∈ level.carrier ∧ PreservedMainPrefixCode M K Labels C D rD z :=
  M.mem_preservedMainPrefixCandidates level.carrier K Labels C D rD z

theorem prefix_mem_preservedMainPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    {Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (preserved : run.PreservesOldProfiles)
    (rank : ZFSet.rank run.code < ZFSet.rank K) : run.code ∈ level.preservedMainPrefixes Labels C D rD :=
  level.mem_preservedMainPrefixes.2 ⟨(level.membership _).2 ⟨run.code_ground, rank⟩, run.preserved_code preserved⟩

end GroundMainCandidateLevel
end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_initialPreservedPrefixCandidate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) seed.source C,
          ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
            level.preservedMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
            run.code ∈ level.preservedMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            run.indices = natSetCode 2 ∧ run.PreservesOldProfiles ∧
            ZFSet.rank run.code < ZFSet.rank K ∧
            run.diagram.stage 0 = seed.source ∧ run.diagram.stage 1 = certificate.target ∧
            (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.code =
              certificate.transition.map.code := by
  dsimp only
  obtain ⟨level, seed, certificate, run, _, preserved, _, indices, _, rank, first, second, crossing⟩ :=
    M.exists_groundInitialPreservedMainPrefix pairing unions powers separation collection infinite choice hK standard
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  exact ⟨level, seed, certificate, run,
    level.preservedMainPrefixes_ground pairing unions powers separation collection infinite
      hK standard.1.1 hC hC seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    level.prefix_mem_preservedMainPrefixes run preserved rank, indices, preserved, rank, first, second, crossing⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainPrefixSelectedStepTotality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

theorem mainPrefixRecursionIndexCode_iff {Omega T S E : ZFSet.{u}} :
    MainPrefixRecursionIndexCode Omega (mainPrefixCode T S E) ↔ T ∈ Omega ∧ T ≠ ∅ := by
  constructor
  · rintro ⟨T', S', E', equal, member, nonempty⟩
    have same := (mainPrefixCode_inj.1 equal).1
    exact same.symm ▸ ⟨member, nonempty⟩
  · rintro ⟨member, nonempty⟩
    exact ⟨T, S, E, rfl, member, nonempty⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixRecursionIndexFormula {n} (Omega z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (mainPrefixRecursionIndexFormula Omega z) env ↔
      MainPrefixRecursionIndexCode (env Omega) (env z) := by
  rw [mainPrefixRecursionIndexFormula, realize_exBlock]
  have actual (fields : Fin 3 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :
      Realize M.sets (BoundedFormula.conj
        (BoundedFormula.mainPrefixTupleFormula (suffixIndex n 3 z)
          (prefixIndex n 3 0) (prefixIndex n 3 1) (prefixIndex n 3 2))
        (.conj (.mem (prefixIndex n 3 0) (suffixIndex n 3 Omega))
          (.neg (BoundedFormula.emptyFormula (prefixIndex n 3 0))))).toFormula
        (extendMany 3 fields env) ↔
      env z = mainPrefixCode (fields 0) (fields 1) (fields 2) ∧
        fields 0 ∈ env Omega ∧ fields 0 ≠ ∅ := by
    rw [BoundedFormula.realize_toFormula M _ _ (extendMany_members 3 fields env ground members)]
    simp only [BoundedFormula.Truth, BoundedFormula.truth_mainPrefixTupleFormula,
      BoundedFormula.truth_emptyFormula, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields 0, fields 1, fields 2, (actual fields ground).1 recognized⟩
  · rintro ⟨T, S, E, equal, member, nonempty⟩
    have ground := M.mainPrefixCode_fields_mem (equal ▸ members z)
    let fields : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have grounds : ∀ j, fields j ∈ M.sets :=
      Fin.cases ground.1 (Fin.cases ground.2.1 (fun _ => ground.2.2))
    exact ⟨fields, grounds, (actual fields grounds).2 ⟨equal, member, nonempty⟩⟩

end TransitiveGround

end

section
open SetFormula SetRealization
universe u v

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

theorem mem_recursionPrefixes {Omega Labels C D rD z : ZFSet.{u}} :
    z ∈ level.recursionPrefixes Omega Labels C D rD ↔
      z ∈ level.preservedMainPrefixes Labels C D rD ∧ MainPrefixRecursionIndexCode Omega z :=
  ZFSet.mem_sep

theorem recursionPrefixes_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K)
    {Omega Labels C D rD : ZFSet.{u}} (hOmega : Omega ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.recursionPrefixes Omega Labels C D rD ∈ M.sets := by
  have hB := level.preservedMainPrefixes_ground pairing unions powers separation collection infinite
    hK ordinal hLabels hC hD hrD
  let params : Fin 1 → ZFSet.{u} := fun _ => Omega
  have ground : ∀ j, params j ∈ M.sets := fun _ => hOmega
  have separated := M.separation_mem separation (mainPrefixRecursionIndexFormula 1 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (mainPrefixRecursionIndexFormula 1 0)
      (extend z params)) (level.preservedMainPrefixes Labels C D rD) =
      level.recursionPrefixes Omega Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, level.mem_recursionPrefixes]
    apply and_congr_right
    intro hz
    exact M.realize_mainPrefixRecursionIndexFormula 1 0 (extend z params)
      (Fin.cases (M.transitive hB hz) ground)
  exact equal ▸ separated

theorem prefix_mem_recursionPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    {Omega Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (preserved : run.PreservesOldProfiles) (rank : ZFSet.rank run.code < ZFSet.rank K)
    (indices : run.indices ∈ Omega) (nonempty : run.indices ≠ ∅) :
    run.code ∈ level.recursionPrefixes Omega Labels C D rD :=
  level.mem_recursionPrefixes.2 ⟨level.prefix_mem_preservedMainPrefixes run preserved rank,
    mainPrefixRecursionIndexCode_iff.2 ⟨indices, nonempty⟩⟩

end GroundMainCandidateLevel
end

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem exists_initialRecursionSeed_oai
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
          ∃ initial : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) pairing unions powers separation
              {i : Fin 2 // run.key i ∈ natSetCode 1},
            level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
            initial.code ∈ level.recursionPrefixes C C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            initial.indices = natSetCode 1 ∧ initial.PreservesOldProfiles ∧
            initial.code ∈ M.sets ∧ ZFSet.rank initial.code < ZFSet.rank K ∧
            initial.stageGraph = graphRestriction (natSetCode 1) run.stageGraph ∧
            initial.transitionGraph = graphRestriction (chronologyPairs (natSetCode 1)) run.transitionGraph ∧
            ∃ i, initial.key i = natSetCode 0 ∧ initial.diagram.stage i = seed.source := by
  dsimp only
  obtain ⟨level, seed, _, run, _, _, indices, preserved, rank, first, _, _⟩ :=
    M.exists_initialPreservedPrefixCandidate pairing unions powers separation collection infinite choice hK standard
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨initial, initialIndices, profiles, initialRank, stages, transitions, _, i, key, stage⟩ :=
    run.exists_initialRestriction indices preserved
      (conditions.rank_isLimit pairing unions powers separation infinite hK) rank
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have indexMember : initial.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite := by
    apply ((M.groundOmegaOne_spec pairing unions powers separation collection infinite).2.2.1 _).2
    refine ⟨initial.indices_ground, initial.indices_ordinal, ?_⟩
    rw [initialIndices]
    exact M.natSetCode_countable pairing unions powers separation infinite 1
  have nonempty : initial.indices ≠ ∅ := by
    rw [initialIndices]
    intro equal
    have member := (natSetCode_mem_iff 0 1).2 (by decide)
    rw [equal] at member
    exact ZFSet.notMem_empty _ member
  exact ⟨level, seed, run, initial,
    level.recursionPrefixes_ground pairing unions powers separation collection infinite hK standard.1.1
      hC hC hC seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    level.prefix_mem_recursionPrefixes initial profiles initialRank indexMember nonempty,
    initialIndices, profiles, initial.code_ground, initialRank, stages, transitions,
    i, key, stage.trans first⟩

end TransitiveGround

open SetFormula SetRealization
universe u v w

end PartitionPilot.Forcing

end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.exists_initialRecursionSeed_oai.{u}
