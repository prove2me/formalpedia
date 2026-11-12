-- Prove2me | solution 1 for OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T06:23:15.088896+00:00
-- url     : https://prove2.me/submissions/ac89bcff-716d-48f8-8fc9-e4bd4ab4b198

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_BinaryTiles
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation

open Attachment

universe u v

namespace Input

variable {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B} (g : Input P Q)

theorem cross_meet (a : A) (b : B) :
    g.order.meet (g.left.toFun a) (g.right.toFun b) = .inl (P.meet a (g.shadow b)) := by
  apply meet_eq g.data g.component_meets
  refine ⟨P.meet_le_left _ _, (g.old_below_represent _ b).mpr (P.meet_le_right _ _), ?_⟩
  intro x hx hy
  rcases g.left_ideal a x hx with ⟨c, rfl⟩
  exact P.le_meet hx ((g.old_below_represent c b).mp hy)

end Input

end PartitionPilot.Compression.RecursiveMaps.PrincipalAmalgamation



namespace PartitionPilot.Compression.RecursiveMaps.BinaryTiles

open Attachment PrincipalAmalgamation

universe u

variable {A : Type u} (P : MeetOrder A)

theorem separation_fixes (W x : A) (below : P.le x W) :
    (separation P W).right.toFun x = (separation P W).left.toFun x :=
  (separation P W).represent_old x below

theorem separation_cross_meet (W D X : A) (belowD : P.le W D) (belowX : P.le W X) :
    (separation P W).order.meet ((separation P W).right.toFun D)
      ((separation P W).left.toFun X) = (separation P W).left.toFun W := by
  rw [meet_comm, (separation P W).cross_meet]
  change Sum.inl (P.meet X (P.meet D W)) = Sum.inl W
  have dw : P.meet D W = W :=
    P.antisymm (P.meet_le_right _ _) (P.le_meet belowD (P.refl W))
  have xw : P.meet X W = W :=
    P.antisymm (P.meet_le_right _ _) (P.le_meet belowX (P.refl W))
  rw [dw, xw]

theorem compression_top (T K : A) (top : ∀ x, P.le x T)
    (S : MeetIso P (idealOrder P K)) :
    (compression P T K top S).right.toFun T =
      (compression P T K top S).left.toFun K := by
  rw [compression_identification]
  apply congrArg (compression P T K top S).left.toFun
  apply P.antisymm (S.toFun T).property
  have bound := (S.le_iff (S.inverse ⟨K, P.refl K⟩) T).mpr (top _)
  rw [S.right_inverse] at bound
  exact bound

end PartitionPilot.Compression.RecursiveMaps.BinaryTiles

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Models_CopyQuotient
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data

universe u v

variable {A : Type u} {I : Type v} {P : MeetOrder A} (d : Data P I)

theorem cross_meet (i j : I) (x y : A) :
    d.order.meet ((d.vertex i).toFun x) ((d.vertex j).toFun y) =
      (d.vertex i).toFun (P.meet x (d.part i j y)) :=
  d.meet_eq (d.cross_meet_spec i j x y)

end PartitionPilot.Compression.RecursiveMaps.CompatibleCopies.Data

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_RectangleTile
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.Rectangle.Input

universe u

variable {A : Type u} {P : MeetOrder A} (r : Input P)

theorem first_agrees (x : A) (below : P.le x r.C) :
    r.first.toFun x = r.root.toFun (r.g1.toFun x) :=
  (r.copies.exact_overlap .one .root x (r.g1.toFun x)).mpr ⟨below, rfl⟩

theorem second_agrees (x : A) (below : P.le x r.C) :
    r.second.toFun x = r.root.toFun (r.g2.toFun x) :=
  (r.copies.exact_overlap .two .root x (r.g2.toFun x)).mpr ⟨below, rfl⟩

theorem meet_D_C : P.meet r.D r.C = r.C :=
  P.antisymm (P.meet_le_right _ _) (P.le_meet r.C_le_D (P.refl _))

theorem meet_D_B : P.meet r.D r.B = r.B :=
  P.antisymm (P.meet_le_right _ _) (P.le_meet r.B_le_D (P.refl _))

theorem first_meet_root (x : A) :
    r.copies.order.meet (r.first.toFun r.D) (r.root.toFun x) =
      r.root.toFun (P.meet (r.g1.toFun r.C) x) := by
  rw [meet_comm r.copies.order]
  have eq := r.copies.cross_meet .root .one x r.D
  change r.copies.order.meet (r.root.toFun x) (r.first.toFun r.D) =
    r.root.toFun (P.meet x (r.g1.toFun (P.meet r.D r.C))) at eq
  rw [r.meet_D_C, meet_comm P x] at eq
  exact eq

theorem second_meet_root (x : A) :
    r.copies.order.meet (r.second.toFun r.D) (r.root.toFun x) =
      r.root.toFun (P.meet (r.g2.toFun r.C) x) := by
  rw [meet_comm r.copies.order]
  have eq := r.copies.cross_meet .root .two x r.D
  change r.copies.order.meet (r.root.toFun x) (r.second.toFun r.D) =
    r.root.toFun (P.meet x (r.g2.toFun (P.meet r.D r.C))) at eq
  rw [r.meet_D_C, meet_comm P x] at eq
  exact eq

theorem children_meet :
    r.copies.order.meet (r.first.toFun r.D) (r.second.toFun r.D) = r.first.toFun r.B := by
  have eq := r.copies.cross_meet .one .two r.D r.D
  change r.copies.order.meet (r.first.toFun r.D) (r.second.toFun r.D) =
    r.first.toFun (P.meet r.D (P.meet r.D r.B)) at eq
  rw [r.meet_D_B, r.meet_D_B] at eq
  exact eq

end PartitionPilot.Compression.RecursiveMaps.Rectangle.Input

end

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GluingHeights
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot



namespace Compression.RecursiveMaps.TileRequests

open Attachment
universe u
variable {A : Type u} (P : MeetOrder A)

namespace Request
variable {P}

theorem separation_agrees (T : A) (greatest : ∀ x, P.le x T) (W x : A) (below : P.le x W) :
    (((Request.separation W).tile T greatest).child ⟨()⟩).toFun x =
      ((Request.separation W).tile T greatest).root.toFun x :=
  BinaryTiles.separation_fixes P W x below

theorem compression_agrees (T : A) (greatest : ∀ x, P.le x T) (K : A)
    (copy : MeetIso P (idealOrder P K)) (x : A) :
    (((Request.compression K copy).tile T greatest).child ⟨()⟩).toFun x =
      ((Request.compression K copy).tile T greatest).root.toFun (copy.toFun x).val :=
  BinaryTiles.compression_identification P T K greatest copy x

end Request

end Compression.RecursiveMaps.TileRequests



end PartitionPilot

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_ExternalTranslation
attribute [-instance] _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Family.child_countable _root_.OAI.PartitionPilot.Compression.RecursiveMaps.TileRequests.Request.child_countable _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps



namespace TileRequests

open Attachment CosetGeometry
universe u
variable {A J : Type u} [Group J] {P : MeetOrder A}

namespace Family
variable {R : Type u} (f : Family P R) (a : OrderAction J P)

theorem transfer_child_root (w : External J f.Letters) (r : R) (j : f.Child r) (x y : A)
    (h : ((f.tile r).child j).toFun x = (f.tile r).root.toFun y) :
    (f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun x = (f.copy a w).toFun y := by
  rw [← f.child_identification, ← f.root_identification, h]

theorem transfer_child_root_meet (w : External J f.Letters) (r : R) (j : f.Child r) (x y z : A)
    (h : (f.tile r).order.meet (((f.tile r).child j).toFun x) ((f.tile r).root.toFun y) =
      (f.tile r).root.toFun z) :
    (f.gluedOrder a).meet ((f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun x)
      ((f.copy a w).toFun y) = (f.copy a w).toFun z := by
  rw [← f.child_identification, ← f.root_identification, ← f.root_identification,
    ← (f.placedTile a w r).map_meet, h]

theorem transfer_child_child_meet (w : External J f.Letters) (r : R)
    (j k : f.Child r) (x y z : A)
    (h : (f.tile r).order.meet (((f.tile r).child j).toFun x) (((f.tile r).child k).toFun y) =
      ((f.tile r).child j).toFun z) :
    (f.gluedOrder a).meet ((f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun x)
      ((f.copy a (w * generator J f.Letters ⟨r, k⟩)).toFun y) =
      (f.copy a (w * generator J f.Letters ⟨r, j⟩)).toFun z := by
  rw [← f.child_identification, ← f.child_identification, ← f.child_identification,
    ← (f.placedTile a w r).map_meet, h]

end Family

end TileRequests



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

end PartitionPilot.Forcing

end

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

theorem groundEligibleBatchAction_old_iff
    {P G r μ A Labels g x y : ZFSet.{u}} (hx : x ∈ P) :
    ZFSet.pair (ZFSet.pair g x) y ∈ M.groundEligibleBatchAction P G r μ A Labels ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ A :=
  taggedActionGraph_old_iff hx

end PartitionPilot.Forcing.TransitiveGround

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

end TransitiveGround

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

theorem externalRectangleCode_mem (P G r μ A c b d g h : ZFSet.{u}) :
    externalRectangleCode c b d g h ∈ externalRectangles P G r μ A ↔
      ExternalRectangleCode P G r μ A c b d g h := by
  rw [mem_externalRectangles]
  constructor
  · rintro ⟨c', b', d', g', h', equal, code⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := externalRectangleCode_inj.1 equal
    exact code
  · intro code
    exact ⟨c, b, d, g, h, rfl, code⟩

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

end PartitionPilot.Forcing.GroundCompressionState



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
open SetFormula
universe u

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)

theorem union_top_arguments_function :
    ZFSet.IsFunc I (algebra.union.fields 0) (constantFamilyGraph I τ) := by
  refine ⟨?_, (constantFamilyGraph_function I τ).2⟩
  intro z hz
  obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 ((constantFamilyGraph_function I τ).1 hz)
  have equal := ZFSet.mem_singleton.1 ha
  subst a
  exact ZFSet.pair_mem_prod.2 ⟨hi, state.union_original_subset algebra.union seed.top_mem⟩

theorem union_caps_function : ZFSet.IsFunc I (algebra.union.fields 0) (algebra.caps τ) :=
  familyEvaluationGraph_function algebra.function.to_isFunc (state.union_top_arguments_function algebra)
    (fun i f entry => (algebra.embedding i f entry).injection.function)

theorem union_cap_entry_iff {i f k : ZFSet.{u}} (map : ZFSet.pair i f ∈ algebra.maps) :
    ZFSet.pair i k ∈ algebra.caps τ ↔ ZFSet.pair τ k ∈ f := by
  have argument := (pair_mem_constantFamilyGraph I τ i τ).2
    ⟨(ZFSet.pair_mem_prod.1 (algebra.function.to_isFunc.1 map)).1, rfl⟩
  rw [GroundCompressionAlgebra.caps,
    familyEvaluationGraph_entry_iff algebra.function.to_isFunc (state.union_top_arguments_function algebra) map argument]
  exact ⟨fun h => h.2, fun h => ⟨(ZFSet.pair_mem_prod.1
    ((algebra.embedding i f map).injection.function.1 h)).2, h⟩⟩

end GroundCompressionState
end PartitionPilot.Forcing



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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_SmallTileHeightInputs
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression Compression.RecursiveMaps
universe u

theorem smallCompressionTileIso_entry {P r μ f : ZFSet.{u}}
    (meet : MeetOrderCode P r μ) (embedding : MeetEmbeddingCode P P r r μ μ f)
    (K : SetMembers P)
    (range : ∀ z, (∃ x ∈ P, ZFSet.pair x z ∈ f) ↔
      z ∈ P ∧ ZFSet.pair z (SetMembers.raw K) ∈ r) (x : SetMembers P) :
    ZFSet.pair (SetMembers.raw x)
      (SetMembers.raw ((smallCompressionTileIso meet embedding K range).toFun x).val) ∈ f :=
  embedding.smallValue_entry x

end PartitionPilot.Forcing



end

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
open SetRealization Compression Compression.RecursiveMaps
universe u

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)

theorem externalCopy_entry (i : SetMembers I) (x : SetMembers (completion.algebra.union.fields 0)) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw ((completion.externalCopy i).toFun x).val) ∈
      completion.externalMap i :=
  smallCompressionTileIso_entry _ _ _ _ x

variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))

theorem externalRectangle_fields (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    let rectangle := completion.externalRectangle group oldAction compression z
    externalRectangleCode (SetMembers.raw rectangle.C) (SetMembers.raw rectangle.B)
      (SetMembers.raw rectangle.D) (SetMembers.raw rectangle.first) (SetMembers.raw rectangle.second) =
        SetMembers.raw z := by
  have fields := (((externalRectangleParameters_spec z).2).lift_compression compression oldAction).toSmallActionRectangle_fields
    group completion.algebra.union.action completion.algebra.union.meet
  change externalRectangleCode _ _ _ _ _ = _
  dsimp only [externalRectangle]
  rw [fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, fields.2.2.2.2]
  exact (externalRectangleParameters_spec z).1.symm

end GroundCompressionCompletion

end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_CompressionRequestRealization
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PartitionPilot.Compression.RecursiveMaps.TileRequests.Family
open Attachment CosetGeometry
universe u
variable {A J R : Type u} [Group J] {P : MeetOrder A}
variable (f : Family P R) (a : OrderAction J P)

theorem generator_root_of_tile (r : R) (j : f.Child r) (x y : A)
    (equal : ((f.tile r).child j).toFun x = (f.tile r).root.toFun y) :
    f.translate a (generator J f.Letters ⟨r, j⟩) ((f.copy a 1).toFun x) =
      (f.copy a 1).toFun y := by
  rw [f.translate_copy, mul_one]
  simpa only [one_mul] using f.transfer_child_root a 1 r j x y equal

theorem generator_root_meet_of_tile (r : R) (j : f.Child r) (x y z : A)
    (equal : (f.tile r).order.meet (((f.tile r).child j).toFun x)
      ((f.tile r).root.toFun y) = (f.tile r).root.toFun z) :
    (f.gluedOrder a).meet
      (f.translate a (generator J f.Letters ⟨r, j⟩) ((f.copy a 1).toFun x))
      ((f.copy a 1).toFun y) = (f.copy a 1).toFun z := by
  rw [f.translate_copy, mul_one]
  simpa only [one_mul] using f.transfer_child_root_meet a 1 r j x y z equal

theorem generator_children_meet_of_tile (r : R) (j k : f.Child r) (x y z : A)
    (equal : (f.tile r).order.meet (((f.tile r).child j).toFun x)
      (((f.tile r).child k).toFun y) = ((f.tile r).child j).toFun z) :
    (f.gluedOrder a).meet
      (f.translate a (generator J f.Letters ⟨r, j⟩) ((f.copy a 1).toFun x))
      (f.translate a (generator J f.Letters ⟨r, k⟩) ((f.copy a 1).toFun y)) =
      f.translate a (generator J f.Letters ⟨r, j⟩) ((f.copy a 1).toFun z) := by
  simp only [f.translate_copy, mul_one]
  simpa only [one_mul] using f.transfer_child_child_meet a 1 r j k x y z equal

theorem generator_fixes_ideal_of_tile (r : R) (j : f.Child r) (W : A)
    (equal : ∀ x, P.le x W → ((f.tile r).child j).toFun x = (f.tile r).root.toFun x)
    (z : f.Node a) (lower : (f.gluedOrder a).le z ((f.copy a 1).toFun W)) :
    f.translate a (generator J f.Letters ⟨r, j⟩) z = z := by
  obtain ⟨x, rfl⟩ := (f.copy a 1).ideal W z lower
  exact f.generator_root_of_tile a r j x x (equal x (((f.copy a 1).le_iff x W).1 lower))

end PartitionPilot.Compression.RecursiveMaps.TileRequests.Family




namespace PartitionPilot.Forcing.GroundCompressionCompletion
open SetRealization Compression Compression.RecursiveMaps Attachment CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (compression : CompressionOriginalData P0 r0 μ0 A0 G
  (completion.algebra.union.fields 0) (completion.algebra.union.fields 1)
  (completion.algebra.union.fields 2) (completion.algebra.union.fields 12))
local notation "U" => completion.algebra.union.fields 0
local notation "P" => completion.algebra.union.meet.toSmallMeetOrder
local notation "family" => completion.externalFamily group oldAction compression
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet

theorem external_separation_fixes (W : SetMembers P0) :
    letI := group.toGroup
    let w : SetMembers U := SetMembers.ofMem (SetMembers.raw W) (compression.subset (SetMembers.raw_mem W))
    ∀ z, ((family).gluedOrder (action)).le z (((family).copy (action) 1).toFun w) →
      (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inl W), ⟨()⟩⟩) z = z := by
  let := group.toGroup
  dsimp only
  exact (family).generator_fixes_ideal_of_tile (action) (.inr (.inl W)) ⟨()⟩ _
    (fun x lower => TileRequests.Request.separation_agrees _ _ _ x lower)

theorem external_separation_meet (W : SetMembers P0) (x y : SetMembers U)
    (wx : ZFSet.pair (SetMembers.raw W) (SetMembers.raw x) ∈ completion.algebra.union.fields 1)
    (wy : ZFSet.pair (SetMembers.raw W) (SetMembers.raw y) ∈ completion.algebra.union.fields 1) :
    letI := group.toGroup
    ((family).gluedOrder (action)).meet
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inl W), ⟨()⟩⟩)
        (((family).copy (action) 1).toFun x)) (((family).copy (action) 1).toFun y) =
      ((family).copy (action) 1).toFun
        (SetMembers.ofMem (SetMembers.raw W) (compression.subset (SetMembers.raw_mem W))) := by
  let := group.toGroup
  exact (family).generator_root_meet_of_tile (action) (.inr (.inl W)) ⟨()⟩ x y _
    (BinaryTiles.separation_cross_meet P _ x y
      (by simpa only [MeetOrderCode.toSmallMeetOrder, SetMembers.raw_ofMem] using wx)
      (by simpa only [MeetOrderCode.toSmallMeetOrder, SetMembers.raw_ofMem] using wy))

theorem external_compression_restriction (i : SetMembers I) (x : SetMembers U) :
    letI := group.toGroup
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inl i, ⟨()⟩⟩)
      (((family).copy (action) 1).toFun x) =
        ((family).copy (action) 1).toFun ((completion.externalCopy i).toFun x).val := by
  let := group.toGroup
  exact (family).generator_root_of_tile (action) (.inl i) ⟨()⟩ x _
    (TileRequests.Request.compression_agrees _ _ _ _ x)

theorem external_compression_top (i : SetMembers I) :
    letI := group.toGroup
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inl i, ⟨()⟩⟩)
      (((family).copy (action) 1).toFun (SetMembers.ofMem τ completion.top_mem)) =
        ((family).copy (action) 1).toFun (completion.externalCap i) := by
  let := group.toGroup
  exact (family).generator_root_of_tile (action) (.inl i) ⟨()⟩ _ _
    (BinaryTiles.compression_top P _ _ (family).greatest _)

theorem external_rectangle_roots (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) (below : (P).le x (completion.externalRectangle group oldAction compression z).C) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction compression z
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
      (((family).copy (action) 1).toFun x) =
        ((family).copy (action) 1).toFun (((action).iso r.first).toFun x) ∧
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨true⟩⟩)
      (((family).copy (action) 1).toFun x) =
        ((family).copy (action) 1).toFun (((action).iso r.second).toFun x) := by
  let := group.toGroup
  dsimp only
  let r := (completion.externalRectangle group oldAction compression z).toInput
    (family).top (family).greatest
  exact ⟨(family).generator_root_of_tile (action) (.inr (.inr z)) ⟨false⟩ x _ (r.first_agrees x below),
    (family).generator_root_of_tile (action) (.inr (.inr z)) ⟨true⟩ x _ (r.second_agrees x below)⟩

theorem external_rectangle_children (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) (below : (P).le x (completion.externalRectangle group oldAction compression z).B) :
    letI := group.toGroup
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
      (((family).copy (action) 1).toFun x) =
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨true⟩⟩)
      (((family).copy (action) 1).toFun x) := by
  let := group.toGroup
  let r := (completion.externalRectangle group oldAction compression z).toInput
    (family).top (family).greatest
  simp only [TileRequests.Family.translate_copy, mul_one]
  have equal := congrArg ((family).placedTile (action) 1 (.inr (.inr z))).toFun
    ((r.children_intersection x x).2 ⟨below, rfl⟩)
  change ((family).placedTile (action) 1 (.inr (.inr z))).toFun
    ((((family).tile (.inr (.inr z))).child ⟨false⟩).toFun x) =
      ((family).placedTile (action) 1 (.inr (.inr z))).toFun
        ((((family).tile (.inr (.inr z))).child ⟨true⟩).toFun x) at equal
  simpa only [one_mul] using
    ((family).child_identification (action) 1 (.inr (.inr z)) ⟨false⟩ x).symm.trans
      (equal.trans ((family).child_identification (action) 1 (.inr (.inr z)) ⟨true⟩ x))

theorem external_rectangle_root_meets (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction compression z
    ((family).gluedOrder (action)).meet
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
        (((family).copy (action) 1).toFun r.D)) (((family).copy (action) 1).toFun x) =
      ((family).copy (action) 1).toFun ((P).meet (((action).iso r.first).toFun r.C) x) ∧
    ((family).gluedOrder (action)).meet
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨true⟩⟩)
        (((family).copy (action) 1).toFun r.D)) (((family).copy (action) 1).toFun x) =
      ((family).copy (action) 1).toFun ((P).meet (((action).iso r.second).toFun r.C) x) := by
  let := group.toGroup
  dsimp only
  let r := (completion.externalRectangle group oldAction compression z).toInput
    (family).top (family).greatest
  exact ⟨(family).generator_root_meet_of_tile (action) (.inr (.inr z)) ⟨false⟩ r.D x _ (r.first_meet_root x),
    (family).generator_root_meet_of_tile (action) (.inr (.inr z)) ⟨true⟩ r.D x _ (r.second_meet_root x)⟩

theorem external_rectangle_children_meet (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction compression z
    ((family).gluedOrder (action)).meet
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
        (((family).copy (action) 1).toFun r.D))
      ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨true⟩⟩)
        (((family).copy (action) 1).toFun r.D)) =
    (family).translate (action) (generator (SetMembers G) (family).Letters ⟨.inr (.inr z), ⟨false⟩⟩)
      (((family).copy (action) 1).toFun r.B) := by
  let := group.toGroup
  dsimp only
  let r := (completion.externalRectangle group oldAction compression z).toInput
    (family).top (family).greatest
  exact (family).generator_children_meet_of_tile (action) (.inr (.inr z)) ⟨false⟩ ⟨true⟩ r.D r.D r.B r.children_meet

end PartitionPilot.Forcing.GroundCompressionCompletion

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
include pairing unions powers separation hP hG hr hμ hA hLabels

theorem union_map_target
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i f a c : ZFSet.{u}} (indexed : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (target : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) :
    ZFSet.pair a c ∈ f := by
  obtain ⟨old, oldEntry⟩ := state.inputs.maps.total (algebra.function.pair_source indexed)
  have indexedOld : ZFSet.pair i old ∈ (M.initialCompressionData P G r μ A Labels).Maps := by
    simpa only [initialData] using oldEntry
  have top : ∀ x ∈ P, ZFSet.pair x τ ∈ r := by
    simpa only [initialData, TransitiveGround.initialCompressionData] using state.invariant.top
  have base := (M.groundInitialMap_cap_base pairing unions powers separation
    hP hG hr hμ hA hLabels state.inputs.group seed.originalAction seed.originalOrder
    seed.top_mem top indexedOld source target).2.2
  have ha : a ∈ P := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 source).1).2
  have haD : a ∈ state.data.D := by
    simp only [initialData]
    exact ha
  exact (algebra.restrict i f indexed 0 old oldEntry a haD c).2 base

theorem union_caps_common_target_meet
    (initialData : state.data = M.initialCompressionData P G r μ A Labels)
    {i j f g a a' c K L : ZFSet.{u}}
    (firstMap : ZFSet.pair i f ∈ algebra.maps) (secondMap : ZFSet.pair j g ∈ algebra.maps)
    (sourceI : ZFSet.pair i a ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (sourceJ : ZFSet.pair j a' ∈ literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (targetI : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (targetJ : ZFSet.pair j c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (capI : ZFSet.pair τ K ∈ f) (capJ : ZFSet.pair τ L ∈ g) (different : i ≠ j)
    (firstStrict : ZFSet.pair K c ∉ algebra.union.fields 1)
    (secondStrict : ZFSet.pair L c ∉ algebra.union.fields 1) :
    ZFSet.pair (ZFSet.pair K L) c ∈ algebra.union.fields 2 := by
  have firstBase := state.union_map_target algebra pairing unions powers separation
    hP hG hr hμ hA hLabels initialData firstMap sourceI targetI
  have secondBase := state.union_map_target algebra pairing unions powers separation
    hP hG hr hμ hA hLabels initialData secondMap sourceJ targetJ
  have apart := state.union_initial_cap_separation algebra pairing unions powers separation
    hP hG hr hμ hA hLabels initialData firstMap secondMap sourceI sourceJ capI capJ
    firstBase secondBase different
  rcases apart with first | second | common
  · exact False.elim (firstStrict first)
  · exact False.elim (secondStrict second)
  · obtain ⟨z, capsMeet, basesMeet⟩ := common
    have hc := (ZFSet.pair_mem_prod.1
      ((algebra.embedding i f firstMap).injection.function.1 firstBase)).2
    have hz := (ZFSet.pair_mem_prod.1 (algebra.union.meet.operation.1 basesMeet)).2
    have equal := algebra.union.meet.order.antisymm z hz c hc
      (algebra.union.meet.lower_left c c z basesMeet)
      (algebra.union.meet.greatest c c z c hc basesMeet
        (algebra.union.meet.order.refl c hc) (algebra.union.meet.order.refl c hc))
    exact equal ▸ capsMeet

end PartitionPilot.Forcing.GroundCompressionState

namespace PartitionPilot.Forcing.GroundCompressionOrigin
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P r μ A τ I Sources Reps G m inv one T Filters Labels : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P r μ A τ I Sources Reps G m inv one T Filters)
variable (algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T)

include origin in
theorem union_caps_common_target_meet
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (initialData : initial = M.initialCompressionData P G r μ A Labels)
    (initialSources : Sources = literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    {i j c K L : ZFSet.{u}}
    (capI : ZFSet.pair i K ∈ algebra.caps τ) (capJ : ZFSet.pair j L ∈ algebra.caps τ)
    (targetI : ZFSet.pair i c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (targetJ : ZFSet.pair j c ∈ literalTaskTargetGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (different : i ≠ j) (firstStrict : ZFSet.pair K c ∉ algebra.union.fields 1)
    (secondStrict : ZFSet.pair L c ∉ algebra.union.fields 1) :
    ZFSet.pair (ZFSet.pair K L) c ∈ algebra.union.fields 2 := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  have hi := (ZFSet.pair_mem_prod.1 ((state.union_caps_function algebra).1 capI)).1
  have hj := (ZFSet.pair_mem_prod.1 ((state.union_caps_function algebra).1 capJ)).1
  obtain ⟨f, indexedI⟩ := algebra.function.total hi
  obtain ⟨g, indexedJ⟩ := algebra.function.total hj
  obtain ⟨a, sourceI, _⟩ := seed.sources.2 i hi
  obtain ⟨a', sourceJ, _⟩ := seed.sources.2 j hj
  exact state.union_caps_common_target_meet algebra pairing unions powers separation
    hP hG hr hμ hA hLabels initialData indexedI indexedJ
    (initialSources ▸ sourceI) (initialSources ▸ sourceJ) targetI targetJ
    ((state.union_cap_entry_iff algebra indexedI).1 capI)
    ((state.union_cap_entry_iff algebra indexedJ).1 capJ) different firstStrict secondStrict

end PartitionPilot.Forcing.GroundCompressionOrigin

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Definability_ExternalRequestGraphCoordinates
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "family" => completion.externalFamily group oldAction data.original
local notation "letters" => completion.externalFamilyLetterPresentation group oldAction data.original
local notation "s" => completion.externalFamilyGroupPresentation group oldAction data.original
  pairing unions powers separation infinite hG data.words.letters_ground
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "generators" => M.externalChildGenerators G
  (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one

include data group oldAction pairing unions powers separation infinite hG in
theorem request_generator_value :
    letI := group.toGroup
    ∀ (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
      (j : (family).Child r) k,
      ZFSet.pair ((letters).encode ⟨r,j⟩) k ∈ generators ↔
        k = (s).encode (generator (SetMembers G) (family).Letters ⟨r,j⟩) := by
  let := group.toGroup
  intro r j k
  rw [completion.externalFamilyGroupPresentation_generators group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground]
  constructor
  · intro entry
    obtain ⟨v, equal⟩ := ((letters).mem_graph (s) (generator (SetMembers G) (family).Letters) _).1 entry
    have parts := ZFSet.pair_inj.1 equal
    have same := (letters).injective parts.1
    simpa only [same] using parts.2.symm
  · rintro rfl
    exact ((letters).pair_mem_graph (s) _ _ _).2 rfl

include data group oldAction pairing unions powers separation infinite hG in
theorem request_generator_action :
    letI := group.toGroup
    ∀ (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
      (j : (family).Child r) k,
      ZFSet.pair ((letters).encode ⟨r,j⟩) k ∈ generators →
      ∀ x y, ZFSet.pair (ZFSet.pair k ((q).encode x)) ((q).encode y) ∈
          completion.externalPointAction P0 r0 μ0 A0 ↔
        (family).translate (action) (generator (SetMembers G) (family).Letters ⟨r,j⟩) x = y := by
  let := group.toGroup
  intro r j k entry x y
  rw [(data.request_generator_value group oldAction pairing unions powers separation infinite hG r j k).1 entry]
  exact (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.2.1 _ x y

include data group oldAction pairing unions powers separation infinite hG in
theorem request_action_value :
    letI := group.toGroup
    ∀ (r : ExternalRequestIndex I P0 (externalRectangles P0 G r0 μ0 A0))
      (j : (family).Child r) k,
      ZFSet.pair ((letters).encode ⟨r,j⟩) k ∈ generators →
      ∀ x y, ZFSet.pair (ZFSet.pair k ((q).encode x)) y ∈
          completion.externalPointAction P0 r0 μ0 A0 ↔
        y = (q).encode ((family).translate (action) (generator (SetMembers G) (family).Letters ⟨r,j⟩) x) := by
  let := group.toGroup
  intro r j k entry x y
  constructor
  · intro acted
    have hy := ((pair_mem_flatCopyActionGraph _ _ _ _ _ _ _ _).1 acted).2.2.1
    rw [← data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG] at hy
    obtain ⟨y, rfl⟩ := ((q).mem_carrier _).1 hy
    exact congrArg (q).encode ((data.request_generator_action group oldAction pairing unions powers separation
      infinite hG r j k entry x y).1 acted).symm
  · rintro rfl
    exact (data.request_generator_action group oldAction pairing unions powers separation infinite hG r j k entry x _).2 rfl

end PartitionPilot.Forcing.GroundExternalGeometryInputs

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundFixedTopStep
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

open SetRealization
universe u

namespace ActionAgreementBelow
variable {Q H R ν B g h v : ZFSet.{u}}

theorem fixedTop_rectangleAgreement (meet : MeetOrderCode Q R ν) (function : ZFSet.IsFunc (ZFSet.prod H Q) Q B) (hv : v ∈ Q)
    (agreement : ActionAgreementBelow Q R B g h v) :
    ActionAgreementBelow (fixedTopCarrier Q) (fixedTopOrder Q R) (fixedTopAction H Q B) g h v := by
  intro x _ y _ lower
  have hx := fixedTopOrder_no_new_below meet.order hv lower
  rw [fixedTopAction_old_iff hx, fixedTopAction_old_iff hx]
  by_cases hy : y ∈ Q
  · exact agreement x hx y hy ((fixedTopOrder_old_iff hv).1 lower)
  · exact ⟨fun entry => (hy (ZFSet.pair_mem_prod.1 (function.1 entry)).2).elim,
      fun entry => (hy (ZFSet.pair_mem_prod.1 (function.1 entry)).2).elim⟩

end ActionAgreementBelow

namespace RectangleActorPairCode
variable {P μ A Q H R ν B e a c b d g h k l : ZFSet.{u}}

theorem fixedTop (code : RectangleActorPairCode P μ A Q H R ν B e a c b d g h k l)
    (meet : MeetOrderCode Q R ν) (function : ZFSet.IsFunc (ZFSet.prod H Q) Q B)
    (images : ∀ x y, ZFSet.pair x y ∈ e → y ∈ Q) :
    RectangleActorPairCode P μ A (fixedTopCarrier Q) H (fixedTopOrder Q R)
      (fixedTopMeet Q R) (fixedTopAction H Q B) e a c b d g h k l := by
  have root {g k} (old : RectangleRootMeetCode P μ A Q ν B e c d g k) :
      RectangleRootMeetCode P μ A (fixedTopCarrier Q) (fixedTopMeet Q R)
        (fixedTopAction H Q B) e c d g k := by
    intro x hx v hv w hw d' _ x' _ w' _ y _ acted met ed ex ew entry
    have hd' := images _ _ ed
    have hx' := images _ _ ex
    have hw' := images _ _ ew
    have entry := (fixedTopAction_old_iff hd').1 entry
    have hy := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    exact (fixedTopMeet_old_iff meet hy hx').2
      (old x hx v hv w hw d' hd' x' hx' w' hw' y hy acted met ed ex ew entry)
  refine ⟨⟨?_, ?_⟩, root code.2.1, root code.2.2.1, ?_⟩
  · intro c' _ g' hg' h' hh' ec ag ah
    have hc' := images _ _ ec
    have agrees := code.1.1 c' hc' g' hg' h' hh' ec ag ah
    exact ⟨ActionAgreementBelow.fixedTop_rectangleAgreement meet function hc' agrees.1,
      ActionAgreementBelow.fixedTop_rectangleAgreement meet function hc' agrees.2⟩
  · intro b' _ eb
    have hb' := images _ _ eb
    exact ActionAgreementBelow.fixedTop_rectangleAgreement meet function hb' (code.1.2 b' hb' eb)
  · intro b' _ d' _ y _ v _ z _ eb ed act1 act2 actB
    have hb' := images _ _ eb
    have hd' := images _ _ ed
    have act1 := (fixedTopAction_old_iff hd').1 act1
    have act2 := (fixedTopAction_old_iff hd').1 act2
    have actB := (fixedTopAction_old_iff hb').1 actB
    have hy := (ZFSet.pair_mem_prod.1 (function.1 act1)).2
    have hv := (ZFSet.pair_mem_prod.1 (function.1 act2)).2
    have hz := (ZFSet.pair_mem_prod.1 (function.1 actB)).2
    have cross := code.2.2.2 b' hb' d' hd' y hy v hv z hz eb ed act1 act2 actB
    exact ⟨(fixedTopMeet_old_iff meet hy hv).2 cross.1,
      (fixedTopAction_old_iff hb').2 cross.2⟩

end RectangleActorPairCode

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundProfiledExternalRequests
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "U" => completion.algebra.union.fields 0
local notation "generators" => M.externalChildGenerators G
  (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one

local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original)
  (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet) 1
local notation "ru" => completion.algebra.union.fields 1
local notation "au" => completion.algebra.union.fields 12
local notation "newAction" => completion.externalPointAction P0 r0 μ0 A0
local notation "newMeet" => completion.externalPointMeet P0 r0 μ0 A0
local notation "newOrder" => completion.externalPointOrder P0 r0 μ0 A0

include data group oldAction pairing unions powers separation infinite hG in
theorem separation_generator_fixes (W : SetMembers P0) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 1) (SetMembers.raw W)) (natSetCode 0)) k ∈ generators →
      ∀ z ∈ completion.externalPointCarrier P0 r0 μ0 A0,
        ZFSet.pair z ((q).encode ((root).toFun
          (SetMembers.ofMem (SetMembers.raw W) (data.original.subset (SetMembers.raw_mem W))))) ∈ newOrder →
        ZFSet.pair (ZFSet.pair k z) z ∈ newAction := by
  let := group.toGroup
  intro k gen z hz lower
  rw [← data.externalPointPresentation_carrier group oldAction pairing unions powers separation infinite hG] at hz
  obtain ⟨z, rfl⟩ := ((q).mem_carrier _).1 hz
  apply (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inr (.inl W)) ⟨()⟩ k gen z z).2
  exact completion.external_separation_fixes group oldAction data.original W z
    (((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).1 _ _).1 lower)

include data group oldAction pairing unions powers separation infinite hG in
theorem separation_generator_meet (W : SetMembers P0) (x y : SetMembers U)
    (wx : ZFSet.pair (SetMembers.raw W) (SetMembers.raw x) ∈ ru)
    (wy : ZFSet.pair (SetMembers.raw W) (SetMembers.raw y) ∈ ru) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 1) (SetMembers.raw W)) (natSetCode 0)) k ∈ generators →
      ∀ z, ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x))) z ∈ newAction →
        ZFSet.pair (ZFSet.pair z ((q).encode ((root).toFun y)))
          ((q).encode ((root).toFun (SetMembers.ofMem (SetMembers.raw W)
            (data.original.subset (SetMembers.raw_mem W))))) ∈ newMeet := by
  let := group.toGroup
  intro k gen z acted
  rw [(data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inl W)) ⟨()⟩ k gen _ z).1 acted]
  exact ((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.1 _ _ _).2
    (completion.external_separation_meet group oldAction data.original W x y wx wy)

include data group oldAction pairing unions powers separation infinite hG in
theorem compression_generator_restriction (i : SetMembers I) (x y : SetMembers U)
    (map : ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ completion.externalMap i) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x))) ((q).encode ((root).toFun y)) ∈ newAction := by
  let := group.toGroup
  intro k gen
  apply (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inl i) ⟨()⟩ k gen _ _).2
  have equal : ((completion.externalCopy i).toFun x).val = y := by
    apply SetMembers.raw_injective U
    exact (show FunctionGraphOn U (completion.externalMap i) from
      ⟨U, (completion.algebra.embedding _ _ (completion.externalMap_entry i)).injection.function⟩).unique
      (completion.externalCopy_entry i x) map
  rw [completion.external_compression_restriction group oldAction data.original, equal]

include data group oldAction pairing unions powers separation infinite hG in
theorem compression_generator_top (i : SetMembers I) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun (SetMembers.ofMem τ completion.top_mem))))
        ((q).encode ((root).toFun (completion.externalCap i))) ∈ newAction := by
  let := group.toGroup
  intro k gen
  exact (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inl i) ⟨()⟩ k gen _ _).2 (completion.external_compression_top group oldAction data.original i)

include data group oldAction pairing unions powers separation infinite hG in
theorem compression_generator_agreement (i : SetMembers I) {a g : ZFSet.{u}}
    (source : ZFSet.pair (SetMembers.raw i) a ∈ Sources)
    (rep : ZFSet.pair (SetMembers.raw i) g ∈ Reps)
    (x y : SetMembers U) (lower : ZFSet.pair (SetMembers.raw x) a ∈ ru)
    (acted : ZFSet.pair (ZFSet.pair g (SetMembers.raw x)) (SetMembers.raw y) ∈ au) :
    letI := group.toGroup
    ∀ k, ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x))) ((q).encode ((root).toFun y)) ∈ newAction := by
  let := group.toGroup
  exact data.compression_generator_restriction group oldAction pairing unions powers separation infinite hG i x y
    ((completion.source_agreement _ _ _ _ _ _ (completion.externalMap_entry i) source rep lower).2 acted)

end GroundExternalGeometryInputs

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "U" => completion.algebra.union.fields 0
local notation "generators" => M.externalChildGenerators G
  (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one

local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original)
  (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet) 1
local notation "newAction" => completion.externalPointAction P0 r0 μ0 A0
local notation "newMeet" => completion.externalPointMeet P0 r0 μ0 A0
local notation "P" => completion.algebra.union.meet.toSmallMeetOrder

include data group oldAction pairing unions powers separation infinite hG in
theorem rectangle_generators_roots (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) (below : (P).le x (completion.externalRectangle group oldAction data.original z).C) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction data.original z
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x)))
        ((q).encode ((root).toFun (((action).iso r.first).toFun x))) ∈ newAction ∧
      ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun x)))
        ((q).encode ((root).toFun (((action).iso r.second).toFun x))) ∈ newAction := by
  let := group.toGroup
  dsimp only
  intro k l gen1 gen2
  have laws := completion.external_rectangle_roots group oldAction data.original z x below
  exact ⟨(data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ _).2 laws.1,
    (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ _).2 laws.2⟩

include data group oldAction pairing unions powers separation infinite hG in
theorem rectangle_generators_agree (z : SetMembers (externalRectangles P0 G r0 μ0 A0))
    (x : SetMembers U) (below : (P).le x (completion.externalRectangle group oldAction data.original z).B) :
    letI := group.toGroup
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ∀ y v, ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun x))) y ∈ newAction →
        ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun x))) v ∈ newAction → y = v := by
  let := group.toGroup
  intro k l gen1 gen2 y v act1 act2
  rw [(data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ y).1 act1,
    (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ v).1 act2]
  exact congrArg (q).encode (completion.external_rectangle_children group oldAction data.original z x below)

include data group oldAction pairing unions powers separation infinite hG in
theorem rectangle_generators_root_meets (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) (x : SetMembers U) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction data.original z
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ∀ y v, ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun r.D))) y ∈ newAction →
        ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun r.D))) v ∈ newAction →
        ZFSet.pair (ZFSet.pair y ((q).encode ((root).toFun x)))
          ((q).encode ((root).toFun ((P).meet (((action).iso r.first).toFun r.C) x))) ∈ newMeet ∧
        ZFSet.pair (ZFSet.pair v ((q).encode ((root).toFun x)))
          ((q).encode ((root).toFun ((P).meet (((action).iso r.second).toFun r.C) x))) ∈ newMeet := by
  let := group.toGroup
  dsimp only
  intro k l gen1 gen2 y v act1 act2
  rw [(data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ y).1 act1,
    (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ v).1 act2]
  have laws := completion.external_rectangle_root_meets group oldAction data.original z x
  have meet := (data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.1
  exact ⟨(meet _ _ _).2 laws.1, (meet _ _ _).2 laws.2⟩

include data group oldAction pairing unions powers separation infinite hG in
theorem rectangle_generators_meet (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction data.original z
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ∀ y v b, ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun r.D))) y ∈ newAction →
        ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun r.D))) v ∈ newAction →
        ZFSet.pair (ZFSet.pair k ((q).encode ((root).toFun r.B))) b ∈ newAction →
        ZFSet.pair (ZFSet.pair y v) b ∈ newMeet ∧
        ZFSet.pair (ZFSet.pair l ((q).encode ((root).toFun r.B))) b ∈ newAction := by
  let := group.toGroup
  dsimp only
  intro k l gen1 gen2 y v b act1 act2 actB
  rw [(data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ y).1 act1,
    (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ v).1 act2,
    (data.request_action_value group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨false⟩ k gen1 _ b).1 actB]
  refine ⟨((data.externalGeometry_entries group oldAction pairing unions powers separation infinite hG).2.1 _ _ _).2
    (completion.external_rectangle_children_meet group oldAction data.original z), ?_⟩
  apply (data.request_generator_action group oldAction pairing unions powers separation infinite hG
    (.inr (.inr z)) ⟨true⟩ l gen2 _ _).2
  exact (completion.external_rectangle_children group oldAction data.original z _ ((P).refl _)).symm

end GroundExternalGeometryInputs

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets)
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "U" => completion.algebra.union.fields 0

local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original)
  (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet) 1
local notation "identityCopy" => completion.externalCopyGraph P0 r0 μ0 A0
  (M.externalGroupIdentity G (externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)) m one)

include data group oldAction pairing unions powers separation infinite hG in
theorem external_identity_copy_value :
    letI := group.toGroup
    ∀ (x : SetMembers U) y, ZFSet.pair (SetMembers.raw x) y ∈ identityCopy ↔
      y = (q).encode ((root).toFun x) := by
  let := group.toGroup
  intro x y
  rw [completion.externalFamilyGroupPresentation_identity group oldAction data.original
    pairing unions powers separation infinite hG data.words.letters_ground,
    data.externalCopyGraph_eq_graph group oldAction pairing unions powers separation infinite hG]
  constructor
  · intro entry
    obtain ⟨v, equal⟩ := ((SetMembers.presentation U).mem_graph (q) (root).toFun _).1 entry
    have parts := ZFSet.pair_inj.1 equal
    have same := (SetMembers.presentation U).injective parts.1
    simpa only [same] using parts.2.symm
  · rintro rfl
    exact ((SetMembers.presentation U).pair_mem_graph (q) _ _ _).2 rfl

end GroundExternalGeometryInputs

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P0 ∈ M.sets)
local notation "Q" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "letters" => externalChildLetters I P0 (externalRectangles P0 G r0 μ0 A0)
local notation "generators" => M.externalChildGenerators G letters m one
local notation "copyGraph" => completion.externalCopyGraph P0 r0 μ0 A0 (M.externalGroupIdentity G letters m one)
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "newAction" => completion.externalPointAction P0 r0 μ0 A0
local notation "newOrder" => completion.externalPointOrder P0 r0 μ0 A0
include data group oldAction pairing unions powers separation infinite hG hP

theorem rectangle_generators_full_ideals (z : SetMembers (externalRectangles P0 G r0 μ0 A0)) :
    letI := group.toGroup
    let r := completion.externalRectangle group oldAction data.original z
    ∀ k l,
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators →
      ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators →
      ∀ g' h' c' b',
      ZFSet.pair (SetMembers.raw r.first) g' ∈ M.externalOldInclusion G letters m one →
      ZFSet.pair (SetMembers.raw r.second) h' ∈ M.externalOldInclusion G letters m one →
      ZFSet.pair (SetMembers.raw r.C) c' ∈ copyGraph →
      ZFSet.pair (SetMembers.raw r.B) b' ∈ copyGraph →
      ActionAgreementBelow Q newOrder newAction k g' c' ∧
      ActionAgreementBelow Q newOrder newAction l h' c' ∧
      ActionAgreementBelow Q newOrder newAction k l b' := by
  let := group.toGroup
  dsimp only
  intro k l gen1 gen2 g' h' c' b' ag ah ec eb
  let r := completion.externalRectangle group oldAction data.original z
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have hk := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen1)).2
  have hl := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen2)).2
  have hg' := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 ag)).2
  have hh' := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 ah)).2
  have same {a b x v : ZFSet.{u}} (ha : a ∈ M.externalGroupCarrier G letters m one) (hb : b ∈ M.externalGroupCarrier G letters m one)
      (hx : x ∈ Q) (first : ZFSet.pair (ZFSet.pair a x) v ∈ newAction)
      (second : ZFSet.pair (ZFSet.pair b x) v ∈ newAction) (y : ZFSet.{u}) :
      ZFSet.pair (ZFSet.pair a x) y ∈ newAction ↔ ZFSet.pair (ZFSet.pair b x) y ∈ newAction := by
    obtain ⟨_, _, ua⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨ha, hx⟩)
    obtain ⟨_, _, ub⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hb, hx⟩)
    exact ⟨fun entry => ((ua y entry).trans (ua v first).symm).symm ▸ second,
      fun entry => ((ub y entry).trans (ub v second).symm).symm ▸ first⟩
  have atC (x' : ZFSet.{u}) (hx' : x' ∈ Q) (lower : ZFSet.pair x' c' ∈ newOrder) :
      ∀ y, (ZFSet.pair (ZFSet.pair k x') y ∈ newAction ↔ ZFSet.pair (ZFSet.pair g' x') y ∈ newAction) ∧
        (ZFSet.pair (ZFSet.pair l x') y ∈ newAction ↔ ZFSet.pair (ZFSet.pair h' x') y ∈ newAction) := by
    obtain ⟨x, hx, below, ex⟩ := ideal.ideal _ _ _ ec hx' lower
    let xu := SetMembers.ofMem x hx
    have eqX := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG xu x').1 (by simpa only [xu, SetMembers.raw_ofMem] using ex)
    have acts := data.rectangle_generators_roots group oldAction pairing unions powers separation infinite hG z xu (by
      change ZFSet.pair (SetMembers.raw xu) _ ∈ _
      simpa only [xu, SetMembers.raw_ofMem] using below) k l gen1 gen2
    rw [← eqX] at acts
    have old1 := (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet
      r.first xu (((action).iso r.first).toFun xu)).1 rfl
    have old2 := (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet
      r.second xu (((action).iso r.second).toFun xu)).1 rfl
    have copy1 := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
      (((action).iso r.first).toFun xu) _).2 rfl
    have copy2 := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
      (((action).iso r.second).toFun xu) _).2 rfl
    have acts1 := data.externalIdentityCopy_equivariant group oldAction pairing unions powers separation infinite hG ag ex copy1 (by simpa only [xu, SetMembers.raw_ofMem] using old1)
    have acts2 := data.externalIdentityCopy_equivariant group oldAction pairing unions powers separation infinite hG ah ex copy2 (by simpa only [xu, SetMembers.raw_ofMem] using old2)
    intro y
    exact ⟨same hk hg' hx' acts.1 acts1 y, same hl hh' hx' acts.2 acts2 y⟩
  refine ⟨fun x hx y _ lower => (atC x hx lower y).1,
    fun x hx y _ lower => (atC x hx lower y).2, ?_⟩
  intro x' hx' y _ lower
  obtain ⟨x, hx, below, ex⟩ := ideal.ideal _ _ _ eb hx' lower
  let xu := SetMembers.ofMem x hx
  have eqX := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG xu x').1 (by simpa only [xu, SetMembers.raw_ofMem] using ex)
  obtain ⟨u, act1, _⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hk, hx'⟩)
  obtain ⟨v, act2, _⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hl, hx'⟩)
  have equal := data.rectangle_generators_agree group oldAction pairing unions powers separation infinite hG z xu (by
    change ZFSet.pair (SetMembers.raw xu) _ ∈ _
    simpa only [xu, SetMembers.raw_ofMem] using below)
    k l gen1 gen2 u v (eqX ▸ act1) (eqX ▸ act2)
  exact same hk hl hx' act1 (equal.symm ▸ act2) y

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

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

end GroundMainTransition
end PartitionPilot.Forcing

end

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

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP

theorem externalOriginal_image_mem {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ completion.externalOriginalEmbedding P r μ A) :
    y ∈ completion.externalPointCarrier P r μ A := by
  have copied := ((completion.externalOriginalEmbedding_entry_iff P r μ A x y).1 entry).1
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP
  exact (ZFSet.pair_mem_prod.1
    ((geometry.copies _ data.group.group_code.identity_mem).injection.function.1 copied)).2

end GroundExternalGeometryInputs

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
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainSuccessorSeparation
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

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "e" => completion.externalOriginalEmbedding P r μ A

theorem externalBounded_separation_actor {W k : ZFSet.{u}} (hW : W ∈ P)
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 1) W) (natSetCode 0)) k ∈
      M.externalChildGenerators G letters m one) :
    SeparationActorCode P r (completion.externalBoundedCarrier P r μ A)
      (completion.externalBoundedOrder P r μ A) (completion.externalBoundedMeet P r μ A)
      (completion.externalBoundedAction P r μ A) e W k := by
  let := group.toGroup
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP
  intro w _ imageW
  have hw : w ∈ Q := data.externalOriginal_image_mem group action pairing unions powers separation infinite hG hP imageW
  have copiedW := ((completion.externalOriginalEmbedding_entry_iff P r μ A W w).1 imageW).1
  have eqW := (data.external_identity_copy_value group action pairing unions powers separation infinite hG
    (SetMembers.ofMem W (data.original.subset hW)) w).1 (by simpa only [SetMembers.raw_ofMem] using copiedW)
  constructor
  · intro z _ lower
    have hz : z ∈ Q := fixedTopOrder_no_new_below geometry.meet.order hw lower
    have oldLower := (fixedTopOrder_old_iff hw).1 lower
    rw [eqW] at oldLower
    exact (fixedTopAction_old_iff hz).2 (data.separation_generator_fixes group action
      pairing unions powers separation infinite hG (SetMembers.ofMem W hW) k
      (by simpa only [SetMembers.raw_ofMem] using generator) z hz
      (by simpa only [SetMembers.raw_ofMem] using oldLower))
  · intro x hx y hy x' _ y' _ z _ wx wy imageX imageY acted
    have hx' : x' ∈ Q := data.externalOriginal_image_mem group action pairing unions powers separation infinite hG hP imageX
    have hy' : y' ∈ Q := data.externalOriginal_image_mem group action pairing unions powers separation infinite hG hP imageY
    have oldAct := (fixedTopAction_old_iff hx').1 acted
    have hz : z ∈ Q := (ZFSet.pair_mem_prod.1 (geometry.action.function.1 oldAct)).2
    have eqX := (data.external_identity_copy_value group action pairing unions powers separation infinite hG
      (SetMembers.ofMem x (data.original.subset hx)) x').1
      (by simpa only [SetMembers.raw_ofMem] using
        ((completion.externalOriginalEmbedding_entry_iff P r μ A x x').1 imageX).1)
    have eqY := (data.external_identity_copy_value group action pairing unions powers separation infinite hG
      (SetMembers.ofMem y (data.original.subset hy)) y').1
      (by simpa only [SetMembers.raw_ofMem] using
        ((completion.externalOriginalEmbedding_entry_iff P r μ A y y').1 imageY).1)
    have wx' := (data.original.order W hW x hx).2 wx
    have wy' := (data.original.order W hW y hy).2 wy
    rw [eqX] at oldAct
    have meetEntry := data.separation_generator_meet group action pairing unions powers separation infinite hG
      (SetMembers.ofMem W hW) (SetMembers.ofMem x (data.original.subset hx))
      (SetMembers.ofMem y (data.original.subset hy))
      (by simpa only [SetMembers.raw_ofMem] using wx')
      (by simpa only [SetMembers.raw_ofMem] using wy') k
      (by simpa only [SetMembers.raw_ofMem] using generator) z oldAct
    apply (fixedTopMeet_old_iff geometry.meet hz hy').2
    simpa only [SetMembers.raw_ofMem, eqY, eqW] using meetEntry

theorem externalBounded_separation_fulfillment :
    SeparationFulfillmentCode P r (completion.externalBoundedCarrier P r μ A)
      (completion.externalBoundedOrder P r μ A) (completion.externalBoundedMeet P r μ A)
      (M.externalGroupCarrier G letters m one) (completion.externalBoundedAction P r μ A) e := by
  intro W hW
  have letter := (separation_child_iff I P (externalRectangles P G r μ A) W (natSetCode 0)).2 ⟨hW, rfl⟩
  obtain ⟨k, entry, _⟩ := data.generators_injection.function.2 _ letter
  have hk := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 entry)).2
  exact ⟨k, hk, data.externalBounded_separation_actor group action
    pairing unions powers separation infinite hG hP hW entry⟩

end GroundExternalGeometryInputs

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem separation_fulfillment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) :
    SeparationFulfillmentCode source.stage.carrier source.stage.order certificate.target.stage.carrier
      certificate.target.stage.order certificate.target.stage.meetGraph certificate.target.stage.actors
      certificate.target.stage.action certificate.transition.map.points := by
  obtain ⟨points, order, meet, actors, _, _, _, action, _⟩ := certificate.target_fields
  rw [points, order, meet, actors, action, certificate.point_graph]
  exact certificate.external.inputs.externalBounded_separation_fulfillment
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground

end GroundInitialMainSuccessorData
end PartitionPilot.Forcing

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundExternalRectangleFulfillment
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
local notation "U" => completion.algebra.union.fields 0
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "generators" => M.externalChildGenerators G letters m one
local notation "oldActors" => M.externalOldInclusion G letters m one
local notation "copyGraph" => completion.externalCopyGraph P r μ A (M.externalGroupIdentity G letters m one)
local notation "e" => completion.externalOriginalEmbedding P r μ A
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "action" => completion.algebra.union.action.toOrderAction group completion.algebra.union.meet
local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original) action 1
local notation "newAction" => completion.externalPointAction P r μ A
local notation "newOrder" => completion.externalPointOrder P r μ A
local notation "newMeet" => completion.externalPointMeet P r μ A
local notation "up" => completion.algebra.union.meet.toSmallMeetOrder
include data group oldAction pairing unions powers separation infinite hG hP

theorem external_rectangle_actor_pair {c b d g h k l : ZFSet.{u}}
    (eligible : ExternalRectangleCode P G r μ A c b d g h)
    (gen1 : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (externalRectangleCode c b d g h)) (natSetCode 0)) k ∈ generators)
    (gen2 : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (externalRectangleCode c b d g h)) (natSetCode 1)) l ∈ generators) :
    RectangleActorPairCode P μ A Q (M.externalGroupCarrier G letters m one)
      newOrder newMeet newAction e oldActors c b d g h k l := by
  let := group.toGroup
  let z := SetMembers.ofMem (externalRectangleCode c b d g h)
    ((externalRectangleCode_mem P G r μ A c b d g h).2 eligible)
  let rect := completion.externalRectangle group oldAction data.original z
  have tuple : externalRectangleCode (SetMembers.raw rect.C) (SetMembers.raw rect.B) (SetMembers.raw rect.D)
      (SetMembers.raw rect.first) (SetMembers.raw rect.second) = externalRectangleCode c b d g h := by
    simpa only [z, SetMembers.raw_ofMem] using (completion.externalRectangle_fields group oldAction data.original z)
  have fields := externalRectangleCode_inj.1 tuple
  have gen1' : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 0)) k ∈ generators := by
    simpa only [z, SetMembers.raw_ofMem] using gen1
  have gen2' : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 2) (SetMembers.raw z)) (natSetCode 1)) l ∈ generators := by
    simpa only [z, SetMembers.raw_ofMem] using gen2
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have hk := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen1)).2
  have hl := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen2)).2
  have copied {x x' : ZFSet.{u}} (image : ZFSet.pair x x' ∈ e) : ZFSet.pair x x' ∈ copyGraph :=
    ((completion.externalOriginalEmbedding_entry_iff P r μ A x x').1 image).1
  have value (u : SetMembers U) {x x' : ZFSet.{u}} (same : SetMembers.raw u = x)
      (image : ZFSet.pair x x' ∈ e) : x' = (q).encode ((root).toFun u) :=
    (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG u x').1
      (same.symm ▸ copied image)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro c' _ g' _ h' _ ec ag ah
    obtain ⟨b', eb, _⟩ := ideal.injection.function.2 _ (SetMembers.raw_mem rect.B)
    have laws := data.rectangle_generators_full_ideals group oldAction pairing unions powers separation infinite hG hP
      z k l gen1' gen2' g' h' c' b'
      (fields.2.2.2.1.symm ▸ ag) (fields.2.2.2.2.symm ▸ ah) (fields.1.symm ▸ copied ec) eb
    exact ⟨laws.1, laws.2.1⟩
  · intro b' _ eb
    obtain ⟨c', ec, _⟩ := ideal.injection.function.2 _ (SetMembers.raw_mem rect.C)
    obtain ⟨g', ag, _⟩ := data.old_inclusion_injection.function.2 _ (SetMembers.raw_mem rect.first)
    obtain ⟨h', ah, _⟩ := data.old_inclusion_injection.function.2 _ (SetMembers.raw_mem rect.second)
    exact (data.rectangle_generators_full_ideals group oldAction pairing unions powers separation infinite hG hP
      z k l gen1' gen2' g' h' c' b' ag ah ec (fields.2.1.symm ▸ copied eb)).2.2
  · intro x hx v hv w hw d' hd' x' _ w' _ y _ acted met ed ex ew acted'
    let xu := SetMembers.ofMem x (data.original.subset hx)
    let vu := SetMembers.ofMem v (data.original.subset hv)
    let wu := SetMembers.ofMem w (data.original.subset hw)
    have eqD := value rect.D fields.2.2.1 ed
    have eqX := value xu (by simp only [xu, SetMembers.raw_ofMem]) ex
    have eqW := value wu (by simp only [wu, SetMembers.raw_ofMem]) ew
    have actEq : (((action).iso rect.first).toFun rect.C) = vu :=
      (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet rect.first rect.C vu).2
        (by simpa only [fields.2.2.2.1, fields.1, vu, SetMembers.raw_ofMem] using
          (data.original.action g c eligible.1 v).2 acted)
    have meetEq : (up).meet vu xu = wu :=
      (completion.algebra.union.meet.toSmallMeetOrder_meet_eq_iff vu xu wu).2
        (by simpa only [vu, xu, wu, SetMembers.raw_ofMem] using (data.original.meet v hv x hx w).2 met)
    obtain ⟨other, otherAct, _⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hl, hd'⟩)
    rw [eqD] at acted' otherAct
    have laws := data.rectangle_generators_root_meets group oldAction pairing unions powers separation infinite hG
      z xu k l gen1' gen2' y other acted' otherAct
    dsimp only [rect] at actEq
    simpa only [actEq, meetEq, ← eqX, ← eqW] using laws.1
  · intro x hx v hv w hw d' hd' x' _ w' _ y _ acted met ed ex ew acted'
    let xu := SetMembers.ofMem x (data.original.subset hx)
    let vu := SetMembers.ofMem v (data.original.subset hv)
    let wu := SetMembers.ofMem w (data.original.subset hw)
    have eqD := value rect.D fields.2.2.1 ed
    have eqX := value xu (by simp only [xu, SetMembers.raw_ofMem]) ex
    have eqW := value wu (by simp only [wu, SetMembers.raw_ofMem]) ew
    have actEq : (((action).iso rect.second).toFun rect.C) = vu :=
      (completion.algebra.union.action.toOrderAction_eq_iff group completion.algebra.union.meet rect.second rect.C vu).2
        (by simpa only [fields.2.2.2.2, fields.1, vu, SetMembers.raw_ofMem] using
          (data.original.action h c eligible.1 v).2 acted)
    have meetEq : (up).meet vu xu = wu :=
      (completion.algebra.union.meet.toSmallMeetOrder_meet_eq_iff vu xu wu).2
        (by simpa only [vu, xu, wu, SetMembers.raw_ofMem] using (data.original.meet v hv x hx w).2 met)
    obtain ⟨other, otherAct, _⟩ := geometry.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hk, hd'⟩)
    rw [eqD] at acted' otherAct
    have laws := data.rectangle_generators_root_meets group oldAction pairing unions powers separation infinite hG
      z xu k l gen1' gen2' other y otherAct acted'
    dsimp only [rect] at actEq
    simpa only [actEq, meetEq, ← eqX, ← eqW] using laws.2
  · intro b' _ d' _ y _ v _ w _ eb ed act1 act2 actB
    have eqB := value rect.B fields.2.1 eb
    have eqD := value rect.D fields.2.2.1 ed
    rw [eqD] at act1 act2
    rw [eqB] at actB
    have laws := data.rectangle_generators_meet group oldAction pairing unions powers separation infinite hG
      z k l gen1' gen2' y v w act1 act2 actB
    dsimp only [rect] at eqB
    simpa only [← eqB] using laws

theorem externalBounded_rectangle_fulfillment :
    RectangleFulfillmentCode P G r μ A (completion.externalBoundedCarrier P r μ A)
      (M.externalGroupCarrier G letters m one) (completion.externalBoundedOrder P r μ A)
      (completion.externalBoundedMeet P r μ A) (completion.externalBoundedAction P r μ A) e oldActors := by
  intro c _ b _ d _ g _ h _ eligible
  have hz := (externalRectangleCode_mem P G r μ A c b d g h).2 eligible
  have letter1 := (rectangle_child_iff I P (externalRectangles P G r μ A)
    (externalRectangleCode c b d g h) (natSetCode 0)).2 ⟨hz, Or.inl rfl⟩
  have letter2 := (rectangle_child_iff I P (externalRectangles P G r μ A)
    (externalRectangleCode c b d g h) (natSetCode 1)).2 ⟨hz, Or.inr rfl⟩
  obtain ⟨k, gen1, _⟩ := data.generators_injection.function.2 _ letter1
  obtain ⟨l, gen2, _⟩ := data.generators_injection.function.2 _ letter2
  have hk := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen1)).2
  have hl := (ZFSet.pair_mem_prod.1 (data.generators_injection.function.1 gen2)).2
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  refine ⟨k, hk, l, hl, ?_⟩
  exact (data.external_rectangle_actor_pair group oldAction pairing unions powers separation infinite hG hP
    eligible gen1 gen2).fixedTop geometry.meet geometry.action.function
    (fun _ _ image => data.externalOriginal_image_mem group oldAction pairing unions powers separation infinite hG hP image)

end PartitionPilot.Forcing.GroundExternalGeometryInputs

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

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem rawFields_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    ∀ j, linked.rawFields j ∈ M.sets :=
  (Fin.cases (linked.main.stage.carrier_ground) (Fin.cases (linked.main.stage.order_ground) (Fin.cases (linked.main.stage.meet_ground) (Fin.cases (linked.main.stage.actors_ground) (Fin.cases (linked.main.stage.multiplication_ground) (Fin.cases (linked.main.stage.inverse_ground) (Fin.cases (linked.main.stage.identity_ground) (Fin.cases (linked.main.stage.action_ground) (Fin.cases (linked.main.stage.bottom_ground) (Fin.cases (linked.main.stage.top_ground) (Fin.cases (linked.main.stage.height_ground) (Fin.cases (linked.main.cutoff_ground) (Fin.cases (linked.serial.fields.time_ground) (Fin.cases (linked.serial.fields.bound_ground) (Fin.cases (linked.serial.fields.graph_ground 0) (Fin.cases (linked.serial.fields.graph_ground 1) (Fin.cases (linked.serial.fields.graph_ground 2) (Fin.cases (linked.serial.fields.graph_ground 3) (Fin.cases (linked.serial.fields.graph_ground 4) (Fin.cases (linked.serial.layer_bound_ground) (Fin.cases (linked.serial.layers_ground) (Fin.cases (linked.serial.fields.code_ground pairing) (Fin.cases (linked.main.stage.code_mem pairing) (fun _ => linked.serial.code_ground pairing))))))))))))))))))))))))

end GroundLinkedMainStage

end

end PartitionPilot.Forcing

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

end

universe u

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainTaskCapFulfillment
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

namespace GroundExternalGeometryInputs
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP
local notation "Q" => completion.externalBoundedCarrier P r μ A
local notation "copyGraph" => completion.externalCopyGraph P r μ A
  (M.externalGroupIdentity G (externalChildLetters I P (externalRectangles P G r μ A)) m one)

theorem boundedCapImages_ground (hI : I ∈ M.sets) :
    completion.boundedCapImages P r μ A ∈ M.sets := by
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP
  exact M.relationCompose_mem pairing unions powers separation hI (completion.algebra.union.ground 0)
    geometry.carrier_ground completion.caps_ground
    (geometry.copies_ground _ data.group.group_code.identity_mem)

theorem boundedCapImages_function :
    ZFSet.IsFunc I Q (completion.boundedCapImages P r μ A) := by
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP
  exact relationCompose_function_of_subset completion.caps_function
    (geometry.copies _ data.group.group_code.identity_mem).injection.function (fun _ h => h)

theorem boundedCapImages_entry_iff {i k' : ZFSet.{u}} :
    ZFSet.pair i k' ∈ completion.boundedCapImages P r μ A ↔
      ∃ k, ZFSet.pair i k ∈ completion.algebra.caps τ ∧ ZFSet.pair k k' ∈ copyGraph := by
  have geometry := data.externalBoundedGeometryData group action pairing unions powers separation infinite hG hP
  rw [GroundCompressionCompletion.boundedCapImages, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, k, _, cap, image⟩
    exact ⟨k, cap, image⟩
  · rintro ⟨k, cap, image⟩
    have bounds := ZFSet.pair_mem_prod.1 (completion.caps_function.1 cap)
    have target := ZFSet.pair_mem_prod.1
      ((geometry.copies _ data.group.group_code.identity_mem).injection.function.1 image)
    exact ⟨bounds.1, target.2, k, bounds.2, cap, image⟩

end GroundExternalGeometryInputs
end

namespace GroundExternalGeometryInputs
open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (group : GroupCode G m inv one) (oldAction : PosetActionCode G P m one r A)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP : P ∈ M.sets)
local notation "Q" => completion.externalPointCarrier P r μ A
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "generators" => M.externalChildGenerators G letters m one
local notation "oldActors" => M.externalOldInclusion G letters m one
local notation "e" => completion.externalOriginalEmbedding P r μ A
local notation "q" => data.externalPointPresentation group oldAction pairing unions powers separation infinite hG
local notation "root" => Compression.RecursiveMaps.TileRequests.Family.copy
  (completion.externalFamily group oldAction data.original)
  (completion.algebra.union.action.toOrderAction group completion.algebra.union.meet) 1
local notation "newAction" => completion.externalPointAction P r μ A
local notation "newOrder" => completion.externalPointOrder P r μ A
include data group oldAction pairing unions powers separation infinite hG hP

theorem bounded_compression_generator_agreement (i : SetMembers I) {a g k g' a' : ZFSet.{u}}
    (source : ZFSet.pair (SetMembers.raw i) a ∈ Sources)
    (representative : ZFSet.pair (SetMembers.raw i) g ∈ Reps)
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators)
    (actor : ZFSet.pair g g' ∈ oldActors) (image : ZFSet.pair a a' ∈ e) :
    ActionAgreementBelow (completion.externalBoundedCarrier P r μ A)
      (completion.externalBoundedOrder P r μ A) (completion.externalBoundedAction P r μ A) k g' a' := by
  let := group.toGroup
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have imageA := ((completion.externalOriginalEmbedding_entry_iff P r μ A a a').1 image).1
  have ha' := (ZFSet.pair_mem_prod.1 (ideal.injection.function.1 imageA)).2
  have hg := (ZFSet.pair_mem_prod.1 (data.old_inclusion_injection.function.1 actor)).1
  have agree : ActionAgreementBelow Q newOrder newAction k g' a' := by
    intro x' hx' z _ lower
    obtain ⟨x, hx, below, imageX⟩ := ideal.ideal _ _ _ imageA hx' lower
    obtain ⟨y, acted, _⟩ := completion.algebra.union.action.function.2 _ (ZFSet.pair_mem_prod.2 ⟨hg, hx⟩)
    have hy := (ZFSet.pair_mem_prod.1 (completion.algebra.union.action.function.1 acted)).2
    let xu := SetMembers.ofMem x hx
    let yu := SetMembers.ofMem y hy
    have eqX := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG xu x').1
      (by simpa only [xu, SetMembers.raw_ofMem] using imageX)
    have imageY := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG yu
      ((q).encode ((root).toFun yu))).2 rfl
    have first := data.compression_generator_agreement group oldAction pairing unions powers separation infinite hG
      i source representative xu yu
      (by simpa only [xu, SetMembers.raw_ofMem] using below)
      (by simpa only [xu, yu, SetMembers.raw_ofMem] using acted) k generator
    rw [← eqX] at first
    have second := data.externalIdentityCopy_equivariant group oldAction pairing unions powers separation infinite hG
      actor imageX imageY (by simpa only [yu, SetMembers.raw_ofMem] using acted)
    have function : FunctionGraphOn (ZFSet.prod (M.externalGroupCarrier G letters m one) Q) newAction :=
      ⟨Q, geometry.action.function⟩
    exact ⟨fun entry => (function.unique entry first).symm ▸ second,
      fun entry => (function.unique entry second).symm ▸ first⟩
  exact agree.fixedTop geometry.meet.order geometry.action ha'

theorem bounded_compression_generator_top_iff (i : SetMembers I) {k τ' v : ZFSet.{u}}
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) (SetMembers.raw i)) (natSetCode 0)) k ∈ generators)
    (imageTop : ZFSet.pair τ τ' ∈ e) :
    ZFSet.pair (ZFSet.pair k τ') v ∈ completion.externalBoundedAction P r μ A ↔
      ZFSet.pair (SetMembers.raw i) v ∈ completion.boundedCapImages P r μ A := by
  let := group.toGroup
  have geometry := data.externalGeometryData group oldAction pairing unions powers separation infinite hG hP
  have ideal := data.externalIdentityCopy_ideal group oldAction pairing unions powers separation infinite hG
  have copiedTop := ((completion.externalOriginalEmbedding_entry_iff P r μ A τ τ').1 imageTop).1
  have hτ' := (ZFSet.pair_mem_prod.1 (ideal.injection.function.1 copiedTop)).2
  have eqTop := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
    (SetMembers.ofMem τ completion.top_mem) τ').1
      (by simpa only [SetMembers.raw_ofMem] using copiedTop)
  have canonical := data.compression_generator_top group oldAction pairing unions powers separation infinite hG i k generator
  rw [← eqTop] at canonical
  have imageCap := (data.external_identity_copy_value group oldAction pairing unions powers separation infinite hG
    (completion.externalCap i) _).2 rfl
  have cap := (data.boundedCapImages_entry_iff group oldAction pairing unions powers separation infinite hG hP).2
    ⟨_, completion.externalCap_entry i, imageCap⟩
  have actionFunction : FunctionGraphOn (ZFSet.prod (M.externalGroupCarrier G letters m one) Q) newAction :=
    ⟨Q, geometry.action.function⟩
  have capFunction : FunctionGraphOn I (completion.boundedCapImages P r μ A) :=
    ⟨_, data.boundedCapImages_function group oldAction pairing unions powers separation infinite hG hP⟩
  change ZFSet.pair (ZFSet.pair k τ') v ∈ fixedTopAction (M.externalGroupCarrier G letters m one) Q newAction ↔ _
  rw [fixedTopAction_old_iff hτ']
  exact ⟨fun entry => (actionFunction.unique entry canonical).symm ▸ cap,
    fun entry => (capFunction.unique entry cap).symm ▸ canonical⟩

end GroundExternalGeometryInputs

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
include pairing unions powers separation infinite

theorem compressionCapImages_ground : certificate.compressionCapImages ∈ M.sets :=
  certificate.external.inputs.boundedCapImages_ground source.stage.group_code source.stage.action_code
    pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground
    certificate.indices_ground

theorem compressionCapImages_function :
    ZFSet.IsFunc (source.stage.compressionTasks Labels) certificate.target.stage.carrier
      certificate.compressionCapImages := by
  rw [certificate.target_fields.1]
  exact certificate.external.inputs.boundedCapImages_function source.stage.group_code source.stage.action_code
    pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground

theorem compressionCapImages_profile {i c v F K' c' v' : ZFSet.{u}}
    (cap : ZFSet.pair i K' ∈ certificate.compressionCapImages)
    (target : ZFSet.pair i c ∈ source.stage.compressionTargets Labels)
    (separator : ZFSet.pair i v ∈ source.stage.compressionSeparators Labels)
    (filter : ZFSet.pair i F ∈ source.stage.compressionFilters Labels)
    (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points)
    (imageV : ZFSet.pair v v' ∈ certificate.transition.map.points) :
    CodedCapProfile certificate.target.stage.carrier certificate.target.stage.order
      certificate.target.stage.meetGraph c' v' K'
      (relationImage F certificate.target.stage.carrier certificate.transition.map.points) := by
  let completion := certificate.compression.born.profiled.heighted.completion
  have geometry := certificate.external.inputs.externalBoundedGeometryData
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground
  obtain ⟨K, oldCap, capCopy⟩ := (certificate.external.inputs.boundedCapImages_entry_iff
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground).1 cap
  have profile := certificate.compression.born.profiled.profiles i c v K F oldCap target separator filter
  have filterBound := (ZFSet.mem_sep.1 (show ZFSet.pair i F ∈ literalTaskFieldGraph
    (source.stage.compressionTasks Labels) source.stage.carrier
    (M.groundRelations source.stage.carrier source.stage.carrier)
    (M.groundMeetFilters source.stage.carrier source.stage.order source.stage.meetGraph) Labels 4 from filter)).1
  have hF : F ∈ M.groundMeetFilters source.stage.carrier source.stage.order source.stage.meetGraph :=
    (ZFSet.pair_mem_prod.1 filterBound).2
  have subset := ((M.mem_groundMeetFilters _ _ _ F).1 hF).2.subset
  obtain ⟨carrierEq, orderEq, meetEq, _⟩ := certificate.target_fields
  rw [carrierEq, orderEq, meetEq, certificate.point_graph]
  rw [certificate.point_graph] at imageC imageV
  rw [completion.externalOriginal_filterImage_eq source.stage.carrier source.stage.order
    source.stage.meetGraph source.stage.action _ subset]
  exact (geometry.copies _ certificate.external.inputs.group.group_code.identity_mem).capProfile
    completion.algebra.union.meet geometry.meet completion.top_mem completion.top profile
    ((completion.externalOriginalEmbedding_entry_iff _ _ _ _ c c').1 imageC).1
    ((completion.externalOriginalEmbedding_entry_iff _ _ _ _ v v').1 imageV).1 capCopy

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem compressionCapImages_common_target_meet
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
    {i j c K' L' c' : ZFSet.{u}}
    (capI : ZFSet.pair i K' ∈ certificate.compressionCapImages)
    (capJ : ZFSet.pair j L' ∈ certificate.compressionCapImages)
    (targetI : ZFSet.pair i c ∈ source.stage.compressionTargets Labels)
    (targetJ : ZFSet.pair j c ∈ source.stage.compressionTargets Labels)
    (different : i ≠ j) (imageC : ZFSet.pair c c' ∈ certificate.transition.map.points) :
    ZFSet.pair (ZFSet.pair K' L') c' ∈ certificate.target.stage.meetGraph := by
  let completion := certificate.compression.born.profiled.heighted.completion
  have geometry := certificate.external.inputs.externalBoundedGeometryData
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground
  obtain ⟨K, oldI, copyI⟩ := (certificate.external.inputs.boundedCapImages_entry_iff
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground).1 capI
  obtain ⟨L, oldJ, copyJ⟩ := (certificate.external.inputs.boundedCapImages_entry_iff
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground).1 capJ
  have hi := (ZFSet.pair_mem_prod.1 (completion.caps_function.1 oldI)).1
  have hj := (ZFSet.pair_mem_prod.1 (completion.caps_function.1 oldJ)).1
  obtain ⟨_, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground
    source.stage.meet_ground source.stage.action_ground hLabels source.stage.meet
  obtain ⟨v, sepI, _⟩ := (fields 3).2.2 i hi
  obtain ⟨w, sepJ, _⟩ := (fields 3).2.2 j hj
  obtain ⟨F, filterI, _⟩ := (fields 4).2.2 i hi
  obtain ⟨H, filterJ, _⟩ := (fields 4).2.2 j hj
  have first := certificate.compression.born.profiled.profiles i c v K F oldI targetI sepI filterI
  have second := certificate.compression.born.profiled.profiles j c w L H oldJ targetJ sepJ filterJ
  have inherited := certificate.origin.union_caps_common_target_meet completion.algebra
    pairing unions powers separation source.stage.carrier_ground source.stage.actors_ground
    source.stage.order_ground source.stage.meet_ground source.stage.action_ground hLabels
    rfl rfl oldI oldJ targetI targetJ different first.cap_not_below_target second.cap_not_below_target
  rw [certificate.point_graph] at imageC
  rw [certificate.target_fields.2.2.1]
  exact (geometry.copies _ certificate.external.inputs.group.group_code.identity_mem).map_meet
    K L c K' L' c' inherited copyI copyJ
    ((completion.externalOriginalEmbedding_entry_iff _ _ _ _ c c').1 imageC).1

end GroundInitialMainSuccessorData

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
include pairing unions powers separation infinite hLabels

theorem taskCapFamily :
    TaskCapFamilyCode (source.stage.compressionTasks Labels) source.stage.carrier
      certificate.target.stage.carrier certificate.target.stage.order certificate.target.stage.meetGraph
      certificate.transition.map.points (source.stage.compressionTargets Labels)
      (source.stage.compressionSeparators Labels) (source.stage.compressionFilters Labels)
      (M.groundPower source.stage.carrier) certificate.compressionCapImages := by
  refine ⟨certificate.compressionCapImages_function pairing unions powers separation infinite, ?_, ?_⟩
  · intro i _ c _ v _ F _ K _ c' _ v' _ target separator filter cap imageC imageV
    exact certificate.compressionCapImages_profile pairing unions powers separation infinite
      cap target separator filter imageC imageV
  · intro i _ j _ c _ K _ L _ c' _ different targetI targetJ capI capJ imageC
    exact certificate.compressionCapImages_common_target_meet pairing unions powers separation infinite
      hLabels capI capJ targetI targetJ different imageC

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_GroundMainSuccessorCompressionActors
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
local notation "tasks" => source.stage.compressionTasks Labels
local notation "letters" => externalChildLetters tasks source.stage.carrier
  (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)
local notation "generators" => M.externalChildGenerators source.stage.actors letters source.stage.multiplication source.stage.identity
include certificate pairing unions powers separation infinite

theorem compression_generator_full_agreement {i a g k g' a' : ZFSet.{u}} (hi : i ∈ tasks)
    (sourceEntry : ZFSet.pair i a ∈ source.stage.compressionSources Labels)
    (representative : ZFSet.pair i g ∈ certificate.Reps)
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) i) (natSetCode 0)) k ∈ generators)
    (actor : ZFSet.pair g g' ∈ certificate.transition.map.actors)
    (image : ZFSet.pair a a' ∈ certificate.transition.map.points) :
    ActionAgreementBelow certificate.target.stage.carrier certificate.target.stage.order
      certificate.target.stage.action k g' a' := by
  rw [certificate.point_graph] at image
  rw [certificate.actor_graph] at actor
  rw [certificate.target_fields.1, certificate.target_fields.2.1,
    certificate.target_fields.2.2.2.2.2.2.2.1]
  exact certificate.external.inputs.bounded_compression_generator_agreement source.stage.group_code
    source.stage.action_code pairing unions powers separation infinite source.stage.actors_ground source.stage.carrier_ground
    (SetMembers.ofMem i hi) (by simpa only [SetMembers.raw_ofMem] using sourceEntry)
    (by simpa only [SetMembers.raw_ofMem] using representative)
    (by simpa only [SetMembers.raw_ofMem] using generator) actor image

theorem compression_generator_cap_iff {i k τ' v : ZFSet.{u}} (hi : i ∈ tasks)
    (generator : ZFSet.pair (ZFSet.pair (ZFSet.pair (natSetCode 0) i) (natSetCode 0)) k ∈ generators)
    (imageTop : ZFSet.pair source.stage.top τ' ∈ certificate.transition.map.points) :
    ZFSet.pair (ZFSet.pair k τ') v ∈ certificate.target.stage.action ↔
      ZFSet.pair i v ∈ certificate.compressionCapImages := by
  rw [certificate.point_graph] at imageTop
  rw [certificate.target_fields.2.2.2.2.2.2.2.1]
  simpa only [SetMembers.raw_ofMem, compressionCapImages] using certificate.external.inputs.bounded_compression_generator_top_iff
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground (SetMembers.ofMem i hi)
    (by simpa only [SetMembers.raw_ofMem] using generator) imageTop

theorem exists_compression_actor {i : ZFSet.{u}} (hi : i ∈ tasks) :
    ∃ k ∈ certificate.target.stage.actors,
      (∀ a g g' a', ZFSet.pair i a ∈ source.stage.compressionSources Labels →
        ZFSet.pair i g ∈ certificate.Reps → ZFSet.pair g g' ∈ certificate.transition.map.actors →
        ZFSet.pair a a' ∈ certificate.transition.map.points →
        ActionAgreementBelow certificate.target.stage.carrier certificate.target.stage.order
          certificate.target.stage.action k g' a') ∧
      ∀ τ' v, ZFSet.pair source.stage.top τ' ∈ certificate.transition.map.points →
        (ZFSet.pair (ZFSet.pair k τ') v ∈ certificate.target.stage.action ↔
          ZFSet.pair i v ∈ certificate.compressionCapImages) := by
  have letter := (compression_child_iff tasks source.stage.carrier
    (externalRectangles source.stage.carrier source.stage.actors source.stage.order source.stage.meetGraph source.stage.action)
    i (natSetCode 0)).2 ⟨hi, rfl⟩
  obtain ⟨k, generator, _⟩ := certificate.external.inputs.generators_injection.function.2 _ letter
  have hk := (ZFSet.pair_mem_prod.1 (certificate.external.inputs.generators_injection.function.1 generator)).2
  refine ⟨k, certificate.target_fields.2.2.2.1.symm ▸ hk, ?_, ?_⟩
  · intro a g g' a' sourceEntry representative actor image
    exact certificate.compression_generator_full_agreement pairing unions powers separation infinite hi
      sourceEntry representative generator actor image
  · intro τ' v image
    exact certificate.compression_generator_cap_iff pairing unions powers separation infinite hi generator image

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainCompressionActorCode
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

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
include pairing unions powers separation infinite

theorem compressionActorFulfillment :
    CompressionActorFulfillmentCode (source.stage.compressionTasks Labels)
      source.stage.carrier source.stage.actors certificate.target.stage.carrier
      certificate.target.stage.actors certificate.target.stage.order certificate.target.stage.action
      certificate.transition.map.points certificate.transition.map.actors
      (source.stage.compressionSources Labels) certificate.Reps source.stage.top
      certificate.compressionCapImages := by
  intro i hi
  obtain ⟨k, hk, agreement, top⟩ :=
    certificate.exists_compression_actor pairing unions powers separation infinite hi
  refine ⟨k, hk, ?_, ?_⟩
  · intro s _ g _ g' _ s' _ hs hg actor point
    exact agreement s g g' s' hs hg actor point
  · intro top' _ v _ image
    exact top top' v image

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end

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



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem rectangle_fulfillment
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) :
    RectangleFulfillmentCode source.stage.carrier source.stage.actors source.stage.order
      source.stage.meetGraph source.stage.action certificate.target.stage.carrier certificate.target.stage.actors
      certificate.target.stage.order certificate.target.stage.meetGraph certificate.target.stage.action
      certificate.transition.map.points certificate.transition.map.actors := by
  obtain ⟨points, order, meet, actors, _, _, _, action, _⟩ := certificate.target_fields
  rw [points, order, meet, actors, action, certificate.point_graph, certificate.actor_graph]
  exact certificate.external.inputs.externalBounded_rectangle_fulfillment
    source.stage.group_code source.stage.action_code pairing unions powers separation infinite
    source.stage.actors_ground source.stage.carrier_ground





variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
include pairing unions powers separation infinite hLabels

theorem successorOutputValues_ground : ∀ j, certificate.successorOutputValues j ∈ M.sets := by
  obtain ⟨_, _, _, _, fields⟩ := M.groundEligibleTaskFields pairing unions powers separation
    source.stage.carrier_ground source.stage.actors_ground source.stage.order_ground
    source.stage.meet_ground source.stage.action_ground hLabels source.stage.meet
  exact Fin.cases (source.stage.carrier_ground)
    (Fin.cases (certificate.target.stage.carrier_ground)
    (Fin.cases (source.stage.order_ground)
    (Fin.cases (certificate.target.stage.order_ground)
    (Fin.cases (source.stage.meet_ground)
    (Fin.cases (certificate.target.stage.meet_ground)
    (Fin.cases (source.stage.actors_ground)
    (Fin.cases (certificate.target.stage.actors_ground)
    (Fin.cases (source.stage.multiplication_ground)
    (Fin.cases (certificate.target.stage.multiplication_ground)
    (Fin.cases (source.stage.identity_ground)
    (Fin.cases (certificate.target.stage.identity_ground)
    (Fin.cases (source.stage.action_ground)
    (Fin.cases (certificate.target.stage.action_ground)
    (Fin.cases (source.stage.bottom_ground)
    (Fin.cases (certificate.target.stage.bottom_ground)
    (Fin.cases (source.stage.height_ground)
    (Fin.cases (certificate.target.stage.height_ground)
    (Fin.cases (certificate.transition.map.points_ground)
    (Fin.cases (certificate.transition.map.actors_ground)
    (Fin.cases (source.stage.top_ground)
    (Fin.cases (certificate.indices_ground)
    (Fin.cases (certificate.sources_ground)
    (Fin.cases ((fields 1).1)
    (Fin.cases ((fields 3).1)
    (Fin.cases (certificate.filters_ground)
    (Fin.cases (M.groundPower_mem powers source.stage.carrier_ground)
    (Fin.cases (certificate.representatives_ground)
    (Fin.cases (certificate.compressionCapImages_ground pairing unions powers separation infinite)
    (Fin.cases (certificate.target.stage.top_ground)
    ((fun j => Fin.elim0 j)))))))))))))))))))))))))))))))

theorem successorOutput : MainSuccessorOutputCode certificate.successorOutputValues := by
  refine ⟨certificate.transition.map.laws, ?_,
    certificate.separation_fulfillment pairing unions powers separation infinite,
    certificate.rectangle_fulfillment pairing unions powers separation infinite,
    certificate.oldProfilePreservation pairing unions powers separation infinite (M.groundPower source.stage.carrier),
    certificate.taskCapFamily pairing unions powers separation infinite hLabels,
    certificate.compressionActorFulfillment pairing unions powers separation infinite⟩
  intro x _ y _ image
  exact certificate.strict_new_top x y image

end PartitionPilot.Forcing.GroundInitialMainSuccessorData



namespace PartitionPilot.Forcing
universe u

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (linked : GroundLinkedMainStage M K Labels C D rD)

theorem rawFields_stage_projections :
    linked.rawFields 0 = linked.main.stage.carrier ∧
    linked.rawFields 1 = linked.main.stage.order ∧
    linked.rawFields 2 = linked.main.stage.meetGraph ∧
    linked.rawFields 3 = linked.main.stage.actors ∧
    linked.rawFields 4 = linked.main.stage.multiplication ∧
    linked.rawFields 5 = linked.main.stage.inverse ∧
    linked.rawFields 6 = linked.main.stage.identity ∧
    linked.rawFields 7 = linked.main.stage.action ∧
    linked.rawFields 8 = linked.main.stage.bottom ∧
    linked.rawFields 9 = linked.main.stage.top ∧
    linked.rawFields 10 = linked.main.stage.height :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GroundLinkedMainStage

namespace GroundInitialMainSuccessorData
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)

theorem successorOutputValues_projections :
    certificate.successorOutputValues 0 = source.stage.carrier ∧
    certificate.successorOutputValues 1 = certificate.target.stage.carrier ∧
    certificate.successorOutputValues 2 = source.stage.order ∧
    certificate.successorOutputValues 3 = certificate.target.stage.order ∧
    certificate.successorOutputValues 4 = source.stage.meetGraph ∧
    certificate.successorOutputValues 5 = certificate.target.stage.meetGraph ∧
    certificate.successorOutputValues 6 = source.stage.actors ∧
    certificate.successorOutputValues 7 = certificate.target.stage.actors ∧
    certificate.successorOutputValues 8 = source.stage.multiplication ∧
    certificate.successorOutputValues 9 = certificate.target.stage.multiplication ∧
    certificate.successorOutputValues 10 = source.stage.identity ∧
    certificate.successorOutputValues 11 = certificate.target.stage.identity ∧
    certificate.successorOutputValues 12 = source.stage.action ∧
    certificate.successorOutputValues 13 = certificate.target.stage.action ∧
    certificate.successorOutputValues 14 = source.stage.bottom ∧
    certificate.successorOutputValues 15 = certificate.target.stage.bottom ∧
    certificate.successorOutputValues 16 = source.stage.height ∧
    certificate.successorOutputValues 17 = certificate.target.stage.height ∧
    certificate.successorOutputValues 18 = certificate.transition.map.points ∧
    certificate.successorOutputValues 19 = certificate.transition.map.actors ∧
    certificate.successorOutputValues 20 = source.stage.top ∧
    certificate.successorOutputValues 21 = source.stage.compressionTasks Labels ∧
    certificate.successorOutputValues 22 = source.stage.compressionSources Labels ∧
    certificate.successorOutputValues 23 = source.stage.compressionTargets Labels ∧
    certificate.successorOutputValues 24 = source.stage.compressionSeparators Labels ∧
    certificate.successorOutputValues 25 = source.stage.compressionFilters Labels ∧
    certificate.successorOutputValues 26 = M.groundPower source.stage.carrier ∧
    certificate.successorOutputValues 27 = certificate.Reps ∧
    certificate.successorOutputValues 28 = certificate.compressionCapImages ∧
    certificate.successorOutputValues 29 = certificate.target.stage.top :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end GroundInitialMainSuccessorData
end PartitionPilot.Forcing



end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Geometry_GroundMainBoundTaskOutput
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundCompressionOrigin
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {P G r μ A Labels m inv one τ Reps : ZFSet.{u}}
local notation "I" => M.groundEligibleTasks P G r μ A Labels
local notation "R" => M.groundRelations P P
local notation "U" => M.groundMeetFilters P r μ
variable (origin : GroundCompressionOrigin M (M.initialCompressionData P G r μ A Labels)
  P r μ A τ (M.groundEligibleTasks P G r μ A Labels)
  (literalTaskSourceGraph (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels) Reps G m inv one
  (M.groundTaskTransport P G r μ A Labels)
  (literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels) P
    (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels))
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include origin pairing unions powers separation

theorem initial_representatives : TaskRepresentativesCode Reps I P G r A R U Labels := by
  refine ⟨origin.state.inputs.representatives, ?_⟩
  intro i g representative
  have hi := (ZFSet.pair_mem_prod.1 (origin.state.inputs.representatives.1 representative)).1
  obtain ⟨S, mapEntry⟩ := origin.state.inputs.maps.total hi
  have hI : I ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.indices
  have hP : P ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.carrier
  have hQs : constantFamilyGraph I P ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.spaces
  have hrs : constantFamilyGraph I r ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.relations
  have hAs : literalTaskSourceGraph I P R U Labels ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.anchors
  have hEs : literalTaskBaseGraph I P R U Labels ∈ M.sets := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using origin.state.ground.embeddings
  have actualMap : ZFSet.pair i S ∈ M.batchEmbeddingFamily I P
      (constantFamilyGraph I P) (constantFamilyGraph I r)
      (literalTaskSourceGraph I P R U Labels) (literalTaskBaseGraph I P R U Labels) := by
    simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using mapEntry
  have mapEq := (((M.batchEmbeddingFamily_spec pairing unions powers separation
    hI hP hQs hrs hAs hEs).2.2 i S).1 actualMap).2
  obtain ⟨a, ha, c, hc, base, hb, e, he, F, hF, label, hl, equal, eligible⟩ :=
    (mem_eligibleTaskSet P G r μ A R U Labels i).1 hi
  obtain ⟨g₀, _, restriction⟩ := eligible.representative
  have represented : TaskRepresentative P r A R U Labels i g₀ :=
    ⟨a, ha, c, hc, base, hb, e, he, F, hF, label, hl, equal, restriction⟩
  have source : ZFSet.pair i a ∈ literalTaskSourceGraph I P R U Labels := by
    rw [equal]
    exact (literalTaskFieldGraph_entry_iff ha hc hb he hF hl 0).2 ⟨equal ▸ hi, rfl⟩
  have agree : ActionAgreementBelow P r A g₀ g a := by
    intro x hx y _ below
    have stored : ZFSet.pair x y ∈ S ↔
        ZFSet.pair (ZFSet.pair g x) y ∈ M.groundEligibleBatchAction P G r μ A Labels := by
      have hx' : x ∈ origin.state.data.D := by
        simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using hx
      have below' : ZFSet.pair x a ∈ origin.state.data.rD := by
        simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using below
      simpa only [origin.initial_data, TransitiveGround.initialCompressionData] using
        origin.state.inputs.agreement i a g S x y source representative mapEntry hx' below'
    have canonical := M.groundEligibleTask_representative_base_iff (y := y)
      origin.state.inputs.group origin.seed.originalAction origin.seed.originalOrder
      hi represented source hx below
    dsimp only at canonical
    rw [← mapEq] at canonical
    exact ((M.groundEligibleBatchAction_old_iff hx).symm.trans canonical.symm).trans
      (stored.trans (M.groundEligibleBatchAction_old_iff hx))
  refine ⟨a, ha, c, hc, base, hb, e, he, F, hF, label, hl, equal,
    restriction.shape, ?_, ?_⟩
  · exact (agree a ha c hc (origin.seed.originalOrder.order.refl a ha)).1 restriction.target_entry
  · intro x hx y hy
    constructor
    · intro entry
      obtain ⟨lower, action⟩ := (restriction.entries x hx y hy).1 entry
      exact ⟨lower, (agree x hx y hy lower).1 action⟩
    · rintro ⟨lower, action⟩
      exact (restriction.entries x hx y hy).2 ⟨lower, (agree x hx y hy lower).2 action⟩

end GroundCompressionOrigin

namespace GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem successorTaskBindings :
    MainSuccessorTaskBindingsCode M Labels certificate.successorOutputValues :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl,
    certificate.origin.initial_representatives pairing unions powers separation⟩

variable (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
include infinite hLabels

theorem boundSuccessorOutput :
    MainSuccessorOutputCode certificate.successorOutputValues ∧
      MainSuccessorTaskBindingsCode M Labels certificate.successorOutputValues :=
  ⟨certificate.successorOutput pairing unions powers separation infinite hLabels,
    certificate.successorTaskBindings pairing unions powers separation⟩

end GroundInitialMainSuccessorData

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Transfinite_LinkedSuccessorOutputFieldEquality
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PartitionPilot.Forcing
universe v

theorem linkedSuccessorOutputFields_0 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 0 = s 0 := rfl

theorem linkedSuccessorOutputFields_1 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 1 = t 0 := rfl

theorem linkedSuccessorOutputFields_2 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 2 = s 1 := rfl

theorem linkedSuccessorOutputFields_3 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 3 = t 1 := rfl

theorem linkedSuccessorOutputFields_4 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 4 = s 2 := rfl

theorem linkedSuccessorOutputFields_5 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 5 = t 2 := rfl

theorem linkedSuccessorOutputFields_6 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 6 = s 3 := rfl

theorem linkedSuccessorOutputFields_7 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 7 = t 3 := rfl

theorem linkedSuccessorOutputFields_8 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 8 = s 4 := rfl

theorem linkedSuccessorOutputFields_9 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 9 = t 4 := rfl

theorem linkedSuccessorOutputFields_10 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 10 = s 6 := rfl

theorem linkedSuccessorOutputFields_11 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 11 = t 6 := rfl

theorem linkedSuccessorOutputFields_12 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 12 = s 7 := rfl

theorem linkedSuccessorOutputFields_13 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 13 = t 7 := rfl

theorem linkedSuccessorOutputFields_14 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 14 = s 8 := rfl

theorem linkedSuccessorOutputFields_15 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 15 = t 8 := rfl

theorem linkedSuccessorOutputFields_16 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 16 = s 10 := rfl

theorem linkedSuccessorOutputFields_17 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 17 = t 10 := rfl

theorem linkedSuccessorOutputFields_18 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 18 = points := rfl

theorem linkedSuccessorOutputFields_19 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 19 = actors := rfl

theorem linkedSuccessorOutputFields_20 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 20 = s 9 := rfl

theorem linkedSuccessorOutputFields_21 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 21 = extra 0 := rfl

theorem linkedSuccessorOutputFields_22 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 22 = extra 1 := rfl

theorem linkedSuccessorOutputFields_23 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 23 = extra 2 := rfl

theorem linkedSuccessorOutputFields_24 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 24 = extra 3 := rfl

theorem linkedSuccessorOutputFields_25 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 25 = extra 4 := rfl

theorem linkedSuccessorOutputFields_26 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 26 = extra 5 := rfl

theorem linkedSuccessorOutputFields_27 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 27 = extra 6 := rfl

theorem linkedSuccessorOutputFields_28 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 28 = extra 7 := rfl

theorem linkedSuccessorOutputFields_29 {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) :
    linkedSuccessorOutputFields s t points actors extra 29 = t 9 := rfl

theorem linkedSuccessorOutputFields_eq {A : Type v} (s t : Fin 24 → A)
    (points actors : A) (extra : Fin 8 → A) (v : Fin 30 → A)
    (fields : s 0 = v 0 ∧
      t 0 = v 1 ∧
      s 1 = v 2 ∧
      t 1 = v 3 ∧
      s 2 = v 4 ∧
      t 2 = v 5 ∧
      s 3 = v 6 ∧
      t 3 = v 7 ∧
      s 4 = v 8 ∧
      t 4 = v 9 ∧
      s 6 = v 10 ∧
      t 6 = v 11 ∧
      s 7 = v 12 ∧
      t 7 = v 13 ∧
      s 8 = v 14 ∧
      t 8 = v 15 ∧
      s 10 = v 16 ∧
      t 10 = v 17 ∧
      points = v 18 ∧
      actors = v 19 ∧
      s 9 = v 20 ∧
      extra 0 = v 21 ∧
      extra 1 = v 22 ∧
      extra 2 = v 23 ∧
      extra 3 = v 24 ∧
      extra 4 = v 25 ∧
      extra 5 = v 26 ∧
      extra 6 = v 27 ∧
      extra 7 = v 28 ∧
      t 9 = v 29) :
    linkedSuccessorOutputFields s t points actors extra = v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29⟩ := fields
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [linkedSuccessorOutputFields_0] using h0
  ·
    refine Fin.cases ?_ (fun j => ?_) j
    · exact (linkedSuccessorOutputFields_1 s t points actors extra).trans h1
    ·
      refine Fin.cases ?_ (fun j => ?_) j
      · exact (linkedSuccessorOutputFields_2 s t points actors extra).trans h2
      ·
        refine Fin.cases ?_ (fun j => ?_) j
        · exact (linkedSuccessorOutputFields_3 s t points actors extra).trans h3
        ·
          refine Fin.cases ?_ (fun j => ?_) j
          · exact (linkedSuccessorOutputFields_4 s t points actors extra).trans h4
          ·
            refine Fin.cases ?_ (fun j => ?_) j
            · exact (linkedSuccessorOutputFields_5 s t points actors extra).trans h5
            ·
              refine Fin.cases ?_ (fun j => ?_) j
              · exact (linkedSuccessorOutputFields_6 s t points actors extra).trans h6
              ·
                refine Fin.cases ?_ (fun j => ?_) j
                · exact (linkedSuccessorOutputFields_7 s t points actors extra).trans h7
                ·
                  refine Fin.cases ?_ (fun j => ?_) j
                  · exact (linkedSuccessorOutputFields_8 s t points actors extra).trans h8
                  ·
                    refine Fin.cases ?_ (fun j => ?_) j
                    · exact (linkedSuccessorOutputFields_9 s t points actors extra).trans h9
                    ·
                      refine Fin.cases ?_ (fun j => ?_) j
                      · exact (linkedSuccessorOutputFields_10 s t points actors extra).trans h10
                      ·
                        refine Fin.cases ?_ (fun j => ?_) j
                        · exact (linkedSuccessorOutputFields_11 s t points actors extra).trans h11
                        ·
                          refine Fin.cases ?_ (fun j => ?_) j
                          · exact (linkedSuccessorOutputFields_12 s t points actors extra).trans h12
                          ·
                            refine Fin.cases ?_ (fun j => ?_) j
                            · exact (linkedSuccessorOutputFields_13 s t points actors extra).trans h13
                            ·
                              refine Fin.cases ?_ (fun j => ?_) j
                              · exact (linkedSuccessorOutputFields_14 s t points actors extra).trans h14
                              ·
                                refine Fin.cases ?_ (fun j => ?_) j
                                · exact (linkedSuccessorOutputFields_15 s t points actors extra).trans h15
                                ·
                                  refine Fin.cases ?_ (fun j => ?_) j
                                  · exact (linkedSuccessorOutputFields_16 s t points actors extra).trans h16
                                  ·
                                    refine Fin.cases ?_ (fun j => ?_) j
                                    · exact (linkedSuccessorOutputFields_17 s t points actors extra).trans h17
                                    ·
                                      refine Fin.cases ?_ (fun j => ?_) j
                                      · exact (linkedSuccessorOutputFields_18 s t points actors extra).trans h18
                                      ·
                                        refine Fin.cases ?_ (fun j => ?_) j
                                        · exact (linkedSuccessorOutputFields_19 s t points actors extra).trans h19
                                        ·
                                          refine Fin.cases ?_ (fun j => ?_) j
                                          · exact (linkedSuccessorOutputFields_20 s t points actors extra).trans h20
                                          ·
                                            refine Fin.cases ?_ (fun j => ?_) j
                                            · exact (linkedSuccessorOutputFields_21 s t points actors extra).trans h21
                                            ·
                                              refine Fin.cases ?_ (fun j => ?_) j
                                              · exact (linkedSuccessorOutputFields_22 s t points actors extra).trans h22
                                              ·
                                                refine Fin.cases ?_ (fun j => ?_) j
                                                · exact (linkedSuccessorOutputFields_23 s t points actors extra).trans h23
                                                ·
                                                  refine Fin.cases ?_ (fun j => ?_) j
                                                  · exact (linkedSuccessorOutputFields_24 s t points actors extra).trans h24
                                                  ·
                                                    refine Fin.cases ?_ (fun j => ?_) j
                                                    · exact (linkedSuccessorOutputFields_25 s t points actors extra).trans h25
                                                    ·
                                                      refine Fin.cases ?_ (fun j => ?_) j
                                                      · exact (linkedSuccessorOutputFields_26 s t points actors extra).trans h26
                                                      ·
                                                        refine Fin.cases ?_ (fun j => ?_) j
                                                        · exact (linkedSuccessorOutputFields_27 s t points actors extra).trans h27
                                                        ·
                                                          refine Fin.cases ?_ (fun j => ?_) j
                                                          · exact (linkedSuccessorOutputFields_28 s t points actors extra).trans h28
                                                          ·
                                                            refine Fin.cases ?_ (fun j => ?_) j
                                                            · exact (linkedSuccessorOutputFields_29 s t points actors extra).trans h29
                                                            ·
                                                              exact Fin.elim0 j

end PartitionPilot.Forcing

end OAI
end

section
-- module Solutions.OAIQ253_PP.PartitionPrinciple_Forcing_GroundTaskBearingSuccessorWitness
attribute [-instance] _root_.OAI.PartitionPilot.Forcing.GroundMainPrefix.withTopSmall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source : GroundLinkedMainStage M K Labels C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source.main Labels)

theorem exists_taskBearingLinkedTarget
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
    (serial : GroundSerializedChronology M (insert certificate.target.cutoff certificate.target.cutoff) C D rD)
    (agreement : ∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
      serial.fields.value j s = certificate.target.history.fieldValue j s)
    (invariant : certificate.target.Invariant K Labels)
    (rank : ZFSet.rank serial.code < ZFSet.rank K) :
    ∃ target : GroundLinkedMainStage M K Labels C D rD,
      target.main = certificate.target ∧
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source.code target.code
        certificate.transition.map.code := by
  let target : GroundLinkedMainStage M K Labels C D rD :=
    ⟨certificate.target, serial, agreement, invariant, rank⟩
  let extra : Fin 8 → ZFSet.{u} :=
    fun j => certificate.successorOutputValues (Fin.natAdd 21 (j.castAdd 1))
  let maps : Fin 4 → ZFSet.{u} := Fin.cases certificate.transition.map.points
    (Fin.cases certificate.transition.map.actors
      (Fin.cases source.main.birth (fun _ => certificate.target.birth)))
  let fields : Fin 60 → ZFSet.{u} :=
    Fin.addCases (m := 24) (n := 36) source.rawFields
      (Fin.addCases (m := 24) (n := 12) target.rawFields
        (Fin.addCases (m := 4) (n := 8) maps extra))
  have extraGround : ∀ j, extra j ∈ M.sets := fun j =>
    certificate.successorOutputValues_ground pairing unions powers separation infinite hLabels _
  have mapsGround : ∀ j, maps j ∈ M.sets :=
    Fin.cases certificate.transition.map.points_ground
      (Fin.cases certificate.transition.map.actors_ground
        (Fin.cases source.main.birth_ground (fun _ => certificate.target.birth_ground)))
  have ground : ∀ j, fields j ∈ M.sets := by
    intro j
    refine Fin.addCases (m := 24) (n := 36) ?_ ?_ j
    · intro a
      simpa only [fields, Fin.addCases_left] using source.rawFields_ground pairing a
    · intro a
      refine Fin.addCases (m := 24) (n := 12) ?_ ?_ a
      · intro b
        simpa only [fields, Fin.addCases_right, Fin.addCases_left] using target.rawFields_ground pairing b
      · intro b
        refine Fin.addCases (m := 4) (n := 8) ?_ ?_ b
        · intro c
          simpa only [fields, Fin.addCases_right, Fin.addCases_left] using mapsGround c
        · intro c
          simpa only [fields, Fin.addCases_right] using extraGround c
  have sourceFields : (fun j : Fin 24 => fields (j.castAdd 36)) = source.rawFields := by
    funext j
    simp only [fields, Fin.addCases_left]
  have targetFields : (fun j : Fin 24 => fields (Fin.natAdd 24 (j.castAdd 12))) = target.rawFields := by
    funext j
    simp only [fields, Fin.addCases_right, Fin.addCases_left]
  have taskFields : (fun j : Fin 8 => fields (Fin.natAdd 52 j)) = extra := by
    funext j
    have index : Fin.natAdd 52 j = Fin.natAdd 24 (Fin.natAdd 24 (Fin.natAdd 4 j)) := by
      apply Fin.ext
      change 52 + j.val = 24 + (24 + (4 + j.val))
      simp only [← Nat.add_assoc]
    rw [index]
    simp only [fields, Fin.addCases_right]
  have outputs : linkedSuccessorOutputFields source.rawFields target.rawFields
      certificate.transition.map.points certificate.transition.map.actors extra =
      certificate.successorOutputValues := by
    obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := source.rawFields_stage_projections
    obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := target.rawFields_stage_projections
    obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25, o26, o27, o28, o29⟩ :=
      certificate.successorOutputValues_projections
    apply linkedSuccessorOutputFields_eq
    exact ⟨
      s0.trans o0.symm, t0.trans o1.symm, s1.trans o2.symm, t1.trans o3.symm,
      s2.trans o4.symm, t2.trans o5.symm, s3.trans o6.symm, t3.trans o7.symm,
      s4.trans o8.symm, t4.trans o9.symm, s6.trans o10.symm, t6.trans o11.symm,
      s7.trans o12.symm, t7.trans o13.symm, s8.trans o14.symm, t8.trans o15.symm,
      s10.trans o16.symm, t10.trans o17.symm, o18.symm, o19.symm,
      s9.trans o20.symm, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl,
      rfl, t9.trans o29.symm⟩
  refine ⟨target, rfl, fields, ground, ?_⟩
  rw [sourceFields, targetFields, taskFields]
  change TaskBearingMainSuccessorRawCode M K Labels C D rD ZFSet.omega source.code target.code
    certificate.transition.map.code certificate.transition.map.points certificate.transition.map.actors
    source.main.birth certificate.target.birth source.rawFields target.rawFields extra
  refine ⟨source.transition_rawFields target certificate.transition certificate.coversOldBirths,
    certificate.cutoff_strict, ?_⟩
  rw [outputs]
  exact certificate.boundSuccessorOutput pairing unions powers separation infinite hLabels

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

omit pairing unions powers separation collection in
theorem mem_linkedMainStageCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.linkedMainStageCandidates B K Labels C D rD ↔
      z ∈ B ∧ ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z := ZFSet.mem_sep

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
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_rankedTaskBearingSuccessor {K Labels D rD c : ZFSet.{u}}
    (source : GroundLinkedMainStage M K Labels C D rD)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hLabels : Labels ∈ M.sets) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD) (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) (level : GroundMainCandidateLevel M K) :
    ∃ certificate : GroundInitialMainSuccessorData M C D rD source.main Labels,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        target.main = certificate.target ∧
        target.code ∈ M.linkedMainStageCandidates level.carrier K Labels C D rD ∧
        certificate.transition.map.code ∈ level.carrier ∧
        TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
          source.code target.code certificate.transition.map.code := by
  obtain ⟨certificate⟩ := M.exists_groundInitialMainSuccessor pairing unions powers separation
    collection infinite choice source.main hLabels hc dense above coordinateInjection
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨serial, _, serialRank, _, agreement, _⟩ :=
    certificate.exists_rankedTargetSerialization pairing unions powers separation collection infinite choice
      hK conditions source.invariant level source.serial source.serial_rank source.agreement
  have invariant := certificate.target_invariant pairing unions powers separation collection infinite choice
    hLabels hK standard source.invariant
  obtain ⟨target, same, code⟩ := certificate.exists_taskBearingLinkedTarget
    pairing unions powers separation infinite hLabels serial agreement invariant serialRank
  have targetBound : target.code ∈ level.carrier := (level.membership _).2
    ⟨target.code_ground pairing, target.code_rank_lt pairing unions powers separation infinite hK conditions⟩
  have transitionBound : certificate.transition.map.code ∈ level.carrier := (level.membership _).2
    ⟨certificate.transition.map.code_mem pairing,
      certificate.transition_code_rank_lt pairing unions powers separation collection infinite
        hK conditions source.invariant.points_rank source.invariant.labels_rank source.invariant.actors_rank⟩
  exact ⟨certificate, target, same,
    (M.mem_linkedMainStageCandidates level.carrier K Labels C D rD target.code).2
      ⟨targetBound, target, rfl⟩, transitionBound, code⟩

include choice in
theorem omegaOne_taskBearingSuccessor_total_oai {K D rD c : ZFSet.{u}}
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD) (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) (level : GroundMainCandidateLevel M K)
    {s : ZFSet.{u}} (hs : s ∈ M.linkedMainStageCandidates level.carrier K C C D rD) :
    ∃ t ∈ M.linkedMainStageCandidates level.carrier K C C D rD, ∃ z ∈ level.carrier,
      TaskBearingMainSuccessorCode M K C C D rD ZFSet.omega s t z := by
  obtain ⟨_, source, sourceEq⟩ := (M.mem_linkedMainStageCandidates level.carrier K C C D rD s).1 hs
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  obtain ⟨certificate, target, _, targetMember, mapMember, code⟩ :=
    M.exists_rankedTaskBearingSuccessor pairing unions powers separation collection infinite choice
      source hK standard hC hc dense above coordinateInjection level
  exact ⟨target.code, targetMember, certificate.transition.map.code, mapMember, sourceEq ▸ code⟩

end PartitionPilot.Forcing.TransitiveGround



end OAI
end

theorem solution.{u} : type_of% @OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total_oai.{u} := @OAI.PartitionPilot.Forcing.TransitiveGround.omegaOne_taskBearingSuccessor_total_oai.{u}
