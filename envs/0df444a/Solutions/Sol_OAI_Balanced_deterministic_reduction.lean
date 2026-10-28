-- Prove2me | solution 1 for OAI.Balanced.deterministic_reduction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:23:26.231427+00:00
-- url     : https://prove2.me/submissions/66d69199-0bec-4960-826b-d15096129e4e

import Mathlib
import Definitions.Def_BalancedRyser
import Definitions.Def_OAIQ63Br004

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffineIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F]

theorem eq_of_onLine_same_direction (p : Point F) (l m : Line F)
    (hdir : l.1 = m.1) (hl : OnLine p l) (hm : OnLine p m) : l = m := by
  rw [line_eq_lineThrough p l hl, line_eq_lineThrough p m hm, hdir]

section Finite

variable [Fintype F] [DecidableEq F]

theorem card_lines_through (p : Point F) :
    ((Finset.univ : Finset (Line F)).filter fun l => OnLine p l).card =
      Fintype.card F + 1 := by
  rw [← Fintype.card_subtype]
  exact (Fintype.card_congr (linesThroughEquiv p)).trans Fintype.card_option

end Finite

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_PencilOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

variable {P I J : Type*} [DecidableEq P]

theorem card_le_exceptional_add_cover_budget
    (S E : Finset P) (B : Finset J) (G : J → Finset P) (k : ℕ)
    (hcover : S ⊆ E ∪ B.biUnion G)
    (htrace : ∀ j ∈ B, (G j ∩ S).card ≤ k) :
    S.card ≤ E.card + k * B.card := by
  have hsub : S ⊆ E ∪ B.biUnion (fun j => G j ∩ S) := by
    intro x hx
    rcases Finset.mem_union.mp (hcover hx) with he | hg
    · exact Finset.mem_union_left _ he
    · obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hg
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨j, hj, Finset.mem_inter.mpr ⟨hxj, hx⟩⟩)
  calc
    S.card ≤ (E ∪ B.biUnion (fun j => G j ∩ S)).card := Finset.card_le_card hsub
    _ ≤ E.card + (B.biUnion (fun j => G j ∩ S)).card := Finset.card_union_le _ _
    _ ≤ E.card + B.card * k := Nat.add_le_add_left
      (Finset.card_biUnion_le_card_mul B (fun j => G j ∩ S) k htrace) _
    _ = E.card + k * B.card := by rw [Nat.mul_comm]

theorem pencil_cover_card_bound
    (S E : Finset P) (A : Finset I) (F : I → Finset P)
    (B : Finset J) (G : J → Finset P) (k : ℕ)
    (hcover : S ⊆ A.biUnion F ∪ B.biUnion G)
    (hpencil : ∀ i ∈ A, F i ∩ S ⊆ E)
    (htrace : ∀ j ∈ B, (G j ∩ S).card ≤ k) :
    S.card ≤ E.card + k * B.card := by
  apply card_le_exceptional_add_cover_budget S E B G k _ htrace
  intro x hx
  rcases Finset.mem_union.mp (hcover hx) with hf | hg
  · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hf
    exact Finset.mem_union_left _ (hpencil i hi (Finset.mem_inter.mpr ⟨hxi, hx⟩))
  · exact Finset.mem_union_right _ hg

theorem affine_pencil_cover_card_bound
    (S : Finset P) (p : P) (A : Finset I) (F : I → Finset P)
    (B : Finset J) (G : J → Finset P)
    (hcover : S ⊆ A.biUnion F ∪ B.biUnion G)
    (hpencil : ∀ i ∈ A, F i ∩ S ⊆ {p})
    (htrace : ∀ j ∈ B, (G j ∩ S).card ≤ 1) :
    S.card ≤ 1 + B.card := by
  simpa using pencil_cover_card_bound S {p} A F B G 1 hcover hpencil htrace

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CoreRepresentatives
attribute [-instance] _root_.OAI.Balanced.instDecidableProjectiveIncident
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

omit [Field F] in
lemma mem_constituentLines (d : Direction F) (s : Bool) :
    constituent C.merged d s ∈ constituentLines C.merged := by
  classical
  exact Finset.mem_image.mpr ⟨(d, s), Finset.mem_univ _, rfl⟩

lemma constituent_not_split (hvalid : C.Valid) (d : Direction F) (s : Bool) :
    constituent C.merged d s ∉ C.splitLines := by
  classical
  intro h
  obtain ⟨slot, _, he⟩ := Finset.mem_image.mp h
  have hex := (hvalid.2 slot).2.1
  apply hex
  rw [he]
  exact C.mem_constituentLines d s

lemma false_constituent_not_deleted (hvalid : C.Valid) (d : Direction F) :
    constituent C.merged d false ∉ C.deletedLines := by
  classical
  intro h
  rcases Finset.mem_union.mp h with hs | hm
  · exact C.constituent_not_split hvalid d false hs
  · obtain ⟨e, _, he⟩ := Finset.mem_image.mp hm
    have hed : e = d := congrArg Prod.fst he
    subst e
    exact hvalid.1 d (congrArg Prod.snd he).symm

lemma core_avoids_deleted {p : Point F} (hp : p ∈ C.core)
    {l : Line F} (hl : l ∈ C.deletedLines) : ¬ OnLine p l := by
  exact (Finset.mem_filter.mp hp).2 l hl

omit [Field F] in
lemma split_mem_deleted (slot : Slot F) : (C.choice slot).line ∈ C.deletedLines := by
  classical
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨slot, Finset.mem_univ _, rfl⟩

lemma tuplePoint_not_core (hvalid : C.Valid) (slot : Slot F) (i : Fin 4) :
    tuplePoint C.merged (C.choice slot).tuple i ∉ C.core := by
  intro hp
  exact C.core_avoids_deleted hp (C.split_mem_deleted slot)
    ((hvalid.2 slot).2.2.2.2.2.1 i)

theorem core_block_has_representative (hvalid : C.Valid)
    {b : BlockLabel F} (hb : C.IsBlockLabel b) {p : Point F}
    (hp : p ∈ C.core) (hpb : p ∈ C.blockPoints b) :
    ∃ l ∈ C.coreRepresentative b, l ∉ C.deletedLines ∧ OnLine p l := by
  classical
  rcases b with l | d | ⟨slot, side⟩
  · refine ⟨l, by simp [coreRepresentative], ?_, ?_⟩
    · intro hd
      rcases Finset.mem_union.mp hd with hs | hm
      · exact hb (Finset.mem_union_left _ hs)
      · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hm
        exact hb (Finset.mem_union_right _ (C.mem_constituentLines d true))
    · exact (Finset.mem_filter.mp (Finset.mem_inter.mp hpb).1).2
  · refine ⟨constituent C.merged d false, by simp [coreRepresentative],
      C.false_constituent_not_deleted hvalid d, ?_⟩
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hpb).1 with hfalse | htrue
    · exact (Finset.mem_filter.mp hfalse).2
    · have hdel : constituent C.merged d true ∈ C.deletedLines := by
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩
      exact False.elim (C.core_avoids_deleted hp hdel (Finset.mem_filter.mp htrue).2)
  · cases side <;> simp only [blockPoints, Finset.mem_insert, Finset.mem_singleton] at hpb
    · rcases hpb with rfl | rfl
      · exact False.elim (C.tuplePoint_not_core hvalid slot 0 hp)
      · exact False.elim (C.tuplePoint_not_core hvalid slot 2 hp)
    · rcases hpb with rfl | rfl
      · exact False.elim (C.tuplePoint_not_core hvalid slot 1 hp)
      · exact False.elim (C.tuplePoint_not_core hvalid slot 3 hp)

lemma core_subset_points_for_representatives : C.core ⊆ C.points := by
  classical
  intro p hp
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro l hl
  exact C.core_avoids_deleted hp (Finset.mem_union_left _ hl)

omit [Field F] [Fintype F] [DecidableEq F] in
lemma coreRepresentative_card_le_one (b : BlockLabel F) :
    (C.coreRepresentative b).card ≤ 1 := by
  rcases b with l | d | s <;> simp [coreRepresentative]

lemma coreRepresentative_not_deleted (hvalid : C.Valid)
    {b : BlockLabel F} (hb : C.IsBlockLabel b)
    {l : Line F} (hl : l ∈ C.coreRepresentative b) : l ∉ C.deletedLines := by
  classical
  rcases b with b | d | s
  · simp only [coreRepresentative, Finset.mem_singleton] at hl
    subst l
    intro hd
    rcases Finset.mem_union.mp hd with hs | hm
    · exact hb (Finset.mem_union_left _ hs)
    · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hm
      exact hb (Finset.mem_union_right _ (C.mem_constituentLines d true))
  · simp only [coreRepresentative, Finset.mem_singleton] at hl
    subst l
    exact C.false_constituent_not_deleted hvalid d
  · simp [coreRepresentative] at hl

omit [Field F] [Fintype F] in
theorem representatives_card_le (B : Finset (BlockLabel F)) :
    (B.biUnion C.coreRepresentative).card ≤ B.card := by
  simpa using Finset.card_biUnion_le_card_mul B C.coreRepresentative 1
    (fun b _ => C.coreRepresentative_card_le_one b)

theorem core_cover_reduction (hvalid : C.Valid)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ p ∈ C.points, ∃ b ∈ B, p ∈ C.blockPoints b) :
    (B.biUnion C.coreRepresentative).card ≤ B.card ∧
    (∀ l ∈ B.biUnion C.coreRepresentative, l ∉ C.deletedLines) ∧
    CoversPoints (B.biUnion C.coreRepresentative) C.core := by
  classical
  refine ⟨C.representatives_card_le B, ?_, ?_⟩
  · intro l hl
    obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hl
    exact C.coreRepresentative_not_deleted hvalid (hlabels b hb) hbl
  · intro p hp
    obtain ⟨b, hb, hpb⟩ := hcover p (C.core_subset_points_for_representatives hp)
    obtain ⟨l, hl, _, hpl⟩ := C.core_block_has_representative hvalid (hlabels b hb) hp hpb
    exact ⟨l, Finset.mem_biUnion.mpr ⟨b, hb, hl⟩, hpl⟩

omit [Fintype F] in
lemma pencil_representatives_card_le_labels (B : Finset (BlockLabel F))
    (P : ProjectivePoint F) :
    ((B.biUnion C.coreRepresentative).filter (fun l => ThroughProjective l P)).card ≤
      (B.filter (C.RepresentedThrough P)).card := by
  classical
  have hsub : (B.biUnion C.coreRepresentative).filter (fun l => ThroughProjective l P) ⊆
      (B.filter (C.RepresentedThrough P)).biUnion C.coreRepresentative := by
    intro l hl
    obtain ⟨hunion, hthrough⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hunion
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, l, hbl, hthrough⟩, hbl⟩
  exact (Finset.card_le_card hsub).trans (C.representatives_card_le _)

omit [Fintype F] in
lemma outside_pencil_representatives_card_le_labels (B : Finset (BlockLabel F))
    (P : ProjectivePoint F) :
    ((B.biUnion C.coreRepresentative).filter (fun l => ¬ ThroughProjective l P)).card ≤
      (B.filter (fun b => ¬ C.RepresentedThrough P b)).card := by
  classical
  have hsub : (B.biUnion C.coreRepresentative).filter (fun l => ¬ ThroughProjective l P) ⊆
      (B.filter (fun b => ¬ C.RepresentedThrough P b)).biUnion C.coreRepresentative := by
    intro l hl
    obtain ⟨hunion, hnot⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hunion
    have hbnot : ¬ C.RepresentedThrough P b := by
      rintro ⟨m, hbm, hm⟩
      have he : l = m := Finset.card_le_one.mp (C.coreRepresentative_card_le_one b) l hbl m hbm
      exact hnot (he.symm ▸ hm)
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_filter.mpr ⟨hb, hbnot⟩, hbl⟩
  exact (Finset.card_le_card hsub).trans (C.representatives_card_le _)

theorem core_cover_outside_pencil_budget (hvalid : C.Valid)
    {rho : ℝ} (hconcentration : C.CoreConcentration rho)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcard : B.card ≤ Fintype.card F)
    (hcover : ∀ p ∈ C.points, ∃ b ∈ B, p ∈ C.blockPoints b) :
    ∃ P : ProjectivePoint F,
      ((B.filter (fun b => ¬ C.RepresentedThrough P b)).card : ℝ) ≤
        rho * Fintype.card F / 4 := by
  classical
  obtain ⟨hrepCard, hrepDeleted, hrepCover⟩ := C.core_cover_reduction hvalid B hlabels hcover
  obtain ⟨P, hlarge⟩ := hconcentration (B.biUnion C.coreRepresentative)
    hrepDeleted (hrepCard.trans hcard) hrepCover
  refine ⟨P, ?_⟩
  have hcount := C.pencil_representatives_card_le_labels B P
  have hcountReal :
      (((B.biUnion C.coreRepresentative).filter (fun l => ThroughProjective l P)).card : ℝ) ≤
      ((B.filter (C.RepresentedThrough P)).card : ℝ) := by exact_mod_cast hcount
  have hcardReal : (B.card : ℝ) ≤ Fintype.card F := by exact_mod_cast hcard
  have hpartition :
      (B.filter (C.RepresentedThrough P)).card +
      (B.filter (fun b => ¬ C.RepresentedThrough P b)).card = B.card := by
    exact Finset.card_filter_add_card_filter_not _
  have hpartitionReal :
      ((B.filter (C.RepresentedThrough P)).card : ℝ) +
      ((B.filter (fun b => ¬ C.RepresentedThrough P b)).card : ℝ) = B.card := by
    exact_mod_cast hpartition
  nlinarith

end
end Configuration
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SizeThreshold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

theorem ordinary_pencil_gap {q B t : ℝ} {rho : ℝ}
    (hB : 0 ≤ B) (hsize : 2 * (1 + B) < rho * q)
    (ht : t ≤ rho * q / 4) : 1 + t < rho * q := by
  nlinarith

theorem partner_pencil_gap {q B t : ℝ} {rho : ℝ}
    (hsize : 2 * (1 + B) < rho * q)
    (ht : t ≤ rho * q / 4) : 1 + B + 2 * t < rho * q := by
  nlinarith

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_AffinePencilForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

lemma distinct_line_intersection_card_le_one (l m : Line F) (hne : l ≠ m) :
    (linePoints l ∩ linePoints m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  exact common_point_eq_of_lines_ne l m hne p r
    (mem_linePoints_iff p l |>.mp (Finset.mem_inter.mp hp).1)
    (mem_linePoints_iff p m |>.mp (Finset.mem_inter.mp hp).2)
    (mem_linePoints_iff r l |>.mp (Finset.mem_inter.mp hr).1)
    (mem_linePoints_iff r m |>.mp (Finset.mem_inter.mp hr).2)

lemma pencil_line_trace_subset_point (l m : Line F) (hne : l ≠ m)
    (p : Point F) (hpl : OnLine p l) (hpm : OnLine p m) :
    linePoints m ∩ linePoints l ⊆ {p} := by
  intro r hr
  apply Finset.mem_singleton.mpr
  exact common_point_eq_of_lines_ne l m hne r p
    (mem_linePoints_iff r l |>.mp (Finset.mem_inter.mp hr).2)
    (mem_linePoints_iff r m |>.mp (Finset.mem_inter.mp hr).1) hpl hpm

theorem missing_pencil_line_occupancy_bound (L : Finset (Line F))
    (U : Finset (Point F)) (hcover : CoversPoints L U)
    (p : Point F) (l : Line F) (hpl : OnLine p l) (homit : l ∉ L) :
    (linePoints l ∩ U).card ≤ 1 + (L.filter (fun m => ¬ OnLine p m)).card := by
  classical
  apply affine_pencil_cover_card_bound (linePoints l ∩ U) p
    (L.filter (OnLine p)) linePoints (L.filter (fun m => ¬ OnLine p m)) linePoints
  · intro x hx
    obtain ⟨m, hm, hxm⟩ := hcover x (Finset.mem_inter.mp hx).2
    by_cases hpm : OnLine p m
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_filter.mpr ⟨hm, hpm⟩, (mem_linePoints_iff x m).mpr hxm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨m, Finset.mem_filter.mpr ⟨hm, hpm⟩, (mem_linePoints_iff x m).mpr hxm⟩)
  · intro m hm x hx
    have hml : l ≠ m := by intro he; subst m; exact homit (Finset.mem_filter.mp hm).1
    apply pencil_line_trace_subset_point l m hml p hpl (Finset.mem_filter.mp hm).2
    exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
  · intro m hm
    have hml : l ≠ m := by intro he; subst m; exact homit (Finset.mem_filter.mp hm).1
    calc
      (linePoints m ∩ (linePoints l ∩ U)).card ≤ (linePoints l ∩ linePoints m).card := by
        apply Finset.card_le_card
        intro x hx
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1, (Finset.mem_inter.mp hx).1⟩
      _ ≤ 1 := distinct_line_intersection_card_le_one l m hml

namespace Configuration

variable (C : Configuration F)

theorem ordinary_pencil_line_is_represented (hvalid : C.Valid)
    {rho : ℝ} {cap : ℕ} (hoccupancy : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4)
    (l : Line F) (hpl : OnLine p l) (hnotdel : l ∉ C.deletedLines) :
    l ∈ B.biUnion C.coreRepresentative := by
  classical
  by_contra homit
  have hcoreCover := (C.core_cover_reduction hvalid B hlabels hcover).2.2
  have hmissing := missing_pencil_line_occupancy_bound
    (B.biUnion C.coreRepresentative) C.core hcoreCover p l hpl homit
  have houtside := C.outside_pencil_representatives_card_le_labels B (Sum.inl p)
  have houtside' :
      ((B.biUnion C.coreRepresentative).filter (fun m => ¬ OnLine p m)).card ≤
      (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card := by
    apply le_trans (Finset.card_le_card ?_) houtside
    intro representative hrepresentative
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hrepresentative).1, (Finset.mem_filter.mp hrepresentative).2⟩
  have hmissingReal : ((linePoints l ∩ C.core).card : ℝ) ≤
      1 + ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) := by
    exact_mod_cast hmissing.trans (Nat.add_le_add_left houtside' 1)
  have hgap := ordinary_pencil_gap (Nat.cast_nonneg cap) hsize hbudget
  have hocc := hoccupancy.2.1 l hnotdel
  linarith

end Configuration

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_DeletedConstituentForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

omit [Field F] [Fintype F] [DecidableEq F] in
lemma constituent_ne_of_direction_ne {d e : Direction F} (h : d ≠ e)
    (s t : Bool) : constituent C.merged d s ≠ constituent C.merged e t := by
  intro he
  exact h (congrArg Prod.fst he)

theorem other_block_constituent_trace_le_two (B : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ B, C.IsBlockLabel b) (d : Direction F)
    (homit : (Sum.inr (Sum.inl d) : BlockLabel F) ∉ B)
    (b : BlockLabel F) (hb : b ∈ B) (s : Bool) :
    (C.blockPoints b ∩ linePoints (constituent C.merged d s)).card ≤ 2 := by
  classical
  rcases b with l | e | ⟨slot, side⟩
  · have hne : l ≠ constituent C.merged d s := by
      intro he
      have hlabel := hlabels (Sum.inl l) hb
      apply hlabel
      exact Finset.mem_union_right _ (he.symm ▸ C.mem_constituentLines d s)
    calc
      ((linePoints l ∩ C.points) ∩ linePoints (constituent C.merged d s)).card ≤
          (linePoints l ∩ linePoints (constituent C.merged d s)).card := by
        apply Finset.card_le_card
        intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1,
          (Finset.mem_inter.mp hx).2⟩
      _ ≤ 1 := distinct_line_intersection_card_le_one l _ hne
      _ ≤ 2 := by omega
  · have hed : e ≠ d := by intro he; subst e; exact homit hb
    have hsub : C.blockPoints (Sum.inr (Sum.inl e)) ∩ linePoints (constituent C.merged d s) ⊆
        (linePoints (constituent C.merged e false) ∩ linePoints (constituent C.merged d s)) ∪
        (linePoints (constituent C.merged e true) ∩ linePoints (constituent C.merged d s)) := by
      intro x hx
      have hxpair := (Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1
      rcases Finset.mem_union.mp hxpair with hf | ht
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hf, (Finset.mem_inter.mp hx).2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ht, (Finset.mem_inter.mp hx).2⟩)
    have hf := distinct_line_intersection_card_le_one
      (constituent C.merged e false) (constituent C.merged d s)
      (C.constituent_ne_of_direction_ne hed false s)
    have ht := distinct_line_intersection_card_le_one
      (constituent C.merged e true) (constituent C.merged d s)
      (C.constituent_ne_of_direction_ne hed true s)
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  · have hsub := Finset.card_le_card
      (Finset.inter_subset_left : C.blockPoints (Sum.inr (Sum.inr (slot, side))) ∩
        linePoints (constituent C.merged d s) ⊆ C.blockPoints (Sum.inr (Sum.inr (slot, side))))
    cases side <;> exact hsub.trans Finset.card_le_two

theorem selected_merged_pencil_card_le (B : Finset (BlockLabel F))
    (p : Point F) {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap) :
    ((Finset.univ : Finset (Direction F)).filter (fun d =>
      (Sum.inr (Sum.inl d) : BlockLabel F) ∈ B ∧
      OnLine p (constituent C.merged d false))).card ≤ cap := by
  classical
  apply le_trans _ (hocc.1 p)
  apply Finset.card_le_card_of_injOn (fun d => constituent C.merged d false)
  · intro d hd
    exact Finset.mem_filter.mpr
      ⟨C.mem_constituentLines d false, (Finset.mem_filter.mp hd).2.2⟩
  · intro d hd e he hde
    exact congrArg Prod.fst hde

theorem missing_deleted_constituent_occupancy_bound
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F) (d : Direction F) (hpd : OnLine p (constituent C.merged d true))
    (homit : (Sum.inr (Sum.inl d) : BlockLabel F) ∉ B) :
    (linePoints (constituent C.merged d true) ∩ C.retained).card ≤
      1 + cap + 2 * (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card := by
  classical
  let l := constituent C.merged d true
  let S := linePoints l ∩ C.retained
  let M := (Finset.univ : Finset (Direction F)).filter (fun e =>
    (Sum.inr (Sum.inl e) : BlockLabel F) ∈ B ∧ OnLine p (constituent C.merged e false))
  let E := {p} ∪ M.biUnion (fun e => linePoints (constituent C.merged e true) ∩ linePoints l)
  have hMcard : M.card ≤ cap := C.selected_merged_pencil_card_le B p hocc
  have hMne : ∀ e ∈ M, e ≠ d := by
    intro e he hed
    subst e
    exact homit (Finset.mem_filter.mp he).2.1
  have htrace : ∀ e ∈ M,
      (linePoints (constituent C.merged e true) ∩ linePoints l).card ≤ 1 := by
    intro e he
    exact distinct_line_intersection_card_le_one _ _
      (C.constituent_ne_of_direction_ne (hMne e he) true true)
  have hEcard : E.card ≤ 1 + cap := by
    have hsum := Finset.card_biUnion_le_card_mul M
      (fun e => linePoints (constituent C.merged e true) ∩ linePoints l) 1 htrace
    have hunion := Finset.card_union_le ({p} : Finset (Point F))
      (M.biUnion (fun e => linePoints (constituent C.merged e true) ∩ linePoints l))
    simp only [Finset.card_singleton, Nat.mul_one] at hsum hunion
    exact hunion.trans (Nat.add_le_add_left (hsum.trans hMcard) 1)
  have hsmall : S.card ≤ E.card +
      2 * (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card := by
    apply pencil_cover_card_bound S E
      (B.filter (C.RepresentedThrough (Sum.inl p))) C.blockPoints
      (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)) C.blockPoints 2
    · intro x hx
      obtain ⟨b, hb, hxb⟩ := hcover x
        (Finset.mem_union_left _ (Finset.mem_inter.mp hx).2)
      by_cases hbp : C.RepresentedThrough (Sum.inl p) b
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨b, Finset.mem_filter.mpr ⟨hb, hbp⟩, hxb⟩)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨b, Finset.mem_filter.mpr ⟨hb, hbp⟩, hxb⟩)
    · intro b hb x hx
      obtain ⟨hbB, hbP⟩ := Finset.mem_filter.mp hb
      obtain ⟨hxb, hxs⟩ := Finset.mem_inter.mp hx
      have hxl := (on_line_iff_mem x l).mp (Finset.mem_inter.mp hxs).1
      rcases b with m | e | ⟨slot, side⟩
      · have hpm : OnLine p m := by simpa [RepresentedThrough, coreRepresentative, ThroughProjective] using hbP
        have hxm : OnLine x m := (on_line_iff_mem x m).mp (Finset.mem_inter.mp hxb).1
        have hml : m ≠ l := by
          intro he
          exact hlabels (Sum.inl m) hbB
            (Finset.mem_union_right _ (he.symm ▸ C.mem_constituentLines d true))
        have hxp := common_point_eq_of_lines_ne m l hml x p hxm hxl hpm hpd
        exact Finset.mem_union_left _ (Finset.mem_singleton.mpr hxp)
      · have hpfalse : OnLine p (constituent C.merged e false) := by
          simpa [RepresentedThrough, coreRepresentative, ThroughProjective] using hbP
        have heM : e ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbB, hpfalse⟩
        have hxpairs := (Finset.mem_inter.mp hxb).1
        rcases Finset.mem_union.mp hxpairs with hf | ht
        · have hne := C.constituent_ne_of_direction_ne (hMne e heM) false true
          have hxp := common_point_eq_of_lines_ne (constituent C.merged e false) l hne x p
            ((on_line_iff_mem x _).mp hf) hxl hpfalse hpd
          exact Finset.mem_union_left _ (Finset.mem_singleton.mpr hxp)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨e, heM, Finset.mem_inter.mpr ⟨ht, (on_line_iff_mem x l).mpr hxl⟩⟩)
      · simp [RepresentedThrough, coreRepresentative] at hbP
    · intro b hb
      have hsub : C.blockPoints b ∩ S ⊆ C.blockPoints b ∩ linePoints l := by
        intro x hx
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
          (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
      exact (Finset.card_le_card hsub).trans
        (C.other_block_constituent_trace_le_two B hlabels d homit b (Finset.mem_filter.mp hb).1 true)
  exact hsmall.trans (Nat.add_le_add_right hEcard _)

theorem deleted_constituent_merged_label_selected
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4)
    (d : Direction F) (hpd : OnLine p (constituent C.merged d true)) :
    (Sum.inr (Sum.inl d) : BlockLabel F) ∈ B := by
  classical
  by_contra homit
  have hbound := C.missing_deleted_constituent_occupancy_bound hocc B hlabels hcover p d hpd homit
  have hboundReal : ((linePoints (constituent C.merged d true) ∩ C.retained).card : ℝ) ≤
      1 + (cap : ℝ) + 2 * ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) := by
    exact_mod_cast hbound
  have hgap := partner_pencil_gap hsize hbudget
  have hoccupancy := hocc.2.2 d
  linarith

end
end Configuration
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_BlockPartitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration.BlockPartitions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {C : Configuration F}

omit [Fintype F] [DecidableEq F] in

theorem line_eq_of_direction_eq {p : Point F} {l m : Line F}
    (hl : OnLine p l) (hm : OnLine p m) (hd : l.1 = m.1) : l = m := by
  apply Prod.ext hd
  exact hl.symm.trans ((congrArg (fun d => lineEval d p) hd).trans hm)

theorem split_not_constituent (hV : C.Valid) (s : Slot F) :
    (C.choice s).line ∉ constituentLines C.merged := (hV.2 s).2.1

theorem tuple_injective (hV : C.Valid) (s : Slot F) :
    Function.Injective (tuplePoint C.merged (C.choice s).tuple) :=
  (hV.2 s).2.2.2.2.1

theorem tuple_on_split (hV : C.Valid) (s : Slot F) (i : Fin 4) :
    OnLine (tuplePoint C.merged (C.choice s).tuple i) (C.choice s).line :=
  (hV.2 s).2.2.2.2.2.1 i

theorem split_line_injective (hV : C.Valid) (hC : C.Compatible) :
    Function.Injective (fun s => (C.choice s).line) := by
  intro s t hst
  by_contra hne
  apply hC.1 s t hne (tuplePoint C.merged (C.choice t).tuple 0)
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · change (C.choice s).line = (C.choice t).line at hst
    rw [hst]
    exact tuple_on_split hV t 0

theorem split_block_onLine (hV : C.Valid) {p : Point F} (s : Slot F) (b : Bool)
    (hp : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, b)))) :
    OnLine p (C.choice s).line := by
  cases b <;> simp only [blockPoints, Finset.mem_insert, Finset.mem_singleton] at hp
  all_goals rcases hp with rfl | rfl
  all_goals exact tuple_on_split hV _ _

theorem split_block_side_unique (hV : C.Valid) {p : Point F}
    (s : Slot F) (b c : Bool)
    (hb : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, b))))
    (hc : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, c)))) : b = c := by
  cases b <;> cases c
  · rfl
  · simp only [blockPoints, Finset.mem_insert, Finset.mem_singleton] at hb hc
    rcases hb with hb | hb <;> rcases hc with hc | hc
    all_goals have h := tuple_injective hV s (hb.symm.trans hc)
    all_goals have hv := congrArg Fin.val h
    all_goals norm_num at hv
  · simp only [blockPoints, Finset.mem_insert, Finset.mem_singleton] at hb hc
    rcases hb with hb | hb <;> rcases hc with hc | hc
    all_goals have h := tuple_injective hV s (hb.symm.trans hc)
    all_goals have hv := congrArg Fin.val h
    all_goals norm_num at hv
  · rfl

omit [Field F] in
theorem constituent_mem (d : Direction F) (b : Bool) :
    constituent C.merged d b ∈ constituentLines C.merged := by
  exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, rfl⟩

theorem regular_block_onLine {p : Point F} {l : Line F}
    (hp : p ∈ C.blockPoints (Sum.inl l)) : OnLine p l :=
  (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2

theorem merged_block_onLine {p : Point F} {d : Direction F}
    (hp : p ∈ C.blockPoints (Sum.inr (Sum.inl d))) :
    ∃ b, OnLine p (constituent C.merged d b) := by
  rcases Finset.mem_union.mp (Finset.mem_inter.mp hp).1 with h | h
  · exact ⟨false, (Finset.mem_filter.mp h).2⟩
  · exact ⟨true, (Finset.mem_filter.mp h).2⟩

theorem regular_split_disjoint (hV : C.Valid) {p : Point F} {l : Line F}
    (hl : C.IsBlockLabel (Sum.inl l)) (s : Slot F) (b : Bool)
    (hd : l.1 = s.1)
    (hp : p ∈ C.blockPoints (Sum.inl l))
    (hs : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, b)))) : False := by
  have heq := line_eq_of_direction_eq (regular_block_onLine hp)
    (split_block_onLine hV s b hs) (hd.trans (split_direction hV s).symm)
  apply hl
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, heq.symm⟩)

theorem regular_merged_disjoint {p : Point F} {l : Line F}
    (hl : C.IsBlockLabel (Sum.inl l)) (d : Direction F)
    (hd : l.1 = d)
    (hp : p ∈ C.blockPoints (Sum.inl l))
    (hm : p ∈ C.blockPoints (Sum.inr (Sum.inl d))) : False := by
  obtain ⟨b, hb⟩ := merged_block_onLine hm
  have heq := line_eq_of_direction_eq (regular_block_onLine hp) hb hd
  apply hl
  apply Finset.mem_union_right
  rw [heq]
  exact constituent_mem d b

theorem merged_split_disjoint (hV : C.Valid) {p : Point F}
    (d : Direction F) (s : Slot F) (b : Bool) (hd : d = s.1)
    (hm : p ∈ C.blockPoints (Sum.inr (Sum.inl d)))
    (hs : p ∈ C.blockPoints (Sum.inr (Sum.inr (s, b)))) : False := by
  obtain ⟨c, hc⟩ := merged_block_onLine hm
  have heq := line_eq_of_direction_eq hc (split_block_onLine hV s b hs)
    (hd.trans (split_direction hV s).symm)
  apply split_not_constituent hV s
  rw [← heq]
  exact constituent_mem d c

theorem block_unique (hV : C.Valid) (hC : C.Compatible)
    {p : Point F} {d : Direction F} {b c : BlockLabel F}
    (hb : b ∈ C.labelsInDirection d) (hc : c ∈ C.labelsInDirection d)
    (hpb : p ∈ C.blockPoints b) (hpc : p ∈ C.blockPoints c) : b = c := by
  classical
  simp only [labelsInDirection, blockLabels, Finset.mem_filter,
    Finset.mem_univ, true_and] at hb hc
  have hdir := hb.2.trans hc.2.symm
  rcases b with l | (g | ⟨s, u⟩) <;> rcases c with m | (h | ⟨t, v⟩)
  · exact congrArg Sum.inl (line_eq_of_direction_eq
      (regular_block_onLine hpb) (regular_block_onLine hpc) hdir)
  · exact (regular_merged_disjoint hb.1 h hdir hpb hpc).elim
  · exact (regular_split_disjoint hV hb.1 t v hdir hpb hpc).elim
  · exact (regular_merged_disjoint hc.1 g hdir.symm hpc hpb).elim
  · exact congrArg (fun g => Sum.inr (Sum.inl g)) hdir
  · exact (merged_split_disjoint hV g t v hdir hpb hpc).elim
  · exact (regular_split_disjoint hV hc.1 s u hdir.symm hpc hpb).elim
  · exact (merged_split_disjoint hV h s u hdir.symm hpc hpb).elim
  · have hline := line_eq_of_direction_eq (split_block_onLine hV s u hpb)
      (split_block_onLine hV t v hpc)
      ((split_direction hV s).trans (hdir.trans (split_direction hV t).symm))
    have hst := split_line_injective hV hC hline
    subst t
    have huv := split_block_side_unique hV s u v hpb hpc
    rw [huv]

theorem pointLabel_mem (hV : C.Valid) (hC : C.Compatible)
    (d : Direction F) (p : {p // p ∈ C.points}) :
    p.val ∈ C.blockPoints (pointLabel hV hC d p).val :=
  (Classical.choose_spec (block_exists hV hC p.property d)).2

theorem pointLabel_eq_iff (hV : C.Valid) (hC : C.Compatible)
    (d : Direction F) (p : {p // p ∈ C.points})
    (b : {b // b ∈ C.labelsInDirection d}) :
    pointLabel hV hC d p = b ↔ p.val ∈ C.blockPoints b.val := by
  constructor
  · intro h
    rw [← h]
    exact pointLabel_mem hV hC d p
  · intro h
    apply Subtype.ext
    exact block_unique hV hC (pointLabel hV hC d p).property b.property
      (pointLabel_mem hV hC d p) h

end Balanced.Configuration.BlockPartitions

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_PartitionEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem encodeAssignment_agree_iff
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x y : X) :
    (∃ i, encodeAssignment eG eL label x i = encodeAssignment eG eL label y i) ↔
      ∃ g, label g x = label g y := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨eG.symm i, (eL (eG.symm i)).injective hi⟩
  · rintro ⟨g, hg⟩
    exact ⟨eG g, by simpa using congrArg (eL g) hg⟩

theorem encodeAssignment_covered_iff
    {G X : Type*} {Label : G → Type*} {r n : ℕ}
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (x : X)
    (C : Finset (Fin r × Fin n)) :
    (∃ i, (i, encodeAssignment eG eL label x i) ∈ C) ↔
      ∃ g, (⟨g, label g x⟩ : Sigma Label) ∈
        C.map (encodeLabel eG eL).symm.toEmbedding := by
  classical
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨eG.symm i, ?_⟩
    apply Finset.mem_map.mpr
    refine ⟨(i, encodeAssignment eG eL label x i), hi, ?_⟩
    apply (encodeLabel eG eL).injective
    simp [encodeAssignment]
  · rintro ⟨g, hg⟩
    rcases Finset.mem_map.mp hg with ⟨v, hv, hvg⟩
    have heq : v = (eG g, eL g (label g x)) := by
      have h := congrArg (encodeLabel eG eL) hvg
      simpa using h
    refine ⟨eG g, ?_⟩
    simpa [heq] using hv

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_PartitionHypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {G X : Type*} [Fintype X] {Label : G → Type*} {r n : ℕ}

theorem partitionHypergraph_nonisolated
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (hblocks : ∀ g, Function.Surjective (label g)) :
    (partitionHypergraph eG eL label).Nonisolated := by
  intro i v
  obtain ⟨x, hx⟩ := hblocks (eG.symm i) ((eL (eG.symm i)).symm v)
  refine ⟨encodeAssignment eG eL label x, ?_, ?_⟩
  · exact (mem_partitionHypergraph_edges eG eL label _).mpr ⟨x, rfl⟩
  · simp [encodeAssignment, hx]

theorem partitionHypergraph_intersecting [Nonempty X]
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (hagrees : ∀ x y, ∃ g, label g x = label g y) :
    (partitionHypergraph eG eL label).Intersecting := by
  constructor
  · obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨_, (mem_partitionHypergraph_edges eG eL label _).mpr ⟨x, rfl⟩⟩
  · intro e he f hf
    obtain ⟨x, rfl⟩ := (mem_partitionHypergraph_edges eG eL label e).mp he
    obtain ⟨y, rfl⟩ := (mem_partitionHypergraph_edges eG eL label f).mp hf
    exact (encodeAssignment_agree_iff eG eL label x y).mpr (hagrees x y)

theorem partitionHypergraph_covers_iff
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (C : Finset (Fin r × Fin n)) :
    (partitionHypergraph eG eL label).Covers C ↔
      ∀ x, ∃ g, (⟨g, label g x⟩ : Sigma Label) ∈
        C.map (encodeLabel eG eL).symm.toEmbedding := by
  constructor
  · intro h x
    apply (encodeAssignment_covered_iff eG eL label x C).mp
    exact h _ ((mem_partitionHypergraph_edges eG eL label _).mpr ⟨x, rfl⟩)
  · intro h e he
    obtain ⟨x, rfl⟩ := (mem_partitionHypergraph_edges eG eL label e).mp he
    exact (encodeAssignment_covered_iff eG eL label x C).mpr (h x)

theorem partitionHypergraph_cover_lower_bound
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g) (k : ℕ)
    (hblocks : ∀ C : Finset (Sigma Label),
      (∀ x, ∃ g, (⟨g, label g x⟩ : Sigma Label) ∈ C) → k ≤ C.card) :
    ∀ C, (partitionHypergraph eG eL label).Covers C → k ≤ C.card := by
  intro C hC
  have h := hblocks (C.map (encodeLabel eG eL).symm.toEmbedding)
    ((partitionHypergraph_covers_iff eG eL label C).mp hC)
  simpa using h

theorem partitionHypergraph_hasCoverNumber [Nonempty G]
    (eG : G ≃ Fin r) (eL : ∀ g, Label g ≃ Fin n)
    (label : (g : G) → X → Label g)
    (hblocks : ∀ C : Finset (Sigma Label),
      (∀ x, ∃ g, (⟨g, label g x⟩ : Sigma Label) ∈ C) → n ≤ C.card) :
    (partitionHypergraph eG eL label).HasCoverNumber n := by
  classical
  constructor
  · obtain ⟨g⟩ := ‹Nonempty G›
    refine ⟨Finset.univ.image (fun v : Fin n => (eG g, v)), ?_, ?_⟩
    · intro e he
      exact ⟨eG g, Finset.mem_image.mpr ⟨e (eG g), Finset.mem_univ _, rfl⟩⟩
    · rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
      exact Finset.card_fin n
  · exact partitionHypergraph_cover_lower_bound eG eL label n hblocks

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FourCycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.FourCycle

theorem opposite_ne (i : Fin 4) : opposite i ≠ i := by
  fin_cases i <;> decide

theorem not_sameBlock_iff_consecutive (i j : Fin 4) :
    ¬ SameBlock i j ↔ Consecutive i j := by
  fin_cases i <;> fin_cases j <;> simp [SameBlock, Consecutive]

theorem sameBlock_or_consecutive (i j : Fin 4) :
    SameBlock i j ∨ Consecutive i j := by
  fin_cases i <;> fin_cases j <;> simp [SameBlock, Consecutive]

variable {α : Type*}

theorem adjacency_of_separated (u : Fin 4 → α) (Adj : α → α → Prop)
    (hsymm : ∀ x y, Adj x y → Adj y x)
    (hcycle : ∀ i : Fin 4, Adj (u i) (u (i + 1)))
    {i j : Fin 4} (h : ¬ SameBlock i j) : Adj (u i) (u j) := by
  rcases (not_sameBlock_iff_consecutive i j).1 h with h | h
  · simpa only [h] using hcycle i
  · rw [h]
    exact hsymm _ _ (hcycle j)

theorem opposite_uncovered (u : Fin 4 → α) (hu : Function.Injective u)
    (Adj : α → α → Prop) (hopp : ∀ i, ¬ Adj (u i) (u (opposite i)))
    (i : Fin 4) : u (opposite i) ≠ u i ∧ ¬ Adj (u i) (u (opposite i)) := by
  exact ⟨fun h => opposite_ne i (hu h), hopp i⟩

theorem exists_uncovered (u : Fin 4 → α) (hu : Function.Injective u)
    (Adj : α → α → Prop) (hopp : ∀ i, ¬ Adj (u i) (u (opposite i)))
    (p : α)
    (hexternal : (∀ i, u i ≠ p) →
      ∀ i j, Adj p (u i) → Adj p (u j) → i = j) :
    ∃ i, u i ≠ p ∧ ¬ Adj p (u i) := by
  classical
  by_cases hp : ∃ i, u i = p
  · obtain ⟨i, rfl⟩ := hp
    exact ⟨opposite i, opposite_uncovered u hu Adj hopp i⟩
  · have hp' : ∀ i, u i ≠ p := by simpa only [not_exists] using hp
    by_cases h0 : Adj p (u 0)
    · refine ⟨1, hp' 1, ?_⟩
      intro h1
      have h := hexternal hp' 0 1 h0 h1
      contradiction
    · exact ⟨0, hp' 0, h0⟩

theorem sameBlock_pairs (i j : Fin 4) (h : SameBlock i j) :
    ((i = 0 ∨ i = 2) ∧ (j = 0 ∨ j = 2)) ∨
      ((i = 1 ∨ i = 3) ∧ (j = 1 ∨ j = 3)) := by
  fin_cases i <;> fin_cases j <;> simp_all [SameBlock]

theorem common_block_or_adjacent [DecidableEq α] (u : Fin 4 → α)
    (Adj : α → α → Prop) (hsymm : ∀ x y, Adj x y → Adj y x)
    (hcycle : ∀ i : Fin 4, Adj (u i) (u (i + 1)))
    {x y : α} (hx : x ∈ designated u) (hy : y ∈ designated u) :
    (x ∈ evenBlock u ∧ y ∈ evenBlock u) ∨
      (x ∈ oddBlock u ∧ y ∈ oddBlock u) ∨ Adj x y := by
  obtain ⟨i, rfl⟩ := (mem_designated u x).1 hx
  obtain ⟨j, rfl⟩ := (mem_designated u y).1 hy
  rcases sameBlock_or_consecutive i j with h | h
  · rcases sameBlock_pairs i j h with h | h
    · left
      simpa only [evenBlock, Finset.mem_insert, Finset.mem_singleton] using
        And.intro (h.1.imp (congrArg u) (congrArg u))
          (h.2.imp (congrArg u) (congrArg u))
    · right; left
      simpa only [oddBlock, Finset.mem_insert, Finset.mem_singleton] using
        And.intro (h.1.imp (congrArg u) (congrArg u))
          (h.2.imp (congrArg u) (congrArg u))
  · right; right
    exact adjacency_of_separated u Adj hsymm hcycle
      ((not_sameBlock_iff_consecutive i j).2 h)

end Balanced.FourCycle

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ValidChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

variable {F : Type*} [Field F]

namespace SplitGeometry

theorem adjacent_symm {M : MergedPairs F} {S : Line F} {p r : Point F}
    (h : Adjacent M S p r) : Adjacent M S r p := by
  rcases h with ⟨hp, hr, hne, d, hd, h⟩
  refine ⟨hr, hp, hne.symm, d, hd, ?_⟩
  exact h.elim (fun h => Or.inr ⟨h.2, h.1⟩) (fun h => Or.inl ⟨h.2, h.1⟩)

theorem intersection_on_left (l m : Line F) : OnLine (lineIntersection l m) l := by
  obtain ⟨d, b⟩ := l
  obtain ⟨e, c⟩ := m
  cases d <;> cases e <;> simp [OnLine, lineIntersection, lineEval]

theorem intersection_on_right (l m : Line F) (h : l.1 ≠ m.1) :
    OnLine (lineIntersection l m) m := by
  obtain ⟨d, b⟩ := l
  obtain ⟨e, c⟩ := m
  cases d with
  | none =>
    cases e with
    | none => exact False.elim (h rfl)
    | some e => simp [OnLine, lineIntersection, lineEval]
  | some d =>
    cases e with
    | none => rfl
    | some e =>
      have hde : d ≠ e := fun he => h (congrArg some he)
      change d * ((c - b) / (d - e)) + b - e * ((c - b) / (d - e)) = c
      field_simp [sub_ne_zero.mpr hde]
      ring

variable [Fintype F] [DecidableEq F]

variable {M : MergedPairs F} {g : Direction F} {C : SplitChoice F}

theorem valid_no_opposite (h : ValidChoice M g C) (i : Fin 4) :
    ¬ Adjacent M C.line (tuplePoint M C.tuple i)
      (tuplePoint M C.tuple (FourCycle.opposite i)) := by
  rcases h with ⟨_, _, _, _, _, _, h0, h1, _⟩
  fin_cases i
  · simpa [FourCycle.opposite] using h0
  · simpa [FourCycle.opposite] using h1
  · simpa [FourCycle.opposite] using fun ha => h0 (adjacent_symm ha)
  · simpa [FourCycle.opposite] using fun ha => h1 (adjacent_symm ha)

theorem valid_external_unique (h : ValidChoice M g C) (p : Point F)
    (hp : OnLine p C.line) (hext : p ∉ designated M C)
    (i j : Fin 4) (hi : Adjacent M C.line p (tuplePoint M C.tuple i))
    (hj : Adjacent M C.line p (tuplePoint M C.tuple j)) : i = j := by
  apply Finset.card_le_one.mp (h.2.2.2.2.2.2.2.2 p hp hext)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hj

theorem valid_exists_uncovered (h : ValidChoice M g C) (p : Point F)
    (hp : OnLine p C.line) :
    ∃ i, tuplePoint M C.tuple i ≠ p ∧ ¬ Adjacent M C.line p (tuplePoint M C.tuple i) := by
  apply FourCycle.exists_uncovered (tuplePoint M C.tuple) h.2.2.2.2.1
    (Adjacent M C.line) (valid_no_opposite h) p
  intro hext i j hi hj
  apply valid_external_unique h p hp ?_ i j hi hj
  intro hm
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hm
  exact hext k hk

theorem valid_not_covered (h : ValidChoice M g C) (p : Point F)
    (hp : OnLine p C.line) (Covered : Point F → Prop)
    (htrace : ∀ x ∈ designated M C, Covered x → x = p ∨ Adjacent M C.line p x) :
    ¬ ∀ x ∈ designated M C, Covered x := by
  obtain ⟨i, hne, hna⟩ := valid_exists_uncovered h p hp
  have hi : tuplePoint M C.tuple i ∈ designated M C :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  intro hall
  exact (htrace _ hi (hall _ hi)).elim hne hna

theorem valid_consecutive_adjacent (h : ValidChoice M g C) (i : Fin 4) :
    Adjacent M C.line (tuplePoint M C.tuple i) (tuplePoint M C.tuple (i + 1)) := by
  rcases h with ⟨hdir, _, hgen, havoid, hpoints, hon, _, _, _⟩
  have hnext : i ≠ i + 1 := by fin_cases i <;> decide
  have hd : (constituent M (C.tuple.generator i) (C.tuple.side i)).1 ≠
      (constituent M (C.tuple.generator (i + 1)) (!(C.tuple.side (i + 1)))).1 :=
    fun he => hnext (hgen he)
  have hi := intersection_on_right
    (constituent M (C.tuple.generator i) (C.tuple.side i))
    (constituent M (C.tuple.generator (i + 1)) (!(C.tuple.side (i + 1)))) hd
  have hj := intersection_on_left
    (constituent M (C.tuple.generator (i + 1)) (C.tuple.side (i + 1)))
    (constituent M (C.tuple.generator ((i + 1) + 1))
      (!(C.tuple.side ((i + 1) + 1))))
  change OnLine (tuplePoint M C.tuple i)
    (constituent M (C.tuple.generator (i + 1)) (!(C.tuple.side (i + 1)))) at hi
  change OnLine (tuplePoint M C.tuple (i + 1))
    (constituent M (C.tuple.generator (i + 1)) (C.tuple.side (i + 1))) at hj
  refine ⟨hon i, hon (i + 1), fun he => hnext (hpoints he),
    C.tuple.generator (i + 1), ?_, ?_⟩
  · simpa only [hdir] using havoid (i + 1)
  · cases hb : C.tuple.side (i + 1)
    · right
      simpa only [hb, Bool.not_false] using And.intro hi hj
    · left
      simpa only [hb, Bool.not_true] using And.intro hi hj

theorem adjacent_mem_merged {M : MergedPairs F} {S : Line F} {p r : Point F}
    (h : Adjacent M S p r) : ∃ d, p ∈ mergedPoints M d ∧ r ∈ mergedPoints M d := by
  rcases h with ⟨_, _, _, d, _, h⟩
  refine ⟨d, ?_⟩
  simp only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact h.elim (fun h => ⟨Or.inl h.1, Or.inr h.2⟩)
    (fun h => ⟨Or.inr h.1, Or.inl h.2⟩)

theorem valid_common_block_or_merged (h : ValidChoice M g C)
    {x y : Point F} (hx : x ∈ designated M C) (hy : y ∈ designated M C) :
    (x ∈ FourCycle.evenBlock (tuplePoint M C.tuple) ∧
      y ∈ FourCycle.evenBlock (tuplePoint M C.tuple)) ∨
    (x ∈ FourCycle.oddBlock (tuplePoint M C.tuple) ∧
      y ∈ FourCycle.oddBlock (tuplePoint M C.tuple)) ∨
    ∃ d, x ∈ mergedPoints M d ∧ y ∈ mergedPoints M d := by
  have hpair := FourCycle.common_block_or_adjacent (tuplePoint M C.tuple)
    (Adjacent M C.line) (fun _ _ => adjacent_symm)
    (valid_consecutive_adjacent h) hx hy
  exact hpair.imp_right (Or.imp_right adjacent_mem_merged)

theorem selected_designated_mem_points (C : Configuration F) (s : Slot F)
    {x : Point F} (hx : x ∈ designated C.merged (C.choice s)) : x ∈ C.points := by
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hx⟩

theorem selected_pair_common_block (C : Configuration F) (h : C.Valid)
    (s : Slot F) {x y : Point F}
    (hx : x ∈ designated C.merged (C.choice s))
    (hy : y ∈ designated C.merged (C.choice s)) :
    ∃ b ∈ C.blockLabels, x ∈ C.blockPoints b ∧ y ∈ C.blockPoints b := by
  classical
  rcases valid_common_block_or_merged (h.2 s) hx hy with he | ho | hm
  · refine ⟨Sum.inr (Sum.inr (s, false)), ?_, he⟩
    simp [Configuration.blockLabels, Configuration.IsBlockLabel]
  · refine ⟨Sum.inr (Sum.inr (s, true)), ?_, ho⟩
    simp [Configuration.blockLabels, Configuration.IsBlockLabel]
  · obtain ⟨d, hxM, hyM⟩ := hm
    refine ⟨Sum.inr (Sum.inl d), ?_, ?_, ?_⟩
    · simp [Configuration.blockLabels, Configuration.IsBlockLabel]
    · exact Finset.mem_inter.mpr ⟨hxM, selected_designated_mem_points C s hx⟩
    · exact Finset.mem_inter.mpr ⟨hyM, selected_designated_mem_points C s hy⟩

end SplitGeometry
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ConfigurationStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ConfigurationStructure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

omit [Field F] in

theorem choice_line_mem_split (s : Slot F) : (C.choice s).line ∈ C.splitLines := by
  exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, rfl⟩

theorem choice_designated_subset (hV : C.Valid) (s : Slot F) :
    designated C.merged (C.choice s) ⊆ linePoints (C.choice s).line := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  have hOn := (hV.2 s).2.2.2.2.2.1 i
  simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and] using hOn

theorem choice_designated_card (hV : C.Valid) (s : Slot F) :
    (designated C.merged (C.choice s)).card = 4 := by
  rw [designated, Finset.card_image_of_injective _ (hV.2 s).2.2.2.2.1]
  simp

theorem choice_designated_disjoint (hV : C.Valid) (hC : C.Compatible)
    {i j : Slot F} (hij : i ≠ j) :
    Disjoint (designated C.merged (C.choice i)) (designated C.merged (C.choice j)) := by
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  have hpOn : OnLine p (C.choice i).line := by
    simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and]
      using choice_designated_subset C hV i hpi
  exact hC.1 i j hij p hpj hpOn

theorem designated_subset_points (s : Slot F) :
    designated C.merged (C.choice s) ⊆ C.points := by
  intro p hp
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hp⟩)

theorem split_inter_points (hV : C.Valid) (hC : C.Compatible) (s : Slot F) :
    linePoints (C.choice s).line ∩ C.points = designated C.merged (C.choice s) := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpLine, hpX⟩ := Finset.mem_inter.mp hp
    have hpOn : OnLine p (C.choice s).line := by
      simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and] using hpLine
    rcases Finset.mem_union.mp hpX with hpR | hpF
    · have hpAvoid := (Finset.mem_filter.mp hpR).2
      exact False.elim (hpAvoid _ (choice_line_mem_split C s) hpOn)
    · obtain ⟨t, _, hpt⟩ := Finset.mem_biUnion.mp hpF
      have hts := designated_slot_unique C hC hpt hpOn
      simpa only [hts] using hpt
  · intro hp
    exact Finset.mem_inter.mpr
      ⟨choice_designated_subset C hV s hp, designated_subset_points C s hp⟩

theorem designated_at_card (hV : C.Valid) (hC : C.Compatible) (p : Point F) :
    (C.designatedAt p).card = 4 * C.splitMultiplicity p := by
  unfold Configuration.designatedAt
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun s _ => choice_designated_card C hV s)]
    simp only [Finset.sum_const, smul_eq_mul]
    rw [split_multiplicity_eq_slots C hV hC p]
    omega
  · intro i _ j _ hij
    exact choice_designated_disjoint C hV hC hij

theorem split_multiplicity_le_one_of_designated (hC : C.Compatible)
    {s : Slot F} {p : Point F} (hp : p ∈ designated C.merged (C.choice s)) :
    C.splitMultiplicity p ≤ 1 := by
  have hsub : C.splitLinesAt p ⊆ {(C.choice s).line} := by
    intro l hl
    obtain ⟨hlS, hpl⟩ := Finset.mem_filter.mp hl
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hlS
    have hst := designated_slot_unique C hC hp hpl
    simp only [Finset.mem_singleton]
    rw [hst]
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_singleton, Configuration.splitMultiplicity] using hc

theorem center_not_designated (hC : C.Compatible) {p : Point F}
    (hb : 2 ≤ C.splitMultiplicity p) (s : Slot F) :
    p ∉ designated C.merged (C.choice s) := by
  intro hp
  have hle := split_multiplicity_le_one_of_designated C hC hp
  omega

theorem split_lines_in_direction (hV : C.Valid) (g : Direction F) :
    C.splitLines.filter (fun l => l.1 = g) =
      {(C.choice (g, false)).line, (C.choice (g, true)).line} := by
  ext l
  constructor
  · intro hl
    obtain ⟨hlS, hdir⟩ := Finset.mem_filter.mp hl
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hlS
    have hs : s.1 = g := (hV.2 s).1.symm.trans hdir
    rcases s with ⟨d, b⟩
    dsimp at hs
    subst d
    cases b <;> simp
  · intro hl
    rcases Finset.mem_insert.mp hl with rfl | hl
    · exact Finset.mem_filter.mpr
        ⟨choice_line_mem_split C (g, false), (hV.2 (g, false)).1⟩
    · have heq := Finset.mem_singleton.mp hl
      subst l
      exact Finset.mem_filter.mpr
        ⟨choice_line_mem_split C (g, true), (hV.2 (g, true)).1⟩

theorem split_pair_ne (hV : C.Valid) (hC : C.Compatible) (g : Direction F) :
    (C.choice (g, false)).line ≠ (C.choice (g, true)).line := by
  intro h
  have hslots := choice_line_injective C hV hC h
  have hb := congrArg Prod.snd hslots
  cases hb

theorem choice_line_ne_constituent (hV : C.Valid) (s : Slot F)
    (d : Direction F) (b : Bool) :
    (C.choice s).line ≠ constituent C.merged d b := by
  intro h
  apply (hV.2 s).2.1
  exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, h.symm⟩

theorem deleted_lines_in_direction (hV : C.Valid) (g : Direction F) :
    C.deletedLines.filter (fun l => l.1 = g) =
      {(C.choice (g, false)).line, (C.choice (g, true)).line,
        constituent C.merged g true} := by
  ext l
  constructor
  · intro hl
    obtain ⟨hlD, hdir⟩ := Finset.mem_filter.mp hl
    rcases Finset.mem_union.mp hlD with hlS | hlM
    · have hp : l ∈ C.splitLines.filter (fun L => L.1 = g) :=
        Finset.mem_filter.mpr ⟨hlS, hdir⟩
      rw [split_lines_in_direction C hV g] at hp
      rcases Finset.mem_insert.mp hp with h | h
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl h
      · simp only [Finset.mem_singleton] at h
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inr (Or.inl h)
    · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hlM
      change d = g at hdir
      subst d
      simp
  · intro hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (choice_line_mem_split C (g, false)),
          (hV.2 (g, false)).1⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_left _ (choice_line_mem_split C (g, true)),
          (hV.2 (g, true)).1⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, Finset.mem_univ _, rfl⟩), rfl⟩

theorem deleted_lines_in_direction_card (hV : C.Valid) (hC : C.Compatible)
    (g : Direction F) : (C.deletedLines.filter (fun l => l.1 = g)).card = 3 := by
  rw [deleted_lines_in_direction C hV g]
  simp [split_pair_ne C hV hC g,
    choice_line_ne_constituent C hV (g, false) g true,
    choice_line_ne_constituent C hV (g, true) g true]

end ConfigurationStructure
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BlockIntersection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem mem_merged_of_on_constituent (M : MergedPairs F)
    (d : Direction F) (s : Bool) {x : Point F}
    (hx : OnLine x (constituent M d s)) : x ∈ mergedPoints M d := by
  simp only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases s
  · exact Or.inl hx
  · exact Or.inr hx

theorem points_nonempty (C : Configuration F) : C.points.Nonempty := by
  let s : Slot F := (none, false)
  refine ⟨tuplePoint C.merged (C.choice s).tuple 0, ?_⟩
  apply SplitGeometry.selected_designated_mem_points C s
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩

theorem pair_common_block (C : Configuration F) (hV : C.Valid) (hC : C.Compatible)
    {x y : Point F} (hx : x ∈ C.points) (hy : y ∈ C.points) :
    ∃ b ∈ C.blockLabels, x ∈ C.blockPoints b ∧ y ∈ C.blockPoints b := by
  classical
  by_cases hs : joiningLine x y ∈ C.splitLines
  · obtain ⟨s, _, hline⟩ := Finset.mem_image.mp hs
    have hxd : x ∈ designated C.merged (C.choice s) := by
      rw [← ConfigurationStructure.split_inter_points C hV hC s]
      refine Finset.mem_inter.mpr ⟨?_, hx⟩
      simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and, hline]
        using onLine_joiningLine_left x y
    have hyd : y ∈ designated C.merged (C.choice s) := by
      rw [← ConfigurationStructure.split_inter_points C hV hC s]
      refine Finset.mem_inter.mpr ⟨?_, hy⟩
      simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and, hline]
        using onLine_joiningLine_right x y
    exact SplitGeometry.selected_pair_common_block C hV s hxd hyd
  · by_cases hm : joiningLine x y ∈ constituentLines C.merged
    · obtain ⟨ds, _, hline⟩ := Finset.mem_image.mp hm
      refine ⟨Sum.inr (Sum.inl ds.1), ?_, ?_, ?_⟩
      · simp [blockLabels, IsBlockLabel]
      · apply Finset.mem_inter.mpr
        refine ⟨mem_merged_of_on_constituent C.merged ds.1 ds.2 ?_, hx⟩
        rw [hline]
        exact onLine_joiningLine_left x y
      · apply Finset.mem_inter.mpr
        refine ⟨mem_merged_of_on_constituent C.merged ds.1 ds.2 ?_, hy⟩
        rw [hline]
        exact onLine_joiningLine_right x y
    · refine ⟨Sum.inl (joiningLine x y), ?_, ?_, ?_⟩
      · simp [blockLabels, IsBlockLabel, hs, hm]
      · apply Finset.mem_inter.mpr
        refine ⟨?_, hx⟩
        simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and]
          using onLine_joiningLine_left x y
      · apply Finset.mem_inter.mpr
        refine ⟨?_, hy⟩
        simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and]
          using onLine_joiningLine_right x y

end Configuration
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ConfigurationBlockCardinality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

lemma core_subset_points : C.core ⊆ C.points := by
  intro p hp
  apply Finset.mem_union.mpr
  left
  simp only [core, retained, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  intro l hl
  exact hp l (Finset.mem_union_left _ hl)

omit [Field F] in
lemma deletedLines_subset_special : C.deletedLines ⊆ C.splitLines ∪ constituentLines C.merged := by
  intro l hl
  rcases Finset.mem_union.mp hl with hs | hm
  · exact Finset.mem_union_left _ hs
  · rcases Finset.mem_image.mp hm with ⟨d, _, rfl⟩
    exact Finset.mem_union_right _ (C.constituent_mem_lines d true)

lemma zero_constituent_not_deleted (hV : C.Valid) (d : Direction F) :
    constituent C.merged d false ∉ C.deletedLines := by
  intro hl
  rcases Finset.mem_union.mp hl with hs | hm
  · exact Finset.disjoint_left.mp (C.split_disjoint_constituent hV) hs
      (C.constituent_mem_lines d false)
  · rcases Finset.mem_image.mp hm with ⟨g, _, heq⟩
    have hgd : g = d := congrArg Prod.fst heq
    subst g
    exact hV.1 d (congrArg Prod.snd heq).symm

lemma core_line_nonempty {ρ : ℝ} {B : ℕ} (hρ : 0 < ρ) (hO : C.Occupancy ρ B)
    (l : Line F) (hl : l ∉ C.deletedLines) : (linePoints l ∩ C.core).Nonempty := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < ((linePoints l ∩ C.core).card : ℝ) :=
    lt_of_lt_of_le (mul_pos hρ hq) (hO.2.1 l hl)
  apply Finset.card_pos.mp
  exact_mod_cast hpos

theorem blockPoints_nonempty (hV : C.Valid) {ρ : ℝ} {B : ℕ}
    (hρ : 0 < ρ) (hO : C.Occupancy ρ B)
    (b : BlockLabel F) (hb : C.IsBlockLabel b) : (C.blockPoints b).Nonempty := by
  rcases b with l | (d | ⟨s, b⟩)
  · have hld : l ∉ C.deletedLines := fun h => hb (C.deletedLines_subset_special h)
    rcases C.core_line_nonempty hρ hO l hld with ⟨p, hp⟩
    rcases Finset.mem_inter.mp hp with ⟨hlp, hpc⟩
    exact ⟨p, Finset.mem_inter.mpr ⟨hlp, C.core_subset_points hpc⟩⟩
  · rcases C.core_line_nonempty hρ hO (constituent C.merged d false)
      (C.zero_constituent_not_deleted hV d) with ⟨p, hp⟩
    rcases Finset.mem_inter.mp hp with ⟨hlp, hpc⟩
    exact ⟨p, Finset.mem_inter.mpr
      ⟨Finset.mem_union_left _ hlp, C.core_subset_points hpc⟩⟩
  · cases b <;> simp [blockPoints]

lemma designated_subset_points (s : Slot F) :
    designated C.merged (C.choice s) ⊆ C.points := by
  intro p hp
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hp⟩)

lemma blockPoints_subset_points (b : BlockLabel F) : C.blockPoints b ⊆ C.points := by
  rcases b with l | (d | ⟨s, b⟩)
  · exact Finset.inter_subset_right
  · exact Finset.inter_subset_right
  · have hi : ∀ i : Fin 4, tuplePoint C.merged (C.choice s).tuple i ∈ C.points := by
      intro i
      exact C.designated_subset_points s (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    cases b <;> simp [blockPoints, Finset.insert_subset_iff, hi]

end
end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PointEdgeInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

theorem point_assignment_injective_of_few_merged
    {G X : Type*} [Fintype G] [DecidableEq G]
    {Label : G → Type*}
    (label : (g : G) → X → Label g)
    (joining : X → X → G)
    (mergedAt : X → Finset G)
    (few_merged : ∀ x, (mergedAt x).card + 1 < Fintype.card G)
    (cross_direction : ∀ x y, x ≠ y → ∀ g, g ≠ joining x y →
      label g x = label g y → g ∈ mergedAt x) :
    Function.Injective (fun x g => label g x) := by
  intro x y hlabels
  by_contra hxy
  have hsub : Finset.univ.erase (joining x y) ⊆ mergedAt x := by
    intro g hg
    exact cross_direction x y hxy g (Finset.mem_erase.mp hg).1
      (congrFun hlabels g)
  have hcard := Finset.card_le_card hsub
  have hsize : (Finset.univ.erase (joining x y)).card = Fintype.card G - 1 := by
    simp
  have hfew := few_merged x
  omega

theorem multiplicity_lt_order_of_size_condition
    {q B : ℕ} {ρ : ℝ}
    (hρ : ρ < 1) (hq : 0 ≤ (q : ℝ))
    (hsize : 2 * (1 + (B : ℝ)) < ρ * q) : B < q := by
  have hmul : ρ * (q : ℝ) ≤ q := mul_le_of_le_one_left hq (le_of_lt hρ)
  have hreal : (B : ℝ) < q := by linarith
  exact_mod_cast hreal

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PointLabelInjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration.BlockPartitions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {C : Configuration F}

theorem mergedDirectionsAt_card_le (p : Point F) :
    (mergedDirectionsAt C p).card ≤
      ((constituentLines C.merged).filter (OnLine p)).card :=
  Finset.card_image_le

theorem mergedDirection_mem_of_block {p : Point F} {d : Direction F}
    (hp : p ∈ C.blockPoints (Sum.inr (Sum.inl d))) :
    d ∈ mergedDirectionsAt C p := by
  obtain ⟨b, hb⟩ := merged_block_onLine hp
  exact Finset.mem_image.mpr ⟨constituent C.merged d b,
    Finset.mem_filter.mpr ⟨constituent_mem d b, hb⟩, rfl⟩

theorem same_label_off_join_merged (hV : C.Valid) (hC : C.Compatible)
    (p q : {p // p ∈ C.points}) (hpq : p ≠ q) (d : Direction F)
    (hd : d ≠ (joiningLine p.val q.val).1)
    (heq : pointLabel hV hC d p = pointLabel hV hC d q) :
    d ∈ mergedDirectionsAt C p.val := by
  have hpq' : p.val ≠ q.val := fun h => hpq (Subtype.ext h)
  let b := pointLabel hV hC d p
  have hpb : p.val ∈ C.blockPoints b.val := pointLabel_mem hV hC d p
  have hqb : q.val ∈ C.blockPoints b.val := by
    change q.val ∈ C.blockPoints (pointLabel hV hC d p).val
    rw [heq]
    exact pointLabel_mem hV hC d q
  have hdir : blockDirection b.val = d := (Finset.mem_filter.mp b.property).2
  rcases hval : b.val with l | (g | ⟨s, c⟩)
  · rw [hval] at hpb hqb hdir
    have hl := eq_of_two_common_points p.val q.val hpq' l (joiningLine p.val q.val)
      (regular_block_onLine hpb) (regular_block_onLine hqb)
      (onLine_joiningLine_left _ _) (onLine_joiningLine_right _ _)
    exact (hd (hdir.symm.trans (congrArg Prod.fst hl))).elim
  · rw [hval] at hpb hdir
    have hm := mergedDirection_mem_of_block hpb
    simpa only [blockDirection] using hdir ▸ hm
  · rw [hval] at hpb hqb hdir
    have hl := eq_of_two_common_points p.val q.val hpq' (C.choice s).line
      (joiningLine p.val q.val) (split_block_onLine hV s c hpb)
      (split_block_onLine hV s c hqb)
      (onLine_joiningLine_left _ _) (onLine_joiningLine_right _ _)
    apply False.elim
    apply hd
    exact hdir.symm.trans ((split_direction hV s).symm.trans (congrArg Prod.fst hl))

theorem pointLabel_injective (hV : C.Valid) (hC : C.Compatible)
    {B : ℕ} (hB : B < Fintype.card F)
    (hocc : ∀ p, ((constituentLines C.merged).filter (OnLine p)).card ≤ B) :
    Function.Injective (fun p d => pointLabel hV hC d p) := by
  apply Balanced.point_assignment_injective_of_few_merged
    (pointLabel hV hC)
    (fun p q => (joiningLine p.val q.val).1)
    (fun p => mergedDirectionsAt C p.val)
  · intro p
    have hle := (mergedDirectionsAt_card_le (C := C) p.val).trans (hocc p.val)
    simp only [Direction, Fintype.card_option]
    omega
  · exact same_label_off_join_merged hV hC

theorem pointLabel_injective_of_occupancy (hV : C.Valid) (hC : C.Compatible)
    {ρ : ℝ} {B : ℕ} (hρ : ρ < 1) (hocc : C.Occupancy ρ B)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * Fintype.card F) :
    Function.Injective (fun p d => pointLabel hV hC d p) := by
  apply pointLabel_injective hV hC
    (Balanced.multiplicity_lt_order_of_size_condition hρ (by positivity) hsize)
  exact hocc.1

end Balanced.Configuration.BlockPartitions

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ConfigurationHypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

open BlockPartitions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem pointLabel_surjective (hV : C.Valid) (hC : C.Compatible)
    {ρ : ℝ} {B : ℕ} (hρ : 0 < ρ) (hO : C.Occupancy ρ B) (d : Direction F) :
    Function.Surjective (pointLabel hV hC d) := by
  classical
  intro b
  have hb : C.IsBlockLabel b.val :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp b.property).1).2
  obtain ⟨p, hp⟩ := C.blockPoints_nonempty hV hρ hO b.val hb
  let x : {p // p ∈ C.points} := ⟨p, C.blockPoints_subset_points b.val hp⟩
  exact ⟨x, (pointLabel_eq_iff hV hC d x b).mpr hp⟩

theorem pointLabel_agrees (hV : C.Valid) (hC : C.Compatible)
    (p q : {p // p ∈ C.points}) :
    ∃ d, pointLabel hV hC d p = pointLabel hV hC d q := by
  obtain ⟨b, hb, hp, hq⟩ := C.pair_common_block hV hC p.property q.property
  let d := blockDirection b
  have hbDir : b ∈ C.labelsInDirection d :=
    Finset.mem_filter.mpr ⟨hb, rfl⟩
  let b' : {b // b ∈ C.labelsInDirection d} := ⟨b, hbDir⟩
  refine ⟨d, ?_⟩
  exact ((pointLabel_eq_iff hV hC d p b').mpr hp).trans
    ((pointLabel_eq_iff hV hC d q b').mpr hq).symm

theorem constructedHypergraph_nonisolated (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) {ρ : ℝ} {B : ℕ}
    (hρ : 0 < ρ) (hO : C.Occupancy ρ B) :
    (C.constructedHypergraph hV hC hq).Nonisolated :=
  partitionHypergraph_nonisolated _ _ _ (C.pointLabel_surjective hV hC hρ hO)

theorem constructedHypergraph_intersecting (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) :
    (C.constructedHypergraph hV hC hq).Intersecting := by
  have : Nonempty {p // p ∈ C.points} := C.points_nonempty.to_subtype
  exact partitionHypergraph_intersecting _ _ _ (C.pointLabel_agrees hV hC)

theorem constructedHypergraph_represents (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) {ρ : ℝ} {B : ℕ}
    (hρ : ρ < 1) (hO : C.Occupancy ρ B)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * Fintype.card F) :
    C.Represents (C.constructedHypergraph hV hC hq) := by
  let eD := directionEquiv (F := F)
  let eL := C.blockLabelEquiv hV hC hq
  have hinj := pointLabel_injective_of_occupancy hV hC hρ hO hsize
  refine ⟨eD, eL, partitionHypergraph_edgeEquiv eD eL (pointLabel hV hC) hinj, ?_⟩
  intro p d b
  change p.val ∈ C.blockPoints b.val ↔
    encodeAssignment eD eL (pointLabel hV hC) p (eD d) = eL d b
  rw [encodeAssignment_apply_index]
  exact (pointLabel_eq_iff hV hC d p b).symm.trans (eL d).apply_eq_iff_eq.symm

theorem constructedHypergraph_hasCoverNumber (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F)
    (hcover : ∀ A : Finset (BlockLabel F), A ⊆ C.blockLabels →
      C.points ⊆ A.biUnion C.blockPoints → Fintype.card F + 1 ≤ A.card) :
    (C.constructedHypergraph hV hC hq).HasCoverNumber (Fintype.card F + 1) := by
  classical
  apply partitionHypergraph_hasCoverNumber
  intro D hD
  let A : Finset (BlockLabel F) := D.image (fun v => v.2.val)
  have hA : A ⊆ C.blockLabels := by
    intro b hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact (Finset.mem_filter.mp v.2.property).1
  have hAcovers : C.points ⊆ A.biUnion C.blockPoints := by
    intro p hp
    obtain ⟨d, hd⟩ := hD ⟨p, hp⟩
    refine Finset.mem_biUnion.mpr ⟨(pointLabel hV hC d ⟨p, hp⟩).val, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨d, pointLabel hV hC d ⟨p, hp⟩⟩, hd, rfl⟩
    · exact pointLabel_mem hV hC d ⟨p, hp⟩
  exact (hcover A hA hAcovers).trans Finset.card_image_le

end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ConfigurationRealizationBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem Represents.realization
    {H : PartiteHypergraph (Fintype.card F + 1) (Fintype.card F + 1)}
    (h : C.Represents H) : Nonempty (ConfigurationRealization C H) := by
  rcases h with ⟨eD, eL, eP, hinc⟩
  refine ⟨{
    directionEquiv := eD
    labelEquiv := (C.blockLabelDirectionEquiv).trans (encodeLabel eD eL)
    edgeEquiv := eP
    label_direction := ?_
    incidence := ?_
  }⟩
  · intro b
    rfl
  · intro p b
    exact hinc p (blockDirection b.val)
      ⟨b.val, Finset.mem_filter.mpr ⟨b.property, rfl⟩⟩

theorem constructedHypergraph_realization (hV : C.Valid) (hC : C.Compatible)
    (hq : 4 ≤ Fintype.card F) {ρ : ℝ} {B : ℕ}
    (hρ : ρ < 1) (hO : C.Occupancy ρ B)
    (hsize : 2 * (1 + (B : ℝ)) < ρ * Fintype.card F) :
    Nonempty (ConfigurationRealization C (C.constructedHypergraph hV hC hq)) :=
  (C.constructedHypergraph_represents hV hC hq hρ hO hsize).realization C

end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ConstructionStructure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace ConstructionStructure

section FiniteDesignatedSets

variable {P I : Type*} [DecidableEq P]

theorem partner_card_le_slots (s : Finset I) (F : I → Finset P) (Z : Finset P)
    (hsub : Z ⊆ s.biUnion F)
    (hone : ∀ i ∈ s, (Z ∩ F i).card ≤ 1) : Z.card ≤ s.card := by
  have hcover : Z ⊆ s.biUnion (fun i => Z ∩ F i) := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp (hsub hp)
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hp, hpi⟩⟩
  calc
    Z.card ≤ (s.biUnion (fun i => Z ∩ F i)).card := Finset.card_le_card hcover
    _ ≤ ∑ i ∈ s, (Z ∩ F i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ s, 1 := Finset.sum_le_sum hone
    _ = s.card := by simp

end FiniteDesignatedSets

end ConstructionStructure
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ConstructionPartners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.ConstructionPartners

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

private theorem designated_on_line (hV : C.Valid) (s : Slot F)
    {x : Point F} (hx : x ∈ designated C.merged (C.choice s)) :
    OnLine x (C.choice s).line := by
  rcases hV.2 s with ⟨_, _, _, _, _, hon, _⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact hon i

theorem partner_adjacent (hV : C.Valid) (s : Slot F) (p x : Point F)
    (hp : OnLine p (C.choice s).line)
    (hpnot : p ∉ designated C.merged (C.choice s))
    (hx : x ∈ C.partnerSet p ∩ designated C.merged (C.choice s)) :
    Adjacent C.merged (C.choice s).line p x := by
  classical
  obtain ⟨hxZ, hxF⟩ := Finset.mem_inter.mp hx
  obtain ⟨_, ⟨⟨d, b⟩, hpM, hxM⟩⟩ := Finset.mem_filter.mp hxZ
  have hxS := designated_on_line C hV s hxF
  have hne : p ≠ x := by
    intro heq
    subst x
    exact hpnot hxF
  have hd : d ≠ (C.choice s).line.1 := by
    intro heq
    have hline : (C.choice s).line = constituent C.merged d b := by
      apply Prod.ext heq.symm
      change (C.choice s).line.2 = C.merged d b
      change lineEval (C.choice s).line.1 p = (C.choice s).line.2 at hp
      change lineEval d p = C.merged d b at hpM
      calc
        (C.choice s).line.2 = lineEval (C.choice s).line.1 p := hp.symm
        _ = lineEval d p := by rw [heq]
        _ = C.merged d b := hpM
    apply (hV.2 s).2.1
    rw [hline]
    exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, rfl⟩
  refine ⟨hp, hxS, hne, d, hd, ?_⟩
  cases b with
  | false => exact Or.inl ⟨hpM, hxM⟩
  | true => exact Or.inr ⟨hpM, hxM⟩

theorem partner_inter_designated_card_le_one (hV : C.Valid)
    (s : Slot F) (p : Point F) (hp : OnLine p (C.choice s).line)
    (hpnot : p ∉ designated C.merged (C.choice s)) :
    (C.partnerSet p ∩ designated C.merged (C.choice s)).card ≤ 1 := by
  classical
  let I : Finset (Fin 4) := Finset.univ.filter
    (fun i => Adjacent C.merged (C.choice s).line p
      (tuplePoint C.merged (C.choice s).tuple i))
  have hsub : C.partnerSet p ∩ designated C.merged (C.choice s) ⊆
      I.image (tuplePoint C.merged (C.choice s).tuple) := by
    intro x hx
    have hadj := partner_adjacent C hV s p x hp hpnot hx
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_inter.mp hx).2
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, hi⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [hi] using hadj
  rcases hV.2 s with ⟨_, _, _, _, _, _, _, _, hext⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_image_le).trans (hext p hp hpnot))

theorem partner_inter_designated_card_le_one_of_two (hV : C.Valid)
    (hC : C.Compatible) (s : Slot F) (p : Point F)
    (hb : 2 ≤ C.splitMultiplicity p) (hp : OnLine p (C.choice s).line) :
    (C.partnerSet p ∩ designated C.merged (C.choice s)).card ≤ 1 :=
  partner_inter_designated_card_le_one C hV s p hp
    (ConfigurationStructure.center_not_designated C hC hb s)

theorem partner_card_le_splitMultiplicity (hV : C.Valid) (hC : C.Compatible)
    (p : Point F) (hb : 2 ≤ C.splitMultiplicity p) :
    (C.partnerSet p).card ≤ C.splitMultiplicity p := by
  classical
  rw [ConfigurationStructure.split_multiplicity_eq_slots C hV hC p]
  apply ConstructionStructure.partner_card_le_slots
    (Finset.univ.filter (fun s : Slot F => OnLine p (C.choice s).line))
    (fun s => designated C.merged (C.choice s)) (C.partnerSet p)
  · exact Finset.filter_subset _ _
  · intro s hs
    exact partner_inter_designated_card_le_one_of_two C hV hC s p hb
      (Finset.mem_filter.mp hs).2

theorem nonsplit_line_disjoint_designatedAt (hV : C.Valid) (hC : C.Compatible)
    (p : Point F) (hb : 2 ≤ C.splitMultiplicity p) (l : Line F)
    (hp : OnLine p l) (hl : l ∉ C.splitLinesAt p) :
    Disjoint (linePoints l) (C.designatedAt p) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxL hxF
  obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hxF
  have hpS := (Finset.mem_filter.mp hs).2
  have hS : (C.choice s).line ∈ C.splitLinesAt p :=
    Finset.mem_filter.mpr ⟨ConfigurationStructure.choice_line_mem_split C s, hpS⟩
  have hne : l ≠ (C.choice s).line := by
    intro heq
    exact hl (heq.symm ▸ hS)
  have hxp : x = p := common_point_eq_of_lines_ne l (C.choice s).line hne x p
    (Finset.mem_filter.mp hxL).2 (designated_on_line C hV s hxs) hp hpS
  exact ConfigurationStructure.center_not_designated C hC hb s (hxp ▸ hxs)

private theorem constituent_not_splitLinesAt (hV : C.Valid) (p : Point F)
    (d : Direction F) (b : Bool) :
    constituent C.merged d b ∉ C.splitLinesAt p := by
  intro h
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp (Finset.mem_filter.mp h).1
  apply (hV.2 s).2.1
  rw [hs]
  exact Finset.mem_image.mpr ⟨(d, b), Finset.mem_univ _, rfl⟩

theorem merged_inter_designatedAt_subset_partnerSet (hV : C.Valid)
    (hC : C.Compatible) (p : Point F) (hb : 2 ≤ C.splitMultiplicity p)
    (d : Direction F) (b : Bool) (hp : OnLine p (constituent C.merged d b)) :
    mergedPoints C.merged d ∩ C.designatedAt p ⊆ C.partnerSet p := by
  classical
  have hdis := nonsplit_line_disjoint_designatedAt C hV hC p hb
    (constituent C.merged d b) hp (constituent_not_splitLinesAt C hV p d b)
  intro x hx
  obtain ⟨hxM, hxF⟩ := Finset.mem_inter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hxF, (d, b), hp, ?_⟩
  cases b with
  | false =>
    rcases Finset.mem_union.mp hxM with hx0 | hx1
    · exact False.elim (Finset.disjoint_left.mp hdis hx0 hxF)
    · exact (Finset.mem_filter.mp hx1).2
  | true =>
    rcases Finset.mem_union.mp hxM with hx0 | hx1
    · exact (Finset.mem_filter.mp hx0).2
    · exact False.elim (Finset.disjoint_left.mp hdis hx1 hxF)

theorem regular_block_disjoint_designatedAt (hV : C.Valid) (hC : C.Compatible)
    (p : Point F) (hb : 2 ≤ C.splitMultiplicity p) (l : Line F)
    (hregular : C.IsBlockLabel (Sum.inl l)) (hp : OnLine p l) :
    Disjoint (C.blockPoints (Sum.inl l)) (C.designatedAt p) := by
  have hl : l ∉ C.splitLinesAt p := by
    intro h
    exact hregular (Finset.mem_union_left _ (Finset.mem_filter.mp h).1)
  exact (nonsplit_line_disjoint_designatedAt C hV hC p hb l hp hl).mono_left
    Finset.inter_subset_left

theorem merged_block_inter_designatedAt_subset_partnerSet (hV : C.Valid)
    (hC : C.Compatible) (p : Point F) (hb : 2 ≤ C.splitMultiplicity p)
    (d : Direction F) (b : Bool) (hp : OnLine p (constituent C.merged d b)) :
    C.blockPoints (Sum.inr (Sum.inl d)) ∩ C.designatedAt p ⊆ C.partnerSet p := by
  intro x hx
  apply merged_inter_designatedAt_subset_partnerSet C hV hC p hb d b hp
  exact Finset.mem_inter.mpr
    ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hx).1).1, (Finset.mem_inter.mp hx).2⟩

end
end Balanced.ConstructionPartners

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_CoverObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CoverObstruction

open scoped BigOperators

variable {α ι : Type*} [DecidableEq α]

theorem card_le_initial_add_sum_inter_card_of_cover
    (F Z : Finset α) (s : Finset ι) (block : ι → Finset α)
    (hcover : F ⊆ Z ∪ s.biUnion block) :
    F.card ≤ (F ∩ Z).card + ∑ i ∈ s, (F ∩ block i).card := by
  have hsub : F ⊆ (F ∩ Z) ∪ s.biUnion (fun i => F ∩ block i) := by
    intro x hx
    rcases Finset.mem_union.mp (hcover hx) with hz | hb
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, hz⟩)
    · obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hb
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨hx, hxi⟩⟩)
  calc
    F.card ≤ ((F ∩ Z) ∪ s.biUnion (fun i => F ∩ block i)).card :=
      Finset.card_le_card hsub
    _ ≤ (F ∩ Z).card + (s.biUnion (fun i => F ∩ block i)).card :=
      Finset.card_union_le _ _
    _ ≤ (F ∩ Z).card + ∑ i ∈ s, (F ∩ block i).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _

theorem card_le_initial_add_capacity_of_cover
    (F Z : Finset α) (s : Finset ι) (block : ι → Finset α) (capacity : ℕ)
    (hcover : F ⊆ Z ∪ s.biUnion block)
    (hcapacity : ∀ i ∈ s, (F ∩ block i).card ≤ capacity) :
    F.card ≤ Z.card + s.card * capacity := by
  calc
    F.card ≤ (F ∩ Z).card + ∑ i ∈ s, (F ∩ block i).card :=
      card_le_initial_add_sum_inter_card_of_cover F Z s block hcover
    _ ≤ Z.card + ∑ i ∈ s, capacity := by
      exact Nat.add_le_add (Finset.card_le_card Finset.inter_subset_right)
        (Finset.sum_le_sum hcapacity)
    _ = Z.card + s.card * capacity := by simp

variable [DecidableEq ι]

theorem cover_by_remaining_of_forced_disjoint
    (F : Finset α) (C forced : Finset ι) (block : ι → Finset α)
    (hcover : F ⊆ C.biUnion block)
    (hmiss : ∀ i ∈ forced, Disjoint F (block i)) :
    F ⊆ (C \ forced).biUnion block := by
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hcover hx)
  have hnot : i ∉ forced := by
    intro hif
    exact Finset.disjoint_left.mp (hmiss i hif) hx hxi
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_sdiff.mpr ⟨hi, hnot⟩, hxi⟩

omit [DecidableEq ι] in
theorem eight_points_not_covered_by_three_pairs
    (F : Finset α) (s : Finset ι) (block : ι → Finset α)
    (hF : F.card = 8) (hs : s.card ≤ 3)
    (hcapacity : ∀ i ∈ s, (F ∩ block i).card ≤ 2) :
    ¬ F ⊆ s.biUnion block := by
  intro hcover
  have h := card_le_initial_add_capacity_of_cover F ∅ s block 2
    (by simpa using hcover) hcapacity
  simp only [Finset.card_empty, zero_add] at h
  omega

omit [DecidableEq ι] in
theorem eight_points_not_covered_by_two_and_four
    (F Z : Finset α) (s : Finset ι) (block : ι → Finset α)
    (hF : F.card = 8) (hZ : Z.card ≤ 2) (hs : s.card ≤ 1)
    (hcapacity : ∀ i ∈ s, (F ∩ block i).card ≤ 4) :
    ¬ F ⊆ Z ∪ s.biUnion block := by
  intro hcover
  have h := card_le_initial_add_capacity_of_cover F Z s block 4 hcover hcapacity
  omega

end Balanced.CoverObstruction

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BlockCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

open scoped BigOperators
noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem linePoints_inter_card_le_one (l m : Line F) (hne : l ≠ m) :
    (linePoints l ∩ linePoints m).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  rcases Finset.mem_inter.mp hx with ⟨hxl, hxm⟩
  rcases Finset.mem_inter.mp hy with ⟨hyl, hym⟩
  exact common_point_eq_of_lines_ne l m hne x y
    (Finset.mem_filter.mp hxl).2 (Finset.mem_filter.mp hxm).2
    (Finset.mem_filter.mp hyl).2 (Finset.mem_filter.mp hym).2

theorem valid_split_not_constituent (hvalid : C.Valid)
    (l : Line F) (hl : l ∈ C.splitLines) : l ∉ constituentLines C.merged := by
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hl
  exact (hvalid.2 s).2.1

theorem constituent_not_splitLinesAt (hvalid : C.Valid)
    (p : Point F) (d : Direction F) (bit : Bool) :
    constituent C.merged d bit ∉ C.splitLinesAt p := by
  intro h
  apply C.valid_split_not_constituent hvalid _ (Finset.mem_filter.mp h).1
  exact Finset.mem_image.mpr ⟨(d, bit), Finset.mem_univ _, rfl⟩

theorem designatedAt_subset_splitLinesAt_union (hvalid : C.Valid) (p : Point F) :
    C.designatedAt p ⊆ (C.splitLinesAt p).biUnion linePoints := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxs
  rcases hvalid.2 s with ⟨_, _, _, _, _, hpoints, _, _, _⟩
  refine Finset.mem_biUnion.mpr ⟨(C.choice s).line, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
      ⟨s, Finset.mem_univ _, rfl⟩, (Finset.mem_filter.mp hs).2⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpoints i⟩

theorem designatedAt_inter_line_card_le (hvalid : C.Valid)
    (p : Point F) (l : Line F) (hline : l ∉ C.splitLinesAt p) :
    (C.designatedAt p ∩ linePoints l).card ≤ C.splitMultiplicity p := by
  have hsub : C.designatedAt p ∩ linePoints l ⊆
      (C.splitLinesAt p).biUnion (fun m => linePoints m ∩ linePoints l) := by
    intro x hx
    obtain ⟨hxd, hxl⟩ := Finset.mem_inter.mp hx
    obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.mp
      (C.designatedAt_subset_splitLinesAt_union hvalid p hxd)
    exact Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_inter.mpr ⟨hxm, hxl⟩⟩
  calc
    (C.designatedAt p ∩ linePoints l).card ≤
        ((C.splitLinesAt p).biUnion (fun m => linePoints m ∩ linePoints l)).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ m ∈ C.splitLinesAt p, (linePoints m ∩ linePoints l).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _m ∈ C.splitLinesAt p, 1 := by
      apply Finset.sum_le_sum
      intro m hm
      exact linePoints_inter_card_le_one m l (by intro heq; exact hline (heq ▸ hm))
    _ = C.splitMultiplicity p := by simp [splitMultiplicity]

theorem designatedAt_inter_merged_card_le (hvalid : C.Valid)
    (p : Point F) (d : Direction F) :
    (C.designatedAt p ∩ mergedPoints C.merged d).card ≤ 2 * C.splitMultiplicity p := by
  rw [mergedPoints, Finset.inter_union_distrib_left]
  calc
    _ ≤ (C.designatedAt p ∩ linePoints (constituent C.merged d false)).card +
        (C.designatedAt p ∩ linePoints (constituent C.merged d true)).card :=
      Finset.card_union_le _ _
    _ ≤ C.splitMultiplicity p + C.splitMultiplicity p :=
      Nat.add_le_add
        (C.designatedAt_inter_line_card_le hvalid p _
          (C.constituent_not_splitLinesAt hvalid p d false))
        (C.designatedAt_inter_line_card_le hvalid p _
          (C.constituent_not_splitLinesAt hvalid p d true))
    _ = 2 * C.splitMultiplicity p := by omega

theorem designatedAt_inter_block_card_le (hvalid : C.Valid)
    (p : Point F) (hb : 1 ≤ C.splitMultiplicity p)
    (label : BlockLabel F) (hlabel : C.IsBlockLabel label) :
    (C.designatedAt p ∩ C.blockPoints label).card ≤ 2 * C.splitMultiplicity p := by
  classical
  rcases label with l | d | ⟨s, bit⟩
  · have hline : l ∉ C.splitLinesAt p := by
      intro hl
      exact hlabel (Finset.mem_union_left _ (Finset.mem_filter.mp hl).1)
    have hsub : C.designatedAt p ∩ C.blockPoints (Sum.inl l) ⊆
        C.designatedAt p ∩ linePoints l := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
    exact (Finset.card_le_card hsub).trans
      ((C.designatedAt_inter_line_card_le hvalid p l hline).trans (by omega))
  · have hsub : C.designatedAt p ∩ C.blockPoints (Sum.inr (Sum.inl d)) ⊆
        C.designatedAt p ∩ mergedPoints C.merged d := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
    exact (Finset.card_le_card hsub).trans (C.designatedAt_inter_merged_card_le hvalid p d)
  · have hsmall : (C.blockPoints (Sum.inr (Sum.inr (s, bit)))).card ≤ 2 := by
      cases bit <;> exact Finset.card_le_two
    exact (Finset.card_le_card Finset.inter_subset_right).trans (hsmall.trans (by omega))

theorem two_split_block_capacity (hvalid : C.Valid)
    (p : Point F) (hb : C.splitMultiplicity p = 2)
    (label : BlockLabel F) (hlabel : C.IsBlockLabel label) :
    (C.designatedAt p ∩ C.blockPoints label).card ≤ 4 := by
  simpa [hb] using C.designatedAt_inter_block_card_le hvalid p (by omega) label hlabel

end
end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ParallelBlockCapacity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem designated_subset_choice_line (hvalid : C.Valid) (s : Slot F) :
    designated C.merged (C.choice s) ⊆ linePoints (C.choice s).line := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  rcases hvalid.2 s with ⟨_, _, _, _, _, hpoints, _, _, _⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpoints i⟩

theorem designated_card_four (hvalid : C.Valid) (s : Slot F) :
    (designated C.merged (C.choice s)).card = 4 := by
  rcases hvalid.2 s with ⟨_, _, _, _, hinj, _, _, _, _⟩
  simpa [designated] using Finset.card_image_of_injective
    (Finset.univ : Finset (Fin 4)) hinj

theorem designated_disjoint_of_slots_ne (hvalid : C.Valid) (hcompat : C.Compatible)
    (s t : Slot F) (hne : s ≠ t) :
    Disjoint (designated C.merged (C.choice s)) (designated C.merged (C.choice t)) := by
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  exact hcompat.1 s t hne x hxt
    (Finset.mem_filter.mp (C.designated_subset_choice_line hvalid s hxs)).2

theorem parallelDesignated_card (hvalid : C.Valid) (hcompat : C.Compatible)
    (g : Direction F) : (C.parallelDesignated g).card = 8 := by
  rw [parallelDesignated, Finset.card_union_of_disjoint
    (C.designated_disjoint_of_slots_ne hvalid hcompat (g, false) (g, true) (by simp))]
  rw [C.designated_card_four hvalid, C.designated_card_four hvalid]

theorem designated_inter_line_card_le_one (hvalid : C.Valid)
    (s : Slot F) (l : Line F) (hne : (C.choice s).line ≠ l) :
    (designated C.merged (C.choice s) ∩ linePoints l).card ≤ 1 := by
  apply (Finset.card_le_card ?_).trans (linePoints_inter_card_le_one (C.choice s).line l hne)
  intro x hx
  exact Finset.mem_inter.mpr
    ⟨C.designated_subset_choice_line hvalid s (Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp hx).2⟩

theorem designated_inter_merged_card_le_two (hvalid : C.Valid)
    (s : Slot F) (d : Direction F) :
    (designated C.merged (C.choice s) ∩ mergedPoints C.merged d).card ≤ 2 := by
  have hne (bit : Bool) : (C.choice s).line ≠ constituent C.merged d bit := by
    intro heq
    apply (hvalid.2 s).2.1
    rw [heq]
    exact Finset.mem_image.mpr ⟨(d, bit), Finset.mem_univ _, rfl⟩
  rw [mergedPoints, Finset.inter_union_distrib_left]
  exact (Finset.card_union_le _ _).trans (by
    have h0 := C.designated_inter_line_card_le_one hvalid s _ (hne false)
    have h1 := C.designated_inter_line_card_le_one hvalid s _ (hne true)
    omega)

theorem parallelDesignated_inter_merged_card_le_two
    (hvalid : C.Valid) (hcompat : C.Compatible) (g d : Direction F) :
    (C.parallelDesignated g ∩ mergedPoints C.merged d).card ≤ 2 := by
  have h0 := C.designated_inter_merged_card_le_two hvalid (g, false) d
  have h1 := C.designated_inter_merged_card_le_two hvalid (g, true) d
  have hc0 := hcompat.2.2 (g, false) (g, true) (by simp) rfl d
  have hc1 := hcompat.2.2 (g, true) (g, false) (by simp) rfl d
  rw [parallelDesignated, Finset.union_inter_distrib_right]
  exact (Finset.card_union_le _ _).trans (by omega)

theorem parallelDesignated_inter_regular_card_le_two
    (hvalid : C.Valid) (g : Direction F) (l : Line F)
    (hlabel : C.IsBlockLabel (Sum.inl l)) :
    (C.parallelDesignated g ∩ linePoints l).card ≤ 2 := by
  have hne (bit : Bool) : (C.choice (g, bit)).line ≠ l := by
    intro heq
    apply hlabel
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(g, bit), Finset.mem_univ _, heq⟩
  rw [parallelDesignated, Finset.union_inter_distrib_right]
  exact (Finset.card_union_le _ _).trans (by
    have h0 := C.designated_inter_line_card_le_one hvalid (g, false) l (hne false)
    have h1 := C.designated_inter_line_card_le_one hvalid (g, true) l (hne true)
    omega)

theorem parallelDesignated_block_capacity
    (hvalid : C.Valid) (hcompat : C.Compatible) (g : Direction F)
    (label : BlockLabel F) (hlabel : C.IsBlockLabel label) :
    (C.parallelDesignated g ∩ C.blockPoints label).card ≤ 2 := by
  classical
  rcases label with l | d | ⟨s, bit⟩
  · have hsub : C.parallelDesignated g ∩ C.blockPoints (Sum.inl l) ⊆
        C.parallelDesignated g ∩ linePoints l := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
    exact (Finset.card_le_card hsub).trans
      (C.parallelDesignated_inter_regular_card_le_two hvalid g l hlabel)
  · have hsub : C.parallelDesignated g ∩ C.blockPoints (Sum.inr (Sum.inl d)) ⊆
        C.parallelDesignated g ∩ mergedPoints C.merged d := by
      intro x hx
      exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
        (Finset.mem_inter.mp (Finset.mem_inter.mp hx).2).1⟩
    exact (Finset.card_le_card hsub).trans
      (C.parallelDesignated_inter_merged_card_le_two hvalid hcompat g d)
  · apply (Finset.card_le_card Finset.inter_subset_right).trans
    cases bit <;> exact Finset.card_le_two

theorem parallelDesignated_subset_points (g : Direction F) :
    C.parallelDesignated g ⊆ C.points := by
  intro x hx
  apply Finset.mem_union_right
  rcases Finset.mem_union.mp hx with h0 | h1
  · exact Finset.mem_biUnion.mpr ⟨(g, false), Finset.mem_univ _, h0⟩
  · exact Finset.mem_biUnion.mpr ⟨(g, true), Finset.mem_univ _, h1⟩

end
end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_ParallelCoverObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem parallelDesignated_disjoint_parallel_line
    (hvalid : C.Valid) (g : Direction F) (l : Line F)
    (hdir : l.1 = g) (hnot : l ∉ C.splitLines) :
    Disjoint (C.parallelDesignated g) (linePoints l) := by
  apply Finset.disjoint_left.mpr
  intro x hx hxl
  have hline : OnLine x l := (Finset.mem_filter.mp hxl).2
  have hmiss (bit : Bool) (hxd : x ∈ designated C.merged (C.choice (g, bit))) : False := by
    have hs : OnLine x (C.choice (g, bit)).line :=
      (Finset.mem_filter.mp (C.designated_subset_choice_line hvalid _ hxd)).2
    have heq : l = (C.choice (g, bit)).line :=
      eq_of_onLine_same_direction x l (C.choice (g, bit)).line
        (hdir.trans (hvalid.2 (g, bit)).1.symm) hline hs
    exact hnot (Finset.mem_image.mpr ⟨(g, bit), Finset.mem_univ _, heq.symm⟩)
  rcases Finset.mem_union.mp hx with h0 | h1
  · exact hmiss false h0
  · exact hmiss true h1

theorem represented_parallel_block_disjoint
    (hvalid : C.Valid) (g : Direction F) (label : BlockLabel F)
    (hlabel : C.IsBlockLabel label)
    (hrep : C.RepresentedThrough (Sum.inr g) label) :
    Disjoint (C.parallelDesignated g) (C.blockPoints label) := by
  classical
  rcases label with l | d | s
  · have hd : l.1 = g := by simpa [RepresentedThrough, coreRepresentative, ThroughProjective] using hrep
    have hnot : l ∉ C.splitLines := fun hl => hlabel (Finset.mem_union_left _ hl)
    exact (C.parallelDesignated_disjoint_parallel_line hvalid g l hd hnot).mono_right
      Finset.inter_subset_left
  · have hd : d = g := by
      simpa [RepresentedThrough, coreRepresentative, ThroughProjective, constituent] using hrep
    subst d
    have h0 := C.parallelDesignated_disjoint_parallel_line hvalid g
      (constituent C.merged g false) rfl (C.constituent_not_split hvalid g false)
    have h1 := C.parallelDesignated_disjoint_parallel_line hvalid g
      (constituent C.merged g true) rfl (C.constituent_not_split hvalid g true)
    have hm : Disjoint (C.parallelDesignated g) (mergedPoints C.merged g) :=
      Finset.disjoint_union_right.mpr ⟨h0, h1⟩
    exact hm.mono_right Finset.inter_subset_left
  · simp [RepresentedThrough, coreRepresentative] at hrep

theorem parallel_cover_impossible_of_forced_count
    (hvalid : C.Valid) (hcompat : C.Compatible)
    (hq : 3 ≤ Fintype.card F)
    (g : Direction F) (labels : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b)
    (hsize : labels.card ≤ Fintype.card F)
    (hforced : Fintype.card F - 3 ≤
      (labels.filter (C.RepresentedThrough (Sum.inr g))).card) :
    ¬ C.points ⊆ labels.biUnion C.blockPoints := by
  classical
  intro hcover
  let pencil := labels.filter (C.RepresentedThrough (Sum.inr g))
  have hpsub : pencil ⊆ labels := Finset.filter_subset _ _
  have hremaining : (labels \ pencil).card ≤ 3 := by
    have hsum := Finset.card_sdiff_add_card_eq_card hpsub
    change Fintype.card F - 3 ≤ pencil.card at hforced
    omega
  have hpencil : ∀ b ∈ pencil, Disjoint (C.parallelDesignated g) (C.blockPoints b) := by
    intro b hb
    exact C.represented_parallel_block_disjoint hvalid g b
      (hlabels b (Finset.mem_filter.mp hb).1) (Finset.mem_filter.mp hb).2
  have htarget : C.parallelDesignated g ⊆ labels.biUnion C.blockPoints :=
    (C.parallelDesignated_subset_points g).trans hcover
  have hres := CoverObstruction.cover_by_remaining_of_forced_disjoint
    (C.parallelDesignated g) labels pencil C.blockPoints htarget hpencil
  exact CoverObstruction.eight_points_not_covered_by_three_pairs
    (C.parallelDesignated g) (labels \ pencil) C.blockPoints
    (C.parallelDesignated_card hvalid hcompat g) hremaining
    (fun b hb => C.parallelDesignated_block_capacity hvalid hcompat g b
      (hlabels b (Finset.mem_sdiff.mp hb).1)) hres

end
end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_LocalCoverObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem blockPoints_subset_labelLocalPiece (b : BlockLabel F) :
    C.blockPoints b ⊆ C.localPiecePoints (C.labelLocalPiece b) := by
  rcases b with l | d | ⟨s, bit⟩
  · exact Finset.inter_subset_left
  · exact Finset.inter_subset_left
  · cases bit <;> exact Finset.Subset.refl _

theorem labelLocalPiece_allowed (p : Point F) (b : BlockLabel F)
    (h : C.IsBlockLabel b) : C.AllowedLocalPiece p (C.labelLocalPiece b) := by
  classical
  rcases b with l | d | ⟨s, bit⟩
  · change l ∉ C.splitLinesAt p ∪ constituentLines C.merged
    intro hl
    apply h
    rcases Finset.mem_union.mp hl with hs | hm
    · exact Finset.mem_union_left _ (Finset.mem_filter.mp hs).1
    · exact Finset.mem_union_right _ hm
  · trivial
  · cases bit <;> change (Finset.card {_, _} ≤ 2) <;> simpa using (Finset.card_insert_le _ {_})

theorem block_family_to_local_pieces
    (p : Point F) (labels : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b) :
    ∃ pieces : Finset (LocalPiece F), pieces.card ≤ labels.card ∧
      (∀ a ∈ pieces, C.AllowedLocalPiece p a) ∧
      labels.biUnion C.blockPoints ⊆ pieces.biUnion C.localPiecePoints := by
  classical
  refine ⟨labels.image C.labelLocalPiece, Finset.card_image_le, ?_, ?_⟩
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact C.labelLocalPiece_allowed p b (hlabels b hb)
  · intro x hx
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨C.labelLocalPiece b,
      Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      C.blockPoints_subset_labelLocalPiece b hxb⟩

theorem local_condition_excludes_block_cover
    (hlocal : C.LocalCondition) (p : Point F)
    (hb : 3 ≤ C.splitMultiplicity p)
    (labels : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b)
    (hcard : labels.card ≤ C.splitMultiplicity p - 1) :
    ¬ C.designatedAt p ⊆ C.partnerSet p ∪ labels.biUnion C.blockPoints := by
  intro hcover
  obtain ⟨pieces, hsize, hallowed, hpoints⟩ :=
    C.block_family_to_local_pieces p labels hlabels
  apply hlocal p hb
  refine ⟨pieces, hsize.trans hcard, hallowed, ?_⟩
  intro x hx
  rcases Finset.mem_union.mp (hcover hx) with hz | hr
  · exact Finset.mem_union_left _ hz
  · exact Finset.mem_union_right _ (hpoints hr)

theorem designatedAt_subset_points (p : Point F) : C.designatedAt p ⊆ C.points := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.mp hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨s, Finset.mem_univ s, hxs⟩)

theorem residual_cover_after_forcing
    (p : Point F) (labels forced : Finset (BlockLabel F))
    (hcover : C.points ⊆ labels.biUnion C.blockPoints)
    (hforced : C.designatedAt p ∩ forced.biUnion C.blockPoints ⊆ C.partnerSet p) :
    C.designatedAt p ⊆ C.partnerSet p ∪ (labels \ forced).biUnion C.blockPoints := by
  classical
  intro x hx
  obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp
    (hcover (C.designatedAt_subset_points p hx))
  by_cases hbf : b ∈ forced
  · exact Finset.mem_union_left _ (hforced (Finset.mem_inter.mpr
      ⟨hx, Finset.mem_biUnion.mpr ⟨b, hbf, hxb⟩⟩))
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨b, Finset.mem_sdiff.mpr ⟨hb, hbf⟩, hxb⟩)

theorem large_affine_pencil_cover_impossible
    (hlocal : C.LocalCondition) (p : Point F)
    (hb : 3 ≤ C.splitMultiplicity p)
    (hbupper : C.splitMultiplicity p ≤ Fintype.card F + 1)
    (labels forced : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b)
    (hsize : labels.card ≤ Fintype.card F)
    (hsubset : forced ⊆ labels)
    (hcount : forced.card = Fintype.card F + 1 - C.splitMultiplicity p)
    (hforced : C.designatedAt p ∩ forced.biUnion C.blockPoints ⊆ C.partnerSet p) :
    ¬ C.points ⊆ labels.biUnion C.blockPoints := by
  classical
  intro hcover
  have hremaining : (labels \ forced).card ≤ C.splitMultiplicity p - 1 := by
    have hsum := Finset.card_sdiff_add_card_eq_card hsubset
    omega
  exact C.local_condition_excludes_block_cover hlocal p hb (labels \ forced)
    (fun b hb => hlabels b (Finset.mem_sdiff.mp hb).1) hremaining
    (C.residual_cover_after_forcing p labels forced hcover hforced)

end
end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_TwoSplitCoverObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration

noncomputable section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem splitMultiplicity_le_order_add_one (p : Point F) :
    C.splitMultiplicity p ≤ Fintype.card F + 1 := by
  calc
    C.splitMultiplicity p ≤ (Finset.univ.filter (fun l : Line F => OnLine p l)).card := by
      apply Finset.card_le_card
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hl).2⟩
    _ = Fintype.card F + 1 := card_lines_through p

theorem two_split_cover_impossible_after_forcing
    (hvalid : C.Valid) (hcompat : C.Compatible)
    (p : Point F) (hb : C.splitMultiplicity p = 2)
    (labels forced : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ labels, C.IsBlockLabel b)
    (hsize : labels.card ≤ Fintype.card F)
    (hsubset : forced ⊆ labels)
    (hcount : Fintype.card F - 1 ≤ forced.card)
    (hforced : C.designatedAt p ∩ forced.biUnion C.blockPoints ⊆ C.partnerSet p) :
    ¬ C.points ⊆ labels.biUnion C.blockPoints := by
  classical
  intro hcover
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hremaining : (labels \ forced).card ≤ 1 := by
    have hsum := Finset.card_sdiff_add_card_eq_card hsubset
    omega
  have htarget : (C.designatedAt p).card = 8 := by
    simpa [hb] using ConfigurationStructure.designated_at_card C hvalid hcompat p
  have hpartner : (C.partnerSet p).card ≤ 2 := by
    simpa [hb] using ConstructionPartners.partner_card_le_splitMultiplicity
      C hvalid hcompat p (by omega)
  exact CoverObstruction.eight_points_not_covered_by_two_and_four
    (C.designatedAt p) (C.partnerSet p) (labels \ forced) C.blockPoints
    htarget hpartner hremaining
    (fun b hb' => C.two_split_block_capacity hvalid p hb b
      (hlabels b (Finset.mem_sdiff.mp hb').1))
    (C.residual_cover_after_forcing p labels forced hcover hforced)

end
end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_SinglePencilObstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] in
private theorem constituent_mem (C : Configuration F) (d : Direction F) (s : Bool) :
    constituent C.merged d s ∈ constituentLines C.merged :=
  Finset.mem_image.mpr ⟨(d, s), Finset.mem_univ _, rfl⟩

theorem split_ne_constituent (C : Configuration F) (hV : C.Valid)
    (s : Slot F) (d : Direction F) (e : Bool) :
    (C.choice s).line ≠ constituent C.merged d e := by
  intro he
  exact (hV.2 s).2.1 (he ▸ constituent_mem C d e)

theorem nonsplit_trace (C : Configuration F) (hV : C.Valid) (s : Slot F)
    (p : Point F) (hp : OnLine p (C.choice s).line)
    (b : BlockLabel F) (hb : b ∈ C.blockLabels) (hbp : C.NonsplitThrough p b)
    {x : Point F} (hx : x ∈ designated C.merged (C.choice s))
    (hxb : x ∈ C.blockPoints b) :
    x = p ∨ Adjacent C.merged (C.choice s).line p x := by
  classical
  have hxS : OnLine x (C.choice s).line := by
    simpa only [linePoints, Finset.mem_filter, Finset.mem_univ, true_and]
      using ConfigurationStructure.choice_designated_subset C hV s hx
  rcases b with l | d | t
  · left
    have hl : l ∉ C.splitLines ∪ constituentLines C.merged := (Finset.mem_filter.mp hb).2
    have hne : l ≠ (C.choice s).line := by
      intro he
      apply hl
      apply Finset.mem_union_left
      rw [he]
      exact ConfigurationStructure.choice_line_mem_split C s
    have hxl : OnLine x l := (Finset.mem_filter.mp (Finset.mem_inter.mp hxb).1).2
    exact common_point_eq_of_lines_ne l (C.choice s).line hne x p hxl hxS hbp hp
  · obtain ⟨e, hpe⟩ := hbp
    by_cases hxp : x = p
    · exact Or.inl hxp
    right
    have hd : d ≠ (C.choice s).line.1 := by
      intro he
      have hlines := eq_of_onLine_same_direction p (constituent C.merged d e)
        (C.choice s).line he hpe hp
      exact split_ne_constituent C hV s d e hlines.symm
    have hxM := (Finset.mem_inter.mp hxb).1
    simp only [mergedPoints, linePoints, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and] at hxM
    refine ⟨hp, hxS, Ne.symm hxp, d, hd, ?_⟩
    cases e
    · rcases hxM with hx0 | hx1
      · exact False.elim (hxp (common_point_eq_of_lines_ne
          (C.choice s).line (constituent C.merged d false)
          (split_ne_constituent C hV s d false) x p hxS hx0 hp hpe))
      · exact Or.inl ⟨hpe, hx1⟩
    · rcases hxM with hx0 | hx1
      · exact Or.inr ⟨hpe, hx0⟩
      · exact False.elim (hxp (common_point_eq_of_lines_ne
          (C.choice s).line (constituent C.merged d true)
          (split_ne_constituent C hV s d true) x p hxS hx1 hp hpe))
  · exact False.elim hbp

theorem nonsplit_pencil_not_cover (C : Configuration F) (hV : C.Valid)
    (s : Slot F) (p : Point F) (hp : OnLine p (C.choice s).line)
    (B : Finset (BlockLabel F)) (hB : B ⊆ C.blockLabels)
    (hthrough : ∀ b ∈ B, C.NonsplitThrough p b) :
    ¬ C.points ⊆ B.biUnion C.blockPoints := by
  classical
  intro hcover
  apply SplitGeometry.valid_not_covered (hV.2 s) p hp
    (fun x => x ∈ B.biUnion C.blockPoints)
  · intro x hx hc
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hc
    exact nonsplit_trace C hV s p hp b (hB hb) (hthrough b hb) hx hxb
  · intro x hx
    exact hcover (ConfigurationStructure.designated_subset_points C s hx)

theorem one_split_cover_impossible (C : Configuration F) (hV : C.Valid)
    (p : Point F) (hb : C.splitMultiplicity p = 1)
    (B A : Finset (BlockLabel F)) (hB : B ⊆ C.blockLabels)
    (hAsub : A ⊆ B) (hBcard : B.card ≤ Fintype.card F)
    (hAcard : Fintype.card F ≤ A.card)
    (hAthrough : ∀ b ∈ A, C.NonsplitThrough p b) :
    ¬ C.points ⊆ B.biUnion C.blockPoints := by
  classical
  have hAB : A = B := Finset.eq_of_subset_of_card_le hAsub (hBcard.trans hAcard)
  have hpos : 0 < (C.splitLinesAt p).card := by
    change 0 < C.splitMultiplicity p
    rw [hb]
    decide
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hpos
  obtain ⟨hl, hpl⟩ := Finset.mem_filter.mp hl
  obtain ⟨s, _, hsl⟩ := Finset.mem_image.mp hl
  have hps : OnLine p (C.choice s).line := by simpa only [hsl] using hpl
  apply nonsplit_pencil_not_cover C hV s p hps B hB
  intro b hbB
  exact hAthrough b (hAB.symm ▸ hbB)

end Configuration
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ForcedNonsplitLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

omit [Field F] in
lemma regular_not_deleted {l : Line F}
    (hsplit : l ∉ C.splitLines) (hconst : l ∉ constituentLines C.merged) :
    l ∉ C.deletedLines := by
  intro hl
  rcases Finset.mem_union.mp hl with hs | ht
  · exact hsplit hs
  · obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp ht
    exact hconst (C.mem_constituentLines d true)

omit [Field F] in
lemma regular_label_selected_of_represented (B : Finset (BlockLabel F))
    {l : Line F} (hconst : l ∉ constituentLines C.merged)
    (hrep : l ∈ B.biUnion C.coreRepresentative) : (Sum.inl l : BlockLabel F) ∈ B := by
  obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hrep
  rcases b with m | d | s
  · simp only [coreRepresentative, Finset.mem_singleton] at hbl
    simpa [hbl] using hb
  · simp only [coreRepresentative, Finset.mem_singleton] at hbl
    exact False.elim (hconst (hbl.symm ▸ C.mem_constituentLines d false))
  · simp [coreRepresentative] at hbl

omit [Field F] in
lemma merged_label_selected_of_false_represented (B : Finset (BlockLabel F))
    (hlabels : ∀ b ∈ B, C.IsBlockLabel b) (d : Direction F)
    (hrep : constituent C.merged d false ∈ B.biUnion C.coreRepresentative) :
    (Sum.inr (Sum.inl d) : BlockLabel F) ∈ B := by
  obtain ⟨b, hb, hbl⟩ := Finset.mem_biUnion.mp hrep
  rcases b with m | e | s
  · simp only [coreRepresentative, Finset.mem_singleton] at hbl
    have hbad := hlabels (Sum.inl m) hb
    exact False.elim (hbad (Finset.mem_union_right _ (hbl ▸ C.mem_constituentLines d false)))
  · simp only [coreRepresentative, Finset.mem_singleton] at hbl
    have hde : d = e := congrArg Prod.fst hbl
    simpa [hde] using hb
  · simp [coreRepresentative] at hbl

theorem forcedNonsplitLabel_injective (p : Point F) :
    Function.Injective (C.forcedNonsplitLabel p) := by
  intro d e h
  have he := congrArg blockDirection h
  simpa using he

theorem forcedNonsplitLabel_mem (hvalid : C.Valid)
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4)
    (d : Direction F) (hnotsplit : lineThrough d p ∉ C.splitLines) :
    C.forcedNonsplitLabel p d ∈ B := by
  classical
  unfold forcedNonsplitLabel
  split
  · rename_i hconst
    obtain ⟨⟨e, side⟩, _, he⟩ := Finset.mem_image.mp hconst
    have hed : e = d := congrArg Prod.fst he
    subst e
    cases side
    · have hnotdel := C.false_constituent_not_deleted hvalid d
      have hpd : OnLine p (constituent C.merged d false) := by rw [he]; rfl
      have hrep := C.ordinary_pencil_line_is_represented hvalid hocc hsize B hlabels hcover
        p hbudget (constituent C.merged d false) hpd hnotdel
      exact C.merged_label_selected_of_false_represented B hlabels d hrep
    · have hpd : OnLine p (constituent C.merged d true) := by rw [he]; rfl
      exact C.deleted_constituent_merged_label_selected hocc hsize B hlabels hcover p hbudget d hpd
  · rename_i hconst
    apply C.regular_label_selected_of_represented B hconst
    exact C.ordinary_pencil_line_is_represented hvalid hocc hsize B hlabels hcover p hbudget
      (lineThrough d p) (onLine_lineThrough d p) (C.regular_not_deleted hnotsplit hconst)

theorem split_directions_card (p : Point F) :
    ((Finset.univ : Finset (Direction F)).filter
      (fun d => lineThrough d p ∈ C.splitLines)).card = C.splitMultiplicity p := by
  classical
  let dirs := (Finset.univ : Finset (Direction F)).filter (fun d => lineThrough d p ∈ C.splitLines)
  have himage : dirs.image (fun d => lineThrough d p) = C.splitLinesAt p := by
    ext l
    constructor
    · intro hl
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hl
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).2, onLine_lineThrough d p⟩
    · intro hl
      obtain ⟨hsplit, hp⟩ := Finset.mem_filter.mp hl
      have he := line_eq_lineThrough p l hp
      refine Finset.mem_image.mpr ⟨l.1, ?_, he.symm⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he ▸ hsplit⟩
  have hinj : Function.Injective (fun d : Direction F => lineThrough d p) := by
    intro d e he
    exact congrArg Prod.fst he
  have hcard := Finset.card_image_of_injective dirs hinj
  rw [himage] at hcard
  exact hcard.symm

theorem forcedNonsplitLabels_card_add (p : Point F) :
    (C.forcedNonsplitLabels p).card + C.splitMultiplicity p = Fintype.card F + 1 := by
  classical
  have hforced : (C.forcedNonsplitLabels p).card = (C.nonsplitDirections p).card :=
    Finset.card_image_of_injective _ (C.forcedNonsplitLabel_injective p)
  rw [hforced, ← C.split_directions_card p]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Direction F))) (fun d => lineThrough d p ∈ C.splitLines)
  simpa [nonsplitDirections, Nat.add_comm, Fintype.card_option] using hpartition

theorem forcedNonsplitLabels_card (p : Point F) :
    (C.forcedNonsplitLabels p).card = Fintype.card F + 1 - C.splitMultiplicity p := by
  have := C.forcedNonsplitLabels_card_add p
  omega

theorem forcedNonsplitLabels_subset (hvalid : C.Valid)
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4) : C.forcedNonsplitLabels p ⊆ B := by
  intro b hb
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hb
  exact C.forcedNonsplitLabel_mem hvalid hocc hsize B hlabels hcover p hbudget d
    (Finset.mem_filter.mp hd).2

theorem remaining_labels_budget (B : Finset (BlockLabel F))
    (p : Point F) (hsubset : C.forcedNonsplitLabels p ⊆ B)
    (hcard : B.card ≤ Fintype.card F) :
    1 ≤ C.splitMultiplicity p ∧
      (B \ C.forcedNonsplitLabels p).card ≤ C.splitMultiplicity p - 1 := by
  have hforce := C.forcedNonsplitLabels_card_add p
  have hle := Finset.card_le_card hsubset
  rw [Finset.card_sdiff_of_subset hsubset]
  omega

end
end Configuration
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ForcedSinglePencil
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.Configuration
noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem forcedNonsplitLabel_through (C : Configuration F) (p : Point F)
    (d : Direction F) : C.NonsplitThrough p (C.forcedNonsplitLabel p d) := by
  classical
  unfold forcedNonsplitLabel
  split
  · rename_i hc
    obtain ⟨⟨e, side⟩, _, he⟩ := Finset.mem_image.mp hc
    have hed : e = d := congrArg Prod.fst he
    subst e
    refine ⟨side, ?_⟩
    rw [he]
    rfl
  · exact onLine_lineThrough d p

theorem forcedNonsplitLabels_through (C : Configuration F) (p : Point F)
    (b : BlockLabel F) (hb : b ∈ C.forcedNonsplitLabels p) : C.NonsplitThrough p b := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hb
  exact forcedNonsplitLabel_through C p d

theorem one_split_impossible_of_pencil_budget (C : Configuration F) (hV : C.Valid)
    {rho : ℝ} {cap : ℕ} (hO : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcard : B.card ≤ Fintype.card F)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4) : C.splitMultiplicity p ≠ 1 := by
  classical
  intro hb
  have hsub := C.forcedNonsplitLabels_subset hV hO hsize B hlabels hcover p hbudget
  have hAcard : Fintype.card F ≤ (C.forcedNonsplitLabels p).card := by
    have hsum := C.forcedNonsplitLabels_card_add p
    omega
  apply C.one_split_cover_impossible hV p hb B (C.forcedNonsplitLabels p)
    (fun b hbB => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlabels b hbB⟩)
    hsub hcard hAcard (C.forcedNonsplitLabels_through p)
  intro x hx
  obtain ⟨b, hbB, hxb⟩ := hcover x hx
  exact Finset.mem_biUnion.mpr ⟨b, hbB, hxb⟩

end
end Balanced.Configuration

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_ParallelPencilForcing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem parallel_mem_linePoints_iff (p : Point F) (l : Line F) :
    p ∈ linePoints l ↔ OnLine p l := by simp [linePoints]

private theorem missing_parallel_line_cover
    (L : Finset (Line F)) (U : Finset (Point F)) (hcover : CoversPoints L U)
    (l : Line F) (homit : l ∉ L) :
    linePoints l ∩ U ⊆
      (∅ : Finset (Point F)) ∪ (L.filter (fun m => m.1 ≠ l.1)).biUnion linePoints := by
  intro p hp
  obtain ⟨m, hm, hpm⟩ := hcover p (Finset.mem_inter.mp hp).2
  have hpl : OnLine p l := (parallel_mem_linePoints_iff p l).mp (Finset.mem_inter.mp hp).1
  have hdir : m.1 ≠ l.1 := by
    intro hsame
    have heq : m = l := eq_of_onLine_same_direction p m l hsame hpm hpl
    exact homit (heq ▸ hm)
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨m, Finset.mem_filter.mpr ⟨hm, hdir⟩, (parallel_mem_linePoints_iff p m).mpr hpm⟩)

private theorem parallel_trace_card_le_one (U : Finset (Point F))
    (l m : Line F) (hne : l ≠ m) :
    (linePoints m ∩ (linePoints l ∩ U)).card ≤ 1 := by
  calc
    (linePoints m ∩ (linePoints l ∩ U)).card ≤ (linePoints l ∩ linePoints m).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp (Finset.mem_inter.mp hp).2).1, (Finset.mem_inter.mp hp).1⟩
    _ ≤ 1 := distinct_line_intersection_card_le_one l m hne

private theorem missing_parallel_trace_bound
    (L : Finset (Line F)) (U : Finset (Point F)) (l : Line F) :
    ∀ m ∈ L.filter (fun m => m.1 ≠ l.1),
      (linePoints m ∩ (linePoints l ∩ U)).card ≤ 1 := by
  intro m hm
  apply parallel_trace_card_le_one U l m
  intro heq
  exact (Finset.mem_filter.mp hm).2 (congrArg Prod.fst heq.symm)

theorem missing_parallel_line_occupancy_bound
    (L : Finset (Line F)) (U : Finset (Point F)) (hcover : CoversPoints L U)
    (l : Line F) (homit : l ∉ L) :
    (linePoints l ∩ U).card ≤ (L.filter (fun m => m.1 ≠ l.1)).card := by
  have hbound : (linePoints l ∩ U).card ≤ (∅ : Finset (Point F)).card +
      1 * (L.filter (fun m => m.1 ≠ l.1)).card := by
    apply card_le_exceptional_add_cover_budget (linePoints l ∩ U)
      (∅ : Finset (Point F)) (L.filter (fun m => m.1 ≠ l.1))
      (fun m : Line F => linePoints m) 1
    · exact missing_parallel_line_cover L U hcover l homit
    · exact missing_parallel_trace_bound L U l
  rw [Finset.card_empty, Nat.one_mul, Nat.zero_add] at hbound
  exact hbound

namespace Configuration
variable (C : Configuration F)

theorem parallel_pencil_line_is_represented (hvalid : C.Valid)
    {rho : ℝ} {cap : ℕ} (hrho : 0 < rho) (hoccupancy : C.Occupancy rho cap)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (g : Direction F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card : ℝ) ≤
      rho * Fintype.card F / 4)
    (l : Line F) (hdir : l.1 = g) (hnotdel : l ∉ C.deletedLines) :
    l ∈ B.biUnion C.coreRepresentative := by
  by_contra homit
  have hcoreCover := (C.core_cover_reduction hvalid B hlabels hcover).2.2
  have hmissing := missing_parallel_line_occupancy_bound
    (B.biUnion C.coreRepresentative) C.core hcoreCover l homit
  have houtside := C.outside_pencil_representatives_card_le_labels B (Sum.inr g)
  have houtside' :
      ((B.biUnion C.coreRepresentative).filter (fun m => m.1 ≠ l.1)).card ≤
      (B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card := by
    apply le_trans (Finset.card_le_card ?_) houtside
    intro representative hrepresentative
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hrepresentative).1, ?_⟩
    simpa only [ThroughProjective, hdir] using (Finset.mem_filter.mp hrepresentative).2
  have hmissingReal : ((linePoints l ∩ C.core).card : ℝ) ≤
      ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card : ℝ) := by
    exact_mod_cast hmissing.trans houtside'
  have hocc := hoccupancy.2.1 l hnotdel
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hpos : 0 < rho * Fintype.card F := mul_pos hrho hq
  linarith

omit [Field F] in
private theorem parallel_direction_card (g : Direction F) :
    (linesInDirection g).card = Fintype.card F := by
  unfold linesInDirection
  rw [← Finset.univ_product_univ,
    Finset.filter_product_left (fun d : Direction F => d = g)]
  simp [Finset.filter_eq']

theorem parallel_nondeleted_card (hvalid : C.Valid) (hcompatible : C.Compatible)
    (g : Direction F) :
    ((linesInDirection g) \ C.deletedLines).card = Fintype.card F - 3 := by
  rw [Finset.card_sdiff, parallel_direction_card]
  have hinter : C.deletedLines ∩ linesInDirection g =
      C.deletedLines.filter (fun l => l.1 = g) := by
    ext l
    simp only [Finset.mem_inter, linesInDirection, Finset.mem_filter,
      Finset.mem_univ, true_and]
  rw [hinter, ConfigurationStructure.deleted_lines_in_direction_card C hvalid hcompatible g]

theorem parallel_pencil_forced_label_count (hvalid : C.Valid)
    (hcompatible : C.Compatible) {rho : ℝ} {cap : ℕ}
    (hrho : 0 < rho) (hoccupancy : C.Occupancy rho cap)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b)
    (g : Direction F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inr g) b)).card : ℝ) ≤
      rho * Fintype.card F / 4) :
    Fintype.card F - 3 ≤ (B.filter (C.RepresentedThrough (Sum.inr g))).card := by
  have hsubset : (linesInDirection g) \ C.deletedLines ⊆
      (B.biUnion C.coreRepresentative).filter (fun l => ThroughProjective l (Sum.inr g)) := by
    intro l hl
    obtain ⟨hlg, hnotdel⟩ := Finset.mem_sdiff.mp hl
    have hdir : l.1 = g := (Finset.mem_filter.mp hlg).2
    exact Finset.mem_filter.mpr
      ⟨C.parallel_pencil_line_is_represented hvalid hrho hoccupancy
        B hlabels hcover g hbudget l hdir hnotdel, hdir⟩
  calc
    Fintype.card F - 3 = ((linesInDirection g) \ C.deletedLines).card :=
      (C.parallel_nondeleted_card hvalid hcompatible g).symm
    _ ≤ ((B.biUnion C.coreRepresentative).filter
        (fun l => ThroughProjective l (Sum.inr g))).card := Finset.card_le_card hsubset
    _ ≤ (B.filter (C.RepresentedThrough (Sum.inr g))).card :=
      C.pencil_representatives_card_le_labels B (Sum.inr g)

end Configuration
end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_NoSmallBlockCover
attribute [-instance] _root_.OAI.Balanced.instDecidableProjectiveIncident
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced
namespace Configuration

noncomputable section
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable (C : Configuration F)

theorem nonsplit_pencil_trace_subset_partner
    (hvalid : C.Valid) (hcompat : C.Compatible)
    (p : Point F) (hb : 2 ≤ C.splitMultiplicity p)
    (A : Finset (BlockLabel F)) (hlabels : ∀ b ∈ A, C.IsBlockLabel b)
    (hthrough : ∀ b ∈ A, C.NonsplitThrough p b) :
    C.designatedAt p ∩ A.biUnion C.blockPoints ⊆ C.partnerSet p := by
  intro x hx
  obtain ⟨hxd, hxb⟩ := Finset.mem_inter.mp hx
  obtain ⟨b, hbA, hxb⟩ := Finset.mem_biUnion.mp hxb
  have hbt := hthrough b hbA
  rcases b with l | d | s
  · exact False.elim (Finset.disjoint_left.mp
      (ConstructionPartners.regular_block_disjoint_designatedAt C hvalid hcompat p hb l
        (hlabels (Sum.inl l) hbA) hbt) hxb hxd)
  · obtain ⟨side, hp⟩ := hbt
    exact ConstructionPartners.merged_block_inter_designatedAt_subset_partnerSet
      C hvalid hcompat p hb d side hp (Finset.mem_inter.mpr ⟨hxb, hxd⟩)
  · exact False.elim hbt

theorem affine_pencil_cover_impossible_of_budget
    (hvalid : C.Valid) (hcompat : C.Compatible)
    {rho : ℝ} {cap : ℕ} (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (hlocal : C.LocalCondition)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcard : B.card ≤ Fintype.card F) (p : Point F)
    (hbudget : ((B.filter (fun b => ¬ C.RepresentedThrough (Sum.inl p) b)).card : ℝ) ≤
      rho * Fintype.card F / 4) :
    ¬ ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b := by
  intro hcover
  have hsubset := C.forcedNonsplitLabels_subset hvalid hocc hsize B hlabels hcover p hbudget
  have hbpos := (C.remaining_labels_budget B p hsubset hcard).1
  by_cases hb1 : C.splitMultiplicity p = 1
  · exact C.one_split_impossible_of_pencil_budget hvalid hocc hsize B hlabels hcard hcover p hbudget hb1
  have hbge : 2 ≤ C.splitMultiplicity p := by omega
  have hforced := C.nonsplit_pencil_trace_subset_partner hvalid hcompat p hbge
    (C.forcedNonsplitLabels p) (fun b hb => hlabels b (hsubset hb))
    (C.forcedNonsplitLabels_through p)
  have hcoverSet : C.points ⊆ B.biUnion C.blockPoints := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨b, hb, hxb⟩
  by_cases hb2 : C.splitMultiplicity p = 2
  · have hcount : Fintype.card F - 1 ≤ (C.forcedNonsplitLabels p).card := by
      have := C.forcedNonsplitLabels_card_add p
      omega
    exact C.two_split_cover_impossible_after_forcing hvalid hcompat p hb2 B
      (C.forcedNonsplitLabels p) hlabels hcard hsubset hcount hforced hcoverSet
  · have hb3 : 3 ≤ C.splitMultiplicity p := by omega
    exact C.large_affine_pencil_cover_impossible hlocal p hb3
      (C.splitMultiplicity_le_order_add_one p) B (C.forcedNonsplitLabels p)
      hlabels hcard hsubset (C.forcedNonsplitLabels_card p) hforced hcoverSet

theorem no_small_block_cover
    (hvalid : C.Valid) (hcompat : C.Compatible)
    {rho : ℝ} {cap : ℕ} (hrho : 0 < rho)
    (hq : 4 ≤ Fintype.card F) (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (hconcentration : C.CoreConcentration rho) (hlocal : C.LocalCondition)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcard : B.card ≤ Fintype.card F) :
    ¬ ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b := by
  intro hcover
  obtain ⟨P, hbudget⟩ := C.core_cover_outside_pencil_budget
    hvalid hconcentration B hlabels hcard hcover
  rcases P with p | g
  · exact C.affine_pencil_cover_impossible_of_budget
      hvalid hcompat hocc hsize hlocal B hlabels hcard p hbudget hcover
  · have hforced := C.parallel_pencil_forced_label_count
      hvalid hcompat hrho hocc B hlabels hcover g hbudget
    apply C.parallel_cover_impossible_of_forced_count
      hvalid hcompat (by omega) g B hlabels hcard hforced
    intro x hx
    obtain ⟨b, hb, hxb⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨b, hb, hxb⟩

theorem block_cover_card_lower_bound
    (hvalid : C.Valid) (hcompat : C.Compatible)
    {rho : ℝ} {cap : ℕ} (hrho : 0 < rho)
    (hq : 4 ≤ Fintype.card F) (hocc : C.Occupancy rho cap)
    (hsize : 2 * (1 + (cap : ℝ)) < rho * Fintype.card F)
    (hconcentration : C.CoreConcentration rho) (hlocal : C.LocalCondition)
    (B : Finset (BlockLabel F)) (hlabels : ∀ b ∈ B, C.IsBlockLabel b)
    (hcover : ∀ x ∈ C.points, ∃ b ∈ B, x ∈ C.blockPoints b) :
    Fintype.card F + 1 ≤ B.card := by
  by_contra hnot
  exact C.no_small_block_cover hvalid hcompat hrho hq hocc hsize
    hconcentration hlocal B hlabels (by omega) hcover

end
end Configuration
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_DeterministicReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

universe u

theorem deterministicReduction_proof : DeterministicReduction.{u} := by
  classical
  intro F _ _ _ C ρ B hq hρ0 hρ1 hV hC hO hCore hLocal hsize
  refine ⟨C.constructedHypergraph hV hC hq,
    C.constructedHypergraph_intersecting hV hC hq,
    C.constructedHypergraph_nonisolated hV hC hq hρ0 hO,
    ?_, C.constructedHypergraph_realization hV hC hq hρ1 hO hsize⟩
  apply C.constructedHypergraph_hasCoverNumber hV hC hq
  intro A hA hCover
  apply C.block_cover_card_lower_bound hV hC hρ0 hq hO hsize hCore hLocal A
  · intro b hb
    exact (Finset.mem_filter.mp (hA hb)).2
  · intro x hx
    exact Finset.mem_biUnion.mp (hCover hx)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Construction_Hypergraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.PartiteHypergraph

variable {r n : ℕ}

@[simp] theorem covers_empty_iff (H : PartiteHypergraph r n) :
    H.Covers ∅ ↔ H.edges = ∅ := by
  constructor
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    rcases h e he with ⟨i, hi⟩
    exact Finset.notMem_empty _ hi
  · intro h e he
    simp [h] at he

end Balanced.PartiteHypergraph

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Deletion_DeletionFieldTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Balanced.FieldTransport

variable {F G : Type*} [Field F] [Field G]

variable [Fintype F] [DecidableEq F] [Fintype G] [DecidableEq G]

omit [DecidableEq F] [DecidableEq G] in
@[simp] theorem cardinal_field (e : F ≃+* G) : Fintype.card G = Fintype.card F :=
  (Fintype.card_congr e.toEquiv).symm

end Balanced.FieldTransport

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_DistinctRoleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal Classical

namespace Balanced.DistinctRole

variable {D F : Type*} [Field F]

variable [Fintype D] [Fintype F]

instance distinctNonempty :
    Nonempty {M : D → Bool → F // ∀ d, M d false ≠ M d true} :=
  ⟨⟨fun _ b => if b then 0 else 1, by simp⟩⟩

end Balanced.DistinctRole

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_PatternExposureBoundary
attribute [-instance] _root_.OAI.Balanced.DistinctRole.distinctNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped BigOperators

namespace Balanced.PatternModel

variable (P : PatternModel)

@[simp] theorem count_eq_zero_of_isEmpty [IsEmpty P.Label] (ω : P.Sample) :
    P.count ω = 0 := by
  simp [count]

end Balanced.PatternModel

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Results
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u v w

open scoped BigOperators

namespace Balanced
open scoped _root_.Balanced

theorem deterministic_reduction_oai : DeterministicReduction.{u} :=
  deterministicReduction_proof

end Balanced

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.deterministic_reduction_oai.{u} := @OAI.Balanced.deterministic_reduction_oai.{u}
