-- Prove2me | solution 1 for OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_incidence_estimates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:13:58.148421+00:00
-- url     : https://prove2.me/submissions/3d3d1b63-9ea9-474a-87dc-64ad7492dafe

import Mathlib
import Definitions.Def_OAIQ63Br002
import Definitions.Def_OAIQ63Br003

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced.CandidateAsymptotics

theorem tendsto_ceil_log_mul_ceil_rpow_div {theta beta : ℝ}
    (htheta : 0 ≤ theta) (hgap : theta < beta) :
    Tendsto (fun x : ℝ => (⌈Real.log x⌉₊ : ℝ) * (⌈x ^ theta⌉₊ : ℝ) / x ^ beta)
      atTop (𝓝 0) := by
  have hlog := (isLittleO_log_rpow_atTop (sub_pos.mpr hgap)).tendsto_div_nhds_zero
  have hx : ∀ᶠ x : ℝ in atTop, 1 ≤ x := eventually_ge_atTop 1
  have hlogone : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  apply squeeze_zero' (hx.mono fun x hx => by positivity)
    (g := fun x : ℝ => 4 * (Real.log x / x ^ (beta - theta)))
  · filter_upwards [hx, hlogone] with x hx hl
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    have hp : 1 ≤ x ^ theta := Real.one_le_rpow hx htheta
    have hceilLog : (⌈Real.log x⌉₊ : ℝ) ≤ 2 * Real.log x := by
      have h := Nat.ceil_lt_add_one (show 0 ≤ Real.log x by linarith)
      linarith
    have hceilPow : (⌈x ^ theta⌉₊ : ℝ) ≤ 2 * x ^ theta := by
      have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hxpos.le theta)
      linarith
    calc
      (⌈Real.log x⌉₊ : ℝ) * (⌈x ^ theta⌉₊ : ℝ) / x ^ beta ≤
          (2 * Real.log x) * (2 * x ^ theta) / x ^ beta := by gcongr
      _ = 4 * (Real.log x / x ^ (beta - theta)) := by
        rw [Real.rpow_sub hxpos]
        field_simp
        ring
  · simpa using hlog.const_mul (4 : ℝ)

theorem eventually_scaled_product_le (C : ℝ) : ∀ᶠ q : ℕ in atTop,
    C * (⌈Real.log (q : ℝ)⌉₊ : ℝ) * (⌈(q : ℝ) ^ (1 / 100 : ℝ)⌉₊ : ℝ) ≤
      (q : ℝ) ^ (1 / 8 : ℝ) := by
  have hlim := ((tendsto_ceil_log_mul_ceil_rpow_div
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1 / 8)).comp
      tendsto_natCast_atTop_atTop).const_mul C
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : C * (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_ge_atTop 1] with q hsmall hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hpos : 0 < (q : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos hqpos _
  have hdiv : (C * (⌈Real.log (q : ℝ)⌉₊ : ℝ) *
      (⌈(q : ℝ) ^ (1 / 100 : ℝ)⌉₊ : ℝ)) / (q : ℝ) ^ (1 / 8 : ℝ) < 1 := by
    simpa only [Function.comp_apply, mul_div_assoc, mul_assoc] using hsmall
  exact ((div_lt_iff₀ hpos).mp hdiv).le.trans_eq (one_mul _)

end Balanced.CandidateAsymptotics

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateBasics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem candidateSlot_offset_injective (M : MergedPairs F) (s : Slot F) :
    Set.InjOn (fun v : CandidateVertex F => v.2) (candidateSlot M s) := by
  intro v hv w hw hoff
  apply Prod.ext
  · exact (mem_candidateSlot.mp hv).2.trans (mem_candidateSlot.mp hw).2.symm
  · exact hoff

theorem candidateSlot_card_le (M : MergedPairs F) (s : Slot F) :
    (candidateSlot M s).card ≤ Fintype.card F := by
  calc
    (candidateSlot M s).card ≤ (Finset.univ : Finset F).card :=
      Finset.card_le_card_of_injOn (fun v : CandidateVertex F => v.2)
        (fun _ _ => Finset.mem_univ _) (candidateSlot_offset_injective M s)
    _ = Fintype.card F := Finset.card_univ

theorem candidateSlot_line_injective (M : MergedPairs F) (s : Slot F) :
    Set.InjOn (candidateLine (F := F)) (candidateSlot M s : Set (CandidateVertex F)) := by
  intro v hv w hw heq
  have hoff : v.2 = w.2 := congrArg (fun l : Line F => l.2) heq
  exact candidateSlot_offset_injective M s hv hw hoff

end
end Balanced

end OAI
end

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

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {M : MergedPairs F}

theorem valid {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    ValidChoice M v.1.1 (candidateChoice M v) :=
  retainedChoice_valid (mem_candidateVertices.mp hv)

theorem points_card {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    (points M v).card = 4 := by
  have hinj := (valid hv).2.2.2.2.1
  simpa [points, designated] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin 4)) hinj

theorem points_nonempty {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    (points M v).Nonempty := by
  apply Finset.card_pos.mp
  rw [points_card hv]
  decide

theorem points_on_line {v : CandidateVertex F} (hv : v ∈ candidateVertices M)
    {p : Point F} (hp : p ∈ points M v) : OnLine p (candidateLine v) := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact (valid hv).2.2.2.2.2.1 i

omit [Field F] [Fintype F] [DecidableEq F] in

theorem eq_of_same_line_same_bit {v w : CandidateVertex F}
    (hl : candidateLine v = candidateLine w) (hb : v.1.2 = w.1.2) : v = w := by
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun l : Line F => l.1) hl
    · exact hb
  · exact congrArg (fun l : Line F => l.2) hl

theorem card_same_line_le_two (M : MergedPairs F) (l : Line F) :
    ((candidateVertices M).filter (fun v => candidateLine v = l)).card ≤ 2 := by
  let A := (candidateVertices M).filter (fun v => candidateLine v = l)
  have hinj : Set.InjOn (fun v : CandidateVertex F => v.1.2) (A : Set _) := by
    intro v hv w hw hb
    exact eq_of_same_line_same_bit
      ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hw).2.symm) hb
  calc
    A.card = (A.image (fun v => v.1.2)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card Bool := Finset.card_le_univ _
    _ = 2 := by decide

theorem exceptional_subset (M : MergedPairs F) (v : CandidateVertex F) :
    exceptionalSet M v ⊆ candidateVertices M := Finset.filter_subset _ _

theorem exceptional_adjacent_or_same_slot {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (hw : w ∈ exceptionalSet M v) :
    CandidateAdjacent M v w ∨ w.1 = v.1 := by
  have hwv := exceptional_subset M v hw
  by_cases hs : v.1 = w.1
  · exact Or.inr hs.symm
  apply Or.inl
  refine ⟨hv, hwv, hs, ?_⟩
  intro hc
  rcases (Finset.mem_filter.mp hw).2 with hl | hpoints
  · obtain ⟨p, hp⟩ := points_nonempty hv
    apply hc.1 p hp
    change OnLine p (candidateLine w)
    rw [hl]
    exact points_on_line hv hp
  · obtain ⟨p, hp⟩ := hpoints
    exact hc.1 p (Finset.mem_inter.mp hp).2
      (points_on_line hwv (Finset.mem_inter.mp hp).1)

theorem not_exceptional_distinct_disjoint {v w : CandidateVertex F}
    (hwv : w ∈ candidateVertices M) (hw : w ∉ exceptionalSet M v) :
    candidateLine w ≠ candidateLine v ∧ Disjoint (points M w) (points M v) := by
  have hn : ¬ (candidateLine w = candidateLine v ∨
      (points M w ∩ points M v).Nonempty) := by
    intro h
    exact hw (Finset.mem_filter.mpr ⟨hwv, h⟩)
  refine ⟨fun h => hn (Or.inl h), ?_⟩
  apply Finset.disjoint_left.mpr
  intro p hpw hpv
  exact hn (Or.inr ⟨p, Finset.mem_inter.mpr ⟨hpw, hpv⟩⟩)

theorem exceptional_card_le {v : CandidateVertex F} (hv : v ∈ candidateVertices M)
    {P : ℕ} (hP : ∀ p : Point F,
      ((candidateVertices M).filter (fun w => p ∈ points M w)).card ≤ P) :
    (exceptionalSet M v).card ≤ 2 + 4 * P := by
  let A := (candidateVertices M).filter (fun w => candidateLine w = candidateLine v)
  let B := (points M v).biUnion (fun p =>
    (candidateVertices M).filter (fun w => p ∈ points M w))
  have hsub : exceptionalSet M v ⊆ A ∪ B := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, hl | hpoints⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwv, hl⟩)
    · obtain ⟨p, hp⟩ := hpoints
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨p, (Finset.mem_inter.mp hp).2,
          Finset.mem_filter.mpr ⟨hwv, (Finset.mem_inter.mp hp).1⟩⟩)
  have hB : B.card ≤ 4 * P := by
    calc
      B.card ≤ ∑ p ∈ points M v,
          ((candidateVertices M).filter (fun w => p ∈ points M w)).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ points M v, P := Finset.sum_le_sum (fun p _ => hP p)
      _ = 4 * P := by simp [points_card hv]
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_union_le A B).trans (Nat.add_le_add (card_same_line_le_two M _) hB))

theorem card_through_point_in_slot_le_one (M : MergedPairs F) (s : Slot F) (p : Point F) :
    ((candidateSlot M s).filter (fun w => OnLine p (candidateLine w))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  rcases Finset.mem_filter.mp hv with ⟨hv, hpv⟩
  rcases Finset.mem_filter.mp hw with ⟨hw, hpw⟩
  apply candidateSlot_line_injective M s hv hw
  apply eq_of_onLine_same_direction p _ _ _ hpv hpw
  change v.1.1 = w.1.1
  rw [(mem_candidateSlot.mp hv).2, (mem_candidateSlot.mp hw).2]

theorem card_through_point_le (M : MergedPairs F) (p : Point F) :
    ((candidateVertices M).filter (fun w => OnLine p (candidateLine w))).card ≤
      2 * (Fintype.card F + 1) := by
  let A := (candidateVertices M).filter (fun w => OnLine p (candidateLine w))
  have hinj : Set.InjOn (fun v : CandidateVertex F => v.1) (A : Set _) := by
    intro v hv w hw hs
    rcases Finset.mem_filter.mp hv with ⟨hv, hpv⟩
    rcases Finset.mem_filter.mp hw with ⟨hw, hpw⟩
    apply Prod.ext hs
    have hl := eq_of_onLine_same_direction p (candidateLine v) (candidateLine w)
      (congrArg (fun s : Slot F => s.1) hs) hpv hpw
    exact congrArg (fun l : Line F => l.2) hl
  calc
    A.card = (A.image (fun v => v.1)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (Slot F) := Finset.card_le_univ _
    _ = 2 * (Fintype.card F + 1) := by simp [Slot, Direction, mul_comm]

theorem B_slot_card_le_four {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (s : Slot F) :
    ((B M v) ∩ candidateSlot M s).card ≤ 4 := by
  have hsub : B M v ∩ candidateSlot M s ⊆
      (points M v).biUnion (fun p =>
        (candidateSlot M s).filter (fun w => OnLine p (candidateLine w))) := by
    intro w hw
    rcases Finset.mem_inter.mp hw with ⟨hwB, hws⟩
    obtain ⟨p, hp, hline⟩ := (Finset.mem_filter.mp hwB).2
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hws, hline⟩⟩
  calc
    ((B M v) ∩ candidateSlot M s).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ points M v,
        ((candidateSlot M s).filter (fun w => OnLine p (candidateLine w))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, 1 :=
      Finset.sum_le_sum (fun p _ => card_through_point_in_slot_le_one M s p)
    _ = 4 := by simp [points_card hv]

theorem B_card_le {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    (B M v).card ≤ 8 * (Fintype.card F + 1) := by
  have hsub : B M v ⊆ (points M v).biUnion (fun p =>
      (candidateVertices M).filter (fun w => OnLine p (candidateLine w))) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, p, hp, hline⟩
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨hwv, hline⟩⟩
  calc
    (B M v).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ points M v,
        ((candidateVertices M).filter (fun w => OnLine p (candidateLine w))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, 2 * (Fintype.card F + 1) :=
      Finset.sum_le_sum (fun p _ => card_through_point_le M p)
    _ = 8 * (Fintype.card F + 1) := by simp [points_card hv]; omega

theorem B_inter_B_card_le {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (hw : w ∈ candidateVertices M)
    (hd : Disjoint (points M v) (points M w)) :
    ((B M v) ∩ (B M w)).card ≤ 32 := by
  let T := (points M v).biUnion (fun p => (points M w).biUnion (fun r =>
    (candidateVertices M).filter (fun z => candidateLine z = joiningLine p r)))
  have hsub : B M v ∩ B M w ⊆ T := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzv, hzw⟩
    rcases Finset.mem_filter.mp hzv with ⟨hz, p, hp, hpz⟩
    obtain ⟨r, hr, hrz⟩ := (Finset.mem_filter.mp hzw).2
    have hpr : p ≠ r := by
      intro heq
      exact Finset.disjoint_left.mp hd hp (heq.symm ▸ hr)
    have hl := eq_of_two_common_points p r hpr (candidateLine z) (joiningLine p r)
      hpz hrz (onLine_joiningLine_left p r) (onLine_joiningLine_right p r)
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_biUnion.mpr
      ⟨r, hr, Finset.mem_filter.mpr ⟨hz, hl⟩⟩⟩
  have hinner : ∀ p : Point F,
      ((points M w).biUnion (fun r =>
        (candidateVertices M).filter (fun z => candidateLine z = joiningLine p r))).card ≤ 8 := by
    intro p
    calc
      _ ≤ ∑ r ∈ points M w,
          ((candidateVertices M).filter (fun z => candidateLine z = joiningLine p r)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _r ∈ points M w, 2 :=
        Finset.sum_le_sum (fun r _ => card_same_line_le_two M _)
      _ = 8 := by simp [points_card hw]
  calc
    (B M v ∩ B M w).card ≤ T.card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ points M v, ((points M w).biUnion (fun r =>
        (candidateVertices M).filter (fun z => candidateLine z = joiningLine p r))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, 8 := Finset.sum_le_sum (fun p _ => hinner p)
    _ = 32 := by simp [points_card hv]

theorem common_line_points_card_le_one (l k : Line F) (hne : l ≠ k) :
    (linePoints l ∩ linePoints k).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp r hr
  rcases Finset.mem_inter.mp hp with ⟨hpl, hpk⟩
  rcases Finset.mem_inter.mp hr with ⟨hrl, hrk⟩
  exact common_point_eq_of_lines_ne l k hne p r
    (Finset.mem_filter.mp hpl).2 (Finset.mem_filter.mp hpk).2
    (Finset.mem_filter.mp hrl).2 (Finset.mem_filter.mp hrk).2

theorem pointLine_subset_of_onLine (M : MergedPairs F) (p : Point F) (l : Line F)
    (hp : OnLine p l) :
    pointLineCandidates M p l ⊆
      ((candidateVertices M).filter (fun z => candidateLine z = l)) ∪ pointCandidates M p := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hzv, hpz, r, hr, hrl⟩
  by_cases hl : candidateLine z = l
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hzv, hl⟩)
  · have hpr := common_point_eq_of_lines_ne (candidateLine z) l hl p r hpz hp
      (points_on_line hzv hr) hrl
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzv, hpr.symm ▸ hr⟩)

theorem pointLine_card_le_of_onLine (M : MergedPairs F) (p : Point F) (l : Line F)
    (hp : OnLine p l) {P : ℕ} (hP : (pointCandidates M p).card ≤ P) :
    (pointLineCandidates M p l).card ≤ 2 + P := by
  apply (Finset.card_le_card (pointLine_subset_of_onLine M p l hp)).trans
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (card_same_line_le_two M l) hP)

theorem B_inter_E_card_le {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {P : ℕ}
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (hmixed : ∀ p, ¬ OnLine p (candidateLine w) →
      (pointLineCandidates M p (candidateLine w)).card ≤ P) :
    (B M v ∩ E M w).card ≤ 4 * (2 + P) := by
  have hsub : B M v ∩ E M w ⊆
      (points M v).biUnion (fun p => pointLineCandidates M p (candidateLine w)) := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzB, hzE⟩
    rcases Finset.mem_filter.mp hzB with ⟨hzv, p, hp, hpz⟩
    exact Finset.mem_biUnion.mpr ⟨p, hp,
      Finset.mem_filter.mpr ⟨hzv, hpz, (Finset.mem_filter.mp hzE).2⟩⟩
  have hsingle : ∀ p, (pointLineCandidates M p (candidateLine w)).card ≤ 2 + P := by
    intro p
    by_cases hp : OnLine p (candidateLine w)
    · exact pointLine_card_le_of_onLine M p (candidateLine w) hp (hpoint p)
    · exact (hmixed p hp).trans (Nat.le_add_left _ _)
  calc
    (B M v ∩ E M w).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ points M v, (pointLineCandidates M p (candidateLine w)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, (2 + P) := Finset.sum_le_sum (fun p _ => hsingle p)
    _ = 4 * (2 + P) := by simp [points_card hv]

theorem E_inter_E_card_le {v w : CandidateVertex F}
    (hne : candidateLine v ≠ candidateLine w) {P : ℕ}
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (htwo : (twoLineCandidates M (candidateLine v) (candidateLine w)).card ≤ P) :
    (E M v ∩ E M w).card ≤ 2 * P := by
  let I := linePoints (candidateLine v) ∩ linePoints (candidateLine w)
  let A := I.biUnion (fun p => pointCandidates M p)
  have hsub : E M v ∩ E M w ⊆
      twoLineCandidates M (candidateLine v) (candidateLine w) ∪ A := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzv, hzw⟩
    rcases Finset.mem_filter.mp hzv with ⟨hz, p, hp, hpl⟩
    obtain ⟨r, hr, hrk⟩ := (Finset.mem_filter.mp hzw).2
    by_cases hpr : p = r
    · subst r
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨p, ?_, Finset.mem_filter.mpr ⟨hz, hp⟩⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrk⟩⟩
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hz, p, hp, r, hr, hpr, hpl, hrk⟩)
  have hA : A.card ≤ P := by
    calc
      A.card ≤ ∑ p ∈ I, (pointCandidates M p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ I, P := Finset.sum_le_sum (fun p _ => hpoint p)
      _ = I.card * P := by simp
      _ ≤ 1 * P := Nat.mul_le_mul_right P (common_line_points_card_le_one _ _ hne)
      _ = P := one_mul P
  calc
    (E M v ∩ E M w).card ≤ _ := Finset.card_le_card hsub
    _ ≤ (twoLineCandidates M (candidateLine v) (candidateLine w)).card + A.card :=
      Finset.card_union_le _ _
    _ ≤ P + P := Nat.add_le_add htwo hA
    _ = 2 * P := by omega

theorem primary_common_card_le {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (hw : w ∈ candidateVertices M)
    (hne : candidateLine v ≠ candidateLine w)
    (hd : Disjoint (points M v) (points M w)) {P : ℕ}
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (hmixedv : ∀ p, ¬ OnLine p (candidateLine v) →
      (pointLineCandidates M p (candidateLine v)).card ≤ P)
    (hmixedw : ∀ p, ¬ OnLine p (candidateLine w) →
      (pointLineCandidates M p (candidateLine w)).card ≤ P)
    (htwo : (twoLineCandidates M (candidateLine v) (candidateLine w)).card ≤ P) :
    ((B M v ∪ E M v) ∩ (B M w ∪ E M w)).card ≤ 48 + 10 * P := by
  have hBB := B_inter_B_card_le hv hw hd
  have hBE := B_inter_E_card_le hv hpoint hmixedw
  have hEB : (E M v ∩ B M w).card ≤ 4 * (2 + P) := by
    simpa only [Finset.inter_comm] using B_inter_E_card_le hw hpoint hmixedv
  have hEE := E_inter_E_card_le hne hpoint htwo
  rw [Finset.union_inter_distrib_right, Finset.inter_union_distrib_left,
    Finset.inter_union_distrib_left]
  have houter := Finset.card_union_le
    ((B M v ∩ B M w) ∪ (B M v ∩ E M w))
    ((E M v ∩ B M w) ∪ (E M v ∩ E M w))
  have hleft := Finset.card_union_le (B M v ∩ B M w) (B M v ∩ E M w)
  have hright := Finset.card_union_le (E M v ∩ B M w) (E M v ∩ E M w)
  omega

theorem neighbors_subset_primary_secondary (M : MergedPairs F) (v : CandidateVertex F) :
    candidateNeighbors M v ⊆ (B M v ∪ E M v) ∪ secondary M v := by
  intro z hz
  by_cases hp : z ∈ B M v ∪ E M v
  · exact Finset.mem_union_left _ hp
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, hp⟩)

theorem common_neighbors_subset (M : MergedPairs F) (v w : CandidateVertex F) :
    candidateNeighbors M v ∩ candidateNeighbors M w ⊆
      (((B M v ∪ E M v) ∩ (B M w ∪ E M w)) ∪ secondary M v) ∪ secondary M w := by
  intro z hz
  rcases Finset.mem_inter.mp hz with ⟨hzv, hzw⟩
  by_cases hvp : z ∈ B M v ∪ E M v
  · by_cases hwp : z ∈ B M w ∪ E M w
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvp, hwp⟩))
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzw, hwp⟩)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzv, hvp⟩))

theorem codegree_le_of_incidence_bounds {v w : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (hw : w ∈ candidateVertices M)
    (hex : w ∉ exceptionalSet M v) {P R : ℕ}
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (hmixedv : ∀ p, ¬ OnLine p (candidateLine v) →
      (pointLineCandidates M p (candidateLine v)).card ≤ P)
    (hmixedw : ∀ p, ¬ OnLine p (candidateLine w) →
      (pointLineCandidates M p (candidateLine w)).card ≤ P)
    (htwo : (twoLineCandidates M (candidateLine v) (candidateLine w)).card ≤ P)
    (hRv : (secondary M v).card ≤ R) (hRw : (secondary M w).card ≤ R) :
    (candidateNeighbors M v ∩ candidateNeighbors M w).card ≤ 48 + 10 * P + 2 * R := by
  have hgeom := not_exceptional_distinct_disjoint hw hex
  have hprimary := primary_common_card_le hv hw (Ne.symm hgeom.1) hgeom.2.symm
    hpoint hmixedv hmixedw htwo
  have hsub := Finset.card_le_card (common_neighbors_subset M v w)
  have houter := Finset.card_union_le
    (((B M v ∪ E M v) ∩ (B M w ∪ E M w)) ∪ secondary M v) (secondary M w)
  have hinner := Finset.card_union_le
    ((B M v ∪ E M v) ∩ (B M w ∪ E M w)) (secondary M v)
  omega

theorem degree_le_of_incidence_bounds {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {Ebound R : ℕ}
    (hE : (E M v).card ≤ Ebound) (hR : (secondary M v).card ≤ R) :
    (candidateNeighbors M v).card ≤ 8 * (Fintype.card F + 1) + Ebound + R := by
  have hB := B_card_le hv
  have hsub := Finset.card_le_card (neighbors_subset_primary_secondary M v)
  have houter := Finset.card_union_le (B M v ∪ E M v) (secondary M v)
  have hinner := Finset.card_union_le (B M v) (E M v)
  omega

theorem slot_degree_le_of_incidence_bounds {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) (s : Slot F) {Ebound R : ℕ}
    (hE : (E M v ∩ candidateSlot M s).card ≤ Ebound)
    (hR : (secondary M v).card ≤ R) :
    (candidateNeighbors M v ∩ candidateSlot M s).card ≤ 4 + Ebound + R := by
  have hB := B_slot_card_le_four hv s
  have hsub : candidateNeighbors M v ∩ candidateSlot M s ⊆
      ((B M v ∩ candidateSlot M s) ∪ (E M v ∩ candidateSlot M s)) ∪ secondary M v := by
    intro z hz
    rcases Finset.mem_inter.mp hz with ⟨hzn, hzs⟩
    rcases Finset.mem_union.mp (neighbors_subset_primary_secondary M v hzn) with hp | hr
    · apply Finset.mem_union_left
      rcases Finset.mem_union.mp hp with hb | he
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hb, hzs⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨he, hzs⟩)
    · exact Finset.mem_union_right _ hr
  have hcard := Finset.card_le_card hsub
  have houter := Finset.card_union_le
    ((B M v ∩ candidateSlot M s) ∪ (E M v ∩ candidateSlot M s)) (secondary M v)
  have hinner := Finset.card_union_le (B M v ∩ candidateSlot M s) (E M v ∩ candidateSlot M s)
  omega

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateSecondary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {M : MergedPairs F}

theorem generators_card {v : CandidateVertex F} (hv : v ∈ candidateVertices M) :
    (generators M v).card = 4 := by
  have hinj := (valid hv).2.2.1
  simpa [generators, generatorSet] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin 4)) hinj

theorem generator_conflicts_card_le {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {P : ℕ}
    (hpair : ∀ e : Finset (Direction F), e.card = 2 → (generatorPairCandidates M e).card ≤ P) :
    (generatorConflicts M v).card ≤ 6 * P := by
  have hsub : generatorConflicts M v ⊆
      ((generators M v).powersetCard 2).biUnion (generatorPairCandidates M) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, htwo⟩
    obtain ⟨e, he, hcard⟩ := Finset.exists_subset_card_eq htwo
    have hev : e ⊆ generators M v := fun x hx => (Finset.mem_inter.mp (he hx)).1
    have hew : e ⊆ generators M w := fun x hx => (Finset.mem_inter.mp (he hx)).2
    exact Finset.mem_biUnion.mpr
      ⟨e, Finset.mem_powersetCard.mpr ⟨hev, hcard⟩, Finset.mem_filter.mpr ⟨hwv, hew⟩⟩
  calc
    (generatorConflicts M v).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ e ∈ (generators M v).powersetCard 2, (generatorPairCandidates M e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ (generators M v).powersetCard 2, P :=
      Finset.sum_le_sum (fun e he => hpair e (Finset.mem_powersetCard.mp he).2)
    _ = 6 * P := by norm_num [Finset.card_powersetCard, generators_card hv, Nat.choose]

theorem directionsAt_card_le_multiplicity (M : MergedPairs F) (p : Point F) :
    (directionsAt M p).card ≤ sampledMultiplicity M p := Finset.card_image_le

theorem mem_directionsAt_iff (M : MergedPairs F) (p : Point F) (d : Direction F) :
    d ∈ directionsAt M p ↔ p ∈ mergedPoints M d := by
  simp only [directionsAt, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    mergedPoints, Finset.mem_union, linePoints]
  constructor
  · rintro ⟨⟨d', b⟩, hp, rfl⟩
    cases b with
    | false => exact Or.inl hp
    | true => exact Or.inr hp
  · rintro (hp | hp)
    · exact ⟨(d, false), hp, rfl⟩
    · exact ⟨(d, true), hp, rfl⟩

theorem mem_touchedDirections_iff (M : MergedPairs F) (v : CandidateVertex F)
    (d : Direction F) :
    d ∈ touchedDirections M v ↔ (points M v ∩ mergedPoints M d).Nonempty := by
  simp only [touchedDirections, Finset.mem_biUnion, mem_directionsAt_iff]
  constructor
  · rintro ⟨p, hp, hpd⟩
    exact ⟨p, Finset.mem_inter.mpr ⟨hp, hpd⟩⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩

theorem touchedDirections_card_le {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {cap : ℕ}
    (hcap : ∀ p, sampledMultiplicity M p ≤ cap) :
    (touchedDirections M v).card ≤ 4 * cap := by
  calc
    (touchedDirections M v).card ≤ ∑ p ∈ points M v, (directionsAt M p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ points M v, cap := Finset.sum_le_sum
      (fun p _ => (directionsAt_card_le_multiplicity M p).trans (hcap p))
    _ = 4 * cap := by simp [points_card hv]

theorem secondary_subset_generator_merged (M : MergedPairs F) (v : CandidateVertex F) :
    secondary M v ⊆ generatorConflicts M v ∪ mergedConflicts M v := by
  intro w hw
  rcases Finset.mem_sdiff.mp hw with ⟨hwn, hnot⟩
  have hadj := (Finset.mem_filter.mp hwn).2
  have hwv := hadj.2.1
  have hnotB : w ∉ B M v := fun h => hnot (Finset.mem_union_left _ h)
  have hnotE : w ∉ E M v := fun h => hnot (Finset.mem_union_right _ h)
  have hpv : ∀ p ∈ points M v, ¬ OnLine p (candidateLine w) := by
    intro p hp hline
    exact hnotB (Finset.mem_filter.mpr ⟨hwv, p, hp, hline⟩)
  have hpw : ∀ p ∈ points M w, ¬ OnLine p (candidateLine v) := by
    intro p hp hline
    exact hnotE (Finset.mem_filter.mpr ⟨hwv, p, hp, hline⟩)
  by_cases hgen : (generators M v ∩ generators M w).card ≤ 1
  · apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hwv, ?_⟩
    by_contra hn
    apply hadj.2.2.2
    refine ⟨hpv, hpw, hgen, ?_⟩
    intro heq d
    constructor
    · intro hbad
      apply hn
      have hvpos : 0 < (points M v ∩ mergedPoints M d).card :=
        lt_of_lt_of_le (by decide : 0 < 2) hbad.1
      have hwpos : 0 < (points M w ∩ mergedPoints M d).card := hbad.2
      exact ⟨heq, d, Finset.card_pos.mp hvpos, Finset.card_pos.mp hwpos⟩
    · intro hbad
      apply hn
      have hvpos : 0 < (points M v ∩ mergedPoints M d).card := hbad.2
      have hwpos : 0 < (points M w ∩ mergedPoints M d).card :=
        lt_of_lt_of_le (by decide : 0 < 2) hbad.1
      exact ⟨heq, d, Finset.card_pos.mp hvpos, Finset.card_pos.mp hwpos⟩
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hwv, by omega⟩

theorem mergedHit_candidates_card_le (M : MergedPairs F) (g d : Direction F) {A : ℕ}
    (hline : ∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ A) :
    (mergedHitCandidates M g d).card ≤ 4 * A := by
  let U := Finset.univ.biUnion (fun sb : Bool × Bool =>
    lineHitSlot M (g, sb.1) (constituent M d sb.2))
  have hsub : mergedHitCandidates M g d ⊆ U := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, hdir, p, hp⟩
    rcases Finset.mem_inter.mp hp with ⟨hpw, hpm⟩
    have hpm' : OnLine p (constituent M d false) ∨ OnLine p (constituent M d true) := by
      simpa [mergedPoints, linePoints] using hpm
    have hws : w ∈ candidateSlot M (g, w.1.2) :=
      mem_candidateSlot.mpr ⟨mem_candidateVertices.mp hwv, Prod.ext hdir rfl⟩
    rcases hpm' with hl | hl
    · exact Finset.mem_biUnion.mpr ⟨(w.1.2, false), Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hws, p, hpw, hl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨(w.1.2, true), Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨hws, p, hpw, hl⟩⟩
  calc
    (mergedHitCandidates M g d).card ≤ U.card := Finset.card_le_card hsub
    _ ≤ ∑ sb : Bool × Bool, (lineHitSlot M (g, sb.1) (constituent M d sb.2)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _sb : Bool × Bool, A := Finset.sum_le_sum (fun sb _ => hline _ _)
    _ = 4 * A := by simp

theorem merged_conflicts_card_le {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {cap A : ℕ}
    (hcap : ∀ p, sampledMultiplicity M p ≤ cap)
    (hline : ∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ A) :
    (mergedConflicts M v).card ≤ 16 * cap * A := by
  have hsub : mergedConflicts M v ⊆
      (touchedDirections M v).biUnion (mergedHitCandidates M v.1.1) := by
    intro w hw
    rcases Finset.mem_filter.mp hw with ⟨hwv, hdir, d, hdv, hdw⟩
    exact Finset.mem_biUnion.mpr ⟨d, (mem_touchedDirections_iff M v d).mpr hdv,
      Finset.mem_filter.mpr ⟨hwv, hdir.symm, hdw⟩⟩
  calc
    (mergedConflicts M v).card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ d ∈ touchedDirections M v, (mergedHitCandidates M v.1.1 d).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ touchedDirections M v, 4 * A :=
      Finset.sum_le_sum (fun d _ => mergedHit_candidates_card_le M _ d hline)
    _ = (touchedDirections M v).card * (4 * A) := by simp
    _ ≤ (4 * cap) * (4 * A) :=
      Nat.mul_le_mul_right (4 * A) (touchedDirections_card_le hv hcap)
    _ = 16 * cap * A := by ring

theorem secondary_card_le {v : CandidateVertex F}
    (hv : v ∈ candidateVertices M) {P cap A : ℕ}
    (hpair : ∀ e : Finset (Direction F), e.card = 2 → (generatorPairCandidates M e).card ≤ P)
    (hcap : ∀ p, sampledMultiplicity M p ≤ cap)
    (hline : ∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ A) :
    (secondary M v).card ≤ 6 * P + 16 * cap * A := by
  apply (Finset.card_le_card (secondary_subset_generator_merged M v)).trans
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (generator_conflicts_card_le hv hpair) (merged_conflicts_card_le hv hcap hline))

theorem E_inter_slot_eq_lineHitSlot (M : MergedPairs F) (v : CandidateVertex F) (s : Slot F) :
    E M v ∩ candidateSlot M s = lineHitSlot M s (candidateLine v) := by
  ext w
  simp only [E, lineHitSlot, Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨⟨_, hp⟩, hws⟩
    exact ⟨hws, hp⟩
  · rintro ⟨hws, hp⟩
    exact ⟨⟨Finset.mem_of_mem_filter w hws, hp⟩, hws⟩

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGraphReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem candidateGraphGood_of_counts (M : MergedPairs F) (c C : ℝ)
    (P A cap D : ℕ)
    (hsize : ∀ s : Slot F, c * Fintype.card F ≤ ((candidateSlot M s).card : ℝ))
    (hpoint : ∀ p, (pointCandidates M p).card ≤ P)
    (hmixed : ∀ p l, ¬ OnLine p l → (pointLineCandidates M p l).card ≤ P)
    (htwo : ∀ l k : Line F, l ≠ k → l ∉ constituentLines M → k ∉ constituentLines M →
      (twoLineCandidates M l k).card ≤ P)
    (hpair : ∀ e : Finset (Direction F), e.card = 2 → (generatorPairCandidates M e).card ≤ P)
    (hcap : ∀ p, sampledMultiplicity M p ≤ cap)
    (hcaplog : cap ≤ Nat.ceil (Real.log (Fintype.card F)))
    (hline : ∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ A)
    (hglobal : ∀ l : Line F, l ∉ constituentLines M →
      ((candidateVertices M).filter (fun w => ∃ p ∈ points M w, OnLine p l)).card ≤ D)
    (hdegree : ((8 * (Fintype.card F + 1) + D + (6 * P + 16 * cap * A) : ℕ) : ℝ) ≤
      C * Fintype.card F)
    (hslot : ((4 + A + (6 * P + 16 * cap * A) : ℕ) : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 / 8 : ℝ))
    (hexception : ((2 + 4 * P : ℕ) : ℝ) ≤ (Fintype.card F : ℝ) ^ (1 / 8 : ℝ))
    (hcodegree : ((48 + 10 * P + 2 * (6 * P + 16 * cap * A) : ℕ) : ℝ) ≤
      (Fintype.card F : ℝ) ^ (1 / 8 : ℝ))
    (hoccupancy : ∀ l : Line F, l ∉ initialDeletedLines M →
      (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)) :
    CandidateGraphGood M c C := by
  have hsecondary : ∀ v ∈ candidateVertices M,
      (secondary M v).card ≤ 6 * P + 16 * cap * A := by
    intro v hv
    exact secondary_card_le hv hpair hcap hline
  have hnonconst : ∀ v ∈ candidateVertices M, candidateLine v ∉ constituentLines M := by
    intro v hv
    exact (valid hv).2.1
  refine ⟨?_, ?_, ?_, ?_, hoccupancy⟩
  · intro s
    exact ⟨hsize s, candidateSlot_card_le M s⟩
  · intro v hv
    constructor
    · have hn := degree_le_of_incidence_bounds hv
        (hglobal (candidateLine v) (hnonconst v hv)) (hsecondary v hv)
      exact (show ((candidateNeighbors M v).card : ℝ) ≤
          ((8 * (Fintype.card F + 1) + D + (6 * P + 16 * cap * A) : ℕ) : ℝ) by
        exact_mod_cast hn).trans hdegree
    · intro s
      have hE : (E M v ∩ candidateSlot M s).card ≤ A := by
        rw [E_inter_slot_eq_lineHitSlot]
        exact hline s (candidateLine v)
      have hn := slot_degree_le_of_incidence_bounds hv s hE (hsecondary v hv)
      exact (show ((candidateNeighbors M v ∩ candidateSlot M s).card : ℝ) ≤
          ((4 + A + (6 * P + 16 * cap * A) : ℕ) : ℝ) by exact_mod_cast hn).trans hslot
  · intro v hv
    refine ⟨exceptionalSet M v, exceptional_subset M v, ?_, ?_, ?_⟩
    · have hn := exceptional_card_le hv hpoint
      exact (show ((exceptionalSet M v).card : ℝ) ≤ ((2 + 4 * P : ℕ) : ℝ) by
        exact_mod_cast hn).trans hexception
    · intro w hw
      exact exceptional_adjacent_or_same_slot hv hw
    · intro w hw hex
      have hgeom := not_exceptional_distinct_disjoint hw hex
      have hn := codegree_le_of_incidence_bounds hv hw hex hpoint
        (fun p hp => hmixed p (candidateLine v) hp)
        (fun p hp => hmixed p (candidateLine w) hp)
        (htwo (candidateLine v) (candidateLine w) (Ne.symm hgeom.1)
          (hnonconst v hv) (hnonconst w hw))
        (hsecondary v hv) (hsecondary w hw)
      exact (show ((candidateNeighbors M v ∩ candidateNeighbors M w).card : ℝ) ≤
          ((48 + 10 * P + 2 * (6 * P + 16 * cap * A) : ℕ) : ℝ) by
        exact_mod_cast hn).trans hcodegree
  · intro p
    exact (hcap p).trans hcaplog

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateCountAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Balanced.CandidateAsymptotics

theorem eventually_scaled_candidate_numerics (a : ℕ) (ha : 1 ≤ a) :
    ∀ᶠ q : ℕ in atTop,
    let P := a * Nat.ceil ((q : ℝ) ^ (1 / 100 : ℝ))
    let B := Nat.ceil (Real.log (q : ℝ))
    let R := 6 * P + 16 * B * P
    (((2 + 4 * P : ℕ) : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
    (((4 + P + R : ℕ) : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
    (((48 + 10 * P + 2 * R : ℕ) : ℝ) ≤ (q : ℝ) ^ (1 / 8 : ℝ)) ∧
    (((8 * (q + 1) + R : ℕ) : ℝ) ≤ 10 * q) := by
  have hsmall := eventually_scaled_product_le (102 * (a : ℝ))
  have hlogone : ∀ᶠ q : ℕ in atTop, 1 ≤ Real.log (q : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hsmall, hlogone, eventually_ge_atTop 8] with q hsmall hlog hq
  dsimp only
  let P : ℝ := (a : ℝ) * Nat.ceil ((q : ℝ) ^ (1 / 100 : ℝ))
  let B : ℝ := Nat.ceil (Real.log (q : ℝ))
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hceil : (1 : ℝ) ≤ Nat.ceil ((q : ℝ) ^ (1 / 100 : ℝ)) :=
    (Real.one_le_rpow hqone (by norm_num : (0 : ℝ) ≤ 1 / 100)).trans (Nat.le_ceil _)
  have hP : 1 ≤ P := by dsimp [P]; nlinarith
  have hB : 1 ≤ B := hlog.trans (Nat.le_ceil _)
  have hBP : 1 ≤ B * P := by nlinarith
  have hPBP : P ≤ B * P := by nlinarith
  have hbig : 102 * (B * P) ≤ (q : ℝ) ^ (1 / 8 : ℝ) := by
    dsimp [P, B]
    nlinarith [hsmall]
  have hpowq : (q : ℝ) ^ (1 / 8 : ℝ) ≤ q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hqone
      (by norm_num : (1 / 8 : ℝ) ≤ 1)
  have hq8 : (8 : ℝ) ≤ q := by exact_mod_cast hq
  push_cast
  change (2 + 4 * P ≤ _) ∧ (4 + P + (6 * P + 16 * B * P) ≤ _) ∧
    (48 + 10 * P + 2 * (6 * P + 16 * B * P) ≤ _) ∧
    (8 * ((q : ℝ) + 1) + (6 * P + 16 * B * P) ≤ _)
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

end Balanced.CandidateAsymptotics

namespace Balanced.CandidateIncidence

noncomputable section
open scoped Classical
universe u

theorem exists_threshold_candidateGraphGood_of_scaled_counts
    (a : ℕ) (ha : 1 ≤ a) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F → ∀ (M : MergedPairs F) (c : ℝ),
      let P := a * Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))
      (∀ s : Slot F, c * Fintype.card F ≤ ((candidateSlot M s).card : ℝ)) →
      (∀ p, (pointCandidates M p).card ≤ P) →
      (∀ p l, ¬ OnLine p l → (pointLineCandidates M p l).card ≤ P) →
      (∀ l k : Line F, l ≠ k → l ∉ constituentLines M → k ∉ constituentLines M →
        (twoLineCandidates M l k).card ≤ P) →
      (∀ e : Finset (Direction F), e.card = 2 → (generatorPairCandidates M e).card ≤ P) →
      (∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card F : ℝ))) →
      (∀ s : Slot F, ∀ l : Line F, (lineHitSlot M s l).card ≤ P) →
      (∀ l : Line F, l ∉ constituentLines M →
        (((candidateVertices M).filter (fun w => ∃ p ∈ points M w, OnLine p l)).card : ℝ) ≤
          C * Fintype.card F) →
      (∀ l : Line F, l ∉ initialDeletedLines M →
        (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)) →
      CandidateGraphGood M c (C + 11) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((CandidateAsymptotics.eventually_scaled_candidate_numerics a ha).and
      (eventually_ge_atTop 1))
  refine ⟨N, ?_⟩
  intro F _ _ _ hq M c P hsize hpoint hmixed htwo hpair hcap hline hglobal hoccupancy
  obtain ⟨hnum, hqone⟩ := hN (Fintype.card F) hq
  let B := Nat.ceil (Real.log (Fintype.card F : ℝ))
  let D := Nat.ceil (C * (Fintype.card F : ℝ))
  apply candidateGraphGood_of_counts M c (C + 11) P P B D
    hsize hpoint hmixed htwo hpair hcap le_rfl hline
  · intro l hl
    exact_mod_cast (hglobal l hl).trans (Nat.le_ceil _)
  · have hD : (D : ℝ) < C * (Fintype.card F : ℝ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hC (Nat.cast_nonneg _))
    have hqreal : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast hqone
    have hn := hnum.2.2.2
    change (((8 * (Fintype.card F + 1) + (6 * P + 16 * B * P) : ℕ) : ℝ)) ≤
      10 * (Fintype.card F : ℝ) at hn
    push_cast at hn ⊢
    nlinarith
  · exact hnum.2.1
  · exact hnum.1
  · exact hnum.2.2.1
  · exact hoccupancy

end
end Balanced.CandidateIncidence

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_ConstituentMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Finset

theorem uniform_toOuterMeasure_equiv
    {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [Nonempty Ω] [Nonempty Ξ]
    (e : Ω ≃ Ξ) (A : Set Ξ) :
    (PMF.uniformOfFintype Ω).toOuterMeasure (e ⁻¹' A) =
      (PMF.uniformOfFintype Ξ).toOuterMeasure A := by
  classical
  let eA : (e ⁻¹' A) ≃ A :=
    { toFun := fun x => ⟨e x, x.2⟩
      invFun := fun y => ⟨e.symm y, by simp⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by intro y; apply Subtype.ext; simp }
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply,
    Fintype.card_congr eA, Fintype.card_congr e]

section Counting

variable {I F : Type*} [Fintype I] [Fintype F]
variable [DecidableEq I] [DecidableEq F]

theorem card_prescribed_coordinates (s : Finset I) (target : I → F) :
    (Finset.univ.filter (fun ω : I → F => ∀ i ∈ s, ω i = target i)).card =
      Fintype.card F ^ (Fintype.card I - s.card) := by
  have hset : Finset.univ.filter (fun ω : I → F => ∀ i ∈ s, ω i = target i) =
      Fintype.piFinset (fun i => if i ∈ s then {target i} else Finset.univ) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h i
      split_ifs with hi
      · simpa using h i hi
      · simp
    · intro h i hi
      simpa [hi] using h i
  rw [hset, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Finset.card_singleton, Finset.card_univ]
  rw [Finset.prod_ite]
  simp [← Finset.compl_eq_univ_sdiff, Finset.filter_not, Finset.card_compl]

theorem card_many_coordinate_matches_le (target : I → F) (m : ℕ) :
    (Finset.univ.filter (fun ω : I → F =>
      m ≤ (Finset.univ.filter (fun i => ω i = target i)).card)).card ≤
      (Fintype.card I).choose m * Fintype.card F ^ (Fintype.card I - m) := by
  classical
  let cylinder (s : Finset I) : Finset (I → F) :=
    Finset.univ.filter (fun ω => ∀ i ∈ s, ω i = target i)
  have hcover : Finset.univ.filter (fun ω : I → F =>
      m ≤ (Finset.univ.filter (fun i => ω i = target i)).card) ⊆
      ((Finset.univ : Finset I).powersetCard m).biUnion cylinder := by
    intro ω hω
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (Finset.mem_filter.mp hω).2
    apply Finset.mem_biUnion.mpr
    refine ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, hcard⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ ω, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp (hs hi)).2
  calc
    _ ≤ (((Finset.univ : Finset I).powersetCard m).biUnion cylinder).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ s ∈ (Finset.univ : Finset I).powersetCard m, (cylinder s).card :=
      Finset.card_biUnion_le
    _ = ∑ _s ∈ (Finset.univ : Finset I).powersetCard m,
        Fintype.card F ^ (Fintype.card I - m) := by
      apply Finset.sum_congr rfl
      intro s hs
      dsimp only [cylinder]
      rw [card_prescribed_coordinates,
        (Finset.mem_powersetCard.mp hs).2]
    _ = _ := by simp

theorem uniform_many_coordinate_matches_le [Nonempty F] (target : I → F) (m : ℕ) :
    ((PMF.uniformOfFintype (I → F)).toOuterMeasure
      {ω | m ≤ (Finset.univ.filter (fun i => ω i = target i)).card}).toReal ≤
      ((Fintype.card I).choose m : ℝ) / (Fintype.card F : ℝ) ^ m := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, Set.mem_ofPred_eq,
    Fintype.card_subtype, Fintype.card_fun, Nat.cast_pow]
  have hcard := card_many_coordinate_matches_le target m
  have hreal :
      ((Finset.univ.filter (fun ω : I → F =>
        m ≤ (Finset.univ.filter (fun i => ω i = target i)).card)).card : ℝ) ≤
      ((Fintype.card I).choose m : ℝ) *
        (Fintype.card F : ℝ) ^ (Fintype.card I - m) := by
    exact_mod_cast hcard
  have hq : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := F)
  by_cases hmn : m ≤ Fintype.card I
  · calc
      _ ≤ (((Fintype.card I).choose m : ℝ) *
          (Fintype.card F : ℝ) ^ (Fintype.card I - m)) /
          (Fintype.card F : ℝ) ^ Fintype.card I :=
        div_le_div_of_nonneg_right hreal (by positivity)
      _ = _ := by
        rw [show (Fintype.card F : ℝ) ^ Fintype.card I =
          (Fintype.card F : ℝ) ^ (Fintype.card I - m) *
            (Fintype.card F : ℝ) ^ m by
          rw [← pow_add, Nat.sub_add_cancel hmn]]
        field_simp
  · have hz : (Fintype.card I).choose m = 0 :=
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hmn)
    simp only [hz, Nat.cast_zero, zero_mul, zero_div] at hreal ⊢
    exact div_nonpos_of_nonpos_of_nonneg hreal (by positivity)

theorem uniform_exists_many_coordinate_matches_le
    [Nonempty F] {P : Type*} [Fintype P] (target : P → I → F) (m : ℕ) :
    ((PMF.uniformOfFintype (I → F)).toOuterMeasure
      {ω | ∃ p, m ≤ (Finset.univ.filter (fun i => ω i = target p i)).card}).toReal ≤
      (Fintype.card P : ℝ) *
        (((Fintype.card I).choose m : ℝ) / (Fintype.card F : ℝ) ^ m) := by
  classical
  let bad (p : P) : Finset (I → F) := Finset.univ.filter (fun ω =>
    m ≤ (Finset.univ.filter (fun i => ω i = target p i)).card)
  have hset : Finset.univ.filter (fun ω : I → F =>
      ∃ p, m ≤ (Finset.univ.filter (fun i => ω i = target p i)).card) =
      Finset.univ.biUnion bad := by
    ext ω
    simp [bad]
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, Set.mem_ofPred_eq,
    Fintype.card_subtype, Fintype.card_fun, Nat.cast_pow]
  rw [hset]
  have hcount : ((Finset.univ.biUnion bad).card : ℝ) ≤
      ∑ p : P, ((bad p).card : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset P)) (t := bad))
  calc
    _ ≤ (∑ p : P, ((bad p).card : ℝ)) / (Fintype.card F : ℝ) ^ Fintype.card I :=
      div_le_div_of_nonneg_right hcount (by positivity)
    _ = ∑ p : P, ((bad p).card : ℝ) / (Fintype.card F : ℝ) ^ Fintype.card I :=
      Finset.sum_div _ _ _
    _ ≤ ∑ _p : P, (((Fintype.card I).choose m : ℝ) / (Fintype.card F : ℝ) ^ m) := by
      apply Finset.sum_le_sum
      intro p _
      have hp := uniform_many_coordinate_matches_le (target p) m
      rw [PMF.toOuterMeasure_uniformOfFintype_apply] at hp
      simpa only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, Set.mem_ofPred_eq,
        Fintype.card_subtype, Fintype.card_fun, Nat.cast_pow, bad] using hp
    _ = _ := by simp

end Counting

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_LogTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology

namespace BalancedRyser

theorem polynomial_mul_ratio_pow_le_inv
    (q r B : ℕ) (C : ℝ) (hq : 0 < q) (hBpos : 0 < B)
    (hC : 0 ≤ C) (hlog : Real.log (q : ℝ) ≤ (B : ℝ))
    (hlarge : C * Real.exp ((r : ℝ) + 1) ≤ (B : ℝ)) :
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B ≤ (q : ℝ)⁻¹ := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hbase : C / (B : ℝ) ≤ Real.exp (-((r : ℝ) + 1)) := by
    rw [Real.exp_neg]
    apply (div_le_iff₀ hBR).2
    simpa [div_eq_mul_inv, mul_comm] using
      ((le_div_iff₀ (Real.exp_pos ((r : ℝ) + 1))).2 hlarge)
  have hpow : (C / (B : ℝ)) ^ B ≤
      Real.exp (-((r : ℝ) + 1)) ^ B :=
    pow_le_pow_left₀ (div_nonneg hC hBR.le) hbase B
  calc
    (q : ℝ) ^ r * (C / (B : ℝ)) ^ B
        ≤ (q : ℝ) ^ r * Real.exp (-((r : ℝ) + 1)) ^ B :=
      mul_le_mul_of_nonneg_left hpow (pow_nonneg hqR.le _)
    _ = Real.exp ((r : ℝ) * Real.log (q : ℝ) - ((r : ℝ) + 1) * B) := by
      have hqpow : (q : ℝ) ^ r = Real.exp ((r : ℝ) * Real.log (q : ℝ)) := by
        rw [Real.exp_nat_mul, Real.exp_log hqR]
      rw [hqpow, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-Real.log (q : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
      nlinarith
    _ = (q : ℝ)⁻¹ := by rw [Real.exp_neg, Real.exp_log hqR]

theorem tendsto_log_cutoff_atTop :
    Tendsto (fun q : ℕ => Nat.ceil (Real.log (q : ℝ))) atTop atTop :=
  tendsto_nat_ceil_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

theorem tendsto_polynomial_mul_cutoff_tail
    (B : ℕ → ℕ)
    (hlog : ∀ᶠ q : ℕ in atTop, Real.log (q : ℝ) ≤ (B q : ℝ))
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ r * (C / (B q : ℝ)) ^ B q)
      atTop (𝓝 0) := by
  have hcut : Tendsto (fun q : ℕ => (B q : ℝ)) atTop atTop :=
    tendsto_atTop_mono' _ hlog
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall (fun q =>
      mul_nonneg (pow_nonneg (Nat.cast_nonneg q) r)
        (pow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _))
  · filter_upwards [eventually_gt_atTop (0 : ℕ), hlog,
      hcut.eventually (eventually_gt_atTop 0),
      hcut.eventually (eventually_ge_atTop (C * Real.exp ((r : ℝ) + 1)))]
      with q hq hlogq hB hlarge
    exact polynomial_mul_ratio_pow_le_inv q r _ C hq
      (by exact_mod_cast hB) hC hlogq hlarge
  · exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem tendsto_polynomial_mul_log_cutoff_tail
    (r : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun q : ℕ =>
      (q : ℝ) ^ r *
        (C / (Nat.ceil (Real.log (q : ℝ)) : ℝ)) ^
          Nat.ceil (Real.log (q : ℝ))) atTop (𝓝 0) :=
  tendsto_polynomial_mul_cutoff_tail _
    (Filter.Eventually.of_forall (fun _ => Nat.le_ceil _)) r C hC

theorem choose_le_exp_mul_div_pow (n B : ℕ) (hB : 0 < B) :
    (n.choose B : ℝ) ≤ (Real.exp 1 * n / B) ^ B := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hf : (0 : ℝ) < B.factorial := by
    exact_mod_cast Nat.factorial_pos B
  have hseries := Real.pow_div_factorial_le_exp (B : ℝ) hBR.le B
  have hinv : 1 / (B.factorial : ℝ) ≤ (Real.exp 1 / B) ^ B := by
    rw [div_pow, Real.exp_one_pow]
    apply (div_le_div_iff₀ hf (pow_pos hBR B)).2
    simpa using (div_le_iff₀ hf).1 hseries
  calc
    (n.choose B : ℝ) ≤ (n : ℝ) ^ B / B.factorial := Nat.choose_le_pow_div B n
    _ = (n : ℝ) ^ B * (1 / (B.factorial : ℝ)) := by ring
    _ ≤ (n : ℝ) ^ B * (Real.exp 1 / B) ^ B :=
      mul_le_mul_of_nonneg_left hinv (pow_nonneg (Nat.cast_nonneg n) B)
    _ = (Real.exp 1 * n / B) ^ B := by rw [← mul_pow]; congr 1; ring

theorem slot_choose_mul_pow_le
    (q B : ℕ) (K : ℝ) (hq : 0 < q) (hB : 0 < B) (hK : 0 ≤ K) :
    ((2 * (q + 1)).choose B : ℝ) * (K / (q : ℝ)) ^ B ≤
      (4 * Real.exp 1 * K / (B : ℝ)) ^ B := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  calc
    ((2 * (q + 1)).choose B : ℝ) * (K / (q : ℝ)) ^ B
        ≤ (Real.exp 1 * (2 * (q + 1) : ℕ) / B) ^ B * (K / (q : ℝ)) ^ B :=
      mul_le_mul_of_nonneg_right (choose_le_exp_mul_div_pow _ B hB)
        (pow_nonneg (div_nonneg hK hqR.le) B)
    _ = (Real.exp 1 * (2 * (q + 1) : ℕ) / B * (K / (q : ℝ))) ^ B := by
      rw [mul_pow]
    _ ≤ (4 * Real.exp 1 * K / (B : ℝ)) ^ B := by
      apply pow_le_pow_left₀ (by positivity)
      have hratio : (2 * (q + 1) : ℕ) / (q : ℝ) ≤ 4 := by
        apply (div_le_iff₀ hqR).2
        push_cast
        linarith
      have hmul := mul_le_mul_of_nonneg_left hratio
        (mul_nonneg (Real.exp_pos 1).le hK)
      have hdiv := div_le_div_of_nonneg_right hmul hBR.le
      convert hdiv using 1 <;> ring

theorem tendsto_polynomial_mul_slot_choose_tail
    (r : ℕ) (K : ℝ) (hK : 0 ≤ K) :
    Tendsto (fun q : ℕ =>
      (q : ℝ) ^ r *
        (((2 * (q + 1)).choose (Nat.ceil (Real.log (q : ℝ))) : ℝ) *
          (K / (q : ℝ)) ^ Nat.ceil (Real.log (q : ℝ))))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_polynomial_mul_log_cutoff_tail r (4 * Real.exp 1 * K) (by positivity))
  · exact Filter.Eventually.of_forall (fun q => by positivity)
  · filter_upwards [eventually_gt_atTop (0 : ℕ),
      tendsto_log_cutoff_atTop.eventually (eventually_gt_atTop 0)] with q hq hB
    exact mul_le_mul_of_nonneg_left (slot_choose_mul_pow_le q _ K hq hB hK)
      (pow_nonneg (Nat.cast_nonneg q) r)

end BalancedRyser

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_ProbabilityPerturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced

open MeasureTheory Filter
open scoped Topology

section SingleSpace

variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem probReal_inter_ge_sub (A G : Set Ω) (hG : MeasurableSet G) :
    μ.real A - (1 - μ.real G) ≤ μ.real (A ∩ G) := by
  have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := A) hG
  have hbound : μ.real (A \ G) ≤ 1 - μ.real G := by
    rw [← probReal_compl_eq_one_sub (μ := μ) hG]
    exact measureReal_mono (Set.sdiff_subset_compl A G)
  linarith

end SingleSpace

section VaryingSpaces

variable {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
variable (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]

theorem tendsto_probReal_inter_of_good
    {l : Filter ι} (A G : ∀ i, Set (Ω i)) (hGmeas : ∀ i, MeasurableSet (G i))
    {L : ℝ} (hA : Tendsto (fun i => (μ i).real (A i)) l (𝓝 L))
    (hG : Tendsto (fun i => (μ i).real (G i)) l (𝓝 1)) :
    Tendsto (fun i => (μ i).real (A i ∩ G i)) l (𝓝 L) := by
  have hlower : Tendsto (fun i => (μ i).real (A i) - (1 - (μ i).real (G i)))
      l (𝓝 L) := by
    simpa using hA.sub ((tendsto_const_nhds (x := (1 : ℝ))).sub hG)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlower hA
    (fun i => probReal_inter_ge_sub (μ i) (A i) (G i) (hGmeas i))
    (fun i => measureReal_mono Set.inter_subset_left)

end VaryingSpaces

theorem pmf_outerReal_mono {Ω : Type*} (p : PMF Ω) {A B : Set Ω} (h : A ⊆ B) :
    (p.toOuterMeasure A).toReal ≤ (p.toOuterMeasure B).toReal := by
  let : MeasurableSpace Ω := ⊤
  have hA : MeasurableSet A := by trivial
  have hB : MeasurableSet B := by trivial
  have hmono := measureReal_mono (μ := p.toMeasure) h
  simpa only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply p hB] using hmono

theorem pmf_outerReal_compl {Ω : Type*} (p : PMF Ω) (A : Set Ω) :
    (p.toOuterMeasure Aᶜ).toReal = 1 - (p.toOuterMeasure A).toReal := by
  let : MeasurableSpace Ω := ⊤
  have hA : MeasurableSet A := by trivial
  have hcompl := probReal_compl_eq_one_sub (μ := p.toMeasure) hA
  simpa only [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply p hA.compl] using hcompl

theorem tendsto_pmf_outerReal_inter_of_good
    {ι : Type*} {Ω : ι → Type*} (p : ∀ i, PMF (Ω i))
    {l : Filter ι} (A G : ∀ i, Set (Ω i)) {L : ℝ}
    (hA : Tendsto (fun i => ((p i).toOuterMeasure (A i)).toReal) l (𝓝 L))
    (hG : Tendsto (fun i => ((p i).toOuterMeasure (G i)).toReal) l (𝓝 1)) :
    Tendsto (fun i => ((p i).toOuterMeasure (A i ∩ G i)).toReal) l (𝓝 L) := by
  let : ∀ i, MeasurableSpace (Ω i) := fun _ => ⊤
  have heq : ∀ i (E : Set (Ω i)), (p i).toMeasure.real E =
      ((p i).toOuterMeasure E).toReal := by
    intro i E
    exact congrArg ENNReal.toReal
      (PMF.toMeasure_apply_eq_toOuterMeasure_apply (p i) (by trivial))
  have hA' : Tendsto (fun i => (p i).toMeasure.real (A i)) l (𝓝 L) := by
    simpa only [heq] using hA
  have hG' : Tendsto (fun i => (p i).toMeasure.real (G i)) l (𝓝 1) := by
    simpa only [heq] using hG
  simpa only [heq] using tendsto_probReal_inter_of_good
    (fun i => (p i).toMeasure) A G (fun _ => by trivial) hA' hG'

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateMultiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem offsetLaw_eq_uniform : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
  unfold offsetLaw
  congr 1
  exact Subsingleton.elim _ _

theorem sampledMultiplicity_some_point_tail (m : ℕ) :
    offsetEventProbability {M : MergedPairs F | ∃ p, m ≤ sampledMultiplicity M p} ≤
      (Fintype.card F : ℝ) ^ 2 *
        ((((2 * (Fintype.card F + 1)).choose m : ℕ) : ℝ) /
          (Fintype.card F : ℝ) ^ m) := by
  classical
  let e := Equiv.curry (Direction F) Bool F
  have he := uniform_toOuterMeasure_equiv e
    {M : MergedPairs F | ∃ p, m ≤ sampledMultiplicity M p}
  have h := uniform_exists_many_coordinate_matches_le
    (fun (p : Point F) (ds : Direction F × Bool) => lineEval ds.1 p) m
  unfold offsetEventProbability
  rw [offsetLaw_eq_uniform, ← he]
  simpa [e, Equiv.curry, Function.curry, sampledMultiplicity, OnLine, constituent,
    Point, eq_comm, Fintype.card_prod, Fintype.card_option, Nat.mul_comm,
    Nat.cast_mul, pow_two] using h

open Filter Topology

theorem tendsto_sampledMultiplicity_bad
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∃ p, Nat.ceil (Real.log (Fintype.card (F n) : ℝ)) < sampledMultiplicity M p})
      atTop (𝓝 0) := by
  have hbound := (BalancedRyser.tendsto_polynomial_mul_slot_choose_tail 2 1
    (by norm_num)).comp hq
  have hbound' : Tendsto (fun n => (Fintype.card (F n) : ℝ) ^ 2 *
      (((2 * (Fintype.card (F n) + 1)).choose
        (Nat.ceil (Real.log (Fintype.card (F n) : ℝ))) : ℝ) /
      (Fintype.card (F n) : ℝ) ^ Nat.ceil (Real.log (Fintype.card (F n) : ℝ))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow, mul_assoc] using hbound
  apply squeeze_zero (fun n => ENNReal.toReal_nonneg) _ hbound'
  intro n
  calc
    _ ≤ offsetEventProbability (F := F n)
        {M | ∃ p, Nat.ceil (Real.log (Fintype.card (F n) : ℝ)) ≤ sampledMultiplicity M p} := by
      apply pmf_outerReal_mono (offsetLaw (F n))
      intro M hM
      obtain ⟨p, hp⟩ := hM
      exact ⟨p, hp.le⟩
    _ ≤ _ := sampledMultiplicity_some_point_tail _

theorem tendsto_sampledMultiplicity_good
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card (F n) : ℝ))})
      atTop (𝓝 1) := by
  have heq (n : ℕ) : offsetEventProbability (F := F n)
      {M | ∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card (F n) : ℝ))} =
      1 - offsetEventProbability (F := F n)
        {M | ∃ p, Nat.ceil (Real.log (Fintype.card (F n) : ℝ)) < sampledMultiplicity M p} := by
    have hset : {M : MergedPairs (F n) | ∀ p, sampledMultiplicity M p ≤
        Nat.ceil (Real.log (Fintype.card (F n) : ℝ))} =
        {M : MergedPairs (F n) | ∃ p, Nat.ceil (Real.log (Fintype.card (F n) : ℝ)) <
          sampledMultiplicity M p}ᶜ := by
      ext M
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_lt]
    rw [hset, offsetEventProbability, pmf_outerReal_compl]
    rfl
  simpa only [heq, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_sampledMultiplicity_bad F hq)

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_DistinctPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology
open scoped Classical

namespace Balanced
open scoped _root_.Balanced

noncomputable section

theorem card_distinct_pairs (K : Type*) [Fintype K] :
    Fintype.card {p : K × K // p.1 ≠ p.2} =
      Fintype.card K * (Fintype.card K - 1) := by
  classical
  let e : {p : K × K // p.1 ≠ p.2} ≃ (Σ x : K, {y : K // y ≠ x}) :=
    { toFun := fun p => ⟨p.1.1, p.1.2, Ne.symm p.2⟩
      invFun := fun p => ⟨(p.1, p.2.1), Ne.symm p.2.2⟩
      left_inv := fun p => by cases p; rfl
      right_inv := fun p => by cases p; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp

theorem card_allConstituentPairsDistinct (D K : Type*) [Fintype D] [Fintype K] :
    Fintype.card {M : ConstituentOffsets D K // AllConstituentPairsDistinct M} =
      (Fintype.card K * (Fintype.card K - 1)) ^ Fintype.card D := by
  classical
  let e : {M : ConstituentOffsets D K // AllConstituentPairsDistinct M} ≃
      (D → {p : K × K // p.1 ≠ p.2}) :=
    { toFun := fun M d => ⟨M.1 d, M.2 d⟩
      invFun := fun M => ⟨fun d => (M d).1, fun d => (M d).2⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  calc
    _ = Fintype.card (D → {p : K × K // p.1 ≠ p.2}) := Fintype.card_congr e
    _ = _ := by
      rw [Fintype.card_fun]
      exact congrArg (fun n => n ^ Fintype.card D) (card_distinct_pairs K)

theorem finiteUniformProbability_eq_toOuterMeasure {Ω : Type*} [Fintype Ω]
    [Nonempty Ω] (E : Ω → Prop) :
    finiteUniformProbability E =
      ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E ω}).toReal := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [finiteUniformProbability, ENNReal.toReal_div, ENNReal.toReal_natCast,
    Fintype.card_eq_nat_card]
  rfl

theorem distinctConstituentProbability_eq (q : ℕ) (hq : 0 < q) :
    distinctConstituentProbability q = (1 - 1 / (q : ℝ)) ^ (q + 1) := by
  unfold distinctConstituentProbability finiteUniformProbability
  have hc := card_allConstituentPairsDistinct (Fin (q + 1)) (Fin q)
  rw [Fintype.card_eq_nat_card] at hc
  rw [hc]
  rw [Nat.card_eq_fintype_card]
  simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_mul]
  rw [← div_pow]
  congr 1
  rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  field_simp

theorem tendsto_distinctConstituentProbability :
    Tendsto distinctConstituentProbability atTop (𝓝 (Real.exp (-1))) := by
  have h₁ : Tendsto (fun q : ℕ => 1 - 1 / (q : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h₂ : Tendsto (fun q : ℕ => (1 - 1 / (q : ℝ)) ^ q)
      atTop (𝓝 (Real.exp (-1))) := by
    simpa only [neg_div, one_div, sub_eq_add_neg] using
      Real.tendsto_one_add_div_pow_exp (-1)
  have h := h₂.mul h₁
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  rw [distinctConstituentProbability_eq q (by omega), pow_succ]

end
end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateDistinctLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced
open scoped _root_.Balanced

open Filter Topology

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [DecidableEq F] in

theorem nat_card_distinctConstituents :
    Nat.card {M : MergedPairs F // DistinctConstituents M} =
      (Fintype.card F * (Fintype.card F - 1)) ^ (Fintype.card F + 1) := by
  classical
  let e := mergedPairsEquivConstituentOffsets (F := F)
  let eA : {M : MergedPairs F // DistinctConstituents M} ≃
      {M : ConstituentOffsets (Direction F) F // AllConstituentPairsDistinct M} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  have hc := card_allConstituentPairsDistinct (Direction F) F
  calc
    _ = Nat.card {M : ConstituentOffsets (Direction F) F //
      AllConstituentPairsDistinct M} := Nat.card_congr eA
    _ = _ := by
      simp only [Direction, Fintype.card_option] at hc
      simpa only [Fintype.card_eq_nat_card] using hc

theorem offsetProbability_distinctConstituents :
    offsetEventProbability {M : MergedPairs F | DistinctConstituents M} =
      (1 - 1 / (Fintype.card F : ℝ)) ^ (Fintype.card F + 1) := by
  classical
  unfold offsetEventProbability
  rw [offsetLaw_eq_uniform, ← finiteUniformProbability_eq_toOuterMeasure]
  unfold finiteUniformProbability
  rw [nat_card_distinctConstituents, Nat.card_eq_fintype_card]
  simp only [MergedPairs, Fintype.card_fun, Fintype.card_bool,
    Direction, Fintype.card_option, Nat.cast_pow, Nat.cast_mul]
  rw [← div_pow]
  congr 1
  rw [Nat.cast_sub (by exact Fintype.card_pos : 1 ≤ Fintype.card F), Nat.cast_one]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := F)
  field_simp

theorem offsetProbability_distinctConstituents_eq_order :
    offsetEventProbability {M : MergedPairs F | DistinctConstituents M} =
      distinctConstituentProbability (Fintype.card F) := by
  rw [offsetProbability_distinctConstituents,
    distinctConstituentProbability_eq _ Fintype.card_pos]

theorem tendsto_offsetProbability_distinctConstituents
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | DistinctConstituents M}) atTop (𝓝 (Real.exp (-1))) := by
  simpa only [offsetProbability_distinctConstituents_eq_order, Function.comp_def] using
    tendsto_distinctConstituentProbability.comp hq

theorem tendsto_candidateGood_and_distinct
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (c C : ℝ)
    (hgood : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c C}) atTop (𝓝 1)) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c C ∧ DistinctConstituents M})
      atTop (𝓝 (Real.exp (-1))) := by
  have hdistinct := tendsto_offsetProbability_distinctConstituents F hq
  have h := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun _ => {M | DistinctConstituents M})
    (fun _ => {M | CandidateGraphGood M c C}) hdistinct hgood
  simpa only [offsetEventProbability, ← Set.ofPred_and, and_comm] using h

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BoundedDriftCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

lemma condExp_exp_le_of_abs_le [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Y : Ω → ℝ} {a : ℝ}
    (ha : 0 < a) (hY : StronglyMeasurable[mΩ] Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ a) (hzero : μ[Y | m] =ᵐ[μ] 0) (θ : ℝ) :
    μ[fun ω ↦ exp (θ * Y ω) | m] ≤ᵐ[μ]
      fun _ ↦ exp (a ^ 2 * θ ^ 2 / 2) := by
  have hIcc : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (-a) a := by
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have hYi : Integrable Y μ := Integrable.of_mem_Icc (-a) a (hY.measurable.aemeasurable (μ := μ)) hIcc
  have hEi : Integrable (fun ω ↦ exp (θ * Y ω)) μ :=
    integrable_exp_mul_of_mem_Icc (hY.measurable.aemeasurable (μ := μ)) hIcc
  let b : ℝ := sinh (a * θ) / a
  have hlin : Integrable (fun ω ↦ cosh (a * θ) + b * Y ω) μ :=
    (integrable_const _).add (hYi.const_mul b)
  have hpoint : (fun ω ↦ exp (θ * Y ω)) ≤ᵐ[μ]
      fun ω ↦ cosh (a * θ) + b * Y ω := by
    filter_upwards [hb] with ω hω
    have hdiv : |Y ω / a| ≤ 1 := by
      rw [abs_div, abs_of_pos ha, div_le_one ha]
      exact hω
    have he := exp_mul_le_cosh_add_mul_sinh hdiv (a * θ)
    convert he using 1
    · congr 1
      field_simp
    · dsimp [b]
      ring
  have hmono := condExp_mono (m := m) hEi hlin hpoint
  have hlinear : μ[fun ω ↦ cosh (a * θ) + b * Y ω | m] =ᵐ[μ]
      fun _ ↦ cosh (a * θ) := by
    have hAdd := condExp_add (integrable_const (cosh (a * θ))) (hYi.const_mul b) m
    have hMul := condExp_smul (μ := μ) b Y m
    filter_upwards [hAdd, hMul, hzero] with ω hA hM hZ
    change μ[fun ω ↦ b * Y ω | m] ω = b * μ[Y | m] ω at hM
    change μ[Y | m] ω = 0 at hZ
    simp only [Pi.add_def] at hA
    simpa only [condExp_const hm, hM, hZ, mul_zero, add_zero] using hA
  filter_upwards [hmono, hlinear] with ω hM hL
  rw [hL] at hM
  exact hM.trans (by simpa only [mul_pow] using cosh_le_exp_half_sq (a * θ))

lemma subGaussian_add_of_bounded_difference [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X Y : Ω → ℝ} {c : ℝ≥0} {a : ℝ}
    (hX : HasSubgaussianMGF X c μ) (hXm : StronglyMeasurable[m] X)
    (ha : 0 < a) (hY : StronglyMeasurable[mΩ] Y)
    (hb : ∀ᵐ ω ∂μ, |Y ω| ≤ a) (hzero : μ[Y | m] =ᵐ[μ] 0) :
    HasSubgaussianMGF (X + Y) (c + NNReal.mk (a ^ 2) (sq_nonneg a)) μ := by
  have hEY (θ : ℝ) : Integrable (fun ω ↦ exp (θ * Y ω)) μ := by
    apply integrable_exp_mul_of_mem_Icc (hY.measurable.aemeasurable (μ := μ))
    filter_upwards [hb] with ω hω using abs_le.mp hω
  have hProd (θ : ℝ) : Integrable
      ((fun ω ↦ exp (θ * X ω)) * fun ω ↦ exp (θ * Y ω)) μ := by
    apply (hX.integrable_exp_mul θ).mul_bdd (hEY θ).aestronglyMeasurable
    filter_upwards [hb] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    calc
      θ * Y ω ≤ |θ * Y ω| := le_abs_self _
      _ = |θ| * |Y ω| := abs_mul _ _
      _ ≤ |θ| * a := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
  refine ⟨?_, ?_⟩
  · intro θ
    simpa only [Pi.add_apply, mul_add, exp_add, Pi.mul_def] using hProd θ
  · intro θ
    have hPull := condExp_mul_of_stronglyMeasurable_left
      (f := fun ω ↦ exp (θ * X ω)) (g := fun ω ↦ exp (θ * Y ω))
      (by exact continuous_exp.comp_stronglyMeasurable (hXm.const_mul θ))
      (hProd θ) (hEY θ)
    have hPullInt : Integrable
        ((fun ω ↦ exp (θ * X ω)) * μ[fun ω ↦ exp (θ * Y ω) | m]) μ :=
      integrable_condExp.congr hPull
    have hcond := condExp_exp_le_of_abs_le hm ha hY hb hzero θ
    calc
      mgf (X + Y) μ θ = ∫ ω, exp (θ * X ω) * exp (θ * Y ω) ∂μ := by
        simp only [mgf, Pi.add_apply, mul_add, exp_add]
      _ = ∫ ω, exp (θ * X ω) * μ[fun ω ↦ exp (θ * Y ω) | m] ω ∂μ := by
        change (∫ ω, ((fun ω ↦ exp (θ * X ω)) * fun ω ↦ exp (θ * Y ω)) ω ∂μ) = _
        rw [← integral_condExp hm]
        exact integral_congr_ae hPull
      _ ≤ ∫ ω, exp (θ * X ω) * exp (a ^ 2 * θ ^ 2 / 2) ∂μ := by
        apply integral_mono_ae hPullInt ((hX.integrable_exp_mul θ).mul_const _)
        filter_upwards [hcond] with ω hω
        exact mul_le_mul_of_nonneg_left hω (exp_nonneg _)
      _ = mgf X μ θ * exp (a ^ 2 * θ ^ 2 / 2) := by rw [integral_mul_const]; rfl
      _ ≤ exp ((c : ℝ) * θ ^ 2 / 2) * exp (a ^ 2 * θ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (hX.mgf_le θ) (exp_nonneg _)
      _ = exp (((c + NNReal.mk (a ^ 2) (sq_nonneg a) : ℝ≥0) : ℝ) * θ ^ 2 / 2) := by
        rw [← exp_add]
        congr 1
        change (c : ℝ) * θ ^ 2 / 2 + a ^ 2 * θ ^ 2 / 2 = ((c : ℝ) + a ^ 2) * θ ^ 2 / 2
        ring

lemma subGaussian_sum_of_bounded_differences [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {Y : ℕ → Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (n : ℕ)
    (hY : ∀ j < n, StronglyMeasurable[ℱ (j + 1)] (Y j))
    (hb : ∀ j < n, ∀ᵐ ω ∂μ, |Y j ω| ≤ a)
    (hzero : ∀ j < n, μ[Y j | ℱ j] =ᵐ[μ] 0) :
    HasSubgaussianMGF (fun ω ↦ ∑ j ∈ Finset.range n, Y j ω)
      ((n : ℝ≥0) * NNReal.mk (a ^ 2) (sq_nonneg a)) μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hprev := ih (fun j hj ↦ hY j (by omega))
      (fun j hj ↦ hb j (by omega)) (fun j hj ↦ hzero j (by omega))
    have hsum : StronglyMeasurable[ℱ n] (fun ω ↦ ∑ j ∈ Finset.range n, Y j ω) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      exact (hY j (by omega)).mono (ℱ.mono (by omega))
    have hnext := subGaussian_add_of_bounded_difference (ℱ.le n) hprev hsum ha
      ((hY n (by omega)).mono (ℱ.le (n + 1))) (hb n (by omega)) (hzero n (by omega))
    simpa only [Finset.sum_range_succ, Pi.add_def, Nat.cast_add, Nat.cast_one,
      add_mul, one_mul] using hnext

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_CenteredIncrements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsFiniteMeasure μ] {Y : Ω → ℝ} {L : ℝ}

theorem integrable_of_abs_le (hY : AEMeasurable Y μ)
    (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ L) : Integrable Y μ := by
  apply Integrable.of_mem_Icc (-L) L hY
  filter_upwards [hbound] with ω hω using abs_le.mp hω

omit [IsFiniteMeasure μ] in

theorem abs_sub_condExp_le (hbound : ∀ᵐ ω ∂μ, |Y ω| ≤ L) :
    ∀ᵐ ω ∂μ, |Y ω - μ[Y | m] ω| ≤ 2 * L := by
  have hc := ae_bdd_abs_condExp_of_ae_bdd_abs (m := m) hbound
  filter_upwards [hbound, hc] with ω hω hcω
  calc
    |Y ω - μ[Y | m] ω| ≤ |Y ω| + |μ[Y | m] ω| := abs_sub _ _
    _ ≤ L + L := add_le_add hω hcω
    _ = 2 * L := by ring

theorem condExp_sub_condExp_eq_zero (hm : m ≤ mΩ) (hYi : Integrable Y μ) :
    μ[fun ω ↦ Y ω - μ[Y | m] ω | m] =ᵐ[μ] 0 := by
  have hsub := condExp_sub hYi (integrable_condExp (f := Y) (m := m)) m
  have hfix : μ[μ[Y | m] | m] = μ[Y | m] :=
    condExp_of_stronglyMeasurable hm stronglyMeasurable_condExp integrable_condExp
  simpa only [Pi.sub_def, hfix, sub_self] using hsub

variable {X : ℕ → Ω → ℝ} {ℱ : Filtration ℕ mΩ}

omit [IsFiniteMeasure μ] in

theorem stronglyMeasurable_centered_increment_of_measurable (j : ℕ)
    (hj : StronglyMeasurable[ℱ j] (X j))
    (hj1 : StronglyMeasurable[ℱ (j + 1)] (X (j + 1))) :
    StronglyMeasurable[ℱ (j + 1)] (fun ω ↦ X (j + 1) ω - X j ω -
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω) := by
  exact (hj1.sub (hj.mono (ℱ.mono (Nat.le_succ j)))).sub
    (stronglyMeasurable_condExp.mono (ℱ.mono (Nat.le_succ j)))

theorem sum_centered_increments_eq (X : ℕ → Ω → ℝ) (ℱ : Filtration ℕ mΩ)
    (μ : Measure Ω) (t : ℕ) (ω : Ω) :
    (∑ j ∈ Finset.range t, (X (j + 1) ω - X j ω -
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω)) =
    X t ω - X 0 ω - ∑ j ∈ Finset.range t,
      μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω := by
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun j ↦ X j ω)]

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_SubGaussianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal NNReal

namespace Balanced
open scoped _root_.Balanced

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ} {c : ℝ≥0}

lemma subGaussian_abs_tail [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (2 * c)) := by
  have hset : {ω | u ≤ |X ω|} = {ω | u ≤ X ω} ∪ {ω | u ≤ -X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    rw [le_abs]
  rw [hset]
  calc
    μ.real ({ω | u ≤ X ω} ∪ {ω | u ≤ -X ω}) ≤
        μ.real {ω | u ≤ X ω} + μ.real {ω | u ≤ -X ω} := measureReal_union_le _ _
    _ ≤ exp (-u ^ 2 / (2 * c)) + exp (-u ^ 2 / (2 * c)) :=
      add_le_add (h.measure_ge_le hu) (h.neg.measure_ge_le hu)
    _ = _ := by ring

lemma subGaussian_mono_parameter (h : HasSubgaussianMGF X c μ)
    {d : ℝ≥0} (hcd : c ≤ d) : HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le θ := (h.mgf_le θ).trans (by
    apply exp_le_exp.mpr
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show (c : ℝ) ≤ d from hcd) (sq_nonneg θ))
      (by norm_num))

lemma subGaussian_abs_tail_of_parameter_le [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {v u : ℝ} (hv : 0 ≤ v)
    (hcv : (c : ℝ) ≤ v) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (2 * v)) := by
  exact subGaussian_abs_tail
    (subGaussian_mono_parameter h (d := ⟨v, hv⟩) hcv) hu

lemma subGaussian_abs_tail_horizon [IsProbabilityMeasure μ]
    (h : HasSubgaussianMGF X c μ) {t T : ℕ} (htT : t ≤ T)
    {L u : ℝ} (hct : (c : ℝ) ≤ 4 * t * L ^ 2) (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * exp (-u ^ 2 / (8 * T * L ^ 2)) := by
  have hv : 0 ≤ 4 * (T : ℝ) * L ^ 2 := by positivity
  have hcv : (c : ℝ) ≤ 4 * (T : ℝ) * L ^ 2 := hct.trans (by
    gcongr)
  have hb := subGaussian_abs_tail_of_parameter_le h hv hcv hu
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  ring

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_BoundedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

namespace Balanced
open scoped _root_.Balanced

universe u

theorem boundedDriftConcentration_proof : BoundedDriftConcentration.{u} := by
  intro Ω mΩ μ hμ ℱ X T L hT hL hX hbound u hu t ht
  let Y : ℕ → Ω → ℝ := fun j ω ↦ X (j + 1) ω - X j ω -
    μ[fun ω ↦ X (j + 1) ω - X j ω | ℱ j] ω
  have hmeas (j : ℕ) (hj : j < t) : StronglyMeasurable[ℱ (j + 1)] (Y j) := by
    exact stronglyMeasurable_centered_increment_of_measurable j
      (hX j (by omega)) (hX (j + 1) (by omega))
  have hb (j : ℕ) (hj : j < t) : ∀ᵐ ω ∂μ, |Y j ω| ≤ 2 * L :=
    abs_sub_condExp_le (hbound j (by omega))
  have hz (j : ℕ) (hj : j < t) : μ[Y j | ℱ j] =ᵐ[μ] 0 := by
    apply condExp_sub_condExp_eq_zero (ℱ.le j)
    apply integrable_of_abs_le
      ((((hX (j + 1) (by omega)).mono (ℱ.le (j + 1))).sub
        ((hX j (by omega)).mono (ℱ.le j))).measurable.aemeasurable)
      (hbound j (by omega))
  have hmgf := subGaussian_sum_of_bounded_differences
    (μ := μ) (ℱ := ℱ) (Y := Y) (by positivity : 0 < 2 * L) t hmeas hb hz
  have hp : (((t : ℝ≥0) * ⟨(2 * L) ^ 2, sq_nonneg (2 * L)⟩ : ℝ≥0) : ℝ)
      ≤ 4 * (t : ℝ) * L ^ 2 := by
    change (t : ℝ) * (2 * L) ^ 2 ≤ 4 * (t : ℝ) * L ^ 2
    nlinarith
  have htail := subGaussian_abs_tail_horizon hmgf ht hp hu.le
  simpa only [Y, sum_centered_increments_eq] using htail

end Balanced

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentDoobGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {A : Fin T → Type*} [∀ j, MeasurableSpace (A j)]
  {ξ : ∀ j, Ω → A j}

theorem prefixFiltration_eq_iSup_past (hξ : ∀ j, Measurable (ξ j)) (n : ℕ) :
    prefixFiltration ξ hξ n =
      ⨆ j : {j : Fin T // j.val < n},
        (inferInstance : MeasurableSpace (A j)).comap (ξ j) := by
  classical
  change ((MeasurableSpace.pi.comap (prefixIndices T n).restrict).comap
    (trialVector ξ)) = _
  rw [MeasurableSpace.comap_comp]
  change (inferInstance : MeasurableSpace (∀ j : prefixIndices T n, A j)).comap
    (fun ω (j : prefixIndices T n) => ξ j ω) = _
  rw [MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · refine iSup_le fun j => ?_
    exact le_iSup_of_le ⟨j, by simpa only [prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and] using j.property⟩ le_rfl
  · refine iSup_le fun j => ?_
    exact le_iSup_of_le ⟨j, by simpa only [prefixIndices, Finset.mem_filter, Finset.mem_univ, true_and] using j.property⟩ le_rfl

theorem comap_past_eq_prefixFiltration (hξ : ∀ j, Measurable (ξ j)) (i : Fin T) :
    (inferInstance : MeasurableSpace (∀ j : {j : Fin T // j.val < i.val}, A j)).comap
      (fun ω (j : {j : Fin T // j.val < i.val}) => ξ j ω) =
        prefixFiltration ξ hξ i.val := by
  rw [MeasurableSpace.comap_process_pi, prefixFiltration_eq_iSup_past]

theorem comap_past_current_eq_prefixFiltration
    (hξ : ∀ j, Measurable (ξ j)) (i : Fin T) :
    (inferInstance : MeasurableSpace
      ((∀ j : {j : Fin T // j.val < i.val}, A j) × A i)).comap
      (fun ω => ((fun j : {j : Fin T // j.val < i.val} => ξ j ω), ξ i ω)) =
        prefixFiltration ξ hξ (i.val + 1) := by
  change (MeasurableSpace.prod MeasurableSpace.pi inferInstance).comap _ = _
  rw [MeasurableSpace.comap_prodMk, MeasurableSpace.comap_process_pi,
    prefixFiltration_eq_iSup_past]
  apply le_antisymm
  · apply sup_le
    · refine iSup_le fun j => ?_
      exact le_iSup_of_le ⟨j, Nat.lt_succ_of_lt j.property⟩ le_rfl
    · exact le_iSup_of_le ⟨i, Nat.lt_succ_self i.val⟩ le_rfl
  · refine iSup_le fun j => ?_
    by_cases hji : (j : Fin T) = i
    · rw [hji]
      exact le_sup_right
    · have hlt : (j : Fin T).val < i.val := by
        have hne : (j : Fin T).val ≠ i.val := fun h => hji (Fin.ext h)
        have hj := j.property
        omega
      exact le_sup_of_le_left (le_iSup_of_le ⟨j, hlt⟩ le_rfl)

end Balanced.IndependentTrials

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrialKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → α} {Y : Ω → β} {f : α × β → ℝ}

theorem condExp_independent_pair
    (hX : Measurable X) (hY : Measurable Y)
    (hind : IndepFun X Y μ) (hf : StronglyMeasurable f)
    (hfi : Integrable (fun ω => f (X ω, Y ω)) μ) :
    μ[fun ω => f (X ω, Y ω) | (inferInstance : MeasurableSpace α).comap X]
      =ᵐ[μ] fun ω => ∫ y, f (X ω, y) ∂(μ.map Y) := by
  have hmap := hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have hfmap : Integrable f (μ.map fun ω => (X ω, Y ω)) :=
    (integrable_map_measure hf.aestronglyMeasurable
      (hX.aemeasurable.prodMk hY.aemeasurable)).mpr hfi
  have hfprod : Integrable f ((μ.map X).prod (μ.map Y)) := hmap ▸ hfmap
  have hg : StronglyMeasurable (fun x => ∫ y, f (x, y) ∂(μ.map Y)) :=
    hf.integral_prod_right'
  have hgi : Integrable (fun ω => ∫ y, f (X ω, y) ∂(μ.map Y)) μ :=
    (integrable_map_measure hg.aestronglyMeasurable hX.aemeasurable).mp
      hfprod.integral_prod_left
  refine (ae_eq_condExp_of_forall_setIntegral_eq hX.comap_le hfi
    (fun s _ _ => hgi.integrableOn) ?_
    (hg.comp_measurable (comap_measurable X)).aestronglyMeasurable).symm
  rintro s ⟨t, ht, rfl⟩ _
  rw [← setIntegral_map ht hg.aestronglyMeasurable hX.aemeasurable]
  have hp := setIntegral_prod f (s := t) (t := Set.univ) hfprod.integrableOn
  simp only [Measure.restrict_univ] at hp
  rw [← hp, ← hmap]
  rw [setIntegral_map (ht.prod MeasurableSet.univ) hf.aestronglyMeasurable
    (hX.aemeasurable.prodMk hY.aemeasurable)]
  simp only [Set.mk_preimage_prod, Set.preimage_univ, Set.inter_univ]

section FiniteBlocks

variable {ι : Type*} {A : ι → Type*} [∀ i, MeasurableSpace (A i)]
  {ξ : ∀ i, Ω → A i}

omit [IsProbabilityMeasure μ] in

theorem independent_predicate_blocks [Fintype ι]
    (p : ι → Prop) [DecidablePred p]
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    IndepFun (fun ω (i : {i // p i}) => ξ i ω)
      (fun ω (i : {i // ¬p i}) => ξ i ω) μ := by
  classical
  have hdisj : Disjoint (Finset.univ.filter p) (Finset.univ.filter (fun i => ¬p i)) := by
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun _ h hp => hp h
  have hbase := hind.indepFun_finset (Finset.univ.filter p)
    (Finset.univ.filter (fun i => ¬p i)) hdisj hξ
  let left : (∀ i : Finset.univ.filter p, A i) → ∀ i : {i // p i}, A i :=
    fun x i => x ⟨i, by simp [i.property]⟩
  let right : (∀ i : Finset.univ.filter (fun i => ¬p i), A i) →
      ∀ i : {i // ¬p i}, A i :=
    fun x i => x ⟨i, by simp [i.property]⟩
  exact hbase.comp
    (Measurable.of_eval (f := left) (fun _ => measurable_pi_apply _))
    (Measurable.of_eval (f := right) (fun _ => measurable_pi_apply _))

end FiniteBlocks

end Balanced.IndependentTrials

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrialGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {A : Fin T → Type*} [∀ i, MeasurableSpace (A i)]
  {μ : Measure Ω} {ξ : (i : Fin T) → Ω → A i}

theorem past_independent_current
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (i : Fin T) :
    IndepFun (fun ω (j : {j : Fin T // j.val < i.val}) ↦ ξ j ω) (ξ i) μ := by
  have h := independent_predicate_blocks (fun j : Fin T ↦ j.val < i.val) hξ hind
  exact h.comp measurable_id (measurable_pi_apply ⟨i, lt_irrefl i.val⟩)

theorem pastCurrent_independent_future
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (i : Fin T) :
    IndepFun
      (fun ω ↦ ((fun j : {j : Fin T // j.val < i.val} ↦ ξ j ω), ξ i ω))
      (fun ω (j : {j : Fin T // i.val < j.val}) ↦ ξ j ω) μ := by
  have h := independent_predicate_blocks (fun j : Fin T ↦ j.val ≤ i.val) hξ hind
  let left : ((j : {j : Fin T // j.val ≤ i.val}) → A j) →
      (((j : {j : Fin T // j.val < i.val}) → A j) × A i) :=
    fun x ↦ ((fun j ↦ x ⟨j.val, le_of_lt j.property⟩), x ⟨i, le_rfl⟩)
  let right : ((j : {j : Fin T // ¬j.val ≤ i.val}) → A j) →
      ((j : {j : Fin T // i.val < j.val}) → A j) :=
    fun x j ↦ x ⟨j.val, not_le_of_gt j.property⟩
  have hl : Measurable left :=
    (Measurable.of_eval (fun index ↦ measurable_pi_apply
      (⟨index.val, le_of_lt index.property⟩ : {j : Fin T // j.val ≤ i.val}))).prodMk
        (measurable_pi_apply (⟨i, le_rfl⟩ : {j : Fin T // j.val ≤ i.val}))
  have hr : Measurable right :=
    Measurable.of_eval (fun index ↦ measurable_pi_apply
      (⟨index.val, not_le_of_gt index.property⟩ : {j : Fin T // ¬j.val ≤ i.val}))
  exact h.comp hl hr

end Balanced.IndependentTrials

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrials3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

theorem abs_integral_sub_integral_le [IsProbabilityMeasure μ]
    {f g : Ω → ℝ} {c : ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ ω ∂μ, |f ω - g ω| ≤ c) :
    |(∫ ω, f ω ∂μ) - ∫ ω, g ω ∂μ| ≤ c := by
  rw [← integral_sub hf hg]
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω ↦ f ω - g ω)
      (C := c) (by simpa only [Real.norm_eq_abs] using hfg))

theorem abs_sub_integral_le_of_oscillation [IsProbabilityMeasure μ]
    {f : Ω → ℝ} {c : ℝ} (hf : Integrable f μ) (x : Ω)
    (hosc : ∀ᵐ y ∂μ, |f x - f y| ≤ c) :
    |f x - ∫ y, f y ∂μ| ≤ c := by
  simpa only [integral_const, probReal_univ, one_smul] using
    (abs_integral_sub_integral_le (integrable_const (f x)) hf hosc)

theorem conditional_second_moment_le {m : MeasurableSpace Ω}
    {Z : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hZ : ∀ᵐ ω ∂μ, |Z ω| ≤ c) :
    ∀ᵐ ω ∂μ, μ[(fun x ↦ (Z x) ^ 2) | m] ω ≤ c ^ 2 := by
  apply condExp_le_nonneg_const (sq_nonneg c)
  filter_upwards [hZ] with ω hω
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (Z ω)) hc).2 hω

theorem conditional_variance_eq_second_moment {m : MeasurableSpace Ω}
    {Z : Ω → ℝ} (hzero : μ[Z | m] =ᵐ[μ] 0) :
    ProbabilityTheory.condVar m Z μ =ᵐ[μ] μ[(fun x ↦ (Z x) ^ 2) | m] := by
  apply condExp_congr_ae
  filter_upwards [hzero] with ω hω
  simp only [Pi.pow_apply, Pi.sub_apply, Pi.zero_apply] at hω ⊢
  rw [hω, sub_zero]

theorem conditional_variance_le_of_centered_bound {m : MeasurableSpace Ω}
    {Z : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hzero : μ[Z | m] =ᵐ[μ] 0) (hZ : ∀ᵐ ω ∂μ, |Z ω| ≤ c) :
    ∀ᵐ ω ∂μ, ProbabilityTheory.condVar m Z μ ω ≤ c ^ 2 := by
  filter_upwards [conditional_variance_eq_second_moment hzero,
    conditional_second_moment_le (m := m) hc hZ] with ω heq hle
  exact heq.trans_le hle

theorem martingale_increment_condExp_zero [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} {D : ℕ → Ω → ℝ}
    (hD : Martingale D ℱ μ) (n : ℕ) :
    μ[(fun ω ↦ D (n + 1) ω - D n ω) | ℱ n] =ᵐ[μ] 0 := by
  filter_upwards [condExp_sub (hD.integrable (n + 1)) (hD.integrable n) (ℱ n),
    hD.condExp_ae_eq (Nat.le_succ n)] with ω hsub hnext
  change μ[D (n + 1) - D n | ℱ n] ω = 0
  rw [hsub]
  change μ[D (n + 1) | ℱ n] ω - μ[D n | ℱ n] ω = 0
  rw [hnext, condExp_of_stronglyMeasurable (ℱ.le n)
    (hD.stronglyMeasurable n) (hD.integrable n), sub_self]

theorem martingale_increment_condVar_le [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m₀} {D : ℕ → Ω → ℝ}
    (hD : Martingale D ℱ μ) (n : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᵐ ω ∂μ, |D (n + 1) ω - D n ω| ≤ c) :
    ∀ᵐ ω ∂μ, ProbabilityTheory.condVar (ℱ n)
      (fun x ↦ D (n + 1) x - D n x) μ ω ≤ c ^ 2 := by
  exact conditional_variance_le_of_centered_bound hc
    (martingale_increment_condExp_zero hD n) hbound

section RevealEndpoints

variable {T : ℕ} {A : Fin T → Type*} [∀ i, MeasurableSpace (A i)]
  (ξ : (i : Fin T) → Ω → A i) (hξ : ∀ i, Measurable (ξ i))

theorem piFinset_univ : Filtration.piFinset (X := A) Finset.univ =
    (inferInstance : MeasurableSpace ((i : Fin T) → A i)) := by
  apply le_antisymm (Filtration.piFinset.le _)
  have hid : @Measurable ((i : Fin T) → A i) ((i : Fin T) → A i)
      (Filtration.piFinset (X := A) Finset.univ) inferInstance id := by
    refine @Measurable.of_eval _ _ A
      (Filtration.piFinset (X := A) Finset.univ) _ id ?_
    intro i
    exact (measurable_pi_apply (⟨i, Finset.mem_univ i⟩ : (Finset.univ : Finset (Fin T)))).comp
      (comap_measurable (Finset.restrict (Finset.univ : Finset (Fin T))))
  simpa only [MeasurableSpace.comap_id] using hid.comap_le

@[simp] theorem prefixFiltration_full : prefixFiltration ξ hξ T =
    MeasurableSpace.comap (trialVector ξ) inferInstance := by
  change (Filtration.piFinset (X := A) (prefixIndices T T)).comap (trialVector ξ) = _
  rw [prefixIndices_full, piFinset_univ]

theorem measurable_outcome_full {F : ((i : Fin T) → A i) → ℝ}
    (hF : Measurable F) :
    Measurable[prefixFiltration ξ hξ T] (fun ω ↦ F (trialVector ξ ω)) := by
  rw [prefixFiltration_full]
  exact hF.comp (comap_measurable (trialVector ξ))

theorem doobProcess_full [IsProbabilityMeasure μ]
    {F : ((i : Fin T) → A i) → ℝ} (hF : Measurable F)
    (hY : Integrable (fun ω ↦ F (trialVector ξ ω)) μ) :
    doobProcess ξ hξ (fun ω ↦ F (trialVector ξ ω)) μ T =
      fun ω ↦ F (trialVector ξ ω) := by
  exact condExp_of_stronglyMeasurable ((prefixFiltration ξ hξ).le T)
    (measurable_outcome_full ξ hξ hF).stronglyMeasurable hY

theorem doobProcess_zero [IsProbabilityMeasure μ] (Y : Ω → ℝ) :
    doobProcess ξ hξ Y μ 0 = fun _ ↦ ∫ ω, Y ω ∂μ := by
  rw [doobProcess, prefixFiltration_zero, condExp_bot]

omit [∀ i, MeasurableSpace (A i)] in
theorem CoordinateOscillation.abs_sub_le_sum
    {F : ((i : Fin T) → A i) → ℝ} {c : Fin T → ℝ}
    (hF : CoordinateOscillation F c) (x y : (i : Fin T) → A i) :
    |F x - F y| ≤ ∑ i, c i := by
  classical
  let mix (s : Finset (Fin T)) : (i : Fin T) → A i :=
    fun i ↦ if i ∈ s then y i else x i
  have hmix (s : Finset (Fin T)) : |F (mix s) - F x| ≤ ∑ i ∈ s, c i := by
    induction s using Finset.induction_on with
    | empty => simp [mix]
    | @insert a s ha ih =>
      have hstep : |F (mix (insert a s)) - F (mix s)| ≤ c a := by
        apply hF a
        intro j hja
        simp [mix, hja]
      calc
        |F (mix (insert a s)) - F x| ≤
            |F (mix (insert a s)) - F (mix s)| + |F (mix s) - F x| :=
          abs_sub_le _ _ _
        _ ≤ c a + ∑ i ∈ s, c i := add_le_add hstep ih
        _ = ∑ i ∈ insert a s, c i := (Finset.sum_insert ha).symm
  have h := hmix Finset.univ
  simpa [mix, abs_sub_comm] using h

omit [∀ i, MeasurableSpace (A i)] in
theorem CoordinateOscillation.abs_le
    {F : ((i : Fin T) → A i) → ℝ} {c : Fin T → ℝ}
    (hF : CoordinateOscillation F c) (x₀ x : (i : Fin T) → A i) :
    |F x| ≤ |F x₀| + ∑ i, c i := by
  calc
    |F x| = |F x - F x₀ + F x₀| := by rw [sub_add_cancel]
    _ ≤ |F x - F x₀| + |F x₀| := abs_add_le _ _
    _ ≤ (∑ i, c i) + |F x₀| := add_le_add (hF.abs_sub_le_sum x x₀) le_rfl
    _ = |F x₀| + ∑ i, c i := add_comm _ _

theorem CoordinateOscillation.integrable_comp [IsFiniteMeasure μ]
    {F : ((i : Fin T) → A i) → ℝ} {c : Fin T → ℝ}
    (hF : CoordinateOscillation F c) (hFm : Measurable F)
    (x₀ : (i : Fin T) → A i) {g : Ω → (i : Fin T) → A i}
    (hg : Measurable g) : Integrable (fun ω ↦ F (g ω)) μ := by
  apply Integrable.of_bound (hFm.comp hg).aestronglyMeasurable (|F x₀| + ∑ i, c i)
  filter_upwards with ω
  simpa only [Real.norm_eq_abs, Function.comp_apply] using hF.abs_le x₀ (g ω)

end RevealEndpoints

end Balanced.IndependentTrials

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrialIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {Ω α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → α} {Z : Ω → β} {V : Ω → γ}
  {f : (α × β) × γ → ℝ} {c : ℝ}

theorem independent_three_block_increment_bound
    (hX : Measurable X) (hZ : Measurable Z) (hV : Measurable V)
    (hindCurrent : IndepFun X Z μ)
    (hindFuture : IndepFun (fun ω => (X ω, Z ω)) V μ)
    (hf : StronglyMeasurable f)
    (hfi : Integrable (fun ω => f ((X ω, Z ω), V ω)) μ)
    (hfslice : ∀ x z, Integrable (fun v => f ((x, z), v)) (μ.map V))
    (hHslice : ∀ x, Integrable (fun z => ∫ v, f ((x, z), v) ∂(μ.map V)) (μ.map Z))
    (hosc : ∀ x z z', ∀ᵐ v ∂(μ.map V), |f ((x, z), v) - f ((x, z'), v)| ≤ c) :
    ∀ᵐ ω ∂μ,
      |μ[fun ω => f ((X ω, Z ω), V ω) |
          (inferInstance : MeasurableSpace (α × β)).comap (fun ω => (X ω, Z ω))] ω -
        μ[fun ω => f ((X ω, Z ω), V ω) |
          (inferInstance : MeasurableSpace α).comap X] ω| ≤ c := by
  have hrep₁ := condExp_independent_pair (hX.prodMk hZ) hV hindFuture hf hfi
  have hH : StronglyMeasurable (fun xz : α × β => ∫ v, f (xz, v) ∂(μ.map V)) :=
    hf.integral_prod_right'
  have hHint : Integrable (fun ω => ∫ v, f ((X ω, Z ω), v) ∂(μ.map V)) μ :=
    integrable_condExp.congr hrep₁
  have hrep₂ := condExp_independent_pair hX hZ hindCurrent hH hHint
  have hsmall :
      (inferInstance : MeasurableSpace α).comap X ≤
        (inferInstance : MeasurableSpace (α × β)).comap (fun ω => (X ω, Z ω)) :=
    MeasurableSpace.comap_le_comap_of_eq_comp Prod.fst measurable_fst rfl
  have htower := condExp_condExp_of_le (μ := μ) (f := fun ω => f ((X ω, Z ω), V ω))
    hsmall (hX.prodMk hZ).comap_le
  have hrep₀ := htower.symm.trans ((condExp_congr_ae hrep₁).trans hrep₂)
  filter_upwards [hrep₁, hrep₀] with ω h₁ h₀
  rw [h₁, h₀]
  haveI : IsProbabilityMeasure (μ.map Z) := Measure.isProbabilityMeasure_map hZ.aemeasurable
  haveI : IsProbabilityMeasure (μ.map V) := Measure.isProbabilityMeasure_map hV.aemeasurable
  apply abs_sub_integral_le_of_oscillation (hHslice (X ω)) (Z ω)
  exact Eventually.of_forall fun z =>
    abs_integral_sub_integral_le (hfslice (X ω) (Z ω)) (hfslice (X ω) z)
      (hosc (X ω) (Z ω) z)

end Balanced.IndependentTrials

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrialReassembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {A : Fin T → Type*}

theorem reassembleAt_restrict (i : Fin T) (w : ∀ j, A j) :
    reassembleAt i (fun j => w j) (w i) (fun j => w j) = w := by
  funext j
  by_cases h : j.val < i.val
  · simp [reassembleAt, h]
  · by_cases e : j = i
    · subst j
      simp [reassembleAt]
    · simp [reassembleAt, h, e]

theorem reassembleAt_eq_of_ne (i : Fin T)
    (x : ∀ j : {j : Fin T // j.val < i.val}, A j)
    (z z' : A i) (v : ∀ j : {j : Fin T // i.val < j.val}, A j)
    (j : Fin T) (hji : j ≠ i) :
    reassembleAt i x z v j = reassembleAt i x z' v j := by
  unfold reassembleAt
  split_ifs <;> rfl

variable [∀ j, MeasurableSpace (A j)]

theorem measurable_reassembleAt (i : Fin T) :
    Measurable (fun p : ((∀ j : {j : Fin T // j.val < i.val}, A j) × A i) ×
        (∀ j : {j : Fin T // i.val < j.val}, A j) =>
      reassembleAt i p.1.1 p.1.2 p.2) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j.val < i.val
  · simpa only [reassembleAt, dite_eq_left h, Function.comp_def] using
      (measurable_pi_apply (⟨j, h⟩ : {j : Fin T // j.val < i.val})).comp (measurable_fst.comp measurable_fst)
  · by_cases e : j = i
    · subst j
      simpa [reassembleAt, Function.comp_def] using
        (measurable_snd.comp measurable_fst)
    · simpa only [reassembleAt, dite_eq_right h, dite_eq_right e, Function.comp_def] using
        (measurable_pi_apply (⟨j, by omega⟩ : {j : Fin T // i.val < j.val})).comp measurable_snd

end Balanced.IndependentTrials

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrialStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials

variable {T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {A : Fin T → Type*} [∀ j, MeasurableSpace (A j)]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : ∀ j, Ω → A j}

theorem doob_increment_bound_of_grouping
    (hξ : ∀ j, Measurable (ξ j))
    (F : (∀ j, A j) → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun ω => F (trialVector ξ ω)) μ)
    (c : Fin T → ℝ) (hosc : CoordinateOscillation F c) (i : Fin T)
    (hindCurrent : IndepFun (fun ω (j : {j : Fin T // j.val < i.val}) => ξ j ω) (ξ i) μ)
    (hindFuture : IndepFun
      (fun ω => ((fun j : {j : Fin T // j.val < i.val} => ξ j ω), ξ i ω))
      (fun ω (j : {j : Fin T // i.val < j.val}) => ξ j ω) μ)
    (hPast : (inferInstance : MeasurableSpace (∀ j : {j : Fin T // j.val < i.val}, A j)).comap
      (fun ω (j : {j : Fin T // j.val < i.val}) => ξ j ω) = prefixFiltration ξ hξ i.val)
    (hNext : (inferInstance : MeasurableSpace
      ((∀ j : {j : Fin T // j.val < i.val}, A j) × A i)).comap
      (fun ω => ((fun j : {j : Fin T // j.val < i.val} => ξ j ω), ξ i ω)) =
        prefixFiltration ξ hξ (i.val + 1)) :
    ∀ᵐ ω ∂μ,
      |doobProcess ξ hξ (fun ω => F (trialVector ξ ω)) μ (i.val + 1) ω -
        doobProcess ξ hξ (fun ω => F (trialVector ξ ω)) μ i.val ω| ≤ c i := by
  classical
  let P := fun ω (j : {j : Fin T // j.val < i.val}) => ξ j ω
  let Q := fun ω (j : {j : Fin T // i.val < j.val}) => ξ j ω
  have hP : Measurable P := Measurable.of_eval (fun index => hξ index)
  have hQ : Measurable Q := Measurable.of_eval (fun index => hξ index)
  obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
  let x₀ := trialVector ξ ω₀
  let f := fun p : ((∀ j : {j : Fin T // j.val < i.val}, A j) × A i) ×
      (∀ j : {j : Fin T // i.val < j.val}, A j) => F (reassembleAt i p.1.1 p.1.2 p.2)
  have hf : StronglyMeasurable f := (hF.comp (measurable_reassembleAt i)).stronglyMeasurable
  have hreconstruct (ω : Ω) : reassembleAt i (P ω) (ξ i ω) (Q ω) = trialVector ξ ω :=
    reassembleAt_restrict i (trialVector ξ ω)
  have hfi : Integrable (fun ω => f ((P ω, ξ i ω), Q ω)) μ := by
    simpa only [f, hreconstruct] using hFi
  have hfslice (x : ∀ j : {j : Fin T // j.val < i.val}, A j) (z : A i) :
      Integrable (fun v => f ((x, z), v)) (μ.map Q) := by
    exact hosc.integrable_comp hF x₀
      ((measurable_reassembleAt i).comp (measurable_const.prodMk measurable_id))
  have hHslice (x : ∀ j : {j : Fin T // j.val < i.val}, A j) :
      Integrable (fun z => ∫ v, f ((x, z), v) ∂(μ.map Q)) (μ.map (ξ i)) := by
    have hpair : Integrable (fun p : A i × (∀ j : {j : Fin T // i.val < j.val}, A j) =>
        f ((x, p.1), p.2)) ((μ.map (ξ i)).prod (μ.map Q)) :=
      hosc.integrable_comp hF x₀ ((measurable_reassembleAt i).comp
        ((measurable_const.prodMk measurable_fst).prodMk measurable_snd))
    exact hpair.integral_prod_left
  have hosc' (x : ∀ j : {j : Fin T // j.val < i.val}, A j) (z z' : A i) :
      ∀ᵐ v ∂(μ.map Q), |f ((x, z), v) - f ((x, z'), v)| ≤ c i := by
    filter_upwards with v
    exact hosc i _ _ (fun j hji => reassembleAt_eq_of_ne i x z z' v j hji)
  have hbound := independent_three_block_increment_bound hP (hξ i) hQ
    hindCurrent hindFuture hf hfi hfslice hHslice hosc'
  simpa only [f, hreconstruct, P, Q, hPast, hNext, doobProcess] using hbound

end Balanced.IndependentTrials

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_IndependentTrials2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory ProbabilityTheory

namespace Balanced.IndependentTrials
open scoped _root_.Balanced

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ} {D : ℕ → Ω → ℝ}

theorem martingale_abs_tail (hD : Martingale D ℱ μ)
    {T : ℕ} {L u : ℝ} (hT : 1 ≤ T) (hL : 0 < L) (hu : 0 < u)
    (hbound : ∀ j < T, ∀ᵐ ω ∂μ, |D (j + 1) ω - D j ω| ≤ L) :
    μ.real {ω | u ≤ |D T ω - D 0 ω|} ≤
      2 * Real.exp (-(u ^ 2) / (8 * (T : ℝ) * L ^ 2)) := by
  have htail := boundedDriftConcentration_proof μ ℱ D T L hT hL
    (fun j _ ↦ hD.stronglyMeasurable j) hbound u hu T le_rfl
  have hset : {ω | u ≤ |D T ω - D 0 ω|} =ᵐ[μ]
      {ω | u ≤ |D T ω - D 0 ω - ∑ j ∈ Finset.range T,
        μ[fun x ↦ D (j + 1) x - D j x | ℱ j] ω|} := by
    filter_upwards [ae_all_iff.2 (fun j ↦ martingale_increment_condExp_zero hD j)] with ω hω
    have hsum : (∑ j ∈ Finset.range T,
        μ[fun x ↦ D (j + 1) x - D j x | ℱ j] ω) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      exact hω j
    change (u ≤ |D T ω - D 0 ω|) =
      (u ≤ |D T ω - D 0 ω - ∑ j ∈ Finset.range T,
        μ[fun x ↦ D (j + 1) x - D j x | ℱ j] ω|)
    rw [hsum, sub_zero]
  rw [measureReal_congr hset]
  exact htail

theorem doob_abs_tail_of_increment_bound
    {T : ℕ} {A : Fin T → Type*} [∀ i, MeasurableSpace (A i)]
    (ξ : (i : Fin T) → Ω → A i) (hξ : ∀ i, Measurable (ξ i))
    {F : ((i : Fin T) → A i) → ℝ} (hF : Measurable F)
    (hY : Integrable (fun ω ↦ F (trialVector ξ ω)) μ)
    {c : Fin T → ℝ}
    (hbound : ∀ i : Fin T, ∀ᵐ ω ∂μ,
      |doobProcess ξ hξ (fun x ↦ F (trialVector ξ x)) μ (i.val + 1) ω -
        doobProcess ξ hξ (fun x ↦ F (trialVector ξ x)) μ i.val ω| ≤ c i)
    {L u : ℝ} (hT : 1 ≤ T) (hL : 0 < L) (hcL : ∀ i, c i ≤ L) (hu : 0 < u) :
    μ.real {ω | u ≤ |F (trialVector ξ ω) - ∫ x, F (trialVector ξ x) ∂μ|} ≤
      2 * Real.exp (-(u ^ 2) / (8 * (T : ℝ) * L ^ 2)) := by
  let Y : Ω → ℝ := fun ω ↦ F (trialVector ξ ω)
  have hD : Martingale (doobProcess ξ hξ Y μ) (prefixFiltration ξ hξ) μ :=
    martingale_condExp Y (prefixFiltration ξ hξ) μ
  have hb : ∀ j < T, ∀ᵐ ω ∂μ,
      |doobProcess ξ hξ Y μ (j + 1) ω - doobProcess ξ hξ Y μ j ω| ≤ L := by
    intro j hj
    filter_upwards [hbound ⟨j, hj⟩] with ω hω
    exact hω.trans (hcL ⟨j, hj⟩)
  have ht := martingale_abs_tail hD hT hL hu hb
  simpa only [Y, doobProcess_full ξ hξ hF hY, doobProcess_zero] using ht

end Balanced.IndependentTrials

namespace Balanced
open scoped _root_.Balanced

open IndependentTrials

universe u v

theorem independentTrialJumps_proof : IndependentTrialJumps.{u, v} := by
  intro T Ω mΩ μ hμ A mA ξ hξ F hF hind hY c hc hosc
  let Y : Ω → ℝ := fun ω ↦ F (trialVector ξ ω)
  let D := doobProcess ξ hξ Y μ
  have hD : Martingale D (prefixFiltration ξ hξ) μ :=
    martingale_condExp Y (prefixFiltration ξ hξ) μ
  have hbound (i : Fin T) :
      ∀ᵐ ω ∂μ, |D (i.val + 1) ω - D i.val ω| ≤ c i := by
    exact doob_increment_bound_of_grouping hξ F hF hY c hosc i
      (past_independent_current hξ hind i)
      (pastCurrent_independent_future hξ hind i)
      (comap_past_eq_prefixFiltration hξ i)
      (comap_past_current_eq_prefixFiltration hξ i)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact Filter.EventuallyEq.of_eq (doobProcess_zero ξ hξ Y)
  · exact Filter.EventuallyEq.of_eq (doobProcess_full ξ hξ hF hY)
  · intro i
    exact ⟨hbound i, martingale_increment_condVar_le hD i.val (hc i) (hbound i)⟩
  · intro L u hT hL hcL hu
    exact doob_abs_tail_of_increment_bound ξ hξ hF hY hbound hT hL hcL hu

end Balanced

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_FiniteUniformConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace Balanced.FiniteUniform

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem measure_eq_product :
    (PMF.uniformOfFintype (I → A)).toMeasure = Slots.law (fun _ : I => A) := by
  rw [Slots.law_eq_uniformOn]
  apply Measure.ext_of_singleton
  intro f
  simp [uniformOn_univ]

theorem bounded_differences (Y : (I → A) → ℝ) (c : I → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hosc : ∀ i x y, (∀ j, j ≠ i → x j = y j) → |Y x - Y y| ≤ c i)
    {L u : ℝ} (hI : 1 ≤ Fintype.card I) (hL : 0 < L)
    (hcL : ∀ i, c i ≤ L) (hu : 0 < u) :
    (PMF.uniformOfFintype (I → A)).toMeasure.real
      {f | u ≤ |Y f - ∫ g, Y g ∂(PMF.uniformOfFintype (I → A)).toMeasure|} ≤
      2 * Real.exp (-(u ^ 2) / (8 * (Fintype.card I : ℝ) * L ^ 2)) := by
  classical
  let e := Fintype.equivFin I
  let μ := (PMF.uniformOfFintype (I → A)).toMeasure
  let ξ : Fin (Fintype.card I) → (I → A) → A := fun i f => f (e.symm i)
  let Z : (Fin (Fintype.card I) → A) → ℝ := fun x => Y (fun i => x (e i))
  have hξ : ∀ i, Measurable (ξ i) := fun i => measurable_pi_apply _
  have hind : iIndepFun ξ μ := by
    dsimp [μ]
    rw [measure_eq_product]
    exact (Slots.independent_coordinates (V := fun _ : I => A)).precomp e.symm.injective
  have hosc' : IndependentTrials.CoordinateOscillation Z (fun i => c (e.symm i)) := by
    intro i x y hxy
    apply hosc (e.symm i)
    intro j hj
    apply hxy (e j)
    intro heq
    apply hj
    exact e.injective (by simpa using heq)
  have hZ (f : I → A) : Z (IndependentTrials.trialVector ξ f) = Y f := by
    simp [Z, IndependentTrials.trialVector, ξ]
  have ht := independentTrialJumps_proof (Fintype.card I) (I → A) inferInstance μ
    (fun _ => A) (fun _ => inferInstance) ξ hξ Z (measurable_of_countable Z)
    hind Integrable.of_finite (fun i => c (e.symm i)) (fun i => hc _) hosc'
  have htail := ht.2.2.2 L u hI hL (fun i => hcL _) hu
  simpa only [hZ] using htail

end Balanced.FiniteUniform

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Probability_VacantBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.VacantBins

open scoped BigOperators

variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]

theorem card_avoiding (a : A) :
    Fintype.card {f : I → A // ∀ i, f i ≠ a} =
      (Fintype.card A - 1) ^ Fintype.card I := by
  classical
  rw [Fintype.card_congr (avoidingEquiv (I := I) a), Fintype.card_fun]
  congr 1
  simp

theorem sum_missedCount :
    (∑ f : I → A, missedCount f) =
      Fintype.card A * (Fintype.card A - 1) ^ Fintype.card I := by
  classical
  have hcount (f : I → A) :
      missedCount f = ∑ a : A, if (∀ i, f i ≠ a) then 1 else 0 := by
    simp [missedCount, missed]
  simp_rw [hcount]
  rw [Finset.sum_comm]
  have havoid (a : A) :
      (∑ f : I → A, if (∀ i, f i ≠ a) then 1 else 0) =
        (Fintype.card A - 1) ^ Fintype.card I := by
    simpa [Fintype.card_subtype] using card_avoiding (I := I) a
  simp_rw [havoid]
  simp

omit [DecidableEq A] in
theorem uniformMean_equiv {B : Type*} [Fintype B] [DecidableEq B]
    (e : (I → A) ≃ (I → B)) (Y : (I → B) → ℝ) :
    uniformMean (fun f : I → A => Y (e f)) = uniformMean Y := by
  unfold uniformMean
  rw [e.sum_comp, Fintype.card_congr e]

theorem uniformMean_missedCount [Nonempty A] :
    uniformMean (fun f : I → A => (missedCount f : ℝ)) =
      (Fintype.card A : ℝ) *
        (1 - 1 / (Fintype.card A : ℝ)) ^ Fintype.card I := by
  classical
  have hq : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr inferInstance
  have hq0 : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : Fintype.card A ≠ 0)
  have hsum : (∑ f : I → A, (missedCount f : ℝ)) =
      (Fintype.card A : ℝ) *
        ((Fintype.card A : ℝ) - 1) ^ Fintype.card I := by
    have h := sum_missedCount (I := I) (A := A)
    exact_mod_cast h
  unfold uniformMean
  rw [hsum, Fintype.card_fun, Nat.cast_pow]
  rw [show (1 : ℝ) - 1 / (Fintype.card A : ℝ) =
      ((Fintype.card A : ℝ) - 1) / (Fintype.card A : ℝ) by
    field_simp]
  rw [div_pow]
  ring

theorem integral_uniform_eq_uniformMean [Nonempty A]
    [MeasurableSpace (I → A)] [MeasurableSingletonClass (I → A)]
    (Y : (I → A) → ℝ) :
    (∫ f, Y f ∂(PMF.uniformOfFintype (I → A)).toMeasure) = uniformMean Y := by
  classical
  rw [MeasureTheory.integral_fintype (MeasureTheory.Integrable.of_finite)]
  have hmass (f : I → A) :
      (PMF.uniformOfFintype (I → A)).toMeasure.real {f} =
        (Fintype.card (I → A) : ℝ)⁻¹ := by
    simp [MeasureTheory.measureReal_def]
  simp_rw [hmass, smul_eq_mul]
  rw [← Finset.mul_sum]
  simp [uniformMean, div_eq_mul_inv, mul_comm]

theorem missedCount_le_add_one_of_eq_off (f g : I → A) (j : I)
    (hfg : ∀ i, i ≠ j → f i = g i) :
    missedCount f ≤ missedCount g + 1 := by
  classical
  have hsub : missed f ⊆ insert (g j) (missed g) := by
    intro a ha
    by_cases hag : a = g j
    · simp [hag]
    · apply Finset.mem_insert_of_mem
      rw [mem_missed] at ha ⊢
      intro i
      by_cases hij : i = j
      · simpa [hij, eq_comm] using hag
      · simpa [hfg i hij] using ha i
  calc
    missedCount f ≤ (insert (g j) (missed g)).card := Finset.card_le_card hsub
    _ ≤ missedCount g + 1 := Finset.card_insert_le _ _

theorem abs_missedCount_sub_le_one (f g : I → A) (j : I)
    (hfg : ∀ i, i ≠ j → f i = g i) :
    |(missedCount f : ℝ) - (missedCount g : ℝ)| ≤ 1 := by
  have h₁ := missedCount_le_add_one_of_eq_off f g j hfg
  have h₂ := missedCount_le_add_one_of_eq_off g f j
    (fun i hi => (hfg i hi).symm)
  have h₁R : (missedCount f : ℝ) ≤ (missedCount g : ℝ) + 1 := by
    exact_mod_cast h₁
  have h₂R : (missedCount g : ℝ) ≤ (missedCount f : ℝ) + 1 := by
    exact_mod_cast h₂
  rw [abs_le]
  constructor <;> linarith

end Balanced.VacantBins

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_LineOccupancy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.LineOccupancy

open scoped BigOperators

variable {F : Type*} [Field F]

theorem transverseHitEquiv_eq_iff (l : Line F) (d : Direction F)
    (hne : l.1 ≠ d) (a : F) (p : {p : Point F // OnLine p l}) :
    transverseHitEquiv l d hne a = p ↔ OnLine p.val (d, a) := by
  rw [← Equiv.eq_symm_apply]
  change a = lineEval d p.val ↔ lineEval d p.val = a
  exact eq_comm

variable [Fintype F] [DecidableEq F]

theorem unhitCount_eq_missedCount (l : Line F) (a : TransverseDirections l → F) :
    unhitCount l a = VacantBins.missedCount (hitAssignmentsEquiv l a) := by
  classical
  unfold unhitCount VacantBins.missedCount
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, VacantBins.mem_missed]
  apply forall_congr'
  intro d
  exact not_congr (transverseHitEquiv_eq_iff l d.val (Ne.symm d.property) (a d) p).symm

theorem unhitCount_eq_filter_card (l : Line F) (a : TransverseDirections l → F) :
    unhitCount l a = ((linePoints l).filter
      (fun p => ∀ d : TransverseDirections l, ¬ OnLine p (d.val, a d))).card := by
  classical
  unfold unhitCount
  refine Finset.card_bij (fun p _ => p.val) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, linePoints, Finset.mem_univ, true_and]
    exact ⟨p.property, hp⟩
  · intro p hp r hr h
    exact Subtype.ext h
  · intro p hp
    simp only [Finset.mem_filter, linePoints, Finset.mem_univ, true_and] at hp
    refine ⟨⟨p, hp.1⟩, ?_, rfl⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hp.2

theorem unhitCount_eq_initiallyRetained (l : Line F) (M : MergedPairs F)
    (hl : l ∉ initialDeletedLines M) :
    unhitCount l (transverseOffsets l M) = (linePoints l ∩ initiallyRetained M).card := by
  classical
  rw [unhitCount_eq_filter_card]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_inter, initiallyRetained,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, ht⟩
    refine ⟨hp, ?_⟩
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨d, _, rfl⟩
    by_cases hd : d = l.1
    · intro hpd
      have hpl : OnLine p l := (Finset.mem_filter.mp hp).2
      have heq : l = constituent M d true :=
        eq_of_onLine_same_direction p l (constituent M d true) hd.symm hpl hpd
      apply hl
      rw [heq]
      exact Finset.mem_image.mpr ⟨d, Finset.mem_univ d, rfl⟩
    · exact ht ⟨d, hd⟩
  · rintro ⟨hp, ht⟩
    refine ⟨hp, ?_⟩
    intro d
    exact ht (constituent M d.val true)
      (Finset.mem_image.mpr ⟨d.val, Finset.mem_univ _, rfl⟩)

theorem uniformMean_unhitCount (l : Line F) :
    VacantBins.uniformMean (fun a : TransverseDirections l → F => (unhitCount l a : ℝ)) =
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F := by
  classical
  let : Nonempty {p : Point F // OnLine p l} := ⟨(linePointsEquiv l).symm 0⟩
  simp_rw [unhitCount_eq_missedCount]
  rw [VacantBins.uniformMean_equiv (hitAssignmentsEquiv l)
    (fun f => (VacantBins.missedCount f : ℝ))]
  rw [VacantBins.uniformMean_missedCount, card_transverseDirections,
    Fintype.card_congr (linePointsEquiv l)]

theorem integral_unhitCount (l : Line F)
    [MeasurableSpace (TransverseDirections l → F)]
    [MeasurableSingletonClass (TransverseDirections l → F)] :
    (∫ a : TransverseDirections l → F, (unhitCount l a : ℝ)
      ∂(PMF.uniformOfFintype (TransverseDirections l → F)).toMeasure) =
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F := by
  rw [VacantBins.integral_uniform_eq_uniformMean, uniformMean_unhitCount]

theorem abs_unhitCount_sub_le_one (l : Line F)
    (a b : TransverseDirections l → F) (j : TransverseDirections l)
    (hab : ∀ i, i ≠ j → a i = b i) :
    |(unhitCount l a : ℝ) - (unhitCount l b : ℝ)| ≤ 1 := by
  simp_rw [unhitCount_eq_missedCount]
  apply VacantBins.abs_missedCount_sub_le_one _ _ j
  intro i hi
  change transverseHitEquiv l i.val (Ne.symm i.property) (a i) =
    transverseHitEquiv l i.val (Ne.symm i.property) (b i)
  rw [hab i hi]

end Balanced.LineOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_LineOccupancyAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.LineOccupancy

open Filter Topology

theorem tendsto_vacant_fraction :
    Tendsto (fun q : ℕ => (1 - 1 / (q : ℝ)) ^ q) atTop (𝓝 (Real.exp (-1))) := by
  simpa [sub_eq_add_neg, div_eq_mul_inv] using Real.tendsto_one_add_div_pow_exp (-1)

theorem one_quarter_lt_exp_neg_one : (1 / 4 : ℝ) < Real.exp (-1) := by
  rw [Real.exp_neg, ← one_div]
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 4) (Real.exp_pos 1)).2
  nlinarith [Real.exp_one_lt_three]

theorem eventually_mean_gap :
    ∀ᶠ q : ℕ in atTop,
      (q : ℝ) * (1 - 1 / (q : ℝ)) ^ q - (q : ℝ) / 5 ≥ (q : ℝ) / 20 := by
  have h := tendsto_vacant_fraction.eventually
    (eventually_gt_nhds one_quarter_lt_exp_neg_one)
  filter_upwards [h] with q hq
  have hm := mul_le_mul_of_nonneg_left hq.le (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  nlinarith

theorem occupancy_exponent (q : ℕ) (hq : 0 < q) :
    -(((q : ℝ) / 20) ^ 2) / (8 * (q : ℝ) * (1 : ℝ) ^ 2) = -(q : ℝ) / 3200 := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
  field_simp
  ring

theorem tendsto_line_union_bound :
    Tendsto (fun q : ℕ =>
      (q : ℝ) * ((q : ℝ) + 1) * (2 * Real.exp (-(q : ℝ) / 3200)))
      atTop (𝓝 0) := by
  have h₁ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    1 (1 / 3200) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h₂ := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    2 (1 / 3200) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h := (h₂.add h₁).const_mul 2
  convert h using 1
  · funext q
    simp only [Function.comp_apply, Real.rpow_one, Real.rpow_two]
    rw [show -(q : ℝ) / 3200 = -(1 / 3200) * (q : ℝ) by ring]
    ring
  · norm_num

end Balanced.LineOccupancy

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Selection_LineOccupancyConcentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Classical

namespace Balanced.LineOccupancy

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem offsetLaw_map_transverse (l : Line F) :
    (offsetLaw F).map (transverseOffsets l) =
      PMF.uniformOfFintype (TransverseDirections l → F) := by
  have ho : offsetLaw F = PMF.uniformOfFintype (MergedPairs F) := by
    unfold offsetLaw
    congr 1
    exact Subsingleton.elim _ _
  rw [ho]
  let e : TransverseDirections l ↪ Direction F × Bool :=
    ⟨fun d => (d.val, true), fun a b h => Subtype.ext (congrArg Prod.fst h)⟩
  let c : MergedPairs F ≃ (Direction F × Bool → F) := Equiv.curry _ _ _ |>.symm
  have hc := TupleAlignment.uniform_map_equiv c
  calc
    _ = ((PMF.uniformOfFintype (MergedPairs F)).map c).map
        (fun o i => o (e i)) := by
      rw [PMF.map_comp]
      rfl
    _ = _ := by
      rw [hc]
      exact TupleAlignment.uniform_map_restrict e

theorem transverse_failure_le (l : Line F)
    (hgap : (Fintype.card F : ℝ) / 20 ≤
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F -
        (Fintype.card F : ℝ) / 5) :
    ((PMF.uniformOfFintype (TransverseDirections l → F)).toOuterMeasure
      {a | (unhitCount l a : ℝ) < (Fintype.card F : ℝ) / 5}).toReal ≤
      2 * Real.exp (-(Fintype.card F : ℝ) / 3200) := by
  let : MeasurableSpace F := ⊤
  let : MeasurableSingletonClass F := ⟨fun _ => trivial⟩
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hqR : (0 : ℝ) < Fintype.card F := Nat.cast_pos.mpr hq
  have ht := FiniteUniform.bounded_differences
    (fun a : TransverseDirections l → F => (unhitCount l a : ℝ)) (fun _ => 1)
    (fun _ => by norm_num)
    (fun i a b h => abs_unhitCount_sub_le_one l a b i h)
    (L := 1) (u := (Fintype.card F : ℝ) / 20)
    (by rw [card_transverseDirections]; exact Nat.succ_le_iff.mpr hq) (by norm_num) (fun _ => le_rfl) (by positivity)
  rw [integral_unhitCount (F := F) l, card_transverseDirections, occupancy_exponent _ hq] at ht
  have hsub : {a : TransverseDirections l → F |
        (unhitCount l a : ℝ) < (Fintype.card F : ℝ) / 5} ⊆
      {a | (Fintype.card F : ℝ) / 20 ≤
        |(unhitCount l a : ℝ) -
          (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F|} := by
    intro a ha
    change (unhitCount l a : ℝ) < (Fintype.card F : ℝ) / 5 at ha
    change (Fintype.card F : ℝ) / 20 ≤
      |(unhitCount l a : ℝ) -
        (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F|
    have habs := neg_le_abs ((unhitCount l a : ℝ) -
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F)
    linarith
  calc
    _ = (PMF.uniformOfFintype (TransverseDirections l → F)).toMeasure.real
        {a | (unhitCount l a : ℝ) < (Fintype.card F : ℝ) / 5} := by
      rw [Measure.real, PMF.toMeasure_apply_eq_toOuterMeasure_apply]
      exact (Set.toFinite _).measurableSet
    _ ≤ _ := measureReal_mono hsub
    _ ≤ _ := ht

theorem offset_failure_le (l : Line F)
    (hgap : (Fintype.card F : ℝ) / 20 ≤
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F -
        (Fintype.card F : ℝ) / 5) :
    offsetEventProbability (F := F)
      {M | (unhitCount l (transverseOffsets l M) : ℝ) < (Fintype.card F : ℝ) / 5} ≤
      2 * Real.exp (-(Fintype.card F : ℝ) / 3200) := by
  have h := transverse_failure_le l hgap
  rw [← offsetLaw_map_transverse l, PMF.toOuterMeasure_map_apply] at h
  exact h

omit [DecidableEq F] in

theorem offsetEventProbability_eq_real [MeasurableSpace (MergedPairs F)]
    [MeasurableSingletonClass (MergedPairs F)] (s : Set (MergedPairs F)) :
    offsetEventProbability s = (offsetLaw F).toMeasure.real s := by
  rw [offsetEventProbability, Measure.real,
    (offsetLaw F).toMeasure_apply_eq_toOuterMeasure_apply ((Set.toFinite s).measurableSet)]

theorem initial_failure_probability_le
    (hgap : (Fintype.card F : ℝ) / 20 ≤
      (Fintype.card F : ℝ) * (1 - 1 / (Fintype.card F : ℝ)) ^ Fintype.card F -
        (Fintype.card F : ℝ) / 5) :
    offsetEventProbability (F := F)
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5} ≤
      (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) + 1) *
        (2 * Real.exp (-(Fintype.card F : ℝ) / 3200)) := by
  let : MeasurableSpace (MergedPairs F) := ⊤
  let : MeasurableSingletonClass (MergedPairs F) := ⟨fun _ => trivial⟩
  let B (l : Line F) : Set (MergedPairs F) :=
    {M | (unhitCount l (transverseOffsets l M) : ℝ) < (Fintype.card F : ℝ) / 5}
  have hsub : {M : MergedPairs F | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5} ⊆
      ⋃ l, B l := by
    rintro M ⟨l, hl, hbad⟩
    apply Set.mem_iUnion.mpr
    refine ⟨l, ?_⟩
    change (unhitCount l (transverseOffsets l M) : ℝ) < _
    rw [unhitCount_eq_initiallyRetained l M hl]
    exact hbad
  rw [offsetEventProbability_eq_real]
  calc
    _ ≤ (offsetLaw F).toMeasure.real (⋃ l, B l) := measureReal_mono hsub
    _ ≤ ∑ l, (offsetLaw F).toMeasure.real (B l) := measureReal_iUnion_fintype_le B
    _ ≤ ∑ _l : Line F, (2 * Real.exp (-(Fintype.card F : ℝ) / 3200)) := by
      apply Finset.sum_le_sum
      intro l _
      rw [← offsetEventProbability_eq_real]
      exact offset_failure_le l hgap
    _ = _ := by simp [Line, Direction, mul_comm]

theorem tendsto_initial_failure (F : ℕ → Type*)
    [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card (F n) : ℝ) / 5})
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
  · filter_upwards [hq.eventually eventually_mean_gap] with n hn
    exact initial_failure_probability_le hn
  · exact tendsto_line_union_bound.comp hq

theorem initial_good_probability_eq_one_sub :
    offsetEventProbability (F := F)
      {M | ∀ l, l ∉ initialDeletedLines M →
        (Fintype.card F : ℝ) / 5 ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)} =
      1 - offsetEventProbability (F := F)
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5} := by
  let : MeasurableSpace (MergedPairs F) := ⊤
  let : MeasurableSingletonClass (MergedPairs F) := ⟨fun _ => trivial⟩
  have heq : {M : MergedPairs F | ∀ l, l ∉ initialDeletedLines M →
        (Fintype.card F : ℝ) / 5 ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)} =
      {M | ∃ l, l ∉ initialDeletedLines M ∧
        ((linePoints l ∩ initiallyRetained M).card : ℝ) < (Fintype.card F : ℝ) / 5}ᶜ := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_and, not_lt]
  rw [heq, offsetEventProbability_eq_real,
    probReal_compl_eq_one_sub ((Set.toFinite _).measurableSet),
    ← offsetEventProbability_eq_real]

theorem tendsto_initial_occupancy (F : ℕ → Type*)
    [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | ∀ l, l ∉ initialDeletedLines M →
        (1 / 5 : ℝ) * (Fintype.card (F n) : ℝ) ≤
          ((linePoints l ∩ initiallyRetained M).card : ℝ)}) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_initial_failure F hq)
  simpa only [one_div, mul_comm (5 : ℝ)⁻¹, ← div_eq_mul_inv,
    initial_good_probability_eq_one_sub, sub_zero] using h

end Balanced.LineOccupancy

end

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateProbabilityAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateProbability

open Filter
open scoped Topology

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem tendsto_geometricGood
    (F : ℕ → Type*) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n) {M | GeometricGood M})
      atTop (𝓝 1) := by
  have h := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => {M | ∀ p, sampledMultiplicity M p ≤
      ⌈Real.log (Fintype.card (F n) : ℝ)⌉₊})
    (fun n => {M | ∀ l, l ∉ initialDeletedLines M →
      (1 / 5 : ℝ) * Fintype.card (F n) ≤
        ((linePoints l ∩ initiallyRetained M).card : ℝ)})
    (tendsto_sampledMultiplicity_good F hq)
    (LineOccupancy.tendsto_initial_occupancy F hq)
  simpa only [offsetEventProbability, ← Set.ofPred_and, GeometricGood] using h

universe u

end
end Balanced.CandidateProbability

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateRetentionTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem valid_mem_successfulChoices {M : MergedPairs F} {g : Direction F}
    {C : SplitChoice F} (h : ValidChoice M g C) : C ∈ successfulChoices M := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, h.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  simpa only [h.1] using h.2.2.2.1

theorem retained_filter_card_le_two (M : MergedPairs F) (P : SplitChoice F → Prop)
    (all : Finset (SplitChoice F))
    (hall : ∀ v ∈ candidateVertices M, P (candidateChoice M v) →
      candidateChoice M v ∈ all) :
    ((candidateVertices M).filter (fun v => P (candidateChoice M v))).card ≤
      2 * all.card := by
  let f : CandidateVertex F → Bool × SplitChoice F :=
    fun v => (v.1.2, candidateChoice M v)
  have h := Finset.card_le_card_of_injOn f
    (s := (candidateVertices M).filter (fun v => P (candidateChoice M v)))
    (t := (Finset.univ : Finset Bool) ×ˢ all)
    (fun v hv => by
      obtain ⟨hv, hp⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, hall v hv hp⟩)
    (fun v _ w _ heq => by
      apply CandidateIncidence.eq_of_same_line_same_bit
      · exact congrArg (fun z : Bool × SplitChoice F => z.2.line) heq
      · exact congrArg (fun z : Bool × SplitChoice F => z.1) heq)
  simpa only [Finset.card_product, Finset.card_univ, Fintype.card_bool] using h

theorem slot_filter_card_le (M : MergedPairs F) (s : Slot F)
    (P : SplitChoice F → Prop) (all : Finset (SplitChoice F))
    (hall : ∀ v ∈ candidateSlot M s, P (candidateChoice M v) →
      candidateChoice M v ∈ all) :
    ((candidateSlot M s).filter (fun v => P (candidateChoice M v))).card ≤ all.card := by
  apply Finset.card_le_card_of_injOn (candidateChoice M)
  · intro v hv
    obtain ⟨hv, hp⟩ := Finset.mem_filter.mp hv
    exact hall v hv hp
  · intro v hv w hw heq
    apply candidateSlot_line_injective M s
      (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hw).1
    exact congrArg SplitChoice.line heq

theorem retained_test_card_le (M : MergedPairs F) (P : SplitChoice F → Prop) :
    ((candidateVertices M).filter (fun v => P (candidateChoice M v))).card ≤
      2 * (successfulTest M P).card := by
  apply retained_filter_card_le_two
  intro v hv hp
  exact Finset.mem_filter.mpr
    ⟨valid_mem_successfulChoices (CandidateIncidence.valid hv), hp⟩

theorem slot_test_card_le (M : MergedPairs F) (s : Slot F)
    (P : SplitChoice F → Prop) :
    ((candidateSlot M s).filter (fun v => P (candidateChoice M v))).card ≤
      (successfulTest M (fun C => C.line.1 = s.1 ∧ P C)).card := by
  apply slot_filter_card_le M s P (successfulTest M (fun C => C.line.1 = s.1 ∧ P C))
  intro v hv hp
  obtain ⟨hv, hs⟩ := mem_candidateSlot.mp hv
  apply (mem_successfulTest M _ _).mpr
  refine ⟨valid_mem_successfulChoices (retainedChoice_valid hv), ?_, hp⟩
  change v.1.1 = s.1
  exact congrArg (fun t : Slot F => t.1) hs

theorem pointCandidates_card_le (M : MergedPairs F) (p : Point F) :
    (CandidateIncidence.pointCandidates M p).card ≤
      2 * (successfulTest M (fun C => p ∈ designated M C)).card := by
  convert retained_test_card_le M (fun choice => p ∈ designated M choice) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  unfold CandidateIncidence.pointCandidates
  congr 1

theorem pointLineCandidates_card_le (M : MergedPairs F) (p : Point F) (l : Line F) :
    (CandidateIncidence.pointLineCandidates M p l).card ≤
      2 * (successfulTest M (fun C => OnLine p C.line ∧
        ∃ r ∈ designated M C, OnLine r l)).card := by
  convert retained_test_card_le M (fun choice => OnLine p choice.line ∧
    ∃ point ∈ designated M choice, OnLine point l) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  unfold CandidateIncidence.pointLineCandidates
  congr 1

theorem twoLineCandidates_card_le (M : MergedPairs F) (l k : Line F) :
    (CandidateIncidence.twoLineCandidates M l k).card ≤
      2 * (successfulTest M (fun C =>
        ∃ p ∈ designated M C, ∃ r ∈ designated M C,
          p ≠ r ∧ OnLine p l ∧ OnLine r k)).card := by
  convert retained_test_card_le M (fun choice =>
    ∃ point ∈ designated M choice, ∃ other ∈ designated M choice,
      point ≠ other ∧ OnLine point l ∧ OnLine other k) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  unfold CandidateIncidence.twoLineCandidates
  congr 1

theorem generatorPairCandidates_card_le (M : MergedPairs F)
    (e : Finset (Direction F)) :
    (CandidateIncidence.generatorPairCandidates M e).card ≤
      2 * (successfulTest M (fun C => e ⊆ generatorSet C.tuple)).card := by
  convert retained_test_card_le M (fun choice => e ⊆ generatorSet choice.tuple) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  unfold CandidateIncidence.generatorPairCandidates
  congr 1

theorem lineHitSlot_card_le (M : MergedPairs F) (s : Slot F) (l : Line F) :
    (CandidateIncidence.lineHitSlot M s l).card ≤
      (successfulTest M (fun C => C.line.1 = s.1 ∧
        ∃ p ∈ designated M C, OnLine p l)).card := by
  convert slot_test_card_le M s
    (fun choice => ∃ point ∈ designated M choice, OnLine point l) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  unfold CandidateIncidence.lineHitSlot
  congr 1

theorem lineHitAll_card_le (M : MergedPairs F) (l : Line F) :
    ((candidateVertices M).filter (fun v =>
      ∃ p ∈ CandidateIncidence.points M v, OnLine p l)).card ≤
      2 * (successfulTest M (fun C => ∃ p ∈ designated M C, OnLine p l)).card := by
  convert retained_test_card_le M
    (fun choice => ∃ point ∈ designated M choice, OnLine point l) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  congr 1

end
end Balanced.CandidateRetentionTransport

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateSuccessfulAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateRetentionTransport

noncomputable section
open scoped Classical
universe u

theorem exists_threshold_candidateGraphGood_of_successful_counts
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F → ∀ (M : MergedPairs F) (c : ℝ),
      let P := Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))
      (∀ s : Slot F, c * Fintype.card F ≤ ((candidateSlot M s).card : ℝ)) →
      (∀ p, (successfulTest M (fun A => p ∈ designated M A)).card ≤ P) →
      (∀ p l, ¬ OnLine p l →
        (successfulTest M (fun A => OnLine p A.line ∧
          ∃ r ∈ designated M A, OnLine r l)).card ≤ P) →
      (∀ l k : Line F, l ≠ k → l ∉ constituentLines M → k ∉ constituentLines M →
        (successfulTest M (fun A => ∃ p ∈ designated M A, ∃ r ∈ designated M A,
          p ≠ r ∧ OnLine p l ∧ OnLine r k)).card ≤ P) →
      (∀ e : Finset (Direction F), e.card = 2 →
        (successfulTest M (fun A => e ⊆ generatorSet A.tuple)).card ≤ P) →
      (∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card F : ℝ))) →
      (∀ g : Direction F, ∀ l : Line F,
        (successfulTest M (fun A => A.line.1 = g ∧
          ∃ p ∈ designated M A, OnLine p l)).card ≤ P) →
      (∀ l : Line F, l ∉ constituentLines M →
        ((successfulTest M (fun A => ∃ p ∈ designated M A, OnLine p l)).card : ℝ) ≤
          C * Fintype.card F) →
      (∀ l : Line F, l ∉ initialDeletedLines M →
        (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)) →
      CandidateGraphGood M c (2 * C + 11) := by
  obtain ⟨N, hN⟩ := CandidateIncidence.exists_threshold_candidateGraphGood_of_scaled_counts.{u}
    2 (by omega) (2 * C) (by positivity)
  refine ⟨N, ?_⟩
  intro F _ _ _ hq M c P hsize hpoint hmixed htwo hpair hcap hline hglobal hoccupancy
  apply hN F hq M c hsize
  · intro p
    exact (pointCandidates_card_le M p).trans (Nat.mul_le_mul_left 2 (hpoint p))
  · intro p l hpl
    exact (pointLineCandidates_card_le M p l).trans
      (Nat.mul_le_mul_left 2 (hmixed p l hpl))
  · intro l k hlk hl hk
    exact (twoLineCandidates_card_le M l k).trans
      (Nat.mul_le_mul_left 2 (htwo l k hlk hl hk))
  · intro e he
    exact (generatorPairCandidates_card_le M e).trans
      (Nat.mul_le_mul_left 2 (hpair e he))
  · exact hcap
  · intro s l
    have h := (lineHitSlot_card_le M s l).trans (hline s.1 l)
    omega
  · intro l hl
    have hcount :
        (((candidateVertices M).filter (fun v =>
          ∃ p ∈ CandidateIncidence.points M v, OnLine p l)).card : ℝ) ≤
        2 * (successfulTest M (fun A => ∃ p ∈ designated M A, OnLine p l)).card := by
      exact_mod_cast lineHitAll_card_le M l
    have hg := hglobal l hl
    nlinarith
  · exact hoccupancy

end
end Balanced.CandidateRetentionTransport

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Incidence_CandidateIncidenceTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open scoped Classical
open CandidateRetentionTransport

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem smallGood_iff (M : MergedPairs F) (P : ℕ) : SmallGood M P ↔
    (∀ p, (successfulTest M (fun A => p ∈ designated M A)).card ≤ P) ∧
    (∀ p l, ¬ OnLine p l →
      (successfulTest M (fun A => OnLine p A.line ∧
        ∃ r ∈ designated M A, OnLine r l)).card ≤ P) ∧
    (∀ l k : Line F, l ≠ k → l ∉ constituentLines M → k ∉ constituentLines M →
      (successfulTest M (fun A => ∃ p ∈ designated M A, ∃ r ∈ designated M A,
        p ≠ r ∧ OnLine p l ∧ OnLine r k)).card ≤ P) ∧
    (∀ e : Finset (Direction F), e.card = 2 →
      (successfulTest M (fun A => e ⊆ generatorSet A.tuple)).card ≤ P) ∧
    (∀ g : Direction F, ∀ l : Line F,
      (successfulTest M (fun A => A.line.1 = g ∧
        ∃ p ∈ designated M A, OnLine p l)).card ≤ P) := by
  constructor
  · intro h
    refine ⟨fun p => h (Sum.inl p), ?_, ?_, ?_,
      fun g l => h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (g,l)))))⟩
    · intro p l hp
      simpa only [count, ite_eq_left hp] using h (Sum.inr (Sum.inl (p,l)))
    · intro l k hne hl hk
      have hg : l ≠ k ∧ l ∉ constituentLines M ∧ k ∉ constituentLines M := ⟨hne, hl, hk⟩
      simpa only [count, ite_eq_left hg] using
        h (Sum.inr (Sum.inr (Sum.inl (l,k))))
    · intro e he
      obtain ⟨d, f, hdf, rfl⟩ := Finset.card_eq_two.mp he
      simpa only [count, ite_eq_left hdf] using
        h (Sum.inr (Sum.inr (Sum.inr (Sum.inl (d,f)))))
  · rintro ⟨hp, hpl, hll, hde, hgl⟩ t
    rcases t with p | (⟨p,l⟩ | (⟨l,k⟩ | (⟨d,e⟩ | ⟨g,l⟩)))
    · exact hp p
    · by_cases h : OnLine p l
      · simp [count, h]
      · simpa only [count, ite_eq_left h] using hpl p l h
    · simp only [count]
      split_ifs with h
      · exact hll l k h.1 h.2.1 h.2.2
      · exact Nat.zero_le P
    · simp only [count]
      split_ifs with h
      · exact hde {d,e} (by simp [h])
      · exact Nat.zero_le P
    · exact hgl g l

universe u

theorem exists_threshold_graphGood (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      N ≤ Fintype.card F → ∀ (M : MergedPairs F) (c : ℝ),
      SizeGood M c →
      SmallGood M (Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ))) →
      GlobalGood M C →
      (∀ p, sampledMultiplicity M p ≤ Nat.ceil (Real.log (Fintype.card F : ℝ))) →
      (∀ l : Line F, l ∉ initialDeletedLines M →
        (1 / 5 : ℝ) * Fintype.card F ≤ ((linePoints l ∩ initiallyRetained M).card : ℝ)) →
      CandidateGraphGood M c (2 * C + 11) := by
  obtain ⟨N, hN⟩ := exists_threshold_candidateGraphGood_of_successful_counts.{u} C hC
  refine ⟨N, ?_⟩
  intro F _ _ _ hq M c hsize hsmall hglobal hcap hocc
  obtain ⟨hp, hpl, hll, hde, hgl⟩ := (smallGood_iff M _).mp hsmall
  exact hN F hq M c hsize hp hpl hll hde hcap hgl hglobal hocc

end
end Balanced.CandidateIncidenceTests

end OAI
end

section
-- module Solutions.OAIQ063_BR.BalancedRyser_Candidates_CandidateGraphProbabilityReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology Classical

namespace Balanced.CandidateIncidenceTests

universe u

theorem tendsto_candidateGraphGood_of_incidence
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop)
    (c C : ℝ) (hC : 0 ≤ C)
    (hsize : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | SizeGood M c}) atTop (𝓝 1))
    (hsmall : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
      atTop (𝓝 1))
    (hglobal : Tendsto (fun n => offsetEventProbability (F := F n)
      {M | GlobalGood M C}) atTop (𝓝 1)) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | CandidateGraphGood M c (2 * C + 11)}) atTop (𝓝 1) := by
  have h₁ := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun _ => {M | SizeGood M c})
    (fun n => {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
    hsize hsmall
  have h₂ := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => {M | SizeGood M c} ∩
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
    (fun _ => {M | GlobalGood M C}) h₁ hglobal
  have h₃ := tendsto_pmf_outerReal_inter_of_good (fun n => offsetLaw (F n))
    (fun n => ({M | SizeGood M c} ∩
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))}) ∩
      {M | GlobalGood M C})
    (fun _ => {M | CandidateProbability.GeometricGood M}) h₂
    (CandidateProbability.tendsto_geometricGood F hq)
  obtain ⟨N, hN⟩ := exists_threshold_graphGood.{u} C hC
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h₃ tendsto_const_nhds
  · filter_upwards [hq.eventually (eventually_ge_atTop N)] with n hn
    apply pmf_outerReal_mono (offsetLaw (F n))
    rintro M ⟨⟨⟨hs, hm⟩, hg⟩, hgeo⟩
    exact hN (F n) hn M c hs hm hg hgeo.1 hgeo.2
  · apply Eventually.of_forall
    intro n
    let : MeasurableSpace (MergedPairs (F n)) := ⊤
    let : MeasurableSingletonClass (MergedPairs (F n)) := ⟨fun _ => trivial⟩
    rw [LineOccupancy.offsetEventProbability_eq_real]
    exact MeasureTheory.measureReal_le_one

theorem candidateGraphResult_of_incidence_estimates_oai (c C : ℝ) (hc : 0 < c) (hC : 0 ≤ C)
    (hsize : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
      [∀ n, DecidableEq (F n)],
      Tendsto (fun n => Fintype.card (F n)) atTop atTop →
      Tendsto (fun n => offsetEventProbability (F := F n) {M | SizeGood M c})
        atTop (𝓝 1))
    (hsmall : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
      [∀ n, DecidableEq (F n)],
      Tendsto (fun n => Fintype.card (F n)) atTop atTop →
      Tendsto (fun n => offsetEventProbability (F := F n)
        {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
        atTop (𝓝 1))
    (hglobal : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
      [∀ n, DecidableEq (F n)],
      Tendsto (fun n => Fintype.card (F n)) atTop atTop →
      Tendsto (fun n => offsetEventProbability (F := F n) {M | GlobalGood M C})
        atTop (𝓝 1)) : CandidateGraphResult.{u} := by
  refine ⟨c, 2 * C + 11, hc, by linarith, ?_⟩
  intro F _ _ _ hq
  have hgood := tendsto_candidateGraphGood_of_incidence F hq c C hC
    (hsize F hq) (hsmall F hq) (hglobal F hq)
  exact ⟨hgood, tendsto_candidateGood_and_distinct F hq c (2 * C + 11) hgood⟩

end Balanced.CandidateIncidenceTests

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_incidence_estimates_oai.{u} := @OAI.Balanced.CandidateIncidenceTests.candidateGraphResult_of_incidence_estimates_oai.{u}
