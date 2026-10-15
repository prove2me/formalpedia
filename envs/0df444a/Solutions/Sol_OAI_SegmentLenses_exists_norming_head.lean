-- Prove2me | solution 1 for OAI.SegmentLenses.exists_norming_head
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T21:37:09.086282+00:00
-- url     : https://prove2.me/submissions/dd02f6cd-2388-4cfd-babe-b154936d859e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/HeadTests.lean:L110-L128
-- (upload_full_project.md Phase 4): solution for node OAI.SegmentLenses.exists_norming_head. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery
import Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests

-- ---- from OAI.Analysis.SegmentLenses.HeadTests ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
# Common finite norming tests and head localization
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

theorem exists_norming_unitBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →L[ℝ] ℝ) :
    ∃ p : E, ‖p‖ ≤ 1 ∧ f p = ‖f‖ := by
  obtain ⟨p, hp, hmax⟩ := (isCompact_closedBall (0 : E) (1 : ℝ)).exists_isMaxOn
    (by exact ⟨0, by simp⟩) f.continuous.continuousOn
  have hpn : ‖p‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hp
  have hpos : 0 ≤ f p := by
    have h := hmax (by simp : (0 : E) ∈ Metric.closedBall 0 1)
    simpa only [Set.mem_ofPred_eq, map_zero] using h
  have hupper : ‖f‖ ≤ f p := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hpos
    intro v hv
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have h := hmax (show -v ∈ Metric.closedBall (0 : E) 1 by
        simp only [Metric.mem_closedBall, dist_zero_right, norm_neg, hv, le_refl])
      change f (-v) ≤ f p at h
      rw [map_neg] at h
      linarith
    · exact hmax (by simpa only [Metric.mem_closedBall, dist_zero_right, hv] using le_rfl)
  have hlower : f p ≤ ‖f‖ := calc
    f p ≤ |f p| := le_abs_self _
    _ ≤ ‖f‖ * ‖p‖ := f.le_opNorm p
    _ ≤ ‖f‖ := mul_le_of_le_one_right (norm_nonneg _) hpn
  exact ⟨p, hpn, le_antisymm hlower hupper⟩

section HeadTests
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

theorem norm_restrictDual_le (H : Finset V) (x : FullDual V) : ‖restrictDual H x‖ ≤ ‖x‖ := by
  have _ := decidableEqV
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  have h := x.le_opNorm (u.val : Primal V)
  change ‖x (u.val : Primal V)‖ ≤ ‖x‖ * ‖u.val‖
  simpa only [UniformSpace.Completion.norm_coe] using h

end HeadTests

section NormingTest
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem norm_restrictDual_eq {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x : FullDual V) (hx : head H x = x) : ‖restrictDual H x‖ = ‖x‖ := by
  apply le_antisymm (norm_restrictDual_le H x)
  apply dual_norm_le x (norm_nonneg (restrictDual H x))
  intro u
  let v : headTestSpace H := ⟨Test.ofFinsupp (u.coeff.filter (· ∈ H)), by
    intro w hw
    exact Finsupp.filter_apply _ _ _ |>.trans (ite_eq_right hw)⟩
  have he : x (u : Primal V) = restrictDual H x v := by
    calc
      x (u : Primal V) = head H x (u : Primal V) := congrArg (fun z : FullDual V => z (u : Primal V)) hx.symm
      _ = x ((Test.ofFinsupp (u.coeff.filter (· ∈ H)) : Test V) : Primal V) := head_pairing H x u
      _ = restrictDual H x v := rfl
  rw [he]
  have h := (restrictDual H x).le_opNorm v
  rw [Real.norm_eq_abs] at h
  exact h.trans (mul_le_mul_of_nonneg_left (norm_headTest_le hH u.coeff) (norm_nonneg (restrictDual H x)))

theorem exists_norming_head {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x : FullDual V) (hx : head H x = x) (hne : x ≠ 0) :
    ∃ p : Test V, p.coeff.support ⊆ H ∧ ‖p‖ = 1 ∧ x (p : Primal V) = ‖x‖ := by
  obtain ⟨p, hp, hpx⟩ := exists_norming_unitBall (restrictDual H x)
  rw [norm_restrictDual_eq hH x hx] at hpx
  change ‖p.val‖ ≤ 1 at hp
  have hs : p.val.coeff.support ⊆ H := by
    intro v hv
    by_contra hn
    exact Finsupp.mem_support_iff.mp hv (p.property v hn)
  have hnorm : ‖p.val‖ = 1 := by
    have h := x.le_opNorm (p.val : Primal V)
    rw [Real.norm_eq_abs, UniformSpace.Completion.norm_coe,
      show x (p.val : Primal V) = ‖x‖ from hpx,
      abs_of_nonneg (norm_nonneg x)] at h
    have hxpos := norm_pos_iff.mpr hne
    apply le_antisymm hp
    nlinarith
  exact ⟨p.val, hs, hnorm, hpx⟩

end NormingTest

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

end FiniteLaw

section ConeReconstruction
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

end ConeReconstruction

end SegmentLenses

end

end OAI

-- ---- platform node ----
open OAI OAI.SegmentLenses
open scoped BigOperators
open Finset
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

theorem solution {H : Finset V} (hH : Ancestral (· ≤ ·) H)
    (x : FullDual V) (hx : head H x = x) (hne : x ≠ 0) :
    ∃ p : Test V, p.coeff.support ⊆ H ∧ ‖p‖ = 1 ∧ x (p : Primal V) = ‖x‖ := by
  first
    | exact OAI.SegmentLenses.exists_norming_head hH x hx hne
    | exact OAI.SegmentLenses.exists_norming_head
    | (apply OAI.SegmentLenses.exists_norming_head <;> assumption)
    | (intros; apply OAI.SegmentLenses.exists_norming_head <;> assumption)
