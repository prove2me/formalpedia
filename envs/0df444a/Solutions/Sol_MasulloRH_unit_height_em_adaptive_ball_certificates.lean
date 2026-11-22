-- Prove2me | solution 1 for MasulloRH.unit_height_em_adaptive_ball_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WalrusPaul
-- created : 2026-11-22T19:06:44.586307+00:00
-- url     : https://prove2.me/submissions/009d6bfd-d07f-40f0-ae4f-16834f3c5b06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_unit_height_em_pointwise_ball_certificate
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Finset.Max

set_option autoImplicit false
open Set

namespace MasulloRH

/-- A pointwise supply of certified balls on a compact set yields one
certified radius per selected center, even if the cover repeats centers. -/
theorem finite_certified_balls {P : Type*} {R : Set ℂ} (hR : IsCompact R)
    (center : P → ℂ) (cert : P → ℚ → Prop)
    (h : ∀ s ∈ R, ∃ p r, cert p r ∧ dist s (center p) < (r : ℝ)) :
    ∃ (points : Finset P) (radius : P → ℚ),
      (∀ p ∈ points, cert p (radius p)) ∧
      ∀ s ∈ R, ∃ p ∈ points, dist s (center p) < (radius p : ℝ) := by
  classical
  let I := {pr : P × ℚ // cert pr.1 pr.2}
  let U (i : I) := Metric.ball (center i.val.1) (i.val.2 : ℝ)
  have cover : R ⊆ ⋃ i, U i := by
    intro s hs
    obtain ⟨p, r, hc, hd⟩ := h s hs
    exact mem_iUnion.mpr ⟨(⟨(p, r), hc⟩ : I), hd⟩
  obtain ⟨t, ht⟩ := hR.elim_finite_subcover U (fun _ => Metric.isOpen_ball) cover
  let points := t.image (fun i => i.val.1)
  have best (p : P) (hp : p ∈ points) :
      ∃ r : ℚ, cert p r ∧ ∀ i ∈ t, i.val.1 = p → i.val.2 ≤ r := by
    obtain ⟨j, hj, hcenter⟩ := Finset.mem_image.mp hp
    let fiber := t.filter (fun i => i.val.1 = p)
    obtain ⟨m, hm, hmax⟩ := fiber.exists_max_image (fun i => i.val.2)
      ⟨j, Finset.mem_filter.mpr ⟨hj, hcenter⟩⟩
    have eqp := (Finset.mem_filter.mp hm).2
    exact ⟨m.val.2, eqp ▸ m.property, fun i hi he =>
      hmax i (Finset.mem_filter.mpr ⟨hi, he⟩)⟩
  let radius (p : P) := if hp : p ∈ points then (best p hp).choose else 0
  refine ⟨points, radius, ?_, ?_⟩
  · intro p hp
    simpa only [radius, dif_pos hp] using (best p hp).choose_spec.1
  · intro s hs
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hs)
    obtain ⟨hit, hdist⟩ := mem_iUnion.mp hi
    have hp : i.val.1 ∈ points := Finset.mem_image_of_mem _ hit
    refine ⟨i.val.1, hp, lt_of_lt_of_le (show dist s (center i.val.1) < (i.val.2 : ℝ) from hdist) ?_⟩
    simp only [radius, dif_pos hp]
    exact_mod_cast (best i.val.1 hp).choose_spec.2 i hit rfl

/-- Instantiate the compact-cover argument with the exact numerical margin of
the frontier theorem. Specialize F to ZetaReflection.EMHigh.emFinite. -/
theorem unit_height_cover_of_local (F : ℕ → ℂ → ℕ → ℂ) (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let R := Complex.reProdIm (Icc (1 / 2 + margin) 1)
      (Icc ((100000 : ℝ) + n + margin) ((100000 : ℝ) + n + 1))
    let M : ℚ := 16 * (100003 + n)
    let center (p : ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ)⟩
    let cert (p : ℚ × ℚ) (r : ℚ) := center p ∈ R ∧
      ∃ K N : ℕ, 1 ≤ K ∧ 1 ≤ N ∧
        let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
        ((M * r + err : ℚ) : ℝ) < ‖F K (center p) N‖
    (∀ s ∈ R, ∃ p r, cert p r ∧ dist s (center p) < (r : ℝ)) →
      ∃ (points : Finset (ℚ × ℚ)) (radius : ℚ × ℚ → ℚ),
        (∀ p ∈ points, cert p (radius p)) ∧
        ∀ s ∈ R, ∃ p ∈ points, dist s (center p) < (radius p : ℝ) := by
  dsimp only
  apply finite_certified_balls
  exact isCompact_Icc.reProdIm isCompact_Icc

end MasulloRH

theorem solution (n k : ℕ) :
    let margin : ℝ := 1 / ((k : ℝ) + 3)
    let R := Complex.reProdIm (Icc (1 / 2 + margin) 1)
      (Icc ((100000 : ℝ) + n + margin) ((100000 : ℝ) + n + 1))
    let M : ℚ := 16 * (100003 + n)
    let center (p : ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ)⟩
    let cert (p : ℚ × ℚ) (r : ℚ) := center p ∈ R ∧
      ∃ K N : ℕ, 1 ≤ K ∧ 1 ≤ N ∧
        let err : ℚ := ((100002 + n + 2 * K : ℕ) : ℚ) ^ (2 * K + 1) /
          (3 * 6 ^ (2 * K) * (N : ℚ) ^ (2 * K))
        ((M * r + err : ℚ) : ℝ) < ‖ZetaReflection.EMHigh.emFinite K (center p) N‖
      ∃ (points : Finset (ℚ × ℚ)) (radius : ℚ × ℚ → ℚ),
        (∀ p ∈ points, cert p (radius p)) ∧
        ∀ s ∈ R, ∃ p ∈ points, dist s (center p) < (radius p : ℝ) := by
  exact MasulloRH.unit_height_cover_of_local ZetaReflection.EMHigh.emFinite n k
    (MasulloRH.unit_height_em_pointwise_ball_certificate n k)
