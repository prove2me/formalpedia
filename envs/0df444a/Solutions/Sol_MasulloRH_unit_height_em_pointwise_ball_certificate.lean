-- Prove2me | solution 1 for MasulloRH.unit_height_em_pointwise_ball_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T02:59:15.801984+00:00
-- url     : https://prove2.me/submissions/7366e8be-7531-45ff-9b08-1831dbabaaa9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_unit_height_em_mesh_covers_logarithmic_edge_and_all_but_finitely_many_points
import Theorems.Thm_MasulloRH_unit_height_interior_order_one_mesh_certificates

open Set MasulloRH.UnitHeightMeshes

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
    ∀ s ∈ R, ∃ p r, cert p r ∧ dist s (center p) < (r : ℝ) := by
  exact MasulloRH.unit_height_em_mesh_covers_logarithmic_edge_and_all_but_finitely_many_points.2.mp
    MasulloRH.unit_height_interior_order_one_mesh_certificates n k
