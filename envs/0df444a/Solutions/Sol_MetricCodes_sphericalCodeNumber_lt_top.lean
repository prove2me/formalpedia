-- Prove2me | solution 1 for MetricCodes.sphericalCodeNumber_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/2771158f-c480-41f4-a65c-2a2660aef2d4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_spherical_dist_sq
import Theorems.Thm_MetricCodes_sphericalCodeNumber_le

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
noncomputable section
open scoped BigOperators InnerProductSpace
open MetricCodes
namespace MetricCodes
theorem _root_.solution {n : ℕ} {s : ℝ}
    (hs : s < 1) : sphericalCodeNumber n s < ⊤ := by
  let ε : NNReal :=
    ⟨Real.sqrt (2 * (1 - s)) / 4, by positivity⟩
  have hε : ε ≠ 0 := by
    apply NNReal.ne_iff.mp
    change Real.sqrt (2 * (1 - s)) / 4 ≠ 0
    positivity
  let S : Set (Ambient n) := Metric.sphere (0 : Ambient n) 1
  have hS : IsCompact S := isCompact_sphere (0 : Ambient n) 1
  obtain ⟨N, hNS, hNfin, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact hε hS
  have hpacking : Metric.packingNumber (2 * ε) S ≤ N.encard :=
    (Metric.packingNumber_two_mul_le_externalCoveringNumber ε S).trans
      hcover.externalCoveringNumber_le_encard
  have hbound : sphericalCodeNumber n s ≤ N.encard := by
    apply sphericalCodeNumber_le
    intro C
    let F : Finset (Ambient n) :=
      C.points.map (Function.Embedding.subtype (fun x : Ambient n => ‖x‖ = 1))
    have hFS : (↑F : Set (Ambient n)) ⊆ S := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      simpa [S, Metric.mem_sphere] using u.property
    have hFsep : Metric.IsSeparated (2 * ε) (↑F : Set (Ambient n)) := by
      intro x hx y hy hxy
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
      have huv : u ≠ v := fun huv => hxy (congrArg Subtype.val huv)
      have hinner : sphericalInner u v ≤ s := C.inner_le hu hv huv
      have hsq : 2 * (1 - s) ≤ dist (u : Ambient n) (v : Ambient n) ^ 2 := by
        rw [dist_eq_norm, spherical_dist_sq]
        nlinarith
      have hsqrt : 0 < Real.sqrt (2 * (1 - s)) := by
        positivity
      have hsqrt_sq : Real.sqrt (2 * (1 - s)) ^ 2 = 2 * (1 - s) :=
        Real.sq_sqrt (by nlinarith)
      have hreal : ((2 * ε : NNReal) : ℝ) <
          dist (u : Ambient n) (v : Ambient n) := by
        change 2 * (Real.sqrt (2 * (1 - s)) / 4) <
          dist (u : Ambient n) (v : Ambient n)
        nlinarith [show 0 ≤ dist (u : Ambient n) (v : Ambient n) from dist_nonneg]
      calc
        (↑(2 * ε) : ENNReal) =
            ENNReal.ofReal (((2 * ε : NNReal) : ℝ)) :=
          ENNReal.coe_nnreal_eq _
        _ < ENNReal.ofReal (dist (u : Ambient n) (v : Ambient n)) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).2 hreal
        _ = edist (u : Ambient n) (v : Ambient n) :=
          (edist_dist _ _).symm
    calc
      (C.points.card : ℕ∞) = (↑F : Set (Ambient n)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_map]
      _ ≤ Metric.packingNumber (2 * ε) S :=
        hFsep.encard_le_packingNumber hFS
      _ ≤ N.encard := hpacking
  exact lt_of_le_of_lt hbound hNfin.encard_lt_top
end MetricCodes
