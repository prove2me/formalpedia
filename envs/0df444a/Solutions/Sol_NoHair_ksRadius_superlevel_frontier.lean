-- Prove2me | solution 1 for NoHair.ksRadius_superlevel_frontier
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T20:03:20.796319+00:00
-- url     : https://prove2.me/submissions/b6198466-463c-4180-9c05-b301f8e28187

import Definitions.Def_NoHair_kerrNewman

open NoHair Set Metric
open scoped Topology

private abbrev Space3 := EuclideanSpace ℝ (Fin 3)

private noncomputable def ellipsoidChart (d b : ℝ) (hd : d ≠ 0) (hb : b ≠ 0) : E4 ≃ₜ ℝ × Space3 where
  toFun x := (x 0, WithLp.toLp 2 ![x 1 / d, x 2 / d, x 3 / b])
  invFun q := WithLp.toLp 2 ![q.1, q.2 0 * d, q.2 1 * d, q.2 2 * b]
  left_inv x := by
    ext i
    fin_cases i <;> simp [PiLp.toLp_apply, hd, hb]
  right_inv q := by
    apply Prod.ext
    · rfl
    · ext i
      fin_cases i <;> simp [PiLp.toLp_apply, hd, hb]
  continuous_toFun := by
    apply Continuous.prodMk
    · fun_prop
    · apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro i
      fin_cases i <;> simp <;> fun_prop
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop

private theorem ellipsoid_compare (a b : ℝ) (hb : 0 < b) (x : E4)
    (d : ℝ) (hd : 0 < d) (hd2 : d ^ 2 = b ^ 2 + a ^ 2) :
    let w := (ellipsoidChart d b hd.ne' hb.ne' x).2
    (b < ksRadius a x ↔ 1 < ‖w‖) ∧ (ksRadius a x = b ↔ ‖w‖ = 1) := by
  let w := (ellipsoidChart d b hd.ne' hb.ne' x).2
  let c := x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 - a ^ 2
  let s := Real.sqrt (c ^ 2 + 4 * a ^ 2 * x 3 ^ 2)
  have hs2 : s ^ 2 = c ^ 2 + 4 * a ^ 2 * x 3 ^ 2 := Real.sq_sqrt (by positivity)
  have habs : |c| ≤ s := calc
    |c| = Real.sqrt (c ^ 2) := (Real.sqrt_sq_eq_abs c).symm
    _ ≤ s := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg (a * x 3)])
  have hp : 0 ≤ (c + s) / 2 := by linarith [neg_abs_le c]
  have hr2 : ksRadius a x ^ 2 = (c + s) / 2 := Real.sq_sqrt hp
  have hneg : (c - s) / 2 ≤ 0 := by linarith [le_abs_self c]
  have hr : 0 ≤ ksRadius a x := Real.sqrt_nonneg _
  have hn : ‖w‖ ^ 2 = (x 1 / d) ^ 2 + (x 2 / d) ^ 2 + (x 3 / b) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    rfl
  have hid : (‖w‖ ^ 2 - 1) * (b ^ 2 * d ^ 2) =
      (ksRadius a x ^ 2 - b ^ 2) * (b ^ 2 - (c - s) / 2) := calc
    _ = (x 1 ^ 2 + x 2 ^ 2) * b ^ 2 + x 3 ^ 2 * d ^ 2 - b ^ 2 * d ^ 2 := by
      rw [hn]
      field_simp [hd.ne', hb.ne'] <;> ring
    _ = _ := by
      rw [hr2, hd2]
      dsimp only [c] at hs2 ⊢
      nlinarith only [hs2]
  have hsign : (‖w‖ - 1) * ((‖w‖ + 1) * (b ^ 2 * d ^ 2)) =
      (ksRadius a x - b) * ((ksRadius a x + b) * (b ^ 2 - (c - s) / 2)) := by
    linear_combination hid
  have hleft : 0 < (‖w‖ + 1) * (b ^ 2 * d ^ 2) := by positivity
  have hgap : 0 < b ^ 2 - (c - s) / 2 := sub_pos.mpr (hneg.trans_lt (sq_pos_of_pos hb))
  have hright : 0 < (ksRadius a x + b) * (b ^ 2 - (c - s) / 2) :=
    mul_pos (add_pos_of_nonneg_of_pos hr hb) hgap
  change (b < ksRadius a x ↔ 1 < ‖w‖) ∧ (ksRadius a x = b ↔ ‖w‖ = 1)
  constructor
  · have h := congrArg (fun v : ℝ => 0 < v) hsign
    simpa only [mul_pos_iff_of_pos_right hleft, mul_pos_iff_of_pos_right hright, sub_pos] using
      (Iff.of_eq h).symm
  · have h := congrArg (fun v : ℝ => v = 0) hsign
    simpa only [mul_eq_zero, hleft.ne', hright.ne', or_false, sub_eq_zero] using (Iff.of_eq h).symm

theorem solution (a b : ℝ) (hb : 0 < b) :
    frontier {x : kerrNewmanSpacetime a | b < ksRadius a x.val} =
        {x : kerrNewmanSpacetime a | ksRadius a x.val = b} ∧
      IsConnected {x : kerrNewmanSpacetime a | ksRadius a x.val = b} := by
  let d := Real.sqrt (b ^ 2 + a ^ 2)
  have hd : 0 < d := Real.sqrt_pos.mpr (by positivity)
  have hd2 : d ^ 2 = b ^ 2 + a ^ 2 := Real.sq_sqrt (by positivity)
  let H := ellipsoidChart d b hd.ne' hb.ne'
  let P : E4 → Space3 := fun x => (H x).2
  let V : Set E4 := {y | b < ksRadius a y}
  let L : Set E4 := {y | ksRadius a y = b}
  have hout : V = P ⁻¹' (closedBall (0 : Space3) 1)ᶜ := by
    ext y
    simpa [V, P, H, Metric.mem_closedBall, dist_zero_right] using (ellipsoid_compare a b hb y d hd hd2).1
  have hlevel : L = P ⁻¹' sphere (0 : Space3) 1 := by
    ext y
    simpa [L, P, H, Metric.mem_sphere, dist_zero_right] using (ellipsoid_compare a b hb y d hd hd2).2
  have op : IsOpenMap P := isOpenMap_snd.comp H.isOpenMap
  have co : Continuous P := continuous_snd.comp H.continuous
  have hfront : frontier V = L := by
    rw [hout, ← op.preimage_frontier_eq_frontier_preimage co, frontier_compl,
      frontier_closedBall (0 : Space3) one_ne_zero, hlevel]
  have hsph : IsConnected (sphere (0 : Space3) 1) := by
    apply isConnected_sphere _ _ zero_le_one
    apply Module.one_lt_rank_of_one_lt_finrank
    rw [finrank_euclideanSpace_fin]
    decide
  have hconn : IsConnected L := by
    have hp : IsConnected ((univ : Set ℝ) ×ˢ sphere (0 : Space3) 1) := isConnected_univ.prod hsph
    have he : P ⁻¹' sphere (0 : Space3) 1 = H ⁻¹' ((univ : Set ℝ) ×ˢ sphere (0 : Space3) 1) := by
      ext x
      simp [P]
    rw [hlevel, he]
    exact H.isConnected_preimage.mpr hp
  let U := kerrNewmanSpacetime a
  have hop : IsOpenMap (Subtype.val : U → E4) := U.isOpen.isOpenMap_subtype_val
  change frontier ((Subtype.val : U → E4) ⁻¹' V) = Subtype.val ⁻¹' L ∧ IsConnected ((Subtype.val : U → E4) ⁻¹' L)
  constructor
  · rw [← hop.preimage_frontier_eq_frontier_preimage continuous_subtype_val, hfront]
  · have him : (Subtype.val : U → E4) '' (Subtype.val ⁻¹' L) = L := by
      apply image_preimage_eq_of_subset
      intro y hy
      exact ⟨⟨y, show 0 < ksRadius a y from (show ksRadius a y = b from hy) ▸ hb⟩, rfl⟩
    have hc : IsConnected ((Subtype.val : U → E4) '' (Subtype.val ⁻¹' L)) := him.symm ▸ hconn
    exact ⟨hc.nonempty.of_image, Topology.IsInducing.subtypeVal.isPreconnected_image.mp hc.isPreconnected⟩
