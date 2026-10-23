-- Prove2me | solution 1 for InertialAVD.Traj.theorem_2_16
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T08:37:21.15564+00:00
-- url     : https://prove2.me/submissions/f2ef3a2b-eb2b-42d2-a668-ba785ab5891d

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting
open Filter Topology Set
open InertialAVD.Traj

namespace InertialTrajectoryProof
end InertialTrajectoryProof

open Filter Topology Set
open InertialAVD.Traj

namespace InertialTrajectoryProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem gradient_support (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦC1 : ContDiff ℝ 1 Φ) (x y : H) :
    inner ℝ (gradient Φ x) (y - x) ≤ Φ y - Φ x := by
  let a : ℝ →ᵃ[ℝ] H :=
    { toFun := fun t => x + t • (y - x)
      linear := (LinearMap.id : ℝ →ₗ[ℝ] ℝ).smulRight (y - x)
      map_vadd' := by intro p v; simp only [vadd_eq_add, LinearMap.smulRight_apply,
        LinearMap.id_coe, id_eq, add_smul]; abel }
  have hc : ConvexOn ℝ Set.univ (fun t : ℝ => Φ (x + t • (y - x))) := by
    simpa [a, Function.comp_def] using hΦconv.comp_affineMap a
  have ha : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hd := ((hΦC1.differentiable one_ne_zero (x + (0 : ℝ) • (y - x))).hasFDerivAt).comp_hasDerivAt 0 ha
  have hd' : HasDerivAt (fun t : ℝ => Φ (x + t • (y - x)))
      (inner ℝ (gradient Φ x) (y - x)) 0 := by
    simpa [Function.comp_def] using hd
  have hh := hc.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) (by norm_num) hd'
  simpa [slope_def_field] using hh

theorem gradient_gap (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦC1 : ContDiff ℝ 1 Φ) (x z : H) :
    Φ x - Φ z ≤ inner ℝ (x - z) (gradient Φ x) := by
  have h := gradient_support Φ hΦconv hΦC1 x z
  rw [inner_sub_right, ← real_inner_comm (gradient Φ x) z,
    ← real_inner_comm (gradient Φ x) x] at h
  rw [inner_sub_left]
  linarith

end InertialTrajectoryProof

open Filter Topology Set
open InertialAVD.Traj

namespace InertialTrajectoryProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem anchor_derivative (Φ : H → ℝ) (α t₀ : ℝ) (x v : ℝ → H)
    (hsol : IsSolution Φ α t₀ x v) (z : H) (t : ℝ) (ht : t₀ ≤ t) :
    HasDerivWithinAt (anchorDist x z) (inner ℝ (x t - z) (v t)) (Set.Ici t₀) t := by
  convert! (((hsol.2 t ht).1.sub_const z).norm_sq.const_mul (1 / 2 : ℝ)) using 1
  ring

theorem energy_derivative (Φ : H → ℝ) (hΦC1 : ContDiff ℝ 1 Φ)
    (α t₀ : ℝ) (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v)
    (z : H) (lam : ℝ) (t : ℝ) (ht : t₀ ≤ t) :
    HasDerivWithinAt (anchoredEnergy Φ x v lam (lam * (α - lam - 1)) z)
      (2 * t * (Φ (x t) - Φ z) - lam * t * inner ℝ (x t - z) (gradient Φ (x t)) -
        (α - lam - 1) * t * ‖v t‖ ^ 2) (Set.Ici t₀) t := by
  have hx := (hsol.2 t ht).1
  have hv := (hsol.2 t ht).2
  have hi : HasDerivWithinAt (fun s : ℝ => s) 1 (Set.Ici t₀) t :=
    (hasDerivAt_id t).hasDerivWithinAt
  have hp := ((hΦC1.differentiable one_ne_zero (x t)).hasFDerivAt).comp_hasDerivWithinAt t hx
  have hp' : HasDerivWithinAt (fun s => Φ (x s))
      (inner ℝ (gradient Φ (x t)) (v t)) (Set.Ici t₀) t := by
    simpa [Function.comp_def] using hp
  have hb := ((hx.sub_const z).const_smul lam).add (hi.smul hv)
  have he := ((hi.pow 2).mul (hp'.sub_const (Φ z))).add
    (hb.norm_sq.const_mul (1 / 2 : ℝ))
  have he' := he.add (((hx.sub_const z).norm_sq).const_mul (lam * (α - lam - 1) / 2))
  have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hsol.1 ht)
  convert! he' using 1
  dsimp only [Pi.add_apply, Pi.smul_apply, Pi.smul_apply', Pi.pow_apply, Pi.mul_apply]
  simp only [Nat.cast_ofNat, mul_one, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, one_smul, real_inner_self_eq_norm_sq]
  rw [← real_inner_comm (gradient Φ (x t)) (v t)]
  field_simp [ht0]
  ring

omit [CompleteSpace H] in
theorem energy_nonneg (Φ : H → ℝ) (x v : ℝ → H) (lam ξ : ℝ) (z : H)
    (hz : ∀ y : H, Φ z ≤ Φ y) (hξ : 0 ≤ ξ) (t : ℝ) :
    0 ≤ anchoredEnergy Φ x v lam ξ z t := by
  unfold anchoredEnergy
  exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg t) (sub_nonneg.mpr (hz _)))
    (mul_nonneg (by norm_num) (sq_nonneg _))) (mul_nonneg (div_nonneg hξ (by norm_num)) (sq_nonneg _))

theorem energy_antitone (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦC1 : ContDiff ℝ 1 Φ) (α t₀ : ℝ) (x v : ℝ → H)
    (hsol : IsSolution Φ α t₀ x v) (z : H) (hz : ∀ y : H, Φ z ≤ Φ y)
    (lam : ℝ) (hlam : 2 ≤ lam) (hupper : lam ≤ α - 1) :
    AntitoneOn (anchoredEnergy Φ x v lam (lam * (α - lam - 1)) z) (Set.Ici t₀) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici t₀)
      (fun t ht => (energy_derivative Φ hΦC1 α t₀ x v hsol z lam t ht).continuousWithinAt)
      (fun t ht => (energy_derivative Φ hΦC1 α t₀ x v hsol z lam t
        (interior_subset ht)).mono interior_subset)
  intro t ht
  have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le hsol.1 (interior_subset ht))
  have hg := gradient_gap Φ hΦconv hΦC1 (x t) z
  have hgap : 0 ≤ Φ (x t) - Φ z := sub_nonneg.mpr (hz _)
  have hmul := mul_le_mul_of_nonneg_left hg (mul_nonneg (by linarith : 0 ≤ lam) ht0)
  have hrest : 0 ≤ (α - lam - 1) * t * ‖v t‖ ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) ht0) (sq_nonneg _)
  have hcoef : 0 ≤ (lam - 2) * t * (Φ (x t) - Φ z) :=
    mul_nonneg (mul_nonneg (by linarith) ht0) hgap
  nlinarith

omit [CompleteSpace H] in
theorem energy_difference (Φ : H → ℝ) (α : ℝ) (x v : ℝ → H) (z : H) (t : ℝ) :
    anchoredEnergy Φ x v (α - 1) 0 z t - anchoredEnergy Φ x v 2 (2 * (α - 3)) z t =
      (α - 3) * (t * inner ℝ (x t - z) (v t) + (α - 1) * anchorDist x z t) := by
  simp only [anchoredEnergy, anchorDist, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  ring

end InertialTrajectoryProof

open Filter Topology Set
open InertialAVD.Traj

namespace InertialTrajectoryProof
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

private theorem antitone_tail_limit (f : ℝ → ℝ) (a : ℝ)
    (ha : AntitoneOn f (Set.Ici a)) (hn : ∀ t, a ≤ t → 0 ≤ f t) :
    ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  let g : ℝ → ℝ := fun t => f (max a t)
  have hm : Antitone g := by
    intro t u htu
    exact ha (show max a t ∈ Set.Ici a from le_max_left a t)
      (show max a u ∈ Set.Ici a from le_max_left a u) (max_le_max_left a htu)
  have hb : BddBelow (Set.range g) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, rfl⟩
    exact hn _ (le_max_left _ _)
  refine ⟨⨅ t, g t, (tendsto_atTop_ciInf hm hb).congr' ?_⟩
  filter_upwards [eventually_ge_atTop a] with t ht
  simp [g, max_eq_right ht]

theorem energy_limits (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦC1 : ContDiff ℝ 1 Φ) (α t₀ : ℝ) (hα : 3 < α)
    (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v) (z : H)
    (hz : ∀ y : H, Φ z ≤ Φ y) :
    ∃ a b : ℝ,
      Tendsto (anchoredEnergy Φ x v 2 (2 * (α - 3)) z) atTop (𝓝 a) ∧
      Tendsto (anchoredEnergy Φ x v (α - 1) 0 z) atTop (𝓝 b) := by
  have h2 : AntitoneOn (anchoredEnergy Φ x v 2 (2 * (α - 3)) z) (Set.Ici t₀) := by
    have he : (2 : ℝ) * (α - 2 - 1) = 2 * (α - 3) := by ring
    simpa only [he] using energy_antitone Φ hΦconv hΦC1 α t₀ x v hsol z hz 2 (by norm_num) (by linarith)
  have hb : AntitoneOn (anchoredEnergy Φ x v (α - 1) 0 z) (Set.Ici t₀) := by
    simpa using energy_antitone Φ hΦconv hΦC1 α t₀ x v hsol z hz (α - 1) (by linarith) le_rfl
  obtain ⟨a, ha⟩ := antitone_tail_limit _ t₀ h2 (fun t _ =>
    energy_nonneg Φ x v 2 (2 * (α - 3)) z hz (by positivity) t)
  obtain ⟨b, hb⟩ := antitone_tail_limit _ t₀ hb (fun t _ =>
    energy_nonneg Φ x v (α - 1) 0 z hz le_rfl t)
  exact ⟨a, b, ha, hb⟩

theorem trajectory_bounded (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦC1 : ContDiff ℝ 1 Φ) (α t₀ : ℝ) (hα : 3 < α)
    (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v) (z : H)
    (hz : ∀ y : H, Φ z ≤ Φ y) :
    ∃ R : ℝ, ∀ t : ℝ, t₀ ≤ t → ‖x t‖ ≤ R := by
  let E := anchoredEnergy Φ x v 2 (2 * (α - 3)) z
  have hδ : 0 < α - 3 := by linarith
  have hm : AntitoneOn E (Set.Ici t₀) := by
    have he : (2 : ℝ) * (α - 2 - 1) = 2 * (α - 3) := by ring
    simpa only [he] using energy_antitone Φ hΦconv hΦC1 α t₀ x v hsol z hz 2 (by norm_num) (by linarith)
  let C := E t₀ / (α - 3)
  have hC : 0 ≤ C := div_nonneg (energy_nonneg Φ x v 2 (2 * (α - 3)) z hz (by positivity) t₀) hδ.le
  refine ⟨C + 1 + ‖z‖, ?_⟩
  intro t ht
  have he := hm (show t₀ ∈ Set.Ici t₀ from le_refl t₀) ht ht
  have hsq : ‖x t - z‖ ^ 2 ≤ C := by
    apply (le_div_iff₀ hδ).mpr
    have hgap := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr (hz (x t)))
    have hnorm := sq_nonneg ‖(2 : ℝ) • (x t - z) + t • v t‖
    dsimp [E, anchoredEnergy] at he ⊢
    nlinarith
  have hr : ‖x t - z‖ ≤ C + 1 := by nlinarith [sq_nonneg (‖x t - z‖ - 1)]
  calc
    ‖x t‖ = ‖(x t - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖x t - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ C + 1 + ‖z‖ := add_le_add hr le_rfl

theorem objective_tendsto (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦC1 : ContDiff ℝ 1 Φ) (α t₀ : ℝ) (hα : 3 < α)
    (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v) (z : H)
    (hz : ∀ y : H, Φ z ≤ Φ y) :
    Tendsto (fun t : ℝ => Φ (x t)) atTop (𝓝 (Φ z)) := by
  let E := anchoredEnergy Φ x v (α - 1) 0 z
  have hm : AntitoneOn E (Set.Ici t₀) := by
    simpa [E] using energy_antitone Φ hΦconv hΦC1 α t₀ x v hsol z hz (α - 1) (by linarith) le_rfl
  have hu : Tendsto (fun t : ℝ => E t₀ / t ^ 2) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.pow 2) :
        Tendsto (fun t : ℝ => E t₀ * (t⁻¹) ^ 2) atTop (𝓝 (E t₀ * (0 : ℝ) ^ 2)))
  have hg : Tendsto (fun t : ℝ => Φ (x t) - Φ z) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · exact Eventually.of_forall (fun t => sub_nonneg.mpr (hz (x t)))
    · filter_upwards [eventually_ge_atTop t₀] with t ht
      have htpos := lt_of_lt_of_le hsol.1 ht
      apply (le_div_iff₀ (sq_pos_of_pos htpos)).mpr
      have he := hm (show t₀ ∈ Set.Ici t₀ from le_refl t₀) ht ht
      have hn := sq_nonneg ‖(α - 1) • (x t - z) + t • v t‖
      dsimp [E, anchoredEnergy] at he ⊢
      nlinarith
  simpa using hg.add_const (Φ z)

end InertialTrajectoryProof

open Filter Topology Set

namespace InertialTrajectoryProof

lemma euler_eventually_lt (a β c : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (h h' : ℝ → ℝ)
    (hh : ∀ t : ℝ, a ≤ t → HasDerivWithinAt h (h' t) (Ici a) t)
    (hq : Tendsto (fun t : ℝ => t * h' t + β * h t) atTop (𝓝 c))
    (b : ℝ) (hb : c / β < b) : ∀ᶠ t in atTop, h t < b := by
  let b' := (c / β + b) / 2
  have hb' : c / β < b' := by dsimp [b']; linarith
  have hb'b : b' < b := by dsimp [b']; linarith
  have hcb : c < β * b' := by
    have := (div_lt_iff₀ hβ).mp hb'
    linarith
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((tendsto_order.mp hq).2 _ hcb)
  let T := max a T₀
  have hTa : a ≤ T := le_max_left _ _
  have hTT : T₀ ≤ T := le_max_right _ _
  let F : ℝ → ℝ := fun t => t ^ β * (h t - b')
  have hF (t : ℝ) (ht : T ≤ t) :
      HasDerivWithinAt F
        (t ^ (β - 1) * (t * h' t + β * h t - β * b')) (Ici T) t := by
    have ht0 : 0 < t := ha.trans_le (hTa.trans ht)
    have hp : HasDerivWithinAt (fun s : ℝ => s ^ β)
        (β * t ^ (β - 1)) (Ici T) t := by
      simpa only [one_mul, id_eq] using
        (hasDerivAt_id t).hasDerivWithinAt.rpow_const (p := β) (Or.inl ht0.ne')
    have hg := ((hh t (hTa.trans ht)).mono (Ici_subset_Ici.mpr hTa)).sub_const b'
    have he : t ^ β = t ^ (β - 1) * t := by
      simpa only [sub_add_cancel] using Real.rpow_add_one ht0.ne' (β - 1)
    convert! hp.mul hg using 1
    rw [he]
    ring
  have hanti : AntitoneOn F (Ici T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici T)
      (fun t ht => (hF t ht).continuousWithinAt)
      (fun t ht => (hF t (interior_subset ht)).mono interior_subset)
      (fun t ht => mul_nonpos_of_nonneg_of_nonpos
        (Real.rpow_nonneg (ha.le.trans (hTa.trans (interior_subset ht))) _)
        (by have := hT₀ t (hTT.trans (interior_subset ht)); linarith))
  have hbound (t : ℝ) (ht : T ≤ t) : h t ≤ b' + F T / t ^ β := by
    have hp : 0 < t ^ β := Real.rpow_pos_of_pos (ha.trans_le (hTa.trans ht)) _
    have hf := hanti (show T ∈ Ici T from mem_Ici.mpr le_rfl) ht ht
    have hd : h t - b' ≤ F T / t ^ β := (le_div_iff₀ hp).mpr (by
      dsimp [F] at hf ⊢
      nlinarith)
    linarith
  have hlim : Tendsto (fun t : ℝ => b' + F T / t ^ β) atTop (𝓝 b') := by
    simpa only [div_eq_mul_inv, Pi.inv_apply, mul_zero, add_zero] using
      tendsto_const_nhds.add ((tendsto_rpow_atTop hβ).inv_tendsto_atTop.const_mul (F T))
  filter_upwards [eventually_ge_atTop T, (tendsto_order.mp hlim).2 b hb'b] with t ht hbnd
  exact (hbound t ht).trans_lt hbnd

theorem euler_limit (a β c : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (h h' : ℝ → ℝ)
    (hh : ∀ t : ℝ, a ≤ t → HasDerivWithinAt h (h' t) (Ici a) t)
    (hq : Tendsto (fun t : ℝ => t * h' t + β * h t) atTop (𝓝 c)) :
    Tendsto h atTop (𝓝 (c / β)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    have hnq : Tendsto (fun t : ℝ => t * (-h' t) + β * (-h t)) atTop (𝓝 (-c)) := by
      convert hq.neg using 1
      ext t
      ring
    have hnb : (-c) / β < -b := by rw [neg_div]; linarith
    filter_upwards [euler_eventually_lt a β (-c) ha hβ (fun t => -h t)
      (fun t => -h' t) (fun t ht => (hh t ht).neg) hnq (-b) hnb] with t ht
    linarith
  · exact euler_eventually_lt a β c ha hβ h h' hh hq

end InertialTrajectoryProof

open Filter Topology Set
open InertialAVD.Traj

namespace InertialTrajectoryProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem distance_limit (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦC1 : ContDiff ℝ 1 Φ) (α t₀ : ℝ) (hα : 3 < α)
    (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v)
    (z : H) (hz : ∀ y : H, Φ z ≤ Φ y) :
    ∃ L : ℝ, Tendsto (anchorDist x z) atTop (𝓝 L) := by
  obtain ⟨a, b, ha, hb⟩ := energy_limits Φ hΦconv hΦC1 α t₀ hα x v hsol z hz
  have hne : α - 3 ≠ 0 := by linarith
  have hq : Tendsto (fun t : ℝ =>
      t * inner ℝ (x t - z) (v t) + (α - 1) * anchorDist x z t)
      atTop (𝓝 ((b - a) / (α - 3))) := by
    convert (hb.sub ha).div_const (α - 3) using 1
    ext t
    rw [energy_difference]
    field_simp [hne]
  refine ⟨((b - a) / (α - 3)) / (α - 1), ?_⟩
  exact euler_limit t₀ (α - 1) ((b - a) / (α - 3)) hsol.1 (by linarith)
    (anchorDist x z) (fun t => inner ℝ (x t - z) (v t))
    (fun t ht => anchor_derivative Φ α t₀ x v hsol z t ht) hq

end InertialTrajectoryProof

open Filter Topology Set

namespace InertialTrajectoryProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable def weakRiesz (q : WeakDual ℝ H) : WeakSpace ℝ H :=
  toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm q.toStrongDual)

theorem continuous_weakRiesz : Continuous (weakRiesz (H := H)) := by
  apply WeakBilin.continuous_of_continuous_eval (topDualPairing ℝ H).flip
  intro f
  change Continuous (fun q : WeakDual ℝ H =>
    f ((InnerProductSpace.toDual ℝ H).symm q.toStrongDual))
  have he (q : WeakDual ℝ H) :
      f ((InnerProductSpace.toDual ℝ H).symm q.toStrongDual) =
        q ((InnerProductSpace.toDual ℝ H).symm f) := by
    rw [← InnerProductSpace.toDual_symm_apply]
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl
  simpa only [he] using WeakDual.eval_continuous ((InnerProductSpace.toDual ℝ H).symm f)

theorem weak_closedBall_isCompact (R : ℝ) :
    IsCompact (toWeakSpace ℝ H '' Metric.closedBall (0 : H) R) := by
  have hc := (WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) R).image
    (continuous_weakRiesz (H := H))
  convert hc using 1
  ext p
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y), ?_, ?_⟩
    · simpa only [mem_preimage, StrongDual.toStrongDual_toWeakDual,
        Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using hy
    · simp [weakRiesz]
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(InnerProductSpace.toDual ℝ H).symm q.toStrongDual, ?_, rfl⟩
    simpa only [mem_preimage, Metric.mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map] using hq

omit [CompleteSpace H] in
theorem weak_eval_continuous (f : H →L[ℝ] ℝ) :
    Continuous (fun p : WeakSpace ℝ H => f ((toWeakSpace ℝ H).symm p)) :=
  WeakBilin.eval_continuous (topDualPairing ℝ H).flip f

theorem weak_inner_continuous (y : H) :
    Continuous (fun p : WeakSpace ℝ H => inner ℝ ((toWeakSpace ℝ H).symm p) y) := by
  simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using
    weak_eval_continuous (InnerProductSpace.toDual ℝ H y)

omit [CompleteSpace H] in
theorem weak_sublevel_isClosed (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦcont : Continuous Φ) (r : ℝ) :
    IsClosed (toWeakSpace ℝ H '' {y : H | Φ y ≤ r}) := by
  have hc : Convex ℝ {y : H | Φ y ≤ r} := by
    simpa only [mem_univ, true_and] using hΦconv.convex_le r
  have hs : IsClosed {y : H | Φ y ≤ r} := isClosed_le hΦcont continuous_const
  have he := hc.toWeakSpace_closure ℝ
  rw [hs.closure_eq] at he
  rw [he]
  exact isClosed_closure

end InertialTrajectoryProof

open Filter Topology Set
open InertialAVD.Traj

namespace InertialTrajectoryProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem weak_cluster_minimizer (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦcont : Continuous Φ) (x : ℝ → H) (z : H) (hz : ∀ y : H, Φ z ≤ Φ y)
    (ho : Tendsto (fun t : ℝ => Φ (x t)) atTop (𝓝 (Φ z)))
    (p : H) (hp : MapClusterPt (toWeakSpace ℝ H p) atTop
      (fun t => toWeakSpace ℝ H (x t))) : ∀ y : H, Φ p ≤ Φ y := by
  intro y
  by_contra hnot
  have hy : Φ y < Φ p := lt_of_not_ge hnot
  let r := (Φ y + Φ p) / 2
  have hzr : Φ z < r := by have := hz y; dsimp [r]; linarith
  have hev : ∀ᶠ t in atTop, toWeakSpace ℝ H (x t) ∈
      toWeakSpace ℝ H '' {y : H | Φ y ≤ r} := by
    filter_upwards [(tendsto_order.mp ho).2 r hzr] with t ht
    exact ⟨x t, ht.le, rfl⟩
  have hm := (weak_sublevel_isClosed Φ hΦconv hΦcont r).mem_of_mapClusterPt hp hev
  obtain ⟨q, hq, he⟩ := hm
  have heq : q = p := (toWeakSpace ℝ H).injective he
  subst q
  dsimp [r] at hq
  linarith

lemma real_cluster_eq_limit {f : ℝ → ℝ} {a b : ℝ}
    (hc : MapClusterPt a atTop f) (hl : Tendsto f atTop (𝓝 b)) : a = b :=
  eq_of_nhds_neBot (hc.clusterPt.mono hl).neBot

theorem weak_cluster_unique (x : ℝ → H) (p q : H)
    (hp : MapClusterPt (toWeakSpace ℝ H p) atTop (fun t => toWeakSpace ℝ H (x t)))
    (hq : MapClusterPt (toWeakSpace ℝ H q) atTop (fun t => toWeakSpace ℝ H (x t)))
    (hdp : ∃ L : ℝ, Tendsto (anchorDist x p) atTop (𝓝 L))
    (hdq : ∃ L : ℝ, Tendsto (anchorDist x q) atTop (𝓝 L)) : p = q := by
  obtain ⟨Lp, hLp⟩ := hdp
  obtain ⟨Lq, hLq⟩ := hdq
  let f : WeakSpace ℝ H → ℝ := fun w => (‖p‖ ^ 2 - ‖q‖ ^ 2) / 2 -
    inner ℝ ((toWeakSpace ℝ H).symm w) (p - q)
  have hf : Continuous f := continuous_const.sub (weak_inner_continuous (p - q))
  have hlim : Tendsto (fun t => f (toWeakSpace ℝ H (x t))) atTop (𝓝 (Lp - Lq)) := by
    convert hLp.sub hLq using 1
    ext t
    simp only [f, LinearEquiv.symm_apply_apply, anchorDist, norm_sub_sq_real,
      inner_sub_right]
    ring
  have hpv := real_cluster_eq_limit (hp.continuousAt_comp hf.continuousAt) hlim
  have hqv := real_cluster_eq_limit (hq.continuousAt_comp hf.continuousAt) hlim
  simp only [f, LinearEquiv.symm_apply_apply, inner_sub_right,
    real_inner_self_eq_norm_sq] at hpv hqv
  rw [← real_inner_comm q p] at hqv
  have hn : ‖p - q‖ ^ 2 = 0 := by
    rw [norm_sub_sq_real]
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

theorem weak_opial_minimizer (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ)
    (hΦcont : Continuous Φ) (x : ℝ → H) (z : H)
    (hz : ∀ y : H, Φ z ≤ Φ y)
    (hb : ∃ R : ℝ, ∀ᶠ t : ℝ in atTop, ‖x t‖ ≤ R)
    (ho : Tendsto (fun t : ℝ => Φ (x t)) atTop (𝓝 (Φ z)))
    (hd : ∀ p : H, (∀ y : H, Φ p ≤ Φ y) →
      ∃ L : ℝ, Tendsto (anchorDist x p) atTop (𝓝 L)) :
    ∃ p : H, (∀ y : H, Φ p ≤ Φ y) ∧ WeakTendstoAtTop x p := by
  obtain ⟨R, hR⟩ := hb
  let K : Set (WeakSpace ℝ H) := toWeakSpace ℝ H '' Metric.closedBall (0 : H) R
  let u : ℝ → WeakSpace ℝ H := fun t => toWeakSpace ℝ H (x t)
  have hc : IsCompact K := weak_closedBall_isCompact R
  have hm : ∀ᶠ t in atTop, u t ∈ K := by
    filter_upwards [hR] with t ht
    exact ⟨x t, by simpa only [Metric.mem_closedBall, dist_zero_right] using ht, rfl⟩
  obtain ⟨p, _, hp⟩ := hc.exists_mapClusterPt_of_frequently hm.frequently
  let p₀ : H := (toWeakSpace ℝ H).symm p
  have hp' : MapClusterPt (toWeakSpace ℝ H p₀) atTop u := by
    simpa only [p₀, LinearEquiv.apply_symm_apply] using hp
  have hmin : ∀ y : H, Φ p₀ ≤ Φ y := weak_cluster_minimizer Φ hΦconv hΦcont x z hz ho p₀ hp'
  have ht : Tendsto u atTop (𝓝 p) := hc.tendsto_nhds_of_unique_mapClusterPt hm (by
    intro q _ hq
    let q₀ : H := (toWeakSpace ℝ H).symm q
    have hq' : MapClusterPt (toWeakSpace ℝ H q₀) atTop u := by
      simpa only [q₀, LinearEquiv.apply_symm_apply] using hq
    have hqmin := weak_cluster_minimizer Φ hΦconv hΦcont x z hz ho q₀ hq'
    have he := weak_cluster_unique x p₀ q₀ hp' hq' (hd p₀ hmin) (hd q₀ hqmin)
    exact (toWeakSpace ℝ H).symm.injective he.symm)
  refine ⟨p₀, hmin, ?_⟩
  intro y
  convert! (weak_inner_continuous y).continuousAt.tendsto.comp ht using 1

end InertialTrajectoryProof

open Filter Topology Set

namespace InertialAVD.Traj

theorem theorem_2_16 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦC1 : ContDiff ℝ 1 Φ)
    (hargmin : ∃ z : H, ∀ y : H, Φ z ≤ Φ y)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v) :
    ∃ xbar : H, (∀ y : H, Φ xbar ≤ Φ y) ∧ WeakTendstoAtTop x xbar := by
  obtain ⟨z, hz⟩ := hargmin
  obtain ⟨R, hR⟩ := InertialTrajectoryProof.trajectory_bounded
    Φ hΦconv hΦC1 α t₀ hα x v hsol z hz
  apply InertialTrajectoryProof.weak_opial_minimizer Φ hΦconv hΦC1.continuous x z hz
  · refine ⟨R, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop t₀] with t ht
    exact hR t ht
  · exact InertialTrajectoryProof.objective_tendsto Φ hΦconv hΦC1 α t₀ hα x v hsol z hz
  · intro p hp
    exact InertialTrajectoryProof.distance_limit Φ hΦconv hΦC1 α t₀ hα x v hsol p hp

end InertialAVD.Traj

open InertialAVD.Traj

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦC1 : ContDiff ℝ 1 Φ)
    (hargmin : ∃ z : H, ∀ y : H, Φ z ≤ Φ y)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v) :
    ∃ xbar : H, (∀ y : H, Φ xbar ≤ Φ y) ∧ WeakTendstoAtTop x xbar := by
  exact InertialAVD.Traj.theorem_2_16 Φ hΦconv hΦC1 hargmin α t₀ hα x v hsol
