-- Prove2me | solution 1 for OAI.Erdos3.exists_realification_finite_bilipschitz_atlas_exp_bound_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:10:58.913427+00:00
-- url     : https://prove2.me/submissions/cd9847c5-83a4-45da-a023-a07b44826dde

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B113
import Definitions.Def_OAIE3v2B119
import Definitions.Def_OAIE3v2B122

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SeparatedCosetBalls
namespace OAI

section

namespace Erdos3

open scoped ENNReal NNReal

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]

theorem dist_le_dist_mul_of_separated_ball (Γ : Subgroup G) (z : G) (R : ℝ)
    (hsep : ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ))
    {x y : G} (hx : dist x z ≤ R) (hy : dist y z ≤ R) (γ : Γ) :
    dist x y ≤ dist x (y * γ) := by
  by_cases hγ : (γ : G) = 1
  · simp only [hγ, mul_one, le_refl]
  · have hs := hsep γ γ.property hγ
    have hchain : dist z (z * γ) ≤ dist z x + dist x (y * γ) + dist (y * γ) (z * γ) :=
      (dist_triangle z x (z * γ)).trans (by linarith [dist_triangle x (y * γ) (z * γ)])
    rw [dist_mul_right] at hchain
    have hxy := dist_triangle x z y
    rw [dist_comm z x] at hchain
    rw [dist_comm z y] at hxy
    linarith

theorem rightCosetEDist_eq_edist_of_separated_ball (Γ : Subgroup G) (z : G) (R : ℝ)
    (hsep : ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ))
    {x y : G} (hx : dist x z ≤ R) (hy : dist y z ≤ R) :
    rightCosetEDist Γ x y = edist x y := by
  apply le_antisymm (rightCosetEDist_le Γ x y)
  apply le_iInf
  intro γ
  simp only [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_le_dist_mul_of_separated_ball Γ z R hsep hx hy γ)

omit [IsIsometricSMul Gᵐᵒᵖ G] in
theorem separated_ball_of_lipschitz_left (Γ : Subgroup G) {δ R : ℝ} {C : ℝ≥0}
    (hC : 0 < C) (hgap : ∀ γ ∈ Γ, γ ≠ 1 → δ ≤ dist 1 γ)
    (hR : 4 * R * C ≤ δ) (z : G) (hleft : LipschitzWith C (fun x => z⁻¹ * x)) :
    ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ) := by
  intro γ hγ hne
  have hLip : dist 1 γ ≤ (C : ℝ) * dist z (z * γ) := by
    simpa only [inv_mul_cancel, inv_mul_cancel_left] using hleft.dist_le_mul z (z * γ)
  have hC' : (0 : ℝ) < C := hC
  have hg := hgap γ hγ hne
  nlinarith

variable [IsTopologicalGroup G]

theorem quotient_dist_eq_of_separated_ball (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G))
    (z : G) (R : ℝ) (hsep : ∀ γ ∈ Γ, γ ≠ 1 → 4 * R ≤ dist z (z * γ)) :
    letI := rightCosetMetricSpace Γ hΓ
    ∀ {x y : G}, dist x z ≤ R → dist y z ≤ R →
      dist (QuotientGroup.mk x : G ⧸ Γ) (QuotientGroup.mk y) = dist x y := by
  let := rightCosetMetricSpace Γ hΓ
  intro x y hx hy
  have h : edist (QuotientGroup.mk x : G ⧸ Γ) (QuotientGroup.mk y) = edist x y :=
    rightCosetEDist_eq_edist_of_separated_ball Γ z R hsep hx hy
  simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using congrArg ENNReal.toReal h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MetricOpenCharts
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_openPartialHomeomorph_of_metric_bounds
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Nonempty X]
    (f : X → Y) (hf : Continuous f) (ho : IsOpenMap f) (U : Set X) (hU : IsOpen U) (K : ℝ≥0)
    (hupper : ∀ x ∈ U, ∀ y ∈ U, dist (f x) (f y) ≤ K * dist x y)
    (hlower : ∀ x ∈ U, ∀ y ∈ U, dist x y ≤ K * dist (f x) (f y)) :
    ∃ e : OpenPartialHomeomorph X Y, (∀ x, e x = f x) ∧ e.source = U ∧ e.target = f '' U ∧
      LipschitzOnWith K e e.source ∧ LipschitzOnWith K e.symm e.target := by
  have hinj : Set.InjOn f U := by
    intro x hx y hy hxy
    apply dist_eq_zero.mp
    exact le_antisymm (by simpa only [hxy, dist_self, mul_zero] using hlower x hx y hy) dist_nonneg
  let e := OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv f U) hf.continuousOn ho hU
  refine ⟨e, fun _ => rfl, rfl, rfl, ?_, ?_⟩
  · exact LipschitzOnWith.of_dist_le_mul hupper
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have h := hlower (e.symm x) (e.map_target hx) (e.symm y) (e.map_target hy)
    change dist (e.symm x) (e.symm y) ≤ K * dist (e (e.symm x)) (e (e.symm y)) at h
    simpa only [e.right_inv hx, e.right_inv hy] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem boxCoverCount_le_exp (C d : ℕ) (hC : 2 ≤ C) (K : ℝ≥0) {B ε p : ℝ}
    (hB0 : 0 ≤ B) (hε : 0 < ε) (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p)
    (hB : B ≤ Real.exp ((p + C) ^ C)) (hK : (K : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hεinv : 1 / ε ≤ Real.exp ((p + C) ^ C)) :
    (((boxCoverMeshCount B K ε + 1) ^ d : ℕ) : ℝ) ≤
      Real.exp ((p + (C + 5)) ^ (C + 5)) := by
  let t : ℝ := p + (C + 5 : ℕ)
  have ht : 5 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have ht1 : 1 ≤ t := by linarith
  have hpt : p ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have hq : (p + C) ^ C ≤ t ^ C :=
    pow_le_pow_left₀ (by positivity) (by dsimp [t]; push_cast; linarith) C
  have hfactor : 3 * (p + C) ^ C + 4 ≤ t ^ (C + 2) := by
    have hpow : 1 ≤ t ^ C := one_le_pow₀ ht1
    have hsquare : 7 ≤ t ^ 2 := by nlinarith
    calc
      _ ≤ 7 * t ^ C := by linarith
      _ ≤ t ^ 2 * t ^ C := mul_le_mul_of_nonneg_right hsquare (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hmesh := boxCoverMeshCount_add_one_le_exp K hB0 hε (by positivity) hB hK hεinv
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (3 * (p + C) ^ C + 4)) ^ d := pow_le_pow_left₀ (by positivity) hmesh d
    _ = Real.exp ((d : ℝ) * (3 * (p + C) ^ C + 4)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (t * t ^ (C + 2)) := Real.exp_le_exp.mpr
      (mul_le_mul (hd.trans hpt) hfactor (by positivity) (by linarith))
    _ = Real.exp (t ^ (C + 3)) := by rw [show C + 3 = (C + 2) + 1 by omega, pow_succ' t (C + 2)]
    _ ≤ Real.exp (t ^ (C + 5)) := Real.exp_le_exp.mpr (pow_le_pow_right₀ ht1 (by omega))
    _ = _ := by simp [t]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem metricPartition_constant_power_budget (C n : ℕ) (hC : 2 ≤ C) (r : ℝ≥0) {p : ℝ}
    (hp : 0 ≤ p) (hn : (n : ℝ) ≤ Real.exp ((p + C) ^ C))
    (hr : 1 / (r : ℝ) ≤ Real.exp ((p + C) ^ C)) :
    (((2 * n + 1 : ℝ≥0) / r : ℝ≥0) : ℝ) ≤ Real.exp ((p + (C + 3)) ^ (C + 3)) := by
  apply (metricPartition_constant_le_exp n r (by positivity) hn hr).trans
  apply Real.exp_le_exp.mpr
  let t : ℝ := p + (C + 3 : ℕ)
  have ht : 5 ≤ t := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    push_cast
    linarith
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (by linarith)
  have hq : (p + C) ^ C ≤ t ^ C :=
    pow_le_pow_left₀ (by positivity) (by dsimp [t]; push_cast; linarith) C
  calc
    _ ≤ 4 * t ^ C := by linarith
    _ ≤ t * t ^ C := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = t ^ (C + 1) := (pow_succ' t C).symm
    _ ≤ t ^ (C + 3) := pow_le_pow_right₀ (by linarith) (by omega)
    _ = _ := by simp [t]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dist_coordinates_le_bchInverseBoxConstant
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (B : ℝ≥0) (hB : 1 ≤ B) (g h : NilpotentLieBCHGroup L s hnil)
    (hg : ∀ i, |e.repr g.coord i| ≤ B) (hh : ∀ i, |e.repr h.coord i| ≤ B) :
    letI := rightMetricSpace (hnil := hnil) e
    dist (basisHomeomorph e g) (basisHomeomorph e h) ≤
      bchInverseBoxConstant s (Fintype.card ι) H B * dist g h := by
  let := rightMetricSpace (hnil := hnil) e
  let A := bchBoxCoordinateBound s (Fintype.card ι) H B
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  have hA : 0 ≤ A := bchBoxCoordinateBound_nonneg _ _ _ B.coe_nonneg
  change dist (basisHomeomorph e g) (basisHomeomorph e h) ≤
    (A + 2 * (B : ℝ)) * (C : ℝ) * dist g h
  by_cases hnear : (C : ℝ) * dist g h < 1
  · let z := h * g⁻¹
    have hdist : dist 1 z = dist g h := by
      simpa only [mul_inv_cancel] using (rightMetricSpace_isometry_mul_right e g⁻¹).dist_eq g h
    have hz : ‖basisHomeomorph e z‖ ≤ (C : ℝ) * dist g h := by
      have hn : (C : ℝ) * dist 1 z < (1 : ℝ≥0) := by simpa only [hdist, NNReal.coe_one] using hnear
      simpa only [hdist] using norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl z hn
    have hzbox : ∀ i, |basisHomeomorph e z i| ≤ B := by
      intro i
      have hi : |basisHomeomorph e z i| ≤ ‖basisHomeomorph e z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (basisHomeomorph e z) i
      exact ((hi.trans hz).trans hnear.le).trans hB
    have hzero : basisHomeomorph (hnil := hnil) e 1 = 0 := by
      simp only [basisHomeomorph_apply, coord_one, map_zero]
    have hRzero : rightTranslate e g 0 = basisHomeomorph e g := by
      rw [← hzero, rightTranslate_coordinates, one_mul]
    have hzg : z * g = h := by simp only [z, inv_mul_cancel_right]
    have hLip := (lipschitzOn_rightTranslate_box e c hstructure hc g B hB hg).dist_le_mul
      (basisHomeomorph e z) hzbox 0
      (show ∀ i, |(0 : ι → ℝ) i| ≤ (B : ℝ) by simpa only [Pi.zero_apply, abs_zero] using fun _ : ι => B.coe_nonneg)
    have hfirst : dist (basisHomeomorph e g) (basisHomeomorph e h) ≤ A * ‖basisHomeomorph e z‖ := by
      rw [rightTranslate_coordinates, hzg, hRzero, dist_zero_right] at hLip
      simpa only [NNReal.toReal, dist_comm, A] using hLip
    calc
      _ ≤ A * ‖basisHomeomorph e z‖ := hfirst
      _ ≤ A * ((C : ℝ) * dist g h) := mul_le_mul_of_nonneg_left hz hA
      _ ≤ (A + 2 * (B : ℝ)) * ((C : ℝ) * dist g h) :=
        mul_le_mul_of_nonneg_right (by linarith [B.coe_nonneg]) (by positivity)
      _ = _ := by ring
  · have hdist : dist (basisHomeomorph e g) (basisHomeomorph e h) ≤ 2 * (B : ℝ) := by
      apply (dist_pi_le_iff (by positivity)).mpr
      intro i
      change |e.repr g.coord i - e.repr h.coord i| ≤ _
      exact (abs_sub _ _).trans (by linarith [hg i, hh i])
    calc
      _ ≤ 2 * (B : ℝ) := hdist
      _ ≤ 2 * (B : ℝ) * ((C : ℝ) * dist g h) :=
        le_mul_of_one_le_right (by positivity) (le_of_not_gt hnear)
      _ ≤ (A + 2 * (B : ℝ)) * ((C : ℝ) * dist g h) := by gcongr; linarith
      _ = _ := by ring

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

theorem bchLatticeSeparationRadius_pos (s d H l : ℕ) : 0 < bchLatticeSeparationRadius s d H l := by
  have hC : (0 : ℝ) < bchLogMetricConstant s d H 1 := bchLogMetricConstant_pos _ _ _ _
  unfold bchLatticeSeparationRadius
  positivity

namespace NilpotentLieBCHGroup

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem eq_one_of_subgroup_of_dist_lt (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l)
    (γ : NilpotentLieBCHGroup L s hnil) (hγ : γ ∈ Γ) :
    letI := rightMetricSpace (hnil := hnil) e
    dist 1 γ < bchLatticeSeparationRadius s (Fintype.card ι) H l → γ = 1 := by
  let := rightMetricSpace (hnil := hnil) e
  intro hsmall
  let C := bchLogMetricConstant s (Fintype.card ι) H 1
  have hC : (0 : ℝ) < C := bchLogMetricConstant_pos _ _ _ _
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have hscaled : (C : ℝ) * dist 1 γ < 1 / ((l : ℝ) + 1) := by
    have h := (lt_div_iff₀ hC).mp hsmall
    simpa only [mul_comm] using h
  have hunit : 1 / ((l : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hn := norm_coordinates_le_of_near_one e c hstructure hc 1 le_rfl γ (hscaled.trans_le hunit)
  apply eq_one_of_subgroup_grid_of_small_coordinates e Γ l hl hgrid γ hγ
  intro i
  have hi : |e.repr γ.coord i| ≤ ‖basisHomeomorph e γ‖ := by
    simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs] using
      norm_le_pi_norm (basisHomeomorph e γ) i
  exact ((hi.trans hn).trans_lt hscaled).trans (one_div_lt_one_div_of_lt hl' (by linarith))

theorem latticeSeparationRadius_le_dist (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l)
    (γ : NilpotentLieBCHGroup L s hnil) (hγ : γ ∈ Γ) (hne : γ ≠ 1) :
    letI := rightMetricSpace (hnil := hnil) e
    bchLatticeSeparationRadius s (Fintype.card ι) H l ≤ dist 1 γ := by
  let := rightMetricSpace (hnil := hnil) e
  by_contra! h
  exact hne (eq_one_of_subgroup_of_dist_lt e c hstructure hc Γ l hl hgrid γ hγ h)

end NilpotentLieBCHGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_dist_eq_on_ball_of_lattice_grid
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ (C : ℝ≥0), 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z⁻¹ * x) →
      letI := quotientMetricSpace e Γ hΓ
      ∀ {x y : NilpotentLieBCHGroup L s hnil},
        dist x z ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) →
        dist y z ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) →
        dist (QuotientGroup.mk x : _ ⧸ Γ) (QuotientGroup.mk y) = dist x y := by
  let : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  let := rightMetricSpace (hnil := hnil) e
  let := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  intro C hC z hleft
  have hC' : (0 : ℝ) < C := hC
  have hgap := fun γ hγ hne => latticeSeparationRadius_le_dist e c hstructure hc Γ l hl hgrid γ hγ hne
  apply quotient_dist_eq_of_separated_ball Γ hΓ z _
  apply separated_ball_of_lipschitz_left Γ hC hgap ?_ z hleft
  have heq : 4 * (bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * (C : ℝ))) * C =
      bchLatticeSeparationRadius s (Fintype.card ι) H l := by
    field_simp
  exact heq.le

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSmoothPartitionBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_bch_partition_input_exp_bound (s a C₀ : ℕ) (hC₀ : 2 ≤ C₀) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      let B : ℝ≥0 := ⟨Real.exp ((p + C₀) ^ C₀), Real.exp_nonneg _⟩
      (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (bchBoxMetricConstant s d H B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      Real.exp ((p + 2) ^ a) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C₁, hC₁, hchart⟩ := exists_bchBoxMetricConstant_exp_bound s C₀
  let C := C₀ + C₁ + a + 4
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C, hC, ?_⟩
  intro d H p hp hd hH
  dsimp only
  have hBp := shifted_power_self_mono (C := C₀) (D := C) hp
    (by omega) (by dsimp [C]; omega)
  refine ⟨Real.exp_le_exp.mpr hBp, ?_, ?_⟩
  · have hKr := hchart d H ⟨Real.exp ((p + C₀) ^ C₀), Real.exp_nonneg _⟩ (p + C₀)
      (by positivity) (hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) C₀]))
      (hH.trans (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) C₀])))
      (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) C₀))
    apply hKr.trans
    apply Real.exp_le_exp.mpr
    have hbase : p + C₀ + C₁ ≤ p + C := by
      have h : (C₀ : ℝ) + C₁ ≤ C := by
        exact_mod_cast (show C₀ + C₁ ≤ C by dsimp [C]; omega)
      linarith
    apply (pow_le_pow_left₀ (by positivity) hbase C₁).trans
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)
  · apply Real.exp_le_exp.mpr
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    apply (pow_le_pow_left₀ (by linarith) (show p + 2 ≤ p + C by linarith) a).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)

end Erdos3

end

section

namespace Erdos3

theorem inverse_radius_product_exp_bound {A l q : ℝ} (hA : 0 ≤ A)
    (hq : 0 ≤ q) (hAq : A ≤ Real.exp q) (hlq : l ≤ Real.exp q) :
    4 * (l + 1) * (A + 1) ≤ Real.exp (2 * q + 16) := by
  have h1 := Real.one_le_exp hq
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  calc
    _ ≤ 4 * (2 * Real.exp q) * (2 * Real.exp q) := by gcongr <;> linarith
    _ = 16 * Real.exp (2 * q) := by rw [show 2 * q = q + q by ring, Real.exp_add]; ring
    _ ≤ Real.exp 16 * Real.exp (2 * q) := mul_le_mul_of_nonneg_right h16 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeMetricGapBudget
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem exists_bchLatticeSeparationRadius_inv_exp_bound (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H l : ℕ) (p : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      1 / bchLatticeSeparationRadius s d H l ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hmetric⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  refine ⟨C + 5, by omega, ?_⟩
  intro d H l p hp hd hH hl
  have hunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
    simpa only [NNReal.coe_one, pow_zero] using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  have hA := bchBoxCoordinateBound_nonneg s d H (B := 1) (by norm_num)
  have hAq := (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H 1).trans
    (hmetric d H 1 p hp hd hH hunit)
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hpq : p ≤ (p + C) ^ C := by
    apply (show p ≤ p + C by linarith).trans
    simpa only [pow_one] using
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + C) (by omega : 1 ≤ C)
  have hprod := inverse_radius_product_exp_bound hA (by positivity : 0 ≤ (p + C) ^ C)
    hAq (hl.trans (Real.exp_le_exp.mpr hpq))
  calc
    1 / bchLatticeSeparationRadius s d H l =
        ((l : ℝ) + 1) * (bchBoxCoordinateBound s d H 1 + 1) := by
      simp only [bchLatticeSeparationRadius, bchLogMetricConstant, NNReal.toReal]
      field_simp
      norm_num
    _ ≤ 4 * ((l : ℝ) + 1) * (bchBoxCoordinateBound s d H 1 + 1) := by
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ l + 1 by positivity) (by linarith : 0 ≤ bchBoxCoordinateBound s d H 1 + 1)]
    _ ≤ Real.exp (2 * (p + C) ^ C + 16) := hprod
    _ ≤ _ := Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp C hC)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuotientCoordinateRadius
namespace OAI

section

namespace Erdos3

theorem quotientCoordinateRadius_pos {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    0 < quotientCoordinateRadius δ K d := by
  unfold quotientCoordinateRadius
  positivity

theorem quotientCoordinateRadius_le_one {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    quotientCoordinateRadius δ K d ≤ 1 := by
  unfold quotientCoordinateRadius
  apply (div_le_one (by positivity)).mpr
  nlinarith [sq_nonneg K, Nat.cast_nonneg (α := ℝ) d,
    mul_nonneg (sq_nonneg K) (show (0 : ℝ) ≤ d + 1 by positivity)]

theorem quotientCoordinateRadius_small {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    4 * K ^ 2 * (d + 1) * quotientCoordinateRadius δ K d ≤ δ := by
  unfold quotientCoordinateRadius
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg δ]

theorem quotientCoordinateRadius_inverse {δ K : ℝ} (hδ : 0 < δ) (d : ℕ) :
    1 / quotientCoordinateRadius δ K d = 1 + 4 * K ^ 2 * (d + 1) * (1 / δ) := by
  unfold quotientCoordinateRadius
  field_simp

theorem quotientCoordinateRadius_inverse_power_budget (A B : ℕ) (hA : 2 ≤ A) (hB : 2 ≤ B)
    {δ K p : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K) (hp : 0 ≤ p) (d : ℕ) (hd : (d : ℝ) ≤ p)
    (hδp : 1 / δ ≤ Real.exp ((p + A) ^ A)) (hKp : K ≤ Real.exp ((p + B) ^ B)) :
    1 / quotientCoordinateRadius δ K d ≤ Real.exp ((p + (A + B + 3 : ℕ)) ^ (A + B + 3)) := by
  let C := A + B
  let q := (p + C) ^ C
  have hC : 2 ≤ C := by dsimp [C]; omega
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqδ : 1 / δ ≤ Real.exp q := hδp.trans (Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := A) (D := C) hp (by omega) (by dsimp [C]; omega)))
  have hqK : K ≤ Real.exp q := hKp.trans (Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := B) (D := C) hp (by omega) (by dsimp [C]; omega)))
  have hpq : p + 1 ≤ q := by
    simpa only [Nat.cast_one, pow_one] using
      shifted_power_self_mono (C := 1) (D := C) hp le_rfl (by omega)
  have hdim : (d : ℝ) + 1 ≤ Real.exp q := by linarith [Real.add_one_le_exp q]
  have hproduct : K ^ 2 * ((d : ℝ) + 1) * (1 / δ) ≤ Real.exp (4 * q) := by
    calc
      _ ≤ (Real.exp q) ^ 2 * Real.exp q * Real.exp q := by gcongr
      _ = (Real.exp q) ^ 4 := by ring
      _ = _ := (Real.exp_nat_mul q 4).symm
  have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hbasic : 1 / quotientCoordinateRadius δ K d ≤ Real.exp (4 * q + 4) := by
    rw [quotientCoordinateRadius_inverse hδ]
    calc
      _ ≤ 5 * Real.exp (4 * q) := by nlinarith [Real.one_le_exp (show 0 ≤ 4 * q by positivity)]
      _ ≤ Real.exp 4 * Real.exp (4 * q) := mul_le_mul_of_nonneg_right hfive (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply hbasic.trans
  apply Real.exp_le_exp.mpr
  let t : ℝ := p + (C + 3 : ℕ)
  have ht : 5 ≤ t := by
    have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
    dsimp [t]
    push_cast
    linarith
  have hpow : 1 ≤ t ^ C := one_le_pow₀ (by linarith)
  have hqt : q ≤ t ^ C := by
    apply pow_le_pow_left₀ (by positivity)
    dsimp [t]
    push_cast
    linarith
  calc
    4 * q + 4 ≤ 8 * t ^ C := by linarith
    _ ≤ t ^ 2 * t ^ C := mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = t ^ (C + 2) := by rw [← pow_add, Nat.add_comm]
    _ ≤ t ^ (C + 3) := pow_le_pow_right₀ (by linarith) (by omega)

theorem product_two_power_bounds (A : ℕ) (hA : 2 ≤ A) {x y p : ℝ}
    (hy : 0 ≤ y) (hp : 0 ≤ p)
    (hx : x ≤ Real.exp ((p + A) ^ A)) (hyb : y ≤ Real.exp ((p + A) ^ A)) :
    x * y ≤ Real.exp ((p + (A + 5 : ℕ)) ^ (A + 5)) := by
  calc
    x * y ≤ Real.exp ((p + A) ^ A) * Real.exp ((p + A) ^ A) :=
      mul_le_mul hx hyb hy (Real.exp_nonneg _)
    _ = Real.exp (2 * (p + A) ^ A) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (2 * (p + A) ^ A + 16) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := Real.exp_le_exp.mpr (enlarged_power_dominates_twice_add_sixteen hp A hA)

theorem quotient_chart_parameter_budget (A B E F : ℕ)
    (hA : 2 ≤ A) (hB : 2 ≤ B) (hE : 2 ≤ E) (hF : 2 ≤ F)
    {δ C U V p : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hp : 0 ≤ p) (d : ℕ) (hd : (d : ℝ) ≤ p)
    (hδp : 1 / δ ≤ Real.exp ((p + A) ^ A)) (hCp : C ≤ Real.exp ((p + B) ^ B))
    (hUp : U ≤ Real.exp ((p + E) ^ E)) (hVp : V ≤ Real.exp ((p + F) ^ F)) :
    let D := A + B + E + F + 10
    1 / quotientCoordinateRadius δ C d ≤ Real.exp ((p + D) ^ D) ∧
      C * U ≤ Real.exp ((p + D) ^ D) ∧ V * C ≤ Real.exp ((p + D) ^ D) := by
  let T := A + B + E + F + 5
  have hT : 2 ≤ T := by dsimp [T]; omega
  have hshift {N : ℕ} (hN : 1 ≤ N) (hNT : N ≤ T) :
      Real.exp ((p + N) ^ N) ≤ Real.exp ((p + T) ^ T) :=
    Real.exp_le_exp.mpr (shifted_power_self_mono hp hN hNT)
  have hCq := hCp.trans (hshift (by omega) (by dsimp [T]; omega))
  have hUq := hUp.trans (hshift (by omega) (by dsimp [T]; omega))
  have hVq := hVp.trans (hshift (by omega) (by dsimp [T]; omega))
  have hCU := product_two_power_bounds T hT hU hp hCq hUq
  have hVC := product_two_power_bounds T hT hC hp hVq hCq
  have hr := quotientCoordinateRadius_inverse_power_budget A B hA hB hδ hC hp d hd hδp hCp
  have hr' : 1 / quotientCoordinateRadius δ C d ≤ Real.exp ((p + (T + 5 : ℕ)) ^ (T + 5)) :=
    hr.trans (Real.exp_le_exp.mpr (shifted_power_self_mono (C := A + B + 3) (D := T + 5)
      hp (by omega) (by dsimp [T]; omega)))
  have heq : T + 5 = A + B + E + F + 10 := rfl
  simpa only [heq] using And.intro hr' (And.intro hCU hVC)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHUniformQuotientCharts
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem quotient_coordinate_chart_metric_bounds
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) :
    letI := rightMetricSpace (hnil := hnil) e
    ∀ C : ℝ≥0, 0 < C → ∀ z : NilpotentLieBCHGroup L s hnil,
      LipschitzWith C (fun x => z * x) → LipschitzWith C (fun x => z⁻¹ * x) →
      ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
        4 * (C : ℝ) ^ 2 * (Fintype.card ι + 1) * r ≤ bchLatticeSeparationRadius s (Fintype.card ι) H l →
        letI := quotientMetricSpace e Γ hΓ
        ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
          let q := fun u => (QuotientGroup.mk (z * (basisHomeomorph e).symm u) : _ ⧸ Γ)
          dist (q v) (q w) ≤ (C : ℝ) * (bchBoxMetricConstant s (Fintype.card ι) H 1 : ℝ) * dist v w ∧
          dist v w ≤ (bchInverseBoxConstant s (Fintype.card ι) H 1 : ℝ) * C * dist (q v) (q w) := by
  let := rightMetricSpace (hnil := hnil) e
  intro C hC z hleft hleftInv r hr hr1 hsmall
  let := quotientMetricSpace e Γ hΓ
  intro v w hv hw
  have hC' : (0 : ℝ) < C := hC
  have hR : (C : ℝ) * (Fintype.card ι + 1) * r ≤
      bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * C)).mpr
    calc
      ((C : ℝ) * (Fintype.card ι + 1) * r) * (4 * C) =
          4 * (C : ℝ) ^ 2 * (Fintype.card ι + 1) * r := by ring
      _ ≤ _ := hsmall
  have hball (u : ι → ℝ) (hu : ∀ i, |u i| ≤ r) :
      dist (z * (basisHomeomorph e).symm u) z ≤
        bchLatticeSeparationRadius s (Fintype.card ι) H l / (4 * C) := by
    have hlog : dist ((basisHomeomorph (hnil := hnil) e).symm u) 1 ≤ (Fintype.card ι + 1) * r := by
      calc
        _ = dist 1 ((basisHomeomorph (hnil := hnil) e).symm u) := dist_comm _ _
        _ ≤ coordinateL2Norm (basisHomeomorph e ((basisHomeomorph (hnil := hnil) e).symm u)) :=
          dist_one_le_coordinateL2Norm e _
        _ = coordinateL2Norm u := by rw [Homeomorph.apply_symm_apply]
        _ ≤ _ := coordinateL2Norm_le_card_bound u hr hu
    have htrans := hleft.dist_le_mul ((basisHomeomorph (hnil := hnil) e).symm u) 1
    rw [mul_one] at htrans
    calc
      _ ≤ (C : ℝ) * dist ((basisHomeomorph (hnil := hnil) e).symm u) 1 := htrans
      _ ≤ (C : ℝ) * ((Fintype.card ι + 1) * r) := mul_le_mul_of_nonneg_left hlog C.coe_nonneg
      _ = (C : ℝ) * (Fintype.card ι + 1) * r := by ring
      _ ≤ _ := hR
  have hq := quotient_dist_eq_on_ball_of_lattice_grid e c hstructure hc Γ hΓ l hl hgrid C hC z
    hleftInv (hball v hv) (hball w hw)
  have hv1 (i) : |v i| ≤ (1 : ℝ) := (hv i).trans hr1
  have hw1 (i) : |w i| ≤ (1 : ℝ) := (hw i).trans hr1
  have hforward := (lipschitzOn_basisHomeomorph_symm_box (hnil := hnil) e c hstructure hc 1 le_rfl).dist_le_mul v hv1 w hw1
  have hinverse := dist_coordinates_le_bchInverseBoxConstant e c hstructure hc 1 le_rfl
    ((basisHomeomorph (hnil := hnil) e).symm v) ((basisHomeomorph (hnil := hnil) e).symm w)
    (fun i => by
      change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm v) i| ≤ _
      simpa only [Homeomorph.apply_symm_apply, NNReal.coe_one] using hv1 i)
    (fun i => by
      change |basisHomeomorph (hnil := hnil) e ((basisHomeomorph (hnil := hnil) e).symm w) i| ≤ _
      simpa only [Homeomorph.apply_symm_apply, NNReal.coe_one] using hw1 i)
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply] at hinverse
  dsimp only
  rw [hq]
  constructor
  · apply (hleft.dist_le_mul _ _).trans
    exact (mul_le_mul_of_nonneg_left hforward C.coe_nonneg).trans_eq (by ring)
  · have hback : dist ((basisHomeomorph (hnil := hnil) e).symm v) ((basisHomeomorph (hnil := hnil) e).symm w) ≤
        (C : ℝ) * dist (z * (basisHomeomorph e).symm v) (z * (basisHomeomorph e).symm w) := by
      have hb := hleftInv.dist_le_mul
        (z * (basisHomeomorph e).symm v) (z * (basisHomeomorph e).symm w)
      rw [inv_mul_cancel_left, inv_mul_cancel_left] at hb
      exact hb
    exact hinverse.trans ((mul_le_mul_of_nonneg_left hback (bchInverseBoxConstant _ _ _ _).coe_nonneg).trans_eq (by ring))

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

theorem exists_uniform_quotient_chart_metric_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι]
      [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
      [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
      (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) (H : ℕ) (p : ℝ)
      (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
      (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) (l : ℕ),
      0 < l → (∀ γ ∈ Γ, e.equivFun γ.coord ∈ realDenominatorGrid l) →
      (∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k) →
      (∀ i j k, RationalHeightLE (c i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := quotientMetricSpace e Γ hΓ
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∀ z : NilpotentLieBCHGroup L s hnil,
            (∀ i, |e.repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
            ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
              let q := fun u => (QuotientGroup.mk (z * (basisHomeomorph e).symm u) : _ ⧸ Γ)
              dist (q v) (q w) ≤ K * dist v w ∧ dist v w ≤ K * dist (q v) (q w) := by
  obtain ⟨A, hA, hgap⟩ := exists_bchLatticeSeparationRadius_inv_exp_bound s
  obtain ⟨B, hB, hleft⟩ := exists_uniform_left_lipschitz_exp_bound s a
  obtain ⟨E, hE, hforward⟩ := exists_bchBoxMetricConstant_exp_bound s 0
  obtain ⟨F, hF, hinverse⟩ := exists_bchInverseBoxConstant_exp_bound s 0
  refine ⟨A + B + E + F + 10, by omega, ?_⟩
  intro ι L _ _ _ _ _ _ _ _ _ e c H p hnil Γ hΓ l hl hgrid hstructure hc hp hd hH hlp
  let := rightMetricSpace (hnil := hnil) e
  let := quotientMetricSpace e Γ hΓ
  obtain ⟨C, hC, hCp, hleft⟩ := hleft e c H p hnil hstructure hp hd hH hc
  let δ := bchLatticeSeparationRadius s (Fintype.card ι) H l
  have hδ : 0 < δ := bchLatticeSeparationRadius_pos _ _ _ _
  let r := quotientCoordinateRadius δ (C : ℝ) (Fintype.card ι)
  let U := bchBoxMetricConstant s (Fintype.card ι) H 1
  let V := bchInverseBoxConstant s (Fintype.card ι) H 1
  have hunit : ((1 : ℝ≥0) : ℝ) ≤ Real.exp ((p + 2) ^ 0) := by
    simpa only [NNReal.coe_one, pow_zero] using Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨hrp, hCU, hVC⟩ := quotient_chart_parameter_budget A B E F hA hB hE hF
    hδ C.coe_nonneg U.coe_nonneg hp (Fintype.card ι) hd
    (hgap _ _ _ _ hp hd hH hlp) hCp
    (hforward _ _ 1 _ hp hd hH hunit) (hinverse _ _ 1 _ hp hd hH hunit)
  let K : ℝ≥0 := max (C * U) (V * C)
  have hK : (K : ℝ) ≤ Real.exp ((p + (A + B + E + F + 10 : ℕ)) ^ (A + B + E + F + 10)) := by
    simpa only [K, NNReal.coe_max, NNReal.coe_mul] using max_le hCU hVC
  have hKU : (C : ℝ) * U ≤ (K : ℝ) := by exact_mod_cast (le_max_left (C * U) (V * C))
  have hKV : (V : ℝ) * C ≤ (K : ℝ) := by exact_mod_cast (le_max_right (C * U) (V * C))
  refine ⟨r, quotientCoordinateRadius_pos hδ _, quotientCoordinateRadius_le_one hδ _, hrp, K, hK, ?_⟩
  intro z hz v w hv hw
  have hzinv (i) : |e.repr z⁻¹.coord i| ≤ Real.exp ((p + 2) ^ a) := by
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hz i
  obtain ⟨hvw, hwv⟩ := quotient_coordinate_chart_metric_bounds e c hstructure hc Γ hΓ l hl hgrid
    C hC z (hleft z hz) (hleft z⁻¹ hzinv) r (quotientCoordinateRadius_pos hδ _).le
    (quotientCoordinateRadius_le_one hδ _) (quotientCoordinateRadius_small hδ _) v w hv hw
  exact ⟨hvw.trans (mul_le_mul_of_nonneg_right hKU dist_nonneg),
    hwv.trans (mul_le_mul_of_nonneg_right hKV dist_nonneg)⟩

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHFiniteAtlas
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

namespace NilpotentLieBCHGroup

theorem quotient_covered_by_coordinate_box {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
    {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
    (e : Basis ι ℝ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (B : ℝ)
    (hrep : ∀ g : NilpotentLieBCHGroup L s hnil, ∃ z,
      (∀ i, |e.repr z.coord i| ≤ B) ∧ ∃ γ ∈ Γ, g = z * γ) :
    ∀ x : NilpotentLieBCHGroup L s hnil ⧸ Γ, ∃ v : ι → ℝ,
      (∀ i, |v i| ≤ B) ∧ (QuotientGroup.mk ((basisHomeomorph e).symm v) : _ ⧸ Γ) = x := by
  intro x
  induction x using Quotient.inductionOn with
  | h g =>
    obtain ⟨z, hz, γ, hγ, hg⟩ := hrep g
    refine ⟨basisHomeomorph e z, hz, ?_⟩
    rw [Homeomorph.symm_apply_apply, hg]
    exact (quotient_mk_mul_mem Γ z ⟨γ, hγ⟩).symm

end NilpotentLieBCHGroup

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]
  {s H : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem inv_mul_coordinates_bound
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (u v : NilpotentLieBCHGroup L s hnil) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hu : ∀ i, |e.repr u.coord i| ≤ B) (hv : ∀ i, |e.repr v.coord i| ≤ B)
    (huv : ∀ i, |e.repr u.coord i - e.repr v.coord i| ≤ δ) (k : ι) :
    |e.repr (u⁻¹ * v).coord k| ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  simpa only [coord_mul, coord_inv, neg_neg] using
    lieBCH_sub_coordinates_bound e c hstructure hc hnil (-u.coord) (-v.coord) hB hδ
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hu i)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hv i)
      (fun i => by simpa only [map_neg, Finsupp.neg_apply, neg_sub_neg, abs_sub_comm] using huv i) k

variable [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem finite_quotient_coordinate_cover
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ)
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (B : ℝ) (hB : 1 ≤ B)
    (hrep : ∀ g : NilpotentLieBCHGroup L s hnil, ∃ z,
      (∀ i, |e.repr z.coord i| ≤ B) ∧ ∃ γ ∈ Γ, g = z * γ)
    (r : ℝ) (hr : 0 < r) :
    let K : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
      bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
    let n := (boxCoverMeshCount B K (r / 2) + 1) ^ Fintype.card ι
    ∃ centers : Fin n → NilpotentLieBCHGroup L s hnil,
      (∀ j i, |e.repr (centers j).coord i| ≤ B) ∧
      ∀ x : NilpotentLieBCHGroup L s hnil ⧸ Γ, ∃ j, ∃ u : ι → ℝ,
        (∀ i, |u i| ≤ r / 2) ∧
        (QuotientGroup.mk (centers j * (basisHomeomorph e).symm u) : _ ⧸ Γ) = x := by
  classical
  let K : ℝ≥0 := ⟨bchBoxCoordinateBound s (Fintype.card ι) H B,
    bchBoxCoordinateBound_nonneg _ _ _ (by linarith)⟩
  let N := boxCoverMeshCount B K (r / 2)
  let n := (N + 1) ^ Fintype.card ι
  let I := ι → Fin (N + 1)
  have hN : 0 < N := boxCoverMeshCount_pos _ _ _
  have hcard : Fintype.card I = n := by simp [I, n]
  let reindex : I ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let centers : Fin n → NilpotentLieBCHGroup L s hnil := fun j =>
    (basisHomeomorph e).symm (uniformBoxGrid B N (reindex.symm j))
  have hcenters (j : Fin n) : e.equivFun (centers j).coord = uniformBoxGrid B N (reindex.symm j) :=
    (basisHomeomorph (hnil := hnil) e).apply_symm_apply _
  have hcentersB (j i) : |e.repr (centers j).coord i| ≤ B := by
    have := uniformBoxGrid_mem (ι := ι) (by linarith : 0 ≤ B) hN (reindex.symm j) i
    simpa only [← hcenters j, Basis.equivFun_apply] using this
  refine ⟨centers, hcentersB, ?_⟩
  intro x
  obtain ⟨v, hv, hvx⟩ := quotient_covered_by_coordinate_box e Γ B hrep x
  obtain ⟨k, hk⟩ := exists_uniformBoxGrid_approx (by linarith : 0 < B) hN v hv
  let j := reindex k
  let g := (basisHomeomorph (hnil := hnil) e).symm v
  have hgv : e.equivFun g.coord = v := (basisHomeomorph (hnil := hnil) e).apply_symm_apply v
  have hgB (i) : |e.repr g.coord i| ≤ B := by
    simpa only [← hgv, Basis.equivFun_apply] using hv i
  have hdiff (i) : |e.repr (centers j).coord i - e.repr g.coord i| ≤ 2 * B / N := by
    have hi := (dist_pi_le_iff (by positivity : 0 ≤ 2 * B / (N : ℝ))).mp hk i
    have hj : reindex.symm j = k := reindex.symm_apply_apply k
    have hci : e.repr (centers j).coord i = uniformBoxGrid B N k i := by
      simpa only [Basis.equivFun_apply, hj] using congrFun (hcenters j) i
    have hgi : e.repr g.coord i = v i := by
      simpa only [Basis.equivFun_apply] using congrFun hgv i
    simpa only [Real.dist_eq, ← hci, ← hgi, abs_sub_comm] using hi
  have herror : (K : ℝ) * (2 * B / N) ≤ r / 2 := boxCoverMeshCount_error K (by linarith)
  have hsmall (i) : |e.repr ((centers j)⁻¹ * g).coord i| ≤ r / 2 :=
    (inv_mul_coordinates_bound e c hstructure hc (centers j) g hB
      (by positivity) (hcentersB j) hgB hdiff i).trans herror
  refine ⟨j, basisHomeomorph e ((centers j)⁻¹ * g), hsmall, ?_⟩
  simp only [Homeomorph.symm_apply_apply, mul_inv_cancel_left]
  exact hvx

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open scoped NNReal

theorem half_radius_inverse_power_bound (C : ℕ) (hC : 2 ≤ C) {r p : ℝ}
    (hr : 0 < r) (hp : 0 ≤ p) (hri : 1 / r ≤ Real.exp ((p + C) ^ C)) :
    1 / (r / 2) ≤ Real.exp ((p + (C + 3 : ℕ)) ^ (C + 3)) := by
  have h := metricPartition_constant_power_budget C 1 hC ⟨r, hr.le⟩ hp
    (by simpa only [Nat.cast_one] using Real.one_le_exp (by positivity : 0 ≤ (p + C) ^ C)) hri
  have hthree : 3 / r ≤ Real.exp ((p + (C + 3 : ℕ)) ^ (C + 3)) := by
    norm_num at h ⊢
    exact h
  apply le_trans ?_ hthree
  rw [show 1 / (r / 2) = 2 / r by ring]
  exact div_le_div_of_nonneg_right (by norm_num) hr.le

theorem exists_bch_flexible_cover_exp_bound (s C₀ Cᵣ : ℕ) (hC₀ : 2 ≤ C₀) (hCᵣ : 2 ≤ Cᵣ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ (d H : ℕ) (p r : ℝ),
      0 ≤ p → (d : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      0 < r → 1 / r ≤ Real.exp ((p + Cᵣ) ^ Cᵣ) →
      let B := Real.exp ((p + C₀) ^ C₀)
      let K : ℝ≥0 := ⟨bchBoxCoordinateBound s d H B,
        bchBoxCoordinateBound_nonneg _ _ _ (Real.exp_nonneg _)⟩
      (((boxCoverMeshCount B K (r / 2) + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C₁, hC₁, hinput⟩ := exists_bch_partition_input_exp_bound s 0 C₀ hC₀
  let C := C₁ + Cᵣ + 5
  have hC : 2 ≤ C := by dsimp [C]; omega
  refine ⟨C + 5, by omega, ?_⟩
  intro d H p r hp hd hH hr hri
  let B := Real.exp ((p + C₀) ^ C₀)
  let K : ℝ≥0 := ⟨bchBoxCoordinateBound s d H B,
    bchBoxCoordinateBound_nonneg _ _ _ (Real.exp_nonneg _)⟩
  obtain ⟨hB, hmetric, _⟩ := hinput d H p hp hd hH
  have hshift := Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := C₁) (D := C) hp (by omega) (by dsimp [C]; omega))
  have hBC := hB.trans hshift
  have hKC : (K : ℝ) ≤ Real.exp ((p + C) ^ C) :=
    (bchBoxCoordinateBound_le_bchBoxMetricConstant s d H ⟨B, Real.exp_nonneg _⟩).trans
      (hmetric.trans hshift)
  have hhalf := (half_radius_inverse_power_bound Cᵣ hCᵣ hr hp hri).trans
    (Real.exp_le_exp.mpr (shifted_power_self_mono (C := Cᵣ + 3) (D := C)
      hp (by omega) (by dsimp [C]; omega)))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    boxCoverCount_le_exp C d hC K (Real.exp_nonneg _) (by linarith) hp hd hBC hKC hhalf

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealifiedBCHSmoothPartition
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_quotient_chart_metric_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∀ z : G,
            (∀ i, |(e.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
            ∀ v w : ι → ℝ, (∀ i, |v i| ≤ r) → (∀ i, |w i| ≤ r) →
              let q := fun u => (QuotientGroup.mk
                (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm u) : G ⧸ ΓR)
              dist (q v) (q w) ≤ K * dist v w ∧ dist v w ≤ K * dist (q v) (q w) := by
  obtain ⟨D, hD, hchart⟩ := NilpotentLieBCHGroup.exists_uniform_quotient_chart_metric_exp_bound s a
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl houter hc hp hd hH hlp
  exact hchart (e.baseChange ℝ) (lieStructureConstants e) H p
    (realification_lowerCentralSeries_eq_bot hnil) (Γ.map NilpotentLieBCHGroup.realificationHom)
    (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).1 l hl
    (NilpotentLieBCHGroup.realification_subgroup_grid e Γ l houter)
    (fun i j k => (realLieBasis_structure e i j k).symm) hc hp hd hH hlp

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_bilipschitz_charts_exp_bound (s a : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
          ∀ z : G, (∀ i, |(e.baseChange ℝ).repr z.coord i| ≤ Real.exp ((p + 2) ^ a)) →
            ∃ φ : OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
              (∀ v, φ v = (QuotientGroup.mk
                (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
              φ.source = {v | ∀ i, |v i| < r} ∧
              LipschitzOnWith K φ φ.source ∧ LipschitzOnWith K φ.symm φ.target := by
  obtain ⟨D, hD, hmetric⟩ := exists_realification_quotient_chart_metric_exp_bound s a
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl houter hc hp hd hH hlp
  let := realificationQuotientMetricSpace e Γ l hl houter
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L) := (e.baseChange ℝ).finiteDimensional_of_finite
  obtain ⟨r, hr, hr1, hrp, K, hK, hcharts⟩ := hmetric e hnil Γ l H p hl houter hc hp hd hH hlp
  refine ⟨r, hr, hr1, hrp, K, hK, ?_⟩
  intro z hz
  let q := fun v : ι → ℝ => (QuotientGroup.mk
    (z * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) :
      _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom)
  have hq : Continuous q := QuotientGroup.continuous_mk.comp
    (continuous_const.mul (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm.continuous)
  have hqo : IsOpenMap q := QuotientGroup.isOpenMap_coe.comp
    ((Homeomorph.mulLeft z).isOpenMap.comp (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm.isOpenMap)
  have hU : IsOpen {v : ι → ℝ | ∀ i, |v i| < r} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i).abs continuous_const)
  obtain ⟨φ, hφ, hsource, _, hLip, hInv⟩ := exists_openPartialHomeomorph_of_metric_bounds q hq hqo
    {v : ι → ℝ | ∀ i, |v i| < r} hU K
    (fun v hv w hw => (hcharts z hz v w (fun i => (hv i).le) (fun i => (hw i).le)).1)
    (fun v hv w hw => (hcharts z hz v w (fun i => (hv i).le) (fun i => (hw i).le)).2)
  exact ⟨φ, hφ, hsource, hLip, hInv⟩

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct NNReal

theorem exists_realification_finite_bilipschitz_atlas_exp_bound_s2_oai (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (e : Basis ι ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l H : ℕ) (p : ℝ)
      (hl : 0 < l) (_hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
      (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l),
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      letI := realificationQuotientMetricSpace e Γ l hl houter
      let G := NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)
      let ΓR : Subgroup G := Γ.map NilpotentLieBCHGroup.realificationHom
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ 1 / r ≤ Real.exp ((p + D) ^ D) ∧
        ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + D) ^ D) ∧
        ∃ centers : Fin n → G, ∃ φ : Fin n → OpenPartialHomeomorph (ι → ℝ) (G ⧸ ΓR),
          (∀ j i, |(e.baseChange ℝ).repr (centers j).coord i| ≤ Real.exp ((p + D) ^ D)) ∧
          (∀ j v, φ j v = (QuotientGroup.mk
            (centers j * (NilpotentLieBCHGroup.basisHomeomorph (e.baseChange ℝ)).symm v) : G ⧸ ΓR)) ∧
          (∀ j, (φ j).source = {v | ∀ i, |v i| < r}) ∧
          (∀ j, LipschitzOnWith K (φ j) (φ j).source) ∧
          (∀ j, LipschitzOnWith K (φ j).symm (φ j).target) ∧
          (∀ x : G ⧸ ΓR, ∃ j, ∃ u : ι → ℝ, (∀ i, |u i| ≤ r / 2) ∧ φ j u = x) := by
  obtain ⟨C₀, hC₀, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨C₁, hC₁, hcharts⟩ := exists_realification_bilipschitz_charts_exp_bound s C₀
  let Cᵣ := C₀ + C₁ + 2
  have hCᵣ : 2 ≤ Cᵣ := by dsimp [Cᵣ]; omega
  obtain ⟨C₂, hC₂, hcount⟩ := exists_bch_flexible_cover_exp_bound s C₀ Cᵣ hC₀ hCᵣ
  let D := Cᵣ + C₂ + 2
  have hD : 2 ≤ D := by dsimp [D]; omega
  refine ⟨D, hD, ?_⟩
  intro ι L _ _ _ _ _ _ _ e hnil Γ l H p hl hinner houter hc hp hd hH hlp
  let := realificationQuotientMetricSpace e Γ l hl houter
  have hpq : 0 ≤ p + C₀ := by positivity
  have hdq : (Fintype.card ι : ℝ) ≤ p + C₀ := hd.trans (by linarith [Nat.cast_nonneg (α := ℝ) C₀])
  have hep : Real.exp p ≤ Real.exp (p + C₀) := Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) C₀])
  obtain ⟨r, hr, hr1, hrp, K, hKp, hcharts⟩ :=
    hcharts e hnil Γ l H (p + C₀) hl houter hc hpq hdq (hH.trans hep) (hlp.trans hep)
  have hshift : Real.exp (((p + C₀) + C₁) ^ C₁) ≤ Real.exp ((p + Cᵣ) ^ Cᵣ) :=
    Real.exp_le_exp.mpr (shifted_center_power_bound C₀ C₁ hp)
  have hrC := hrp.trans hshift
  have hKC := hKp.trans hshift
  have hRD := Real.exp_le_exp.mpr (shifted_power_self_mono (C := Cᵣ) (D := D)
    hp (by omega) (by dsimp [D]; omega))
  let B := Real.exp ((p + C₀) ^ C₀)
  have hB : 1 ≤ B := Real.one_le_exp (by positivity)
  have hBD : B ≤ Real.exp ((p + D) ^ D) := Real.exp_le_exp.mpr
    (shifted_power_self_mono (C := C₀) (D := D) hp (by omega) (by dsimp [D, Cᵣ]; omega))
  have hBZ : B ≤ Real.exp (((p + C₀) + 2) ^ C₀) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) C₀)
  obtain ⟨centers, hcenters, hcover⟩ := NilpotentLieBCHGroup.finite_quotient_coordinate_cover
    (e.baseChange ℝ) (lieStructureConstants e) (fun i j k => (realLieBasis_structure e i j k).symm) hc
    (Γ.map NilpotentLieBCHGroup.realificationHom) B hB
    (hrep e hnil Γ l H p hl hinner hc hp hd hH hlp) r hr
  choose φ hφ hsource hLip hInv using fun j => hcharts (centers j) (fun i => (hcenters j i).trans hBZ)
  have hn := (hcount (Fintype.card ι) H p r hp hd hH hr hrC).trans
    (Real.exp_le_exp.mpr (shifted_power_self_mono (C := C₂) (D := D)
      hp (by omega) (by dsimp [D]; omega)))
  refine ⟨r, hr, hr1, hrC.trans hRD, K, hKC.trans hRD, _, by positivity, hn,
    centers, φ, fun j i => (hcenters j i).trans hBD, hφ, hsource, hLip, hInv, ?_⟩
  intro x
  obtain ⟨j, u, hu, heq⟩ := hcover x
  exact ⟨j, u, hu, (hφ j u).trans heq⟩

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.exists_realification_finite_bilipschitz_atlas_exp_bound_s2_oai.{u_1, u_2} := @OAI.Erdos3.exists_realification_finite_bilipschitz_atlas_exp_bound_s2_oai.{u_1, u_2}
