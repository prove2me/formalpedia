-- Prove2me | solution 1 for OAI.PolycyclicRecognition.CartanWordModel.exists_invertible_height_factor_of_stationary_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T00:14:37.791287+00:00
-- url     : https://prove2.me/submissions/3ffcddfb-4f0d-47df-b2a2-1c77be25632c

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_segmentSupport_le_of_stationary_mean_m

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorOrbit
attribute [-instance] _root_.GeneratesNS.fintype_closedBall _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Spanning by conjugated generator directions

Products of adjoint exponentials applied to a Lie-generating family span the
whole algebra. This proves the linear nondegeneracy needed to construct a
submersive generator product scheme; it does not assume controllability or a
volume estimate.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.generatorOrbitNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.generatorOrbitNormedSpace
theorem generator_mem_orbitSpan (X : I → L) (i : I) : X i ∈ generatorOrbitSpan X := by
  apply Submodule.subset_span
  exact ⟨([], i), rfl⟩

/-- Each adjoint exponential preserves this span by prefixing a word. -/
theorem exp_ad_mem_orbitSpan (X : I → L) (i : I) (t : ℝ) {v : L}
    (hv : v ∈ generatorOrbitSpan X) :
    NormedSpace.exp (t • continuousAd (X i)) v ∈ generatorOrbitSpan X := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨w, j⟩, rfl⟩ := hv
    apply Submodule.subset_span
    exact ⟨((i, t) :: w, j), rfl⟩
  | zero => simp
  | add v u _ _ hv hu => simpa using (generatorOrbitSpan X).add_mem hv hu
  | smul c v _ hv => simpa using (generatorOrbitSpan X).smul_mem c hv

/-- Differentiating the genuine operator exponential recovers the adjoint. -/
theorem hasDerivAt_exp_ad_apply (x v : L) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • continuousAd x) v) ⁅x, v⁆ 0 := by
  have h := (hasDerivAt_exp_smul_const (continuousAd x) (0 : ℝ)).clm_apply
    (hasDerivAt_const (0 : ℝ) v)
  simpa using h

/-- A derivative of a curve in a closed linear subspace stays in that subspace. -/
theorem derivative_mem_submodule {f : ℝ → L} {v : L} {t : ℝ}
    (hf : HasDerivAt f v t) (U : Submodule ℝ L) (hU : ∀ s, f s ∈ U) : v ∈ U := by
  have h := range_deriv_subset_closure_span_image f dense_univ (Set.mem_range_self t)
  rw [hf.deriv] at h
  have hs : Submodule.span ℝ (f '' Set.univ) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s, _, rfl⟩
    exact hU s
  have hc : IsClosed (U : Set L) := U.closed_of_finiteDimensional
  exact (closure_minimal hs hc) h

/-- Invariance under generator exponentials implies infinitesimal invariance. -/
theorem ad_mem_orbitSpan (X : I → L) (i : I) {v : L}
    (hv : v ∈ generatorOrbitSpan X) : ⁅X i, v⁆ ∈ generatorOrbitSpan X :=
  derivative_mem_submodule (hasDerivAt_exp_ad_apply (X i) v) (generatorOrbitSpan X)
    (fun t => exp_ad_mem_orbitSpan X i t hv)

/-- The conjugated generator directions span the entire generated Lie
algebra. No nilpotence assumption is needed for this nondegeneracy step. -/
theorem generatorOrbitSpan_eq_top (X : I → L)
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    generatorOrbitSpan X = ⊤ := by
  let U := generatorOrbitSpan X
  have hstab : submoduleAdjointStabilizer U = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩ v hv
    exact ad_mem_orbitSpan X i hv
  let K : LieSubalgebra ℝ L := { U with
    lie_mem' := by
      intro x y hx hy
      have hx' : x ∈ submoduleAdjointStabilizer U := by rw [hstab]; trivial
      exact hx' y hy }
  have hK : K = ⊤ := by
    apply top_unique
    rw [← hX]
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i, rfl⟩
    exact generator_mem_orbitSpan X i
  exact congrArg LieSubalgebra.toSubmodule hK

/-- Choose finitely many actual conjugated generator directions as a basis.
These are the differential columns in a conjugated generator scheme. -/
theorem exists_generatorOrbit_basis (X : I → L)
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    ∃ (b : Basis (Fin (finrank ℝ L)) ℝ L)
      (w : Fin (finrank ℝ L) → List (I × ℝ)) (i : Fin (finrank ℝ L) → I),
      ∀ k, generatorAdjointWord X (w k) (X (i k)) = b k := by
  classical
  have hspan : ⊤ ≤ generatorOrbitSpan X := (generatorOrbitSpan_eq_top X hX).ge
  let J := (linearIndepOn_empty ℝ (id : L → L)).extend
    (Set.empty_subset (Set.range (fun p : List (I × ℝ) × I =>
      generatorAdjointWord X p.1 (X p.2))))
  let b : Basis J ℝ L := Basis.ofSpan hspan
  let : Fintype J := Fintype.ofFinite _
  let e : J ≃ Fin (finrank ℝ L) :=
    Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  have hb (k : Fin (finrank ℝ L)) : ∃ p : List (I × ℝ) × I,
      generatorAdjointWord X p.1 (X p.2) = (b.reindex e) k := by
    simpa only [Basis.coe_reindex, Function.comp_apply, Set.mem_range] using
      (Basis.ofSpan_subset hspan (show b (e.symm k) ∈ Set.range b from ⟨_, rfl⟩))
  choose p hp using hb
  exact ⟨b.reindex e, fun k => (p k).1, fun k => (p k).2, hp⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_LogDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic distortion from polynomially corrected contraction

The nilpotent part of a real weight action introduces a polynomial factor.
It is absorbed by an additional logarithmic conjugating time. These lemmas
retain that factor instead of assuming a semisimple action.
-/

noncomputable section

open Filter
open scoped Topology

namespace PolycyclicRecognition

/-- A polynomial correction to exponential contraction can be absorbed
uniformly at a time bounded by twice the logarithm of the initial size. -/
theorem exists_logarithmic_contraction_time {C : ℝ} (hC : 0 ≤ C) (b : ℕ) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ R : ℝ, 0 ≤ R →
      let t := 2 * Real.log (2 + R) + a
      1 ≤ t ∧ C * (1 + t) ^ b * Real.exp (-t) * R ≤ 1 := by
  have hp : Tendsto (fun t : ℝ => t ^ b * Real.exp (-(1 / 2 : ℝ) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b : ℝ) (1 / 2) (by norm_num)
  have hs : Tendsto (fun t : ℝ => 1 + t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro z
    filter_upwards [eventually_ge_atTop (z - 1)] with t ht
    linarith
  have heq (t : ℝ) : C * (1 + t) ^ b * Real.exp (-t / 2) =
      (C * Real.exp (1 / 2)) * ((1 + t) ^ b * Real.exp (-(1 / 2) * (1 + t))) := by
    have hh : Real.exp (-t / 2) = Real.exp (1 / 2) * Real.exp (-(1 / 2) * (1 + t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hh]
    ring
  have ht : Tendsto (fun t : ℝ => C * (1 + t) ^ b * Real.exp (-t / 2)) atTop (𝓝 0) := by
    simpa only [heq, Function.comp_def, mul_zero] using
      (hp.comp hs).const_mul (C * Real.exp (1 / 2))
  obtain ⟨a₀, ha₀⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  let a := max a₀ 1
  refine ⟨a, (by dsimp [a] <;> positivity), fun R hR => ?_⟩
  let t := 2 * Real.log (2 + R) + a
  have hlog : 0 ≤ Real.log (2 + R) := Real.log_nonneg (by linarith)
  have ha1 : 1 ≤ a := le_max_right _ _
  have ha : 0 ≤ a := by linarith
  have ht0 : 0 ≤ t := by dsimp [t] <;> positivity
  have ht1 : 1 ≤ t := by dsimp [t] <;> linarith
  have hta : a₀ ≤ t := (le_max_left _ _).trans (by dsimp [t] <;> linarith)
  have hcoef : C * (1 + t) ^ b * Real.exp (-t / 2) ≤ 1 := (ha₀ t hta).le
  have hsmall : Real.exp (-t / 2) * R ≤ 1 := by
    calc
      Real.exp (-t / 2) * R ≤ Real.exp (-Real.log (2 + R)) * R := by
        apply mul_le_mul_of_nonneg_right _ hR
        apply Real.exp_le_exp.mpr
        dsimp [t]
        linarith
      _ = R / (2 + R) := by rw [Real.exp_neg, Real.exp_log (by linarith)]; ring
      _ ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
  refine ⟨ht1, ?_⟩
  have hnonneg : 0 ≤ C * (1 + t) ^ b * Real.exp (-t / 2) := by positivity
  calc
    C * (1 + t) ^ b * Real.exp (-t) * R =
        (C * (1 + t) ^ b * Real.exp (-t / 2)) * (Real.exp (-t / 2) * R) := by
      have hh : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hh]
      ring
    _ ≤ (C * (1 + t) ^ b * Real.exp (-t / 2)) * 1 :=
      mul_le_mul_of_nonneg_left hsmall hnonneg
    _ ≤ 1 := by simpa using hcoef

variable {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- Product lengths in a left invariant metric. -/
theorem dist_one_mul_le (a b : G) : dist 1 (a * b) ≤ dist 1 a + dist 1 b := by
  calc
    dist 1 (a * b) ≤ dist 1 a + dist a (a * b) := dist_triangle _ _ _
    _ = _ := by simpa only [mul_one] using congrArg (dist 1 a + ·) (dist_mul_left a 1 b)

/-- Conjugation costs at most twice the conjugating length. -/
theorem dist_one_conjugate_le (a x : G) :
    dist 1 (a * x * a⁻¹) ≤ 2 * dist 1 a + dist 1 x := by
  have hi : dist 1 a⁻¹ = dist 1 a := by
    simpa only [mul_one, mul_inv_cancel, dist_comm] using (dist_mul_left a 1 a⁻¹).symm
  calc
    dist 1 (a * x * a⁻¹) ≤ dist 1 (a * x) + dist 1 a⁻¹ := dist_one_mul_le _ _
    _ ≤ (dist 1 a + dist 1 x) + dist 1 a⁻¹ := add_le_add (dist_one_mul_le _ _) le_rfl
    _ = _ := by rw [hi]; ring

/-- Exponential contraction up to a polynomial, together with a bounded
unit neighborhood and linear conjugating paths, implies logarithmic distortion. -/
theorem logarithmic_distortion_of_contracting_flow
    {V : Type} [NormedAddCommGroup V]
    (Exp : V → G) (d : ℝ → G) (T : ℝ → V → V)
    {C L B : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hB : 0 ≤ B) (b : ℕ)
    (hconj : ∀ v t, 0 ≤ t → Exp v = d t * Exp (T t v) * (d t)⁻¹)
    (hcontract : ∀ v t, 0 ≤ t → ‖T t v‖ ≤ C * (1 + t) ^ b * Real.exp (-t) * ‖v‖)
    (hpath : ∀ t, 1 ≤ t → dist 1 (d t) ≤ L * t)
    (hlocal : ∀ v, ‖v‖ ≤ 1 → dist 1 (Exp v) ≤ B) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  obtain ⟨a, ha, htime⟩ := exists_logarithmic_contraction_time hC b
  let c := (2 * L * a + B) / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ c := by dsimp [c] <;> positivity
  refine ⟨4 * L + c + 1, by positivity, fun v => ?_⟩
  let t := 2 * Real.log (2 + ‖v‖) + a
  obtain ⟨ht1, hsize⟩ := htime ‖v‖ (norm_nonneg v)
  have ht : 0 ≤ t := le_trans zero_le_one ht1
  have hunit : ‖T t v‖ ≤ 1 := (hcontract v t ht).trans hsize
  have hlog : Real.log 2 ≤ Real.log (2 + ‖v‖) :=
    Real.log_le_log (by norm_num) (by linarith [norm_nonneg v])
  have hconst : 2 * L * a + B ≤ c * Real.log (2 + ‖v‖) := by
    calc
      2 * L * a + B = c * Real.log 2 := by dsimp [c]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog hc
  calc
    dist 1 (Exp v) = dist 1 (d t * Exp (T t v) * (d t)⁻¹) := by rw [← hconj v t ht]
    _ ≤ 2 * dist 1 (d t) + dist 1 (Exp (T t v)) := dist_one_conjugate_le _ _
    _ ≤ 2 * (L * t) + B := add_le_add (by gcongr; exact hpath t ht1) (hlocal _ hunit)
    _ = 4 * L * Real.log (2 + ‖v‖) + (2 * L * a + B) := by dsimp [t] <;> ring
    _ ≤ (4 * L + c + 1) * Real.log (2 + ‖v‖) := by nlinarith

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ContinuousFlowDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instNonemptyBases _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous contracting flows

The local metric bounds in logarithmic distortion follow from continuity
and compactness. A continuous one-parameter homomorphism has at most linear
metric growth, so no differentiability estimate needs to be assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Metric

variable {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

theorem dist_one_pow_le (g : G) (n : ℕ) : dist 1 (g ^ n) ≤ (n : ℝ) * dist 1 g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      dist 1 (g ^ n * g) ≤ dist 1 (g ^ n) + dist 1 g := dist_one_mul_le _ _
      _ ≤ (n : ℝ) * dist 1 g + dist 1 g := add_le_add ih le_rfl
      _ = _ := by push_cast <;> ring

/-- Every continuous one-parameter homomorphism has a linear metric bound
for times at least one, using only boundedness of its compact unit interval. -/
theorem continuous_flow_linear_growth
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t, 1 ≤ t → dist 1 (d t) ≤ L * t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (continuous_const.dist hd).continuousOn
  have hC0 : 0 ≤ C := by
    have h := hC (mem_image_of_mem (fun t => dist (1 : G) (d t))
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num))
    simpa [hd0] using h
  have hpower (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hd0]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨2 * C, by positivity, fun t ht => ?_⟩
  let n := ⌊t⌋₊ + 1
  have hn : 0 < n := Nat.succ_pos _
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  have htn : t ≤ (n : ℝ) := by simpa [n] using (Nat.lt_floor_add_one t).le
  have hnt : (n : ℝ) ≤ t + 1 := by
    simpa [n] using add_le_add_right (Nat.floor_le (by linarith : 0 ≤ t)) 1
  have hs : t / n ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hnr.le, (div_le_one hnr).mpr htn⟩
  have hlocal : dist 1 (d (t / n)) ≤ C := hC (mem_image_of_mem _ hs)
  have heq : d t = d (t / n) ^ n := by
    convert hpower (t / n) n using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  calc
    dist 1 (d t) = dist 1 (d (t / n) ^ n) := congrArg (dist 1) heq
    _ ≤ (n : ℝ) * dist 1 (d (t / n)) := dist_one_pow_le _ _
    _ ≤ (n : ℝ) * C := mul_le_mul_of_nonneg_left hlocal hnr.le
    _ ≤ (2 * C) * t := by nlinarith

/-- For a continuous exponential chart and continuous contracting flow,
polynomially corrected contraction implies an actual logarithmic distance bound.
The compact unit-ball bound and the flow-length bound are derived in the proof. -/
theorem logarithmic_distortion_of_continuous_flow
    {V : Type} [NormedAddCommGroup V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t) (T : ℝ → V → V)
    {C : ℝ} (hC : 0 ≤ C) (b : ℕ)
    (hconj : ∀ v t, 0 ≤ t → Exp v = d t * Exp (T t v) * (d t)⁻¹)
    (hcontract : ∀ v t, 0 ≤ t → ‖T t v‖ ≤ C * (1 + t) ^ b * Real.exp (-t) * ‖v‖) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  obtain ⟨L, hL, hpath⟩ := continuous_flow_linear_growth d hd hd0 hmul
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : V) 1).bddAbove_image
    (continuous_const.dist hExp).continuousOn
  have hB0 : 0 ≤ B := (dist_nonneg (x := (1 : G)) (y := Exp 0)).trans
    (hB (mem_image_of_mem _ (by simp : (0 : V) ∈ closedBall 0 1)))
  apply logarithmic_distortion_of_contracting_flow Exp d T hC hL hB0 b hconj hcontract hpath
  intro v hv
  apply hB
  exact mem_image_of_mem _ (by simpa only [mem_closedBall, dist_zero_right] using hv)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Exponential coordinates for upper unipotent matrices

The analytic matrix exponential is a finite polynomial on nilpotent matrices.
This bridges the ordered-product bounds to actual exponential increments,
rather than a separately stipulated polynomial group law.
-/

namespace PolycyclicRecognition

open scoped BigOperators

section Algebra

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A]

/-- The polynomial exponential gives a uniform increment bound on any fixed
bounded set of nilpotent logarithms. -/
theorem norm_exp_sub_one_le_of_pow_eq_zero [NormOneClass A]
    (x : A) {c : ℕ} (hx : x ^ (c + 1) = 0)
    {M : ℝ} (hM : 0 ≤ M) (hbound : ‖x‖ ≤ M) :
    ‖NormedSpace.exp x - 1‖ ≤ (c : ℝ) * (1 + M) ^ c := by
  rw [exp_eq_finite_sum_of_pow_eq_zero x hx, Finset.sum_range_succ']
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul,
    add_sub_cancel_right]
  calc
    _ ≤ ∑ k ∈ Finset.range c, ‖((k + 1).factorial : ℝ)⁻¹ • x ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range c, (1 + M) ^ c := by
      apply Finset.sum_le_sum
      intro k hk
      have hf : (1 : ℝ) ≤ (k + 1).factorial := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos (k + 1))
      have hi : ‖((k + 1).factorial : ℝ)⁻¹‖ ≤ 1 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
        exact inv_le_one_of_one_le₀ hf
      calc
        _ = ‖((k + 1).factorial : ℝ)⁻¹‖ * ‖x ^ (k + 1)‖ := norm_smul _ _
        _ ≤ 1 * ‖x ^ (k + 1)‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
        _ ≤ (1 + M) ^ (k + 1) := by
          rw [one_mul]
          exact (norm_pow_le _ _).trans
            (pow_le_pow_left₀ (norm_nonneg _) (by linarith) (k + 1))
        _ ≤ (1 + M) ^ c := pow_le_pow_right₀ (by linarith) (Finset.mem_range.mp hk)
    _ = _ := by simp

end Algebra

end PolycyclicRecognition

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_NilpotentFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Nilpotent corrections in a contracting weight flow

The nilpotent part of the infinitesimal action gives a polynomial bound
for its actual analytic exponential. Coupled with scalar exponential
contraction, it gives logarithmic metric distortion of the weight chart.
-/

noncomputable section

namespace PolycyclicRecognition

/-- Split the scalar weight from the nilpotent part in the actual analytic
exponential of the infinitesimal generator. -/
theorem exp_smul_sub_one
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (N : A) (t : ℝ) :
    NormedSpace.exp (t • (N - 1)) = Real.exp (-t) • NormedSpace.exp (t • N) := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hc : Commute ((-t) • (1 : A)) (t • N) := by
    change ((-t) • (1 : A)) * (t • N) = (t • N) * ((-t) • (1 : A))
    simpa only [Algebra.algebraMap_eq_smul_one] using Algebra.commutes (-t) (t • N)
  have he : NormedSpace.exp ((-t) • (1 : A)) = Real.exp (-t) • (1 : A) := by
    simpa only [Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one] using
      (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := A) (-t)).symm
  rw [show t • (N - 1) = (-t) • (1 : A) + t • N by module,
    NormedSpace.exp_add_of_commute hc, he, smul_mul_assoc, one_mul]

/-- The actual exponential of a nilpotent operator has polynomial growth
in its real parameter, with an explicit uniform coefficient. -/
theorem norm_exp_smul_nilpotent_le
    {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A]
    (N : A) {c : ℕ} (hN : N ^ (c + 1) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • N)‖ ≤
      ((c : ℝ) + 1) * (1 + ‖N‖) ^ c * (1 + t) ^ c := by
  have hpow : (t • N) ^ (c + 1) = 0 := by simp [smul_pow, hN]
  have hbound : ‖NormedSpace.exp (t • N) - 1‖ ≤
      (c : ℝ) * (1 + t * ‖N‖) ^ c := by
    apply norm_exp_sub_one_le_of_pow_eq_zero _ hpow (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hbase : 1 + t * ‖N‖ ≤ (1 + ‖N‖) * (1 + t) := by
    nlinarith [norm_nonneg N]
  have hpoly : (1 + t * ‖N‖) ^ c ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) hbase c
  have hone : 1 ≤ (1 + ‖N‖) ^ c * (1 + t) ^ c :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg N]))
      (one_le_pow₀ (by linarith))
  calc
    ‖NormedSpace.exp (t • N)‖ ≤ ‖NormedSpace.exp (t • N) - 1‖ + ‖(1 : A)‖ :=
      norm_le_norm_sub_add _ _
    _ ≤ (c : ℝ) * (1 + t * ‖N‖) ^ c + 1 := by simpa only [norm_one] using add_le_add hbound le_rfl
    _ ≤ (c : ℝ) * ((1 + ‖N‖) ^ c * (1 + t) ^ c) +
        ((1 + ‖N‖) ^ c * (1 + t) ^ c) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hpoly (Nat.cast_nonneg _)) hone
    _ = _ := by ring

/-- The infinitesimal nilpotent correction, with its actual operator
exponential, has exactly the polynomially corrected contraction needed above. -/
theorem norm_contracted_nilpotent_flow_le
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [Nontrivial V]
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (v : V) {t : ℝ} (ht : 0 ≤ t) :
    ‖Real.exp (-t) • (NormedSpace.exp (t • N)) v‖ ≤
      (((c : ℝ) + 1) * (1 + ‖N‖) ^ c) * (1 + t) ^ c * Real.exp (-t) * ‖v‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-t) * ‖(NormedSpace.exp (t • N)) v‖ ≤
        Real.exp (-t) * (‖NormedSpace.exp (t • N)‖ * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (Real.exp_pos _).le
    _ ≤ Real.exp (-t) *
        ((((c : ℝ) + 1) * (1 + ‖N‖) ^ c * (1 + t) ^ c) * ‖v‖) := by
      gcongr
      exact norm_exp_smul_nilpotent_le N hN ht
    _ = _ := by ring

/-- A continuous weight chart with a nilpotent correction in its contracting
action is logarithmically distorted. This is the individual weight-space
estimate, before taking bounded products of generator directions. -/
theorem logarithmic_distortion_of_nilpotent_flow
    {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Nontrivial V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp (Real.exp (-t) • (NormedSpace.exp (t • N)) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  exact logarithmic_distortion_of_continuous_flow Exp hExp d hd hd0 hmul
    (fun t v => Real.exp (-t) • (NormedSpace.exp (t • N)) v)
    (C := ((c : ℝ) + 1) * (1 + ‖N‖) ^ c) (by positivity) c hconj
    (fun v _ ht => norm_contracted_nilpotent_flow_le N hN v ht)

/-- The same distortion conclusion stated directly for a generator whose
nilpotent part is `N` and whose real weight is `-1`. -/
theorem logarithmic_distortion_of_weight_generator
    {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] [Nontrivial V] [ProperSpace V]
    (Exp : V → G) (hExp : Continuous Exp)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (N : V →L[ℝ] V) {c : ℕ} (hN : N ^ (c + 1) = 0)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp ((NormedSpace.exp (t • (N - 1))) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  apply logarithmic_distortion_of_nilpotent_flow Exp hExp d hd hd0 hmul N hN
  intro v t ht
  have hh := hconj v t ht
  rw [exp_smul_sub_one N t] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_AlgebraExponential
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Algebra exponentials as actual group elements

The unit-valued exponential keeps the inverse explicit. This bridges the
operator conjugation identity to a faithful group representation.
-/

noncomputable section

namespace PolycyclicRecognition

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem algebraExpUnit_add_of_commute {x y : A} (hxy : Commute x y) :
    algebraExpUnit (x + y) = algebraExpUnit x * algebraExpUnit y := by
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  apply Units.ext
  exact NormedSpace.exp_add_of_commute hxy

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorConjugation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual group words realizing a basis of generator conjugates

A faithful exponential-compatible representation turns the operator words
from `GeneratorOrbit` into conjugation by finite words in generator
one-parameter subgroups. No generation or submersion assertion is assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

variable {G : Type} [Group G] (X : I → L) (Exp : L → G)

variable (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
  (hExp : ∀ x, ρ (Exp x) = algebraExpUnit (j x))

attribute [local instance] OAI.PolycyclicRecognition.generatorConjugationNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.generatorConjugationNormedSpace
include hρ hExp in
/-- The whole operator word is conjugation by its matching group word. -/
theorem exp_adjointWord_eq_group_conjugation (w : List (I × ℝ)) (v : L) :
    Exp (generatorAdjointWord X w v) =
      generatorGroupWord X Exp w * Exp v * (generatorGroupWord X Exp w)⁻¹ := by
  induction w with
  | nil => simp
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    rw [generatorAdjointWord_cons, generatorGroupWord_cons]
    change Exp (NormedSpace.exp (t • continuousAd (X i)) (generatorAdjointWord X w v)) = _
    rw [exp_ad_eq_group_conjugation Exp j ρ hρ hExp, ih]
    group

include hρ hExp in
/-- Every finite-dimensional generated algebra has a basis of directions
whose full one-parameter subgroups are generator-word conjugates. -/
theorem exists_generatorGroupWord_basis
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤) :
    ∃ (b : Basis (Fin (finrank ℝ L)) ℝ L)
      (w : Fin (finrank ℝ L) → List (I × ℝ)) (i : Fin (finrank ℝ L) → I),
      ∀ k (t : ℝ), Exp (t • b k) =
        generatorGroupWord X Exp (w k) * Exp (t • X (i k)) *
          (generatorGroupWord X Exp (w k))⁻¹ := by
  obtain ⟨b, w, i, hb⟩ := exists_generatorOrbit_basis X hX
  refine ⟨b, w, i, ?_⟩
  intro k t
  rw [← hb k, ← map_smul]
  exact exp_adjointWord_eq_group_conjugation X Exp j ρ hρ hExp (w k) (t • X (i k))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_FiniteLieSmooth
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Smoothness of finite Lie polynomials

A finite-dimensional Lie bracket is a continuous bilinear map in basis
coordinates. Consequently the actual finite Dynkin expressions are smooth;
no smoothness of a chosen logarithm chart is assumed here.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {I : Type} {n : ℕ∞}

attribute [local instance] OAI.PolycyclicRecognition.finiteLieSmoothNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.finiteLieSmoothNormedSpace
/-- Any fixed evaluated bracket word in smooth input functions is smooth. -/
theorem contDiff_evalBracketWord (X : V → I → L)
    (hX : ∀ i, ContDiff ℝ n (fun v => X v i)) (w : FreeMagma I) :
    ContDiff ℝ n (fun v => evalBracketWord (X v) w) := by
  induction w using FreeMagma.rec with
  | of i => exact hX i
  | mul a b ha hb =>
    exact (finiteLieBracket.contDiff.comp ha).clm_apply hb

/-- The finite published Dynkin expression is smooth in all its logarithms. -/
theorem contDiff_finiteDynkinPolynomial {c k : ℕ} (coeff : DynkinCoefficients c k)
    (X : V → Fin k → L) (hX : ∀ i, ContDiff ℝ n (fun v => X v i)) :
    ContDiff ℝ n (fun v => finiteDynkinPolynomial coeff (X v)) := by
  apply ContDiff.sum
  intro d _
  apply ContDiff.sum
  intro w _
  exact (contDiff_evalBracketWord X hX (rightNestedWord d.val w)).const_smul _

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialProductChart
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local product charts from the finite Dynkin identity

Products of exponentials in a basis have a locally surjective logarithm map.
The proof gets smoothness from the finite Dynkin polynomial and its derivative
from the exact one-coordinate restrictions. No smooth-logarithm or local
product assertion is a separate input.
-/

noncomputable section

namespace PolycyclicRecognition

open Module Set Filter
open scoped Topology ContDiff

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

attribute [local instance] OAI.PolycyclicRecognition.exponentialProductNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.exponentialProductNormedSpace
variable {G : Type} [Group G] {n : ℕ} (Exp : L → G) (b : Basis (Fin n) ℝ L)

variable (hExp : Function.Bijective Exp) (hzero : Exp 0 = 1)

include hExp in
/-- The exact polynomial identity supplies all differentiability of the
logarithmic endpoint map. -/
theorem contDiff_basisProductLog {c : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → L, (List.ofFn (fun i => Exp (X i))).prod =
      Exp (finiteDynkinPolynomial coeff X)) :
    ContDiff ℝ ∞ (basisProductLog Exp b hExp) := by
  have he : basisProductLog Exp b hExp =
      fun t => finiteDynkinPolynomial coeff (fun i => t i • b i) := by
    funext t
    apply hExp.injective
    exact ((Equiv.ofBijective Exp hExp).apply_symm_apply _).trans (hprod _)
  rw [he]
  exact contDiff_finiteDynkinPolynomial coeff _
    (fun i => (contDiff_apply ℝ ℝ i).smul contDiff_const)

include hzero in
/-- The differential of the logarithmic endpoint map at the origin is the
basis synthesis map, proved from its coordinate-axis restrictions. -/
theorem fderiv_basisProductLog_zero
    (hd : DifferentiableAt ℝ (basisProductLog Exp b hExp) 0) :
    fderiv ℝ (basisProductLog Exp b hExp) 0 = b.equivFun.symm.toContinuousLinearEquiv := by
  apply ContinuousLinearMap.ext
  intro t
  have hcol (i : Fin n) :
      fderiv ℝ (basisProductLog Exp b hExp) 0 (Pi.single i 1) = b i := by
    have h := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ)
      (hasDerivAt_single i (0 : ℝ)) (by simp)
    have he : (fun s : ℝ => basisProductLog Exp b hExp (Pi.single i s)) =
        fun s => s • b i := by funext s; exact basisProductLog_single Exp b hExp hzero i s
    change HasDerivAt (fun s : ℝ => basisProductLog Exp b hExp (Pi.single i s)) _ 0 at h
    rw [he] at h
    exact h.unique (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const (b i))
  calc
    _ = fderiv ℝ (basisProductLog Exp b hExp) 0
        (∑ i, t i • Pi.single i (1 : ℝ)) := congrArg _ (pi_eq_sum_univ' t)
    _ = ∑ i, t i • b i := by simp only [map_sum, map_smul, hcol]
    _ = _ := by
      change (∑ i, t i • b i) = b.equivFun.symm t
      simpa only [LinearEquiv.apply_symm_apply] using b.sum_equivFun (b.equivFun.symm t)

include hzero in
/-- The basis exponential map covers a logarithmic neighborhood using
parameters from any prescribed neighborhood of zero. -/
theorem basisProductLog_map_nhds {c : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → L, (List.ofFn (fun i => Exp (X i))).prod =
      Exp (finiteDynkinPolynomial coeff X)) :
    map (basisProductLog Exp b hExp) (𝓝 0) = 𝓝 (0 : L) := by
  have hc := contDiff_basisProductLog Exp b hExp coeff hprod
  have hf : ContDiffAt ℝ 1 (basisProductLog Exp b hExp) 0 :=
    hc.contDiffAt.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞)
  have he := fderiv_basisProductLog_zero Exp b hExp hzero
    (hf.differentiableAt one_ne_zero)
  have hs := (hf.hasStrictFDerivAt one_ne_zero).map_nhds_eq_of_surj
    (by rw [he]; exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective)
  simpa only [basisProductLog_zero Exp b hExp hzero] using hs

include hzero in
/-- A fixed parameter ball suffices for a nonzero logarithmic ball. -/
theorem exists_ball_subset_basisProductLog_image {c : ℕ} (coeff : DynkinCoefficients c n)
    (hprod : ∀ X : Fin n → L, (List.ofFn (fun i => Exp (X i))).prod =
      Exp (finiteDynkinPolynomial coeff X)) :
    ∃ ε : ℝ, 0 < ε ∧ Metric.ball (0 : L) ε ⊆
      basisProductLog Exp b hExp '' Metric.ball (0 : Fin n → ℝ) 1 := by
  have hm := basisProductLog_map_nhds Exp b hExp hzero coeff hprod
  have him : basisProductLog Exp b hExp '' Metric.ball (0 : Fin n → ℝ) 1 ∈ 𝓝 (0 : L) := by
    rw [← hm]
    exact Filter.image_mem_map (Metric.ball_mem_nhds _ zero_lt_one)
  exact Metric.mem_nhds_iff.mp him

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_GeneratorSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite generator schemes with locally open endpoint maps

A conjugated-generator basis gives a single finite scheme, with fixed
conjugating words, whose endpoint map covers a neighborhood of the identity.
The logarithm of that map has the identity-rank differential proved from BCH.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type} [Group G]

variable (X : I → L) (Exp : L → G)

attribute [local instance] OAI.PolycyclicRecognition.generatorSchemeNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.generatorSchemeNormedSpace
theorem generatorGroupWord_append (u v : List (I × ℝ)) :
    generatorGroupWord X Exp (u ++ v) =
      generatorGroupWord X Exp u * generatorGroupWord X Exp v := by
  simp only [generatorGroupWord, List.map_append, List.prod_append]

theorem generatorGroupWord_inverse (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (w : List (I × ℝ)) :
    generatorGroupWord X Exp (inverseGeneratorWord w) = (generatorGroupWord X Exp w)⁻¹ := by
  induction w with
  | nil => simp [inverseGeneratorWord]
  | cons p w ih =>
    rcases p with ⟨i, t⟩
    simp only [inverseGeneratorWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, generatorGroupWord_append, generatorGroupWord_cons,
      generatorGroupWord_nil, mul_one, mul_inv_rev] at *
    rw [ih]
    congr 1
    simpa only [neg_smul] using hneg (t • X i)

/-- The word length is fixed even though the inserted amplitudes vary. -/
theorem length_generatorSchemeWord {n : ℕ} (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (t : Fin n → ℝ) :
    (generatorSchemeWord w i t).length = ∑ k, (2 * (w k).length + 1) := by
  simp [generatorSchemeWord, inverseGeneratorWord, List.length_flatten,
    List.map_ofFn, List.sum_ofFn]
  congr 1
  funext k
  omega

/-- Endpoint of the expanded scheme is exactly the product in the chosen
basis directions. -/
theorem generatorScheme_endpoint {n : ℕ}
    (b : Basis (Fin n) ℝ L) (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (hb : ∀ k (s : ℝ), Exp (s • b k) =
      generatorGroupWord X Exp (w k) * Exp (s • X (i k)) *
        (generatorGroupWord X Exp (w k))⁻¹)
    (t : Fin n → ℝ) :
    generatorGroupWord X Exp (generatorSchemeWord w i t) = basisExponentialProduct Exp b t := by
  unfold generatorSchemeWord generatorGroupWord
  rw [List.map_flatten, List.prod_flatten, List.map_map, List.map_ofFn]
  change (List.ofFn (fun k => generatorGroupWord X Exp
    (w k ++ [(i k, t k)] ++ inverseGeneratorWord (w k)))).prod = _
  congr 1
  apply congrArg List.ofFn
  funext k
  rw [generatorGroupWord_append, generatorGroupWord_append, generatorGroupWord_inverse X Exp hneg]
  simpa only [generatorGroupWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one] using (hb k (t k)).symm

variable {A : Type} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual finite scheme and a neighborhood covered with bounded
variable amplitudes. All the hypotheses are algebraic representation/BCH
identities; local surjectivity is proved, not assumed. -/
theorem exists_local_generator_scheme
    (hX : LieSubalgebra.lieSpan ℝ L (Set.range X) = ⊤)
    (hExp : Function.Bijective Exp) (hzero : Exp 0 = 1)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x))
    {c : ℕ} (coeff : DynkinCoefficients c (finrank ℝ L))
    (hprod : ∀ Z : Fin (finrank ℝ L) → L,
      (List.ofFn (fun k => Exp (Z k))).prod = Exp (finiteDynkinPolynomial coeff Z)) :
    ∃ (w : Fin (finrank ℝ L) → List (I × ℝ)) (i : Fin (finrank ℝ L) → I)
      (ε : ℝ), 0 < ε ∧ ∀ v : L, ‖v‖ < ε →
      ∃ t : Fin (finrank ℝ L) → ℝ, ‖t‖ < 1 ∧
        generatorGroupWord X Exp (generatorSchemeWord w i t) = Exp v := by
  obtain ⟨b, w, i, hb⟩ := exists_generatorGroupWord_basis X Exp j ρ hρ hmatch hX
  obtain ⟨ε, hε, hcover⟩ := exists_ball_subset_basisProductLog_image Exp b hExp hzero coeff hprod
  refine ⟨w, i, ε, hε, ?_⟩
  intro v hv
  obtain ⟨t, ht, he⟩ := hcover (by simpa only [Metric.mem_ball, dist_zero_right] using hv)
  refine ⟨t, by simpa only [Metric.mem_ball, dist_zero_right] using ht, ?_⟩
  rw [generatorScheme_endpoint X Exp b w i hneg hb]
  exact ((Equiv.ofBijective Exp hExp).apply_symm_apply _).symm.trans (congrArg Exp he)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_BoundedGeneratorSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Quantitative bounds for a fixed generator scheme

The fixed conjugating words give a common amplitude bound; scaling a
logarithm into the local product chart and repeating the resulting word
covers any prescribed bounded logarithmic set.
-/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {I : Type}

/-- Amplitudes in every fixed conjugating word admit one finite bound. -/
theorem exists_fixed_word_amplitude_bound {n : ℕ} (w : Fin n → List (I × ℝ)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k, ∀ p ∈ w k, |p.2| ≤ C := by
  let S := (List.ofFn w).flatten
  let C := 1 + (S.map (fun p => |p.2|)).sum
  have hnonneg : ∀ x ∈ S.map (fun p => |p.2|), (0 : ℝ) ≤ x := by
    intro x hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _
  refine ⟨C, by dsimp [C] <;> linarith [List.sum_nonneg hnonneg], ?_⟩
  intro k p hp
  have hpS : p ∈ S := by
    exact List.mem_flatten.mpr ⟨w k, List.mem_ofFn.mpr ⟨k, rfl⟩, hp⟩
  have h := List.single_le_sum hnonneg |p.2| (List.mem_map.mpr ⟨p, hpS, rfl⟩)
  dsimp [C]
  linarith

/-- Inserting unit-bounded parameters keeps every amplitude uniformly bounded. -/
theorem generatorSchemeWord_amplitude_bound {n : ℕ} (w : Fin n → List (I × ℝ))
    (i : Fin n → I) {C : ℝ} (hC : 1 ≤ C)
    (hw : ∀ k, ∀ p ∈ w k, |p.2| ≤ C) (t : Fin n → ℝ) (ht : ‖t‖ ≤ 1) :
    ∀ p ∈ generatorSchemeWord w i t, |p.2| ≤ C := by
  intro p hp
  obtain ⟨s, hs, hp⟩ := List.mem_flatten.mp hp
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hs
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · exact hw k p hp
    · have he : p = (i k, t k) := by simpa using hp
      rw [he]
      exact ((Real.norm_eq_abs _ ▸ norm_le_pi_norm t k).trans ht).trans hC
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have hq' : q ∈ w k := List.mem_reverse.mp hq
    simpa only [abs_neg] using hw k q hq'

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {G : Type} [Group G]

variable (X : I → L) (Exp : L → G)

attribute [local instance] OAI.PolycyclicRecognition.boundedSchemeNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.boundedSchemeNormedSpace
/-- The one-parameter identity identifies integer multiples with group powers. -/
theorem exp_nat_smul (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    (v : L) (k : ℕ) : Exp ((k : ℝ) • v) = (Exp v) ^ k := by
  induction k with
  | zero => simp [hzero]
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, hadd, ih, one_smul, pow_succ]

/-- Any bounded logarithmic set is covered by words of uniformly bounded
length and uniformly bounded generator amplitudes, for a fixed local scheme. -/
theorem bounded_generation_of_local_scheme {n : ℕ}
    (w : Fin n → List (I × ℝ)) (i : Fin n → I)
    (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    {ε : ℝ} (hε : 0 < ε)
    (hlocal : ∀ v : L, ‖v‖ < ε → ∃ t : Fin n → ℝ, ‖t‖ < 1 ∧
      generatorGroupWord X Exp (generatorSchemeWord w i t) = Exp v)
    (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ v : L, ‖v‖ ≤ R →
      ∃ u : List (I × ℝ), u.length ≤ N ∧ (∀ p ∈ u, |p.2| ≤ C) ∧
        generatorGroupWord X Exp u = Exp v := by
  obtain ⟨C, hC, hw⟩ := exists_fixed_word_amplitude_bound w
  obtain ⟨k, hk⟩ := exists_nat_gt (max (R / ε) 0)
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (le_max_right _ _) hk
  have hkR : R < (k : ℝ) * ε := by
    have h := lt_of_le_of_lt (le_max_left (R / ε) 0) hk
    exact (div_lt_iff₀ hε).mp h
  refine ⟨k * ∑ j, (2 * (w j).length + 1), C, hC, ?_⟩
  intro v hv
  have hsmall : ‖((k : ℝ)⁻¹) • v‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0)]
    have h := lt_of_le_of_lt hv hkR
    rw [← div_eq_inv_mul]
    exact (div_lt_iff₀ hk0).mpr (by simpa only [mul_comm] using h)
  obtain ⟨t, ht, he⟩ := hlocal _ hsmall
  let u := generatorSchemeWord w i t
  refine ⟨(List.replicate k u).flatten, ?_, ?_, ?_⟩
  · simp only [List.length_flatten, List.map_replicate, List.sum_replicate]
    rw [length_generatorSchemeWord]
    simp
  · intro p hp
    obtain ⟨s, hs, hp⟩ := List.mem_flatten.mp hp
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hs
    exact generatorSchemeWord_amplitude_bound w i hC hw t ht.le p hp
  · have hprod : generatorGroupWord X Exp ((List.replicate k u).flatten) =
        (generatorGroupWord X Exp u) ^ k := by
      simp only [generatorGroupWord, List.map_flatten, List.map_replicate,
        List.prod_flatten, List.prod_replicate]
    rw [hprod, he, ← exp_nat_smul Exp hzero hadd]
    congr 1
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hk0), one_smul]

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_CoordinateHomLinear
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Continuous homomorphisms in smooth exponential coordinates

Only differentiability of multiplication at the identity, its two unit
identities, and the straight-line one-parameter law are needed. The scaling
limit of multiplication proves additivity without an automatic-smoothness
assumption on the homomorphism.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The derivative of exponential-coordinate multiplication at the origin
is addition, by differentiating its unit identities along the two axes. -/
theorem hasDerivAt_scaled_product (m : V → V → V)
    (hm : DifferentiableAt ℝ (fun p : V × V => m p.1 p.2) (0, 0))
    (hleft : ∀ x, m 0 x = x) (hright : ∀ x, m x 0 = x) (x y : V) :
    HasDerivAt (fun t : ℝ => m (t • x) (t • y)) (x + y) 0 := by
  let T := fderiv ℝ (fun p : V × V => m p.1 p.2) (0, 0)
  have hd : HasFDerivAt (fun p : V × V => m p.1 p.2) T (0, 0) := hm.hasFDerivAt
  have hx : T (x, 0) = x := by
    have h := hd.comp_hasDerivAt_of_eq 0
      (((hasDerivAt_id (0 : ℝ)).smul_const x).prodMk (hasDerivAt_const 0 (0 : V)))
      (by simp)
    simp only [Function.comp_def, hright] at h
    simpa only [one_smul] using h.unique (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const x)
  have hy : T (0, y) = y := by
    have h := hd.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_const 0 (0 : V)).prodMk ((hasDerivAt_id (0 : ℝ)).smul_const y))
      (by simp)
    simp only [Function.comp_def, hleft] at h
    simpa only [one_smul] using h.unique (by simpa using (hasDerivAt_id (0 : ℝ)).smul_const y)
  have h := hd.comp_hasDerivAt_of_eq 0
    (((hasDerivAt_id (0 : ℝ)).smul_const x).prodMk
      ((hasDerivAt_id (0 : ℝ)).smul_const y)) (by simp)
  have hT : T (x, y) = x + y := by
    rw [show (x, y) = (x, 0) + (0, y) by simp, map_add, hx, hy]
  simpa only [Function.comp_def, id_eq, one_smul, hT] using h

/-- A continuous multiplicative-coordinate map which is linear on each
radial line is additive, hence defines a continuous real-linear map. -/
theorem exists_linearMap_of_coordinate_hom (m : V → V → V)
    (hm : DifferentiableAt ℝ (fun p : V × V => m p.1 p.2) (0, 0))
    (hleft : ∀ x, m 0 x = x) (hright : ∀ x, m x 0 = x)
    (f : V → W) (hf : Continuous f)
    (hmul : ∀ x y, f (m x y) = f x + f y)
    (hsmul : ∀ (t : ℝ) x, f (t • x) = t • f x) :
    ∃ A : V →L[ℝ] W, ∀ x, A x = f x := by
  have hadd (x y : V) : f (x + y) = f x + f y := by
    have hd := hasDerivAt_scaled_product m hm hleft hright x y
    have hlim : Tendsto (fun t : ℝ => t⁻¹ • m (t • x) (t • y))
        (𝓝[≠] 0) (𝓝 (x + y)) := by
      simpa only [zero_add, zero_smul, hleft, sub_zero] using hd.tendsto_slope_zero
    have hfLim := (hf.continuousAt (x := x + y)).tendsto.comp hlim
    have hevent : (fun t : ℝ => f (t⁻¹ • m (t • x) (t • y))) =ᶠ[𝓝[≠] 0]
        (fun _ => f x + f y) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : t ≠ 0 := ht
      rw [hsmul, hmul, hsmul, hsmul, ← smul_add, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    exact tendsto_nhds_unique hfLim (tendsto_const_nhds.congr' hevent.symm)
  exact ⟨{ toLinearMap := { toFun := f, map_add' := hadd, map_smul' := hsmul }
           cont := hf }, fun _ => rfl⟩

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootFlow
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Logarithmic distortion in Cartan root spaces

Generalized root spaces determine the nilpotent correction to the scalar
weight action. A compatible group conjugation identity then gives logarithmic
distortion.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

variable {L : Type} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)

attribute [local instance] OAI.PolycyclicRecognition.rootNormedAddCommGroup
attribute [local instance] OAI.PolycyclicRecognition.rootNormedSpace
attribute [local instance] OAI.PolycyclicRecognition.rootNontrivial
theorem rootAction_nilpotent_correction (h : H) :
    _root_.IsNilpotent (rootAction H χ h - χ h • 1) := by
  have hn := isNilpotent_toEnd_sub_algebraMap L (χ : H → ℝ) h
  obtain ⟨k, hk⟩ := hn
  refine ⟨k, ?_⟩
  have hm := congrArg (Module.End.toContinuousLinearMap (𝕜 := ℝ) (rootSpace H χ)) hk
  simpa only [map_pow, map_sub, Algebra.algebraMap_eq_smul_one,
    map_smul, map_one, map_zero, rootAction] using hm

/-- Each nonzero real root has a direction where its value is `-1`. -/
theorem exists_contracting_root_direction (hχ : χ.IsNonZero) :
    ∃ h : H, χ h = -1 := by
  have hn : ∃ h : H, χ h ≠ 0 := by
    by_contra! hn
    apply hχ
    exact funext hn
  obtain ⟨h, hh⟩ := hn
  refine ⟨(-(χ h)⁻¹) • h, ?_⟩
  rw [map_smul]
  change -(χ h)⁻¹ * χ h = -1
  rw [neg_mul, inv_mul_cancel₀ hh]

/-- Logarithmic distortion follows for an integrated nonzero root chart.
No semisimplicity or diagonal adjoint action is assumed. -/
theorem root_logarithmic_distortion
    {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    (Exp : (rootSpace H χ) → G) (hExp : Continuous Exp)
    (h : H) (hh : χ h = -1)
    (d : ℝ → G) (hd : Continuous d) (hd0 : d 0 = 1)
    (hmul : ∀ s t, d (s + t) = d s * d t)
    (hconj : ∀ v t, 0 ≤ t → Exp v =
      d t * Exp ((NormedSpace.exp (t • rootAction H χ h)) v) * (d t)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  let N := rootAction H χ h + 1
  have hnil : _root_.IsNilpotent N := by
    simpa only [hh, neg_smul, one_smul, sub_neg_eq_add, N] using
      rootAction_nilpotent_correction H χ h
  obtain ⟨k, hk⟩ := hnil
  have hk' : N ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  apply logarithmic_distortion_of_weight_generator Exp hExp d hd hd0 hmul N hk'
  simpa only [N, add_sub_cancel_right] using hconj

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_RootRepresentation
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Root distortion in a faithful integrated representation

The conjugation identity is proved from a Lie homomorphism into a normed
algebra and the ordinary exponential matching identities. It is not an
additional geometric hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {L : Type} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {A : Type} [NormedRing A] [NormedAlgebra ℝ A]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra] (χ : Weight ℝ H L)
  (j : L →ₗ⁅ℝ⁆ A)

theorem representedRootVector_intertwines (h : H) (v : rootSpace H χ) :
    representedRootVector H χ j (rootAction H χ h v) =
      adjointOperator (j h) (representedRootVector H χ j v) := by
  change j ⁅(h : L), (v : L)⁆ = j h * j v - j v * j h
  rw [j.map_lie, Ring.lie_def]

variable [CompleteSpace A]

/-- The restricted root action exponentiates to actual matrix conjugation. -/
theorem represented_root_flow (h : H) (t : ℝ) (v : rootSpace H χ) :
    representedRootVector H χ j ((NormedSpace.exp (t • rootAction H χ h)) v) =
      NormedSpace.exp (t • j h) * j v * NormedSpace.exp (-(t • j h)) := by
  have hi := exp_intertwine_apply (representedRootVector H χ j)
    (t • rootAction H χ h) (t • adjointOperator (j h)) (by
      intro v
      simp only [smul_apply, map_smul, representedRootVector_intertwines]) v
  rw [exp_smul_adjointOperator_apply] at hi
  exact hi

theorem represented_root_exp_conjugation (h : H) (t : ℝ) (v : rootSpace H χ) :
    algebraExpUnit (j (((NormedSpace.exp (t • rootAction H χ h)) v : rootSpace H χ) : L)) =
      algebraExpUnit (t • j h) * algebraExpUnit (j v) * (algebraExpUnit (t • j h))⁻¹ := by
  change algebraExpUnit (representedRootVector H χ j
    ((NormedSpace.exp (t • rootAction H χ h)) v)) = _
  rw [represented_root_flow]
  exact algebraExpUnit_conj (algebraExpUnit (t • j h)) (j v)

theorem represented_root_exp_inverse_conjugation
    (h : H) (t : ℝ) (v : rootSpace H χ) :
    algebraExpUnit (j v) = algebraExpUnit (-(t • j h)) *
      algebraExpUnit (j (((NormedSpace.exp (t • rootAction H χ h)) v : rootSpace H χ) : L)) *
        (algebraExpUnit (-(t • j h)))⁻¹ := by
  rw [represented_root_exp_conjugation, algebraExpUnit_neg]
  simp only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

/-- In an integrated faithful representation, logarithmic root distortion
requires only the exponential matching data. -/
theorem represented_root_logarithmic_distortion
    {G : Type} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (Exp : (rootSpace H χ) → G) (hExp : Continuous Exp)
    (h : H) (hh : χ h = -1) (d : ℝ → G) (hd : Continuous d)
    (hExpρ : ∀ v, ρ (Exp v) = algebraExpUnit (j v))
    (hdρ : ∀ t, ρ (d t) = algebraExpUnit (-(t • j h))) :
    ∃ D : ℝ, 0 < D ∧ ∀ v, dist 1 (Exp v) ≤ D * Real.log (2 + ‖v‖) := by
  have hd0 : d 0 = 1 := by
    apply hρ
    simp only [hdρ, zero_smul, neg_zero, algebraExpUnit_zero, map_one]
  have hmul : ∀ s t, d (s + t) = d s * d t := by
    intro s t
    apply hρ
    rw [map_mul, hdρ, hdρ, hdρ]
    have hc : Commute (-(s • j h)) (-(t • j h)) := by
      exact (((Commute.refl (j h)).smul_left s).smul_right t).neg_left.neg_right
    rw [← algebraExpUnit_add_of_commute hc]
    congr 1
    module
  apply root_logarithmic_distortion H χ Exp hExp h hh d hd hd0 hmul
  intro v t _
  apply hρ
  simp only [map_mul, map_inv, hExpρ, hdρ]
  exact represented_root_exp_inverse_conjugation H χ j h t v

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanFactorHeight
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical height of the constructed Cartan factors

The nilpotent root factor has zero height. The Cartan logarithm records the
height of every lifted prefix exactly, not just up to bounded error.
-/

noncomputable section

namespace PolycyclicRecognition.CartanFactorModel

open scoped Manifold

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  {W : Type} [AddCommGroup W] [Module ℝ W]
  (q : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = q (heightProjection T.character x))

set_option maxHeartbeats 1000000 in
include hπExp in
/-- The root ideal lies in the canonical height kernel, hence so does its
entire integrated group. -/
theorem inclusionN_height_eq_one
    (hbij : Function.Bijective F.ExpN) (n : F.N.carrier) :
    π (F.inclusionN n) = 1 := by
  obtain ⟨x, rfl⟩ := (hbij.comp F.N.equiv.bijective).surjective n
  change π (F.inclusionN (F.ExpN (F.N.equiv x))) = 1
  rw [F.compatibleN]
  change (π (ExpG x)).toAdd = 0
  rw [hπExp]
  have hz : heightProjection T.character (x : GroupLieAlgebra (𝓘(ℝ, EG)) G) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (cartanRootIdeal_le_kernel H T x.property)
  rw [hz, map_zero]

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_PublishedRootDistortion
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Actual root distortion from the published linear realization

All contraction, continuity, and conjugation premises of the root-space
distortion theorem are now discharged for the ambient Lie group. Only the
already recorded faithful exponential-realization input remains assumed.
-/

noncomputable section

namespace PolycyclicRecognition

open LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] rootNormedAddCommGroup rootNormedSpace rootNontrivial

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- Every actual nonzero Cartan root space is logarithmically distorted
in the ambient metric. -/
theorem root_distortion_of_published_realization
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G)) :
    ∃ D : ℝ, 0 < D ∧ ∀ v : rootSpace H χ,
      dist 1 (Exp v) ≤ D * Real.log (2 + ‖(rootCoordinates H χ) v‖) := by
  let : TopologicalSpace (rootSpace H χ) :=
    (rootNormedAddCommGroup H χ).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨m, hm, ρ, j, hind, hmatch⟩ := realize ⟨a, ⟨T⟩⟩ Exp hExp
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨h, hh⟩ := exists_contracting_root_direction H χ hχ
  let d : ℝ → G := fun t => Exp (-(t • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
  have hEr : Continuous (fun v : rootSpace H χ => Exp v) := by
    apply hind.continuous_iff.mpr
    change Continuous (fun v : rootSpace H χ => (ρ (Exp v) : Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch]
    exact Units.continuous_val.comp
      (algebraExpUnit_continuous.comp (representedRootVector H χ j).continuous)
  have hd : Continuous d := by
    apply hind.continuous_iff.mpr
    change Continuous (fun t : ℝ => (ρ (Exp (-(t • (h : GroupLieAlgebra (𝓘(ℝ, EG)) G)))) :
      Matrix (Fin m) (Fin m) ℝ))
    simp_rw [hmatch, map_neg, map_smul]
    exact Units.continuous_val.comp (algebraExpUnit_continuous.comp
      (continuous_id.smul continuous_const).neg)
  exact represented_root_logarithmic_distortion H χ j ρ hρ
    (fun v => Exp v) hEr h hh d hd (fun v => hmatch v)
    (fun t => by simp only [d, hmatch, map_neg, map_smul])

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Algebra_DistortedHomomorphisms
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Averaged homomorphisms vanish on logarithmically distorted flows

A continuous homomorphism is linear on each one-parameter subgroup. A
linear metric bound and logarithmic distortion force that linear value to
vanish. In particular, the stationary mean kills the actual root flows.
-/

noncomputable section

namespace PolycyclicRecognition

open Filter LieAlgebra LieModule
open scoped Topology Manifold

section Flow

variable {G W : Type} [Group G] [PseudoMetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The image of a continuous one-parameter subgroup under a continuous
homomorphism is a real-linear one-parameter subgroup. -/
theorem hom_flow_eq_smul
    (d : ℝ → G) (hd : Continuous d) (hd₀ : d 0 = 1)
    (hdadd : ∀ s t, d (s + t) = d s * d t)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd) (t : ℝ) :
    (l (d t)).toAdd = t • (l (d 1)).toAdd := by
  let a : ℝ →+ W := {
    toFun t := (l (d t)).toAdd
    map_zero' := by rw [hd₀, map_one]; rfl
    map_add' := fun s t => by rw [hdadd, map_mul]; rfl }
  have ha : Continuous a := hl.comp hd
  have h := (a.toRealLinearMap ha).map_smul t (1 : ℝ)
  change a t = t • a 1
  change a (t • (1 : ℝ)) = t • a 1 at h
  simpa only [smul_eq_mul, mul_one] using h

/-- Linear metric control precludes a nonzero homomorphism on a flow of
logarithmic ambient size. -/
theorem hom_eq_one_of_logarithmic_flow
    (d : ℝ → G) (hd : Continuous d) (hd₀ : d 0 = 1)
    (hdadd : ∀ s t, d (s + t) = d s * d t)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L D B : ℝ} (hL : 0 ≤ L) (hB : 0 < B)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hdist : ∀ t, dist 1 (d t) ≤ D * Real.log (2 + B * |t|)) :
    ∀ t, l (d t) = 1 := by
  have hscale := hom_flow_eq_smul d hd hd₀ hdadd l hl
  have hat : Tendsto (fun t : ℝ => 2 + B * t) atTop atTop := by
    apply tendsto_atTop.mpr
    intro x
    filter_upwards [eventually_ge_atTop ((x - 2) / B)] with t ht
    have hh := (div_le_iff₀ hB).mp ht
    nlinarith
  have hden (t : ℝ) : (1 / B) * (2 + B * t) + (-2 / B) = t := by
    field_simp
    ring
  have hlim : Tendsto (fun t : ℝ => L * D * Real.log (2 + B * t) / t) atTop (𝓝 0) := by
    have hh := (Real.tendsto_pow_log_div_mul_add_atTop (1 / B) (-2 / B) 1
      (one_div_ne_zero hB.ne')).comp hat
    change Tendsto (fun t : ℝ => Real.log (2 + B * t) ^ 1 /
      ((1 / B) * (2 + B * t) + (-2 / B))) atTop (𝓝 0) at hh
    simp only [pow_one, hden] at hh
    simpa only [mul_zero, mul_div_assoc] using hh.const_mul (L * D)
  have hle : ∀ᶠ t : ℝ in atTop,
      ‖(l (d 1)).toAdd‖ ≤ L * D * Real.log (2 + B * t) / t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have ht0 : 0 < t := by linarith
    have hb := (hbound (d t)).trans (mul_le_mul_of_nonneg_left (hdist t) hL)
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hb
    apply (le_div_iff₀ ht0).mpr
    nlinarith
  have hz : (l (d 1)).toAdd = 0 := norm_eq_zero.mp
    (le_antisymm (ge_of_tendsto hlim hle) (norm_nonneg _))
  intro t
  change (l (d t)).toAdd = 0
  rw [hscale, hz, smul_zero]

end Flow

variable {G W EG : Type} [Group G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

/-- Every continuous homomorphism with linear metric control kills the
root exponentials, using their logarithmic distortion. -/
theorem hom_eq_one_on_root_exp
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : LieModule.Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (v : rootSpace H χ) :
    ∀ t : ℝ, l (Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1 := by
  obtain ⟨D, hD, hb⟩ := root_distortion_of_published_realization T H χ hχ Exp hExp realize
  let B := 1 + ‖rootCoordinates H χ v‖
  have hB : 0 < B := by dsimp [B] <;> positivity
  apply hom_eq_one_of_logarithmic_flow
    (fun t : ℝ => Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (continuous_exp_line_of_published_realization T Exp hExp realize v)
    (by simp [hExp.map_zero])
    (fun s t => hExp.map_add_smul v s t) l hl hL hB hbound
  intro t
  have h := hb (t • v)
  have hn : 2 + ‖rootCoordinates H χ (t • v)‖ ≤ 2 + B * |t| := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    dsimp [B]
    nlinarith [abs_nonneg t]
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.log_le_log (by positivity) hn) hD.le)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Analysis_StationaryVolumeAlgebra
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.TangentSpace.instFiniteDimensionalCompat _root_.TangentSpace.instT2SpaceCompat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Algebraic consequences of stationary volume comparison

Once the forward volume comparison gives domination of segment supports,
the averaged homomorphism factors through canonical height by an invertible
linear map. The reverse comparison for the coupled inverse then makes this
map a support isometry. Neither conclusion is taken as a new hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V W : Type} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- A surjective quotient and a map to the same finite-dimensional target
with a smaller kernel differ by an invertible linear map. -/
theorem exists_linearEquiv_factor_of_kernel_le
    (π l : V →ₗ[ℝ] W) (hπ : Function.Surjective π) (hker : l.ker ≤ π.ker) :
    ∃ A : W ≃ₗ[ℝ] W, ∀ v, l v = A (π v) := by
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hsection (w : W) : π (s w) = w := by
    exact congrArg (fun f : W →ₗ[ℝ] W => f w) hs
  let A₀ : W →ₗ[ℝ] W := l.comp s
  have hinj : Function.Injective A₀ := by
    intro x y hxy
    have hl : s (x - y) ∈ l.ker := by
      change l (s (x - y)) = 0
      change l (s x) = l (s y) at hxy
      simpa only [map_sub, sub_eq_zero] using hxy
    have hp := hker hl
    change π (s (x - y)) = 0 at hp
    rw [hsection] at hp
    exact sub_eq_zero.mp hp
  have hsurj : Function.Surjective A₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  let A : W ≃ₗ[ℝ] W := LinearEquiv.ofBijective A₀ ⟨hinj, hsurj⟩
  refine ⟨A, ?_⟩
  intro v
  obtain ⟨w, hw⟩ := hsurj (l v)
  have hl : v - s w ∈ l.ker := by
    change l (v - s w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hw.symm
  have hp := hker hl
  change π (v - s w) = 0 at hp
  rw [map_sub, hsection] at hp
  rw [sub_eq_zero] at hp
  change l v = A₀ (π v)
  rw [hp, hw]

/-- The actual support norm turns the forward volume inequality into the
invertible height factor of the stationary slope. -/
theorem exists_linearEquiv_factor_of_support_domination
    {I B : Type} [Fintype I] [Fintype B] [Nonempty B]
    (D : SupportDatum W I B) (π l : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (hvol : ∀ v, D.segmentSupport (π v) ≤ D.segmentSupport (l v)) :
    ∃ A : W ≃ₗ[ℝ] W, ∀ v, l v = A (π v) := by
  apply exists_linearEquiv_factor_of_kernel_le π l hπ
  intro v hv
  have h := hvol v
  rw [LinearMap.mem_ker.mp hv, D.segmentSupport_zero] at h
  exact LinearMap.mem_ker.mpr ((D.segmentSupport_eq_zero_iff _).mp
    (le_antisymm h (D.segmentSupport_nonneg _)))

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanGeneratorSchemes
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.cartanWeightDerivation_apply_root _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.nilshadowWeightDerivation_symm _root_.OAI.PolycyclicRecognition.nilshadowWeightOperator_symm _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Local generator schemes for the actual Cartan nilpotent factor

The published faithful realization and finite Dynkin formula instantiate the
proved local generator scheme with the actual homogeneous Cartan generators.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

variable {EG G : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
include T in
/-- A concrete scheme in the homogeneous generator exponentials covers a
nonzero logarithmic neighborhood in the constructed nilpotent factor. -/
theorem exists_local_cartan_generator_scheme
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier) :
    ∃ (w : Fin (finrank ℝ (cartanRootIdeal H)) → List (Fin M.letterCount × ℝ))
      (i : Fin (finrank ℝ (cartanRootIdeal H)) → Fin M.letterCount)
      (ε : ℝ), 0 < ε ∧ ∀ v : cartanRootIdeal H,
      ‖(finBasis ℝ (cartanRootIdeal H)).equivFun v‖ < ε →
      ∃ t : Fin (finrank ℝ (cartanRootIdeal H)) → ℝ, ‖t‖ < 1 ∧
        generatorGroupWord M.letter (F.ExpN ∘ F.N.equiv) (generatorSchemeWord w i t) =
          F.ExpN (F.N.equiv v) := by
  obtain ⟨m, hm, ρ, j, hind, hExp⟩ := realize ⟨a, ⟨T⟩⟩ ExpG hExpG
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hρ : Function.Injective ρ := by
    intro g h he
    exact hind.injective (congrArg (fun u : (Matrix (Fin m) (Fin m) ℝ)ˣ =>
      (u : Matrix (Fin m) (Fin m) ℝ)) he)
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hbij : Function.Bijective (F.ExpN ∘ F.N.equiv) :=
    (funext hchartN ▸ chartN.bijective).comp F.N.equiv.bijective
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkinN F.N.equiv F.ExpN
    F.isExpN M.bound_zero (finrank ℝ (cartanRootIdeal H))
  exact exists_local_generator_scheme M.letter (F.ExpN ∘ F.N.equiv) M.generates
    hbij (by simp [F.isExpN.map_zero]) (fun v => by simp [F.isExpN.map_neg])
    (j.comp (cartanRootIdeal H).incl) (ρ.comp F.inclusionN)
    (hρ.comp F.closedN.injective) (fun v => by
      change ρ (F.inclusionN (F.ExpN (F.N.equiv v))) = _
      rw [F.compatibleN, hExp]
      rfl) coeff hprod

set_option maxHeartbeats 1000000 in
include T in
/-- A bounded logarithmic set in the actual Cartan factor has a common
finite bound on generator word length and on all amplitudes. -/
theorem exists_bounded_cartan_generator_words
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (R : ℝ) :
    ∃ (N : ℕ) (C : ℝ), 1 ≤ C ∧ ∀ v : cartanRootIdeal H,
      ‖(finBasis ℝ (cartanRootIdeal H)).equivFun v‖ ≤ R →
      ∃ u : List (Fin M.letterCount × ℝ), u.length ≤ N ∧
        (∀ p ∈ u, |p.2| ≤ C) ∧
        generatorGroupWord M.letter (F.ExpN ∘ F.N.equiv) u = F.ExpN (F.N.equiv v) := by
  obtain ⟨w, i, ε, hε, hlocal⟩ := M.exists_local_cartan_generator_scheme T F
    hExpG realize haarN dynkinN
  exact bounded_generation_of_local_scheme M.letter (F.ExpN ∘ F.N.equiv) w i
    (by simp [F.isExpN.map_zero]) (fun v s t => by
      simpa only [Function.comp_apply, map_smul] using F.isExpN.map_add_smul (F.N.equiv v) s t)
    hε hlocal R

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanHomKernel
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Vanishing on the actual Cartan root factor

Logarithmic distortion kills each root generator under a linearly bounded
continuous homomorphism. The proved generator schemes then kill the whole
constructed nilpotent factor, including every point of its group model.
-/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (hExp : IsGroupExponential Exp)
  (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
  (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
  {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)

include T M hExp realize hl hL hbound

set_option maxHeartbeats 1000000 in
/-- The actual homogeneous letters lie in the kernel. -/
theorem hom_eq_one_on_letter (i : Fin M.letterCount) (t : ℝ) :
    l (Exp (t • (M.letter i : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = 1 :=
  hom_eq_one_on_root_exp T H (M.weight i) (M.weight_nonzero i) Exp hExp realize
    l hl hL hbound ⟨M.letter i, M.letter_root i⟩ t

set_option maxHeartbeats 1000000 in
/-- Every exponential in the root ideal lies in the kernel. -/
theorem hom_eq_one_on_root_factor_exp
    (F : CartanFactorModel H Exp)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (v : cartanRootIdeal H) : l (F.inclusionN (F.ExpN (F.N.equiv v))) = 1 := by
  obtain ⟨_, _, _, hgen⟩ := M.exists_bounded_cartan_generator_words T F hExp realize
    haarN dynkinN ‖(finBasis ℝ (cartanRootIdeal H)).equivFun v‖
  obtain ⟨u, _, _, hu⟩ := hgen v le_rfl
  rw [← hu]
  unfold generatorGroupWord
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  have he : ∀ z ∈ u, l (F.inclusionN ((F.ExpN ∘ F.N.equiv) (z.2 • M.letter z.1))) = 1 := by
    intro z _
    rw [Function.comp_apply, F.compatibleN]
    exact M.hom_eq_one_on_letter T hExp realize l hl hL hbound z.1 z.2
  exact List.prod_eq_one (by simpa only [List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, Function.comp_apply] using he)

set_option maxHeartbeats 1000000 in
/-- Surjectivity of the intrinsic nilpotent exponential gives vanishing on
all points of the factor, not only its logarithmic coordinate model. -/
theorem hom_eq_one_on_root_factor
    (F : CartanFactorModel H Exp)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (n : F.N.carrier) : l (F.inclusionN n) = 1 := by
  obtain ⟨⟨chartN, hchartN⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  obtain ⟨x, hx⟩ := chartN.surjective n
  have hex : F.ExpN x = n := (hchartN x).symm.trans hx
  rw [← hex]
  simpa only [F.N.equiv.apply_symm_apply] using
    M.hom_eq_one_on_root_factor_exp T hExp realize l hl hL hbound F haarN dynkinN
      (F.N.equiv.symm x)

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_ExponentialHomLinear
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linearity of continuous homomorphisms on nilpotent logarithms -/

noncomputable section

namespace PolycyclicRecognition

open Module

variable {L G W : Type} [LieRing L] [LieAlgebra ℝ L] [Group G] [PseudoMetricSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Finite polynomial exponential coordinates and continuity suffice to
linearize a homomorphism into an additive real vector space. -/
theorem exists_linearMap_of_exponential_hom {n c : ℕ} (b : Basis (Fin n) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (hadd : ∀ x (s t : ℝ), Exp ((s + t) • x) = Exp (s • x) * Exp (t • x))
    (hcont : Continuous (fun x : Fin n → ℝ => Exp (b.equivFun.symm x)))
    (coeff : DynkinCoefficients c 2)
    (hmul : ∀ x y, Exp (finiteDynkinPolynomial coeff ![x, y]) = Exp x * Exp y)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd) :
    ∃ A : L →ₗ[ℝ] W, ∀ x, A x = (l (Exp x)).toAdd := by
  let m := dynkinProduct coeff (basisBracket b)
  let e : (Fin n → ℝ) → G := fun x => Exp (b.equivFun.symm x)
  have he : Function.Injective e := hinj.comp b.equivFun.symm.injective
  have hemul (x y : Fin n → ℝ) : e (m x y) = e x * e y := by
    have h := basis_dynkinProduct b coeff (b.equivFun.symm x) (b.equivFun.symm y)
    simp only [LinearEquiv.apply_symm_apply] at h
    dsimp only [e, m]
    rw [h, LinearEquiv.symm_apply_apply, hmul]
  have hleft (x : Fin n → ℝ) : m 0 x = x := by
    apply he
    rw [hemul]
    have h : e 0 = 1 := by simp [e, hzero]
    rw [h, one_mul]
  have hright (x : Fin n → ℝ) : m x 0 = x := by
    apply he
    rw [hemul]
    have h : e 0 = 1 := by simp [e, hzero]
    rw [h, mul_one]
  have hdiff : DifferentiableAt ℝ (fun p : (Fin n → ℝ) × (Fin n → ℝ) => m p.1 p.2) (0, 0) :=
    (contDiff_dynkinProduct (k := 1) coeff (fun _ => basisBracket b) Prod.fst Prod.snd
      contDiff_const contDiff_fst contDiff_snd).contDiffAt.differentiableAt (by norm_num)
  let f : (Fin n → ℝ) → W := fun x => (l (e x)).toAdd
  have hscale (t : ℝ) (x : Fin n → ℝ) : f (t • x) = t • f x := by
    have h := hom_flow_eq_smul (fun s : ℝ => e (s • x))
      (hcont.comp (continuous_id.smul continuous_const))
      (by simp [e, hzero])
      (fun s u => by simpa only [e, map_smul] using hadd (b.equivFun.symm x) s u) l hl t
    simpa only [f, one_smul] using h
  obtain ⟨A, hA⟩ := exists_linearMap_of_coordinate_hom m hdiff hleft hright f (hl.comp hcont)
    (fun x y => by dsimp [f]; rw [hemul, map_mul]; rfl) hscale
  refine ⟨A.toLinearMap.comp b.equivFun.toLinearMap, ?_⟩
  intro x
  change A (b.equivFun x) = _
  simpa only [f, e, LinearEquiv.symm_apply_apply] using hA (b.equivFun x)

end PolycyclicRecognition

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanHomLinear
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
attribute [-simp] _root_.OAI.PolycyclicRecognition.CartanFactorModel.heightRay_zero _root_.OAI.PolycyclicRecognition.CartanFactorModel.realScaleProfile_apply _root_.OAI.PolycyclicRecognition.CartanFactorModel.sampledProbeProfile_apply _root_.OAI.PolycyclicRecognition.basisDynkinParameter_zero _root_.OAI.PolycyclicRecognition.chartExponentialFlow_zero _root_.OAI.PolycyclicRecognition.derivationSemidirectHom_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_apply _root_.OAI.PolycyclicRecognition.dynkinRightTranslation_symm_apply _root_.OAI.PolycyclicRecognition.exponentialHomOfDynkin_apply_exp _root_.OAI.PolycyclicRecognition.induction_mk_left_inv _root_.OAI.PolycyclicRecognition.modelNilradicalLinearAction_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_apply _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_mul _root_.OAI.PolycyclicRecognition.modelNilradicalRotation_one _root_.OAI.PolycyclicRecognition.normalInductionMap_mk _root_.OAI.PolycyclicRecognition.normalQuotient_mk_subgroup _root_.OAI.PolycyclicRecognition.subgroupInductionMap_mk _root_.isStarNormal_unitary_coe _root_.isStarNormal_unitary_coe_toLin _root_.toIntLinearMap_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Linear logarithms of homomorphisms on the actual Cartan factor -/

noncomputable section

namespace PolycyclicRecognition.CartanFactorModel

open Module LieAlgebra LieModule
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

set_option maxHeartbeats 1000000 in
/-- A continuous additive-target homomorphism is real-linear on Cartan
logarithms, derived from the published finite BCH identity. -/
theorem exists_linearMap_on_cartan
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd) :
    ∃ A : H →ₗ[ℝ] W, ∀ v : H, A v = (l (Exp v)).toAdd := by
  let b := finBasis ℝ H
  let e : H → G := fun x => F.inclusionD (F.ExpD (F.D.equiv x))
  have he (x : H) : e x = Exp x := F.compatibleD x
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  have hinj : Function.Injective e :=
    F.closedD.injective.comp (hbijD.injective.comp F.D.equiv.injective)
  have hzero : e 0 = 1 := by simp [e, F.isExpD.map_zero]
  have hadd (x : H) (s t : ℝ) : e ((s + t) • x) = e (s • x) * e (t • x) := by
    simp only [e, map_smul, F.isExpD.map_add_smul, map_mul]
  have hcont : Continuous (fun x : Fin (finrank ℝ H) → ℝ => e (b.equivFun.symm x)) := by
    change Continuous (F.inclusionD ∘ F.ExpD ∘ F.D.equiv ∘ b.equivFun.symm)
    rw [← show chartD = F.ExpD from funext hchartD]
    exact F.closedD.continuous.comp (chartD.continuous.comp
      (F.D.equiv.toLinearMap.comp b.equivFun.symm.toLinearMap).continuous_of_finiteDimensional)
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℝ H H
  obtain ⟨coeff, _, hprod⟩ := model_finiteDynkinExpansion dynkinD F.D.equiv F.ExpD F.isExpD hc 2
  have hmul (x y : H) : e (finiteDynkinPolynomial coeff ![x, y]) = e x * e y := by
    have hp := congrArg F.inclusionD (hprod ![x, y]).symm
    simpa [List.ofFn_succ, e] using hp
  obtain ⟨A, hA⟩ := exists_linearMap_of_exponential_hom b e hinj hzero hadd hcont coeff hmul l hl
  exact ⟨A, fun v => by simpa only [he] using hA v⟩

end PolycyclicRecognition.CartanFactorModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanMeanFactorization
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.finite_templateSymmetryGroup _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.instFiniteRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.instFiniteSubtypeLinearEquivRealIdMemSubgroupLinearSupportSymmetryGroup _root_.OAI.PolycyclicRecognition.instNonemptyRootOffsetConeIndex _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invertible factorization of a Cartan mean after volume comparison -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra
open scoped Manifold

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))

set_option maxHeartbeats 1000000 in
include hπExp in
/-- Segment domination, root-factor vanishing, and actual Cartan polynomial
coordinates give an invertible factor on every point of the ambient group. -/
theorem exists_height_factor_of_cartan_domination
    (hbijN : Function.Bijective F.ExpN)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (l : G →* Multiplicative W) (hl : Continuous fun g => (l g).toAdd)
    (hroot : ∀ n, l (F.inclusionN n) = 1)
    (hdom : ∀ v : H,
      (M.supportIn T hunimod eW).segmentSupport (π (Exp v)).toAdd ≤
        (M.supportIn T hunimod eW).segmentSupport (l (Exp v)).toAdd) :
    ∃ A : W ≃ₗ[ℝ] W, ∀ g, (l g).toAdd = A (π g).toAdd := by
  obtain ⟨lH, hlH⟩ := F.exists_linearMap_on_cartan chartD hchartD dynkinD l hl
  let q : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
  have hq : Function.Surjective q := eW.surjective.comp (cartan_height_surjective T H)
  have hdom' (v : H) : (M.supportIn T hunimod eW).segmentSupport (q v) ≤
      (M.supportIn T hunimod eW).segmentSupport (lH v) := by
    change (M.supportIn T hunimod eW).segmentSupport
      (eW (heightProjection T.character (v : GroupLieAlgebra (𝓘(ℝ, EG)) G))) ≤ _
    rw [hlH]
    simpa only [hπExp] using hdom v
  obtain ⟨A, hA⟩ := exists_linearEquiv_factor_of_support_domination
    (M.supportIn T hunimod eW) q lH hq hdom'
  refine ⟨A, ?_⟩
  intro g
  obtain ⟨⟨n, d⟩, rfl⟩ := F.surjective g
  rw [map_mul, hroot, one_mul, map_mul,
    F.inclusionN_height_eq_one T eW π hπExp hbijN, one_mul]
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  obtain ⟨v, rfl⟩ := (hbijD.comp F.D.equiv.bijective).surjective d
  change (l (F.inclusionD (F.ExpD (F.D.equiv v)))).toAdd =
    A (π (F.inclusionD (F.ExpD (F.D.equiv v)))).toAdd
  rw [F.compatibleD, ← hlH, hA, hπExp]
  rfl

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

section
-- module Solutions.OAIQ093_PR.PolycyclicRecognition_Geometry_CartanStationaryFactor
attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.inversePairCoupling_finiteOnCompacts _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.normalizedPair_polishSpace _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Invertible height factor for the actual stationary mean -/

noncomputable section

namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set
open scoped Manifold NNReal ENNReal Pointwise

variable {EG G W : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  [ProperSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {Λ : ℝ≥0} [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G) (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
  (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hπExp hchartN hchartD dynkinN dynkinD haarN haarD in
/-- The actual stationary mean factors through canonical height by an
invertible linear map; no factorization or volume domination is assumed. -/
theorem exists_invertible_height_factor_of_stationary_mean_oai
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
    (l : G →* Multiplicative W)
    (hπ : Continuous fun g => (π g).toAdd) (hl : Continuous fun g => (l g).toAdd)
    (hΛ : 0 < (Λ : ℝ)) {K L : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hbound : ∀ g, ‖(l g).toAdd‖ ≤ L * dist 1 g)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ g,
      ‖pairHeightL2 μ π hπ g - Lp.const 2 μ (l g).toAdd‖ ≤ ε * dist 1 g + B)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    : ∃ A : W ≃ₗ[ℝ] W, ∀ g, (l g).toAdd = A (π g).toAdd := by
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  apply M.exists_height_factor_of_cartan_domination T F hunimod eW π hπExp
    hbijN chartD hchartD dynkinD l hl
  · exact M.hom_eq_one_on_root_factor T hExp realize l hl hL hbound F haarN dynkinN
  · intro v
    exact M.segmentSupport_le_of_stationary_mean_m T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD haarN haarD hExp realize
      μ l hπ hl hΛ hK hL hLip hbound hsub b₀ hφ hpath v

end PolycyclicRecognition.CartanWordModel

end

end OAI
end

theorem solution : type_of% @OAI.PolycyclicRecognition.CartanWordModel.exists_invertible_height_factor_of_stationary_mean_oai := @OAI.PolycyclicRecognition.CartanWordModel.exists_invertible_height_factor_of_stationary_mean_oai
