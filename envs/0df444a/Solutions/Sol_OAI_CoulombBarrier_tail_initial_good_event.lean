-- Prove2me | solution 1 for OAI.CoulombBarrier.tail_initial_good_event
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T06:46:53.399061+00:00
-- url     : https://prove2.me/submissions/7f1c7316-a1a4-43bb-9a2f-e1880fe7499f

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_TailTiltState_initial_pointwise
import Theorems.Thm_OAI_CoulombAtom_actual_priced_particle_bound_three

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterWidth
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.fermionGraph_completeSpace _root_.OAI.CoulombAtom.fermionGraph_innerProductSpace _root_.OAI.CoulombAtom.fermionGraph_normedAddCommGroup _root_.OAI.CoulombAtom.fermionGraph_normedSpace _root_.OAI.CoulombAtom.fermionSpace_completeSpace _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.sectorGraph_innerProductSpace _root_.OAI.CoulombAtom.sectorGraph_normedSpace _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombAtom.weakSectorGraph_innerProductSpace _root_.OAI.CoulombAtom.weakSectorGraph_normedAddCommGroup _root_.OAI.CoulombAtom.weakSectorGraph_normedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Metric
open scoped NNReal

lemma masterWidth_lower {c₁ r₀ s : ℝ} (hc : 0 ≤ c₁) (hr : 0 < r₀) (hrs : r₀ ≤ s)
    (x : Space) : c₁*r₀^(1+masterExponent) ≤ masterWidth c₁ r₀ s x := by
  have hD : r₀ ≤ masterBaseDistance r₀ x := le_max_right _ _
  rw [Real.rpow_one_add' hr.le (by linarith [masterExponent_pos])]
  simpa only [masterWidth,mul_assoc] using mul_le_mul_of_nonneg_left
    (mul_le_mul hD (Real.rpow_le_rpow hr.le (le_min hD hrs) masterExponent_nonneg)
      (Real.rpow_nonneg hr.le _) (hr.le.trans hD)) hc

open Set Metric
open scoped NNReal

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_LocalWidthKernel
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped NNReal ContDiff

lemma masterKernel_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ masterKernel c₁ r₀ s g x y := sq_nonneg _

lemma masterKernel_joint_continuous {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) :
    Continuous (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2) := by
  rw [masterKernel_eq_widthKernel hc hr hs g]
  have ht := (masterWidth_lipschitz hc.le hr hs).continuous.comp (continuous_fst : Continuous (Prod.fst : Space × Space → Space))
  have hi := ht.inv₀ (fun p => (masterWidth_pos hc hr hs p.1).ne')
  exact (hi.pow 3).mul ((hg.pow 2).comp (hi.smul (continuous_snd.sub continuous_fst)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterJointPosterior
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma jointMasterPosterior_nonneg {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (c₁ r₀ s : ℝ) (g : Space → ℝ)
    (z : OriginalDatum N K ell j) (y : Space) :
    0 ≤ jointMasterPosterior μ ell j c₁ r₀ s g z y :=
  integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) y))

lemma jointMasterPosterior_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2) := by
  have hm := (masterKernel_joint_continuous hc hr hs hg).measurable
  have h : StronglyMeasurable (fun p : (OriginalDatum N K ell j × Space) × Configuration N =>
      ∑ i, masterKernel c₁ r₀ s g (p.2 i) p.1.2) :=
    (Finset.measurable_sum _ (fun i _ => hm.comp
      (((measurable_pi_apply i).comp measurable_snd).prodMk measurable_fst.snd))).stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := (originalRawKernel μ ell j).comap Prod.fst measurable_fst)).measurable

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierTruncationBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierTruncation_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis
attribute [local irreducible] masterKernel masterWidth scaledRealPacket

lemma innerPotential_eq_tfPotential (r : ℝ) (ρ : Space → ℝ) (y : Space) :
    innerPotential r ρ y = tfPotential ((ball (0 : Space) r).indicator ρ) y := by
  unfold innerPotential tfPotential
  rw [←integral_indicator measurableSet_ball]
  congr 1
  funext z
  by_cases hz : z ∈ ball (0 : Space) r <;> simp [hz]

end CoulombAtom

end Work_BarrierTruncation_barrier_scope

open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_BarrierInitialEventBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma jointMasterPosterior_inner_measurable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (r : ℝ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun z : OriginalDatum N K ell j =>
      innerPotential r (jointMasterPosterior μ ell j c₁ r₀ s g z) y) := by
  have hm : Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2 / ‖y-p.2‖) :=
    (jointMasterPosterior_measurable μ ell j hc hr hs hg).div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierMasterRegularityBarrier
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma masterKernel_scale_bound {c₁ r₀ s G : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ} (hG : ∀ z, (g z)^2 ≤ G)
    (x y : Space) :
    masterKernel c₁ r₀ s g x y ≤ (c₁*r₀^(1+masterExponent))⁻¹^3*G := by
  have hδ : 0 < c₁*r₀^(1+masterExponent) := mul_pos hc (Real.rpow_pos_of_pos hr _)
  have hi : (masterWidth c₁ r₀ s x)⁻¹ ≤ (c₁*r₀^(1+masterExponent))⁻¹ :=
    inv_anti₀ hδ (masterWidth_lower hc.le hr hrs x)
  rw [masterKernel,scaledRealPacket_sq (masterWidth_pos hc hr hs x)]
  exact mul_le_mul (pow_le_pow_left₀ (inv_nonneg.mpr (masterWidth_pos hc hr hs x).le) hi 3)
    (hG _) (sq_nonneg _) (by positivity)

lemma jointMasterPosterior_scale_bound {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s G : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ}
    (hG : ∀ z, (g z)^2 ≤ G) (z : OriginalDatum N K ell j) (y : Space) :
    jointMasterPosterior μ ell j c₁ r₀ s g z y ≤ (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G := by
  have hGn : 0 ≤ G := (sq_nonneg (g 0)).trans (hG 0)
  have hb (x : Configuration N) :
      ‖∑ i, masterKernel c₁ r₀ s g (x i) y‖ ≤ (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G := by
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_nonneg c₁ r₀ s g (x i) y))]
    calc
      _ ≤ ∑ _i : Fin N, (c₁*r₀^(1+masterExponent))⁻¹^3*G :=
        Finset.sum_le_sum (fun i _ => masterKernel_scale_bound hc hr hs hrs hG (x i) y)
      _ = _ := by simp [mul_assoc]
  change (∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) y ∂originalRawKernel μ ell j z) ≤ _
  calc
    _ ≤ ‖∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) y ∂originalRawKernel μ ell j z‖ := by simpa only [Real.norm_eq_abs] using le_abs_self _
    _ ≤ ∫ _x : Configuration N, (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G ∂originalRawKernel μ ell j z :=
      norm_integral_le_of_norm_le (integrable_const _) (ae_of_all _ hb)
    _ = _ := by simp

lemma initial_radius_factor {c r : ℝ} (hr : 0 < r) :
    (c*r^(1+masterExponent))⁻¹^3*r = c⁻¹^3*r^(-2-3*masterExponent) := by
  rw [mul_inv_rev,mul_pow]
  have hp : (r^(1+masterExponent))⁻¹^3*r = r^(-2-3*masterExponent) := by
    rw [←Real.rpow_neg hr.le,←Real.rpow_natCast,←Real.rpow_mul hr.le]
    norm_num only [Nat.cast_ofNat]
    calc
      _ = r^(-(1+masterExponent)*(3:ℝ))*r^(1:ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hr]; congr 1; ring
  calc
    _ = c⁻¹^3*((r^(1+masterExponent))⁻¹^3*r) := by ring
    _ = _ := by rw [hp]

theorem jointMasterPosterior_inner_difference {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {c₁ r₀ s G : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) (hrs : r₀ ≤ s) {g : Space → ℝ} (hg : Continuous g)
    (hG : ∀ z, (g z)^2 ≤ G) (z : OriginalDatum N K ell j) (x y : Space)
    (hx : ‖x‖ ≤ (11/10)*r₀) (hy : ‖y‖ ≤ (11/10)*r₀) :
    |innerPotential r₀ (jointMasterPosterior μ ell j c₁ r₀ s g z) x-
      innerPotential r₀ (jointMasterPosterior μ ell j c₁ r₀ s g z) y| ≤
      (16*Real.pi*(N:ℝ)*G*c₁⁻¹^3)*r₀^(-2-3*masterExponent)*‖x-y‖ := by
  let ρ := (ball (0:Space) r₀).indicator (jointMasterPosterior μ ell j c₁ r₀ s g z)
  have hGn : 0 ≤ G := (sq_nonneg (g 0)).trans (hG 0)
  have hM : 0 ≤ (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G := by positivity
  have hm : Measurable ρ := ((jointMasterPosterior_measurable μ ell j hc hr hs hg).comp
    (measurable_const.prodMk measurable_id)).indicator measurableSet_ball
  have hn : ∀ y, 0 ≤ ρ y := indicator_nonneg (fun y _ => jointMasterPosterior_nonneg μ ell j c₁ r₀ s g z y)
  have hb : ∀ y, ρ y ≤ (N:ℝ)*(c₁*r₀^(1+masterExponent))⁻¹^3*G :=
    fun y => by
      by_cases hy : y ∈ ball (0:Space) r₀
      · simpa only [ρ,indicator_of_mem hy] using jointMasterPosterior_scale_bound μ ell j hc hr hs hrs hG z y
      · simpa only [ρ,indicator_of_notMem hy] using hM
  have hsup : Function.support ρ ⊆ ball (0:Space) (2*r₀) :=
    (support_indicator_subset).trans (ball_subset_ball (by linarith))
  have hh := bounded_density_potential_difference hm hM (by positivity : 0 < 2*r₀) hn hb hsup x y
    (by linarith) (by linarith)
  rw [innerPotential_eq_tfPotential,innerPotential_eq_tfPotential]
  apply hh.trans_eq
  calc
    _ = (16*Real.pi*(N:ℝ)*G)*((c₁*r₀^(1+masterExponent))⁻¹^3*r₀)*‖x-y‖ := by ring
    _ = _ := by rw [initial_radius_factor hr]; ring

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_BarrierSpatialNetBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_BarrierSpatialNet_barrier_scope

open Set Metric
open scoped BigOperators

open CoulombAtom

lemma spatialGridIndex_close {h : ℝ} (hh : 0 < h) {x y : Space}
    (he : spatialGridIndex h x = spatialGridIndex h y) : ‖x-y‖ ≤ 3*h := by
  have hc (i : Fin 3) : |x i-y i| ≤ h := by
    have hi := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun he i)
    change |x i/h-y i/h| < 1 at hi
    rw [←sub_div,abs_div,abs_of_pos hh] at hi
    exact ((div_lt_one hh).mp hi).le
  have hs : ‖x-y‖^2 ≤ 3*h^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, h^2 := Finset.sum_le_sum (fun i _ => by
        change (x i-y i)^2 ≤ h^2
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (x i-y i)) hh.le).mpr (hc i))
      _ = _ := by simp
  nlinarith [norm_nonneg (x-y)]

lemma spatialGridIndex_bound {R h : ℝ} (hh : 0 < h)
    {x : Space} (hx : ‖x‖ ≤ R) (i : Fin 3) :
    spatialGridIndex h x i ∈ Finset.Icc (-(⌈R/h⌉₊+1 : ℕ):ℤ) (⌈R/h⌉₊+1 : ℕ) := by
  have hcoord : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hi : |x i| ≤ R := hcoord.trans hx
  have hM : R/h < (⌈R/h⌉₊+1 : ℕ) := by
    have hh := Nat.le_ceil (R/h)
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith
  norm_num only [Nat.cast_add,Nat.cast_one] at hM
  simp only [Finset.mem_Icc,spatialGridIndex]
  constructor
  · apply Int.le_floor.mpr
    push_cast
    have hxi := (abs_le.mp hi).1
    have hd : -R/h ≤ x i/h := div_le_div_of_nonneg_right hxi hh.le
    rw [neg_div] at hd
    linarith
  · apply Int.floor_le_iff.mpr
    push_cast
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right (abs_le.mp hi).2 hh.le) (by linarith)

theorem exists_spatial_grid_net {A : Set Space} {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h)
    (hA : ∀ x ∈ A, ‖x‖ ≤ R) :
    ∃ Q : Finset Space, (∀ x ∈ Q, x ∈ A) ∧
      (∀ y ∈ A, ∃ x ∈ Q, ‖y-x‖ ≤ 3*h) ∧
      (Q.card:ℝ) ≤ (2*(R/h)+5)^3 := by
  classical
  let M : ℕ := ⌈R/h⌉₊+1
  let D : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => Finset.Icc (-(M:ℤ)) (M:ℤ))
  let E := D.filter (fun k => ∃ x ∈ A, spatialGridIndex h x = k)
  let f : (Fin 3 → ℤ) → Space := fun k => if hk : ∃ x ∈ A, spatialGridIndex h x = k then hk.choose else 0
  have hf {k : Fin 3 → ℤ} (hk : k ∈ E) : f k ∈ A ∧ spatialGridIndex h (f k) = k := by
    have he := (Finset.mem_filter.mp hk).2
    simpa only [f,dite_eq_left he] using he.choose_spec
  have hd {x : Space} (hx : x ∈ A) : spatialGridIndex h x ∈ E := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,x,hx,rfl⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    exact spatialGridIndex_bound hh (hA x hx) i
  refine ⟨E.image f,?_,?_,?_⟩
  · intro x hx
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    exact (hf hk).1
  · intro y hy
    refine ⟨f (spatialGridIndex h y),Finset.mem_image.mpr ⟨_,hd hy,rfl⟩,?_⟩
    apply spatialGridIndex_close hh
    exact (hf (hd hy)).2.symm
  · have hcard : (Finset.Icc (-(M:ℤ)) (M:ℤ)).card = 2*M+1 := by
      rw [Int.card_Icc]
      omega
    have hD : D.card = (2*M+1)^3 := by
      simp only [D,Fintype.card_piFinset,hcard,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    have hM : (M:ℝ) ≤ R/h+2 := by
      have hm := Nat.ceil_lt_add_one (div_nonneg hR hh.le)
      dsimp [M]
      push_cast
      linarith
    calc
      _ ≤ (D.card:ℝ) := by exact_mod_cast (Finset.card_image_le.trans (Finset.card_filter_le D _))
      _ = ((2*M+1:ℕ):ℝ)^3 := by rw [hD]; push_cast; rfl
      _ ≤ _ := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith

theorem exists_initial_spatial_net {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ Q : Finset Space, (∀ x ∈ Q, ‖x‖ ≤ (11/10)*r) ∧
      (∀ y : Space, ‖y‖ ≤ (11/10)*r → ∃ x ∈ Q, ‖y-x‖ ≤ r^2) ∧
      (Q.card:ℝ) ≤ (12/r)^3 := by
  obtain ⟨Q,hQ,hcover,hcard⟩ := exists_spatial_grid_net (A := {x : Space | ‖x‖ ≤ (11/10)*r})
    (h := r^2/3) (by positivity) (by positivity) (fun _ hx => hx)
  refine ⟨Q,hQ,?_,hcard.trans ?_⟩
  · intro y hy
    obtain ⟨x,hx,hxy⟩ := hcover y hy
    refine ⟨x,hx,?_⟩
    nlinarith
  · apply pow_le_pow_left₀ (by positivity)
    have he : 2*((11/10)*r/(r^2/3))+5 = (33/5)/r+5 := by field_simp; ring
    rw [he]
    apply (le_div_iff₀ hr).mpr
    field_simp
    nlinarith

end Work_BarrierSpatialNet_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAtom CoulombAnalysis CoulombObservation

lemma finite_net_good_event {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) {m : MeasurableSpace Ω} (P : Ω → Space → ℝ)
    (Q : Finset Space) {A : Set Space} {θ p L d : ℝ}
    (hm : ∀ x ∈ Q, Measurable[m] (fun z => P z x))
    (hpoint : ∀ x ∈ Q, μ.real {z | θ < P z x} ≤ p)
    (hcover : ∀ y ∈ A, ∃ x ∈ Q, ‖y-x‖ ≤ d)
    (hQ : ∀ x ∈ Q, x ∈ A) (hL : 0 ≤ L)
    (hmod : ∀ z, ∀ x ∈ A, ∀ y ∈ A, |P z x-P z y| ≤ L*‖x-y‖) :
    ∃ G : Set Ω, MeasurableSet[m] G ∧
      (∀ z ∈ G, ∀ y ∈ A, P z y ≤ θ+L*d) ∧
      μ.real Gᶜ ≤ (Q.card:ℝ)*p := by
  classical
  let B : Set Ω := ⋃ x ∈ Q, {z | θ < P z x}
  refine ⟨Bᶜ,?_,?_,?_⟩
  · exact (Finset.measurableSet_biUnion Q (fun x hx => measurableSet_lt measurable_const (hm x hx))).compl
  · intro z hz y hy
    obtain ⟨x,hx,hxy⟩ := hcover y hy
    have hpx : P z x ≤ θ := by
      by_contra! hnot
      exact hz (mem_iUnion.mpr ⟨x,mem_iUnion.mpr ⟨hx,hnot⟩⟩)
    have hh := (le_abs_self (P z y-P z x)).trans (hmod z y hy x (hQ x hx))
    have hd := mul_le_mul_of_nonneg_left hxy hL
    linarith
  · rw [compl_compl]
    exact (measureReal_biUnion_finset_le Q _).trans (by
      calc
        _ ≤ ∑ _x ∈ Q, p := Finset.sum_le_sum hpoint
        _ = _ := by simp)

lemma initial_interpolation_exponent {r : ℝ} (hr : 0 < r) :
    r^(-2-3*masterExponent)*r^2*r = r^(1-3*masterExponent) := by
  rw [←Real.rpow_natCast,←Real.rpow_add hr]
  calc
    _ = r^((-2-3*masterExponent)+2)*r^(1:ℝ) := by rw [Real.rpow_one]; norm_num
    _ = _ := by rw [←Real.rpow_add hr]; congr 1; ring

lemma initial_interpolation_bound {N : ℕ} {Z r c G : ℝ}
    (hcount : (N:ℝ) ≤ 3*Z) (hr : 0 < r) (hc : 0 < c) (hG : 0 ≤ G)
    (hsmall : (48*Real.pi*G*c⁻¹^3)*r^(1-3*masterExponent) ≤ 1/20) :
    (16*Real.pi*(N:ℝ)*G*c⁻¹^3)*r^(-2-3*masterExponent)*r^2 ≤ Z/(20*r) := by
  have hZ : 0 ≤ Z := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  apply (le_div_iff₀ (by positivity : 0 < 20*r)).mpr
  have he : ((16*Real.pi*(N:ℝ)*G*c⁻¹^3)*r^(-2-3*masterExponent)*r^2)*(20*r) =
      (N:ℝ)*(16*Real.pi*G*c⁻¹^3)*r^(1-3*masterExponent)*20 := by
    calc
      _ = (N:ℝ)*(16*Real.pi*G*c⁻¹^3)*(r^(-2-3*masterExponent)*r^2*r)*20 := by ring
      _ = _ := by rw [initial_interpolation_exponent hr]
  rw [he]
  calc
    _ ≤ (3*Z)*(16*Real.pi*G*c⁻¹^3)*r^(1-3*masterExponent)*20 := by gcongr
    _ = Z*((48*Real.pi*G*c⁻¹^3)*r^(1-3*masterExponent))*20 := by ring
    _ ≤ Z*(1/20)*20 := by gcongr
    _ = Z := by ring

lemma initial_net_probability {r : ℝ} (hr : 0 < r) :
    (12/r)^3*r^40 = 1728*r^37 := by
  field_simp
  ring

end CoulombBarrier

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TailInitialPointwiseBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

section Work_TailInitialGood_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem tail_initial_good_event_oai {Z : ℕ} (hZ : 1 ≤ Z)
    {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hr1 : r₀ ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hrs : r₀ ≤ s) (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2)
    {N K : ℕ} (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ G : ℝ}
    {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
    (j : Fin (K+1)) (h₀ : 0 < p₀ j) (hp40 : p₀ j ≤ r₀^40)
    (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < (Z:ℝ)/(20*r₀))
    (hinterp : (48*Real.pi*G*c₁⁻¹^3)*r₀^(1-3*masterExponent) ≤ 1/20)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
    (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)),
      MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r₀ k) j] A ∧
      (∀ z ∈ A, ∀ y : Space, ‖y‖ ≤ (11/10)*r₀ →
        innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
            (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y ≤ (Z:ℝ)/(10*r₀)) ∧
      (physicalObservationLaw (graphRawLaw F) K).real Aᶜ ≤ 1728*r₀^37 := by
  have hcount := actual_priced_particle_bound_three Z hZ hlam hN
  have hpoint := hF.initial_pointwise hZ hlam hr hs hs1 hc hc1 hN j h₀ hbudget hsmall hg hcg hgn hrad hgs
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r₀ k
  let P := fun z y => innerPotential r₀ (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s g (originalDatum ell j z)) y
  let L := (16*Real.pi*(N:ℝ)*G*c₁⁻¹^3)*r₀^(-2-3*masterExponent)
  obtain ⟨Q,hQ,hcover,hcard⟩ := exists_initial_spatial_net hr hr1
  have hGn : 0 ≤ G := (sq_nonneg (g 0)).trans (hG 0)
  have hm (y : Space) : Measurable[observationInformation ell j] (fun z => P z y) :=
    jointMasterPosterior_inner_measurable (graphRawLaw F) ell j r₀ y hc hr hs hg.continuous
  obtain ⟨A,hA,hgood,hbad⟩ := finite_net_good_event (physicalObservationLaw (graphRawLaw F) K) P Q
    (A := {y : Space | ‖y‖ ≤ (11/10)*r₀}) (θ := (Z:ℝ)/(20*r₀)) (p := r₀^40) (L := L) (d := r₀^2)
    (fun y _ => hm y) (fun y hy => (hpoint y (hQ y hy)).le.trans hp40) hcover hQ (by dsimp [L]; positivity)
    (fun z x hx y hy => jointMasterPosterior_inner_difference (graphRawLaw F) ell j hc hr hs hrs hg.continuous hG _ x y hx hy)
  refine ⟨A,hA,?_,?_⟩
  · intro z hz y hy
    have hh := hgood z hz y hy
    have hi := initial_interpolation_bound (show (N:ℝ) ≤ 3*(Z:ℝ) by exact_mod_cast hcount) hr hc hGn hinterp
    change L*r₀^2 ≤ (Z:ℝ)/(20*r₀) at hi
    change P z y ≤ (Z:ℝ)/(10*r₀)
    have he : (Z:ℝ)/(10*r₀) = 2*((Z:ℝ)/(20*r₀)) := by ring
    rw [he]
    linarith
  · exact hbad.trans ((mul_le_mul_of_nonneg_right hcard (pow_nonneg hr.le 40)).trans_eq (initial_net_probability hr))

end CoulombBarrier

end Work_TailInitialGood_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.CoulombBarrier.tail_initial_good_event_oai := @OAI.CoulombBarrier.tail_initial_good_event_oai
