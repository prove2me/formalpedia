-- Prove2me | solution 1 for OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T05:38:56.438886+00:00
-- url     : https://prove2.me/submissions/865d43f4-e0ae-41c7-878f-17cb35bc466d

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010
import Theorems.Thm_OAI_CoulombAtom_sharp_cell_local_potential
import Theorems.Thm_OAI_CoulombAtom_sharp_joint_selected_patch

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_CoulombCoercivity
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section CoulombCoercivity

lemma graphValue_norm_sq {N : ℕ} (F : fermionGraph N) :
    ‖fermionGraphValue N F‖ ^ 2 = ∑ s : Spins N, ‖graphComponent s none F‖ ^ 2 := by
  change ‖(fermionGraphValue N F).val‖ ^ 2 = _
  exact PiLp.norm_sq_eq_of_L2 _ _

attribute [local irreducible] graphComponent graphNuclear graphPair fermionGraphValue

end CoulombCoercivity

lemma graphFormVector_admissible {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖ ^ 2 = 1) : FormAdmissible (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_, ?_, ?_, ?_⟩
  · intro s i a φ hφ hcφ
    exact ((mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property
      (i, a)) φ hφ hcφ
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s
  · have hmass := graphValue_norm_sq F
    rw [hn] at hmass
    simpa only [lp_norm_sq, graphComponent_apply, graphFormVector] using hmass.symm
  · intro s i
    exact nuclear_integrable i (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))
  · intro s i j hij
    exact pair_integrable i j hij (Lp.memLp _) (fun a => Lp.memLp _)
      (fun a => (mem_weakGraph (sectorDirections N) (F.val s).val).mp (F.val s).property (i, a))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FineSmearingPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable _root_.OAI.CoulombNeumann.cubePartition_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_memLp {b : ℝ} (hb : 0 < b) : MemLp (varthetaScaled b) (5/3) := by
  apply bounded_compact_memLp (varthetaScaled_measurable b) (isCompact_closedBall (0:Space) (Real.sqrt 3*b))
  · intro x hx
    simpa only [mem_closedBall,dist_zero_right] using varthetaScaled_support_bound hb x hx
  · intro x
    rw [abs_of_nonneg (varthetaScaled_nonneg hb x)]
    exact varthetaScaled_le hb x

lemma varthetaScaled_potential_le {b : ℝ} (hb : 0 < b) {x : Space} (hx : x ≠ 0) :
    tfPotential (varthetaScaled b) x ≤ 1/‖x‖ := by
  have hh := radial_potential_le_point (varthetaScaled_integrable hb) (varthetaScaled_memLp hb)
    (varthetaScaled_nonneg hb) (fun _ _ h => varthetaScaled_radial b h)
    (by positivity : 0 ≤ Real.sqrt 3*b) (varthetaScaled_support_bound hb) hx
  simpa only [integral_varthetaScaled hb] using hh

lemma varthetaScaled_potential_eq_far {b : ℝ} (hb : 0 < b) {x : Space}
    (hx : Real.sqrt 3*b ≤ ‖x‖) : tfPotential (varthetaScaled b) x = 1/‖x‖ := by
  have hh := tfPotential_newton_exterior_closed (varthetaScaled_integrable hb)
    (varthetaScaled_memLp hb) (fun _ _ h => varthetaScaled_radial b h)
    (by positivity : 0 < Real.sqrt 3*b) (varthetaScaled_support_bound hb) hx
  simpa only [integral_varthetaScaled hb] using hh

lemma retainedSmear_potential {N : ℕ} {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) :
    tfPotential (retainedSmear b S x) y = ∑ i ∈ S, tfPotential (varthetaScaled b) (y-x i) := by
  simp only [tfPotential,retainedSmear,Finset.sum_div]
  rw [integral_finsetSum _ (fun i _ => translated_pole_integrable
    (varthetaScaled_integrable hb) (varthetaScaled_memLp hb) y (x i))]
  exact Finset.sum_congr rfl (fun i _ => integral_translated_pole (varthetaScaled b) y (x i))

theorem retainedSmear_potential_loss {N : ℕ} {b : ℝ} (hb : 0 < b) (S : Finset (Fin N))
    (x : Configuration N) (y : Space) (hxy : ∀ i ∈ S, x i ≠ y) :
    0 ≤ (∑ i ∈ S, 1/‖y-x i‖)-tfPotential (retainedSmear b S x) y ∧
      (∑ i ∈ S, 1/‖y-x i‖)-tfPotential (retainedSmear b S x) y ≤
        ∑ i ∈ S, (ball y (Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
  rw [retainedSmear_potential hb,←Finset.sum_sub_distrib]
  have hh (i : Fin N) (hi : i ∈ S) :
      0 ≤ 1/‖y-x i‖-tfPotential (varthetaScaled b) (y-x i) ∧
      1/‖y-x i‖-tfPotential (varthetaScaled b) (y-x i) ≤
        (ball y (Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
    have hn := tfPotential_nonneg (ae_of_all _ (varthetaScaled_nonneg hb)) (y-x i)
    have hle := varthetaScaled_potential_le hb (sub_ne_zero.mpr (hxy i hi).symm)
    refine ⟨sub_nonneg.mpr hle,?_⟩
    by_cases hB : x i ∈ ball y (Real.sqrt 3*b)
    · rw [indicator_of_mem hB]
      exact sub_le_self _ hn
    · rw [indicator_of_notMem hB,varthetaScaled_potential_eq_far hb (by
        simpa only [mem_ball,dist_eq_norm,norm_sub_rev,not_lt] using hB)]
      simp only [sub_self,le_refl]
  exact ⟨Finset.sum_nonneg (fun i hi => (hh i hi).1),
    Finset.sum_le_sum (fun i hi => (hh i hi).2)⟩

end CoulombNeumann

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_MasterPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis

lemma scaled_packet_density_radial (b : ℝ) {g : Space → ℝ} (hr : IsRadial g) :
    IsRadial (fun x => (scaledRealPacket b g x)^2) := by
  intro x y hxy
  dsimp only
  rw [scaledRealPacket_radial b hr x y hxy]

lemma scaled_packet_density_support {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hs : tsupport g ⊆ ball 0 1) (x : Space) (hx : (scaledRealPacket b g x)^2 ≠ 0) :
    ‖x‖ ≤ b := (scaledRealPacket_support hb hs (by intro hz; exact hx (by rw [hz]; norm_num))).le

lemma scaled_packet_potential_le {b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x, (g x)^2 = 1) (hr : IsRadial g) (hs : tsupport g ⊆ ball 0 1)
    {x : Space} (hx : x ≠ 0) :
    tfPotential (fun z => (scaledRealPacket b g z)^2) x ≤ 1/‖x‖ := by
  have hc : Continuous (fun z => (scaledRealPacket b g z)^2) := by
    exact (scaledRealPacket_smooth b hg).continuous.pow 2
  have hcomp : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
    convert! (scaledRealPacket_compact hb hcg).mul_right (f' := scaledRealPacket b g) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact pow_two _
  have hh := radial_potential_le_point (hc.integrable_of_hasCompactSupport hcomp)
    (hc.memLp_of_hasCompactSupport hcomp) (fun z => sq_nonneg _)
    (scaled_packet_density_radial b hr) hb.le (scaled_packet_density_support hb hs) hx
  simpa only [scaledRealPacket_mass hb,hgn] using hh

lemma scaled_packet_potential_eq {b : ℝ} (hb : 0 < b)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ x, (g x)^2 = 1) (hr : IsRadial g) (hs : tsupport g ⊆ ball 0 1)
    {x : Space} (hx : b ≤ ‖x‖) :
    tfPotential (fun z => (scaledRealPacket b g z)^2) x = 1/‖x‖ := by
  have hc : Continuous (fun z => (scaledRealPacket b g z)^2) := by
    exact (scaledRealPacket_smooth b hg).continuous.pow 2
  have hcomp : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
    convert! (scaledRealPacket_compact hb hcg).mul_right (f' := scaledRealPacket b g) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    exact pow_two _
  have hh := tfPotential_newton_exterior_closed (hc.integrable_of_hasCompactSupport hcomp)
    (hc.memLp_of_hasCompactSupport hcomp) (scaled_packet_density_radial b hr) hb
    (scaled_packet_density_support hb hs) hx
  simpa only [scaledRealPacket_mass hb,hgn] using hh

lemma masterKernel_potential_centered (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    tfPotential (masterKernel c₁ r₀ s g x) y =
      tfPotential (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) (y-x) :=
  integral_translated_pole (fun z => (scaledRealPacket (masterWidth c₁ r₀ s x) g z)^2) y x

lemma masterKernel_potential_nonneg (c₁ r₀ s : ℝ) (g : Space → ℝ) (x y : Space) :
    0 ≤ tfPotential (masterKernel c₁ r₀ s g x) y :=
  tfPotential_nonneg (ae_of_all _ (masterKernel_nonneg c₁ r₀ s g x)) y

lemma masterKernel_potential_le {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : x ≠ y) :
    tfPotential (masterKernel c₁ r₀ s g x) y ≤ 1/‖y-x‖ := by
  rw [masterKernel_potential_centered]
  exact scaled_packet_potential_le (masterWidth_pos hc hr hs x) hg hcg hgn hrad hgs
    (sub_ne_zero.mpr hxy.symm)

lemma masterWidth_le_distance {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) {x y : Space}
    (hxy : 2*masterWidth c₁ r₀ s y ≤ ‖y-x‖) :
    masterWidth c₁ r₀ s x ≤ ‖y-x‖ := by
  have hh := (masterWidth_small_lipschitz hc hcL hr hs hs1).dist_le_mul x y
  simp only [dist_eq_norm,Real.norm_eq_abs,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat] at hh
  rw [norm_sub_rev x y] at hh
  have h := (le_abs_self (masterWidth c₁ r₀ s x-masterWidth c₁ r₀ s y)).trans hh
  linarith

lemma masterKernel_potential_eq_far {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : 2*masterWidth c₁ r₀ s y ≤ ‖y-x‖) :
    tfPotential (masterKernel c₁ r₀ s g x) y = 1/‖y-x‖ := by
  rw [masterKernel_potential_centered]
  exact scaled_packet_potential_eq (masterWidth_pos hc hr hs x) hg hcg hgn hrad hgs
    (masterWidth_le_distance hc hcL hr hs hs1 hxy)

theorem masterKernel_potential_loss {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {x y : Space} (hxy : x ≠ y) :
    0 ≤ 1/‖y-x‖-tfPotential (masterKernel c₁ r₀ s g x) y ∧
      1/‖y-x‖-tfPotential (masterKernel c₁ r₀ s g x) y ≤
        (ball y (2*masterWidth c₁ r₀ s y)).indicator (fun x => 1/‖y-x‖) x := by
  refine ⟨sub_nonneg.mpr (masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs hxy),?_⟩
  by_cases hx : x ∈ ball y (2*masterWidth c₁ r₀ s y)
  · rw [indicator_of_mem hx]
    linarith [masterKernel_potential_nonneg c₁ r₀ s g x y]
  · rw [indicator_of_notMem hx]
    have hfar : 2*masterWidth c₁ r₀ s y ≤ ‖y-x‖ := by
      simpa only [mem_ball,dist_eq_norm,norm_sub_rev,not_lt] using hx
    rw [masterKernel_potential_eq_far hc hcL hr hs hs1 hg hcg hgn hrad hgs hfar,sub_self]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_SpatialRotation
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
namespace CoulombAtom

lemma averagedPacket_nonneg (p : Space) (r : ℝ) (x : Space) : 0 ≤ averagedPacket p r x :=
  integral_nonneg (fun g => packetDensity_nonneg (rotate g p) r x)

end CoulombAtom

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_RadialShellPotential
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAnalysis

lemma tfPotential_annular_bounds {ρ : TFSpace → ℝ} (h1 : Integrable ρ)
    (hp : MemLp ρ (5/3)) (hr : IsRadial ρ) (hn : ∀ y, 0 ≤ ρ y)
    (hm : ∫ y, ρ y = 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : ∀ y, ρ y ≠ 0 → a ≤ ‖y‖ ∧ ‖y‖ ≤ b) (x : TFSpace) :
    1/max ‖x‖ b ≤ tfPotential ρ x ∧ tfPotential ρ x ≤ 1/max ‖x‖ a := by
  rw [tfPotential_radial_max h1 hp hr (ha.le.trans hab) (fun y hy => (hs y hy).2)]
  have ham : 0 < max ‖x‖ a := ha.trans_le (le_max_right _ _)
  have hbm : 0 < max ‖x‖ b := (ha.trans_le hab).trans_le (le_max_right _ _)
  have hind (y : TFSpace) : ‖ρ y/max ‖x‖ ‖y‖‖ ≤ ρ y/max ‖x‖ a := by
    by_cases hy : ρ y = 0
    · simp [hy]
    · rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (hn _) (le_max_left _ _ |>.trans' (norm_nonneg _)))]
      exact div_le_div_of_nonneg_left (hn _) ham (max_le_max_left _ (hs y hy).1)
  have hi : Integrable (fun y => ρ y/max ‖x‖ ‖y‖) :=
    (h1.div_const _).mono' (h1.aemeasurable.div
      ((continuous_const.max continuous_norm).aemeasurable)).aestronglyMeasurable
      (Eventually.of_forall hind)
  constructor
  · rw [← hm, ← integral_div]
    apply integral_mono (h1.div_const _) hi
    intro y
    by_cases hy : ρ y = 0
    · simp [hy]
    · have hp0 : 0 < max ‖x‖ ‖y‖ := ham.trans_le (max_le_max_left _ (hs y hy).1)
      exact div_le_div_of_nonneg_left (hn _) hp0 (max_le_max_left _ (hs y hy).2)
  · rw [← hm, ← integral_div]
    exact integral_mono hi (h1.div_const _) (fun y => (le_abs_self _).trans (hind y))

end CoulombAnalysis
namespace CoulombAtom

lemma averagedPacket_annulus (p : Space) {r : ℝ} (hr : 0 < r) {x : Space}
    (hx : averagedPacket p r x ≠ 0) : ‖p‖-r ≤ ‖x‖ ∧ ‖x‖ ≤ ‖p‖+r := by
  refine ⟨?_,averagedPacket_support p hr hx⟩
  by_contra hn
  apply hx
  unfold averagedPacket
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro g
  by_contra hg
  have hd := packetDensity_support (rotate g p) hr hg
  have hh := norm_add_le (rotate g p-x) x
  rw [sub_add_cancel,(rotate g).norm_map,norm_sub_rev] at hh
  linarith

lemma averagedPacket_potential_bounds (p : Space) {r : ℝ} (hr : 0 < r)
    (hpr : r < ‖p‖) (x : Space) :
    1/max ‖x‖ (‖p‖+r) ≤ CoulombAnalysis.tfPotential (averagedPacket p r) x ∧
      CoulombAnalysis.tfPotential (averagedPacket p r) x ≤ 1/max ‖x‖ (‖p‖-r) :=
  CoulombAnalysis.tfPotential_annular_bounds (averagedPacket_integrable p hr)
    (averagedPacket_memLp p hr) (averagedPacket_radial p r) (averagedPacket_nonneg p r)
    (averagedPacket_mass p hr) (by linarith) (by linarith)
    (fun _ hh => averagedPacket_annulus p hr hh) x

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ShellCoulombDuality
attribute [-instance] _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAnalysis

lemma tfCoulomb_density_bound (R : ℝ) {ρ : TFSpace → ℝ}
    (hp : MemLp ρ (5/3)) (hs : Function.support ρ ⊆ ball 0 R)
    (hn : ∀ x, 0 ≤ ρ x) (hmass : ∫ x, ρ x = 1) {C : ℝ}
    (hbound : ∀ x, tfPotential ρ x ≤ C) (f : TFLp (ballMeasure R)) :
    (∫ x, tfPotential ρ x*f x ∂ballMeasure R)^2 ≤ C*tfCoulombL R f f := by
  obtain ⟨q,hq,hpot⟩ := exists_patch_density R hp hs
  have hmassq : (∫ x, q x ∂ballMeasure R) = 1 := by
    rw [integral_congr_ae hq,ballMeasure,← integral_indicator measurableSet_ball]
    convert hmass using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    funext x
    by_cases hx : x ∈ ball (0 : TFSpace) R
    · simp [hx]
    · have hz : ρ x = 0 := Function.notMem_support.mp (fun hh => hx (hs hh))
      simp [hx,hz]
  have hself : tfCoulombL R q q ≤ C := by
    rw [tfCoulombL_potential,← mul_one C,← hmassq,← integral_const_mul]
    apply integral_mono_ae (tfBallPotential_mul_integrable R q q)
      (((Lp.memLp q).integrable (Fact.out : (1:ENNReal) ≤ 5/3)).const_mul C)
    filter_upwards [hq] with x hx
    rw [hpot x,hx]
    exact mul_le_mul_of_nonneg_right (hbound x) (hn x)
  have hpair : tfCoulombL R q f = ∫ x, tfPotential ρ x*f x ∂ballMeasure R := by
    rw [tfCoulombL_potential]
    simp_rw [hpot]
  rw [← hpair]
  exact (tfCoulombL_pair_sq_le R q f).trans
    (mul_le_mul_of_nonneg_right hself (tfCoulombL_nonneg R f))

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

lemma shell_coulomb_test_bound {R : ℝ} (f : TFLp (ballMeasure R)) (p : Space)
    {r : ℝ} (hr : 0 < r) (hpr : r < ‖p‖) (hR : ‖p‖+r < R) :
    (∫ x, tfPotential (averagedPacket p r) x*f x ∂ballMeasure R)^2 ≤
      (1/(‖p‖-r))*tfCoulombL R f f := by
  apply tfCoulomb_density_bound R (averagedPacket_memLp p hr) _
    (averagedPacket_nonneg p r) (averagedPacket_mass p hr)
  · intro x
    exact (averagedPacket_potential_bounds p hr hpr x).2.trans
      (one_div_le_one_div_of_le (by linarith) (le_max_right _ _))
  · intro x hx
    exact mem_ball_zero_iff.mpr ((averagedPacket_support p hr hx).trans_lt hR)

end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped BigOperators Topology

namespace CoulombAtom
open CoulombAnalysis

lemma shell_potential_tendsto (p : Space) (hp : 0 < ‖p‖) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hpr : ∀ n, r n < ‖p‖)
    (hlim : Tendsto r atTop (𝓝 0)) (x : Space) :
    Tendsto (fun n => tfPotential (averagedPacket p (r n)) x) atTop
      (𝓝 (1/max ‖x‖ ‖p‖)) := by
  have hmax : max ‖x‖ ‖p‖ ≠ 0 := (hp.trans_le (le_max_right _ _)).ne'
  have hplus : Tendsto (fun n => 1/max ‖x‖ (‖p‖+r n)) atTop
      (𝓝 (1/max ‖x‖ ‖p‖)) := by
    convert! tendsto_const_nhds.div
      (tendsto_const_nhds.max (tendsto_const_nhds.add hlim)) (by simpa only [add_zero] using hmax) using 1; simp
  have hminus : Tendsto (fun n => 1/max ‖x‖ (‖p‖-r n)) atTop
      (𝓝 (1/max ‖x‖ ‖p‖)) := by
    convert! tendsto_const_nhds.div
      (tendsto_const_nhds.max (tendsto_const_nhds.sub hlim)) (by simpa only [sub_zero] using hmax) using 1; simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hplus hminus
    (fun n => (averagedPacket_potential_bounds p (hr n) (hpr n) x).1)
    (fun n => (averagedPacket_potential_bounds p (hr n) (hpr n) x).2)

lemma shell_potential_pair_tendsto (μ : Measure Space) {f : Space → ℝ}
    (hf : Integrable f μ) (p : Space) (hp : 0 < ‖p‖) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hpr : ∀ n, r n ≤ ‖p‖/2)
    (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, tfPotential (averagedPacket p (r n)) x*f x ∂μ) atTop
      (𝓝 (∫ x, (1/max ‖x‖ ‖p‖)*f x ∂μ)) := by
  have hpr' (n : ℕ) : r n < ‖p‖ := by linarith [hpr n]
  apply tendsto_integral_of_dominated_convergence (fun x => (2/‖p‖)*‖f x‖)
  · intro n
    exact ((tfPotential_continuous (averagedPacket_integrable p (hr n))
      (averagedPacket_memLp p (hr n))).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · exact hf.norm.const_mul _
  · intro n
    apply Eventually.of_forall
    intro x
    rw [norm_mul,Real.norm_eq_abs]
    have hh := averagedPacket_potential_bounds p (hr n) (hpr' n) x
    have hn : 0 ≤ tfPotential (averagedPacket p (r n)) x :=
      (by positivity : 0 ≤ 1/max ‖x‖ (‖p‖+r n)).trans hh.1
    rw [abs_of_nonneg hn]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hden : ‖p‖/2 ≤ max ‖x‖ (‖p‖-r n) :=
      (by linarith [hpr n] : ‖p‖/2 ≤ ‖p‖-r n).trans (le_max_right _ _)
    have hh' := one_div_le_one_div_of_le (by positivity : 0 < ‖p‖/2) hden
    exact hh.2.trans (by convert hh' using 1; ring)
  · exact Eventually.of_forall fun x =>
      (shell_potential_tendsto p hp hr hpr' hlim x).mul_const (f x)

end CoulombAtom
namespace CoulombAnalysis
open CoulombAtom

theorem tfCoulomb_truncated_duality {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (f : TFLp (ballMeasure R)) :
    (∫ x, (1/max ‖x‖ t)*f x ∂ballMeasure R)^2 ≤ (1/t)*tfCoulombL R f f := by
  let p : Space := t • radialAxis
  have hp : ‖p‖ = t := by simp [p,norm_smul,abs_of_pos ht]
  let δ : ℝ := min (t/2) ((R-t)/2)
  have hd : 0 < δ := by dsimp [δ]; positivity
  let r : ℕ → ℝ := fun n => δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hrd (n : ℕ) : r n ≤ δ := by
    exact div_le_self hd.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hrt (n : ℕ) : r n ≤ t/2 := (hrd n).trans (min_le_left _ _)
  have hrR (n : ℕ) : ‖p‖+r n < R := by
    have hh := (hrd n).trans (min_le_right (t/2) ((R-t)/2))
    rw [hp]
    linarith
  have hpr (n : ℕ) : r n < ‖p‖ := by rw [hp]; linarith [hrt n]
  have hlim : Tendsto r atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ
  have hpair := shell_potential_pair_tendsto (ballMeasure R)
    ((Lp.memLp f).integrable (Fact.out : (1:ENNReal) ≤ 5/3)) p (by rwa [hp]) hr
    (fun n => by simpa only [hp] using hrt n) hlim
  rw [hp] at hpair
  have hcoef : Tendsto (fun n => (1/(‖p‖-r n))*tfCoulombL R f f) atTop
      (𝓝 ((1/t)*tfCoulombL R f f)) := by
    convert! (tendsto_const_nhds.div
      (tendsto_const_nhds.sub hlim) (show ‖p‖-0 ≠ 0 by rw [sub_zero,hp]; exact ht.ne')).mul_const
      (tfCoulombL R f f) using 1; simp only [hp,sub_zero]
  exact le_of_tendsto_of_tendsto (hpair.pow 2) hcoef
    (Eventually.of_forall fun n => shell_coulomb_test_bound f p (hr n) (hpr n) (hrR n))

theorem tfPatchGap_truncated_control {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) :
    (∫ x, (1/max ‖x‖ t)*(σ-tfPatchMinimizer R T hT Φ) x ∂ballMeasure R)^2 ≤
      (2/t)*tfPatchGap R T hT Φ σ := by
  have hh := tfCoulomb_truncated_duality ht htR (σ-tfPatchMinimizer R T hT Φ)
  have he := mul_le_mul_of_nonneg_left (tfPatchGap_coulomb_le R T hT Φ hσ)
    (by positivity : 0 ≤ 1/t)
  exact hh.trans (by convert he using 1; ring)

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_QuantumRawLaw
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_QuantumRawLaw_scope

open MeasureTheory Set Finset Filter
open scoped ENNReal NNReal BigOperators Topology

namespace CoulombAtom

attribute [local irreducible] graphComponent fermionGraphValue

lemma graphRawLaw_probability {N : ℕ} (F : fermionGraph N)
    (hn : ‖fermionGraphValue N F‖^2 = 1) : IsProbabilityMeasure (graphRawLaw F) := by
  constructor
  rw [graphRawLaw_univ, hn, ENNReal.ofReal_one]

end CoulombAtom

end Work_QuantumRawLaw_scope

open MeasureTheory Filter Set
open scoped ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegratedLipschitzControl
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

namespace CoulombAtom
open CoulombNeumann CoulombAnalysis

lemma weightedPatchTestSquare_nonneg {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) (R : ℝ) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (g : TFSpace → ℝ)
    (u : Configuration M) : 0 ≤ weightedPatchTestSquare ψ s Z lam y R hb S g u :=
  mul_nonneg (formMass_nonneg _) (sq_nonneg _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegratedTruncatedControl
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

namespace CoulombAtom
open CoulombNeumann CoulombAnalysis
local instance instFactNeENNRealHDivOfNatTop_solutions_5 : Fact ((5/3:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_3_re73791_1 (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_3_re73791_1 (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
attribute [local instance] OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_3
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_3 (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma patch_test_continuous_of_memLp (R : ℝ) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    Continuous (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) := by
  have he : (fun f : TFLp (ballMeasure R) => ∫ x, g x*f x ∂ballMeasure R) =
      tfPatchPair R (hm.toLp g) := by
    funext f
    rw [tfPatchPair_apply]
    exact integral_congr_ae (hm.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx])
  rw [he]
  exact (tfPatchPair R (hm.toLp g)).continuous

lemma truncated_kernel_memLp (R : ℝ) {t : ℝ} (ht : 0 < t) :
    MemLp (fun x : TFSpace => 1/max ‖x‖ t) (5/2) (ballMeasure R) := by
  have hc : Continuous (fun x : TFSpace => 1/max ‖x‖ t) :=
    continuous_const.div (continuous_norm.max continuous_const)
      (fun x => (ht.trans_le (le_max_right ‖x‖ t)).ne')
  apply MemLp.of_bound hc.aestronglyMeasurable (1/t)
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact one_div_le_one_div_of_le ht (le_max_right _ _)

local instance instFactNeENNRealHDivOfNatTop_solutions_6_re73791_1 : Fact ((5/2:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
lemma weightedPatchTestSquare_memLp_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    AEMeasurable (weightedPatchTestSquare ψ s Z lam y R hb S g) := by
  have hmass := (hψ.coreSlice_mass_integrable s).aestronglyMeasurable.aemeasurable
  have hs : Measurable (fun u : Configuration M => retainedPatchLp hb (S u) u y R) :=
    retainedPatchLp_measurable hb S id hS measurable_id y R
  have hr := conditionalPatchMinimizer_aemeasurable hψ s Z lam y R
  have hp := (patch_test_continuous_of_memLp R hm).measurable.comp_aemeasurable
    (hs.aemeasurable.sub hr)
  exact hmass.mul (hp.pow_const 2)

lemma weightedPatchTruncatedSquare_le {N M : ℕ} (ψ : FormVector (N+M)) (s : Spins M)
    (Z lam : ℝ) (y : Space) {R t : ℝ} (ht : 0 < t) (hR : t < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M)) (u : Configuration M) :
    weightedPatchTestSquare ψ s Z lam y R hb S (fun x => 1/max ‖x‖ t) u ≤
      (2/t)*weightedPatchGap ψ s Z lam y R hb S u := by
  have hh := mul_le_mul_of_nonneg_left
    (tfPatchGap_truncated_control ht hR tfKinetic tfKinetic_pos
      (conditionalPatchField ψ s Z lam y R u) (retainedPatchLp_nonneg hb (S u) u y R))
    (formMass_nonneg (coreSlice ψ s u))
  simpa only [weightedPatchTestSquare,weightedPatchGap,mul_left_comm,mul_assoc] using hh

lemma weightedPatchTruncatedSquare_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R t : ℝ} (ht : 0 < t) (hR : t < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestSquare ψ s Z lam y R hb S (fun x => 1/max ‖x‖ t)) := by
  apply (hi.const_mul (2/t)).mono'
    (weightedPatchTestSquare_memLp_aemeasurable hψ s Z lam y R hb S hS
      (truncated_kernel_memLp R ht)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs,abs_of_nonneg (weightedPatchTestSquare_nonneg ψ s Z lam y R hb S _ u)]
    exact weightedPatchTruncatedSquare_le ψ s Z lam y ht hR hb S u

lemma integral_weightedPatchTruncatedSquare_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R t : ℝ} (ht : 0 < t) (hR : t < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    (∫ u, weightedPatchTestSquare ψ s Z lam y R hb S (fun x => 1/max ‖x‖ t) u) ≤
      (2/t)*(∫ u, weightedPatchGap ψ s Z lam y R hb S u) := by
  rw [←integral_const_mul]
  exact integral_mono (weightedPatchTruncatedSquare_integrable hψ s Z lam y ht hR hb S hS hi)
    (hi.const_mul _) (weightedPatchTruncatedSquare_le ψ s Z lam y ht hR hb S)

theorem radial_truncated_test_control {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {r : ℝ} (hr : 0 < r) (hR : r < t-4*b) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestSquare (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) ≤
      (2/r)*
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
          (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
          (radialPatchRetention N y t b c s) u) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  exact integral_weightedPatchTruncatedSquare_le
    (orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) hψ.sobolevVector c)
    s Z lam y hr hR hb _ (radialPatchRetention_measurable N y t b c s)
    (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PotentialRecovery
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_PotentialRecovery_scope

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma truncated_potential_remainder {R t : ℝ} (ht : 0 < t) (htR : t < R)
    {f : TFSpace → ℝ} (hf : MemLp f (5/3) (ballMeasure R)) :
    |(∫ x, f x/‖x‖ ∂ballMeasure R)-
      (∫ x, (1/max ‖x‖ t)*f x ∂ballMeasure R)| ≤
      ∫ x in ball 0 t, ‖f x‖/‖x‖ := by
  have hi : Integrable (fun x => f x/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul hf using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  have hj : Integrable (fun x => (1/max ‖x‖ t)*f x) (ballMeasure R) := by
    convert! (truncated_kernel_memLp R ht).integrable_mul hf using 1
    all_goals try with_reducible_and_instances rfl
  have hn : Integrable (fun x => ‖f x‖/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul hf.norm using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  have hb := hn.indicator (measurableSet_ball (x := (0:TFSpace)) (ε := t))
  have he : (∫ x, (ball (0:TFSpace) t).indicator (fun x => ‖f x‖/‖x‖) x ∂ballMeasure R) =
      ∫ x in ball 0 t, ‖f x‖/‖x‖ := by
    rw [integral_indicator measurableSet_ball]
    change (∫ x, ‖f x‖/‖x‖ ∂(volume.restrict (ball 0 R)).restrict (ball 0 t)) = _
    rw [Measure.restrict_restrict measurableSet_ball,
      inter_eq_left.mpr (ball_subset_ball htR.le)]
  rw [←integral_sub hi hj]
  rw [←he,←Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le hb
  filter_upwards [ae_restrict_of_ae (ae_ne_point (0:Space))] with x hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  by_cases hxt : ‖x‖ < t
  · rw [indicator_of_mem (by simpa only [mem_ball_zero_iff] using hxt)]
    have hle := one_div_le_one_div_of_le hx0 (le_max_left ‖x‖ t)
    have hpos : 0 ≤ 1/‖x‖-1/max ‖x‖ t := sub_nonneg.mpr hle
    have hid : f x/‖x‖-(1/max ‖x‖ t)*f x = (1/‖x‖-1/max ‖x‖ t)*f x := by ring
    rw [hid,norm_mul,Real.norm_eq_abs,abs_of_nonneg hpos,div_eq_inv_mul]
    have hh := mul_le_mul_of_nonneg_right
      (sub_le_self (1/‖x‖) (by positivity : 0 ≤ 1/max ‖x‖ t)) (norm_nonneg (f x))
    simpa only [one_div,div_eq_inv_mul,mul_one] using hh
  · rw [indicator_of_notMem (by simpa only [mem_ball_zero_iff] using hxt),
      max_eq_left (le_of_not_gt hxt)]
    simp [div_eq_mul_inv,mul_comm]

lemma tfBallPotential_at_zero (R : ℝ) (f : TFLp (ballMeasure R)) :
    tfBallPotential R f 0 = ∫ x, f x/‖x‖ ∂ballMeasure R := by
  simp only [tfBallPotential,zero_sub,norm_neg]

end CoulombAnalysis

end Work_PotentialRecovery_scope

open MeasureTheory Filter
open scoped ENNReal

namespace CoulombAtom

lemma weighted_abs_integrable_and_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {w f : α → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hi : Integrable w μ)
    (hf : AEStronglyMeasurable f μ)
    (hs : Integrable (fun x => w x*(f x)^2) μ) :
    Integrable (fun x => w x*|f x|) μ ∧
      (∫ x, w x*|f x| ∂μ) ≤ Real.sqrt (∫ x, w x ∂μ)*
        Real.sqrt (∫ x, w x*(f x)^2 ∂μ) := by
  let a := fun x => Real.sqrt (w x)
  let b := fun x => Real.sqrt (w x)*|f x|
  have ha : AEStronglyMeasurable a μ := Real.continuous_sqrt.comp_aestronglyMeasurable hi.aestronglyMeasurable
  have hb : AEStronglyMeasurable b μ := ha.mul hf.norm
  have ha2 (x : α) : a x^2 = w x := Real.sq_sqrt (hw x)
  have hb2 (x : α) : b x^2 = w x*(f x)^2 := by
    dsimp only [b]
    rw [mul_pow,Real.sq_sqrt (hw x),sq_abs]
  have hab (x : α) : a x*b x = w x*|f x| := by
    dsimp only [a,b]
    rw [←mul_assoc,←pow_two,Real.sq_sqrt (hw x)]
  have hma : MemLp a 2 μ := (memLp_two_iff_integrable_sq ha).2 (by simpa only [ha2] using hi)
  have hmb : MemLp b 2 μ := (memLp_two_iff_integrable_sq hb).2 (by simpa only [hb2] using hs)
  have hip : Integrable (fun x => a x*b x) μ := by
    convert! hma.integrable_mul hmb using 1
    all_goals try with_reducible_and_instances rfl
  refine ⟨by simpa only [hab] using hip,?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) (f := a) (g := b)
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => Real.sqrt_nonneg (w x))
    (Eventually.of_forall fun x => mul_nonneg (Real.sqrt_nonneg (w x)) (abs_nonneg (f x)))
    (show MemLp a (ENNReal.ofReal 2) μ by simpa using hma)
    (show MemLp b (ENNReal.ofReal 2) μ by simpa using hmb)
  simpa only [hab,Real.rpow_two,ha2,hb2,←Real.sqrt_eq_rpow] using h

lemma finite_weighted_abs_bound {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    {μ : ∀ i, Measure (α i)} {w f : ∀ i, α i → ℝ}
    (hw : ∀ i x, 0 ≤ w i x) (hi : ∀ i, Integrable (w i) (μ i))
    (hf : ∀ i, AEStronglyMeasurable (f i) (μ i))
    (hs : ∀ i, Integrable (fun x => w i x*(f i x)^2) (μ i)) :
    (∑ i, ∫ x, w i x*|f i x| ∂μ i) ≤
      Real.sqrt (∑ i, ∫ x, w i x ∂μ i)*
        Real.sqrt (∑ i, ∫ x, w i x*(f i x)^2 ∂μ i) := by
  calc
    _ ≤ ∑ i, Real.sqrt (∫ x, w i x ∂μ i)*
        Real.sqrt (∫ x, w i x*(f i x)^2 ∂μ i) :=
      Finset.sum_le_sum fun i _ => (weighted_abs_integrable_and_bound (hw i) (hi i) (hf i) (hs i)).2
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le Finset.univ
      (fun i => integral_nonneg (hw i))
      (fun i => integral_nonneg (fun x => mul_nonneg (hw i x) (sq_nonneg _)))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ExpectedTruncatedControl
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ExpectedTruncatedControl_scope

open MeasureTheory Set Metric
open scoped BigOperators ENNReal NNReal ContDiff

open CoulombNeumann CoulombAnalysis
local instance instFactNeENNRealHDivOfNatTop_solutions_7 : Fact ((5/3:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
local instance instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_4_re73791_1 (R : ℝ) : MeasurableSpace (TFField R) := borel _
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFField_4_re73791_1 (R : ℝ) : BorelSpace (TFField R) := ⟨rfl⟩
attribute [local instance] OAI.CoulombAtom.instMeasurableSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_4
local instance instBorelSpaceSubtypeAEEqFunTFSpaceRealBallMeasureMemAddSubgroupTFLp_4 (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

local instance instFactNeENNRealHDivOfNatTop_solutions_8_re73791_1 : Fact ((5/2:ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by finiteness⟩
lemma patchTestError_aestronglyMeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u}) {g : TFSpace → ℝ}
    (hm : MemLp g (5/2) (ballMeasure R)) :
    AEStronglyMeasurable (fun u =>
      ∫ x, g x*(retainedPatchLp hb (S u) u y R-
        tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ s Z lam y R u)) x
          ∂ballMeasure R) := by
  have hs : Measurable (fun u : Configuration M => retainedPatchLp hb (S u) u y R) :=
    retainedPatchLp_measurable hb S id hS measurable_id y R
  have hr := conditionalPatchMinimizer_aemeasurable hψ s Z lam y R
  exact ((patch_test_continuous_of_memLp R hm).measurable.comp_aemeasurable
    (hs.aemeasurable.sub hr)).aestronglyMeasurable

lemma weightedPatchTruncatedAbs_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (Z lam : ℝ) (y : Space)
    {R r : ℝ} (hr : 0 < r) (hR : r < R)
    {b : ℝ} (hb : 0 < b) (S : Configuration M → Finset (Fin M))
    (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/max ‖x‖ r)) :=
  (weighted_abs_integrable_and_bound (fun _ => formMass_nonneg _)
    (hψ.coreSlice_mass_integrable s)
    (patchTestError_aestronglyMeasurable hψ s Z lam y R hb S hS (truncated_kernel_memLp R hr))
    (weightedPatchTruncatedSquare_integrable hψ s Z lam y hr hR hb S hS hi)).1

theorem radial_truncated_absolute_control {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {r : ℝ} (hr : 0 < r) (hR : r < t-4*b) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestAbs (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/r)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (orderedCutForm (coreFirstRadialCut y ht hb)
            (coreFirstRadialCut_partition y ht hb) ψ c) s Z lam y (t-4*b) hb
            (radialPatchRetention N y t b c s) u)) := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let I := (c : Fin N → Fin 2) × Spins (cutOutNumber c)
  let w := fun i : I => fun u : Configuration (cutOutNumber i.1) =>
    formMass (coreSlice (orderedCutForm p hp ψ i.1) i.2 u)
  let f := fun i : I => fun u : Configuration (cutOutNumber i.1) =>
    ∫ x, (1/max ‖x‖ r)*(retainedPatchLp hb (radialPatchRetention N y t b i.1 i.2 u) u y (t-4*b)-
      tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos
        (conditionalPatchField (orderedCutForm p hp ψ i.1) i.2 Z lam y (t-4*b) u)) x
      ∂ballMeasure (t-4*b)
  have hχ (c : Fin N → Fin 2) : SobolevVector (orderedCutForm p hp ψ c) :=
    orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hgap (i : I) := radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam
    hg hcg hgn hrad hgs i.1 i.2
  have hcs := finite_weighted_abs_bound (μ := fun i : I => (volume : Measure (Configuration (cutOutNumber i.1))))
    (w := w) (f := f) (fun _ _ => formMass_nonneg _)
    (fun i => (hχ i.1).coreSlice_mass_integrable i.2)
    (fun i => patchTestError_aestronglyMeasurable (hχ i.1) i.2 Z lam y (t-4*b) hb _
      (radialPatchRetention_measurable N y t b i.1 i.2) (truncated_kernel_memLp _ hr))
    (fun i => weightedPatchTruncatedSquare_integrable (hχ i.1) i.2 Z lam y hr hR hb _
      (radialPatchRetention_measurable N y t b i.1 i.2) (hgap i))
  have hmass : (∑ i : I, ∫ u, w i u) = formMass ψ := by
    rw [Fintype.sum_sigma]
    change (∑ c, ∑ s, ∫ u, formMass (coreSlice (orderedCutForm p hp ψ c) s u)) = _
    simp_rw [SobolevVector.integral_coreSlice_mass (hχ _)]
    exact orderedCutForm_mass_sum p hp hψ.sobolevVector
  rw [hmass,Fintype.sum_sigma,Fintype.sum_sigma] at hcs
  change (∑ c, ∑ s, ∫ u, weightedPatchTestAbs (orderedCutForm p hp ψ c) s Z lam y _ hb
    (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c, ∑ s, ∫ u, weightedPatchTestSquare (orderedCutForm p hp ψ c) s Z lam y _ hb
          (radialPatchRetention N y t b c s) (fun x => 1/max ‖x‖ r) u) at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (radial_truncated_test_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hr hR))
    (Real.sqrt_nonneg _))

end Work_ExpectedTruncatedControl_scope

open MeasureTheory Filter Set Metric
open scoped ENNReal ContDiff

open CoulombAnalysis

lemma scaled_packet_density_compact {b : ℝ} (hb : 0 < b) {g : Space → ℝ}
    (hg : HasCompactSupport g) : HasCompactSupport (fun z => (scaledRealPacket b g z)^2) := by
  convert! (scaledRealPacket_compact hb hg).mul_right (f' := scaledRealPacket b g) using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  exact pow_two _

lemma masterKernel_pole_measurable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀)
    (hs : 0 < s) {g : Space → ℝ} (hg : Continuous g) (y : Space) :
    Measurable (fun x => tfPotential (masterKernel c₁ r₀ s g x) y) := by
  have hm : Measurable (fun p : Space × Space => masterKernel c₁ r₀ s g p.1 p.2/‖y-p.2‖) :=
    (masterKernel_joint_continuous hc hr hs hg).measurable.div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_TranslatedShortRange
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped ContDiff

namespace CoulombAnalysis

lemma ball_translation_preserving (y : TFSpace) (R : ℝ) :
    MeasurePreserving (fun x : TFSpace => y+x) (ballMeasure R) (volume.restrict (ball y R)) := by
  have h := (measurePreserving_add_left (volume : Measure TFSpace) y).restrict_preimage
    (measurableSet_ball (x := y) (ε := R))
  have he : (fun x : TFSpace => y+x) ⁻¹' ball y R = ball 0 R := by
    ext x
    simp only [mem_preimage,mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero]
  simpa only [he,ballMeasure] using h

lemma setIntegral_translate_ball (y : TFSpace) (R : ℝ) (f : TFSpace → ℝ) :
    (∫ x in ball 0 R, f (y+x)) = ∫ x in ball y R, f x :=
  (ball_translation_preserving y R).integral_comp (MeasurableEquiv.addLeft y).measurableEmbedding f

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FineLocalPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma varthetaScaled_local_potential_le {b q : ℝ} (hb : 0 < b)
    (y a : Space) (ha : a ≠ y) :
    (∫ z in ball y q, varthetaScaled b (z-a)/‖y-z‖) ≤
      (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) a := by
  by_cases hnear : a ∈ ball y (q+Real.sqrt 3*b)
  · rw [indicator_of_mem hnear]
    calc
      _ ≤ ∫ z : Space, varthetaScaled b (z-a)/‖y-z‖ :=
        setIntegral_le_integral
          (translated_pole_integrable (varthetaScaled_integrable hb) (varthetaScaled_memLp hb) y a)
          (Eventually.of_forall fun z => div_nonneg (varthetaScaled_nonneg hb _) (norm_nonneg _))
      _ = tfPotential (varthetaScaled b) (y-a) := integral_translated_pole _ _ _
      _ ≤ _ := varthetaScaled_potential_le hb (sub_ne_zero.mpr ha.symm)
  · rw [indicator_of_notMem hnear]
    apply le_of_eq
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    have hzero : varthetaScaled b (z-a) = 0 := by
      by_contra hne
      have hs := varthetaScaled_support_bound hb (z-a) hne
      have hd := dist_triangle a z y
      have hfar : q+Real.sqrt 3*b ≤ dist a y := le_of_not_gt hnear
      have hclose : dist z y < q := hz
      rw [←dist_eq_norm,dist_comm z a] at hs
      linarith
    simp only [hzero,zero_div,Pi.zero_apply]

lemma retainedSmear_local_potential_le {N : ℕ} {b q : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hxy : ∀ i ∈ S, x i ≠ y) :
    (∫ z in ball y q, retainedSmear b S x z/‖y-z‖) ≤
      ∑ i ∈ S, (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
  simp only [retainedSmear,Finset.sum_div]
  rw [integral_finsetSum _ (fun i _ =>
    (translated_pole_integrable (varthetaScaled_integrable hb) (varthetaScaled_memLp hb) y (x i)).restrict)]
  exact Finset.sum_le_sum (fun i hi => varthetaScaled_local_potential_le hb y (x i) (hxy i hi))

theorem retainedPatchLp_local_potential_le {N : ℕ} {b q R : ℝ} (hb : 0 < b) (hqR : q ≤ R)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hxy : ∀ i ∈ S, x i ≠ y) :
    (∫ z in ball 0 q, ‖retainedPatchLp hb S x y R z‖/‖z‖) ≤
      ∑ i ∈ S, (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (x i) := by
  have he := ae_mono (Measure.restrict_mono (ball_subset_ball hqR) le_rfl)
    (retainedPatchLp_ae hb S x y R)
  have hid : (∫ z in ball 0 q, ‖retainedPatchLp hb S x y R z‖/‖z‖) =
      ∫ z in ball 0 q, retainedSmear b S x (y+z)/‖z‖ := by
    apply integral_congr_ae
    filter_upwards [he] with z hz
    rw [hz,Real.norm_of_nonneg (retainedSmear_nonneg hb S x _)]
  rw [hid]
  have ht := setIntegral_translate_ball y q (fun z => retainedSmear b S x z/‖y-z‖)
  simp only [sub_add_cancel_left,norm_neg] at ht
  rw [ht]
  exact retainedSmear_local_potential_le hb S x y hxy

end CoulombNeumann

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_IntegrableCutTower
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_IntegrableCutTower_scope

open MeasureTheory Set Filter
open scoped BigOperators

lemma cutOuter_expectation_eq_full_integrable {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (ψ : FormVector L)
    (c : Fin L → Fin 2) (g : Configuration (cutOutNumber c) → ℝ)
    (hi : ∀ s : Spins (cutCoreNumber c+cutOutNumber c), Integrable (fun x =>
      g (outProjection x)*‖(orderedCutForm p hp ψ c).value s x‖^2)) :
    (∑ s : Spins (cutOutNumber c), ∫ u,
      g u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) =
      ∑ s : Spins L, ∫ x, g (cutOutPositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 := by
  rw [weighted_coreSlice_eq_full_integrable _ _ hi]
  have he (s : Spins (cutCoreNumber c+cutOutNumber c)) :
      (∫ x, g (outProjection x)*‖(orderedCutForm p hp ψ c).value s x‖^2) =
      ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value
        (s ∘ (cutOrder c).symm) x‖^2 := by
    simpa only [orderedCutForm,reindexForm,cutOutPositions_reindex] using
      integral_reindex (cutOrder c) (fun x => g (cutOutPositions c x)*
        ‖(multiplyForm (spatialProduct p hp c) ψ).value (s ∘ (cutOrder c).symm) x‖^2)
  simp_rw [he]
  exact sum_spin_reindex (cutOrder c) (fun s : Spins L =>
    ∫ x, g (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2)

end Work_IntegrableCutTower_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma rawLocalPotential_nonneg {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) :
    0 ≤ rawLocalPotential y q x := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · positivity
  · exact le_rfl

lemma rawLocalPotential_measurable (N : ℕ) (y : Space) (q : ℝ) :
    Measurable (rawLocalPotential (N := N) y q) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_lt (configuration_distance_measurable y i) measurable_const)
    (measurable_const.div (configuration_distance_measurable y i)) measurable_const

lemma rawLocalPotential_weighted_integrable {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (s : Spins N) (y : Space) (q : ℝ) :
    Integrable (fun x => rawLocalPotential y q x*‖ψ.value s x‖^2) := by
  simp only [rawLocalPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  have hi := (hψ.shifted_nuclear_integrable s i y).indicator
    (measurableSet_lt (configuration_distance_measurable y i) (measurable_const (a := q)))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [indicator_apply,mul_ite,div_eq_mul_inv,mul_comm]

lemma rawLocalPotential_core_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) (q : ℝ) :
    Integrable (fun u => rawLocalPotential y q u*formMass (coreSlice ψ s u)) := by
  simp only [rawLocalPotential,Finset.sum_mul]
  apply integrable_finsetSum
  intro i _
  have hi := (coreSlice_mass_shifted_integrable hψ s i y).indicator
    (measurableSet_lt (configuration_distance_measurable y i) (measurable_const (a := q)))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [indicator_apply,mul_ite,div_eq_mul_inv,mul_comm]

lemma rawLocalPotential_out_weighted_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins (N+M)) (y : Space) (q : ℝ) :
    Integrable (fun x => rawLocalPotential y q (outProjection x)*‖ψ.value s x‖^2) := by
  simp only [rawLocalPotential,Finset.sum_mul,outProjection]
  apply integrable_finsetSum
  intro i _
  have hi := (hψ.shifted_nuclear_integrable s (finSumFinEquiv (Sum.inr i)) y).indicator
    (measurableSet_lt (configuration_distance_measurable y (finSumFinEquiv (Sum.inr i))) (measurable_const (a := q)))
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp [indicator_apply,mul_ite,div_eq_mul_inv,mul_comm]

lemma rawLocalPotential_cutOutPositions_le {N : ℕ} (y : Space) (q : ℝ)
    (c : Fin N → Fin 2) (x : Configuration N) :
    rawLocalPotential y q (cutOutPositions c x) ≤ rawLocalPotential y q x := by
  classical
  let e : Fin (cutOutNumber c) → Fin N := fun i => cutOrder c (finSumFinEquiv (Sum.inr i))
  have hinj : Function.Injective e :=
    (cutOrder c).injective.comp (finSumFinEquiv.injective.comp Sum.inr_injective)
  let k : Fin N → ℝ := fun i => if ‖x i-y‖ < q then 1/‖x i-y‖ else 0
  have hn (i : Fin N) : 0 ≤ k i := by dsimp only [k]; split_ifs <;> positivity
  change (∑ i, k (e i)) ≤ ∑ i, k i
  calc
    _ = ∑ i ∈ Finset.univ.image e, k i := (Finset.sum_image (fun i _ j _ h => hinj h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hn i)

lemma rawLocalPotential_cut_weighted_integrable {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (c : Fin N → Fin 2)
    (s : Spins N) (y : Space) (q : ℝ) :
    Integrable (fun x => rawLocalPotential y q (cutOutPositions c x)*
      ‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) := by
  have hmp := (hψ.multiply (spatialProduct p hp c)).1 s
  have hmeas : Measurable (cutOutPositions c) := by
    apply Measurable.of_eval
    exact fun _ => measurable_pi_apply _
  apply (rawLocalPotential_weighted_integrable (hψ.multiply (spatialProduct p hp c)) s y q).mono'
    (((rawLocalPotential_measurable _ y q).comp hmeas).aestronglyMeasurable.mul
      (hmp.aestronglyMeasurable.norm.pow 2))
  filter_upwards [] with x
  simp only [Pi.mul_apply,Pi.pow_apply,Function.comp_apply]
  rw [Real.norm_of_nonneg (mul_nonneg (rawLocalPotential_nonneg _ _ _) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (rawLocalPotential_cutOutPositions_le y q c x) (sq_nonneg _)

theorem fresh_cut_raw_local_control {N : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections) (hp : ∀ x, ∑ a, (p a).value x^2 = 1)
    {ψ : FormVector N} (hψ : SobolevVector ψ) (y : Space) (q : ℝ) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      rawLocalPotential y q u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤
      ∫ x, rawLocalPotential y q x ∂formRawLaw ψ := by
  have htw (c : Fin N → Fin 2) := cutOuter_expectation_eq_full_integrable p hp ψ c
    (rawLocalPotential y q)
    (fun s => rawLocalPotential_out_weighted_integrable (orderedCutForm_sobolev p hp hψ c) s y q)
  simp_rw [htw]
  have hb : (∑ c : Fin N → Fin 2, ∑ s : Spins N, ∫ x,
      rawLocalPotential y q (cutOutPositions c x)*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) ≤
      ∑ c : Fin N → Fin 2, ∑ s : Spins N, ∫ x,
        rawLocalPotential y q x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2 := by
    apply Finset.sum_le_sum; intro c _
    apply Finset.sum_le_sum; intro s _
    exact integral_mono (rawLocalPotential_cut_weighted_integrable p hp hψ c s y q)
      (rawLocalPotential_weighted_integrable (hψ.multiply _) s y q)
      (fun x => mul_le_mul_of_nonneg_right (rawLocalPotential_cutOutPositions_le y q c x) (sq_nonneg _))
  apply hb.trans_eq
  rw [Finset.sum_comm,formRawLaw_integral hψ]
  have he (s : Spins N) : (∑ c : Fin N → Fin 2, ∫ x,
      rawLocalPotential y q x*‖(multiplyForm (spatialProduct p hp c) ψ).value s x‖^2) =
      ∫ x, rawLocalPotential y q x*‖ψ.value s x‖^2 := by
    rw [←integral_finsetSum _ (fun c _ => rawLocalPotential_weighted_integrable (hψ.multiply _) s y q)]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [←Finset.mul_sum,finite_partition_value (spatialProduct p hp) (spatial_square_partition p hp)]
  simp_rw [he]
  rw [←integral_finsetSum _ (fun s _ => rawLocalPotential_weighted_integrable hψ s y q)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [←Finset.mul_sum,formRawDensity,mul_comm]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_FormRawPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAtom

lemma rawPotential_measurable {N : ℕ} (y : Space) : Measurable (rawPotential (N := N) y) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.div (configuration_distance_measurable y i))

lemma rawLocalPotential_le_raw {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) :
    rawLocalPotential y q x ≤ rawPotential y x := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · positivity

lemma formRawLaw_ae_no_poles {N : ℕ} (ψ : FormVector N) (y : Space) :
    ∀ᵐ x ∂formRawLaw ψ, ∀ i, x i ≠ y := by
  apply (withDensity_absolutelyContinuous volume _).ae_le
  exact ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ : Fin N => (volume : Measure Space)) i y)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_RadialPatchCap
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

namespace CoulombAtom
open CoulombAnalysis

theorem radialPatchMinimizer_nonradial_cap {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hbt : 4*b < t) (hy : t ≤ ‖y‖) (Z lam : ℝ) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := orderedCutForm p hp ψ c
    ∀ᵐ u, ∀ x : Space, ‖x‖ ≤ 3*(t-4*b)/4 →
      let f := tfPatchMinimizer (t-4*b) tfKinetic tfKinetic_pos
        (conditionalPatchField χ s Z lam y (t-4*b) u)
      normalizedCoreField Z lam (coreSlice χ s u) (y+x)-tfBallPotential (t-4*b) f x ≤
        tfPatchCapConstant/(t-4*b)^4 := by
  dsimp only
  filter_upwards [(orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c).ae_coreSlice s] with u hu
  intro x hx
  apply conditionalPatchMinimizer_nonradial_cap _ s u hu (radialPatchCore y t) _ y
    (by linarith) hb hb (radialPatch_nuclear_distance hb hy)
    (radialPatch_core_distance y hb) Z lam x hx
  intro x i hi
  apply FormZeroAt.coreSlice
  exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
    (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
    (joinLists x u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)

end CoulombAtom

open MeasureTheory Filter Set Metric Laplacian
open scoped BigOperators ContDiff Topology

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PatchCenterObservable
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann
attribute [local instance] OAI.CoulombAtom.patchCenterMeasurableSpace
local instance patchCenterBorelSpace (R : ℝ) : BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma tfBallPotential_zero_continuous (R : ℝ) :
    Continuous (fun f : TFLp (ballMeasure R) => tfBallPotential R f 0) := by
  convert patch_test_continuous_of_memLp R (nuclear_memLp R) using 1
  all_goals try with_reducible_and_instances rfl
  funext f
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [zero_sub,norm_neg]
    ring

lemma conditionalPatchCenter_aemeasurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (Z lam : ℝ) (y : Space) (R : ℝ) :
    AEMeasurable (conditionalPatchCenter ψ t Z lam y R) :=
  (normalizedCoreField_eval_aemeasurable hψ t Z lam y).sub
    ((tfBallPotential_zero_continuous R).measurable.comp_aemeasurable
      (conditionalPatchMinimizer_aemeasurable hψ t Z lam y R))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_DeletedPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

lemma outerDeletedPotential_nonneg {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    0 ≤ outerDeletedPotential y t b u := by
  apply Finset.sum_nonneg; intro i _; split_ifs <;> positivity

lemma outerDeletedPotential_measurable {M : ℕ} (y : Space) (t b : ℝ) :
    Measurable (outerDeletedPotential (M := M) y t b) := by
  apply Finset.measurable_sum; intro i _
  exact (measurable_const.div (configuration_distance_measurable y i)).ite
    (measurableSet_le measurable_const (configuration_distance_measurable y i)) measurable_const

lemma outerDeletedPotential_le_count {M : ℕ} (y : Space) {t b : ℝ} (h : 7*b < t)
    (u : Configuration M) :
    outerDeletedPotential y t b u ≤ outerDeletedCount y t b u/(t-7*b) := by
  rw [outerDeletedCount,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  split_ifs with hi
  · exact one_div_le_one_div_of_le (by linarith) hi
  · simp

lemma outerDeletedPotential_le {M : ℕ} (y : Space) {t b : ℝ} (h : 7*b < t) (u : Configuration M) :
    outerDeletedPotential y t b u ≤ M/(t-7*b) :=
  (outerDeletedPotential_le_count y h u).trans
    (div_le_div_of_nonneg_right (outerDeletedCount_le y t b u) (by linarith))

lemma weighted_outerDeletedPotential_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) {t b : ℝ} (h : 7*b < t) :
    Integrable (fun u => outerDeletedPotential y t b u*formMass (coreSlice ψ s u)) :=
  (hψ.coreSlice_mass_integrable s).bdd_mul
    (outerDeletedPotential_measurable y t b).aestronglyMeasurable
    (ae_of_all _ (fun u => by
      rw [Real.norm_of_nonneg (outerDeletedPotential_nonneg y t b u)]
      exact outerDeletedPotential_le y h u))

theorem fresh_cut_deleted_potential_bound {N : ℕ} (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {t b : ℝ} (h : 7*b < t) :
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      outerDeletedPotential y t b u*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) ≤
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          outerDeletedCount y t b u^2*formMass (coreSlice (orderedCutForm p hp ψ c) s u))/(t-7*b) := by
  let I := (c : Fin N → Fin 2) × Spins (cutOutNumber c)
  let w := fun i : I => fun u : Configuration (cutOutNumber i.1) =>
    formMass (coreSlice (orderedCutForm p hp ψ i.1) i.2 u)
  let f := fun i : I => fun u : Configuration (cutOutNumber i.1) => outerDeletedCount y t b u
  have hχ (c : Fin N → Fin 2) := orderedCutForm_sobolev p hp hψ c
  have hi (i : I) : Integrable (fun u => f i u*w i u) :=
    ((hχ i.1).coreSlice_mass_integrable i.2).bdd_mul
      (outerDeletedCount_measurable y t b).aestronglyMeasurable
      (ae_of_all _ (fun u => by
        rw [Real.norm_of_nonneg (outerDeletedCount_nonneg y t b u)]
        exact outerDeletedCount_le y t b u))
  have hi2 (i : I) : Integrable (fun u => w i u*(f i u)^2) := by
    have H := ((hχ i.1).coreSlice_mass_integrable i.2).bdd_mul
      ((outerDeletedCount_measurable y t b).pow_const 2).aestronglyMeasurable
      (ae_of_all _ (fun u => norm_sq_le_of_nonneg (outerDeletedCount_nonneg y t b u)
        (outerDeletedCount_le y t b u)))
    simpa only [mul_comm] using H
  have hcs := finite_weighted_abs_bound
    (μ := fun i : I => (volume : Measure (Configuration (cutOutNumber i.1))))
    (w := w) (f := f) (fun _ _ => formMass_nonneg _)
    (fun i => (hχ i.1).coreSlice_mass_integrable i.2)
    (fun _ => (outerDeletedCount_measurable y t b).aestronglyMeasurable) hi2
  have hmass : (∑ i : I, ∫ u, w i u) = formMass ψ := by
    rw [Fintype.sum_sigma]
    change (∑ c, ∑ s, ∫ u, formMass (coreSlice (orderedCutForm p hp ψ c) s u)) = _
    simp_rw [SobolevVector.integral_coreSlice_mass (hχ _)]
    exact orderedCutForm_mass_sum p hp hψ
  have hc (i : I) : (∫ u, outerDeletedPotential y t b u*w i u) ≤
      (∫ u, f i u*w i u)/(t-7*b) := by
    rw [←integral_div]
    apply integral_mono (weighted_outerDeletedPotential_integrable (hχ i.1) i.2 y h)
      ((hi i).div_const _)
    intro u
    have hh := mul_le_mul_of_nonneg_right (outerDeletedPotential_le_count y h u)
      (formMass_nonneg (coreSlice (orderedCutForm p hp ψ i.1) i.2 u))
    simpa only [div_mul_eq_mul_div] using hh
  rw [hmass] at hcs
  have hcauchy : (∑ i : I, ∫ u, f i u*w i u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt (∑ i : I, ∫ u, (f i u)^2*w i u) := by
    simpa only [f,abs_of_nonneg (outerDeletedCount_nonneg y t b _),mul_comm] using hcs
  have hd : (∑ i : I, ∫ u, outerDeletedPotential y t b u*w i u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt (∑ i : I, ∫ u, (f i u)^2*w i u)/(t-7*b) := calc
    _ ≤ (∑ i : I, ∫ u, f i u*w i u)/(t-7*b) := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum (fun i _ => hc i)
    _ ≤ _ := div_le_div_of_nonneg_right hcauchy (by linarith)
  rw [Fintype.sum_sigma, Fintype.sum_sigma] at hd
  simpa only [w,f] using hd

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_FreshFieldTower
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

namespace CoulombNeumann
open CoulombAtom CoulombAnalysis

lemma retainedPatchLp_potential {N : ℕ} {b R : ℝ} (hb : 0 < b)
    (S : Finset (Fin N)) (x : Configuration N) (y : Space)
    (hmargin : ∀ i ∈ S, ‖x i-y‖+Real.sqrt 3*b ≤ R) :
    tfBallPotential R (retainedPatchLp hb S x y R) 0 = tfPotential (retainedSmear b S x) y := by
  rw [←tfPotential_extension]
  have he : tfPotential (tfExtension R (retainedPatchLp hb S x y R)) 0 =
      ∫ z, retainedSmear b S x (y+z)/‖z‖ := by
    apply integral_congr_ae
    filter_upwards [retainedPatchLp_extension hb S x y hmargin] with z hz
    simp only [hz,zero_sub,norm_neg]
  rw [he]
  have ht := integral_add_left_eq_self (μ := volume)
    (fun z => retainedSmear b S x z/‖y-z‖) y
  simpa only [sub_add_cancel_left,norm_neg,tfPotential] using ht

end CoulombNeumann
namespace CoulombAtom
open CoulombNeumann CoulombAnalysis

lemma rawLocalPotential_indicator {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) :
    rawLocalPotential y q x = ∑ i, (ball y q).indicator (fun z => 1/‖y-z‖) (x i) := by
  classical
  simp only [rawLocalPotential, indicator_apply, mem_ball, dist_eq_norm, norm_sub_rev]

lemma rawPotential_retained_deleted {M : ℕ} (y : Space) (t b : ℝ) (u : Configuration M) :
    rawPotential y u = rawLocalPotential y (t-7*b) u+outerDeletedPotential y t b u := by
  rw [rawPotential,rawLocalPotential,outerDeletedPotential,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ‖u i-y‖ < t-7*b
  · simp [h, not_le.mpr h]
  · simp [h, le_of_not_gt h]

lemma radial_fine_potential_loss_ae {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :
    ∀ᵐ u : Configuration (cutOutNumber c),
      0 ≤ rawLocalPotential y (t-7*b) u-
        tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0 ∧
      rawLocalPotential y (t-7*b) u-
        tfBallPotential (t-4*b) (retainedPatchLp hb (radialPatchRetention N y t b c s u) u y (t-4*b)) 0 ≤
      rawLocalPotential y (Real.sqrt 3*b) u := by
  have he : ∀ᵐ u : Configuration (cutOutNumber c), ∀ i, u i ≠ y :=
    ae_all_iff.mpr (fun i => Measure.ae_eval_ne (fun _ : Fin (cutOutNumber c) => (volume : Measure Space)) i y)
  filter_upwards [he] with u hu
  rw [retainedPatchLp_potential hb _ u y (radialPatch_retained_margin y hb c s u)]
  have hh := retainedSmear_potential_loss hb (radialPatchRetention N y t b c s u) u y (fun i _ => hu i)
  have hret : (∑ i ∈ radialPatchRetention N y t b c s u, 1/‖y-u i‖) = rawLocalPotential y (t-7*b) u := by
    simp only [radialPatchRetention,Finset.sum_filter,rawLocalPotential,norm_sub_rev]
  rw [hret] at hh
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [rawLocalPotential_indicator]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => indicator_nonneg (fun z _ => by positivity) _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ObservationIntegral
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombObservation

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_ObservationIntegral_scope

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

lemma eventLog_eq {p : ℝ} (hp : 0 < p) : Real.log (Real.exp 1/p) = 1-Real.log p := by
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hp), Real.log_exp]

end Work_ObservationIntegral_scope

open MeasureTheory Set Finset
open scoped ENNReal NNReal BigOperators ContDiff

lemma observationFisherConstant_pos : 0 < observationFisherConstant := by
  unfold observationFisherConstant
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) observationMomentConstant_pos

end CoulombObservation

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_UnorderedObservations
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_UnorderedObservations_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation

lemma unorderedConfiguration_measurable {N : ℕ} :
    Measurable (unorderedConfiguration (N := N)) := measurable_quotient_mk''

lemma physicalObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (physicalObservedConfiguration (N := N) ell k) := by
  apply Measurable.of_eval
  intro i
  apply (Continuous.measurable (by fun_prop : Continuous (WithLp.toLp 2 : (Fin 3 → ℝ) → Space))).comp
  apply Measurable.of_eval
  intro a
  exact (((EuclideanSpace.proj a : Space →L[ℝ] ℝ).measurable.comp
    ((measurable_pi_apply i).comp measurable_fst)).add
    (((measurable_pi_apply (k,i,a)).comp measurable_snd).const_mul _))

lemma unorderedObservedConfiguration_measurable {N K : ℕ} (ell : Fin K → ℝ) (k : Fin K) :
    Measurable (unorderedObservedConfiguration (N := N) ell k) :=
  unorderedConfiguration_measurable.comp (physicalObservedConfiguration_measurable ell k)

lemma observationInformation_le {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j ≤
      (inferInstance : MeasurableSpace (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))) := by
  apply iSup_le
  intro k
  split_ifs
  · exact (unorderedObservedConfiguration_measurable ell k).comap_le
  · exact bot_le

end CoulombAtom

end Work_UnorderedObservations_scope

open MeasureTheory Set Filter Metric
open scoped BigOperators NNReal

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_OriginalPosteriorKernel
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom
open CoulombObservation ProbabilityTheory

lemma originalDatum_measurable {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    Measurable (originalDatum (N := N) ell j) := by
  apply Measurable.of_comap_le
  change MeasurableSpace.comap id (observationInformation ell j) ≤ _
  simpa only [MeasurableSpace.comap_id] using (observationInformation_le (N := N) ell j)

lemma originalDatum_comap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    MeasurableSpace.comap (originalDatum (N := N) ell j) inferInstance =
      observationInformation ell j := MeasurableSpace.comap_id

lemma kernelPosteriorTest_eq {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
      ∑ i, g (z.1 i)) (physicalObservationLaw μ K)) :
    posteriorTestValue μ ell j g =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z) := by
  have h := condExp_ae_eq_integral_condDistrib (originalDatum_measurable (N := N) ell j)
    measurable_fst.aemeasurable
    ((Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))).stronglyMeasurable) hi
  simpa only [originalDatum_comap,posteriorTestValue,kernelPosteriorTest,originalRawKernel,Function.comp_def] using h

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
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_MasterKernelFubini
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
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
open scoped BigOperators ContDiff

open CoulombAnalysis

lemma masterKernel_pole_integrable {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g) (x y : Space) :
    Integrable (fun z => masterKernel c₁ r₀ s g x z/‖y-z‖) := by
  have hη := scaled_packet_density_compact (masterWidth_pos hc hr hs x) hcg
  have hηc := (scaledRealPacket_smooth (masterWidth c₁ r₀ s x) hg).continuous.pow 2
  exact translated_pole_integrable (hηc.integrable_of_hasCompactSupport hη)
    (hηc.memLp_of_hasCompactSupport hη) y x

lemma master_configuration_potential_integrable {N : ℕ} (ν : Measure (Configuration N))
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun x : Configuration N => ∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y) ν := by
  apply hi.mono' ((Finset.measurable_sum _ (fun i _ =>
    (masterKernel_pole_measurable hc hr hs hg.continuous y).comp (measurable_pi_apply i))).aestronglyMeasurable)
  filter_upwards [he] with x hx
  change ‖∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y‖ ≤ rawPotential y x
  rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ => masterKernel_potential_nonneg c₁ r₀ s g (x i) y))]
  apply Finset.sum_le_sum
  intro i _
  simpa only [norm_sub_rev] using masterKernel_potential_le hc hr hs hg hcg hgn hrad hgs (hx i)

lemma master_configuration_pole_integrable {N : ℕ} (ν : Measure (Configuration N))
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun p : Configuration N × Space => (∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)/‖y-p.2‖)
      (ν.prod volume) := by
  have hm : Measurable (fun p : Configuration N × Space => (∑ i, masterKernel c₁ r₀ s g (p.1 i) p.2)/‖y-p.2‖) :=
    (Finset.measurable_sum _ (fun i _ => (masterKernel_joint_continuous hc hr hs hg.continuous).measurable.comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd))).div (by fun_prop)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun x => ?_),?_⟩
  · simp only [Finset.sum_div]
    exact integrable_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y)
  · have hp := master_configuration_potential_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [Finset.sum_div]
    simp_rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun i _ =>
      div_nonneg (masterKernel_nonneg c₁ r₀ s g (x i) _) (norm_nonneg _)))]
    exact integral_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y)

theorem master_configuration_potential_fubini {N : ℕ} (ν : Measure (Configuration N)) [SFinite ν]
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    tfPotential (fun z => ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν) y =
      ∫ x, ∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y ∂ν := by
  change (∫ z, (∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν)/‖y-z‖) = _
  calc
    _ = ∫ z, ∫ x, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖ ∂ν := by simp only [integral_div]
    _ = ∫ x, (∫ z, (∑ i, masterKernel c₁ r₀ s g (x i) z)/‖y-z‖) ∂ν :=
      integral_integral_swap (master_configuration_pole_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs).swap
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        simp only [Finset.sum_div]
        exact integral_finsetSum _ (fun i _ => masterKernel_pole_integrable hc hr hs hg hcg (x i) y))

section Work_MasterConfigurationLoss_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

open CoulombAnalysis

lemma rawLocalPotential_eq_indicator {N : ℕ} (y : Space) (q : ℝ) (x : Configuration N) :
    rawLocalPotential y q x = ∑ i, (ball y q).indicator (fun z => 1/‖z-y‖) (x i) := by
  classical
  unfold rawLocalPotential
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ‖x i-y‖ < q
  · rw [ite_eq_left h,Set.indicator_of_mem (by simpa only [mem_ball,dist_eq_norm] using h)]
  · rw [ite_eq_right h,Set.indicator_of_notMem (by simpa only [mem_ball,dist_eq_norm] using h)]

lemma rawLocalPotential_integrable_of_raw {N : ℕ} {ν : Measure (Configuration N)}
    (y : Space) (q : ℝ) (hi : Integrable (rawPotential y) ν) :
    Integrable (rawLocalPotential y q) ν := by
  apply hi.mono' (rawLocalPotential_measurable N y q).aestronglyMeasurable
  exact ae_of_all _ (fun x => by
    simpa only [Real.norm_of_nonneg (rawLocalPotential_nonneg y q x)] using
      (rawLocalPotential_le_raw y q x))

theorem master_configuration_potential_loss {N : ℕ} (ν : Measure (Configuration N)) [SFinite ν]
    (y : Space) (hi : Integrable (rawPotential y) ν) (he : ∀ᵐ x ∂ν, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    0 ≤ (∫ x, rawPotential y x ∂ν)-
      tfPotential (fun z => ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν) y ∧
    (∫ x, rawPotential y x ∂ν)-
      tfPotential (fun z => ∫ x, ∑ i, masterKernel c₁ r₀ s g (x i) z ∂ν) y ≤
      ∫ x, rawLocalPotential y (2*masterWidth c₁ r₀ s y) x ∂ν := by
  rw [master_configuration_potential_fubini ν y hi he hc hr hs hg hcg hgn hrad hgs]
  have hp := master_configuration_potential_integrable ν y hi he hc hr hs hg hcg hgn hrad hgs
  rw [←integral_sub hi hp]
  have hh : ∀ᵐ x ∂ν,
      0 ≤ rawPotential y x-(∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y) ∧
      rawPotential y x-(∑ i, tfPotential (masterKernel c₁ r₀ s g (x i)) y) ≤
        rawLocalPotential y (2*masterWidth c₁ r₀ s y) x := by
    filter_upwards [he] with x hx
    have hpoint (i : Fin N) := masterKernel_potential_loss hc hcL hr hs hs1 hg hcg hgn hrad hgs (hx i)
    simp only [rawPotential,←Finset.sum_sub_distrib,rawLocalPotential_eq_indicator]
    constructor
    · exact Finset.sum_nonneg (fun i _ => by simpa only [norm_sub_rev] using (hpoint i).1)
    · apply Finset.sum_le_sum
      intro i _
      simpa only [norm_sub_rev] using (hpoint i).2
  exact ⟨integral_nonneg_of_ae (hh.mono fun _ h => h.1),
    integral_mono_ae (hi.sub hp) (rawLocalPotential_integrable_of_raw y _ hi) (hh.mono fun _ h => h.2)⟩

end Work_MasterConfigurationLoss_scope

open MeasureTheory Filter Set
open scoped BigOperators

open CoulombObservation ProbabilityTheory

lemma originalRawKernel_comp {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) :
    originalRawKernel μ ell j ∘ₘ ((physicalObservationLaw μ K).map (originalDatum ell j)) = μ := by
  rw [originalRawKernel,condDistrib_comp_map (originalDatum_measurable ell j).aemeasurable
    measurable_fst.aemeasurable]
  simp [physicalObservationLaw,Measure.map_fst_prod]

lemma originalRawKernel_ae {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {P : Configuration N → Prop} (hP : ∀ᵐ x ∂μ, P x) :
    ∀ᵐ z ∂physicalObservationLaw μ K, ∀ᵐ x ∂originalRawKernel μ ell j (originalDatum ell j z), P x := by
  rw [←originalRawKernel_comp μ ell j] at hP
  exact ae_of_ae_map (originalDatum_measurable ell j).aemeasurable (Measure.ae_ae_of_ae_comp hP)

lemma originalRawKernel_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {f : Configuration N → ℝ} (hf : Measurable f) (hi : Integrable f μ) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      Integrable f (originalRawKernel μ ell j (originalDatum ell j z)) := by
  have hx := originalDatum_measurable (N := N) ell j
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hi0 : Integrable (fun a : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => f a.1)
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  have hi1 : Integrable (fun p : OriginalDatum N K ell j × Configuration N => f p.2)
      ((physicalObservationLaw μ K).map (fun a => (originalDatum ell j a,a.1))) := by
    apply (integrable_map_measure (hf.comp measurable_snd).aestronglyMeasurable
      (hx.prodMk measurable_fst).aemeasurable).mpr
    exact hi0
  exact hi1.condDistrib_ae hx.aemeasurable measurable_fst.aemeasurable

lemma kernelPosteriorTest_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x : Configuration N => ∑ i, g (x i)) μ) :
    Integrable (fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z))
      (physicalObservationLaw μ K) := by
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hf : Measurable (fun x : Configuration N => ∑ i, g (x i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hg.comp (measurable_pi_apply i))
  have hi0 : Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => ∑ i, g (z.1 i))
      (physicalObservationLaw μ K) := by
    apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
    rwa [he]
  exact integrable_condExp.congr (kernelPosteriorTest_eq μ ell j hg hi0)

lemma kernelPosteriorTest_eq_of_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x : Configuration N => ∑ i, g (x i)) μ) :
    posteriorTestValue μ ell j g =ᵐ[physicalObservationLaw μ K]
      fun z => kernelPosteriorTest μ ell j g (originalDatum ell j z) := by
  have he : (physicalObservationLaw μ K).map Prod.fst = μ := by
    simp [physicalObservationLaw,Measure.map_fst_prod]
  have hf : Measurable (fun x : Configuration N => ∑ i, g (x i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hg.comp (measurable_pi_apply i))
  apply kernelPosteriorTest_eq μ ell j hg
  apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
  rwa [he]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterPosteriorPotential
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
open CoulombAnalysis

lemma jointMasterPosterior_potential_eq_kernel {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    (fun z => tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y) =ᵐ[
      physicalObservationLaw μ K] fun z => kernelPosteriorTest μ ell j
        (fun x => tfPotential (masterKernel c₁ r₀ s g x) y) (originalDatum ell j z) := by
  filter_upwards [originalRawKernel_integrable μ ell j (rawPotential_measurable y) hi,
    originalRawKernel_ae μ ell j he] with z hz hze
  exact master_configuration_potential_fubini _ y hz hze hc hr hs hg hcg hgn hrad hgs

lemma jointMasterPosterior_potential_integrable {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    Integrable (fun z => tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y)
      (physicalObservationLaw μ K) :=
  (kernelPosteriorTest_integrable μ ell j (masterKernel_pole_measurable hc hr hs hg.continuous y)
    (master_configuration_potential_integrable μ y hi he hc hr hs hg hcg hgn hrad hgs)).congr
      (jointMasterPosterior_potential_eq_kernel μ ell j y hi he hc hr hs hg hcg hgn hrad hgs).symm

theorem jointMasterPosterior_potential_loss {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      0 ≤ kernelPosteriorTest μ ell j (fun x => 1/‖x-y‖) (originalDatum ell j z)-
        tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y ∧
      kernelPosteriorTest μ ell j (fun x => 1/‖x-y‖) (originalDatum ell j z)-
        tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y ≤
      kernelPosteriorTest μ ell j ((ball y (2*masterWidth c₁ r₀ s y)).indicator (fun x => 1/‖x-y‖))
        (originalDatum ell j z) := by
  filter_upwards [originalRawKernel_integrable μ ell j (rawPotential_measurable y) hi,
    originalRawKernel_ae μ ell j he] with z hz hze
  unfold jointMasterPosterior kernelPosteriorTest
  simpa only [rawLocalPotential_eq_indicator,rawPotential] using
    (master_configuration_potential_loss (originalRawKernel μ ell j (originalDatum ell j z)) y hz hze
      hc hcL hr hs hs1 hg hcg hgn hrad hgs)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_OriginalKernelEvent
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

namespace CoulombAtom

lemma original_configuration_integrable {N K : ℕ} (μ : Measure (Configuration N))
    (f : Configuration N → ℝ) (hf : Measurable f) (hi : Integrable f μ) :
    Integrable (fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) => f z.1)
      (physicalObservationLaw μ K) := by
  apply (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).mp
  simpa [physicalObservationLaw,Measure.map_fst_prod] using hi

lemma kernelPosteriorTest_setIntegral {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) {g : Space → ℝ} (hg : Measurable g)
    (hi : Integrable (fun x : Configuration N => ∑ i, g (x i)) μ)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    (∫ z in A, kernelPosteriorTest μ ell j g (originalDatum ell j z) ∂physicalObservationLaw μ K) =
      ∫ z in A, ∑ i, g (z.1 i) ∂physicalObservationLaw μ K := by
  rw [←integral_congr_ae (ae_restrict_of_ae (kernelPosteriorTest_eq_of_integrable μ ell j hg hi))]
  exact setIntegral_condExp (observationInformation_le ell j)
    (original_configuration_integrable μ _
      (Finset.measurable_sum _ (fun i _ => hg.comp (measurable_pi_apply i))) hi) hA

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_MasterPotentialEvent
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
open CoulombAnalysis

theorem master_potential_event_loss {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    0 ≤ (∫ z in A, rawPotential y z.1 ∂physicalObservationLaw μ K)-
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K) ∧
    (∫ z in A, rawPotential y z.1 ∂physicalObservationLaw μ K)-
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K) ≤
      ∫ z in A, rawLocalPotential y (2*masterWidth c₁ r₀ s y) z.1 ∂physicalObservationLaw μ K := by
  let v : Space → ℝ := fun x => 1/‖x-y‖
  let l : Space → ℝ := (ball y (2*masterWidth c₁ r₀ s y)).indicator v
  have hv : Measurable v := by fun_prop
  have hl : Measurable l := hv.indicator measurableSet_ball
  have hli : Integrable (fun x : Configuration N => ∑ i, l (x i)) μ := by
    have heq : (fun x : Configuration N => ∑ i, l (x i)) =
        rawLocalPotential y (2*masterWidth c₁ r₀ s y) := by
      funext x
      exact (rawLocalPotential_eq_indicator y _ x).symm
    rw [heq]
    exact rawLocalPotential_integrable_of_raw y _ hi
  have hvr := (kernelPosteriorTest_integrable μ ell j hv hi).integrableOn (s := A)
  have hlr := (kernelPosteriorTest_integrable μ ell j hl hli).integrableOn (s := A)
  have hpr := (jointMasterPosterior_potential_integrable μ ell j y hi he hc hr hs hg hcg hgn hrad hgs).integrableOn (s := A)
  have hpoint := ae_restrict_of_ae (s := A) (jointMasterPosterior_potential_loss μ ell j y hi he
    hc hcL hr hs hs1 hg hcg hgn hrad hgs)
  have hn := integral_nonneg_of_ae (hpoint.mono fun _ h => h.1)
  have hb := integral_mono_ae (hvr.sub hpr) hlr (hpoint.mono fun _ h => h.2)
  simp only [Pi.sub_apply] at hb
  rw [integral_sub hvr hpr,kernelPosteriorTest_setIntegral μ ell j hv hi hA] at hn hb
  rw [kernelPosteriorTest_setIntegral μ ell j hl hli hA] at hb
  simpa only [rawPotential,rawLocalPotential_eq_indicator] using And.intro hn hb

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchTruncationLoss
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchDensityCap_scale {R : ℝ} (hR : 0 < R) :
    (tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic))^(3/2:ℝ) = tfPatchDensityCapConstant/R^6 := by
  have he : tfPatchCapConstant/R^4/((5/3:ℝ)*tfKinetic) =
      (tfPatchCapConstant/((5/3:ℝ)*tfKinetic))/R^4 := by ring
  rw [he,cap_reaction_scale (div_nonneg tfPatchCapConstant_pos.le (mul_nonneg (by norm_num) tfKinetic_pos.le)) hR]
  rfl

lemma local_coulomb_le_of_density_cap {f : TFSpace → ℝ} {q C : ℝ}
    (hq : 0 < q) (hf : MemLp f (5/3) (ballMeasure q))
    (hcap : ∀ᵐ x ∂ballMeasure q, ‖f x‖ ≤ C) :
    (∫ x in ball 0 q, ‖f x‖/‖x‖) ≤ 2*Real.pi*C*q^2 := by
  have hi : Integrable (fun x => ‖f x‖/‖x‖) (ballMeasure q) := by
    convert! (nuclear_memLp q).integrable_mul hf.norm using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  have hk : Integrable (fun x : TFSpace => ‖x‖⁻¹) (ballMeasure q) := by
    simpa only [one_div] using (nuclear_memLp q).integrable (Fact.out : (1 : ENNReal) ≤ 5/2)
  have hh : (∫ x, ‖f x‖/‖x‖ ∂ballMeasure q) ≤ ∫ x, C*‖x‖⁻¹ ∂ballMeasure q := by
    apply integral_mono_ae hi (hk.const_mul C)
    filter_upwards [hcap] with x hx
    exact (div_le_div_of_nonneg_right hx (norm_nonneg x)).trans_eq (by ring)
  apply hh.trans_eq
  rw [integral_const_mul]
  change C*(∫ x : TFSpace in ball 0 q, ‖x‖⁻¹) = _
  rw [integral_coulomb_ball hq]
  ring

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

theorem conditionalPatchMinimizer_truncation_loss {N M : ℕ} (ψ : FormVector (N+M))
    (t : Spins M) (u : Configuration M) (hu : SobolevVector (coreSlice ψ t u))
    (A : Set Space) (hcore : ∀ x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (y : Space) {R d r q : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (Z lam : ℝ) :
    let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
    |tfBallPotential R f 0-(∫ x, (1/max ‖x‖ q)*f x ∂ballMeasure R)| ≤
      2*Real.pi*tfPatchDensityCapConstant*q^2/R^6 := by
  let f := tfPatchMinimizer R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  have hqR' : q < R := by linarith
  have hmeasure : ballMeasure q ≤ ballMeasure R :=
    Measure.restrict_mono (ball_subset_ball hqR'.le) le_rfl
  have hcap := conditionalPatchMinimizer_density_cap ψ t u hu A hcore y hR hd hr hnuc hsep Z lam
  have hn := tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos (conditionalPatchField ψ t Z lam y R u)
  have hn' := ae_mono hmeasure hn
  have hc' := ae_mono hmeasure hcap
  have hb : ∀ᵐ x ∂ballMeasure q, ‖f x‖ ≤ tfPatchDensityCapConstant/R^6 := by
    filter_upwards [hn',hc',ae_restrict_mem measurableSet_ball] with x hx hxcap hxb
    rw [Real.norm_of_nonneg hx]
    have hnorm : ‖x‖ ≤ 3*R/4 := (mem_ball_zero_iff.mp hxb).le.trans hqR
    simpa only [tfPatchDensityCap_scale hR] using hxcap hnorm
  have he := truncated_potential_remainder hq hqR' (Lp.memLp f)
  rw [←tfBallPotential_at_zero] at he
  apply he.trans
  have hh := local_coulomb_le_of_density_cap hq ((Lp.memLp f).mono_measure hmeasure) hb
  exact hh.trans_eq (by ring)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_PatchLocalObservable
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma local_coulomb_pair_eq {R q : ℝ} (hqR : q ≤ R)
    (f : TFLp (ballMeasure R)) (hf : NonnegDensity f) :
    (∫ x, ((ball (0 : Space) q).indicator (fun z => 1/‖z‖) x)*f x ∂ballMeasure R) =
      ∫ x in ball 0 q, ‖f x‖/‖x‖ := by
  have hh : (fun x => ((ball (0 : Space) q).indicator (fun z => 1/‖z‖) x)*f x) =
      (ball (0 : Space) q).indicator (fun x => f x/‖x‖) := by
    funext x
    by_cases hx : x ∈ ball (0 : Space) q
    · simp only [indicator_of_mem hx]; ring
    · simp only [indicator_of_notMem hx,zero_mul]
  rw [hh,integral_indicator measurableSet_ball]
  change (∫ x, f x/‖x‖ ∂(volume.restrict (ball 0 R)).restrict (ball 0 q)) = _
  rw [Measure.restrict_restrict measurableSet_ball,inter_eq_left.mpr (ball_subset_ball hqR)]
  apply integral_congr_ae
  filter_upwards [ae_mono (Measure.restrict_mono (ball_subset_ball hqR) le_rfl) hf] with x hx
  rw [Real.norm_of_nonneg hx]

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis CoulombNeumann
attribute [local instance] OAI.CoulombAtom.instMeasurableSpacePatchLocalObservableTFLp
local instance instBorelSpacePatchLocalObservableTFLp (R : ℝ) :
    BorelSpace (TFLp (ballMeasure R)) := ⟨rfl⟩

lemma retainedPatchLocalPotential_nonneg {M : ℕ} (y : Space) (R q : ℝ)
    {b : ℝ} (hb : 0 < b) (S : Finset (Fin M)) (u : Configuration M) :
    0 ≤ ∫ x in ball 0 q, ‖retainedPatchLp hb S u y R x‖/‖x‖ :=
  integral_nonneg (fun _ => div_nonneg (norm_nonneg _) (norm_nonneg _))

lemma retainedPatchLocalPotential_le {M : ℕ} (y : Space) {R q : ℝ}
    (hq : 0 < q) (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Finset (Fin M)) (u : Configuration M) :
    (∫ x in ball 0 q, ‖retainedPatchLp hb S u y R x‖/‖x‖) ≤
      2*Real.pi*(M*b⁻¹^3)*q^2 := by
  have hmeasure : ballMeasure q ≤ ballMeasure R :=
    Measure.restrict_mono (ball_subset_ball hqR) le_rfl
  apply local_coulomb_le_of_density_cap hq
    ((Lp.memLp (retainedPatchLp hb S u y R)).mono_measure hmeasure)
  filter_upwards [ae_mono hmeasure (retainedPatchLp_nonneg hb S u y R),
    ae_mono hmeasure (retainedPatchLp_bound hb S u y R)] with x hx hxcap
  rw [Real.norm_of_nonneg hx]
  apply hxcap.trans
  have hcNat : S.card ≤ M := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have hc : (S.card : ℝ) ≤ M := by exact_mod_cast hcNat
  exact mul_le_mul_of_nonneg_right hc (by positivity)

lemma retainedPatchLocalPotential_measurable {M : ℕ} (y : Space) {R q : ℝ}
    (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    Measurable (fun u => ∫ x in ball 0 q, ‖retainedPatchLp hb (S u) u y R x‖/‖x‖) := by
  have hg := (nuclear_memLp R).indicator measurableSet_ball (s := ball (0 : Space) q)
  have hs := retainedPatchLp_measurable hb S id hS measurable_id y R
  have hm := (patch_test_continuous_of_memLp R hg).measurable.comp hs
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext u
  simpa only [one_div,Function.comp_apply,id_eq] using
    (local_coulomb_pair_eq hqR _ (retainedPatchLp_nonneg hb (S u) u y R)).symm

lemma weightedPatchLocalPotential_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) {R q : ℝ}
    (hq : 0 < q) (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    Integrable (weightedPatchLocalPotential ψ s y R q hb S) := by
  have hm := (retainedPatchLocalPotential_measurable y hqR hb S hS).aestronglyMeasurable (μ := volume)
  have hd : ∀ᵐ u, ‖∫ x in ball 0 q, ‖retainedPatchLp hb (S u) u y R x‖/‖x‖‖ ≤
      2*Real.pi*(M*b⁻¹^3)*q^2 := by
    filter_upwards [] with u
    rw [Real.norm_of_nonneg (retainedPatchLocalPotential_nonneg y R q hb _ u)]
    exact retainedPatchLocalPotential_le y hq hqR hb _ u
  exact ((hψ.coreSlice_mass_integrable s).bdd_mul hm hd).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_ThomasFermi_PatchFullPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal

namespace CoulombAnalysis
open CoulombAtom

lemma tfBallPotential_sub_at_zero (R : ℝ) (f g : TFLp (ballMeasure R)) :
    tfBallPotential R f 0-tfBallPotential R g 0 =
      ∫ x, (1/‖x‖)*(f-g) x ∂ballMeasure R := by
  rw [tfBallPotential_at_zero,tfBallPotential_at_zero]
  have hf : Integrable (fun x => f x/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul (Lp.memLp f) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  have hg : Integrable (fun x => g x/‖x‖) (ballMeasure R) := by
    convert! (nuclear_memLp R).integrable_mul (Lp.memLp g) using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact div_eq_inv_mul _ _
  rw [←integral_sub hf hg]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub f g] with x hx
  simp only [hx,Pi.sub_apply]
  ring

lemma tfBallPotential_truncated_triangle {R q : ℝ} (hq : 0 < q) (hqR : q < R)
    (f g : TFLp (ballMeasure R)) {C : ℝ}
    (hg : |tfBallPotential R g 0-(∫ x, (1/max ‖x‖ q)*g x ∂ballMeasure R)| ≤ C) :
    |tfBallPotential R f 0-tfBallPotential R g 0| ≤
      |∫ x, (1/max ‖x‖ q)*(f-g) x ∂ballMeasure R|+
      (∫ x in ball 0 q, ‖f x‖/‖x‖)+C := by
  let A := ∫ x, (1/max ‖x‖ q)*f x ∂ballMeasure R
  let B := ∫ x, (1/max ‖x‖ q)*g x ∂ballMeasure R
  have hp : (∫ x, (1/max ‖x‖ q)*(f-g) x ∂ballMeasure R) = A-B := by
    dsimp only [A,B]
    have hf : Integrable (fun x => (1/max ‖x‖ q)*f x) (ballMeasure R) :=
      (truncated_kernel_memLp R hq).integrable_mul (Lp.memLp f)
    have hg : Integrable (fun x => (1/max ‖x‖ q)*g x) (ballMeasure R) :=
      (truncated_kernel_memLp R hq).integrable_mul (Lp.memLp g)
    rw [←integral_sub hf hg]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with x hx
    simp only [hx,Pi.sub_apply,mul_sub]
  have hf := truncated_potential_remainder hq hqR (Lp.memLp f)
  rw [←tfBallPotential_at_zero] at hf
  rw [hp]
  have he : tfBallPotential R f 0-tfBallPotential R g 0 =
      (A-B)+(tfBallPotential R f 0-A)-(tfBallPotential R g 0-B) := by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans
    (add_le_add (add_le_add le_rfl hf) hg))

end CoulombAnalysis

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_ExpectedFullPotential
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma weightedPatchFull_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ s u) x)
    (y : Space) {R d r q b : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (Z lam : ℝ) :
    ∀ᵐ u, weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖) u ≤
      weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/max ‖x‖ q) u+
      weightedPatchLocalPotential ψ s y R q hb S u+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)*formMass (coreSlice ψ s u) := by
  have hqR' : q < R := by linarith
  filter_upwards [hψ.ae_coreSlice s] with u hu
  have he := tfBallPotential_truncated_triangle hq hqR' (retainedPatchLp hb (S u) u y R) _
    (conditionalPatchMinimizer_truncation_loss ψ s u hu A (hcore u) y hR hd hr hnuc hsep hq hqR Z lam)
  rw [tfBallPotential_sub_at_zero] at he
  have hw := mul_le_mul_of_nonneg_left he (formMass_nonneg (coreSlice ψ s u))
  simpa only [weightedPatchTestAbs,weightedPatchLocalPotential,mul_add,mul_comm
    (formMass (coreSlice ψ s u)) (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)] using hw

lemma weightedPatchFull_integrable_and_bound {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ s u) x)
    (y : Space) {R d r q b : ℝ} (hR : 0 < R) (hd : 0 < d) (hr : 0 < r)
    (hnuc : ∀ z ∈ closedBall y R, r ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, d ≤ ‖a-z‖)
    (hq : 0 < q) (hqR : q ≤ 3*R/4) (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u})
    (Z lam : ℝ) (hi : Integrable (weightedPatchGap ψ s Z lam y R hb S)) :
    Integrable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖)) ∧
    (∫ u, weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖) u) ≤
      (∫ u, weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/max ‖x‖ q) u)+
      (∫ u, weightedPatchLocalPotential ψ s y R q hb S u)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)*(∫ u, formMass (coreSlice ψ s u)) := by
  have hqR' : q < R := by linarith
  have ht := weightedPatchTruncatedAbs_integrable hψ s Z lam y hq hqR' hb S hS hi
  have hl := weightedPatchLocalPotential_integrable hψ s y hq hqR'.le hb S hS
  have hc := (hψ.coreSlice_mass_integrable s).const_mul (2*Real.pi*tfPatchDensityCapConstant*q^2/R^6)
  have hbnd := weightedPatchFull_le hψ s A hcore y hR hd hr hnuc hsep hq hqR hb S Z lam
  have hker : MemLp (fun x : TFSpace => 1/‖x‖) (5/2) (ballMeasure R) := by
    simpa only [one_div] using nuclear_memLp R
  have hm : AEStronglyMeasurable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖)) := by
    have he := (hψ.coreSlice_mass_integrable s).aestronglyMeasurable.mul
      (patchTestError_aestronglyMeasurable hψ s Z lam y R hb S hS hker).norm
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hfull : Integrable (weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖)) := by
    apply ((ht.add hl).add hc).mono' hm
    filter_upwards [hbnd] with u hu
    have hn : 0 ≤ weightedPatchTestAbs ψ s Z lam y R hb S (fun x => 1/‖x‖) u :=
      mul_nonneg (formMass_nonneg _) (abs_nonneg _)
    rw [Real.norm_of_nonneg hn]
    exact hu
  refine ⟨hfull,?_⟩
  have hh := integral_mono_ae hfull ((ht.add hl).add hc) hbnd
  have he := integral_add (ht.add hl) hc
  have he' := integral_add ht hl
  simp only [Pi.add_apply] at he he' hh
  rw [he, he', integral_const_mul] at hh
  exact hh

theorem radial_full_absolute_control {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestAbs (χ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention N y t b c s) u))+
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchLocalPotential (χ c) s y (t-4*b) q hb (radialPatchRetention N y t b c s) u)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ := by
  dsimp only
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  have hR : 0 < t-4*b := by linarith
  have hqR' : q < t-4*b := by linarith
  have hχ (c : Fin N → Fin 2) : SobolevVector (χ c) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hc (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c)) (i : Fin (cutCoreNumber c))
      (hi : v i ∉ radialPatchCore y t) : FormZeroAt (coreSlice (χ c) s u) v := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
      (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
      (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hbranch (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    (weightedPatchFull_integrable_and_bound (hχ c) s (radialPatchCore y t) (hc c s) y hR hb hb
      (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) hq hqR hb _
      (radialPatchRetention_measurable N y t b c s) Z lam
      (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)).2
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbranch c s))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hsum
  have hmass : (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      formMass (coreSlice (χ c) s u)) = formMass ψ := by
    simp_rw [SobolevVector.integral_coreSlice_mass (hχ _)]
    exact orderedCutForm_mass_sum p hp hψ.sobolevVector
  rw [hmass] at hsum
  exact hsum.trans (add_le_add (add_le_add
    (radial_truncated_absolute_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR') le_rfl) le_rfl)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_FullPotentialComparison
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma retainedPatchLocalPotential_raw_le_ae {M : ℕ} (y : Space) {R q : ℝ}
    (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) :
    ∀ᵐ u, (∫ z in ball 0 q, ‖retainedPatchLp hb (S u) u y R z‖/‖z‖) ≤
      rawLocalPotential y (q+Real.sqrt 3*b) u := by
  classical
  have he : ∀ᵐ u : Configuration M, ∀ i, u i ≠ y := by
    exact (ae_all_iff.mpr fun i => Measure.ae_eval_ne (fun _ : Fin M => (volume : Measure Space)) i y)
  filter_upwards [he] with u hu
  apply (retainedPatchLp_local_potential_le hb hqR (S u) u y (fun i _ => hu i)).trans
  have heq (i : Fin M) : (ball y (q+Real.sqrt 3*b)).indicator (fun z => 1/‖y-z‖) (u i) =
      if ‖u i-y‖ < q+Real.sqrt 3*b then 1/‖u i-y‖ else 0 := by
    simp only [indicator_apply,mem_ball,dist_eq_norm,norm_sub_rev]
  simp_rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by
    split_ifs <;> positivity)

lemma weightedPatchLocalPotential_raw_integral_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (s : Spins M) (y : Space) {R q : ℝ}
    (hq : 0 < q) (hqR : q ≤ R) {b : ℝ} (hb : 0 < b)
    (S : Configuration M → Finset (Fin M)) (hS : ∀ i, MeasurableSet {u | i ∈ S u}) :
    (∫ u, weightedPatchLocalPotential ψ s y R q hb S u) ≤
      ∫ u, rawLocalPotential y (q+Real.sqrt 3*b) u*formMass (coreSlice ψ s u) := by
  apply integral_mono_ae (weightedPatchLocalPotential_integrable hψ s y hq hqR hb S hS)
    (rawLocalPotential_core_integrable hψ s y _)
  filter_upwards [retainedPatchLocalPotential_raw_le_ae y hqR hb S] with u hu
  simpa only [weightedPatchLocalPotential,mul_comm (formMass (coreSlice ψ s u))] using
    mul_le_mul_of_nonneg_left hu (formMass_nonneg (coreSlice ψ s u))

theorem radial_full_potential_comparison {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      weightedPatchTestAbs (χ c) s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u) ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention N y t b c s) u))+
      (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ := by
  dsimp only
  have hqR' : q ≤ t-4*b := by linarith
  apply (radial_full_absolute_control hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR).trans
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  apply le_trans (Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ =>
      weightedPatchLocalPotential_raw_integral_le
        (orderedCutForm_sobolev _ _ hψ.sobolevVector c) s y hq hqR' hb _
        (radialPatchRetention_measurable N y t b c s))))
  exact fresh_cut_raw_local_control _ _ hψ.sobolevVector y _

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Variational_PatchCenterIntegrable
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology

namespace CoulombAnalysis
open CoulombAtom

lemma tfPatchMinimizer_potential_zero_le {R T F : ℝ} (hR : 0 < R)
    (hT : 0 < T) (Φ : TFField R) (hΦ : ∀ᵐ x ∂ballMeasure R, Φ x ≤ F) :
    tfBallPotential R (tfPatchMinimizer R T hT Φ) 0 ≤
      2*Real.pi*((max F 0/((5/3:ℝ)*T))^(3/2:ℝ))*R^2 := by
  have hn := tfPatchMinimizer_nonneg R T hT Φ
  have hb := tfPatchMinimizer_ae_bound hT Φ hΦ
  have he := local_coulomb_le_of_density_cap hR (Lp.memLp (tfPatchMinimizer R T hT Φ))
    (hb.and hn |>.mono fun x hx => by simpa only [Real.norm_of_nonneg hx.2] using hx.1)
  apply le_trans _ he
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp only [zero_sub,norm_neg,Real.norm_of_nonneg hx]

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis

lemma conditionalPatchCenter_abs_le {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R b : ℝ} (hR : 0 < R)
    (Z lam : ℝ) (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    ∀ᵐ u, |conditionalPatchCenter ψ t Z lam y R u| ≤
      finiteCorePatchBound N Z lam b +
        2*Real.pi*((finiteCorePatchBound N Z lam b/((5/3:ℝ)*tfKinetic))^(3/2:ℝ))*R^2 := by
  have hy : y ∈ closedBall y R := mem_closedBall_self hR.le
  filter_upwards [hψ.ae_coreSlice t,
    conditionalPatchField_upper hψ t y R Z lam hb A hcore hnuc hsep] with u hu hf
  have h1 := normalizedCoreField_abs_le hu A (hcore u) hb y
    (fun a ha => hsep a ha y hy) hb (hnuc y hy) Z lam
  have h2 := tfPatchMinimizer_potential_zero_le hR tfKinetic_pos _ hf
  rw [max_eq_left (finiteCorePatchBound_nonneg N Z lam hb)] at h2
  have hn := tfBallPotential_nonneg (tfPatchMinimizer_nonneg R tfKinetic tfKinetic_pos
    (conditionalPatchField ψ t Z lam y R u)) 0
  exact (abs_sub _ _).trans (add_le_add h1 (by simpa only [abs_of_nonneg hn] using h2))

lemma weightedPatchCenter_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {R b : ℝ} (hR : 0 < R)
    (Z lam : ℝ) (hb : 0 < b) (A : Set Space)
    (hcore : ∀ u x i, x i ∉ A → FormZeroAt (coreSlice ψ t u) x)
    (hnuc : ∀ z ∈ closedBall y R, b ≤ ‖z‖)
    (hsep : ∀ a ∈ A, ∀ z ∈ closedBall y R, b ≤ ‖a-z‖) :
    Integrable (weightedPatchCenter ψ t Z lam y R) := by
  have hbnd := conditionalPatchCenter_abs_le hψ t y hR Z lam hb A hcore hnuc hsep
  have hm := (conditionalPatchCenter_aemeasurable hψ t Z lam y R).aestronglyMeasurable
  exact ((hψ.coreSlice_mass_integrable t).bdd_mul hm
    (hbnd.mono fun u hu => by simpa only [Real.norm_eq_abs] using hu)).congr
    (Eventually.of_forall fun _ => mul_comm _ _)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_RadialCenterRawComparison
attribute [-instance] _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.physicalObservationLaw_finite _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAnalysis

lemma center_raw_error_of_loss {m a p f r d l : ℝ}
    (hm : 0 ≤ m) (hd : 0 ≤ d) (hl : 0 ≤ r-f) (hb : r-f ≤ l) :
    |(a-(r+d))*m-m*(a-p)| ≤ m*|f-p|+l*m+d*m := by
  have he : (a-(r+d))*m-m*(a-p) = -(m*(f-p))-(r-f)*m-d*m := by ring
  rw [he]
  apply (abs_sub _ _).trans
  apply (add_le_add (abs_sub _ _) le_rfl).trans
  rw [abs_neg,abs_mul,abs_of_nonneg hm,abs_of_nonneg (mul_nonneg hl hm),
    abs_of_nonneg (mul_nonneg hd hm)]
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb hm)) le_rfl

end CoulombAnalysis
namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma radial_branch_center_raw_bound {N : ℕ} (y : Space) {t b : ℝ} (hb : 0 < b)
    (htb : 7*b < t) (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
    {ψ : FormVector (cutCoreNumber c+cutOutNumber c)} (hψ : SobolevVector ψ) (Z lam : ℝ)
    (hc : Integrable (weightedPatchCenter ψ s Z lam y (t-4*b)))
    (hi : Integrable (weightedPatchTestAbs ψ s Z lam y (t-4*b) hb
      (radialPatchRetention N y t b c s) (fun x => 1/‖x‖))) :
    |(∫ u, (normalizedCoreField Z lam (coreSlice ψ s u) y-rawPotential y u)*
        formMass (coreSlice ψ s u))-(∫ u, weightedPatchCenter ψ s Z lam y (t-4*b) u)| ≤
      (∫ u, weightedPatchTestAbs ψ s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u)+
      (∫ u, rawLocalPotential y (Real.sqrt 3*b) u*formMass (coreSlice ψ s u))+
      (∫ u, outerDeletedPotential y t b u*formMass (coreSlice ψ s u)) := by
  have hf : Integrable (fun u => (normalizedCoreField Z lam (coreSlice ψ s u) y-rawPotential y u)*
      formMass (coreSlice ψ s u)) := by
    convert (normalizedCoreField_weighted_integrable hψ s Z lam y).sub
      (rawPotential_coreSlice_integrable hψ s y) using 1
    all_goals try with_reducible_and_instances rfl
    funext u
    exact sub_mul _ _ _
  have hl := rawLocalPotential_core_integrable hψ s y (Real.sqrt 3*b)
  have hd := weighted_outerDeletedPotential_integrable hψ s y htb
  have he : ∀ᵐ u, |(normalizedCoreField Z lam (coreSlice ψ s u) y-rawPotential y u)*
      formMass (coreSlice ψ s u)-weightedPatchCenter ψ s Z lam y (t-4*b) u| ≤
      weightedPatchTestAbs ψ s Z lam y (t-4*b) hb
        (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u+
      rawLocalPotential y (Real.sqrt 3*b) u*formMass (coreSlice ψ s u)+
      outerDeletedPotential y t b u*formMass (coreSlice ψ s u) := by
    filter_upwards [radial_fine_potential_loss_ae y (t := t) hb c s] with u hu
    simp only [weightedPatchCenter,conditionalPatchCenter,weightedPatchTestAbs,
      ←tfBallPotential_sub_at_zero,rawPotential_retained_deleted y t b u]
    exact center_raw_error_of_loss (formMass_nonneg _) (outerDeletedPotential_nonneg y t b u) hu.1 hu.2
  rw [←integral_sub hf hc]
  apply (abs_integral_le_integral_abs).trans
  have hh := integral_mono_ae (hf.sub hc).abs ((hi.add hl).add hd) he
  simp only [Pi.sub_apply,Pi.add_apply] at hh
  have hi1 := integral_add (hi.add hl) hd
  have hi2 := integral_add hi hl
  simp only [Pi.add_apply] at hi1 hi2
  rw [hi1,hi2] at hh
  exact hh

theorem radial_center_raw_comparison {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchCenter (χ c) s Z lam y (t-4*b) u)| ≤
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchTestAbs (χ c) s Z lam y (t-4*b) hb
          (radialPatchRetention N y t b c s) (fun x => 1/‖x‖) u)+
      (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          (outerDeletedCount y t b u)^2*formMass (coreSlice (χ c) s u))/(t-7*b) := by
  dsimp only
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  have hR : 0 < t-4*b := by linarith
  have hχ (c : Fin N → Fin 2) : SobolevVector (χ c) := orderedCutForm_sobolev p hp hψ.sobolevVector c
  have hc (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c)) (i : Fin (cutCoreNumber c))
      (hi : v i ∉ radialPatchCore y t) : FormZeroAt (coreSlice (χ c) s u) v := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
      (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
      (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hbranch (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    radial_branch_center_raw_bound y hb htb c s (hχ c) Z lam
      (weightedPatchCenter_integrable (hχ c) s y hR Z lam hb (radialPatchCore y t) (hc c s)
        (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb))
      (weightedPatchFull_integrable_and_bound (hχ c) s (radialPatchCore y t) (hc c s) y
        hR hb hb (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb) hq hqR hb _
        (radialPatchRetention_measurable N y t b c s) Z lam
        (radial_weightedPatchGap_integrable hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs c s)).1
  rw [←fresh_cut_field_tower p hp hψ.sobolevVector Z lam y,←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    (Finset.abs_sum_le_sum_abs (fun s : Spins (cutOutNumber c) =>
      (∫ u, (normalizedCoreField Z lam (coreSlice (χ c) s u) y-rawPotential y u)*formMass (coreSlice (χ c) s u))-
      (∫ u, weightedPatchCenter (χ c) s Z lam y (t-4*b) u)) Finset.univ).trans
      (Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbranch c s)))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib] at hh
  apply hh.trans
  exact add_le_add
    (add_le_add le_rfl (fresh_cut_raw_local_control p hp hψ.sobolevVector y (Real.sqrt 3*b)))
    (fresh_cut_deleted_potential_bound p hp hψ.sobolevVector y htb)

theorem radial_center_field_quantitative {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (htb : 7*b < t) (hy : t ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z : Space, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
    |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchCenter (χ c) s Z lam y (t-4*b) u)| ≤
      Real.sqrt (formMass ψ)*Real.sqrt ((2/q)*
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          weightedPatchGap (χ c) s Z lam y (t-4*b) hb (radialPatchRetention N y t b c s) u))+
      (∫ x, rawLocalPotential y (q+Real.sqrt 3*b) x ∂formRawLaw ψ)+
      (2*Real.pi*tfPatchDensityCapConstant*q^2/(t-4*b)^6)*formMass ψ+
      (∫ x, rawLocalPotential y (Real.sqrt 3*b) x ∂formRawLaw ψ)+
      Real.sqrt (formMass ψ)*Real.sqrt
        (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          (outerDeletedCount y t b u)^2*formMass (coreSlice (χ c) s u))/(t-7*b) := by
  apply (radial_center_raw_comparison hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR).trans
  exact add_le_add (add_le_add
    (radial_full_potential_comparison hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR)
    le_rfl) le_rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_NormalizedMasterEvent
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
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma normalized_event_integral {N K : ℕ} (μ ν : Measure (Configuration N))
    (A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)))
    {p : ℝ} (hp : 0 < p)
    (hlaw : ν = (ENNReal.ofReal p)⁻¹ • Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A))
    {f : Configuration N → ℝ} (hf : Measurable f) :
    (∫ x, f x ∂ν) = p⁻¹*(∫ z in A, f z.1 ∂physicalObservationLaw μ K) := by
  rw [hlaw,integral_smul_measure,integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal hp.le,smul_eq_mul]

theorem normalized_master_event_loss {N K : ℕ} (μ ν : Measure (Configuration N)) [IsFiniteMeasure μ]
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) {p : ℝ} (hp : 0 < p)
    (hlaw : ν = (ENNReal.ofReal p)⁻¹ • Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A)) :
    0 ≤ (∫ x, rawPotential y x ∂ν)-p⁻¹*
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K) ∧
    (∫ x, rawPotential y x ∂ν)-p⁻¹*
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K) ≤
      ∫ x, rawLocalPotential y (2*masterWidth c₁ r₀ s y) x ∂ν := by
  have hh := master_potential_event_loss μ ell j y hi he hc hcL hr hs hs1 hg hcg hgn hrad hgs hA
  rw [normalized_event_integral μ ν A hp hlaw (rawPotential_measurable y),
    normalized_event_integral μ ν A hp hlaw (rawLocalPotential_measurable N y _),←mul_sub]
  exact ⟨mul_nonneg (inv_nonneg.mpr hp.le) hh.1,
    mul_le_mul_of_nonneg_left hh.2 (inv_nonneg.mpr hp.le)⟩

theorem original_master_radial_center_comparison {N K : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) {p : ℝ} (hp : 0 < p)
    (hlaw : formRawLaw ψ = (ENNReal.ofReal p)⁻¹ •
      Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A))
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (htb : 7*b < t) (hy : t ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {q : ℝ} (hq : 0 < q) (hqR : q ≤ 3*(t-4*b)/4) :
    |(Z/‖y‖-lam)*formMass ψ-p⁻¹*
      (∫ z in A, tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
        ∂physicalObservationLaw μ K)-expectedRadialPatchCenter ψ y ht hb Z lam| ≤
      radialPotentialError ψ y ht hb Z lam q+
      (∫ x, rawLocalPotential y (2*masterWidth c₁ r₀ s y) x ∂formRawLaw ψ) := by
  have hraw := radial_center_field_quantitative hψ y ht hb htb hy hZ hlam hg hcg hgn hrad hgs hq hqR
  change |(Z/‖y‖-lam)*formMass ψ-(∫ x, rawPotential y x ∂formRawLaw ψ)-
    expectedRadialPatchCenter ψ y ht hb Z lam| ≤ radialPotentialError ψ y ht hb Z lam q at hraw
  have hm := normalized_master_event_loss μ (formRawLaw ψ) ell j y hi he hc hcL hr hs hs1
    hg hcg hgn hrad hgs hA hp hlaw
  have hid (a b c d : ℝ) : a-b-c = (a-d-c)+(d-b) := by ring
  rw [hid _ _ _ (∫ x, rawPotential y x ∂formRawLaw ψ)]
  apply (abs_add_le _ _).trans
  rw [abs_of_nonneg hm.1]
  exact add_le_add hraw hm.2

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FormDomain_ActualMasterCenterComparison
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

lemma graphFormVector_sobolev {N : ℕ} (F : fermionGraph N) :
    SobolevFermion (graphFormVector F) := by
  refine ⟨fun s => Lp.memLp _, fun s i a => Lp.memLp _, ?_, ?_⟩
  · intro s i a
    exact (mem_weakGraph _ _).mp (F.val s).property (i,a)
  · intro π s
    exact (mem_fermionSpace_ae _).mp (fermionGraphValue N F).property π s

lemma formRawLaw_graph {N : ℕ} (F : fermionGraph N) :
    formRawLaw (graphFormVector F) = graphRawLaw F := rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_FieldAnalysis_LocalFieldScalarBoundBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom

lemma sharpFreshFieldConstant_one_le : 1 ≤ sharpFreshFieldConstant := by
  have hC := actualCellMomentConstant_one_le
  have hI := localizationIMSConstant_nonneg
  have hT := thinFieldUniversalConstant_pos
  unfold sharpFreshFieldConstant
  have h : 0 ≤ thinFieldUniversalConstant*(6+actualCellMomentConstant+
      localizationIMSConstant*actualCellMomentConstant) := by positivity
  linarith only [h]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_BarrierEventSymmetryBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.coherentIndex_countable _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.orbitalHilbert_secondCountable _root_.OAI.CoulombAtom.originalRawKernel_markov _root_.OAI.CoulombAtom.rotationMeasureHaar _root_.OAI.CoulombAtom.rotationMeasureLeftInvariant _root_.OAI.CoulombAtom.rotationMeasureProbability _root_.OAI.CoulombAtom.spatialOperatorContinuousStar _root_.OAI.CoulombAtom.spatialRotationBorel _root_.OAI.CoulombAtom.spatialRotationCompact _root_.OAI.CoulombAtom.spatialRotationMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set

namespace CoulombAtom
open CoulombObservation

lemma observationInformation_eq_arrayComap {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ) :
    observationInformation (N := N) ell j =
      (arrayObservationInformation N K j).comap (physicalObservationArray ell) := by
  unfold observationInformation arrayObservationInformation
  rw [MeasurableSpace.comap_iSup]
  congr 1
  funext k
  split_ifs
  · rw [MeasurableSpace.comap_comp]
    rfl
  · exact MeasurableSpace.comap_bot.symm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_BarrierInitialEventBarrier
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

lemma threshold_event_mean_ge {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hi : Integrable f μ) {t : ℝ} {A : Set Ω} (hA : MeasurableSet A)
    (hAB : ∀ z ∈ A, t ≤ f z) (hp : 0 < (μ A).toReal) :
    t ≤ ((μ A).toReal)⁻¹*(∫ z in A, f z ∂μ) := by
  have he : (μ A).toReal*t ≤ ∫ z in A, f z ∂μ := by
    calc
      _ = ∫ z in A, t ∂μ := by simp [Measure.real,smul_eq_mul]
      _ ≤ _ := setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn hA hAB
  have hm := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hp.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hm

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_LocalOrdinaryBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators

lemma sharpFreshKineticConstant_one_le : 1 ≤ sharpFreshKineticConstant := by
  have := localizationIMSConstant_nonneg
  have := actualCellMomentConstant_one_le
  have := sharpFreshFieldConstant_one_le
  have hh : 0 ≤ localizationIMSConstant*actualCellMomentConstant+
      sharpFreshFieldConstant*actualCellMomentConstant := by positivity
  unfold sharpFreshKineticConstant
  linarith only [hh]

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpLocalPotentialBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpLocalPotential_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

lemma sharpOrdinaryDensityConstant_nonneg : 0 ≤ sharpOrdinaryDensityConstant := by
  have hc := le_trans zero_le_one actualCellMomentConstant_one_le
  have hk := le_trans zero_le_one sharpFreshKineticConstant_one_le
  unfold sharpOrdinaryDensityConstant
  positivity

end Work_SharpLocalPotential_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_ExpectedRadialCapBarrier
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
section Work_ExpectedRadialCap_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis

theorem expectedRadialPatchCenter_le {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hbt : 4*b < t) (hy : t ≤ ‖y‖) (Z lam : ℝ) :
    expectedRadialPatchCenter ψ y ht hb Z lam ≤
      (tfPatchCapConstant/(t-4*b)^4)*formMass ψ := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  let χ := fun c : Fin N → Fin 2 => orderedCutForm p hp ψ c
  have hR : 0 < t-4*b := by linarith
  have hχ (c : Fin N → Fin 2) : SobolevVector (χ c) := orderedCutForm_sobolev p hp hψ c
  have hcore (c : Fin N → Fin 2) (s : Spins (cutOutNumber c))
      (u : Configuration (cutOutNumber c)) (v : Configuration (cutCoreNumber c))
      (i : Fin (cutCoreNumber c)) (hi : v i ∉ radialPatchCore y t) :
      FormZeroAt (coreSlice (χ c) s u) v := by
    apply FormZeroAt.coreSlice
    exact orderedCutForm_core_hole _ _ ψ c (radialPatchCore y t)ᶜ
      (coreFirstRadialCut_core_zero y ht hb) (coreFirstRadialCut_core_deriv_zero y ht hb)
      (joinLists v u) i (by simpa only [joinLists_left,mem_compl_iff] using hi)
  have hi (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :=
    weightedPatchCenter_integrable (hχ c) s y hR Z lam hb (radialPatchCore y t)
      (hcore c s) (radialPatch_nuclear_distance hb hy) (radialPatch_core_distance y hb)
  have hbnd (c : Fin N → Fin 2) (s : Spins (cutOutNumber c)) :
      (∫ u, weightedPatchCenter (χ c) s Z lam y (t-4*b) u) ≤
        (tfPatchCapConstant/(t-4*b)^4)*(∫ u, formMass (coreSlice (χ c) s u)) := by
    rw [←integral_const_mul]
    apply integral_mono_ae (hi c s) ((hχ c).coreSlice_mass_integrable s |>.const_mul _)
    filter_upwards [radialPatchMinimizer_nonradial_cap hψ y ht hb hbt hy Z lam c s] with u hu
    have h := hu 0 (by simpa only [norm_zero] using (by positivity : 0 ≤ 3*(t-4*b)/4))
    simp only [add_zero] at h
    have hh := mul_le_mul_of_nonneg_left h (formMass_nonneg (coreSlice (χ c) s u))
    simpa only [weightedPatchCenter,conditionalPatchCenter,mul_comm,χ,p,hp] using hh
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun c _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun s _ => hbnd c s))
  simp_rw [←Finset.mul_sum,(hχ _).integral_coreSlice_mass] at hh
  rw [orderedCutForm_mass_sum p hp hψ] at hh
  exact hh

end Work_ExpectedRadialCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_SharpBudgetMonotoneBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

lemma sharpPatchRemainder_mono {a b m n : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (hmn : m ≤ n) : sharpPatchRemainder a b m ≤ sharpPatchRemainder a b n := by
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  have hF : 0 ≤ sharpFreshFieldConstant := le_trans zero_le_one sharpFreshFieldConstant_one_le
  have hn : 0 ≤ n := hm.trans hmn
  unfold sharpPatchRemainder
  gcongr

lemma sharpLocalPotentialBudget_mono {a m n u v : ℝ} (ha : 0 < a)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hu : 0 ≤ u) (huv : u ≤ v) :
    sharpLocalPotentialBudget a m u ≤ sharpLocalPotentialBudget a n v := by
  have hC : 0 ≤ sharpOrdinaryDensityConstant := sharpOrdinaryDensityConstant_nonneg
  unfold sharpLocalPotentialBudget
  gcongr

lemma sharpPotentialRemainder_mono {a b m n D E q : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 ≤ m) (hmn : m ≤ n) (hDE : D ≤ E) (hq : 0 < q) :
    sharpPotentialRemainder a b m D q ≤ sharpPotentialRemainder a b n E q := by
  have hC : 0 ≤ actualCellMomentConstant := le_trans zero_le_one actualCellMomentConstant_one_le
  unfold sharpPotentialRemainder
  apply add_le_add
  · apply add_le_add
    · apply add_le_add
      · apply add_le_add
        · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
            (add_le_add hDE (sharpPatchRemainder_mono ha hb hm hmn)) (by positivity))
        · exact sharpLocalPotentialBudget_mono ha hm hmn (by positivity) le_rfl
      · exact le_rfl
    · exact sharpLocalPotentialBudget_mono ha hm hmn (by positivity) le_rfl
  · gcongr

lemma sharp_combined_error_mono {y : Space} (hy : y ≠ 0) {b q D E u : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hDE : D ≤ E) (hu : 0 ≤ u) :
    sharpPotentialRemainder (localCellRadius y) b (localOffsetMass D y) D q+
      sharpLocalPotentialBudget (localCellRadius y) (localOffsetMass D y) u ≤
    sharpPotentialRemainder (localCellRadius y) b (localOffsetMass E y) E q+
      sharpLocalPotentialBudget (localCellRadius y) (localOffsetMass E y) u := by
  have hm := localOffsetMass_mono hDE y
  have hn : 0 ≤ localOffsetMass D y := le_trans zero_le_one (localOffsetMass_one_le D y)
  exact add_le_add (sharpPotentialRemainder_mono (localCellRadius_pos hy) hb hn hm hDE hq)
    (sharpLocalPotentialBudget_mono (localCellRadius_pos hy) hn hm hu le_rfl)

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_ActualPosteriorCapBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma jointMasterPosterior_potential_measurable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hr : 0 < r₀) (hs : 0 < s)
    {g : Space → ℝ} (hg : Continuous g) :
    Measurable (fun z : OriginalDatum N K ell j =>
      tfPotential (jointMasterPosterior μ ell j c₁ r₀ s g z) y) := by
  have hm : Measurable (fun p : OriginalDatum N K ell j × Space =>
      jointMasterPosterior μ ell j c₁ r₀ s g p.1 p.2 / ‖y-p.2‖) :=
    (jointMasterPosterior_measurable μ ell j hc hr hs hg).div (by fun_prop)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma normalized_setIntegral_const_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : Set Ω) {f : Ω → ℝ}
    (hi : Integrable f μ) (hp : 0 < (μ A).toReal) (c : ℝ) :
    ((μ A).toReal)⁻¹*(∫ x in A, c-f x ∂μ) =
      c-((μ A).toReal)⁻¹*(∫ x in A, f x ∂μ) := by
  rw [integral_sub (integrable_const c) hi.integrableOn,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_sub,←mul_assoc,inv_mul_cancel₀ hp.ne',one_mul]

lemma dyadicUniformEventBudget_mono {r p₀ p δ : ℝ}
    (hr : 0 < r) (h₀ : 0 < p₀) (hp : p₀ ≤ p) (hp1 : p ≤ 1) :
    observationFisherConstant*r^(-2.02:ℝ)*(Real.log (Real.exp 1/p))^5+δ ≤
      dyadicUniformEventBudget r p₀ δ := by
  have hp' : 0 < p := h₀.trans_le hp
  have hlog : 0 ≤ Real.log (Real.exp 1/p) := by
    rw [eventLog_eq hp']
    linarith [Real.log_nonpos hp'.le hp1]
  have hh : Real.log (Real.exp 1/p) ≤ Real.log (Real.exp 1/p₀) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left (Real.exp_pos 1).le h₀ hp
  unfold dyadicUniformEventBudget
  exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog hh 5)
    (mul_nonneg observationFisherConstant_pos.le (Real.rpow_nonneg hr.le _))) le_rfl

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Localization_TailObservationEventBarrier
attribute [-instance] _root_.OAI.CoulombAnalysis.tfConjugate _root_.OAI.CoulombAnalysis.tfDualFact _root_.OAI.CoulombAnalysis.tfLpFact _root_.OAI.CoulombAtom.cosetWedgeFintype _root_.OAI.CoulombAtom.graphRawLaw_finite _root_.OAI.CoulombAtom.originalRawKernel_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set

namespace CoulombAtom
open CoulombObservation

lemma observation_event_tail_representation {N K : ℕ} (ell : Fin K → ℝ) (j : ℕ)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) :
    ∃ B : Set (Fin K × (Fin N × Fin 3) → ℝ),
      MeasurableSet[arrayObservationInformation N K j] B ∧ physicalObservationEvent ell B = A := by
  rw [observationInformation_eq_arrayComap] at hA
  exact MeasurableSpace.measurableSet_comap.mp hA

end CoulombAtom

open MeasureTheory Set Finset
open scoped BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_Ionization_SharpEventLawJointComparisonCell
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CoulombAtom

section
open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis CoulombObservation

theorem sharp_eventLaw_joint_comparison_of_cell {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N K : ℕ} (F G : fermionGraph N) (hG : ‖fermionGraphValue N G‖^2 = 1)
    (ell : Fin K → ℝ) (j : ℕ) {A : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hinfo : MeasurableSet[observationInformation ell j] (physicalObservationEvent ell A))
    (hp : 0 < physicalObservationProbability F ell A)
    (hlaw : graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
      Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
        (physicalObservationEvent ell A)))
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*
      localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y) :
    ∃ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ ht : 0 ≤ t,
      radialPatchGapMean (graphFormVector G) y ht hb Z lam ≤
        corePriceExcess Z lam (graphFormVector G)+sharpPatchRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y) ∧
      |Z/‖y‖-lam-(physicalObservationProbability F ell A)⁻¹*
        (∫ z in physicalObservationEvent ell A,
          tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
            (originalDatum ell j z)) y ∂physicalObservationLaw (graphRawLaw F) K)-
        expectedRadialPatchCenter (graphFormVector G) y ht hb Z lam| ≤
        sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
          (max (corePriceExcess Z lam (graphFormVector G)) 0) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
          (2*masterWidth c₁ r₀ s y) := by
  have hψ := graphFormVector_admissible G hG
  have hm : formMass (graphFormVector G) = 1 := hψ.2.2.2.2.1
  obtain ⟨t,ht,ht0,hgap,hpot⟩ := sharp_joint_selected_patch hψ hy ha1 hb hba hZ hlam hq hqr hcollar
  refine ⟨t,ht,ht0,hgap,?_⟩
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    rw [←formRawLaw_graph]
    exact rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    rw [←formRawLaw_graph]
    exact formRawLaw_ae_no_poles (graphFormVector F) y
  have hn : t ≤ ‖y‖ := by
    have := ht.2
    unfold localCellRadius at this
    nlinarith [norm_nonneg y]
  have hcmp := original_master_radial_center_comparison (graphRawLaw F)
    hψ.sobolevFermion ell j y hi he hc hcL hr hs hs1 canonicalRealPacket_smooth
    canonicalRealPacket_compact canonicalRealPacket_normalized canonicalRealPacket_radial
    canonicalRealPacket_support hinfo hp (by rw [formRawLaw_graph]; exact hlaw)
    ht0 hb (by linarith [ht.1,localCellRadius_pos hy]) hn hZ hlam hq (by linarith [ht.1])
  have hraw := sharp_cell_local_potential hψ hy ha1 hZ hlam
    (by linarith [masterWidth_pos hc hr hs y] : 0 < 2*masterWidth c₁ r₀ s y)
    hcell
  simp only [hm,mul_one] at hcmp
  exact hcmp.trans (add_le_add hpot hraw)

end

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis

theorem sharp_eventLaw_field_cap_of_cell {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    {N K : ℕ} (F G : fermionGraph N) (hG : ‖fermionGraphValue N G‖^2 = 1)
    (ell : Fin K → ℝ) (j : ℕ) {A : Set (Fin K × (Fin N × Fin 3) → ℝ)}
    (hinfo : MeasurableSet[observationInformation ell j] (physicalObservationEvent ell A))
    (hp : 0 < physicalObservationProbability F ell A)
    (hlaw : graphRawLaw G = (ENNReal.ofReal (physicalObservationProbability F ell A))⁻¹ •
      Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict
        (physicalObservationEvent ell A)))
    {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y)
    {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*
      localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y) :
    Z/‖y‖-lam-(physicalObservationProbability F ell A)⁻¹*
      (∫ z in physicalObservationEvent ell A,
        tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
          (originalDatum ell j z)) y ∂physicalObservationLaw (graphRawLaw F) K) ≤
      tfPatchCapConstant/(localCellRadius y)^4+
      (sharpPotentialRemainder (localCellRadius y) b
        (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
        (max (corePriceExcess Z lam (graphFormVector G)) 0) q+
      sharpLocalPotentialBudget (localCellRadius y)
        (localOffsetMass (max (corePriceExcess Z lam (graphFormVector G)) 0) y)
        (2*masterWidth c₁ r₀ s y)) := by
  obtain ⟨t,ht,ht0,hgap,hcmp⟩ := sharp_eventLaw_joint_comparison_of_cell hZ hlam F G hG ell j
    hinfo hp hlaw hy ha1 hc hcL hr hs hs1 hcell hb hba hq hqr hqR hcollar
  have ha := localCellRadius_pos hy
  have hnorm : t ≤ ‖y‖ := by
    have := ht.2
    unfold localCellRadius at this
    nlinarith [norm_nonneg y]
  have hcap := expectedRadialPatchCenter_le (graphFormVector_sobolev G).sobolevVector
    y ht0 hb (by linarith [ht.1]) hnorm Z lam
  have hm : formMass (graphFormVector G) = 1 := (graphFormVector_admissible G hG).2.2.2.2.1
  rw [hm,mul_one] at hcap
  have hpw : (localCellRadius y)^4 ≤ (t-4*b)^4 := pow_le_pow_left₀ ha.le (by linarith [ht.1]) 4
  have hd := div_le_div_of_nonneg_left tfPatchCapConstant_pos.le (by positivity : 0 < (localCellRadius y)^4) hpw
  have hh := (le_abs_self _).trans hcmp
  linarith [hcap.trans hd]

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget

end CoulombAtom
end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityTailTiltBarrier
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma OwnProbabilityTailTiltState.to_tailTiltState {N K : ℕ} {F : fermionGraph N}
    {Z lam r δ : ℝ} {p₀ p₁ : Fin (K+1) → ℝ}
    (hF : OwnProbabilityTailTiltState Z lam r K p₀ δ F)
    (hr : 0 < r) (h₁ : ∀ j, 0 < p₁ j) (h01 : ∀ j, p₀ j ≤ p₁ j) :
    TailTiltState Z lam r K p₁ δ F := by
  refine ⟨hF.1,hF.2.1,?_⟩
  intro j A hA hp
  obtain ⟨G,hGn,hGlaw,hGE⟩ := hF.2.2 j A hA ((h01 j).trans hp)
  refine ⟨G,hGn,hGlaw,hGE.trans ?_⟩
  let := graphRawLaw_probability F hF.1
  let := physicalObservationLaw_probability (K := K) (graphRawLaw F)
  exact dyadicUniformEventBudget_mono (by positivity) (h₁ j) hp (measureReal_le_one (s := A))

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_OwnProbabilityRareCapBarrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

lemma tinyProbabilityFloor_le_eighty {Z u : ℝ} (hZ : 0 ≤ Z) (hu : 0 ≤ u) :
    tinyProbabilityFloor Z u ≤ min 1 (u^80) := by
  exact div_le_self (le_min (by norm_num) (pow_nonneg hu _)) (by linarith)

end Work_OwnProbabilityRareCap_barrier_scope

open MeasureTheory Filter Set
open scoped Topology

open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end

section
-- module Solutions.OAIQ071_CI.CoulombIonization_RadialBounds_PointInverseEventsCell
attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CoulombAtom

section
open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem TailTiltState.posterior_cap_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1) :
      ∀ (j : Fin (K+1)) (y : Space) (_hy : y ≠ 0) (_ha1 : localCellRadius y ≤ 1)
        (_hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y) (b q θ : ℝ) (_hb : 0 < b) (_hba : 2*b ≤ localCellRadius y)
        (_hq : 0 < q) (_hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
        (_hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
        (_hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3)),
      tfPatchCapConstant/(localCellRadius y)^4+
        (sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y)) < θ →
      ((physicalObservationLaw (graphRawLaw F) K)
        {z | θ < Z/‖y‖-lam-tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
            (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y}).toReal < p₀ j := by
  intro j y hy ha1 hcell b q θ hb hba hq hqr hqR hcollar hsmall
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let P := fun z : Configuration N × (Fin K × (Fin N × Fin 3) → ℝ) =>
    tfPotential (jointMasterPosterior (graphRawLaw F) ell j c₁ r₀ s canonicalRealPacket
      (originalDatum ell j z)) y
  let A := {z | θ < Z/‖y‖-lam-P z}
  have hA : MeasurableSet[observationInformation ell j] A :=
    measurableSet_lt measurable_const (measurable_const.sub
      (jointMasterPosterior_potential_measurable (graphRawLaw F) ell j y hc hr₀ hs canonicalRealPacket_smooth.continuous))
  obtain ⟨B,hB,hBA⟩ := observation_event_tail_representation ell j hA
  let p := ((physicalObservationLaw (graphRawLaw F) K) A).toReal
  have hpB : physicalObservationProbability F ell B = p := by
    change ((physicalObservationLaw (graphRawLaw F) K) (physicalObservationEvent ell B)).toReal = p
    rw [hBA]
  change p < p₀ j
  by_contra! hn
  have hp : 0 < p := (h₀ j).trans_le hn
  obtain ⟨G,hGn,hlaw,hDE⟩ := hstate.2.2 j A hA hn
  rw [←hBA] at hlaw
  have hcollar' : localCellRadius y ≤ b^2*localOffsetMass
      (max (corePriceExcess Z lam (graphFormVector G)) 0) y := by
    apply hcollar.trans
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg b)
    unfold localOffsetMass
    linarith [le_max_left (1/(localCellRadius y)^3) 1,Real.sqrt_nonneg
      (max (corePriceExcess Z lam (graphFormVector G)) 0*localCellRadius y)]
  have hupper := sharp_eventLaw_field_cap_of_cell hZ hlam F G hGn ell j
    (by rwa [hBA]) (by rwa [hpB]) hlaw hy ha1 hc hcL hr₀ hs hs1 hcell hb hba hq hqr hqR hcollar'
  have herror := sharp_combined_error_mono hy hb hq hDE
    (by linarith [masterWidth_pos hc hr₀ hs y] : 0 ≤ 2*masterWidth c₁ r₀ s y)
  rw [hpB,hBA] at hupper
  have hi : Integrable (rawPotential y) (graphRawLaw F) := by
    simpa only [formRawLaw_graph] using rawPotential_form_integrable (graphFormVector_sobolev F).sobolevVector y
  have he : ∀ᵐ x ∂graphRawLaw F, ∀ i, x i ≠ y := by
    simpa only [formRawLaw_graph] using formRawLaw_ae_no_poles (graphFormVector F) y
  have hPi : Integrable P (physicalObservationLaw (graphRawLaw F) K) :=
    jointMasterPosterior_potential_integrable (graphRawLaw F) ell j y hi he hc hr₀ hs
      canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
        canonicalRealPacket_radial canonicalRealPacket_support
  have hlower := threshold_event_mean_ge (physicalObservationLaw (graphRawLaw F) K)
    ((integrable_const (Z/‖y‖-lam)).sub hPi) ((observationInformation_le ell j) A hA)
    (fun z hz => hz.le) hp
  simp only [Pi.sub_apply] at hlower
  rw [normalized_setIntegral_const_sub _ A hPi hp] at hlower
  exact (not_le_of_gt (lt_of_le_of_lt (hupper.trans (add_le_add le_rfl herror)) hsmall)) hlower

end

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem OwnProbabilityTailTiltState.rare_cap_event_of_cell_oai {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {δ c₁ r₀ s : ℝ}
    (hF : OwnProbabilityTailTiltState Z lam r K
      (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*r)) δ F)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) {y : Space} (hy : y ≠ 0)
    (hu1 : (2:ℝ)^j.val*r ≤ 1)
    (hgeom : InverseFiniteGeometry c₁ r₀ s (((2:ℝ)^j.val*r)^(101/100:ℝ)) y)
    (hcap : originalFieldCapBudget ((2:ℝ)^j.val*r) (((2:ℝ)^j.val*r)^80) δ c₁ r₀ s y
        ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent) <
        (tfPatchCapConstant+2)/(localCellRadius y)^4) :
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | (tfPatchCapConstant+2)/(localCellRadius y)^4 <
        originalQueryField F Z lam r j c₁ r₀ s z y} < ((2:ℝ)^j.val*r)^80 := by
  have hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y := by
    linarith [hgeom.master_fit,hgeom.cut_pos,localCellRadius_pos hy]
  let p₁ : Fin (K+1) → ℝ := fun k => min 1 (((2:ℝ)^k.val*r)^80)
  have h₁ : ∀ k, 0 < p₁ k := by intro k; dsimp [p₁]; positivity
  have hT := hF.to_tailTiltState hr h₁
    (fun _ => tinyProbabilityFloor_le_eighty hZ (by positivity))
  have hu : 0 < (2:ℝ)^j.val*r := by positivity
  have hj : p₁ j = ((2:ℝ)^j.val*r)^80 := min_eq_right (pow_le_one₀ hu.le hu1)
  have hh := hT.posterior_cap_of_cell hZ hlam h₁ hc hcL hr₀ hs hs1 j y hy hgeom.radius_le hcell
    ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent)
    ((tfPatchCapConstant+2)/(localCellRadius y)^4)
    hgeom.cut_pos hgeom.cut_le hgeom.probe_pos hgeom.probe_fit hgeom.probe_margin hgeom.collar
    (by rw [hj]; exact hcap)
  unfold originalQueryField originalQueryDensity
  simpa only [hj,Measure.real] using hh

end CoulombAtom

end

end OAI
end

theorem solution : type_of% @OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell_oai := @OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell_oai
