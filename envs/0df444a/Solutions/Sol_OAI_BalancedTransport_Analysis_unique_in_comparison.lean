-- Prove2me | solution 1 for OAI.BalancedTransport.Analysis.unique_in_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T06:00:59.006701+00:00
-- url     : https://prove2.me/submissions/3db73bdd-f61e-412a-b3df-f0686b376e35

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/Comparison.lean:L85-L132
-- (upload_full_project.md Phase 4): solution for node OAI.BalancedTransport.Analysis.unique_in_comparison. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FieldBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_CompactFamilies
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ResidualRegularity
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RhoAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveLog
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericPrograms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_ComputabilityRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_MachineRecursion
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FiniteSimulator
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_UniversalInput
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericEvaluation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericDifferentiation
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericScopes
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericJets
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_NumericAlgebra
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Elementary
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergyCurve
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Sobolev
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EnergySlice
import Theorems.Thm_OAI_BalancedTransport_Analysis_SliceH2_sub
import Theorems.Thm_OAI_BalancedTransport_Analysis_energy_pairing_bound
import Theorems.Thm_OAI_BalancedTransport_Analysis_l2Energy_eq_zero_of_bound
import Theorems.Thm_OAI_BalancedTransport_Analysis_l2Energy_zero_pointwise
import Theorems.Thm_OAI_BalancedTransport_Geometry_ForwardEq_mixedD

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Work ----
namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pd_sub (i : Fin 3) {f g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    pd i (fun y => f y - g y) x = pd i f x - pd i g x := by
  simp only [pd, fderiv_fun_sub hf hg, sub_apply]

theorem pd_contDiff (i : Fin 3) {f : Space → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (pd i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

end BalancedTransport.Geometry
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EnergyCurve ----
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal

lemma coordinateL2_coe (i : Fin 3) (V : Lp Space 2 (volume : Measure Space)) :
    (coordinateL2 i V : Space → ℝ) =ᵐ[volume] fun x => (V : Space → Space) x i :=
  ContinuousLinearMap.coeFn_compLpL _ _

lemma l2Inner_integral {V W : Lp Space 2 (volume : Measure Space)}
    {v w : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v)
    (hw : (W : Space → Space) =ᵐ[volume] w) (i : Fin 3) :
    inner ℝ (coordinateL2 i V) (coordinateL2 i W) = ∫ x, v x i * w x i := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coordinateL2_coe i V, coordinateL2_coe i W, hv, hw] with x hv' hw' hx hy
  simp only [hv', hw', hx, hy, RCLike.inner_apply, conj_trivial]
  ring

lemma l2Energy_integral {V : Lp Space 2 (volume : Measure Space)}
    {v : Space → Space} (hv : (V : Space → Space) =ᵐ[volume] v) :
    l2Energy V = ∑ i : Fin 3, ∫ x, (v x i)^2 := by
  unfold l2Energy
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq, l2Inner_integral hv hv]
  simp only [pow_two]

end BalancedTransport.Analysis
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Energy ----
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma Smooth.slice {v : Field F} (hv : Smooth v) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ (⊤ : ℕ∞) (v t) := by
  apply contDiffOn_univ.mp
  exact hv.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩)

lemma CH.memLp {v : Field F} {k : ℕ} (hv : CH k v)
    (a : List (Fin 3)) (ha : a.length ≤ k) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (spatialD a v t) 2 (volume : Measure Space) := by
  obtain ⟨V, _, he⟩ := hv a ha
  exact (Lp.memLp (V t)).ae_eq (he t ht)

lemma membrane_component {f : Space → Space} (hf : MemLp f 2 (volume : Measure Space))
    (hc : Continuous f) (i : Fin 3) : MemLp (fun x => f x i) 2 (volume : Measure Space) := by
  apply hf.of_le ((continuous_apply i).comp hc).aestronglyMeasurable
  exact Eventually.of_forall (fun x => norm_le_pi_norm (f x) i)

end BalancedTransport.Analysis
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.EnergySlice ----
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry

lemma sliceH2_of_CH {u : Velocity} (hu : Smooth u) (hH : CH 2 u) {t : ℝ} (ht : 0 ≤ t) :
    SliceH2 (u t) := by
  have hs := Smooth.slice hu ht
  exact ⟨hs, fun i => membrane_component (CH.memLp hH [] (by simp) ht) hs.continuous i,
    fun i j => membrane_component (CH.memLp hH [j] (by simp) ht) (pd_contDiff j hs).continuous i,
    fun i j => membrane_component (CH.memLp hH [j,j] (by simp) ht)
      (pd_contDiff j (pd_contDiff j hs)).continuous i⟩

end BalancedTransport.Analysis
end

end OAI

-- ---- from OAI.MathematicalPhysics.NavierStokes.BalancedTransport.Comparison ----
namespace OAI

noncomputable section
namespace BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry

lemma difference_divergence {u U : Velocity} (hu : Smooth u) (hU : Smooth U)
    {t : ℝ} (ht : 0 ≤ t) (hdu : ∀ x, div u t x = 0) (hdU : ∀ x, div U t x = 0)
    (x : Space) : ∑ j, pd j (fun x => u t x - U t x) x j = 0 := by
  simp only [pd_sub _ ((Smooth.slice hu ht).differentiable (by simp) x)
      ((Smooth.slice hU ht).differentiable (by simp) x), Pi.sub_apply,
    Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr ((hdu x).trans (hdU x).symm)

lemma difference_equation {ν : ℝ} {f u U : Velocity} {p : Pressure}
    (hu : ZeroDataSolution ν f u p) (hU : ZeroDataSolution ν f U (fun _ _ => 0))
    {t : ℝ} (ht : 0 ≤ t) (c : ℝ) (x : Space) (i : Fin 3) :
    timeD u t x i - timeD U t x i =
      ν * (∑ j, pd j (pd j (fun x => u t x - U t x)) x i) -
      (∑ j, u t x j * pd j (fun x => u t x - U t x) x i) -
      (∑ j, (u t x j - U t x j) * pd j (U t) x i) - pd i (fun x => p t x - c) x := by
  have hus := Smooth.slice hu.1 ht
  have hUs := Smooth.slice hU.1 ht
  have hd (j : Fin 3) : pd j (fun x => u t x - U t x) = fun x => pd j (u t) x - pd j (U t) x :=
    funext (fun x => pd_sub j (hus.differentiable (by simp) x) (hUs.differentiable (by simp) x))
  have hdu := congrFun (hu.2.2.2.2 t ht x) i
  have hdU := congrFun (hU.2.2.2.2 t ht x) i
  simp only [convection, laplacian, gradient, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul] at hdu hdU
  have hu' : timeD u t x i + (∑ j, u t x j * pd j (u t) x i) =
      -pd i (p t) x + ν * (∑ j, pd j (pd j (u t)) x i) + f t x i := hdu
  have hU' : timeD U t x i + (∑ j, U t x j * pd j (U t) x i) =
      ν * (∑ j, pd j (pd j (U t)) x i) + f t x i := by
    change timeD U t x i + (∑ j, U t x j * pd j (U t) x i) =
      -pd i (fun _ => (0 : ℝ)) x + ν * (∑ j, pd j (pd j (U t)) x i) + f t x i at hdU
    simpa only [pd_const, neg_zero, zero_add] using hdU
  simp only [hd, pd_sub _ ((pd_contDiff _ hus).differentiable (by simp) x)
      ((pd_contDiff _ hUs).differentiable (by simp) x), Pi.sub_apply, pd_sub_const]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hu' hU' ⊢
  linear_combination hu' - hU'

lemma constant_pressure_of_velocity_eq {ν : ℝ} {f u U : Velocity} {p : Pressure}
    (hu : ZeroDataSolution ν f u p) (hU : ZeroDataSolution ν f U (fun _ _ => 0))
    (he : ∀ t, 0 ≤ t → ∀ x, u t x = U t x) :
    ∀ t, 0 ≤ t → ∀ x y, p t x = p t y := by
  have hf : ForwardEq u U := fun t ht => funext (he t ht)
  intro t ht
  have hg (x : Space) : gradient p t x = 0 := by
    have hd := hu.2.2.2.2 t ht x
    have hD := hU.2.2.2.2 t ht x
    have heD := congrFun (hf.mixedD [none] t ht) x
    change timeD u t x = timeD U t x at heD
    have heL : laplacian u t x = laplacian U t x := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun (hf.mixedD [some i, some i] t ht) x
    have heC : convection u t x = convection U t x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [he t ht x, show spaceD i u t x = spaceD i U t x from
        congrFun (hf.mixedD [some i] t ht) x]
    have hz : gradient (fun _ _ => 0) t x = 0 := by ext i; simp [gradient, spaceD]
    rw [heD, heL, heC] at hd
    rw [hz, neg_zero, zero_add] at hD
    have hh : -gradient p t x = 0 := by
      exact add_left_cancel (a := ν • laplacian U t x + f t x)
        (by simpa only [add_assoc, zero_add, add_zero, add_comm, add_left_comm] using hd.symm.trans hD)
    exact neg_eq_zero.mp hh
  apply is_const_of_fderiv_eq_zero ((Smooth.slice hu.2.1 ht).differentiable (by simp))
  intro x
  ext y
  have hd (i : Fin 3) : fderiv ℝ (p t) x (Pi.single i 1) = 0 := congrFun (hg x) i
  have hy : y = ∑ i : Fin 3, y i • (Pi.single i (1 : ℝ) : Space) := by
    ext i
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    fin_cases i <;> simp
  rw [hy, map_sum]
  simp only [map_smul, hd, smul_zero, Finset.sum_const_zero, zero_apply]

theorem unique_in_comparison {ν : ℝ} (hν : 0 ≤ ν) {f U : Velocity}
    (hU : ZeroDataSolution ν f U (fun _ _ => 0)) (hUC : ComparisonClass U (fun _ _ => 0)) :
    UniqueInComparison ν f U := by
  intro u p hu hc
  obtain ⟨Vu, Wu, hVu, _, hdu⟩ := hc.2.1
  obtain ⟨VU, WU, hVU, _, hdU⟩ := hUC.2.1
  let V : ℝ → Lp Space 2 (volume : Measure Space) := fun t => Vu t - VU t
  let W : ℝ → Lp Space 2 (volume : Measure Space) := fun t => Wu t - WU t
  have hV : ContinuousOn V (Ici 0) := hVu.sub hVU
  have hv (t : ℝ) (ht : 0 ≤ t) : (V t : Space → Space) =ᵐ[volume] fun x => u t x - U t x :=
    (Lp.coeFn_sub _ _).trans ((hdu t ht).1.sub (hdU t ht).1)
  have hw (t : ℝ) (ht : 0 ≤ t) : (W t : Space → Space) =ᵐ[volume] fun x => timeD u t x - timeD U t x :=
    (Lp.coeFn_sub _ _).trans ((hdu t ht).2.1.sub (hdU t ht).2.1)
  have hd (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt V (W t) (Ici 0) t :=
    (hdu t ht).2.2.sub (hdU t ht).2.2
  have hzero : V 0 = 0 := by
    apply Lp.ext
    filter_upwards [hv 0 le_rfl, Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx hy
    rw [hx, hu.2.2.1, hU.2.2.1, sub_self, hy]
    rfl
  have he : ∀ t, 0 ≤ t → ∀ x, u t x = U t x := by
    intro T hT
    obtain ⟨C, hC, hbU⟩ := hUC.2.2.1 T hT
    obtain ⟨A, _, hbu⟩ := hc.2.2.1 T hT
    obtain ⟨c, hpc⟩ := hc.2.2.2
    have hbound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
        l2EnergyRate (V t) (W t) ≤ (12 * C) * l2Energy (V t) := by
      have hpair := energy_pairing_bound
        ((sliceH2_of_CH hu.1 hc.1 ht.1).sub (sliceH2_of_CH hU.1 hUC.1 ht.1))
        (Smooth.slice hu.1 ht.1) (Smooth.slice hU.1 ht.1)
        ((Smooth.slice hu.2.1 ht.1).sub contDiff_const) hν hC
        (fun x => (hbu t ⟨ht.1, ht.2.le⟩ x).1)
        (fun x j => (hbu t ⟨ht.1, ht.2.le⟩ x).2 j)
        (fun x j => (hbU t ⟨ht.1, ht.2.le⟩ x).2 j)
        (hu.2.2.2.1 t ht.1)
        (difference_divergence hu.1 hU.1 ht.1 (hu.2.2.2.1 t ht.1) (hU.2.2.2.1 t ht.1))
        (CH.memLp hpc [] (by simp) ht.1) (fun j => CH.memLp hpc [j] (by simp) ht.1)
        (difference_equation hu hU ht.1 (c t))
      simp only [l2EnergyRate, l2Inner_integral (hv t ht.1) (hw t ht.1),
        l2Energy_integral (hv t ht.1), Pi.sub_apply]
      simpa only [Pi.sub_apply, ← mul_assoc, show (2 : ℝ) * 6 = 12 from by norm_num] using
        mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 2)
    have hz := l2Energy_eq_zero_of_bound hV hd hzero hT hbound
    have hzv := l2Energy_zero_pointwise (hv T hT)
      ((Smooth.slice hu.1 hT).continuous.sub (Smooth.slice hU.1 hT).continuous) hz
    intro x
    exact sub_eq_zero.mp (congrFun hzv x)
  exact ⟨he, constant_pressure_of_velocity_eq hu hU he⟩

end BalancedTransport.Analysis
end

end OAI

-- ---- platform node ----
open OAI OAI.BalancedTransport OAI.BalancedTransport.Analysis
open MeasureTheory Filter Set
open scoped Topology ENNReal
open BalancedTransport.Geometry


theorem solution : type_of% @_root_.OAI.BalancedTransport.Analysis.unique_in_comparison := @_root_.OAI.BalancedTransport.Analysis.unique_in_comparison
