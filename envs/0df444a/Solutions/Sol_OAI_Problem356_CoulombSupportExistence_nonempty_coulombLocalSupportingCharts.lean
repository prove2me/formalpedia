-- Prove2me | solution 1 for OAI.Problem356.CoulombSupportExistence.nonempty_coulombLocalSupportingCharts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:56:13.684109+00:00
-- url     : https://prove2.me/submissions/819383c5-1d45-4ac2-8d30-f8d7f16b850a

-- Generated from openai/math@1581d4c lean/OAI/Analysis/CoulombTransport/CoulombSupportExistence.lean:L43-L99
-- (upload_full_project.md Phase 4): solution for node OAI.Problem356.CoulombSupportExistence.nonempty_coulombLocalSupportingCharts. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CoulombCounterexample
import Definitions.Def_OAI_Analysis_CoulombTransport_AxisHessian
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchCoupling
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombEstimates
import Definitions.Def_OAI_Analysis_CoulombTransport_BranchSeparation
import Definitions.Def_OAI_Analysis_CoulombTransport_GraphBridge
import Definitions.Def_OAI_Analysis_CoulombTransport_DualCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_OptimalLocalization
import Definitions.Def_OAI_Analysis_CoulombTransport_Calibration
import Definitions.Def_OAI_Analysis_CoulombTransport_CertificateAttainment
import Definitions.Def_OAI_Analysis_CoulombTransport_SplitMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_PartitionLabel
import Definitions.Def_OAI_Analysis_CoulombTransport_CenterCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_CommonBranches
import Definitions.Def_OAI_Analysis_CoulombTransport_DensityMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_ComponentPotential
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalImplicit
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianCLM
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCalculus
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryEquation
import Definitions.Def_OAI_Analysis_CoulombTransport_HessianMatrix
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombCoercivity
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_StationaryMap
import Definitions.Def_OAI_Analysis_CoulombTransport_LocalBranchMeasure
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothPushforward
import Definitions.Def_OAI_Analysis_CoulombTransport_GluedCertificate
import Definitions.Def_OAI_Analysis_CoulombTransport_GoodTypePermutation
import Definitions.Def_OAI_Analysis_CoulombTransport_IsometryTransport
import Definitions.Def_OAI_Analysis_CoulombTransport_SmoothBranchMarginal
import Definitions.Def_OAI_Analysis_CoulombTransport_StateDual
import Definitions.Def_OAI_Analysis_CoulombTransport_CoulombSupportExistence
import Theorems.Thm_OAI_Problem356_CoulombCharts_centerStateHessian_axis_eq
import Theorems.Thm_OAI_Problem356_CoulombCharts_nonempty_coulombCharts
import Theorems.Thm_OAI_Problem356_GeometryJets_contDiffAt_stationaryEquation_center
import Theorems.Thm_OAI_Problem356_GeometryJets_hasFDerivAt_stationary_center
import Theorems.Thm_OAI_Problem356_LocalGeometry_nonempty_localSupportingCharts
import Theorems.Thm_OAI_Problem356_StationaryMap_hasFDerivAt_statePotential

-- ---- from OAI.Analysis.CoulombTransport.AxisHessian ----
namespace OAI

/-! Explicit nondegeneracy algebra for the two local Coulomb branches.
The Hessian eigenvalues are 2 in the axial direction and -1 transversely.
A common regularization parameter K = 20 works in every direction. -/

noncomputable section

namespace Problem356.LocalHessian

open Matrix

lemma eigenvalue_cases (k i : Fin 3) :
    eigenvalue k i = 2 ∨ eigenvalue k i = -1 := by
  unfold eigenvalue
  split_ifs <;> simp

lemma scalar_quadratic_coercive {q x z : ℝ}
    (hq : q = 2 ∨ q = -1) :
    16 * (x ^ 2 + z ^ 2) ≤
      (20 + 2 * q) * x ^ 2 - 2 * q * x * z +
        (20 + (9 / 8) * q) * z ^ 2 := by
  rcases hq with rfl | rfl
  · nlinarith [sq_nonneg (x - z), sq_nonneg x, sq_nonneg z]
  · nlinarith [sq_nonneg (x + z), sq_nonneg x, sq_nonneg z]

end Problem356.LocalHessian

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.HessianCLM ----
namespace OAI

universe uN

noncomputable section

namespace Problem356.LocalHessian

open Matrix
open scoped RealInnerProductSpace

lemma stateOperator_fst_apply (k : Fin 3) (v : StateSpace) (i : Fin 3) :
    (stateOperator k v).1 i =
      (20 + 2 * eigenvalue k i) * v.1 i - eigenvalue k i * v.2 i := by
  change ((regularizedHessian k) *ᵥ (WithLp.ofLp (stateCoordinates.symm v)))
    (Sum.inl i) = _
  rw [regularizedHessian, fromBlocks_mulVec]
  simp [upperBlock, mixedBlock, mulVec_diagonal, sub_eq_add_neg]

lemma stateOperator_snd_apply (k : Fin 3) (v : StateSpace) (i : Fin 3) :
    (stateOperator k v).2 i =
      -eigenvalue k i * v.1 i + (20 + (9 / 8) * eigenvalue k i) * v.2 i := by
  change ((regularizedHessian k) *ᵥ (WithLp.ofLp (stateCoordinates.symm v)))
    (Sum.inr i) = _
  rw [regularizedHessian, fromBlocks_mulVec]
  simp [lowerBlock, mixedBlock, mulVec_diagonal]

lemma stateOperator_joint_coercive (k : Fin 3) (v : StateSpace) :
    16 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) ≤
      ⟪v.1, (stateOperator k v).1⟫ + ⟪v.2, (stateOperator k v).2⟫ := by
  simp only [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, stateOperator_fst_apply, stateOperator_snd_apply,
    mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := scalar_quadratic_coercive (x := v.1 i) (z := v.2 i) (eigenvalue_cases k i)
  nlinarith

lemma stateOperator_coercive (k : Fin 3) (v : StateSpace) :
    16 * ‖v‖ ^ 2 ≤
      ⟪v.1, (stateOperator k v).1⟫ + ⟪v.2, (stateOperator k v).2⟫ := by
  have hn : ‖v‖ ^ 2 ≤ ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖v.1‖ ‖v.2‖ with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg ‖v.1‖]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ‖v.2‖]
  nlinarith [stateOperator_joint_coercive k v]

end Problem356.LocalHessian

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CoulombCalculus ----
namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma contDiffAt_pairCost {n : WithTop ENat} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ n (pairCost : E → ℝ) x := by
  exact (contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)

lemma contDiffAt_pairGradient {n : WithTop ENat} {x : E} (hx : x ≠ 0) :
    ContDiffAt ℝ n (pairGradient : E → E) x := by
  exact (((contDiffAt_norm ℝ hx).pow 3).inv
    (pow_ne_zero 3 (norm_ne_zero_iff.mpr hx))).neg.smul contDiffAt_id

end Problem356.CoulombCalculus

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.StationaryEquation ----
namespace OAI

universe uE

noncomputable section

namespace Problem356.GeometryJets

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma contDiffAt_stationaryEquation {n : WithTop ENat} (K : ℝ) (a : E)
    (p : E × (E × E)) (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2)
    (hyz : p.1 ≠ p.2.2) : ContDiffAt ℝ n (stationaryEquation K a) p := by
  have hy : ContDiffAt ℝ n (fun q : E × (E × E) => q.1) p := contDiffAt_fst
  have hx : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.1) p := contDiffAt_snd.fst
  have hz : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.2) p := contDiffAt_snd.snd
  have h1 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hxy)).comp p (hx.sub hy)
  have h2 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hxz)).comp p (hx.sub hz)
  have h3 := (contDiffAt_pairGradient (n := n) (sub_ne_zero.mpr hyz)).comp p (hy.sub hz)
  exact ((h1.add h2).add (hx.const_smul K)).prodMk
    (((h2.neg.sub h3).sub contDiffAt_const).add ((hz.add contDiffAt_const).const_smul K))

end Problem356.GeometryJets

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CoulombCharts ----
namespace OAI

noncomputable section
open scoped ContDiff

namespace Problem356.CoulombCharts

open CoulombCalculus GeometryJets LocalImplicit

theorem stationary_state_partial_eq (k : Fin 3) :
    fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k)) ∘L
      ContinuousLinearMap.inr ℝ E3 (E3 × E3) = LocalHessian.stateOperator k := by
  rw [(hasFDerivAt_stationary_center 20 (axisVector k) (norm_axisVector k)).fderiv]
  have h : centerTotalDerivative 20 (CoulombCalculus.pairHessian (axisVector k)) ∘L
      ContinuousLinearMap.inr ℝ E3 (E3 × E3) =
      centerStateHessian 20 (CoulombCalculus.pairHessian (axisVector k)) := by
    apply ContinuousLinearMap.ext
    intro v
    simp [centerTotalDerivative]
  rw [h, centerStateHessian_axis_eq]

end Problem356.CoulombCharts

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.StationaryMap ----
namespace OAI

universe uE

noncomputable section

open scoped RealInnerProductSpace

namespace Problem356.StationaryMap

open CoulombCalculus

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Joint parameter/state analyticity on pairwise-distinct triples. -/
theorem contDiffAt_jointPotential (a : E) {p : E × (E × E)}
    (hxy : p.2.1 ≠ p.1) (hxz : p.2.1 ≠ p.2.2) (hzy : p.2.2 ≠ p.1)
    {n : WithTop ENat} : ContDiffAt ℝ n (jointPotential a) p := by
  have hY : ContDiffAt ℝ n (fun q : E × (E × E) => q.1) p := contDiffAt_fst
  have hX : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.1) p := contDiffAt_snd.fst
  have hZ : ContDiffAt ℝ n (fun q : E × (E × E) => q.2.2) p := contDiffAt_snd.snd
  have hXY := (contDiffAt_pairCost (sub_ne_zero.mpr hxy)).comp p (hX.sub hY)
  have hXZ := (contDiffAt_pairCost (sub_ne_zero.mpr hxz)).comp p (hX.sub hZ)
  have hZY := (contDiffAt_pairCost (sub_ne_zero.mpr hzy)).comp p (hZ.sub hY)
  exact (((hXY.add hXZ).add hZY).sub
    (contDiffAt_const.sub (contDiffAt_const.mul (hX.norm_sq ℝ)))).sub
    ((contDiffAt_const.mul (contDiffAt_const.inner ℝ (hZ.add contDiffAt_const))).sub
      (contDiffAt_const.mul ((hZ.add contDiffAt_const).norm_sq ℝ)))

end Problem356.StationaryMap

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.StateDual ----
namespace OAI

universe uE uF uP

noncomputable section

open Set
open scoped InnerProductSpace

namespace Problem356

variable (E : Type uE) (F : Type uF) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Differentiating the scalar representative of a product-state gradient. -/
theorem hasFDerivAt_stateDual_comp {P : Type uP} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {G : P → E × F} {G' : P →L[ℝ] E × F} {p : P}
    (hG : HasFDerivAt G G' p) :
    HasFDerivAt (fun q => stateDual E F (G q)) ((stateDual E F).comp G') p :=
  by
  exact HasFDerivAt.comp (𝕜 := ℝ) (g := stateDual E F) p
    ((stateDual E F).hasFDerivAt (x := G p)) hG

/-- The quadratic form of the scalar Hessian agrees with the product-state
coercivity expression, with the argument order used by matrix certificates. -/
theorem stateDual_comp_quadratic (A : (E × F) →L[ℝ] E × F) (v : E × F) :
    ((stateDual E F).comp A) v v =
      ⟪v.1, (A v).1⟫_ℝ + ⟪v.2, (A v).2⟫_ℝ := by
  simp only [ContinuousLinearMap.comp_apply, stateDual_apply, real_inner_comm]

end Problem356

end

end OAI

-- ---- from OAI.Analysis.CoulombTransport.CoulombSupportExistence ----
namespace OAI

noncomputable section
open Filter Set
open scoped Topology ContDiff RealInnerProductSpace

namespace Problem356.CoulombSupportExistence

open CoulombCalculus GeometryJets LocalGeometry

/-- The two explicit conventions for the stationary field coincide. -/
theorem stationary_eq (a : E3) :
    StationaryMap.stationary a = stationaryEquation 20 a := by
  funext p
  apply Prod.ext
  · rfl
  · simp only [StationaryMap.stationary, stationaryEquation]
    have hn (x y : E3) : pairGradient (x - y) = -pairGradient (y - x) := by
      rw [← neg_sub y x, pairGradient_neg]
    rw [hn p.2.2 p.2.1, hn p.2.2 p.1]
    module

private def H (a y : E3) (s : E3 × E3) :
    (E3 × E3) →L[ℝ] ((E3 × E3) →L[ℝ] ℝ) :=
  (stateDual E3 E3).comp
    ((fderiv ℝ (stationaryEquation 20 a) (y, s)).comp
      (ContinuousLinearMap.inr ℝ E3 (E3 × E3)))

private theorem D_eq (a y : E3) (s : E3 × E3) :
    D a y s = StationaryMap.stateDifferential a y s := by
  unfold D
  rw [← stationary_eq]
  rfl

/-- The actual Coulomb stationary charts admit a local supporting potential
with exact equality precisely on the stationary branch. -/
theorem nonempty_coulombLocalSupportingCharts (k : Fin 3) :
    Nonempty (LocalSupportingCharts
      (StationaryMap.jointPotential (axisVector k))
      (stationaryEquation 20 (axisVector k))
      (axisVector k) (0, -axisVector k)) := by
  let a : E3 := axisVector k
  have ha : ‖a‖ = 1 := norm_axisVector k
  have ha0 : a ≠ 0 := axisVector_ne_zero k
  have haminus : a ≠ -a := by
    intro h
    have hh := congrArg (fun x : E3 => x k) h
    norm_num [a, axisVector] at hh
  have hsep : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)),
      q.2.1 ≠ q.1 ∧ q.2.1 ≠ q.2.2 ∧ q.2.2 ≠ q.1 := by
    have h₁ : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)), q.2.1 ≠ q.1 :=
      (isOpen_ne_fun (f := fun q : E3 × (E3 × E3) => q.2.1)
        (g := fun q => q.1) (by fun_prop) (by fun_prop)).mem_nhds ha0.symm
    have h₂ : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)), q.2.1 ≠ q.2.2 :=
      (isOpen_ne_fun (f := fun q : E3 × (E3 × E3) => q.2.1)
        (g := fun q => q.2.2) (by fun_prop) (by fun_prop)).mem_nhds
          (neg_ne_zero.mpr ha0).symm
    have h₃ : ∀ᶠ q : E3 × (E3 × E3) in 𝓝 (a, (0, -a)), q.2.2 ≠ q.1 :=
      (isOpen_ne_fun (f := fun q : E3 × (E3 × E3) => q.2.2)
        (g := fun q => q.1) (by fun_prop) (by fun_prop)).mem_nhds haminus.symm
    exact h₁.and (h₂.and h₃)
  obtain ⟨C⟩ := CoulombCharts.nonempty_coulombCharts k
  apply nonempty_localSupportingCharts (D := D a) (H := H a) C
  · exact StationaryMap.contDiffAt_jointPotential a ha0.symm
      (neg_ne_zero.mpr ha0).symm haminus.symm
  · filter_upwards [hsep] with q hq
    change HasFDerivAt (StationaryMap.statePotential a q.1) (D a q.1 q.2) q.2
    rw [D_eq]
    exact StationaryMap.hasFDerivAt_statePotential a q.1 hq.1 hq.2.1 hq.2.2
  · filter_upwards [hsep] with q hq
    have hG := (contDiffAt_stationaryEquation (n := ω) 20 a q hq.1 hq.2.1
      hq.2.2.symm).differentiableAt (by simp)
    have hp : HasFDerivAt (fun z : E3 × E3 => (q.1, z))
        (ContinuousLinearMap.inr ℝ E3 (E3 × E3)) q.2 := by
      exact hasFDerivAt_prodMk_right q.1 q.2
    have hpartial := hG.hasFDerivAt.comp q.2 hp
    convert! hasFDerivAt_stateDual_comp E3 E3 hpartial using 1
  · have hc := (contDiffAt_stationaryEquation_center (n := ω) 20 a ha).continuousAt_fderiv
      (by simp)
    exact continuousAt_const.clm_comp (hc.clm_comp continuousAt_const)
  · intro v hv
    change 0 < ((stateDual E3 E3).comp
      ((fderiv ℝ (stationaryEquation 20 (axisVector k))
        (axisVector k, (0, -axisVector k))).comp
          (ContinuousLinearMap.inr ℝ E3 (E3 × E3)))) v v
    rw [CoulombCharts.stationary_state_partial_eq, stateDual_comp_quadratic]
    have hc := LocalHessian.stateOperator_coercive k v
    have hp : 0 < (16 : ℝ) * ‖v‖ ^ 2 := by positivity
    exact hp.trans_le hc
  · intro q hq
    simp only [D, a, Prod.eta, hq, map_zero]

end Problem356.CoulombSupportExistence

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem356 OAI.Problem356.CoulombSupportExistence
open Filter Set
open scoped Topology ContDiff RealInnerProductSpace
open CoulombCalculus GeometryJets LocalGeometry


theorem solution : type_of% @_root_.OAI.Problem356.CoulombSupportExistence.nonempty_coulombLocalSupportingCharts := @_root_.OAI.Problem356.CoulombSupportExistence.nonempty_coulombLocalSupportingCharts
