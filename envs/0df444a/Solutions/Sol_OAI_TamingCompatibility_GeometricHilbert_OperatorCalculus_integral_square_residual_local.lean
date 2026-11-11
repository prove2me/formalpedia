-- Prove2me | solution 1 for OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.integral_square_residual_local
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:50:03.48242+00:00
-- url     : https://prove2.me/submissions/abfb639c-a9a4-42dc-983c-37c6f5a50904

import Mathlib
import Definitions.Def_OAIQ239Tc003
import Definitions.Def_OAIQ239Tc004

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeWeightedAdjoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open _root_.MeasureTheory MeasureTheory.Measure Set
open scoped ContDiff RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace
variable (μ : Measure V) [IsAddHaarMeasure μ]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma integrable_inner_compact_left {f g : V → W} (hf : Continuous f) (hg : Continuous g)
    (hc : HasCompactSupport f) : Integrable (fun x => ⟪f x,g x⟫) μ := by
  apply (hf.inner hg).integrable_of_hasCompactSupport
  exact hc.mono (fun x hx => by
    change f x ≠ 0
    intro hz
    exact hx (by simp [hz]))

omit [CompleteSpace W] [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma integral_inner_fderiv {u v : V → W} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport u) (e : V) :
    (∫ x, ⟪u x,fderiv ℝ v x e⟫ ∂μ) = -(∫ x, ⟪fderiv ℝ u x e,v x⟫ ∂μ) := by
  apply integral_bilinear_fderiv_right_eq_neg_left_of_integrable (B := innerSL ℝ)
  · exact integrable_inner_compact_left μ
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const) hv.continuous (hc.fderiv_apply ℝ e)
  · exact integrable_inner_compact_left μ hu.continuous
      ((hv.continuous_fderiv (by simp)).clm_apply continuous_const) hc
  · exact integrable_inner_compact_left μ hu.continuous hv.continuous hc
  · exact fun x _ => hu.differentiable (by simp) x
  · exact fun x _ => hv.differentiable (by simp) x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma weightedAdjoint_pairing (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (u : V → W) (v : V → Q)
    (x : V) (hρ : u x ≠ 0 → ρ x ≠ 0) :
    ρ x * ⟪u x,weightedAdjoint e a b ρ v x⟫ =
      -(∑ i, ⟪u x,fderiv ℝ (fun y => (ρ y • a i y).adjoint (v y)) x (e i)⟫) +
        ρ x * ⟪b x (u x),v x⟫ := by
  by_cases hu : u x = 0
  · simp [hu]
  · have hp := hρ hu
    simp only [weightedAdjoint,inner_add_right,inner_smul_right,inner_sum,
      ContinuousLinearMap.adjoint_inner_right]
    rw [mul_add,← mul_assoc,show ρ x * -(ρ x)⁻¹ = -1 by simp [hp]]
    ring

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open _root_.MeasureTheory MeasureTheory.Measure Set Filter
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [MeasurableSpace V] [BorelSpace V] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma exists_smooth_extension_compact {U K : Set V} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : V → W} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : V → W, ContDiff ℝ ∞ g ∧ ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨O,hO,hKO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  have hKi : K ⊆ interior (closure O) := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hO.mem_nhds (hKO hx)) subset_closure)
  obtain ⟨φ,hφone,hφzero,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,V)) hK.isClosed hKi (n := ⊤)
  have hφsupp : tsupport (φ : V → ℝ) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (hφzero x hn)
  refine ⟨fun x => φ x • f x,SchwartzCutoff.smooth hU hf
    (contMDiff_iff_contDiff.mp φ.contMDiff) (hφsupp.trans hOU),?_⟩
  intro x hx
  filter_upwards [hφone.filter_mono (nhds_le_nhdsSet hx)] with y hy
  simp [hy]

variable (μ : Measure V) [IsAddHaarMeasure μ]
omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma integrable_inner_compact_local {u v : V → W} (hu : Continuous u)
    (hv : ∀ x ∈ tsupport u, ContinuousAt v x) (hc : HasCompactSupport u) :
    Integrable (fun x => ⟪u x,v x⟫) μ := by
  have hcont : Continuous (fun x => ⟪u x,v x⟫) := continuous_iff_continuousAt.mpr (fun x => by
    by_cases hx : x ∈ tsupport u
    · exact hu.continuousAt.inner (hv x hx)
    · apply (continuousAt_const : ContinuousAt (fun _ : V => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hx] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy])
  apply hcont.integrable_of_hasCompactSupport
  exact hc.mono (fun x hx => by
    change u x ≠ 0
    intro hz
    exact hx (by simp [hz]))

omit [CompleteSpace W] [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [Fintype ι] in
lemma integral_inner_fderiv_on {U : Set V} (hU : IsOpen U) {u v : V → W}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiffOn ℝ ∞ v U)
    (hc : HasCompactSupport u) (hsub : tsupport u ⊆ U) (e : V) :
    (∫ x, ⟪u x,fderiv ℝ v x e⟫ ∂μ) = -(∫ x, ⟪fderiv ℝ u x e,v x⟫ ∂μ) := by
  obtain ⟨w,hw,hvw⟩ := exists_smooth_extension_compact hU hc hsub hv
  have hl (x : V) : ⟪u x,fderiv ℝ v x e⟫ = ⟪u x,fderiv ℝ w x e⟫ := by
    by_cases hx : x ∈ tsupport u
    · rw [(hvw x hx).fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hr (x : V) : ⟪fderiv ℝ u x e,v x⟫ = ⟪fderiv ℝ u x e,w x⟫ := by
    by_cases hx : x ∈ tsupport u
    · rw [(hvw x hx).eq_of_nhds]
    · rw [fderiv_of_notMem_tsupport ℝ hx]
      simp
  simp_rw [hl,hr]
  exact integral_inner_fderiv μ hu hw hc e

lemma integral_weightedAdjoint_on {U : Set V} (hU : IsOpen U)
    (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (u : V → W) (v : V → Q)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U)
    (hρ : ContDiffOn ℝ ∞ ρ U) (hu : ContDiff ℝ ∞ u) (hv : ContDiffOn ℝ ∞ v U)
    (hc : HasCompactSupport u) (hsub : tsupport u ⊆ U)
    (hρ0 : ∀ x, u x ≠ 0 → ρ x ≠ 0) :
    (∫ x, ρ x * ⟪u x,weightedAdjoint e a b ρ v x⟫ ∂μ) =
      ∫ x, ρ x * ⟪differential e a b u x,v x⟫ ∂μ := by
  classical
  let F : ι → V → W := fun i x => (ρ x • a i x).adjoint (v x)
  let Adj : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  have hF (i : ι) : ContDiffOn ℝ ∞ (F i) U :=
    (Adj.contDiff.comp_contDiffOn (hρ.smul (ha i))).clm_apply hv
  have hFat (i : ι) (x : V) (hx : x ∈ U) : ContDiffAt ℝ ∞ (F i) x :=
    (hF i x hx).contDiffAt (hU.mem_nhds hx)
  have hi (i : ι) : Integrable (fun x => ⟪u x,fderiv ℝ (F i) x (e i)⟫) μ :=
    integrable_inner_compact_local μ hu.continuous (fun x hx =>
      ((hFat i x (hsub hx)).continuousAt_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuousAt_const) hc
  have hj (i : ι) : Integrable (fun x => ⟪fderiv ℝ u x (e i),F i x⟫) μ :=
    integrable_inner_compact_local μ
      ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
      (fun x hx => (hFat i x (hsub (tsupport_fderiv_apply_subset ℝ (e i) hx))).continuousAt)
      (hc.fderiv_apply ℝ (e i))
  have hbF : ContDiffOn ℝ ∞ (fun x => (ρ x • b x).adjoint (v x)) U :=
    (Adj.contDiff.comp_contDiffOn (hρ.smul hb)).clm_apply hv
  have hbi : Integrable (fun x => ρ x * ⟪b x (u x),v x⟫) μ := by
    have hh := integrable_inner_compact_local μ hu.continuous (fun x hx =>
      ((hbF x (hsub hx)).contDiffAt (hU.mem_nhds (hsub hx))).continuousAt) hc
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    simp only [ContinuousLinearMap.adjoint_inner_right,_root_.smul_apply,inner_smul_left,conj_trivial]
  have he (x : V) : ρ x * ⟪differential e a b u x,v x⟫ =
      (∑ i, ⟪fderiv ℝ u x (e i),F i x⟫) + ρ x * ⟪b x (u x),v x⟫ := by
    simp only [differential,inner_add_left,sum_inner,mul_add,Finset.mul_sum,F,
      ContinuousLinearMap.adjoint_inner_right,_root_.smul_apply,inner_smul_left,conj_trivial]
  simp_rw [weightedAdjoint_pairing e a b ρ u v _ (hρ0 _),he]
  change (∫ x, -(∑ i, ⟪u x,fderiv ℝ (F i) x (e i)⟫) + ρ x * ⟪b x (u x),v x⟫ ∂μ) = _
  have hsumi := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hsumj := integrable_finsetSum Finset.univ (fun i _ => hj i)
  have hneg : Integrable (fun x => -(∑ i, ⟪u x,fderiv ℝ (F i) x (e i)⟫)) μ := hsumi.neg
  rw [integral_add hneg hbi, integral_neg,integral_finsetSum _ (fun i _ => hi i),
    integral_add hsumj hbi,integral_finsetSum _ (fun i _ => hj i)]
  congr 1
  simp_rw [integral_inner_fderiv_on μ hU hu (hF _) hc hsub]
  simp

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Concentration_HodgeWeakResidual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open _root_.MeasureTheory MeasureTheory.Measure Set Filter
open scoped ContDiff Topology RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace W] [CompleteSpace Q] in
lemma differential_contDiffAt (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (u : V → W) {x : V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hu : ContDiffAt ℝ ∞ u x) :
    ContDiffAt ℝ ∞ (differential e a b u) x := by
  exact (ContDiffAt.sum (fun i _ => (ha i).clm_apply
    ((hu.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const))).add (hb.clm_apply hu)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma weightedAdjoint_contDiffAt (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (v : V → Q) {x : V}
    (ha : ∀ i, ContDiffAt ℝ ∞ (a i) x) (hb : ContDiffAt ℝ ∞ b x)
    (hρ : ContDiffAt ℝ ∞ ρ x) (hv : ContDiffAt ℝ ∞ v x) (hρ0 : ρ x ≠ 0) :
    ContDiffAt ℝ ∞ (weightedAdjoint e a b ρ v) x := by
  let Adj : (W →L[ℝ] Q) →L[ℝ] (Q →L[ℝ] W) :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  exact ((hρ.inv hρ0).neg.smul (ContDiffAt.sum (fun i _ =>
    ((((Adj.contDiff.contDiffAt.comp x (hρ.smul (ha i))).clm_apply hv).fderiv_right
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiffAt_const)))).add
        ((Adj.contDiff.contDiffAt.comp x hb).clm_apply hv)

variable (μ : Measure V) [IsAddHaarMeasure μ]
lemma integral_square_residual {U : Set V} (hU : IsOpen U)
    (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (k d r η : V → W)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U)
    (hρ : ContDiffOn ℝ ∞ ρ U) (hk : ContDiffOn ℝ ∞ k U)
    (hd : ∀ x ∈ tsupport η, ContinuousAt d x)
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hsub : tsupport η ⊆ U)
    (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hres : ∀ x ∈ tsupport η, d x + weightedAdjoint e a b ρ (differential e a b k) x = r x) :
    (∫ x, ρ x * ⟪η x,d x⟫ ∂μ) + (∫ x, ρ x * ⟪differential e a b η x,differential e a b k x⟫ ∂μ) =
      ∫ x, ρ x * ⟪η x,r x⟫ ∂μ := by
  have hat (i : ι) (x : V) (hx : x ∈ U) := (ha i x hx).contDiffAt (hU.mem_nhds hx)
  have hbt (x : V) (hx : x ∈ U) := (hb x hx).contDiffAt (hU.mem_nhds hx)
  have hρt (x : V) (hx : x ∈ U) := (hρ x hx).contDiffAt (hU.mem_nhds hx)
  have hkt (x : V) (hx : x ∈ U) := (hk x hx).contDiffAt (hU.mem_nhds hx)
  have hDt (x : V) (hx : x ∈ U) : ContDiffAt ℝ ∞ (differential e a b k) x :=
    differential_contDiffAt e a b k (fun i => hat i x hx) (hbt x hx) (hkt x hx)
  have hD : ContDiffOn ℝ ∞ (differential e a b k) U := fun x hx => (hDt x hx).contDiffWithinAt
  have hAt (x : V) (hx : x ∈ U) : ContDiffAt ℝ ∞ (weightedAdjoint e a b ρ (differential e a b k)) x :=
    weightedAdjoint_contDiffAt e a b ρ _ (fun i => hat i x hx) (hbt x hx) (hρt x hx)
      (hDt x hx) (hρ0 x hx)
  have hi : Integrable (fun x => ρ x * ⟪η x,d x⟫) μ := by
    have hh := integrable_inner_compact_local μ hη.continuous
      (fun x hx => (hρt x (hsub hx)).continuousAt.smul (hd x hx)) hc
    change Integrable (fun x => ⟪η x,ρ x • d x⟫) μ at hh
    simpa only [inner_smul_right] using hh
  have hj : Integrable (fun x => ρ x * ⟪η x,weightedAdjoint e a b ρ (differential e a b k) x⟫) μ := by
    have hh := integrable_inner_compact_local μ hη.continuous
      (fun x hx => (hρt x (hsub hx)).continuousAt.smul (hAt x (hsub hx)).continuousAt) hc
    change Integrable (fun x => ⟪η x,ρ x • weightedAdjoint e a b ρ (differential e a b k) x⟫) μ at hh
    simpa only [inner_smul_right] using hh
  rw [← integral_weightedAdjoint_on μ hU e a b ρ η (differential e a b k) ha hb hρ hη hD hc hsub
    (fun x hx => hρ0 x (hsub (subset_tsupport _ hx))),← integral_add hi hj]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ tsupport η
  · rw [← mul_add,← inner_add_right,hres x hx]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ239_TC.TamingCompatibility_Hodge_HodgeCompactExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open Set Filter
open scoped Manifold ContDiff Topology
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma exists_compact_smooth_extension {U K : Set V} (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) {f : V → W} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ g : V → W, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨O,hO,hKO,hOU,hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  have hKi : K ⊆ interior (closure O) := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hO.mem_nhds (hKO hx)) subset_closure)
  obtain ⟨φ,hφone,hφzero,_⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,V)) hK.isClosed hKi (n := ⊤)
  have hφsupp : tsupport (φ : V → ℝ) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (hφzero x hn)
  have hgsub : tsupport (fun x => φ x • f x) ⊆ closure O := by
    apply closure_minimal _ isClosed_closure
    intro x hx
    by_contra hn
    exact hx (by simp [hφzero x hn])
  refine ⟨fun x => φ x • f x,SchwartzCutoff.smooth hU hf
    (contMDiff_iff_contDiff.mp φ.contMDiff) (hφsupp.trans hOU),
    hOc.of_isClosed_subset (isClosed_tsupport _) hgsub,hgsub.trans hOU,?_⟩
  intro x hx
  filter_upwards [hφone.filter_mono (nhds_le_nhdsSet hx)] with y hy
  simp [hy]

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.OperatorCalculus
open _root_.MeasureTheory MeasureTheory.Measure Set Filter
open scoped ContDiff Topology RealInnerProductSpace
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
  [Fintype ι]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace W] [CompleteSpace Q] in
lemma differential_congr_nhds (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) {u v : V → W} {x : V} (h : u =ᶠ[𝓝 x] v) :
    differential e a b u x = differential e a b v x := by
  simp only [differential,h.fderiv_eq,h.eq_of_nhds]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompleteSpace W] [CompleteSpace Q] in
lemma differential_zero_off (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (u : V → W) {x : V} (hx : x ∉ tsupport u) :
    differential e a b u x = 0 := by
  have he : u =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isClosed_tsupport u).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [differential_congr_nhds e a b he]
  simp [differential]

variable (μ : Measure V) [IsAddHaarMeasure μ]
lemma integral_square_residual_local_oai {U K : Set V} (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (e : ι → V) (a : ι → V → W →L[ℝ] Q) (b : V → W →L[ℝ] Q)
    (ρ : V → ℝ) (k d r η : V → W)
    (ha : ∀ i, ContDiffOn ℝ ∞ (a i) U) (hb : ContDiffOn ℝ ∞ b U)
    (hρ : ContDiffOn ℝ ∞ ρ U) (hk : ContDiffOn ℝ ∞ k U)
    (hd : ContinuousOn d U) (hη : ContDiffOn ℝ ∞ η U)
    (hks : tsupport k ⊆ K) (hds : Function.support d ⊆ K) (hrs : Function.support r ⊆ K)
    (hρ0 : ∀ x ∈ U, ρ x ≠ 0)
    (hres : ∀ x ∈ U, d x + weightedAdjoint e a b ρ (differential e a b k) x = r x) :
    (∫ x, ρ x * ⟪η x,d x⟫ ∂μ) +
      (∫ x, ρ x * ⟪differential e a b η x,differential e a b k x⟫ ∂μ) =
      ∫ x, ρ x * ⟪η x,r x⟫ ∂μ := by
  obtain ⟨η',hη',hc,hsupp,he⟩ := exists_compact_smooth_extension hU hK hKU hη
  have hi := integral_square_residual μ hU e a b ρ k d r η' ha hb hρ hk
    (fun x hx => (hd x (hsupp hx)).continuousAt (hU.mem_nhds (hsupp hx)))
    hη' hc hsupp hρ0 (fun x hx => hres x (hsupp hx))
  have hid : (fun x => ρ x * ⟪η' x,d x⟫) = (fun x => ρ x * ⟪η x,d x⟫) := by
    funext x
    by_cases hx : x ∈ K
    · rw [(he x hx).eq_of_nhds]
    · have hz : d x = 0 := by by_contra hn; exact hx (hds hn)
      simp [hz]
  have hir : (fun x => ρ x * ⟪η' x,r x⟫) = (fun x => ρ x * ⟪η x,r x⟫) := by
    funext x
    by_cases hx : x ∈ K
    · rw [(he x hx).eq_of_nhds]
    · have hz : r x = 0 := by by_contra hn; exact hx (hrs hn)
      simp [hz]
  have hik : (fun x => ρ x * ⟪differential e a b η' x,differential e a b k x⟫) =
      (fun x => ρ x * ⟪differential e a b η x,differential e a b k x⟫) := by
    funext x
    by_cases hx : x ∈ K
    · rw [differential_congr_nhds e a b (he x hx)]
    · have hz := differential_zero_off e a b k (fun hh => hx (hks hh))
      simp [hz]
  rwa [hid,hir,hik] at hi

end TamingCompatibility.GeometricHilbert.OperatorCalculus

end
end

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.integral_square_residual_local_oai.{u_1, u_2, u_3, u_4} := @OAI.TamingCompatibility.GeometricHilbert.OperatorCalculus.integral_square_residual_local_oai.{u_1, u_2, u_3, u_4}
