-- Prove2me | solution 1 for OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:07:35.054864+00:00
-- url     : https://prove2.me/submissions/000c40cd-af17-4641-8202-ef6f6849a4e1

import Mathlib
import Definitions.Def_OAIQ059C006
import Definitions.Def_OAIQ059C007

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusFourierTranslation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

lemma mFourier_norm_one {d : Type*} [Fintype d] (h : d → ℤ)
    (x : UnitAddTorus d) : ‖mFourier h x‖=1 := by
  simp [mFourier,fourier_apply,norm_prod,Circle.norm_coe]

end

open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderJetOrthogonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cylinderJetMode_smooth {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) :
    cylinderJetMode R h (smoothAxisModeJet hq R h)=smoothCylinderModeJet hq R h := by
  ext j
  fin_cases j <;> rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CylinderPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cylinderPolynomialJetL_apply (R : ℝ) (p : TorusModes →₀ smoothComplexAxis) :
    cylinderPolynomialJetL R p=
      ∑ h∈p.support,smoothCylinderModeJet (smoothComplexAxis_smooth (p h)) R h := by
  rw [cylinderPolynomialJetL,Finsupp.lsum_apply]
  exact Finset.sum_congr rfl (fun h _ => cylinderJetMode_smooth _ R h)

open Set MeasureTheory Filter Topology
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderPoissonTrace
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma spectralTraceSingle_hasSum (s : Fin 3 → ℝ)
    (f : spectralTraceGraph (torusRate s)) :
    HasSum (fun h => spectralTraceSingleL s h (f.val 0 h)) f := by
  have hc (j : Fin 2) :
      HasSum (fun h => (spectralTraceSingleL s h (f.val 0 h)).val j) (f.val j) := by
    fin_cases j
    · exact lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) (f.val 0)
    · have H := lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) (f.val 1)
      convert H using 1
      · funext h
        change (lp.single 2 h ((Real.sqrt (torusRate s h):ℂ)*f.val 0 h) : SpectralL2 TorusModes)=lp.single 2 h (f.val 1 h)
        rw [f.property h]
      · rfl
  have ht : Tendsto (fun F : Finset TorusModes => fun j =>
        ∑ h∈F,(spectralTraceSingleL s h (f.val 0 h)).val j) atTop
      (𝓝 (fun j => f.val j)) := tendsto_pi_nhds.mpr hc
  have H := (PiLp.continuous_toLp 2 (fun _ : Fin 2 => SpectralL2 TorusModes)).continuousAt.tendsto.comp ht
  change Tendsto (fun F : Finset TorusModes => ∑ h∈F,spectralTraceSingleL s h (f.val 0 h)) atTop (𝓝 f)
  apply tendsto_subtype_rng.mpr
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext F
  apply PiLp.ext
  intro j
  simp only [Function.comp_apply,WithLp.ofLp_toLp,Submodule.coe_sum,WithLp.ofLp_sum,Finset.sum_apply]

lemma cylinderPolynomialJetL_single (R : ℝ) (h : TorusModes) (q : smoothComplexAxis) :
    cylinderPolynomialJetL R (Finsupp.single h q)=
      smoothCylinderModeJet (smoothComplexAxis_smooth q) R h := by
  rw [cylinderPolynomialJetL,Finsupp.lsum_single]
  exact cylinderJetMode_smooth _ R h

lemma cylinderPolynomialTraceL_single (s : Fin 3 → ℝ) (t : ℝ) (h : TorusModes)
    (q : smoothComplexAxis) :
    cylinderPolynomialTraceL s t (Finsupp.single h q)=spectralTraceSingleL s h (q t) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_single]
  rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceUniqueness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma squareFace_interior_unique (i k : Fin 4) {a b : ℝ} (ha : |a|<1)
    (he : squareFace i a=squareFace k b) : i=k := by
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have ha₁ := (abs_lt.mp ha).1
  have ha₂ := (abs_lt.mp ha).2
  fin_cases i <;> fin_cases k <;>
    simp [squareFace,squareFaceBase,squareFaceDirection] at h0 h1 ⊢ <;> linarith

lemma sourceCollarPiece_open_unique (i j k l : Fin 4) {x z : Fin 3 → ℝ}
    (hx : x∈sourceCollarOpenBox)
    (hz : z∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (he : sourceCollarPiece i j x=sourceCollarPiece k l z) : i=k ∧ j=l := by
  obtain ⟨hzt,hza,hzb⟩ := mem_sourceExtendedBox.mp hz
  have hx' := sourceCollarOpenBox_subset hx
  obtain ⟨hxt,hxa,hxb⟩ := mem_sourceExtendedBox.mp hx'
  have hxR : 0 < sourceCollarRadius j (x 0) (x 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended j hxt hxb).1
  have hzR : 0 < sourceCollarRadius l (z 0) (z 2) :=
    (by norm_num : (0:ℝ)<1/50).trans_le (sourceCollarRadius_extended l hzt hzb).1
  have hR : sourceCollarRadius j (x 0) (x 2)=sourceCollarRadius l (z 0) (z 2) := by
    have hh := congrArg sourceRadial he
    rwa [sourceCollarPiece_radial_pos i j hxR.le hxa,
      sourceCollarPiece_radial_pos k l hzR.le hza] at hh
  have ht : x 0=z 0 := by
    have hh := congrArg sourceCollarTime he
    rwa [sourceCollarPiece_time_pos i j hxR.le (by linarith [hxt.2]) hxa hxb,
      sourceCollarPiece_time_pos k l hzR.le (by linarith [hzt.2]) hza hzb] at hh
  constructor
  · apply squareFace_interior_unique i k hx.2.1
    have hh := congrArg (fun y : Fin 3 → ℝ => ![y 0/sourceLength,y 1]) he
    rw [sourceCollarPiece_angular,sourceCollarPiece_angular,←hR] at hh
    exact smul_right_injective (Fin 2 → ℝ) hxR.ne' hh
  · apply squareFace_interior_unique j l hx.2.2
    have hh := congrArg sourceCrossCoordinates he
    rw [sourceCollarPiece_cross_pos i j hxR.le hxa,
      sourceCollarPiece_cross_pos k l hzR.le hza,←ht] at hh
    exact smul_right_injective (Fin 2 → ℝ) (by linarith [hxt.2] : 1-x 0≠0) hh

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalTestEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma clm_eq_coordinate_dot (L : (Fin 3 → ℝ) →L[ℝ] ℝ) (v : Fin 3 → ℝ) :
    L v=(fun k => L (Pi.single k 1)) ⬝ᵥ v := by
  have hv : v=∑ k : Fin 3,v k • Pi.single k (1:ℝ) := by
    ext k
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum,map_smul,smul_eq_mul,dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma attachedFlatTestCovector_transport (φ : (Fin 3 → ℝ) → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) :
    attachedCartesianMatrix a i j x*ᵥattachedFlatTestCovector φ a i j x=
      physicalTestCovector φ (sourceCollarPiece i j x) := by
  rw [attachedFlatTestCovector,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (attachedCartesianMatrix_det_ne_zero ha i j hx)),Matrix.one_mulVec]

lemma physicalTestCovector_chain (φ : (Fin 3 → ℝ) → ℝ)
    (i j : Fin 4) (x : Fin 3 → ℝ)
    (hφ : DifferentiableAt ℝ φ (sourceCollarPiece i j x)) :
    physicalTestCovector (φ ∘ sourceCollarPiece i j) x=
      (sourceCollarJacobian i j x)ᵀ *ᵥ physicalTestCovector φ (sourceCollarPiece i j x) := by
  ext k
  rw [physicalTestCovector,(hφ.hasFDerivAt.comp x (sourceCollarPiece_hasFDeriv i j x)).fderiv]
  change fderiv ℝ φ (sourceCollarPiece i j x)
    (sourceCollarDerivative i j x (Pi.single k 1))=_
  change fderiv ℝ φ (sourceCollarPiece i j x)
    (sourceCollarJacobian i j x*ᵥPi.single k 1)=_
  rw [Matrix.mulVec_single_one,clm_eq_coordinate_dot]
  simp only [physicalTestCovector,Matrix.mulVec,Matrix.transpose_apply,dotProduct]
  apply Finset.sum_congr rfl
  intro q _
  simp [Matrix.col,mul_comm]

theorem attachedFlatTestCovector_chain (φ : (Fin 3 → ℝ) → ℝ) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    (hφ : DifferentiableAt ℝ φ (sourceCollarPiece i j x)) :
    physicalTestCovector (φ ∘ sourceCollarPiece i j) x=
      sourceFaceAngleMatrix i j x*ᵥ(endAxialMatrix a*ᵥattachedFlatTestCovector φ a i j x) := by
  rw [physicalTestCovector_chain φ i j x hφ,
    ←attachedFlatTestCovector_transport φ ha i j hx,attachedCartesianMatrix,
    ←Matrix.mulVec_mulVec,sourceCartesianGradient_chain i j hx]

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceExtendedBox_open_ae {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    ∀ᵐ x∂volume.restrict (sourceExtendedBox l r),x∈sourceCollarOpenBox := by
  let B := sourceExtendedBox (-(1:ℝ)/100) (1/100)
  have hB : volume (frontier B)=0 := (convex_Icc _ _).addHaar_frontier volume
  have hn : ∀ᵐ x : Fin 3 → ℝ,x∉frontier B := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using hB
  filter_upwards [ae_restrict_mem (show MeasurableSet (sourceExtendedBox l r) from measurableSet_Icc),
    ae_restrict_of_ae hn] with x hx hn
  have hxB : x∈B := by
    obtain ⟨ht,hi,hj⟩ := mem_sourceExtendedBox.mp hx
    exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,hi,hj⟩
  rw [sourceCollarOpenBox_eq_interior]
  by_contra h
  exact hn ⟨subset_closure hxB,h⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_FullWeakEndEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise ENNReal

lemma sourceCollarClosedPiece_measurable (l r : ℝ) (i j : Fin 4) :
    MeasurableSet (sourceCollarPiece i j '' sourceExtendedBox l r) :=
  (isCompact_Icc.image (sourceCollarPiece_contDiff i j).continuous).measurableSet

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularPeriodization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma AngularPeriodic.fderiv {T : ℝ} {f : Coord3 → E} (hf : AngularPeriodic T f) :
    AngularPeriodic T (fderiv ℝ f) := by
  intro n x
  have he : (fun y => f (y+angularShift T n))=f := funext (hf n)
  rw [←fderiv_comp_add_right,he]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusBoxFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

lemma integral_coord2_Icc {a b : Fin 2 → ℝ} (hab : a≤b) {f : (Fin 2 → ℝ) → ℝ}
    (hf : Continuous f) :
    (∫ x in Icc a b,f x)=∫ y in a 0..b 0,∫ z in a 1..b 1,f ![y,z] := by
  have hc : Continuous (fun q : ℝ×ℝ => f ![q.1,q.2]) := hf.comp (by fun_prop)
  have hi := hc.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1)))
  have he := (volume_preserving_finTwoArrow ℝ).setIntegral_image_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding (fun q : ℝ×ℝ => f ![q.1,q.2]) (Icc a b)
  have hid (x : Fin 2 → ℝ) : ![x 0,x 1]=x := by ext i; fin_cases i <;> rfl
  simp only [MeasurableEquiv.finTwoArrow_apply] at he
  simp_rw [hid] at he
  have him : MeasurableEquiv.finTwoArrow '' Icc a b=Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1) := by
    ext q
    rw [MeasurableEquiv.image_eq_preimage_symm]
    simp only [mem_preimage,mem_Icc,Pi.le_def,mem_prod]
    constructor
    · intro h
      exact ⟨⟨h.1 0,h.2 0⟩,⟨h.1 1,h.2 1⟩⟩
    · intro h
      constructor <;> intro i <;> fin_cases i
      · exact h.1.1
      · exact h.2.1
      · exact h.1.2
      · exact h.2.2
  change (∫ y in (MeasurableEquiv.finTwoArrow '' Icc a b),f ![y.1,y.2])=_ at he
  rw [←he,him]
  change (∫ x in Icc (a 0) (b 0) ×ˢ Icc (a 1) (b 1),f ![x.1,x.2] ∂volume.prod volume)=_
  rw [setIntegral_prod _ hi]
  simp_rw [intervalIntegral.integral_of_le (hab 0),intervalIntegral.integral_of_le (hab 1),
    ←integral_Icc_eq_integral_Ioc]

lemma integral_coord3_Icc {a b : Coord3} (hab : a≤b) {f : Coord3 → ℝ} (hf : Continuous f) :
    (∫ x in Icc a b,f x)=∫ t in a 0..b 0,∫ y in a 1..b 1,∫ z in a 2..b 2,f ![t,y,z] := by
  have hc : Continuous (fun q : ℝ×(ℝ×ℝ) => f ![q.1,q.2.1,q.2.2]) := hf.comp (by fun_prop)
  have hi := hc.continuousOn.integrableOn_compact (μ:=volume)
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
      IsCompact (Icc (a 0) (b 0) ×ˢ (Icc (a 1) (b 1) ×ˢ Icc (a 2) (b 2))))
  have he := threeArrow_volume.setIntegral_image_emb threeArrow.measurableEmbedding
    (fun q : ℝ×(ℝ×ℝ) => f ![q.1,q.2.1,q.2.2]) (Icc a b)
  simp only [threeArrow_apply] at he
  have hid (x : Coord3) : ![x 0,x 1,x 2]=x := by ext i; fin_cases i <;> rfl
  simp_rw [hid] at he
  have him : threeArrow '' Icc a b=Icc (a 0) (b 0) ×ˢ (Icc (a 1) (b 1) ×ˢ Icc (a 2) (b 2)) := by
    ext q
    rw [MeasurableEquiv.image_eq_preimage_symm]
    simp only [mem_preimage,mem_Icc,Pi.le_def,mem_prod,threeArrow_symm_apply]
    constructor
    · intro h
      exact ⟨⟨h.1 0,h.2 0⟩,⟨⟨h.1 1,h.2 1⟩,⟨h.1 2,h.2 2⟩⟩⟩
    · intro h
      constructor <;> intro i <;> fin_cases i
      · exact h.1.1
      · exact h.2.1.1
      · exact h.2.2.1
      · exact h.1.2
      · exact h.2.1.2
      · exact h.2.2.2
  change (∫ y in (threeArrow '' Icc a b),f ![y.1,y.2.1,y.2.2])=_ at he
  rw [←he,him]
  change (∫ x in Icc (a 0) (b 0) ×ˢ (Icc (a 1) (b 1) ×ˢ Icc (a 2) (b 2)),
    f ![x.1,x.2.1,x.2.2] ∂volume.prod volume)=_
  rw [setIntegral_prod _ hi]
  simp_rw [intervalIntegral.integral_of_le (hab 0),intervalIntegral.integral_of_le (hab 1),
    intervalIntegral.integral_of_le (hab 2),←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t _
  exact setIntegral_prod _ ((hc.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc))

lemma coordinateDivergence_eq_trace {F : Coord3 → Coord3} (hF : Differentiable ℝ F) (x : Coord3) :
    coordinateDivergence F x=∑ i : Fin 3,fderiv ℝ F x (Pi.single i 1) i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [(hasFDerivAt_pi'.mp (hF x).hasFDerivAt i).fderiv]
  rfl

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusFluxDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

lemma coordinateDivergence_smul_at {f : Coord3 → ℝ} {F : Coord3 → Coord3} {x : Coord3}
    (hf : DifferentiableAt ℝ f x) (hF : DifferentiableAt ℝ F x) :
    coordinateDivergence (fun y => f y • F y) x=
      f x*coordinateDivergence F x+fderiv ℝ f x (F x) := by
  have he (i : Fin 3) :
      fderiv ℝ (fun y => (f y • F y) i) x (Pi.single i 1)=
        f x*fderiv ℝ (fun y => F y i) x (Pi.single i 1)+
        F x i*fderiv ℝ f x (Pi.single i 1) := by
    change fderiv ℝ (fun y => f y*F y i) x _=_
    rw [fderiv_fun_mul hf ((hasFDerivAt_pi'.mp hF.hasFDerivAt i).differentiableAt)]
    rfl
  simp only [coordinateDivergence,he,Finset.sum_add_distrib,←Finset.mul_sum]
  rw [←coordinate_fderiv_expansion]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_WeakFluxClassicalC1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

lemma coordinateDivergence_C1_continuous {F : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) : Continuous (coordinateDivergence F) := by
  apply continuous_finsetSum
  intro i _
  exact (((contDiff_pi.mp hF) i).continuous_fderiv (by norm_num)).clm_apply continuous_const

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory

theorem torus_band_divergence_C1 {T a b : ℝ} (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} (hF : ContDiff ℝ 1 F) (hp : AngularPeriodic T F) :
    (∫ t in a..b,torusCellIntegral T (coordinateDivergence F) t)=
      torusCellIntegral T (fun x => F x 0) b-torusCellIntegral T (fun x => F x 0) a := by
  let A : Coord3 := ![a,0,0]
  let B : Coord3 := ![b,T,T]
  have hAB : A≤B := by intro i; fin_cases i; exact hab; exact hT; exact hT
  have hc := coordinateDivergence_C1_continuous hF
  have hfd := hF.differentiable (by norm_num)
  have hh := integral_divergence_of_hasFDerivAt_off_countable A B hAB F (fderiv ℝ F)
    ∅ countable_empty hF.continuous.continuousOn (fun x _ => (hfd x).hasFDerivAt)
    (by simpa only [←coordinateDivergence_eq_trace hfd] using (hc.continuousOn.integrableOn_compact
      (μ:=volume) (isCompact_Icc : IsCompact (Icc A B))))
  simp_rw [←coordinateDivergence_eq_trace hfd] at hh
  rw [integral_coord3_Icc hAB hc] at hh
  have h1 (q : Fin 2 → ℝ) : F ((1:Fin 3).insertNth T q) 1=F ((1:Fin 3).insertNth 0 q) 1 := by
    have he : ((1:Fin 3).insertNth 0 q)+angularShift T ![1,0]=(1:Fin 3).insertNth T q := by
      ext i; fin_cases i <;> simp [angularShift,Fin.insertNth,Fin.succAboveCases]
    have hh := hp ![1,0] ((1:Fin 3).insertNth 0 q)
    rw [he] at hh
    exact congrFun hh 1
  have h2 (q : Fin 2 → ℝ) : F ((2:Fin 3).insertNth T q) 2=F ((2:Fin 3).insertNth 0 q) 2 := by
    have he : ((2:Fin 3).insertNth 0 q)+angularShift T ![0,1]=(2:Fin 3).insertNth T q := by
      ext i; fin_cases i <;> simp [angularShift,Fin.insertNth,Fin.succAboveCases]
    have hh := hp ![0,1] ((2:Fin 3).insertNth 0 q)
    rw [he] at hh
    exact congrFun hh 2
  rw [Fin.sum_univ_succ] at hh
  simp only [Fin.sum_univ_two,Fin.succ_zero_eq_one,Fin.succ_one_eq_two] at hh
  simp only [A,B,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] at hh
  simp_rw [h1,h2] at hh
  simp only [sub_self,add_zero] at hh
  have hf0 (c : ℝ) :
      (∫ q in Icc (A ∘ (0:Fin 3).succAbove) (B ∘ (0:Fin 3).succAbove),
        F ((0:Fin 3).insertNth c q) 0)=torusCellIntegral T (fun x => F x 0) c := by
    have hc0 : Continuous (fun q : Fin 2 → ℝ => F ((0:Fin 3).insertNth c q) 0) :=
      (continuous_apply 0).comp (hF.continuous.comp (by fun_prop))
    refine (integral_coord2_Icc (a:=A ∘ (0:Fin 3).succAbove) (b:=B ∘ (0:Fin 3).succAbove) (fun i => hAB ((0:Fin 3).succAbove i)) hc0).trans ?_
    change (∫ y in (0:ℝ)..T,∫ z in (0:ℝ)..T,F ((0:Fin 3).insertNth c ![y,z]) 0)=_
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    have hi : (0:Fin 3).insertNth c ![y,z]=![c,y,z] := by
      ext i
      fin_cases i <;> simp [Fin.insertNth,Fin.succAboveCases]
    exact congrArg (fun x : Coord3 => F x 0) hi
  exact hh.trans (congrArg₂ (· - ·) (hf0 b) (hf0 a))

lemma coordinateDivergence_smul_scalar {F : Coord3 → Coord3} {φ : Coord3 → ℝ}
    {x : Coord3} (hF : DifferentiableAt ℝ F x) (hφ : DifferentiableAt ℝ φ x) :
    coordinateDivergence (fun y => φ y • F y) x=
      fderiv ℝ φ x (F x)+φ x*coordinateDivergence F x := by
  rw [coordinateDivergence_smul_at hφ hF]
  ring

theorem torus_band_green_C1 {T a b : ℝ} (hT : 0≤T) (hab : a≤b)
    {F : Coord3 → Coord3} {φ : Coord3 → ℝ}
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ)
    (hp : AngularPeriodic T F) (hφp : AngularPeriodic T φ)
    (hd : ∀ x,x 0∈Icc a b → coordinateDivergence F x=0) :
    (∫ t in a..b,torusCellIntegral T (fun x => fderiv ℝ φ x (F x)) t)=
      torusCellIntegral T (fun x => φ x*F x 0) b-
        torusCellIntegral T (fun x => φ x*F x 0) a := by
  have hprod : AngularPeriodic T (fun x => φ x • F x) := by
    intro n x
    change φ (x+angularShift T n) • F (x+angularShift T n)=φ x • F x
    rw [hφp n x,hp n x]
  have he := torus_band_divergence_C1 hT hab (hφ.smul hF) hprod
  refine Eq.trans ?_ he
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t∈Icc a b := by simpa only [uIcc_of_le hab] using ht
  unfold torusCellIntegral
  apply intervalIntegral.integral_congr
  intro y _
  apply intervalIntegral.integral_congr
  intro z _
  change fderiv ℝ φ ![t,y,z] (F ![t,y,z])=
    coordinateDivergence (fun x => φ x • F x) ![t,y,z]
  rw [coordinateDivergence_smul_scalar (hF.differentiable (by norm_num) _) (hφ.differentiable (by norm_num) _),
    hd _ ht',mul_zero,add_zero]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusDirectionalFourier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.torusDirectionalFourierMeasureSpace
local instance torusDirectionalFourierProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma torusCoordinateShift_add (j : Fin 2) (s t : ℝ) :
    torusCoordinateShift j (s+t)=torusCoordinateShift j s+torusCoordinateShift j t := by
  ext i
  by_cases hi : i=j <;> simp [torusCoordinateShift,hi]

theorem mFourierCoeff_of_directional_derivative
    (f : C(UnitAddTorus (Fin 2),ℂ)) (j : Fin 2) (K : ℝ) (hK : 0≤K)
    (hLip : ∀ t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤K*|t|)
    {d : UnitAddTorus (Fin 2) → ℂ} (hd : AEStronglyMeasurable d volume)
    (hder : ∀ᵐ θ : UnitAddTorus (Fin 2),
      HasDerivAt (fun t => f (θ+torusCoordinateShift j t)) (d θ) 0)
    (h : TorusModes) :
    mFourierCoeff d h = (2*Real.pi*Complex.I*(h j)) * mFourierCoeff f h := by
  let F : ℝ → UnitAddTorus (Fin 2) → ℂ := fun t θ =>
    mFourier (-h) θ * f (θ+torusCoordinateShift j t)
  have hFc (t : ℝ) : Continuous (F t) :=
    (mFourier (-h)).continuous.mul (f.continuous.comp (continuous_id.add continuous_const))
  have hFL : ∀ᵐ θ : UnitAddTorus (Fin 2),
      LipschitzOnWith (Real.nnabs K) (fun t => F t θ) univ := by
    apply Eventually.of_forall
    intro θ
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro t s
    have he : θ+torusCoordinateShift j t=
        (θ+torusCoordinateShift j s)+torusCoordinateShift j (t-s) := by
      rw [add_assoc,←torusCoordinateShift_add,add_sub_cancel]
    calc
      dist (F t θ) (F s θ)=‖f (θ+torusCoordinateShift j t)-f (θ+torusCoordinateShift j s)‖ := by
        rw [dist_eq_norm]
        simp only [F,←mul_sub,norm_mul,mFourier_norm_one,one_mul]
      _≤K*|t-s| := by rw [he]; exact hLip (t-s) (θ+torusCoordinateShift j s)
      _=(Real.nnabs K:ℝ)*dist t s := by rw [Real.coe_nnabs,abs_of_nonneg hK,Real.dist_eq]
  have hI := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ:=(volume : Measure (UnitAddTorus (Fin 2))))
    (F:=F) (F':=fun θ => mFourier (-h) θ*d θ)
    (s:=univ) (bound:=fun _ => K) (x₀:=(0:ℝ)) (univ_mem)
    (Eventually.of_forall fun t => (hFc t).aestronglyMeasurable)
    ((hFc 0).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((mFourier (-h)).continuous.aestronglyMeasurable.mul hd) hFL
    (integrable_const _) (hder.mono fun θ hθ => hθ.const_mul _)
  have he : (fun t => ∫ θ,F t θ) =
      fun t : ℝ => Complex.exp (2*Real.pi*Complex.I*(h j)*t)*mFourierCoeff f h := by
    funext t
    change mFourierCoeff (fun θ => f (θ+torusCoordinateShift j t)) h=_
    rw [mFourierCoeff_translation,mFourier_coordinateShift]
  rw [he] at hI
  have hE := ((((hasDerivAt_id (0:ℝ)).ofReal_comp).const_mul
    (2*Real.pi*Complex.I*(h j))).cexp).mul_const (mFourierCoeff f h)
  have heD := hI.2.unique hE
  simpa only [mFourierCoeff,smul_eq_mul,id_eq,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,Complex.ofReal_one,mul_one,one_mul] using heD

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_TorusDirectionalDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

lemma torusRealProjection_add (x y : TorusRealPlane) :
    torusRealProjection (x+y)=torusRealProjection x+torusRealProjection y := by
  ext j
  simp [torusRealProjection]

lemma torusRealProjection_direction (j : Fin 2) (t : ℝ) :
    torusRealProjection (t • Pi.single j (1:ℝ))=torusCoordinateShift j t := by
  ext i
  by_cases hij : i=j <;> simp [torusRealProjection,torusCoordinateShift,hij]

attribute [local instance] OAI.ScalarConductivity.torusDirectionalDerivativeMeasureSpace
local instance torusDirectionalDerivativeProbabilityMeasure_r4812a5_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma torusRealRepresentative_ae {P : TorusRealPlane → Prop}
    (h : ∀ᵐ x ∂(volume : Measure TorusRealPlane),P x) :
    ∀ᵐ θ : UnitAddTorus (Fin 2), P (torusRealRepresentative θ) := by
  let K : Set TorusRealPlane := {x | ∀ i,x i∈Ioc (0:ℝ) (0+1)}
  have hK : MeasurableSet K := MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  have hp := (measurePreserving_subtype_coe hK).comp
    (measurePreserving_equivPiIoc (fun _ : Fin 2 => (0:ℝ)))
  exact hp.quasiMeasurePreserving.ae (ae_restrict_of_ae h)

lemma torusDirectionalDerivative_eq (f : UnitAddTorus (Fin 2) → ℂ) (j : Fin 2)
    (θ : UnitAddTorus (Fin 2)) :
    torusDirectionalDerivative f j θ=deriv (fun t => f (θ+torusCoordinateShift j t)) 0 := by
  unfold torusDirectionalDerivative lineDeriv
  congr 2
  ext t
  change f (torusRealProjection (torusRealRepresentative θ+t • Pi.single j 1))=_
  rw [torusRealProjection_add,torusRealProjection_representative,torusRealProjection_direction]

lemma measurable_torusDirectionalDerivative {f : UnitAddTorus (Fin 2) → ℂ}
    (hf : Continuous f) (j : Fin 2) : Measurable (torusDirectionalDerivative f j) :=
  (measurable_lineDeriv (hf.comp continuous_torusRealProjection)).comp measurable_torusRealRepresentative

lemma torusDirectionalDerivative_ae (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|) (j : Fin 2) :
    ∀ᵐ θ : UnitAddTorus (Fin 2),
      HasDerivAt (fun t => f (θ+torusCoordinateShift j t)) (torusDirectionalDerivative f j θ) 0 := by
  have hd : ∀ᵐ x ∂(volume : Measure TorusRealPlane),
      DifferentiableAt ℝ (fun y => f (torusRealProjection y)) x :=
    (torusRealLift_lipschitz f K hLip).ae_differentiableAt
  filter_upwards [torusRealRepresentative_ae hd] with θ hθ
  have he (t : ℝ) : f (torusRealProjection (torusRealRepresentative θ+t • Pi.single j 1))=
      f (θ+torusCoordinateShift j t) := by
    rw [torusRealProjection_add,torusRealProjection_representative,torusRealProjection_direction]
  simpa only [HasLineDerivAt,he,torusDirectionalDerivative] using (hθ.lineDifferentiableAt (v:=Pi.single j 1)).hasLineDerivAt

theorem torusDirectionalDerivative_fourier (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|)
    (j : Fin 2) (h : TorusModes) :
    mFourierCoeff (torusDirectionalDerivative f j) h=
      (2*Real.pi*Complex.I*(h j))*mFourierCoeff f h :=
  mFourierCoeff_of_directional_derivative f j K K.coe_nonneg (hLip j)
    (measurable_torusDirectionalDerivative f.continuous j).aestronglyMeasurable
    (torusDirectionalDerivative_ae f K hLip j) h

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusPeriodicDescent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.torusPeriodicDescentMeasureSpace
local instance torusPeriodicDescentProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma torusPeriodicDescent_angles {f : Coord3 → E}
    (hp : AngularPeriodic (2*Real.pi) f) (x : Coord3) :
    torusPeriodicDescent f (x 0,torusAngles x)=f x := by
  change f ![x 0,2*Real.pi*torusRealRepresentative (torusAngles x) 0,
    2*Real.pi*torusRealRepresentative (torusAngles x) 1]=_
  apply hp.eq_of_angles
  · rfl
  rw [torusAngles_scaled,torusRealProjection_representative]

lemma integral_unitTorus_iterated_general [CompleteSpace E]
    {F : UnitAddTorus (Fin 2) → E} (hF : Continuous F) :
    (∫ θ,F θ)=∫ θ : UnitAddCircle,∫ η : UnitAddCircle,F ![θ,η]
      ∂AddCircle.haarAddCircle ∂AddCircle.haarAddCircle := by
  have hc : Continuous (MeasurableEquiv.finTwoArrow.symm :
      UnitAddCircle × UnitAddCircle → UnitAddTorus (Fin 2)) := by
    change Continuous (fun z : UnitAddCircle × UnitAddCircle => ![z.1,z.2])
    fun_prop
  rw [←(volume_preserving_finTwoArrow UnitAddCircle).symm.integral_comp']
  change (∫ z : UnitAddCircle × UnitAddCircle,F (MeasurableEquiv.finTwoArrow.symm z)
    ∂volume.prod volume)=_
  rw [integral_prod (fun z : UnitAddCircle × UnitAddCircle => F (MeasurableEquiv.finTwoArrow.symm z))
    ((hF.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  rfl

lemma integral_unitCircle_haar_interval {F : UnitAddCircle → E} :
    (∫ θ : UnitAddCircle,F θ ∂AddCircle.haarAddCircle)=∫ t in (0:ℝ)..1,F (t:UnitAddCircle) := by
  have h := (UnitAddCircle.intervalIntegral_preimage 0 F).symm
  simpa only [zero_add,unitCircle_volume_eq_haar] using h

lemma torusPeriodicDescent_integral {f : Coord3 → ℝ}
    (hf : Continuous f) (hp : AngularPeriodic (2*Real.pi) f) (t : ℝ) :
    (∫ θ,torusPeriodicDescent f (t,θ))=(2*Real.pi)⁻¹^2*torusCellIntegral (2*Real.pi) f t := by
  have hc : Continuous (fun θ => torusPeriodicDescent f (t,θ)) :=
    (continuous_torusPeriodicDescent hf hp).comp (continuous_const.prodMk continuous_id)
  rw [integral_unitTorus_iterated_general hc]
  rw [integral_unitCircle_haar_interval]
  have hπ : 2*Real.pi≠0 := by positivity
  have hi (x : ℝ) : (∫ θ : UnitAddCircle,torusPeriodicDescent f (t,![(x:UnitAddCircle),θ])
      ∂AddCircle.haarAddCircle)=
      (2*Real.pi)⁻¹*(∫ y in (0:ℝ)..(2*Real.pi),f ![t,2*Real.pi*x,y]) := by
    rw [integral_unitCircle_haar_interval]
    have he (y : ℝ) : torusPeriodicDescent f (t,![(x:UnitAddCircle),(y:UnitAddCircle)])=
        f ![t,2*Real.pi*x,2*Real.pi*y] := torusPeriodicDescent_real hp t ![x,y]
    simp_rw [he]
    rw [intervalIntegral.integral_comp_mul_left (fun y => f ![t,2*Real.pi*x,y]) hπ]
    simp
  simp_rw [hi]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left (fun x => ∫ y in (0:ℝ)..(2*Real.pi),f ![t,x,y]) hπ]
  simp only [mul_zero,mul_one,smul_eq_mul,torusCellIntegral]
  ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_SmoothCompactParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Metric

section CompactParameter
variable {E Q P G : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [TopologicalSpace P] [SecondCountableTopology P] [CompactSpace P]
  [MeasurableSpace P] [BorelSpace P]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  {μ : Measure P} [IsFiniteMeasure μ]

omit [CompleteSpace G] in
lemma hasDerivAt_compact_parameter {F D : ℝ × P → G}
    (hF : Continuous F) (hD : Continuous D)
    (hd : ∀ x p, HasDerivAt (fun y => F (y,p)) (D (x,p)) x) (x : ℝ) :
    HasDerivAt (fun y => ∫ p, F (y,p) ∂μ) (∫ p, D (x,p) ∂μ) x := by
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod (isCompact_univ : IsCompact (univ : Set P))).exists_bound_of_continuousOn
    hD.continuousOn
  have hFs (y : ℝ) : Continuous (fun p => F (y,p)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hDs (y : ℝ) : Continuous (fun p => D (y,p)) :=
    hD.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ:=μ) (F:=fun y p => F (y,p)) (F':=fun y p => D (y,p))
    (s:=closedBall x 1) (bound:=fun _ => C)
    (closedBall_mem_nhds x (by norm_num))
    (Eventually.of_forall fun y => (hFs y).aestronglyMeasurable)
    ((hFs x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hDs x).aestronglyMeasurable ?_ (integrable_const _) ?_).2
  · exact Eventually.of_forall (fun p y hy => hC (y,p) ⟨hy,mem_univ p⟩)
  · exact Eventually.of_forall (fun p y _ => hd y p)

end CompactParameter
end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.angularCoefficientMeasureSpace
attribute [local instance] OAI.ScalarConductivity.angularCoefficientProbabilityMeasure
lemma sourceAngularCoefficient_hasDerivAt {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) (h : TorusModes) (t : ℝ) :
    HasDerivAt (sourceAngularCoefficient f a b h)
      (mFourierCoeff (sourceAngularAxial f a b t) h) t := by
  have hF : Continuous (fun z : ℝ × UnitAddTorus (Fin 2) =>
      mFourier (-h) z.2 * (f (sourceAngularCollar (a*z.1+b) z.2) : ℂ)) := by
    apply ((mFourier (-h)).continuous.comp continuous_snd).mul
    exact Complex.continuous_ofReal.comp (hf.continuous.comp
      (contDiff_sourceAngularPolynomial_joint.continuous.comp
        ((continuous_const.mul continuous_fst |>.add continuous_const).prodMk
          (continuous_sourceRayCoordinates.comp continuous_snd))))
  have hD := ((mFourier (-h)).continuous.comp continuous_snd).mul
    (continuous_sourceAngularAxial hf a b)
  apply hasDerivAt_compact_parameter hF hD
  intro u θ
  have hg : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun v => f (sourceAngularCollar (a*v+b) θ)) :=
    hf.comp (contDiff_sourceAngularPolynomial_joint.comp
      ((contDiff_const.mul contDiff_id |>.add contDiff_const).prodMk contDiff_const))
  simpa only [sourceAngularAxial,Function.comp_def,Pi.mul_apply] using
    (((hg.differentiable (by simp)).differentiableAt (x:=u)).hasDerivAt.ofReal_comp).const_mul
      (mFourier (-h) θ)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal

attribute [local instance] OAI.ScalarConductivity.angularJetFiniteCylinderMeasureSpace
attribute [local instance] OAI.ScalarConductivity.angularJetFiniteCylinderProbabilityMeasure
lemma sourceAngularLpJet_ae {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (j : Fin 4) :
    sourceAngularLpJet hf a b R j =ᵐ[(FiniteAxisMeasure R).prod volume]
      sourceAngularJet f a b j :=
  (sourceAngularJet_memLp hf a b R j).coeFn_toLp

lemma mFourierCoeff_div_const (f : UnitAddTorus (Fin 2) → ℂ) (h : TorusModes) (c : ℂ) :
    mFourierCoeff (fun θ => f θ/c) h=mFourierCoeff f h/c := by
  simp only [mFourierCoeff,smul_eq_mul,←mul_div_assoc,integral_div]

lemma torusDirectionalDerivative_scaled_fourier (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|)
    (j : Fin 2) (h : TorusModes) :
    mFourierCoeff (fun θ => torusDirectionalDerivative f j θ/(2*Real.pi)) h=
      (Complex.I*(h j))*mFourierCoeff f h := by
  rw [mFourierCoeff_div_const,torusDirectionalDerivative_fourier f K hLip]
  have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

lemma sourceAngularJet_fourier {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (h : TorusModes)
    {t : ℝ} (ht : t∈Icc (0:ℝ) R) (j : Fin 4) :
    mFourierCoeff (fun θ => sourceAngularJet f a b j (t,θ)) h=
      ![sourceAngularCoefficient f a b h t,deriv (sourceAngularCoefficient f a b h) t,
        (Complex.I*(h 0))*sourceAngularCoefficient f a b h t,
        (Complex.I*(h 1))*sourceAngularCoefficient f a b h t] j := by
  obtain ⟨K,hK⟩ := sourceAngularTest_lipschitz hf a b R
  have ha (k : Fin 2) := torusDirectionalDerivative_scaled_fourier
    ⟨fun θ => sourceAngularTest f a b (t,θ),
      (continuous_sourceAngularTest hf a b).comp (continuous_const.prodMk continuous_id)⟩
    K (hK t ht) k h
  fin_cases j
  · rfl
  · exact (sourceAngularCoefficient_hasDerivAt hf a b h t).deriv.symm
  · exact ha 0
  · exact ha 1

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusCylinderGreenReal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.torusCylinderGreenRealMeasureSpaceUnitAddCircle
local instance torusCylinderGreenRealIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma continuous_memLp_finiteCylinder_general {E : Type*} [NormedAddCommGroup E]
    {f : ℝ × UnitAddTorus (Fin 2) → E} (hf : Continuous f) (R : ℝ) :
    MemLp f 2 ((FiniteAxisMeasure R).prod volume) := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a:=(0:ℝ)) (b:=R)).prod
    (isCompact_univ : IsCompact (univ : Set (UnitAddTorus (Fin 2))))).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [finiteCylinder_ae_mem R] with z hz
  exact hC z ⟨hz,mem_univ _⟩

lemma torusPeriodicDescent_cylinderIntegral {f : Coord3 → ℝ}
    (hf : Continuous f) (hp : AngularPeriodic (2*Real.pi) f) {R : ℝ} (hR : 0≤R) :
    (∫ z,torusPeriodicDescent f z ∂(FiniteAxisMeasure R).prod volume)=
      (2*Real.pi)⁻¹^2*(∫ t in (0:ℝ)..R,torusCellIntegral (2*Real.pi) f t) := by
  rw [integral_prod _ ((continuous_memLp_finiteCylinder_general
    (continuous_torusPeriodicDescent hf hp) R).integrable (by norm_num))]
  simp_rw [torusPeriodicDescent_integral hf hp]
  rw [integral_const_mul,intervalIntegral.integral_of_le hR]

theorem torusCylinder_green_real {R : ℝ} (hR : 0≤R)
    {F : Coord3 → Coord3} {φ : Coord3 → ℝ}
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ)
    (hp : AngularPeriodic (2*Real.pi) F) (hφp : AngularPeriodic (2*Real.pi) φ)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) :
    (∫ z,torusPeriodicDescent (fun x => fderiv ℝ φ x (F x)) z
      ∂(FiniteAxisMeasure R).prod volume)=
      (∫ θ,torusPeriodicDescent (fun x => φ x*F x 0) (R,θ))-
        (∫ θ,torusPeriodicDescent (fun x => φ x*F x 0) (0,θ)) := by
  have hc := (hφ.continuous_fderiv (by norm_num)).clm_apply hF.continuous
  have hdp : AngularPeriodic (2*Real.pi) (fun x => fderiv ℝ φ x (F x)) := by
    intro n x
    dsimp only
    rw [hφp.fderiv n x,hp n x]
  have hpc : Continuous (fun x => φ x*F x 0) := hφ.continuous.mul ((continuous_apply 0).comp hF.continuous)
  have hpp : AngularPeriodic (2*Real.pi) (fun x => φ x*F x 0) := by
    intro n x
    dsimp only
    rw [hφp n x,hp n x]
  rw [torusPeriodicDescent_cylinderIntegral hc hdp hR,
    torusPeriodicDescent_integral hpc hpp,torusPeriodicDescent_integral hpc hpp,
    torus_band_green_C1 (by positivity) hR hF hφ hp hφp hd,mul_sub]

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

variable {F : Coord3 → Coord3}

attribute [local instance] OAI.ScalarConductivity.torusCylinderGreenRealFluxMeasureSpaceUnitAddCircle
attribute [local instance] OAI.ScalarConductivity.torusCylinderGreenRealFluxIsProbabilityMeasure
lemma cylinderFluxLp_ae (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) (j : Fin 3) : cylinderFluxLp hF hp R j=ᵐ[(FiniteAxisMeasure R).prod volume]
      fun z => (torusPeriodicDescent F z j:ℂ) :=
  (continuous_memLp_finiteCylinder (continuous_torusFluxComponent hF hp j) R).coeFn_toLp

lemma cylinderFluxPairL_apply (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) (J : FiniteCylinderJets R) :
    cylinderFluxPairL hF hp R J=∑ j : Fin 3,inner ℂ (cylinderFluxLp hF hp R j) (J j.succ) := by
  simp [cylinderFluxPairL]

lemma cylinderFluxPairL_integral (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (R : ℝ) (J : FiniteCylinderJets R) :
    cylinderFluxPairL hF hp R J=
      ∫ z,∑ j : Fin 3,(torusPeriodicDescent F z j:ℂ)*J j.succ z ∂(FiniteAxisMeasure R).prod volume := by
  rw [cylinderFluxPairL_apply]
  simp_rw [L2.inner_def]
  rw [←integral_finsetSum _ (fun i _ => L2.integrable_inner (𝕜:=ℂ) _ _)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (cylinderFluxLp_ae hF hp R)] with z hz
  apply Finset.sum_congr rfl
  intro j _
  rw [hz j]
  simp [RCLike.inner_apply,mul_comm]

lemma torusFluxLp_ae (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F) (t : ℝ) :
    torusFluxLp hF hp t=ᵐ[volume] fun θ => (torusPeriodicDescent F (t,θ) 0:ℂ) :=
  ContinuousMap.coeFn_toLp volume _

lemma torusSpectralSynthesis_single (s : Fin 3 → ℝ) (h : TorusModes) (a : ℂ) :
    torusSpectralSynthesis s (spectralTraceSingleL s h a)=a • mFourierLp 2 h := by
  change (mFourierBasis (d:=Fin 2)).repr.symm (lp.single 2 h a)=_
  rw [show (a:ℂ)=a • (1:ℂ) by simp,lp.single_smul,map_smul,HilbertBasis.repr_symm_single]
  simp only [coe_mFourierBasis,smul_eq_mul,mul_one]

lemma torusFluxPairL_integral (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (s : Fin 3 → ℝ) (t : ℝ) (f : spectralTraceGraph (torusRate s)) :
    torusFluxPairL hF hp s t f=
      ∫ θ,(torusPeriodicDescent F (t,θ) 0:ℂ)*torusSpectralSynthesis s f θ := by
  change inner ℂ (torusFluxLp hF hp t) (torusSpectralSynthesis s f)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [torusFluxLp_ae hF hp t] with θ hθ
  rw [hθ]
  simp [RCLike.inner_apply,mul_comm]

lemma torusFluxPairL_single (hF : Continuous F) (hp : AngularPeriodic (2*Real.pi) F)
    (s : Fin 3 → ℝ) (t : ℝ) (h : TorusModes) (a : ℂ) :
    torusFluxPairL hF hp s t (spectralTraceSingleL s h a)=
      ∫ θ,(torusPeriodicDescent F (t,θ) 0:ℂ)*(a*mFourier h θ) := by
  rw [torusFluxPairL_integral,torusSpectralSynthesis_single]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul a (mFourierLp 2 h),coeFn_mFourierLp 2 h] with θ h1 h2
  rw [h1]
  simp only [Pi.smul_apply,smul_eq_mul,h2]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderFourierComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.cylinderFourierCompleteMeasureSpace
lemma cylinderCoefficient_fourier {μ : Measure ℝ} [SFinite μ]
    (q : lp (fun _ : TorusModes => Lp ℂ 2 μ) 2) (h : TorusModes) :
    cylinderCoefficientLp (cylinderFourier μ q) h = q h := by
  classical
  apply ext_inner_left ℂ
  intro f
  rw [←cylinderMode_inner_coefficient]
  have he : cylinderMode μ h f=cylinderFourier μ (lp.single 2 h f) :=
    ((cylinderMode_orthogonal μ).linearIsometry_apply_single f).symm
  rw [he,(cylinderFourier μ).inner_map_map,lp.inner_single_left]

lemma cylinderFourierEquiv_symm_apply {μ : Measure ℝ} [SFinite μ]
    (F : CylinderL2 μ) (h : TorusModes) :
    (cylinderFourierEquiv μ).symm F h = cylinderCoefficientLp F h := by
  have he := cylinderCoefficient_fourier ((cylinderFourierEquiv μ).symm F) h
  change cylinderCoefficientLp ((cylinderFourierEquiv μ) ((cylinderFourierEquiv μ).symm F)) h=_ at he
  simpa only [LinearIsometryEquiv.apply_symm_apply] using he.symm

theorem cylinderCoefficient_hasSum {μ : Measure ℝ} [SFinite μ] (F : CylinderL2 μ) :
    HasSum (fun h => cylinderMode μ h (cylinderCoefficientLp F h)) F := by
  have hh := cylinderFourier_hasSum μ ((cylinderFourierEquiv μ).symm F)
  simp only [cylinderFourierEquiv_symm_apply] at hh
  change HasSum _ ((cylinderFourierEquiv μ) ((cylinderFourierEquiv μ).symm F)) at hh
  simpa only [LinearIsometryEquiv.apply_symm_apply] using hh

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_CylinderFourierGraph
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma cylinderJetCoefficient_hasSum (R : ℝ) (J : FiniteCylinderJets R) :
    HasSum (fun h => cylinderJetMode R h (cylinderJetCoefficient R J h)) J := by
  have ht : Tendsto (fun F : Finset TorusModes => fun j =>
      ∑ h ∈ F,cylinderJetMode R h (cylinderJetCoefficient R J h) j)
      atTop (𝓝 (fun j => J j)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    exact cylinderCoefficient_hasSum (J j)
  have hmap := (PiLp.continuous_toLp 2 (fun _ : Fin 4 => CylinderL2 (FiniteAxisMeasure R))).continuousAt.tendsto.comp ht
  change Tendsto (fun F : Finset TorusModes => ∑ h ∈ F,cylinderJetMode R h (cylinderJetCoefficient R J h)) atTop _
  convert hmap using 1
  all_goals try with_reducible_and_instances rfl
  funext F
  apply PiLp.ext
  intro j
  simp only [Function.comp_apply,WithLp.ofLp_toLp,WithLp.ofLp_sum,Finset.sum_apply]

theorem cylinderGraph_of_smooth_coefficients (s : Fin 3 → ℝ) (R : ℝ)
    (J : FiniteCylinderJets R) (q : TorusModes → smoothComplexAxis)
    (hq : ∀ h,cylinderJetCoefficient R J h=smoothAxisModeJet (smoothComplexAxis_smooth (q h)) R h)
    (f₀ f₁ : spectralTraceGraph (torusRate s))
    (hf₀ : ∀ h,f₀.val 0 h=q h 0) (hf₁ : ∀ h,f₁.val 0 h=q h R) :
    (J,(f₀,f₁))∈cylinderSobolevGraph s R := by
  classical
  have hsum := cylinderJetCoefficient_hasSum R J
  simp only [hq,cylinderJetMode_smooth] at hsum
  have hg := hsum.prodMk ((spectralTraceSingle_hasSum s f₀).prodMk (spectralTraceSingle_hasSum s f₁))
  apply mem_closure_of_tendsto hg
  apply Eventually.of_forall
  intro F
  apply Submodule.sum_mem
  intro h _
  refine ⟨Finsupp.single h (q h),?_⟩
  change (cylinderPolynomialJetL R (Finsupp.single h (q h)),
      (cylinderPolynomialTraceL s 0 (Finsupp.single h (q h)),
      cylinderPolynomialTraceL s R (Finsupp.single h (q h))))=_
  rw [cylinderPolynomialJetL_single,cylinderPolynomialTraceL_single,cylinderPolynomialTraceL_single,hf₀,hf₁]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.angularGraphMeasureSpace
local instance angularGraphIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma smoothAxisModeJet_ae {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) (j : Fin 4) :
    (smoothAxisModeJet hq R h) j =ᵐ[FiniteAxisMeasure R]
      fun t => ![q t,deriv q t,(Complex.I*(h 0))*q t,(Complex.I*(h 1))*q t] j := by
  have hq₀ := smoothFiniteAxisLp_ae hq.continuous R
  have hq₁ := smoothFiniteAxisLp_ae (hq.continuous_deriv (by simp)) R
  have hq₂ := Lp.coeFn_smul (Complex.I*(h 0:ℂ)) (smoothFiniteAxisLp hq.continuous R)
  have hq₃ := Lp.coeFn_smul (Complex.I*(h 1:ℂ)) (smoothFiniteAxisLp hq.continuous R)
  fin_cases j
  · exact hq₀
  · exact hq₁
  · exact hq₂.trans (hq₀.mono fun t ht => by simp [ht,smul_eq_mul])
  · exact hq₃.trans (hq₀.mono fun t ht => by simp [ht,smul_eq_mul])

lemma sourceAngularLpJet_coefficient {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (h : TorusModes) :
    cylinderJetCoefficient R (sourceAngularLpJet hf a b R) h=
      smoothAxisModeJet (sourceAngularCoefficient_smooth hf a b h) R h := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [cylinderCoefficientLp_ae (sourceAngularLpJet hf a b R j) h,
    Measure.ae_ae_of_ae_prod (sourceAngularLpJet_ae hf a b R j),
    smoothAxisModeJet_ae (sourceAngularCoefficient_smooth hf a b h) R h j,
    ae_restrict_mem measurableSet_Ioc] with t ht₁ ht₂ ht₃ htm
  change cylinderCoefficientLp (sourceAngularLpJet hf a b R j) h t=_
  rw [ht₁,ht₃]
  calc
    cylinderCoefficient (sourceAngularLpJet hf a b R j) h t=
        mFourierCoeff (fun θ => sourceAngularJet f a b j (t,θ)) h := by
      unfold cylinderCoefficient mFourierCoeff
      apply integral_congr_ae
      filter_upwards [ht₂] with θ hθ
      rw [hθ]
    _=_ := sourceAngularJet_fourier hf a b R h (Ioc_subset_Icc_self htm) j

theorem sourceAngularLpJet_graph (s : Fin 3 → ℝ) {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) :
    (sourceAngularLpJet hf a b R,
      (smoothCollarTrace s b hf,smoothCollarTrace s (a*R+b) hf))∈cylinderSobolevGraph s R := by
  let q : TorusModes → smoothComplexAxis := fun h =>
    ⟨sourceAngularCoefficient f a b h,sourceAngularCoefficient_smooth hf a b h⟩
  apply cylinderGraph_of_smooth_coefficients s R _ q
    (sourceAngularLpJet_coefficient hf a b R) _ _
  · intro h
    rw [smoothCollarTrace_fst]
    simp [q,sourceAngularCoefficient]
  · intro h
    rw [smoothCollarTrace_fst]
    rfl

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

lemma hasDerivAt_outer_of_strict_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → E} {g : ℝ → ℝ} {x d : ℝ} {v : E}
    (hg : HasStrictDerivAt g d x) (hd : d≠0)
    (hF : HasDerivAt (F ∘ g) v x) : HasDerivAt F (d⁻¹ • v) (g x) := by
  let q := hg.localInverse g d x hd
  have hq : q (g x)=x := hg.eventually_left_inverse hd |>.self_of_nhds
  have h := hF.scomp_of_eq (g x) (hg.to_localInverse hd).hasDerivAt hq.symm
  apply h.congr_of_eventuallyEq
  filter_upwards [hg.eventually_right_inverse hd] with y hy
  exact congrArg F hy.symm

lemma hasStrictDerivAt_faceRayAngle (w : ℝ) (j : Fin 4) (b : ℝ) :
    HasStrictDerivAt (faceRayAngle w j) (faceRayDensity w j b) b :=
  hasStrictDerivAt_of_hasDerivAt_of_continuousAt
    (Filter.Eventually.of_forall fun x => hasDerivAt_faceRayAngle w j x)
    (continuous_faceRayDensity w j).continuousAt

lemma faceRayDensity_pos' {w : ℝ} (hw : 0<w) (j : Fin 4) (b : ℝ) :
    0<faceRayDensity w j b := by
  fin_cases j <;> dsimp [faceRayDensity] <;> positivity

lemma torusDirectionalDerivative_of_face (F : UnitAddTorus (Fin 2) → ℂ)
    (θ : UnitAddTorus (Fin 2)) (k : Fin 2) {w : ℝ} (hw : 0<w)
    (i : Fin 4) (b : ℝ) (v : ℂ)
    (hF : HasDerivAt (fun u => F (θ+torusCoordinateShift k
      (faceRayAngle w i u-faceRayAngle w i b))) v b) :
    torusDirectionalDerivative F k θ=(faceRayDensity w i b)⁻¹ • v := by
  have h := hasDerivAt_outer_of_strict_comp (F:=fun t => F (θ+torusCoordinateShift k t))
    ((hasStrictDerivAt_faceRayAngle w i b).sub_const (faceRayAngle w i b))
    (faceRayDensity_pos' hw i b).ne' hF
  simpa only [sub_self,torusDirectionalDerivative_eq] using h.deriv

lemma hasDerivAt_coordinate_update (x : Fin 3 → ℝ) (k : Fin 3) :
    HasDerivAt (fun u => Function.update x k u) (Pi.single k 1) (x k) := by
  apply hasDerivAt_pi.mpr
  intro l
  by_cases hl : l=k
  · subst l
    simp only [Function.update_self,Pi.single_eq_same]
    exact hasDerivAt_id' (x k)
  · simpa [Function.update_of_ne hl,Pi.single_apply,hl] using hasDerivAt_const (x k) (x l)

lemma physicalTestCovector_update {f : (Fin 3 → ℝ) → ℝ} {point : Fin 3 → ℝ}
    (hf : DifferentiableAt ℝ f point) (k : Fin 3) :
    HasDerivAt (fun u => f (Function.update point k u)) (physicalTestCovector f point k) (point k) := by
  simpa only [Function.update_eq_self,Function.comp_def,physicalTestCovector] using
    hf.hasFDerivAt.comp_hasDerivAt_of_eq (point k) (hasDerivAt_coordinate_update point k)
      (Function.update_eq_self k point).symm

lemma sourceAngularTest_face0 {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|<1) (h2 : |x 2|≤1) :
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 0
      (torusAngles (sourceFaceAngles i j x))=
      (faceRayDensity 1 i (x 1))⁻¹ •
        (physicalTestCovector (f ∘ sourceCollarPiece i j) x 1 : ℂ) := by
  apply torusDirectionalDerivative_of_face _ _ _ (by norm_num) i (x 1)
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 1).ofReal_comp
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ u in 𝓝 (x 1), |u|<1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds h1
  filter_upwards [hn] with u hu
  dsimp only [Function.comp_def,sourceAngularTest]
  congr 1
  rw [sourceFaceAngles_torus,hx]
  have he : ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
      ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)]+
      torusCoordinateShift 0 (faceRayAngle 1 i u-faceRayAngle 1 i (x 1))=
      ![((faceRayAngle 1 i u:ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)] := by
    ext k
    fin_cases k <;> simp [torusCoordinateShift]
  rw [he,sourceAngular_face _ _ _ _ _ hu.le h2]
  congr 2
  ext k
  fin_cases k <;> simp

lemma sourceAngularTest_face1 {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|≤1) (h2 : |x 2|<1) :
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 1
      (torusAngles (sourceFaceAngles i j x))=
      (faceRayDensity sourceRadialWidth j (x 2))⁻¹ •
        (physicalTestCovector (f ∘ sourceCollarPiece i j) x 2 : ℂ) := by
  apply torusDirectionalDerivative_of_face _ _ _ (by norm_num [sourceRadialWidth,sourceHole]) j (x 2)
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 2).ofReal_comp
  apply hd.congr_of_eventuallyEq
  have hn : ∀ᶠ u in 𝓝 (x 2), |u|<1 :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds h2
  filter_upwards [hn] with u hu
  dsimp only [Function.comp_def,sourceAngularTest]
  congr 1
  rw [sourceFaceAngles_torus,hx]
  have he : ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
      ((faceRayAngle sourceRadialWidth j (x 2):ℝ):UnitAddCircle)]+
      torusCoordinateShift 1 (faceRayAngle sourceRadialWidth j u-faceRayAngle sourceRadialWidth j (x 2))=
      ![((faceRayAngle 1 i (x 1):ℝ):UnitAddCircle),
        ((faceRayAngle sourceRadialWidth j u:ℝ):UnitAddCircle)] := by
    ext k
    fin_cases k <;> simp [torusCoordinateShift]
  rw [he,sourceAngular_face _ _ _ _ _ h1 hu.le]
  congr 2
  ext k
  fin_cases k <;> simp

lemma sourceAngularAxial_face {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|≤1) (h2 : |x 2|≤1) :
    sourceAngularAxial f a b t (torusAngles (sourceFaceAngles i j x))=
      (a*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0 : ℝ) := by
  have hd := (physicalTestCovector_update
    ((hf.differentiable (by simp)).differentiableAt.comp x
      (sourceCollarPiece_hasFDeriv i j x).differentiableAt) 0).comp_of_eq t
      (((hasDerivAt_id t).const_mul a).add_const b) hx.symm
  have he : (fun u => f (sourceAngularCollar (a*u+b) (torusAngles (sourceFaceAngles i j x))))=
      (fun u => (f ∘ sourceCollarPiece i j) (Function.update x 0 (a*u+b))) := by
    funext u
    dsimp only [Function.comp_def]
    rw [sourceFaceAngles_torus,sourceAngular_face _ _ _ _ _ h1 h2]
    congr 2
    ext k
    fin_cases k <;> simp
  unfold sourceAngularAxial
  rw [he]
  change ((deriv ((fun u => (f ∘ sourceCollarPiece i j) (Function.update x 0 u)) ∘
    (fun u => a*u+b)) t : ℝ) : ℂ)=_
  have hd' := hd.deriv
  simpa only [id_eq,mul_one,mul_comm] using congrArg Complex.ofReal hd'

theorem sourceAngularJet_face {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b t : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : a*t+b=x 0) (h1 : |x 1|<1) (h2 : |x 2|<1) :
    (fun k : Fin 3 => (sourceAngularJet f a b k.succ
      (t,torusAngles (sourceFaceAngles i j x))).re)=
      ![a*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0,
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1)),
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))] := by
  ext k
  fin_cases k
  · change (sourceAngularAxial f a b t (torusAngles (sourceFaceAngles i j x))).re=_
    exact congrArg Complex.re (sourceAngularAxial_face hf a b t i j hx h1.le h2.le)
  · change (torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 0
      (torusAngles (sourceFaceAngles i j x))/(2*Real.pi)).re=
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1))
    rw [sourceAngularTest_face0 hf a b t i j hx h1 h2.le]
    rw [Complex.real_smul]
    norm_cast
    ring
  · change (torusDirectionalDerivative (fun θ => sourceAngularTest f a b (t,θ)) 1
      (torusAngles (sourceFaceAngles i j x))/(2*Real.pi)).re=
        physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))
    rw [sourceAngularTest_face1 hf a b t i j hx h1.le h2]
    rw [Complex.real_smul]
    norm_cast
    ring

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_TorusSmoothModeJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

lemma torusAngles_shift (n : Fin 2 → ℤ) (x : Coord3) :
    torusAngles (x+angularShift (2*Real.pi) n)=torusAngles x := by
  have hπ : 2*Real.pi≠0 := by positivity
  ext i
  fin_cases i <;> simp [torusAngles,angularShift,add_div,hπ,mul_div_cancel_left₀]

lemma angularFrequency_apply (h : TorusModes) (x : Coord3) :
    angularFrequency h x=(torusAngular h x:ℂ)*Complex.I := by
  simp [angularFrequency,torusAngular]
  ring

lemma flatSmoothMode_eq (q : ℝ → ℂ) (h : TorusModes) (x : Coord3) :
    flatSmoothMode q h x=q (x 0)*mFourier h (torusAngles x) := by
  rw [flatSmoothMode,angularFrequency_apply,mFourier_torusAngles]

lemma flatSmoothMode_smooth {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (h : TorusModes) : ContDiff ℝ (↑(⊤:ℕ∞)) (flatSmoothMode q h) :=
  (hq.comp (contDiff_apply ℝ ℝ (0:Fin 3))).mul (angularFrequency h).contDiff.cexp

lemma flatSmoothMode_periodic (q : ℝ → ℂ) (h : TorusModes) :
    AngularPeriodic (2*Real.pi) (flatSmoothMode q h) := by
  intro n x
  rw [flatSmoothMode_eq,flatSmoothMode_eq,torusAngles_shift]
  simp [angularShift]

lemma flatSmoothMode_derivative {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (h : TorusModes) (x : Coord3) (j : Fin 3) :
    fderiv ℝ (flatSmoothMode q h) x (Pi.single j 1)=
      smoothModePointJet q h j.succ (x 0,torusAngles x) := by
  have hq' := ((hq.differentiable (by simp) (x 0)).hasDerivAt.hasFDerivAt).comp x (f:=fun y : Coord3 => y 0)
    ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Fin 3 => ℝ) 0).hasFDerivAt (x:=x))
  have he := ((angularFrequency h).hasFDerivAt (x:=x)).cexp
  have hd := hq'.mul he
  change HasFDerivAt (flatSmoothMode q h) _ x at hd
  rw [hd.fderiv]
  rw [smoothModePointJet,mFourier_torusAngles,←angularFrequency_apply]
  fin_cases j <;> simp [angularFrequency] <;> ring

attribute [local instance] OAI.ScalarConductivity.torusSmoothModeJetMeasureSpace
local instance torusSmoothModeJetIsProbabilityMeasure_r4812a5_1 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma smoothCylinderModeJet_ae {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q)
    (R : ℝ) (h : TorusModes) (j : Fin 4) :
    smoothCylinderModeJet hq R h j=ᵐ[(FiniteAxisMeasure R).prod volume]
      smoothModePointJet q h j := by
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ:=FiniteAxisMeasure R) (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae
      (smoothAxisModeJet_ae hq R h j)
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ:=FiniteAxisMeasure R) (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae
      (coeFn_mFourierLp 2 h)
  have hc : smoothCylinderModeJet hq R h j=
      cylinderTensor (smoothAxisModeJet hq R h j) (mFourierLp 2 h) := by
    fin_cases j <;> rfl
  rw [hc]
  filter_upwards [cylinderTensor_ae (smoothAxisModeJet hq R h j) (mFourierLp 2 h),h1,h2]
    with z hz ht hθ
  rw [hz,ht,hθ]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Flux_TorusCylinderGreenComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.torusCylinderGreenComplexMeasureSpaceUnitAddCircle
local instance torusCylinderGreenComplexIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem torusCylinder_green_complex {R : ℝ} (hR : 0≤R)
    {F : Coord3 → Coord3} {φ : Coord3 → ℂ}
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ)
    (hp : AngularPeriodic (2*Real.pi) F) (hφp : AngularPeriodic (2*Real.pi) φ)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) :
    (∫ z,torusPeriodicDescent (fun x => fderiv ℝ φ x (F x)) z
      ∂(FiniteAxisMeasure R).prod volume)=
      (∫ θ,torusPeriodicDescent (fun x => (F x 0) • φ x) (R,θ))-
        (∫ θ,torusPeriodicDescent (fun x => (F x 0) • φ x) (0,θ)) := by
  have hc := (hφ.continuous_fderiv (by norm_num)).clm_apply hF.continuous
  have hdp : AngularPeriodic (2*Real.pi) (fun x => fderiv ℝ φ x (F x)) := by
    intro n x
    dsimp only
    rw [hφp.fderiv n x,hp n x]
  have hpc : Continuous (fun x => (F x 0) • φ x) := ((continuous_apply 0).comp hF.continuous).smul hφ.continuous
  have hpp : AngularPeriodic (2*Real.pi) (fun x => (F x 0) • φ x) := by
    intro n x
    dsimp only
    rw [hφp n x,hp n x]
  have hi := (continuous_memLp_finiteCylinder_general
    (continuous_torusPeriodicDescent hc hdp) R).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hib (t : ℝ) : Integrable (fun θ => torusPeriodicDescent (fun x => (F x 0) • φ x) (t,θ)) :=
    ((continuous_torusPeriodicDescent hpc hpp).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hL (L : ℂ →L[ℝ] ℝ) :
      L (∫ z,torusPeriodicDescent (fun x => fderiv ℝ φ x (F x)) z
        ∂(FiniteAxisMeasure R).prod volume)=
      L ((∫ θ,torusPeriodicDescent (fun x => (F x 0) • φ x) (R,θ))-
        (∫ θ,torusPeriodicDescent (fun x => (F x 0) • φ x) (0,θ))) := by
    rw [map_sub,←L.integral_comp_comm hi,←L.integral_comp_comm (hib R),←L.integral_comp_comm (hib 0)]
    have hLp : AngularPeriodic (2*Real.pi) (fun x => L (φ x)) := by
      intro n x
      dsimp only
      rw [hφp n x]
    have he := torusCylinder_green_real hR hF (L.contDiff.comp hφ) hp hLp hd
    have hder (x : Coord3) : fderiv ℝ (fun y => L (φ y)) x=L.comp (fderiv ℝ φ x) :=
      (L.hasFDerivAt.comp x ((hφ.differentiable (by norm_num)) x).hasFDerivAt).fderiv
    simpa only [Function.comp_def,torusPeriodicDescent,hder,ContinuousLinearMap.comp_apply,map_smul,smul_eq_mul,mul_comm] using he
  exact Complex.ext (hL Complex.reCLM) (hL Complex.imCLM)

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus
open scoped ENNReal

lemma complex_coordinate_fderiv_expansion (φ : Coord3 → ℂ) (x v : Coord3) :
    fderiv ℝ φ x v=∑ j : Fin 3,(v j:ℂ)*fderiv ℝ φ x (Pi.single j 1) := by
  have he : v=∑ j : Fin 3,(v j) • (Pi.single j 1 : Coord3) := by
    ext i
    fin_cases i <;> simp [Pi.smul_apply,Pi.single_apply]
  conv_lhs => rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.real_smul]

local instance torusCylinderGreenComplexModeMeasureSpaceUnitAddCircle_r4812a5_1 : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
lemma torusFlux_mode_green {R : ℝ} (hR : 0≤R) (s : Fin 3 → ℝ)
    {F : Coord3 → Coord3} (hF : ContDiff ℝ 1 F)
    (hp : AngularPeriodic (2*Real.pi) F)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0)
    {q : ℝ → ℂ} (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (h : TorusModes) :
    cylinderFluxPairL hF.continuous hp R (smoothCylinderModeJet hq R h)=
      torusFluxPairL hF.continuous hp s R (spectralTraceSingleL s h (q R))-
      torusFluxPairL hF.continuous hp s 0 (spectralTraceSingleL s h (q 0)) := by
  have hh := torusCylinder_green_complex hR hF ((flatSmoothMode_smooth hq h).of_le (by simp))
    hp (flatSmoothMode_periodic q h) hd
  rw [cylinderFluxPairL_integral,torusFluxPairL_single,torusFluxPairL_single]
  convert hh using 1
  · apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (smoothCylinderModeJet_ae hq R h)] with z hz
    simp_rw [hz]
    simp only [torusPeriodicDescent]
    rw [complex_coordinate_fderiv_expansion]
    apply Finset.sum_congr rfl
    intro j _
    rw [flatSmoothMode_derivative hq]
    simp only [torusAngles_scaled,torusRealProjection_representative,Matrix.cons_val_zero]
  · congr 1 <;> apply integral_congr_ae <;> exact Filter.Eventually.of_forall (fun θ => by
      simp only [torusPeriodicDescent,flatSmoothMode_eq,torusAngles_scaled,
        torusRealProjection_representative,Matrix.cons_val_zero,Complex.real_smul])

lemma torusFluxPairL_polynomial {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) (s : Fin 3 → ℝ) (t : ℝ)
    (p : TorusModes →₀ smoothComplexAxis) :
    torusFluxPairL hF hp s t (cylinderPolynomialTraceL s t p)=
      ∑ h∈p.support,torusFluxPairL hF hp s t (spectralTraceSingleL s h (p h t)) := by
  rw [cylinderPolynomialTraceL,Finsupp.lsum_apply,Finsupp.sum,map_sum]
  rfl

theorem torusFlux_completed_green {R : ℝ} (hR : 0≤R) (s : Fin 3 → ℝ)
    {F : Coord3 → Coord3} (hF : ContDiff ℝ 1 F)
    (hp : AngularPeriodic (2*Real.pi) F)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0)
    (z : cylinderSobolevGraph s R) :
    cylinderFluxPairL hF.continuous hp R z.val.1=
      torusFluxPairL hF.continuous hp s R z.val.2.2-
      torusFluxPairL hF.continuous hp s 0 z.val.2.1 := by
  let J : CylinderTraceAmbient s R →L[ℂ] FiniteCylinderJets R := ContinuousLinearMap.fst ℂ _ _
  let T₀ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let T₁ : CylinderTraceAmbient s R →L[ℂ] spectralTraceGraph (torusRate s) :=
    (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
  let L := (cylinderFluxPairL hF.continuous hp R).comp J-
    (((torusFluxPairL hF.continuous hp s R).comp T₁)-
      ((torusFluxPairL hF.continuous hp s 0).comp T₀))
  have hr : LinearMap.range (cylinderPolynomialGraphL s R)≤L.ker := by
    rintro _ ⟨p,rfl⟩
    change cylinderFluxPairL hF.continuous hp R (cylinderPolynomialJetL R p)-
      (torusFluxPairL hF.continuous hp s R (cylinderPolynomialTraceL s R p)-
        torusFluxPairL hF.continuous hp s 0 (cylinderPolynomialTraceL s 0 p))=0
    rw [cylinderPolynomialJetL_apply,map_sum,torusFluxPairL_polynomial,torusFluxPairL_polynomial]
    simp_rw [torusFlux_mode_green hR s hF hp hd,Finset.sum_sub_distrib,sub_self]
  have hz := Submodule.topologicalClosure_minimal _ hr L.isClosed_ker z.property
  exact sub_eq_zero.mp hz

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AngularMeasureExact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped NNReal ENNReal

lemma continuous_faceRayCircle (w : ℝ) (j : Fin 4) :
    Continuous (fun b : ℝ => ((faceRayAngle w j b:ℝ):UnitAddCircle)) :=
  (AddCircle.continuous_mk' 1).comp
    (continuous_iff_continuousAt.mpr fun b => (hasDerivAt_faceRayAngle w j b).continuousAt)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_AffineCylinderIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.affineCylinderIntegralMeasureSpace
local instance affineCylinderIntegralProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma integrable_affineEndCoordinates {a b l r R : ℝ} (ha : a≠0)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Integrable F ((FiniteAxisMeasure R).prod volume)) :
    Integrable (F ∘ affineEndCoordinates a b) ((volume.restrict (Ioc l r)).prod volume) := by
  have hle := affineEndCoordinates_interval_le ha hT
  have hν : sourceCylinderMeasure 0 R=(FiniteAxisMeasure R).prod volume := by
    rfl
  have hμ : sourceCylinderMeasure l r=(volume.restrict (Ioc l r)).prod volume := by
    rfl
  rw [hν,hμ] at hle
  have h := (hF.smul_measure (c:=ENNReal.ofReal |a⁻¹|) ENNReal.ofReal_ne_top).mono_measure hle
  exact (integrable_map_measure h.aestronglyMeasurable
    (measurable_affineEndCoordinates a b).aemeasurable).mp h

lemma integral_affineEndCoordinates_pos {a b l r R : ℝ} (ha : 0<a) (hlr : l ≤ r)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hl : a*(l-b)=0) (hr : a*(r-b)=R) (hR : 0≤R)
    {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Integrable F ((FiniteAxisMeasure R).prod volume)) :
    |a| *(∫ z,F (affineEndCoordinates a b z) ∂(volume.restrict (Ioc l r)).prod volume)=
      ∫ z,F z ∂(FiniteAxisMeasure R).prod volume := by
  have hg := integrable_affineEndCoordinates ha.ne' hT hF
  rw [integral_prod (fun z => F (affineEndCoordinates a b z)) hg,integral_prod F hF,abs_of_pos ha,
    ←intervalIntegral.integral_of_le hlr,←intervalIntegral.integral_of_le hR]
  have he : (fun t => ∫ θ,F (affineEndCoordinates a b (t,θ)))=
      (fun t => (fun u => ∫ θ,F (u,θ)) (a*t-a*b)) := by
    funext t
    simp only [affineEndCoordinates,Prod.map_apply,affineEndTime,id_eq]
    rw [mul_sub]
  rw [he]
  change a • (∫ t in l..r,(fun u => ∫ θ,F (u,θ)) (a*t-a*b))=_
  rw [intervalIntegral.smul_integral_comp_mul_sub (fun u => ∫ θ,F (u,θ)) a (a*b)]
  rw [←mul_sub,←mul_sub,hl,hr]

lemma integral_affineEndCoordinates_neg {a b l r R : ℝ} (ha : a<0) (hlr : l ≤ r)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hl : a*(l-b)=R) (hr : a*(r-b)=0) (hR : 0≤R)
    {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Integrable F ((FiniteAxisMeasure R).prod volume)) :
    |a| *(∫ z,F (affineEndCoordinates a b z) ∂(volume.restrict (Ioc l r)).prod volume)=
      ∫ z,F z ∂(FiniteAxisMeasure R).prod volume := by
  have hg := integrable_affineEndCoordinates ha.ne hT hF
  rw [integral_prod (fun z => F (affineEndCoordinates a b z)) hg,integral_prod F hF,abs_of_neg ha,
    ←intervalIntegral.integral_of_le hlr,←intervalIntegral.integral_of_le hR]
  have he : (fun t => ∫ θ,F (affineEndCoordinates a b (t,θ)))=
      (fun t => (fun u => ∫ θ,F (u,θ)) (a*t-a*b)) := by
    funext t
    simp only [affineEndCoordinates,Prod.map_apply,affineEndTime,id_eq]
    rw [mul_sub]
  rw [he,neg_mul]
  change -(a • (∫ t in l..r,(fun u => ∫ θ,F (u,θ)) (a*t-a*b)))=_
  rw [intervalIntegral.smul_integral_comp_mul_sub (fun u => ∫ θ,F (u,θ)) a (a*b)]
  rw [←mul_sub,←mul_sub,hl,hr,intervalIntegral.integral_symm,neg_neg]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_AngularPhysicalTest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal

theorem sourceAngularJet_attachedCovector {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) {a : ℝ} (ha : a≠0) (b : ℝ) (i j : Fin 4)
    {x : Fin 3 → ℝ} (hx : x∈sourceCollarOpenBox) :
    (fun k : Fin 3 => (sourceAngularJet f a⁻¹ b k.succ
      (a*(x 0-b),torusAngles (sourceFaceAngles i j x))).re)=
      attachedFlatTestCovector f a i j x := by
  have h1 : |x 1|<1 := by exact hx.2.1
  have h2 : |x 2|<1 := by exact hx.2.2
  have ht : a⁻¹*(a*(x 0-b))+b=x 0 := by field_simp; ring
  rw [sourceAngularJet_face hf a⁻¹ b (a*(x 0-b)) i j ht h1 h2]
  have h := attachedFlatTestCovector_chain f ha i j (sourceCollarOpenBox_subset hx)
    ((hf.differentiable (by simp)).differentiableAt)
  have h0 := congrFun h 0
  have h1' := congrFun h 1
  have h2' := congrFun h 2
  simp only [sourceFaceAngleMatrix,endAxialMatrix,mulVec_diagonal] at h0 h1' h2'
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 0=
    1*(a*attachedFlatTestCovector f a i j x 0) at h0
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 1=
    (2*Real.pi*faceRayDensity 1 i (x 1))*(1*attachedFlatTestCovector f a i j x 1) at h1'
  change physicalTestCovector (f ∘ sourceCollarPiece i j) x 2=
    (2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))*(1*attachedFlatTestCovector f a i j x 2) at h2'
  ext k
  fin_cases k
  · change a⁻¹*physicalTestCovector (f ∘ sourceCollarPiece i j) x 0=_
    rw [h0]; field_simp [ha]; rfl
  · change physicalTestCovector (f ∘ sourceCollarPiece i j) x 1/(2*Real.pi*faceRayDensity 1 i (x 1))=_
    rw [h1']
    field_simp [(faceRayDensity_pos' (w:=1) (by norm_num) i (x 1)).ne',Real.pi_ne_zero]; rfl
  · change physicalTestCovector (f ∘ sourceCollarPiece i j) x 2/(2*Real.pi*faceRayDensity sourceRadialWidth j (x 2))=_
    rw [h2']
    field_simp [(faceRayDensity_pos' (w:=sourceRadialWidth) (by norm_num [sourceRadialWidth,sourceHole]) j (x 2)).ne',Real.pi_ne_zero]; rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FaceMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.sourceFaceMeasureCircleMeasureSpace
local instance sourceFaceMeasureCircleIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma continuous_sourceFaceParameter (i j : Fin 4) : Continuous (sourceFaceParameter i j) := by
  unfold sourceFaceParameter
  simp_rw [sourceFaceAngles_torus]
  apply (continuous_apply 0).prodMk
  apply continuous_pi
  intro k
  fin_cases k
  · exact (continuous_faceRayCircle 1 i).comp (continuous_apply 1)
  · exact (continuous_faceRayCircle sourceRadialWidth j).comp (continuous_apply 2)

lemma continuous_sourceFaceWeight (i j : Fin 4) : Continuous (sourceFaceWeight i j) :=
  ((continuous_faceRayDensity 1 i).comp (continuous_apply 1)).mul
    ((continuous_faceRayDensity sourceRadialWidth j).comp (continuous_apply 2))

lemma sourceFaceWeight_pos (i j : Fin 4) (x : Fin 3 → ℝ) : 0 < sourceFaceWeight i j x :=
  mul_pos (faceRayDensity_pos' (by norm_num) i (x 1))
    (faceRayDensity_pos' (by norm_num [sourceRadialWidth,sourceHole]) j (x 2))

instance finite_sourceFaceMeasure (l r : ℝ) (i j : Fin 4) :
    IsFiniteMeasure (sourceFaceMeasure l r i j) := by
  have h : IntegrableOn (sourceFaceWeight i j) (sourceExtendedBox l r) volume :=
    (continuous_sourceFaceWeight i j).continuousOn.integrableOn_compact isCompact_Icc
  have := isFiniteMeasure_withDensity_ofReal h.hasFiniteIntegral
  unfold sourceFaceMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

lemma integral_sourceFaceMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l r : ℝ) (i j : Fin 4) {F : ℝ × UnitAddTorus (Fin 2) → E}
    (hF : AEStronglyMeasurable F (sourceFaceMeasure l r i j)) :
    (∫ z,F z ∂sourceFaceMeasure l r i j)=
      ∫ x in sourceExtendedBox l r,sourceFaceWeight i j x • F (sourceFaceParameter i j x) := by
  rw [sourceFaceMeasure,integral_map (continuous_sourceFaceParameter i j).aemeasurable hF,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_sourceFaceWeight i j).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (sourceFaceWeight_pos i j x).le]

lemma integral_sourceFaceWeight_continuous {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (i j : Fin 4) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in sourceExtendedBox l r,sourceFaceWeight i j x * F (sourceFaceParameter i j x))=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,
        (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
          faceRayDensity 1 i a := by
  rw [integral_sourceExtendedBox (g:=fun x => sourceFaceWeight i j x * F (sourceFaceParameter i j x)) ((continuous_sourceFaceWeight i j).mul
    (hF.comp (continuous_sourceFaceParameter i j))) hlr]
  congr 1
  funext t
  congr 1
  funext a
  rw [←intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro b _
  simp only [sourceFaceWeight,sourceFaceParameter,sourceFaceAngles_torus,torusFaceTerm,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply]
  ring

lemma continuous_sourceFaceIntegral {F : ℝ × UnitAddTorus (Fin 2) → ℝ}
    (hF : Continuous F) (i j : Fin 4) :
    Continuous (fun t => ∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
        faceRayDensity 1 i a) := by
  apply continuous_parametric_unitInterval
  apply Continuous.mul
  · apply continuous_parametric_unitInterval
    unfold torusFaceTerm
    apply Continuous.mul
    · apply hF.comp
      apply continuous_fst.fst.prodMk
      apply continuous_pi
      intro k
      fin_cases k
      · exact (continuous_faceRayCircle 1 i).comp continuous_fst.snd
      · exact (continuous_faceRayCircle sourceRadialWidth j).comp continuous_snd
    · exact (continuous_faceRayDensity sourceRadialWidth j).comp continuous_snd
  · exact (continuous_faceRayDensity 1 i).comp continuous_snd

theorem sourceCylinderMeasure_eq_faces {l r : ℝ} (hlr : l ≤ r) :
    (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))=
      ∑ i : Fin 4,∑ j : Fin 4,sourceFaceMeasure l r i j := by
  have : ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro F
  have hi : Integrable (fun z => F z)
      ((volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2)))) := F.integrable
  rw [integral_prod _ hi,←intervalIntegral.integral_of_le hlr]
  rw [integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => F.integrable))]
  simp_rw [integral_finsetSum_measure (fun j _ => F.integrable)]
  have hh (i j : Fin 4) : (∫ z,F z ∂sourceFaceMeasure l r i j)=
      ∫ t in l..r,∫ a in (-1:ℝ)..1,
        (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
          faceRayDensity 1 i a := by
    rw [integral_sourceFaceMeasure (F:=fun z => F z) l r i j F.continuous.aestronglyMeasurable]
    exact integral_sourceFaceWeight_continuous F.continuous i j hlr
  simp_rw [hh]
  have he (t : ℝ) := integral_unitTorus_faces (w₀:=1) (w₁:=sourceRadialWidth)
    (F:=fun θ => F (t,θ)) (by norm_num) (by norm_num [sourceRadialWidth,sourceHole])
    (F.continuous.comp (continuous_const.prodMk continuous_id) : Continuous (fun θ => F (t,θ)))
  simp only [volume_pi,unitCircle_volume_eq_haar] at he
  trans ∫ t in l..r,∑ i : Fin 4,∑ j : Fin 4,∫ a in (-1:ℝ)..1,
      (∫ b in (-1:ℝ)..1,torusFaceTerm 1 sourceRadialWidth (fun θ => F (t,θ)) i j a b)*
        faceRayDensity 1 i a
  · apply intervalIntegral.integral_congr
    intro t _
    exact he t
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum _ (fun j _ => continuous_sourceFaceIntegral (F:=fun z => F z) F.continuous i j)).intervalIntegrable l r)]
  apply Finset.sum_congr rfl
  intro i _
  exact intervalIntegral.integral_finsetSum (fun j _ =>
    (continuous_sourceFaceIntegral (F:=fun z => F z) F.continuous i j).intervalIntegrable l r)

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FaceIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.sourceFaceIntegralCircleMeasureSpace
local instance sourceFaceIntegralCircleIsProbabilityMeasure_r4812a5_1 :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
lemma sourceFaceMeasure_le_cylinder {l r : ℝ} (hlr : l ≤ r) (i j : Fin 4) :
    sourceFaceMeasure l r i j ≤
      (volume.restrict (Ioc l r)).prod (volume : Measure (UnitAddTorus (Fin 2))) := by
  rw [sourceCylinderMeasure_eq_faces hlr]
  exact le_trans (Finset.single_le_sum (fun _ _ => Measure.zero_le _) (Finset.mem_univ j))
    (Finset.single_le_sum (f := fun face => ∑ patch,sourceFaceMeasure l r face patch)
      (fun _ _ => Measure.zero_le _) (Finset.mem_univ i))

lemma integrable_sourceFacePullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × UnitAddTorus (Fin 2) → E} {l r : ℝ} (hlr : l ≤ r)
    (hF : Integrable F ((volume.restrict (Ioc l r)).prod volume)) (i j : Fin 4) :
    IntegrableOn (fun x => sourceFaceWeight i j x • F (sourceFaceParameter i j x))
      (sourceExtendedBox l r) volume := by
  have hf := hF.mono_measure (sourceFaceMeasure_le_cylinder hlr i j)
  have hg := (integrable_map_measure hf.aestronglyMeasurable
    (continuous_sourceFaceParameter i j).aemeasurable).mp hf
  have hh := (integrable_withDensity_iff_integrable_smul'
    (continuous_sourceFaceWeight i j).measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mp hg
  simpa only [IntegrableOn,Function.comp_apply,ENNReal.toReal_ofReal (sourceFaceWeight_pos i j _).le] using hh

theorem integral_sourceCylinder_faces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ × UnitAddTorus (Fin 2) → E} {l r : ℝ} (hlr : l ≤ r)
    (hF : Integrable F ((volume.restrict (Ioc l r)).prod volume)) :
    (∫ z,F z ∂(volume.restrict (Ioc l r)).prod volume)=
      ∑ i : Fin 4,∑ j : Fin 4,∫ x in sourceExtendedBox l r,
        sourceFaceWeight i j x • F (sourceFaceParameter i j x) := by
  have hf (i j : Fin 4) := hF.mono_measure (sourceFaceMeasure_le_cylinder hlr i j)
  rw [sourceCylinderMeasure_eq_faces hlr,integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => hf i j))]
  simp_rw [integral_finsetSum_measure (fun j _ => hf _ j)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact integral_sourceFaceMeasure l r i j (hf i j).aestronglyMeasurable

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FacePasting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Matrix

variable {E : Type*}

lemma sourceFacePasteList_local (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (y : Coord3)
    (hy : ∃ k∈ks,y∈sourceFlatPatch k.1 k.2) :
    ∃ k∈ks,y∈sourceFlatPatch k.1 k.2 ∧ sourceFacePasteList B v ks y=B k.1 k.2 y := by
  classical
  induction ks with
  | nil => simp at hy
  | cons k ks ih =>
    by_cases hk : y∈sourceFlatPatch k.1 k.2
    · exact ⟨k,List.mem_cons_self,hk,by rw [sourceFacePasteList_cons,ite_eq_left hk]⟩
    · obtain ⟨l,hl,hly⟩ := hy
      have hl' : l∈ks := (List.mem_cons.mp hl).resolve_left (by rintro rfl; exact hk hly)
      obtain ⟨l,hl,hly,he⟩ := ih ⟨l,hl',hly⟩
      exact ⟨l,List.mem_cons_of_mem _ hl,hly,by rw [sourceFacePasteList_cons,ite_eq_right hk,he]⟩

lemma sourceFacePasteList_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (ks : List (Fin 4 × Fin 4)) (i j : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (hk : (i,j)∈ks) :
    sourceFacePasteList B v ks (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) := by
  obtain ⟨k,_,hy,he⟩ := sourceFacePasteList_local B v ks _
    ⟨(i,j),hk,⟨x,sourceCollarOpenBox_subset hx,rfl⟩⟩
  obtain ⟨z,hz,hze⟩ := hy
  obtain ⟨hi,hj⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx hz hze.symm
  simpa only [←hi,←hj] using he

lemma sourceFacePaste_open (B : Fin 4 → Fin 4 → Coord3 → E) (v : E)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    sourceFacePaste B v (sourceCollarPiece i j x)=B i j (sourceCollarPiece i j x) :=
  sourceFacePasteList_open B v _ i j hx (by simp)

lemma flatEndCoordinates_angles (a b : ℝ) (x : Coord3) :
    torusAngles (flatEndCoordinates a b x)=torusAngles x := rfl

lemma flatEndCoordinates_axial (a b : ℝ) (x : Coord3) :
    flatEndCoordinates a b x 0=a*(x 0-b) := rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sources_FluxCylinder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal
attribute [local instance] OAI.ScalarConductivity.sourceFluxCylinderMeasureSpace
local instance sourceFluxCylinderIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma cylinderFluxPairL_integrable {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) (R : ℝ) (J : FiniteCylinderJets R) :
    Integrable (fun z => ∑ j : Fin 3,(torusPeriodicDescent F z j:ℂ)*J j.succ z)
      ((FiniteAxisMeasure R).prod volume) := by
  have hi := integrable_finsetSum (μ:=(FiniteAxisMeasure R).prod volume) Finset.univ
    (fun j _ => L2.integrable_inner (𝕜:=ℂ) (cylinderFluxLp hF hp R j) (J j.succ))
  apply hi.congr
  filter_upwards [ae_all_iff.mpr (cylinderFluxLp_ae hF hp R)] with z hz
  apply Finset.sum_congr rfl
  intro j _
  rw [hz j]
  simp [RCLike.inner_apply,mul_comm]

lemma sourceFluxDensity_cylinder {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) (a b R : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    Integrable (sourceFluxDensity F a b φ) ((FiniteAxisMeasure R).prod volume) ∧
    (∫ z,sourceFluxDensity F a b φ z ∂(FiniteAxisMeasure R).prod volume)=
      (cylinderFluxPairL hF hp R (sourceAngularLpJet hφ a b R)).re := by
  let G := fun z => ∑ j : Fin 3,(torusPeriodicDescent F z j:ℂ)*sourceAngularLpJet hφ a b R j.succ z
  have hi : Integrable G ((FiniteAxisMeasure R).prod volume) :=
    cylinderFluxPairL_integrable hF hp R (sourceAngularLpJet hφ a b R)
  have he : (fun z => (G z).re)=ᵐ[(FiniteAxisMeasure R).prod volume] sourceFluxDensity F a b φ := by
    filter_upwards [ae_all_iff.mpr (sourceAngularLpJet_ae hφ a b R)] with z hz
    simp only [G,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,hz,sourceFluxDensity,dotProduct]
  refine ⟨hi.re.congr he,?_⟩
  rw [cylinderFluxPairL_integral]
  exact (integral_congr_ae he).symm.trans (Complex.reCLM.integral_comp_comm hi)

lemma torusSpectralSynthesis_smoothCollar_ae (s : Fin 3 → ℝ) (b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    torusSpectralSynthesis s (smoothCollarTrace s b hφ)=ᵐ[volume]
      fun θ => (φ (sourceAngularCollar b θ):ℂ) := by
  have he : (smoothCollarTrace s b hφ).val 0=smoothCollarTraceFourier b hφ := by
    apply lp.ext
    funext h
    rw [smoothCollarTrace_fst,smoothCollarTraceFourier_apply]
  change (mFourierBasis (d:=Fin 2)).repr.symm ((smoothCollarTrace s b hφ).val 0)=ᵐ[volume] _
  rw [he,smoothCollarTraceFourier,LinearIsometryEquiv.symm_apply_apply]
  exact ContinuousMap.coeFn_toLp volume _

lemma torusFluxPairL_smoothCollar {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) (s : Fin 3 → ℝ) (t b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (torusFluxPairL hF hp s t (smoothCollarTrace s b hφ)).re=
      ∫ θ,torusPeriodicDescent F (t,θ) 0*φ (sourceAngularCollar b θ) := by
  rw [torusFluxPairL_integral]
  have hc : Continuous (fun θ => (torusPeriodicDescent F (t,θ) 0:ℂ)*(φ (sourceAngularCollar b θ):ℂ)) :=
    ((continuous_torusFluxComponent hF hp 0).comp (continuous_const.prodMk continuous_id)).mul
      (Complex.continuous_ofReal.comp (hφ.continuous.comp (continuous_sourceAngularCollar b)))
  have he : (∫ θ,(torusPeriodicDescent F (t,θ) 0:ℂ)*torusSpectralSynthesis s (smoothCollarTrace s b hφ) θ)=
      ∫ θ,(torusPeriodicDescent F (t,θ) 0:ℂ)*(φ (sourceAngularCollar b θ):ℂ) := by
    apply integral_congr_ae
    filter_upwards [torusSpectralSynthesis_smoothCollar_ae s b hφ] with θ hθ
    rw [hθ]
  rw [he]
  simpa using (Complex.reCLM.integral_comp_comm (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))).symm

theorem sourceFluxDensity_green {F : Coord3 → Coord3} (hF : ContDiff ℝ 1 F)
    (hp : AngularPeriodic (2*Real.pi) F) {R : ℝ} (hR : 0≤R)
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) (a b : ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ z,sourceFluxDensity F a b φ z ∂(FiniteAxisMeasure R).prod volume)=
      (∫ θ,torusPeriodicDescent F (R,θ) 0*φ (sourceAngularCollar (a*R+b) θ))-
      (∫ θ,torusPeriodicDescent F (0,θ) 0*φ (sourceAngularCollar b θ)) := by
  let s : Fin 3 → ℝ := ![1,0,1]
  rw [(sourceFluxDensity_cylinder hF.continuous hp a b R hφ).2]
  have hh := torusFlux_completed_green hR s hF hp hd
    ⟨(_,(_,_)),sourceAngularLpJet_graph s hφ a b R⟩
  rw [hh,Complex.sub_re,torusFluxPairL_smoothCollar,torusFluxPairL_smoothCollar]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_PhysicalFaceSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceExtendedBox_mono {l r l' r' : ℝ} (hl : l'≤l) (hr : r ≤ r') :
    sourceExtendedBox l r ⊆ sourceExtendedBox l' r' := by
  intro x hx
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  exact mem_sourceExtendedBox.mpr ⟨⟨hl.trans ht.1,ht.2.trans hr⟩,ha,hb⟩

lemma sourceCollarPieces_aedisjoint {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    Pairwise (fun k m : Fin 4 × Fin 4 => AEDisjoint volume
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r)
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r)) := by
  intro k m hkm
  have hn : ∀ᵐ y : Fin 3 → ℝ, y∉
      (sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r) ∩
      (sourceCollarPiece m.1 m.2 '' sourceExtendedBox l r) := by
    filter_upwards [sourceCollar_open_charts_ae] with y hy hm
    obtain ⟨⟨z,hz,hzy⟩,w,hw,hwy⟩ := hm
    have hyb := sourceCollarClosedPiece_subset (l:=-(1:ℝ)/100) (r:=1/100)
      le_rfl le_rfl k.1 k.2 ⟨z,sourceExtendedBox_mono hl hr hz,hzy⟩
    obtain ⟨i,j,x,hx,hxy⟩ := hy hyb
    obtain ⟨hik,hjk⟩ := sourceCollarPiece_open_unique i j k.1 k.2 hx
      (sourceExtendedBox_mono hl hr hz) (hxy.trans hzy.symm)
    obtain ⟨him,hjm⟩ := sourceCollarPiece_open_unique i j m.1 m.2 hx
      (sourceExtendedBox_mono hl hr hw) (hxy.trans hwy.symm)
    exact hkm (Prod.ext (hik.symm.trans him) (hjk.symm.trans hjm))
  simpa only [AEDisjoint,ae_iff,not_not,Set.ofPred_mem_eq] using hn

theorem sourceClosedCollarBand_measure_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    volume.restrict (sourceClosedCollarBand l r)=
      ∑ i : Fin 4,∑ j : Fin 4,
        volume.restrict (sourceCollarPiece i j '' sourceExtendedBox l r) := by
  rw [sourceClosedCollarBand_eq l r hl hr]
  have he : (⋃ i : Fin 4,⋃ j : Fin 4,sourceCollarPiece i j '' sourceExtendedBox l r)=
      ⋃ k : Fin 4 × Fin 4,sourceCollarPiece k.1 k.2 '' sourceExtendedBox l r := by
    ext x
    simp
  rw [he,Measure.restrict_iUnion_ae (sourceCollarPieces_aedisjoint hl hr)
    (fun k => (sourceCollarClosedPiece_measurable l r k.1 k.2).nullMeasurableSet),
    Measure.sum_fintype,Fintype.sum_prod_type]

lemma integral_sourceClosedCollarBand_faces {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) {F : (Fin 3 → ℝ) → ℝ}
    (hF : IntegrableOn F (sourceClosedCollarBand l r) volume) :
    (∫ y in sourceClosedCollarBand l r,F y)=
      ∑ i : Fin 4,∑ j : Fin 4,
        ∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,F y := by
  have hi (i j : Fin 4) := hF.mono_set (sourceCollarClosedPiece_subset hl hr i j)
  rw [sourceClosedCollarBand_measure_faces hl hr,integral_finsetSum_measure (fun i _ =>
    integrable_finsetSum_measure.mpr (fun j _ => hi i j))]
  simp_rw [integral_finsetSum_measure (fun j _ => hi _ j)]

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AttachedPeriodicFlux
attribute [-instance] _root_.OAI.ScalarConductivity.instBorelSpaceSymmetric3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal

lemma inverseTranspose_flux_pair (A : Mat3) (hA : A.det≠0) (v w : Coord3) :
    (A⁻¹ᵀ*ᵥv) ⬝ᵥ(A*ᵥw)=v ⬝ᵥw := by
  rw [dotProduct_comm,Matrix.dotProduct_transpose_mulVec,Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),Matrix.one_mulVec]

lemma attachedPeriodicFlux_open (F : Coord3 → Coord3) (a b : ℝ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    attachedPeriodicFlux F a b (sourceCollarPiece i j x)=
      (|a| *sourceFlatDensity i j x) • ((attachedCartesianMatrix a i j x)⁻¹ᵀ*ᵥ
        F (flatEndCoordinates a b (sourceFaceAngles i j x))) := by
  rw [attachedPeriodicFlux,sourceFacePaste_open _ _ i j hx]
  simp only [attachedPeriodicFluxFace,sourceCollarInverse_point i j hx]

lemma attachedPeriodicFlux_test_density {F : Coord3 → Coord3}
    (hp : AngularPeriodic (2*Real.pi) F) {a b : ℝ} (ha : a≠0)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) :
    |(sourceCollarJacobian i j x).det| *
      (attachedPeriodicFlux F a b (sourceCollarPiece i j x) ⬝ᵥ
        physicalTestCovector φ (sourceCollarPiece i j x))=
      (|a| *angularArea)*(sourceFaceWeight i j x*
        sourceFluxDensity F a⁻¹ b φ (affineEndCoordinates a b (sourceFaceParameter i j x))) := by
  rw [attachedPeriodicFlux_open F a b i j hx,
    ←attachedFlatTestCovector_transport φ ha i j (sourceCollarOpenBox_subset hx),smul_dotProduct,
    inverseTranspose_flux_pair _ (attachedCartesianMatrix_det_ne_zero ha i j (sourceCollarOpenBox_subset hx))]
  have hp' : torusPeriodicDescent F (affineEndCoordinates a b (sourceFaceParameter i j x))=
      F (flatEndCoordinates a b (sourceFaceAngles i j x)) := by
    simpa only [flatEndCoordinates_axial,flatEndCoordinates_angles,affineEndCoordinates,
      Prod.map_apply,affineEndTime,id_eq,sourceFaceParameter,show sourceFaceAngles i j x 0=x 0 from rfl] using
      torusPeriodicDescent_angles hp (flatEndCoordinates a b (sourceFaceAngles i j x))
  simp only [sourceFluxDensity,hp']
  have hj := sourceAngularJet_attachedCovector hφ ha b i j hx
  change (fun k : Fin 3 => (sourceAngularJet φ a⁻¹ b k.succ
    (affineEndCoordinates a b (sourceFaceParameter i j x))).re)=attachedFlatTestCovector φ a i j x at hj
  rw [hj,smul_eq_mul,sourceFlatDensity,sourceFaceWeight,sourceFaceAngleMatrix_det]
  field_simp [abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j (sourceCollarOpenBox_subset hx))]

attribute [local instance] OAI.ScalarConductivity.attachedPeriodicFluxMeasureSpace
local instance attachedPeriodicFluxIsProbabilityMeasure_r4812a5_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem attachedPeriodicFlux_smooth_pullback {F : Coord3 → Coord3} (hF : Continuous F)
    (hp : AngularPeriodic (2*Real.pi) F) {φ : Coord3 → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) {a b l r R : ℝ} (ha : a≠0)
    (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) :
    IntegrableOn (fun y => attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)
      (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)=
      |a| *angularArea*(∫ z,sourceFluxDensity F a⁻¹ b φ (affineEndCoordinates a b z)
        ∂(volume.restrict (Ioc l r)).prod volume) := by
  let H := sourceFluxDensity F a⁻¹ b φ
  let G := fun y => attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y
  have hH := (sourceFluxDensity_cylinder hF hp a⁻¹ b R hφ).1
  have hg := integrable_affineEndCoordinates ha hT hH
  have he (i j : Fin 4) :
      (fun x => |(sourceCollarDerivative i j x).det| • G (sourceCollarPiece i j x))=ᵐ[
        volume.restrict (sourceExtendedBox l r)]
      (fun x => (|a| *angularArea)*(sourceFaceWeight i j x*
        H (affineEndCoordinates a b (sourceFaceParameter i j x)))) := by
    filter_upwards [sourceExtendedBox_open_ae hl hr] with x hx
    dsimp only [G,H]
    rw [smul_eq_mul,sourceCollarDerivative_det,←sourceCollarJacobian_det]
    exact attachedPeriodicFlux_test_density hp ha hφ i j hx
  have hi (i j : Fin 4) : IntegrableOn G
      (sourceCollarPiece i j '' sourceExtendedBox l r) volume := by
    apply (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume measurableSet_Icc
      (fun x _ => (sourceCollarPiece_hasFDeriv i j x).hasFDerivWithinAt)
      (sourceExtendedBox_injOn i j hl hr) G).mpr
    exact ((integrable_sourceFacePullback hlr hg i j).const_mul (|a| *angularArea)).congr (he i j).symm
  have hG : IntegrableOn G (sourceClosedCollarBand l r) volume := by
    unfold IntegrableOn
    rw [sourceClosedCollarBand_measure_faces hl hr]
    exact integrable_finsetSum_measure.mpr (fun i _ =>
      integrable_finsetSum_measure.mpr fun j _ => hi i j)
  refine ⟨hG,?_⟩
  change (∫ y in sourceClosedCollarBand l r,G y)=_
  rw [integral_sourceClosedCollarBand_faces hl hr hG,
    integral_sourceCylinder_faces (F:=fun z => sourceFluxDensity F a⁻¹ b φ
      (affineEndCoordinates a b z)) hlr hg,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceExtended_integral i j hl hr G,integral_congr_ae (he i j),integral_const_mul]
  rfl

end ScalarConductivity

end
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Fourier_AttachedPeriodicGreen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.attachedPeriodicGreenMeasureSpace
local instance attachedPeriodicGreenIsProbabilityMeasure_r4812a5_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem attachedPeriodicFlux_smooth_green_oai {F : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) (hp : AngularPeriodic (2*Real.pi) F)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a b l r R : ℝ} (ha : a≠0) (hlr : l ≤ r) (hR : 0≤R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (he : (0<a ∧ a*(l-b)=0 ∧ a*(r-b)=R) ∨
      (a<0 ∧ a*(l-b)=R ∧ a*(r-b)=0))
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) :
    IntegrableOn (fun y => attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)
      (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)=
      angularArea*((∫ θ,torusPeriodicDescent F (R,θ) 0*
          φ (sourceAngularCollar (a⁻¹*R+b) θ))-
        (∫ θ,torusPeriodicDescent F (0,θ) 0*φ (sourceAngularCollar b θ))) := by
  obtain ⟨hi,hiE⟩ := attachedPeriodicFlux_smooth_pullback hF.continuous hp hφ ha hlr hl hr hT
  refine ⟨hi,hiE.trans ?_⟩
  have hI := (sourceFluxDensity_cylinder hF.continuous hp a⁻¹ b R hφ).1
  have hj : |a| *(∫ z,sourceFluxDensity F a⁻¹ b φ (affineEndCoordinates a b z)
      ∂(volume.restrict (Ioc l r)).prod volume)=
      ∫ z,sourceFluxDensity F a⁻¹ b φ z ∂(FiniteAxisMeasure R).prod volume := by
    rcases he with ⟨h,he₀,heR⟩|⟨h,heR,he₀⟩
    · exact integral_affineEndCoordinates_pos h hlr hT he₀ heR hR hI
    · exact integral_affineEndCoordinates_neg h hlr hT heR he₀ hR hI
  rw [mul_comm |a| angularArea,mul_assoc,hj,sourceFluxDensity_green hF hp hR hd a⁻¹ b hφ]

end ScalarConductivity

end
end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green_oai := @OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green_oai
