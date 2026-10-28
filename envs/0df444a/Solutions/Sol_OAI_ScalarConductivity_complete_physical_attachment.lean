-- Prove2me | solution 1 for OAI.ScalarConductivity.complete_physical_attachment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:08:20.247786+00:00
-- url     : https://prove2.me/submissions/72d403e7-c1c5-46a2-adb4-14b057c3e975

import Mathlib
import Definitions.Def_Conductivity
import Definitions.Def_OAIQ059C006

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_PhysicalCollarBand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus

lemma sourcePhysicalCoordinates_right {y : Fin 3 → ℝ}
    (ht : sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100)) :
    sourceAngularCollar (sourceCollarTime y) (sourcePhysicalAngles y)=y := by
  obtain ⟨i,j,a,b,ha,hb,he⟩ := sourceCollarPiece_cover_extended
    (sourceRadial_pos_of_time ht.1) (by linarith [ht.2])
  have he' : sourceAngularCollar (sourceCollarTime y)
      (torusAngles (sourceFaceAngles i j ![sourceCollarTime y,a,b]))=y :=
    (sourceFaceAngles_physical i j ha hb).trans he
  have hinv := sourcePhysicalAngles_angular ht
    (torusAngles (sourceFaceAngles i j ![sourceCollarTime y,a,b]))
  rw [he'] at hinv
  rw [hinv]
  exact he'

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CompactLipschitzH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

theorem compact_lipschitz_H1 {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hR : R<3)
    (hs : ∀ x, R<‖x‖ → f x=0) :
    ∃ u : H1, u∈H10 ∧ (∀ᵐ x ∂ballMeasure,
      weakValue u x=f x ∧ ∀ i : Fin 3,
        weakGradient u x i=lineDeriv ℝ f x (EuclideanSpace.single i 1)) := by
  have hm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport (bounded_support_compact hs)
  have hd (i : Fin 3) := lipschitz_lineDeriv_memLp hf hs (EuclideanSpace.single i 1)
  let F : Fin 4 → WholeL2 := Fin.cases (hm.toLp f)
    (fun i => (hd i).toLp (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)))
  have hv : (F 0 : R3 → ℝ)=ᵐ[volume] f := hm.coeFn_toLp
  have hg (i : Fin 3) : (F i.succ : R3 → ℝ)=ᵐ[volume]
      (fun x => lineDeriv ℝ f x (EuclideanSpace.single i 1)) := (hd i).coeFn_toLp
  have hw (i : Fin 3) : WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1) :=
    (lipschitz_weakDirection hf _).congr hv (hg i)
  obtain ⟨u,hu,he⟩ := compact_weak_H1 F hw hR (by
    filter_upwards [hv] with x hx
    intro hn
    exact hx.trans (hs x hn))
  refine ⟨u,hu,?_⟩
  have hv' := hv.filter_mono (ae_mono (Measure.restrict_le_self (s := ball)))
  have hg' := (ae_all_iff.mpr hg).filter_mono (ae_mono (Measure.restrict_le_self (s := ball)))
  filter_upwards [he,hv',hg'] with x hx hy hz
  exact ⟨hx.1.trans hy,fun i => (hx.2 i).trans (hz i)⟩

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ParentCompletionJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχb : ∀ x,|χ x|≤1)
  (hχs : tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness))

lemma parentCompletionJoin_mem_H10 (u : centralEnergySpace s) :
    parentCompletionJoin s hs ha hχ hc hχb hχs u∈H10 :=
  parentLocalJetCLM_central_H10 s hs ha hχ hc hχb hχs u

end

open Set MeasureTheory Filter Topology
open scoped ENNReal

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_CentralJoinCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma centralJoinPartition_eventually_sum {y : Fin 3 → ℝ} (hy : y∈centralPhysical) :
    (fun z => ∑ i : Fin 4,centralJoinPartition i z)=ᶠ[𝓝 y] (fun _ => (1:ℝ)) :=
  (Classical.choose_spec exists_centralJoinPartition_neighborhood).2 y hy

lemma centralJoinPartition_sum {y : Fin 3 → ℝ} (hy : y∈centralPhysical) :
    ∑ i : Fin 4,centralJoinPartition i y=1 := by
  simpa only [finsum_eq_sum_of_fintype] using centralJoinPartition.sum_eq_one hy

lemma centralJoinPartition_derivative_sum {y : Fin 3 → ℝ} (hy : y∈interior centralPhysical)
    (j : Fin 3) : ∑ i : Fin 4,fderiv ℝ (centralJoinPartition i) y (Pi.single j 1)=0 := by
  have he : (fun z => ∑ i : Fin 4,centralJoinPartition i z)=ᶠ[𝓝 y] (fun _ => (1:ℝ)) := by
    filter_upwards [mem_interior_iff_mem_nhds.mp hy] with z hz
    exact centralJoinPartition_sum hz
  have hd := Filter.EventuallyEq.fderiv_eq he (𝕜:=ℝ)
  rw [fderiv_fun_sum (fun i _ => (centralJoinPartition_smooth i).differentiable (by simp) y)] at hd
  have h := congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L (Pi.single j 1)) hd
  simpa using h

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ChildH10Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a) (k : Fin 2)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
  (hχb : ∀ x,|χ x|≤1)
  (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)

lemma physicalChildCompletionJoin_mem_H10 (u : centralEnergySpace s) :
    physicalChildCompletionJoin s hs ha k hχ hc hχb hχs u∈H10 :=
  childH10Transport_mem_H10 k _

end

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)

lemma centralInteriorCompletion_mem_H10 (hχs : tsupport χ⊆centralPhysical)
    (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) (u : centralEnergySpace s) :
    centralInteriorCompletion s hχ hc hχs hχB u∈H10 :=
  centralInteriorJetCLM_central_H10 s hχ hc hχs hχB u

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildTransportFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childTransportComponentCLM_ae_of_ae (k : Fin 2) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber) (he : ballWholePiJetCLM z=ᵐ[volume] f) (i : Fin 4) :
    childTransportComponentCLM k i z=ᵐ[volume] (fun y => Fin.cases
      (f ((sourceChildHomeomorph (actualChildSign k)).symm y) 0)
      (fun j => sourceScale⁻¹*f ((sourceChildHomeomorph (actualChildSign k)).symm y) (childAxis j).succ) i) := by
  have hc (j : Fin 4) : ballWholePiComponentCLM j z=ᵐ[volume] (fun y => f y j) := by
    filter_upwards [ballWholePiComponentCLM_ae j z,he] with y hi hy
    rw [hi,hy]
  have hp (j : Fin 4) := (sourceChildPushforwardCLM_ae (actualChildSign k) (ballWholePiComponentCLM j z)).trans
    ((sourceChildInverse_quasi _).ae_eq_comp (hc j))
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hp 0
  · apply (Lp.coeFn_smul _ _).trans
    filter_upwards [hp (childAxis j).succ] with y hy
    exact congrArg (fun t : ℝ => sourceScale⁻¹*t) hy

lemma childTransportJetCLM_ae_of_ae (k : Fin 2) (z : JetSpace)
    (f : (Fin 3 → ℝ) → JetFiber) (he : ballWholePiJetCLM z=ᵐ[volume] f) :
    childTransportJetCLM k z=ᵐ[ballMeasure] (fun x => WithLp.toLp 2 (Fin.cases
      (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) 0)
      (fun j => sourceScale⁻¹*f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis j).succ))) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (childTransportComponentCLM_ae_of_ae k z f he i))
  filter_upwards [physicalFourJetCLM_ae (fun i => childTransportComponentCLM k i z),ae_all_iff.mpr hi] with x hx hi
  change physicalFourJetCLM (fun i => childTransportComponentCLM k i z) x=_
  rw [hx]
  ext i
  exact hi i

lemma childAxis_involutive (i : Fin 3) : childAxis (childAxis i)=i := by
  fin_cases i <;> rfl

lemma physical_child_partial_cancel {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (σ : ℝ) (y : Fin 3 → ℝ) (i : Fin 3) :
    sourceScale⁻¹*fderiv ℝ (q ∘ sourceChildCoordinates σ)
      ((sourceChildHomeomorph σ).symm y) (Pi.single (childAxis i) 1)=
        fderiv ℝ q y (Pi.single i 1) := by
  have hD := ((hq.differentiable (by simp)) _).hasFDerivAt.comp
    ((sourceChildHomeomorph σ).symm y) (sourceChildCoordinates_hasFDeriv σ _)
  rw [hD.fderiv,ContinuousLinearMap.comp_apply,sourceChildDerivative_single,
    childAxis_involutive,map_smul,smul_eq_mul]
  change sourceScale⁻¹*(sourceScale*fderiv ℝ q
    ((sourceChildHomeomorph σ) ((sourceChildHomeomorph σ).symm y)) (Pi.single i 1))=_
  rw [Homeomorph.apply_symm_apply]
  rw [←mul_assoc,inv_mul_cancel₀ (by norm_num [sourceScale]),one_mul]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CutSlopeH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped NNReal

lemma lipschitz_mul_real_bounded {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L A B : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hA : ∀ x,|f x|≤A) (hB : ∀ x,|g x|≤B) :
    LipschitzWith (K*B+A*L) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have he : f x*g x-f y*g y=(f x-f y)*g x+f y*(g x-g y) := by ring
  rw [he]
  calc
    _ ≤ |(f x-f y)*g x|+|f y*(g x-g y)| := abs_add_le _ _
    _ = |f x-f y| *|g x|+|f y| *|g x-g y| := by rw [abs_mul,abs_mul]
    _ ≤ (K*dist x y)*B+A*(L*dist x y) := add_le_add
      (mul_le_mul (by simpa only [Real.dist_eq] using hf.dist_le_mul x y) (hB x) (abs_nonneg _) (by positivity))
      (mul_le_mul (hA y) (by simpa only [Real.dist_eq] using hg.dist_le_mul x y) (abs_nonneg _) (by positivity))
    _ = _ := by push_cast; ring

lemma compact_cut_positive_lipschitz {τ χ : (Fin 3 → ℝ) → ℝ} {K : ℝ≥0}
    (hτ : LipschitzWith K τ) (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {M : ℝ} (hM : 0≤M) (hb : ∀ x∈tsupport χ,τ x≤M) :
    ∃ C,LipschitzWith C (fun x => χ x*max 0 (τ x)) := by
  obtain ⟨C,hC⟩ := hχ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hr := (LipschitzWith.const (0:ℝ)).max (hτ.min (LipschitzWith.const M))
  have hbound (x : Fin 3 → ℝ) : |max 0 (min (τ x) M)|≤(⟨M,hM⟩:ℝ≥0) := by
    rw [abs_of_nonneg (le_max_left _ _)]
    exact max_le hM (min_le_right _ _)
  have H := lipschitz_mul_real_bounded hC hr (A:=1) (B:=(⟨M,hM⟩ : ℝ≥0)) (by simpa using hχb) hbound
  have he : (fun x => χ x*max 0 (τ x))=(fun x => χ x*max 0 (min (τ x) M)) := by
    funext x
    by_cases hx : x∈tsupport χ
    · rw [min_eq_left (hb x hx)]
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  have H' : ∃ D,LipschitzWith D (fun x => χ x*max 0 (min (τ x) M)) := ⟨_,H⟩
  rwa [←he] at H'

theorem compact_collar_slope_H1 {χ : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    (a b κ l r : ℝ) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand l r) :
    let f := fun x : R3 => κ*(χ (WithLp.ofLp x)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b)))
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=f x ∧ ∀ i,weakGradient w x i=lineDeriv ℝ f x (EuclideanSpace.single i 1)) := by
  obtain ⟨K,hK⟩ := attachedEndTime_lipschitz a b
  have hb (x : Fin 3 → ℝ) (hx : x∈tsupport χ) :
      a*(sourceCollarTime x-b)≤|a| *(|l|+|r|+|b|) := by
    have ht := hχs hx
    have hav : |sourceCollarTime x|≤|l|+|r| := by
      apply abs_le.mpr
      constructor
      · linarith [(neg_abs_le l).trans ht.1,abs_nonneg r]
      · linarith [ht.2.trans (le_abs_self r),abs_nonneg l]
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (show |sourceCollarTime x| + |b| ≤ |l|+|r|+|b| by linarith)) (abs_nonneg _))
  obtain ⟨C,hC⟩ := compact_cut_positive_lipschitz hK hχ hc hχb (by positivity) hb
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have H := (ContinuousLinearMap.toSpanSingleton ℝ κ).lipschitz.comp (hC.comp E.lipschitz)
  have hF : LipschitzWith (‖ContinuousLinearMap.toSpanSingleton ℝ κ‖₊ * (C * ‖E.toContinuousLinearMap‖₊))
      (fun x : R3 => κ*(χ (WithLp.ofLp x)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b)))) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Function.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,E,
      PiLp.coe_continuousLinearEquiv,smul_eq_mul,mul_comm] using H.dist_le_mul x y
  apply compact_lipschitz_H1 hF (by norm_num : (5:ℝ)/2<3)
  intro x hx
  have hn : WithLp.ofLp x∉tsupport χ := by
    intro hs
    have hh := sourceBand_euclidean_bound (show WithLp.ofLp x∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) from
      ⟨hl.trans (hχs hs).1,(hχs hs).2.trans hr⟩)
    exact not_le_of_gt hx hh
  simp [image_eq_zero_of_notMem_tsupport hn]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Geometry_CutSlopeGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma differentiable_cut_positive {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {χ τ : X → ℝ} {x : X} (hχ : DifferentiableAt ℝ χ x)
    (hτ : DifferentiableAt ℝ τ x) (hne : τ x≠0) (κ : ℝ) :
    DifferentiableAt ℝ (fun x => κ*(χ x*max 0 (τ x))) x := by
  rcases lt_or_gt_of_ne hne with hn | hp
  · have he : (fun x => κ*(χ x*max 0 (τ x))) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hτ.continuousAt.eventually (gt_mem_nhds hn)] with y hy
      simp [max_eq_left hy.le]
    exact (differentiableAt_const (0:ℝ)).congr_of_eventuallyEq he
  · have he : (fun x => κ*(χ x*max 0 (τ x))) =ᶠ[𝓝 x] (fun x => κ*(χ x*τ x)) := by
      filter_upwards [hτ.continuousAt.eventually (lt_mem_nhds hp)] with y hy
      rw [max_eq_right hy.le]
    exact ((hχ.mul hτ).const_mul κ).congr_of_eventuallyEq he

lemma fderiv_cut_positive {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {χ τ : X → ℝ} {x : X} (hχ : DifferentiableAt ℝ χ x)
    (hτ : DifferentiableAt ℝ τ x) (hne : τ x≠0) (κ : ℝ) (v : X) :
    fderiv ℝ (fun x => κ*(χ x*max 0 (τ x))) x v=
      κ*(fderiv ℝ χ x v*max 0 (τ x)+χ x*(if 0<τ x then fderiv ℝ τ x v else 0)) := by
  rcases lt_or_gt_of_ne hne with hn | hp
  · have he : (fun x => κ*(χ x*max 0 (τ x))) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [hτ.continuousAt.eventually (gt_mem_nhds hn)] with y hy
      simp [max_eq_left hy.le]
    rw [he.fderiv_eq,fderiv_const_apply]
    simp [max_eq_left hn.le,not_lt_of_ge hn.le]
  · have he : (fun x => κ*(χ x*max 0 (τ x))) =ᶠ[𝓝 x] (fun x => κ*(χ x*τ x)) := by
      filter_upwards [hτ.continuousAt.eventually (lt_mem_nhds hp)] with y hy
      rw [max_eq_right hy.le]
    have hh := ((hχ.hasFDerivAt.mul hτ.hasFDerivAt).const_mul κ).fderiv
    simp only [Pi.mul_apply] at hh
    rw [he.fderiv_eq,hh]
    simp [smul_apply,add_apply,smul_eq_mul,max_eq_right hp.le,hp]
    ring

theorem compact_collar_slope_value_gradient {χ : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    {a : ℝ} (ha : a≠0) {b : ℝ} (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (κ l r : ℝ) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hχs : tsupport χ⊆sourceClosedCollarBand l r) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=κ*(χ (WithLp.ofLp x)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b))) ∧
      ∀ i,weakGradient w x i=κ*(fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b))+
        χ (WithLp.ofLp x)*(if 0<a*(sourceCollarTime (WithLp.ofLp x)-b) then
          fderiv ℝ (fun y => a*(sourceCollarTime y-b)) (WithLp.ofLp x) (Pi.single i 1) else 0))) := by
  obtain ⟨w,hw,hwe⟩ := compact_collar_slope_H1 hχ hc hχb a b κ l r hl hr hχs
  refine ⟨w,hw,?_⟩
  obtain ⟨K,hK⟩ := attachedEndTime_lipschitz a b
  have hd := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (hK.ae_differentiableAt (μ:=volume)))
  have hn := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    (sourceColevel_ae_ne hb))
  filter_upwards [hwe,hd,hn] with x hx hd hn
  refine ⟨hx.1,fun i => ?_⟩
  have hne : a*(sourceCollarTime (WithLp.ofLp x)-b)≠0 := mul_ne_zero ha (sub_ne_zero.mpr hn)
  have hχd := hχ.differentiable (by simp) (WithLp.ofLp x)
  have hD := differentiable_cut_positive hχd hd hne κ
  let E : R3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hE := hD.hasFDerivAt.comp x E.hasFDerivAt
  simp only [Function.comp_def] at hE
  rw [hx.2 i,hE.differentiableAt.lineDeriv_eq_fderiv,hE.fderiv,ContinuousLinearMap.comp_apply]
  have hi : E.toContinuousLinearMap (EuclideanSpace.single i 1)=Pi.single i 1 := rfl
  rw [hi]
  exact fderiv_cut_positive hχd hd hne κ _

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_WholeBallJetFormula
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped Classical

lemma localJoinedJet_zero_outside_ball {τ χ q p : (Fin 3 → ℝ) → ℝ}
    (hs : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball) {y : Fin 3 → ℝ}
    (hy : WithLp.toLp 2 y∉ball) :
    WithLp.toLp 2 (Fin.cases (localJoinedValue τ χ q p y)
      (fun i => localJoinedGradient τ χ q p i y))=(0:JetFiber) := by
  have ht : y∉tsupport χ := fun h => hy (hs y h)
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [localJoinedValue,image_eq_zero_of_notMem_tsupport ht]
  · simp [localJoinedGradient,image_eq_zero_of_notMem_tsupport ht,fderiv_of_notMem_tsupport ℝ ht]

lemma ballWholePiJetCLM_localJoined_ae {z : JetSpace} {τ χ q p : (Fin 3 → ℝ) → ℝ}
    (hs : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball)
    (he : z=ᵐ[ballMeasure] (fun x => WithLp.toLp 2
      (Fin.cases (localJoinedValue τ χ q p (WithLp.ofLp x))
        (fun i => localJoinedGradient τ χ q p i (WithLp.ofLp x))))) :
    ballWholePiJetCLM z=ᵐ[volume] (fun y => WithLp.toLp 2
      (Fin.cases (localJoinedValue τ χ q p y) (fun i => localJoinedGradient τ χ q p i y))) := by
  apply (ballWholePiJetCLM_ae_of_ae z (fun y => WithLp.toLp 2
    (Fin.cases (localJoinedValue τ χ q p y) (fun i => localJoinedGradient τ χ q p i y))) he).trans
  exact Filter.Eventually.of_forall (fun y => by
    dsimp only
    split_ifs with hb
    · rfl
    · exact (localJoinedJet_zero_outside_ball hs hb).symm)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_PhysicalProductJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma localJoinedJet_eq_piSmoothJet {τ χ q p : (Fin 3 → ℝ) → ℝ} {y : Fin 3 → ℝ}
    (hτ : τ y ≤ 0) (hχ : DifferentiableAt ℝ χ y) (hq : DifferentiableAt ℝ q y) :
    WithLp.toLp 2 (Fin.cases (localJoinedValue τ χ q p y)
      (fun i => localJoinedGradient τ χ q p i y))=piSmoothJet (χ*q) y := by
  have hn : ¬0<τ y := not_lt_of_ge hτ
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [localJoinedValue,piSmoothJet,hn]
  · simp only [localJoinedGradient,hn,ite_false,PiLp.toLp_apply,Fin.cases_succ,
      piSmoothJet,fderiv_mul hχ hq,add_apply,smul_apply,
      smul_eq_mul,Pi.mul_apply]
    ring

lemma sourceChild_piSmoothJet_cancel (q : (Fin 3 → ℝ) → ℝ)
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (σ : ℝ) (y : Fin 3 → ℝ) :
    WithLp.toLp 2 (Fin.cases
      (piSmoothJet (q ∘ sourceChildCoordinates σ) ((sourceChildHomeomorph σ).symm y) 0)
      (fun j => sourceScale⁻¹*piSmoothJet (q ∘ sourceChildCoordinates σ)
        ((sourceChildHomeomorph σ).symm y) (childAxis j).succ))=piSmoothJet q y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change q ((sourceChildHomeomorph σ) ((sourceChildHomeomorph σ).symm y))=q y
    rw [Homeomorph.apply_symm_apply]
  · exact physical_child_partial_cancel hq σ y j

lemma piSmoothJet_partition {ρ : Fin 4 → (Fin 3 → ℝ) → ℝ}
    (hρ : ∀ i,ContDiff ℝ (↑(⊤:ℕ∞)) (ρ i)) {q : (Fin 3 → ℝ) → ℝ}
    (hq : ContDiff ℝ (↑(⊤:ℕ∞)) q) (y : Fin 3 → ℝ)
    (hv : ∑ i : Fin 4,ρ i y=1)
    (hg : ∀ j : Fin 3,∑ i : Fin 4,fderiv ℝ (ρ i) y (Pi.single j 1)=0) :
    ∑ i : Fin 4,piSmoothJet (ρ i*q) y=piSmoothJet q y := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (∑ i : Fin 4,piSmoothJet (ρ i*q) y) 0=q y
    simp only [WithLp.ofLp_sum,Finset.sum_apply,piSmoothJet,Fin.cases_zero,Pi.mul_apply]
    rw [←Finset.sum_mul,hv,one_mul]
  · change (∑ i : Fin 4,piSmoothJet (ρ i*q) y) j.succ=fderiv ℝ q y (Pi.single j 1)
    simp only [WithLp.ofLp_sum,Finset.sum_apply,piSmoothJet,Fin.cases_succ,
      fderiv_mul ((hρ _).differentiable (by simp) y) (hq.differentiable (by simp) y),
      add_apply,smul_apply,smul_eq_mul,
      Finset.sum_add_distrib,←Finset.sum_mul,←Finset.mul_sum,hv,hg,one_mul,mul_zero,add_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralLocalAgreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)

lemma centralInteriorCompletion_smooth_ae (f : centralSmoothFunctions) :
    (centralInteriorCompletion s (centralJoinPartition_smooth 0)
      centralJoinPartition_interior_compact centralJoinPartition_interior_support
      (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy))
      (centralSmoothElement s f)).val=ᵐ[ballMeasure]
        (fun x => piSmoothJet ((centralJoinPartition 0)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x)) := by
  have h₀ := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (centralInteriorComponentCLM_smooth_value s (centralJoinPartition_smooth 0)
      centralJoinPartition_interior_compact centralJoinPartition_interior_support f))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball) ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
    (centralInteriorComponentCLM_smooth_gradient s (centralJoinPartition_smooth 0)
      centralJoinPartition_interior_compact centralJoinPartition_interior_support f i))
  filter_upwards [physicalFourJetCLM_ae (fun i => centralInteriorComponentCLM s
    (centralJoinPartition_smooth 0) centralJoinPartition_interior_compact i (centralEmbedL s f)),h₀,ae_all_iff.mpr h₁] with x hj hv hg
  change physicalFourJetCLM (fun i => centralInteriorComponentCLM s
    (centralJoinPartition_smooth 0) centralJoinPartition_interior_compact i (centralEmbedL s f)) x=_
  rw [hj]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hv
  · exact hg j

lemma parentCompletionJoin_smooth_central {a : ℝ} (ha : a<0) (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support (centralSmoothElement s f)).val x=
      piSmoothJet ((centralJoinPartition 1)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := by
  filter_upwards [parentLocalJetCLM_smooth_ae s hs ha (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact centralJoinPartition_parent_support f] with x hx
  intro hy
  change parentLocalJetCLM s hs ha _ _ (centralEmbedL s f) x=_
  rw [hx]
  apply localJoinedJet_eq_piSmoothJet
  · exact mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr ((centralPhysical_time_iff _).mp hy).1)
  · exact (centralJoinPartition_smooth 1).differentiable (by simp) _
  · exact ((central_smooth f).comp sourcePairCLE.contDiff).differentiable (by simp) _

lemma physicalChildCompletionJoin_smooth_central {a : ℝ} (ha : 0<a) (k : Fin 2)
    (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) (centralSmoothElement s f)).val x=
      piSmoothJet ((centralJoinPartition (centralChildPatch k))*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := by
  have hB : ∀ y∈tsupport (centralJoinChildCutoff k),WithLp.toLp 2 y∈ball := by
    intro y hy
    have hb := centralJoinChildCutoff_support k hy
    exact sourceBand_mem_ball ⟨le_trans (by norm_num [centralThickness]) hb.1,
      le_trans hb.2 (by norm_num)⟩
  have hw := ballWholePiJetCLM_localJoined_ae hB
    (childLocalJetCLM_smooth_ae s hs ha k (centralJoinChildCutoff_smooth k)
      (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_support k) f)
  filter_upwards [childTransportJetCLM_ae_of_ae k _ _ hw] with x hx
  intro hy
  change childTransportJetCLM k (childLocalJetCLM s hs ha k
    (centralJoinChildCutoff_smooth k) (centralJoinChildCutoff_compact k) (centralEmbedL s f)) x=_
  rw [hx]
  let y := (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)
  have ht : a*(sourceCollarTime y-(-centralThickness)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr (((centralPhysical_time_iff _).mp hy).2 k))
  have hq := ((central_smooth f).comp sourcePairCLE.contDiff).comp (sourceChildCoordinates_contDiff (actualChildSign k))
  have he := localJoinedJet_eq_piSmoothJet
    (τ:=fun y => a*(sourceCollarTime y-(-centralThickness)))
    (χ:=centralJoinChildCutoff k)
    (q:=fun y => f (sourcePairCoordinates (sourceChildCoordinates (actualChildSign k) y)))
    (p:=fun y =>
      (attachedEndPoissonField s (centralSmoothTrace s f k.succ) a (-centralThickness) 0 y).re)
    ht ((centralJoinChildCutoff_smooth k).differentiable (by simp) y) (hq.differentiable (by simp) y)
  have he' := congrArg (fun z : JetFiber => (WithLp.toLp 2
    (Fin.cases (z 0) (fun j => sourceScale⁻¹*z (childAxis j).succ)) : JetFiber)) he
  exact he'.trans (sourceChild_piSmoothJet_cancel
    ((centralJoinPartition (centralChildPatch k))*(fun y => f (sourcePairCoordinates y)))
    ((centralJoinPartition_smooth _).mul ((central_smooth f).comp sourcePairCLE.contDiff))
    (actualChildSign k) (WithLp.ofLp x))

end

open Set MeasureTheory Filter Topology

lemma centralPhysical_ae_interior :
    ∀ᵐ y : Fin 3 → ℝ,y∈centralPhysical → y∈interior centralPhysical := by
  have hp := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hc (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hp,ae_all_iff.mpr hc] with y hp hc
  intro hy
  have ht := (centralPhysical_time_iff y).mp hy
  exact centralPhysical_mem_interior_of_strict (lt_of_le_of_ne ht.1 hp.symm)
    (fun k => lt_of_le_of_ne (ht.2 k) (hc k))

lemma centralPhysical_ball_ae_interior :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical → WithLp.ofLp x∈interior centralPhysical :=
  ae_restrict_of_ae ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae centralPhysical_ae_interior)

open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

lemma centralNeighborhoodCompletion_val (u : centralEnergySpace s) :
    (centralNeighborhoodCompletion s hs ha₀ ha u).val=centralNeighborhoodRawCLM s hs ha₀ ha u.val := by
  simp only [centralNeighborhoodCompletion,Fin.sum_univ_two,centralNeighborhoodRawCLM,
    add_apply,ContinuousLinearMap.comp_apply,Submodule.coe_add]
  rfl

lemma centralFullJetCLM_smooth_ae (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      centralFullJetCLM s (centralEmbedL s f) x=
        piSmoothJet (fun y => f (sourcePairCoordinates y)) (WithLp.ofLp x) := by
  have hi (i : Fin 4) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp
      (centralPhysicalWholeCLM_smooth_ae f i))
  filter_upwards [physicalFourJetCLM_ae (fun i => centralPhysicalWholeCLM (centralSmoothJet f i)),
    ae_all_iff.mpr hi] with x hx hi
  intro hy
  simp only [Function.comp_apply] at hi
  change physicalFourJetCLM (fun i => centralPhysicalWholeCLM (centralSmoothJet f i)) x=_
  rw [hx]
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [indicator_of_mem hy,piSmoothJet,PiLp.toLp_apply,Fin.cases_zero,
      centralJetField,Matrix.cons_val_zero] using hi 0
  · change centralPhysicalWholeCLM (centralSmoothJet f j.succ) (WithLp.ofLp x)=_
    rw [hi j.succ,indicator_of_mem hy,central_parent_partial]
    rfl

lemma centralNeighborhoodRawCLM_smooth_ae (f : centralSmoothFunctions) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      centralNeighborhoodRawCLM s hs ha₀ ha (centralEmbedL s f) x=
        piSmoothJet (fun y => f (sourcePairCoordinates y)) (WithLp.ofLp x) := by
  let zi := centralInteriorJetCLM s (centralJoinPartition_smooth 0)
    centralJoinPartition_interior_compact (centralEmbedL s f)
  let zp := parentLocalJetCLM s hs ha₀ (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralEmbedL s f)
  let zc (k : Fin 2) := childTransportJetCLM k (childLocalJetCLM s hs (ha k) k
    (centralJoinChildCutoff_smooth k) (centralJoinChildCutoff_compact k) (centralEmbedL s f))
  filter_upwards [Lp.coeFn_add (zi+zp) (zc 0+zc 1),Lp.coeFn_add zi zp,Lp.coeFn_add (zc 0) (zc 1),
    centralInteriorCompletion_smooth_ae s f,parentCompletionJoin_smooth_central s hs ha₀ f,
    physicalChildCompletionJoin_smooth_central s hs (ha 0) 0 f,
    physicalChildCompletionJoin_smooth_central s hs (ha 1) 1 f,
    centralPhysical_ball_ae_interior] with x hz hip hcc hi hp hc₀ hc₁ hinter
  intro hy
  change (zi+zp+(zc 0+zc 1)) x=_
  rw [hz]
  change (zi+zp) x+(zc 0+zc 1) x=_
  rw [hip,hcc]
  change zi x+zp x+(zc 0 x+zc 1 x)=_
  change zi x=_ at hi
  have hp' : zp x=piSmoothJet ((centralJoinPartition 1)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := hp hy
  have h₀ : zc 0 x=piSmoothJet ((centralJoinPartition 2)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := hc₀ hy
  have h₁ : zc 1 x=piSmoothJet ((centralJoinPartition 3)*(fun y => f (sourcePairCoordinates y))) (WithLp.ofLp x) := hc₁ hy
  rw [hi,hp',h₀,h₁]
  have he := piSmoothJet_partition (q:=fun y => f (sourcePairCoordinates y)) centralJoinPartition_smooth
    ((central_smooth f).comp sourcePairCLE.contDiff) (WithLp.ofLp x)
    (centralJoinPartition_sum hy) (centralJoinPartition_derivative_sum (hinter hy))
  simpa only [Fin.sum_univ_four,add_assoc] using he

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CentralJetIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ScalarConductivity

section
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : Fin 3 → ℝ} (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)

lemma centralBallSet_measurable : MeasurableSet centralBallSet :=
  centralPhysical_compact.measurableSet.preimage
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).continuous.measurable

lemma centralNeighborhoodRawCLM_smooth_restrict (f : centralSmoothFunctions) :
    lpRestrictionCLM centralBallSet (centralNeighborhoodRawCLM s hs ha₀ ha (centralEmbedL s f))=
      lpRestrictionCLM centralBallSet (centralFullJetCLM s (centralEmbedL s f)) := by
  apply Lp.ext
  filter_upwards [lpRestrictionCLM_ae centralBallSet (centralNeighborhoodRawCLM s hs ha₀ ha (centralEmbedL s f)),
    lpRestrictionCLM_ae centralBallSet (centralFullJetCLM s (centralEmbedL s f)),
    ae_restrict_of_ae (centralNeighborhoodRawCLM_smooth_ae s hs ha₀ ha f),
    ae_restrict_of_ae (centralFullJetCLM_smooth_ae s f),
    ae_restrict_mem centralBallSet_measurable] with x h₁ h₂ hn hc hx
  exact h₁.trans ((hn hx).trans ((hc hx).symm.trans h₂.symm))

theorem centralNeighborhoodCompletion_restrict (u : centralEnergySpace s) :
    lpRestrictionCLM centralBallSet (centralNeighborhoodCompletion s hs ha₀ ha u).val=
      lpRestrictionCLM centralBallSet (centralFullJetCLM s u.val) := by
  let L := (lpRestrictionCLM centralBallSet).comp (centralNeighborhoodRawCLM s hs ha₀ ha)-
    (lpRestrictionCLM centralBallSet).comp (centralFullJetCLM s)
  have hr : LinearMap.range (centralEmbedL s)≤LinearMap.ker L.toLinearMap := by
    rintro _ ⟨f,rfl⟩
    change lpRestrictionCLM centralBallSet (centralNeighborhoodRawCLM s hs ha₀ ha (centralEmbedL s f))-
      lpRestrictionCLM centralBallSet (centralFullJetCLM s (centralEmbedL s f))=0
    exact sub_eq_zero.mpr (centralNeighborhoodRawCLM_smooth_restrict s hs ha₀ ha f)
  have hu := Submodule.topologicalClosure_minimal _ hr L.isClosed_ker u.property
  rw [centralNeighborhoodCompletion_val]
  exact sub_eq_zero.mp hu

lemma centralNeighborhoodCompletion_central_ae (u : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈centralPhysical →
      (centralNeighborhoodCompletion s hs ha₀ ha u).val x=centralFullJetCLM s u.val x := by
  have he := centralNeighborhoodCompletion_restrict s hs ha₀ ha u
  apply (ae_restrict_iff' centralBallSet_measurable).mp
  filter_upwards [lpRestrictionCLM_ae centralBallSet (centralNeighborhoodCompletion s hs ha₀ ha u).val,
    lpRestrictionCLM_ae centralBallSet (centralFullJetCLM s u.val)] with x h₁ h₂
  rw [←h₁,he,h₂]

end

open Set MeasureTheory Filter Topology

lemma H1_add_jet_ae (u v : H1) :
    (u+v).val=ᵐ[ballMeasure] (fun x => u.val x+v.val x) := by
  exact Lp.coeFn_add u.val v.val

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ParentCompletedEndJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : a<0)

lemma parentCentralComponentCLM_zero_end (u : CentralAmbient s) (i : Fin 4) :
    ∀ᵐ y∂volume,sourceCollarTime y < centralThickness →
      parentCentralComponentCLM s i u y=0 := by
  have he := lpZeroExtensionCLM_ae parentBand_measurable
    (lpRestrictionCLM (sourceClosedCollarBand centralThickness (2*centralThickness))
      (centralPhysicalWholeCLM (centralAmbientComponent s i u)))
  filter_upwards [he] with y hy ht
  rw [show parentCentralComponentCLM s i u y=_ from hy]
  exact indicator_of_notMem (fun hh => not_le_of_gt ht hh.1) _

lemma parentJoinedComponentCLM_end_value (u : CentralAmbient s) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand 0 centralThickness →
      parentJoinedComponentCLM s hs ha 0 u y=
        (attachedEndPoissonField s (centralAmbientT s 0 u) a centralThickness 0 y).re := by
  have hadd := Lp.coeFn_add (parentCentralComponentCLM s 0 u)
    (parentEndValueCLM s hs ha (centralAmbientT s 0 u))
  filter_upwards [hadd,parentCentralComponentCLM_zero_end s u 0,
    parentEndValueCLM_ae s hs ha (centralAmbientT s 0 u),
    sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
      norm_num [centralThickness])] with y hy hc he hn hb
  change (parentCentralComponentCLM s 0 u+parentEndValueCLM s hs ha (centralAmbientT s 0 u)) y=_
  rw [hy]
  simp only [Pi.add_apply,hc (lt_of_le_of_ne hb.2 hn),he,indicator_of_mem hb,zero_add]

lemma parentJoinedComponentCLM_end_gradient (u : CentralAmbient s) (i : Fin 3) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand 0 centralThickness →
      parentJoinedComponentCLM s hs ha i.succ u y=
        fderiv ℝ (fun y => (attachedEndPoissonField s (centralAmbientT s 0 u)
          a centralThickness 0 y).re) y (Pi.single i 1) := by
  have hadd := Lp.coeFn_add (parentCentralComponentCLM s i.succ u)
    (parentEndGradientCLM s hs ha i (centralAmbientT s 0 u))
  filter_upwards [hadd,parentCentralComponentCLM_zero_end s u i.succ,
    parentEndGradientCLM_ae s hs ha (centralAmbientT s 0 u) i,
    sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
      norm_num [centralThickness])] with y hy hc he hn hb
  change (parentCentralComponentCLM s i.succ u+parentEndGradientCLM s hs ha i (centralAmbientT s 0 u)) y=_
  rw [hy]
  simp only [Pi.add_apply,hc (lt_of_le_of_ne hb.2 hn),he,indicator_of_mem hb,zero_add]

variable {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
  (hc : HasCompactSupport χ)

lemma parentLocalComponentCLM_end_value (u : CentralAmbient s) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand 0 centralThickness →
      parentLocalComponentCLM s hs ha hχ hc 0 u y=
        χ y*(attachedEndPoissonField s (centralAmbientT s 0 u) a centralThickness 0 y).re := by
  filter_upwards [compactMultiplierCLM_ae hχ.continuous hc
    (parentJoinedComponentCLM s hs ha 0 u),
    parentJoinedComponentCLM_end_value s hs ha u] with y he hv hb
  exact he.trans (congrArg (fun z => χ y*z) (hv hb))

lemma parentLocalComponentCLM_end_gradient (u : CentralAmbient s) (i : Fin 3) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand 0 centralThickness →
      parentLocalComponentCLM s hs ha hχ hc i.succ u y=
        fderiv ℝ χ y (Pi.single i 1)*
          (attachedEndPoissonField s (centralAmbientT s 0 u) a centralThickness 0 y).re+
        χ y*fderiv ℝ (fun y => (attachedEndPoissonField s (centralAmbientT s 0 u)
          a centralThickness 0 y).re) y (Pi.single i 1) := by
  have h₀ := compactMultiplierCLM_ae
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (parentJoinedComponentCLM s hs ha 0 u)
  have h₁ := compactMultiplierCLM_ae hχ.continuous hc
    (parentJoinedComponentCLM s hs ha i.succ u)
  have hadd := Lp.coeFn_add
    (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) (parentJoinedComponentCLM s hs ha 0 u))
    (compactMultiplierCLM hχ.continuous hc (parentJoinedComponentCLM s hs ha i.succ u))
  filter_upwards [hadd,h₀,h₁,parentJoinedComponentCLM_end_value s hs ha u,
    parentJoinedComponentCLM_end_gradient s hs ha u i] with y he h₀ h₁ hv hg hb
  apply he.trans
  simp only [Pi.add_apply,h₀,h₁,hv hb,hg hb]

theorem parentCompletionJoin_end_ae (hχb : ∀ x,|χ x|≤1)
    (hχs : tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness))
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand 0 centralThickness →
      weakValue (parentCompletionJoin s hs ha hχ hc hχb hχs p) x=
        χ (WithLp.ofLp x)*(attachedEndPoissonField s (centralT s 0 p)
          a centralThickness 0 (WithLp.ofLp x)).re ∧
      ∀ i,weakGradient (parentCompletionJoin s hs ha hχ hc hχb hχs p) x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*
          (attachedEndPoissonField s (centralT s 0 p) a centralThickness 0 (WithLp.ofLp x)).re+
        χ (WithLp.ofLp x)*fderiv ℝ (fun y =>
          (attachedEndPoissonField s (centralT s 0 p) a centralThickness 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1) := by
  have h₀ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (parentLocalComponentCLM_end_value s hs ha hχ hc p.val))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (parentLocalComponentCLM_end_gradient s hs ha hχ hc p.val i))
  have hjet := physicalFourJetCLM_ae
    (fun i => parentLocalComponentCLM s hs ha hχ hc i p.val)
  filter_upwards [hjet,h₀,ae_all_iff.mpr h₁] with x hj hv hg hb
  constructor
  · change WithLp.ofLp ((parentLocalJetCLM s hs ha hχ hc p.val) x) 0=_
    exact (congrArg (fun z : JetFiber => WithLp.ofLp z 0) hj).trans (hv hb)
  · intro i
    change WithLp.ofLp ((parentLocalJetCLM s hs ha hχ hc p.val) x) i.succ=_
    exact (congrArg (fun z : JetFiber => WithLp.ofLp z i.succ) hj).trans (hg i hb)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_CutAttachedEndH1
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem cut_attachedEnd_H10 (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s))
    {a b l r R : ℝ} (ha : a≠0) (hR : 0≤R)
    (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hpos : ∀ t∈Icc l r,0<a*(t-b))
    {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχs : tsupport χ⊆sourceClosedCollarBand l r) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=χ (WithLp.ofLp x)*(attachedEndPoissonField s f a b 0 (WithLp.ofLp x)).re ∧
      ∀ i,weakGradient w x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*
          (attachedEndPoissonField s f a b 0 (WithLp.ofLp x)).re+
        χ (WithLp.ofLp x)*fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1)) := by
  let D := sourceClosedCollarBand l r
  have hD : MeasurableSet D := measurableSet_Icc.preimage measurable_sourcePhysicalCoordinates.fst
  have hband {x : Fin 3 → ℝ} (hx : x∈D) :
      x∈sourceClosedCollarBand (-(1:ℝ)/100) (1/100) := ⟨hl.trans hx.1,hx.2.trans hr⟩
  let p := fun y => (attachedEndPoissonField s f a b 0 y).re
  have hp : MemLp p 2 (volume.restrict D) :=
    (attachedEndPoissonField_memLp s hs f ha hR hlr hl hr hT 0).re
  have hd : ∀ᵐ x∂volume.restrict D,0<(1:ℝ) → HasFDerivAt p (fderiv ℝ p x) x := by
    filter_upwards [ae_restrict_mem hD,
      ae_restrict_of_ae (attachedEndPoisson_real_differentiable_ae s hs f a b)] with x hx hdx _
    exact (hdx (hband hx) (hpos _ hx)).hasFDerivAt
  have hthin : Tendsto (fun n : ℕ => ((n:ℝ)+1)^2*
      ∫ x in {x | 0<(1:ℝ) ∧ ((n:ℝ)+1)*(1:ℝ)≤2},
        (cutMatchedValue (fun _ => 1) χ p x)^2) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (3:ℕ)] with n hn
    have hn' : (3:ℝ)≤n := by exact_mod_cast hn
    have he : {x : Fin 3 → ℝ | 0<(1:ℝ) ∧ ((n:ℝ)+1)*(1:ℝ)≤2}=∅ := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false,not_and]
      intro _
      linarith
    simp only [he,Measure.restrict_empty,integral_zero_measure,mul_zero]
  obtain ⟨w,hw,he⟩ := localized_matched_seam_H1_pi
    (LipschitzWith.const (1:ℝ)) hχ hc hD hp
    (fun x hx _ => hχs hx)
    (fun x hx _ => attachedEndPoissonField_localLip s hs f a b
      (hpos _ (hχs hx)) (sourceDirections_ne_zero_on_band (hband (hχs hx))))
    (fderiv ℝ p) (attachedEndPoisson_grad_memLp s hs f ha hR hb hlr hl hr hT)
    hd (show (5:ℝ)/2<3 by norm_num)
    (fun x hx => sourceBand_euclidean_bound (hband (hχs hx))) hthin
  refine ⟨w,hw,?_⟩
  simpa only [cutMatchedValue,cutMatchedGradient,show (0:ℝ)<1 by norm_num,ite_true,p] using he

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem cut_fullAttachedEnd_H10 (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ)
    {a b l r R : ℝ} (ha : a≠0) (hR : 0≤R)
    (hb : b∈Icc (-(1:ℝ)/100) (1/100))
    (hlr : l ≤ r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (hpos : ∀ t∈Icc l r,0<a*(t-b))
    {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
    (hc : HasCompactSupport χ) (hχb : ∀ x,|χ x|≤1)
    (hχs : tsupport χ⊆sourceClosedCollarBand l r) :
    ∃ w : H1,w∈H10 ∧ (∀ᵐ x∂ballMeasure,
      weakValue w x=χ (WithLp.ofLp x)*fullAttachedEndValue s f a b κ (WithLp.ofLp x) ∧
      ∀ i,weakGradient w x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*fullAttachedEndValue s f a b κ (WithLp.ofLp x)+
        χ (WithLp.ofLp x)*fullAttachedEndGradient s f a b κ (WithLp.ofLp x) i) := by
  obtain ⟨u,hu,he⟩ := cut_attachedEnd_H10 s hs f ha hR hb hlr hl hr hT hpos hχ hc hχs
  obtain ⟨v,hv,hve⟩ := compact_collar_slope_value_gradient hχ hc hχb ha hb κ l r hl hr hχs
  refine ⟨u+v,H10.add_mem hu hv,?_⟩
  filter_upwards [he,hve,weakValue_add u v,weakGradient_add u v] with x hx hy hv hg
  rw [hv,hg]
  simp only [Pi.add_apply,WithLp.ofLp_add]
  rw [hx.1,hy.1]
  constructor
  · by_cases h : WithLp.ofLp x∈tsupport χ
    · rw [max_eq_right (hpos _ (hχs h)).le]
      dsimp only [fullAttachedEndValue]
      ring
    · simp only [image_eq_zero_of_notMem_tsupport h,zero_mul,mul_zero,add_zero]
  · intro i
    simp only [hx.2 i,hy.2 i]
    by_cases h : WithLp.ofLp x∈tsupport χ
    · rw [max_eq_right (hpos _ (hχs h)).le,ite_eq_left (hpos _ (hχs h))]
      dsimp only [fullAttachedEndValue,fullAttachedEndGradient]
      ring
    · have hd : fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)=0 :=
        image_eq_zero_of_notMem_tsupport (f:=fun y => fderiv ℝ χ y (Pi.single i 1))
          (fun hh => h (tsupport_fderiv_apply_subset ℝ _ hh))
      simp only [image_eq_zero_of_notMem_tsupport h,hd,zero_mul,mul_zero,add_zero]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_EndPartitionJet
attribute [-instance] _root_.OAI.ScalarConductivity.centralAmbientInnerProductSpace _root_.OAI.ScalarConductivity.centralAmbientNormedSpace _root_.OAI.ScalarConductivity.spectralTraceGraph_realInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma fullEnd_partition_jet (s : Fin 3 → ℝ) (f : spectralTraceGraph (torusRate s))
    (a b κ : ℝ) {D : Set (Fin 3 → ℝ)}
    {χ η : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hη : ContDiff ℝ (↑(⊤:ℕ∞)) η)
    (hpart : ∀ x∈D,(fun y => χ y+η y)=ᶠ[𝓝 x] (fun _ => 1))
    (hpos : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → 0<a*(sourceCollarTime (WithLp.ofLp x)-b))
    (u v z : H1)
    (hue : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue u x=χ (WithLp.ofLp x)*(attachedEndPoissonField s f a b 0 (WithLp.ofLp x)).re ∧
      ∀ i,weakGradient u x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*(attachedEndPoissonField s f a b 0 (WithLp.ofLp x)).re+
        χ (WithLp.ofLp x)*fderiv ℝ (fun y => (attachedEndPoissonField s f a b 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1))
    (hve : ∀ᵐ x∂ballMeasure,
      weakValue v x=κ*(χ (WithLp.ofLp x)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b))) ∧
      ∀ i,weakGradient v x i=κ*(fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*max 0 (a*(sourceCollarTime (WithLp.ofLp x)-b))+
        χ (WithLp.ofLp x)*(if 0<a*(sourceCollarTime (WithLp.ofLp x)-b) then
          fderiv ℝ (fun y => a*(sourceCollarTime y-b)) (WithLp.ofLp x) (Pi.single i 1) else 0)))
    (hze : ∀ᵐ x∂ballMeasure,
      weakValue z x=η (WithLp.ofLp x)*fullAttachedEndValue s f a b κ (WithLp.ofLp x) ∧
      ∀ i,weakGradient z x i=
        fderiv ℝ η (WithLp.ofLp x) (Pi.single i 1)*fullAttachedEndValue s f a b κ (WithLp.ofLp x)+
        η (WithLp.ofLp x)*fullAttachedEndGradient s f a b κ (WithLp.ofLp x) i) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue (u+v+z) x=fullAttachedEndValue s f a b κ (WithLp.ofLp x) ∧
      ∀ i,weakGradient (u+v+z) x i=fullAttachedEndGradient s f a b κ (WithLp.ofLp x) i := by
  filter_upwards [hue,hve,hze,hpos,weakValue_add u v,weakValue_add (u+v) z,
    weakGradient_add u v,weakGradient_add (u+v) z] with x hux hvx hzx hnx hv₀ hv₁ hg₀ hg₁ hx
  have ht := hnx hx
  have hpu := (hpart (WithLp.ofLp x) hx).self_of_nhds
  change χ (WithLp.ofLp x)+η (WithLp.ofLp x)=1 at hpu
  have hpd : ∀ i : Fin 3,
      fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)+
      fderiv ℝ η (WithLp.ofLp x) (Pi.single i 1)=0 := by
    have hd : fderiv ℝ (fun y => χ y+η y) (WithLp.ofLp x)=0 := by
      rw [(hpart (WithLp.ofLp x) hx).fderiv_eq]
      exact fderiv_const_apply (1:ℝ)
    change fderiv ℝ (χ+η) (WithLp.ofLp x)=0 at hd
    rw [fderiv_add (hχ.differentiable (by simp) _) (hη.differentiable (by simp) _)] at hd
    intro i
    exact congrArg (fun L : (Fin 3 → ℝ) →L[ℝ] ℝ => L (Pi.single i 1)) hd
  constructor
  · rw [hv₁]
    simp only [Pi.add_apply]
    rw [hv₀]
    simp only [Pi.add_apply]
    rw [(hux hx).1,hvx.1,hzx.1,max_eq_right ht.le]
    dsimp only [fullAttachedEndValue]
    calc
      _=(χ (WithLp.ofLp x)+η (WithLp.ofLp x))*
        ((attachedEndPoissonField s (f) a b 0 (WithLp.ofLp x)).re+
         κ*(a*(sourceCollarTime (WithLp.ofLp x)-b))) := by ring
      _=_ := by rw [hpu,one_mul]
  · intro i
    rw [hg₁]
    simp only [Pi.add_apply]
    rw [hg₀]
    simp only [Pi.add_apply,WithLp.ofLp_add]
    rw [(hux hx).2 i,hvx.2 i,hzx.2 i,max_eq_right ht.le,ite_eq_left ht]
    dsimp only [fullAttachedEndValue,fullAttachedEndGradient]
    calc
      _=(fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)+
          fderiv ℝ η (WithLp.ofLp x) (Pi.single i 1))*
        ((attachedEndPoissonField s (f) a b 0 (WithLp.ofLp x)).re+
          κ*(a*(sourceCollarTime (WithLp.ofLp x)-b)))+
        (χ (WithLp.ofLp x)+η (WithLp.ofLp x))*
        (fderiv ℝ (fun y => (attachedEndPoissonField s (f) a b 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1)+
          κ*fderiv ℝ (fun y => a*(sourceCollarTime y-b))
            (WithLp.ofLp x) (Pi.single i 1)) := by ring
      _=_ := by rw [hpd i,hpu,zero_mul,one_mul,zero_add]

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ParentFullEndEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable (s : Fin 3 → ℝ)
  (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
  {a : ℝ} (ha : 0<a) (k : Fin 2)

lemma childCentralRawComponentCLM_zero_end (k : Fin 2) (u : CentralAmbient s) (i : Fin 4) :
    ∀ᵐ y∂volume,-centralThickness < sourceCollarTime y →
      childCentralRawComponentCLM s k i u y=0 := by
  have he := lpZeroExtensionCLM_ae childCentralBand_measurable
    (lpRestrictionCLM (sourceClosedCollarBand (-2*centralThickness) (-centralThickness))
      (sourceChildPullbackCLM (actualChildSign k)
        (centralPhysicalWholeCLM (centralAmbientComponent s i u))))
  filter_upwards [he] with y hy ht
  rw [show childCentralRawComponentCLM s k i u y=_ from hy]
  exact indicator_of_notMem (fun hh => not_le_of_gt ht hh.2) _

lemma childCentralComponentCLM_zero_end (k : Fin 2) (u : CentralAmbient s) (i : Fin 4) :
    ∀ᵐ y∂volume,-centralThickness < sourceCollarTime y →
      childCentralComponentCLM s k i u y=0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact childCentralRawComponentCLM_zero_end s k u 0
  · filter_upwards [childCentralRawComponentCLM_zero_end s k u (childAxis j).succ,
      Lp.coeFn_smul sourceScale (childCentralRawComponentCLM s k (childAxis j).succ u)] with y hy he ht
    change (sourceScale • childCentralRawComponentCLM s k (childAxis j).succ u) y=0
    rw [he]
    simp only [Pi.smul_apply,smul_eq_mul,hy ht,mul_zero]

lemma childJoinedComponentCLM_end_value (u : CentralAmbient s) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand (-centralThickness) 0 →
      childJoinedComponentCLM s hs ha k 0 u y=
        (attachedEndPoissonField s (centralAmbientT s k.succ u) a (-centralThickness) 0 y).re := by
  have hadd := Lp.coeFn_add (childCentralComponentCLM s k 0 u)
    (childEndValueCLM s hs ha (centralAmbientT s k.succ u))
  filter_upwards [hadd,childCentralComponentCLM_zero_end s k u 0,
    childEndValueCLM_ae s hs ha (centralAmbientT s k.succ u),
    sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
      norm_num [centralThickness])] with y hy hc he hn hb
  change (childCentralComponentCLM s k 0 u+childEndValueCLM s hs ha (centralAmbientT s k.succ u)) y=_
  rw [hy]
  simp only [Pi.add_apply,hc (lt_of_le_of_ne hb.1 (Ne.symm hn)),he,indicator_of_mem hb,zero_add]

lemma childJoinedComponentCLM_end_gradient (u : CentralAmbient s) (i : Fin 3) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand (-centralThickness) 0 →
      childJoinedComponentCLM s hs ha k i.succ u y=
        fderiv ℝ (fun y => (attachedEndPoissonField s (centralAmbientT s k.succ u)
          a (-centralThickness) 0 y).re) y (Pi.single i 1) := by
  have hadd := Lp.coeFn_add (childCentralComponentCLM s k i.succ u)
    (childEndGradientCLM s hs ha i (centralAmbientT s k.succ u))
  filter_upwards [hadd,childCentralComponentCLM_zero_end s k u i.succ,
    childEndGradientCLM_ae s hs ha (centralAmbientT s k.succ u) i,
    sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
      norm_num [centralThickness])] with y hy hc he hn hb
  change (childCentralComponentCLM s k i.succ u+childEndGradientCLM s hs ha i (centralAmbientT s k.succ u)) y=_
  rw [hy]
  simp only [Pi.add_apply,hc (lt_of_le_of_ne hb.1 (Ne.symm hn)),he,indicator_of_mem hb,zero_add]

variable {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ)
  (hc : HasCompactSupport χ)

lemma childLocalComponentCLM_end_value (u : CentralAmbient s) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand (-centralThickness) 0 →
      childLocalComponentCLM s hs ha k hχ hc 0 u y=
        χ y*(attachedEndPoissonField s (centralAmbientT s k.succ u) a (-centralThickness) 0 y).re := by
  filter_upwards [compactMultiplierCLM_ae hχ.continuous hc
    (childJoinedComponentCLM s hs ha k 0 u),
    childJoinedComponentCLM_end_value s hs ha k u] with y he hv hb
  exact he.trans (congrArg (fun z => χ y*z) (hv hb))

lemma childLocalComponentCLM_end_gradient (u : CentralAmbient s) (i : Fin 3) :
    ∀ᵐ y∂volume,y∈sourceClosedCollarBand (-centralThickness) 0 →
      childLocalComponentCLM s hs ha k hχ hc i.succ u y=
        fderiv ℝ χ y (Pi.single i 1)*
          (attachedEndPoissonField s (centralAmbientT s k.succ u) a (-centralThickness) 0 y).re+
        χ y*fderiv ℝ (fun y => (attachedEndPoissonField s (centralAmbientT s k.succ u)
          a (-centralThickness) 0 y).re) y (Pi.single i 1) := by
  have h₀ := compactMultiplierCLM_ae
    ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ (Pi.single i 1)) (childJoinedComponentCLM s hs ha k 0 u)
  have h₁ := compactMultiplierCLM_ae hχ.continuous hc
    (childJoinedComponentCLM s hs ha k i.succ u)
  have hadd := Lp.coeFn_add
    (compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) (childJoinedComponentCLM s hs ha k 0 u))
    (compactMultiplierCLM hχ.continuous hc (childJoinedComponentCLM s hs ha k i.succ u))
  filter_upwards [hadd,h₀,h₁,childJoinedComponentCLM_end_value s hs ha k u,
    childJoinedComponentCLM_end_gradient s hs ha k u i] with y he h₀ h₁ hv hg hb
  apply he.trans
  simp only [Pi.add_apply,h₀,h₁,hv hb,hg hb]

theorem childCompletionJoin_end_ae (hχb : ∀ x,|χ x|≤1)
    (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand (-centralThickness) 0 →
      weakValue (childCompletionJoin s hs ha k hχ hc hχb hχs p) x=
        χ (WithLp.ofLp x)*(attachedEndPoissonField s (centralT s k.succ p)
          a (-centralThickness) 0 (WithLp.ofLp x)).re ∧
      ∀ i,weakGradient (childCompletionJoin s hs ha k hχ hc hχb hχs p) x i=
        fderiv ℝ χ (WithLp.ofLp x) (Pi.single i 1)*
          (attachedEndPoissonField s (centralT s k.succ p) a (-centralThickness) 0 (WithLp.ofLp x)).re+
        χ (WithLp.ofLp x)*fderiv ℝ (fun y =>
          (attachedEndPoissonField s (centralT s k.succ p) a (-centralThickness) 0 y).re)
          (WithLp.ofLp x) (Pi.single i 1) := by
  have h₀ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (childLocalComponentCLM_end_value s hs ha k hχ hc p.val))
  have h₁ (i : Fin 3) := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      (childLocalComponentCLM_end_gradient s hs ha k hχ hc p.val i))
  have hjet := physicalFourJetCLM_ae
    (fun i => childLocalComponentCLM s hs ha k hχ hc i p.val)
  filter_upwards [hjet,h₀,ae_all_iff.mpr h₁] with x hj hv hg hb
  constructor
  · change WithLp.ofLp ((childLocalJetCLM s hs ha k hχ hc p.val) x) 0=_
    exact (congrArg (fun z : JetFiber => WithLp.ofLp z 0) hj).trans (hv hb)
  · intro i
    change WithLp.ofLp ((childLocalJetCLM s hs ha k hχ hc p.val) x) i.succ=_
    exact (congrArg (fun z : JetFiber => WithLp.ofLp z i.succ) hj).trans (hg i hb)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_CentralSeamCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceJoinInner_bounds {y : Fin 3 → ℝ}
    (hy : -2*centralThickness ≤ sourceCollarTime y) :
    |y 0|≤1604/1000 ∧ |y 1|≤1002/1000 ∧ |y 2|≤1004/1000 := by
  have hh := (sourceCollarTime_ge_iff y (-2*centralThickness)).mp hy
  have hx := (le_max_left (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  have hy' := (le_max_right (|y 0|/sourceLength) (|y 1|)).trans hh.2.2
  norm_num [centralThickness,sourceRadialWidth,sourceHole,sourceLength] at hx hy' hh ⊢
  exact ⟨by linarith,by linarith,by linarith [hh.1]⟩

lemma sourceJoinChild_far_parent (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : -2*centralThickness ≤ sourceCollarTime y) :
    2*centralThickness ≤ sourceCollarTime (sourceChildCoordinates (actualChildSign k) y) := by
  obtain ⟨h₀,h₁,h₂⟩ := sourceJoinInner_bounds hy
  have hsign : |actualChildSign k|=1 := by fin_cases k <;> norm_num [actualChildSign]
  have ha : |actualChildSign k*sourceOffset|=sourceOffset := by
    rw [abs_mul,hsign,one_mul]; norm_num [sourceOffset]
  have hu := abs_add_le (sourceScale*y 1) (actualChildSign k*sourceOffset)
  rw [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale]),ha] at hu
  have hl := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+actualChildSign k*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+actualChildSign k*sourceOffset)=
    actualChildSign k*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at hl
  apply (sourceCollarTime_ge_iff _ _).mpr
  change |sourceScale*y 2|≤_ ∧ _≤ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
    (|sourceScale*y 0|) ∧ max (|sourceScale*y 1+actualChildSign k*sourceOffset|/sourceLength)
      (|sourceScale*y 0|)≤_
  simp only [abs_mul,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])]
  constructor
  · norm_num [sourceScale,centralThickness]; linarith
  · constructor
    · apply le_trans _ (le_max_left _ _)
      norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
      linarith
    · apply max_le
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith
      · norm_num [sourceHole,sourceRadialWidth,sourceLength,sourceScale,sourceOffset,centralThickness] at *
        linarith

lemma centralPhysical_parent_face_not_interior {y : Fin 3 → ℝ}
    (hy : sourceCollarTime y=centralThickness) : y∉interior centralPhysical := by
  let g : ℝ → (Fin 3 → ℝ) := fun t => sourceAngularCollar t (sourcePhysicalAngles y)
  have hg : Continuous g := continuous_uncurry_sourceAngularCollar.comp
    (continuous_id.prodMk continuous_const)
  have hz : centralThickness∈closure (Ioo 0 centralThickness) := by
    rw [closure_Ioo (show (0:ℝ)≠centralThickness by norm_num [centralThickness])]
    exact ⟨by norm_num [centralThickness],le_rfl⟩
  have hin : g '' Ioo 0 centralThickness ⊆ (interior centralPhysical)ᶜ := by
    rintro _ ⟨t,ht,rfl⟩ hn
    have he := sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
      ⟨by linarith [ht.1],ht.2.le.trans (by norm_num [centralThickness])⟩) (sourcePhysicalAngles y)
    have hp := ((centralPhysical_time_iff (g t)).mp (interior_subset hn)).1
    change centralThickness ≤ sourceCollarTime (sourceAngularCollar t (sourcePhysicalAngles y)) at hp
    rw [he] at hp
    exact (not_le_of_gt ht.2) hp
  have hmem := closure_minimal hin isOpen_interior.isClosed_compl
    (image_closure_subset_closure_image hg ⟨centralThickness,hz,rfl⟩)
  have he := sourcePhysicalCoordinates_right
    (show sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100) by rw [hy]; norm_num [centralThickness])
  rw [hy] at he
  simpa only [g,he,Set.mem_compl_iff] using hmem

lemma centralJoinPartition_parent_one {y : Fin 3 → ℝ}
    (hy : sourceCollarTime y=centralThickness) :
    centralJoinPartition 1=ᶠ[𝓝 y] (fun _ => 1) := by
  have hc : y∈centralPhysical := parentBand_central
    (show y∈sourceClosedCollarBand centralThickness (2*centralThickness) by
      change sourceCollarTime y∈Icc centralThickness (2*centralThickness)
      rw [hy]; constructor <;> norm_num [centralThickness])
  have hi : y∉tsupport (centralJoinPartition 0) := fun h =>
    centralPhysical_parent_face_not_interior hy (centralJoinPartition_subordinate 0 h)
  have hj (k : Fin 2) : y∉tsupport (centralJoinPartition (centralChildPatch k)) := by
    intro h
    have hlocal := centralJoinPartition_subordinate (centralChildPatch k) h
    have ht : -2*centralThickness ≤ sourceCollarTime
        ((sourceChildHomeomorph (actualChildSign k)).symm y) := by
      fin_cases k
      · change sourceCollarTime ((sourceChildHomeomorph 1).symm y)∈Ioo (-2*centralThickness) 0 at hlocal
        exact hlocal.1.le
      · change sourceCollarTime ((sourceChildHomeomorph (-1)).symm y)∈Ioo (-2*centralThickness) 0 at hlocal
        exact hlocal.1.le
    have hp := sourceJoinChild_far_parent k ht
    have he : sourceChildCoordinates (actualChildSign k)
        ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
    rw [he,hy] at hp
    norm_num [centralThickness] at hp
  have h₀ := notMem_tsupport_iff_eventuallyEq.mp hi
  have h₂ := notMem_tsupport_iff_eventuallyEq.mp (hj 0)
  have h₃ := notMem_tsupport_iff_eventuallyEq.mp (hj 1)
  filter_upwards [centralJoinPartition_eventually_sum hc,h₀,h₂,h₃] with z hz h₀ h₂ h₃
  change centralJoinPartition 0 z=0 at h₀
  change centralJoinPartition 2 z=0 at h₂
  change centralJoinPartition 3 z=0 at h₃
  simpa only [Fin.sum_univ_four,h₀,h₂,h₃,zero_add,add_zero] using hz

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Walls_ChildSeamCutoff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceJoinChildren_exclusive (y : Fin 3 → ℝ)
    (h₀ : -2*centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y))
    (h₁ : -2*centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)) : False := by
  have ha := (sourceJoinInner_bounds h₀).2.1
  have hb := (sourceJoinInner_bounds h₁).2.1
  change |(y 0 - actualChildSign 0 * sourceOffset)/sourceScale| ≤ _ at ha
  change |(y 0 - actualChildSign 1 * sourceOffset)/sourceScale| ≤ _ at hb
  norm_num [actualChildSign] at ha hb
  rw [abs_div,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at ha hb
  have ha' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp ha)
  have hb' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp hb)
  norm_num [sourceScale,sourceOffset] at ha' hb'
  linarith [ha'.1,hb'.2]

lemma sourceJoinChild_other (k j : Fin 2) (hkj : k≠j) {y : Fin 3 → ℝ}
    (hy : -2*centralThickness ≤ sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)) :
    sourceCollarTime ((sourceChildHomeomorph (actualChildSign j)).symm y)< -2*centralThickness := by
  by_contra h
  have hj := le_of_not_gt h
  fin_cases k <;> fin_cases j
  · exact hkj rfl
  · exact sourceJoinChildren_exclusive y hy hj
  · exact sourceJoinChildren_exclusive y hj hy
  · exact hkj rfl

lemma centralPhysical_child_face_not_interior (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)= -centralThickness) :
    y∉interior centralPhysical := by
  let z := (sourceChildHomeomorph (actualChildSign k)).symm y
  let g : ℝ → (Fin 3 → ℝ) := fun t => sourceChildCoordinates (actualChildSign k)
    (sourceAngularCollar t (sourcePhysicalAngles z))
  have hg : Continuous g := (sourceChildCoordinates_contDiff _).continuous.comp
    (continuous_uncurry_sourceAngularCollar.comp (continuous_id.prodMk continuous_const))
  have hz : -centralThickness∈closure (Ioo (-centralThickness) 0) := by
    rw [closure_Ioo (show -centralThickness≠(0:ℝ) by norm_num [centralThickness])]
    exact ⟨le_rfl,by norm_num [centralThickness]⟩
  have hin : g '' Ioo (-centralThickness) 0 ⊆ (interior centralPhysical)ᶜ := by
    rintro _ ⟨t,ht,rfl⟩ hn
    have he := sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
      ⟨(show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans ht.1.le,
        by linarith [ht.2]⟩) (sourcePhysicalAngles z)
    have hp := ((centralPhysical_time_iff (g t)).mp (interior_subset hn)).2 k
    have hi : (sourceChildHomeomorph (actualChildSign k)).symm (g t)=
        sourceAngularCollar t (sourcePhysicalAngles z) :=
      (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply _
    rw [hi,he] at hp
    exact (not_le_of_gt ht.1) hp
  have hmem := closure_minimal hin isOpen_interior.isClosed_compl
    (image_closure_subset_closure_image hg ⟨-centralThickness,hz,rfl⟩)
  have he := sourcePhysicalCoordinates_right
    (show sourceCollarTime z∈Icc (-(1:ℝ)/100) (1/100) by
      change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)∈_
      rw [hy]
      norm_num [centralThickness])
  change sourceAngularCollar (sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y))
    (sourcePhysicalAngles z)=z at he
  rw [hy] at he
  have he' : sourceChildCoordinates (actualChildSign k) z=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  simpa only [g,he,he',Set.mem_compl_iff] using hmem

lemma centralJoinPartition_child_one (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)= -centralThickness) :
    centralJoinPartition (centralChildPatch k)=ᶠ[𝓝 y] (fun _ => 1) := by
  have hb : (sourceChildHomeomorph (actualChildSign k)).symm y∈
      sourceClosedCollarBand (-2*centralThickness) (-centralThickness) := by
    change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)∈Icc _ _
    rw [hy]; constructor <;> norm_num [centralThickness]
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  have hc : y∈centralPhysical := by
    have hh := childBand_central k hb
    rw [he] at hh
    exact hh
  have hi : y∉tsupport (centralJoinPartition 0) := fun h =>
    centralPhysical_child_face_not_interior k hy (centralJoinPartition_subordinate 0 h)
  have hfar := sourceJoinChild_far_parent k hb.1
  rw [he] at hfar
  have hp : y∉tsupport (centralJoinPartition 1) := by
    intro h
    have hh := centralJoinPartition_subordinate 1 h
    change sourceCollarTime y∈Ioo 0 (2*centralThickness) at hh
    exact (not_lt_of_ge hfar) hh.2
  have hj (j : Fin 2) (hjk : k≠j) : y∉tsupport (centralJoinPartition (centralChildPatch j)) := by
    intro h
    have hh := centralJoinPartition_subordinate (centralChildPatch j) h
    have hlocal : -2*centralThickness < sourceCollarTime
        ((sourceChildHomeomorph (actualChildSign j)).symm y) := by
      fin_cases j
      · change sourceCollarTime ((sourceChildHomeomorph 1).symm y)∈Ioo (-2*centralThickness) 0 at hh
        exact hh.1
      · change sourceCollarTime ((sourceChildHomeomorph (-1)).symm y)∈Ioo (-2*centralThickness) 0 at hh
        exact hh.1
    exact (not_lt_of_ge (sourceJoinChild_other k j hjk hb.1).le) hlocal
  have h₀ := notMem_tsupport_iff_eventuallyEq.mp hi
  have h₁ := notMem_tsupport_iff_eventuallyEq.mp hp
  have hsum := centralJoinPartition_eventually_sum hc
  fin_cases k
  · have hother := notMem_tsupport_iff_eventuallyEq.mp (hj 1 (by decide))
    filter_upwards [h₀,h₁,hsum,hother] with z h₀ h₁ hz h₃
    change centralJoinPartition 0 z=0 at h₀
    change centralJoinPartition 1 z=0 at h₁
    change centralJoinPartition 3 z=0 at h₃
    change centralJoinPartition 2 z=1
    simpa only [Fin.sum_univ_four,h₀,h₁,h₃,zero_add,add_zero] using hz
  · have hother := notMem_tsupport_iff_eventuallyEq.mp (hj 0 (by decide))
    filter_upwards [h₀,h₁,hsum,hother] with z h₀ h₁ hz h₂
    change centralJoinPartition 0 z=0 at h₀
    change centralJoinPartition 1 z=0 at h₁
    change centralJoinPartition 2 z=0 at h₂
    change centralJoinPartition 3 z=1
    simpa only [Fin.sum_univ_four,h₀,h₁,h₂,zero_add,add_zero] using hz

lemma centralJoinChildCutoff_one (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : sourceCollarTime y= -centralThickness) :
    centralJoinChildCutoff k=ᶠ[𝓝 y] (fun _ => 1) := by
  have he : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  have hh := centralJoinPartition_child_one k
    (show sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y))= -centralThickness by rw [he]; exact hy)
  exact hh.comp_tendsto (sourceChildCoordinates_contDiff _).continuous.continuousAt

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ChildComplementPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem centralChild_complement_partition (k : Fin 2) :
    ∃ (l : ℝ) (η : (Fin 3 → ℝ) → ℝ),-centralThickness<l ∧ l<0 ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) η ∧ HasCompactSupport η ∧
      (∀ y,|η y|≤1) ∧ tsupport η⊆sourceClosedCollarBand l (centralThickness/2) ∧
      (∀ y,sourceCollarTime y≤-centralThickness → η=ᶠ[𝓝 y] 0) ∧
      (∀ y∈sourceClosedCollarBand (-centralThickness) 0,
        (fun z => centralJoinChildCutoff k z+η z)=ᶠ[𝓝 y] (fun _ => 1)) := by
  let χ : (Fin 3 → ℝ) → ℝ := centralJoinChildCutoff k
  let q := fun y => 1-χ y
  let K := sourceClosedCollarBand (-centralThickness) 0 ∩ tsupport q
  have hK : IsCompact K :=
    (isCompact_sourceClosedCollarBand (show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness])
      (show (0:ℝ)≤1/100 by norm_num)).inter_right (isClosed_tsupport q)
  have hKt (y) (hy : y∈K) : -centralThickness < sourceCollarTime y := by
    apply lt_of_le_of_ne hy.1.1
    intro he
    have hn : y∉tsupport q := notMem_tsupport_iff_eventuallyEq.mpr (by
      filter_upwards [centralJoinChildCutoff_one k he.symm] with z hz
      change 1-χ z=0
      change χ z=1 at hz
      rw [hz]; ring)
    exact hn hy.2
  have hl : ∃ l : ℝ,-centralThickness<l ∧ l<0 ∧ ∀ y∈K,l < sourceCollarTime y := by
    by_cases hn : K.Nonempty
    · obtain ⟨y,hy,hmin⟩ := hK.exists_isMinOn hn locallyLipschitz_sourceCollarTime.continuous.continuousOn
      refine ⟨(sourceCollarTime y-centralThickness)/2,?_,?_,?_⟩
      · linarith [hKt y hy]
      · have hp := hy.1.2
        have : (0:ℝ) < centralThickness := by norm_num [centralThickness]
        linarith
      · intro z hz
        have hh : sourceCollarTime y ≤ sourceCollarTime z := hmin hz
        linarith [hKt y hy]
    · refine ⟨-centralThickness/2,by norm_num [centralThickness],by norm_num [centralThickness],?_⟩
      intro y hy
      exact (hn ⟨y,hy⟩).elim
  obtain ⟨l,hl,hl₀,hlK⟩ := hl
  have hl' : -(1:ℝ)/100≤l := (show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hl.le
  have hbig := isCompact_sourceClosedCollarBand hl'
    (show centralThickness/2≤1/100 by norm_num [centralThickness])
  have hi : K⊆interior (sourceClosedCollarBand l (centralThickness/2)) := by
    intro y hy
    apply mem_interior_iff_mem_nhds.mpr
    have hm := locallyLipschitz_sourceCollarTime.continuous.continuousAt
      (isOpen_Ioo.mem_nhds (show sourceCollarTime y∈Ioo l (centralThickness/2) from
        ⟨hlK y hy,by have := hy.1.2; dsimp [centralThickness] at *; linarith⟩))
    exact mem_of_superset hm (fun z hz => ⟨hz.1.le,hz.2.le⟩)
  obtain ⟨ψ,hψ1,hψ0,hψb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hK.isClosed hi (n:=↑(⊤:ℕ∞))
  have hψc : HasCompactSupport ψ := HasCompactSupport.intro hbig hψ0
  have hψs : tsupport ψ⊆sourceClosedCollarBand l (centralThickness/2) := by
    apply closure_minimal _ hbig.isClosed
    intro y hy
    by_contra hn
    exact hy (hψ0 y hn)
  let η := fun y => q y*ψ y
  have hηs : tsupport η⊆sourceClosedCollarBand l (centralThickness/2) :=
    tsupport_mul_subset_right.trans hψs
  refine ⟨l,η,hl,hl₀,(contDiff_const.sub (centralJoinChildCutoff_smooth k)).mul ψ.contMDiff.contDiff,
    hψc.mul_left,?_,hηs,?_,?_⟩
  · intro y
    have h₀ := centralJoinPartition.nonneg (centralChildPatch k) (sourceChildCoordinates (actualChildSign k) y)
    have h₁ := centralJoinPartition.le_one (centralChildPatch k) (sourceChildCoordinates (actualChildSign k) y)
    change 0≤χ y at h₀
    change χ y≤1 at h₁
    have h₂ := (hψb y).1
    have h₃ := (hψb y).2
    dsimp only [η,q]
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr h₁) h₂)]
    nlinarith [mul_nonneg h₀ h₂]
  · intro y hy
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hn
    have hle := (hηs hn).1
    linarith
  · intro y hy
    by_cases hk : y∈K
    · have hψ := hψ1.filter_mono (nhds_le_nhdsSet hk)
      filter_upwards [hψ] with z hz
      change centralJoinChildCutoff k z+((1-centralJoinChildCutoff k z)*ψ z)=1
      rw [hz]
      ring
    · have hq : y∉tsupport q := fun hn => hk ⟨hy,hn⟩
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with z hz
      change q z=0 at hz
      change χ z+q z*ψ z=1
      rw [hz,zero_mul,add_zero]
      dsimp only [q] at hz
      linarith

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_ParentComplementPartition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem centralParent_complement_partition :
    ∃ (r : ℝ) (η : (Fin 3 → ℝ) → ℝ),0 < r ∧ r < centralThickness ∧
      ContDiff ℝ (↑(⊤:ℕ∞)) η ∧ HasCompactSupport η ∧
      (∀ y,|η y|≤1) ∧ tsupport η⊆sourceClosedCollarBand (-centralThickness/2) r ∧
      (∀ y∈centralPhysical,η=ᶠ[𝓝 y] 0) ∧
      (∀ y∈sourceClosedCollarBand 0 centralThickness,
        (fun z => centralJoinPartition 1 z+η z)=ᶠ[𝓝 y] (fun _ => 1)) := by
  let χ : (Fin 3 → ℝ) → ℝ := centralJoinPartition 1
  let q := fun y => 1-χ y
  let K := sourceClosedCollarBand 0 centralThickness ∩ tsupport q
  have hK : IsCompact K :=
    (isCompact_sourceClosedCollarBand (show -(1:ℝ)/100≤0 by norm_num)
      (show centralThickness≤1/100 by norm_num [centralThickness])).inter_right (isClosed_tsupport q)
  have hKt (y) (hy : y∈K) : sourceCollarTime y < centralThickness := by
    apply lt_of_le_of_ne hy.1.2
    intro he
    have hn : y∉tsupport q := notMem_tsupport_iff_eventuallyEq.mpr (by
      filter_upwards [centralJoinPartition_parent_one he] with z hz
      change 1-χ z=0
      change χ z=1 at hz
      rw [hz]; ring)
    exact hn hy.2
  have hr : ∃ r : ℝ,0 < r ∧ r < centralThickness ∧ ∀ y∈K,sourceCollarTime y < r := by
    by_cases hn : K.Nonempty
    · obtain ⟨y,hy,hmax⟩ := hK.exists_isMaxOn hn locallyLipschitz_sourceCollarTime.continuous.continuousOn
      refine ⟨(sourceCollarTime y+centralThickness)/2,?_,?_,?_⟩
      · have hp := hy.1.1
        have : (0:ℝ) < centralThickness := by norm_num [centralThickness]
        linarith
      · linarith [hKt y hy]
      · intro z hz
        have hh : sourceCollarTime z ≤ sourceCollarTime y := hmax hz
        linarith [hKt y hy]
    · refine ⟨centralThickness/2,by norm_num [centralThickness],by norm_num [centralThickness],?_⟩
      intro y hy
      exact (hn ⟨y,hy⟩).elim
  obtain ⟨r,hr₀,hr,hrK⟩ := hr
  have hr' : r≤1/100 := hr.le.trans (by norm_num [centralThickness])
  have hbig := isCompact_sourceClosedCollarBand
    (show -(1:ℝ)/100≤-centralThickness/2 by norm_num [centralThickness]) hr'
  have hi : K⊆interior (sourceClosedCollarBand (-centralThickness/2) r) := by
    intro y hy
    apply mem_interior_iff_mem_nhds.mpr
    have hm := locallyLipschitz_sourceCollarTime.continuous.continuousAt
      (isOpen_Ioo.mem_nhds (show sourceCollarTime y∈Ioo (-centralThickness/2) r from
        ⟨by have := hy.1.1; dsimp [centralThickness] at *; linarith,hrK y hy⟩))
    exact mem_of_superset hm (fun z hz => ⟨hz.1.le,hz.2.le⟩)
  obtain ⟨ψ,hψ1,hψ0,hψb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (Fin 3 → ℝ)) hK.isClosed hi (n:=↑(⊤:ℕ∞))
  have hψc : HasCompactSupport ψ := HasCompactSupport.intro hbig hψ0
  have hψs : tsupport ψ⊆sourceClosedCollarBand (-centralThickness/2) r := by
    apply closure_minimal _ hbig.isClosed
    intro y hy
    by_contra hn
    exact hy (hψ0 y hn)
  let η := fun y => q y*ψ y
  have hηs : tsupport η⊆sourceClosedCollarBand (-centralThickness/2) r :=
    tsupport_mul_subset_right.trans hψs
  refine ⟨r,η,hr₀,hr,(contDiff_const.sub (centralJoinPartition_smooth 1)).mul ψ.contMDiff.contDiff,
    hψc.mul_left,?_,hηs,?_,?_⟩
  · intro y
    have h₀ := centralJoinPartition.nonneg 1 y
    have h₁ := centralJoinPartition.le_one 1 y
    have h₂ := (hψb y).1
    have h₃ := (hψb y).2
    dsimp only [η,q,χ]
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr h₁) h₂)]
    nlinarith [mul_nonneg h₀ h₂]
  · intro y hy
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro hn
    have hle := (hηs hn).2
    have hge := ((centralPhysical_time_iff y).mp hy).1
    linarith
  · intro y hy
    by_cases hk : y∈K
    · have hψ := hψ1.filter_mono (nhds_le_nhdsSet hk)
      filter_upwards [hψ] with z hz
      change centralJoinPartition 1 z+((1-centralJoinPartition 1 z)*ψ z)=1
      rw [hz]
      ring
    · have hq : y∉tsupport q := fun hn => hk ⟨hy,hn⟩
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with z hz
      change q z=0 at hz
      change χ z+q z*ψ z=1
      rw [hz,zero_mul,add_zero]
      dsimp only [q] at hz
      linarith

end ScalarConductivity



end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_JoinedPhysicalEnds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem parentAttachedCorrection_supported (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : a<0) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure, WithLp.ofLp x∉sourceClosedCollarBand (-2*centralThickness) (2*centralThickness) →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,centralThickness ≤ sourceCollarTime (WithLp.ofLp x) →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand 0 centralThickness →
        weakValue (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
          centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
          centralJoinPartition_parent_support p+d) x=
          fullAttachedEndValue s (centralT s 0 p) a centralThickness κ (WithLp.ofLp x) ∧
        ∀ i,weakGradient (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
          centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
          centralJoinPartition_parent_support p+d) x i=
          fullAttachedEndGradient s (centralT s 0 p) a centralThickness κ (WithLp.ofLp x) i) := by
  obtain ⟨r,η,hr₀,hr,hη,hηc,hηb,hηs,hηzero,hpart⟩ := centralParent_complement_partition
  obtain ⟨v,hv,hve⟩ := compact_collar_slope_value_gradient (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralJoinPartition_bound 1) ha.ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    κ 0 (2*centralThickness) (by norm_num) (by norm_num [centralThickness]) centralJoinPartition_parent_support
  have hR : 0≤-a*(3*centralThickness/2) :=
    mul_nonneg (neg_nonneg.mpr ha.le) (by norm_num [centralThickness])
  have hT : ∀ t∈Icc (-centralThickness/2) r,
      affineEndTime a centralThickness t∈Icc 0 (-a*(3*centralThickness/2)) := by
    intro t ht
    dsimp only [affineEndTime]
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr (ht.2.trans hr.le))
    · have hm := mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr ht.1)
      nlinarith
  have hpos : ∀ t∈Icc (-centralThickness/2) r,0<a*(t-centralThickness) :=
    fun t ht => mul_pos_of_neg_of_neg ha (sub_neg.mpr (ht.2.trans_lt hr))
  obtain ⟨z,hz,hze⟩ := cut_fullAttachedEnd_H10 s hs (centralT s 0 p) κ ha.ne hR
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    (show -centralThickness/2 ≤ r by
      have ht : (0:ℝ) < centralThickness := by norm_num [centralThickness]
      linarith)
    (by norm_num [centralThickness]) (hr.le.trans (by norm_num [centralThickness]))
    hT hpos hη hηc hηb hηs
  refine ⟨v+z,H10.add_mem hv hz,?_,?_,?_⟩
  · filter_upwards [hve,hze,weakValue_add v z,weakGradient_add v z] with x hx hy hval hgrad hout
    have hχn : WithLp.ofLp x∉tsupport (centralJoinPartition 1) := by
      intro hm
      apply hout
      have h := centralJoinPartition_parent_support hm
      exact ⟨(by norm_num [centralThickness]; linarith [h.1]),h.2⟩
    have hηn : WithLp.ofLp x∉tsupport η := by
      intro hm
      apply hout
      rcases hηs hm with ⟨hlo,hhi⟩
      constructor <;> dsimp [centralThickness] at * <;> linarith
    have hχ0 := image_eq_zero_of_notMem_tsupport hχn
    have hdχ0 := fderiv_of_notMem_tsupport ℝ hχn
    have hη0 := image_eq_zero_of_notMem_tsupport hηn
    have hdη0 := fderiv_of_notMem_tsupport ℝ hηn
    constructor
    · rw [hval]
      simp [hx.1,hy.1,hχ0,hη0]
    · intro i
      rw [hgrad]
      simp [hx.2 i,hy.2 i,hχ0,hη0,hdχ0,hdη0]

  · filter_upwards [hve,hze,weakValue_add v z,weakGradient_add v z] with x hx hy hval hgrad hcentral
    have ht := hcentral
    have hn : a*(sourceCollarTime (WithLp.ofLp x)-centralThickness)≤0 :=
      mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr ht)
    have hηn : WithLp.ofLp x∉tsupport η := by
      intro hm
      have ht' := (hηs hm).2
      exact (not_le.mpr hr) (ht.trans ht')
    have he : η (WithLp.ofLp x)=0 := image_eq_zero_of_notMem_tsupport hηn
    have hd : fderiv ℝ η (WithLp.ofLp x)=0 := fderiv_of_notMem_tsupport ℝ hηn
    constructor
    · rw [hval]
      simp only [Pi.add_apply,hx.1,hy.1,max_eq_left hn,he,mul_zero,zero_mul,add_zero]
    · intro i
      rw [hgrad]
      simp only [WithLp.ofLp_add,Pi.add_apply,hx.2 i,hy.2 i,max_eq_left hn,
        ite_eq_right (not_lt_of_ge hn),he,hd,zero_apply,mul_zero,zero_mul,add_zero]
  · have hne := ae_restrict_of_ae (s:=ball)
      ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
        (sourceColevel_ae_ne (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
          norm_num [centralThickness])))
    have hp : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand 0 centralThickness →
        0<a*(sourceCollarTime (WithLp.ofLp x)-centralThickness) := by
      filter_upwards [hne] with x hx hb
      exact mul_pos_of_neg_of_neg ha (sub_neg.mpr (lt_of_le_of_ne hb.2 hx))
    have hh := fullEnd_partition_jet s (centralT s 0 p) a centralThickness κ
      (centralJoinPartition_smooth 1) hη hpart (v:=v) (z:=z)
      (u:=parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support p) hp
      (parentCompletionJoin_end_ae s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support p) hve hze
    simpa only [add_assoc] using hh

end ScalarConductivity


namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem childAttachedCorrection_supported (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure, WithLp.ofLp x∉sourceClosedCollarBand (-2*centralThickness) (2*centralThickness) →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,sourceCollarTime (WithLp.ofLp x)≤-centralThickness →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand (-centralThickness) 0 →
        weakValue (childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+d) x=
          fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ (WithLp.ofLp x) ∧
        ∀ i,weakGradient (childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+d) x i=
          fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ (WithLp.ofLp x) i) := by
  obtain ⟨l,η,hl,hl₀,hη,hηc,hηb,hηs,hηzero,hpart⟩ := centralChild_complement_partition k
  obtain ⟨v,hv,hve⟩ := compact_collar_slope_value_gradient (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k) ha.ne'
    (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    κ (-2*centralThickness) 0 (by norm_num [centralThickness]) (by norm_num) (centralJoinChildCutoff_support k)
  have hR : 0≤a*(3*centralThickness/2) :=
    mul_nonneg ha.le (by norm_num [centralThickness])
  have hT : ∀ t∈Icc l (centralThickness/2),
      affineEndTime a (-centralThickness) t∈Icc 0 (a*(3*centralThickness/2)) := by
    intro t ht
    dsimp only [affineEndTime]
    constructor
    · exact mul_nonneg ha.le (sub_nonneg.mpr (hl.le.trans ht.1))
    · have hm := mul_nonneg ha.le (sub_nonneg.mpr ht.2)
      nlinarith
  have hpos : ∀ t∈Icc l (centralThickness/2),0<a*(t-(-centralThickness)) :=
    fun t ht => mul_pos ha (sub_pos.mpr (hl.trans_le ht.1))
  obtain ⟨z,hz,hze⟩ := cut_fullAttachedEnd_H10 s hs (centralT s k.succ p) κ ha.ne' hR
    (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
    (show l ≤ centralThickness/2 by
      have ht : (0:ℝ) < centralThickness := by norm_num [centralThickness]
      linarith)
    ((show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hl.le)
    (by norm_num [centralThickness])
    hT hpos hη hηc hηb hηs
  refine ⟨v+z,H10.add_mem hv hz,?_,?_,?_⟩
  · filter_upwards [hve,hze,weakValue_add v z,weakGradient_add v z] with x hx hy hval hgrad hout
    have hχn : WithLp.ofLp x∉tsupport (centralJoinChildCutoff k) := by
      intro hm
      apply hout
      have h := centralJoinChildCutoff_support k hm
      exact ⟨h.1,(by norm_num [centralThickness]; linarith [h.2])⟩
    have hηn : WithLp.ofLp x∉tsupport η := by
      intro hm
      apply hout
      rcases hηs hm with ⟨hlo,hhi⟩
      constructor <;> dsimp [centralThickness] at * <;> linarith
    have hχ0 := image_eq_zero_of_notMem_tsupport hχn
    have hdχ0 := fderiv_of_notMem_tsupport ℝ hχn
    have hη0 := image_eq_zero_of_notMem_tsupport hηn
    have hdη0 := fderiv_of_notMem_tsupport ℝ hηn
    constructor
    · rw [hval]
      simp [hx.1,hy.1,hχ0,hη0]
    · intro i
      rw [hgrad]
      simp [hx.2 i,hy.2 i,hχ0,hη0,hdχ0,hdη0]

  · filter_upwards [hve,hze,weakValue_add v z,weakGradient_add v z] with x hx hy hval hgrad hcentral
    have hn : a*(sourceCollarTime (WithLp.ofLp x)-(-centralThickness))≤0 :=
      mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hcentral)
    have he : η (WithLp.ofLp x)=0 := (hηzero _ hcentral).self_of_nhds
    have hd : fderiv ℝ η (WithLp.ofLp x)=0 := by
      rw [(hηzero _ hcentral).fderiv_eq]
      exact fderiv_const_apply (0:ℝ)
    constructor
    · rw [hval]
      simp only [Pi.add_apply,hx.1,hy.1,max_eq_left hn,he,mul_zero,zero_mul,add_zero]
    · intro i
      rw [hgrad]
      simp only [WithLp.ofLp_add,Pi.add_apply,hx.2 i,hy.2 i,max_eq_left hn,
        ite_eq_right (not_lt_of_ge hn),he,hd,zero_apply,mul_zero,zero_mul,add_zero]
  · have hne := ae_restrict_of_ae (s:=ball)
      ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
        (sourceColevel_ae_ne (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by
          norm_num [centralThickness])))
    have hp : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈sourceClosedCollarBand (-centralThickness) 0 →
        0<a*(sourceCollarTime (WithLp.ofLp x)-(-centralThickness)) := by
      filter_upwards [hne] with x hx hb
      exact mul_pos ha (sub_pos.mpr (lt_of_le_of_ne hb.1 (Ne.symm hx)))
    have hh := fullEnd_partition_jet s (centralT s k.succ p) a (-centralThickness) κ
      (centralJoinChildCutoff_smooth k) hη hpart (v:=v) (z:=z)
      (u:=childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) p) hp
      (childCompletionJoin_end_ae s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) p) hve hze
    simpa only [add_assoc] using hh

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Sobolev_ChildFullEndH1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childH10Transport_local_jet (k : Fin 2) (u : H10)
    {D : Set (Fin 3 → ℝ)}
    (hD : ∀ y∈D,WithLp.toLp 2 y∈ball)
    (V : (Fin 3 → ℝ) → ℝ) (G : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue u.val x=V (WithLp.ofLp x) ∧
      ∀ i,weakGradient u.val x i=G (WithLp.ofLp x) i) :
    ∀ᵐ x∂ballMeasure,
      (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈D →
      weakValue (childH10Transport k u) x=
        V ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) ∧
      ∀ i,weakGradient (childH10Transport k u) x i=
        sourceScale⁻¹*G ((sourceChildHomeomorph (actualChildSign k)).symm
          (WithLp.ofLp x)) (childAxis i) := by
  classical
  let f : (Fin 3 → ℝ) → JetFiber := fun y =>
    if WithLp.toLp 2 y∈ball then u.val.val (WithLp.toLp 2 y) else 0
  have hj := childTransportJetCLM_ae_of_ae k u.val.val f
    (ballWholePiJetCLM_ae_of_ae u.val.val
      (fun y => u.val.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl))
  have he₀ := (ae_restrict_iff' (show MeasurableSet ball from
    Metric.isOpen_ball.measurableSet)).mp he
  have he₁ := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae he₀
  have he₂ := (sourceChildInverse_quasi (actualChildSign k)).ae he₁
  have he₃ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae he₂)
  filter_upwards [hj,he₃] with x hj hx hm
  have hb := hD _ hm
  have hloc := hx hb hm
  constructor
  · change (childTransportJetCLM k u.val.val x) 0=_
    rw [hj]
    change (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))) 0=_
    rw [show f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))=
      u.val.val (WithLp.toLp 2 ((sourceChildHomeomorph (actualChildSign k)).symm
        (WithLp.ofLp x))) from ite_eq_left hb]
    exact hloc.1
  · intro i
    change (childTransportJetCLM k u.val.val x) i.succ=_
    rw [hj]
    change sourceScale⁻¹*(f ((sourceChildHomeomorph (actualChildSign k)).symm
      (WithLp.ofLp x))) (childAxis i).succ=_
    rw [show f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))=
      u.val.val (WithLp.toLp 2 ((sourceChildHomeomorph (actualChildSign k)).symm
        (WithLp.ofLp x))) from ite_eq_left hb]
    exact congrArg (fun q : ℝ => sourceScale⁻¹*q) (hloc.2 (childAxis i))

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalChildAttachedCorrection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma childH10Transport_zero_on (k : Fin 2) (u : H10) (D : Set (Fin 3 → ℝ))
    (he : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D →
      weakValue u.val x=0 ∧ ∀ i,weakGradient u.val x i=0) :
    ∀ᵐ x∂ballMeasure,
      (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈D →
      weakValue (childH10Transport k u) x=0 ∧
      ∀ i,weakGradient (childH10Transport k u) x i=0 := by
  classical
  let f : (Fin 3 → ℝ) → JetFiber := fun y =>
    if WithLp.toLp 2 y∈ball then u.val.val (WithLp.toLp 2 y) else 0
  have hj := childTransportJetCLM_ae_of_ae k u.val.val f
    (ballWholePiJetCLM_ae_of_ae u.val.val
      (fun y => u.val.val (WithLp.toLp 2 y)) (by filter_upwards [] with x; rfl))
  have he₀ := (ae_restrict_iff' (show MeasurableSet ball from
    Metric.isOpen_ball.measurableSet)).mp he
  have he₁ := (PiLp.volume_preserving_toLp (Fin 3)).quasiMeasurePreserving.ae he₀
  have he₂ := (sourceChildInverse_quasi (actualChildSign k)).ae he₁
  have he₃ := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae he₂)
  filter_upwards [hj,he₃] with x hj hx hm
  have hf : f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))=0 := by
    dsimp only [f]
    split_ifs with hb
    · have hh := hx hb hm
      ext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hh.1
      · exact hh.2 j
    · rfl
  constructor
  · change (childTransportJetCLM k u.val.val x) 0=0
    rw [hj]
    change (f ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))) 0=0
    rw [hf]
    rfl
  · intro i
    change (childTransportJetCLM k u.val.val x) i.succ=0
    rw [hj]
    change sourceScale⁻¹*(f ((sourceChildHomeomorph (actualChildSign k)).symm
      (WithLp.ofLp x))) (childAxis i).succ=0
    rw [hf]
    simp

lemma childH10Transport_add (k : Fin 2) (u v : H1) (hu : u∈H10) (hv : v∈H10) :
    childH10Transport k ⟨u+v,H10.add_mem hu hv⟩=
      childH10Transport k ⟨u,hu⟩+childH10Transport k ⟨v,hv⟩ := by
  apply Subtype.ext
  change childTransportJetCLM k (u.val+v.val)=
    childTransportJetCLM k u.val+childTransportJetCLM k v.val
  exact map_add (childTransportJetCLM k) u.val v.val

lemma physicalChildCompletionJoin_eq_transport (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (p : centralEnergySpace s) :
    physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
      (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
      (centralJoinChildCutoff_support k) p=
    childH10Transport k ⟨childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
      (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
      (centralJoinChildCutoff_support k) p,childCompletionJoin_mem_H10 s hs ha k _ _ _ _ p⟩ := rfl

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalAttachedAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem physicalChildAttachedCorrection_supported (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) (κ : ℝ) (p : centralEnergySpace s) :
    ∃ d : H1,d∈H10 ∧
      (∀ᵐ x∂ballMeasure,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))≤-centralThickness →
        weakValue d x=0 ∧ ∀ i,weakGradient d x i=0) ∧
      (∀ᵐ x∂ballMeasure,
        (sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)∈
          sourceClosedCollarBand (-centralThickness) 0 →
        weakValue (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+d) x=
          fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ
            ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) ∧
        ∀ i,weakGradient (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+d) x i=sourceScale⁻¹*
          fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ
            ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)) (childAxis i)) := by
  obtain ⟨d,hd,hds,hdzero,hde⟩ := childAttachedCorrection_supported s hs ha k κ p
  refine ⟨childH10Transport k ⟨d,hd⟩,childH10Transport_mem_H10 k _,?_,?_⟩
  · have hh := childH10Transport_zero_on k ⟨d,hd⟩
      {y | sourceCollarTime y≤-centralThickness} hdzero
    exact hh
  · let u := childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
      (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
      (centralJoinChildCutoff_support k) p
    have hu : u∈H10 := childCompletionJoin_mem_H10 s hs ha k _ _ _ _ p
    have hh := childH10Transport_local_jet k ⟨u+d,H10.add_mem hu hd⟩
      (D:=sourceClosedCollarBand (-centralThickness) 0)
      (fun y hy => sourceBand_mem_ball ⟨
        (show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hy.1,
        hy.2.trans (by norm_num)⟩)
      (fullAttachedEndValue s (centralT s k.succ p) a (-centralThickness) κ)
      (fullAttachedEndGradient s (centralT s k.succ p) a (-centralThickness) κ) hde
    have hsum : childH10Transport k ⟨u+d,H10.add_mem hu hd⟩=
        physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
          (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
          (centralJoinChildCutoff_support k) p+childH10Transport k ⟨d,hd⟩ := by
      rw [childH10Transport_add k u d hu hd]
      exact congrArg (fun q : H1 => q+childH10Transport k ⟨d,hd⟩)
        (physicalChildCompletionJoin_eq_transport s hs ha k p).symm
    rw [hsum] at hh
    exact hh

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma weak_jet_eq_iff (u : H1) (x : R3) (v : ℝ) (g : Fin 3 → ℝ) :
    u.val x=physicalJet v g ↔ weakValue u x=v ∧ ∀ i,weakGradient u x i=g i := by
  constructor
  · intro h
    constructor
    · exact congrArg (fun z : JetFiber => z 0) h
    · intro i
      exact congrArg (fun z : JetFiber => z i.succ) h
  · rintro ⟨hv,hg⟩
    ext i
    exact Fin.cases hv hg i

lemma weak_jet_zero_iff (u : H1) (x : R3) :
    u.val x=0 ↔ weakValue u x=0 ∧ ∀ i,weakGradient u x i=0 := by
  have he : physicalJet 0 (fun _ => 0)=0 := by ext i; exact Fin.cases rfl (fun _ => rfl) i
  rw [←he,weak_jet_eq_iff]

lemma H1JetOn.mono {u : H1} {D E : Set (Fin 3 → ℝ)} {f : R3 → JetFiber}
    (h : H1JetOn u D f) (hED : E⊆D) : H1JetOn u E f := by
  filter_upwards [h] with x hx hy
  exact hx (hED hy)

lemma H1JetOn.add {u v : H1} {D : Set (Fin 3 → ℝ)} {f g : R3 → JetFiber}
    (hu : H1JetOn u D f) (hv : H1JetOn v D g) :
    H1JetOn (u+v) D (fun x => f x+g x) := by
  filter_upwards [hu,hv,H1_add_jet_ae u v] with x hx hy he hm
  rw [he,hx hm,hy hm]

lemma H1JetOn.add_zero {u v : H1} {D : Set (Fin 3 → ℝ)} {f : R3 → JetFiber}
    (hu : H1JetOn u D f) (hv : H1JetOn v D (fun _ => 0)) : H1JetOn (u+v) D f := by
  simpa only [_root_.add_zero] using hu.add hv

lemma H1JetOn.zero_add {u v : H1} {D : Set (Fin 3 → ℝ)} {f : R3 → JetFiber}
    (hu : H1JetOn u D (fun _ => 0)) (hv : H1JetOn v D f) : H1JetOn (u+v) D f := by
  simpa only [_root_.zero_add] using hu.add hv

lemma H1JetOn.of_weak {u : H1} {D : Set (Fin 3 → ℝ)} {v : R3 → ℝ}
    {g : R3 → Fin 3 → ℝ}
    (h : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → weakValue u x=v x ∧
      ∀ i,weakGradient u x i=g x i) : H1JetOn u D (fun x => physicalJet (v x) (g x)) := by
  filter_upwards [h] with x hx hm
  exact (weak_jet_eq_iff u x _ _).mpr (hx hm)

lemma H1JetOn.zero_of_weak {u : H1} {D : Set (Fin 3 → ℝ)}
    (h : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈D → weakValue u x=0 ∧
      ∀ i,weakGradient u x i=0) : H1JetOn u D (fun _ => 0) := by
  filter_upwards [h] with x hx hm
  exact (weak_jet_zero_iff u x).mpr (hx hm)

end ScalarConductivity
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalBlockEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma physicalBlockRegion_central_end_exclusive_ae :
    ∀ᵐ y∂(volume : Measure (Fin 3 → ℝ)),
      y∈centralPhysical → ∀ i : Fin 3,y∉physicalEndRegion i := by
  have hparent := sourceColevel_ae_ne
    (show centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness])
  have hchild (k : Fin 2) := (sourceChildInverse_quasi (actualChildSign k)).ae
    (sourceColevel_ae_ne
      (show -centralThickness∈Icc (-(1:ℝ)/100) (1/100) by norm_num [centralThickness]))
  filter_upwards [hparent,hchild 0,hchild 1] with y hp hc₀ hc₁ hy i hi
  have ht := (centralPhysical_time_iff y).mp hy
  fin_cases i
  · change sourceCollarTime y∈Icc 0 centralThickness at hi
    exact hp (le_antisymm hi.2 ht.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 0)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hc₀ (le_antisymm (ht.2 0) hi.1)
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign 1)).symm y)
      ∈Icc (-centralThickness) 0 at hi
    exact hc₁ (le_antisymm (ht.2 1) hi.1)

end ScalarConductivity

end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Branching_PhysicalJoin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma physical_localized_jet_zero
    {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (f : Fin 4 → Lp ℝ 2 (volume : Measure (Fin 3 → ℝ))) :
    let g : Fin 4 → Lp ℝ 2 (volume : Measure (Fin 3 → ℝ)) :=
      Fin.cases (compactMultiplierCLM hχ.continuous hc (f 0))
        (fun i => compactMultiplierCLM ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hc.fderiv_apply ℝ (Pi.single i 1)) (f 0) +
          compactMultiplierCLM hχ.continuous hc (f i.succ))
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉tsupport χ → physicalFourJetCLM g x=0 := by
  intro g
  have h₀ := compactMultiplierCLM_ae hχ.continuous hc (f 0)
  have hᵢ (i : Fin 3) : g i.succ=ᵐ[volume] fun y =>
      fderiv ℝ χ y (Pi.single i 1)*f 0 y+χ y*f i.succ y := by
    apply (Lp.coeFn_add _ _).trans
    filter_upwards [compactMultiplierCLM_ae
      ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (Pi.single i 1)) (f 0),
      compactMultiplierCLM_ae hχ.continuous hc (f i.succ)] with y h₁ h₂
    exact congrArg₂ (·+·) h₁ h₂
  have h₀' := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae_eq_comp h₀)
  have hᵢ' := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae (ae_all_iff.mpr hᵢ))
  filter_upwards [physicalFourJetCLM_ae g,h₀',hᵢ'] with x hx h₀x hᵢx hn
  rw [hx]
  dsimp only [Function.comp_apply] at h₀x
  have hχ0 := image_eq_zero_of_notMem_tsupport hn
  have hdχ0 := fderiv_of_notMem_tsupport ℝ hn
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change compactMultiplierCLM hχ.continuous hc (f 0) (WithLp.ofLp x)=0
    rw [h₀x,hχ0,zero_mul]
  · change g j.succ (WithLp.ofLp x)=0
    rw [hᵢx j]
    simp [hχ0,hdχ0]

lemma weak_jet_zero_of_val_zero (u : H1) {x : R3} (h : u.val x=0) :
    weakValue u x=0 ∧ ∀ i,weakGradient u x i=0 := by
  constructor
  · change (u.val x) 0=0
    rw [h]; rfl
  · intro i
    change (u.val x) i.succ=0
    rw [h]; rfl

lemma parentCompletionJoin_zero_off_support (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : a<0) {χ : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (hχb : ∀ y,|χ y|≤1) (hχs : tsupport χ⊆sourceClosedCollarBand 0 (2*centralThickness))
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉tsupport χ →
      weakValue (parentCompletionJoin s hs ha hχ hc hχb hχs p) x=0 ∧
      ∀ i,weakGradient (parentCompletionJoin s hs ha hχ hc hχb hχs p) x i=0 := by
  have hh := physical_localized_jet_zero hχ hc (fun i => parentJoinedComponentCLM s hs ha i p.val)
  filter_upwards [hh] with x hx hn
  exact weak_jet_zero_of_val_zero _ (hx hn)

lemma childCompletionJoin_zero_off_support (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (k : Fin 2) {χ : (Fin 3 → ℝ) → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (hχb : ∀ y,|χ y|≤1) (hχs : tsupport χ⊆sourceClosedCollarBand (-2*centralThickness) 0)
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉tsupport χ →
      weakValue (childCompletionJoin s hs ha k hχ hc hχb hχs p) x=0 ∧
      ∀ i,weakGradient (childCompletionJoin s hs ha k hχ hc hχb hχs p) x i=0 := by
  have hh := physical_localized_jet_zero hχ hc (fun i => childJoinedComponentCLM s hs ha k i p.val)
  filter_upwards [hh] with x hx hn
  exact weak_jet_zero_of_val_zero _ (hx hn)

lemma centralInteriorCompletion_zero_off_support (s : Fin 3 → ℝ)
    {χ : (Fin 3 → ℝ) → ℝ} (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (hχs : tsupport χ⊆centralPhysical) (hχB : ∀ y∈tsupport χ,WithLp.toLp 2 y∈ball)
    (p : centralEnergySpace s) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∉tsupport χ →
      weakValue (centralInteriorCompletion s hχ hc hχs hχB p) x=0 ∧
      ∀ i,weakGradient (centralInteriorCompletion s hχ hc hχs hχB p) x i=0 := by
  have hh := physical_localized_jet_zero hχ hc
    (fun i => centralPhysicalWholeCLM (centralAmbientComponent s i p.val))
  filter_upwards [hh] with x hx hn
  exact weak_jet_zero_of_val_zero _ (hx hn)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceJoin_children_separate (k l : Fin 2) (hkl : k≠l) {y : Fin 3 → ℝ}
    (hk : -2*centralThickness ≤ sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y))
    (hl : -2*centralThickness ≤ sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign l)).symm y)) : False := by
  have h₁ := (sourceJoinInner_bounds hk).2.1
  have h₂ := (sourceJoinInner_bounds hl).2.1
  change |(y 0-actualChildSign k*sourceOffset)/sourceScale|≤1002/1000 at h₁
  change |(y 0-actualChildSign l*sourceOffset)/sourceScale|≤1002/1000 at h₂
  rw [abs_div,abs_of_pos (show 0 < sourceScale by norm_num [sourceScale])] at h₁ h₂
  have h₁' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp h₁)
  have h₂' := abs_le.mp ((div_le_iff₀ (show 0 < sourceScale by norm_num [sourceScale])).mp h₂)
  fin_cases k <;> fin_cases l
  · exact hkl rfl
  · norm_num [actualChildSign,sourceScale,sourceOffset] at h₁' h₂'
    linarith [h₁'.1,h₂'.2]
  · norm_num [actualChildSign,sourceScale,sourceOffset] at h₁' h₂'
    linarith [h₂'.1,h₁'.2]
  · exact hkl rfl

lemma physicalOtherEnd_child_time (k : Fin 2) (i : Fin 3) (hik : i≠k.succ)
    {y : Fin 3 → ℝ} (hy : y∈physicalEndRegion i) :
    sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)< -2*centralThickness := by
  by_contra hn
  have ht := le_of_not_gt hn
  revert hy hik
  refine Fin.cases ?_ (fun l => ?_) i
  · intro _ hy
    have hh := sourceJoinChild_far_parent k ht
    have he : sourceChildCoordinates (actualChildSign k)
        ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
      (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
    rw [he] at hh
    change sourceCollarTime y∈Icc 0 centralThickness at hy
    norm_num [centralThickness] at hh hy
    linarith [hy.2]
  · intro hik hy
    have hl : -2*centralThickness ≤ sourceCollarTime
        ((sourceChildHomeomorph (actualChildSign l)).symm y) := by
      change sourceCollarTime ((sourceChildHomeomorph (actualChildSign l)).symm y)
        ∈Icc (-centralThickness) 0 at hy
      have := hy.1
      dsimp [centralThickness] at *
      linarith
    exact sourceJoin_children_separate k l (fun he => hik (congrArg Fin.succ he.symm)) ht hl

lemma physicalChildEnd_parent_time (k : Fin 2) {y : Fin 3 → ℝ}
    (hy : y∈physicalEndRegion k.succ) : 2*centralThickness ≤ sourceCollarTime y := by
  have hh := physicalChildEnd_far_parent k hy
  have he : sourceChildCoordinates (actualChildSign k)
      ((sourceChildHomeomorph (actualChildSign k)).symm y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y
  rwa [he] at hh

lemma parent_join_zero_on_children (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : a<0) (p : centralEnergySpace s) (k : Fin 2) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈physicalEndRegion k.succ →
      weakValue (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support p) x=0 ∧
      ∀ i,weakGradient (parentCompletionJoin s hs ha (centralJoinPartition_smooth 1)
        centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
        centralJoinPartition_parent_support p) x i=0 := by
  have hh := parentCompletionJoin_zero_off_support s hs ha (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
    centralJoinPartition_parent_support p
  filter_upwards [hh] with x hx hy
  apply hx
  intro hm
  have ht := centralJoinPartition_subordinate 1 hm
  change sourceCollarTime (WithLp.ofLp x)∈Ioo 0 (2*centralThickness) at ht
  exact (not_le.mpr ht.2) (physicalChildEnd_parent_time k hy)

lemma physical_child_join_zero_on_other_ends (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    {a : ℝ} (ha : 0<a) (p : centralEnergySpace s) (k : Fin 2)
    (i : Fin 3) (hik : i≠k.succ) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈physicalEndRegion i →
      weakValue (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) p) x=0 ∧
      ∀ j,weakGradient (physicalChildCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
        (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
        (centralJoinChildCutoff_support k) p) x j=0 := by
  let u := childCompletionJoin s hs ha k (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
    (centralJoinChildCutoff_support k) p
  have hu : u∈H10 := childCompletionJoin_mem_H10 s hs ha k _ _ _ _ p
  have he := childCompletionJoin_zero_off_support s hs ha k (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
    (centralJoinChildCutoff_support k) p
  have hz : ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈{y | sourceCollarTime y< -2*centralThickness} →
      weakValue u x=0 ∧ ∀ j,weakGradient u x j=0 := by
    filter_upwards [he] with x hx hy
    exact hx (fun hm => (not_le.mpr hy) ((centralJoinChildCutoff_support k hm).1))
  have hh := childH10Transport_zero_on k ⟨u,hu⟩ _ hz
  filter_upwards [hh] with x hx hy
  exact hx (physicalOtherEnd_child_time k i hik hy)

lemma central_interior_join_zero_on_ends (s : Fin 3 → ℝ) (p : centralEnergySpace s)
    (i : Fin 3) :
    ∀ᵐ x∂ballMeasure,WithLp.ofLp x∈physicalEndRegion i →
      weakValue (centralInteriorCompletion s (centralJoinPartition_smooth 0)
        centralJoinPartition_interior_compact centralJoinPartition_interior_support
        (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy)) p) x=0 ∧
      ∀ j,weakGradient (centralInteriorCompletion s (centralJoinPartition_smooth 0)
        centralJoinPartition_interior_compact centralJoinPartition_interior_support
        (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy)) p) x j=0 := by
  have hh := centralInteriorCompletion_zero_off_support s (centralJoinPartition_smooth 0)
    centralJoinPartition_interior_compact centralJoinPartition_interior_support
    (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy)) p
  have he := ae_restrict_of_ae (s:=ball)
    ((PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
      physicalBlockRegion_central_end_exclusive_ae)
  filter_upwards [hh,he] with x hx he hy
  exact hx (fun hm => he (centralJoinPartition_interior_support hm) i hy)

end ScalarConductivity
end

end OAI
end

section
-- module Solutions.OAIQ059_CD.Conductivity_Variational_CompletePhysicalAttachment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

theorem complete_physical_attachment_oai (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (a κ : Fin 3 → ℝ) (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ)
    (p : centralEnergySpace s) :
    ∃ w : H1,w∈H10 ∧
      H1JetOn w centralPhysical (centralFullJetCLM s p.val) ∧
      ∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i) := by
  let zi := centralInteriorCompletion s (centralJoinPartition_smooth 0)
    centralJoinPartition_interior_compact centralJoinPartition_interior_support
    (fun _ hy => centralPhysical_subset_ball (centralJoinPartition_interior_support hy)) p
  let zp := parentCompletionJoin s hs ha₀ (centralJoinPartition_smooth 1)
    centralJoinPartition_parent_compact (centralJoinPartition_bound 1)
    centralJoinPartition_parent_support p
  let zc (k : Fin 2) := physicalChildCompletionJoin s hs (ha k) k (centralJoinChildCutoff_smooth k)
    (centralJoinChildCutoff_compact k) (centralJoinChildCutoff_bound k)
    (centralJoinChildCutoff_support k) p
  obtain ⟨dp,hdp,hds,hdpZ,hdpE⟩ := parentAttachedCorrection_supported s hs ha₀ (κ 0) p
  have hdcEx (k : Fin 2) := physicalChildAttachedCorrection_supported s hs (ha k) k (κ k.succ) p
  choose dc hdc hdcZ hdcE using hdcEx
  let w : H1 := zi+(zp+dp)+((zc 0+dc 0)+(zc 1+dc 1))
  have hw : w∈H10 := H10.add_mem
    (H10.add_mem (centralInteriorCompletion_mem_H10 s _ _ _ _ p)
      (H10.add_mem (parentCompletionJoin_mem_H10 s hs ha₀ _ _ _ _ p) hdp))
    (H10.add_mem
      (H10.add_mem (physicalChildCompletionJoin_mem_H10 s hs (ha 0) 0 _ _ _ _ p) (hdc 0))
      (H10.add_mem (physicalChildCompletionJoin_mem_H10 s hs (ha 1) 1 _ _ _ _ p) (hdc 1)))
  have hpC : H1JetOn dp centralPhysical (fun _ => 0) :=
    (H1JetOn.zero_of_weak (D:={y | centralThickness≤ sourceCollarTime y}) hdpZ).mono
      (fun y hy => ((centralPhysical_time_iff y).mp hy).1)
  have hcC (k : Fin 2) : H1JetOn (dc k) centralPhysical (fun _ => 0) :=
    (H1JetOn.zero_of_weak (D:={y | sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)≤-centralThickness}) (hdcZ k)).mono
      (fun y hy => ((centralPhysical_time_iff y).mp hy).2 k)
  have hpO (k : Fin 2) : H1JetOn (zp+dp) (physicalEndRegion k.succ) (fun _ => 0) := by
    apply H1JetOn.add_zero
    · exact H1JetOn.zero_of_weak (parent_join_zero_on_children s hs ha₀ p k)
    · apply (H1JetOn.zero_of_weak (D:={y | centralThickness≤ sourceCollarTime y}) hdpZ).mono
      intro y hy
      exact (show centralThickness≤2*centralThickness by norm_num [centralThickness]).trans
        (physicalChildEnd_parent_time k hy)
  have hcO (k : Fin 2) (i : Fin 3) (hik : i≠k.succ) :
      H1JetOn (zc k+dc k) (physicalEndRegion i) (fun _ => 0) := by
    apply H1JetOn.add_zero
    · exact H1JetOn.zero_of_weak (physical_child_join_zero_on_other_ends s hs (ha k) p k i hik)
    · apply (H1JetOn.zero_of_weak (D:={y | sourceCollarTime
      ((sourceChildHomeomorph (actualChildSign k)).symm y)≤-centralThickness}) (hdcZ k)).mono
      intro y hy
      exact (physicalOtherEnd_child_time k i hik hy).le.trans
        (by norm_num [centralThickness])
  have hiO (i : Fin 3) : H1JetOn zi (physicalEndRegion i) (fun _ => 0) :=
    H1JetOn.zero_of_weak (central_interior_join_zero_on_ends s p i)
  have hpE : H1JetOn (zp+dp) (physicalEndRegion 0) (attachedPhysicalJet s a κ p 0) :=
    H1JetOn.of_weak hdpE
  have hcE (k : Fin 2) : H1JetOn (zc k+dc k) (physicalEndRegion k.succ)
      (attachedPhysicalJet s a κ p k.succ) := H1JetOn.of_weak (hdcE k)
  refine ⟨w,hw,?_,?_⟩
  · have he : w=centralNeighborhoodCompletion s hs ha₀ ha p+(dp+(dc 0+dc 1)) := by
      simp only [w,centralNeighborhoodCompletion,Fin.sum_univ_two,add_apply]
      change zi+(zp+dp)+((zc 0+dc 0)+(zc 1+dc 1))=zi+zp+(zc 0+zc 1)+(dp+(dc 0+dc 1))
      abel
    rw [he]
    have hc : H1JetOn (centralNeighborhoodCompletion s hs ha₀ ha p) centralPhysical
        (centralFullJetCLM s p.val) := centralNeighborhoodCompletion_central_ae s hs ha₀ ha p
    exact hc.add_zero (hpC.add_zero ((hcC 0).add_zero (hcC 1)))
  · intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact ((hiO 0).zero_add hpE).add_zero
        ((hcO 0 0 (by decide)).add_zero (hcO 1 0 (by decide)))
    · fin_cases k
      · exact ((hiO 1).add_zero (hpO 0)).zero_add
          ((hcE 0).add_zero (hcO 1 1 (by decide)))
      · exact ((hiO 2).add_zero (hpO 1)).zero_add
          ((hcO 0 2 (by decide)).zero_add (hcE 1))

end ScalarConductivity
end

end

end OAI
end

theorem solution : type_of% @OAI.ScalarConductivity.complete_physical_attachment_oai := @OAI.ScalarConductivity.complete_physical_attachment_oai
