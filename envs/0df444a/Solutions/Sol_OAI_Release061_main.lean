-- Prove2me | solution 1 for OAI.Release061.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:04:26.505243+00:00
-- url     : https://prove2.me/submissions/df8f1fe3-f523-4a13-80b4-c8e713138ea7

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S003
import Theorems.Thm_OAI_Release061_Biholomorph_hermitian_model_bounded_symmetric
import Theorems.Thm_OAI_Release061_original_supported_hermitian_model

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ContinuityPrinciple
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra
open Set

theorem point_isBoundedSymmetricDomain :
    IsBoundedSymmetricDomain (univ : Set (Affine 0)) := by
  refine ⟨isOpen_univ,isConnected_univ,?_,?_⟩
  · exact (Set.toFinite _).isBounded
  · intro p
    refine ⟨biholomorphOfSubsingleton _ _,?_,Subsingleton.elim _ _,univ,isOpen_univ,mem_univ _,?_⟩
    · exact fun _ => Subsingleton.elim _ _
    · exact fun _ _ _ => Subsingleton.elim _ _

theorem main_point {n : ℕ} (U : Set (Affine n)) (hne : U.Nonempty)
    (hsub : U.Subsingleton) :
    IsSmooth U ∧ ∃ (m : ℕ) (D : Set (Affine m)),
      IsBoundedSymmetricDomain D ∧ Nonempty (Biholomorph U D) := by
  let : Subsingleton U := (Set.subsingleton_coe U).mpr hsub
  let : Nonempty U := hne.to_subtype
  let B := biholomorphOfSubsingleton U (univ : Set (Affine 0))
  refine ⟨?_,0,univ,point_isBoundedSymmetricDomain,⟨B⟩⟩
  intro p
  exact ⟨0,U,Subset.rfl,by simp,p.property,univ,isOpen_univ,⟨B⟩⟩

open Filter
open scoped Topology

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ConjugateMulActionCompact
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set

theorem conjugateMulAction_proper {G X Y : Type*} [Group G]
    [TopologicalSpace G] [TopologicalSpace X] [TopologicalSpace Y]
    [MulAction G X] [ProperSMul G X] (e : X ≃ₜ Y) :
    let _ : MulAction G Y := conjugateMulAction e.toEquiv
    ProperSMul G Y := by
  let _ : MulAction G Y := conjugateMulAction e.toEquiv
  constructor
  change IsProperMap (fun gx : G × Y => (e (gx.1 • e.symm gx.2),gx.2))
  have H := ((e.prodCongr e).isProperMap.comp
    (ProperSMul.isProperMap_smul_pair (G := G) (X := X))).comp
    ((Homeomorph.refl G).prodCongr e.symm).isProperMap
  change IsProperMap (fun gx : G × Y => (e (gx.1 • e.symm gx.2),e (e.symm gx.2))) at H
  simpa only [e.apply_symm_apply] using H

theorem conjugateMulAction_compact_quotient {G X Y : Type*} [Group G]
    [TopologicalSpace X] [TopologicalSpace Y] [MulAction G X]
    [CompactSpace (Quotient (MulAction.orbitRel G X))] (e : X ≃ₜ Y) :
    let _ : MulAction G Y := conjugateMulAction e.toEquiv
    CompactSpace (Quotient (MulAction.orbitRel G Y)) := by
  let _ : MulAction G Y := conjugateMulAction e.toEquiv
  have hr : ∀ x x' : X, MulAction.orbitRel G X x x' →
      MulAction.orbitRel G Y (e x) (e x') := by
    intro x x' h
    obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨g,?_⟩
    change e (g • e.symm (e x')) = e x
    simpa only [e.symm_apply_apply] using congrArg e hg
  let f : Quotient (MulAction.orbitRel G X) → Quotient (MulAction.orbitRel G Y) :=
    Quotient.map' e hr
  have hf : Continuous f := e.continuous.quotient_map' hr
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨y,rfl⟩ := Quotient.mk_surjective y
    refine ⟨Quotient.mk _ (e.symm y),?_⟩
    simp [f]
  exact ⟨by simpa only [Set.image_univ,hs.range_eq] using isCompact_univ.image hf⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BoundaryFiberClosureContinuity
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

theorem Biholomorph.conjugate_action_holomorphic {n m : ℕ}
    {S : Set (Affine n)} {T : Set (Affine m)} (e : Biholomorph S T)
    {Γ : Type*} [Group Γ] [MulAction Γ S]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset S (fun p => (γ • p : S).val)) (γ : Γ) :
    let _ : MulAction Γ T := conjugateMulAction e.toHomeomorph.toEquiv
    HolomorphicOnSubset T (fun p => (γ • p : T).val) := by
  let _ : MulAction Γ T := conjugateMulAction e.toHomeomorph.toEquiv
  change HolomorphicOnSubset T
    (fun p => (e.toHomeomorph (γ • e.toHomeomorph.symm p)).val)
  have h₁ := (hhol γ).comp (f := e.toHomeomorph.symm) e.holomorphic_invFun
  have h₂ := e.holomorphic_toFun.comp
    (f := fun p : T => γ • e.toHomeomorph.symm p) h₁
  exact h₂

open Set Filter Topology Metric Classical

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CayleyTangentBound
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Complex Set Filter Metric
open scoped Topology

lemma add_I_ne_zero_of_im_pos {u : ℂ} (hu : 0 < u.im) : u+I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [add_im,I_im,zero_im] at this
  linarith

lemma norm_normalCayley_lt_one {u : ℂ} (hu : 0 < u.im) :
    ‖normalCayley u‖ < 1 := by
  rw [normalCayley,norm_div,div_lt_one (norm_pos_iff.mpr (add_I_ne_zero_of_im_pos hu))]
  apply (sq_lt_sq₀ (norm_nonneg (u-I)) (norm_nonneg (u+I))).mp
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.I_re,Complex.I_im,sub_zero,add_zero]
  nlinarith

lemma one_add_im_le_norm_add_I {u : ℂ} (hu : 0 ≤ u.im) :
    1+u.im ≤ ‖u+I‖ := by
  have hh := Complex.abs_im_le_norm (u+I)
  simpa only [add_im,I_im,abs_of_nonneg (by linarith : 0 ≤ u.im+1),add_comm] using hh

lemma cayley_tangent_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c : ℝ} (hc : 0 < c) {z : E} {u : ℂ} (hu : c*‖z‖^2 ≤ u.im) :
    ‖(u+I)⁻¹ • z‖ ≤ (2*Real.sqrt c)⁻¹ := by
  have hy : 0 ≤ u.im := (mul_nonneg hc.le (sq_nonneg _)).trans hu
  have hd : 0 < 1+u.im := by linarith
  have hd' : 0 < ‖u+I‖ := hd.trans_le (one_add_im_le_norm_add_I hy)
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsq := Real.sq_sqrt hc.le
  have hest : 2*Real.sqrt c*‖z‖ ≤ 1+u.im := by
    have hh := sq_nonneg (Real.sqrt c*‖z‖-1)
    nlinarith
  rw [norm_smul,norm_inv]
  rw [← one_div (2*Real.sqrt c)]
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt c)).mpr
  calc
    ‖u+I‖⁻¹*‖z‖*(2*Real.sqrt c) = (2*Real.sqrt c*‖z‖)/‖u+I‖ := by ring
    _ ≤ 1 := (div_le_one hd').mpr (hest.trans (one_add_im_le_norm_add_I hy))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SupportCayleyOpenImage
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Complex Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

theorem supportCayley_bounded {D : Set (E × (Fin (k+1) → ℂ))}
    {c : ℝ} (hc : 0 < c) (hD : ∀ x ∈ D, ∀ i, c*‖x.1‖^2 < (x.2 i).im) :
    Bornology.IsBounded (supportCayley '' D) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max (2*Real.sqrt c)⁻¹ 1,?_⟩
  rintro y ⟨x,hx,rfl⟩
  rw [supportCayley,Prod.norm_def]
  apply max_le
  · exact (cayley_tangent_bound hc (hD x hx 0).le).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    apply (norm_normalCayley_lt_one ?_).le
    exact (mul_nonneg hc.le (sq_nonneg _)).trans_lt (hD x hx i)

theorem supportCayley_open_image {D : Set (E × (Fin (k+1) → ℂ))}
    (hD : IsOpen D) (hupper : ∀ x ∈ D, ∀ i, 0 < (x.2 i).im) :
    IsOpen (supportCayley '' D) := by
  have hsub : D ⊆ (supportCayleyChart (E := E) (k := k)).source := by
    intro x hx i
    exact add_I_ne_zero_of_im_pos (hupper x hx i)
  exact supportCayleyChart.isOpen_image_of_subset_source hD hsub

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelChartOpen
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

lemma modelBoundedChart_analytic
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {x : E × (Fin (k+1) → ℂ)}
    (hx : ∀ i, (supportLinearCoordinates e x).2 i+I ≠ 0) :
    AnalyticAt ℂ (modelBoundedChart e) x :=
  (analyticAt_supportCayley hx).comp ((supportLinearCoordinates e).toContinuousLinearMap.analyticAt x)

lemma modelBoundedChart_inverse_analytic
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {x : E × (Fin (k+1) → ℂ)} (hx : ∀ i, 1-x.2 i ≠ 0) :
    AnalyticAt ℂ (modelBoundedChart e).symm x := by
  change AnalyticAt ℂ (fun y => (supportLinearCoordinates (E := E) e).symm (supportUncayley y)) x
  exact ((supportLinearCoordinates (E := E) e).symm.toContinuousLinearMap.analyticAt _).comp
    (analyticAt_supportUncayley hx)

theorem modelBoundedChart_bounded_open
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {D : Set (E × (Fin (k+1) → ℂ))} (hD : IsOpen D)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ D, ∀ i, c*‖x.1‖^2 < e (fun t => (x.2 t).im) i) :
    D ⊆ (modelBoundedChart e).source ∧
    IsOpen (modelBoundedChart e '' D) ∧
    Bornology.IsBounded (modelBoundedChart e '' D) := by
  have hcoord : IsOpen (supportLinearCoordinates e '' D) :=
    (supportLinearCoordinates e).toHomeomorph.isOpenMap D hD
  have hupper : ∀ x ∈ supportLinearCoordinates e '' D, ∀ i,
      c*‖x.1‖^2 < (x.2 i).im := by
    rintro _ ⟨x,hx,rfl⟩ i
    simpa only [supportLinearCoordinates_fst,supportLinearCoordinates_im] using hbound x hx i
  have himage : modelBoundedChart e '' D =
      supportCayley '' (supportLinearCoordinates e '' D) := by
    rw [Set.image_image]
    rfl
  constructor
  · intro x hx
    change x ∈ Set.univ ∩ (supportLinearCoordinates e) ⁻¹' {y | ∀ i, y.2 i+I ≠ 0}
    refine ⟨Set.mem_univ _,fun i => ?_⟩
    apply add_I_ne_zero_of_im_pos
    simpa only [supportLinearCoordinates_im] using
      (mul_nonneg hc.le (sq_nonneg ‖x.1‖)).trans_lt (hbound x hx i)
  · rw [himage]
    refine ⟨supportCayley_open_image hcoord ?_,supportCayley_bounded hc hupper⟩
    intro x hx i
    exact (mul_nonneg hc.le (sq_nonneg ‖x.1‖)).trans_lt (hupper x hx i)

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Model
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma linearConjugateChart_analytic (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (ha : AnalyticOnNhd ℂ f f.source) :
    AnalyticOnNhd ℂ (linearConjugateChart e f) (linearConjugateChart e f).source := by
  intro x hx
  rw [linearConjugateChart_source] at hx
  exact (e.analyticAt _).comp ((ha _ hx).comp (e.symm.analyticAt x))

lemma linearConjugateChart_inverse_analytic (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (ha : AnalyticOnNhd ℂ f.symm f.target) :
    AnalyticOnNhd ℂ (linearConjugateChart e f).symm (linearConjugateChart e f).target := by
  intro x hx
  rw [linearConjugateChart_target] at hx
  exact (e.analyticAt _).comp ((ha _ hx).comp (e.symm.analyticAt x))

lemma linearConjugateChart_image (e : E ≃L[ℂ] F)
    (f : OpenPartialHomeomorph E E) (D : Set E) :
    linearConjugateChart e f '' (e '' D) = e '' (f '' D) := by
  simp only [Set.image_image]
  congr 1
  funext x
  simp

theorem model_bounded_biholomorph {m k : ℕ}
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {D : Set (Affine m × Affine (k+1))} (hD : IsOpen D) (hconn : IsConnected D)
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ D, ∀ i, c*‖x.1‖^2 < e (fun t => (x.2 t).im) i) :
    ∃ B : Set (Affine (m+(k+1))), IsOpen B ∧ IsConnected B ∧ Bornology.IsBounded B ∧
      Nonempty (Biholomorph (affineProductCoordinates m (k+1) '' D) B) := by
  let a := affineProductCoordinates m (k+1)
  let f := modelBoundedChart (E := Affine m) e
  have hp := modelBoundedChart_bounded_open e hD hc hbound
  have hsub : D ⊆ f.source := hp.1
  have hf : AnalyticOnNhd ℂ f f.source := by
    intro x hx
    apply modelBoundedChart_analytic e
    exact hx.2
  have hfi : AnalyticOnNhd ℂ f.symm f.target := by
    intro x hx
    apply modelBoundedChart_inverse_analytic e
    exact hx.1
  have hsub' : a '' D ⊆ (linearConjugateChart a f).source := by
    rintro _ ⟨x,hx,rfl⟩
    simpa only [linearConjugateChart_source,mem_preimage,a.symm_apply_apply] using hsub hx
  let b : Biholomorph (a '' D) (linearConjugateChart a f '' (a '' D)) :=
    Biholomorph.ofOpenPartialHomeomorph (linearConjugateChart a f)
      (linearConjugateChart_analytic a f hf) (linearConjugateChart_inverse_analytic a f hfi)
      (a '' D) hsub'
  refine ⟨linearConjugateChart a f '' (a '' D),?_,?_,?_,⟨b⟩⟩
  · rw [linearConjugateChart_image]
    exact a.isOpenMap _ hp.2.1
  · rw [linearConjugateChart_image]
    exact (hconn.image f (f.continuousOn.mono hsub)).image a a.continuous.continuousOn
  · rw [linearConjugateChart_image]
    exact a.toContinuousLinearMap.lipschitz.isBounded_image hp.2.2

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HermPartUnit
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Complex
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E]

lemma hermPart_smul_both (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (x y : E) :
    hermPart B (c • x) (c • y) = (Complex.normSq c : ℂ)*hermPart B x y := by
  rw [hermPart_smul_left,hermPart_smul_right,← mul_assoc,Complex.mul_conj]

omit [IsScalarTower ℝ ℂ E] in
lemma hermPart_zero (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : hermPart B 0 0 = 0 := by
  simp [hermPart]

omit [IsScalarTower ℝ ℂ E] [Module ℂ E] in
lemma symmetrize_diag (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (x : E) :
    symmetrize B x x = B x x := by
  simp [symmetrize]
  ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ F] in
lemma hermPart_unit (B : F →ₗ[ℝ] F →ₗ[ℝ] ℝ) (c : ℂ) (hc : ‖c‖ = 1) (x y : F) :
    hermPart B (c • x) (c • y) = hermPart B x y := by
  rw [hermPart_smul_both,Complex.normSq_eq_norm_sq,hc]
  norm_num

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_HolQuadraticSmul
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
  {k : ℕ}

omit [FiniteDimensional ℂ E] in
lemma hermQuadratic_unit (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (c : ℂ) (hc : ‖c‖ = 1)
    (z : E) : hermQuadratic B (c • z) = hermQuadratic B z := by
  funext i
  exact congrArg re (hermPart_unit (symmetrize (B i)) c hc z z)

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_QuadraticDomainConnectedComponent
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}

omit [NormedSpace ℂ E] in
lemma quadraticDomain_eq_preimage (H : E → Fin k → ℝ) (hH : Continuous H)
    (C : Set (Fin k → ℝ)) :
    quadraticDomain H C = (quadraticDomainCoordinates H hH) ⁻¹' (univ ×ˢ (univ ×ˢ C)) := by
  ext p
  simp only [quadraticDomain,mem_ofPred_eq,mem_preimage,mem_prod,mem_univ,true_and]
  rfl

omit [NormedSpace ℂ E] in
theorem quadraticDomain_isOpen (H : E → Fin k → ℝ) (hH : Continuous H)
    (C : Set (Fin k → ℝ)) (hC : IsOpen C) : IsOpen (quadraticDomain H C) := by
  rw [quadraticDomain_eq_preimage H hH]
  exact (isOpen_univ.prod (isOpen_univ.prod hC)).preimage
    (quadraticDomainCoordinates H hH).continuous

theorem quadraticDomain_isConnected (H : E → Fin k → ℝ) (hH : Continuous H)
    (C : Set (Fin k → ℝ)) (hC : IsConnected C) : IsConnected (quadraticDomain H C) := by
  rw [quadraticDomain_eq_preimage H hH]
  exact (quadraticDomainCoordinates H hH).isConnected_preimage.mpr
    (isConnected_univ.prod (isConnected_univ.prod hC))

omit [NormedSpace ℂ E] in
lemma quadraticDomain_axis (H : E → Fin k → ℝ) (hH0 : H 0 = 0)
    {C : Set (Fin k → ℝ)} {a : Fin k → ℝ} (ha : a ∈ C) :
    ((0 : E),fun i => I*(a i : ℂ)) ∈ quadraticDomain H C := by
  simpa [quadraticDomain,hH0] using ha

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
lemma quadraticDomain_translation (H : E → Fin k → ℝ) (C : Set (Fin k → ℝ))
    (p : E × (Fin k → ℂ)) (a : Fin k → ℝ) :
    (p.1,fun i => p.2 i+(a i : ℂ)) ∈ quadraticDomain H C ↔ p ∈ quadraticDomain H C := by
  simp [quadraticDomain]

lemma quadraticDomain_unit_rotation (H : E → Fin k → ℝ) (C : Set (Fin k → ℝ))
    (c : ℂ) (hHc : ∀ z, H (c • z) = H z) (p : E × (Fin k → ℂ)) :
    (c • p.1,p.2) ∈ quadraticDomain H C ↔ p ∈ quadraticDomain H C := by
  simp [quadraticDomain,hHc]

lemma quadraticDomain_positive_dilation [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (H : E → Fin k → ℝ) (C : Set (Fin k → ℝ)) (r : ℝ)
    (hH : ∀ z, H (Real.sqrt r • z) = r • H z)
    (hC : ∀ v, r • v ∈ C ↔ v ∈ C) (p : E × (Fin k → ℂ)) :
    (Real.sqrt r • p.1,r • p.2) ∈ quadraticDomain H C ↔ p ∈ quadraticDomain H C := by
  have he : (fun i => ((r • p.2) i).im-H (Real.sqrt r • p.1) i) =
      r • (fun i => (p.2 i).im-H p.1 i) := by
    funext i
    simp only [hH,Pi.smul_apply,Complex.real_smul,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,smul_eq_mul]
    ring
  change (fun i => ((r • p.2) i).im-H (Real.sqrt r • p.1) i) ∈ C ↔ _
  rw [he,hC]
  rfl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_QuadraticModelDomain
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] {k : ℕ}

lemma hermQuadratic_continuous (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    Continuous (hermQuadratic B) := by
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  apply continuous_pi
  intro i
  let b : E →L[ℝ] E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp (B i))
  have hq : Continuous (fun z : E => B i z z) :=
    b.continuous.clm_apply continuous_id
  have hqI : Continuous (fun z : E => B i (I • z) (I • z)) :=
    hq.comp (continuous_const.smul continuous_id)
  have he : (fun z => hermQuadratic B z i) =
      (fun z => (B i z z+B i (I • z) (I • z))/2) := by
    funext z
    simp [hermQuadratic,hermPart,symmetrize_diag]
  rw [he]
  exact (hq.add hqI).div_const 2

omit [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E] in
lemma hermQuadratic_zero (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    hermQuadratic B 0 = 0 := by
  funext i
  simp [hermQuadratic,hermPart_zero]

omit [FiniteDimensional ℂ E] in

theorem actual_quadratic_model_invariances
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (hcone : ∀ r : ℝ, 0 < r → ∀ v, r • v ∈ C ↔ v ∈ C) :
    (∀ (p : E × (Fin k → ℂ)) (a : Fin k → ℝ), (p.1,fun i => p.2 i+(a i : ℂ)) ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C) ∧
    (∀ c : ℂ, ‖c‖ = 1 → ∀ p,
      (c • p.1,p.2) ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C) ∧
    (∀ r : ℝ, 0 < r → ∀ p,
      (Real.sqrt r • p.1,r • p.2) ∈ quadraticDomain (hermQuadratic B) C ↔
      p ∈ quadraticDomain (hermQuadratic B) C) := by
  refine ⟨fun p a => quadraticDomain_translation _ _ p a,?_,?_⟩
  · intro c hc p
    exact quadraticDomain_unit_rotation _ _ c (hermQuadratic_unit B c hc) p
  · intro r hr p
    apply quadraticDomain_positive_dilation _ _ r _ (hcone r hr) p
    intro z
    rw [hermQuadratic_real_smul,Real.sq_sqrt hr.le]

theorem actual_quadratic_model_domain
    (B : Fin k → E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (C : Set (Fin k → ℝ))
    (hC : IsOpen C) (hc : IsConnected C) :
    IsOpen (quadraticDomain (hermQuadratic B) C) ∧
    IsConnected (quadraticDomain (hermQuadratic B) C) ∧
    ∃ a : Fin k → ℝ, ((0 : E),fun i => I*(a i : ℂ)) ∈ quadraticDomain (hermQuadratic B) C := by
  refine ⟨quadraticDomain_isOpen _ (hermQuadratic_continuous B) C hC,
    quadraticDomain_isConnected _ (hermQuadratic_continuous B) C hc,?_⟩
  obtain ⟨a,ha⟩ := hc.nonempty
  exact ⟨a,quadraticDomain_axis _ (hermQuadratic_zero B) ha⟩

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_StrictModelSupports
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions _root_.OAI.Release061.Wiener.instNormedCommRingPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Set Filter Metric Complex
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma positive_on_open_of_nonnegative (ℓ : V →L[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {C : Set V} (hC : IsOpen C) (hnonneg : ∀ y ∈ C, 0 ≤ ℓ y) :
    ∀ y ∈ C, 0 < ℓ y := by
  intro y hy
  have h0 := hnonneg y hy
  by_contra h
  have hzero : ℓ y = 0 := by linarith
  have hex : ∃ v : V, ℓ v ≠ 0 := by
    by_contra hv
    push Not at hv
    apply hℓ
    ext v
    exact hv v
  obtain ⟨v,hv⟩ := hex
  let w : V := -(ℓ v)⁻¹ • v
  have hw : ℓ w = -1 := by simp [w,hv]
  have ht : Tendsto (fun t : ℝ => y+t • w) (𝓝 (0:ℝ)) (𝓝 y) := by
    have hc : Continuous (fun t : ℝ => y+t • w) := by fun_prop
    simpa using hc.tendsto 0
  have hevent : ∀ᶠ t : ℝ in 𝓝[>] 0, y+t • w ∈ C :=
    (ht.eventually (hC.mem_nhds hy)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,htp,htC⟩ := ((show ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t from self_mem_nhdsWithin).and hevent).exists
  have hbad := hnonneg (y+t • w) htC
  simp only [map_add,map_smul,hzero,hw,smul_eq_mul,mul_neg,mul_one,zero_add] at hbad
  exact (not_le_of_gt htp) (neg_nonneg.mp hbad)

theorem strict_model_supports [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {k : ℕ} (H : E → Fin k → ℝ) (hH0 : H 0 = 0)
    {C : Set (Fin k → ℝ)} (hC : IsOpen C) (hne : C.Nonempty)
    (hcone : ∀ r : ℝ, 0 < r → ∀ y ∈ C, r • y ∈ C)
    (ℓ : (Fin k → ℝ) →L[ℝ] ℝ) (hℓ : ℓ ≠ 0) (c : ℝ)
    (hbound : ∀ (z : E) (v : Fin k → ℝ), v-H z ∈ C → c*‖z‖^2 ≤ ℓ v) :
    (∀ y ∈ C, 0 < ℓ y) ∧ ∀ z, c*‖z‖^2 ≤ ℓ (H z) := by
  constructor
  · apply positive_on_open_of_nonnegative ℓ hℓ hC
    intro y hy
    simpa only [hH0,sub_zero,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] using
      hbound 0 y (by simpa only [hH0,sub_zero] using hy)
  · intro z
    obtain ⟨y,hy⟩ := hne
    have hb : ∀ᶠ r : ℝ in 𝓝[>] 0, c*‖z‖^2 ≤ ℓ (H z+r • y) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      apply hbound
      simpa only [add_sub_cancel_left] using hcone r hr y hy
    have ht : Tendsto (fun r : ℝ => ℓ (H z+r • y)) (𝓝[>] 0) (𝓝 (ℓ (H z))) := by
      have hc : Continuous (fun r : ℝ => ℓ (H z+r • y)) := by fun_prop
      simpa using (hc.tendsto 0).mono_left
        (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    exact ge_of_tendsto ht hb

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ModelUnaveraged
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition _root_.OAI.Release061.ambientAction_subtype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.Hermitian
open Complex Set

lemma support_coordinate_nonzero {k : ℕ}
    (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (i : Fin k) :
    (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap ≠ 0 := by
  classical
  intro h
  have hh := congrArg (fun L : (Fin k → ℝ) →L[ℝ] ℝ => L (e.symm (Pi.single i 1))) h
  simp at hh

theorem actual_model_bounded_realization {m k : ℕ}
    (B : Fin (k+1) → Affine m →ₗ[ℝ] Affine m →ₗ[ℝ] ℝ)
    (C : Set (Fin (k+1) → ℝ)) (hC : IsOpen C) (hconn : IsConnected C)
    (hcone : ∀ r : ℝ, 0 < r → ∀ y ∈ C, r • y ∈ C)
    (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ))
    {c : ℝ} (hc : 0 < c)
    (hbound : ∀ x ∈ quadraticDomain (hermQuadratic B) C,
      ∀ i, c*‖x.1‖^2 ≤ e (fun t => (x.2 t).im) i) :
    ∃ D : Set (Affine (m+(k+1))), IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
      Nonempty (Biholomorph
        (affineProductCoordinates m (k+1) '' quadraticDomain (hermQuadratic B) C) D) := by
  have hH := hermQuadratic_continuous B
  apply model_bounded_biholomorph e
    (quadraticDomain_isOpen _ hH C hC) (quadraticDomain_isConnected _ hH C hconn) hc
  intro x hx i
  let ℓ : (Fin (k+1) → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have hn : ℓ ≠ 0 := support_coordinate_nonzero e i
  have hb : ∀ (z : Affine m) (v : Fin (k+1) → ℝ), v-hermQuadratic B z ∈ C →
      c*‖z‖^2 ≤ ℓ v := by
    intro z v hv
    have hp : (z,fun j => I*(v j : ℂ)) ∈ quadraticDomain (hermQuadratic B) C := by
      change (fun i => v i-hermQuadratic B z i) ∈ C at hv
      simpa [quadraticDomain] using hv
    simpa [ℓ] using hbound (z,fun j => I*(v j : ℂ)) hp i
  have hs := strict_model_supports (hermQuadratic B) (hermQuadratic_zero B)
    hC hconn.nonempty hcone ℓ hn c hb
  have hl := hs.2 x.1
  have hp := hs.1 ((fun t => (x.2 t).im)-hermQuadratic B x.1) hx
  change c*‖x.1‖^2 ≤ e (hermQuadratic B x.1) i at hl
  change 0 < e ((fun t => (x.2 t).im)-hermQuadratic B x.1) i at hp
  rw [map_sub,Pi.sub_apply] at hp
  linarith

end Release061.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DivisibleHermitianModel
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Biholomorph.completeGeneratorLieAlgebra _root_.OAI.Release061.Biholomorph.completeGeneratorLieRing
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex
open scoped Classical

theorem Hermitian.model_support_coordinates {m k : ℕ}
    (B : Fin k → Affine m →ₗ[ℝ] Affine m →ₗ[ℝ] ℝ)
    (C : Set (Fin k → ℝ)) (hC : IsOpen C) (hne : C.Nonempty)
    (hcone : ∀ t : ℝ, 0 < t → ∀ y ∈ C, t • y ∈ C)
    (e : (Fin k → ℝ) ≃L[ℝ] (Fin k → ℝ)) (c : ℝ)
    (hbound : ∀ x ∈ quadraticDomain (hermQuadratic B) C,
      ∀ i, c*‖x.1‖^2 ≤ e (fun j => (x.2 j).im) i) :
    (∀ y ∈ C, ∀ i, 0 < e y i) ∧
    ∀ z, ∀ i, c*‖z‖^2 ≤ e (hermQuadratic B z) i := by
  have hh : ∀ i : Fin k, (∀ y ∈ C, 0 < e y i) ∧
      ∀ z, c*‖z‖^2 ≤ e (hermQuadratic B z) i := by
    intro i
    let ℓ : (Fin k → ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
    apply strict_model_supports (hermQuadratic B) (hermQuadratic_zero B) hC hne
      hcone ℓ (support_coordinate_nonzero e i) c
    intro z v hv
    have hp : (z,fun j => I*(v j : ℂ)) ∈ quadraticDomain (hermQuadratic B) C := by
      change (fun i => v i-hermQuadratic B z i) ∈ C at hv
      simpa [quadraticDomain] using hv
    simpa [ℓ] using hbound (z,fun j => I*(v j : ℂ)) hp i
  exact ⟨fun y hy i => (hh i).1 y hy,fun z i => (hh i).2 z⟩

theorem original_divisible_hermitian_model {N : ℕ} (V U : Set (Affine N))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (r k : ℕ) (B : Fin (k+1) → Affine r →ₗ[ℝ] Affine r →ₗ[ℝ] ℝ)
      (C : Set (Fin (k+1) → ℝ))
      (e : (Fin (k+1) → ℝ) ≃L[ℝ] (Fin (k+1) → ℝ)) (c : ℝ),
      let D := quadraticDomain (Hermitian.hermQuadratic B) C
      let M := (affineProductCoordinates r (k+1)) '' D
      IsOpen C ∧ IsConnected C ∧ (0 : Fin (k+1) → ℝ) ∉ C ∧
      (∀ t : ℝ, 0 < t → ∀ y, t • y ∈ C ↔ y ∈ C) ∧ 0 < c ∧
      (∀ y ∈ C, ∀ i, 0 < e y i) ∧
      (∀ z, ∀ i, c*‖z‖^2 ≤ e (Hermitian.hermQuadratic B z) i) ∧
      IsOpen D ∧ IsConnected D ∧
      (∃ a : Fin (k+1) → ℝ, (0,fun i => I*(a i : ℂ)) ∈ D) ∧
      (∀ p : Affine r × Affine (k+1), ∀ a : Fin (k+1) → ℝ,
        (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p ∈ D) ∧
      (∀ t : ℂ, ‖t‖=1 → ∀ p, (t • p.1,p.2) ∈ D ↔ p ∈ D) ∧
      (∀ t : ℝ, 0 < t → ∀ p, (Real.sqrt t • p.1,t • p.2) ∈ D ↔ p ∈ D) ∧
      (∃ A : Set (Affine (r+(k+1))), IsOpen A ∧ IsConnected A ∧
        Bornology.IsBounded A ∧ Nonempty (Biholomorph M A)) ∧
      ∃ g : Biholomorph U M,
        let _ : MulAction Γ M := conjugateMulAction g.toHomeomorph.toEquiv
        ProperSMul Γ M ∧ CompactSpace (Quotient (MulAction.orbitRel Γ M)) ∧
        ∀ γ : Γ, HolomorphicOnSubset M (fun p => (γ • p : M).val) := by
  obtain ⟨r,k,B,C,e,c,hk,hCo,hCc,hCzero,hcone,hcpos,hbound,⟨g⟩⟩ :=
    original_supported_hermitian_model V U hV hUV hU hc hn hb hs Γ hhol
  cases k with
  | zero => omega
  | succ k =>
    have hconep : ∀ t : ℝ, 0 < t → ∀ y ∈ C, t • y ∈ C :=
      fun t ht y hy => (hcone t ht y).mpr hy
    obtain ⟨hpositive,hherm⟩ := Hermitian.model_support_coordinates B C hCo hCc.nonempty hconep e c hbound
    obtain ⟨hDo,hDc,ha⟩ := Hermitian.actual_quadratic_model_domain B C hCo hCc
    obtain ⟨htrans,hunit,hdilation⟩ := Hermitian.actual_quadratic_model_invariances B C hcone
    have hbounded := Hermitian.actual_model_bounded_realization B C hCo hCc hconep e hcpos hbound
    refine ⟨r,k,B,C,e,c,hCo,hCc,hCzero,hcone,hcpos,hpositive,hherm,
      hDo,hDc,ha,htrans,hunit,hdilation,hbounded,g,?_,?_,?_⟩
    · exact conjugateMulAction_proper g.toHomeomorph
    · exact conjugateMulAction_compact_quotient g.toHomeomorph
    · exact g.conjugate_action_holomorphic hhol

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Filter Topology
open Polynomial
open Filter Topology
open scoped TensorProduct
open Set Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open Filter Topology
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
open scoped TensorProduct
open scoped TensorProduct
open Filter Topology
open scoped TensorProduct
namespace Release061
open Set

theorem main_oai {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hopen : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hconn : IsConnected U) (hsa : IsSemialgebraic U)
    (hbounded : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    IsSmooth U ∧ ∃ (m : ℕ) (D : Set (Affine m)),
      IsBoundedSymmetricDomain D ∧ Nonempty (Biholomorph U D) := by
  classical
  by_cases hpoint : U.Subsingleton
  · exact main_point U hconn.nonempty hpoint
  obtain ⟨r,k,B,C,l,c,_hCo,_hCc,_hC0,_hcone,_hcpos,_hpositive,_hherm,
      hDo,_hDc,_ha,htr,hr,hd,⟨A,hAo,hAc,hAb,⟨e⟩⟩,g,_hg⟩ :=
    original_divisible_hermitian_model V U hV hUV hopen hconn hpoint hbounded hsa Γ hhol
  let S := (affineProductCoordinates r (k+1)) '' quadraticDomain (Hermitian.hermQuadratic B) C
  let : LocallyCompactSpace S :=
    ((affineProductCoordinates r (k+1)).isOpenMap _ hDo).locallyCompactSpace
  let : LocallyCompactSpace A := hAo.locallyCompactSpace
  let f : Biholomorph U A := g.trans e
  let : MulAction Γ A := conjugateMulAction f.toHomeomorph.toEquiv
  let : ProperSMul Γ A := conjugateMulAction_proper f.toHomeomorph
  let : CompactSpace (Quotient (MulAction.orbitRel Γ A)) :=
    conjugateMulAction_compact_quotient f.toHomeomorph
  have hholA : ∀ γ : Γ, HolomorphicOnSubset A (fun p => (γ • p : A).val) :=
    f.conjugate_action_holomorphic hhol
  have hsymm := Biholomorph.hermitian_model_bounded_symmetric hAo hAc hAb Γ hholA B C hDo htr hd hr e
  refine ⟨?_,r+(k+1),A,hsymm,⟨f⟩⟩
  intro p
  exact ⟨r+(k+1),U,Subset.rfl,by simp,p.property,A,hAo,⟨f⟩⟩

end Release061

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Release061.main_oai.{u_1} := @OAI.Release061.main_oai.{u_1}
