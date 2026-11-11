-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:51:15.044129+00:00
-- url     : https://prove2.me/submissions/58ea8b9b-3998-4d34-84d9-ef97c3650cf1

import Mathlib
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_PackingSufficiencySupport_Hamiltonian_exists_compact_radial_relative_moser_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCovectorPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem symplecticProjection_leftInverse {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hi : (Ω.bilinearComp i i).IsInvertible) (u : F) :
    symplecticProjection Ω i (i u) = u := by
  exact hi.inverse_apply_self u

theorem symplecticProjection_pairing {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hi : (Ω.bilinearComp i i).IsInvertible) (x : E) (u : F) :
    Ω (i (symplecticProjection Ω i x)) (i u) = Ω x (i u) := by
  exact congrArg (fun A : F →L[ℝ] ℝ => A u)
    (hi.self_apply_inverse ((Ω.bilinearComp (ContinuousLinearMap.id ℝ E) i) x))

theorem symplecticNormalJet_tangent {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hi : (Ω.bilinearComp i i).IsInvertible) (α : E →L[ℝ] ℝ) (u : F) :
    symplecticNormalJet Ω i α (i u) = 0 := by
  simp only [symplecticNormalJet,sub_apply,ContinuousLinearMap.comp_apply,
    symplecticProjection_leftInverse hi,sub_self]

theorem corrected_moser_vector_tangent
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hΩ : Ω.IsInvertible) (hi : (Ω.bilinearComp i i).IsInvertible)
    (hskew : ∀ u v, Ω u v = -Ω v u) (α : E →L[ℝ] ℝ) :
    -Ω.inverse (α + symplecticNormalJet Ω i α) =
      i (-((Ω.bilinearComp i i).inverse (α.comp i))) := by
  let u := (Ω.bilinearComp i i).inverse (α.comp i)
  have hu (v : F) : Ω (i u) (i v) = α (i v) :=
    congrArg (fun A : F →L[ℝ] ℝ => A v) (hi.self_apply_inverse (α.comp i))
  have hp (x : E) : Ω (i u) x = α (i (symplecticProjection Ω i x)) := by
    calc
      Ω (i u) x = -Ω x (i u) := hskew _ _
      _ = -Ω (i (symplecticProjection Ω i x)) (i u) := by
        rw [symplecticProjection_pairing hi]
      _ = Ω (i u) (i (symplecticProjection Ω i x)) := (hskew _ _).symm
      _ = _ := hu _
  apply hΩ.injective
  rw [map_neg,hΩ.self_apply_inverse,map_neg,map_neg]
  apply ContinuousLinearMap.ext
  intro x
  change -(α x + (α (i (symplecticProjection Ω i x)) - α x)) = -Ω (i u) x
  rw [hp]
  ring

theorem smooth_bilinear_flip {P A B C : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    {f : P → A →L[ℝ] B →L[ℝ] C} {p : P} (h : ContDiffAt ℝ ∞ f p) :
    ContDiffAt ℝ ∞ (fun q => (f q).flip) p := by
  have hflip : ContDiff ℝ ∞ (fun L : A →L[ℝ] B →L[ℝ] C => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜 := ℝ) (n := ∞) (E := A →L[ℝ] B →L[ℝ] C)
      (F := B →L[ℝ] A →L[ℝ] C) (ContinuousLinearMap.flipₗᵢ ℝ A B C)
  exact hflip.contDiffAt.comp p h

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace F]

theorem symplecticProjection_contDiffAt {Ω : P → E →L[ℝ] E →L[ℝ] ℝ}
    {i : P → F →L[ℝ] E} {p : P}
    (hΩ : ContDiffAt ℝ ∞ Ω p) (hi : ContDiffAt ℝ ∞ i p)
    (hinv : ((Ω p).bilinearComp (i p) (i p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun q => symplecticProjection (Ω q) (i q)) p := by
  have hB : ContDiffAt ℝ ∞ (fun q => (Ω q).bilinearComp (i q) (i q)) p :=
    smooth_bilinear_flip ((smooth_bilinear_flip (hΩ.clm_comp hi)).clm_comp hi)
  exact (hinv.contDiffAt_map_inverse.comp p hB).clm_comp
    (smooth_bilinear_flip ((smooth_bilinear_flip (hΩ.clm_comp (contDiffAt_const (c := ContinuousLinearMap.id ℝ E)))).clm_comp hi))


end

section
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bilinearComp_isInvertible {A : E →L[ℝ] E →L[ℝ] ℝ} {C : E →L[ℝ] E}
    (hA : A.IsInvertible) (hC : C.IsInvertible) : (A.bilinearComp C C).IsInvertible := by
  obtain ⟨a,rfl⟩ := hA
  obtain ⟨c,rfl⟩ := hC
  refine ⟨(c.trans a).trans (c.symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)),?_⟩
  ext u v
  rfl


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartTwoForm_apply_chart {Ω : ManifoldTwoForm E M} {c z : M}
    (hz : z ∈ (extChartAt 𝓘(ℝ,E) c).source) (v w : TangentSpace 𝓘(ℝ,E) z) :
    chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c z)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z v)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) z w) = Ω z v w := by
  change E at v w
  change chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c z)
    (chartDifferential c z v) (chartDifferential c z w) = Ω z v w
  simp only [chartTwoForm,(extChartAt 𝓘(ℝ,E) c).left_inv hz,
    ContinuousLinearMap.bilinearComp_apply]
  have hA : (chartDifferential (E := E) c z).IsInvertible := by
    convert! (isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hz) using 1
    all_goals try with_reducible_and_instances rfl
  rw [hA.inverse_apply_eq.mpr rfl,hA.inverse_apply_eq.mpr rfl]



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_add _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_add _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.partialChartCoefficient_smul _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem spatialDifferential_contDiffAt {f : ℝ × E → ℝ} {p : ℝ × E}
    (hf : ContDiffAt ℝ ∞ f p) : ContDiffAt ℝ ∞ (spatialDifferential f) p :=
  (hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiffAt_const

theorem spatialDifferential_fderivAt {f : ℝ × E → ℝ} {p : ℝ × E}
    (hf : ContDiffAt ℝ ∞ f p) (v : ℝ × E) (w : E) :
    fderiv ℝ (spatialDifferential f) p v w =
      fderiv ℝ (fderiv ℝ f) p v (0,w) := by
  have hd := ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hh := hd.clm_comp (hasFDerivAt_const (ContinuousLinearMap.inr ℝ ℝ E) p)
  rw [show fderiv ℝ (spatialDifferential f) p = _ from hh.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.inr_apply]

theorem spatialDifferential_closedAt {f : ℝ × E → ℝ} {p : ℝ × E}
    (hf : ContDiffAt ℝ ∞ f p) (v w : E) :
    fderiv ℝ (spatialDifferential f) p (0,v) w -
      fderiv ℝ (spatialDifferential f) p (0,w) v = 0 := by
  rw [spatialDifferential_fderivAt hf,spatialDifferential_fderivAt hf]
  exact sub_eq_zero.mpr ((hf.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)).eq (0,v) (0,w))


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifoldPotentialChart_contDiffAt {f : ℝ × M → ℝ}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f)
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    ContDiffAt ℝ ∞ (manifoldPotentialChart f c) p := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp)
  exact (hf.contMDiffAt.comp p
    (contDiffAt_fst.contMDiffAt.prodMk (hi.comp p contDiffAt_snd.contMDiffAt))).contDiffAt

theorem chartDifferential_inverse {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).inverse =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm y := by
  apply ContinuousLinearMap.inverse_eq
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ,E)) hy)
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hy)

theorem chartOneForm_manifoldSpatialDifferential {f : ℝ × M → ℝ}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f)
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartOneForm (manifoldSpatialDifferential f p.1) c p.2 =
      spatialDifferential (manifoldPotentialChart f c) p := by
  have hs : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (fun z => f (p.1,z)) :=
    hf.comp (contMDiff_const.prodMk contMDiff_id)
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp)
  have hm := ((hs.mdifferentiable (by simp) _).hasMFDerivAt).comp p.2
    (hi.mdifferentiableAt (by simp)).hasMFDerivAt
  have hj := (manifoldPotentialChart_contDiffAt hf hp).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have ha : HasFDerivAt (fun y : E => (p.1,y)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
    convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2) using 1
    all_goals try with_reducible_and_instances rfl
  have hd := hj.hasFDerivAt.comp p.2 ha
  have hdm : HasFDerivAt (fun y => f (p.1,(extChartAt 𝓘(ℝ,E) c).symm y))
      (chartOneForm (manifoldSpatialDifferential f p.1) c p.2) p.2 := by
    rw [chartOneForm,chartDifferential_inverse hp]
    exact hasMFDerivAt_iff_hasFDerivAt.mp hm
  have hdj : HasFDerivAt (fun y => f (p.1,(extChartAt 𝓘(ℝ,E) c).symm y))
      (spatialDifferential (manifoldPotentialChart f c) p) p.2 := by
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
  exact hdm.unique hdj


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclideanPullbackTwoForm_chart {Ω : ℝ → ManifoldTwoForm E M} {g : F → M}
    {p : ℝ × F} {c : M} (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanPullbackTwoForm Ω g p =
      (chartTwoForm (Ω p.1) c (extChartAt 𝓘(ℝ,E) c (g p.2))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2) := by
  have hd := ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp p.2 hg.hasMFDerivAt)
  let A : F →L[ℝ] E :=
    (chartDifferential c (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A p.2 :=
    hasMFDerivAt_iff_hasFDerivAt.mp hd
  have hdf := hf.fderiv
  dsimp only [A,chartDifferential] at hdf
  rw [hdf]
  ext v w
  exact (chartTwoForm_apply_chart hc _ _).symm

theorem euclideanPullbackOneForm_chart {α : ℝ → ManifoldOneForm E M} {g : F → M}
    {p : ℝ × F} {c : M} (hg : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
    (hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    euclideanPullbackOneForm α g p =
      (chartOneForm (α p.1) c (extChartAt 𝓘(ℝ,E) c (g p.2))).comp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2) := by
  have hd := ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c)
    (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp p.2 hg.hasMFDerivAt)
  let A : F →L[ℝ] E :=
    (chartDifferential c (g p.2)).comp (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) c ∘ g) A p.2 :=
    hasMFDerivAt_iff_hasFDerivAt.mp hd
  have hdf := hf.fderiv
  dsimp only [A,chartDifferential] at hdf
  rw [hdf]
  have hC : (chartDifferential (E := E) c (g p.2)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hc using 1
    all_goals try with_reducible_and_instances rfl
  ext v
  change α p.1 (g p.2) _ = α p.1 ((extChartAt 𝓘(ℝ,E) c).symm
    (extChartAt 𝓘(ℝ,E) c (g p.2))) _
  rw [(extChartAt 𝓘(ℝ,E) c).left_inv hc]
  change _ = α p.1 (g p.2) ((chartDifferential c (g p.2)).inverse
    (chartDifferential c (g p.2) (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) g p.2 v)))
  erw [hC.inverse_apply_self]
  rfl

theorem euclideanPullbackTwoForm_contDiffAt
    {Ω : ℝ → ManifoldTwoForm E M} {g : F → M} {p : ℝ × F}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (euclideanPullbackTwoForm Ω g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : ℝ × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := ((hΩ c).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) c).map_source hc⟩)).comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
  have hsm := smooth_bilinear_flip ((smooth_bilinear_flip (hform.clm_comp hder)).clm_comp hder)
  apply hsm.congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackTwoForm_chart (hq.mdifferentiableAt (by simp)) hqc

theorem euclideanPullbackOneForm_contDiffAt
    {α : ℝ → ManifoldOneForm E M} {g : F → M} {p : ℝ × F}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) :
    ContDiffAt ℝ ∞ (euclideanPullbackOneForm α g) p := by
  let c := g p.2
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ (extChartAt 𝓘(ℝ,E) c ∘ g) p.2 := hch.contDiffAt
  have hcoord : ContDiffAt ℝ ∞ (fun q : ℝ × F => (q.1,extChartAt 𝓘(ℝ,E) c (g q.2))) p :=
    contDiffAt_fst.prodMk (hs.comp p contDiffAt_snd)
  have hform := ((hα c).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) c).map_source hc⟩)).comp p hcoord
  have hder := (hs.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
  have hsm := hform.clm_comp hder
  apply hsm.congr_of_eventuallyEq
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
    continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
  exact euclideanPullbackOneForm_chart (hq.mdifferentiableAt (by simp)) hqc


end

open scoped ContDiff Manifold Topology
open MeasureTheory Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_DiskMaps_FlatIsotopy
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Set Function
open MeasureTheory
open scoped ComplexConjugate
section

universe u
variable {P E F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiff_fixed_integral {f : ℝ × P → F} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun p => ∫ t in (0:ℝ)..1, f (t,p)) := by
  let τ : C(Time,ℝ × P) := ⟨fun t => ((t:ℝ),0),continuous_subtype_val.prodMk continuous_const⟩
  let v : P → C(Time,ℝ × P) := fun p => τ + constantPath (0,p)
  have hv : ContDiff ℝ ∞ v := contDiff_const.add
    ((constantPath (E := ℝ × P)).contDiff.comp (contDiff_const.prodMk contDiff_id))
  let I : C(Time,F) →L[ℝ] F := (ContinuousMap.evalCLM ℝ (⟨1,by simp⟩ : Time)).comp pathIntegral
  have he : (fun p => ∫ t in (0:ℝ)..1, f (t,p)) =
      fun p => I ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) := by
    funext p
    change _ = ∫ t in (0:ℝ)..1, extendPath ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) t
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    rw [show extendPath ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) t =
      ((⟨f,hf.continuous⟩ : C(ℝ × P,F)).comp (v p)) ⟨t,ht⟩ from extendPath_coe _ ⟨t,ht⟩]
    change f (t,p) = f ((t,0)+(0,p))
    simp
  rw [he]
  exact I.contDiff.comp ((postcomp_contDiff hf).comp hv)

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldMapDifferential
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped Manifold
open scoped ContDiff Topology
open Set Function Manifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartTwoForm_manifoldPullback {Ω : ℝ → ManifoldTwoForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target) :
    chartTwoForm (manifoldPullbackTwoForm Ω e p.1) b p.2 =
      euclideanPullbackTwoForm Ω (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := ((he.mdifferentiable (by simp) _).hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackTwoForm,hd,chartTwoForm,manifoldPullbackTwoForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v w
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chartOneForm_manifoldPullback {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {b : N} {p : ℝ × F}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,F) b).target) :
    chartOneForm (manifoldPullbackOneForm α e p.1) b p.2 =
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) b).symm) p := by
  have hc := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) b).mem_nhds hp)).mdifferentiableAt (by simp)
  have hd := ((he.mdifferentiable (by simp) _).hasMFDerivAt.comp p.2 hc.hasMFDerivAt).mfderiv
  simp only [euclideanPullbackOneForm,hd,chartOneForm,manifoldPullbackOneForm,
    manifoldMapDifferential,chartDifferential_inverse hp,Function.comp_apply]
  ext v
  rfl

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem vector_chartOneForm (α : E → E →L[ℝ] ℝ) (c y : E) :
    chartOneForm α c y=α y := by
  simp only [chartOneForm,chartDifferential,extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe,PartialEquiv.refl_symm,fderiv_id,
    mfderiv_eq_fderiv,ContinuousLinearMap.inverse_id,ContinuousLinearMap.comp_id,id_eq]

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_QuadricInfinityPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff BigOperators
open Set Function
open scoped Manifold Topology
open Manifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem chart_parameterPullbackOneForm {α : ℝ → ManifoldOneForm E M} {g : ℝ × N → M}
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ g)
    (c : N) (s t : ℝ) {y : F} (hy : y ∈ (extChartAt 𝓘(ℝ,F) c).target) :
    chartOneForm (parameterPullbackOneForm α g s t) c y =
      (euclideanPullbackOneForm α
        (fun q : ℝ × F => g (q.1,(extChartAt 𝓘(ℝ,F) c).symm q.2)) (t,(s,y))).comp
          (ContinuousLinearMap.inr ℝ ℝ F) := by
  have hs : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ (fun x => g (s,x)) :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  rw [parameterPullbackOneForm,chartOneForm_manifoldPullback (α := α) (p := (t,y)) hs hy]
  let h : ℝ × F → M := fun q => g (q.1,(extChartAt 𝓘(ℝ,F) c).symm q.2)
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy)
  have hh : ContMDiffAt 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ h (s,y) :=
    hg.contMDiffAt.comp (s,y) (contDiffAt_fst.contMDiffAt.prodMk
      (hc.comp (s,y) contDiffAt_snd.contMDiffAt))
  have hi : HasMFDerivAt 𝓘(ℝ,F) 𝓘(ℝ,ℝ × F) (fun z => (s,z)) y
      (ContinuousLinearMap.inr ℝ ℝ F) := by
    apply hasMFDerivAt_iff_hasFDerivAt.mpr
    convert! ((hasFDerivAt_const (𝕜 := ℝ) s y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)) using 1
    all_goals try with_reducible_and_instances rfl
  have hd := ((hh.mdifferentiableAt (by simp)).hasMFDerivAt.comp y hi).mfderiv
  simp only [euclideanPullbackOneForm]
  rw [show mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E)
    ((fun x => g (s,x)) ∘ (extChartAt 𝓘(ℝ,F) c).symm) y = _ from hd]
  ext v
  rfl

theorem parameterPullbackOneForm_smooth
    {α : ℝ → ManifoldOneForm E M} {g : ℝ × N → M}
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,F)) 𝓘(ℝ,E) ∞ g)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (c : N) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × F) =>
      chartOneForm (parameterPullbackOneForm α g q.1 q.2.1) c q.2.2)
      (univ ×ˢ (univ ×ˢ (extChartAt 𝓘(ℝ,F) c).target)) := by
  intro p hp
  let h : ℝ × F → M := fun q => g (q.1,(extChartAt 𝓘(ℝ,F) c).symm q.2)
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hp.2.2)
  have hh : ContMDiffAt 𝓘(ℝ,ℝ × F) 𝓘(ℝ,E) ∞ h (p.1,p.2.2) :=
    hg.contMDiffAt.comp (p.1,p.2.2) (contDiffAt_fst.contMDiffAt.prodMk
      (hc.comp (p.1,p.2.2) contDiffAt_snd.contMDiffAt))
  have hs := ((euclideanPullbackOneForm_contDiffAt (p := (p.2.1,(p.1,p.2.2))) hα hh).comp p
    (contDiffAt_snd.fst.prodMk (contDiffAt_fst.prodMk contDiffAt_snd.snd))).clm_comp
      (contDiffAt_const (c := ContinuousLinearMap.inr ℝ ℝ F))
  apply (hs.congr_of_eventuallyEq _).contDiffWithinAt
  have ht := continuousAt_snd.snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hp.2.2)
  filter_upwards [ht] with q hq
  exact chart_parameterPullbackOneForm hg c q.1 q.2.1 hq

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Annuli_AnnularMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_smooth_local_identity {U : Set E} {x : E} (hU : U ∈ 𝓝 x) :
    ∃ r : E → E, ContDiff ℝ ∞ r ∧ (∀ y, r y ∈ U) ∧ r =ᶠ[𝓝 x] id := by
  obtain ⟨a,ha,haU⟩ := Metric.mem_nhds_iff.mp hU
  let χ : ContDiffBump x := ⟨a/2,a,by positivity,by linarith⟩
  let r : E → E := fun y => x + χ y • (y-x)
  refine ⟨r,contDiff_const.add (χ.contDiff.smul (contDiff_id.sub contDiff_const)),?_,?_⟩
  · intro y
    apply haU
    by_cases hy : y ∈ ball x a
    · rw [mem_ball_iff_norm]
      change ‖x + χ y • (y-x) - x‖ < a
      rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg χ.nonneg]
      exact (mul_le_of_le_one_left (norm_nonneg _) χ.le_one).trans_lt (mem_ball_iff_norm.mp hy)
    · have hz : χ y = 0 := χ.zero_of_le_dist (not_lt.mp hy)
      simp only [r,hz,zero_smul,add_zero]
      exact mem_ball_self ha
  · filter_upwards [χ.eventuallyEq_one] with y hy
    change x + χ y • (y-x) = y
    rw [hy,Pi.one_apply,one_smul,add_sub_cancel]


end

section
open scoped ContDiff Topology
open Set Function MeasureTheory
variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem contDiffOn_fixed_integral {U : Set P} (hU : IsOpen U) {f : ℝ × P → F}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun p => ∫ s in (0:ℝ)..1, f (s,p)) U := by
  intro p hp
  obtain ⟨r,hr,hrU,hre⟩ := exists_smooth_local_identity (hU.mem_nhds hp)
  have hg : ContDiff ℝ ∞ (fun q : ℝ × P => f (q.1,r q.2)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    exact (hf.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,hrU q.2⟩)).comp q
      (contDiff_fst.prodMk (hr.comp contDiff_snd)).contDiffAt
  apply ((contDiff_fixed_integral hg).contDiffAt.congr_of_eventuallyEq _).contDiffWithinAt
  filter_upwards [hre] with q hq
  change (∫ s in (0:ℝ)..1, f (s,q)) = ∫ s in (0:ℝ)..1, f (s,r q)
  rw [show r q = q from hq]

omit [CompleteSpace F] in

theorem hasFDerivAt_fixed_integral {f : ℝ × P → F} (hf : ContDiff ℝ ∞ f) (x : P) :
    HasFDerivAt (fun p => ∫ s in (0:ℝ)..1, f (s,p))
      (∫ s in (0:ℝ)..1, fderiv ℝ (fun p => f (s,p)) x) x := by
  let D : ℝ × P → P →L[ℝ] F := fun q => (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ ℝ P)
  have hD : Continuous D := (hf.fderiv_right (m := ∞) (by simp)).continuous.clm_comp continuous_const
  have hd (s : ℝ) (p : P) : HasFDerivAt (fun q => f (s,q)) (D (s,p)) p := by
    convert! ((hf.differentiable (by simp) (s,p)).hasFDerivAt.comp p
      ((hasFDerivAt_const s p).prodMk (hasFDerivAt_id p))) using 1
    all_goals try with_reducible_and_instances rfl
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x (1:ℝ))).exists_bound_of_continuousOn hD.continuousOn
  have hi : HasFDerivAt (fun p => ∫ s in (0:ℝ)..1, f (s,p))
      (∫ s in (0:ℝ)..1, D (s,x)) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
      (s := Metric.closedBall x 1) (bound := fun _ => C) (Metric.closedBall_mem_nhds x zero_lt_one)
    · exact Filter.Eventually.of_forall fun p =>
        (hf.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 1
    · exact (hD.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      intro p hp
      rw [uIoc_of_le zero_le_one] at hs
      exact hC (s,p) ⟨⟨hs.1.le,hs.2⟩,hp⟩
    · exact intervalIntegrable_const
    · exact Filter.Eventually.of_forall fun s p _ => hd s p
  convert! hi using 1
  all_goals try with_reducible_and_instances rfl
  apply intervalIntegral.integral_congr
  intro s _
  exact (hd s x).fderiv

omit [CompleteSpace F] in

theorem hasFDerivAt_fixed_integral_on {U : Set P} (hU : IsOpen U) {f : ℝ × P → F}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ U)) {x : P} (hx : x ∈ U) :
    HasFDerivAt (fun p => ∫ s in (0:ℝ)..1, f (s,p))
      (∫ s in (0:ℝ)..1, fderiv ℝ (fun p => f (s,p)) x) x := by
  obtain ⟨r,hr,hrU,hre⟩ := exists_smooth_local_identity (hU.mem_nhds hx)
  have hg : ContDiff ℝ ∞ (fun q : ℝ × P => f (q.1,r q.2)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro q
    exact (hf.contDiffAt ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,hrU q.2⟩)).comp q
      (contDiff_fst.prodMk (hr.comp contDiff_snd)).contDiffAt
  have hd := hasFDerivAt_fixed_integral hg x
  have hi : (fun p => ∫ s in (0:ℝ)..1, f (s,p)) =ᶠ[𝓝 x]
      (fun p => ∫ s in (0:ℝ)..1, f (s,r p)) := by
    filter_upwards [hre] with p hp
    rw [show r p = p from hp]
  have hD (s : ℝ) : fderiv ℝ (fun p => f (s,p)) x = fderiv ℝ (fun p => f (s,r p)) x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hre] with p hp
    rw [show r p = p from hp]
  simpa only [hD] using hd.congr_of_eventuallyEq hi


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_SmoothManifoldIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable (E : Type) (M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

variable {E M}
namespace SmoothCircleAction
variable (A : SmoothCircleAction E M)

theorem slice_smooth (s : ℝ) : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (A.slice s) :=
  A.smooth.comp (contMDiff_const.prodMk contMDiff_id)

theorem differential_add (s t : ℝ) (x : M) :
    A.differential (s+t) x = (A.differential s (A.slice t x)).comp (A.differential t x) := by
  have he : A.slice (s+t) = A.slice s ∘ A.slice t := funext (A.add s t)
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (A.slice (s+t)) x = _
  rw [he]
  exact ((A.slice_smooth s).mdifferentiable (by simp) _).hasMFDerivAt.comp x
    ((A.slice_smooth t).mdifferentiable (by simp) x).hasMFDerivAt |>.mfderiv

theorem slice_inverse (s : ℝ) (x : M) : A.slice (-s) (A.slice s x) = x := by
  change A.toFun (-s,A.toFun (s,x)) = x
  rw [←A.add,neg_add_cancel,A.zero]

theorem differential_invertible (s : ℝ) (x : M) : (A.differential s x).IsInvertible := by
  refine ContinuousLinearMap.IsInvertible.of_inverse (g := A.differential (-s) (A.slice s x)) ?_ ?_
  · have h := A.differential_add s (-s) (A.slice s x)
    rw [add_neg_cancel,A.differential_zero,A.slice_inverse] at h
    exact h.symm
  · rw [←A.differential_add,neg_add_cancel,A.differential_zero]

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem average_invariant (f : ℝ × M → ℝ) (t s : ℝ) (x : M) :
    A.average f (t,A.slice s x) = A.average f (t,x) := by
  have hp : Function.Periodic (fun r => f (t,A.slice r x)) 1 := by
    intro r
    change f (t,A.toFun (r+1,x)) = f (t,A.toFun (r,x))
    rw [A.period]
  change (∫ r in (0:ℝ)..1, f (t,A.toFun (r,A.toFun (s,x)))) = _
  simp_rw [←A.add]
  rw [intervalIntegral.integral_comp_add_right (fun r => f (t,A.toFun (r,x))) s]
  simpa only [zero_add,add_comm (1:ℝ) s,average,slice] using hp.intervalIntegral_add_eq s 0

end SmoothCircleAction

end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartOneForm_reconstruct (α : ManifoldOneForm E M) {c x : M}
    (hc : x ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    (chartOneForm α c (extChartAt 𝓘(ℝ,E) c x)).comp (chartDifferential c x) = α x := by
  have hC : (chartDifferential (E := E) c x).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hc using 1
    all_goals try with_reducible_and_instances rfl
  unfold chartOneForm
  rw [(extChartAt 𝓘(ℝ,E) c).left_inv hc]
  ext v
  exact congrArg (α x) (hC.inverse_apply_self v)

namespace SmoothCircleAction
variable (A : SmoothCircleAction E M)

theorem pullbackOneForm_continuous {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (t : ℝ) (x : M) :
    Continuous (fun s => parameterPullbackOneForm (E := E) (F := E) α A.toFun s t x) := by
  have hs := parameterPullbackOneForm_smooth (E := E) (F := E) A.smooth hα x
  have hc : Continuous (fun s : ℝ => chartOneForm
      (parameterPullbackOneForm (E := E) (F := E) α A.toFun s t) x (extChartAt 𝓘(ℝ,E) x x)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    have hfull : ContinuousAt (fun q : ℝ × (ℝ × E) => chartOneForm
        (parameterPullbackOneForm (E := E) (F := E) α A.toFun q.1 q.2.1) x q.2.2)
        (s,(t,extChartAt 𝓘(ℝ,E) x x)) :=
      (hs.contDiffAt ((isOpen_univ.prod (isOpen_univ.prod
        (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x))).mem_nhds
          ⟨mem_univ _,mem_univ _,mem_extChartAt_target x⟩)).continuousAt
    have hmap : ContinuousAt (fun r : ℝ => (r,(t,extChartAt 𝓘(ℝ,E) x x))) s :=
      continuousAt_id.prodMk continuousAt_const
    exact hfull.comp (f := fun r : ℝ => (r,(t,extChartAt 𝓘(ℝ,E) x x))) hmap
  have hh := hc.clm_comp (continuous_const (y := chartDifferential (E := E) x x))
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  exact (chartOneForm_reconstruct _ (mem_extChartAt_source x)).symm

theorem chart_averageOneForm {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (t : ℝ) (c : M) (y : E) :
    chartOneForm (A.averageOneForm α t) c y =
      ∫ s in (0:ℝ)..1, chartOneForm (parameterPullbackOneForm (E := E) (F := E) α A.toFun s t) c y := by
  let x := (extChartAt 𝓘(ℝ,E) c).symm y
  let L := (ContinuousLinearMap.compL ℝ E E ℝ).flip (chartDifferential (E := E) c x).inverse
  exact (L.intervalIntegral_comp_comm ((A.pullbackOneForm_continuous hα t x).intervalIntegrable 0 1)).symm

variable [FiniteDimensional ℝ E]

theorem averageOneForm_smooth {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (c : M) :
    ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (A.averageOneForm α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  have hs := contDiffOn_fixed_integral (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c))
    (parameterPullbackOneForm_smooth (E := E) (F := E) A.smooth hα c)
  apply hs.congr
  intro p _
  exact A.chart_averageOneForm hα p.1 c p.2

end SmoothCircleAction

end

section
open scoped ContDiff Topology
open Set Function
variable {S P F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_fiber_derivative {U : Set P} (hU : IsOpen U) {f : S × P → F}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun q : S × P => fderiv ℝ (fun p => f (q.1,p)) q.2) (univ ×ˢ U) := by
  have hD := (hf.fderiv_of_isOpen (m := ∞) (isOpen_univ.prod hU) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp
    (contDiffOn_const (c := ContinuousLinearMap.inr ℝ S P))
  apply hD.congr
  intro q hq
  have hc : HasFDerivAt (fun p : P => (q.1,p)) (ContinuousLinearMap.inr ℝ S P) q.2 := by
    convert! (hasFDerivAt_const (𝕜 := ℝ) q.1 q.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) q.2) using 1
    all_goals try with_reducible_and_instances rfl
  have hh := ((hf.contDiffAt ((isOpen_univ.prod hU).mem_nhds hq)).differentiableAt
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp q.2 hc
  exact hh.fderiv

theorem continuous_at_fixed_fiber_derivative {U : Set P} (hU : IsOpen U) {f : S × P → F}
    (hf : ContDiffOn ℝ ∞ f (univ ×ˢ U)) {x : P} (hx : x ∈ U) :
    Continuous (fun s : S => fderiv ℝ (fun p => f (s,p)) x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  exact ((contDiffOn_fiber_derivative hU hf).contDiffAt
    ((isOpen_univ.prod hU).mem_nhds ⟨mem_univ _,hx⟩)).continuousAt.comp
      (continuousAt_id.prodMk continuousAt_const)


end

section
open scoped ContDiff Topology
open Set Function
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem timePullbackTwoForm_contDiffAt {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {g : F → E} {p : ℝ × F} (hΩ : ContDiffAt ℝ ∞ Ω (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2) : ContDiffAt ℝ ∞ (timePullbackTwoForm Ω g) p := by
  have hval := hΩ.comp p (contDiffAt_fst.prodMk (hg.comp p contDiffAt_snd))
  have hd := (hg.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp p contDiffAt_snd
  exact smooth_bilinear_flip ((smooth_bilinear_flip (hval.clm_comp hd)).clm_comp hd)

theorem timePullbackOneForm_fderiv {α : ℝ × E → E →L[ℝ] ℝ}
    {g : F → E} {p : ℝ × F} (hα : ContDiffAt ℝ ∞ α (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2) (v : ℝ × F) (w : F) :
    fderiv ℝ (timePullbackOneForm α g) p v w =
      fderiv ℝ α (p.1,g p.2) (v.1,fderiv ℝ g p.2 v.2) (fderiv ℝ g p.2 w) +
      α (p.1,g p.2) (fderiv ℝ (fderiv ℝ g) p.2 v.2 w) := by
  have hmap := (hasFDerivAt_fst (p := p)).prodMk
    ((hg.differentiableAt (by simp)).hasFDerivAt.comp p (hasFDerivAt_snd (p := p)))
  have hd := ((hα.differentiableAt (by simp)).hasFDerivAt.comp p hmap).clm_comp
    (((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.comp p
      (hasFDerivAt_snd (p := p)))
  rw [show fderiv ℝ (timePullbackOneForm α g) p = _ from hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.prod_apply]
  exact add_comm _ _

theorem timePullbackOneForm_exterior {α : ℝ × E → E →L[ℝ] ℝ}
    {g : F → E} {p : ℝ × F} (hα : ContDiffAt ℝ ∞ α (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2) (v w : F) :
    fderiv ℝ (timePullbackOneForm α g) p (0,v) w -
      fderiv ℝ (timePullbackOneForm α g) p (0,w) v =
    fderiv ℝ α (p.1,g p.2) (0,fderiv ℝ g p.2 v) (fderiv ℝ g p.2 w) -
      fderiv ℝ α (p.1,g p.2) (0,fderiv ℝ g p.2 w) (fderiv ℝ g p.2 v) := by
  rw [timePullbackOneForm_fderiv hα hg,timePullbackOneForm_fderiv hα hg]
  have hs := hg.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs.eq v w]
  simp only
  ring

theorem timePullbackTwoForm_time {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {g : F → E} {p : ℝ × F} (hΩ : ContDiffAt ℝ ∞ Ω (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2) (v w : F) :
    fderiv ℝ (timePullbackTwoForm Ω g) p (1,0) v w =
      fderiv ℝ Ω (p.1,g p.2) (1,0) (fderiv ℝ g p.2 v) (fderiv ℝ g p.2 w) := by
  have hL := (((timePullbackTwoForm_contDiffAt hΩ hg).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.clm_apply
    (hasFDerivAt_const v p)).clm_apply (hasFDerivAt_const w p)
  have hLt := hL.comp_hasDerivAt p.1 ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have hR := (((hΩ.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.clm_apply
    (hasFDerivAt_const (fderiv ℝ g p.2 v) (p.1,g p.2))).clm_apply
    (hasFDerivAt_const (fderiv ℝ g p.2 w) (p.1,g p.2))).comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 (g p.2)))
  have he := hLt.unique hR
  simpa only [add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,ContinuousLinearMap.apply_apply,
    zero_apply,map_zero,zero_add] using he

theorem timePullback_exact_time {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} {g : F → E} {p : ℝ × F}
    (hΩ : ContDiffAt ℝ ∞ Ω (p.1,g p.2)) (hα : ContDiffAt ℝ ∞ α (p.1,g p.2))
    (hg : ContDiffAt ℝ ∞ g p.2)
    (he : ∀ v w, fderiv ℝ Ω (p.1,g p.2) (1,0) v w =
      fderiv ℝ α (p.1,g p.2) (0,v) w - fderiv ℝ α (p.1,g p.2) (0,w) v) (v w : F) :
    fderiv ℝ (timePullbackTwoForm Ω g) p (1,0) v w =
      fderiv ℝ (timePullbackOneForm α g) p (0,v) w -
      fderiv ℝ (timePullbackOneForm α g) p (0,w) v := by
  rw [timePullbackTwoForm_time hΩ hg,timePullbackOneForm_exterior hα hg]
  exact he _ _


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_RelativeJets_SymplecticProjectionNaturality
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.chartOneForm_sub _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_inside _root_.OAI.PackingSufficiencySupport.Hamiltonian.extendManifoldOneForm_outside _root_.OAI.PackingSufficiencySupport.Hamiltonian.manifoldWedge_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_apply _root_.OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift_vertical _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open Set Function
open scoped ContDiff Topology
open scoped Manifold
open Manifold IsManifold
section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem symplecticProjection_natural
    {Ω₀ Ω₁ : E →L[ℝ] E →L[ℝ] ℝ} {i₀ i₁ : F →L[ℝ] E}
    {L : E →L[ℝ] E} {K : F →L[ℝ] F}
    (h₀ : (Ω₀.bilinearComp i₀ i₀).IsInvertible)
    (h₁ : (Ω₁.bilinearComp i₁ i₁).IsInvertible)
    (hK : Surjective K) (hL : ∀ u v, Ω₁ (L u) (L v) = Ω₀ u v)
    (hi : ∀ u, L (i₀ u) = i₁ (K u)) (x : E) :
    symplecticProjection Ω₁ i₁ (L x) = K (symplecticProjection Ω₀ i₀ x) := by
  apply h₁.injective
  ext w
  obtain ⟨u,rfl⟩ := hK w
  change Ω₁ (i₁ (symplecticProjection Ω₁ i₁ (L x))) (i₁ (K u)) =
    Ω₁ (i₁ (K (symplecticProjection Ω₀ i₀ x))) (i₁ (K u))
  rw [symplecticProjection_pairing h₁,←hi,←hi,hL,hL,symplecticProjection_pairing h₀]

theorem normal_annihilation_pullback
    {Ω₀ Ω₁ : E →L[ℝ] E →L[ℝ] ℝ} {i₀ i₁ : F →L[ℝ] E}
    {L : E →L[ℝ] E} {K : F →L[ℝ] F} {β : E →L[ℝ] ℝ}
    (h₀ : (Ω₀.bilinearComp i₀ i₀).IsInvertible)
    (h₁ : (Ω₁.bilinearComp i₁ i₁).IsInvertible)
    (hK : Surjective K) (hL : ∀ u v, Ω₁ (L u) (L v) = Ω₀ u v)
    (hi : ∀ u, L (i₀ u) = i₁ (K u))
    (hβ : ∀ v, β v = β (i₁ (symplecticProjection Ω₁ i₁ v))) (v : E) :
    β (L v) = β (L (i₀ (symplecticProjection Ω₀ i₀ v))) := by
  rw [hβ (L v),symplecticProjection_natural h₀ h₁ hK hL hi,hi]

theorem moser_vector_tangent_of_annihilation
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E}
    (hΩ : Ω.IsInvertible) (hi : (Ω.bilinearComp i i).IsInvertible)
    (hskew : ∀ u v, Ω u v = -Ω v u) (β : E →L[ℝ] ℝ)
    (hb : ∀ v, β v = β (i (symplecticProjection Ω i v))) :
    -Ω.inverse β = i (-((Ω.bilinearComp i i).inverse (β.comp i))) := by
  have hz : symplecticNormalJet Ω i β = 0 := by
    ext v
    exact sub_eq_zero.mpr (hb v).symm
  simpa only [hz,add_zero] using corrected_moser_vector_tangent hΩ hi hskew β

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem localNormalJet_hasFDerivAt {β : E → E →L[ℝ] ℝ} {r : E → E} {x : E}
    (hβ : DifferentiableAt ℝ β x) (hr : DifferentiableAt ℝ r x)
    (hx : r x = x) (hβr : (β x).comp (fderiv ℝ r x) = 0) :
    HasFDerivAt (localNormalJet β r) (β x) x := by
  apply (hβ.hasFDerivAt.clm_apply ((hasFDerivAt_id x).sub hr.hasFDerivAt)).congr_fderiv
  ext v
  have hz : β x (fderiv ℝ r x v) = 0 :=
    congrArg (fun A : E →L[ℝ] ℝ => A v) hβr
  simp only [ContinuousLinearMap.comp_apply,Pi.sub_apply,id_eq,hx,sub_self,map_zero,add_zero,
    sub_apply,ContinuousLinearMap.id_apply,map_sub,hz,sub_zero]

end
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem splitRetraction_eq {L : (F × G) ≃L[ℝ] E} {x : E}
    (hx : (L.symm x).2 = 0) : splitRetraction L x = x := by
  change L ((L.symm x).1,0) = x
  rw [←hx,Prod.mk.eta,L.apply_symm_apply]

theorem localSymplecticPotential_zero {L : (F × G) ≃L[ℝ] E}
    (Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (α : ℝ × E → E →L[ℝ] ℝ) {p : ℝ × E}
    (hp : (L.symm p.2).2 = 0) : localSymplecticPotential L Ω α p = 0 := by
  simp only [localSymplecticPotential,splitRetraction_eq hp,sub_self,map_zero]

variable [CompleteSpace F]

theorem symplecticNormalJet_contDiffAt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {Ω : P → E →L[ℝ] E →L[ℝ] ℝ} {α : P → E →L[ℝ] ℝ}
    {i : P → F →L[ℝ] E} {p : P}
    (hΩ : ContDiffAt ℝ ∞ Ω p) (hα : ContDiffAt ℝ ∞ α p) (hi : ContDiffAt ℝ ∞ i p)
    (hinv : ((Ω p).bilinearComp (i p) (i p)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun q => symplecticNormalJet (Ω q) (i q) (α q)) p :=
  (hα.clm_comp (hi.clm_comp (symplecticProjection_contDiffAt hΩ hi hinv))).sub hα

theorem localSymplecticPotential_contDiffAt {L : (F × G) ≃L[ℝ] E}
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {α : ℝ × E → E →L[ℝ] ℝ} {p : ℝ × E}
    (hΩ : ContDiffAt ℝ ∞ Ω p) (hα : ContDiffAt ℝ ∞ α p)
    (hinv : ((Ω p).bilinearComp (splitInclusion L) (splitInclusion L)).IsInvertible) :
    ContDiffAt ℝ ∞ (localSymplecticPotential L Ω α) p :=
  (symplecticNormalJet_contDiffAt hΩ hα contDiffAt_const hinv).clm_apply
    (contDiffAt_snd.sub ((splitRetraction L).contDiff.contDiffAt.comp p contDiffAt_snd))

theorem localSymplecticPotential_hasFDerivAt {L : (F × G) ≃L[ℝ] E}
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {α : ℝ × E → E →L[ℝ] ℝ} {p : ℝ × E}
    (hΩ : ContDiffAt ℝ ∞ Ω p) (hα : ContDiffAt ℝ ∞ α p)
    (hinv : ((Ω p).bilinearComp (splitInclusion L) (splitInclusion L)).IsInvertible)
    (hp : (L.symm p.2).2 = 0) :
    HasFDerivAt (localSymplecticPotential L Ω α)
      ((symplecticNormalJet (Ω p) (splitInclusion L) (α p)).comp
        (ContinuousLinearMap.snd ℝ ℝ E)) p := by
  let β : ℝ × E → (ℝ × E) →L[ℝ] ℝ := fun q =>
    (symplecticNormalJet (Ω q) (splitInclusion L) (α q)).comp (ContinuousLinearMap.snd ℝ ℝ E)
  let r : (ℝ × E) →L[ℝ] ℝ × E :=
    (ContinuousLinearMap.fst ℝ ℝ E).prod ((splitRetraction L).comp (ContinuousLinearMap.snd ℝ ℝ E))
  have he : localSymplecticPotential L Ω α = localNormalJet β r := rfl
  rw [he]
  apply localNormalJet_hasFDerivAt
    (((symplecticNormalJet_contDiffAt hΩ hα contDiffAt_const hinv).clm_comp
      contDiffAt_const).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) r.differentiableAt
  · exact Prod.ext rfl (splitRetraction_eq hp)
  · rw [r.fderiv]
    apply ContinuousLinearMap.ext
    intro v
    exact symplecticNormalJet_tangent hinv (α p) ((L.symm v.2).1)

end
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

variable [CompleteSpace F]

theorem relativeLocalDomain_isOpen {Ω : ℝ → ManifoldTwoForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {d : OpenPartialHomeomorph M E} (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E) : IsOpen (relativeLocalDomain Ω d L) := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hp' : p.2 ∈ d.source := hp.1
  have hform := euclideanPullbackTwoForm_contDiffAt (p := (p.1,d p.2)) hΩ
    (contMDiffAt_symm_of_mem_maximalAtlas hd (d.map_source hp'))
  have hi : ContDiffAt ℝ ∞ (fun q : ℝ × E => (euclideanPullbackTwoForm Ω d.symm q).bilinearComp
      (splitInclusion L) (splitInclusion L)) (p.1,d p.2) :=
    smooth_bilinear_flip ((smooth_bilinear_flip (hform.clm_comp contDiffAt_const)).clm_comp contDiffAt_const)
  have hc : ContinuousAt (fun q : ℝ × M => (q.1,d q.2)) p :=
    continuousAt_fst.prodMk ((d.continuousOn.continuousAt (d.open_source.mem_nhds hp')).comp
      continuousAt_snd)
  have hn := (hi.continuousAt.comp (f := fun q : ℝ × M => (q.1,d q.2)) hc).preimage_mem_nhds
    (ContinuousLinearEquiv.isOpen.mem_nhds hp.2)
  filter_upwards [hn,continuousAt_snd.preimage_mem_nhds (d.open_source.mem_nhds hp')] with q hq hqs
  exact ⟨hqs,hq⟩

theorem relativeLocalPotential_contMDiffOn {Ω : ℝ → ManifoldTwoForm E M}
    {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {d : OpenPartialHomeomorph M E} (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E) :
    ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (relativeLocalPotential Ω α d L) (relativeLocalDomain Ω d L) := by
  intro p hp
  have hi := contMDiffAt_symm_of_mem_maximalAtlas hd (d.map_source hp.1)
  have hf := localSymplecticPotential_contDiffAt
    (euclideanPullbackTwoForm_contDiffAt (p := (p.1,d p.2)) hΩ hi)
    (euclideanPullbackOneForm_contDiffAt (p := (p.1,d p.2)) hα hi) hp.2
  have hc : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ × E) ∞
      (fun q : ℝ × M => (q.1,d q.2)) p := contMDiffAt_fst.prodMk_space
    ((contMDiffAt_of_mem_maximalAtlas hd hp.1).comp p contMDiffAt_snd)
  exact (hf.contMDiffAt.comp p hc).contMDiffWithinAt

end
section

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem symplecticProjection_reparametrize
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E} (D : G ≃L[ℝ] F)
    (hi : (Ω.bilinearComp i i).IsInvertible)
    (hi' : (Ω.bilinearComp (i.comp D.toContinuousLinearMap) (i.comp D.toContinuousLinearMap)).IsInvertible) (x : E) :
    symplecticProjection Ω (i.comp D.toContinuousLinearMap) x = D.symm (symplecticProjection Ω i x) := by
  apply hi'.injective
  apply ContinuousLinearMap.ext
  intro u
  rw [show (Ω.bilinearComp (i.comp D.toContinuousLinearMap) (i.comp D.toContinuousLinearMap))
      (symplecticProjection Ω (i.comp D.toContinuousLinearMap) x) u = Ω x (i (D u)) from
        symplecticProjection_pairing hi' x u]
  change Ω x (i (D u)) = Ω (i (D (D.symm (symplecticProjection Ω i x)))) (i (D u))
  rw [D.apply_symm_apply,symplecticProjection_pairing hi]

theorem symplecticNormalJet_reparametrize
    {Ω : E →L[ℝ] E →L[ℝ] ℝ} {i : F →L[ℝ] E} (D : G ≃L[ℝ] F)
    (hi : (Ω.bilinearComp i i).IsInvertible)
    (hi' : (Ω.bilinearComp (i.comp D.toContinuousLinearMap) (i.comp D.toContinuousLinearMap)).IsInvertible) (α : E →L[ℝ] ℝ) :
    symplecticNormalJet Ω (i.comp D.toContinuousLinearMap) α = symplecticNormalJet Ω i α := by
  ext x
  change α (i (D (symplecticProjection Ω (i.comp D.toContinuousLinearMap) x))) - α x =
    α (i (symplecticProjection Ω i x)) - α x
  rw [symplecticProjection_reparametrize D hi hi',D.apply_symm_apply]

theorem symplecticProjection_changeCoordinates (C : E ≃L[ℝ] H)
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E) (x : E) :
    symplecticProjection (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap) (C.toContinuousLinearMap.comp i) (C x) =
      symplecticProjection Ω i x := by
  have hB : (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap).bilinearComp
      (C.toContinuousLinearMap.comp i) (C.toContinuousLinearMap.comp i) = Ω.bilinearComp i i := by
    ext u v
    simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,C.symm_apply_apply]
  simp only [symplecticProjection,hB,ContinuousLinearMap.comp_apply]
  congr 1
  ext u
  simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearEquiv.coe_coe,C.symm_apply_apply]

theorem symplecticNormalJet_changeCoordinates (C : E ≃L[ℝ] H)
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E) (α : E →L[ℝ] ℝ) (x : E) :
    symplecticNormalJet (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap)
      (C.toContinuousLinearMap.comp i) (α.comp C.symm.toContinuousLinearMap) (C x) = symplecticNormalJet Ω i α x := by
  change α (C.symm (C (i (symplecticProjection (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap)
    (C.toContinuousLinearMap.comp i) (C x))))) - α (C.symm (C x)) = _
  rw [C.symm_apply_apply,C.symm_apply_apply,symplecticProjection_changeCoordinates]
  rfl

end
section

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem adapted_restriction_isInvertible
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E)
    (C : E ≃L[ℝ] E) (D : F ≃L[ℝ] F) (L : (F × G) ≃L[ℝ] E)
    (hsplit : splitInclusion (F := F) (G := G) L = C.toContinuousLinearMap.comp (i.comp D.symm.toContinuousLinearMap))
    (hi : (Ω.bilinearComp i i).IsInvertible) :
    ((Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap).bilinearComp
      (splitInclusion (F := F) (G := G) L) (splitInclusion (F := F) (G := G) L)).IsInvertible := by
  have hB : (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap).bilinearComp
      (splitInclusion (F := F) (G := G) L) (splitInclusion (F := F) (G := G) L) =
        (Ω.bilinearComp i i).bilinearComp D.symm.toContinuousLinearMap D.symm.toContinuousLinearMap := by
    rw [hsplit]
    ext u v
    simp only [ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe,C.symm_apply_apply]
  rw [hB]
  exact bilinearComp_isInvertible hi ⟨D.symm,rfl⟩

theorem adapted_normal_jet
    (Ω : E →L[ℝ] E →L[ℝ] ℝ) (i : F →L[ℝ] E) (α : E →L[ℝ] ℝ)
    (C : E ≃L[ℝ] E) (D : F ≃L[ℝ] F) (L : (F × G) ≃L[ℝ] E)
    (hsplit : splitInclusion (F := F) (G := G) L = C.toContinuousLinearMap.comp (i.comp D.symm.toContinuousLinearMap))
    (hi : (Ω.bilinearComp i i).IsInvertible) (v : E) :
    symplecticNormalJet
      (Ω.bilinearComp C.symm.toContinuousLinearMap C.symm.toContinuousLinearMap)
      (splitInclusion (F := F) (G := G) L) (α.comp C.symm.toContinuousLinearMap) (C v) =
        symplecticNormalJet Ω i α v := by
  rw [hsplit,symplecticNormalJet_changeCoordinates]
  have hi' : (Ω.bilinearComp (i.comp D.symm.toContinuousLinearMap)
      (i.comp D.symm.toContinuousLinearMap)).IsInvertible := by
    have he : Ω.bilinearComp (i.comp D.symm.toContinuousLinearMap)
        (i.comp D.symm.toContinuousLinearMap) =
        (Ω.bilinearComp i i).bilinearComp D.symm.toContinuousLinearMap D.symm.toContinuousLinearMap := by
      ext u v
      rfl
    rw [he]
    exact bilinearComp_isInvertible hi ⟨D.symm,rfl⟩
  rw [symplecticNormalJet_reparametrize D.symm hi hi']

end

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

private theorem fderiv_eq_of_hasFDerivAt {f : F → E} {f' : F →L[ℝ] E} {x : F}
    (h : HasFDerivAt f f' x) : fderiv ℝ f x = f' := h.fderiv

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem adapted_inclusion_differential {e : N → M}
    {c : OpenPartialHomeomorph N F} {d : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,F) ∞ N) (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E)
    (heq : EqOn (d ∘ e ∘ c.symm) (fun y => L (y,0)) c.target)
    {b : N} (hb : b ∈ c.source) (hdb : e b ∈ d.source)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e b) :
    splitInclusion (E := E) (F := F) (G := G) L =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b) : E →L[ℝ] E).comp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e b : F →L[ℝ] E).comp
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) c.symm (c b) : F →L[ℝ] F)) := by
  have hi := (contMDiffAt_symm_of_mem_maximalAtlas hc (c.map_source hb)).mdifferentiableAt (by simp)
  have he' : HasMFDerivAt 𝓘(ℝ,F) 𝓘(ℝ,E) e (c.symm (c b))
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e b) := by rw [c.left_inv hb]; exact he.hasMFDerivAt
  have hd' : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) d (e (c.symm (c b)))
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b)) := by
    rw [c.left_inv hb]
    exact (contMDiffAt_of_mem_maximalAtlas hd hdb).mdifferentiableAt (by simp) |>.hasMFDerivAt
  have hfd : HasFDerivAt (d ∘ e ∘ c.symm)
      ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b) : E →L[ℝ] E).comp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e b : F →L[ℝ] E).comp
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) c.symm (c b) : F →L[ℝ] F))) (c b) :=
    hasMFDerivAt_iff_hasFDerivAt.mp (hd'.comp (c b) (he'.comp (c b) hi.hasMFDerivAt))
  have hcomp : fderiv ℝ (d ∘ e ∘ c.symm) (c b) =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b) : E →L[ℝ] E).comp
        ((mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) e b : F →L[ℝ] E).comp
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,F) c.symm (c b) : F →L[ℝ] F)) := fderiv_eq_of_hasFDerivAt hfd
  have hloc : (d ∘ e ∘ c.symm) =ᶠ[𝓝 (c b)] fun y => L (y,0) :=
    heq.eventuallyEq_of_mem (c.open_target.mem_nhds (c.map_source hb))
  rw [hloc.fderiv_eq (𝕜 := ℝ)] at hcomp
  have hf : fderiv ℝ (fun y : F => L (y,0)) (c b) = splitInclusion (E := E) (F := F) (G := G) L := by
    exact (splitInclusion (E := E) (F := F) (G := G) L).fderiv
  rw [hf] at hcomp
  exact hcomp

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem maximalChart_pullback_two (Ω : ℝ → ManifoldTwoForm E M)
    {d : OpenPartialHomeomorph M E} (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    {x : M} (hx : x ∈ d.source) (t : ℝ) :
    euclideanPullbackTwoForm Ω d.symm (t,d x) =
      (Ω t x).bilinearComp (maximalChartLinearEquiv hd hx).symm.toContinuousLinearMap
        (maximalChartLinearEquiv hd hx).symm.toContinuousLinearMap := by
  dsimp [euclideanPullbackTwoForm]
  rw [d.left_inv hx]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem maximalChart_pullback_one (α : ℝ → ManifoldOneForm E M)
    {d : OpenPartialHomeomorph M E} (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    {x : M} (hx : x ∈ d.source) (t : ℝ) :
    euclideanPullbackOneForm α d.symm (t,d x) =
      (α t x).comp (maximalChartLinearEquiv hd hx).symm.toContinuousLinearMap := by
  dsimp [euclideanPullbackOneForm]
  rw [d.left_inv hx]
  rfl

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem relativeLocalDomain_mem (Ω : ℝ → ManifoldTwoForm E M) {e : N → M}
    {c : OpenPartialHomeomorph N F} {d : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,F) ∞ N) (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E)
    (heq : EqOn (d ∘ e ∘ c.symm) (fun y => L (y,0)) c.target)
    {b : N} (hb : b ∈ c.source) (hdb : e b ∈ d.source)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e b) {t : ℝ}
    (hi : ((Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
      (manifoldMapDifferential (E := E) (F := F) e b)).IsInvertible) :
    (t,e b) ∈ relativeLocalDomain Ω d L := by
  refine ⟨hdb,?_⟩
  rw [maximalChart_pullback_two Ω hd hdb]
  exact adapted_restriction_isInvertible _ _ (maximalChartLinearEquiv hd hdb)
    (maximalChartLinearEquiv hc hb) L (adapted_inclusion_differential hc hd L heq hb hdb he) hi

variable [CompleteSpace F]

omit [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem relativeLocalPotential_hasMFDerivAt
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {c : OpenPartialHomeomorph N F} {d : OpenPartialHomeomorph M E}
    (hc : c ∈ maximalAtlas 𝓘(ℝ,F) ∞ N) (hd : d ∈ maximalAtlas 𝓘(ℝ,E) ∞ M)
    (L : (F × G) ≃L[ℝ] E)
    (heq : EqOn (d ∘ e ∘ c.symm) (fun y => L (y,0)) c.target)
    {b : N} (hb : b ∈ c.source) (hdb : e b ∈ d.source)
    (he : MDifferentiableAt 𝓘(ℝ,F) 𝓘(ℝ,E) e b) {t : ℝ}
    (hi : ((Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
      (manifoldMapDifferential (E := E) (F := F) e b)).IsInvertible) :
    HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ)
      (relativeLocalPotential Ω α d L) (t,e b)
      ((symplecticNormalJet (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) (α t (e b))).comp
        (ContinuousLinearMap.snd ℝ ℝ E)) := by
  have hds := contMDiffAt_symm_of_mem_maximalAtlas hd (d.map_source hdb)
  have hinv := (relativeLocalDomain_mem Ω hc hd L heq hb hdb he hi).2
  have hzero : (L.symm (d (e b))).2 = 0 := by
    have h := heq (c.map_source hb)
    simp only [Function.comp_apply,c.left_inv hb] at h
    rw [h,L.symm_apply_apply]
  have hf := localSymplecticPotential_hasFDerivAt
    (euclideanPullbackTwoForm_contDiffAt (p := (t,d (e b))) hΩ hds)
    (euclideanPullbackOneForm_contDiffAt (p := (t,d (e b))) hα hds) hinv hzero
  have ha : HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) Prod.fst (t,e b)
      (ContinuousLinearMap.fst ℝ ℝ E) := hasMFDerivAt_fst (t,e b)
  have hb' := ((contMDiffAt_of_mem_maximalAtlas hd hdb).mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasMFDerivAt.comp
      (t,e b) (hasMFDerivAt_snd (I := 𝓘(ℝ,ℝ)) (I' := 𝓘(ℝ,E)) (t,e b))
  have hcoord : HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ × E)
      (fun q : ℝ × M => (q.1,d q.2)) (t,e b)
      ((ContinuousLinearMap.fst ℝ ℝ E).prod
        ((mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b)).comp (ContinuousLinearMap.snd ℝ ℝ E))) :=
    ⟨ha.1.prodMk hb'.1,ha.2.prodMk hb'.2⟩
  have hcomp := (hasMFDerivAt_iff_hasFDerivAt.mpr hf).comp (t,e b) hcoord
  apply hcomp.congr_mfderiv
  ext v
  change symplecticNormalJet (euclideanPullbackTwoForm Ω d.symm (t,d (e b)))
    (splitInclusion L) (euclideanPullbackOneForm α d.symm (t,d (e b)))
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) d (e b) v.2) = _
  rw [maximalChart_pullback_two Ω hd hdb,maximalChart_pullback_one α hd hdb]
  exact adapted_normal_jet _ _ _ (maximalChartLinearEquiv hd hdb)
    (maximalChartLinearEquiv hc hb) L (adapted_inclusion_differential hc hd L heq hb hdb he) hi v.2

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_RelativeJets_EmbeddingAdaptedNeighborhood
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem embedding_adapted_neighborhood {e : N → M}
    (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) (a : N) :
    let h := he.isImmersion.isImmersionAt a
    ∃ U : Set M, IsOpen U ∧ e a ∈ U ∧ U ⊆ h.codChart.source ∧
      ∀ b : N, e b ∈ U → b ∈ h.domChart.source ∧
        h.equiv.symm ((h.codChart.extend 𝓘(ℝ,E)) (e b)) =
          ((h.domChart.extend 𝓘(ℝ,F)) b,0) := by
  let h := he.isImmersion.isImmersionAt a
  obtain ⟨V,hV,hpre⟩ := he.isEmbedding.isInducing.isOpen_iff.mp h.domChart.open_source
  refine ⟨V ∩ h.codChart.source,hV.inter h.codChart.open_source,?_,inter_subset_right,?_⟩
  · constructor
    · have ha := h.mem_domChart_source
      rw [←hpre] at ha
      exact ha
    · exact h.mem_codChart_source
  · intro b hb
    have hb' : b ∈ h.domChart.source := by rw [←hpre]; exact hb.1
    refine ⟨hb',?_⟩
    have hz : b ∈ (h.domChart.extend 𝓘(ℝ,F)).source := by
      simpa only [OpenPartialHomeomorph.extend_source] using hb'
    have hh := h.writtenInCharts ((h.domChart.extend 𝓘(ℝ,F)).map_source hz)
    simp only [Function.comp_apply,(h.domChart.extend 𝓘(ℝ,F)).left_inv hz] at hh
    rw [hh,h.equiv.symm_apply_apply]


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold IsManifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem exists_relative_jet_patch
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {T : Set ℝ}
    (hi : ∀ t ∈ T, ∀ b, ((Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
      (manifoldMapDifferential (E := E) (F := F) e b)).IsInvertible) (a : N) :
    ∃ U : Set (ℝ × M), ∃ f : ℝ × M → ℝ,
      IsOpen U ∧ (∀ t ∈ T, (t,e a) ∈ U) ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f U ∧
      ∀ t ∈ T, ∀ b, (t,e b) ∈ U → f (t,e b) = 0 ∧
        HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) f (t,e b)
          ((symplecticNormalJet (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) (α t (e b))).comp
            (ContinuousLinearMap.snd ℝ ℝ E)) := by
  let h := he.isImmersion.isImmersionAt a
  obtain ⟨V,hV,ha,hVd,hVb⟩ := embedding_adapted_neighborhood he a
  have hw : EqOn (h.codChart ∘ e ∘ h.domChart.symm)
      (fun y => h.equiv (y,0)) h.domChart.target := by
    simpa only [Function.comp_def, mfld_simps] using h.writtenInCharts
  let U := relativeLocalDomain Ω h.codChart h.equiv ∩ (univ ×ˢ V)
  refine ⟨U,relativeLocalPotential Ω α h.codChart h.equiv,?_,?_,?_,?_⟩
  · exact (relativeLocalDomain_isOpen hΩ h.codChart_mem_maximalAtlas h.equiv).inter
      (isOpen_univ.prod hV)
  · intro t ht
    exact ⟨relativeLocalDomain_mem Ω h.domChart_mem_maximalAtlas h.codChart_mem_maximalAtlas
      h.equiv hw h.mem_domChart_source h.mem_codChart_source
      (he.contMDiff.mdifferentiable (by simp) a) (hi t ht a),mem_univ _,ha⟩
  · exact (relativeLocalPotential_contMDiffOn hΩ hα h.codChart_mem_maximalAtlas h.equiv).mono
      inter_subset_left
  · intro t ht b hb
    have hbb := hVb b hb.2.2
    have hbd := hVd hb.2.2
    constructor
    · apply localSymplecticPotential_zero
      simpa using congrArg Prod.snd hbb.2
    · exact relativeLocalPotential_hasMFDerivAt hΩ hα h.domChart_mem_maximalAtlas
        h.codChart_mem_maximalAtlas h.equiv hw hbb.1 hbd
        (he.contMDiff.mdifferentiable (by simp) b) (hi t ht b)


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type}

omit [IsManifold I ∞ M] in

theorem smoothPartition_eventually_finite_sum {S : Set M}
    (ρ : SmoothPartitionOfUnity ι I M S) (g : ι → M → ℝ) (x : M) :
    (fun y => ∑ᶠ i, ρ i y • g i y) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ ρ.fintsupport x, ρ i y • g i y) := by
  classical
  filter_upwards [ρ.eventually_finsupport_subset x] with y hy
  rw [←ρ.sum_finsupport_smul_eq_finsum y g]
  apply Finset.sum_subset hy
  intro i hi hni
  have hz : ρ i y = 0 := by
    simpa only [ρ.mem_finsupport,mem_support,not_not] using hni
  rw [hz,zero_smul]

omit [IsManifold I ∞ M] in

theorem smoothPartition_glues_zero_first_jet {S : Set M}
    (ρ : SmoothPartitionOfUnity ι I M S) {U : ι → Set M}
    (hρ : ρ.IsSubordinate U)
    {g : ι → M → ℝ} {β : (x : M) → TangentSpace I x →L[ℝ] ℝ}
    (hzero : ∀ i x, x ∈ S → x ∈ U i → g i x = 0)
    (hjet : ∀ i x, x ∈ S → x ∈ U i → HasMFDerivAt I 𝓘(ℝ,ℝ) (g i) x (β x))
    (x : M) (hx : x ∈ S) :
    (∑ᶠ i, ρ i x • g i x) = 0 ∧
    HasMFDerivAt I 𝓘(ℝ,ℝ) (fun y => ∑ᶠ i, ρ i y • g i y) x (β x) := by
  classical
  have hloc := smoothPartition_eventually_finite_sum ρ g x
  have hmem (i : ι) (hi : i ∈ ρ.fintsupport x) : x ∈ U i :=
    hρ i ((ρ.mem_fintsupport_iff x i).1 hi)
  constructor
  · rw [hloc.eq_of_nhds]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i x hx (hmem i hi),smul_zero]
  · have hd (i : ι) (hi : i ∈ ρ.fintsupport x) :
        HasMFDerivAt I 𝓘(ℝ,ℝ) (fun y => ρ i y • g i y) x (ρ i x • β x) := by
      have hp := ((ρ i).contMDiff.mdifferentiable (by simp) x).hasMFDerivAt
      refine (hp.mul (hjet i x hx (hmem i hi))).congr_mfderiv ?_
      let A : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ,ℝ) (ρ i) x
      change ρ i x • β x + g i x • A = ρ i x • β x
      rw [hzero i x hx (hmem i hi), zero_smul, add_zero]
    have hsum := HasMFDerivAt.sum (I := I) (t := ρ.fintsupport x)
      (f := fun i y => ρ i y • g i y) (f' := fun i => ρ i x • β x) hd
    have hweights : (∑ i ∈ ρ.fintsupport x, ρ i x • β x) = β x := by
      rw [←Finset.sum_smul,ρ.sum_finsupport' x hx (ρ.finsupport_subset_fintsupport x),one_smul]
    rw [hweights] at hsum
    exact hsum.congr_of_eventuallyEq (by
      filter_upwards [hloc] with y hy
      simpa only [Finset.sum_apply] using hy)

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

theorem exists_smooth_zero_first_jet {S : Set M} (hS : IsClosed S)
    {U : ι → Set M} (hU : ∀ i, IsOpen (U i)) (hcover : S ⊆ ⋃ i, U i)
    {g : ι → M → ℝ} (hg : ∀ i, ContMDiffOn I 𝓘(ℝ,ℝ) ∞ (g i) (U i))
    {β : (x : M) → TangentSpace I x →L[ℝ] ℝ}
    (hzero : ∀ i x, x ∈ S → x ∈ U i → g i x = 0)
    (hjet : ∀ i x, x ∈ S → x ∈ U i → HasMFDerivAt I 𝓘(ℝ,ℝ) (g i) x (β x)) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ,ℝ) ∞ f ∧
      ∀ x ∈ S, f x = 0 ∧ HasMFDerivAt I 𝓘(ℝ,ℝ) f x (β x) := by
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hS U hU hcover
  exact ⟨_,hρ.contMDiff_finsum_smul hU hg,
    fun x hx => smoothPartition_glues_zero_first_jet ρ hρ hzero hjet x hx⟩


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold IsManifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} {N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
theorem embeddedNormalJet_apply (Ω : ℝ → ManifoldTwoForm E M) (α : ℝ → ManifoldOneForm E M)
    {e : N → M} (he : Injective e) (t : ℝ) (b : N) :
    embeddedNormalJet (F := F) Ω α e (t,e b) =
      (symplecticNormalJet (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) (α t (e b))).comp
        (ContinuousLinearMap.snd ℝ ℝ E) := by
  classical
  have hx : ∃ a, e a = (t,e b).2 := ⟨b,rfl⟩
  have hy : hx.choose = b := he hx.choose_spec
  simp only [embeddedNormalJet,dite_eq_left hx,hy]

variable [CompleteSpace F] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

omit [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem exists_relative_global_potential
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) (hclosed : IsClosed (range e))
    {T : Set ℝ} (hT : IsClosed T)
    (hi : ∀ t ∈ T, ∀ b, ((Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
      (manifoldMapDifferential (E := E) (F := F) e b)).IsInvertible) :
    ∃ f : ℝ × M → ℝ, ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f ∧
      ∀ t ∈ T, ∀ b, f (t,e b) = 0 ∧
        HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) f (t,e b)
          ((symplecticNormalJet (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) (α t (e b))).comp
            (ContinuousLinearMap.snd ℝ ℝ E)) := by
  classical
  choose U g hU hcover hg hjet using exists_relative_jet_patch hΩ hα he hi
  have hcov : (T ×ˢ range e) ⊆ ⋃ a, U a := by
    rintro ⟨t,x⟩ ⟨ht,b,rfl⟩
    exact mem_iUnion.mpr ⟨b,hcover b t ht⟩
  obtain ⟨f,hf,hfjet⟩ := exists_smooth_zero_first_jet (I := (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E))
    (β := embeddedNormalJet (F := F) Ω α e) (hT.prod hclosed) hU hcov hg
    (by
      rintro a ⟨t,x⟩ ⟨ht,b,rfl⟩ hp
      exact (hjet a t ht b hp).1)
    (by
      rintro a ⟨t,x⟩ ⟨ht,b,rfl⟩ hp
      rw [embeddedNormalJet_apply Ω α he.isEmbedding.injective]
      exact (hjet a t ht b hp).2)
  refine ⟨f,hf,?_⟩
  intro t ht b
  have h := hfjet (t,e b) ⟨ht,mem_range_self b⟩
  rw [embeddedNormalJet_apply Ω α he.isEmbedding.injective] at h
  exact h


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartOneForm_corrected {α : ℝ → ManifoldOneForm E M} {f : ℝ × M → ℝ}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f)
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartOneForm (correctedOneForm α f p.1) c p.2 =
      chartOneForm (α p.1) c p.2 + spatialDifferential (manifoldPotentialChart f c) p := by
  rw [←chartOneForm_manifoldSpatialDifferential hf hp]
  exact ContinuousLinearMap.add_comp _ _ _

theorem ManifoldMoserData.corrected {Ω : ℝ → ManifoldTwoForm E M}
    {α : ℝ → ManifoldOneForm E M} (h : ManifoldMoserData Ω α) {f : ℝ × M → ℝ}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f) :
    ManifoldMoserData Ω (correctedOneForm α f) := by
  have he (c : M) (p : ℝ × E) (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
      (fun q : ℝ × E => chartOneForm (correctedOneForm α f q.1) c q.2) =ᶠ[𝓝 p]
        (fun q => chartOneForm (α q.1) c q.2 + spatialDifferential (manifoldPotentialChart f c) q) := by
    have ht := continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp)
    filter_upwards [ht] with q hq
    exact chartOneForm_corrected hf hq
  have hs (c : M) (p : ℝ × E) (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
      ContDiffAt ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) p :=
    (h.smooth_one c).contDiffAt ((isOpen_univ.prod
      (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds ⟨mem_univ _,hp⟩)
  refine ⟨h.smooth_two,?_,h.nondegenerate,h.skew,h.closed,?_⟩
  · intro c p hp
    exact (((hs c p hp.2).add (spatialDifferential_contDiffAt
      (manifoldPotentialChart_contDiffAt hf hp.2))).congr_of_eventuallyEq
        (he c p hp.2)).contDiffWithinAt
  · intro t ht c y hy v w
    have hd := (he c (t,y) hy).fderiv_eq (𝕜 := ℝ)
    rw [hd]
    have ha := fderiv_add ((hs c (t,y) hy).differentiableAt (by simp))
      ((spatialDifferential_contDiffAt (manifoldPotentialChart_contDiffAt hf hy)).differentiableAt
        (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    change fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2 +
      spatialDifferential (manifoldPotentialChart f c) q) (t,y) = _ at ha
    rw [ha]
    simp only [add_apply]
    have hz := spatialDifferential_closedAt (manifoldPotentialChart_contDiffAt hf (p := (t,y)) hy) v w
    have ho := h.exact_time t ht c y hy v w
    linarith


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifoldSpatialDifferential_of_jet {f : ℝ × M → ℝ} {t : ℝ} {x : M}
    {β : E →L[ℝ] ℝ}
    (hf : HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) f (t,x)
      (β.comp (ContinuousLinearMap.snd ℝ ℝ E))) :
    manifoldSpatialDifferential f t x = β := by
  have hc : HasMFDerivAt 𝓘(ℝ,E) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E))
      (fun z : M => (t,z)) x (ContinuousLinearMap.inr ℝ ℝ E) := by
    convert! (hasMFDerivAt_const (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,ℝ)) t x).prodMk
      (hasMFDerivAt_id (I := 𝓘(ℝ,E)) x) using 1
    all_goals try with_reducible_and_instances rfl
  have h := (hf.comp x hc).mfderiv
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (f ∘ fun z => (t,z)) x = β
  rw [h]
  ext v
  rfl

theorem ManifoldMoserData.skew_intrinsic {Ω : ℝ → ManifoldTwoForm E M}
    {α : ℝ → ManifoldOneForm E M} (h : ManifoldMoserData Ω α)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : M) (u v : E) :
    Ω t x u v = -Ω t x v u := by
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hs := h.skew t ht x _ (mem_extChartAt_target x)
    (chartDifferential x x u) (chartDifferential x x v)
  have h1 := chartTwoForm_apply_chart (Ω := Ω t) hx u v
  have h2 := chartTwoForm_apply_chart (Ω := Ω t) hx v u
  exact h1.symm.trans (hs.trans (congrArg (fun r : ℝ => -r) h2))



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_CircleAction_CircleRelativeOneForm
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

namespace SmoothCircleAction
variable (A : SmoothCircleAction E M) (B : SmoothCircleAction F N)

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem differential_intertwine {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    (heq : ∀ s b, e (B.slice s b) = A.slice s (e b)) (s : ℝ) (b : N) :
    (A.differential s (e b)).comp (manifoldMapDifferential (E := E) (F := F) e b) =
      (manifoldMapDifferential (E := E) (F := F) e (B.slice s b)).comp (B.differential s b) := by
  have heq' : A.slice s ∘ e = e ∘ B.slice s := funext (fun b => (heq s b).symm)
  have h₀ := (((A.slice_smooth s).mdifferentiable (by simp) (e b)).hasMFDerivAt.comp b
    (he.mdifferentiable (by simp) b).hasMFDerivAt).mfderiv
  have h₁ := ((he.mdifferentiable (by simp) (B.slice s b)).hasMFDerivAt.comp b
    ((B.slice_smooth s).mdifferentiable (by simp) b).hasMFDerivAt).mfderiv
  rw [heq'] at h₀
  exact h₀.symm.trans h₁

variable [FiniteDimensional ℝ E]

omit [IsManifold 𝓘(ℝ,F) ∞ N] [FiniteDimensional ℝ E] in
theorem averageOneForm_apply {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) (t : ℝ) (x : M) (v : E) :
    A.averageOneForm α t x v = ∫ s in (0:ℝ)..1,
      parameterPullbackOneForm (E := E) (F := E) α A.toFun s t x v := by
  exact ContinuousLinearMap.intervalIntegral_apply (μ := volume)
    ((A.pullbackOneForm_continuous hα t x).intervalIntegrable 0 1) v

omit [IsManifold 𝓘(ℝ,F) ∞ N] [FiniteDimensional ℝ E] in

theorem averageOneForm_normal_annihilation
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e)
    (heq : ∀ s b, e (B.slice s b) = A.slice s (e b))
    (hΩ : ∀ s t x u v, Ω t (A.slice s x) (A.differential s x u) (A.differential s x v) = Ω t x u v)
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) {t : ℝ}
    (hi : ∀ b, (manifoldPullbackTwoForm (F := F) Ω e t b).IsInvertible)
    (ha : ∀ b v, α t (e b) v = α t (e b)
      (manifoldMapDifferential (E := E) (F := F) e b
        (symplecticProjection (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) v)))
    (b : N) (v : E) :
    A.averageOneForm α t (e b) v = A.averageOneForm α t (e b)
      (manifoldMapDifferential (E := E) (F := F) e b
        (symplecticProjection (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) v)) := by
  rw [A.averageOneForm_apply hα,A.averageOneForm_apply hα]
  apply intervalIntegral.integral_congr
  intro s _
  have hL : ∀ u w, Ω t (e (B.slice s b)) (A.differential s (e b) u)
      (A.differential s (e b) w) = Ω t (e b) u w := by
    intro u w
    rw [heq]
    exact hΩ s t (e b) u w
  have hI : ∀ u, A.differential s (e b) (manifoldMapDifferential (E := E) (F := F) e b u) =
      manifoldMapDifferential (E := E) (F := F) e (B.slice s b) (B.differential s b u) :=
    fun u => congrArg (fun L : F →L[ℝ] E => L u) (A.differential_intertwine B he heq s b)
  have hh := normal_annihilation_pullback (hi b) (hi (B.slice s b))
    (B.differential_invertible s b).surjective hL hI (ha (B.slice s b)) v
  rw [heq] at hh
  exact hh

end SmoothCircleAction

end
section

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

namespace SmoothCircleAction

theorem generator_natural (A : SmoothCircleAction E M) (B : SmoothCircleAction F N)
    {f : M → N} (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f)
    (heq : ∀ s x, f (A.slice s x) = B.slice s (f x)) (x : M) :
    manifoldMapDifferential f x (A.generator x) = B.generator (f x) := by
  have hpath : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ∞ (fun s : ℝ => A.slice s x) :=
    A.smooth.comp (contMDiff_id.prodMk contMDiff_const)
  have he : (f ∘ fun s : ℝ => A.slice s x) = (fun s : ℝ => B.slice s (f x)) :=
    funext (fun s => heq s x)
  have hc : manifoldMapDifferential (f ∘ fun s : ℝ => A.slice s x) 0 =
      (manifoldMapDifferential f (A.slice 0 x)).comp
        (manifoldMapDifferential (fun s : ℝ => A.slice s x) 0) :=
    mfderiv_comp 0 (hf.mdifferentiable (by simp) _) (hpath.mdifferentiable (by simp) 0)
  have hz : A.slice 0 x = x := A.zero x
  rw [he,hz] at hc
  exact (congrArg (fun L : ℝ →L[ℝ] F => L 1) hc).symm
end SmoothCircleAction

end

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace SmoothCircleAction

 omit [FiniteDimensional ℝ E] in
 theorem vector_smooth (A : SmoothCircleAction E E) : ContDiff ℝ ∞ A.toFun := by
  have h := A.smooth
  rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h
  exact contMDiff_iff_contDiff.mp h

 theorem averageOneForm_spatialDifferential (A : SmoothCircleAction E E)
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    A.averageOneForm (manifoldSpatialDifferential (E := E) f) t x =
      fderiv ℝ (fun y => A.average f (t,y)) x := by
  have hg : ContDiff ℝ ∞ (fun p : ℝ × E => f (t,A.slice p.1 p.2)) :=
    hf.comp (contDiff_const.prodMk A.vector_smooth)
  have hd := (hasFDerivAt_fixed_integral hg x).fderiv
  change A.averageOneForm (manifoldSpatialDifferential (E := E) f) t x =
    fderiv ℝ (fun y => ∫ s in (0:ℝ)..1,f (t,A.slice s y)) x
  rw [hd]
  apply intervalIntegral.integral_congr
  intro s _
  have hs : ContDiff ℝ ∞ (A.slice s) := contMDiff_iff_contDiff.mp (A.slice_smooth s)
  have hft : ContDiff ℝ ∞ (fun y => f (t,y)) := hf.comp (contDiff_const.prodMk contDiff_id)
  change (manifoldSpatialDifferential f t (A.slice s x)).comp (A.differential s x) = _
  simp only [manifoldSpatialDifferential,differential,manifoldMapDifferential,mfderiv_eq_fderiv]
  exact (fderiv_comp x (hft.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)).symm

 theorem averaged_spatial_differential_generator_zero (A : SmoothCircleAction E E)
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    A.averageOneForm (manifoldSpatialDifferential (E := E) f) t x (A.generator x)=0 := by
  rw [A.averageOneForm_spatialDifferential hf]
  let G : E → ℝ := fun y => A.average f (t,y)
  have hG : ContDiff ℝ ∞ G := contDiff_fixed_integral
    (hf.comp (contDiff_const.prodMk A.vector_smooth))
  have hpath : ContDiff ℝ ∞ (fun s : ℝ => A.slice s x) :=
    A.vector_smooth.comp (contDiff_id.prodMk contDiff_const)
  have he : (G ∘ fun s : ℝ => A.slice s x)=(fun _ : ℝ => G x) :=
    funext fun s => A.average_invariant f t s x
  have hc := fderiv_comp (0:ℝ) (hG.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)
    (hpath.differentiable (by simp) 0)
  rw [he] at hc
  simp only [fderiv_const_apply] at hc
  have hz : A.slice 0 x=x := A.zero x
  rw [hz] at hc
  have hh := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) hc
  simpa only [generator,manifoldMapDifferential,mfderiv_eq_fderiv,
    ContinuousLinearMap.comp_apply,zero_apply] using hh.symm

 omit [FiniteDimensional ℝ E] in
 theorem differential_generator (A : SmoothCircleAction E E) (s : ℝ) (x : E) :
    A.differential s x (A.generator x)=A.generator (A.slice s x) := by
  apply A.generator_natural A (A.slice_smooth s)
  intro r y
  change A.toFun (s,A.toFun (r,y))=A.toFun (r,A.toFun (s,y))
  rw [←A.add,←A.add,add_comm]

 omit [FiniteDimensional ℝ E] in
 theorem averageOneForm_generator_zero (A : SmoothCircleAction E E)
    {α : ℝ → ManifoldOneForm E E} (hα : SmoothOneFormFamily α)
    (ha : ∀ t x,α t x (A.generator x)=0) (t : ℝ) (x : E) :
    A.averageOneForm α t x (A.generator x)=0 := by
  rw [A.averageOneForm_apply hα]
  have he : (fun s => parameterPullbackOneForm (E := E) (F := E) α A.toFun s t x (A.generator x))=
      (fun _ : ℝ => (0:ℝ)) := by
    funext s
    change α t (A.slice s x) (A.differential s x (A.generator x))=0
    rw [A.differential_generator,ha]
  rw [he]
  simp

 omit [FiniteDimensional ℝ E] in
 theorem averageOneForm_add (A : SmoothCircleAction E E)
    {α β : ℝ → ManifoldOneForm E E} (hα : SmoothOneFormFamily α) (hβ : SmoothOneFormFamily β)
    (t : ℝ) (x : E) : A.averageOneForm (fun t x => α t x+β t x) t x=
      A.averageOneForm α t x+A.averageOneForm β t x := by
  change (∫ s in (0:ℝ)..1,(α t (A.slice s x)+β t (A.slice s x)).comp (A.differential s x))=_
  simp only [ContinuousLinearMap.add_comp]
  exact intervalIntegral.integral_add
    ((A.pullbackOneForm_continuous hα t x).intervalIntegrable 0 1)
    ((A.pullbackOneForm_continuous hβ t x).intervalIntegrable 0 1)

 theorem averaged_corrected_generator_zero (A : SmoothCircleAction E E)
    {α : ℝ → ManifoldOneForm E E} (hα : SmoothOneFormFamily α)
    (ha : ∀ t x,α t x (A.generator x)=0)
    {f : ℝ × E → ℝ} (hf : ContDiff ℝ ∞ f) (t : ℝ) (x : E) :
    A.averageOneForm (correctedOneForm (E := E) α f) t x (A.generator x)=0 := by
  have hdf : SmoothOneFormFamily (manifoldSpatialDifferential (E := E) f) := by
    have hD : ContDiff ℝ ∞ (fun p : ℝ × E => manifoldSpatialDifferential (E := E) f p.1 p.2) := by
      have hh := (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp
        (contDiff_const (c := ContinuousLinearMap.inr ℝ ℝ E))
      convert! hh using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      simp only [manifoldSpatialDifferential,mfderiv_eq_fderiv]
      have hi : HasFDerivAt (fun y : E => (p.1,y)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
        convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1
        all_goals try with_reducible_and_instances rfl
      exact ((hf.differentiable (by simp) p).hasFDerivAt.comp p.2 hi).fderiv
    intro z
    simpa only [vector_chartOneForm] using hD.contDiffOn
  change A.averageOneForm (fun t x => α t x+manifoldSpatialDifferential (E := E) f t x) t x (A.generator x)=0
  rw [A.averageOneForm_add hα hdf]
  simp only [add_apply,A.averageOneForm_generator_zero hα ha,
    A.averaged_spatial_differential_generator_zero hf,add_zero]

end SmoothCircleAction

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldExteriorNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open MeasureTheory
section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem euclideanPullback_exact_time
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (h : ManifoldMoserData Ω α) {g : F → M} {p : ℝ × F}
    (hg : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ g p.2) (ht : p.1 ∈ Icc (0:ℝ) 1) (v w : F) :
    fderiv ℝ (euclideanPullbackTwoForm Ω g) p (1,0) v w =
      fderiv ℝ (euclideanPullbackOneForm α g) p (0,v) w -
      fderiv ℝ (euclideanPullbackOneForm α g) p (0,w) v := by
  let c := g p.2
  let g' := extChartAt 𝓘(ℝ,E) c ∘ g
  have hc : g p.2 ∈ (extChartAt 𝓘(ℝ,E) c).source := mem_extChartAt_source c
  have hch := (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞)
    (x := c) (by simpa only [extChartAt_source] using hc)).comp p.2 hg
  have hs : ContDiffAt ℝ ∞ g' p.2 := hch.contDiffAt
  have hp : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 (p.1,g' p.2) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,(extChartAt 𝓘(ℝ,E) c).map_source hc⟩
  have he := timePullback_exact_time ((h.smooth_two c).contDiffAt hp)
    ((h.smooth_one c).contDiffAt hp) hs
      (h.exact_time p.1 ht c (g' p.2) ((extChartAt 𝓘(ℝ,E) c).map_source hc)) v w
  have hg' := (contMDiffAt_iff_contMDiffAt_nhds (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≠ ∞)).mp
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞))
  have hc' := hg.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
  have heΩ : euclideanPullbackTwoForm Ω g =ᶠ[𝓝 p]
      timePullbackTwoForm (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) g' := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
      continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
    exact euclideanPullbackTwoForm_chart (p := q) (hq.mdifferentiableAt (by simp)) hqc
  have heα : euclideanPullbackOneForm α g =ᶠ[𝓝 p]
      timePullbackOneForm (fun q : ℝ × E => chartOneForm (α q.1) c q.2) g' := by
    filter_upwards [continuousAt_snd.preimage_mem_nhds hg',
      continuousAt_snd.preimage_mem_nhds hc'] with q hq hqc
    exact euclideanPullbackOneForm_chart (p := q) (hq.mdifferentiableAt (by simp)) hqc
  rw [heΩ.fderiv_eq,heα.fderiv_eq]
  exact he

variable {N : Type*} [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

theorem manifoldPullback_exact_time
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (h : ManifoldMoserData Ω α) {e : N → M}
    (he : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    {c : N} {y : F} (hy : y ∈ (extChartAt 𝓘(ℝ,F) c).target) (v w : F) :
    fderiv ℝ (fun q : ℝ × F => chartTwoForm (manifoldPullbackTwoForm Ω e q.1) c q.2)
      (t,y) (1,0) v w =
    fderiv ℝ (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) c q.2)
      (t,y) (0,v) w -
    fderiv ℝ (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) c q.2)
      (t,y) (0,w) v := by
  have hg := he.contMDiffAt.comp y ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,F)) (n := ∞) c).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy))
  have htarg : ∀ᶠ q : ℝ × F in 𝓝 (t,y), q.2 ∈ (extChartAt 𝓘(ℝ,F) c).target :=
    continuousAt_snd.preimage_mem_nhds
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,F)) c).mem_nhds hy)
  have hΩ : (fun q : ℝ × F => chartTwoForm (manifoldPullbackTwoForm Ω e q.1) c q.2) =ᶠ[𝓝 (t,y)]
      euclideanPullbackTwoForm Ω (e ∘ (extChartAt 𝓘(ℝ,F) c).symm) := by
    filter_upwards [htarg] with q hq
    exact chartTwoForm_manifoldPullback (p := q) he hq
  have hα : (fun q : ℝ × F => chartOneForm (manifoldPullbackOneForm α e q.1) c q.2) =ᶠ[𝓝 (t,y)]
      euclideanPullbackOneForm α (e ∘ (extChartAt 𝓘(ℝ,F) c).symm) := by
    filter_upwards [htarg] with q hq
    exact chartOneForm_manifoldPullback (p := q) he hq
  rw [hΩ.fderiv_eq,hα.fderiv_eq]
  exact euclideanPullback_exact_time h hg ht v w

end
section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

namespace SmoothCircleAction
variable (A : SmoothCircleAction E M)

theorem chart_averageOneForm_fderiv {α : ℝ → ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target)) {c : M} {p : ℝ × E}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) (v : ℝ × E) (w : E) :
    fderiv ℝ (fun q : ℝ × E => chartOneForm (A.averageOneForm α q.1) c q.2) p v w =
      ∫ s in (0:ℝ)..1, fderiv ℝ (fun q : ℝ × E =>
        chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) p v w := by
  have hf := parameterPullbackOneForm_smooth (E := E) (F := E) A.smooth hα c
  have hU := (isOpen_univ (X := ℝ)).prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)
  have he : (fun q : ℝ × E => chartOneForm (A.averageOneForm α q.1) c q.2) =
      (fun q => ∫ s in (0:ℝ)..1, chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) := by
    funext q
    exact A.chart_averageOneForm hα q.1 c q.2
  rw [he,(hasFDerivAt_fixed_integral_on hU hf ⟨mem_univ _,hp⟩).fderiv]
  have hD := continuous_at_fixed_fiber_derivative hU hf ⟨mem_univ _,hp⟩
  rw [ContinuousLinearMap.intervalIntegral_apply (hD.intervalIntegrable 0 1),
    ContinuousLinearMap.intervalIntegral_apply
      ((hD.clm_apply continuous_const).intervalIntegrable 0 1)]

theorem averaged_moser_data {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (h : ManifoldMoserData Ω α)
    (hΩ : ∀ s t x, (Ω t (A.slice s x)).bilinearComp (A.differential s x) (A.differential s x) = Ω t x) :
    ManifoldMoserData Ω (A.averageOneForm α) := by
  refine ⟨h.smooth_two,A.averageOneForm_smooth h.smooth_one,h.nondegenerate,h.skew,h.closed,?_⟩
  intro t ht c y hy v w
  have hpb (s : ℝ) : manifoldPullbackTwoForm (F := E) Ω (A.slice s) = Ω := by
    funext r x
    exact hΩ s r x
  have he (s : ℝ) := manifoldPullback_exact_time h (A.slice_smooth s) ht hy v w
  simp only [hpb] at he
  have hf := parameterPullbackOneForm_smooth (E := E) (F := E) A.smooth h.smooth_one c
  have hU := (isOpen_univ (X := ℝ)).prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)
  have hD := continuous_at_fixed_fiber_derivative hU hf (x := (t,y)) ⟨mem_univ _,hy⟩
  have hiv : IntervalIntegrable (fun s => fderiv ℝ (fun q : ℝ × E =>
      chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) (t,y) (0,v) w) volume 0 1 :=
    ((hD.clm_apply continuous_const).clm_apply continuous_const).intervalIntegrable 0 1
  have hiw : IntervalIntegrable (fun s => fderiv ℝ (fun q : ℝ × E =>
      chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) (t,y) (0,w) v) volume 0 1 :=
    ((hD.clm_apply continuous_const).clm_apply continuous_const).intervalIntegrable 0 1
  rw [A.chart_averageOneForm_fderiv h.smooth_one hy,A.chart_averageOneForm_fderiv h.smooth_one hy,
    ←intervalIntegral.integral_sub hiv hiw]
  have hh : (fun s =>
      fderiv ℝ (fun q : ℝ × E => chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (parameterPullbackOneForm (F := E) α A.toFun s q.1) c q.2) (t,y) (0,w) v) =
      (fun _ : ℝ => fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (1,0) v w) := by
    funext s
    exact (he s).symm
  rw [hh]
  simp

end SmoothCircleAction

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_CircleAction_CircleRelativeRadialMoser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped BigOperators
section

variable {ι : Type} [Fintype ι]
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

 theorem exists_circle_relative_radial_moser_bp240_oai
    {Ω : ℝ → ManifoldTwoForm (PlanePhase ι) (PlanePhase ι)}
    {α : ℝ → ManifoldOneForm (PlanePhase ι) (PlanePhase ι)}
    (h : ManifoldMoserData Ω α)
    (A : SmoothCircleAction (PlanePhase ι) (PlanePhase ι)) (B : SmoothCircleAction F F)
    {lam : ℝ} (hlam : lam≠0) (hgen : ∀ z,A.generator z=lam•phaseJ z)
    (e : F →L[ℝ] PlanePhase ι) (P : PlanePhase ι →L[ℝ] F)
    (hPe : P.comp e=ContinuousLinearMap.id ℝ F)
    (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,PlanePhase ι) ∞ e)
    (heq : ∀ s b,e (B.slice s b)=A.slice s (e b))
    (hΩ : ∀ s t z,(Ω t (A.slice s z)).bilinearComp (A.differential s z) (A.differential s z)=Ω t z)
    (hi : ∀ t∈Icc (0:ℝ) 1,∀ b,((Ω t (e b)).bilinearComp e e).IsInvertible)
    {K O : Set (PlanePhase ι)} (hK : IsCompact K) (hO : IsOpen O) (hKO : K⊆O)
    (hKr : ∀ x∈K,∀ y,phaseSq y=phaseSq x → y∈K)
    {c : ℝ} (hc : c≠0)
    (hcircle : ∀ s,∀ z∈O,∀ v,Ω s z v (phaseJ z)=c*phaseDot z v)
    (ha : ∀ s z,α s z (phaseJ z)=0) :
    ∃ Φ Ψ : ℝ × PlanePhase ι → PlanePhase ι,
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Ψ ∧
      (∀ x,Φ (0,x)=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x,phaseSq (Φ (t,x))=phaseSq x) ∧
      (∀ t∈Icc (0:ℝ) 1,(fun x => Φ (t,x)) '' range e=range e) ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈K,∀ v w,manifoldPullback Φ Ω t x v w=Ω 0 x v w) := by
  have hPe' (x : F) : P (e x)=x := congrArg (fun L : F →L[ℝ] F => L x) hPe
  have hclosed : IsClosed (range e) :=
    (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr (LeftInverse.injective hPe'))).isClosed_range
  have hI (b : F) : manifoldMapDifferential (E := PlanePhase ι) (F := F) e b=e := by
    simp only [manifoldMapDifferential,mfderiv_eq_fderiv,e.fderiv]
  obtain ⟨f,hf,hjet⟩ := exists_relative_global_potential h.smooth_two h.smooth_one he hclosed
    (isClosed_Icc (a := (0:ℝ)) (b := 1)) (by simpa only [hI] using hi)
  have hfs : ContDiff ℝ ∞ f := by
    rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hf
    exact contMDiff_iff_contDiff.mp hf
  let β := correctedOneForm (E := PlanePhase ι) α f
  have hβ : ManifoldMoserData Ω β := h.corrected (by
    rw [←modelWithCornersSelf_prod,chartedSpaceSelf_prod]
    exact hfs.contMDiff)
  have hγ : ManifoldMoserData Ω (A.averageOneForm β) := A.averaged_moser_data hβ hΩ
  have hαgen (t : ℝ) (z : PlanePhase ι) : α t z (A.generator z)=0 := by
    rw [hgen,map_smul,ha,smul_zero]
  have hγcircle (t : ℝ) (z : PlanePhase ι) : A.averageOneForm β t z (phaseJ z)=0 := by
    have hh := A.averaged_corrected_generator_zero h.smooth_one hαgen hfs t z
    change A.averageOneForm β t z (A.generator z)=0 at hh
    rw [hgen,map_smul,smul_eq_mul] at hh
    exact (mul_eq_zero.mp hh).resolve_left hlam
  have hβnormal (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (b : F) (v : PlanePhase ι) :
      β t (e b) v=β t (e b) (e (symplecticProjection (Ω t (e b)) e v)) := by
    have hd := manifoldSpatialDifferential_of_jet (hjet t ht b).2
    rw [hI] at hd
    simp only [β,correctedOneForm,hd,symplecticNormalJet,add_apply,sub_apply,
      ContinuousLinearMap.comp_apply,symplecticProjection_leftInverse (hi t ht b)]
    ring
  have hγnormal (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (b : F) (v : PlanePhase ι) :
      A.averageOneForm β t (e b) v=A.averageOneForm β t (e b)
        (e (symplecticProjection (Ω t (e b)) e v)) := by
    have hh := A.averageOneForm_normal_annihilation B he.contMDiff heq
      (fun s t z u v => congrArg (fun L : PlanePhase ι →L[ℝ] PlanePhase ι →L[ℝ] ℝ => L u v) (hΩ s t z))
      hβ.smooth_one (by simpa only [manifoldPullbackTwoForm,hI] using hi t ht)
      (by simpa only [hI] using hβnormal t ht) b v
    simpa only [hI] using hh
  apply exists_compact_radial_relative_moser_bp240 hγ hK hO hKO hKr hc hcircle
    (fun t z _ => hγcircle t z) e P hPe
  intro t ht b _
  have hh := moser_vector_tangent_of_annihilation (h.nondegenerate t ht (e b))
    (hi t ht b) (h.skew_intrinsic ht (e b)) (A.averageOneForm β t (e b)) (hγnormal t ht b)
  change e (P (-((Ω t (e b)).inverse (A.averageOneForm β t (e b))))) =
    -((Ω t (e b)).inverse (A.averageOneForm β t (e b)))
  rw [hh,hPe']

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

theorem solution : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser_bp240_oai := @OAI.PackingSufficiencySupport.Hamiltonian.exists_circle_relative_radial_moser_bp240_oai
