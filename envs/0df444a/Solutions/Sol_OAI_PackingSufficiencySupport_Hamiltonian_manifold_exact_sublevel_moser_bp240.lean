-- Prove2me | solution 1 for OAI.PackingSufficiencySupport.Hamiltonian.manifold_exact_sublevel_moser_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:18.586282+00:00
-- url     : https://prove2.me/submissions/0fbddda2-8ea6-48c0-8eb5-9d507cd47d28

import Mathlib
import Definitions.Def_OAIQ240Bp015

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_PlanarCovectorPrimitive
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem staticPullbackOneForm_fderiv {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) (u v : F) :
    fderiv ℝ (staticPullbackOneForm α g) x u v =
      fderiv ℝ α (g x) (fderiv ℝ g x u) (fderiv ℝ g x v) +
        α (g x) (fderiv ℝ (fderiv ℝ g) x u v) := by
  have hd := ((ha.differentiableAt (by simp)).hasFDerivAt.comp x
    (hg.differentiableAt (by simp)).hasFDerivAt).clm_comp
      ((hg.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  rw [show fderiv ℝ (staticPullbackOneForm α g) x = _ from hd.fderiv]
  simp only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply]
  exact add_comm _ _

theorem staticPullbackOneForm_exterior {α : E → E →L[ℝ] ℝ} {g : F → E} {x : F}
    (ha : ContDiffAt ℝ ∞ α (g x)) (hg : ContDiffAt ℝ ∞ g x) :
    euclideanExteriorOneForm (staticPullbackOneForm α g) x =
      (euclideanExteriorOneForm α (g x)).bilinearComp (fderiv ℝ g x) (fderiv ℝ g x) := by
  ext u v
  simp only [euclideanExteriorOneForm,sub_apply,ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.bilinearComp_apply,staticPullbackOneForm_fderiv ha hg]
  have hs := hg.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs.eq u v]
  ring


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

theorem timeChartField_hasDerivAt
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    {γ : ℝ → M} {t : ℝ} {c : M}
    (hγ : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,γ t))))
    (hc : γ t ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    HasDerivAt (fun s => extChartAt 𝓘(ℝ,E) c (γ s))
      (timeChartField V c (t,extChartAt 𝓘(ℝ,E) c (γ t))) t := by
  have hd := (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c) (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp t hγ
  rw [timeChartField,(extChartAt 𝓘(ℝ,E) c).left_inv hc]
  rw [hasDerivAt_iff_hasFDerivAt]
  apply (hasMFDerivAt_iff_hasFDerivAt.mp hd).congr_fderiv
  ext
  change (chartDifferential (E := E) c (γ t)) ((1 : ℝ) • (V (t,γ t) : E)) =
    (1 : ℝ) • ((chartDifferential (E := E) c (γ t)) (V (t,γ t)))
  simp only [one_smul]

theorem chart_spatial_pullback {f : M → M} {x c : M}
    (hf : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) f x)
    (hc : f x ∈ (extChartAt 𝓘(ℝ,E) c).source) (Ω : ManifoldTwoForm E M)
    (v w : TangentSpace 𝓘(ℝ,E) x) :
    chartTwoForm Ω c (extChartAt 𝓘(ℝ,E) c (f x))
      (fderiv ℝ (fun y => extChartAt 𝓘(ℝ,E) c (f ((extChartAt 𝓘(ℝ,E) x).symm y)))
        (extChartAt 𝓘(ℝ,E) x x) v)
      (fderiv ℝ (fun y => extChartAt 𝓘(ℝ,E) c (f ((extChartAt 𝓘(ℝ,E) x).symm y)))
        (extChartAt 𝓘(ℝ,E) x x) w) =
      Ω (f x) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x v) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x w) := by
  have hx := mem_extChartAt_source (I := 𝓘(ℝ,E)) x
  have hy := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hinv : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E)
      (extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x) := by
    simpa only [mfld_simps,mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hy
  have hid : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) x).symm
      (extChartAt 𝓘(ℝ,E) x x) = ContinuousLinearMap.id ℝ E := by
    simpa only [mfld_simps] using!
      (mfderivWithin_range_extChartAt_symm (I := 𝓘(ℝ,E)) (x := x))
  have hd := ((mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := c) (by simpa only [extChartAt_source] using hc)).hasMFDerivAt.comp x hf.hasMFDerivAt)
  have hd1 : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c ∘ f)
      ((extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x))
      ((chartDifferential (E := E) c (f x)).comp (preferredDifferential (E := E) f x)) := by
    rw [(extChartAt 𝓘(ℝ,E) x).left_inv hx]
    exact hd
  have hd' := hd1.comp (extChartAt 𝓘(ℝ,E) x x) hinv.hasMFDerivAt
  have he : fderiv ℝ (fun y => extChartAt 𝓘(ℝ,E) c (f ((extChartAt 𝓘(ℝ,E) x).symm y)))
      (extChartAt 𝓘(ℝ,E) x x) =
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c) (f x)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x) := by
    let A : E →L[ℝ] E :=
      ((chartDifferential (E := E) c (f x)).comp (preferredDifferential (E := E) f x)).comp
        (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) x).symm (extChartAt 𝓘(ℝ,E) x x))
    have hh : HasFDerivAt
        (fun y : E => extChartAt 𝓘(ℝ,E) c (f ((extChartAt 𝓘(ℝ,E) x).symm y)))
        A (extChartAt 𝓘(ℝ,E) x x) := hasMFDerivAt_iff_hasFDerivAt.mp hd'
    dsimp only [A] at hh
    have hh1 := hh.fderiv
    rw [hid] at hh1
    change _ = (chartDifferential (E := E) c (f x)).comp
      (preferredDifferential (E := E) f x)
    convert! hh1 using 1
    all_goals try with_reducible_and_instances rfl
  rw [he]
  exact chartTwoForm_apply_chart hc _ _



theorem timeChartField_contDiffOn
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) (c : M) :
    ContDiffOn ℝ ∞ (timeChartField V c) (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
  have h := (contMDiff_iff.mp hV).2 (0,c) (⟨c,V (0,c)⟩ : TangentBundle 𝓘(ℝ,E) M)
  have hh := h.snd
  have hs : ContDiffOn ℝ ∞
      (fun p : ℝ × E => let z := (extChartAt 𝓘(ℝ,E) c).symm p.2
        tangentCoordChange 𝓘(ℝ,E) z c z (V (p.1,z)))
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) := by
    apply hh.mono
    intro p hp
    refine ⟨?_,?_⟩
    · simp only [mfld_simps]
      change p ∈ univ ×ˢ (chartAt E c).target
      simpa only [mfld_simps] using hp
    · simp only [Set.mem_preimage,mfld_simps,TangentBundle.mem_chart_source_iff]
      change (chartAt E c).symm p.2 ∈ (chartAt E c).source
      simpa only [mfld_simps] using (extChartAt 𝓘(ℝ,E) c).map_target hp.2

  apply hs.congr
  intro p hp
  dsimp only [timeChartField,chartDifferential]
  have hz := (extChartAt 𝓘(ℝ,E) c).map_target hp.2
  have hz' : (extChartAt 𝓘(ℝ,E) c).symm p.2 ∈ (chartAt E c).source := by
    simpa only [extChartAt_source] using hz
  rw [show (extChartAt 𝓘(ℝ,E) c : M → E) = chartAt E c from rfl,
    mfderiv_chartAt_eq_tangentCoordChange hz']

theorem manifoldFamily_coordinate_smoothAt
    {Φ : ℝ × M → M}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    {x c : M} {p : ℝ × E}
    (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) x).target)
    (hc : Φ (p.1,(extChartAt 𝓘(ℝ,E) x).symm p.2) ∈
      (extChartAt 𝓘(ℝ,E) c).source) :
    ContDiffAt ℝ ∞ (fun q : ℝ × E => extChartAt 𝓘(ℝ,E) c
      (Φ (q.1,(extChartAt 𝓘(ℝ,E) x).symm q.2))) p := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hp)
  have hc' : Φ (p.1,(extChartAt 𝓘(ℝ,E) x).symm p.2) ∈ (chartAt E c).source := by
    simpa only [extChartAt_source] using hc
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) hc'
  have hm : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞
      (fun q : ℝ × E => extChartAt 𝓘(ℝ,E) c
        (Φ (q.1,(extChartAt 𝓘(ℝ,E) x).symm q.2))) p :=
    ho.comp p (hΦ.contMDiffAt.comp p
      (contDiffAt_fst.contMDiffAt.prodMk (hi.comp p contDiffAt_snd.contMDiffAt)))
  exact hm.contDiffAt



theorem timeField_smooth_of_coordinates
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ∀ p : ℝ × M, ContDiffAt ℝ ∞ (timeChartField V p.2)
      (p.1,extChartAt 𝓘(ℝ,E) p.2 p.2)) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)) := by
  intro p
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_snd,?_⟩
  have hc : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ × E) ∞
      (fun q : ℝ × M => (q.1,extChartAt 𝓘(ℝ,E) p.2 q.2)) p :=
    contMDiffAt_fst.prodMk_space (contMDiffAt_extChartAt.comp p contMDiffAt_snd)
  have hh := (hV p).contMDiffAt.comp p hc
  apply hh.congr_of_eventuallyEq
  have hn : ∀ᶠ q : ℝ × M in 𝓝 p, q.2 ∈ (extChartAt 𝓘(ℝ,E) p.2).source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds p.2)
  filter_upwards [hn] with q hq
  dsimp only [Function.comp_apply,timeChartField]
  rw [(extChartAt 𝓘(ℝ,E) p.2).left_inv hq]
  have hq' : q.2 ∈ (chartAt E p.2).source := by simpa only [extChartAt_source] using hq
  have he := (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p.2).continuousLinearMapAt_apply_of_mem
    (R := ℝ) (show q.2 ∈ (trivializationAt E (TangentSpace 𝓘(ℝ,E)) p.2).baseSet by
      simpa only [TangentBundle.trivializationAt_baseSet] using hq') (V q)
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hq'] at he
  exact he.symm



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moser_ManifoldMoserField
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
open scoped NNReal
open MeasureTheory
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartTwoForm_isInvertible {Ω : ManifoldTwoForm E M} {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : (Ω ((extChartAt 𝓘(ℝ,E) c).symm y)).IsInvertible) :
    (chartTwoForm Ω c y).IsInvertible := by
  apply bilinearComp_isInvertible hΩ
  apply ContinuousLinearMap.IsInvertible.inverse
  convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
    ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1
  all_goals try with_reducible_and_instances rfl

theorem chart_moser_contraction
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : (Ω p.1 ((extChartAt 𝓘(ℝ,E) c).symm p.2)).IsInvertible) :
    chartTwoForm (Ω p.1) c p.2 (timeChartField (manifoldMoserField Ω α) c p) =
      -chartOneForm (α p.1) c p.2 := by
  let z := (extChartAt 𝓘(ℝ,E) c).symm p.2
  have hC : (chartDifferential (E := E) c z).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E))
      ((extChartAt 𝓘(ℝ,E) c).map_target hp) using 1
    all_goals try with_reducible_and_instances rfl
  ext w
  change Ω p.1 z ((chartDifferential c z).inverse
      (chartDifferential c z (manifoldMoserField Ω α (p.1,z))))
      ((chartDifferential c z).inverse w) =
    -(α p.1 z ((chartDifferential c z).inverse w))
  erw [hC.inverse_apply_self]
  change Ω p.1 z (-((Ω p.1 z).inverse (α p.1 z))) _ = _
  rw [map_neg,hΩ.self_apply_inverse]
  rfl

theorem timeChartField_moser_eq
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : (Ω p.1 ((extChartAt 𝓘(ℝ,E) c).symm p.2)).IsInvertible) :
    timeChartField (manifoldMoserField Ω α) c p =
      -(chartTwoForm (Ω p.1) c p.2).inverse (chartOneForm (α p.1) c p.2) := by
  have hi := chartTwoForm_isInvertible hp hΩ
  apply hi.injective
  rw [chart_moser_contraction hp hΩ,map_neg,hi.self_apply_inverse]

variable [CompleteSpace E]

theorem timeChartField_moser_contDiffAt
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (hΩ : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) p)
    (hα : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) p)
    (hinv : ∀ᶠ q : ℝ × E in 𝓝 p,
      (Ω q.1 ((extChartAt 𝓘(ℝ,E) c).symm q.2)).IsInvertible) :
    ContDiffAt ℝ ∞ (timeChartField (manifoldMoserField Ω α) c) p := by
  have hi := chartTwoForm_isInvertible hp hinv.self_of_nhds
  have hs := ((hi.contDiffAt_map_inverse.comp p hΩ).clm_apply hα).neg
  apply hs.congr_of_eventuallyEq
  have ht : ∀ᶠ q : ℝ × E in 𝓝 p, q.2 ∈ (extChartAt 𝓘(ℝ,E) c).target :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp)
  filter_upwards [hinv,ht] with q hq hqt
  exact timeChartField_moser_eq hqt hq

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_SpatialOneForm
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartDifferential_inverse {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).inverse =
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) c).symm y := by
  apply ContinuousLinearMap.inverse_eq
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := 𝓘(ℝ,E)) hy)
  · simpa only [mfld_simps,chartDifferential] using!
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := 𝓘(ℝ,E)) hy)


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

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


end

open scoped ContDiff Manifold Topology
open MeasureTheory Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ChartSupportedDensity
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
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
variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem SmoothOneFormFamily.spatial_smooth {α : P → ManifoldOneForm E M}
    (hα : SmoothOneFormFamily α) (p : P) (c : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    ContDiffAt ℝ ∞ (chartOneForm (α p) c) y :=
  ((hα c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds ⟨mem_univ p,hy⟩)).comp y
    (contDiffAt_const.prodMk contDiffAt_id)


end


open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Residues_AreaPolarChart
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology ENNReal
open Set Function MeasureTheory
open Filter
open scoped Manifold

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) : ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨L,hL,hKL,hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,E) hK.isClosed hKL (n := ⊤)
  have hs : tsupport (χ : E → ℝ) ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    exact hx (hχ0 x hn)
  exact ⟨χ,χ.contMDiff.contDiff,hL.of_isClosed_subset (isClosed_tsupport _) hs,
    hs.trans hLU,hχ1,hχrange⟩

theorem exists_smooth_compact_extension {K U : Set E} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ x, χ x ∈ Icc 0 1) ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧
      ContDiff ℝ ∞ (fun x => χ x • f x) ∧
      HasCompactSupport (fun x => χ x • f x) ∧
      (∀ᶠ x in 𝓝ˢ K, χ x • f x = f x) := by
  obtain ⟨χ,hχ,hχc,hχU,hχ1,hχrange⟩ := exists_smooth_cutoff hK hU hKU
  have hg : ContDiff ℝ ∞ (fun x => χ x • f x) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hχ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have hn : x ∉ tsupport χ := fun h => hx (hχU h)
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hn)
      apply (contDiffAt_const (c := (0:F))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp only [hy,zero_smul,Pi.zero_apply]
  have hs : tsupport (fun x => χ x • f x) ⊆ tsupport χ := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hn
    apply hx
    change χ x • f x = 0
    rw [image_eq_zero_of_notMem_tsupport hn,zero_smul]
  refine ⟨χ,hχ,hχc,hχU,hχrange,hχ1,hg,
    hχc.of_isClosed_subset (isClosed_tsupport _) hs,?_⟩
  filter_upwards [hχ1] with x hx
  rw [hx,one_smul]

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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartOneForm_transition {α : ManifoldOneForm E M} {b c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source) :
    chartOneForm α b y =
      staticPullbackOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y := by
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have he := euclideanPullbackOneForm_chart (α := fun _ => α) (p := (0,y)) hi hc
  simpa only [euclideanPullbackOneForm,chartOneForm,chartDifferential_inverse hy,
    staticPullbackOneForm,Function.comp_apply] using he

theorem chartOneForm_exterior_transition {α : ManifoldOneForm E M} {b c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target)
    (hc : (extChartAt 𝓘(ℝ,E) b).symm y ∈ (extChartAt 𝓘(ℝ,E) c).source)
    (hα : ContDiffAt ℝ ∞ (chartOneForm α c)
      (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))) :
    euclideanExteriorOneForm (chartOneForm α b) y =
      (euclideanExteriorOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ((extChartAt 𝓘(ℝ,E) b).symm y))).bilinearComp
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y)
        (fderiv ℝ (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y) := by
  have hi := (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)
  have ho := contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (n := ∞) (x := c)
    (by simpa only [extChartAt_source] using hc)
  have ht : ContDiffAt ℝ ∞
      (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) y :=
    (ho.comp y hi).contDiffAt
  have he : chartOneForm α b =ᶠ[𝓝 y]
      staticPullbackOneForm (chartOneForm α c)
        (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm) := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy,
      hi.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)]
      with z hz hzc
    exact chartOneForm_transition hz hzc
  calc
    _ = euclideanExteriorOneForm
        (staticPullbackOneForm (chartOneForm α c)
          (extChartAt 𝓘(ℝ,E) c ∘ (extChartAt 𝓘(ℝ,E) b).symm)) y := by
      unfold euclideanExteriorOneForm
      rw [he.fderiv_eq]
    _ = _ := staticPullbackOneForm_exterior hα ht

theorem manifoldExteriorOneForm_chart {α : ManifoldOneForm E M}
    (hα : ∀ c, ContDiffOn ℝ ∞ (chartOneForm α c) (extChartAt 𝓘(ℝ,E) c).target)
    {b : M} {y : E} (hy : y ∈ (extChartAt 𝓘(ℝ,E) b).target) :
    chartTwoForm (manifoldExteriorOneForm α) b y =
      euclideanExteriorOneForm (chartOneForm α b) y := by
  let x := (extChartAt 𝓘(ℝ,E) b).symm y
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hi := ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) b).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b).mem_nhds hy)).mdifferentiableAt (by simp)
  have ho := mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) (x := x)
    (by simpa only [extChartAt_source] using hx)
  let A : E →L[ℝ] E := (chartDifferential x x).comp
    (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (extChartAt 𝓘(ℝ,E) b).symm y)
  have hf : HasFDerivAt (extChartAt 𝓘(ℝ,E) x ∘ (extChartAt 𝓘(ℝ,E) b).symm) A y :=
    hasMFDerivAt_iff_hasFDerivAt.mp (ho.hasMFDerivAt.comp y hi.hasMFDerivAt)
  have he := hf.fderiv
  dsimp only [A,chartDifferential] at he
  rw [chartOneForm_exterior_transition hy hx ((hα x).contDiffAt
    ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds
      ((extChartAt 𝓘(ℝ,E) x).map_source hx)))]
  change fderiv ℝ (extChartAt 𝓘(ℝ,E) x ∘ (extChartAt 𝓘(ℝ,E) b).symm) y = _ at he
  rw [he]
  simp only [chartTwoForm,manifoldExteriorOneForm,chartDifferential_inverse hy]
  rfl

end

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_HorizontalCoupling
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_evaluation_const {P F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : P → F →L[ℝ] G} {p : P} (hg : DifferentiableAt ℝ g p) (u : P) (v : F) :
    fderiv ℝ (fun q => g q v) p u = fderiv ℝ g p u v := by
  rw [(hg.hasFDerivAt.clm_apply (hasFDerivAt_const v p)).fderiv]
  simp

theorem pathSpatialExterior_fderivAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (u : ℝ × E) (v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p u v w =
      fderiv ℝ (fderiv ℝ Γ) p u (0,v) w - fderiv ℝ (fderiv ℝ Γ) p u (0,w) v := by
  have hD := (hΓ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hΩ := (pathSpatialExterior_smoothAt hΓ).differentiableAt (by simp)
  rw [←fderiv_evaluation_const hΩ u v,
    ←fderiv_evaluation_const (hΩ.clm_apply (differentiableAt_const v)) u w]
  simp only [pathSpatialExterior_apply]
  change fderiv ℝ ((fun q => fderiv ℝ Γ q (0,v) w)-(fun q => fderiv ℝ Γ q (0,w) v)) p u = _
  rw [fderiv_sub (hD.clm_apply (differentiableAt_const (0,v)) |>.clm_apply (differentiableAt_const w))
    (hD.clm_apply (differentiableAt_const (0,w)) |>.clm_apply (differentiableAt_const v))]
  simp only [sub_apply,fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (0,v))),
    fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (0,w))),fderiv_evaluation_const hD]

theorem pathTimePrimitive_fderivAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (u : ℝ × E) (v : E) :
    fderiv ℝ (pathTimePrimitive Γ) p u v = fderiv ℝ (fderiv ℝ Γ) p u (1,0) v := by
  have hD := (hΓ.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [←fderiv_evaluation_const ((pathTimePrimitive_smoothAt hΓ).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  simp only [pathTimePrimitive,fderiv_evaluation_const (hD.clm_apply (differentiableAt_const (1,0))),
    fderiv_evaluation_const hD]

theorem exact_path_time_equationAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p (1,0) v w =
      fderiv ℝ (pathTimePrimitive Γ) p (0,v) w -
        fderiv ℝ (pathTimePrimitive Γ) p (0,w) v := by
  have hs := hΓ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [pathSpatialExterior_fderivAt hΓ,pathTimePrimitive_fderivAt hΓ]
  rw [hs.eq (1,0) (0,v),hs.eq (1,0) (0,w)]

theorem exact_path_closedAt {Γ : ℝ × E → E →L[ℝ] ℝ}
    {p : ℝ × E} (hΓ : ContDiffAt ℝ ∞ Γ p) (u v w : E) :
    fderiv ℝ (pathSpatialExterior Γ) p (0,u) v w -
      fderiv ℝ (pathSpatialExterior Γ) p (0,v) u w +
      fderiv ℝ (pathSpatialExterior Γ) p (0,w) u v = 0 := by
  have hs := hΓ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [pathSpatialExterior_fderivAt hΓ]
  rw [hs.eq (0,u) (0,v),hs.eq (0,u) (0,w),hs.eq (0,v) (0,w)]
  ring


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartOneForm_reconstruct_target {α : ManifoldOneForm E M} {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    (chartOneForm α c y).comp (chartDifferential c ((extChartAt 𝓘(ℝ,E) c).symm y)) =
      α ((extChartAt 𝓘(ℝ,E) c).symm y) := by
  have hC : (chartDifferential (E := E) c ((extChartAt 𝓘(ℝ,E) c).symm y)).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1
    all_goals try with_reducible_and_instances rfl
  ext v
  exact congrArg (α ((extChartAt 𝓘(ℝ,E) c).symm y)) (hC.inverse_apply_self v)

theorem manifoldTimePrimitive_chart {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {c : M} {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartOneForm (manifoldTimePrimitive Γ t) c y =
      pathTimePrimitive (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) (t,y) := by
  let F : ℝ × E → E →L[ℝ] ℝ := fun q => chartOneForm (Γ q.1) c q.2
  let x := (extChartAt 𝓘(ℝ,E) c).symm y
  have hF : ContDiffAt ℝ ∞ F (t,y) := (hΓ c).contDiffAt ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds
    (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ t,hy⟩))
  have hdf : HasFDerivAt F (fderiv ℝ F (t,y)) (t,y) :=
    (hF.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hinc : HasDerivAt (fun s : ℝ => (s,y)) (1,0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have hd : HasDerivAt (fun s => F (s,y)) (pathTimePrimitive F (t,y)) t := by
    have hh := hdf.comp_hasDerivAt t hinc
    simpa only [Function.comp_def,pathTimePrimitive] using hh
  have he : (fun s => (F (s,y)).comp (chartDifferential c x)) = fun s => Γ s x := by
    funext s
    exact chartOneForm_reconstruct_target hy
  have hdn := hd.clm_comp (hasDerivAt_const t (chartDifferential c x))
  rw [he] at hdn
  have hC : (chartDifferential (E := E) c x).IsInvertible := by
    convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,E)) ((extChartAt 𝓘(ℝ,E) c).map_target hy) using 1
    all_goals try with_reducible_and_instances rfl
  have hdne : deriv (fun s => Γ s x) t = (pathTimePrimitive F (t,y)).comp (chartDifferential c x) := by
    simpa only [ContinuousLinearMap.comp_zero,add_zero] using hdn.deriv
  unfold chartOneForm manifoldTimePrimitive
  change (deriv (fun s => Γ s x) t).comp (chartDifferential c x).inverse = _
  rw [hdne]
  apply ContinuousLinearMap.ext
  intro v
  change pathTimePrimitive F (t,y) ((chartDifferential c x) ((chartDifferential c x).inverse v)) =
    pathTimePrimitive F (t,y) v
  exact congrArg (pathTimePrimitive F (t,y)) (hC.self_apply_inverse v)

theorem pathSpatialExterior_eq_slice {Γ : ℝ × E → E →L[ℝ] ℝ} {p : ℝ × E}
    (hΓ : DifferentiableAt ℝ Γ p) :
    pathSpatialExterior Γ p = euclideanExteriorOneForm (fun y => Γ (p.1,y)) p.2 := by
  have hi : HasFDerivAt (fun y : E => (p.1,y))
      ((0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hh : HasFDerivAt Γ (fderiv ℝ Γ p) (p.1,p.2) := hΓ.hasFDerivAt
  have hd := (hh.comp p.2 hi).fderiv
  change fderiv ℝ (fun y => Γ (p.1,y)) p.2 = _ at hd
  unfold euclideanExteriorOneForm
  rw [hd]
  rfl

theorem manifoldExteriorOneForm_path_chart {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {c : M} {t : ℝ} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartTwoForm (manifoldExteriorOneForm (Γ t)) c y =
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) (t,y) := by
  rw [manifoldExteriorOneForm_chart (fun b z hz => (hΓ.spatial_smooth t b hz).contDiffWithinAt) hy]
  exact (pathSpatialExterior_eq_slice ((hΓ c).contDiffAt
    ((isOpen_univ.prod (isOpen_extChartAt_target c)).mem_nhds (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ t,hy⟩))
      |>.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))).symm

theorem manifoldExteriorOneForm_path_smooth {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothTwoFormFamily (fun t => manifoldExteriorOneForm (Γ t)) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((pathSpatialExterior_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  exact manifoldExteriorOneForm_path_chart hΓ hq.2

theorem manifoldTimePrimitive_smooth {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) : SmoothOneFormFamily (manifoldTimePrimitive Γ) := by
  intro c p hp
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds hp
  apply ((pathTimePrimitive_smoothAt ((hΓ c).contDiffAt hn)).congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with q hq
  exact manifoldTimePrimitive_chart hΓ hq.2


end

open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Forms_ManifoldExteriorAlgebra
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_manifold_cutoff {K U : Set M}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : M → ℝ, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ (∀ x, χ x ∈ Icc (0:ℝ) 1) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  obtain ⟨D,hD,hKD,hDU⟩ := exists_compact_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχ⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (n := (⊤ : ℕ∞)) 𝓘(ℝ,E) hK.isClosed hKD
  have hs : tsupport (χ : M → ℝ) ⊆ D :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hχ0 x hn)) hD.isClosed
  exact ⟨χ,χ.contMDiff,HasCompactSupport.of_support_subset_isCompact hD
    ((subset_tsupport χ).trans hs),hs.trans hDU,hχ1,hχ⟩


end


open scoped ContDiff Manifold Topology
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Toric_RestrictedMassIndependence
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceFirstPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData.globalSurfaceSecondPrimitive_zero _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifoldExteriorOneForm_path_closed {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (c : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) (u v w : E) :
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (0,u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (0,v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (0,w) u v=0 := by
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
    (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ _,hy⟩)
  have he : (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) =ᶠ[𝓝 (t,y)]
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) := by
    filter_upwards [hn] with q hq
    exact manifoldExteriorOneForm_path_chart hΓ hq.2
  rw [he.fderiv_eq]
  exact exact_path_closedAt ((hΓ c).contDiffAt hn) u v w

theorem manifoldExteriorOneForm_path_time {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (c : M) (y : E)
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target) (v w : E) :
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) (t,y) (1,0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (manifoldTimePrimitive Γ q.1) c q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (manifoldTimePrimitive Γ q.1) c q.2) (t,y) (0,w) v := by
  have hn := (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
    (show (t,y) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target from ⟨mem_univ _,hy⟩)
  have he : (fun q : ℝ × E => chartTwoForm (manifoldExteriorOneForm (Γ q.1)) c q.2) =ᶠ[𝓝 (t,y)]
      pathSpatialExterior (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) := by
    filter_upwards [hn] with q hq
    exact manifoldExteriorOneForm_path_chart hΓ hq.2
  have ha : (fun q : ℝ × E => chartOneForm (manifoldTimePrimitive Γ q.1) c q.2) =ᶠ[𝓝 (t,y)]
      pathTimePrimitive (fun q : ℝ × E => chartOneForm (Γ q.1) c q.2) := by
    filter_upwards [hn] with q hq
    exact manifoldTimePrimitive_chart hΓ hq.2
  rw [he.fderiv_eq,ha.fderiv_eq]
  exact exact_path_time_equationAt ((hΓ c).contDiffAt hn) v w

theorem SmoothOneFormFamily.time_contDiffAt {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) (t : ℝ) (x : M) : ContDiffAt ℝ ∞ (fun s => Γ s x) t := by
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hxt := (extChartAt 𝓘(ℝ,E) x).map_source hx
  have hcam := ((hΓ x).contDiffAt ((isOpen_univ.prod
    (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x)).mem_nhds
      (show (t,extChartAt 𝓘(ℝ,E) x x) ∈ univ ×ˢ (extChartAt 𝓘(ℝ,E) x).target from ⟨mem_univ t,hxt⟩))).comp t (contDiffAt_id.prodMk contDiffAt_const)
  have hsm := hcam.clm_comp (contDiffAt_const (c := chartDifferential x x))
  apply hsm.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => by
    simpa only [(extChartAt 𝓘(ℝ,E) x).left_inv hx,Function.comp_def,id_eq] using (chartOneForm_reconstruct_target
      (α := Γ s) hxt).symm)

theorem manifoldTimePrimitive_eval_constant {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {x : M} {Z : E}
    (hz : ∀ t, Γ t x Z=Γ 0 x Z) (t : ℝ) : manifoldTimePrimitive Γ t x Z=0 := by
  have hd := (((hΓ.time_contDiffAt t x).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasDerivAt).clm_apply
    (hasDerivAt_const t Z)
  have he : (fun s => Γ s x Z) = fun _ : ℝ => Γ 0 x Z := funext hz
  change HasDerivAt (fun s => Γ s x Z) _ t at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const t (Γ 0 x Z))
  simpa only [manifoldTimePrimitive,ContinuousLinearMap.map_zero,add_zero] using hh

omit [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifoldTimePrimitive_stationary {Γ : ℝ → ManifoldOneForm E M}
    {x : M} (hz : ∀ t, Γ t x=Γ 0 x) (t : ℝ) : manifoldTimePrimitive Γ t x=0 := by
  unfold manifoldTimePrimitive
  rw [show (fun s => Γ s x)=fun _ : ℝ => Γ 0 x from funext hz]
  exact deriv_const t (Γ 0 x)

omit [IsManifold 𝓘(ℝ,E) ∞ M] in
theorem manifoldExteriorOneForm_skew (α : ManifoldOneForm E M) (x : M) (v w : E) :
    manifoldExteriorOneForm α x v w = -manifoldExteriorOneForm α x w v := by
  change fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x v) (chartDifferential x x w) -
    fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x w) (chartDifferential x x v) = -_
  change _ = -(fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x w) (chartDifferential x x v) -
    fderiv ℝ (chartOneForm α x) (extChartAt 𝓘(ℝ,E) x x)
      (chartDifferential x x v) (chartDifferential x x w))
  ring

end PackingSufficiencySupport.Hamiltonian

end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_AnnularPathGerms
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_joint_localized_manifold_moser_field
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {K U : Set (ℝ × M)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible) :
    ∃ V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
        (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)) ∧
      (∀ᶠ p in 𝓝ˢ K, V p = manifoldMoserField Ω α p) ∧
      (∀ p, α p.1 p.2=0 → V p=0) ∧
      (∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → V (t,x)=0) ∧
      (∀ p (L : E →L[ℝ] ℝ), (p ∈ U → L (manifoldMoserField Ω α p)=0) → L (V p)=0) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : NormalSpace (ℝ × M) := inferInstance
  have hprod : IsManifold ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ (ℝ × M) := inferInstance
  let instProd : ChartedSpace (ℝ × E) (ℝ × M) := prodChartedSpace ℝ ℝ E M
  have : IsManifold 𝓘(ℝ,ℝ × E) ∞ (ℝ × M) := by
    simpa only [modelWithCornersSelf_prod,instProd] using hprod
  obtain ⟨χ,hχ,hχc,hχU,hχ1,_⟩ := exists_smooth_manifold_cutoff (E := ℝ × E) hK hU hKU
  have hχs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ χ := by
    simpa only [modelWithCornersSelf_prod,instProd] using hχ
  let V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2 := fun p => χ p • manifoldMoserField Ω α p
  have he (c : M) (q : ℝ × E) : timeChartField V c q =
      χ (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2) • timeChartField (manifoldMoserField Ω α) c q := by
    dsimp only [timeChartField,V]
    exact (chartDifferential c _).map_smul _ _
  refine ⟨V,?_,?_,?_,?_,?_⟩
  · apply timeField_smooth_of_coordinates
    intro p
    let c := p.2
    let q : ℝ × E := (p.1,extChartAt 𝓘(ℝ,E) c c)
    let F : ℝ × E → ℝ × M := fun z => (z.1,(extChartAt 𝓘(ℝ,E) c).symm z.2)
    have hq : q.2 ∈ (extChartAt 𝓘(ℝ,E) c).target := mem_extChartAt_target c
    have hFe : F q=p := by dsimp only [F,q,c]; rw [extChartAt_to_inv]
    have hi : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extChartAt 𝓘(ℝ,E) c).symm q.2 :=
      (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) c).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hq)
    have hF : ContMDiffAt 𝓘(ℝ,ℝ × E) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ F q :=
      contDiffAt_fst.contMDiffAt.prodMk (hi.comp q contDiffAt_snd.contMDiffAt)
    have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 q :=
      (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds ⟨mem_univ _,hq⟩
    by_cases hp : p ∈ U
    · have hnU : ∀ᶠ z in 𝓝 q, F z ∈ U := hF.continuousAt.preimage_mem_nhds
        (by rw [hFe]; exact hU.mem_nhds hp)
      have hs := timeChartField_moser_contDiffAt hq ((hΩ c).contDiffAt hn)
        ((hα c).contDiffAt hn) (hnU.mono fun z hz => hinv (F z) hz)
      have hc : ContDiffAt ℝ ∞ (fun z => χ (F z)) q :=
        (hχs.contMDiffAt.comp q hF).contDiffAt
      exact (hc.smul hs).congr_of_eventuallyEq (Filter.Eventually.of_forall (he c))
    · have hp' : p ∉ tsupport χ := fun h => hp (hχU h)
      have hz : ∀ᶠ z in 𝓝 q, χ (F z)=0 := by
        have hh : F ⁻¹' (tsupport χ)ᶜ ∈ 𝓝 q := hF.continuousAt.preimage_mem_nhds
          (show (tsupport χ)ᶜ ∈ 𝓝 (F q) by
            rw [hFe]; exact (isClosed_tsupport χ).isOpen_compl.mem_nhds hp')
        filter_upwards [hh] with z hz
        exact image_eq_zero_of_notMem_tsupport hz
      apply (contDiffAt_const (c := (0:E))).congr_of_eventuallyEq
      filter_upwards [hz] with z hz
      rw [he,hz,zero_smul]
  · filter_upwards [hχ1] with p hp
    change χ p • _ = _
    rw [hp,one_smul]
  · intro p hp
    change χ p • (-((Ω p.1 p.2).inverse (α p.1 p.2)))=0
    rw [hp,map_zero,neg_zero,smul_zero]
  · refine ⟨Prod.snd '' tsupport χ,hχc.image continuous_snd,?_⟩
    intro t x hx
    have hz : χ (t,x)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx ⟨(t,x),h,rfl⟩)
    change χ (t,x) • _ = 0
    rw [hz,zero_smul]
  · intro p L hL
    change L (χ p • manifoldMoserField Ω α p)=0
    erw [map_smul]
    by_cases hp : p ∈ U
    · rw [hL hp,smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hp (hχU h)),zero_smul]

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem local_contraction_derivative
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} {X : ℝ × E → E} {p : ℝ × E}
    (hΩ : DifferentiableAt ℝ Ω p) (hα : DifferentiableAt ℝ α p)
    (hX : DifferentiableAt ℝ X p)
    (hcon : (fun q => Ω q (X q)) =ᶠ[𝓝 p] (fun q => -α q))
    (q : ℝ × E) (w : E) :
    fderiv ℝ Ω p q (X p) w + Ω p (fderiv ℝ X p q) w = -(fderiv ℝ α p q w) := by
  have hl := hΩ.hasFDerivAt.clm_apply hX.hasFDerivAt
  have hr := hα.hasFDerivAt.neg.congr_of_eventuallyEq hcon
  have he := congrArg (fun A : (ℝ × E) →L[ℝ] E →L[ℝ] ℝ => A q w) (hl.unique hr)
  simpa only [add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    neg_apply,add_comm] using he

theorem local_moser_transport_equation
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    {α : ℝ × E → E →L[ℝ] ℝ} {X : ℝ × E → E} {p : ℝ × E}
    (hΩ : DifferentiableAt ℝ Ω p) (hα : DifferentiableAt ℝ α p)
    (hX : DifferentiableAt ℝ X p)
    (hcon : (fun q => Ω q (X q)) =ᶠ[𝓝 p] (fun q => -α q))
    (hskew : ∀ u v, Ω p u v = -Ω p v u)
    (hclosed : ∀ u v w, fderiv ℝ Ω p (0,u) v w - fderiv ℝ Ω p (0,v) u w +
      fderiv ℝ Ω p (0,w) u v = 0)
    (htime : ∀ v w, fderiv ℝ Ω p (1,0) v w =
      fderiv ℝ α p (0,v) w - fderiv ℝ α p (0,w) v) (v w : E) :
    fderiv ℝ Ω p (1,X p) v w +
      Ω p (fderiv ℝ X p (0,v)) w + Ω p v (fderiv ℝ X p (0,w)) = 0 := by
  have h1 := local_contraction_derivative hΩ hα hX hcon (0,v) w
  have h2 := local_contraction_derivative hΩ hα hX hcon (0,w) v
  have hc := hclosed (X p) v w
  have ht := htime v w
  rw [show (1,X p) = ((1,0) : ℝ × E)+(0,X p) by ext <;> simp,
    map_add,add_apply,add_apply,hskew v]
  linarith

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem joint_manifold_moser_PDE
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {U : Set (ℝ × M)} (hU : IsOpen U) {t : ℝ} {c : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ,E) c).target)
    (ht : (t,(extChartAt 𝓘(ℝ,E) c).symm y) ∈ U)
    (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible)
    (heq : ∀ᶠ p in 𝓝 (t,(extChartAt 𝓘(ℝ,E) c).symm y),
      V p = manifoldMoserField Ω α p)
    (hΩ : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y))
    (hα : ContDiffAt ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y))
    (hskew : ∀ u v, chartTwoForm (Ω t) c y u v = -chartTwoForm (Ω t) c y v u)
    (hclosed : ∀ u v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (0,w) u v = 0)
    (htime : ∀ v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y) (1,0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) (t,y) (0,w) v)
    (v w : E) :
    fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y)
        (1,timeChartField V c (t,y)) v w +
      chartTwoForm (Ω t) c y (fderiv ℝ (timeChartField V c) (t,y) (0,v)) w +
      chartTwoForm (Ω t) c y v (fderiv ℝ (timeChartField V c) (t,y) (0,w)) = 0 := by
  have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target) ∈ 𝓝 (t,y) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds
      ⟨mem_univ _,hy⟩
  have hX := ((timeChartField_contDiffOn hV c).contDiffAt hn).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  apply local_moser_transport_equation (hΩ.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (hα.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hX _ hskew hclosed htime
  let F : ℝ × E → ℝ × M := fun q => (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2)
  have hCs : ContinuousAt (fun z : E => (extChartAt 𝓘(ℝ,E) c).symm z) y :=
    continuousAt_extChartAt_symm'' (I := 𝓘(ℝ,E)) hy
  have hS : ContinuousAt (fun q : ℝ × E => (extChartAt 𝓘(ℝ,E) c).symm q.2) (t,y) :=
    ContinuousAt.comp (f := fun q : ℝ × E => q.2)
      (g := fun z : E => (extChartAt 𝓘(ℝ,E) c).symm z) (x := (t,y)) hCs continuousAt_snd
  have hF : ContinuousAt F (t,y) := continuousAt_fst.prodMk hS
  have hspaceU : ∀ᶠ q in 𝓝 (t,y), F q ∈ U :=
    hF.preimage_mem_nhds (hU.mem_nhds ht)
  have hVe : ∀ᶠ q in 𝓝 (t,y), V (F q)=manifoldMoserField Ω α (F q) :=
    hF.preimage_mem_nhds heq
  have htarg : ∀ᶠ q : ℝ × E in 𝓝 (t,y), q.2 ∈ (extChartAt 𝓘(ℝ,E) c).target :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hy)
  filter_upwards [hspaceU,htarg,hVe] with q hq hqt hqe
  have hVC : timeChartField V c q = timeChartField (manifoldMoserField Ω α) c q := by
    dsimp only [timeChartField]
    rw [show V (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2)=
      manifoldMoserField Ω α (q.1,(extChartAt 𝓘(ℝ,E) c).symm q.2) from hqe]
  rw [hVC]
  exact chart_moser_contraction hqt (hinv (F q) hq)

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smoothAt_fderiv_apply_const {D G : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : D → G}
    {p : D} (hf : ContDiffAt ℝ ∞ f p) (v w : D) :
    fderiv ℝ (fun q => fderiv ℝ f q v) p w = fderiv ℝ (fderiv ℝ f) p w v := by
  have hfd : ContDiffAt ℝ ∞ (fderiv ℝ f) p := hf.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hh := (hfd.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.clm_apply
    (hasFDerivAt_const v p)
  rw [hh.fderiv]
  simp

theorem local_spatial_fderiv {F : ℝ × E → E} {p : ℝ × E}
    (hF : DifferentiableAt ℝ F p) (v : E) :
    fderiv ℝ (fun y => F (p.1,y)) p.2 v = fderiv ℝ F p (0,v) := by
  have hd := hF.hasFDerivAt.comp p.2
    ((hasFDerivAt_const (c := p.1) p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
  exact congrArg (fun A : E →L[ℝ] E => A v) hd.fderiv

theorem local_time_fderiv {F X : ℝ × E → E} {p : ℝ × E}
    (hF : DifferentiableAt ℝ F p)
    (hflow : HasDerivAt (fun s => F (s,p.2)) (X (p.1,F p)) p.1) :
    fderiv ℝ F p (1,0) = X (p.1,F p) := by
  have hd := hF.hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  exact hd.unique hflow

theorem local_flow_variation {F X : ℝ × E → E} {p : ℝ × E}
    (hF : ContDiffAt ℝ ∞ F p) (hX : DifferentiableAt ℝ X (p.1,F p))
    (hflow : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => F (s,q.2)) (X (q.1,F q)) q.1)
    (v : E) :
    HasDerivAt (fun s => fderiv ℝ F (s,p.2) (0,v))
      (fderiv ℝ X (p.1,F p) (0,fderiv ℝ F p (0,v))) p.1 := by
  have hFd : ContDiffAt ℝ ∞ (fderiv ℝ F) p := hF.fderiv_right (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hV : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (0,v)) p :=
    hFd.clm_apply contDiffAt_const
  have hd := (hV.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt.comp_hasDerivAt p.1
    ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  have he : (fun q => fderiv ℝ F q (1,0)) =ᶠ[𝓝 p] (fun q => X (q.1,F q)) := by
    have hF1 : ContDiffAt ℝ 1 F p := hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    filter_upwards [hF1.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),hflow] with q hq hqf
    exact local_time_fderiv (hq.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hqf
  have hchain := hX.hasFDerivAt.comp p
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
      (hF.differentiableAt (by simp)).hasFDerivAt)
  have hc := congrArg (fun A : (ℝ × E) →L[ℝ] E => A (0,v)) hchain.fderiv
  have he' := congrArg (fun A : (ℝ × E) →L[ℝ] E => A (0,v)) he.fderiv_eq
  change fderiv ℝ (fun q => X (q.1,F q)) p (0,v) = _ at hc
  rw [smoothAt_fderiv_apply_const hF,hc] at he'
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply] at he'
  have hs := hF.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  apply hd.congr_deriv
  rw [smoothAt_fderiv_apply_const hF,hs.eq (1,0) (0,v)]
  exact he'

theorem local_flow_form_derivative {F X : ℝ × E → E} {p : ℝ × E}
    (hF : ContDiffAt ℝ ∞ F p) (hX : DifferentiableAt ℝ X (p.1,F p))
    (hflow : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => F (s,q.2)) (X (q.1,F q)) q.1)
    {Ω : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} (hΩ : DifferentiableAt ℝ Ω (p.1,F p))
    (hPDE : ∀ u z, fderiv ℝ Ω (p.1,F p) (1,X (p.1,F p)) u z +
      Ω (p.1,F p) (fderiv ℝ X (p.1,F p) (0,u)) z +
      Ω (p.1,F p) u (fderiv ℝ X (p.1,F p) (0,z)) = 0) (v w : E) :
    HasDerivAt (fun s => Ω (s,F (s,p.2))
      (fderiv ℝ (fun y => F (s,y)) p.2 v) (fderiv ℝ (fun y => F (s,y)) p.2 w)) 0 p.1 := by
  have hpos : HasDerivAt (fun s => (s,F (s,p.2))) (1,X (p.1,F p)) p.1 := by
    simpa only [id_eq,Prod.eta] using
      (hasDerivAt_id p.1).prodMk hflow.self_of_nhds
  have hdΩ := HasFDerivAt.comp_hasDerivAt_of_eq (𝕜 := ℝ)
    (E := E →L[ℝ] E →L[ℝ] ℝ) (F := ℝ × E) (l := Ω)
    p.1 hΩ.hasFDerivAt hpos (by simp only [Prod.eta])
  have hd := (hdΩ.clm_apply (local_flow_variation hF hX hflow v)).clm_apply
    (local_flow_variation hF hX hflow w)
  have hz : HasDerivAt (fun s => Ω (s,F (s,p.2))
      (fderiv ℝ F (s,p.2) (0,v)) (fderiv ℝ F (s,p.2) (0,w))) 0 p.1 := by
    apply hd.congr_deriv
    simpa only [add_apply,Function.comp_apply,id_eq] using hPDE
      (fderiv ℝ F p (0,v)) (fderiv ℝ F p (0,w))
  apply hz.congr_of_eventuallyEq
  have hF1 : ContDiffAt ℝ 1 F p := hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hev := (hF1.eventually (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).filter_mono
    (continuousAt_id.prodMk continuousAt_const).tendsto
  filter_upwards [hev] with s hs
  change ContDiffAt ℝ 1 F (s,p.2) at hs
  rw [local_spatial_fderiv (hs.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),
    local_spatial_fderiv (hs.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_ManifoldFormTransport
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]



theorem local_manifold_form_transport_derivative
    {Φ : ℝ × M → M} {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {U : Set ℝ} (hU : IsOpen U)
    (hflow : ∀ x s, s ∈ U → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun r => Φ (r,x)) s ((1 : ℝ →L[ℝ] ℝ).smulRight (V (s,Φ (s,x)))))
    {Ω : ℝ → ManifoldTwoForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {t : ℝ} (ht : t ∈ U)
    (x : M)
    (hPDE : ∀ c y, y ∈ (extChartAt 𝓘(ℝ,E) c).target →
      (extChartAt 𝓘(ℝ,E) c).symm y=Φ (t,x) → ∀ u w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2) (t,y)
        (1,timeChartField V c (t,y)) u w +
      chartTwoForm (Ω t) c y (fderiv ℝ (timeChartField V c) (t,y) (0,u)) w +
      chartTwoForm (Ω t) c y u (fderiv ℝ (timeChartField V c) (t,y) (0,w)) = 0)
    (v w : E) :
    HasDerivAt (fun s => manifoldPullback Φ Ω s x v w) 0 t := by
  let a := extChartAt 𝓘(ℝ,E) x
  let c := Φ (t,x)
  let b := extChartAt 𝓘(ℝ,E) c
  let p : ℝ × E := (t,a x)
  let H : ℝ × E → M := fun q => Φ (q.1,a.symm q.2)
  let F : ℝ × E → E := b ∘ H
  have hx : x ∈ a.source := mem_extChartAt_source x
  have hy : a x ∈ a.target := a.map_source hx
  have hcx : Φ (t,x) ∈ b.source := mem_extChartAt_source c
  have hH : H p = Φ (t,x) := by dsimp [H,p]; rw [a.left_inv hx]
  have hc : H p ∈ b.source := hH ▸ hcx
  have hi : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ a.symm (a x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) (n := ∞) x).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x).mem_nhds hy)
  have hHs : ContMDiffAt 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞ H p :=
    hΦ.contMDiffAt.comp p (contDiffAt_fst.contMDiffAt.prodMk (hi.comp p contDiffAt_snd.contMDiffAt))
  have hFc : ContDiffAt ℝ ∞ F p := manifoldFamily_coordinate_smoothAt hΦ hy hc
  have hbc : F p ∈ b.target := b.map_source hc
  have hn : (univ ×ˢ b.target) ∈ 𝓝 (t,F p) :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds ⟨mem_univ _,hbc⟩
  have hX := ((timeChartField_contDiffOn hV c).contDiffAt hn).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hO := ((hΩ c).contDiffAt hn).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hflowc : ∀ᶠ q in 𝓝 p, HasDerivAt (fun s => F (s,q.2))
      (timeChartField V c (q.1,F q)) q.1 := by
    have hneigh := hHs.continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hc)
    have htime : ∀ᶠ q in 𝓝 p, q.1 ∈ U :=
      continuousAt_fst.preimage_mem_nhds (hU.mem_nhds ht)
    filter_upwards [hneigh,htime] with q hq hqt
    exact timeChartField_hasDerivAt (hflow (a.symm q.2) q.1 hqt) hq
  have hd := local_flow_form_derivative hFc hX hflowc hO (hPDE c (F p) hbc ((b.left_inv hc).trans hH)) v w
  apply hd.congr_of_eventuallyEq
  have hΦt : ContinuousAt (fun s => Φ (s,x)) t :=
    hΦ.continuous.continuousAt.comp (continuousAt_id.prodMk continuousAt_const)
  filter_upwards [hΦt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓘(ℝ,E)) c).mem_nhds hcx)] with s hs
  have hfs : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (s,y)) x :=
    (hΦ.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp) x
  have he := chart_spatial_pullback hfs hs (Ω s) v w
  dsimp only [F,H,p,Function.comp_apply]
  rw [a.left_inv hx]
  exact he.symm


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem manifoldMoserField_moment_tangent
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    {p : ℝ × M} (hinv : (Ω p.1 p.2).IsInvertible)
    (hskew : ∀ u v, Ω p.1 p.2 u v = -Ω p.1 p.2 v u)
    (L : E →L[ℝ] ℝ) (Z : E) (hface : Ω p.1 p.2 Z = -L)
    (hhor : α p.1 p.2 Z=0) : L (manifoldMoserField Ω α p)=0 := by
  let v : E := manifoldMoserField Ω α p
  change L v = 0
  have hs : Ω p.1 p.2 v = -α p.1 p.2 := by
    simp only [v,manifoldMoserField,map_neg,hinv.self_apply_inverse]
  have hh := congrArg (fun A : E →L[ℝ] ℝ => A Z) hs
  have hz := congrArg (fun A : E →L[ℝ] ℝ => A v) hface
  simp only [neg_apply,hhor,neg_zero] at hh
  simp only [neg_apply] at hz
  rw [hskew] at hh
  linarith


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem chartField_smoothOn {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (x : M) : ContDiffOn ℝ ∞ (chartField v x) (extChartAt 𝓘(ℝ,E) x).target := by
  have h := (contMDiff_iff.mp hv).2 x (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)
  have hh := h.snd
  change ContDiffOn ℝ ∞ (chartField v x) _ at hh
  apply hh.mono
  intro y hy
  refine ⟨hy,?_⟩
  simp only [Set.mem_preimage, extChartAt_source, TangentBundle.mem_chart_source_iff]
  simpa only [extChartAt_source] using (extChartAt 𝓘(ℝ,E) x).map_target hy

theorem chartCurve_hasMFDerivAt {v : (z : M) → TangentSpace 𝓘(ℝ,E) z}
    (x : M) {f : ℝ → E} {t : ℝ}
    (hf : f t ∈ (extChartAt 𝓘(ℝ,E) x).target)
    (hd : HasDerivAt f (chartField v x (f t)) t) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) ((extChartAt 𝓘(ℝ,E) x).symm ∘ f) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v ((extChartAt 𝓘(ℝ,E) x).symm (f t)))) := by
  change M → E at v
  let z : M := (extChartAt 𝓘(ℝ,E) x).symm (f t)
  have hz : z ∈ (extChartAt 𝓘(ℝ,E) x).source := (extChartAt 𝓘(ℝ,E) x).map_target hf
  have hz' := mem_extChartAt_source (I := 𝓘(ℝ,E)) z
  have hd' : HasDerivAt f (tangentCoordChange 𝓘(ℝ,E) z x z (v z)) t := hd
  refine ⟨(continuousAt_extChartAt_symm'' hf).comp hd.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt (𝕜 := ℝ) (F := E) ?_⟩
  simp only [mfld_simps,hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt 𝓘(ℝ,E) z ∘ (extChartAt 𝓘(ℝ,E) x).symm) ∘ f) (v z) t
  rw [←tangentCoordChange_self (I := 𝓘(ℝ,E)) (x := z) (z := z) (v := v z) hz',
    ←tangentCoordChange_comp (x := x) ⟨⟨hz',hz⟩,hz'⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ hd'
  apply HasFDerivWithinAt.hasFDerivAt (s := range 𝓘(ℝ,E)) _ (by simp)
  rw [←(extChartAt 𝓘(ℝ,E) x).right_inv hf]
  exact hasFDerivWithinAt_tangentCoordChange ⟨hz,hz'⟩


end

section
open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_global_bounded_trajectory {X : E → E} {L : ℝ≥0}
    (hL : LipschitzWith L X) {B : ℝ≥0} (hB : ∀ x, ‖X x‖ ≤ B) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (X (γ t)) t := by
  have hex (a : ℝ≥0) : ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Icc (-(a:ℝ)) a, HasDerivWithinAt γ (X (γ t)) (Icc (-(a:ℝ)) a) t := by
    let t₀ : Icc (-(a:ℝ)) a := ⟨0, neg_nonpos.mpr a.coe_nonneg, a.coe_nonneg⟩
    have hp : IsPicardLindelof (fun _ : ℝ => X) t₀ x (B*a) 0 B L := {
      lipschitzOnWith := fun _ _ => hL.lipschitzOnWith
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ y _ => hB y
      mul_max_le := by simp [t₀] }
    exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  choose u hu0 hud using hex
  have heq {a b : ℝ≥0} (hab : a ≤ b) : EqOn (u a) (u b) (Ioo (-(a:ℝ)) a) := by
    by_cases ha : a = 0
    · simp [ha]
    · have ha' : (0:ℝ) < a := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha)
      apply ODE_solution_unique_of_mem_Ioo
        (s := fun _ => univ) (fun _ _ => hL.lipschitzOnWith)
        (t₀ := 0) ⟨by linarith,ha'⟩
        (fun t ht => ⟨(hud a t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2),mem_univ _⟩)
      · intro t ht
        have ht' : t ∈ Ioo (-(b:ℝ)) b := by
          have hab' : (a:ℝ) ≤ b := hab
          constructor <;> linarith [ht.1,ht.2]
        exact ⟨(hud b t (Ioo_subset_Icc_self ht')).hasDerivAt
          (Icc_mem_nhds ht'.1 ht'.2),mem_univ _⟩
      · rw [hu0 a,hu0 b]
  let γ : ℝ → E := fun t => u (‖t‖₊+1) t
  have hmatch {a : ℝ≥0} : EqOn γ (u a) (Ioo (-(a:ℝ)) a) := by
    intro t ht
    have ht' : t ∈ Ioo (-((‖t‖₊+1:ℝ≥0):ℝ)) (‖t‖₊+1:ℝ≥0) := by
      simp only [NNReal.coe_add,NNReal.coe_one,coe_nnnorm,Real.norm_eq_abs]
      exact abs_lt.mp (lt_add_one |t|)
    rcases le_total (‖t‖₊+1) a with h | h
    · exact heq h ht'
    · exact (heq h ht).symm
  refine ⟨γ,?_,?_⟩
  · change u (‖(0:ℝ)‖₊+1) 0 = x
    exact hu0 _
  · intro t
    let a : ℝ≥0 := ‖t‖₊+1
    have ht : t ∈ Ioo (-(a:ℝ)) a := by
      simpa only [a,NNReal.coe_add,NNReal.coe_one,coe_nnnorm,Real.norm_eq_abs,mem_Ioo]
        using abs_lt.mp (lt_add_one |t|)
    have he : γ =ᶠ[𝓝 t] u a := Filter.eventually_of_mem
      (isOpen_Ioo.mem_nhds ht) (fun s hs => hmatch hs)
    have hd := (hud a t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    rw [he.eq_of_nhds]
    exact hd.congr_of_eventuallyEq he


end

section
open scoped ContDiff Topology NNReal
open Set Function
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem stepEndpoint_eq_trajectory {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    {h : ℝ} (hh : ‖h‖*L < 1) {γ : ℝ → E} (hγ : ∀ t, HasDerivAt γ (X (γ t)) t) :
    stepEndpoint X hX h (γ 0) = γ h := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  let u : C(Time,E) := ⟨fun s => γ (h*(s:ℝ)),
    hγc.comp (continuous_const.mul continuous_subtype_val)⟩
  have hu0 : u ⟨0,by simp⟩ = γ 0 := by simp [u]
  have hud (s : ℝ) (hs : s ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (extendPath u) (h • X (extendPath u s)) s := by
    have he : extendPath u =ᶠ[𝓝 s] (fun t => γ (h*t)) := by
      filter_upwards [Icc_mem_nhds hs.1 hs.2] with t ht
      exact extendPath_coe u ⟨t,ht⟩
    have hd := (hγ (h*s)).scomp s (hasDerivAt_const_mul h)
    rw [he.eq_of_nhds]
    exact hd.congr_of_eventuallyEq he
  have he := fixedStep_eq_solution X hX hh u (γ 0) hu0 hud
  have he' := congrArg (fun v : C(Time,E) => v ⟨1,by simp⟩) he
  simpa only [stepEndpoint,u,ContinuousMap.coe_mk,mul_one] using he'

theorem shortFlow_zero {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X) (x : E) :
    shortFlow X hX (0,x) = x := by
  have he := fixedStep_equation X hX (h := 0) (by simp) x
  simp only [zero_smul,add_zero] at he
  change fixedStep X hX 0 x ⟨1,by simp⟩ = x
  rw [he]
  rfl

variable [FiniteDimensional ℝ E]

theorem shortFlow_smoothOn {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) :
    ContDiffOn ℝ ∞ (shortFlow X hX) {p : ℝ × E | ‖p.1‖*(L:ℝ) < 1} := by
  have hc := (localPath_smooth X hX hXs).comp
    (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun p hp => hp)
  exact (ContinuousMap.evalCLM (M := E) ℝ (⟨1,by simp⟩ : Time)).contDiff.comp_contDiffOn hc

omit [FiniteDimensional ℝ E] in

theorem shortFlow_derivative {L : ℝ≥0} (X : C(E,E)) (hX : LipschitzWith L X)
    (hXc : HasCompactSupport X) {t : ℝ} (ht : ‖t‖*(L:ℝ) < 1) (x : E) :
    HasDerivAt (fun s => shortFlow X hX (s,x)) (X (shortFlow X hX (t,x))) t := by
  obtain ⟨B,hB⟩ := X.continuous.bounded_above_of_compact_support hXc
  have hB0 : 0 ≤ B := (norm_nonneg (X x)).trans (hB x)
  obtain ⟨γ,hγ0,hγd⟩ := exists_global_bounded_trajectory hX (B := ⟨B,hB0⟩) hB x
  have hopen : IsOpen {s : ℝ | ‖s‖*(L:ℝ) < 1} :=
    isOpen_lt (continuous_id.norm.mul continuous_const) continuous_const
  have he : (fun s => shortFlow X hX (s,x)) =ᶠ[𝓝 t] γ := by
    filter_upwards [hopen.mem_nhds ht] with s hs
    change stepEndpoint X hX s x = γ s
    rw [←hγ0]
    exact stepEndpoint_eq_trajectory X hX hs hγd
  rw [he.eq_of_nhds]
  exact (hγd t).congr_of_eventuallyEq he


end

section
open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_local_manifold_flow
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (x : M) : ∃ (ε : ℝ) (U : Set E) (Φ : ℝ × E → M),
      0 < ε ∧ IsOpen U ∧ extChartAt 𝓘(ℝ,E) x x ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ,E) x).target ∧
      ContMDiffOn 𝓘(ℝ,ℝ × E) 𝓘(ℝ,E) ∞ Φ (Ioo (-ε) ε ×ˢ U) ∧
      (∀ y ∈ U, Φ (0,y) = (extChartAt 𝓘(ℝ,E) x).symm y) ∧
      (∀ y ∈ U, IsMIntegralCurveOn (fun t => Φ (t,y)) v (Ioo (-ε) ε)) := by
  let c := extChartAt 𝓘(ℝ,E) x x
  have hc : c ∈ (extChartAt 𝓘(ℝ,E) x).target := mem_extChartAt_target x
  have hT := isOpen_extChartAt_target (I := 𝓘(ℝ,E)) x
  obtain ⟨χ,_,_,_,_,_,hXs,hXc,hEq⟩ := exists_smooth_compact_extension
    (isCompact_singleton (x := c)) hT (singleton_subset_iff.mpr hc) (chartField_smoothOn hv x)
  let X : C(E,E) := ⟨fun y => χ y • chartField v x y,hXs.continuous⟩
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq : ∀ᶠ y in 𝓝 c, X y = chartField v x y := by
    simpa only [nhdsSet_singleton,X,ContinuousMap.coe_mk] using hEq
  have hnb : {y | X y = chartField v x y ∧ y ∈ (extChartAt 𝓘(ℝ,E) x).target} ∈ 𝓝 c :=
    heq.and (hT.mem_nhds hc)
  obtain ⟨V,hVsub,hVo,hcV⟩ := mem_nhds_iff.mp hnb
  let D : Set (ℝ × E) := {p | ‖p.1‖*(L:ℝ) < 1}
  have hDo : IsOpen D := isOpen_lt (continuous_fst.norm.mul continuous_const) continuous_const
  have hcD : ((0,c) : ℝ × E) ∈ D := by simp [D]
  have hflowc : ContinuousAt (shortFlow X hL) (0,c) :=
    ((shortFlow_smoothOn X hL hXs).contDiffAt (hDo.mem_nhds hcD)).continuousAt
  have hpV : (shortFlow X hL) ⁻¹' V ∈ 𝓝 ((0,c) : ℝ × E) := by
    apply hflowc.preimage_mem_nhds
    rw [shortFlow_zero]
    exact hVo.mem_nhds hcV
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem (hDo.mem_nhds hcD) hpV)
  let U : Set E := Metric.ball c δ
  have hroom {t : ℝ} (ht : t ∈ Ioo (-δ) δ) {y : E} (hy : y ∈ U) :
      (t,y) ∈ D ∧ shortFlow X hL (t,y) ∈ V := by
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by simpa only [dist_zero_right,Real.norm_eq_abs] using (abs_lt.mpr ht),hy⟩
  have hUtarget : U ⊆ (extChartAt 𝓘(ℝ,E) x).target := by
    intro y hy
    have hm := (hroom (t := 0) ⟨by linarith,hδ⟩ hy).2
    rw [shortFlow_zero] at hm
    exact (hVsub hm).2
  let Φ : ℝ × E → M := (extChartAt 𝓘(ℝ,E) x).symm ∘ shortFlow X hL
  refine ⟨δ,U,Φ,hδ,Metric.isOpen_ball,Metric.mem_ball_self hδ,hUtarget,?_,?_,?_⟩
  · apply (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ,E)) x).comp
      ((shortFlow_smoothOn X hL hXs).mono (fun p hp => (hroom hp.1 hp.2).1)).contMDiffOn
    intro p hp
    exact (hVsub (hroom hp.1 hp.2).2).2
  · intro y _
    change (extChartAt 𝓘(ℝ,E) x).symm (shortFlow X hL (0,y)) = _
    rw [shortFlow_zero]
  · intro y hy t ht
    have hm := hroom ht hy
    have hd := shortFlow_derivative X hL hXc hm.1 y
    rw [(hVsub hm.2).1] at hd
    exact (chartCurve_hasMFDerivAt x (hVsub hm.2).2 hd).hasMFDerivWithinAt

theorem exists_smooth_local_manifold_family
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    (x : M) : ∃ (ε : ℝ) (W : Set M) (Ψ : ℝ × M → M),
      0 < ε ∧ IsOpen W ∧ x ∈ W ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ (Ioo (-ε) ε ×ˢ W) ∧
      (∀ y ∈ W, Ψ (0,y) = y) ∧
      (∀ y ∈ W, IsMIntegralCurveOn (fun t => Ψ (t,y)) v (Ioo (-ε) ε)) := by
  obtain ⟨ε,U,Φ,hε,hU,hxU,_,hΦ,hΦ0,hΦd⟩ := exists_smooth_local_manifold_flow hv x
  let e := extChartAt 𝓘(ℝ,E) x
  let W : Set M := e.source ∩ e ⁻¹' U
  have hW : IsOpen W := (continuousOn_extChartAt x).isOpen_inter_preimage
    (isOpen_extChartAt_source x) hU
  have hxW : x ∈ W := ⟨mem_extChartAt_source x,hxU⟩
  let Ψ : ℝ × M → M := fun p => Φ (p.1,e p.2)
  refine ⟨ε,W,Ψ,hε,hW,hxW,?_,?_,?_⟩
  · have hc : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : ℝ × M => e p.2) (Ioo (-ε) ε ×ˢ W) :=
      (contMDiffOn_extChartAt (I := 𝓘(ℝ,E)) (x := x)).comp contMDiff_snd.contMDiffOn
        (fun p hp => by
          change p.2 ∈ (chartAt E x).source
          simpa only [e,extChartAt_source] using hp.2.1)
    exact hΦ.comp (contMDiff_fst.contMDiffOn.prodMk_space hc) (fun _ hp => ⟨hp.1,hp.2.2⟩)
  · intro y hy
    exact (hΦ0 (e y) hy.2).trans (e.left_inv hy.1)
  · intro y hy
    exact hΦd (e y) hy.2


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_uniform_smooth_manifold_families
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x, x ∉ K → v x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : M, ∃ (W : Set M) (Ψ : ℝ × M → M),
      IsOpen W ∧ x ∈ W ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ (Ioo (-ε) ε ×ˢ W) ∧
      (∀ y ∈ W, Ψ (0,y) = y) ∧
      (∀ y ∈ W, IsMIntegralCurveOn (fun t => Ψ (t,y)) v (Ioo (-ε) ε)) := by
  classical
  choose ε W Ψ hε hW hxW hΨs hΨ0 hΨd using exists_smooth_local_manifold_family hv
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover W hW (fun x _ => mem_iUnion.mpr ⟨x,hxW x⟩)
  have hsmall : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, δ ≤ ε x := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ,hδ,hδs⟩ := ih
      refine ⟨min (ε a) δ,lt_min (hε a) hδ,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hδs x hx)
  obtain ⟨δ,hδ,hδs⟩ := hsmall
  refine ⟨δ,hδ,fun x => ?_⟩
  by_cases hx : x ∈ K
  · obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hs hx)
    have hI : Ioo (-δ) δ ⊆ Ioo (-ε a) (ε a) :=
      Ioo_subset_Ioo (neg_le_neg (hδs a ha)) (hδs a ha)
    exact ⟨W a,Ψ a,hW a,hxa,(hΨs a).mono (prod_mono hI Subset.rfl),
      hΨ0 a,fun y hy => (hΨd a y hy).mono hI⟩
  · exact ⟨Kᶜ,Prod.snd,hK.isClosed.isOpen_compl,hx,contMDiff_snd.contMDiffOn,
      fun _ _ => rfl,fun y hy => (isMIntegralCurve_const (hvK y hy)).isMIntegralCurveOn _⟩

theorem exists_global_compact_manifold_trajectory
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x, x ∉ K → v x = 0) (x : M) :
    ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ v := by
  obtain ⟨ε,hε,h⟩ := exists_uniform_smooth_manifold_families hv hK hvK
  apply exists_isMIntegralCurve_of_isMIntegralCurveOn (hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hε _ x
  intro y
  obtain ⟨W,Ψ,_,hy,_,hΨ0,hΨd⟩ := h y
  exact ⟨fun t => Ψ (t,y),hΨ0 y hy,hΨd y hy⟩



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_FlowSmoothExtension
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem flow_smooth_of_uniform_local
    (F : ℝ × M → M) (hzero : ∀ x, F (0,x) = x)
    (hadd : ∀ s t x, F (s+t,x) = F (s,F (t,x)))
    {ε : ℝ} (hε : 0 < ε)
    (hs : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (Ioo (-ε) ε ×ˢ univ)) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F := by
  have hshort (t : ℝ) (ht : t ∈ Ioo (-ε) ε) (x : M) :
      ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (t,x) :=
    hs.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht,mem_univ x⟩)
  have hmultiple (n : ℕ) (t : ℝ) (ht : t ∈ Ioo (-ε) ε) (x : M) :
      ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞
        (fun p : ℝ × M => F ((n:ℝ)*p.1,p.2)) (t,x) := by
    induction n with
    | zero => simpa only [Nat.cast_zero,zero_mul,hzero] using
        (contMDiffAt_snd : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Prod.snd (t,x))
    | succ n ih =>
      have h := (hshort t ht (F ((n:ℝ)*t,x))).comp (t,x) (contMDiffAt_fst.prodMk ih)
      have he : (fun p : ℝ × M => F (((n+1:ℕ):ℝ)*p.1,p.2)) =
          (fun p : ℝ × M => F (p.1,F ((n:ℝ)*p.1,p.2))) := by
        funext p
        rw [Nat.cast_add,Nat.cast_one,add_mul,one_mul,add_comm,hadd]
      rw [he]
      exact h
  intro p
  obtain ⟨n,hn⟩ := exists_nat_gt (max (|p.1|/ε) 1)
  have hn0 : (0:ℝ) < n := lt_trans (by norm_num) ((le_max_right _ _).trans_lt hn)
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hn0
  have ht : p.1/(n:ℝ) ∈ Ioo (-ε) ε := by
    apply abs_lt.mp
    rw [abs_div,abs_of_pos hn0,div_lt_iff₀ hn0]
    have hb := (div_lt_iff₀ hε).mp ((le_max_left _ _).trans_lt hn)
    simpa only [mul_comm] using hb
  have hc : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞
      (fun q : ℝ × M => (q.1/(n:ℝ),q.2)) :=
    ((contDiff_id.div_const (n:ℝ)).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  have h := (hmultiple n (p.1/n) ht p.2).comp p hc.contMDiffAt
  have hcancel (r : ℝ) : (n:ℝ)*(r/(n:ℝ)) = r := by field_simp
  simpa only [Function.comp_def,hcancel] using h


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_smooth_global_manifold_flow
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hvK : ∀ x, x ∉ K → v x = 0) :
    ∃ F : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F ∧
      (∀ x, F (0,x) = x) ∧
      (∀ s t x, F (s+t,x) = F (s,F (t,x))) ∧
      (∀ x, IsMIntegralCurve (fun t => F (t,x)) v) ∧
      (∀ x, v x = 0 → ∀ t, F (t,x) = x) := by
  classical
  choose γ hγ0 hγd using exists_global_compact_manifold_trajectory hv hK hvK
  let F : ℝ × M → M := fun p => γ p.2 p.1
  have hF0 (x : M) : F (0,x) = x := hγ0 x
  have hFd (x : M) : IsMIntegralCurve (fun t => F (t,x)) v := hγd x
  have hv1 : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)) := hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hFa (s t : ℝ) (x : M) : F (s+t,x) = F (s,F (t,x)) := by
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
      ((hFd x).comp_add t) (hFd (F (t,x))) (by simp only [Function.comp_apply,zero_add,hF0])
    exact congrFun he s
  obtain ⟨ε,hε,hfamilies⟩ := exists_uniform_smooth_manifold_families hv hK hvK
  have hFs : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (Ioo (-ε) ε ×ˢ univ) := by
    intro p hp
    obtain ⟨W,Ψ,hW,hpW,hΨs,hΨ0,hΨd⟩ := hfamilies p.2
    have heq : EqOn F Ψ (Ioo (-ε) ε ×ˢ W) := by
      intro q hq
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (t₀ := 0) ⟨neg_lt_zero.mpr hε,hε⟩ hv1 ((hFd q.2).isMIntegralCurveOn _)
        (hΨd q.2 hq.2) ((hF0 q.2).trans (hΨ0 q.2 hq.2).symm) hq.1
    have hnb : Ioo (-ε) ε ×ˢ W ∈ 𝓝 p := (isOpen_Ioo.prod hW).mem_nhds ⟨hp.1,hpW⟩
    exact ((hΨs.contMDiffAt hnb).congr_of_eventuallyEq
      (Filter.mem_of_superset hnb heq)).contMDiffWithinAt
  refine ⟨F,flow_smooth_of_uniform_local F hF0 hFa hε hFs,hF0,hFa,hFd,?_⟩
  intro x hx t
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
    (hFd x) (isMIntegralCurve_const hx) (hF0 x)
  exact congrFun he t



omit [FiniteDimensional ℝ E] in

theorem exists_smooth_global_manifold_flow_of_uniform_families
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {ε : ℝ} (hε : 0 < ε)
    (hfamilies : ∀ x : M, ∃ (W : Set M) (Ψ : ℝ × M → M),
      IsOpen W ∧ x ∈ W ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ (Ioo (-ε) ε ×ˢ W) ∧
      (∀ y ∈ W, Ψ (0,y) = y) ∧
      (∀ y ∈ W, IsMIntegralCurveOn (fun t => Ψ (t,y)) v (Ioo (-ε) ε))) :
    ∃ F : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F ∧
      (∀ x, F (0,x) = x) ∧
      (∀ s t x, F (s+t,x) = F (s,F (t,x))) ∧
      (∀ x, IsMIntegralCurve (fun t => F (t,x)) v) ∧
      (∀ x, v x = 0 → ∀ t, F (t,x) = x) := by
  classical
  have hex (x : M) : ∃ γ : ℝ → M, γ 0=x ∧ IsMIntegralCurve γ v := by
    apply exists_isMIntegralCurve_of_isMIntegralCurveOn (hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hε _ x
    intro y
    obtain ⟨W,Ψ,_,hy,_,hΨ0,hΨd⟩ := hfamilies y
    exact ⟨fun t => Ψ (t,y),hΨ0 y hy,hΨd y hy⟩
  choose γ hγ0 hγd using hex
  let F : ℝ × M → M := fun p => γ p.2 p.1
  have hF0 (x : M) : F (0,x) = x := hγ0 x
  have hFd (x : M) : IsMIntegralCurve (fun t => F (t,x)) v := hγd x
  have hv1 : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent 1
      (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)) := hv.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hFa (s t : ℝ) (x : M) : F (s+t,x) = F (s,F (t,x)) := by
    have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
      ((hFd x).comp_add t) (hFd (F (t,x))) (by simp only [Function.comp_apply,zero_add,hF0])
    exact congrFun he s
  have hFs : ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ F (Ioo (-ε) ε ×ˢ univ) := by
    intro p hp
    obtain ⟨W,Ψ,hW,hpW,hΨs,hΨ0,hΨd⟩ := hfamilies p.2
    have heq : EqOn F Ψ (Ioo (-ε) ε ×ˢ W) := by
      intro q hq
      exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        (t₀ := 0) ⟨neg_lt_zero.mpr hε,hε⟩ hv1 ((hFd q.2).isMIntegralCurveOn _)
        (hΨd q.2 hq.2) ((hF0 q.2).trans (hΨ0 q.2 hq.2).symm) hq.1
    have hnb : Ioo (-ε) ε ×ˢ W ∈ 𝓝 p := (isOpen_Ioo.prod hW).mem_nhds ⟨hp.1,hpW⟩
    exact ((hΨs.contMDiffAt hnb).congr_of_eventuallyEq
      (Filter.mem_of_superset hnb heq)).contMDiffWithinAt
  refine ⟨F,flow_smooth_of_uniform_local F hF0 hFa hε hFs,hF0,hFa,hFd,?_⟩
  intro x hx t
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hv1
    (hFd x) (isMIntegralCurve_const hx) (hF0 x)
  exact congrFun he t



theorem exists_uniform_smooth_manifold_families_of_background
    {v : (x : M) → TangentSpace 𝓘(ℝ,E) x}
    (hv : ContMDiff 𝓘(ℝ,E) (𝓘(ℝ,E)).tangent ∞ (fun x => (⟨x,v x⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (B : ℝ × M → M)
    (hB : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ B)
    (hB0 : ∀ x, B (0,x)=x)
    (hBd : ∀ x, x ∉ K → IsMIntegralCurve (fun t => B (t,x)) v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : M, ∃ (W : Set M) (Ψ : ℝ × M → M),
      IsOpen W ∧ x ∈ W ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ (Ioo (-ε) ε ×ˢ W) ∧
      (∀ y ∈ W, Ψ (0,y) = y) ∧
      (∀ y ∈ W, IsMIntegralCurveOn (fun t => Ψ (t,y)) v (Ioo (-ε) ε)) := by
  classical
  choose ε W Ψ hε hW hxW hΨs hΨ0 hΨd using exists_smooth_local_manifold_family hv
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover W hW (fun x _ => mem_iUnion.mpr ⟨x,hxW x⟩)
  have hsmall : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, δ ≤ ε x := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1,by norm_num,by simp⟩
    | @insert a s ha ih =>
      obtain ⟨δ,hδ,hδs⟩ := ih
      refine ⟨min (ε a) δ,lt_min (hε a) hδ,?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hδs x hx)
  obtain ⟨δ,hδ,hδs⟩ := hsmall
  refine ⟨δ,hδ,fun x => ?_⟩
  by_cases hx : x ∈ K
  · obtain ⟨a,ha,hxa⟩ := mem_iUnion₂.mp (hs hx)
    have hI : Ioo (-δ) δ ⊆ Ioo (-ε a) (ε a) :=
      Ioo_subset_Ioo (neg_le_neg (hδs a ha)) (hδs a ha)
    exact ⟨W a,Ψ a,hW a,hxa,(hΨs a).mono (prod_mono hI Subset.rfl),
      hΨ0 a,fun y hy => (hΨd a y hy).mono hI⟩
  · exact ⟨Kᶜ,B,hK.isClosed.isOpen_compl,hx,hB.contMDiffOn,
      fun y _ => hB0 y,fun y hy => (hBd y hy).isMIntegralCurveOn _⟩


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold

theorem exists_smooth_scalar_clock_flow {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) :
    ∃ C : ℝ × ℝ → ℝ, ContDiff ℝ ∞ C ∧ (∀ a, C (0,a)=a) ∧
      (∀ a t, HasDerivAt (fun s => C (s,a)) (χ (C (t,a))) t) ∧
      (∀ a, χ a=0 → ∀ t, C (t,a)=a) := by
  have hv : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ)).tangent ∞
      (fun a => (⟨a,χ a⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hχ
  obtain ⟨C,hC,hC0,_,hCd,hCfix⟩ := exists_smooth_global_manifold_flow hv hχc
    (fun _ hx => image_eq_zero_of_notMem_tsupport hx)
  refine ⟨C,?_,hC0,?_,hCfix⟩
  · rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at hC
    exact contMDiff_iff_contDiff.mp hC
  · intro a t
    have hd := hasMFDerivAt_iff_hasFDerivAt.mp (hCd a t)
    rw [hasDerivAt_iff_hasFDerivAt]
    exact hd


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem timeLiftField_smooth {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M))) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)).tangent) ∞
      (fun p => (⟨p,timeLiftField χ V p⟩ : TangentBundle ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (ℝ × M))) := by
  have hc : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,ℝ)).tangent ∞
      (fun p : ℝ × M => (⟨p.1,(1:ℝ)⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ)) := by
    have hp : ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,ℝ)).tangent ∞
        (fun r : ℝ => (⟨r,(1:ℝ)⟩ : TangentBundle 𝓘(ℝ,ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    exact hp.comp contMDiff_fst
  have hu : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)).tangent) ∞
      (fun p : ℝ × M => (⟨p,((1:ℝ),V p)⟩ : TangentBundle ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (ℝ × M))) :=
    contMDiff_equivTangentBundleProd_symm.comp (hc.prodMk hV)
  exact (hχ.contMDiff.comp contMDiff_fst).smul_section hu

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem timeLiftField_clock_derivative {χ : ℝ → ℝ}
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2} {γ : ℝ → ℝ × M} {t : ℝ}
    (hd : HasMFDerivAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeLiftField χ V (γ t)))) :
    HasDerivAt (fun s => (γ s).1) (χ (γ t).1) t := by
  rw [hasDerivAt_iff_hasFDerivAt]
  apply hasMFDerivAt_iff_hasFDerivAt.mp
  apply ((hasMFDerivAt_fst (γ t)).comp t hd).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change a * (χ (γ t).1 * 1) = a * χ (γ t).1
  rw [mul_one]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem timeLiftField_spatial_derivative {χ : ℝ → ℝ}
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2} {γ : ℝ → ℝ × M} {t : ℝ}
    (hd : HasMFDerivAt 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (timeLiftField χ V (γ t)))) :
    HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s => (γ s).2) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (χ (γ t).1 • V (γ t))) := by
  apply ((hasMFDerivAt_snd (γ t)).comp t hd).congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  rfl


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

theorem timeLift_constant_spatial_curve {χ : ℝ → ℝ}
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    {x : M} (hx : ∀ s, V (s,x) = 0) {γ : ℝ → ℝ}
    (hγ : ∀ t, HasDerivAt γ (χ (γ t)) t) :
    IsMIntegralCurve (fun t => (γ t,x)) (timeLiftField χ V) := by
  intro t
  have hc : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun _ : ℝ => x) t 0 :=
    hasMFDerivAt_const (x := t) x
  have hr : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (χ (γ t))) := (hγ t).hasFDerivAt.hasMFDerivAt
  have hd := hr.prodMk hc
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro a
  change ℝ at a
  change (a * χ (γ t),0) = (a * (χ (γ t) * 1),a • (χ (γ t) • V (γ t,x)))
  rw [hx,mul_one,smul_zero,smul_zero]

variable [T2Space M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem timeLift_spatial_stationary {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {a : ℝ} {x : M} (hx : ∀ s, V (s,x) = 0)
    {γ : ℝ → ℝ × M} (hγ : IsMIntegralCurve γ (timeLiftField χ V))
    (h0 : γ 0 = (a,x)) (t : ℝ) : (γ t).2 = x := by
  have hd := timeLift_constant_spatial_curve hx (fun s => timeLiftField_clock_derivative (hγ s))
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    ((timeLiftField_smooth hχ hV).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hγ hd (by rw [h0])
  exact congrArg Prod.snd (congrFun he t)


end

section
open scoped Topology NNReal
open Set Function

theorem scalar_clock_eq {χ : ℝ → ℝ} {L : ℝ≥0} (hL : LipschitzWith L χ)
    (hχ : ∀ s ∈ Icc (-3:ℝ) 3, χ s = 1)
    {γ : ℝ → ℝ} (hd : ∀ t, HasDerivAt γ (χ (γ t)) t)
    {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (h0 : γ 0 = a) :
    EqOn γ (fun t => a+t) (Ioo (-2:ℝ) 2) := by
  apply ODE_solution_unique_of_mem_Ioo
    (s := fun _ => univ) (fun _ _ => hL.lipschitzOnWith)
    (t₀ := 0) (by constructor <;> norm_num)
    (fun t _ => ⟨hd t,mem_univ _⟩)
  · intro t ht
    have hm : a+t ∈ Icc (-3:ℝ) 3 := by constructor <;> linarith [ha.1,ha.2,ht.1,ht.2]
    rw [hχ _ hm]
    exact ⟨by simpa only [Function.id_def] using (hasDerivAt_id t).const_add a,mem_univ _⟩
  · simpa only [add_zero] using h0


end

section
open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_spatially_compact_time_lift
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hVK : ∀ s x, x ∉ K → V (s,x)=0) :
    ∃ (χ : ℝ → ℝ) (G : ℝ × (ℝ × M) → ℝ × M),
      ContDiff ℝ ∞ χ ∧ (∀ s ∈ Icc (-3:ℝ) 3, χ s = 1) ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)))
        ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ G ∧
      (∀ p, G (0,p) = p) ∧
      (∀ s t p, G (s+t,p) = G (s,G (t,p))) ∧
      (∀ p, IsMIntegralCurve (fun t => G (t,p)) (timeLiftField χ V)) ∧
      (∀ a ∈ Icc (0:ℝ) 1, ∀ x t, t ∈ Ioo (-2:ℝ) 2 → (G (t,(a,x))).1 = a+t) := by
  obtain ⟨χ,hχ,hχc,_,hχone,_⟩ := exists_smooth_cutoff (isCompact_Icc (a := (-3:ℝ)) (b := 3))
    isOpen_univ (subset_univ _)
  have hχ1 : ∀ s ∈ Icc (-3:ℝ) 3, χ s = 1 := hχone.self_of_nhdsSet
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hprod : IsManifold ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ (ℝ × M) := inferInstance
  let instProd : ChartedSpace (ℝ × E) (ℝ × M) := prodChartedSpace ℝ ℝ E M
  have : IsManifold 𝓘(ℝ,ℝ × E) ∞ (ℝ × M) := by
    simpa only [modelWithCornersSelf_prod,instProd] using hprod
  have hv : ContMDiff 𝓘(ℝ,ℝ × E) (𝓘(ℝ,ℝ × E)).tangent ∞
      (fun p => (⟨p,timeLiftField χ V p⟩ : TangentBundle 𝓘(ℝ,ℝ × E) (ℝ × M))) := by
    simpa only [modelWithCornersSelf_prod,instProd] using! timeLiftField_smooth hχ hV
  obtain ⟨C,hC,hC0,hCd,hCfix⟩ := exists_smooth_scalar_clock_flow hχ hχc
  let B : ℝ × (ℝ × M) → ℝ × M := fun p => (C (p.1,p.2.1),p.2.2)
  have hCm : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ)) 𝓘(ℝ,ℝ) ∞ C := by
    rw [← modelWithCornersSelf_prod,chartedSpaceSelf_prod]
    exact hC.contMDiff
  have hBm : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)))
      ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ B :=
    (hCm.comp (contMDiff_fst.prodMk (contMDiff_fst.comp contMDiff_snd))).prodMk
      (contMDiff_snd.comp contMDiff_snd)
  have hB0 (p : ℝ × M) : B (0,p)=p := by dsimp [B]; rw [hC0]
  have hBd (p : ℝ × M) (hp : p ∉ tsupport χ ×ˢ K) :
      IsMIntegralCurve (fun t => B (t,p)) (timeLiftField χ V) := by
    by_cases hx : p.2 ∈ K
    · have ha : p.1 ∉ tsupport χ := fun ht => hp ⟨ht,hx⟩
      have hz : χ p.1=0 := image_eq_zero_of_notMem_tsupport ha
      have he : (fun t => B (t,p))=(fun _ => p) := by
        funext t
        dsimp [B]
        rw [hCfix p.1 hz t]
      rw [he]
      apply isMIntegralCurve_const
      rw [timeLiftField,hz,zero_smul]
      rfl
    · exact timeLift_constant_spatial_curve (fun s => hVK s p.2 hx) (hCd p.1)
  have hBs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,ℝ × E)) 𝓘(ℝ,ℝ × E) ∞ B := by
    simpa only [modelWithCornersSelf_prod,instProd] using hBm
  have hBd' (p : ℝ × M) (hp : p ∉ tsupport χ ×ˢ K) :
      IsMIntegralCurve (I := 𝓘(ℝ,ℝ × E)) (fun t => B (t,p)) (timeLiftField χ V) := by
    intro t
    have hderiv := hBd p hp t
    simp only [HasMFDerivAt,modelWithCornersSelf_prod] at hderiv ⊢
    refine ⟨hderiv.1,?_⟩
    convert hderiv.2 using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  obtain ⟨ε,hε,hfamilies⟩ := exists_uniform_smooth_manifold_families_of_background
    hv (hχc.prod hK) B hBs hB0 hBd'
  obtain ⟨G,hGs,hG0,hGa,hGd,_⟩ := exists_smooth_global_manifold_flow_of_uniform_families
    hv hε hfamilies
  have hGs' : ContMDiff ((𝓘(ℝ,ℝ)).prod ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)))
      ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) ∞ G := by
    simpa only [modelWithCornersSelf_prod,instProd] using hGs
  have hGd' : ∀ p, IsMIntegralCurve (fun t => G (t,p)) (timeLiftField χ V) := by
    intro p t
    have hderiv := hGd p t
    simp only [HasMFDerivAt,modelWithCornersSelf_prod] at hderiv ⊢
    refine ⟨hderiv.1,?_⟩
    convert hderiv.2 using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  refine ⟨χ,G,hχ,hχ1,hGs',hG0,hGa,hGd',?_⟩
  intro a ha x t ht
  exact scalar_clock_eq hL hχ1 (fun s => timeLiftField_clock_derivative (hGd' (a,x) s)) ha
    (congrArg Prod.fst (hG0 (a,x))) ht


end

open scoped ContDiff Manifold Topology NNReal
open Set Function Manifold



end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Flows_NonautonomousManifoldFlow
attribute [-simp] _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_one _root_.OAI.PackingSufficiencySupport.Hamiltonian.toricPrimitiveInterpolation_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem exists_spatially_compact_nonautonomous_flow
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hV : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) (𝓘(ℝ,E)).tangent ∞
      (fun p => (⟨p.2,V p⟩ : TangentBundle 𝓘(ℝ,E) M)))
    {K : Set M} (hK : IsCompact K) (hVK : ∀ s x, x ∉ K → V (s,x)=0) :
    ∃ Φ Ψ : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x)) = x ∧ Φ (t,Ψ (t,x)) = x) ∧
      (∀ x t, t ∈ Ioo (-2:ℝ) 2 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
        (fun s => Φ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x))))) ∧
      (∀ x, (∀ s, V (s,x) = 0) → ∀ t, Φ (t,x) = x) := by
  obtain ⟨χ,G,hχ,hχ1,hGs,hG0,hGa,hGd,hclock⟩ := exists_spatially_compact_time_lift hV hK hVK
  let Φ : ℝ × M → M := fun p => (G (p.1,(0,p.2))).2
  let Ψ : ℝ × M → M := fun p => (G (-p.1,p)).2
  have hΦs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ :=
    contMDiff_snd.comp (hGs.comp (contMDiff_fst.prodMk (contMDiff_const.prodMk contMDiff_snd)))
  have hneg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (fun p : ℝ × M => -p.1) :=
    contDiff_neg.contMDiff.comp contMDiff_fst
  have hΨs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ :=
    contMDiff_snd.comp (hGs.comp (hneg.prodMk contMDiff_id))
  have hΦclock (t : ℝ) (ht : t ∈ Ioo (-2:ℝ) 2) (x : M) : G (t,(0,x)) = (t,Φ (t,x)) := by
    apply Prod.ext
    · simpa only [zero_add] using hclock 0 (by norm_num) x t ht
    · rfl
  refine ⟨Φ,Ψ,hΦs,hΨs,?_,?_,?_,?_⟩
  · intro x
    exact congrArg Prod.snd (hG0 (0,x))
  · intro t ht x
    have ht' : t ∈ Ioo (-2:ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
    have hmt : -t ∈ Ioo (-2:ℝ) 2 := by constructor <;> linarith [ht.1,ht.2]
    constructor
    · change (G (-t,(t,Φ (t,x)))).2 = x
      rw [←hΦclock t ht' x,←hGa,neg_add_cancel,hG0]
    · have hΨclock : G (-t,(t,x)) = (0,Ψ (t,x)) := by
        apply Prod.ext
        · simpa only [add_neg_cancel] using hclock t ht x (-t) hmt
        · rfl
      change (G (t,(0,Ψ (t,x)))).2 = x
      rw [←hΨclock,←hGa,add_neg_cancel,hG0]
  · intro x t ht
    have hd := timeLiftField_spatial_derivative (hGd (0,x) t)
    have hh : χ t = 1 := hχ1 t ⟨by linarith [ht.1],by linarith [ht.2]⟩
    rw [hΦclock t ht x] at hd
    simpa only [hh,one_smul] using hd
  · intro x hx t
    exact timeLift_spatial_stationary hχ hV hx (hGd (0,x)) (hG0 (0,x)) t

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport
open Set

theorem constant_above_on_convex {s : Set ℝ} (hs : Convex ℝ s)
    {f : ℝ → ℝ} (hf : ContinuousOn f s) {a t₀ : ℝ} (ht₀ : t₀ ∈ s)
    (hzero : ∀ t ∈ s, a < f t → HasDerivWithinAt f 0 s t)
    (h₀ : a < f t₀) : ∀ t ∈ s, f t = f t₀ := by
  let : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs.isPreconnected
  let T : Set s := {t | f t = f t₀}
  have hfc : Continuous (fun t : s => f t) := hf.domRestrict
  have hc : IsClosed T := isClosed_eq hfc continuous_const
  have ho : IsOpen T := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have hft : a < f t := by rw [ht]; exact h₀
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
      ((isOpen_lt continuous_const hfc).mem_nhds hft)
    apply Filter.mem_of_superset (Metric.ball_mem_nhds t hr)
    intro u hu
    let U : Set ℝ := s ∩ Metric.ball (t : ℝ) r
    have hUc : Convex ℝ U := hs.inter (convex_ball (t:ℝ) r)
    have hUd (v : ℝ) (hv : v ∈ U) : HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) U v := by
      have habove : a < f v := hball (show (⟨v,hv.1⟩ : s) ∈ Metric.ball t r from hv.2)
      simpa using (hzero v hv.1 habove).hasFDerivWithinAt.mono inter_subset_left
    have htU : (t : ℝ) ∈ U := ⟨t.property,Metric.mem_ball_self hr⟩
    have huU : (u : ℝ) ∈ U := ⟨u.property,hu⟩
    have hb := hUc.norm_image_sub_le_of_norm_hasFDerivWithin_le hUd
      (fun v hv => by simp : ∀ v ∈ U, ‖(0 : ℝ →L[ℝ] ℝ)‖ ≤ (0:ℝ)) htU huU
    have he : f u = f t := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hb))
    exact he.trans ht
  have he : T = univ := (show IsClopen T from ⟨hc,ho⟩).eq_univ ⟨⟨t₀,ht₀⟩,rfl⟩
  intro t ht
  exact (show (⟨t,ht⟩ : s) ∈ T from he.symm ▸ mem_univ _)

theorem sublevel_iff_of_zero_in_collar {s : Set ℝ} (hs : Convex ℝ s)
    {f : ℝ → ℝ} (hf : ContinuousOn f s) {a c t u : ℝ} (hac : a < c)
    (ht : t ∈ s) (hu : u ∈ s)
    (hzero : ∀ r ∈ s, a < f r → HasDerivWithinAt f 0 s r) :
    f t ≤ c ↔ f u ≤ c := by
  have hdir (t u : ℝ) (ht : t ∈ s) (hu : u ∈ s) (h : f t ≤ c) : f u ≤ c := by
    by_contra hn
    have hc : c < f u := lt_of_not_ge hn
    have he := constant_above_on_convex hs hf hu hzero (hac.trans hc) t ht
    linarith
  exact ⟨hdir t u ht hu,hdir u t hu ht⟩

end PackingSufficiencySupport

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifold_flow_sublevels_iff
    {Φ : ℝ × M → M} {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,E) p.2}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    (hΦ0 : ∀ x, Φ (0,x)=x)
    (hODE : ∀ x t, t ∈ Icc (0:ℝ) 1 → HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E)
      (fun s => Φ (s,x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t,Φ (t,x)))))
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i < c i)
    (htan : ∀ i t x, a i<μ i x → mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) x (V (t,x))=0)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : M) :
    (∀ i, μ i (Φ (t,x)) ≤ c i) ↔ (∀ i, μ i x ≤ c i) := by
  have he (i : ι) : μ i (Φ (t,x)) ≤ c i ↔ μ i x ≤ c i := by
    have hz (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (ha : a i<μ i (Φ (s,x))) :
        HasDerivWithinAt (fun r => μ i (Φ (r,x))) 0 (Icc (0:ℝ) 1) s := by
      have hd := ((hμ i).mdifferentiable (by simp) (Φ (s,x))).hasMFDerivAt.comp s
        (hODE x s hs)
      have heq : (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) (Φ (s,x))).comp
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (s,Φ (s,x))))=(0 : ℝ →L[ℝ] ℝ) := by
        ext
        simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
          map_smul,htan i s (Φ (s,x)) ha,smul_zero]
        rfl
      have hd' : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ)
          (fun r => μ i (Φ (r,x))) s 0 := hd.congr_mfderiv heq
      exact (hasDerivAt_iff_hasFDerivAt.mpr
        (by simpa using! hasMFDerivAt_iff_hasFDerivAt.mp hd')).hasDerivWithinAt
    have hc : ContinuousOn (fun r => μ i (Φ (r,x))) (Icc (0:ℝ) 1) :=
      ((hμ i).continuous.comp (hΦ.continuous.comp
        (continuous_id.prodMk continuous_const))).continuousOn
    simpa only [hΦ0] using sublevel_iff_of_zero_in_collar (convex_Icc (0:ℝ) 1)
      hc (hac i) ht (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) hz
  exact forall_congr' he

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifold_flow_image_sublevels
    {Φ Ψ : ℝ × M → M}
    (hΦ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ)
    (hΨ : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ)
    (t : ℝ) (hinv : ∀ x, Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x)
    {D : Set M} (hD : ∀ x, Φ (t,x) ∈ D ↔ x ∈ D) :
    (fun x => Φ (t,x)) '' D=D ∧
      (fun x => Φ (t,x)) '' interior D=interior D := by
  let f := nonautonomousSlice Φ Ψ hΦ hΨ t hinv
  have he : (fun x => Φ (t,x)) '' D=D := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩; exact (hD x).mpr hx
    · intro hy
      exact ⟨Ψ (t,y),(hD _).mp (by simpa only [(hinv y).2] using hy),(hinv y).2⟩
  refine ⟨he,?_⟩
  change f.toHomeomorph '' interior D=interior D
  rw [f.toHomeomorph.image_interior]
  exact congrArg interior he

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem manifold_relative_sublevel_moser
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i < c i)
    (hD : IsCompact {x | ∀ i, μ i x ≤ c i})
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hDU : Icc (0:ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i} ⊆ U)
    (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible)
    (hskew : ∀ p ∈ U, ∀ v w, Ω p.1 p.2 v w = -Ω p.1 p.2 w v)
    (hclosed : ∀ t b y, y ∈ (extChartAt 𝓘(ℝ,E) b).target →
      (t,(extChartAt 𝓘(ℝ,E) b).symm y) ∈ U → ∀ u v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t,y) (0,u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t,y) (0,v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t,y) (0,w) u v = 0)
    (htime : ∀ t b y, y ∈ (extChartAt 𝓘(ℝ,E) b).target →
      (t,(extChartAt 𝓘(ℝ,E) b).symm y) ∈ U → ∀ v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t,y) (1,0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) b q.2) (t,y) (0,v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) b q.2) (t,y) (0,w) v)
    (Z : ι → M → E)
    (hface : ∀ i p, p ∈ U → a i<μ i p.2 →
      α p.1 p.2=0 ∨
      (Ω p.1 p.2 (Z i p.2) = -mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) p.2 ∧
        α p.1 p.2 (Z i p.2)=0)) :
    ∃ Φ Ψ : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
      (∀ x, Φ (0,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → Φ (t,x)=x) ∧
      (∀ x, (∀ t, α t x=0) → ∀ t, Φ (t,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1,
        (fun x => Φ (t,x)) '' {x | ∀ i, μ i x ≤ c i}={x | ∀ i, μ i x ≤ c i} ∧
        (fun x => Φ (t,x)) '' interior {x | ∀ i, μ i x ≤ c i}=interior {x | ∀ i, μ i x ≤ c i}) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, (∀ i, μ i x ≤ c i) → ∀ v w,
        manifoldPullback Φ Ω t x v w=Ω 0 x v w) := by
  obtain ⟨V,hV,hVe,hVz,⟨C,hC,hVC⟩,hVtan⟩ := exists_joint_localized_manifold_moser_field
    hΩ hα (isCompact_Icc.prod hD) hU hDU hinv
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦinv,hODE,hfix⟩ :=
    exists_spatially_compact_nonautonomous_flow hV hC hVC
  have htangent (i : ι) (t : ℝ) (x : M) (hx : a i<μ i x) :
      mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) x (V (t,x))=0 := by
    apply hVtan
    intro hp
    rcases hface i (t,x) hp hx with hz | ⟨hm,hh⟩
    · simp only [manifoldMoserField,hz,map_zero,neg_zero]
      exact (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) x).map_zero
    · exact manifoldMoserField_moment_tangent (hinv (t,x) hp) (hskew (t,x) hp)
        _ (Z i x) hm hh
  have hiff (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) (x : M) :
      (∀ i, μ i (Φ (t,x)) ≤ c i) ↔ (∀ i, μ i x ≤ c i) := by
    apply manifold_flow_sublevels_iff hΦ hΦ0 _ μ hμ a c hac htangent t ht x
    intro y s hs
    exact hODE y s ⟨by linarith [hs.1],by linarith [hs.2]⟩
  refine ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦinv,⟨C,hC,?_⟩,?_,?_,?_⟩
  · intro t x hx
    exact hfix x (fun s => hVC s x hx) t
  · intro x hx t
    exact hfix x (fun s => hVz (s,x) (hx s)) t
  · intro t ht
    exact manifold_flow_image_sublevels hΦ hΨ t (hΦinv t ht) (hiff t ht)
  · intro t ht x hx v w
    have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
        HasDerivAt (fun r => manifoldPullback Φ Ω r x v w) 0 s := by
      apply local_manifold_form_transport_derivative hΦ hV isOpen_Ioo hODE hΩ
        (show s ∈ Ioo (-2:ℝ) 2 by constructor <;> linarith [hs.1,hs.2]) x
      intro b y hy he
      have hpK : (s,(extChartAt 𝓘(ℝ,E) b).symm y) ∈
          Icc (0:ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i} :=
        ⟨hs,by rw [he]; exact (hiff s hs x).mpr hx⟩
      have hpU := hDU hpK
      have hn : (univ ×ˢ (extChartAt 𝓘(ℝ,E) b).target) ∈ 𝓝 (s,y) :=
        (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) b)).mem_nhds ⟨mem_univ _,hy⟩
      apply joint_manifold_moser_PDE hV hU hy hpU hinv
        (hVe.filter_mono (nhds_le_nhdsSet hpK)) ((hΩ b).contDiffAt hn)
        ((hα b).contDiffAt hn) _ (hclosed s b y hy hpU) (htime s b y hy hpU)
      intro u z
      exact hskew _ hpU _ _
    have he := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hd s hs).hasDerivWithinAt)
      (fun s hs => (by simp : ‖(0:ℝ)‖ ≤ (0:ℝ)))
      (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) ht
    have hconst : manifoldPullback Φ Ω t x v w=manifoldPullback Φ Ω 0 x v w := by
      simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using he
    rw [hconst]
    have hid : (fun y => Φ (0,y))=id := funext hΦ0
    have hDifferential : preferredDifferential (E := E) (fun y => Φ (0,y)) x=
        ContinuousLinearMap.id ℝ E := by
      change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) (fun y => Φ (0,y)) x=_
      rw [hid]
      exact mfderiv_id
    rw [manifoldPullback,hDifferential]
    simp only [hΦ0,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]

theorem manifold_exact_sublevel_moser_bp240_oai
    {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i < c i)
    (hD : IsCompact {x | ∀ i, μ i x ≤ c i})
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hDU : Icc (0:ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i} ⊆ U)
    (hinv : ∀ p ∈ U, (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible)
    (Z : ι → M → E)
    (hface : ∀ i p, p ∈ U → a i<μ i p.2 →
      (∀ t, Γ t p.2=Γ 0 p.2) ∨
      (manifoldExteriorOneForm (Γ p.1) p.2 (Z i p.2) = -mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) p.2 ∧
        ∀ t, Γ t p.2 (Z i p.2)=Γ 0 p.2 (Z i p.2))) :
    ∃ Φ Ψ : ℝ × M → M,
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Φ ∧
      ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ Ψ ∧
      (∀ x, Φ (0,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, Ψ (t,Φ (t,x))=x ∧ Φ (t,Ψ (t,x))=x) ∧
      (∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → Φ (t,x)=x) ∧
      (∀ x, (∀ t, Γ t x=Γ 0 x) → ∀ t, Φ (t,x)=x) ∧
      (∀ t ∈ Icc (0:ℝ) 1,
        (fun x => Φ (t,x)) '' {x | ∀ i, μ i x ≤ c i}={x | ∀ i, μ i x ≤ c i} ∧
        (fun x => Φ (t,x)) '' interior {x | ∀ i, μ i x ≤ c i}=interior {x | ∀ i, μ i x ≤ c i}) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ x, (∀ i, μ i x ≤ c i) → ∀ v w,
        manifoldPullback Φ (fun s => manifoldExteriorOneForm (Γ s)) t x v w=
          manifoldExteriorOneForm (Γ 0) x v w) := by
  have hf : ∀ i p, p ∈ U → a i<μ i p.2 →
      manifoldTimePrimitive Γ p.1 p.2=0 ∨
      (manifoldExteriorOneForm (Γ p.1) p.2 (Z i p.2) = -mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (μ i) p.2 ∧
        manifoldTimePrimitive Γ p.1 p.2 (Z i p.2)=0) := by
    intro i p hp ha
    rcases hface i p hp ha with hz | ⟨hm,hz⟩
    · exact Or.inl (manifoldTimePrimitive_stationary hz p.1)
    · exact Or.inr ⟨hm,manifoldTimePrimitive_eval_constant hΓ hz p.1⟩
  have hΩ := manifoldExteriorOneForm_path_smooth hΓ
  have hα := manifoldTimePrimitive_smooth hΓ
  have hc := manifoldExteriorOneForm_path_closed hΓ
  have ht := manifoldExteriorOneForm_path_time hΓ
  obtain ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hC,hfix,hpres,hpull⟩ := manifold_relative_sublevel_moser
    (Ω := fun s => manifoldExteriorOneForm (Γ s)) (α := manifoldTimePrimitive Γ)
    hΩ hα μ hμ a c hac hD hU hDU hinv
    (fun p _ v w => manifoldExteriorOneForm_skew (Γ p.1) p.2 v w)
    (fun t b y hy _ u v w => hc t b y hy u v w)
    (fun t b y hy _ v w => ht t b y hy v w) Z hf
  refine ⟨Φ,Ψ,hΦ,hΨ,h0,hi,hC,?_,hpres,hpull⟩
  intro x hx t
  exact hfix x (fun s => manifoldTimePrimitive_stationary hx s) t

end

end PackingSufficiencySupport.Hamiltonian
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PackingSufficiencySupport.Hamiltonian.manifold_exact_sublevel_moser_bp240_oai.{u_1, u_2, u_3} := @OAI.PackingSufficiencySupport.Hamiltonian.manifold_exact_sublevel_moser_bp240_oai.{u_1, u_2, u_3}
