-- Prove2me | solution 1 for OAI.ThreeTorus.exact_neutral_circle_spectral_estimate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T12:06:03.434584+00:00
-- url     : https://prove2.me/submissions/dc38872f-865b-4d50-873a-b6e17895d88d

import Mathlib
import Definitions.Def_OAIQ13Tt000
import Theorems.Thm_OAI_ThreeTorus_exact_passage_circle_spectral_limit

section
-- module Solutions.OAIQ13_TT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual Fourier passage coefficients, branch Jacobians, rounding removal, and integrated stationary mass. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

namespace ThreeTorus

lemma continuous_fourierCoeff_param {Ω : Type*} [TopologicalSpace Ω]
    [FirstCountableTopology Ω] [LocallyCompactSpace Ω]
    {f : Ω → UnitAddCircle → ℂ} (hf : Continuous f.uncurry) (j : ℤ) :
    Continuous (fun a => fourierCoeff (f a) j) := by
  have hh : Continuous (fun p : Ω × UnitAddCircle => fourier (-j) p.2*f p.1 p.2) :=
    ((fourier (-j)).continuous.comp continuous_snd).mul hf
  simpa only [fourierCoeff,smul_eq_mul,setIntegral_univ] using
    (continuous_parametric_integral_of_continuous (μ := AddCircle.haarAddCircle)
      (f := fun a θ => fourier (-j) θ*f a θ) hh isCompact_univ)

lemma continuous_passageFourierInput {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) :
    Continuous (passageFourierInput m H A).uncurry := by
  exact (hA.comp continuous_swap).mul ((fourier m).continuous.comp (hH.comp continuous_snd))

lemma continuous_exactPassageCoeff {m : ℤ} {H : UnitAddCircle → UnitAddCircle}
    {A : UnitAddCircle × UnitAddCircle → ℂ} (hH : Continuous H) (hA : Continuous A) (j : ℤ) :
    Continuous (exactPassageCoeff m H A j) :=
  continuous_fourierCoeff_param (continuous_passageFourierInput hH hA) j

end ThreeTorus

namespace ThreeTorus

open Function

lemma branchDensity_on {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hg : ∀ x ∈ I, g (J x) = x) {x : ℝ} (hx : x ∈ I) :
    branchDensity I J g D q (J x) = q x/|D x| := by
  simp only [branchDensity,indicator_of_mem (mem_image_of_mem J hx),hg x hx]

lemma contDiffAt_invFunOn_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hinj : InjOn J I) {x d : ℝ} (hx : x ∈ I)
    (hd : HasDerivAt J d x) (hd0 : d ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (invFunOn J I) (J x) := by
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hd.hasFDerivAt_equiv hd0) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hd.hasFDerivAt_equiv hd0) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hi : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) e.symm (J x) := by
    apply e.contDiffAt_symm_deriv hd0 hyt
    · simpa only [he,hix] using hd
    · simpa only [he,hix] using hJ.contDiffAt (x := x)
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply hi.continuousAt.eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  apply hi.congr_of_eventuallyEq
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  have hr : J (e.symm y) = y := by simpa only [he] using e.right_inv hy
  have hp := invFunOn_pos (show y ∈ J '' I from ⟨e.symm y,hyI,hr⟩)
  exact hinj hp.1 hyI (hp.2.trans hr.symm)

lemma isOpen_image_of_deriv_ne_zero {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J)
    (hIo : IsOpen I) (hd : ∀ x ∈ I, deriv J x ≠ 0) : IsOpen (J '' I) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x,hx,rfl⟩
  have hdx := (hJ.differentiable (by simp) x).hasDerivAt
  let e := hJ.contDiffAt.toOpenPartialHomeomorph J (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have he : (e : ℝ → ℝ) = J := rfl
  have hxs : x ∈ e.source := hJ.contDiffAt.mem_toOpenPartialHomeomorph_source
    (hdx.hasFDerivAt_equiv (hd x hx)) (by simp)
  have hyt : J x ∈ e.target := by simpa only [he] using e.map_source hxs
  have hix : e.symm (J x) = x := by simpa only [he] using e.left_inv hxs
  have hnear : ∀ᶠ y in 𝓝 (J x), e.symm y ∈ I := by
    apply (e.continuousAt_symm hyt).eventually
    change I ∈ 𝓝 (e.symm (J x))
    rw [hix]
    exact hIo.mem_nhds hx
  filter_upwards [e.open_target.mem_nhds hyt,hnear] with y hy hyI
  exact ⟨e.symm y,hyI,by simpa only [he] using e.right_inv hy⟩

lemma branchFamily_congr_branch {Ω : Type*} {C I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × Ω → ℝ}
    (hIC : I ⊆ C) (hinj : InjOn J C) (hs : support F ⊆ I ×ˢ univ) :
    branchFamily C J F = branchFamily I J F := by
  classical
  funext p
  have him : J '' I ⊆ J '' C := image_mono hIC
  by_cases hp : p.1 ∈ J '' C
  · have hc := invFunOn_pos hp
    by_cases hpi : p.1 ∈ J '' I
    · have hi := invFunOn_pos hpi
      have hinv : invFunOn J C p.1 = invFunOn J I p.1 :=
        hinj hc.1 (hIC hi.1) (hc.2.trans hi.2.symm)
      simp [branchFamily,hp,hpi,hinv]
    · have hz : F (invFunOn J C p.1,p.2) = 0 := by
        by_contra hn
        exact hpi ⟨_, (hs hn).1, hc.2⟩
      simp [branchFamily,hp,hpi,hz]
  · have hpi : p.1 ∉ J '' I := fun h => hp (him h)
    simp [branchFamily,hp,hpi]

open scoped NNReal

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_PassageDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unfolded and folded retained densities, branch kernels, residue sampling, and spectral limits. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace ThreeTorus

lemma integrable_circleDensityLift {q : UnitAddCircle → ℝ}
    (hq : Integrable q AddCircle.haarAddCircle) (o : ℝ) :
    Integrable (circleDensityLift o q) := by
  have hmp : MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ioc o (o+1))) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 o
  have hi : IntegrableOn (fun x : ℝ => q (x : UnitAddCircle)) (Ioc o (o+1)) :=
    (hmp.integrable_comp hq.aestronglyMeasurable).2 hq
  exact hi.integrable_indicator measurableSet_Ioc

lemma integrable_branchDensity {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : IntegrableOn q I) : Integrable (branchDensity I J g D q) := by
  have he : IntegrableOn (branchDensity I J g D q) (J '' I) := by
    rw [integrableOn_image_iff_integrableOn_abs_deriv_smul hI hJ hinj]
    apply hq.congr (ae_restrict_of_forall_mem hI (fun x hx => ?_))
    rw [smul_eq_mul,branchDensity_on hg hx]
    field_simp [abs_ne_zero.mpr (hD x hx)]
  have hs : (J '' I).indicator (branchDensity I J g D q) = branchDensity I J g D q := by
    funext y
    by_cases hy : y ∈ J '' I
    · exact indicator_of_mem hy _
    · simp [hy,branchDensity]
  simpa only [hs] using he.integrable_indicator himage

/-- Total variation contracts under the actual temporal-frequency pushforward.
The real L¹ normalization has no factor 1/2. -/
lemma l1_pushforward_contraction {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f : X → ℝ} {g : Y → ℝ} {T : X → Y}
    (hf : Integrable f μ) (hg : Integrable g ν) (hT : Measurable T)
    (hmap : (μ.withDensityᵥ f).map T = ν.withDensityᵥ g) :
    (∫ y, |g y| ∂ν) ≤ ∫ x, |f x| ∂μ := by
  have hv := MeasureTheory.VectorMeasure.variation_map_le (μ := μ.withDensityᵥ f) (φ := T)
  rw [hmap,Measure.variation_withDensityᵥ hg,Measure.variation_withDensityᵥ hf] at hv
  have hh := hv univ
  rw [Measure.map_apply hT MeasurableSet.univ] at hh
  simp only [preimage_univ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ] at hh
  have he (z : ℝ) : ‖z‖ₑ = ENNReal.ofReal |z| := Real.enorm_eq_ofReal_abs z
  simp_rw [he] at hh
  rw [← ofReal_integral_eq_lintegral_ofReal hg.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hf.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _))] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun _ => abs_nonneg _))).mp hh

lemma l1_pushforward_difference {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {f₁ f₂ : X → ℝ} {g₁ g₂ : Y → ℝ} {T : X → Y}
    (hf₁ : Integrable f₁ μ) (hf₂ : Integrable f₂ μ)
    (hg₁ : Integrable g₁ ν) (hg₂ : Integrable g₂ ν) (hT : Measurable T)
    (h₁ : (μ.withDensityᵥ f₁).map T = ν.withDensityᵥ g₁)
    (h₂ : (μ.withDensityᵥ f₂).map T = ν.withDensityᵥ g₂) :
    (∫ y, |g₁ y-g₂ y| ∂ν) ≤ ∫ x, |f₁ x-f₂ x| ∂μ := by
  apply l1_pushforward_contraction (hf₁.sub hf₂) (hg₁.sub hg₂) hT
  rw [withDensityᵥ_sub hf₁ hf₂,withDensityᵥ_sub hg₁ hg₂]
  have he := map_sub (MeasureTheory.VectorMeasure.mapGm T) (μ.withDensityᵥ f₁) (μ.withDensityᵥ f₂)
  change (μ.withDensityᵥ f₁-μ.withDensityᵥ f₂).map T =
    (μ.withDensityᵥ f₁).map T-(μ.withDensityᵥ f₂).map T at he
  rw [he,h₁,h₂]

lemma integrable_scaledBranchKernel {I : Set ℝ} {J g D q : ℝ → ℝ}
    (hq : Integrable (branchDensity I J g D q)) {s : ℝ} (hs : s ≠ 0) :
    Integrable (scaledBranchKernel I J g D q s) :=
  ((integrable_comp_div_iff _ hs).2 hq).const_mul _

lemma integrable_unfoldedModeDensity {I : Set ℝ} {J g D q₀ : ℝ → ℝ}
    (hI : MeasurableSet I) (himage : MeasurableSet (J '' I))
    (hJ : ∀ x ∈ I, HasDerivWithinAt J (D x) I x) (hinj : InjOn J I)
    (hg : ∀ x ∈ I, g (J x) = x) (hD : ∀ x ∈ I, D x ≠ 0)
    (hq : Integrable q₀) {n j : ℝ} (hn : 0 < n) (hj : j ≠ 0) :
    Integrable (unfoldedModeDensity I J g D q₀ n j) := by
  have hi := integrable_scaledBranchKernel
    (integrable_branchDensity hI himage hJ hinj hg hD (hq.const_mul n).integrableOn)
    (div_ne_zero hj hn.ne')
  change Integrable (fun t => scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (n*t-j))
  simpa only [sub_eq_add_neg] using
    (integrable_comp_mul_left_iff (fun x =>
      scaledBranchKernel I J g D (fun a => n*q₀ a) (j/n) (x+ -j)) hn.ne').2
      (hi.comp_add_right (-j))

end ThreeTorus

noncomputable section
open Set Function Filter
open scoped Topology NNReal
namespace ThreeTorus

lemma support_branchKernel_subset {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ} :
    support (branchKernel I J F) ⊆ (fun p : ℝ × ℝ => (J p.1,p.2)) '' tsupport F := by
  rintro ⟨s,a⟩ hh
  have hs : s ∈ J '' I := by
    by_contra hn
    exact hh (by simp [branchKernel,hn])
  have hp := invFunOn_pos hs
  refine ⟨(invFunOn J I s,a),subset_tsupport F ?_,?_⟩
  · intro hz
    exact hh (by simp [branchKernel,hs,hz])
  · simp only [hp.2]

lemma branchKernel_compact {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) : HasCompactSupport (branchKernel I J F) := by
  apply HasCompactSupport.intro (hc.image (by fun_prop : Continuous (fun p : ℝ × ℝ => (J p.1,p.2))))
  intro p hp
  by_contra hn
  exact hp (support_branchKernel_subset hn)

lemma branchKernel_smooth {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (branchKernel I J F) := by
  classical
  let g := invFunOn J I
  let M := (fun p : ℝ × ℝ => (J p.1,p.2)) '' tsupport F
  have hM : IsCompact M := hc.image (by fun_prop)
  have hzero {p : ℝ × ℝ} (hp : p ∉ M) : branchKernel I J F p = 0 :=
    notMem_support.mp (fun hn => hp (support_branchKernel_subset hn))
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := by
    exact hJ.deriv' 
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hp : p ∈ M
  · rcases hp with ⟨⟨x,a⟩,hx,rfl⟩
    have hxI : x ∈ I := (hs hx).1
    have hy : J x ∈ J '' I := mem_image_of_mem J hxI
    have hgi := contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hxI
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hxI)
    have hge : g (J x) = x := by
      exact hinj (invFunOn_pos hy).1 hxI (invFunOn_pos hy).2
    have hin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (g p.1,p.2)) (J x,a) :=
      (hgi.comp (J x,a) contDiffAt_fst).prodMk contDiffAt_snd
    have hDen : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => |deriv J (g p.1)|) (J x,a) := by
      have hh : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × ℝ => deriv J (g p.1)) (J x,a) :=
        hD.contDiffAt.comp (J x,a) (hgi.comp (J x,a) contDiffAt_fst)
      exact (contDiffAt_abs (by simpa only [hge] using hd x hxI)).comp (J x,a) hh
    have hquot : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => F (g p.1,p.2) / |deriv J (g p.1)|) (J x,a) := by
      apply (hF.contDiffAt.comp _ hin).div hDen
      simpa only [hge] using abs_ne_zero.mpr (hd x hxI)
    apply hquot.congr_of_eventuallyEq
    have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 (J x,a), p.1 ∈ J '' I :=
      continuous_fst.continuousAt.eventually ((isOpen_image_of_deriv_ne_zero hJ hIo hd).mem_nhds hy)
    filter_upwards [hnear] with p hp
    simp only [branchKernel,ite_eq_left hp,g]
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [hM.isClosed.isOpen_compl.mem_nhds hp] with q hq
    exact hzero hq

lemma branchKernel_bounds {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : Continuous J) (hc : HasCompactSupport F) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      (∀ s a, A < |s| → branchKernel I J F (s,a) = 0) ∧
      (∀ s a, D < |a| → branchKernel I J F (s,a) = 0) := by
  have hC := branchKernel_compact (I := I) hJ hc
  obtain ⟨R,hR⟩ := hC.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine ⟨max R 0,max R 0,le_max_right _ _,le_max_right _ _,?_,?_⟩
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hab : |s| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_left ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hab.trans (le_max_left _ _))) hs
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hab : |a| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_right ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hab.trans (le_max_left _ _))) hs

lemma affineKernel_eq_zero_s {F : ℝ × ℝ → ℝ} {L β A s y : ℝ}
    (hF : ∀ s a, A < |s| → F (s,a) = 0) (hs : A < |s|) :
    affineKernel F L β s y = 0 := by simp [affineKernel,hF _ _ hs]

lemma affineKernel_eq_zero_y {F : ℝ × ℝ → ℝ} {L β A D s y : ℝ}
    (hL : 0 < L) (_hA : 0 ≤ A) (hD : 0 ≤ D)
    (hFs : ∀ s a, A < |s| → F (s,a) = 0)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0)
    (hy : A*(L*D+|β|) < |y|) : affineKernel F L β s y = 0 := by
  by_cases hs : s = 0
  · simp [affineKernel,hs]
  by_cases hsA : A < |s|
  · exact affineKernel_eq_zero_s hFs hsA
  have hsA' : |s| ≤ A := le_of_not_gt hsA
  have hh : D < |(y/s-β)/L| := by
    by_contra hn
    have hn' := le_of_not_gt hn
    rw [abs_div,abs_of_pos hL,div_le_iff₀ hL] at hn'
    have hb := abs_add_le (y/s-β) β
    rw [sub_add_cancel] at hb
    have hx : |y/s| ≤ L*D+|β| := by linarith
    rw [abs_div,div_le_iff₀ (abs_pos.mpr hs)] at hx
    have hright : (L*D+|β|)*|s| ≤ (L*D+|β|)*A :=
      mul_le_mul_of_nonneg_left hsA' (by positivity)
    nlinarith
  simp [affineKernel,hFa _ _ hh]

lemma affineKernel_smooth {F : ℝ × ℝ → ℝ} {L β ε : ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hε : 0 < ε)
    (hz : ∀ s a, |s| < ε → F (s,a) = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry (affineKernel F L β)) := by
  rw [contDiff_iff_contDiffAt]
  rintro ⟨s,y⟩
  by_cases hs : s = 0
  · have he : ∀ᶠ p : ℝ × ℝ in 𝓝 (s,y), |p.1| < ε := by
      have hc : Continuous (fun p : ℝ × ℝ => |p.1|) := by fun_prop
      apply hc.continuousAt.eventually (gt_mem_nhds ?_)
      simpa [hs] using hε
    apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [he] with p hp
    simp [Function.uncurry,affineKernel,hz _ _ hp]
  · have ha : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => |p.1|) (s,y) := by
      exact (contDiffAt_abs hs).comp (s,y) contDiffAt_fst
    have hin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × ℝ => (p.1,(p.2/p.1-β)/L)) (s,y) := by
      exact contDiffAt_fst.prodMk (((contDiffAt_snd.div contDiffAt_fst hs).sub contDiffAt_const).div_const L)
    by_cases hL : L = 0
    · have he : Function.uncurry (affineKernel F L β) = fun _ => (0:ℝ) := by
        funext p; simp [Function.uncurry,affineKernel,hL]
      rw [he]
      exact contDiffAt_const
    · exact ((ha.mul contDiffAt_const).inv (mul_ne_zero (abs_ne_zero.mpr hs) hL)).mul
        (hF.contDiffAt.comp (s,y) hin)

/-- A compact smooth kernel has a single global Lipschitz bound. -/
lemma compact_smooth_lipschitz {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hc : HasCompactSupport F) : ∃ C : ℝ≥0, LipschitzWith C F := by
  obtain ⟨C,hC⟩ := (hc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    (hF.continuous_fderiv (by simp))
  refine ⟨⟨max C 0, le_max_right _ _⟩, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by simp))
  intro p
  exact (hC p).trans (le_max_left _ _)

end ThreeTorus
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace ThreeTorus

private lemma mem_samplingWindow {x : ℝ} {M : ℕ} {j : ℤ}
    (hj : |x-j| ≤ M) : j ∈ samplingWindow x M := by
  have hf := Int.floor_le x
  have hf' := Int.lt_floor_add_one x
  have ha := abs_le.mp hj
  simp only [samplingWindow, Finset.mem_Icc]
  constructor
  · have : (⌊x⌋:ℝ)-(M:ℝ)-1 ≤ j := by linarith
    exact_mod_cast this
  · have : (j:ℝ) ≤ (⌊x⌋:ℝ)+(M:ℝ)+1 := by linarith
    exact_mod_cast this

end ThreeTorus

namespace ThreeTorus

lemma fineResidueKernel_eq_zero {K : ℝ → ℝ → ℝ} {A t : ℝ}
    (hKs : ∀ s y, A < |s| → K s y = 0) (ht : A < |t|) (P n : ℕ) (h : ℤ) :
    fineResidueKernel K P h n t = 0 := by
  unfold fineResidueKernel
  simp only [hKs _ _ ht,tsum_zero]

end ThreeTorus

namespace ThreeTorus

private lemma residue_abs_bound {P : ℕ} (hP : 0 < P) (h k : ℤ) :
    |(k:ℝ)| ≤ |(h:ℝ)+k*P|+|(h:ℝ)| := by
  have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hP
  calc
    _ ≤ |(k:ℝ)| * P := by nlinarith [abs_nonneg (k:ℝ)]
    _ = |(h:ℝ)+k*P-h| := by rw [show (h:ℝ)+k*P-h = k*P by ring,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ P from Nat.cast_nonneg P)]
    _ ≤ _ := abs_sub _ _

lemma continuous_fineResidueKernel {K : ℝ → ℝ → ℝ} {A : ℝ} {M n P : ℕ} (h : ℤ)
    (hK : Continuous (fun p : ℝ × ℝ => K p.1 p.2))
    (hKs : ∀ s y, A < |s| → K s y = 0)
    (hKy : ∀ s y, (M:ℝ) < |y| → K s y = 0) (hP : 0 < P) :
    Continuous (fineResidueKernel K P h n) := by
  classical
  obtain ⟨B,hB⟩ := exists_nat_gt ((n:ℝ)*A+M+|(h:ℝ)|)
  let S := samplingWindow 0 B
  have he (t : ℝ) : fineResidueKernel K P h n t =
      ∑ k ∈ S, K t ((n:ℝ)*t-h-k*P) := by
    apply tsum_eq_sum
    intro k hk
    by_cases hs : A < |t|
    · exact hKs _ _ hs
    apply hKy
    by_contra hh
    have ha : |(h:ℝ)+k*P| ≤ (n:ℝ)*A+M := by
      calc
        _ = |(n:ℝ)*t-((n:ℝ)*t-h-k*P)| := by congr 1; ring
        _ ≤ |(n:ℝ)*t|+|(n:ℝ)*t-h-k*P| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg n)]
          exact add_le_add (mul_le_mul_of_nonneg_left (not_lt.mp hs) (Nat.cast_nonneg n)) (not_lt.mp hh)
    have hk' : |(k:ℝ)| < B := lt_of_le_of_lt (residue_abs_bound hP h k) (by linarith)
    exact hk (mem_samplingWindow (by simpa only [zero_sub,abs_neg] using hk'.le))
  rw [show fineResidueKernel K P h n = fun t => ∑ k ∈ S, K t ((n:ℝ)*t-h-k*P) from funext he]
  apply continuous_finsetSum
  intro k _
  exact hK.comp (show Continuous (fun t : ℝ => (t, (n:ℝ)*t-h-k*P)) by fun_prop)

end ThreeTorus

namespace ThreeTorus

lemma passageBranchKernel_formula (I : Set ℝ) (J : ℝ → ℝ) (F : ℝ × ℝ → ℝ) (s y : ℝ) :
    passageBranchKernel I J F s y = |s|⁻¹*branchKernel I J F (y/s,s) := by
  simp [passageBranchKernel,affineKernel]

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_family_of_branch {Ω : Type*} {C I : Set ℝ}
    {J : ℝ → ℝ} {A : Ω → ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C) (hs : ∀ a, support (A a) ⊆ I) :
    (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily I J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
  have he (C : Set ℝ) :
      (fun p : ℝ × Ω => stationaryWeight C J (A p.2) p.1) =
      branchFamily C J (fun p : ℝ × Ω => ‖A p.2 p.1‖^2) := by
    funext p
    simp only [stationaryWeight,branchDensity,branchFamily]
    split_ifs with h <;> simp [h]
  rw [he]
  apply branchFamily_congr_branch hIC hi
  intro p hp
  refine ⟨hs p.2 ?_,mem_univ _⟩
  intro hz
  apply hp
  simp [hz]

/-- Smoothness of the actual old-frequency Jacobian, with a compactly
supported real lift of the old amplitude (including the new good-arc cutoff).
Both positive and negative angular indices are allowed by the injective branch. -/
lemma stationaryWeight_smooth_lift {C I : Set ℝ} {J : ℝ → ℝ} {B : ℝ × ℝ → ℂ}
    (hIC : I ⊆ C) (hi : InjOn J C)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B) (hc : HasCompactSupport B)
    (hs : tsupport B ⊆ I ×ˢ univ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => stationaryWeight C J (fun x => B (x,p.2)) p.1) ∧
    HasCompactSupport (fun p : ℝ × ℝ => stationaryWeight C J (fun x => B (x,p.2)) p.1) := by
  let F : ℝ × ℝ → ℝ := fun p => ‖B p‖^2
  have hFt : tsupport F ⊆ tsupport B := by
    apply closure_mono
    intro p hp hz
    exact hp (by simp [F,show B p = 0 from hz])
  have hFc : HasCompactSupport F := hc.of_isClosed_subset (isClosed_tsupport F) hFt
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F := hB.norm_sq (𝕜 := ℂ)
  have hA (a : ℝ) : support (fun x => B (x,a)) ⊆ I := by
    intro x hx
    exact (hs (subset_tsupport B hx)).1
  have he := stationaryWeight_family_of_branch (A := fun a x => B (x,a)) hIC hi hA
  rw [he]
  change ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (branchKernel I J F) ∧
    HasCompactSupport (branchKernel I J F)
  exact ⟨branchKernel_smooth hJ hIo (hi.mono hIC) hd hF hFc (hFt.trans hs),
    branchKernel_compact hJ.continuous hFc⟩

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma retainedCircleWeight_integrable {ψ : UnitAddCircle → ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (n : ℕ) (j : ℤ) :
    Integrable (retainedCircleWeight ψ χ c n j) AddCircle.haarAddCircle := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
    ((hc n j).norm.pow 2)

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma scaled_speed_good_branch {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hd : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x) :
    InjOn (fun x => (m:ℝ)*V x) (Icc (l-R) (u+R)) ∧
      ∀ x ∈ Ioo (l-R) (u+R), deriv (fun x => (m:ℝ)*V x) x ≠ 0 := by
  have hsub : Icc (l-R) (u+R) ⊆ Icc (l-2*R) (u+2*R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hi : InjOn V (Icc (l-R) (u+R)) :=
    (strictMonoOn_of_deriv_pos (convex_Icc _ _) hV.continuous.continuousOn
      (fun x hx => hd x (hsub (interior_subset hx)))).injOn
  have hm' : (m:ℝ) ≠ 0 := by exact_mod_cast hm
  refine ⟨?_,?_⟩
  · intro x hx y hy he
    exact hi hx hy (mul_left_cancel₀ hm' he)
  · intro x hx
    rw [deriv_const_mul _ (hV.differentiable (by simp) x)]
    exact mul_ne_zero hm' (hd x (hsub (Ioo_subset_Icc_self hx))).ne'

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

lemma stationaryWeight_mul (C : Set ℝ) (J : ℝ → ℝ) (A : ℝ → ℂ) (c : ℂ) (s : ℝ) :
    stationaryWeight C J (fun x => c*A x) s = ‖c‖^2*stationaryWeight C J A s := by
  classical
  unfold stationaryWeight branchDensity
  simp only [Set.indicator_apply]
  split_ifs <;> simp [mul_pow,mul_div_assoc]

lemma stationaryCutoffLift_eq {C : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ} :
    stationaryCutoffLift C J A ψ = fun p : ℝ × ℝ =>
      stationaryWeight C J (fun x => (ψ p.1 : ℂ)*A (x,p.1)) p.2 := by
  funext p
  rw [stationaryWeight_mul]
  simp [stationaryCutoffLift,Complex.norm_real,Real.norm_eq_abs,sq_abs]

lemma cutoff_amplitude_regular {K : Set ℝ} {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) (hK : IsCompact K)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ∧
      HasCompactSupport (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ∧
      tsupport (fun p : ℝ × ℝ => (ψ p.2 : ℂ)*A p) ⊆ K ×ˢ tsupport ψ := by
  let B : ℝ × ℝ → ℂ := fun p => (ψ p.2 : ℂ)*A p
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B :=
    (Complex.ofRealCLM.contDiff.comp (hψ.comp contDiff_snd)).mul hA
  have hsB : tsupport B ⊆ K ×ˢ tsupport ψ := by
    apply closure_minimal _ (hK.isClosed.prod (isClosed_tsupport ψ))
    intro p hp
    have ha : A p ≠ 0 := fun hz => hp (by simp [B,hz])
    have hψn : ψ p.2 ≠ 0 := fun hz => hp (by simp [B,hz])
    exact ⟨hKA p ha,subset_tsupport ψ hψn⟩
  have hcB : HasCompactSupport B :=
    (hK.prod hcψ).of_isClosed_subset (isClosed_tsupport B) hsB
  exact ⟨hB,hcB,hsB⟩

lemma stationaryCutoffLift_regular {C I K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hIC : I ⊆ C) (hi : InjOn J C)
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A)
    (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) (hK : IsCompact K) (hKI : K ⊆ I)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (hcψ : HasCompactSupport ψ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (stationaryCutoffLift C J A ψ) ∧
      HasCompactSupport (stationaryCutoffLift C J A ψ) := by
  let B : ℝ × ℝ → ℂ := fun p => (ψ p.2 : ℂ)*A p
  obtain ⟨hB,hcB,hsB⟩ := cutoff_amplitude_regular hA hKA hK hψ hcψ
  have hsBI : tsupport B ⊆ I ×ˢ univ := fun p hp => ⟨hKI (hsB hp).1,mem_univ _⟩
  have h := stationaryWeight_smooth_lift (C := C) (I := I) (J := J) (B := B)
    hIC hi hJ hIo hd hB hcB hsBI
  let G : ℝ × ℝ → ℝ := fun p => stationaryWeight C J (fun x => B (x,p.2)) p.1
  have hswap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Prod.swap : ℝ × ℝ → ℝ × ℝ) :=
    contDiff_snd.prodMk contDiff_fst
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G ∘ Prod.swap) := h.1.comp hswap
  have hc : HasCompactSupport (G ∘ Prod.swap) :=
    h.2.comp_homeomorph (Homeomorph.prodComm ℝ ℝ)
  have he : stationaryCutoffLift C J A ψ = G ∘ Prod.swap := stationaryCutoffLift_eq
  rw [he]
  exact ⟨hs,hc⟩

lemma stationaryWeight_support_subset {C K : Set ℝ} {J : ℝ → ℝ} {A : ℝ → ℂ}
    (hA : support A ⊆ K) : support (stationaryWeight C J A) ⊆ J '' K := by
  classical
  intro s hs
  have hsC : s ∈ J '' C := by
    by_contra hn
    exact hs (by simp [stationaryWeight,branchDensity,hn])
  have hp := invFunOn_pos hsC
  refine ⟨invFunOn J C s,hA ?_,hp.2⟩
  intro hz
  exact hs (by simp [stationaryWeight,branchDensity,hsC,show A (invFunOn J C s) = 0 from hz])

lemma stationaryCutoffLift_support {C K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hJ : Continuous J) (hK : IsCompact K) (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K) :
    tsupport (stationaryCutoffLift C J A ψ) ⊆ tsupport ψ ×ˢ (J '' K) := by
  apply closure_minimal _ ((isClosed_tsupport ψ).prod (hK.image hJ).isClosed)
  intro p hp
  have hψn : ψ p.1 ≠ 0 := fun hz => hp (by simp [stationaryCutoffLift,hz])
  have hWn : stationaryWeight C J (fun x => A (x,p.1)) p.2 ≠ 0 :=
    fun hz => hp (by simp [stationaryCutoffLift,hz])
  exact ⟨subset_tsupport ψ hψn,
    stationaryWeight_support_subset (fun x hx => hKA (x,p.1) hx) hWn⟩

lemma stationaryCutoffLift_zero_near_zero {C K : Set ℝ} {J : ℝ → ℝ}
    {A : ℝ × ℝ → ℂ} {ψ : ℝ → ℝ}
    (hJ : Continuous J) (hK : IsCompact K) (hKA : ∀ p, A p ≠ 0 → p.1 ∈ K)
    (h0 : 0 ∉ J '' K) :
    ∃ ε > 0, ∀ a s, |s| < ε → stationaryCutoffLift C J A ψ (a,s) = 0 := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ((hK.image hJ).isClosed.isOpen_compl.mem_nhds h0)
  refine ⟨ε,hε,?_⟩
  intro a s hs
  by_contra hh
  have hh' := stationaryCutoffLift_support hJ hK hKA (subset_tsupport _ hh)
  exact hball (by simpa [Metric.mem_ball,Real.dist_eq] using hs) hh'.2

end ThreeTorus

namespace ThreeTorus
open Function Set MeasureTheory Filter
open scoped Topology

/-- The cutoff old-frequency Jacobian used in the Passage Lemma has all
required regularity, including the frequency gap. These conclusions are
derived from the actual smooth amplitude and compact cutoffs. -/
lemma exact_cutoff_weight_regular
    {V : ℝ → ℝ} {m : ℤ} {l u R : ℝ} {A₀ : UnitAddCircle → ℝ → ℂ} {ψ₀ : ℝ → ℝ}
    (hm : m ≠ 0) (hR : 0 < R)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Icc l u)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧ HasCompactSupport F ∧
      ∃ ε > 0, ∀ a s, |s| < ε → F (a,s) = 0 := by
  dsimp only
  have hb := scaled_speed_good_branch hm hR hV hdV
  have hKI : Icc l u ⊆ Ioo (l-R) (u+R) := by
    intro x hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hKA : ∀ p : ℝ × ℝ, A₀ (p.2 : UnitAddCircle) p.1 ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => hsupp _ hp
  have h := stationaryCutoffLift_regular Ioo_subset_Icc_self hb.1 (contDiff_const.mul hV)
    isOpen_Ioo hb.2 hAr hKA isCompact_Icc hKI hψ₀ hcψ₀
  exact ⟨h.1,h.2,stationaryCutoffLift_zero_near_zero
    (continuous_const.mul hV.continuous) isCompact_Icc hKA h0⟩

end ThreeTorus

noncomputable section
open MeasureTheory Set Function
open scoped Topology ENNReal
namespace ThreeTorus

lemma measurable_periodizedReal {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (periodizedReal q) := by
  exact Measurable.tsum (fun k => hq.comp (measurable_id.add_const (k:ℝ)))

lemma measurable_foldCircleDensity {q : ℝ → ℝ} (hq : Measurable q) :
    Measurable (foldCircleDensity q) := by
  exact ((measurable_periodizedReal hq).comp measurable_subtype_coe).comp
    (AddCircle.measurableEquivIoc 1 0).measurable

lemma foldCircleDensity_coe {q : ℝ → ℝ} {x : ℝ} (hx : x ∈ Ioc 0 1) :
    foldCircleDensity q (x : UnitAddCircle) = periodizedReal q x := by
  exact AddCircle.liftIoc_coe_apply (by simpa using hx)

lemma integral_real_eq_lattice (q : ℝ → ℝ) (hq : Integrable q) :
    (∫ x, q x) = ∑' k : ℤ, ∫ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).integral_eq_tsum'' q hq
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma lintegral_real_eq_lattice (q : ℝ → ℝ≥0∞) :
    (∫⁻ x, q x) = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, q (x+k) := by
  have h := (isAddFundamentalDomain_Ioc (by norm_num : (0:ℝ)<1) 0).lintegral_eq_tsum'' q
  rw [← intUnitEquiv.tsum_eq] at h
  have he (k : ℤ) (x : ℝ) : intUnitEquiv k +ᵥ x = x+(k:ℝ) := by
    change (k • (1:ℝ))+x = x+(k:ℝ)
    simp [add_comm]
  simpa only [he,zero_add] using h

lemma integrableOn_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    IntegrableOn (periodizedReal q) (Ioc 0 1) := by
  refine ⟨(measurable_periodizedReal hm).aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  calc
    (∫⁻ x in Ioc (0:ℝ) 1, ‖periodizedReal q x‖ₑ) ≤
        ∫⁻ x in Ioc (0:ℝ) 1, ∑' k : ℤ, ‖q (x+k)‖ₑ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' k : ℤ, ∫⁻ x in Ioc (0:ℝ) 1, ‖q (x+k)‖ₑ :=
      lintegral_tsum (fun k => (hm.comp (measurable_id.add_const (k:ℝ))).enorm.aemeasurable)
    _ = ∫⁻ x, ‖q x‖ₑ := (lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)).symm
    _ < ∞ := hq.hasFiniteIntegral

lemma integral_periodizedReal {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ x in Ioc (0:ℝ) 1, periodizedReal q x) = ∫ x, q x := by
  change (∫ x in Ioc (0:ℝ) 1, ∑' k : ℤ, q (x+k)) = ∫ x, q x
  rw [integral_tsum]
  · exact (integral_real_eq_lattice q hq).symm
  · exact fun k => (hm.comp (measurable_id.add_const (k:ℝ))).aestronglyMeasurable
  · rw [← lintegral_real_eq_lattice (fun x => ‖q x‖ₑ)]
    exact hq.hasFiniteIntegral.ne

lemma integrable_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    Integrable (foldCircleDensity q) AddCircle.haarAddCircle := by
  have hp : MeasurePreserving (fun x : ℝ => (x:UnitAddCircle))
      (volume.restrict (Ioc (0:ℝ) 1)) AddCircle.haarAddCircle := by
    simpa [AddCircle.volume_eq_smul_haarAddCircle] using AddCircle.measurePreserving_mk 1 0
  apply (hp.integrable_comp (measurable_foldCircleDensity hm).aestronglyMeasurable).1
  exact (integrableOn_periodizedReal hm hq).congr
    (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => (foldCircleDensity_coe hx).symm))

lemma integral_foldCircleDensity {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    (∫ a, foldCircleDensity q a ∂AddCircle.haarAddCircle) = ∫ x, q x := by
  have he := AddCircle.integral_preimage 1 0 (foldCircleDensity q)
  simp only [zero_add,AddCircle.volume_eq_smul_haarAddCircle,ENNReal.ofReal_one,
    one_smul] at he
  rw [← he]
  exact (setIntegral_congr_fun measurableSet_Ioc (fun x hx => foldCircleDensity_coe hx)).trans
    (integral_periodizedReal hm hq)

lemma quotient_add_int (x : ℝ) (k : ℤ) : ((x+k : ℝ):UnitAddCircle) = (x:UnitAddCircle) := by
  have h : ((k:ℝ):UnitAddCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).2 ⟨k,by simp⟩
  rw [AddCircle.coe_add,h,add_zero]

lemma foldCircleDensity_indicator (q : ℝ → ℝ) (s : Set UnitAddCircle) :
    foldCircleDensity (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) =
      s.indicator (foldCircleDensity q) := by
  classical
  funext a
  let x : ℝ := (AddCircle.equivIoc 1 0 a).1
  have hx : x ∈ Ioc (0:ℝ) 1 := by simpa using (AddCircle.equivIoc 1 0 a).2
  have ha : (x:UnitAddCircle) = a := (AddCircle.equivIoc 1 0).symm_apply_apply a
  rw [← ha]
  by_cases hs : (x:UnitAddCircle) ∈ s
  · simp only [indicator_of_mem hs,foldCircleDensity_coe hx,periodizedReal]
    apply tsum_congr
    intro k
    exact indicator_of_mem (by simpa only [mem_preimage,quotient_add_int] using hs) q
  · simp only [indicator_of_notMem hs,foldCircleDensity_coe hx,periodizedReal]
    have hz (k : ℤ) : (((fun x : ℝ => (x:UnitAddCircle)) ⁻¹' s).indicator q) (x+k) = 0 :=
      indicator_of_notMem (by simpa only [mem_preimage,quotient_add_int] using hs) q
    simp only [hz,tsum_zero]

/-- Folding is exactly pushforward under the quotient, not a replacement kernel. -/
lemma foldCircleDensity_pushforward {q : ℝ → ℝ} (hm : Measurable q) (hq : Integrable q) :
    ((volume : Measure ℝ).withDensityᵥ q).map (fun x : ℝ => (x:UnitAddCircle)) =
      AddCircle.haarAddCircle.withDensityᵥ (foldCircleDensity q) := by
  ext s hs
  rw [VectorMeasure.map_apply _ AddCircle.measurable_mk' hs,
    withDensityᵥ_apply hq (AddCircle.measurable_mk' hs),
    withDensityᵥ_apply (integrable_foldCircleDensity hm hq) hs,
    ← integral_indicator (AddCircle.measurable_mk' hs),← integral_indicator hs]
  rw [← foldCircleDensity_indicator]
  exact (integral_foldCircleDensity (hm.indicator (AddCircle.measurable_mk' hs))
    (hq.indicator (AddCircle.measurable_mk' hs))).symm

lemma foldCircleDensity_l1_difference {q r : ℝ → ℝ}
    (hqm : Measurable q) (hqi : Integrable q) (hrm : Measurable r) (hri : Integrable r) :
    (∫ a, |foldCircleDensity q a-foldCircleDensity r a| ∂AddCircle.haarAddCircle) ≤
      ∫ x, |q x-r x| := by
  exact l1_pushforward_difference hqi hri (integrable_foldCircleDensity hqm hqi)
    (integrable_foldCircleDensity hrm hri) AddCircle.measurable_mk'
    (foldCircleDensity_pushforward hqm hqi) (foldCircleDensity_pushforward hrm hri)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma measurable_branchDensity_smooth {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) :
    Measurable (branchDensity I J (invFunOn J I) (deriv J) q) := by
  classical
  let S := J '' I
  let g := S.piecewise (invFunOn J I) (fun _ => 0)
  have hS : IsOpen S := isOpen_image_of_deriv_ne_zero hJ hIo hd
  have hgi : ContinuousOn (invFunOn J I) S := by
    rintro y ⟨x,hx,rfl⟩
    exact (contDiffAt_invFunOn_of_deriv_ne_zero hJ hIo hinj hx
      ((hJ.differentiable (by simp) x).hasDerivAt) (hd x hx)).continuousAt.continuousWithinAt
  have hg : Measurable g := hgi.measurable_piecewise continuous_const.continuousOn hS.measurableSet
  have he : branchDensity I J (invFunOn J I) (deriv J) q =
      S.indicator (fun y => q (g y)/|deriv J (g y)|) := by
    funext y
    by_cases hy : y ∈ S
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp [g,hy]
    · change S.indicator (fun y => q (invFunOn J I y)/|deriv J (invFunOn J I y)|) y = _
      simp only [indicator_of_notMem hy]
  rw [he]
  have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv J) := hJ.deriv'
  exact ((hq.comp hg).div ((hD.continuous.measurable.comp hg).abs)).indicator hS.measurableSet

lemma measurable_circleDensityLift {q : UnitAddCircle → ℝ} (hq : Measurable q) (o : ℝ) :
    Measurable (circleDensityLift o q) :=
  (hq.comp AddCircle.measurable_mk').indicator measurableSet_Ioc

lemma measurable_unfoldedModeDensity {I : Set ℝ} {J q : ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0) (hq : Measurable q) (n j : ℝ) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J) q n j) := by
  have hm := measurable_branchDensity_smooth hJ hIo hinj hd (hq.const_mul n)
  unfold unfoldedModeDensity scaledBranchKernel
  exact (hm.comp ((measurable_const.mul measurable_id).sub_const j |>.div_const (j/n))).const_mul |j/n|⁻¹

lemma passageBranchKernel_regular {J : ℝ → ℝ} {I : Set ℝ} {F : ℝ × ℝ → ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hc : HasCompactSupport F)
    (hs : tsupport F ⊆ I ×ˢ univ) {ε : ℝ} (hε : 0 < ε)
    (hz : ∀ a s, |s| < ε → F (a,s) = 0) :
    Continuous (passageBranchKernel I J F).uncurry ∧
      ∃ A > 0, ∃ M : ℕ,
        (∀ s y, A < |s| → passageBranchKernel I J F s y = 0) ∧
        ∀ s y, (M:ℝ) < |y| → passageBranchKernel I J F s y = 0 := by
  have hSm := branchKernel_smooth hJ hIo hinj hd hF hc hs
  obtain ⟨D,A,hD,hA,hx,ha⟩ := branchKernel_bounds (I := I) hJ.continuous hc
  have hsmooth := affineKernel_smooth (L := (1:ℝ)) (β := (0:ℝ))
    (hSm.comp (contDiff_snd.prodMk contDiff_fst)) hε (show
      ∀ s a, |s| < ε → branchKernel I J F (a,s) = 0 from fun s a hh => by
        simp [branchKernel,hz _ _ hh])
  obtain ⟨M,hM⟩ := exists_nat_ge (A*((1:ℝ)*D+|(0:ℝ)|))
  refine ⟨hsmooth.continuous,max A 1,lt_max_of_lt_right zero_lt_one,M,?_,?_⟩
  · intro s y hh
    exact affineKernel_eq_zero_s (fun s a hh => ha a s hh) (lt_of_le_of_lt (le_max_left _ _) hh)
  · intro s y hy
    exact affineKernel_eq_zero_y (by norm_num) hA hD
      (fun s a hh => ha a s hh) (fun s a hh => hx a s hh) (lt_of_le_of_lt hM hy)

lemma fineResidueKernel_regular {K : ℝ → ℝ → ℝ} {A : ℝ} {M n P : ℕ}
    (hK : Continuous K.uncurry) (_hA : 0 < A)
    (hs : ∀ s y, A < |s| → K s y = 0)
    (hy : ∀ s y, (M:ℝ) < |y| → K s y = 0)
    ( _hn : 0 < n) (hP : 0 < P) (h : ℤ) :
    Continuous (fineResidueKernel K P h n) ∧ Integrable (fineResidueKernel K P h n) := by
  have hc := continuous_fineResidueKernel (n := n) h hK hs hy hP
  refine ⟨hc,hc.integrable_of_hasCompactSupport ?_⟩
  apply HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
  intro t ht
  apply fineResidueKernel_eq_zero hs
  by_contra hh
  exact ht ⟨(abs_le.mp (le_of_not_gt hh)).1,(abs_le.mp (le_of_not_gt hh)).2⟩

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology

lemma retained_unfolded_regular {J : ℝ → ℝ} {I : Set ℝ}
    (hJ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J) (hIo : IsOpen I)
    (hinj : InjOn J I) (hd : ∀ x ∈ I, deriv J x ≠ 0)
    {ψ : UnitAddCircle → ℝ} {χ : ℝ → UnitAddCircle → ℝ}
    {c : ℕ → ℤ → UnitAddCircle → ℂ}
    (hψ : Continuous ψ) (hχ : Continuous χ.uncurry) (hc : ∀ n j, Continuous (c n j))
    (o : ℝ) {n : ℕ} (hn : 0 < n) {j : ℤ} (hj : j ≠ 0) :
    Measurable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) ∧
    Integrable (unfoldedModeDensity I J (invFunOn J I) (deriv J)
      (circleDensityLift o (retainedCircleWeight ψ χ c n j)) n j) := by
  have hq : Continuous (retainedCircleWeight ψ χ c n j) :=
    ((hψ.pow 2).mul ((hχ.comp (continuous_const.prodMk continuous_id)).pow 2)).mul
      ((hc n j).norm.pow 2)
  exact ⟨measurable_unfoldedModeDensity hJ hIo hinj hd
      (measurable_circleDensityLift hq.measurable o) n j,
    integrable_unfoldedModeDensity hIo.measurableSet
      (isOpen_image_of_deriv_ne_zero hJ hIo hd).measurableSet
      (fun x _ => (hJ.differentiable (by simp) x).hasDerivAt.hasDerivWithinAt) hinj
      (fun _ hx => hinj.leftInvOn_invFunOn hx) hd
      (integrable_circleDensityLift (retainedCircleWeight_integrable hψ hχ hc n j) o)
      (by exact_mod_cast hn) (by exact_mod_cast hj)⟩

end ThreeTorus

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_Transmission
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Law averaging and weighted errors, folded packet transmission, and concrete signal-circle comparison. -/

noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology SchwartzMap FourierTransform Real
open scoped Topology
open MeasureTheory Set
open scoped ENNReal Topology
open Set Function Filter
open scoped Topology NNReal
open MeasureTheory Filter Set
open MeasureTheory Set Function
open scoped Topology ENNReal
open scoped Topology BigOperators
open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MeasureTheory Set Filter Asymptotics
open MeasureTheory Set Filter Function

namespace ThreeTorus
open MeasureTheory Set Filter Function
open scoped Topology BigOperators FourierTransform

lemma integral_abs_sub_triangle {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g h : X → ℝ} (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    (∫ x, |f x-h x| ∂μ) ≤ (∫ x, |f x-g x| ∂μ)+(∫ x, |g x-h x| ∂μ) := by
  calc
    _ ≤ ∫ x, |f x-g x|+|g x-h x| ∂μ :=
      integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
        (fun x => abs_sub_le _ _ _)
    _ = _ := integral_add (hf.sub hg).abs (hg.sub hh).abs

end ThreeTorus

end

end OAI
end

section
-- module Solutions.OAIQ13_TT.ThreeTorus_NeutralSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Neutral lattice sampling, retained support, and stationary image separation. -/

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace ThreeTorus

lemma cell_sample_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (a : ℝ) :
    |f a - ∫ x in a..a+1, f x| ≤ ∫ x in a..a+1, |deriv f x| := by
  have hc : Continuous (fun x => |deriv f x|) := (hf.continuous_deriv (by norm_num)).abs
  have hbound (x : ℝ) (hx : x ∈ Icc a (a+1)) :
      |f a-f x| ≤ ∫ t in a..a+1, |deriv f t| := by
    have hFTC := intervalIntegral.integral_deriv_eq_sub
      (fun t _ => hf.differentiable (by norm_num) t)
      ((hf.continuous_deriv (by norm_num)).intervalIntegrable (a := a) (b := x))
    calc
      _ = |∫ t in a..x, deriv f t| := by rw [hFTC, abs_sub_comm]
      _ ≤ ∫ t in a..x, |deriv f t| := by
        simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm hx.1 (f := deriv f)
      _ ≤ ∫ t in a..a+1, |deriv f t| := by
        exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
          (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) (hc.intervalIntegrable _ _)
  calc
    _ = |∫ x in a..a+1, (f a-f x)| := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.continuous.intervalIntegrable _ _)]
      simp
    _ ≤ ∫ x in a..a+1, |f a-f x| := by
      simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (by linarith : a ≤ a+1)
        (f := fun x => f a-f x)
    _ ≤ ∫ _ in a..a+1, (∫ t in a..a+1, |deriv f t|) :=
      intervalIntegral.integral_mono_on (by linarith) ((continuous_const.sub hf.continuous).abs.intervalIntegrable _ _)
        intervalIntegrable_const hbound
    _ = _ := by simp

/-- Arbitrary-offset unit lattice estimate, before scaling to the neutral refresh mesh. -/
lemma lattice_sample_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdi : Integrable (fun x => |deriv f x|)) (a : ℝ) :
    Summable (fun j : ℤ => f (a+j)) ∧
      |(∑' j : ℤ, f (a+j)) - ∫ x, f x| ≤ ∫ x, |deriv f x| := by
  let c (j : ℤ) := ∫ x in (a+j)..(a+j+1), f x
  let b (j : ℤ) := ∫ x in (a+j)..(a+j+1), |deriv f x|
  let e (j : ℤ) := f (a+j)-c j
  have hc : HasSum c (∫ x, f x) := hi.hasSum_intervalIntegral a
  have hb : HasSum b (∫ x, |deriv f x|) := hdi.hasSum_intervalIntegral a
  have heB (j : ℤ) : ‖e j‖ ≤ b j := by
    exact cell_sample_error hf (a+j)
  have he : Summable e := hb.summable.of_norm_bounded heB
  have hid (j : ℤ) : e j+c j = f (a+j) := by dsimp [e,c]; ring
  have hsum : HasSum (fun j : ℤ => f (a+j)) ((∑' j, e j)+(∫ x, f x)) :=
    (he.hasSum.add hc).congr_fun (fun j => (hid j).symm)
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq, add_sub_cancel_right]
  calc
    _ ≤ ∑' j, ‖e j‖ := by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm he.norm
    _ ≤ ∑' j, b j := he.norm.tsum_le_tsum heB hb.summable
    _ = _ := hb.tsum_eq

/-- The mesh version of the arbitrary-offset Riemann estimate in neutral refresh. -/
lemma mesh_sample_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdi : Integrable (fun x => |deriv f x|))
    {h : ℝ} (hh : 0 < h) (a : ℝ) :
    Summable (fun j : ℤ => f (a+h*j)) ∧
      |h*(∑' j : ℤ, f (a+h*j)) - ∫ x, f x| ≤ h*∫ x, |deriv f x| := by
  let g : ℝ → ℝ := fun x => f (h*x)
  have hg : ContDiff ℝ 1 g := hf.comp (contDiff_const.mul contDiff_id)
  have hgi : Integrable g := hi.comp_mul_left' hh.ne'
  have hd (x : ℝ) : deriv g x = deriv f (h*x)*h := by
    simpa only [g, Function.comp_def, mul_one] using (((hf.differentiable (by norm_num) (h*x)).hasDerivAt).comp x
      ((hasDerivAt_id x).const_mul h)).deriv
  have hdgi : Integrable (fun x => |deriv g x|) := by
    simp_rw [hd, abs_mul, abs_of_pos hh]
    exact (hdi.comp_mul_left' hh.ne').mul_const h
  have hid (j : ℤ) : g (a/h+j) = f (a+h*j) := by
    dsimp [g]; congr 1; field_simp
  obtain ⟨hs,hb⟩ := lattice_sample_error hg hgi hdgi (a/h)
  simp_rw [hid] at hs hb
  refine ⟨hs, ?_⟩
  have hgint : (∫ x, g x) = h⁻¹*(∫ x, f x) := by
    exact (Measure.integral_comp_mul_left f h).trans (by rw [abs_of_pos (inv_pos.mpr hh)]; rfl)
  have hdint : (∫ x, |deriv g x|) = ∫ x, |deriv f x| := by
    simp_rw [hd, abs_mul, abs_of_pos hh]
    rw [integral_mul_const, Measure.integral_comp_mul_left (fun x => |deriv f x|) h]
    rw [abs_of_pos (inv_pos.mpr hh)]
    simp only [smul_eq_mul]
    field_simp
  rw [hgint, hdint] at hb
  calc
    _ = |h*((∑' j : ℤ, f (a+h*j)) - h⁻¹*(∫ x, f x))| := by
      congr 1
      rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul]
    _ = h*|(∑' j : ℤ, f (a+h*j)) - h⁻¹*(∫ x, f x)| := by
      rw [abs_mul, abs_of_pos hh]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb hh.le

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

/-- Mesh reversal uses the actual integer negation bijection; negative old
angular indices have the same arbitrary-offset Riemann estimate. -/
lemma signed_mesh_sample_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdi : Integrable (fun x => |deriv f x|))
    {h : ℝ} (hh : h ≠ 0) (a : ℝ) :
    Summable (fun j : ℤ => f (a+h*j)) ∧
      |(|h| *(∑' j : ℤ, f (a+h*j))) - ∫ x, f x| ≤ |h| *∫ x, |deriv f x| := by
  rcases lt_or_gt_of_ne hh with hh | hh
  · obtain ⟨hs,hb⟩ := mesh_sample_error hf hi hdi (h := -h) (by linarith) a
    have he (j : ℤ) : f (a+h*j) = f (a+(-h)*(-j:ℤ)) := by
      push_cast; congr 1; ring
    have ht : (∑' j : ℤ, f (a+h*j)) = ∑' j : ℤ, f (a+(-h)*j) := by
      simp_rw [he]
      exact (Equiv.neg ℤ).tsum_eq (fun j : ℤ => f (a+(-h)*j))
    refine ⟨?_,?_⟩
    · simpa only [Function.comp_def, he] using hs.comp_injective (neg_injective : Injective (Neg.neg : ℤ → ℤ))
    · rw [abs_of_neg hh,ht]
      exact hb
  · simpa only [abs_of_pos hh] using mesh_sample_error hf hi hdi hh a

/-- Exact signed normalization, with arbitrary offset and arbitrary positive
integer residue spacing. This is source (neutral-riemann-error). -/
lemma signed_neutral_residue_error {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hi : Integrable f) (hdi : Integrable (fun x => |deriv f x|))
    {P s L : ℝ} (hP : 0 < P) (hs : s ≠ 0) (hL : 0 < L) (y β : ℝ) :
    Summable (fun j : ℤ => (|s| *L)⁻¹*f (((y+j*P)/s-β)/L)) ∧
      |(∑' j : ℤ, (|s| *L)⁻¹*f (((y+j*P)/s-β)/L))-
          P⁻¹*(∫ a, f a)| ≤ (|s| *L)⁻¹*(∫ a, |deriv f a|) := by
  have hh : P/(s*L) ≠ 0 := div_ne_zero hP.ne' (mul_ne_zero hs hL.ne')
  obtain ⟨hsum,hb⟩ := signed_mesh_sample_error hf hi hdi hh ((y/s-β)/L)
  have hi' (j : ℤ) : (y/s-β)/L+(P/(s*L))*j = ((y+j*P)/s-β)/L := by ring
  simp_rw [hi'] at hsum hb
  have hab : |P/(s*L)| = P/(|s| *L) := by rw [abs_div,abs_mul,abs_of_pos hP,abs_of_pos hL]
  rw [hab] at hb
  refine ⟨hsum.mul_left _,?_⟩
  rw [tsum_mul_left]
  calc
    _ = |P⁻¹*((P/(|s| *L))*(∑' j : ℤ, f (((y+j*P)/s-β)/L)) - ∫ a, f a)| := by
      generalize (∑' j : ℤ, f (((y+j*P)/s-β)/L)) = S
      congr 1; field_simp
    _ = P⁻¹*|(P/(|s| *L))*(∑' j : ℤ, f (((y+j*P)/s-β)/L)) - ∫ a, f a| := by
      rw [abs_mul,abs_of_pos (inv_pos.mpr hP)]
    _ ≤ P⁻¹*((P/(|s| *L))*(∫ a, |deriv f a|)) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

lemma fine_affine_neutral_error {F : ℝ × ℝ → ℝ} {P n : ℕ} {h : ℤ} {L s : ℝ}
    (hP : 0 < P) (hs : s ≠ 0) (hL : 0 < L) (β : ℝ)
    (hF : ContDiff ℝ 1 (fun a => F (s,a)))
    (hi : Integrable (fun a => F (s,a)))
    (hd : Integrable (fun a => |deriv (fun a => F (s,a)) a|)) :
    |fineResidueKernel (affineKernel F L β) P h n s-
      (P:ℝ)⁻¹*(∫ a, F (s,a))| ≤
      (|s| *L)⁻¹*(∫ a, |deriv (fun a => F (s,a)) a|) := by
  have hh := (signed_neutral_residue_error (P := (P:ℝ)) hF hi hd (by exact_mod_cast hP) hs hL
    ((n:ℝ)*s-h) β).2
  have he : fineResidueKernel (affineKernel F L β) P h n s =
      ∑' j : ℤ, (|s| *L)⁻¹*F (s,((((n:ℝ)*s-h)+j*P)/s-β)/L) := by
    unfold fineResidueKernel affineKernel
    have ht := (Equiv.neg ℤ).tsum_eq
      (fun j : ℤ => (|s| *L)⁻¹*F (s,((((n:ℝ)*s-h)+j*P)/s-β)/L))
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    apply tsum_congr
    intro j
    simp only [Equiv.neg_apply,Int.cast_neg]
    congr 3; ring
  rw [he]
  exact hh

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma compact_slice_tsupport {F : ℝ × ℝ → ℝ} {D : ℝ}
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (s : ℝ) :
    tsupport (fun a => F (s,a)) ⊆ Icc (-D) D := by
  apply closure_minimal _ isClosed_Icc
  intro a ha
  by_contra hn
  exact ha (hFa s a (lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using hn)))

lemma compact_slice_support {F : ℝ × ℝ → ℝ} {D : ℝ}
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (s : ℝ) :
    HasCompactSupport (fun a => F (s,a)) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (compact_slice_tsupport hFa s)

lemma compact_slice_derivative_bound {F : ℝ × ℝ → ℝ} {D : ℝ} {C : ℝ≥0}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (hD : 0 ≤ D)
    (hC : LipschitzWith C F) (s : ℝ) :
    Integrable (fun a => F (s,a)) ∧
    Integrable (fun a => |deriv (fun a => F (s,a)) a|) ∧
    (∫ a, |deriv (fun a => F (s,a)) a|) ≤ 2*D*C := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => F (s,a)) :=
    hF.comp ((contDiff_const (c := s)).prodMk contDiff_id)
  have hc := compact_slice_support hFa s
  have hfd : Continuous (deriv (fun a => F (s,a))) := hf.continuous_deriv (by simp)
  have hdi : Integrable (fun a => |deriv (fun a => F (s,a)) a|) :=
    hfd.abs.integrable_of_hasCompactSupport (hc.deriv.comp_left (abs_zero))
  have hl : LipschitzWith C (fun a => F (s,a)) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hC.dist_le_mul (s,a) (s,b)
  refine ⟨hf.continuous.integrable_of_hasCompactSupport hc,hdi,?_⟩
  have hzero (a : ℝ) (ha : a ∉ Icc (-D) D) : deriv (fun a => F (s,a)) a = 0 := by
    by_contra hn
    exact ha (compact_slice_tsupport hFa s (support_deriv_subset hn))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-D) D)
    (f := fun a => |deriv (fun a => F (s,a)) a|) (fun a ha => by rw [hzero a ha,abs_zero])]
  calc
    _ ≤ ∫ _ in Icc (-D) D, (C:ℝ) :=
      setIntegral_mono_on hdi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
        (fun a _ => by simpa only [← Real.norm_eq_abs] using norm_deriv_le_of_lipschitz (x₀ := a) hl)
    _ = _ := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -D ≤ D)]
      simp only [smul_eq_mul]
      ring

lemma compact_slice_integral_continuous {F : ℝ × ℝ → ℝ} {D : ℝ}
    (hF : Continuous F) (hFa : ∀ s a, D < |a| → F (s,a) = 0) :
    Continuous (fun s => ∫ a, F (s,a)) := by
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support (k := Icc (-D) D) isCompact_Icc
  · exact hF.continuousOn
  · intro s a _ ha
    exact hFa s a (lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using ha))

lemma fine_affine_neutral_uniform {F : ℝ × ℝ → ℝ} {P n : ℕ} {h : ℤ}
    {D ε L : ℝ} {C : ℝ≥0}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (hD : 0 ≤ D)
    (hC : LipschitzWith C F) (hε : 0 < ε)
    (hz : ∀ s a, |s| < ε → F (s,a) = 0)
    (hP : 0 < P) (hL : 0 < L) (β s : ℝ) :
    |fineResidueKernel (affineKernel F L β) P h n s-
      (P:ℝ)⁻¹*(∫ a, F (s,a))| ≤ (ε*L)⁻¹*(2*D*C) := by
  by_cases hs : |s| < ε
  · have he : (∫ a, F (s,a)) = 0 := by simp [hz s _ hs]
    have hk : fineResidueKernel (affineKernel F L β) P h n s = 0 := by
      unfold fineResidueKernel affineKernel
      simp [hz s _ hs]
    rw [hk,he,mul_zero,sub_self,abs_zero]
    positivity
  · have hsε : ε ≤ |s| := le_of_not_gt hs
    have hs0 : s ≠ 0 := by intro hh; simp [hh] at hsε; linarith
    obtain ⟨hi,hd,hb⟩ := compact_slice_derivative_bound hF hFa hD hC s
    calc
      _ ≤ (|s| *L)⁻¹*(∫ a, |deriv (fun a => F (s,a)) a|) :=
        fine_affine_neutral_error hP hs0 hL β
          ((hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)) hi hd
      _ ≤ (|s| *L)⁻¹*(2*D*C) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right hsε hL.le)) (by positivity)

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma fine_affine_neutral_l1_error {F : ℝ × ℝ → ℝ} {P n : ℕ} {h : ℤ}
    {A D ε L : ℝ} {C : ℝ≥0}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hFs : ∀ s a, A < |s| → F (s,a) = 0) (hA : 0 ≤ A)
    (hFa : ∀ s a, D < |a| → F (s,a) = 0) (hD : 0 ≤ D)
    (hC : LipschitzWith C F) (hε : 0 < ε)
    (hz : ∀ s a, |s| < ε → F (s,a) = 0)
    (hn : 0 < n) (hP : 0 < P) (hL : 0 < L) (β : ℝ) :
    (∫ s, |fineResidueKernel (affineKernel F L β) P h n s-
      (P:ℝ)⁻¹*(∫ a, F (s,a))|) ≤ (2*A)*((ε*L)⁻¹*(2*D*C)) := by
  obtain ⟨M,hM⟩ := exists_nat_ge (A*(L*D+|β|))
  have hk := fineResidueKernel_regular (h := h) (n := n)
    (affineKernel_smooth (L := L) (β := β) hF hε hz).continuous
    (show 0 < max A 1 from lt_max_of_lt_right zero_lt_one)
    (fun s y hh => affineKernel_eq_zero_s hFs (lt_of_le_of_lt (le_max_left _ _) hh))
    (fun s y hh => affineKernel_eq_zero_y hL hA hD hFs hFa (lt_of_le_of_lt hM hh)) hn hP
  have hZ := compact_slice_integral_continuous hF.continuous hFa
  have hcZ : HasCompactSupport (fun s => ∫ a, F (s,a)) := by
    apply HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
    intro s hs
    have hab : A < |s| := lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using hs)
    simp [hFs s _ hab]
  have hi := (hk.2.sub ((hZ.integrable_of_hasCompactSupport hcZ).const_mul (P:ℝ)⁻¹)).abs
  have hzero (s : ℝ) (hs : s ∉ Icc (-A) A) :
      |fineResidueKernel (affineKernel F L β) P h n s-(P:ℝ)⁻¹*(∫ a, F (s,a))| = 0 := by
    have hab : A < |s| := lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using hs)
    rw [fineResidueKernel_eq_zero (fun s y hh => affineKernel_eq_zero_s hFs hh) hab]
    simp [hFs s _ hab]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-A) A) hzero]
  calc
    _ ≤ ∫ _ in Icc (-A) A, (ε*L)⁻¹*(2*D*C) :=
      setIntegral_mono_on hi.integrableOn (integrableOn_const (by simp)) measurableSet_Icc
        (fun s _ => fine_affine_neutral_uniform hF hFa hD hC hε hz hP hL β s)
    _ = _ := by
      rw [setIntegral_const,Real.volume_real_Icc_of_le (by linarith : -A ≤ A)]
      simp only [smul_eq_mul]
      ring

lemma compact_rect_bounds {F : ℝ × ℝ → ℝ} (hc : HasCompactSupport F) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      (∀ s a, A < |s| → F (s,a) = 0) ∧ (∀ s a, D < |a| → F (s,a) = 0) := by
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0 : ℝ × ℝ)
  refine ⟨max R 0,max R 0,le_max_right _ _,le_max_right _ _,?_,?_⟩
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hh' : |s| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_left ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hh'.trans (le_max_left _ _))) hs
  · intro s a hs
    by_contra hn
    have hh := hR (subset_tsupport _ hn)
    rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def] at hh
    have hh' : |a| ≤ R := by simpa only [Real.norm_eq_abs] using (le_max_right ‖s‖ ‖a‖).trans hh
    exact (not_lt_of_ge (hh'.trans (le_max_left _ _))) hs

/-- Uniform residue equalization for actual compact smooth stationary weight.
One slope is chosen before the passage integer, with all lattice phases,
all residues, and both signs controlled. -/
lemma neutral_fine_l1_bound {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ s a, |s| < ε → F (s,a) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {P n : ℕ}, 0 < P → 0 < n → ∀ h : ℤ, ∀ L : ℝ, 0 < L → ∀ β : ℝ,
      (∫ s, |fineResidueKernel (affineKernel F L β) P h n s-
        (P:ℝ)⁻¹*(∫ a, F (s,a))|) ≤ C/L := by
  obtain ⟨A,D,hA,hD,hFs,hFa⟩ := compact_rect_bounds hcF
  obtain ⟨C,hC⟩ := compact_smooth_lipschitz hF hcF
  refine ⟨(2*A)*(2*D*C)/ε,by positivity,?_⟩
  intro P n hP hn h L hL β
  have hb := fine_affine_neutral_l1_error (h := h) hF hFs hA hFa hD hC hε hz hn hP hL β
  convert hb using 1 <;> first | rfl | ring

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

lemma deriv_affine_on {I : Set ℝ} {J : ℝ → ℝ} {L β : ℝ}
    (hIo : IsOpen I) (he : ∀ a ∈ I, J a = L*a+β) {a : ℝ} (ha : a ∈ I) :
    deriv J a = L := by
  have hev : J =ᶠ[𝓝 a] (fun x => L*x+β) := by
    filter_upwards [hIo.mem_nhds ha] with x hx using he x hx
  rw [hev.deriv_eq]
  simp

/-- The branch is the actual inverse of the affine jitter on the good arc.
Off that image both sides vanish because the old stationary weight is cut off. -/
lemma branchKernel_affine_on {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × ℝ → ℝ} {L β : ℝ}
    (hIo : IsOpen I) (hL : 0 < L) (he : ∀ a ∈ I, J a = L*a+β)
    (hs : tsupport F ⊆ I ×ˢ univ) (y s : ℝ) :
    branchKernel I J F (y,s) = L⁻¹*F ((y-β)/L,s) := by
  classical
  have hinj : InjOn J I := by
    intro a ha b hb hab
    rw [he a ha,he b hb] at hab
    nlinarith
  by_cases hy : y ∈ J '' I
  · obtain ⟨a,ha,rfl⟩ := hy
    have hg := hinj.leftInvOn_invFunOn ha
    have ht : (J a-β)/L = a := by rw [he a ha]; field_simp; ring
    rw [branchKernel,ite_eq_left (mem_image_of_mem J ha),hg,deriv_affine_on hIo he ha,
      abs_of_pos hL,ht]
    ring
  · have ha : (y-β)/L ∉ I := by
      intro hh
      apply hy
      refine ⟨(y-β)/L,hh,?_⟩
      rw [he _ hh]
      field_simp
      ring
    have hz : F ((y-β)/L,s) = 0 := by
      by_contra hn
      exact ha (hs (subset_tsupport _ hn)).1
    rw [branchKernel,ite_eq_right hy,hz,mul_zero]

lemma passageBranchKernel_affine_on {I : Set ℝ} {J : ℝ → ℝ} {F : ℝ × ℝ → ℝ} {L β : ℝ}
    (hIo : IsOpen I) (hL : 0 < L) (he : ∀ a ∈ I, J a = L*a+β)
    (hs : tsupport F ⊆ I ×ˢ univ) :
    passageBranchKernel I J F = affineKernel (F ∘ Prod.swap) L β := by
  funext s y
  rw [passageBranchKernel_formula,branchKernel_affine_on hIo hL he hs]
  simp only [affineKernel,Function.comp_apply,Prod.swap_prod_mk,mul_inv_rev]
  ring

lemma compact_slice_integral_regular {F : ℝ × ℝ → ℝ}
    (hF : Continuous F) (hcF : HasCompactSupport F) :
    Continuous (fun s => ∫ a, F (s,a)) ∧ Integrable (fun s => ∫ a, F (s,a)) := by
  obtain ⟨A,D,_,_,hFs,hFa⟩ := compact_rect_bounds hcF
  have hZ := compact_slice_integral_continuous hF hFa
  refine ⟨hZ,hZ.integrable_of_hasCompactSupport ?_⟩
  apply HasCompactSupport.intro (isCompact_Icc (a := -A) (b := A))
  intro s hs
  have hab : A < |s| := lt_of_not_ge (by simpa only [mem_Icc,← abs_le] using hs)
  simp [hFs s _ hab]

lemma affine_fine_regular {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ s a, |s| < ε → F (s,a) = 0)
    {P n : ℕ} (hP : 0 < P) (hn : 0 < n) (h : ℤ) {L : ℝ} (hL : 0 < L) (β : ℝ) :
    Continuous (fineResidueKernel (affineKernel F L β) P h n) ∧
      Integrable (fineResidueKernel (affineKernel F L β) P h n) := by
  obtain ⟨A,D,hA,hD,hFs,hFa⟩ := compact_rect_bounds hcF
  obtain ⟨M,hM⟩ := exists_nat_ge (A*(L*D+|β|))
  apply fineResidueKernel_regular
    (affineKernel_smooth (L := L) (β := β) hF hε hz).continuous
    (show 0 < max A 1 from lt_max_of_lt_right zero_lt_one)
    (fun s y hh => affineKernel_eq_zero_s hFs (lt_of_le_of_lt (le_max_left _ _) hh))
    (fun s y hh => affineKernel_eq_zero_y hL hA hD hFs hFa (lt_of_le_of_lt hM hh)) hn hP

/-- The neutral equalization estimate on the actual temporal circle, uniformly
in the large preparation integer, residues, offsets and affine good-arc jitter.
The constant is fixed using only the old cut-off stationary weight. -/
lemma neutral_branch_circle_l1_bound {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (hcF : HasCompactSupport F)
    {ε : ℝ} (hε : 0 < ε) (hz : ∀ a s, |s| < ε → F (a,s) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {I : Set ℝ} {J : ℝ → ℝ} {P n : ℕ},
      IsOpen I → tsupport F ⊆ I ×ˢ univ → 0 < P → 0 < n →
      ∀ h : ℤ, ∀ L : ℝ, 0 < L → ∀ β : ℝ, (∀ a ∈ I, J a = L*a+β) →
      (∫ z, |foldCircleDensity (fineResidueKernel (passageBranchKernel I J F) P h n) z-
        foldCircleDensity (fun s => (P:ℝ)⁻¹*(∫ a, F (a,s))) z| ∂AddCircle.haarAddCircle) ≤ C/L := by
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (F ∘ Prod.swap) :=
    hF.comp (contDiff_snd.prodMk contDiff_fst)
  have hc : HasCompactSupport (F ∘ Prod.swap) := hcF.comp_homeomorph (Homeomorph.prodComm ℝ ℝ)
  have hzf : ∀ s a, |s| < ε → (F ∘ Prod.swap) (s,a) = 0 := fun s a hs => hz a s hs
  obtain ⟨C,hC,hb⟩ := neutral_fine_l1_bound hf hc hε hzf
  refine ⟨C,hC,?_⟩
  intro I J P n hIo hsF hP hn h L hL β he
  rw [passageBranchKernel_affine_on hIo hL he hsF]
  have hq := affine_fine_regular hf hc hε hzf hP hn h hL β
  have hr := compact_slice_integral_regular hf.continuous hc
  calc
    _ ≤ ∫ s, |fineResidueKernel (affineKernel (F ∘ Prod.swap) L β) P h n s-
        (P:ℝ)⁻¹*(∫ a, F (a,s))| :=
      foldCircleDensity_l1_difference hq.1.measurable hq.2
        (measurable_const.mul hr.1.measurable) (hr.2.const_mul _)
    _ ≤ _ := hb hP hn h L hL β

end ThreeTorus

namespace ThreeTorus
open MeasureTheory Set Function Filter
open scoped Topology NNReal

/-- The broad slope is chosen after the cutoff weight and before the periodic jitter is fixed;
the final passage integer is only subject to a lower bound. The displayed
reference density is exactly the old cutoff stationary marginal, folded to
the temporal circle and divided by the residue modulus. -/
lemma exact_neutral_circle_spectral_estimate_oai
    {A : UnitAddCircle × UnitAddCircle → ℂ} {A₀ : UnitAddCircle → ℝ → ℂ}
    {Pr V : ℝ → ℝ} {m : ℤ} {δ : ℕ → ℝ} {H : ℕ → UnitAddCircle → UnitAddCircle}
    {o l u R : ℝ}
    (hm : m ≠ 0)
    (hH : ∀ n (x : ℝ), H n (x : UnitAddCircle) = ((n:ℝ)*(Pr x+δ n*x) : UnitAddCircle))
    (hA : ∀ a x, x ∈ Ioc o (o+1) → A ((x : UnitAddCircle),a) = A₀ a x)
    (hA₀ : ∀ a, ContDiff ℝ 2 (A₀ a)) (hAc : Continuous A₀.uncurry)
    (hAd : Continuous (fun p : UnitAddCircle × ℝ => deriv (A₀ p.1) p.2))
    (hAr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1))
    (hsupp : ∀ a, support (A₀ a) ⊆ Ioc l u)
    (hlo : o ≤ l) (huo : u ≤ o+1) (hlu : l ≤ u) (hR : 0 < R)
    (hPr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Pr)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V) (hPV : deriv Pr = V)
    (hdV : ∀ x ∈ Icc (l-2*R) (u+2*R), 0 < deriv V x)
    (h0 : 0 ∉ (fun x => (m:ℝ)*V x) '' Icc l u)
    (hHc : ∀ n, Continuous (H n)) (hAcont : Continuous A) (hδt : Tendsto δ atTop (𝓝 0))
    {I : Set ℝ} {o' : ℝ}
    {χ : ℝ → UnitAddCircle → ℝ} {ψ : UnitAddCircle → ℝ} {ψ₀ : ℝ → ℝ}
    (hIo : IsOpen I)
    (hψ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ₀) (hcψ₀ : HasCompactSupport ψ₀)
    (hsψ₀ : tsupport ψ₀ ⊆ Ioc o' (o'+1) ∩ I)
    (heψ : ∀ x ∈ Ioc o' (o'+1), ψ₀ x = ψ (x : UnitAddCircle))
    (hψc : Continuous ψ) (hχc : Continuous χ.uncurry) (hcχ : HasCompactSupport χ.uncurry)
    (hzχ : ∀ a, χ 0 a = 0)
    (hψ : ∀ a, 0 ≤ ψ a ∧ ψ a ≤ 1) (hχ : ∀ s a, 0 ≤ χ s a ∧ χ s a ≤ 1)
    (hχW : ∀ s a, stationaryWeight (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) (A₀ a) s ≠ 0 → χ s a = 1)
    {Q : ℕ} (hQ : 0 < Q) (h : ℤ) :
    let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x)
      (fun p : ℝ × ℝ => A₀ (p.2 : UnitAddCircle) p.1) ψ₀
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 < L → ∀ β : ℝ,
      ∀ (J₀ : ℝ → ℝ) (J : UnitAddCircle → ℝ),
      (∀ a ∈ I, J₀ a = L*a+β) →
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) J₀ → Measurable J →
      (∀ x ∈ I, J (x : UnitAddCircle) = J₀ x) →
      ∃ S : ℕ → Finset ℤ,
        (∀ n, 0 < n → ∀ k ∈ S n, h+k*(Q:ℤ) ≠ 0) ∧
        (∀ n, 0 < n → ∀ k ∉ S n, ∀ a, χ (((h+k*(Q:ℤ):ℤ):ℝ)/n) a = 0) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ n : ℕ in atTop,
          (∫ a, |foldCircleDensity (fun t => ∑ k ∈ S n,
            unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
              (circleDensityLift o' (retainedCircleWeight ψ χ
                (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
              n ((h+k*(Q:ℤ):ℤ):ℝ) t) a-
            foldCircleDensity (fun s => (Q:ℝ)⁻¹*(∫ a, F (a,s))) a|
            ∂AddCircle.haarAddCircle) < C/L+η := by
  let B : ℝ × ℝ → ℂ := fun p => A₀ (p.2 : UnitAddCircle) p.1
  let F := stationaryCutoffLift (Icc (l-R) (u+R)) (fun x => (m:ℝ)*V x) B ψ₀
  change ∃ C, _
  obtain ⟨hF,hcF,ε,hε,hz⟩ := exact_cutoff_weight_regular hm hR hV hdV hAr
    (fun a => (hsupp a).trans Ioc_subset_Icc_self) hψ₀ hcψ₀ h0
  have hKA : ∀ p : ℝ × ℝ, B p ≠ 0 → p.1 ∈ Icc l u :=
    fun p hp => Ioc_subset_Icc_self (hsupp _ hp)
  have hsF : tsupport F ⊆ I ×ˢ univ := by
    intro p hp
    exact ⟨(hsψ₀ (stationaryCutoffLift_support (continuous_const.mul hV.continuous)
      isCompact_Icc hKA hp).1).2,mem_univ _⟩
  obtain ⟨C,hC,hBound⟩ := neutral_branch_circle_l1_bound hF hcF hε hz
  refine ⟨C,hC,?_⟩
  intro L hL β J₀ J he hJ hj hJe
  have hinj : InjOn J₀ I := by
    intro a ha b hb hab
    rw [he a ha,he b hb] at hab
    nlinarith
  have hd : ∀ x ∈ I, deriv J₀ x ≠ 0 := fun x hx => by
    rw [deriv_affine_on hIo he hx]
    exact hL.ne'
  obtain ⟨S,hSN,hST,ht⟩ := exact_passage_circle_spectral_limit hm hH hA hA₀ hAc hAd hAr
    hsupp hlo huo hlu hR hPr hV hPV hdV h0 hHc hAcont hδt hJ hIo hinj hd hj hJe
    hψ₀ hcψ₀ hsψ₀ heψ hψc hχc hcχ hzχ hψ hχ hχW hQ h
  refine ⟨S,hSN,hST,?_⟩
  intro η hη
  have hηt := ht.eventually (gt_mem_nhds hη)
  have hu (n : ℕ) (hn : 0 < n) :
      Integrable (foldCircleDensity (fun t => ∑ k ∈ S n,
        unfoldedModeDensity I J₀ (invFunOn J₀ I) (deriv J₀)
          (circleDensityLift o' (retainedCircleWeight ψ χ
            (fun n j => exactPassageCoeff m (H n) A j) n (h+k*(Q:ℤ))))
          n ((h+k*(Q:ℤ):ℤ):ℝ) t)) AddCircle.haarAddCircle := by
    apply integrable_foldCircleDensity
    · exact (S n).measurable_fun_sum (fun k hk => (retained_unfolded_regular hJ hIo hinj hd
        hψc hχc (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j)
        o' hn (hSN n hn k hk)).1)
    · exact integrable_finsetSum _ (fun k hk => (retained_unfolded_regular hJ hIo hinj hd
        hψc hχc (fun n j => continuous_exactPassageCoeff (hHc n) hAcont j)
        o' hn (hSN n hn k hk)).2)
  obtain ⟨hK,AK,hAK,MK,hsK,hyK⟩ := passageBranchKernel_regular hJ hIo hinj hd hF hcF hsF hε hz
  have hv (n : ℕ) (hn : 0 < n) := fineResidueKernel_regular (h := h) hK hAK hsK hyK hn hQ
  have hw := compact_slice_integral_regular ((hF.comp (contDiff_snd.prodMk contDiff_fst)).continuous)
    (hcF.comp_homeomorph (Homeomorph.prodComm ℝ ℝ))
  have hwi : Integrable (foldCircleDensity (fun s => (Q:ℝ)⁻¹*(∫ a, F (a,s))))
      AddCircle.haarAddCircle :=
    integrable_foldCircleDensity (measurable_const.mul hw.1.measurable) (hw.2.const_mul _)
  filter_upwards [hηt,eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hbn := hBound hIo hsF hQ hn0 h L hL β he
  exact (integral_abs_sub_triangle (hu n hn0)
    (integrable_foldCircleDensity (hv n hn0).1.measurable (hv n hn0).2) hwi).trans_lt
    (by linarith)

end ThreeTorus
end
end

end OAI
end

theorem solution : type_of% @OAI.ThreeTorus.exact_neutral_circle_spectral_estimate_oai := @OAI.ThreeTorus.exact_neutral_circle_spectral_estimate_oai
