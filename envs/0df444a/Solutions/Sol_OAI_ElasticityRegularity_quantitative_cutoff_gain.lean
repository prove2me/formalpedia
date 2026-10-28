-- Prove2me | solution 1 for OAI.ElasticityRegularity.quantitative_cutoff_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:57:45.692235+00:00
-- url     : https://prove2.me/submissions/99a14edf-6bef-4b83-878a-64c4d1d78716

import Mathlib
import Definitions.Def_OAIQ6El002
import Definitions.Def_OAIQ6El003

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
namespace ElasticityRegularity

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma fourierMultiplier_add {g h : E → ℂ}
    (hg : g.HasTemperateGrowth) (hh : h.HasTemperateGrowth) (u : 𝓢'(E,F)) :
    fourierMultiplierCLM F (g+h) u=fourierMultiplierCLM F g u+fourierMultiplierCLM F h u := by
  simp only [fourierMultiplierCLM_apply,smulLeftCLM_add hg hh,add_apply,fourierInv_add]

omit [CompleteSpace F] in
lemma besselPotential_two (u : 𝓢'(E,F)) :
    besselPotential E F 2 u=u+fourierMultiplierCLM F (fun x : E => ((‖x‖^2 : ℝ) : ℂ)) u := by
  have he : (fun x : E => (((1+‖x‖^2)^(2/2 : ℝ) : ℝ) : ℂ)) =
      (fun _ : E => (1 : ℂ))+(fun x : E => ((‖x‖^2 : ℝ) : ℂ)) := by
    funext x
    norm_num
  rw [besselPotential,he,fourierMultiplier_add (by fun_prop) (by fun_prop)]
  simp

lemma sobolev_real_smul {s : ℝ} {u : 𝓢'(E,F)} (hu : MemSobolev s 2 u) (c : ℝ) :
    MemSobolev s 2 (c • u) := by
  convert hu.smul (c : ℂ) using 1
  all_goals try with_reducible_and_instances rfl

/-- Whole-space elliptic gain for the actual distributional Laplacian. -/
theorem laplacian_gain {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hΔ : MemSobolev s 2 (Δ u)) : MemSobolev (s+2) 2 u := by
  have hp : (-(2*Real.pi)^2 : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have hm := sobolev_real_smul hΔ (-(2*Real.pi)^2)⁻¹
  rw [laplacian_eq_fourierMultiplierCLM,smul_smul,inv_mul_cancel₀ hp,one_smul] at hm
  have h := hu.add hm
  rw [← besselPotential_two,memSobolev_besselPotential_iff] at h
  simpa only [add_comm] using h

/-- One derivative of gain from information on all coordinate first derivatives. -/
theorem coordinate_derivative_gain {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {s : ℝ} {u : 𝓢'(E,F)}
    (hu : MemSobolev s 2 u) (hd : ∀ i, MemSobolev s 2 (∂_{b i} u)) :
    MemSobolev (s+1) 2 u := by
  have hall : ∀ S : Finset ι, MemSobolev (s-1) 2 (∑ i ∈ S, ∂_{b i} (∂_{b i} u)) := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi hS =>
      rw [Finset.sum_insert hi]
      exact ((hd i).lineDerivOp).add hS
  have hsum := hall Finset.univ
  rw [← laplacian_eq_sum b] at hsum
  have h := laplacian_gain (hu.mono (by linarith : s-1 ≤ s)) hsum
  have he : s-1+2=s+1 := by ring
  rwa [he] at h

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma compact_derivative {g : E → ℂ} (hg : HasCompactSupport g) (m : E) :
    HasCompactSupport (fun x => fderiv ℝ g x m) :=
  (hg.fderiv ℝ).comp_left (g := fun T : E →L[ℝ] ℂ => T m) (by simp)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
lemma smooth_derivative {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (m : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ g x m) :=
  (hg.fderiv_right (by simp)).clm_apply contDiff_const

lemma sobolev_zero_product {g : E → ℂ} (hg : g.HasTemperateGrowth)
    (hb : MemLp g ∞ (volume : Measure E)) {u : 𝓢'(E,F)} (hu : MemSobolev 0 2 u) :
    MemSobolev 0 2 (smulLeftCLM F g u) := by
  obtain ⟨v,rfl⟩ := memSobolev_zero_iff.mp hu
  apply memSobolev_zero_iff.mpr
  exact ⟨hb.toLp g • v, (Lp.toTemperedDistribution_smul_eq hg hb v).symm⟩

/-- Smooth compact coefficients preserve every nonnegative integral Sobolev order.
This is proved for the actual tempered distribution product, not an assumed
bounded multiplier on an unspecified Sobolev completion. -/
theorem sobolev_nat_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (n : ℕ) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,F)} (hu : MemSobolev n 2 u) : MemSobolev n 2 (smulLeftCLM F g u) := by
  induction n generalizing u g with
  | zero =>
    rw [Nat.cast_zero] at hu ⊢
    exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one] at hu ⊢
    apply coordinate_derivative_gain b (ih hg hc (hu.mono (by norm_num)))
    intro i
    have hd : MemSobolev (n : ℝ) 2 (∂_{b i} u) := by
      simpa only [add_sub_cancel_right] using hu.lineDerivOp (m := b i)
    rw [distribution_leibniz (hc.hasTemperateGrowth hg) (b i)
      ((compact_derivative hc (b i)).hasTemperateGrowth (smooth_derivative hg (b i)))]
    exact (ih (smooth_derivative hg (b i)) (compact_derivative hc (b i))
      (hu.mono (by norm_num))).add (ih hg hc hd)

end ElasticityRegularity

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
namespace ElasticityRegularity


section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

lemma sobolev_sum {ι : Type*} (S : Finset ι) {s : ℝ} {v : ι → 𝓢'(E,F)}
    (hv : ∀ i ∈ S, MemSobolev s 2 (v i)) : MemSobolev s 2 (∑ i ∈ S, v i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi hS =>
    rw [Finset.sum_insert hi]
    exact (hv i (Finset.mem_insert_self _ _)).add
      (hS (fun j hj => hv j (Finset.mem_insert_of_mem hj)))

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma derivative_support_subset (g : E → ℂ) (m : E) :
    tsupport (fun x => fderiv ℝ g x m) ⊆ tsupport g :=
  (tsupport_comp_subset (g := fun T : E →L[ℝ] ℂ => T m) (by simp) (fderiv ℝ g)).trans
    (tsupport_fderiv_subset ℝ)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma laplacian_product {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (u : 𝓢'(E,F)) :
    Δ (smulLeftCLM F g u) = smulLeftCLM F g (Δ u)+
      ∑ d, (smulLeftCLM F (fun x => fderiv ℝ (fun y => fderiv ℝ g y (b d)) x (b d)) u+
        (2 : ℂ) • smulLeftCLM F (fun x => fderiv ℝ g x (b d)) (∂_{b d} u)) := by
  classical
  rw [laplacian_eq_sum b,laplacian_eq_sum b,map_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have hgd := smooth_derivative hg (b d)
  have hcd := compact_derivative hc (b d)
  rw [distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd),LineDeriv.lineDerivOp_add,
    distribution_leibniz (hcd.hasTemperateGrowth hgd) _
      ((compact_derivative hcd (b d)).hasTemperateGrowth (smooth_derivative hgd (b d))),
    distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd)]
  module

end ElasticityRegularity

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_LocalRegularity
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal
namespace ElasticityRegularity


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma LocalEqual.lp_ae {Ω : Set E} (hΩ : IsOpen Ω)
    (u v : Lp ℂ 2 (volume : Measure E))
    (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → u x=v x := by
  have hu : LocallyIntegrable (u : E → ℂ) (volume : Measure E) := (Lp.memLp u).locallyIntegrable (by norm_num)
  have hv : LocallyIntegrable (v : E → ℂ) (volume : Measure E) := (Lp.memLp v).locallyIntegrable (by norm_num)
  have he : ∀ᵐ x ∂(volume : Measure E), x ∈ Ω → (u x-v x)=0 := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hu.sub hv).locallyIntegrableOn Ω) ?_
  · filter_upwards [he] with x hx
    intro hxΩ
    exact sub_eq_zero.mp (hx hxΩ)
  intro g hg hc hs
  let f : E → ℂ := fun x => (g x : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  let φ : 𝓢(E,ℂ) := hfc.toSchwartzMap hfg
  have hfs : tsupport (φ : E → ℂ) ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro x hx hzero
    apply hx
    change (g x : ℂ)=0
    rw [hzero,Complex.ofReal_zero]
  have hh := h φ hfc hfs
  simp only [Lp.toTemperedDistribution_apply] at hh
  have hiu := hu.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  have hiv := hv.integrable_smul_left_of_hasCompactSupport hg.continuous hc
  simp only [smul_sub]
  rw [integral_sub hiu hiv,sub_eq_zero]
  simp only [show (φ : E → ℂ)=f from rfl,f,Complex.real_smul,smul_eq_mul] at hh ⊢
  convert hh using 1
  all_goals try with_reducible_and_instances rfl

end ElasticityRegularity

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Planar
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
namespace ElasticityRegularity

/-- The closed graph argument supplies norms for genuine distribution operators,
not additional quantitative regularity assumptions. -/
theorem exists_continuous_lift
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    (J : Y →L[ℂ] Z) (hJ : Function.Injective J) (T : X →L[ℂ] Z)
    (hT : ∀ x, ∃ y, J y=T x) :
    ∃ L : X →L[ℂ] Y, ∀ x, J (L x)=T x := by
  choose l hl using hT
  let L : X →ₗ[ℂ] Y := {
    toFun := l
    map_add' := fun x y => hJ (by rw [map_add,hl,hl,hl,map_add])
    map_smul' := fun c x => hJ (by rw [map_smul,hl,hl,map_smul]; rfl) }
  have hc : IsClosed (L.graph : Set (X × Y)) := by
    have he : (L.graph : Set (X × Y))={p | T p.1=J p.2} := by
      ext p
      change p.2=L p.1 ↔ T p.1=J p.2
      constructor
      · intro h
        rw [h]
        exact (hl p.1).symm
      · intro h
        apply hJ
        exact h.symm.trans (hl p.1).symm
    rw [he]
    exact isClosed_eq (T.continuous.comp continuous_fst) (J.continuous.comp continuous_snd)
  exact ⟨⟨L,L.continuous_of_isClosed_graph hc⟩,hl⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma lp_distribution_injective : Function.Injective
    (fun u : Lp ℂ 2 (volume : Measure E) => (u : 𝓢'(E,ℂ))) := by
  intro u v huv
  apply Lp.ext
  have h : LocalEqual Set.univ (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ)) :=
    fun _ _ _ => congrArg (fun T : 𝓢'(E,ℂ) => T _) huv
  filter_upwards [h.lp_ae isOpen_univ u v] with x hx
  exact hx (Set.mem_univ x)

lemma sobolevInjection_injective (s : ℝ) :
    Function.Injective (sobolevInjection (E := E) s) := by
  intro u v huv
  have h := congrArg (besselPotential E ℂ s) huv
  have hh : (u : 𝓢'(E,ℂ))=(v : 𝓢'(E,ℂ)) := by
    simpa only [sobolevInjection,ContinuousLinearMap.comp_apply,
      besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
      ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply] using h
  exact lp_distribution_injective hh

lemma sobolevInjection_mem (s : ℝ) (f : Lp ℂ 2 (volume : Measure E)) :
    MemSobolev s 2 (sobolevInjection s f) := by
  refine ⟨f,?_⟩
  simp only [sobolevInjection,ContinuousLinearMap.comp_apply,
    besselPotential_besselPotential_apply,neg_add_cancel,besselPotential_zero,
    ContinuousLinearMap.id_apply,Lp.toTemperedDistributionCLM_apply]

lemma memSobolev_iff_range (s : ℝ) (u : 𝓢'(E,ℂ)) :
    MemSobolev s 2 u ↔ ∃ f : Lp ℂ 2 (volume : Measure E), sobolevInjection s f=u := by
  constructor
  · rintro ⟨f,hf⟩
    refine ⟨f,?_⟩
    change besselPotential E ℂ (-s) (f : 𝓢'(E,ℂ))=u
    exact (besselPotential_neg_apply_eq_iff s (f : 𝓢'(E,ℂ)) u).mpr hf
  · rintro ⟨f,rfl⟩
    exact sobolevInjection_mem s f

/-- A qualitative everywhere-defined Sobolev mapping theorem for a continuous
actual distribution operator automatically gives its bounded Sobolev realization.
This is useful for smooth multipliers and coordinate derivatives on cutoffs. -/
theorem exists_sobolev_realization (s t : ℝ) (P : 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ))
    (hP : ∀ u, MemSobolev s 2 u → MemSobolev t 2 (P u)) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection t (L f)=P (sobolevInjection s f) := by
  exact exists_continuous_lift (sobolevInjection t) (sobolevInjection_injective t)
    (P.comp (sobolevInjection s)) (fun f =>
      (memSobolev_iff_range t _).mp (hP _ (sobolevInjection_mem s f)))

theorem exists_bounded_sobolev_derivative (s : ℝ) (m : E) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (s-1) (L f)=∂_{m} (sobolevInjection s f) := by
  exact exists_sobolev_realization s (s-1) (LineDeriv.lineDerivOpCLM ℂ 𝓢'(E,ℂ) m)
    (fun _ h => h.lineDerivOp)

theorem exists_bounded_sobolev_inclusion {s t : ℝ} (hst : t ≤ s) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection t (L f)=sobolevInjection s f := by
  exact exists_sobolev_realization s t (ContinuousLinearMap.id ℂ _)
    (fun _ h => h.mono hst)

end ElasticityRegularity

end
namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma sobolev_product_step_down (s : ℝ)
    (hm : ∀ (g : E → ℂ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∀ u : 𝓢'(E,ℂ), MemSobolev s 2 u → MemSobolev s 2 (smulLeftCLM ℂ g u))
    {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,ℂ)} (hu : MemSobolev (s-1) 2 u) :
    MemSobolev (s-1) 2 (smulLeftCLM ℂ g u) := by
  let v := besselPotential E ℂ (-2) u
  have hv : MemSobolev (s+1) 2 v := by
    apply memSobolev_besselPotential_iff.mpr
    convert hu using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hvs : MemSobolev s 2 v := hv.mono (by linarith)
  let b := stdOrthonormalBasis ℝ E
  have hd : MemSobolev (s-1) 2 (smulLeftCLM ℂ g (Δ v)) := by
    rw [laplacian_eq_sum b,map_sum]
    apply sobolev_sum Finset.univ
    intro i _
    have hdi : MemSobolev s 2 (∂_{b i} v) := by
      simpa only [add_sub_cancel_right] using (hv.lineDerivOp (m := b i))
    have hgd := smooth_derivative hg (b i)
    have hcd := compact_derivative hc (b i)
    have h₁ := (hm g hg hc _ hdi).lineDerivOp (m := b i)
    have h₂ := (hm _ hgd hcd _ hdi).mono (by linarith : s-1 ≤ s)
    have hh := h₁.sub h₂
    rw [distribution_leibniz (hc.hasTemperateGrowth hg) _ (hcd.hasTemperateGrowth hgd),
      add_sub_cancel_left] at hh
    exact hh
  have hp : (-(2*Real.pi)^2 : ℝ) ≠ 0 :=
    neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (by norm_num) Real.pi_ne_zero))
  have he : u=v+(-(2*Real.pi)^2 : ℝ)⁻¹ • Δ v := by
    rw [laplacian_eq_fourierMultiplierCLM,smul_smul,inv_mul_cancel₀ hp,one_smul,
      ← besselPotential_two]
    simp only [v,besselPotential_besselPotential_apply,neg_add_cancel,
      besselPotential_zero,ContinuousLinearMap.id_apply]
  rw [he,map_add,ContinuousLinearMap.map_smul_of_tower]
  exact ((hm g hg hc _ hvs).mono (by linarith)).add (sobolev_real_smul hd _)

/-- Smooth compact multiplication preserves every integral Sobolev order,
including the H^-2 forcing order in the first augmented bootstrap step. -/
theorem sobolev_negative_product (n : ℕ) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    {u : 𝓢'(E,ℂ)} (hu : MemSobolev (-(n : ℝ)) 2 u) :
    MemSobolev (-(n : ℝ)) 2 (smulLeftCLM ℂ g u) := by
  induction n generalizing g u with
  | zero =>
    simp only [Nat.cast_zero,neg_zero] at hu ⊢
    exact sobolev_zero_product (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) hu
  | succ n ih =>
    have hh := sobolev_product_step_down (-(n : ℝ))
      (fun g hg hc u hu => ih hg hc hu) hg hc (u := u)
    have he : (-(n : ℝ)-1 : ℝ)= -((n+1 : ℕ) : ℝ) := by push_cast; ring
    rw [he] at hh
    exact hh hu

theorem exists_bounded_negative_multiplier (n : ℕ) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (-(n : ℝ)) (L f)=smulLeftCLM ℂ g (sobolevInjection (-(n : ℝ)) f) := by
  exact exists_sobolev_realization _ _ (smulLeftCLM ℂ g)
    (fun _ h => sobolev_negative_product n hg hc h)

theorem exists_bounded_nat_multiplier (n : ℕ) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (n : ℝ) (L f)=smulLeftCLM ℂ g (sobolevInjection (n : ℝ) f) := by
  exact exists_sobolev_realization _ _ (smulLeftCLM ℂ g)
    (fun _ h => sobolev_nat_product (stdOrthonormalBasis ℝ E) n hg hc h)
end ElasticityRegularity

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The actual whole-space Laplacian gain has a uniform norm estimate. Its
constant does not depend on any conjugation parameter or on the unknown. -/
theorem quantitative_laplacian_gain (s : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ f g : Lp ℂ 2 (volume : Measure E),
      Δ (sobolevInjection s f)=sobolevInjection (s-1) g →
      ∃ q : Lp ℂ 2 (volume : Measure E),
        sobolevInjection (s+1) q=sobolevInjection s f ∧
        ‖q‖ ≤ C*(‖f‖+‖g‖) := by
  let H := Lp ℂ 2 (volume : Measure E)
  let D : 𝓢'(E,ℂ) →L[ℂ] 𝓢'(E,ℂ) := LineDeriv.laplacianCLM ℂ E _
  let T : H × H →L[ℂ] 𝓢'(E,ℂ) := (sobolevInjection s).comp (ContinuousLinearMap.fst ℂ H H)
  let A : H × H →L[ℂ] 𝓢'(E,ℂ) := D.comp T-
    (sobolevInjection (s-1)).comp (ContinuousLinearMap.snd ℂ H H)
  let G : Submodule ℂ (H × H) := A.ker
  have hclosed : IsClosed (G : Set (H × H)) := A.isClosed_ker
  let : CompleteSpace G := hclosed.completeSpace_coe
  have he (p : G) : Δ (sobolevInjection s p.1.1)=sobolevInjection (s-1) p.1.2 := by
    have hp := p.2
    change A p.1=0 at hp
    apply sub_eq_zero.mp
    simpa only [A,D,T,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',laplacianCLM_apply] using hp
  obtain ⟨L,hL⟩ := exists_continuous_lift (sobolevInjection (E := E) (s+1))
    (sobolevInjection_injective (s+1)) (T.comp G.subtypeL) (fun p => by
      apply (memSobolev_iff_range (s+1) _).mp
      change MemSobolev (s+1) 2 (sobolevInjection s p.1.1)
      have hΔ : MemSobolev (s-1) 2 (Δ (sobolevInjection s p.1.1)) := by
        rw [he]
        exact sobolevInjection_mem _ _
      have h := laplacian_gain ((sobolevInjection_mem s p.1.1).mono (by linarith : s-1 ≤ s)) hΔ
      rw [show s-1+2=s+1 by ring] at h
      exact h)
  refine ⟨‖L‖+1,by positivity,fun f g hfg => ?_⟩
  have hG : (f,g) ∈ G := by
    change A (f,g)=0
    simpa only [A,D,T,sub_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',laplacianCLM_apply] using
      (sub_eq_zero.mpr hfg)
  let p : G := ⟨(f,g),hG⟩
  refine ⟨L p,hL p,?_⟩
  have hp : ‖p‖ ≤ ‖f‖+‖g‖ := by
    change max ‖f‖ ‖g‖ ≤ ‖f‖+‖g‖
    exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
  calc
    ‖L p‖ ≤ ‖L‖*‖p‖ := L.le_opNorm p
    _ ≤ (‖L‖+1)*(‖f‖+‖g‖) := by gcongr; linarith


end ElasticityRegularity

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityRegularity
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma exists_bounded_integer_multiplier (k : ℤ) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) :
    ∃ L : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E),
      ∀ f, sobolevInjection (k : ℝ) (L f)=smulLeftCLM ℂ g (sobolevInjection (k : ℝ) f) := by
  cases k with
  | ofNat n => exact exists_bounded_nat_multiplier n hg hc
  | negSucc n =>
    simpa only [Int.cast_negSucc,Nat.cast_add,Nat.cast_one] using
      exists_bounded_negative_multiplier (n+1) hg hc

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma nested_multiplier {g η : E → ℂ} (hg : g.HasTemperateGrowth)
    (hη : η.HasTemperateGrowth) (h1 : Set.EqOn η 1 (tsupport g)) (u : 𝓢'(E,ℂ)) :
    smulLeftCLM ℂ g (smulLeftCLM ℂ η u)=smulLeftCLM ℂ g u := by
  have he : η*g=g := by
    ext x
    change η x*g x=g x
    by_cases hx : x ∈ tsupport g
    · rw [h1 hx]
      simp only [Pi.one_apply,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx,mul_zero]
  rw [smulLeftCLM_smulLeftCLM_apply hη hg,he]

omit [MeasurableSpace E] [BorelSpace E] in
lemma laplacian_product_divergence {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {g : E → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g) (u : 𝓢'(E,ℂ)) :
    Δ (smulLeftCLM ℂ g u)=smulLeftCLM ℂ g (Δ u)+
      ∑ i, ((2 : ℂ) • ∂_{b i} (smulLeftCLM ℂ (fun x => fderiv ℝ g x (b i)) u)-
        smulLeftCLM ℂ (fun x => fderiv ℝ (fun y => fderiv ℝ g y (b i)) x (b i)) u) := by
  rw [laplacian_product b hg hc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hgd := smooth_derivative hg (b i)
  have hcd := compact_derivative hc (b i)
  rw [distribution_leibniz (hcd.hasTemperateGrowth hgd) _
    ((compact_derivative hcd (b i)).hasTemperateGrowth (smooth_derivative hgd (b i)))]
  module

/-- A nested-cutoff interior norm estimate for the genuine distributional
Laplacian. All multiplier and derivative constants are produced by previously
proved closed graph arguments. The result includes the initial negative order. -/
theorem quantitative_cutoff_gain_oai (k : ℤ) {χ η : E → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (h1 : Set.EqOn η 1 (tsupport χ)) :
    ∃ C : ℝ, 0<C ∧ ∀ (u : 𝓢'(E,ℂ)) (f g : Lp ℂ 2 (volume : Measure E)),
      sobolevInjection (k : ℝ) f=smulLeftCLM ℂ η u →
      sobolevInjection ((k : ℝ)-1) g=smulLeftCLM ℂ η (Δ u) →
      ∃ q : Lp ℂ 2 (volume : Measure E),
        sobolevInjection ((k : ℝ)+1) q=smulLeftCLM ℂ χ u ∧
        ‖q‖ ≤ C*(‖f‖+‖g‖) := by
  let b := stdOrthonormalBasis ℝ E
  let s : ℝ := k
  let H := Lp ℂ 2 (volume : Measure E)
  obtain ⟨M,hM⟩ := exists_bounded_integer_multiplier k hχ hcχ
  obtain ⟨N,hN⟩ := exists_bounded_integer_multiplier (k-1) hχ hcχ
  simp only [Int.cast_sub,Int.cast_one] at hN
  obtain ⟨J,hJ⟩ := exists_bounded_sobolev_inclusion (E := E) (show s-1 ≤ s by linarith)
  have hd (i : Fin (Module.finrank ℝ E)) := exists_bounded_sobolev_derivative s (b i)
  choose D hD using hd
  have hm (i : Fin (Module.finrank ℝ E)) := exists_bounded_integer_multiplier k
    (smooth_derivative hχ (b i)) (compact_derivative hcχ (b i))
  choose M₁ hM₁ using hm
  have hm₂ (i : Fin (Module.finrank ℝ E)) := exists_bounded_integer_multiplier k
    (smooth_derivative (smooth_derivative hχ (b i)) (b i))
    (compact_derivative (compact_derivative hcχ (b i)) (b i))
  choose M₂ hM₂ using hm₂
  let A : H →L[ℂ] H := ∑ i, ((2 : ℂ) • ((D i).comp (M₁ i))-J.comp (M₂ i))
  have hA (f : H) : sobolevInjection (s-1) (A f)=
      ∑ i, ((2 : ℂ) • ∂_{b i} (smulLeftCLM ℂ (fun x => fderiv ℝ χ x (b i)) (sobolevInjection s f))-
        smulLeftCLM ℂ (fun x => fderiv ℝ (fun y => fderiv ℝ χ y (b i)) x (b i)) (sobolevInjection s f)) := by
    dsimp only [s] at hD hJ ⊢
    simp only [A,sum_apply,sub_apply,smul_apply,ContinuousLinearMap.comp_apply,
      map_sum,map_sub,map_smul,hD,hJ,hM₁,hM₂]
  obtain ⟨K,hK,hgain⟩ := quantitative_laplacian_gain (E := E) s
  refine ⟨K*(‖M‖+‖N‖+‖A‖+1),by positivity,fun u f g hf hg => ?_⟩
  have hMf : sobolevInjection s (M f)=smulLeftCLM ℂ χ u := by
    rw [hM,hf]
    exact nested_multiplier (hcχ.hasTemperateGrowth hχ) (hcη.hasTemperateGrowth hη) h1 u
  have hsource : sobolevInjection (s-1) (N g+A f)=Δ (smulLeftCLM ℂ χ u) := by
    rw [map_add,hN,hg,hA,hf,laplacian_product_divergence b hχ hcχ]
    rw [nested_multiplier (hcχ.hasTemperateGrowth hχ) (hcη.hasTemperateGrowth hη) h1]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hdi := smooth_derivative hχ (b i)
    have hcdi := compact_derivative hcχ (b i)
    rw [nested_multiplier (hcdi.hasTemperateGrowth hdi) (hcη.hasTemperateGrowth hη)
      (fun x hx => h1 ((derivative_support_subset χ (b i)) hx)),
      nested_multiplier ((compact_derivative hcdi (b i)).hasTemperateGrowth (smooth_derivative hdi (b i)))
        (hcη.hasTemperateGrowth hη)
        (fun x hx => h1 ((derivative_support_subset χ (b i))
          ((derivative_support_subset _ (b i)) hx)))]
  obtain ⟨q,hq,hqn⟩ := hgain (M f) (N g+A f) (hMf ▸ hsource.symm)
  refine ⟨q,hq.trans hMf,hqn.trans ?_⟩
  have hMn := M.le_opNorm f
  have hNn := N.le_opNorm g
  have hAn := A.le_opNorm f
  have hsumn := norm_add_le (N g) (A f)
  have hsum : ‖M f‖+‖N g+A f‖ ≤ (‖M‖+‖N‖+‖A‖+1)*(‖f‖+‖g‖) := by
    have hNN := mul_nonneg (norm_nonneg N) (norm_nonneg f)
    have hMM := mul_nonneg (norm_nonneg M) (norm_nonneg g)
    have hAA := mul_nonneg (norm_nonneg A) (norm_nonneg g)
    nlinarith [norm_nonneg f,norm_nonneg g]
  calc
    K*(‖M f‖+‖N g+A f‖) ≤ K*((‖M‖+‖N‖+‖A‖+1)*(‖f‖+‖g‖)) := mul_le_mul_of_nonneg_left hsum hK.le
    _ = _ := by ring
end ElasticityRegularity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElasticityRegularity.quantitative_cutoff_gain_oai.{u_1} := @OAI.ElasticityRegularity.quantitative_cutoff_gain_oai.{u_1}
