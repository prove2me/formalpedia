-- Prove2me | solution 1 for OAI.ElasticityDistribution.compact_transport_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:16:55.734994+00:00
-- url     : https://prove2.me/submissions/8926e6d3-ede6-45f6-b681-98a59886ef90

import Mathlib
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_ElasticityCoordinates_planar_smooth_representative

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

end ElasticityRegularity

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityDistribution

open ElasticityAugmented ElasticityRegularity TemperedDistribution
lemma eval_smooth (a : Coeff) : ContDiff ℝ (⊤ : ℕ∞) (eval a) := (growth a).1

open ElasticityAugmented TrivSqZeroExt

end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators
namespace ElasticityDistribution
open ElasticityAugmented TemperedDistribution
namespace LocalEq
variable {Ω : Set X} {u v w u' v' : Dist}
lemma cutoff (h : LocalEq Ω u v) {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    smulLeftCLM ℂ g u = smulLeftCLM ℂ g v := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ g φ) = v (SchwartzMap.smulLeftCLM ℂ g φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_right : HasCompactSupport (g * (φ : X → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_left (f := g) (g := (φ : X → ℂ))).trans hs
end LocalEq

end ElasticityDistribution

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


section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma distribution_schwartz_product {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢(E,ℂ)) :
    smulLeftCLM ℂ g (u : 𝓢'(E,ℂ)) = (SchwartzMap.smulLeftCLM ℂ g u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply,SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

end

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
namespace ElasticityDistribution
open ElasticityAugmented ElasticityPhysicalAlgebra ElasticityNegativeOrder

lemma coe_schwartz_add (u v : S) : ((u+v : S) : Dist)=(u : Dist)+(v : Dist) := map_add _ _ _
lemma coe_schwartz_smul (c : ℂ) (u : S) : ((c • u : S) : Dist)=c • (u : Dist) := map_smul _ _ _
lemma coe_schwartz_sum {ι : Type*} (s : Finset ι) (u : ι → S) :
    ((∑ i ∈ s, u i : S) : Dist)=∑ i ∈ s, (u i : Dist) := map_sum _ _ _
lemma coeff_schwartz (a : Coeff) (u : S) : a • (u : Dist)=(mult (eval a) u : Dist) :=
  ElasticityRegularity.distribution_schwartz_product (growth a) u
end ElasticityDistribution

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityDistribution
open Set MeasureTheory TemperedDistribution

section
open scoped SchwartzMap LineDeriv ENNReal
open ElasticityRegularity

lemma compactLpMul_coe (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (u : L2Space) :
    (compactLpMul g hg hc u : X → ℂ)=ᵐ[volume] fun x => g x*u x := by
  filter_upwards [Lp.coeFn_lpSMul (r := 2) ((compact_bounded_multiplier hg hc).toLp g) u,
    (compact_bounded_multiplier hg hc).coeFn_toLp] with x hx hy
  change (((compact_bounded_multiplier hg hc).toLp g) • u) x=_
  rw [hx,Pi.smul_apply',hy,smul_eq_mul]
lemma compactLpMul_dist (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (u : L2Space) :
    (compactLpMul g hg hc u : Dist)=smulLeftCLM ℂ g (u : Dist) :=
  Lp.toTemperedDistribution_smul_eq (hc.hasTemperateGrowth hg) (compact_bounded_multiplier hg hc) u

lemma lp_mul_eq {K : Set X} (u : L2Space) (hu : ∀ᵐ x,x∉K → u x=0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (h1 : EqOn g 1 K) : smulLeftCLM ℂ g (u : Dist)=(u : Dist) := by
  rw [← compactLpMul_dist g hg hc]
  congr 1
  apply Lp.ext
  filter_upwards [compactLpMul_coe g hg hc u,hu] with x hx hux
  rw [hx]
  by_cases h : x∈K
  · rw [h1 h,Pi.one_apply,one_mul]
  · rw [hux h,mul_zero]
lemma lp_mul_zero {K : Set X} (u : L2Space) (hu : ∀ᵐ x,x∉K → u x=0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (h0 : EqOn g 0 K) : smulLeftCLM ℂ g (u : Dist)=0 := by
  rw [← compactLpMul_dist g hg hc]
  have he : compactLpMul g hg hc u=0 := by
    apply Lp.ext
    filter_upwards [compactLpMul_coe g hg hc u,hu,Lp.coeFn_zero (E := ℂ) (p := (2 : ℝ≥0∞)) (μ := (volume : Measure X))] with x hx hux hz
    rw [hx,hz]
    change g x*u x=0
    by_cases h : x∈K
    · rw [h0 h,Pi.zero_apply,zero_mul]
    · rw [hux h,mul_zero]
  rw [he]
  exact (Lp.toTemperedDistributionCLM ℂ (volume : Measure X) 2).map_zero

lemma lp_cutoff_derivative {K B : Set X} (hB : IsOpen B) (hKB : K⊆B)
    (u : L2Space) (hu : ∀ᵐ x,x∉K → u x=0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (h1 : EqOn g 1 B) (a : X) :
    smulLeftCLM ℂ g (∂_{a} (u : Dist))=∂_{a} (u : Dist) := by
  have he := lp_mul_eq u hu g hg hc (h1.mono hKB)
  have h0 : EqOn (fun x => fderiv ℝ g x a) 0 K := by
    intro x hx
    have hh : g=ᶠ[nhds x] (fun _ => (1 : ℂ)) :=
      Filter.mem_of_superset (hB.mem_nhds (hKB hx)) h1
    change fderiv ℝ g x a=0
    rw [hh.fderiv_eq]
    simp only [fderiv_fun_const]
    rfl
  have hz := lp_mul_zero u hu _ (smooth_derivative hg a) (compact_derivative hc a) h0
  have hl := distribution_leibniz (hc.hasTemperateGrowth hg) a
    ((compact_derivative hc a).hasTemperateGrowth (smooth_derivative hg a)) (u : Dist)
  rw [he,hz,zero_add] at hl
  exact hl.symm

lemma continuous_supported_of_ae {K : Set X} (hK : IsClosed K)
    (u : L2Space) (hu : ∀ᵐ x,x∉K → u x=0)
    (v : X → ℂ) (hv : Continuous v) (hvu : (u : X → ℂ)=ᵐ[volume] v) :
    tsupport v⊆K := by
  have he : v=ᵐ[volume.restrict Kᶜ] 0 := by
    change ∀ᵐ x ∂volume.restrict Kᶜ,v x=0
    rw [ae_restrict_iff' hK.isOpen_compl.measurableSet]
    filter_upwards [hu,hvu] with x hx he
    intro hk
    rw [← he,hx hk]
  have hh : EqOn v 0 Kᶜ := Measure.eqOn_of_ae_eq he hv.continuousOn continuousOn_const
    (by rw [hK.isOpen_compl.interior_eq];exact subset_closure)
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (hh hn)

end
open scoped SchwartzMap LineDeriv ENNReal BigOperators
open ElasticityRegularity
variable {n P : Type*} [Fintype n]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]

lemma planeDerivative_schwartz (α β : X) (a : Test) :
    planeDerivative α β (a : Dist)=(planeSchwartz α β a : Dist) := by
  change ∂_{α} (a : Dist)+Complex.I • ∂_{β} (a : Dist)=
    ((∂_{α} a+Complex.I • ∂_{β} a : Test) : Dist)
  simp only [coe_schwartz_add,coe_schwartz_smul,
    lineDerivOp_toTemperedDistributionCLM_eq]

/-- Compactly supported differences of the actual weak columns are smooth,
including the transverse variable. No inverse of the transferred frame is
assumed and no ellipticity in three dimensions is asserted. -/
theorem compact_transport_smoothing_oai (L : (P × ℂ) ≃L[ℝ] X)
    {K B B₀ : Set X} (hK : IsCompact K) (hB₀ : IsOpen B₀) (hKB : K⊆B₀)
    (A : n → n → Coeff) (W : n → L2Space) (a : n → Test)
    (hext : ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist))
    (he : ∀ i,LocalEq B (planeDerivative (L (0,1)) (L (0,Complex.I)) (W i : Dist)+
      ∑ j,A i j • (W j : Dist)) 0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆B) (h1 : EqOn g 1 B₀) :
    ∃ v : n → Test,(∀ i,(W i : Dist)=(v i : Dist)) ∧
      ∀ i,tsupport (v i-a i : Test)⊆K := by
  classical
  let α := L (0,1)
  let β := L (0,Complex.I)
  let u := fun i => W i-(a i).toLp 2 volume
  have hu (i) : ∀ᵐ x,x∉K → u i x=0 := by
    have hh : LocalEqual Kᶜ (W i : Dist) (((a i).toLp 2 volume : L2Space) : Dist) := by
      simpa only [Lp.toTemperedDistribution_toLp_eq,LocalEqual,LocalEq] using hext i
    filter_upwards [LocalEqual.lp_ae hK.isClosed.isOpen_compl (W i) ((a i).toLp 2 volume) hh,
      Lp.coeFn_sub (W i) ((a i).toLp 2 volume)] with x hx hy
    intro hk
    change (W i-(a i).toLp 2 volume) x=0
    rw [hy,Pi.sub_apply,hx hk,sub_self]
  have ud (i) : (u i : Dist)=(W i : Dist)-(a i : Dist) := by
    change (Lp.toTemperedDistributionCLM ℂ volume 2) (W i-(a i).toLp 2 volume)=_
    rw [map_sub,Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistributionCLM_apply,
      Lp.toTemperedDistribution_toLp_eq]
  let q : n → Test := fun i => planeSchwartz α β (a i)+
    ∑ j,SchwartzMap.smulLeftCLM ℂ (eval (A i j)) (a j)
  have qd (i) : (q i : Dist)=planeDerivative α β (a i : Dist)+∑ j,A i j • (a j : Dist) := by
    simp only [q,coe_schwartz_add,coe_schwartz_sum,← planeDerivative_schwartz,coeff_schwartz,ElasticityNegativeOrder.mult]
  let f : n → Test := fun i => -(SchwartzMap.smulLeftCLM ℂ g (q i))
  have fd (i) : (f i : Dist)= -(smulLeftCLM ℂ g (q i : Dist)) := by
    rw [show f i= -(SchwartzMap.smulLeftCLM ℂ g (q i)) from rfl,map_neg]
    congr 1
    exact (distribution_schwartz_product (hc.hasTemperateGrowth hg) (q i)).symm
  have fcoe (i) : (f i : X → ℂ)=fun x => -(g x*q i x) := by
    funext x
    simp only [f,neg_apply,SchwartzMap.smulLeftCLM_apply_apply (hc.hasTemperateGrowth hg),smul_eq_mul]
  have hfc (i) : HasCompactSupport (f i : X → ℂ) := by
    rw [fcoe]
    exact (hc.mul_right (f' := (q i : X → ℂ))).neg
  have hfs (i) : tsupport (f i : X → ℂ)⊆tsupport g := by
    rw [fcoe]
    change tsupport (-(fun x => g x*q i x))⊆tsupport g
    rw [tsupport_neg]
    exact tsupport_mul_subset_left
  let b := fun i j x => g x*eval (A i j) x
  have hb (i j) : ContDiff ℝ (⊤ : ℕ∞) (b i j) := hg.mul (eval_smooth (A i j))
  have hbc (i j) : HasCompactSupport (b i j) := hc.mul_right
  let w := fun i => (∑ j,compactLpMul (b i j) (hb i j) (hbc i j) (u j))-(f i).toLp 2 volume
  have wd (i) : (w i : Dist)=(∑ j,smulLeftCLM ℂ (b i j) (u j : Dist))-(f i : Dist) := by
    change (Lp.toTemperedDistributionCLM ℂ volume 2) (_-_)=_
    simp only [map_sub,map_sum,Lp.toTemperedDistributionCLM_apply,compactLpMul_dist,
      Lp.toTemperedDistribution_toLp_eq]
  have wcoe (i) : ∀ᵐ x,w i x=∑ j,b i j x*u j x-f i x := by
    have hall : ∀ᵐ x,∀ j,compactLpMul (b i j) (hb i j) (hbc i j) (u j) x=b i j x*u j x := by
      rw [ae_all_iff]
      exact fun j => compactLpMul_coe _ _ _ _
    filter_upwards [hall,Lp.coeFn_finsetSum Finset.univ (fun j => compactLpMul (b i j) (hb i j) (hbc i j) (u j)),
      Lp.coeFn_sub (∑ j,compactLpMul (b i j) (hb i j) (hbc i j) (u j)) ((f i).toLp 2 volume),
      (f i).coeFn_toLp 2 volume] with x hx hy hz hf
    change ((∑ j,compactLpMul (b i j) (hb i j) (hbc i j) (u j))-(f i).toLp 2 volume) x=_
    rw [hz,Pi.sub_apply,hy,hf]
    simp only [Finset.sum_apply,hx]
  have we (i) : planeDerivative α β (u i : Dist)+(w i : Dist)=0 := by
    have hlu : LocalEq B (planeDerivative α β (u i : Dist)+∑ j,A i j • (u j : Dist)) (-(q i : Dist)) := by
      intro φ hφ hφs
      have hhi := he i φ hφ hφs
      simp only [ud,map_sub,smul_def,map_sub,Finset.sum_sub_distrib,qd,add_apply,sub_apply,neg_apply,zero_apply] at hhi ⊢
      linear_combination hhi
    have ht := hlu.cutoff hg hc hs
    simp only [map_add,map_sum,map_neg] at ht
    have hd : smulLeftCLM ℂ g (planeDerivative α β (u i : Dist))=planeDerivative α β (u i : Dist) := by
      change smulLeftCLM ℂ g (∂_{α} (u i : Dist)+Complex.I • ∂_{β} (u i : Dist))=_
      rw [map_add,map_smul,lp_cutoff_derivative hB₀ hKB (u i) (hu i) g hg hc h1 α,
        lp_cutoff_derivative hB₀ hKB (u i) (hu i) g hg hc h1 β]
      rfl
    have hm (j) : smulLeftCLM ℂ g (A i j • (u j : Dist))=smulLeftCLM ℂ (b i j) (u j : Dist) := by
      rw [smul_def,smulLeftCLM_smulLeftCLM_apply (growth (A i j)) (hc.hasTemperateGrowth hg)]
      congr 2
      funext x
      exact mul_comm _ _
    rw [hd] at ht
    simp_rw [hm] at ht
    rw [wd,fd]
    rw [sub_neg_eq_add]
    rw [← add_assoc,ht,neg_add_cancel]
  have hw (i) : ∀ᵐ x,x∉K∪tsupport g → w i x=0 := by
    have hall : ∀ᵐ x,∀ j,x∉K → u j x=0 := by rw [ae_all_iff];exact hu
    filter_upwards [wcoe i,hall] with x hx hxu
    intro hn
    rw [hx]
    have hf : f i x=0 := image_eq_zero_of_notMem_tsupport (fun hh => hn (Or.inr (hfs i hh)))
    simp only [hxu _ (fun hh => hn (Or.inl hh)),mul_zero,Finset.sum_const_zero,hf,sub_self]
  obtain ⟨v,hv,hvu⟩ := ElasticityCoordinates.planar_smooth_representative L
    (K∪tsupport g) (tsupport g) (hK.union hc) hc b hb
    (fun i j x hx => by simp only [b,image_eq_zero_of_notMem_tsupport hx,zero_mul])
    (fun i => (f i : X → ℂ)) (fun i => (f i).smooth ⊤)
    (fun i x hx => image_eq_zero_of_notMem_tsupport (fun hh => hx (hfs i hh)))
    u w (fun i => (hu i).mono fun x hx hn => hx (fun hh => hn (Or.inl hh))) hw wcoe we
  have hvK (i) : tsupport (v i)⊆K := continuous_supported_of_ae hK.isClosed (u i) (hu i) (v i) (hv i).continuous (hvu i)
  have hvc (i) : HasCompactSupport (v i) := hK.of_isClosed_subset (isClosed_tsupport _) (hvK i)
  let vS := fun i => (hvc i).toSchwartzMap (hv i)
  have vsd (i) : (u i : Dist)=(vS i : Dist) := by
    have hL : u i=(vS i).toLp 2 volume := by
      apply Lp.ext
      exact (hvu i).trans ((vS i).coeFn_toLp 2 volume).symm
    rw [hL,Lp.toTemperedDistribution_toLp_eq]
  refine ⟨fun i => vS i+a i,fun i => ?_,fun i => ?_⟩
  · rw [coe_schwartz_add,← vsd,ud,sub_add_cancel]
  · rw [add_sub_cancel_right]
    change tsupport (v i)⊆K
    exact hvK i
end ElasticityDistribution
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElasticityDistribution.compact_transport_smoothing_oai.{u_1, u_2} := @OAI.ElasticityDistribution.compact_transport_smoothing_oai.{u_1, u_2}
