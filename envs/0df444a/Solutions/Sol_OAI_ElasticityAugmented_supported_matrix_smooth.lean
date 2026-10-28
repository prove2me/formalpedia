-- Prove2me | solution 1 for OAI.ElasticityAugmented.supported_matrix_smooth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:06:34.168703+00:00
-- url     : https://prove2.me/submissions/9688282a-8d73-4d25-98a1-c371c160f31d

import Mathlib
import Definitions.Def_OAIQ6El004
import Definitions.Def_OAIQ6El005
import Theorems.Thm_OAI_ElasticityPlanar_supported_parameter_inversion
import Theorems.Thm_OAI_ElasticityPlanar_supported_weak_unique

section
-- module Solutions.OAIQ6_Elast.Elasticity_Extension
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Metric
open scoped Topology Manifold
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ ∀ x, χ x∈Icc 0 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V,hV,hKV,hVU⟩ := normal_exists_closure_subset hK.isClosed (hU.inter isOpen_ball)
    (show K⊆U∩ball (0 : E) R from fun x hx => ⟨hKU hx,hR hx⟩)
  obtain ⟨χ,hχ,hzero,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hV.interior_eq])
  have hs : tsupport (χ : E → ℝ)⊆closure V := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨χ,χ.contMDiff.contDiff,?_,fun x hx => (hVU (hs hx)).1,hχ,hb⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport χ)
  exact fun x hx => ball_subset_closedBall ((hVU (hs hx)).2)

end ElasticityBoundary

end
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

namespace LocalEqual
variable {Ω : Set E} {u v w u' v' : 𝓢'(E,ℂ)}
lemma cutoff (h : LocalEqual Ω u v) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) (hs : tsupport g ⊆ Ω) :
    smulLeftCLM ℂ g u = smulLeftCLM ℂ g v := by
  ext φ
  change u (SchwartzMap.smulLeftCLM ℂ g φ) = v (SchwartzMap.smulLeftCLM ℂ g φ)
  apply h
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (hc.mul_right : HasCompactSupport (g * (φ : E → ℂ)))
  · simpa only [SchwartzMap.smulLeftCLM_apply (hc.hasTemperateGrowth hg),Pi.smul_def,smul_eq_mul,Pi.mul_def] using
      (tsupport_mul_subset_left (f := g) (g := (φ : E → ℂ))).trans hs
end LocalEqual
end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma schwartz_dist_injective : Function.Injective (fun u : 𝓢(E,ℂ) => (u : 𝓢'(E,ℂ))) := by
  intro u v h
  apply SchwartzMap.injective_toLp 2 volume
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ))
  change ((u.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ)) =
    ((v.toLp 2 volume : Lp ℂ 2 (volume : Measure E)) : 𝓢'(E,ℂ))
  simpa only [Lp.toTemperedDistribution_toLp_eq] using h

lemma distribution_schwartz_product {g : E → ℂ} (hg : g.HasTemperateGrowth) (u : 𝓢(E,ℂ)) :
    smulLeftCLM ℂ g (u : 𝓢'(E,ℂ)) = (SchwartzMap.smulLeftCLM ℂ g u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [smulLeftCLM_apply_apply,SchwartzMap.coe_apply,SchwartzMap.smulLeftCLM_apply_apply hg,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  ring

lemma LocalEqual.schwartz_eqOn {Ω : Set E} (hΩ : IsOpen Ω)
    {u v : 𝓢(E,ℂ)} (h : LocalEqual Ω (u : 𝓢'(E,ℂ)) (v : 𝓢'(E,ℂ))) :
    Set.EqOn (u : E → ℂ) (v : E → ℂ) Ω := by
  intro x hx
  obtain ⟨g,hs,hc,hg,_,h1⟩ := exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hΩ.mem_nhds hx)
  let f : E → ℂ := fun y => (g y : ℂ)
  have hfc : HasCompactSupport f :=
    show HasCompactSupport (Complex.ofReal ∘ g) from hc.comp_left Complex.ofReal_zero
  have hfg : ContDiff ℝ (⊤ : ℕ∞) f :=
    (Complex.ofRealCLM.contDiff : ContDiff ℝ (⊤ : ℕ∞) Complex.ofReal).comp hg
  have hfs : tsupport f ⊆ Ω := by
    change closure (Function.support f) ⊆ Ω
    apply Set.Subset.trans (closure_mono ?_) hs
    intro y hy
    change g y ≠ 0
    intro hy0
    apply hy
    change (g y : ℂ)=0
    rw [hy0,Complex.ofReal_zero]
  have he := h.cutoff hfg hfc hfs
  rw [distribution_schwartz_product (hfc.hasTemperateGrowth hfg),
    distribution_schwartz_product (hfc.hasTemperateGrowth hfg)] at he
  have he' := congrArg (fun w : 𝓢(E,ℂ) => w x) (schwartz_dist_injective he)
  simp only [SchwartzMap.smulLeftCLM_apply_apply (hfc.hasTemperateGrowth hfg),smul_eq_mul] at he'
  have hx1 : f x=1 := by simp only [f,h1,Complex.ofReal_one]
  simpa only [hx1,one_mul] using he'

end

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

namespace ElasticityPlanar
open MeasureTheory Complex TemperedDistribution
open scoped SchwartzMap ENNReal BigOperators LineDeriv
variable {n : Type*} [Fintype n]

lemma toSchwartz_d (v : ℂ) (φ : Test) : toSchwartz (d v φ)=∂_{v} (toSchwartz φ) := by
  ext z
  rfl
lemma toSchwartz_mul (a : ℂ → ℂ) (ha : a.HasTemperateGrowth) (φ : Test) :
    toSchwartz (mulSmooth a ha.1 φ)=SchwartzMap.smulLeftCLM ℂ a (toSchwartz φ) := by
  ext z
  simp only [toSchwartz_apply,SchwartzMap.smulLeftCLM_apply_apply ha,smul_eq_mul]
  rfl
end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions _root_.OAI.ElasticityPlanar.graphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators LineDeriv Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]

omit [Fintype n] in
lemma entryInjection_apply (i : n) (f : Hilbert n) : entryInjection i f=(f i : 𝓢'(ℂ,ℂ)) := rfl

lemma planarOperator_apply (a : n → n → ℂ → ℂ) (i : n) (f : Hilbert n) :
    planarOperator a i f=ElasticityPlanarDistribution.dbar (f i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (f j : 𝓢'(ℂ,ℂ)) := by
  simp only [planarOperator,ContinuousLinearMap.comp_apply,add_apply,smul_apply,sum_apply,
    entryInjection_apply,LineDeriv.lineDerivOpCLM_apply,ElasticityPlanarDistribution.dbar]

end ElasticityPlanar
namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Complex
open scoped SchwartzMap ENNReal LineDeriv BigOperators
variable {n : Type*} [Fintype n]
open ElasticityRegularity

lemma dbar_schwartz (v : 𝓢(ℂ,ℂ)) :
    ElasticityPlanarDistribution.dbar (v : 𝓢'(ℂ,ℂ))=(schwartzDbar v : 𝓢'(ℂ,ℂ)) := by
  simp only [ElasticityPlanarDistribution.dbar,schwartzDbar,
    TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq]
  rw [map_add,map_smul]
end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory Set Topology
open scoped BigOperators ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : Type*} [Fintype n]

lemma plane_deriv (J : ℂ →L[ℝ] E) (x : E) {f : E → ℂ}
    (hf : Differentiable ℝ f) (z v : ℂ) :
    fderiv ℝ (f ∘ planeMap J x) z v=fderiv ℝ f (planeMap J x z) (J v) := by
  have hp : HasFDerivAt (planeMap J x) J z := by
    change HasFDerivAt (fun t : ℂ => x+J t) J z
    simpa only [Pi.add_def,zero_add] using (hasFDerivAt_const x z).add J.hasFDerivAt
  exact congrArg (fun T : ℂ →L[ℝ] ℂ => T v) ((hf _).hasFDerivAt.comp z hp).fderiv

end ElasticityPlanar
namespace ElasticityParameter
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k n : Type*} [Fintype k] [Fintype n]

lemma characteristicPlane_one (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ 1=∑ r, (θ r).re • e r := by simp [characteristicPlane]
lemma characteristicPlane_I (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ Complex.I=∑ r, (θ r).im • e r := by simp [characteristicPlane]
lemma characteristicPlane_principal (e : k → E) (θ : k → ℂ) (L : E →L[ℝ] ℂ) :
    L (characteristicPlane e θ 1)+Complex.I*L (characteristicPlane e θ Complex.I)=
      ∑ r, θ r*L (e r) := by
  rw [characteristicPlane_one,characteristicPlane_I]
  simp only [map_sum,map_smul,Complex.real_smul,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ((θ r).re+(θ r).im*Complex.I)*L (e r) := by ring
    _ = θ r*L (e r) := by rw [Complex.re_add_im]

end ElasticityParameter
namespace ElasticityParameter
open scoped BigOperators InnerProductSpace

lemma real_complex_plane_injective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b : E) (ha : a≠0) (hb : b≠0) (hab : inner ℝ a b=0) :
    Function.Injective (Complex.reCLM.smulRight a+Complex.imCLM.smulRight b : ℂ →L[ℝ] E) := by
  let J : ℂ →L[ℝ] E := Complex.reCLM.smulRight a+Complex.imCLM.smulRight b
  suffices hn : ∀ z : ℂ, J z=0 → z=0 by
    intro z w h
    apply sub_eq_zero.mp
    apply hn
    rw [map_sub,h,sub_self]
  intro z hz
  have ha0 : inner ℝ a a≠0 := by
    intro h
    exact ha (inner_self_eq_zero.mp h)
  have hb0 : inner ℝ b b≠0 := by
    intro h
    exact hb (inner_self_eq_zero.mp h)
  have hba : inner ℝ b a=0 := by rwa [real_inner_comm]
  have hr := congrArg (fun v : E => inner ℝ a v) hz
  have hi := congrArg (fun v : E => inner ℝ b v) hz
  change inner ℝ a (z.re • a+z.im • b)=inner ℝ a 0 at hr
  change inner ℝ b (z.re • a+z.im • b)=inner ℝ b 0 at hi
  simp only [inner_add_right,inner_smul_right,hab,hba,mul_zero,zero_add,add_zero,inner_zero_right] at hr hi
  apply Complex.ext
  · exact (mul_eq_zero.mp hr).resolve_right ha0
  · exact (mul_eq_zero.mp hi).resolve_right hb0

lemma basis_sum_apply (v : Fin 3 → ℝ) (i : Fin 3) :
    (∑ r, v r • basis r : X) i=v i := by
  simp [basis,Pi.single_apply]

lemma null_re_im (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) :
    (∑ i, (θ i).re*(θ i).re)=(∑ i, (θ i).im*(θ i).im) ∧
      (∑ i, (θ i).re*(θ i).im)=0 := by
  have hr := congrArg Complex.re hθ
  have hi := congrArg Complex.im hθ
  simp only [Complex.re_sum,Complex.mul_re,Complex.zero_re,Finset.sum_sub_distrib] at hr
  simp only [Complex.im_sum,Complex.mul_im,Complex.zero_im,Finset.sum_add_distrib] at hi
  have he : (∑ i, (θ i).im*(θ i).re)=(∑ i, (θ i).re*(θ i).im) :=
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  rw [he] at hi
  constructor
  · exact sub_eq_zero.mp hr
  · linarith

lemma null_plane_injective (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (hne : θ≠0) :
    Function.Injective (characteristicPlane basis θ) := by
  obtain ⟨hre,him⟩ := null_re_im θ hθ
  let a : X := ∑ i, (θ i).re • basis i
  let b : X := ∑ i, (θ i).im • basis i
  have hai (i : Fin 3) : a i=(θ i).re := basis_sum_apply _ i
  have hbi (i : Fin 3) : b i=(θ i).im := basis_sum_apply _ i
  have haa : inner ℝ a a=∑ i, (θ i).re*(θ i).re := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai]
  have hbb : inner ℝ b b=∑ i, (θ i).im*(θ i).im := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hbi]
  have hab : inner ℝ a b=0 := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,hai,hbi]
    simpa only [mul_comm] using him
  have he : inner ℝ a a=inner ℝ b b := by rw [haa,hbb,hre]
  have hboth : ¬ (a=0 ∧ b=0) := by
    rintro ⟨ha,hb⟩
    apply hne
    funext i
    apply Complex.ext
    · simpa only [ha,PiLp.zero_apply,Pi.zero_apply,Complex.zero_re] using (hai i).symm
    · simpa only [hb,PiLp.zero_apply,Pi.zero_apply,Complex.zero_im] using (hbi i).symm
  have ha : a≠0 := by
    intro hz
    apply hboth
    refine ⟨hz,(@inner_self_eq_zero ℝ X _ _ _).mp ?_⟩
    rw [← he,hz,inner_zero_left]
  have hb : b≠0 := by
    intro hz
    apply ha
    apply (@inner_self_eq_zero ℝ X _ _ _).mp
    rw [he,hz,inner_zero_left]
  exact real_complex_plane_injective a b ha hb hab
end ElasticityParameter
namespace ElasticityAugmented
open scoped BigOperators

lemma thetaDerivation_apply (θ : Fin 3 → ℂ) (f : Smooth) :
    thetaDerivation θ f=direction (A := Smooth) coord θ f := by
  simp [thetaDerivation,direction,Fin.sum_univ_three]
end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/- The exact extension proofs are reused from their canonical original module. -/

namespace ElasticityPlanar
open Set MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

open ElasticityRegularity
variable {n : Type*} [Fintype n]
lemma L2_distribution (u : Test) : (L2 u : 𝓢'(ℂ,ℂ))=(toSchwartz u : 𝓢'(ℂ,ℂ)) :=
  Lp.toTemperedDistribution_toLp_eq (toSchwartz u)
lemma planarOperator_test (a : n → n → ℂ → ℂ) (ha : ∀ i j, (a i j).HasTemperateGrowth)
    (u : n → Test) (i : n) :
    planarOperator a i (embed u)=entryInjection i (embed (transport a (fun i j => (ha i j).1) u)) := by
  simp only [planarOperator_apply,entryInjection_apply,embed_apply,L2_distribution,dbar_schwartz]
  have ht : toSchwartz (transport a (fun i j => (ha i j).1) u i)=
      schwartzDbar (toSchwartz (u i))+∑ j, SchwartzMap.smulLeftCLM ℂ (a i j) (toSchwartz (u j)) := by
    simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,map_add,map_smul,map_sum,
      toSchwartz_d,schwartzDbar]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => toSchwartz_mul (a i j) (ha i j) (u j))
  rw [ht,map_add,map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun j _ => distribution_schwartz_product (ha i j) (toSchwartz (u j)))

lemma test_support_distribution {S : Set ℂ} (u : Test) (hu : tsupport (u : ℂ → ℂ)⊆S) :
    LocalEqual Sᶜ (L2 u : 𝓢'(ℂ,ℂ)) 0 := by
  intro φ _ hs
  rw [L2_distribution]
  change (∫ z : ℂ, φ z • toSchwartz u z)=0
  apply integral_eq_zero_of_ae
  filter_upwards [] with z
  by_cases hz : z∈S
  · have hz' : z∉tsupport (φ : ℂ → ℂ) := fun h => hs h hz
    rw [image_eq_zero_of_notMem_tsupport hz',zero_smul]
    rfl
  · have hz' : z∉tsupport (u : ℂ → ℂ) := fun h => hz (hu h)
    rw [toSchwartz_apply,image_eq_zero_of_notMem_tsupport hz',smul_zero]
    rfl

end ElasticityPlanar

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CommonFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityAugmented
lemma smooth_sum_eval {ι : Type*} [Fintype ι] (f : ι → Smooth) (x : X) :
    ((∑ i,f i : Smooth) : X → ℂ) x=∑ i,(f i : X → ℂ) x := by
  exact map_sum ((Pi.evalRingHom (fun _ : X => ℂ) x).comp Smooth.val.toRingHom) f Finset.univ
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Conic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [Fintype n] in
lemma matrixD_one (θ : Fin 3 → ℂ) : matrixD θ (1 : Matrix n n Smooth)=0 := by
  ext i j
  simp only [matrixD,Matrix.one_apply,Matrix.zero_apply]
  split_ifs <;> simp

end ElasticityAugmented

end
end
section
noncomputable section
open Set
open scoped BigOperators
namespace ElasticityParameter
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma commutator_flatten {R : Type*} [CommRing R]
    (M₂ M₁ G : n → n → R) (i j : n) :
    (∑ k, (M₂ i k*G k j-G i k*M₁ k j))=
      ∑ q : n × n, ((if q.2=j then M₂ i q.1 else 0)-
        (if q.1=i then M₁ q.2 j else 0))*G q.1 q.2 := by
  rw [Fintype.sum_prod_type]
  simp only [sub_mul,Finset.sum_sub_distrib,ite_mul,zero_mul]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [mul_comm]

end ElasticityParameter

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma matrixD_eval (θ : Fin 3 → ℂ) (G : Matrix n n Smooth) (x : X) (i j : n) :
    matrixEval x (matrixD θ G) i j=∑ r,θ r*fderiv ℝ (G i j : X → ℂ) x (ElasticityParameter.basis r) := by
  simp only [matrixEval_apply,matrixD,thetaDerivation_apply,direction,smooth_sum_eval,
    Subalgebra.coe_smul,Pi.smul_apply,smul_eq_mul]
  rfl

end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Holomorphy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap BigOperators
namespace ElasticityPlanar
open ElasticityRegularity
variable {n : Type*} [Fintype n]
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
lemma test_equation_distribution (a : n → n → ℂ → ℂ)
    (ha : ∀ i j,(a i j).HasTemperateGrowth) (u f : n → Test)
    (he : ∀ i z,schwartzDbar (toSchwartz (u i)) z+∑ j,a i j z*u j z=f i z) (i : n) :
    planarOperator a i (embed u)=(toSchwartz (f i) : 𝓢'(ℂ,ℂ)) := by
  rw [planarOperator_test a ha]
  change (L2 (transport a (fun i j => (ha i j).1) u i) : 𝓢'(ℂ,ℂ))=_
  rw [L2_distribution]
  congr 1
  apply congrArg toSchwartz
  apply Subtype.ext
  funext z
  simp only [transport,LinearMap.coe_mk,AddHom.coe_mk,Submodule.coe_add,Submodule.coe_smul,
    Submodule.coe_sum,Pi.add_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  exact he i z

/-- Uniqueness identifies the independently supplied smooth slices with the
jointly smooth selection; smooth parameter dependence is a conclusion. -/
theorem classical_parameter_smooth {S K : Set ℂ} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j p z,z∉K → a i j (p,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i p z,z∉K → f i (p,z)=0)
    (u : P → n → Test) (hu : ∀ p i,tsupport (u p i : ℂ → ℂ)⊆S)
    (he : ∀ p i z,schwartzDbar (toSchwartz (u p i)) z+
      ∑ j,a i j (p,z)*u p j z=f i (p,z)) :
    ∀ i,ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => u q.1 i q.2) := by
  have hat (p : P) (i j : n) : (fun z => a i j (p,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) p).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  let F (p : P) (i : n) : Test := ⟨fun z => f i (p,z),
    (hf i).comp (contDiff_const.prodMk contDiff_id),compact_slice hK (f i) (hfs i) p⟩
  have hdist (p : P) (i : n) := test_equation_distribution (fun i j z => a i j (p,z))
    (hat p) (u p) (F p) (he p) i
  obtain ⟨v,hv,hvs,hve⟩ := supported_parameter_inversion hS hK a ha hs f hf hfs
    (D := univ) dense_univ (fun p _ => ⟨embed (u p),fun i => ⟨hdist p i,
      test_support_distribution (u p i) (hu p i)⟩⟩)
  have huv (p : P) : embed (u p)=embed (v p) := by
    apply supported_weak_unique hS (fun i j z => a i j (p,z)) (hat p)
    · intro i
      exact (hdist p i).trans (test_equation_distribution (fun i j z => a i j (p,z))
        (hat p) (v p) (F p) (hve p) i).symm
    · intro i
      exact test_support_distribution (u p i) (hu p i)
    · intro i
      exact test_support_distribution (v p i) (hvs p i)
  have htest (p : P) (i : n) : u p i=v p i := by
    have hh := congrArg (entryInjection i) (huv p)
    change (L2 (u p i) : 𝓢'(ℂ,ℂ))=(L2 (v p i) : 𝓢'(ℂ,ℂ)) at hh
    rw [L2_distribution,L2_distribution] at hh
    have heq : LocalEqual univ (toSchwartz (u p i) : 𝓢'(ℂ,ℂ)) (toSchwartz (v p i) : 𝓢'(ℂ,ℂ)) :=
      fun φ _ _ => congrArg (fun t : 𝓢'(ℂ,ℂ) => t φ) hh
    apply Subtype.ext
    funext z
    exact heq.schwartz_eqOn isOpen_univ (mem_univ z)
  simpa only [htest] using hv
end ElasticityPlanar

end
end
section
noncomputable section
open Set Filter
open scoped Topology
namespace ElasticityCoordinates
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma compact_parameter_identity (p₀ : P) :
    ∃ τ : P → P,ContDiff ℝ (⊤ : ℕ∞) τ ∧ IsCompact (range τ) ∧ τ=ᶠ[𝓝 p₀] id := by
  obtain ⟨χ,hχ,hc,_,h1,_⟩ := ElasticityBoundary.compact_smooth_cutoff
    (K := {p₀}) (U := univ) isCompact_singleton isOpen_univ (subset_univ _)
  let u := fun p => χ p • (p-p₀)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hχ.smul (contDiff_id.sub contDiff_const)
  have huc : HasCompactSupport u := hc.smul_right
  refine ⟨fun p => p₀+u p,contDiff_const.add hu,?_,?_⟩
  · have he : range (fun p => p₀+u p)=(fun q => p₀+q) '' range u := by
      ext q
      simp only [mem_range,mem_image,exists_exists_eq_and]
    rw [he]
    exact (huc.isCompact_range hu.continuous).image (continuous_const.add continuous_id)
  · have hh : ∀ᶠ p in 𝓝 p₀,χ p=1 := by simpa only [nhdsSet_singleton] using h1
    filter_upwards [hh] with p hp
    simp only [u,hp,one_smul,id_eq]
    abel

omit [NormedSpace ℝ P] [FiniteDimensional ℝ P] [FiniteDimensional ℝ E] in
/-- Uniform properness of an injective family of characteristic planes on a
compact parameter set. This supplies a fixed planar support for parameter
inversion, rather than silently treating moving planes as fixed. -/
lemma uniform_plane_support {T : Set P} (hT : IsCompact T)
    (J : P → ℂ →L[ℝ] E) (hJ : Continuous J) (hinj : ∀ p∈T,Function.Injective (J p))
    (x : P → E) (hx : Continuous x) {K : Set E} (hK : IsCompact K) :
    ∃ S : Set ℂ,IsCompact S ∧ ∀ p∈T,∀ w,x p+J p w∈K → w∈S := by
  have hc : IsCompact (T ×ˢ Metric.sphere (0 : ℂ) 1) := hT.prod (isCompact_sphere _ _)
  have hf : Continuous (fun q : P × ℂ => ‖J q.1 q.2‖) :=
    ((hJ.comp continuous_fst).clm_apply continuous_snd).norm
  have hp : ∀ q∈T ×ˢ Metric.sphere (0 : ℂ) 1,0<‖J q.1 q.2‖ := by
    rintro ⟨p,w⟩ ⟨hpt,hws⟩
    apply norm_pos_iff.mpr
    intro hz
    have hw : w=0 := hinj p hpt (hz.trans (map_zero _).symm)
    have hh : ‖w‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hws
    rw [hw,norm_zero] at hh
    norm_num at hh
  obtain ⟨c,hc0,hc⟩ := hc.exists_forall_le' hf.continuousOn hp
  have hlow (p : P) (hpt : p∈T) (w : ℂ) : c*‖w‖≤‖J p w‖ := by
    by_cases hw : w=0
    · simp only [hw,norm_zero,mul_zero,map_zero,le_refl]
    have hn : 0<‖w‖ := norm_pos_iff.mpr hw
    have hu : (‖w‖⁻¹ : ℝ) • w∈Metric.sphere (0 : ℂ) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn]
      exact inv_mul_cancel₀ hn.ne'
    have hh := hc (p,(‖w‖⁻¹ : ℝ) • w) ⟨hpt,hu⟩
    simp only [map_smul,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hn] at hh
    have he := mul_le_mul_of_nonneg_left hh hn.le
    calc
      c*‖w‖=‖w‖*c := mul_comm _ _
      _ ≤ ‖w‖*(‖w‖⁻¹*‖J p w‖) := he
      _ = ‖J p w‖ := by rw [← mul_assoc,mul_inv_cancel₀ hn.ne',one_mul]
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨C,hC⟩ := (hT.image hx).isBounded.exists_norm_le
  refine ⟨Metric.closedBall 0 ((R+C)/c),isCompact_closedBall _ _,fun p hpt w hw => ?_⟩
  rw [Metric.mem_closedBall,dist_zero_right,le_div_iff₀ hc0]
  have hu : ‖J p w‖≤R+C := by
    have he : J p w=(x p+J p w)-x p := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (hR _ hw) (hC _ (mem_image_of_mem x hpt)))
  have hh : ‖w‖*c≤‖J p w‖ := by simpa only [mul_comm] using hlow p hpt w
  exact hh.trans hu
end ElasticityCoordinates

end
end
section
noncomputable section
open Set Filter
open scoped Topology BigOperators SchwartzMap
namespace ElasticityPlanar
variable {n : Type*} [Fintype n]
variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
/-- Joint smoothness from supported transport on moving characteristic planes.
Neither continuity nor parameter differentiability of the unknown is assumed. -/
theorem moving_plane_parameter_smooth (J : P → ℂ →L[ℝ] E)
    (hJ : ContDiff ℝ (⊤ : ℕ∞) J) (hJi : ∀ p,Function.Injective (J p))
    {S K : Set E} (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → E × P → ℂ) (ha : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (has : ∀ i j x p,x∉K → a i j (x,p)=0)
    (f : n → E × P → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i x p,x∉K → f i (x,p)=0)
    (u : P → n → E → ℂ) (hu : ∀ p i,ContDiff ℝ (⊤ : ℕ∞) (u p i))
    (hus : ∀ p i,tsupport (u p i)⊆S)
    (he : ∀ p i x,fderiv ℝ (u p i) x (J p 1)+Complex.I*fderiv ℝ (u p i) x (J p Complex.I)+
      ∑ j,a i j (x,p)*u p j x=f i (x,p)) :
    ∀ i,ContDiff ℝ (⊤ : ℕ∞) (fun q : E × P => u q.2 i q.1) := by
  intro i
  apply contDiff_iff_contDiffAt.mpr
  intro q₀
  obtain ⟨τ,hτ,hτc,hτe⟩ := ElasticityCoordinates.compact_parameter_identity q₀
  obtain ⟨W,hW,hWs⟩ := ElasticityCoordinates.uniform_plane_support hτc
    (fun q : E × P => J q.2) (hJ.continuous.comp continuous_snd)
    (fun q _ => hJi q.2) Prod.fst continuous_fst (hS.union hK)
  let F : (E × P) × ℂ → E := fun q => (τ q.1).1+J (τ q.1).2 q.2
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (hτ.fst.comp contDiff_fst).add ((hJ.comp (hτ.snd.comp contDiff_fst)).clm_apply contDiff_snd)
  let A : n → n → (E × P) × ℂ → ℂ := fun i j q => a i j (F q,(τ q.1).2)
  let b : n → (E × P) × ℂ → ℂ := fun i q => f i (F q,(τ q.1).2)
  have hA (i j) : ContDiff ℝ (⊤ : ℕ∞) (A i j) :=
    (ha i j).comp (hF.prodMk (hτ.snd.comp contDiff_fst))
  have hb (i) : ContDiff ℝ (⊤ : ℕ∞) (b i) :=
    (hf i).comp (hF.prodMk (hτ.snd.comp contDiff_fst))
  have hout (q : E × P) (z : ℂ) (hz : z∉W) : F (q,z)∉S∪K :=
    fun hh => hz (hWs (τ q) (mem_range_self q) z hh)
  have hAs (i j q z) (hz : z∉W) : A i j (q,z)=0 :=
    has i j _ _ (fun hh => hout q z hz (Or.inr hh))
  have hbs (i q z) (hz : z∉W) : b i (q,z)=0 :=
    hfs i _ _ (fun hh => hout q z hz (Or.inr hh))
  have hvu (q : E × P) (j : n) : ContDiff ℝ (⊤ : ℕ∞) (fun z => u (τ q).2 j (F (q,z))) :=
    (hu _ _).comp (hF.comp (contDiff_const.prodMk contDiff_id))
  have hvs (q : E × P) (j : n) : tsupport (fun z => u (τ q).2 j (F (q,z)))⊆W := by
    apply closure_minimal _ hW.isClosed
    intro z hz
    by_contra hn
    exact hz (image_eq_zero_of_notMem_tsupport (fun hh => hout q z hn (Or.inl (hus _ _ hh))))
  let v : (E × P) → n → Test := fun q j => ⟨fun z => u (τ q).2 j (F (q,z)),
    hvu q j,hW.of_isClosed_subset isClosed_closure (hvs q j)⟩
  have hve (q : E × P) (j : n) (z : ℂ) :
      schwartzDbar (toSchwartz (v q j)) z+∑ k,A j k (q,z)*v q k z=b j (q,z) := by
    change fderiv ℝ (u (τ q).2 j ∘ planeMap (J (τ q).2) (τ q).1) z 1+
      Complex.I*fderiv ℝ (u (τ q).2 j ∘ planeMap (J (τ q).2) (τ q).1) z Complex.I+_=_
    rw [plane_deriv _ _ ((hu _ _).differentiable (by simp)),
      plane_deriv _ _ ((hu _ _).differentiable (by simp))]
    exact he (τ q).2 j (F (q,z))
  have hv := classical_parameter_smooth hW hW A hA hAs b hb hbs v hvs hve
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun q : E × P => u (τ q).2 i (τ q).1) := by
    have hg := (hv i).comp (contDiff_id.prodMk (contDiff_const (c := (0 : ℂ))))
    simpa only [Function.comp_def,id,v,F,map_zero,add_zero] using hg
  apply hg.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hτe] with q hq
  simp only [hq,id_eq]
end ElasticityPlanar

end
end
section
noncomputable section
open Set
open scoped BigOperators Matrix
namespace ElasticityAugmented
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma characteristicPlane_smooth (θ : Fin 3 → ℂ → ℂ)
    (hθ : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (θ i)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ElasticityParameter.characteristicPlane ElasticityParameter.basis (fun i => θ i z)) := by
  apply ContDiff.add
  · exact contDiff_const.smulRight (ContDiff.sum (fun i _ =>
      (Complex.reCLM.contDiff.comp (hθ i)).smul contDiff_const))
  · exact contDiff_const.smulRight (ContDiff.sum (fun i _ =>
      (Complex.imCLM.contDiff.comp (hθ i)).smul contDiff_const))

/-- Joint smoothness of the actual supported comparison. Continuity in the
conic parameter is not supplied as data. -/
theorem supported_matrix_smooth_oai (θ : Fin 3 → ℂ → ℂ)
    (hθ : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (θ i))
    (hnull : ∀ z,∑ i,θ i z*θ i z=0) (hne : ∀ z,(fun i => θ i z)≠0)
    (M₀ M₁ G : ℂ → Matrix n n Smooth)
    (hM₀ : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (M₀ q.2 i j : X → ℂ) q.1))
    (hM₁ : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (M₁ q.2 i j : X → ℂ) q.1))
    {S : Set X} (hS : IsCompact S) (χ : Smooth) (hχ : HasCompactSupport (χ : X → ℂ))
    (hχ1 : ∀ x∈S,(χ : X → ℂ) x=1)
    (hs : ∀ z i j,tsupport ((G z i j-(1 : Matrix n n Smooth) i j : Smooth) : X → ℂ)⊆S)
    (hMe : ∀ z x,x∉S → matrixEval x (M₀ z)=matrixEval x (M₁ z))
    (he : ∀ z,matrixD (fun i => θ i z) (G z)=M₁ z*G z-G z*M₀ z) :
    ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (fun q : X × ℂ => (G q.2 i j : X → ℂ) q.1) := by
  let U : ℂ → Matrix n n Smooth := fun z => G z-1
  let C : (n × n) → (n × n) → X × ℂ → ℂ := fun p q y =>
    (if q.2=p.2 then (M₁ y.2 p.1 q.1 : X → ℂ) y.1 else 0)-
      (if q.1=p.1 then (M₀ y.2 q.2 p.2 : X → ℂ) y.1 else 0)
  let a : (n × n) → (n × n) → X × ℂ → ℂ := fun p q y => -(χ : X → ℂ) y.1*C p q y
  let f : (n × n) → X × ℂ → ℂ := fun p y => (M₁ y.2 p.1 p.2 : X → ℂ) y.1-(M₀ y.2 p.1 p.2 : X → ℂ) y.1
  have ha (p q : n × n) : ContDiff ℝ (⊤ : ℕ∞) (a p q) := by
    have hχs : ContDiff ℝ (⊤ : ℕ∞) (χ : X → ℂ) := χ.property
    apply ((hχs.comp contDiff_fst).neg).mul
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : X × ℂ => if q.2=p.2 then (M₁ y.2 p.1 q.1 : X → ℂ) y.1 else 0) := by
      split_ifs
      · exact hM₁ _ _
      · exact contDiff_const
    have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun y : X × ℂ => if q.1=p.1 then (M₀ y.2 q.2 p.2 : X → ℂ) y.1 else 0) := by
      split_ifs
      · exact hM₀ _ _
      · exact contDiff_const
    exact h1.sub h0
  have hf (p : n × n) : ContDiff ℝ (⊤ : ℕ∞) (f p) := (hM₁ _ _).sub (hM₀ _ _)
  let K := S∪tsupport (χ : X → ℂ)
  have hK : IsCompact K := hS.union hχ
  have has (p q : n × n) (x : X) (z : ℂ) (hx : x∉K) : a p q (x,z)=0 := by
    have hz := image_eq_zero_of_notMem_tsupport (fun hh => hx (Or.inr hh))
    change -(χ : X → ℂ) x*C p q (x,z)=0
    rw [hz,neg_zero,zero_mul]
  have hfs (p : n × n) (x : X) (z : ℂ) (hx : x∉K) : f p (x,z)=0 := by
    exact sub_eq_zero.mpr (congrArg (fun A : Matrix n n ℂ => A p.1 p.2)
      (hMe z x (fun hh => hx (Or.inl hh)))).symm
  have hUe (z : ℂ) : matrixD (fun i => θ i z) (U z)=
      M₁ z*U z-U z*M₀ z+(M₁ z-M₀ z) := by
    have hd : matrixD (fun i => θ i z) (G z-1)=matrixD (fun i => θ i z) (G z)-matrixD (fun i => θ i z) 1 := by
      funext i j; exact map_sub _ _ _
    dsimp only [U]
    rw [hd,matrixD_one,sub_zero,he]
    simp only [mul_sub,sub_mul,mul_one,one_mul]
    abel
  have hg := ElasticityPlanar.moving_plane_parameter_smooth
    (fun z => ElasticityParameter.characteristicPlane ElasticityParameter.basis (fun i => θ i z))
    (characteristicPlane_smooth θ hθ) (fun z => ElasticityParameter.null_plane_injective _ (hnull z) (hne z))
    hS hK a ha has f hf hfs
    (fun z p => (U z p.1 p.2 : X → ℂ)) (fun z p => (U z p.1 p.2).property)
    (fun z p => hs z p.1 p.2) (fun z p x => ?_)
  · intro i j
    have h := (hg (i,j)).add (contDiff_const (c := ((1 : Matrix n n Smooth) i j : X → ℂ) 0))
    have hid (x : X) : ((1 : Matrix n n Smooth) i j : X → ℂ) x=((1 : Matrix n n Smooth) i j : X → ℂ) 0 := by
      simp only [Matrix.one_apply]
      split_ifs <;> rfl
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext q
    change (G q.2 i j : X → ℂ) q.1=(G q.2 i j : X → ℂ) q.1-((1 : Matrix n n Smooth) i j : X → ℂ) q.1+_
    rw [hid,sub_add_cancel]
  · rw [ElasticityParameter.characteristicPlane_principal]
    have hh := congrArg (fun A : Matrix n n Smooth => matrixEval x A p.1 p.2) (hUe z)
    rw [matrixD_eval] at hh
    simp only [map_add,map_sub,map_mul,Matrix.add_apply,Matrix.sub_apply,Matrix.mul_apply,
      ← Finset.sum_sub_distrib] at hh
    rw [ElasticityParameter.commutator_flatten (matrixEval x (M₁ z)) (matrixEval x (M₀ z)) (matrixEval x (U z)) p.1 p.2] at hh
    change (∑ r,θ r z*fderiv ℝ (U z p.1 p.2 : X → ℂ) x (ElasticityParameter.basis r))=
      (∑ q : n × n,C p q (x,z)*(U z q.1 q.2 : X → ℂ) x)+f p (x,z) at hh
    rw [hh]
    have hc : ∑ q : n × n,a p q (x,z)*(U z q.1 q.2 : X → ℂ) x=
        -(∑ q : n × n,C p q (x,z)*(U z q.1 q.2 : X → ℂ) x) := by
      by_cases hx : x∈S
      · simp only [a,hχ1 x hx,neg_mul,one_mul,Finset.sum_neg_distrib]
      · have hu (q : n × n) : (U z q.1 q.2 : X → ℂ) x=0 :=
          image_eq_zero_of_notMem_tsupport (fun hh => hx (hs z q.1 q.2 hh))
        simp only [hu,mul_zero,Finset.sum_const_zero,neg_zero]
    rw [hc]
    ring
end ElasticityAugmented

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElasticityAugmented.supported_matrix_smooth_oai.{u_1} := @OAI.ElasticityAugmented.supported_matrix_smooth_oai.{u_1}
