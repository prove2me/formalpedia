-- Prove2me | solution 1 for OAI.Elasticity.dn_smooth_transport_column
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:27:17.769958+00:00
-- url     : https://prove2.me/submissions/03f0bf05-f255-4c5a-8d7d-fa456a74567d

import Mathlib
import Definitions.Def_ElasticityUniqueness
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_Elasticity_dn_weak_transport_column
import Theorems.Thm_OAI_ElasticityDistribution_compact_transport_smoothing
import Theorems.Thm_OAI_ElasticityDistribution_leading_matrix_local
import Theorems.Thm_OAI_ElasticityDistribution_smooth_column_patch

section
-- module Solutions.OAIQ6_Elast.Elasticity_Bessel
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete Fourier Bessel potentials for the required negative-order
supported Carleman estimate. All functions and operators are actual Schwartz
maps; no Sobolev-shift estimate is being assumed. -/
open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

lemma mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (f : S) (x : X) :
    mult a f x = a x * f x :=
  SchwartzMap.smulLeftCLM_apply_apply ha f x

end

lemma basis_expansion (v : X) : v = ∑ i : Fin 3, (v i) • e i := by
  ext j
  simp only [e, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply,
    PiLp.single_apply, smul_eq_mul]
  fin_cases j <;> simp

end ElasticityNegativeOrder

end

end OAI
end

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

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityDistribution

open ElasticityAugmented ElasticityRegularity TemperedDistribution
lemma dd_apply (i : Fin 3) (u : Dist) : dd i u = ∂_{e i} u := rfl

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
lemma smul (h : LocalEq Ω u v) (c : ℂ) : LocalEq Ω (c • u) (c • v) := by
  intro φ hc hs
  simp only [smul_apply,h φ hc hs]
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
-- module Solutions.OAIQ6_Elast.Elasticity_Solvability
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv

open scoped BigOperators
namespace ElasticityCoeffBounds
open ElasticityAugmented ElasticityPhysicalEstimate

lemma ExteriorConstant.add {f g : Smooth} (hf : ExteriorConstant f) (hg : ExteriorConstant g) :
    ExteriorConstant (f+g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨c+d, ?_⟩
  have he : (fun x => ((f+g : Smooth) : X → ℂ) x - (c+d)) =
      (fun x => (f : X → ℂ) x-c) + (fun x => (g : X → ℂ) x-d) := by
    funext x
    change (f : X → ℂ) x + (g : X → ℂ) x - (c+d) = _
    dsimp
    ring
  rw [he]
  exact hc.add hd

lemma reciprocal_mul (f : Smooth) (hf : ∀ x, (f : X → ℂ) x ≠ 0) :
    reciprocal f hf * f = 1 := by
  apply Subtype.ext
  funext x
  exact inv_mul_cancel₀ (hf x)

open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder
open ElasticityPhysicalAlgebra (physical phase)

end ElasticityCoeffBounds

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators
namespace ElasticityDistribution
open ElasticityAugmented ElasticityRegularity ElasticityCoeffBounds
open ElasticityPhysicalAlgebra (phase)
open ElasticityPhysicalDual

lemma inverseCoeff_mul (f : Smooth) (hf : ExteriorConstant f) (hn : ∀ x, (f : X → ℂ) x ≠ 0) :
    inverseCoeff f hf hn*exteriorCoeff f hf=1 := by
  apply Subtype.ext
  exact reciprocal_mul f hn

end ElasticityDistribution

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

namespace ElasticityParameter
open Set
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {k n : Type*} [Fintype k] [Fintype n]

lemma characteristicPlane_one (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ 1=∑ r, (θ r).re • e r := by simp [characteristicPlane]
lemma characteristicPlane_I (e : k → E) (θ : k → ℂ) :
    characteristicPlane e θ Complex.I=∑ r, (θ r).im • e r := by simp [characteristicPlane]
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

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_PhysicalCGO
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented

open Set
open scoped BigOperators
lemma real_longitudinal_positive (lam m : X → ℝ) (hp : ∀ x,0 < m x ∧ 0<3*lam x+2*m x) (x : X) :
    0<lam x+m x+m x := by have hh := hp x; linarith

end ElasticityAugmented
namespace ElasticityCGO

open Set
open ElasticityAugmented
open ElasticityNegativeOrder (cutoff)

lemma fiveCutoff_one (R : ℝ) (hR : 1≤R) (i : Fin 5) {x : X}
    (hx : x∈Metric.closedBall 0 (R+(i.val : ℝ)+1)) : fiveCutoff R hR i x=1 := by
  have hh := (cutoff (R+(i.val : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) i.val; linarith)).one_of_mem_closedBall hx
  unfold fiveCutoff
  rw [hh,Complex.ofReal_one]
lemma fiveCutoff_initial (R : ℝ) (hR : 1≤R) :
    EqOn (fiveCutoff R hR 0) 1 (Metric.ball 0 R) := by
  intro x hx
  apply fiveCutoff_one
  simp only [Fin.val_zero,Nat.cast_zero,add_zero,Metric.mem_closedBall]
  have hh := Metric.mem_ball.mp hx
  linarith
end ElasticityCGO

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

namespace ElasticityCoordinates
open Set MeasureTheory
open scoped ENNReal SchwartzMap LineDeriv
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

lemma planeSplit_symm (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ) (hK : Function.LeftInverse K J)
    (q : LinearMap.ker K.toLinearMap × ℂ) : (planeSplit J K hK).symm q=(q.1 : E)+J q.2 := rfl
lemma planeSplit_symm_plane (J : ℂ →L[ℝ] E) (K : E →L[ℝ] ℂ) (hK : Function.LeftInverse K J)
    (z : ℂ) : (planeSplit J K hK).symm (0,z)=J z := by
  simp only [planeSplit_symm,ZeroMemClass.coe_zero,zero_add]

end ElasticityCoordinates
namespace ElasticityDistribution

section
open TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented

lemma directiond_real_complex (α β : X) (u : Dist) :
    directiond (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) u=
      ∂_{α} u+Complex.I • ∂_{β} u := by
  have hα := ElasticityNegativeOrder.basis_expansion α
  have hβ := ElasticityNegativeOrder.basis_expansion β
  conv_rhs => rw [hα,hβ]
  ext φ
  simp only [LineDeriv.lineDerivOp_left_sum,LineDeriv.lineDerivOp_left_smul,
    directiond,dd_apply]
  simp [ElasticitySchwartzCarleman.e,e,Finset.smul_sum,add_mul,mul_assoc,Finset.sum_add_distrib,add_comm]

lemma exists_direction_coordinates (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0) :
    ∃ (J : ℂ →L[ℝ] X) (K : X →L[ℝ] ℂ),Function.LeftInverse K J ∧
      J 1=WithLp.toLp 2 (fun i => (θ i).re) ∧ J Complex.I=WithLp.toLp 2 (fun i => (θ i).im) := by
  let J := ElasticityParameter.characteristicPlane ElasticityParameter.basis θ
  have hJ := ElasticityParameter.null_plane_injective θ hθ hne
  obtain ⟨K,hK⟩ := ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hJ
  refine ⟨J,K,hK,?_,?_⟩
  · rw [show J 1=∑ i,(θ i).re • ElasticityParameter.basis i from ElasticityParameter.characteristicPlane_one _ _]
    ext i
    exact ElasticityParameter.basis_sum_apply _ i
  · rw [show J Complex.I=∑ i,(θ i).im • ElasticityParameter.basis i from ElasticityParameter.characteristicPlane_I _ _]
    ext i
    exact ElasticityParameter.basis_sum_apply _ i
end
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators
open ElasticityAugmented

lemma half_contraction (C : Fin 3 → Fin 4 → Fin 4 → Coeff) (θ : Fin 3 → ℂ)
    (U : Fin 4 → Dist) (i : Fin 4) :
    (∑ j,((1/2 : ℂ) • ∑ k,θ k • C k i j) • U j)=
      (1/2 : ℂ) • (∑ k,∑ j,θ k • (C k i j • U j)) := by
  have he (j : Fin 4) : ((1/2 : ℂ) • ∑ k,θ k • C k i j) • U j=
      (1/2 : ℂ) • ∑ k,θ k • (C k i j • U j) := by
    rw [smul_assoc]
    congr 1
    rw [@Finset.sum_smul (Fin 3) Coeff Dist _ _ _ (fun k => θ k • C k i j) Finset.univ (U j)]
    exact Finset.sum_congr rfl (fun k _ => smul_assoc (θ k) (C k i j) (U j))
  simp only [he,← Finset.smul_sum]
  congr 1
  simp only [Finset.smul_sum]
  exact Finset.sum_comm

/-- The actual weak leading augmented solution has a globally smooth
representative; the compact exterior difference is preserved exactly. -/
theorem weak_leading_smooth {K B B₀ : Set X} (hK : IsCompact K) (hB₀ : IsOpen B₀) (hKB : K⊆B₀)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (lam m n o : Coeff) (hn : n*m=1) (ho : o*(lam+m+m)=1)
    (W : Fin 4 → L2Space) (a : Fin 4 → Test)
    (hext : ∀ i,LocalEq Kᶜ (W i : Dist) (a i : Dist))
    (hr : ∀ i,LocalEq B (leadingRd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist) i) 0)
    (hs : LocalEq B (leadingSd θ lam m (fun j => (W j.succ : Dist)) (W 0 : Dist)) 0)
    (g : X → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hgs : tsupport g⊆B) (h1 : EqOn g 1 B₀) :
    ∃ v : Fin 4 → Test,(∀ i,(W i : Dist)=(v i : Dist)) ∧
      ∀ i,tsupport (v i-a i : Test)⊆K := by
  obtain ⟨J,Q,hQ,hα,hβ⟩ := exists_direction_coordinates θ hθ hne
  let L := (ElasticityCoordinates.planeSplit J Q hQ).symm
  let A := fun i j => (1/2 : ℂ) • ∑ k,θ k • coeffA dc lam m n o k i j
  have hD (u : Dist) : planeDerivative (L (0,1)) (L (0,Complex.I)) u=directiond θ u := by
    rw [show L (0,1)=J 1 from ElasticityCoordinates.planeSplit_symm_plane J Q hQ 1,
      show L (0,Complex.I)=J Complex.I from ElasticityCoordinates.planeSplit_symm_plane J Q hQ Complex.I,hα,hβ]
    have hh := directiond_real_complex (WithLp.toLp 2 (fun i => (θ i).re))
      (WithLp.toLp 2 (fun i => (θ i).im)) u
    have he : (fun i => ((θ i).re : ℂ)+Complex.I*((θ i).im : ℂ))=θ := by
      funext i
      simpa only [mul_comm] using (Complex.re_add_im (θ i))
    change ∂_{WithLp.toLp 2 (fun i => (θ i).re)} u+Complex.I •
      ∂_{WithLp.toLp 2 (fun i => (θ i).im)} u=directiond θ u
    simpa only [he] using hh.symm
  have hA (U : Fin 4 → Dist) (i : Fin 4) := half_contraction (coeffA dc lam m n o) θ U i
  have hE (i) : LocalEq B (planeDerivative (L (0,1)) (L (0,Complex.I)) (W i : Dist)+
      ∑ j,A i j • (W j : Dist)) 0 := by
    have hh := (leading_matrix_local θ hθ lam m n o hn ho (fun i => (W i : Dist)) hr hs i).smul (1/2)
    rw [hD,hA]
    intro φ hφ hφs
    have he := hh φ hφ hφs
    simp only [smul_apply,add_apply,smul_eq_mul,zero_apply] at he ⊢
    linear_combination he
  exact compact_transport_smoothing L hK hB₀ hKB A W a hext hE g hg hc hgs h1
end ElasticityDistribution
section
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (temperate_partial)
open ElasticityNegativeOrder (mult_apply)

lemma localizedLeading_eqOn {B : Set X} (hB : IsOpen B) (R : ℝ) (hR : 1≤R)
    (hBR : B⊆Metric.ball 0 R) (a : ℕ → Amplitude Smooth) (g : Smooth)
    (hc : HasCompactSupport (g : X → ℂ)) (hg : EqOn (g : X → ℂ) 1 B) (i : Fin 4) :
    EqOn (localizedLeading R hR a g i : X → ℂ)
      ((Fin.cons (a 0).2 (a 0).1 : Fin 4 → Smooth) i : X → ℂ) B := by
  have ht := hc.hasTemperateGrowth (smooth_coe g)
  have hd (x : X) (hx : x∈B) (j : Fin 3) : fderiv ℝ (g : X → ℂ) x (e j)=0 := by
    have hh : (g : X → ℂ)=ᶠ[𝓝 x] (fun _ => (1 : ℂ)) :=
      Filter.mem_of_superset (hB.mem_nhds hx) hg
    rw [hh.fderiv_eq]
    simp only [fderiv_fun_const]
    rfl
  have hχ (x : X) (hx : x∈B) : fiveCutoff R hR 0 x=1 := fiveCutoff_initial R hR (hBR hx)
  intro x hx
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [localizedLeading,Fin.cons_zero,add_apply,sum_apply,mult_apply _ ht,
      mult_apply _ (temperate_partial _ ht _),cut_apply,hd x hx,hg hx,Pi.one_apply,hχ x hx,
      zero_mul,one_mul,Finset.sum_const_zero,add_zero]
  · simp only [localizedLeading,Fin.cons_succ,mult_apply _ ht,cut_apply,hg hx,Pi.one_apply,hχ x hx,one_mul]
end ElasticityCGO

end
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

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
open Set MeasureTheory Filter TemperedDistribution
open scoped BigOperators SchwartzMap Topology
namespace Elasticity
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityDistribution (Coeff Dist LocalEq AugHilbert leadingRd leadingSd normald)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityNegativeOrder (sobNorm)
open ElasticityCGO

theorem dn_smooth_transport_column_oai {Ω B B' B₀ : Set X}
    (hΩ : IsOpen Ω) (hOB : Bornology.IsBounded Ω) (hB : IsOpen B)
    (hBB : Bornology.IsBounded B) (hB' : IsOpen B') (hsub : B'⊆B) (hcl : closure Ω⊆B')
    (R : ℝ) (hR : 1≤R) (hKR : closure Ω⊆Metric.closedBall 0 R)
    (hBR : B⊆Metric.ball 0 R) (α β : X) (hα : α≠0)
    (hθ : ∑ i,((α i : ℂ)+Complex.I*(β i : ℂ))*((α i : ℂ)+Complex.I*(β i : ℂ))=0)
    (lam m : Fin 2 → X → ℝ)
    (hl : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (lam q)) (hm : ∀ q,ContDiff ℝ (⊤ : ℕ∞) (m q))
    (hp : ∀ q x,0 < m q x ∧ 0<3*lam q x+2*m q x)
    (hcll : ∀ q,ExteriorConstant (smoothOfReal (lam q) (hl q)))
    (hclm : ∀ q,ExteriorConstant (smoothOfReal (m q) (hm q)))
    (he : ∀ x∉Ω,lam 0 x=lam 1 x ∧ m 0 x=m 1 x)
    (hDN : DN Ω (lam 0) (m 0)=DN Ω (lam 1) (m 1))
    (χ g η : Smooth) (hcχ : HasCompactSupport (χ : X → ℂ))
    (hc : HasCompactSupport (g : X → ℂ)) (hs : tsupport (g : X → ℂ)⊆B)
    (hχ : EqOn (χ : X → ℂ) 1 B) (hg : EqOn (g : X → ℂ) 1 B')
    (hcη : HasCompactSupport (η : X → ℂ)) (hsη : tsupport (η : X → ℂ)⊆Metric.ball 0 R)
    (hη : EqOn (η : X → ℂ) 1 B)
    (a : ℕ → Amplitude Smooth)
    (ha : PhysicalColumn R hR α β (smoothOfReal (lam 0) (hl 0)) (smoothOfReal (m 0) (hm 0)) a)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(ElasticityAugmented.div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
    (hB₀ : IsOpen B₀) (hKB₀ : closure Ω⊆B₀)
    (ρ : Smooth) (hcρ : HasCompactSupport (ρ : X → ℂ))
    (hρs : tsupport (ρ : X → ℂ)⊆B') (hρ1 : EqOn (ρ : X → ℂ) 1 B₀) :
    let θ := fun i => (α i : ℂ)+Complex.I*(β i : ℂ)
    ∃ v : Fin 4 → Smooth,
      (∀ i,tsupport ((v i-(Fin.cons (a 0).2 (a 0).1 : Fin 4 → Smooth) i : Smooth) : X → ℂ)⊆closure Ω) ∧
      (∀ i,EqOn (leadingR coord θ (smoothOfReal (lam 1) (hl 1)) (smoothOfReal (m 1) (hm 1))
        (fun j => v j.succ) (v 0) i).val 0 B') ∧
      EqOn (leadingS coord θ (smoothOfReal (lam 1) (hl 1)) (smoothOfReal (m 1) (hm 1))
        (fun j => v j.succ) (v 0)).val 0 B' ∧
      normal θ (fun j => v j.succ)=0 := by
  intro θ
  let l := smoothOfReal (lam 1) (hl 1)
  let μ := smoothOfReal (m 1) (hm 1)
  let L : Coeff := ⟨l,(hcll 1).growth⟩
  let M : Coeff := ⟨μ,(hclm 1).growth⟩
  have hm0 : ∀ x,(μ : X → ℂ) x≠0 := fun x => Complex.ofReal_ne_zero.mpr (hp 1 x).1.ne'
  have he0 : ∀ x,((l+μ+μ : Smooth) : X → ℂ) x≠0 := by
    intro x
    change (lam 1 x : ℂ)+(m 1 x : ℂ)+(m 1 x : ℂ)≠0
    exact_mod_cast (real_longitudinal_positive (lam 1) (m 1) (hp 1) x).ne'
  let n := ElasticityDistribution.inverseCoeff μ (hclm 1) hm0
  let o := ElasticityDistribution.inverseCoeff (l+μ+μ) (((hcll 1).add (hclm 1)).add (hclm 1)) he0
  have hn : n*M=1 := ElasticityDistribution.inverseCoeff_mul μ (hclm 1) hm0
  have ho : o*(L+M+M)=1 := by
    apply Subtype.ext
    exact ElasticityCoeffBounds.reciprocal_mul (l+μ+μ) he0
  have hne : θ≠0 := by
    intro hz
    apply hα
    ext i
    change α i=0
    have hh := congrArg Complex.re (congrFun hz i)
    simpa [θ] using hh
  obtain ⟨W,hRW,hS,hN,hE⟩ := dn_weak_transport_column hΩ hOB hB hBB hB' hsub hcl
    R hR hKR hBR α β hα hθ lam m hl hm hp hcll hclm he hDN χ g η hcχ hc hs hχ hg
    hcη hsη hη a ha h₀ hrec
  obtain ⟨v,hv,hvs⟩ := ElasticityDistribution.weak_leading_smooth hOB.isCompact_closure hB₀ hKB₀
    θ hθ hne L M n o hn ho W (localizedLeading R hR a η) hE hRW hS
    ρ (smooth_coe ρ) hcρ hρs hρ1
  have hR' : ∀ i,LocalEq B' (leadingRd θ L M (fun j => (v j.succ : Dist)) (v 0 : Dist) i) 0 := by
    simpa only [hv] using hRW
  have hS' : LocalEq B' (leadingSd θ L M (fun j => (v j.succ : Dist)) (v 0 : Dist)) 0 := by
    simpa only [hv] using hS
  have hN' : LocalEq B' (normald θ (fun j => (v j.succ : Dist))) 0 := by
    simpa only [hv] using hN
  exact ElasticityDistribution.smooth_column_patch hB' hcl θ L M v (localizedLeading R hR a η)
    (Fin.cons (a 0).2 (a 0).1) hvs
    (fun i => (localizedLeading_eqOn hB R hR hBR a η hcη hη i).mono hsub) hR' hS' hN' h₀
end Elasticity

end
end

end OAI
end

theorem solution : type_of% @OAI.Elasticity.dn_smooth_transport_column_oai := @OAI.Elasticity.dn_smooth_transport_column_oai
