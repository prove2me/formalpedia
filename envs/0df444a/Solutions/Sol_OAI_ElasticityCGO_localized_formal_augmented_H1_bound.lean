-- Prove2me | solution 1 for OAI.ElasticityCGO.localized_formal_augmented_H1_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:29:17.661114+00:00
-- url     : https://prove2.me/submissions/2d215134-532e-4676-b384-0d0c2376e38e

import Mathlib
import Definitions.Def_OAIQ6El006

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact differential-algebra identities of the physical and normalized
augmented elasticity systems. Smooth derivatives are constructed below;
commutation and Leibniz are proved, not postulated for the physical operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

omit [Fintype ι] in
lemma shifted_apply (z : ι → ℂ) (i : ι) (f : A) :
    shifted D z i f = D i f + z i • f := rfl

end CovariantAlgebra

end ElasticityAugmented

end

end OAI
end

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
namespace ElasticityBessel

lemma temperate_weight (h s : ℝ) : (weight h s).HasTemperateGrowth := by
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow X (s/2)).comp
    (((2*Real.pi*h) • ContinuousLinearMap.id ℝ X).hasTemperateGrowth)

lemma temperate_complex_weight (h s : ℝ) :
    (fun x => (weight h s x : ℂ)).HasTemperateGrowth := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp (temperate_weight h s)

lemma weight_add (h s t : ℝ) (x : X) : weight h (s+t) x = weight h s x * weight h t x := by
  simp only [weight, add_div]
  exact Real.rpow_add (by positivity) _ _

@[simp] lemma M_apply (h s : ℝ) (f : S) (x : X) :
    M h s f x = (weight h s x : ℂ)*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (temperate_complex_weight h s) f x

lemma M_add (h s t : ℝ) (f : S) : M h (s+t) f = M h s (M h t f) := by
  ext x
  simp only [M_apply, weight_add, Complex.ofReal_mul]
  ring

@[simp] lemma M_zero (h : ℝ) (f : S) : M h 0 f = f := by
  ext x
  simp only [M_apply, weight_zero, Complex.ofReal_one, one_mul]

lemma fourier_J (h s : ℝ) (f : S) : 𝓕 (J h s f) = M h s (𝓕 f) := by
  simp only [J, FourierTransform.fourier_fourierInv_eq]

lemma J_add_order (h s t : ℝ) (f : S) : J h (s+t) f = J h s (J h t f) := by
  simp only [J, FourierTransform.fourier_fourierInv_eq, M_add]

@[simp] lemma J_zero (h : ℝ) (f : S) : J h 0 f = f := by
  simp only [J, M_zero, FourierTransform.fourierInv_fourier_eq]

lemma J_add (h s : ℝ) (f g : S) : J h s (f+g) = J h s f + J h s g := by
  simp only [J, FourierTransform.fourier_add, map_add, FourierTransform.fourierInv_add]

lemma J_smul (h s : ℝ) (a : ℂ) (f : S) : J h s (a • f) = a • J h s f := by
  simp only [J, FourierTransform.fourier_smul, map_smul, FourierTransform.fourierInv_smul]

lemma norm2_nonneg (f : S) : 0 ≤ norm2 f := norm_nonneg _

lemma norm2_add_le (f g : S) : norm2 (f+g) ≤ norm2 f + norm2 g := by
  simpa only [norm2, map_add] using norm_add_le (L2 f) (L2 g)

lemma norm2_const_smul (a : ℂ) (f : S) : norm2 (a • f) = ‖a‖*norm2 f := by
  simp only [norm2, map_smul, norm_smul]

lemma ip_integral (f g : S) : ip f g = ∫ x : X, star (f x) * g x := by
  simpa only [ip, L2, SchwartzMap.toLpCLM_apply, RCLike.inner_apply', RCLike.star_def]
    using SchwartzMap.inner_toL2_toL2_eq f g volume

lemma norm2_sq (f : S) : norm2 f ^ 2 = (ip f f).re := by
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (L2 f)).symm

lemma ip_fourier (f g : S) : ip (𝓕 f) (𝓕 g) = ip f g :=
  SchwartzMap.inner_fourier_toL2_eq f g

lemma ip_M (h s : ℝ) (f g : S) : ip (M h s f) g = ip f (M h s g) := by
  simp only [ip_integral]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [M_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

lemma ip_J (h s : ℝ) (f g : S) : ip (J h s f) g = ip f (J h s g) := by
  rw [← ip_fourier (J h s f) g, ← ip_fourier f (J h s g), fourier_J, fourier_J]
  exact ip_M h s _ _

lemma norm2_J_sq (h s : ℝ) (f : S) :
    norm2 (J h s f)^2 = (ip f (J h (s+s) f)).re := by
  rw [norm2_sq, ip_J, ← J_add_order]

end ElasticityBessel

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap
namespace ElasticitySchwartzCarleman

lemma smooth (f : Test) : ContDiff ℝ (⊤ : ℕ∞) (f : X → ℂ) := f.smooth _

lemma deriv_conj (f : Test) (z v : X) :
    fderiv ℝ (fun z => star (f z)) z v = star (fderiv ℝ (f : X → ℂ) z v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    ((smooth f).differentiable (by simp) z).hasFDerivAt).fderiv
  exact congrArg (fun L : X →L[ℝ] ℂ => L v) h

lemma integrable_pair (f g : Test) : Integrable (fun z : X => star (f z)*g z) := by
  have hi := (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℂ)
    (f.postcompCLM Complex.conjCLE.toContinuousLinearMap) g).integrable (μ := volume)
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  rfl

lemma pair_add_right (f g h : Test) : pair f (g+h) = pair f g + pair f h := by
  simpa only [pair, FunLike.coe_add, Pi.add_apply, mul_add] using
    integral_add (integrable_pair f g) (integrable_pair f h)

lemma pair_sub_right (f g h : Test) : pair f (g-h) = pair f g - pair f h := by
  simpa only [pair, FunLike.coe_sub, Pi.sub_apply, mul_sub] using
    integral_sub (integrable_pair f g) (integrable_pair f h)

lemma pair_smul_right (f g : Test) (a : ℂ) : pair f (a • g) = a * pair f g := by
  simp only [pair, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc, mul_comm (star (f _)) a, mul_assoc]
  exact integral_const_mul a _

lemma pair_d (f g : Test) (v : X) : pair f (d v g) = -pair (d v f) g := by
  have h1 : Integrable (fun z : X => fderiv ℝ (fun z => star (f z)) z v * g z) := by
    simpa only [deriv_conj, d_apply] using integrable_pair (d v f) g
  have h2 : Integrable (fun z : X => star (f z)*fderiv ℝ (g : X → ℂ) z v) :=
    integrable_pair f (d v g)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable h1 h2 (integrable_pair f g)
    (fun z _ => Complex.conjCLE.differentiableAt.comp z ((smooth f).differentiable (by simp) z))
    (fun z _ => (smooth g).differentiable (by simp) z)
    |>.trans (by simp only [pair, deriv_conj, d_apply])

lemma mass_integral (f : Test) : mass f = ∫ z : X, Complex.normSq (f z) := by
  have h := integral_re (integrable_pair f f)
  simpa only [mass, pair, Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    RCLike.re_to_complex, Complex.ofReal_re] using h.symm

lemma mass_nonneg (f : Test) : 0 ≤ mass f := by
  rw [mass_integral]
  exact integral_nonneg fun _ => Complex.normSq_nonneg _

lemma lap_apply (f : Test) : lap f = d (e 0) (d (e 0) f) +
    d (e 1) (d (e 1) f) + d (e 2) (d (e 2) f) := by
  simp [lap, Fin.sum_univ_three]

lemma gradientMass_nonneg (f : Test) : 0 ≤ gradientMass f :=
  Finset.sum_nonneg fun _ _ => mass_nonneg _

lemma lap_energy (f : Test) : (pair f (lap f)).re = -gradientMass f := by
  simp only [gradientMass, lap_apply, Fin.sum_univ_three, pair_add_right,
    pair_d, Complex.add_re, Complex.neg_re, mass]
  ring

end ElasticitySchwartzCarleman

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

lemma fourier_d (i : Fin 3) (f : S) (x : X) :
    𝓕 (d (e i) f) x = (2*Real.pi*Complex.I)*(x i : ℂ)*𝓕 f x := by
  have ht : (inner ℝ · (e i)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (e i)).hasTemperateGrowth
  change 𝓕 (∂_{e i} f) x = _
  simp only [SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply ht, Complex.real_smul, smul_eq_mul]
  simp only [e, EuclideanSpace.inner_single_right, conj_trivial, one_mul]
  ring

lemma J_two (h : ℝ) (f : S) : J h 2 f = f - (h : ℂ)^2 • lap f := by
  apply (FourierTransform.fourierCLE ℂ S).injective
  rw [map_sub, map_smul]
  simp only [FourierTransform.fourierCLE_apply, fourier_J, lap_apply,
    FourierTransform.fourier_add]
  ext x
  simp only [M_apply, weight_two, sub_apply, add_apply, smul_apply, smul_eq_mul,
    fourier_d, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three,
    PiLp.smul_apply, smul_eq_mul]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma H1_energy (h : ℝ) (f : S) :
    norm2 (J h 1 f)^2 = mass f + h^2*gradientMass f := by
  rw [norm2_J_sq]
  norm_num only [show (1:ℝ)+1=2 by norm_num]
  rw [J_two, ip_integral]
  change (pair f (f-(h:ℂ)^2 • lap f)).re = _
  rw [pair_sub_right, pair_smul_right]
  have hc : (h:ℂ)^2 = ((h^2:ℝ):ℂ) := by push_cast; rfl
  rw [hc]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, lap_energy, mass]
  ring

lemma mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (f : S) (x : X) :
    mult a f x = a x * f x :=
  SchwartzMap.smulLeftCLM_apply_apply ha f x

lemma d_mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (v : X)
    (f : S) (x : X) :
    d v (mult a f) x = a x * d v f x + fderiv ℝ a x v * f x := by
  rw [d_apply]
  have he : (mult a f : X → ℂ) = a * (f : X → ℂ) := by
    funext y
    exact mult_apply a ha f y
  rw [he, fderiv_mul (ha.1.differentiable (by simp) x) (f.differentiable x)]
  simp only [add_apply, smul_apply,
    smul_eq_mul, d_apply]
  ring

lemma norm2_sum_le {ι : Type*} (T : Finset ι) (f : ι → S) :
    norm2 (∑ i ∈ T, f i) ≤ ∑ i ∈ T, norm2 (f i) := by
  simpa only [norm2, map_sum] using norm_sum_le T (fun i => L2 (f i))

lemma sumNorm_nonneg {n : ℕ} (h s : ℝ) (U : Fin n → S) : 0 ≤ sumNorm h s U :=
  Finset.sum_nonneg (fun _ _ => norm2_nonneg _)

lemma sobNorm_le_sumNorm {n : ℕ} (h s : ℝ) (U : Fin n → S) :
    sobNorm h s U ≤ sumNorm h s U := by
  have hn : 0 ≤ ∑ i, norm2 (J h s (U i))^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have ht := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => norm2 (J h s (U i))) (fun _ _ => norm2_nonneg _)
  dsimp only [sobNorm, sumNorm]
  have hsum := sumNorm_nonneg h s U
  dsimp only [sumNorm] at hsum
  nlinarith only [hs, ht, hsum, Real.sqrt_nonneg (∑ i, norm2 (J h s (U i))^2)]

end

end ElasticityNegativeOrder

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma J_sum {ι : Type*} (T : Finset ι) (h s : ℝ) (f : ι → S) :
    J h s (∑ i ∈ T, f i) = ∑ i ∈ T, J h s (f i) := by
  simp only [J, FourierTransform.fourier_sum, map_sum, FourierTransform.fourierInv_sum]

end ElasticityPhysicalEstimate

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma toSmooth_d (f : S) (i : Fin 3) :
    toSmooth (d (e i) f) = ElasticityAugmented.coord i (toSmooth f) := by
  apply Subtype.ext
  rfl

lemma shiftD_apply (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    shiftD z i f = d (e i) f + z i • f := rfl

lemma toSmooth_shiftD (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    toSmooth (shiftD z i f) = ElasticityAugmented.shifted ElasticityAugmented.coord z i (toSmooth f) := by
  simp only [shiftD_apply, map_add, map_smul, toSmooth_d, ElasticityAugmented.shifted_apply]

lemma toSmooth_divShift (z : Fin 3 → ℂ) (u : Fin 3 → S) :
    toSmooth (divShift z u) =
      ElasticityAugmented.divT (ElasticityAugmented.shifted ElasticityAugmented.coord z) (fun i => toSmooth (u i)) := by
  simp only [divShift, ElasticityAugmented.divT, map_sum, toSmooth_shiftD]

end ElasticityPhysicalAlgebra

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_TransportAlgebra
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section FiniteExpansion
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
lemma truncation_zero (h : ℂ) (a : ℕ → V) : truncation h 0 a=a 0 := by simp [truncation]
lemma truncation_succ (h : ℂ) (N : ℕ) (a : ℕ → V) :
    truncation h (N+1) a=truncation h N a+h^(N+1) • a (N+1) := by
  exact Finset.sum_range_succ _ _

/-- Exact finite telescoping, not an asymptotic formal series. -/
lemma truncated_transport (L T : V →ₗ[ℂ] W) (h : ℂ) (hh : h ≠ 0) (N : ℕ) (a : ℕ → V)
    (h₀ : T (a 0)=0) (hrec : ∀ j<N, T (a (j+1))=-L (a j)) :
    L (truncation h N a)+h⁻¹ • T (truncation h N a)=h^N • L (a N) := by
  induction N with
  | zero => simp only [truncation_zero,h₀,smul_zero,add_zero,pow_zero,one_smul]
  | succ N ih =>
    have hn := ih (fun j hj => hrec j (hj.trans (Nat.lt_succ_self N)))
    have hp : h⁻¹*h^(N+1)=h^N := by rw [pow_succ]; field_simp
    simp only [truncation_succ,map_add,map_smul,smul_add,smul_smul,hp,hrec N (Nat.lt_succ_self N),smul_neg]
    rw [← hn]
    abel
end FiniteExpansion
section PhysicalRecursion
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)

lemma divT_expansion (θ : Fin 3 → ℂ) (h : ℂ) (u : Fin 3 → A) :
    divT (shifted D (h • θ)) u=div D u+h • normal θ u := by
  simp only [divT,div,normal,shifted_apply,Pi.smul_apply,smul_eq_mul,
    Finset.sum_add_distrib,smul_smul,Finset.smul_sum]

/-- The physical divergence constraint telescopes independently. -/
lemma truncated_divergence (θ : Fin 3 → ℂ) (h : ℂ) (hh : h ≠ 0) (N : ℕ) (a : ℕ → Amplitude A)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N, normal θ (a (j+1)).1=-(div D (a j).1-(a j).2)) :
    divT (shifted D (h⁻¹ • θ)) (truncation h N a).1 =
      (truncation h N a).2+h^N • (div D (a N).1-(a N).2) := by
  rw [divT_expansion]
  have ht := truncated_transport (divergenceDefect D) (normalPair θ) h hh N a h₀ hrec
  change div D (truncation h N a).1-(truncation h N a).2+h⁻¹ • normal θ (truncation h N a).1=h^N • (div D (a N).1-(a N).2) at ht
  linear_combination ht
end PhysicalRecursion
end ElasticityAugmented

end
end
section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityAugmented

lemma localCoord_restrict {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth) :
    localCoord hU i (restrictSmooth U f)=restrictSmooth U (coord i f) := by
  exact Derivation.liftOfSurjective_apply (restrictSmooth_surjective U) (restrict_coord_zero hU i) f

lemma restrict_div {U : Set X} (hU : IsOpen U) (a : Fin 3 → Smooth) :
    restrictSmooth U (div coord a)=div (localCoord hU) (fun i => restrictSmooth U (a i)) := by
  simp only [div,map_sum,localCoord_restrict]
lemma restrict_normal (U : Set X) (θ : Fin 3 → ℂ) (a : Fin 3 → Smooth) :
    restrictSmooth U (normal θ a)=normal θ (fun i => restrictSmooth U (a i)) := by
  simp only [normal,map_sum,map_smul]
end ElasticityAugmented

end
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

namespace ElasticityAugmented
open Set
open scoped BigOperators

lemma localAmp_truncation (U : Set X) (h : ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth) :
    localAmp U (truncation h N a)=truncation h N (fun j => localAmp U (a j)) := by
  exact map_sum (localAmpLM U) _ _ |>.trans (by simp only [map_smul]; rfl)
lemma restrict_shifted {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (i : Fin 3) (f : Smooth) :
    restrictSmooth U (shifted coord z i f)=shifted (localCoord hU) z i (restrictSmooth U f) := by
  simp only [shifted_apply,map_add,map_smul,localCoord_restrict]
end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transfer
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply physical phase)
open ElasticityDistribution (finiteResidual)
lemma cut_local {U : Set X} (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 U) (f : Smooth) :
    restrictSmooth U (toSmooth (cut χ hc f))=restrictSmooth U f := by
  apply (restrictSmooth_eq_iff U _ _).mpr
  intro x hx
  simp only [toSmooth_apply,cut_apply,hχ hx,Pi.one_apply,one_mul]
end ElasticityCGO

end
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

namespace ElasticityCGO
open Set MeasureTheory TemperedDistribution

open scoped SchwartzMap LineDeriv BigOperators ENNReal
open ElasticityRegularity ElasticityAugmented
open ElasticityBessel (norm2 J)
open ElasticityNegativeOrder (mult sobNorm sumNorm)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityDistribution (HV Dist divd)

lemma divShift_mult (z : Fin 3 → ℂ) (g : X → ℂ) (hg : g.HasTemperateGrowth)
    (v : Fin 3 → S) :
    ElasticityPhysicalAlgebra.divShift z (fun i => mult g (v i))=
      mult g (ElasticityPhysicalAlgebra.divShift z v)+
        ∑ i,mult (fun x => fderiv ℝ g x (e i)) (v i) := by
  have hd (i : Fin 3) : (fun x => fderiv ℝ g x (e i)).HasTemperateGrowth :=
    ElasticityPhysicalAlgebra.temperate_partial g hg (e i)
  ext x
  simp only [ElasticityPhysicalAlgebra.divShift,sum_apply,
    ElasticityPhysicalAlgebra.shiftD_apply,add_apply,smul_apply,
    ElasticityNegativeOrder.d_mult_apply g hg,
    ElasticityNegativeOrder.mult_apply g hg,
    ElasticityNegativeOrder.mult_apply _ (hd _),smul_eq_mul,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [ElasticitySchwartzCarleman.e,ElasticityAugmented.e]
  ring

end ElasticityCGO
section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityAugmented
lemma restrict_divT {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (a : Fin 3 → Smooth) :
    restrictSmooth U (divT (shifted coord z) a)=
      divT (shifted (localCoord hU) z) (fun j => restrictSmooth U (a j)) := by
  simp only [divT,map_sum,restrict_shifted hU]

/-- The actual finite divergence constraint on an open physical region. -/
theorem truncation_divergence_on {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (h : ℂ) (hh : h≠0) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U) :
    EqOn ((divT (shifted coord (h⁻¹ • θ)) (truncation h N a).1 : Smooth) : X → ℂ)
      (((truncation h N a).2+h^N • (div coord (a N).1-(a N).2) : Smooth) : X → ℂ) U := by
  have hn₀ : normal θ (localAmp U (a 0)).1=0 := by
    simp only [localAmp,← restrict_normal,h₀,map_zero]
  have hn (j) (hj : j<N) : normal θ (localAmp U (a (j+1))).1=
      -(div (localCoord hU) (localAmp U (a j)).1-(localAmp U (a j)).2) := by
    have he := (restrictSmooth_eq_iff U _ _).mpr (hrec j hj)
    simpa only [restrict_normal,map_neg,map_sub,restrict_div hU,localAmp] using he
  have ht := truncated_divergence (localCoord hU) θ h hh N (fun j => localAmp U (a j)) hn₀ hn
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [restrict_divT hU]
  change divT (shifted (localCoord hU) (h⁻¹ • θ)) (localAmp U (truncation h N a)).1=_
  rw [localAmp_truncation,ht]
  simp only [map_add,map_smul,map_sub,restrict_div hU]
  congr 1
  exact congrArg Prod.snd (localAmp_truncation U h N a).symm
end ElasticityAugmented

namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply toSmooth_divShift divShift)
lemma divShift_cut_local {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 U) (u : Fin 3 → Smooth) :
    EqOn (divShift z (fun j => cut χ hc (u j)) : X → ℂ)
      ((divT (shifted coord z) u : Smooth) : X → ℂ) U := by
  change EqOn ((toSmooth (divShift z (fun j => cut χ hc (u j))) : Smooth) : X → ℂ) _ U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_divShift,restrict_divT hU,restrict_divT hU]
  congr 1
  funext j
  exact cut_local χ hc hχ (u j)

/-- The exact scalar augmented amplitude has the same eight-order truncation
plus a single h^8 defect. No unjustified differentiation of small L2 errors. -/
theorem cut_truncation_divergence {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (h : ℂ) (hh : h≠0) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U) :
    EqOn (divShift (h⁻¹ • θ) (fun j => cut χ hc ((truncation h N a).1 j)) : X → ℂ)
      (cut χ hc ((truncation h N a).2+h^N • (div coord (a N).1-(a N).2))) U := by
  intro x hx
  rw [divShift_cut_local hU _ χ hc hχ _ hx,truncation_divergence_on hU θ h hh N a h₀ hrec hx,
    cut_apply,hχ hx]
  exact (one_mul _).symm
end ElasticityCGO

end
namespace ElasticityCGO

section
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2 norm2_nonneg J_smul norm2_const_smul)
open ElasticityNegativeOrder (H1_energy)
open ElasticitySchwartzCarleman (gradientMass_nonneg)

lemma semiclassical_H1_le_H1 (h : ℝ) (hh : 0≤h) (hh1 : h≤1) (f : S) :
    norm2 (J h 1 f)≤norm2 (J 1 1 f) := by
  have hsq : h^2≤1 := by nlinarith
  have he := H1_energy h f
  have he1 := H1_energy 1 f
  have hm := mul_le_mul_of_nonneg_right hsq (gradientMass_nonneg f)
  norm_num only [one_pow,one_mul] at he1 hm
  nlinarith only [he,he1,hm,norm2_nonneg (J h 1 f),norm2_nonneg (J 1 1 f)]

/-- A literal finite Schwartz amplitude polynomial is uniformly bounded
in the semiclassical H1 norm. There is no h-dependent Sobolev constant. -/
theorem finite_polynomial_H1_bound (N : ℕ) (f : ℕ → S) (h : ℝ)
    (hh : 0≤h) (hh1 : h≤1) :
    norm2 (J h 1 (truncation (h : ℂ) N f))≤
      ∑ j ∈ Finset.range (N+1),norm2 (J 1 1 (f j)) := by
  rw [truncation,ElasticityPhysicalEstimate.J_sum]
  apply (ElasticityNegativeOrder.norm2_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [J_smul,norm2_const_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh]
  calc
    _ ≤ 1*norm2 (J h 1 (f j)) :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hh hh1) (norm2_nonneg _)
    _ ≤ norm2 (J 1 1 (f j)) := by simpa only [one_mul] using semiclassical_H1_le_H1 h hh hh1 (f j)

lemma cut_truncation (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (h : ℂ) (N : ℕ) (a : ℕ → Smooth) :
    cut χ hc (truncation h N a)=truncation h N (fun j => cut χ hc (a j)) := by
  simp only [truncation,map_sum,map_smul]

end
open Set
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2 norm2_nonneg J_smul norm2_const_smul)
open ElasticityNegativeOrder (mult mult_apply)
open ElasticityPhysicalAlgebra (divShift)

lemma truncation_scalar (h : ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth) :
    (truncation h N a).2=truncation h N (fun j => (a j).2) := by
  induction N with
  | zero => simp only [truncation_zero]
  | succ N ih =>
    rw [truncation_succ,truncation_succ]
    change (truncation h N a).2+h^(N+1) • (a (N+1)).2=_
    rw [ih]
lemma truncation_vector (h : ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth) (i : Fin 3) :
    (truncation h N a).1 i=truncation h N (fun j => (a j).1 i) := by
  induction N with
  | zero => simp only [truncation_zero]
  | succ N ih =>
    rw [truncation_succ,truncation_succ]
    change (truncation h N a).1 i+h^(N+1) • (a (N+1)).1 i=_
    rw [ih]

lemma mult_eq_of_local {U : Set X} {g : X → ℂ} (hg : g.HasTemperateGrowth)
    (hs : tsupport g⊆U) {f k : S} (hf : EqOn (f : X → ℂ) k U) :
    mult g f=mult g k := by
  ext x
  rw [mult_apply g hg,mult_apply g hg]
  by_cases h : g x=0
  · simp only [h,zero_mul]
  · rw [hf (hs (subset_tsupport _ h))]

lemma H1_monomial_bound (h : ℝ) (hh : 0≤h) (hh1 : h≤1) (N : ℕ) (f : S) :
    norm2 (J h 1 ((h : ℂ)^N • f))≤norm2 (J 1 1 f) := by
  rw [J_smul,norm2_const_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh]
  exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hh hh1) (norm2_nonneg _)).trans
    (by simpa only [one_mul] using semiclassical_H1_le_H1 h hh hh1 f)

/-- The formal divergence, localized strictly inside the physical region,
is uniformly H_h^1 bounded. The apparent h⁻¹ term is removed by the actual
finite divergence recurrence, not by estimating an independent scalar. -/
theorem localized_formal_divergence_H1_bound {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆U) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0<h → h≤1 →
      norm2 (J h 1 (mult g (divShift ((h : ℂ)⁻¹ • θ)
        (fun j => cut χ hc ((truncation (h : ℂ) N a).1 j)))))≤C := by
  let b : ℕ → S := fun j => mult g (cut χ hc (a j).2)
  let d : S := mult g (cut χ hc (div coord (a N).1-(a N).2))
  let B := ∑ j ∈ Finset.range (N+1),norm2 (J 1 1 (b j))
  let D := norm2 (J 1 1 d)
  have hB : 0≤B := Finset.sum_nonneg (fun j _ => norm2_nonneg _)
  have hD : 0≤D := norm2_nonneg _
  refine ⟨1+B+D,by linarith only [hB,hD],fun h hh hh1 => ?_⟩
  have he := cut_truncation_divergence hU θ (h : ℂ) (Complex.ofReal_ne_zero.mpr hh.ne')
    N a h₀ hrec χ hc hχ
  rw [mult_eq_of_local hg hs he]
  have hp : mult g (cut χ hc ((truncation (h : ℂ) N a).2+
      (h : ℂ)^N • (div coord (a N).1-(a N).2)))=
      truncation (h : ℂ) N b+(h : ℂ)^N • d := by
    rw [truncation_scalar]
    simp only [map_add,map_smul,cut_truncation]
    simp only [truncation,map_sum,map_smul,b,d]
  rw [hp,ElasticityBessel.J_add]
  calc
    _ ≤ norm2 (J h 1 (truncation (h : ℂ) N b))+norm2 (J h 1 ((h : ℂ)^N • d)) :=
      ElasticityBessel.norm2_add_le _ _
    _ ≤ B+D := add_le_add (finite_polynomial_H1_bound N b h hh.le hh1)
      (H1_monomial_bound h hh.le hh1 N d)
    _ ≤ 1+B+D := by linarith
end ElasticityCGO
namespace ElasticityCGO
open Set
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2 norm2_nonneg)
open ElasticityNegativeOrder (mult sobNorm sumNorm)
open ElasticityPhysicalAlgebra (divShift)
open ElasticityPhysicalEstimate (physicalAug)

lemma mult_cut_truncation_vector (g : X → ℂ) (χ : Smooth)
    (hc : HasCompactSupport (χ : X → ℂ)) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h : ℂ) (i : Fin 3) :
    mult g (cut χ hc ((truncation h N a).1 i))=
      truncation h N (fun j => mult g (cut χ hc ((a j).1 i))) := by
  rw [truncation_vector,cut_truncation]
  simp only [truncation,map_sum,map_smul]

/-- Fixed interior localization of the whole formal physical displacement
has a uniformly bounded ACTUAL four-component H_h^1 amplitude. The singular
phase is cancelled by the actual divergence recurrence. -/
theorem localized_formal_augmented_H1_bound_oai {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆U) :
    ∃ C : ℝ,0<C ∧ ∀ h : ℝ,0<h → h≤1 →
      sobNorm h 1 (physicalAug ((h : ℂ)⁻¹ • θ)
        (fun i => mult g (cut χ hc ((truncation (h : ℂ) N a).1 i))))≤C := by
  obtain ⟨C,hC,hscalar⟩ := localized_formal_divergence_H1_bound hU θ N a h₀ hrec χ hc hχ hg hs
  let dg : Fin 3 → X → ℂ := fun i x => fderiv ℝ g x (e i)
  let B : Fin 3 → ℝ := fun i => ∑ j ∈ Finset.range (N+1),
    norm2 (J 1 1 (mult g (cut χ hc ((a j).1 i))))
  let D : Fin 3 → ℝ := fun i => ∑ j ∈ Finset.range (N+1),
    norm2 (J 1 1 (mult (dg i) (cut χ hc ((a j).1 i))))
  have hB (i) : 0≤B i := Finset.sum_nonneg (fun j _ => norm2_nonneg _)
  have hD (i) : 0≤D i := Finset.sum_nonneg (fun j _ => norm2_nonneg _)
  have hBs : 0≤∑ i,B i := Finset.sum_nonneg (fun i _ => hB i)
  have hDs : 0≤∑ i,D i := Finset.sum_nonneg (fun i _ => hD i)
  refine ⟨C+(∑ i,D i)+(∑ i,B i),by linarith only [hC,hBs,hDs],fun h hh hh1 => ?_⟩
  let u : Fin 3 → S := fun i => cut χ hc ((truncation (h : ℂ) N a).1 i)
  have hv (i : Fin 3) : norm2 (J h 1 (mult g (u i)))≤B i := by
    dsimp only [u]
    rw [mult_cut_truncation_vector]
    exact finite_polynomial_H1_bound N _ h hh.le hh1
  have hd (i : Fin 3) : norm2 (J h 1 (mult (dg i) (u i)))≤D i := by
    dsimp only [u]
    rw [mult_cut_truncation_vector]
    exact finite_polynomial_H1_bound N _ h hh.le hh1
  have hsc : norm2 (J h 1 (divShift ((h : ℂ)⁻¹ • θ) (fun i => mult g (u i))))≤C+∑ i,D i := by
    rw [divShift_mult _ g hg,ElasticityBessel.J_add,ElasticityPhysicalEstimate.J_sum]
    apply (ElasticityBessel.norm2_add_le _ _).trans
    exact add_le_add (hscalar h hh hh1)
      ((ElasticityNegativeOrder.norm2_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hd i)))
  apply (ElasticityNegativeOrder.sobNorm_le_sumNorm h 1 _).trans
  change (∑ i : Fin 4,norm2 (J h 1 (physicalAug ((h : ℂ)⁻¹ • θ)
    (fun j => mult g (u j)) i)))≤_
  rw [Fin.sum_univ_succ]
  exact add_le_add hsc (Finset.sum_le_sum (fun i _ => hv i))
end ElasticityCGO

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityCGO.localized_formal_augmented_H1_bound_oai := @OAI.ElasticityCGO.localized_formal_augmented_H1_bound_oai
