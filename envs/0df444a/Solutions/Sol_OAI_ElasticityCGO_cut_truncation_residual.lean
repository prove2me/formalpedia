-- Prove2me | solution 1 for OAI.ElasticityCGO.cut_truncation_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:12:44.917884+00:00
-- url     : https://prove2.me/submissions/54b8de23-dcf5-4236-8f0f-5769b7ff05a2

import Mathlib
import Definitions.Def_OAIQ6El004
import Definitions.Def_OAIQ6El005

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
attribute [-instance] _root_.OAI.ElasticityDistribution.instIsCentralScalarSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexMulOppositeSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instIsScalarTowerComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instModuleSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulCommClassComplexSubtypeForallXMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulMulOppositeSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityDistribution.instSMulSubtypeForallXComplexMemSubalgebraSmoothCoeffDist _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
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

lemma coord_coord (f : Smooth) (i j : Fin 3) (x : X) :
    (coord i (coord j f) : X → ℂ) x = fderiv ℝ (fderiv ℝ (f : X → ℂ)) x (e i) (e j) := by
  have hd : Differentiable ℝ (fderiv ℝ (f : X → ℂ)) :=
    ((smooth_coe f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : X → ℂ) y (e j)) x (e i) = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const (e j))]
  simp

lemma coord_commute (i j : Fin 3) (f : Smooth) : coord i (coord j f) = coord j (coord i f) := by
  apply Subtype.ext
  funext x
  rw [coord_coord, coord_coord]
  exact (smooth_coe f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A)

omit [Fintype ι] in
lemma partial_mul (i : ι) (a b : A) : D i (a*b) = D i a*b + a*D i b := by
  simpa only [smul_eq_mul, add_comm, mul_comm] using (D i).leibniz a b

end DifferentialAlgebra

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

include hT hTD in
lemma physical_conjugated_expansion (lam m : A) (u : ι → A) (i : ι) :
    LT T lam m u i = RT D T lam m u (divT T u) i := by
  have ht : (∑ j, T j (T i (u j))) = T i (divT T u) := by
    simp only [divT, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hT j i]
  simp only [LT, RT, hTD, map_add, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [ht]
  simp only [cmT, lapT, mul_add, Finset.sum_add_distrib]
  ring

omit [Fintype ι] in
lemma shifted_apply (z : ι → ℂ) (i : ι) (f : A) :
    shifted D z i f = D i f + z i • f := rfl

omit [Fintype ι] in
lemma shifted_mul (z : ι → ℂ) (i : ι) (a b : A) :
    shifted D z i (a*b) = D i a*b+a*shifted D z i b := by
  simp only [shifted_apply, partial_mul, Algebra.smul_def]
  ring

include hD in
omit [Fintype ι] in
lemma shifted_commute (z : ι → ℂ) (i j : ι) (f : A) :
    shifted D z i (shifted D z j f) = shifted D z j (shifted D z i f) := by
  simp only [shifted_apply, map_add, map_smul, smul_add, smul_smul, hD i j]
  simp only [Algebra.smul_def]
  ring_nf

theorem shifted_physical_expansion (z : ι → ℂ) (lam m : A) (u : ι → A)
    (hc : ∀ i j f, D i (D j f) = D j (D i f)) (i : ι) :
    LT (shifted D z) lam m u i = RT D (shifted D z) lam m u (divT (shifted D z) u) i :=
  physical_conjugated_expansion D (shifted D z) (shifted_commute D hc z) (shifted_mul D z) lam m u i

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

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder

lemma toSmooth_d (f : S) (i : Fin 3) :
    toSmooth (d (e i) f) = ElasticityAugmented.coord i (toSmooth f) := by
  apply Subtype.ext
  rfl

lemma toSmooth_mult (a : Smooth) (ha : (a : X → ℂ).HasTemperateGrowth) (f : S) :
    toSmooth (mult a f) = a*toSmooth f := by
  apply Subtype.ext
  funext x
  exact mult_apply a ha f x

lemma shiftD_apply (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    shiftD z i f = d (e i) f + z i • f := rfl

lemma toSmooth_shiftD (z : Fin 3 → ℂ) (i : Fin 3) (f : S) :
    toSmooth (shiftD z i f) = ElasticityAugmented.shifted ElasticityAugmented.coord z i (toSmooth f) := by
  simp only [shiftD_apply, map_add, map_smul, toSmooth_d, ElasticityAugmented.shifted_apply]

lemma toSmooth_physical (z : Fin 3 → ℂ) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (u : Fin 3 → S) (i : Fin 3) :
    toSmooth (physical z lam m u i) =
      ElasticityAugmented.LT (ElasticityAugmented.shifted ElasticityAugmented.coord z)
        lam m (fun j => toSmooth (u j)) i := by
  simp only [physical, ElasticityAugmented.LT, ElasticityAugmented.divT, map_add, map_sum,
    toSmooth_shiftD, toSmooth_mult lam hl, toSmooth_mult m hm,
    Finset.mul_sum, mul_add]

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
section CGO
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)

lemma RT_phase_polynomial (θ : Fin 3 → ℂ) (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A) :
    RT D (shifted D (τ • θ)) lam m u b =
      (fun i => R D lam m u b i+τ • leadingR D θ lam m u b i+
        (τ*τ*(∑ j, θ j*θ j)) • (m*u i)) := by
  funext i
  simp only [RT,R,cmT,cm,lapT,lap,shifted_apply,direction,leadingR,
    Pi.smul_apply,smul_eq_mul,Fin.sum_univ_three,map_add,Derivation.map_smul,smul_add]
  simp only [Algebra.smul_def,map_add,map_mul]
  ring

lemma RT_null_expansion (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0)
    (τ : ℂ) (lam m : A) (u : Fin 3 → A) (b : A) (i : Fin 3) :
    RT D (shifted D (τ • θ)) lam m u b i=R D lam m u b i+τ • leadingR D θ lam m u b i := by
  have hh := congrFun (RT_phase_polynomial D θ τ lam m u b) i
  simpa only [hθ,mul_zero,zero_smul,add_zero] using hh

end CGO
end ElasticityAugmented

end
end
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

lemma truncated_R (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (lam m : A)
    (h : ℂ) (hh : h ≠ 0) (N : ℕ) (a : ℕ → Amplitude A)
    (h₀ : leadingR D θ lam m (a 0).1 (a 0).2=0)
    (hrec : ∀ j<N, leadingR D θ lam m (a (j+1)).1 (a (j+1)).2=-R D lam m (a j).1 (a j).2) (i : Fin 3) :
    RT D (shifted D (h⁻¹ • θ)) lam m (truncation h N a).1 (truncation h N a).2 i=
      h^N • R D lam m (a N).1 (a N).2 i := by
  rw [RT_null_expansion D θ hθ]
  exact congrFun (truncated_transport (Rpair D lam m) (leadingRpair D θ lam m) h hh N a h₀ hrec) i

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
open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)

lemma RT_scalar_add (T : Fin 3 → A →ₗ[ℂ] A) (lam m : A) (u : Fin 3 → A) (b d : A) (i : Fin 3) :
    RT D T lam m u (b+d) i=RT D T lam m u b i+(lam+m)*T i d+D i lam*d := by
  simp only [RT,map_add,mul_add]
  ring

theorem truncated_physical_residual (hD : ∀ i j f, D i (D j f)=D j (D i f))
    (θ : Fin 3 → ℂ) (hθ : ∑ i, θ i*θ i=0) (lam m : A)
    (h : ℂ) (hh : h ≠ 0) (N : ℕ) (a : ℕ → Amplitude A)
    (hR₀ : leadingR D θ lam m (a 0).1 (a 0).2=0)
    (hRrec : ∀ j<N, leadingR D θ lam m (a (j+1)).1 (a (j+1)).2=-R D lam m (a j).1 (a j).2)
    (hn₀ : normal θ (a 0).1=0)
    (hnrec : ∀ j<N, normal θ (a (j+1)).1=-(div D (a j).1-(a j).2)) (i : Fin 3) :
    LT (shifted D (h⁻¹ • θ)) lam m (truncation h N a).1 i =
      h^N • (R D lam m (a N).1 (a N).2 i +
        (lam+m)*D i (div D (a N).1-(a N).2)+D i lam*(div D (a N).1-(a N).2)+
        (h⁻¹*θ i) • ((lam+m)*(div D (a N).1-(a N).2))) := by
  rw [shifted_physical_expansion D _ _ _ _ hD i,
    truncated_divergence D θ h hh N a hn₀ hnrec,RT_scalar_add,
    truncated_R D θ hθ lam m h hh N a hR₀ hRrec i]
  simp only [shifted_apply,Pi.smul_apply,smul_eq_mul,Derivation.map_smul]
  simp only [Algebra.smul_def]
  ring

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
lemma localCoord_commute {U : Set X} (hU : IsOpen U) (i j : Fin 3) (f : LocalSmooth U) :
    localCoord hU i (localCoord hU j f)=localCoord hU j (localCoord hU i f) := by
  obtain ⟨f,rfl⟩ := restrictSmooth_surjective U f
  simp only [localCoord_restrict,coord_commute i j]

lemma restrict_div {U : Set X} (hU : IsOpen U) (a : Fin 3 → Smooth) :
    restrictSmooth U (div coord a)=div (localCoord hU) (fun i => restrictSmooth U (a i)) := by
  simp only [div,map_sum,localCoord_restrict]
lemma restrict_normal (U : Set X) (θ : Fin 3 → ℂ) (a : Fin 3 → Smooth) :
    restrictSmooth U (normal θ a)=normal θ (fun i => restrictSmooth U (a i)) := by
  simp only [normal,map_sum,map_smul]
lemma restrict_R {U : Set X} (hU : IsOpen U) (lam mu : Smooth) (a : Fin 3 → Smooth) (b : Smooth) (i : Fin 3) :
    restrictSmooth U (R coord lam mu a b i)=
      R (localCoord hU) (restrictSmooth U lam) (restrictSmooth U mu)
        (fun i => restrictSmooth U (a i)) (restrictSmooth U b) i := by
  simp only [R,cm,lap,map_add,map_mul,map_sum,localCoord_restrict]
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
lemma restrict_LT {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (lam m : Smooth)
    (a : Fin 3 → Smooth) (i : Fin 3) :
    restrictSmooth U (LT (shifted coord z) lam m a i)=
      LT (shifted (localCoord hU) z) (restrictSmooth U lam) (restrictSmooth U m)
        (fun j => restrictSmooth U (a j)) i := by
  simp only [LT,divT,restrict_shifted hU,map_mul,map_sum,map_add]

/-- Literal finite physical residual on an open region. All compatibility
identities are local equalities, not strengthened global transport hypotheses. -/
theorem physical_truncation_residual_on {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (lam m : Smooth)
    (h : ℂ) (hh : h≠0) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m)
      (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
    (hn₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,RecursOn hU θ lam m (a j) (a (j+1))) (i : Fin 3) :
    EqOn ((LT (shifted coord (h⁻¹ • θ)) lam m (truncation h N a).1 i : Smooth) : X → ℂ)
      ((h^N • (R coord lam m (a N).1 (a N).2 i+
        (lam+m)*coord i (div coord (a N).1-(a N).2)+
        coord i lam*(div coord (a N).1-(a N).2)+
        (h⁻¹*θ i) • ((lam+m)*(div coord (a N).1-(a N).2))) : Smooth) : X → ℂ) U := by
  have hn₀' : normal θ (localAmp U (a 0)).1=0 := by
    simp only [localAmp,← restrict_normal,hn₀,map_zero]
  have hnrec (j) (hj : j<N) : normal θ (localAmp U (a (j+1))).1=
      -(div (localCoord hU) (localAmp U (a j)).1-(localAmp U (a j)).2) := by
    have hh := congrArg (restrictSmooth U) (hrec j hj).2.2
    simpa only [restrict_normal,map_neg,map_sub,restrict_div hU,localAmp] using hh
  have hhres := truncated_physical_residual (localCoord hU) (localCoord_commute hU) θ hθ
    (restrictSmooth U lam) (restrictSmooth U m) h hh N (fun j => localAmp U (a j))
    hR₀ (fun j hj => (hrec j hj).1) hn₀' hnrec i
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [restrict_LT hU]
  change LT (shifted (localCoord hU) (h⁻¹ • θ)) (restrictSmooth U lam) (restrictSmooth U m)
    (localAmp U (truncation h N a)).1 i=_
  rw [localAmp_truncation,hhres]
  simp only [map_smul,map_add,map_mul,map_sub,restrict_R hU,localCoord_restrict,restrict_div hU,localAmp]
  rw [← restrict_div hU,localCoord_restrict]
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
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply toSmooth_physical physical phase)
open ElasticityDistribution (finiteResidual)
lemma cut_local {U : Set X} (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (hχ : EqOn (χ : X → ℂ) 1 U) (f : Smooth) :
    restrictSmooth U (toSmooth (cut χ hc f))=restrictSmooth U f := by
  apply (restrictSmooth_eq_iff U _ _).mpr
  intro x hx
  simp only [toSmooth_apply,cut_apply,hχ hx,Pi.one_apply,one_mul]
lemma physical_cut_local {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (u : Fin 3 → Smooth) (i : Fin 3) :
    EqOn (physical z lam m (fun j => cut χ hc (u j)) i : X → ℂ)
      ((LT (shifted coord z) lam m u i : Smooth) : X → ℂ) U := by
  change EqOn ((toSmooth (physical z lam m (fun j => cut χ hc (u j)) i) : Smooth) : X → ℂ) _ U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_physical z lam m hl hm,restrict_LT hU,restrict_LT hU]
  congr 1
  funext j
  exact cut_local χ hc hχ (u j)

/-- The actual Schwartz residual has precisely the two powers h^8 and h^7.
The amplitude recursions are only required on the indicated open region. -/
theorem cut_truncation_residual_oai {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (lam m χ : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    (h : ℝ) (hh : h≠0) (a : ℕ → Amplitude Smooth)
    (hR₀ : leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m)
      (localAmp U (a 0)).1 (localAmp U (a 0)).2=0)
    (hn₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<8,RecursOn hU θ lam m (a j) (a (j+1))) (i : Fin 3) :
    EqOn (physical ((h : ℂ)⁻¹ • θ) lam m
      (fun j => cut χ hc ((truncation (h : ℂ) 8 a).1 j)) i : X → ℂ)
      (finiteResidual h (fun j => cut χ hc (residual0 lam m (a 8) j))
        (fun j => cut χ hc (residual1 θ lam m (a 8) j)) i : X → ℂ) U := by
  intro x hx
  rw [physical_cut_local hU _ lam m χ hl hm hc hχ _ i hx]
  have hh' : (h : ℂ)≠0 := by exact_mod_cast hh
  rw [physical_truncation_residual_on hU θ hθ lam m (h : ℂ) hh' 8 a hR₀ hn₀ hrec i hx]
  change (h : ℂ)^8 * ( _ + ((h : ℂ)⁻¹*θ i) * _) =
    (h : ℂ)^8 * ((χ : X → ℂ) x * (residual0 lam m (a 8) i : X → ℂ) x) +
    (h : ℂ)^7 * ((χ : X → ℂ) x * (residual1 θ lam m (a 8) i : X → ℂ) x)
  rw [hχ hx]
  change (h : ℂ)^8 * ( _ + ((h : ℂ)⁻¹*θ i) * _) =
    (h : ℂ)^8 * (1 * _) + (h : ℂ)^7 * (1 * (θ i * _))
  simp only [one_mul,residual0]
  field_simp

end ElasticityCGO

end
end

end OAI
end

theorem solution : type_of% @OAI.ElasticityCGO.cut_truncation_residual_oai := @OAI.ElasticityCGO.cut_truncation_residual_oai
