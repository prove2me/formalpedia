-- Prove2me | solution 1 for OAI.ElasticityCGO.localized_formal_L2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:29:16.659496+00:00
-- url     : https://prove2.me/submissions/57de66b4-57c9-4598-8223-d25118f01639

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

lemma phase_eq (h : ℝ) (α β : X) :
    phase h α β=(h : ℂ)⁻¹ • (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) := by
  funext i
  simp only [phase,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
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
open ElasticityBessel (J norm2 )

lemma cut_truncation (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ))
    (h : ℂ) (N : ℕ) (a : ℕ → Smooth) :
    cut χ hc (truncation h N a)=truncation h N (fun j => cut χ hc (a j)) := by
  simp only [truncation,map_sum,map_smul]

end
open Set
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2 )
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

end ElasticityCGO
namespace ElasticityCGO
open Set
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2 )
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

end ElasticityCGO

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCGO

section
open Set Filter MeasureTheory
open scoped SchwartzMap Topology BigOperators ENNReal
open ElasticityAugmented
open ElasticityBessel (L2 norm2 J)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (divShift)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityDistribution (AugHilbert)

lemma truncation_at_zero (N : ℕ) (f : ℕ → S) : truncation 0 N f=f 0 := by
  induction N with
  | zero => exact truncation_zero 0 f
  | succ N ih => simp only [truncation_succ,ih,zero_pow (Nat.succ_ne_zero N),zero_smul,add_zero]
lemma truncation_continuous (N : ℕ) (f : ℕ → S) : Continuous (fun h : ℂ => truncation h N f) := by
  unfold truncation
  exact continuous_finsetSum _ (fun j _ => (continuous_id.pow j).smul continuous_const)
lemma truncation_tendsto {h : ℕ → ℂ} (hh : Tendsto h atTop (𝓝 0)) (N : ℕ) (f : ℕ → S) :
    Tendsto (fun n => truncation (h n) N f) atTop (𝓝 (f 0)) := by
  simpa only [truncation_at_zero,Function.comp_def] using (truncation_continuous N f).continuousAt.tendsto.comp hh

/-- Exact polynomial formula for the actual localized formal scalar amplitude.
The derivative of the localization is retained; it disappears only where g=1. -/
lemma formal_scalar_polynomial {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (N : ℕ) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆U)
    (h : ℂ) (hh : h≠0) :
    divShift (h⁻¹ • θ) (fun i => mult g (cut χ hc ((truncation h N a).1 i)))=
      truncation h N (fun j => mult g (cut χ hc (a j).2))+
      h^N • mult g (cut χ hc (div coord (a N).1-(a N).2))+
      ∑ i, truncation h N (fun j => mult (fun x => fderiv ℝ g x (e i)) (cut χ hc ((a j).1 i))) := by
  rw [divShift_mult _ g hg]
  have he := cut_truncation_divergence hU θ h hh N a h₀ hrec χ hc hχ
  rw [mult_eq_of_local hg hs he,truncation_scalar]
  simp only [map_add,map_smul,cut_truncation]
  congr 1
  · simp only [truncation,map_sum,map_smul]
  · exact Finset.sum_congr rfl (fun i _ => mult_cut_truncation_vector _ χ hc N a h i)

/-- Strong Schwartz convergence of the formal augmented amplitudes, including
its physical scalar component and the cutoff derivative. -/
theorem formal_augmented_tendsto {U : Set X} (hU : IsOpen U)
    (θ : Fin 3 → ℂ) (N : ℕ) (hN : 0<N) (a : ℕ → Amplitude Smooth)
    (h₀ : normal θ (a 0).1=0)
    (hrec : ∀ j<N,EqOn (fun x => ((normal θ (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) U)
    (χ : Smooth) (hc : HasCompactSupport (χ : X → ℂ)) (hχ : EqOn (χ : X → ℂ) 1 U)
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆U)
    {h : ℕ → ℂ} (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n,h n≠0) :
    ∀ i : Fin 4, Tendsto (fun n => physicalAug ((h n)⁻¹ • θ)
      (fun j => mult g (cut χ hc ((truncation (h n) N a).1 j))) i) atTop
      (𝓝 ((Fin.cons (mult g (cut χ hc (a 0).2)+
        ∑ j, mult (fun x => fderiv ℝ g x (e j)) (cut χ hc ((a 0).1 j)))
        (fun j => mult g (cut χ hc ((a 0).1 j))) : Fin 4 → S) i)) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [physicalAug,Fin.cons_zero]
    have he : (fun n => divShift ((h n)⁻¹ • θ)
        (fun j => mult g (cut χ hc ((truncation (h n) N a).1 j))))=
        (fun n => truncation (h n) N (fun j => mult g (cut χ hc (a j).2))+
          h n^N • mult g (cut χ hc (div coord (a N).1-(a N).2))+
          ∑ j, truncation (h n) N (fun k => mult (fun x => fderiv ℝ g x (e j))
            (cut χ hc ((a k).1 j)))) := by
      funext n
      exact formal_scalar_polynomial hU θ N a h₀ hrec χ hc hχ hg hs _ (hne n)
    rw [he]
    have hm := (hh.pow N).smul (tendsto_const_nhds (x := mult g (cut χ hc (div coord (a N).1-(a N).2))))
    simp only [zero_pow hN.ne',zero_smul] at hm
    have hv := tendsto_finsetSum Finset.univ (fun j _ => truncation_tendsto hh N
      (fun k => mult (fun x => fderiv ℝ g x (e j)) (cut χ hc ((a k).1 j))))
    simpa only [add_zero] using ((truncation_tendsto hh N
      (fun k => mult g (cut χ hc (a k).2))).add hm).add hv
  · simp only [physicalAug,Fin.cons_succ]
    simp_rw [mult_cut_truncation_vector]
    exact truncation_tendsto hh N _

end
open Set MeasureTheory Filter
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityBessel (L2 norm2)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)

lemma localized_formal_L2_tendsto_oai (R : ℝ) (hR : 1≤R) (α β : X)
    (a : ℕ → Amplitude Smooth)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
    {g : X → ℂ} (hg : g.HasTemperateGrowth) (hs : tsupport g⊆Metric.ball 0 R)
    {h : ℕ → ℝ} (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ n,h n≠0) (i : Fin 4) :
    Tendsto (fun n => L2 (physicalAug (phase (h n) α β)
      (localizedFormal R hR (h n : ℂ) a g) i)) atTop
      (𝓝 (L2 (localizedLeading R hR a g i))) := by
  have hh' : Tendsto (fun n => (h n : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero,Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hh
  have ht := formal_augmented_tendsto Metric.isOpen_ball
    (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) 8 (by norm_num) a h₀ hrec
    ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩ (fiveCutoff_compact R hR 0)
    (fiveCutoff_initial R hR) hg hs hh' (fun n => Complex.ofReal_ne_zero.mpr (hne n)) i
  simp_rw [← phase_eq] at ht
  exact L2.continuous.continuousAt.tendsto.comp ht

end ElasticityCGO

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityCGO.localized_formal_L2_tendsto_oai := @OAI.ElasticityCGO.localized_formal_L2_tendsto_oai
