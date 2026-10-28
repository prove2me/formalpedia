-- Prove2me | solution 1 for OAI.ElasticityCGO.localized_actual_strong_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:28:04.992413+00:00
-- url     : https://prove2.me/submissions/901cb055-b094-41e2-8688-d72c47650dde

import Mathlib
import Definitions.Def_OAIQ6El006
import Theorems.Thm_OAI_ElasticityCGO_localized_formal_augmented_H1_bound
import Theorems.Thm_OAI_ElasticityCGO_physical_column_shifted_realization

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

lemma weight_pos (h s : ℝ) (x : X) : 0 < weight h s x := by
  exact Real.rpow_pos_of_pos (by positivity) _

lemma temperate_weight (h s : ℝ) : (weight h s).HasTemperateGrowth := by
  exact (Function.hasTemperateGrowth_one_add_norm_sq_rpow X (s/2)).comp
    (((2*Real.pi*h) • ContinuousLinearMap.id ℝ X).hasTemperateGrowth)

lemma temperate_complex_weight (h s : ℝ) :
    (fun x => (weight h s x : ℂ)).HasTemperateGrowth := by
  exact Complex.ofRealCLM.hasTemperateGrowth.comp (temperate_weight h s)

@[simp] lemma M_apply (h s : ℝ) (f : S) (x : X) :
    M h s f x = (weight h s x : ℂ)*f x := by
  exact SchwartzMap.smulLeftCLM_apply_apply (temperate_complex_weight h s) f x

@[simp] lemma M_zero (h : ℝ) (f : S) : M h 0 f = f := by
  ext x
  simp only [M_apply, weight_zero, Complex.ofReal_one, one_mul]

@[simp] lemma J_zero (h : ℝ) (f : S) : J h 0 f = f := by
  simp only [J, M_zero, FourierTransform.fourierInv_fourier_eq]

lemma J_add (h s : ℝ) (f g : S) : J h s (f+g) = J h s f + J h s g := by
  simp only [J, FourierTransform.fourier_add, map_add, FourierTransform.fourierInv_add]

lemma J_smul (h s : ℝ) (a : ℂ) (f : S) : J h s (a • f) = a • J h s f := by
  simp only [J, FourierTransform.fourier_smul, map_smul, FourierTransform.fourierInv_smul]

lemma norm2_nonneg (f : S) : 0 ≤ norm2 f := norm_nonneg _

lemma norm2_bound (f g : S) (c : ℝ) (h : ∀ x : X, ‖f x‖ ≤ c*‖g x‖) :
    norm2 f ≤ c*norm2 g := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hx hy
  change ‖f.toLp 2 volume x‖ ≤ c * ‖g.toLp 2 volume x‖
  rw [hx, hy]
  exact h x

lemma norm2_fourier (f : S) : norm2 (𝓕 f) = norm2 f :=
  SchwartzMap.norm_fourier_toL2_eq f

lemma norm2_fourierInv (f : S) : norm2 (𝓕⁻ f) = norm2 f := by
  have h := norm2_fourier (𝓕⁻ f)
  rw [FourierTransform.fourier_fourierInv_eq] at h
  exact h.symm

lemma norm2_J (h s : ℝ) (f : S) : norm2 (J h s f) = norm2 (M h s (𝓕 f)) :=
  norm2_fourierInv _

lemma real_weight_bound (h s t c : ℝ)
    (hw : ∀ x : X, weight h s x ≤ c*weight h t x) (f : S) :
    norm2 (J h s f) ≤ c*norm2 (J h t f) := by
  rw [norm2_J, norm2_J]
  apply norm2_bound
  intro x
  simp only [M_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos _ _ _)]
  exact (mul_le_mul_of_nonneg_right (hw x) (norm_nonneg (𝓕 f x))).trans_eq (by ring)

lemma weight_mono (h : ℝ) {s t : ℝ} (hst : s ≤ t) (x : X) :
    weight h s x ≤ weight h t x := by
  exact Real.rpow_le_rpow_of_exponent_le
    (by nlinarith [sq_nonneg ‖(2*Real.pi*h) • x‖]) (by linarith)

lemma norm2_J_mono (h : ℝ) {s t : ℝ} (hst : s ≤ t) (f : S) :
    norm2 (J h s f) ≤ norm2 (J h t f) := by
  have he := real_weight_bound h s t 1 (fun x => by
    simpa only [one_mul] using weight_mono h hst x) f
  simpa only [one_mul] using he

end ElasticityBessel

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap

namespace ElasticityNegativeOrder
open ElasticityBessel
open ElasticitySchwartzCarleman

section

lemma norm2_sub_le (f g : S) : norm2 (f-g) ≤ norm2 f+norm2 g := by
  simpa only [norm2, map_sub] using norm_sub_le (L2 f) (L2 g)

lemma J_sub (h s : ℝ) (f g : S) : J h s (f-g) = J h s f-J h s g := by
  rw [sub_eq_add_neg, J_add, ← neg_one_smul ℂ g, J_smul]
  simp only [neg_one_smul, sub_eq_add_neg]

lemma norm2_J_one_ge (h : ℝ) (f : S) : norm2 f ≤ norm2 (J h 1 f) := by
  have ht := norm2_J_mono h (show (0 : ℝ) ≤ 1 by norm_num) f
  simpa only [J_zero] using ht

lemma mult_apply (a : X → ℂ) (ha : a.HasTemperateGrowth) (f : S) (x : X) :
    mult a f x = a x * f x :=
  SchwartzMap.smulLeftCLM_apply_apply ha f x

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

lemma sumNorm_four_le (h s : ℝ) (U : Fin 4 → S) :
    sumNorm h s U ≤ 2*sobNorm h s U := by
  have hn : 0 ≤ ∑ i, norm2 (J h s (U i))^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hs := Real.sq_sqrt hn
  have ht := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun i => norm2 (J h s (U i)))
  norm_num only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at ht
  dsimp only [sobNorm, sumNorm]
  nlinarith only [hs, ht, Real.sqrt_nonneg (∑ i, norm2 (J h s (U i))^2)]

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
open Set Filter
open scoped Topology BigOperators
namespace ElasticityAugmented

lemma localCoord_restrict {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth) :
    localCoord hU i (restrictSmooth U f)=restrictSmooth U (coord i f) := by
  exact Derivation.liftOfSurjective_apply (restrictSmooth_surjective U) (restrict_coord_zero hU i) f
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

lemma restrict_shifted {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (i : Fin 3) (f : Smooth) :
    restrictSmooth U (shifted coord z i f)=shifted (localCoord hU) z i (restrictSmooth U f) := by
  simp only [shifted_apply,map_add,map_smul,localCoord_restrict]
lemma restrict_LT {U : Set X} (hU : IsOpen U) (z : Fin 3 → ℂ) (lam m : Smooth)
    (a : Fin 3 → Smooth) (i : Fin 3) :
    restrictSmooth U (LT (shifted coord z) lam m a i)=
      LT (shifted (localCoord hU) z) (restrictSmooth U lam) (restrictSmooth U m)
        (fun j => restrictSmooth U (a j)) i := by
  simp only [LT,divT,restrict_shifted hU,map_mul,map_sum,map_add]

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

lemma phase_eq (h : ℝ) (α β : X) :
    phase h α β=(h : ℂ)⁻¹ • (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) := by
  funext i
  simp only [phase,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
end ElasticityCGO

end
end
section
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators SchwartzMap
namespace ElasticityPhysicalAlgebra
open ElasticityAugmented

lemma physical_eqOn_of_eqOn {U : Set X} (hU : IsOpen U)
    (z : Fin 3 → ℂ) (lam m : Smooth)
    (hl : (lam : X → ℂ).HasTemperateGrowth) (hm : (m : X → ℂ).HasTemperateGrowth)
    (f g : Fin 3 → SchwartzMap X ℂ) (hfg : ∀ j,EqOn (f j : X → ℂ) (g j) U) (i : Fin 3) :
    EqOn (physical z lam m f i : X → ℂ) (physical z lam m g i) U := by
  change EqOn ((toSmooth (physical z lam m f i) : Smooth) : X → ℂ)
    ((toSmooth (physical z lam m g i) : Smooth) : X → ℂ) U
  apply (restrictSmooth_eq_iff U _ _).mp
  rw [toSmooth_physical z lam m hl hm,toSmooth_physical z lam m hl hm,
    restrict_LT hU,restrict_LT hU]
  congr 1
  funext j
  exact (restrictSmooth_eq_iff U _ _).mpr (hfg j)

end ElasticityPhysicalAlgebra

end
end
section
noncomputable section
open Set
open scoped BigOperators SchwartzMap
namespace ElasticityPhysicalEstimate
open ElasticityBessel ElasticitySchwartzCarleman ElasticityNegativeOrder ElasticityPhysicalAlgebra
open ElasticityAugmented (coord coeffA coeffV)
open ElasticityCoeffBounds

lemma physicalAug_sub (z : Fin 3 → ℂ) (u v : Fin 3 → S) :
    physicalAug z (v-u)=physicalAug z v-physicalAug z u := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [physicalAug,Fin.cons_zero,Pi.sub_apply,divShift,map_sub,Finset.sum_sub_distrib]
  · rfl

end ElasticityPhysicalEstimate

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
open Set
open scoped SchwartzMap BigOperators
open ElasticityAugmented
open ElasticityBessel (J norm2)
open ElasticityNegativeOrder (mult sobNorm sumNorm)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)
open ElasticityCoeffBounds (ExteriorConstant)

lemma sobNorm_sub_four (h s : ℝ) (u v : Fin 4 → S) :
    sobNorm h s (u-v)≤2*(sobNorm h s u+sobNorm h s v) := by
  apply (ElasticityNegativeOrder.sobNorm_le_sumNorm h s _).trans
  have hs : sumNorm h s (u-v)≤ sumNorm h s u+sumNorm h s v := by
    simp only [sumNorm,Pi.sub_apply,ElasticityNegativeOrder.J_sub,← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => ElasticityNegativeOrder.norm2_sub_le _ _)
  have hu := ElasticityNegativeOrder.sumNorm_four_le h s u
  have hv := ElasticityNegativeOrder.sumNorm_four_le h s v
  linarith only [hs,hu,hv]

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

lemma norm2_le_sobNorm {n : ℕ} (h : ℝ) (u : Fin n → S) (i : Fin n) :
    norm2 (u i)≤ sobNorm h 1 u := by
  apply (ElasticityNegativeOrder.norm2_J_one_ge h (u i)).trans
  exact Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun j _ => sq_nonneg (norm2 (J h 1 (u j))))
    (Finset.mem_univ i))

end
open Set MeasureTheory Filter
open scoped SchwartzMap Topology BigOperators
open ElasticityAugmented
open ElasticityCoeffBounds (ExteriorConstant)
open ElasticityBessel (L2 norm2)
open ElasticityNegativeOrder (mult sobNorm)
open ElasticityPhysicalAlgebra (phase physical)
open ElasticityPhysicalEstimate (physicalAug)

/-- Actual shifted physical solutions, bounded in the literal augmented H1
norm, whose augmented L2 error from the formal series is O(h). -/
theorem localized_actual_strong_bound_oai (R : ℝ) (hR : 1≤R) (α β : X)
    (lam m : Smooth) (hl : ExteriorConstant lam) (hm : ExteriorConstant m)
    (a : ℕ → Amplitude Smooth) (ha : PhysicalColumn R hR α β lam m a)
    (h₀ : normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) (a 0).1=0)
    (hrec : ∀ j<8,EqOn (fun x => ((normal (fun i => (α i : ℂ)+Complex.I*(β i : ℂ))
      (a (j+1)).1 : Smooth) : X → ℂ) x)
      (fun x => ((-(div coord (a j).1-(a j).2) : Smooth) : X → ℂ) x) (Metric.ball 0 R))
    {g : X → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (hs : tsupport g⊆Metric.ball 0 R) {B : Set X} (hB : IsOpen B)
    (hBR : B⊆Metric.ball 0 R) (hg1 : EqOn g 1 B) :
    ∃ C D h₁ : ℝ,0<C ∧ 0<D ∧ 0<h₁ ∧ ∀ h : ℝ,0<h → h≤h₁ → ∃ u : Fin 3 → S,
      (∀ i,EqOn (physical (phase h α β) lam m u i : X → ℂ) 0 B) ∧
      sobNorm h 1 (physicalAug (phase h α β) u)≤C ∧
      ∀ i,‖L2 (physicalAug (phase h α β) u i-
        physicalAug (phase h α β) (localizedFormal R hR (h : ℂ) a g) i)‖≤D*h := by
  let χ : Smooth := ⟨fiveCutoff R hR 0,fiveCutoff_smooth R hR 0⟩
  have hcχ : HasCompactSupport (χ : X → ℂ) := fiveCutoff_compact R hR 0
  obtain ⟨A,hA,hformal⟩ := localized_formal_augmented_H1_bound Metric.isOpen_ball
    (fun i => (α i : ℂ)+Complex.I*(β i : ℂ)) 8 a h₀ hrec χ hcχ
    (fiveCutoff_initial R hR) (hc.hasTemperateGrowth hg) hs
  obtain ⟨D,h₁,hD,hh₁,hh₁1,hsol⟩ := physical_column_shifted_realization
    R hR α β lam m a ha hg hc hs
  refine ⟨2*(A+D),D,h₁,by linarith only [hA,hD],hD,hh₁,fun h hh hsmall => ?_⟩
  obtain ⟨w,q,v,_hv,hp,_hq,_hw,_hn,hbound⟩ := hsol h hh hsmall
  let F := localizedFormal R hR (h : ℂ) a g
  let V : Fin 3 → S := fun i => mult g (v i)
  let u := F-V
  have hlocal : ∀ j,EqOn (u j : X → ℂ)
      (((fun k => cut χ hcχ ((truncation (h : ℂ) 8 a).1 k))-v) j) B := by
    intro j x hx
    change mult g (cut χ hcχ ((truncation (h : ℂ) 8 a).1 j)) x-mult g (v j) x=_
    simp only [ElasticityNegativeOrder.mult_apply g (hc.hasTemperateGrowth hg),hg1 hx,
      Pi.one_apply,one_mul,Pi.sub_apply,sub_apply]
  refine ⟨u,fun i x hx => (ElasticityPhysicalAlgebra.physical_eqOn_of_eqOn hB _ lam m
    hl.growth hm.growth u _ hlocal i hx).trans (hp i (hBR hx)),?_,fun i => ?_⟩
  · have hh1 : h≤1 := hsmall.trans hh₁1
    have hf := hformal h hh hh1
    rw [← phase_eq] at hf
    change sobNorm h 1 (physicalAug (phase h α β) F)≤A at hf
    change sobNorm h 1 (physicalAug (phase h α β) V)≤D*h at hbound
    change sobNorm h 1 (physicalAug (phase h α β) (F-V))≤_
    rw [ElasticityPhysicalEstimate.physicalAug_sub]
    have hn := sobNorm_sub_four h 1 (physicalAug (phase h α β) F) (physicalAug (phase h α β) V)
    have hDh : D*h≤D := by nlinarith only [hD,hh1]
    linarith only [hn,hf,hbound,hDh]
  · have ht : physicalAug (phase h α β) u i-physicalAug (phase h α β) F i=
        -physicalAug (phase h α β) V i := by
      change physicalAug (phase h α β) (F-V) i-physicalAug (phase h α β) F i=_
      rw [ElasticityPhysicalEstimate.physicalAug_sub]
      simp only [Pi.sub_apply,sub_sub_cancel_left]
    rw [ht,map_neg,norm_neg]
    exact (norm2_le_sobNorm h (physicalAug (phase h α β) V) i).trans hbound

end ElasticityCGO

end

end OAI
end

theorem solution : type_of% @OAI.ElasticityCGO.localized_actual_strong_bound_oai := @OAI.ElasticityCGO.localized_actual_strong_bound_oai
