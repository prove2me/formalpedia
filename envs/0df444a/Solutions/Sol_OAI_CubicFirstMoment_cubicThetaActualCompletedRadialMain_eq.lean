-- Prove2me | solution 1 for OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:14:15.204298+00:00
-- url     : https://prove2.me/submissions/6106434d-6d3c-4691-a8b2-171096f1697c

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A020
import Definitions.Def_OAIQ096A026
import Theorems.Thm_OAI_CubicFirstMoment_cubicThetaArithmeticAxisDerivative_re_neg
import Theorems.Thm_OAI_CubicFirstMoment_cubicThetaArithmeticRankinMass_unfold
import Theorems.Thm_OAI_CubicFirstMoment_cubicThetaScalarRankinKernel_integral_limit

section
-- module Solutions.OAIQ096_CM.CubicGram_ResidueCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Primitive cube roots, Euler residue characters and additive trace phases. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gaussAtPrime_eq_finite_sum {p : Eisenstein} (hp : p ≠ 0)
    [Fintype (Residues p)] (reps : Residues p → Eisenstein)
    (hreps : ∀ x, Ideal.Quotient.mk (modulus p) (reps x) = x) :
    gaussAtPrime p = (Real.sqrt (norm p) : ℂ)⁻¹ *
      ∑ x : Residues p, cubicSymbolAtPrime p (reps x) * additivePhase p (reps x) := by
  unfold gaussAtPrime
  rw [tsum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hrep : Ideal.Quotient.mk (modulus p) (residueRepresentative p x) =
      Ideal.Quotient.mk (modulus p) (reps x) := by
    rw [residueRepresentative_spec, hreps]
  rw [cubicSymbolAtPrime_congr hrep, additivePhase_congr hp hrep]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Conjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein conjugation, characters and Gauss-sum symmetry. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma additivePhase_conjugate (p v : Eisenstein) :
    additivePhase (conjugate p) (conjugate v) = additivePhase p v := by
  simp only [additivePhase, conjugate_coe, ← star_div₀, star_star]
  rw [add_comm (star ((v : ℂ) / (p : ℂ))) ((v : ℂ) / (p : ℂ))]

theorem gaussAtPrime_conjugate {p : Eisenstein} (hp : primaryPrime p) :
    gaussAtPrime (conjugate p) = star (gaussAtPrime p) := by
  let : Finite (Residues p) := finite_residues hp.2.ne_zero
  let : Fintype (Residues p) := Fintype.ofFinite _
  let : Finite (Residues (conjugate p)) :=
    finite_residues (primaryPrime_conjugate hp).2.ne_zero
  let : Fintype (Residues (conjugate p)) := Fintype.ofFinite _
  let e : Residues p ≃ Residues (conjugate p) := (residueConjugate p).toEquiv
  let r : Residues (conjugate p) → Eisenstein := fun x =>
    conjugate (residueRepresentative p (e.symm x))
  have hr (x) : Ideal.Quotient.mk (modulus (conjugate p)) (r x) = x := by
    change residueConjugate p (Ideal.Quotient.mk (modulus p)
      (residueRepresentative p (e.symm x))) = x
    rw [residueRepresentative_spec]
    exact e.apply_symm_apply x
  rw [gaussAtPrime_eq_finite_sum (primaryPrime_conjugate hp).2.ne_zero r hr,
    norm_conjugate]
  rw [← e.sum_comp (fun x => cubicSymbolAtPrime (conjugate p) (r x) *
    additivePhase (conjugate p) (r x))]
  simp only [r, Equiv.symm_apply_apply, cubicSymbolAtPrime_conjugate hp,
    additivePhase_conjugate]
  rw [gaussAtPrime_eq_finite_sum hp.2.ne_zero (residueRepresentative p)
    (residueRepresentative_spec p), star_mul', star_inv₀,
    show star ((Real.sqrt (norm p) : ℝ) : ℂ) = (Real.sqrt (norm p) : ℂ) from by
      simp only [Complex.star_def, Complex.conj_ofReal], star_sum]
  congr 1
  rw [← Equiv.sum_comp (Equiv.neg (Residues p))
    (fun x => star (cubicSymbolAtPrime p (residueRepresentative p x)) *
      additivePhase p (residueRepresentative p x))]
  apply Finset.sum_congr rfl
  intro x _
  have hrep : Ideal.Quotient.mk (modulus p) (residueRepresentative p (-x)) =
      Ideal.Quotient.mk (modulus p) (-residueRepresentative p x) := by
    rw [map_neg, residueRepresentative_spec, residueRepresentative_spec]
  simp only [Equiv.neg_apply, star_mul', cubicSymbolAtPrime_congr hrep,
    additivePhase_congr hp.2.ne_zero hrep, cubicSymbolAtPrime_neg hp,
    additivePhase_neg hp.2.ne_zero]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiate the fixed order-one-third heat integral on its positive
axis. The dominating inverse Laplace moment is integrable there. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicBesselHeat_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun y => cubicBesselHeat y t) (cubicBesselHeatDerivative x t) x := by
  have h := (((hasDerivAt_id x).neg.div_const t).exp).const_mul
    (t^(-4/3:ℝ)*Real.exp (-t))
  simp only [Pi.neg_apply,id_eq] at h
  refine h.congr_deriv ?_
  · unfold cubicBesselHeatDerivative cubicBesselHeat
    ring

lemma cubicBesselHeatDerivative_local_bound {a x t : ℝ} (hax : a≤x) (ht : 0<t) :
    ‖cubicBesselHeatDerivative x t‖≤t^(-7/3:ℝ)*Real.exp (-a/t) := by
  have h := div_le_div_of_nonneg_right (cubicBesselHeat_local_bound hax ht) ht.le
  have he : t^(-4/3:ℝ)/t=t^(-7/3:ℝ) := by
    calc
      _ = t^(-4/3:ℝ)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^((-4/3:ℝ)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by norm_num
  simpa only [cubicBesselHeatDerivative,norm_div,norm_neg,Real.norm_eq_abs,
    abs_of_pos ht,mul_div_right_comm,he] using h

lemma cubicBesselHeat_integral_hasDerivAt {x : ℝ} (hx : 0<x) :
    HasDerivAt (fun y => ∫ t in Ioi (0:ℝ),cubicBesselHeat y t)
      (∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t) x := by
  have hi : IntegrableOn (fun t : ℝ => t^(-7/3:ℝ)*Real.exp (-(x/2)/t)) (Ioi 0) := by
    convert integrable_inverse_laplace_rpow (by norm_num : (0:ℝ)<4/3)
      (show 0<x/2 by positivity) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s:=Ioi (x/2)) (bound:=fun t : ℝ => t^(-7/3:ℝ)*Real.exp (-(x/2)/t))
    (isOpen_Ioi.mem_nhds (by change x/2<x; linarith))
    (Eventually.of_forall (fun y => by
      apply Measurable.aestronglyMeasurable
      unfold cubicBesselHeat
      fun_prop)) (cubicBesselHeat_integrable hx) ?_ ?_ hi ?_).2
  · apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeatDerivative cubicBesselHeat
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro y hy
    exact cubicBesselHeatDerivative_local_bound hy.le ht
  · filter_upwards with t
    intro y _
    exact cubicBesselHeat_hasDerivAt y t

theorem cubicBesselKernel_hasDerivAt {x : ℝ} (hx : 0<x) :
    HasDerivAt cubicBesselKernel (cubicBesselKernelDerivative x) x := by
  have hp := Real.hasDerivAt_rpow_const (x:=x) (p:=(1/6:ℝ)) (Or.inl (ne_of_gt hx))
  have h := hp.mul (cubicBesselHeat_integral_hasDerivAt hx)
  refine h.congr_deriv ?_
  · norm_num [cubicBesselKernelDerivative]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselDerivativeBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Power decay of the first derivative of the fixed Bessel kernel.
The same lattice majorants can therefore control vertical theta derivatives. -/
noncomputable section
open MeasureTheory Set Filter
namespace CubicFirstMoment

lemma cubicBesselHeatDerivative_integrable {x : ℝ} (hx : 0<x) :
    IntegrableOn (cubicBesselHeatDerivative x) (Ioi 0) := by
  have hi : IntegrableOn (fun t : ℝ => t^(-7/3:ℝ)*Real.exp (-x/t)) (Ioi 0) := by
    convert integrable_inverse_laplace_rpow (by norm_num : (0:ℝ)<4/3) hx using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  apply hi.mono' (by
    apply Measurable.aestronglyMeasurable
    unfold cubicBesselHeatDerivative cubicBesselHeat
    fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact cubicBesselHeatDerivative_local_bound le_rfl ht

lemma cubicBesselHeatDerivative_power_bound (k : ℕ) {x t : ℝ}
    (hx : 0<x) (ht : 0<t) :
    ‖cubicBesselHeatDerivative x t‖≤((k+1).factorial:ℝ)/x^(k+1)*
      (t^((k:ℝ)-4/3)*Real.exp (-t)) := by
  have h := div_le_div_of_nonneg_right (cubicBesselHeat_power_bound (k+1) hx ht) ht.le
  have hp : t^((k+1:ℕ)-4/3:ℝ)/t=t^((k:ℝ)-4/3) := by
    calc
      _ = t^((k+1:ℕ)-4/3:ℝ)/t^(1:ℝ) := by rw [Real.rpow_one]
      _ = t^(((k+1:ℕ)-4/3:ℝ)-1) := (Real.rpow_sub ht _ _).symm
      _ = _ := by congr 1; push_cast; ring
  simp only [cubicBesselHeatDerivative,norm_div,norm_neg,Real.norm_eq_abs,
    abs_of_pos ht,abs_of_nonneg (cubicBesselHeat_nonneg ht)]
  refine h.trans_eq ?_
  calc
    _ = ((k+1).factorial:ℝ)/x^(k+1)*
        ((t^((k+1:ℕ)-4/3:ℝ)/t)*Real.exp (-t)) := by ring
    _ = _ := by rw [hp]

lemma cubicBesselHeatDerivative_integral_bound (k : ℕ) (hk : 1≤k) {x : ℝ} (hx : 0<x) :
    ‖∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t‖≤
      ((k+1).factorial:ℝ)/x^(k+1)*Real.Gamma ((k:ℝ)-1/3) := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have ha : 0<(k:ℝ)-1/3 := by linarith
  have hefun : (fun t : ℝ => t^((k:ℝ)-4/3)*Real.exp (-t))=
      fun t => t^(((k:ℝ)-1/3)-1)*Real.exp (-1*t) := by
    funext t
    congr 2 <;> ring
  have hi : IntegrableOn (fun t : ℝ => t^((k:ℝ)-4/3)*Real.exp (-t)) (Ioi 0) := by
    rw [hefun]
    exact integrable_laplace_rpow ha (by norm_num : (0:ℝ)<1)
  have hb := integral_mono_ae (cubicBesselHeatDerivative_integrable hx).norm
    (hi.const_mul (((k+1).factorial:ℝ)/x^(k+1))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact cubicBesselHeatDerivative_power_bound k hx ht)
  have he : (∫ t in Ioi (0:ℝ),t^((k:ℝ)-4/3)*Real.exp (-t))=Real.Gamma ((k:ℝ)-1/3) := by
    rw [hefun,laplace_rpow ha (by norm_num : (0:ℝ)<1)]
    simp
  exact (norm_integral_le_integral_norm _).trans (by
    simpa only [integral_const_mul,he] using hb)

lemma cubicBesselDerivativePowerConstant_pos {k : ℕ} (hk : 1≤k) :
    0 < cubicBesselDerivativePowerConstant k := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  unfold cubicBesselDerivativePowerConstant
  positivity [Real.Gamma_pos_of_pos (show 0<(k:ℝ)-1/3 by linarith)]

theorem cubicBesselKernelDerivative_power_bound (k : ℕ) (hk : 1≤k)
    {x : ℝ} (hx : 0<x) :
    ‖cubicBesselKernelDerivative x‖≤
      cubicBesselDerivativePowerConstant k*x^(-5/6-(k:ℝ)) := by
  have hI : 0≤∫ t in Ioi (0:ℝ),cubicBesselHeat x t :=
    setIntegral_nonneg measurableSet_Ioi (fun _ ht => cubicBesselHeat_nonneg ht)
  have hKI : (∫ t in Ioi (0:ℝ),cubicBesselHeat x t)≤
      (k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)/x^k := by
    apply (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hx (1/6:ℝ))).mp
    convert cubicBesselKernel_power_bound k hk hx using 1
    all_goals first
      | rfl
      | (rw [Real.rpow_sub hx,Real.rpow_natCast]
         ring)
  have hp1 : x^(-5/6:ℝ)/x^k=x^(-5/6-(k:ℝ)) := by
    rw [Real.rpow_sub hx,Real.rpow_natCast]
  have hp2 : x^(1/6:ℝ)/x^(k+1)=x^(-5/6-(k:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_sub hx]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ((1/6:ℝ)*x^(-5/6:ℝ))*(∫ t in Ioi (0:ℝ),cubicBesselHeat x t)+
        x^(1/6:ℝ)*‖∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t‖ := by
      unfold cubicBesselKernelDerivative
      calc
        _ ≤ ‖((1/6:ℝ)*x^(-5/6:ℝ))*(∫ t in Ioi (0:ℝ),cubicBesselHeat x t)‖+
            ‖x^(1/6:ℝ)*(∫ t in Ioi (0:ℝ),cubicBesselHeatDerivative x t)‖ := norm_add_le _ _
        _ = _ := by
          simp only [norm_mul,Real.norm_of_nonneg (by norm_num : 0≤(1/6:ℝ)),
            Real.norm_of_nonneg (Real.rpow_nonneg hx.le (-5/6:ℝ)),
            Real.norm_of_nonneg hI,Real.norm_of_nonneg (Real.rpow_nonneg hx.le (1/6:ℝ))]
    _ ≤ ((1/6:ℝ)*x^(-5/6:ℝ))*
        ((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)/x^k)+
        x^(1/6:ℝ)*(((k+1).factorial:ℝ)/x^(k+1)*Real.Gamma ((k:ℝ)-1/3)) :=
      add_le_add (mul_le_mul_of_nonneg_left hKI (by positivity))
        (mul_le_mul_of_nonneg_left (cubicBesselHeatDerivative_integral_bound k hk hx) (by positivity))
    _ = _ := by
      calc
        _ = ((k.factorial:ℝ)/6*Real.Gamma ((k:ℝ)-1/3))*(x^(-5/6:ℝ)/x^k)+
            (((k+1).factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3))*(x^(1/6:ℝ)/x^(k+1)) := by ring
        _ = _ := by rw [hp1,hp2]; unfold cubicBesselDerivativePowerConstant; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselSumIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive-quadrant Gamma integral needed for the square of the
fixed order-one-third Schlaefli kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicBesselTriangle_nonneg (p : ℝ × ℝ) : 0 ≤ cubicBesselTriangle p := by
  unfold cubicBesselTriangle cubicBesselSumWeight
  split_ifs with hp
  · exact mul_nonneg (Real.rpow_nonneg (by linarith [hp.1,hp.2]) _) (Real.exp_pos _).le
  · rfl

lemma cubicBesselTriangle_inner_integrable (s : ℝ) :
    Integrable (fun t : ℝ => cubicBesselTriangle (s,t)) := by
  have hi : IntegrableOn (fun _ : ℝ => cubicBesselSumWeight s) (Ioo 0 s) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  convert hi.integrable_indicator measurableSet_Ioo using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  simp only [cubicBesselTriangle,Set.indicator]

lemma cubicBesselTriangle_inner (s : ℝ) :
    (∫ t : ℝ, cubicBesselTriangle (s,t)) =
      if 0 < s then s^(-1/3:ℝ)*Real.exp (-s) else 0 := by
  have he : (fun t : ℝ => cubicBesselTriangle (s,t))=
      (Ioo 0 s).indicator (fun _ => cubicBesselSumWeight s) := by
    ext t
    simp only [cubicBesselTriangle,Set.indicator]
  rw [he]
  rw [integral_indicator measurableSet_Ioo,setIntegral_const,smul_eq_mul,Real.volume_real_Ioo]
  by_cases hs : 0 < s
  · rw [ite_eq_left hs,sub_zero,max_eq_left hs.le,cubicBesselSumWeight]
    have hp : s*s^(-4/3:ℝ)=s^(-1/3:ℝ) := by
      calc
        _ = s^(1:ℝ)*s^(-4/3:ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [←Real.rpow_add hs]; norm_num
    rw [←mul_assoc,hp]
  · rw [ite_eq_right hs,sub_zero,max_eq_right (le_of_not_gt hs),zero_mul]

lemma cubicBesselTriangle_integrable :
    Integrable cubicBesselTriangle ((volume : Measure ℝ).prod volume) := by
  have hm : Measurable cubicBesselTriangle := by
    unfold cubicBesselTriangle cubicBesselSumWeight
    apply Measurable.ite ?_ (by fun_prop) measurable_const
    exact (isOpen_lt continuous_const continuous_snd).measurableSet.inter
      (isOpen_lt continuous_snd continuous_fst).measurableSet
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall cubicBesselTriangle_inner_integrable
  · have hi := integrable_laplace_rpow (by norm_num : (0:ℝ) < 2/3) (by norm_num : (0:ℝ) < 1)
    rw [←integrable_indicator_iff measurableSet_Ioi] at hi
    apply hi.congr
    filter_upwards with s
    rw [show (∫ t : ℝ, ‖cubicBesselTriangle (s,t)‖)=
        ∫ t : ℝ, cubicBesselTriangle (s,t) from integral_congr_ae
          (Filter.Eventually.of_forall (fun t => Real.norm_of_nonneg (cubicBesselTriangle_nonneg (s,t)))),
      cubicBesselTriangle_inner]
    by_cases hs : 0 < s <;> simp [Set.indicator,hs]
    congr 2
    norm_num

lemma cubicBesselTriangle_integral :
    (∫ p : ℝ × ℝ, cubicBesselTriangle p ∂((volume : Measure ℝ).prod volume))=Real.Gamma (2/3) := by
  rw [integral_prod _ cubicBesselTriangle_integrable]
  simp_rw [cubicBesselTriangle_inner]
  change (∫ s : ℝ, (Ioi 0).indicator (fun s => s^(-1/3:ℝ)*Real.exp (-s)) s)=_
  rw [integral_indicator measurableSet_Ioi]
  convert laplace_rpow (by norm_num : (0:ℝ) < 2/3) (by norm_num : (0:ℝ) < 1) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)

lemma cubicBesselSumShear_preserving :
    MeasurePreserving cubicBesselSumShear ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := measurePreserving_add_prod volume volume

lemma cubicBesselSumShear_weight (p : ℝ × ℝ) :
    cubicBesselTriangle (cubicBesselSumShear p)=
      (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)).indicator
        (fun p : ℝ × ℝ => cubicBesselSumWeight (p.1+p.2)) p := by
  have he : p.2 ∈ Ioo 0 (p.1+p.2) ↔ p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
    simp only [mem_Ioo,mem_prod,mem_Ioi]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  simp only [cubicBesselTriangle,cubicBesselSumShear,MeasurableEquiv.coe_mk,Equiv.coe_fn_mk,he,
    Set.indicator]

lemma cubicBesselSumWeight_integrable :
    Integrable (fun p : ℝ × ℝ => cubicBesselSumWeight (p.1+p.2))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hi := cubicBesselSumShear_preserving.integrable_comp_of_integrable cubicBesselTriangle_integrable
  simp only [Function.comp_def,cubicBesselSumShear_weight] at hi
  rw [integrable_indicator_iff (measurableSet_Ioi.prod measurableSet_Ioi)] at hi
  change Integrable _ ((volume.prod volume).restrict (Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))) at hi
  simpa only [Measure.prod_restrict] using hi

theorem cubicBesselSumWeight_integral :
    (∫ p : ℝ × ℝ, cubicBesselSumWeight (p.1+p.2)
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))))=Real.Gamma (2/3) := by
  have he := cubicBesselSumShear_preserving.integral_comp' cubicBesselTriangle
  simp only [cubicBesselSumShear_weight] at he
  rw [integral_indicator (measurableSet_Ioi.prod measurableSet_Ioi),cubicBesselTriangle_integral] at he
  simpa only [Measure.prod_restrict] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselSquareHeat
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square of the fixed Schlaefli integral as a positive double heat
integral. Its inner Mellin integral reduces to the proved Gamma sum. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicBesselSquareHeat_nonneg {p : ℝ × ℝ} (hp : p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ))
    {x : ℝ} (hx : 0 < x) : 0 ≤ cubicBesselSquareHeat p x :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hx.le _) (cubicBesselHeat_nonneg hp.1))
    (cubicBesselHeat_nonneg hp.2)

lemma cubicBesselSquareHeat_laplace (t u x : ℝ) :
    cubicBesselSquareHeat (t,u) x =
      (t^(-4/3:ℝ)*u^(-4/3:ℝ)*Real.exp (-(t+u)))*
        (x^((4/3:ℝ)-1)*Real.exp (-(1/t+1/u)*x)) := by
  have he : -(1/t+1/u)*x=(-x/t)+(-x/u) := by ring
  rw [he,Real.exp_add,show -(t+u)= -t + -u by ring,Real.exp_add]
  norm_num only [show (4/3:ℝ)-1=1/3 by norm_num]
  unfold cubicBesselSquareHeat cubicBesselHeat
  ring_nf

lemma cubicBesselSquareHeat_inner_integrable {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    IntegrableOn (cubicBesselSquareHeat (t,u)) (Ioi 0) := by
  have hr : 0 < 1/t+1/u := add_pos (one_div_pos.mpr ht) (one_div_pos.mpr hu)
  have hi := (integrable_laplace_rpow (by norm_num : (0:ℝ) < 4/3) hr).const_mul
    (t^(-4/3:ℝ)*u^(-4/3:ℝ)*Real.exp (-(t+u)))
  apply hi.congr
  filter_upwards with x
  exact (cubicBesselSquareHeat_laplace t u x).symm

lemma cubicBesselSquareHeat_inner {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    (∫ x in Ioi (0:ℝ), cubicBesselSquareHeat (t,u) x)=
      Real.Gamma (4/3)*cubicBesselSumWeight (t+u) := by
  have hr : 0 < 1/t+1/u := add_pos (one_div_pos.mpr ht) (one_div_pos.mpr hu)
  simp_rw [cubicBesselSquareHeat_laplace t u]
  rw [integral_const_mul,laplace_rpow (by norm_num : (0:ℝ) < 4/3) hr]
  have he : t*u*(1/t+1/u)=t+u := by field_simp; ring
  have hp : t^(-4/3:ℝ)*u^(-4/3:ℝ)*(1/t+1/u)^(-4/3:ℝ)=(t+u)^(-4/3:ℝ) := by
    rw [←Real.mul_rpow ht.le hu.le,←Real.mul_rpow (mul_pos ht hu).le hr.le,he]
  unfold cubicBesselSumWeight
  calc
    _ = Real.Gamma (4/3)*(t^(-4/3:ℝ)*u^(-4/3:ℝ)*(1/t+1/u)^(-4/3:ℝ))*
        Real.exp (-(t+u)) := by ring_nf
    _ = _ := by rw [hp]; ring

lemma cubicBesselKernel_sq_integral {x : ℝ} (hx : 0 < x) :
    (cubicBesselKernel x)^2 =
      ∫ p : ℝ × ℝ, cubicBesselSquareHeat p x
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hp : (x^(1/6:ℝ))^2=x^(1/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
    congr 1
    norm_num
  rw [cubicBesselKernel,mul_pow,hp]
  rw [show (∫ t in Ioi (0:ℝ), cubicBesselHeat x t)^2=
      ∫ p : ℝ × ℝ, cubicBesselHeat x p.1*cubicBesselHeat x p.2
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) by
          rw [integral_prod_mul,pow_two],←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with p
  unfold cubicBesselSquareHeat
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicBesselSquareIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Fubini evaluates the square of the cubic Bessel kernel.
Only the fixed order one third and the needed zero Mellin exponent occur. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

private lemma positive_pair_ae :
    ∀ᵐ p : ℝ × ℝ ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))),
      p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ) := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioi.prod measurableSet_Ioi)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact ⟨ht,hu⟩

lemma cubicBesselSquareHeat_inner_norm {p : ℝ × ℝ}
    (hp : p ∈ Ioi (0:ℝ) ×ˢ Ioi (0:ℝ)) :
    (∫ x in Ioi (0:ℝ), ‖cubicBesselSquareHeat p x‖)=
      Real.Gamma (4/3)*cubicBesselSumWeight (p.1+p.2) := by
  rw [←cubicBesselSquareHeat_inner hp.1 hp.2]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact Real.norm_of_nonneg (cubicBesselSquareHeat_nonneg hp hx)

lemma cubicBesselSquareHeat_integrable :
    Integrable (fun q : (ℝ × ℝ) × ℝ => cubicBesselSquareHeat q.1 q.2)
      (((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))).prod
        (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => cubicBesselSquareHeat q.1 q.2) := by
    unfold cubicBesselSquareHeat cubicBesselHeat
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [positive_pair_ae] with p hp
    exact cubicBesselSquareHeat_inner_integrable hp.1 hp.2
  · apply (cubicBesselSumWeight_integrable.const_mul (Real.Gamma (4/3))).congr
    filter_upwards [positive_pair_ae] with p hp
    exact (cubicBesselSquareHeat_inner_norm hp).symm

theorem cubicBesselKernel_sq_integral_value :
    (∫ x in Ioi (0:ℝ), (cubicBesselKernel x)^2)=Real.Gamma (4/3)*Real.Gamma (2/3) := by
  calc
    _ = ∫ x in Ioi (0:ℝ), ∫ p : ℝ × ℝ, cubicBesselSquareHeat p x
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact cubicBesselKernel_sq_integral hx
    _ = ∫ p : ℝ × ℝ, (∫ x in Ioi (0:ℝ), cubicBesselSquareHeat p x)
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) :=
      (integral_integral_swap cubicBesselSquareHeat_integrable).symm
    _ = ∫ p : ℝ × ℝ, Real.Gamma (4/3)*cubicBesselSumWeight (p.1+p.2)
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
      apply integral_congr_ae
      filter_upwards [positive_pair_ae] with p hp
      exact cubicBesselSquareHeat_inner hp.1 hp.2
    _ = _ := by rw [integral_const_mul,cubicBesselSumWeight_integral]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerDerivative
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First vertical derivative of the actual cubic Whittaker kernel,
with arbitrary fixed power decay. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaWhittaker_hasDerivAt {v : ℝ} (hv : 0<v) :
    HasDerivAt cubicThetaWhittaker (cubicThetaWhittakerDerivative v) v := by
  have hx : 0<(2*Real.pi*v)^2 := by positivity
  have hp := ((hasDerivAt_id v).const_mul (2*Real.pi)).pow 2
  have hb := (cubicBesselKernel_hasDerivAt hx).comp v hp
  have h := ((hasDerivAt_id v).div_const 2).mul hb
  refine (h.ofReal_comp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · beta_reduce
    simp [cubicThetaWhittaker,Function.comp_apply,Pi.mul_apply,Pi.pow_apply]
  · simp only [cubicThetaWhittakerDerivative,Function.comp_apply,Pi.pow_apply,id_eq,
      Nat.cast_ofNat,mul_one]
    push_cast
    ring

lemma cubicWhittakerDerivativePowerConstant_pos {k : ℕ} (hk : 1≤k) :
    0 < cubicWhittakerDerivativePowerConstant k := by
  have hkR : (1:ℝ)≤k := by exact_mod_cast hk
  have hG := Real.Gamma_pos_of_pos (show 0<(k:ℝ)-1/3 by linarith)
  have hD := cubicBesselDerivativePowerConstant_pos hk
  unfold cubicWhittakerDerivativePowerConstant
  positivity

theorem cubicThetaWhittakerDerivative_power_bound (k : ℕ) (hk : 1≤k)
    {v : ℝ} (hv : 0<v) :
    ‖cubicThetaWhittakerDerivative v‖≤
      cubicWhittakerDerivativePowerConstant k*v^(1/3-2*(k:ℝ)) := by
  let x := (2*Real.pi*v)^2
  have hx : 0<x := by dsimp [x]; positivity
  have hK := cubicBesselKernel_power_bound k hk hx
  have hD := cubicBesselKernelDerivative_power_bound k hk hx
  have hp : x*x^(-5/6-(k:ℝ))=x^(1/6-(k:ℝ)) := by
    calc
      _ = x^(1:ℝ)*x^(-5/6-(k:ℝ)) := by rw [Real.rpow_one]
      _ = x^(1+(-5/6-(k:ℝ))) := (Real.rpow_add hx _ _).symm
      _ = _ := by congr 1; ring
  have hs : x^(1/6-(k:ℝ))=(2*Real.pi)^(1/3-2*(k:ℝ))*v^(1/3-2*(k:ℝ)) := by
    dsimp [x]
    rw [←Real.rpow_natCast_mul (by positivity : 0≤2*Real.pi*v)]
    norm_num only [Nat.cast_ofNat]
    rw [show (2:ℝ)*(1/6-(k:ℝ))=1/3-2*(k:ℝ) by ring,
      Real.mul_rpow (by positivity : 0≤2*Real.pi) hv.le]
  calc
    _ ≤ cubicBesselKernel x/2+x*‖cubicBesselKernelDerivative x‖ := by
      change ‖((cubicBesselKernel x/2+x*cubicBesselKernelDerivative x:ℝ):ℂ)‖≤_
      rw [Complex.norm_real]
      calc
        _ ≤ ‖cubicBesselKernel x/2‖+‖x*cubicBesselKernelDerivative x‖ := norm_add_le _ _
        _ = _ := by rw [norm_div,norm_mul,Real.norm_of_nonneg (cubicBesselKernel_nonneg hx.le),
          Real.norm_of_nonneg hx.le]; norm_num
    _ ≤ ((k.factorial:ℝ)*Real.Gamma ((k:ℝ)-1/3)*x^(1/6-(k:ℝ)))/2+
        x*(cubicBesselDerivativePowerConstant k*x^(-5/6-(k:ℝ))) :=
      add_le_add (div_le_div_of_nonneg_right hK (by norm_num))
        (mul_le_mul_of_nonneg_left hD hx.le)
    _ = _ := by
      rw [show x*(cubicBesselDerivativePowerConstant k*x^(-5/6-(k:ℝ)))=
        cubicBesselDerivativePowerConstant k*(x*x^(-5/6-(k:ℝ))) by ring,hp,hs]
      unfold cubicWhittakerDerivativePowerConstant
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute squared Mellin masses for the fixed cubic Whittaker kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaWhittaker_sq_bound {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaWhittaker v‖^2 ≤ cubicWhittakerExpConstant^2 *
      v^(4/3:ℝ) * Real.exp (-(4*Real.pi*v)) := by
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) (cubicThetaWhittaker_exponential_bound hv) 2).trans_eq
  have hp : (v^(2/3:ℝ))^2=v^(4/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hv.le]
    congr 1
    norm_num
  have he : (Real.exp (-(2*Real.pi*v)))^2=Real.exp (-(4*Real.pi*v)) := by
    rw [←Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [mul_pow,mul_pow,hp,he]

lemma cubicWhittakerEnergy_integrable {σ : ℝ} (hσ : 0 ≤ σ) :
    IntegrableOn (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker v‖^2) (Ioi 0) := by
  have hc : ContinuousOn (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker v‖^2) (Ioi 0) := by
    intro v hv
    have hW := cubicThetaWhittaker_continuousAt hv
    have hp : ContinuousAt (fun v : ℝ => v^(2*σ-1)) v := by
      exact Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hv))
    exact (hp.mul (hW.norm.pow 2)).continuousWithinAt
  have hi := (integrable_laplace_rpow (by linarith : 0 < 2*σ+4/3)
    (by positivity : 0 < 4*Real.pi)).const_mul (cubicWhittakerExpConstant^2)
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _))]
  apply (mul_le_mul_of_nonneg_left (cubicThetaWhittaker_sq_bound hv)
    (Real.rpow_nonneg hv.le _)).trans_eq
  rw [show v^(2*σ-1)*(cubicWhittakerExpConstant^2*v^(4/3:ℝ)*
      Real.exp (-(4*Real.pi*v))) = cubicWhittakerExpConstant^2*
      (v^(2*σ-1)*v^(4/3:ℝ))*Real.exp (-(4*Real.pi*v)) by ring,
    ←Real.rpow_add hv]
  rw [show 2*σ-1+4/3=2*σ+4/3-1 by ring,
    show -(4*Real.pi*v)=-(4*Real.pi)*v by ring]
  ring

lemma cubicWhittakerEnergy_mass_scale (σ : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ v in Ioi (0:ℝ), v^(2*σ-1)*‖cubicThetaWhittaker (r*v)‖^2) =
      r^(-2*σ)*cubicWhittakerEnergyMass σ := by
  have hcancel : r^(1-2*σ)*r^(2*σ-1)=1 := by
    rw [←Real.rpow_add hr]
    ring_nf
    exact Real.rpow_zero _
  have he : (∫ v in Ioi (0:ℝ), v^(2*σ-1)*‖cubicThetaWhittaker (r*v)‖^2) =
      r^(1-2*σ)*(∫ v in Ioi (0:ℝ), (r*v)^(2*σ-1)*‖cubicThetaWhittaker (r*v)‖^2) := by
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [Real.mul_rpow hr.le hv.le]
    simp only [←mul_assoc,hcancel,one_mul]
  rw [he,integral_comp_mul_left_Ioi
    (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker v‖^2) 0 hr,mul_zero]
  simp only [smul_eq_mul]
  have hp : r^(1-2*σ)*r⁻¹=r^(-2*σ) := by
    rw [←Real.rpow_neg_one,←Real.rpow_add hr]
    congr 1
    ring
  rw [←mul_assoc,hp]
  rfl

lemma cubicWhittakerEnergy_scaled_integrable {σ : ℝ} (hσ : 0 ≤ σ)
    {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker (r*v)‖^2) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_mul_left_iff
    (fun v : ℝ => v^(2*σ-1)*‖cubicThetaWhittaker v‖^2) 0 hr).mpr
    (by simpa only [mul_zero] using cubicWhittakerEnergy_integrable hσ)
  have hi := h.const_mul (r^(1-2*σ))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  rw [Real.mul_rpow hr.le hv.le]
  have hp : r^(1-2*σ)*r^(2*σ-1)=1 := by
    rw [←Real.rpow_add hr]
    ring_nf
    exact Real.rpow_zero _
  rw [←mul_assoc,←mul_assoc,hp,one_mul]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerEnergyContinuity
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuity of the squared Mellin mass at the exponent needed in the
Rankin integral. The two endpoint powers give an integrable majorant. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicWhittakerEnergy_domination {σ v : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (hv : 0 < v) :
    ‖v^(2*σ-1)*‖cubicThetaWhittaker v‖^2‖ ≤
      v^(2*(0:ℝ)-1)*‖cubicThetaWhittaker v‖^2 +
      v^(2*(1:ℝ)-1)*‖cubicThetaWhittaker v‖^2 := by
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _))]
  by_cases hv1 : v ≤ 1
  · have hp : v^(2*σ-1) ≤ v^(2*(0:ℝ)-1) :=
      Real.rpow_le_rpow_of_exponent_ge hv hv1 (by linarith)
    exact (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans
      (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _)))
  · have hp : v^(2*σ-1) ≤ v^(2*(1:ℝ)-1) :=
      Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hv1) (by linarith)
    exact (mul_le_mul_of_nonneg_right hp (sq_nonneg _)).trans
      (le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _)))

theorem cubicWhittakerEnergyMass_tendsto_zero :
    Tendsto cubicWhittakerEnergyMass (𝓝[>] 0) (𝓝 (cubicWhittakerEnergyMass 0)) := by
  let bound (v : ℝ) := v^(2*(0:ℝ)-1)*‖cubicThetaWhittaker v‖^2 +
      v^(2*(1:ℝ)-1)*‖cubicThetaWhittaker v‖^2
  have hb : IntegrableOn bound (Ioi 0) :=
    (cubicWhittakerEnergy_integrable (by norm_num : (0:ℝ) ≤ 0)).add
      (cubicWhittakerEnergy_integrable (by norm_num : (0:ℝ) ≤ 1))
  apply tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hb ?_
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (cubicWhittakerEnergy_integrable (le_of_lt hσ)).aestronglyMeasurable
  · have hs0 : ∀ᶠ σ : ℝ in 𝓝 0, σ < 1 := Iio_mem_nhds (by norm_num : (0:ℝ) < 1)
    have hs : ∀ᶠ σ : ℝ in 𝓝[>] 0, σ < 1 := hs0.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin,hs] with σ hσ hσ1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact cubicWhittakerEnergy_domination hσ.le hσ1.le hv
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hp : ContinuousAt (fun σ : ℝ => v^(2*σ-1)) 0 :=
      (Real.continuousAt_const_rpow (ne_of_gt hv)).comp (f := fun σ : ℝ => 2*σ-1) (by fun_prop)
    exact (hp.mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicWhittakerEnergyValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact archimedean constant in the zero-exponent energy integral. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

theorem cubicWhittakerEnergyMass_zero :
    cubicWhittakerEnergyMass 0=
      Real.Gamma (4/3)*Real.Gamma (2/3)/(32*Real.pi^2) := by
  let c : ℝ := (2*Real.pi)^2
  have hc : 0 < c := by dsimp [c]; positivity
  calc
    _ = (1/8:ℝ)*(∫ v in Ioi (0:ℝ), (2*v^((2:ℝ)-1))*
        (cubicBesselKernel (c*v^(2:ℝ)))^2) := by
      rw [←integral_const_mul]
      unfold cubicWhittakerEnergyMass
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [cubicThetaWhittaker_norm hv]
      norm_num only [mul_zero,zero_sub,Real.rpow_neg_one,Real.rpow_one,Real.rpow_two]
      rw [show (2*Real.pi*v)^2=c*v^2 by dsimp [c]; ring]
      field_simp
      ring
    _ = (1/8:ℝ)*(∫ x in Ioi (0:ℝ), (cubicBesselKernel (c*x))^2) := by
      rw [show (∫ v in Ioi (0:ℝ), (2*v^((2:ℝ)-1))*
          (cubicBesselKernel (c*v^(2:ℝ)))^2)=
          ∫ x in Ioi (0:ℝ), (cubicBesselKernel (c*x))^2 from
        by simpa only [smul_eq_mul] using
          (integral_comp_rpow_Ioi_of_pos (g := fun x : ℝ => (cubicBesselKernel (c*x))^2)
            (by norm_num : (0:ℝ) < 2))]
    _ = (1/8:ℝ)*(c⁻¹*(Real.Gamma (4/3)*Real.Gamma (2/3))) := by
      rw [integral_comp_mul_left_Ioi (fun x : ℝ => (cubicBesselKernel x)^2) 0 hc,mul_zero,
        cubicBesselKernel_sq_integral_value]
      rfl
    _ = _ := by
      dsimp [c]
      field_simp
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Divisor and pair-product multiplicities with a bounded number of prime bases. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealExponentOf_inj_primary {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (h : idealExponentOf a = idealExponentOf b) : a = b := by
  have hA := idealExponentOf_associated (primary_ne_zero ha)
  have hB := idealExponentOf_associated (primary_ne_zero hb)
  rw [h] at hA
  exact primary_associated_eq ha hb (hA.symm.trans hB)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerSeries
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Euler factors for the complete ideal Dirichlet series.
These retain the ramified factors lost in primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealDirichlet_single_exclusion (p : EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    normDirichletSeries (primeIdealRestriction {p} χ) idealExponentNorm s =
      (1-χ (Finsupp.single p 1)*(idealExponentNorm (Finsupp.single p 1):ℂ)^(-s))*
        normDirichletSeries χ idealExponentNorm s := by
  let δ : EisensteinIdealExponent := Finsupp.single p 1
  let f (ν : EisensteinIdealExponent) := χ ν*(idealExponentNorm ν:ℂ)^(-s)
  let g (ν : EisensteinIdealExponent) := if δ ≤ ν then f ν else 0
  have hf : Summable f := (idealDirichlet_norm_summable χ hχ hs).of_norm
  have hg : Summable g := by
    convert hf.indicator {ν | δ ≤ ν} using 1
    all_goals try with_reducible_and_instances rfl
    ext ν
    by_cases hν : δ ≤ ν <;> simp [g,Set.indicator,hν]
  have hi : Function.Injective (fun ν : EisensteinIdealExponent => δ+ν) :=
    fun _ _ h => add_left_cancel h
  have hshift : (∑' ν, g ν)=f δ*(∑' ν, f ν) := by
    have hsup : Function.support g ⊆ Set.range (fun ν => δ+ν) := by
      intro ν hν
      have hd : δ ≤ ν := by
        by_contra hn
        exact hν (by simp [g,hn])
      exact ⟨ν-δ,add_tsub_cancel_of_le hd⟩
    rw [←hi.tsum_eq hsup]
    simp only [g,le_add_of_nonneg_right zero_le,ite_true, if_true]
    simp_rw [show ∀ ν, f (δ+ν)=f δ*f ν from fun ν => idealDirichlet_weight_add χ hadd s δ ν]
    exact tsum_mul_left
  have he (ν : EisensteinIdealExponent) :
      primeIdealRestriction {p} χ ν*(idealExponentNorm ν:ℂ)^(-s)=f ν-g ν := by
    have hd : δ ≤ ν ↔ 0 < ν p := by
      simp only [δ,Finsupp.single_le_iff,Nat.one_le_iff_ne_zero,Nat.pos_iff_ne_zero]
    simp only [primeIdealRestriction,Finset.mem_singleton,forall_eq]
    by_cases hp : ν p=0
    · simp [f,g,hd,hp]
    · simp [f,g,hd,hp,Nat.pos_of_ne_zero hp]
  unfold normDirichletSeries
  simp_rw [he]
  rw [hf.tsum_sub hg,hshift]
  dsimp only [f,δ]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact frequency powers in the fixed-angular theta Mellin transform. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaAngularCoefficient_norm {a : Eisenstein → ℂ} (ℓ : ℤ)
    {n : Eisenstein} (hn : n ≠ 0) :
    ‖cubicThetaAngularCoefficient a ℓ n‖ = ‖cubicThetaFrequency n‖^ℓ.natAbs*‖a n‖ := by
  simp only [cubicThetaAngularCoefficient,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _),norm_theta hn,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAngularConvergence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence of the fixed-angular frequency derivatives.
An explicit summable lattice majorant absorbs every fixed derivative order. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_inverse_pow {n : Eisenstein} (hn : n ≠ 0) (k : ℕ) :
    ‖cubicThetaFrequency n‖^(-(k:ℝ)) ≤ (9:ℝ)^k := by
  calc
    _ ≤ (1/9:ℝ)^(-(k:ℝ)) := Real.rpow_le_rpow_of_nonpos (by norm_num)
      (cubicThetaFrequency_lower hn) (neg_nonpos.mpr (Nat.cast_nonneg k))
    _ = (9:ℝ)^k := by
      rw [Real.rpow_neg_eq_inv_rpow]
      norm_num only [one_div,inv_inv]
      rw [Real.rpow_natCast]

lemma cubicThetaAngular_kernel_bound (k : ℕ) {n : Eisenstein} (hn : n ≠ 0)
    {v : ℝ} (hv : 0 < v) :
    ‖cubicThetaFrequency n‖^k*‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖ ≤
      (cubicWhittakerPowerConstant (k+3)*(9:ℝ)^k*81^(7/3:ℝ))*
        v^(4/3-2*((k:ℝ)+3))*norm n^(-7/3:ℝ) := by
  have hr := cubicThetaFrequency_pos hn
  have hK := (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ k+3)).le
  have hw := cubicThetaWhittaker_power_bound (k+3) (by omega) (mul_pos hr hv)
  simp only [Nat.cast_add,Nat.cast_ofNat] at hw
  rw [Real.mul_rpow hr.le hv.le] at hw
  have hp : ‖cubicThetaFrequency n‖^k*‖cubicThetaFrequency n‖^(4/3-2*((k:ℝ)+3)) =
      ‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hr,←Real.rpow_add hr]
    congr 1
    ring
  calc
    _ ≤ ‖cubicThetaFrequency n‖^k*(cubicWhittakerPowerConstant (k+3)*
        (‖cubicThetaFrequency n‖^(4/3-2*((k:ℝ)+3))*v^(4/3-2*((k:ℝ)+3)))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = cubicWhittakerPowerConstant (k+3)*v^(4/3-2*((k:ℝ)+3))*
        (‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      calc
        _ = cubicWhittakerPowerConstant (k+3)*v^(4/3-2*((k:ℝ)+3))*
            (‖cubicThetaFrequency n‖^k*‖cubicThetaFrequency n‖^(4/3-2*((k:ℝ)+3))) := by ring
        _ = _ := by rw [hp]
    _ ≤ cubicWhittakerPowerConstant (k+3)*v^(4/3-2*((k:ℝ)+3))*
        ((9:ℝ)^k*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      gcongr
      exact cubicThetaFrequency_inverse_pow hn k
    _ = _ := by rw [cubicThetaFrequency_power hn]; ring

lemma cubicThetaAngular_term_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 0 < v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v n‖ ≤
      (C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
        v^(4/3-2*((ℓ.natAbs:ℝ)+3)))*norm n^(-4/3:ℝ) := by
  have hK := (cubicWhittakerPowerConstant_pos (by omega : 1 ≤ ℓ.natAbs+3)).le
  by_cases hn : n = 0
  · simp only [cubicThetaSeriesTerm,hn,ite_true, if_true,norm_zero]
    norm_num [norm]
  · have hN := norm_pos_of_ne_zero hn
    simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,norm_mul,Circle.norm_coe,mul_one,
      cubicThetaAngularCoefficient_norm ℓ hn]
    have hp : norm n*norm n^(-7/3:ℝ) = norm n^(-4/3:ℝ) := by
      calc
        _ = norm n^(1:ℝ)*norm n^(-7/3:ℝ) := by rw [Real.rpow_one]
        _ = norm n^(1+(-7/3:ℝ)) := (Real.rpow_add hN _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = ‖a n‖*(‖cubicThetaFrequency n‖^ℓ.natAbs*
          ‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖) := by ring
      _ ≤ (C*norm n)*((cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ))*
          v^(4/3-2*((ℓ.natAbs:ℝ)+3))*norm n^(-7/3:ℝ)) :=
        mul_le_mul (ha n hn) (cubicThetaAngular_kernel_bound ℓ.natAbs hn hv)
          (mul_nonneg (by positivity) (_root_.norm_nonneg _)) (mul_nonneg hC hN.le)
      _ = _ := by
        calc
          _ = (C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
              v^(4/3-2*((ℓ.natAbs:ℝ)+3)))*(norm n*norm n^(-7/3:ℝ)) := by ring
          _ = _ := by rw [hp]

/-- Every fixed signed angular derivative is an absolutely convergent
Fourier series at each positive height. -/
theorem cubicThetaAngular_summable {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0 ≤ C) (ha : ∀ n : Eisenstein, n ≠ 0 → ‖a n‖ ≤ C*norm n)
    (ℓ : ℤ) (hv : 0 < v) (z : ℂ) :
    Summable (cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z v) := by
  apply ((summable_eisenstein_norm_rpow (by norm_num : (1:ℝ) < 4/3)).mul_left
    (C*cubicWhittakerPowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
      v^(4/3-2*((ℓ.natAbs:ℝ)+3)))).of_norm_bounded
  intro n
  simpa only [neg_div] using cubicThetaAngular_term_bound hC ha ℓ hv z n

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaInversionGeometry
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The geometric inversion in the cubic theta transformation, restricted
only by positive height and nonzero level. No automorphy law is assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaInversion_center (q : ℂ) {v : ℝ} (hv : 0 < v) :
    cubicThetaInversion q (0,v) = (0,(Complex.normSq q*v)⁻¹) := by
  apply Prod.ext
  · simp [cubicThetaInversion]
  · dsimp [cubicThetaInversion,cubicThetaRadius]
    simp only [map_zero,zero_add]
    by_cases hq : q = 0
    · simp [hq]
    · have hN : Complex.normSq q ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hq)
      field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact squared sizes of the theta coefficients, for normalization by
their Fourier energy. The zero classes remain in the formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaTwistedGauss_unit_lambda_norm {c : Eisenstein} (hc : primary c)
    (hs : Squarefree c) (u : Eisensteinˣ) :
    ‖cubicThetaTwistedGauss c ((u:Eisenstein)^4*lambdaE^2)‖=1 := by
  have hu : IsCoprime c ((u:Eisenstein)^4) := by
    refine ⟨0,(↑(u⁻¹):Eisenstein)^4,?_⟩
    simp only [zero_mul,zero_add,←mul_pow]
    simp
  have hcop : IsCoprime c ((u:Eisenstein)^4*lambdaE^2) :=
    hu.mul_right (primary_coprime_lambda hc).pow_right
  rw [cubicThetaTwistedGauss,norm_mul,norm_star,
    norm_cubicSymbol_of_isCoprime hc hcop,norm_gauss_of_squarefree hc hs,one_mul]

lemma CubicThetaCoordinates.coefficient_norm {n : Eisenstein} (R : CubicThetaCoordinates n) :
    ‖R.coefficient‖=
      if R.order%3=0 ∧ 3≤R.order then R.amplitude
      else if R.order%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)
        then R.amplitude else 0 := by
  classical
  unfold coefficient
  split_ifs
  · rw [norm_mul,norm_mul,norm_star,cubicThetaUnitPhase_norm,
      cubicThetaTwistedGauss_unit_lambda_norm R.squarefree_primary R.squarefree,
      mul_one,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
  · rw [norm_mul,norm_star,norm_gauss_of_squarefree R.squarefree_primary R.squarefree,
      mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg R.amplitude_nonneg]
  · exact norm_zero

lemma CubicThetaCoordinates.amplitude_sq {n : Eisenstein} (R : CubicThetaCoordinates n) :
    R.amplitude^2=
      3^(8-2*((R.order/3:ℕ):ℝ))/(norm R.squarefreePart*(norm R.cubePart)^2) := by
  unfold amplitude
  rw [div_pow,mul_pow,Real.sq_sqrt (norm_nonneg _),
    ←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  congr 2
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact horizontal energy of the arithmetic residue model.
This retains the common scalar for its remaining normalization. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaArithmeticModelEnergyMeasureSpace
lemma cubicThetaTorusCoefficient_inner (F : CubicThetaTorusL2) (h : Eisenstein) :
    cubicThetaTorusCoefficient F h=inner ℂ (cubicThetaTorusBasis h) F := by
  unfold cubicThetaTorusCoefficient cubicThetaTorusBasis
  rw [←UnitAddTorus.mFourierBasis_repr,HilbertBasis.repr_apply_apply]

attribute [local instance] OAI.CubicFirstMoment.cubicThetaArithmeticModelEnergyProbability
lemma cubicThetaArithmeticModelRemainder_energy {v : ℝ} (hv : 0<v) :
    ‖ContinuousMap.toLp 2 volume ℂ (cubicThetaArithmeticModelRemainder v)‖^2=
      cubicThetaArithmeticFourierEnergy v := by
  rw [←cubicThetaTorus_parseval]
  simp only [cubicThetaArithmeticModelRemainder_coefficient hv,cubicThetaArithmeticFourierEnergy]

theorem cubicThetaArithmeticModelTorus_energy (A : ℂ) {v : ℝ} (hv : 0<v) :
    ‖ContinuousMap.toLp 2 volume ℂ (cubicThetaArithmeticModelTorus A v)‖^2=
      (cubicThetaConstant*v^(2/3:ℝ))^2+
        ‖A‖^2*cubicThetaArithmeticFourierEnergy v := by
  let L : C(UnitAddTorus (Fin 2),ℂ) →L[ℂ] CubicThetaTorusL2 :=
    ContinuousMap.toLp 2 volume ℂ
  let R := L (cubicThetaArithmeticModelRemainder v)
  have hz : inner ℂ (cubicThetaTorusBasis 0) R=0 := by
    rw [←cubicThetaTorusCoefficient_inner,cubicThetaArithmeticModelRemainder_coefficient hv]
    simp [cubicThetaArithmeticRowTerm]
  have hb : ‖cubicThetaTorusBasis 0‖=1 :=
    UnitAddTorus.mFourierBasis.orthonormal.norm_eq_one _
  change ‖L (cubicThetaArithmeticModelTorus A v)‖^2=_
  rw [cubicThetaArithmeticModelTorus,map_add,map_smul,map_smul,
    cubicThetaTorusFourier_toLp]
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜:=ℂ)
    (((cubicThetaConstant*v^(2/3:ℝ):ℝ):ℂ) • cubicThetaTorusBasis 0) (A • R)
    (by rw [inner_smul_left,inner_smul_right,hz,mul_zero,mul_zero])
  simp only [←sq] at he
  rw [he]
  rw [norm_smul,norm_smul,hb,mul_one,mul_pow,cubicThetaArithmeticModelRemainder_energy hv,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBaseScalarNonzero
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual common nonconstant coefficient is nonzero. Otherwise
global automorphy would force a pure height power to be invariant. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

theorem cubicThetaArithmeticBaseScalar_ne_zero : cubicThetaArithmeticBaseScalar≠0 := by
  intro hB
  let p : CubicThetaPoint := ⟨(0,1),by norm_num⟩
  let g₀ : SL(2,Eisenstein) := ⟨!![1,0;3,1],by simp [Matrix.det_fin_two]⟩
  have hg : g₀∈cubicThetaPrincipalGroup :=
    (cubicThetaPrincipalGroup_mem_iff g₀).mpr
      ⟨primary_one,dvd_zero _,dvd_refl _,primary_one⟩
  let g : cubicThetaPrincipalGroup := ⟨g₀,hg⟩
  have hp : (g • p).val.2=(1/10:ℝ) := by
    change (cubicThetaMobius (cubicThetaPrincipalComplex g) (0,1)).2=(1/10:ℝ)
    norm_num [cubicThetaMobius,cubicThetaMobiusDenominator,
      cubicThetaPrincipalComplex_apply,g,g₀]
    change (1+Complex.normSq (3:ℂ))⁻¹=(1/10:ℝ)
    norm_num [Complex.normSq_apply]
  have hC : 0 < cubicThetaConstant := by unfold cubicThetaConstant; positivity
  have hnorm (q : CubicThetaPoint) :
      ‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar q.val‖=
        cubicThetaConstant*q.val.2^(2/3:ℝ) := by
    rw [cubicThetaArithmeticModel,hB,zero_mul,add_zero,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (mul_pos hC (Real.rpow_pos_of_pos q.property _))]
  have he := congrArg (fun z : ℂ => ‖z‖) (cubicThetaArithmeticModel_automorphy g p)
  rw [norm_mul,cubicThetaKubotaValue_norm,one_mul,hnorm,hnorm,hp] at he
  change cubicThetaConstant*(1/10:ℝ)^(2/3:ℝ)=cubicThetaConstant*1^(2/3:ℝ) at he
  have hlt : (1/10:ℝ)^(2/3:ℝ)<1 := by
    simpa using Real.rpow_lt_rpow (by norm_num : (0:ℝ)≤1/10)
      (by norm_num : (1/10:ℝ)<1) (by norm_num : (0:ℝ)<2/3)
  rw [Real.one_rpow] at he
  have he' := (mul_left_cancel₀ hC.ne' he)
  exact (ne_of_lt hlt) he'

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelPullback
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Null sets on the arithmetic quotient lift to null sets upstairs.
The countable translates of positive strips supply the required exhaustion. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_1 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable

theorem cubicThetaQuotient_pull_ae {P : CubicThetaQuotient → Prop}
    (hP : ∀ᵐ q ∂cubicThetaQuotientMeasure,P q) :
    ∀ᵐ p ∂cubicThetaPointMeasure,P (cubicThetaQuotientMap p) := by
  have hs (n : ℕ) : ∀ᵐ p ∂cubicThetaPointMeasure,
      p∈cubicThetaCuspStrip (1/(n+1:ℝ)) → P (cubicThetaQuotientMap p) :=
    (ae_restrict_iff' (cubicThetaCuspStrip_measurable _)).mp
      (cubicThetaPositiveStrip_pull_ae (by positivity) hP)
  have hall : ∀ᵐ p ∂cubicThetaPointMeasure,∀ w : Eisenstein,∀ n : ℕ,
      cubicThetaPrincipalTranslation w • p∈cubicThetaCuspStrip (1/(n+1:ℝ)) →
        P (cubicThetaQuotientMap (cubicThetaPrincipalTranslation w • p)) :=
    ae_all_iff.mpr (fun w => ae_all_iff.mpr (fun n =>
      (measurePreserving_smul (cubicThetaPrincipalTranslation w)
        cubicThetaPointMeasure).quasiMeasurePreserving.ae (hs n)))
  filter_upwards [hall] with p hp
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt p.property
  obtain ⟨w,hw⟩ := cubicThetaCuspStrip_reduction p hn
  simpa only [cubicThetaQuotient_covering.map_smul] using hp w n hw

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBorelInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual inversion operator on quotient representatives, including
the cubic phase of the chosen Borel section. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaBorelInversionFunction_lift (f : CubicThetaQuotient → ℂ)
    (p : CubicThetaPoint) :
    cubicThetaBorelLift (cubicThetaBorelInversionFunction f) p=
      cubicThetaBorelLift f (cubicThetaFullInversion • p) := by
  obtain ⟨g,hg⟩ := cubicThetaBorelSheet_cover p
  rw [cubicThetaBorelLift,cubicThetaBorelPhase_sheet g hg,cubicThetaBorelInversionFunction,
    ←cubicThetaInversionConjugate_character g,←cubicThetaBorelLift_automorphy,
    ←cubicThetaInversion_intertwine]
  exact congrArg (fun x => cubicThetaBorelLift f (cubicThetaFullInversion • x)) hg

theorem cubicThetaBorelInversion_lift (f : CubicThetaGlobalL2) :
    cubicThetaBorelLift (cubicThetaBorelInversion f)
      =ᵐ[cubicThetaPointMeasure] fun p => cubicThetaBorelLift f (cubicThetaFullInversion • p) := by
  filter_upwards [cubicThetaQuotient_pull_ae
    (cubicThetaBorelInversionFunction_memLp f).coeFn_toLp] with p hp
  change ((cubicThetaBorelInversionFunction_memLp f).toLp _)
    (cubicThetaQuotientMap p)=_ at hp
  change cubicThetaBorelPhase p*((cubicThetaBorelInversionFunction_memLp f).toLp _)
    (cubicThetaQuotientMap p)=_
  rw [hp]
  exact cubicThetaBorelInversionFunction_lift f p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaArithmeticModelInversion
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inversion symmetry of the actual residual vector holds
pointwise for its continuous arithmetic Fourier expansion. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaBorelInversion_smooth (F : cubicThetaSmoothTests) :
    cubicThetaBorelInversion (cubicThetaGlobalMass F)=
      cubicThetaGlobalMass (cubicThetaInversionSmooth F) := by
  apply Lp.ext
  have hcomp := (cubicThetaIntegralQuotient_measurePreserving
    cubicThetaFullInversion).quasiMeasurePreserving.ae
      (cubicThetaSectionRepresentative_memLp F).coeFn_toLp
  filter_upwards [(cubicThetaBorelInversionFunction_memLp
    (cubicThetaGlobalMass F)).coeFn_toLp,
    (cubicThetaSectionRepresentative_memLp (cubicThetaInversionSmooth F)).coeFn_toLp,
    hcomp] with q hT hI hF
  change ((cubicThetaBorelInversionFunction_memLp (cubicThetaGlobalMass F)).toLp _) q=
    ((cubicThetaSectionRepresentative_memLp (cubicThetaInversionSmooth F)).toLp _) q
  rw [hT,hI]
  unfold cubicThetaBorelInversionFunction
  change cubicThetaBorelPhase (cubicThetaFullInversion • cubicThetaBorelSection q)*
    (cubicThetaGlobalMass F) (cubicThetaQuotientMap
      (cubicThetaFullInversion • cubicThetaBorelSection q))=
        F.val.val (cubicThetaFullInversion • cubicThetaBorelSection q)
  have he : (cubicThetaGlobalMass F) (cubicThetaQuotientMap
      (cubicThetaFullInversion • cubicThetaBorelSection q))=
      cubicThetaSectionRepresentative F (cubicThetaQuotientMap
        (cubicThetaFullInversion • cubicThetaBorelSection q)) := by
    change (cubicThetaGlobalMass F) (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)=
      cubicThetaSectionRepresentative F (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) at hF
    simpa only [←cubicThetaIntegralQuotientMap_apply,cubicThetaBorelSection_rightInverse q]
      using hF
  rw [he]
  exact cubicThetaBorelLift_section F (cubicThetaFullInversion • cubicThetaBorelSection q)

theorem cubicThetaBorelInversion_energy (u : cubicThetaGlobalEnergySpace) :
    cubicThetaBorelInversion (cubicThetaGlobalInclusion u)=
      cubicThetaGlobalInclusion (cubicThetaInversionEnergy u) := by
  refine cubicThetaGlobalEnergyTestLinear_dense.induction_on u
    (isClosed_eq (cubicThetaBorelInversion.continuous.comp cubicThetaGlobalInclusion.continuous)
      (cubicThetaGlobalInclusion.continuous.comp cubicThetaInversionEnergy.continuous)) ?_
  intro F
  change cubicThetaBorelInversion (cubicThetaGlobalInclusion (cubicThetaGlobalEnergyTest F))=
    cubicThetaGlobalInclusion (cubicThetaInversionEnergy (cubicThetaGlobalEnergyTest F))
  rw [cubicThetaInversionEnergy_test,cubicThetaGlobalInclusion_test,
    cubicThetaGlobalInclusion_test,cubicThetaBorelInversion_smooth]

theorem cubicThetaNormalizedArithmeticResidue_inversion :
    cubicThetaInversionEnergy cubicThetaNormalizedArithmeticResidue=
      cubicThetaNormalizedArithmeticResidue := by
  unfold cubicThetaNormalizedArithmeticResidue
  rw [map_smul,cubicThetaArithmeticResidueEnergy_inversion]

theorem cubicThetaArithmeticModel_inversion (p : CubicThetaPoint) :
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (cubicThetaFullInversion • p).val=
      cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val := by
  have hT := cubicThetaBorelInversion_lift
    (cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue)
  rw [cubicThetaBorelInversion_energy,cubicThetaNormalizedArithmeticResidue_inversion] at hT
  have hcomp := (measurePreserving_smul cubicThetaFullInversion
    cubicThetaPointMeasure).quasiMeasurePreserving.ae cubicThetaArithmeticModel_global_ae
  have he : (fun p : CubicThetaPoint => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar
      (cubicThetaFullInversion • p).val)=ᵐ[cubicThetaPointMeasure]
        (fun p => cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val) := by
    filter_upwards [cubicThetaArithmeticModel_global_ae,hcomp,hT] with q hq hSq hIq
    exact hSq.symm.trans (hIq.symm.trans hq)
  have hc := cubicThetaArithmeticModel_point_continuous cubicThetaArithmeticBaseScalar
  exact congrFun (Measure.eq_of_ae_eq he
    (hc.comp (continuous_const_smul cubicThetaFullInversion)) hc) p

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConjugateProjection
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite projection expressed in the original conjugate theta
function, including cancellation of its constant term. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaWhittaker_star (v : ℝ) : star (cubicThetaWhittaker v) = cubicThetaWhittaker v := by
  have he : cubicThetaWhittaker v = ((v/2*cubicBesselKernel ((2*Real.pi*v)^2):ℝ):ℂ) := by
    simp only [cubicThetaWhittaker,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  rw [he]
  exact Complex.conj_ofReal _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaNormalizedSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize the actual automorphic function by its nonzero Fourier
coefficient. Its constant coefficient is retained explicitly. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNormalizedSeriesSection_apply (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val p=
      cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaArithmeticCoefficient p.val := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar p.val=_
  unfold cubicThetaArithmeticModel cubicThetaSeriesConstant
  push_cast
  field_simp [cubicThetaArithmeticBaseScalar_ne_zero]

theorem cubicThetaNormalizedSeriesSection_inversion (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (cubicThetaFullInversion • p)=
      cubicThetaNormalizedSeriesSection.val p := by
  change cubicThetaArithmeticBaseScalar⁻¹*
    cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (cubicThetaFullInversion • p).val=_
  rw [cubicThetaArithmeticModel_inversion]
  rfl

theorem cubicThetaArithmetic_center_inversion {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v⁻¹)=
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v)+
        cubicThetaSeriesConstant*(((v^(2/3:ℝ):ℝ):ℂ)-(((v⁻¹)^(2/3:ℝ):ℝ):ℂ)) := by
  let p : CubicThetaPoint := ⟨(0,v),hv⟩
  have he := cubicThetaNormalizedSeriesSection_inversion p
  rw [cubicThetaNormalizedSeriesSection_apply (cubicThetaFullInversion • p),
    cubicThetaNormalizedSeriesSection_apply p] at he
  change cubicThetaSeriesConstant*
      (((cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (0,v)).2^(2/3:ℝ):ℝ):ℂ)+
    cubicThetaNonconstant cubicThetaArithmeticCoefficient
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) (0,v))=_ at he
  rw [cubicThetaFullInversion_complex,cubicThetaMobius_inversion one_ne_zero hv,
    cubicThetaInversion_center 1 hv] at he
  norm_num only [map_one,one_mul] at he
  linear_combination he

theorem cubicThetaArithmetic_center_small {v : ℝ} (hv : 0<v) :
    cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v)=
      cubicThetaNonconstant cubicThetaArithmeticCoefficient (0,v⁻¹)+
        cubicThetaSeriesConstant*((((v⁻¹)^(2/3:ℝ):ℝ):ℂ)-((v^(2/3:ℝ):ℝ):ℂ)) := by
  have he := cubicThetaArithmetic_center_inversion hv
  linear_combination -he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaVerticalTermDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual first vertical derivatives of the fixed-angular Fourier terms. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaSeriesTerm_vertical_hasDerivAt (a : Eisenstein → ℂ)
    (z : ℂ) {v : ℝ} (hv : 0<v) (n : Eisenstein) :
    HasDerivAt (fun y => cubicThetaSeriesTerm a z y n) (cubicThetaSeriesTermVertical a z v n) v := by
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTerm,cubicThetaSeriesTermVertical,hn,ite_true, if_true]
    exact hasDerivAt_const v 0
  have hr := cubicThetaFrequency_pos hn
  have h := ((cubicThetaWhittaker_hasDerivAt (mul_pos hr hv)).scomp v
    ((hasDerivAt_id v).const_mul ‖cubicThetaFrequency n‖)).const_mul (a n)
  have h' := h.mul_const (Real.fourierChar (tracePair (cubicThetaFrequency n) z):ℂ)
  refine (h'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · beta_reduce
    simp only [cubicThetaSeriesTerm,hn,ite_false, if_false,Function.comp_apply]
  · simp only [cubicThetaSeriesTermVertical,hn,ite_false, if_false,Complex.real_smul,mul_one]
    ring

lemma cubicThetaVertical_kernel_bound (k : ℕ) {n : Eisenstein} (hn : n≠0)
    {v : ℝ} (hv : 0<v) :
    ‖cubicThetaFrequency n‖^(k+1)*
        ‖cubicThetaWhittakerDerivative (‖cubicThetaFrequency n‖*v)‖≤
      (cubicWhittakerDerivativePowerConstant (k+3)*(9:ℝ)^k*81^(7/3:ℝ))*
        v^(1/3-2*((k:ℝ)+3))*norm n^(-7/3:ℝ) := by
  have hr := cubicThetaFrequency_pos hn
  have hD := (cubicWhittakerDerivativePowerConstant_pos (by omega : 1≤k+3)).le
  have hw := cubicThetaWhittakerDerivative_power_bound (k+3) (by omega) (mul_pos hr hv)
  simp only [Nat.cast_add,Nat.cast_ofNat] at hw
  rw [Real.mul_rpow hr.le hv.le] at hw
  have hp : ‖cubicThetaFrequency n‖^(k+1)*‖cubicThetaFrequency n‖^(1/3-2*((k:ℝ)+3))=
      ‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_add hr,←Real.rpow_add hr]
    congr 1
    push_cast
    ring
  calc
    _ ≤ ‖cubicThetaFrequency n‖^(k+1)*(cubicWhittakerDerivativePowerConstant (k+3)*
        (‖cubicThetaFrequency n‖^(1/3-2*((k:ℝ)+3))*v^(1/3-2*((k:ℝ)+3)))) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    _ = cubicWhittakerDerivativePowerConstant (k+3)*v^(1/3-2*((k:ℝ)+3))*
        (‖cubicThetaFrequency n‖^(-(k:ℝ))*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      calc
        _ = cubicWhittakerDerivativePowerConstant (k+3)*v^(1/3-2*((k:ℝ)+3))*
            (‖cubicThetaFrequency n‖^(k+1)*‖cubicThetaFrequency n‖^(1/3-2*((k:ℝ)+3))) := by ring
        _ = _ := by rw [hp]
    _ ≤ cubicWhittakerDerivativePowerConstant (k+3)*v^(1/3-2*((k:ℝ)+3))*
        ((9:ℝ)^k*‖cubicThetaFrequency n‖^(-14/3:ℝ)) := by
      gcongr
      exact cubicThetaFrequency_inverse_pow hn k
    _ = _ := by rw [cubicThetaFrequency_power hn]; ring

lemma cubicThetaAngular_vertical_term_bound {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hv : 0<v) (z : ℂ) (n : Eisenstein) :
    ‖cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) z v n‖≤
      (C*cubicWhittakerDerivativePowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*
        v^(1/3-2*((ℓ.natAbs:ℝ)+3)))*norm n^(-4/3:ℝ) := by
  by_cases hn : n=0
  · simp only [cubicThetaSeriesTermVertical,hn,ite_true, if_true,norm_zero]
    norm_num [norm]
  have hN := norm_pos_of_ne_zero hn
  simp only [cubicThetaSeriesTermVertical,hn,ite_false, if_false,norm_mul,Circle.norm_coe,mul_one,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _),
    cubicThetaAngularCoefficient_norm ℓ hn]
  have hp : norm n*norm n^(-7/3:ℝ)=norm n^(-4/3:ℝ) := by
    calc
      _ = norm n^(1:ℝ)*norm n^(-7/3:ℝ) := by rw [Real.rpow_one]
      _ = norm n^(1+(-7/3:ℝ)) := (Real.rpow_add hN _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = ‖a n‖*(‖cubicThetaFrequency n‖^(ℓ.natAbs+1)*
        ‖cubicThetaWhittakerDerivative (‖cubicThetaFrequency n‖*v)‖) := by rw [pow_succ]; ring
    _ ≤ (C*norm n)*((cubicWhittakerDerivativePowerConstant (ℓ.natAbs+3)*
        (9:ℝ)^ℓ.natAbs*81^(7/3:ℝ))*v^(1/3-2*((ℓ.natAbs:ℝ)+3))*norm n^(-7/3:ℝ)) :=
      mul_le_mul (ha n hn) (cubicThetaVertical_kernel_bound ℓ.natAbs hn hv)
        (mul_nonneg (by positivity) (_root_.norm_nonneg _)) (mul_nonneg hC hN.le)
    _ = _ := by
      calc
        _ = (C*cubicWhittakerDerivativePowerConstant (ℓ.natAbs+3)*
            (9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)*v^(1/3-2*((ℓ.natAbs:ℝ)+3)))*
            (norm n*norm n^(-7/3:ℝ)) := by ring
        _ = _ := by rw [hp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaVerticalSeriesDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical differentiation of the actual fixed-angular theta expansion.
A local lower height bound gives a single summable majorant. -/
noncomputable section
open Set
namespace CubicFirstMoment

theorem cubicThetaAngular_vertical_hasDerivAt {a : Eisenstein → ℂ} {C v : ℝ}
    (hC : 0≤C) (ha : ∀ n : Eisenstein,n≠0 → ‖a n‖≤C*norm n)
    (ℓ : ℤ) (hv : 0<v) (z : ℂ) :
    HasDerivAt (fun y => cubicThetaNonconstant (cubicThetaAngularCoefficient a ℓ) (z,y))
      (∑' n : Eisenstein,cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) z v n) v := by
  let K := C*cubicWhittakerDerivativePowerConstant (ℓ.natAbs+3)*(9:ℝ)^ℓ.natAbs*81^(7/3:ℝ)
  let p : ℝ := 1/3-2*((ℓ.natAbs:ℝ)+3)
  let u : Eisenstein → ℝ := fun n => (K*(v/2)^p)*norm n^(-4/3:ℝ)
  have hK : 0≤K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC
      (cubicWhittakerDerivativePowerConstant_pos (by omega : 1≤ℓ.natAbs+3)).le)
      (by positivity)) (by positivity)
  have hp : p≤0 := by
    dsimp [p]
    have hk : (0:ℝ)≤ℓ.natAbs := Nat.cast_nonneg _
    linarith
  have hu : Summable u := by
    simpa only [u,neg_div] using
      (summable_eisenstein_norm_rpow (by norm_num : (1:ℝ)<4/3)).mul_left (K*(v/2)^p)
  have hg (n : Eisenstein) (y : ℝ) (hy : y∈Ioi (v/2)) :
      HasDerivAt (fun t => cubicThetaSeriesTerm (cubicThetaAngularCoefficient a ℓ) z t n)
        (cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) z y n) y :=
    cubicThetaSeriesTerm_vertical_hasDerivAt _ z (lt_trans (by positivity) hy) n
  have hb (n : Eisenstein) (y : ℝ) (hy : y∈Ioi (v/2)) :
      ‖cubicThetaSeriesTermVertical (cubicThetaAngularCoefficient a ℓ) z y n‖≤u n := by
    have hy0 : 0<y := lt_trans (by positivity) hy
    have hpower : y^p≤(v/2)^p :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hy.le hp
    calc
      _ ≤ (K*y^p)*norm n^(-4/3:ℝ) :=
        cubicThetaAngular_vertical_term_bound hC ha ℓ hy0 z n
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hK)
        (Real.rpow_nonneg (norm_nonneg n) _)
  exact hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi (convex_Ioi (v/2)).isPreconnected
    hg hb (show v∈Ioi (v/2) by change v/2<v; linarith)
    (cubicThetaAngular_summable hC ha ℓ hv z) (by change v/2<v; linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMellinReciprocity
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin continuation of the actual arithmetic theta expansion.
The undetermined constant-to-Fourier ratio remains visible in both residues. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaArithmeticAxis_small {v : ℝ} (hv : 0<v) :
    cubicThetaArithmeticAxis v=cubicThetaArithmeticAxis v⁻¹+
      cubicThetaSeriesConstant*((v:ℂ)^(-(2/3:ℂ))-(v:ℂ)^(2/3:ℂ)) := by
  have hp : ((v^(2/3:ℝ):ℝ):ℂ)=(v:ℂ)^(2/3:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_ofNat] using
      Complex.ofReal_cpow hv.le (2/3:ℝ)
  have hi : (((v⁻¹)^(2/3:ℝ):ℝ):ℂ)=(v:ℂ)^(-(2/3:ℂ)) := by
    rw [Complex.ofReal_cpow (inv_nonneg.mpr hv.le),Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hv.le,←Complex.cpow_neg]
    norm_num
  simpa only [cubicThetaArithmeticAxis,hp,hi] using cubicThetaArithmetic_center_small hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaLevelReciprocity
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Put the genuine primary-level theta transformation on a symmetric
height scale, before Mellin integration. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaLevelScale_pos {q : Eisenstein} (hq : primary q) :
    0 < cubicThetaLevelScale q :=
  inv_pos.mpr (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (primary_ne_zero hq)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCommonIndex
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual dual support is indexed once by its unit, ramified order,
squarefree primary factor and primary cube factor. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaCommonNumerator_injective : Function.Injective cubicThetaCommonNumerator := by
  rintro ⟨u,k,cd⟩ ⟨v,l,ef⟩ he
  have hp (x : CubicThetaPrimaryPair) : primary (x.val.1*x.val.2^3) :=
    primary_mul x.property.1 (by
      simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using
        primary_mul x.property.2.1 (primary_mul x.property.2.1 x.property.2.1))
  have h := unit_ramified_primary_unique (hp cd) (hp ef) he
  have hc := primary_squarefree_cube_unique cd.property.1 cd.property.2.1
    ef.property.1 ef.property.2.1 cd.property.2.2 ef.property.2.2 h.2.2
  have hcd : cd=ef := Subtype.ext (Prod.ext hc.1 hc.2)
  exact Prod.ext h.1 (Prod.ext h.2.1 hcd)

lemma cubicThetaCommonNumerator_range (n : Eisenstein) :
    n∈Set.range cubicThetaCommonNumerator ↔ Nonempty (CubicThetaCoordinates n) := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨cubicThetaCommonCoordinates x⟩
  · rintro ⟨R⟩
    refine ⟨(R.unit,R.order,⟨(R.squarefreePart,R.cubePart),
      R.squarefree_primary,R.cube_primary,R.squarefree⟩),?_⟩
    exact R.numerator_eq.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientMass
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact Dirichlet mass of the literal theta coefficients. The
unit, ramified, squarefree and cube factors are kept separate. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaCoefficientMass_reindex (σ : ℝ) :
    cubicThetaCoefficientMass σ = ∑' x : CubicThetaCommonIndex,
      cubicThetaCoefficientMassTerm σ (cubicThetaCommonNumerator x) := by
  unfold cubicThetaCoefficientMass
  apply (cubicThetaCommonNumerator_injective.tsum_eq ?_).symm
  intro n hn
  apply (cubicThetaCommonNumerator_range n).mpr
  by_contra he
  exact hn (by simp [cubicThetaCoefficientMassTerm,cubicThetaArithmeticCoefficient,he])

lemma cubicThetaCoordinates_norm {n : Eisenstein} (R : CubicThetaCoordinates n) :
    norm n = 3^R.order * norm R.squarefreePart * (norm R.cubePart)^3 := by
  conv_lhs => rw [R.numerator_eq]
  rw [norm_mul_eq,norm_mul_eq,norm_mul_eq,eisenstein_norm_pow,eisenstein_norm_pow]
  have hu : norm (R.unit:Eisenstein) = 1 := norm_of_isUnit R.unit.isUnit
  have hLam : norm lambdaE = 3 := traceLambda_normSq
  rw [hu,hLam,one_mul]
  ring

lemma CubicThetaCoordinates.mass_term {n : Eisenstein} (R : CubicThetaCoordinates n)
    (σ : ℝ) :
    cubicThetaCoefficientMassTerm σ n =
      (if R.order%3=0 ∧ 3 ≤ R.order then (1:ℝ)
       else if R.order%3=1 ∧ ((R.unit:Eisenstein)=1 ∨ (R.unit:Eisenstein)=-1)
         then 1 else 0) *
      3^(8-2*((R.order/3:ℕ):ℝ)-(R.order:ℝ)*σ) *
      (norm R.squarefreePart)^(-(1+σ)) *
      (norm R.cubePart)^(-(2+3*σ)) := by
  have hc := norm_pos_of_ne_zero (primary_ne_zero R.squarefree_primary)
  have hd := norm_pos_of_ne_zero (primary_ne_zero R.cube_primary)
  have hpow : (norm n)^(-σ) =
      3^(-(R.order:ℝ)*σ) * (norm R.squarefreePart)^(-σ) *
        (norm R.cubePart)^(-3*σ) := by
    rw [cubicThetaCoordinates_norm R,
      Real.mul_rpow (mul_nonneg (by positivity) hc.le) (pow_nonneg hd.le 3),
      Real.mul_rpow (by positivity) hc.le,
      ←Real.rpow_natCast (3:ℝ) R.order,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
      ←Real.rpow_natCast (norm R.cubePart) 3,←Real.rpow_mul hd.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (R.order:ℝ)*(-σ) = -(R.order:ℝ)*σ by ring,
      show (3:ℝ)*(-σ) = -3*σ by ring]
  have ha : R.amplitude^2 * (norm n)^(-σ) =
      3^(8-2*((R.order/3:ℕ):ℝ)-(R.order:ℝ)*σ) *
      (norm R.squarefreePart)^(-(1+σ)) *
      (norm R.cubePart)^(-(2+3*σ)) := by
    have h3 : (3:ℝ)^(8-2*((R.order/3:ℕ):ℝ)) * 3^(-(R.order:ℝ)*σ) =
        3^(8-2*((R.order/3:ℕ):ℝ)-(R.order:ℝ)*σ) := by
      rw [←Real.rpow_add (by norm_num : (0:ℝ) < 3)]
      congr 1
      ring
    have hce : (norm R.squarefreePart)^(-σ) / norm R.squarefreePart =
        (norm R.squarefreePart)^(-(1+σ)) := by
      rw [div_eq_mul_inv,←Real.rpow_neg_one,←Real.rpow_add hc]
      congr 1
      ring
    have hde : (norm R.cubePart)^(-3*σ) / (norm R.cubePart)^2 =
        (norm R.cubePart)^(-(2+3*σ)) := by
      rw [div_eq_mul_inv,←Real.rpow_two,←Real.rpow_neg hd.le,←Real.rpow_add hd]
      congr 1
      ring
    rw [R.amplitude_sq,hpow]
    calc
      _ = (3^(8-2*((R.order/3:ℕ):ℝ))*3^(-(R.order:ℝ)*σ)) *
          ((norm R.squarefreePart)^(-σ)/norm R.squarefreePart) *
          ((norm R.cubePart)^(-3*σ)/(norm R.cubePart)^2) := by
        simp only [div_eq_mul_inv,mul_inv_rev]
        ring
      _ = _ := by rw [h3,hce,hde]
  rw [cubicThetaCoefficientMassTerm,cubicThetaArithmeticCoefficient_formula R,R.coefficient_norm]
  split_ifs <;> simp_all only [one_mul,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMass
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact six-unit multiplicity in the squared theta coefficients.
The order congruent to one has precisely the two real units. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicTheta_real_unit_sum (x : ℝ) :
    (∑ u : Eisensteinˣ, if (u:Eisenstein)=1 ∨ (u:Eisenstein)=-1 then x else 0)=2*x := by
  have hne : (1:Eisensteinˣ) ≠ -1 := by
    intro h
    have he := congrArg (fun u : Eisensteinˣ => (u:Eisenstein)) h
    norm_num at he
  have he (u : Eisensteinˣ) :
      ((u:Eisenstein)=1 ∨ (u:Eisenstein)=-1) ↔ (u=1 ∨ u=-1) := by
    constructor
    · exact Or.imp (fun h => Units.ext h) (fun h => Units.ext h)
    · rintro (rfl|rfl) <;> simp
  have hf (u : Eisensteinˣ) :
      (if u=1 ∨ u=-1 then x else 0) =
        (if u=1 then x else 0)+(if u=-1 then x else 0) := by
    by_cases h1 : u=1 <;> by_cases hm : u=-1 <;> simp_all
  simp_rw [he,hf]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true]
  ring

lemma cubicThetaRamifiedMass_unit_sum (σ : ℝ) (k : ℕ) :
    (∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k) =
      (if k%3=0 ∧ 3 ≤ k then 6 else if k%3=1 then 2 else 0) *
        3^(8-2*((k/3:ℕ):ℝ)-(k:ℝ)*σ) := by
  rw [tsum_fintype]
  have hcard : Fintype.card Eisensteinˣ = 6 := by
    rw [←Nat.card_eq_fintype_card,eisenstein_units_card]
  by_cases h0 : k%3=0 ∧ 3 ≤ k
  · simp only [cubicThetaRamifiedMass,ite_eq_left h0,one_mul,Finset.sum_const,
      Finset.card_univ,nsmul_eq_mul,hcard,Nat.cast_ofNat]
  · simp only [cubicThetaRamifiedMass,ite_eq_right h0]
    by_cases h1 : k%3=1
    · simp only [h1,true_and,ite_true, if_true]
      simpa only [ite_mul,one_mul,zero_mul] using
        cubicTheta_real_unit_sum (3^(8-2*((k/3:ℕ):ℝ)-(k:ℝ)*σ))
    · simp only [h1,false_and,ite_false, if_false,zero_mul,Finset.sum_const_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRamifiedMassSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ramified coefficient mass is an explicit geometric series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaRamifiedRatio_pos (σ : ℝ) : 0 < cubicThetaRamifiedRatio σ := by
  exact Real.rpow_pos_of_pos (by norm_num) _

lemma cubicThetaRamifiedRatio_lt_one {σ : ℝ} (hσ : 0 < σ) :
    cubicThetaRamifiedRatio σ < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

lemma cubicThetaRamifiedMass_power (σ : ℝ) (k : ℕ) (j : Fin 3) :
    (3:ℝ)^(8-2*(((k*3+j.val)/3:ℕ):ℝ)-((k*3+j.val:ℕ):ℝ)*σ) =
      3^(8-(j.val:ℝ)*σ) * cubicThetaRamifiedRatio σ^k := by
  have hd : (k*3+j.val)/3=k := by omega
  rw [hd,cubicThetaRamifiedRatio,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3),
    ←Real.rpow_add (by norm_num : (0:ℝ) < 3)]
  push_cast
  congr 1
  ring

lemma cubicThetaRamifiedMass_class_zero (σ : ℝ) (k : ℕ) :
    (∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u (k*3)) =
      6*3^(8:ℝ)*cubicThetaRamifiedRatio σ^k - (if k=0 then 6*3^(8:ℝ) else 0) := by
  rw [cubicThetaRamifiedMass_unit_sum]
  have hp := cubicThetaRamifiedMass_power σ k (0:Fin 3)
  simp only [Fin.val_zero,Nat.add_zero,Nat.cast_zero,zero_mul,sub_zero] at hp
  rw [hp]
  by_cases hk : k=0
  · subst k
    norm_num
  · have h3 : 3 ≤ k*3 := by omega
    simp only [Nat.mul_mod_left,h3,true_and,ite_true, if_true,ite_eq_right hk,sub_zero]
    ring

lemma cubicThetaRamifiedMass_class_one (σ : ℝ) (k : ℕ) :
    (∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u (k*3+1)) =
      2*3^(8-σ)*cubicThetaRamifiedRatio σ^k := by
  rw [cubicThetaRamifiedMass_unit_sum]
  have hp := cubicThetaRamifiedMass_power σ k (1:Fin 3)
  norm_num only [Fin.val_one,Nat.cast_one,one_mul] at hp
  rw [hp]
  have hm : (k*3+1)%3=1 := by omega
  simp only [hm,one_ne_zero,false_and,ite_false, if_false,ite_true, if_true]
  ring

lemma cubicThetaRamifiedMass_class_two (σ : ℝ) (k : ℕ) :
    (∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u (k*3+2)) = 0 := by
  rw [cubicThetaRamifiedMass_unit_sum]
  have hm : (k*3+2)%3=2 := by omega
  norm_num [hm]

lemma cubicThetaRamifiedMass_class_hasSum {σ : ℝ} (hσ : 0 < σ) (j : Fin 3) :
    HasSum (fun k : ℕ => ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u (k*3+j.val))
      (if j.val=0 then 6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1)
       else if j.val=1 then 2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹ else 0) := by
  have hg := hasSum_geometric_of_lt_one (cubicThetaRamifiedRatio_pos σ).le
    (cubicThetaRamifiedRatio_lt_one hσ)
  fin_cases j
  · norm_num only [Nat.reduceEqDiff,ite_true,ite_false,Nat.add_zero]
    convert (hg.mul_left (6*3^(8:ℝ))).sub (hasSum_ite_eq (0:ℕ) (6*3^(8:ℝ))) using 1
    all_goals first | rfl | (ext k; exact cubicThetaRamifiedMass_class_zero σ k) | ring
  · norm_num only [Nat.reduceEqDiff,ite_true,ite_false]
    simpa only [cubicThetaRamifiedMass_class_one] using hg.mul_left (2*3^(8-σ))
  · norm_num only [Nat.reduceEqDiff,ite_true,ite_false]
    simp only [cubicThetaRamifiedMass_class_two]
    exact hasSum_zero

lemma cubicThetaRamifiedMass_nonneg (σ : ℝ) (u : Eisensteinˣ) (k : ℕ) :
    0 ≤ cubicThetaRamifiedMass σ u k := by
  unfold cubicThetaRamifiedMass
  split_ifs <;> positivity

lemma cubicThetaRamifiedMass_sum_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun k : ℕ => ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k) := by
  let e := (Nat.divModEquiv 3).trans (Equiv.prodComm ℕ (Fin 3))
  apply (e.symm.summable_iff).mp
  apply (summable_prod_of_nonneg (fun p => tsum_nonneg
    (fun u => cubicThetaRamifiedMass_nonneg σ u _))).2
  constructor
  · intro j
    exact (cubicThetaRamifiedMass_class_hasSum hσ j).summable
  · exact Summable.of_finite

lemma cubicThetaRamifiedMass_sum {σ : ℝ} (hσ : 0 < σ) :
    (∑' k : ℕ, ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k) =
      6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1) +
      2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹ := by
  let e := (Nat.divModEquiv 3).trans (Equiv.prodComm ℕ (Fin 3))
  rw [←e.symm.tsum_eq (fun k => ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k)]
  have he := ((e.symm.summable_iff).mpr (cubicThetaRamifiedMass_sum_summable hσ)).tsum_prod
  dsimp only [Function.comp_def] at he
  rw [he]
  change (∑' j : Fin 3, ∑' k : ℕ, ∑' u : Eisensteinˣ,
    cubicThetaRamifiedMass σ u (k*3+j.val)) = _
  simp_rw [(cubicThetaRamifiedMass_class_hasSum hσ _).tsum_eq]
  rw [tsum_fintype]
  simp [Fin.sum_univ_succ]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassFactorization
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and factorization of the literal coefficient mass.
The unramified factors retain the primary and squarefree restrictions. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryMass_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun d : PrimaryArgument => (norm d.val)^(-t)) :=
  (summable_eisenstein_norm_rpow ht).subtype _

lemma cubicThetaSquarefreeMass_summable {t : ℝ} (ht : 1 < t) :
    Summable (fun c : CubicThetaSquarefreePrimary => (norm c.val)^(-t)) :=
  (summable_eisenstein_norm_rpow ht).subtype _

lemma cubicThetaPairMassTerm_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (cubicThetaPairMassTerm σ) := by
  have hc := cubicThetaSquarefreeMass_summable (show 1 < 1+σ by linarith)
  have hd := cubicThetaPrimaryMass_summable (show 1 < 2+3*σ by linarith)
  have hp := summable_mul_of_summable_norm hc.norm hd.norm
  have he := hp.comp_injective cubicThetaMassPairEquiv.injective
  exact he.congr (fun _ => rfl)

lemma cubicThetaPairMassTerm_sum {σ : ℝ} (hσ : 0 < σ) :
    (∑' cd, cubicThetaPairMassTerm σ cd) =
      cubicThetaSquarefreeMass (1+σ) * cubicThetaPrimaryMass (2+3*σ) := by
  have hc := cubicThetaSquarefreeMass_summable (show 1 < 1+σ by linarith)
  have hd := cubicThetaPrimaryMass_summable (show 1 < 2+3*σ by linarith)
  rw [←cubicThetaMassPairEquiv.symm.tsum_eq (cubicThetaPairMassTerm σ)]
  change (∑' cd : CubicThetaSquarefreePrimary × PrimaryArgument,
    (norm cd.1.val)^(-(1+σ)) * (norm cd.2.val)^(-(2+3*σ))) = _
  exact (tsum_mul_tsum_of_summable_norm hc.norm hd.norm).symm

lemma cubicThetaRamifiedMass_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun p : Eisensteinˣ × ℕ => cubicThetaRamifiedMass σ p.1 p.2) := by
  have : Finite Eisensteinˣ := Nat.finite_of_card_ne_zero (by rw [eisenstein_units_card]; norm_num)
  have h : Summable (fun p : ℕ × Eisensteinˣ => cubicThetaRamifiedMass σ p.2 p.1) := by
    apply (summable_prod_of_nonneg (fun p => cubicThetaRamifiedMass_nonneg σ _ _)).2
    exact ⟨fun _ => Summable.of_finite,cubicThetaRamifiedMass_sum_summable hσ⟩
  exact h.prod_symm

lemma cubicThetaRamifiedMass_total {σ : ℝ} (hσ : 0 < σ) :
    (∑' p : Eisensteinˣ × ℕ, cubicThetaRamifiedMass σ p.1 p.2) =
      6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1) +
      2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹ := by
  have h := cubicThetaRamifiedMass_summable hσ
  have hc : Summable (Function.uncurry
      (fun u : Eisensteinˣ => fun k : ℕ => cubicThetaRamifiedMass σ u k)) := h
  calc
    _ = ∑' u : Eisensteinˣ, ∑' k : ℕ, cubicThetaRamifiedMass σ u k := h.tsum_prod
    _ = ∑' k : ℕ, ∑' u : Eisensteinˣ, cubicThetaRamifiedMass σ u k := hc.tsum_comm.symm
    _ = _ := cubicThetaRamifiedMass_sum hσ

lemma cubicThetaCoefficientMassTerm_common (σ : ℝ) (x : CubicThetaCommonIndex) :
    cubicThetaCoefficientMassTerm σ (cubicThetaCommonNumerator x) =
      cubicThetaRamifiedMass σ x.1 x.2.1 * cubicThetaPairMassTerm σ x.2.2 := by
  rw [(cubicThetaCommonCoordinates x).mass_term σ]
  simp only [cubicThetaCommonCoordinates,cubicThetaRamifiedMass,cubicThetaPairMassTerm]
  split_ifs <;> simp_all [mul_assoc]

lemma cubicThetaCoefficientMass_common_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (fun x : CubicThetaCommonIndex =>
      cubicThetaCoefficientMassTerm σ (cubicThetaCommonNumerator x)) := by
  have hr := cubicThetaRamifiedMass_summable hσ
  have hp := cubicThetaPairMassTerm_summable hσ
  have h := summable_mul_of_summable_norm hr.norm hp.norm
  have he := h.comp_injective (Equiv.prodAssoc Eisensteinˣ ℕ CubicThetaPrimaryPair).symm.injective
  simp only [Function.comp_def,Equiv.prodAssoc_symm_apply] at he
  simpa only [cubicThetaCoefficientMassTerm_common] using he

lemma cubicThetaCoefficientMassTerm_summable {σ : ℝ} (hσ : 0 < σ) :
    Summable (cubicThetaCoefficientMassTerm σ) := by
  apply (cubicThetaCommonNumerator_injective.summable_iff (f := cubicThetaCoefficientMassTerm σ) ?_).mp
    (cubicThetaCoefficientMass_common_summable hσ)
  intro n hn
  have hnone : ¬Nonempty (CubicThetaCoordinates n) := fun h =>
    hn ((cubicThetaCommonNumerator_range n).mpr h)
  simp [cubicThetaCoefficientMassTerm,cubicThetaArithmeticCoefficient,hnone]


theorem cubicThetaCoefficientMass_factorization {σ : ℝ} (hσ : 0 < σ) :
    cubicThetaCoefficientMass σ =
      (6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1) +
       2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹) *
      cubicThetaSquarefreeMass (1+σ) * cubicThetaPrimaryMass (2+3*σ) := by
  rw [cubicThetaCoefficientMass_reindex]
  simp_rw [cubicThetaCoefficientMassTerm_common]
  rw [←(Equiv.prodAssoc Eisensteinˣ ℕ CubicThetaPrimaryPair).tsum_eq
    (fun x : CubicThetaCommonIndex =>
      cubicThetaRamifiedMass σ x.1 x.2.1 * cubicThetaPairMassTerm σ x.2.2)]
  change (∑' x : (Eisensteinˣ × ℕ) × CubicThetaPrimaryPair,
    cubicThetaRamifiedMass σ x.1.1 x.1.2 * cubicThetaPairMassTerm σ x.2) = _
  rw [←tsum_mul_tsum_of_summable_norm (cubicThetaRamifiedMass_summable hσ).norm
    (cubicThetaPairMassTerm_summable hσ).norm,
    cubicThetaRamifiedMass_total hσ,cubicThetaPairMassTerm_sum hσ]
  exact (mul_assoc _ _ _).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticEulerFactor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The completed cubic Gauss series uses an actual primary coprimality
Euler factor. It is identified with a complete principal ideal series and
is nonzero throughout the half-plane needed for decompletion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_ideal_tsum (f : Eisenstein → ℂ) :
    (∑' ν : EisensteinIdealExponent, if primary (idealPrimaryGenerator ν) then
      f (idealPrimaryGenerator ν) else 0) = ∑' u : PrimaryArgument, f u := by
  let g (ν : EisensteinIdealExponent) : ℂ :=
    if primary (idealPrimaryGenerator ν) then f (idealPrimaryGenerator ν) else 0
  have hi : Function.Injective (fun u : PrimaryArgument => idealExponentOf u.val) := by
    intro a b h
    exact Subtype.ext (idealExponentOf_inj_primary a.property b.property h)
  have hs : Function.support g ⊆ Set.range (fun u : PrimaryArgument => idealExponentOf u.val) := by
    intro ν hν
    have hp : primary (idealPrimaryGenerator ν) := by
      by_contra hn
      exact hν (by simp [g,hn])
    exact ⟨⟨idealPrimaryGenerator ν,hp⟩,idealExponentOf_primaryGenerator ν⟩
  rw [←hi.tsum_eq hs]
  apply tsum_congr
  intro u
  simp [g,idealPrimaryGenerator_at_element u.property,u.property]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaPrimaryMassEuler
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The primary norm series omits exactly the single ideal above three. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaPrimaryGenerator_iff_unramified (ν : EisensteinIdealExponent) :
    primary (idealPrimaryGenerator ν) ↔ ν cubicThetaRamifiedPrime=0 := by
  constructor
  · intro hp
    apply Nat.eq_zero_of_not_pos
    intro hν
    have hd := (cubicThetaRamifiedPrime_dvd_iff ν).mpr hν
    have hd' : lambdaE ∣ idealPrimaryGenerator ν :=
      hd.trans (primaryNormalize_associated (idealExponentGenerator ν)).dvd
    exact lambdaE_prime.not_isUnit ((primary_coprime_lambda hp).isRelPrime hd' dvd_rfl)
  · intro hν
    exact cubicThetaPrimaryGenerator_primary ⟨ν,hν⟩

lemma cubicThetaPrimaryMass_ideal (t : ℝ) :
    (cubicThetaPrimaryMass t:ℂ)=normDirichletSeries
      (primeIdealRestriction {cubicThetaRamifiedPrime} (fun _ => 1)) idealExponentNorm (t:ℂ) := by
  have h := primary_ideal_tsum (fun a => ((norm a)^(-t):ℝ))
  change (∑' ν, if primary (idealPrimaryGenerator ν) then
    (((norm (idealPrimaryGenerator ν))^(-t):ℝ):ℂ) else 0)=_ at h
  unfold cubicThetaPrimaryMass
  rw [Complex.ofReal_tsum,←h]
  unfold normDirichletSeries
  apply tsum_congr
  intro ν
  rw [cubicThetaPrimaryGenerator_iff_unramified,idealPrimaryGenerator_norm]
  simp only [primeIdealRestriction,Finset.mem_singleton,forall_eq]
  split_ifs
  · rw [one_mul]
    simpa only [Complex.ofReal_neg] using Complex.ofReal_cpow (idealExponentNorm_pos ν).le (-t)
  · rw [zero_mul]

theorem cubicThetaPrimaryMass_euler {t : ℝ} (ht : 1 < t) :
    (cubicThetaPrimaryMass t:ℂ)=(1-(3:ℂ)^(-(t:ℂ)))*principalIdealZeta (t:ℂ) := by
  rw [cubicThetaPrimaryMass_ideal,idealDirichlet_single_exclusion _ _ (by simp)
    (by intros; simp) (by simpa using ht),←principalIdealZeta_right (by simpa using ht)]
  simp only [idealExponentNorm_single,pow_one,cubicThetaRamifiedPrime_norm,Nat.cast_ofNat,
    one_mul,Complex.ofReal_ofNat]

lemma cubicThetaPrimaryMass_pos {t : ℝ} (ht : 1 < t) : 0 < cubicThetaPrimaryMass t := by
  have h := (cubicThetaPrimaryMass_summable ht).le_tsum
    (⟨1,by norm_num [primary]⟩:PrimaryArgument)
    (fun d _ => Real.rpow_nonneg (norm_nonneg d.val) _)
  have he : (norm (1:Eisenstein))^(-t)=1 := by rw [norm_one_eq,Real.one_rpow]
  exact lt_of_lt_of_le (he ▸ zero_lt_one) h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaSquarefreeMassEuler
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The squarefree norm series is the quotient by the square factor.
Every primary element occurs exactly once. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaSquareNumerator_weight (t : ℝ) (cd : CubicThetaPrimaryPair) :
    (norm (cubicThetaSquareNumerator cd))^(-t) =
      (norm cd.val.1)^(-t) * (norm cd.val.2)^(-(2*t)) := by
  rw [cubicThetaSquareNumerator,norm_mul_eq,eisenstein_norm_pow,
    Real.mul_rpow (norm_nonneg _) (sq_nonneg _),←Real.rpow_natCast,
    ←Real.rpow_mul (norm_nonneg _)]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*(-t)=-(2*t) by ring]

theorem cubicThetaSquarefreeMass_mul {t : ℝ} (ht : 1 < t) :
    cubicThetaSquarefreeMass t * cubicThetaPrimaryMass (2*t)=cubicThetaPrimaryMass t := by
  have hc := cubicThetaSquarefreeMass_summable ht
  have hd := cubicThetaPrimaryMass_summable (show 1 < 2*t by linarith)
  symm
  calc
    cubicThetaPrimaryMass t = ∑' cd : CubicThetaPrimaryPair,
        (norm (cubicThetaSquareNumerator cd))^(-t) :=
      (cubicThetaSquareIndexEquiv.tsum_eq (fun d : PrimaryArgument => (norm d.val)^(-t))).symm
    _ = ∑' cd : CubicThetaPrimaryPair, (norm cd.val.1)^(-t) *
        (norm cd.val.2)^(-(2*t)) := tsum_congr (cubicThetaSquareNumerator_weight t)
    _ = ∑' cd : CubicThetaSquarefreePrimary × PrimaryArgument,
        (norm cd.1.val)^(-t) * (norm cd.2.val)^(-(2*t)) :=
      (cubicThetaMassPairEquiv.symm.tsum_eq _).symm
    _ = _ := (tsum_mul_tsum_of_summable_norm hc.norm hd.norm).symm

lemma cubicThetaSquarefreeMass_quotient {t : ℝ} (ht : 1 < t) :
    cubicThetaSquarefreeMass t=cubicThetaPrimaryMass t/cubicThetaPrimaryMass (2*t) := by
  apply (eq_div_iff (cubicThetaPrimaryMass_pos (by linarith : 1 < 2*t)).ne').mpr
  exact cubicThetaSquarefreeMass_mul ht

theorem cubicThetaCoefficientMass_primary_quotient {σ : ℝ} (hσ : 0 < σ) :
    cubicThetaCoefficientMass σ =
      (6*3^(8:ℝ)*((1-cubicThetaRamifiedRatio σ)⁻¹-1) +
       2*3^(8-σ)*(1-cubicThetaRamifiedRatio σ)⁻¹) *
      (cubicThetaPrimaryMass (1+σ)/cubicThetaPrimaryMass (2+2*σ)) *
      cubicThetaPrimaryMass (2+3*σ) := by
  rw [cubicThetaCoefficientMass_factorization hσ,
    cubicThetaSquarefreeMass_quotient (by linarith : 1 < 1+σ)]
  rw [show 2*(1+σ)=2+2*σ by ring]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassEuler
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit zeta expression for the squared arithmetic theta coefficients. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaThree_rpow_complex (t : ℝ) :
    (((3:ℝ)^t:ℝ):ℂ)=(3:ℂ)^(t:ℂ) :=
  Complex.ofReal_cpow (by norm_num) t

theorem cubicThetaCoefficientMass_euler {σ : ℝ} (hσ : 0 < σ) :
    (cubicThetaCoefficientMass σ:ℂ)=cubicThetaMassEulerPrefactor (σ:ℂ)*
      principalIdealZeta (1+(σ:ℂ))*principalIdealZeta (2+3*(σ:ℂ))/
      principalIdealZeta (2+2*(σ:ℂ)) := by
  rw [cubicThetaCoefficientMass_primary_quotient hσ]
  simp only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_sub,Complex.ofReal_inv,
    Complex.ofReal_div,cubicThetaRamifiedRatio,cubicThetaThree_rpow_complex,
    Complex.ofReal_ofNat,Complex.ofReal_one]
  rw [cubicThetaPrimaryMass_euler (by linarith : 1 < 1+σ),
    cubicThetaPrimaryMass_euler (by linarith : 1 < 2+2*σ),
    cubicThetaPrimaryMass_euler (by linarith : 1 < 2+3*σ)]
  push_cast
  unfold cubicThetaMassEulerPrefactor
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma cubicThetaMassEulerPrefactor_zero : cubicThetaMassEulerPrefactor 0=2*3^(8:ℂ) := by
  norm_num [cubicThetaMassEulerPrefactor,Complex.cpow_neg,Complex.cpow_ofNat]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaMassResidue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact residue of the arithmetic coefficient-energy Dirichlet series.
This is an arithmetic calculation, before comparison with the global norm. -/
noncomputable section
open Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaMassEulerPrefactor_analyticAt_zero :
    AnalyticAt ℂ cubicThetaMassEulerPrefactor 0 := by
  let _ : NeZero (3:ℂ) := ⟨by norm_num⟩
  have hp (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
      AnalyticAt ℂ (fun s => (3:ℂ)^(f s)) 0 :=
    ((differentiable_const_cpow_of_neZero (3:ℂ)).analyticAt _).comp hf
  have hq := hp (fun s => -2-3*s) (by fun_prop)
  have h1 := hp (fun s => -(1+s)) (by fun_prop)
  have h2 := hp (fun s => -(2+3*s)) (by fun_prop)
  have h3 := hp (fun s => -(2+2*s)) (by fun_prop)
  have h8 := hp (fun s => 8-s) (by fun_prop)
  have hn : 1-(3:ℂ)^(-2-3*(0:ℂ))≠0 := by norm_num [Complex.cpow_neg,Complex.cpow_ofNat]
  have hd : 1-(3:ℂ)^(-(2+2*(0:ℂ)))≠0 := by norm_num [Complex.cpow_neg,Complex.cpow_ofNat]
  have hi := (analyticAt_const.sub hq).inv hn
  unfold cubicThetaMassEulerPrefactor
  exact ((((analyticAt_const.mul (hi.sub analyticAt_const)).add
    ((analyticAt_const.mul h8).mul hi)).mul (analyticAt_const.sub h1)).mul
      (analyticAt_const.sub h2)).div (analyticAt_const.sub h3) hd

lemma cubicThetaMassRegular_analyticAt_zero : AnalyticAt ℂ cubicThetaMassRegular 0 := by
  have hr : AnalyticAt ℂ (fun s : ℂ => principalZetaRegularFactor (1+s)) 0 := by
    have ho : AnalyticAt ℂ principalZetaRegularFactor (1+(0:ℂ)) := by
      simpa only [add_zero] using principalZetaRegularFactor_analyticAt_one
    exact ho.comp (f := fun s : ℂ => 1+s) (x := 0) (by fun_prop)
  have hz (a : ℂ) : AnalyticAt ℂ (fun s : ℂ => principalIdealZeta (2+a*s)) 0 := by
    have ho : AnalyticAt ℂ principalIdealZeta (2+a*(0:ℂ)) := by
      simpa only [mul_zero,add_zero] using
        (cubicTheta_principalZeta_analyticAt (s:=2) (by norm_num) (by norm_num))
    exact ho.comp (f := fun s : ℂ => 2+a*s) (x := 0) (by fun_prop)
  exact ((cubicThetaMassEulerPrefactor_analyticAt_zero.mul hr).mul (hz 3)).div (hz 2)
    (by simpa using cubicTheta_principalZeta_two_ne_zero)

lemma cubicThetaMassRegular_zero :
    cubicThetaMassRegular 0=(2*3^(8:ℂ))*(principalThetaConstant/(residueHeckeScale 1:ℂ)) := by
  rw [cubicThetaMassRegular,cubicThetaMassEulerPrefactor_zero]
  simp only [mul_zero,add_zero,principalZetaRegularFactor_one]
  exact mul_div_cancel_right₀ _ cubicTheta_principalZeta_two_ne_zero

lemma cubicThetaMassRegular_real {σ : ℝ} (hσ : 0 < σ) :
    cubicThetaMassRegular (σ:ℂ)=(σ:ℂ)*(cubicThetaCoefficientMass σ:ℂ) := by
  have hs0 : (1+(σ:ℂ))≠0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.zero_re] at hr
    linarith
  have hs1 : (1+(σ:ℂ))≠1 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re] at hr
    linarith
  rw [cubicThetaMassRegular,principalZetaRegularFactor_eq hs0 hs1,
    cubicThetaCoefficientMass_euler hσ]
  ring

theorem cubicThetaCoefficientMass_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*(cubicThetaCoefficientMass σ:ℂ)) (𝓝[>] 0)
      (𝓝 ((2*3^(8:ℂ))*(principalThetaConstant/(residueHeckeScale 1:ℂ)))) := by
  have h := cubicThetaMassRegular_analyticAt_zero.continuousAt.tendsto.comp
    (Complex.continuous_ofReal.tendsto (0:ℝ))
  rw [cubicThetaMassRegular_zero] at h
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact cubicThetaMassRegular_real hσ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyMellin
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Fubini for the actual horizontal Fourier energy and its
coefficient Dirichlet mass. The frequency dilation is retained exactly. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment

lemma cubicThetaEnergyMellinTerm_nonneg (σ : ℝ) (n : Eisenstein) {v : ℝ}
    (hv : 0 < v) : 0 ≤ cubicThetaEnergyMellinTerm σ n v :=
  mul_nonneg (Real.rpow_nonneg hv.le _) (sq_nonneg _)

lemma cubicThetaEnergyMellinTerm_integrable {σ : ℝ} (hσ : 0 ≤ σ) (n : Eisenstein) :
    IntegrableOn (cubicThetaEnergyMellinTerm σ n) (Ioi 0) := by
  by_cases hn : n=0
  · subst n
    have hz : IntegrableOn (fun _ : ℝ => (0:ℝ)) (Ioi 0) (volume : Measure ℝ) := integrableOn_zero
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    ext v
    simp [cubicThetaEnergyMellinTerm,cubicThetaSeriesTerm]
  · have hi := (cubicWhittakerEnergy_scaled_integrable hσ (cubicThetaFrequency_pos hn)).const_mul
      (‖cubicThetaArithmeticCoefficient n‖^2)
    apply hi.congr
    filter_upwards with v
    simp only [cubicThetaEnergyMellinTerm,cubicThetaSeriesTerm,ite_eq_right hn,
      norm_mul,Circle.norm_coe,mul_one,mul_pow]
    ring

lemma cubicThetaEnergyMellinTerm_integral (σ : ℝ) (n : Eisenstein) :
    (∫ v in Ioi (0:ℝ), cubicThetaEnergyMellinTerm σ n v)=
      (81^σ*cubicWhittakerEnergyMass σ)*cubicThetaCoefficientMassTerm σ n := by
  by_cases hn : n=0
  · subst n
    have hz : ¬Nonempty (CubicThetaCoordinates (0:Eisenstein)) := by
      rintro ⟨R⟩
      exact R.ne_zero rfl
    simp [cubicThetaEnergyMellinTerm,cubicThetaSeriesTerm,
      cubicThetaCoefficientMassTerm,cubicThetaArithmeticCoefficient,hz]
  · calc
      _ = ‖cubicThetaArithmeticCoefficient n‖^2 *
          (∫ v in Ioi (0:ℝ), v^(2*σ-1)*‖cubicThetaWhittaker (‖cubicThetaFrequency n‖*v)‖^2) := by
        rw [←integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro v _
        simp only [cubicThetaEnergyMellinTerm,cubicThetaSeriesTerm,ite_eq_right hn,
          norm_mul,Circle.norm_coe,mul_one,mul_pow]
        ring
      _ = _ := by
        rw [cubicWhittakerEnergy_mass_scale σ (cubicThetaFrequency_pos hn),cubicThetaFrequency_rpow hn]
        rw [show -(-2*σ)/2=σ by ring,show (-2*σ)/2= -σ by ring]
        unfold cubicThetaCoefficientMassTerm
        ring

lemma cubicThetaEnergyMellinTerm_norm_integral (σ : ℝ) (n : Eisenstein) :
    (∫ v in Ioi (0:ℝ), ‖cubicThetaEnergyMellinTerm σ n v‖)=
      (81^σ*cubicWhittakerEnergyMass σ)*cubicThetaCoefficientMassTerm σ n := by
  rw [←cubicThetaEnergyMellinTerm_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact Real.norm_of_nonneg (cubicThetaEnergyMellinTerm_nonneg σ n hv)

lemma cubicThetaArithmeticFourierEnergy_all (v : ℝ) :
    cubicThetaArithmeticFourierEnergy v=
      ∑' n : Eisenstein, ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖^2 := by
  let f (n : Eisenstein) : ℝ := ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖^2
  have hs : Function.support f ⊆ Set.range (fun h : Eisenstein => -lambdaE*h) := by
    intro n hn
    apply cubicThetaSeriesTerm_row_support 0 v
    intro hz
    exact hn (by simp only [f,hz,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)])
  have he := cubicThetaRowIndex_injective.tsum_eq hs
  simpa only [f,←cubicThetaArithmeticRowTerm_eq,cubicThetaArithmeticFourierEnergy] using he

local instance localInst_r8af80d_1 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
theorem cubicThetaArithmeticFourierEnergy_mellin {σ : ℝ} (hσ : 0 < σ) :
    (∫ v in Ioi (0:ℝ), v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v)=
      81^σ*cubicWhittakerEnergyMass σ*cubicThetaCoefficientMass σ := by
  have hi := fun n => cubicThetaEnergyMellinTerm_integrable hσ.le n
  have hs : Summable (fun n : Eisenstein =>
      ∫ v in Ioi (0:ℝ), ‖cubicThetaEnergyMellinTerm σ n v‖) := by
    simpa only [cubicThetaEnergyMellinTerm_norm_integral] using
      (cubicThetaCoefficientMassTerm_summable hσ).mul_left (81^σ*cubicWhittakerEnergyMass σ)
  calc
    _ = ∫ v in Ioi (0:ℝ), ∑' n : Eisenstein, cubicThetaEnergyMellinTerm σ n v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v _
      dsimp only
      rw [cubicThetaArithmeticFourierEnergy_all,←tsum_mul_left]
      rfl
    _ = ∑' n : Eisenstein, ∫ v in Ioi (0:ℝ), cubicThetaEnergyMellinTerm σ n v :=
      (integral_tsum_of_summable_integral_norm hi hs).symm
    _ = _ := by
      simp_rw [cubicThetaEnergyMellinTerm_integral]
      rw [tsum_mul_left]
      rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyResidue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The Mellin pole of the actual nonconstant horizontal energy, retaining
the squared Whittaker mass that will enter the geometric norm comparison. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CubicFirstMoment

theorem cubicThetaArithmeticFourierEnergy_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*
      ((∫ v in Ioi (0:ℝ), v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v:ℝ):ℂ))
      (𝓝[>] 0) (𝓝 ((cubicWhittakerEnergyMass 0:ℂ)*
        ((2*3^(8:ℂ))*(principalThetaConstant/(residueHeckeScale 1:ℂ))))) := by
  have hp : Tendsto (fun σ : ℝ => (81:ℝ)^σ) (𝓝[>] 0) (𝓝 1) := by
    have h := (Real.continuousAt_const_rpow (by norm_num : (81:ℝ)≠0) (b:=0)).tendsto
    simpa only [Real.rpow_zero] using h.mono_left nhdsWithin_le_nhds
  have he : Tendsto (fun σ : ℝ => ((81^σ*cubicWhittakerEnergyMass σ:ℝ):ℂ))
      (𝓝[>] 0) (𝓝 (cubicWhittakerEnergyMass 0:ℂ)) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (hp.mul cubicWhittakerEnergyMass_tendsto_zero)
    simpa only [one_mul,Function.comp_def] using h
  apply (he.mul cubicThetaCoefficientMass_residue).congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [cubicThetaArithmeticFourierEnergy_mellin hσ,Complex.ofReal_mul,Complex.ofReal_mul]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaEnergyPoleValue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Numerical evaluation of the arithmetic horizontal-energy pole. -/
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicWhittakerEnergy_gamma_product :
    Real.Gamma (4/3)*Real.Gamma (2/3)=2*Real.pi/(3*Real.sqrt 3) := by
  have hr := Real.Gamma_mul_Gamma_one_sub (1/3)
  rw [show (1:ℝ)-1/3=2/3 by norm_num,
    show Real.pi*(1/3)=Real.pi/3 by ring,Real.sin_pi_div_three] at hr
  rw [show (4/3:ℝ)=1/3+1 by norm_num,Real.Gamma_add_one (by norm_num : (1/3:ℝ)≠0),
    mul_assoc,hr]
  ring

lemma cubicWhittakerEnergyMass_zero_explicit :
    cubicWhittakerEnergyMass 0=1/(48*Real.pi*Real.sqrt 3) := by
  rw [cubicWhittakerEnergyMass_zero,cubicWhittakerEnergy_gamma_product]
  field_simp
  ring

lemma cubicThetaArithmeticEnergyResidue_value :
    (cubicWhittakerEnergyMass 0:ℂ)*
      ((2*3^(8:ℂ))*(principalThetaConstant/(residueHeckeScale 1:ℂ)))=243/8 := by
  have hr : cubicWhittakerEnergyMass 0 *
      ((2*(3:ℝ)^8)*(Real.pi/(3*Real.sqrt 3)))=243/8 := by
    rw [cubicWhittakerEnergyMass_zero_explicit]
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    field_simp
    nlinarith
  rw [cubicTheta_principalZeta_residue_value]
  norm_num only [Complex.cpow_ofNat]
  norm_num at hr
  have hc := congrArg Complex.ofReal hr
  push_cast at hc
  exact hc

theorem cubicThetaArithmeticFourierEnergy_residue_explicit :
    Tendsto (fun σ : ℝ => (σ:ℂ)*
      ((∫ v in Ioi (0:ℝ), v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v:ℝ):ℂ))
      (𝓝[>] 0) (𝓝 (243/8)) := by
  simpa only [cubicThetaArithmeticEnergyResidue_value] using
    cubicThetaArithmeticFourierEnergy_residue

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierEnergyIntegrable
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute integrability of the actual Fourier-energy Mellin transform. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaArithmeticFourierEnergy_nonneg (v : ℝ) :
    0 ≤ cubicThetaArithmeticFourierEnergy v := tsum_nonneg (fun _ => sq_nonneg _)

local instance localInst_r8af80d_2 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
theorem cubicThetaArithmeticFourierEnergy_mellin_integrable {σ : ℝ} (hσ : 0<σ) :
    IntegrableOn (fun v : ℝ => v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v) (Ioi 0) := by
  let F := cubicThetaEnergyMellinTerm σ
  have hi (n : Eisenstein) : IntegrableOn (F n) (Ioi 0) :=
    cubicThetaEnergyMellinTerm_integrable hσ.le n
  have hs : Summable (fun n : Eisenstein => ∫ v in Ioi (0:ℝ),‖F n v‖) := by
    simpa only [F,cubicThetaEnergyMellinTerm_norm_integral] using
      (cubicThetaCoefficientMassTerm_summable hσ).mul_left (81^σ*cubicWhittakerEnergyMass σ)
  have hm : AEMeasurable (fun v => ∑' n : Eisenstein,F n v) (volume.restrict (Ioi 0)) :=
    AEMeasurable.tsum (fun n => (hi n).aestronglyMeasurable.aemeasurable)
  have hsum : IntegrableOn (fun v => ∑' n : Eisenstein,F n v) (Ioi 0) := by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    change (∫⁻ v,‖∑' n : Eisenstein,F n v‖ₑ ∂volume.restrict (Ioi 0)) < ⊤
    have he : (fun v => ‖∑' n : Eisenstein,F n v‖ₑ)=ᵐ[volume.restrict (Ioi 0)]
        (fun v => ∑' n : Eisenstein,‖F n v‖ₑ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
      have hn (n : Eisenstein) : 0≤F n v := cubicThetaEnergyMellinTerm_nonneg σ n hv
      have hbase := (cubicThetaArithmetic_summable hv 0).norm
      have hprod := summable_mul_of_summable_norm hbase.norm hbase.norm
      have hsq : Summable (fun n : Eisenstein =>
          ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖^2) := by
        have hd := hprod.comp_injective (show Function.Injective (fun n : Eisenstein => (n,n))
          from fun _ _ h => congrArg Prod.fst h)
        change Summable (fun n : Eisenstein =>
          ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖*
            ‖cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n‖) at hd
        simpa only [pow_two] using hd
      have hsn : Summable (fun n : Eisenstein => F n v) := hsq.mul_left _

      rw [Real.enorm_of_nonneg (tsum_nonneg hn),ENNReal.ofReal_tsum_of_nonneg hn hsn]
      apply tsum_congr
      intro n
      exact (Real.enorm_of_nonneg (hn n)).symm
    rw [lintegral_congr_ae he,lintegral_tsum (fun n => (hi n).aestronglyMeasurable.enorm)]
    simp_rw [←ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg (fun _ => _root_.norm_nonneg _)) hs]
    exact ENNReal.ofReal_lt_top
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _hv
  dsimp only [F,cubicThetaEnergyMellinTerm]
  rw [cubicThetaArithmeticFourierEnergy_all,tsum_mul_left]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFourierEnergyLowPole
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutting the arithmetic energy Mellin integral at height one preserves its pole. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaFourierEnergyHighMass_tendsto :
    Tendsto cubicThetaFourierEnergyHighMass (𝓝[>] 0)
      (𝓝 (cubicThetaFourierEnergyHighMass 0)) := by
  have hmajor := (cubicThetaArithmeticFourierEnergy_mellin_integrable (σ:=1) (by norm_num)).mono_set
    (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  apply tendsto_integral_filter_of_dominated_convergence
    (fun v : ℝ => v^(2*(1:ℝ)-1)*cubicThetaArithmeticFourierEnergy v) ?_ ?_ hmajor ?_
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact ((cubicThetaArithmeticFourierEnergy_mellin_integrable hσ).mono_set
      (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))).aestronglyMeasurable
  · have hs0 : ∀ᶠ σ : ℝ in 𝓝 0,σ<1 := Iio_mem_nhds (by norm_num : (0:ℝ)<1)
    have hs : ∀ᶠ σ : ℝ in 𝓝[>] 0,σ<1 := hs0.filter_mono nhdsWithin_le_nhds
    filter_upwards [hs] with σ hσ
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 1<v at hv
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (cubicThetaArithmeticFourierEnergy_nonneg v))]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hv.le (by linarith))
      (cubicThetaArithmeticFourierEnergy_nonneg v)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    change 1<v at hv
    have hc : ContinuousAt (fun σ : ℝ => v^(2*σ-1)) 0 :=
      (Real.continuousAt_const_rpow (by linarith : v≠0)).comp (by fun_prop)
    exact (hc.mul continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds

lemma cubicThetaFourierEnergyLowMass_eq {σ : ℝ} (hσ : 0<σ) :
    cubicThetaFourierEnergyLowMass σ=
      (∫ v in Ioi (0:ℝ),v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v)-
        cubicThetaFourierEnergyHighMass σ := by
  have hi := cubicThetaArithmeticFourierEnergy_mellin_integrable hσ
  have he : (∫ v in Ioi (0:ℝ),v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v)=
      cubicThetaFourierEnergyLowMass σ+cubicThetaFourierEnergyHighMass σ := by
    rw [←Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ)≤1),
      setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hi.mono_set Ioc_subset_Ioi_self)
        (hi.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1)))]
    rfl
  linarith

theorem cubicThetaFourierEnergyLowMass_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*(cubicThetaFourierEnergyLowMass σ:ℂ))
      (𝓝[>] 0) (𝓝 (243/8)) := by
  have hσ : Tendsto (fun σ : ℝ => (σ:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hH := (Complex.continuous_ofReal.tendsto _).comp cubicThetaFourierEnergyHighMass_tendsto
  have hz := hσ.mul hH
  simp only [zero_mul] at hz
  have h := cubicThetaArithmeticFourierEnergy_residue_explicit.sub hz
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  dsimp only [Function.comp_apply]
  rw [cubicThetaFourierEnergyLowMass_eq hσ]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaHorizontalEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized Fourier energy is the literal squared modulus integrated
over the physical level-three horizontal cell, with its exact area. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

attribute [local instance] OAI.CubicFirstMoment.cubicThetaHorizontalEnergyMeasureSpace
attribute [local instance] OAI.CubicFirstMoment.cubicThetaHorizontalEnergyProbability
lemma cubicThetaTorus_norm_square_integral (F : C(UnitAddTorus (Fin 2),ℂ)) :
    (∫ t, (‖F t‖^2:ℂ))=(‖ContinuousMap.toLp 2 volume ℂ F‖^2:ℂ) := by
  have hr : (∫ t,‖F t‖^2)=‖ContinuousMap.toLp 2 volume ℂ F‖^2 := by
    rw [cubicTheta_l2_norm_sq_measure]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) volume F] with t ht
    rw [ht]
  have hc := congrArg Complex.ofReal hr
  rw [←integral_complex_ofReal] at hc
  simpa only [Complex.ofReal_pow] using hc

lemma cubicThetaArithmeticModel_horizontal_energy (A : ℂ) {v : ℝ} (hv : 0<v) :
    (∫ z in cubicThetaHorizontalCell,(‖cubicThetaArithmeticModel A (z,v)‖^2:ℂ))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*
        (((cubicThetaConstant*v^(2/3:ℝ))^2:ℝ)+
          ‖A‖^2*cubicThetaArithmeticFourierEnergy v) := by
  let G : C(UnitAddTorus (Fin 2),ℂ) :=
    ⟨fun t => (‖cubicThetaArithmeticModelTorus A v t‖^2:ℂ),by fun_prop⟩
  have he := cubicThetaHorizontalCoefficient
    (fun z => (‖cubicThetaArithmeticModel A (z,v)‖^2:ℂ)) G 0
    (fun x => by change _=(‖cubicThetaArithmeticModelTorus A v _‖^2:ℂ)
                 rw [cubicThetaArithmeticModelTorus_real A hv])
  have hzero (z : ℂ) :
      (Real.fourierChar (tracePair z (cubicThetaRowFrequency 0)):ℂ)=1 := by
    simp [cubicThetaRowFrequency,tracePair]
  simp_rw [hzero,star_one,one_mul] at he
  rw [he,cubicThetaTorusCoefficient_integral]
  simp only [cubicThetaTorusFourier_zero,ContinuousMap.one_apply,star_one,one_mul]
  change _ • (∫ t,(‖cubicThetaArithmeticModelTorus A v t‖^2:ℂ))=_
  rw [cubicThetaTorus_norm_square_integral]
  rw [←Complex.ofReal_pow,cubicThetaArithmeticModelTorus_energy A hv]
  simp only [Complex.real_smul,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaModelGlobalL2
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The continuous arithmetic model is the actual global L2 residue,
not only its restriction to a cusp. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

theorem cubicThetaArithmeticModelGlobalL2 :
    cubicThetaArithmeticModelGlobal_memLp.toLp
        (cubicThetaSectionRepresentative cubicThetaArithmeticModelSection)=
      cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue := by
  apply Lp.ext
  exact cubicThetaArithmeticModelGlobal_memLp.coeFn_toLp.trans
    cubicThetaArithmeticModelRepresentative_ae

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaFullGaussianMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute Mellin interchange for the literal affine row heat kernel. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment
local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_2 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarRankinKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive truncated scalar kernel on the actual arithmetic quotient.
Its residue is known before any integration against the theta norm. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable
local instance instCountableSubtypeComplexMemSubalgebraIntEisenstein_3 : Countable Eisenstein := coordinatesEquiv.symm.injective.countable

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueMassPairing
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaComplexPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaComplexPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_openPositive _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual residue's global mass is fixed by its high-cusp constant
observation. This uses the weak eigenvalue equation, not a norm assumption. -/
noncomputable section
open scoped InnerProduct
namespace CubicFirstMoment

lemma cubicThetaResidue_energy_pairing (v : cubicThetaGlobalEnergySpace) :
    inner ℂ v (cubicThetaArithmeticResidueEnergy (4/3)) =
      (17/9:ℂ)*inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))) := by
  have hw := cubicThetaArithmeticResidueEnergy_weak (4/3) v
  rw [cubicThetaGlobalEnergy_inner]
  norm_num at hw
  linear_combination hw

lemma cubicThetaResidue_mass_pairing (v : cubicThetaGlobalEnergySpace)
    (hv : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ)) v=0) :
    inner ℂ (cubicThetaGlobalInclusion v)
        (cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))) =
      (3/2:ℂ)*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaHighWindowL2 (4/3)) := by
  have hp := cubicThetaResidue_kernel_pairing v hv
  rw [cubicThetaResidue_energy_pairing,cubicThetaKernel_window_balance v hv] at hp
  norm_num [cubicThetaGlobalSpectralParameter] at hp
  linear_combination (9/17:ℂ)*hp

lemma cubicThetaArithmeticResidue_mass_sq :
    (‖cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))‖^2:ℂ) =
      (3/2:ℂ)*star ((3*Real.pi:ℂ)*cubicThetaScatteringResidue*
        cubicThetaZeroRadialTest (cubicThetaHighWindowWeight (4/3)) (4/3)) := by
  have hk : cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter (4/3:ℂ))
      (cubicThetaArithmeticResidueEnergy (4/3))=0 := by
    convert cubicThetaArithmeticResidueEnergy_kernel (4/3) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
  have hp := cubicThetaResidue_mass_pairing (cubicThetaArithmeticResidueEnergy (4/3)) hk
  rw [inner_self_eq_norm_sq_to_K,←inner_conj_symm,cubicThetaHighWindowPairing_energy,
    cubicThetaResidue_zero_observation _
      (fun _ hv => cubicThetaHighWindowForcing_low (4/3) hv)] at hp
  exact hp

lemma cubicThetaNormalizedArithmeticResidue_mass_sq :
    (‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ) =
      (3/2:ℂ)*cubicThetaResidueScale*
        star (((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ)*
          cubicThetaZeroRadialTest (cubicThetaHighWindowWeight (4/3)) (4/3)) := by
  rw [cubicThetaNormalizedArithmeticResidue,map_smul,norm_smul]
  push_cast
  rw [mul_pow,cubicThetaArithmeticResidue_mass_sq]
  have hn : (‖cubicThetaResidueScale‖:ℂ)^2=
      star cubicThetaResidueScale*cubicThetaResidueScale := by
    simpa only [Complex.star_def] using
      (Complex.conj_mul' cubicThetaResidueScale).symm
  rw [hn]
  have h := cubicThetaResidueScale_constant
  push_cast at h
  rw [←h]
  simp only [star_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWindowFlux
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The radial Green flux of the actual compact incoming window. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaWindowFlux_hasDerivAt {v : ℝ} (hv : 0<v) :
    HasDerivAt cubicThetaWindowFlux
      ((v:ℂ)^(-7/3:ℂ)*cubicThetaWindowDefect (4/3) v) v := by
  have hH := cubicThetaWindowHeight_smooth (4/3:ℂ)
  have hHd := (contDiff_infty_iff_deriv.mp hH).2
  have h₁ := (cubicThetaHeightPower_hasDerivAt (-1/3) hv).mul
    (hHd.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) v).hasDerivAt
  have h₂ := ((cubicThetaHeightPower_hasDerivAt (-4/3) hv).const_mul (2/3:ℂ)).mul
    (hH.differentiable (by simp) v).hasDerivAt
  have hn : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp₁ : (v:ℂ)^(-1/3:ℂ)=(v:ℂ)^(-7/3:ℂ)*(v:ℂ)^2 := by
    rw [←Complex.cpow_ofNat,←Complex.cpow_add _ _ hn]
    congr 1
    ring
  have hp₂ : (v:ℂ)^(-4/3:ℂ)=(v:ℂ)^(-7/3:ℂ)*(v:ℂ) := by
    calc
      _ = (v:ℂ)^((-7/3:ℂ)+1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hn,Complex.cpow_one]
  refine (h₁.sub h₂).congr_deriv ?_
  · norm_num only [show (-1/3:ℂ)-1= -4/3 by ring,
      show (-4/3:ℂ)-1= -7/3 by ring]
    simp only [neg_div] at hp₁ hp₂
    rw [hp₁,hp₂]
    unfold cubicThetaWindowDefect
    ring

lemma cubicThetaWindowHeight_high_deriv (s : ℂ) {v : ℝ} (hv : 4≤v) :
    deriv (cubicThetaWindowHeight s) v=0 := by
  have hc := (cubicThetaWindowHeight_smooth s).continuous_deriv
  have he : EqOn (deriv (cubicThetaWindowHeight s)) (fun _ => 0) (Ioi 4) := by
    intro x hx
    have hn : cubicThetaWindowHeight s =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      exact cubicThetaWindowHeight_zero s (Or.inr ht.le)
    simpa only [deriv_const] using hn.deriv_eq
  exact he.closure (hc (by simp)) continuous_const (by simpa only [closure_Ioi,mem_Ici] using hv)

lemma cubicThetaWindowFlux_high {v : ℝ} (hv : 4≤v) :
    cubicThetaWindowFlux v=0 := by
  simp only [cubicThetaWindowFlux,cubicThetaWindowHeight_high_deriv _ hv,
    cubicThetaWindowHeight_zero _ (Or.inr hv),mul_zero,sub_self]

lemma cubicThetaCuspCutoff_deriv_endpoints :
    deriv cubicThetaCuspCutoff 1=0 ∧ deriv cubicThetaCuspCutoff 2=0 := by
  have hc := cubicThetaCuspCutoff_smooth.continuous_deriv (by simp)
  constructor
  · have he : EqOn (deriv cubicThetaCuspCutoff) (fun _ => 0) (Iio 1) :=
      fun _ hv => (cubicThetaCuspCutoff_derivatives_zero (Or.inl hv)).1
    exact he.closure hc continuous_const (by simp)
  · have he : EqOn (deriv cubicThetaCuspCutoff) (fun _ => 0) (Ioi 2) :=
      fun _ hv => (cubicThetaCuspCutoff_derivatives_zero (Or.inr hv)).1
    exact he.closure hc continuous_const (by simp)

lemma cubicThetaWindowHeight_two (s : ℂ) :
    cubicThetaWindowHeight s 2=(2:ℂ)^s := by
  simp only [cubicThetaWindowHeight,cubicThetaIncomingWindowCutoff,
    cubicThetaCuspCutoff_one (by norm_num : (2:ℝ)≤2),
    show (2:ℝ)/2=1 by norm_num,
    cubicThetaCuspCutoff_zero (by norm_num : (1:ℝ)≤1),sub_zero,one_mul,Complex.ofReal_ofNat]

lemma cubicThetaWindowHeight_two_deriv (s : ℂ) :
    deriv (cubicThetaWindowHeight s) 2=s*(2:ℂ)^(s-1) := by
  have hc : Differentiable ℝ cubicThetaCuspCutoff :=
    cubicThetaCuspCutoff_smooth.differentiable (by simp)
  have h₁ := (hc 2).hasDerivAt
  have h₂ := (hc ((2:ℝ)/2)).hasDerivAt.scomp (h:=fun t : ℝ => t/2) 2 ((hasDerivAt_id (2:ℝ)).div_const 2)
  norm_num only [id_eq,show (2:ℝ)/2=1 by norm_num] at h₂
  have hd := h₁.sub h₂
  rw [cubicThetaCuspCutoff_deriv_endpoints.1,cubicThetaCuspCutoff_deriv_endpoints.2] at hd
  have hp := hd.mul (cubicThetaHeightPower_hasDerivAt s (by norm_num : (0:ℝ)<2))
  change HasDerivAt (cubicThetaWindowHeight s) _ 2 at hp
  simpa only [Pi.sub_apply,Function.comp_apply,smul_zero,zero_mul,sub_zero,zero_add,cubicThetaIncomingWindowCutoff,
    cubicThetaCuspCutoff_one (by norm_num : (2:ℝ)≤2),
    show (2:ℝ)/2=1 by norm_num,
    cubicThetaCuspCutoff_zero (by norm_num : (1:ℝ)≤1),one_mul,Complex.ofReal_ofNat] using hp.deriv

lemma cubicThetaWindowFlux_two : cubicThetaWindowFlux 2=2/3 := by
  rw [cubicThetaWindowFlux,cubicThetaWindowHeight_two_deriv,cubicThetaWindowHeight_two]
  norm_num only [Complex.ofReal_ofNat]
  have h₁ : (2:ℂ)^(-1/3:ℂ)*(2:ℂ)^((4/3:ℂ)-1)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
  have h₂ : (2:ℂ)^(-4/3:ℂ)*(2:ℂ)^(4/3:ℂ)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    norm_num
  calc
    _ = (4/3:ℂ)*((2:ℂ)^(-1/3:ℂ)*(2:ℂ)^((4/3:ℂ)-1)) -
        (2/3:ℂ)*((2:ℂ)^(-4/3:ℂ)*(2:ℂ)^(4/3:ℂ)) := by ring_nf
    _ = _ := by rw [h₁,h₂]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaWindowFluxIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact boundary evaluation of the constant theta-window observation. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHighWindowFluxDensity_continuousOn :
    ContinuousOn cubicThetaHighWindowFluxDensity (Icc (2:ℝ) 4) := by
  intro v hv
  exact (((cubicThetaHeightPower_analytic (-7/3) (by linarith [hv.1])).continuousAt).mul
    (cubicThetaHighWindowForcing_continuous (4/3)).continuousAt).continuousWithinAt

lemma cubicThetaHighWindowFluxDensity_integral :
    (∫ v in Ioi (2:ℝ),cubicThetaHighWindowFluxDensity v)=2/3 := by
  have hi : IntervalIntegrable cubicThetaHighWindowFluxDensity volume 2 4 :=
    cubicThetaHighWindowFluxDensity_continuousOn.intervalIntegrable_of_Icc (by norm_num)
  have hcont : ContinuousOn cubicThetaWindowFlux (Icc (2:ℝ) 4) := by
    intro v hv
    exact (cubicThetaWindowFlux_hasDerivAt (by linarith [hv.1])).continuousAt.continuousWithinAt
  have hd (v : ℝ) (hv : v∈Ioo (2:ℝ) 4) :
      HasDerivAt cubicThetaWindowFlux (-cubicThetaHighWindowFluxDensity v) v := by
    have hf := cubicThetaWindowFlux_hasDerivAt (by linarith [hv.1])
    convert hf using 1
    all_goals try with_reducible_and_instances rfl
    rw [cubicThetaHighWindowFluxDensity,cubicThetaHighWindowForcing,
      cubicThetaIncomingForcing_zero (4/3) (Or.inr hv.1)]
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by norm_num : (2:ℝ)≤4) hcont hd hi.neg
  rw [intervalIntegral.integral_neg,cubicThetaWindowFlux_high (by norm_num),
    cubicThetaWindowFlux_two] at he
  have he' : (∫ v in (2:ℝ)..4,cubicThetaHighWindowFluxDensity v)=2/3 := by
    linear_combination -he
  rw [intervalIntegral.integral_of_le (by norm_num)] at he'
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (show Ioc (2:ℝ) 4⊆Ioi 2 from fun _ hv => hv.1)]
  · exact he'
  · intro v hv
    have hv4 : 4≤v := by
      have hn := hv.2
      simp only [mem_Ioc,not_and] at hn
      exact (lt_of_not_ge (hn hv.1)).le
    rw [cubicThetaHighWindowFluxDensity,cubicThetaHighWindowForcing_high _ hv4,mul_zero]

lemma cubicThetaHighWindowZeroRadial_integrand {v : ℝ} (hv : 0<v) :
    star (cubicThetaHighWindowForcing (4/3) v)*(v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3=
      star (cubicThetaHighWindowFluxDensity v) := by
  have hn : (v:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hp : (v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3=(v:ℂ)^(-7/3:ℂ) := by
    rw [←Complex.cpow_ofNat,←Complex.cpow_sub _ _ hn]
    congr 1
    ring
  have hs : star ((v:ℂ)^(-7/3:ℂ))=(v:ℂ)^(-7/3:ℂ) := by
    have hr := Complex.ofReal_cpow hv.le (-7/3:ℝ)
    norm_num only [Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_ofNat] at hr
    norm_num only [neg_div] at hr ⊢
    rw [←hr]
    exact Complex.conj_ofReal _
  rw [cubicThetaHighWindowFluxDensity,star_mul,hs]
  calc
    _ = star (cubicThetaHighWindowForcing (4/3) v)*
      ((v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3) := by ring
    _ = _ := by rw [hp]

theorem cubicThetaHighWindow_zero_radial :
    cubicThetaZeroRadialTest (cubicThetaHighWindowWeight (4/3)) (4/3)=2/3 := by
  unfold cubicThetaZeroRadialTest
  have he : (∫ v in Ioi (2:ℝ),star (cubicThetaHighWindowForcing (4/3) v)*
      (v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3)=
      ∫ v in Ioi (2:ℝ),star (cubicThetaHighWindowFluxDensity v) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    exact cubicThetaHighWindowZeroRadial_integrand (lt_trans (by norm_num) hv)
  change (∫ v in Ioi (2:ℝ),star (cubicThetaHighWindowForcing (4/3) v)*
    (v:ℂ)^((2:ℂ)-4/3)/(v:ℂ)^3)=_
  rw [he]
  change (∫ v in Ioi (2:ℝ),(starRingEnd ℂ) (cubicThetaHighWindowFluxDensity v))=_
  rw [integral_conj,cubicThetaHighWindowFluxDensity_integral]
  norm_num [starRingEnd_apply,Complex.star_def]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaResidueNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact global L2 norms of the actual and constant-normalized residues. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaNormalizedArithmeticResidue_norm_sq :
    (‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ)=
      cubicThetaResidueScale*((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ) := by
  rw [cubicThetaNormalizedArithmeticResidue_mass_sq,cubicThetaHighWindow_zero_radial]
  simp only [star_mul,star_div₀,star_ofNat,Complex.star_def,Complex.conj_ofReal]
  ring

theorem cubicThetaNormalizedArithmeticResidue_norm_identity :
    (‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ)*
      ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))=
      ((9*Real.sqrt 3/2:ℝ):ℂ)*(cubicThetaConstant:ℂ)^2 := by
  rw [cubicThetaNormalizedArithmeticResidue_norm_sq,cubicThetaResidueScale]
  have hπ : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hZ := cubicTheta_principalZeta_two_ne_zero
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaModelRankinLimit
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Rankin pole paired with the actual global cubic theta section. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProduct
namespace CubicFirstMoment

lemma cubicThetaArithmeticModelPairing_eq (q : CubicThetaQuotient) :
    cubicThetaSectionPairing cubicThetaArithmeticModelSection cubicThetaArithmeticModelSection q=
      (‖cubicThetaSectionRepresentative cubicThetaArithmeticModelSection q‖^2:ℂ) := by
  have h := cubicThetaSectionPairing_apply cubicThetaArithmeticModelSection
    cubicThetaArithmeticModelSection (cubicThetaBorelSection q)
  rw [cubicThetaBorelSection_rightInverse,inner_self_eq_norm_sq_to_K] at h
  exact h

lemma cubicThetaArithmeticModelPairing_integrable :
    Integrable (cubicThetaSectionPairing cubicThetaArithmeticModelSection
      cubicThetaArithmeticModelSection) cubicThetaQuotientMeasure := by
  have hr : Integrable (fun q => ‖cubicThetaSectionRepresentative cubicThetaArithmeticModelSection q‖^2)
      cubicThetaQuotientMeasure :=
    cubicThetaArithmeticModelGlobal_memLp.integrable_norm_pow (by norm_num)
  have h := hr.ofReal (𝕜:=ℂ)
  apply h.congr
  filter_upwards with q
  rw [cubicThetaArithmeticModelPairing_eq]
  norm_cast

lemma cubicThetaArithmeticModelPairing_integral :
    (∫ q,cubicThetaSectionPairing cubicThetaArithmeticModelSection
      cubicThetaArithmeticModelSection q ∂cubicThetaQuotientMeasure)=
      (‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ) := by
  rw [←cubicThetaSectionPairing_L2 _ _ cubicThetaArithmeticModelGlobal_memLp
    cubicThetaArithmeticModelGlobal_memLp,cubicThetaArithmeticModelGlobalL2,
    inner_self_eq_norm_sq_to_K]
  norm_cast

theorem cubicThetaArithmeticRankinMass_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*cubicThetaArithmeticRankinMass σ) (𝓝[>] 0)
      (𝓝 (((9*Real.sqrt 3/4:ℝ):ℂ)*(cubicThetaConstant:ℂ)^2)) := by
  have h := cubicThetaScalarRankinKernel_integral_limit
    (cubicThetaSectionPairing cubicThetaArithmeticModelSection cubicThetaArithmeticModelSection)
    cubicThetaArithmeticModelPairing_integrable
  have he (σ : ℝ) : (∫ q,(σ:ℂ)*(cubicThetaScalarRankinKernel σ q:ℂ)*
      cubicThetaSectionPairing cubicThetaArithmeticModelSection cubicThetaArithmeticModelSection q
      ∂cubicThetaQuotientMeasure)=(σ:ℂ)*cubicThetaArithmeticRankinMass σ := by
    rw [cubicThetaArithmeticRankinMass,←integral_const_mul]
    congr 1
    funext q
    ring
  simp_rw [he] at h
  rw [cubicThetaArithmeticModelPairing_integral] at h
  have hn := cubicThetaNormalizedArithmeticResidue_norm_identity
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  calc
    ((9*Real.sqrt 3/4:ℝ):ℂ)*(cubicThetaConstant:ℂ)^2 =
        (1/2:ℂ)*((‖cubicThetaGlobalInclusion cubicThetaNormalizedArithmeticResidue‖^2:ℂ)*
          ((Real.pi:ℂ)^2/(54*principalIdealZeta 2))) := by rw [hn]; push_cast; ring
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaScalarRankinRadial
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact radial integral of the positive scalar Rankin seed. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

lemma cubicThetaRankin_height_power {v : ℝ} (hv : 0<v) (σ : ℝ) :
    ((v^(2+2*σ):ℝ):ℂ)/(v:ℂ)^3=((v^(2*σ-1):ℝ):ℂ) := by
  have hr : v^(2+2*σ)/v^3=v^(2*σ-1) := by
    rw [←Real.rpow_natCast,←Real.rpow_sub hv]
    congr 1
    ring
  exact_mod_cast hr

lemma cubicThetaScalarEnergySeed_radial {σ : ℝ}
    (hi : Integrable (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ)
      cubicThetaPointMeasure) :
    (∫ p,(cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)
      ∂cubicThetaPointMeasure)=((9*Real.sqrt 3/2:ℝ):ℂ)*
        ∫ v in Ioc (0:ℝ) 1,cubicThetaRankinRadialEnergy σ v := by
  let f : ℂ × ℝ → ℂ := fun y => if y.2≤1 then
    ((y.2^(2+2*σ):ℝ):ℂ)*(‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar y‖^2:ℂ) else 0
  have hseed (p : CubicThetaPoint) :
      (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)=
        if p.val.1∈cubicThetaHorizontalCell then f p.val else 0 := by
    simp only [cubicThetaScalarEnergySeed,cubicThetaScalarHeightSeed,
      cubicThetaScalarHeightWeight,cubicThetaArithmeticModelSection,f]
    split_ifs <;> simp_all only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_zero,zero_mul]
    rfl
  have hstrip : ∀ p∈cubicThetaCuspStrip 0,
      (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)=f p.val := by
    intro p hp
    change 0<p.val.2 ∧ p.val.1∈cubicThetaHorizontalCell at hp
    rw [hseed,ite_eq_left hp.2]
  have hfi : IntegrableOn (fun p : CubicThetaPoint => f p.val)
      (cubicThetaCuspStrip 0) cubicThetaPointMeasure := by
    apply hi.ofReal.integrableOn.congr
    filter_upwards [ae_restrict_mem (cubicThetaCuspStrip_measurable 0)] with p hp
    exact hstrip p hp
  have hout : ∀ p∉cubicThetaCuspStrip 0,
      (cubicThetaScalarEnergySeed cubicThetaArithmeticModelSection σ p:ℂ)=0 := by
    intro p hp
    rw [hseed]
    exact ite_eq_right (fun hc => hp ⟨p.property,hc⟩)
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  rw [setIntegral_congr_fun (cubicThetaCuspStrip_measurable 0) hstrip]
  have hfub := cubicThetaPositiveCuspStrip_fubini (le_refl (0:ℝ)) f hfi
  change (∫ p in cubicThetaCuspStrip 0,f p.val ∂cubicThetaPointMeasure)=_ at hfub
  rw [hfub]
  have hz (v : ℝ) (hv : 0<v) :
      (∫ z in cubicThetaHorizontalCell,f (z,v)/(v:ℂ)^3)=
        if v≤1 then ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaRankinRadialEnergy σ v else 0 := by
    by_cases hv1 : v≤1
    · simp only [f,ite_eq_left hv1]
      have he (z : ℂ) : ((v^(2+2*σ):ℝ):ℂ)*
          (‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v)‖^2:ℂ)/(v:ℂ)^3=
            (((v^(2+2*σ):ℝ):ℂ)/(v:ℂ)^3)*
              (‖cubicThetaArithmeticModel cubicThetaArithmeticBaseScalar (z,v)‖^2:ℂ) := by ring
      simp_rw [he]
      rw [integral_const_mul,cubicThetaArithmeticModel_horizontal_energy _ hv,
        cubicThetaRankin_height_power hv]
      unfold cubicThetaRankinRadialEnergy
      ring
    · simp only [f,ite_eq_right hv1,zero_div,integral_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi hz]
  have he : (fun v : ℝ => if v≤1 then
      ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaRankinRadialEnergy σ v else 0)=
      (Iic (1:ℝ)).indicator (fun v => ((9*Real.sqrt 3/2:ℝ):ℂ)*cubicThetaRankinRadialEnergy σ v) := rfl
  rw [he,integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have hset : Iic (1:ℝ)∩Ioi 0=Ioc 0 1 := by ext v; simp only [mem_inter_iff,mem_Iic,mem_Ioi,mem_Ioc,and_comm]
  rw [hset,integral_const_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRankinRadialMass
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Splitting the constant mode from the exact radial Rankin integral. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaRankin_constant_integral {σ : ℝ} (hσ : 0<σ) :
    (∫ v in Ioc (0:ℝ) 1,cubicThetaConstant^2*v^(2*σ+1/3))=
      cubicThetaConstant^2/(2*σ+4/3) := by
  rw [integral_const_mul,←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),
    integral_rpow (Or.inl (by linarith : -1<2*σ+1/3))]
  rw [Real.one_rpow,Real.zero_rpow (by linarith : 2*σ+1/3+1≠0)]
  ring

lemma cubicThetaRankin_constant_term {σ v : ℝ} (hv : 0<v) :
    v^(2*σ-1)*(cubicThetaConstant*v^(2/3:ℝ))^2=
      cubicThetaConstant^2*v^(2*σ+1/3) := by
  have hp : (v^(2/3:ℝ))^2=v^(4/3:ℝ) := by
    rw [←Real.rpow_mul_natCast hv.le]
    norm_num
  rw [mul_pow,hp]
  calc
    _ = cubicThetaConstant^2*(v^(2*σ-1)*v^(4/3:ℝ)) := by ring
    _ = _ := by rw [←Real.rpow_add hv]; congr 1; congr 1; ring

lemma cubicThetaRankinRadialEnergy_integral {σ : ℝ} (hσ : 0<σ) :
    (∫ v in Ioc (0:ℝ) 1,cubicThetaRankinRadialEnergy σ v)=
      ((cubicThetaConstant^2/(2*σ+4/3):ℝ):ℂ)+
        (‖cubicThetaArithmeticBaseScalar‖^2:ℝ)*
          (cubicThetaFourierEnergyLowMass σ:ℂ) := by
  have hconst : IntegrableOn (fun v : ℝ => cubicThetaConstant^2*v^(2*σ+1/3)) (Ioc 0 1) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<2*σ+1/3))).const_mul _
  have henergy := ((cubicThetaArithmeticFourierEnergy_mellin_integrable hσ).mono_set
    (show Ioc (0:ℝ) 1⊆Ioi 0 from Ioc_subset_Ioi_self)).const_mul
      (‖cubicThetaArithmeticBaseScalar‖^2)
  have he : (∫ v in Ioc (0:ℝ) 1,cubicThetaRankinRadialEnergy σ v)=
      ((∫ v in Ioc (0:ℝ) 1,cubicThetaConstant^2*v^(2*σ+1/3)+
        ‖cubicThetaArithmeticBaseScalar‖^2*(v^(2*σ-1)*cubicThetaArithmeticFourierEnergy v):ℝ):ℂ) := by
    rw [←integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    unfold cubicThetaRankinRadialEnergy
    have hc := cubicThetaRankin_constant_term (σ:=σ) hv.1
    push_cast
    have hcc := congrArg Complex.ofReal hc
    push_cast at hcc
    linear_combination hcc
  rw [he,integral_add hconst henergy,cubicThetaRankin_constant_integral hσ,integral_const_mul]
  push_cast
  rfl

theorem cubicThetaRankinRadialEnergy_residue :
    Tendsto (fun σ : ℝ => (σ:ℂ)*∫ v in Ioc (0:ℝ) 1,cubicThetaRankinRadialEnergy σ v)
      (𝓝[>] 0) (𝓝 ((‖cubicThetaArithmeticBaseScalar‖^2:ℝ)*(243/8:ℂ))) := by
  have hσ : Tendsto (fun σ : ℝ => (σ:ℂ)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
  have hc : ContinuousAt (fun σ : ℝ => ((cubicThetaConstant^2/(2*σ+4/3):ℝ):ℂ)) 0 := by
    fun_prop (disch := norm_num)
  have hz := hσ.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [zero_mul] at hz
  have h := hz.add (cubicThetaFourierEnergyLowMass_residue.const_mul
    ((‖cubicThetaArithmeticBaseScalar‖^2:ℝ):ℂ))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  rw [cubicThetaRankinRadialEnergy_integral hσ]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBaseScalarNorm
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global norm and the arithmetic coefficient pole determine
precisely the magnitude of the Fourier normalization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaConstant_square : cubicThetaConstant^2=243/4 := by
  rw [cubicThetaConstant,div_pow,←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  norm_num

theorem cubicThetaArithmeticBaseScalar_norm_sq : ‖cubicThetaArithmeticBaseScalar‖^2=1 := by
  have hmath := cubicThetaRankinRadialEnergy_residue.const_mul ((9*Real.sqrt 3/2:ℝ):ℂ)
  have hsecond : Tendsto (fun σ : ℝ => (σ:ℂ)*cubicThetaArithmeticRankinMass σ)
      (𝓝[>] 0) (𝓝 (((9*Real.sqrt 3/2:ℝ):ℂ)*
        ((‖cubicThetaArithmeticBaseScalar‖^2:ℝ)*(243/8:ℂ)))) := by
    apply hmath.congr'
    filter_upwards [cubicThetaArithmeticRankinMass_unfold] with σ hσ
    rw [hσ.2,cubicThetaScalarEnergySeed_radial hσ.1]
    ring
  have he := tendsto_nhds_unique cubicThetaArithmeticRankinMass_residue hsecond
  have hr : (9*Real.sqrt 3/4)*cubicThetaConstant^2=
      (9*Real.sqrt 3/2)*(‖cubicThetaArithmeticBaseScalar‖^2*(243/8)) := by
    apply Complex.ofReal_injective
    push_cast at he ⊢
    exact he
  rw [cubicThetaConstant_square] at hr
  have h3 : 0<Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hz : Real.sqrt 3*(‖cubicThetaArithmeticBaseScalar‖^2-1)=0 := by nlinarith [hr]
  have h := (mul_eq_zero.mp hz).resolve_left h3.ne'
  linarith

theorem cubicThetaArithmeticBaseScalar_norm : ‖cubicThetaArithmeticBaseScalar‖=1 := by
  have h := cubicThetaArithmeticBaseScalar_norm_sq
  have hn := _root_.norm_nonneg cubicThetaArithmeticBaseScalar
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaGaussConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complex conjugation of the finite arithmetic data used to normalize
Patterson's theta series. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicTheta_gauss_conjugate {b : Eisenstein} (hb : primary b) :
    gauss (conjugate b) = star (gauss b) := by
  refine primary_induction (P := fun b => gauss (conjugate b) = star (gauss b)) ?_ ?_ hb
  · simp only [map_one, gauss_one, star_one]
  · intro p c hp hc ih
    rw [map_mul, gauss_mul (primary_conjugate hp.1) (primary_conjugate hc),
      gauss_mul hp.1 hc, cubicSymbol_conjugate hc p, ih,
      gauss_prime (primaryPrime_conjugate hp), gaussAtPrime_conjugate hp,
      ← gauss_prime hp, star_mul, star_mul, star_star]
    ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaConjugateCoordinates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation preserves the exact arithmetic coefficient coordinates,
including their ramified exponent and unit phase. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicThetaNinePhase_conjugate (n : Eisenstein) :
    cubicThetaNinePhase (conjugate n) = star (cubicThetaNinePhase n) := by
  obtain ⟨a,b,hn⟩ := exists_coordinates n
  have he : n = ofCoords a b := Subtype.ext (by simpa only [ofCoords_coe] using hn)
  have hc : conjugate n = ofCoords (a-b) (-b) := by
    apply Subtype.ext
    rw [conjugate_coe,hn]
    simp only [star_add,star_mul,star_intCast,star_omega_linear,ofCoords_coe]
    push_cast
    ring
  rw [hc,he,cubicThetaNinePhase_coordinates,cubicThetaNinePhase_coordinates]
  simp only [Int.cast_neg,neg_div,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj,
    Complex.star_def]

lemma cubicThetaUnitPhase_fourth {u v : Eisensteinˣ}
    (h : (u:Eisenstein)^4 = (v:Eisenstein)^4) :
    cubicThetaUnitPhase u = cubicThetaUnitPhase v := by
  simp only [cubicThetaUnitPhase,h]

lemma cubicThetaUnitPhase_conjugate (u : Eisensteinˣ) :
    cubicThetaUnitPhase (Units.map conjugate.toMonoidHom u) =
      star (cubicThetaUnitPhase u) := by
  rw [cubicThetaUnitPhase_eq,cubicThetaUnitPhase_eq]
  simpa only [cubicTheta_conjugateUnit_val,←map_pow] using
    cubicThetaNinePhase_conjugate ((u:Eisenstein)^2)

lemma CubicThetaCoordinates.conjugated_amplitude {n : Eisenstein}
    (R : CubicThetaCoordinates n) : R.conjugated.amplitude = R.amplitude := by
  simp only [amplitude,conjugated,norm_conjugate]

lemma CubicThetaCoordinates.conjugated_unit_fourth {n : Eisenstein}
    (R : CubicThetaCoordinates n) :
    (R.conjugated.unit:Eisenstein)^4 = conjugate ((R.unit:Eisenstein)^4) := by
  simp only [conjugated,Units.val_mul,Units.val_pow_eq_pow_val,cubicTheta_conjugateUnit_val,Units.val_neg,Units.val_one,mul_pow,←pow_mul]
  rw [Nat.mul_comm R.order 4,pow_mul]
  norm_num [map_pow]

lemma CubicThetaCoordinates.conjugated_phase {n : Eisenstein}
    (R : CubicThetaCoordinates n) :
    cubicThetaUnitPhase R.conjugated.unit = star (cubicThetaUnitPhase R.unit) := by
  rw [cubicThetaUnitPhase_fourth (v := Units.map conjugate.toMonoidHom R.unit)
    (by simpa only [cubicTheta_conjugateUnit_val,map_pow] using R.conjugated_unit_fourth)]
  exact cubicThetaUnitPhase_conjugate R.unit

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCoefficientConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full normalized arithmetic Fourier family commutes with
Eisenstein conjugation. Its ramified support and phases remain explicit. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma CubicThetaCoordinates.conjugated_unit_square {n : Eisenstein}
    (R : CubicThetaCoordinates n) :
    (R.conjugated.unit:Eisenstein)^2 = conjugate ((R.unit:Eisenstein)^2) := by
  simp only [conjugated,Units.val_mul,Units.val_pow_eq_pow_val,cubicTheta_conjugateUnit_val,Units.val_neg,Units.val_one,mul_pow,←pow_mul]
  rw [Nat.mul_comm R.order 2,pow_mul]
  norm_num [map_pow]

lemma CubicThetaCoordinates.conjugated_unit_real {n : Eisenstein}
    (R : CubicThetaCoordinates n) :
    ((R.conjugated.unit:Eisenstein) = 1 ∨ (R.conjugated.unit:Eisenstein) = -1) ↔
      ((R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1) := by
  rw [←sq_eq_one_iff,←sq_eq_one_iff,R.conjugated_unit_square]
  exact ⟨fun h => conjugate.injective (h.trans (map_one conjugate).symm),
    fun h => by rw [h,map_one]⟩

lemma CubicThetaCoordinates.conjugated_coefficient {n : Eisenstein}
    (R : CubicThetaCoordinates n) : R.conjugated.coefficient = star R.coefficient := by
  have ht : cubicThetaTwistedGauss (conjugate R.squarefreePart)
      ((R.conjugated.unit:Eisenstein)^4*lambdaE^2) =
      star (cubicThetaTwistedGauss R.squarefreePart ((R.unit:Eisenstein)^4*lambdaE^2)) := by
    have hLam : conjugate (lambdaE^2) = lambdaE^2 := by
      rw [map_pow,cubicTheta_conjugate_lambda,neg_sq]
    have harg : (R.conjugated.unit:Eisenstein)^4*lambdaE^2 =
        conjugate ((R.unit:Eisenstein)^4*lambdaE^2) := by
      rw [map_mul,R.conjugated_unit_fourth,hLam]
    rw [harg,cubicThetaTwistedGauss,cubicThetaTwistedGauss,
      cubicSymbol_conjugate R.squarefree_primary,
      cubicTheta_gauss_conjugate R.squarefree_primary,star_mul,star_star]
    ring
  have hs : (R.conjugated.order % 3 = 1 ∧
      ((R.conjugated.unit:Eisenstein) = 1 ∨ (R.conjugated.unit:Eisenstein) = -1)) ↔
      (R.order % 3 = 1 ∧ ((R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1)) :=
    and_congr Iff.rfl R.conjugated_unit_real
  change (R.order % 3 = 1 ∧
    ((R.conjugated.unit:Eisenstein) = 1 ∨ (R.conjugated.unit:Eisenstein) = -1)) ↔
    (R.order % 3 = 1 ∧ ((R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1)) at hs
  simp only [coefficient,show R.conjugated.order = R.order from rfl,hs,
    show R.conjugated.squarefreePart = conjugate R.squarefreePart from rfl,
    R.conjugated_amplitude,R.conjugated_phase,ht]
  split_ifs <;> simp only [star_mul,star_zero,Complex.star_def,Complex.conj_ofReal,
    cubicTheta_gauss_conjugate R.squarefree_primary] <;> ring


theorem cubicThetaArithmeticCoefficient_conjugate (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (conjugate n) = star (cubicThetaArithmeticCoefficient n) := by
  by_cases hn : Nonempty (CubicThetaCoordinates n)
  · let R := Classical.choice hn
    rw [cubicThetaArithmeticCoefficient_formula R.conjugated,
      cubicThetaArithmeticCoefficient_formula R,R.conjugated_coefficient]
  · have hc : ¬Nonempty (CubicThetaCoordinates (conjugate n)) := by
      rintro ⟨R⟩
      exact hn (by simpa only [conjugate_conjugate] using
        (show Nonempty (CubicThetaCoordinates (conjugate (conjugate n))) from ⟨R.conjugated⟩))
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hn,dite_eq_right hc,star_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBaseScalarReal
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual base scalar is real. This uses exact conjugation of the
arithmetic series and its proved inversion law; it does not set the scalar
or its absolute value equal to one. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmetic_axis_term_star (n : Eisenstein) (v : ℝ) :
    star (cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v n) =
      cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v (conjugate n) := by
  by_cases hn : n = 0
  · simp [hn,cubicThetaSeriesTerm]
  · have hc : conjugate n ≠ 0 := fun h => hn (conjugate.injective (h.trans (map_zero conjugate).symm))
    have hf : ‖cubicThetaFrequency (conjugate n)‖ = ‖cubicThetaFrequency n‖ := by
      simp only [cubicThetaFrequency,norm_div,conjugate_coe,norm_star]
    simp only [cubicThetaSeriesTerm,hn,hc,ite_false, if_false,
      cubicThetaArithmeticCoefficient_conjugate,hf,tracePair,mul_zero,
      Complex.zero_re,mul_zero,AddChar.map_zero_eq_one,Circle.coe_one,mul_one,
      star_mul,cubicThetaWhittaker_star]
    ring

lemma cubicThetaArithmeticAxis_star (v : ℝ) :
    star (cubicThetaArithmeticAxis v) = cubicThetaArithmeticAxis v := by
  unfold cubicThetaArithmeticAxis cubicThetaNonconstant
  rw [tsum_star]
  calc
    _ = ∑' n : Eisenstein,
        cubicThetaSeriesTerm cubicThetaArithmeticCoefficient 0 v (conjugate n) :=
      tsum_congr (fun n => cubicThetaArithmetic_axis_term_star n v)
    _ = _ := conjugate.toEquiv.tsum_eq _

lemma cubicThetaSeriesConstant_star : star cubicThetaSeriesConstant = cubicThetaSeriesConstant := by
  let d : ℝ := (2:ℝ)^(-(2/3:ℝ))-(2:ℝ)^(2/3:ℝ)
  have hd : d < 0 := sub_neg.mpr (Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num))
  have hd0 : (d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne
  have he := cubicThetaArithmeticAxis_small (v:=2) (by norm_num)
  have hp : ((2:ℂ)^(-(2/3:ℂ))-(2:ℂ)^(2/3:ℂ)) = (d:ℂ) := by
    rw [Complex.ofReal_sub,Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2),
      Complex.ofReal_cpow (by norm_num : (0:ℝ) ≤ 2)]
    norm_num only [Complex.ofReal_neg,Complex.ofReal_div,Complex.ofReal_ofNat]
  norm_num only [Complex.ofReal_ofNat] at he
  rw [hp] at he
  have hs := congrArg star he
  simp only [star_add,star_mul,cubicThetaArithmeticAxis_star,
    Complex.star_def,Complex.conj_ofReal] at hs
  apply mul_right_cancel₀ hd0
  simpa only [←Complex.star_def,mul_comm] using add_left_cancel (hs.symm.trans he)

theorem cubicThetaArithmeticBaseScalar_star :
    star cubicThetaArithmeticBaseScalar = cubicThetaArithmeticBaseScalar := by
  have hC : (cubicThetaConstant:ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold cubicThetaConstant
    positivity
  have he := cubicThetaSeriesConstant_star
  rw [cubicThetaSeriesConstant,star_div₀,Complex.star_def,Complex.conj_ofReal] at he
  have hb := cubicThetaArithmeticBaseScalar_ne_zero
  have hx := (div_eq_div_iff (star_ne_zero.mpr hb) hb).mp he
  exact (mul_left_cancel₀ hC hx).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBaseScalarSign
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The only remaining normalization ambiguity is the sign of the actual
base coefficient. No choice of that sign is made here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticBaseScalar_sq : cubicThetaArithmeticBaseScalar^2=1 := by
  calc
    _ = star cubicThetaArithmeticBaseScalar*cubicThetaArithmeticBaseScalar := by
      rw [cubicThetaArithmeticBaseScalar_star]
      ring
    _ = (‖cubicThetaArithmeticBaseScalar‖:ℂ)^2 := by
      simpa only [Complex.star_def] using Complex.conj_mul' cubicThetaArithmeticBaseScalar
    _ = 1 := by rw [cubicThetaArithmeticBaseScalar_norm]; norm_num

theorem cubicThetaArithmeticBaseScalar_sign :
    cubicThetaArithmeticBaseScalar=1 ∨ cubicThetaArithmeticBaseScalar= -1 := by
  have h : (cubicThetaArithmeticBaseScalar-1)*(cubicThetaArithmeticBaseScalar+1)=0 := by
    linear_combination cubicThetaArithmeticBaseScalar_sq
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaAxisDerivativeBalance
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inversion fixes the axis derivative at height one. A negative real
arithmetic derivative determines the remaining sign of the base scalar. -/
noncomputable section
open Filter Set
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaArithmeticAxis_hasDerivAt {v : ℝ} (hv : 0<v) :
    HasDerivAt cubicThetaArithmeticAxis (cubicThetaArithmeticAxisDerivative v) v := by
  have h := cubicThetaAngular_vertical_hasDerivAt (by norm_num : (0:ℝ)≤81)
    cubicThetaArithmeticCoefficient_bound 0 hv 0
  have he : cubicThetaAngularCoefficient cubicThetaArithmeticCoefficient 0=cubicThetaArithmeticCoefficient := by
    funext n
    simp only [cubicThetaAngularCoefficient,Int.natAbs_zero,pow_zero,theta_zero,one_mul]
  rw [he] at h
  exact h


lemma cubicThetaArithmeticAxisDerivative_balance :
    cubicThetaArithmeticAxisDerivative 1= -(2/3:ℂ)*cubicThetaSeriesConstant := by
  let A := cubicThetaArithmeticAxisDerivative 1
  have hA : HasDerivAt cubicThetaArithmeticAxis A 1 :=
    cubicThetaArithmeticAxis_hasDerivAt (by norm_num)
  have hinv : HasDerivAt (fun v : ℝ => v⁻¹) (-1) 1 := by
    simpa using (hasDerivAt_inv (by norm_num : (1:ℝ)≠0))
  have hAi : HasDerivAt (fun v : ℝ => cubicThetaArithmeticAxis v⁻¹) (-A) 1 := by
    have hA' : HasDerivAt cubicThetaArithmeticAxis A ((1:ℝ)⁻¹) := by simpa using hA
    simpa only [Function.comp_def,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
      hA'.scomp 1 hinv
  have hp : HasDerivAt (fun v : ℝ => ((v^(2/3:ℝ):ℝ):ℂ)) (2/3) 1 := by
    convert (Real.hasDerivAt_rpow_const (x:=1) (p:=(2/3:ℝ)) (Or.inl (by norm_num))).ofReal_comp using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
  have hpi : HasDerivAt (fun v : ℝ => (((v⁻¹)^(2/3:ℝ):ℝ):ℂ)) (-(2/3)) 1 := by
    have hp' : HasDerivAt (fun v : ℝ => ((v^(2/3:ℝ):ℝ):ℂ)) (2/3) ((1:ℝ)⁻¹) := by simpa using hp
    simpa only [Function.comp_def,Complex.real_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
      hp'.scomp 1 hinv
  have hR := hAi.add ((hpi.sub hp).const_mul cubicThetaSeriesConstant)
  have he : cubicThetaArithmeticAxis =ᶠ[𝓝 (1:ℝ)]
      (fun v => cubicThetaArithmeticAxis v⁻¹+cubicThetaSeriesConstant*
        ((((v⁻¹)^(2/3:ℝ):ℝ):ℂ)-((v^(2/3:ℝ):ℝ):ℂ))) := by
    filter_upwards [show Ioi (0:ℝ)∈𝓝 1 from Ioi_mem_nhds (by norm_num)] with v hv
    exact cubicThetaArithmetic_center_small hv
  have h := hA.unique (hR.congr_of_eventuallyEq he)
  change A= -A+cubicThetaSeriesConstant*(-(2/3)-(2/3)) at h
  dsimp [A] at h
  linear_combination (1/2:ℂ)*h

theorem cubicThetaArithmeticBaseScalar_eq_one_of_axisDerivative_neg
    (hneg : (cubicThetaArithmeticAxisDerivative 1).re<0) :
    cubicThetaArithmeticBaseScalar=1 := by
  rcases cubicThetaArithmeticBaseScalar_sign with h | h
  · exact h
  · rw [cubicThetaArithmeticAxisDerivative_balance,cubicThetaSeriesConstant,h] at hneg
    have hC : 0 < cubicThetaConstant := by unfold cubicThetaConstant; positivity
    norm_num [div_neg] at hneg
    nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaBaseScalarValue
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two negative leading terms dominate the complete arithmetic tail,
fixing the sign of the actual theta normalization. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cubicThetaArithmeticBaseScalar_eq_one : cubicThetaArithmeticBaseScalar=1 :=
  cubicThetaArithmeticBaseScalar_eq_one_of_axisDerivative_neg
    cubicThetaArithmeticAxisDerivative_re_neg

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaRadialMainConstant
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact comparison of the constructed radial residue with the printed
main-term constant. The remaining arithmetic normalization is explicit. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaRadial_uncompletion_pole {r : Eisenstein} (hr : primary r) :
    cubicThetaAngularUncompletion r 0 (5/6)=
      ((4*cubicThetaLevelScale r^(2/3:ℝ)*(2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ):ℝ):ℂ) := by
  unfold cubicThetaAngularUncompletion
  norm_num only [Nat.cast_zero,zero_div,add_zero,
    show 2*(5/6:ℂ)-1=2/3 by norm_num,
    show 2*(5/6:ℂ)=5/3 by norm_num,
    show (5/6:ℂ)+1/6=1 by norm_num,
    show (5/6:ℂ)-1/6=2/3 by norm_num,
    Complex.Gamma_one,inv_one,mul_one]
  rw [show (2/3:ℂ)=((2/3:ℝ):ℂ) by norm_num,
    show (5/3:ℂ)=((5/3:ℝ):ℂ) by norm_num,
    ←Complex.ofReal_cpow (cubicThetaLevelScale_pos hr).le,
    ←Complex.ofReal_cpow (by positivity : (0:ℝ)≤2*Real.pi),Complex.Gamma_ofReal]
  push_cast
  ring

lemma cubicThetaRadial_level_pole_power {r : Eisenstein} (hr : primary r) :
    cubicThetaLevelScale r^(2/3:ℝ)*cubicThetaLevelScale r^(2/3:ℝ)/Real.sqrt (norm r)=
      norm r^(-7/6:ℝ) := by
  have hN := norm_pos_of_ne_zero (primary_ne_zero hr)
  have hS := Real.sqrt_pos.mpr hN
  rw [←Real.rpow_add (cubicThetaLevelScale_pos hr)]
  norm_num only [show (2/3:ℝ)+2/3=4/3 by norm_num]
  unfold cubicThetaLevelScale
  rw [Real.inv_rpow hS.le,div_eq_mul_inv,←Real.rpow_neg hS.le,
    ←Real.rpow_neg_one,←Real.rpow_add hS,
    Real.sqrt_eq_rpow,←Real.rpow_mul hN.le]
  congr 1
  norm_num

lemma cubicThetaSeriesConstant_mul_base :
    star cubicThetaSeriesConstant*star cubicThetaArithmeticBaseScalar=(cubicThetaConstant:ℂ) := by
  rw [←star_mul,cubicThetaSeriesConstant,mul_div_cancel₀ _ cubicThetaArithmeticBaseScalar_ne_zero]
  exact Complex.conj_ofReal _

lemma cubicThetaRadial_scale_pole {X : ℝ} (hX : 0<X) :
    (X/27)^(5/6:ℝ)=X^(5/6:ℝ)/(3:ℝ)^(5/2:ℝ) := by
  rw [Real.div_rpow hX.le (by norm_num)]
  congr 1
  calc
    (27:ℝ)^(5/6:ℝ)=((3:ℝ)^(3:ℝ))^(5/6:ℝ) := by norm_num
    _ = (3:ℝ)^((3:ℝ)*(5/6)) := (Real.rpow_mul (by norm_num) _ _).symm
    _ = _ := by norm_num

lemma cubicThetaRadial_real_main {r : Eisenstein} (hr : primary r) {X : ℝ} (hX : 0<X) :
    (4*cubicThetaLevelScale r^(2/3:ℝ)*(2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ))/2*
      (metaplecticTotient r*(cubicThetaConstant/3))*cubicThetaLevelScale r^(2/3:ℝ)/
      ((3:ℝ)^(5/2:ℝ)*Real.sqrt (norm r))*(X/27)^(5/6:ℝ)=
      metaplecticA0*X^(5/6:ℝ)*metaplecticTotient r*norm r^(-7/6:ℝ) := by
  have hthree : (3:ℝ)^(7/2:ℝ)=3*(3:ℝ)^(5/2:ℝ) := by
    rw [show (7/2:ℝ)=1+5/2 by norm_num,Real.rpow_add (by norm_num),Real.rpow_one]
  have h35 : (3:ℝ)^(5/2:ℝ)≠0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hG : Real.Gamma (2/3:ℝ)≠0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  calc
    _ = (2*cubicThetaConstant/(3*(3:ℝ)^(5/2:ℝ)))*
        (cubicThetaLevelScale r^(2/3:ℝ)*cubicThetaLevelScale r^(2/3:ℝ)/Real.sqrt (norm r))*
        ((2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ))*metaplecticTotient r*(X/27)^(5/6:ℝ) := by ring
    _ = _ := by
      rw [cubicThetaRadial_level_pole_power hr,cubicThetaRadial_scale_pole hX]
      unfold cubicThetaConstant metaplecticA0
      rw [hthree]
      field_simp

/-- This comparison isolates the exact outstanding normalization: the
constructed main term times the conjugate base scalar is the printed one. -/
theorem cubicThetaActualCompletedRadialMain_mul_base {r : Eisenstein} (hr : primary r)
    (W : ℝ→ℂ) {X : ℝ} (hX : 0<X) :
    cubicThetaActualCompletedRadialMain r W X*star cubicThetaArithmeticBaseScalar=
      metaplecticMain r 0 W X := by
  rw [cubicThetaActualCompletedRadialMain,cubicThetaResidueRadialPole,
    cubicThetaRadial_uncompletion_pole hr]
  have hX27 : 0≤X/27 := (div_pos hX (by norm_num)).le
  rw [show (5/6:ℂ)=((5/6:ℝ):ℂ) by norm_num,←Complex.ofReal_cpow hX27]
  calc
    _ = ((4*cubicThetaLevelScale r^(2/3:ℝ)*(2*Real.pi)^(5/3:ℝ)/Real.Gamma (2/3:ℝ):ℝ):ℂ)/2*
        ((Nat.card (Residues r)ˣ:ℂ)*((star cubicThetaSeriesConstant*star cubicThetaArithmeticBaseScalar)/3))*
        ((cubicThetaLevelScale r^(2/3:ℝ):ℝ):ℂ)/
        (((3^(5/2:ℝ):ℝ):ℂ)*(Real.sqrt (norm r):ℂ))*
        (((X/27)^(5/6:ℝ):ℝ):ℂ)*mellin W (5/6) := by
      push_cast
      ring
    _ = _ := by
      rw [cubicThetaSeriesConstant_mul_base]
      have he := congrArg (fun q : ℝ => (q:ℂ)*mellin W (5/6)) (cubicThetaRadial_real_main hr hX)
      simpa only [Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,
        metaplecticMain,ite_true, if_true,metaplecticTotient,Complex.ofReal_natCast,mul_assoc] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Theta_CubicThetaCenteredLow
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centering the actual completed transform with its now determined
radial constant, at every fixed angular mode. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaActualCompletedRadialMain_eq_oai {r : Eisenstein} (hr : primary r)
    (W : ℝ → ℂ) {X : ℝ} (hX : 0<X) :
    cubicThetaActualCompletedRadialMain r W X=metaplecticMain r 0 W X := by
  simpa only [cubicThetaArithmeticBaseScalar_eq_one,star_one,mul_one] using
    cubicThetaActualCompletedRadialMain_mul_base hr W hX

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq_oai := @OAI.CubicFirstMoment.cubicThetaActualCompletedRadialMain_eq_oai
