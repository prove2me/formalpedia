-- Prove2me | solution 1 for OAI.CubicFirstMoment.hecke_zero_free_log_from_square_disk
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:22:49.206849+00:00
-- url     : https://prove2.me/submissions/710f4d29-a105-464d-8474-1dcf0e57548e

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A026

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeFunctionalEquation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebra of the published primitive Hecke functional equation.
The completion uses A = sqrt(3 D)/(2 pi), where D is the ideal conductor
norm. See Watkins (2011), Section 3.6, and Rajan (1998), Section 1,
pp. 281--283 for the fixed infinity-type completion. The uncompleted and symmetry-line identities follow from that exact equation. -/

noncomputable section
namespace CubicFirstMoment

theorem hecke_uncompleted {A k : ℝ} (hA : 0 < A) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hFE : HeckeFunctionalEquation A k ε L Ldual) (s : ℂ)
    (hG : Complex.Gamma (s+(k:ℂ)) ≠ 0)
    (hGdual : Complex.Gamma (1-s+(k:ℂ)) ≠ 0) :
    L s = ε*(A:ℂ)^(1-2*s) *
      (Complex.Gamma (1-s+(k:ℂ))/Complex.Gamma (s+(k:ℂ))) * Ldual (1-s) := by
  have ha : (A:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hap : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl ha)
  have hp : (A:ℂ)^s*(A:ℂ)^(1-2*s) = (A:ℂ)^(1-s) := by
    rw [← Complex.cpow_add _ _ ha]
    congr 1
    ring
  apply mul_left_cancel₀ (mul_ne_zero hap hG)
  calc
    _ = ε*((A:ℂ)^(1-s)*Complex.Gamma (1-s+(k:ℂ))*Ldual (1-s)) := hFE s hG hGdual
    _ = _ := by
      field_simp [hG]
      rw [← hp]
      rw [show (1-s*2:ℂ) = 1-2*s by ring]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularGamma
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The far-left Gamma quotient for a fixed angular parameter. Its two
arguments differ, after conjugation, by the integer `2m` independently
of the angular order. Possible Gamma poles are retained explicitly. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

private lemma angular_norm_ascPochhammer_le (n : ℕ) (z : ℂ) :
    ‖(ascPochhammer ℂ n).eval z‖ ≤ (‖z‖+(n:ℝ))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval,norm_mul]
      have hn : ‖z+(n:ℂ)‖ ≤ ‖z‖+(n:ℝ) := by
        simpa using norm_add_le z (n:ℂ)
      calc
        _ ≤ (‖z‖+(n:ℝ))^n*(‖z‖+(n:ℝ)) :=
          mul_le_mul ih hn (_root_.norm_nonneg _) (by positivity)
        _ = (‖z‖+(n:ℝ))^(n+1) := (pow_succ _ _).symm
        _ ≤ (‖z‖+((n+1:ℕ):ℝ))^(n+1) := by
          apply pow_le_pow_left₀ (by positivity)
          push_cast
          linarith

theorem norm_angular_gamma_left_ratio_le {k : ℝ} (hk : 0 ≤ k) (m : ℕ) (u : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(u:ℂ)*Complex.I) /
      Complex.Gamma ((1/2:ℂ)-(m:ℂ)+(k:ℂ)+(u:ℂ)*Complex.I)‖ ≤
        (k+3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m) := by
  let z : ℂ := (1/2:ℂ)-(m:ℂ)+(k:ℂ)+(u:ℂ)*Complex.I
  by_cases hG : Complex.Gamma z = 0
  · change ‖_ / Complex.Gamma z‖ ≤ _
    rw [hG,div_zero,norm_zero]
    positivity
  have hreg : ∀ n : ℕ, z ≠ -(n:ℂ) := by
    intro n hn
    apply hG
    rw [hn,Complex.Gamma_neg_nat_eq_zero]
  have he : ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(u:ℂ)*Complex.I) =
      starRingEnd ℂ (z+(2*m:ℕ)) := by
    dsimp [z]
    simp only [map_add,map_sub,map_mul,Complex.conj_ofReal,Complex.conj_I,
      map_natCast,map_div₀,map_one,map_ofNat]
    push_cast
    ring
  have hq := Complex.Gamma_add_nat_div_Gamma_eq (n := 2*m) z hreg
  have hn : ‖z‖ ≤ k+(m:ℝ)+1+|u| := by
    calc
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)+(k:ℂ)‖+‖(u:ℂ)*Complex.I‖ := norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)‖+‖(k:ℂ)‖+‖(u:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)‖+‖(m:ℂ)‖+‖(k:ℂ)‖+‖(u:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ _ := by simp [abs_of_nonneg hk]; linarith
  calc
    _ = ‖Complex.Gamma (z+(2*m:ℕ))/Complex.Gamma z‖ := by
      rw [he,Complex.Gamma_conj,norm_div,norm_div,Complex.norm_conj]
    _ = ‖(ascPochhammer ℂ (2*m)).eval z‖ := congrArg (fun w : ℂ => ‖w‖) hq
    _ ≤ (‖z‖+((2*m:ℕ):ℝ))^(2*m) := angular_norm_ascPochhammer_le _ _
    _ ≤ ((k+3*(m:ℝ)+1)*(1+|u|))^(2*m) := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      nlinarith [abs_nonneg u, show (0:ℝ) ≤ m by positivity]
    _ = _ := mul_pow _ _ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The short Möbius identity on Eisenstein ideals

Nonzero Eisenstein ideals are represented by their finite prime-ideal
exponent vectors. Their arithmetic functions form the multivariate power
series ring: its multiplication is exactly finite Dirichlet convolution.
The norm below is the norm of the product of prime representatives, so
the support statements retain the actual multiplicative ideal norm.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealZeta_mul_moebiusSeries : idealZeta * idealMoebiusSeries = 1 := by
  rw [mul_comm, idealMoebiusSeries_mul_zeta]

lemma idealZeta_mul_vonMangoldt : idealZeta * idealVonMangoldt = idealLogNorm := by
  rw [idealVonMangoldt, ← mul_assoc, idealZeta_mul_moebiusSeries, one_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DualPolynomialScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact `sqrt(Z/J)` normalization of a retained dual norm block.
The normalized coefficients are independent of the character conductor. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma positive_cpow_phase {x : ℝ} (hx : 0 < x) (σ u : ℝ) :
    (x:ℂ)^((σ:ℂ)+(u:ℂ)*Complex.I) = (x^σ:ℝ)*mellinPhase u x := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hx.le,Real.rpow_def_of_pos hx,Complex.ofReal_exp]
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealVonMangoldt
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.idealExponentCountable _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The convolution definition of ideal von Mangoldt has exactly its usual
prime-power coefficients. This is the arithmetic bridge for prime replacement
in the short Möbius decomposition. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma idealLogNorm_prime_difference (ν : EisensteinIdealExponent)
    (p : EisensteinIdealPrime) (hp : 1 ≤ ν p) :
    MvPowerSeries.coeff ν idealLogNorm -
        MvPowerSeries.coeff (ν - Finsupp.single p 1) idealLogNorm =
      Real.log (normNat (idealPrimeRepresentative p)) := by
  have hle : Finsupp.single p 1 ≤ ν := Finsupp.single_le_iff.mpr hp
  have he : ν = (ν - Finsupp.single p 1) + Finsupp.single p 1 :=
    (tsub_add_cancel_of_le hle).symm
  change Real.log (idealExponentNorm ν) -
    Real.log (idealExponentNorm (ν - Finsupp.single p 1)) = _
  conv_lhs => lhs; rw [he, idealExponentNorm_add]
  rw [Real.log_mul (idealExponentNorm_pos _).ne' (idealExponentNorm_pos _).ne',
    idealExponentNorm_single, pow_one]
  ring

private lemma coeff_logNorm_finite_nonempty (S : Finset EisensteinIdealPrime)
    (ν : EisensteinIdealExponent) (hS : S.Nonempty) (hν : S ⊆ ν.support) :
    MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius S) =
      if S.card = 1 then ∑ p ∈ S, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  induction S using Finset.induction_on generalizing ν with
  | empty => exact (Finset.not_nonempty_empty hS).elim
  | @insert p S hp ih =>
    have hνp : 1 ≤ ν p := Nat.one_le_iff_ne_zero.mpr
      (Finsupp.mem_support_iff.mp (hν (Finset.mem_insert_self _ _)))
    have he : idealLogNorm * finiteIdealMoebius (insert p S) =
        (idealLogNorm * finiteIdealMoebius S) * (1 - MvPowerSeries.X p) := by
      rw [finiteIdealMoebius, Finset.prod_insert hp]
      unfold finiteIdealMoebius
      ring
    rw [he, mul_sub, mul_one, map_sub, MvPowerSeries.X_def,
      MvPowerSeries.coeff_mul_monomial]
    simp only [Finsupp.single_le_iff, ite_eq_left hνp, mul_one]
    by_cases hSE : S = ∅
    · subst S
      simpa [finiteIdealMoebius] using idealLogNorm_prime_difference ν p hνp
    · have hS' : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSE
      have hνS : S ⊆ ν.support := fun q hq => hν (Finset.mem_insert_of_mem hq)
      have hνS' : S ⊆ (ν - Finsupp.single p 1 : EisensteinIdealExponent).support := by
        intro q hq
        apply Finsupp.mem_support_iff.mpr
        have hqp : q ≠ p := ne_of_mem_of_not_mem hq hp
        simpa [Finsupp.tsub_apply, hqp] using Finsupp.mem_support_iff.mp (hνS hq)
      rw [ih ν hS' hνS, ih _ hS' hνS', sub_self]
      have hc : (insert p S).card ≠ 1 := by
        rw [Finset.card_insert_of_notMem hp]
        have := Finset.card_pos.mpr hS'
        omega
      simp [hc]

lemma idealVonMangoldt_coeff_eq_finite (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      MvPowerSeries.coeff ν (idealLogNorm * finiteIdealMoebius ν.support) := by
  rw [idealVonMangoldt, mul_comm idealLogNorm, MvPowerSeries.coeff_mul,
    MvPowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hle : a.1 ≤ ν := by
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp ha]
    exact le_add_of_nonneg_right zero_le
  rw [coeff_idealMoebiusSeries_eq_finite ν.support a.1 (Finsupp.support_mono hle)]

/-- The von Mangoldt coefficient is supported precisely on prime-ideal
powers and has weight the logarithm of that prime-ideal norm. -/
lemma idealVonMangoldt_coeff (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt =
      if ν.support.card = 1 then
        ∑ p ∈ ν.support, Real.log (normNat (idealPrimeRepresentative p)) else 0 := by
  rw [idealVonMangoldt_coeff_eq_finite]
  by_cases hs : ν.support.Nonempty
  · exact coeff_logNorm_finite_nonempty _ _ hs (Finset.Subset.refl _)
  · have hz : ν = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs)
    subst ν
    simp only [Finsupp.support_zero, finiteIdealMoebius, Finset.prod_empty, mul_one,
      Finset.card_empty, Nat.zero_ne_one, ite_false, if_false]
    change Real.log (idealExponentNorm 0) = 0
    simp [idealExponentNorm, idealExponentGenerator]

lemma idealVonMangoldt_not_prime_power (ν : EisensteinIdealExponent)
    (hν : ν.support.card ≠ 1) :
    MvPowerSeries.coeff ν idealVonMangoldt = 0 := by
  rw [idealVonMangoldt_coeff, ite_eq_right hν]

lemma idealVonMangoldt_coeff_nonneg (ν : EisensteinIdealExponent) :
    0 ≤ MvPowerSeries.coeff ν idealVonMangoldt := by
  rw [idealVonMangoldt_coeff]
  split_ifs
  · apply Finset.sum_nonneg
    intro p hp
    apply Real.log_nonneg
    simpa only [idealExponentNorm_single, pow_one] using
      idealExponentNorm_ge_one (Finsupp.single p 1)
  · exact le_rfl

lemma idealVonMangoldt_coeff_le_logNorm (ν : EisensteinIdealExponent) :
    MvPowerSeries.coeff ν idealVonMangoldt ≤ Real.log (idealExponentNorm ν) := by
  by_cases hc : ν.support.card = 1
  · obtain ⟨p,hp,he⟩ := Finsupp.card_support_eq_one.mp hc
    have hlog : 0 ≤ Real.log (normNat (idealPrimeRepresentative p)) := by
      apply Real.log_nonneg
      simpa only [idealExponentNorm_single, pow_one] using
        idealExponentNorm_ge_one (Finsupp.single p 1)
    have hn : (1 : ℝ) ≤ (ν p : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp
    rw [idealVonMangoldt_coeff, ite_eq_left hc, he, Finsupp.support_single _ hp,
      Finset.sum_singleton, idealExponentNorm_single, Real.log_pow]
    exact le_mul_of_one_le_left hlog hn
  · rw [idealVonMangoldt_not_prime_power ν hc]
    exact Real.log_nonneg (idealExponentNorm_ge_one ν)

lemma idealVonMangoldt_coeff_abs_le_logNorm (ν : EisensteinIdealExponent) :
    |MvPowerSeries.coeff ν idealVonMangoldt| ≤ Real.log (idealExponentNorm ν) := by
  rw [abs_of_nonneg (idealVonMangoldt_coeff_nonneg ν)]
  exact idealVonMangoldt_coeff_le_logNorm ν

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSmoothDual
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! From the ordinary analytic properties of a primitive Hecke series
to a truncated smooth dual sum. The smooth-duality conclusion follows from the contour shift. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma mellinPhase_eq_cpow {x : ℝ} (hx : 0 < x) (t : ℝ) :
    mellinPhase t x = (x:ℂ)^((t:ℂ)*Complex.I) := by
  simpa only [Complex.ofReal_zero,zero_add,Real.rpow_zero,Complex.ofReal_one,one_mul]
    using (positive_cpow_phase hx 0 t).symm

lemma twisted_normDirichletSeries (χ : EisensteinIdealExponent → ℂ) (t : ℝ) (s : ℂ) :
    normDirichletSeries (fun ν => χ ν*mellinPhase t (idealExponentNorm ν)) idealExponentNorm s =
      normDirichletSeries χ idealExponentNorm (s-(t:ℂ)*Complex.I) := by
  apply tsum_congr
  intro ν
  dsimp only
  rw [mellinPhase_eq_cpow (idealExponentNorm_pos ν),mul_assoc,← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne')]
  congr 2
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialStrip
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial strip growth from finite order and polynomial boundary
bounds. The finite-order hypothesis is much weaker than the conclusion;
the proof uses the Phragmén–Lindelöf theorem in mathlib. -/

noncomputable section
open Set Filter Asymptotics
namespace CubicFirstMoment

lemma finiteVerticalOrder_double_exp {f : ℂ → ℂ} {a b c : ℝ}
    (hf : FiniteVerticalOrder f a b) (hc : 0 < c) :
    f =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b)]
      (fun z : ℂ => Real.exp (Real.exp (c*|z.im|))) := by
  obtain ⟨C,k,hC,hf⟩ := hf
  have he := ((isLittleO_pow_exp_pos_mul_atTop k hc).const_mul_left (C*2^k)).bound
    (by norm_num : (0:ℝ) < 1)
  have hlarge : ∀ᶠ u : ℝ in atTop,
      C*(1+u)^k ≤ Real.exp (c*u) := by
    filter_upwards [he,eventually_ge_atTop (1:ℝ)] with u hu hu1
    have hu0 : 0 ≤ u := le_trans zero_le_one hu1
    have hpow : (1+u)^k ≤ (2*u)^k := pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      C*(1+u)^k ≤ C*(2*u)^k := mul_le_mul_of_nonneg_left hpow hC
      _ = (C*2^k)*u^k := by rw [mul_pow]; ring
      _ ≤ Real.exp (c*u) := by
        exact (le_abs_self _).trans (by
          simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),one_mul] using hu)
  apply IsBigO.of_bound' 
  have hlarge' := ((tendsto_comap : Tendsto (abs ∘ Complex.im) (comap (abs ∘ Complex.im) atTop) atTop).eventually hlarge).filter_mono (inf_le_left :
    comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b) ≤
      comap (abs ∘ Complex.im) atTop)
  have hs : ∀ᶠ z : ℂ in comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Ioo a b), z.re ∈ Ioo a b :=
    Filter.Eventually.filter_mono inf_le_right (by simp)
  filter_upwards [hlarge',hs] with z hz hzstrip
  exact (hf z ⟨hzstrip.1.le,hzstrip.2.le⟩).trans <| by
    simpa using Real.exp_le_exp.mpr hz

private lemma strip_shift_norm_lower {a : ℝ} {z : ℂ} (hz : a ≤ z.re) :
    1 ≤ ‖z+((1-a:ℝ):ℂ)‖ := by
  have hr := Complex.re_le_norm (z+((1-a:ℝ):ℂ))
  simp only [Complex.add_re,Complex.ofReal_re] at hr
  linarith

private lemma strip_shift_norm_upper {a b : ℝ} {z : ℂ}
    (hz : z.re ∈ Icc a b) :
    ‖z+((1-a:ℝ):ℂ)‖ ≤ (b-a+1)*(1+|z.im|) := by
  have hn := Complex.norm_le_abs_re_add_abs_im (z+((1-a:ℝ):ℂ))
  simp only [Complex.add_re,Complex.ofReal_re,Complex.add_im,Complex.ofReal_im,add_zero] at hn
  rw [abs_of_nonneg (by linarith [hz.1] : 0 ≤ z.re+(1-a))] at hn
  nlinarith [abs_nonneg z.im,hz.1,hz.2]

/-- A finite-order holomorphic function with polynomial bounds on both
vertical edges has polynomial growth throughout the strip. -/
theorem polynomial_strip_of_finite_order {f : ℂ → ℂ} {a b C : ℝ}
    (hab : a < b) (hfd : Differentiable ℂ f) (hf : FiniteVerticalOrder f a b)
    (hC : 0 ≤ C) (n : ℕ)
    (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C*(1+|z.im|)^n)
    (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C*(1+|z.im|)^n) :
    ∀ z : ℂ, z.re ∈ Icc a b →
      ‖f z‖ ≤ (C*2^n*(b-a+1)^n)*(1+|z.im|)^n := by
  let g (z : ℂ) := f z/(z+((1-a:ℝ):ℂ))^n
  have hcl : closure (Complex.re ⁻¹' Ioo a b) ⊆ Complex.re ⁻¹' Icc a b := by
    apply closure_minimal
    · intro z hz
      exact ⟨hz.1.le,hz.2.le⟩
    · exact isClosed_Icc.preimage Complex.continuous_re
  have hne {z : ℂ} (hz : a ≤ z.re) : z+((1-a:ℝ):ℂ) ≠ 0 := by
    have hn := strip_shift_norm_lower hz
    intro he
    rw [he,norm_zero] at hn
    norm_num at hn
  have hgd : DiffContOnCl ℂ g (Complex.re ⁻¹' Ioo a b) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    exact (hfd z).differentiableWithinAt.div
      (((differentiable_id.add_const ((1-a:ℝ):ℂ)).pow n) z).differentiableWithinAt
      (pow_ne_zero _ (hne (hcl hz).1))
  have hgnorm {z : ℂ} (hz : a ≤ z.re) : ‖g z‖ ≤ ‖f z‖ := by
    dsimp [g]
    rw [norm_div,norm_pow]
    exact div_le_self (_root_.norm_nonneg _) (one_le_pow₀ (strip_shift_norm_lower hz))
  have hgf : FiniteVerticalOrder g a b := by
    obtain ⟨D,k,hD,hf⟩ := hf
    exact ⟨D,k,hD,fun z hz => (hgnorm hz.1).trans (hf z hz)⟩
  have hboundary {z : ℂ} (hz : z.re ∈ Icc a b)
      (hfz : ‖f z‖ ≤ C*(1+|z.im|)^n) : ‖g z‖ ≤ C*2^n := by
    have hn := strip_shift_norm_lower hz.1
    have hi : |z.im| ≤ ‖z+((1-a:ℝ):ℂ)‖ := by
      simpa using Complex.abs_im_le_norm (z+((1-a:ℝ):ℂ))
    have hpow : (1+|z.im|)^n ≤ (2*‖z+((1-a:ℝ):ℂ)‖)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    dsimp [g]
    rw [norm_div,norm_pow]
    apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hn) _)).mpr
    calc
      ‖f z‖ ≤ C*(1+|z.im|)^n := hfz
      _ ≤ C*(2*‖z+((1-a:ℝ):ℂ)‖)^n := mul_le_mul_of_nonneg_left hpow hC
      _ = _ := by rw [mul_pow]; ring
  have hc : 0 < Real.pi/(2*(b-a)) := div_pos Real.pi_pos (by linarith)
  have hcb : Real.pi/(2*(b-a)) < Real.pi/(b-a) := by
    apply div_lt_div_of_pos_left Real.pi_pos (by linarith) (by linarith)
  intro z hz
  have hg : ‖g z‖ ≤ C*2^n := PhragmenLindelof.vertical_strip hgd
    ⟨Real.pi/(2*(b-a)),hcb,1,by
      simpa only [one_mul] using finiteVerticalOrder_double_exp hgf hc⟩
    (fun w hw => hboundary ⟨hw.ge,hw ▸ hab.le⟩ (ha w hw))
    (fun w hw => hboundary ⟨hw ▸ hab.le,hw.le⟩ (hb w hw)) hz.1 hz.2
  have hfeq : ‖f z‖ = ‖g z‖*‖z+((1-a:ℝ):ℂ)‖^n := by
    dsimp [g]
    rw [norm_div,norm_pow,div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr (hne hz.1)))]
  rw [hfeq]
  calc
    _ ≤ (C*2^n)*((b-a+1)*(1+|z.im|))^n :=
      mul_le_mul hg (pow_le_pow_left₀ (_root_.norm_nonneg _) (strip_shift_norm_upper hz) n)
        (by positivity) (by positivity)
    _ = _ := by rw [mul_pow]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeStripGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial strip-growth field used by the Mellin proof follows
from finite order, absolute convergence, and the functional equation.
No polynomial strip bound is assumed in the input structure here. -/

noncomputable section
open Set
namespace CubicFirstMoment

lemma norm_idealDirichlet_le_zeta_two (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (s : ℂ) (hs : 2 ≤ s.re) :
    ‖normDirichletSeries χ idealExponentNorm s‖ ≤
      ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)) := by
  have hb := summable_ideal_norm_rpow (by norm_num : (1:ℝ) < 2)
  have hf (ν : EisensteinIdealExponent) :
      ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖ ≤ idealExponentNorm ν^(-(2:ℝ)) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg (idealExponentNorm_pos ν).le _) (hχ ν)).trans
      (Real.rpow_le_rpow_of_exponent_le (idealExponentNorm_ge_one ν) (neg_le_neg hs))
  have hfn : Summable (fun ν => ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖) :=
    hb.of_norm_bounded (fun ν => by simpa only [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)] using hf ν)
  exact (norm_tsum_le_tsum_norm hfn).trans (Summable.tsum_le_tsum hf hfn hb)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeGrowth
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial strip growth for the shifted completion Gamma(s+k).
The input is the ordinary entire order-one completion, expressed by a
coarse quadratic exponential bound. All strip bounds are derived. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma shifted_completed_hecke_decompletion {A k : ℝ} (hA : 0 < A)
    {L Λ : ℂ → ℂ} (hL : Continuous L) (hΛ : Continuous Λ)
    (heq : ∀ s : ℂ, Complex.Gamma (s+(k:ℂ)) ≠ 0 → Λ s = heckeCompleted A k L s) :
    L = fun s : ℂ => (A:ℂ)^(-s)*(Complex.Gamma (s+(k:ℂ)))⁻¹*Λ s := by
  have : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  apply Continuous.ext_on
    ((Set.countable_range (fun n : ℕ => -(n:ℂ)-(k:ℂ))).dense_compl ℂ)
    hL (((differentiable_const_cpow_of_neZero (A:ℂ)).continuous.comp continuous_neg).mul
      (Complex.differentiable_one_div_Gamma.continuous.comp
        (continuous_id.add continuous_const)) |>.mul hΛ)
  intro s hs
  have hG : Complex.Gamma (s+(k:ℂ)) ≠ 0 := Complex.Gamma_ne_zero (by
    intro n hn
    apply hs
    refine ⟨n,?_⟩
    linear_combination -hn)
  change L s = (A:ℂ)^(-s)*(Complex.Gamma (s+(k:ℂ)))⁻¹*Λ s
  rw [heq s hG,heckeCompleted,Complex.cpow_neg]
  have hAp : (A:ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (NeZero.ne _))
  field_simp

theorem shifted_completed_finiteVerticalOrder {A k : ℝ} (hA : 0 < A)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) {a b : ℝ}
    (hGamma : GammaInverseFiniteOrder (a+k) (b+k)) : FiniteVerticalOrder L a b := by
  obtain ⟨Λ,hΛ,heq,C,hC,hbound⟩ := hcomp
  obtain ⟨B,hB,hGamma⟩ := hGamma
  have hdec := shifted_completed_hecke_decompletion hA hL.continuous hΛ.continuous heq
  let R : ℝ := 1+|a|+|b|
  have hR : 1 ≤ R := by dsimp [R]; linarith [abs_nonneg a,abs_nonneg b]
  refine ⟨R*|Real.log A|+C*R^2+B,2,by positivity,?_⟩
  intro s hs
  have hreal : |s.re| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a,abs_nonneg b,hs.1]
    · linarith [le_abs_self b,abs_nonneg a,hs.2]
  have hn : 1+‖s‖ ≤ R*(1+|s.im|) := by
    have hn := Complex.norm_le_abs_re_add_abs_im s
    dsimp [R]
    nlinarith [abs_nonneg a,abs_nonneg b,abs_nonneg s.im]
  have hnsq : (1+‖s‖)^2 ≤ R^2*(1+|s.im|)^2 := by
    calc
      _ ≤ (R*(1+|s.im|))^2 := pow_le_pow_left₀ (by positivity) hn _
      _ = _ := mul_pow _ _ _
  have haexp : ‖(A:ℂ)^(-s)‖ ≤ Real.exp (R*|Real.log A|) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA,Complex.neg_re,Real.rpow_def_of_pos hA]
    apply Real.exp_le_exp.mpr
    calc
      Real.log A*(-s.re) ≤ |Real.log A*(-s.re)| := le_abs_self _
      _ = |Real.log A| *|s.re| := by rw [abs_mul,abs_neg]
      _ ≤ |Real.log A| *R := mul_le_mul_of_nonneg_left
        (hreal.trans (by dsimp [R]; linarith)) (abs_nonneg _)
      _ = _ := mul_comm _ _
  have hg : ‖(Complex.Gamma (s+(k:ℂ)))⁻¹‖ ≤ Real.exp (B*(1+|s.im|)^2) := by
    simpa using hGamma (s+(k:ℂ)) (by simpa using
      (show a+k ≤ s.re+k ∧ s.re+k ≤ b+k from
        ⟨by linarith [hs.1],by linarith [hs.2]⟩))
  have hp : 1 ≤ (1+|s.im|)^2 := one_le_pow₀ (by linarith [abs_nonneg s.im])
  rw [congrFun hdec s,norm_mul,norm_mul]
  calc
    _ ≤ Real.exp (R*|Real.log A|)*Real.exp (B*(1+|s.im|)^2)*
        Real.exp (C*(1+‖s‖)^2) :=
      mul_le_mul (mul_le_mul haexp hg (_root_.norm_nonneg _) (Real.exp_pos _).le)
        (hbound s) (_root_.norm_nonneg _) (by positivity)
    _ = Real.exp (R*|Real.log A|+B*(1+|s.im|)^2+C*(1+‖s‖)^2) := by
      rw [←Real.exp_add,←Real.exp_add]
    _ ≤ Real.exp ((R*|Real.log A|+C*R^2+B)*(1+|s.im|)^2) := by
      apply Real.exp_le_exp.mpr
      have h1 := mul_le_mul_of_nonneg_left hp (show 0 ≤ R*|Real.log A| by positivity)
      have h2 := mul_le_mul_of_nonneg_left hnsq hC
      nlinarith

lemma angular_hecke_left_boundary (χdual : EisensteinIdealExponent → ℂ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k)
    {ε : ℂ} {L Ldual : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hd : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s)
    {m : ℕ} (hm : 2 ≤ m) (u : ℝ) :
    ‖L ((1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I)‖ ≤
      (‖ε‖*A^(2*m)*(k+3*(m:ℝ)+1)^(2*m)*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))))*(1+|u|)^(2*m) := by
  let s : ℂ := (1/2:ℂ)-(m:ℂ)+(u:ℂ)*Complex.I
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  have hr : 2 ≤ (1-s).re := by dsimp [s]; simp; linarith
  have hS : 0 ≤ ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)) :=
    tsum_nonneg fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _
  by_cases hG : Complex.Gamma (s+(k:ℂ)) = 0
  · obtain ⟨Λ,hΛ,heq,-⟩ := hcomp
    have hdec := shifted_completed_hecke_decompletion hA hL.continuous hΛ.continuous heq
    change ‖L s‖ ≤ _
    rw [congrFun hdec s,hG,inv_zero,mul_zero,zero_mul,norm_zero]
    positivity
  have hGd : Complex.Gamma (1-s+(k:ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith
  have he := hecke_uncompleted hA hFE s hG hGd
  rw [hd _ (by linarith)] at he
  have hp : ‖(A:ℂ)^(1-2*s)‖ = A^(2*m) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have hre : (1-2*s).re = ((2*m:ℕ):ℝ) := by dsimp [s]; simp; ring
    rw [hre,Real.rpow_natCast]
  have hg : ‖Complex.Gamma (1-s+(k:ℂ))/Complex.Gamma (s+(k:ℂ))‖ ≤
      (k+3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m) := by
    have heq : 1-s+(k:ℂ) = (1/2:ℂ)+(m:ℂ)+(k:ℂ)-(u:ℂ)*Complex.I := by
      dsimp [s]
      ring
    have heq2 : s+(k:ℂ) = (1/2:ℂ)-(m:ℂ)+(k:ℂ)+(u:ℂ)*Complex.I := by
      dsimp [s]
      ring
    rw [heq,heq2]
    exact norm_angular_gamma_left_ratio_le hk m u
  change ‖L s‖ ≤ _
  rw [he,norm_mul,norm_mul,norm_mul,hp]
  calc
    _ ≤ (‖ε‖*A^(2*m))*((k+3*(m:ℝ)+1)^(2*m)*(1+|u|)^(2*m))*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hg (by positivity))
        (norm_idealDirichlet_le_zeta_two χdual hχdual (1-s) hr)
        (_root_.norm_nonneg _) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.Erdos970_PNT1_ComplexAnalysis
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


lemma real_part_of_diff (M : ℝ) (w : ℂ) : (2 * M - w).re = 2 * M - w.re := by
  simp [Complex.sub_re]

lemma real_part_of_diffz (M : ℝ) (f_z : ℂ) : (2 * M - f_z).re = 2 * M - f_z.re := real_part_of_diff M f_z

lemma inequality_reversal (x M : ℝ) (hxM : x ≤ M) : 2 * M - x ≥ M := by linarith

lemma real_part_lower_bound (w : ℂ) (M : ℝ) (_hM : M > 0) (h : w.re ≤ M) : 2 * M - w.re ≥ M := by apply inequality_reversal w.re M h

lemma real_part_lower_bound3 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w).re > 0 := by
  rw [real_part_of_diffz]
  apply lt_of_le_of_lt'
  apply real_part_lower_bound
  exact hM
  exact h
  exact hM

lemma nonzero_if_real_part_positive (w : ℂ) (hw_re_pos : w.re > 0) : w ≠ 0 := by
  by_contra h
  rw [h] at hw_re_pos
  exact lt_irrefl 0 hw_re_pos

lemma lem_real_part_lower_bound4 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w) ≠ 0 := by
  apply nonzero_if_real_part_positive
  exact real_part_lower_bound3 w M hM h

lemma lem_abspos (z : ℂ) : z ≠ 0 → norm z > 0 := by
  intro h_ne_zero
  apply Real.sqrt_pos.mpr
  exact Complex.normSq_pos.mpr h_ne_zero

lemma lem_real_part_lower_bound5 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : norm (2 * M - w) > 0 := by
  apply lem_abspos
  exact lem_real_part_lower_bound4 w M hM h

lemma lem_modulus_sq_ReImw (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := by
  simp_rw [Complex.sq_norm]
  simp_rw [Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma lem_modulus_sq_identity (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := lem_modulus_sq_ReImw M w

lemma lem_nonnegative_product (M x : ℝ) (hM : M > 0) (hxM : x ≤ M) : 4 * M * (M - x) ≥ 0 := by
  have h_four_M_nonneg : 4 * M ≥ 0 := by linarith [hM]
  have h_diff_nonneg : M - x ≥ 0 := by linarith [hxM]
  apply mul_nonneg h_four_M_nonneg h_diff_nonneg

lemma lem_nonnegative_product2 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : 4 * M * (M - w.re) ≥ 0 := by
  apply lem_nonnegative_product
  exact hM
  exact hw_re_le_M

lemma lem_nonnegative_product3 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 - norm w ^ 2 ≥ 0 := by
  rw [lem_modulus_sq_identity]
  apply lem_nonnegative_product2
  exact hM
  exact hw_re_le_M

lemma lem_nonnegative_product4 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 ≥ norm w ^ 2 := by
  have h := lem_nonnegative_product3 M w hM hw_re_le_M
  linarith

lemma lem_nonnegative_product5 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ≥ norm w := by
  have h_sq_ge : ‖2 * M - w‖ ^ 2 ≥ ‖w‖ ^ 2 := by
    apply lem_nonnegative_product4 M w hM hw_re_le_M
  rw [ge_iff_le] at h_sq_ge                                                

  apply (sq_le_sq₀ (norm_nonneg w) (norm_nonneg (2 * M - w))).mp
  exact h_sq_ge

lemma lem_nonnegative_product6 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm w ≤ norm (2 * M - w) := by apply lem_nonnegative_product5 M w hM hw_re_le_M

lemma lem_ineqmultr (a b c : ℝ) (hc : c > 0) (_ha : 0 ≤ a) (hab : a ≤ b) : a / c ≤ b / c := by
  apply div_le_div_of_nonneg_right
  exact hab
  linarith [hc]

lemma lem_ineqmultrbb (a b : ℝ) (hb : b > 0) (ha : 0 ≤ a) (hab : a ≤ b) : a / b ≤ 1 := by
  have h := lem_ineqmultr a b b hb ha hab
  rw [div_self (ne_of_gt hb)] at h
  exact h

lemma lem_nonnegative_product7 (M : ℝ) (w : ℂ) (_hM : M > 0) (h_abs_diff_pos : norm (2 * M - w) > 0) (h_abs_le_abs_diff : norm w ≤ norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 := by
                                                                                   
  have h_abs_w_nonneg : 0 ≤ ‖w‖ := norm_nonneg w

  apply lem_ineqmultrbb
  exact h_abs_diff_pos
  exact h_abs_w_nonneg
  exact h_abs_le_abs_diff

lemma lem_nonnegative_product8 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) (h_abs_le_abs_diff : norm w ≤
norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 := by
  apply lem_nonnegative_product7 M w
  exact hM
  apply lem_real_part_lower_bound5 w M hM hw_re_le_M
  exact h_abs_le_abs_diff

lemma lem_nonnegative_product9 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm w / norm (2 * M - w) ≤ 1 := by
  apply lem_nonnegative_product8
  exact hM
  exact hw_re_le_M
  apply lem_nonnegative_product6
  exact hM
  exact hw_re_le_M

lemma lem_triangle_ineq (N G : ℂ) : norm (N + G) ≤ norm N + norm G := by
  exact norm_add_le N G

lemma lem_triangleineqminus (N F : ℂ) : norm (N - F) ≤ norm N + norm F := by
  rw [sub_eq_add_neg]
  calc
    ‖N + (-F)‖ ≤ ‖N‖ + ‖-F‖ := by apply lem_triangle_ineq
    _ = ‖N‖ + ‖F‖ := by rw [norm_neg]

lemma lem_rtriangle (r : ℝ) (N F : ℂ) (hr : r > 0) : r * norm (N - F) ≤ r * (norm N + norm F) := by
  apply mul_le_mul_of_nonneg_left
  apply lem_triangleineqminus
  linarith

lemma rtriangle2 (r : ℝ) (N F : ℂ) (hr : r > 0) : r * norm (N - F) ≤ r * norm N + r * norm F := by
  have h := lem_rtriangle r N F hr
  linarith [h]

lemma lem_rtriangle3 (r R : ℝ) (N F : ℂ) (hr : r > 0) (_hR : r < R) (h : R * norm F ≤ r * norm (N - F)) : R * norm F ≤ r * norm N + r * norm F := by
  calc
    R * norm F ≤ r * norm (N - F) := by exact h
    _ ≤ r * norm N + r * norm F := by apply rtriangle2 r N F hr

lemma lem_rtriangle4 (r R : ℝ) (N F : ℂ) (hr : 0 < r) (hR : r < R) (h_hyp : R * norm F ≤ r * norm (N - F)) : (R - r) * norm F ≤ r * norm N := by
  have h_result_from_lem3 : R * norm F ≤ r * norm N + r * norm F := by
    apply lem_rtriangle3 r R N F hr hR h_hyp
  linarith [h_result_from_lem3]

lemma lem_rtriangle5 (r R M : ℝ) (F : ℂ) (hr : 0 < r) (hrR : r < R) (hM : M > 0)
    (h_hyp : R * norm F ≤ r * norm (2 * M - F)) :
(R - r) * norm F ≤ 2 * M * r := by
                                        
  have h1 : (R - r) * norm F ≤ r * norm (2 * M : ℂ) :=
    lem_rtriangle4 r R (2 * M : ℂ) F hr hrR h_hyp

  have h2 : norm (2 * M : ℂ) = 2 * M := by

    have h_pos : (2 * M : ℝ) > 0 := by linarith [hM]
                                                                        
    convert (preTransparency := .instances) Complex.norm_of_nonneg (le_of_lt h_pos) using 1
                                                             
    norm_cast
                             
  rw [h2] at h1
                                     
  rw [mul_comm r (2 * M)] at h1
  exact h1

lemma lem_RrFpos (r R : ℝ) (F : ℂ) (_hr : 0 < r) (hrR : r < R) : (R - r) * norm F ≥ 0 := by
  have h_R_minus_r_nonneg : R - r ≥ 0 := by linarith [hrR]
  have h_abs_F_nonneg : 0 ≤ norm F := by apply norm_nonneg
  apply mul_nonneg h_R_minus_r_nonneg h_abs_F_nonneg

lemma lem_rtriangle6 (r R M : ℝ) (F : ℂ) (hr : 0 < r) (hrR : r < R) (_hM : M > 0)
    (h_hyp : (R - r) * norm F ≤ 2 * M * r) :
norm F ≤ (2 * M * r) / (R - r) := by
  have h_R_minus_r_pos : R - r > 0 := by linarith [hrR]
  have h_numerator_nonneg : 0 ≤ (R - r) * ‖F‖ := by apply lem_RrFpos r R F hr hrR
                                                                          
  have h_ineq_with_denominators : ( (R - r) * ‖F‖ ) / (R - r) ≤ (2 * M * r) / (R - r) := by
    apply lem_ineqmultr
    exact h_R_minus_r_pos          
    exact h_numerator_nonneg          
    exact h_hyp          
                                                                        
  rw [mul_div_cancel_left₀ (‖F‖) (ne_of_gt h_R_minus_r_pos)] at h_ineq_with_denominators
                                                     
  exact h_ineq_with_denominators

lemma lem_rtriangle7 (r R M : ℝ) (F : ℂ)
    (hr : 0 < r) (hrR : r < R) (hM : M > 0)
    (h_hyp : R * norm F ≤ r * norm (2 * M - F)) :
norm F ≤ (2 * M * r) / (R - r) := by
  have h_step1 := lem_rtriangle5 r R M F hr hrR hM h_hyp
  apply lem_rtriangle6 r R M F hr hrR hM h_step1

theorem analyticWithinAt_to_analyticAt_aux {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ} (_hS : S ∈ nhds z)
  (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : ENNReal) (_h_conv_on_inter : r ≤ p.radius) (_hr_pos : 0 < r)
  (hasSumt : ∀ {y : ℂ}, z + y ∈ insert z S → y ∈ Metric.eball 0 r → HasSum (fun n => (p n) fun _x => y) (f (z + y)))
  (ε : ℝ) (hε_pos : ε > 0) (h_ball_subset_S : Metric.ball z ε ⊆ S) :
  let r' := min r (ENNReal.ofReal ε);
  ∀ {y : ℂ}, y ∈ Metric.eball 0 r' → HasSum (fun n => (p n) fun _x => y) (f (z + y)) := by
  intro r' y hy
  apply hasSumt
  ·                            

    right                                              
    apply h_ball_subset_S
    rw [Metric.mem_ball]
                                      
    simp
                               
    have : y ∈ Metric.eball 0 (ENNReal.ofReal ε) := by
      apply Metric.eball_subset_eball (min_le_right r (ENNReal.ofReal ε)) hy

    have ε_nn : ENNReal.ofReal ε = ↑(ε.toNNReal) := by
      simp [ENNReal.ofReal]
    rw [ε_nn] at this
    rw [@Metric.eball_coe] at this
    simpa [Metric.mem_ball, dist_self_add_right, Real.toNNReal_of_nonneg hε_pos.le]

  ·                              
    exact Metric.eball_subset_eball (min_le_left r (ENNReal.ofReal ε)) hy

theorem analyticWithinAt_to_analyticAt {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ}
    (hS : S ∈ nhds z) (h : AnalyticWithinAt ℂ f S z) : AnalyticAt ℂ f z := by
  rcases h with ⟨p, hp⟩

  use p

  rcases hp with ⟨r, h_conv_on_inter, hr_pos⟩

  rcases Metric.mem_nhds_iff.mp hS with ⟨ε, hε_pos, h_ball_subset_S⟩

  let r' := min r (ENNReal.ofReal ε)
  use r'

  constructor

  · exact inf_le_of_left_le h_conv_on_inter

  ·
    exact lt_min hr_pos (ENNReal.ofReal_pos.mpr hε_pos)
  rename_i hasSumt
  exact analyticWithinAt_to_analyticAt_aux hS p r h_conv_on_inter hr_pos hasSumt ε hε_pos h_ball_subset_S

lemma lem_1zanalDR (R : ℝ) (_hR_pos : 0 < R) :
    AnalyticOn ℂ (fun z ↦ z⁻¹) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by

  apply AnalyticOn.mono (analyticOn_inv)
                                                     
  intro z hz
                                                       
  exact hz.2

lemma lem_analprod {T : Set ℂ} {f1 f2 : ℂ → ℂ} (hf1 : AnalyticOn ℂ f1 T) (hf2 : AnalyticOn ℂ f2 T) :
    AnalyticOn ℂ (f1 * f2) T := by
  exact hf1.mul hf2

lemma lem_fzzTanal {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
                          
  rw [show (fun z ↦ f z / z) = (fun z ↦ f z) * (fun z ↦ z⁻¹) by ext; simp [div_eq_mul_inv]]
                                
  let T := {z : ℂ | norm z ≤ R ∧ z ≠ 0}
                                                            
  have hf_on_T : AnalyticOn ℂ f T := hf.mono (?_)
                         
  have h_inv_on_T : AnalyticOn ℂ (fun z ↦ z⁻¹) T := lem_1zanalDR R hR_pos
                                                                
  exact lem_analprod hf_on_T h_inv_on_T
  intro z hz
  have hT : T = {z | norm z ≤ R ∧ z ≠ 0} := rfl
  rw [hT] at hz
  simp only [Set.mem_ofPred_eq] at hz
  simp only [Metric.mem_closedBall]
  simp only [dist_zero_right]
  exact hz.1

lemma lem_AnalOntoWithin {V : Set ℂ} {h : ℂ → ℂ} (hh : AnalyticOn ℂ h V) (z : ℂ) (hz : z ∈ V) :
    AnalyticWithinAt ℂ h V z := by
  exact hh z hz

lemma lem_DR0T {R : ℝ} (hR : 0 < R) :
    Metric.closedBall 0 R = {0} ∪ {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
  ext z
  simp [Metric.closedBall, dist_zero_right]
  by_cases hz : z = 0
  · simp [hz, hR.le]
  · simp [hz]

lemma lem_analWWWithin {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    (AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0) →
    (∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) →
    (∀ z ∈ Metric.closedBall 0 R, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) := by
  intro h0 hT z hz
  rw [lem_DR0T hR_pos] at hz
  cases' hz with hz hz
  · simp at hz
    rw [hz]
    exact h0
  · exact hT z hz

lemma lem_analWWithinAtOn (R : ℝ) (hR_pos : 0 < R) (h : ℂ → ℂ)
    (h_at_0 : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0)
    (h_at_T : ∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) :
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  exact lem_analWWWithin hR_pos h h_at_0 h_at_T

lemma lem_AnalAttoWithin {h : ℂ → ℂ} {s : Set ℂ} (hh : AnalyticAt ℂ h 0) :
    AnalyticWithinAt ℂ h s 0 := by
  exact hh.analyticWithinAt

lemma analyticWithinAt_punctured_to_closedBall {R : ℝ} (_hR : 0 < R) {h : ℂ → ℂ} {z : ℂ} (hz : z ∈ {w : ℂ | norm w ≤ R ∧ w ≠ 0}) (h_within : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z) : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z := by
                                                                                                                   
  apply AnalyticWithinAt.mono_of_mem_nhdsWithin h_within

  have hz_ne_zero : z ≠ 0 := hz.2

  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]

  use Metric.ball z (‖z‖ / 2)

  constructor
  ·                                      
    exact Metric.ball_mem_nhds z (half_pos (norm_pos_iff.mpr hz_ne_zero))

  ·                                                                                       
    intro w hw
    constructor
    ·                   
      have w_in_closedball : w ∈ Metric.closedBall 0 R := hw.2
      simp only [Metric.mem_closedBall, dist_zero_right] at w_in_closedball
                                           
      simp [w_in_closedball]
    ·              
      intro hw_eq_zero
      have w_in_ball : w ∈ Metric.ball z (‖z‖ / 2) := hw.1
      rw [hw_eq_zero] at w_in_ball
      simp only [Metric.mem_ball] at w_in_ball

      rw [dist_comm] at w_in_ball
      simp at w_in_ball
      have pos_norm : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne_zero
      linarith [pos_norm]

lemma lem_analAtOnOn {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    AnalyticAt ℂ h 0 →
    AnalyticOn ℂ h {z : ℂ | norm z ≤ R ∧ z ≠ 0} →
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  intro h_at_0 h_on_punctured

  apply lem_analWWithinAtOn R hR_pos h

  · exact lem_AnalAttoWithin h_at_0

  · intro z hz
                                                       
    have h_within_punctured : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z :=
      lem_AnalOntoWithin h_on_punctured z hz
                                     
    exact analyticWithinAt_punctured_to_closedBall hR_pos hz h_within_punctured

lemma lem_orderne0 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) :
    analyticOrderAt f 0 ≠ 0 := by exact (AnalyticAt.analyticOrderAt_ne_zero hf).mpr hf0

lemma lem_ordernetop (f : ℂ → ℂ) (_hf : AnalyticAt ℂ f 0) (hf_ne_zero : ¬(∀ᶠ z in nhds 0, f z = 0)) :
    analyticOrderAt f 0 ≠ ⊤ := by
  intro h
  rw [analyticOrderAt_eq_top] at h
  exact hf_ne_zero h

lemma lem_ordernatcast (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) (hn : analyticOrderAt f 0 = n) :
    ∃ (g : ℂ → ℂ), AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧ ∀ᶠ (z : ℂ) in nhds 0, f z = z ^ n * g z := by

  rw [AnalyticAt.analyticOrderAt_eq_natCast] at hn
  · convert (preTransparency := .instances) hn
    aesop
  · exact hf

lemma lem_ordernatcast1 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) (hn : analyticOrderAt f 0 = n) (hn_ne_zero : n ≠ 0) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
                           
  rcases lem_ordernatcast f hf n hn with ⟨g, hg_analytic, _, hf_eq_g⟩
                              
  use fun z ↦ z ^ (n - 1) * g z
  constructor
  ·                                                    
    exact (analyticAt_id.pow (n - 1)).mul hg_analytic
  ·                        
    filter_upwards [hf_eq_g] with z h_eq
    rw [h_eq]
    ring_nf
    rw [← pow_succ' z (n - 1), Nat.sub_add_cancel (Nat.pos_of_ne_zero hn_ne_zero)]

lemma lem_ordernatcast2_old (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (h_not_eventually_zero : ¬ (∀ᶠ z in nhds 0, f z = 0)) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
                                 
  let n₀ := analyticOrderAt f 0
                                                                        
  have hn_ne_top : n₀ ≠ ⊤ := lem_ordernetop f hf h_not_eventually_zero
                                             
  lift n₀ to ℕ using hn_ne_top with n hn_eq
                                                  
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    rw [hn_zero] at hn_eq

    have t := (lem_orderne0 f hf hf0)
    have : n₀ = analyticOrderAt f 0 := rfl
    rw [←this] at t
    exact t (id (Eq.symm hn_eq))
                                                                       
  exact lem_ordernatcast1 f hf n (by aesop) hn_ne_zero

lemma lem_ordernatcast2 {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ) (hf0 : f 0 = 0)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticAt ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) 0 := by
                                                                            
  have hS : Metric.closedBall 0 R ∈ nhds (0 : ℂ) := by
                                                              
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hR_pos) ?subset
    exact Metric.ball_subset_closedBall
  have hf_within : AnalyticWithinAt ℂ f (Metric.closedBall 0 R) 0 := hf 0 (by
    simp [Metric.mem_closedBall, hR_pos.le])
  have hf_at0 : AnalyticAt ℂ f 0 := analyticWithinAt_to_analyticAt hS hf_within

  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  by_cases hEZ : (∀ᶠ z in nhds (0 : ℂ), f z = 0)
  ·                                                                                          
                                          
    have hU : {z : ℂ | f z = 0} ∈ nhds (0 : ℂ) := by simpa only [Filter.Eventually] using hEZ
                                        
    have hf_eq_zero : f =ᶠ[nhds (0 : ℂ)] (fun _ : ℂ => 0) := by
      refine (Filter.eventuallyEq_iff_exists_mem).2 ?_
      exact ⟨{z | f z = 0}, hU, by intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
                                                                    
    have h_fderiv_zero : (fderiv ℂ f 0) = 0 := by
      simpa using (Filter.EventuallyEq.fderiv_eq hf_eq_zero)

    have h_g_zero_on_U : ∀ z ∈ {z : ℂ | f z = 0}, g z = 0 := by
      intro z hzU
      by_cases hz0 : z = 0
      ·                                  
        simp [g, hz0, h_fderiv_zero]
      ·                                  
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hzU
        simp [g, hz0, this]
                                                                                  
    have h_const0_within : AnalyticWithinAt ℂ (fun _ : ℂ => (0 : ℂ)) {z : ℂ | f z = 0} 0 :=
      analyticAt_const.analyticWithinAt
    have h_g_within : AnalyticWithinAt ℂ g {z : ℂ | f z = 0} 0 := by
                                        
      apply h_const0_within.congr
      intro z hz
      by_cases hz0 : z = 0
      ·        
        simp [g, hz0, h_fderiv_zero]
      ·             
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hz
        simp [g, hz0, this]
                           
      simp [g, h_fderiv_zero]
    exact analyticWithinAt_to_analyticAt hU h_g_within

  ·                                                                
    have h_notEZ : ¬ (∀ᶠ z in nhds (0 : ℂ), f z = 0) := hEZ
                                                        
    rcases lem_ordernatcast2_old f hf_at0 hf0 h_notEZ with ⟨h0, h0_at0, hfac_ev⟩
                                                               
    have hV : {z : ℂ | f z = z * h0 z} ∈ nhds (0 : ℂ) := by simpa only [Filter.Eventually] using hfac_ev
    have h_eq_nhds : f =ᶠ[nhds (0 : ℂ)] (fun z => z * h0 z) :=
      (Filter.eventuallyEq_iff_exists_mem).2 ⟨{z : ℂ | f z = z * h0 z}, hV, by
        intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
                              
    have h_fderiv_prod : fderiv ℂ f 0 = fderiv ℂ (fun z => z * h0 z) 0 :=
      Filter.EventuallyEq.fderiv_eq h_eq_nhds
                                                                              
    have h_diff_id : DifferentiableAt ℂ (fun z : ℂ => z) 0 := differentiableAt_id
    have h_diff_h0 : DifferentiableAt ℂ h0 0 := h0_at0.differentiableAt
                             
    have h_val0 : (fderiv ℂ f 0) 1 = h0 0 := by
                                                           
      rw [h_fderiv_prod]
      rw [fderiv_fun_mul' h_diff_id h_diff_h0]
      simp only [add_apply, smul_apply]
      rw [fderiv_fun_id]
      simp only [ContinuousLinearMap.id_apply]
      simp only [zero_smul, zero_add]
      simp

    have h_geq_h0_on_V : ∀ z ∈ {z : ℂ | f z = z * h0 z}, g z = h0 z := by
      intro z hzU
      by_cases hz0 : z = 0
      ·        
        simpa [g, hz0] using h_val0
      ·                                    
        have : f z = z * h0 z := by simpa [Set.mem_ofPred_eq] using hzU
        simp only [g, if_neg hz0, this]
        exact mul_div_cancel_left₀ (h0 z) hz0
                                                                    
    have h0_within : AnalyticWithinAt ℂ h0 {z : ℂ | f z = z * h0 z} 0 := h0_at0.analyticWithinAt
    have hg_within : AnalyticWithinAt ℂ g {z : ℂ | f z = z * h0 z} 0 := by

      apply AnalyticWithinAt.congr h0_within
                                 
      intro z hz
      exact h_geq_h0_on_V z hz

      have h_0_in_V : (0 : ℂ) ∈ {z : ℂ | f z = z * h0 z} := by
        simp [hf0]
      exact h_geq_h0_on_V 0 h_0_in_V
    exact analyticWithinAt_to_analyticAt hV hg_within

lemma lem_ballDR (R : ℝ) (hR : R > 0) : closure (ballDR R) = Metric.closedBall (0 : ℂ) R := by
  unfold ballDR
  exact closure_ball 0 (ne_of_gt hR)

lemma lem_inDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw : w ∈ closure (ballDR R)) : norm w ≤ R := by
  rw [lem_ballDR R hR] at hw
  rw [Metric.mem_closedBall] at hw
  rw [Complex.dist_eq] at hw
  simp at hw
  exact hw

lemma lem_notinDR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw : w ∉ ballDR R) : norm w ≥ R := by
                               
  unfold ballDR at hw
                                                   
  rw [Metric.mem_ball] at hw
                                                              
  push Not at hw
                                                                     
  rw [Complex.dist_eq] at hw
                       
  simp at hw
  exact hw

lemma lem_legeR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw1 : norm w ≤ R) (hw2 : norm w ≥ R) : norm w = R := by
  linarith

lemma lem_circleDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw1 : w ∈ closure (ballDR R)) (hw2 : w ∉ ballDR R) : norm w = R := by
  have h1 : norm w ≤ R := lem_inDR R hR w hw1
  have h2 : norm w ≥ R := lem_notinDR R hR w hw2
  exact lem_legeR R hR w h1 h2

lemma lem_Rself (R : ℝ) (hR : R > 0) : |R| = R := by
  rw [abs_eq_self]
  linarith

lemma lem_Rself2 (R : ℝ) (hR : R > 0) : |R| ≤ R := by
  rw [lem_Rself R hR]

lemma lem_Rself3 (R : ℝ) (hR : R > 0) : (R : ℂ) ∈ closure (ballDR R) := by
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  simp
  exact lem_Rself2 R hR

lemma lem_DRcompact (R : ℝ) (hR : R > 0) : IsCompact (closure (ballDR R)) := by
  rw [lem_ballDR R hR]
  apply Metric.isCompact_of_isClosed_isBounded
  · exact Metric.isClosed_closedBall
  · exact Metric.isBounded_closedBall

lemma lem_ExtrValThm {K : Set ℂ} (hK : IsCompact K) (hK_nonempty : K.Nonempty) (g : K → ℂ) (hg : Continuous g) :
∃ v : K, ∀ z : K, norm (g z) ≤ norm (g v) := by
                                       
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
                            
  have : Nonempty K := hK_nonempty.to_subtype
                                                             
  let f : K → ℝ := fun z => norm (g z)
                                
  have hf_cont : Continuous f := continuous_norm.comp hg
                                                       
  obtain ⟨v, hv_mem, hv_max⟩ := IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty hf_cont.continuousOn
  use v
  intro z
  exact hv_max (Set.mem_univ z)

lemma lem_ExtrValThmDR (R : ℝ) (hR : R > 0) (g : closure (ballDR R) → ℂ) (hg : Continuous g) :
∃ v : closure (ballDR R), ∀ z : closure (ballDR R), norm (g z) ≤ norm (g v) := by
                                                     
  have hK_compact : IsCompact (closure (ballDR R)) := lem_DRcompact R hR
                                             
  have hK_nonempty : (closure (ballDR R)).Nonempty := by
    rw [lem_ballDR R hR]
    rw [Metric.nonempty_closedBall]
    linarith
                                    
  exact lem_ExtrValThm hK_compact hK_nonempty g hg

lemma lem_AnalCont {R : ℝ} (_hR : R > 0) (H : ℂ → ℂ) (h_analytic : AnalyticOn ℂ H (closure (ballDR R))) :
Continuous (H ∘ (Subtype.val : closure (ballDR R) → ℂ)) := by
                                                                    
  have h_cont_on : ContinuousOn H (closure (ballDR R)) := AnalyticOn.continuousOn h_analytic
                              
  have h_val_cont : Continuous (Subtype.val : closure (ballDR R) → ℂ) := continuous_subtype_val

  exact ContinuousOn.comp_continuous h_cont_on h_val_cont (fun _ => Subtype.mem _)

lemma lem_ExtrValThmh {R : ℝ} (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ u : closure (ballDR R), ∀ z : closure (ballDR R), norm (h u) ≥ norm (h z) := by
                                                    
  have hg_continuous : Continuous (h ∘ Subtype.val : closure (ballDR R) → ℂ) :=
    lem_AnalCont hR h h_analytic
                                              
  obtain ⟨v, hv⟩ := lem_ExtrValThmDR R hR (h ∘ Subtype.val) hg_continuous
                   
  use v
                                        
  intro z
  have : norm ((h ∘ Subtype.val) z) ≤ norm ((h ∘ Subtype.val) v) := hv z
                             
  simp [Function.comp] at this
  exact this

lemma lem_MaxModP (R : ℝ) (_hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) := by
                                                             
  have h_preconnected : IsPreconnected (ballDR R) := by
    unfold ballDR
    apply Convex.isPreconnected
    exact convex_ball (0 : ℂ) R

  have h_open : IsOpen (ballDR R) := by
    unfold ballDR
    exact Metric.isOpen_ball

  have h_diff_cont : DiffContOnCl ℂ h (ballDR R) := by
    constructor
    ·                                   
      apply AnalyticOn.differentiableOn
      exact h_analytic.mono subset_closure
    ·                                         
      exact AnalyticOn.continuousOn h_analytic

  have h_max_on : IsMaxOn (norm ∘ h) (ballDR R) w := by
    intro z hz
    change ‖h z‖ ≤ ‖h w‖
    exact hw_max z hz

  have h_eq := Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn h_preconnected h_open h_diff_cont hw_in_DR h_max_on

  intro z hz
  have norm_eq := h_eq hz
  simp only [Function.comp_apply, Function.const_apply] at norm_eq
                                                                                   
  convert (preTransparency := .instances) norm_eq

lemma lem_MaxModR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : norm (h R) = norm (h w) := by
                                                                
  have h_const : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) :=
    lem_MaxModP R hR h h_analytic w hw_in_DR hw_max
                                                      
  have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
                                         
  exact h_const (R : ℂ) hR_in_closure

lemma lem_MaxModRR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) :
∀ z ∈ closure (ballDR R), norm (h R) ≥ norm (h z) := by
  intro z hz
                                                                            
  have h1 := lem_MaxModP R hR h h_analytic w hw_in_DR hw_max z hz
                                             
  have h2 := lem_MaxModR R hR h h_analytic w hw_in_DR hw_max
                                                                             
  rw [h2, h1]

theorem lem_MaxModv2 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : closure (ballDR R), norm (v : ℂ) = R ∧ ∀ z : closure (ballDR R), norm (h (v : ℂ)) ≥ norm (h (z : ℂ)) := by
                                                       
  obtain ⟨u, hu⟩ := lem_ExtrValThmh hR h h_analytic

  if h_case : (u : ℂ) ∈ ballDR R then
                                 
    have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
    let v : closure (ballDR R) := ⟨R, hR_in_closure⟩
    use v
    constructor
    ·                
                                                                             
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                                               
      have : norm (R : ℂ) = abs R := by
        simp [Complex.norm_real]
      rw [this, lem_Rself R hR]
    ·                                                     
      intro z
                                                                        
      have hw_max : ∀ w ∈ ballDR R, norm (h w) ≤ norm (h (u : ℂ)) := by
        intro w hw
                                                      
        have hw_closure : w ∈ closure (ballDR R) := subset_closure hw
                                              
        let w_sub : closure (ballDR R) := ⟨w, hw_closure⟩
        exact hu w_sub
                                             
      have h_result := lem_MaxModRR R hR h h_analytic (u : ℂ) h_case hw_max
                                                  
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                           
      exact h_result (z : ℂ) (Subtype.mem z)
  else
                                 
    use u
    constructor
    ·                                   
      exact lem_circleDR R hR (u : ℂ) (Subtype.mem u) h_case
    ·                                                                  
      exact hu

theorem lem_MaxModv3 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : ℂ, norm v = R ∧ ∀ z : ℂ, z ∈ closure (ballDR R) → norm (h v) ≥ norm (h z) := by
                                                                                   
  obtain ⟨v_sub, hv_abs, hv_max⟩ := lem_MaxModv2 R hR h h_analytic
                                                           
  let v := (v_sub : ℂ)
  use v
  constructor
  ·                
    exact hv_abs
  ·                            
    intro z hz
                                               
    have hz_sub : z ∈ closure (ballDR R) := hz
    let z_sub : closure (ballDR R) := ⟨z, hz_sub⟩
    have := hv_max z_sub
                             
    simp at this
    exact this

lemma lem_MaxModv4 (R B : ℝ) (hR : R > 0) (_hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∃ v : ℂ, norm v = R ∧ (∀ w : ℂ, w ∈ closure (ballDR R) → norm (h v) ≥ norm (h w)) ∧ norm (h v) ≤ B := by
                                                                             
  obtain ⟨v, hv_abs, hv_max⟩ := lem_MaxModv3 R hR h h_analytic
                         
  use v
  constructor
  ·           
    exact hv_abs
  constructor
  ·                                                  
    exact hv_max
  ·                                                  
    apply h_boundary_bound
    exact hv_abs

lemma lem_HardMMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B := by
  intro w hw
                                                                                            
  obtain ⟨v, hv_abs, hv_max, hv_bound⟩ := lem_MaxModv4 R B hR hB h h_analytic h_boundary_bound
                                
  have h1 : norm (h w) ≤ norm (h v) := hv_max w hw
  have h2 : norm (h v) ≤ B := hv_bound
                             
  linarith [h1, h2]

lemma lem_EasyMMP (R B : ℝ) (hR : R > 0) (_hB : B ≥ 0)
  (h : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_closure_bound : ∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B) :
∀ z : ℂ, norm z = R → norm (h z) ≤ B := by
  intro z hz
                                                  
  apply h_closure_bound z
                                     
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  rw [Complex.dist_eq]
  simp

  have : ‖z‖ = R := hz
  linarith

theorem lem_MMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
(∀ z : ℂ, z ∈ closure (ballDR R) → norm (h z) ≤ B) ↔ (∀ z : ℂ, norm z = R → norm (h z) ≤ B) := by
  constructor
  ·                                                     
    intro h_closure_bound
    exact lem_EasyMMP R B hR hB h h_analytic h_closure_bound
  ·                                                      
    intro h_boundary_bound
    exact lem_HardMMP R B hR hB h h_analytic h_boundary_bound

lemma lem_denominator_nonzero (R M : ℝ) (_hR : R > 0) (hM : M > 0)
  (f : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
  (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → (2 * M - f z) ≠ 0 := by
  intro z hz
                                                  
  apply lem_real_part_lower_bound4 (f z) M hM
                                   
  exact h_re_bound z hz

lemma lem_f_vs_2M_minus_f (R M : ℝ) (_hR : R > 0) (hM : M > 0)
  (f : ℂ → ℂ) (_h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
  (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → norm (f z) / norm (2 * M - f z) ≤ 1 := by
  intro z hz
                                                 
  apply lem_nonnegative_product9 M (f z) hM
                                   
  exact h_re_bound z hz

lemma lem_removable_singularity (R : ℝ) (hR : R > 0) (f : ℂ → ℂ)
  (h_analytic : AnalyticOn ℂ f (closure (ballDR R))) (h_zero : f 0 = 0) :
AnalyticOn ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) (closure (ballDR R)) := by
                                                                             
  rw [lem_ballDR R hR] at h_analytic ⊢

  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  apply lem_analAtOnOn hR g

  ·                                
                                                   
    exact lem_ordernatcast2 hR f h_zero h_analytic

  ·                                                         

    have f_on_closedball : AnalyticOn ℂ f (Metric.closedBall 0 R) := h_analytic
    have quotient_analytic : AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | ‖z‖ ≤ R ∧ z ≠ 0} :=
      lem_fzzTanal hR f f_on_closedball

    apply AnalyticOn.congr quotient_analytic
    intro z hz
                                                                 
    simp [g, if_neg hz.2]

lemma lem_quotient_analytic {R : ℝ} (_hR : R > 0) (h1 h2 : ℂ → ℂ)
  (h_analytic1 : AnalyticOn ℂ h1 (closure (ballDR R)))
  (h_analytic2 : AnalyticOn ℂ h2 (closure (ballDR R)))
  (h_nonzero : ∀ z ∈ closure (ballDR R), h2 z ≠ 0) :
AnalyticOn ℂ (fun z ↦ h1 z / h2 z) (closure (ballDR R)) := by
  exact AnalyticOn.div h_analytic1 h_analytic2 h_nonzero

lemma lem_g_analytic (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
AnalyticOn ℂ (f_M R M hR hM f h_analytic h_zero h_re_bound) (closure (ballDR R)) := by
                                                          
  let h₁ : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z
                              
  let h₂ : ℂ → ℂ := fun z ↦ 2 * M - f z

  have h_eq : f_M R M hR hM f h_analytic h_zero h_re_bound = fun z ↦ h₁ z / h₂ z := by
    ext z
    unfold f_M h₁ h₂
    simp

  rw [h_eq]

  apply lem_quotient_analytic hR

  · exact lem_removable_singularity R hR f h_analytic h_zero

  · have h₂_analytic : AnalyticOn ℂ h₂ (closure (ballDR R)) := by
      unfold h₂
      apply AnalyticOn.sub
      · exact analyticOn_const
      · exact h_analytic
    exact h₂_analytic

  · intro z hz
    unfold h₂
    exact lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz

lemma lem_absab (a b : ℂ) (_hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
  exact IsAbsoluteValue.abv_div norm a b

lemma lem_g_on_boundaryz (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_in_closure : z ∈ closure (ballDR R)) (hz_nonzero : z ≠ 0) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
norm (f z / z) / norm (2 * M - f z) := by
                              
  unfold f_M
                                                                
  simp only [if_neg hz_nonzero]

  have h_nonzero : (2 * M - f z) ≠ 0 := lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz_in_closure
                    
  exact lem_absab (f z / z) (2 * M - f z) h_nonzero

lemma lem_fzzR (R : ℝ) (hR : R > 0) (z w : ℂ) (hz : norm z = R) : norm (w / z) = norm w / R := by
                          
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz
    simp at hz
    linarith [hz, hR]
                    
  rw [lem_absab w z hz_nonzero]
                               
  rw [hz]

lemma lem_g_on_boundary (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_on_boundary : norm z = R) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
(norm (f z) / R) / norm (2 * M - f z) := by
                                            
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz_on_boundary
    simp at hz_on_boundary
    linarith [hz_on_boundary, hR]

  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    convert (preTransparency := .instances) le_of_eq hz_on_boundary

  have h1 : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    norm (f z / z) / norm (2 * M - f z) :=
    lem_g_on_boundaryz R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure hz_nonzero

  have h2 : norm (f z / z) = norm (f z) / R :=
    lem_fzzR R hR z (f z) hz_on_boundary

  rw [h1, h2]

lemma lem_f_vs_2M_minus_fR (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (_h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_in_closure : z ∈ closure (ballDR R)) :
(norm (f z) / R) / norm (2 * M - f z) ≤ 1 / R := by
                                               
  have h1 : norm (f z) / norm (2 * M - f z) ≤ 1 :=
    lem_f_vs_2M_minus_f R M hR hM f h_analytic h_re_bound z hz_in_closure

  rw [div_div]

  rw [mul_comm R]

  rw [← div_div]

  exact div_le_div_of_nonneg_right h1 (le_of_lt hR)

lemma lem_g_boundary_bound0 (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_on_boundary : norm z = R) :
norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R := by
                                                          
  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    convert (preTransparency := .instances) le_of_eq hz_on_boundary

  rw [lem_g_on_boundary R M hR hM f h_analytic h_zero h_re_bound z hz_on_boundary]

  exact lem_f_vs_2M_minus_fR R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure

lemma lem_g_interior_bound (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (ballDR R) → norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R := by
                      
  have hB : (1 / R : ℝ) ≥ 0 := div_nonneg zero_le_one (le_of_lt hR)
                                          
  have h_g_analytic : AnalyticOn ℂ (f_M R M hR hM f h_analytic h_zero h_re_bound) (closure (ballDR R)) :=
    lem_g_analytic R M hR hM f h_analytic h_zero h_re_bound
                                                                       
  apply (lem_MMP R (1 / R) hR hB (f_M R M hR hM f h_analytic h_zero h_re_bound) h_g_analytic).mpr
                                                                
  intro z hz_boundary
  exact lem_g_boundary_bound0 R M hR hM f h_analytic h_zero h_re_bound z hz_boundary

lemma lem_g_at_r (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
(norm (f z) / r) / norm (2 * M - f z) := by
                                            
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz_on_boundary
    simp at hz_on_boundary
    linarith [hz_on_boundary, hr_pos]

  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h1 : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    norm (f z / z) / norm (2 * M - f z) :=
    lem_g_on_boundaryz R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure hz_nonzero

  have h2 : norm (f z / z) = norm (f z) / r :=
    lem_fzzR r hr_pos z (f z) hz_on_boundary

  rw [h1, h2]

lemma lem_g_at_rR (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
(norm (f z) / r) / norm (2 * M - f z) ≤ 1 / R := by
                                                       
  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h_bound : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R :=
    lem_g_interior_bound R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure

  have h_eq : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    (norm (f z) / r) / norm (2 * M - f z) :=
    lem_g_at_r R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  rw [← h_eq]
  exact h_bound

lemma lem_fracs (a b r R : ℝ) (ha : a > 0) (hb : b > 0) (hr : r > 0) (hR : R > 0)
(h_le : (a / r) / b ≤ 1 / R) : R * a ≤ r * b := by
                                              
  have h1 : (a / r) / b = a / (r * b) := by
    field_simp
  rw [h1] at h_le

  have h_pos_rb : 0 < r * b := mul_pos hr hb
  rw [div_le_div_iff₀ h_pos_rb hR] at h_le
                                      
  simp only [one_mul] at h_le

  linarith

lemma lem_nonneg_product_with_real_abs (r M : ℝ) (hr : r > 0) (hM : M > 0) : 0 ≤ r * (2 * |M|) := by
                                 
  have h_abs_eq : |M| = M := abs_of_pos hM
                                         
  rw [h_abs_eq]

  have h_two_M_pos : (2 : ℝ) * M > 0 := by
    apply mul_pos
    norm_num
    exact hM
                              
  apply mul_nonneg
  linarith [hr]
  linarith [h_two_M_pos]

lemma lem_f_bound_rearranged (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
R * norm (f z) ≤ r * norm (2 * M - f z) := by
                                     
  have hz_in_closure : z ∈ closure (ballDR R) := by
    rw [lem_ballDR R hR]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  have h_ineq : (norm (f z) / r) / norm (2 * M - f z) ≤ 1 / R :=
    lem_g_at_rR R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  have h_denom_nonzero : (2 * M - f z) ≠ 0 :=
    lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz_in_closure

  have h_denom_pos : norm (2 * M - f z) > 0 :=
    lem_abspos (2 * M - f z) h_denom_nonzero

  by_cases h_case : f z = 0
  ·                                                      
    rw [h_case]
    simp [mul_zero]
    exact lem_nonneg_product_with_real_abs r M hr_pos hM
  ·                                    
    have h_num_pos : norm (f z) > 0 :=
      lem_abspos (f z) h_case

    exact lem_fracs (norm (f z)) (norm (2 * M - f z)) r R
           h_num_pos h_denom_pos hr_pos hR h_ineq

lemma lem_final_bound_on_circle0 (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
                                                                                     
  have h_ineq : R * norm (f z) ≤ r * norm (2 * M - f z) :=
    lem_f_bound_rearranged R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  have h_bound : norm (f z) ≤ (2 * M * r) / (R - r) :=
    lem_rtriangle7 r R M (f z) hr_pos hr_lt_R hM h_ineq

  have h_rearrange : (2 * M * r) / (R - r) = (2 * r / (R - r)) * M := by
    field_simp

  rw [← h_rearrange]
  exact h_bound

lemma lem_final_bound_on_circle (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
  exact lem_final_bound_on_circle0 R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

lemma lem_BCI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_in_ball : norm z ≤ r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
                                  
  let B := (2 * r / (R - r)) * M

  have hB : B ≥ 0 := by
    unfold B
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · linarith [hr_pos]
      · linarith [hr_lt_R]
    · linarith [hM]

  have h_analytic_r : AnalyticOn ℂ f (closure (ballDR r)) := by
    apply AnalyticOn.mono h_analytic
                                                   
    apply closure_mono
    unfold ballDR
    exact Metric.ball_subset_ball (le_of_lt hr_lt_R)

  have hz_in_closure_r : z ∈ closure (ballDR r) := by
    rw [lem_ballDR r hr_pos]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    exact hz_in_ball

  have h_boundary : ∀ w : ℂ, norm w = r → norm (f w) ≤ B := by
    intro w hw_boundary
    exact lem_final_bound_on_circle R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R w hw_boundary

  have h_closure := (lem_MMP r B hr_pos hB f h_analytic_r).mpr h_boundary

  exact h_closure z hz_in_closure_r

theorem thm_BorelCaratheodoryI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (ballDR R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (ballDR R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R) :
sSup ((norm ∘ f) '' (closure (ballDR r))) ≤ (2 * r / (R - r)) * M := by
                                                                                               
  apply Real.sSup_le
  ·                                                                                                      
    intro x hx

    obtain ⟨z, hz_in_closure, hx_eq⟩ := hx
    rw [← hx_eq]

    have hz_bound : norm z ≤ r := by
      rw [lem_ballDR r hr_pos] at hz_in_closure
      rw [Metric.mem_closedBall] at hz_in_closure
      rw [Complex.dist_eq] at hz_in_closure
      simp at hz_in_closure
      exact hz_in_closure
                    
    exact lem_BCI R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_bound
  ·                                       
    apply mul_nonneg
    · apply div_nonneg
      · apply mul_nonneg
        · norm_num
        · linarith [hr_pos]
      · linarith [hr_lt_R]
    · linarith [hM]

lemma cauchy_formula_deriv {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (_h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r_int), (w - z)⁻¹ ^ 2 • f w := by
                                       
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain

  have hz_in_ball : z ∈ Metric.ball (0 : ℂ) r_int := by
    apply Metric.mem_ball.mpr
    have h1 : ‖z - 0‖ ≤ r_z := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hz
    simp only [sub_zero] at h1
    have h2 : ‖z‖ < r_int := lt_of_le_of_lt h1 h_r_z_lt_r_int
    rwa [dist_eq_norm, sub_zero]

  set U := Metric.ball (0 : ℂ) R_analytic

  have hc_subset : Metric.closedBall (0 : ℂ) r_int ⊆ U := by
    apply Metric.closedBall_subset_ball
    exact h_r_int_lt_R_analytic

  have hf_on_U : DifferentiableOn ℂ f U := by

    apply DifferentiableOn.mono hf_diff_U'
    calc U = Metric.ball 0 R_analytic := rfl
         _ ⊆ Metric.closedBall 0 R_analytic := Metric.ball_subset_closedBall
         _ ⊆ U' := h_subset

  have cauchy_eq := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
    Metric.isOpen_ball hc_subset hf_on_U hz_in_ball

  rw [← cauchy_eq]

  congr 2
  ·                                         
    simp only [one_div]
                                  
    rfl
  ·                                               
    ext w
    rw [← inv_pow]

lemma circleMap_zero_eq_exp (r : ℝ) (t : ℝ) : circleMap 0 r t = r * Complex.exp (I * t) := by
                                                                         
  rw [circleMap]
                                                                                    
  simp only [zero_add]
                                                                          
  congr 2
  rw [mul_comm (t : ℂ) Complex.I]
                                      
  rfl

lemma deriv_ofReal_eq_one (t : ℝ) : deriv Complex.ofReal t = 1 := by

  have h : deriv Complex.ofReal t = Complex.ofReal 1 := by

    rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
    exact ContinuousLinearMap.deriv Complex.ofRealCLM
                                       
  rw [h]
  simp only [Complex.ofReal_one]

lemma differentiableAt_ofReal (t : ℝ) : DifferentiableAt ℝ Complex.ofReal t := by
                                                                                
  rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl]
                                                                                    
  apply ContinuousLinearMap.differentiableAt

lemma lem_dw_dt_real {r_int : ℝ} (t : ℝ) :
deriv (fun (t' : ℝ) => r_int * Complex.exp (I * t')) t = I * r_int * Complex.exp (I * t) := by
                                       
  rw [deriv_const_mul]
                                             
  rw [deriv_cexp]
                                                  
  rw [deriv_const_mul]
                                                            
  rw [deriv_ofReal_eq_one]
                                                                                        
  ring
                                                                         
  · exact differentiableAt_ofReal t
  · exact (differentiableAt_const I).mul (differentiableAt_ofReal t)
  · exact DifferentiableAt.cexp ((differentiableAt_const I).mul (differentiableAt_ofReal t))

lemma deriv_circleMap_zero (r : ℝ) (t : ℝ) : deriv (circleMap 0 r) t = I * r * Complex.exp (I * t) := by
                                                            
  have h : circleMap 0 r = fun (t' : ℝ) => r * Complex.exp (I * t') := by
    ext t'
    exact circleMap_zero_eq_exp r t'

  rw [h]

  exact lem_dw_dt_real t

lemma lem_CIF_deriv_param {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi * I)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(I * r_int * Complex.exp (I * t) * ((r_int * Complex.exp (I * t)) - z)⁻¹ ^ 2) * f (r_int * Complex.exp (I * t))) := by
                                                               
  rw [cauchy_formula_deriv hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  rw [circleIntegral_def_Icc]

  rw [smul_eq_mul]

  simp only [circleMap_zero_eq_exp, deriv_circleMap_zero]

  congr 2
  ext t
  simp only [smul_eq_mul]
  ring

lemma complex_coeff_I_cancel : (1 : ℂ) / (2 * Real.pi * I) * I = 1 / (2 * Real.pi) := by
  field_simp [I, Complex.I_ne_zero, Real.pi_pos.ne']

lemma factor_I_from_integrand (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) :
  ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  I * ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) := by

  have h : ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
           ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I • (↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t))) := by
    congr 1
    ext t
    rw [smul_eq_mul]
    ring
  rw [h]
                                                              
  rw [MeasureTheory.integral_smul]
                                                                 
  rw [smul_eq_mul]

lemma integrand_transform_div (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) (t : ℝ) :
  ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  ↑r_int * Complex.exp (I * ↑t) * f (↑r_int * Complex.exp (I * ↑t)) / (↑r_int * Complex.exp (I * ↑t) - z) ^ 2 := by
                                                              
  rw [inv_pow]
                                                                                     
  rw [← div_eq_mul_inv]
                                                
  ring

lemma lem_CIF_deriv_simplified {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
                              
  rw [lem_CIF_deriv_param hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  rw [factor_I_from_integrand f r_int z]

  rw [← mul_assoc, complex_coeff_I_cancel]

  congr 2
  funext t
  rw [integrand_transform_div f r_int z t]

lemma lem_modulus_of_f_prime0 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) = norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
                                                                 
  rw [lem_CIF_deriv_simplified hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

lemma one_div_two_pi_pos : (1 : ℝ) / (2 * Real.pi) > 0 := by
                            
  have h_pi_pos : Real.pi > 0 := Real.pi_pos
                        
  have h_2pi_pos : 2 * Real.pi > 0 := by
    apply mul_pos
    · norm_num
    · exact h_pi_pos
                              
  apply div_pos
  · norm_num
  · exact h_2pi_pos

lemma abs_integral_le_integral_abs {a b : ℝ} {g : ℝ → ℂ} (_hab : a ≤ b) : norm (∫ (t : ℝ) in Set.Icc a b, g t) ≤ ∫ (t : ℝ) in Set.Icc a b, norm (g t) := by

  exact MeasureTheory.norm_integral_le_integral_norm g

lemma complex_abs_mul (a b : ℂ) : norm (a * b) = norm a * norm b :=
  Complex.norm_mul a b

lemma complex_abs_ofReal_nonneg (r : ℝ) (hr : r ≥ 0) : norm (↑r : ℂ) = r := by
                                          
  have h1 : norm (↑r * 1) = r * norm (1 : ℂ) := by simp; assumption
                                         
  simp only [mul_one] at h1
  have h2 : norm (1 : ℂ) = 1 := by simp
  rw [h2] at h1
  simp only [mul_one] at h1
  simp
  assumption

lemma abs_one_div_two_pi_complex : norm (1 / (2 * ↑Real.pi : ℂ)) = 1 / (2 * Real.pi) := by
                                                                              
  have h_eq : (1 / (2 * ↑Real.pi) : ℂ) = ↑(1 / (2 * Real.pi) : ℝ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]

  rw [h_eq]

  have h_nonneg : (1 / (2 * Real.pi) : ℝ) ≥ 0 := by
    apply div_nonneg
    · norm_num
    · apply mul_nonneg
      · norm_num
      · exact le_of_lt Real.pi_pos

  exact complex_abs_ofReal_nonneg (1 / (2 * Real.pi)) h_nonneg

lemma lem_integral_modulus_inequality {r_int : ℝ} {z : ℂ} {f : ℂ → ℂ} :
norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), (r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
                                                        
  rw [complex_abs_mul]

  rw [abs_one_div_two_pi_complex]

  apply mul_le_mul_of_nonneg_left
  ·                                                                  
    have h_2pi_nonneg : (0 : ℝ) ≤ 2 * Real.pi := by
      apply mul_nonneg
      · norm_num
      · exact le_of_lt Real.pi_pos
    exact abs_integral_le_integral_abs h_2pi_nonneg
  · exact le_of_lt one_div_two_pi_pos

lemma lem_modulus_of_f_prime {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
                                                           
  rw [lem_modulus_of_f_prime0 hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
                                                                        
  exact lem_integral_modulus_inequality

lemma lem_modulus_of_integrand_product2 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (_hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (_h_r_z_pos : 0 < r_z)
    (_h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic) :
    norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) =
norm (f (r_int * Complex.exp (I * t))) * norm (r_int * Complex.exp (I * t)) := by
                                                                     
  rw [norm_mul]

lemma lem_modeit (t : ℝ) : norm (Complex.exp (I * t)) = Real.exp (Complex.re (I * t)) := by
                                                        
  exact Complex.norm_exp (I * t)

lemma lem_Reit0 (t : ℝ) : Complex.re (I * t) = 0 := by
                                        
  unfold I
                                                    
  rw [Complex.mul_re]

  rw [Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
                                  
  ring

lemma lem_e01 : Real.exp 0 = 1 := by
  exact Real.exp_zero

lemma lem_modulus_of_e_it_is_one (t : ℝ) : norm (Complex.exp (I * t)) = 1 := by
                                                                                            
  rw [lem_modeit]
                                                   
  rw [lem_Reit0]
                                         
  rw [lem_e01]

lemma lem_modulus_of_ae_it {a t : ℝ} (ha : 0 < a) : norm (a * Complex.exp (I * t)) = a := by
                                                              
  rw [norm_mul, lem_modulus_of_e_it_is_one, mul_one, Complex.norm_real]
  exact abs_of_pos ha

lemma lem_modulus_of_integrand_product3 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) = r_int * norm (f (r_int * Complex.exp (I * t))) := by
                                                                      
  rw [lem_modulus_of_integrand_product2 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]
                                                                            
  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  rw [lem_modulus_of_ae_it h_r_int_pos]
                                                                
  ring

lemma lem_modulus_wz (w z : ℂ) : norm ((w - z) ^ 2) = (norm (w - z)) ^ 2 := by
                                     
  exact Complex.norm_pow (w - z) 2

lemma lem_reverse_triangle (w z : ℂ) : norm w - norm z ≤ norm (w - z) := by

  exact norm_sub_norm_le w z

lemma lem_reverse_triangle3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic) :
r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z) := by
                                                  
  have h_mod : norm (r_int * Complex.exp (I * t)) = r_int := by
    have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
    exact lem_modulus_of_ae_it h_r_int_pos
                                                                    
  have h_triangle := lem_reverse_triangle (r_int * Complex.exp (I * t)) z
                                     
  rw [h_mod] at h_triangle
  exact h_triangle

lemma lem_zrr1 {R_analytic r_z r_int : ℝ}
    (_h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (_h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
0 < r_int - norm z := by
                                                      
  have h1 : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
                                        
  have h2 : dist z 0 = ‖z‖ := by
    rw [dist_eq_norm, sub_zero]
                 
  have h3 : ‖z‖ ≤ r_z := by rwa [← h2]
                                      
  have h4 : norm z = ‖z‖ := rfl
                    
  have h5 : norm z ≤ r_z := by rwa [h4]
                                                     
  have h6 : norm z < r_int := lt_of_le_of_lt h5 h_r_z_lt_r_int
                                 
  linarith

lemma lem_zrr2 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
r_int - r_z ≤ norm (r_int * Complex.exp (I * t) - z) := by
                                                        
  have h1 : norm z ≤ r_z := by
    have h_dist : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
    rw [dist_eq_norm, sub_zero] at h_dist
    exact h_dist
                                                             
  have h2 : r_int - r_z ≤ r_int - norm z := by linarith [h1]
                                                                                               
  have h3 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
                               
  exact le_trans h2 h3

lemma lem_zrr3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int - r_z) ^ 2 ≤ norm (r_int * Complex.exp (I * t) - z) ^ 2 := by
                                                       
  have h_ineq := @lem_zrr2 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                    
  have h_nonneg_left : 0 ≤ r_int - r_z := by linarith [h_r_z_lt_r_int]
  have h_nonneg_right : 0 ≤ norm (r_int * Complex.exp (I * t) - z) := norm_nonneg _
                                                    
  have h_sq := mul_self_le_mul_self h_nonneg_left h_ineq
                                
  rw [pow_two, pow_two]
  exact h_sq

lemma lem_reverse_triangle4 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
0 < norm (r_int * Complex.exp (I * t) - z) := by
                                             
  have h1 := lem_zrr1 h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                                               
  have h2 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
                               
  exact lt_of_lt_of_le h1 h2

lemma lem_wposneq0 (w : ℂ) : norm w > 0 → w ≠ 0 := by
  intro h
                                                  
  by_contra h_eq_zero
                              
  have h_abs_zero : norm w = 0 := by
    rw [h_eq_zero]
    simp
                                        
  rw [h_abs_zero] at h
  exact lt_irrefl 0 h

lemma lem_reverse_triangle5 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
r_int * Complex.exp (I * t) - z ≠ 0 := by
                                                                                  
  have h_pos := @lem_reverse_triangle4 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                  
  exact lem_wposneq0 (r_int * Complex.exp (I * t) - z) h_pos

lemma lem_reverse_triangle6 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
                                                                   
  have h_ne_zero := lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                                    
  exact pow_ne_zero 2 h_ne_zero

lemma lem_absdiv {a b : ℂ} (_hb : b ≠ 0) : norm (a / b) = norm a / norm b := by
                                             
  exact norm_div a b

lemma lem_modulus_of_integrand_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (_hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
                                               
  have h_neq_zero : r_int * Complex.exp (I * t) - z ≠ 0 :=
    lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                         
  have h_sq_neq_zero : (r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_self_ne_zero.mpr h_neq_zero
                                              
  rw [lem_absdiv h_sq_neq_zero]
                                                              
  rw [lem_modulus_wz]

lemma lem_modulus_of_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
(r_int * norm (f (r_int * Complex.exp (I * t)))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
                                                                                             
  rw [lem_modulus_of_integrand_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
                                                                           
  rw [lem_modulus_of_integrand_product3 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]

lemma lem_modulus_of_product4 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤
(r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2) := by
                                               
  rw [lem_modulus_of_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  have h_ineq := @lem_zrr3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  apply div_le_div_of_nonneg_left
  ·                            
    apply mul_nonneg
    · linarith [h_r_z_pos, h_r_z_lt_r_int]
    · exact norm_nonneg _
  ·                                           
    apply pow_pos
    linarith [h_r_z_lt_r_int]
  ·                                                              
    exact h_ineq

lemma lem_bound_on_f_at_r_prime {M R_analytic r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (hr_int_pos : 0 < r_int)
    (hr_int_lt_R_analytic : r_int < R_analytic)
    (f : ℂ → ℂ)

    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ z ∈ Metric.closedBall 0 R_analytic, (f z).re ≤ M)
    (t : ℝ) :
norm (f (r_int * Complex.exp (I * t))) ≤ (2 * r_int * M) / (R_analytic - r_int) := by
                                         
  obtain ⟨U, hU_open, h_subset, hf_diff_U⟩ := hf_domain

  let z₀ := r_int * Complex.exp (I * t)

  have h_sSup_bound := thm_BorelCaratheodoryI R_analytic M hR_analytic_pos hM_pos f
                                                                   
    (by
                                        
      have h_analytic_U : AnalyticOn ℂ f U := hf_diff_U.analyticOn hU_open

      rw [ballDR]
      convert (preTransparency := .instances) h_analytic_U.mono h_subset
                                                                              
      apply closure_ball
      linarith
      )
    hf0
    (by rwa [lem_ballDR R_analytic hR_analytic_pos])                         
    r_int hr_int_pos hr_int_lt_R_analytic

  have hz₀_in_ball : z₀ ∈ Metric.closedBall 0 r_int := by
    rw [Metric.mem_closedBall]
    simp only [dist_eq_norm, sub_zero]
                                                          
    have h_norm : ‖r_int * Complex.exp (I * t)‖ = r_int := by
      rw [norm_mul]

      have h1 : ‖(r_int : ℂ)‖ = r_int := by
        rw [Complex.norm_real]
        exact abs_of_pos hr_int_pos
                                           
      have h2 : ‖Complex.exp (I * ↑t)‖ = 1 := by
                                                               
        exact lem_modulus_of_e_it_is_one t
      rw [h1, h2]
      ring
    rw [h_norm]

  have hz₀_in_closure : z₀ ∈ closure (ballDR r_int) := by
    rw [lem_ballDR r_int hr_int_pos]
    exact hz₀_in_ball

  have h_in_image : norm (f z₀) ∈ (norm ∘ f) '' (closure (ballDR r_int)) := by
    use z₀, hz₀_in_closure
    rfl

  have h_le_sSup : norm (f z₀) ≤ sSup ((norm ∘ f) '' (closure (ballDR r_int))) := by
    apply le_csSup
                                            
    · use (2 * r_int / (R_analytic - r_int)) * M
      intros x hx
      obtain ⟨w, hw_in, hx_eq⟩ := hx
      rw [← hx_eq]
                                         
      have hw_in_closed : w ∈ Metric.closedBall 0 r_int := by
        rwa [← lem_ballDR r_int hr_int_pos]
                                                                   
      have hw_in_R : w ∈ Metric.closedBall 0 R_analytic := by
        have h_subset : Metric.closedBall (0 : ℂ) r_int ⊆ Metric.closedBall 0 R_analytic := by
          apply Metric.closedBall_subset_closedBall
          linarith [hr_int_lt_R_analytic]
        exact h_subset hw_in_closed
                                                  
      exact lem_BCI R_analytic M hR_analytic_pos hM_pos f
        (by
          rw [ballDR]
          have h_analytic_U : AnalyticOn ℂ f U := hf_diff_U.analyticOn hU_open
          convert (preTransparency := .instances) h_analytic_U.mono h_subset
          apply closure_ball
          linarith)
        hf0
        (by rwa [lem_ballDR R_analytic hR_analytic_pos])
        r_int hr_int_pos hr_int_lt_R_analytic w
        (by aesop)
                                
    · exact h_in_image

  calc norm (f z₀)
    ≤ sSup ((norm ∘ f) '' (closure (ballDR r_int))) := h_le_sSup
    _ ≤ (2 * r_int / (R_analytic - r_int)) * M := h_sSup_bound
    _ = (2 * r_int * M) / (R_analytic - r_int) := by ring

lemma lem_bound_on_integrand_modulus {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z)
    (t : ℝ) :
norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
                                                            
  have h1 := lem_modulus_of_product4 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
                                                                 
  have h2 := lem_bound_on_f_at_r_prime hM_pos hR_analytic_pos (lt_trans h_r_z_pos h_r_z_lt_r_int) h_r_int_lt_R_analytic f hf_domain hf0 hRe_f_le_M t

  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  have h_denom_nonneg : 0 ≤ (r_int - r_z) ^ 2 := by
    apply sq_nonneg

  have h3 : (r_int * norm (f (r_int * Complex.exp (I * t)))) / (r_int - r_z) ^ 2 ≤
            (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 := by
    apply div_le_div_of_nonneg_right _ h_denom_nonneg
    apply mul_le_mul_of_nonneg_left h2
    linarith [h_r_int_pos]

  have h4 : (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 =
            (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
    have h_R_sub_r_pos : 0 < R_analytic - r_int := by linarith [h_r_int_lt_R_analytic]
    have h_r_sub_r_pos : 0 < r_int - r_z := by linarith [h_r_z_lt_r_int]
    field_simp [ne_of_gt h_R_sub_r_pos, ne_of_gt (pow_pos h_r_sub_r_pos 2)]

  rw [h4] at h3
  exact le_trans h1 h3

lemma lem_integral_inequality_aux {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in a..b, g t ≤ ∫ _t in a..b, C := by

  have h_const_integrable : IntervalIntegrable (fun _ => C) MeasureTheory.volume a b :=
    intervalIntegrable_const
                                                                             
  have h_pointwise : ∀ x ∈ Set.Icc a b, g x ≤ (fun _ => C) x := by
    intro x hx
    simp
    exact h_bound x hx
                                   
  exact intervalIntegral.integral_mono_on hab h_integrable h_const_integrable h_pointwise

lemma lem_integral_inequality {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in Set.Icc a b, g t ≤ ∫ _t in Set.Icc a b, C := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact lem_integral_inequality_aux hab h_integrable h_bound

lemma continuous_real_parameterization (r : ℝ) : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := by

  have h1 : Continuous (fun t : ℝ => (t : ℂ)) := Complex.continuous_ofReal

  have h2 : Continuous (fun z : ℂ => I * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  have h3 : Continuous Complex.exp := Complex.continuous_exp

  have h4 : Continuous (fun z : ℂ => (r : ℂ) * z) := by
    apply Continuous.mul
    · exact continuous_const
    · exact continuous_id

  apply Continuous.comp h4
  apply Continuous.comp h3
  apply Continuous.comp h2
  exact h1

lemma continuous_f_parameterized {f : ℂ → ℂ} {R r : ℝ}     (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
 (hr_pos : 0 < r) (hr_lt_R : r < R) : Continuous (fun t : ℝ => f (r * Complex.exp (I * t))) := by
                                                                       
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain
  have hf_cont : ContinuousOn f (Metric.closedBall 0 R) := by
                                                                  
    have hf_on_closed : DifferentiableOn ℂ f (Metric.closedBall 0 R) :=
      hf_diff_U'.mono h_subset
                                                               
    exact DifferentiableOn.continuousOn hf_on_closed

  have hparam_cont : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := continuous_real_parameterization r

  have hparam_range : ∀ t : ℝ, r * Complex.exp (I * t) ∈ Metric.closedBall 0 R := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
                                                        
    change norm (r * Complex.exp (I * t)) ≤ R
    rw [lem_modulus_of_ae_it hr_pos]
    exact le_of_lt hr_lt_R

  have hcomp_on : ContinuousOn (fun t : ℝ => f (r * Complex.exp (I * t))) Set.univ := by
    apply ContinuousOn.comp hf_cont (Continuous.continuousOn hparam_cont)
    intro t _
    exact hparam_range t

  exact continuousOn_univ.mp hcomp_on

lemma continuous_denominator_parameterized (r : ℝ) (z : ℂ) : Continuous (fun t : ℝ => (r * Complex.exp (I * t) - z) ^ 2) := by

  have h1 : Continuous (fun t : ℝ => r * Complex.exp (I * t) - z) := by
                                                         
    apply Continuous.sub
    ·                                                                                 
      exact continuous_real_parameterization r
    ·                                           
      exact continuous_const

  have h2 : Continuous (fun x : ℂ => x ^ 2) := continuous_pow 2

  exact Continuous.comp h2 h1

lemma interval_integrable_cauchy_integrand {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} {z : ℂ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
                                                             
  apply Continuous.intervalIntegrable

  apply Continuous.comp continuous_norm

  apply Continuous.div₀

  · apply Continuous.mul
                                                     
    · exact continuous_real_parameterization r_int
                                                         
    · have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
      exact continuous_f_parameterized hf_domain h_r_int_pos h_r_int_lt_R_analytic

  · exact continuous_denominator_parameterized r_int z

  · intro t
    exact lem_reverse_triangle6 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

lemma integral_const_over_interval (C : ℝ) :
∫ _t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
                                                                             
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
                                                                                     
  have h_le : (0 : ℝ) ≤ 2 * Real.pi := by
    apply mul_nonneg
    · norm_num
    · exact Real.pi_pos.le
  rw [← intervalIntegral.integral_of_le h_le]
                                                 
  rw [intervalIntegral.integral_const]
                                                        
  simp [sub_zero, smul_eq_mul]

lemma lem_f_prime_bound_by_integral_of_constant {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
                                                                 
  have h1 := lem_modulus_of_f_prime hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  set C := (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2)

  have h_bound : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    exact lem_bound_on_integrand_modulus hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz t

  have h_eq : ∀ t, norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
    intro t
    congr 2
    ring

  have h_bound_h1 : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    rw [h_eq]
    exact h_bound t ht

  have h_integrable : IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
                                            
    exact interval_integrable_cauchy_integrand hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  have h2 := lem_integral_inequality ?_ h_integrable h_bound_h1

  have h_const_integral : ∫ t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
                                                       
    exact integral_const_over_interval C

  rw [h_const_integral] at h2

  have h3 : (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤
    (1 / (2 * Real.pi)) * (2 * Real.pi * C) := by
    apply mul_le_mul_of_nonneg_left h2
    apply div_nonneg
    · norm_num
    · linarith [Real.pi_pos]

  have h4 : (1 / (2 * Real.pi)) * (2 * Real.pi * C) = C := by
    have h_pi_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
    field_simp [h_pi_ne_zero]

  rw [h4] at h3
  exact le_trans h1 h3
  simp [Real.pi_nonneg]

lemma lem_f_prime_bound {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
                                              
  exact lem_f_prime_bound_by_integral_of_constant hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz

lemma lem_r_prime_lt_R {r R : ℝ}
    (_h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(r + R) / 2 < R := by
                                                                  
  rw [add_div_two_lt_right]
  exact h_r_lt_R

lemma lem_r_prime_is_intermediate {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
r < (r + R) / 2 ∧ (r + R) / 2 < R := by
  constructor
  ·                         
    rw [left_lt_add_div_two]
    exact h_r_lt_R
  ·                         
    exact lem_r_prime_lt_R h_r_pos h_r_lt_R

lemma lem_calc_R_minus_r_prime {r R : ℝ}
    (_h_r_pos : 0 < r)
    (_h_r_lt_R : r < R) :
R - ((r + R) / 2) = (R - r) / 2 := by
  field_simp; ring

lemma lem_calc_denominator_specific {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(R - ((r + R) / 2)) * (((r + R) / 2) - r) ^ 2 = ((R - r) ^ 3) / 8 := by
                                                           
  rw [lem_calc_R_minus_r_prime h_r_pos h_r_lt_R]
                                              
  have h_calc : ((r + R) / 2) - r = (R - r) / 2 := by
    field_simp; ring
                                
  rw [h_calc]

  ring

lemma lem_calc_numerator_specific {M r R : ℝ}
    (_hM_pos : 0 < M)
    (_hr_pos : 0 < r)
    (_hr_lt_R : r < R) :
2 * (((r + R) / 2) ^ 2) * M = ((R + r) ^ 2 * M) / 2 := by
                                                  
  ring

lemma lem_frac_simplify {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (((R + r) ^ 2 * M) / 2) / (((R - r) ^ 3) / 8) := by
                                     
  dsimp only
                              
  have h_num := lem_calc_numerator_specific hM_pos hr_pos hr_lt_R
                                
  have h_denom := lem_calc_denominator_specific hr_pos hr_lt_R
                              
  rw [← h_num, ← h_denom]

lemma lem_frac_simplify2 {M r R : ℝ}
    (hM_pos : 0 < M)
    (_hr_pos : 0 < r)
    (hr_lt_R : r < R) :
((R + r) ^ 2 * M / 2) / ((R - r) ^ 3 / 8) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by

  have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
  have h_eight_ne_zero : (8 : ℝ) ≠ 0 := by norm_num
  have h_R_minus_r_ne_zero : R - r ≠ 0 := by linarith [hr_lt_R]
  have h_R_minus_r_pow_ne_zero : (R - r) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    exact h_R_minus_r_ne_zero

  field_simp [h_two_ne_zero, h_eight_ne_zero, h_R_minus_r_pow_ne_zero]; ring

lemma lem_frac_simplify3 {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by
                              
  dsimp only
                                                         
  have h1 := lem_frac_simplify hM_pos hr_pos hr_lt_R
                                                            
  have h2 := lem_frac_simplify2 hM_pos hr_pos hr_lt_R
                          
  rw [h1, h2]

lemma lem_ineq_R_plus_r_lt_2R {r R : ℝ} (h_r_lt_R : r < R) :
R + r < 2 * R := by
                           
  rw [two_mul]
                                                                
  linarith [h_r_lt_R]

lemma lem_R_plus_r_is_positive {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
0 < R + r := by
                                         
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
                                       
  exact add_pos hR_pos hr_pos

lemma lem_square_inequality_strict {a b : ℝ}
    (h_a_pos : 0 < a)
    (h_a_lt_b : a < b) :
a ^ 2 < b ^ 2 := by
                             
  have h_a_nonneg : 0 ≤ a := le_of_lt h_a_pos
                                                    
  have h_b_pos : 0 < b := lt_trans h_a_pos h_a_lt_b
  have h_b_nonneg : 0 ≤ b := le_of_lt h_b_pos
                                   
  have h_squares := mul_self_lt_mul_self_iff h_a_nonneg h_b_nonneg
                                                     
  have h_mult : a * a < b * b := h_squares.mp h_a_lt_b
                                                   
  rw [← pow_two, ← pow_two] at h_mult
  exact h_mult

lemma lem_2R_sq_is_4R_sq {R : ℝ} (_hR_pos : 0 < R) : (2 * R) ^ 2 = 4 * R ^ 2 := by
                                                  
  ring

lemma lem_ineq_R_plus_r_sq {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(R + r) ^ 2 < 4 * R ^ 2 := by
                      
  have h1 := lem_ineq_R_plus_r_lt_2R hr_lt_R
                  
  have h2 := lem_R_plus_r_is_positive hr_pos hr_lt_R
                                                                    
  have h3 := lem_square_inequality_strict h2 h1
                                                          
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
  have h4 := lem_2R_sq_is_4R_sq hR_pos
  rw [h4] at h3
  exact h3

lemma lem_ineq_R_plus_r_sqM {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
4 * (R + r) ^ 2 * M < 16 * R ^ 2 * M := by
                                                              
  have h_ineq := lem_ineq_R_plus_r_sq hr_pos hr_lt_R
                        
  have h_4M_pos : 0 < 4 * M := by
    apply mul_pos
    · norm_num
    · exact hM_pos
                                 
  have h_mult := mul_lt_mul_of_pos_right h_ineq h_4M_pos
                                      
  nlinarith [h_mult]

lemma lem_simplify_final_bound {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) < (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
                                                                
  have h_num_ineq := lem_ineq_R_plus_r_sqM hM_pos hr_pos hr_lt_R
                            
  have h_denom_pos : 0 < (R - r) ^ 3 := by
    apply pow_pos
    linarith [hr_lt_R]
                                
  exact div_lt_div_of_pos_right h_num_ineq h_denom_pos

lemma lem_bound_after_substitution {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
                           
  dsimp only
                                                      
  have h1 := lem_frac_simplify3 hM_pos hr_pos hr_lt_R
                                 
  dsimp only at h1
  rw [h1]
                                                            
  have h2 := lem_simplify_final_bound hM_pos hr_pos hr_lt_R
                                  
  exact le_of_lt h2

theorem borel_caratheodory_II {f : ℂ → ℂ} {R M r : ℝ}
    (hR_pos : 0 < R)
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r) :
norm (deriv f z) ≤ (16 * M * R ^ 2) / ((R - r) ^ 3) := by
                                                            
  set r_prime := (r + R) / 2

  have h_intermediate := lem_r_prime_is_intermediate hr_pos hr_lt_R
  have h_r_lt_r_prime := h_intermediate.1
  have h_r_prime_lt_R := h_intermediate.2

  have h_bound := lem_f_prime_bound hM_pos hR_pos hr_pos h_r_lt_r_prime h_r_prime_lt_R hf_domain hf0 hRe_f_le_M hz

  have h_final := lem_bound_after_substitution hM_pos hr_pos hr_lt_R

  have h_combined : norm (deriv f z) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
    exact le_trans h_bound h_final

  convert (preTransparency := .instances) h_combined using 1
  all_goals try with_reducible_and_instances rfl
  ring

open Complex MeasureTheory intervalIntegral
open scoped Interval

open Filter Topology

open Classical

open scoped Topology

end Erdos970
end

section
-- module Solutions.OAIQ096_CM.Erdos970_PNT2_LogDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos970


lemma DRinD1 (R : ℝ) (_hR : 0 < R) (hR' : R < 1) :
    Metric.closedBall (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) 1 := by
  exact Metric.closedBall_subset_ball hR'
lemma lemKinDR (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ Metric.closedBall (0 : ℂ) R := by
  intro ρ hρ

  rw [zerosetKfR] at hρ
                                                                     
  exact hρ.1
lemma lemKRinK1 (R : ℝ) (hR : 0 < R) (hR' : R < 1) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} := by
  intro ρ hρ
  simp only [zerosetKfR, Set.mem_ofPred_eq] at hρ ⊢
  constructor
  · exact DRinD1 R hR hR' hρ.1
  · exact hρ.2

lemma lem_bolzano_weierstrass {D : Set ℂ} (hD : IsCompact D) {Z : Set ℂ} (hZ_inf : Z.Infinite) (hZ_sub_D : Z ⊆ D) :
    ∃ ρ₀ ∈ D, AccPt ρ₀ (Filter.principal Z) :=
  Set.Infinite.exists_accPt_of_subset_isCompact hZ_inf hD hZ_sub_D
lemma lem_zeros_have_limit_point (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f)) := by
  apply lem_bolzano_weierstrass
  ·                                                
    rw [← lem_ballDR R hR]
    exact lem_DRcompact R hR
  · exact h_Kf_inf
  · exact lemKinDR R hR f

open Filter Metric _root_.Set Bornology Function

lemma lem_identity_theorem (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
                                                 
  have h_subset : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall
                                                        
  have hf_open : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := AnalyticOnNhd.mono hf h_subset
                                                         
  have h_conn : IsConnected (Metric.ball (0 : ℂ) 1) := Metric.isConnected_ball (by norm_num : (0 : ℝ) < 1)
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) := h_conn.isPreconnected
                                                     
  have h_zeros_subset : {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} ⊆ {z | f z = 0} := by
    intro z hz
    exact hz.2
                                                                                           
  have h_acc_zero : AccPt ρ₀ (Filter.principal ({z | f z = 0})) := by
    exact AccPt.mono h_acc (principal_mono.2 h_zeros_subset)
                                                                                                  
  have h_closure : ρ₀ ∈ closure ({z | f z = 0} \ {ρ₀}) := by
                                                                                
    have h_cluster : ClusterPt ρ₀ (Filter.principal ({z | f z = 0} \ {ρ₀})) :=
      (accPt_principal_iff_clusterPt).mp h_acc_zero
    exact (mem_closure_iff_clusterPt).2 h_cluster
                               
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hf_open h_preconn hρ₀_in_D1 h_closure
lemma lem_identity_theoremR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_DR : ρ₀ ∈ Metric.closedBall (0 : ℂ) R)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1 := DRinD1 R hR hR' hρ₀_in_DR
  exact lem_identity_theorem f hf ρ₀ hρ₀_in_D1 h_acc
lemma lem_identity_theoremKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_rho0 : ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
                                
  obtain ⟨ρ₀, hρ₀_in_R, h_acc⟩ := h_exists_rho0
                                
  apply lem_identity_theoremR R hR hR' f hf ρ₀ hρ₀_in_R
                                                                    
  exact AccPt.mono h_acc (principal_mono.2 (lemKRinK1 R hR hR' f))
lemma lem_identity_infiniteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have h_exists_rho0 := lem_zeros_have_limit_point R hR f h_Kf_inf
  exact lem_identity_theoremKR R hR hR' f hf h_exists_rho0
lemma lem_Contra_finiteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0) :
    Set.Finite (zerosetKfR R hR f) := by
                                                  
  by_contra h_not_finite

  have h_Kf_inf : Set.Infinite (zerosetKfR R hR f) := h_not_finite
                                  
  have h_eq_zero := lem_identity_infiniteKR R hR hR' f hf h_Kf_inf

  obtain ⟨z, hz_in_ball, hz_nonzero⟩ := h_exists_nonzero
  have h_f_z_zero : f z = 0 := h_eq_zero hz_in_ball
  exact hz_nonzero h_f_z_zero

open Classical

lemma lem_analytic_zero_factor (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ) (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∃ h_σ : ℂ → ℂ, AnalyticAt ℂ h_σ σ ∧ h_σ σ ≠ 0 ∧
    ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ z := by
  classical
                       
  have hσ_closed_R1 : σ ∈ Metric.closedBall (0 : ℂ) R1 := hσ.1
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
  have hσ_closed1 : σ ∈ Metric.closedBall (0 : ℂ) 1 :=
    (Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)) hσ_closed_R1
  have hfσ : AnalyticAt ℂ f σ := h_f_analytic σ hσ_closed1
                             
  have h_order_finite : analyticOrderAt f σ ≠ ⊤ :=
    lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 σ hσ
                                                                      
  rcases (hfσ.analyticOrderAt_ne_top).mp h_order_finite with ⟨g, hgσ, hgσ_ne, h_eq⟩
                                                                                 
  have h_eq' : ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * g z := by
    refine h_eq.mono ?_
    intro z hz
    simpa [smul_eq_mul, analyticOrderNatAt] using hz
  exact ⟨g, hgσ, hgσ_ne, h_eq'⟩

theorem lem_rho_in_disk_R1
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    norm ρ ≤ R1 := by
                                                                      
  have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                                                     
  rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
  simp only [sub_zero] at h_in_ball
  exact h_in_ball

theorem lem_zero_not_in_Kf (R R1 : ℝ)
  (hR1_pos : 0 < R1)
  (_hR1_lt_R : R1 < R)
  (f : ℂ → ℂ)
  (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z) :
    f 0 ≠ 0 → 0 ∉ zerosetKfR R1 (by linarith) f := by
  intro h_f_zero_ne_zero h_zero_in_KfR1
                                                  
  have h_f_zero_eq_zero : f 0 = 0 := h_zero_in_KfR1.2
                                                 
  exact h_f_zero_ne_zero h_f_zero_eq_zero

lemma lem_rho_ne_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f, ρ ≠ 0 := by
  intro ρ h_ρ_in_zeros h_ρ_eq_zero
                                                         
  rw [h_ρ_eq_zero] at h_ρ_in_zeros
                                            
  have h_zero_not_in : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  exact h_zero_not_in h_ρ_in_zeros

lemma lem_mod_pos_iff_ne_zero (z : ℂ) : z ≠ 0 → norm z > 0 :=
  lem_abspos z

theorem lem_mod_rho_pos
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ (ρ : ℂ), ρ ∈ zerosetKfR R1 (by linarith) f → norm ρ > 0 := by
  intro ρ h_ρ_in_zeros
                          
  have h_ρ_ne_zero : ρ ≠ 0 :=
    lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
                                                                 
  exact lem_mod_pos_iff_ne_zero ρ h_ρ_ne_zero

lemma lem_inv_mono_decr (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : 1 / x ≥ 1 / y := by
                                   
  have hy : 0 < y := lt_of_lt_of_le hx hxy
                                                       
  exact one_div_le_one_div_of_le hx hxy

lemma lem_inv_mod_rho_ge_inv_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    1 / norm ρ ≥ 1 / R1 := by
                                                    
  have h_abs_ρ_le_R1 : norm ρ ≤ R1 :=
    lem_rho_in_disk_R1 R R1 hR1_pos hR1_lt_R f ρ h_rho_in_KfR1
                                                            
  have h_abs_ρ_pos : norm ρ > 0 :=
    lem_mod_rho_pos R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
                   
  have h_R1_pos : R1 > 0 := by
    linarith
                                                                   
  exact lem_inv_mono_decr (norm ρ) R1 h_abs_ρ_pos h_abs_ρ_le_R1

theorem lem_R_div_mod_rho_ge_R_div_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ R / R1 := by
                                             
  have h_inv_ineq : 1 / norm ρ ≥ 1 / R1 :=
    lem_inv_mod_rho_ge_inv_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1

  have h_R_div_abs_ρ_eq : R * (1 / norm ρ) = R / norm ρ := by ring
  have h_R_div_R1_eq : R * (1 / R1) = R / R1 := by ring
  rw [← h_R_div_abs_ρ_eq, ← h_R_div_R1_eq]
  exact mul_le_mul_of_nonneg_left h_inv_ineq (by linarith)

theorem lem_R_div_mod_rho_ge_R_over_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ (R/R1 : ℝ) := by
                                
  have h_ineq1 : R / norm ρ ≥ R / R1 :=
    lem_R_div_mod_rho_ge_R_div_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
                           
  linarith

theorem lem_mod_of_prod2 {ι : Type*} (K : Finset ι) (w : ι → ℂ) :
    ‖∏ ρ ∈ K, w ρ‖ = ∏ ρ ∈ K, ‖w ρ‖ := by
  classical
  refine Finset.induction_on K ?h0 ?hstep
  · simp
  · intro a s ha ih
                                                       
    simp [Finset.prod_insert ha, ih]

lemma lem_mod_Bf_is_prod_mod (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ)
    (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat‖ := by
                                                                          
  unfold Bf
  rw [norm_mul]
                                                                                            
  rw [lem_mod_of_prod2]
                                                                                  
  have hCf : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp only [hz, ↓reduceDIte]
  rw [hCf, norm_div]
                                              
  rw [lem_mod_of_prod2]
                                                                        
  rw [div_mul_eq_mul_div]
                                                                                                    
  rw [mul_div_assoc]
                                                    
  rw [← Finset.prod_div_distrib]
  congr 2
  ext ρ
                                   
  rw [← norm_div, ← div_pow]
  congr 2
                                                  
  ring

lemma lem_abs_pow (w : ℂ) (n : ℕ) : ‖w ^ n‖ = ‖w‖ ^ n := by
  simp

lemma lem_mod_Bf_prod_mod (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
  (z : ℂ)
  (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
                                                                                 
  have h1 := lem_mod_Bf_is_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  rw [h1]
                                                              
  congr 2
  ext ρ
  rw [lem_abs_pow]

lemma lem_mod_Bf_at_0 (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖((R : ℂ) / (-ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
                                                                                       
  have hz0 : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec 0 hz0]
                                                                                  
  congr 2
  ext ρ
  congr 1
  simp only [zero_mul, zero_div, sub_zero, zero_sub]

lemma lem_mod_div_ (w1 w2 : ℂ) (_hw2_ne_zero : w2 ≠ 0) : ‖w1 / w2‖ = ‖w1‖ / ‖w2‖ := by
  simp

lemma lem_mod_div_and_neg (R : ℝ) (hR_pos : 0 < R) (ρ : ℂ) (h_rho_ne_zero : ρ ≠ 0) :
  ‖(R : ℂ) / (-ρ)‖ = R / ‖ρ‖ := by
                                                              
  have hden : (-ρ) ≠ 0 := by simpa using neg_ne_zero.mpr h_rho_ne_zero
  have hdiv := lem_mod_div_ (R : ℂ) (-ρ) hden
  calc
    ‖(R : ℂ) / (-ρ)‖ = ‖(R : ℂ)‖ / ‖-ρ‖ := hdiv
    _ = ‖(R : ℂ)‖ / ‖ρ‖ := by simp [norm_neg]
    _ = |R| / ‖ρ‖ := by simp
    _ = R / ‖ρ‖ := by simp [abs_of_pos hR_pos]

theorem lem_mod_Bf_at_0_eval  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
                               
  rw [lem_mod_Bf_at_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec]
                                               
  congr 1
                                                         
  apply Finset.prod_congr rfl
  intro ρ hρ

  have h_ρ_ne_zero : ρ ≠ 0 := by
                                                             
    have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
      exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
    exact lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
                                                  
  rw [lem_mod_div_and_neg R (by linarith) ρ h_ρ_ne_zero]

theorem lem_mod_Bf_at_0_as_ratio  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
  exact lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec

lemma lem_prod_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
    (h_nonneg : ∀ ρ ∈ K, 0 ≤ a ρ) (h_le : ∀ ρ ∈ K, a ρ ≤ b ρ) :
    ∏ ρ ∈ K, a ρ ≤ ∏ ρ ∈ K, b ρ := by
  exact Finset.prod_le_prod h_nonneg h_le

lemma lem_mod_lower_bound_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (_hR_lt_1 : R < 1) :
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 := by
  classical
  set K := h_finite_zeros.toFinset

  have h_base_ge_1 : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have h :=
    lem_prod_ineq K (fun _ : ℂ => (1 : ℝ))
      (fun ρ : ℂ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (by intro ρ hρ; norm_num)
      (by
        intro ρ hρ
        simpa using (one_le_pow₀ (by linarith [h_base_ge_1])))
  simpa [K] using h

theorem lem_mod_Bf_at_0_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≥ 1 := by
                                      
  have R_over_R1_nonneg : 1 < R / R1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have R_over_R1_nonneg : 0 ≤ R / R1 := by linarith
  have h_f_nonzero_at_zero : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
                                                                    
  rw [lem_mod_Bf_at_0_as_ratio R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros]
                                     
  rw [hf0_eq_one, norm_one, one_mul]
                                                    
  have h_prod_ge : ∏ ρ ∈ h_finite_zeros.toFinset, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat ≥
                   ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat := by
    apply Finset.prod_le_prod
                       
    · intro ρ hρ
      apply pow_nonneg
      apply R_over_R1_nonneg
                                            
    · intro ρ hρ
      have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
        exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
                                                   
      have h_ratio_ge : R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
                                                    
        have h_norm_abs_eq : ‖ρ‖ = norm ρ := by rfl
        rw [h_norm_abs_eq]
        exact lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros

      have h_3_2_pos : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
      have h_3_2_pos : (0 : ℝ) < (R/R1 : ℝ) := by linarith
      have h_ratio_pos : (0 : ℝ) ≤ R / ‖ρ‖ := by
        linarith [h_ratio_ge]
      exact pow_le_pow_left₀ R_over_R1_nonneg h_ratio_ge (analyticOrderAt f ρ).toNat
                                                          
  have h_3_2_prod_ge_1 : ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 :=
    lem_mod_lower_bound_1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_eq_one h_finite_zeros hR_lt_1
                                                     
  exact le_trans h_3_2_prod_ge_1 h_prod_ge
  assumption

lemma complex_mul_star_eq_norm_sq (z : ℂ) : z * star z = (‖z‖ ^ 2 : ℂ) := by
                                                      
  rw [Complex.star_def]
                                                    
  exact Complex.mul_conj' z

lemma lem_mod_Bf_eq_mod_f_on_boundary (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ = ‖f z‖ := by
  intro z hz
                                                                              
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := by
    intro h_in
                                                    
    have h_norm_le_R1 : ‖z‖ ≤ R1 := by simpa [sub_zero] using (h_in.1 : z ∈ Metric.closedBall (0 : ℂ) R1)
                                                  
    have h_norm_eq_R : ‖z‖ = R := by simpa using hz
    linarith [h_norm_le_R1, h_norm_eq_R, hR1_lt_R]
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_not_in]

  have h_each_factor_one : ∀ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ = 1 := by
    intro ρ hρ

    have z_ne_rho : z ≠ ρ := by
      intro h_eq
      have rho_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      have rho_bound : ‖ρ‖ ≤ R1 := by
        have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := rho_in_zeros.1
        rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
        simpa using h_in_ball
      have R1_lt_R : R1 < R := by linarith
      rw [← h_eq, hz] at rho_bound
      linarith [R1_lt_R]

    rw [Complex.norm_div]

    have z_conj_eq : z * star z = (R ^ 2 : ℂ) := by
      rw [complex_mul_star_eq_norm_sq z, hz, pow_two]

    have num_rewrite : (R : ℂ) - z * star ρ / (R : ℂ) = ((R : ℂ)^2 - z * star ρ) / (R : ℂ) := by
      have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (hR1_pos.trans hR1_lt_R).ne'
      field_simp [hRne]

    rw [num_rewrite, Complex.norm_div]

    have factor_eq : (R : ℂ)^2 - z * star ρ = z * star (z - ρ) := by
      rw [← z_conj_eq, star_sub]
      ring

    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    have hRpos : 0 < R := hR1_pos.trans hR1_lt_R
    have hnorm_denom : ‖z - ρ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z_ne_rho)
    simp [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, hnorm_denom, hRpos.ne']

  have h_prod_one : ∏ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat = 1 := by
                                        
    rw [← Finset.prod_congr rfl (fun ρ hρ => by rw [h_each_factor_one ρ hρ, one_pow])]
    rw [Finset.prod_const_one]

  rw [h_prod_one, mul_one]

lemma lem_Bf_bounded_on_boundary (B R R1 : ℝ) (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
                                             
  intro z hz
  have hz_le : ‖z‖ ≤ R := le_of_eq hz
  have h_eq :=
    lem_mod_Bf_eq_mod_f_on_boundary R R1 (by linarith) hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  simpa [h_eq] using hf_le_B z hz_le

lemma mem_closedBall_of_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  have : dist z (0 : ℂ) ≤ R := by simpa [Complex.dist_eq, sub_zero] using hz
  simpa [Metric.closedBall] using this

lemma closure_ball_eq_closedBall_center (R : ℝ) (hR : 0 < R) :
  closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := by
  simpa using (closure_ball (x := (0 : ℂ)) (r := R) (ne_of_gt hR))

lemma lem_max_mod_principle_for_Bf (B R : ℝ) (hB : 1 < B) (hR_pos : 0 < R)
    (fB : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ fB (Metric.closedBall (0 : ℂ) R))
  (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R → ‖fB z‖ ≤ B) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖fB z‖ ≤ B := by
  intro z hz
                               
  have hB0 : 0 ≤ B := le_of_lt (lt_trans zero_lt_one hB)
                                                                 
  have h_an_on_closure : AnalyticOn ℂ fB (closure (ballDR R)) := by
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using h_analytic.analyticOn
                                                                        
  have h_le :=
    lem_HardMMP R B hR_pos hB0 fB h_an_on_closure (by
      intro z hzR; exact h_bd_boundary z hzR)
                                                                                 
  have hz_cl : z ∈ closure (ballDR R) := by
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_of_norm_le hz
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using hz_closed
  exact h_le z hz_cl

lemma lem_Bf_bounded_in_disk_from_boundary (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  have hA := lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec
  exact lem_max_mod_principle_for_Bf B R hB (by linarith)
    (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) hA h_bd_boundary

lemma lem_Bf_bounded_in_disk_from_f (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  intro z hz
  have h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B :=
    lem_Bf_bounded_on_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  exact (lem_Bf_bounded_in_disk_from_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec h_bd_boundary) z hz

lemma lem_Bf_at_0_le_M (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B := by
  have h :=
    lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  have h0 : ‖(0 : ℂ)‖ ≤ R := by simpa using (le_of_lt (by linarith))
  simpa using h 0 h0

lemma lem_combine_bounds_on_Bf0 (B R R1 : ℝ) (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hBf0 : ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
  classical
                                       
  set K := h_finite_zeros.toFinset
                                                        
  have hf0_ne0 : f 0 ≠ 0 := by simp [hf0_eq_one]
  have hf0_norm : ‖f 0‖ = 1 := by simp [hf0_eq_one]
  have h_eval0 :=
    lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec
  have h_eval_prod :
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖
        = ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    rw [h_eval0, hf0_norm, one_mul]
                                             
  have h_base_ge : ∀ ρ ∈ K, R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
    intro ρ hρK
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := by simpa [K] using hρK
    simpa using
      (lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_ne0 ρ hρ_in)
                                          
  have R_over_R1_nonneg : 0 ≤ R/R1 := by
    have : 0 ≤ R := by linarith
    apply div_nonneg (by assumption) (le_of_lt hR1_pos)
  have h_prod_le :
      ∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat
        ≤ ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    refine lem_prod_ineq K
      (fun ρ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (fun ρ => (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat)
      ?h_nonneg ?h_le
    · intro ρ hρK; exact pow_nonneg (R_over_R1_nonneg) _
    · intro ρ hρK
      exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ R / R1) (h_base_ge ρ hρK) _
  have h_prod_le_B :
      ∏ ρ ∈ K, (R / R1: ℝ) ^ (analyticOrderAt f ρ).toNat ≤ B := by
    have h_right : ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat =
        ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ := by
      simp [h_eval_prod]
    exact le_trans h_prod_le (by simpa [h_right] using hBf0)
                                                                                       
  have h_prod_pow_sum :
      (∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
        = (R/R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum K (fun ρ => (analyticOrderAt f ρ).toNat) (R/R1 : ℝ))
                                                                          
  have h_natPow : (R / R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) ≤ B := by
    simpa [h_prod_pow_sum] using h_prod_le_B
                                                
  set S : ℕ := ∑ ρ ∈ K, (analyticOrderAt f ρ).toNat
  have h_natPowS : (R / R1 : ℝ) ^ S ≤ B := by simpa [S] using h_natPow
                                                     
  have h_rpowS : (R / R1 : ℝ) ^ (S : ℝ) ≤ B := by
                                                    
    simpa [(Real.rpow_natCast (R / R1 : ℝ) S)] using h_natPowS
                                                                    
  have h_cast_sum : (S : ℝ)
      = (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) := by
    simp [S]
                                       
  have : (R / R1 : ℝ) ^ (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ B := by
    simpa [h_cast_sum] using h_rpowS
  simpa [K] using this

lemma lem_jensen_inequality_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
                                
  have hf0_ne0 : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
                                                      
  have hBf0 :=
    lem_Bf_at_0_le_M B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec hf_le_B
                                                      
  let K := h_finite_zeros.toFinset
  have hres := lem_combine_bounds_on_Bf0 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hBf0
                                                                         
  simpa using hres

lemma lem_log_mono_inc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy

lemma lem_jensen_log_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R / R1) ≤ Real.log B := by
                                               
  set S : ℝ := ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)
                                    
  have hpow_le : (R / R1 : ℝ) ^ S ≤ B := by
    simpa [S] using
      (lem_jensen_inequality_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B)
                    
  have hbase_pos : 1 < (R / R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have hbase_pos' : 0 < (R / R1 : ℝ) := by
    have : 0 < R := by linarith
    linarith
                                                               
  have hxpos : 0 < (R / R1 : ℝ) ^ S := by
    simpa [S] using Real.rpow_pos_of_pos hbase_pos' S
                              
  have hlog_le : Real.log ((R / R1 : ℝ) ^ S) ≤ Real.log B :=
    lem_log_mono_inc hxpos hpow_le
                           
  have hlog_rpow : Real.log ((R / R1 : ℝ) ^ S) = S * Real.log (R / R1) := by
    simpa using (Real.log_rpow hbase_pos' S)
             
  simpa [S, hlog_rpow] using hlog_le

lemma lem_sum_m_rho_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ (1/Real.log (R/R1)) * Real.log B := by
  have h_div_log : (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R/R1) ≤ Real.log B := by
    apply lem_jensen_log_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B
  have log_pos' : R/R1 > 1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have log_pos : Real.log (R/R1) > 0 := by exact Real.log_pos log_pos'
  calc
    ∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat
    _ = 1 / Real.log (R / R1) * (Real.log (R / R1) * (∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat)) := by
      field_simp [ne_of_gt log_pos]
    _ ≤ 1 / Real.log (R / R1) * Real.log B := by
      gcongr
      rw [mul_comm]
      exact h_div_log

variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)

lemma Lf_is_analytic
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec)
                     (Metric.closedBall (0 : ℂ) r) := by
  unfold Lf
  exact (Classical.choose_spec (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
    )
  )).1

lemma Lf_at_0_is_0
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec 0 = 0 := by
  unfold Lf
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  let log_exists := log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
  exact (Classical.choose_spec log_exists).2.1

lemma lem_BCII {L : ℂ → ℂ} {r M r₁ : ℝ}
    (hr_pos : 0 < r)
    (hM_pos : 0 < M)
    (hr₁_pos : 0 < r₁)
    (hr₁_lt_r : r₁  < r)
    (hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U)
    (hL0 : L 0 = 0)
    (hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r₁) :
norm (deriv L z) ≤ (16 * M * r ^ 2) / ((r - r₁) ^ 3) := by
  apply borel_caratheodory_II hr_pos hM_pos hr₁_pos hr₁_lt_r hL_domain hL0 hre_L_le_M hz

lemma re_Lf_as_diff_of_log_mods
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) =
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) -
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)) := by
  intro z hz
                                                                                                                      
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  have h_Bf_analytic : AnalyticOnNhd ℂ B_f (Metric.closedBall (0 : ℂ) R) :=
    Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_Bf_ne_zero : ∀ w ∈ Metric.closedBall (0 : ℂ) R1, B_f w ≠ 0 := by
    intro w hw
    exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw

  have h_log_exists := log_of_analytic hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 h_Bf_analytic h_Bf_ne_zero
  have h_choose_spec := Classical.choose_spec h_log_exists

  have h_Lf_def : Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec = Classical.choose h_log_exists := by
    unfold Lf
    simp only [B_f]

  rw [h_Lf_def]
  exact (h_choose_spec.2.2.2 z hz).symm

lemma log_Bf_le_log_B
    (B R R1 : ℝ)
    (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_pos : ∀ z, norm z ≤ R1 →
                0 < norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z))
    (h_Bf_bound : ∀ z, norm z ≤ R1 →
                  norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
  intro z hz
  apply Real.log_le_log
  · exact h_Bf_pos z hz
  · exact h_Bf_bound z hz

lemma log_Bf_le_log_B2
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_bound : ∀ z, ‖z‖ ≤ R →
                  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z, ‖z‖ ≤ R1 →
      Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖) ≤ Real.log B := by
                                 
  apply log_Bf_le_log_B B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  ·                                                  
    intro z hz
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) R1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz
    have hBf_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz_mem
    exact norm_pos_iff.mpr hBf_ne_zero
  ·                                                    
    intro z hz
    have hz_le_R : ‖z‖ ≤ R := by linarith [hz, hR1_lt_R]
    exact h_Bf_bound z hz_le_R

lemma log_Bf_le_log_B3
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
                                                                              
  apply log_Bf_le_log_B2 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
                                                       
  apply lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec
                                                               
  exact h_f_bound

lemma log_Bf0_ge_0
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    0 ≤ Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖) := by
                                                          
  have h_pos : 0 < (1 : ℝ) := by norm_num
  have h_Bf_ge_1 : 1 ≤ ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖ :=
    lem_mod_Bf_at_0_ge_1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_log_mono := lem_log_mono_inc h_pos h_Bf_ge_1
  rw [Real.log_one] at h_log_mono
  exact h_log_mono

lemma re_Lf_le_log_B
    (B r R R1 : ℝ)
    (hB : 1 < B)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r →
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) ≤ Real.log B := by
  intro z hz
                                                                                         
  rw [re_Lf_as_diff_of_log_mods r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z]
  ·                                           
                                                                 
    have hz_apply_BC_to_Lfle_R1 : ‖z‖ ≤ R1 := by linarith [hz, hr_lt_R1]
    have h1 := log_Bf_le_log_B3 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound z hz_apply_BC_to_Lfle_R1
    have h2 := log_Bf0_ge_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
    linarith
  ·                                            
    exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hz)

lemma apply_BC_to_Lf
    (B r1 r R R1 : ℝ)
    (hB : 1 < B)
    (hr1_pos : 0 < r1)
    (hr1_lt_r : r1 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r1 →
      norm (deriv (Lf (lt_trans hr1_pos hr1_lt_r : 0 < r) hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z) ≤
      (16 * Real.log B * r^2) / (r - r1)^3 := by
  classical
  intro z hz
                                        
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
                                                              
  let L := Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
                                                                   
  have h_analytic_nhd :=
    Lf_is_analytic r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
                                                                             
  let U : Set ℂ :=
    { y | ∃ x ∈ Metric.closedBall (0 : ℂ) r, ∃ s : ℝ, 0 < s ∧ y ∈ Metric.ball x s ∧
        AnalyticOnNhd ℂ L (Metric.ball x s) }
  have hU_open : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hyin, hAnaBall⟩
    have hnhds : Metric.ball x s ∈ nhds y := (Metric.isOpen_ball.mem_nhds hyin)
    exact Filter.mem_of_superset hnhds (by intro z hz; exact ⟨x, hxCB, s, hs_pos, hz, hAnaBall⟩)
  have hCB_subset : Metric.closedBall (0 : ℂ) r ⊆ U := by
    intro x hx
    have hAt : AnalyticAt ℂ L x := h_analytic_nhd x hx
    rcases AnalyticAt.exists_ball_analyticOnNhd hAt with ⟨s, hs_pos, hAnaBall⟩
    have hx_in_ball : x ∈ Metric.ball x s := by
      simpa [Metric.mem_ball, dist_self] using hs_pos
    exact ⟨x, hx, s, hs_pos, hx_in_ball, hAnaBall⟩
  have hDiffU : DifferentiableOn ℂ L U := by
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hy_in, hAnaBall⟩
                                                          
    have hAt : AnalyticAt ℂ L y := hAnaBall y hy_in
    exact (AnalyticAt.differentiableAt hAt).differentiableWithinAt
                        
  have hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U :=
    ⟨U, hU_open, hCB_subset, hDiffU⟩
             
  have hL0 : L 0 = 0 := by
    simpa [L] using (Lf_at_0_is_0 r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
                                                
  have hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ Real.log B := by
    intro w hw
    have hw' : norm w ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact re_Lf_le_log_B B r R R1 hB hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound w hw'
                        
  have hz' : z ∈ Metric.closedBall 0 r1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
                                
  have hBC :=
    lem_BCII hr_pos (Real.log_pos hB) hr1_pos hr1_lt_r hL_domain hL0 hre_L_le_M hz'
             
  simpa [L] using hBC

lemma logDerivconst {a : ℂ} {g : ℂ → ℂ} (ha : a ≠ 0) :
    ∀ z, logDeriv (fun w ↦ a * g w) z = logDeriv g z := by
  intro z
  exact logDeriv_const_mul z a ha

lemma Lf_deriv_is_logBf_deriv (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                           Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) z =
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) z := by
  intro z _
                                                      
  have h_eq : (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) =
              (fun w ↦ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ *
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) := by
    ext w
    rw [div_eq_mul_inv]
    ring
  rw [h_eq]
                                               
  have h0_in_ball : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R1 := by
    simp [Metric.mem_closedBall]
    exact le_of_lt hR1_pos
  have h_Bf0_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec 0 h0_in_ball
                                      
  have h_inv_ne_zero : (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ ≠ 0 :=
    inv_ne_zero h_Bf0_ne_zero
                        
  exact logDerivconst h_inv_ne_zero z

lemma deriv_over_fun_is_logDeriv {g : ℂ → ℂ} : ∀ z, deriv g z / g z = logDeriv g z := by
  intro z
  rfl

lemma logDerivmul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z)
    (hf_ne : f z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ f w * g w) z = logDeriv f z + logDeriv g z := by
  exact logDeriv_mul z hf_ne hg_ne hf hg

lemma logDerivprod {K : Finset ℂ} {g : ℂ → ℂ → ℂ} {z : ℂ}
    (hg_diff : ∀ ρ ∈ K, DifferentiableAt ℂ (g ρ) z)
    (hg_ne : ∀ ρ ∈ K, g ρ z ≠ 0) :
    logDeriv (fun w ↦ ∏ ρ ∈ K, g ρ w) z = ∑ ρ ∈ K, logDeriv (g ρ) z := by
  simpa only [Finset.prod_fn] using logDeriv_prod hg_ne hg_diff

lemma logDerivdiv {h g : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (hg : DifferentiableAt ℂ g z)
    (hh_ne : h z ≠ 0) (hg_ne : g z ≠ 0) :
    logDeriv (fun w ↦ h w / g w) z = logDeriv h z - logDeriv g z := by
  exact logDeriv_div z hh_ne hg_ne hh hg

lemma logDerivfunpow {g : ℂ → ℂ} {z : ℂ} {m : ℕ}
    (hg : DifferentiableAt ℂ g z) :
    logDeriv (fun w ↦ (g w) ^ m) z = m * logDeriv g z := by
  exact logDeriv_fun_pow hg m

lemma z_minus_rho_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    z - ρ ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ w - ρ) z := by
  intro ρ hρ z hz
  have hz_pair := (Set.mem_sdiff z).1 hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_pair.1
  have hz_notK : z ∉ zerosetKfR R1 (by linarith) f := hz_pair.2
                               
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz_notK (by simpa [h_eq] using hρ)
  have h_nonzero : z - ρ ≠ 0 := sub_ne_zero.mpr hz_ne_rho
                                        
  have hdiff : DifferentiableAt ℂ (fun w => w) z := differentiableAt_fun_id
  have hdiff_sub : DifferentiableAt ℂ (fun w => w - ρ) z := hdiff.sub_const ρ
  exact ⟨h_nonzero, hdiff_sub⟩

lemma blaschke_num_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
    R - (star ρ) * z / R ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := by
  intro ρ hρ z hz
  constructor
  · intro hzero
    have hRne : (R : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (hR1_pos.trans hR1_lt_R)))
                                                                          
    have heq : (R : ℂ) = (star ρ) * z / (R : ℂ) := sub_eq_zero.mp hzero
    have hmul := congrArg (fun t : ℂ => t * (R : ℂ)) heq
    have heq_mul : (R : ℂ) * (R : ℂ) = (star ρ) * z := by
                                     
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hRne] using hmul
                              
    have hnorm_eq : ‖(R : ℂ)‖ * ‖(R : ℂ)‖ = ‖ρ‖ * ‖z‖ := by
      simpa [Complex.norm_mul, Complex.norm_conj] using congrArg (fun t : ℂ => ‖t‖) heq_mul
                                   
    have hz_norm_le : ‖z‖ ≤ R := by
      have hz' : dist z (0 : ℂ) ≤ R := (Metric.mem_closedBall.mp hz)
      simpa [dist_eq_norm] using hz'
    have hrho_norm_le : ‖ρ‖ ≤ R1 := by
      rcases hρ with ⟨hρ_ball, _hρ_zero⟩
      have : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_ball)
      simpa [dist_eq_norm] using this
    have hz_nonneg : 0 ≤ ‖z‖ := by simp
    have hR1_nonneg : 0 ≤ R1 := le_of_lt hR1_pos
    have hle : ‖ρ‖ * ‖z‖ ≤ R1 * R := by
      have h1 : ‖ρ‖ * ‖z‖ ≤ R1 * ‖z‖ := mul_le_mul_of_nonneg_right hrho_norm_le hz_nonneg
      have h2 : R1 * ‖z‖ ≤ R1 * R := mul_le_mul_of_nonneg_left hz_norm_le hR1_nonneg
      exact le_trans h1 h2
                                            
    have hnorm_R : ‖(R : ℂ)‖ = R := by
      have h1 : ‖(R : ℂ)‖ = |R| := by simp
      simp [abs_of_pos (hR1_pos.trans hR1_lt_R)]
                                         
    have : R * R = ‖ρ‖ * ‖z‖ := by simpa [hnorm_R] using hnorm_eq
    have hle' : R * R ≤ R1 * R := by simpa [this] using hle
                                                                     
    have hposR : 0 < R := hR1_pos.trans hR1_lt_R
    have hposRR : 0 < R * R := by nlinarith [hposR]
    have hlt : R1 * R < R * R := by
      exact mul_lt_mul_of_pos_right hR1_lt_R hposR
    exact (lt_irrefl _ (lt_of_le_of_lt hle' hlt))
  ·                                      
    have h_const : DifferentiableAt ℂ (fun _ : ℂ => (R : ℂ)) z := by
      simp
    have h_id : DifferentiableAt ℂ (fun w : ℂ => w) z := by
      simp
    have h_mul : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w) z := by
      simpa using h_id.const_mul (star ρ)
    have h_div : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w / (R : ℂ)) z := by
      simpa [div_eq_mul_inv] using h_mul.mul_const ((R : ℂ)⁻¹)
    simpa using h_const.sub h_div

lemma blaschke_frac_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (R - (star ρ) * z / R) / (z - ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro ρ hρ z hz
                                                 
  have hden := z_minus_rho_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz
  have hden_ne : z - ρ ≠ 0 := hden.1
  have hden_diff : DifferentiableAt ℂ (fun w ↦ w - ρ) z := hden.2
                                                  
  have hz_in_small : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_small : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_in_small.1
                                                       
  have hz_dist_le_small : dist z (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hz_small
  have hRle : R ≤ 1 := le_of_lt hR_lt_1
  have hR1_le_R : R1 ≤ R := le_of_lt hR1_lt_R
  have hR1_le_1 : R1 ≤ 1 := le_trans hR1_le_R hRle
  have hz_ball1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have hz_le1 : dist z (0 : ℂ) ≤ 1 := le_trans hz_dist_le_small hR1_le_1
    simpa [Metric.mem_closedBall] using hz_le1
                                               
  have hz_ballR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : dist z (0 : ℂ) ≤ R := le_trans hz_dist_le_small (le_of_lt hR1_lt_R)
    simpa [Metric.mem_closedBall] using hz_le_R
  have hnum := blaschke_num_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz_ballR
  have hnum_ne : R - (star ρ) * z / R ≠ 0 := hnum.1
  have hnum_diff : DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := hnum.2
             
  refine And.intro ?_ ?_
  · intro h
    have h' : (R - (star ρ) * z / R) * (z - ρ)⁻¹ = 0 := by
      simpa [div_eq_mul_inv] using h
    rcases mul_eq_zero.mp h' with hnum0 | hinv0
    · exact hnum_ne hnum0
    · exact hden_ne (inv_eq_zero.mp hinv0)
  · exact hnum_diff.div hden_diff hden_ne

lemma blaschke_pow_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro ρ hρ z hz
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ z hz
  rcases hfrac with ⟨hne, hdiff⟩
  constructor
  · exact pow_ne_zero _ hne
  · convert (preTransparency := .instances) hdiff.pow ((analyticOrderAt f ρ).toNat) using 1
    all_goals try with_reducible_and_instances rfl

lemma blaschke_prod_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (∏ ρ ∈ h_finite_zeros.toFinset, ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  classical
  constructor
  ·                                
    have hne_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.1
    exact (Finset.prod_ne_zero_iff).2 hne_each
  ·                                    
    have hdiff_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        DifferentiableAt ℂ
          (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.2
                                                                 
    have hdiff :=
      (DifferentiableAt.finsetProd (u := h_finite_zeros.toFinset)
        (f := fun ρ => fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        (x := z) hdiff_each)
    have hfun_eq :
        (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        =
        (∏ ρ ∈ h_finite_zeros.toFinset,
            (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)) := by
      funext w
      simp [Finset.prod_apply]
    exact hfun_eq.symm ▸ hdiff

lemma f_diff_nonzero_outside_Kf {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (_h_finite_zeros : (zerosetKfR R1 (by linarith ) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    f z ≠ 0 ∧ DifferentiableAt ℂ f z := by
  intro z hz
                                            
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 := hz'.1
  have hz_notin : z ∉ zerosetKfR R1 (by linarith) f := hz'.2
                 
  have hz_nonzero : f z ≠ 0 := by
    intro hfz
    exact hz_notin ⟨hz_in_R1, hfz⟩
                                                               
  have hR1_lt_1 : R1 < 1 := by linarith
  have hsubset1 :
      Metric.closedBall (0 : ℂ) R1 ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball hR1_lt_1
  have hz_in_ball1 : z ∈ Metric.ball (0 : ℂ) 1 := hsubset1 hz_in_R1
  have hz_in_1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.ball_subset_closedBall hz_in_ball1
  have hAna : AnalyticAt ℂ f z := h_f_analytic z hz_in_1
  have hDiff : DifferentiableAt ℂ f z := hAna.differentiableAt
  exact ⟨hz_nonzero, hDiff⟩

lemma logDeriv_fprod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ f w * ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    logDeriv f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hf' := f_diff_nonzero_outside_Kf (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hf' with ⟨hf_ne, hf_diff⟩
  have hg' := blaschke_prod_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  rcases hg' with ⟨hg_ne, hg_diff⟩
  simpa using
    (logDerivmul (f:=f) (g:=fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) (z:=z)
      hf_diff hg_diff hf_ne hg_ne)

lemma div_mul_eq_mul_mul_inv_fun {α} (f A B : α → ℂ) :
  (fun w => (f w / A w) * B w) = (fun w => f w * (B w * (A w)⁻¹)) := by
  funext w
  simp [div_eq_mul_inv, mul_comm, mul_left_comm]

lemma prod_num_mul_inv_den_eq_prod_ratio_fun_mem
  (K : Finset ℂ) (N D : ℂ → ℂ → ℂ) (m : ℂ → ℕ) :
  (fun w ↦ (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹)
  = (fun w ↦ ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ))) := by
  funext w
  classical
  calc
    (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) / (∏ ρ ∈ K, (D ρ w) ^ (m ρ)) := by
          simp [div_eq_mul_inv]
    _ = ∏ ρ ∈ K, ((N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ)) := by
          simp
    _ = ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ)) := by
          refine Finset.prod_congr rfl ?_
          intro ρ hρ
          have hpow_div :
              (N ρ w / D ρ w) ^ (m ρ)
                = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
            calc
              (N ρ w / D ρ w) ^ (m ρ)
                  = (N ρ w * (D ρ w)⁻¹) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
              _ = (N ρ w) ^ (m ρ) * ((D ρ w)⁻¹) ^ (m ρ) := by
                        simpa using (mul_pow (N ρ w) ((D ρ w)⁻¹) (m ρ))
              _ = (N ρ w) ^ (m ρ) * ((D ρ w) ^ (m ρ))⁻¹ := by
                        simp
              _ = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
          simpa using hpow_div.symm

lemma logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
  (hfg : f =ᶠ[nhds z] g) : logDeriv f z = logDeriv g z := by
                                                                                         
  have hval : f z = g z := Filter.EventuallyEq.eq_of_nhds hfg
  have hderiv_eq_ev : deriv f =ᶠ[nhds z] deriv g := hfg.deriv
  have hderiv : deriv f z = deriv g z := Filter.EventuallyEq.eq_of_nhds hderiv_eq_ev
                                                      
  have hf := deriv_over_fun_is_logDeriv (g := f) z
  have hg := deriv_over_fun_is_logDeriv (g := g) z
  simp [hf.symm, hg.symm, hval, hderiv]

lemma logDeriv_Bf_is_sum :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \
          zerosetKfR R1 (by linarith) f,
    logDeriv (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z =
    logDeriv f z +
      logDeriv
        (fun w ↦
          ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  classical
  intro z hz
                  
  set K : Finset ℂ := h_finite_zeros.toFinset
                                                                    
  let A : ℂ → ℂ := fun w => ∏ ρ ∈ K, (w - ρ) ^ (analyticOrderAt f ρ).toNat
  let BN : ℂ → ℂ := fun w => ∏ ρ ∈ K, (R - (star ρ) * w / R) ^ (analyticOrderAt f ρ).toNat
  let RatProd : ℂ → ℂ :=
    fun w => ∏ ρ ∈ K, ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat
                                                                              
  set S : Set ℂ := zerosetKfR R1 (by linarith) f
  have hS_fin : S.Finite := h_finite_zeros
  have hU_open : IsOpen Sᶜ := hS_fin.isClosed.isOpen_compl
  have hz_notin : z ∉ S := by
    rcases hz with ⟨_, hnotin⟩; exact hnotin
  have hzU : z ∈ Sᶜ := by simpa [Set.mem_compl] using hz_notin
  have hU_mem : Sᶜ ∈ nhds z := hU_open.mem_nhds hzU
  have h_ev :
      (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
        =ᶠ[nhds z]
      (fun w ↦ f w * RatProd w) := by
    refine Filter.eventually_of_mem hU_mem ?_
    intro w hwU
    have hw_notin : w ∉ S := by simpa [Set.mem_compl] using hwU
                                                         
    have hBf_w :
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w * BN w := by
      simp [Bf, BN, K]
    have hCf_w :
        Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = f w / A w := by
      simp [Cf, S, A, K, hw_notin]
                                                           
    have h_eq1 := div_mul_eq_mul_mul_inv_fun (f := f) (A := A) (B := BN)
    have h_eq1_w : (f w / A w) * BN w = f w * (BN w * (A w)⁻¹) := by
      simpa using congrArg (fun g : (ℂ → ℂ) => g w) h_eq1
    have h_eq2 :=
      prod_num_mul_inv_den_eq_prod_ratio_fun_mem
        (K := K)
        (N := fun ρ w ↦ (R - (star ρ) * w / R))
        (D := fun ρ w ↦ (w - ρ))
        (m := fun ρ ↦ (analyticOrderAt f ρ).toNat)
    have h_eq2_w : BN w * (A w)⁻¹ = RatProd w := by
      simpa [BN, A, RatProd] using congrArg (fun g : (ℂ → ℂ) => g w) h_eq2
                           
    calc
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = (f w / A w) * BN w := by simpa [hCf_w] using hBf_w
      _ = f w * (BN w * (A w)⁻¹) := h_eq1_w
      _ = f w * RatProd w := by simp [h_eq2_w]
                                       
  have hlog_congr := logDeriv_congr_of_eventuallyEq (f := fun w ↦
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
      (g := fun w ↦ f w * RatProd w) (z := z) h_ev
                                  
  have hsum :=
    (logDeriv_fprod_is_sum (R:=R) (R1:=R1) (f:=f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz)
  simpa [RatProd, K] using hlog_congr.trans hsum

lemma logDeriv_def_as_frac {f : ℂ → ℂ} {z : ℂ}
    (_hf : DifferentiableAt ℂ f z) (_hf_ne : f z ≠ 0) :
    logDeriv f z = deriv f z / f z := by
  simp [logDeriv]

theorem ball_containment {r R1 : ℝ} (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (z : ℂ) (hz : z ∈ Metric.closedBall 0 r) : z ∈ Metric.closedBall 0 R1 := by
  simp at *
  exact le_trans hz (le_of_lt hr_lt_R1)

theorem in_r_minus_kf {R1 r : ℝ} {f : ℂ → ℂ}
  (hr_pos : 0 < r)
  (hr_lt_R1 : r < R1)
  (z : ℂ)
  (hz : z ∈ Metric.closedBall 0 r \ zerosetKfR R1 (by linarith) f) :
   z ∈ Metric.closedBall 0 R1 \ zerosetKfR R1 (by linarith) f := by
  obtain ⟨h1, h2⟩ := hz
  have : z ∈ Metric.closedBall 0 R1 := by
    apply ball_containment hr_pos hr_lt_R1 z h1
  constructor <;> assumption

lemma Lf_deriv_step1 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                                ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
                                  
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r ∧ z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) r := hz'.1
                               
  have hLf :=
    
    (Lf_deriv_is_logBf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
      z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)).symm
                                   
  have hsum :
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z =
      logDeriv f z +
        logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    have h :=
      (logDeriv_Bf_is_sum (R := R) (R1 := R1) (r := r) (f := f) (h_σ := h_σ)
        hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros) z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
    simpa using h
                                                                              
  obtain ⟨hf_ne, hfdiff⟩ :=
    f_diff_nonzero_outside_Kf (R := R) (R1 := R1) (f := f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have hfrac : logDeriv f z = deriv f z / f z :=
    logDeriv_def_as_frac (f := f) (z := z) hfdiff hf_ne

  have hLf_eq_logDerivBf :
      deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z := by

    have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r := hz_ball
                                                               
    let B_f : ℂ → ℂ :=
      fun w => Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
    let log_exists := log_of_analytic
      (r1 := r) (R' := R1) (R := R)
      hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
      (B := B_f)
      (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1
                f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
      (hB_ne_zero := by
        intro w hw
        exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1
          f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw)
    have hderiv_all : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
        deriv (Classical.choose log_exists) w = deriv B_f w / B_f w :=
      (Classical.choose_spec log_exists).2.2.1
    have hderiv_Lf :
        deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos
                    h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
          = deriv B_f z / B_f z := by
                                                                            
      unfold Lf
                                                                                                       
      simpa using hderiv_all z hz_in_r
                                                  
    have h_as_log : deriv B_f z / B_f z = logDeriv B_f z :=
      deriv_over_fun_is_logDeriv (g := B_f) z
               
    simpa [B_f] using hderiv_Lf.trans h_as_log

  calc
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
        = logDeriv (fun w ↦
            Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
              h_finite_zeros h_σ w) z := hLf_eq_logDerivBf
    _ = logDeriv f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := hsum
    _ = deriv f z / f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
            simp [hfrac]

lemma logDeriv_prod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, logDeriv (fun w ↦
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hdiff : ∀ ρ ∈ h_finite_zeros.toFinset,
      DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.2
  have hne : ∀ ρ ∈ h_finite_zeros.toFinset,
      ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.1
  simpa using
    (logDerivprod (K := h_finite_zeros.toFinset)
      (g := fun ρ w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
      (z := z) hdiff hne)

lemma logDeriv_power_is_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    (analyticOrderAt f ρ).toNat * logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz ρ hρFin
  have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    simpa using (h_finite_zeros.mem_toFinset.mp hρFin)
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρmem z hz
  rcases hfrac with ⟨_hneq, hdiff⟩
  simpa using
    (logDerivfunpow (g := fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) (z := z)
      (m := (analyticOrderAt f ρ).toNat) hdiff)

lemma logDeriv_prod_is_sum_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have hsum :=
    logDeriv_prod_is_sum (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  exact
    logDeriv_power_is_mul (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ

lemma Lf_deriv_step2 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                                       logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have h1 :=
    Lf_deriv_step1 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  have hsum :=
    logDeriv_prod_is_sum_mul (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have h2 := congrArg (fun t => deriv f z / f z + t) hsum
  exact h1.trans h2

lemma logDeriv_Blaschke_is_diff {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
    logDeriv (fun w ↦ R - (star ρ) * w / R) z - logDeriv (fun w ↦ w - ρ) z := by
  intro z hz ρ hρ
  have hρ_set : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (Set.Finite.mem_toFinset (hs := h_finite_zeros) (a := ρ)).mp hρ
  rcases hz with ⟨hz_in, hz_notin⟩
  have hden := z_minus_rho_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z ⟨hz_in, hz_notin⟩
  rcases hden with ⟨hden_nz, hden_diff⟩
  have hz_le : ‖z‖ ≤ R1 := by
    simpa [Metric.closedBall, dist_eq_norm] using hz_in
  have hle1 : R1 < 1 := by linarith [hR1_lt_R, hR_lt_1]
  have hz_in1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have : ‖z‖ ≤ 1 := le_of_lt (hz_le.trans_lt hle1)
    simpa [Metric.closedBall, dist_eq_norm] using this
  have hz_inR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : ‖z‖ ≤ R := by
      calc ‖z‖ ≤ R1 := hz_le
      _ ≤  R := le_of_lt hR1_lt_R
    simpa [Metric.closedBall, dist_eq_norm] using hz_le_R
  have hnum := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z hz_inR
  rcases hnum with ⟨hnum_nz, hnum_diff⟩
  simpa using
    (logDerivdiv (hh := hnum_diff) (hg := hden_diff) (hh_ne := hnum_nz) (hg_ne := hden_nz))

lemma logDeriv_linear {a b : ℂ} {z : ℂ} (_ha : a ≠ 0) (_hz : z ≠ -b/a) :
    logDeriv (fun w ↦ a * w + b) z = a / (a * z + b) := by
                                 
  have h_id : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id _
  have h_mul' : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa [one_mul] using (h_id.const_mul a)
  have h_deriv_mul : deriv (fun w : ℂ => a * w) z = a := h_mul'.deriv
                                
  simp [logDeriv]

lemma logDeriv_denominator {ρ : ℂ} {z : ℂ} (hz : z ≠ ρ) :
    logDeriv (fun w ↦ w - ρ) z = 1 / (z - ρ) := by
  have h :=
    logDeriv_linear (a := (1 : ℂ)) (b := -ρ) (z := z)
      (_ha := by simp)
      (_hz := by simpa using hz)
  simpa [one_mul, sub_eq_add_neg] using h

lemma logDeriv_numerator_pre {R : ℝ} {ρ : ℂ} {z : ℂ} :
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = -(star ρ) / R / (R - (star ρ) * z / R) := by
  classical
                                                  
  let a : ℂ := -(star ρ) / (R : ℂ)
  let b : ℂ := (R : ℂ)
  have hlin : (fun w : ℂ ↦ (R : ℂ) - (star ρ) * w / (R : ℂ)) = (fun w : ℂ ↦ b + a * w) := by
    funext w
                         
    simp [a, b, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm]
                                        
  have hderiv_add : deriv (fun w : ℂ => b + a * w) z =
      deriv (fun _ : ℂ => b) z + deriv (fun y : ℂ => a * y) z := by
    simp
  have hderiv_ab : deriv (fun w : ℂ => b + a * w) z = a := by
    simp [deriv_const, mul_comm]
                                                            
  simp [logDeriv, sub_eq_add_neg, div_eq_mul_inv,
         mul_comm, mul_left_comm, mul_assoc, add_comm]

lemma star_ne_zero_of_ne_zero {ρ : ℂ} (hρ : ρ ≠ 0) : star ρ ≠ 0 := by

  intro h
                                          
  have : ρ = 0 := (star_eq_zero).1 h
  exact hρ this

lemma field_identity_general {K : Type*} [Field K] {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (_hden : a - c*b/a ≠ 0) : (-(b/a)) / (a - c*b/a) = (1 : K) / (c - a^2/b) := by
                                               
  have hmul : (-(a / b) : K) ≠ 0 := by
    have hdiv_ne : a / b ≠ 0 := div_ne_zero ha hb
    exact neg_ne_zero.mpr hdiv_ne
  have hnum : (-(b/a) * (-(a/b))) = (1 : K) := by
    calc
      (-(b/a) * (-(a/b))) = (b/a) * (a/b) := by simp
      _ = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have hOne : (b/a) * (a/b) = (1 : K) := by
    calc
      (b/a) * (a/b) = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have haab : a * (a / b) = a^2 / b := by
    simp [div_eq_mul_inv, pow_two, mul_assoc]
  have hcbab : (c * b / a) * (a / b) = c := by
    calc
      (c * b / a) * (a / b) = (c * (b / a)) * (a / b) := by simp [div_eq_mul_inv, mul_assoc]
      _ = c * ((b / a) * (a / b)) := by simp [mul_assoc]
      _ = c * 1 := by simp [hOne]
      _ = c := by simp
  have hdenom : ((a - c*b/a) * (-(a/b))) = c - a^2 / b := by
    calc
      ((a - c*b/a) * (-(a/b))) = -((a - c*b/a) * (a / b)) := by simp [mul_neg]
      _ = -(a * (a / b) - (c * b / a) * (a / b)) := by simp [sub_mul]
      _ = (c * b / a) * (a / b) - a * (a / b) := by simp [neg_sub]
      _ = c - a^2 / b := by simp [hcbab, haab]
  calc
    (-(b/a)) / (a - c*b/a)
        = (-(b/a) * (-(a/b))) / ((a - c*b/a) * (-(a/b))) := by
          simpa using
            (mul_div_mul_right (a := (-(b / a))) (b := (a - c * b / a)) (c := (-(a / b))) hmul).symm
    _ = 1 / ((a - c*b/a) * (-(a/b))) := by simp [hnum]
    _ = 1 / (c - a^2/b) := by simp [hdenom]

lemma complex_identity_from_field {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hρ : ρ ≠ 0) (hden : (R:ℂ) - (star ρ) * z / R ≠ 0) : (-(star ρ) / (R:ℂ)) / ((R:ℂ) - (star ρ) * z / R) = (1 : ℂ) / (z - (R:ℂ)^2 / (star ρ)) := by
  have ha : (R : ℂ) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr hR)
  have hb : star ρ ≠ 0 := star_ne_zero_of_ne_zero hρ
  have hden' : (R : ℂ) - z * (star ρ) / (R : ℂ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hden
  have h := field_identity_general (K := ℂ) (a := (R : ℂ)) (b := star ρ) (c := z) ha hb hden'
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h

lemma logDeriv_numerator_rearranged {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hrho : ρ ≠ 0) (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0) : -(star ρ) / R / ((R : ℂ) - (star ρ) * z / R) = 1 / (z - (R : ℂ)^2 / (star ρ)) := by
  simpa using (complex_identity_from_field (R:=R) (ρ:=ρ) (z:=z) (hR:=hR) (hρ:=hrho) (hden:=h_denom_ne_zero))

lemma logDeriv_numerator {R : ℝ} {ρ : ℂ} {z : ℂ}
    (hR : R ≠ 0)
    (hrho : ρ ≠ 0)
    (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0):
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = 1 / (z - R^2 / (star ρ)) := by
  rw [logDeriv_numerator_pre, logDeriv_numerator_rearranged]
  <;> assumption

lemma logDeriv_Blaschke_is_diff_frac {R R1 : ℝ} {f : ℂ → ℂ}
     (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (h_f_zero : f 0 = 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ h_finite_zeros.toFinset,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f , logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
         1 / (z - R^2 / (star ρ)) - 1 / (z - ρ) := by
  intro ρ hρ z hz
                                                                         
  have h_div := logDeriv_Blaschke_is_diff (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ
                                                                     
  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (h_finite_zeros.mem_toFinset).mp hρ
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h_eq
                                                            
    have : f 0 = 0 := by simpa [h_eq] using hρ_mem.2
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (this.symm.trans h_f_zero)
  have hR_ne_zero : R ≠ 0 := ne_of_gt (hR1_pos.trans hR1_lt_R)
  have h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0 := by
                                                  
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R := by
      have hle : R1 < R := hR1_lt_R
      apply Metric.closedBall_subset_closedBall (le_of_lt hle)
      exact hz.1
    have h := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ_mem z hz_ball
    exact h.1
  have h_num := logDeriv_numerator hR_ne_zero hρ_ne_zero h_denom_ne_zero
                                                        
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz.2 (by simpa [h_eq] using hρ_mem)
  have h_den := logDeriv_denominator hz_ne_rho
                                
  rw [h_div, h_num, h_den]

lemma Lf_deriv_step3 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat * (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) := by
  intro z hz
                                                          
  rw [Lf_deriv_step2 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  exact logDeriv_Blaschke_is_diff_frac hR1_pos hR1_lt_R hR_lt_1 h_f_zero h_f_analytic h_finite_zeros ρ hρ z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)

lemma sum_rearranged {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (_h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) := by
  intro z hz
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext ρ
  rw [mul_sub, mul_one_div, mul_one_div]

lemma Lf_deriv_final_formula :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) +
                      ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
                                                               
  rw [Lf_deriv_step3 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
                                                  
  rw [sum_rearranged hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz]
                    
  ring

lemma rearrange_Lf_deriv :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) =
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
                                                                               
  have h_final := Lf_deriv_final_formula hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  rw [h_final]
  ring

lemma target_inequality_setup :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
  ‖deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
  ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ +
  ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := by
  intro z hz

  have hrearr := rearrange_Lf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz

  rw [hrearr]
  exact norm_sub_le _ _

lemma norm_div_eq (a b : ℂ) (_hb : b ≠ 0) : ‖a / b‖ = ‖a‖ / ‖b‖ := by
  calc
    ‖a / b‖ = ‖a * b⁻¹‖ := by simp [div_eq_mul_inv]
    _ = ‖a‖ * ‖b⁻¹‖ := norm_mul _ _
    _ = ‖a‖ * ‖b‖⁻¹ := by simp [norm_inv]
    _ = ‖a‖ / ‖b‖ := by simp [div_eq_mul_inv]

lemma norm_Rsq_div_conj (R : ℝ) (ρ : ℂ) (hρ : ρ ≠ 0) : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ := by
  have hb : star ρ ≠ 0 := by
    intro h
    have h' := congrArg star h
                                     
    have : ρ = 0 := by simpa [star_star] using h'
    exact hρ this
  have hnormR : ‖(R^2 : ℂ)‖ = (R^2 : ℝ) := by
    have h := (RCLike.norm_ofReal (K:=ℂ) (R^2))
    simp
  calc
    ‖((R^2 : ℂ) / (star ρ))‖
        = ‖(R^2 : ℂ)‖ / ‖star ρ‖ := norm_div_eq _ _ hb
    _ = (R^2 : ℝ) / ‖ρ‖ := by
      simp [hnormR]

lemma zerosetKfR_subset_closedBall {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} :
  zerosetKfR R1 hR1 f ⊆ Metric.closedBall (0 : ℂ) R1 := by
  intro ρ hρ
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  exact hmem.left

lemma mem_zerosetKfR_ne_zero_of_f0_eq_one {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ}
  (hf0 : f 0 = 1) {ρ : ℂ} (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ρ ≠ 0 := by
  intro hρ0
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  have hzero : f 0 = 0 := by simpa [hρ0] using hmem.right
  have h10 : (1 : ℂ) ≠ 0 := one_ne_zero
  exact h10 (by simp [hf0] at hzero)

lemma norm_sub_ge_norm_sub (x y : ℂ) : ‖x - y‖ ≥ ‖y‖ - ‖x‖ := by
  have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_add_le (y - x) x
  have h' : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := (sub_le_iff_le_add).mpr htri
  have hsymm : ‖y - x‖ = ‖x - y‖ := by
    simpa [sub_eq_add_neg, add_comm] using (norm_neg (x - y))
  simpa [hsymm] using h'

lemma mem_zerosetKfR_norm_le {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} {ρ : ℂ}
  (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ‖ρ‖ ≤ R1 := by
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 :=
    (zerosetKfR_subset_closedBall (R1 := R1) hR1 (f := f)) hρ
  have hdist : dist ρ (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hmem
  simpa [dist_eq_norm, sub_zero] using hdist

lemma lem_sum_bound_step2 {R R1: ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (_hR_lt_1 : R < 1)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      (∑ ρ ∈ h_finite_zeros.toFinset,
          ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ (1/(R^2/R1 - R1)) *
          (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := by
  classical
  intro z hz
  rcases hz with ⟨hzball, _hznotin⟩
  have hz_norm : ‖z‖ ≤ R1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
                            
  set S := h_finite_zeros.toFinset
  have hS_spec : ∀ {ρ : ℂ}, ρ ∈ S → ρ ∈ zerosetKfR R1 (by linarith) f := by
    intro ρ hρ
    have hiff := (Set.Finite.mem_toFinset (hs := h_finite_zeros) : ρ ∈ S ↔ ρ ∈ zerosetKfR R1 (by linarith) f)
    exact (Iff.mp hiff) hρ
                                
  have hsum_le :
      (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ ∑ ρ ∈ S, (1/(R^2/R1 - R1)) * ((analyticOrderAt f ρ).toNat : ℝ) := by
    refine Finset.sum_le_sum ?termwise
    intro ρ hρS
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := hS_spec hρS
    have hρ_ne : ρ ≠ 0 :=
      mem_zerosetKfR_ne_zero_of_f0_eq_one (R1 := R1) (hR1 := by linarith)
        (f := f) h_f_zero hρmem
    have hρ_norm : ‖ρ‖ ≤ R1 := mem_zerosetKfR_norm_le (R1 := R1)
      (hR1 := by linarith) (f := f) hρmem
    have hpt : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1/(R^2/R1 - R1) := by
                                          
      have h_Rsq_norm : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ :=
        norm_Rsq_div_conj R ρ hρ_ne
      have h_lower_bound : ‖z - (R^2 : ℂ) / (star ρ)‖ ≥ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ :=
        norm_sub_ge_norm_sub z ((R^2 : ℂ) / (star ρ))
                                                                              
      have hρ_pos : 0 < ‖ρ‖ := by
        simpa [norm_pos_iff] using hρ_ne
      have h_Rsq_bound : R^2/R1 ≤ ‖((R^2 : ℂ) / (star ρ))‖ := by
        rw [h_Rsq_norm]
        exact div_le_div_of_nonneg_left (sq_nonneg R) hρ_pos hρ_norm
      have h_combined : R^2/R1 - R1 ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        calc R^2/R1 - R1
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - R1 := by linarith [h_Rsq_bound]
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ := by linarith [hz_norm]
        _ ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := h_lower_bound
      have h_pos_denom : 0 < R^2/R1 - R1 := by
        have h_R_pos : 0 < R := by linarith [hR1_pos, hR1_lt_R]
        have h_Rsq_pos : 0 < R^2 := sq_pos_of_pos h_R_pos
        calc R^2/R1 - R1
        _ = (R^2 - R1*R1)/R1 := by field_simp
        _ = (R - R1)*(R + R1)/R1 := by ring
        _ > 0 := by
          apply div_pos
          · apply mul_pos
            · linarith [hR1_lt_R]
            · linarith [hR1_pos, hR1_lt_R]
          · exact hR1_pos
      have h_pos_norm : 0 < ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        apply lt_of_lt_of_le h_pos_denom h_combined
                                                              
      have h_reciprocal : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1 / (R^2/R1 - R1) := by
        apply div_le_div_of_nonneg_left
        · norm_num
        · exact h_pos_denom
        · exact h_combined
      exact h_reciprocal
    have hmnonneg : 0 ≤ ((analyticOrderAt f ρ).toNat : ℝ) := by
      exact_mod_cast (Nat.zero_le (analyticOrderAt f ρ).toNat)
    have hmul := mul_le_mul_of_nonneg_left hpt hmnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
                                         
  rw [← Finset.mul_sum] at hsum_le
  exact hsum_le

lemma sq_div_sub_pos (a b : ℝ) (ha_pos : 0 < a) (hab : a < b) : 0 < b^2/a - a := by
                                        
  rw [sub_pos]
                                                        
  rw [lt_div_iff₀ ha_pos]
                         
  rw [← pow_two]
                                                                         
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  apply pow_lt_pow_left₀ hab ha_nonneg
  norm_num                                          

lemma final_sum_bound {R R1 B : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (hB : 1 < B)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ ≤
    1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
  intro z hz
                                                  
  have h_norm_bound := norm_sum_le h_finite_zeros.toFinset (fun ρ => (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)))

  have h_sum_eq : ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ =
    ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast]

  have h_step2 := lem_sum_bound_step2 hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz

  have h_f_nonzero : f 0 ≠ 0 := by rw [h_f_zero]; norm_num
  have h_f_bounded_alt : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B := by
    intro w hw
    exact h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw))
                                                  
  have h_exists : ∀ σ : ℂ, ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g σ ∧ g σ ≠ 0 ∧
      (σ ∈ zerosetKfR R1 (by linarith) f →
        ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * g z) := by
    intro σ
    by_cases hσ : σ ∈ zerosetKfR R1 (by linarith) f
    ·                                             
      have hex := lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero σ hσ
      obtain ⟨g, hg_at, hg_ne, h_eq⟩ := hex
      exact ⟨g, hg_at, hg_ne, fun _ => h_eq⟩
    ·                                            
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · exact analyticAt_const
      · norm_num
      · intro h_contra
        contradiction
                                                 
  let h_σ : ℂ → (ℂ → ℂ) := fun σ => Classical.choose (h_exists σ)
  have h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z := by
    intro σ hσ
    have spec := Classical.choose_spec (h_exists σ)
    exact ⟨spec.1, spec.2.1, spec.2.2 hσ⟩
  have h_sum_bound := lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero h_f_zero h_finite_zeros h_σ h_f_bounded_alt h_σ_spec

  have h_pos : 0 < R^2/R1 - R1 := sq_div_sub_pos R1 R hR1_pos hR1_lt_R
  have h_ratio_gt_one : 1 < R/R1 := by
    rw [one_lt_div_iff]
    left
    exact ⟨hR1_pos, hR1_lt_R⟩
  have h_log_pos : 0 < Real.log (R/R1) := Real.log_pos h_ratio_gt_one

  calc ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖
    ≤ ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := h_norm_bound
    _ = ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := h_sum_eq
    _ ≤ (1/(R^2/R1 - R1)) * (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := h_step2
    _ ≤ (1/(R^2/R1 - R1)) * ((1/Real.log (R/R1)) * Real.log B) := by
              apply mul_le_mul_of_nonneg_left h_sum_bound (div_nonneg zero_le_one (le_of_lt h_pos))
    _ = 1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
      field_simp [ne_of_gt h_pos, ne_of_gt h_log_pos]

lemma final_inequality
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic :
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec :
      ∀ σ ∈ zerosetKfR R1 (by linarith) f,
        AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
        ∀ᶠ z in nhds σ,
          f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,

        ‖(deriv f z / f z
          - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ))‖
      ≤
      16 * r^2 / ((r - r1)^3) * Real.log B
        + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
  intro z hz

  have hr_pos : 0 < r := by linarith [hr1pos, hr1_lt_r]
  have hR1_pos : 0 < R1 := by linarith [hr_pos, hr_lt_R1]

  have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_r)
      exact hz.1
    · exact hz.2

  have hineq :=
    target_inequality_setup hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz_in_r

  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall
      exact le_of_lt (lt_trans hr1_lt_r hr_lt_R1)
      exact hz.1
    · exact hz.2

  have hsum :=
    final_sum_bound hR1_pos hR1_lt_R hR_lt_1 hB h_f_analytic h_f_zero h_finite_zeros h_f_bounded z hz_in_R1

  have hz_le_r1 : ‖z‖ ≤ r1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1

  have hz_abs : ‖z‖ ≤ r1 := hz_le_r1

  have h_BC := apply_BC_to_Lf
    (B := B) (r1 := r1) (r := r) (R := R) (R1 := R1)
    (hB := hB) (hr1_pos := hr1pos) (hr1_lt_r := hr1_lt_r) (hr_lt_R1 := hr_lt_R1)
    (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
    (f := f) (h_f_analytic := h_f_analytic) (h_f_zero := h_f_zero)
    (h_finite_zeros := h_finite_zeros) (h_σ := h_σ) (h_σ_spec := h_σ_spec)
    (h_f_bound := fun w hw => h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw)))
    z hz_abs

  have hLf : ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ ≤
             16 * r^2 / ((r - r1)^3) * Real.log B := by

    convert (preTransparency := .instances) h_BC using 1
                                                                                             
    ring

  exact le_trans hineq (add_le_add hLf hsum)

lemma final_ineq1
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,
    ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset,
                 (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
    (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log B := by
  intro z hz
                                                            
  have h_bound : ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
      16 * r^2 / ((r - r1)^3) * Real.log B + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
    apply final_inequality <;> assumption
                                                                                  
  rw [← add_mul] at h_bound
  exact h_bound

end Erdos970
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AnalyticDiskLogDerivative
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local logarithmic-derivative estimate at the fixed radii needed
for the Hecke zero-free argument. -/
noncomputable section
open Filter Set Erdos970
open scoped Topology BigOperators
namespace CubicFirstMoment

theorem normalized_disk_logDeriv (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf0 : f 0=1) {B : ℝ} (hB : 1 < B)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖f z‖ ≤ B) :
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ ‖ρ‖ ≤ (3/4:ℝ) ∧ f ρ=0) ∧
      ∀ z : ℂ, ‖z‖ ≤ (1/2:ℝ) → f z ≠ 0 →
        ‖logDeriv f z-∑ ρ ∈ Z, ((analyticOrderAt f ρ).toNat:ℂ)/(z-ρ)‖ ≤
          diskLogDerivativeConstant*Real.log B := by
  classical
  have ha : ∀ z ∈ Metric.closedBall (0:ℂ) 1, AnalyticAt ℂ f z :=
    fun z _ => hf.analyticAt z
  have hfin : (zerosetKfR (3/4:ℝ) (by norm_num) f).Finite :=
    lem_Contra_finiteKR (3/4:ℝ) (by norm_num) (by norm_num) f ha
      ⟨0,by simp,hf0 ▸ one_ne_zero⟩
  have hex : ∀ ρ : ℂ, ∃ g : ℂ → ℂ,
      ρ ∈ zerosetKfR (3/4:ℝ) (by norm_num) f →
      AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
        ∀ᶠ z in 𝓝 ρ, f z=(z-ρ)^(analyticOrderAt f ρ).toNat*g z := by
    intro ρ
    by_cases hρ : ρ ∈ zerosetKfR (3/4:ℝ) (by norm_num) f
    · obtain ⟨g,hg⟩ := lem_analytic_zero_factor (7/8:ℝ) (3/4:ℝ)
        (by norm_num) (by norm_num) (by norm_num) f ha (hf0 ▸ one_ne_zero) ρ hρ
      exact ⟨g,fun _ => hg⟩
    · exact ⟨fun _ => 1,fun h => (hρ h).elim⟩
  choose g hg using hex
  refine ⟨hfin.toFinset,?_,?_⟩
  · intro ρ
    simp only [Set.Finite.mem_toFinset,zerosetKfR,Set.mem_ofPred_eq,
      Metric.mem_closedBall,dist_zero_right]
  · intro z hz hzero
    have hz' : z ∈ Metric.closedBall (0:ℂ) (1/2:ℝ) \ zerosetKfR (3/4:ℝ) (by norm_num) f :=
      ⟨by simpa using hz,fun h => hzero h.2⟩
    have h := final_ineq1 B hB (1/2:ℝ) (2/3:ℝ) (7/8:ℝ) (3/4:ℝ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      f ha hf0 hfin (h_σ := g) hg
      (fun w hw => hb w (by simpa using hw)) z hz'
    exact h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AnalyticDiskLowerBound
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real lower bound obtained by retaining one zero in the local
logarithmic-derivative expansion. All other zero terms have nonnegative
real part on the zero-free right half-plane. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma reciprocal_real_nonneg {z w : ℂ} (hw : w.re ≤ z.re) :
    0 ≤ ((z-w)⁻¹).re := by
  rw [Complex.inv_re]
  exact div_nonneg (by simpa using sub_nonneg.mpr hw) (Complex.normSq_nonneg _)

theorem normalized_disk_logDeriv_real_lower_bound (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf0 : f 0=1) {B : ℝ} (hB : 1 < B)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖f z‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ (1/2:ℝ)) (hfz : f z ≠ 0)
    (hleft : ∀ w : ℂ, f w=0 → w.re ≤ z.re) :
    -(diskLogDerivativeConstant*Real.log B) ≤ (logDeriv f z).re := by
  classical
  obtain ⟨Z,hZ,herr⟩ := normalized_disk_logDeriv f hf hf0 hB hb
  have hpos (w : ℂ) (hw : w ∈ Z) :
      0 ≤ (((analyticOrderAt f w).toNat:ℂ)/(z-w)).re := by
    simp only [div_eq_mul_inv,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
      zero_mul,sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (reciprocal_real_nonneg (hleft w (hZ w |>.mp hw).2))
  have hsum := Finset.sum_nonneg hpos
  have he := (Complex.abs_re_le_norm _).trans (herr z hz hfz)
  rw [Complex.sub_re,Complex.re_sum] at he
  linarith [(abs_le.mp he).1]

theorem normalized_disk_logDeriv_lower_bound (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf0 : f 0=1) {B : ℝ} (hB : 1 < B)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖f z‖ ≤ B)
    {z ρ : ℂ} (hz : ‖z‖ ≤ (1/2:ℝ)) (hfz : f z ≠ 0)
    (hρ : ‖ρ‖ ≤ (3/4:ℝ)) (hfρ : f ρ=0)
    (hleft : ∀ w : ℂ, f w=0 → w.re ≤ z.re) :
    ((analyticOrderAt f ρ).toNat:ℝ)*((z-ρ)⁻¹).re-
      diskLogDerivativeConstant*Real.log B ≤ (logDeriv f z).re := by
  classical
  obtain ⟨Z,hZ,herr⟩ := normalized_disk_logDeriv f hf hf0 hB hb
  have hmem : ρ ∈ Z := (hZ ρ).mpr ⟨hρ,hfρ⟩
  have hpos (w : ℂ) (hw : w ∈ Z) :
      0 ≤ (((analyticOrderAt f w).toNat:ℂ)/(z-w)).re := by
    simp only [div_eq_mul_inv,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
      zero_mul,sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (reciprocal_real_nonneg (hleft w (hZ w |>.mp hw).2))
  have hsingle := Finset.single_le_sum hpos hmem
  have he := (Complex.abs_re_le_norm _).trans (herr z hz hfz)
  rw [Complex.sub_re,Complex.re_sum] at he
  have hm : (((analyticOrderAt f ρ).toNat:ℂ)/(z-ρ)).re=
      ((analyticOrderAt f ρ).toNat:ℝ)*((z-ρ)⁻¹).re := by
    simp only [div_eq_mul_inv,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
      zero_mul,sub_zero]
  rw [hm] at hsingle
  linarith [(abs_le.mp he).1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaElementaryGrowth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary bounds used to discharge reciprocal Gamma growth. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma gamma_norm_le_real {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral, Real.Gamma_eq_integral hs]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos (-x)).le,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma gamma_norm_le_add_nat {s : ℂ} (hs : 1 ≤ |s.im|) (n : ℕ) :
    ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s+n)‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have him : (s+(n:ℂ)).im = s.im := by simp
    have hn : 1 ≤ ‖s+(n:ℂ)‖ := hs.trans (by simpa using Complex.abs_im_le_norm (s+(n:ℂ)))
    have hne : s+(n:ℂ) ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hn)
    calc
      _ ≤ ‖Complex.Gamma (s+n)‖ := ih
      _ ≤ ‖s+(n:ℂ)‖*‖Complex.Gamma (s+n)‖ :=
        le_mul_of_one_le_left (_root_.norm_nonneg _) hn
      _ = ‖Complex.Gamma (s+(n+1:ℕ))‖ := by
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]

lemma complex_sin_norm_le_exp_im (s : ℂ) :
    ‖Complex.sin s‖ ≤ Real.exp |s.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one]
  have hp : ‖Complex.exp (-s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using le_abs_self s.im
  have hm : ‖Complex.exp (s*Complex.I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa [Complex.mul_re] using neg_le_abs s.im
  have hd := (norm_sub_le (Complex.exp (-s*Complex.I)) (Complex.exp (s*Complex.I))).trans
    (add_le_add hp hm)
  norm_num
  simp only [neg_mul] at hd
  linarith

lemma gamma_real_interval_bound {a b : ℝ} (ha : 0 < a) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Icc a b, Real.Gamma x ≤ M := by
  have hc : ContinuousOn (fun x : ℝ => Complex.Gamma (x:ℂ)) (Icc a b) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply (Complex.continuousAt_Gamma (x:ℂ) ?_).comp Complex.continuous_ofReal.continuousAt
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.ofReal_re,Complex.neg_re,Complex.natCast_re] at hr
    have : (0:ℝ) ≤ n := by positivity
    linarith [hx.1]
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max M 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro x hx
  exact (Complex.re_le_norm (Complex.Gamma (x:ℂ))).trans ((hM x hx).trans (le_max_left _ _))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GammaInverseGrowth
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reciprocal Gamma has the coarse strip growth needed for the completed
Hecke functions. This uses Euler's integral, reflection and recurrence. -/
noncomputable section
open Set
namespace CubicFirstMoment

private lemma gamma_inverse_reflection {s : ℂ} (hs : 1 ≤ |s.im|) :
    (Complex.Gamma s)⁻¹ = Complex.Gamma (1-s)*Complex.sin (Real.pi*s)/Real.pi := by
  have hi : s.im ≠ 0 := by intro h; simp only [h,abs_zero] at hs; linarith
  have hreg : ∀ n : ℕ, s ≠ -(n:ℂ) := by
    intro n hn
    apply hi
    simpa using congrArg Complex.im hn
  have hreg' : ∀ n : ℕ, 1-s ≠ -(n:ℂ) := by
    intro n hn
    apply hi
    have hh := congrArg Complex.im hn
    simpa using hh
  have hG := Complex.Gamma_ne_zero hreg
  have hG' := Complex.Gamma_ne_zero hreg'
  have hr := Complex.Gamma_mul_Gamma_one_sub s
  have hsin : Complex.sin (Real.pi*s) ≠ 0 := by
    intro hz
    rw [hz,div_zero] at hr
    exact mul_ne_zero hG hG' hr
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hr' := (eq_div_iff hsin).mp hr
  apply (eq_div_iff hp).mpr
  calc
    _ = (Complex.Gamma s)⁻¹*(Complex.Gamma s*Complex.Gamma (1-s)*
        Complex.sin (Real.pi*s)) := congrArg (fun z : ℂ => (Complex.Gamma s)⁻¹*z) hr'.symm
    _ = _ := by field_simp [hG]

private lemma gamma_inverse_large_height_bound (a b : ℝ) :
    ∃ D : ℝ, 0 < D ∧ ∀ s : ℂ, s.re ∈ Icc a b → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ D*Real.exp (Real.pi*|s.im|) := by
  obtain ⟨n,hn⟩ := exists_nat_gt b
  have hlo : 0 < 1-b+(n:ℝ) := by linarith
  obtain ⟨M,hM,hbound⟩ := gamma_real_interval_bound (b := 1-a+(n:ℝ)) hlo
  refine ⟨M/Real.pi,div_pos hM Real.pi_pos,?_⟩
  intro s hs ht
  have hz : 0 < (1-s+(n:ℂ)).re := by
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.natCast_re]
    linarith [hs.2]
  have hΓ : ‖Complex.Gamma (1-s)‖ ≤ M := by
    calc
      _ ≤ ‖Complex.Gamma (1-s+(n:ℂ))‖ := gamma_norm_le_add_nat (by simpa using ht) n
      _ ≤ Real.Gamma (1-s+(n:ℂ)).re := gamma_norm_le_real hz
      _ ≤ M := hbound _ (by
        simp only [mem_Icc,Complex.add_re,Complex.sub_re,Complex.one_re,Complex.natCast_re]
        constructor <;> linarith [hs.1,hs.2])
  have hsin : ‖Complex.sin (Real.pi*s)‖ ≤ Real.exp (Real.pi*|s.im|) := by
    simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,
      abs_mul,abs_of_pos Real.pi_pos] using complex_sin_norm_le_exp_im (Real.pi*s)
  rw [gamma_inverse_reflection ht,norm_div,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  exact (div_le_div_of_nonneg_right (mul_le_mul hΓ hsin (_root_.norm_nonneg _) hM.le)
    Real.pi_pos.le).trans_eq (by ring)

/-- The exact reciprocal-Gamma strip input is an elementary theorem. -/
theorem gammaInverseFiniteOrder (a b : ℝ) : GammaInverseFiniteOrder a b := by
  obtain ⟨D,hD,hlarge⟩ := gamma_inverse_large_height_bound a b
  let F : ℝ × ℝ → ℂ := fun p => (Complex.Gamma ((p.1:ℂ)+(p.2:ℂ)*Complex.I))⁻¹
  have hF : Continuous F := by
    simpa only [F,one_div,Function.comp_def] using Complex.differentiable_one_div_Gamma.continuous.comp
      (show Continuous (fun p : ℝ × ℝ => (p.1:ℂ)+(p.2:ℂ)*Complex.I) by fun_prop)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := (Icc a b) ×ˢ (Icc (-1:ℝ) 1)) hF.continuousOn
  let E := max (max C 1) D
  have hE1 : 1 ≤ E := (le_max_right C 1).trans (le_max_left _ _)
  have hE : 0 < E := zero_lt_one.trans_le hE1
  have hlog : 0 ≤ Real.log E := Real.log_nonneg hE1
  refine ⟨Real.log E+Real.pi,add_nonneg hlog Real.pi_pos.le,?_⟩
  intro s hs
  have hb : ‖(Complex.Gamma s)⁻¹‖ ≤ E*Real.exp (Real.pi*|s.im|) := by
    by_cases ht : |s.im| ≤ 1
    · have hc := hC (s.re,s.im) ⟨hs,abs_le.mp ht⟩
      have hc' : ‖(Complex.Gamma s)⁻¹‖ ≤ C := by
        simpa only [F,Complex.re_add_im] using hc
      exact (hc'.trans ((le_max_left C 1).trans (le_max_left _ _))).trans
        (le_mul_of_one_le_right hE.le (Real.one_le_exp (mul_nonneg Real.pi_pos.le (abs_nonneg _))))
    · exact (hlarge s hs (le_of_not_ge ht)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  have hquad1 : 1 ≤ (1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  have hquad2 : |s.im| ≤ (1+|s.im|)^2 := by nlinarith [abs_nonneg s.im,sq_nonneg |s.im|]
  calc
    _ ≤ E*Real.exp (Real.pi*|s.im|) := hb
    _ = Real.exp (Real.log E+Real.pi*|s.im|) := by rw [Real.exp_add,Real.exp_log hE]
    _ ≤ Real.exp ((Real.log E+Real.pi)*(1+|s.im|)^2) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ Real.log E*(1+|s.im|)^2+Real.pi*(1+|s.im|)^2 :=
          add_le_add (by simpa using mul_le_mul_of_nonneg_left hquad1 hlog)
            (mul_le_mul_of_nonneg_left hquad2 Real.pi_pos.le)
        _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RamifiedIdealParts
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the finitely many primes above three in the
complete ideal lattice. No ramified Euler term is discarded. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_mul_pos (u : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    mellinPhase u (x*y) = mellinPhase u x*mellinPhase u y := by
  unfold mellinPhase
  rw [Real.log_mul hx.ne' hy.ne',mul_add,Complex.ofReal_add,add_mul,Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramMellinTwist
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact conversion of the existing Poisson/Mellin kernel's Fourier
frequency to the norm heights used by the proved structured moments. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellinPhase_add_height (u v x : ℝ) :
    mellinPhase (u+v) x = mellinPhase u x*mellinPhase v x := by
  unfold mellinPhase
  rw [show (((u+v)*Real.log x:ℝ):ℂ)*Complex.I =
    ((u*Real.log x:ℝ):ℂ)*Complex.I+((v*Real.log x:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDirichletBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform normalization of the complete ideal series on Re(s) ≥ 2.
The lower bound follows from its actual Möbius inverse. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma idealZetaTwo_ge_one : 1 ≤ idealZetaTwo := by
  have h := (summable_ideal_norm_rpow (by norm_num : (1:ℝ) < 2)).le_tsum
    0 (fun ν _ => Real.rpow_nonneg (idealExponentNorm_pos ν).le _)
  simpa [idealZetaTwo,idealExponentNorm,idealExponentGenerator] using h

lemma idealZetaTwo_pos : 0 < idealZetaTwo := zero_lt_one.trans_le idealZetaTwo_ge_one

lemma idealMoebius_character_norm (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (ν : EisensteinIdealExponent) :
    ‖((MvPowerSeries.coeff ν idealMoebiusSeries:ℝ):ℂ)*χ ν‖ ≤ 1 := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) (hχ ν)).trans
    (idealMoebiusSeries_abs_le_one ν)

theorem idealDirichlet_upper_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖normDirichletSeries χ idealExponentNorm s‖ ≤ idealZetaTwo :=
  norm_idealDirichlet_le_zeta_two χ hχ s hs

theorem idealDirichlet_inverse_lower_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 2 ≤ s.re) :
    1 ≤ idealZetaTwo*‖normDirichletSeries χ idealExponentNorm s‖ := by
  have he := congrArg (fun z : ℂ => ‖z‖) (idealDirichlet_moebius_mul χ hχ hχ0 hχadd
    (show 1 < s.re by linarith))
  rw [norm_mul,norm_one] at he
  rw [←he]
  exact mul_le_mul_of_nonneg_right
    (idealDirichlet_upper_bound _ (idealMoebius_character_norm χ hχ) hs)
    (_root_.norm_nonneg _)

theorem idealDirichlet_reciprocal_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖(normDirichletSeries χ idealExponentNorm s)⁻¹‖ ≤ idealZetaTwo := by
  rw [norm_inv,inv_eq_one_div,div_le_iff₀ (norm_pos_iff.mpr
    (idealDirichlet_ne_zero χ hχ hχ0 hχadd (show 1 < s.re by linarith)))]
  simpa only [mul_comm] using idealDirichlet_inverse_lower_bound χ hχ hχ0 hχadd hs

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeUniformGrowth
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A conductor-explicit polynomial bound in the fixed strip needed by
the local zero-free argument. The finite-order constant disappears under
Phragmen--Lindelof; only the actual functional-equation factors remain. -/
noncomputable section
open Set
namespace CubicFirstMoment

lemma heckeZeroFreeMajorant_ge_zeta (A k : ℝ) (ε : ℂ) :
    idealZetaTwo ≤ heckeZeroFreeMajorant A k ε := by
  have h := idealZetaTwo_pos
  have hp : 0 ≤ ‖ε‖*A^4*(k+7)^4*idealZetaTwo := by positivity
  unfold heckeZeroFreeMajorant
  nlinarith

lemma heckeZeroFreeMajorant_pos (A k : ℝ) (ε : ℂ) :
    0 < heckeZeroFreeMajorant A k ε :=
  idealZetaTwo_pos.trans_le (heckeZeroFreeMajorant_ge_zeta A k ε)

theorem shifted_hecke_uniform_strip
    {χ χdual : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) :
    ∀ z : ℂ, -(3/2:ℝ) ≤ z.re →
      ‖L z‖ ≤ heckeZeroFreeMajorant A k ε*(1+|z.im|)^4 := by
  let C : ℝ := idealZetaTwo+‖ε‖*A^4*(k+7)^4*idealZetaTwo
  have hS0 := idealZetaTwo_pos
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hS : idealZetaTwo ≤ C := le_add_of_nonneg_right (by positivity)
  have ha : ∀ z : ℂ, z.re=-(3/2:ℝ) → ‖L z‖ ≤ C*(1+|z.im|)^4 := by
    intro z hz
    have he : z=(1/2:ℂ)-(2:ℕ)+(z.im:ℂ)*Complex.I := by
      apply Complex.ext <;> norm_num
      linarith
    have hb := angular_hecke_left_boundary χdual hχdual hA hk hL hcomp hFE hds
      (m := 2) (by norm_num) z.im
    rw [←he] at hb
    have hb' : ‖L z‖ ≤ (‖ε‖*A^4*(k+7)^4*idealZetaTwo)*(1+|z.im|)^4 := by
      simpa only [idealZetaTwo,Nat.reduceMul,Nat.cast_ofNat,
        show k+3*(2:ℝ)+1=k+7 by ring] using! hb
    exact hb'.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [idealZetaTwo_pos])
      (by positivity))
  have hb : ∀ z : ℂ, z.re=2 → ‖L z‖ ≤ C*(1+|z.im|)^4 := by
    intro z hz
    rw [hs z (by linarith)]
    exact (idealDirichlet_upper_bound χ hχ hz.ge).trans
      (hS.trans (le_mul_of_one_le_right hC (one_le_pow₀ (by linarith [abs_nonneg z.im]))))
  have hfin : FiniteVerticalOrder L (-(3/2:ℝ)) 2 :=
    shifted_completed_finiteVerticalOrder hA hL hcomp
      (gammaInverseFiniteOrder (-(3/2:ℝ)+k) (2+k))
  have hbound := polynomial_strip_of_finite_order (a := -(3/2:ℝ)) (b := 2)
    (by norm_num) hL hfin hC 4 ha hb
  intro z hz
  by_cases hz2 : z.re ≤ 2
  · simpa only [heckeZeroFreeMajorant,C,show 2-(-(3/2:ℝ))+1=9/2 by norm_num,
      show (2:ℝ)^4=16 by norm_num]
      using hbound z ⟨hz,hz2⟩
  · rw [hs z (by linarith)]
    exact (idealDirichlet_upper_bound χ hχ (by linarith)).trans
      ((heckeZeroFreeMajorant_ge_zeta A k ε).trans
        (le_mul_of_one_le_right (heckeZeroFreeMajorant_pos A k ε).le
          (one_le_pow₀ (by linarith [abs_nonneg z.im]))))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDirichletHolomorphic
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Holomorphy and termwise differentiation of the complete ideal series
on its half-plane of absolute convergence. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

lemma idealDirichlet_term_differentiable (χ : EisensteinIdealExponent → ℂ)
    (ν : EisensteinIdealExponent) :
    Differentiable ℂ (fun s : ℂ => χ ν*(idealExponentNorm ν:ℂ)^(-s)) := by
  let : NeZero (idealExponentNorm ν:ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'⟩
  exact (differentiable_const (χ ν)).mul
    ((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg)

lemma idealDirichlet_uniform_bound (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {σ : ℝ} (ν : EisensteinIdealExponent)
    {s : ℂ} (hs : σ < s.re) :
    ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖ ≤ idealExponentNorm ν^(-σ) := by
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
  apply (mul_le_of_le_one_left (Real.rpow_nonneg (idealExponentNorm_pos ν).le _) (hχ ν)).trans
  exact Real.rpow_le_rpow_of_exponent_le (idealExponentNorm_ge_one ν) (by linarith)

lemma idealDirichlet_term_hasDerivAt (χ : EisensteinIdealExponent → ℂ)
    (ν : EisensteinIdealExponent) (s : ℂ) :
    HasDerivAt (fun z : ℂ => χ ν*(idealExponentNorm ν:ℂ)^(-z))
      (χ ν*(-(Real.log (idealExponentNorm ν):ℂ))*(idealExponentNorm ν:ℂ)^(-s)) s := by
  have hn : (idealExponentNorm ν:ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos ν).ne'
  have h := (((hasDerivAt_id s).neg).const_cpow (Or.inl hn)).const_mul (χ ν)
  rw [←Complex.ofReal_log (idealExponentNorm_pos ν).le] at h
  refine h.congr_deriv ?_
  · simp only [Pi.neg_apply,id_eq]
    ring

lemma idealDirichlet_hasSum_deriv (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun ν => χ ν*(-(Real.log (idealExponentNorm ν):ℂ))*
      (idealExponentNorm ν:ℂ)^(-s)) (deriv (normDirichletSeries χ idealExponentNorm) s) := by
  have hσ : 1 < (1+s.re)/2 := by linarith
  have hm : (1+s.re)/2 < s.re := by linarith
  have h := Complex.hasSum_deriv_of_summable_norm (summable_ideal_norm_rpow hσ)
    (fun ν => (idealDirichlet_term_differentiable χ ν).differentiableOn)
    (isOpen_lt continuous_const Complex.continuous_re)
    (fun ν z hz => idealDirichlet_uniform_bound χ hχ ν hz) hm
  simpa only [normDirichletSeries,(idealDirichlet_term_hasDerivAt χ _ _).deriv] using! h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealLogDirichlet
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence of the logarithmically weighted ideal series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma summable_ideal_log_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun ν : EisensteinIdealExponent =>
      Real.log (idealExponentNorm ν)*idealExponentNorm ν^(-σ)) := by
  let ε : ℝ := (σ-1)/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hmid : 1 < σ-ε := by dsimp [ε]; linarith
  apply ((summable_ideal_norm_rpow hmid).mul_left ε⁻¹).of_nonneg_of_le
    (fun ν => mul_nonneg (Real.log_nonneg (idealExponentNorm_ge_one ν))
      (Real.rpow_nonneg (idealExponentNorm_pos ν).le _))
  intro ν
  have hp := idealExponentNorm_pos ν
  have h := mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hp.le hε)
    (Real.rpow_nonneg hp.le (-σ))
  calc
    _ ≤ (idealExponentNorm ν^ε/ε)*idealExponentNorm ν^(-σ) := h
    _ = ε⁻¹*idealExponentNorm ν^(-(σ-ε)) := by
      rw [div_eq_mul_inv]
      calc
        _ = ε⁻¹*(idealExponentNorm ν^ε*idealExponentNorm ν^(-σ)) := by ring
        _ = _ := by rw [←Real.rpow_add hp]; congr 2; ring

lemma idealVonMangoldtDirichlet_norm_summable (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun ν => ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν*
      (idealExponentNorm ν:ℂ)^(-s)‖) := by
  apply (summable_ideal_log_rpow hs).of_nonneg_of_le (fun _ => _root_.norm_nonneg _)
  intro ν
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_right (abs_nonneg _) (hχ ν)).trans (idealVonMangoldt_coeff_abs_le_logNorm ν))
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealLogDerivative
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubePointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic derivative of the complete ideal series is the
actual ideal von Mangoldt Dirichlet series on `Re(s)>1`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealVonMangoldt_antidiagonal (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      ((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ))=(Real.log (idealExponentNorm ν):ℂ) := by
  have h := congrArg (MvPowerSeries.coeff ν) idealZeta_mul_vonMangoldt
  rw [MvPowerSeries.coeff_mul] at h
  simp only [MvPowerSeries.coeff_apply,idealZeta,one_mul,idealLogNorm] at h
  simpa only [Complex.ofReal_sum,MvPowerSeries.coeff_apply] using congrArg Complex.ofReal h

lemma idealVonMangoldt_twist_convolution (f : EisensteinIdealExponent → ℂ)
    (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) (ν : EisensteinIdealExponent) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
      f p.1*(((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*f p.2))=
        (Real.log (idealExponentNorm ν):ℂ)*f ν := by
  calc
    _ = (∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        ((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ))*f ν := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [show f p.1*(((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*f p.2)=
          ((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*(f p.1*f p.2) by ring,
        ←hfadd,Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
    _ = _ := by rw [idealVonMangoldt_antidiagonal]

lemma idealVonMangoldt_tsum_mul (f : EisensteinIdealExponent → ℂ)
    (hf : Summable (fun ν => ‖f ν‖))
    (hg : Summable (fun ν => ‖((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*f ν‖))
    (hfadd : ∀ ν κ, f (ν+κ)=f ν*f κ) :
    (∑' ν, f ν)*(∑' ν, ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*f ν)=
      ∑' ν, (Real.log (idealExponentNorm ν):ℂ)*f ν := by
  calc
    _ = ∑' ν, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal ν,
        f p.1*(((MvPowerSeries.coeff p.2 idealVonMangoldt:ℝ):ℂ)*f p.2) :=
      ideal_cauchy_product _ _ hf hg
    _ = _ := tsum_congr (idealVonMangoldt_twist_convolution f hfadd)

theorem idealDirichlet_neg_logDeriv (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (normDirichletSeries χ idealExponentNorm) s=
      normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)
        idealExponentNorm s := by
  have hM := idealVonMangoldt_tsum_mul (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(-s))
    (idealDirichlet_norm_summable χ hχ hs)
    (by simpa only [mul_assoc] using idealVonMangoldtDirichlet_norm_summable χ hχ hs)
    (idealDirichlet_weight_add χ hχadd s)
  have hD := (idealDirichlet_hasSum_deriv χ hχ hs).tsum_eq
  have hlog : deriv (normDirichletSeries χ idealExponentNorm) s=
      -(∑' ν, (Real.log (idealExponentNorm ν):ℂ)*(χ ν*(idealExponentNorm ν:ℂ)^(-s))) := by
    rw [←hD,←tsum_neg]
    apply tsum_congr
    intro ν
    ring
  have hn := idealDirichlet_ne_zero χ hχ hχ0 hχadd hs
  rw [logDeriv_apply,hlog,neg_div,neg_neg,div_eq_iff hn]
  simpa only [normDirichletSeries,mul_assoc,mul_comm,mul_left_comm] using hM.symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerPositivity
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonnegative 3-4-1 combination for the actual ideal logarithmic
derivatives. This is the Euler-coefficient positivity used in the zero-free
argument, including the primes where a character vanishes. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma complex_341_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 3+4*z.re+(z^2).re := by
  have hn : z.re^2+z.im^2 ≤ 1 := by
    calc
      _ = ‖z‖^2 := by rw [←Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply,pow_two]
      _ ≤ 1 := by nlinarith [_root_.norm_nonneg z]
  simp only [pow_two,Complex.mul_re]
  nlinarith [sq_nonneg (z.re+1)]

lemma idealMangoldt_term_re (χ : EisensteinIdealExponent → ℂ)
    (σ : ℝ) (ν : EisensteinIdealExponent) :
    ((((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)*
      (idealExponentNorm ν:ℂ)^(-(σ:ℂ))).re =
      (MvPowerSeries.coeff ν idealVonMangoldt:ℝ)*(χ ν).re*idealExponentNorm ν^(-σ) := by
  rw [←Complex.ofReal_neg,←Complex.ofReal_cpow (idealExponentNorm_pos ν).le]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,zero_mul]

lemma idealMangoldt_real_hasSum (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun ν => (MvPowerSeries.coeff ν idealVonMangoldt:ℝ)*(χ ν).re*
      idealExponentNorm ν^(-σ))
      (normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)
        idealExponentNorm (σ:ℂ)).re := by
  have hs := (idealVonMangoldtDirichlet_norm_summable χ hχ
    (s := (σ:ℂ)) (by simpa using hσ)).of_norm
  simpa only [normDirichletSeries,idealMangoldt_term_re] using! Complex.hasSum_re hs.hasSum

theorem idealMangoldt_341_nonneg (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ 3*(normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ))
          idealExponentNorm (σ:ℂ)).re+
      4*(normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*χ ν)
          idealExponentNorm (σ:ℂ)).re+
      (normDirichletSeries (fun ν => ((MvPowerSeries.coeff ν idealVonMangoldt:ℝ):ℂ)*(χ ν)^2)
          idealExponentNorm (σ:ℂ)).re := by
  have hsq : ∀ ν, ‖(χ ν)^2‖ ≤ 1 := by
    intro ν
    rw [norm_pow]
    nlinarith [hχ ν,_root_.norm_nonneg (χ ν)]
  have h0 := idealMangoldt_real_hasSum (fun _ => 1) (by simp) hσ
  have h1 := idealMangoldt_real_hasSum χ hχ hσ
  have h2 := idealMangoldt_real_hasSum (fun ν => (χ ν)^2) hsq hσ
  have h := ((h0.mul_left 3).add (h1.mul_left 4)).add h2
  simp only [mul_one,Complex.one_re] at h
  rw [←h.tsum_eq]
  apply tsum_nonneg
  intro ν
  have hp := mul_nonneg (idealVonMangoldt_coeff_nonneg ν)
    (Real.rpow_nonneg (idealExponentNorm_pos ν).le (-σ))
  have hz := complex_341_nonneg (hχ ν)
  nlinarith [mul_nonneg hp hz]

theorem idealLogDeriv_341_nonneg (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {σ : ℝ} (hσ : 1 < σ) :
    0 ≤ 3*(-logDeriv (normDirichletSeries (fun _ => 1) idealExponentNorm) (σ:ℂ)).re+
      4*(-logDeriv (normDirichletSeries χ idealExponentNorm) (σ:ℂ)).re+
      (-logDeriv (normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm) (σ:ℂ)).re := by
  have hsq : ∀ ν, ‖(χ ν)^2‖ ≤ 1 := by
    intro ν
    rw [norm_pow]
    nlinarith [hχ ν,_root_.norm_nonneg (χ ν)]
  rw [idealDirichlet_neg_logDeriv _ (by simp) (by simp) (by simp) (by simpa using hσ),
    idealDirichlet_neg_logDeriv χ hχ hχ0 hχadd (by simpa using hσ),
    idealDirichlet_neg_logDeriv _ hsq (by simp [hχ0])
      (by intro ν κ; rw [hχadd,mul_pow]) (by simpa using hσ)]
  simpa only [mul_one] using idealMangoldt_341_nonneg χ hχ hσ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealLogDerivativeTwist
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Vertical translation and the zero-free positivity inequality for the
literal complete ideal series. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

lemma idealNormTwist_norm (χ : EisensteinIdealExponent → ℂ) (t : ℝ)
    (ν : EisensteinIdealExponent) : ‖idealNormTwist χ t ν‖=‖χ ν‖ := by
  simp only [idealNormTwist,norm_mul,mellinPhase_norm,mul_one]

lemma idealNormTwist_zero (χ : EisensteinIdealExponent → ℂ) (t : ℝ)
    (hχ0 : χ 0=1) : idealNormTwist χ t 0=1 := by
  simp [idealNormTwist,hχ0,idealExponentNorm,idealExponentGenerator,mellinPhase]

lemma idealNormTwist_add (χ : EisensteinIdealExponent → ℂ) (t : ℝ)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) (ν κ : EisensteinIdealExponent) :
    idealNormTwist χ t (ν+κ)=idealNormTwist χ t ν*idealNormTwist χ t κ := by
  simp only [idealNormTwist,hχadd,idealExponentNorm_add,
    mellinPhase_mul_pos t (idealExponentNorm_pos ν) (idealExponentNorm_pos κ)]
  ring

lemma idealNormTwist_sq (χ : EisensteinIdealExponent → ℂ) (t : ℝ) :
    (fun ν => (idealNormTwist χ t ν)^2)=idealNormTwist (fun ν => (χ ν)^2) (2*t) := by
  funext ν
  simp only [idealNormTwist,pow_two]
  rw [show 2*t=t+t by ring,mellinPhase_add_height]
  ring

lemma idealNormTwist_logDeriv (χ : EisensteinIdealExponent → ℂ) (t : ℝ) (s : ℂ) :
    logDeriv (normDirichletSeries (idealNormTwist χ t) idealExponentNorm) s=
      logDeriv (normDirichletSeries χ idealExponentNorm) (s-(t:ℂ)*Complex.I) := by
  have he : normDirichletSeries (idealNormTwist χ t) idealExponentNorm=
      fun z => normDirichletSeries χ idealExponentNorm (z-(t:ℂ)*Complex.I) := by
    funext z
    exact twisted_normDirichletSeries χ t z
  rw [he,logDeriv_apply,deriv_comp_sub_const]
  rfl

theorem idealLogDeriv_vertical_341_nonneg (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {σ : ℝ} (hσ : 1 < σ) (t : ℝ) :
    0 ≤ 3*(-logDeriv (normDirichletSeries (fun _ => 1) idealExponentNorm) (σ:ℂ)).re+
      4*(-logDeriv (normDirichletSeries χ idealExponentNorm) ((σ:ℂ)+(t:ℂ)*Complex.I)).re+
      (-logDeriv (normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm)
        ((σ:ℂ)+(2*t:ℝ)*Complex.I)).re := by
  have h := idealLogDeriv_341_nonneg (idealNormTwist χ (-t))
    (fun ν => by simpa only [idealNormTwist_norm] using hχ ν)
    (idealNormTwist_zero χ (-t) hχ0) (idealNormTwist_add χ (-t) hχadd) hσ
  rw [idealNormTwist_sq,idealNormTwist_logDeriv,idealNormTwist_logDeriv] at h
  have e1 : (σ:ℂ)-(-t:ℝ)*Complex.I=(σ:ℂ)+(t:ℂ)*Complex.I := by
    push_cast
    ring
  have e2 : (σ:ℂ)-(2*(-t):ℝ)*Complex.I=(σ:ℂ)+(2*t:ℝ)*Complex.I := by
    push_cast
    ring
  simpa only [e1,e2] using h

lemma idealSeries_logDeriv_eq {χ : EisensteinIdealExponent → ℂ} {L : ℂ → ℂ}
    (hseries : ∀ z : ℂ, 1 < z.re → L z=normDirichletSeries χ idealExponentNorm z)
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv L s=logDeriv (normDirichletSeries χ idealExponentNorm) s := by
  have he : L =ᶠ[𝓝 s] normDirichletSeries χ idealExponentNorm := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact hseries z hz
  exact (logDeriv_congr_nhds he).self_of_nhds

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeNormalizedDisk
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a complete Hecke function at 2+it on a disk of radius 3.
The resulting bound is explicit in the finite and archimedean conductor. -/
noncomputable section
open scoped Topology
namespace CubicFirstMoment

lemma normalizedHeckeDiskBound_gt_one (A k : ℝ) (ε : ℂ) (t : ℝ) :
    1 < normalizedHeckeDiskBound A k ε t := by
  have h1 := idealZetaTwo_pos
  have h2 := heckeZeroFreeMajorant_pos A k ε
  unfold normalizedHeckeDiskBound
  have hp : 0 ≤ idealZetaTwo*heckeZeroFreeMajorant A k ε*(4+|t|)^4 := by positivity
  linarith

lemma normalizedHeckeDisk_differentiable {L : ℂ → ℂ}
    (hL : Differentiable ℂ L) (t : ℝ) : Differentiable ℂ (normalizedHeckeDisk L t) := by
  unfold normalizedHeckeDisk
  fun_prop

lemma normalizedHeckeDisk_zero {L : ℂ → ℂ} (t : ℝ)
    (hL0 : L (2+(t:ℂ)*Complex.I) ≠ 0) : normalizedHeckeDisk L t 0=1 := by
  simp [normalizedHeckeDisk,hL0]

lemma normalizedHeckeDisk_logDeriv {L : ℂ → ℂ}
    (hL : Differentiable ℂ L) (t : ℝ) (z : ℂ)
    (hL0 : L (2+(t:ℂ)*Complex.I) ≠ 0) :
    logDeriv (normalizedHeckeDisk L t) z=
      3*logDeriv L (2+(t:ℂ)*Complex.I+3*z) := by
  change logDeriv (fun w : ℂ => L (2+(t:ℂ)*Complex.I+3*w)*
    (L (2+(t:ℂ)*Complex.I))⁻¹) z= _
  rw [logDeriv_mul_const z _ (inv_ne_zero hL0)]
  have h : logDeriv (fun w : ℂ => L (2+(t:ℂ)*Complex.I+3*w)) z =
      logDeriv L (2+(t:ℂ)*Complex.I+3*z) * deriv (fun w : ℂ => 2+(t:ℂ)*Complex.I+3*w) z :=
    logDeriv_comp (f := L) (g := fun w : ℂ => 2+(t:ℂ)*Complex.I+3*w)
    (hL (2+(t:ℂ)*Complex.I+3*z))
    (show DifferentiableAt ℂ (fun w : ℂ => 2+(t:ℂ)*Complex.I+3*w) z by fun_prop)
  have hd : deriv (fun w : ℂ => 2+(t:ℂ)*Complex.I+3*w) z=3 := by
    simpa only [Pi.add_apply,id_eq,zero_add,mul_one] using!
      ((hasDerivAt_const z (2+(t:ℂ)*Complex.I)).add ((hasDerivAt_id z).const_mul (3:ℂ))).deriv
  rw [hd] at h
  simpa only [mul_comm] using h

theorem normalizedHeckeDisk_bound
    {χ χdual : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L) (t : ℝ) :
    ∀ z : ℂ, ‖z‖ ≤ 1 → ‖normalizedHeckeDisk L t z‖ ≤ normalizedHeckeDiskBound A k ε t := by
  have hK := heckeZeroFreeMajorant_pos A k ε
  have hc : (2+(t:ℂ)*Complex.I).re=2 := by simp
  have hinv : ‖(L (2+(t:ℂ)*Complex.I))⁻¹‖ ≤ idealZetaTwo := by
    rw [hs _ (by rw [hc]; norm_num)]
    exact idealDirichlet_reciprocal_bound χ hχ hχ0 hχadd hc.ge
  intro z hz
  have hr : -(3/2:ℝ) ≤ (2+(t:ℂ)*Complex.I+3*z).re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm z)).1
    have he : (2+(t:ℂ)*Complex.I+3*z).re=2+3*z.re := by simp
    rw [he]
    linarith
  have hi : |(2+(t:ℂ)*Complex.I+3*z).im| ≤ |t|+3 := by
    have h := Complex.abs_im_le_norm z
    have hh := abs_add_le t (3*z.im)
    have he : (2+(t:ℂ)*Complex.I+3*z).im=t+3*z.im := by simp
    rw [he]
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3)] at hh
    linarith
  have hl := shifted_hecke_uniform_strip hχ hχdual hA hk hL hs hds hFE hcomp _ hr
  have hp : (1+|(2+(t:ℂ)*Complex.I+3*z).im|)^4 ≤ (4+|t|)^4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  have hfinal := mul_le_mul
    (hl.trans (mul_le_mul_of_nonneg_left hp (heckeZeroFreeMajorant_pos A k ε).le))
    hinv (_root_.norm_nonneg _) (by positivity)
  rw [normalizedHeckeDisk,div_eq_mul_inv,norm_mul]
  exact hfinal.trans (by unfold normalizedHeckeDiskBound; nlinarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeZeros
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Zeros of the actual entire Hecke continuations: none occur right of
one, bounded sets contain finitely many, and local multiplicities are
positive finite integers. -/
noncomputable section
open Set Filter
open scoped Topology
namespace CubicFirstMoment

theorem heckeSeries_ne_zero {χ : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {s : ℂ} (hs1 : 1 < s.re) : L s ≠ 0 := by
  rw [hs s hs1]
  exact idealDirichlet_ne_zero χ hχ hχ0 hχadd hs1

theorem heckeZero_real_le_one {χ : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχ0 : χ 0=1)
    (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ) {L : ℂ → ℂ}
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {ρ : ℂ} (hρ : L ρ=0) : ρ.re ≤ 1 := by
  by_contra h
  exact heckeSeries_ne_zero hχ hχ0 hχadd hs (lt_of_not_ge h) hρ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDiskLowerBound
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of the fixed-disk logarithmic-derivative bound to the
literal Hecke continuation, keeping the contribution of a nearby zero. -/
noncomputable section
namespace CubicFirstMoment

lemma entire_zero_order_pos {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : f 0=1) {ρ : ℂ} (hρ : f ρ=0) : 0 < (analyticOrderAt f ρ).toNat := by
  apply ENat.toNat_pos
  · exact (hf.analyticAt ρ).analyticOrderAt_ne_zero.mpr hρ
  · intro ht
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
      (fun z => hf.analyticAt z)).mp ht
    have := congrFun he 0
    simp only [hf0,Pi.zero_apply] at this
    exact one_ne_zero this

theorem hecke_logDeriv_real_lower_of_disk
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {B : ℝ} (hB : 1 < B) {t : ℝ}
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖normalizedHeckeDisk L t z‖ ≤ B)
    {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    -((diskLogDerivativeConstant/3)*Real.log B) ≤
      (logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by
  let z : ℂ := ((σ-2:ℝ):ℂ)/3
  have hc : L (2+(t:ℂ)*Complex.I) ≠ 0 :=
    heckeSeries_ne_zero hχ hχ0 hχadd hs (by simp)
  have hzN : ‖z‖ ≤ (1/2:ℝ) := by
    simp only [z,norm_div,Complex.norm_real,Real.norm_eq_abs,show ‖(3:ℂ)‖=3 by norm_num]
    rw [div_le_iff₀ (by norm_num)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hzEq : 2+(t:ℂ)*Complex.I+3*z=(σ:ℂ)+(t:ℂ)*Complex.I := by
    dsimp [z]
    push_cast
    ring
  have hfz : normalizedHeckeDisk L t z ≠ 0 := by
    exact div_ne_zero (by rw [hzEq]; exact heckeSeries_ne_zero hχ hχ0 hχadd hs (by simpa)) hc
  have hleft (w : ℂ) (hw : normalizedHeckeDisk L t w=0) : w.re ≤ z.re := by
    have hroot : L (2+(t:ℂ)*Complex.I+3*w)=0 := (div_eq_zero_iff.mp hw).resolve_right hc
    have hwr := heckeZero_real_le_one hχ hχ0 hχadd hs hroot
    have hwre : (2+(t:ℂ)*Complex.I+3*w).re=2+3*w.re := by simp
    have hzre : z.re=(σ-2)/3 := by simp [z]
    rw [hwre] at hwr
    rw [hzre]
    linarith
  have hd := normalized_disk_logDeriv_real_lower_bound _
    (normalizedHeckeDisk_differentiable hL t) (normalizedHeckeDisk_zero t hc)
    hB hb hzN hfz hleft
  rw [normalizedHeckeDisk_logDeriv hL t z hc,hzEq] at hd
  have hre : (3*logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re=
      3*(logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by simp
  rw [hre] at hd
  linarith

theorem hecke_logDeriv_lower_of_disk
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    {B : ℝ} (hB : 1 < B) {t : ℝ}
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖normalizedHeckeDisk L t z‖ ≤ B)
    {σ β : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) (hβ : (1/2:ℝ) ≤ β)
    (hzero : L ((β:ℂ)+(t:ℂ)*Complex.I)=0) :
    1/(σ-β)-(diskLogDerivativeConstant/3)*Real.log B ≤
      (logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by
  let z : ℂ := ((σ-2:ℝ):ℂ)/3
  let ρ : ℂ := ((β-2:ℝ):ℂ)/3
  have hc : L (2+(t:ℂ)*Complex.I) ≠ 0 :=
    heckeSeries_ne_zero hχ hχ0 hχadd hs (by simp)
  have hβ1 : β ≤ 1 := by
    simpa using heckeZero_real_le_one hχ hχ0 hχadd hs hzero
  have hzN : ‖z‖ ≤ (1/2:ℝ) := by
    simp only [z,norm_div,Complex.norm_real,Real.norm_eq_abs,show ‖(3:ℂ)‖=3 by norm_num]
    rw [div_le_iff₀ (by norm_num)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hρN : ‖ρ‖ ≤ (3/4:ℝ) := by
    simp only [ρ,norm_div,Complex.norm_real,Real.norm_eq_abs,show ‖(3:ℂ)‖=3 by norm_num]
    rw [div_le_iff₀ (by norm_num)]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hzEq : 2+(t:ℂ)*Complex.I+3*z=(σ:ℂ)+(t:ℂ)*Complex.I := by
    dsimp [z]
    push_cast
    ring
  have hρEq : 2+(t:ℂ)*Complex.I+3*ρ=(β:ℂ)+(t:ℂ)*Complex.I := by
    dsimp [ρ]
    push_cast
    ring
  have hf := normalizedHeckeDisk_differentiable hL t
  have hf0 := normalizedHeckeDisk_zero t hc
  have hfρ : normalizedHeckeDisk L t ρ=0 := by
    simp only [normalizedHeckeDisk,hρEq,hzero,zero_div]
  have hfz : normalizedHeckeDisk L t z ≠ 0 := by
    exact div_ne_zero (by rw [hzEq]; exact heckeSeries_ne_zero hχ hχ0 hχadd hs (by simpa)) hc
  have hleft (w : ℂ) (hw : normalizedHeckeDisk L t w=0) : w.re ≤ z.re := by
    have hroot : L (2+(t:ℂ)*Complex.I+3*w)=0 := (div_eq_zero_iff.mp hw).resolve_right hc
    have hwr := heckeZero_real_le_one hχ hχ0 hχadd hs hroot
    have hwre : (2+(t:ℂ)*Complex.I+3*w).re=2+3*w.re := by simp
    have hzre : z.re=(σ-2)/3 := by simp [z]
    rw [hwre] at hwr
    rw [hzre]
    linarith
  have hd := normalized_disk_logDeriv_lower_bound _ hf hf0 hB hb hzN hfz hρN hfρ hleft
  have hn := entire_zero_order_pos hf hf0 hfρ
  have hnr : (1:ℝ) ≤ (analyticOrderAt (normalizedHeckeDisk L t) ρ).toNat := by exact_mod_cast hn
  have hr : ((z-ρ)⁻¹).re=3/(σ-β) := by
    have he : z-ρ=(((σ-β)/3:ℝ):ℂ) := by
      dsimp [z,ρ]
      push_cast
      ring
    rw [he,←Complex.ofReal_inv,Complex.ofReal_re]
    field_simp
  have hpos : 0 < σ-β := by linarith
  have hm : 3/(σ-β) ≤ ((analyticOrderAt (normalizedHeckeDisk L t) ρ).toNat:ℝ)*
      (3/(σ-β)) := le_mul_of_one_le_left (by positivity) hnr
  rw [hr,normalizedHeckeDisk_logDeriv hL t z hc,hzEq] at hd
  have hre : (3*logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re=
      3*(logDeriv L ((σ:ℂ)+(t:ℂ)*Complex.I)).re := by simp
  rw [hre] at hd
  rw [show 3/(σ-β)=3*(1/(σ-β)) by ring] at hd hm
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeZeroFreeAlgebra
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The numerical contradiction in the de la Vallée Poussin argument,
at the explicit displacement 1/(4E). -/
noncomputable section
namespace CubicFirstMoment

lemma hecke_zero_free_numerical {E e : ℝ} (hE : 0 < E)
    (he0 : 0 ≤ e) (he : e ≤ 1/(32*E)) :
    3/(1/(4*E))-4/(1/(4*E)+e)+E < 0 := by
  let d : ℝ := 1/(4*E)
  have hd : 0 < d := by dsimp [d]; positivity
  have hde : 0 < d+e := add_pos_of_pos_of_nonneg hd he0
  have he' : e ≤ d/8 := by
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [d]
    ring
  have hA : 0 ≤ 3/d+E := by positivity
  have hAd : (3/d+E)*d=13/4 := by
    dsimp [d]
    field_simp
    ring
  have hprod := mul_le_mul_of_nonneg_left he' hA
  have hprod' : (3/d+E)*(d+e) < 4 := by
    calc
      (3/d+E)*(d+e)=(3/d+E)*d+(3/d+E)*e := mul_add _ _ _
      _ ≤ (3/d+E)*d+(3/d+E)*(d/8) := by linarith
      _ = 117/32 := by simp only [←mul_div_assoc,hAd]; norm_num
      _ < 4 := by norm_num
  have hineq : 3/d+E < 4/(d+e) := (lt_div_iff₀ hde).mpr hprod'
  change 3/d-4/(d+e)+E < 0
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeZeroFreePair
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The zero-free step for a nonreal character and its square. The inputs
are the actual entire continuations and proved disk bounds; no prime-sum
or zero-free assertion is assumed. -/
noncomputable section
namespace CubicFirstMoment

lemma principalPoleConstant_pos : 0 < principalPoleConstant :=
  principalIdealZeta_real_logDeriv_bound.choose_spec.choose_spec.1

lemma principalPoleRadius_pos : 0 < principalPoleRadius :=
  principalIdealZeta_real_logDeriv_bound.choose_spec.choose_spec.2.1

lemma principalPoleBound (σ : ℝ) (hσ : 1 < σ) (hσδ : σ < 1+principalPoleRadius) :
    (-logDeriv principalIdealZeta (σ:ℂ)).re ≤ 1/(σ-1)+principalPoleConstant :=
  principalIdealZeta_real_logDeriv_bound.choose_spec.choose_spec.2.2 σ hσ hσδ

lemma diskLogDerivativeConstant_pos : 0 < diskLogDerivativeConstant := by
  have hl : 0 < Real.log ((7/8:ℝ)/(3/4)) := Real.log_pos (by norm_num)
  unfold diskLogDerivativeConstant
  positivity

lemma heckePairZeroFreeError_ge_one {B B2 : ℝ} (hB : 1 < B) (hB2 : 1 < B2) :
    1 ≤ heckePairZeroFreeError B B2 := by
  have h1 := principalPoleConstant_pos
  have h2 := principalPoleRadius_pos
  have h3 := diskLogDerivativeConstant_pos
  have hl1 := Real.log_pos hB
  have hl2 := Real.log_pos hB2
  have hp : 0 ≤ 3*principalPoleConstant+
      4*((diskLogDerivativeConstant/3)*Real.log B)+
      (diskLogDerivativeConstant/3)*Real.log B2+1/principalPoleRadius := by positivity
  unfold heckePairZeroFreeError
  linarith

theorem hecke_zero_free_of_disk_pair
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L L2 : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    {B B2 t : ℝ} (hB : 1 < B) (hB2 : 1 < B2)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖normalizedHeckeDisk L t z‖ ≤ B)
    (hb2 : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖normalizedHeckeDisk L2 (2*t) z‖ ≤ B2)
    {β : ℝ} (hβ : 1-1/(32*heckePairZeroFreeError B B2) < β) :
    L ((β:ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
  intro hzero
  let E := heckePairZeroFreeError B B2
  have hE1 : 1 ≤ E := heckePairZeroFreeError_ge_one hB hB2
  have hE : 0 < E := lt_of_lt_of_le zero_lt_one hE1
  have hβ1 : β ≤ 1 := by
    simpa using heckeZero_real_le_one hχ hχ0 hχadd hs hzero
  have hw : 1/(32*E) ≤ (1/2:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 32*E)).mpr
    linarith
  have hβhalf : (1/2:ℝ) ≤ β := by change 1-1/(32*E)<β at hβ; linarith
  let d : ℝ := 1/(4*E)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp [d]
    apply (div_le_iff₀ (by positivity : 0 < 4*E)).mpr
    linarith
  have hEδ : 1/principalPoleRadius < E := by
    have hC := principalPoleConstant_pos
    have hK := diskLogDerivativeConstant_pos
    have hl1 := Real.log_pos hB
    have hl2 := Real.log_pos hB2
    have hp : 0 < 1+3*principalPoleConstant+
        4*((diskLogDerivativeConstant/3)*Real.log B)+
        (diskLogDerivativeConstant/3)*Real.log B2 := by positivity
    dsimp [E,heckePairZeroFreeError]
    linarith
  have hdδ : d < principalPoleRadius := by
    have hδ := principalPoleRadius_pos
    have hδE : 1 < E*principalPoleRadius := (div_lt_iff₀ hδ).mp hEδ
    dsimp [d]
    apply (div_lt_iff₀ (by positivity : 0 < 4*E)).mpr
    nlinarith
  have hσ : 1 < 1+d := by linarith
  have hσ2 : 1+d ≤ 2 := by linarith
  have hlow := hecke_logDeriv_lower_of_disk hχ hχ0 hχadd hL hs hB hb hσ hσ2 hβhalf hzero
  have hχ2 : ∀ ν, ‖(χ ν)^2‖ ≤ 1 := by
    intro ν
    rw [norm_pow]
    exact pow_le_one₀ (_root_.norm_nonneg _) (hχ ν)
  have hχ20 : (χ 0)^2=1 := by rw [hχ0]; norm_num
  have hχ2add : ∀ ν κ, (χ (ν+κ))^2=(χ ν)^2*(χ κ)^2 := by
    intro ν κ
    rw [hχadd,mul_pow]
  have hlow2 := hecke_logDeriv_real_lower_of_disk hχ2 hχ20 hχ2add hL2 hs2 hB2 hb2 hσ hσ2
  have hpole := principalPoleBound (1+d) hσ (by linarith)
  have hpos := idealLogDeriv_vertical_341_nonneg χ hχ hχ0 hχadd hσ t
  rw [←idealSeries_logDeriv_eq (fun s hs => principalIdealZeta_right hs) (by simpa using hσ),
    ←idealSeries_logDeriv_eq hs (by simpa using hσ),
    ←idealSeries_logDeriv_eq hs2 (by simpa using hσ)] at hpos
  simp only [Complex.neg_re] at hpole hpos
  change 0 ≤ 3* -(logDeriv principalIdealZeta ((1+d:ℝ):ℂ)).re+
    4* -(logDeriv L (((1+d:ℝ):ℂ)+(t:ℂ)*Complex.I)).re+
    -(logDeriv L2 (((1+d:ℝ):ℂ)+(2*t:ℝ)*Complex.I)).re at hpos
  have heq : 1+d-β=d+(1-β) := by ring
  have hneg := hecke_zero_free_numerical hE (show 0 ≤ 1-β by linarith)
    (show 1-β ≤ 1/(32*E) by change 1-1/(32*E)<β at hβ; linarith)
  change 3/d-4/(d+(1-β))+E < 0 at hneg
  have hEbound : 3*principalPoleConstant+
      4*((diskLogDerivativeConstant/3)*Real.log B)+
      (diskLogDerivativeConstant/3)*Real.log B2 ≤ E := by
    have hδ := principalPoleRadius_pos
    have hi : 0 < 1/principalPoleRadius := one_div_pos.mpr hδ
    dsimp [E,heckePairZeroFreeError]
    linarith
  rw [heq] at hlow
  have hone : 1+d-1=d := by ring
  rw [hone] at hpole
  simp only [div_eq_mul_inv,one_mul] at hneg hlow hpole
  linarith only [hpos,hpole,hlow,hlow2,hEbound,hneg]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDiskGrowth
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial and logarithmic conductor-height bounds for the actual
normalized Hecke disks. The constants depend only on the fixed ideal lattice. -/
noncomputable section
namespace CubicFirstMoment

lemma heckeDiskPolynomialConstant_gt_one : 1 < heckeDiskPolynomialConstant := by
  have h : 0 ≤ 32*(9/2:ℝ)^4*idealZetaTwo^2 := by positivity
  unfold heckeDiskPolynomialConstant
  linarith

theorem normalizedHeckeDiskBound_polynomial {A k u t : ℝ} {ε : ℂ}
    (hA : 0 < A) (hk : 0 ≤ k) (hε : ‖ε‖ ≤ 1) (hu : 1 ≤ u)
    (huA : A ≤ u) (huk : k+7 ≤ u) (hut : 4+|t| ≤ u) :
    normalizedHeckeDiskBound A k ε t ≤ heckeDiskPolynomialConstant*u^12 := by
  have hS := idealZetaTwo_pos
  have hu0 : 0 ≤ u := by linarith
  have hpA := pow_le_pow_left₀ hA.le huA 4
  have hpk := pow_le_pow_left₀ (show 0 ≤ k+7 by linarith) huk 4
  have hpt := pow_le_pow_left₀ (show 0 ≤ 4+|t| by positivity) hut 4
  have hu8 : 1 ≤ u^8 := one_le_pow₀ hu
  have hu12 : 1 ≤ u^12 := one_le_pow₀ hu
  have hprod : ‖ε‖*A^4*(k+7)^4*idealZetaTwo ≤ idealZetaTwo*u^8 := by
    calc
      ‖ε‖*A^4*(k+7)^4*idealZetaTwo ≤ 1*u^4*u^4*idealZetaTwo := by gcongr
      _ = _ := by ring
  have hinner : idealZetaTwo+‖ε‖*A^4*(k+7)^4*idealZetaTwo ≤
      2*idealZetaTwo*u^8 := by
    have hscale := mul_le_mul_of_nonneg_left hu8 hS.le
    nlinarith
  calc
    normalizedHeckeDiskBound A k ε t ≤
        2+idealZetaTwo*(2*idealZetaTwo*u^8*16*(9/2:ℝ)^4)*u^4 := by
      dsimp only [normalizedHeckeDiskBound,heckeZeroFreeMajorant]
      gcongr
    _ = 2+(32*(9/2:ℝ)^4*idealZetaTwo^2)*u^12 := by ring
    _ ≤ heckeDiskPolynomialConstant*u^12 := by
      unfold heckeDiskPolynomialConstant
      nlinarith

theorem normalizedHeckeDiskBound_log {A k u t : ℝ} {ε : ℂ}
    (hA : 0 < A) (hk : 0 ≤ k) (hε : ‖ε‖ ≤ 1) (hu : 1 ≤ u)
    (huA : A ≤ u) (huk : k+7 ≤ u) (hut : 4+|t| ≤ u) :
    Real.log (normalizedHeckeDiskBound A k ε t) ≤
      Real.log heckeDiskPolynomialConstant+12*Real.log u := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hC : 0 < heckeDiskPolynomialConstant :=
    zero_lt_one.trans heckeDiskPolynomialConstant_gt_one
  have h := Real.log_le_log (zero_lt_one.trans (normalizedHeckeDiskBound_gt_one A k ε t))
    (normalizedHeckeDiskBound_polynomial hA hk hε hu huA huk hut)
  simpa only [Real.log_mul hC.ne' (pow_pos hu0 12).ne',Real.log_pow,Nat.cast_ofNat] using h

theorem heckePairZeroFreeError_log {A A2 k k2 u t : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (hut : 4+|t| ≤ u) (hut2 : 4+|2*t| ≤ u) :
    heckePairZeroFreeError (normalizedHeckeDiskBound A k ε t)
      (normalizedHeckeDiskBound A2 k2 ε2 (2*t)) ≤ heckePairLogConstant*Real.log u := by
  have hu1 : 1 ≤ u := by linarith
  have h1 := normalizedHeckeDiskBound_log hA hk hε hu1 huA huk hut
  have h2 := normalizedHeckeDiskBound_log hA2 hk2 hε2 hu1 huA2 huk2 hut2
  have hD := diskLogDerivativeConstant_pos
  have hR := principalPoleRadius_pos
  have hP := principalPoleConstant_pos
  have hC := Real.log_pos heckeDiskPolynomialConstant_gt_one
  have h10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlu := Real.log_le_log (by norm_num : (0:ℝ)<10) hu
  let K : ℝ := 1+3*principalPoleConstant+1/principalPoleRadius+
    5*(diskLogDerivativeConstant/3)*Real.log heckeDiskPolynomialConstant
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hs : K ≤ (K/Real.log 10)*Real.log u := by
    calc
      K=(K/Real.log 10)*Real.log 10 := by field_simp
      _ ≤ (K/Real.log 10)*Real.log u := by gcongr
  have hb : heckePairZeroFreeError (normalizedHeckeDiskBound A k ε t)
      (normalizedHeckeDiskBound A2 k2 ε2 (2*t)) ≤ K+20*diskLogDerivativeConstant*Real.log u := by
    unfold heckePairZeroFreeError
    dsimp [K]
    nlinarith
  unfold heckePairLogConstant
  dsimp [K] at hs hb
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeZeroFreeLog
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The logarithmic zero-free width obtained from the actual polynomial
Hecke disk bounds, for a character and its square. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_zero_free_log_of_disks
    {χ : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    {L L2 : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    {A A2 k k2 u t : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (hut : 4+|t| ≤ u) (hut2 : 4+|2*t| ≤ u)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L t z‖ ≤ normalizedHeckeDiskBound A k ε t)
    (hb2 : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 (2*t) z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 (2*t))
    {β : ℝ} (hβ : 1-1/(32*heckePairLogConstant*Real.log u) < β) :
    L ((β:ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
  have he := heckePairZeroFreeError_log hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hut hut2
  have he1 := heckePairZeroFreeError_ge_one (normalizedHeckeDiskBound_gt_one A k ε t)
    (normalizedHeckeDiskBound_gt_one A2 k2 ε2 (2*t))
  have he0 : 0 < heckePairZeroFreeError (normalizedHeckeDiskBound A k ε t)
      (normalizedHeckeDiskBound A2 k2 ε2 (2*t)) := by linarith
  have hrec : 1/(32*heckePairLogConstant*Real.log u) ≤
      1/(32*heckePairZeroFreeError (normalizedHeckeDiskBound A k ε t)
        (normalizedHeckeDiskBound A2 k2 ε2 (2*t))) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  exact hecke_zero_free_of_disk_pair hχ hχ0 hχadd hL hL2 hs hs2
    (normalizedHeckeDiskBound_gt_one A k ε t)
    (normalizedHeckeDiskBound_gt_one A2 k2 ε2 (2*t)) hb hb2 (by linarith)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSquareDisk
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The existing zero-free argument needs only the actual square series
and its normalized disk bound. This permits the proved finite Euler correction. -/
noncomputable section
namespace CubicFirstMoment

theorem hecke_zero_free_log_from_square_disk_oai
    {χ χdual : EisensteinIdealExponent → ℂ} (hχ : ∀ ν, ‖χ ν‖ ≤ 1)
    (hχ0 : χ 0=1) (hχadd : ∀ ν κ, χ (ν+κ)=χ ν*χ κ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {L Ldual L2 : ℂ → ℂ} (hL : Differentiable ℂ L) (hL2 : Differentiable ℂ L2)
    (hs : ∀ s : ℂ, 1 < s.re → L s=normDirichletSeries χ idealExponentNorm s)
    (hs2 : ∀ s : ℂ, 1 < s.re → L2 s=normDirichletSeries (fun ν => (χ ν)^2) idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s=normDirichletSeries χdual idealExponentNorm s)
    {A A2 k k2 u t : ℝ} {ε ε2 : ℂ}
    (hA : 0 < A) (hA2 : 0 < A2) (hk : 0 ≤ k) (hk2 : 0 ≤ k2)
    (hε : ‖ε‖ ≤ 1) (hε2 : ‖ε2‖ ≤ 1) (hu : 10 ≤ u)
    (huA : A ≤ u) (huA2 : A2 ≤ u) (huk : k+7 ≤ u) (huk2 : k2+7 ≤ u)
    (hut : 4+|t| ≤ u) (hut2 : 4+|2*t| ≤ u)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hdisk2 : ∀ t z, ‖z‖ ≤ (7/8:ℝ) →
      ‖normalizedHeckeDisk L2 t z‖ ≤ normalizedHeckeDiskBound A2 k2 ε2 t)
    {β : ℝ} (hβ : 1-1/(32*heckePairLogConstant*Real.log u) < β) :
    L ((β:ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
  apply hecke_zero_free_log_of_disks hχ hχ0 hχadd hL hL2 hs hs2
    hA hA2 hk hk2 hε hε2 hu huA huA2 huk huk2 hut hut2
    (β := β) (hβ := hβ)
  · intro z hz
    exact normalizedHeckeDisk_bound hχ hχ0 hχadd hχdual hA hk hL hs hds hFE hcomp t z
      (hz.trans (by norm_num))
  · intro z hz
    exact hdisk2 (2*t) z hz

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.hecke_zero_free_log_from_square_disk_oai := @OAI.CubicFirstMoment.hecke_zero_free_log_from_square_disk_oai
