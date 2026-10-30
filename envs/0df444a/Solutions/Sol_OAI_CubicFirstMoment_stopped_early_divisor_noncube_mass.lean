-- Prove2me | solution 1 for OAI.CubicFirstMoment.stopped_early_divisor_noncube_mass
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:47:33.189866+00:00
-- url     : https://prove2.me/submissions/08e6036b-52ba-4b6a-8c0b-f3ab07f52783
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015
import Theorems.Thm_OAI_CubicFirstMoment_outer_core_block_sieve
import Theorems.Thm_OAI_CubicFirstMoment_smallB_core_hybrid_sieve
import Theorems.Thm_OAI_CubicFirstMoment_stopped_low_core_mass

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unique primary associates and canonical prime factorization. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma primaryPrimeFactors_norm_prod {n : Eisenstein} (hn : primary n) (hs : Squarefree n) :
    ∏ p ∈ primaryPrimeFactors n, normNat p = normNat n := by
  calc
    _ = normNat (∏ p ∈ primaryPrimeFactors n, p) := (map_prod normNatHom _ _).symm
    _ = normNat n := congrArg normNat (primaryPrimeFactors_prod hn hs)

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ideal Moebius weights and exact prime-factor subset identities. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
open UniqueFactorizationMonoid

lemma idealMoebius_sq (b : Eisenstein) :
    (idealMoebius b : ℝ)^2 = if Squarefree b then 1 else 0 := by
  unfold idealMoebius UniqueFactorizationMonoid.moebius
  split_ifs <;> push_cast
  · rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  · norm_num

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite cubic sieve operators, bilinear norms and coprime completion. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

open UniqueFactorizationMonoid

namespace CubicFirstMoment

lemma norm_idealMoebius_le_one (m : Eisenstein) : ‖(idealMoebius m : ℂ)‖ ≤ 1 := by
  have hs : (idealMoebius m : ℝ)^2 ≤ 1 := by
    rw [idealMoebius_sq]
    split_ifs <;> norm_num
  have hn : ‖(idealMoebius m : ℂ)‖ = |(idealMoebius m : ℝ)| :=
    Complex.norm_intCast _
  rw [hn]
  nlinarith [sq_abs (idealMoebius m : ℝ), abs_nonneg (idealMoebius m : ℝ)]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency dyads and summable base Gram recurrences. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normNat_ne_zero_of_ne_zero {h : Eisenstein} (hh : h ≠ 0) : normNat h ≠ 0 := by
  intro hz
  apply hh
  apply norm_eq_zero_iff.mp
  rw [← normNat_cast,hz,Nat.cast_zero]

lemma mem_frequencyDyad {j : ℕ} {h : Eisenstein} :
    h ∈ frequencyDyad j ↔ h ≠ 0 ∧ Nat.log 2 (normNat h) = j := by
  simp only [frequencyDyad, Finset.mem_filter, mem_nonzeroNormBall]
  refine ⟨fun h => ⟨h.1.2,h.2⟩,fun hh => ⟨⟨?_,hh.1⟩,hh.2⟩⟩
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at ht
  rw [← normNat_cast]
  exact_mod_cast ht.le

lemma frequencyDyad_norm {j : ℕ} {h : Eisenstein} (hh : h ∈ frequencyDyad j) :
    (2 : ℝ)^j ≤ norm h ∧ norm h ≤ 2*(2 : ℝ)^j := by
  rw [mem_frequencyDyad] at hh
  have hl := Nat.pow_log_le_self 2 (normNat_ne_zero_of_ne_zero hh.1)
  have ht := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (normNat h)
  rw [hh.2] at hl ht
  rw [← normNat_cast]
  constructor
  · exact_mod_cast hl
  · have ht' : (normNat h : ℝ) ≤ (2 : ℝ)^(j+1) := by exact_mod_cast ht.le
    simpa [pow_succ,mul_comm] using ht'

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_FullCubeExtraction
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ramified residual factors and full cube decomposition. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem cube_decomposition (n : Eisenstein) :
    ∃ s t c : Eisenstein, Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧ n = s*t^2*c^3 := by
  refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
  · exact ⟨1,1,0,squarefree_one,squarefree_one,isCoprime_one_left,by simp⟩
  · intro u hu
    exact ⟨u,1,1,hu.squarefree,squarefree_one,isCoprime_one_right,by simp⟩
  · intro b p hb hp ih
    obtain ⟨s,t,c,hss,hst,hcop,rfl⟩ := ih
    by_cases hps : p ∣ s
    · obtain ⟨s',rfl⟩ := hps
      have hps' : IsCoprime p s' := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hss).1
      have hpt : IsCoprime p t := hcop.of_mul_left_left
      refine ⟨s',p*t,c,hss.of_mul_right,
        squarefree_mul_iff.mpr ⟨hpt.isRelPrime,hp.squarefree,hst⟩,
        hps'.symm.mul_right hcop.of_mul_left_right,?_⟩
      ring
    · by_cases hpt : p ∣ t
      · obtain ⟨t',rfl⟩ := hpt
        refine ⟨s,t',p*c,hss,hst.of_mul_right,hcop.of_mul_right_right,?_⟩
        ring
      · have hps' := hp.coprime_iff_not_dvd.mpr hps
        have hpt' := hp.coprime_iff_not_dvd.mpr hpt
        refine ⟨p*s,t,c,squarefree_mul_iff.mpr ⟨hps'.isRelPrime,hp.squarefree,hss⟩,
          hst,hpt'.mul_left hcop,?_⟩
        ring

theorem squarefree_ramified_split (n : Eisenstein) (hs : Squarefree n) :
    ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
  have h : ∀ n : Eisenstein, Squarefree n →
      ∃ d e : Eisenstein, d ∣ 3 ∧ IsCoprime e 3 ∧ n = d*e := by
    intro n
    refine UniqueFactorizationMonoid.induction_on_prime n ?_ ?_ ?_
    · intro hs
      have hh := hs 0 (by simp)
      exact (not_isUnit_zero hh).elim
    · intro u hu hs
      refine ⟨1,u,one_dvd _,?_,by simp⟩
      exact (isCoprime_zero_right.mpr hu).of_isCoprime_of_dvd_right (dvd_zero 3)
    · intro b p hb hp ih hs
      obtain ⟨d,e,hd,he,hbe⟩ := ih hs.of_mul_right
      have hpb : IsCoprime p b := isRelPrime_iff_isCoprime.mp (squarefree_mul_iff.mp hs).1
      by_cases hp3 : p ∣ 3
      · have hpd : IsCoprime p d := (hbe ▸ hpb).of_mul_right_left
        refine ⟨p*d,e,hpd.mul_dvd hp3 hd,he,?_⟩
        rw [hbe]; ring
      · refine ⟨d,p*e,hd,(hp.coprime_iff_not_dvd.mpr hp3).mul_left he,?_⟩
        rw [hbe]; ring
  exact h n hs

lemma unit_residue_of_isCoprime_three {e : Eisenstein} (he : IsCoprime e 3) :
    IsUnit (Ideal.Quotient.mk (modulus 3) e) := by
  have h := he.map (Ideal.Quotient.mk (modulus 3))
  simpa only [residue_three_eq_zero, isCoprime_zero_right] using h

lemma norm_le_of_dvd {a b : Eisenstein} (hb : b ≠ 0) (hd : a ∣ b) :
    norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := hd
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg a) (one_le_norm hc)

theorem squarefree_primary_residual (n : Eisenstein) (hs : Squarefree n) :
    ∃ r s : Eisenstein, r ≠ 0 ∧ norm r ≤ 9 ∧ primary s ∧ Squarefree s ∧ n = r*s := by
  obtain ⟨d,e,hd,he,hde⟩ := squarefree_ramified_split n hs
  obtain ⟨u,hu,hprim⟩ := unit_lift_mod_three (unit_residue_of_isCoprime_three he)
  obtain ⟨v,rfl⟩ := hu
  have hd0 : d ≠ 0 := by
    intro hd0
    rw [hd0, zero_dvd_iff] at hd
    norm_num at hd
  have hvi : norm (↑v⁻¹ : Eisenstein) = 1 := by
    rw [← normNat_cast, normNat_of_isUnit (Units.isUnit _), Nat.cast_one]
  refine ⟨d*(↑v⁻¹ : Eisenstein),e*(↑v : Eisenstein),mul_ne_zero hd0 (Units.ne_zero _),?_,hprim,?_,?_⟩
  · rw [norm_mul_eq, hvi, mul_one]
    have h := norm_le_of_dvd (by norm_num : (3 : Eisenstein) ≠ 0) hd
    have h3 : norm (3 : Eisenstein) = 9 := by
      change Complex.normSq (3 : ℂ) = 9
      norm_num
    simpa only [h3] using h
  · have hes : Squarefree e := (hde ▸ hs).of_mul_right
    exact squarefree_mul_iff.mpr ⟨((isCoprime_zero_left.mpr (Units.isUnit v)).of_isCoprime_of_dvd_left (dvd_zero e)).isRelPrime,hes,
      (Units.isUnit v).squarefree⟩
  · rw [hde]
    simp [mul_assoc, mul_left_comm, mul_comm]

end CubicFirstMoment

namespace CubicFirstMoment

theorem full_cube_decomposition {n : Eisenstein} (hn : n ≠ 0) :
    ∃ r s t c : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      c ≠ 0 ∧ n = r*s*t^2*c^3 := by
  obtain ⟨s₀,t₀,c,hs₀,ht₀,hst,hn'⟩ := cube_decomposition n
  obtain ⟨r,s,hr0,hr,hs,hss,hs'⟩ := squarefree_primary_residual s₀ hs₀
  obtain ⟨q,t,hq0,hq,ht,hst',ht'⟩ := squarefree_primary_residual t₀ ht₀
  have hc0 : c ≠ 0 := by intro hc; simp [hc] at hn'; exact hn hn'
  have hcop : IsCoprime s t :=
    hst.of_isCoprime_of_dvd_left (hs' ▸ dvd_mul_left s r) |>.of_isCoprime_of_dvd_right
      (ht' ▸ dvd_mul_left t q)
  refine ⟨r*q^2,s,t,c,mul_ne_zero hr0 (pow_ne_zero _ hq0),?_,hs,ht,hss,hst',hcop,hc0,?_⟩
  · rw [norm_mul_eq]
    have he : norm (q^2) = norm q ^ 2 := by simp [pow_two]
    rw [he]
    have hq2 : norm q ^ 2 ≤ 81 := by nlinarith [norm_nonneg q]
    nlinarith [norm_nonneg r, sq_nonneg (norm q)]
  · rw [hn',hs',ht']; ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubeEstimates
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric decay, cube frequency dyads and numerical block inequalities. -/

section

noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_squarefreePrimaryDyad {n : Eisenstein} {j : ℕ} :
    n ∈ squarefreePrimaryDyad j ↔ n ∈ frequencyDyad j ∧ primary n ∧ Squarefree n := by
  simp [squarefreePrimaryDyad]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Convergent norm series on the Eisenstein lattice

These elementary lattice bounds provide a quantitative tail for the
Möbius residue sum after square-divisor truncation.
-/

noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment

lemma norm_rpow_tail_pointwise {D s t : ℝ} (hD : 0 < D) (hst : s < t)
    {a : Eisenstein} (ha : D < norm a) :
    norm a^(-t) ≤ D^(s-t)*norm a^(-s) := by
  have hn : 0 < norm a := hD.trans ha
  calc
    _ = norm a^(s-t)*norm a^(-s) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hD ha.le (by linarith))
      (Real.rpow_nonneg hn.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform coefficient bounds for a bounded number of ordered prime factors. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Every prime in another tuple with the same product occurs in the
reference tuple. This includes repeated primes. -/
lemma prime_tuple_range_subset (f g : ι → Eisenstein)
    (hf : ∀ i, primaryPrime (f i)) (hg : ∀ i, primaryPrime (g i))
    (hprod : (∏ i, g i) = ∏ i, f i) (i : ι) :
    g i ∈ Finset.univ.image f := by
  have hd : g i ∣ ∏ j, f j := hprod ▸ Finset.dvd_prod_of_mem g (Finset.mem_univ i)
  obtain ⟨j,_,hj⟩ := ((hg i).2.dvd_finsetProd_iff f).mp hd
  have he : g i = f j := primary_associated_eq (hg i).1 (hf j).1
    (((hg i).2.dvd_prime_iff_associated (hf j).2).mp hj)
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩

/-- The deliberately generous `k^k` bound avoids ordering conventions and
is uniform in the norm and in all independent supports. -/
theorem prime_tuple_fiber_card (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (b : Eisenstein) :
    ((Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)).card ≤
      (Fintype.card ι)^(Fintype.card ι) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  by_cases ht : T.Nonempty
  · obtain ⟨f,hf⟩ := ht
    have hfs := (Finset.mem_filter.mp hf).1
    have hfb := (Finset.mem_filter.mp hf).2
    have hprime : ∀ i, primaryPrime (f i) :=
      fun i => hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)
    have hsub : T ⊆ Fintype.piFinset (fun _ : ι => Finset.univ.image f) := by
      intro g hg
      obtain ⟨hgs,hgb⟩ := Finset.mem_filter.mp hg
      apply Fintype.mem_piFinset.mpr
      exact prime_tuple_range_subset f g hprime
        (fun i => hS i (g i) ((Fintype.mem_piFinset.mp hgs) i)) (hgb.trans hfb.symm)
    calc
      T.card ≤ (Fintype.piFinset (fun _ : ι => Finset.univ.image f)).card :=
        Finset.card_le_card hsub
      _ = ((Finset.univ.image f).card)^(Fintype.card ι) := by
        simp [Fintype.card_piFinset]
      _ ≤ _ := Nat.pow_le_pow_left (by
        simpa using (Finset.card_image_le (s := (Finset.univ:Finset ι)) (f := f))) _
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change T.card ≤ _
    rw [he,Finset.card_empty]
    exact Nat.zero_le _

/-- The coefficient bound depends only on the number of prime factors
and on their separate weight bounds, including for nonsquarefree products. -/
theorem orderedConvolution_norm_bound (S : ι → Finset Eisenstein)
    (w : ι → Eisenstein → ℂ) (M : ι → ℝ)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (hM : ∀ i, 0 ≤ M i) (hw : ∀ i, ∀ p ∈ S i, ‖w i p‖ ≤ M i)
    (b : Eisenstein) :
    ‖orderedConvolution S w b‖ ≤
      ((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i) := by
  let T := (Fintype.piFinset S).filter (fun f => (∏ i, f i) = b)
  have hprod : 0 ≤ ∏ i, M i := Finset.prod_nonneg (fun i _ => hM i)
  unfold orderedConvolution
  calc
    _ ≤ ∑ f ∈ T, ‖∏ i, w i (f i)‖ := norm_sum_le _ _
    _ ≤ ∑ _f ∈ T, ∏ i, M i := by
      apply Finset.sum_le_sum
      intro f hf
      rw [norm_prod]
      exact Finset.prod_le_prod (fun i _ => _root_.norm_nonneg _)
        (fun i _ => hw i (f i) ((Fintype.mem_piFinset.mp (Finset.mem_filter.mp hf).1) i))
    _ = (T.card:ℝ)*(∏ i, M i) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (prime_tuple_fiber_card S hS b)) hprod

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryConvolutionEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-length convolutions of arbitrary primary elements. The divisor
bound absorbs the tuple multiplicity in any positive norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma orderedPrimarySupport_primary (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ a ∈ S i, primary a) {b : Eisenstein}
    (hb : b ∈ orderedConvolutionSupport S) : primary b := by
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  exact primary_finset_prod _ _ (fun i _ => hS i (f i) (Fintype.mem_piFinset.mp hf i))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic multiplicities and moments of products of finitely many prime powers. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

/-- A fixed logarithmic power is bounded by every positive norm power,
with an explicit constant uniform down to norm one. -/
lemma natLog_power_bound (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ((Nat.log 2 n + 1 : ℕ) : ℝ)^m ≤ C*(n:ℝ)^ε := by
  by_cases hm : m = 0
  · subst m
    refine ⟨1,zero_lt_one,?_⟩
    intro n hn
    simpa using Real.one_le_rpow (by exact_mod_cast hn) hε.le
  let δ : ℝ := ε/m
  have hm0 : (0:ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hδ : 0 < δ := div_pos hε hm0
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A : ℝ := 1/(δ*Real.log 2)+1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A^m,pow_pos hA _,?_⟩
  intro n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := zero_lt_one.trans_le hn1
  have hlog : (Nat.log 2 n:ℝ) ≤ Real.log n/Real.log 2 := by
    change (Nat.log 2 n:ℝ) ≤ Real.logb (2:ℝ) (n:ℝ)
    rw [← Real.natFloor_logb_natCast 2 n]
    exact Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hn1)
  have hx : 1 ≤ (n:ℝ)^δ := Real.one_le_rpow hn1 hδ.le
  have hbase : ((Nat.log 2 n+1:ℕ):ℝ) ≤ A*(n:ℝ)^δ := by
    push_cast
    calc
      _ ≤ Real.log n/Real.log 2+1 := by linarith
      _ ≤ ((n:ℝ)^δ/δ)/Real.log 2+(n:ℝ)^δ :=
        add_le_add (div_le_div_of_nonneg_right (Real.log_le_rpow_div hn0.le hδ) hL.le) hx
      _ = _ := by dsimp [A]; ring
  have he : ((n:ℝ)^δ)^m = (n:ℝ)^ε := by
    rw [← Real.rpow_mul_natCast hn0.le]
    congr 1
    dsimp [δ]
    exact div_mul_cancel₀ ε (ne_of_gt hm0)
  calc
    _ ≤ (A*(n:ℝ)^δ)^m := pow_le_pow_left₀ (by positivity) hbase m
    _ = _ := by rw [mul_pow,he]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FixedScalePowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed dilations preserve every strict exponent margin used by the
finite output partition. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventually_const_mul_rpow_le {a b : ℝ} (hab : a < b) (C : ℝ) :
    ∀ᶠ Y : ℝ in atTop, C*Y^a ≤ Y^b := by
  filter_upwards [eventually_gt_atTop (0:ℝ),
    (tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop C] with Y hY hC
  calc
    _ ≤ Y^(b-a)*Y^a := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hY.le _)
    _ = _ := by rw [← Real.rpow_add hY]; congr 1; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SieveMobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The Möbius coefficient below the sieve truncation

The union convolution of the squarefree Möbius weights is the same
Möbius weight. This proves the exact low-divisor coefficient identity,
which is stronger than a divisor bound and is needed in the residue.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrimeFactors_finset_prod (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) :
    primaryPrimeFactors (∏ p ∈ U, p) = U := by
  have hprod := primary_finset_prod U (fun p : Eisenstein => p) (fun p hp => (hU p hp).1)
  ext p
  rw [primaryPrime_mem_factors_iff hprod]
  constructor
  · rintro ⟨hp,hd⟩
    obtain ⟨q,hq,hpq⟩ := (hp.2.dvd_finsetProd_iff (fun p : Eisenstein => p)).mp hd
    have he : p = q := primary_associated_eq hp.1 (hU q hq).1
      (hp.2.associated_of_dvd (hU q hq).2 hpq)
    exact he ▸ hq
  · intro hp
    exact ⟨hU p hp,Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp⟩

lemma primaryPrimeFactors_prod_injective {U : Finset Eisenstein}
    (hU : ∀ p ∈ U, primaryPrime p) :
    Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s, p) (↑U.powerset : Set (Finset Eisenstein)) := by
  intro s hs t ht he
  have hs' := Finset.mem_powerset.mp hs
  have ht' := Finset.mem_powerset.mp ht
  have hh := congrArg primaryPrimeFactors he
  simpa only [primaryPrimeFactors_finset_prod s (fun p hp => hU p (hs' hp)),
    primaryPrimeFactors_finset_prod t (fun p hp => hU p (ht' hp))] using hh

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual primary factor tuples in the distinguished-prime expansion.
Ordering a subset contributes its factorial; the remaining primary factor
is the literal complementary product, not an abstract coefficient. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma distinguishedPrimeWeight_support {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 0 < w) (hwz : w ≤ z) {p : Eisenstein}
    (hp : 0 < norm p) (hne : distinguishedPrimeWeight ψ w z p ≠ 0) :
    w < norm p ∧ norm p < 2*z := by
  have hz : 0 < z := hw.trans_le hwz
  constructor
  · by_contra h
    have hpw : norm p ≤ w := not_lt.mp h
    apply hne
    rw [distinguishedPrimeWeight,hψone _ (div_pos hp hw) ((div_le_one hw).mpr hpw),
      hψone _ (div_pos hp hz) ((div_le_one hz).mpr (hpw.trans hwz)),sub_self]
    rfl
  · by_contra h
    have hpz : 2*z ≤ norm p := not_lt.mp h
    apply hne
    rw [distinguishedPrimeWeight,hψzero _ ((le_div_iff₀ hw).mpr (by linarith)),
      hψzero _ ((le_div_iff₀ hz).mpr hpz),sub_self]
    rfl

/-- Every chosen prime is large; the product bound therefore bounds the
number of chosen factors, uniformly in the original squarefree element. -/
lemma primary_factor_subset_card_lt {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n)
    {w : ℝ} (hw : 1 ≤ w) (hlarge : ∀ p ∈ s, w ≤ norm p)
    {k : ℕ} (hsize : norm n < w^k) : s.card < k := by
  have hprod : w^s.card ≤ norm n := by
    calc
      _ = ∏ _p ∈ s, w := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ s, norm p := Finset.prod_le_prod (fun _ _ => zero_le_one.trans hw) hlarge
      _ ≤ (∏ p ∈ s, norm p)*(∏ p ∈ primaryPrimeFactors n \ s, norm p) :=
        le_mul_of_one_le_right (Finset.prod_nonneg (fun p _ => norm_nonneg p))
          (Finset.one_le_prod (fun p hp => one_le_norm
            (primaryPrimeFactor_spec hn (Finset.mem_sdiff.mp hp).1).1.2.ne_zero))
      _ = ∏ p ∈ primaryPrimeFactors n, norm p := by
        rw [mul_comm,Finset.prod_sdiff hsub]
      _ = norm n := by
        simpa only [Nat.cast_prod,normNat_cast] using
          congrArg (fun m : ℕ => (m:ℝ)) (primaryPrimeFactors_norm_prod hn hs)
  by_contra h
  exact (not_lt_of_ge ((pow_le_pow_right₀ hw (not_lt.mp h)).trans hprod)) hsize

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Literal independent coefficients from the stopping construction.
The selected-side test may contain the first-stage failure and crossing
conditions; the remaining-side test is a separate condition on its divisor.
No coprimality condition is inserted between the two sides. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPairFiber_card_le (S T : Finset Eisenstein)
    (hS : ∀ r ∈ S, primary r) (b : Eisenstein) :
    (primaryPairFiber S T b).card ≤ (S.filter (fun r => r ∣ b)).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    have hm := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
    exact Finset.mem_filter.mpr ⟨hm.1,⟨p.2,(Finset.mem_filter.mp hp).2.symm⟩⟩
  · intro p hp q hq he
    apply Prod.ext he
    have hmul : p.1*p.2 = p.1*q.2 := by
      calc
        _ = b := (Finset.mem_filter.mp hp).2
        _ = q.1*q.2 := (Finset.mem_filter.mp hq).2.symm
        _ = _ := by rw [he]
    exact mul_left_cancel₀ (primary_ne_zero
      (hS p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1)) hmul

lemma primaryPairCoefficient_norm_le (S T : Finset Eisenstein)
    (hS : ∀ r ∈ S, primary r) (b : Eisenstein)
    (w : Eisenstein × Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ p ∈ primaryPairFiber S T b, ‖w p‖ ≤ M) :
    ‖primaryPairCoefficient S T w b‖ ≤ ((S.filter (fun r => r ∣ b)).card:ℝ)*M := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hw).trans
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (primaryPairFiber_card_le S T hS b)) hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeDetectorCutoff
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit smooth cutoff for the exact prime detector. -/
noncomputable section
open Filter
open scoped ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primeDetectorCutoff_nonneg (x : ℝ) : 0 ≤ primeDetectorCutoff x :=
  sub_nonneg.mpr (Real.smoothTransition.le_one _)

lemma primeDetectorCutoff_le_one (x : ℝ) : primeDetectorCutoff x ≤ 1 := by
  unfold primeDetectorCutoff
  linarith [Real.smoothTransition.nonneg (x-1)]

lemma primeDetectorCutoff_one {x : ℝ} (hx : x ≤ 1) : primeDetectorCutoff x = 1 := by
  rw [primeDetectorCutoff,Real.smoothTransition.zero_of_nonpos (by linarith),sub_zero]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoefficientBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise bounds for the actual stopped coefficients, before any
analytic sequence estimate. The divisor count is literal and introduces
no dependence on the number or width of prime bins. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cutoffMoebius_norm_le_one {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ) (d : Eisenstein) :
    ‖cutoffMoebius ψ w d‖ ≤ 1 := by
  rw [cutoffMoebius,norm_mul,norm_prod]
  have hp : (∏ p ∈ primaryPrimeFactors d, ‖(ψ (norm p/w):ℂ)‖) ≤ 1 := by
    apply Finset.prod_le_one (fun _ _ => _root_.norm_nonneg _)
    intro p hp
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hψ _).1] using (hψ (norm p/w)).2
  exact (mul_le_mul (norm_idealMoebius_le_one d) hp
    (Finset.prod_nonneg (fun _ _ => _root_.norm_nonneg _)) zero_le_one).trans_eq (one_mul 1)

theorem stoppedBeta_divisor_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w : ℝ)
    (selected : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M) (b : Eisenstein) :
    ‖stoppedBeta R D v ψ w selected b‖ ≤ ((R.filter (fun r => r ∣ b)).card:ℝ)*M := by
  apply primaryPairCoefficient_norm_le R D hR b _ hM
  intro p hp
  by_cases hs : selected p.1 p.2
  · simp only [ite_eq_left hs,norm_mul]
    exact (mul_le_mul_of_nonneg_left (cutoffMoebius_norm_le_one hψ w p.2)
      (_root_.norm_nonneg _)).trans ((mul_one _).le.trans
        (hv p.1 (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1))
  · simpa only [ite_eq_right hs,norm_zero] using hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedCoefficients
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished-tuple weight occurring in stopped coefficients.
Its multiplicity is bounded in terms of the fixed tuple length, so the
literal beta coefficient has one divisor-count loss independently of bins. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma distinguishedPrimeWeight_norm_le_one {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w z : ℝ) (p : Eisenstein) :
    ‖distinguishedPrimeWeight ψ w z p‖ ≤ 1 := by
  rw [distinguishedPrimeWeight,Complex.norm_real,Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith [(hψ (norm p/w)).1,(hψ (norm p/w)).2,
    (hψ (norm p/z)).1,(hψ (norm p/z)).2]

theorem distinguishedTupleCoefficient_norm (S : ι → Finset Eisenstein)
    (hS : ∀ i, ∀ p ∈ S i, primaryPrime p) (W : ι → Eisenstein → ℂ)
    (hW : ∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) {ψ : ℝ → ℝ}
    (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (w z : ℝ) (r : Eisenstein) :
    ‖distinguishedTupleCoefficient S W ψ w z r‖ ≤
      ‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
        ((Fintype.card ι)^(Fintype.card ι):ℕ) := by
  unfold distinguishedTupleCoefficient
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
  have hp (i : ι) (p : Eisenstein) (hp : p ∈ S i) :
      ‖W i p*distinguishedPrimeWeight ψ w z p‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (hW i p hp) (distinguishedPrimeWeight_norm_le_one hψ w z p)
      (_root_.norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  simpa only [Finset.prod_const_one,mul_one] using
    orderedConvolution_norm_bound S (fun i p => W i p*distinguishedPrimeWeight ψ w z p)
      (fun _ => 1) hS (fun _ => zero_le_one) hp r

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BoundedPrimeTuples
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniformly bounded tuple lengths in the manuscript's actual
prime detector. The bound depends on xi, not on the envelope scale. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventually_prime_tuple_norm_bound {ξ C : ℝ} (hC : 0 < C)
    {k : ℕ} (hk : 1 < ξ*(k:ℝ)) :
    ∀ᶠ X : ℝ in atTop, C*X < (X^ξ)^k := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    eventually_const_mul_rpow_le hk (2*C)] with X hX h
  rw [Real.rpow_one] at h
  rw [←Real.rpow_natCast,←Real.rpow_mul (zero_lt_one.trans hX).le]
  nlinarith [mul_pos hC (zero_lt_one.trans hX)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_RoughDivisorBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The distinguished divisor is rough at a fixed power scale. On a
squarefree product this gives a uniform number of possible distinguished
divisors, stronger than the generic divisor bound for stopped beta. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem rough_primary_divisor_card (R : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {b : Eisenstein} (hb : primary b) (hs : Squarefree b)
    {w : ℝ} (hw : 1 ≤ w) (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    {k : ℕ} (hsize : norm b < w^k) :
    (R.filter (fun r => r ∣ b)).card ≤ 2^k := by
  let T := R.filter (fun r => r ∣ b)
  let L := (primaryPrimeFactors b).filter (fun p => w ≤ norm p)
  have hS (r : Eisenstein) (hr : r ∈ T) : Squarefree r :=
    fun x hx => hs x (hx.trans (Finset.mem_filter.mp hr).2)
  have hL : L.card < k := primary_factor_subset_card_lt hb hs
    (Finset.filter_subset _ _) hw (fun p hp => (Finset.mem_filter.mp hp).2) hsize
  have hcard : T.card ≤ L.powerset.card := by
    apply Finset.card_le_card_of_injOn primaryPrimeFactors
    · intro r hr
      apply Finset.mem_powerset.mpr
      intro p hp
      have hp' := primaryPrimeFactor_spec (hR r (Finset.mem_filter.mp hr).1) hp
      exact Finset.mem_filter.mpr ⟨primaryPrime_mem_factors hb hp'.1
        (hp'.2.trans (Finset.mem_filter.mp hr).2),hrough r (Finset.mem_filter.mp hr).1 p hp⟩
    · intro r hr q hq he
      calc
        r = ∏ p ∈ primaryPrimeFactors r, p :=
          (primaryPrimeFactors_prod (hR r (Finset.mem_filter.mp hr).1) (hS r hr)).symm
        _ = ∏ p ∈ primaryPrimeFactors q, p := by rw [he]
        _ = q := primaryPrimeFactors_prod (hR q (Finset.mem_filter.mp hq).1) (hS q hq)
  exact hcard.trans (by rw [Finset.card_powerset]; exact Nat.pow_le_pow_right (by decide) hL.le)

theorem stoppedBeta_rough_bound (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (w : ℝ) (hw : 1 ≤ w) (hrough : ∀ r ∈ R, ∀ p ∈ primaryPrimeFactors r, w ≤ norm p)
    (selected : Eisenstein → Eisenstein → Prop) (v : Eisenstein → ℂ)
    {M : ℝ} (hM : 0 ≤ M) (hv : ∀ r ∈ R, ‖v r‖ ≤ M)
    {b : Eisenstein} (hb : primary b) (hs : Squarefree b) {k : ℕ} (hsize : norm b < w^k) :
    ‖stoppedBeta R D v ψ w selected b‖ ≤ (2^k:ℕ)*M := by
  apply (stoppedBeta_divisor_bound R D hR hψ w selected v hM hv b).trans
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr
    (rough_primary_divisor_card R hR hb hs hw hrough hsize)) hM

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedRoughness
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The roughness of the actual distinguished coefficient, followed by
a uniform bound for the stopped beta. Zero distinguished coefficients
are removed before counting divisors, so no support hypothesis is added. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem distinguishedTupleCoefficient_prime_support
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) {ψ : ℝ → ℝ}
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 0 < w) (hwz : w ≤ z) {r p : Eisenstein}
    (hr : distinguishedTupleCoefficient S W ψ w z r ≠ 0)
    (hp : primaryPrime p) (hpr : p ∣ r) : w < norm p ∧ norm p < 2*z := by
  have ho : orderedConvolution S (fun i q => W i q*distinguishedPrimeWeight ψ w z q) r ≠ 0 :=
    (mul_ne_zero_iff.mp hr).2
  obtain ⟨f,hf,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ho
  obtain ⟨hfs,hfr⟩ := Finset.mem_filter.mp hf
  have hd : p ∣ ∏ i, f i := by rw [hfr]; exact hpr
  obtain ⟨i,_,hpi⟩ := (hp.2.dvd_finsetProd_iff f).mp hd
  have hfi := hS i (f i) ((Fintype.mem_piFinset.mp hfs) i)
  have he : p = f i := primary_associated_eq hp.1 hfi.1
    ((hp.2.dvd_prime_iff_associated hfi.2).mp hpi)
  have hweight := (mul_ne_zero_iff.mp
    ((Finset.prod_ne_zero_iff.mp hterm) i (Finset.mem_univ i))).2
  rw [he]
  exact distinguishedPrimeWeight_support hψone hψzero hw hwz
    (zero_lt_one.trans_le (one_le_norm hfi.2.ne_zero)) hweight

lemma stoppedBeta_filter_nonzero (R D : Finset Eisenstein) (v : Eisenstein → ℂ)
    (ψ : ℝ → ℝ) (w : ℝ) (selected : Eisenstein → Eisenstein → Prop) (b : Eisenstein) :
    stoppedBeta (R.filter (fun r => v r ≠ 0)) D v ψ w selected b =
      stoppedBeta R D v ψ w selected b := by
  unfold stoppedBeta primaryPairCoefficient
  apply Finset.sum_subset
  · intro q hq
    obtain ⟨hq,hprod⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqr,hqd⟩ := Finset.mem_product.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(Finset.mem_filter.mp hqr).1,hqd⟩,hprod⟩
  · intro q hq hn
    obtain ⟨hq,hprod⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqr,hqd⟩ := Finset.mem_product.mp hq
    have hz : v q.1 = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨hqr,h⟩,hqd⟩,hprod⟩)
    simp [hz]

/-- Literal beta has a fixed bound, independent of the number of bin
primes. Only distinguished prime factors are counted in its divisor fibre. -/
theorem stoppedBeta_distinguished_rough_bound
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (hW : ∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1)
    (R D : Finset Eisenstein) (hR : ∀ r ∈ R, primary r)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z : ℝ} (hw : 1 ≤ w) (hwz : w ≤ z)
    (selected : Eisenstein → Eisenstein → Prop)
    {b : Eisenstein} (hb : primary b) (hs : Squarefree b) {k : ℕ}
    (hsize : norm b < w^k) :
    ‖stoppedBeta R D (distinguishedTupleCoefficient S W ψ w z) ψ w selected b‖ ≤
      (2^k:ℕ)*(‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
        ((Fintype.card ι)^(Fintype.card ι):ℕ)) := by
  rw [←stoppedBeta_filter_nonzero]
  apply stoppedBeta_rough_bound _ D
    (fun r hr => hR r (Finset.mem_filter.mp hr).1) hψ w hw
  · intro r hr p hp
    have hpr := primaryPrimeFactor_spec (hR r (Finset.mem_filter.mp hr).1) hp
    exact (distinguishedTupleCoefficient_prime_support S hS W hψone hψzero
      (zero_lt_one.trans_le hw) hwz (Finset.mem_filter.mp hr).2 hpr.1 hpr.2).1.le
  · positivity
  · intro r _
    exact distinguishedTupleCoefficient_norm S hS W hW hψ w z r
  · exact hb
  · exact hs
  · exact hsize

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_DistinguishedUniform
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform bounds for the literal stopped distinguished coefficient on
the fixed X-envelope. The bin boundary parameter does not enter them. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedBeta_distinguished_uniform {ξ C : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hC : 0 < C)
    {ψ : ℝ → ℝ} (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1)
    (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (S : ι → Finset Eisenstein) (W : ι → Eisenstein → ℂ)
        (R D : Finset Eisenstein) (selected : Eisenstein → Eisenstein → Prop),
      (∀ i, ∀ p ∈ S i, primaryPrime p) →
      (∀ i, ∀ p ∈ S i, ‖W i p‖ ≤ 1) → (∀ r ∈ R, primary r) →
      ∀ b : Eisenstein, primary b → Squarefree b → norm b ≤ C*X →
        ‖stoppedBeta R D (distinguishedTupleCoefficient S W ψ (X^ξ) (X^(2/5:ℝ)))
          ψ (X^ξ) selected b‖ ≤ K := by
  obtain ⟨k,hk⟩ := exists_nat_gt (1/ξ)
  have hk' : 1 < ξ*(k:ℝ) := by
    have hh := (div_lt_iff₀ hξ).mp hk
    nlinarith
  let M : ℝ := ‖((Fintype.card ι).factorial:ℂ)⁻¹‖ *
    ((Fintype.card ι)^(Fintype.card ι):ℕ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨(2^k:ℕ)*(M+1),by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_prime_tuple_norm_bound hC hk']
    with X hX hnorm
  intro S W R D selected hS hW hR b hb hs hbX
  apply (stoppedBeta_distinguished_rough_bound S hS W hW R D hR hψ hψone hψzero
    (Real.one_le_rpow hX.le hξ.le) (Real.rpow_le_rpow_of_exponent_le hX.le hξz)
    selected hb hs (hbX.trans_lt hnorm)).trans
  change (2^k:ℕ)*M ≤ (2^k:ℕ)*(M+1)
  exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeBinGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform norm distortion for the multiplicative bin surrogate.
The bin ratio is fixed before the norm parameter; all selected subsets
simultaneously satisfy the manuscript's small-power distortion bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_norm_ge_two {p : Eisenstein} (hp : primaryPrime p) : 2 ≤ norm p := by
  have hz := normNat_ne_zero hp.2.ne_zero
  have ho : normNat p ≠ 1 := by
    intro h
    apply hp.2.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [←normNat_cast,h]
    norm_num
  have h : 2 ≤ normNat p := by omega
  rw [←normNat_cast]
  exact_mod_cast h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GeometricPrimeBins
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete descending geometric binning of the actual prime norms.
The number of bins is logarithmic and all lower endpoints exceed one,
so the exact first-crossing construction applies without empty-bin cases. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma geometricPrimeBin_cell {ρ B : ℝ} (hρ : 1 < ρ) (_hρ₂ : ρ ≤ 2)
    {p : Eisenstein} (hp : primaryPrime p) (hpB : norm p ≤ B) :
    geometricBinLower ρ B (geometricPrimeBin ρ B p) ≤ norm p ∧
      norm p < ρ*geometricBinLower ρ B (geometricPrimeBin ρ B p) := by
  have hr := Real.log_pos hρ
  have hpn : 0 < norm p := by linarith [primaryPrime_norm_ge_two hp]
  have hl : 0 ≤ Real.log (norm p)/Real.log ρ :=
    div_nonneg (Real.log_nonneg (by linarith [primaryPrime_norm_ge_two hp])) hr.le
  have hkM : ⌊Real.log (norm p)/Real.log ρ⌋₊ ≤ geometricBinCount ρ B := by
    exact (Nat.floor_mono (div_le_div_of_nonneg_right
      (Real.log_le_log hpn hpB) hr.le)).trans (Nat.floor_le_ceil _)
  have hidx : geometricBinCount ρ B - geometricPrimeBin ρ B p =
      ⌊Real.log (norm p)/Real.log ρ⌋₊ := by
    unfold geometricPrimeBin
    omega
  change ρ^(geometricBinCount ρ B-geometricPrimeBin ρ B p) ≤ norm p ∧
    norm p < ρ*ρ^(geometricBinCount ρ B-geometricPrimeBin ρ B p)
  rw [hidx]
  constructor
  · apply (Real.pow_le_iff_le_log (zero_lt_one.trans hρ) hpn).mpr
    exact (le_div_iff₀ hr).mp (Nat.floor_le hl)
  · rw [←pow_succ',Real.lt_pow_iff_log_lt hpn (zero_lt_one.trans hρ)]
    have h := (div_lt_iff₀ hr).mp (Nat.lt_floor_add_one (Real.log (norm p)/Real.log ρ))
    simpa only [Nat.cast_add,Nat.cast_one] using h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted finite-sum forms of the exact largest-prime decomposition,
ready for the actual norm twist and cubic character. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPairSupport_primary (R D : Finset Eisenstein)
    (hR : ∀ r ∈ R, primary r) (hD : ∀ d ∈ D, primary d)
    {n : Eisenstein} (hn : n ∈ primaryPairSupport R D) : primary n := by
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hr,hd⟩ := Finset.mem_product.mp ht
  exact primary_mul (hR _ hr) (hD _ hd)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The uniform exponent saving applied to the actual finite frequency mass. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma primary_support_card_le (S : Finset Eisenstein) {U : ℝ} (hU : 0 ≤ U)
    (hS : ∀ s ∈ S, primary s ∧ norm s ≤ U) : (S.card:ℝ) ≤ 18*U := by
  have hsub : S ⊆ nonzeroNormBall U := fun s hs =>
    mem_nonzeroNormBall.mpr ⟨(hS s hs).2,primary_ne_zero (hS s hs).1⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hU)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCharacterRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal stopped character sum as a squarefree coefficient row.
The norm phase preserves its energy, and the energy is derived from the
actual distinguished coefficient rather than supplied as a hypothesis. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedIntervalSupport_spec (X a b : ℝ) (e : Eisenstein)
    {n : Eisenstein} (hn : n ∈ stoppedIntervalSupport ι X a b e) :
    primary n ∧ Squarefree n ∧ norm n ≤ b := by
  obtain ⟨hm,hs,_,_,hb⟩ := Finset.mem_filter.mp hn
  have hp := primaryPairSupport_primary _ _
    (fun r hr => orderedPrimarySupport_primary _
      (fun _ _ h => (mem_primeCutoff.mp h).1.1) hr)
    (fun d hd => (mem_primaryElementBall.mp hd).1) hm
  exact ⟨hp,hs,hb⟩

theorem stoppedCharacterSum_row (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein) :
    stoppedCharacterSum X w z a b u W selected v e =
      ∑ n ∈ stoppedIntervalSupport ι X a b e,
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v := by
  unfold stoppedCharacterSum stoppedIntervalSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold stoppedRowCoefficient
  split_ifs <;> ring

theorem stopped_interval_energy {ξ : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (u a b : ℝ) (e : Eisenstein),
      0 ≤ b → b ≤ X →
      (∀ n ∈ stoppedIntervalSupport ι X a b e,
        ‖stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n‖ ≤ M) ∧
      (∑ n ∈ stoppedIntervalSupport ι X a b e,
        ‖stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n‖^2) ≤ 18*b*M^2 := by
  obtain ⟨M,hM,hbound⟩ := stoppedBeta_distinguished_uniform (ι := ι) hξ hξz
    (C := 1) (by norm_num)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
    (fun _ _ hx => primeDetectorCutoff_one hx)
    (fun _ hx => primeDetectorCutoff_zero hx)
  refine ⟨M,hM,?_⟩
  filter_upwards [hbound] with X hbound
  intro W hW selected u a b e hb hbX
  have hrow (n : Eisenstein) (hn : n ∈ stoppedIntervalSupport ι X a b e) :
      ‖stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n‖ ≤ M := by
    obtain ⟨hnp,hns,hnB⟩ := stoppedIntervalSupport_spec X a b e hn
    unfold stoppedRowCoefficient
    rw [norm_mul,norm_normTwist,mul_one]
    apply hbound (fun _ : ι => primeCutoff X) (fun i p => W i (norm p))
      (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X)
      selected (fun _ _ hp => (mem_primeCutoff.mp hp).1) (fun i p _ => hW i (norm p))
      (fun r hr => orderedPrimarySupport_primary _
        (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr) n hnp hns
    simpa only [one_mul] using hnB.trans hbX
  refine ⟨hrow,?_⟩
  have hcard := primary_support_card_le (stoppedIntervalSupport ι X a b e) hb
    (fun n hn => ⟨(stoppedIntervalSupport_spec X a b e hn).1,
      (stoppedIntervalSupport_spec X a b e hn).2.2⟩)
  calc
    _ ≤ ∑ _n ∈ stoppedIntervalSupport ι X a b e, M^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hrow n hn) 2
    _ = ((stoppedIntervalSupport ι X a b e).card:ℝ)*M^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg M)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete finite low-conductor frequency support: a small
nonzero core times a bounded cube, with precisely the cubes removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mem_lowNoncubeSupport {V J : ℝ} {h : Eisenstein} (hh : h ∈ lowNoncubeSupport V J) :
    (¬∃ a : Eisenstein, a^3 = h) ∧ ∃ v j : Eisenstein,
      v ≠ 0 ∧ j ≠ 0 ∧ norm v ≤ V ∧ norm j ≤ J ∧ h = v*j^3 := by
  obtain ⟨hi,hn⟩ := Finset.mem_filter.mp hh
  obtain ⟨⟨v,j⟩,hm,he⟩ := Finset.mem_image.mp hi
  have hv := mem_nonzeroNormBall.mp (Finset.mem_product.mp hm).1
  have hj := mem_nonzeroNormBall.mp (Finset.mem_product.mp hm).2
  exact ⟨hn,v,j,hv.2,hj.2,hv.1,hj.1,he.symm⟩

lemma lowNoncubeSupport_card {V J : ℝ} (hV : 0 ≤ V) (hJ : 0 ≤ J) :
    ((lowNoncubeSupport V J).card:ℝ) ≤ 324*V*J := by
  have hc : (lowNoncubeSupport V J).card ≤
      ((nonzeroNormBall V).product (nonzeroNormBall J)).card :=
    (Finset.card_filter_le _ _).trans (Finset.card_image_le)
  have hb : (((nonzeroNormBall V).product (nonzeroNormBall J)).card:ℝ) =
      ((nonzeroNormBall V).card:ℝ)*((nonzeroNormBall J).card:ℝ) := by
    exact_mod_cast Finset.card_product (nonzeroNormBall V) (nonzeroNormBall J)
  calc
    _ ≤ (((nonzeroNormBall V).product (nonzeroNormBall J)).card:ℝ) := Nat.cast_le.mpr hc
    _ = _ := hb
    _ ≤ (18*V)*(18*J) := mul_le_mul (nonzeroNormBall_card_le hV) (nonzeroNormBall_card_le hJ)
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicCoreCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coverage of a noncube frequency by either the low-core set or
a ramified/squarefree pair of large conductor. No decomposition is assumed. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_cube (j : Eisenstein) : norm (j^3) = norm j^3 := by
  simp only [pow_succ,norm_mul_eq,pow_zero,norm_one_eq]

lemma cube_part_norm_bound {h v j : Eisenstein} {H : ℝ}
    (hv : v ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H) :
    norm j ≤ H^(1/3:ℝ) := by
  have hcube : norm j^3 ≤ H := by
    calc
      _ ≤ norm v*norm j^3 := le_mul_of_one_le_left (pow_nonneg (norm_nonneg j) _) (one_le_norm hv)
      _ = norm h := by rw [heq,norm_mul_eq,norm_cube]
      _ ≤ H := hh
  have hp := Real.rpow_le_rpow (pow_nonneg (norm_nonneg j) 3) hcube (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (norm j^3)^(1/3:ℝ) = norm j := by
    rw [← Real.rpow_natCast (norm j) 3,← Real.rpow_mul (norm_nonneg j)]
    norm_num
  rwa [he] at hp

lemma mem_lowNoncubeSupport_of_core {h v j : Eisenstein} {V H : ℝ}
    (hv : v ≠ 0) (hj : j ≠ 0) (heq : h = v*j^3) (hh : norm h ≤ H)
    (hsmall : norm v ≤ V) (hn : ¬∃ a : Eisenstein, a^3 = h) :
    h ∈ lowNoncubeSupport V (H^(1/3:ℝ)) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(v,j),?_,heq.symm⟩,hn⟩
  exact Finset.mem_product.mpr ⟨mem_nonzeroNormBall.mpr ⟨hsmall,hv⟩,
    mem_nonzeroNormBall.mpr ⟨cube_part_norm_bound hv heq hh,hj⟩⟩

theorem noncube_large_core_decomposition {h : Eisenstein} {V H : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ H) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (H^(1/3:ℝ))) :
    ∃ r s t j : Eisenstein, r ≠ 0 ∧ norm r ≤ 729 ∧
      primary s ∧ primary t ∧ Squarefree s ∧ Squarefree t ∧ IsCoprime s t ∧
      j ≠ 0 ∧ h = r*s*t^2*j^3 ∧
      V/729 < norm s*norm t^2 ∧ norm s*norm t^2 ≤ H ∧ norm j ≤ H^(1/3:ℝ) := by
  obtain ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq⟩ := full_cube_decomposition hh0
  have hv : r*s*t^2 ≠ 0 := mul_ne_zero (mul_ne_zero hr (primary_ne_zero hs))
    (pow_ne_zero _ (primary_ne_zero ht))
  have hcore : h = (r*s*t^2)*j^3 := heq
  have hlarge : V < norm (r*s*t^2) := lt_of_not_ge (fun hsmall => hnot
    (mem_lowNoncubeSupport_of_core hv hj hcore hh hsmall hn))
  have hc : norm (r*s*t^2) = norm r*(norm s*norm t^2) := by
    rw [norm_mul_eq,norm_mul_eq]
    have ht2 : norm (t^2) = norm t^2 := by simp only [pow_two,norm_mul_eq]
    rw [ht2]
    ring
  have hD0 : 0 ≤ norm s*norm t^2 := mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hsmall : norm (r*s*t^2) ≤ norm h := by
    calc
      _ ≤ norm (r*s*t^2)*norm (j^3) :=
        le_mul_of_one_le_right (norm_nonneg _) (one_le_norm (pow_ne_zero _ hj))
      _ = norm h := by simp only [hcore,norm_mul_eq]
  refine ⟨r,s,t,j,hr,hrN,hs,ht,hss,hst,hcop,hj,heq,?_,?_,cube_part_norm_bound hv hcore hh⟩
  · apply (div_lt_iff₀ (by norm_num : (0:ℝ) < 729)).mpr
    rw [hc] at hlarge
    nlinarith [mul_le_mul_of_nonneg_right hrN hD0]
  · apply le_trans _ (hsmall.trans hh)
    rw [hc]
    exact le_mul_of_one_le_left hD0 (one_le_norm hr)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite cover of all noncube frequencies outside the small-core set
by the actual coprime ramified/squarefree blocks used in the moment bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma coreDyadicConductor_pos (i j : ℕ) : 0 < coreDyadicConductor i j := by
  unfold coreDyadicConductor
  positivity

lemma squarefreePrimaryDyad_gramDyad {i : ℕ} {s : Eisenstein}
    (hs : s ∈ squarefreePrimaryDyad i) : gramDyad ((2:ℝ)^i) s := by
  obtain ⟨hf,hp,hq⟩ := mem_squarefreePrimaryDyad.mp hs
  have hlog := (mem_frequencyDyad.mp hf).2
  refine ⟨hp,hq,(frequencyDyad_norm hf).1,?_⟩
  have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) (normNat s)
  rw [hlog] at hlt
  have hcast : norm s < (2:ℝ)^(i+1) := by
    rw [← normNat_cast]
    exact_mod_cast hlt
  simpa only [pow_succ,mul_comm] using hcast

lemma real_cube_scale_bound {x B D : ℝ} (hx : 0 ≤ x) (hD : 0 < D)
    (h : x^3*D ≤ B) : x ≤ (B/D)^(1/3:ℝ) := by
  have hc : x^3 ≤ B/D := (le_div_iff₀ hD).mpr h
  have hp := Real.rpow_le_rpow (pow_nonneg hx 3) hc (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (x^3)^(1/3:ℝ) = x := by
    rw [← Real.rpow_natCast x 3,← Real.rpow_mul hx]
    norm_num
  rwa [he] at hp

theorem noncube_mem_coreDyadicBlock {h : Eisenstein} {V B : ℝ}
    (hh0 : h ≠ 0) (hh : norm h ≤ B) (hn : ¬∃ a : Eisenstein, a^3 = h)
    (hnot : h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) :
    ∃ z ∈ largeCoreDyadicIndices V B, h ∈ coreDyadicBlock B z.1 z.2 := by
  obtain ⟨r,s,t,c,hr,hrN,hs,ht,hss,hst,hcop,hc,heq,hlarge,hcore,hcN⟩ :=
    noncube_large_core_decomposition hh0 hh hn hnot
  let i := Nat.log 2 (normNat s)
  let j := Nat.log 2 (normNat t)
  have hsD : s ∈ squarefreePrimaryDyad i := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero hs,rfl⟩,hs,hss⟩
  have htD : t ∈ squarefreePrimaryDyad j := mem_squarefreePrimaryDyad.mpr
    ⟨mem_frequencyDyad.mpr ⟨primary_ne_zero ht,rfl⟩,ht,hst⟩
  have hsG := squarefreePrimaryDyad_gramDyad hsD
  have htG := squarefreePrimaryDyad_gramDyad htD
  have hDlo : coreDyadicConductor i j ≤ norm s*norm t^2 := by
    exact mul_le_mul hsG.2.2.1 (pow_le_pow_left₀ (by positivity) htG.2.2.1 2)
      (by positivity) (norm_nonneg s)
  have hDhi : norm s*norm t^2 < 8*coreDyadicConductor i j := by
    have ht2 : norm t^2 < (2*(2:ℝ)^j)^2 :=
      (pow_lt_pow_left₀ htG.2.2.2 (norm_nonneg t) (by norm_num : (2:ℕ) ≠ 0))
    calc
      _ < (2*(2:ℝ)^i)*((2*(2:ℝ)^j)^2) := mul_lt_mul hsG.2.2.2 ht2.le
        (sq_pos_of_pos (zero_lt_one.trans_le (one_le_norm (primary_ne_zero ht)))) (by positivity)
      _ = _ := by unfold coreDyadicConductor; ring
  have hDb : coreDyadicConductor i j ≤ B := hDlo.trans hcore
  have hidx : ∀ (a : Eisenstein), primary a → norm a ≤ B →
      Nat.log 2 (normNat a) < Nat.log 2 ⌊B⌋₊+1 := by
    intro a ha haB
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    apply Nat.le_floor
    rwa [normNat_cast]
  have hsB : norm s ≤ B := (le_mul_of_one_le_right (norm_nonneg s)
    (one_le_pow₀ (one_le_norm (primary_ne_zero ht)))).trans hcore
  have htB : norm t ≤ B := by
    have htt : norm t ≤ norm t^2 := by
      nlinarith [one_le_norm (primary_ne_zero ht)]
    exact htt.trans ((le_mul_of_one_le_left (sq_nonneg _) (one_le_norm (primary_ne_zero hs))).trans hcore)
  have hcube : norm c^3*coreDyadicConductor i j ≤ B := by
    have hn : norm h = norm r*(norm s*norm t^2)*norm c^3 := by
      simp only [heq,norm_mul_eq,norm_cube,pow_two]
      ring
    calc
      _ ≤ norm c^3*(norm s*norm t^2) := mul_le_mul_of_nonneg_left hDlo (pow_nonneg (norm_nonneg c) _)
      _ ≤ norm r*(norm s*norm t^2)*norm c^3 := by
        nlinarith [mul_le_mul_of_nonneg_right
          (one_le_norm hr) (mul_nonneg (mul_nonneg (norm_nonneg s) (sq_nonneg (norm t)))
            (pow_nonneg (norm_nonneg c) 3))]
      _ = norm h := hn.symm
      _ ≤ B := hh
  refine ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (hidx s hs hsB),Finset.mem_range.mpr (hidx t ht htB)⟩,
    ⟨by dsimp only; linarith,hDb⟩⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨((r,c),(s,t)),Finset.mem_product.mpr ⟨Finset.mem_product.mpr
    ⟨mem_nonzeroNormBall.mpr ⟨hrN,hr⟩,mem_nonzeroNormBall.mpr
      ⟨real_cube_scale_bound (norm_nonneg c) (coreDyadicConductor_pos i j) hcube,hc⟩⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsD,htD⟩,hcop⟩⟩,heq.symm⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicFrequencyMassSplit
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete small-core / dyadic-core partition of a finite noncube
mass. Multiple arithmetic decompositions cost no frequency multiplicity. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem noncube_frequency_mass_split (H : Finset Eisenstein) {V B : ℝ}
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h)
    (f : Eisenstein → ℝ) (hf : ∀ h, 0 ≤ f h) :
    (∑ h ∈ H, f h) ≤
      (∑ h ∈ H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))), f h)+
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
  let I := (largeCoreDyadicIndices V B).sigma (fun z => coreDyadicBlock B z.1 z.2)
  let F : Sigma (fun _ : ℕ × ℕ => Eisenstein) → Eisenstein := Sigma.snd
  have hcover : H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))) ⊆ I.image F := by
    intro h hh
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hh
    obtain ⟨z,hz,hb⟩ := noncube_mem_coreDyadicBlock (hH h hm).1
      (hH h hm).2.1 (hH h hm).2.2 hn
    exact Finset.mem_image.mpr ⟨⟨z,h⟩,Finset.mem_sigma.mpr ⟨hz,hb⟩,rfl⟩
  have hsum : (∑ h ∈ H.filter (fun h => h ∉ lowNoncubeSupport V (B^(1/3:ℝ))), f h) ≤
      ∑ z ∈ largeCoreDyadicIndices V B, ∑ h ∈ coreDyadicBlock B z.1 z.2, f h := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hcover (fun h _ _ => hf h)).trans
    apply (Finset.sum_image_le_of_nonneg (s := I) (g := F) (f := f) (fun h _ => hf h)).trans_eq
    exact Finset.sum_sigma _ _ _
  rw [← Finset.sum_filter_add_sum_filter_not H
    (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ))) f]
  exact add_le_add le_rfl hsum

lemma largeCoreDyadicIndices_card (V B : ℝ) :
    (largeCoreDyadicIndices V B).card ≤ (Nat.log 2 ⌊B⌋₊+1)^2 := by
  unfold largeCoreDyadicIndices
  apply (Finset.card_filter_le _ _).trans
  exact le_of_eq ((Finset.card_product _ _).trans (by simp only [Finset.card_range,pow_two]))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Transform_MetaplecticRetainedPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit absorption of the retained norm-dyad count and arbitrarily
small arithmetic losses in a fixed polynomial scale range. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_dyad_count_log_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ) ≤ C*(1+Real.log J) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let C := 1+Real.log 3/Real.log 2+1/Real.log 2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J hJ
  have hJp : 0 < J := zero_lt_one.trans_le hJ
  have hfloor : (1:ℕ) ≤ ⌊3*J⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    norm_num
    linarith
  have hfloorpos : (0:ℝ) < (⌊3*J⌋₊:ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hfloor)
  have hlog := Real.log_le_log hfloorpos (Nat.floor_le (by positivity : 0 ≤ 3*J))
  have hn := Real.natLog_le_logb ⌊3*J⌋₊ 2
  simp only [Real.logb,Nat.cast_ofNat] at hn
  have hjlog := Real.log_nonneg hJ
  have hh : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ) ≤
      (Real.log 3+Real.log J)/Real.log 2 := by
    apply hn.trans
    apply (div_le_div_iff_of_pos_right h2).mpr
    simpa only [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) hJp.ne'] using hlog
  rw [Nat.cast_add,Nat.cast_one]
  have hhp : ((Nat.log 2 ⌊3*J⌋₊:ℕ):ℝ)+1 ≤
      (Real.log 3+Real.log J)/Real.log 2+1 := by linarith only [hh]
  apply hhp.trans
  dsimp [C]
  have hx := mul_nonneg (show 0 ≤ 1+Real.log 3/Real.log 2 by positivity) hjlog
  simp only [div_eq_mul_inv] at *
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoreIndexLogCount
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The concrete two-dimensional core partition costs only two powers
of the logarithm, uniformly throughout the required frequency range. -/
noncomputable section
namespace CubicFirstMoment

theorem core_dyadic_index_log_count :
    ∃ C : ℝ, 0 < C ∧ ∀ (V B L : ℝ), 1 ≤ B → 1 ≤ L → B ≤ L^2 →
      ((largeCoreDyadicIndices V B).card:ℝ) ≤ C*(1+Real.log L)^2 := by
  obtain ⟨C,hC,hcount⟩ := metaplectic_dyad_count_log_bound
  refine ⟨4*C^2,by positivity,?_⟩
  intro V B L hB hL hBL
  have hmono : Nat.log 2 ⌊B⌋₊+1 ≤ Nat.log 2 ⌊3*B⌋₊+1 :=
    Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono (by linarith))) 1
  have hn : ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ) ≤ C*(1+Real.log B) :=
    (Nat.cast_le.mpr hmono).trans (hcount B hB)
  have hlog : Real.log B ≤ 2*Real.log L := by
    have h := Real.log_le_log (zero_lt_one.trans_le hB) hBL
    rw [← Real.rpow_natCast L 2,Real.log_rpow (zero_lt_one.trans_le hL)] at h
    norm_num only [Nat.cast_ofNat] at h
    exact h
  have hn' : ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ) ≤ 2*C*(1+Real.log L) :=
    hn.trans (by nlinarith)
  calc
    _ ≤ ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ)^2 := by
      exact_mod_cast largeCoreDyadicIndices_card V B
    _ ≤ (2*C*(1+Real.log L))^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hn' 2
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeCutoffMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full finite noncube cutoff, with all arithmetic decompositions,
small conductors and exceptional conductor regions included. -/
noncomputable section
open scoped BigOperators
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma cube_cutoff_le_length {B L : ℝ} (hB : 0 ≤ B) (hL : 1 ≤ L) (hBL : B ≤ L^2) :
    B^(1/3:ℝ) ≤ L := by
  have hcube : B ≤ L^3 := hBL.trans (pow_le_pow_right₀ hL (by norm_num))
  have hr := Real.rpow_le_rpow hB hcube (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (L^3)^(1/3:ℝ) = L := by
    rw [← Real.rpow_natCast L 3,← Real.rpow_mul (zero_le_one.trans hL)]
    norm_num
  rwa [he] at hr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoreBlocks
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise noncube mass for the actual stopped coefficient. The small
core uses its proved prime cancellation and every other core uses the
ordinary/cubic sieve with the literal squarefree coefficient row. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_noncube_core_blocks
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (a k : ℕ) (ha : 0 < a) :
    ∃ K₀ K₁ : ℝ, 0 < K₀ ∧ 0 < K₁ ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X → 65536 ≤ b →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ X^2 → 8*B ≤ b^(3/4:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool),
      (∑ v ∈ S, ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤
        K₀*B^(1/3:ℝ)*b^2/(Real.log X)^k+
        K₁*((largeCoreDyadicIndices ((Real.log X)^a) B).card:ℝ)*B^(1/3:ℝ)*
          (b*(((Real.log X)^a)/5832)^(-(1/4:ℝ))+b^(1-1/20000:ℝ))*b := by
  obtain ⟨K₀,hK₀,hlow⟩ := stopped_low_core_mass (ι := ι) (d := 1)
    hpnt hSW hξ hξz hκ hH hF hJ a k ha
  obtain ⟨M,hM,henergy⟩ := stopped_interval_energy (ι := ι) hξ hξz
  obtain ⟨K,hK,hcore⟩ := smallB_core_hybrid_sieve hHuxley
  refine ⟨K₀,18*K*M^2,hK₀,by positivity,?_⟩
  filter_upwards [hlow,henergy,eventually_ge_atTop (Real.exp 1)]
    with X hlow henergy hX
  intro δ l b u V B hδ hδone hwidth hl hb hbX hbmin hV hu hVF
    hB hBX hsize W hW hWi hWd S hS e he hNe j₀ k₀ h Z Q early
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let U := (Real.log X)^a
  let I := largeCoreDyadicIndices U B
  let T := stoppedIntervalSupport ι X l b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected
  let f := fun v => ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W selected v e‖^2
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hlog : 0 < Real.log X := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1)
    (by simpa using Real.log_le_log (Real.exp_pos 1) hX)
  have hbpos : 0 < b := by linarith
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hU : 0 < U := pow_pos hlog a
  have hroot : B^(1/3:ℝ) ≤ X^(1:ℝ) := by
    simpa using cube_cutoff_le_length hB0 hX1 hBX
  have hsmall : (∑ v ∈ S.filter (fun v => v ∈ lowNoncubeSupport U (B^(1/3:ℝ))), f v) ≤
      K₀*B^(1/3:ℝ)*b^2/(Real.log X)^k := by
    exact hlow δ l b u V (B^(1/3:ℝ)) hδ hδone hwidth hl hb hbX hV hu hVF
      (Real.rpow_nonneg hB0 _) hroot W hW hWi hWd _
      (fun v hv => (Finset.mem_filter.mp hv).2) e he hNe j₀ k₀ h Z Q early
  have henergy' : (∑ n ∈ T, ‖β n‖^2) ≤ 18*b*M^2 :=
    (henergy W hW selected u l b e hbpos.le hbX).2
  have hrow (z : ℕ × ℕ) (hz : z ∈ I) :
      (∑ v ∈ coreDyadicBlock B z.1 z.2, f v) ≤
        (18*K*M^2)*B^(1/3:ℝ)*(b*(U/5832)^(-(1/4:ℝ))+b^(1-1/20000:ℝ))*b := by
    have hz' := (Finset.mem_filter.mp hz).2
    have hm := hcore T (coreDyadicBlock B z.1 z.2) β b B U z.1 z.2
      hbmin hB0 hU (fun n hn => stoppedIntervalSupport_spec X l b e hn) hz'.1.le
      ((mul_le_mul_of_nonneg_left hz'.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
      (Finset.Subset.refl _)
    have heq (v : Eisenstein) : (∑ n ∈ T, β n*cubicSymbol n v) =
        stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W selected v e :=
      (stoppedCharacterSum_row X (X^ξ) (X^(2/5:ℝ)) l b u W selected v e).symm
    simp_rw [heq] at hm
    apply hm.trans
    have hnonneg : 0 ≤ K*B^(1/3:ℝ)*(b*(U/5832)^(-(1/4:ℝ))+b^(1-1/20000:ℝ)) := by
      positivity
    exact (mul_le_mul_of_nonneg_left henergy' hnonneg).trans_eq (by ring)
  have hlarge : (∑ z ∈ I, ∑ v ∈ coreDyadicBlock B z.1 z.2, f v) ≤
      (18*K*M^2)*(I.card:ℝ)*B^(1/3:ℝ)*
        (b*(U/5832)^(-(1/4:ℝ))+b^(1-1/20000:ℝ))*b := by
    apply (Finset.sum_le_sum hrow).trans_eq
    rw [Finset.sum_const,nsmul_eq_mul]
    ring
  exact (noncube_frequency_mass_split S hS f (fun _ => sq_nonneg _)).trans
    (add_le_add hsmall hlarge)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowHeightLogScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit logarithmic choices for the low-height noncube moment. -/
noncomputable section
namespace CubicFirstMoment

lemma rpow_log_saving {N L H p s : ℝ} (hN : 0 < N) (hL : 0 < L)
    (k d : ℕ) (hlog : N^(-s)*L^(k+d) ≤ H) :
    N^(p-s)*L^d ≤ H*N^p/L^k := by
  apply (le_div_iff₀ (pow_pos hL k)).mpr
  rw [sub_eq_add_neg,Real.rpow_add hN]
  rw [pow_add] at hlog
  have hp := mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hN.le p)
  nlinarith only [hp]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedCoreScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar logarithmic absorption for the pointwise stopped-core sieve.
The power saving is measured at the coefficient length; its comparison
with the outer length is retained explicitly. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_core_cutoff {L : ℝ} (hL : 0 < L) (k : ℕ) :
    ((L^(4*(k+2)))/5832)^(-(1/4:ℝ)) = (5832:ℝ)^(1/4:ℝ)/L^(k+2) := by
  rw [Real.div_rpow (pow_nonneg hL.le _) (by norm_num : (0:ℝ) ≤ 5832),
    ←Real.rpow_natCast L (4*(k+2)),←Real.rpow_mul hL.le]
  have he : ((4*(k+2):ℕ):ℝ)*(-(1/4:ℝ)) = -((k+2:ℕ):ℝ) := by push_cast; ring
  rw [he,Real.rpow_neg hL.le,Real.rpow_natCast,
    Real.rpow_neg (by norm_num : (0:ℝ) ≤ 5832)]
  field_simp

lemma stopped_large_core_scale {N L I C H : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hC : 0 ≤ C)
    (k : ℕ) (hcount : I ≤ C*L^2)
    (hpower : N^(-(1/20000:ℝ))*L^(k+2) ≤ H) :
    I*(N*((L^(4*(k+2)))/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*N ≤
      C*((5832:ℝ)^(1/4:ℝ)+H)*N^2/L^k := by
  have hmid : I*(N*((L^(4*(k+2)))/5832)^(-(1/4:ℝ)))*N ≤
      C*(5832:ℝ)^(1/4:ℝ)*N^2/L^k := by
    rw [stopped_core_cutoff hL k]
    calc
      _ ≤ (C*L^2)*(N*((5832:ℝ)^(1/4:ℝ)/L^(k+2)))*N := by gcongr
      _ = _ := by rw [pow_add]; field_simp
  have hp : N^(2-1/20000:ℝ)*L^2 ≤ H*N^2/L^k := by
    simpa only [Real.rpow_two,Nat.add_comm k 2] using
      (rpow_log_saving hN hL k 2 (p := 2) (s := 1/20000) hpower)
  have hmul : N^(1-1/20000:ℝ)*N = N^(2-1/20000:ℝ) := by
    nth_rw 2 [←Real.rpow_one N]
    rw [←Real.rpow_add hN]
    norm_num
  have hlarge : I*N^(1-1/20000:ℝ)*N ≤ C*H*N^2/L^k := by
    calc
      _ ≤ (C*L^2)*N^(1-1/20000:ℝ)*N := by gcongr
      _ = C*(N^(2-1/20000:ℝ)*L^2) := by rw [←hmul]; ring
      _ ≤ C*(H*N^2/L^k) := mul_le_mul_of_nonneg_left hp hC
      _ = _ := by ring
  calc
    _ = I*(N*((L^(4*(k+2)))/5832)^(-(1/4:ℝ)))*N+I*N^(1-1/20000:ℝ)*N := by ring
    _ ≤ C*(5832:ℝ)^(1/4:ℝ)*N^2/L^k+C*H*N^2/L^k := add_le_add hmid hlarge
    _ = _ := by ring

lemma stopped_length_log_power {X N κ : ℝ}
    (hX : 1 ≤ X) (hN : X^κ ≤ N) (k : ℕ) :
    N^(-(1/20000:ℝ))*(Real.log X)^(k+2) ≤
      X^(-(κ/20000))*(1+Real.log X)^(k+2) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hp := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp κ) hN
    (by norm_num : -(1/20000:ℝ) ≤ 0)
  rw [←Real.rpow_mul hXp.le] at hp
  have he : κ*(-(1/20000:ℝ)) = -(κ/20000) := by ring
  rw [he] at hp
  exact mul_le_mul hp
    (pow_le_pow_left₀ (Real.log_nonneg hX) (by linarith) _)
    (pow_nonneg (Real.log_nonneg hX) _) (Real.rpow_nonneg hXp.le _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorGeometry
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed divisor cutoff preserves the hybrid sieve range when the
frequency length is at most the three-fifths power of the coefficient length. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma stopped_divisor_cutoff_geometry {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ b B : ℝ, X^κ ≤ b → B ≤ b^(3/5:ℝ) →
      1 ≤ b ∧ 65536 ≤ b/b^(1/8:ℝ) ∧
        8*B ≤ (b/b^(1/8:ℝ))^(3/4:ℝ) := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0 < κ*(7/8) by positivity)).eventually_ge_atTop 65536,
    (tendsto_rpow_atTop (show 0 < κ*(9/160) by positivity)).eventually_ge_atTop 8]
    with X hX hsize hgap
  intro b B hb hB
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hb1 : 1 ≤ b := (Real.one_le_rpow hX hκ.le).trans hb
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hquot : b/b^(1/8:ℝ) = b^(7/8:ℝ) := by
    rw [div_eq_mul_inv,←Real.rpow_neg hbp.le]
    nth_rw 1 [←Real.rpow_one b]
    rw [←Real.rpow_add hbp]
    norm_num
  have hsize' : 65536 ≤ b^(7/8:ℝ) := by
    apply hsize.trans
    rw [Real.rpow_mul hXp.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hb (by norm_num)
  have hgap' : 8 ≤ b^(9/160:ℝ) := by
    apply hgap.trans
    rw [Real.rpow_mul hXp.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hb (by norm_num)
  refine ⟨hb1,by rwa [hquot],?_⟩
  calc
    8*B ≤ 8*b^(3/5:ℝ) := mul_le_mul_of_nonneg_left hB (by norm_num)
    _ ≤ b^(9/160:ℝ)*b^(3/5:ℝ) :=
      mul_le_mul_of_nonneg_right hgap' (Real.rpow_nonneg hbp.le _)
    _ = (b/b^(1/8:ℝ))^(3/4:ℝ) := by
      rw [hquot,←Real.rpow_add hbp,←Real.rpow_mul hbp.le]
      norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorLogScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Logarithmic choices for the two nonempty-divisor error terms. -/
noncomputable section
namespace CubicFirstMoment

lemma rough_cutoff_log_saving {L R : ℝ} (hL : 0 < L) (v k : ℕ)
    (hR : 2*L^(2*(v+k)) ≤ R) :
    L^v*(R/2)^(-(1/2:ℝ)) ≤ 1/L^k := by
  have hlower : L^(2*(v+k)) ≤ R/2 := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos (pow_pos hL _) hlower
    (show -(1/2:ℝ) ≤ 0 by norm_num)
  apply (mul_le_mul_of_nonneg_left hp (pow_nonneg hL.le _)).trans_eq
  rw [←Real.rpow_natCast L (2*(v+k)),←Real.rpow_mul hL.le]
  have he : ((2*(v+k):ℕ):ℝ)*(-(1/2:ℝ)) = -((v+k:ℕ):ℝ) := by
    push_cast
    ring
  rw [he,Real.rpow_neg hL.le,Real.rpow_natCast,pow_add]
  field_simp

lemma stopped_hybrid_weighted_scale {b L I C H C₁ C₂ C₃ : ℝ}
    (hb : 0 < b) (hL : 0 < L) (hC : 0 ≤ C) (k : ℕ)
    (hI : 0 ≤ I) (hcount : I ≤ C*L^2)
    (hpower : b^(-(1/20000:ℝ))*L^(k+2) ≤ H)
    (hC₁ : C₁ ≤ C₃) (hC₂ : C₂ ≤ C₃) (hC₃ : 0 ≤ C₃) :
    I*(b^2*((L^(4*(k+2)))/5832)^(-(1/4:ℝ))*C₁+
      b^(2-1/20000:ℝ)*C₂) ≤
    C₃*C*((5832:ℝ)^(1/4:ℝ)+H)*b^2/L^k := by
  have hp := stopped_large_core_scale hb hL hC k hcount hpower
  have he : b^(1-1/20000:ℝ)*b = b^(2-1/20000:ℝ) := by
    nth_rw 2 [←Real.rpow_one b]
    rw [←Real.rpow_add hb]
    congr 1
    ring
  calc
    _ ≤ I*(b^2*((L^(4*(k+2)))/5832)^(-(1/4:ℝ))*C₃+
        b^(2-1/20000:ℝ)*C₃) := by gcongr
    _ = C₃*(I*(b*((L^(4*(k+2)))/5832)^(-(1/4:ℝ))+
        b^(1-1/20000:ℝ))*b) := by rw [←he]; ring
    _ ≤ C₃*(C*((5832:ℝ)^(1/4:ℝ)+H)*b^2/L^k) :=
      mul_le_mul_of_nonneg_left hp hC₃
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact shortening for a divisor-restricted stopped row. The shortened
coefficient remains the original coefficient evaluated at d*n; no new
prime-factor independence is asserted. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedDivisorSlice_spec (X l b : ℝ) (e d : Eisenstein)
    {n : Eisenstein} (hn : n ∈ stoppedDivisorSlice ι X l b e d) :
    primary n ∧ Squarefree n ∧ norm n ≤ b/norm d := by
  obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hn
  have hs := (stoppedIntervalSupport_spec X l b e hp).2.1
  exact ⟨(mem_primaryElementBall.mp hm).1,
    hs.squarefree_of_dvd (dvd_mul_left _ _),(mem_primaryElementBall.mp hm).2⟩

lemma stoppedDivisorSlice_complete (X l b : ℝ) (e : Eisenstein)
    {d : Eisenstein} (hd : primary d) (n : Eisenstein)
    (hn : d*n ∈ stoppedIntervalSupport ι X l b e) :
    n ∈ stoppedDivisorSlice ι X l b e d := by
  have hp := stoppedIntervalSupport_spec X l b e hn
  apply Finset.mem_filter.mpr
  refine ⟨mem_primaryElementBall.mpr ⟨primary_of_mul hd hp.1,?_⟩,hn⟩
  apply (le_div_iff₀ (norm_pos_of_ne_zero (primary_ne_zero hd))).mpr
  simpa only [norm_mul_eq,mul_comm] using hp.2.2

theorem stopped_divisor_sum_eq_slice (X l b : ℝ) (e : Eisenstein)
    {d : Eisenstein} (hd : primary d) (F : Eisenstein → ℂ) :
    (∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n), F n) =
      ∑ n ∈ stoppedDivisorSlice ι X l b e d, F (d*n) := by
  symm
  apply Finset.sum_bij (fun n _ => d*n)
  · intro n hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).2,dvd_mul_right _ _⟩
  · intro n _ m _ hnm
    exact mul_left_cancel₀ (primary_ne_zero hd) hnm
  · intro n hn
    obtain ⟨m,hm⟩ := (Finset.mem_filter.mp hn).2
    refine ⟨m,?_,hm.symm⟩
    apply stoppedDivisorSlice_complete X l b e hd
    simpa only [←hm] using (Finset.mem_filter.mp hn).1
  · intro n _
    rfl

theorem stopped_divisor_character_sum (X w z l b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e v : Eisenstein)
    {d : Eisenstein} (hd : primary d) :
    (∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
      stoppedRowCoefficient X w z u W selected n*cubicSymbol n v) =
      cubicSymbol d v*∑ n ∈ stoppedDivisorSlice ι X l b e d,
        stoppedRowCoefficient X w z u W selected (d*n)*cubicSymbol n v := by
  rw [stopped_divisor_sum_eq_slice X l b e hd,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [cubicSymbol_mul_lower (primary_ne_zero hd)
    (primary_ne_zero (stoppedDivisorSlice_spec X l b e d hn).1)]
  ring

theorem stopped_divisor_character_norm_le (X w z l b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e v : Eisenstein)
    {d : Eisenstein} (hd : primary d) :
    ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
      stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖ ≤
      ‖∑ n ∈ stoppedDivisorSlice ι X l b e d,
        stoppedRowCoefficient X w z u W selected (d*n)*cubicSymbol n v‖ := by
  rw [stopped_divisor_character_sum X w z l b u W selected e v hd,norm_mul]
  exact mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_cubicSymbol_le_one hd v)

theorem stopped_slice_energy (X w z l b u M : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e d : Eisenstein)
    (hb : 0 ≤ b)
    (hcoeff : ∀ n ∈ stoppedIntervalSupport ι X l b e,
      ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) :
    (∑ n ∈ stoppedDivisorSlice ι X l b e d,
      ‖stoppedRowCoefficient X w z u W selected (d*n)‖^2) ≤
        18*(b/norm d)*M^2 := by
  have hc := primary_support_card_le (stoppedDivisorSlice ι X l b e d)
    (div_nonneg hb (norm_nonneg d))
    (fun n hn => ⟨(stoppedDivisorSlice_spec X l b e d hn).1,
      (stoppedDivisorSlice_spec X l b e d hn).2.2⟩)
  calc
    _ ≤ ∑ _n ∈ stoppedDivisorSlice ι X l b e d, M^2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) (hcoeff _ (Finset.mem_filter.mp hn).2) 2
    _ = ((stoppedDivisorSlice ι X l b e d).card:ℝ)*M^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg M)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedRoughSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prime-factor roughness of the actual stopped coefficient. The selected
factor is rough because its bins precede the stopping bin; the distinguished
factor is rough because its coefficient vanishes at small primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma geometricBinLower_antitone {ρ X : ℝ} (hρ : 1 ≤ ρ) :
    Antitone (geometricBinLower ρ X) := by
  intro i j hij
  exact pow_le_pow_right₀ hρ (Nat.sub_le_sub_left hij _)

theorem stoppingSideTest_prime_roughness {ρ X Z : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j k : ℕ} {r d p : Eisenstein} (hd : primary d) (hdX : norm d ≤ X)
    (hs : stoppingSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X) j k Z r d)
    (hp : primaryPrime p) (hpd : p ∣ d) :
    geometricBinLower ρ X j ≤ norm p := by
  have hmem := (primaryPrime_mem_factors_iff hd).mpr ⟨hp,hpd⟩
  have hbin := hs.1 p hmem
  have hpX := (norm_le_of_dvd (primary_ne_zero hd) hpd).trans hdX
  exact (geometricBinLower_antitone hρ.le hbin).trans
    (geometricPrimeBin_cell hρ hρ₂ hp hpX).1

theorem stoppedBeta_prime_roughness
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (R D : Finset Eisenstein)
    {ψ : ℝ → ℝ} (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z ρ X Z Q : ℝ} (hw : 0 < w) (hwz : w ≤ z)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    (j k h : ℕ) (early : Bool) {b p : Eisenstein}
    (hb : stoppedBeta R D (distinguishedTupleCoefficient S W ψ w z) ψ w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) b ≠ 0)
    (hp : primaryPrime p) (hpb : p ∣ b) :
    min w (geometricBinLower ρ X j) ≤ norm p := by
  unfold stoppedBeta primaryPairCoefficient at hb
  obtain ⟨q,hq,hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hb
  obtain ⟨hq,hprod⟩ := Finset.mem_filter.mp hq
  obtain ⟨_hr,hd⟩ := Finset.mem_product.mp hq
  have hsel : stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
      j k h Z Q early q.1 q.2 := by
    by_contra hn
    exact hterm (ite_eq_right hn)
  rw [ite_eq_left hsel] at hterm
  have hv := (mul_ne_zero_iff.mp hterm).1
  have hdiv : p ∣ q.1*q.2 := by rwa [hprod]
  rcases hp.2.dvd_mul.mp hdiv with hpr | hpd
  · exact (min_le_left _ _).trans
      (distinguishedTupleCoefficient_prime_support S hS W hψone hψzero
        hw hwz hv hp hpr).1.le
  · exact (min_le_right _ _).trans
      (stoppingSideTest_prime_roughness hρ hρ₂ (hD q.2 hd).1 (hD q.2 hd).2
        hsel.1 hp hpd)

theorem stoppedBeta_early_prime_roughness
    (S : ι → Finset Eisenstein) (hS : ∀ i, ∀ p ∈ S i, primaryPrime p)
    (W : ι → Eisenstein → ℂ) (R D : Finset Eisenstein)
    {ψ : ℝ → ℝ} (hψone : ∀ x : ℝ, 0 < x → x ≤ 1 → ψ x = 1)
    (hψzero : ∀ x : ℝ, 2 ≤ x → ψ x = 0)
    {w z ρ X Z Q : ℝ} (hw : 0 < w) (hwz : w ≤ z)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hD : ∀ d ∈ D, primary d ∧ norm d ≤ X)
    (j k h : ℕ) (early : Bool) (hj : j ≤ h) {b p : Eisenstein}
    (hb : stoppedBeta R D (distinguishedTupleCoefficient S W ψ w z) ψ w
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) b ≠ 0)
    (hp : primaryPrime p) (hpb : p ∣ b) :
    min w (geometricBinLower ρ X h) ≤ norm p := by
  exact (min_le_min_left w (geometricBinLower_antitone hρ.le hj)).trans
    (stoppedBeta_prime_roughness S hS W R D hψone hψzero hw hwz hρ hρ₂ hD
      j k h early hb hp hpb)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedRoughRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Early stopping makes every nonempty small-divisor row identically
zero. The cutoff is the actual minimum of the distinguished-prime cutoff
and the final permitted stopping-bin endpoint. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma rough_filtered_row_zero (S U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (hne : U.Nonempty)
    (F : Eisenstein → ℂ) (R : ℝ)
    (hrough : ∀ n ∈ S, F n ≠ 0 → ∀ p, primaryPrime p → p ∣ n → R ≤ norm p)
    (hsmall : norm (∏ p ∈ U,p) < R) (v : Eisenstein) :
    (∑ n ∈ S.filter (fun n => (∏ p ∈ U,p) ∣ n), F n*cubicSymbol n v) = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  obtain ⟨hn,hd⟩ := Finset.mem_filter.mp hn
  have hF : F n = 0 := by
    by_contra hF
    obtain ⟨p,hp⟩ := hne
    have hpd : p ∣ ∏ p ∈ U,p := Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp
    have hprod : (∏ p ∈ U,p) ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun q hq => (hU q hq).2.ne_zero)
    have hlow := hrough n hn hF p (hU p hp) (hpd.trans hd)
    exact (not_lt_of_ge (hlow.trans (norm_le_of_dvd hprod hpd))) hsmall
  rw [hF,zero_mul]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stoppedRowCoefficient_early_roughness
    (X w z u ρ Z Q : ℝ) (W : ι → ℝ → ℂ)
    (hw : 0 < w) (hwz : w ≤ z) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (j k h : ℕ) (early : Bool) (hj : j ≤ h) {n p : Eisenstein}
    (hn : stoppedRowCoefficient X w z u W
      (stoppedSideTest (geometricPrimeBin ρ X) (geometricBinLower ρ X)
        j k h Z Q early) n ≠ 0)
    (hp : primaryPrime p) (hpn : p ∣ n) :
    min w (geometricBinLower ρ X h) ≤ norm p := by
  have hb := (mul_ne_zero_iff.mp hn).1
  exact stoppedBeta_early_prime_roughness (fun _ : ι => primeCutoff X)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1) (fun i p => W i (norm p))
    (orderedConvolutionSupport (fun _ : ι => primeCutoff X)) (primaryElementBall X)
    (fun _ _ hx => primeDetectorCutoff_one hx)
    (fun _ hx => primeDetectorCutoff_zero hx) hw hwz hρ hρ₂
    (fun _ hd => mem_primaryElementBall.mp hd) j k h early hj hb hp hpn

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorPartition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact divisor partition for a rough stopped coefficient. Every
nonempty row below the roughness cutoff and every row above the original
support length vanishes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_rough_divisor_partition (X w z l b u R D : ℝ)
    (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
    (e : Eisenstein) (U H : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (hR : 2 < R) (hD : 1 ≤ D)
    (hrough : ∀ n ∈ stoppedIntervalSupport ι X l b e,
      stoppedRowCoefficient X w z u W selected n ≠ 0 →
      ∀ p, primaryPrime p → p ∣ n → R ≤ norm p) :
    stoppedDivisorMass X w z l b u W selected e H U =
      (∑ v ∈ H, ‖stoppedCharacterSum X w z l b u W selected v e‖^2)+
      (∑ s ∈ U.powerset.filter (fun s => R/2 < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ D),
        stoppedDivisorRowMass X w z l b u W selected e H s)+
      (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b),
        stoppedDivisorRowMass X w z l b u W selected e H s) := by
  let f := stoppedDivisorRowMass X w z l b u W selected e H
  let E := ∑ v ∈ H, ‖stoppedCharacterSum X w z l b u W selected v e‖^2
  have hempty : f ∅ = E := by
    simp [f,E,stoppedDivisorRowMass,stoppedCharacterSum_row]
  have hsmall (s : Finset Eisenstein) (hs : s ∈ U.powerset) (hne : s ≠ ∅)
      (hn : norm (∏ p ∈ s,p) ≤ R/2) : f s = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    have hh := rough_filtered_row_zero (stoppedIntervalSupport ι X l b e) s
      (fun p hp => hU p (Finset.mem_powerset.mp hs hp))
      (Finset.nonempty_iff_ne_empty.mpr hne)
      (stoppedRowCoefficient X w z u W selected) R hrough
      (show norm (∏ p ∈ s,p) < R by linarith) v
    simp only [hh,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hlarge (s : Finset Eisenstein) (hn : b < norm (∏ p ∈ s,p)) : f s = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    have hh : (∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
        (fun n => (∏ p ∈ s,p) ∣ n),
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v) = 0 := by
      apply Finset.sum_eq_zero
      intro n hm
      have hp := stoppedIntervalSupport_spec X l b e (Finset.mem_filter.mp hm).1
      have hle := (norm_le_of_dvd (primary_ne_zero hp.1)
        (Finset.mem_filter.mp hm).2).trans hp.2.2
      exact False.elim ((not_lt_of_ge hle) hn)
    simp only [hh,norm_zero,zero_pow (by decide : 2 ≠ 0)]
  have hterm (s : Finset Eisenstein) (hs : s ∈ U.powerset) :
      f s = (if s = ∅ then E else 0)+
        (if R/2 < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ D then f s else 0)+
        (if D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b then f s else 0) := by
    by_cases hse : s = ∅
    · subst s
      have hhalf : ¬R/2 < (1:ℝ) := by linarith
      simp [hempty,norm_one_eq,hhalf,not_lt_of_ge hD]
    · by_cases hq : R/2 < norm (∏ p ∈ s,p)
      · by_cases hqd : norm (∏ p ∈ s,p) ≤ D
        · simp [hse,hq,hqd,not_lt_of_ge hqd]
        · by_cases hqb : norm (∏ p ∈ s,p) ≤ b
          · simp [hse,hq,hqd,hqb,lt_of_not_ge hqd]
          · simp [hse,hqd,hqb,hlarge s (lt_of_not_ge hqb)]
      · simp [hse,hq,hsmall s hs hse (le_of_not_gt hq)]
  change (∑ s ∈ U.powerset,f s) = _
  calc
    _ = ∑ s ∈ U.powerset, ((if s = ∅ then E else 0)+
        (if R/2 < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ D then f s else 0)+
        (if D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b then f s else 0)) :=
      Finset.sum_congr rfl hterm
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      simp [Finset.sum_filter,f,E]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NoncubeOuterSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full outer cubic-sieve estimate for finite noncube frequencies,
derived by covering with the actual core dyads and summing their bounds. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma lowNoncubeSupport_zero (J : ℝ) : lowNoncubeSupport 0 J = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro h hh
  obtain ⟨_,v,j,hv,_,hNv,_,_⟩ := mem_lowNoncubeSupport hh
  have hv1 := one_le_norm hv
  linarith

theorem noncube_outer_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ),
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ z : Eisenstein, z^3 = h) →
      ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  have he : 0 < ε/2 := by linarith
  obtain ⟨C,hC,hblock⟩ := outer_core_block_sieve he
  obtain ⟨D,hD,hlog⟩ := natLog_power_bound 2 he
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro S H B N hB hN hS hH β
  have hB0 := zero_le_one.trans hB
  have hN0 := zero_le_one.trans hN
  have hcount : ((largeCoreDyadicIndices 0 B).card:ℝ) ≤ D*B^(ε/2) := by
    calc
      _ ≤ ((Nat.log 2 ⌊B⌋₊+1:ℕ):ℝ)^2 := by
        exact_mod_cast largeCoreDyadicIndices_card 0 B
      _ ≤ D*(⌊B⌋₊:ℝ)^(ε/2) := hlog _ ((Nat.one_le_floor_iff B).mpr hB)
      _ ≤ D*B^(ε/2) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hB0) he.le) hD.le
  have hsplit := noncube_frequency_mass_split (V := 0) H hH
    (fun h => ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) (fun _ => sq_nonneg _)
  simp only [lowNoncubeSupport_zero,Finset.notMem_empty,Finset.filter_false,
    Finset.sum_empty,zero_add] at hsplit
  have hrows (z : ℕ × ℕ) (hz : z ∈ largeCoreDyadicIndices 0 B) :=
    hblock S (coreDyadicBlock B z.1 z.2) B N z.1 z.2 hB0 hN
      (Finset.mem_filter.mp hz).2.2 hS (fun _ h => h) β
  have hE : 0 ≤ ∑ n ∈ S, ‖β n‖^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hp : B^(ε/2)*(2*B*N)^(ε/2) ≤ (2*B*N)^ε := by
    calc
      _ ≤ (2*B*N)^(ε/2)*(2*B*N)^(ε/2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        apply Real.rpow_le_rpow hB0 _ he.le
        nlinarith
      _ = _ := by rw [← Real.rpow_add (by positivity : 0 < 2*B*N)]; congr 1; ring
  calc
    _ ≤ ∑ z ∈ largeCoreDyadicIndices 0 B,
        C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 :=
      hsplit.trans (Finset.sum_le_sum hrows)
    _ = ((largeCoreDyadicIndices 0 B).card:ℝ)*
        (C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2) := by simp
    _ ≤ (D*B^(ε/2))*
        (C*(2*B*N)^(ε/2)*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (C*D)*(B^(ε/2)*(2*B*N)^(ε/2))*
        (B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*∑ n ∈ S, ‖β n‖^2 := by ring
    _ ≤ _ := by gcongr

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_AllFrequencyOuterSieve
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Add the explicit cube frequencies to the proved outer sieve. The
cube count is a lattice count, not an additional analytic hypothesis. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cube_frequency_card_le (H : Finset Eisenstein) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ∃ j : Eisenstein, j^3 = h) :
    (H.card:ℝ) ≤ 18*B^(1/3:ℝ) := by
  have hs : H ⊆ (nonzeroNormBall (B^(1/3:ℝ))).image (fun j => j^3) := by
    intro h hh
    obtain ⟨hne,hn,j,rfl⟩ := hH h hh
    have hj : j ≠ 0 := fun hj => hne (by rw [hj,zero_pow (by decide)])
    have hpow : (norm j)^3 ≤ B := by simpa only [eisenstein_norm_pow] using hn
    have hr := Real.rpow_le_rpow (pow_nonneg (norm_nonneg j) 3) hpow
      (by norm_num : (0:ℝ) ≤ 1/3)
    rw [← Real.rpow_natCast,← Real.rpow_mul (norm_nonneg j)] at hr
    norm_num at hr
    exact Finset.mem_image.mpr ⟨j,mem_nonzeroNormBall.mpr ⟨hr,hj⟩,rfl⟩
  exact (Nat.cast_le.mpr ((Finset.card_le_card hs).trans Finset.card_image_le)).trans
    (nonzeroNormBall_card_le (Real.rpow_nonneg hB _))

lemma cubic_character_row_sq (S : Finset Eisenstein)
    (hS : ∀ n ∈ S, primary n) (β : Eisenstein → ℂ) (h : Eisenstein) :
    ‖∑ n ∈ S, β n*cubicSymbol n h‖^2 ≤ (S.card:ℝ)*∑ n ∈ S, ‖β n‖^2 := by
  have hn : ‖∑ n ∈ S, β n*cubicSymbol n h‖ ≤ ∑ n ∈ S, ‖β n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS n hn) _)
  apply (pow_le_pow_left₀ (_root_.norm_nonneg _) hn 2).trans
  simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] using
    Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun n => ‖β n‖)

theorem all_frequency_outer_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S H : Finset Eisenstein) (B N : ℝ),
      1 ≤ B → 1 ≤ N →
      (∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ N) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) → ∀ β : Eisenstein → ℂ,
      (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤
        C*(2*B*N)^ε*(B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N)*
          ∑ n ∈ S, ‖β n‖^2 := by
  obtain ⟨C,hC,hbound⟩ := noncube_outer_sieve hε
  refine ⟨C+324,by positivity,?_⟩
  intro S H B N hB hN hS hH β
  let Q := H.filter (fun h => ∃ j : Eisenstein, j^3 = h)
  let T := H.filter (fun h => ¬∃ j : Eisenstein, j^3 = h)
  let E := ∑ n ∈ S, ‖β n‖^2
  let P := B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hscale : 1 ≤ (2*B*N)^ε := Real.one_le_rpow (by nlinarith) hε.le
  have hnc := hbound S T B N hB hN hS (fun h hh =>
    ⟨(hH h (Finset.mem_filter.mp hh).1).1,
      (hH h (Finset.mem_filter.mp hh).1).2,(Finset.mem_filter.mp hh).2⟩) β
  have hcube : (∑ h ∈ Q, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) ≤ 324*P*E := by
    have hc := cube_frequency_card_le Q (zero_le_one.trans hB) (fun h hh =>
      ⟨(hH h (Finset.mem_filter.mp hh).1).1,
        (hH h (Finset.mem_filter.mp hh).1).2,(Finset.mem_filter.mp hh).2⟩)
    have hs := primary_support_card_le S (zero_le_one.trans hN)
      (fun n hn => ⟨(hS n hn).1,(hS n hn).2.2⟩)
    calc
      _ ≤ ∑ _h ∈ Q, (S.card:ℝ)*E := Finset.sum_le_sum (fun _ _ =>
        cubic_character_row_sq S (fun n hn => (hS n hn).1) β _)
      _ = (Q.card:ℝ)*((S.card:ℝ)*E) := by simp
      _ ≤ (18*B^(1/3:ℝ))*((18*N)*E) := by gcongr
      _ ≤ 324*P*E := by
        dsimp only [P]
        have hp : B^(1/3:ℝ)*N ≤ B+(B*N)^(2/3:ℝ)+B^(1/3:ℝ)*N := by
          exact le_add_of_nonneg_left (add_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg (by positivity) _))
        nlinarith [mul_le_mul_of_nonneg_right hp hE]
  have heq : (∑ h ∈ H, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) =
      (∑ h ∈ Q, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2) +
      ∑ h ∈ T, ‖∑ n ∈ S, β n*cubicSymbol n h‖^2 := by
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [heq]
  apply (add_le_add hcube hnc).trans
  change 324*P*E+C*(2*B*N)^ε*P*E ≤ (C+324)*(2*B*N)^ε*P*E
  have hh := mul_le_mul_of_nonneg_right hscale (mul_nonneg hP hE)
  nlinarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedFilteredCore
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The nonempty divisor rows use their actual quotient length. Small
cores admit the elementary coefficient bound; larger cores retain the
hybrid ordinary/cubic-sieve saving. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_filtered_outer_sieve {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M B : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e d : Eisenstein), primary d → 0 ≤ b → 1 ≤ B → 1 ≤ b/norm d →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      ∀ H : Finset Eisenstein, (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤
      K*(2*B*(b/norm d))^ε*
        (B+(B*(b/norm d))^(2/3:ℝ)+B^(1/3:ℝ)*(b/norm d))*(b/norm d)*M^2 := by
  obtain ⟨K,hK,hbound⟩ := all_frequency_outer_sieve hε
  refine ⟨18*K,by positivity,?_⟩
  intro X w z l b u M B W selected e d hd hb hB hN hcoeff H hH
  have hm := hbound (stoppedDivisorSlice ι X l b e d) H B (b/norm d) hB hN
    (fun n hn => stoppedDivisorSlice_spec X l b e d hn) hH
    (fun n => stoppedRowCoefficient X w z u W selected (d*n))
  have he := stopped_slice_energy X w z l b u M W selected e d hb hcoeff
  apply (Finset.sum_le_sum (fun v _ => pow_le_pow_left₀ (_root_.norm_nonneg _)
    (stopped_divisor_character_norm_le X w z l b u W selected e v hd) 2)).trans
      (hm.trans _)
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (by ring)

theorem stopped_filtered_core_blocks (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M V B : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e d : Eisenstein), primary d → 0 ≤ b → 0 < V → 0 ≤ B →
      65536 ≤ b/norm d → 8*B ≤ (b/norm d)^(3/4:ℝ) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      ∀ H : Finset Eisenstein,
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤
      104976*V*B^(1/3:ℝ)*(b/norm d)^2*M^2+
      K*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*
        ((b/norm d)*(V/5832)^(-(1/4:ℝ))+(b/norm d)^(1-1/20000:ℝ))*
          (b/norm d)*M^2 := by
  obtain ⟨K,hK,hcore⟩ := smallB_core_hybrid_sieve hHuxley
  refine ⟨18*K,by positivity,?_⟩
  intro X w z l b u M V B W selected e d hd hb hV hB hN hsize hcoeff H hH
  let N := b/norm d
  let S := stoppedDivisorSlice ι X l b e d
  let β := fun n => stoppedRowCoefficient X w z u W selected (d*n)
  let f := fun v => ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => d ∣ n),
    stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2
  have hNp : 0 < N := by dsimp [N]; linarith
  have henergy : (∑ n ∈ S, ‖β n‖^2) ≤ 18*N*M^2 :=
    stopped_slice_energy X w z l b u M W selected e d hb hcoeff
  have hcard : (S.card:ℝ) ≤ 18*N := primary_support_card_le S hNp.le
    (fun n hn => ⟨(stoppedDivisorSlice_spec X l b e d hn).1,
      (stoppedDivisorSlice_spec X l b e d hn).2.2⟩)
  have hshift (v : Eisenstein) : f v ≤ ‖∑ n ∈ S, β n*cubicSymbol n v‖^2 :=
    pow_le_pow_left₀ (_root_.norm_nonneg _)
      (stopped_divisor_character_norm_le X w z l b u W selected e v hd) 2
  have htrivial (v : Eisenstein) : f v ≤ 324*N^2*M^2 := by
    apply (hshift v).trans
    apply (cubic_character_row_sq S
      (fun n hn => (stoppedDivisorSlice_spec X l b e d hn).1) β v).trans
    exact (mul_le_mul hcard henergy (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (by positivity)).trans_eq (by ring)
  have hsmall : (∑ v ∈ H.filter (fun v => v ∈ lowNoncubeSupport V (B^(1/3:ℝ))), f v) ≤
      104976*V*B^(1/3:ℝ)*N^2*M^2 := by
    have hc : ((H.filter (fun v => v ∈ lowNoncubeSupport V (B^(1/3:ℝ)))).card:ℝ) ≤
        324*V*B^(1/3:ℝ) :=
      (Nat.cast_le.mpr (Finset.card_le_card (by
        intro v hv
        exact (Finset.mem_filter.mp hv).2))).trans
          (lowNoncubeSupport_card hV.le (Real.rpow_nonneg hB _))
    calc
      _ ≤ ∑ _v ∈ H.filter (fun v => v ∈ lowNoncubeSupport V (B^(1/3:ℝ))),
          324*N^2*M^2 := Finset.sum_le_sum (fun v _ => htrivial v)
      _ = ((H.filter (fun v => v ∈ lowNoncubeSupport V (B^(1/3:ℝ)))).card:ℝ)*
          (324*N^2*M^2) := by simp
      _ ≤ (324*V*B^(1/3:ℝ))*(324*N^2*M^2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by ring
  have hrow (q : ℕ × ℕ) (hq : q ∈ largeCoreDyadicIndices V B) :
      (∑ v ∈ coreDyadicBlock B q.1 q.2, f v) ≤
      (18*K)*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*N*M^2 := by
    have hq' := (Finset.mem_filter.mp hq).2
    have hm := hcore S (coreDyadicBlock B q.1 q.2) β N B V q.1 q.2 hN hB hV
      (fun n hn => stoppedDivisorSlice_spec X l b e d hn) hq'.1.le
      ((mul_le_mul_of_nonneg_left hq'.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
      (Finset.Subset.refl _)
    apply (Finset.sum_le_sum (fun v _ => hshift v)).trans (hm.trans _)
    exact (mul_le_mul_of_nonneg_left henergy (by positivity)).trans_eq (by ring)
  have hlarge := Finset.sum_le_sum hrow
  simp only [Finset.sum_const,nsmul_eq_mul] at hlarge
  apply (noncube_frequency_mass_split H hH f (fun _ => sq_nonneg _)).trans
    ((add_le_add hsmall hlarge).trans_eq _)
  dsimp only [N]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorScale
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary scaling of the unrestricted sieve on shortened rows. -/
noncomputable section
namespace CubicFirstMoment

lemma quotient_power_times_self {b q : ℝ} (hb : 0 < b) (hq : 0 < q) (a : ℝ) :
    (b/q)^a*(b/q) = b^(a+1)*q^(-(a+1)) := by
  calc
    _ = (b/q)^(a+1) := by rw [Real.rpow_add (div_pos hb hq),Real.rpow_one]
    _ = b^(a+1)/q^(a+1) := Real.div_rpow hb.le hq.le (a+1)
    _ = _ := by rw [Real.rpow_neg hq.le,div_eq_mul_inv]

lemma stopped_outer_row_scale {b q B : ℝ} (hb : 0 < b) (hq : 0 < q) (hB : 0 ≤ B) :
    (B+(B*(b/q))^(2/3:ℝ)+B^(1/3:ℝ)*(b/q))*(b/q) =
      B*b*q^(-1:ℝ)+B^(2/3:ℝ)*b^(5/3:ℝ)*q^(-5/3:ℝ)+
        B^(1/3:ℝ)*b^2*q^(-2:ℝ) := by
  have hmid : (B*(b/q))^(2/3:ℝ)*(b/q) =
      B^(2/3:ℝ)*b^(5/3:ℝ)*q^(-5/3:ℝ) := by
    rw [Real.mul_rpow hB (div_nonneg hb.le hq.le),mul_assoc,
      quotient_power_times_self hb hq]
    norm_num
    ring
  have hsq : (b/q)^2 = b^2*q^(-2:ℝ) := by
    rw [Real.rpow_neg hq.le,Real.rpow_two,div_pow,div_eq_mul_inv]
  have hone : B*(b/q) = B*b*q^(-1:ℝ) := by
    rw [Real.rpow_neg_one]
    ring
  calc
    _ = B*(b/q)+(B*(b/q))^(2/3:ℝ)*(b/q)+B^(1/3:ℝ)*(b/q)^2 := by ring
    _ = _ := by rw [hmid,hsq,hone]; ring

lemma stopped_outer_row_scale_le {b q B ε : ℝ} (hb : 0 < b) (hq : 1 ≤ q)
    (hB : 0 ≤ B) (hε : 0 ≤ ε) :
    (2*B*(b/q))^ε*(B+(B*(b/q))^(2/3:ℝ)+B^(1/3:ℝ)*(b/q))*(b/q) ≤
      (2*B*b)^ε*(B*b*q^(-1:ℝ)+B^(2/3:ℝ)*b^(5/3:ℝ)*q^(-5/3:ℝ)+
        B^(1/3:ℝ)*b^2*q^(-2:ℝ)) := by
  have hqp : 0 < q := zero_lt_one.trans_le hq
  have hquot : b/q ≤ b := (div_le_iff₀ hqp).mpr (by nlinarith)
  calc
    _ = (2*B*(b/q))^ε*((B+(B*(b/q))^(2/3:ℝ)+B^(1/3:ℝ)*(b/q))*(b/q)) := by ring
    _ ≤ (2*B*b)^ε*((B+(B*(b/q))^(2/3:ℝ)+B^(1/3:ℝ)*(b/q))*(b/q)) := by
      apply mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by positivity)
          (mul_le_mul_of_nonneg_left hquot (by positivity)) hε)
      positivity
    _ = _ := by rw [stopped_outer_row_scale hb hqp hB]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorPowers
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed power margin in the unrestricted large-divisor terms for
frequency length at most the three-fifths power of the coefficient length. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_frequency_monomial {b B a c d : ℝ}
    (hb : 1 ≤ b) (hB : 0 < B) (hBb : B ≤ b^(3/5:ℝ))
    (ha : (1/3:ℝ) ≤ a) (hexp : (a-1/3)*(3/5)+c ≤ d) :
    B^a*b^c ≤ B^(1/3:ℝ)*b^d := by
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have hpower : B^(a-1/3) ≤ b^((a-1/3)*(3/5)) := by
    apply (Real.rpow_le_rpow hB.le hBb (by linarith)).trans_eq
    rw [←Real.rpow_mul hbp.le]
    congr 1
    ring
  calc
    _ = B^(1/3:ℝ)*(B^(a-1/3)*b^c) := by
      rw [←mul_assoc,←Real.rpow_add hB]
      congr 2
      ring
    _ ≤ B^(1/3:ℝ)*(b^((a-1/3)*(3/5))*b^c) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpower (by positivity)) (by positivity)
    _ = B^(1/3:ℝ)*b^((a-1/3)*(3/5)+c) := by rw [Real.rpow_add hbp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb hexp) (by positivity)

theorem stopped_large_divisor_power {b B C₁ C₂ C₃ : ℝ}
    (hb : 1 ≤ b) (hB : 0 < B) (hBb : B ≤ b^(3/5:ℝ))
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) :
    (2*B*b)^(1/1000:ℝ)*(
      B*b*b^(1/12:ℝ)*C₁+B^(2/3:ℝ)*b^(5/3:ℝ)*C₂+
      B^(1/3:ℝ)*b^2*(b^(1/8:ℝ))^(-(1/2:ℝ))*C₃) ≤
      (2:ℝ)^(1/1000:ℝ)*(C₁+C₂+C₃)*B^(1/3:ℝ)*b^(2-1/20:ℝ) := by
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have h₁ := stopped_frequency_monomial hb hB hBb
    (show (1/3:ℝ) ≤ 1+1/1000 by norm_num)
    (show ((1+1/1000:ℝ)-1/3)*(3/5)+(1+1/12+1/1000) ≤ 2-1/20 by norm_num)
  have h₂ := stopped_frequency_monomial hb hB hBb
    (show (1/3:ℝ) ≤ 2/3+1/1000 by norm_num)
    (show ((2/3+1/1000:ℝ)-1/3)*(3/5)+(5/3+1/1000) ≤ 2-1/20 by norm_num)
  have h₃ := stopped_frequency_monomial hb hB hBb
    (show (1/3:ℝ) ≤ 1/3+1/1000 by norm_num)
    (show ((1/3+1/1000:ℝ)-1/3)*(3/5)+(2+(-(1/16))+1/1000) ≤ 2-1/20 by norm_num)
  have hs : (b^(1/8:ℝ))^(-(1/2:ℝ)) = b^(-(1/16:ℝ)) := by
    rw [←Real.rpow_mul hbp.le]
    norm_num
  have hp : (2*B*b)^(1/1000:ℝ) = (2:ℝ)^(1/1000:ℝ)*B^(1/1000:ℝ)*b^(1/1000:ℝ) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 2*B) hbp.le,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hB.le]
  calc
    _ = (2:ℝ)^(1/1000:ℝ)*(
        C₁*(B^(1+1/1000:ℝ)*b^(1+1/12+1/1000:ℝ))+
        C₂*(B^(2/3+1/1000:ℝ)*b^(5/3+1/1000:ℝ))+
        C₃*(B^(1/3+1/1000:ℝ)*b^(2+(-(1/16))+1/1000:ℝ))) := by
      rw [hp,hs]
      simp only [Real.rpow_add hB,Real.rpow_add hbp,Real.rpow_one,Real.rpow_two]
      ring
    _ ≤ (2:ℝ)^(1/1000:ℝ)*(
        C₁*(B^(1/3:ℝ)*b^(2-1/20:ℝ))+C₂*(B^(1/3:ℝ)*b^(2-1/20:ℝ))+
        C₃*(B^(1/3:ℝ)*b^(2-1/20:ℝ))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left h₁ hC₁) (mul_le_mul_of_nonneg_left h₂ hC₂))
        (mul_le_mul_of_nonneg_left h₃ hC₃)) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedNoncubeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All finite noncube frequencies in the small-coefficient range have
arbitrary logarithmic cancellation for the literal stopped sequence.
The statement is pointwise in the logarithmic norm height. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_noncube_mass
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X → 65536 ≤ b →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ X^2 → 8*B ≤ b^(3/4:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool),
      (∑ v ∈ S, ‖stoppedCharacterSum X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) v e‖^2) ≤ K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K₀,K₁,hK₀,hK₁,hbound⟩ := stopped_noncube_core_blocks (ι := ι)
    hpnt hSW hHuxley hξ hξz hκ hH hF hJ (4*(k+2)) k (by omega)
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨C,hC,hnorm⟩ := log_power_normalization_bound (k+2)
    (show 0 < κ/20000 by positivity)
  let K := K₀+K₁*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (Real.exp 1)] with X hbound hX
  intro δ l b u V B hδ hδone hwidth hl hb hbX hbmin hV hu hVF
    hB hBX hsize W hW hWi hWd S hS e he hNe j₀ k₀ h Z Q early
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hlog : 1 ≤ Real.log X := by
    simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlogp : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hbp : 0 < b := by linarith
  let I := (largeCoreDyadicIndices ((Real.log X)^(4*(k+2))) B).card
  have hI : (I:ℝ) ≤ (4*CI)*(Real.log X)^2 := by
    apply (hcount _ B X hB hX1 hBX).trans
    calc
      _ ≤ CI*(2*Real.log X)^2 := by gcongr; linarith
      _ = _ := by ring
  have hpower : b^(-(1/20000:ℝ))*(Real.log X)^(k+2) ≤ C :=
    (stopped_length_log_power hX1 hb k).trans (hnorm X hX1)
  have hlarge := stopped_large_core_scale hbp hlogp (by positivity : 0 ≤ 4*CI)
    k hI hpower
  have hm := hbound δ l b u V B hδ hδone hwidth hl hb hbX hbmin hV hu hVF
    hB hBX hsize W hW hWi hWd S hS e he hNe j₀ k₀ h Z Q early
  apply hm.trans
  have hh := mul_le_mul_of_nonneg_left hlarge
    (show 0 ≤ K₁*B^(1/3:ℝ) by positivity)
  calc
    _ = K₀*B^(1/3:ℝ)*b^2/(Real.log X)^k+
        (K₁*B^(1/3:ℝ))*((I:ℝ)*
          (b*(((Real.log X)^(4*(k+2)))/5832)^(-(1/4:ℝ))+
            b^(1-1/20000:ℝ))*b) := by dsimp [I]; ring
    _ ≤ K₀*B^(1/3:ℝ)*b^2/(Real.log X)^k+
        (K₁*B^(1/3:ℝ))*((4*CI)*((5832:ℝ)^(1/4:ℝ)+C)*b^2/(Real.log X)^k) :=
      add_le_add_right hh _
    _ = _ := by dsimp [K]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLargeDivisorRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalize a single large-divisor row before summing the divisor norms. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_large_divisor_row {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M B : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e d : Eisenstein), primary d → 0 < b → 1 ≤ B → norm d ≤ b →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      ∀ H : Finset Eisenstein, (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
        (fun n => d ∣ n),
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤
      (K*(2*B*b)^ε*M^2)*(B*b*norm d^(-1:ℝ)+
        B^(2/3:ℝ)*b^(5/3:ℝ)*norm d^(-5/3:ℝ)+
        B^(1/3:ℝ)*b^2*norm d^(-2:ℝ)) := by
  obtain ⟨K,hK,hbound⟩ := stopped_filtered_outer_sieve (ι := ι) hε
  refine ⟨K,hK,?_⟩
  intro X w z l b u M B W selected e d hd hb hB hdb hcoeff H hH
  have hq := norm_pos_of_ne_zero (primary_ne_zero hd)
  have hqone := one_le_norm (primary_ne_zero hd)
  have hraw := hbound X w z l b u M B W selected e d
    hd hb.le hB ((le_div_iff₀ hq).mpr (by simpa using hdb)) hcoeff H hH
  have hh := stopped_outer_row_scale_le hb hqone (zero_le_one.trans hB) hε.le
  calc
    _ ≤ K*((2*B*(b/norm d))^ε*
        (B+(B*(b/norm d))^(2/3:ℝ)+B^(1/3:ℝ)*(b/norm d))*
        (b/norm d))*M^2 := hraw.trans_eq (by ring)
    _ ≤ K*((2*B*b)^ε*(B*b*norm d^(-1:ℝ)+
        B^(2/3:ℝ)*b^(5/3:ℝ)*norm d^(-5/3:ℝ)+
        B^(1/3:ℝ)*b^2*norm d^(-2:ℝ)))*M^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh hK.le) (sq_nonneg M)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSubsetNormTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The sum over distinct prime subsets has no multiplicity loss after
mapping each subset to its primary product. A convergent lattice norm
series therefore controls its inverse-square tail. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primary_prime_subset_norm_sum (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (A : Finset (Finset Eisenstein))
    (hA : A ⊆ U.powerset) {s : ℝ} (hs : 1 < s) :
    (∑ d ∈ A, norm (∏ p ∈ d,p)^(-s)) ≤
      ∑' n : Eisenstein, norm n^(-s) := by
  have hinj : Set.InjOn (fun d : Finset Eisenstein => ∏ p ∈ d,p) (↑A : Set _) := by
    intro d hd e he hde
    exact primaryPrimeFactors_prod_injective hU (hA hd) (hA he) hde
  calc
    _ = ∑ n ∈ A.image (fun d : Finset Eisenstein => ∏ p ∈ d,p), norm n^(-s) :=
      (Finset.sum_image (f := fun n : Eisenstein => norm n^(-s)) hinj).symm
    _ ≤ _ := (summable_eisenstein_norm_rpow hs).sum_le_tsum _
      (fun n _ => Real.rpow_nonneg (norm_nonneg n) _)

theorem primary_prime_subset_harmonic (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) :
    (∑ d ∈ U.powerset.filter (fun d => norm (∏ p ∈ d,p) ≤ b),
      (norm (∏ p ∈ d,p))⁻¹) ≤
      b^ε*(∑' n : Eisenstein, norm n^(-(1+ε))) := by
  let A := U.powerset.filter (fun d => norm (∏ p ∈ d,p) ≤ b)
  have hp (d : Finset Eisenstein) (hd : d ∈ A) :
      (norm (∏ p ∈ d,p))⁻¹ ≤ b^ε*norm (∏ p ∈ d,p)^(-(1+ε)) := by
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hd).1
    have hdp := norm_pos_of_ne_zero (primary_ne_zero
      (primary_finset_prod d (fun p => p) (fun p hp => (hU p (hsub hp)).1)))
    have he : (norm (∏ p ∈ d,p))⁻¹ =
        norm (∏ p ∈ d,p)^ε*norm (∏ p ∈ d,p)^(-(1+ε)) := by
      rw [←Real.rpow_add hdp]
      rw [show ε+ -(1+ε) = (-1:ℝ) by ring,Real.rpow_neg_one]
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hdp.le (Finset.mem_filter.mp hd).2 hε.le) (by positivity)
  calc
    _ ≤ ∑ d ∈ A, b^ε*norm (∏ p ∈ d,p)^(-(1+ε)) := Finset.sum_le_sum hp
    _ = b^ε*(∑ d ∈ A, norm (∏ p ∈ d,p)^(-(1+ε))) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (primary_prime_subset_norm_sum U hU A (fun _ hd => (Finset.mem_filter.mp hd).1)
        (by linarith : 1 < 1+ε)) (Real.rpow_nonneg hb.le _)

lemma finite_eisenstein_norm_square_tail (S : Finset Eisenstein) {D : ℝ}
    (hD : 0 < D) (hS : ∀ n ∈ S, D < norm n) :
    (∑ n ∈ S, norm n^(-2:ℝ)) ≤
      D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) := by
  calc
    _ ≤ ∑ n ∈ S, D^(-(1/2:ℝ))*norm n^(-(3/2:ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [show (3/2:ℝ)-2 = -(1/2:ℝ) by norm_num] using
        norm_rpow_tail_pointwise (s := 3/2) (t := 2) hD (by norm_num) (hS n hn)
    _ = D^(-(1/2:ℝ))*(∑ n ∈ S, norm n^(-(3/2:ℝ))) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_eisenstein_norm_rpow (show (1:ℝ) < 3/2 by norm_num)).sum_le_tsum S
        (fun n _ => Real.rpow_nonneg (norm_nonneg n) _)) (by positivity)

theorem primary_prime_subset_norm_tail (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) {D : ℝ} (hD : 0 < D) :
    (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s,p)),
      norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) := by
  let S := U.powerset.filter (fun s => D < norm (∏ p ∈ s,p))
  have hinj : Set.InjOn (fun s : Finset Eisenstein => ∏ p ∈ s,p) (↑S : Set _) := by
    intro s hs t ht he
    exact primaryPrimeFactors_prod_injective hU
      (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp ht).1 he
  calc
    _ = ∑ n ∈ S.image (fun s : Finset Eisenstein => ∏ p ∈ s,p), norm n^(-2:ℝ) :=
      (Finset.sum_image (f := fun n : Eisenstein => norm n^(-2:ℝ)) hinj).symm
    _ ≤ _ := finite_eisenstein_norm_square_tail _ hD (by
      intro n hn
      obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hn
      exact (Finset.mem_filter.mp hs).2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeSubsetBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricted versions of the convergent prime-subset norm sums. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_prime_subset_harmonic_on (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (A : Finset (Finset Eisenstein))
    (hA : A ⊆ U.powerset) {b η : ℝ} (hb : 0 < b) (hη : 0 < η)
    (hbound : ∀ s ∈ A, norm (∏ p ∈ s,p) ≤ b) :
    (∑ s ∈ A, norm (∏ p ∈ s,p)^(-1:ℝ)) ≤
      b^η*(∑' n : Eisenstein, norm n^(-(1+η))) := by
  apply le_trans _ (primary_prime_subset_harmonic U hU hb hη)
  simp only [Real.rpow_neg_one]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    exact Finset.mem_filter.mpr ⟨hA hs,hbound s hs⟩
  · intro s _ _
    exact inv_nonneg.mpr (norm_nonneg _)

lemma primary_prime_subset_tail_on (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) (A : Finset (Finset Eisenstein))
    (hA : A ⊆ U.powerset) {D : ℝ} (hD : 0 < D)
    (hbound : ∀ s ∈ A, D < norm (∏ p ∈ s,p)) :
    (∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) := by
  apply le_trans _ (primary_prime_subset_norm_tail U hU hD)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    exact Finset.mem_filter.mpr ⟨hA hs,hbound s hs⟩
  · intro s _ _
    exact Real.rpow_nonneg (norm_nonneg _) _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLargeDivisorMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the large-divisor rows using genuine quotient lengths. The
distinct-prime-subset map is injective, so the estimates involve convergent
lattice norm series and no cardinality of the ambient prime set. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_large_divisor_mass {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M B D : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e : Eisenstein) (U H : Finset Eisenstein),
      0 < b → 1 ≤ B → 0 < D → (∀ p ∈ U, primaryPrime p) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ s ∈ U.powerset.filter (fun s => D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b),
        ∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
            (fun n => (∏ p ∈ s,p) ∣ n),
          stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤
      K*(2*B*b)^ε*M^2*(
        B*b*b^η*(∑' n : Eisenstein, norm n^(-(1+η)))+
        B^(2/3:ℝ)*b^(5/3:ℝ)*(∑' n : Eisenstein, norm n^(-(5/3:ℝ)))+
        B^(1/3:ℝ)*b^2*D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ)))) := by
  obtain ⟨K,hK,hbound⟩ := stopped_large_divisor_row (ι := ι) hε
  refine ⟨K,hK,?_⟩
  intro X w z l b u M B D W selected e U H hb hB hD hU hcoeff hH
  let A := U.powerset.filter
    (fun s => D < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b)
  let P := K*(2*B*b)^ε*M^2
  let F := fun s : Finset Eisenstein =>
    B*b*norm (∏ p ∈ s,p)^(-1:ℝ)+
    B^(2/3:ℝ)*b^(5/3:ℝ)*norm (∏ p ∈ s,p)^(-5/3:ℝ)+
    B^(1/3:ℝ)*b^2*norm (∏ p ∈ s,p)^(-2:ℝ)
  have hrow (s : Finset Eisenstein) (hs : s ∈ A) :
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
        (fun n => (∏ p ∈ s,p) ∣ n),
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤ P*F s := by
    have hsub := Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1
    have hsp := primary_finset_prod s (fun p => p) (fun p hp => (hU p (hsub hp)).1)
    exact hbound X w z l b u M B W selected e (∏ p ∈ s,p)
      hsp hb hB (Finset.mem_filter.mp hs).2.2 hcoeff H hH
  have h₁ : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-1:ℝ)) ≤
      b^η*(∑' n : Eisenstein, norm n^(-(1+η))) :=
    primary_prime_subset_harmonic_on U hU A
      (fun _ hs => (Finset.mem_filter.mp hs).1) hb hη
      (fun _ hs => (Finset.mem_filter.mp hs).2.2)
  have h₂ : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-5/3:ℝ)) ≤
      ∑' n : Eisenstein, norm n^(-(5/3:ℝ)) :=
    by simpa only [neg_div] using
      (primary_prime_subset_norm_sum (s := 5/3) U hU A
        (fun _ hs => (Finset.mem_filter.mp hs).1) (by norm_num))
  have h₃ : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) :=
    primary_prime_subset_tail_on U hU A
      (fun _ hs => (Finset.mem_filter.mp hs).1) hD
      (fun _ hs => (Finset.mem_filter.mp hs).2.1)
  have hsum : (∑ s ∈ A, F s) ≤
      B*b*(b^η*(∑' n : Eisenstein, norm n^(-(1+η))))+
      B^(2/3:ℝ)*b^(5/3:ℝ)*(∑' n : Eisenstein, norm n^(-(5/3:ℝ)))+
      B^(1/3:ℝ)*b^2*(D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ)))) := by
    dsimp only [F]
    simp only [Finset.sum_add_distrib,←Finset.mul_sum]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₁ (by positivity))
      (mul_le_mul_of_nonneg_left h₂ (by positivity)))
      (mul_le_mul_of_nonneg_left h₃ (by positivity))
  calc
    _ ≤ ∑ s ∈ A, P*F s := Finset.sum_le_sum hrow
    _ = P*(∑ s ∈ A, F s) := (Finset.mul_sum _ _ _).symm
    _ ≤ P*(B*b*(b^η*(∑' n : Eisenstein, norm n^(-(1+η))))+
        B^(2/3:ℝ)*b^(5/3:ℝ)*(∑' n : Eisenstein, norm n^(-(5/3:ℝ)))+
        B^(1/3:ℝ)*b^2*(D^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))))) :=
      mul_le_mul_of_nonneg_left hsum (by dsimp [P]; positivity)
    _ = _ := by dsimp [P]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedLargeDivisorPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At the fixed cutoff b^(1/8), the actual large-divisor rows save
a fixed power uniformly in the ambient set of primes. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_large_divisor_power_mass :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M B : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e : Eisenstein) (U H : Finset Eisenstein),
      1 ≤ b → 1 ≤ B → B ≤ b^(3/5:ℝ) → (∀ p ∈ U, primaryPrime p) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B) →
      (∑ s ∈ U.powerset.filter
          (fun s => b^(1/8:ℝ) < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b),
        ∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
            (fun n => (∏ p ∈ s,p) ∣ n),
          stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤
      K*B^(1/3:ℝ)*b^(2-1/20:ℝ)*M^2 := by
  obtain ⟨K,hK,hbound⟩ := stopped_large_divisor_mass (ι := ι)
    (show (0:ℝ) < 1/1000 by norm_num) (show (0:ℝ) < 1/12 by norm_num)
  let C₁ := ∑' n : Eisenstein, norm n^(-(1+1/12:ℝ))
  let C₂ := ∑' n : Eisenstein, norm n^(-(5/3:ℝ))
  let C₃ := ∑' n : Eisenstein, norm n^(-(3/2:ℝ))
  have hC₁ : 0 ≤ C₁ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  have hC₂ : 0 ≤ C₂ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  have hC₃ : 0 ≤ C₃ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  let C := (2:ℝ)^(1/1000:ℝ)*(C₁+C₂+C₃)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨K*(C+1),by positivity,?_⟩
  intro X w z l b u M B W selected e U H hb hB hBb hU hcoeff hH
  have hbp : 0 < b := zero_lt_one.trans_le hb
  have hm := hbound X w z l b u M B (b^(1/8:ℝ)) W selected e U H
    hbp hB (Real.rpow_pos_of_pos hbp _) hU hcoeff hH
  have hs := stopped_large_divisor_power hb (zero_lt_one.trans_le hB) hBb hC₁ hC₂ hC₃
  apply hm.trans
  calc
    _ = (K*M^2)*((2*B*b)^(1/1000:ℝ)*(
        B*b*b^(1/12:ℝ)*C₁+B^(2/3:ℝ)*b^(5/3:ℝ)*C₂+
        B^(1/3:ℝ)*b^2*(b^(1/8:ℝ))^(-(1/2:ℝ))*C₃)) := by
      dsimp [C₁,C₂,C₃]; ring
    _ ≤ (K*M^2)*(C*B^(1/3:ℝ)*b^(2-1/20:ℝ)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (K*M^2)*((C+1)*B^(1/3:ℝ)*b^(2-1/20:ℝ)) := by gcongr; linarith
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSmallDivisorMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the hybrid core bound over actual short divisor rows. The rough
lower cutoff is used only in the elementary small-core term; the two
hybrid terms are summed by convergent norm series. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_small_divisor_mass (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (X w z l b u M V B R : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e : Eisenstein) (U : Finset Eisenstein) (A : Finset (Finset Eisenstein))
      (H : Finset Eisenstein),
      0 < b → 0 < V → 0 ≤ B → 0 < R → (∀ p ∈ U, primaryPrime p) →
      A ⊆ U.powerset →
      (∀ s ∈ A, R < norm (∏ p ∈ s,p) ∧ 65536 ≤ b/norm (∏ p ∈ s,p) ∧
        8*B ≤ (b/norm (∏ p ∈ s,p))^(3/4:ℝ)) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∑ s ∈ A, ∑ v ∈ H,
        ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter (fun n => (∏ p ∈ s,p) ∣ n),
          stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤
      104976*V*B^(1/3:ℝ)*b^2*M^2*R^(-(1/2:ℝ))*
        (∑' n : Eisenstein, norm n^(-(3/2:ℝ)))+
      K*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*M^2*(
        b^2*(V/5832)^(-(1/4:ℝ))*(∑' n : Eisenstein, norm n^(-2:ℝ))+
        b^(2-1/20000:ℝ)*(∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ)))) := by
  obtain ⟨K,hK,hbound⟩ := stopped_filtered_core_blocks (ι := ι) hHuxley
  refine ⟨K,hK,?_⟩
  intro X w z l b u M V B R W selected e U A H hb hV hB hR hU hA hrows hcoeff hH
  let L := 104976*V*B^(1/3:ℝ)*b^2*M^2
  let P := K*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*M^2
  let E := (V/5832)^(-(1/4:ℝ))
  let f := fun s : Finset Eisenstein =>
    L*norm (∏ p ∈ s,p)^(-2:ℝ)+P*(b^2*E*norm (∏ p ∈ s,p)^(-2:ℝ)+
      b^(2-1/20000:ℝ)*norm (∏ p ∈ s,p)^(-(2-1/20000:ℝ)))
  have hrow (s : Finset Eisenstein) (hs : s ∈ A) :
      (∑ v ∈ H, ‖∑ n ∈ (stoppedIntervalSupport ι X l b e).filter
        (fun n => (∏ p ∈ s,p) ∣ n),
        stoppedRowCoefficient X w z u W selected n*cubicSymbol n v‖^2) ≤ f s := by
    have hsp := primary_finset_prod s (fun p => p)
      (fun p hp => (hU p (Finset.mem_powerset.mp (hA hs) hp)).1)
    have hq := norm_pos_of_ne_zero (primary_ne_zero hsp)
    have hm := hbound X w z l b u M V B W selected e (∏ p ∈ s,p)
      hsp hb.le hV hB (hrows s hs).2.1 (hrows s hs).2.2 hcoeff H hH
    have hsquare : (b/norm (∏ p ∈ s,p))^2 =
        b^2*norm (∏ p ∈ s,p)^(-2:ℝ) := by
      rw [Real.rpow_neg hq.le,Real.rpow_two,div_pow,div_eq_mul_inv]
    have hpower := quotient_power_times_self hb hq (1-1/20000:ℝ)
    rw [show (1-1/20000:ℝ)+1 = 2-1/20000 by ring] at hpower
    apply hm.trans_eq
    dsimp [f,L,P,E]
    rw [hsquare]
    calc
      _ = 104976*V*B^(1/3:ℝ)*(b^2*norm (∏ p ∈ s,p)^(-2:ℝ))*M^2+
          K*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*M^2*
          ((b/norm (∏ p ∈ s,p))^2*(V/5832)^(-(1/4:ℝ))+
            (b/norm (∏ p ∈ s,p))^(1-1/20000:ℝ)*(b/norm (∏ p ∈ s,p))) := by ring
      _ = _ := by rw [hsquare,hpower]; ring
  have hsmall : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      R^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))) := by
    apply le_trans _ (primary_prime_subset_norm_tail U hU hR)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro s hs
      exact Finset.mem_filter.mpr ⟨hA hs,(hrows s hs).1⟩
    · intro s _ _
      exact Real.rpow_nonneg (norm_nonneg _) _
  have htwo : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ)) ≤
      ∑' n : Eisenstein, norm n^(-2:ℝ) :=
    primary_prime_subset_norm_sum (s := 2) U hU A hA (by norm_num)
  have hpower : (∑ s ∈ A, norm (∏ p ∈ s,p)^(-(2-1/20000:ℝ))) ≤
      ∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ)) :=
    primary_prime_subset_norm_sum (s := 2-1/20000) U hU A hA (by norm_num)
  calc
    _ ≤ ∑ s ∈ A, f s := Finset.sum_le_sum hrow
    _ = L*(∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ))+
        P*(b^2*E*(∑ s ∈ A, norm (∏ p ∈ s,p)^(-2:ℝ))+
          b^(2-1/20000:ℝ)*(∑ s ∈ A, norm (∏ p ∈ s,p)^(-(2-1/20000:ℝ)))) := by
      dsimp [f]
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_assoc]
    _ ≤ L*(R^(-(1/2:ℝ))*(∑' n : Eisenstein, norm n^(-(3/2:ℝ))))+
        P*(b^2*E*(∑' n : Eisenstein, norm n^(-2:ℝ))+
          b^(2-1/20000:ℝ)*(∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ)))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsmall (by dsimp [L]; positivity))
        (mul_le_mul_of_nonneg_left (add_le_add
          (mul_le_mul_of_nonneg_left htwo (by dsimp [E]; positivity))
          (mul_le_mul_of_nonneg_left hpower (by positivity))) (by dsimp [P]; positivity))
    _ = _ := by dsimp [L,P,E]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedRoughDivisorMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete divisor mass differs from its empty row by the two
controlled tails. The roughness premise concerns the actual coefficients. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_rough_divisor_mass (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ (X w z l b u M V B R : ℝ)
      (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop)
      (e : Eisenstein) (U H : Finset Eisenstein),
      1 ≤ b → 0 < V → 1 ≤ B → B ≤ b^(3/5:ℝ) → 2 < R →
      65536 ≤ b/b^(1/8:ℝ) → 8*B ≤ (b/b^(1/8:ℝ))^(3/4:ℝ) →
      (∀ p ∈ U, primaryPrime p) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        stoppedRowCoefficient X w z u W selected n ≠ 0 →
        ∀ p, primaryPrime p → p ∣ n → R ≤ norm p) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      stoppedDivisorMass X w z l b u W selected e H U ≤
      (∑ v ∈ H, ‖stoppedCharacterSum X w z l b u W selected v e‖^2)+
      (104976*V*B^(1/3:ℝ)*b^2*M^2*(R/2)^(-(1/2:ℝ))*
        (∑' n : Eisenstein, norm n^(-(3/2:ℝ)))+
      K₁*((largeCoreDyadicIndices V B).card:ℝ)*B^(1/3:ℝ)*M^2*(
        b^2*(V/5832)^(-(1/4:ℝ))*(∑' n : Eisenstein, norm n^(-2:ℝ))+
        b^(2-1/20000:ℝ)*(∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ)))))+
      K₂*B^(1/3:ℝ)*b^(2-1/20:ℝ)*M^2 := by
  obtain ⟨K₁,hK₁,hsmall⟩ := stopped_small_divisor_mass (ι := ι) hHuxley
  obtain ⟨K₂,hK₂,hlarge⟩ := stopped_large_divisor_power_mass (ι := ι)
  refine ⟨K₁,K₂,hK₁,hK₂,?_⟩
  intro X w z l b u M V B R W selected e U H hb hV hB hBb hR hN hsize hU hcoeff hrough hH
  let A := U.powerset.filter
    (fun s => R/2 < norm (∏ p ∈ s,p) ∧ norm (∏ p ∈ s,p) ≤ b^(1/8:ℝ))
  have hA : A ⊆ U.powerset := Finset.filter_subset _ _
  have hrows (s : Finset Eisenstein) (hs : s ∈ A) :
      R/2 < norm (∏ p ∈ s,p) ∧ 65536 ≤ b/norm (∏ p ∈ s,p) ∧
        8*B ≤ (b/norm (∏ p ∈ s,p))^(3/4:ℝ) := by
    have hsp := primary_finset_prod s (fun p => p)
      (fun p hp => (hU p (Finset.mem_powerset.mp (hA hs) hp)).1)
    have hq := norm_pos_of_ne_zero (primary_ne_zero hsp)
    have hquot := div_le_div_of_nonneg_left (zero_le_one.trans hb) hq
      (Finset.mem_filter.mp hs).2.2
    exact ⟨(Finset.mem_filter.mp hs).2.1,hN.trans hquot,
      hsize.trans (Real.rpow_le_rpow (by positivity) hquot (by norm_num))⟩
  have hs := hsmall X w z l b u M V B (R/2) W selected e U A H
    (zero_lt_one.trans_le hb) hV (zero_le_one.trans hB) (by linarith) hU hA hrows hcoeff hH
  have hl := hlarge X w z l b u M B W selected e U H hb hB hBb hU hcoeff
    (fun v hv => ⟨(hH v hv).1,(hH v hv).2.1⟩)
  rw [stopped_rough_divisor_partition X w z l b u R (b^(1/8:ℝ)) W selected e U H
    hU hR (Real.one_le_rpow hb (by norm_num)) hrough]
  exact add_le_add (add_le_add (le_refl _) hs) hl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedRoughDivisorLog
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summed nonempty divisor rows have arbitrary logarithmic savings.
No cancellation is assumed for the empty row in this arithmetic estimate. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_rough_divisor_log (hHuxley : HuxleyAdditiveLargeSieve)
    {κ : ℝ} (hκ : 0 < κ) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (w z l b u M B R : ℝ) (W : ι → ℝ → ℂ)
      (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
      (U H : Finset Eisenstein),
      X^κ ≤ b → b ≤ X → 1 ≤ B → B ≤ b^(3/5:ℝ) → 2 < R →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤ R →
      (∀ p ∈ U, primaryPrime p) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        ‖stoppedRowCoefficient X w z u W selected n‖ ≤ M) →
      (∀ n ∈ stoppedIntervalSupport ι X l b e,
        stoppedRowCoefficient X w z u W selected n ≠ 0 →
        ∀ p, primaryPrime p → p ∣ n → R ≤ norm p) →
      (∀ v ∈ H, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      stoppedDivisorMass X w z l b u W selected e H U ≤
        (∑ v ∈ H, ‖stoppedCharacterSum X w z l b u W selected v e‖^2)+
        K*b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
  obtain ⟨K₁,K₂,hK₁,hK₂,hbound⟩ := stopped_rough_divisor_mass (ι := ι) hHuxley
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨C,hC,hnorm⟩ := log_power_normalization_bound (k+2)
    (show 0 < κ/20000 by positivity)
  let S₂ := ∑' n : Eisenstein, norm n^(-2:ℝ)
  let Sε := ∑' n : Eisenstein, norm n^(-(2-1/20000:ℝ))
  let S₃ := ∑' n : Eisenstein, norm n^(-(3/2:ℝ))
  have hS₂ : 0 ≤ S₂ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  have hSε : 0 ≤ Sε := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  have hS₃ : 0 ≤ S₃ := tsum_nonneg (fun n => Real.rpow_nonneg (norm_nonneg n) _)
  let K := 104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C+1
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  filter_upwards [stopped_divisor_cutoff_geometry hκ,
    eventually_ge_atTop (Real.exp 1)] with X hgeometry hX
  intro w z l b u M B R W selected e U H hb hbX hB hBb hR hRL hU hcoeff hrough hH
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hL1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hL1
  obtain ⟨hb1,hN,hsize⟩ := hgeometry b B hb hBb
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hBX : B ≤ X^2 := by
    apply hBb.trans
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow (zero_le_one.trans hb1) hbX (by norm_num : (0:ℝ) ≤ 3/5)).trans
        (Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num : (3/5:ℝ) ≤ 2))
  let V := (Real.log X)^(4*(k+2))
  let I := ((largeCoreDyadicIndices V B).card:ℝ)
  have hI : I ≤ (4*CI)*(Real.log X)^2 := by
    apply (hcount V B X hB hX1 hBX).trans
    calc
      _ ≤ CI*(2*Real.log X)^2 := by gcongr; linarith
      _ = _ := by ring
  have hpower : b^(-(1/20000:ℝ))*(Real.log X)^(k+2) ≤ C :=
    (stopped_length_log_power hX1 hb k).trans (hnorm X hX1)
  have hlargePower : b^(-(1/20:ℝ))*(Real.log X)^k ≤ C := by
    apply le_trans _ hpower
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hb1 (by norm_num : -(1/20:ℝ) ≤ -(1/20000)))
      (pow_le_pow_right₀ hL1 (Nat.le_add_right k 2))
      (pow_nonneg hLp.le _) (Real.rpow_nonneg hbp.le _)
  have hlargeScalar : b^(2-1/20:ℝ) ≤ C*b^2/(Real.log X)^k := by
    simpa only [pow_zero,mul_one,Real.rpow_two] using
      (rpow_log_saving hbp hLp k 0 (p := 2) (s := 1/20) (by simpa using hlargePower))
  have hhybrid := stopped_hybrid_weighted_scale hbp hLp
    (show 0 ≤ 4*CI by positivity) k (show 0 ≤ I by dsimp [I]; positivity) hI hpower
    (show S₂ ≤ S₂+Sε by linarith) (show Sε ≤ S₂+Sε by linarith)
    (show 0 ≤ S₂+Sε by positivity)
  have hcut := rough_cutoff_log_saving hLp (4*(k+2)) k hRL
  have hm := hbound X w z l b u M V B R W selected e U H hb1
    (by dsimp [V]; positivity) hB hBb hR hN hsize hU hcoeff hrough hH
  apply hm.trans
  have hs : 104976*V*B^(1/3:ℝ)*b^2*M^2*(R/2)^(-(1/2:ℝ))*S₃ ≤
      (104976*S₃)*b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
    calc
      _ = (104976*S₃*b^2*B^(1/3:ℝ)*M^2)*(V*(R/2)^(-(1/2:ℝ))) := by ring
      _ ≤ (104976*S₃*b^2*B^(1/3:ℝ)*M^2)*(1/(Real.log X)^k) :=
        mul_le_mul_of_nonneg_left hcut (by positivity)
      _ = _ := by ring
  have hh : K₁*I*B^(1/3:ℝ)*M^2*(
      b^2*(V/5832)^(-(1/4:ℝ))*S₂+b^(2-1/20000:ℝ)*Sε) ≤
      (K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C))*
        b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
    calc
      _ = (K₁*B^(1/3:ℝ)*M^2)*(I*(b^2*(V/5832)^(-(1/4:ℝ))*S₂+
          b^(2-1/20000:ℝ)*Sε)) := by ring
      _ ≤ (K₁*B^(1/3:ℝ)*M^2)*((S₂+Sε)*(4*CI)*
          ((5832:ℝ)^(1/4:ℝ)+C)*b^2/(Real.log X)^k) :=
        mul_le_mul_of_nonneg_left hhybrid (by positivity)
      _ = _ := by ring
  have hl : K₂*B^(1/3:ℝ)*b^(2-1/20:ℝ)*M^2 ≤
      (K₂*C)*b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
    calc
      _ = (K₂*B^(1/3:ℝ)*M^2)*b^(2-1/20:ℝ) := by ring
      _ ≤ (K₂*B^(1/3:ℝ)*M^2)*(C*b^2/(Real.log X)^k) :=
        mul_le_mul_of_nonneg_left hlargeScalar (by positivity)
      _ = _ := by ring
  have he := add_le_add (add_le_add hs hh) hl
  have hn : 0 ≤ b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by positivity
  have herror := he.trans_eq (show _ =
      (104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C)*
        b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k by ring)
  have htotal :
      (104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C)*
        b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k ≤
      K*b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k := by
    calc
      _ = (104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C)*
          (b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k) := by ring
      _ ≤ (104976*S₃+K₁*(S₂+Sε)*(4*CI)*((5832:ℝ)^(1/4:ℝ)+C)+K₂*C+1)*
          (b^2*B^(1/3:ℝ)*M^2/(Real.log X)^k) :=
        mul_le_mul_of_nonneg_right (by linarith) hn
      _ = _ := by dsimp [K]; ring
  have hf := add_le_add_left (herror.trans htotal)
    (∑ v ∈ H, ‖stoppedCharacterSum X w z l b u W selected v e‖^2)
  first | (convert hf using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hf.trans (le_of_eq (by ring)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedEarlyDivisorMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Noncube cancellation for the full coprimality expansion of the literal
early-stopped coefficient. Its coefficient bound and roughness are proved
from the actual stopping construction. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_early_divisor_noncube_mass_oai
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ H E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hH : 0 ≤ H) (hF : 0 ≤ F) (hJ : 0 ≤ J) (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ l b u V B : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      1 ≤ l → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      ∀ (S U : Finset Eisenstein),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∀ p ∈ U, primaryPrime p) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      stoppedDivisorMass X (X^ξ) (X^(2/5:ℝ)) l b u W
        (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
          j₀ k₀ h Z Q early) e S U ≤
        K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K₀,hK₀,hempty⟩ := stopped_noncube_mass (ι := ι)
    hpnt hSW hHuxley hξ hξz hκ hH hF hJ k
  obtain ⟨K₁,hK₁,hdiv⟩ := stopped_rough_divisor_log (ι := ι) hHuxley hκ k
  obtain ⟨M,hM,hcoeff⟩ := stopped_interval_energy (ι := ι) hξ hξz
  refine ⟨K₀+K₁*M^2,by positivity,?_⟩
  filter_upwards [hempty,hdiv,hcoeff,stopped_divisor_cutoff_geometry hκ,
    eventually_ge_atTop (1:ℝ)] with X hempty hdiv hcoeff hgeometry hX
  intro δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb W hW hWi hWd
    S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL
  have hXp : 0 < X := zero_lt_one.trans_le hX
  obtain ⟨hb1,hN,hsize⟩ := hgeometry b B hb hBb
  have hD1 : 1 ≤ b^(1/8:ℝ) := Real.one_le_rpow hb1 (by norm_num)
  have hqb : b/b^(1/8:ℝ) ≤ b := div_le_self (zero_le_one.trans hb1) hD1
  have hbmin : 65536 ≤ b := hN.trans hqb
  have hsize' : 8*B ≤ b^(3/4:ℝ) := hsize.trans
    (Real.rpow_le_rpow (by positivity) hqb (by norm_num))
  have hBX : B ≤ X^2 := by
    apply hBb.trans
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow (zero_le_one.trans hb1) hbX (by norm_num : (0:ℝ) ≤ 3/5)).trans
        (Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (3/5:ℝ) ≤ 2))
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  have hcoeff' := (hcoeff W hW selected u l b e (zero_le_one.trans hb1) hbX).1
  have hrough : ∀ n ∈ stoppedIntervalSupport ι X l b e,
      stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n ≠ 0 →
      ∀ p, primaryPrime p → p ∣ n →
        min (X^ξ) (geometricBinLower (1+δ) X h) ≤ norm p := by
    intro n _ hn p hp hpn
    exact stoppedRowCoefficient_early_roughness X (X^ξ) (X^(2/5:ℝ)) u
      (1+δ) Z Q W (Real.rpow_pos_of_pos hXp _)
      (Real.rpow_le_rpow_of_exponent_le hX hξz) (by linarith) (by linarith)
      j₀ k₀ h early hj hn hp hpn
  have hd := hdiv (X^ξ) (X^(2/5:ℝ)) l b u M B
    (min (X^ξ) (geometricBinLower (1+δ) X h)) W selected e U S
    hb hbX hB hBb hR hRL hU hcoeff' hrough hS
  have he' := hempty δ l b u V B hδ hδone hwidth hl hb hbX hbmin hV hu hVF
    hB hBX hsize' W hW hWi hWd S hS e he hNe j₀ k₀ h Z Q early
  exact hd.trans ((add_le_add he' (le_refl _)).trans_eq (by ring))

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.stopped_early_divisor_noncube_mass_oai.{u_1} := @OAI.CubicFirstMoment.stopped_early_divisor_noncube_mass_oai.{u_1}
