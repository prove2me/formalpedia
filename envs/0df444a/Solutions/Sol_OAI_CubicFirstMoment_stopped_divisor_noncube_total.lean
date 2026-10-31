-- Prove2me | solution 1 for OAI.CubicFirstMoment.stopped_divisor_noncube_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:46:23.920869+00:00
-- url     : https://prove2.me/submissions/234547c2-7352-4542-be19-8bc71c8f94dc

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015
import Definitions.Def_OAIQ096A016
import Theorems.Thm_OAI_CubicFirstMoment_stopped_noncube_radial_form

section
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_GramPoisson
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal character Gram kernel and normalized radial Poisson expansion. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable

noncomputable section
open Filter
open scoped ContDiff

namespace CubicFirstMoment

lemma normProfileFourier_mul_unit (W : ℝ → ℂ) {u : ℂ}
    (hu : Complex.normSq u = 1) (w : ℂ) :
    normProfileFourier W (u*w) = normProfileFourier W w := by
  have hu0 : u ≠ 0 := by
    intro he
    simp [he] at hu
  have hf : (fun z : ℂ => W (Complex.normSq (u⁻¹*z))) =
      (fun z : ℂ => W (Complex.normSq z)) := by
    funext z
    simp only [Complex.normSq_mul, Complex.normSq_inv, hu, inv_one, one_mul]
  have he := traceFourier_complexMul u⁻¹ (inv_ne_zero hu0)
    (fun z : ℂ => W (Complex.normSq z)) w
  rw [hf, Complex.normSq_inv, hu, inv_one, inv_one, one_smul] at he
  unfold normProfileFourier
  congr 1
  simpa only [div_inv_eq_mul, mul_comm] using he.symm

lemma normProfileFourier_eq_of_normSq_eq (W : ℝ → ℂ) {y y' : ℂ}
    (hy : Complex.normSq y = Complex.normSq y') :
    normProfileFourier W y = normProfileFourier W y' := by
  by_cases hy0 : y' = 0
  · have hy1 : y = 0 := Complex.normSq_eq_zero.mp (by simpa [hy0] using hy)
    rw [hy0, hy1]
  · have hu : Complex.normSq (y / y') = 1 := by
      rw [Complex.normSq_div, hy, div_self (mt Complex.normSq_eq_zero.mp hy0)]
    simpa only [div_mul_cancel₀ _ hy0] using normProfileFourier_mul_unit W hu y'

lemma normProfileFourier_radial (W : ℝ → ℂ) (y : ℂ) :
    normProfileFourier W y = radialDualProfile W (Complex.normSq y) := by
  apply normProfileFourier_eq_of_normSq_eq
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (Complex.normSq_nonneg y)]

lemma gramDualTerm_radial (a b : Eisenstein) (W : ℝ → ℂ) {Z : ℝ}
    (hZ : 0 ≤ Z) (h : Eisenstein) :
    gramDualTerm a b W Z h =
      (star (cubicSymbol a h) * cubicSymbol b h) *
        (Real.fourierChar (tracePair (h : ℂ) (1 / (3*traceLambda))) : ℂ) *
          radialDualProfile W (Z * norm h / (27 * norm (a*b))) := by
  rw [gramDualTerm, normProfileFourier_radial]
  congr 2
  simp only [Complex.normSq_mul, Complex.normSq_div, Complex.normSq_ofReal,
    Real.mul_self_sqrt hZ, Complex.normSq_ofNat]
  have hl : Complex.normSq traceLambda = 3 := by
    rw [traceLambda_eq]
    simp [Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt]
  rw [hl]
  dsimp [norm]
  ring

end CubicFirstMoment
end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicGram_MellinDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separated radial Mellin kernels with uniform rapid decay. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem radialDualProfile_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t →
      (1+t)^A * ‖radialDualProfile W t‖ ≤ C := by
  let F := normProfileFourierSchwartz W hW hW'
  let C := 2 ^ (2*A) * (Finset.Iic (2*A,0)).sup
      (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  have hC : 0 ≤ C := by positivity
  refine ⟨C+1, by linarith, ?_⟩
  intro t ht
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (2*A,0)) (k := 2*A) (n := 0) (by rfl) (by rfl) F
      (Real.sqrt t : ℂ)
  simp only [norm_iteratedFDeriv_zero] at hb
  have hn : ‖(Real.sqrt t : ℂ)‖ = Real.sqrt t := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsmall : (1+t)^A ≤ (1+‖(Real.sqrt t : ℂ)‖)^(2*A) := by
    rw [hn, pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]
  have he : F (Real.sqrt t : ℂ) = radialDualProfile W t :=
    normProfileFourierSchwartz_apply W hW hW' _
  have hbound := mul_le_mul_of_nonneg_right hsmall (_root_.norm_nonneg (F (Real.sqrt t : ℂ)))
  rw [he] at hb hbound
  exact (hbound.trans hb).trans (by dsimp [C]; linarith)

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

namespace CubicFirstMoment

lemma frequencyDyad_card_le (j : ℕ) :
    ((frequencyDyad j).card : ℝ) ≤ 36*(2 : ℝ)^j := by
  have hs : frequencyDyad j ⊆ nonzeroNormBall ((2 : ℝ)^(j+1)) := Finset.filter_subset _ _
  have hh : ((frequencyDyad j).card : ℝ) ≤ (nonzeroNormBall ((2 : ℝ)^(j+1))).card := by
    exact_mod_cast Finset.card_le_card hs
  exact hh.trans ((nonzeroNormBall_card_le (by positivity)).trans_eq (by rw [pow_succ]; ring))

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth weights and Mellin twists

The derivative cost below explains why the unweighted published Hecke
estimate continues to give any prescribed logarithmic saving after a
fixed-logarithmic-height norm twist. It is used with `weighted_cubic_prime_bound`.
-/

noncomputable section

namespace CubicFirstMoment

theorem normTwist_eq_mellinPhase (u : ℝ) (a : Eisenstein) :
    normTwist u a = mellinPhase u (norm a) := rfl

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedBinMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeExclusionSavingPowers
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomially bounded exclusion remains negligible compared with
a rough prime coordinate, with every prescribed logarithmic saving. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma exclusion_log_absorption {c d ε : ℝ} (hε : 0 < ε) (hgap : d*ε < c)
    {C : ℝ} (hC : 0 ≤ C) (m k : ℕ) :
    ∀ᶠ L : ℝ in atTop, ∀ Y E : ℝ, 0 ≤ E → E ≤ L^d → L^c ≤ Y →
      C*E^ε*(1+Real.log L)^m ≤ Y/(1+Real.log L)^k := by
  let s := (c-d*ε)/2
  have hs : 0 < s := by dsimp [s]; linarith
  have hexp : d*ε+s < c := by dsimp [s]; linarith
  obtain ⟨K,hK,hlog⟩ := log_power_normalization_bound (m+k) hs
  filter_upwards [eventually_ge_atTop (1:ℝ),eventually_const_mul_rpow_le hexp (C*K)]
    with L hL hbound
  intro Y E hE hEd hY
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log L := by linarith [Real.log_nonneg hL]
  have hlog' : (1+Real.log L)^(m+k) ≤ K*L^s := by
    calc
      _ = L^s*(L^(-s)*(1+Real.log L)^(m+k)) := by
        rw [← mul_assoc,← Real.rpow_add hLp]
        simp
      _ ≤ L^s*K := mul_le_mul_of_nonneg_left (hlog L hL) (Real.rpow_nonneg hLp.le _)
      _ = _ := mul_comm _ _
  apply (le_div_iff₀ (pow_pos hz k)).mpr
  calc
    _ = C*E^ε*(1+Real.log L)^(m+k) := by rw [pow_add]; ring
    _ ≤ C*(L^d)^ε*(K*L^s) := mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hE hEd hε.le) hC) hlog'
      (pow_nonneg hz.le _) (mul_nonneg hC (Real.rpow_nonneg (Real.rpow_nonneg hLp.le _) _))
    _ = (C*K)*L^(d*ε+s) := by
      rw [← Real.rpow_mul hLp.le,Real.rpow_add hLp]
      ring
    _ ≤ L^c := hbound
    _ ≤ Y := hY

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_UniformCoreBlockMoment
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One logarithmic saving on every actual core dyad above the small
core cutoff, obtained by joining the ordinary and exceptional estimates. -/
noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma negative_power_log_saving {ν : ℝ} (hν : 0 < ν) (k : ℕ) :
    ∀ᶠ L : ℝ in atTop, L^(-ν) ≤ 1/(1+Real.log L)^k := by
  have h := exclusion_log_absorption (c := ν) (d := 0) (ε := 1)
    (by norm_num) (by simpa using hν) (C := 1) (by norm_num) k 0
  filter_upwards [h,eventually_ge_atTop (1:ℝ)] with L h hL
  have hp := h (L^ν) 1 (by norm_num) (by simp) le_rfl
  simp only [Real.one_rpow,one_mul,pow_zero,div_one] at hp
  have hz : 0 < (1+Real.log L)^k := pow_pos (by linarith [Real.log_nonneg hL]) _
  rw [Real.rpow_neg (zero_le_one.trans hL),← one_div]
  exact one_div_le_one_div_of_le hz hp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMellinRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two actual coprime Poisson rows are the literal stopped rows at
the shifted norm heights. Divisibility filters and the original interval
support remain in the statement. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedRowCoefficient_phase (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (n : Eisenstein) :
    stoppedRowCoefficient X w z u W selected n =
      stoppedRowCoefficient X w z 0 W selected n*mellinPhase u (norm n) := by
  have hz : mellinPhase 0 (norm n) = 1 := by simp [mellinPhase]
  simp only [stoppedRowCoefficient,normTwist_eq_mellinPhase,hz,mul_one]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The effective frequency after a square-divisor restriction is d*h.
This identity retains vanishing when the divisor meets a conductor. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicSymbol_square_eq_star {b : Eisenstein} (hb : primary b) (d : Eisenstein) :
    cubicSymbol b (d^2) = star (cubicSymbol b d) := by
  rw [cubicSymbol_pow_upper hb]
  by_cases hc : IsCoprime b d
  · have hm : cubicSymbol b d*star (cubicSymbol b d) = 1 := by
      have h := Complex.mul_conj' (cubicSymbol b d)
      simpa only [starRingEnd_apply,norm_cubicSymbol_of_isCoprime hb hc,
        Complex.ofReal_one,one_pow] using h
    have hz : cubicSymbol b d ≠ 0 := by
      intro hz
      rw [hz,zero_mul] at hm
      norm_num at hm
    apply mul_left_cancel₀ hz
    calc
      cubicSymbol b d*(cubicSymbol b d)^2 = (cubicSymbol b d)^3 := by ring
      _ = 1 := cubicSymbol_cube_of_isCoprime hb d hc
      _ = _ := hm.symm
  · rw [cubicSymbol_eq_zero_of_not_isCoprime hb hc]
    simp

lemma divisor_mixed_frequency {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (d h : Eisenstein) :
    mixedSymbol b a (d^2)*(star (cubicSymbol b h)*cubicSymbol a h) =
      star (cubicSymbol b (d*h))*cubicSymbol a (d*h) := by
  simp only [mixedSymbol,cubicSymbol_square_eq_star ha,cubicSymbol_square_eq_star hb,
    cubicSymbol_mul_upper ha,cubicSymbol_mul_upper hb,star_mul,star_star]
  ring

lemma divisor_gram_radial {a b d : Eisenstein} (ha : primary a) (hb : primary b)
    (hd : d ≠ 0) (W : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) (h : Eisenstein) :
    mixedSymbol b a (d^2)*gramDualTerm b a W (A/(norm d)^2) h =
      (star (cubicSymbol b (d*h))*cubicSymbol a (d*h))*
        (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ)*
        radialDualProfile W (A*norm (d*h)/(27*(norm d)^3*norm (b*a))) := by
  rw [gramDualTerm_radial b a W (div_nonneg hA (sq_nonneg _))]
  have he : A/(norm d)^2*norm h/(27*norm (b*a)) =
      A*norm (d*h)/(27*(norm d)^3*norm (b*a)) := by
    simp only [norm_mul_eq]
    have hn : norm d ≠ 0 := (norm_pos_of_ne_zero hd).ne'
    have hab0 : norm (b*a) ≠ 0 := (norm_pos_of_ne_zero
      (mul_ne_zero (primary_ne_zero hb) (primary_ne_zero ha))).ne'
    field_simp
  rw [he]
  calc
    _ = (mixedSymbol b a (d^2)*(star (cubicSymbol b h)*cubicSymbol a h))*
        (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ)*
        radialDualProfile W (A*norm (d*h)/(27*(norm d)^3*norm (b*a))) := by ring
    _ = _ := by rw [divisor_mixed_frequency ha hb]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FinitePoissonRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact identification of a finite Poisson frequency block with the
radial form used in the Mellin estimates, including its scalar. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma poisson_scaled_sqrt {L : ℝ} (hL : 0 < L) (a b : Eisenstein) :
    Real.sqrt ((norm a/L)*(norm b/L)) = Real.sqrt (norm (b*a))/L := by
  have he : (norm a/L)*(norm b/L) = norm (b*a)/L^2 := by
    rw [norm_mul_eq]
    ring
  rw [he,Real.sqrt_div (norm_nonneg _),Real.sqrt_sq hL.le]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorPoissonRadial
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reindexing by the effective frequency d*h for a square-divisor
Poisson block. The additive phase uses the actual inverse on the image. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorFourierPhase_mul {d : Eisenstein} (hd : d ≠ 0) (h : Eisenstein) :
    divisorFourierPhase d (d*h) = (Real.fourierChar (tracePair (h:ℂ) (1/(3*traceLambda))):ℂ) := by
  unfold divisorFourierPhase
  rw [Function.leftInverse_invFun (fun a b he => mul_left_cancel₀ hd he)]

theorem finiteDivisorPoissonContribution_radial {d : Eisenstein} (hd : d ≠ 0)
    (S H : Finset Eisenstein) (hS : ∀ a ∈ S, primary a)
    (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ)
    {A L J : ℝ} (hA : 0 ≤ A) (hL : 0 < L) (hJ : 0 < J) :
    finiteDivisorPoissonContribution d S H β u W A =
      (A/(9*(norm d)^2*L):ℝ)*normCoprimeRadialForm S (H.image (fun h => d*h))
        (fun a => star (β a*mellinPhase u (norm a)))
        (fun a => star (β a*mellinPhase u (norm a)))
        (divisorFourierPhase d) (fun h => norm h/J) (fun a => norm a/L) W
        (A*J/(27*(norm d)^3*L^2)) := by
  unfold finiteDivisorPoissonContribution normCoprimeRadialForm
  rw [Finset.sum_image (fun a _ b _ he => mul_left_cancel₀ hd he)]
  simp only [Finset.mul_sum,divisorFourierPhase_mul hd]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hc : IsCoprime b a ↔ IsCoprime a b := isCoprime_comm
  simp only [hc]
  split_ifs with hab
  · rw [divisor_gram_radial (hS b hb) (hS a ha) hd W hA]
    have harg : A*J/(27*(norm d)^3*L^2)*(norm (d*h)/J)/((norm a/L)*(norm b/L)) =
        A*norm (d*h)/(27*(norm d)^3*norm (a*b)) := by
      simp only [norm_mul_eq]
      field_simp
    rw [harg,poisson_scaled_sqrt hL a b]
    simp only [star_mul,star_star,normTwist_eq_mellinPhase,Complex.ofReal_div,
      Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat]
    have hs : (Real.sqrt (norm (b*a)):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (norm_pos_of_ne_zero (mul_ne_zero (primary_ne_zero (hS b hb))
        (primary_ne_zero (hS a ha))))).ne'
    have hl : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
    have hd' : (norm d:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos_of_ne_zero hd).ne'
    rw [mul_comm b a]
    field_simp
  · simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorAnnulus
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The literal stopped square-divisor Poisson annulus, with principal
frequencies tested at d*h and the exact inverse-square divisor cost. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_divisor_noncube_poisson_annulus
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V B Y A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      0 < Y → 0 ≤ A → ∀ (d : Eisenstein), d ≠ 0 → ∀ (S : Finset Eisenstein),
      (∀ v ∈ S, d*v ≠ 0 ∧ norm (d*v) ≤ B ∧ ¬∃ n : Eisenstein, n^3 = d*v) →
      (∀ v ∈ S, Y ≤ norm (d*v) ∧ norm (d*v) ≤ 2*Y) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      (1+A*Y/(27*(norm d)^3*(b/2)^2))^q*
        ‖finiteDivisorPoissonContribution d (stoppedIntervalSupport ι X (b/2) b e) S
          (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
            (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
              j₀ k₀ h Z Q early)) u Φ A‖ ≤
        K*A*b*B^(1/3:ℝ)/((norm d)^2*(Real.log X)^k) := by
  obtain ⟨K,hK,hr⟩ := stopped_noncube_radial_form (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k q H
  refine ⟨2*K/9,by positivity,?_⟩
  filter_upwards [hr] with X hr
  intro δ b u V B Y A hδ hδone hwidth hb2 hb hbX hV hu hVF hB hBb
    W hW hWi hWd hY hA d hd S hS hSY e he hNe j₀ k₀ h Z Q early hj hR hRL
  let P := stoppedIntervalSupport ι X (b/2) b e
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  let S' := S.image (fun v => d*v)
  let phase := divisorFourierPhase d
  let ρ := A*Y/(27*(norm d)^3*(b/2)^2)
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hbpos : 0 < b := by linarith
  have hN : 0 < b/2 := by positivity
  have hρ : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hS' : ∀ v ∈ S', v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hS w hw
  have hSY' : ∀ v ∈ S', Y ≤ norm v ∧ norm v ≤ 2*Y := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact hSY w hw
  have hphase : ∀ v ∈ S', ‖phase v‖ ≤ 1 := by
    intro v _
    exact (norm_divisorFourierPhase d v).le
  have hrad := hr δ b u V B Y hδ hδone hwidth hb2 hb hbX hV hu hVF hB hBb
    W hW hWi hWd hY S' phase hS' hSY' hphase e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  have heq := finiteDivisorPoissonContribution_radial hd P S
    (fun n hn => (stoppedIntervalSupport_spec X (b/2) b e hn).1)
    β u Φ hA hN hY
  dsimp only [β] at heq
  simp only [←stoppedRowCoefficient_phase] at heq
  rw [heq,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hA (by positivity))]
  have hscalar : A/(9*(norm d)^2*(b/2))*b^2 = (2/9:ℝ)*A*b/(norm d)^2 := by
    field_simp [hbpos.ne',hdN.ne']
  calc
    _ = A/(9*(norm d)^2*(b/2))*((1+ρ)^q*‖normCoprimeRadialForm P S'
        (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n))
        (fun n => star (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n))
        phase (fun v => norm v/Y) (fun n => norm n/(b/2)) Φ ρ‖) := by ring
    _ ≤ A/(9*(norm d)^2*(b/2))*(K*b^2*B^(1/3:ℝ)/(Real.log X)^k) :=
      mul_le_mul_of_nonneg_left hrad (by positivity)
    _ = (A/(9*(norm d)^2*(b/2))*b^2)*K*B^(1/3:ℝ)/(Real.log X)^k := by ring
    _ = _ := by rw [hscalar]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonEntryDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute decay of the literal Poisson summands outside the useful
frequency range. This estimate uses only the smooth compact profile. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
namespace CubicFirstMoment

lemma gramDualTerm_norm_le_radial {a b : Eisenstein} (ha : primary a) (hb : primary b)
    (V : ℝ → ℂ) {A : ℝ} (hA : 0 ≤ A) (h : Eisenstein) :
    ‖gramDualTerm b a V A h‖ ≤ ‖radialDualProfile V (A*norm h/(27*norm (b*a)))‖ := by
  rw [gramDualTerm_radial b a V hA h,norm_mul]
  apply mul_le_of_le_one_left (_root_.norm_nonneg _)
  simp only [norm_mul,norm_star,Circle.norm_coe,mul_one]
  calc
    _ ≤ 1*1 := mul_le_mul (norm_cubicSymbol_le_one hb h) (norm_cubicSymbol_le_one ha h)
      (_root_.norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

theorem poisson_entry_decay (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A L D J : ℝ), 0 < A → 0 < L → L ≤ D → 0 ≤ J →
      ∀ (a b h : Eisenstein), primary a → primary b →
      L ≤ norm a → norm a ≤ D → L ≤ norm b → norm b ≤ D → J ≤ norm h →
      ‖(A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h‖ ≤
        (A/(9*L))*C/(1+A*J/(27*D^2))^m := by
  obtain ⟨C,hC,hdecay⟩ := radialDualProfile_rapidDecay V hV hV' m
  refine ⟨C,hC,?_⟩
  intro A L D J hA hL hLD hJ a b h ha hb hLa haD hLb hbD hJh
  have hD : 0 < D := hL.trans_le hLD
  have hh0 : 0 ≤ norm h := norm_nonneg h
  have hN : 0 < norm (b*a) := norm_pos_of_ne_zero (mul_ne_zero (primary_ne_zero hb) (primary_ne_zero ha))
  have hupper : norm (b*a) ≤ D^2 := by
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul hbD haD (norm_nonneg a) hD.le
  have hlower : L^2 ≤ norm (b*a) := by
    rw [norm_mul_eq,pow_two]
    exact mul_le_mul hLb hLa hL.le (norm_nonneg b)
  have hsqrt : L ≤ Real.sqrt (norm (b*a)) := (Real.le_sqrt hL.le hN.le).mpr hlower
  have harg : A*J/(27*D^2) ≤ A*norm h/(27*norm (b*a)) := by
    apply (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hJh hA.le) (by positivity)).trans
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
  have ht : 0 ≤ A*norm h/(27*norm (b*a)) := by positivity
  have hdec := hdecay _ ht
  have hrad : ‖radialDualProfile V (A*norm h/(27*norm (b*a)))‖ ≤ C/(1+A*J/(27*D^2))^m := by
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+A*J/(27*D^2)) m)).mpr
    have hh := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity)
        (add_le_add (le_rfl : (1:ℝ) ≤ 1) harg) m)
      (_root_.norm_nonneg (radialDualProfile V (A*norm h/(27*norm (b*a)))))
    nlinarith
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (A/(9*L))*(C/(1+A*J/(27*D^2))^m) :=
      mul_le_mul (div_le_div_of_nonneg_left hA.le (by positivity) (by nlinarith))
        ((gramDualTerm_norm_le_radial ha hb V hA.le h).trans hrad)
        (_root_.norm_nonneg _) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonAbsoluteDyad
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute control of arbitrary subsets of a Poisson frequency annulus. -/
noncomputable section
open scoped BigOperators ContDiff
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem finitePoissonContribution_absolute (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A L D J : ℝ), 0 < A → 0 < L → L ≤ D → 0 ≤ J →
      ∀ (S H : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ L ≤ norm a ∧ norm a ≤ D) →
      (∀ h ∈ H, J ≤ norm h) → ∀ (β : Eisenstein → ℂ) (u : ℝ),
      ‖finitePoissonContribution S H β u V A‖ ≤
        C*(A/(9*L))*(H.card:ℝ)*(∑ a ∈ S, ‖β a‖)^2/(1+A*J/(27*D^2))^m := by
  obtain ⟨C,hC,hentry⟩ := poisson_entry_decay V hV hV' m
  refine ⟨C,hC,?_⟩
  intro A L D J hA hL hLD hJ S H hS hH β u
  let E := (A/(9*L))*C/(1+A*J/(27*D^2))^m
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hpair (h a b : Eisenstein) (hh : h ∈ H) (ha : a ∈ S) (hb : b ∈ S) :
      ‖(if IsCoprime a b then
        (β a*normTwist u a)*star (β b*normTwist u b)*
          (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h else 0)‖ ≤
        ‖β a‖*‖β b‖*E := by
    split_ifs
    · have heq : (β a*normTwist u a)*star (β b*normTwist u b)*
          (A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h =
        ((β a*normTwist u a)*star (β b*normTwist u b))*
          ((A/(9*Real.sqrt (norm (b*a))):ℝ)*gramDualTerm b a V A h) := by ring
      rw [heq,norm_mul]
      simp only [norm_mul,norm_star,norm_normTwist,mul_one]
      have hp := hentry A L D J hA hL hLD hJ a b h (hS a ha).1 (hS b hb).1
        (hS a ha).2.1 (hS a ha).2.2 (hS b hb).2.1 (hS b hb).2.2 (hH h hh)
      simp only [norm_mul] at hp
      exact mul_le_mul_of_nonneg_left hp (by positivity)
    · simp only [norm_zero]
      positivity
  unfold finitePoissonContribution
  calc
    _ ≤ ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, ‖β a‖*‖β b‖*E := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro h hh
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro a ha
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun b hb => hpair h a b hh ha hb)
    _ = _ := by
      simp only [← Finset.mul_sum,← Finset.sum_mul,Finset.sum_const,nsmul_eq_mul]
      dsimp [E]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-divisor character can be absorbed into the original
coefficient. Its norm never increases, including at noncoprime inputs. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorTwistedCoefficient_norm_le (d : Eisenstein) (β : Eisenstein → ℂ)
    {a : Eisenstein} (ha : primary a) :
    ‖divisorTwistedCoefficient d β a‖ ≤ ‖β a‖ := by
  rw [divisorTwistedCoefficient,norm_mul,norm_star]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one ha _)

theorem finiteDivisorPoissonContribution_twist (d : Eisenstein)
    (S H : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) (W : ℝ → ℂ) (A : ℝ) :
    finiteDivisorPoissonContribution d S H β u W A =
      finitePoissonContribution S H (divisorTwistedCoefficient d β) u W (A/(norm d)^2) := by
  unfold finiteDivisorPoissonContribution finitePoissonContribution
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : IsCoprime a b
  · simp only [ite_eq_left hab,divisorTwistedCoefficient,star_mul,star_star,mixedSymbol]
    ring
  · simp only [ite_eq_right hab]

theorem finiteDivisorPoissonContribution_absolute (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A L D J : ℝ), 0 < A → 0 < L → L ≤ D → 0 ≤ J →
      ∀ (d : Eisenstein), d ≠ 0 → ∀ (S H : Finset Eisenstein),
      (∀ a ∈ S, primary a ∧ L ≤ norm a ∧ norm a ≤ D) →
      (∀ h ∈ H, J ≤ norm h) → ∀ (β : Eisenstein → ℂ) (u : ℝ),
      ‖finiteDivisorPoissonContribution d S H β u V A‖ ≤
        C*((A/(norm d)^2)/(9*L))*(H.card:ℝ)*(∑ a ∈ S, ‖β a‖)^2/
          (1+(A/(norm d)^2)*J/(27*D^2))^m := by
  obtain ⟨C,hC,hbound⟩ := finitePoissonContribution_absolute V hV hV' m
  refine ⟨C,hC,?_⟩
  intro A L D J hA hL hLD hJ d hd S H hS hH β u
  have hdN := norm_pos_of_ne_zero hd
  rw [finiteDivisorPoissonContribution_twist]
  apply (hbound (A/(norm d)^2) L D J (by positivity) hL hLD hJ S H hS hH
    (divisorTwistedCoefficient d β) u).trans
  have he : (∑ a ∈ S, ‖divisorTwistedCoefficient d β a‖)^2 ≤ (∑ a ∈ S, ‖β a‖)^2 := by
    apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))
    exact Finset.sum_le_sum (fun a ha => divisorTwistedCoefficient_norm_le d β (hS a ha).1)
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorFrequencyDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The dyads used by the divisor Poisson sum are dyads of d*h.
They form an exact finite-fiber partition, with no lost multiplicity. -/
noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorFrequencyDyad_card_le (d : Eisenstein) (hd : d ≠ 0) (j : ℕ) :
    (divisorFrequencyDyad d hd j).card ≤ (frequencyDyad j).card := by
  let H := divisorFrequencyDyad d hd j
  have he : H.image (fun h => d*h) ⊆ frequencyDyad j := by
    intro h hh
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
    exact mem_divisorFrequencyDyad.mp hx
  have hc : (H.image (fun h => d*h)).card = H.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => mul_left_cancel₀ hd h)
  rw [← hc]
  exact Finset.card_le_card he

lemma divisorFrequencyDyad_norm {d : Eisenstein} {hd : d ≠ 0} {j : ℕ} {h : Eisenstein}
    (hh : h ∈ divisorFrequencyDyad d hd j) :
    (2:ℝ)^j/norm d ≤ norm h ∧ norm h ≤ 2*(2:ℝ)^j/norm d := by
  have hn := frequencyDyad_norm (mem_divisorFrequencyDyad.mp hh)
  rw [norm_mul_eq] at hn
  have hdN := norm_pos_of_ne_zero hd
  constructor
  · exact (div_le_iff₀ hdN).mpr (by simpa only [mul_comm] using hn.1)
  · exact (le_div_iff₀ hdN).mpr (by simpa only [mul_comm] using hn.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.DirichletL_CubicDyadicDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

lemma dyadic_rpow (α : ℝ) (j : ℕ) :
    ((2 : ℝ)^j)^α = ((2 : ℝ)^α)^j := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]

lemma decay_le_low (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤ ((2 : ℝ)^α)^j := by
  rw [← dyadic_rpow]
  exact div_le_self (by positivity) (one_le_pow₀ (by
    have : 0 ≤ t * (2 : ℝ)^j := by positivity
    linarith))

lemma decay_le_high (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α - 3))^j := by
  have hk : 0 < (2 : ℝ)^j := by positivity
  calc
    _ ≤ ((2 : ℝ)^j)^α / (t * (2 : ℝ)^j)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 3)
    _ = _ := by
      rw [← dyadic_rpow, Real.rpow_sub hk, Real.rpow_neg ht.le, mul_pow]
      simp only [Real.rpow_ofNat]
      ring

lemma decay_summable (t α : ℝ) (ht : 0 < t) (hα : α < 3) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) := by
  have hr : (2 : ℝ)^(α - 3) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact ((summable_geometric_of_lt_one (by positivity) hr).mul_left (t^(-3 : ℝ))).of_nonneg_of_le
    (fun j => by positivity) (decay_le_high t α ht)

lemma decayConstant_pos (α : ℝ) (hα : 0 < α) (hα3 : α < 3) :
    0 < decayConstant α := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold decayConstant
  positivity

lemma geometric_prefix_le (q : ℝ) (hq : 1 < q) (k : ℕ) :
    (∑ j ∈ Finset.range k, q^j) ≤ q^k / (q - 1) := by
  rw [geom_sum_eq (ne_of_gt hq)]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma decay_tail_le (t α : ℝ) (ht : 0 < t) (hα3 : α < 3) (k : ℕ) :
    (∑' j : ℕ, ((2 : ℝ)^(j+k))^α / (1 + t * (2 : ℝ)^(j+k))^3) ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k * (1 - (2 : ℝ)^(α-3))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^(α-3) := by positivity
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs := summable_geometric_of_lt_one hr0 hr
  calc
    _ ≤ ∑' j : ℕ, t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^(j+k) := by
      apply (decay_summable t α ht hα3).comp_injective (add_left_injective k) |>.tsum_le_tsum
        (fun j => decay_le_high t α ht (j+k))
      exact (hs.comp_injective (add_left_injective k)).mul_left _
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr]
      ring

theorem dyadic_decay_bound (t α : ℝ) (ht : 0 < t) (hα : 0 < α) (hα3 : α < 3) :
    (∑' j : ℕ, ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
      decayConstant α * t^(-α) := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < (1 - (2 : ℝ)^(α-3))⁻¹ := inv_pos.mpr (by linarith)
  by_cases ht1 : 1 ≤ t
  · have hp : t^(-3 : ℝ) ≤ t^(-α) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hh := decay_tail_le t α ht hα3 0
    simp only [Nat.add_zero, pow_zero, mul_one] at hh
    apply hh.trans
    unfold decayConstant
    nlinarith [mul_nonneg (div_nonneg (by positivity : 0 ≤ (2 : ℝ)^α)
      (by linarith : 0 ≤ (2 : ℝ)^α - 1)) (by positivity : 0 ≤ t^(-α)),
      mul_le_mul_of_nonneg_right hp hden.le]
  · have hit : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr (le_of_not_ge ht1)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hit (by norm_num : (1 : ℝ) < 2)
    let k := n+1
    have hk0 : 0 < (2 : ℝ)^k := by positivity
    have hk : t⁻¹ ≤ (2 : ℝ)^k := le_of_lt hn'
    have hk' : (2 : ℝ)^k ≤ 2*t⁻¹ := by
      dsimp [k]
      rw [pow_succ]
      nlinarith
    have hlow : (∑ j ∈ Finset.range k,
        ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
        (2 : ℝ)^α / ((2 : ℝ)^α - 1) * t^(-α) := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, ((2 : ℝ)^α)^j :=
          Finset.sum_le_sum (fun j hj => decay_le_low t α ht j)
        _ ≤ ((2 : ℝ)^α)^k / ((2 : ℝ)^α - 1) := geometric_prefix_le _ hq k
        _ ≤ (2*t⁻¹)^α / ((2 : ℝ)^α - 1) := by
          rw [← dyadic_rpow]
          exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hk0.le hk' hα.le)
            (by linarith)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr ht.le),
            ← Real.rpow_neg_eq_inv_rpow]
          ring
    have hhigh : t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k ≤ t^(-α) := by
      rw [← dyadic_rpow]
      calc
        _ ≤ t^(-3 : ℝ) * (t⁻¹)^(α-3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ht)
            hk (by linarith)) (by positivity)
        _ = _ := by
          rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_add ht]
          congr 1
          ring
    rw [← (decay_summable t α ht hα3).sum_add_tsum_nat_add k]
    have htail := (decay_tail_le t α ht hα3 k).trans
      (mul_le_mul_of_nonneg_right hhigh hden.le)
    unfold decayConstant
    nlinarith

end
end SevenEighths.CubicDyadicDecay

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonTailSum
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily rapid tails of the actual dyadic Poisson envelope. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_tsum_prefix_tail {F : ℕ → ℂ} (n : ℕ) {A B : ℝ}
    (hf : Summable (fun j => F (j+n)))
    (hprefix : ‖∑ j ∈ Finset.range n, F j‖ ≤ A)
    (htail : ‖∑' j : ℕ, F (j+n)‖ ≤ B) : ‖∑' j : ℕ, F j‖ ≤ A+B := by
  have hs : Summable F := hf.comp_nat_add
  rw [← hs.sum_add_tsum_nat_add n]
  exact (norm_add_le _ _).trans (add_le_add hprefix htail)

lemma poisson_dyadic_tail_majorant {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (m n j : ℕ) :
    C*(2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^(m+3) ≤
      (C/(t*(2:ℝ)^n)^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) := by
  have hpow : (2:ℝ)^n ≤ (2:ℝ)^(j+n) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_add_left n j)
  have hbase : t*(2:ℝ)^n ≤ 1+t*(2:ℝ)^(j+n) := by nlinarith
  calc
    _ = (C/(1+t*(2:ℝ)^(j+n))^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) := by
      rw [pow_add]
      field_simp
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hC (by positivity) (pow_le_pow_left₀ (by positivity) hbase m))
      (by positivity)

theorem poisson_dyadic_tail {t C : ℝ} (ht : 0 < t) (hC : 0 ≤ C)
    (m n : ℕ) (F : ℕ → ℂ)
    (hF : ∀ j, ‖F j‖ ≤ C*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3)) :
    Summable (fun j => F (j+n)) ∧
      ‖∑' j : ℕ, F (j+n)‖ ≤
        (C/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  have hs := (SevenEighths.CubicDyadicDecay.decay_summable t 1 ht (by norm_num)).comp_injective
    (add_left_injective n)
  simp only [Real.rpow_one] at hs
  have hm := hs.mul_left (C/(t*(2:ℝ)^n)^m)
  have hb (j : ℕ) : ‖F (j+n)‖ ≤
      (C/(t*(2:ℝ)^n)^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) :=
    (hF (j+n)).trans (poisson_dyadic_tail_majorant ht hC m n j)
  have hsum : Summable (fun j => F (j+n)) := hm.of_norm_bounded hb
  refine ⟨hsum,?_⟩
  have ht' := SevenEighths.CubicDyadicDecay.decay_tail_le t 1 ht (by norm_num) n
  norm_num only [Real.rpow_one,show (1:ℝ)-3 = -2 by norm_num] at ht'
  calc
    _ ≤ ∑' j : ℕ, ‖F (j+n)‖ := norm_tsum_le_tsum_norm (hm.of_nonneg_of_le (fun _ => _root_.norm_nonneg _) hb)
    _ ≤ ∑' j : ℕ, (C/(t*(2:ℝ)^n)^m)*((2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) :=
      Summable.tsum_le_tsum hb (hm.of_nonneg_of_le (fun _ => _root_.norm_nonneg _) hb) hm
    _ = (C/(t*(2:ℝ)^n)^m)*(∑' j : ℕ, (2:ℝ)^(j+n)/(1+t*(2:ℝ)^(j+n))^3) := tsum_mul_left
    _ ≤ _ := by
      have htwo : (2:ℝ)^(-2:ℝ) = 1/4 := by norm_num
      simpa only [htwo,show ((1:ℝ)-1/4)⁻¹ = 4/3 by norm_num] using
        mul_le_mul_of_nonneg_left ht' (show 0 ≤ C/(t*(2:ℝ)^n)^m by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorEnvelope
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An absolute effective-frequency envelope for arbitrary coefficients.
It uses the exact quadratic energy and does not assume a prime convolution. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem arbitrary_divisor_poisson_dyad_energy (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (A N Z u : ℝ) (j : ℕ) (d : Eisenstein) (hd : d ≠ 0),
      0 < A → 0 < N → N ≤ Z →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      H ⊆ divisorFrequencyDyad d hd j →
      ‖finiteDivisorPoissonContribution d S H β u V A‖ ≤
        K*((A/(norm d)^2)/N)*Z*(∑ a ∈ S, ‖β a‖^2)*(2:ℝ)^j /
          (1+A*(2:ℝ)^j/(27*(norm d)^3*Z^2))^m := by
  obtain ⟨C,hC,hbound⟩ := finiteDivisorPoissonContribution_absolute V hV hV' m
  refine ⟨72*C,by positivity,?_⟩
  intro S H β A N Z u j d hd hA hN hNZ hS hH
  have hZ : 0 < Z := hN.trans_le hNZ
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hcard := primary_support_card_le S hZ.le (fun a ha => ⟨(hS a ha).1,(hS a ha).2.2⟩)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun a => ‖β a‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hcs
  have he : (∑ a ∈ S, ‖β a‖)^2 ≤ 18*Z*∑ a ∈ S, ‖β a‖^2 :=
    hcs.trans (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hh : (H.card:ℝ) ≤ 36*(2:ℝ)^j :=
    (show (H.card:ℝ) ≤ (frequencyDyad j).card from by
      exact_mod_cast (Finset.card_le_card hH).trans (divisorFrequencyDyad_card_le d hd j)).trans
        (frequencyDyad_card_le j)
  have hb := hbound A N Z ((2:ℝ)^j/norm d) hA hN hNZ (by positivity) d hd S H hS
    (fun h hh => (divisorFrequencyDyad_norm (hH hh)).1) β u
  have heq : (A/(norm d)^2)*((2:ℝ)^j/norm d)/(27*Z^2) =
      A*(2:ℝ)^j/(27*(norm d)^3*Z^2) := by ring
  rw [heq] at hb
  calc
    _ ≤ C*((A/(norm d)^2)/(9*N))*(36*(2:ℝ)^j)*
        (18*Z*∑ a ∈ S, ‖β a‖^2)/(1+A*(2:ℝ)^j/(27*(norm d)^3*Z^2))^m := by
      apply hb.trans
      gcongr
    _ = _ := by ring

theorem arbitrary_divisor_poisson_energy_tail (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (m : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ) (d : Eisenstein) (hd : d ≠ 0),
      0 < A → 0 < N → N ≤ Z →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ divisorFrequencyDyad d hd j) →
      let t := A/(27*(norm d)^3*Z^2)
      Summable (fun j => finiteDivisorPoissonContribution d S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finiteDivisorPoissonContribution d S (H (j+n)) β u V A‖ ≤
        (K*((A/(norm d)^2)/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^m)*
          (t^(-3:ℝ)*((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹) := by
  obtain ⟨K,hK,hbound⟩ := arbitrary_divisor_poisson_dyad_energy V hV hV' (m+3)
  refine ⟨K,hK,?_⟩
  intro S H β A N Z u n d hd hA hN hNZ hS hH
  have hZ : 0 < Z := hN.trans_le hNZ
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  let t := A/(27*(norm d)^3*Z^2)
  let E := K*((A/(norm d)^2)/N)*Z*∑ a ∈ S, ‖β a‖^2
  have ht : 0 < t := by dsimp [t]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hrow (j : ℕ) : ‖finiteDivisorPoissonContribution d S (H j) β u V A‖ ≤
      E*(2:ℝ)^j/(1+t*(2:ℝ)^j)^(m+3) := by
    have he : t*(2:ℝ)^j = A*(2:ℝ)^j/(27*(norm d)^3*Z^2) := by dsimp [t]; ring
    dsimp only [E]
    rw [he]
    exact hbound S (H j) β A N Z u j d hd hA hN hNZ hS (hH j)
  exact poisson_dyadic_tail ht hE m n
    (fun j => finiteDivisorPoissonContribution d S (H j) β u V A) hrow

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedPoissonTail
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute control after the stopped-row frequency cutoff b^(3/5).
At A≥b^(3/2) this is a positive power beyond the natural Poisson scale;
the inverse powers of A make the bound valid without an upper A limit. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma stopped_poisson_cutoff {Z : ℝ} (_hZ : 0 < Z) (hlarge : 2 ≤ Z^(3/5:ℝ)) :
    ∃ n : ℕ, Z^(3/5:ℝ)/4 ≤ (2:ℝ)^n ∧
      ∀ j : ℕ, j < n → 2*(2:ℝ)^j ≤ Z^(3/5:ℝ) := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near
    ((le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mpr (by simpa using hlarge))
    (by norm_num : (1:ℝ) < 2)
  refine ⟨n,?_,?_⟩
  · have hh := (div_lt_iff₀ (by norm_num : (0:ℝ) < 2)).mp hn'
    rw [pow_succ] at hh
    linarith
  · intro j hj
    have hp : (2:ℝ)^j ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hj.le
    have hn := (le_div_iff₀ (by norm_num : (0:ℝ) < 2)).mp hn
    nlinarith

lemma stopped_poisson_cutoff_scale {Z A J : ℝ} (hZ : 1 ≤ Z)
    (hA : Z^(3/2:ℝ) ≤ A) (hJ : Z^(3/5:ℝ)/4 ≤ J) :
    1/(108*Z^2) ≤ A/(27*Z^2) ∧
      Z^(1/10:ℝ)/108 ≤ (A/(27*Z^2))*J := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have ha : 1 ≤ A := (Real.one_le_rpow hZ (by norm_num)).trans hA
  constructor
  · apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 108*Z^2)
      (by positivity : (0:ℝ) < 27*Z^2)).mpr
    nlinarith [sq_pos_of_pos hz]
  · have hmul := mul_le_mul hA hJ (by positivity : 0 ≤ Z^(3/5:ℝ)/4)
      (zero_le_one.trans ha)
    have hid : Z^(3/2:ℝ)*Z^(3/5:ℝ) = Z^(1/10:ℝ)*Z^2 := by
      rw [← Real.rpow_natCast Z 2,← Real.rpow_add hz,← Real.rpow_add hz]
      norm_num
    have hp : Z^(1/10:ℝ)*Z^2 ≤ 4*(A*J) := by
      rw [← mul_div_assoc,hid] at hmul
      linarith
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 108)).mpr
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hz)).mp
    calc
      _ = Z^(1/10:ℝ)*Z^2 := mul_comm _ _
      _ ≤ 4*(A*J) := hp
      _ = Z^2*((A/(27*Z^2))*J*108) := by field_simp; ring

lemma stopped_poisson_tail_scale {Z A J : ℝ} (hZ : 1 ≤ Z)
    (hA : Z^(3/2:ℝ) ≤ A) (hJ : Z^(3/5:ℝ)/4 ≤ J) :
    let t := A/(27*Z^2)
    A*Z*t^(-3:ℝ)/(t*J)^80 ≤ (108:ℝ)^83*Z^(-2:ℝ) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have ha : 0 < A := (Real.rpow_pos_of_pos hz _).trans_le hA
  let t := A/(27*Z^2)
  change A*Z*t^(-3:ℝ)/(t*J)^80 ≤ _
  have ht : 0 < t := by dsimp [t]; positivity
  have hj : 0 < J := (div_pos (Real.rpow_pos_of_pos hz _) (by norm_num)).trans_le hJ
  have hcut : Z^(1/10:ℝ)/108 ≤ t*J := (stopped_poisson_cutoff_scale hZ hA hJ).2
  have ha2 : Z^3 ≤ A^2 := by
    have hh := pow_le_pow_left₀ (Real.rpow_nonneg hz.le (3/2:ℝ)) hA 2
    have he : (Z^(3/2:ℝ))^2 = Z^3 := by
      rw [← Real.rpow_mul_natCast hz.le]
      norm_num
    rwa [he] at hh
  have hfirst : A*Z*t^(-3:ℝ) ≤ (108:ℝ)^3*Z^4 := by
    have he : A*Z*t^(-3:ℝ) = (27:ℝ)^3*Z^7/A^2 := by
      rw [Real.rpow_neg ht.le,Real.rpow_ofNat]
      dsimp [t]
      field_simp
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos ha)).mpr
    have hm := mul_le_mul_of_nonneg_left ha2 (show 0 ≤ (27:ℝ)^3*Z^4 by positivity)
    have hc : (27:ℝ)^3*Z^4*A^2 ≤ (108:ℝ)^3*Z^4*A^2 := by gcongr; norm_num
    apply (le_trans ?_ hm).trans hc
    ring_nf
    rfl
  have hinv : (t*J)⁻¹ ≤ 108/Z^(1/10:ℝ) := by
    rw [← one_div,div_le_iff₀ (mul_pos ht hj),div_mul_eq_mul_div]
    have hh := (div_le_iff₀ (by norm_num : (0:ℝ) < 108)).mp hcut
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hz _)).mpr
    nlinarith
  have hpower : ((t*J)^80)⁻¹ ≤ (108:ℝ)^80*Z^(-8:ℝ) := by
    rw [← inv_pow]
    apply (pow_le_pow_left₀ (by positivity) hinv 80).trans_eq
    rw [div_pow,← Real.rpow_mul_natCast hz.le]
    norm_num
    simp only [div_eq_mul_inv]
  calc
    _ ≤ ((108:ℝ)^3*Z^4)*((108:ℝ)^80*Z^(-8:ℝ)) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul hfirst hpower (by positivity) (by positivity)
    _ = (108:ℝ)^83*Z^(-4:ℝ) := by
      have he : Z^4*Z^(-8:ℝ) = Z^(-4:ℝ) := by
        rw [← Real.rpow_natCast Z 4,← Real.rpow_add hz]
        norm_num
      rw [show (108:ℝ)^83 = 108^3*108^80 by ring]
      nlinarith only [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorTailPower
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full high-frequency tail at the stopped cutoff, retaining the
explicit polynomial cost of the small square divisor. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma stopped_divisor_tail_scale {Z A J D : ℝ} (hZ : 1 ≤ Z) (hD : 0 < D)
    (hA : Z^(3/2:ℝ) ≤ A) (hJ : Z^(3/5:ℝ)/4 ≤ J) :
    let t := A/(27*D^3*Z^2)
    (A/D^2)*Z*t^(-3:ℝ)/(t*J)^80 ≤ (108:ℝ)^83*D^247*Z^(-2:ℝ) := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hAp : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  have hJp : 0 < J := (div_pos (Real.rpow_pos_of_pos hZp _) (by norm_num)).trans_le hJ
  let t := A/(27*D^3*Z^2)
  let t₀ := A/(27*Z^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₀ : 0 < t₀ := by dsimp [t₀]; positivity
  change (A/D^2)*Z*t^(-3:ℝ)/(t*J)^80 ≤ _
  have he : (A/D^2)*Z*t^(-3:ℝ)/(t*J)^80 =
      D^247*(A*Z*t₀^(-3:ℝ)/(t₀*J)^80) := by
    rw [Real.rpow_neg ht.le,Real.rpow_ofNat,Real.rpow_neg ht₀.le,Real.rpow_ofNat]
    dsimp [t,t₀]
    field_simp
  rw [he]
  exact (mul_le_mul_of_nonneg_left (stopped_poisson_tail_scale hZ hA hJ)
    (pow_nonneg hD.le _)).trans_eq (by ring)

theorem stopped_divisor_poisson_tail_power (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (H : ℕ → Finset Eisenstein)
      (β : Eisenstein → ℂ) (A N Z u : ℝ) (n : ℕ) (d : Eisenstein) (hd : d ≠ 0),
      1 ≤ N → N ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(3/5:ℝ)/4 ≤ (2:ℝ)^n →
      (∀ a ∈ S, primary a ∧ N ≤ norm a ∧ norm a ≤ Z) →
      (∀ j, H j ⊆ divisorFrequencyDyad d hd j) →
      Summable (fun j => finiteDivisorPoissonContribution d S (H (j+n)) β u V A) ∧
      ‖∑' j : ℕ, finiteDivisorPoissonContribution d S (H (j+n)) β u V A‖ ≤
        K*(norm d)^247*Z^(-2:ℝ)*∑ a ∈ S, ‖β a‖^2 := by
  obtain ⟨K,hK,hbound⟩ := arbitrary_divisor_poisson_energy_tail V hV hV' 80
  refine ⟨2*K*(108:ℝ)^83,by positivity,?_⟩
  intro S H β A N Z u n d hd hN hNZ hAlo hcut hS hH
  have hZ : 1 ≤ Z := hN.trans hNZ
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hA : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hAlo
  let t := A/(27*(norm d)^3*Z^2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hb := hbound S H β A N Z u n d hd hA hNp hNZ hS hH
  refine ⟨hb.1,?_⟩
  have hp := stopped_divisor_tail_scale hZ hdN hAlo hcut
  have hgeo : ((2:ℝ)^(-2:ℝ))^n*(1-(2:ℝ)^(-2:ℝ))⁻¹ ≤ 2 := by
    norm_num
    have hh : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  calc
    _ ≤ (K*((A/(norm d)^2)/N)*Z*(∑ a ∈ S, ‖β a‖^2)/(t*(2:ℝ)^n)^80)*
        (t^(-3:ℝ)*2) := hb.2.trans (mul_le_mul_of_nonneg_left
      (by nlinarith [mul_le_mul_of_nonneg_left hgeo (Real.rpow_nonneg ht.le (-3))])
      (by positivity))
    _ = (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*
        ((A/(norm d)^2)*Z*t^(-3:ℝ)/(t*(2:ℝ)^n)^80) := by ring
    _ ≤ (2*K/N)*(∑ a ∈ S, ‖β a‖^2)*((108:ℝ)^83*(norm d)^247*Z^(-2:ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ (2*K)*(∑ a ∈ S, ‖β a‖^2)*((108:ℝ)^83*(norm d)^247*Z^(-2:ℝ)) := by
      gcongr
      exact div_le_self (by positivity) hN
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PoissonDyadicSum
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the annular noncube estimate at its natural Poisson scale. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finite_cubic_dyadic_sum (I : Finset ℕ) (F : ℕ → ℂ) {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 < t)
    (hF : ∀ j ∈ I, ‖F j‖ ≤ C*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3) :
    ‖∑ j ∈ I, F j‖ ≤ C*SevenEighths.CubicDyadicDecay.decayConstant (1/3)*t^(-(1/3:ℝ)) := by
  have hs := SevenEighths.CubicDyadicDecay.decay_summable t (1/3) ht (by norm_num)
  have hb := SevenEighths.CubicDyadicDecay.dyadic_decay_bound t (1/3) ht (by norm_num) (by norm_num)
  calc
    _ ≤ ∑ j ∈ I, ‖F j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ I, C*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := Finset.sum_le_sum hF
    _ = C*(∑ j ∈ I, ((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ C*(∑' j : ℕ, ((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3) :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum I (fun j _ => by positivity)) hC
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC

lemma cubic_poisson_scale {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    A*L*(A/(27*L^2))^(-(1/3:ℝ)) = 3*A^(2/3:ℝ)*L^(5/3:ℝ) := by
  have h27 : (27:ℝ)^(1/3:ℝ) = 3 := by
    rw [show (27:ℝ) = 3^3 by norm_num,← Real.rpow_natCast (3:ℝ) 3,
      ← Real.rpow_mul (by norm_num)]
    norm_num
  rw [Real.div_rpow hA.le (by positivity : 0 ≤ 27*L^2),
    Real.mul_rpow (by norm_num : (0:ℝ) ≤ 27) (sq_nonneg L),
    Real.rpow_neg hA.le,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 27),
    Real.rpow_neg (sq_nonneg L),h27,← Real.rpow_natCast L 2,
    ← Real.rpow_mul hL.le]
  have hAa : A/A^(1/3:ℝ) = A^(2/3:ℝ) := by
    nth_rw 1 [← Real.rpow_one A]
    rw [← Real.rpow_sub hA]
    norm_num
  have hLa : L*L^((2:ℝ)*(1/3)) = L^(5/3:ℝ) := by
    nth_rw 1 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    norm_num
  calc
    _ = 3*(A/A^(1/3:ℝ))*(L*L^((2:ℝ)*(1/3))) := by field_simp; norm_num
    _ = _ := by rw [hAa,hLa]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorNoncubeDyadic
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sum the actual effective-frequency annuli of a square-divisor block.
Their natural scale gives an additional reciprocal divisor norm. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisor_cubic_poisson_scale {A L D : ℝ} (hA : 0 < A) (hL : 0 < L)
    (hD : 0 < D) :
    (A*L/D^2)*(A/(27*D^3*L^2))^(-(1/3:ℝ)) =
      3*A^(2/3:ℝ)*L^(5/3:ℝ)/D := by
  have he : A/(27*D^3*L^2) = (A/(27*L^2))/D^3 := by ring
  have hp : (D^3)^(-(1/3:ℝ)) = D⁻¹ := by
    rw [← Real.rpow_natCast D 3,← Real.rpow_mul hD.le]
    norm_num [Real.rpow_neg_one]
  rw [he,Real.div_rpow (by positivity : 0 ≤ A/(27*L^2)) (by positivity),hp,div_inv_eq_mul]
  calc
    _ = (A*L*(A/(27*L^2))^(-(1/3:ℝ)))/D := by field_simp
    _ = _ := by rw [cubic_poisson_scale hA hL]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorAssembly
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-prefix and absolute-tail assembly for the actual effective
frequency partition of one square divisor. -/
noncomputable section
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem stopped_divisor_prefix_tail (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (b A u L M C : ℝ) (k : ℕ) (d : Eisenstein) (hd : d ≠ 0),
      2 ≤ b → 0 < L → 0 ≤ M → 0 ≤ C → b^(3/2:ℝ) ≤ A →
      2 ≤ b^(3/5:ℝ) → (norm d)^247*b^(-1:ℝ) ≤ 1/L^k →
      (∀ a ∈ S, primary a ∧ b/2 ≤ norm a ∧ norm a ≤ b) →
      (∑ a ∈ S, ‖β a‖^2) ≤ M*b →
      (∀ n : ℕ, (∀ j : ℕ, j < n → 2*(2:ℝ)^j ≤ b^(3/5:ℝ)) →
        ‖∑ j ∈ Finset.range n, finiteDivisorPoissonContribution d S
          ((divisorFrequencyDyad d hd j).filter (fun v => ¬∃ z : Eisenstein, z^3 = d*v))
          β u Φ A‖ ≤ C*A^(2/3:ℝ)*b^(5/3:ℝ)/L^k) →
      ‖divisorNoncubePoissonContribution d hd S β u Φ A‖ ≤
        (C+K*M)*A^(2/3:ℝ)*b^(5/3:ℝ)/L^k := by
  obtain ⟨K,hK,htail⟩ := stopped_divisor_poisson_tail_power Φ hΦ hΦ'
  refine ⟨K,hK,?_⟩
  intro S β b A u L M C k d hd hb hL hM hC hA hlarge hinverse hS henergy hprefix
  have hbp : 0 < b := by linarith
  have hdN : 0 ≤ norm d := norm_nonneg d
  have hb1 : 1 ≤ b := by linarith
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hA
  obtain ⟨n,hn,hn'⟩ := stopped_poisson_cutoff hbp hlarge
  let G := fun j => (divisorFrequencyDyad d hd j).filter (fun v => ¬∃ z : Eisenstein, z^3 = d*v)
  let F := fun j => finiteDivisorPoissonContribution d S (G j) β u Φ A
  have ht : Summable (fun j => F (j+n)) ∧
      ‖∑' j : ℕ, F (j+n)‖ ≤ K*(norm d)^247*b^(-2:ℝ)*(∑ a ∈ S, ‖β a‖^2) :=
    htail S G β A (b/2) b u n d hd (by linarith) (by linarith)
      hA hn hS (fun _ => Finset.filter_subset _ _)
  have hbt : b^(-2:ℝ)*b = b^(-1:ℝ) := by
    nth_rw 2 [←Real.rpow_one b]
    rw [←Real.rpow_add hbp]
    norm_num
  have ht' : ‖∑' j : ℕ, F (j+n)‖ ≤ K*M/L^k := by
    apply ht.2.trans
    calc
      _ ≤ K*(norm d)^247*b^(-2:ℝ)*(M*b) :=
        mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = (K*M)*((norm d)^247*(b^(-2:ℝ)*b)) := by ring
      _ = (K*M)*((norm d)^247*b^(-1:ℝ)) := by rw [hbt]
      _ ≤ (K*M)*(1/L^k) := mul_le_mul_of_nonneg_left hinverse (by positivity)
      _ = _ := by ring
  have hs : ‖∑ j ∈ Finset.range n, F j‖ ≤ C*A^(2/3:ℝ)*b^(5/3:ℝ)/L^k := hprefix n hn'
  have hscale : 1 ≤ A^(2/3:ℝ)*b^(5/3:ℝ) := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow hA1 (by norm_num)) (Real.one_le_rpow hb1 (by norm_num))
  change ‖∑' j : ℕ, F j‖ ≤ _
  apply (norm_tsum_prefix_tail n ht.1 hs ht').trans
  calc
    _ ≤ C*A^(2/3:ℝ)*b^(5/3:ℝ)/L^k+(K*M)*(A^(2/3:ℝ)*b^(5/3:ℝ))/L^k := by
      apply add_le_add le_rfl
      exact div_le_div_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hscale (mul_nonneg hK.le hM))
        (pow_nonneg hL.le _)
    _ = _ := by ring

lemma stopped_small_divisor_inverse {b D : ℝ} (hb : 1 ≤ b) (hD : 0 ≤ D)
    (hDb : D ≤ b^(1/1000:ℝ)) : D^247*b^(-1:ℝ) ≤ b^(-(1/2):ℝ) := by
  have hbp : 0 < b := zero_lt_one.trans_le hb
  calc
    _ ≤ (b^(1/1000:ℝ))^247*b^(-1:ℝ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD hDb 247) (by positivity)
    _ = b^((1/1000:ℝ)*247-1) := by
      rw [←Real.rpow_mul_natCast hbp.le,←Real.rpow_add hbp]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb (by norm_num)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorDyadic
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual stopped effective-frequency annuli sum with a reciprocal
square-divisor norm. The principal-frequency test remains at d*h. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_divisor_noncube_dyadic
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ) (hΦ' : ContDiff ℝ ∞ Φ)
    (k H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) → 0 < A →
      ∀ (I : Finset ℕ) (d : Eisenstein) (Qf : ℕ → Finset Eisenstein), d ≠ 0 →
      (∀ j ∈ I, 2*(2:ℝ)^j ≤ b^(3/5:ℝ)) →
      (∀ j ∈ I, ∀ v ∈ Qf j, d*v ∈ frequencyDyad j ∧ ¬∃ z : Eisenstein, z^3 = d*v) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ‖∑ j ∈ I, finiteDivisorPoissonContribution d
        (stoppedIntervalSupport ι X (b/2) b e) (Qf j)
        (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early)) u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(norm d*(Real.log X)^k) := by
  obtain ⟨K,hK,hannulus⟩ := stopped_divisor_noncube_poisson_annulus (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k 3 H
  let D := SevenEighths.CubicDyadicDecay.decayConstant (1/3)
  have hD : 0 < D := SevenEighths.CubicDyadicDecay.decayConstant_pos _ (by norm_num) (by norm_num)
  refine ⟨3*K*(2:ℝ)^(1/3:ℝ)*D,by positivity,?_⟩
  filter_upwards [hannulus,eventually_ge_atTop (Real.exp 1)] with X hannulus hX
  intro δ b u V A hδ hδone hwidth hb2 hb hbX hV hu hVF W hW hWi hWd hA
    I d Qf hd hI hQf e he hNe j₀ k₀ h Z Q early hj hR hRL
  have hbp : 0 < b := by linarith
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hz : 0 < Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hh
    linarith
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let t := A/(27*(norm d)^3*(b/2)^2)
  let t₀ := A/(27*(norm d)^3*b^2)
  let C₀ := K*A*b*(2:ℝ)^(1/3:ℝ)/((norm d)^2*(Real.log X)^k)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₀ : 0 < t₀ := by dsimp [t₀]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hrow (j : ℕ) (hjI : j ∈ I) :
      ‖finiteDivisorPoissonContribution d S (Qf j) β u Φ A‖ ≤
        C₀*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := by
    have hY : 0 < (2:ℝ)^j := by positivity
    have hh := hannulus δ b u V (2*(2:ℝ)^j) ((2:ℝ)^j) A hδ hδone hwidth
      hb2 hb hbX hV hu hVF
      (by have := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j); linarith)
      (hI j hjI) W hW hWi hWd hY hA.le d hd (Qf j)
      (fun v hv => ⟨(mem_frequencyDyad.mp (hQf j hjI v hv).1).1,
        (frequencyDyad_norm (hQf j hjI v hv).1).2,(hQf j hjI v hv).2⟩)
      (fun v hv => frequencyDyad_norm (hQf j hjI v hv).1)
      e he hNe j₀ k₀ h Z Q early hj hR hRL
    have heq : A*(2:ℝ)^j/(27*(norm d)^3*(b/2)^2) = t*2^j := by dsimp [t]; ring
    rw [heq,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hY.le] at hh
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+t*(2:ℝ)^j) 3)).mpr
    dsimp only [C₀]
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  have hs := finite_cubic_dyadic_sum I _ hC₀ ht hrow
  have htt : t₀ ≤ t := by
    apply div_le_div_of_nonneg_left hA.le (by positivity)
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg b] : (b/2)^2 ≤ b^2) (by positivity)
  have hp := Real.rpow_le_rpow_of_nonpos ht₀ htt (show -(1/3:ℝ) ≤ 0 by norm_num)
  apply (hs.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hC₀ hD.le))).trans_eq
  calc
    _ = (K*(2:ℝ)^(1/3:ℝ)*D/(Real.log X)^k)*
        ((A*b/(norm d)^2)*(A/(27*(norm d)^3*b^2))^(-(1/3:ℝ))) := by
      dsimp [C₀,t₀,D]
      ring
    _ = _ := by rw [divisor_cubic_poisson_scale hA hbp hdN]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorTotal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full early-stopped effective-frequency series for a small square divisor.
The divisor cost in the absolute tail is absorbed by an explicit power bound. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem stopped_divisor_noncube_total_oai
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      b^(3/2:ℝ) ≤ A →
      ∀ (d : Eisenstein) (hd : d ≠ 0), norm d ≤ b^(1/1000:ℝ) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ‖divisorNoncubePoissonContribution d hd (stoppedIntervalSupport ι X (b/2) b e)
        (stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early)) u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
  obtain ⟨K₁,hK₁,hshort⟩ := stopped_divisor_noncube_dyadic (ι := ι) (E := E)
    hpnt hSW hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k H
  obtain ⟨K₂,hK₂,hassemble⟩ := stopped_divisor_prefix_tail Φ hΦ hΦ'
  obtain ⟨M,hM,hcoeff⟩ := stopped_interval_energy (ι := ι) hξ hξz
  refine ⟨K₁+18*K₂*M^2,by positivity,?_⟩
  filter_upwards [hshort,hcoeff,negative_power_log_saving (show 0 < κ/2 by positivity) k,
    (tendsto_rpow_atTop (show 0 < κ*(3/5) by positivity)).eventually_ge_atTop 2,
    eventually_ge_atTop (Real.exp 1)] with X hshort hcoeff hdecay hlargeX hX
  intro δ b u V A hδ hδone hwidth hb2 hb hbX hV hu hVF W hW hWi hWd hAlo
    d hd hdhi e he hNe j₀ k₀ h Z Q early hj hR hRL
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hbp : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hA1 : 1 ≤ A := (Real.one_le_rpow hb1 (by norm_num)).trans hAlo
  have hA : 0 < A := zero_lt_one.trans_le hA1
  have hL : 0 < Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hh
    linarith
  have hlarge : 2 ≤ b^(3/5:ℝ) := by
    apply hlargeX.trans
    rw [Real.rpow_mul hXp.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hXp.le _) hb (by norm_num)
  let P := stoppedIntervalSupport ι X (b/2) b e
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let β := stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  have hp : ∀ a ∈ P, primary a ∧ b/2 ≤ norm a ∧ norm a ≤ b := by
    intro a ha
    have hs := stoppedIntervalSupport_spec X (b/2) b e ha
    exact ⟨hs.1,(Finset.mem_filter.mp ha).2.2.2.1.le,hs.2.2⟩
  have henergy : (∑ a ∈ P, ‖β a‖^2) ≤ (18*M^2)*b := by
    have he := (hcoeff W hW selected 0 (b/2) b e hbp.le hbX).2
    exact he.trans_eq (by ring)
  have hinverse : (norm d)^247*b^(-1:ℝ) ≤ 1/(Real.log X)^k := by
    have ht := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hXp κ) hb
      (by norm_num : (-(1/2):ℝ) ≤ 0)
    rw [←Real.rpow_mul hXp.le] at ht
    have heq : κ*(-(1/2):ℝ) = -(κ/2) := by ring
    rw [heq] at ht
    exact (((stopped_small_divisor_inverse hb1 (norm_nonneg d) hdhi).trans ht).trans hdecay).trans (one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ hL.le (by linarith) _))
  have hd1 : 1 ≤ norm d := one_le_norm hd
  let G := fun j => (divisorFrequencyDyad d hd j).filter
    (fun v => ¬∃ z : Eisenstein, z^3 = d*v)
  have hprefix (n : ℕ) (hn : ∀ j : ℕ, j < n → 2*(2:ℝ)^j ≤ b^(3/5:ℝ)) :
      ‖∑ j ∈ Finset.range n, finiteDivisorPoissonContribution d P (G j) β u Φ A‖ ≤
        K₁*A^(2/3:ℝ)*b^(5/3:ℝ)/(Real.log X)^k := by
    have hh := hshort δ b u V A hδ hδone hwidth hb2 hb hbX hV hu hVF
      W hW hWi hWd hA (Finset.range n) d G hd
      (fun j hj => hn j (Finset.mem_range.mp hj))
      (fun j _ v hv => ⟨mem_divisorFrequencyDyad.mp (Finset.mem_filter.mp hv).1,
        (Finset.mem_filter.mp hv).2⟩)
      e he hNe j₀ k₀ h Z Q early hj hR hRL
    exact hh.trans (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (pow_nonneg hL.le _) hd1))
  have hfinal := hassemble P β b A u (Real.log X) (18*M^2) K₁ k d hd
    hb2 hL (by positivity) hK₁.le hAlo hlarge hinverse hp henergy hprefix
  exact hfinal.trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.stopped_divisor_noncube_total_oai.{u_1} := @OAI.CubicFirstMoment.stopped_divisor_noncube_total_oai.{u_1}
