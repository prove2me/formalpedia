-- Prove2me | solution 1 for OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:32:33.935334+00:00
-- url     : https://prove2.me/submissions/4ed796a2-0c55-492e-b44c-baf3c6b43137
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A018
import Definitions.Def_OAIQ096A019
import Theorems.Thm_OAI_CubicFirstMoment_bounded_cubic_moment

section
-- module Solutions.OAIQ096_CM.Compat
attribute [-instance] _root_.instMeasurableSpace
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `Finset.sum_le_sum_of_injOn`; ours has no such lemma (LipschitzHilbert, oaiq-090). -/
theorem sum_le_sum_of_injOn {ι κ M : Type*} [DecidableEq κ] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedAddMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M} {g : κ → M} (e : ι → κ)
    (he : Set.InjOn e s) (hest : s.image e ⊆ t) (hf : ∀ i ∈ s, f i ≤ g (e i))
    (hg : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) : ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc ∑ i ∈ s, f i ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hf
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ ∑ j ∈ t, g j := Finset.sum_le_sum_of_subset_of_nonneg hest hg
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma norm_le_of_dvd {a b : Eisenstein} (hb : b ≠ 0) (hd : a ∣ b) :
    norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := hd
  have hc : c ≠ 0 := by intro h; simp [h] at hb
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg a) (one_le_norm hc)

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_InnerExtension
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full inner cube covers and sharp coefficient extension bounds. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma complex_norm_sum_sq_le {ι : Type*} (I : Finset ι) (v : ι → ℂ) :
    ‖∑ i ∈ I, v i‖^2 ≤ (I.card : ℝ)*∑ i ∈ I, ‖v i‖^2 := by
  have ht := norm_sum_le I v
  have hc := Finset.sum_mul_sq_le_sq_mul_sq I (fun _ => (1 : ℝ)) (fun i => ‖v i‖)
  simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
  exact (pow_le_pow_left₀ (_root_.norm_nonneg _) ht 2).trans hc

lemma complex_mass_sum_sq_le {ι κ : Type*} (I : Finset ι) (P : Finset κ)
    (F : κ → ι → ℂ) :
    (∑ a ∈ P, ‖∑ i ∈ I, F a i‖^2) ≤
      (I.card : ℝ)*∑ i ∈ I, ∑ a ∈ P, ‖F a i‖^2 := by
  calc
    _ ≤ ∑ a ∈ P, (I.card : ℝ)*∑ i ∈ I, ‖F a i‖^2 :=
      Finset.sum_le_sum (fun a _ => complex_norm_sum_sq_le I (F a))
    _ = _ := by rw [← Finset.mul_sum,Finset.sum_comm]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSymmetry
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar factors on the symmetry line in the primitive Hecke
functional equation. These identities apply also to fixed infinity type.
They keep conductor-dependent phases outside the dual polynomial. -/

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma norm_heckeGammaRatio {k : ℝ} (hk : 0 ≤ k) (t : ℝ) :
    ‖heckeGammaRatio k t‖ = 1 := by
  have hre : 0 < (((k+1/2:ℝ):ℂ) + (t:ℂ)*Complex.I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    linarith
  have hne := Complex.Gamma_ne_zero_of_re_pos hre
  have hc : ((k+1/2:ℝ):ℂ) - (t:ℂ)*Complex.I =
      starRingEnd ℂ (((k+1/2:ℝ):ℂ) + (t:ℂ)*Complex.I) := by
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg,
      sub_eq_add_neg]
  rw [heckeGammaRatio, hc, Complex.Gamma_conj, norm_div, Complex.norm_conj]
  exact div_self (norm_ne_zero_iff.mpr hne)

lemma norm_heckeSymmetryFactor {ε : ℂ} (hε : ‖ε‖ = 1)
    (D Z k t τ : ℝ) (hk : 0 ≤ k) :
    ‖heckeSymmetryFactor ε D Z k t τ‖ = 1 := by
  simp [heckeSymmetryFactor, hε, norm_heckeGammaRatio hk]

end CubicFirstMoment

end

end OAI
end

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

lemma hecke_conductor_phase {A : ℝ} (hA : 0 < A) (t τ : ℝ) :
    (A:ℂ)^(1-2*((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)) =
      mellinPhase (t-τ) (A^2) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA.ne'),
    ← Complex.ofReal_log hA.le]
  unfold mellinPhase
  rw [Real.log_pow]
  congr 1
  push_cast
  ring

lemma hecke_scale_phase {Z : ℝ} (hZ : 0 < Z) (τ : ℝ) :
    (Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I) =
      (Real.sqrt Z:ℂ)*mellinPhase τ Z := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hZ.ne'),
    ← Complex.ofReal_log hZ.le,Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hZ,Complex.ofReal_exp]
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contour shifting for the Mellin integrals in the smooth Hecke sum.
The horizontal edges are kept explicit until a uniform decay bound is
available; no functional equation or dual-sum estimate is assumed here. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace CubicFirstMoment

lemma mellin_rectangle_identity {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (T : ℝ) :
    (∫ x in a..b, f (x - (T : ℂ) * Complex.I)) -
      (∫ x in a..b, f (x + (T : ℂ) * Complex.I)) +
      Complex.I * (∫ y in -T..T, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y in -T..T, f (a + (y : ℂ) * Complex.I)) = 0 := by
  have hd := hf.mono (show
      (Set.uIcc a b ×ℂ Set.uIcc (-T) T) ⊆ closedVerticalStrip a b from by
    intro z hz
    simpa only [Set.uIcc_of_le hab, Set.mem_preimage, Set.mem_Icc,
      closedVerticalStrip, Set.mem_ofPred_eq] using hz.1)
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    ((a : ℂ) - (T : ℂ) * Complex.I) ((b : ℂ) + (T : ℂ) * Complex.I)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero,
    sub_zero, add_zero, zero_sub, mul_one, zero_add] at h
  simpa only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, Complex.sub_im, Complex.add_im, mul_zero, zero_mul,
    sub_zero, add_zero, zero_sub, mul_one, zero_add, Complex.ofReal_neg,
    neg_mul, add_neg_cancel, sub_self, smul_eq_mul, sub_eq_add_neg] using h hd

/-- Vertical Mellin integrals agree after shifting through a holomorphic
strip, once both horizontal edges vanish. -/
theorem mellin_contour_shift {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (ha : Integrable (fun y : ℝ => f (a + (y : ℂ) * Complex.I)))
    (hb : Integrable (fun y : ℝ => f (b + (y : ℂ) * Complex.I)))
    (hTop : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + (T : ℂ) * Complex.I))
      atTop (𝓝 0))
    (hBot : Tendsto (fun T : ℝ => ∫ x in a..b, f (x - (T : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hia := intervalIntegral_tendsto_integral ha
    tendsto_neg_atTop_atBot tendsto_id
  have hib := intervalIntegral_tendsto_integral hb
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hBot.sub hTop).add (hib.const_mul Complex.I)).sub
    (hia.const_mul Complex.I)
  have hz : (0 : ℂ) + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
      Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
    have hz' : 0 - 0 + Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) = 0 := by
      apply tendsto_nhds_unique hlim
      apply tendsto_const_nhds.congr'
      exact Filter.Eventually.of_forall (fun T => (mellin_rectangle_identity hab f hf T).symm)
    simpa only [sub_self] using hz'
  have he : Complex.I * (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      Complex.I * (∫ y : ℝ, f (b + (y : ℂ) * Complex.I)) := by
    linear_combination -hz
  exact mul_left_cancel₀ Complex.I_ne_zero he

/-- A common decaying majorant supplies both horizontal limits. This is
the form used for a rapidly decreasing Mellin transform times an
L-function of polynomial growth. -/
theorem mellin_contour_shift_of_majorant {a b : ℝ} (hab : a ≤ b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (closedVerticalStrip a b))
    (H : ℝ → ℝ) (hH : Integrable H)
    (hHtop : Tendsto H atTop (𝓝 0)) (hHbot : Tendsto H atBot (𝓝 0))
    (hbound : ∀ x ∈ Icc a b, ∀ t : ℝ, ‖f (x + (t : ℂ) * Complex.I)‖ ≤ H t) :
    (∫ y : ℝ, f (a + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ, f (b + (y : ℂ) * Complex.I) := by
  have hline (x : ℝ) (hx : x ∈ Icc a b) :
      Integrable (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) := by
    have hc : Continuous (fun y : ℝ => f (x + (y : ℂ) * Complex.I)) :=
      hf.continuousOn.comp_continuous
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
        (by intro y; simpa [closedVerticalStrip] using hx)
    exact hH.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall (hbound x hx))
  have hedge (t : ℝ) :
      ‖∫ x in a..b, f (x + (t : ℂ) * Complex.I)‖ ≤ H t * |b-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    apply hbound x
    rw [Set.uIoc_of_le hab] at hx
    exact ⟨hx.1.le,hx.2⟩
  apply mellin_contour_shift hab f hf
    (hline a ⟨le_rfl,hab⟩) (hline b ⟨hab,le_rfl⟩)
  · exact squeeze_zero_norm hedge (by simpa using hHtop.mul_const |b-a|)
  · have he : Tendsto (fun T : ℝ => ∫ x in a..b, f (x + ((-T : ℝ) : ℂ) * Complex.I))
        atTop (𝓝 0) :=
      squeeze_zero_norm (fun T => hedge (-T))
        (by simpa using (hHbot.comp tendsto_neg_atTop_atBot).mul_const |b-a|)
    simpa only [Complex.ofReal_neg, neg_mul, sub_eq_add_neg] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSmooth
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Analytic properties of the actual compactly supported smooth norm
weights. Passing to logarithmic coordinates realizes every vertical
Mellin line as a Schwartz Fourier transform. -/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

lemma mellinVerticalSchwartz_apply (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ t : ℝ) :
    mellinVerticalSchwartz W hW hpos hsm σ t = mellin W (σ + (t : ℂ)*Complex.I) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
    Complex.add_im, Complex.mul_im, mul_one, zero_add]
  rfl

theorem smooth_mellin_vertical_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin W) σ := by
  change Integrable (fun t : ℝ => mellin W (σ + (t : ℂ)*Complex.I))
  have hi : Integrable (mellinVerticalSchwartz W hW hpos hsm σ) :=
    (mellinVerticalSchwartz W hW hpos hsm σ).integrable
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  exact (mellinVerticalSchwartz_apply W hW hpos hsm σ t).symm

theorem smooth_mellin_vertical_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (1+|t|)^A * ‖mellin W (σ + (t : ℂ)*Complex.I)‖ ≤ C := by
  let F := mellinVerticalSchwartz W hW hpos hsm σ
  let C := 2^A * (Finset.Iic (A,0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  refine ⟨C+1,by dsimp [C]; positivity,?_⟩
  intro t
  have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl F t
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hb
  rw [← mellinVerticalSchwartz_apply W hW hpos hsm σ t]
  exact hb.trans (by dsimp [C]; linarith)

/-- The Mellin inversion used for a single norm weight, with convergence
and the vertical integral discharged from its actual smooth support. -/
theorem smooth_mellin_inversion (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    {x : ℝ} (hx : 0 < x) : mellinInv σ (mellin W) x = W x :=
  mellinInv_mellin_eq σ W hx (smooth_mellin_convergent W hW hpos hsm.continuous σ)
    (smooth_mellin_vertical_integrable W hW hpos hsm σ) hsm.continuous.continuousAt

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute sum-integral interchange for the full norm Dirichlet series
in Mellin inversion. No smooth-duality formula is an input. -/

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CubicFirstMoment

/-- The complete smoothed series has the exact Mellin representation on
any line of absolute convergence of its norm Dirichlet series. -/
theorem smooth_mellin_series {ι : Type*} [Countable ι]
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i, 0 < N i)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Set.Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (σ : ℝ)
    (habs : Summable (fun i => ‖a i‖*(N i)^(-σ)))
    {Z : ℝ} (hZ : 0 < Z) :
    (∑' i, a i*W (N i/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
        normDirichletSeries a N (σ+(τ:ℂ)*Complex.I) := by
  let s (τ : ℝ) : ℂ := σ+(τ:ℂ)*Complex.I
  let F (i : ι) (τ : ℝ) : ℂ :=
    (a i*(N i:ℂ)^(-s τ))*((Z:ℂ)^(s τ)*mellin W (s τ))
  have hsre (τ : ℝ) : (s τ).re = σ := by simp [s]
  have hsnre (τ : ℝ) : (-s τ).re = -σ := by simp [hsre]
  have hnorm (i : ι) (τ : ℝ) : ‖F i τ‖ =
      (‖a i‖*(N i)^(-σ))*Z^σ*‖mellin W (s τ)‖ := by
    simp only [F,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (hN i),
      Complex.norm_cpow_eq_rpow_re_of_pos hZ,hsre,hsnre]
    ring
  have hm : Integrable (fun τ => mellin W (s τ)) :=
    smooth_mellin_vertical_integrable W hW hpos hsm σ
  have hFi (i : ι) : Integrable (F i) := by
    have hn0 : (N i:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hN i).ne'
    have hz0 : (Z:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
    have : NeZero (N i:ℂ) := ⟨hn0⟩
    have : NeZero (Z:ℂ) := ⟨hz0⟩
    have hs : Continuous s := by dsimp [s]; fun_prop
    have hc : Continuous (F i) :=
      (continuous_const.mul ((differentiable_const_cpow_of_neZero _).continuous.comp hs.neg)).mul
        (((differentiable_const_cpow_of_neZero _).continuous.comp hs).mul
          ((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp hs))
    exact (hm.norm.const_mul ((‖a i‖*(N i)^(-σ))*Z^σ)).mono'
      hc.aestronglyMeasurable (Filter.Eventually.of_forall (fun τ => (hnorm i τ).le))
  have hsum : Summable (fun i => ∫ τ : ℝ, ‖F i τ‖) := by
    have he (i : ι) : (∫ τ : ℝ, ‖F i τ‖) =
        (‖a i‖*(N i)^(-σ))*(Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖)) := by
      simp_rw [hnorm]
      rw [integral_const_mul]
      ring
    simpa only [he] using habs.mul_right (Z^σ*(∫ τ : ℝ, ‖mellin W (s τ)‖))
  have hi := integral_tsum_of_summable_integral_norm hFi hsum
  have hsingle (i : ι) : a i*W (N i/Z) =
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := by
    rw [← smooth_mellin_inversion W hW hpos hsm σ (div_pos (hN i) hZ),mellinInv]
    simp only [RCLike.real_smul_eq_coe_mul]
    rw [← mul_assoc,mul_comm (a i),mul_assoc,← integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards with τ
    rw [mellin_scale_cpow (hN i) hZ]
    dsimp [F,s]
    ring
  calc
    _ = ∑' i, ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F i τ) := tsum_congr hsingle
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∑' i, ∫ τ : ℝ, F i τ) := tsum_mul_left
    _ = ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, ∑' i, F i τ) := by rw [hi]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with τ
      simp only [F,normDirichletSeries]
      rw [tsum_mul_right]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealExponentOf_norm {a : Eisenstein} (ha : a ≠ 0) :
    idealExponentNorm (idealExponentOf a) = norm a := by
  unfold idealExponentNorm
  rw [associated_normNat (idealExponentOf_associated ha), normNat_cast]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealMellinSeries
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absolute convergence and Mellin inversion for the complete ideal
series. Prime-exponent vectors include all nonzero ideals, including
the ramified prime; no Euler factor is silently removed. -/

noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

/-- The complete ideal character sum, with its full Dirichlet series,
has the Mellin representation on every line to the right of one. -/
theorem ideal_smooth_mellin (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Set.Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {σ Z : ℝ} (hσ : 1 < σ) (hZ : 0 < Z) :
    (∑' ν, χ ν*W (idealExponentNorm ν/Z)) = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ τ : ℝ, mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
        normDirichletSeries χ idealExponentNorm (σ+(τ:ℂ)*Complex.I) :=
  smooth_mellin_series χ idealExponentNorm idealExponentNorm_pos W hW hpos hsm σ
    (summable_ideal_character_weight hσ χ hχ) hZ

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinStrip
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform rapid Mellin decay on a fixed closed real strip. The bound
comes from the actual compact logarithmic support, not an additional
analytic input. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology SchwartzMap ContDiff FourierTransform

namespace CubicFirstMoment

private lemma exp_linear_deriv_bound {M R σ u : ℝ} (hM : 0 ≤ M)
    (hσ : |σ| ≤ M) (hu : |u| ≤ R) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun v : ℝ => Real.exp (-σ*v)) u‖ ≤
      M^n * Real.exp (M*R) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_exp_const_mul]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_neg,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hσ n) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  calc
    -σ*u ≤ |-σ*u| := le_abs_self _
    _ = |σ| * |u| := by rw [abs_mul,abs_neg]
    _ ≤ M*R := mul_le_mul hσ hu (abs_nonneg _) hM

private lemma mellinLogSchwartz_eq_smul (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) :
    (mellinLogSchwartz W hW hpos hsm σ : ℝ → ℂ) =
      fun u => Real.exp (-σ*u) • mellinLogSchwartz W hW hpos hsm 0 u := by
  ext u
  simp [mellinLogSchwartz_apply]

theorem mellinLogSchwartz_seminorm_uniform (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ)
    (k n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, |σ| ≤ M →
      SchwartzMap.seminorm ℝ k n (mellinLogSchwartz W hW hpos hsm σ) ≤ C := by
  let G := mellinLogSchwartz W hW hpos hsm 0
  obtain ⟨R₀,hR₀⟩ := (logPullback_compact W hW hpos).isCompact.isBounded.exists_norm_le
  let R := max R₀ 1
  let M' := max M 0
  let B := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    (M'^i * Real.exp (M'*R)) * SchwartzMap.seminorm ℝ 0 (n-i) G
  have hR : 0 ≤ R := le_trans zero_le_one (le_max_right _ _)
  have hM : 0 ≤ M' := le_max_right _ _
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => by positivity)
  refine ⟨R^k*B, by positivity, ?_⟩
  intro σ hσ
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ R
  · have he : ContDiff ℝ ∞ (fun v : ℝ => Real.exp (-σ*v)) := by fun_prop
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) he (G.smooth ⊤) u
      (n := n) (mod_cast le_top)
    have hg (i : ℕ) : ‖iteratedFDeriv ℝ i G u‖ ≤ SchwartzMap.seminorm ℝ 0 i G := by
      simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm ℝ 0 i G u
    have hb : ‖iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u‖ ≤ B := by
      rw [mellinLogSchwartz_eq_smul W hW hpos hsm σ]
      apply hd.trans
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (exp_linear_deriv_bound hM (hσ.trans (le_max_left _ _)) hu i) (by positivity)
      · exact hg (n-i)
      · positivity
      · positivity
    simpa only [Real.norm_eq_abs] using
      mul_le_mul (pow_le_pow_left₀ (by positivity : 0 ≤ |u|) hu k) hb
        (by positivity) (by positivity)
  · have hz : iteratedFDeriv ℝ n (mellinLogSchwartz W hW hpos hsm σ) u = 0 := by
      by_contra hn
      have hs := support_iteratedFDeriv_subset (𝕜 := ℝ)
        (f := mellinLogSchwartz W hW hpos hsm σ) n hn
      have hs' : u ∈ tsupport (fun v : ℝ => W (Real.exp (-v))) :=
        tsupport_smul_subset_right (fun v : ℝ => Real.exp (-σ*v))
          (fun v : ℝ => W (Real.exp (-v))) hs
      have hb : |u| ≤ R₀ := by simpa only [Real.norm_eq_abs] using hR₀ u hs'
      exact hu (hb.trans (le_max_left _ _))
    rw [hz,norm_zero,mul_zero]
    positivity

theorem mellinVertical_family_bounded (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) :
    Bornology.IsVonNBounded ℝ
      ((fun σ => mellinVerticalSchwartz W hW hpos hsm σ) '' {σ | |σ| ≤ M}) := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun σ => mellinLogSchwartz W hW hpos hsm σ
  have hb : Bornology.IsVonNBounded ℝ (f '' {σ | |σ| ≤ M}) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,h⟩ := mellinLogSchwartz_seminorm_uniform W hW hpos hsm M i.1 i.2
    exact ⟨C+1,by linarith,fun σ hσ => (h σ hσ).trans_lt (by linarith)⟩
  let L : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.compCLM ℝ (by
      simp only [div_eq_mul_inv]
      fun_prop : (fun t : ℝ => t/(2*Real.pi)).HasTemperateGrowth)
      mellin_frequency_growth).comp (SchwartzMap.fourierTransformCLM ℝ)
  convert hb.image L using 1
  all_goals try with_reducible_and_instances rfl
  rw [← Set.image_comp]
  rfl

theorem smooth_mellin_strip_decay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (M : ℝ) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, |σ| ≤ M → ∀ t : ℝ,
      (1+|t|)^A * ‖mellin W (σ + (t : ℂ)*Complex.I)‖ ≤ C := by
  have hb := mellinVertical_family_bounded W hW hpos hsm M
  obtain ⟨C,hC,h⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_finset_seminorm_bounded
      (fun σ => mellinVerticalSchwartz W hW hpos hsm σ) |>.mp hb (Finset.Iic (A,0))
  refine ⟨2^A*C,by positivity,?_⟩
  intro σ hσ t
  have hp := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (A,0)) (k := A) (n := 0) le_rfl le_rfl
      (mellinVerticalSchwartz W hW hpos hsm σ) t
  simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,mellinVerticalSchwartz_apply] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (h σ hσ).le (by positivity))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinHeckeContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The contour step for the full smooth character sum. Polynomial
vertical growth is an analytic property of the L-function; the decay,
integrability and vanishing edges are derived for the actual weight. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace CubicFirstMoment

lemma mellinEdgeMajorant_integrable (C : ℝ) : Integrable (mellinEdgeMajorant C) := by
  have hi : Integrable (fun t : ℝ => (1+‖t‖)^(-(2:ℝ))) :=
    integrable_one_add_norm (by norm_num)
  convert hi.const_mul C using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  rw [mellinEdgeMajorant, Real.rpow_neg (by positivity), Real.rpow_ofNat,
    Real.norm_eq_abs, div_eq_mul_inv]

lemma mellinEdgeMajorant_tendsto (C : ℝ) :
    Tendsto (mellinEdgeMajorant C) atTop (𝓝 0) ∧
      Tendsto (mellinEdgeMajorant C) atBot (𝓝 0) := by
  have h (l : Filter ℝ) (hl : Tendsto (fun t : ℝ => |t|) l atTop) :
      Tendsto (mellinEdgeMajorant C) l (𝓝 0) := by
    change Tendsto (fun t : ℝ => C/(1+|t|)^2) l (𝓝 0)
    have hp : Tendsto (fun t : ℝ => (1+|t|)⁻¹) l (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_mono (fun t => by linarith) hl)
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0),
      mul_zero] using (hp.pow 2).const_mul C
  exact ⟨h atTop tendsto_abs_atTop_atTop,h atBot tendsto_abs_atBot_atTop⟩

lemma norm_mellinHecke_integrand_le (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (hZ : 1 ≤ Z) (t : ℝ)
    (L : ℂ → ℂ) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hL : ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖L (σ + ((τ-t : ℝ) : ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖mellin W (σ+(τ:ℂ)*Complex.I) * (Z:ℂ)^(σ+(τ:ℂ)*Complex.I) *
          L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤ mellinEdgeMajorant K τ := by
  obtain ⟨Cw,hCw,hdecay⟩ := smooth_mellin_strip_decay W hW hpos hsm (|a|+|b|) (N+2)
  let B := Z^b*C*(1+|t|)^N
  have hB : 0 ≤ B := by positivity
  refine ⟨B*Cw,by positivity,?_⟩
  intro σ hσ τ
  have hσabs : |σ| ≤ |a|+|b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a,abs_nonneg b,hσ.1]
    · linarith [le_abs_self b,abs_nonneg a,hσ.2]
  have hscale : ‖(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)‖ ≤ Z^b := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < Z)]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hZ hσ.2
  have hshift : (1+|τ-t|)^N ≤ (1+|t|)^N*(1+|τ|)^N := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hd := abs_sub_le τ 0 t
    simp only [sub_zero,zero_sub,abs_neg] at hd
    nlinarith [mul_nonneg (abs_nonneg τ) (abs_nonneg t)]
  have hL' : ‖L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤
      C*((1+|t|)^N*(1+|τ|)^N) :=
    (hL σ hσ τ).trans (mul_le_mul_of_nonneg_left hshift hC)
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|τ|)^2)).mpr
  calc
    _ ≤ (‖mellin W (σ+(τ:ℂ)*Complex.I)‖ * Z^b *
        (C*((1+|t|)^N*(1+|τ|)^N)))*(1+|τ|)^2 := by
      rw [norm_mul,norm_mul]
      gcongr
    _ = B*((1+|τ|)^(N+2)*‖mellin W (σ+(τ:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      dsimp [B]
      ring
    _ ≤ B*Cw := mul_le_mul_of_nonneg_left (hdecay σ hσabs τ) hB

/-- Shifting the full Mellin integrand crosses no pole when the
nonprincipal L-function is entire. The weight supplies every required
decay and convergence assertion. -/
theorem mellinHecke_contour_shift (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {a b Z : ℝ} (hab : a ≤ b) (hZ : 1 ≤ Z) (t : ℝ)
    (L : ℂ → ℂ) (hLd : Differentiable ℂ L) {C : ℝ} (hC : 0 ≤ C) (N : ℕ)
    (hL : ∀ σ ∈ Icc a b, ∀ τ : ℝ,
      ‖L (σ+((τ-t : ℝ):ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^N) :
    (∫ τ : ℝ, mellin W (a+(τ:ℂ)*Complex.I) * (Z:ℂ)^(a+(τ:ℂ)*Complex.I) *
      L (a+((τ-t : ℝ):ℂ)*Complex.I)) =
    ∫ τ : ℝ, mellin W (b+(τ:ℂ)*Complex.I) * (Z:ℂ)^(b+(τ:ℂ)*Complex.I) *
      L (b+((τ-t : ℝ):ℂ)*Complex.I) := by
  let f : ℂ → ℂ := fun s => mellin W s*(Z:ℂ)^s*L (s-(t:ℂ)*Complex.I)
  have hZn : (Z:ℂ) ≠ 0 := by exact_mod_cast (show Z ≠ 0 by linarith)
  have : NeZero (Z:ℂ) := ⟨hZn⟩
  have hf : Differentiable ℂ f :=
    ((smooth_mellin_entire W hW hpos hsm.continuous).mul
      (differentiable_const_cpow_of_neZero _)).mul
      (hLd.comp (differentiable_id.sub_const _))
  obtain ⟨K,_,hbound⟩ := norm_mellinHecke_integrand_le W hW hpos hsm hZ t L hC N hL
  have heq (σ τ : ℝ) : f (σ+(τ:ℂ)*Complex.I) =
      mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        L (σ+((τ-t : ℝ):ℂ)*Complex.I) := by
    dsimp [f]
    congr 2
    push_cast
    ring
  have hshift := mellin_contour_shift_of_majorant hab f hf.differentiableOn
    (mellinEdgeMajorant K) (mellinEdgeMajorant_integrable K)
    (mellinEdgeMajorant_tendsto K).1 (mellinEdgeMajorant_tendsto K).2
    (by intro σ hσ τ; rw [heq]; exact hbound σ hσ τ)
  simpa only [heq] using hshift

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinDualTail
attribute [-instance] _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual far-left dual-series tails. The integer-line Gamma estimate
and smooth Mellin decay provide the analytic bounds. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma shifted_power_le (N : ℕ) (τ t : ℝ) :
    (1+|τ-t|)^N ≤ (1+|t|)^N*(1+|τ|)^N := by
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hd := abs_sub_le τ 0 t
  simp only [sub_zero,zero_sub,abs_neg] at hd
  nlinarith [mul_nonneg (abs_nonneg τ) (abs_nonneg t)]

lemma mellin_polynomial_majorant (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W) (σ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t τ : ℝ,
      ‖mellin W (σ+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^N ≤
        mellinEdgeMajorant (C*(1+|t|)^N) τ := by
  obtain ⟨C,hC,hdecay⟩ := smooth_mellin_vertical_decay W hW hpos hsm σ (N+2)
  refine ⟨C,hC,?_⟩
  intro t τ
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|τ|)^2)).mpr
  calc
    _ ≤ (‖mellin W (σ+(τ:ℂ)*Complex.I)‖*
        ((1+|t|)^N*(1+|τ|)^N))*(1+|τ|)^2 := by
      gcongr
      exact shifted_power_le N τ t
    _ = (1+|t|)^N*((1+|τ|)^(N+2)*‖mellin W (σ+(τ:ℂ)*Complex.I)‖) := by
      rw [pow_add]
      ring
    _ ≤ (1+|t|)^N*C := mul_le_mul_of_nonneg_left (hdecay τ) (by positivity)
    _ = _ := mul_comm _ _

lemma ideal_norm_tail_le {J r : ℝ} (hJ : 0 < J) (hr : 2 < r) :
    (∑' ν : EisensteinIdealExponent,
      if J < idealExponentNorm ν then idealExponentNorm ν^(-r) else 0) ≤
      J^(2-r)*(∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))) := by
  have ht := (summable_ideal_norm_rpow (by linarith : 1 < r)).indicator
    (fun ν => J < idealExponentNorm ν)
  have hs := (summable_ideal_norm_rpow (by norm_num : (1:ℝ) < 2)).mul_left (J^(2-r))
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum _ ht hs
  intro ν
  change (if J < idealExponentNorm ν then idealExponentNorm ν^(-r) else 0) ≤
    J^(2-r)*idealExponentNorm ν^(-(2:ℝ))
  by_cases hν : J < idealExponentNorm ν
  · simp only [hν,ite_true, if_true]
    have hn := idealExponentNorm_pos ν
    calc
      _ = idealExponentNorm ν^(2-r)*idealExponentNorm ν^(-(2:ℝ)) := by
        rw [← Real.rpow_add hn]
        congr 1
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hJ hν.le (by linarith)) (by positivity)
  · simp only [hν,ite_false, if_false]
    exact mul_nonneg (Real.rpow_nonneg hJ.le _)
      (Real.rpow_nonneg (idealExponentNorm_pos ν).le _)

lemma norm_idealDirichletTail_le (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {J : ℝ} (hJ : 0 < J) (s : ℂ) (hs : 2 < s.re) :
    ‖idealDirichletTail χ J s‖ ≤
      J^(2-s.re)*(∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))) := by
  let f (ν : EisensteinIdealExponent) : ℂ :=
    if J < idealExponentNorm ν then χ ν*(idealExponentNorm ν:ℂ)^(-s) else 0
  let b (ν : EisensteinIdealExponent) : ℝ :=
    if J < idealExponentNorm ν then idealExponentNorm ν^(-s.re) else 0
  have hb : Summable b :=
    (summable_ideal_norm_rpow (by linarith : 1 < s.re)).indicator _
  have hf (ν : EisensteinIdealExponent) : ‖f ν‖ ≤ b ν := by
    dsimp [f,b]
    split_ifs with hν
    · rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),
        Complex.neg_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (idealExponentNorm_pos ν).le _) (hχ ν)
    · simp
  have hfn : Summable (fun ν => ‖f ν‖) :=
    hb.of_norm_bounded (fun ν => by rw [Real.norm_eq_abs,abs_of_nonneg (_root_.norm_nonneg _)]; exact hf ν)
  calc
    _ ≤ ∑' ν, ‖f ν‖ := norm_tsum_le_tsum_norm hfn
    _ ≤ ∑' ν, b ν := Summable.tsum_le_tsum hf hfn hb
    _ ≤ _ := ideal_norm_tail_le hJ hs

lemma dual_tail_scale_identity {A Z J : ℝ} (hZ : 0 < Z) (hJ : 0 < J)
    (m : ℕ) (t : ℝ) :
    Z^(1/2-(m:ℝ))*A^(2*m)*J^(3/2-(m:ℝ))*(1+|t|)^(2*m) =
      Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m := by
  rw [Real.rpow_sub hZ,Real.rpow_sub hJ,Real.rpow_natCast,Real.rpow_natCast,
    div_pow,mul_pow,mul_pow,pow_mul,pow_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DualTailTruncation
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative truncation at a small power beyond the natural Hecke
length. The cutoff is a numerical inequality, not a duality assumption. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma exists_dual_tail_order {δ : ℝ} (hδ : 0 < δ) (B H : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ 2*B-δ*(m:ℝ) ≤ -H := by
  obtain ⟨m,hm⟩ := exists_nat_gt (max 2 ((2*B+H)/δ))
  have hm2 : (2:ℝ) < m := lt_of_le_of_lt (le_max_left _ _) hm
  have hm' : (2*B+H)/δ < m := lt_of_le_of_lt (le_max_right _ _) hm
  have he := (div_lt_iff₀ hδ).mp hm'
  refine ⟨m,?_,by nlinarith⟩
  have : 2 < m := by exact_mod_cast hm2
  omega

lemma dual_tail_scale_bound {δ B H Y A Z J : ℝ} {m : ℕ}
    (hY : 1 ≤ Y) (hA : 0 < A) (hZ : 0 < Z) (hJ : 0 < J)
    (hZB : Z ≤ Y^B) (hJB : J ≤ Y^B)
    (hcut : (A^2*(1+|H|)^2)/(Z*J) ≤ Y^(-δ))
    {R : ℝ} (hm : 2*B-δ*(m:ℝ) ≤ -R) :
    Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|H|)^2)/(Z*J))^m ≤ Y^(-R) := by
  have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hz : Z^(1/2:ℝ) ≤ Y^(B/2) := by
    calc
      _ ≤ (Y^B)^(1/2:ℝ) := Real.rpow_le_rpow hZ.le hZB (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hY0.le]; congr 1; ring
  have hj : J^(3/2:ℝ) ≤ Y^(3*B/2) := by
    calc
      _ ≤ (Y^B)^(3/2:ℝ) := Real.rpow_le_rpow hJ.le hJB (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hY0.le]; congr 1; ring
  have hc : ((A^2*(1+|H|)^2)/(Z*J))^m ≤ Y^(-δ*(m:ℝ)) := by
    calc
      _ ≤ (Y^(-δ))^m := pow_le_pow_left₀ (by positivity) hcut _
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
  calc
    _ ≤ Y^(B/2)*Y^(3*B/2)*Y^(-δ*(m:ℝ)) := by gcongr
    _ = Y^(2*B-δ*(m:ℝ)) := by rw [← Real.rpow_add hY0,← Real.rpow_add hY0]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY hm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDualTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-angular far-left tail, with explicit natural dual length.
Only the constant changes with the angular shift; every power of the
length, conductor and height is retained from the full ideal series. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

lemma norm_angularDualTailIntegrand_le (W : ℝ → ℂ)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {k : ℝ} (hk : 0 ≤ k)
    {ε : ℂ} (hε : ‖ε‖ ≤ 1) {A Z J : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (hJ : 0 < J) {m : ℕ} (hm : 2 ≤ m) (t τ : ℝ) :
    ‖angularDualTailIntegrand W χ ε A Z J k m t τ‖ ≤
      (Z^(1/2-(m:ℝ))*A^(2*m)*(k+3*(m:ℝ)+1)^(2*m)*J^(3/2-(m:ℝ))*
        (∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)))) *
      (‖mellin W ((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^(2*m)) := by
  let u : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I
  have hu : u = (1/2:ℂ)-(m:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by
    dsimp [u]
    push_cast
    ring
  have hdu : 1-u = (1/2:ℂ)+(m:ℂ)-((τ-t:ℝ):ℂ)*Complex.I := by
    dsimp [u]
    push_cast
    ring
  have hur : (1-u).re = 1/2+(m:ℝ) := by rw [hdu]; simp
  have hd := norm_idealDirichletTail_le χ hχ hJ (1-u)
    (by
      rw [hur]
      have hm' : (2:ℝ) ≤ m := by exact_mod_cast hm
      linarith)
  rw [hur] at hd
  have hde : (2:ℝ)-(1/2+(m:ℝ)) = 3/2-(m:ℝ) := by ring
  rw [hde] at hd
  have hg : ‖Complex.Gamma (1-u+(k:ℂ))/Complex.Gamma (u+(k:ℂ))‖ ≤
      (k+3*(m:ℝ)+1)^(2*m)*(1+|τ-t|)^(2*m) := by
    rw [hdu,hu]
    have hnum : (1/2:ℂ)+(m:ℂ)-((τ-t:ℝ):ℂ)*Complex.I+(k:ℂ) =
        (1/2:ℂ)+(m:ℂ)+(k:ℂ)-((τ-t:ℝ):ℂ)*Complex.I := by ring
    have hden : (1/2:ℂ)-(m:ℂ)+((τ-t:ℝ):ℂ)*Complex.I+(k:ℂ) =
        (1/2:ℂ)-(m:ℂ)+(k:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by ring
    rw [hnum,hden]
    exact norm_angular_gamma_left_ratio_le hk m (τ-t)
  have hAs : ‖(A:ℂ)^(1-2*u)‖ = A^(2*m) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    have hre : (1-2*u).re = ((2*m:ℕ):ℝ) := by dsimp [u]; simp; ring
    rw [hre,Real.rpow_natCast]
  have hZs : ‖(Z:ℂ)^((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖ =
      Z^(1/2-(m:ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]
    congr 1
    simp
  change ‖mellin W _ * (Z:ℂ)^_ * ε * (A:ℂ)^(1-2*u) *
    (Complex.Gamma (1-u+(k:ℂ))/Complex.Gamma (u+(k:ℂ)))*idealDirichletTail χ J (1-u)‖ ≤ _
  simp only [norm_mul,hAs,hZs]
  calc
    _ ≤ ‖mellin W ((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖ *
        Z^(1/2-(m:ℝ))*1*A^(2*m) *
        ((k+3*(m:ℝ)+1)^(2*m)*(1+|τ-t|)^(2*m)) *
        (J^(3/2-(m:ℝ))*(∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ)))) := by
      gcongr
    _ = _ := by ring

/-- An arbitrary-order tail bound with the natural dual length displayed.
The constant depends only on the fixed weight and the chosen order `m`. -/
theorem angular_dual_tail_integral_bound (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {k : ℝ} (hk : 0 ≤ k) {m : ℕ} (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (χ : EisensteinIdealExponent → ℂ),
      (∀ ν, ‖χ ν‖ ≤ 1) → ∀ (ε : ℂ), ‖ε‖ ≤ 1 →
      ∀ (A Z J : ℝ), 0 < A → 0 < Z → 0 < J → ∀ t : ℝ,
      ‖∫ τ : ℝ, angularDualTailIntegrand W χ ε A Z J k m t τ‖ ≤
        C*Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m := by
  obtain ⟨Cw,hCw,hdecay⟩ := mellin_polynomial_majorant W hW hpos hsm
    (1/2-(m:ℝ)) (2*m)
  let S : ℝ := ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))
  let I : ℝ := ∫ τ : ℝ, mellinEdgeMajorant 1 τ
  have hS : 0 ≤ S := tsum_nonneg fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _
  have hI : 0 ≤ I := integral_nonneg fun τ => by dsimp [mellinEdgeMajorant]; positivity
  refine ⟨(k+3*(m:ℝ)+1)^(2*m)*S*Cw*I,by positivity,?_⟩
  intro χ hχ ε hε A Z J hA hZ hJ t
  let B : ℝ := Z^(1/2-(m:ℝ))*A^(2*m)*(k+3*(m:ℝ)+1)^(2*m)*J^(3/2-(m:ℝ))*S
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (τ : ℝ) : ‖angularDualTailIntegrand W χ ε A Z J k m t τ‖ ≤
      mellinEdgeMajorant (B*Cw*(1+|t|)^(2*m)) τ := by
    have hd := hdecay t τ
    have he : (((1/2-(m:ℝ):ℝ):ℂ)+(τ:ℂ)*Complex.I) =
        (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I := by push_cast; ring
    rw [he] at hd
    calc
      _ ≤ B*(‖mellin W ((1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I)‖*(1+|τ-t|)^(2*m)) :=
        norm_angularDualTailIntegrand_le W χ hχ hk hε hA hZ hJ hm t τ
      _ ≤ B*mellinEdgeMajorant (Cw*(1+|t|)^(2*m)) τ :=
        mul_le_mul_of_nonneg_left hd hB
      _ = _ := by unfold mellinEdgeMajorant; ring
  calc
    _ ≤ ∫ τ : ℝ, mellinEdgeMajorant (B*Cw*(1+|t|)^(2*m)) τ :=
      norm_integral_le_of_norm_le (mellinEdgeMajorant_integrable _) (Filter.Eventually.of_forall hb)
    _ = B*Cw*(1+|t|)^(2*m)*I := by
      have he : (fun τ => mellinEdgeMajorant (B*Cw*(1+|t|)^(2*m)) τ) =
          fun τ => (B*Cw*(1+|t|)^(2*m))*mellinEdgeMajorant 1 τ := by
        funext τ
        unfold mellinEdgeMajorant
        ring
      rw [he,integral_const_mul]
    _ = ((k+3*(m:ℝ)+1)^(2*m)*S*Cw*I) *
        (Z^(1/2-(m:ℝ))*A^(2*m)*J^(3/2-(m:ℝ))*(1+|t|)^(2*m)) := by dsimp [B]; ring
    _ = _ := by rw [dual_tail_scale_identity hZ hJ]; ring


/-- The omitted far-left tail is smaller than every fixed negative power
once the cutoff exceeds the natural length by `Y^δ`. Only polynomial
upper bounds for the two lengths are used. -/
theorem angular_dual_tail_arbitrary_power (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {k : ℝ} (hk : 0 ≤ k) {δ : ℝ} (hδ : 0 < δ) (B R : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 2 ≤ m ∧ 0 ≤ C ∧
      ∀ (χ : EisensteinIdealExponent → ℂ), (∀ ν, ‖χ ν‖ ≤ 1) →
      ∀ (ε : ℂ), ‖ε‖ ≤ 1 → ∀ (Y A Z J : ℝ),
      1 ≤ Y → 0 < A → 0 < Z → 0 < J → Z ≤ Y^B → J ≤ Y^B →
      ∀ t : ℝ, (A^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ‖∫ τ : ℝ, angularDualTailIntegrand W χ ε A Z J k m t τ‖ ≤ C*Y^(-R) := by
  obtain ⟨m,hm2,hm⟩ := exists_dual_tail_order hδ B R
  obtain ⟨C,hC,hbound⟩ := angular_dual_tail_integral_bound W hW hpos hsm hk hm2
  refine ⟨m,C,hm2,hC,?_⟩
  intro χ hχ ε hε Y A Z J hY hA hZ hJ hZB hJB t hcut
  calc
    _ ≤ C*Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m :=
      hbound χ hχ ε hε A Z J hA hZ hJ t
    _ = C*(Z^(1/2:ℝ)*J^(3/2:ℝ)*((A^2*(1+|t|)^2)/(Z*J))^m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (dual_tail_scale_bound hY hA hZ hJ hZB hJB hcut hm) hC


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDualContour
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moving finite dual polynomials back to the symmetry line. The only
new conditional analytic input is the bounded-strip polynomial estimate
for the classical Gamma quotient, a specialization of NIST DLMF 5.11.9
(uniformly for bounded real parts). The half-integer-line estimate needed
for the discarded tail was proved directly in GammaLeftLine. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma norm_conductor_power_strip {A a σ u : ℝ} (hA : 0 < A)
    (hσ : σ ∈ Icc a (1/2:ℝ)) :
    ‖(A:ℂ)^(1-2*(σ+(u:ℂ)*Complex.I))‖ ≤ max 1 (A^(1-2*a)) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
  have hre : (1-2*((σ:ℂ)+(u:ℂ)*Complex.I)).re = 1-2*σ := by simp
  rw [hre]
  by_cases hA1 : 1 ≤ A
  · exact (Real.rpow_le_rpow_of_exponent_le hA1 (by linarith [hσ.1])).trans (le_max_right _ _)
  · exact (Real.rpow_le_one hA.le (le_of_not_ge hA1) (by linarith [hσ.2])).trans
      (le_max_left _ _)

lemma differentiable_finiteNormDirichlet {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 0 < N i) :
    Differentiable ℂ (finiteNormDirichlet S a N) := by
  apply Differentiable.fun_sum
  intro i hi
  have : NeZero (N i:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (hN i hi).ne'⟩
  exact ((differentiable_const_cpow_of_neZero _).comp differentiable_id.neg).const_mul _

lemma norm_finiteNormDirichlet_le {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (s : ℂ) (hs : 0 ≤ s.re) :
    ‖finiteNormDirichlet S a N s‖ ≤ ∑ i ∈ S, ‖a i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le zero_lt_one (hN i hi)),
    Complex.neg_re]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (Real.rpow_le_one_of_one_le_of_nonpos
    (hN i hi) (by linarith))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDualContour
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retained finite dual polynomials for fixed infinity type. The sole
Gamma strip input is the bounded-strip consequence of NIST DLMF 5.11.9;
there is no arithmetic moment or smooth-duality conclusion in that input. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma differentiableOn_angularGammaFEQuotient {k : ℝ} (hk : 0 ≤ k) :
    DifferentiableOn ℂ (angularGammaFEQuotient k) {s : ℂ | s.re < 1} := by
  intro s hs
  have hreg : ∀ n : ℕ, 1-s+(k:ℂ) ≠ -(n:ℂ) := by
    intro n hn
    have hr := congrArg Complex.re hn
    simp only [Complex.add_re,Complex.sub_re,Complex.one_re,Complex.ofReal_re,
      Complex.neg_re,Complex.natCast_re] at hr
    have : (0:ℝ) ≤ n := by positivity
    change s.re < 1 at hs
    linarith
  have hu : DifferentiableAt ℂ (fun z : ℂ => 1-z+(k:ℂ)) s := by fun_prop
  have htop := (Complex.differentiableAt_Gamma (1-s+(k:ℂ)) hreg).comp s hu
  have hbot := (Complex.differentiable_one_div_Gamma (s+(k:ℂ))).comp s
    (show DifferentiableAt ℂ (fun z : ℂ => z+(k:ℂ)) s by fun_prop)
  exact (htop.mul hbot).differentiableWithinAt

lemma differentiableOn_angularFiniteHeckeDual {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 0 < N i)
    (ε : ℂ) {k : ℝ} (hk : 0 ≤ k) {A : ℝ} (hA : 0 < A) :
    DifferentiableOn ℂ (angularFiniteHeckeDual S a N ε A k) {s : ℂ | s.re < 1} := by
  have : NeZero (A:ℂ) := ⟨Complex.ofReal_ne_zero.mpr hA.ne'⟩
  have hp : Differentiable ℂ (fun s : ℂ => (A:ℂ)^(1-2*s)) :=
    (differentiable_const_cpow_of_neZero _).comp (by fun_prop)
  have hd : Differentiable ℂ (fun s : ℂ => finiteNormDirichlet S a N (1-s)) :=
    (differentiable_finiteNormDirichlet S a N hN).comp (by fun_prop)
  exact ((hp.const_mul ε).differentiableOn.mul
    (differentiableOn_angularGammaFEQuotient hk)).mul hd.differentiableOn

/-- The finite retained dual polynomial admits the actual contour move.
Its coefficients are unchanged during the move. -/
theorem angular_finite_dual_contour_shift {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (ε : ℂ) {k : ℝ} (hk : 0 ≤ k) {A Z b : ℝ} (hA : 0 < A) (hZ : 1 ≤ Z) (hb : b ≤ 1/2)
    (hGamma : AngularGammaQuotientStripBound k b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    (∫ τ : ℝ, mellin W (b+(τ:ℂ)*Complex.I)*(Z:ℂ)^(b+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual S a N ε A k (b+((τ-t:ℝ):ℂ)*Complex.I)) =
    ∫ τ : ℝ, mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual S a N ε A k ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) := by
  obtain ⟨Cg,n,hCg,hg⟩ := hGamma
  let B := ‖ε‖*max 1 (A^(1-2*b))*Cg*(∑ i ∈ S, ‖a i‖)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoly (σ : ℝ) (hσ : σ ∈ Icc b (1/2:ℝ)) (τ : ℝ) :
      ‖angularFiniteHeckeDual S a N ε A k (σ+((τ-t:ℝ):ℂ)*Complex.I)‖ ≤ B*(1+|τ-t|)^n := by
    have hn := norm_finiteNormDirichlet_le S a N hN
      (1-(σ+((τ-t:ℝ):ℂ)*Complex.I)) (by simp; linarith [hσ.2])
    have hpow := norm_conductor_power_strip (u := τ-t) hA hσ
    have hgam := hg σ hσ (τ-t)
    unfold angularFiniteHeckeDual
    simp only [norm_mul]
    calc
      _ ≤ ‖ε‖*max 1 (A^(1-2*b))*(Cg*(1+|τ-t|)^n)*(∑ i ∈ S, ‖a i‖) := by gcongr
      _ = _ := by dsimp [B]; ring
  let f : ℂ → ℂ := fun s => mellin W s*(Z:ℂ)^s*
    angularFiniteHeckeDual S a N ε A k (s-(t:ℂ)*Complex.I)
  have : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hZ).ne'⟩
  have hshift : DifferentiableOn ℂ (fun s : ℂ =>
      angularFiniteHeckeDual S a N ε A k (s-(t:ℂ)*Complex.I)) (closedVerticalStrip b (1/2)) := by
    apply (differentiableOn_angularFiniteHeckeDual S a N
      (fun i hi => lt_of_lt_of_le zero_lt_one (hN i hi)) ε hk hA).comp
      (differentiable_id.sub_const _).differentiableOn
    intro s hs
    change (s-(t:ℂ)*Complex.I).re < 1
    have hsr := hs.2
    simpa using lt_of_le_of_lt hsr (by norm_num : (1/2:ℝ) < 1)
  have hf : DifferentiableOn ℂ f (closedVerticalStrip b (1/2)) :=
    ((smooth_mellin_entire W hW hpos hsm.continuous).mul
      (differentiable_const_cpow_of_neZero _)).differentiableOn.mul hshift
  obtain ⟨K,_,hK⟩ := norm_mellinHecke_integrand_le W hW hpos hsm hZ t
    (angularFiniteHeckeDual S a N ε A k) hB n hpoly
  have he (σ τ : ℝ) : f (σ+(τ:ℂ)*Complex.I) =
      mellin W (σ+(τ:ℂ)*Complex.I)*(Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*
        angularFiniteHeckeDual S a N ε A k (σ+((τ-t:ℝ):ℂ)*Complex.I) := by
    dsimp [f]
    congr 2
    push_cast
    ring
  have hc := mellin_contour_shift_of_majorant hb f hf (mellinEdgeMajorant K)
    (mellinEdgeMajorant_integrable K) (mellinEdgeMajorant_tendsto K).1
    (mellinEdgeMajorant_tendsto K).2 (by intro σ hσ τ; rw [he]; exact hK σ hσ τ)
  simp_rw [he] at hc
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hc

lemma angular_finite_dual_strip_growth {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (ε : ℂ) {k : ℝ} (_hk : 0 ≤ k) {A b : ℝ} (hA : 0 < A) (hGamma : AngularGammaQuotientStripBound k b) :
    ∃ (B : ℝ) (n : ℕ), 0 ≤ B ∧ ∀ σ ∈ Icc b (1/2:ℝ), ∀ u : ℝ,
      ‖angularFiniteHeckeDual S a N ε A k (σ+(u:ℂ)*Complex.I)‖ ≤ B*(1+|u|)^n := by
  obtain ⟨Cg,n,hCg,hg⟩ := hGamma
  let B := ‖ε‖*max 1 (A^(1-2*b))*Cg*(∑ i ∈ S, ‖a i‖)
  refine ⟨B,n,by dsimp [B]; positivity,?_⟩
  intro σ hσ u
  have hn := norm_finiteNormDirichlet_le S a N hN (1-(σ+(u:ℂ)*Complex.I))
    (by simp; linarith [hσ.2])
  have hpow := norm_conductor_power_strip (u := u) hA hσ
  have hgam := hg σ hσ u
  unfold angularFiniteHeckeDual
  simp only [norm_mul]
  calc
    _ ≤ ‖ε‖*max 1 (A^(1-2*b))*(Cg*(1+|u|)^n)*(∑ i ∈ S, ‖a i‖) := by gcongr
    _ = _ := by dsimp [B]; ring


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ShortMoebiusFinite
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite primary ideal polynomials and their actual Eisenstein-element
realizations. These sums omit the ramified prime above three. They are
not identified with the complete ideal series of `IdealMellinSeries`. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealPrimaryGenerator_injective : Function.Injective idealPrimaryGenerator :=
  Function.LeftInverse.injective idealExponentOf_primaryGenerator

@[simp] lemma mem_primaryIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ primaryIdealBall Y ↔ primary (idealPrimaryGenerator ν) ∧ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ha,hN⟩ := mem_primaryElementBall.mp ha
    rw [idealPrimaryGenerator_at_element ha,idealExponentOf_norm (primary_ne_zero ha)]
    exact ⟨ha,hN⟩
  · rintro ⟨hν,hN⟩
    exact Finset.mem_image.mpr ⟨idealPrimaryGenerator ν,
      mem_primaryElementBall.mpr ⟨hν,(idealPrimaryGenerator_norm ν).trans_le hN⟩,
      idealExponentOf_primaryGenerator ν⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealEulerExclusion
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite Euler exclusions on the complete ideal lattice. The full norm
ball includes the ramified prime; excluding it is an explicit choice of
prime set, and every rescaling factor is retained. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[simp] lemma mem_fullIdealBall {ν : EisensteinIdealExponent} {Y : ℝ} :
    ν ∈ fullIdealBall Y ↔ idealExponentNorm ν ≤ Y := by
  constructor
  · intro h
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp h
    rw [idealExponentOf_norm (mem_nonzeroNormBall.mp ha).2]
    exact (mem_nonzeroNormBall.mp ha).1
  · intro h
    exact Finset.mem_image.mpr ⟨idealExponentGenerator ν,
      mem_nonzeroNormBall.mpr ⟨by simpa only [idealExponentNorm,normNat_cast] using h,
        idealExponentGenerator_ne_zero ν⟩,idealExponentOf_generator ν⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimePowerDivisors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
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

lemma idealPrimeRepresentative_normNat_ge_two (p : EisensteinIdealPrime) :
    2 ≤ normNat (idealPrimeRepresentative p) := by
  have hp := idealPrimeRepresentative_irreducible p
  have hz := normNat_ne_zero hp.ne_zero
  have ho : normNat (idealPrimeRepresentative p) ≠ 1 := by
    intro h
    apply hp.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [← normNat_cast, h]
    norm_num
  omega

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeToThreeIdeals
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual ramified Euler restriction in primary-element polynomials.
Prime-to-three ideals are identified arithmetically, then the complete
ideal-sum exclusion formula restores their missing local factors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealGenerator_coprime_three_iff (ν : EisensteinIdealExponent) :
    IsCoprime (idealExponentGenerator ν) 3 ↔ ∀ p ∈ ramifiedIdealPrimes, ν p = 0 := by
  rw [isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν) (by norm_num),
    idealExponentOf_generator]
  constructor
  · intro h p hp
    rcases h p with hν | h3
    · exact hν
    · exact False.elim ((Finsupp.mem_support_iff.mp hp) h3)
  · intro h p
    by_cases hp : p ∈ ramifiedIdealPrimes
    · exact Or.inl (h p hp)
    · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

/-- Primary normalization succeeds exactly on the ideals prime to three. -/
theorem idealPrimaryGenerator_primary_iff (ν : EisensteinIdealExponent) :
    primary (idealPrimaryGenerator ν) ↔ ∀ p ∈ ramifiedIdealPrimes, ν p = 0 := by
  rw [← idealGenerator_coprime_three_iff]
  constructor
  · intro h
    exact (primary_coprime_three h).of_isCoprime_of_dvd_left
      (primaryNormalize_associated (idealExponentGenerator ν)).dvd
  · intro h
    exact primaryNormalize_primary (residue_isUnit_of_isCoprime h.symm)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ResidueIdealCharacters
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite residue character as an actual complete ideal character,
and exact restoration of Euler factors after primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma residueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν κ : EisensteinIdealExponent) :
    residueIdealChar q χ (ν+κ) = residueIdealChar q χ ν*residueIdealChar q χ κ := by
  simp only [residueIdealChar,idealExponentGenerator_add,map_mul]

lemma residueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ν : EisensteinIdealExponent) :
    ‖residueIdealChar q χ ν‖ ≤ 1 := residueChar_norm_le_one hq χ _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularHeckeCharacter
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite factor at 3 required by a fixed angular Hecke character.
The archimedean phase is retained separately, including after primitive
conductor reduction. Complete ideal sums therefore include every prime
at which the primitive character is unramified. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment

lemma star_theta {x : Eisenstein} (hx : x ≠ 0) (ℓ : ℤ) :
    star (theta ℓ x) = theta (-ℓ) x := by
  rw [show theta (-ℓ) x = (theta ℓ x)⁻¹ by simp only [theta, zpow_neg]]
  exact (Complex.inv_eq_conj (norm_theta hx ℓ)).symm

lemma angularResidueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν κ : EisensteinIdealExponent) :
    angularResidueIdealChar q χ ℓ (ν+κ) =
      angularResidueIdealChar q χ ℓ ν*angularResidueIdealChar q χ ℓ κ := by
  simp only [angularResidueIdealChar, residueIdealChar_add, idealExponentGenerator_add, theta_mul]
  ring

lemma angularResidueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    ‖angularResidueIdealChar q χ ℓ ν‖ ≤ 1 := by
  rw [angularResidueIdealChar, norm_mul, norm_theta (idealExponentGenerator_ne_zero ν), mul_one]
  exact residueIdealChar_norm_le_one hq χ ν

lemma star_angularResidueIdealChar (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (ν : EisensteinIdealExponent) :
    star (angularResidueIdealChar q χ ℓ ν) = angularResidueIdealChar q (star χ) (-ℓ) ν := by
  simp only [angularResidueIdealChar, residueIdealChar, star_mul, MulChar.star_apply,
    star_theta (idealExponentGenerator_ne_zero ν)]
  ring

lemma angular_character_associated {q x y : Eisenstein}
    (χ : MulChar (Residues q) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible q χ ℓ)
    (hxy : Associated x y) :
    χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x =
      χ (Ideal.Quotient.mk (modulus q) y)*theta ℓ y := by
  obtain ⟨u,rfl⟩ := hxy
  rw [map_mul, map_mul, theta_mul]
  symm
  calc
    _ = (χ (Ideal.Quotient.mk (modulus q) x)*theta ℓ x)*
        (χ (Ideal.Quotient.mk (modulus q) u)*theta ℓ u) := by ring
    _ = _ := by rw [hu u, mul_one]

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

lemma dual_dyad_weight_identity {J x : ℝ} (hJ : 0 < J) (hx : 0 < x) :
    x^(-(1/2:ℝ)) = J^(-(1/2:ℝ))*(J/x)^(1/2:ℝ) := by
  rw [Real.div_rpow hJ.le hx.le,Real.rpow_neg hJ.le,Real.rpow_neg hx.le]
  field_simp [(Real.rpow_pos_of_pos hJ (1/2:ℝ)).ne']

lemma dual_dyad_weight_le_one {J x : ℝ} (hJ : 0 < J) (hx : J ≤ x) :
    (J/x)^(1/2:ℝ) ≤ 1 := by
  apply Real.rpow_le_one
  · exact div_nonneg hJ.le (hJ.le.trans hx)
  · exact (div_le_one (hJ.trans_le hx)).mpr hx
  · norm_num

/-- Extracting the inverse square-root dyadic length changes only the
fixed norm coefficients; the character remains in the same polynomial. -/
theorem finite_dual_dyad_rescale {ι : Type*} (S : Finset ι) (a : ι → ℂ)
    (N : ι → ℝ) {J : ℝ} (hJ : 0 < J) (hN : ∀ i ∈ S, 0 < N i) (u : ℝ) :
    finiteNormDirichlet S a N ((1/2:ℂ)-(u:ℂ)*Complex.I) =
      (J^(-(1/2:ℝ)):ℝ)*∑ i ∈ S,
        (a i*((J/N i)^(1/2:ℝ):ℝ))*mellinPhase u (N i) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have he : -((1/2:ℂ)-(u:ℂ)*Complex.I) = ((-(1/2:ℝ)):ℂ)+(u:ℂ)*Complex.I := by
    push_cast
    ring
  change a i*(N i:ℂ)^(-((1/2:ℂ)-(u:ℂ)*Complex.I)) = _
  rw [he,← Complex.ofReal_neg,positive_cpow_phase (hN i hi) (-(1/2:ℝ)) u,dual_dyad_weight_identity hJ (hN i hi)]
  push_cast
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeSmoothDual
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
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

/-- Exact Mellin inversion for the actual norm-twisted complete ideal sum. -/
theorem hecke_twisted_smooth_mellin (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (L : ℂ → ℂ)
    (hL : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W (2+(τ:ℂ)*Complex.I)*(Z:ℂ)^(2+(τ:ℂ)*Complex.I)*
          L (2+((τ-t:ℝ):ℂ)*Complex.I) := by
  have h := ideal_smooth_mellin (fun ν => χ ν*mellinPhase t (idealExponentNorm ν))
    (by intro ν; simpa only [norm_mul,mellinPhase_norm,mul_one] using hχ ν)
    W hW hpos hsm (by norm_num : (1:ℝ) < 2) hZ
  rw [h]
  congr 1
  apply integral_congr_ae
  filter_upwards with τ
  rw [twisted_normDirichletSeries]
  have he : ((2:ℂ)+(τ:ℂ)*Complex.I)-(t:ℂ)*Complex.I =
      2+((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
  norm_num only [Complex.ofReal_ofNat]
  rw [he,hL _ (by simp)]

lemma summable_idealDirichlet (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun ν => χ ν*(idealExponentNorm ν:ℂ)^(-s)) := by
  apply Summable.of_norm
  have hn (ν : EisensteinIdealExponent) :
      ‖χ ν*(idealExponentNorm ν:ℂ)^(-s)‖ = ‖χ ν‖*idealExponentNorm ν^(-s.re) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (idealExponentNorm_pos ν),Complex.neg_re]
  simpa only [hn] using summable_ideal_character_weight hs χ hχ

lemma idealDirichlet_split (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) (J : ℝ) :
    normDirichletSeries χ idealExponentNorm s =
      finiteNormDirichlet (fullIdealBall J) χ idealExponentNorm s + idealDirichletTail χ J s := by
  let f (ν : EisensteinIdealExponent) := χ ν*(idealExponentNorm ν:ℂ)^(-s)
  have hf : Summable f := summable_idealDirichlet χ hχ s hs
  have hhead : Summable (fun ν => if idealExponentNorm ν ≤ J then f ν else 0) :=
    hf.indicator _
  have htail : Summable (fun ν => if J < idealExponentNorm ν then f ν else 0) :=
    hf.indicator _
  have hfinite : (∑' ν, if idealExponentNorm ν ≤ J then f ν else 0) =
      ∑ ν ∈ fullIdealBall J, f ν := by
    calc
      _ = ∑ ν ∈ fullIdealBall J, if idealExponentNorm ν ≤ J then f ν else 0 := by
        apply tsum_eq_sum
        intro ν hν
        simp only [mem_fullIdealBall] at hν
        simp [hν]
      _ = _ := Finset.sum_congr rfl (fun ν hν => ite_eq_left (mem_fullIdealBall.mp hν))
  calc
    _ = ∑' ν, ((if idealExponentNorm ν ≤ J then f ν else 0) +
        (if J < idealExponentNorm ν then f ν else 0)) := by
      apply tsum_congr
      intro ν
      by_cases hν : idealExponentNorm ν ≤ J <;> simp [hν,not_lt_of_ge,lt_of_not_ge,f]
    _ = (∑' ν, if idealExponentNorm ν ≤ J then f ν else 0) +
        ∑' ν, if J < idealExponentNorm ν then f ν else 0 := hhead.tsum_add htail
    _ = _ := by rw [hfinite]; rfl

lemma mellinHecke_line_integrable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {Z : ℝ} (hZ : 1 ≤ Z) (σ t : ℝ) (L : ℂ → ℂ)
    (hcont : Continuous (fun τ : ℝ => L (σ+((τ-t:ℝ):ℂ)*Complex.I)))
    {C : ℝ} (hC : 0 ≤ C) (n : ℕ)
    (hbound : ∀ τ : ℝ, ‖L (σ+((τ-t:ℝ):ℂ)*Complex.I)‖ ≤ C*(1+|τ-t|)^n) :
    Integrable (fun τ : ℝ => mellin W (σ+(τ:ℂ)*Complex.I)*
      (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*L (σ+((τ-t:ℝ):ℂ)*Complex.I)) := by
  have : NeZero (Z:ℂ) := ⟨Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hZ).ne'⟩
  have hs : Continuous (fun τ : ℝ => (σ:ℂ)+(τ:ℂ)*Complex.I) := by fun_prop
  have hc := (((smooth_mellin_entire W hW hpos hsm.continuous).continuous.comp hs).mul
    ((differentiable_const_cpow_of_neZero (Z:ℂ)).continuous.comp hs)).mul hcont
  obtain ⟨K,_,hK⟩ := norm_mellinHecke_integrand_le W hW hpos hsm hZ t L hC n
    (a := σ) (b := σ) (by intro x hx τ; have he : x = σ := le_antisymm hx.2 hx.1; subst x; exact hbound τ)
  exact (mellinEdgeMajorant_integrable K).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (hK σ ⟨le_rfl,le_rfl⟩))

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

theorem shifted_hecke_analyticData_of_completed
    {χ χdual : EisensteinIdealExponent → ℂ}
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (hL : Differentiable ℂ L)
    (hs : ∀ s : ℂ, 1 < s.re → L s = normDirichletSeries χ idealExponentNorm s)
    (hds : ∀ s : ℂ, 1 < s.re → Ldual s = normDirichletSeries χdual idealExponentNorm s)
    (hFE : HeckeFunctionalEquation A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (hGamma : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+k) (2+k)) :
    ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual := by
  refine ⟨hL,hs,hds,hFE,?_⟩
  intro m
  let M := m+2
  let a : ℝ := 1/2-(M:ℝ)
  let S : ℝ := ∑' ν : EisensteinIdealExponent, idealExponentNorm ν^(-(2:ℝ))
  let C : ℝ := S+‖ε‖*A^(2*M)*(k+3*(M:ℝ)+1)^(2*M)*S
  have hS : 0 ≤ S := tsum_nonneg fun ν => Real.rpow_nonneg (idealExponentNorm_pos ν).le _
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ha : ∀ z : ℂ, z.re = a → ‖L z‖ ≤ C*(1+|z.im|)^(2*M) := by
    intro z hz
    have he : z = (1/2:ℂ)-(M:ℂ)+(z.im:ℂ)*Complex.I := by
      apply Complex.ext <;> simp [a] at hz ⊢; assumption
    have hb := angular_hecke_left_boundary χdual hχdual hA hk hL hcomp hFE hds
      (show 2 ≤ M by dsimp [M]; omega) z.im
    rw [←he] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity))
  have hb : ∀ z : ℂ, z.re = 2 → ‖L z‖ ≤ C*(1+|z.im|)^(2*M) := by
    intro z hz
    rw [hs z (by linarith)]
    calc
      _ ≤ S := norm_idealDirichlet_le_zeta_two χ hχ z hz.ge
      _ ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)
      _ ≤ C*(1+|z.im|)^(2*M) := le_mul_of_one_le_right hC
        (one_le_pow₀ (by linarith [abs_nonneg z.im]))
  have ha2 : a < 2 := by
    dsimp [a]
    have hM : (0:ℝ) ≤ M := by positivity
    linarith
  have hbound := polynomial_strip_of_finite_order (a := a) (b := 2) ha2 hL
    (shifted_completed_finiteVerticalOrder hA hL hcomp (hGamma M)) hC (2*M) ha hb
  have hapos : 0 < 2-a+1 := by linarith
  refine ⟨C*2^(2*M)*(2-a+1)^(2*M),2*M,by positivity,?_⟩
  intro σ hσ u
  have hσa : a ≤ σ := by
    dsimp [a,M]
    push_cast
    linarith [hσ.1]
  simpa using hbound (σ+(u:ℂ)*Complex.I) (by simpa using And.intro hσa hσ.2)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PublishedAngularHecke
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-angular primitive input, and its first contour consequence.
Rajan, Acta Arith. 85 (1998), Section 1, pp.281--282, gives the completed
unitary Hecke equation and entire order-one completion. Here the field
has one complex place, discriminant 3, and no imaginary norm parameter.
The Gamma shift is therefore |ell|/2. No smooth-sum estimate is an input. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

theorem angular_hecke_smooth_mellin_left (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {A k : ℝ} {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 1 ≤ Z) (m : ℕ) (t : ℝ) :
    (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W (((1/2-(m:ℝ)):ℝ)+(τ:ℂ)*Complex.I)*
          (Z:ℂ)^(((1/2-(m:ℝ)):ℝ)+(τ:ℂ)*Complex.I)*
          L (((1/2-(m:ℝ)):ℝ)+((τ-t:ℝ):ℂ)*Complex.I) := by
  obtain ⟨C,n,hC,hgrowth⟩ := data.strip_growth m
  have hshift := mellinHecke_contour_shift W hW hpos hsm
    (show 1/2-(m:ℝ) ≤ 2 by
      have hmr : (0:ℝ) ≤ m := by positivity
      linarith)
    hZ t L data.entire hC n (by intro σ hσ τ; exact hgrowth σ hσ (τ-t))
  norm_num only [Complex.ofReal_ofNat] at hshift
  rw [hecke_twisted_smooth_mellin χ hχ L data.right_series W hW hpos hsm
    (lt_of_lt_of_le zero_lt_one hZ) t,←hshift]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTruncatedDual
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact retained-plus-tail decomposition for a fixed angular Hecke
series. The possible poles of the totalized Gamma denominator are handled
using the entire completion, before any integration is performed. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma angular_left_uncompleted (χ χdual : EisensteinIdealExponent → ℂ)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    {m : ℕ} (hm : 2 ≤ m) (t τ : ℝ) :
    let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
    let u : ℂ := s-(t:ℂ)*Complex.I
    L u = ε*(A:ℂ)^(1-2*u)*angularGammaFEQuotient k u*
      normDirichletSeries χdual idealExponentNorm (1-u) := by
  dsimp only
  let u : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I
  have hre : (1-u).re = 1/2+(m:ℝ) := by dsimp [u]; simp; ring
  have hr : 1 < (1-u).re := by
    rw [hre]
    have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  by_cases hGu : Complex.Gamma (u+(k:ℂ)) = 0
  · obtain ⟨Λ,hΛ,heq,-⟩ := hcomp
    have hdec := shifted_completed_hecke_decompletion hA data.entire.continuous hΛ.continuous heq
    have hzero : L u = 0 := by
      rw [congrFun hdec u,hGu,inv_zero,mul_zero,zero_mul]
    change L u = _
    rw [hzero,angularGammaFEQuotient,hGu,div_zero,mul_zero,zero_mul]
  have hGd : Complex.Gamma (1-u+(k:ℂ)) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.add_re,Complex.ofReal_re]
    linarith
  have hf := hecke_uncompleted hA data.functional_equation u hGu hGd
  rw [data.dual_right_series _ hr] at hf
  exact hf

lemma angular_left_integrand_split (χ χdual : EisensteinIdealExponent → ℂ)
    (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1) {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k)
    {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (W : ℝ → ℂ) (Z J : ℝ) {m : ℕ} (hm : 2 ≤ m) (t τ : ℝ) :
    let s : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I
    mellin W s*(Z:ℂ)^s*L (s-(t:ℂ)*Complex.I) =
      mellin W s*(Z:ℂ)^s*angularFiniteHeckeDual (fullIdealBall J) χdual idealExponentNorm
        ε A k (s-(t:ℂ)*Complex.I) + angularDualTailIntegrand W χdual ε A Z J k m t τ := by
  dsimp only
  let u : ℂ := (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I
  have hr : 1 < (1-u).re := by
    have hre : (1-u).re = 1/2+(m:ℝ) := by dsimp [u]; simp; ring
    rw [hre]
    have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
    linarith
  rw [angular_left_uncompleted χ χdual hA hk data hcomp hm t τ,
    idealDirichlet_split χdual hχdual (1-u) hr J]
  dsimp [angularFiniteHeckeDual,angularDualTailIntegrand,angularGammaFEQuotient,u]
  ring

lemma angular_finite_dual_mellin_integrable {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (hN : ∀ i ∈ S, 1 ≤ N i)
    (ε : ℂ) {A b σ Z k : ℝ} (hk : 0 ≤ k) (hA : 0 < A) (hZ : 1 ≤ Z)
    (hσ : σ ∈ Icc b (1/2:ℝ)) (hGamma : AngularGammaQuotientStripBound k b)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    Integrable (fun τ : ℝ => mellin W (σ+(τ:ℂ)*Complex.I)*
      (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*angularFiniteHeckeDual S a N ε A k
        (σ+((τ-t:ℝ):ℂ)*Complex.I)) := by
  obtain ⟨C,n,hC,hbound⟩ := angular_finite_dual_strip_growth S a N hN ε hk hA hGamma
  apply mellinHecke_line_integrable W hW hpos hsm hZ σ t _ _ hC n
    (fun τ => hbound σ hσ (τ-t))
  apply (differentiableOn_angularFiniteHeckeDual S a N
    (fun i hi => lt_of_lt_of_le zero_lt_one (hN i hi)) ε hk hA).continuousOn.comp_continuous
    (by fun_prop)
  intro τ
  change ((σ:ℂ)+((τ-t:ℝ):ℂ)*Complex.I).re < 1
  simpa using lt_of_le_of_lt hσ.2 (by norm_num : (1/2:ℝ) < 1)

theorem angular_smooth_truncated_identity
    (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) (hχdual : ∀ ν, ‖χdual ν‖ ≤ 1)
    {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k) {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual)
    (hcomp : ShiftedCompletedHeckeFiniteOrder A k L)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 1 ≤ Z)
    {m : ℕ} (hm : 2 ≤ m) (J t : ℝ)
    (hGamma : AngularGammaQuotientStripBound k (1/2-(m:ℝ))) :
    (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*
        ((∫ τ : ℝ, mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          (Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          angularFiniteHeckeDual (fullIdealBall J) χdual idealExponentNorm ε A k
            ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)) +
        ∫ τ : ℝ, angularDualTailIntegrand W χdual ε A Z J k m t τ) := by
  let σ : ℝ := 1/2-(m:ℝ)
  let F (τ : ℝ) : ℂ := mellin W (σ+(τ:ℂ)*Complex.I)*
    (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*L (σ+((τ-t:ℝ):ℂ)*Complex.I)
  let D (τ : ℝ) : ℂ := mellin W (σ+(τ:ℂ)*Complex.I)*
    (Z:ℂ)^(σ+(τ:ℂ)*Complex.I)*angularFiniteHeckeDual (fullIdealBall J) χdual
      idealExponentNorm ε A k (σ+((τ-t:ℝ):ℂ)*Complex.I)
  let E (τ : ℝ) : ℂ := angularDualTailIntegrand W χdual ε A Z J k m t τ
  have hσ : σ ≤ 1/2 := by
    dsimp [σ]
    have hmr : (0:ℝ) ≤ m := by positivity
    linarith
  have hsplit (τ : ℝ) : F τ = D τ+E τ := by
    have h := angular_left_integrand_split χ χdual hχdual hA hk data hcomp W Z J hm t τ
    dsimp only at h
    have hs : ((σ:ℝ):ℂ)+(τ:ℂ)*Complex.I =
        (1/2:ℂ)-(m:ℂ)+(τ:ℂ)*Complex.I := by dsimp [σ]; push_cast; ring
    have hu : (σ:ℂ)+(τ:ℂ)*Complex.I-(t:ℂ)*Complex.I =
        (σ:ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
    rw [← hs,hu] at h
    exact h
  obtain ⟨C,n,hC,hgrowth⟩ := data.strip_growth m
  have hFi : Integrable F := by
    apply mellinHecke_line_integrable W hW hpos hsm hZ σ t L
      (data.entire.continuous.comp (by fun_prop)) hC n
    intro τ
    exact hgrowth σ ⟨le_rfl,hσ.trans (by norm_num)⟩ (τ-t)
  have hDi : Integrable D := angular_finite_dual_mellin_integrable (fullIdealBall J)
    χdual idealExponentNorm (fun ν _ => idealExponentNorm_ge_one ν) ε hk hA hZ
    ⟨le_rfl,hσ⟩ hGamma W hW hpos hsm t
  have hEi : Integrable E := (hFi.sub hDi).congr (Filter.Eventually.of_forall (fun τ => by
    have h := hsplit τ
    change F τ-D τ = E τ
    linear_combination h))
  have hi : (∫ τ : ℝ, F τ) = (∫ τ : ℝ, D τ)+(∫ τ : ℝ, E τ) := by
    calc
      _ = ∫ τ : ℝ, D τ+E τ := integral_congr_ae (Filter.Eventually.of_forall hsplit)
      _ = _ := integral_add hDi hEi
  have hmell := angular_hecke_smooth_mellin_left χ χdual hχ data W hW hpos hsm hZ m t
  change (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
    ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ, F τ) at hmell
  rw [hmell,hi]
  have hmove := angular_finite_dual_contour_shift (fullIdealBall J) χdual idealExponentNorm
    (fun ν _ => idealExponentNorm_ge_one ν) ε hk hA hZ hσ hGamma W hW hpos hsm t
  change (∫ τ : ℝ, D τ) = _ at hmove
  rw [hmove]


end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeMajorant
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common scalar majorant permits integration before the finite
character square-sum. The conductor and root number remain row scalars. -/

noncomputable section
open scoped BigOperators
open MeasureTheory
namespace CubicFirstMoment

theorem common_majorant_square_sum {ι : Type*} [Fintype ι]
    (F : ι → ℝ → ℂ) (w : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ i, Integrable (F i)) (hw : Integrable w)
    (hw0 : ∀ τ, 0 ≤ w τ)
    (hbound : ∀ τ, (∑ i, ‖F i τ‖^2) ≤ (w τ)^2*B) :
    (∑ i, ‖∫ τ : ℝ, F i τ‖^2) ≤ (∫ τ : ℝ, w τ)^2*B := by
  let v : ℝ → EuclideanSpace ℂ ι := fun τ => WithLp.toLp 2 (fun i => F i τ)
  have hpi : Integrable (fun τ => fun i => F i τ) := Integrable.of_eval hF
  have hv : Integrable v :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℂ)).symm.toContinuousLinearMap.integrable_comp hpi
  have hnorm (τ : ℝ) : ‖v τ‖ ≤ w τ * Real.sqrt B := by
    have he : ‖v τ‖^2 = ∑ i, ‖F i τ‖^2 := EuclideanSpace.norm_sq_eq (v τ)
    apply (sq_le_sq₀ (_root_.norm_nonneg _) (mul_nonneg (hw0 τ) (Real.sqrt_nonneg _))).mp
    rw [he,mul_pow,Real.sq_sqrt hB]
    exact hbound τ
  have hint : ‖∫ τ : ℝ, v τ‖ ≤ (∫ τ : ℝ, w τ)*Real.sqrt B := by
    calc
      _ ≤ ∫ τ : ℝ, ‖v τ‖ := norm_integral_le_integral_norm v
      _ ≤ ∫ τ : ℝ, w τ*Real.sqrt B := integral_mono hv.norm (hw.mul_const _) hnorm
      _ = _ := integral_mul_const _ _
  have hcoord (i : ι) : (∫ τ : ℝ, v τ) i = ∫ τ : ℝ, F i τ := by
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℂ) i).integral_comp_comm hv).symm
  have he : ‖∫ τ : ℝ, v τ‖^2 = ∑ i, ‖∫ τ : ℝ, F i τ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [hcoord]
  have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _) hint 2
  rw [he,mul_pow,Real.sq_sqrt hB] at hsq
  exact hsq

/-- A simultaneous character average can use one norm-shift measure:
the conductor-dependent Hecke factor contributes exactly no loss. -/
theorem hecke_common_majorant_square_sum {ι : Type*} [Fintype ι]
    (ε : ι → ℂ) (D : ι → ℝ) (Z k t : ℝ) (P W : ι → ℝ → ℂ)
    (w : ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hε : ∀ i, ‖ε i‖ = 1) (hk : 0 ≤ k)
    (hInt : ∀ i, Integrable (fun τ =>
      W i τ * heckeSymmetryFactor (ε i) (D i) Z k t τ * P i τ))
    (hw : Integrable w) (hw0 : ∀ τ, 0 ≤ w τ)
    (hW : ∀ i τ, ‖W i τ‖ ≤ w τ)
    (hP : ∀ τ, (∑ i, ‖P i τ‖^2) ≤ B) :
    (∑ i, ‖∫ τ : ℝ,
      W i τ * heckeSymmetryFactor (ε i) (D i) Z k t τ * P i τ‖^2) ≤
        (∫ τ : ℝ, w τ)^2*B := by
  apply common_majorant_square_sum _ w hB hInt hw hw0
  intro τ
  calc
    _ = ∑ i, ‖W i τ‖^2 * ‖P i τ‖^2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul,norm_mul,norm_heckeSymmetryFactor (hε i) _ _ _ _ _ hk,mul_one,mul_pow]
    _ ≤ ∑ i, (w τ)^2 * ‖P i τ‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (_root_.norm_nonneg _) (hW i τ) 2) (sq_nonneg _)
    _ = (w τ)^2 * ∑ i, ‖P i τ‖^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hP τ) (sq_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_IdealDualDyads
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact dyadic decomposition of the retained full-ideal polynomial.
The square-root normalization changes only coefficients, not characters. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealDyad_norm {S : Finset EisensteinIdealExponent} {j : ℕ}
    {ν : EisensteinIdealExponent} (hν : ν ∈ idealDyad S j) :
    (2:ℝ)^j ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*(2:ℝ)^j := by
  have hmem : idealExponentGenerator ν ∈ frequencyDyad j :=
    mem_frequencyDyad.mpr ⟨idealExponentGenerator_ne_zero ν,(Finset.mem_filter.mp hν).2⟩
  simpa only [idealExponentNorm,normNat_cast] using frequencyDyad_norm hmem

lemma finite_idealDirichlet_dyad_partition (S : Finset EisensteinIdealExponent)
    (χ : EisensteinIdealExponent → ℂ) (s : ℂ) :
    finiteNormDirichlet S χ idealExponentNorm s =
      ∑ j ∈ idealDyadIndices S, finiteNormDirichlet (idealDyad S j) χ idealExponentNorm s := by
  unfold finiteNormDirichlet idealDyadIndices idealDyad
  exact (Finset.sum_fiberwise_of_maps_to
    (fun ν hν => Finset.mem_image_of_mem idealDyadIndex hν) _).symm

lemma idealDyadIndices_card_le {J : ℝ} (S : Finset EisensteinIdealExponent)
    (hS : ∀ ν ∈ S, idealExponentNorm ν ≤ J) :
    (idealDyadIndices S).card ≤ Nat.log 2 ⌊J⌋₊+1 := by
  have hsub : idealDyadIndices S ⊆ Finset.range (Nat.log 2 ⌊J⌋₊+1) := by
    intro j hj
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hj
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.log_mono_right
    apply Nat.le_floor
    simpa only [normNat_cast,idealExponentNorm] using hS ν hν
  simpa only [Finset.card_range] using Finset.card_le_card hsub

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeckeDualMoment
attribute [-instance] _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer of a common bound for normalized dual polynomials to the
retained Hecke integrals. Root numbers and conductors only enter through
unit-modulus row factors. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma norm_normalization_sq {Z J : ℝ} (hZ : 0 < Z) (hJ : 0 < J) :
    ‖(Real.sqrt Z:ℂ)*(J^(-(1/2:ℝ)):ℝ)‖^2 = Z/J := by
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),abs_of_nonneg (Real.rpow_nonneg hJ.le _),
    mul_pow,Real.sq_sqrt hZ.le]
  have hp : (J^(-(1/2:ℝ)))^2 = J⁻¹ := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hJ.le]
    norm_num
    exact Real.rpow_neg_one J
  rw [hp,div_eq_mul_inv]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDualMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The shifted Gamma factor has unit modulus on the symmetry line.
Thus the actual angular retained integral obeys the same finite moment
transfer, with no angular loss in the sieve or conductor parameter. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma angularGammaQuotient_half_strip {k : ℝ} (hk : 0 ≤ k) :
    AngularGammaQuotientStripBound k (1/2) := by
  refine ⟨1,0,by norm_num,?_⟩
  intro σ hσ u
  have hσe : σ = 1/2 := le_antisymm hσ.2 hσ.1
  subst σ
  have he : angularGammaFEQuotient k ((1/2:ℝ)+(u:ℂ)*Complex.I) = heckeGammaRatio k u := by
    unfold angularGammaFEQuotient heckeGammaRatio
    push_cast
    congr 2 <;> ring
  rw [he,norm_heckeGammaRatio hk]
  simp

lemma angular_finite_dual_symmetry_integrand {ι : Type*} (S : Finset ι)
    (a : ι → ℂ) (N : ι → ℝ) (ε : ℂ) {A Z : ℝ} (hA : 0 < A) (hZ : 0 < Z)
    (k : ℝ) (G : ℂ → ℂ) (t τ : ℝ) :
    G ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual S a N ε A k ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
    (Real.sqrt Z:ℂ)*G ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      heckeSymmetryFactor ε (A^2) Z k t τ *
      finiteNormDirichlet S a N ((1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I) := by
  unfold angularFiniteHeckeDual angularGammaFEQuotient
  rw [hecke_scale_phase hZ,hecke_conductor_phase hA]
  have hu : 1-((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
      (1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I := by ring
  rw [hu]
  unfold heckeSymmetryFactor heckeGammaRatio
  push_cast
  have hn : (1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I+(k:ℂ) =
      ((k+1/2:ℝ):ℂ)-((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
  have hd : (1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I+(k:ℂ) =
      ((k+1/2:ℝ):ℂ)+((τ-t:ℝ):ℂ)*Complex.I := by push_cast; ring
  push_cast at hn hd
  rw [hn,hd]
  ring

lemma angularFiniteHeckeDual_integrand_normalized {ν : Type*} (S : Finset ν)
    (χ : ν → ℂ) (N : ν → ℝ) (hN : ∀ v ∈ S, 0 < N v)
    (ε : ℂ) (k : ℝ) {A Z J : ℝ} (hA : 0 < A) (hZ : 0 < Z) (hJ : 0 < J)
    (G : ℂ → ℂ) (t τ : ℝ) :
    G ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual S χ N ε A k ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I) =
    ((Real.sqrt Z:ℂ)*(J^(-(1/2:ℝ)):ℝ))*
      (G ((1/2:ℂ)+(τ:ℂ)*Complex.I)*heckeSymmetryFactor ε (A^2) Z k t τ*
        normalizedDualPolynomial S χ N J (τ-t)) := by
  rw [angular_finite_dual_symmetry_integrand S χ N ε hA hZ k G t τ,
    finite_dual_dyad_rescale S χ N hJ hN (τ-t)]
  unfold normalizedDualPolynomial
  ring

lemma integrable_angular_normalized_dual_kernel {ν : Type*} (S : Finset ν)
    (χ : ν → ℂ) (N : ν → ℝ) (hN : ∀ v ∈ S, 1 ≤ N v)
    (ε : ℂ) {k : ℝ} (hk : 0 ≤ k) {A Z J : ℝ} (hA : 0 < A) (hZ : 1 ≤ Z) (hJ : 0 < J)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (t : ℝ) :
    Integrable (fun τ : ℝ => mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      heckeSymmetryFactor ε (A^2) Z k t τ*normalizedDualPolynomial S χ N J (τ-t)) := by
  let κ : ℂ := (Real.sqrt Z:ℂ)*(J^(-(1/2:ℝ)):ℝ)
  have hκ : κ ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans_le hZ)).ne')
    (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hJ _).ne')
  have hi := angular_finite_dual_mellin_integrable S χ N hN ε hk hA hZ
    (σ := (1/2:ℝ)) (b := (1/2:ℝ)) ⟨le_rfl,le_rfl⟩ (angularGammaQuotient_half_strip hk) W hW hpos hsm t
  apply (hi.const_mul κ⁻¹).congr
  apply Filter.Eventually.of_forall
  intro τ
  have he := angularFiniteHeckeDual_integrand_normalized S χ N
    (fun v hv => zero_lt_one.trans_le (hN v hv)) ε k hA (zero_lt_one.trans_le hZ) hJ
    (mellin W) t τ
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at *
  rw [he,← mul_assoc,inv_mul_cancel₀ hκ,one_mul]

/-- Any common bound on the normalized dual polynomial square-sum gives
exactly the factor Z/J in the retained integral square-sum. The constant
is independent of the characters, conductors, root numbers and height. -/
theorem angular_retained_dual_moment_transfer {ν : Type*}
    (k : ℝ) (hk : 0 ≤ k)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι], ∀ (S : Finset ν) (χ : ι → ν → ℂ) (N : ν → ℝ),
      (∀ v ∈ S, 1 ≤ N v) → ∀ (ε : ι → ℂ) (A : ι → ℝ),
      (∀ i, ‖ε i‖ = 1) → (∀ i, 0 < A i) → ∀ (Z J t B : ℝ),
      1 ≤ Z → 0 < J → 0 ≤ B →
      (∀ τ : ℝ, (∑ i, ‖normalizedDualPolynomial S (χ i) N J (τ-t)‖^2) ≤ B) →
      (∑ i, ‖((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          angularFiniteHeckeDual S (χ i) N (ε i) (A i) k
            ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)‖^2) ≤ C*(Z/J)*B := by
  obtain ⟨K,hK,hbound⟩ := mellin_polynomial_majorant W hW hpos hsm (1/2) 0
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)
  let w : ℝ → ℝ := mellinEdgeMajorant K
  refine ⟨‖c‖^2*(∫ τ : ℝ, w τ)^2,by positivity,?_⟩
  intro ι inst S χ N hN ε A hε hA Z J t B hZ hJ hB hP
  let G (i : ι) (τ : ℝ) := mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
    heckeSymmetryFactor (ε i) ((A i)^2) Z k t τ*
      normalizedDualPolynomial S (χ i) N J (τ-t)
  have hi : ∀ i, Integrable (G i) := fun i =>
    integrable_angular_normalized_dual_kernel S (χ i) N hN (ε i) hk (hA i) hZ hJ W hW hpos hsm t
  have hmass : (∑ i, ‖∫ τ : ℝ, G i τ‖^2) ≤ (∫ τ : ℝ, w τ)^2*B := by
    apply hecke_common_majorant_square_sum ε (fun i => (A i)^2) Z k t
      (fun i τ => normalizedDualPolynomial S (χ i) N J (τ-t))
      (fun _ τ => mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)) w hB hε hk hi
      (mellinEdgeMajorant_integrable K) (fun τ => by dsimp [w,mellinEdgeMajorant]; positivity)
    · intro i τ
      simpa only [pow_zero,mul_one,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
        using hbound 0 τ
    · exact hP
  have he (i : ι) :
      ((1/(2*Real.pi):ℝ):ℂ)*(∫ τ : ℝ,
        mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          angularFiniteHeckeDual S (χ i) N (ε i) (A i) k
            ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)) =
      (c*((Real.sqrt Z:ℂ)*(J^(-(1/2:ℝ)):ℝ)))*(∫ τ : ℝ, G i τ) := by
    simp_rw [angularFiniteHeckeDual_integrand_normalized S (χ i) N
      (fun v hv => zero_lt_one.trans_le (hN v hv)) (ε i) k (hA i) (zero_lt_one.trans_le hZ) hJ]
    rw [integral_const_mul]
    dsimp [c,G]
    ring
  have henorm (i : ι) :
      ‖((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          angularFiniteHeckeDual S (χ i) N (ε i) (A i) k
            ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)‖^2 =
      (‖c‖^2*(Z/J))*‖∫ τ : ℝ, G i τ‖^2 := by
    rw [he,norm_mul,mul_pow]
    congr 1
    rw [norm_mul,mul_pow,norm_normalization_sq (zero_lt_one.trans_le hZ) hJ]
  simp_rw [henorm]
  rw [← Finset.mul_sum]
  calc
    _ ≤ (‖c‖^2*(Z/J))*((∫ τ : ℝ, w τ)^2*B) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularDyadicMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite dyadic splitting of the retained dual integral and the
resulting character-average bound. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finiteAngularIdealDualIntegral_dyad_partition (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    (S : Finset EisensteinIdealExponent) (χ : EisensteinIdealExponent → ℂ)
    (ε : ℂ) {k : ℝ} (hk : 0 ≤ k) {A Z : ℝ} (hA : 0 < A) (hZ : 1 ≤ Z) (t : ℝ) :
    finiteAngularDualIntegral W S χ idealExponentNorm ε A k Z t =
      ∑ j ∈ idealDyadIndices S, finiteAngularDualIntegral W (idealDyad S j) χ idealExponentNorm ε A k Z t := by
  let F (T : Finset EisensteinIdealExponent) (τ : ℝ) :=
    mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual T χ idealExponentNorm ε A k ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)
  have hf (τ : ℝ) : F S τ = ∑ j ∈ idealDyadIndices S, F (idealDyad S j) τ := by
    dsimp [F,angularFiniteHeckeDual]
    rw [finite_idealDirichlet_dyad_partition]
    simp only [Finset.mul_sum]
  have hi (j : ℕ) : Integrable (F (idealDyad S j)) := by
    simpa only [F,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      angular_finite_dual_mellin_integrable (idealDyad S j) χ idealExponentNorm
      (fun ν _ => idealExponentNorm_ge_one ν) ε hk hA hZ
      (σ := (1/2:ℝ)) (b := (1/2:ℝ)) ⟨le_rfl,le_rfl⟩ (angularGammaQuotient_half_strip hk) W hW hpos hsm t
  unfold finiteAngularDualIntegral
  rw [← Finset.mul_sum]
  congr 1
  change (∫ τ : ℝ, F S τ) = ∑ j ∈ idealDyadIndices S, ∫ τ : ℝ, F (idealDyad S j) τ
  rw [show F S = fun τ => ∑ j ∈ idealDyadIndices S, F (idealDyad S j) τ from funext hf]
  exact integral_finsetSum _ (fun j _ => hi j)

/-- A bound for each actual normalized ideal dyad transfers to the
whole retained integral with only its finite number of dyads lost. -/
theorem angular_retained_ideal_dyadic_moment_transfer
    (k : ℝ) (hk : 0 ≤ k)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι], ∀ (S : Finset EisensteinIdealExponent)
      (χ : ι → EisensteinIdealExponent → ℂ) (ε : ι → ℂ) (A : ι → ℝ),
      (∀ i, ‖ε i‖ = 1) → (∀ i, 0 < A i) → ∀ (Z t : ℝ) (B : ℕ → ℝ),
      1 ≤ Z → (∀ j ∈ idealDyadIndices S, 0 ≤ B j) →
      (∀ j ∈ idealDyadIndices S, ∀ τ : ℝ,
        (∑ i, ‖normalizedDualPolynomial (idealDyad S j) (χ i) idealExponentNorm
          ((2:ℝ)^j) (τ-t)‖^2) ≤ B j) →
      (∑ i, ‖finiteAngularDualIntegral W S (χ i) idealExponentNorm (ε i) (A i) k Z t‖^2) ≤
        (idealDyadIndices S).card * C *
          ∑ j ∈ idealDyadIndices S, (Z/(2:ℝ)^j)*B j := by
  obtain ⟨C,hC,hbound⟩ := angular_retained_dual_moment_transfer
    (ν := EisensteinIdealExponent) k hk W hW hpos hsm
  refine ⟨C,hC,?_⟩
  intro ι inst S χ ε A hε hA Z t B hZ hB hP
  let F (i : ι) (j : ℕ) := finiteAngularDualIntegral W (idealDyad S j) (χ i) idealExponentNorm (ε i) (A i) k Z t
  have hsplit (i : ι) : finiteAngularDualIntegral W S (χ i) idealExponentNorm (ε i) (A i) k Z t =
      ∑ j ∈ idealDyadIndices S, F i j :=
    finiteAngularIdealDualIntegral_dyad_partition W hW hpos hsm S (χ i) (ε i) hk (hA i) hZ t
  simp_rw [hsplit]
  have hcauchy := complex_mass_sum_sq_le (idealDyadIndices S) (Finset.univ : Finset ι) F
  apply hcauchy.trans
  calc
    _ ≤ (idealDyadIndices S).card * ∑ j ∈ idealDyadIndices S, C*(Z/(2:ℝ)^j)*B j := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro j hj
      exact hbound (idealDyad S j) χ idealExponentNorm (fun ν _ => idealExponentNorm_ge_one ν)
        ε A hε hA Z ((2:ℝ)^j) t (B j) hZ (by positivity) (hB j hj) (hP j hj)
    _ = _ := by rw [Finset.mul_sum]; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryIdealMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sieve moments of the actual primary-normalized ideal character.
The primary representative and the ramified zero are retained explicitly. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryMixedIdealChar_eq (a b : Eisenstein) (ν : EisensteinIdealExponent) :
    primaryMixedIdealChar a b ν =
      if primary (idealPrimaryGenerator ν) then
        mixedCubic a b (idealPrimaryGenerator ν) else 0 := by
  unfold primaryMixedIdealChar primaryMixedLift idealPrimaryGenerator
  by_cases h : IsUnit (Ideal.Quotient.mk (modulus 3) (idealExponentGenerator ν))
  · rw [ite_eq_left h,ite_eq_left (primaryNormalize_primary h)]
  · rw [ite_eq_right h,ite_eq_right]
    intro hp
    exact h (unit_residue_of_dvd_primary hp (primaryNormalize_associated _).dvd)

/-- The normalized ideal character is sieved with the exact primary
representative. A fixed mixed factor and any fixed bounded coefficient
twist are allowed, including the ramified local factors. -/
theorem normalized_primary_ideal_cubic_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (S : Finset EisensteinIdealExponent)
      (b : Eisenstein) (ξ : EisensteinIdealExponent → ℂ) (N Y J u : ℝ),
      primary b → (∀ ν ∈ S, ‖ξ ν‖ ≤ 1) → 1 ≤ N → 1 ≤ Y → 0 < J →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N) →
      (∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ Y) →
      (∑ a ∈ P, ‖normalizedDualPolynomial S
        (fun ν => ξ ν*primaryMixedIdealChar a b ν) idealExponentNorm J u‖^2) ≤
        C*(N*Y)^ε*Y*(N+Y+(N*Y)^(2/3:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := bounded_cubic_moment hε
  refine ⟨C,hC,?_⟩
  intro P S b ξ N Y J u hb hξ hN hY hJ hP hS
  let T := S.image idealPrimaryGenerator
  let v : Eisenstein → ℂ := fun n => if primary n then
    ξ (idealExponentOf n)*(((J/norm n)^(1/2:ℝ):ℝ)*mellinPhase u (norm n))*
      star (cubicSymbol b n) else 0
  have hT : ∀ n ∈ T, n ≠ 0 ∧ norm n ≤ Y := by
    intro n hn
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hn
    exact ⟨(primaryNormalize_associated _).ne_zero_iff.mp (idealExponentGenerator_ne_zero ν),
      (idealPrimaryGenerator_norm ν).trans_le (hS ν hν).2⟩
  have hv : ∀ n ∈ T, ‖v n‖ ≤ 1 := by
    intro n hn
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hn
    dsimp only [v]
    split
    · rw [idealExponentOf_primaryGenerator,idealPrimaryGenerator_norm,norm_mul,norm_mul,
        norm_mul,norm_star,mellinPhase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (div_nonneg hJ.le (idealExponentNorm_pos ν).le) _)]
      have hw := dual_dyad_weight_le_one hJ (hS ν hν).1
      have hc := norm_cubicSymbol_le_one hb (idealPrimaryGenerator ν)
      have hx := hξ ν hν
      have hxw : ‖ξ ν‖*(J/idealExponentNorm ν)^(1/2:ℝ) ≤ 1 := by
        simpa using mul_le_mul hx hw (Real.rpow_nonneg (div_nonneg hJ.le (idealExponentNorm_pos ν).le) _) zero_le_one
      exact (mul_le_mul hxw hc (_root_.norm_nonneg _) zero_le_one).trans_eq (by norm_num)
    · simp
  have heq (a : Eisenstein) :
      normalizedDualPolynomial S (fun ν => ξ ν*primaryMixedIdealChar a b ν)
        idealExponentNorm J u = ∑ n ∈ T, v n*cubicSymbol a n := by
    rw [Finset.sum_image (fun ν _ κ _ h => idealPrimaryGenerator_injective h)]
    unfold normalizedDualPolynomial
    apply Finset.sum_congr rfl
    intro ν hν
    dsimp only [v]
    rw [idealExponentOf_primaryGenerator,idealPrimaryGenerator_norm,primaryMixedIdealChar_eq]
    split_ifs
    · unfold mixedCubic
      ring
    · simp
  simp_rw [heq]
  simpa only [one_pow,mul_one] using hbound P T N Y 1 hN hY zero_le_one hP hT v hv

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ConductorLocal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local detection of the squarefree cubic conductor. A nontrivial
prime character survives every inducing modulus, as witnessed by CRT. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma cubicSymbol_eq_one_of_dvd_sub {q x : Eisenstein}
    (hq : primary q) (hx : q ∣ x-1) : cubicSymbol q x = 1 := by
  rw [cubicSymbol_congr (residue_eq_of_dvd_sub hx)]
  exact (cubic_reciprocity hq (by norm_num [primary])).trans (cubicSymbol_one_lower q)

lemma squarefree_primary_dvd_of_prime_dvd {a d : Eisenstein} (ha : primary a)
    (hsa : Squarefree a)
    (hprime : ∀ p : Eisenstein, primaryPrime p → p ∣ a → p ∣ d) : a ∣ d := by
  apply (primary_induction (P := fun a => Squarefree a →
    (∀ p : Eisenstein, primaryPrime p → p ∣ a → p ∣ d) → a ∣ d) ?_ ?_ ha) hsa hprime
  · intro _ _
    exact one_dvd d
  · intro p c hp hc ih hsf hall
    have hpd : p ∣ d := hall p hp (dvd_mul_right p c)
    have hcd : c ∣ d := ih hsf.of_mul_right (fun r hr hrc =>
      hall r hr (hrc.trans (dvd_mul_left c p)))
    exact (IsRelPrime.of_squarefree_mul hsf).mul_dvd hpd hcd

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

lemma idealExponent_exponent_bound {ν : EisensteinIdealExponent} {J : ℝ}
    (hν : idealExponentNorm ν ≤ J) (p : EisensteinIdealPrime) :
    ν p ≤ Nat.log 2 ⌊J⌋₊ := by
  have hsingle : Finsupp.single p (ν p) ≤ ν := Finsupp.single_le_iff.mpr le_rfl
  have hN := norm_le_of_dvd (idealExponentGenerator_ne_zero ν)
    (idealExponentGenerator_dvd_of_le hsingle)
  have hpow : (2:ℝ)^(ν p) ≤ idealExponentNorm ν := by
    calc
      _ ≤ (normNat (idealPrimeRepresentative p):ℝ)^(ν p) :=
        pow_le_pow_left₀ (by norm_num) (by exact_mod_cast idealPrimeRepresentative_normNat_ge_two p) _
      _ = idealExponentNorm (Finsupp.single p (ν p)) := (idealExponentNorm_single _ _).symm
      _ ≤ idealExponentNorm ν := by simpa only [idealExponentNorm,normNat_cast] using hN
  apply Nat.le_log_of_pow_le (by norm_num)
  apply Nat.le_floor
  exact_mod_cast hpow.trans hν

lemma mellinPhase_mul_pos (u : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    mellinPhase u (x*y) = mellinPhase u x*mellinPhase u y := by
  unfold mellinPhase
  rw [Real.log_mul hx.ne' hy.ne',mul_add,Complex.ofReal_add,add_mul,Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimitiveDualMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic second moments for the actual primitive ideal characters.
The primes above three are separated exactly before applying the cubic sieve. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma angularResidueIdealChar_primaryNormalize {d : Eisenstein}
    (ψ : MulChar (Residues d) ℂ) {ℓ : ℤ} (hu : AngularUnitCompatible d ψ ℓ)
    (ν : EisensteinIdealExponent) :
    angularResidueIdealChar d ψ ℓ ν =
      ψ (Ideal.Quotient.mk (modulus d) (idealPrimaryGenerator ν))*
        theta ℓ (idealPrimaryGenerator ν) :=
  angular_character_associated ψ hu
    (primaryNormalize_associated (idealExponentGenerator ν))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryDualMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing the actual cubic dual dyads. The conductor and root-number
phases are outside the polynomials, and the dyadic loss is explicit. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealDyadIndex_scale_le {J : ℝ} {j : ℕ}
    (hj : j ∈ idealDyadIndices (fullIdealBall J)) : (2:ℝ)^j ≤ J := by
  obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hj
  exact (idealDyad_norm (show ν ∈ idealDyad (fullIdealBall J) (idealDyadIndex ν) from
    Finset.mem_filter.mpr ⟨hν,rfl⟩)).1.trans (mem_fullIdealBall.mp hν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimitiveDualConjugation
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conjugation preserves the normalized dual moment and reverses the
Mellin height. Thus the cubic sieve controls the actual dual coefficients. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma star_mellinPhase (u x : ℝ) : star (mellinPhase u x) = mellinPhase (-u) x := by
  change (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul,Complex.ofReal_neg]
  ring

lemma star_normalizedDualPolynomial {ν : Type*} (S : Finset ν) (χ : ν → ℂ)
    (N : ν → ℝ) (J u : ℝ) :
    star (normalizedDualPolynomial S χ N J u) =
      normalizedDualPolynomial S (fun v => star (χ v)) N J (-u) := by
  simp only [normalizedDualPolynomial,star_sum,star_mul,star_mellinPhase,
    Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro v hv
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularPrimitiveRetainedMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained functional-equation integrals of the actual primitive
characters have the cubic second moment, with explicit logarithmic losses. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_angular_dual_conjugate {q : Eisenstein} (ψ : MulChar (Residues q) ℂ)
    (ℓ : ℤ) (S : Finset EisensteinIdealExponent) (J u : ℝ) :
    ‖normalizedDualPolynomial S (angularResidueIdealChar q (star ψ) (-ℓ))
      idealExponentNorm J u‖ =
    ‖normalizedDualPolynomial S (angularResidueIdealChar q ψ ℓ)
      idealExponentNorm J (-u)‖ := by
  rw [← norm_star (normalizedDualPolynomial S (angularResidueIdealChar q ψ ℓ)
    idealExponentNorm J (-u)), star_normalizedDualPolynomial,neg_neg]
  congr 2
  funext ν
  exact (star_angularResidueIdealChar q ψ ℓ ν).symm

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularSmoothApproximation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform smooth dual approximation at each fixed infinity type,
derived from the precise published completion and classical Gamma
inputs. The original sum retains every primitive local Euler factor. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

/-- Uniform arbitrary-power approximation beyond the natural dual
length. The original sum and retained integral are explicitly defined. -/
theorem angular_smooth_approximation
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {k : ℝ} (hk : 0 ≤ k) {δ : ℝ} (hδ : 0 < δ) (B R : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 2 ≤ m ∧ 0 ≤ C ∧
      ∀ (χ χdual : EisensteinIdealExponent → ℂ),
      (∀ ν, ‖χ ν‖ ≤ 1) → (∀ ν, ‖χdual ν‖ ≤ 1) →
      ∀ (ε : ℂ), ‖ε‖ ≤ 1 → ∀ (Y A Z J t : ℝ),
      1 ≤ Y → 0 < A → 1 ≤ Z → 0 < J → Z ≤ Y^B → J ≤ Y^B →
      (A^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ∀ (L Ldual : ℂ → ℂ), ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual →
      ShiftedCompletedHeckeFiniteOrder A k L →
      AngularGammaQuotientStripBound k (1/2-(m:ℝ)) →
      ‖(∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) -
        angularRetainedIntegral W χdual ε A k Z J t‖ ≤ C*Y^(-R) := by
  obtain ⟨m,C,hm,hC,hbound⟩ := angular_dual_tail_arbitrary_power W hW hpos hsm hk hδ B R
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)
  refine ⟨m,‖c‖*C,hm,mul_nonneg (_root_.norm_nonneg _) hC,?_⟩
  intro χ χdual hχ hχdual ε hε Y A Z J t hY hA hZ hJ hZB hJB hcut L Ldual data hcomp hGamma
  have he := angular_smooth_truncated_identity χ χdual hχ hχdual hA hk data hcomp W hW hpos hsm hZ hm J t hGamma
  have hid : (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) -
      angularRetainedIntegral W χdual ε A k Z J t =
      c*(∫ τ : ℝ, angularDualTailIntegrand W χdual ε A Z J k m t τ) := by
    dsimp [angularRetainedIntegral,c]
    linear_combination he
  rw [hid,norm_mul]
  calc
    _ ≤ ‖c‖*(C*Y^(-R)) := mul_le_mul_of_nonneg_left
      (hbound χdual hχdual ε hε Y A Z J hY hA (zero_lt_one.trans_le hZ) hJ hZB hJB t hcut)
      (_root_.norm_nonneg _)
    _ = _ := by ring


/-- Actual primitive angular characters satisfy the proved approximation.
The constant is chosen before the modulus, character, root and lengths. -/
theorem primitive_angular_smooth_approximation (hpub : PrimitiveAngularHeckeInput)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder
      (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Eisenstein), q ≠ 0 →
      ∀ χ : MulChar (Residues q) ℂ, PrimitiveResidueCharacter q χ →
      AngularUnitCompatible q χ ℓ → (ℓ ≠ 0 ∨ χ ≠ 1) →
      ∃ root : ℂ, ‖root‖ = 1 ∧ ∀ (Y Z J t : ℝ),
      1 ≤ Y → 1 ≤ Z → 0 < J → Z ≤ Y^H → J ≤ Y^H →
      ((residueHeckeScale q)^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ‖(∑' ν, angularResidueIdealChar q χ ℓ ν*mellinPhase t (idealExponentNorm ν)*
          W (idealExponentNorm ν/Z))-
        angularRetainedIntegral W (angularResidueIdealChar q (star χ) (-ℓ)) root
          (residueHeckeScale q) (|(ℓ:ℝ)|/2) Z J t‖ ≤ C*Y^(-R) := by
  have hk : 0 ≤ |(ℓ:ℝ)|/2 := by positivity
  obtain ⟨m,C,hm,hC,hbound⟩ := angular_smooth_approximation W hW hpos hsm hk hδ H R
  refine ⟨C,hC,?_⟩
  intro q hq χ hp hu hn
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub ℓ q hq χ hp hu hn
  have hχ := angularResidueIdealChar_norm_le_one hq χ ℓ
  have hχdual := angularResidueIdealChar_norm_le_one hq (star χ) (-ℓ)
  have data := shifted_hecke_analyticData_of_completed hχ hχdual
    (residueHeckeScale_pos hq) hk hL hs hds hFE hcomp hGI
  refine ⟨root,hr,?_⟩
  intro Y Z J t hY hZ hJ hZH hJH hcut
  exact hbound _ _ hχ hχdual root hr.le Y (residueHeckeScale q) Z J t hY
    (residueHeckeScale_pos hq) hZ hJ hZH hJH hcut L Ldual data hcomp (hGQ m)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SupportedIdealParts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the primes of an arbitrary nonzero modulus. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma supportedIdealPart_norm_le (v : Eisenstein) (ν : EisensteinIdealExponent) :
    idealExponentNorm (supportedIdealPart v ν) ≤ idealExponentNorm ν := by
  simpa only [idealExponentNorm,normNat_cast] using
    norm_le_of_dvd (idealExponentGenerator_ne_zero ν)
      (idealExponentGenerator_dvd_of_le (supportedIdealPart_le v ν))

lemma outsideIdealPart_primary {v : Eisenstein} (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v)
    (ν : EisensteinIdealExponent) : primary (idealPrimaryGenerator (outsideIdealPart v ν)) := by
  rw [idealPrimaryGenerator_primary_iff]
  intro p hp
  have hle := idealExponentOf_le_of_dvd (by norm_num : (3:Eisenstein) ≠ 0) hv h3
  have hpin : p ∈ (idealExponentOf v).support := Finsupp.mem_support_iff.mpr (by
    have hp3 := Finsupp.mem_support_iff.mp hp
    have h := hle p
    omega)
  have hne := Finsupp.mem_support_iff.mp hpin
  simp [outsideIdealPart,hne]

lemma outsideIdealPart_coprime {v : Eisenstein} (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v)
    (ν : EisensteinIdealExponent) : IsCoprime (idealPrimaryGenerator (outsideIdealPart v ν)) v := by
  rw [isCoprime_iff_idealExponent_disjoint
    (primary_ne_zero (outsideIdealPart_primary hv h3 ν)) hv,idealExponentOf_primaryGenerator]
  intro p
  by_cases hp : p ∈ (idealExponentOf v).support
  · left
    have hne := Finsupp.mem_support_iff.mp hp
    simp [outsideIdealPart,hne]
  · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

lemma sum_outsideFiber (v : Eisenstein) (S : Finset EisensteinIdealExponent)
    (ρ : EisensteinIdealExponent) (f : EisensteinIdealExponent → ℂ) :
    (∑ κ ∈ outsideFiber v S ρ, f (ρ+κ)) =
      ∑ ν ∈ S.filter (fun ν => supportedIdealPart v ν = ρ), f ν := by
  unfold outsideFiber
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro ν hν
    rw [← (Finset.mem_filter.mp hν).2,supported_add_outside]
  · intro ν hν κ hκ he
    have hn := supported_add_outside v ν
    have hk := supported_add_outside v κ
    rw [(Finset.mem_filter.mp hν).2,he] at hn
    rw [(Finset.mem_filter.mp hκ).2] at hk
    exact hn.symm.trans hk

lemma ideal_sum_supported_partition (v : Eisenstein) (S : Finset EisensteinIdealExponent)
    (f : EisensteinIdealExponent → ℂ) :
    (∑ ν ∈ S, f ν) = ∑ ρ ∈ supportedParts v S, ∑ κ ∈ outsideFiber v S ρ, f (ρ+κ) := by
  simp_rw [sum_outsideFiber]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun ν hν => Finset.mem_image_of_mem (supportedIdealPart v) hν) _).symm

 theorem normalizedDualPolynomial_supported_partition
    (v : Eisenstein) (S : Finset EisensteinIdealExponent) (χ : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν κ, χ (ν+κ) = χ ν*χ κ) (J u : ℝ) :
    normalizedDualPolynomial S χ idealExponentNorm J u =
      ∑ ρ ∈ supportedParts v S, (χ ρ*mellinPhase u (idealExponentNorm ρ))*
        normalizedDualPolynomial (outsideFiber v S ρ) χ idealExponentNorm
          (J/idealExponentNorm ρ) u := by
  unfold normalizedDualPolynomial
  rw [ideal_sum_supported_partition v]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro κ hκ
  rw [hχ,idealExponentNorm_add,div_mul_eq_div_div,
    mellinPhase_mul_pos u (idealExponentNorm_pos ρ) (idealExponentNorm_pos κ)]
  ring

lemma outsideFiber_primary {v : Eisenstein} (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v)
    {S : Finset EisensteinIdealExponent} {ρ κ : EisensteinIdealExponent} (hκ : κ ∈ outsideFiber v S ρ) :
    primary (idealPrimaryGenerator κ) := by
  obtain ⟨ν,_,rfl⟩ := Finset.mem_image.mp hκ
  exact outsideIdealPart_primary hv h3 ν

lemma outsideFiber_coprime {v : Eisenstein} (hv : v ≠ 0) (h3 : (3:Eisenstein) ∣ v)
    {S : Finset EisensteinIdealExponent} {ρ κ : EisensteinIdealExponent} (hκ : κ ∈ outsideFiber v S ρ) :
    IsCoprime (idealPrimaryGenerator κ) v := by
  obtain ⟨ν,_,rfl⟩ := Finset.mem_image.mp hκ
  exact outsideIdealPart_coprime hv h3 ν

lemma outsideFiber_norm {v : Eisenstein} {S : Finset EisensteinIdealExponent} {J : ℝ}
    (hS : ∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*J)
    {ρ κ : EisensteinIdealExponent} (hκ : κ ∈ outsideFiber v S ρ) :
    J/idealExponentNorm ρ ≤ idealExponentNorm κ ∧
      idealExponentNorm κ ≤ (2*J)/idealExponentNorm ρ := by
  obtain ⟨ν,hν,hκν⟩ := Finset.mem_image.mp hκ
  obtain ⟨hνS,hνρ⟩ := Finset.mem_filter.mp hν
  have hn : idealExponentNorm ν = idealExponentNorm ρ*idealExponentNorm κ := by
    rw [← supported_add_outside v ν,idealExponentNorm_add,hνρ,hκν]
  constructor
  · exact (div_le_iff₀ (idealExponentNorm_pos ρ)).mpr (by simpa [mul_comm,← hn] using (hS ν hνS).1)
  · exact (le_div_iff₀ (idealExponentNorm_pos ρ)).mpr (by simpa [mul_comm,← hn] using (hS ν hνS).2)

lemma supportedPart_norm_le_upper {v : Eisenstein} {S : Finset EisensteinIdealExponent} {J : ℝ}
    (hS : ∀ ν ∈ S, idealExponentNorm ν ≤ 2*J)
    {ρ : EisensteinIdealExponent} (hρ : ρ ∈ supportedParts v S) :
    1 ≤ (2*J)/idealExponentNorm ρ := by
  obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hρ
  apply (le_div_iff₀ (idealExponentNorm_pos _)).mpr
  simpa only [one_mul] using (supportedIdealPart_norm_le v ν).trans (hS ν hν)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedConductor
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variable squarefree conductor survives multiplication by a fixed
character of coprime small modulus. Detection is by explicit local CRT. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem twisted_conductor_left_prime {a b d p r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r) (hp : primaryPrime p) (hpa : p ∣ a)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) : p ∣ d := by
  by_contra hpd
  obtain ⟨c,rfl⟩ := hpa
  have hc : primary c := primary_of_mul hp.1 ha
  have hpc : IsCoprime p c := (IsRelPrime.of_squarefree_mul hsa).isCoprime
  have hpb : IsCoprime p b := hab.of_mul_left_left
  have hpd' : IsCoprime p d := hp.2.irreducible.coprime_iff_not_dvd.mpr hpd
  have hpr : IsCoprime p r := hsmall.of_mul_left_left.of_mul_left_left
  let Q := 3*c*b*d*r
  have hpQ : IsCoprime p Q :=
    ((((primary_coprime_three hp.1).mul_right hpc).mul_right hpb).mul_right hpd').mul_right hpr
  obtain ⟨u,hu⟩ := MulChar.ne_one_iff.mp (cubicResidueChar_ne_one hp)
  obtain ⟨y,hy⟩ := Ideal.Quotient.mk_surjective (u : Residues p)
  obtain ⟨x,hxp,hxQ⟩ := residue_crt_one hpQ y
  have hx3 : (3:Eisenstein) ∣ x-1 := (show (3:Eisenstein) ∣ Q from ⟨c*b*d*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxc : c ∣ x-1 := (show c ∣ Q from ⟨3*b*d*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxb : b ∣ x-1 := (show b ∣ Q from ⟨3*c*d*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxd : d ∣ x-1 := (show d ∣ Q from ⟨3*c*b*r,by dsimp [Q]; ring⟩).trans hxQ
  have hxr : r ∣ x-1 := (show r ∣ Q from ⟨3*c*b*d,by dsimp [Q]; ring⟩).trans hxQ
  have hrx := isCoprime_of_dvd_sub_one hxr
  have hη : η (Ideal.Quotient.mk (modulus r) x) = 1 := by
    rw [residue_eq_of_dvd_sub hxr,map_one,map_one]
  have hxp' : Ideal.Quotient.mk (modulus p) x = u :=
    (residue_eq_of_dvd_sub hxp).trans hy
  have hpx : IsCoprime p x := isCoprime_of_residue_isUnit (by rw [hxp']; exact u.isUnit)
  have hcx := isCoprime_of_dvd_sub_one hxc
  have hbx := isCoprime_of_dvd_sub_one hxb
  have hval := hagree x hx3 (((hpx.mul_left hcx).mul_left hbx).mul_left hrx)
  have hψ : ψ (Ideal.Quotient.mk (modulus d) x) = 1 := by
    rw [residue_eq_of_dvd_sub hxd,map_one,map_one]
  rw [hψ,hη,mul_one,mixedCubic,cubicSymbol_mul_lower hp.2.ne_zero (primary_ne_zero hc),
    cubicSymbol_eq_one_of_dvd_sub hc hxc,cubicSymbol_eq_one_of_dvd_sub hb hxb,
    star_one,mul_one,mul_one,cubicSymbol_prime hp,← cubicResidueChar_mk p hp,hxp'] at hval
  exact hu hval.symm


theorem twisted_conductor_contains {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) :
    a*b ∣ d := by
  have had : a ∣ d := squarefree_primary_dvd_of_prime_dvd ha hsa
    (fun p hp hpa => twisted_conductor_left_prime ha hb hsa hab hsmall hp hpa ψ η hagree)
  have hswap : ∀ x : Eisenstein, primary x → IsCoprime (b*a*r) x →
      (star ψ) (Ideal.Quotient.mk (modulus d) x) =
        mixedCubic b a x*(star η) (Ideal.Quotient.mk (modulus r) x) := by
    intro x hx hcop
    rw [MulChar.star_apply,hagree x hx (by simpa only [mul_comm] using hcop)]
    simp only [mixedCubic,star_mul,star_star,MulChar.star_apply]
    ring
  have hbd : b ∣ d := squarefree_primary_dvd_of_prime_dvd hb hsb
    (fun p hp hpb => twisted_conductor_left_prime hb ha hsb hab.symm
      (by simpa only [mul_comm] using hsmall) hp hpb (star ψ) (star η) hswap)
  exact hab.isRelPrime.mul_dvd had hbd

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedIdealMatch
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Agreement with the actual small-twisted mixed coefficients outside
three and the small modulus, including every common zero. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma twisted_character_primary_match {a b d r x : Eisenstein}
    (ha : primary a) (hb : primary b) (ψ : MulChar (Residues d) ℂ)
    (η : MulChar (Residues r) ℂ) (hdiv : a*b ∣ d)
    (hagree : ∀ y : Eisenstein, primary y → IsCoprime (a*b*r) y →
      ψ (Ideal.Quotient.mk (modulus d) y) = mixedCubic a b y*η (Ideal.Quotient.mk (modulus r) y))
    (hx : primary x) (hxr : IsCoprime r x) :
    ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x) := by
  by_cases hcop : IsCoprime (a*b) x
  · exact hagree x hx (hcop.mul_left hxr)
  · have hz : mixedCubic a b x = 0 := mixedCubic_eq_zero_of_nonunit ha hb x
      (fun h => hcop (isCoprime_of_residue_isUnit h))
    rw [hz,zero_mul]
    apply MulChar.map_nonunit
    intro h
    exact hcop ((isCoprime_of_residue_isUnit h).of_isCoprime_of_dvd_left hdiv)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedIdealMatch
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Agreement with the actual small-twisted mixed coefficients outside
three and the small modulus, including every common zero. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma angular_twisted_ideal_mixed_match {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible d ψ ℓ)
    (hη : AngularUnitCompatible r η ℓ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (ν : EisensteinIdealExponent) (hν : primary (idealPrimaryGenerator ν))
    (hνr : IsCoprime r (idealPrimaryGenerator ν)) :
    angularResidueIdealChar d ψ ℓ ν = primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν := by
  rw [angularResidueIdealChar_primaryNormalize ψ hu ν,
    angularResidueIdealChar_primaryNormalize η hη ν,
    twisted_character_primary_match ha hb ψ η
      (twisted_conductor_contains ha hb hsa hsb hab hsmall ψ η hagree) hagree hν hνr,
    primaryMixedIdealChar_eq,ite_eq_left hν]
  ring

 theorem angularTwistedDualPolynomial_supported_partition {a b d r : Eisenstein}
    (ha : primary a) (hb : primary b) (hsa : Squarefree a) (hsb : Squarefree b)
    (hab : IsCoprime a b) (hr : r ≠ 0) (hsmall : IsCoprime (a*b) r)
    (ψ : MulChar (Residues d) ℂ) (η : MulChar (Residues r) ℂ)
    (ℓ : ℤ) (hu : AngularUnitCompatible d ψ ℓ)
    (hη : AngularUnitCompatible r η ℓ)
    (hagree : ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
      ψ (Ideal.Quotient.mk (modulus d) x) = mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x))
    (S : Finset EisensteinIdealExponent) (J u : ℝ) :
    normalizedDualPolynomial S (angularResidueIdealChar d ψ ℓ) idealExponentNorm J u =
      ∑ ρ ∈ supportedParts (3*r) S,
        (angularResidueIdealChar d ψ ℓ ρ*mellinPhase u (idealExponentNorm ρ))*
          normalizedDualPolynomial (outsideFiber (3*r) S ρ)
            (fun ν => primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν)
            idealExponentNorm (J/idealExponentNorm ρ) u := by
  have h3r : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have h3 : (3:Eisenstein) ∣ 3*r := dvd_mul_right 3 r
  rw [normalizedDualPolynomial_supported_partition (3*r) S _ (angularResidueIdealChar_add d ψ ℓ)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  unfold normalizedDualPolynomial
  apply Finset.sum_congr rfl
  intro ν hν
  rw [angular_twisted_ideal_mixed_match ha hb hsa hsb hab hsmall ψ η ℓ hu hη hagree ν
    (outsideFiber_primary h3r h3 hν)
    (outsideFiber_coprime h3r h3 hν).symm.of_mul_left_right]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedDualMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cubic second moment for actual primitive characters after a fixed
small twist. All exceptional small-prime parts remain explicit. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

/-- A family of primitive mixed characters satisfies the cubic second moment
on a full ideal dyad. Only the explicit number of ramified parts is lost. -/
theorem normalized_angular_twisted_primitive_ideal_cubic_moment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (S : Finset EisensteinIdealExponent)
      (b : Eisenstein) (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ)
      (r : Eisenstein) (η : MulChar (Residues r) ℂ) (ℓ : ℤ) (N J u : ℝ),
      primary b → Squarefree b → r ≠ 0 →
      (AngularUnitCompatible r η ℓ) →
      1 ≤ N → 1 ≤ J →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∀ a ∈ P, IsCoprime (a*b) r) →
      (∀ a ∈ P, d a ≠ 0) →
      (∀ a ∈ P, AngularUnitCompatible (d a) (ψ a) ℓ) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) →
      (∀ ν ∈ S, J ≤ idealExponentNorm ν ∧ idealExponentNorm ν ≤ 2*J) →
      (∑ a ∈ P, ‖normalizedDualPolynomial S (angularResidueIdealChar (d a) (ψ a) ℓ)
        idealExponentNorm J u‖^2) ≤
        C*((supportedParts (3*r) S).card:ℝ)^2*(N*(2*J))^ε*(2*J)*
          (N+2*J+(N*(2*J))^(2/3:ℝ)) := by
  obtain ⟨C,hC,hcubic⟩ := normalized_primary_ideal_cubic_moment hε
  refine ⟨C,hC,?_⟩
  intro P S b d ψ r η ℓ N J u hb hsb hr hη hN hJ hP hsmall hd hu hagree hS
  let B : ℝ := C*(N*(2*J))^ε*(2*J)*(N+2*J+(N*(2*J))^(2/3:ℝ))
  let F (a : Eisenstein) (ρ : EisensteinIdealExponent) : ℂ :=
    (angularResidueIdealChar (d a) (ψ a) ℓ ρ*mellinPhase u (idealExponentNorm ρ))*
      normalizedDualPolynomial (outsideFiber (3*r) S ρ) (fun ν => primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν)
        idealExponentNorm (J/idealExponentNorm ρ) u
  have hrow (ρ : EisensteinIdealExponent) (hρ : ρ ∈ supportedParts (3*r) S) :
      (∑ a ∈ P, ‖F a ρ‖^2) ≤ B := by
    have hY : 1 ≤ (2*J)/idealExponentNorm ρ :=
      supportedPart_norm_le_upper (fun ν hν => (hS ν hν).2) hρ
    have hYJ : (2*J)/idealExponentNorm ρ ≤ 2*J :=
      div_le_self (by positivity) (idealExponentNorm_ge_one ρ)
    calc
      _ ≤ ∑ a ∈ P, ‖normalizedDualPolynomial (outsideFiber (3*r) S ρ)
          (fun ν => primaryMixedIdealChar a b ν*angularResidueIdealChar r η ℓ ν) idealExponentNorm (J/idealExponentNorm ρ) u‖^2 := by
        apply Finset.sum_le_sum
        intro a ha
        apply pow_le_pow_left₀ (_root_.norm_nonneg _)
        dsimp only [F]
        rw [norm_mul,norm_mul,mellinPhase_norm,mul_one]
        exact mul_le_of_le_one_left (_root_.norm_nonneg _)
          (angularResidueIdealChar_norm_le_one (hd a ha) (ψ a) ℓ ρ)
      _ ≤ C*(N*((2*J)/idealExponentNorm ρ))^ε*((2*J)/idealExponentNorm ρ)*
          (N+(2*J)/idealExponentNorm ρ+(N*((2*J)/idealExponentNorm ρ))^(2/3:ℝ)) := by
        simpa only [mul_comm] using hcubic P (outsideFiber (3*r) S ρ) b (angularResidueIdealChar r η ℓ)
          N ((2*J)/idealExponentNorm ρ) (J/idealExponentNorm ρ) u hb
          (fun ν _ => angularResidueIdealChar_norm_le_one hr η ℓ ν) hN hY (div_pos (by positivity) (idealExponentNorm_pos ρ))
          (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1⟩)
          (fun ν hν => outsideFiber_norm hS hν)
      _ ≤ B := by
        dsimp [B]
        gcongr
  have hsplit (a : Eisenstein) (ha : a ∈ P) :
      normalizedDualPolynomial S (angularResidueIdealChar (d a) (ψ a) ℓ) idealExponentNorm J u =
        ∑ ρ ∈ supportedParts (3*r) S, F a ρ :=
    angularTwistedDualPolynomial_supported_partition (hP a ha).1 hb (hP a ha).2.1 hsb
      (hP a ha).2.2.2 hr (hsmall a ha) (ψ a) η ℓ (hu a ha) hη (hagree a ha) S J u
  calc
    _ = ∑ a ∈ P, ‖∑ ρ ∈ supportedParts (3*r) S, F a ρ‖^2 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hsplit a ha]
    _ ≤ ((supportedParts (3*r) S).card:ℝ)*∑ ρ ∈ supportedParts (3*r) S, ∑ a ∈ P, ‖F a ρ‖^2 :=
      complex_mass_sum_sq_le (supportedParts (3*r) S) P F
    _ ≤ ((supportedParts (3*r) S).card:ℝ)*∑ _ρ ∈ supportedParts (3*r) S, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow) (Nat.cast_nonneg _)
    _ = _ := by simp [B]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedRetainedMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained functional-equation integrals of the actual primitive
characters have the cubic second moment, with explicit logarithmic losses. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma smallTwistMomentLoss_nonneg (r : Eisenstein) (J : ℝ) :
    0 ≤ smallTwistMomentLoss r J := sq_nonneg _

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedRetainedMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained functional-equation integrals of the actual primitive
characters have the cubic second moment, with explicit logarithmic losses. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem retained_angular_twisted_primitive_cubic_moment {ε : ℝ} (hε : 0 < ε)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset Eisenstein) (b : Eisenstein)
      (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ)
      (r : Eisenstein) (η : MulChar (Residues r) ℂ)
      (root : Eisenstein → ℂ) (A : Eisenstein → ℝ) (N J Z t : ℝ),
      primary b → Squarefree b → r ≠ 0 →
      (AngularUnitCompatible r η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) r) →
      (∀ a ∈ P, d a ≠ 0) →
      (∀ a ∈ P, AngularUnitCompatible (d a) (ψ a) ℓ) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) →
      (∀ a ∈ P, ‖root a‖ = 1) → (∀ a ∈ P, 0 < A a) →
      1 ≤ N → 1 ≤ J → 1 ≤ Z →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∑ a ∈ P, ‖finiteAngularDualIntegral W (fullIdealBall J)
        (angularResidueIdealChar (d a) (star (ψ a)) (-ℓ)) idealExponentNorm (root a) (A a) (|(ℓ:ℝ)|/2) Z t‖^2) ≤
        C*((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) := by
  obtain ⟨C,hC,hret⟩ := angular_retained_ideal_dyadic_moment_transfer (|(ℓ:ℝ)|/2) (by positivity) W hW hpos hsm
  obtain ⟨D,hD,hcubic⟩ := normalized_angular_twisted_primitive_ideal_cubic_moment hε
  refine ⟨2*C*D,by positivity,?_⟩
  intro P b d ψ r η root A N J Z t hb hsb hr hη hsmall hd hu hagree hroot hA hN hJ hZ hP
  let L := smallTwistMomentLoss r J
  have hL : 0 ≤ L := smallTwistMomentLoss_nonneg r J
  let B (j : ℕ) : ℝ := D*L*(N*(2*(2:ℝ)^j))^ε*(2*(2:ℝ)^j)*
    (N+2*(2:ℝ)^j+(N*(2*(2:ℝ)^j))^(2/3:ℝ))
  have hbudget : ∀ j ∈ idealDyadIndices (fullIdealBall J),
      (Z/(2:ℝ)^j)*B j ≤
        2*D*L*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) := by
    intro j hj
    have hjJ := idealDyadIndex_scale_le hj
    have hj0 : 0 < (2:ℝ)^j := by positivity
    have hNj : 0 ≤ N*(2*(2:ℝ)^j) := by positivity
    have hmul : N*(2*(2:ℝ)^j) ≤ N*(2*J) := by gcongr
    have he := Real.rpow_le_rpow hNj hmul hε.le
    have he23 := Real.rpow_le_rpow hNj hmul (by norm_num : (0:ℝ) ≤ 2/3)
    have hsum : N+2*(2:ℝ)^j+(N*(2*(2:ℝ)^j))^(2/3:ℝ) ≤
        N+2*J+(N*(2*J))^(2/3:ℝ) := by linarith
    calc
      _ = 2*D*L*Z*(N*(2*(2:ℝ)^j))^ε*
          (N+2*(2:ℝ)^j+(N*(2*(2:ℝ)^j))^(2/3:ℝ)) := by
            dsimp [B]
            field_simp
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) hsum
        (by positivity) (by positivity)
  have hm : ∀ j ∈ idealDyadIndices (fullIdealBall J), ∀ τ : ℝ,
      (∑ a : P, ‖normalizedDualPolynomial (idealDyad (fullIdealBall J) j)
        (angularResidueIdealChar (d a) (star (ψ a)) (-ℓ)) idealExponentNorm ((2:ℝ)^j) (τ-t)‖^2) ≤ B j := by
    intro j hj τ
    have hjJ := idealDyadIndex_scale_le hj
    have hj1 : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have hcard : ((supportedParts (3*r) (idealDyad (fullIdealBall J) j)).card:ℝ)^2 ≤ L := by
      dsimp [L,smallTwistMomentLoss,supportedParts]
      apply pow_le_pow_left₀ (Nat.cast_nonneg _)
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      apply Finset.image_subset_image
      intro ν hν
      exact mem_fullIdealBall.mpr ((idealDyad_norm hν).2.trans (by gcongr))
    rw [Finset.sum_coe_sort P (fun a : Eisenstein =>
      ‖normalizedDualPolynomial (idealDyad (fullIdealBall J) j)
        (angularResidueIdealChar (d a) (star (ψ a)) (-ℓ)) idealExponentNorm ((2:ℝ)^j) (τ-t)‖^2)]
    simp_rw [norm_angular_dual_conjugate]
    apply (hcubic P (idealDyad (fullIdealBall J) j) b d ψ r η ℓ N ((2:ℝ)^j) (-(τ-t))
      hb hsb hr hη hN hj1 hP hsmall hd hu hagree
      (fun ν hν => ⟨(idealDyad_norm hν).1,(idealDyad_norm hν).2⟩)).trans
    dsimp [B]
    gcongr
  have h := hret (fullIdealBall J)
    (fun a : P => angularResidueIdealChar (d a) (star (ψ a)) (-ℓ))
    (fun a : P => root a) (fun a : P => A a)
    (fun a => hroot a a.property) (fun a => hA a a.property) Z t B hZ
    (fun j _ => by dsimp [B]; positivity) hm
  rw [Finset.sum_coe_sort P (fun a : Eisenstein =>
    ‖finiteAngularDualIntegral W (fullIdealBall J) (angularResidueIdealChar (d a) (star (ψ a)) (-ℓ))
      idealExponentNorm (root a) (A a) (|(ℓ:ℝ)|/2) Z t‖^2)] at h
  apply h.trans
  calc
    _ ≤ ((idealDyadIndices (fullIdealBall J)).card:ℝ)*C*
      ∑ _j ∈ idealDyadIndices (fullIdealBall J),
        2*D*L*Z*(N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hbudget) (by positivity)
    _ = _ := by simp [L]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedSmoothMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual primitive mixed-character smooth sums, conditional only
on the cited Hecke continuation/completion and Gamma inputs. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem full_smooth_angular_twisted_primitive_cubic_moment (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b : Eisenstein) (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ)
      (r : Eisenstein) (η : MulChar (Residues r) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → r ≠ 0 →
      (AngularUnitCompatible r η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) r) → 1 ≤ N → 1 ≤ Y → 1 ≤ Z → 1 ≤ J →
      Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∀ a ∈ P, d a ≠ 0) → (∀ a ∈ P, PrimitiveResidueCharacter (d a) (ψ a)) →
      (∀ a ∈ P, ℓ ≠ 0 ∨ ψ a ≠ 1) →
      (∀ a ∈ P, AngularUnitCompatible (d a) (ψ a) ℓ) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) →
      (∀ a ∈ P, ((residueHeckeScale (d a))^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ)) →
      (∑ a ∈ P, ‖∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*
        mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)‖^2) ≤
        C*((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := by
  obtain ⟨C,hC,hret⟩ := retained_angular_twisted_primitive_cubic_moment hε ℓ W hW hpos hsm
  obtain ⟨D,hD,happrox⟩ := primitive_angular_smooth_approximation hpub ℓ
    W hW hpos hsm hδ H R hGI hGQ
  refine ⟨2*C,2*D^2,by positivity,by positivity,?_⟩
  intro P b d ψ r η N Y Z J t hb hsb hr hη hsmall hN hY hZ hJ hZH hJH hP hd hp hn hu hagree hcut
  have hex (a : P) : ∃ root : ℂ, ‖root‖ = 1 ∧
      ‖(∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*mellinPhase t (idealExponentNorm ν)*
        W (idealExponentNorm ν/Z))-
        finiteAngularDualIntegral W (fullIdealBall J) (angularResidueIdealChar (d a) (star (ψ a)) (-ℓ))
          idealExponentNorm root (residueHeckeScale (d a)) (|(ℓ:ℝ)|/2) Z t‖ ≤ D*Y^(-R) := by
    obtain ⟨r,hr,he⟩ := happrox (d a) (hd a a.property) (ψ a)
      (hp a a.property) (hu a a.property) (hn a a.property)
    exact ⟨r,hr,he Y Z J t hY hZ (zero_lt_one.trans_le hJ) hZH hJH (hcut a a.property)⟩
  choose roots hroots he using hex
  let root : Eisenstein → ℂ := fun a => if h : a ∈ P then roots ⟨a,h⟩ else 1
  have hroot (a : Eisenstein) (ha : a ∈ P) : root a = roots ⟨a,ha⟩ := dite_eq_left ha
  let V (a : Eisenstein) := finiteAngularDualIntegral W (fullIdealBall J)
    (angularResidueIdealChar (d a) (star (ψ a)) (-ℓ)) idealExponentNorm (root a) (residueHeckeScale (d a)) (|(ℓ:ℝ)|/2) Z t
  have hv := hret P b d ψ r η root (fun a => residueHeckeScale (d a)) N J Z t
    hb hsb hr hη hsmall hd hu hagree (fun a ha => by rw [hroot a ha]; exact hroots ⟨a,ha⟩)
    (fun a ha => residueHeckeScale_pos (hd a ha)) hN hJ hZ hP
  have ha (a : Eisenstein) (hap : a ∈ P) :
      ‖(∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*mellinPhase t (idealExponentNorm ν)*
        W (idealExponentNorm ν/Z))-V a‖ ≤ D*Y^(-R) := by
    dsimp only [V]
    rw [hroot a hap]
    exact he ⟨a,hap⟩
  have hs (a : Eisenstein) (hap : a ∈ P) :
      ‖∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*mellinPhase t (idealExponentNorm ν)*
        W (idealExponentNorm ν/Z)‖^2 ≤ 2*‖V a‖^2+2*(D*Y^(-R))^2 := by
    have htriangle := norm_add_le (V a)
      ((∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*mellinPhase t (idealExponentNorm ν)*
        W (idealExponentNorm ν/Z))-V a)
    have hsame : V a+((∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*
        mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z))-V a) =
        ∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*mellinPhase t (idealExponentNorm ν)*
          W (idealExponentNorm ν/Z) := by ring
    rw [hsame] at htriangle
    have hsq := pow_le_pow_left₀ (_root_.norm_nonneg _)
      (htriangle.trans (add_le_add le_rfl (ha a hap))) 2
    nlinarith [sq_nonneg (‖V a‖-D*Y^(-R))]
  calc
    _ ≤ ∑ a ∈ P, (2*‖V a‖^2+2*(D*Y^(-R))^2) := Finset.sum_le_sum hs
    _ = 2*(∑ a ∈ P, ‖V a‖^2)+2*P.card*(D*Y^(-R))^2 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul]
      ring
    _ ≤ 2*(C*((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ)))+2*P.card*(D*Y^(-R))^2 := by
      gcongr
    _ = _ := by
      have hpow : (Y^(-R))^2 = Y^(-2*R) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul (zero_lt_one.trans_le hY).le]
        congr 1
        ring
      rw [mul_pow,hpow]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SupportedIdealCount
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A Rankin bound for ideals supported on a varying small modulus. The
finite Euler product is controlled by an arbitrarily small modulus power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponentNorm_prod_of_support_subset (ν : EisensteinIdealExponent)
    (S : Finset EisensteinIdealPrime) (hS : ν.support ⊆ S) :
    idealExponentNorm ν = ∏ p ∈ S, (normNat (idealPrimeRepresentative p):ℝ)^ν p := by
  rw [idealExponentNorm_eq_prod]
  apply Finset.prod_subset hS
  intro p hp hpn
  rw [Finsupp.notMem_support_iff.mp hpn,pow_zero]

lemma supported_norm_rpow (ν : EisensteinIdealExponent)
    (S : Finset EisensteinIdealPrime) (hS : ν.support ⊆ S) (ε : ℝ) :
    idealExponentNorm ν^(-ε) =
      ∏ p : S, ((normNat (idealPrimeRepresentative p):ℝ)^(-ε))^(ν p) := by
  rw [idealExponentNorm_prod_of_support_subset ν S hS,
    ← Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity),
    ← Real.rpow_mul_natCast (by positivity)]
  congr 1
  ring

lemma finite_geometric_code_sum {α β : Type*} [Fintype α] [Fintype β]
    (M : ℕ) (f : α → β → Fin M) (hf : Function.Injective f)
    (w : β → ℝ) (hw : ∀ p, 0 ≤ w p ∧ w p < 1) :
    (∑ a : α, ∏ p : β, w p^(f a p).val) ≤ ∏ p : β, (1-w p)⁻¹ := by
  classical
  calc
    _ ≤ ∑ g : β → Fin M, ∏ p : β, w p^(g p).val := by
      apply OAI.sum_le_sum_of_injOn f (fun _ _ _ _ h => hf h)
        (Finset.subset_univ _)
      · intro a ha
        exact le_rfl
      · intro g hg hgn
        exact Finset.prod_nonneg (fun p _ => pow_nonneg (hw p).1 _)
    _ = ∏ p : β, ∑ n : Fin M, w p^n.val := (Fintype.prod_sum (fun (p : β) (n : Fin M) => w p^n.val)).symm
    _ ≤ ∏ p : β, (1-w p)⁻¹ := by
      apply Finset.prod_le_prod
      · intro p hp
        exact Finset.sum_nonneg (fun n _ => pow_nonneg (hw p).1 _)
      · intro p hp
        rw [Fin.sum_univ_eq_sum_range]
        exact sum_le_hasSum (Finset.range M) (fun n _ => pow_nonneg (hw p).1 n)
          (hasSum_geometric_of_lt_one (hw p).1 (hw p).2)

lemma ideal_supported_rankin_sum {ε J : ℝ} (hε : 0 < ε)
    (S : Finset EisensteinIdealPrime) (T : Finset EisensteinIdealExponent)
    (hT : ∀ ν ∈ T, ν.support ⊆ S ∧ idealExponentNorm ν ≤ J) :
    (∑ ν ∈ T, idealExponentNorm ν^(-ε)) ≤
      ∏ p ∈ S, (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹ := by
  let M := Nat.log 2 ⌊J⌋₊+1
  let f : T → (S → Fin M) := fun ν p =>
    ⟨ν.val p, Nat.lt_succ_of_le (idealExponent_exponent_bound (hT ν ν.property).2 p)⟩
  have hf : Function.Injective f := by
    intro ν κ he
    apply Subtype.ext
    apply Finsupp.ext
    intro p
    by_cases hp : p ∈ S
    · exact congrArg Fin.val (congrFun he ⟨p,hp⟩)
    · rw [Finsupp.notMem_support_iff.mp (fun h => hp ((hT ν ν.property).1 h)),
        Finsupp.notMem_support_iff.mp (fun h => hp ((hT κ κ.property).1 h))]
  let w : S → ℝ := fun p => (normNat (idealPrimeRepresentative p):ℝ)^(-ε)
  have hw (p : S) : 0 ≤ w p ∧ w p < 1 := by
    have hp : (1:ℝ) < normNat (idealPrimeRepresentative p) := by
      have := idealPrimeRepresentative_normNat_ge_two p
      exact_mod_cast (by omega : 1 < normNat (idealPrimeRepresentative p))
    exact ⟨Real.rpow_nonneg (by positivity) _,Real.rpow_lt_one_of_one_lt_of_neg hp (neg_neg_of_pos hε)⟩
  have hnorm (ν : T) : idealExponentNorm ν^(-ε) = ∏ p : S, w p^(f ν p).val :=
    supported_norm_rpow ν S (hT ν ν.property).1 ε
  calc
    _ = ∑ ν : T, ∏ p : S, w p^(f ν p).val := by
      rw [← Finset.sum_coe_sort T]
      exact Finset.sum_congr rfl (fun ν _ => hnorm ν)
    _ ≤ ∏ p : S, (1-w p)⁻¹ := finite_geometric_code_sum M f hf w hw
    _ = _ := Finset.prod_coe_sort S
      (fun p => (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallEulerProduct
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite Euler factor for a varying small modulus costs only an
arbitrary positive power of its norm. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

 theorem supported_euler_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : EisensteinIdealExponent,
      (∏ p ∈ ν.support, (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹) ≤
        C*idealExponentNorm ν^ε := by
  let R : ℝ := (2:ℝ)^(1/ε)
  let T : Finset EisensteinIdealPrime :=
    (fullIdealBall R).biUnion (fun ν => ν.support)
  let A : ℝ := (1-(2:ℝ)^(-ε))⁻¹
  have ht : (2:ℝ)^(-ε) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hA : 1 ≤ A := by
    dsimp [A]
    rw [← one_div]
    apply (le_div_iff₀ (by linarith : 0 < 1-(2:ℝ)^(-ε))).mpr
    rw [one_mul]
    linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-ε)]
  have hR : 0 < R := Real.rpow_pos_of_pos (by norm_num) _
  have hRe : R^ε = 2 := by
    dsimp [R]
    rw [← Real.rpow_mul (by norm_num),one_div_mul_cancel hε.ne',Real.rpow_one]
  have hT (p : EisensteinIdealPrime) :
      (normNat (idealPrimeRepresentative p):ℝ) ≤ R → p ∈ T := by
    intro hp
    apply Finset.mem_biUnion.mpr
    refine ⟨Finsupp.single p 1,?_,by simp⟩
    apply mem_fullIdealBall.mpr
    simpa only [idealExponentNorm_single,pow_one] using hp
  refine ⟨A^T.card,pow_pos (zero_lt_one.trans_le hA) _,?_⟩
  intro ν
  have hpoint : ∀ p ∈ ν.support,
      (1-(normNat (idealPrimeRepresentative p):ℝ)^(-ε))⁻¹ ≤
        (if p ∈ T then A else 1)*(normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p) := by
    intro p hp
    let q : ℝ := normNat (idealPrimeRepresentative p)
    have hq : (2:ℝ) ≤ q := by
      dsimp [q]
      exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
    have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
    have hqt : q^(-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
    have hexp : ε ≤ ε*ν p := by
      have hn : (1:ℝ) ≤ ν p := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hp))
      nlinarith
    have hpow : 1 ≤ q^(ε*ν p) := Real.one_le_rpow (by linarith) (by positivity)
    by_cases hpT : p ∈ T
    · simp only [ite_eq_left hpT]
      have hlocal : (1-q^(-ε))⁻¹ ≤ A := by
        apply (inv_le_inv₀ (by linarith) (by linarith)).mpr
        have hmono := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ)<2) hq (by linarith : -ε ≤ 0)
        linarith
      exact hlocal.trans (le_mul_of_one_le_right (zero_le_one.trans hA) hpow)
    · simp only [ite_eq_right hpT,one_mul]
      have hRp : R ≤ q := le_of_lt (lt_of_not_ge (fun h => hpT (hT p h)))
      have htwo : (2:ℝ) ≤ q^ε := by
        rw [← hRe]
        exact Real.rpow_le_rpow hR.le hRp hε.le
      have hhalf : q^(-ε) ≤ 1/2 := by
        rw [Real.rpow_neg hqp.le]
        simpa only [one_div] using
          (inv_le_inv₀ (Real.rpow_pos_of_pos hqp ε) (by norm_num : (0:ℝ) < 2)).mpr htwo
      have hlocal : (1-q^(-ε))⁻¹ ≤ 2 := by
        rw [← one_div]
        apply (div_le_iff₀ (by linarith : 0 < 1-q^(-ε))).mpr
        linarith
      exact hlocal.trans (htwo.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) hexp))
  have hprod := Finset.prod_le_prod (s := ν.support)
    (fun p _ => inv_nonneg.mpr (by
      have hp : (1:ℝ) < normNat (idealPrimeRepresentative p) := by
        have := idealPrimeRepresentative_normNat_ge_two p
        exact_mod_cast (by omega : 1 < normNat (idealPrimeRepresentative p))
      exact sub_nonneg.mpr (le_of_lt (Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith))))) hpoint
  rw [Finset.prod_mul_distrib] at hprod
  have hsmall : (∏ p ∈ ν.support, if p ∈ T then A else 1) ≤ A^T.card := by
    rw [Finset.prod_ite_mem,Finset.prod_const]
    exact pow_le_pow_right₀ hA (Finset.card_le_card Finset.inter_subset_right)
  have hnorm : (∏ p ∈ ν.support,
      (normNat (idealPrimeRepresentative p):ℝ)^(ε*ν p)) = idealExponentNorm ν^ε := by
    calc
      _ = ∏ p ∈ ν.support, ((normNat (idealPrimeRepresentative p):ℝ)^ν p)^ε := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity)]
        congr 1
        ring
      _ = (∏ p ∈ ν.support, ((normNat (idealPrimeRepresentative p):ℝ)^ν p))^ε :=
        Real.finsetProd_rpow _ _ (fun _ _ => by positivity) ε
      _ = _ := by rw [idealExponentNorm_eq_prod]
  rw [hnorm] at hprod
  exact hprod.trans (mul_le_mul_of_nonneg_right hsmall (Real.rpow_nonneg (idealExponentNorm_pos ν).le _))

/-- Uniform subpower counting of the actual supported parts. -/
theorem supportedParts_card_small_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Eisenstein) (S : Finset EisensteinIdealExponent) (J : ℝ),
      v ≠ 0 → 1 ≤ J → (∀ ν ∈ S, idealExponentNorm ν ≤ J) →
      ((supportedParts v S).card:ℝ) ≤ C*(J*norm v)^ε := by
  obtain ⟨C,hC,hEuler⟩ := supported_euler_small_power hε
  refine ⟨C,hC,?_⟩
  intro v S J hv hJ hS
  have hT (ρ : EisensteinIdealExponent) (hρ : ρ ∈ supportedParts v S) :
      ρ.support ⊆ (idealExponentOf v).support ∧ idealExponentNorm ρ ≤ J := by
    obtain ⟨ν,hν,rfl⟩ := Finset.mem_image.mp hρ
    refine ⟨?_,(supportedIdealPart_norm_le v ν).trans (hS ν hν)⟩
    intro p hp
    by_contra hpin
    have hzero : supportedIdealPart v ν p = 0 := by
      have hz := Finsupp.notMem_support_iff.mp hpin
      simp [supportedIdealPart,hz]
    exact (Finsupp.mem_support_iff.mp hp) hzero
  have hsum := ideal_supported_rankin_sum hε (idealExponentOf v).support
    (supportedParts v S) hT
  have he := hEuler (idealExponentOf v)
  rw [idealExponentOf_norm hv] at he
  calc
    _ = ∑ _ρ ∈ supportedParts v S, (1:ℝ) := by simp
    _ ≤ ∑ ρ ∈ supportedParts v S, J^ε*idealExponentNorm ρ^(-ε) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [Real.rpow_neg (idealExponentNorm_pos ρ).le,← div_eq_mul_inv]
      apply (le_div_iff₀ (Real.rpow_pos_of_pos (idealExponentNorm_pos ρ) ε)).mpr
      rw [one_mul]
      exact Real.rpow_le_rpow (idealExponentNorm_pos ρ).le (hT ρ hρ).2 hε.le
    _ = J^ε*∑ ρ ∈ supportedParts v S, idealExponentNorm ρ^(-ε) := (Finset.mul_sum _ _ _).symm
    _ ≤ J^ε*(C*norm v^ε) := mul_le_mul_of_nonneg_left (hsum.trans he) (by positivity)
    _ = C*(J*norm v)^ε := by rw [Real.mul_rpow (by linarith) (norm_nonneg v)]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_TwistedMomentLoss
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Absorption of the exact small-prime partition and dyadic losses. -/
noncomputable section
namespace CubicFirstMoment

lemma dyad_card_sq_power {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ J : ℝ, 1 ≤ J →
      ((idealDyadIndices (fullIdealBall J)).card:ℝ)^2 ≤ C*(2*J)^ε := by
  obtain ⟨C,hC,hlog⟩ := natLog_power_bound 2 hε
  refine ⟨C,hC,?_⟩
  intro J hJ
  have hJ0 : 0 ≤ 2*J := by linarith
  have hn : 1 ≤ ⌊2*J⌋₊ := (Nat.one_le_floor_iff (2*J)).mpr (by linarith)
  have hc : (idealDyadIndices (fullIdealBall J)).card ≤ Nat.log 2 ⌊2*J⌋₊+1 :=
    idealDyadIndices_card_le _ (fun ν hν => (mem_fullIdealBall.mp hν).trans (by linarith))
  have hc' : ((idealDyadIndices (fullIdealBall J)).card:ℝ) ≤ (Nat.log 2 ⌊2*J⌋₊+1:ℕ) := by
    exact_mod_cast hc
  calc
    _ ≤ ((Nat.log 2 ⌊2*J⌋₊+1:ℕ):ℝ)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hc' 2
    _ ≤ C*(⌊2*J⌋₊:ℝ)^ε := hlog _ hn
    _ ≤ C*(2*J)^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hJ0) hε.le) hC.le

 theorem twisted_moment_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : Eisenstein) (J : ℝ), r ≠ 0 → 1 ≤ J →
      ((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J ≤
        C*(2*J)^ε*norm (3*r)^ε := by
  obtain ⟨A,hA,hdyad⟩ := dyad_card_sq_power (show 0 < ε/2 by positivity)
  obtain ⟨B,hB,hparts⟩ := supportedParts_card_small_power (show 0 < ε/4 by positivity)
  refine ⟨A*B^2,by positivity,?_⟩
  intro r J hr hJ
  have h3r : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have hJp : 0 < 2*J := by linarith
  have hNp : 0 < norm (3*r) := lt_of_lt_of_le zero_lt_one (one_le_norm h3r)
  have hprod : 0 < (2*J)*norm (3*r) := mul_pos hJp hNp
  have hp := hparts (3*r) (fullIdealBall (2*J)) (2*J) h3r (by linarith)
    (fun ν hν => mem_fullIdealBall.mp hν)
  have hs : smallTwistMomentLoss r J ≤ B^2*(2*J)^(ε/2)*norm (3*r)^(ε/2) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hp 2).trans_eq
    rw [mul_pow,← Real.rpow_mul_natCast hprod.le]
    have he : ε/4*(2:ℕ) = ε/2 := by norm_num; ring
    rw [he,Real.mul_rpow hJp.le hNp.le]
    ring
  have hnorm : norm (3*r)^(ε/2) ≤ norm (3*r)^ε :=
    Real.rpow_le_rpow_of_exponent_le (one_le_norm h3r) (by linarith)
  calc
    _ ≤ (A*(2*J)^(ε/2))*(B^2*(2*J)^(ε/2)*norm (3*r)^(ε/2)) :=
      mul_le_mul (hdyad J hJ) hs (smallTwistMomentLoss_nonneg r J) (by positivity)
    _ = (A*B^2)*((2*J)^(ε/2)*(2*J)^(ε/2))*norm (3*r)^(ε/2) := by ring
    _ = (A*B^2)*(2*J)^ε*norm (3*r)^(ε/2) := by
      have he : (2*J)^(ε/2)*(2*J)^(ε/2) = (2*J)^ε := by
        rw [← Real.rpow_add hJp]
        congr 1
        ring
      rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)

 theorem twisted_moment_weighted_loss {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : Eisenstein) (N J : ℝ), r ≠ 0 → 1 ≤ N → 1 ≤ J →
      (((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J)*
        (N*(2*J))^(ε/2) ≤ C*(N*(2*J))^ε*norm (3*r)^ε := by
  obtain ⟨C,hC,hbound⟩ := twisted_moment_loss (show 0 < ε/2 by positivity)
  refine ⟨C,hC,?_⟩
  intro r N J hr hN hJ
  have hQ : 0 < N*(2*J) := by positivity
  have h3r : (3:Eisenstein)*r ≠ 0 := mul_ne_zero (by norm_num) hr
  have hj : (2*J)^(ε/2) ≤ (N*(2*J))^(ε/2) := Real.rpow_le_rpow (by positivity)
    (le_mul_of_one_le_left (by positivity) hN) (by positivity)
  have hn : norm (3*r)^(ε/2) ≤ norm (3*r)^ε :=
    Real.rpow_le_rpow_of_exponent_le (one_le_norm h3r) (by linarith)
  calc
    _ ≤ (C*(2*J)^(ε/2)*norm (3*r)^(ε/2))*(N*(2*J))^(ε/2) :=
      mul_le_mul_of_nonneg_right (hbound r J hr hJ) (by positivity)
    _ ≤ (C*(N*(2*J))^(ε/2)*norm (3*r)^ε)*(N*(2*J))^(ε/2) := by
      have hn0 := Real.rpow_nonneg (norm_nonneg (3*r)) (ε/2)
      gcongr
    _ = (C*norm (3*r)^ε)*((N*(2*J))^(ε/2)*(N*(2*J))^(ε/2)) := by ring
    _ = _ := by
      have he : (N*(2*J))^(ε/2)*(N*(2*J))^(ε/2) = (N*(2*J))^ε := by
        rw [← Real.rpow_add hQ]
        congr 1
        ring
      rw [he]
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularTwistedSmoothBound
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p0 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p3 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p2 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The application-sized primitive cubic moment, with the fixed logarithmic
losses absorbed into an arbitrary positive power. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem full_smooth_angular_twisted_primitive_cubic_bound_oai (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b : Eisenstein) (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ)
      (r : Eisenstein) (η : MulChar (Residues r) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → r ≠ 0 →
      (AngularUnitCompatible r η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) r) → 1 ≤ N → 1 ≤ Y → 1 ≤ Z → 1 ≤ J →
      Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∀ a ∈ P, d a ≠ 0) → (∀ a ∈ P, PrimitiveResidueCharacter (d a) (ψ a)) →
      (∀ a ∈ P, ℓ ≠ 0 ∨ ψ a ≠ 1) →
      (∀ a ∈ P, AngularUnitCompatible (d a) (ψ a) ℓ) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) →
      (∀ a ∈ P, ((residueHeckeScale (d a))^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ)) →
      (∑ a ∈ P, ‖∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*
        mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)‖^2) ≤
        C*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*r)^ε + D*P.card*Y^(-2*R) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := full_smooth_angular_twisted_primitive_cubic_moment hpub ℓ
    (show 0 < ε/2 by positivity) W hW hpos hsm hδ H R hGI hGQ
  obtain ⟨E,hE,hlog⟩ := twisted_moment_weighted_loss hε
  refine ⟨C*E,D,mul_nonneg hC hE.le,hD,?_⟩
  intro P b d ψ r η N Y Z J t hb hsb hr hη hsmall hN hY hZ hJ hZH hJH hP hd hp hn hu hagree hcut
  apply (hbound P b d ψ r η N Y Z J t hb hsb hr hη hsmall hN hY hZ hJ hZH hJH
    hP hd hp hn hu hagree hcut).trans
  have hF : 0 ≤ N+2*J+(N*(2*J))^(2/3:ℝ) := by positivity
  calc
    _ = C*Z*((((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J)*
        (N*(2*J))^(ε/2))*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := by ring
    _ ≤ C*Z*(E*(N*(2*J))^ε*norm (3*r)^ε)*(N+2*J+(N*(2*J))^(2/3:ℝ)) + D*P.card*Y^(-2*R) := by
      have hm : C*Z*((((idealDyadIndices (fullIdealBall J)).card:ℝ)^2*smallTwistMomentLoss r J)*
          (N*(2*J))^(ε/2))*(N+2*J+(N*(2*J))^(2/3:ℝ)) ≤
          C*Z*(E*(N*(2*J))^ε*norm (3*r)^ε)*(N+2*J+(N*(2*J))^(2/3:ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hlog r N J hr hN hJ)
          (show 0 ≤ C*Z by positivity)) hF
      exact add_le_add hm le_rfl
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

theorem solution : type_of% @OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound_oai := @OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound_oai
