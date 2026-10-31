-- Prove2me | solution 1 for OAI.CubicFirstMoment.angular_stopped_noncube_radial_form
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:17:02.76955+00:00
-- url     : https://prove2.me/submissions/a9d5bf62-2c5d-4c49-861d-3044bc592b57

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A016
import Definitions.Def_OAIQ096A020
import Theorems.Thm_OAI_CubicFirstMoment_angular_stopped_early_divisor_noncube_mass
import Theorems.Thm_OAI_CubicFirstMoment_smallB_core_hybrid_sieve

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
-- module Solutions.OAIQ096_CM.CubicGram_PrimaryNormalization
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
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

end CubicFirstMoment
end
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_Mobius
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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

lemma idealMoebius_mul {a b : Eisenstein} (h : IsCoprime a b) :
    idealMoebius (a*b) = idealMoebius a * idealMoebius b :=
  (isRelPrime_iff_isCoprime.mpr h).moebius_mul

lemma idealMoebius_primaryPrime {p : Eisenstein} (hp : primaryPrime p) :
    idealMoebius p = -1 := hp.2.irreducible.moebius_eq

lemma idealMoebius_prod_primaryPrimes (s : Finset Eisenstein)
    (hp : ∀ p ∈ s, primaryPrime p) :
    idealMoebius (∏ p ∈ s, p) = (-1 : ℤ)^s.card := by
  induction s using Finset.induction_on with
  | empty => simp [idealMoebius]
  | @insert p s hps ih =>
    have hp' := hp p (Finset.mem_insert_self _ _)
    have hs : ∀ q ∈ s, primaryPrime q := fun q hq => hp q (Finset.mem_insert_of_mem hq)
    have hc : IsCoprime p (∏ q ∈ s, q) := by
      apply IsCoprime.prod_right
      intro q hq
      exact primaryPrimes_isCoprime hp' (hs q hq) (fun h => hps (h ▸ hq))
    rw [Finset.prod_insert hps, idealMoebius_mul hc, idealMoebius_primaryPrime hp',
      ih hs, Finset.card_insert_of_notMem hps, pow_succ]
    ring

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CommonFactors
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Moebius removal of common factors and coprime Gram decomposition. -/

section

noncomputable section
open scoped BigOperators SchwartzMap ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primary_subsets_prod_dvd {k : Eisenstein} (hk : primary k)
    {s : Finset Eisenstein} (hs : s ⊆ primaryPrimeFactors k) (n : Eisenstein) :
    (∏ p ∈ s, p) ∣ n ↔ ∀ p ∈ s, p ∣ n := by
  constructor
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp) h
  · intro h
    apply Finset.prod_dvd_of_coprime _ h
    intro p hp q hq hpq
    exact primaryPrimes_isCoprime (primaryPrimeFactor_spec hk (hs hp)).1
      (primaryPrimeFactor_spec hk (hs hq)).1 hpq

theorem primary_moebius_coprimality {k : Eisenstein} (hk : primary k)
    (hsk : Squarefree k) (n : Eisenstein) :
    (if IsCoprime k n then (1 : ℂ) else 0) =
      ∑ s ∈ (primaryPrimeFactors k).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℂ) *
          (if (∏ p ∈ s, p) ∣ n then 1 else 0) := by
  let P := primaryPrimeFactors k
  have hprod : (∏ p ∈ P, (1 - (if p ∣ n then (1 : ℂ) else 0))) =
      if IsCoprime k n then 1 else 0 := by
    by_cases h : IsCoprime k n
    · rw [ite_eq_left h]
      apply Finset.prod_eq_one
      intro p hp
      have hpn : ¬p ∣ n := by
        intro hd
        exact (primaryPrimeFactor_spec hk hp).1.2.not_isUnit
          (h.isUnit_of_dvd' (primaryPrimeFactor_spec hk hp).2 hd)
      simp [hpn]
    · rw [ite_eq_right h]
      have hex : ∃ p ∈ P, p ∣ n := by
        by_contra hn
        have hall : ∀ p ∈ P, IsCoprime p n := by
          intro p hp
          exact ((primaryPrimeFactor_spec hk hp).1.2.irreducible.coprime_iff_not_dvd).mpr
            (fun hd => hn ⟨p, hp, hd⟩)
        have := IsCoprime.prod_left hall
        rw [primaryPrimeFactors_prod hk hsk] at this
        exact h this
      obtain ⟨p, hp, hpn⟩ := hex
      apply Finset.prod_eq_zero hp
      simp [hpn]
  rw [← hprod]
  have hex := Finset.prod_add (fun p : Eisenstein => -(if p ∣ n then (1 : ℂ) else 0))
    (fun _ => (1 : ℂ)) P
  simp only [Finset.prod_const_one, mul_one, ← sub_eq_neg_add] at hex
  rw [hex]
  apply Finset.sum_congr rfl
  intro s hs
  have hsub : s ⊆ primaryPrimeFactors k := Finset.mem_powerset.mp hs
  rw [idealMoebius_prod_primaryPrimes s
    (fun p hp => (primaryPrimeFactor_spec hk (hsub hp)).1), Finset.prod_neg]
  push_cast
  congr 1
  by_cases h : (∏ p ∈ s, p) ∣ n
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro p hp
    simp [(primary_subsets_prod_dvd hk hsub n).mp h p hp]
  · rw [ite_eq_right h]
    have hex : ∃ p ∈ s, ¬p ∣ n := by
      by_contra hn
      apply h
      apply (primary_subsets_prod_dvd hk hsub n).mpr
      intro p hp
      by_contra hpn
      exact hn ⟨p, hp, hpn⟩
    obtain ⟨p, hp, hpn⟩ := hex
    exact Finset.prod_eq_zero hp (by simp [hpn])

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_LatticeCounts
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Eisenstein lattice counts and arbitrarily small divisor losses. -/

section

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_finset_prod {α : Type*} (s : Finset α) (f : α → Eisenstein) :
    norm (∏ p ∈ s, f p) = ∏ p ∈ s, norm (f p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih => simp [hp, ih]

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_CubicOperator
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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

lemma primeSet_subset_factors_of_prod_dvd {n : Eisenstein} (hn : primary n)
    {s : Finset Eisenstein} (hs : ∀ p ∈ s, primaryPrime p)
    (hd : (∏ p ∈ s, p) ∣ n) : s ⊆ primaryPrimeFactors n := by
  intro p hp
  exact primaryPrime_mem_factors hn (hs p hp)
    ((Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp).trans hd)

lemma primary_moebius_universal_indicator {U : Finset Eisenstein}
    (hU : ∀ p ∈ U, primaryPrime p) {a b : Eisenstein}
    (ha : primary a) (hsa : Squarefree a) (haU : primaryPrimeFactors a ⊆ U) :
    (if IsCoprime a b then (1 : ℂ) else 0) =
      ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p) : ℂ) *
        (if (∏ p ∈ s, p) ∣ a ∧ (∏ p ∈ s, p) ∣ b then (1 : ℂ) else 0) := by
  rw [primary_moebius_coprimality ha hsa]
  calc
    _ = ∑ s ∈ (primaryPrimeFactors a).powerset,
        (idealMoebius (∏ p ∈ s, p) : ℂ) *
          (if (∏ p ∈ s, p) ∣ a ∧ (∏ p ∈ s, p) ∣ b then (1 : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hd : (∏ p ∈ s, p) ∣ a :=
        (primary_subsets_prod_dvd ha (Finset.mem_powerset.mp hs) a).mpr
          (fun p hp => (primaryPrimeFactor_spec ha (Finset.mem_powerset.mp hs hp)).2)
      simp only [hd, true_and]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr haU)
      intro s hs hn
      have hnd : ¬(∏ p ∈ s, p) ∣ a := by
        intro hd
        apply hn
        exact Finset.mem_powerset.mpr (primeSet_subset_factors_of_prod_dvd ha
          (fun p hp => hU p (Finset.mem_powerset.mp hs hp)) hd)
      simp [hnd]

theorem coprime_bilinear_moebius (S T U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U) (v w : Eisenstein → ℂ) :
    (∑ a ∈ S, ∑ b ∈ T, if IsCoprime a b then v a * star (w b) else 0) =
      ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p) : ℂ) *
        (∑ a ∈ S, if (∏ p ∈ s, p) ∣ a then v a else 0) *
          star (∑ b ∈ T, if (∏ p ∈ s, p) ∣ b then w b else 0) := by
  have hpoint (a : Eisenstein) (ha : a ∈ S) (b : Eisenstein) :
      (if IsCoprime a b then v a * star (w b) else 0) =
        ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p) : ℂ) *
          ((if (∏ p ∈ s, p) ∣ a then v a else 0) *
            star (if (∏ p ∈ s, p) ∣ b then w b else 0)) := by
    have hi := congrArg (fun z : ℂ => z * (v a * star (w b)))
      (primary_moebius_universal_indicator hU (hS a ha).1 (hS a ha).2 (hSU a ha)
        (b := b))
    rw [Finset.sum_mul] at hi
    convert hi using 1
    · split_ifs <;> simp
    · apply Finset.sum_congr rfl
      intro s hs
      split_ifs <;> simp_all
  simp_rw [Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl
    (fun b _ => hpoint a ha b))]
  
  simp_rw [Finset.sum_comm (s := T) (t := U.powerset)]
  rw [Finset.sum_comm (s := S) (t := U.powerset)]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [star_sum]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := T) (t := S)]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

end CubicFirstMoment

namespace CubicFirstMoment

lemma finiteCubicOperator_apply (S H : Finset Eisenstein) (u : Eisenstein → ℂ)
    (h : H) :
    finiteCubicOperator S H (WithLp.toLp 2 (fun a : S => u a.val)) h =
      ∑ a ∈ S, u a * cubicSymbol a h.val := by
  change (∑ a : S, cubicSymbol a.val h.val * u a.val) = _
  rw [← Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => cubicSymbol a h.val * u a)]
  apply Finset.sum_congr rfl
  intro a ha
  ring

lemma finiteCubicBound_controls_mass (S H : Finset Eisenstein) (u : Eisenstein → ℂ) :
    (∑ h ∈ H, ‖∑ a ∈ S, u a * cubicSymbol a h‖^2) ≤
      finiteCubicBound S H * ∑ a ∈ S, ‖u a‖^2 := by
  let v : EuclideanSpace ℂ S := WithLp.toLp 2 (fun a : S => u a.val)
  have hb := (finiteCubicOperator S H).le_opNorm v
  have hs := pow_le_pow_left₀ (_root_.norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  change (∑ h : H, ‖finiteCubicOperator S H v h‖^2) ≤
      finiteCubicBound S H * ∑ a : S, ‖u a.val‖^2 at hs
  dsimp only [v] at hs
  simp_rw [finiteCubicOperator_apply] at hs
  simpa only [← Finset.sum_subtype H (fun _ => Iff.rfl)
    (fun h => ‖∑ a ∈ S, u a * cubicSymbol a h‖^2),
    ← Finset.sum_subtype S (fun _ => Iff.rfl) (fun a => ‖u a‖^2)] using hs

end CubicFirstMoment

namespace CubicFirstMoment

theorem finiteCubicBound_bilinear (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1) :
    ‖∑ h ∈ H, phase h * (∑ a ∈ S, v a * cubicSymbol a h) *
      star (∑ a ∈ S, w a * cubicSymbol a h)‖ ≤
      finiteCubicBound S H *
        ((∑ a ∈ S, ‖v a‖^2) + (∑ a ∈ S, ‖w a‖^2)) / 2 := by
  let V (h : Eisenstein) := ∑ a ∈ S, v a * cubicSymbol a h
  let W (h : Eisenstein) := ∑ a ∈ S, w a * cubicSymbol a h
  calc
    _ ≤ ∑ h ∈ H, ‖phase h * V h * star (W h)‖ := norm_sum_le _ _
    _ ≤ ∑ h ∈ H, (‖V h‖^2+‖W h‖^2)/2 := by
      apply Finset.sum_le_sum
      intro h hh
      rw [norm_mul, norm_mul, norm_star]
      calc
        _ ≤ 1 * ‖V h‖ * ‖W h‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hphase h hh) (_root_.norm_nonneg _))
            (_root_.norm_nonneg _)
        _ ≤ _ := by nlinarith [sq_nonneg (‖V h‖-‖W h‖)]
    _ = ((∑ h ∈ H, ‖V h‖^2) + (∑ h ∈ H, ‖W h‖^2))/2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by
      have hv := finiteCubicBound_controls_mass S H v
      have hw := finiteCubicBound_controls_mass S H w
      change (∑ h ∈ H, ‖V h‖^2) ≤ _ at hv
      change (∑ h ∈ H, ‖W h‖^2) ≤ _ at hw
      nlinarith

theorem finiteCubicBound_conjugate_bilinear (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1) :
    ‖∑ h ∈ H, phase h * (∑ a ∈ S, v a * star (cubicSymbol a h)) *
      star (∑ a ∈ S, w a * star (cubicSymbol a h))‖ ≤
      finiteCubicBound S H *
        ((∑ a ∈ S, ‖v a‖^2) + (∑ a ∈ S, ‖w a‖^2)) / 2 := by
  have h := finiteCubicBound_bilinear S H (fun a => star (w a))
    (fun a => star (v a)) phase hphase
  simp only [norm_star] at h
  have he : (∑ h ∈ H, phase h * (∑ a ∈ S, v a * star (cubicSymbol a h)) *
      star (∑ a ∈ S, w a * star (cubicSymbol a h))) =
      ∑ h ∈ H, phase h * (∑ a ∈ S, star (w a) * cubicSymbol a h) *
        star (∑ a ∈ S, star (v a) * cubicSymbol a h) := by
    apply Finset.sum_congr rfl
    intro h hh
    simp [star_sum, star_mul, mul_comm, mul_left_comm, mul_assoc]
  rw [he]
  simpa only [add_comm] using h

end CubicFirstMoment

namespace CubicFirstMoment

lemma norm_idealMoebius_le_one (m : Eisenstein) : ‖(idealMoebius m : ℂ)‖ ≤ 1 := by
  have hs : (idealMoebius m : ℝ)^2 ≤ 1 := by
    rw [idealMoebius_sq]
    split_ifs <;> norm_num
  have hn : ‖(idealMoebius m : ℂ)‖ = |(idealMoebius m : ℝ)| :=
    Complex.norm_intCast _
  rw [hn]
  nlinarith [sq_abs (idealMoebius m : ℝ), abs_nonneg (idealMoebius m : ℝ)]

theorem finiteCubicBound_coprime_bilinear (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1) :
    ‖∑ h ∈ H, phase h * ∑ a ∈ S, ∑ b ∈ S,
      if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0‖ ≤
      ∑ s ∈ U.powerset,
        finiteCubicBound (S.filter (fun a => (∏ p ∈ s, p) ∣ a)) H *
          ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖^2) +
           (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖^2)) / 2 := by
  let V (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), v a * star (cubicSymbol a h)
  let W (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), w a * star (cubicSymbol a h)
  have he (h : Eisenstein) := coprime_bilinear_moebius S S U hS hU hSU
    (fun a => v a * star (cubicSymbol a h)) (fun a => w a * star (cubicSymbol a h))
  have he' (h : Eisenstein) :
      (∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0) =
      ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p) : ℂ) * V s h * star (W s h) := by
    simpa only [V, W, Finset.sum_filter] using he h
  simp_rw [he', Finset.mul_sum]
  rw [Finset.sum_comm]
  have hfactor (s : Finset Eisenstein) :
      (∑ h ∈ H, phase h * ((idealMoebius (∏ p ∈ s, p) : ℂ) * V s h * star (W s h))) =
      (idealMoebius (∏ p ∈ s, p) : ℂ) * ∑ h ∈ H, phase h * V s h * star (W s h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  simp_rw [hfactor]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∑ h ∈ H, phase h * V s h * star (W s h)‖ :=
      mul_le_mul_of_nonneg_right (norm_idealMoebius_le_one _) (_root_.norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact finiteCubicBound_conjugate_bilinear _ H v w phase hphase

end CubicFirstMoment
end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_MellinNorm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mellin integral bounds for coprime radial forms. -/

section

noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gramMellinPhase_continuous (x : ℝ) : Continuous (fun t => gramMellinPhase t x) := by
  unfold gramMellinPhase
  fun_prop

lemma gramMellinPhase_mul (t : ℝ) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    gramMellinPhase t (x*y) = gramMellinPhase t x * gramMellinPhase t y := by
  simp only [gramMellinPhase, Real.log_mul hx.ne' hy.ne', mul_add,
    AddChar.map_add_eq_mul, Circle.coe_mul]

lemma coprimeNormMajorant_phases (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) :
    coprimeNormMajorant S H U (fun a => v a * star (gramMellinPhase t (y a)))
      (fun a => w a * gramMellinPhase t (y a)) = coprimeNormMajorant S H U v w := by
  simp only [coprimeNormMajorant, norm_mul, norm_star, norm_gramMellinPhase, mul_one]

end CubicFirstMoment

namespace CubicFirstMoment

lemma coprimeMellinKernel_continuous (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (x y : Eisenstein → ℝ) :
    Continuous (coprimeMellinKernel S H v w phase x y) := by
  unfold coprimeMellinKernel
  apply continuous_finsetSum
  intro h hh
  apply Continuous.mul
  · exact continuous_const.mul (gramMellinPhase_continuous _)
  · apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    by_cases hab : IsCoprime a b
    · simp only [ite_eq_left hab]
      exact ((continuous_const.mul (gramMellinPhase_continuous _).star).mul
        continuous_const).mul
        (((continuous_const.mul (gramMellinPhase_continuous _)).mul continuous_const).star)
    · simp only [ite_eq_right hab]
      exact continuous_const

lemma norm_coprimeMellinKernel_le (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ) (t : ℝ) :
    ‖coprimeMellinKernel S H v w phase x y t‖ ≤ coprimeNormMajorant S H U v w := by
  have h := finiteCubicBound_coprime_bilinear S H U hS hU hSU
    (fun a => v a * star (gramMellinPhase t (y a)))
    (fun a => w a * gramMellinPhase t (y a))
    (fun h => phase h * gramMellinPhase t (x h)) (fun h hh => by
      simpa only [norm_mul, norm_gramMellinPhase, mul_one] using hphase h hh)
  change ‖coprimeMellinKernel S H v w phase x y t‖ ≤
    coprimeNormMajorant S H U _ _ at h
  rw [coprimeNormMajorant_phases] at h
  exact h

end CubicFirstMoment

end
end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicGram_DyadicRecurrence
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinWeights
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PolynomialMeanValue
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Ordinary mean values after collecting Eisenstein norms

The input `MontgomeryVaughanBound` is the ordinary Dirichlet-polynomial
mean-square theorem of Montgomery--Vaughan, *Hilbert's inequality*,
J. London Math. Soc. (2) 8 (1974), Corollary 3, p. 75, equation (1.11),
in the form explicitly recorded
in the manuscript as `eq:ordinary-mean-value`.

The deductions below collect the actual Eisenstein norms, record their
multiplicity cost, and preserve an arbitrary fixed angular weight and
an arbitrary translated height. These are the ordinary mean-value steps
in `eq:dispersion-height-small` and `eq:angular-completed-height`.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace CubicFirstMoment

lemma mellinPhase_add (t u x : ℝ) :
    mellinPhase (t + u) x = mellinPhase t x * mellinPhase u x := by
  unfold mellinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma normPolynomial_collected (s : Finset Eisenstein) (v : Eisenstein → ℂ)
    (Z : ℕ) (hs : ∀ b ∈ s, normNat b ∈ Finset.Icc 1 Z) (t : ℝ) :
    eisensteinNormPolynomial s v t = integerNormPolynomial Z (normCollectedCoeff s v) t := by
  unfold eisensteinNormPolynomial integerNormPolynomial normCollectedCoeff
  rw [← Finset.sum_fiberwise_of_maps_to hs]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  have he := (Finset.mem_filter.mp hb).2
  rw [← normNat_cast b, he]

lemma norm_sum_sq_le_card_mul (s : Finset Eisenstein) (v : Eisenstein → ℂ) :
    ‖∑ b ∈ s, v b‖ ^ 2 ≤ (s.card : ℝ) * ∑ b ∈ s, ‖v b‖ ^ 2 := by
  have hnorm := norm_sum_le s v
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun b => ‖v b‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcauchy
  exact (sq_le_sq₀ (_root_.norm_nonneg _) (Finset.sum_nonneg (fun _ _ => _root_.norm_nonneg _))).mpr
    hnorm |>.trans hcauchy

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeConvolutionBounds
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeJoin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Collecting the squarefree majorant by least common multiples

The join is the product of the union of the primary prime factors. Its
square divides an element exactly when both input squares divide it.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_le_of_dvd_nonzero {a b : Eisenstein} (hb : b ≠ 0) (h : a ∣ b) : norm a ≤ norm b := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := by intro h; apply hb; rw [h,mul_zero]
  rw [norm_mul_eq]
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_norm hc)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeTupleDecomposition
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ModelPartialSummation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The elementary prime model from the ordinary prime ideal theorem

The only number-theoretic hypothesis used here is the ordinary asymptotic
for the number of primary prime elements.  The power-weighted consequence
is derived by Abel summation.
-/

noncomputable section

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace CubicFirstMoment

private lemma primaryPrimeFiber_eq (n : ℕ) (X : ℝ) (hn : (n : ℝ) ≤ X) :
    (primeCutoff (n : ℝ)).filter (fun p => normNat p = n) =
      (primeCutoff X).filter (fun p => normNat p = n) := by
  ext p
  simp only [Finset.mem_filter, mem_primeCutoff]
  constructor
  · intro hp
    exact ⟨⟨hp.1.1, hp.1.2.trans hn⟩, hp.2⟩
  · intro hp
    have he : norm p = (n : ℝ) := by rw [← normNat_cast p, hp.2]
    exact ⟨⟨hp.1.1, he.le⟩, hp.2⟩

lemma primaryPrimeMultiplicity_zero : primaryPrimeMultiplicity 0 = 0 := by
  have he : (primeCutoff (0 : ℝ)).filter (fun p => normNat p = 0) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hp' := (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
    have hn : norm p = 0 := by
      rw [← normNat_cast p, (Finset.mem_filter.mp hp).2, Nat.cast_zero]
    have hz : p = 0 := by
      apply Subtype.ext
      exact Complex.normSq_eq_zero.mp hn
    exact hp'.2.ne_zero hz
  simp only [primaryPrimeMultiplicity, Nat.cast_zero, he, Finset.card_empty]

lemma primeNorm_sum_eq (g : ℕ → ℝ) {X : ℝ} (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, g n * primaryPrimeMultiplicity n) =
      ∑ p ∈ primeCutoff X, g (normNat p) := by
  have hmaps : ∀ p ∈ primeCutoff X, normNat p ∈ Finset.Icc 0 ⌊X⌋₊ := by
    intro p hp
    simp only [Finset.mem_Icc, Nat.zero_le, true_and]
    apply (Nat.le_floor_iff hX).mpr
    rw [normNat_cast]
    exact (mem_primeCutoff.mp hp).2
  rw [← Finset.sum_fiberwise_of_maps_to' hmaps g]
  apply Finset.sum_congr rfl
  intro n hn
  have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX).mp (Finset.mem_Icc.mp hn).2
  rw [primaryPrimeMultiplicity, primaryPrimeFiber_eq n X hnX]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

lemma normCountingSum_primaryPrimeMultiplicity {X : ℝ} (hX : 0 ≤ X) :
    normCountingSum primaryPrimeMultiplicity X = primaryPrimeCount X := by
  simpa only [normCountingSum, one_mul, Finset.sum_const, nsmul_eq_mul, mul_one,
    primaryPrimeCount] using primeNorm_sum_eq (fun _ => 1) hX

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimaryPrimeUpper
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisensteinEuclideanDomain _root_.OAI.CubicFirstMoment.eisensteinNormalization _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instFiniteIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instFreeIntSubtypeComplexMemSubalgebraEisenstein _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The elementary counting upper bound needed in the smooth-number
Rankin argument, derived from the existing ordinary prime PNT input. -/
noncomputable section
open Filter
namespace CubicFirstMoment

lemma primaryPrimeCount_mono {x y : ℝ} (hxy : x ≤ y) :
    primaryPrimeCount x ≤ primaryPrimeCount y := by
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hp,hpx⟩ := mem_primeCutoff.mp hp
  exact mem_primeCutoff.mpr ⟨hp,hpx.trans hxy⟩

theorem primaryPrimeCount_upper (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 2 ≤ Y →
      primaryPrimeCount Y ≤ C*Y/Real.log Y := by
  have hevent : ∀ᶠ Y : ℝ in atTop,
      primaryPrimeCount Y*Real.log Y/Y < 2 :=
    hpnt.eventually (eventually_lt_nhds (by norm_num : (1:ℝ) < 2))
  obtain ⟨Y₀,hY₀⟩ := eventually_atTop.mp hevent
  let Q := max 2 Y₀
  let C := 2+primaryPrimeCount Q
  have hc : 0 ≤ primaryPrimeCount Q := Nat.cast_nonneg _
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro Y hY
  have hY1 : 1 < Y := lt_of_lt_of_le (by norm_num) hY
  have hY0 : 0 < Y := zero_lt_one.trans hY1
  have hl : 0 < Real.log Y := Real.log_pos hY1
  apply (le_div_iff₀ hl).mpr
  by_cases hQ : Q ≤ Y
  · have h := (div_lt_iff₀ hY0).mp (hY₀ Y ((le_max_right 2 Y₀).trans hQ))
    apply h.le.trans
    apply mul_le_mul_of_nonneg_right _ hY0.le
    dsimp [C]
    linarith
  · have hcount := primaryPrimeCount_mono (le_of_not_ge hQ)
    have hCQ : primaryPrimeCount Q ≤ C := by dsimp [C]; linarith
    calc
      primaryPrimeCount Y*Real.log Y ≤ C*Real.log Y :=
        mul_le_mul_of_nonneg_right (hcount.trans hCQ) hl.le
      _ ≤ C*Y := mul_le_mul_of_nonneg_left (Real.log_le_self hY0.le) hC.le

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_PrimeReciprocal
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The prime reciprocal estimate used in the smooth-number discard,
derived from ordinary prime counting by literal Abel summation. -/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma primaryPrimeMultiplicity_one : primaryPrimeMultiplicity 1 = 0 := by
  have he : (primeCutoff (1:ℝ)).filter (fun p => normNat p = 1) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro p hp
    have hpp := (mem_primeCutoff.mp (Finset.mem_filter.mp hp).1).1
    have hn : norm p = 1 := by
      rw [←normNat_cast p,(Finset.mem_filter.mp hp).2,Nat.cast_one]
    exact hpp.2.not_isUnit (isUnit_of_norm_eq_one hn)
  simp only [primaryPrimeMultiplicity,Nat.cast_one,he,Finset.card_empty,Nat.cast_zero]

private lemma inverse_square_continuous (X : ℝ) :
    ContinuousOn (fun t : ℝ => (t^2)⁻¹) (Set.Icc 2 X) := by
  apply (continuousOn_id.pow 2).inv₀
  intro t ht
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))

lemma primaryPrime_reciprocal_integrable {X : ℝ} (hX : 2 ≤ X) :
    IntervalIntegrable (fun t => primaryPrimeCount t/t^2) volume 2 X := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr
  have h := integrableOn_mul_sum_Icc (c := primaryPrimeMultiplicity)
    (m := 0) (a := 2) (b := X) (by norm_num)
    (inverse_square_continuous X).integrableOn_Icc
  apply h.congr_fun _ measurableSet_Icc
  intro t ht
  change (t^2)⁻¹*normCountingSum primaryPrimeMultiplicity t = _
  rw [normCountingSum_primaryPrimeMultiplicity (by linarith [ht.1])]
  ring

lemma primaryPrime_reciprocal_identity {X : ℝ} (hX : 2 ≤ X) :
    (∑ p ∈ primeCutoff X, (norm p)⁻¹) = primaryPrimeCount X/X+
      ∫ t in 2..X, primaryPrimeCount t/t^2 := by
  have hdiff : ∀ t ∈ Set.Icc (2:ℝ) X,
      DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))).differentiableAt
  have hderiv : ∀ t ∈ Set.Icc (2:ℝ) X,
      deriv (fun x : ℝ => x⁻¹) t = -(t^2)⁻¹ := by
    intro t ht
    exact (hasDerivAt_inv (ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1))).deriv
  have hint : IntegrableOn (deriv (fun x : ℝ => x⁻¹)) (Set.Icc 2 X) := by
    exact ((inverse_square_continuous X).neg.integrableOn_Icc).congr_fun
      (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ (c := primaryPrimeMultiplicity)
    primaryPrimeMultiplicity_zero primaryPrimeMultiplicity_one X hdiff hint
  rw [primeNorm_sum_eq (fun n => (n:ℝ)⁻¹) (by linarith)] at h
  change (∑ p ∈ primeCutoff X, (normNat p:ℝ)⁻¹) =
    X⁻¹*normCountingSum primaryPrimeMultiplicity X-
      ∫ t in Set.Ioc 2 X, deriv (fun x : ℝ => x⁻¹) t*
        normCountingSum primaryPrimeMultiplicity t at h
  rw [normCountingSum_primaryPrimeMultiplicity (by linarith),
    ←intervalIntegral.integral_of_le hX] at h
  have hi : (∫ t in 2..X, deriv (fun x : ℝ => x⁻¹) t*
      normCountingSum primaryPrimeMultiplicity t) =
      -(∫ t in 2..X, primaryPrimeCount t/t^2) := by
    rw [←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    dsimp only
    rw [hderiv t ht,normCountingSum_primaryPrimeMultiplicity (by linarith [ht.1])]
    ring
  rw [hi] at h
  simpa only [normNat_cast,sub_neg_eq_add,div_eq_mul_inv,mul_comm] using h

theorem primaryPrime_reciprocal_upper (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 2 ≤ X →
      (∑ p ∈ primeCutoff X, (norm p)⁻¹) ≤
        C/Real.log X+C*(Real.log (Real.log X)-Real.log (Real.log 2)) := by
  obtain ⟨C,hC,hcount⟩ := primaryPrimeCount_upper hpnt
  refine ⟨C,hC,?_⟩
  intro X hX
  have hX0 : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hlog : 0 < Real.log X := Real.log_pos (lt_of_lt_of_le (by norm_num) hX)
  rw [primaryPrime_reciprocal_identity hX]
  apply add_le_add
  · calc
      _ ≤ (C*X/Real.log X)/X := div_le_div_of_nonneg_right (hcount X hX) hX0.le
      _ = C/Real.log X := by field_simp
  · have hright : IntervalIntegrable (fun t : ℝ => t⁻¹/Real.log t) volume 2 X := by
      have hpos : ∀ t ∈ Set.uIcc (2:ℝ) X, 0 < t := by
        intro t ht
        rw [Set.uIcc_of_le hX] at ht
        exact lt_of_lt_of_le (by norm_num) ht.1
      have hinv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc 2 X) :=
        continuousOn_id.inv₀ (fun t ht => (hpos t ht).ne')
      have hlog : ContinuousOn Real.log (Set.uIcc 2 X) :=
        Real.continuousOn_log.mono (fun t ht => (hpos t ht).ne')
      apply (hinv.div hlog _).intervalIntegrable
      intro t ht
      rw [Set.uIcc_of_le hX] at ht
      exact (Real.log_pos (lt_of_lt_of_le (by norm_num) ht.1)).ne'
    calc
      _ ≤ ∫ t in 2..X, C*(t⁻¹/Real.log t) := by
        apply intervalIntegral.integral_mono_on hX (primaryPrime_reciprocal_integrable hX)
          (hright.const_mul C)
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht.1
        calc
          _ ≤ (C*t/Real.log t)/t^2 :=
            div_le_div_of_nonneg_right (hcount t ht.1) (sq_nonneg t)
          _ = C*(t⁻¹/Real.log t) := by field_simp
      _ = C*(Real.log (Real.log X)-Real.log (Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul,integral_inv_div_log (by norm_num)
          (lt_of_lt_of_le (by norm_num) hX)]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmoothRankinSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth-number discard on the exp(sqrt(log X)) scale.
Only the ordinary prime number theorem is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_reciprocal_exp_bound (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∑ p ∈ primeCutoff (Real.exp T), (norm p)⁻¹) ≤ C*(1+Real.log T) := by
  obtain ⟨C,hC,hbound⟩ := primaryPrime_reciprocal_upper hpnt
  let K : ℝ := 1+|Real.log (Real.log 2)|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg (Real.log (Real.log 2))]
  refine ⟨C*K,mul_pos hC (zero_lt_one.trans_le hK),?_⟩
  intro T hT
  have h2 : (2:ℝ) ≤ Real.exp T := by
    have htwo : (2:ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1:ℝ) using 1 <;> first | (with_reducible_and_instances rfl) | (norm_num)
    exact htwo.trans (Real.exp_le_exp.mpr hT)
  have hb := hbound (Real.exp T) h2
  simp only [Real.log_exp] at hb
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  calc
    _ ≤ C/T+C*(Real.log T-Real.log (Real.log 2)) := hb
    _ ≤ C+C*(Real.log T+|Real.log (Real.log 2)|) :=
      add_le_add (div_le_self hC.le hT)
        (mul_le_mul_of_nonneg_left (by linarith [neg_le_abs (Real.log (Real.log 2))]) hC.le)
    _ ≤ C*K*(1+Real.log T) := by
      dsimp [K]
      nlinarith [mul_nonneg (abs_nonneg (Real.log (Real.log 2))) hlog]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_QuantitativeNoncube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedCharacterRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed-angular stopped coefficient and its exact character row.
Angular multiplication preserves the proved pointwise and energy bounds;
cube factors and divisor exclusions remain literal finite identities. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angularStoppedRowCoefficient_norm (ℓ : ℤ) (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) {n : Eisenstein} (hn : primary n) :
    ‖angularStoppedRowCoefficient ℓ X w z u W selected n‖ =
      ‖stoppedRowCoefficient X w z u W selected n‖ := by
  rw [angularStoppedRowCoefficient,norm_mul,norm_theta (primary_ne_zero hn),mul_one]

theorem angular_stopped_interval_energy (ℓ : ℤ) {ξ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (u a b : ℝ) (e : Eisenstein),
      0 ≤ b → b ≤ X →
      (∀ n ∈ stoppedIntervalSupport ι X a b e,
        ‖angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n‖ ≤ M) ∧
      (∑ n ∈ stoppedIntervalSupport ι X a b e,
        ‖angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n‖^2) ≤
          18*b*M^2 := by
  obtain ⟨M,hM,he⟩ := stopped_interval_energy (ι := ι) hξ hξz
  refine ⟨M,hM,?_⟩
  filter_upwards [he] with X he
  intro W hW selected u a b e hb hbX
  have hnorm (n : Eisenstein) (hn : n ∈ stoppedIntervalSupport ι X a b e) :=
    angularStoppedRowCoefficient_norm ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected
      (stoppedIntervalSupport_spec X a b e hn).1
  constructor
  · intro n hn
    rw [hnorm n hn]
    exact (he W hW selected u a b e hb hbX).1 n hn
  · have hsum : (∑ n ∈ stoppedIntervalSupport ι X a b e,
          ‖angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n‖^2) =
        ∑ n ∈ stoppedIntervalSupport ι X a b e,
          ‖stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n‖^2 :=
      Finset.sum_congr rfl (fun n hn => by rw [hnorm n hn])
    rw [hsum]
    exact (he W hW selected u a b e hb hbX).2

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorRowEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The total energy of all rows in the genuine coprimality expansion.
Every coefficient occurs once per squarefree primary divisor, so the
loss is bounded by an arbitrarily small norm power. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma prime_subset_divisor_count (U : Finset Eisenstein)
    (hU : ∀ p ∈ U, primaryPrime p) {a : Eisenstein} (ha : primary a) :
    (U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ a)).card ≤
      2^(primaryPrimeFactors a).card := by
  rw [← Finset.card_powerset]
  apply Finset.card_le_card
  intro s hs
  obtain ⟨hsU,hd⟩ := Finset.mem_filter.mp hs
  apply Finset.mem_powerset.mpr
  intro p hp
  apply (primaryPrime_mem_factors_iff ha).mpr
  exact ⟨hU p (Finset.mem_powerset.mp hsU hp),
    dvd_trans (Finset.dvd_prod_of_mem (fun p : Eisenstein => p) hp) hd⟩

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

lemma gramMellinPhase_eq_mellinPhase (t x : ℝ) :
    gramMellinPhase t x = mellinPhase (2*Real.pi*t) x := by
  rw [gramMellinPhase,Real.fourierChar_apply]
  unfold mellinPhase
  congr 1
  push_cast
  ring

lemma mellinPhase_add_height (u v x : ℝ) :
    mellinPhase (u+v) x = mellinPhase u x*mellinPhase v x := by
  unfold mellinPhase
  rw [show (((u+v)*Real.log x:ℝ):ℂ)*Complex.I =
    ((u*Real.log x:ℝ):ℂ)*Complex.I+((v*Real.log x:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

lemma gramMellinPhase_ratio (t : ℝ) {x N : ℝ} (hx : 0 < x) (hN : 0 < N) :
    gramMellinPhase t (x/N) =
      mellinPhase (2*Real.pi*t) x*mellinPhase (-(2*Real.pi*t)) N := by
  rw [gramMellinPhase_eq_mellinPhase]
  unfold mellinPhase
  rw [Real.log_div hx.ne' hN.ne']
  rw [show (((2*Real.pi*t)*(Real.log x-Real.log N):ℝ):ℂ)*Complex.I =
    (((2*Real.pi*t)*Real.log x:ℝ):ℂ)*Complex.I+
      ((-(2*Real.pi*t)*Real.log N:ℝ):ℂ)*Complex.I by push_cast; ring,
    Complex.exp_add]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_GramStructuredRows
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rows in the Poisson kernel are exactly the full structured prime
sums, including the squarefree restriction and the reversal of Mellin height. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gramMellinPhase_neg (t x : ℝ) :
    gramMellinPhase (-t) x = star (gramMellinPhase t x) := by
  rw [gramMellinPhase_eq_mellinPhase,gramMellinPhase_eq_mellinPhase,star_mellinPhase]
  congr 1
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreSupport
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_StructuredHeightMass
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite frequency blocks retain the proved height mean, with an explicit
row count for the actual ramified and cube decomposition. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_dyadic_integral_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ a ∈ S, Continuous (f a)) (T : ℝ) :
    ((∫ t in T..2*T, ∑ a ∈ S, f a t) + (∫ t in -2*T..-T, ∑ a ∈ S, f a t))/T =
      ∑ a ∈ S, ((∫ t in T..2*T, f a t)+(∫ t in -2*T..-T, f a t))/T := by
  rw [intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    intervalIntegral.integral_finsetSum (fun a ha => (hf a ha).intervalIntegrable _ _),
    ← Finset.sum_add_distrib,Finset.sum_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightAveraging
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive, normalized two-sided height averaging. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma dyadicHeightMean_mono {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ g t) :
    dyadicHeightMean f T ≤ dyadicHeightMean g T := by
  apply div_le_div_of_nonneg_right _ hT.le
  apply add_le_add
  · apply intervalIntegral.integral_mono_on (by linarith : T ≤ 2*T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨by linarith [ht.1],ht.2⟩
  · apply intervalIntegral.integral_mono_on (by linarith : -2*T ≤ -T)
      (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    intro t ht
    exact h t ⟨ht.1,by linarith [ht.2]⟩

lemma dyadicHeightMean_const (C : ℝ) {T : ℝ} (hT : T ≠ 0) :
    dyadicHeightMean (fun _ => C) T = 2*C := by
  simp only [dyadicHeightMean,intervalIntegral.integral_const,smul_eq_mul]
  field_simp
  ring

lemma dyadicHeightMean_le_const {f : ℝ → ℝ} (hf : Continuous f)
    {T C : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (-2*T) (2*T), f t ≤ C) :
    dyadicHeightMean f T ≤ 2*C :=
  (dyadicHeightMean_mono hf continuous_const hT h).trans_eq
    (dyadicHeightMean_const C hT.ne')

lemma dyadicHeightMean_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (T : ℝ) :
    dyadicHeightMean (fun t => f t+g t) T = dyadicHeightMean f T+dyadicHeightMean g T := by
  simp only [dyadicHeightMean,intervalIntegral.integral_add
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  ring

lemma dyadicHeightMean_sum {α : Type*} (S : Finset α) (f : α → ℝ → ℝ)
    (hf : ∀ a ∈ S, Continuous (f a)) (T : ℝ) :
    dyadicHeightMean (fun t => ∑ a ∈ S, f a t) T = ∑ a ∈ S, dyadicHeightMean (f a) T :=
  finite_dyadic_integral_sum S f hf T

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CubicDyadicCoverage
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightCubeMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube frequencies in a height average use the ordinary polynomial
mean, rather than the low-height cube lattice asymptotic. -/
noncomputable section
open scoped BigOperators
open Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

lemma mem_nonzeroCubeNormBall {B : ℝ} {h : Eisenstein}
    (hh : h ≠ 0) (hB : norm h ≤ B) (hc : ∃ z : Eisenstein, z^3 = h) :
    h ∈ nonzeroCubeNormBall B := by
  obtain ⟨z,hz⟩ := hc
  have hz0 : z ≠ 0 := by intro he; apply hh; rw [←hz,he]; simp
  have hr := cube_part_norm_bound (h := h) (v := 1) (j := z) one_ne_zero
    (by simpa using hz.symm) hB
  exact Finset.mem_image.mpr ⟨z,mem_nonzeroNormBall.mpr ⟨hr,hz0⟩,hz⟩

lemma nonzeroCubeNormBall_card {B : ℝ} (hB : 0 ≤ B) :
    ((nonzeroCubeNormBall B).card:ℝ) ≤ 18*B^(1/3:ℝ) :=
  (Nat.cast_le.mpr Finset.card_image_le).trans
    (nonzeroNormBall_card_le (Real.rpow_nonneg hB (1/3:ℝ)))

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_HeightMeanSquare
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite spectral expansion of the height-averaged square.
The diagonal and every off-diagonal pair are retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_normTwist (b : Eisenstein) : Continuous (fun u : ℝ => normTwist u b) := by
  unfold normTwist
  fun_prop

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArbitraryHeightMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary height means for arbitrary primary coefficient supports,
including sharp norm cells and every translated angular mode. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma continuous_finite_character_height (B : Finset Eisenstein)
    (β : Eisenstein → ℂ) (h : Eisenstein) (ℓ : ℤ) (u : ℝ) :
    Continuous (fun t => ∑ b ∈ B, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)) := by
  apply continuous_finsetSum
  intro b hb
  change Continuous (fun t => (β b*cubicSymbol b h*theta ℓ b)*normTwist (t+u) b)
  exact continuous_const.mul ((continuous_normTwist b).comp (continuous_id.add continuous_const))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramMellin
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact Mellin separation on the entire fixed norm range of a prime
convolution. The cutoff belongs to the transform, so no cutoff is inserted
into the arithmetic coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma wideGramLogKernel_eq_radial (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    {ρ u : ℝ} (hρ : 0 ≤ ρ) (hu : |u| ≤ M) :
    wideGramLogKernel M hM W ρ u = radialDualProfile W (ρ*Real.exp u) := by
  have hcut : wideGramLogBump M hM u = 1 :=
    (wideGramLogBump M hM).one_of_mem_closedBall
      (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,wideGramLogBump] using hu)
  rw [wideGramLogKernel,hcut,one_smul,normProfileFourier_radial]
  congr 1
  rw [Complex.normSq_ofReal]
  calc
    _ = (Real.sqrt ρ*Real.sqrt ρ)*(Real.exp (u/2)*Real.exp (u/2)) := by ring
    _ = _ := by rw [Real.mul_self_sqrt hρ,← Real.exp_add]; congr 2; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WideGramDecay
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform Fourier decay for the fixed wider log-norm cutoff used by the
actual prime convolution. -/
noncomputable section
open scoped BigOperators SchwartzMap ContDiff FourierTransform
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma wideGramExp_deriv_bound (M : ℝ) (n : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (i : ℕ), i ≤ n → ∀ u : ℝ, |u| ≤ 2*M →
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D := by
  have hb (i : ℕ) : ∃ D : ℝ, ∀ u ∈ Set.Icc (-2*M) (2*M),
      ‖iteratedFDeriv ℝ i gramExp u‖ ≤ D :=
    isCompact_Icc.exists_bound_of_continuousOn
      (gramExp_contDiff.continuous_iteratedFDeriv (mod_cast le_top)).continuousOn
  choose B hB using hb
  let D := 1 + ∑ i ∈ Finset.range (n+1), |B i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (n+1), |B i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨D, by dsimp [D]; linarith, ?_⟩
  intro i hi u hu
  have hbi : |B i| ≤ ∑ j ∈ Finset.range (n+1), |B j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_range.mpr (by omega))
  exact (hB i u ⟨by linarith [(abs_le.mp hu).1], (abs_le.mp hu).2⟩).trans
    ((le_abs_self (B i)).trans (hbi.trans (by dsimp [D]; linarith)))

lemma wideGramExp_scale_growth {M c u : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) (hu : |u| ≤ 2*M) :
    1+c ≤ Real.exp M * (1+‖c • gramExp u‖) := by
  have hE : 1 ≤ Real.exp M := Real.one_le_exp hM
  have hEu : 1 ≤ Real.exp M * Real.exp (u/2) := by
    rw [← Real.exp_add]
    simpa using Real.exp_le_exp.mpr (show (0:ℝ) ≤ M + u/2 by
      linarith [(abs_le.mp hu).1])
  have hEc := mul_le_mul_of_nonneg_left hEu hc
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, gramExp,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  nlinarith

theorem schwartz_wideGramExp_comp_uniform (M : ℝ) (hM : 0 ≤ M) (F : 𝓢(ℂ, ℂ)) (n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c → ∀ u : ℝ, |u| ≤ 2*M →
      (1+c)^K * ‖iteratedFDeriv ℝ n (fun v => F (c • gramExp v)) u‖ ≤ C := by
  obtain ⟨D, hD, hderiv⟩ := wideGramExp_deriv_bound M n
  let L := n+K
  let S := (Finset.Iic (L,n)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) F
  let H := (Real.exp M)^L * 2^L * S
  have hS : 0 ≤ S := by positivity
  have hH : 0 ≤ H := by positivity
  refine ⟨(n.factorial : ℝ)*H*D^n, by positivity, ?_⟩
  intro c hc u hu
  have hc1 : 0 < 1+c := by positivity
  have hC (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ ≤ H / (1+c)^L := by
    rw [le_div_iff₀' (pow_pos hc1 L)]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (L,n)) (k := L) (n := i) (le_refl L) hi F (c • gramExp u)
    calc
      _ ≤ (Real.exp M * (1+‖c • gramExp u‖))^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖ := by
        gcongr
        exact wideGramExp_scale_growth hM hc hu
      _ = (Real.exp M)^L * ((1+‖c • gramExp u‖)^L *
            ‖iteratedFDeriv ℝ i F (c • gramExp u)‖) := by rw [mul_pow]; ring
      _ ≤ (Real.exp M)^L * (2^L*S) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = H := by dsimp [H]; ring
  have hDb (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDeriv ℝ i (fun v => c • gramExp v) u‖ ≤ ((1+c)*D)^i := by
    rw [iteratedFDeriv_const_smul_apply' (gramExp_contDiff.of_le (mod_cast le_top)).contDiffAt,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
    calc
      _ ≤ c*D := mul_le_mul_of_nonneg_left (hderiv i hin u hu) hc
      _ ≤ (1+c)*D := by nlinarith
      _ ≤ ((1+c)*D)^i := le_self_pow₀ (by nlinarith) (by omega)
  have hb := norm_iteratedFDeriv_comp_le (F.smooth ⊤) (gramExp_contDiff.const_smul c)
    (n := n) (mod_cast le_top) u hC hDb
  calc
    _ ≤ (1+c)^K * ((n.factorial : ℝ)*(H/(1+c)^L)*((1+c)*D)^n) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (n.factorial : ℝ)*H*D^n := by
      dsimp [L]
      rw [pow_add, mul_pow]
      field_simp


lemma wideAnnularLogSchwartz_deriv_zero (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (c u : ℝ) (n : ℕ)
    (hu : ¬ |u| ≤ 2*M) : iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u = 0 := by
  by_contra hn
  have hs := support_iteratedFDeriv_subset (𝕜 := ℝ) (f := wideAnnularLogSchwartz M hM F c) n hn
  have hb := tsupport_smul_subset_left ((wideGramLogBump M hM) : ℝ → ℝ)
    (fun v => F (c • gramExp v)) hs
  rw [(wideGramLogBump M hM).tsupport_eq] at hb
  exact hu (by simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, wideGramLogBump] using hb)

theorem wideAnnularLogSchwartz_seminorm_uniform (M : ℝ) (hM : 0 < M) (F : 𝓢(ℂ, ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c →
      (1+c)^K * SchwartzMap.seminorm ℝ k n (wideAnnularLogSchwartz M hM F c) ≤ C := by
  choose C hC hbound using fun i => schwartz_wideGramExp_comp_uniform M hM.le F i K
  let B : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
    SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) * C (n-i)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => mul_nonneg (by positivity) (hC (n-i)))
  refine ⟨(2*M)^k * B, by positivity, ?_⟩
  intro c hc
  have hp : 0 < (1+c)^K := pow_pos (by positivity) _
  rw [← le_div_iff₀' hp]
  apply SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity)
  intro u
  by_cases hu : |u| ≤ 2*M
  · rw [le_div_iff₀' hp]
    have hd := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (wideGramLogBump M hM).contDiff
      ((F.smooth ⊤).comp (gramExp_contDiff.const_smul c)) u (n := n) (mod_cast le_top)
    have hd' : (1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖ ≤ B := by
      calc
        _ ≤ (1+c)^K * ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
              ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖ :=
          mul_le_mul_of_nonneg_left hd hp.le
        _ = ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ *
              ((1+c)^K * ‖iteratedFDeriv ℝ (n-i) (fun v => F (c • gramExp v)) u‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ B := by
          apply Finset.sum_le_sum
          intro i hi
          have hb : ‖iteratedFDeriv ℝ i (wideGramLogBump M hM) u‖ ≤
              SchwartzMap.seminorm ℝ 0 i (wideGramBumpSchwartz M hM) := by
            have hb := SchwartzMap.le_seminorm ℝ 0 i (wideGramBumpSchwartz M hM) u
            rw [show (wideGramBumpSchwartz M hM : ℝ → ℝ) = ((wideGramLogBump M hM) : ℝ → ℝ) from rfl] at hb
            simpa only [pow_zero, one_mul] using hb
          exact mul_le_mul (mul_le_mul_of_nonneg_left hb (by positivity))
            (hbound (n-i) c hc u hu) (by positivity) (by positivity)
    calc
      _ = ‖u‖^k * ((1+c)^K * ‖iteratedFDeriv ℝ n (wideAnnularLogSchwartz M hM F c) u‖) := by ring
      _ ≤ (2*M)^k * B := mul_le_mul (pow_le_pow_left₀ (_root_.norm_nonneg _)
        (by simpa only [Real.norm_eq_abs] using hu) k) hd' (by positivity) (by positivity)
  · rw [wideAnnularLogSchwartz_deriv_zero M hM F c u n hu, norm_zero, mul_zero]
    positivity

lemma wideAnnularLogSchwartz_eq_wideGramLogSchwartz (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ) =
      wideGramLogSchwartz M hM W hW hW' ρ := by
  ext u
  simp only [wideAnnularLogSchwartz_apply M hM, wideGramLogSchwartz_apply, wideGramLogKernel,
    normProfileFourierSchwartz_apply]
  congr 2
  simp only [gramExp, Complex.real_smul, Complex.ofReal_mul]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormDenominatorMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The norm denominator in the actual Poisson formula stays in its
Mellin kernel. No real power is inserted into the prime coefficients. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

lemma normDenominatorMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    Integrable (normDenominatorMellinCoefficient M hM W hW hW' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integrable

lemma normDenominatorLogSchwartz_apply (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ u : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ u =
      (Real.exp (u/2):ℂ)*wideGramLogKernel M hM W ρ u := by
  rw [normDenominatorLogSchwartz,SchwartzMap.smulLeftCLM_apply_apply
    (normDenominatorMultiplier M hM).hasTemperateGrowth,wideGramLogSchwartz_apply]
  change ((wideGramLogBump (2*M) (by positivity) u:ℝ) • (Real.exp (u/2):ℂ)) •
    wideGramLogKernel M hM W ρ u = _
  by_cases hu : |u| ≤ 2*M
  · have he : wideGramLogBump (2*M) (by positivity) u = 1 :=
      (wideGramLogBump (2*M) (by positivity)).one_of_mem_closedBall
        (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,wideGramLogBump] using hu)
    rw [he,one_smul,smul_eq_mul]
  · have he : wideGramLogBump M hM u = 0 :=
      (wideGramLogBump M hM).zero_of_le_dist
        (by simpa only [Real.dist_eq,sub_zero,wideGramLogBump] using le_of_not_ge hu)
    simp only [wideGramLogKernel,he,zero_smul,smul_zero,mul_zero]

lemma normDenominatorLogSchwartz_eq_radial (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ u : ℝ} (hρ : 0 ≤ ρ) (hu : |u| ≤ M) :
    normDenominatorLogSchwartz M hM W hW hW' ρ u =
      (Real.exp (u/2):ℂ)*radialDualProfile W (ρ*Real.exp u) := by
  rw [normDenominatorLogSchwartz_apply,wideGramLogKernel_eq_radial M hM W hρ hu]


lemma normDenominatorLogSchwartz_eq_annular (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (ρ : ℝ) :
    normDenominatorLogSchwartz M hM W hW hW' ρ =
      SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM (normProfileFourierSchwartz W hW hW') (Real.sqrt ρ)) := by
  rw [wideAnnularLogSchwartz_eq_wideGramLogSchwartz]
  rfl

lemma normDenominatorFourier_seminorm_uniform (M : ℝ) (hM : 0 < M)
    (F : 𝓢(ℂ,ℂ)) (k n K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 ≤ c → (1+c)^K * SchwartzMap.seminorm ℝ k n
      (𝓕 (SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)
        (wideAnnularLogSchwartz M hM F c))) ≤ C := by
  let f : ℝ → 𝓢(ℝ,ℂ) := fun c => (1+c)^K • wideAnnularLogSchwartz M hM F c
  have hb : Bornology.IsVonNBounded ℝ (f '' Ici 0) := by
    apply (schwartz_withSeminorms ℝ ℝ ℂ).image_isVonNBounded_iff_seminorm_bounded f |>.2
    intro i
    obtain ⟨C,hC,hc⟩ := wideAnnularLogSchwartz_seminorm_uniform M hM F i.1 i.2 K
    refine ⟨C+1,by linarith,?_⟩
    intro c hc0
    have hc0' : 0 ≤ c := hc0
    change SchwartzMap.seminorm ℝ i.1 i.2 ((1+c)^K • wideAnnularLogSchwartz M hM F c) < _
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos (pow_pos (by linarith [hc0']) _)]
    exact (hc c hc0).trans_lt (by linarith)
  let A : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
    (SchwartzMap.fourierTransformCLM ℝ (V := ℝ) (E := ℂ)).comp
      ((SchwartzMap.smulLeftCLM ℂ (normDenominatorMultiplier M hM)).restrictScalars ℝ)
  have hA := hb.image A
  obtain ⟨C,hC,hc⟩ :=
    (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mp hA (k,n)
  refine ⟨C,hC,?_⟩
  intro c hc0
  have h := hc (A (f c)) ⟨f c,⟨c,hc0,rfl⟩,rfl⟩
  change SchwartzMap.seminorm ℝ k n (A ((1+c)^K • wideAnnularLogSchwartz M hM F c)) < C at h
  rw [map_smul,map_smul_eq_mul,Real.norm_eq_abs,
    abs_of_pos (pow_pos (by linarith) _)] at h
  exact h.le

theorem normDenominatorMellinCoefficient_pointwise_rapidDecay (M : ℝ) (hM : 0 < M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ t : ℝ,
      (1+ρ)^A * ‖t‖^B * ‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖ ≤ C := by
  obtain ⟨C,hC,hc⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') B 0 (2*A)
  refine ⟨C,hC,?_⟩
  intro ρ hρ t
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have hb := SchwartzMap.le_seminorm ℝ B 0
    (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)) t
  simp only [norm_iteratedFDeriv_zero] at hb
  have h := hc (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [← normDenominatorLogSchwartz_eq_annular] at h
  calc
    _ = (1+ρ)^A * (‖t‖^B * ‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) := by ring
    _ ≤ (1+Real.sqrt ρ)^(2*A) * SchwartzMap.seminorm ℝ B 0
        (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)) :=
      mul_le_mul hs hb (by positivity) (by positivity)
    _ ≤ C := h

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormMellinMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrated decay with polynomial Mellin-height weights. This controls
truncated shifts in the dispersion kernel. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

theorem normDenominatorMellinCoefficient_moment_decay (M : ℝ) (hM : 0 < M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) (A B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ C := by
  let k := (volume : Measure ℝ).integrablePower
  let D : ℝ := 2^k * ∫ t : ℝ, (1+‖t‖)^(-(k:ℝ))
  have hD : 0 ≤ D := mul_nonneg (by positivity) (integral_nonneg (fun t => by positivity))
  obtain ⟨C₀,hC₀,hc₀⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') 0 0 (2*A)
  obtain ⟨C₁,hC₁,hc₁⟩ := normDenominatorFourier_seminorm_uniform M hM
    (normProfileFourierSchwartz W hW hW') (B+k) 0 (2*A)
  refine ⟨D*(C₀+C₁)+1,by positivity,?_⟩
  intro ρ hρ
  have hs : (1+ρ)^A ≤ (1+Real.sqrt ρ)^(2*A) := by
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [Real.sq_sqrt hρ,Real.sqrt_nonneg ρ]
  have h := (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)).integral_pow_mul_iteratedFDeriv_le ℝ volume B 0
  simp only [norm_iteratedFDeriv_zero] at h
  have h₀ := hc₀ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  have h₁ := hc₁ (Real.sqrt ρ) (Real.sqrt_nonneg ρ)
  rw [← normDenominatorLogSchwartz_eq_annular] at h₀ h₁
  have hb : (1+ρ)^A * (∫ t : ℝ, ‖t‖^B*‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖) ≤ D*(C₀+C₁) := by
    calc
      _ ≤ (1+Real.sqrt ρ)^(2*A) * (D *
          (SchwartzMap.seminorm ℝ 0 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
           SchwartzMap.seminorm ℝ (B+k) 0 (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ)))) :=
        mul_le_mul hs h (integral_nonneg (fun t => by positivity)) (by positivity)
      _ = D*((1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ 0 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))+
        (1+Real.sqrt ρ)^(2*A)*SchwartzMap.seminorm ℝ (B+k) 0
          (𝓕 (normDenominatorLogSchwartz M hM W hW hW' ρ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add h₀ h₁) hD
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticMellinKernel
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the Fourier-transform frequency to the arithmetic height in
N(n)^(it). The fixed factor 2π stays in the actual kernel. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set MeasureTheory
namespace CubicFirstMoment

lemma arithmeticMellinCoefficient_continuous (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) :
    Continuous (arithmeticMellinCoefficient M hM V hV hV' ρ) :=
  (𝓕 (normDenominatorLogSchwartz M hM V hV hV' ρ)).continuous.comp
    (continuous_id.div_const _)

lemma arithmeticMellinCoefficient_integrable (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) :
    Integrable (arithmeticMellinCoefficient M hM V hV hV' ρ) :=
  (normDenominatorMellinCoefficient_integrable M hM V hV hV' ρ).comp_div
    (mul_ne_zero (by norm_num) Real.pi_ne_zero)

theorem arithmeticMellinCoefficient_quadratic_decay (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ t : ℝ,
      (1+ρ)^q*‖t‖^2*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖ ≤ D := by
  obtain ⟨C,hC,hb⟩ := normDenominatorMellinCoefficient_pointwise_rapidDecay M hM V hV hV' q 2
  have hc : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  refine ⟨C*(2*Real.pi)^2,mul_pos hC (sq_pos_of_ne_zero hc),?_⟩
  intro ρ hρ t
  have h := mul_le_mul_of_nonneg_right (hb ρ hρ (t/(2*Real.pi))) (sq_nonneg (2*Real.pi))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  simp only [arithmeticMellinCoefficient,Real.norm_eq_abs,sq_abs,div_pow]
  field_simp

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_ArithmeticMellinMoments
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial integral moments after the exact 2π rescaling. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace CubicFirstMoment

lemma arithmetic_mellin_moment_scale (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (ρ : ℝ) (k : ℕ) (t : ℝ) :
    ‖t‖^k*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖ =
      (2*Real.pi)^k*(‖t/(2*Real.pi)‖^k*
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ (t/(2*Real.pi))‖) := by
  have hc : 2*Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  simp only [arithmeticMellinCoefficient,norm_div,Real.norm_of_nonneg (by positivity : 0 ≤ 2*Real.pi),div_pow]
  field_simp

theorem arithmeticMellinCoefficient_moment_decay (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖t‖^k*‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖) ≤ C := by
  obtain ⟨C,hC,hb⟩ := normDenominatorMellinCoefficient_moment_decay M hM V hV hV' q k
  refine ⟨(2*Real.pi)^(k+1)*C,by positivity,?_⟩
  intro ρ hρ
  simp_rw [arithmetic_mellin_moment_scale]
  have he := Measure.integral_comp_div
    (fun t : ℝ => ‖t‖^k*‖normDenominatorMellinCoefficient M hM V hV hV' ρ t‖) (2*Real.pi)
  rw [integral_const_mul,he,abs_of_pos (by positivity : 0 < 2*Real.pi),smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (hb ρ hρ) (pow_nonneg (by positivity : 0 ≤ 2*Real.pi) (k+1))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  rw [pow_succ]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SmallBMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual arbitrary-coefficient small-B mass over the entire Mellin
line. The height bound is uniform in translation, so no tail is assumed. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma finite_character_mass_bound (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ b ∈ S, primary b) (ℓ : ℤ) (t : ℝ) :
    ‖∑ h ∈ H, ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase t (norm b)‖^2‖ ≤
      (H.card:ℝ)*S.card*∑ b ∈ S, ‖β b‖^2 := by
  rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  have hrow (h : Eisenstein) :
      ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase t (norm b)‖^2 ≤
      (S.card:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
    apply (norm_sum_sq_le_card_mul S _).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro b hb
    apply pow_le_pow_left₀ (_root_.norm_nonneg _) _ 2
    simp only [norm_mul,norm_theta (primary_ne_zero (hS b hb)),mellinPhase_norm,mul_one]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS b hb) h)
  apply (Finset.sum_le_sum (fun h _ => hrow h)).trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FiniteCharacterMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrary finite cubic-character rows and their exact Mellin twists. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma finiteCharacterMass_nonneg (S H : Finset Eisenstein) (β : Eisenstein → ℂ) (u : ℝ) :
    0 ≤ finiteCharacterMass S H β u := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma finiteCharacterMass_continuous (S H : Finset Eisenstein) (β : Eisenstein → ℂ) :
    Continuous (finiteCharacterMass S H β) := by
  unfold finiteCharacterMass
  apply continuous_finsetSum
  intro h hh
  convert (continuous_finite_character_height S β h 0 0).norm.pow 2 using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  simp only [Pi.pow_apply,theta_zero,mul_one,add_zero]

lemma finiteCharacterMass_bound (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (u : ℝ) :
    ‖finiteCharacterMass S H β u‖ ≤ (H.card:ℝ)*S.card*∑ a ∈ S, ‖β a‖^2 := by
  simpa only [finiteCharacterMass,theta_zero,mul_one] using
    finite_character_mass_bound S H β hS 0 u

lemma finite_character_gram_row_norm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (h : Eisenstein) (u s : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ S, star (β a*mellinPhase u (norm a))*
      star (gramMellinPhase s (norm a/N))*star (cubicSymbol a h)‖ =
    ‖∑ a ∈ S, β a*cubicSymbol a h*mellinPhase (u+2*Real.pi*s) (norm a)‖ := by
  have he : (∑ a ∈ S, star (β a*mellinPhase u (norm a))*
      star (gramMellinPhase s (norm a/N))*star (cubicSymbol a h)) =
      star (mellinPhase (-(2*Real.pi*s)) N*
        ∑ a ∈ S, β a*cubicSymbol a h*mellinPhase (u+2*Real.pi*s) (norm a)) := by
    rw [star_mul,star_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [gramMellinPhase_ratio s (norm_pos_of_ne_zero (primary_ne_zero (hS a ha))) hN,
      mellinPhase_add_height]
    simp only [star_mul]
    ring
  rw [he,norm_star,norm_mul,mellinPhase_norm,one_mul]

lemma finite_character_gram_reverse_row_norm (S : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (h : Eisenstein) (u s : ℝ) {N : ℝ} (hN : 0 < N) :
    ‖∑ a ∈ S, star (β a*mellinPhase u (norm a))*
      gramMellinPhase s (norm a/N)*star (cubicSymbol a h)‖ =
    ‖∑ a ∈ S, β a*cubicSymbol a h*mellinPhase (u-2*Real.pi*s) (norm a)‖ := by
  have he := finite_character_gram_row_norm S β hS h u (-s) hN
  simpa only [gramMellinPhase_neg,star_star,mul_neg,← sub_eq_add_neg] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeMellinMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The divisor expansion of the actual radial kernel is bounded by its
literal character-row masses. This keeps the oscillation that is lost in
the coarse operator norm bound. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finite_bilinear_mass_bound {α : Type*} (H : Finset α)
    (v w phase : α → ℂ) (hp : ∀ h ∈ H, ‖phase h‖ ≤ 1) :
    ‖∑ h ∈ H, phase h*v h*star (w h)‖ ≤
      ((∑ h ∈ H, ‖v h‖^2)+(∑ h ∈ H, ‖w h‖^2))/2 := by
  apply (norm_sum_le _ _).trans
  rw [← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro h hh
  rw [norm_mul,norm_mul,norm_star]
  calc
    _ ≤ ‖v h‖*‖w h‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (_root_.norm_nonneg _) (hp h hh)) (_root_.norm_nonneg _)
    _ ≤ _ := by nlinarith [sq_nonneg (‖v h‖-‖w h‖)]

theorem norm_coprimeMellinKernel_le_mass (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ) (t : ℝ) :
    ‖coprimeMellinKernel S H v w phase x y t‖ ≤ coprimeMellinMass S H U v w y t := by
  let V (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h)
  let W (s : Finset Eisenstein) (h : Eisenstein) : ℂ :=
    ∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a),
      w a*gramMellinPhase t (y a)*star (cubicSymbol a h)
  have he (h : Eisenstein) := coprime_bilinear_moebius S S U hS hU hSU
    (fun a => v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h))
    (fun a => w a*gramMellinPhase t (y a)*star (cubicSymbol a h))
  have he' (h : Eisenstein) :
      (∑ a ∈ S, ∑ b ∈ S, if IsCoprime a b then
        (v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h))*
          star (w b*gramMellinPhase t (y b)*star (cubicSymbol b h)) else 0) =
      ∑ s ∈ U.powerset, (idealMoebius (∏ p ∈ s, p):ℂ)*V s h*star (W s h) := by
    simpa only [V,W,Finset.sum_filter] using he h
  unfold coprimeMellinKernel
  simp_rw [he',Finset.mul_sum]
  rw [Finset.sum_comm]
  have hf (s : Finset Eisenstein) :
      (∑ h ∈ H, (phase h*gramMellinPhase t (x h))*
        ((idealMoebius (∏ p ∈ s, p):ℂ)*V s h*star (W s h))) =
      (idealMoebius (∏ p ∈ s, p):ℂ)*
        ∑ h ∈ H, (phase h*gramMellinPhase t (x h))*V s h*star (W s h) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  simp_rw [hf]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [norm_mul]
  apply (mul_le_of_le_one_left (_root_.norm_nonneg _) (norm_idealMoebius_le_one _)).trans
  exact finite_bilinear_mass_bound H (V s) (W s)
    (fun h => phase h*gramMellinPhase t (x h)) (fun h hh => by
      simpa only [norm_mul,norm_gramMellinPhase,mul_one] using hphase h hh)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_CoprimeMellinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An integral estimate for the literal radial Poisson form in terms of
the actual divisor-restricted character moments. -/
noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma mellin_character_row_norm_le (S : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (v : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (h : Eisenstein) (t : ℝ) :
    ‖∑ a ∈ S, v a*gramMellinPhase t (y a)*star (cubicSymbol a h)‖ ≤
      ∑ a ∈ S, ‖v a‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a ha
  rw [norm_mul,norm_mul,norm_gramMellinPhase,mul_one,norm_star]
  exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS a ha) _)

lemma coprimeMellinMass_nonneg (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) : 0 ≤ coprimeMellinMass S H U v w y t := by
  apply Finset.sum_nonneg
  intro s hs
  exact div_nonneg (add_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))) (by norm_num)

lemma coprimeMellinMass_continuous (S H U : Finset Eisenstein) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) : Continuous (coprimeMellinMass S H U v w y) := by
  unfold coprimeMellinMass
  apply continuous_finsetSum
  intro s hs
  apply Continuous.div_const
  apply Continuous.add
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact (continuous_const.mul (gramMellinPhase_continuous _).star).mul continuous_const
  · apply continuous_finsetSum
    intro h hh
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro a ha
    exact (continuous_const.mul (gramMellinPhase_continuous _)).mul continuous_const

lemma coprimeMellinMass_le_envelope (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a) (v w : Eisenstein → ℂ)
    (y : Eisenstein → ℝ) (t : ℝ) :
    coprimeMellinMass S H U v w y t ≤
      ∑ s ∈ U.powerset, (H.card:ℝ)*
        ((∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖v a‖)^2+
         (∑ a ∈ S.filter (fun a => (∏ p ∈ s, p) ∣ a), ‖w a‖)^2)/2 := by
  unfold coprimeMellinMass
  apply Finset.sum_le_sum
  intro s hs
  let F := S.filter (fun a => (∏ p ∈ s, p) ∣ a)
  have hF : ∀ a ∈ F, primary a := fun a ha => hS a (Finset.mem_filter.mp ha).1
  have hneg (h : Eisenstein) :
      ‖∑ a ∈ F, v a*star (gramMellinPhase t (y a))*star (cubicSymbol a h)‖ ≤
      ∑ a ∈ F, ‖v a‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a ha
    rw [norm_mul,norm_mul,norm_star,norm_gramMellinPhase,mul_one,norm_star]
    exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hF a ha) _)
  have hv := Finset.sum_le_sum (s := H) (fun h _ =>
    pow_le_pow_left₀ (_root_.norm_nonneg _) (hneg h) 2)
  have hw := Finset.sum_le_sum (s := H) (fun h _ =>
    pow_le_pow_left₀ (_root_.norm_nonneg _) (mellin_character_row_norm_le F hF w y h t) 2)
  simp only [Finset.sum_const,nsmul_eq_mul] at hv hw
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (add_le_add hv hw).trans_eq (by dsimp [F]; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormDenominatorSeparation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact separation of the square-root norm denominator in Poisson summation. -/
noncomputable section
open scoped BigOperators ContDiff FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology
namespace CubicFirstMoment

theorem normDenominator_radial_mellin_separated (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ}
    (hρ : 0 ≤ ρ) (hx : 0 < x) (hy : 0 < y) (hxy : |Real.log x-Real.log y| ≤ M) :
    (Real.exp ((Real.log x-Real.log y)/2):ℂ)*radialDualProfile W (ρ*x/y) = ∫ t : ℝ,
      normDenominatorMellinCoefficient M hM W hW hW' ρ t*gramMellinPhase t x*star (gramMellinPhase t y) := by
  have hk := normDenominatorLogSchwartz_eq_radial M hM W hW hW' hρ hxy
  rw [Real.exp_sub,Real.exp_log hx,Real.exp_log hy,← mul_div_assoc] at hk
  rw [← hk]
  have he := congrArg (fun f : 𝓢(ℝ,ℂ) => f (Real.log x-Real.log y))
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(ℝ,ℂ))
      (normDenominatorLogSchwartz M hM W hW hW' ρ))
  rw [SchwartzMap.fourierInv_coe,Real.fourierInv_eq] at he
  change normDenominatorLogSchwartz M hM W hW hW' ρ (Real.log x-Real.log y) = _
  rw [← he]
  apply integral_congr_ae
  filter_upwards with t
  have hi : inner ℝ t (Real.log x-Real.log y) = t*Real.log x-t*Real.log y := by
    simp only [RCLike.inner_apply,conj_trivial]
    ring
  have hp : (Real.fourierChar (inner ℝ t (Real.log x-Real.log y)):ℂ) =
      gramMellinPhase t x*star (gramMellinPhase t y) := by
    rw [hi,AddChar.map_sub_eq_div,div_eq_mul_inv,Circle.coe_mul,Circle.coe_inv_eq_conj]
    rfl
  change (Real.fourierChar (inner ℝ t (Real.log x-Real.log y)):ℂ)*
    normDenominatorMellinCoefficient M hM W hW hW' ρ t = _
  rw [hp]
  ring

lemma exp_half_log_ratio {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp ((Real.log x-Real.log y)/2) = Real.sqrt x/Real.sqrt y := by
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos hx,Real.rpow_def_of_pos hy,← Real.exp_sub]
  congr 1
  ring

theorem normDenominator_radial_div_sqrt (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W) {ρ x y : ℝ}
    (hρ : 0 ≤ ρ) (hx : 0 < x) (hy : 0 < y) (hxy : |Real.log x-Real.log y| ≤ M) :
    radialDualProfile W (ρ*x/y)/(Real.sqrt y:ℂ) = ∫ t : ℝ,
      (Real.sqrt x:ℂ)⁻¹*normDenominatorMellinCoefficient M hM W hW hW' ρ t*
        gramMellinPhase t x*star (gramMellinPhase t y) := by
  have he := normDenominator_radial_mellin_separated M hM W hW hW' hρ hx hy hxy
  rw [exp_half_log_ratio hx hy,Complex.ofReal_div] at he
  calc
    _ = (Real.sqrt x:ℂ)⁻¹ * ((Real.sqrt x:ℂ)/(Real.sqrt y:ℂ)*radialDualProfile W (ρ*x/y)) := by
      have hs : (Real.sqrt x:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
      field_simp
    _ = _ := by
      rw [he,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_NormCoprimeMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite Mellin separation of the Poisson form including its
square-root norm denominator. The character rows retain their original weights. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma normDenominatorMellinCoefficient_integrable_phases (M : ℝ) (hM : 0 < M) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) (ρ x y : ℝ) :
    Integrable (fun t => normDenominatorMellinCoefficient M hM W hW hW' ρ t * gramMellinPhase t x *
      star (gramMellinPhase t y)) := by
  apply Integrable.mul_bdd (c := 1)
  · exact (normDenominatorMellinCoefficient_integrable M hM W hW hW' ρ).mul_bdd
      (gramMellinPhase_continuous x).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => (norm_gramMellinPhase t x).le))
  · exact (gramMellinPhase_continuous y).star.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by simp)


theorem normCoprimeRadialForm_mellin (M : ℝ) (hM : 0 < M) (S H : Finset Eisenstein)
    (v w phase : Eisenstein → ℂ) (x y : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, 0 < x h)
    (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    normCoprimeRadialForm S H v w phase x y W ρ = ∫ t : ℝ,
      normDenominatorMellinCoefficient M hM W hW hW' ρ t * coprimeMellinKernel S H v w (fun h => phase h*(Real.sqrt (x h):ℂ)⁻¹) x y t := by
  let F (h a b : Eisenstein) (t : ℝ) : ℂ :=
    (phase h*(Real.sqrt (x h):ℂ)⁻¹ * (if IsCoprime a b then
      (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) else 0)) *
      (normDenominatorMellinCoefficient M hM W hW hW' ρ t * gramMellinPhase t (x h) *
        star (gramMellinPhase t (y a*y b)))
  have hF (h a b : Eisenstein) : Integrable (F h a b) :=
    (normDenominatorMellinCoefficient_integrable_phases M hM W hW hW' ρ (x h) (y a*y b)).const_mul _
  have he (h : Eisenstein) (hh : h ∈ H) (a : Eisenstein) (ha : a ∈ S)
      (b : Eisenstein) (hb : b ∈ S) :
      phase h * (if IsCoprime a b then
        (v a * star (cubicSymbol a h)) * star (w b * star (cubicSymbol b h)) *
          (radialDualProfile W (ρ*x h/(y a*y b))/(Real.sqrt (y a*y b):ℂ)) else 0) = ∫ t, F h a b t := by
    have hi := normDenominator_radial_div_sqrt M hM W hW hW' hρ (hx h hh)
      (mul_pos (hy a ha) (hy b hb)) (hlog h hh a ha b hb)
    have heq : (∫ t : ℝ, (Real.sqrt (x h):ℂ)⁻¹*
        normDenominatorMellinCoefficient M hM W hW hW' ρ t*
          gramMellinPhase t (x h)*star (gramMellinPhase t (y a*y b))) =
        (Real.sqrt (x h):ℂ)⁻¹*(∫ t : ℝ,
          normDenominatorMellinCoefficient M hM W hW hW' ρ t*
            gramMellinPhase t (x h)*star (gramMellinPhase t (y a*y b))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    rw [heq] at hi
    rw [hi]
    rw [show (∫ t, F h a b t) = _ from integral_const_mul _ _]
    split_ifs <;> ring
  calc
    _ = ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, ∫ t, F h a b t := by
      unfold normCoprimeRadialForm
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_congr rfl (fun b hb => he h hh a ha b hb)
    _ = ∫ t, ∑ h ∈ H, ∑ a ∈ S, ∑ b ∈ S, F h a b t := by
      rw [integral_finsetSum H (fun h _ =>
        integrable_finsetSum S (fun a _ => integrable_finsetSum S (fun b _ => hF h a b)))]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_finsetSum S (fun a _ => integrable_finsetSum S (fun b _ => hF h a b))]
      exact Finset.sum_congr rfl (fun a _ => (integral_finsetSum S (fun b _ => hF h a b)).symm)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      unfold coprimeMellinKernel
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      dsimp only [F]
      rw [gramMellinPhase_mul t (hy a ha)
        (hy b hb), star_mul]
      split_ifs <;> simp only [star_mul, mul_zero] <;> ring



lemma norm_denominator_phase_bound (H : Finset Eisenstein) (phase : Eisenstein → ℂ)
    (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1) (x : Eisenstein → ℝ)
    (hx : ∀ h ∈ H, 1 ≤ x h) :
    ∀ h ∈ H, ‖phase h*(Real.sqrt (x h):ℂ)⁻¹‖ ≤ 1 := by
  intro h hh
  have hs : 0 < Real.sqrt (x h) := Real.sqrt_pos.mpr (zero_lt_one.trans_le (hx h hh))
  have hs₁ : 1 ≤ Real.sqrt (x h) := (Real.le_sqrt (by norm_num) (by linarith [hx h hh])).mpr
    (by simpa using hx h hh)
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs,← div_eq_mul_inv]
  exact (div_le_one hs).mpr ((hphase h hh).trans hs₁)

theorem normCoprimeRadialForm_norm_le_mass (M : ℝ) (hM : 0 < M) (S H U : Finset Eisenstein)
    (hS : ∀ a ∈ S, primary a ∧ Squarefree a)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hSU : ∀ a ∈ S, primaryPrimeFactors a ⊆ U)
    (v w phase : Eisenstein → ℂ) (hphase : ∀ h ∈ H, ‖phase h‖ ≤ 1)
    (x y : Eisenstein → ℝ) (hx : ∀ h ∈ H, 1 ≤ x h) (hy : ∀ a ∈ S, 0 < y a)
    (hlog : ∀ h ∈ H, ∀ a ∈ S, ∀ b ∈ S, |Real.log (x h)-Real.log (y a*y b)| ≤ M)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ‖normCoprimeRadialForm S H v w phase x y W ρ‖ ≤
      ∫ t : ℝ, ‖normDenominatorMellinCoefficient M hM W hW hW' ρ t‖*
        coprimeMellinMass S H U v w y t := by
  let phase' : Eisenstein → ℂ := fun h => phase h*(Real.sqrt (x h):ℂ)⁻¹
  have hphase' : ∀ h ∈ H, ‖phase' h‖ ≤ 1 := norm_denominator_phase_bound H phase hphase x hx
  have hc := normDenominatorMellinCoefficient_integrable M hM W hW hW' ρ
  have hi := hc.mul_bdd
    (coprimeMellinKernel_continuous S H v w phase' x y).aestronglyMeasurable
    (Eventually.of_forall (norm_coprimeMellinKernel_le S H U hS hU hSU v w phase' hphase' x y))
  have hm := hc.norm.mul_bdd
    (coprimeMellinMass_continuous S H U v w y).aestronglyMeasurable
    (Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (coprimeMellinMass_nonneg S H U v w y t)]
      exact coprimeMellinMass_le_envelope S H U (fun a ha => (hS a ha).1) v w y t))
  rw [normCoprimeRadialForm_mellin M hM S H v w phase x y
    (fun h hh => zero_lt_one.trans_le (hx h hh)) hy hlog W hW hW' hρ]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono hi.norm hm
  intro t
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_coprimeMellinKernel_le_mass S H U hS hU hSU v w phase' hphase' x y t)
    (_root_.norm_nonneg _)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorCharacterMass
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact divisor mass behind the genuine coprimality kernel, with
arbitrary squarefree coefficients and both Fourier signs. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisorCharacterMass_continuous (S H U : Finset Eisenstein) (β : Eisenstein → ℂ) :
    Continuous (divisorCharacterMass S H U β) := by
  unfold divisorCharacterMass
  exact continuous_finsetSum _ (fun _ _ => finiteCharacterMass_continuous _ _ _)

lemma divisorCharacterMass_bound (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ a ∈ S, primary a) (u : ℝ) :
    ‖divisorCharacterMass S H U β u‖ ≤
      ∑ d ∈ U.powerset, (H.card:ℝ)*(S.filter (fun a => (∏ p ∈ d, p) ∣ a)).card*
        ∑ a ∈ S.filter (fun a => (∏ p ∈ d, p) ∣ a), ‖β a‖^2 := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  exact finiteCharacterMass_bound _ _ _ (fun a ha => hS a (Finset.mem_filter.mp ha).1) u

lemma twistedCoprimeMellinMass_eq_divisor_mass (S H U : Finset Eisenstein)
    (β : Eisenstein → ℂ) (hS : ∀ a ∈ S, primary a) (u s : ℝ)
    {N : ℝ} (hN : 0 < N) :
    twistedCoprimeMellinMass S H U β (fun a => norm a/N) u s =
      (divisorCharacterMass S H U β (u+2*Real.pi*s)+
        divisorCharacterMass S H U β (u-2*Real.pi*s))/2 := by
  unfold twistedCoprimeMellinMass coprimeMellinMass divisorCharacterMass finiteCharacterMass
  rw [← Finset.sum_add_distrib,← Finset.sum_div]
  apply congrArg (fun x : ℝ => x/2)
  apply Finset.sum_congr rfl
  intro d hd
  apply congrArg₂ (fun x y : ℝ => x+y)
  · apply Finset.sum_congr rfl
    intro h hh
    rw [finite_character_gram_row_norm _ β (fun a ha => hS a (Finset.mem_filter.mp ha).1) h u s hN]
  · apply Finset.sum_congr rfl
    intro h hh
    rw [finite_character_gram_reverse_row_norm _ β (fun a ha => hS a (Finset.mem_filter.mp ha).1) h u s hN]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMellinRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedCoefficient
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Phase and active roughness of the literal angular stopped coefficient. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma angularStoppedRowCoefficient_phase (ℓ : ℤ) (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (n : Eisenstein) :
    angularStoppedRowCoefficient ℓ X w z u W selected n =
      angularStoppedRowCoefficient ℓ X w z 0 W selected n*mellinPhase u (norm n) := by
  unfold angularStoppedRowCoefficient
  rw [stoppedRowCoefficient_phase]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedMellinRows
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
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

lemma angularStoppedDivisorMass_eq (ℓ : ℤ) (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (e : Eisenstein)
    (H U : Finset Eisenstein) :
    angularStoppedDivisorMass ℓ X w z a b u W selected e H U =
      divisorCharacterMass (stoppedIntervalSupport ι X a b e) H U
        (angularStoppedRowCoefficient ℓ X w z 0 W selected) u := by
  unfold angularStoppedDivisorMass divisorCharacterMass finiteCharacterMass
  simp_rw [angularStoppedRowCoefficient_phase ℓ X w z u W selected]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro h _
  congr 2
  apply Finset.sum_congr rfl
  intro n _
  ring

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

lemma logarithmic_core_cutoff {L : ℝ} (hL : 0 < L) (k : ℕ) :
    ((5832*L^(4*(k+2)))/5832)^(-(1/4:ℝ)) = 1/L^(k+2) := by
  rw [show (5832*L^(4*(k+2)))/5832 = L^(4*(k+2)) by ring,
    ←Real.rpow_natCast,←Real.rpow_mul hL.le]
  have he : ((4*(k+2):ℕ):ℝ)*(-(1/4:ℝ)) = -((k+2:ℕ):ℝ) := by push_cast; ring
  rw [he,Real.rpow_neg hL.le,Real.rpow_natCast,one_div]

lemma low_height_small_core_log_scale {N L T H : ℝ}
    (hN : 0 < N) (hL : 1 ≤ L) (k d : ℕ)
    (hT : L^(4*(k+2)+d+k) ≤ T)
    (hlog : N^(-(1:ℝ))*L^(4*(k+2)+d+k) ≤ H) :
    N*(1+N/T)*(5832*L^(4*(k+2)))*L^d ≤
      5832*(H+1)*N^2/L^k := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hTp : 0 < T := (pow_pos hLp _).trans_le hT
  have ha : N*L^(4*(k+2)+d) ≤ H*N^2/L^k := by
    have hh := rpow_log_saving hN hLp k (4*(k+2)+d)
      (p := 2) (s := 1) (by simpa only [Nat.add_comm k] using hlog)
    norm_num at hh
    exact hh
  have hb : N^2/T*L^(4*(k+2)+d) ≤ N^2/L^k := by
    apply (le_div_iff₀ (pow_pos hLp k)).mpr
    calc
      _ = N^2*L^(4*(k+2)+d+k)/T := by rw [pow_add]; ring
      _ ≤ N^2 := (div_le_iff₀ hTp).mpr (mul_le_mul_of_nonneg_left hT (sq_nonneg N))
  have hab := add_le_add ha hb
  calc
    _ = 5832*(N*L^(4*(k+2)+d)+N^2/T*L^(4*(k+2)+d)) := by rw [pow_add]; ring
    _ ≤ 5832*(H*N^2/L^k+N^2/L^k) := mul_le_mul_of_nonneg_left hab (by norm_num)
    _ = _ := by ring

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
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeThirdMoment
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The third divisor moment on primary squarefree elements, from a
finite Euler product and the already specified ordinary prime theorem. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_eight_reciprocal_sum (S U : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hU : ∀ b ∈ S, primaryPrimeFactors b ⊆ U) :
    (∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card / norm b) ≤
      ∏ p ∈ U, (1+8/norm p) := by
  rw [Finset.prod_one_add]
  apply OAI.sum_le_sum_of_injOn primaryPrimeFactors
  · intro b hb c hc he
    calc
      b = ∏ p ∈ primaryPrimeFactors b, p :=
        (primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2).symm
      _ = ∏ p ∈ primaryPrimeFactors c, p := by rw [he]
      _ = c := primaryPrimeFactors_prod (hS c hc).1 (hS c hc).2
  · intro s hs
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_powerset.mpr (hU b hb)
  · intro b hb
    have hn : norm b = ∏ p ∈ primaryPrimeFactors b, norm p := by
      rw [←norm_finset_prod,primaryPrimeFactors_prod (hS b hb).1 (hS b hb).2]
    rw [Finset.prod_div_distrib,Finset.prod_const,hn]
  · intro s hs hnot
    exact Finset.prod_nonneg (fun p _ => div_nonneg (by norm_num) (norm_nonneg p))

lemma squarefree_eight_sum_le_euler (S : Finset Eisenstein) {X : ℝ}
    (hX : 0 ≤ X) (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) :
    (∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card) ≤
      X*Real.exp (8*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
  have hsub : ∀ b ∈ S, primaryPrimeFactors b ⊆ primeCutoff X := by
    intro b hb p hp
    have hprime := primaryPrimeFactor_spec (hS b hb).1 hp
    exact mem_primeCutoff.mpr ⟨hprime.1,
      (norm_le_of_dvd_nonzero (primary_ne_zero (hS b hb).1) hprime.2).trans (hS b hb).2.2⟩
  have hprod : (∏ p ∈ primeCutoff X, (1+8/norm p)) ≤
      Real.exp (8*∑ p ∈ primeCutoff X, (norm p)⁻¹) := by
    rw [Finset.mul_sum,Real.exp_sum]
    apply Finset.prod_le_prod
    · intro p hp
      exact add_nonneg zero_le_one (div_nonneg (by norm_num) (norm_nonneg p))
    · intro p hp
      simpa only [div_eq_mul_inv,add_comm] using Real.add_one_le_exp (8*(norm p)⁻¹)
  calc
    _ ≤ ∑ b ∈ S, X*((8:ℝ)^(primaryPrimeFactors b).card/norm b) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb0 := norm_pos_of_ne_zero (primary_ne_zero (hS b hb).1)
      calc
        _ = norm b*((8:ℝ)^(primaryPrimeFactors b).card/norm b) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (hS b hb).2.2 (by positivity)
    _ = X*∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card/norm b := by rw [Finset.mul_sum]
    _ ≤ X*(∏ p ∈ primeCutoff X, (1+8/norm p)) :=
      mul_le_mul_of_nonneg_left (squarefree_eight_reciprocal_sum S (primeCutoff X)
        (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) hsub) hX
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hX

theorem squarefree_divisor_third_moment (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (X : ℝ) (S : Finset Eisenstein),
      Real.exp 1 ≤ X →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ X) →
      (∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card) ≤ K*X*(1+Real.log X)^d := by
  obtain ⟨C,hC,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  obtain ⟨d,hd⟩ := exists_nat_ge (8*C)
  refine ⟨Real.exp (8*C),d,Real.exp_pos _,?_⟩
  intro X S hX hS
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hl : 1 ≤ Real.log X := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hX
  have hl0 : 0 < Real.log X := zero_lt_one.trans_le hl
  have hrec := hprime (Real.log X) hl
  rw [Real.exp_log hX0] at hrec
  have he : Real.exp (8*(C*(1+Real.log (Real.log X)))) =
      Real.exp (8*C)*(Real.log X)^(8*C) := by
    rw [Real.rpow_def_of_pos hl0,←Real.exp_add]
    congr 1
    ring
  have hpow : (Real.log X)^(8*C) ≤ (1+Real.log X)^d := by
    calc
      _ ≤ (Real.log X)^(d:ℝ) := Real.rpow_le_rpow_of_exponent_le hl hd
      _ = (Real.log X)^d := Real.rpow_natCast _ _
      _ ≤ _ := pow_le_pow_left₀ hl0.le (by linarith : Real.log X ≤ 1+Real.log X) d
  calc
    _ ≤ X*Real.exp (8*∑ p ∈ primeCutoff X, (norm p)⁻¹) :=
      squarefree_eight_sum_le_euler S hX0.le hS
    _ ≤ X*Real.exp (8*(C*(1+Real.log (Real.log X)))) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hrec (by norm_num))) hX0.le
    _ = X*(Real.exp (8*C)*(Real.log X)^(8*C)) := by rw [he]
    _ ≤ X*(Real.exp (8*C)*(1+Real.log X)^d) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)) hX0.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SquarefreeNormFiber
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.eisenstein_discreteTopology _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Squarefree norm fibers have a divisor weight attached to each actual
member. Summing this weight retains logarithmic rather than small-power loss. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma squarefree_primeFactors_norm_subset {b c : Eisenstein}
    (hb : primary b) (hsb : Squarefree b) (hc : primary c)
    (hn : normNat c = normNat b) :
    primaryPrimeFactors c ⊆ primaryPrimeFactors b ∪ (primaryPrimeFactors b).image conjugate := by
  intro p hp
  have hpc := primaryPrimeFactor_spec hc hp
  have he : c*conjugate c = b*conjugate b := by
    rw [←normNat_cast_eq_mul_conjugate,←normNat_cast_eq_mul_conjugate,hn]
  have hd : p ∣ b*conjugate b := he ▸ dvd_mul_of_dvd_left hpc.2 _
  rcases hpc.1.2.dvd_or_dvd hd with hd | hd
  · have hprod := primaryPrimeFactors_prod hb hsb
    rw [←hprod] at hd
    obtain ⟨q,hq,hpq⟩ := (hpc.1.2.dvd_finsetProd_iff (fun q : Eisenstein => q)).mp hd
    have hqprime := (primaryPrimeFactor_spec hb hq).1
    have heq := primary_associated_eq hpc.1.1 hqprime.1
      ((hpc.1.2.dvd_prime_iff_associated hqprime.2).mp hpq)
    exact Finset.mem_union_left _ (heq ▸ hq)
  · rw [←primaryPrimeFactors_prod hb hsb,map_prod] at hd
    obtain ⟨q,hq,hpq⟩ := (hpc.1.2.dvd_finsetProd_iff conjugate).mp hd
    have hqprime := primaryPrime_conjugate (primaryPrimeFactor_spec hb hq).1
    have heq := primary_associated_eq hpc.1.1 hqprime.1
      ((hpc.1.2.dvd_prime_iff_associated hqprime.2).mp hpq)
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q,hq,heq.symm⟩)

lemma squarefree_norm_fiber_card (S : Finset Eisenstein)
    (hS : ∀ c ∈ S, primary c ∧ Squarefree c) {b : Eisenstein}
    (hb : primary b) (hsb : Squarefree b) :
    (S.filter (fun c => normNat c = normNat b)).card ≤
      4^(primaryPrimeFactors b).card := by
  let U := primaryPrimeFactors b ∪ (primaryPrimeFactors b).image conjugate
  have hcard : (S.filter (fun c => normNat c = normNat b)).card ≤ U.powerset.card := by
    apply Finset.card_le_card_of_injOn primaryPrimeFactors
    · intro c hc
      apply Finset.mem_powerset.mpr
      exact squarefree_primeFactors_norm_subset hb hsb (hS c (Finset.mem_filter.mp hc).1).1
        (Finset.mem_filter.mp hc).2
    · intro c hc d hd he
      calc
        c = ∏ p ∈ primaryPrimeFactors c, p :=
          (primaryPrimeFactors_prod (hS c (Finset.mem_filter.mp hc).1).1
            (hS c (Finset.mem_filter.mp hc).1).2).symm
        _ = ∏ p ∈ primaryPrimeFactors d, p := by rw [he]
        _ = d := primaryPrimeFactors_prod (hS d (Finset.mem_filter.mp hd).1).1
          (hS d (Finset.mem_filter.mp hd).1).2
  have hU : U.card ≤ 2*(primaryPrimeFactors b).card := by
    exact (Finset.card_union_le _ _).trans
      ((Nat.add_le_add_left Finset.card_image_le _).trans_eq (by omega))
  calc
    _ ≤ 2^U.card := by simpa only [Finset.card_powerset] using hcard
    _ ≤ 2^(2*(primaryPrimeFactors b).card) := Nat.pow_le_pow_right (by decide) hU
    _ = _ := by rw [pow_mul]; norm_num

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_BoundedSquarefreeMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary height means with a logarithmic loss for bounded squarefree
coefficients. No maximum norm-fiber bound or small power of the length occurs. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma normPolynomial_dyadic_energy {C T : ℝ}
    (hMV : MontgomeryVaughanBound C) (hT : 0 < T)
    (S : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ)
    (hZ : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z) :
    dyadicHeightMean (fun t => ‖eisensteinNormPolynomial S v t‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ n ∈ Finset.Icc 1 Z, ‖normCollectedCoeff S v n‖^2) := by
  unfold dyadicHeightMean
  simp_rw [normPolynomial_collected S v Z hZ]
  have hp := hMV Z (normCollectedCoeff S v) T (2*T) (by linarith)
  have hn := hMV Z (normCollectedCoeff S v) (-2*T) (-T) (by linarith)
  apply (div_le_div_of_nonneg_right (add_le_add hp hn) hT.le).trans_eq
  field_simp
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedSquarefreeMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weighted norm-fiber mean. The divisor weight is retained explicitly
so coprimality rows can later be summed without a uniform-fiber loss. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace CubicFirstMoment

lemma normCollectedCoeff_squarefree_weighted_energy (S : Finset Eisenstein)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b) (v : Eisenstein → ℂ) (Z : ℕ)
    (hZ : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z) :
    (∑ n ∈ Finset.Icc 1 Z, ‖normCollectedCoeff S v n‖^2) ≤
      ∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖v b‖^2 := by
  have hf (n : ℕ) : ‖normCollectedCoeff S v n‖^2 ≤
      ∑ b ∈ S.filter (fun b => normNat b = n), (4:ℝ)^(primaryPrimeFactors b).card*‖v b‖^2 := by
    apply (norm_sum_sq_le_card_mul _ v).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hbs := (Finset.mem_filter.mp hb).1
    have he : S.filter (fun c => normNat c = n) = S.filter (fun c => normNat c = normNat b) := by
      rw [(Finset.mem_filter.mp hb).2]
    have hcard : ((S.filter (fun c => normNat c = n)).card:ℝ) ≤
        (4:ℝ)^(primaryPrimeFactors b).card := by
      rw [he]
      exact_mod_cast squarefree_norm_fiber_card S hS (hS b hbs).1 (hS b hbs).2
    exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  exact (Finset.sum_le_sum (fun n _ => hf n)).trans_eq
    (Finset.sum_fiberwise_of_maps_to hZ _)

lemma squarefree_weighted_dyadic_mean {C T : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hT : 0 < T) (S : Finset Eisenstein) (v : Eisenstein → ℂ) (Z : ℕ)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b)
    (hZ : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z) :
    dyadicHeightMean (fun t => ‖eisensteinNormPolynomial S v t‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖v b‖^2) := by
  exact (normPolynomial_dyadic_energy hMV hT S v Z hZ).trans
    (mul_le_mul_of_nonneg_left (normCollectedCoeff_squarefree_weighted_energy S hS v Z hZ)
      (by positivity))

lemma squarefree_weighted_character_height {C T : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hT : 0 < T)
    (S H : Finset Eisenstein) (β : Eisenstein → ℂ) (Z : ℕ)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) (u : ℝ) (ℓ : ℤ) :
    dyadicHeightMean (fun t => ∑ h ∈ H,
      ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2)*H.card := by
  have hindex : ∀ b ∈ S, normNat b ∈ Finset.Icc 1 Z := by
    intro b hb
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero (primary_ne_zero (hS b hb).1)),?_⟩
    have hn := (hS b hb).2.2
    rw [←normNat_cast b] at hn
    exact_mod_cast hn
  rw [dyadicHeightMean_sum H
    (fun h t => ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2)
    (fun h _ => (continuous_finite_character_height S β h ℓ u).norm.pow 2)]
  have hrow (h : Eisenstein) :
      dyadicHeightMean (fun t =>
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2) := by
    let v := fun b => β b*cubicSymbol b h*theta ℓ b*mellinPhase u (norm b)
    have hv : ∀ b ∈ S, ‖v b‖ ≤ ‖β b‖ := by
      intro b hb
      dsimp [v]
      rw [norm_mul,norm_mul,norm_mul,norm_theta (primary_ne_zero (hS b hb).1),mellinPhase_norm,mul_one,mul_one]
      exact mul_le_of_le_one_right (_root_.norm_nonneg _) (norm_cubicSymbol_le_one (hS b hb).1 h)
    have he : (fun t => ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) =
        (fun t => ‖eisensteinNormPolynomial S v t‖^2) := by
      funext t
      congr 2
      unfold eisensteinNormPolynomial
      apply Finset.sum_congr rfl
      intro b _
      rw [mellinPhase_add]
      dsimp [v]
      ring
    rw [he]
    apply (squarefree_weighted_dyadic_mean hMV hC hT S v Z
      (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) hindex).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro b hb
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (_root_.norm_nonneg _) (hv b hb) 2) (by positivity)
  apply (Finset.sum_le_sum (fun h _ => hrow h)).trans_eq
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedDivisorEnergy
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Summing actual coprimality rows adds one divisor factor to the norm-fiber
weight. The resulting third divisor moment is logarithmic. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma weighted_divisor_row_energy (S U : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hU : ∀ p ∈ U, primaryPrime p) (hS : ∀ b ∈ S, primary b) :
    (∑ s ∈ U.powerset, ∑ b ∈ S.filter (fun b => (∏ p ∈ s, p) ∣ b),
      (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2) ≤
        ∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2 := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have hc : ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card:ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors b).card := by
    exact_mod_cast prime_subset_divisor_count U hU (hS b hb)
  calc
    _ ≤ (2:ℝ)^(primaryPrimeFactors b).card*((4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [←mul_assoc,←mul_pow]; norm_num

lemma ordinary_divisor_row_energy (S U : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hU : ∀ p ∈ U, primaryPrime p) (hS : ∀ b ∈ S, primary b) :
    (∑ s ∈ U.powerset, ∑ b ∈ S.filter (fun b => (∏ p ∈ s, p) ∣ b), ‖β b‖^2) ≤
        ∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2 := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have hc : ((U.powerset.filter (fun s => (∏ p ∈ s, p) ∣ b)).card:ℝ) ≤
      (2:ℝ)^(primaryPrimeFactors b).card := by
    exact_mod_cast prime_subset_divisor_count U hU (hS b hb)
  exact mul_le_mul_of_nonneg_right
    (hc.trans (pow_le_pow_left₀ (by norm_num) (by norm_num) _)) (sq_nonneg _)

lemma bounded_third_divisor_energy (hpnt : PrimaryPrimePNT) :
    ∃ (K : ℝ) (d : ℕ), 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (N M : ℝ), Real.exp 1 ≤ N → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ N) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      (∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2) ≤
        K*M^2*N*(1+Real.log N)^d := by
  obtain ⟨K,d,hK,hbound⟩ := squarefree_divisor_third_moment hpnt
  refine ⟨K,d,hK,?_⟩
  intro S β N M hN _hM hS hβ
  calc
    _ ≤ ∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*M^2 := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (_root_.norm_nonneg _) (hβ b hb) 2) (by positivity)
    _ = (∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card)*M^2 := (Finset.sum_mul _ _ _).symm
    _ ≤ (K*N*(1+Real.log N)^d)*M^2 :=
      mul_le_mul_of_nonneg_right (hbound N S hN hS) (sq_nonneg M)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorWeightedMean
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Ordinary mean values summed over the literal coprimality divisors. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma divisor_weighted_character_height {C T : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (hT : 0 < T)
    (S H U : Finset Eisenstein) (β : Eisenstein → ℂ) (Z : ℕ)
    (hU : ∀ p ∈ U, primaryPrime p)
    (hS : ∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) (u : ℝ) :
    dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
      2*C*(1+(Z:ℝ)/T)*(∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2)*H.card := by
  let F := fun s : Finset Eisenstein => S.filter (fun b => (∏ p ∈ s, p) ∣ b)
  let E := fun s => ∑ b ∈ F s, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2
  have hrow (s : Finset Eisenstein) :
      dyadicHeightMean (fun t => finiteCharacterMass (F s) H β (t+u)) T ≤
        2*C*(1+(Z:ℝ)/T)*E s*H.card := by
    simpa only [finiteCharacterMass,theta_zero,mul_one] using
      squarefree_weighted_character_height hMV hC hT (F s) H β Z
        (fun b hb => hS b (Finset.mem_filter.mp hb).1) u 0
  unfold divisorCharacterMass
  rw [dyadicHeightMean_sum U.powerset
    (fun s t => finiteCharacterMass (F s) H β (t+u))
    (fun s _ => (finiteCharacterMass_continuous (F s) H β).comp
      (continuous_id.add continuous_const))]
  calc
    _ ≤ ∑ s ∈ U.powerset, 2*C*(1+(Z:ℝ)/T)*E s*H.card :=
      Finset.sum_le_sum (fun s _ => hrow s)
    _ = 2*C*(1+(Z:ℝ)/T)*(∑ s ∈ U.powerset, E s)*H.card := by
      rw [Finset.mul_sum,Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (weighted_divisor_row_energy S U β hU (fun b hb => (hS b hb).1)) (by positivity)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorLowCube
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cube frequencies in all coprimality rows, with logarithmic divisor cost. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem divisor_cube_low_log_saving (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T M u : ℝ), 65536 ≤ (Z:ℝ) → 0 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) → H ⊆ nonzeroCubeNormBall B →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨Ke,d,hKe,he⟩ := bounded_third_divisor_energy hpnt
  obtain ⟨D,hD,hlog⟩ := log_power_normalization_bound (4*(k+2)+d+k)
    (by norm_num : (0:ℝ) < 1)
  refine ⟨36*(C+1)*Ke*(5832*(D+1)),4*(k+2)+d+k,by positivity,?_⟩
  intro S H U β Z B T M u hZ hB hM hT hU hS hβ hH
  let N : ℝ := Z
  let L := 1+Real.log N
  have hN1 : 1 ≤ N := by dsimp [N]; linarith
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hTp : 0 < T := (pow_pos hLp _).trans_le hT
  have hexp : Real.exp 1 ≤ N := by
    have hh : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    dsimp [N]
    linarith
  have henergy := he S β N M hexp hM hS hβ
  have hcard : (H.card:ℝ) ≤ 18*B^(1/3:ℝ) :=
    (Nat.cast_le.mpr (Finset.card_le_card hH)).trans (nonzeroCubeNormBall_card hB)
  have hscale := low_height_small_core_log_scale hNp hL1 k d hT (hlog N hN1)
  have hv : 1 ≤ 5832*L^(4*(k+2)) := by
    have hh := one_le_pow₀ hL1 (n := 4*(k+2))
    linarith
  have hs : N*(1+N/T)*L^d ≤ 5832*(D+1)*N^2/L^k := by
    apply le_trans ?_ hscale
    have hh := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ N*(1+N/T)*L^d by positivity)
    first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  calc
    _ ≤ 2*C*(1+N/T)*(Ke*M^2*N*L^d)*(18*B^(1/3:ℝ)) :=
      (divisor_weighted_character_height hMV hC hTp S H U β Z hU hS u).trans
        (by gcongr)
    _ ≤ 2*(C+1)*(1+N/T)*(Ke*M^2*N*L^d)*(18*B^(1/3:ℝ)) := by gcongr; linarith
    _ = (36*(C+1)*Ke*M^2*B^(1/3:ℝ))*(N*(1+N/T)*L^d) := by ring
    _ ≤ (36*(C+1)*Ke*M^2*B^(1/3:ℝ))*(5832*(D+1)*N^2/L^k) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by dsimp [N,L]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_WeightedLowHeightBlocks
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-height noncube moment with an explicit core cutoff. The small
cores use a summed divisor moment; no length-to-a-small-power loss remains. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem smallB_noncube_weighted_blocks
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (K : ℝ), 0 < K ∧ ∀ (S H : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B V T u : ℝ) (ℓ : ℤ), 65536 ≤ (Z:ℝ) → 0 ≤ B → 0 < V → 0 < T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => ∑ h ∈ H,
        ‖∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)‖^2) T ≤
        K*B^(1/3:ℝ)*((∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2)*(1+(Z:ℝ)/T)*V+
          ((largeCoreDyadicIndices V B).card:ℝ)*
            ((Z:ℝ)*(V/5832)^(-(1/4:ℝ))+(Z:ℝ)^(1-1/20000:ℝ))*
              ∑ b ∈ S, ‖β b‖^2) := by
  obtain ⟨Kh,hKh,hcore⟩ := smallB_core_hybrid_sieve hHuxley
  refine ⟨648*C+2*Kh,by positivity,?_⟩
  intro S H β Z B V T u ℓ hZ hB hV hT hS hsize hH
  let N : ℝ := Z
  let E := ∑ b ∈ S, ‖β b‖^2
  let E₄ := ∑ b ∈ S, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2
  let I := largeCoreDyadicIndices V B
  let HS := H.filter (fun h => h ∈ lowNoncubeSupport V (B^(1/3:ℝ)))
  let P := fun h t => ∑ b ∈ S, β b*cubicSymbol b h*theta ℓ b*mellinPhase (t+u) (norm b)
  let F := fun (J : Finset Eisenstein) t => ∑ h ∈ J, ‖P h t‖^2
  let A := E₄*(1+N/T)*V
  let R := (I.card:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*E
  have hNp : 0 < N := by dsimp [N]; linarith
  have hE : 0 ≤ E := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hE₄ : 0 ≤ E₄ := Finset.sum_nonneg (fun _ _ => by positivity)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcont (J : Finset Eisenstein) : Continuous (F J) := by
    exact continuous_finsetSum J (fun h _ => (continuous_finite_character_height S β h ℓ u).norm.pow 2)
  have hsmall : dyadicHeightMean (F HS) T ≤ (648*C)*B^(1/3:ℝ)*A := by
    have hm := squarefree_weighted_character_height hMV hC hT S HS β Z hS u ℓ
    have hcard : (HS.card:ℝ) ≤ 324*V*B^(1/3:ℝ) :=
      (Nat.cast_le.mpr (Finset.card_le_card (fun h hh => (Finset.mem_filter.mp hh).2))).trans
        (lowNoncubeSupport_card hV.le (Real.rpow_nonneg hB _))
    have hp := mul_le_mul_of_nonneg_left hcard
      (show 0 ≤ 2*C*(1+(Z:ℝ)/T)*E₄ by positivity)
    apply hm.trans
    convert hp using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [A,N,E₄]; ring)
  have hrow (z : ℕ × ℕ) (hz : z ∈ I) :
      dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T ≤
        2*Kh*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*E := by
    have hd := (Finset.mem_filter.mp hz).2
    apply (dyadicHeightMean_le_const (hcont _) hT
      (C := Kh*B^(1/3:ℝ)*(N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))*E)
      (fun t _ => ?_)).trans_eq (by ring)
    let γ := fun b => β b*theta ℓ b*mellinPhase (t+u) (norm b)
    have hγ : (∑ b ∈ S, ‖γ b‖^2) = E := by
      apply Finset.sum_congr rfl
      intro b hb
      simp only [γ,norm_mul,norm_theta (primary_ne_zero (hS b hb).1),mellinPhase_norm,mul_one]
    have heq (h : Eisenstein) : (∑ b ∈ S, γ b*cubicSymbol b h) = P h t := by
      apply Finset.sum_congr rfl
      intro b _
      dsimp [γ,P]
      ring
    have hh := hcore S (coreDyadicBlock B z.1 z.2) γ N B V z.1 z.2 hZ hB hV hS hd.1.le
      ((mul_le_mul_of_nonneg_left hd.2 (by norm_num : (0:ℝ) ≤ 8)).trans hsize)
      (Finset.Subset.refl _)
    simp_rw [heq] at hh
    rw [hγ] at hh
    exact hh
  have hlarge : (∑ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T) ≤
      (2*Kh)*B^(1/3:ℝ)*R := by
    apply (Finset.sum_le_sum (fun z hz => hrow z hz)).trans_eq
    simp only [Finset.sum_const,nsmul_eq_mul]
    dsimp [R]
    ring
  have hsplit : dyadicHeightMean (F H) T ≤ dyadicHeightMean (F HS) T+
      ∑ z ∈ I, dyadicHeightMean (F (coreDyadicBlock B z.1 z.2)) T := by
    have hm := dyadicHeightMean_mono (hcont H)
      ((hcont HS).add (continuous_finsetSum I (fun z _ => hcont _))) hT
      (g := fun t => F HS t+∑ z ∈ I, F (coreDyadicBlock B z.1 z.2) t)
      (fun t _ => noncube_frequency_mass_split H hH (fun h => ‖P h t‖^2) (fun _ => sq_nonneg _))
    rw [dyadicHeightMean_add (hcont HS) (continuous_finsetSum I (fun z _ => hcont _)),
      dyadicHeightMean_sum I (fun z => F (coreDyadicBlock B z.1 z.2)) (fun z _ => hcont _)] at hm
    exact hm
  apply hsplit.trans ((add_le_add hsmall hlarge).trans ?_)
  change (648*C)*B^(1/3:ℝ)*A+(2*Kh)*B^(1/3:ℝ)*R ≤
    (648*C+2*Kh)*B^(1/3:ℝ)*(A+R)
  nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 648*C) (Real.rpow_nonneg hB (1/3:ℝ))) hR,
    mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2*Kh) (Real.rpow_nonneg hB (1/3:ℝ))) hA]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorLowHeightBlocks
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full coprimality expansion at low height, with its divisor cost
retained in the actual third weighted coefficient energy. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem divisor_noncube_low_height_blocks
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B V T u : ℝ), 65536 ≤ (Z:ℝ) → 0 ≤ B → 0 < V → 0 < T →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*B^(1/3:ℝ)*(∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2)*
          ((1+(Z:ℝ)/T)*V+((largeCoreDyadicIndices V B).card:ℝ)*
            ((Z:ℝ)*(V/5832)^(-(1/4:ℝ))+(Z:ℝ)^(1-1/20000:ℝ))) := by
  obtain ⟨K,hK,hbound⟩ := smallB_noncube_weighted_blocks hMV hC hHuxley
  refine ⟨K,hK,?_⟩
  intro S H U β Z B V T u hZ hB hV hT hU hS hsize hH
  let F := fun s : Finset Eisenstein => S.filter (fun b => (∏ p ∈ s, p) ∣ b)
  let E₄ := fun s => ∑ b ∈ F s, (4:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2
  let E₀ := fun s => ∑ b ∈ F s, ‖β b‖^2
  let E₈ := ∑ b ∈ S, (8:ℝ)^(primaryPrimeFactors b).card*‖β b‖^2
  let A := (1+(Z:ℝ)/T)*V
  let R := ((largeCoreDyadicIndices V B).card:ℝ)*
    ((Z:ℝ)*(V/5832)^(-(1/4:ℝ))+(Z:ℝ)^(1-1/20000:ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrow (s : Finset Eisenstein) :
      dyadicHeightMean (fun t => finiteCharacterMass (F s) H β (t+u)) T ≤
        K*B^(1/3:ℝ)*(A*E₄ s+R*E₀ s) := by
    have hh := hbound (F s) H β Z B V T u 0 hZ hB hV hT
      (fun b hb => hS b (Finset.mem_filter.mp hb).1) hsize hH
    simp only [theta_zero,mul_one] at hh
    convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (dsimp [finiteCharacterMass,A,R,E₄,E₀])
    ring
  have hfour : (∑ s ∈ U.powerset, E₄ s) ≤ E₈ :=
    weighted_divisor_row_energy S U β hU (fun b hb => (hS b hb).1)
  have hzero : (∑ s ∈ U.powerset, E₀ s) ≤ E₈ :=
    ordinary_divisor_row_energy S U β hU (fun b hb => (hS b hb).1)
  unfold divisorCharacterMass
  rw [dyadicHeightMean_sum U.powerset
    (fun s t => finiteCharacterMass (F s) H β (t+u))
    (fun s _ => (finiteCharacterMass_continuous (F s) H β).comp (continuous_id.add continuous_const))]
  calc
    _ ≤ ∑ s ∈ U.powerset, K*B^(1/3:ℝ)*(A*E₄ s+R*E₀ s) :=
      Finset.sum_le_sum (fun s _ => hrow s)
    _ = K*B^(1/3:ℝ)*(A*(∑ s ∈ U.powerset, E₄ s)+R*(∑ s ∈ U.powerset, E₀ s)) := by
      simp only [mul_add,Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ K*B^(1/3:ℝ)*(A*E₈+R*E₈) := by gcongr
    _ = _ := by dsimp [A,R,E₈]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowHeightBracketLog
attribute [-instance] _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit low-height bracket, independently of any coefficients. -/
noncomputable section
namespace CubicFirstMoment

theorem low_height_bracket_log_saving (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ N B T : ℝ,
      65536 ≤ N → 1 ≤ B → B ≤ N^2 → (1+Real.log N)^Ct ≤ T →
      N*((1+N/T)*(5832*(1+Real.log N)^(4*(k+2)))+
        ((largeCoreDyadicIndices (5832*(1+Real.log N)^(4*(k+2))) B).card:ℝ)*
          (N*((5832*(1+Real.log N)^(4*(k+2)))/5832)^(-(1/4:ℝ))+
            N^(1-1/20000:ℝ))) ≤ K*N^2/(1+Real.log N)^k := by
  obtain ⟨CI,hCI,hcount⟩ := core_dyadic_index_log_count
  obtain ⟨H₁,hH₁,hlog₁⟩ := log_power_normalization_bound (4*(k+2)+k)
    (by norm_num : (0:ℝ) < 1)
  obtain ⟨H₂,hH₂,hlog₂⟩ := log_power_normalization_bound (k+2)
    (by norm_num : (0:ℝ) < 1/20000)
  let Q := 5832*(H₁+1)+CI*(1+H₂)
  refine ⟨Q,4*(k+2)+k,by dsimp [Q]; positivity,?_⟩
  intro N B T hN hB hBN hT
  let L := 1+Real.log N
  let V := 5832*L^(4*(k+2))
  let I := (largeCoreDyadicIndices V B).card
  have hN1 : 1 ≤ N := by linarith
  have hNp : 0 < N := by linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hI : (I:ℝ) ≤ CI*L^2 := hcount V B N hB hN1 hBN
  have hs := low_height_small_core_log_scale hNp hL1 k 0
    (by simpa only [Nat.add_zero] using hT) (by simpa only [Nat.add_zero] using hlog₁ N hN1)
  have hsmall : N*((1+N/T)*V) ≤ 5832*(H₁+1)*N^2/L^k := by
    simpa only [pow_zero,mul_one,mul_assoc] using hs
  have hv : (V/5832)^(-(1/4:ℝ)) = 1/L^(k+2) := logarithmic_core_cutoff hLp k
  have hmid : N*(I:ℝ)*(N*(V/5832)^(-(1/4:ℝ))) ≤ CI*N^2/L^k := by
    rw [hv]
    calc
      _ ≤ N*(CI*L^2)*(N*(1/L^(k+2))) := by gcongr
      _ = _ := by rw [pow_add]; field_simp
  have hnlog : N^(2-1/20000:ℝ)*L^2 ≤ H₂*N^2/L^k := by
    simpa only [Real.rpow_two] using
      rpow_log_saving hNp hLp k 2 (p := 2) (s := 1/20000) (hlog₂ N hN1)
  have hn : N*N^(1-1/20000:ℝ) = N^(2-1/20000:ℝ) := by
    nth_rw 1 [←Real.rpow_one N]
    rw [←Real.rpow_add hNp]
    congr 1
    norm_num
  have hlarge : N*(I:ℝ)*N^(1-1/20000:ℝ) ≤ (CI*H₂)*N^2/L^k := by
    calc
      _ ≤ N*(CI*L^2)*N^(1-1/20000:ℝ) := by gcongr
      _ = CI*(N^(2-1/20000:ℝ)*L^2) := by rw [←hn]; ring
      _ ≤ CI*(H₂*N^2/L^k) := mul_le_mul_of_nonneg_left hnlog hCI.le
      _ = _ := by ring
  have hh := add_le_add hsmall (add_le_add hmid hlarge)
  dsimp [Q]
  first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorLowLogSaving
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual noncube coprimality mass at polylogarithmic height. No
small norm power is lost when the divisor rows are summed. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

theorem divisor_noncube_low_log_saving (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T M u : ℝ), 65536 ≤ (Z:ℝ) → 1 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) → 8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B ∧ ¬∃ a : Eisenstein, a^3 = h) →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨K,hK,hbound⟩ := divisor_noncube_low_height_blocks hMV hC hHuxley
  obtain ⟨Ke,d,hKe,he⟩ := bounded_third_divisor_energy hpnt
  obtain ⟨Kb,Ct,hKb,hbracket⟩ := low_height_bracket_log_saving (k+d)
  refine ⟨K*Ke*Kb,Ct,by positivity,?_⟩
  intro S H U β Z B T M u hZ hB hM hT hU hS hβ hsize hH
  let N : ℝ := Z
  let L := 1+Real.log N
  let V := 5832*L^(4*(k+d+2))
  let A := (1+N/T)*V+((largeCoreDyadicIndices V B).card:ℝ)*
    (N*(V/5832)^(-(1/4:ℝ))+N^(1-1/20000:ℝ))
  have hN1 : 1 ≤ N := by dsimp [N]; linarith
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hN1]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hTp : 0 < T := (pow_pos hLp _).trans_le hT
  have hV : 0 < V := by dsimp [V]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hBN : B ≤ N^2 := by
    calc
      B ≤ 8*B := by linarith
      _ ≤ N^(3/4:ℝ) := hsize
      _ ≤ N^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = _ := Real.rpow_two N
  have hs := hbracket N B T hZ hB hBN hT
  have hexp : Real.exp 1 ≤ N := by
    have hh : Real.exp (1:ℝ) < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    dsimp [N]
    linarith
  have henergy := he S β N M hexp hM hS hβ
  have hb := hbound S H U β Z B V T u hZ (zero_le_one.trans hB) hV hTp hU hS hsize hH
  calc
    _ ≤ K*B^(1/3:ℝ)*(Ke*M^2*N*L^d)*A := hb.trans (by gcongr)
    _ = (K*Ke*M^2*B^(1/3:ℝ)*L^d)*(N*A) := by ring
    _ ≤ (K*Ke*M^2*B^(1/3:ℝ)*L^d)*(Kb*N^2/L^(k+d)) := by
      apply mul_le_mul_of_nonneg_left hs
      positivity
    _ = _ := by
      rw [pow_add]
      field_simp
      ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DivisorLowAllFrequency
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All nonzero frequencies in the actual coprimality expansion at
polylogarithmic height, uniformly in the common height shift. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem divisor_all_frequency_low_log_saving (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T M u : ℝ), 65536 ≤ (Z:ℝ) → 1 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) → 8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨Kn,Cn,hKn,hn⟩ := divisor_noncube_low_log_saving hpnt hMV hC hHuxley k
  obtain ⟨Kc,Cc,hKc,hc⟩ := divisor_cube_low_log_saving hpnt hMV hC k
  refine ⟨Kn+Kc,max Cn Cc,by positivity,?_⟩
  intro S H U β Z B T M u hZ hB hM hT hU hS hβ hsize hH
  have hN1 : 1 ≤ (Z:ℝ) := by linarith
  have hL1 : 1 ≤ 1+Real.log (Z:ℝ) := by linarith [Real.log_nonneg hN1]
  have hTn := (pow_le_pow_right₀ hL1 (le_max_left Cn Cc)).trans hT
  have hTc := (pow_le_pow_right₀ hL1 (le_max_right Cn Cc)).trans hT
  let HC := H.filter (fun h => ∃ a : Eisenstein, a^3 = h)
  let HN := H.filter (fun h => ¬∃ a : Eisenstein, a^3 = h)
  let F := fun (J : Finset Eisenstein) t => divisorCharacterMass S J U β (t+u)
  have hCsub : HC ⊆ nonzeroCubeNormBall B := by
    intro h hh
    obtain ⟨hh,hcube⟩ := Finset.mem_filter.mp hh
    exact mem_nonzeroCubeNormBall (hH h hh).1 (hH h hh).2 hcube
  have hnon := hn S HN U β Z B T M u hZ hB hM hTn hU hS hβ hsize
    (fun h hh => ⟨(hH h (Finset.mem_filter.mp hh).1).1,
      (hH h (Finset.mem_filter.mp hh).1).2,(Finset.mem_filter.mp hh).2⟩)
  have hcube := hc S HC U β Z B T M u hZ (zero_le_one.trans hB) hM hTc hU hS hβ hCsub
  have hcont (J : Finset Eisenstein) : Continuous (F J) :=
    (divisorCharacterMass_continuous S J U β).comp (continuous_id.add continuous_const)
  have heq : F H = fun t => F HC t+F HN t := by
    funext t
    unfold F divisorCharacterMass
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    exact (Finset.sum_filter_add_sum_filter_not H
      (fun h => ∃ a : Eisenstein, a^3 = h) _).symm
  change dyadicHeightMean (F H) T ≤ _
  rw [heq,dyadicHeightMean_add (hcont HC) (hcont HN)]
  exact (add_le_add hcube hnon).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_DyadicMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A weighted Mellin tail from actual dyadic height means. -/
noncomputable section
open Set Filter MeasureTheory
namespace CubicFirstMoment

lemma mellinHeightDyad_union {T : ℝ} (hT : 0 < T) :
    (⋃ n : ℕ, mellinHeightDyad T n) = Ici T := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact (le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num))).trans hn.1
  · intro hx
    obtain ⟨n,hn,hnext⟩ := exists_nat_pow_near ((le_div_iff₀ hT).mpr (by simpa using hx))
      (by norm_num : (1:ℝ) < 2)
    exact mem_iUnion.mpr ⟨n,⟨(le_div_iff₀ hT).mp hn,(div_lt_iff₀ hT).mp hnext⟩⟩

lemma mellinHeightDyad_disjoint {T : ℝ} (hT : 0 < T) :
    Pairwise (fun i j => Disjoint (mellinHeightDyad T i) (mellinHeightDyad T j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : i+1 ≤ j)) hT.le
    exact (not_lt_of_ge (hp.trans hj.1)) hi.2
  · have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : j+1 ≤ i)) hT.le
    exact (not_lt_of_ge (hp.trans hi.1)) hj.2

theorem weighted_positive_mellin_tail {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ t, 0 ≤ g t) (hfg : Integrable (fun t => f t*g t))
    {T B C : ℝ} (hT : 0 < T) (_hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmean : ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g t) ≤ B*S)
    (hdecay : ∀ t : ℝ, T ≤ t → f t ≤ C/t^2) :
    (∫ t in Ici T, f t*g t) ≤ 2*B*C/T := by
  have hdyad (n : ℕ) : (∫ t in mellinHeightDyad T n, f t*g t) ≤
      (B*C/T)*((1/2:ℝ)^n) := by
    let S := (2:ℝ)^n*T
    have hS : 0 < S := mul_pos (pow_pos (by norm_num) _) hT
    have hTS : T ≤ S := le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num))
    have hS2 : S ≤ 2*S := by linarith
    have he : (2:ℝ)^(n+1)*T = 2*S := by dsimp [S]; rw [pow_succ]; ring
    change (∫ t in Ico S ((2:ℝ)^(n+1)*T), f t*g t) ≤ _
    rw [he,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le hS2]
    have hi := intervalIntegral.integral_mono_on (μ := volume) hS2
      ((hf.mul hg).intervalIntegrable _ _)
      ((continuous_const.mul hg).intervalIntegrable S (2*S))
      (show ∀ t ∈ Icc S (2*S), f t*g t ≤ (C/S^2)*g t from fun t ht => by
        apply mul_le_mul_of_nonneg_right _ (hg0 t)
        apply (hdecay t (hTS.trans ht.1)).trans
        exact div_le_div_of_nonneg_left hC (sq_pos_of_pos hS)
          (pow_le_pow_left₀ hS.le ht.1 2))
    calc
      _ ≤ ∫ t in S..2*S, (C/S^2)*g t := hi
      _ = (C/S^2)*(∫ t in S..2*S, g t) := intervalIntegral.integral_const_mul _ _
      _ ≤ (C/S^2)*(B*S) := mul_le_mul_of_nonneg_left (hmean S hTS) (by positivity)
      _ = (B*C/T)*((1/2:ℝ)^n) := by
        dsimp [S]
        rw [div_pow,one_pow]
        field_simp
  have hsum := hasSum_integral_iUnion (μ := volume)
    (s := mellinHeightDyad T) (f := fun t => f t*g t)
    (fun n : ℕ => (measurableSet_Ico : MeasurableSet (mellinHeightDyad T n))) (mellinHeightDyad_disjoint hT)
    hfg.integrableOn
  rw [mellinHeightDyad_union hT] at hsum
  calc
    _ = ∑' n : ℕ, ∫ t in mellinHeightDyad T n, f t*g t := hsum.tsum_eq.symm
    _ ≤ ∑' n : ℕ, (B*C/T)*((1/2:ℝ)^n) :=
      Summable.tsum_le_tsum hdyad hsum.summable (summable_geometric_two.mul_left _)
    _ = (B*C/T)*2 := (hasSum_geometric_two.mul_left _).tsum_eq
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_SignedMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both signs of the height variable in the low-core Mellin integral. -/
noncomputable section
open Set Filter MeasureTheory
namespace CubicFirstMoment

theorem signed_height_mean_positive {g : ℝ → ℝ} (_hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B) :
    ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g t) ≤ B*S := by
  intro S hTS
  have hS : 0 < S := hT.trans_le hTS
  have hn : 0 ≤ ∫ t in -2*S..-S, g t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => hg0 t)
  have hm := (div_le_iff₀ hS).mp (hmean S hTS)
  linarith

theorem signed_height_mean_negative {g : ℝ → ℝ} (_hg : Continuous g) (hg0 : ∀ t, 0 ≤ g t)
    {T B : ℝ} (hT : 0 < T)
    (hmean : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B) :
    ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g (-t)) ≤ B*S := by
  intro S hTS
  have hS : 0 < S := hT.trans_le hTS
  have hn : 0 ≤ ∫ t in S..2*S, g t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => hg0 t)
  have hm := (div_le_iff₀ hS).mp (hmean S hTS)
  rw [intervalIntegral.integral_comp_neg]
  have he : -(2*S) = -2*S := by ring
  rw [he]
  linarith

theorem weighted_signed_mellin_tail {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ t, 0 ≤ g t) (hfg : Integrable (fun t => f t*g t))
    {T B C : ℝ} (hT : 0 < T) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmean : ∀ S : ℝ, T ≤ S →
      ((∫ t in S..2*S, g t)+(∫ t in -2*S..-S, g t))/S ≤ B)
    (hdecay : ∀ t : ℝ, T ≤ |t| → f t ≤ C/t^2) :
    ((∫ t in Ici T, f t*g t)+(∫ t in Ici T, f (-t)*g (-t))) ≤ 4*B*C/T := by
  have hp := weighted_positive_mellin_tail hf hg hg0 hfg hT hB hC
    (signed_height_mean_positive hg hg0 hT hmean) (fun t ht =>
      hdecay t (by rw [abs_of_pos (hT.trans_le ht)]; exact ht))
  have hi : Integrable (fun t : ℝ => f (-t)*g (-t)) :=
    (MeasurePreserving.integrable_comp_emb (Measure.measurePreserving_neg volume)
      (Homeomorph.neg ℝ).measurableEmbedding).mpr hfg
  have hn := weighted_positive_mellin_tail (hf.comp continuous_neg) (hg.comp continuous_neg)
    (fun t => hg0 (-t)) hi hT hB hC (signed_height_mean_negative hg hg0 hT hmean)
    (fun t ht => by
      have hh := hdecay (-t) (by rw [abs_neg,abs_of_pos (hT.trans_le ht)]; exact ht)
      simpa only [Function.comp_apply,neg_sq] using hh)
  calc
    _ ≤ 2*B*C/T+2*B*C/T := add_le_add hp hn
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedDivisorMellinTail
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The entire arithmetic Mellin tail of bounded squarefree coefficients.
The mean bound is the proved divisor-weighted low-height theorem, uniformly
in the height shift. It needs no prime-cancellation hypothesis. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem bounded_divisor_arithmetic_mellin_tail
    (hpnt : PrimaryPrimePNT) {C : ℝ} (hMV : MontgomeryVaughanBound C)
    (hC : 0 ≤ C) (hHuxley : HuxleyAdditiveLargeSieve)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (k q : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
        (Z : ℕ) (B A u T ρ : ℝ),
      65536 ≤ (Z:ℝ) → 1 ≤ B → 0 ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ ρ →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ A) → 8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      let F := arithmeticMellinCoefficient M hM V hV hV' ρ
      let G := fun t => divisorCharacterMass S H U β (t+u)
      (1+ρ)^q*((∫ t in Ici T, ‖F t‖*G t)+(∫ t in Ici T, ‖F (-t)‖*G (-t))) ≤
        K*A^2*(Z:ℝ)^2*B^(1/3:ℝ)/((1+Real.log Z)^k*T) := by
  obtain ⟨K,Ct,hK,hmean⟩ := divisor_all_frequency_low_log_saving hpnt hMV hC hHuxley k
  obtain ⟨D,hD,hdecay⟩ := arithmeticMellinCoefficient_quadratic_decay M hM V hV hV' q
  refine ⟨4*K*D,Ct,by positivity,?_⟩
  intro S H U β Z B A u T ρ hZ hB hA hT hρ hU hS hβ hsize hH
  dsimp only
  let F := arithmeticMellinCoefficient M hM V hV hV' ρ
  let G := fun t => divisorCharacterMass S H U β (t+u)
  let E := ∑ d ∈ U.powerset, (H.card:ℝ)*(S.filter (fun a => (∏ p ∈ d,p) ∣ a)).card*
    ∑ a ∈ S.filter (fun a => (∏ p ∈ d,p) ∣ a), ‖β a‖^2
  have hG : Continuous G :=
    (divisorCharacterMass_continuous S H U β).comp (continuous_id.add continuous_const)
  have hG0 (t : ℝ) : 0 ≤ G t :=
    Finset.sum_nonneg (fun _ _ => finiteCharacterMass_nonneg _ _ _ _)
  have hGb (t : ℝ) : ‖G t‖ ≤ E :=
    divisorCharacterMass_bound S H U β (fun a ha => (hS a ha).1) (t+u)
  have hF : Continuous F := arithmeticMellinCoefficient_continuous M hM V hV hV' ρ
  have hfg : Integrable (fun t => ((1+ρ)^q*‖F t‖)*G t) :=
    ((arithmeticMellinCoefficient_integrable M hM V hV hV' ρ).norm.const_mul _).mul_bdd
      hG.aestronglyMeasurable (Eventually.of_forall hGb)
  have hZ1 : 1 ≤ (Z:ℝ) := by linarith
  have hL : 0 < 1+Real.log (Z:ℝ) := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos hL Ct).trans_le hT
  have hb : 0 ≤ K*A^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by positivity
  have ht := weighted_signed_mellin_tail (continuous_const.mul hF.norm) hG hG0 hfg
    hTp hb hD.le
    (fun T' hT' => hmean S H U β Z B T' A u hZ hB hA (hT.trans hT') hU hS hβ hsize hH)
    (fun t ht => by
      have ht0 : t ≠ 0 := by intro he; simp [he] at ht; linarith
      apply (le_div_iff₀ (sq_pos_of_ne_zero ht0)).mpr
      simpa only [Pi.mul_apply,F,Real.norm_eq_abs,sq_abs,mul_assoc,mul_left_comm,mul_comm]
        using hdecay ρ hρ t)
  simp only [Pi.mul_apply,mul_assoc,integral_const_mul] at ht
  dsimp only [F] at ht
  first | (convert ht using 1 <;> ring) | exact (le_of_eq (by ring)).trans (ht.trans (le_of_eq (by ring)))

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedMellinScale
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rounding the coefficient length in the ordinary mean introduces only
fixed factors. Its logarithmic cutoff remains a fixed power of log X. -/
noncomputable section
namespace CubicFirstMoment

lemma stopped_mellin_ceil_scale {X b κ : ℝ} (hX : Real.exp 1 ≤ X)
    (hκ : 0 < κ) (hb : X^κ ≤ b) (hbX : b ≤ X) :
    1 ≤ b ∧ b ≤ (⌈b⌉₊:ℝ) ∧ (⌈b⌉₊:ℝ) ≤ 2*b ∧
      κ*Real.log X ≤ 1+Real.log (⌈b⌉₊:ℝ) ∧
      1+Real.log (⌈b⌉₊:ℝ) ≤ 3*Real.log X := by
  have hX1 : 1 ≤ X := (Real.one_le_exp_iff.mpr (by norm_num)).trans hX
  have hXp : 0 < X := zero_lt_one.trans_le hX1
  have hb1 : 1 ≤ b := (Real.one_le_rpow hX1 hκ.le).trans hb
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hbceil : b ≤ (⌈b⌉₊:ℝ) := Nat.le_ceil b
  have hceil : (⌈b⌉₊:ℝ) ≤ 2*b := by linarith [Nat.ceil_lt_add_one hbp.le]
  have hceilX : (⌈b⌉₊:ℝ) ≤ 2*X := hceil.trans (by linarith)
  have hlog1 : 1 ≤ Real.log X := by simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlow := Real.log_le_log (Real.rpow_pos_of_pos hXp κ) (hb.trans hbceil)
  rw [Real.log_rpow hXp] at hlow
  have hhigh := Real.log_le_log (hbp.trans_le hbceil) hceilX
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hXp.ne'] at hhigh
  have htwo := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  refine ⟨hb1,hbceil,hceil,by linarith,by linarith⟩

lemma stopped_mellin_cutoff_scale {L A : ℝ} (hL : 1 ≤ L) (n : ℕ)
    (hA : 0 ≤ A) (hAL : A ≤ 3*L) (hLn : (3:ℝ)^n ≤ L) :
    A^n ≤ L^(n+1) := by
  calc
    _ ≤ (3*L)^n := pow_le_pow_left₀ hA hAL _
    _ = (3:ℝ)^n*L^n := mul_pow _ _ _
    _ ≤ L*L^n := mul_le_mul_of_nonneg_right hLn (pow_nonneg (zero_le_one.trans hL) _)
    _ = _ := by rw [pow_succ]; ring

lemma stopped_mellin_mass_scale {b N L A κ : ℝ} (_hb : 0 ≤ b) (hL : 0 < L)
    (hκ : 0 < κ) (hN : 0 ≤ N) (hNb : N ≤ 2*b) (hA : κ*L ≤ A) (k : ℕ) :
    N^2/A^k ≤ (4/κ^k)*b^2/L^k := by
  have hAp : 0 < A := (mul_pos hκ hL).trans_le hA
  have hden := pow_le_pow_left₀ (mul_nonneg hκ.le hL.le) hA k
  rw [mul_pow] at hden
  calc
    _ ≤ (2*b)^2/(κ^k*L^k) :=
      div_le_div₀ (sq_nonneg (2*b)) (pow_le_pow_left₀ hN hNb 2) (by positivity) hden
    _ = _ := by field_simp; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinMassIntegration
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble a local Mellin estimate and the two signed tails as a bound
for the full integral. -/
noncomputable section
open Set MeasureTheory Filter
namespace CubicFirstMoment

lemma integral_height_split {F : ℝ → ℝ} (hF : Integrable F) {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, F t) = (∫ t in Ioo (-T) T, F t)+
      (∫ t in Ici T, F t)+(∫ t in Ici T, F (-t)) := by
  have hc : (Ioo (-T) T)ᶜ = Ici T ∪ Iic (-T) := by
    ext t
    simp only [mem_compl_iff,mem_Ioo,not_and_or,not_lt,mem_union,mem_Ici,mem_Iic]
    tauto
  have hd : Disjoint (Ici T) (Iic (-T)) := by
    apply disjoint_left.mpr
    intro t ht hs
    have ht' : T ≤ t := ht
    have hs' : t ≤ -T := hs
    linarith
  rw [← integral_add_compl measurableSet_Ioo hF,hc,
    setIntegral_union hd measurableSet_Iic hF.integrableOn hF.integrableOn]
  have hn : (∫ t in Ici T, F (-t)) = ∫ t in Iic (-T), F t := by
    rw [integral_Ici_eq_integral_Ioi,integral_comp_neg_Ioi]
  rw [hn]
  ring

theorem integral_local_and_signed_tail {f g : ℝ → ℝ} (hfi : Integrable f)
    (hf0 : ∀ t, 0 ≤ f t) (hfg : Integrable (fun t => f t*g t))
    {T B E : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hlocal : ∀ t : ℝ, |t| < T → g t ≤ B)
    (htail : (∫ t in Ici T, f t*g t)+(∫ t in Ici T, f (-t)*g (-t)) ≤ E) :
    (∫ t : ℝ, f t*g t) ≤ B*(∫ t : ℝ, f t)+E := by
  have hi : (∫ t in Ioo (-T) T, f t*g t) ≤ B*(∫ t : ℝ, f t) := by
    calc
      _ ≤ ∫ t in Ioo (-T) T, B*f t := by
        apply setIntegral_mono_on hfg.integrableOn (hfi.const_mul B).integrableOn measurableSet_Ioo
        intro t ht
        calc
          _ ≤ f t*B := mul_le_mul_of_nonneg_left (hlocal t (abs_lt.mpr ht)) (hf0 t)
          _ = _ := mul_comm _ _
      _ = B*(∫ t in Ioo (-T) T, f t) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hfi (Eventually.of_forall hf0)) hB
  rw [integral_height_split hfg hT]
  linarith

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_LowCoreMellinIntegral
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Full low-core Mellin integral: Kummer cancellation near zero, the
ordinary signed height mean in the tails. Both estimates are applied to
the actual finite structured sums. -/
noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma log_height_translate {z t u : ℝ} (hz : 2 ≤ z) (A U : ℕ)
    (ht : |t| ≤ z^A) (hu : |u| ≤ z^U) : |t+u| ≤ z^(max A U+1) := by
  have hz1 : 1 ≤ z := by linarith
  have ha := pow_le_pow_right₀ hz1 (le_max_left A U)
  have hu' := pow_le_pow_right₀ hz1 (le_max_right A U)
  calc
    _ ≤ |t|+|u| := abs_add_le _ _
    _ ≤ z^A+z^U := add_le_add ht hu
    _ ≤ 2*z^(max A U) := by linarith
    _ ≤ z*z^(max A U) := mul_le_mul_of_nonneg_right hz (pow_nonneg (by linarith) _)
    _ = _ := by rw [pow_succ]; ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedMellinIntegral
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full arithmetic Mellin integral for the actual early-stopped
coefficient. Pointwise Kummer cancellation controls the central interval;
the proved divisor-weighted mean controls its two infinite tails. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_arithmetic_mellin_integral
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (m : ℝ) (hm : 0 < m) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
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
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
        angularStoppedDivisorMass ℓ X (X^ξ) (X^(2/5:ℝ)) l b (t+u) W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) e S U) ≤ K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  obtain ⟨Kt,Ct,hKt,htail⟩ := bounded_divisor_arithmetic_mellin_tail
    hpnt hMV hC hHuxley m hm Φ hΦ hΦ' k q
  obtain ⟨Kn,hKn,hnear⟩ := angular_stopped_early_divisor_noncube_mass (ι := ι)
    hpnt hEF ℓ hℓ hHuxley hξ hξz hκ
    (show (0:ℝ) ≤ ((max (Ct+1) H+1:ℕ):ℝ) by positivity) hF hJ k
  obtain ⟨A,hA,hcoeff⟩ := angular_stopped_interval_energy ℓ (ι := ι) hξ hξz
  obtain ⟨D,hD,hmoment⟩ := arithmeticMellinCoefficient_moment_decay m hm Φ hΦ hΦ' q 0
  refine ⟨Kn*D+Kt*A^2*(4/κ^k),by positivity,?_⟩
  filter_upwards [hnear,hcoeff,stopped_divisor_cutoff_geometry hκ,
    eventually_ge_atTop (Real.exp 1),Real.tendsto_log_atTop.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop ((3:ℝ)^Ct)]
    with X hnear hcoeff hgeometry hX hL2 hLC
  intro δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb W hW hWi hWd
    S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  obtain ⟨hb1,hbceil,hceil,hloglo,hloghi⟩ := stopped_mellin_ceil_scale hX hκ hb hbX
  have hbp : 0 < b := zero_lt_one.trans_le hb1
  have hLp : 0 < Real.log X := by linarith
  obtain ⟨_,hN,hsize⟩ := hgeometry b B hb hBb
  have hqb : b/b^(1/8:ℝ) ≤ b := div_le_self hbp.le (Real.one_le_rpow hb1 (by norm_num))
  have hbmin : 65536 ≤ b := hN.trans hqb
  let N := ⌈b⌉₊
  let T := (1+Real.log (N:ℝ))^Ct
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let P := stoppedIntervalSupport ι X l b e
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W selected
  let G := fun t => divisorCharacterMass P S U β (t+u)
  let f := fun t => (1+ρ)^q*‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖
  let B₀ := Kn*b^2*B^(1/3:ℝ)/(Real.log X)^k
  have hNmin : 65536 ≤ (N:ℝ) := hbmin.trans hbceil
  have hN1 : 1 ≤ (N:ℝ) := hb1.trans hbceil
  have hNp : 0 < (N:ℝ) := zero_lt_one.trans_le hN1
  have hT1 : 1 ≤ T := one_le_pow₀ (by linarith [Real.log_nonneg hN1])
  have hTp : 0 < T := zero_lt_one.trans_le hT1
  have hTlog : T ≤ (Real.log X)^(Ct+1) :=
    stopped_mellin_cutoff_scale (by linarith) Ct
      (by linarith [Real.log_nonneg hN1]) hloghi hLC
  have hP : ∀ n ∈ P, primary n ∧ Squarefree n ∧ norm n ≤ (N:ℝ) := by
    intro n hn
    have hs := stoppedIntervalSupport_spec X l b e hn
    exact ⟨hs.1,hs.2.1,hs.2.2.trans hbceil⟩
  have hβ : ∀ n ∈ P, ‖β n‖ ≤ A :=
    (hcoeff W hW selected 0 l b e hbp.le hbX).1
  have hsizeN : 8*B ≤ (N:ℝ)^(3/4:ℝ) := hsize.trans
    (Real.rpow_le_rpow (by positivity) (hqb.trans hbceil) (by norm_num))
  have hG : Continuous G :=
    (divisorCharacterMass_continuous P S U β).comp (continuous_id.add continuous_const)
  have hGbound := divisorCharacterMass_bound P S U β (fun n hn => (hP n hn).1)
  have hfi : Integrable f :=
    (arithmeticMellinCoefficient_integrable m hm Φ hΦ hΦ' ρ).norm.const_mul _
  have hfg : Integrable (fun t => f t*G t) := hfi.mul_bdd hG.aestronglyMeasurable
    (Eventually.of_forall (fun t => hGbound (t+u)))
  have hGmass (t : ℝ) : G t = angularStoppedDivisorMass ℓ X (X^ξ) (X^(2/5:ℝ)) l b
      (t+u) W selected e S U := (angularStoppedDivisorMass_eq ℓ _ _ _ _ _ _ _ _ _ _ _).symm
  have hlocal (t : ℝ) (ht : |t| < T) : G t ≤ B₀ := by
    rw [hGmass]
    have ht' := log_height_translate hL2 (Ct+1) H (ht.le.trans hTlog) hu
    exact hnear δ l b (t+u) V B hδ hδone hwidth hl hb hbX hV
      (by simpa only [Real.rpow_natCast] using ht') hVF hB hBb W hW hWi hWd
      S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL
  have ht := htail P S U β N B A u T ρ hNmin hB hA.le le_rfl hρ hU hP hβ hsizeN
    (fun v hv => ⟨(hS v hv).1,(hS v hv).2.1⟩)
  have hscale := stopped_mellin_mass_scale hbp.le hLp hκ hNp.le hceil hloglo k
  have htail' : (∫ t in Ici T, f t*G t)+(∫ t in Ici T, f (-t)*G (-t)) ≤
      (Kt*A^2*(4/κ^k))*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
    simp only [f,mul_assoc,integral_const_mul]
    rw [←mul_add]
    apply ht.trans
    calc
      _ = (Kt*A^2*B^(1/3:ℝ))*((N:ℝ)^2/(1+Real.log (N:ℝ))^k)/T := by ring
      _ ≤ (Kt*A^2*B^(1/3:ℝ))*((4/κ^k)*b^2/(Real.log X)^k)/T :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hscale (by positivity)) hTp.le
      _ ≤ (Kt*A^2*B^(1/3:ℝ))*((4/κ^k)*b^2/(Real.log X)^k) :=
        div_le_self (by positivity) hT1
      _ = _ := by ring
  have hi := integral_local_and_signed_tail hfi (fun t => by dsimp [f]; positivity)
    hfg hTp (show 0 ≤ B₀ by dsimp [B₀]; positivity) hlocal htail'
  have hf : (∫ t : ℝ, f t) ≤ D := by
    rw [show f = fun t => (1+ρ)^q*‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖ from rfl,
      integral_const_mul]
    simpa only [pow_zero,one_mul] using hmoment ρ hρ
  have hi' := hi.trans (add_le_add (mul_le_mul_of_nonneg_left hf
    (show 0 ≤ B₀ by dsimp [B₀]; positivity)) le_rfl)
  simp_rw [hGmass] at hi'
  simp only [f,mul_assoc,integral_const_mul] at hi'
  convert hi' using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [B₀]; ring)

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinConjugation
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reflection of the actual Mellin kernel is obtained by conjugating its
original radial weight. This handles the reverse character row without
adding an analytic hypothesis. -/
noncomputable section
open scoped ContDiff FourierTransform SchwartzMap
open MeasureTheory
namespace CubicFirstMoment

lemma star_fourierChar (x : ℝ) :
    star (Real.fourierChar x : ℂ) = (Real.fourierChar (-x) : ℂ) := by
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

lemma traceFourier_conj (f : ℂ → ℂ) (w : ℂ) :
    traceFourier (fun z => star (f z)) w = star (traceFourier f (-w)) := by
  unfold traceFourier
  calc
    _ = ∫ z : ℂ, star ((Real.fourierChar (-tracePair z (-w)) : ℂ)*f z) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [star_mul,star_fourierChar]
      simp only [tracePair,mul_neg,Complex.neg_re,neg_neg]
      ring
    _ = _ := integral_conj

lemma normProfileFourier_conj (V : ℝ → ℂ) (w : ℂ) :
    normProfileFourier (fun x => star (V x)) w = star (normProfileFourier V w) := by
  unfold normProfileFourier
  rw [traceFourier_conj]
  have he := normProfileFourier_eq_of_normSq_eq V
    (show Complex.normSq (-w) = Complex.normSq w by simp)
  change (2 / Real.sqrt 3 : ℝ) • star (traceFourier (fun z => V (Complex.normSq z)) (-w)) = _
  calc
    _ = star ((2 / Real.sqrt 3 : ℝ) •
        traceFourier (fun z => V (Complex.normSq z)) (-w)) := by
      simp only [star_smul,star_trivial]
    _ = _ := congrArg star he

lemma normDenominatorLogSchwartz_conj (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport (fun x => star (V x)))
    (hVc' : ContDiff ℝ ∞ (fun x => star (V x))) (ρ u : ℝ) :
    normDenominatorLogSchwartz M hM (fun x => star (V x)) hVc hVc' ρ u =
      star (normDenominatorLogSchwartz M hM V hV hV' ρ u) := by
  simp only [normDenominatorLogSchwartz_apply,wideGramLogKernel,
    normProfileFourier_conj,star_mul,star_smul,star_trivial]
  rw [show star (Real.exp (u/2) : ℂ) = (Real.exp (u/2) : ℂ) from RCLike.conj_ofReal _]
  ring

lemma real_fourier_conj (f : ℝ → ℂ) (t : ℝ) :
    𝓕 (fun x => star (f x)) t = star (𝓕 f (-t)) := by
  rw [Real.fourier_eq,Real.fourier_eq]
  calc
    _ = ∫ x : ℝ, star ((Real.fourierChar (-inner ℝ x (-t)) : ℂ)*f x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [Circle.smul_def,smul_eq_mul,star_mul,star_fourierChar,inner_neg_right,
        neg_neg]
      ring
    _ = _ := integral_conj

lemma arithmeticMellinCoefficient_conj (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hVc : HasCompactSupport (fun x => star (V x)))
    (hVc' : ContDiff ℝ ∞ (fun x => star (V x))) (ρ t : ℝ) :
    arithmeticMellinCoefficient M hM (fun x => star (V x)) hVc hVc' ρ t =
      star (arithmeticMellinCoefficient M hM V hV hV' ρ (-t)) := by
  unfold arithmeticMellinCoefficient normDenominatorMellinCoefficient
  rw [SchwartzMap.fourier_coe,SchwartzMap.fourier_coe]
  have he : (normDenominatorLogSchwartz M hM (fun x => star (V x)) hVc hVc' ρ : ℝ → ℂ) =
      fun x => star (normDenominatorLogSchwartz M hM V hV hV' ρ x) := by
    funext x
    exact normDenominatorLogSchwartz_conj M hM V hV hV' hVc hVc' ρ x
  rw [he,real_fourier_conj,neg_div]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedReflectedMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The reflected arithmetic kernel follows by conjugating the fixed smooth
weight. The stopped coefficients, selected interval, and all divisor rows
are unchanged. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_reflected_arithmetic_mellin_integral
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (m : ℝ) (hm : 0 < m) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
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
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ (-t)‖*
        angularStoppedDivisorMass ℓ X (X^ξ) (X^(2/5:ℝ)) l b (t+u) W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) e S U) ≤ K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  have hΦc : HasCompactSupport (fun x => star (Φ x)) :=
    hΦ.comp_left (show star (0:ℂ) = 0 from star_zero _)
  have hΦc' : ContDiff ℝ ∞ (fun x => star (Φ x)) :=
    Complex.conjCLE.contDiff.comp hΦ'
  have he := angular_stopped_arithmetic_mellin_integral (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley hξ hξz hκ hF hJ
    m hm (fun x => star (Φ x)) hΦc hΦc' k q H
  simpa only [arithmeticMellinCoefficient_conj m hm Φ hΦ hΦ' hΦc hΦc',norm_star] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_MellinSignedIntegration
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact changes of variable for the two signs of the Poisson rows.
The Jacobian 2π is retained. -/
noncomputable section
open scoped ContDiff
open MeasureTheory Filter
namespace CubicFirstMoment

lemma integral_scaled_mass (f g : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, f t*g (c*t)) = c⁻¹*(∫ t : ℝ, f (t/c)*g t) := by
  have he := Measure.integral_comp_mul_left (fun t : ℝ => f (t/c)*g t) c
  simp only [abs_inv,abs_of_pos hc,smul_eq_mul,mul_div_cancel_left₀ _ hc.ne'] at he
  exact he

lemma integral_scaled_signed_mass (f g : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    (hplus : Integrable (fun t : ℝ => f t*g (c*t)))
    (hminus : Integrable (fun t : ℝ => f t*g (-(c*t)))) :
    (∫ t : ℝ, f t*((g (c*t)+g (-(c*t)))/2)) =
      ((∫ t : ℝ, f (t/c)*g t)+(∫ t : ℝ, f (-(t/c))*g t))/(2*c) := by
  have hminus' : (∫ t : ℝ, f t*g (-(c*t))) =
      c⁻¹*(∫ t : ℝ, f (-(t/c))*g t) := by
    have hn := integral_neg_eq_self (fun t : ℝ => f t*g (-(c*t)))
    simp only [mul_neg,neg_neg] at hn
    rw [← hn]
    exact integral_scaled_mass (fun t => f (-t)) g hc
  have hs (t : ℝ) : f t*((g (c*t)+g (-(c*t)))/2) =
      (f t*g (c*t))/2+(f t*g (-(c*t)))/2 := by ring
  simp_rw [hs]
  rw [integral_add (hplus.div_const 2) (hminus.div_const 2),
    integral_div,integral_div,integral_scaled_mass f g hc,hminus']
  ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedSignedMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact signed arithmetic-height representation of the divisor mass.
All finite coefficient supports and coprimality rows are retained. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma divisor_normMellin_signed_integral
    (m : ℝ) (hm : 0 < m) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
    (hS : ∀ n ∈ S, primary n) (u ρ : ℝ) {N : ℝ} (hN : 0 < N) :
    (∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
      twistedCoprimeMellinMass S H U β (fun a => norm a/N) u t) =
    ((∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
        divisorCharacterMass S H U β (t+u))+
      (∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ (-t)‖*
        divisorCharacterMass S H U β (t+u)))/(4*Real.pi) := by
  let G := fun t => divisorCharacterMass S H U β (t+u)
  let f := fun t => ‖normDenominatorMellinCoefficient m hm Φ hΦ hΦ' ρ t‖
  have hG : Continuous G :=
    (divisorCharacterMass_continuous S H U β).comp (continuous_id.add continuous_const)
  have hf : Integrable f := (normDenominatorMellinCoefficient_integrable m hm Φ hΦ hΦ' ρ).norm
  have hp : Integrable (fun t => f t*G (2*Real.pi*t)) :=
    hf.mul_bdd (hG.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => divisorCharacterMass_bound S H U β hS _))
  have hn : Integrable (fun t => f t*G (-(2*Real.pi*t))) :=
    hf.mul_bdd (hG.comp (continuous_neg.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun t => divisorCharacterMass_bound S H U β hS _))
  have he := integral_scaled_signed_mass f G (by positivity : 0 < 2*Real.pi) hp hn
  have hpoint (t : ℝ) : twistedCoprimeMellinMass S H U β (fun a => norm a/N) u t =
      (G (2*Real.pi*t)+G (-(2*Real.pi*t)))/2 := by
    rw [twistedCoprimeMellinMass_eq_divisor_mass S H U β hS u t hN]
    dsimp [G]
    congr 2 <;> congr 1 <;> ring
  simp_rw [hpoint]
  simpa only [f,G,arithmeticMellinCoefficient,neg_div,
    show (2:ℝ)*(2*Real.pi) = 4*Real.pi by ring] using he

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedNormMellin
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual stopped coefficients satisfy the full two-sign coprimality
Mellin bound. Its normalization is the exact Jacobian 1/(4π). -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_norm_mellin_integral
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (m : ℝ) (hm : 0 < m) (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
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
      ∀ {N : ℝ}, 0 < N → ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
        coprimeMellinMass (stoppedIntervalSupport ι X l b e) S U
          (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W
            (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
              j₀ k₀ h Z Q early) n))
          (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W
            (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
              j₀ k₀ h Z Q early) n))
          (fun n => norm n/N) t) ≤ K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  obtain ⟨Kp,hKp,hplus⟩ := angular_stopped_arithmetic_mellin_integral (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley hξ hξz hκ hF hJ m hm Φ hΦ hΦ' k q H
  obtain ⟨Kn,hKn,hminus⟩ := angular_stopped_reflected_arithmetic_mellin_integral (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley hξ hξz hκ hF hJ m hm Φ hΦ hΦ' k q H
  refine ⟨(Kp+Kn)/(4*Real.pi),by positivity,?_⟩
  filter_upwards [hplus,hminus] with X hplus hminus
  intro δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb W hW hWi hWd
    S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL N hN ρ hρ
  have hp := hplus δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb
    W hW hWi hWd S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  have hn := hminus δ l b u V B hδ hδone hwidth hl hb hbX hV hu hVF hB hBb
    W hW hWi hWd S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  have hid := divisor_normMellin_signed_integral m hm Φ hΦ hΦ'
    (stoppedIntervalSupport ι X l b e) S U
    (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W selected)
    (fun n hn => (stoppedIntervalSupport_spec X l b e hn).1) u ρ hN
  simp only [twistedCoprimeMellinMass,←angularStoppedRowCoefficient_phase ℓ,
    ←angularStoppedDivisorMass_eq ℓ] at hid
  change (1+ρ)^q*(∫ t : ℝ, ‖normDenominatorMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
    coprimeMellinMass (stoppedIntervalSupport ι X l b e) S U
      (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n))
      (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n))
      (fun n => norm n/N) t) ≤ _
  rw [hid]
  calc
    _ = ((1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ t‖*
          angularStoppedDivisorMass ℓ X (X^ξ) (X^(2/5:ℝ)) l b (t+u) W selected e S U)+
        (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient m hm Φ hΦ hΦ' ρ (-t)‖*
          angularStoppedDivisorMass ℓ X (X^ξ) (X^(2/5:ℝ)) l b (t+u) W selected e S U))/(4*Real.pi) := by ring
    _ ≤ (Kp*b^2*B^(1/3:ℝ)/(Real.log X)^k+
          Kn*b^2*B^(1/3:ℝ)/(Real.log X)^k)/(4*Real.pi) :=
      div_le_div_of_nonneg_right (add_le_add hp hn) (by positivity)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Estimates_FullPrimeNormRange
attribute [-instance] _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed log-norm range for an unchanged prime convolution is derived
from its coordinate supports. -/
noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma compact_norm_log_ratio {D x y z : ℝ} (_hD : 1 ≤ D)
    (hx : x ∈ Icc (1:ℝ) 2) (hy : y ∈ Icc (1:ℝ) D) (hz : z ∈ Icc (1:ℝ) D) :
    |Real.log x-Real.log (y*z)| ≤ 1+2*Real.log D := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx.1
  have hy0 : 0 < y := zero_lt_one.trans_le hy.1
  have hz0 : 0 < z := zero_lt_one.trans_le hz.1
  have hxlog : Real.log x ≤ 1 :=
    (Real.log_le_sub_one_of_pos hx0).trans (by linarith [hx.2])
  have hylog : Real.log y ≤ Real.log D := Real.log_le_log hy0 hy.2
  have hzlog : Real.log z ≤ Real.log D := Real.log_le_log hz0 hz.2
  rw [Real.log_mul hy0.ne' hz0.ne',abs_le]
  constructor <;> linarith [Real.log_nonneg hx.1,Real.log_nonneg hy.1,
    Real.log_nonneg hz.1]

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Decomposition_StoppedRadialForm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A noncube Poisson annulus for literal early-stopped coefficients.
The coefficient interval is an actual dyad; its normalized log range and
ambient prime support are constructed here. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma stoppedIntervalSupport_scaled_norm {X b : ℝ} (hb : 0 < b) (e : Eisenstein)
    {n : Eisenstein} (hn : n ∈ stoppedIntervalSupport ι X (b/2) b e) :
    norm n/(b/2) ∈ Icc (1:ℝ) 2 := by
  have hn' := (Finset.mem_filter.mp hn).2
  have hp : 0 < b/2 := by positivity
  exact ⟨(le_div_iff₀ hp).mpr (by simpa using hn'.2.2.1.le),
    (div_le_iff₀ hp).mpr (by linarith [hn'.2.2.2])⟩

end CubicFirstMoment

end

end OAI
end

section
-- module Solutions.OAIQ096_CM.CubicMoment_Angular_AngularStoppedRadialForm
attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeIwahori_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootHeckeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootAutomorphicL2_complete _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCoverGroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointMeasure_invariant _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_finiteOnCompacts _root_.OAI.CubicFirstMoment.cubicThetaQuotientMeasure_locallyFinite _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_chartedSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_isManifold _root_.OAI.CubicFirstMoment.cubicThetaQuotient_locallyCompact _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_secondCountable _root_.OAI.CubicFirstMoment.cubicThetaQuotient_t2 _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_action _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaScaledPeriodGroup_measure _root_.OAI.CubicFirstMoment.instCommGroupCubicThetaScaledPeriodGroup _root_.OAI.CubicFirstMoment.instContinuousConstSMulSubtypeSpecialLinearGroupFinOfNatNatComplexMemSubalgebraIntEisensteinSubgroupCubicThetaPrincipalGroupGroupCubicThetaPoint _root_.OAI.CubicFirstMoment.instCountableCubicThetaScaledPeriodGroup _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.OAI.CubicFirstMoment.instFiniteUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.OAI.CubicFirstMoment.instFintypeUnitsSubtypeComplexMemSubalgebraIntEisenstein_p1 _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A noncube Poisson annulus for literal early-stopped coefficients.
The coefficient interval is an actual dyad; its normalized log range and
ambient prime support are constructed here. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_noncube_radial_form_oai
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ)
    (hΦ' : ContDiff ℝ ∞ Φ) (k q H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V B Y : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      1 ≤ B → B ≤ b^(3/5:ℝ) →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) →
      0 < Y → ∀ (S : Finset Eisenstein) (phase : Eisenstein → ℂ),
      (∀ v ∈ S, v ≠ 0 ∧ norm v ≤ B ∧ ¬∃ n : Eisenstein, n^3 = v) →
      (∀ v ∈ S, Y ≤ norm v ∧ norm v ≤ 2*Y) → (∀ v ∈ S, ‖phase v‖ ≤ 1) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^q*‖normCoprimeRadialForm (stoppedIntervalSupport ι X (b/2) b e) S
        (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) n))
        (fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early) n))
        phase (fun v => norm v/Y) (fun n => norm n/(b/2)) Φ ρ‖ ≤
      K*b^2*B^(1/3:ℝ)/(Real.log X)^k := by
  let m := 1+2*Real.log 2
  have hm : 0 < m := by dsimp [m]; positivity
  obtain ⟨K,hK,hmass⟩ := angular_stopped_norm_mellin_integral (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley hξ hξz hκ hF hJ m hm Φ hΦ hΦ' k q H
  refine ⟨K,hK,?_⟩
  filter_upwards [hmass] with X hmass
  intro δ b u V B Y hδ hδone hwidth hb2 hb hbX hV hu hVF hB hBb
    W hW hWi hWd hY S phase hS hSY hphase e he hNe j₀ k₀ h Z Q early hj hR hRL ρ hρ
  let P := stoppedIntervalSupport ι X (b/2) b e
  let U := P.biUnion primaryPrimeFactors
  let selected := stoppedSideTest (geometricPrimeBin (1+δ) X)
    (geometricBinLower (1+δ) X) j₀ k₀ h Z Q early
  let v := fun n => star (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n)
  have hbpos : 0 < b := by linarith
  have hN : 0 < b/2 := by positivity
  have hP : ∀ n ∈ P, primary n ∧ Squarefree n :=
    fun n hn => ⟨(stoppedIntervalSupport_spec X (b/2) b e hn).1,
      (stoppedIntervalSupport_spec X (b/2) b e hn).2.1⟩
  have hU : ∀ p ∈ U, primaryPrime p := by
    intro p hp
    obtain ⟨n,hn,hpn⟩ := Finset.mem_biUnion.mp hp
    exact (primaryPrimeFactor_spec (hP n hn).1 hpn).1
  have hPU : ∀ n ∈ P, primaryPrimeFactors n ⊆ U := by
    intro n hn p hp
    exact Finset.mem_biUnion.mpr ⟨n,hn,hp⟩
  have hlog : ∀ v ∈ S, ∀ a ∈ P, ∀ c ∈ P,
      |Real.log (norm v/Y)-Real.log ((norm a/(b/2))*(norm c/(b/2)))| ≤ m := by
    intro v hv a ha c hc
    exact compact_norm_log_ratio (by norm_num : (1:ℝ) ≤ 2)
      ⟨(le_div_iff₀ hY).mpr (by simpa using (hSY v hv).1),
        (div_le_iff₀ hY).mpr (hSY v hv).2⟩
      (stoppedIntervalSupport_scaled_norm hbpos e ha)
      (stoppedIntervalSupport_scaled_norm hbpos e hc)
  have hn := normCoprimeRadialForm_norm_le_mass m hm P S U hP hU hPU v v phase hphase
    (fun v => norm v/Y) (fun n => norm n/(b/2))
    (fun v hv => (le_div_iff₀ hY).mpr (by simpa using (hSY v hv).1))
    (fun n hn => zero_lt_one.trans_le (stoppedIntervalSupport_scaled_norm hbpos e hn).1)
    hlog Φ hΦ hΦ' hρ
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans
    (hmass δ (b/2) b u V B hδ hδone hwidth (by linarith) hb hbX hV hu hVF hB hBb
      W hW hWi hWd S U hS hU e he hNe j₀ k₀ h Z Q early hj hR hRL hN ρ hρ)

end CubicFirstMoment

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CubicFirstMoment.angular_stopped_noncube_radial_form_oai.{u_1} := @OAI.CubicFirstMoment.angular_stopped_noncube_radial_form_oai.{u_1}
